import FormalConjectures.Paper.OneTwoThreeConjecture
import Mathlib.Tactic

-- Problem: The 1-2-3 conjecture (Karoński–Łuczak–Thomason 2004), proved by Keusch (2024).
-- Upstream: formal-conjectures FormalConjectures/Paper/OneTwoThreeConjecture.lean:66 (declaration OneTwoThreeConjecture.one_two_three_conjecture)
-- Credit: @mattdorman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Formalization of R. Keusch, A solution to the 1-2-3 conjecture, J. Combin. Theory Ser. B 166 (2024),
arXiv:2303.02611. Integral flows replace the max-flow step (Lemma 2) and the spanning-tree parity
step (Lemma 4); Lemmas 1 and 8 are proved by extremal arguments.
-/

namespace OMA.K123
open Finset


section Flow
variable {V : Type} [Fintype V] [DecidableEq V]

/-- capacity of the cut leaving `X` -/
def cutCap (c : V → V → ℕ) (X : Finset V) : ℤ :=
  ∑ a, ∑ b, if a ∈ X ∧ b ∉ X then (c a b : ℤ) else 0

lemma cutCap_nonneg (c : V → V → ℕ) (X : Finset V) : 0 ≤ cutCap c X := by
  unfold cutCap
  apply sum_nonneg; intro a _; apply sum_nonneg; intro b _
  split_ifs <;> simp

lemma pt_submod (c : ℤ) (hc : 0 ≤ c) (p q r s : Prop) [Decidable p] [Decidable q]
    [Decidable r] [Decidable s] :
    (if (p ∧ r) ∧ ¬(q ∧ s) then c else 0) + (if (p ∨ r) ∧ ¬ (q ∨ s) then c else 0)
      + (if (p ∧ ¬ r) ∧ (s ∧ ¬ q) then c else 0) ≤
    (if p ∧ ¬q then c else 0) + (if r ∧ ¬s then c else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> by_cases hs : s <;> simp [*]

lemma cutCap_submod (c : V → V → ℕ) (A B : Finset V) (x y : V) (hxA : x ∈ A) (hxB : x ∉ B)
    (hyA : y ∉ A) (hyB : y ∈ B) :
    cutCap c (A ∩ B) + cutCap c (A ∪ B) + c x y ≤ cutCap c A + cutCap c B := by
  have key : ∀ a b, (if a ∈ A ∩ B ∧ b ∉ A ∩ B then (c a b : ℤ) else 0) +
      (if a ∈ A ∪ B ∧ b ∉ A ∪ B then (c a b : ℤ) else 0) +
      (if (a ∈ A ∧ a ∉ B) ∧ (b ∈ B ∧ b ∉ A) then (c a b : ℤ) else 0) ≤
      (if a ∈ A ∧ b ∉ A then (c a b : ℤ) else 0) + (if a ∈ B ∧ b ∉ B then (c a b : ℤ) else 0) := by
    intro a b
    have := pt_submod (c a b : ℤ) (by positivity) (a ∈ A) (b ∈ A) (a ∈ B) (b ∈ B)
    simpa [mem_inter, mem_union] using this
  have h3 : (c x y : ℤ) ≤ ∑ a, ∑ b,
      (if (a ∈ A ∧ a ∉ B) ∧ (b ∈ B ∧ b ∉ A) then (c a b : ℤ) else 0) := by
    have hin : (c x y : ℤ) ≤ ∑ b,
        (if (x ∈ A ∧ x ∉ B) ∧ (b ∈ B ∧ b ∉ A) then (c x b : ℤ) else 0) := by
      have := single_le_sum (f := fun b => if (x ∈ A ∧ x ∉ B) ∧ (b ∈ B ∧ b ∉ A)
        then (c x b : ℤ) else 0) (fun b _ => by split_ifs <;> simp) (mem_univ y)
      simpa [hxA, hxB, hyA, hyB] using this
    refine hin.trans ?_
    exact single_le_sum (f := fun a => ∑ b,
      (if (a ∈ A ∧ a ∉ B) ∧ (b ∈ B ∧ b ∉ A) then (c a b : ℤ) else 0))
      (fun a _ => sum_nonneg fun b _ => by split_ifs <;> simp) (mem_univ x)
  unfold cutCap
  calc (∑ a, ∑ b, if a ∈ A ∩ B ∧ b ∉ A ∩ B then (c a b : ℤ) else 0) +
        (∑ a, ∑ b, if a ∈ A ∪ B ∧ b ∉ A ∪ B then (c a b : ℤ) else 0) + (c x y : ℤ)
      ≤ (∑ a, ∑ b, if a ∈ A ∩ B ∧ b ∉ A ∩ B then (c a b : ℤ) else 0) +
        (∑ a, ∑ b, if a ∈ A ∪ B ∧ b ∉ A ∪ B then (c a b : ℤ) else 0) +
        ∑ a, ∑ b, (if (a ∈ A ∧ a ∉ B) ∧ (b ∈ B ∧ b ∉ A) then (c a b : ℤ) else 0) := by
        linarith
    _ = ∑ a, ∑ b, ((if a ∈ A ∩ B ∧ b ∉ A ∩ B then (c a b : ℤ) else 0) +
        (if a ∈ A ∪ B ∧ b ∉ A ∪ B then (c a b : ℤ) else 0) +
        (if (a ∈ A ∧ a ∉ B) ∧ (b ∈ B ∧ b ∉ A) then (c a b : ℤ) else 0)) := by
        simp only [sum_add_distrib]
    _ ≤ ∑ a, ∑ b, ((if a ∈ A ∧ b ∉ A then (c a b : ℤ) else 0) +
        (if a ∈ B ∧ b ∉ B then (c a b : ℤ) else 0)) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => key a b
    _ = _ := by simp only [sum_add_distrib]

lemma cutCap_dec (c : V → V → ℕ) (x y : V) (hc : 0 < c x y) (X : Finset V) :
    cutCap (fun a b => if a = x ∧ b = y then c a b - 1 else c a b) X =
      cutCap c X - (if x ∈ X ∧ y ∉ X then 1 else 0) := by
  unfold cutCap
  have h1 : ∀ a b, (if a ∈ X ∧ b ∉ X then
      (((if a = x ∧ b = y then c a b - 1 else c a b : ℕ)) : ℤ) else 0) =
      (if a ∈ X ∧ b ∉ X then (c a b : ℤ) else 0) -
        (if a = x ∧ b = y then (if x ∈ X ∧ y ∉ X then 1 else 0) else 0) := by
    intro a b
    by_cases hab : a = x ∧ b = y
    · obtain ⟨rfl, rfl⟩ := hab
      by_cases hX : a ∈ X ∧ b ∉ X
      · have h1c : 1 ≤ c a b := hc
        simp only [hX, not_false_eq_true, and_self, if_true]
        rw [Nat.cast_sub h1c]; simp
      · simp [hX]
    · simp [hab]
  simp only [h1, sum_sub_distrib]
  congr 1
  rw [sum_eq_single x]
  · rw [sum_eq_single y]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · intro a _ ha; apply sum_eq_zero; intro b _; simp [ha]
  · simp

lemma sum_shift (b : V → ℤ) (x y : V) (X : Finset V) :
    ∑ v ∈ X, (b v - (if v = x then 1 else 0) + (if v = y then 1 else 0)) =
      ∑ v ∈ X, b v - (if x ∈ X then 1 else 0) + (if y ∈ X then 1 else 0) := by
  rw [sum_add_distrib, sum_sub_distrib, sum_ite_eq', sum_ite_eq']

theorem flow_exists : ∀ (N : ℕ) (c : V → V → ℕ), ∑ a, ∑ b, c a b = N → ∀ (b : V → ℤ),
    ∑ v, b v = 0 → (∀ X : Finset V, ∑ x ∈ X, b x ≤ cutCap c X) →
    ∃ φ : V → V → ℕ, (∀ x y, φ x y ≤ c x y) ∧
      ∀ x, (∑ y, (φ x y : ℤ)) - ∑ y, (φ y x : ℤ) = b x := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro c hN b hsum hcut
  by_cases hz : ∀ x y, c x y = 0
  · -- all capacities vanish, so b = 0
    have hcap : ∀ X, cutCap c X = 0 := by
      intro X; unfold cutCap; simp [hz]
    have hle : ∀ v, b v ≤ 0 := by
      intro v
      by_contra hv
      push Not at hv
      have h1 := hcut (univ.filter fun v => 0 < b v)
      rw [hcap] at h1
      have h2 : 0 < ∑ x ∈ univ.filter (fun v => 0 < b v), b x :=
        sum_pos (fun i hi => (mem_filter.mp hi).2) ⟨v, by simp [hv]⟩
      linarith
    have hb0 : ∀ v, b v = 0 := by
      intro v
      have := (sum_eq_zero_iff_of_nonpos (fun i _ => hle i)).mp hsum v (mem_univ v)
      exact this
    refine ⟨fun _ _ => 0, fun x y => by simp, fun x => by simp [hb0]⟩
  push Not at hz
  obtain ⟨x, y, hxy⟩ := hz
  have hxy' : 0 < c x y := Nat.pos_of_ne_zero hxy
  set c1 : V → V → ℕ := fun a b => if a = x ∧ b = y then c a b - 1 else c a b with hc1
  have hc1le : ∀ a b, c1 a b ≤ c a b := by
    intro a b; simp only [hc1]; split_ifs <;> omega
  have hlt : ∑ a, ∑ b, c1 a b < N := by
    rw [← hN]
    apply sum_lt_sum (fun a _ => sum_le_sum fun b _ => hc1le a b)
    refine ⟨x, mem_univ _, ?_⟩
    apply sum_lt_sum (fun b _ => hc1le x b)
    exact ⟨y, mem_univ _, by simp only [hc1, and_self, if_true]; omega⟩
  have hcap1 : ∀ X, cutCap c1 X = cutCap c X - (if x ∈ X ∧ y ∉ X then 1 else 0) :=
    cutCap_dec c x y hxy'
  by_cases h1 : ∀ X : Finset V, ∑ v ∈ X, b v ≤ cutCap c1 X
  · obtain ⟨φ, hφ, hφb⟩ := ih _ hlt c1 rfl b hsum h1
    exact ⟨φ, fun a b => (hφ a b).trans (hc1le a b), hφb⟩
  set b' : V → ℤ := fun v => b v - (if v = x then 1 else 0) + (if v = y then 1 else 0) with hb'
  by_cases h2 : ∀ X : Finset V, ∑ v ∈ X, b' v ≤ cutCap c1 X
  · have hsum' : ∑ v, b' v = 0 := by
      simp only [hb']; rw [sum_shift]; simp [hsum]
    obtain ⟨φ, hφ, hφb⟩ := ih _ hlt c1 rfl b' hsum' h2
    refine ⟨fun a b => φ a b + (if a = x ∧ b = y then 1 else 0), ?_, ?_⟩
    · intro a b
      by_cases hab : a = x ∧ b = y
      · obtain ⟨rfl, rfl⟩ := hab
        have := hφ a b; simp only [hc1, and_self, if_true] at this; simp; omega
      · have := hφ a b; simp only [hc1, hab, if_false] at this; simp [hab, this]
    · intro v
      have e1 : (∑ u, ((φ v u + (if v = x ∧ u = y then 1 else 0) : ℕ) : ℤ)) =
          (∑ u, (φ v u : ℤ)) + (if v = x then 1 else 0) := by
        push_cast; rw [sum_add_distrib]; congr 1
        by_cases hv : v = x
        · subst hv; simp
        · simp [hv]
      have e2 : (∑ u, ((φ u v + (if u = x ∧ v = y then 1 else 0) : ℕ) : ℤ)) =
          (∑ u, (φ u v : ℤ)) + (if v = y then 1 else 0) := by
        push_cast; rw [sum_add_distrib]; congr 1
        by_cases hv : v = y
        · subst hv; simp
        · simp [hv]
      rw [e1, e2]
      have := hφb v
      simp only [hb'] at this
      linarith
  exfalso
  push Not at h1 h2
  obtain ⟨X1, hX1⟩ := h1
  obtain ⟨X2, hX2⟩ := h2
  rw [hcap1] at hX1 hX2
  have g1 := hcut X1
  have g2 := hcut X2
  have hX1' : x ∈ X1 ∧ y ∉ X1 := by
    by_contra hh; simp [hh] at hX1; linarith
  simp only [hX1', not_false_eq_true, and_self, if_true] at hX1
  simp only [hb'] at hX2
  rw [sum_shift] at hX2
  have hyX2 : y ∈ X2 := by
    by_contra hy
    by_cases hx : x ∈ X2
    · simp [hx, hy] at hX2; linarith
    · simp [hx, hy] at hX2; linarith
  have hxX2 : x ∉ X2 := by
    intro hx
    simp only [hx, hyX2, if_true, not_true_eq_false, and_false, if_false] at hX2
    linarith
  simp only [hxX2, hyX2, if_false, if_true, false_and] at hX2
  have hsub := cutCap_submod c X1 X2 x y hX1'.1 hxX2 hX1'.2 hyX2
  have hmod : ∑ v ∈ X1 ∩ X2, b v + ∑ v ∈ X1 ∪ X2, b v = ∑ v ∈ X1, b v + ∑ v ∈ X2, b v := by
    rw [add_comm]; exact sum_union_inter
  have g3 := hcut (X1 ∩ X2)
  have g4 := hcut (X1 ∪ X2)
  have : (1 : ℤ) ≤ c x y := by exact_mod_cast hxy'
  linarith

end Flow
section Basic
variable {V : Type} [Fintype V] [DecidableEq V]

/-- weighted degree, as a sum over neighbours -/
def sd (H : SimpleGraph V) [DecidableRel H.Adj] (w : Sym2 V → ℤ) (v : V) : ℤ :=
  ∑ u ∈ univ.filter (H.Adj v), w s(v, u)

lemma sum_filter_univ (p : V → Prop) [DecidablePred p] (t : V → ℤ) :
    ∑ u ∈ univ.filter p, t u = ∑ u, if p u then t u else 0 := sum_filter _ _

lemma sum_XnotX (t : V → V → ℤ) (X : Finset V) :
    ∑ a, ∑ b, (if a ∈ X ∧ b ∉ X then t a b else 0) = ∑ a ∈ X, ∑ b ∈ univ \ X, t a b := by
  have h1 : ∀ a, ∑ b, (if a ∈ X ∧ b ∉ X then t a b else 0) =
      if a ∈ X then ∑ b ∈ univ \ X, t a b else 0 := by
    intro a
    by_cases ha : a ∈ X
    · simp only [ha, true_and, if_true]
      rw [← sum_filter]; congr 1; ext b; simp
    · simp [ha]
  simp only [h1]
  rw [← sum_filter]; congr 1; ext a; simp

lemma cutCap_eq (c : V → V → ℕ) (X : Finset V) :
    cutCap c X = ∑ a ∈ X, ∑ b ∈ univ \ X, (c a b : ℤ) := sum_XnotX _ X

lemma netout_sum (ψ : V → V → ℤ) (X : Finset V) :
    ∑ v ∈ X, (∑ u, ψ v u - ∑ u, ψ u v) = ∑ a ∈ X, ∑ u ∈ univ \ X, (ψ a u - ψ u a) := by
  have split : ∀ (F : V → ℤ), ∑ u, F u = ∑ u ∈ X, F u + ∑ u ∈ univ \ X, F u := by
    intro F
    rw [← sum_union disjoint_sdiff, union_sdiff_of_subset (subset_univ X)]
  have hA : ∑ v ∈ X, ∑ u ∈ X, ψ v u = ∑ v ∈ X, ∑ u ∈ X, ψ u v := sum_comm
  simp only [sum_sub_distrib]
  rw [show (∑ v ∈ X, ∑ u, ψ v u) = ∑ v ∈ X, ∑ u ∈ X, ψ v u + ∑ v ∈ X, ∑ u ∈ univ \ X, ψ v u by
        rw [← sum_add_distrib]; exact sum_congr rfl fun v _ => split _,
      show (∑ v ∈ X, ∑ u, ψ u v) = ∑ v ∈ X, ∑ u ∈ X, ψ u v + ∑ v ∈ X, ∑ u ∈ univ \ X, ψ u v by
        rw [← sum_add_distrib]; exact sum_congr rfl fun v _ => split _, hA]
  ring

lemma natAbs_mul_sign' (g : ℤ) : (g.natAbs : ℤ) * g.sign = g := by
  rw [mul_comm]; exact Int.sign_mul_natAbs g

lemma sign_abs_le (g : ℤ) : -1 ≤ g.sign ∧ g.sign ≤ 1 := by
  rcases Int.sign_trichotomy g with h | h | h <;> simp [h]

end Basic
section Weighting
variable {V : Type} [Fintype V] [DecidableEq V]

lemma maxcut_exists (H : SimpleGraph V) [DecidableRel H.Adj] : ∃ S : Finset V, ∀ X : Finset V,
    ∑ a ∈ X, ∑ b ∈ univ \ X, (if H.Adj a b ∧ (a ∈ S ↔ b ∈ S) then (1:ℤ) else 0) ≤
    ∑ a ∈ X, ∑ b ∈ univ \ X, (if H.Adj a b ∧ ¬(a ∈ S ↔ b ∈ S) then (1:ℤ) else 0) := by
  let κ : Finset V → ℤ := fun T => ∑ a, ∑ b, if H.Adj a b ∧ ¬(a ∈ T ↔ b ∈ T) then 1 else 0
  obtain ⟨S, -, hS⟩ := exists_max_image (univ : Finset (Finset V)) κ univ_nonempty
  refine ⟨S, fun X => ?_⟩
  set S' : Finset V := univ.filter (fun a => ¬ (a ∈ S ↔ a ∈ X)) with hS'
  have hle := hS S' (mem_univ _)
  let t : V → V → ℤ := fun a b => (if H.Adj a b ∧ (a ∈ S ↔ b ∈ S) then (1:ℤ) else 0) -
    (if H.Adj a b ∧ ¬(a ∈ S ↔ b ∈ S) then (1:ℤ) else 0)
  have pt : ∀ a b, (if H.Adj a b ∧ ¬(a ∈ S' ↔ b ∈ S') then (1:ℤ) else 0) -
      (if H.Adj a b ∧ ¬(a ∈ S ↔ b ∈ S) then (1:ℤ) else 0) =
      (if a ∈ X ∧ b ∉ X then t a b else 0) + (if b ∈ X ∧ a ∉ X then t b a else 0) := by
    intro a b
    simp only [hS', mem_filter, mem_univ, true_and, t]
    have hs : H.Adj b a ↔ H.Adj a b := ⟨fun h => h.symm, fun h => h.symm⟩
    by_cases hab : H.Adj a b <;> by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
      by_cases hxa : a ∈ X <;> by_cases hxb : b ∈ X <;> simp [*]
  have hsum : κ S' - κ S = 2 * ∑ a ∈ X, ∑ b ∈ univ \ X, t a b := by
    simp only [κ, ← sum_sub_distrib, pt, sum_add_distrib]
    rw [sum_comm (f := fun a b => if b ∈ X ∧ a ∉ X then t b a else 0), sum_XnotX]
    ring
  have : ∑ a ∈ X, ∑ b ∈ univ \ X, t a b ≤ 0 := by linarith
  simp only [t, sum_sub_distrib] at this
  linarith

/-- the designated odd colour obtained from a target even value -/
def desig (S : Finset V) (s0 : V → ℤ) (v : V) (t : ℤ) : ℤ :=
  if ((s0 v + 2 * t) % 4 = 0 ↔ v ∈ S) then s0 v + 2 * t + 1 else s0 v + 2 * t - 1

lemma desig_mod (S : Finset V) (s0 : V → ℤ) (hs0 : ∀ v, Even (s0 v)) (v : V) (t : ℤ) :
    (v ∈ S → desig S s0 v t % 4 = 1) ∧ (v ∉ S → desig S s0 v t % 4 = 3) := by
  obtain ⟨r, hr⟩ := hs0 v
  unfold desig
  constructor <;> intro hv <;> split_ifs with h <;> simp_all <;> omega

lemma desig_odd (S : Finset V) (s0 : V → ℤ) (hs0 : ∀ v, Even (s0 v)) (v : V) (t : ℤ) :
    Odd (desig S s0 v t) := by
  obtain ⟨r, hr⟩ := hs0 v
  unfold desig
  split_ifs
  · exact ⟨r + t, by omega⟩
  · exact ⟨r + t - 1, by omega⟩

lemma desig_dist (S : Finset V) (s0 : V → ℤ) (v : V) (t : ℤ) :
    |s0 v + 2 * t - desig S s0 v t| = 1 := by
  unfold desig; split_ifs <;> simp [abs_eq]

lemma desig_fiber (S : Finset V) (s0 : V → ℤ) (v : V) (I : Finset ℤ) (a : ℤ) :
    (I.filter fun t => desig S s0 v t = a).card ≤ 2 := by
  have hsub : I.filter (fun t => desig S s0 v t = a) ⊆
      {(a - 1 - s0 v) / 2, (a + 1 - s0 v) / 2} := by
    intro t ht
    simp only [mem_filter] at ht
    have := ht.2
    unfold desig at this
    simp only [mem_insert, mem_singleton]
    split_ifs at this <;> omega
  exact (card_le_card hsub).trans (card_insert_le _ _)

theorem weighting (H : SimpleGraph V) [DecidableRel H.Adj] (h : V → ℤ) (hh : ∀ v, Even (h v)) :
    ∃ (w : Sym2 V → ℤ) (f : V → ℤ),
      (∀ u v, H.Adj u v → 1 ≤ w s(u, v) ∧ w s(u, v) ≤ 3) ∧
      (∀ v, Odd (f v)) ∧ (∀ u v, H.Adj u v → f u ≠ f v) ∧
      ∀ v, |sd H w v + h v - f v| = 1 := by
  obtain ⟨S, hS⟩ := maxcut_exists H
  let rk : V → ℕ := fun v => (Fintype.equivFin V v : ℕ)
  have rk_inj : ∀ a b, rk a = rk b → a = b := by
    intro a b hab
    exact (Fintype.equivFin V).injective (Fin.ext hab)
  have rk_lt : ∀ a, rk a < Fintype.card V := fun a => (Fintype.equivFin V a).isLt
  let dg : V → ℤ := fun v => ((univ.filter (H.Adj v)).card : ℤ)
  let s0 : V → ℤ := fun v => h v + 2 * dg v
  have hs0 : ∀ v, Even (s0 v) := by
    intro v; obtain ⟨r, hr⟩ := hh v; exact ⟨r + dg v, by simp only [s0]; omega⟩
  let back : V → Finset V := fun v =>
    univ.filter (fun u => H.Adj v u ∧ rk u < rk v ∧ (u ∈ S ↔ v ∈ S))
  let F : V → ℤ → ℤ := desig S s0
  -- greedy choice of g
  have greedy : ∀ m : ℕ, ∃ g : V → ℤ, (∀ v, |g v| ≤ (back v).card) ∧
      ∀ u v, H.Adj u v → (u ∈ S ↔ v ∈ S) → rk u < m → rk v < m → F u (g u) ≠ F v (g v) := by
    intro m
    induction m with
    | zero => exact ⟨fun _ => 0, fun v => by simp, fun u v _ _ hu _ => absurd hu (Nat.not_lt_zero _)⟩
    | succ m ih =>
      obtain ⟨g, hgb, hgp⟩ := ih
      by_cases hv : ∃ v, rk v = m
      · obtain ⟨v, hv⟩ := hv
        set k : ℕ := (back v).card with hk
        let Forb : Finset ℤ := (back v).image (fun u => F u (g u))
        have hex : ∃ t ∈ Icc (-(k : ℤ)) k, F v t ∉ Forb := by
          by_contra hno
          push Not at hno
          have := card_le_mul_card_image_of_maps_to (s := Icc (-(k : ℤ)) k) (t := Forb)
            (f := F v) hno 2 (fun a _ => desig_fiber S s0 v _ a)
          have h1 : (Icc (-(k : ℤ)) k).card = 2 * k + 1 := by
            simp only [Int.card_Icc]; omega
          have h2 : Forb.card ≤ k := card_image_le
          omega
        obtain ⟨t, ht, htF⟩ := hex
        refine ⟨Function.update g v t, ?_, ?_⟩
        · intro u
          by_cases huv : u = v
          · subst huv; simp only [Function.update_self]; rw [abs_le]; simp at ht; omega
          · simp only [Function.update_of_ne huv]; exact hgb u
        · intro a b hab hs ha hb
          have key : ∀ a b, H.Adj a b → (a ∈ S ↔ b ∈ S) → rk a < m + 1 → rk b < m + 1 →
              rk b < rk a → a = v → F a (Function.update g v t a) ≠
                F b (Function.update g v t b) := by
            intro a b hab hs ha hb hba hav
            subst hav
            have hbv : b ≠ a := fun h => by subst h; omega
            simp only [Function.update_self, Function.update_of_ne hbv]
            intro heq
            apply htF
            simp only [Forb, mem_image]
            refine ⟨b, ?_, heq.symm⟩
            simp only [back, mem_filter, mem_univ, true_and]
            exact ⟨hab, hba, hs.symm⟩
          by_cases hav : a = v
          · have hba : rk b < rk a := by
              have : b ≠ a := fun h => by subst h; exact hab.ne rfl
              have : rk b ≠ rk a := fun h => this (rk_inj _ _ h)
              have e1 : rk a = m := hav ▸ hv
              omega
            exact key a b hab hs ha hb hba hav
          by_cases hbv : b = v
          · have hab' : rk a < rk b := by
              have : a ≠ b := hab.ne
              have : rk a ≠ rk b := fun h => this (rk_inj _ _ h)
              have e1 : rk b = m := hbv ▸ hv
              omega
            exact (key b a hab.symm hs.symm hb ha hab' hbv).symm
          simp only [Function.update_of_ne hav, Function.update_of_ne hbv]
          have ha' : rk a < m := by
            have : rk a ≠ m := fun h => hav (rk_inj _ _ (h.trans hv.symm))
            omega
          have hb' : rk b < m := by
            have : rk b ≠ m := fun h => hbv (rk_inj _ _ (h.trans hv.symm))
            omega
          exact hgp a b hab hs ha' hb'
      · push Not at hv
        refine ⟨g, hgb, fun a b hab hs ha hb => hgp a b hab hs ?_ ?_⟩
        · have := hv a; omega
        · have := hv b; omega
  obtain ⟨g, hgb, hgp⟩ := greedy (Fintype.card V)
  -- choose the edges to modify
  have hch : ∀ v, ∃ C ⊆ back v, C.card = (g v).natAbs := by
    intro v
    apply le_card_iff_exists_subset_card.mp
    have := hgb v; have e := Int.natCast_natAbs (g v); omega
  choose Ch hChs hChc using hch
  have mem_Ch : ∀ a u, u ∈ Ch a → H.Adj a u ∧ rk u < rk a ∧ (u ∈ S ↔ a ∈ S) := by
    intro a u hu
    have := hChs a hu
    simpa [back] using this
  let sg : V → ℤ := fun v => (g v).sign
  let ψ : V → V → ℤ := fun a u => if u ∈ Ch a then (if a ∈ S then sg a else - sg a) else 0
  let bb : V → ℤ := fun v => ∑ u, ψ v u - ∑ u, ψ u v
  let c : V → V → ℕ := fun a b => if H.Adj a b ∧ ¬(a ∈ S ↔ b ∈ S) then 1 else 0
  have hbsum : ∑ v, bb v = 0 := by
    simp only [bb, sum_sub_distrib]; rw [sum_comm]; ring
  have hψpt : ∀ a u, ψ a u - ψ u a ≤ if H.Adj a u ∧ (a ∈ S ↔ u ∈ S) then 1 else 0 := by
    intro a u
    have hsa := sign_abs_le (g a)
    have hsu := sign_abs_le (g u)
    by_cases hua : u ∈ Ch a
    · obtain ⟨h1, h2, h3⟩ := mem_Ch a u hua
      have hau : a ∉ Ch u := fun h => by have := (mem_Ch u a h).2.1; omega
      simp only [ψ, hua, hau, if_true, if_false, sg, h1, h3.symm, true_and]
      split_ifs <;> omega
    · by_cases hau : a ∈ Ch u
      · obtain ⟨h1, h2, h3⟩ := mem_Ch u a hau
        simp only [ψ, hua, hau, if_true, if_false, sg, h1.symm, h3, true_and]
        split_ifs <;> omega
      · simp only [ψ, hua, hau, if_false]; split_ifs <;> omega
  have hcut : ∀ X : Finset V, ∑ x ∈ X, bb x ≤ cutCap c X := by
    intro X
    rw [netout_sum, cutCap_eq]
    calc ∑ a ∈ X, ∑ u ∈ univ \ X, (ψ a u - ψ u a)
        ≤ ∑ a ∈ X, ∑ u ∈ univ \ X, (if H.Adj a u ∧ (a ∈ S ↔ u ∈ S) then (1:ℤ) else 0) :=
          sum_le_sum fun a _ => sum_le_sum fun u _ => hψpt a u
      _ ≤ _ := hS X
      _ = ∑ a ∈ X, ∑ b ∈ univ \ X, (c a b : ℤ) := by
          apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _
          simp only [c]; split_ifs <;> simp
  obtain ⟨φ, hφc, hφb⟩ := flow_exists _ c rfl bb hbsum hcut
  -- the weighting
  let ein : V → V → ℤ := fun a b =>
    if rk b < rk a then (if b ∈ Ch a then sg a else 0) else (if a ∈ Ch b then sg b else 0)
  let ecut : V → V → ℤ := fun a b =>
    if a ∈ S then (φ a b : ℤ) - φ b a else (φ b a : ℤ) - φ a b
  let E : V → V → ℤ := fun a b => if (a ∈ S ↔ b ∈ S) then ein a b else ecut a b
  have Esymm : ∀ a b, E a b = E b a := by
    intro a b
    by_cases hab : a = b
    · subst hab; rfl
    have hr : rk a ≠ rk b := fun h => hab (rk_inj _ _ h)
    simp only [E, ein, ecut]
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp only [ha, hb, iff_true, iff_false,
      true_iff, false_iff, not_true, not_false_eq_true, if_true, if_false] <;>
      (try rcases Nat.lt_or_gt_of_ne hr with h | h) <;> simp [h, not_lt_of_gt h]
  let w : Sym2 V → ℤ := Sym2.lift ⟨fun a b => 2 + E a b, fun a b => by simp only [Esymm a b]⟩
  have hw : ∀ a b, w s(a, b) = 2 + E a b := fun a b => rfl
  refine ⟨w, fun v => F v (g v), ?_, fun v => desig_odd S s0 hs0 v _, ?_, ?_⟩
  · -- weights in [1,3]
    intro a b _
    rw [hw]
    have hsa := sign_abs_le (g a)
    have hsb := sign_abs_le (g b)
    have h1 := hφc a b
    have h2 := hφc b a
    have hc1 : c a b ≤ 1 := by simp only [c]; split_ifs <;> omega
    have hc2 : c b a ≤ 1 := by simp only [c]; split_ifs <;> omega
    simp only [E, ein, ecut, sg]
    split_ifs <;> omega
  · -- proper
    intro a b hab
    by_cases hs : (a ∈ S ↔ b ∈ S)
    · have := hgp a b hab hs (rk_lt a) (rk_lt b)
      exact this
    · intro heq
      have ma := desig_mod S s0 hs0 a (g a)
      have mb := desig_mod S s0 hs0 b (g b)
      simp only [F] at heq
      by_cases ha : a ∈ S
      · have hb : b ∉ S := fun hb => hs ⟨fun _ => hb, fun _ => ha⟩
        have := ma.1 ha; have := mb.2 hb; omega
      · have hb : b ∈ S := by by_contra hb; exact hs ⟨fun h => absurd h ha, fun h => absurd h hb⟩
        have := ma.2 ha; have := mb.1 hb; omega
  · -- the weighted degree
    intro v
    have hsd : sd H w v = 2 * dg v + (g v + ∑ u, (if v ∈ Ch u then sg u else 0)) +
        (if v ∈ S then bb v else - bb v) := by
      simp only [sd, hw, sum_add_distrib, sum_const, nsmul_eq_mul, mul_comm]
      simp only [dg]
      have hsplit := sum_filter_add_sum_filter_not (univ.filter (H.Adj v))
        (fun u => (v ∈ S ↔ u ∈ S)) (fun u => E v u)
      rw [← hsplit]
      have hin : ∑ u ∈ (univ.filter (H.Adj v)).filter (fun u => (v ∈ S ↔ u ∈ S)), E v u =
          g v + ∑ u, (if v ∈ Ch u then sg u else 0) := by
        rw [filter_filter, sum_filter]
        have pt : ∀ u, (if H.Adj v u ∧ (v ∈ S ↔ u ∈ S) then E v u else 0) =
            (if u ∈ Ch v then sg v else 0) + (if v ∈ Ch u then sg u else 0) := by
          intro u
          by_cases hu : u ∈ Ch v
          · obtain ⟨h1, h2, h3⟩ := mem_Ch v u hu
            have hvu : v ∉ Ch u := fun h => by have := (mem_Ch u v h).2.1; omega
            simp [E, ein, hu, hvu, h1, h3.symm, h2]
          · by_cases hvu : v ∈ Ch u
            · obtain ⟨h1, h2, h3⟩ := mem_Ch u v hvu
              simp [E, ein, hu, hvu, h1.symm, h3, not_lt_of_gt h2]
            · simp only [hu, hvu, if_false, add_zero]
              split_ifs with hh
              · simp only [E, hh.2, if_true, ein]; split_ifs <;> rfl
              · rfl
        simp only [pt, sum_add_distrib]
        congr 1
        rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul, hChc]
        exact natAbs_mul_sign' (g v)
      have hcutp : ∑ u ∈ (univ.filter (H.Adj v)).filter (fun u => ¬(v ∈ S ↔ u ∈ S)), E v u =
          if v ∈ S then bb v else - bb v := by
        rw [filter_filter, sum_filter]
        have hφ0 : ∀ a b, ¬(H.Adj a b ∧ ¬(a ∈ S ↔ b ∈ S)) → φ a b = 0 := by
          intro a b hab
          have := hφc a b; simp only [c, hab, if_false] at this; omega
        have hb := hφb v
        have pt : ∀ u, (if H.Adj v u ∧ ¬(v ∈ S ↔ u ∈ S) then E v u else 0) =
            if v ∈ S then (φ v u : ℤ) - φ u v else (φ u v : ℤ) - φ v u := by
          intro u
          by_cases hh : H.Adj v u ∧ ¬(v ∈ S ↔ u ∈ S)
          · simp only [hh, not_false_eq_true, and_self, if_true, E, if_false, ecut]
          · have e1 := hφ0 v u hh
            have e2 := hφ0 u v (fun h => hh ⟨h.1.symm, fun h' => h.2 h'.symm⟩)
            simp [hh, e1, e2]
        simp only [pt]
        split_ifs
        · rw [sum_sub_distrib]; exact hb
        · rw [sum_sub_distrib]; simp only [bb] at hb ⊢; linarith
      rw [hin, hcutp]
      ring
    have hIN : ∀ v, (if v ∈ S then bb v else - bb v) = g v - ∑ u, (if v ∈ Ch u then sg u else 0) := by
      intro v
      have h1 : ∑ u, ψ v u = if v ∈ S then g v else - g v := by
        simp only [ψ]
        rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul, hChc]
        split_ifs
        · exact natAbs_mul_sign' (g v)
        · rw [mul_neg, natAbs_mul_sign']
      have h2 : ∑ u, ψ u v = if v ∈ S then ∑ u, (if v ∈ Ch u then sg u else 0)
          else - ∑ u, (if v ∈ Ch u then sg u else 0) := by
        split_ifs with hv
        · apply sum_congr rfl; intro u _
          by_cases hu : v ∈ Ch u
          · have := (mem_Ch u v hu).2.2
            simp [ψ, hu, this.mp hv]
          · simp [ψ, hu]
        · rw [← sum_neg_distrib]; apply sum_congr rfl; intro u _
          by_cases hu : v ∈ Ch u
          · have := (mem_Ch u v hu).2.2
            have hu' : u ∉ S := fun h => hv (this.mpr h)
            simp [ψ, hu, hu']
          · simp [ψ, hu]
      simp only [bb, h1, h2]
      split_ifs <;> ring
    rw [hsd, hIN]
    have := desig_dist S s0 v (g v)
    simp only [s0] at this
    have e : 2 * dg v + (g v + ∑ u, (if v ∈ Ch u then sg u else 0)) +
        (g v - ∑ u, (if v ∈ Ch u then sg u else 0)) + h v - F v (g v) =
        h v + 2 * dg v + 2 * g v - desig S s0 v (g v) := by simp only [F]; ring
    rw [e]; exact this

end Weighting
section Between
variable {V : Type} [Fintype V] [DecidableEq V]

lemma even_sum_sub_card_odd (s : Finset V) (f : V → ℤ) :
    Even (∑ u ∈ s, f u - ((s.filter fun u => Odd (f u)).card : ℤ)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, filter_insert]
    by_cases hfa : Odd (f a)
    · rw [if_pos hfa, card_insert_of_notMem (by simp [ha])]
      obtain ⟨r, hr⟩ := hfa
      obtain ⟨q, hq⟩ := ih
      exact ⟨r + q, by push_cast; linarith⟩
    · rw [if_neg hfa]
      have hfa' : Even (f a) := Int.not_odd_iff_even.mp hfa
      obtain ⟨r, hr⟩ := hfa'
      obtain ⟨q, hq⟩ := ih
      exact ⟨r + q, by linarith⟩

lemma reach_cross (K : SimpleGraph V) (X : Finset V) {a b : V} (h : K.Reachable a b)
    (ha : a ∈ X) (hb : b ∉ X) : ∃ u v, K.Adj u v ∧ u ∈ X ∧ v ∉ X := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact absurd ha hb
  | cons hadj p ih =>
    rename_i x y z
    by_cases hy : y ∈ X
    · exact ih hy hb
    · exact ⟨x, y, hadj, ha, hy⟩

lemma local_choice (N : Finset V) (δ : ℤ) (hδ : |δ| ≤ 1)
    (hpar : Even ((N.card : ℤ) - δ)) (a c e : V) (pf ef : Prop) (hpe : ¬ (pf ∧ ef)) :
    ∃ P ⊆ N, 2 * (P.card : ℤ) - N.card = δ ∧
      (pf → a ∈ N → c ∈ N → a ≠ c → (a ∈ P ↔ c ∉ P)) ∧
      (ef → e ∈ N → (e ∈ P ↔ δ = 1)) := by
  obtain ⟨r, hr⟩ := hpar
  rw [abs_le] at hδ
  by_cases hp : pf ∧ a ∈ N ∧ c ∈ N ∧ a ≠ c
  · obtain ⟨hpf, haN, hcN, hac⟩ := hp
    have hc2 : 2 ≤ N.card := by
      have : ({a, c} : Finset V) ⊆ N := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      have := card_le_card this
      rw [card_pair hac] at this; exact this
    set p : ℕ := (N.card + δ).toNat / 2 with hpdef
    have hp1 : 1 ≤ p := by omega
    have hp2 : p + 1 ≤ N.card := by omega
    obtain ⟨Q, hQs, hQc⟩ := le_card_iff_exists_subset_card.mp
      (show p - 1 ≤ ((N.erase a).erase c).card by
        rw [card_erase_of_mem (by simp [hcN, Ne.symm hac]), card_erase_of_mem haN]; omega)
    have haQ : a ∉ Q := fun h => by have := hQs h; simp at this
    have hcQ : c ∉ Q := fun h => by have := hQs h; simp at this
    refine ⟨insert a Q, ?_, ?_, ?_, ?_⟩
    · intro x hx; rw [mem_insert] at hx
      rcases hx with rfl | hx
      · exact haN
      · exact mem_of_mem_erase (mem_of_mem_erase (hQs hx))
    · rw [card_insert_of_notMem haQ, hQc]; push_cast [Nat.cast_sub hp1]; omega
    · intro _ _ _ _; simp [haQ, hcQ, Ne.symm hac]
    · intro hef; exact absurd ⟨hpf, hef⟩ hpe
  by_cases he : ef ∧ e ∈ N
  · obtain ⟨hef, heN⟩ := he
    have hN1 : 1 ≤ N.card := card_pos.mpr ⟨e, heN⟩
    by_cases hd : δ = 1
    · obtain ⟨Q, hQs, hQc⟩ := le_card_iff_exists_subset_card.mp
        (show (N.card - 1) / 2 ≤ (N.erase e).card by rw [card_erase_of_mem heN]; omega)
      have heQ : e ∉ Q := fun h => by have := hQs h; simp at this
      refine ⟨insert e Q, ?_, ?_, ?_, ?_⟩
      · intro x hx; rw [mem_insert] at hx
        rcases hx with rfl | hx
        · exact heN
        · exact mem_of_mem_erase (hQs hx)
      · rw [card_insert_of_notMem heQ, hQc]; push_cast; omega
      · intro hpf; exact absurd ⟨hpf, hef⟩ hpe
      · intro _ _; simp [hd]
    · obtain ⟨Q, hQs, hQc⟩ := le_card_iff_exists_subset_card.mp
        (show (N.card + δ).toNat / 2 ≤ (N.erase e).card by rw [card_erase_of_mem heN]; omega)
      have heQ : e ∉ Q := fun h => by have := hQs h; simp at this
      refine ⟨Q, fun x hx => mem_of_mem_erase (hQs hx), ?_, ?_, ?_⟩
      · rw [hQc]; omega
      · intro hpf; exact absurd ⟨hpf, hef⟩ hpe
      · intro _ _; simp [hd, heQ]
  · obtain ⟨Q, hQs, hQc⟩ := le_card_iff_exists_subset_card.mp
      (show (N.card + δ).toNat / 2 ≤ N.card by omega)
    refine ⟨Q, hQs, ?_, ?_, ?_⟩
    · rw [hQc]; omega
    · intro hpf haN hcN hac; exact absurd ⟨hpf, haN, hcN, hac⟩ hp
    · intro hef heN; exact absurd ⟨hef, heN⟩ he

/-- Keusch, Lemma 4: weighting the edges between the blue set and the rest. -/
theorem between (K : SimpleGraph V) [DecidableRel K.Adj] (B Rp : Finset V)
    (hbip : ∀ u v, K.Adj u v → (u ∈ B ↔ v ∉ B)) (hRp : Disjoint Rp B)
    (α : V → ℤ) (hα : ∀ v ∈ B, |α v - 2 * ((univ.filter (K.Adj v)).card : ℤ)| ≤ 1)
    (hpar : Even ((Rp.card : ℤ) + ∑ v ∈ B, α v))
    (hconn : ∀ a ∈ B ∪ Rp, ∀ b ∈ B ∪ Rp, K.Reachable a b)
    (pa pc en : V → V) (pairOn endOn : Finset V) (hpe : ∀ v, v ∈ pairOn → v ∉ endOn) :
    ∃ w : Sym2 V → ℤ, (∀ u v, K.Adj u v → 1 ≤ w s(u, v) ∧ w s(u, v) ≤ 3) ∧
      (∀ v, v ∉ B → (Odd (sd K w v) ↔ v ∈ Rp)) ∧ (∀ v ∈ B, sd K w v = α v) ∧
      (∀ v ∈ B, v ∈ pairOn → pa v ≠ pc v → K.Adj v (pa v) → K.Adj v (pc v) →
        3 ≤ w s(v, pa v) + w s(v, pc v) ∧ w s(v, pa v) + w s(v, pc v) ≤ 5) ∧
      (∀ v ∈ B, v ∈ endOn → K.Adj v (en v) →
        (α v = 2 * ((univ.filter (K.Adj v)).card : ℤ) + 1 → w s(v, en v) ≠ 1) ∧
        (α v ≠ 2 * ((univ.filter (K.Adj v)).card : ℤ) + 1 → w s(v, en v) ≠ 3)) := by
  let dg : V → ℤ := fun v => ((univ.filter (K.Adj v)).card : ℤ)
  let Vo : Finset V := Rp ∪ B.filter (fun v => Odd (α v))
  have hVo_even : Even (Vo.card : ℤ) := by
    have hdisj : Disjoint Rp (B.filter fun v => Odd (α v)) :=
      disjoint_of_subset_right (filter_subset _ _) hRp
    have hc : (Vo.card : ℤ) = Rp.card + (B.filter fun v => Odd (α v)).card := by
      simp only [Vo]; rw [card_union_of_disjoint hdisj]; push_cast; ring
    have h2 := even_sum_sub_card_odd B α
    rw [hc]
    obtain ⟨r1, hr1⟩ := hpar
    obtain ⟨r2, hr2⟩ := h2
    exact ⟨r1 - r2, by linarith⟩
  obtain ⟨P, hPs, hPc⟩ := le_card_iff_exists_subset_card.mp
    (show Vo.card / 2 ≤ Vo.card by omega)
  have hPc2 : 2 * (P.card : ℤ) = Vo.card := by
    obtain ⟨r, hr⟩ := hVo_even
    have h1 : Vo.card % 2 = 0 := by omega
    have h2 : 2 * P.card = Vo.card := by rw [hPc]; omega
    exact_mod_cast h2
  let bb : V → ℤ := fun v => if v ∈ P then 1 else if v ∈ Vo then -1 else 0
  let NN : ℕ := Fintype.card V + 1
  let c : V → V → ℕ := fun a b => if K.Adj a b then NN else 0
  have hbsum : ∑ v, bb v = 0 := by
    have : ∑ v, bb v = ∑ v ∈ Vo, bb v := by
      symm; apply sum_subset (subset_univ _); intro x _ hx
      simp only [bb, hx, if_false]; split_ifs with h
      · exact absurd (hPs h) hx
      · rfl
    rw [this, ← sum_sdiff hPs]
    have e1 : ∑ v ∈ Vo \ P, bb v = - ((Vo \ P).card : ℤ) := by
      rw [card_eq_sum_ones, Nat.cast_sum, ← sum_neg_distrib]
      apply sum_congr rfl; intro x hx; rw [mem_sdiff] at hx; simp [bb, hx.1, hx.2]
    have e2 : ∑ v ∈ P, bb v = (P.card : ℤ) := by
      rw [card_eq_sum_ones, Nat.cast_sum]
      apply sum_congr rfl; intro x hx; simp [bb, hx]
    rw [e1, e2, card_sdiff_of_subset hPs]; push_cast [card_le_card hPs]; linarith
  have hcut : ∀ X : Finset V, ∑ x ∈ X, bb x ≤ cutCap c X := by
    intro X
    by_cases hcr : ∃ u v, K.Adj u v ∧ u ∈ X ∧ v ∉ X
    · obtain ⟨u, v, huv, hu, hv⟩ := hcr
      have h1 : (NN : ℤ) ≤ cutCap c X := by
        unfold cutCap
        have := single_le_sum (f := fun a => ∑ b, if a ∈ X ∧ b ∉ X then (c a b : ℤ) else 0)
          (fun a _ => sum_nonneg fun b _ => by split_ifs <;> simp) (mem_univ u)
        refine le_trans ?_ this
        have := single_le_sum (f := fun b => if u ∈ X ∧ b ∉ X then (c u b : ℤ) else 0)
          (fun b _ => by split_ifs <;> simp) (mem_univ v)
        refine le_trans ?_ this
        simp [hu, hv, c, huv]
      have h2 : ∑ x ∈ X, bb x ≤ X.card := by
        rw [card_eq_sum_ones, Nat.cast_sum]
        apply sum_le_sum; intro x _; simp only [bb]; split_ifs <;> simp
      have h3 : (X.card : ℤ) ≤ NN := by
        have := card_le_univ X; simp only [NN]; push_cast; omega
      linarith
    · push Not at hcr
      have hall : (∀ v ∈ Vo, v ∈ X) ∨ (∀ v ∈ Vo, v ∉ X) := by
        by_contra hh
        push Not at hh
        obtain ⟨⟨a, haV, haX⟩, ⟨b, hbV, hbX⟩⟩ := hh
        have hsub : Vo ⊆ B ∪ Rp := by
          intro x hx; simp only [Vo, mem_union, mem_filter] at hx ⊢; tauto
        obtain ⟨u, v, huv, hu, hv⟩ := reach_cross K X (hconn b (hsub hbV) a (hsub haV)) hbX haX
        exact hv (hcr u v huv hu)
      have hcap := cutCap_nonneg c X
      rcases hall with hall | hall
      · have : ∑ x ∈ X, bb x = ∑ v, bb v := by
          apply sum_subset (subset_univ _); intro x _ hx
          have : x ∉ Vo := fun h => hx (hall x h)
          simp only [bb, this, if_false]; split_ifs with h
          · exact absurd (hPs h) this
          · rfl
        rw [this, hbsum]; exact hcap
      · have : ∑ x ∈ X, bb x = 0 := by
          apply sum_eq_zero; intro x hx
          have : x ∉ Vo := fun h => hall x h hx
          simp only [bb, this, if_false]; split_ifs with h
          · exact absurd (hPs h) this
          · rfl
        rw [this]; exact hcap
  obtain ⟨φ, hφc, hφb⟩ := flow_exists _ c rfl bb hbsum hcut
  have hφ0 : ∀ a b, ¬ K.Adj a b → φ a b = 0 := by
    intro a b h; have := hφc a b; simp only [c, h, if_false] at this; omega
  -- odd edges
  let No : V → Finset V := fun v => univ.filter (fun u => K.Adj v u ∧ Odd ((φ v u : ℤ) + φ u v))
  have No_symm : ∀ v u, u ∈ No v ↔ v ∈ No u := by
    intro v u; simp only [No, mem_filter, mem_univ, true_and]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, by rwa [add_comm]⟩
  have No_par : ∀ v, Even ((No v).card - bb v) := by
    intro v
    have h1 := even_sum_sub_card_odd (univ.filter (K.Adj v)) (fun u => (φ v u : ℤ) + φ u v)
    have h2 : ∑ u ∈ univ.filter (K.Adj v), ((φ v u : ℤ) + φ u v) =
        ∑ u, ((φ v u : ℤ) + φ u v) := by
      rw [sum_filter]; apply sum_congr rfl; intro u _
      split_ifs with h
      · rfl
      · rw [hφ0 v u h, hφ0 u v (fun h' => h h'.symm)]; simp
    rw [h2, filter_filter] at h1
    have h3 := hφb v
    rw [sum_add_distrib] at h1
    obtain ⟨r, hr⟩ := h1
    refine ⟨∑ u, (φ u v : ℤ) - r, ?_⟩
    simp only [No]; linarith
  -- local choices
  have hloc : ∀ v, ∃ Q ⊆ No v, (v ∈ B → 2 * (Q.card : ℤ) - (No v).card = α v - 2 * dg v) ∧
      (v ∈ B → v ∈ pairOn → pa v ∈ No v → pc v ∈ No v → pa v ≠ pc v → (pa v ∈ Q ↔ pc v ∉ Q)) ∧
      (v ∈ B → v ∈ endOn → en v ∈ No v → (en v ∈ Q ↔ α v - 2 * dg v = 1)) := by
    intro v
    by_cases hv : v ∈ B
    · have hpv : Even (((No v).card : ℤ) - (α v - 2 * dg v)) := by
        have := No_par v
        have hbv : (bb v - α v) % 2 = 0 := by
          simp only [bb]
          by_cases h1 : v ∈ P
          · have : v ∈ Vo := hPs h1
            simp only [Vo, mem_union, mem_filter] at this
            have ho : Odd (α v) := by
              rcases this with h | h
              · exact absurd hv (disjoint_left.mp hRp h)
              · exact h.2
            obtain ⟨r, hr⟩ := ho; simp only [h1, if_true]; omega
          · simp only [h1, if_false]
            by_cases h2 : v ∈ Vo
            · have h2' := h2
              simp only [Vo, mem_union, mem_filter] at h2'
              have ho : Odd (α v) := by
                rcases h2' with h | h
                · exact absurd hv (disjoint_left.mp hRp h)
                · exact h.2
              obtain ⟨r, hr⟩ := ho
              simp only [h2, if_true]; omega
            · have : ¬ Odd (α v) := fun ho => h2 (by simp [Vo, hv, ho])
              have := Int.not_odd_iff_even.mp this
              obtain ⟨r, hr⟩ := this
              simp only [h2, if_false]; omega
        obtain ⟨r, hr⟩ := this
        refine ⟨r + dg v + (bb v - α v) / 2, ?_⟩
        omega
      obtain ⟨Q, hQs, h1, h2, h3⟩ := local_choice (No v) (α v - 2 * dg v) (hα v hv) hpv
        (pa v) (pc v) (en v) (v ∈ pairOn) (v ∈ endOn) (fun h => hpe v h.1 h.2)
      exact ⟨Q, hQs, fun _ => h1, fun _ hp ha hc hac => h2 hp ha hc hac, fun _ he hn => h3 he hn⟩
    · exact ⟨∅, empty_subset _, fun h => absurd h hv, fun h => absurd h hv, fun h => absurd h hv⟩
  choose Q hQs hQc hQp hQe using hloc
  let val : V → V → ℤ := fun v u => if u ∈ No v then (if u ∈ Q v then 1 else -1) else 0
  let W : V → V → ℤ := fun a b =>
    if a ∈ B ∧ b ∉ B then val a b else if b ∈ B ∧ a ∉ B then val b a else 0
  have Wsymm : ∀ a b, W a b = W b a := by
    intro a b; simp only [W]
    by_cases ha : a ∈ B <;> by_cases hb : b ∈ B <;> simp [ha, hb]
  let w : Sym2 V → ℤ := Sym2.lift ⟨fun a b => 2 + W a b, fun a b => by simp only [Wsymm a b]⟩
  have hw : ∀ a b, w s(a, b) = 2 + W a b := fun a b => rfl
  have hWB : ∀ v u, v ∈ B → K.Adj v u → W v u = val v u := by
    intro v u hv hvu
    have hu : u ∉ B := (hbip v u hvu).mp hv
    simp [W, hv, hu]
  have hWR : ∀ v u, v ∉ B → K.Adj v u → W v u = val u v := by
    intro v u hv hvu
    have hu : u ∈ B := by have := hbip v u hvu; tauto
    simp [W, hv, hu]
  have hval : ∀ v u, -1 ≤ val v u ∧ val v u ≤ 1 := by
    intro v u; simp only [val]; split_ifs <;> omega
  have hsd : ∀ v, sd K w v = 2 * dg v + ∑ u ∈ univ.filter (K.Adj v), W v u := by
    intro v; simp only [sd, hw, sum_add_distrib, sum_const, nsmul_eq_mul, dg]; ring
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    rw [hw]
    by_cases hu : u ∈ B
    · rw [hWB u v hu huv]; have := hval u v; omega
    · rw [hWR u v hu huv]; have := hval v u; omega
  · intro v hv
    rw [hsd]
    have h1 := even_sum_sub_card_odd (univ.filter (K.Adj v)) (fun u => W v u)
    have h2 : (univ.filter (K.Adj v)).filter (fun u => Odd (W v u)) = No v := by
      ext u
      simp only [mem_filter, mem_univ, true_and, No]
      constructor
      · rintro ⟨hvu, hodd⟩
        rw [hWR v u hv hvu] at hodd
        simp only [val] at hodd
        have : v ∈ No u := by
          by_contra hh; simp [hh] at hodd
        exact (No_symm u v).mp this |> fun h => by simpa [No] using h
      · rintro ⟨hvu, hodd⟩
        refine ⟨hvu, ?_⟩
        rw [hWR v u hv hvu]
        have : v ∈ No u := (No_symm v u).mp (by simp [No, hvu, hodd])
        simp only [val, this, if_true]; split_ifs
        · exact odd_one
        · exact ⟨-1, by norm_num⟩
    rw [h2] at h1
    have h3 := No_par v
    have hbv : (Odd (bb v) ↔ v ∈ Rp) := by
      simp only [bb]
      by_cases h1 : v ∈ P
      · have : v ∈ Vo := hPs h1
        simp only [Vo, mem_union, mem_filter] at this
        have hR : v ∈ Rp := by tauto
        simp [h1, hR]
      · by_cases h2 : v ∈ Vo
        · have hR : v ∈ Rp := by simp only [Vo, mem_union, mem_filter] at h2; tauto
          simp only [h1, h2, if_false, if_true, hR, iff_true]; exact ⟨-1, by norm_num⟩
        · have hR : v ∉ Rp := fun h => h2 (by simp [Vo, h])
          simp [h1, h2, hR]
    rw [← hbv]
    obtain ⟨r1, hr1⟩ := h1
    obtain ⟨r2, hr2⟩ := h3
    constructor
    · rintro ⟨r, hr⟩; exact ⟨r - dg v - r1 - r2, by linarith⟩
    · rintro ⟨r, hr⟩; exact ⟨r + dg v + r1 + r2, by linarith⟩
  · intro v hv
    rw [hsd]
    have : ∑ u ∈ univ.filter (K.Adj v), W v u = α v - 2 * dg v := by
      rw [sum_congr rfl (fun u hu => hWB v u hv (mem_filter.mp hu).2)]
      have hsplit : ∑ u ∈ univ.filter (K.Adj v), val v u = ∑ u ∈ No v, val v u := by
        symm; apply sum_subset
        · intro u hu; simp only [No, mem_filter] at hu ⊢; exact ⟨hu.1, hu.2.1⟩
        · intro u _ hu; simp [val, hu]
      rw [hsplit, ← sum_sdiff (hQs v)]
      have e1 : ∑ u ∈ No v \ Q v, val v u = - ((No v \ Q v).card : ℤ) := by
        rw [card_eq_sum_ones, Nat.cast_sum, ← sum_neg_distrib]
        apply sum_congr rfl; intro x hx; rw [mem_sdiff] at hx; simp [val, hx.1, hx.2]
      have e2 : ∑ u ∈ Q v, val v u = ((Q v).card : ℤ) := by
        rw [card_eq_sum_ones, Nat.cast_sum]
        apply sum_congr rfl; intro x hx; simp [val, hx, hQs v hx]
      rw [e1, e2, card_sdiff_of_subset (hQs v)]
      have := hQc v hv
      push_cast [card_le_card (hQs v)]; linarith
    rw [this]; ring
  · intro v hv hpo hne hva hvc
    rw [hw, hw, hWB v _ hv hva, hWB v _ hv hvc]
    have h1 := hval v (pa v)
    have h2 := hval v (pc v)
    by_cases ha : pa v ∈ No v
    · by_cases hc : pc v ∈ No v
      · have := hQp v hv hpo ha hc hne
        simp only [val, ha, hc, if_true]
        by_cases hq : pa v ∈ Q v
        · have : pc v ∉ Q v := this.mp hq
          simp [hq, this]
        · have : pc v ∈ Q v := by tauto
          simp [hq, this]
      · simp only [val, hc, if_false] at h2 ⊢; omega
    · simp only [val, ha, if_false] at h1 ⊢; omega
  · intro v hv hen hve
    rw [hw, hWB v _ hv hve]
    by_cases hn : en v ∈ No v
    · have := hQe v hv hen hn
      constructor
      · intro h; simp only [val, hn, if_true]
        have : en v ∈ Q v := this.mpr (by simp only [dg] at *; omega)
        simp [this]
      · intro h; simp only [val, hn, if_true]
        have : en v ∉ Q v := fun hq => h (by have := this.mp hq; simp only [dg] at *; omega)
        simp [this]
    · simp [val, hn]

end Between
section Framework
variable {V : Type} [Fintype V] [DecidableEq V]

/-- the bipartite subgraph between `R` and `B` -/
def bip (G : SimpleGraph V) (R B : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ((a ∈ R ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ R))
  symm := ⟨fun a b h => ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨fun a h => G.ne_of_adj h.1 rfl⟩

instance bip_dec (G : SimpleGraph V) [DecidableRel G.Adj] (R B : Finset V) :
    DecidableRel (bip G R B).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj a b ∧ ((a ∈ R ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ R))))

@[simp] lemma bip_adj (G : SimpleGraph V) (R B : Finset V) (a b : V) :
    (bip G R B).Adj a b ↔ G.Adj a b ∧ ((a ∈ R ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ R)) := Iff.rfl

/-- the subgraph induced on `B` -/
def indB (G : SimpleGraph V) (B : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ B ∧ b ∈ B
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.ne_of_adj h.1 rfl⟩

instance indB_dec (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    DecidableRel (indB G B).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj a b ∧ a ∈ B ∧ b ∈ B))

@[simp] lemma indB_adj (G : SimpleGraph V) (B : Finset V) (a b : V) :
    (indB G B).Adj a b ↔ G.Adj a b ∧ a ∈ B ∧ b ∈ B := Iff.rfl

/-- a good red-blue partition -/
structure Good (G : SimpleGraph V) (R B : Finset V) : Prop where
  disj : Disjoint R B
  indep : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b
  conn : ∀ a ∈ R ∪ B, ∀ b ∈ R ∪ B, (bip G R B).Reachable a b
  even : Even B.card
  supp : ∀ a b, G.Adj a b → a ∈ R ∪ B

lemma sd_split (G H1 H2 : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H1.Adj]
    [DecidableRel H2.Adj] (w w1 w2 : Sym2 V → ℤ) (v : V)
    (h : ∀ u, (if G.Adj v u then w s(v, u) else 0) =
      (if H1.Adj v u then w1 s(v, u) else 0) + (if H2.Adj v u then w2 s(v, u) else 0)) :
    sd G w v = sd H1 w1 v + sd H2 w2 v := by
  simp only [sd, sum_filter]; rw [← sum_add_distrib]; exact sum_congr rfl (fun u _ => h u)

lemma even_sum_of_odd (s : Finset V) (f : V → ℤ) (hf : ∀ v ∈ s, Odd (f v))
    (hs : Even s.card) : Even (∑ v ∈ s, f v) := by
  have h := even_sum_sub_card_odd s f
  have : s.filter (fun u => Odd (f u)) = s := filter_true_of_mem hf
  rw [this] at h
  obtain ⟨r, hr⟩ := h
  obtain ⟨q, hq⟩ := hs
  exact ⟨r + q, by push_cast [hq] at hr; linarith⟩

/-- combine two weightings: `w1` inside `B`, `w2` elsewhere -/
def comb (B : Finset V) (w1 w2 : Sym2 V → ℤ) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun a b => if a ∈ B ∧ b ∈ B then w1 s(a, b) else w2 s(a, b), fun a b => by
    simp only [Sym2.eq_swap (a := a) (b := b), and_comm]⟩

lemma comb_mk (B : Finset V) (w1 w2 : Sym2 V → ℤ) (a b : V) :
    comb B w1 w2 s(a, b) = if a ∈ B ∧ b ∈ B then w1 s(a, b) else w2 s(a, b) := rfl

/-- the first two steps shared by the three basic situations: Lemma 2 on `B`. -/
lemma blue_step (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) (o : V → ℤ)
    (ho : ∀ v, Even (o v)) :
    ∃ (w1 : Sym2 V → ℤ) (f : V → ℤ),
      (∀ u v, (indB G B).Adj u v → 1 ≤ w1 s(u, v) ∧ w1 s(u, v) ≤ 3) ∧
      (∀ v, Odd (f v)) ∧ (∀ u v, (indB G B).Adj u v → f u ≠ f v) ∧
      ∀ v, |f v - sd (indB G B) w1 v - o v -
        2 * ((univ.filter (fun u => G.Adj v u ∧ u ∉ B)).card : ℤ)| = 1 := by
  obtain ⟨w1, f, h1, h2, h3, h4⟩ := weighting (indB G B)
    (fun v => 2 * ((univ.filter (fun u => G.Adj v u ∧ u ∉ B)).card : ℤ) + o v)
    (fun v => by obtain ⟨r, hr⟩ := ho v; exact ⟨_ + r, by rw [hr]; ring⟩)
  refine ⟨w1, f, h1, h2, h3, fun v => ?_⟩
  have := h4 v
  rw [← abs_neg]; convert this using 2; ring

theorem basic (G : SimpleGraph V) [DecidableRel G.Adj] (R B : Finset V) (hg : Good G R B)
    (o : V → ℤ) (ho : ∀ v, Even (o v)) :
    ∃ w : Sym2 V → ℤ, (∀ u v, G.Adj u v → 1 ≤ w s(u, v) ∧ w s(u, v) ≤ 3) ∧
      (∀ v ∈ B, Odd (sd G w v + o v)) ∧ (∀ v ∈ R, Even (sd G w v)) ∧
      (∀ u ∈ B, ∀ v ∈ B, G.Adj u v → sd G w u + o u ≠ sd G w v + o v) := by
  obtain ⟨w1, f, hw1, hfo, hfp, hfd⟩ := blue_step G B o ho
  have hdegK : ∀ v ∈ B, (univ.filter ((bip G R B).Adj v)).card =
      (univ.filter (fun u => G.Adj v u ∧ u ∉ B)).card := by
    intro v hv; congr 1; ext u
    simp only [mem_filter, mem_univ, true_and, bip_adj]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rcases h2 with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd hv (disjoint_left.mp hg.disj h)
      · exact disjoint_left.mp hg.disj h
    · rintro ⟨h1, h2⟩
      refine ⟨h1, Or.inr ⟨hv, ?_⟩⟩
      have := hg.supp u v h1.symm
      simp only [mem_union] at this; tauto
  let α : V → ℤ := fun v => f v - sd (indB G B) w1 v - o v
  have hα : ∀ v ∈ B, |α v - 2 * ((univ.filter ((bip G R B).Adj v)).card : ℤ)| = 1 := by
    intro v hv; rw [hdegK v hv]; exact hfd v
  have hαodd : ∀ v ∈ B, Odd (α v) := by
    intro v hv
    have := hα v hv
    rcases abs_eq (zero_le_one) |>.mp this with h | h
    · exact ⟨((univ.filter ((bip G R B).Adj v)).card : ℤ), by linarith⟩
    · exact ⟨((univ.filter ((bip G R B).Adj v)).card : ℤ) - 1, by linarith⟩
  have hRB : ∀ x, x ∈ R → x ∉ B := fun x hx => disjoint_left.mp hg.disj hx
  have hbip : ∀ u v, (bip G R B).Adj u v → (u ∈ B ↔ v ∉ B) := by
    intro u v ⟨_, h⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun h => absurd h (hRB u h1), fun h => absurd h2 h⟩
    · exact ⟨fun _ => hRB v h2, fun _ => h1⟩
  have hpar : Even (((∅ : Finset V).card : ℤ) + ∑ v ∈ B, α v) := by
    simp only [card_empty, Nat.cast_zero, zero_add]
    exact even_sum_of_odd B α hαodd hg.even
  obtain ⟨w2, hw2, hw2R, hw2B, -, -⟩ := between (bip G R B) B ∅ hbip (disjoint_empty_left _) α
    (fun v hv => (hα v hv).le) hpar
    (fun a ha b hb => hg.conn a (by simp at ha ⊢; tauto) b (by simp at hb ⊢; tauto))
    id id id ∅ ∅ (fun v h => absurd h (notMem_empty v))
  have hsplit : ∀ v ∈ R ∪ B, sd G (comb B w1 w2) v = sd (indB G B) w1 v + sd (bip G R B) w2 v := by
    intro v hv
    apply sd_split
    intro u
    by_cases hvu : G.Adj v u
    · have hu := hg.supp u v hvu.symm
      simp only [mem_union] at hv hu
      by_cases hvB : v ∈ B
      · by_cases huB : u ∈ B
        · have h1 : v ∉ R := fun h => hRB v h hvB
          have h2 : u ∉ R := fun h => hRB u h huB
          simp [hvu, comb_mk, hvB, huB, h1, h2]
        · have huR : u ∈ R := by tauto
          simp [hvu, comb_mk, hvB, huB, huR]
      · have hvR : v ∈ R := by tauto
        have huB : u ∈ B := by
          by_contra hh; exact hg.indep v hvR u (by tauto) hvu
        simp [hvu, comb_mk, hvB, huB, hvR]
    · simp [hvu]
  refine ⟨comb B w1 w2, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    rw [comb_mk]
    split_ifs with h
    · exact hw1 u v ⟨huv, h.1, h.2⟩
    · apply hw2
      have hu := hg.supp u v huv
      have hv := hg.supp v u huv.symm
      simp only [mem_union] at hu hv
      refine ⟨huv, ?_⟩
      by_cases huB : u ∈ B
      · have : v ∉ B := fun hv => h ⟨huB, hv⟩
        right; exact ⟨huB, by tauto⟩
      · left; refine ⟨by tauto, ?_⟩
        by_contra hvB
        exact hg.indep u (by tauto) v (by tauto) huv
  · intro v hv
    rw [hsplit v (by simp [hv]), hw2B v hv]
    simp only [α]; ring_nf; exact hfo v
  · intro v hv
    rw [hsplit v (by simp [hv])]
    have h1 : sd (indB G B) w1 v = 0 := by
      apply sum_eq_zero; intro u hu; simp only [mem_filter, indB_adj] at hu
      exact absurd hu.2.2.1 (hRB v hv)
    have h2 := hw2R v (hRB v hv)
    rw [h1, zero_add]
    exact Int.not_odd_iff_even.mp (fun ho => by simpa using h2.mp ho)
  · intro u hu v hv huv
    rw [hsplit u (by simp [hu]), hsplit v (by simp [hv]), hw2B u hu, hw2B v hv]
    simp only [α]; ring_nf
    exact hfp u v ⟨huv, hu, hv⟩

end Framework
section Comb
variable {V : Type} [Fintype V] [DecidableEq V]

lemma comb_choice_of_m (A : Finset V) (b : V → ℤ) (m : ℤ) (hm0 : 0 ≤ m)
    (h1 : ((A.filter (fun r => b r = m)).card : ℤ) ≤ m)
    (h2 : ((A.filter (fun r => b r = m - 1)).card : ℤ) + m ≤ A.card) :
    ∃ U ⊆ A, ∀ r ∈ A, (U.card : ℤ) ≠ b r + (if r ∈ U then 1 else 0) := by
  set F1 := A.filter (fun r => b r = m)
  set F2 := A.filter (fun r => b r = m - 1)
  have hdisj : Disjoint F1 F2 := by
    rw [disjoint_left]; intro r h1 h2
    simp only [F1, F2, mem_filter] at h1 h2; omega
  have hrest : (m - F1.card).toNat ≤ (A \ (F1 ∪ F2)).card := by
    have hsub : F1 ∪ F2 ⊆ A := union_subset (filter_subset _ _) (filter_subset _ _)
    rw [card_sdiff_of_subset hsub, card_union_of_disjoint hdisj]
    have := card_le_card hsub
    rw [card_union_of_disjoint hdisj] at this
    omega
  obtain ⟨W, hWs, hWc⟩ := le_card_iff_exists_subset_card.mp hrest
  have hWd : Disjoint F1 W := by
    rw [disjoint_left]; intro r h1 h2
    have := hWs h2; simp only [mem_sdiff, mem_union] at this; tauto
  refine ⟨F1 ∪ W, union_subset (filter_subset _ _) (fun r hr => (mem_sdiff.mp (hWs hr)).1), ?_⟩
  have hcard : ((F1 ∪ W).card : ℤ) = m := by
    rw [card_union_of_disjoint hWd, hWc]; push_cast; omega
  intro r hr
  rw [hcard]
  by_cases hU : r ∈ F1 ∪ W
  · rw [if_pos hU]
    rcases mem_union.mp hU with h | h
    · simp only [F1, mem_filter] at h; omega
    · have := hWs h
      simp only [mem_sdiff, mem_union, F1, F2, mem_filter, not_or] at this
      have := this.2.2; intro hh; apply this; exact ⟨hr, by omega⟩
  · rw [if_neg hU]
    intro hh
    apply hU; apply mem_union_left; simp only [F1, mem_filter]; exact ⟨hr, by omega⟩

lemma comb_choice (A : Finset V) (hA : 2 ≤ A.card) (b : V → ℤ) :
    ∃ U ⊆ A, ∀ r ∈ A, (U.card : ℤ) ≠ b r + (if r ∈ U then 1 else 0) := by
  set k := A.card with hk
  let n : ℤ → ℕ := fun t => (A.filter (fun r => b r = t)).card
  have Lfib : ∀ T : Finset ℤ, ∑ t ∈ T, n t ≤ k := by
    intro T
    have := card_eq_sum_card_fiberwise (s := A.filter (fun r => b r ∈ T)) (t := T) (f := b)
      (fun r hr => (mem_filter.mp hr).2)
    have e : ∀ t ∈ T, ((A.filter (fun r => b r ∈ T)).filter (fun r => b r = t)).card = n t := by
      intro t ht; congr 1; ext r; simp only [mem_filter]; constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ ht⟩, h3⟩
    rw [sum_congr rfl e] at this
    rw [← this]; exact card_le_card (filter_subset _ _)
  have Lsum : ∀ (T : Finset ℤ) (j : ℤ), j ∈ T → (∀ t ∈ T, 1 ≤ n t) →
      n j + (T.card - 1) ≤ ∑ t ∈ T, n t := by
    intro T j hj h1
    rw [← add_sum_erase T n hj]
    have : (T.erase j).card ≤ ∑ t ∈ T.erase j, n t := by
      rw [card_eq_sum_ones]; exact sum_le_sum fun t ht => h1 t (mem_of_mem_erase ht)
    rw [card_erase_of_mem hj] at this; omega
  have hnk : ∀ t, n t ≤ k := fun t => card_le_card (filter_subset _ _)
  by_cases h0 : n 0 = 0
  · exact comb_choice_of_m A b 0 le_rfl (by simp only [n] at h0; simp [h0])
      (by have := hnk (0 - 1); simp only [n] at this ⊢; omega)
  have hex : ∃ t : ℕ, 1 ≤ t ∧ n (t : ℤ) = 0 := by
    by_contra hno
    push Not at hno
    have hall : ∀ t ∈ Icc (0 : ℤ) (k + 1), 1 ≤ n t := by
      intro t ht
      simp only [mem_Icc] at ht
      by_cases ht0 : t = 0
      · subst ht0; omega
      · have := hno t.toNat (by omega)
        rw [Int.toNat_of_nonneg ht.1] at this; omega
    have := Lsum (Icc (0 : ℤ) (k + 1)) 0 (by simp; omega) hall
    have := Lfib (Icc (0 : ℤ) (k + 1))
    simp only [Int.card_Icc] at *; omega
  classical
  let x := Nat.find hex
  have hx : 1 ≤ x ∧ n (x : ℤ) = 0 := Nat.find_spec hex
  have hxmin : ∀ t : ℕ, t < x → 1 ≤ t → 1 ≤ n t := by
    intro t ht h1
    have := Nat.find_min hex ht
    push Not at this
    have := this h1; omega
  have hpos : ∀ t ∈ Icc (0 : ℤ) (x - 1), 1 ≤ n t := by
    intro t ht
    simp only [mem_Icc] at ht
    by_cases ht0 : t = 0
    · subst ht0; omega
    · have := hxmin t.toNat (by omega) (by omega)
      rw [Int.toNat_of_nonneg ht.1] at this; exact this
  have hxk : (x : ℤ) ≤ k := by
    have h1 := Lsum (Icc (0 : ℤ) (x - 1)) 0 (by simp; omega) hpos
    have h2 := Lfib (Icc (0 : ℤ) (x - 1))
    simp only [Int.card_Icc] at h1; omega
  by_cases hA1 : ((n ((x : ℤ) - 1)) : ℤ) + x ≤ k
  · exact comb_choice_of_m A b x (by omega) (by simp only [n] at hx ⊢; omega) hA1
  push Not at hA1
  by_cases hxk1 : (x : ℤ) + 1 ≤ k
  · -- m = x + 1
    have hnx1 : n ((x : ℤ) + 1) = 0 := by
      have h1 := Lsum (Icc (0 : ℤ) (x - 1)) ((x : ℤ) - 1) (by simp; omega) hpos
      have hnot : (x : ℤ) + 1 ∉ Icc (0 : ℤ) (x - 1) := by simp
      have h2 := Lfib (insert ((x : ℤ) + 1) (Icc (0 : ℤ) (x - 1)))
      rw [sum_insert hnot] at h2
      simp only [Int.card_Icc] at h1; omega
    exact comb_choice_of_m A b ((x : ℤ) + 1) (by omega) (by simp only [n] at hnx1 ⊢; omega)
      (by have := hx.2; simp only [n, add_sub_cancel_right] at this ⊢; omega)
  · -- x = k, all fibres on [0, k-1] are singletons; m = 1
    have hxk' : (x : ℤ) = k := by omega
    have hb : ∀ j ∈ Icc (0 : ℤ) (x - 1), n j ≤ 1 := by
      intro j hj
      have h1 := Lsum (Icc (0 : ℤ) (x - 1)) j hj hpos
      have h2 := Lfib (Icc (0 : ℤ) (x - 1))
      simp only [Int.card_Icc] at h1; omega
    have e1 := hb 1 (by simp; omega)
    have e0 := hb 0 (by simp; omega)
    exact comb_choice_of_m A b 1 (by omega) (by simp only [n] at e1 ⊢; omega)
      (by simp only [n, sub_self] at e0 ⊢; omega)

end Comb
section Remaining
variable {V : Type} [Fintype V] [DecidableEq V]

/-- a vertex-colouring weighting with weights in `[1,3]` -/
def VC (G : SimpleGraph V) [DecidableRel G.Adj] (w : Sym2 V → ℤ) : Prop :=
  (∀ u v, G.Adj u v → 1 ≤ w s(u, v) ∧ w s(u, v) ≤ 3) ∧ ∀ u v, G.Adj u v → sd G w u ≠ sd G w v

lemma comb_pt (G : SimpleGraph V) [DecidableRel G.Adj] (R B : Finset V) (hdisj : Disjoint R B)
    (hind : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b) (w1 w2 : Sym2 V → ℤ) (v u : V)
    (hv : v ∈ R ∪ B) (hu : u ∈ R ∪ B) (hvu : G.Adj v u) :
    comb B w1 w2 s(v, u) = (if (indB G B).Adj v u then w1 s(v, u) else 0) +
      (if (bip G R B).Adj v u then w2 s(v, u) else 0) := by
  have hRB : ∀ x, x ∈ R → x ∉ B := fun x hx => disjoint_left.mp hdisj hx
  simp only [mem_union] at hv hu
  by_cases hvB : v ∈ B
  · by_cases huB : u ∈ B
    · have h1 : v ∉ R := fun h => hRB v h hvB
      have h2 : u ∉ R := fun h => hRB u h huB
      simp [hvu, comb_mk, hvB, huB, h1, h2]
    · have huR : u ∈ R := by tauto
      simp [hvu, comb_mk, hvB, huB, huR]
  · have hvR : v ∈ R := by tauto
    have huB : u ∈ B := by
      by_contra hh; exact hind v hvR u (by tauto) hvu
    simp [hvu, comb_mk, hvB, huB, hvR]

lemma comb_wt (G : SimpleGraph V) [DecidableRel G.Adj] (R B : Finset V)
    (hind : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b) (w1 w2 : Sym2 V → ℤ)
    (hw1 : ∀ u v, (indB G B).Adj u v → 1 ≤ w1 s(u, v) ∧ w1 s(u, v) ≤ 3)
    (hw2 : ∀ u v, (bip G R B).Adj u v → 1 ≤ w2 s(u, v) ∧ w2 s(u, v) ≤ 3)
    (u v : V) (hu : u ∈ R ∪ B) (hv : v ∈ R ∪ B) (huv : G.Adj u v) :
    1 ≤ comb B w1 w2 s(u, v) ∧ comb B w1 w2 s(u, v) ≤ 3 := by
  rw [comb_mk]
  split_ifs with h
  · exact hw1 u v ⟨huv, h.1, h.2⟩
  · apply hw2
    simp only [mem_union] at hu hv
    refine ⟨huv, ?_⟩
    by_cases huB : u ∈ B
    · have : v ∉ B := fun hv => h ⟨huB, hv⟩
      right; exact ⟨huB, by tauto⟩
    · left; refine ⟨by tauto, ?_⟩
      by_contra hvB
      exact hind u (by tauto) v (by tauto) huv

/-- a weighting that is `c3` on the edges at `v0` and `w` elsewhere -/
def atv (v0 : V) (c3 : V → ℤ) (w : Sym2 V → ℤ) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun a b => if a = v0 then c3 b else if b = v0 then c3 a else w s(a, b),
    fun a b => by
      by_cases ha : a = v0 <;> by_cases hb : b = v0 <;> simp [ha, hb, Sym2.eq_swap]⟩

lemma atv_mk (v0 : V) (c3 : V → ℤ) (w : Sym2 V → ℤ) (a b : V) :
    atv v0 c3 w s(a, b) = if a = v0 then c3 b else if b = v0 then c3 a else w s(a, b) := rfl

lemma sd_atv_v0 (G : SimpleGraph V) [DecidableRel G.Adj] (v0 : V) (c3 : V → ℤ)
    (w : Sym2 V → ℤ) : sd G (atv v0 c3 w) v0 = ∑ u ∈ univ.filter (G.Adj v0), c3 u := by
  simp only [sd, atv_mk, if_true]

lemma sd_atv (G : SimpleGraph V) [DecidableRel G.Adj] (R B : Finset V) (hdisj : Disjoint R B)
    (hind : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b) (v0 : V) (hv0 : v0 ∉ R ∪ B)
    (hsupp : ∀ a b, G.Adj a b → a ≠ v0 → a ∈ R ∪ B) (c3 : V → ℤ) (w1 w2 : Sym2 V → ℤ)
    (v : V) (hv : v ∈ R ∪ B) :
    sd G (atv v0 c3 (comb B w1 w2)) v = sd (indB G B) w1 v + sd (bip G R B) w2 v +
      (if G.Adj v v0 then c3 v else 0) := by
  have hvv0 : v ≠ v0 := fun h => hv0 (h ▸ hv)
  have pt : ∀ u, (if G.Adj v u then atv v0 c3 (comb B w1 w2) s(v, u) else 0) =
      (if (indB G B).Adj v u then w1 s(v, u) else 0) +
      (if (bip G R B).Adj v u then w2 s(v, u) else 0) +
      (if u = v0 then (if G.Adj v v0 then c3 v else 0) else 0) := by
    intro u
    by_cases hu0 : u = v0
    · subst hu0
      have h1 : ¬ (indB G B).Adj v u := fun h => hv0 (mem_union_right _ h.2.2)
      have h2 : ¬ (bip G R B).Adj v u := fun h => by
        rcases h.2 with h | h
        · exact hv0 (mem_union_right _ h.2)
        · exact hv0 (mem_union_left _ h.2)
      rw [if_neg h1, if_neg h2]; simp [atv_mk, hvv0]
    · by_cases hvu : G.Adj v u
      · have hu := hsupp u v hvu.symm hu0
        rw [if_pos hvu, atv_mk, if_neg hvv0, if_neg hu0, comb_pt G R B hdisj hind w1 w2 v u hv hu hvu]
        simp [hu0]
      · have h1 : ¬ (indB G B).Adj v u := fun h => hvu h.1
        have h2 : ¬ (bip G R B).Adj v u := fun h => hvu h.1
        simp [hvu, h1, h2, hu0]
  simp only [sd, sum_filter]
  rw [sum_congr rfl (fun u _ => pt u), sum_add_distrib, sum_add_distrib, sum_ite_eq']
  simp

/-- Keusch, Lemma 6: one extra vertex with at least two red neighbours. -/
theorem remaining (G : SimpleGraph V) [DecidableRel G.Adj] (v0 : V) (R B : Finset V)
    (hdisj : Disjoint R B) (hv0 : v0 ∉ R ∪ B) (hind : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b)
    (hconn : ∀ a ∈ R ∪ B, ∀ b ∈ R ∪ B, (bip G R B).Reachable a b) (heven : Even B.card)
    (hsupp : ∀ a b, G.Adj a b → a ≠ v0 → a ∈ R ∪ B)
    (hk : 2 ≤ (univ.filter (fun u => G.Adj v0 u ∧ u ∈ R)).card)
    (hpar : Even (univ.filter (fun u => G.Adj v0 u ∧ u ∈ R)).card ∨
      1 ≤ (univ.filter (fun u => G.Adj v0 u ∧ u ∈ B)).card) :
    ∃ w, VC G w := by
  have hRB : ∀ x, x ∈ R → x ∉ B := fun x hx => disjoint_left.mp hdisj hx
  obtain ⟨w1, f, hw1, hfo, hfp, hfd⟩ := blue_step G B (fun _ => 0) (fun _ => ⟨0, by ring⟩)
  set NR := univ.filter (fun u => G.Adj v0 u ∧ u ∈ R) with hNR
  set NB := univ.filter (fun u => G.Adj v0 u ∧ u ∈ B) with hNB
  set kk := NR.card with hkk
  let dR : V → ℤ := fun v => ((univ.filter (fun u => G.Adj v u ∧ u ∈ R)).card : ℤ)
  have hdK : ∀ v ∈ B, ((univ.filter ((bip G R B).Adj v)).card : ℤ) = dR v := by
    intro v hv; simp only [dR]; congr 2; ext u
    simp only [mem_filter, mem_univ, true_and, bip_adj]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rcases h2 with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd hv (hRB v h)
      · exact h
    · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr ⟨hv, h2⟩⟩
  have hdout : ∀ v ∈ B, ((univ.filter (fun u => G.Adj v u ∧ u ∉ B)).card : ℤ) =
      dR v + (if G.Adj v v0 then 1 else 0) := by
    intro v hv
    have hsplit : univ.filter (fun u => G.Adj v u ∧ u ∉ B) =
        univ.filter (fun u => G.Adj v u ∧ u ∈ R) ∪ univ.filter (fun u => G.Adj v u ∧ u = v0) := by
      ext u; simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hu0 : u = v0
        · exact Or.inr ⟨h1, hu0⟩
        · have := hsupp u v h1.symm hu0
          simp only [mem_union] at this; left; exact ⟨h1, by tauto⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, hRB u h2⟩
        · exact ⟨h1, fun h => hv0 (h2 ▸ mem_union_right _ h)⟩
    have hdj : Disjoint (univ.filter (fun u => G.Adj v u ∧ u ∈ R))
        (univ.filter (fun u => G.Adj v u ∧ u = v0)) := by
      rw [disjoint_left]; intro u h1 h2
      simp only [mem_filter] at h1 h2
      exact hv0 (h2.2.2 ▸ mem_union_left _ h1.2.2)
    rw [hsplit, card_union_of_disjoint hdj]
    have : univ.filter (fun u => G.Adj v u ∧ u = v0) = if G.Adj v v0 then {v0} else ∅ := by
      ext u; split_ifs with h <;> simp only [mem_filter, mem_univ, true_and, mem_singleton,
        notMem_empty, iff_false, not_and] <;> [exact ⟨fun h' => h'.2, fun h' => ⟨h' ▸ h, h'⟩⟩;
        exact fun h' h'' => h (h'' ▸ h')]
    rw [this]; split_ifs <;> simp [dR]
  have hfd' : ∀ v ∈ B, |f v - sd (indB G B) w1 v - 2 * dR v - 2 * (if G.Adj v v0 then 1 else 0)| = 1 := by
    intro v hv
    have := hfd v
    rw [hdout v hv] at this
    convert this using 2; ring
  -- the special blue neighbour
  obtain ⟨u0, hu0⟩ : ∃ u0, Odd kk → u0 ∈ NB := by
    by_cases ho : Odd kk
    · rcases hpar with h | h
      · exact absurd h (Nat.not_even_iff_odd.mpr ho)
      · obtain ⟨u0, hu⟩ := card_pos.mp h
        exact ⟨u0, fun _ => hu⟩
    · exact ⟨v0, fun h => absurd h ho⟩
  let cor : V → ℤ := fun v => if G.Adj v v0 then
    (if Odd kk ∧ v = u0 then f v - sd (indB G B) w1 v - 2 * dR v else 2) else 0
  let α : V → ℤ := fun v => f v - sd (indB G B) w1 v - cor v
  have hcor : ∀ v, cor v = if G.Adj v v0 then
      (if Odd kk ∧ v = u0 then f v - sd (indB G B) w1 v - 2 * dR v else 2) else 0 := fun v => rfl
  have hα : ∀ v ∈ B, |α v - 2 * ((univ.filter ((bip G R B).Adj v)).card : ℤ)| ≤ 1 := by
    intro v hv
    rw [hdK v hv]
    have := hfd' v hv
    rw [abs_eq zero_le_one] at this
    have hαv : α v = f v - sd (indB G B) w1 v - cor v := rfl
    rw [hαv, hcor v, abs_le]
    by_cases h1 : G.Adj v v0
    · rw [if_pos h1]; rw [if_pos h1] at this
      by_cases h2 : Odd kk ∧ v = u0
      · rw [if_pos h2]; omega
      · rw [if_neg h2]; omega
    · rw [if_neg h1]; rw [if_neg h1] at this; omega
  have hαodd : ∀ v ∈ B, ¬ (Odd kk ∧ v = u0) → Odd (α v) := by
    intro v hv hns
    have := hfd' v hv
    rw [abs_eq zero_le_one] at this
    have hαv : α v = f v - sd (indB G B) w1 v - cor v := rfl
    rw [hαv, hcor v]
    by_cases h1 : G.Adj v v0
    · rw [if_pos h1, if_neg hns]; rw [if_pos h1] at this
      rcases this with h | h
      · exact ⟨dR v, by omega⟩
      · exact ⟨dR v - 1, by omega⟩
    · rw [if_neg h1]; rw [if_neg h1] at this
      rcases this with h | h
      · exact ⟨dR v, by omega⟩
      · exact ⟨dR v - 1, by omega⟩
  have hpar' : Even ((NR.card : ℤ) + ∑ v ∈ B, α v) := by
    by_cases ho : Odd kk
    · have hu0B : u0 ∈ B := (mem_filter.mp (hu0 ho)).2.2
      have hu0adj : G.Adj u0 v0 := (mem_filter.mp (hu0 ho)).2.1.symm
      rw [← add_sum_erase B α hu0B]
      have h1 : α u0 = 2 * dR u0 := by simp [α, cor, hu0adj, ho]
      have h2 := even_sum_sub_card_odd (B.erase u0) α
      rw [filter_true_of_mem (fun v hv => hαodd v (mem_of_mem_erase hv)
        (fun h => (ne_of_mem_erase hv) h.2)), card_erase_of_mem hu0B] at h2
      obtain ⟨r, hr⟩ := h2
      obtain ⟨q, hq⟩ := ho
      obtain ⟨p, hp⟩ := heven
      have hB1 : 1 ≤ B.card := card_pos.mpr ⟨u0, hu0B⟩
      refine ⟨q + dR u0 + r + p, ?_⟩
      rw [h1]; push_cast [Nat.cast_sub hB1] at hr; rw [← hkk, hq]; push_cast; omega
    · have := even_sum_of_odd B α (fun v hv => hαodd v hv (fun h => ho h.1)) heven
      have hk' : Even kk := Nat.not_odd_iff_even.mp ho
      obtain ⟨r, hr⟩ := this
      obtain ⟨q, hq⟩ := hk'
      exact ⟨q + r, by rw [hr, ← hkk, hq]; push_cast; ring⟩
  have hbip : ∀ u v, (bip G R B).Adj u v → (u ∈ B ↔ v ∉ B) := by
    intro u v ⟨_, h⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun h => absurd h (hRB u h1), fun h => absurd h2 h⟩
    · exact ⟨fun _ => hRB v h2, fun _ => h1⟩
  have hNRB : Disjoint NR B := by
    rw [disjoint_left]; intro u hu; exact hRB u (mem_filter.mp hu).2.2
  obtain ⟨w2, hw2, hw2R, hw2B, -, -⟩ := between (bip G R B) B NR hbip hNRB α hα hpar'
    (fun a ha b hb => hconn a (by
        simp only [mem_union] at ha ⊢
        rcases ha with h | h
        · exact Or.inr h
        · exact Or.inl (mem_filter.mp h).2.2) b (by
        simp only [mem_union] at hb ⊢
        rcases hb with h | h
        · exact Or.inr h
        · exact Or.inl (mem_filter.mp h).2.2))
    id id id ∅ ∅ (fun v h => absurd h (notMem_empty v))
  -- the weights at v0, depending on the set U of red neighbours raised to 3
  let c3 : Finset V → V → ℤ := fun U u => if u ∈ R then (if u ∈ U then 3 else 1) else cor u
  let W : Finset V → Sym2 V → ℤ := fun U => atv v0 (c3 U) (comb B w1 w2)
  have hsdv : ∀ U, ∀ v ∈ R ∪ B, sd G (W U) v = sd (indB G B) w1 v + sd (bip G R B) w2 v +
      (if G.Adj v v0 then c3 U v else 0) :=
    fun U v hv => sd_atv G R B hdisj hind v0 hv0 hsupp (c3 U) w1 w2 v hv
  have hsdB : ∀ U, ∀ v ∈ B, sd G (W U) v = f v := by
    intro U v hv
    rw [hsdv U v (mem_union_right _ hv), hw2B v hv]
    have : (if G.Adj v v0 then c3 U v else 0) = cor v := by
      have hvR : v ∉ R := fun h => hRB v h hv
      simp only [c3, hvR, if_false]; rw [hcor v]; split_ifs <;> rfl
    rw [this]; simp only [α]; ring
  have hsdR : ∀ U, ∀ v ∈ R, sd G (W U) v = sd (bip G R B) w2 v +
      (if G.Adj v v0 then c3 U v else 0) := by
    intro U v hv
    rw [hsdv U v (mem_union_left _ hv)]
    have : sd (indB G B) w1 v = 0 := by
      apply sum_eq_zero; intro u hu; simp only [mem_filter, indB_adj] at hu
      exact absurd hu.2.2.1 (hRB v hv)
    rw [this, zero_add]
  have hevR : ∀ U, ∀ v ∈ R, Even (sd G (W U) v) := by
    intro U v hv
    rw [hsdR U v hv]
    have hpv := hw2R v (hRB v hv)
    by_cases hadj : G.Adj v v0
    · have hin : v ∈ NR := by simp [NR, hadj.symm, hv]
      have ho : Odd (sd (bip G R B) w2 v) := hpv.mpr hin
      simp only [hadj, if_true, c3, hv]
      obtain ⟨r, hr⟩ := ho
      split_ifs
      · exact ⟨r + 2, by omega⟩
      · exact ⟨r + 1, by omega⟩
    · have hin : v ∉ NR := by simp [NR, hv]; exact fun h => hadj h.symm
      have : ¬ Odd (sd (bip G R B) w2 v) := fun h => hin (hpv.mp h)
      simp only [hadj, if_false, add_zero]
      exact Int.not_odd_iff_even.mp this
  -- the weighted degree of v0
  have hN0 : univ.filter (G.Adj v0) = NR ∪ NB := by
    ext u; simp only [mem_filter, mem_univ, true_and, mem_union, NR, NB]
    constructor
    · intro h
      have := hsupp u v0 h.symm (fun hu => G.ne_of_adj h hu.symm)
      simp only [mem_union] at this; tauto
    · rintro (h | h) <;> exact h.1
  have hNRB' : Disjoint NR NB := by
    rw [disjoint_left]; intro u h1 h2
    exact hRB u (mem_filter.mp h1).2.2 (mem_filter.mp h2).2.2
  let C : ℤ := ∑ u ∈ NB, cor u
  have hsd0 : ∀ U, U ⊆ NR → sd G (W U) v0 = kk + 2 * U.card + C := by
    intro U hU
    simp only [W]; rw [sd_atv_v0, hN0, sum_union hNRB']
    have h1 : ∑ u ∈ NR, c3 U u = kk + 2 * U.card := by
      have : ∀ u ∈ NR, c3 U u = 1 + 2 * (if u ∈ U then 1 else 0) := by
        intro u hu
        simp only [c3, (mem_filter.mp hu).2.2, if_true]; split_ifs <;> ring
      rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, sum_boole]
      simp only [sum_const, nsmul_eq_mul, mul_one, kk]
      rw [filter_mem_eq_inter, inter_eq_right.mpr hU]
    have h2 : ∑ u ∈ NB, c3 U u = C := by
      apply sum_congr rfl; intro u hu
      have huR : u ∉ R := fun h => hRB u h (mem_filter.mp hu).2.2
      simp only [c3, huR, if_false]
    rw [h1, h2]
  have hCpar : Even (kk + C) := by
    have h := even_sum_sub_card_odd NB cor
    have hf : NB.filter (fun u => Odd (cor u)) = if Odd kk then {u0} else ∅ := by
      ext u
      simp only [mem_filter]
      split_ifs with ho
      · simp only [mem_singleton]
        constructor
        · rintro ⟨hu, hodd⟩
          by_contra hne
          have hadj : G.Adj u v0 := (mem_filter.mp hu).2.1.symm
          simp only [cor, hadj, if_true, ho, true_and, hne, if_false] at hodd
          exact (Int.not_odd_iff_even.mpr even_two) hodd
        · intro hu'
          rw [hu']
          refine ⟨hu0 ho, ?_⟩
          have hadj : G.Adj u0 v0 := (mem_filter.mp (hu0 ho)).2.1.symm
          have := hfd' u0 (mem_filter.mp (hu0 ho)).2.2
          simp only [hadj, if_true] at this
          simp only [cor, hadj, if_true, ho, and_self]
          rw [abs_eq zero_le_one] at this
          rcases this with h | h
          · exact ⟨1, by omega⟩
          · exact ⟨0, by omega⟩
      · simp only [notMem_empty, iff_false, not_and]
        intro hu hodd
        have hadj : G.Adj u v0 := (mem_filter.mp hu).2.1.symm
        simp only [cor, hadj, if_true, ho, false_and, if_false] at hodd
        exact (Int.not_odd_iff_even.mpr even_two) hodd
    rw [hf] at h
    obtain ⟨r, hr⟩ := h
    by_cases ho : Odd kk
    · simp only [ho, if_true, card_singleton] at hr
      obtain ⟨q, hq⟩ := ho
      exact ⟨q + r + 1, by simp only [C]; push_cast [hq]; omega⟩
    · simp only [ho, if_false, card_empty] at hr
      obtain ⟨q, hq⟩ := Nat.not_odd_iff_even.mp ho
      exact ⟨q + r, by simp only [C]; push_cast [hq]; omega⟩
  -- choose U
  let T : V → ℤ := fun r => sd (bip G R B) w2 r + 1
  obtain ⟨U, hUs, hU⟩ := comb_choice NR hk (fun r => (T r - (kk + C)) / 2)
  refine ⟨W U, ?_, ?_⟩
  · -- weights
    intro a b hab
    simp only [W, atv_mk]
    by_cases ha : a = v0
    · subst ha
      have hb := hsupp b a hab.symm (fun h => G.ne_of_adj hab h.symm)
      simp only [if_true, c3]
      split_ifs with h1 h2 <;> try omega
      have hbB : b ∈ B := by simp only [mem_union] at hb; tauto
      simp only [cor, hab.symm, if_true]
      split_ifs with h3
      · have := hfd' b hbB; simp only [hab.symm, if_true] at this
        rw [abs_eq zero_le_one] at this; omega
      · omega
    by_cases hb : b = v0
    · subst hb
      have ha' := hsupp a b hab ha
      simp only [ha, if_false, if_true, c3]
      split_ifs with h1 h2 <;> try omega
      have haB : a ∈ B := by simp only [mem_union] at ha'; tauto
      simp only [cor, hab, if_true]
      split_ifs with h3
      · have := hfd' a haB; simp only [hab, if_true] at this
        rw [abs_eq zero_le_one] at this; omega
      · omega
    simp only [ha, hb, if_false]
    exact comb_wt G R B hind w1 w2 hw1 hw2 a b (hsupp a b hab ha) (hsupp b a hab.symm hb) hab
  · -- proper
    have key0 : ∀ b, G.Adj v0 b → sd G (W U) v0 ≠ sd G (W U) b := by
      intro b hb
      have hbRB := hsupp b v0 hb.symm (fun h => G.ne_of_adj hb h.symm)
      have hev0 : Even (sd G (W U) v0) := by
        rw [hsd0 U hUs]; obtain ⟨r, hr⟩ := hCpar; exact ⟨r + U.card, by omega⟩
      simp only [mem_union] at hbRB
      rcases hbRB with hbR | hbB
      · have hbN : b ∈ NR := by simp [NR, hb, hbR]
        have := hU b hbN
        rw [hsd0 U hUs, hsdR U b hbR]
        simp only [hb.symm, if_true, c3, hbR]
        intro heq
        apply this
        split_ifs at heq ⊢ with h1
        · simp only [T]; omega
        · simp only [T]; omega
      · rw [hsdB U b hbB]
        intro heq; rw [heq] at hev0
        exact (Int.not_even_iff_odd.mpr (hfo b)) hev0
    intro a b hab
    by_cases ha : a = v0
    · subst ha; exact key0 b hab
    by_cases hb : b = v0
    · subst hb; exact (key0 a hab.symm).symm
    have haRB := hsupp a b hab ha
    have hbRB := hsupp b a hab.symm hb
    simp only [mem_union] at haRB hbRB
    rcases haRB with haR | haB <;> rcases hbRB with hbR | hbB
    · exact absurd hab (hind a haR b hbR)
    · rw [hsdB U b hbB]; intro heq
      have := hevR U a haR; rw [heq] at this
      exact (Int.not_even_iff_odd.mpr (hfo b)) this
    · rw [hsdB U a haB]; intro heq
      have := hevR U b hbR; rw [← heq] at this
      exact (Int.not_even_iff_odd.mpr (hfo a)) this
    · rw [hsdB U a haB, hsdB U b hbB]; exact hfp a b ⟨hab, haB, hbB⟩

end Remaining
section WalkSwitch
variable {V : Type} [Fintype V] [DecidableEq V]
open SimpleGraph

/-- successor of `x` on a walk -/
def wnxt {H : SimpleGraph V} : {a b : V} → H.Walk a b → V → V
  | _, _, .nil, x => x
  | a, _, .cons (v := c) _ q, x => if x = a then c else wnxt q x

/-- predecessor of `x` on a walk -/
def wprv {H : SimpleGraph V} : {a b : V} → H.Walk a b → V → V
  | _, _, .nil, x => x
  | a, _, .cons (v := c) _ q, x => if x = c then a else wprv q x

/-- value of the switch on a dart -/
def dval (B : Finset V) (σ : V → ℤ) (u v : V) : ℤ := if u ∈ B then σ u else - σ v

/-- the switch along a walk -/
def swD {H : SimpleGraph V} (B : Finset V) (σ : V → ℤ) : {a b : V} → H.Walk a b → Sym2 V → ℤ
  | _, _, .nil, _ => 0
  | a, _, .cons (v := c) _ q, e => (if e = s(a, c) then dval B σ a c else 0) + swD B σ q e

/-- the change of the weighted degree at `v` -/
def chg (Δ : Sym2 V → ℤ) (v : V) : ℤ := ∑ u, Δ s(v, u)

lemma sum_sym2_ind (v x c : V) (hxc : x ≠ c) (t : ℤ) :
    ∑ u, (if s(v, u) = s(x, c) then t else 0) = (if v = x then t else 0) + (if v = c then t else 0) := by
  by_cases hvx : v = x
  · subst hvx
    have : ∀ u, (s(v, u) = s(v, c) ↔ u = c) := by
      intro u; constructor
      · intro h; rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact h
        · exact absurd h1 hxc
      · rintro rfl; rfl
    simp only [this, sum_ite_eq', mem_univ, if_true, hxc, if_false, add_zero]
  · by_cases hvc : v = c
    · subst hvc
      have : ∀ u, (s(v, u) = s(x, v) ↔ u = x) := by
        intro u; constructor
        · intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h⟩
          · exact absurd h1 hvx
          · exact h
        · rintro rfl; exact Sym2.eq_swap
      simp only [this, sum_ite_eq', mem_univ, if_true, hvx, if_false, zero_add]
    · have : ∀ u, ¬ (s(v, u) = s(x, c)) := by
        intro u h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hvx h1
        · exact hvc h1
      simp [this, hvx, hvc]

variable {H : SimpleGraph V}

lemma walk_snd_ne_start {c y : V} (q : H.Walk c y) (hq : q.IsPath) (d : H.Dart)
    (hd : d ∈ q.darts) : d.snd ≠ c := by
  induction q with
  | nil => simp at hd
  | cons h q ih =>
    rename_i a c' b
    rw [Walk.cons_isPath_iff] at hq
    simp only [Walk.darts_cons, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact (H.ne_of_adj h).symm
    · intro he
      exact hq.2 (he ▸ q.dart_snd_mem_support_of_mem_darts hd)

lemma walk_fst_ne_end {c y : V} (q : H.Walk c y) (hq : q.IsPath) (d : H.Dart)
    (hd : d ∈ q.darts) : d.fst ≠ y := by
  induction q with
  | nil => simp at hd
  | cons h q ih =>
    rename_i a c' b
    rw [Walk.cons_isPath_iff] at hq
    simp only [Walk.darts_cons, List.mem_cons] at hd
    rcases hd with rfl | hd
    · intro he; exact hq.2 (he ▸ q.end_mem_support)
    · exact ih hq.1 hd

lemma wnxt_dart {a b : V} (q : H.Walk a b) (hq : q.IsPath) (d : H.Dart) (hd : d ∈ q.darts) :
    wnxt q d.fst = d.snd := by
  induction q with
  | nil => simp at hd
  | cons h q ih =>
    rename_i x c y
    rw [Walk.cons_isPath_iff] at hq
    simp only [Walk.darts_cons, List.mem_cons] at hd
    rcases hd with rfl | hd
    · simp [wnxt]
    · have : d.fst ≠ x := fun he => hq.2 (he ▸ q.dart_fst_mem_support_of_mem_darts hd)
      simp only [wnxt, this, if_false]; exact ih hq.1 hd

lemma wprv_dart {a b : V} (q : H.Walk a b) (hq : q.IsPath) (d : H.Dart) (hd : d ∈ q.darts) :
    wprv q d.snd = d.fst := by
  induction q with
  | nil => simp at hd
  | cons h q ih =>
    rename_i x c y
    have hq' := hq
    rw [Walk.cons_isPath_iff] at hq
    simp only [Walk.darts_cons, List.mem_cons] at hd
    rcases hd with rfl | hd
    · simp [wprv]
    · have : d.snd ≠ c := walk_snd_ne_start q hq.1 d hd
      simp only [wprv, this, if_false]; exact ih hq.1 hd

lemma walk_in_dart {a b : V} (q : H.Walk a b) (v : V) (hv : v ∈ q.support) (hva : v ≠ a) :
    ∃ d ∈ q.darts, d.snd = v := by
  induction q with
  | nil => simp at hv; exact absurd hv hva
  | cons h q ih =>
    rename_i x c y
    simp only [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact absurd rfl hva
    · by_cases hvc : v = c
      · subst hvc; exact ⟨⟨(x, v), h⟩, by simp, rfl⟩
      · obtain ⟨d, hd, hd'⟩ := ih hv hvc
        exact ⟨d, by simp [hd], hd'⟩

lemma walk_out_dart {a b : V} (q : H.Walk a b) (v : V) (hv : v ∈ q.support) (hvb : v ≠ b) :
    ∃ d ∈ q.darts, d.fst = v := by
  induction q with
  | nil => simp at hv; exact absurd hv hvb
  | cons h q ih =>
    rename_i x c y
    simp only [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨⟨(v, c), h⟩, by simp, rfl⟩
    · obtain ⟨d, hd, hd'⟩ := ih hv hvb
      exact ⟨d, by simp [hd], hd'⟩

lemma walk_dart_edge_inj {a b : V} (q : H.Walk a b) (hq : q.IsPath) (d1 d2 : H.Dart)
    (h1 : d1 ∈ q.darts) (h2 : d2 ∈ q.darts) (he : d1.edge = d2.edge) : d1 = d2 := by
  induction q with
  | nil => simp at h1
  | cons h q ih =>
    rename_i x c y
    rw [Walk.cons_isPath_iff] at hq
    simp only [Walk.darts_cons, List.mem_cons] at h1 h2
    have key : ∀ d ∈ q.darts, d.edge ≠ s(x, c) := by
      intro d hd hde
      have : x ∈ d.edge := hde ▸ Sym2.mem_mk_left x c
      rw [Dart.edge, Sym2.mem_iff] at this
      rcases this with h' | h'
      · exact hq.2 (h' ▸ q.dart_fst_mem_support_of_mem_darts hd)
      · exact hq.2 (h' ▸ q.dart_snd_mem_support_of_mem_darts hd)
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · rfl
    · exact absurd he.symm (key d2 h2)
    · exact absurd he (key d1 h1)
    · exact ih hq.1 h1 h2

lemma swD_zero {a b : V} (B : Finset V) (σ : V → ℤ) (q : H.Walk a b) (e : Sym2 V)
    (he : e ∉ q.edges) : swD B σ q e = 0 := by
  induction q with
  | nil => rfl
  | cons h q ih =>
    rename_i x c y
    simp only [Walk.edges_cons, List.mem_cons, not_or] at he
    simp only [swD, he.1, if_false, ih he.2, add_zero]

lemma swD_dart {a b : V} (B : Finset V) (σ : V → ℤ) (q : H.Walk a b) (hq : q.IsPath)
    (d : H.Dart) (hd : d ∈ q.darts) : swD B σ q d.edge = dval B σ d.fst d.snd := by
  induction q with
  | nil => simp at hd
  | cons h q ih =>
    rename_i x c y
    rw [Walk.cons_isPath_iff] at hq
    simp only [Walk.darts_cons, List.mem_cons] at hd
    have hnot : s(x, c) ∉ q.edges := fun hm => hq.2 (q.fst_mem_support_of_mem_edges hm)
    rcases hd with rfl | hd
    · simp only [swD, Dart.edge_mk, if_true, swD_zero B σ q _ hnot, add_zero]
    · have hne : d.edge ≠ s(x, c) := by
        intro hde
        have : x ∈ d.edge := hde ▸ Sym2.mem_mk_left x c
        rw [Dart.edge, Sym2.mem_iff] at this
        rcases this with h' | h'
        · exact hq.2 (h' ▸ q.dart_fst_mem_support_of_mem_darts hd)
        · exact hq.2 (h' ▸ q.dart_snd_mem_support_of_mem_darts hd)
      simp only [swD, hne, if_false, zero_add]; exact ih hq.1 hd

/-- the effect of the switch along a path -/
theorem switch_walk (B : Finset V) (σ : V → ℤ) (hσ : ∀ v, σ v = 1 ∨ σ v = -1)
    (hbip : ∀ u v, H.Adj u v → (u ∈ B ↔ v ∉ B)) {x y : V} (q : H.Walk x y) (hq : q.IsPath) :
    (∀ v, v ∉ q.support → chg (swD B σ q) v = 0) ∧
    (¬ q.Nil → chg (swD B σ q) x = dval B σ x (q.getVert 1)) ∧
    (¬ q.Nil → chg (swD B σ q) y = dval B σ q.penultimate y) ∧
    (∀ v ∈ q.support, v ≠ x → v ≠ y →
      (v ∈ B → chg (swD B σ q) v = 0) ∧ (v ∉ B → Even (chg (swD B σ q) v))) := by
  induction q with
  | nil =>
    refine ⟨fun v _ => by simp [chg, swD], fun h => absurd Walk.Nil.nil h,
      fun h => absurd Walk.Nil.nil h, fun v hv h1 _ => ?_⟩
    simp at hv; exact absurd hv h1
  | cons h q ih =>
    rename_i a c b
    have hq' := hq
    rw [Walk.cons_isPath_iff] at hq
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih hq.1
    have hac : a ≠ c := H.ne_of_adj h
    have hchg : ∀ v, chg (swD B σ (Walk.cons h q)) v = chg (swD B σ q) v +
        ((if v = a then dval B σ a c else 0) + (if v = c then dval B σ a c else 0)) := by
      intro v
      simp only [chg, swD, sum_add_distrib]
      rw [add_comm, sum_sym2_ind v a c hac]
    have haq : a ∉ q.support := hq.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv
      simp only [Walk.support_cons, List.mem_cons, not_or] at hv
      have hvc : v ≠ c := fun he => hv.2 (he ▸ q.start_mem_support)
      rw [hchg, ih1 v hv.2]; simp [hv.1, hvc]
    · intro _
      rw [hchg, ih1 a haq]; simp [hac]
    · intro _
      by_cases hn : q.Nil
      · have hcb : c = b := hn.eq
        subst hcb
        rw [hchg]
        have : chg (swD B σ q) c = 0 := by
          rw [Walk.nil_iff_eq_nil.mp hn]; simp [chg, swD]
        rw [this]
        have hpen : (Walk.cons h q).penultimate = a := by
          rw [Walk.nil_iff_eq_nil.mp hn]; rfl
        rw [hpen]; simp [Ne.symm hac]
      · have hba : b ≠ a := fun he => haq (he ▸ q.end_mem_support)
        have hbc : b ≠ c := fun he => hn (by subst he; exact Walk.nil_iff_eq_nil.mpr (Walk.isPath_iff_eq_nil.mp hq.1))
        rw [hchg, ih3 hn]
        rw [Walk.penultimate_cons_of_not_nil _ _ hn]
        simp [hba, hbc]
    · intro v hv hva hvb
      simp only [Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact absurd rfl hva
      by_cases hvc : v = c
      · subst hvc
        have hn : ¬ q.Nil := fun hn => hvb hn.eq
        rw [hchg, ih2 hn]
        simp only [hva, if_false, if_true, zero_add]
        have h2 : H.Adj v (q.getVert 1) := Walk.adj_snd hn
        have hb1 := hbip a v h
        have hb2 := hbip v _ h2
        constructor
        · intro hvB
          have haB : a ∉ B := fun haB => (hb1.mp haB) hvB
          simp [dval, hvB, haB]
        · intro hvB
          have haB : a ∈ B := by by_contra hh; exact hvB (by tauto)
          have hdB : q.getVert 1 ∈ B := by by_contra hh; exact hvB (hb2.mpr hh)
          simp only [dval, haB, hvB, hdB, if_true, if_false]
          rcases hσ a with h1 | h1 <;> rcases hσ (q.getVert 1) with h3 | h3 <;> rw [h1, h3] <;>
            decide
      · rw [hchg]; simp only [hva, hvc, if_false, add_zero]
        exact ih4 v hv hvc hvb

end WalkSwitch
section Rearr
variable {V : Type} [Fintype V] [DecidableEq V]
open SimpleGraph

/-- delete a set of vertices (keeping the vertex type) -/
def delv (H : SimpleGraph V) (X : Finset V) : SimpleGraph V where
  Adj x y := H.Adj x y ∧ x ∉ X ∧ y ∉ X
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => H.ne_of_adj h.1 rfl⟩

@[simp] lemma delv_adj (H : SimpleGraph V) (X : Finset V) (x y : V) :
    (delv H X).Adj x y ↔ H.Adj x y ∧ x ∉ X ∧ y ∉ X := Iff.rfl

instance delv_dec (H : SimpleGraph V) [DecidableRel H.Adj] (X : Finset V) :
    DecidableRel (delv H X).Adj :=
  fun a b => inferInstanceAs (Decidable (H.Adj a b ∧ a ∉ X ∧ b ∉ X))

lemma vc_of_parity (G : SimpleGraph V) [DecidableRel G.Adj] (R B : Finset V)
    (hdisj : Disjoint R B) (hind : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b) (v0 : V)
    (hsupp : ∀ a b, G.Adj a b → a ≠ v0 → a ∈ R ∪ B) (W : Sym2 V → ℤ)
    (hw : ∀ u v, G.Adj u v → 1 ≤ W s(u, v) ∧ W s(u, v) ≤ 3)
    (hB : ∀ v ∈ B, Odd (sd G W v)) (hR : ∀ v ∈ R, Even (sd G W v)) (h0 : Even (sd G W v0))
    (hBB : ∀ u ∈ B, ∀ v ∈ B, G.Adj u v → sd G W u ≠ sd G W v)
    (h0R : ∀ r ∈ R, G.Adj v0 r → sd G W v0 ≠ sd G W r) : VC G W := by
  refine ⟨hw, ?_⟩
  have key0 : ∀ b, G.Adj v0 b → sd G W v0 ≠ sd G W b := by
    intro b hb
    have hbRB := hsupp b v0 hb.symm (fun h => G.ne_of_adj hb h.symm)
    simp only [mem_union] at hbRB
    rcases hbRB with hbR | hbB
    · exact h0R b hbR hb
    · intro heq; rw [heq] at h0
      exact (Int.not_even_iff_odd.mpr (hB b hbB)) h0
  intro a b hab
  by_cases ha : a = v0
  · subst ha; exact key0 b hab
  by_cases hb : b = v0
  · subst hb; exact (key0 a hab.symm).symm
  have haRB := hsupp a b hab ha
  have hbRB := hsupp b a hab.symm hb
  simp only [mem_union] at haRB hbRB
  rcases haRB with haR | haB <;> rcases hbRB with hbR | hbB
  · exact absurd hab (hind a haR b hbR)
  · intro heq
    have := hR a haR; rw [heq] at this
    exact (Int.not_even_iff_odd.mpr (hB b hbB)) this
  · intro heq
    have := hR b hbR; rw [← heq] at this
    exact (Int.not_even_iff_odd.mpr (hB a haB)) this
  · exact hBB a haB b hbB hab

lemma sd_add (G : SimpleGraph V) [DecidableRel G.Adj] (W D : Sym2 V → ℤ) (v : V)
    (hD : ∀ x y, D s(x, y) ≠ 0 → G.Adj x y) :
    sd G (fun e => W e + D e) v = sd G W v + chg D v := by
  simp only [sd, sum_add_distrib, chg]
  congr 1
  rw [sum_filter]; apply sum_congr rfl; intro u _
  split_ifs with h
  · rfl
  · by_contra hne; exact h (hD v u (Ne.symm hne))

lemma dR_facts (G : SimpleGraph V) [DecidableRel G.Adj] (R B : Finset V) (hdisj : Disjoint R B)
    (v0 : V) (hv0 : v0 ∉ R ∪ B) (hsupp : ∀ a b, G.Adj a b → a ≠ v0 → a ∈ R ∪ B) (v : V)
    (hv : v ∈ B) :
    ((univ.filter ((bip G R B).Adj v)).card : ℤ) =
        ((univ.filter (fun u => G.Adj v u ∧ u ∈ R)).card : ℤ) ∧
    ((univ.filter (fun u => G.Adj v u ∧ u ∉ B)).card : ℤ) =
        ((univ.filter (fun u => G.Adj v u ∧ u ∈ R)).card : ℤ) + (if G.Adj v v0 then 1 else 0) := by
  have hRB : ∀ x, x ∈ R → x ∉ B := fun x hx => Finset.disjoint_left.mp hdisj hx
  constructor
  · congr 2; ext u
    simp only [mem_filter, mem_univ, true_and, bip_adj]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rcases h2 with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd hv (hRB v h)
      · exact h
    · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr ⟨hv, h2⟩⟩
  · have hsplit : univ.filter (fun u => G.Adj v u ∧ u ∉ B) =
        univ.filter (fun u => G.Adj v u ∧ u ∈ R) ∪ univ.filter (fun u => G.Adj v u ∧ u = v0) := by
      ext u; simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hu0 : u = v0
        · exact Or.inr ⟨h1, hu0⟩
        · have := hsupp u v h1.symm hu0
          simp only [mem_union] at this; left; exact ⟨h1, by tauto⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, hRB u h2⟩
        · exact ⟨h1, fun h => hv0 (h2 ▸ mem_union_right _ h)⟩
    have hdj : Disjoint (univ.filter (fun u => G.Adj v u ∧ u ∈ R))
        (univ.filter (fun u => G.Adj v u ∧ u = v0)) := by
      rw [Finset.disjoint_left]; intro u h1 h2
      simp only [mem_filter] at h1 h2
      exact hv0 (h2.2.2 ▸ mem_union_left _ h1.2.2)
    rw [hsplit, card_union_of_disjoint hdj]
    have : univ.filter (fun u => G.Adj v u ∧ u = v0) = if G.Adj v v0 then {v0} else ∅ := by
      ext u; split_ifs with h <;> simp only [mem_filter, mem_univ, true_and, mem_singleton,
        notMem_empty, iff_false, not_and] <;> [exact ⟨fun h' => h'.2, fun h' => ⟨h' ▸ h, h'⟩⟩;
        exact fun h' h'' => h (h'' ▸ h')]
    rw [this]; split_ifs <;> simp

lemma sigma_choice (P N : ℤ) (hP : 1 ≤ P ∧ P ≤ 3) (hN : 1 ≤ N ∧ N ≤ 3) (h : 3 ≤ P + N ∧ P + N ≤ 5) :
    let σ : ℤ := if N ≤ 2 ∧ 2 ≤ P then 1 else -1
    (1 ≤ N + σ ∧ N + σ ≤ 3) ∧ (1 ≤ P - σ ∧ P - σ ≤ 3) := by
  intro σ
  simp only [σ]; split_ifs with hh <;> omega

set_option maxHeartbeats 4000000 in
/-- Keusch, Lemma 7: one extra vertex with a single red neighbour. -/
theorem rearr (G : SimpleGraph V) [DecidableRel G.Adj] (v0 u0 : V) (R B : Finset V)
    (hdisj : Disjoint R B) (hv0 : v0 ∉ R ∪ B) (hind : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b)
    (hconn : ∀ a ∈ R ∪ B, ∀ b ∈ R ∪ B, (bip G R B).Reachable a b) (heven : Even B.card)
    (hsupp : ∀ a b, G.Adj a b → a ≠ v0 → a ∈ R ∪ B)
    (hu0 : u0 ∈ R) (hN0 : ∀ r ∈ R, G.Adj v0 r ↔ r = u0)
    (a b : V) (ha : a ∈ B) (hb : b ∈ B) (hab : a ≠ b) (hva : G.Adj v0 a) (hvb : G.Adj v0 b)
    (hreach : (delv (bip G R B) {u0}).Reachable a b) : ∃ w, VC G w := by
  have hRB : ∀ x, x ∈ R → x ∉ B := fun x hx => Finset.disjoint_left.mp hdisj hx
  obtain ⟨w1, f, hw1, hfo, hfp, hfd⟩ := blue_step G B (fun _ => 0) (fun _ => ⟨0, by ring⟩)
  let dR : V → ℤ := fun v => ((univ.filter (fun u => G.Adj v u ∧ u ∈ R)).card : ℤ)
  have hdK : ∀ v ∈ B, ((univ.filter ((bip G R B).Adj v)).card : ℤ) = dR v :=
    fun v hv => (dR_facts G R B hdisj v0 hv0 hsupp v hv).1
  let β : V → ℤ := fun v => f v - sd (indB G B) w1 v - 2 * dR v
  have hβ : ∀ v ∈ B, |β v - 2 * (if G.Adj v v0 then 1 else 0)| = 1 := by
    intro v hv
    have := hfd v
    rw [(dR_facts G R B hdisj v0 hv0 hsupp v hv).2] at this
    simp only [β]; convert this using 2; ring
  have hβ13 : ∀ v ∈ B, G.Adj v v0 → β v = 1 ∨ β v = 3 := by
    intro v hv hadj
    have := hβ v hv; simp only [hadj, if_true] at this
    rw [abs_eq zero_le_one] at this; omega
  have main : ∀ a b : V, a ∈ B → b ∈ B → a ≠ b → G.Adj v0 a → G.Adj v0 b →
      (delv (bip G R B) {u0}).Reachable a b → ¬ (β a = 1 ∧ β b = 3) → ∃ w, VC G w := by
    intro a b ha hb hab hva hvb hreach hwlog
    set K' := delv (bip G R B) {u0} with hK'
    obtain ⟨p⟩ := hreach
    obtain ⟨q, hq⟩ := p.toPath
    have hK'adj : ∀ x y, K'.Adj x y → (bip G R B).Adj x y ∧ x ≠ u0 ∧ y ≠ u0 := by
      intro x y h; simp only [hK', delv_adj, mem_singleton] at h; exact ⟨h.1, h.2.1, h.2.2⟩
    have hβa := hβ13 a ha hva.symm
    have hβb := hβ13 b hb hvb.symm
    let caseB : Prop := β a ≠ β b
    have hcB : caseB → β a = 3 ∧ β b = 1 := by
      intro h; simp only [caseB] at h; omega
    let c0 : V → ℤ := fun v => if caseB ∧ v = a then 3 else 2
    let cor : V → ℤ := fun v => if G.Adj v v0 then c0 v else 0
    let α : V → ℤ := fun v => f v - sd (indB G B) w1 v - cor v
    let Rp : Finset V := if caseB then {u0} else ∅
    have hαv : ∀ v, α v = f v - sd (indB G B) w1 v - cor v := fun v => rfl
    have hαβ : ∀ v, α v - 2 * dR v = β v - cor v := by intro v; simp only [hαv, β]; ring
    have hα : ∀ v ∈ B, |α v - 2 * ((univ.filter ((bip G R B).Adj v)).card : ℤ)| ≤ 1 := by
      intro v hv
      rw [hdK v hv, hαβ]
      have := hβ v hv
      rw [abs_eq zero_le_one] at this; rw [abs_le]
      simp only [cor, c0]
      by_cases h1 : G.Adj v v0
      · simp only [h1, if_true] at this ⊢
        by_cases h2 : caseB ∧ v = a
        · rw [if_pos h2]; have := hcB h2.1; rw [h2.2]; omega
        · rw [if_neg h2]; omega
      · simp only [h1, if_false] at this ⊢; omega
    have hαodd : ∀ v ∈ B, ¬ (caseB ∧ v = a) → Odd (α v) := by
      intro v hv hns
      have e := hαβ v
      have := hβ v hv
      rw [abs_eq zero_le_one] at this
      simp only [cor, c0] at e
      by_cases h1 : G.Adj v v0
      · simp only [h1, if_true, if_neg hns] at this e
        rcases this with h | h
        · exact ⟨dR v, by omega⟩
        · exact ⟨dR v - 1, by omega⟩
      · simp only [h1, if_false] at this e
        rcases this with h | h
        · exact ⟨dR v, by omega⟩
        · exact ⟨dR v - 1, by omega⟩
    have hpar : Even ((Rp.card : ℤ) + ∑ v ∈ B, α v) := by
      by_cases hc : caseB
      · rw [← add_sum_erase B α ha]
        have h1 : α a = 2 * dR a := by
          have := hαβ a; simp only [cor, c0, hva.symm, if_true, hc, and_self] at this
          have := (hcB hc).1; omega
        have h2 := even_sum_sub_card_odd (B.erase a) α
        rw [filter_true_of_mem (fun v hv => hαodd v (mem_of_mem_erase hv)
          (fun h => (ne_of_mem_erase hv) h.2)), card_erase_of_mem ha] at h2
        obtain ⟨r, hr⟩ := h2
        obtain ⟨pp, hp⟩ := heven
        have hB1 : 1 ≤ B.card := card_pos.mpr ⟨a, ha⟩
        have hRp : Rp.card = 1 := by simp [Rp, hc]
        refine ⟨dR a + r + pp, ?_⟩
        rw [h1, hRp]; push_cast [Nat.cast_sub hB1] at hr; push_cast; omega
      · have := even_sum_of_odd B α (fun v hv => hαodd v hv (fun h => hc h.1)) heven
        have hRp : Rp.card = 0 := by simp [Rp, hc]
        rw [hRp]; simpa using this
    have hbip : ∀ u v, (bip G R B).Adj u v → (u ∈ B ↔ v ∉ B) := by
      intro u v ⟨_, h⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨fun h => absurd h (hRB u h1), fun h => absurd h2 h⟩
      · exact ⟨fun _ => hRB v h2, fun _ => h1⟩
    have hRpB : Disjoint Rp B := by
      simp only [Rp]; split_ifs
      · exact disjoint_singleton_left.mpr (hRB u0 hu0)
      · exact disjoint_empty_left _
    have hRpR : Rp ⊆ R := by
      simp only [Rp]; split_ifs
      · exact singleton_subset_iff.mpr hu0
      · exact empty_subset _
    let en : V → V := fun x => if x = a then wnxt q x else wprv q x
    let pairOn : Finset V := (B.filter (fun x => x ∈ q.support)) \ {a, b}
    obtain ⟨w2, hw2, hw2R, hw2B, hpair, hend⟩ := between (bip G R B) B Rp hbip hRpB α hα hpar
      (fun x hx y hy => hconn x (by
          simp only [mem_union] at hx ⊢; rcases hx with h | h
          · exact Or.inr h
          · exact Or.inl (hRpR h)) y (by
          simp only [mem_union] at hy ⊢; rcases hy with h | h
          · exact Or.inr h
          · exact Or.inl (hRpR h)))
      (wprv q) (wnxt q) en pairOn {a, b}
      (fun v hv hv' => by simp only [pairOn, mem_sdiff] at hv; exact hv.2 hv')
    -- the combined weighting
    let c3 : V → ℤ := fun u => if u ∈ R then (if caseB then 3 else 2) else c0 u
    let W : Sym2 V → ℤ := atv v0 c3 (comb B w1 w2)
    have hsdv : ∀ v ∈ R ∪ B, sd G W v = sd (indB G B) w1 v + sd (bip G R B) w2 v +
        (if G.Adj v v0 then c3 v else 0) :=
      fun v hv => sd_atv G R B hdisj hind v0 hv0 hsupp c3 w1 w2 v hv
    have hsdB : ∀ v ∈ B, sd G W v = f v := by
      intro v hv
      rw [hsdv v (mem_union_right _ hv), hw2B v hv]
      have hvR : v ∉ R := fun h => hRB v h hv
      have : (if G.Adj v v0 then c3 v else 0) = cor v := by
        simp only [c3, hvR, if_false, cor]
      rw [this, hαv]; ring
    have hevR : ∀ v ∈ R, Even (sd G W v) := by
      intro v hv
      rw [hsdv v (mem_union_left _ hv)]
      have h0 : sd (indB G B) w1 v = 0 := by
        apply sum_eq_zero; intro u hu; simp only [mem_filter, indB_adj] at hu
        exact absurd hu.2.2.1 (hRB v hv)
      rw [h0, zero_add]
      have hpv := hw2R v (hRB v hv)
      by_cases hvu : v = u0
      · subst hvu
        have hadj : G.Adj v v0 := ((hN0 v hv).mpr rfl).symm
        simp only [hadj, if_true, c3, hv]
        by_cases hc : caseB
        · have ho : Odd (sd (bip G R B) w2 v) := hpv.mpr (by simp [Rp, hc])
          simp only [hc, if_true]; obtain ⟨r, hr⟩ := ho; exact ⟨r + 2, by omega⟩
        · have : ¬ Odd (sd (bip G R B) w2 v) := fun h => by
            have := hpv.mp h; simp [Rp, hc] at this
          simp only [hc, if_false]
          obtain ⟨r, hr⟩ := Int.not_odd_iff_even.mp this; exact ⟨r + 1, by omega⟩
      · have hadj : ¬ G.Adj v v0 := fun h => hvu ((hN0 v hv).mp h.symm)
        have : ¬ Odd (sd (bip G R B) w2 v) := fun h => by
          have := hpv.mp h; simp only [Rp] at this; split_ifs at this <;> simp_all
        simp only [hadj, if_false, add_zero]
        exact Int.not_odd_iff_even.mp this
    have hN0' : univ.filter (G.Adj v0) = insert u0 (univ.filter (fun u => G.Adj v0 u ∧ u ∈ B)) := by
      ext u; simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro h
        have := hsupp u v0 h.symm (fun hu => G.ne_of_adj h hu.symm)
        simp only [mem_union] at this
        rcases this with h' | h'
        · exact Or.inl ((hN0 u h').mp h)
        · exact Or.inr ⟨h, h'⟩
      · rintro (rfl | h)
        · exact (hN0 u hu0).mpr rfl
        · exact h.1
    have hev0 : Even (sd G W v0) := by
      simp only [W]; rw [sd_atv_v0, hN0']
      have hu0n : u0 ∉ univ.filter (fun u => G.Adj v0 u ∧ u ∈ B) := by
        simp only [mem_filter, not_and]; intro _ _ h; exact hRB u0 hu0 h
      rw [sum_insert hu0n]
      have e : ∀ u ∈ univ.filter (fun u => G.Adj v0 u ∧ u ∈ B), c3 u =
          2 + (if caseB ∧ u = a then 1 else 0) := by
        intro u hu
        have huR : u ∉ R := fun h => hRB u h (mem_filter.mp hu).2.2
        simp only [c3, huR, if_false, c0]; split_ifs <;> ring
      rw [sum_congr rfl e, sum_add_distrib, sum_const, nsmul_eq_mul]
      have e2 : ∑ u ∈ univ.filter (fun u => G.Adj v0 u ∧ u ∈ B),
          (if caseB ∧ u = a then (1 : ℤ) else 0) = if caseB then 1 else 0 := by
        by_cases hc : caseB
        · simp only [hc, true_and]; rw [sum_ite_eq']; simp [hva, ha]
        · simp [hc]
      rw [e2]
      simp only [c3, hu0, if_true]
      by_cases hc : caseB
      · simp only [hc, if_true]; exact ⟨_ + 2, by ring⟩
      · simp only [hc, if_false]; exact ⟨_ + 1, by ring⟩
    have hwW : ∀ x y, G.Adj x y → 1 ≤ W s(x, y) ∧ W s(x, y) ≤ 3 := by
      intro x y hxy
      simp only [W, atv_mk]
      have c3ok : ∀ u, 1 ≤ c3 u ∧ c3 u ≤ 3 := by
        intro u; simp only [c3, c0]; split_ifs <;> omega
      by_cases hx : x = v0
      · simp only [hx, if_true]; exact c3ok y
      by_cases hy : y = v0
      · simp only [hx, hy, if_false, if_true]; exact c3ok x
      simp only [hx, hy, if_false]
      exact comb_wt G R B hind w1 w2 hw1 hw2 x y (hsupp x y hxy hx) (hsupp y x hxy.symm hy) hxy
    have hBB : ∀ u ∈ B, ∀ v ∈ B, G.Adj u v → sd G W u ≠ sd G W v := by
      intro u hu v hv huv; rw [hsdB u hu, hsdB v hv]; exact hfp u v ⟨huv, hu, hv⟩
    by_cases hconf : sd G W v0 = sd G W u0
    swap
    · refine ⟨W, vc_of_parity G R B hdisj hind v0 hsupp W hwW (fun v hv => by
        rw [hsdB v hv]; exact hfo v) hevR hev0 hBB ?_⟩
      intro r hr hadj
      rw [(hN0 r hr).mp hadj]; exact hconf
    -- the switch along the cycle v0, a, ..., b, v0
    have hWv0 : ∀ u, W s(v0, u) = c3 u := fun u => by simp only [W, atv_mk, if_true]
    have hWbip : ∀ x y, (bip G R B).Adj x y → W s(x, y) = w2 s(x, y) := by
      intro x y h
      have hx : x ≠ v0 := fun he => by
        rcases h.2 with h' | h'
        · exact hv0 (he ▸ mem_union_left _ h'.1)
        · exact hv0 (he ▸ mem_union_right _ h'.1)
      have hy : y ≠ v0 := fun he => by
        rcases h.2 with h' | h'
        · exact hv0 (he ▸ mem_union_right _ h'.2)
        · exact hv0 (he ▸ mem_union_left _ h'.2)
      have hnb : ¬ (x ∈ B ∧ y ∈ B) := fun hh => (hbip x y h).mp hh.1 hh.2
      simp only [W, atv_mk, hx, hy, if_false, comb_mk, hnb]
    clear_value W
    obtain ⟨s, hsdef⟩ : ∃ s : ℤ, s = if caseB then 1 else (if β a = 1 then 1 else -1) := ⟨_, rfl⟩
    have hs : s = 1 ∨ s = -1 := by rw [hsdef]; split_ifs <;> simp
    obtain ⟨σ, hσdef⟩ : ∃ σ : V → ℤ, ∀ v, σ v = if v = a then s else if v = b then -s else
      (if W s(v, wnxt q v) ≤ 2 ∧ 2 ≤ W s(v, wprv q v) then 1 else -1) := ⟨_, fun v => rfl⟩
    have hσ : ∀ v, σ v = 1 ∨ σ v = -1 := by
      intro v; rw [hσdef]; split_ifs <;> omega
    have hK'bip : ∀ x y, K'.Adj x y → (x ∈ B ↔ y ∉ B) := fun x y h => hbip x y (hK'adj x y h).1
    obtain ⟨sw1, sw2, sw3, sw4⟩ := switch_walk B σ hσ hK'bip q hq
    set Δ : Sym2 V → ℤ := swD B σ q with hΔdef
    obtain ⟨E0, hE0def⟩ : ∃ E0 : Sym2 V → ℤ, ∀ e, E0 e =
        if e = s(v0, a) then -s else if e = s(v0, b) then -s else 0 := ⟨_, fun e => rfl⟩
    obtain ⟨W', hW'def⟩ : ∃ W' : Sym2 V → ℤ, ∀ e, W' e = W e + (Δ e + E0 e) := ⟨_, fun e => rfl⟩
    have hqn : ¬ q.Nil := fun h => hab h.eq
    have hsupp_q : ∀ v ∈ q.support, v ∈ R ∪ B ∧ v ≠ u0 := by
      intro v hv
      by_cases hva' : v = a
      · subst hva'; exact ⟨mem_union_right _ ha, fun h => hRB v (h ▸ hu0) ha⟩
      obtain ⟨d, hd, rfl⟩ := walk_in_dart q v hv hva'
      have := hK'adj _ _ d.adj
      refine ⟨?_, this.2.2⟩
      rcases this.1.2 with h | h
      · exact mem_union_right _ h.2
      · exact mem_union_left _ h.2
    have hv0q : v0 ∉ q.support := fun h => hv0 (hsupp_q v0 h).1
    have hu0q : u0 ∉ q.support := fun h => (hsupp_q u0 h).2 rfl
    have hΔadj : ∀ x y, Δ s(x, y) ≠ 0 → G.Adj x y := by
      intro x y h
      by_contra hn
      apply h
      apply swD_zero
      intro hm
      exact hn (hK'adj x y (q.adj_of_mem_edges hm)).1.1
    have hE0 : ∀ v, chg E0 v = -s * ((if v = v0 then 1 else 0) + (if v = a then 1 else 0)) +
        -s * ((if v = v0 then 1 else 0) + (if v = b then 1 else 0)) := by
      intro v
      have hne : s(v0, a) ≠ s(v0, b) := by
        intro h; rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact hab h
        · exact G.ne_of_adj hva h2.symm
      have pt : ∀ u, E0 s(v, u) = (if s(v, u) = s(v0, a) then -s else 0) +
          (if s(v, u) = s(v0, b) then -s else 0) := by
        intro u; rw [hE0def]
        by_cases h1 : s(v, u) = s(v0, a)
        · have h2 : s(v, u) ≠ s(v0, b) := fun h => hne (h1.symm.trans h)
          rw [if_pos h1, if_pos h1, if_neg h2, add_zero]
        · rw [if_neg h1, if_neg h1, zero_add]
      simp only [chg, pt, sum_add_distrib]
      rw [sum_sym2_ind v v0 a (G.ne_of_adj hva), sum_sym2_ind v v0 b (G.ne_of_adj hvb)]
      split_ifs <;> ring
    have hDadj : ∀ x y, Δ s(x, y) + E0 s(x, y) ≠ 0 → G.Adj x y := by
      intro x y h
      by_cases h1 : Δ s(x, y) = 0
      · rw [h1, zero_add, hE0def] at h
        split_ifs at h with h2 h3
        · rcases Sym2.eq_iff.mp h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hva
          · exact hva.symm
        · rcases Sym2.eq_iff.mp h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hvb
          · exact hvb.symm
        · exact absurd rfl h
      · exact hΔadj x y h1
    have hsd' : ∀ v, sd G W' v = sd G W v + chg Δ v + chg E0 v := by
      intro v
      have := sd_add G W (fun e => Δ e + E0 e) v hDadj
      have hW'f : W' = fun e => W e + (Δ e + E0 e) := funext hW'def
      rw [hW'f, this]; simp only [chg, sum_add_distrib]; ring
    have hchg_a : chg Δ a = s := by
      rw [sw2 hqn]
      have h1 := hK'bip a (q.getVert 1) (Walk.adj_snd hqn)
      simp only [dval, ha, if_true]; rw [hσdef]; simp
    have hchg_b : chg Δ b = s := by
      rw [sw3 hqn]
      have h1 := hK'bip _ b (Walk.adj_penultimate hqn)
      have hpB : q.penultimate ∉ B := fun h => (h1.mp h) hb
      simp only [dval, hpB, if_false]; rw [hσdef]; simp [Ne.symm hab]
    have hblue : ∀ v ∈ B, sd G W' v = sd G W v := by
      intro v hv
      rw [hsd', hE0]
      have hvv0 : v ≠ v0 := fun h => hv0 (h ▸ mem_union_right _ hv)
      by_cases hva' : v = a
      · subst hva'; rw [hchg_a]; simp [hvv0, hab]
      by_cases hvb' : v = b
      · subst hvb'; rw [hchg_b]; simp [hvv0, hva']
      by_cases hvq : v ∈ q.support
      · rw [(sw4 v hvq hva' hvb').1 hv]; simp [hvv0, hva', hvb']
      · rw [sw1 v hvq]; simp [hvv0, hva', hvb']
    have hred : ∀ v ∈ R, Even (sd G W' v) := by
      intro v hv
      rw [hsd', hE0]
      have hvv0 : v ≠ v0 := fun h => hv0 (h ▸ mem_union_left _ hv)
      have hva' : v ≠ a := fun h => hRB v hv (h ▸ ha)
      have hvb' : v ≠ b := fun h => hRB v hv (h ▸ hb)
      simp only [hvv0, hva', hvb', if_false, add_zero, mul_zero]
      by_cases hvq : v ∈ q.support
      · have := (sw4 v hvq hva' hvb').2 (hRB v hv)
        obtain ⟨r1, hr1⟩ := hevR v hv
        obtain ⟨r2, hr2⟩ := this
        exact ⟨r1 + r2, by rw [hr1, hr2]; ring⟩
      · rw [sw1 v hvq]; simpa using hevR v hv
    have hsd0' : sd G W' v0 = sd G W v0 - 2 * s := by
      rw [hsd', hE0, sw1 v0 hv0q]
      have h1 : v0 ≠ a := G.ne_of_adj hva
      have h2 : v0 ≠ b := G.ne_of_adj hvb
      simp [h1, h2]; ring
    have hsdu0' : sd G W' u0 = sd G W u0 := by
      rw [hsd', hE0, sw1 u0 hu0q]
      have h1 : u0 ≠ v0 := fun h => hv0 (h ▸ mem_union_left _ hu0)
      have h2 : u0 ≠ a := fun h => hRB u0 hu0 (h ▸ ha)
      have h3 : u0 ≠ b := fun h => hRB u0 hu0 (h ▸ hb)
      simp [h1, h2, h3]
    -- weights stay in [1,3]
    have hdart : ∀ d ∈ q.darts, 1 ≤ W d.edge + dval B σ d.fst d.snd ∧
        W d.edge + dval B σ d.fst d.snd ≤ 3 := by
      intro d hd
      obtain ⟨⟨x, y⟩, hxy⟩ := d
      simp only [Dart.edge_mk]
      have hK := (hK'adj x y hxy).1
      rw [hWbip x y hK]
      have hw2xy := hw2 x y hK
      have hnx : wnxt q x = y := wnxt_dart q hq _ hd
      have hpy : wprv q y = x := wprv_dart q hq _ hd
      have hxb : x ≠ b := walk_fst_ne_end q hq _ hd
      have hya : y ≠ a := walk_snd_ne_start q hq _ hd
      have hxq : x ∈ q.support := q.dart_fst_mem_support_of_mem_darts hd
      have hyq : y ∈ q.support := q.dart_snd_mem_support_of_mem_darts hd
      by_cases hxB : x ∈ B
      · simp only [dval, hxB, if_true]
        by_cases hxa : x = a
        · subst hxa
          have he := hend x hxB (by simp) (by simpa [en, hnx] using hK)
          simp only [en, if_true, hnx] at he
          rw [hσdef, if_pos rfl, hsdef]
          rw [hdK x hxB] at he
          have eα := hαβ x
          simp only [cor, c0, hva.symm, if_true] at eα
          by_cases hc : caseB
          · have := (hcB hc).1
            simp only [hc, and_self, if_true] at eα ⊢
            have h3 : w2 s(x, y) ≠ 3 := he.2 (by omega)
            omega
          · simp only [hc, false_and, if_false] at eα ⊢
            rcases hβa with h1 | h1
            · simp only [h1, if_true]
              have h3 : w2 s(x, y) ≠ 3 := he.2 (by omega)
              omega
            · simp only [h1, show ¬ ((3 : ℤ) = 1) by norm_num, if_false]
              have h3 : w2 s(x, y) ≠ 1 := he.1 (by omega)
              omega
        · -- internal blue vertex
          have hpo : x ∈ pairOn := by
            simp only [pairOn, mem_sdiff, mem_filter, mem_insert, mem_singleton, not_or]
            exact ⟨⟨hxB, hxq⟩, hxa, hxb⟩
          obtain ⟨d', hd', hd's⟩ := walk_in_dart q x hxq hxa
          have hpx : wprv q x = d'.fst := by rw [← hd's]; exact wprv_dart q hq d' hd'
          have hK2 : (bip G R B).Adj x (wprv q x) := by
            rw [hpx]; have := (hK'adj _ _ d'.adj).1; rw [hd's] at this; exact this.symm
          have hne : wprv q x ≠ wnxt q x := by
            intro he
            have : d' = ⟨(x, y), hxy⟩ := by
              apply walk_dart_edge_inj q hq d' _ hd' hd
              rw [Dart.edge, Dart.edge]
              simp only
              rw [← hd's, ← hpx, he, hnx]; exact Sym2.eq_swap
            have := congrArg (fun d : K'.Dart => d.toProd.2) this
            simp only at this
            rw [hd's] at this
            exact (G.ne_of_adj hK.1) (by first | exact this | exact this.symm)
          have hp := hpair x hxB hpo hne hK2 (by rw [hnx]; exact hK)
          rw [hnx] at hp
          have hw2p := hw2 x (wprv q x) hK2
          have := sigma_choice (w2 s(x, wprv q x)) (w2 s(x, y)) hw2p hw2xy
            ⟨by linarith [hp.1], by linarith [hp.2]⟩
          rw [hσdef, if_neg hxa, if_neg hxb, hnx]
          rw [hWbip x y hK, hWbip x (wprv q x) hK2]
          exact this.1
      · have hyB : y ∈ B := by by_contra hh; exact hxB ((hbip x y hK).mpr hh)
        simp only [dval, hxB, if_false]
        by_cases hyb : y = b
        · subst hyb
          have he := hend y hyB (by simp) (by
            simp only [en, hya, if_false, hpy]; exact hK.symm)
          simp only [en, hya, if_false, hpy] at he
          rw [hσdef, if_neg hya, if_pos rfl, hsdef]
          rw [hdK y hyB] at he
          have eα := hαβ y
          simp only [cor, c0, hvb.symm, if_true, Ne.symm hab, and_false, if_false] at eα
          rw [Sym2.eq_swap] at he
          by_cases hc : caseB
          · have := (hcB hc).2
            simp only [hc, if_true]
            have h3 : w2 s(x, y) ≠ 3 := he.2 (by omega)
            omega
          · simp only [hc, if_false]
            have hββ : β a = β y := by by_contra hh; exact hc hh
            rcases hβa with h1 | h1
            · simp only [h1, if_true]
              have h3 : w2 s(x, y) ≠ 3 := he.2 (by omega)
              omega
            · simp only [h1, show ¬ ((3 : ℤ) = 1) by norm_num, if_false]
              have h3 : w2 s(x, y) ≠ 1 := he.1 (by omega)
              omega
        · -- internal blue vertex y, incoming dart
          have hpo : y ∈ pairOn := by
            simp only [pairOn, mem_sdiff, mem_filter, mem_insert, mem_singleton, not_or]
            exact ⟨⟨hyB, hyq⟩, hya, hyb⟩
          obtain ⟨d', hd', hd'f⟩ := walk_out_dart q y hyq hyb
          have hny : wnxt q y = d'.snd := by rw [← hd'f]; exact wnxt_dart q hq d' hd'
          have hK2 : (bip G R B).Adj y (wnxt q y) := by
            rw [hny]; have := (hK'adj _ _ d'.adj).1; rw [hd'f] at this; exact this
          have hne : wprv q y ≠ wnxt q y := by
            intro he
            have : d' = ⟨(x, y), hxy⟩ := by
              apply walk_dart_edge_inj q hq d' _ hd' hd
              rw [Dart.edge, Dart.edge]
              simp only
              rw [← hd'f, ← hny, ← he, hpy]; exact Sym2.eq_swap
            have := congrArg (fun d : K'.Dart => d.toProd.1) this
            simp only at this
            rw [hd'f] at this
            exact (G.ne_of_adj hK.1) (by first | exact this | exact this.symm)
          have hp := hpair y hyB hpo hne (by rw [hpy]; exact hK.symm) hK2
          rw [hpy] at hp
          have hw2n := hw2 y (wnxt q y) hK2
          have hw2xy' : 1 ≤ w2 s(y, x) ∧ w2 s(y, x) ≤ 3 := by rw [Sym2.eq_swap]; exact hw2xy
          have := sigma_choice (w2 s(y, x)) (w2 s(y, wnxt q y)) hw2xy' hw2n
            ⟨by linarith [hp.1], by linarith [hp.2]⟩
          rw [hσdef, if_neg hya, if_neg hyb, hpy]
          rw [hWbip y (wnxt q y) hK2, hWbip y x hK.symm]
          rw [Sym2.eq_swap (a := x)]
          have h4 := this.2
          constructor <;> split_ifs at h4 ⊢ <;> omega
    refine ⟨W', vc_of_parity G R B hdisj hind v0 hsupp W' ?_ (fun v hv => by
        rw [hblue v hv, hsdB v hv]; exact hfo v) hred ?_ ?_ ?_⟩
    · intro x y hxy
      rw [hW'def]
      by_cases hq' : s(x, y) ∈ q.edges
      · obtain ⟨d, hd, hde⟩ : ∃ d ∈ q.darts, d.edge = s(x, y) := by
          rw [Walk.edges] at hq'; simpa using hq'
        have hE : E0 s(x, y) = 0 := by
          rw [hE0def]
          have h1 : s(x, y) ≠ s(v0, a) := fun h => hv0q (by
            have := q.fst_mem_support_of_mem_edges (h ▸ hq'); exact this)
          have h2 : s(x, y) ≠ s(v0, b) := fun h => hv0q (by
            have := q.fst_mem_support_of_mem_edges (h ▸ hq'); exact this)
          simp [h1, h2]
        rw [hE, add_zero, ← hde, hΔdef, swD_dart B σ q hq d hd]
        exact hdart d hd
      · have hΔ : Δ s(x, y) = 0 := swD_zero B σ q _ hq'
        rw [hΔ, zero_add]
        have hW := hwW x y hxy
        rw [hE0def]
        split_ifs with h1 h2
        · rw [h1, hWv0]; simp only [c3, c0]
          have haR : a ∉ R := fun h => hRB a h ha
          rw [hsdef]
          by_cases hc : caseB
          · simp [haR, hc]
          · simp only [haR, hc, if_false, false_and]; split_ifs <;> omega
        · rw [h2, hWv0]; simp only [c3, c0]
          have hbR : b ∉ R := fun h => hRB b h hb
          rw [hsdef]
          simp only [hbR, if_false, Ne.symm hab, and_false]
          split_ifs <;> omega
        · omega
    · rw [hsd0']; obtain ⟨r, hr⟩ := hev0; exact ⟨r - s, by omega⟩
    · intro u hu v hv huv
      rw [hblue u hu, hblue v hv]; exact hBB u hu v hv huv
    · intro r hr hadj
      rw [(hN0 r hr).mp hadj, hsd0', hsdu0', hconf]
      rcases hs with h | h <;> rw [h] <;> omega
  by_cases hw : β a = 1 ∧ β b = 3
  · exact main b a hb ha (Ne.symm hab) hvb hva hreach.symm (by omega)
  · exact main a b ha hb hab hva hvb hreach hw

end Rearr
section Divide
variable {V : Type} [Fintype V] [DecidableEq V]
open SimpleGraph

lemma reach_mono_on {H1 H2 : SimpleGraph V} {p v : V} (h : H1.Reachable p v)
    (hle : ∀ x y, H1.Reachable p x → H1.Adj x y → H2.Adj x y) : H2.Reachable p v := by
  have key : ∀ x (w : H1.Walk x v), H1.Reachable p x → H2.Reachable p x → H2.Reachable p v := by
    intro x w
    clear h
    induction w with
    | nil => intro _ h; exact h
    | cons hadj w ih =>
      intro h1 h2
      exact ih (h1.trans hadj.reachable) (h2.trans (hle _ _ h1 hadj).reachable)
  obtain ⟨w⟩ := h
  exact key p w (Reachable.refl p) (Reachable.refl p)

lemma reach_avoid {H : SimpleGraph V} {a b : V} (w : H.Walk a b) (X : Finset V)
    (h : ∀ v ∈ w.support, v ∉ X) : (delv H X).Reachable a b := by
  induction w with
  | nil => exact Reachable.refl _
  | cons hadj w ih =>
    simp only [Walk.support_cons, List.mem_cons, forall_eq_or_imp] at h
    exact (Reachable.trans ⟨Walk.cons ((delv_adj H X _ _).mpr ⟨hadj, h.1,
      h.2 _ w.start_mem_support⟩) Walk.nil⟩ (ih h.2))

lemma first_hit {H : SimpleGraph V} {s t b : V} (h : H.Reachable s t) (hsb : s ≠ b)
    (hbt : b ≠ t) : (delv H {b}).Reachable s t ∨ (delv H {t}).Reachable s b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Or.inl (Reachable.refl _)
  | cons hadj w ih =>
    rename_i x y z
    by_cases hxz : x = z
    · subst hxz; exact Or.inl (Reachable.refl _)
    by_cases hyb : y = b
    · subst hyb
      exact Or.inr ⟨Walk.cons ((delv_adj H _ _ _).mpr ⟨hadj, by simpa using hxz,
        by simpa using hbt⟩) Walk.nil⟩
    rcases ih hyb hbt with h1 | h1
    · exact Or.inl ((Reachable.trans ⟨Walk.cons ((delv_adj H _ _ _).mpr ⟨hadj, by simpa using hsb,
        by simpa using hyb⟩) Walk.nil⟩) h1)
    · by_cases hyz : y = z
      · subst hyz
        exact Or.inl ⟨Walk.cons ((delv_adj H _ _ _).mpr ⟨hadj, by simpa using hsb,
          by simpa using hyb⟩) Walk.nil⟩
      · exact Or.inr ((Reachable.trans ⟨Walk.cons ((delv_adj H _ _ _).mpr ⟨hadj,
          by simpa using hxz, by simpa using hyz⟩) Walk.nil⟩) h1)

/-- Keusch, Lemma 1 (with a seed): a red independent set with connected bipartite graph. -/
theorem divide (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V)
    (hsupp : ∀ a b, H.Adj a b → a ∈ U) (hconn : ∀ a ∈ U, ∀ b ∈ U, H.Reachable a b)
    (P R0 : Finset V) (hPU : P ⊆ U) (hR0P : R0 ⊆ P) (p0 : V) (hp0 : p0 ∈ P)
    (hR0ind : ∀ a ∈ R0, ∀ b ∈ R0, ¬ H.Adj a b)
    (hseed : ∀ a ∈ P, (bip H R0 (P \ R0)).Reachable p0 a) :
    ∃ R ⊆ U, (∀ a ∈ R, ∀ b ∈ R, ¬ H.Adj a b) ∧ (∀ v ∈ P, v ∈ R ↔ v ∈ R0) ∧
      ∀ a ∈ U, ∀ b ∈ U, (bip H R (U \ R)).Reachable a b := by
  classical
  let F : Finset (Finset V) := U.powerset.filter (fun R =>
    (∀ a ∈ R, ∀ b ∈ R, ¬ H.Adj a b) ∧ ∀ v ∈ P, v ∈ R ↔ v ∈ R0)
  have hR0F : R0 ∈ F := by
    simp only [F, mem_filter, mem_powerset]
    exact ⟨hR0P.trans hPU, hR0ind, by intro v _; simp⟩
  let K : Finset V → Finset V := fun R => U.filter (fun v => (bip H R (U \ R)).Reachable p0 v)
  obtain ⟨R, hRF, hRmax⟩ := exists_max_image F (fun R => (K R).card) ⟨R0, hR0F⟩
  simp only [F, mem_filter, mem_powerset] at hRF
  obtain ⟨hRU, hRind, hRP⟩ := hRF
  -- the seed lies in the component of p0
  have hPK : ∀ v ∈ P, (bip H R (U \ R)).Reachable p0 v := by
    intro v hv
    apply (hseed v hv).mono
    intro a b hab
    simp only [bip_adj, mem_sdiff] at hab ⊢
    refine ⟨hab.1, ?_⟩
    rcases hab.2 with ⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inl ⟨(hRP a (hR0P h1)).mpr h1, hPU h2, fun h => h3 ((hRP b h2).mp h)⟩
    · exact Or.inr ⟨⟨hPU h1, fun h => h2 ((hRP a h1).mp h)⟩, (hRP b (hR0P h3)).mpr h3⟩
  have hp0U : p0 ∈ U := hPU hp0
  -- every vertex of U is in the component
  have hall : ∀ v ∈ U, (bip H R (U \ R)).Reachable p0 v := by
    by_contra hno
    push Not at hno
    obtain ⟨v, hvU, hv⟩ := hno
    obtain ⟨a, b, hab, ha, hb⟩ := reach_cross H (K R) (hconn p0 hp0U v hvU)
      (by simp [K, hp0U]) (by simp [K, hv])
    simp only [K, mem_filter] at ha hb
    have hbU : b ∈ U := hsupp b a hab.symm
    have hb' : ¬ (bip H R (U \ R)).Reachable p0 b := fun h => hb ⟨hbU, h⟩
    -- a and b are blue
    have haR : a ∉ R := by
      intro haR
      have hbR : b ∉ R := fun hbR => hRind a haR b hbR hab
      exact hb' (ha.2.trans ⟨Walk.cons (by simp [hab, haR, hbU, hbR]) Walk.nil⟩)
    have hbR : b ∉ R := by
      intro hbR
      exact hb' (ha.2.trans ⟨Walk.cons (by simp [hab, haR, ha.1, hbR]) Walk.nil⟩)
    -- recolour b
    let R' : Finset V := insert b (R.filter (fun r => ¬ H.Adj b r))
    have hbP : b ∉ P := fun h => hb' (hPK b h)
    have hNbK : ∀ r ∈ R, H.Adj b r → ¬ (bip H R (U \ R)).Reachable p0 r := by
      intro r hr hbr hrr
      exact hb' (hrr.trans ⟨Walk.cons (by simp [hbr.symm, hr, hbU, hbR]) Walk.nil⟩)
    have hR'F : R' ∈ F := by
      simp only [F, mem_filter, mem_powerset]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx; simp only [R', mem_insert, mem_filter] at hx
        rcases hx with rfl | hx
        · exact hbU
        · exact hRU hx.1
      · intro x hx y hy hxy
        simp only [R', mem_insert, mem_filter] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact H.ne_of_adj hxy rfl
        · exact hy.2 hxy
        · exact hx.2 hxy.symm
        · exact hRind x hx.1 y hy.1 hxy
      · intro v hv
        rw [← hRP v hv]
        simp only [R', mem_insert, mem_filter]
        constructor
        · rintro (rfl | h)
          · exact absurd hv hbP
          · exact h.1
        · intro h
          right; refine ⟨h, fun hbv => hNbK v h hbv (hPK v hv)⟩
    have hsub : K R ⊆ K R' := by
      intro v hv
      simp only [K, mem_filter] at hv ⊢
      refine ⟨hv.1, reach_mono_on hv.2 ?_⟩
      intro x y hx hxy
      have hy : (bip H R (U \ R)).Reachable p0 y := hx.trans ⟨Walk.cons hxy Walk.nil⟩
      have hxb : x ≠ b := fun h => hb' (h ▸ hx)
      have hyb : y ≠ b := fun h => hb' (h ▸ hy)
      have hxN : ∀ r, r = x → r ∈ R → ¬ H.Adj b r := fun r hr hrR hbr => hNbK r hrR hbr (hr ▸ hx)
      have hyN : ∀ r, r = y → r ∈ R → ¬ H.Adj b r := fun r hr hrR hbr => hNbK r hrR hbr (hr ▸ hy)
      simp only [bip_adj, mem_sdiff, R', mem_insert, mem_filter, not_or, not_and,
        not_not] at hxy ⊢
      refine ⟨hxy.1, ?_⟩
      rcases hxy.2 with ⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
      · left
        exact ⟨Or.inr ⟨h1, hxN x rfl h1⟩, h2, hyb, fun h => absurd h h3⟩
      · right
        exact ⟨⟨h1, hxb, fun h => absurd h h2⟩, Or.inr ⟨h3, hyN y rfl h3⟩⟩
    have hbK' : b ∈ K R' := by
      simp only [K, mem_filter]
      refine ⟨hbU, ?_⟩
      have haK' : (bip H R' (U \ R')).Reachable p0 a := by
        have := hsub (show a ∈ K R by simp [K, ha.1, ha.2])
        simp only [K, mem_filter] at this; exact this.2
      refine haK'.trans ⟨Walk.cons ?_ Walk.nil⟩
      rw [bip_adj]
      refine ⟨hab, Or.inr ⟨mem_sdiff.mpr ⟨ha.1, ?_⟩, mem_insert_self _ _⟩⟩
      simp only [R', mem_insert, mem_filter, not_or]
      exact ⟨H.ne_of_adj hab, fun h => haR h.1⟩
    have hlt : (K R).card < (K R').card := by
      apply card_lt_card
      refine ⟨hsub, fun h => ?_⟩
      have := h hbK'
      simp only [K, mem_filter] at this
      exact hb' this.2
    have := hRmax R' hR'F
    omega
  refine ⟨R, hRU, hRind, hRP, fun a ha b hb => (hall a ha).symm.trans (hall b hb)⟩

end Divide
section Seed
variable {V : Type} [Fintype V] [DecidableEq V]
open SimpleGraph

lemma reach_mem (H : SimpleGraph V) (U : Finset V) (hsupp : ∀ a b, H.Adj a b → a ∈ U)
    {a b : V} (h : H.Reachable a b) (ha : a ∈ U) : b ∈ U := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ha
  | cons hadj w ih => exact ih (hsupp _ _ hadj.symm)

lemma delv_reach_out (H : SimpleGraph V) (X : Finset V) {c v : V}
    (h : (delv H X).Reachable c v) (hc : c ∉ X) : v ∉ X := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hc
  | cons hadj w ih => exact ih ((delv_adj H X _ _).mp hadj).2.2

lemma reach_delv_mono (H : SimpleGraph V) (X Y : Finset V) {c v : V}
    (h : (delv H X).Reachable c v) (hY : ∀ z, (delv H X).Reachable c z → z ∉ Y) :
    (delv H Y).Reachable c v := by
  apply reach_mono_on h
  intro x1 y1 hx hxy
  have hy : (delv H X).Reachable c y1 := hx.trans hxy.reachable
  exact (delv_adj H Y _ _).mpr ⟨((delv_adj H X _ _).mp hxy).1, hY x1 hx, hY y1 hy⟩

/-- a shortest connection between two vertex sets, as a seed for `divide` -/
theorem path_seed (H : SimpleGraph V) [DecidableRel H.Adj] (A Bs : Finset V) (a0 b0 : V)
    (ha0 : a0 ∈ A) (hb0 : b0 ∈ Bs) (hr : H.Reachable a0 b0) :
    ∃ za ∈ A, ∃ zb ∈ Bs, ∃ P R0 : Finset V, za ∈ P ∧ zb ∈ P ∧ za ∉ R0 ∧ R0 ⊆ P ∧
      (∀ c ∈ R0, ∀ d ∈ R0, ¬ H.Adj c d) ∧ (∀ c ∈ P, (bip H R0 (P \ R0)).Reachable za c) ∧
      (∀ v ∈ P, (v ∈ A ∨ v ∈ Bs) → v = za ∨ v = zb) ∧ (za = zb ∨ (za ∉ Bs ∧ zb ∉ A)) ∧
      (∀ v ∈ P, H.Reachable za v) := by
  classical
  have hex : ∃ n, ∃ a ∈ A, ∃ b ∈ Bs, ∃ w : H.Walk a b, w.length = n :=
    ⟨_, a0, ha0, b0, hb0, hr.some, rfl⟩
  obtain ⟨a, ha, b, hb, w, hw⟩ := Nat.find_spec hex
  set n := Nat.find hex with hn
  have hmin : ∀ a' ∈ A, ∀ b' ∈ Bs, ∀ w' : H.Walk a' b', n ≤ w'.length := by
    intro a' ha' b' hb' w'
    exact Nat.find_min' hex ⟨a', ha', b', hb', w', rfl⟩
  let g : ℕ → V := fun i => w.getVert i
  have hg0 : g 0 = a := w.getVert_zero
  have hgn : g n = b := by simp only [g, ← hw]; exact w.getVert_length
  have F3 : ∀ i j, i < j → j ≤ n → g i ≠ g j := by
    intro i j hij hj he
    let w' : H.Walk a b := (w.take i).append ((w.drop j).copy he.symm rfl)
    have := hmin a ha b hb w'
    simp only [w', Walk.length_append, Walk.take_length, Walk.length_copy, Walk.drop_length] at this
    omega
  have F2 : ∀ i j, i + 2 ≤ j → j ≤ n → ¬ H.Adj (g i) (g j) := by
    intro i j hij hj hadj
    let w' : H.Walk a b := (w.take i).append (Walk.cons hadj (w.drop j))
    have := hmin a ha b hb w'
    simp only [w', Walk.length_append, Walk.take_length, Walk.length_cons,
      Walk.drop_length] at this
    omega
  have F1a : ∀ i, 0 < i → i ≤ n → g i ∉ A := by
    intro i hi hin hgA
    have := hmin _ hgA b hb (w.drop i)
    simp only [Walk.drop_length] at this; omega
  have F1b : ∀ i, i < n → g i ∉ Bs := by
    intro i hi hgB
    have := hmin a ha _ hgB (w.take i)
    simp only [Walk.take_length] at this; omega
  let P : Finset V := (range (n + 1)).image g
  let R0 : Finset V := ((range (n + 1)).filter (fun i => Odd i)).image g
  have hgP : ∀ i, i ≤ n → g i ∈ P := fun i hi => mem_image_of_mem g (by simp; omega)
  have hR0iff : ∀ i, i ≤ n → (g i ∈ R0 ↔ Odd i) := by
    intro i hi
    constructor
    · intro h
      simp only [R0, mem_image, mem_filter, mem_range] at h
      obtain ⟨j, ⟨hj, hjo⟩, hji⟩ := h
      rcases lt_trichotomy i j with h | h | h
      · exact absurd hji.symm (F3 i j h (by omega))
      · rw [h]; exact hjo
      · exact absurd hji (F3 j i h hi)
    · intro h; exact mem_image_of_mem g (by simp [h]; omega)
  refine ⟨a, ha, b, hb, P, R0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hg0]; exact hgP 0 (by omega)
  · rw [← hgn]; exact hgP n le_rfl
  · rw [← hg0, hR0iff 0 (by omega)]; simp
  · exact image_subset_image (filter_subset _ _)
  · intro c hc d hd hcd
    simp only [R0, mem_image, mem_filter, mem_range] at hc hd
    obtain ⟨i, ⟨hi, hio⟩, rfl⟩ := hc
    obtain ⟨j, ⟨hj, hjo⟩, rfl⟩ := hd
    rcases lt_trichotomy i j with h | h | h
    · obtain ⟨k, rfl⟩ := hio; obtain ⟨l, rfl⟩ := hjo
      exact F2 (2 * k + 1) (2 * l + 1) (by omega) (by omega) hcd
    · subst h; exact H.ne_of_adj hcd rfl
    · obtain ⟨k, rfl⟩ := hio; obtain ⟨l, rfl⟩ := hjo
      exact F2 (2 * l + 1) (2 * k + 1) (by omega) (by omega) hcd.symm
  · have key : ∀ i, i ≤ n → (bip H R0 (P \ R0)).Reachable a (g i) := by
      intro i
      induction i with
      | zero => intro _; rw [hg0]
      | succ i ih =>
        intro hi
        refine (ih (by omega)).trans (Adj.reachable ?_)
        have hadj : H.Adj (g i) (g (i + 1)) := w.adj_getVert_succ (by omega)
        rw [bip_adj]
        refine ⟨hadj, ?_⟩
        by_cases ho : Odd i
        · left
          refine ⟨(hR0iff i (by omega)).mpr ho, mem_sdiff.mpr ⟨hgP _ hi, ?_⟩⟩
          rw [hR0iff _ hi]; intro h'; exact (Nat.not_odd_iff_even.mpr (ho.add_one)) h'
        · right
          refine ⟨mem_sdiff.mpr ⟨hgP _ (by omega), ?_⟩, ?_⟩
          · rw [hR0iff _ (by omega)]; exact ho
          · rw [hR0iff _ hi]; exact (Nat.not_odd_iff_even.mp ho).add_one
    intro c hc
    simp only [P, mem_image, mem_range] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    exact key i (by omega)
  · intro v hv hAB
    simp only [P, mem_image, mem_range] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    by_cases h0 : i = 0
    · left; rw [h0, hg0]
    by_cases hn' : i = n
    · right; rw [hn', hgn]
    rcases hAB with h | h
    · exact absurd h (F1a i (by omega) (by omega))
    · exact absurd h (F1b i (by omega))
  · by_cases h0 : n = 0
    · left; rw [← hg0, ← hgn, h0]
    · right
      exact ⟨by rw [← hg0]; exact F1b 0 (by omega), by rw [← hgn]; exact F1a n (by omega) le_rfl⟩
  · intro v hv
    simp only [P, mem_image, mem_range] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    exact ⟨w.take i⟩

/-- Keusch, Lemma 8: an edge whose removal (with both ends) keeps the graph connected. -/
theorem blocks (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U) (hconn : ∀ a ∈ U, ∀ b ∈ U, G.Reachable a b)
    (hdeg : ∀ v ∈ U, 2 ≤ (univ.filter (G.Adj v)).card) (h3 : 3 ≤ U.card) :
    ∃ x y, G.Adj x y ∧ ∀ a ∈ U \ {x, y}, ∀ b ∈ U \ {x, y}, (delv G {x, y}).Reachable a b := by
  classical
  let T : Finset ((V × V) × V) := ((U ×ˢ U) ×ˢ U).filter
    (fun t => G.Adj t.1.1 t.1.2 ∧ t.2 ≠ t.1.1 ∧ t.2 ≠ t.1.2)
  let Comp : (V × V) × V → Finset V := fun t =>
    U.filter (fun v => (delv G {t.1.1, t.1.2}).Reachable t.2 v)
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < U.card)
    obtain ⟨y, hy⟩ := card_pos.mp (by have := hdeg x hx; omega :
      0 < (univ.filter (G.Adj x)).card)
    have hxy : G.Adj x y := (mem_filter.mp hy).2
    have hyU : y ∈ U := hsupp y x hxy.symm
    have : 0 < (U \ {x, y}).card := by
      have h1 : ({x, y} : Finset V) ⊆ U := by
        intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
      rw [card_sdiff_of_subset h1]
      have := card_le_two (a := x) (b := y); omega
    obtain ⟨c, hc⟩ := card_pos.mp this
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hc
    exact ⟨((x, y), c), by simp [T, hx, hyU, hc.1, hxy, hc.2.1, hc.2.2]⟩
  obtain ⟨⟨⟨x, y⟩, c⟩, htT, hmax⟩ := exists_max_image T (fun t => (Comp t).card) hTne
  simp only [T, mem_filter, mem_product] at htT
  obtain ⟨⟨⟨hxU, hyU⟩, hcU⟩, hxy, hcx, hcy⟩ := htT
  refine ⟨x, y, hxy, ?_⟩
  have hcX : c ∉ ({x, y} : Finset V) := by simp [hcx, hcy]
  set C := Comp ((x, y), c) with hC
  have hCmem : ∀ v, v ∈ C ↔ v ∈ U ∧ (delv G {x, y}).Reachable c v := by
    intro v; simp [hC, Comp]
  have hCX : ∀ v ∈ C, v ∉ ({x, y} : Finset V) := fun v hv =>
    delv_reach_out G _ ((hCmem v).mp hv).2 hcX
  have grow : ∀ t ∈ T, C ⊆ Comp t → ∀ z ∈ Comp t, z ∉ C → False := by
    intro t ht hsub z hz hzC
    have := hmax t ht
    have : C.card < (Comp t).card := card_lt_card ⟨hsub, fun h => hzC (h hz)⟩
    omega
  have hall : ∀ d ∈ U \ {x, y}, (delv G {x, y}).Reachable c d := by
    intro d hd
    by_contra hnd
    have hdU : d ∈ U := (mem_sdiff.mp hd).1
    have hdX : d ∉ ({x, y} : Finset V) := (mem_sdiff.mp hd).2
    have hdC : d ∉ C := fun h => hnd ((hCmem d).mp h).2
    -- a vertex of C adjacent to x or y
    have hcC : c ∈ C := (hCmem c).mpr ⟨hcU, Reachable.refl _⟩
    have hxC : x ∉ C := fun h => hCX x h (by simp)
    obtain ⟨u, u', huu', huC, hu'C⟩ := reach_cross G C (hconn c hcU x hxU) hcC hxC
    have hu'X : u' ∈ ({x, y} : Finset V) := by
      by_contra hh
      apply hu'C
      rw [hCmem]
      refine ⟨hsupp u' u huu'.symm, ((hCmem u).mp huC).2.trans (Adj.reachable ?_)⟩
      exact (delv_adj G _ _ _).mpr ⟨huu', hCX u huC, hh⟩
    have hTmem : ∀ x' y' c', x' ∈ U → y' ∈ U → c' ∈ U → G.Adj x' y' → c' ≠ x' → c' ≠ y' →
        ((x', y'), c') ∈ T := by
      intro x' y' c' h1 h2 h3 h4 h5 h6; simp [T, h1, h2, h3, h4, h5, h6]
    have hCsub : ∀ x' y', (∀ v ∈ C, v ≠ x' ∧ v ≠ y') → C ⊆ Comp ((x', y'), c) := by
      intro x' y' hav v hv
      simp only [Comp, mem_filter]
      refine ⟨((hCmem v).mp hv).1, reach_delv_mono G _ _ ((hCmem v).mp hv).2 ?_⟩
      intro z hz
      have : z ∈ C := (hCmem z).mpr ⟨reach_mem G U hsupp (hz.mono (fun a b h => ((delv_adj G _ a b).mp h).1)) hcU, hz⟩
      simp [(hav z this).1, (hav z this).2]
    have hreachC : ∀ x' y' v, (∀ v ∈ C, v ≠ x' ∧ v ≠ y') → v ∈ C →
        (delv G {x', y'}).Reachable c v := by
      intro x' y' v hav hv
      have := hCsub x' y' hav hv
      simp only [Comp, mem_filter] at this; exact this.2
    by_cases hi : ∃ d', G.Adj d d' ∧ d' ∉ ({x, y} : Finset V)
    · obtain ⟨d', hdd', hd'X⟩ := hi
      have hd'U : d' ∈ U := hsupp d' d hdd'.symm
      have hd'C : d' ∉ C := by
        intro h
        exact hdC ((hCmem d).mpr ⟨hdU, ((hCmem d').mp h).2.trans (Adj.reachable
          ((delv_adj G _ _ _).mpr ⟨hdd'.symm, hd'X, hdX⟩))⟩)
      have hav : ∀ v ∈ C, v ≠ d ∧ v ≠ d' :=
        fun v hv => ⟨fun h => hdC (h ▸ hv), fun h => hd'C (h ▸ hv)⟩
      have hxd : x ≠ d := fun h => hdX (by simp [h])
      have hyd : y ≠ d := fun h => hdX (by simp [h])
      have hxd' : x ≠ d' := fun h => hd'X (by simp [h])
      have hyd' : y ≠ d' := fun h => hd'X (by simp [h])
      have hx' : (delv G {d, d'}).Reachable c x := by
        have huR := hreachC d d' u hav huC
        have hud := hav u huC
        simp only [mem_insert, mem_singleton] at hu'X
        rcases hu'X with rfl | rfl
        · exact huR.trans (Adj.reachable ((delv_adj G _ _ _).mpr
            ⟨huu', by simp [hud.1, hud.2], by simp [hxd, hxd']⟩))
        · refine (huR.trans (Adj.reachable ((delv_adj G _ _ _).mpr
            ⟨huu', by simp [hud.1, hud.2], by simp [hyd, hyd']⟩))).trans (Adj.reachable ?_)
          exact (delv_adj G _ _ _).mpr ⟨hxy.symm, by simp [hyd, hyd'], by simp [hxd, hxd']⟩
      exact grow _ (hTmem d d' c hdU hd'U hcU hdd' (fun h => hdC (h ▸ hcC))
        (fun h => hd'C (h ▸ hcC))) (hCsub d d' hav) x
        (by simp only [Comp, mem_filter]; exact ⟨hxU, hx'⟩) hxC
    · push Not at hi
      have hdx : G.Adj d x ∧ G.Adj d y := by
        have hsub : univ.filter (G.Adj d) ⊆ {x, y} := by
          intro z hz; exact hi z (mem_filter.mp hz).2
        have h2 := hdeg d hdU
        have hcard := card_le_card hsub
        have hxyne : x ≠ y := G.ne_of_adj hxy
        rw [card_pair hxyne] at hcard
        have heq := eq_of_subset_of_card_le hsub (by rw [card_pair hxyne]; omega)
        constructor
        · have : x ∈ univ.filter (G.Adj d) := by rw [heq]; simp
          exact (mem_filter.mp this).2
        · have : y ∈ univ.filter (G.Adj d) := by rw [heq]; simp
          exact (mem_filter.mp this).2
      have hyC : y ∉ C := fun h => hCX y h (by simp)
      have hxd : x ≠ d := fun h => hdX (by simp [h])
      have hyd : y ≠ d := fun h => hdX (by simp [h])
      simp only [mem_insert, mem_singleton] at hu'X
      rcases hu'X with hux | huy
      · rw [hux] at huu'
        refine grow _ (hTmem y d c hyU hdU hcU hdx.2.symm hcy (fun h => hdC (h ▸ hcC)))
          (hCsub y d (fun v hv => ⟨fun h => hyC (h ▸ hv), fun h => hdC (h ▸ hv)⟩)) x ?_ hxC
        simp only [Comp, mem_filter]
        refine ⟨hxU, (hreachC y d u (fun v hv => ⟨fun h => hyC (h ▸ hv),
          fun h => hdC (h ▸ hv)⟩) huC).trans (Adj.reachable ((delv_adj G _ _ _).mpr ⟨huu', ?_, ?_⟩))⟩
        · simp only [mem_insert, mem_singleton, not_or]
          exact ⟨fun h => hyC (h ▸ huC), fun h => hdC (h ▸ huC)⟩
        · simp only [mem_insert, mem_singleton, not_or]
          exact ⟨G.ne_of_adj hxy, hxd⟩
      · rw [huy] at huu'
        refine grow _ (hTmem x d c hxU hdU hcU hdx.1.symm hcx (fun h => hdC (h ▸ hcC)))
          (hCsub x d (fun v hv => ⟨fun h => hxC (h ▸ hv), fun h => hdC (h ▸ hv)⟩)) y ?_ hyC
        simp only [Comp, mem_filter]
        refine ⟨hyU, (hreachC x d u (fun v hv => ⟨fun h => hxC (h ▸ hv),
          fun h => hdC (h ▸ hv)⟩) huC).trans (Adj.reachable ((delv_adj G _ _ _).mpr ⟨huu', ?_, ?_⟩))⟩
        · simp only [mem_insert, mem_singleton, not_or]
          exact ⟨fun h => hxC (h ▸ huC), fun h => hdC (h ▸ huC)⟩
        · simp only [mem_insert, mem_singleton, not_or]
          exact ⟨(G.ne_of_adj hxy).symm, hyd⟩
  intro a ha b hb
  exact (hall a ha).symm.trans (hall b hb)

end Seed
section Tools
variable {V : Type} [Fintype V] [DecidableEq V]
open SimpleGraph

lemma vc_of_good (G : SimpleGraph V) [DecidableRel G.Adj] (R B : Finset V) (hg : Good G R B)
    (w : Sym2 V → ℤ) (hw : ∀ u v, G.Adj u v → 1 ≤ w s(u, v) ∧ w s(u, v) ≤ 3)
    (hB : ∀ v ∈ B, Odd (sd G w v)) (hR : ∀ v ∈ R, Even (sd G w v))
    (hBB : ∀ u ∈ B, ∀ v ∈ B, G.Adj u v → sd G w u ≠ sd G w v) : VC G w := by
  refine ⟨hw, fun a b hab => ?_⟩
  have haRB := hg.supp a b hab
  have hbRB := hg.supp b a hab.symm
  simp only [mem_union] at haRB hbRB
  rcases haRB with haR | haB <;> rcases hbRB with hbR | hbB
  · exact absurd hab (hg.indep a haR b hbR)
  · intro heq
    have := hR a haR; rw [heq] at this
    exact (Int.not_even_iff_odd.mpr (hB b hbB)) this
  · intro heq
    have := hR b hbR; rw [← heq] at this
    exact (Int.not_even_iff_odd.mpr (hB a haB)) this
  · exact hBB a haB b hbB hab

theorem basic_vc (G : SimpleGraph V) [DecidableRel G.Adj] (R B : Finset V) (hg : Good G R B) :
    ∃ w, VC G w := by
  obtain ⟨w, hw, hB, hR, hBB⟩ := basic G R B hg (fun _ => 0) (fun _ => ⟨0, by ring⟩)
  exact ⟨w, vc_of_good G R B hg w hw (fun v hv => by simpa using hB v hv) hR
    (fun u hu v hv h => by simpa using hBB u hu v hv h)⟩

lemma conn_ext {H : SimpleGraph V} (S T : Finset V) (hS : ∀ a ∈ S, ∀ b ∈ S, H.Reachable a b)
    (hT : ∀ t ∈ T, ∃ s ∈ S, H.Reachable t s) : ∀ a ∈ S ∪ T, ∀ b ∈ S ∪ T, H.Reachable a b := by
  have key : ∀ a ∈ S ∪ T, ∃ s ∈ S, H.Reachable a s := by
    intro a ha
    rcases mem_union.mp ha with h | h
    · exact ⟨a, h, Reachable.refl _⟩
    · exact hT a h
  intro a ha b hb
  obtain ⟨s1, hs1, h1⟩ := key a ha
  obtain ⟨s2, hs2, h2⟩ := key b hb
  exact h1.trans ((hS s1 hs1 s2 hs2).trans h2.symm)

lemma sd_nbr_congr (G1 G2 : SimpleGraph V) [DecidableRel G1.Adj] [DecidableRel G2.Adj]
    (w1 w2 : Sym2 V → ℤ) (v : V) (S : Finset V)
    (h : ∀ u ∉ S, (if G1.Adj v u then w1 s(v, u) else 0) = (if G2.Adj v u then w2 s(v, u) else 0)) :
    sd G2 w2 v = sd G1 w1 v + ∑ u ∈ S, ((if G2.Adj v u then w2 s(v, u) else 0) -
      (if G1.Adj v u then w1 s(v, u) else 0)) := by
  simp only [sd, sum_filter]
  rw [← sub_eq_iff_eq_add', ← sum_sub_distrib]
  symm; apply sum_subset (subset_univ S)
  intro u _ hu; rw [h u hu]; ring

lemma sd_pos (H : SimpleGraph V) [DecidableRel H.Adj] (w : Sym2 V → ℤ) (v u : V)
    (hvu : H.Adj v u) (hw : ∀ a, H.Adj v a → 1 ≤ w s(v, a)) : 1 ≤ sd H w v := by
  unfold sd
  have hu : u ∈ univ.filter (H.Adj v) := by simp [hvu]
  calc (1 : ℤ) ≤ w s(v, u) := hw u hvu
    _ ≤ ∑ a ∈ univ.filter (H.Adj v), w s(v, a) :=
      single_le_sum (f := fun a => w s(v, a))
        (fun a ha => le_trans zero_le_one (hw a (mem_filter.mp ha).2)) hu

lemma s2ne {a b c d : V} (h : a ≠ c) (h' : a ≠ d) : s(a, b) ≠ s(c, d) := by
  intro he
  have : a ∈ s(c, d) := he ▸ Sym2.mem_mk_left a b
  rw [Sym2.mem_iff] at this
  rcases this with h1 | h1
  · exact h h1
  · exact h' h1

lemma s2ne' {a b c d : V} (h : b ≠ c) (h' : b ≠ d) : s(a, b) ≠ s(c, d) := by
  rw [Sym2.eq_swap]; exact s2ne h h'

lemma path_two_nbrs {H : SimpleGraph V} {a b : V} (q : H.Walk a b) (hq : q.IsPath) (v : V)
    (hv : v ∈ q.support) (hva : v ≠ a) (hvb : v ≠ b) :
    ∃ u1 u2, u1 ≠ u2 ∧ H.Adj v u1 ∧ H.Adj v u2 := by
  obtain ⟨d1, hd1, hd1s⟩ := walk_in_dart q v hv hva
  obtain ⟨d2, hd2, hd2f⟩ := walk_out_dart q v hv hvb
  refine ⟨d1.fst, d2.snd, ?_, by rw [← hd1s]; exact d1.adj.symm, by rw [← hd2f]; exact d2.adj⟩
  intro he
  have : d1 = d2 := by
    apply walk_dart_edge_inj q hq d1 d2 hd1 hd2
    rw [Dart.edge, Dart.edge]
    have e1 : d1.toProd = (d1.fst, d1.snd) := rfl
    have e2 : d2.toProd = (d2.fst, d2.snd) := rfl
    rw [e1, e2, hd1s, hd2f, he]; exact Sym2.eq_swap
  have h1 : d1.snd = d2.snd := by rw [this]
  rw [hd1s] at h1
  have h2 : d1.fst = d2.fst := by rw [this]
  rw [hd2f] at h2
  rw [h2] at he
  exact H.ne_of_adj d2.adj (by rw [hd2f, ← h1])

lemma leaf_conn (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hconn : ∀ a ∈ U, ∀ b ∈ U, G.Reachable a b) (x : V)
    (hx : ∀ u1 u2, G.Adj x u1 → G.Adj x u2 → u1 = u2) :
    ∀ a ∈ U \ {x}, ∀ b ∈ U \ {x}, (delv G {x}).Reachable a b := by
  intro a ha b hb
  simp only [mem_sdiff, mem_singleton] at ha hb
  obtain ⟨p⟩ := hconn a ha.1 b hb.1
  obtain ⟨q, hq⟩ := p.toPath
  apply reach_avoid q {x}
  intro v hv hvx
  rw [mem_singleton] at hvx
  subst hvx
  obtain ⟨u1, u2, hne, h1, h2⟩ := path_two_nbrs q hq v hv (Ne.symm ha.2) (Ne.symm hb.2)
  exact hne (hx u1 u2 h1 h2)

lemma sd_atv_gen (G : SimpleGraph V) [DecidableRel G.Adj] (v0 : V) (c : V → ℤ)
    (w : Sym2 V → ℤ) (v : V) (hv : v ≠ v0) :
    sd G (atv v0 c w) v = sd (delv G {v0}) w v + (if G.Adj v v0 then c v else 0) := by
  have pt : ∀ u, (if G.Adj v u then atv v0 c w s(v, u) else 0) =
      (if (delv G {v0}).Adj v u then w s(v, u) else 0) +
      (if u = v0 then (if G.Adj v v0 then c v else 0) else 0) := by
    intro u
    by_cases hu : u = v0
    · subst hu
      have : ¬ (delv G {u}).Adj v u := fun h => by simp at h
      rw [if_neg this]; simp [atv_mk, hv]
    · by_cases hvu : G.Adj v u
      · have : (delv G {v0}).Adj v u := by simp [hvu, hv, hu]
        rw [if_pos hvu, if_pos this, atv_mk, if_neg hv, if_neg hu]; simp [hu]
      · have : ¬ (delv G {v0}).Adj v u := fun h => hvu h.1
        simp [hvu, this, hu]
  simp only [sd, sum_filter]
  rw [sum_congr rfl (fun u _ => pt u), sum_add_distrib, sum_ite_eq']
  simp

lemma filter_adj_pair (G : SimpleGraph V) [DecidableRel G.Adj] (x a b : V)
    (h : ∀ u, G.Adj x u ↔ u = a ∨ u = b) : univ.filter (G.Adj x) = {a, b} := by
  ext u; simp [h u]

lemma odd_term_of_odd_sum (s : Finset V) (f : V → ℤ) (h : Odd (∑ u ∈ s, f u)) :
    ∃ u ∈ s, Odd (f u) := by
  by_contra hno
  push Not at hno
  have : Even (∑ u ∈ s, f u) := by
    apply Finset.even_sum; intro u hu; exact Int.not_odd_iff_even.mp (hno u hu)
  exact (Int.not_even_iff_odd.mpr h) this

end Tools
section CaseA
variable {V : Type} [Fintype V] [DecidableEq V]
open SimpleGraph

lemma bip_mono (G : SimpleGraph V) {R B R1 B1 : Finset V} (hR : R ⊆ R1) (hB : B ⊆ B1) :
    bip G R B ≤ bip G R1 B1 := by
  intro a b h
  simp only [bip_adj] at h ⊢
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hR h1, hB h2⟩
  · exact Or.inr ⟨hB h1, hR h2⟩

lemma bip_delv_le (G : SimpleGraph V) (X R B : Finset V) : bip (delv G X) R B ≤ bip G R B := by
  intro a b h
  simp only [bip_adj, delv_adj] at h ⊢
  exact ⟨h.1.1, h.2⟩

lemma conn_cover {H : SimpleGraph V} (S T R1 B1 : Finset V) (hS : ∀ a ∈ S, ∀ b ∈ S, H.Reachable a b)
    (hcov : ∀ v, v ∈ R1 ∪ B1 ↔ v ∈ S ∨ v ∈ T) (hT : ∀ t ∈ T, ∃ s ∈ S, H.Reachable t s) :
    ∀ a ∈ R1 ∪ B1, ∀ b ∈ R1 ∪ B1, H.Reachable a b := by
  intro a ha b hb
  exact conn_ext S T hS hT a (mem_union.mpr ((hcov a).mp ha)) b (mem_union.mpr ((hcov b).mp hb))

/-- the setting after removing some vertices `X` and colouring the rest -/
structure Base (G : SimpleGraph V) (U X R : Finset V) : Prop where
  RU : R ⊆ U \ X
  ind : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b
  conn : ∀ a ∈ U \ X, ∀ b ∈ U \ X, (bip G R ((U \ X) \ R)).Reachable a b

lemma base_of_divide (G : SimpleGraph V) [DecidableRel G.Adj] (U X : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U)
    (hconn : ∀ a ∈ U \ X, ∀ b ∈ U \ X, (delv G X).Reachable a b)
    (P R0 : Finset V) (hPU : P ⊆ U \ X) (hR0P : R0 ⊆ P) (p0 : V) (hp0 : p0 ∈ P)
    (hR0ind : ∀ a ∈ R0, ∀ b ∈ R0, ¬ G.Adj a b)
    (hseed : ∀ a ∈ P, (bip (delv G X) R0 (P \ R0)).Reachable p0 a) :
    ∃ R, Base G U X R ∧ ∀ v ∈ P, v ∈ R ↔ v ∈ R0 := by
  have hsupp' : ∀ a b, (delv G X).Adj a b → a ∈ U \ X := fun a b h =>
    mem_sdiff.mpr ⟨hsupp a b h.1, h.2.1⟩
  obtain ⟨R, hRU, hRind, hRP, hRc⟩ := divide (delv G X) (U \ X) hsupp' hconn P R0 hPU hR0P p0 hp0
    (fun a ha b hb h => hR0ind a ha b hb h.1) hseed
  refine ⟨R, ⟨hRU, fun a ha b hb h => hRind a ha b hb ?_, fun a ha b hb =>
    (hRc a ha b hb).mono (bip_delv_le G X _ _)⟩, hRP⟩
  have ha' := mem_sdiff.mp (hRU ha)
  have hb' := mem_sdiff.mp (hRU hb)
  exact ⟨h, ha'.2, hb'.2⟩

lemma base_mem (G : SimpleGraph V) (U X R : Finset V) (hb : Base G U X R) (v : V) :
    v ∈ R ∪ ((U \ X) \ R) ↔ v ∈ U \ X := by
  constructor
  · intro h; rcases mem_union.mp h with h | h
    · exact hb.RU h
    · exact (mem_sdiff.mp h).1
  · intro h; by_cases hv : v ∈ R
    · exact mem_union_left _ hv
    · exact mem_union_right _ (mem_sdiff.mpr ⟨h, hv⟩)

lemma base_disj (G : SimpleGraph V) (U X R : Finset V) : Disjoint R ((U \ X) \ R) :=
  disjoint_sdiff

/-- Case: a vertex of degree one. -/
theorem caseA (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U) (hconn : ∀ a ∈ U, ∀ b ∈ U, G.Reachable a b)
    (x y : V) (hxU : x ∈ U) (hxleaf : ∀ u, G.Adj x u ↔ u = y) (hy2 : ∃ u, u ≠ x ∧ G.Adj y u) :
    ∃ w, VC G w := by
  have hxy : G.Adj x y := (hxleaf y).mpr rfl
  have hyU : y ∈ U := hsupp y x hxy.symm
  have hyx : y ≠ x := (G.ne_of_adj hxy).symm
  have hconn' := leaf_conn G U hconn x (fun u1 u2 h1 h2 =>
    ((hxleaf u1).mp h1).trans ((hxleaf u2).mp h2).symm)
  have hyU' : y ∈ U \ {x} := by simp [hyU, hyx]
  obtain ⟨R, hb, hRP⟩ := base_of_divide G U {x} hsupp hconn' {y} {y}
    (singleton_subset_iff.mpr hyU') (subset_refl _) y (mem_singleton_self y)
    (fun a ha b hb h => by
      rw [mem_singleton] at ha hb; subst ha; subst hb; exact G.ne_of_adj h rfl)
    (fun a ha => by rw [mem_singleton] at ha; subst ha; exact Reachable.refl _)
  have hyR : y ∈ R := (hRP y (mem_singleton_self y)).mpr (mem_singleton_self y)
  set B := (U \ {x}) \ R with hBdef
  have hxR : x ∉ R := fun h => by have := hb.RU h; simp at this
  have hxB : x ∉ B := by simp [hBdef]
  have hmem := base_mem G U {x} R hb
  by_cases hBo : Odd B.card
  · let B1 := insert x B
    have hg : Good G R B1 := by
      refine ⟨?_, hb.ind, ?_, ?_, ?_⟩
      · exact disjoint_insert_right.mpr ⟨hxR, base_disj G U {x} R⟩
      · apply conn_cover (U \ {x}) {x} R B1 (fun a ha b hb' =>
          (hb.conn a ha b hb').mono (bip_mono G (subset_refl _) (subset_insert _ _)))
        · intro v
          have := hmem v
          simp only [B1, mem_union, mem_insert, mem_singleton] at this ⊢
          constructor
          · rintro (h | h | h)
            · exact Or.inl (this.mp (Or.inl h))
            · exact Or.inr h
            · exact Or.inl (this.mp (Or.inr h))
          · rintro (h | h)
            · rcases this.mpr h with h' | h'
              · exact Or.inl h'
              · exact Or.inr (Or.inr h')
            · exact Or.inr (Or.inl h)
        · intro t ht
          rw [mem_singleton] at ht; subst ht
          exact ⟨y, hyU', Adj.reachable (by simp [B1, hxy, hyR])⟩
      · rw [card_insert_of_notMem hxB]; exact hBo.add_one
      · intro a b hab
        by_cases hax : a = x
        · subst hax; simp [B1]
        · have := (hmem a).mpr (by simp [hsupp a b hab, hax])
          simp only [mem_union] at this ⊢
          rcases this with h | h
          · exact Or.inl h
          · exact Or.inr (mem_insert_of_mem h)
    exact basic_vc G R B1 hg
  · have hBe : Even B.card := Nat.not_odd_iff_even.mp hBo
    have hg : Good (delv G {x}) R B := by
      refine ⟨base_disj G U {x} R, fun a ha b hb' h => hb.ind a ha b hb' h.1, ?_, hBe, ?_⟩
      · intro a ha b hb'
        have h1 := (hmem a).mp ha
        have h2 := (hmem b).mp hb'
        apply (hb.conn a h1 b h2).mono
        intro u v huv
        simp only [bip_adj, delv_adj] at huv ⊢
        refine ⟨⟨huv.1, ?_, ?_⟩, huv.2⟩
        · rcases huv.2 with ⟨h, _⟩ | ⟨h, _⟩
          · exact fun hu => hxR (by simp at hu; exact hu ▸ h)
          · exact fun hu => hxB (by simp at hu; exact hu ▸ h)
        · rcases huv.2 with ⟨_, h⟩ | ⟨_, h⟩
          · exact fun hu => hxB (by simp at hu; exact hu ▸ h)
          · exact fun hu => hxR (by simp at hu; exact hu ▸ h)
      · intro a b hab
        exact (hmem a).mpr (mem_sdiff.mpr ⟨hsupp a b hab.1, hab.2.1⟩)
    obtain ⟨w', hw', hB', hR', hBB'⟩ := basic (delv G {x}) R B hg (fun _ => 0) (fun _ => ⟨0, by ring⟩)
    let W := atv x (fun _ => 2) w'
    have hsdv : ∀ v, v ≠ x → sd G W v = sd (delv G {x}) w' v + (if G.Adj v x then 2 else 0) :=
      fun v hv => sd_atv_gen G x (fun _ => 2) w' v hv
    have hsupp_x : ∀ a b, G.Adj a b → a ≠ x → a ∈ R ∪ B := fun a b hab hax =>
      (hmem a).mpr (by simp [hsupp a b hab, hax])
    have hBnx : ∀ v ∈ B, ¬ G.Adj v x := by
      intro v hv h
      have := (hxleaf v).mp h.symm
      subst this
      exact (mem_sdiff.mp hv).2 hyR
    refine ⟨W, vc_of_parity G R B (base_disj G U {x} R) hb.ind x hsupp_x W ?_ ?_ ?_ ?_ ?_ ?_⟩
    · intro u v huv
      simp only [W, atv_mk]
      by_cases hu : u = x
      · simp [hu]
      by_cases hv : v = x
      · simp [hu, hv]
      simp only [hu, hv, if_false]
      exact hw' u v ⟨huv, by simpa using hu, by simpa using hv⟩
    · intro v hv
      have hvx : v ≠ x := fun h => hxB (h ▸ hv)
      rw [hsdv v hvx, if_neg (hBnx v hv)]
      simpa using hB' v hv
    · intro v hv
      have hvx : v ≠ x := fun h => hxR (h ▸ hv)
      rw [hsdv v hvx]
      obtain ⟨r, hr⟩ := hR' v hv
      split_ifs
      · exact ⟨r + 1, by omega⟩
      · exact ⟨r, by omega⟩
    · simp only [W]
      rw [sd_atv_v0]
      have : univ.filter (G.Adj x) = {y} := by ext u; simp [hxleaf u]
      rw [this, sum_singleton]; exact ⟨1, by ring⟩
    · intro u hu v hv huv
      have hux : u ≠ x := fun h => hxB (h ▸ hu)
      have hvx : v ≠ x := fun h => hxB (h ▸ hv)
      rw [hsdv u hux, hsdv v hvx, if_neg (hBnx u hu), if_neg (hBnx v hv)]
      have := hBB' u hu v hv ⟨huv, by simpa using hux, by simpa using hvx⟩
      simpa using this
    · intro r hr hxr
      have hry : r = y := (hxleaf r).mp hxr
      subst hry
      obtain ⟨u, hux, hyu⟩ := hy2
      have h1 : 1 ≤ sd (delv G {x}) w' r := sd_pos (delv G {x}) w' r u
        ⟨hyu, by simpa using hyx, by simpa using hux⟩
        (fun a ha => (hw' r a ha).1)
      have h2 : sd G W x = 2 := by
        simp only [W]; rw [sd_atv_v0]
        have : univ.filter (G.Adj x) = {r} := by ext u; simp [hxleaf u]
        rw [this, sum_singleton]
      rw [h2, hsdv r hyx, if_pos hxr.symm]
      omega

end CaseA
section Place
variable {V : Type} [Fintype V] [DecidableEq V]
open SimpleGraph

lemma place_common (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U) (X R : Finset V) (hb : Base G U X R)
    (Rn Bn : Finset V) (hRn : Rn ⊆ X) (hBn : Bn ⊆ X) (hdis : Disjoint Rn Bn)
    (hindn : ∀ a ∈ Rn, ∀ b ∈ R ∪ Rn, ¬ G.Adj a b)
    (hatt : ∀ t ∈ Rn ∪ Bn, ∃ s ∈ U \ X,
      (bip G (R ∪ Rn) (((U \ X) \ R) ∪ Bn)).Reachable t s) :
    Disjoint (R ∪ Rn) (((U \ X) \ R) ∪ Bn) ∧ (∀ a ∈ R ∪ Rn, ∀ b ∈ R ∪ Rn, ¬ G.Adj a b) ∧
    (∀ a ∈ (R ∪ Rn) ∪ (((U \ X) \ R) ∪ Bn), ∀ b ∈ (R ∪ Rn) ∪ (((U \ X) \ R) ∪ Bn),
      (bip G (R ∪ Rn) (((U \ X) \ R) ∪ Bn)).Reachable a b) := by
  have hmem := base_mem G U X R hb
  have hRX : ∀ v ∈ R, v ∉ X := fun v hv => (mem_sdiff.mp (hb.RU hv)).2
  refine ⟨?_, ?_, ?_⟩
  · rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    refine ⟨⟨base_disj G U X R, ?_⟩, ?_, hdis⟩
    · rw [Finset.disjoint_left]; intro v hv hv'; exact hRX v hv (hBn hv')
    · rw [Finset.disjoint_left]; intro v hv hv'; exact (mem_sdiff.mp (mem_sdiff.mp hv').1).2 (hRn hv)
  · intro a ha b hbb hab
    rcases mem_union.mp ha with ha | ha
    · rcases mem_union.mp hbb with hbb | hbb
      · exact hb.ind a ha b hbb hab
      · exact hindn b hbb a (mem_union_left _ ha) hab.symm
    · exact hindn a ha b hbb hab
  · apply conn_cover (U \ X) (Rn ∪ Bn) _ _ (fun a ha b hb' =>
      (hb.conn a ha b hb').mono (bip_mono G subset_union_left subset_union_left)) _ hatt
    intro v
    have := hmem v
    simp only [mem_union] at this ⊢
    tauto

theorem good_place (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U) (X R : Finset V) (hb : Base G U X R)
    (Rn Bn : Finset V) (hRn : Rn ⊆ X) (hBn : Bn ⊆ X) (hcov : ∀ v ∈ X, v ∈ Rn ∨ v ∈ Bn)
    (hdis : Disjoint Rn Bn) (hindn : ∀ a ∈ Rn, ∀ b ∈ R ∪ Rn, ¬ G.Adj a b)
    (hatt : ∀ t ∈ Rn ∪ Bn, ∃ s ∈ U \ X,
      (bip G (R ∪ Rn) (((U \ X) \ R) ∪ Bn)).Reachable t s)
    (heven : Even (((U \ X) \ R) ∪ Bn).card) : ∃ w, VC G w := by
  obtain ⟨h1, h2, h3⟩ := place_common G U hsupp X R hb Rn Bn hRn hBn hdis hindn hatt
  refine basic_vc G _ _ ⟨h1, h2, h3, heven, ?_⟩
  intro a b hab
  have haU := hsupp a b hab
  by_cases haX : a ∈ X
  · rcases hcov a haX with h | h
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ (mem_union_right _ h)
  · have := (base_mem G U X R hb a).mpr (mem_sdiff.mpr ⟨haU, haX⟩)
    simp only [mem_union] at this ⊢; tauto

theorem rem_place (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U) (X R : Finset V) (hb : Base G U X R) (v0 : V)
    (hv0 : v0 ∈ X) (Rn Bn : Finset V) (hRn : Rn ⊆ X.erase v0) (hBn : Bn ⊆ X.erase v0)
    (hcov : ∀ v ∈ X.erase v0, v ∈ Rn ∨ v ∈ Bn)
    (hdis : Disjoint Rn Bn) (hindn : ∀ a ∈ Rn, ∀ b ∈ R ∪ Rn, ¬ G.Adj a b)
    (hatt : ∀ t ∈ Rn ∪ Bn, ∃ s ∈ U \ X,
      (bip G (R ∪ Rn) (((U \ X) \ R) ∪ Bn)).Reachable t s)
    (heven : Even (((U \ X) \ R) ∪ Bn).card)
    (hk : 2 ≤ (univ.filter (fun u => G.Adj v0 u ∧ u ∈ R ∪ Rn)).card)
    (hpar : Even (univ.filter (fun u => G.Adj v0 u ∧ u ∈ R ∪ Rn)).card ∨
      1 ≤ (univ.filter (fun u => G.Adj v0 u ∧ u ∈ ((U \ X) \ R) ∪ Bn)).card) :
    ∃ w, VC G w := by
  obtain ⟨h1, h2, h3⟩ := place_common G U hsupp X R hb Rn Bn
    (hRn.trans (erase_subset _ _)) (hBn.trans (erase_subset _ _)) hdis hindn hatt
  have hv0n : v0 ∉ (R ∪ Rn) ∪ (((U \ X) \ R) ∪ Bn) := by
    simp only [mem_union, not_or]
    refine ⟨⟨fun h => (mem_sdiff.mp (hb.RU h)).2 hv0, fun h => by
        have := hRn h; simp at this⟩, fun h => (mem_sdiff.mp (mem_sdiff.mp h).1).2 hv0,
        fun h => by have := hBn h; simp at this⟩
  refine remaining G v0 _ _ h1 hv0n h2 h3 heven ?_ hk hpar
  intro a b hab hav
  have haU := hsupp a b hab
  by_cases haX : a ∈ X
  · rcases hcov a (mem_erase.mpr ⟨hav, haX⟩) with h | h
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ (mem_union_right _ h)
  · have := (base_mem G U X R hb a).mpr (mem_sdiff.mpr ⟨haU, haX⟩)
    simp only [mem_union] at this ⊢; tauto

theorem rearr_place (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U) (X R : Finset V) (hb : Base G U X R) (v0 : V)
    (hv0 : v0 ∈ X) (Rn Bn : Finset V) (hRn : Rn ⊆ X.erase v0) (hBn : Bn ⊆ X.erase v0)
    (hcov : ∀ v ∈ X.erase v0, v ∈ Rn ∨ v ∈ Bn)
    (hdis : Disjoint Rn Bn) (hindn : ∀ a ∈ Rn, ∀ b ∈ R ∪ Rn, ¬ G.Adj a b)
    (hatt : ∀ t ∈ Rn ∪ Bn, ∃ s ∈ U \ X,
      (bip G (R ∪ Rn) (((U \ X) \ R) ∪ Bn)).Reachable t s)
    (heven : Even (((U \ X) \ R) ∪ Bn).card) (u0 : V) (hu0 : u0 ∈ R ∪ Rn)
    (hN0 : ∀ r ∈ R ∪ Rn, G.Adj v0 r ↔ r = u0)
    (a b : V) (ha : a ∈ ((U \ X) \ R) ∪ Bn) (hb' : b ∈ ((U \ X) \ R) ∪ Bn) (hab : a ≠ b)
    (hva : G.Adj v0 a) (hvb : G.Adj v0 b)
    (hreach : (delv (bip G (R ∪ Rn) (((U \ X) \ R) ∪ Bn)) {u0}).Reachable a b) :
    ∃ w, VC G w := by
  obtain ⟨h1, h2, h3⟩ := place_common G U hsupp X R hb Rn Bn
    (hRn.trans (erase_subset _ _)) (hBn.trans (erase_subset _ _)) hdis hindn hatt
  have hv0n : v0 ∉ (R ∪ Rn) ∪ (((U \ X) \ R) ∪ Bn) := by
    simp only [mem_union, not_or]
    refine ⟨⟨fun h => (mem_sdiff.mp (hb.RU h)).2 hv0, fun h => by
        have := hRn h; simp at this⟩, fun h => (mem_sdiff.mp (mem_sdiff.mp h).1).2 hv0,
        fun h => by have := hBn h; simp at this⟩
  refine rearr G v0 u0 _ _ h1 hv0n h2 h3 heven ?_ hu0 hN0 a b ha hb' hab hva hvb hreach
  intro a b hab hav
  have haU := hsupp a b hab
  by_cases haX : a ∈ X
  · rcases hcov a (mem_erase.mpr ⟨hav, haX⟩) with h | h
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ (mem_union_right _ h)
  · have := (base_mem G U X R hb a).mpr (mem_sdiff.mpr ⟨haU, haX⟩)
    simp only [mem_union] at this ⊢; tauto

end Place
section GadgetE
variable {V : Type} [Fintype V] [DecidableEq V]
open SimpleGraph

/-- delete two edges -/
def del2 (G : SimpleGraph V) (e1 e2 : Sym2 V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ s(a, b) ≠ e1 ∧ s(a, b) ≠ e2
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2.1,
    by rw [Sym2.eq_swap]; exact h.2.2⟩⟩
  loopless := ⟨fun a h => G.ne_of_adj h.1 rfl⟩

@[simp] lemma del2_adj (G : SimpleGraph V) (e1 e2 : Sym2 V) (a b : V) :
    (del2 G e1 e2).Adj a b ↔ G.Adj a b ∧ s(a, b) ≠ e1 ∧ s(a, b) ≠ e2 := Iff.rfl

instance del2_dec (G : SimpleGraph V) [DecidableRel G.Adj] (e1 e2 : Sym2 V) :
    DecidableRel (del2 G e1 e2).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj a b ∧ s(a, b) ≠ e1 ∧ s(a, b) ≠ e2))

lemma vc_of_split (G : SimpleGraph V) [DecidableRel G.Adj] (R B : Finset V)
    (hind : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b) (hsupp : ∀ a b, G.Adj a b → a ∈ R ∪ B)
    (w : Sym2 V → ℤ) (hw : ∀ u v, G.Adj u v → 1 ≤ w s(u, v) ∧ w s(u, v) ≤ 3)
    (hB : ∀ v ∈ B, Odd (sd G w v)) (hR : ∀ v ∈ R, Even (sd G w v))
    (hBB : ∀ u ∈ B, ∀ v ∈ B, G.Adj u v → sd G w u ≠ sd G w v) : VC G w := by
  refine ⟨hw, fun a b hab => ?_⟩
  have haRB := hsupp a b hab
  have hbRB := hsupp b a hab.symm
  simp only [mem_union] at haRB hbRB
  rcases haRB with haR | haB <;> rcases hbRB with hbR | hbB
  · exact absurd hab (hind a haR b hbR)
  · intro heq
    have := hR a haR; rw [heq] at this
    exact (Int.not_even_iff_odd.mpr (hB b hbB)) this
  · intro heq
    have := hR b hbR; rw [← heq] at this
    exact (Int.not_even_iff_odd.mpr (hB a haB)) this
  · exact hBB a haB b hbB hab

lemma s2ne_l {a u v : V} (huv : u ≠ v) (hav : a ≠ v) : s(a, u) ≠ s(a, v) := by
  intro h; rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h1, _⟩
  · exact huv h
  · exact hav h1

/-- the gadget for a common red neighbour `q` of `x` and `y` -/
theorem gadgetE (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U) (x y q : V) (hxy : G.Adj x y)
    (R : Finset V) (hb : Base G U {x, y} R) (hqR : q ∈ R)
    (hNRx : ∀ r ∈ R, G.Adj x r ↔ r = q) (hNRy : ∀ r ∈ R, G.Adj y r ↔ r = q)
    (hz : ∃ z, G.Adj x z ∧ z ≠ y ∧ z ≠ q) (hBo : Odd ((U \ {x, y}) \ R).card) :
    ∃ w, VC G w := by
  set B := (U \ {x, y}) \ R with hBdef
  have hxyne : x ≠ y := G.ne_of_adj hxy
  have hmem := base_mem G U {x, y} R hb
  have hRxy : ∀ v ∈ R, v ≠ x ∧ v ≠ y := by
    intro v hv; have := hb.RU hv; simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at this
    exact this.2
  have hBxy : ∀ v ∈ B, v ≠ x ∧ v ≠ y := by
    intro v hv; simp only [hBdef, mem_sdiff, mem_insert, mem_singleton, not_or] at hv
    exact hv.1.2
  have hBR : ∀ v ∈ B, v ∉ R := fun v hv => (mem_sdiff.mp hv).2
  have hxq : G.Adj x q := (hNRx q hqR).mpr rfl
  have hyq : G.Adj y q := (hNRy q hqR).mpr rfl
  have hqx : q ≠ x := (hRxy q hqR).1
  have hqy : q ≠ y := (hRxy q hqR).2
  have hxR : x ∉ R := fun h => (hRxy x h).1 rfl
  have hyR : y ∉ R := fun h => (hRxy y h).2 rfl
  have hxB : x ∉ B := fun h => (hBxy x h).1 rfl
  have hyB : y ∉ B := fun h => (hBxy y h).2 rfl
  let Ge := del2 G s(x, y) s(x, q)
  let R1 := R ∪ {x}
  let B1 := B ∪ {y}
  let o : V → ℤ := fun v => if v = y then 2 else 0
  have hUxy : ∀ v, v ∈ U \ {x, y} ↔ v ∈ R ∨ v ∈ B := by
    intro v; rw [← hmem v, mem_union]
  have hGe_of : ∀ a b, G.Adj a b → a ≠ x → b ≠ x → Ge.Adj a b := by
    intro a b hab ha hb'
    exact ⟨hab, (s2ne (Ne.symm ha) (Ne.symm hb')).symm, (s2ne (Ne.symm ha) (Ne.symm hb')).symm⟩
  have hg : Good Ge R1 B1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
      refine ⟨⟨base_disj G U {x, y} R, ?_⟩, ?_, ?_⟩
      · exact disjoint_singleton_right.mpr hyR
      · exact disjoint_singleton_left.mpr hxB
      · exact disjoint_singleton.mpr hxyne
    · intro a ha b hb' hab
      simp only [R1, mem_union, mem_singleton] at ha hb'
      rcases ha with ha | rfl <;> rcases hb' with hb' | rfl
      · exact hb.ind a ha b hb' hab.1
      · have := (hNRx a ha).mp hab.1.symm; subst this
        exact hab.2.2 (Sym2.eq_swap)
      · have := (hNRx b hb').mp hab.1; subst this
        exact hab.2.2 rfl
      · exact G.ne_of_adj hab.1 rfl
    · obtain ⟨z, hxz, hzy, hzq⟩ := hz
      have hzU : z ∈ U \ {x, y} := by
        simp [hsupp z x hxz.symm, (G.ne_of_adj hxz).symm, hzy]
      have hzB : z ∈ B := mem_sdiff.mpr ⟨hzU, fun h => hzq ((hNRx z h).mp hxz)⟩
      apply conn_cover (U \ {x, y}) {x, y} R1 B1 _ _ _
      · intro a ha b hb'
        apply (hb.conn a ha b hb').mono
        intro u v huv
        simp only [bip_adj] at huv ⊢
        have hu : u ≠ x := by
          rcases huv.2 with ⟨h, _⟩ | ⟨h, _⟩
          · exact (hRxy u h).1
          · exact (hBxy u h).1
        have hv : v ≠ x := by
          rcases huv.2 with ⟨_, h⟩ | ⟨_, h⟩
          · exact (hBxy v h).1
          · exact (hRxy v h).1
        refine ⟨hGe_of u v huv.1 hu hv, ?_⟩
        rcases huv.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨mem_union_left _ h1, mem_union_left _ h2⟩
        · exact Or.inr ⟨mem_union_left _ h1, mem_union_left _ h2⟩
      · intro v
        have := hUxy v
        simp only [R1, B1, mem_union, mem_insert, mem_singleton] at this ⊢
        constructor
        · rintro ((h | h) | (h | h))
          · exact Or.inl (this.mpr (Or.inl h))
          · exact Or.inr (Or.inl h)
          · exact Or.inl (this.mpr (Or.inr h))
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · rcases this.mp h with h' | h'
            · exact Or.inl (Or.inl h')
            · exact Or.inr (Or.inl h')
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inr h)
      · intro t ht
        simp only [mem_insert, mem_singleton] at ht
        rcases ht with rfl | rfl
        · refine ⟨z, hzU, Adj.reachable ?_⟩
          simp only [bip_adj, R1, B1, mem_union, mem_singleton]
          exact ⟨⟨hxz, s2ne' (G.ne_of_adj hxz).symm hzy, s2ne' (G.ne_of_adj hxz).symm hzq⟩,
            Or.inl ⟨Or.inr trivial, Or.inl hzB⟩⟩
        · refine ⟨q, hb.RU hqR, Adj.reachable ?_⟩
          simp only [bip_adj, R1, B1, mem_union, mem_singleton]
          refine ⟨hGe_of t q hyq (Ne.symm hxyne) hqx, Or.inr ⟨Or.inr trivial, Or.inl hqR⟩⟩
    · rw [card_union_of_disjoint (disjoint_singleton_right.mpr hyB), card_singleton]
      exact hBo.add_one
    · intro a b hab
      have haU := hsupp a b hab.1
      by_cases hax : a = x
      · subst hax; simp [R1]
      by_cases hay : a = y
      · subst hay; simp [B1]
      have := (hUxy a).mp (by simp [haU, hax, hay])
      simp only [R1, B1, mem_union]; tauto
  obtain ⟨wt, hwt, hBt, hRt, hBBt⟩ := basic Ge R1 B1 hg o (fun v => by
    simp only [o]; split_ifs
    · exact ⟨1, by ring⟩
    · exact ⟨0, by ring⟩)
  have hBt' : ∀ v ∈ B1, Odd (sd Ge wt v + o v) := hBt
  set μ := wt s(y, q) with hμ
  have hGeyq : Ge.Adj y q := hGe_of y q hyq (Ne.symm hxyne) hqx
  have hμb : 1 ≤ μ ∧ μ ≤ 3 := hwt y q hGeyq
  -- choice of the three triangle weights
  obtain ⟨a1, a2, a3, h1, h2, h3, hy2, hq2, hxq'⟩ : ∃ a1 a2 a3 : ℤ, (1 ≤ a1 ∧ a1 ≤ 3) ∧
      (1 ≤ a2 ∧ a2 ≤ 3) ∧ (1 ≤ a3 ∧ a3 ≤ 3) ∧ a1 + a3 - μ = 2 ∧ a2 + a3 - μ = 2 ∧
      sd Ge wt x + a1 + a2 ≠ sd Ge wt q + 2 := by
    by_cases hc : sd Ge wt x + 4 = sd Ge wt q + 2
    · by_cases hm : μ = 2
      · exact ⟨1, 1, 3, by omega, by omega, by omega, by omega, by omega, by omega⟩
      · exact ⟨μ, μ, 2, hμb, hμb, by omega, by omega, by omega, by omega⟩
    · exact ⟨2, 2, μ, by omega, by omega, hμb, by omega, by omega, by omega⟩
  let W : Sym2 V → ℤ := fun e => if e = s(x, y) then a1 else if e = s(x, q) then a2 else
    if e = s(y, q) then a3 else wt e
  have hxqy : s(x, q) ≠ s(x, y) := s2ne' hqx hqy
  have hyqxy : s(y, q) ≠ s(x, y) := s2ne' hqx hqy
  have hyqxq : s(y, q) ≠ s(x, q) := s2ne (Ne.symm hxyne) (Ne.symm hqy)
  have W1 : W s(x, y) = a1 := by simp [W]
  have W2 : W s(x, q) = a2 := by simp only [W, hxqy, if_false, if_true]
  have W3 : W s(y, q) = a3 := by simp only [W, hyqxy, hyqxq, if_false, if_true]
  have W1' : W s(y, x) = a1 := by rw [Sym2.eq_swap]; exact W1
  have W2' : W s(q, x) = a2 := by rw [Sym2.eq_swap]; exact W2
  have W3' : W s(q, y) = a3 := by rw [Sym2.eq_swap]; exact W3
  have hμ' : wt s(q, y) = μ := by rw [hμ, Sym2.eq_swap]
  have Wo : ∀ e, e ≠ s(x, y) → e ≠ s(x, q) → e ≠ s(y, q) → W e = wt e := by
    intro e h1 h2 h3; simp only [W, h1, h2, h3, if_false]
  -- the vertices away from the triangle
  have hfar : ∀ v, v ≠ x → v ≠ y → v ≠ q → sd G W v = sd Ge wt v := by
    intro v hvx hvy hvq
    have := sd_nbr_congr Ge G wt W v ∅ (fun u _ => ?_)
    · simpa using this
    have e1 : s(v, u) ≠ s(x, y) := s2ne hvx hvy
    have e2 : s(v, u) ≠ s(x, q) := s2ne hvx hvq
    have e3 : s(v, u) ≠ s(y, q) := s2ne hvy hvq
    have hiff : Ge.Adj v u ↔ G.Adj v u := ⟨fun h => h.1, fun h => ⟨h, e1, e2⟩⟩
    by_cases h : G.Adj v u
    · rw [if_pos (hiff.mpr h), if_pos h, Wo _ e1 e2 e3]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  have hsdx : sd G W x = sd Ge wt x + (a1 + a2) := by
    rw [sd_nbr_congr Ge G wt W x {y, q} (fun u hu => ?_), sum_pair (Ne.symm hqy)]
    · have n1 : ¬ Ge.Adj x y := fun h => h.2.1 rfl
      have n2 : ¬ Ge.Adj x q := fun h => h.2.2 rfl
      rw [if_pos hxy, if_neg n1, if_pos hxq, if_neg n2, W1, W2]; ring
    · simp only [mem_insert, mem_singleton, not_or] at hu
      have e1 : s(x, u) ≠ s(x, y) := s2ne_l hu.1 hxyne
      have e2 : s(x, u) ≠ s(x, q) := s2ne_l hu.2 (Ne.symm hqx)
      have e3 : s(x, u) ≠ s(y, q) := s2ne hxyne (Ne.symm hqx)
      have hiff : Ge.Adj x u ↔ G.Adj x u := ⟨fun h => h.1, fun h => ⟨h, e1, e2⟩⟩
      by_cases h : G.Adj x u
      · rw [if_pos (hiff.mpr h), if_pos h, Wo _ e1 e2 e3]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  have hsdy : sd G W y = sd Ge wt y + (a1 + a3 - μ) := by
    rw [sd_nbr_congr Ge G wt W y {x, q} (fun u hu => ?_), sum_pair (Ne.symm hqx)]
    · have n1 : ¬ Ge.Adj y x := fun h => h.2.1 Sym2.eq_swap
      rw [if_pos hxy.symm, if_neg n1, if_pos hyq, if_pos hGeyq, W1', W3]; ring
    · simp only [mem_insert, mem_singleton, not_or] at hu
      have e1 : s(y, u) ≠ s(x, y) := by rw [Sym2.eq_swap (a := x)]; exact s2ne_l hu.1 (Ne.symm hxyne)
      have e2 : s(y, u) ≠ s(x, q) := s2ne (Ne.symm hxyne) (Ne.symm hqy)
      have e3 : s(y, u) ≠ s(y, q) := s2ne_l hu.2 (Ne.symm hqy)
      have hiff : Ge.Adj y u ↔ G.Adj y u := ⟨fun h => h.1, fun h => ⟨h, e1, e2⟩⟩
      by_cases h : G.Adj y u
      · rw [if_pos (hiff.mpr h), if_pos h, Wo _ e1 e2 e3]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  have hsdq : sd G W q = sd Ge wt q + (a2 + a3 - μ) := by
    rw [sd_nbr_congr Ge G wt W q {x, y} (fun u hu => ?_), sum_pair hxyne]
    · have n1 : ¬ Ge.Adj q x := fun h => h.2.2 Sym2.eq_swap
      have hGeqy : Ge.Adj q y := hGeyq.symm
      rw [if_pos hxq.symm, if_neg n1, if_pos hyq.symm, if_pos hGeqy, W2', W3', hμ']; ring
    · simp only [mem_insert, mem_singleton, not_or] at hu
      have e1 : s(q, u) ≠ s(x, y) := s2ne hqx hqy
      have e2 : s(q, u) ≠ s(x, q) := by rw [Sym2.eq_swap (a := x)]; exact s2ne_l hu.1 hqx
      have e3 : s(q, u) ≠ s(y, q) := by rw [Sym2.eq_swap (a := y)]; exact s2ne_l hu.2 hqy
      have hiff : Ge.Adj q u ↔ G.Adj q u := ⟨fun h => h.1, fun h => ⟨h, e1, e2⟩⟩
      by_cases h : G.Adj q u
      · rw [if_pos (hiff.mpr h), if_pos h, Wo _ e1 e2 e3]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  have hBsd : ∀ v ∈ B ∪ {y}, sd G W v = sd Ge wt v + o v := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · have hvq : v ≠ q := fun h => hBR v hv (h ▸ hqR)
      rw [hfar v (hBxy v hv).1 (hBxy v hv).2 hvq]; simp [o, (hBxy v hv).2]
    · rw [mem_singleton] at hv; subst hv; rw [hsdy, hy2]; simp [o]
  refine ⟨W, vc_of_parity G R (B ∪ {y}) (disjoint_union_right.mpr ⟨base_disj G U {x, y} R,
    disjoint_singleton_right.mpr hyR⟩) hb.ind x ?_ W ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro a b hab hax
    have haU := hsupp a b hab
    by_cases hay : a = y
    · subst hay; simp
    · have := (hUxy a).mp (by simp [haU, hax, hay])
      simp only [mem_union, mem_singleton]; tauto
  · intro a b hab
    by_cases e1 : s(a, b) = s(x, y)
    · rw [e1, W1]; exact h1
    by_cases e2 : s(a, b) = s(x, q)
    · rw [e2, W2]; exact h2
    by_cases e3 : s(a, b) = s(y, q)
    · rw [e3, W3]; exact h3
    rw [Wo _ e1 e2 e3]; exact hwt a b ⟨hab, e1, e2⟩
  · intro v hv
    rw [hBsd v hv]; exact hBt' v (by simpa [B1] using hv)
  · intro v hv
    by_cases hvq : v = q
    · subst hvq; rw [hsdq, hq2]
      obtain ⟨r, hr⟩ := hRt v (mem_union_left _ hv); exact ⟨r + 1, by omega⟩
    · rw [hfar v (hRxy v hv).1 (hRxy v hv).2 hvq]; exact hRt v (mem_union_left _ hv)
  · rw [hsdx]
    obtain ⟨r, hr⟩ := hRt x (mem_union_right _ (mem_singleton_self _))
    exact ⟨r + (a1 + a2) / 2, by omega⟩
  · intro u hu v hv huv
    rw [hBsd u hu, hBsd v hv]
    have hux : u ≠ x := by
      rcases mem_union.mp hu with h | h
      · exact (hBxy u h).1
      · rw [mem_singleton] at h; rw [h]; exact Ne.symm hxyne
    have hvx : v ≠ x := by
      rcases mem_union.mp hv with h | h
      · exact (hBxy v h).1
      · rw [mem_singleton] at h; rw [h]; exact Ne.symm hxyne
    exact hBBt u (by simpa [B1] using hu) v (by simpa [B1] using hv) (hGe_of u v huv hux hvx)
  · intro r hr hxr
    have := (hNRx r hr).mp hxr; subst this
    rw [hsdx, hsdq, hq2]
    intro h; apply hxq'; linarith

end GadgetE
section CaseB1
variable {V : Type} [Fintype V] [DecidableEq V]
open SimpleGraph

/-- the gadget case of B1: `|B|` odd and both outer neighbours red -/
theorem caseB1_gadget (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U) (x y zx zy : V) (hxU : x ∈ U) (hyU : y ∈ U)
    (hNx : ∀ u, G.Adj x u ↔ u = y ∨ u = zx) (hNy : ∀ u, G.Adj y u ↔ u = x ∨ u = zy)
    (hzxy : zx ≠ y) (hzyx : zy ≠ x) (R : Finset V) (hb : Base G U {x, y} R)
    (hzxR : zx ∈ R) (hzyR : zy ∈ R) (hBo : Odd ((U \ {x, y}) \ R).card) : ∃ w, VC G w := by
  set B := (U \ {x, y}) \ R with hBdef
  have hxy : G.Adj x y := (hNx y).mpr (Or.inl rfl)
  have hxyne : x ≠ y := G.ne_of_adj hxy
  have hxzx : x ≠ zx := G.ne_of_adj ((hNx zx).mpr (Or.inr rfl))
  have hyzy : y ≠ zy := G.ne_of_adj ((hNy zy).mpr (Or.inr rfl))
  have hmem := base_mem G U {x, y} R hb
  have hRxy : ∀ v ∈ R, v ≠ x ∧ v ≠ y := by
    intro v hv; have := hb.RU hv; simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at this
    exact this.2
  have hBxy : ∀ v ∈ B, v ≠ x ∧ v ≠ y := by
    intro v hv; simp only [hBdef, mem_sdiff, mem_insert, mem_singleton, not_or] at hv
    exact hv.1.2
  have hBR : ∀ v ∈ B, v ∉ R := fun v hv => (mem_sdiff.mp hv).2
  have hxR : x ∉ R := fun h => (hRxy x h).1 rfl
  have hyR : y ∉ R := fun h => (hRxy y h).2 rfl
  have hxB : x ∉ B := fun h => (hBxy x h).1 rfl
  have hyB : y ∉ B := fun h => (hBxy y h).2 rfl
  -- the auxiliary graph: delete y
  let Gt := delv G {y}
  let B1 := insert x B
  have hg : Good Gt R B1 := by
    refine ⟨disjoint_insert_right.mpr ⟨hxR, base_disj G U {x, y} R⟩,
      fun a ha b hbb h => hb.ind a ha b hbb h.1, ?_, ?_, ?_⟩
    · apply conn_cover (U \ {x, y}) {x} R B1 _ _ _
      · intro a ha b hbb
        apply (hb.conn a ha b hbb).mono
        intro u v huv
        simp only [bip_adj, delv_adj, Gt, B1] at huv ⊢
        have hu : u ≠ y := by
          rcases huv.2 with ⟨h, _⟩ | ⟨h, _⟩
          · exact (hRxy u h).2
          · exact (hBxy u h).2
        have hv : v ≠ y := by
          rcases huv.2 with ⟨_, h⟩ | ⟨_, h⟩
          · exact (hBxy v h).2
          · exact (hRxy v h).2
        refine ⟨⟨huv.1, by simpa using hu, by simpa using hv⟩, ?_⟩
        rcases huv.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, mem_insert_of_mem h2⟩
        · exact Or.inr ⟨mem_insert_of_mem h1, h2⟩
      · intro v
        have := hmem v
        simp only [B1, mem_union, mem_insert, mem_singleton] at this ⊢
        tauto
      · intro t ht
        rw [mem_singleton] at ht; subst ht
        refine ⟨zx, hb.RU hzxR, Adj.reachable ?_⟩
        simp only [bip_adj, delv_adj, Gt, B1, mem_singleton]
        exact ⟨⟨(hNx zx).mpr (Or.inr rfl), hxyne, hzxy⟩, Or.inr ⟨mem_insert_self _ _, hzxR⟩⟩
    · rw [card_insert_of_notMem hxB]; exact hBo.add_one
    · intro a b hab
      have hay : a ≠ y := by simpa using hab.2.1
      by_cases hax : a = x
      · subst hax; exact mem_union_right _ (mem_insert_self _ _)
      · have := (hmem a).mpr (by simp [hsupp a b hab.1, hax, hay])
        simp only [B1, mem_union, mem_insert] at this ⊢; tauto
  obtain ⟨wt, hwt, hBt, hRt, hBBt⟩ := basic Gt R B1 hg (fun _ => 0) (fun _ => ⟨0, by ring⟩)
  simp only [add_zero] at hBt hBBt
  -- the weight on x z_x in the auxiliary graph is odd
  have hNxt : univ.filter (Gt.Adj x) = {zx} := by
    ext u; simp only [mem_filter, mem_univ, true_and, mem_singleton, Gt, delv_adj, hNx]
    constructor
    · rintro ⟨h1 | h1, -, h3⟩
      · exact absurd h1 (by simpa using h3)
      · exact h1
    · rintro rfl; exact ⟨Or.inr rfl, by simpa using hxyne, by simpa using hzxy⟩
  have hodd : Odd (wt s(x, zx)) := by
    have := hBt x (mem_insert_self _ _)
    simp only [sd, hNxt, sum_singleton] at this; exact this
  -- the final weighting
  let sdzx : ℤ := sd Gt wt zx - wt s(x, zx) + 1 + (if zx = zy then 2 else 0)
  let t : ℤ := if sdzx = 2 then 3 else 1
  let ω : Sym2 V → ℤ := fun e => if e = s(x, zx) then 1 else if e = s(x, y) then t else
    if e = s(y, zy) then 2 else wt e
  have e1 : ω s(x, zx) = 1 := by simp [ω]
  have e2 : ω s(x, y) = t := by
    have h1 : s(x, y) ≠ s(x, zx) := s2ne' hxyne.symm hzxy.symm
    simp only [ω, h1, if_false, if_true]
  have e2' : ω s(y, x) = t := by rw [Sym2.eq_swap]; exact e2
  have e3 : ω s(y, zy) = 2 := by
    have h1 : s(y, zy) ≠ s(x, zx) := s2ne hxyne.symm hzxy.symm
    have h2 : s(y, zy) ≠ s(x, y) := s2ne' hzyx (Ne.symm hyzy)
    simp only [ω, h1, h2, if_false, if_true]
  have e4 : ∀ a b, a ≠ x → a ≠ y → b ≠ x → b ≠ y → ω s(a, b) = wt s(a, b) := by
    intro a b ha hb' hbx hby
    have h1 : s(a, b) ≠ s(x, zx) := (s2ne (Ne.symm ha) (Ne.symm hbx)).symm
    have h2 : s(a, b) ≠ s(x, y) := (s2ne (Ne.symm ha) (Ne.symm hbx)).symm
    have h3 : s(a, b) ≠ s(y, zy) := (s2ne (Ne.symm hb') (Ne.symm hby)).symm
    simp only [ω, h1, h2, h3, if_false]
  have ht : t = 1 ∨ t = 3 := by simp only [t]; split_ifs <;> simp
  have hNx' : univ.filter (G.Adj x) = {y, zx} := filter_adj_pair G x y zx hNx
  have hNy' : univ.filter (G.Adj y) = {x, zy} := filter_adj_pair G y x zy hNy
  have hsdx : sd G ω x = t + 1 := by
    simp only [sd, hNx']; rw [sum_pair hzxy.symm, e2, e1]
  have hsdy : sd G ω y = t + 2 := by
    simp only [sd, hNy']; rw [sum_pair hzyx.symm, e2', e3]
  have hsdB : ∀ v ∈ B, sd G ω v = sd Gt wt v := by
    intro v hv
    have hvx := (hBxy v hv).1
    have hvy := (hBxy v hv).2
    have := sd_nbr_congr Gt G wt ω v ∅ (fun u _ => ?_)
    · simpa using this
    by_cases huy : u = y
    · subst huy
      have h1 : ¬ G.Adj v u := by
        intro h; rcases (hNy v).mp h.symm with h | h
        · exact hvx h
        · exact hBR v hv (h ▸ hzyR)
      have h2 : ¬ Gt.Adj v u := fun h => h1 h.1
      simp [h1, h2]
    by_cases hux : u = x
    · subst hux
      have h1 : ¬ G.Adj v u := by
        intro h; rcases (hNx v).mp h.symm with h | h
        · exact hvy h
        · exact hBR v hv (h ▸ hzxR)
      have h2 : ¬ Gt.Adj v u := fun h => h1 h.1
      simp [h1, h2]
    have hiff : Gt.Adj v u ↔ G.Adj v u := by
      simp only [Gt, delv_adj, mem_singleton]; exact ⟨fun h => h.1, fun h => ⟨h, hvy, huy⟩⟩
    by_cases hvu : G.Adj v u
    · rw [if_pos (hiff.mpr hvu), if_pos hvu, e4 v u hvx hvy hux huy]
    · rw [if_neg (fun h => hvu (hiff.mp h)), if_neg hvu]
  have hsdR : ∀ v ∈ R, sd G ω v = sd Gt wt v + ((if v = zx then 1 - wt s(x, zx) else 0) +
      (if v = zy then 2 else 0)) := by
    intro v hv
    have hvx := (hRxy v hv).1
    have hvy := (hRxy v hv).2
    rw [sd_nbr_congr Gt G wt ω v {x, y} (fun u hu => ?_), sum_pair hxyne]
    · congr 1
      congr 1
      · have hiff : Gt.Adj v x ↔ G.Adj v x := by
          simp only [Gt, delv_adj, mem_singleton]; exact ⟨fun h => h.1, fun h => ⟨h, hvy, hxyne⟩⟩
        by_cases hvz : v = zx
        · subst hvz
          have hadj : G.Adj v x := ((hNx v).mpr (Or.inr rfl)).symm
          rw [if_pos hadj, if_pos (hiff.mpr hadj), if_pos rfl, Sym2.eq_swap, e1]
        · have hna : ¬ G.Adj v x := by
            intro h; rcases (hNx v).mp h.symm with h | h
            · exact hvy h
            · exact hvz h
          rw [if_neg hna, if_neg (fun h => hna (hiff.mp h)), if_neg hvz]; ring
      · have hn : ¬ Gt.Adj v y := fun h => by simp [Gt] at h
        rw [if_neg hn]
        by_cases hvz : v = zy
        · subst hvz
          have hadj : G.Adj v y := ((hNy v).mpr (Or.inr rfl)).symm
          rw [if_pos hadj, if_pos rfl, Sym2.eq_swap, e3]; ring
        · have hna : ¬ G.Adj v y := by
            intro h; rcases (hNy v).mp h.symm with h | h
            · exact hvx h
            · exact hvz h
          rw [if_neg hna, if_neg hvz]; ring
    · simp only [mem_insert, mem_singleton, not_or] at hu
      have hiff : Gt.Adj v u ↔ G.Adj v u := by
        simp only [Gt, delv_adj, mem_singleton]; exact ⟨fun h => h.1, fun h => ⟨h, hvy, hu.2⟩⟩
      by_cases hvu : G.Adj v u
      · rw [if_pos (hiff.mpr hvu), if_pos hvu, e4 v u hvx hvy hu.1 hu.2]
      · rw [if_neg (fun h => hvu (hiff.mp h)), if_neg hvu]
  have hsdzx : sd G ω zx = sdzx := by
    rw [hsdR zx hzxR]; simp only [sdzx, if_true]; ring
  have hyBR : y ∉ R := hyR
  refine ⟨ω, vc_of_parity G R (insert y B) (disjoint_insert_right.mpr ⟨hyBR,
    base_disj G U {x, y} R⟩) hb.ind x ?_ ω ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro a b hab hax
    by_cases hay : a = y
    · subst hay; exact mem_union_right _ (mem_insert_self _ _)
    · have := (hmem a).mpr (by simp [hsupp a b hab, hax, hay])
      simp only [mem_union, mem_insert] at this ⊢; tauto
  · intro a b hab
    by_cases h1 : s(a, b) = s(x, zx)
    · rw [h1, e1]; omega
    by_cases h2 : s(a, b) = s(x, y)
    · rw [h2, e2]; omega
    by_cases h3 : s(a, b) = s(y, zy)
    · rw [h3, e3]; omega
    have hay : a ≠ y := by
      rintro rfl
      rcases (hNy b).mp hab with h | h
      · exact h2 (by rw [h]; exact Sym2.eq_swap)
      · exact h3 (by rw [h])
    have hby : b ≠ y := by
      rintro rfl
      rcases (hNy a).mp hab.symm with h | h
      · exact h2 (by rw [h])
      · exact h3 (by rw [h]; exact Sym2.eq_swap)
    have hv : ω s(a, b) = wt s(a, b) := by simp only [ω, h1, h2, h3, if_false]
    rw [hv]
    exact hwt a b ⟨hab, by simpa using hay, by simpa using hby⟩
  · intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · rw [hsdy]; rcases ht with h | h <;> rw [h] <;> decide
    · rw [hsdB v hv]; exact hBt v (mem_insert_of_mem hv)
  · intro v hv
    rw [hsdR v hv]
    obtain ⟨r1, hr1⟩ := hRt v hv
    obtain ⟨k, hk⟩ := hodd
    refine ⟨r1 + (if v = zx then -k else 0) + (if v = zy then 1 else 0), ?_⟩
    split_ifs <;> omega
  · rw [hsdx]; rcases ht with h | h <;> rw [h] <;> decide
  · intro u hu v hv huv
    have hyn : ∀ w ∈ insert y B, G.Adj y w → False := by
      intro w hw h
      rcases (hNy w).mp h with h | h
      · rcases mem_insert.mp hw with h' | h'
        · exact hxyne (h ▸ h')
        · exact hxB (h ▸ h')
      · rcases mem_insert.mp hw with h' | h'
        · exact hyzy (h'.symm.trans h)
        · exact hBR w h' (h ▸ hzyR)
    rcases mem_insert.mp hu with rfl | hu'
    · exact absurd huv (fun h => hyn v hv h)
    rcases mem_insert.mp hv with rfl | hv'
    · exact absurd huv.symm (fun h => hyn u hu h)
    rw [hsdB u hu', hsdB v hv']
    exact hBBt u (mem_insert_of_mem hu') v (mem_insert_of_mem hv')
      ⟨huv, by simpa using (hBxy u hu').2, by simpa using (hBxy v hv').2⟩
  · intro r hr hxr
    have hrz : r = zx := by
      rcases (hNx r).mp hxr with h | h
      · exact absurd h (hRxy r hr).2
      · exact h
    subst hrz
    rw [hsdx, hsdzx]
    simp only [t]
    split_ifs with h <;> omega

/-- Case B1: both ends of the removable edge have degree two. -/
theorem caseB1 (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U) (x y zx zy : V) (hxU : x ∈ U) (hyU : y ∈ U)
    (hNx : ∀ u, G.Adj x u ↔ u = y ∨ u = zx) (hNy : ∀ u, G.Adj y u ↔ u = x ∨ u = zy)
    (hzxy : zx ≠ y) (hzyx : zy ≠ x)
    (hconn : ∀ a ∈ U \ {x, y}, ∀ b ∈ U \ {x, y}, (delv G {x, y}).Reachable a b) :
    ∃ w, VC G w := by
  have hxy : G.Adj x y := (hNx y).mpr (Or.inl rfl)
  have hxyne : x ≠ y := G.ne_of_adj hxy
  have hxzx : G.Adj x zx := (hNx zx).mpr (Or.inr rfl)
  have hyzy : G.Adj y zy := (hNy zy).mpr (Or.inr rfl)
  have hzxU : zx ∈ U \ {x, y} := by
    simp [hsupp zx x hxzx.symm, (G.ne_of_adj hxzx).symm, hzxy]
  have hzyU : zy ∈ U \ {x, y} := by
    simp [hsupp zy y hyzy.symm, (G.ne_of_adj hyzy).symm, hzyx]
  obtain ⟨R, hb, hRP⟩ := base_of_divide G U {x, y} hsupp hconn {zx} {zx}
    (singleton_subset_iff.mpr hzxU) (subset_refl _) zx (mem_singleton_self zx)
    (fun a ha b hb h => by
      rw [mem_singleton] at ha hb; subst ha; subst hb; exact G.ne_of_adj h rfl)
    (fun a ha => by rw [mem_singleton] at ha; subst ha; exact Reachable.refl _)
  have hzxR : zx ∈ R := (hRP zx (mem_singleton_self zx)).mpr (mem_singleton_self zx)
  set B := (U \ {x, y}) \ R with hBdef
  have hBX : ∀ v ∈ B, v ≠ x ∧ v ≠ y := by
    intro v hv; simp only [hBdef, mem_sdiff, mem_insert, mem_singleton, not_or] at hv
    exact hv.1.2
  have hRX : ∀ v ∈ R, v ≠ x ∧ v ≠ y := by
    intro v hv; have := hb.RU hv; simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at this
    exact this.2
  have hBdisjX : Disjoint B {x, y} := by
    rw [Finset.disjoint_left]; intro v hv hv'
    simp only [mem_insert, mem_singleton] at hv'
    rcases hv' with rfl | rfl
    · exact (hBX v hv).1 rfl
    · exact (hBX v hv).2 rfl
  have hzyB : zy ∉ R → zy ∈ B := fun h => mem_sdiff.mpr ⟨hzyU, h⟩
  by_cases hBe : Even B.card
  · by_cases hzy : zy ∈ R
    · -- (i): x and y blue
      refine good_place G U hsupp {x, y} R hb ∅ {x, y} (empty_subset _) (subset_refl _)
        (fun v hv => Or.inr hv) (disjoint_empty_left _) (fun a ha => absurd ha (notMem_empty a))
        ?_ ?_
      · intro t ht
        simp only [empty_union, mem_insert, mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact ⟨zx, hzxU, Adj.reachable (by simp [hxzx, hzxR])⟩
        · exact ⟨zy, hzyU, Adj.reachable (by simp [hyzy, hzy])⟩
      · rw [card_union_of_disjoint hBdisjX, card_pair hxyne]; exact hBe.add (by decide)
    · -- (ii): y red, x the extra vertex
      have hzyB' := hzyB hzy
      have hind : ∀ a ∈ ({y} : Finset V), ∀ b ∈ R ∪ {y}, ¬ G.Adj a b := by
        intro a ha b hb' hab
        rw [mem_singleton] at ha; subst ha
        rcases (hNy b).mp hab with h | h
        · subst h; simp only [mem_union, mem_singleton] at hb'
          rcases hb' with h' | h'
          · exact (hRX b h').1 rfl
          · exact hxyne h'
        · subst h; simp only [mem_union, mem_singleton] at hb'
          rcases hb' with h' | h'
          · exact hzy h'
          · exact (G.ne_of_adj hyzy) h'.symm
      refine rem_place G U hsupp {x, y} R hb x (by simp) {y} ∅ (by simp [hxyne.symm])
        (empty_subset _) (fun v hv => by simp at hv; exact Or.inl (by simp [hv.2])) (disjoint_empty_right _)
        hind ?_ (by simpa using hBe) ?_ (Or.inl ?_)
      · intro t ht
        simp only [union_empty, mem_singleton] at ht; subst ht
        exact ⟨zy, hzyU, Adj.reachable ((bip_adj _ _ _ _ _).mpr ⟨hyzy, Or.inl
          ⟨mem_union_right _ (mem_singleton_self _), mem_union_left _ hzyB'⟩⟩)⟩
      · have : univ.filter (fun u => G.Adj x u ∧ u ∈ R ∪ {y}) = {y, zx} := by
          ext u; simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton,
            mem_insert, hNx]
          constructor
          · rintro ⟨h, -⟩; exact h
          · rintro (rfl | rfl)
            · exact ⟨Or.inl rfl, Or.inr rfl⟩
            · exact ⟨Or.inr rfl, Or.inl hzxR⟩
        rw [this, card_pair hzxy.symm]
      · have : univ.filter (fun u => G.Adj x u ∧ u ∈ R ∪ {y}) = {y, zx} := by
          ext u; simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton,
            mem_insert, hNx]
          constructor
          · rintro ⟨h, -⟩; exact h
          · rintro (rfl | rfl)
            · exact ⟨Or.inl rfl, Or.inr rfl⟩
            · exact ⟨Or.inr rfl, Or.inl hzxR⟩
        rw [this, card_pair hzxy.symm]; decide
  · have hBo : Odd B.card := Nat.not_even_iff_odd.mp hBe
    by_cases hzy : zy ∈ R
    · exact caseB1_gadget G U hsupp x y zx zy hxU hyU hNx hNy hzxy hzyx R hb hzxR hzy hBo
    · -- (iii): x blue, y red
      have hzyB' := hzyB hzy
      have hind : ∀ a ∈ ({y} : Finset V), ∀ b ∈ R ∪ {y}, ¬ G.Adj a b := by
        intro a ha b hb' hab
        rw [mem_singleton] at ha; subst ha
        rcases (hNy b).mp hab with h | h
        · subst h; simp only [mem_union, mem_singleton] at hb'
          rcases hb' with h' | h'
          · exact (hRX b h').1 rfl
          · exact hxyne h'
        · subst h; simp only [mem_union, mem_singleton] at hb'
          rcases hb' with h' | h'
          · exact hzy h'
          · exact (G.ne_of_adj hyzy) h'.symm
      refine good_place G U hsupp {x, y} R hb {y} {x} (by simp) (by simp)
        (fun v hv => by simp at hv; rcases hv with rfl | rfl <;> simp)
        (disjoint_singleton.mpr hxyne.symm) hind ?_ ?_
      · intro t ht
        simp only [mem_union, mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact ⟨zy, hzyU, Adj.reachable ((bip_adj _ _ _ _ _).mpr ⟨hyzy, Or.inl
            ⟨mem_union_right _ (mem_singleton_self _), mem_union_left _ hzyB'⟩⟩)⟩
        · exact ⟨zx, hzxU, Adj.reachable ((bip_adj _ _ _ _ _).mpr ⟨hxzx, Or.inr
            ⟨mem_union_right _ (mem_singleton_self _), mem_union_left _ hzxR⟩⟩)⟩
      · have hxB : Disjoint B {x} := by
          rw [Finset.disjoint_singleton_right]; exact fun h => (hBX x h).1 rfl
        rw [card_union_of_disjoint hxB, card_singleton]; exact hBo.add_one

end CaseB1
section GadgetL
variable {V : Type} [Fintype V] [DecidableEq V]
open SimpleGraph

/-- delete two edges and add one -/
def swapE (G : SimpleGraph V) (e1 e2 : Sym2 V) (p1 p2 : V) : SimpleGraph V where
  Adj a b := (G.Adj a b ∧ s(a, b) ≠ e1 ∧ s(a, b) ≠ e2) ∨ (s(a, b) = s(p1, p2) ∧ a ≠ b)
  symm := ⟨fun a b h => by
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, by rw [Sym2.eq_swap]; exact h2, by rw [Sym2.eq_swap]; exact h3⟩
    · exact Or.inr ⟨by rw [Sym2.eq_swap]; exact h1, Ne.symm h2⟩⟩
  loopless := ⟨fun a h => by
    rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact G.ne_of_adj h1 rfl
    · exact h2 rfl⟩

@[simp] lemma swapE_adj (G : SimpleGraph V) (e1 e2 : Sym2 V) (p1 p2 a b : V) :
    (swapE G e1 e2 p1 p2).Adj a b ↔
      (G.Adj a b ∧ s(a, b) ≠ e1 ∧ s(a, b) ≠ e2) ∨ (s(a, b) = s(p1, p2) ∧ a ≠ b) := Iff.rfl

instance swapE_dec (G : SimpleGraph V) [DecidableRel G.Adj] (e1 e2 : Sym2 V) (p1 p2 : V) :
    DecidableRel (swapE G e1 e2 p1 p2).Adj :=
  fun a b => inferInstanceAs (Decidable ((G.Adj a b ∧ s(a, b) ≠ e1 ∧ s(a, b) ≠ e2) ∨
    (s(a, b) = s(p1, p2) ∧ a ≠ b)))

lemma s2ne_r {a b c v : V} (h1 : v ≠ a) (h2 : v ≠ b) : s(a, b) ≠ s(c, v) := by
  intro h
  have : v ∈ s(a, b) := h ▸ Sym2.mem_mk_right c v
  rw [Sym2.mem_iff] at this
  rcases this with h' | h'
  · exact h1 h'
  · exact h2 h'

lemma s2ne_lft {a b c v : V} (h1 : v ≠ a) (h2 : v ≠ b) : s(a, b) ≠ s(v, c) := by
  rw [Sym2.eq_swap (a := v)]; exact s2ne_r h1 h2

/-- the gadget for `y` with only red neighbours besides `x`, and odd degree -/
theorem gadgetL (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U) (x y zy : V) (hxy : G.Adj x y)
    (R : Finset V) (hb : Base G U {x, y} R) (hzyR : zy ∈ R) (hyzy : G.Adj y zy)
    (hNRx : ∀ r ∈ R, ¬ G.Adj x r) (hNBy : ∀ b ∈ (U \ {x, y}) \ R, ¬ G.Adj y b)
    (hr0 : ∃ r0, G.Adj y r0 ∧ r0 ≠ x ∧ r0 ≠ zy) (hBe : Even ((U \ {x, y}) \ R).card) :
    ∃ w, VC G w := by
  set B := (U \ {x, y}) \ R with hBdef
  have hxyne : x ≠ y := G.ne_of_adj hxy
  have hmem := base_mem G U {x, y} R hb
  have hUxy : ∀ v, v ∈ U \ {x, y} ↔ v ∈ R ∨ v ∈ B := by
    intro v; rw [← hmem v, mem_union]
  have hRxy : ∀ v ∈ R, v ≠ x ∧ v ≠ y := by
    intro v hv; have := hb.RU hv; simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at this
    exact this.2
  have hBxy : ∀ v ∈ B, v ≠ x ∧ v ≠ y := by
    intro v hv; simp only [hBdef, mem_sdiff, mem_insert, mem_singleton, not_or] at hv
    exact hv.1.2
  have hBR : ∀ v ∈ B, v ∉ R := fun v hv => (mem_sdiff.mp hv).2
  have hxR : x ∉ R := fun h => (hRxy x h).1 rfl
  have hyR : y ∉ R := fun h => (hRxy y h).2 rfl
  have hxB : x ∉ B := fun h => (hBxy x h).1 rfl
  have hyB : y ∉ B := fun h => (hBxy y h).2 rfl
  have hzyx : zy ≠ x := (hRxy zy hzyR).1
  have hzyy : zy ≠ y := (hRxy zy hzyR).2
  have hxzy : ¬ G.Adj x zy := hNRx zy hzyR
  -- neighbours of y other than x are red
  have hyred : ∀ u, G.Adj y u → u ≠ x → u ∈ R := by
    intro u hu hux
    have huU : u ∈ U \ {x, y} := by
      simp [hsupp u y hu.symm, hux, (G.ne_of_adj hu).symm]
    rcases (hUxy u).mp huU with h | h
    · exact h
    · exact absurd hu (hNBy u h)
  let Gl := swapE G s(x, y) s(y, zy) x zy
  let B1 := B ∪ {x, y}
  have hGl_of : ∀ a b, G.Adj a b → a ≠ y → b ≠ y → Gl.Adj a b := by
    intro a b hab ha hb'
    exact Or.inl ⟨hab, s2ne_r (Ne.symm ha) (Ne.symm hb'), s2ne_lft (Ne.symm ha) (Ne.symm hb')⟩
  have hGl_le : ∀ a b, Gl.Adj a b → G.Adj a b ∨ s(a, b) = s(x, zy) := by
    intro a b h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hGlxzy : Gl.Adj x zy := Or.inr ⟨rfl, hzyx.symm⟩
  obtain ⟨r0, hyr0, hr0x, hr0zy⟩ := hr0
  have hr0R : r0 ∈ R := hyred r0 hyr0 hr0x
  have hg : Good Gl R B1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [disjoint_union_right]
      refine ⟨base_disj G U {x, y} R, ?_⟩
      rw [Finset.disjoint_left]; intro v hv hv'
      simp only [mem_insert, mem_singleton] at hv'
      rcases hv' with rfl | rfl
      · exact hxR hv
      · exact hyR hv
    · intro a ha b hb' hab
      rcases hGl_le a b hab with h | h
      · exact hb.ind a ha b hb' h
      · have : x ∈ s(a, b) := h ▸ Sym2.mem_mk_left x zy
        rw [Sym2.mem_iff] at this
        rcases this with rfl | rfl
        · exact hxR ha
        · exact hxR hb'
    · apply conn_cover (U \ {x, y}) {x, y} R B1 _ _ _
      · intro a ha b hb'
        apply (hb.conn a ha b hb').mono
        intro u v huv
        simp only [bip_adj] at huv ⊢
        have hu : u ≠ y := by
          rcases huv.2 with ⟨h, _⟩ | ⟨h, _⟩
          · exact (hRxy u h).2
          · exact (hBxy u h).2
        have hv : v ≠ y := by
          rcases huv.2 with ⟨_, h⟩ | ⟨_, h⟩
          · exact (hBxy v h).2
          · exact (hRxy v h).2
        refine ⟨hGl_of u v huv.1 hu hv, ?_⟩
        rcases huv.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, mem_union_left _ h2⟩
        · exact Or.inr ⟨mem_union_left _ h1, h2⟩
      · intro v
        have := hUxy v
        simp only [B1, mem_union, mem_insert, mem_singleton] at this ⊢
        tauto
      · intro t ht
        simp only [mem_insert, mem_singleton] at ht
        rcases ht with rfl | rfl
        · refine ⟨zy, hb.RU hzyR, Adj.reachable ?_⟩
          rw [bip_adj]
          exact ⟨hGlxzy, Or.inr ⟨by simp [B1], hzyR⟩⟩
        · refine ⟨r0, hb.RU hr0R, Adj.reachable ?_⟩
          rw [bip_adj]
          refine ⟨Or.inl ⟨hyr0, ?_, ?_⟩, Or.inr ⟨by simp [B1], hr0R⟩⟩
          · rw [Sym2.eq_swap (a := x)]; exact s2ne_l hr0x (Ne.symm hxyne)
          · exact s2ne_l hr0zy hzyy.symm
    · have hd : Disjoint B {x, y} := by
        rw [Finset.disjoint_left]; intro v hv hv'
        simp only [mem_insert, mem_singleton] at hv'
        rcases hv' with rfl | rfl
        · exact hxB hv
        · exact hyB hv
      rw [card_union_of_disjoint hd, card_pair hxyne]; exact hBe.add (by decide)
    · intro a b hab
      rcases hGl_le a b hab with h | h
      · have haU := hsupp a b h
        by_cases hax : a = x
        · subst hax; simp [B1]
        by_cases hay : a = y
        · subst hay; simp [B1]
        have := (hUxy a).mp (by simp [haU, hax, hay])
        simp only [B1, mem_union]; tauto
      · have : a ∈ s(x, zy) := h ▸ Sym2.mem_mk_left a b
        rw [Sym2.mem_iff] at this
        rcases this with rfl | rfl
        · simp [B1]
        · exact mem_union_left _ hzyR
  obtain ⟨wt, hwt, hBt, hRt, hBBt⟩ := basic Gl R B1 hg (fun _ => 0) (fun _ => ⟨0, by ring⟩)
  simp only [add_zero] at hBt hBBt
  set μ := wt s(x, zy) with hμ
  have hμb : 1 ≤ μ ∧ μ ≤ 3 := hwt x zy hGlxzy
  -- an odd edge at y in the auxiliary graph
  have hyodd : Odd (sd Gl wt y) := hBt y (by simp [B1])
  obtain ⟨r, hrN, hrodd⟩ := odd_term_of_odd_sum _ _ hyodd
  have hGlyr : Gl.Adj y r := (mem_filter.mp hrN).2
  have hyr : G.Adj y r ∧ r ≠ x ∧ r ≠ zy := by
    rcases hGlyr with ⟨h1, h2, h3⟩ | ⟨h1, _⟩
    · refine ⟨h1, fun h => h2 (by rw [h]; exact Sym2.eq_swap), fun h => h3 (by rw [h])⟩
    · exfalso
      have : y ∈ s(x, zy) := h1 ▸ Sym2.mem_mk_left y r
      rw [Sym2.mem_iff] at this
      rcases this with h | h
      · exact hxyne h.symm
      · exact hzyy h.symm
  obtain ⟨hyr', hrx, hrzy⟩ := hyr
  have hrR : r ∈ R := hyred r hyr' hrx
  have hry : r ≠ y := (hRxy r hrR).2
  set ν := wt s(y, r) with hν
  have hνb : 1 ≤ ν ∧ ν ≤ 3 := hwt y r hGlyr
  have hν13 : ν = 1 ∨ ν = 3 := by
    obtain ⟨k, hk⟩ := hrodd; omega
  -- choice of the new weight on y r
  obtain ⟨c, hc, hcpar, hcxy⟩ : ∃ c : ℤ, (1 ≤ c ∧ c ≤ 3) ∧ Even (c - ν) ∧
      sd Gl wt x ≠ sd Gl wt y + 2 * μ + (c - ν) := by
    by_cases h : sd Gl wt x = sd Gl wt y + 2 * μ
    · refine ⟨4 - ν, by omega, ⟨2 - ν, by ring⟩, by omega⟩
    · exact ⟨ν, hνb, ⟨0, by ring⟩, by simpa using h⟩
  let W : Sym2 V → ℤ := fun e => if e = s(y, r) then c else if e = s(x, y) then μ else
    if e = s(y, zy) then μ else wt e
  have hyrxy : s(y, r) ≠ s(x, y) := by rw [Sym2.eq_swap (a := x)]; exact s2ne_l hrx (Ne.symm hxyne)
  have hyryzy : s(y, r) ≠ s(y, zy) := s2ne_l hrzy hzyy.symm
  have hxyyzy : s(x, y) ≠ s(y, zy) := s2ne hxyne (Ne.symm hzyx)
  have W1 : W s(y, r) = c := by simp [W]
  have W2 : W s(x, y) = μ := by simp only [W, hyrxy.symm, if_false, if_true]
  have W3 : W s(y, zy) = μ := by simp only [W, hyryzy.symm, hxyyzy.symm, if_false, if_true]
  have Wo : ∀ e, e ≠ s(y, r) → e ≠ s(x, y) → e ≠ s(y, zy) → W e = wt e := by
    intro e h1 h2 h3; simp only [W, h1, h2, h3, if_false]
  have hxgl : ∀ u, u ≠ y → u ≠ zy → (Gl.Adj x u ↔ G.Adj x u) := by
    intro u huy huzy
    constructor
    · intro h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · exfalso; rcases Sym2.eq_iff.mp h1 with ⟨_, h⟩ | ⟨h, _⟩
        · exact huzy h
        · exact hzyx h.symm
    · intro h; exact Or.inl ⟨h, s2ne_l huy hxyne, s2ne hxyne (Ne.symm hzyx)⟩
  -- weighted degrees
  have hsdx : sd G W x = sd Gl wt x := by
    rw [sd_nbr_congr Gl G wt W x {y, zy} (fun u hu => ?_), sum_pair hzyy.symm]
    · have n1 : ¬ Gl.Adj x y := by
        intro h; rcases h with ⟨_, h2, _⟩ | ⟨h1, _⟩
        · exact h2 rfl
        · rcases Sym2.eq_iff.mp h1 with ⟨_, h⟩ | ⟨h, _⟩
          · exact hzyy h.symm
          · exact hzyx h.symm
      rw [if_pos hxy, if_neg n1, if_neg hxzy, if_pos hGlxzy, W2]; ring
    · simp only [mem_insert, mem_singleton, not_or] at hu
      have e1 : s(x, u) ≠ s(y, r) := s2ne hxyne (Ne.symm hrx)
      have e2 : s(x, u) ≠ s(x, y) := s2ne_l hu.1 hxyne
      have e3 : s(x, u) ≠ s(y, zy) := s2ne hxyne (Ne.symm hzyx)
      by_cases h : G.Adj x u
      · rw [if_pos ((hxgl u hu.1 hu.2).mpr h), if_pos h, Wo _ e1 e2 e3]
      · rw [if_neg (fun h' => h ((hxgl u hu.1 hu.2).mp h')), if_neg h]
  have hsdzy : sd G W zy = sd Gl wt zy := by
    rw [sd_nbr_congr Gl G wt W zy {x, y} (fun u hu => ?_), sum_pair hxyne]
    · have n1 : ¬ Gl.Adj zy y := by
        intro h; rcases h with ⟨_, _, h3⟩ | ⟨h1, _⟩
        · exact h3 Sym2.eq_swap
        · rcases Sym2.eq_iff.mp h1 with ⟨h, _⟩ | ⟨_, h⟩
          · exact hzyx h
          · exact hxyne h.symm
      have h2 : Gl.Adj zy x := hGlxzy.symm
      have e : W s(zy, y) = μ := by rw [Sym2.eq_swap]; exact W3
      have e' : wt s(zy, x) = μ := by rw [hμ, Sym2.eq_swap]
      rw [if_neg (fun h => hxzy h.symm), if_pos h2, if_pos hyzy.symm, if_neg n1, e, e']; ring
    · simp only [mem_insert, mem_singleton, not_or] at hu
      have e1 : s(zy, u) ≠ s(y, r) := s2ne hzyy hrzy.symm
      have e2 : s(zy, u) ≠ s(x, y) := s2ne hzyx hzyy
      have e3 : s(zy, u) ≠ s(y, zy) := by rw [Sym2.eq_swap (a := y)]; exact s2ne_l hu.2 hzyy
      have hiff : Gl.Adj zy u ↔ G.Adj zy u := by
        constructor
        · intro h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact h1
          · exfalso; rcases Sym2.eq_iff.mp h1 with ⟨h, _⟩ | ⟨_, h⟩
            · exact hzyx h
            · exact hu.1 h
        · intro h; exact Or.inl ⟨h, e2, e3⟩
      by_cases h : G.Adj zy u
      · rw [if_pos (hiff.mpr h), if_pos h, Wo _ e1 e2 e3]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  have hsdy : sd G W y = sd Gl wt y + (μ + (μ + (c - ν))) := by
    have hx1 : x ∉ ({zy, r} : Finset V) := by simp [hzyx.symm, hrx.symm]
    have hx2 : zy ∉ ({r} : Finset V) := by simp [hrzy.symm]
    rw [sd_nbr_congr Gl G wt W y {x, zy, r} (fun u hu => ?_), sum_insert hx1, sum_insert hx2,
      sum_singleton]
    · have n1 : ¬ Gl.Adj y x := by
        intro h; rcases h with ⟨_, h2, _⟩ | ⟨h1, _⟩
        · exact h2 Sym2.eq_swap
        · rcases Sym2.eq_iff.mp h1 with ⟨h, _⟩ | ⟨h, _⟩
          · exact hxyne h.symm
          · exact hzyy h.symm
      have n2 : ¬ Gl.Adj y zy := by
        intro h; rcases h with ⟨_, _, h3⟩ | ⟨h1, _⟩
        · exact h3 rfl
        · rcases Sym2.eq_iff.mp h1 with ⟨h, _⟩ | ⟨h, _⟩
          · exact hxyne h.symm
          · exact hzyy h.symm
      have e1 : W s(y, x) = μ := by rw [Sym2.eq_swap]; exact W2
      rw [if_pos hxy.symm, if_neg n1, e1, if_pos hyzy, if_neg n2, W3, if_pos hyr', if_pos hGlyr, W1]
      ring
    · simp only [mem_insert, mem_singleton, not_or] at hu
      have e1 : s(y, u) ≠ s(y, r) := s2ne_l hu.2.2 hry.symm
      have e2 : s(y, u) ≠ s(x, y) := by rw [Sym2.eq_swap (a := x)]; exact s2ne_l hu.1 (Ne.symm hxyne)
      have e3 : s(y, u) ≠ s(y, zy) := s2ne_l hu.2.1 hzyy.symm
      have hiff : Gl.Adj y u ↔ G.Adj y u := by
        constructor
        · intro h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact h1
          · exfalso; rcases Sym2.eq_iff.mp h1 with ⟨h, _⟩ | ⟨h, _⟩
            · exact hxyne h.symm
            · exact hzyy h.symm
        · intro h; exact Or.inl ⟨h, e2, e3⟩
      by_cases h : G.Adj y u
      · rw [if_pos (hiff.mpr h), if_pos h, Wo _ e1 e2 e3]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  have hsdr : sd G W r = sd Gl wt r + (c - ν) := by
    rw [sd_nbr_congr Gl G wt W r {y} (fun u hu => ?_), sum_singleton]
    · have e1 : W s(r, y) = c := by rw [Sym2.eq_swap]; exact W1
      have e2 : wt s(r, y) = ν := by rw [hν, Sym2.eq_swap]
      rw [if_pos hyr'.symm, if_pos hGlyr.symm, e1, e2]
    · rw [mem_singleton] at hu
      have e1 : s(r, u) ≠ s(y, r) := by rw [Sym2.eq_swap (a := y)]; exact s2ne_l hu hry
      have e2 : s(r, u) ≠ s(x, y) := s2ne hrx hry
      have e3 : s(r, u) ≠ s(y, zy) := s2ne hry hrzy
      have hiff : Gl.Adj r u ↔ G.Adj r u := by
        constructor
        · intro h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact h1
          · exfalso; rcases Sym2.eq_iff.mp h1 with ⟨h, _⟩ | ⟨h, _⟩
            · exact hrx h
            · exact hrzy h
        · intro h; exact Or.inl ⟨h, e2, e3⟩
      by_cases h : G.Adj r u
      · rw [if_pos (hiff.mpr h), if_pos h, Wo _ e1 e2 e3]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  have hsdfar : ∀ v, v ≠ x → v ≠ y → v ≠ zy → v ≠ r → sd G W v = sd Gl wt v := by
    intro v hvx hvy hvzy hvr
    have := sd_nbr_congr Gl G wt W v ∅ (fun u _ => ?_)
    · simpa using this
    have e1 : s(v, u) ≠ s(y, r) := s2ne hvy hvr
    have e2 : s(v, u) ≠ s(x, y) := s2ne hvx hvy
    have e3 : s(v, u) ≠ s(y, zy) := s2ne hvy hvzy
    have hiff : Gl.Adj v u ↔ G.Adj v u := by
      constructor
      · intro h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1
        · exfalso; rcases Sym2.eq_iff.mp h1 with ⟨h, _⟩ | ⟨h, _⟩
          · exact hvx h
          · exact hvzy h
      · intro h; exact Or.inl ⟨h, e2, e3⟩
    by_cases h : G.Adj v u
    · rw [if_pos (hiff.mpr h), if_pos h, Wo _ e1 e2 e3]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  have hB1y : ∀ v ∈ B1, v ≠ y → sd G W v = sd Gl wt v := by
    intro v hv hvy
    simp only [B1, mem_union, mem_insert, mem_singleton] at hv
    rcases hv with hv | rfl | rfl
    · exact hsdfar v (hBxy v hv).1 hvy (fun h => hBR v hv (h ▸ hzyR)) (fun h => hBR v hv (h ▸ hrR))
    · exact hsdx
    · exact absurd rfl hvy
  refine ⟨W, vc_of_split G R B1 hb.ind ?_ W ?_ ?_ ?_ ?_⟩
  · intro a b hab
    have haU := hsupp a b hab
    by_cases hax : a = x
    · subst hax; simp [B1]
    by_cases hay : a = y
    · subst hay; simp [B1]
    have := (hUxy a).mp (by simp [haU, hax, hay])
    simp only [B1, mem_union]; tauto
  · intro a b hab
    by_cases e1 : s(a, b) = s(y, r)
    · rw [e1, W1]; exact hc
    by_cases e2 : s(a, b) = s(x, y)
    · rw [e2, W2]; exact hμb
    by_cases e3 : s(a, b) = s(y, zy)
    · rw [e3, W3]; exact hμb
    rw [Wo _ e1 e2 e3]; exact hwt a b (Or.inl ⟨hab, e2, e3⟩)
  · intro v hv
    by_cases hvy : v = y
    · subst hvy; rw [hsdy]
      obtain ⟨k, hk⟩ := hyodd
      obtain ⟨m, hm⟩ := hcpar
      exact ⟨k + μ + m, by omega⟩
    · rw [hB1y v hv hvy]; exact hBt v hv
  · intro v hv
    have hvx := (hRxy v hv).1
    have hvy := (hRxy v hv).2
    by_cases hvr : v = r
    · subst hvr; rw [hsdr]
      obtain ⟨k, hk⟩ := hRt v hv
      obtain ⟨m, hm⟩ := hcpar
      exact ⟨k + m, by omega⟩
    by_cases hvzy : v = zy
    · subst hvzy; rw [hsdzy]; exact hRt v hv
    rw [hsdfar v hvx hvy hvzy hvr]; exact hRt v hv
  · intro u hu v hv huv
    have hyonly : ∀ w ∈ B1, G.Adj y w → w = x := by
      intro w hw h
      by_contra hwx
      have := hyred w h hwx
      simp only [B1, mem_union, mem_insert, mem_singleton] at hw
      rcases hw with hw | rfl | rfl
      · exact hBR w hw this
      · exact hwx rfl
      · exact G.ne_of_adj h rfl
    by_cases huy : u = y
    · subst huy
      have := hyonly v hv huv; subst this
      rw [hsdy, hsdx]; intro h; apply hcxy; linarith
    by_cases hvy : v = y
    · subst hvy
      have := hyonly u hu huv.symm; subst this
      rw [hsdy, hsdx]; intro h; apply hcxy; linarith
    rw [hB1y u hu huy, hB1y v hv hvy]
    exact hBBt u hu v hv (hGl_of u v huv huy hvy)
end GadgetL
section CaseB2
variable {V : Type} [Fintype V] [DecidableEq V]
open SimpleGraph

lemma erase_pair_l {x y : V} (h : x ≠ y) : ({x, y} : Finset V).erase x = {y} := by
  ext v; simp only [mem_erase, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact absurd h2 h1
    · exact h2
  · rintro rfl; exact ⟨Ne.symm h, Or.inr rfl⟩

lemma erase_pair_r {x y : V} (h : x ≠ y) : ({x, y} : Finset V).erase y = {x} := by
  rw [pair_comm]; exact erase_pair_l (Ne.symm h)

lemma delv_le_of {H1 H2 : SimpleGraph V} (X : Finset V) (h : H1 ≤ H2) : delv H1 X ≤ delv H2 X := by
  intro a b hab
  exact ⟨h hab.1, hab.2.1, hab.2.2⟩

lemma card_two_of (s : Finset V) (a b : V) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : 2 ≤ s.card := by
  have : ({a, b} : Finset V) ⊆ s := by
    intro v hv; simp only [mem_insert, mem_singleton] at hv; rcases hv with rfl | rfl <;> assumption
  have := card_le_card this
  rw [card_pair hab] at this; exact this

/-- Case B2: the removable edge `x y` with `deg x ≥ 3`. -/
theorem caseB2 (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U) (x y : V) (hxU : x ∈ U) (hyU : y ∈ U) (hxy : G.Adj x y)
    (hdx : 3 ≤ (univ.filter (G.Adj x)).card) (hdy : 2 ≤ (univ.filter (G.Adj y)).card)
    (hconn : ∀ a ∈ U \ {x, y}, ∀ b ∈ U \ {x, y}, (delv G {x, y}).Reachable a b) :
    ∃ w, VC G w := by
  have hxyne : x ≠ y := G.ne_of_adj hxy
  set X : Finset V := {x, y} with hX
  have hnbU : ∀ v u, G.Adj v u → v = x ∨ v = y → u ≠ x → u ≠ y → u ∈ U \ X := by
    intro v u hvu _ hux huy
    simp [hX, hsupp u v hvu.symm, hux, huy]
  let A := (univ.filter (G.Adj x)).erase y
  let Bs := (univ.filter (G.Adj y)).erase x
  have hAmem : ∀ v, v ∈ A ↔ G.Adj x v ∧ v ≠ y := by
    intro v; simp only [A, mem_erase, mem_filter, mem_univ, true_and]; tauto
  have hBsmem : ∀ v, v ∈ Bs ↔ G.Adj y v ∧ v ≠ x := by
    intro v; simp only [Bs, mem_erase, mem_filter, mem_univ, true_and]; tauto
  have hAU : ∀ v ∈ A, v ∈ U \ X := fun v hv =>
    hnbU x v ((hAmem v).mp hv).1 (Or.inl rfl) (G.ne_of_adj ((hAmem v).mp hv).1).symm
      ((hAmem v).mp hv).2
  have hBsU : ∀ v ∈ Bs, v ∈ U \ X := fun v hv =>
    hnbU y v ((hBsmem v).mp hv).1 (Or.inr rfl) ((hBsmem v).mp hv).2
      (G.ne_of_adj ((hBsmem v).mp hv).1).symm
  have hAc : 2 ≤ A.card := by
    have : y ∈ univ.filter (G.Adj x) := by simp [hxy]
    simp only [A]; rw [card_erase_of_mem this]; omega
  have hBsc : 1 ≤ Bs.card := by
    have : x ∈ univ.filter (G.Adj y) := by simp [hxy.symm]
    simp only [Bs]; rw [card_erase_of_mem this]; omega
  obtain ⟨a0, ha0⟩ := card_pos.mp (by omega : 0 < A.card)
  obtain ⟨b0, hb0⟩ := card_pos.mp (by omega : 0 < Bs.card)
  obtain ⟨zx, hzxA, zy, hzyBs, P, R0, hzxP, hzyP, hzxR0, hR0P, hR0ind, hPconn, hPAB, hzz,
    hPreach⟩ := path_seed (delv G X) A Bs a0 b0 ha0 hb0 (hconn a0 (hAU a0 ha0) b0 (hBsU b0 hb0))
  have hsuppX : ∀ a b, (delv G X).Adj a b → a ∈ U \ X := fun a b h =>
    mem_sdiff.mpr ⟨hsupp a b h.1, h.2.1⟩
  have hPU : P ⊆ U \ X := fun v hv =>
    reach_mem (delv G X) (U \ X) hsuppX (hPreach v hv) (hAU zx hzxA)
  obtain ⟨R, hb, hRP⟩ := base_of_divide G U X hsupp hconn P R0 hPU hR0P zx hzxP
    (fun a ha b hb' h => hR0ind a ha b hb' ⟨h, (mem_sdiff.mp (hPU (hR0P ha))).2,
      (mem_sdiff.mp (hPU (hR0P hb'))).2⟩) hPconn
  set B := (U \ X) \ R with hBdef
  have hmem := base_mem G U X R hb
  have hUX : ∀ v, v ∈ U \ X ↔ v ∈ R ∨ v ∈ B := by intro v; rw [← hmem v, mem_union]
  have hRX : ∀ v ∈ R, v ≠ x ∧ v ≠ y := by
    intro v hv; have := hb.RU hv; simp only [hX, mem_sdiff, mem_insert, mem_singleton, not_or] at this
    exact this.2
  have hBX : ∀ v ∈ B, v ≠ x ∧ v ≠ y := by
    intro v hv; simp only [hBdef, hX, mem_sdiff, mem_insert, mem_singleton, not_or] at hv
    exact hv.1.2
  have hBR : ∀ v ∈ B, v ∉ R := fun v hv => (mem_sdiff.mp hv).2
  have hxzx : G.Adj x zx := ((hAmem zx).mp hzxA).1
  have hyzy : G.Adj y zy := ((hBsmem zy).mp hzyBs).1
  have hzxU := hAU zx hzxA
  have hzyU := hBsU zy hzyBs
  have hzxR : zx ∉ R := fun h => hzxR0 ((hRP zx hzxP).mp h)
  have hzxB : zx ∈ B := mem_sdiff.mpr ⟨hzxU, hzxR⟩
  have hxnb : ∀ u, G.Adj x u → u ≠ y → u ∈ R ∨ u ∈ B := fun u h h' =>
    (hUX u).mp (hnbU x u h (Or.inl rfl) (G.ne_of_adj h).symm h')
  have hynb : ∀ u, G.Adj y u → u ≠ x → u ∈ R ∨ u ∈ B := fun u h h' =>
    (hUX u).mp (hnbU y u h (Or.inr rfl) h' (G.ne_of_adj h).symm)
  have hXR : ∀ v ∈ R, v ∉ X := fun v hv h => by
    simp only [hX, mem_insert, mem_singleton] at h
    rcases h with rfl | rfl
    · exact (hRX v hv).1 rfl
    · exact (hRX v hv).2 rfl
  have hdBx : Disjoint B {x} := disjoint_singleton_right.mpr (fun h => (hBX x h).1 rfl)
  have hdBy : Disjoint B {y} := disjoint_singleton_right.mpr (fun h => (hBX y h).2 rfl)
  have hdBxy : Disjoint B {x, y} := by
    rw [Finset.disjoint_left]; intro v hv hv'
    simp only [mem_insert, mem_singleton] at hv'
    rcases hv' with rfl | rfl
    · exact (hBX v hv).1 rfl
    · exact (hBX v hv).2 rfl
  -- an edge of the bipartite graph
  have bipe : ∀ (R1 B1 : Finset V) (u v : V), G.Adj u v → u ∈ R1 → v ∈ B1 →
      (bip G R1 B1).Reachable u v := fun R1 B1 u v h hu hv =>
    Adj.reachable ((bip_adj _ _ _ _ _).mpr ⟨h, Or.inl ⟨hu, hv⟩⟩)
  have bipe' : ∀ (R1 B1 : Finset V) (u v : V), G.Adj u v → u ∈ B1 → v ∈ R1 →
      (bip G R1 B1).Reachable u v := fun R1 B1 u v h hu hv =>
    Adj.reachable ((bip_adj _ _ _ _ _).mpr ⟨h, Or.inr ⟨hu, hv⟩⟩)
  have hXex : ∀ v ∈ X, v = x ∨ v = y := by intro v hv; simpa [hX] using hv
  have hel : X.erase x = {y} := erase_pair_l hxyne
  have her : X.erase y = {x} := erase_pair_r hxyne
  have hy2 : ∃ b, G.Adj y b ∧ b ≠ x := by
    have : x ∈ univ.filter (G.Adj y) := by simp [hxy.symm]
    have hc := card_erase_of_mem this
    obtain ⟨b, hb'⟩ := card_pos.mp (by omega : 0 < ((univ.filter (G.Adj y)).erase x).card)
    simp only [mem_erase, mem_filter, mem_univ, true_and] at hb'
    exact ⟨b, hb'.2, hb'.1⟩
  by_cases hBo : Odd B.card
  · ---------------- |B| odd
    by_cases hxR : ¬ ∃ r ∈ R, G.Adj x r
    · -- (a): x red, y blue
      push Not at hxR
      refine good_place G U hsupp X R hb {x} {y} (by simp [hX]) (by simp [hX])
        (fun v hv => by rcases hXex v hv with rfl | rfl <;> simp)
        (disjoint_singleton.mpr hxyne) ?_ ?_ ?_
      · intro a ha b hb' hab
        rw [mem_singleton] at ha; subst ha
        rcases mem_union.mp hb' with h | h
        · exact hxR b h hab
        · rw [mem_singleton] at h; subst h; exact G.ne_of_adj hab rfl
      · intro t ht
        have hx' : (bip G (R ∪ {x}) (B ∪ {y})).Reachable x zx :=
          bipe _ _ x zx hxzx (by simp) (mem_union_left _ hzxB)
        simp only [mem_union, mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact ⟨zx, hzxU, hx'⟩
        · exact ⟨zx, hzxU, (bipe' _ _ t x hxy.symm (by simp) (by simp)).trans hx'⟩
      · rw [card_union_of_disjoint hdBy, card_singleton]; exact hBo.add_one
    push Not at hxR
    obtain ⟨rx, hrxR, hxrx⟩ := hxR
    by_cases hyR : ¬ ∃ r ∈ R, G.Adj y r
    · -- (b): y red, x blue
      push Not at hyR
      refine good_place G U hsupp X R hb {y} {x} (by simp [hX]) (by simp [hX])
        (fun v hv => by rcases hXex v hv with rfl | rfl <;> simp)
        (disjoint_singleton.mpr hxyne.symm) ?_ ?_ ?_
      · intro a ha b hb' hab
        rw [mem_singleton] at ha; subst ha
        rcases mem_union.mp hb' with h | h
        · exact hyR b h hab
        · rw [mem_singleton] at h; subst h; exact G.ne_of_adj hab rfl
      · intro t ht
        have hx' : (bip G (R ∪ {y}) (B ∪ {x})).Reachable x rx :=
          bipe' _ _ x rx hxrx (by simp) (mem_union_left _ hrxR)
        simp only [mem_union, mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact ⟨rx, hb.RU hrxR, (bipe _ _ t x hxy.symm (by simp) (by simp)).trans hx'⟩
        · exact ⟨rx, hb.RU hrxR, hx'⟩
      · rw [card_union_of_disjoint hdBx, card_singleton]; exact hBo.add_one
    push Not at hyR
    obtain ⟨ry, hryR, hyry⟩ := hyR
    by_cases hx2 : 2 ≤ (univ.filter (fun u => G.Adj x u ∧ u ∈ R)).card
    · -- (c): x extra, y blue
      refine rem_place G U hsupp X R hb x (by simp [hX]) ∅ {y} (empty_subset _) (by rw [hel])
        (fun v hv => by rw [hel, mem_singleton] at hv; subst hv; simp)
        (disjoint_empty_left _) (fun a ha => absurd ha (notMem_empty a)) ?_ ?_ ?_ ?_
      · intro t ht
        simp only [empty_union, mem_singleton] at ht; subst ht
        exact ⟨ry, hb.RU hryR, bipe' _ _ t ry hyry (by simp) (by simp [hryR])⟩
      · rw [card_union_of_disjoint hdBy, card_singleton]; exact hBo.add_one
      · simpa using hx2
      · right; apply card_pos.mpr; exact ⟨y, by simp [hxy]⟩
    by_cases hy2' : 2 ≤ (univ.filter (fun u => G.Adj y u ∧ u ∈ R)).card
    · -- (d): y extra, x blue
      refine rem_place G U hsupp X R hb y (by simp [hX]) ∅ {x} (empty_subset _) (by rw [her])
        (fun v hv => by rw [her, mem_singleton] at hv; subst hv; simp)
        (disjoint_empty_left _) (fun a ha => absurd ha (notMem_empty a)) ?_ ?_ ?_ ?_
      · intro t ht
        simp only [empty_union, mem_singleton] at ht; subst ht
        exact ⟨rx, hb.RU hrxR, bipe' _ _ t rx hxrx (by simp) (by simp [hrxR])⟩
      · rw [card_union_of_disjoint hdBx, card_singleton]; exact hBo.add_one
      · simpa using hy2'
      · right; apply card_pos.mpr; exact ⟨x, by simp [hxy.symm]⟩
    push Not at hx2 hy2'
    have hNRx : ∀ r ∈ R, G.Adj x r ↔ r = rx := by
      intro r hr; constructor
      · intro h; by_contra hne
        exact absurd (card_two_of (univ.filter (fun u => G.Adj x u ∧ u ∈ R)) r rx (by simp [h, hr]) (by simp [hxrx, hrxR]) hne) (by omega)
      · rintro rfl; exact hxrx
    have hNRy : ∀ r ∈ R, G.Adj y r ↔ r = ry := by
      intro r hr; constructor
      · intro h; by_contra hne
        exact absurd (card_two_of (univ.filter (fun u => G.Adj y u ∧ u ∈ R)) r ry (by simp [h, hr]) (by simp [hyry, hryR]) hne) (by omega)
      · rintro rfl; exact hyry
    by_cases hq : rx = ry
    · -- (e): a common red neighbour
      subst hq
      have hz : ∃ z, G.Adj x z ∧ z ≠ y ∧ z ≠ rx := by
        obtain ⟨z, hz⟩ := card_pos.mp (by
          have h1 : y ∈ univ.filter (G.Adj x) := by simp [hxy]
          have h2 : rx ∈ (univ.filter (G.Adj x)).erase y := by
            simp [hxrx, (hRX rx hrxR).2]
          have := card_erase_of_mem h2
          rw [card_erase_of_mem h1] at this
          omega : 0 < (((univ.filter (G.Adj x)).erase y).erase rx).card)
        simp only [mem_erase, mem_filter, mem_univ, true_and] at hz
        exact ⟨z, hz.2.2, hz.2.1, hz.1⟩
      exact gadgetE G U hsupp x y rx hxy R hb hrxR hNRx hNRy hz hBo
    -- (f): distinct red neighbours; the seed path avoids both
    have hrxP : rx ∉ P := by
      intro h
      rcases hPAB rx h (Or.inl ((hAmem rx).mpr ⟨hxrx, (hRX rx hrxR).2⟩)) with h' | h'
      · exact hzxR (h' ▸ hrxR)
      · have : zy = ry := (hNRy zy (h' ▸ hrxR)).mp hyzy
        exact hq (h'.trans this)
    have hPmono : ∀ (Rn Bn : Finset V) (u0 : V), u0 ∉ P →
        bip (delv G X) R0 (P \ R0) ≤ delv (bip G (R ∪ Rn) (B ∪ Bn)) {u0} := by
      intro Rn Bn u0 hu0 a b hab
      simp only [bip_adj, delv_adj, mem_sdiff, mem_singleton] at hab ⊢
      have hR0R : ∀ v ∈ R0, v ∈ R := fun v hv => (hRP v (hR0P hv)).mpr hv
      have hPB : ∀ v, v ∈ P → v ∉ R0 → v ∈ B := fun v hv hv' =>
        mem_sdiff.mpr ⟨hPU hv, fun h => hv' ((hRP v hv).mp h)⟩
      rcases hab.2 with ⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
      · exact ⟨⟨hab.1.1, Or.inl ⟨mem_union_left _ (hR0R a h1), mem_union_left _ (hPB b h2 h3)⟩⟩,
          fun h => hu0 (h ▸ hR0P h1), fun h => hu0 (h ▸ h2)⟩
      · exact ⟨⟨hab.1.1, Or.inr ⟨mem_union_left _ (hPB a h1 h2), mem_union_left _ (hR0R b h3)⟩⟩,
          fun h => hu0 (h ▸ h1), fun h => hu0 (h ▸ hR0P h3)⟩
    by_cases hzyR : zy ∈ R
    · -- (f1): v0 = x, path zx ... zy, y
      have hzyry : zy = ry := (hNRy zy hzyR).mp hyzy
      refine rearr_place G U hsupp X R hb x (by simp [hX]) ∅ {y} (empty_subset _) (by rw [hel])
        (fun v hv => by rw [hel, mem_singleton] at hv; subst hv; simp)
        (disjoint_empty_left _) (fun a ha => absurd ha (notMem_empty a)) ?_ ?_ rx (by simp [hrxR])
        (fun r hr => hNRx r (by simpa using hr)) zx y (mem_union_left _ hzxB) (by simp)
        (hBX zx hzxB).2 hxzx hxy ?_
      · intro t ht
        simp only [empty_union, mem_singleton] at ht; subst ht
        exact ⟨ry, hb.RU hryR, bipe' _ _ t ry hyry (by simp) (by simp [hryR])⟩
      · rw [card_union_of_disjoint hdBy, card_singleton]; exact hBo.add_one
      · refine ((hPconn zy hzyP).mono (hPmono ∅ {y} rx hrxP)).trans (Adj.reachable ?_)
        simp only [delv_adj, bip_adj, mem_singleton, mem_union]
        refine ⟨⟨hyzy.symm, Or.inl ⟨Or.inl hzyR, by simp⟩⟩, fun h => hq (h.symm.trans hzyry),
          fun h => (hRX rx hrxR).2 h.symm⟩
    · -- (f2)
      have hzyB : zy ∈ B := mem_sdiff.mpr ⟨hzyU, hzyR⟩
      have hzyry : zy ≠ ry := fun h => hzyR (h ▸ hryR)
      rcases first_hit (hb.conn zy hzyU rx (hb.RU hrxR)) hzyry (fun h => hq h.symm) with h | h
      · -- v0 = y, path zy ... rx, x
        refine rearr_place G U hsupp X R hb y (by simp [hX]) ∅ {x} (empty_subset _) (by rw [her])
          (fun v hv => by rw [her, mem_singleton] at hv; subst hv; simp)
          (disjoint_empty_left _) (fun a ha => absurd ha (notMem_empty a)) ?_ ?_ ry
          (by simp [hryR]) (fun r hr => hNRy r (by simpa using hr)) zy x (mem_union_left _ hzyB)
          (by simp) (hBX zy hzyB).1 hyzy hxy.symm ?_
        · intro t ht
          simp only [empty_union, mem_singleton] at ht; subst ht
          exact ⟨rx, hb.RU hrxR, bipe' _ _ t rx hxrx (by simp) (by simp [hrxR])⟩
        · rw [card_union_of_disjoint hdBx, card_singleton]; exact hBo.add_one
        · refine (h.mono (delv_le_of {ry} (bip_mono G (by simp) subset_union_left))).trans
            (Adj.reachable ?_)
          simp only [delv_adj, bip_adj, mem_singleton, mem_union]
          exact ⟨⟨hxrx.symm, Or.inl ⟨Or.inl hrxR, by simp⟩⟩, hq, fun h => (hRX ry hryR).1 h.symm⟩
      · -- v0 = x, path zx ... zy ... ry, y
        have hzyP' : (delv (bip G (R ∪ ∅) (B ∪ {y})) {rx}).Reachable zx zy :=
          (hPconn zy hzyP).mono (hPmono ∅ {y} rx hrxP)
        refine rearr_place G U hsupp X R hb x (by simp [hX]) ∅ {y} (empty_subset _) (by rw [hel])
          (fun v hv => by rw [hel, mem_singleton] at hv; subst hv; simp)
          (disjoint_empty_left _) (fun a ha => absurd ha (notMem_empty a)) ?_ ?_ rx
          (by simp [hrxR]) (fun r hr => hNRx r (by simpa using hr)) zx y (mem_union_left _ hzxB)
          (by simp) (hBX zx hzxB).2 hxzx hxy ?_
        · intro t ht
          simp only [empty_union, mem_singleton] at ht; subst ht
          exact ⟨ry, hb.RU hryR, bipe' _ _ t ry hyry (by simp) (by simp [hryR])⟩
        · rw [card_union_of_disjoint hdBy, card_singleton]; exact hBo.add_one
        · refine (hzyP'.trans (h.mono (delv_le_of {rx} (bip_mono G (by simp)
            subset_union_left)))).trans (Adj.reachable ?_)
          simp only [delv_adj, bip_adj, mem_singleton, mem_union]
          exact ⟨⟨hyry.symm, Or.inl ⟨Or.inl hryR, by simp⟩⟩, fun h => hq h.symm,
            fun h => (hRX rx hrxR).2 h.symm⟩
  · ---------------- |B| even
    have hBe : Even B.card := Nat.not_odd_iff_even.mp hBo
    by_cases hxR : ∃ r ∈ R, G.Adj x r
    · obtain ⟨rx, hrxR, hxrx⟩ := hxR
      by_cases hyR : ∃ r ∈ R, G.Adj y r
      · -- (g): both blue
        obtain ⟨ry, hryR, hyry⟩ := hyR
        refine good_place G U hsupp X R hb ∅ {x, y} (empty_subset _) (subset_refl _)
          (fun v hv => Or.inr hv) (disjoint_empty_left _) (fun a ha => absurd ha (notMem_empty a))
          ?_ ?_
        · intro t ht
          simp only [empty_union, mem_insert, mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact ⟨rx, hb.RU hrxR, bipe' _ _ t rx hxrx (by simp) (by simp [hrxR])⟩
          · exact ⟨ry, hb.RU hryR, bipe' _ _ t ry hyry (by simp) (by simp [hryR])⟩
        · rw [card_union_of_disjoint hdBxy, card_pair hxyne]; exact hBe.add (by decide)
      · -- (h): y red, x extra
        push Not at hyR
        obtain ⟨b, hyb, hbx⟩ := hy2
        have hbB : b ∈ B := by
          rcases hynb b hyb hbx with h | h
          · exact absurd hyb (hyR b h)
          · exact h
        refine rem_place G U hsupp X R hb x (by simp [hX]) {y} ∅ (by rw [hel]) (empty_subset _)
          (fun v hv => by rw [hel, mem_singleton] at hv; subst hv; simp)
          (disjoint_empty_right _) ?_ ?_ ?_ ?_ ?_
        · intro a ha c hc hac
          rw [mem_singleton] at ha; subst ha
          rcases mem_union.mp hc with h | h
          · exact hyR c h hac
          · rw [mem_singleton] at h; subst h; exact G.ne_of_adj hac rfl
        · intro t ht
          simp only [union_empty, mem_singleton] at ht; subst ht
          exact ⟨b, mem_sdiff.mp hbB |>.1, bipe _ _ t b hyb (by simp) (mem_union_left _ hbB)⟩
        · simpa using hBe
        · exact card_two_of _ y rx (by simp [hxy]) (by simp [hxrx, hrxR]) (hRX rx hrxR).2.symm
        · right; apply card_pos.mpr; exact ⟨zx, mem_filter.mpr ⟨mem_univ _, hxzx, mem_union_left _ hzxB⟩⟩
    · push Not at hxR
      have hxzR : ∀ u, G.Adj x u → u ≠ y → u ∈ B := by
        intro u hu huy
        rcases hxnb u hu huy with h | h
        · exact absurd hu (hxR u h)
        · exact h
      by_cases hyR : ∃ r ∈ R, G.Adj y r
      · obtain ⟨ry, hryR, hyry⟩ := hyR
        by_cases hyB : ∃ b ∈ B, G.Adj y b
        · -- (j): x red, y extra
          obtain ⟨b, hbB, hyb⟩ := hyB
          refine rem_place G U hsupp X R hb y (by simp [hX]) {x} ∅ (by rw [her]) (empty_subset _)
            (fun v hv => by rw [her, mem_singleton] at hv; subst hv; simp)
            (disjoint_empty_right _) ?_ ?_ ?_ ?_ ?_
          · intro a ha c hc hac
            rw [mem_singleton] at ha; subst ha
            rcases mem_union.mp hc with h | h
            · exact hxR c h hac
            · rw [mem_singleton] at h; subst h; exact G.ne_of_adj hac rfl
          · intro t ht
            simp only [union_empty, mem_singleton] at ht; subst ht
            exact ⟨zx, hzxU, bipe _ _ t zx hxzx (by simp) (mem_union_left _ hzxB)⟩
          · simpa using hBe
          · exact card_two_of _ x ry (by simp [hxy.symm]) (by simp [hyry, hryR])
              (hRX ry hryR).1.symm
          · right; apply card_pos.mpr; exact ⟨b, mem_filter.mpr ⟨mem_univ _, hyb, mem_union_left _ hbB⟩⟩
        · push Not at hyB
          have hyonlyR : ∀ u, G.Adj y u → u ≠ x → u ∈ R := by
            intro u hu hux
            rcases hynb u hu hux with h | h
            · exact h
            · exact absurd hu (hyB u h)
          have hzyR : zy ∈ R := hyonlyR zy hyzy ((hBsmem zy).mp hzyBs).2
          by_cases hde : Even (univ.filter (G.Adj y)).card
          · -- (k): x red, y extra with an even number of red neighbours
            have hfe : univ.filter (fun u => G.Adj y u ∧ u ∈ R ∪ {x}) = univ.filter (G.Adj y) := by
              ext u; simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton]
              constructor
              · exact fun h => h.1
              · intro h; refine ⟨h, ?_⟩
                by_cases hux : u = x
                · exact Or.inr hux
                · exact Or.inl (hyonlyR u h hux)
            refine rem_place G U hsupp X R hb y (by simp [hX]) {x} ∅ (by rw [her]) (empty_subset _)
              (fun v hv => by rw [her, mem_singleton] at hv; subst hv; simp)
              (disjoint_empty_right _) ?_ ?_ ?_ ?_ ?_
            · intro a ha c hc hac
              rw [mem_singleton] at ha; subst ha
              rcases mem_union.mp hc with h | h
              · exact hxR c h hac
              · rw [mem_singleton] at h; subst h; exact G.ne_of_adj hac rfl
            · intro t ht
              simp only [union_empty, mem_singleton] at ht; subst ht
              exact ⟨zx, hzxU, bipe _ _ t zx hxzx (by simp) (mem_union_left _ hzxB)⟩
            · simpa using hBe
            · rw [hfe]; exact hdy
            · left; rw [hfe]; exact hde
          · -- (l): the second gadget
            have hr0 : ∃ r0, G.Adj y r0 ∧ r0 ≠ x ∧ r0 ≠ zy := by
              have hodd : Odd (univ.filter (G.Adj y)).card := Nat.not_even_iff_odd.mp hde
              have h3 : 3 ≤ (univ.filter (G.Adj y)).card := by
                obtain ⟨k, hk⟩ := hodd; omega
              have h1 : x ∈ univ.filter (G.Adj y) := by simp [hxy.symm]
              have h2 : zy ∈ (univ.filter (G.Adj y)).erase x := by
                simp [hyzy, ((hBsmem zy).mp hzyBs).2]
              obtain ⟨r0, hr0⟩ := card_pos.mp (by
                have := card_erase_of_mem h2
                rw [card_erase_of_mem h1] at this
                omega : 0 < (((univ.filter (G.Adj y)).erase x).erase zy).card)
              simp only [mem_erase, mem_filter, mem_univ, true_and] at hr0
              exact ⟨r0, hr0.2.2, hr0.2.1, hr0.1⟩
            exact gadgetL G U hsupp x y zy hxy R hb hzyR hyzy hxR hyB hr0 hBe
      · -- (i'): x extra with y its only red neighbour
        push Not at hyR
        obtain ⟨b, hyb, hbx⟩ := hy2
        have hbB : b ∈ B := by
          rcases hynb b hyb hbx with h | h
          · exact absurd hyb (hyR b h)
          · exact h
        obtain ⟨z, hz⟩ := card_pos.mp (by
          have := card_erase_of_mem hzxA; omega : 0 < (A.erase zx).card)
        have hzA : z ∈ A := mem_of_mem_erase hz
        have hzzx : z ≠ zx := ne_of_mem_erase hz
        have hxz : G.Adj x z := ((hAmem z).mp hzA).1
        have hzB : z ∈ B := hxzR z hxz ((hAmem z).mp hzA).2
        refine rearr_place G U hsupp X R hb x (by simp [hX]) {y} ∅ (by rw [hel]) (empty_subset _)
          (fun v hv => by rw [hel, mem_singleton] at hv; subst hv; simp)
          (disjoint_empty_right _) ?_ ?_ ?_ y (by simp) ?_ zx z (mem_union_left _ hzxB) (mem_union_left _ hzB)
          (Ne.symm hzzx) hxzx hxz ?_
        · intro a ha c hc hac
          rw [mem_singleton] at ha; subst ha
          rcases mem_union.mp hc with h | h
          · exact hyR c h hac
          · rw [mem_singleton] at h; subst h; exact G.ne_of_adj hac rfl
        · intro t ht
          simp only [union_empty, mem_singleton] at ht; subst ht
          exact ⟨b, mem_sdiff.mp hbB |>.1, bipe _ _ t b hyb (by simp) (mem_union_left _ hbB)⟩
        · simpa using hBe
        · intro r hr
          rcases mem_union.mp hr with h | h
          · exact ⟨fun h' => absurd h' (hxR r h), fun h' => absurd (h' ▸ h) (fun h'' => (hRX y h'').2 rfl)⟩
          · rw [mem_singleton] at h; subst h; exact ⟨fun _ => rfl, fun _ => hxy⟩
        · apply (hb.conn zx hzxU z (mem_sdiff.mp hzB).1).mono
          intro u v huv
          simp only [bip_adj, delv_adj, mem_singleton, mem_union] at huv ⊢
          have hu : u ≠ y := by
            rcases huv.2 with ⟨h, _⟩ | ⟨h, _⟩
            · exact (hRX u h).2
            · exact (hBX u h).2
          have hv : v ≠ y := by
            rcases huv.2 with ⟨_, h⟩ | ⟨_, h⟩
            · exact (hBX v h).2
            · exact (hRX v h).2
          refine ⟨⟨huv.1, ?_⟩, hu, hv⟩
          rcases huv.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Or.inl h1, Or.inl h2⟩
          · exact Or.inr ⟨Or.inl h1, Or.inl h2⟩

end CaseB2
section Final
variable {V : Type} [Fintype V] [DecidableEq V]
open SimpleGraph

lemma nbr_other (G : SimpleGraph V) [DecidableRel G.Adj] (v a : V)
    (h : 2 ≤ (univ.filter (G.Adj v)).card) : ∃ u, G.Adj v u ∧ u ≠ a := by
  obtain ⟨u, hu⟩ := card_pos.mp (by
    have := card_erase_le (s := univ.filter (G.Adj v)) (a := a)
    have h2 := pred_card_le_card_erase (s := univ.filter (G.Adj v)) (a := a)
    omega : 0 < ((univ.filter (G.Adj v)).erase a).card)
  simp only [mem_erase, mem_filter, mem_univ, true_and] at hu
  exact ⟨u, hu.2, hu.1⟩

lemma filter_eq_single (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (h : (univ.filter (G.Adj v)).card = 1) : ∃ y, ∀ u, G.Adj v u ↔ u = y := by
  obtain ⟨y, hy⟩ := card_eq_one.mp h
  refine ⟨y, fun u => ?_⟩
  have := congrArg (fun s => u ∈ s) hy
  simpa using this

theorem connected_case (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hsupp : ∀ a b, G.Adj a b → a ∈ U) (hconn : ∀ a ∈ U, ∀ b ∈ U, G.Reachable a b)
    (hNI : ∀ u v, G.Adj u v → 2 ≤ (univ.filter (G.Adj u)).card ∨
      2 ≤ (univ.filter (G.Adj v)).card)
    (hU : 3 ≤ U.card) : ∃ w, VC G w := by
  have hpos : ∀ v ∈ U, 1 ≤ (univ.filter (G.Adj v)).card := by
    intro v hv
    obtain ⟨u, hu⟩ := card_pos.mp (by
      have := card_erase_of_mem hv; omega : 0 < (U.erase v).card)
    obtain ⟨p⟩ := hconn v hv u (mem_of_mem_erase hu)
    have hn : ¬ p.Nil := fun h => (ne_of_mem_erase hu) h.eq.symm
    exact card_pos.mpr ⟨p.snd, by simp [Walk.adj_snd hn]⟩
  by_cases hleaf : ∃ x ∈ U, (univ.filter (G.Adj x)).card = 1
  · obtain ⟨x, hxU, hx1⟩ := hleaf
    obtain ⟨y, hy⟩ := filter_eq_single G x hx1
    have hxy : G.Adj x y := (hy y).mpr rfl
    have hy2 : 2 ≤ (univ.filter (G.Adj y)).card := by
      rcases hNI x y hxy with h | h
      · omega
      · exact h
    obtain ⟨u, hyu, hux⟩ := nbr_other G y x hy2
    exact caseA G U hsupp hconn x y hxU hy ⟨u, hux, hyu⟩
  push Not at hleaf
  have hdeg : ∀ v ∈ U, 2 ≤ (univ.filter (G.Adj v)).card := by
    intro v hv; have := hpos v hv; have := hleaf v hv; omega
  obtain ⟨x, y, hxy, hc⟩ := blocks G U hsupp hconn hdeg hU
  have hxU : x ∈ U := hsupp x y hxy
  have hyU : y ∈ U := hsupp y x hxy.symm
  by_cases hx3 : 3 ≤ (univ.filter (G.Adj x)).card
  · exact caseB2 G U hsupp x y hxU hyU hxy hx3 (hdeg y hyU) hc
  by_cases hy3 : 3 ≤ (univ.filter (G.Adj y)).card
  · have hp : ({y, x} : Finset V) = {x, y} := pair_comm y x
    exact caseB2 G U hsupp y x hyU hxU hxy.symm hy3 (hdeg x hxU) (by rw [hp]; exact hc)
  have hx2 : (univ.filter (G.Adj x)).card = 2 := by have := hdeg x hxU; omega
  have hy2 : (univ.filter (G.Adj y)).card = 2 := by have := hdeg y hyU; omega
  have other : ∀ v w, G.Adj v w → (univ.filter (G.Adj v)).card = 2 →
      ∃ z, z ≠ w ∧ ∀ u, G.Adj v u ↔ u = w ∨ u = z := by
    intro v w hvw h2
    have hw : w ∈ univ.filter (G.Adj v) := by simp [hvw]
    have hc1 : ((univ.filter (G.Adj v)).erase w).card = 1 := by
      rw [card_erase_of_mem hw]; omega
    obtain ⟨z, hz⟩ := card_eq_one.mp hc1
    have hzm : z ∈ (univ.filter (G.Adj v)).erase w := by rw [hz]; exact mem_singleton_self z
    refine ⟨z, ne_of_mem_erase hzm, fun u => ?_⟩
    constructor
    · intro hu
      by_cases huw : u = w
      · exact Or.inl huw
      · right
        have : u ∈ (univ.filter (G.Adj v)).erase w := by simp [huw, hu]
        rw [hz] at this; simpa using this
    · rintro (rfl | rfl)
      · exact hvw
      · exact (mem_filter.mp (mem_of_mem_erase hzm)).2
  obtain ⟨zx, hzx, hNx⟩ := other x y hxy hx2
  obtain ⟨zy, hzy, hNy⟩ := other y x hxy.symm hy2
  exact caseB1 G U hsupp x y zx zy hxU hyU hNx hNy hzx hzy hc

/-- every graph with no isolated edge has a vertex-colouring weighting with weights 1, 2, 3 -/
theorem main_vc (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNI : ∀ u v, G.Adj u v → 2 ≤ (univ.filter (G.Adj u)).card ∨
      2 ≤ (univ.filter (G.Adj v)).card) : ∃ w, VC G w := by
  classical
  let C : V → Finset V := fun v => univ.filter (G.Reachable v)
  have hCmem : ∀ v a, a ∈ C v ↔ G.Reachable v a := by intro v a; simp [C]
  have hCeq : ∀ v a, a ∈ C v → C a = C v := by
    intro v a ha; ext b
    rw [hCmem, hCmem]
    have := (hCmem v a).mp ha
    exact ⟨fun h => this.trans h, fun h => this.symm.trans h⟩
  have hCadj : ∀ v a b, a ∈ C v → G.Adj a b → b ∈ C v := by
    intro v a b ha hab
    exact (hCmem v b).mpr (((hCmem v a).mp ha).trans hab.reachable)
  -- a weighting for every component
  have hcomp : ∀ v, ∃ w, VC (delv G (univ \ C v)) w := by
    intro v
    let Gc := delv G (univ \ C v)
    have hGc : ∀ a b, Gc.Adj a b ↔ G.Adj a b ∧ a ∈ C v ∧ b ∈ C v := by
      intro a b; simp [Gc]
    by_cases hedge : ∃ a b, Gc.Adj a b
    · obtain ⟨a, b, hab⟩ := hedge
      have hsuppc : ∀ a b, Gc.Adj a b → a ∈ C v := fun a b h => ((hGc a b).mp h).2.1
      have hconnc : ∀ a ∈ C v, ∀ b ∈ C v, Gc.Reachable a b := by
        intro a ha b hb
        obtain ⟨p⟩ := ((hCmem v a).mp ha).symm.trans ((hCmem v b).mp hb)
        apply reach_avoid p
        intro u hu hu'
        simp only [mem_sdiff, mem_univ, true_and] at hu'
        apply hu'
        exact (hCmem v u).mpr (((hCmem v a).mp ha).trans
          ⟨p.takeUntil u hu⟩)
      have hdegc : ∀ u ∈ C v, univ.filter (Gc.Adj u) = univ.filter (G.Adj u) := by
        intro u hu; ext x
        simp only [mem_filter, mem_univ, true_and, hGc]
        exact ⟨fun h => h.1, fun h => ⟨h, hu, hCadj v u x hu h⟩⟩
      have hNIc : ∀ u w, Gc.Adj u w → 2 ≤ (univ.filter (Gc.Adj u)).card ∨
          2 ≤ (univ.filter (Gc.Adj w)).card := by
        intro u w huw
        have := (hGc u w).mp huw
        rw [hdegc u this.2.1, hdegc w this.2.2]
        exact hNI u w this.1
      have hab' := (hGc a b).mp hab
      have h3 : 3 ≤ (C v).card := by
        have key : ∀ p q, G.Adj p q → p ∈ C v → 2 ≤ (univ.filter (G.Adj p)).card →
            3 ≤ (C v).card := by
          intro p q hpq hp h2
          obtain ⟨r, hpr, hrq⟩ := nbr_other G p q h2
          have hq : q ∈ C v := hCadj v p q hp hpq
          have hr : r ∈ C v := hCadj v p r hp hpr
          have : ({p, q, r} : Finset V) ⊆ C v := by
            intro z hz; simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl | rfl <;> assumption
          have hc := card_le_card this
          rw [card_insert_of_notMem (by simp [G.ne_of_adj hpq, G.ne_of_adj hpr]),
            card_pair (Ne.symm hrq)] at hc
          exact hc
        rcases hNI a b hab'.1 with h | h
        · exact key a b hab'.1 hab'.2.1 h
        · exact key b a hab'.1.symm hab'.2.2 h
      exact connected_case Gc (C v) hsuppc hconnc hNIc h3
    · push Not at hedge
      exact ⟨fun _ => 2, fun u w h => absurd h (hedge u w), fun u w h => absurd h (hedge u w)⟩
  -- choose one weighting per component (indexed by the component itself)
  have hcomp' : ∀ S : Finset V, ∃ w : Sym2 V → ℤ, ∀ v, C v = S → VC (delv G (univ \ C v)) w := by
    intro S
    by_cases hS : ∃ v, C v = S
    · obtain ⟨v, hv⟩ := hS
      obtain ⟨w, hw⟩ := hcomp v
      exact ⟨w, fun u hu => by rw [hu, ← hv]; exact hw⟩
    · push Not at hS
      exact ⟨fun _ => 0, fun v hv => absurd hv (hS v)⟩
  choose wc hwc using hcomp'
  let W : Sym2 V → ℤ := Sym2.lift ⟨fun a b => if G.Adj a b then wc (C a) s(a, b) else 1,
    fun a b => by
      dsimp only
      by_cases h : G.Adj a b
      · have : C b = C a := hCeq a b (hCadj a a b ((hCmem a a).mpr (Reachable.refl a)) h)
        rw [if_pos h, if_pos h.symm, this, Sym2.eq_swap]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]⟩
  have hW : ∀ a b, G.Adj a b → W s(a, b) = wc (C a) s(a, b) := by
    intro a b h; simp [W, h]
  have haC : ∀ a, a ∈ C a := fun a => (hCmem a a).mpr (Reachable.refl a)
  have hsdW : ∀ a, sd G W a = sd (delv G (univ \ C a)) (wc (C a)) a := by
    intro a
    simp only [sd, sum_filter]
    apply sum_congr rfl; intro u _
    have hiff : (delv G (univ \ C a)).Adj a u ↔ G.Adj a u := by
      simp only [delv_adj, mem_sdiff, mem_univ, true_and, not_not]
      exact ⟨fun h => h.1, fun h => ⟨h, haC a, hCadj a a u (haC a) h⟩⟩
    by_cases h : G.Adj a u
    · rw [if_pos h, if_pos (hiff.mpr h), hW a u h]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
  refine ⟨W, ?_, ?_⟩
  · intro a b hab
    rw [hW a b hab]
    exact (hwc (C a) a rfl).1 a b ⟨hab, by simp [haC a], by simp [hCadj a a b (haC a) hab]⟩
  · intro a b hab
    rw [hsdW a, hsdW b]
    have hCb : C b = C a := hCeq a b (hCadj a a b (haC a) hab)
    rw [hCb]
    exact (hwc (C a) a rfl).2 a b ⟨hab, by simp [haC a], by simp [hCadj a a b (haC a) hab]⟩

lemma incidence_sum (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (f : Sym2 V → ℤ) :
    ∑ e ∈ G.incidenceFinset v, f e = ∑ u ∈ univ.filter (G.Adj v), f s(v, u) := by
  symm
  apply Finset.sum_bij (fun u _ => s(v, u))
  · intro u hu
    rw [mem_incidenceFinset]
    exact ⟨(mem_filter.mp hu).2, Sym2.mem_mk_left v u⟩
  · intro u1 _ u2 _ h
    exact Sym2.congr_right.mp h
  · intro e he
    rw [mem_incidenceFinset] at he
    obtain ⟨he1, he2⟩ := he
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp he2
    exact ⟨u, by simpa using he1, rfl⟩
  · intro u _; rfl

end Final
end OMA.K123

theorem OMA.solution : type_of% @OneTwoThreeConjecture.one_two_three_conjecture := by
  intro V _ _ G _ hNI
  have hdeg : ∀ u, G.degree u = (Finset.univ.filter (G.Adj u)).card := by
    intro u; rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  obtain ⟨W, hWb, hWp⟩ := OMA.K123.main_vc G (fun u v h => by
    have := hNI u v h; rw [hdeg u, hdeg v] at this; exact this)
  refine ⟨fun e => (W e).toNat, ?_, ?_⟩
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have := hWb a b he
      show 1 ≤ (W s(a, b)).toNat ∧ (W s(a, b)).toNat ≤ 3
      omega
  · intro u v huv
    have key : ∀ x, ((OneTwoThreeConjecture.weightedDegree G (fun e => (W e).toNat) x : ℕ) : ℤ) =
        OMA.K123.sd G W x := by
      intro x
      unfold OneTwoThreeConjecture.weightedDegree
      push_cast
      rw [OMA.K123.incidence_sum G x (fun e => ((W e).toNat : ℤ))]
      unfold OMA.K123.sd
      apply Finset.sum_congr rfl
      intro y hy
      have := hWb x y (Finset.mem_filter.mp hy).2
      omega
    intro heq
    apply hWp u v huv
    rw [← key u, ← key v, heq]
