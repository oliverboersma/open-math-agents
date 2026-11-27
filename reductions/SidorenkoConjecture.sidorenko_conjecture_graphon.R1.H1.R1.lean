import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1
import Mathlib

/-! The 13-point, 22-face incidence pattern and sampling error constants are
from OpenAI, A counterexample to Sidorenko's conjecture. The face table and
sample-size estimate are adapted under Apache-2.0 from openai/math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Sidorenko/Exposure.lean and
Sidorenko/RandomHost.lean. -/

open SimpleGraph
namespace OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1

/-- A finite symmetric weighted kernel with a strict moment gap for the pattern. -/
def H1 : Prop :=
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0, 1, 3], ![0, 1, 9], ![0, 2, 3], ![0, 2, 9], ![1, 3, 10], ![1, 7, 10], ![1, 7, 12], ![1, 9, 12], ![2, 3, 4], ![2, 4, 9], ![3, 4, 11], ![3, 10, 11], ![4, 8, 9], ![4, 8, 11], ![5, 6, 7], ![5, 6, 11], ![5, 7, 10], ![5, 10, 11], ![6, 7, 12], ![6, 8, 11], ![6, 8, 12], ![8, 9, 12]]
  ∃ (Ω : Type) (_ : Fintype Ω) (_ : Nonempty Ω) (w : Ω → ℝ) (K : Ω → Ω → ℝ),
    (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 ∧ (∀ a b, 0 ≤ K a b ∧ K a b ≤ 1) ∧
    (∀ a b, K a b = K b a) ∧ 0 < (∑ x, w x * ∑ y, w y * K x y) ∧
    (∑ x : Fin 13 → Ω, (∏ i, w (x i)) *
      ∑ y : Fin 22 → Ω, (∏ j, w (y j)) * ∏ k : Fin 22 × Fin 3, K (x (t k.1 k.2)) (y k.1)) < (∑ x, w x * ∑ y, w y * K x y)^66

/-- Sample the weighted pattern on n vertices. The 595 possible collisions
give the additive 595/n term on homomorphism density. -/
def H2 : Prop :=
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0, 1, 3], ![0, 1, 9], ![0, 2, 3], ![0, 2, 9], ![1, 3, 10], ![1, 7, 10], ![1, 7, 12], ![1, 9, 12], ![2, 3, 4], ![2, 4, 9], ![3, 4, 11], ![3, 10, 11], ![4, 8, 9], ![4, 8, 11], ![5, 6, 7], ![5, 6, 11], ![5, 7, 10], ![5, 10, 11], ![6, 7, 12], ![6, 8, 11], ![6, 8, 12], ![8, 9, 12]]
  ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (w : Ω → ℝ) (K : Ω → Ω → ℝ),
    (∀ a, 0 ≤ w a) → ∑ a, w a = 1 → (∀ a b, 0 ≤ K a b ∧ K a b ≤ 1) →
    (∀ a b, K a b = K b a) →
    let μ := (∑ x, w x * ∑ y, w y * K x y)
    let τ := (∑ x : Fin 13 → Ω, (∏ i, w (x i)) *
      ∑ y : Fin 22 → Ω, (∏ j, w (y j)) * ∏ k : Fin 22 × Fin 3, K (x (t k.1 k.2)) (y k.1))
    0 < μ → τ < μ^66 → ∀ n : ℕ, 0 < n → τ + 595 / n < ((1 - 1/(n : ℝ))*μ)^66 →
    ∃ G : SimpleGraph (Fin n),
      (Nat.card {f : Fin 13 ⊕ Fin 22 → Fin n //
        ∀ j i, G.Adj (f (.inl (t j i))) (f (.inr j))} : ℝ) / (n : ℝ)^35 <
        (2 * (Nat.card G.edgeSet : ℝ) / (n : ℝ)^2)^66

lemma finiteHost_arithmetic {μ τ : ℝ} (hμ : 0≤μ) (hgap : τ<μ^66) {n : ℕ} (hn : 0<n)
    (hsize : (595+66*μ^66)/(μ^66-τ)<n) :
    τ+595/(n:ℝ)<((1-1/(n:ℝ))*μ)^66 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hΔ : 0<μ^66-τ := sub_pos.mpr hgap
  have hs := (div_lt_iff₀ hΔ).mp hsize
  have hd : (595+66*μ^66)/(n:ℝ)<μ^66-τ := (div_lt_iff₀ hn').mpr (by nlinarith [hs])
  rw [add_div] at hd
  have hfirst : τ+595/(n:ℝ)<μ^66-66*μ^66/(n:ℝ) := by linarith
  apply hfirst.trans_le
  have hinv : 1/(n:ℝ)≤1 := (div_le_one hn').mpr hn1
  have hb := one_add_mul_le_pow (a := -(1/(n:ℝ))) (by linarith : (-2:ℝ)≤-(1/(n:ℝ))) 66
  have hmul := mul_le_mul_of_nonneg_right hb (pow_nonneg hμ 66)
  calc
    _ = (1+(66:ℝ)* -(1/(n:ℝ)))*μ^66 := by ring
    _ ≤ (1+ -(1/(n:ℝ)))^66*μ^66 := hmul
    _ = _ := by rw [sub_eq_add_neg,mul_pow]

theorem main : H1 → H2 → OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1.H1 := by
  intro kernel sample univ
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0, 1, 3], ![0, 1, 9], ![0, 2, 3], ![0, 2, 9], ![1, 3, 10], ![1, 7, 10], ![1, 7, 12], ![1, 9, 12], ![2, 3, 4], ![2, 4, 9], ![3, 4, 11], ![3, 10, 11], ![4, 8, 9], ![4, 8, 11], ![5, 6, 7], ![5, 6, 11], ![5, 7, 10], ![5, 10, 11], ![6, 7, 12], ![6, 8, 11], ![6, 8, 12], ![8, 9, 12]]
  obtain ⟨Ω,fi,ne,w,K,hw,sw,hK,hs,hμ,gap⟩ := kernel
  let μ := (∑ x, w x * ∑ y, w y * K x y)
  let τ := (∑ x : Fin 13 → Ω, (∏ i, w (x i)) *
      ∑ y : Fin 22 → Ω, (∏ j, w (y j)) * ∏ k : Fin 22 × Fin 3, K (x (t k.1 k.2)) (y k.1))
  change 0 < μ at hμ
  change τ < μ^66 at gap
  obtain ⟨n,hn⟩ := exists_nat_gt (max 0 ((595+66*μ^66)/(μ^66-τ)))
  have hn0 : 0 < n := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨G,hG⟩ := sample Ω w K hw sw hK hs hμ gap n hn0
    (finiteHost_arithmetic hμ.le gap hn0 (lt_of_le_of_lt (le_max_right _ _) hn))
  let r : Fin 13 ⊕ Fin 22 → Fin 13 ⊕ Fin 22 → Prop
    | .inl i,.inr j => ∃ a, t j a = i
    | .inr j,.inl i => ∃ a, t j a = i
    | _,_ => False
  let H : SimpleGraph (Fin 13 ⊕ Fin 22) := {
    Adj := r
    symm.symm := by intro a b; cases a <;> cases b <;> exact id
    loopless.irrefl := by intro a; cases a <;> exact id }
  letI : DecidableRel H.Adj := fun u v => by
    cases u <;> cases v <;> dsimp [H,r] <;> infer_instance
  have hc : H.edgeFinset.card = 66 := by decide +kernel
  have hb : H.IsBipartite := ⟨SimpleGraph.Coloring.mk
    (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1))
    (by intro a b h; cases a <;> cases b <;> simp_all [H,r])⟩
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,hn0⟩⟩
  have u := univ H G hb
  let E : (H →g G) ≃ {f : Fin 13 ⊕ Fin 22 → Fin n //
        ∀ j i, G.Adj (f (.inl (t j i))) (f (.inr j))} := {
    toFun := fun f => ⟨f,fun j i => f.map_rel' (show H.Adj (.inl (t j i)) (.inr j) from ⟨i,rfl⟩)⟩
    invFun := fun f => ⟨f.1,by
      intro a b h
      cases a with
      | inl i =>
        cases b with
        | inl j => exact False.elim h
        | inr j => obtain ⟨k,rfl⟩ := h; exact f.2 j k
      | inr j =>
        cases b with
        | inl i => obtain ⟨k,rfl⟩ := h; exact (f.2 j k).symm
        | inr i => exact False.elim h⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [hc] at u
  unfold SimpleGraph.homDensity at u
  rw [SidorenkoConjecture.homCount_completeGraph_fin_two_eq_two_mul_card_edgeFinset] at u
  change _ < _ at hG
  have hnum : Nat.card {f : Fin 13 ⊕ Fin 22 → Fin n //
        ∀ j i, G.Adj (f (.inl (t j i))) (f (.inr j))} = SimpleGraph.homCount H G := by
    rw [← Nat.card_congr E,Nat.card_eq_fintype_card]; rfl
  change (Nat.card {f : Fin 13 ⊕ Fin 22 → Fin n //
        ∀ j i, G.Adj (f (.inl (t j i))) (f (.inr j))} : ℝ) / (n : ℝ)^35 < _ at hG
  rw [hnum,Nat.card_eq_fintype_card,G.card_edgeSet] at hG
  simp only [Fintype.card_fin,Fintype.card_sum,Nat.cast_mul,Nat.cast_ofNat] at u
  exact (not_lt_of_ge u) hG

end OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1
