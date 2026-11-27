import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2
import Mathlib

/-! McKay's order-22 bound removes a vertex of degree at most five. For the
remaining graphs it suffices to enumerate maximal triangle-free graphs of
minimum degree six. The unique order-23 extremal maximal graph in McKay's
catalogue is a blow-up of the five-cycle. All its subgraphs with at most
99 edges admit a cut with at most 19 monochromatic edges: averaging the
five alternating cuts charges every edge exactly once.
The vertex-extension lemma is from the parent reduction by @steveDOTdigital. -/

namespace OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1
open Finset SimpleGraph
open scoped Classical

def H1 : Prop := ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 → ∀ W : Finset (Fin 25),
  W.card = 22 → ∃ c : Fin 25 → Bool,
    (∑ i ∈ W, ∑ j ∈ W, if G.Adj i j ∧ c i = c j then 1 else 0) ≤ (34 : ℕ)

def H2 : Prop := ∀ (W : Finset (Fin 25)), W.card = 23 → ∀ K : SimpleGraph (Fin 25),
  K.CliqueFree 3 → (∀ i j, K.Adj i j → i ∈ W ∧ j ∈ W) →
  (∀ H : SimpleGraph (Fin 25), K ≤ H → H.CliqueFree 3 →
    (∀ i j, H.Adj i j → i ∈ W ∧ j ∈ W) → H = K) →
  (∀ i ∈ W, 6 ≤ (W.filter (K.Adj i)).card) →
  (∀ c : Fin 25 → Bool, (38 : ℕ) < ∑ i ∈ W, ∑ j ∈ W,
     if K.Adj i j ∧ c i = c j then 1 else 0) →
  ∃ f : Fin 25 → Fin 5, ∀ i j, K.Adj i j → f i + 1 = f j ∨ f j + 1 = f i

lemma unordered {V : Type*} [LinearOrder V] (W : Finset V) (w : V → V → ℕ)
    (hs : ∀ i j, w i j = w j i) (hz : ∀ i, w i i = 0) :
    (∑ i ∈ W, ∑ j ∈ W, w i j) =
      2 * ∑ i ∈ W, ∑ j ∈ W, if i < j then w i j else 0 := by
  let u i j := if i < j then w i j else 0
  have part (i j) : w i j = u i j + u j i := by
    rcases lt_trichotomy i j with h|rfl|h
    · simp [u,h,not_lt_of_gt h]
    · simp [u,hz]
    · simp [u,h,not_lt_of_gt h,hs i j]
  calc _ = ∑ i ∈ W, ∑ j ∈ W, (u i j + u j i) :=
            sum_congr rfl fun i _ => sum_congr rfl fun j _ => part i j
       _ = _ := by
            simp only [sum_add_distrib]
            rw [sum_comm (s := W) (t := W) (f := fun i j => u j i)]
            change _ + _ = 2 * (∑ i ∈ W, ∑ j ∈ W, u i j)
            omega

lemma cycle_cut (G : SimpleGraph (Fin 25)) (W : Finset (Fin 25)) (f : Fin 25 → Fin 5)
    (edge : ∀ i ∈ W, ∀ j ∈ W, G.Adj i j → f i + 1 = f j ∨ f j + 1 = f i)
    (size : (∑ i ∈ W, ∑ j ∈ W, if G.Adj i j then 1 else 0) ≤ (198 : ℕ)) :
    ∃ c : Fin 25 → Bool, (∑ i ∈ W, ∑ j ∈ W, if G.Adj i j ∧ c i = c j then 1 else 0) ≤ (38 : ℕ) := by
  classical
  let paint (e x : Fin 5) := decide (((x.val + 5 - e.val) % 5) % 2 = 0)
  have five : ∀ a b : Fin 5, a+1=b ∨ b+1=a →
      (∑ e : Fin 5, if paint e a = paint e b then 1 else 0) = (1 : ℕ) := by decide
  let w (e : Fin 5) (i j : Fin 25) : ℕ := if G.Adj i j ∧ paint e (f i) = paint e (f j) then 1 else 0
  let cost e := ∑ i ∈ W, ∑ j ∈ W, w e i j
  have charges (i) (hi : i∈W) (j) (hj : j∈W) :
      (∑ e : Fin 5, w e i j) = if G.Adj i j then 1 else 0 := by
    by_cases h : G.Adj i j
    · simpa only [w,h,true_and,if_true] using five (f i) (f j) (edge i hi j hj h)
    · simp [w,h]
  have total : (∑ e : Fin 5, cost e) ≤ 198 := by
    calc _ = ∑ i ∈ W, ∑ j ∈ W, ∑ e : Fin 5, w e i j := by
               unfold cost
               rw [sum_comm]
               exact sum_congr rfl fun i _ => sum_comm
         _ = _ := sum_congr rfl fun i hi => sum_congr rfl fun j hj => charges i hi j hj
         _ ≤ _ := size
  by_contra! h
  have large (e : Fin 5) : 40 ≤ cost e := by
    have high := h (fun i => paint e (f i))
    change 38 < cost e at high
    have evenCost := unordered W (w e) (fun i j => by
      by_cases p : paint e (f i) = paint e (f j)
      · simp [w,p,G.adj_comm i j]
      · simp [w,p,Ne.symm p]) (fun i => by simp [w])
    change cost e = _ at evenCost
    omega
  have enough := sum_le_sum (s := (univ : Finset (Fin 5))) (fun e _ => large e)
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at enough
  omega

theorem main : H1 → H2 → OMA.R_Erdos23_erdos_23_variants_n5_R2.H2 := by
  classical
  intro small classify G triangle W cardW size
  by_cases low : ∃ v ∈ W, (W.filter (G.Adj v)).card ≤ 5
  · obtain ⟨v,hv,hdeg⟩ := low
    obtain ⟨c,hc⟩ := small G triangle (W.erase v) (by rw [card_erase_of_mem hv,cardW])
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    have expandCost (U : Finset (Fin 25)) (g : Fin 25 → Bool) :
        (∑ i ∈ U, ∑ j ∈ U, if g i = g j then w i j else 0) =
        ∑ i ∈ U, ∑ j ∈ U, if G.Adj i j ∧ g i = g j then 1 else 0 := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      by_cases e : g i = g j <;> simp [w,e]
    have symm (i j) : w i j = w j i := by simp only [w,G.adj_comm i j]
    obtain ⟨g,hg⟩ := OMA.R_Erdos23_erdos_23_variants_n5_R2.extend_color W hv w symm
      (fun i => by simp [w]) c
    rw [expandCost,expandCost] at hg
    have d : (∑ j ∈ W.erase v, w v j) ≤ 5 := by
      rw [← card_filter] at *
      exact (card_le_card (filter_subset_filter _ (erase_subset _ _))).trans hdeg
    exact ⟨g,by omega⟩
  let G₀ : SimpleGraph (Fin 25) := {
    Adj := fun i j => G.Adj i j ∧ i ∈ W ∧ j ∈ W
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
    loopless := ⟨fun i h => G.loopless.irrefl i h.1⟩ }
  have gcf : G₀.CliqueFree 3 := triangle.anti (show G₀ ≤ G from fun _ _ h => h.1)
  let eligible (K : SimpleGraph (Fin 25)) := K.CliqueFree 3 ∧ ∀ i j, K.Adj i j → i ∈ W ∧ j ∈ W
  have good : eligible G₀ := ⟨gcf,fun _ _ h => h.2⟩
  obtain ⟨K,sub,maximal⟩ := Finite.exists_le_maximal (p := eligible) good
  have lift (i) (hi : i ∈ W) (j) (hj : j ∈ W) (e : G.Adj i j) : K.Adj i j := sub ⟨e,hi,hj⟩
  have cost (c : Fin 25 → Bool) :
      (∑ i ∈ W, ∑ j ∈ W, if G.Adj i j ∧ c i = c j then 1 else 0) ≤
      (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ c i = c j then 1 else (0:ℕ)) := by
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    by_cases h : G.Adj i j ∧ c i = c j
    · simp [h,lift i hi j hj h.1]
    · simp [h]
  by_contra! fail
  obtain ⟨f,hf⟩ := classify W cardW K maximal.1.1 maximal.1.2
    (fun H le cf support => le_antisymm (maximal.2 ⟨cf,support⟩ le) le)
    (fun i hi => by
      have hd : 6 ≤ (W.filter (G.Adj i)).card := by by_contra! h; exact low ⟨i,hi,by omega⟩
      exact hd.trans (card_le_card (fun j hj => mem_filter.mpr
        ⟨(mem_filter.mp hj).1,lift i hi j (mem_filter.mp hj).1 (mem_filter.mp hj).2⟩)))
    (fun c => (fail c).trans_le (cost c))
  obtain ⟨c,hc⟩ := cycle_cut G W f (fun i hi j hj e => hf i j (lift i hi j hj e)) size
  exact (fail c).not_ge hc

end OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1

