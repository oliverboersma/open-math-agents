import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2
import Mathlib

/-! # Reducing the high-density blow-up step to finite five-cycle cases
The counts below use ordered edges. A cut rooted at a high-degree-sum
neighborhood and greedy extension of any induced bipartite subgraph give
two necessary constraints on a counterexample. The two-ball of a vertex is
bipartite in a triangle-free graph without five-cycles. -/

namespace OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1
open Finset SimpleGraph Filter
open OMA.R_Erdos23_erdos_23_variants_n5_R2 (erase_total extend_color)
open scoped Classical

def H1 : Prop := ∀ G : SimpleGraph (Fin 25), G.CliqueFree 3 →
  let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
  let d (i : Fin 25) := ∑ j, w i j
  let S := ∑ i, d i
  200 ≤ S → S ≤ 248 →
  (¬ ∃ g : Fin 25 → Fin 5, ∀ i j, G.Adj i j → g j=g i+1 ∨ g i=g j+1) →
  (∀ v, 2*(∑ j, w v j*d j)+51 ≤ S) →
  (∀ W : Finset (Fin 25), ∀ b : Fin 25 → Bool,
    (∀ i ∈ W, ∀ j ∈ W, G.Adj i j → b i ≠ b j) →
    (∑ i ∈ W, ∑ j ∈ W, w i j)+102 ≤ S) →
  ∀ a b c d e : Fin 25, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e a →
    (∀ u, G.Adj u a ∨ G.Adj u b ∨ G.Adj u c ∨ G.Adj u d ∨ G.Adj u e) →
    ∃ f : Fin 25 → Bool, (∑ i, ∑ j, if G.Adj i j ∧ f i = f j then 1 else 0) ≤ (50:ℕ)

def H2 : Prop := ∀ G : SimpleGraph (Fin 25), G.CliqueFree 3 →
  let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
  let d (i : Fin 25) := ∑ j, w i j
  let S := ∑ i, d i
  200 ≤ S → S ≤ 248 →
  (¬ ∃ g : Fin 25 → Fin 5, ∀ i j, G.Adj i j → g j=g i+1 ∨ g i=g j+1) →
  (∀ v, 2*(∑ j, w v j*d j)+51 ≤ S) →
  (∀ W : Finset (Fin 25), ∀ b : Fin 25 → Bool,
    (∀ i ∈ W, ∀ j ∈ W, G.Adj i j → b i ≠ b j) →
    (∑ i ∈ W, ∑ j ∈ W, w i j)+102 ≤ S) →
  ∀ a b c d e : Fin 25, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e a →
    (∃ u, ¬G.Adj u a ∧ ¬G.Adj u b ∧ ¬G.Adj u c ∧ ¬G.Adj u d ∧ ¬G.Adj u e) →
    ∃ f : Fin 25 → Bool, (∑ i, ∑ j, if G.Adj i j ∧ f i = f j then 1 else 0) ≤ (50:ℕ)

lemma extendHalf {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℕ) (sym : ∀ i j, w i j = w j i) (diag : ∀ i, w i i=0)
    (W : Finset V) (b : V → Bool) :
    ∃ f : V → Bool,
      2*(∑ i,∑ j,if f i=f j then w i j else 0) + (∑ i ∈ W,∑ j ∈ W,w i j) ≤
      (∑ i,∑ j,w i j) + 2*(∑ i ∈ W,∑ j ∈ W,if b i=b j then w i j else 0) := by
  let edges (T : Finset V) := ∑ i ∈ T,∑ j ∈ T,w i j
  let cost (T : Finset V) (f : V → Bool) := ∑ i ∈ T,∑ j ∈ T,if f i=f j then w i j else 0
  have more (U : Finset V) : ∃ f, 2*cost (W∪U) f + edges W ≤ edges (W∪U)+2*cost W b := by
    induction U using Finset.induction_on with
    | empty => exact ⟨b,by simp [add_comm]⟩
    | @insert x U _ ih =>
      obtain ⟨f,bound⟩ := ih
      by_cases old : x ∈ W∪U
      · have eq : W∪insert x U = W∪U := by rw [union_insert,insert_eq_of_mem old]
        exact ⟨f,by rwa [eq]⟩
      · let T := W∪insert x U
        have tx : x ∈ T := mem_union_right _ (mem_insert_self ..)
        have er : T.erase x = W∪U := by change (W∪insert x U).erase x = _; rw [union_insert,erase_insert old]
        obtain ⟨g,extra⟩ := extend_color T tx w sym diag f
        have inc := erase_total T tx w sym (diag x)
        rw [er] at extra inc
        change cost T g ≤ cost (W∪U) f + 2*((∑ j ∈ W∪U,w x j)/2) at extra
        change edges T = edges (W∪U) + 2*(∑ j ∈ W∪U,w x j) at inc
        refine ⟨g,?_⟩
        change 2*cost T g + edges W ≤ edges T+2*cost W b
        omega
  obtain ⟨f,hf⟩ := more univ
  have allVerts : W ∪ univ = univ := eq_univ_of_forall (fun x => mem_union_right _ (mem_univ x))
  rw [allVerts] at hf
  exact ⟨f,hf⟩

lemma rootedAverage (w : Fin 25 → Fin 25 → ℕ) (sym : ∀ i j, w i j = w j i) :
    ∃ v : Fin 25, (∑ i,∑ j,w i j)^2 ≤ 625*(∑ i, w v i * ∑ j,w i j) := by
  let d (i : Fin 25) := ∑ j,w i j
  let p (v : Fin 25) := ∑ i, w v i*d i
  obtain ⟨v,_,hi⟩ := univ.exists_max_image p univ_nonempty
  have swap : (∑ v,p v) = ∑ i, d i^2 := by
    dsimp only [p]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [← sum_mul]
    have col : (∑ v,w v i)=d i := sum_congr rfl (fun j _ => sym j i)
    rw [col,pow_two]
  have avg : (∑ i, d i^2) ≤ 25*p v := by
    rw [← swap]
    simpa using (sum_le_sum (s:=univ) (g:=fun _ => p v) hi)
  have cs : (∑ i,d i)^2 ≤ 25*∑ i,d i^2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s:=univ) (f:=d)
  exact ⟨v,by change (∑ i, d i)^2 ≤ 625*p v; omega⟩


lemma cycleCut (G : SimpleGraph (Fin 25)) (g : Fin 25 → Fin 5)
    (maps : ∀ i j, G.Adj i j → g j=g i+1 ∨ g i=g j+1) :
    ∃ f : Fin 25 → Bool, (∑ i,∑ j,if G.Adj i j ∧ f i=f j then 1 else 0) ≤ (50:ℕ) := by
  classical
  let size (a : Fin 5) := (univ.filter (fun i : Fin 25 => g i=a)).card
  have total : (∑ a,size a) = 25 := by
    have eq := card_eq_sum_card_fiberwise (f:=g) (s:=univ) (t:=univ) (fun i _ => mem_univ (g i))
    simpa [size] using eq.symm
  have shift : (∑ a : Fin 5,size (a+1)) = ∑ a,size a :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin 5)) size
  obtain ⟨q,_,small⟩ := univ.exists_min_image (fun i : Fin 5 => size i+size (i+1)) univ_nonempty
  have sumBound := sum_le_sum (s:=univ) (f:=fun _ => size q+size (q+1)) small
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,sum_add_distrib,shift,total] at sumBound
  have pair : size q+size (q+1) ≤ 10 := by omega
  have product : size q * size (q+1) ≤ 25 := by
    have h : (size q:ℤ) + size (q+1) ≤ 10 := by exact_mod_cast pair
    have co : (0:ℤ) ≤ (size q:ℤ) + size (q+1) := by positivity
    have sq := mul_nonneg (sub_nonneg.mpr h) (show (0:ℤ) ≤ 10+((size q:ℤ)+size (q+1)) by omega)
    have res : (size q:ℤ)*size (q+1) ≤ 25 := by nlinarith [sq_nonneg ((size q:ℤ)-size (q+1))]
    exact_mod_cast res
  have colors : ∀ a : Fin 5, ∃ b : Fin 5 → Bool, ∀ i j : Fin 5,
      (j=i+1 ∨ i=j+1) → b i=b j → (i=a ∧ j=a+1) ∨ (i=a+1 ∧ j=a) := by decide +kernel
  obtain ⟨b,hb⟩ := colors q
  let tag (a : Fin 5) (i : Fin 25) : ℕ := if g i=a then 1 else 0
  have tags (a : Fin 5) : (∑ i,tag a i) = size a := by simp [tag,size]
  have box (a b : Fin 5) : (∑ i,∑ j,tag a i*tag b j) = size a*size b := by
    simp_rw [← mul_sum,tags,← sum_mul,tags]
  have bound (i j : Fin 25) :
      (if G.Adj i j ∧ b (g i)=b (g j) then (1:ℕ) else 0) ≤
      tag q i*tag (q+1) j+tag (q+1) i*tag q j := by
    by_cases h : G.Adj i j ∧ b (g i)=b (g j)
    · rw [if_pos h]
      rcases hb _ _ (maps i j h.1) h.2 with ⟨hi,hj⟩ | ⟨hi,hj⟩ <;> simp [tag,hi,hj]
    · simp [h]
  have sumBound := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ => bound i j))
  simp only [sum_add_distrib,box] at sumBound
  rw [mul_comm (size (q+1))] at sumBound
  exact ⟨fun i => b (g i),sumBound.trans (by omega)⟩

lemma rootedSums (w : Fin 25 → Fin 25 → ℕ) (sym : ∀ i j, w i j = w j i) (v : Fin 25) :
    (∑ i, ∑ j, w v i*w i j) + (∑ i, ∑ j, w v j*w i j) = 2*(∑ i, w v i * ∑ j,w i j) := by
  have left : (∑ i, ∑ j, w v i*w i j) = ∑ i, w v i * ∑ j,w i j :=
    sum_congr rfl (fun i _ => (mul_sum ..).symm)
  have right : (∑ i, ∑ j, w v j*w i j) = ∑ i, ∑ j, w v i*w i j := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    exact sum_congr rfl (fun j _ => by rw [sym j i])
  omega

lemma restrictedSum (W : Finset (Fin 25)) (w : Fin 25 → Fin 25 → ℕ) :
    (∑ i, ∑ j, if i∈W ∧ j∈W then w i j else 0) = ∑ i ∈ W,∑ j ∈ W,w i j := by
  calc
    _ = ∑ i, if i∈W then (∑ j,if j∈W then w i j else 0) else 0 := by
      apply sum_congr rfl; intro i _
      by_cases hi : i∈W <;> simp [hi]
    _ = _ := by simp_rw [← sum_filter,filter_mem_eq_inter]; simp

lemma finiteCases (one : H1) (two : H2) (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (dense : 200 ≤ ∑ i, ∑ j, if G.Adj i j then 1 else (0:ℕ)) :
    ∃ f : Fin 25 → Bool, (∑ i, ∑ j, if G.Adj i j ∧ f i=f j then 1 else 0) ≤ (50:ℕ) := by
  classical
  let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
  let d (i : Fin 25) := ∑ j,w i j
  let S := ∑ i,d i
  let P (v : Fin 25) := ∑ i,w v i*d i
  have sym (i j : Fin 25) : w i j = w j i := by simp only [w,G.adj_comm i j]
  have diag (i : Fin 25) : w i i = 0 := by simp [w]
  have triangle {v i j : Fin 25} (vi : G.Adj v i) (vj : G.Adj v j) (ij : G.Adj i j) : False :=
    tri _ (is3Clique_triple_iff.mpr ⟨vi,vj,ij⟩)
  by_contra! fail
  have bad (f : Fin 25 → Bool) : 51 ≤ ∑ i,∑ j,if f i=f j then w i j else 0 := by
    have hc := fail f
    have eq (i j : Fin 25) : (if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) =
        (if f i=f j then w i j else 0) := by by_cases h : f i=f j <;> simp [h,w]
    simp only [eq] at hc
    omega
  have noCycleMap : ¬ ∃ g : Fin 25 → Fin 5, ∀ i j, G.Adj i j → g j=g i+1 ∨ g i=g j+1 := by
    rintro ⟨g,hg⟩
    obtain ⟨f,hf⟩ := cycleCut G g hg
    exact (not_lt_of_ge hf) (fail f)
  have rooted (v : Fin 25) : 2*P v+51 ≤ S := by
    let b (i : Fin 25) := decide (G.Adj v i)
    have localEq (i j : Fin 25) : (if b i=b j then w i j else 0)+w v i*w i j+w v j*w i j=w i j := by
      by_cases ij : G.Adj i j <;> by_cases vi : G.Adj v i <;> by_cases vj : G.Adj v j <;>
        simp [w,b,ij,vi,vj] <;> exact (triangle vi vj ij).elim
    have total := sum_congr (s₁:=univ) rfl (fun i _ => sum_congr (s₁:=univ) rfl (fun j _ => localEq i j))
    simp only [sum_add_distrib] at total
    have both := rootedSums w sym v
    have hbad := bad b
    change _ = S at total
    change _ = 2*P v at both
    omega
  have induced (W : Finset (Fin 25)) (b : Fin 25 → Bool)
      (proper : ∀ i ∈ W, ∀ j ∈ W, G.Adj i j → b i ≠ b j) :
      (∑ i ∈ W,∑ j ∈ W,w i j)+102 ≤ S := by
    obtain ⟨f,hf⟩ := extendHalf w sym diag W b
    have zero : (∑ i ∈ W,∑ j ∈ W,if b i=b j then w i j else 0)=0 := by
      apply sum_eq_zero; intro i hi
      apply sum_eq_zero; intro j hj
      by_cases ij : G.Adj i j
      · simp [proper i hi j hj ij]
      · simp [w,ij]
    rw [zero] at hf
    have fbad := bad f
    change _ ≤ S+2*0 at hf
    omega
  obtain ⟨v,cs⟩ := rootedAverage w sym
  change S^2 ≤ 625*P v at cs
  have bound : S ≤ 248 := by
    have root := rooted v
    by_contra! above
    have sq : (0:ℤ) ≤ ((S:ℤ)-249)^2 := sq_nonneg _
    have rootZ : 2*(P v:ℤ)+51 ≤ S := by exact_mod_cast root
    have csZ : (S:ℤ)^2 ≤ 625*(P v:ℤ) := by exact_mod_cast cs
    have sZ : (249:ℤ) ≤ S := by exact_mod_cast above
    nlinarith
  have pent : ∃ a b c d e : Fin 25, G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e a := by
    by_contra! no
    let W := univ.filter (fun i => G.Adj v i ∨ ∃ u, G.Adj v u ∧ G.Adj u i)
    let b (i : Fin 25) := decide (G.Adj v i)
    have proper (i : Fin 25) (hi : i∈W) (j : Fin 25) (hj : j∈W) (ij : G.Adj i j) : b i ≠ b j := by
      by_cases vi : G.Adj v i <;> by_cases vj : G.Adj v j
      · exact (triangle vi vj ij).elim
      · simp [b,vi,vj]
      · simp [b,vi,vj]
      · obtain ⟨a,va,ai⟩ := (mem_filter.mp hi).2.resolve_left vi
        obtain ⟨b,vb,bj⟩ := (mem_filter.mp hj).2.resolve_left vj
        exact (no v a i j b va ai ij bj.symm vb.symm).elim
    have hits (i j : Fin 25) (vi : G.Adj v i) (ij : G.Adj i j) : i ∈ W ∧ j ∈ W :=
      ⟨mem_filter.mpr ⟨mem_univ _,Or.inl vi⟩,mem_filter.mpr ⟨mem_univ _,Or.inr ⟨i,vi,ij⟩⟩⟩
    have localLe (i j : Fin 25) : w v i*w i j+w v j*w i j ≤
        if i∈W ∧ j∈W then w i j else 0 := by
      by_cases ij : G.Adj i j
      · by_cases vi : G.Adj v i
        · have vj : ¬G.Adj v j := fun h => triangle vi h ij
          simp [w,vi,vj,ij,hits i j vi ij]
        · by_cases vj : G.Adj v j
          · have meet := hits j i vj ij.symm
            simp [w,vi,vj,ij,meet.1,meet.2]
          · simp [w,vi,vj]
      · simp [w,ij]
    have arc := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ => localLe i j))
    rw [restrictedSum] at arc
    simp only [sum_add_distrib] at arc
    rw [rootedSums w sym v] at arc
    have hc := induced W b proper
    change 2*P v ≤ _ at arc
    have comb : 2*P v + 102 ≤ S := by omega
    have wc : 2*(P v:ℤ)+102 ≤ S := by exact_mod_cast comb
    have cc : (S:ℤ)^2 ≤ 625*(P v:ℤ) := by exact_mod_cast cs
    nlinarith [sq_nonneg (4*(S:ℤ)-625)]
  obtain ⟨a,b,c,d',e,ab,bc,cd,de,ea⟩ := pent
  let split (u : Fin 25) := G.Adj u a ∨ G.Adj u b ∨ G.Adj u c ∨ G.Adj u d' ∨ G.Adj u e
  by_cases all : ∀ u, split u
  · obtain ⟨f,hf⟩ := one G tri dense bound noCycleMap rooted induced a b c d' e ab bc cd de ea all
    exact (not_lt_of_ge hf) (fail f)
  · push Not at all
    obtain ⟨u,miss⟩ := all
    have out : ¬G.Adj u a ∧ ¬G.Adj u b ∧ ¬G.Adj u c ∧ ¬G.Adj u d' ∧ ¬G.Adj u e := by simpa [split] using miss
    obtain ⟨f,hf⟩ := two G tri dense bound noCycleMap rooted induced a b c d' e ab bc cd de ea ⟨u,out⟩
    exact (not_lt_of_ge hf) (fail f)

theorem main : H1 → H2 → OMA.R_Erdos23_erdos_23_variants_n5_R2.H1 := by
  intro one two
  filter_upwards [eventually_ge_atTop (10:ℕ)] with r hr
  intro G tri density
  let S : ℕ := ∑ i,∑ j,if G.Adj i j then 1 else 0
  change 3197*(25*r)*(25*r-1) ≤ 10000*r^2*S at density
  have dense : 200 ≤ S := by
    by_contra! few
    have e : S ≤ 199 := by omega
    have a := Nat.mul_le_mul_left (3197*(25*r)) (show 249*r ≤ 10*(25*r-1) by omega)
    have b := Nat.mul_le_mul_left 10 density
    have c := Nat.mul_le_mul_left (10000*r^2) e
    nlinarith [show 0 < r^2 by positivity]
  obtain ⟨f,hf⟩ := finiteCases one two G tri dense
  refine ⟨fun i _ => f i,?_⟩
  have pulls : (∑ i : Fin 25,∑ j : Fin 25,∑ _a : Fin r,∑ _b : Fin r,
      if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) =
      r^2*(∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) := by
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,mul_sum,pow_two,mul_assoc]
  rw [pulls]
  nlinarith [Nat.mul_le_mul_left (r^2) hf]

end OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1
