import OMAReductions.R_Erdos876_erdos_876_variants_recip_sum_bounds_R1

/-!
Levine and O'Sullivan, Acta Arithmetica 34 (1977), Theorems 1 and 2,
obtain a counting inequality by adding an element to each initial subset
sum. We give a discrete dyadic level-set proof of the upper bound. In
a block above threshold t, either its early allowance exceeds t or every
other sufficiently dense block lies within a bounded number of indices.
The two geometric majorants sum explicitly. The finite decision tree
handles the elements up through 16.
-/

namespace LO876
open Finset Erdos876
open scoped Classical
noncomputable def F (A : Set ℕ) (n : ℕ) := (Icc 1 n).filter (· ∈ A)
noncomputable abbrev C (A : Set ℕ) (n : ℕ) := (F A n).card
lemma memF {A : Set ℕ} {n i : ℕ} : i∈F A n ↔ (1 ≤ i ∧ i≤n) ∧ i∈A := by simp [F]
lemma monoC (A : Set ℕ) : Monotone (C A) :=
  fun _ _ h => card_le_card (fun _ hx => memF.mpr ⟨⟨(memF.mp hx).1.1,(memF.mp hx).1.2.trans h⟩,(memF.mp hx).2⟩)

lemma no_sum {A : Set ℕ} (hf : IsSubsetSumFree A) {T : Finset ℕ} {a : ℕ} (ha : a∈A)
    (hTA : (T:Set ℕ) ⊆ A) (hc : 2 ≤ T.card) (he : ∑ t∈T,t=a) : False := by
  apply (hf a ha).2
  refine ⟨T,?_,he.symm⟩
  intro x hx
  refine ⟨hTA hx,?_⟩
  have hn : (T.erase x).Nonempty := card_pos.mp (by rw [card_erase_of_mem hx]; omega)
  have hpos : 0 < ∑ i∈T.erase x,i := sum_pos (fun i hi => (hf i (hTA (mem_of_mem_erase hi))).1) hn
  have hh := sum_erase_add T (fun i : ℕ => i) hx
  change x<a; omega

lemma counting (A : Set ℕ) (hf : IsSubsetSumFree A) (n y : ℕ) :
    (C A y+1)*C A n ≤ n+(C A y+1)*y := by
  classical
  let S := F A y
  let D := F A n
  let K := S ∪ {0}
  let P (s : ℕ) := S.filter (· ≤ s)
  have h0 : 0 ∉ S := by simp [S,F]
  have hK : K.card=S.card+1 := by simp [K,h0]
  have hps (s : ℕ) : P s ⊆ S := filter_subset _ _
  have strict {s t : ℕ} (hst : s<t) (ht : t∈K) : t∈P t \ P s := by
    have htn : t ≠ 0 := by omega
    have htS : t∈S := by simpa [K,htn] using ht
    simp [P,htS,hst.not_ge]
  have neq (s t q r : ℕ) (hlt : s<t) (ht : t∈K) (hq : q∈D \ P s) (hr : r∈D \ P t) :
      (∑ i∈P s,i)+q ≠ (∑ i∈P t,i)+r := by
    intro he
    let B := P t \ P s
    have hp : P s ⊆ P t := fun i hi => mem_filter.mpr ⟨(mem_filter.mp hi).1,(mem_filter.mp hi).2.trans hlt.le⟩
    have hsum := sum_sdiff (f:=fun i : ℕ => i) hp
    have hrB : r∉B := fun h => (mem_sdiff.mp hr).2 (mem_sdiff.mp h).1
    have htB : t∈B := strict hlt ht
    apply no_sum hf (T:=insert r B) ((memF.mp (mem_sdiff.mp hq).1).2)
    · intro i hi; rcases mem_insert.mp hi with rfl|hi
      · exact (memF.mp (mem_sdiff.mp hr).1).2
      · exact (memF.mp (hps t (mem_sdiff.mp hi).1)).2
    · rw [card_insert_of_notMem hrB]
      have := card_pos.mpr (show B.Nonempty from ⟨t,htB⟩); omega
    · rw [sum_insert hrB]
      change (∑ i∈B,i)+(∑ i∈P s,i)=∑ i∈P t,i at hsum
      omega
  have upper' : (K.sigma fun s => D \ P s).card ≤ (Icc 1 (n+∑ i∈S,i)).card := by
    apply card_le_card_of_injOn (fun v : (_ : ℕ) × ℕ => (∑ i∈P v.1,i)+v.2)
    · rintro ⟨s,q⟩ h
      have hq := memF.mp (mem_sdiff.mp (mem_sigma.mp h).2).1
      change (1 ≤ q ∧ q≤n) ∧ q∈A at hq
      have hh := sum_le_sum_of_subset_of_nonneg (hps s) (f:=fun i : ℕ => i) (fun _ _ _ => Nat.zero_le _)
      exact mem_Icc.mpr ⟨by dsimp; omega,by dsimp; omega⟩
    · rintro ⟨s,q⟩ hv ⟨t,r⟩ hw he
      obtain ⟨hs,hq⟩ := mem_sigma.mp hv
      obtain ⟨ht,hr⟩ := mem_sigma.mp hw
      change (∑ i∈P s,i)+q=(∑ i∈P t,i)+r at he
      rcases lt_trichotomy s t with hh|rfl|hh
      · exact (neq s t q r hh ht hq hr he).elim
      · have : q=r := Nat.add_left_cancel he; subst r; rfl
      · exact (neq t s r q hh hs hr hq he.symm).elim
  simp only [Nat.card_Icc,Nat.add_sub_cancel,card_sigma] at upper'
  have hd (s : ℕ) : D.card ≤ (D \ P s).card+(P s).card := by
    have h := card_le_card (show D ⊆ (D \ P s) ∪ P s by intro x hx; by_cases h : x∈P s <;> simp [hx,h])
    exact h.trans (card_union_le _ _)
  have hn := sum_le_sum (s:=K) (fun s _ => hd s)
  rw [sum_const,nsmul_eq_mul,hK,sum_add_distrib] at hn
  have countsum : ∑ s∈K,(P s).card = ∑ a∈S,(K.filter (a≤·)).card := by
    simp only [P,card_filter]
    rw [sum_comm]
  have hj (a : ℕ) (ha : a∈S) : (K.filter (a≤·)).card+a ≤ y+1 := by
    have ha' := memF.mp ha
    have inc : K.filter (a≤·) ⊆ Icc a y := by
      intro s hs
      obtain ⟨hsk,has⟩ := mem_filter.mp hs
      have hsn : s≠0 := by omega
      have hsS : s∈S := by simpa [K,hsn] using hsk
      exact mem_Icc.mpr ⟨has,(memF.mp hsS).1.2⟩
    have := card_le_card inc
    rw [Nat.card_Icc] at this
    omega
  have hsums := sum_le_sum hj
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,←countsum] at hsums
  have hsy : S.card ≤ y := by simpa [S,F] using card_le_card (filter_subset (·∈A) (Icc 1 y))
  change (S.card+1)*D.card ≤ n+(S.card+1)*y
  nlinarith only [upper',hn,hsums,hsy]
end LO876

namespace LO876
open Finset
open scoped Classical
-- Finite layer-cake comparison obtained by successively matching a largest
-- summand to one of the majorants that is at least as large.
lemma compareSum {ι κ : Type*} (a : ι → ℝ) (b : κ → ℝ) (S : Finset ι) (T : Finset κ)
    (hb : ∀ i∈T, 0 ≤ b i)
    (h : ∀ t : ℝ, 0<t → (S.filter (fun i => t≤a i)).card ≤ (T.filter (fun j => t≤b j)).card) :
    ∑ i∈S,a i ≤ ∑ j∈T,b j := by
  classical
  induction S using Finset.strongInduction generalizing T with
  | H S ih =>
    by_cases hn : S.Nonempty
    · obtain ⟨x,hx,hmax⟩ := exists_max_image S a hn
      by_cases hp : 0<a x
      · have hpos : 0 < (S.filter (fun i => a x ≤ a i)).card := card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,le_rfl⟩⟩
        obtain ⟨y,hy⟩ := card_pos.mp (hpos.trans_le (h _ hp))
        obtain ⟨hyT,hxy⟩ := mem_filter.mp hy
        have key := ih _ (erase_ssubset hx) (T.erase y) (fun j hj => hb j (mem_of_mem_erase hj)) (by
          intro t ht
          by_cases htx : t ≤ a x
          · simp only [filter_erase]
            rw [card_erase_of_mem (mem_filter.mpr ⟨hx,htx⟩),card_erase_of_mem (mem_filter.mpr ⟨hyT,htx.trans hxy⟩)]
            exact Nat.sub_le_sub_right (h t ht) 1
          · have he : ((S.erase x).filter (fun i => t≤a i))=∅ := by
              apply filter_eq_empty_iff.mpr
              intro i hi hti
              exact htx (hti.trans (hmax i (mem_of_mem_erase hi)))
            rw [he,card_empty]; exact Nat.zero_le _)
        rw [←sum_erase_add S a hx,←sum_erase_add T b hyT]
        exact add_le_add key hxy
      · exact (sum_nonpos fun i hi => (hmax i hi).trans (le_of_not_gt hp)).trans (sum_nonneg hb)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn,sum_empty]; exact sum_nonneg hb

lemma compareTwo (a b c : ℕ → ℝ) (N : ℕ) (hb : ∀ i,0 ≤ b i) (hc : ∀ i,0 ≤ c i)
    (h : ∀ t : ℝ, 0<t → ((range N).filter (fun i => t≤a i)).card ≤
      ((range N).filter (fun i => t≤b i)).card+((range N).filter (fun i => t≤c i)).card) :
    ∑ i∈range N,a i ≤ (∑ i∈range N,b i)+∑ i∈range N,c i := by
  classical
  let S := range N
  let f := Sum.elim b c
  have hh := compareSum a f S (S.disjSum S) (by rintro (i|j) _; exacts [hb i,hc j]) (by
    intro t ht
    have eq : (S.disjSum S).filter (fun i => t≤f i) = (S.filter (fun i => t≤b i)).disjSum (S.filter (fun i => t≤c i)) := by
      ext (i|j) <;> simp [f]
    rw [eq,card_disjSum]; exact h t ht)
  simpa [f,S,sum_disjSum] using hh
end LO876

namespace LO876
open Finset Erdos876
open scoped Classical
noncomputable def z (n : ℕ) : ℝ := (1/(n:ℝ)-1/(n+1:ℝ))
noncomputable def piece (A : Set ℕ) (l u : ℕ) : ℝ := ∑ n∈Ioc l u,(C A n:ℝ)*z n
def L (e : ℕ) := 16*2^e
noncomputable def beta (A : Set ℕ) (e : ℕ) := piece A (L e) (2*L e)
lemma Lpos (e : ℕ) : 0 < L e := by dsimp [L]; positivity
lemma Lsucc (e : ℕ) : L (e+1)=2*L e := by dsimp [L]; ring
lemma z_eq {n : ℕ} (hn : 0<n) : z n = 1/((n:ℝ)*(n+1)) := by
  have h : 0 < (n:ℝ) := by exact_mod_cast hn
  dsimp [z]; field_simp; ring
lemma zpos {n : ℕ} (hn : 0<n) : 0≤z n := by rw [z_eq hn]; positivity
lemma nz {n : ℕ} (hn : 0<n) : (n:ℝ)*z n=1/(n+1:ℝ) := by
  have h : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [z_eq hn]; field_simp
lemma telesc (l u : ℕ) (h : l≤u) : ∑ n∈Ioc l u,z n = 1/((l:ℝ)+1)-1/((u:ℝ)+1) := by
  induction u,h using Nat.le_induction with
  | base => simp
  | succ u hu ih => rw [sum_Ioc_succ_top hu,ih]; dsimp [z]; push_cast; ring
lemma zblock (l : ℕ) (hp : 0<l) : ∑ n∈Ioc l (2*l),z n ≤ 1/(2*(l:ℝ)) := by
  rw [telesc _ _ (by omega)]; push_cast
  have hl : (0:ℝ) < l := by exact_mod_cast hp
  field_simp; nlinarith
lemma harmonic (e : ℕ) : ∑ n∈Ioc (L e) (2*L e),1/((n:ℝ)+1) ≤ 5/6 := by
  let m := 8*2^e
  have hm : 0 < m := by dsimp [m]; positivity
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  have he : L e=2*m := by dsimp [L,m]; ring
  rw [he,show 2*(2*m)=4*m by ring,←sum_Ioc_consecutive (f:=fun n:ℕ => 1/((n:ℝ)+1)) (show 2*m≤3*m by omega) (show 3*m≤4*m by omega)]
  have part (k : ℕ) (hk : 0<k) : ∑ n∈Ioc (k*m) ((k+1)*m),1/((n:ℝ)+1) ≤ 1/(k:ℝ) := by
    have hk' : 0<(k:ℝ) := by exact_mod_cast hk
    calc _ ≤ ∑ _n∈Ioc (k*m) ((k+1)*m),1/((k:ℝ)*m) := by
            apply sum_le_sum; intro n hn
            have hlt : (k:ℝ)*m < n := by exact_mod_cast (mem_Ioc.mp hn).1
            exact one_div_le_one_div_of_le (by positivity) (by linarith)
         _ = _ := by simp [Nat.add_mul]; field_simp
  linarith only [part 2 (by decide),part 3 (by decide)]
lemma beta_nonneg (A : Set ℕ) (e : ℕ) : 0 ≤ beta A e := by
  unfold beta piece
  exact sum_nonneg fun n hn => mul_nonneg (Nat.cast_nonneg _) (zpos (by have := (mem_Ioc.mp hn).1; omega))
lemma beta_count (A : Set ℕ) (e : ℕ) : beta A e ≤ (C A (2*L e):ℝ)/(2*L e) := by
  unfold beta piece
  calc _ ≤ ∑ n∈Ioc (L e) (2*L e),(C A (2*L e):ℝ)*z n := by
          apply sum_le_sum; intro n hn
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast monoC A (mem_Ioc.mp hn).2) (zpos (by have := (mem_Ioc.mp hn).1; omega))
       _ ≤ _ := by rw [←mul_sum,div_eq_mul_inv,←one_div]; exact mul_le_mul_of_nonneg_left (zblock _ (Lpos e)) (Nat.cast_nonneg _)
lemma beta_bound (A : Set ℕ) (hf : IsSubsetSumFree A) (e y : ℕ) :
    beta A e ≤ (5/6)/((C A y:ℝ)+1)+(y:ℝ)/(2*L e) := by
  let K : ℝ := (C A y:ℝ)+1
  have hK : 0<K := by dsimp [K]; positivity
  have pt (n : ℕ) (hn : 0<n) : (C A n:ℝ)*z n ≤ (1/((n:ℝ)+1))/K + y*z n := by
    have h := counting A hf n y
    have h' : K*(C A n:ℝ) ≤ n+K*y := by dsimp [K]; exact_mod_cast h
    have hv : (C A n:ℝ) ≤ n/K+y := by
      rw [←sub_le_iff_le_add,le_div_iff₀ hK]; nlinarith only [h']
    have hh := mul_le_mul_of_nonneg_right hv (zpos hn)
    rw [←nz hn]; linarith only [hh,show ((n:ℝ)/K+y)*z n=(n*z n)/K+y*z n by ring]
  unfold beta piece
  calc _ ≤ ∑ n∈Ioc (L e) (2*L e),((1/((n:ℝ)+1))/K+(y:ℝ)*z n) :=
          sum_le_sum fun n hn => pt n (by have := (mem_Ioc.mp hn).1; omega)
       _ ≤ _ := by
         rw [sum_add_distrib,←sum_div,←mul_sum,div_eq_mul_one_div (y:ℝ)]
         exact add_le_add (div_le_div_of_nonneg_right (harmonic e) hK.le) (mul_le_mul_of_nonneg_left (zblock _ (Lpos e)) (Nat.cast_nonneg _))
end LO876

namespace LO876
open Erdos876 Finset
open scoped Classical
lemma abel (A : Set ℕ) (N : ℕ) :
    (∑ v∈F A N,1/(v:ℝ)) = piece A 0 N + (C A N:ℝ)/((N:ℝ)+1) := by
  induction N with
  | zero => simp [C,F,piece]
  | succ n ih =>
    have he : F A (n+1) = if n+1∈A then insert (n+1) (F A n) else F A n := by
      ext x
      split <;> rename_i h
      · simp only [memF,mem_insert]; constructor
        · rintro ⟨⟨hx,hu⟩,ha⟩; by_cases hxn : x=n+1
          · exact Or.inl hxn
          · exact Or.inr ⟨⟨hx,by omega⟩,ha⟩
        · rintro (rfl|h'); exact ⟨⟨by omega,le_rfl⟩,h⟩; exact ⟨⟨h'.1.1,by omega⟩,h'.2⟩
      · simp only [memF]; constructor
        · rintro ⟨⟨hx,hu⟩,ha⟩
          have : x≠n+1 := fun e => h (e ▸ ha); exact ⟨⟨hx,by omega⟩,ha⟩
        · rintro ⟨⟨hx,hu⟩,ha⟩; exact ⟨⟨hx,by omega⟩,ha⟩
    have hnot : n+1∉F A n := fun h => (Nat.not_succ_le_self n) (memF.mp h).1.2
    have hstep : piece A 0 (n+1) = piece A 0 n+(C A (n+1):ℝ)*z (n+1) :=
      sum_Ioc_succ_top (Nat.zero_le n) _
    rw [hstep]
    change _ = _ + ((F A (n+1)).card:ℝ)/_
    unfold C at *
    rw [he]
    split <;> simp only [card_insert_of_notMem hnot,sum_insert hnot,z,Nat.cast_add,Nat.cast_one,Nat.cast_succ]
    · rw [ih]; ring
    · rw [ih]; ring

lemma first (A : Set ℕ) : piece A 0 16 = ∑ v∈F A 16,((1:ℝ)/v-1/17) := by
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul,abel]
  change piece A 0 16 = piece A 0 16+((C A 16:ℝ)/(16+1))-((C A 16:ℝ)*(1/17))
  ring
lemma join_blocks (A : Set ℕ) (N : ℕ) : piece A 0 (L N)=piece A 0 16+∑ e∈range N,beta A e := by
  induction N with
  | zero => simp [L]
  | succ N ih =>
    rw [sum_range_succ,←add_assoc,←ih,Lsucc]
    exact (sum_Ioc_consecutive _ (Nat.zero_le _) (show L N≤2*L N by omega)).symm
end LO876

namespace LO876
open Finset Erdos876
inductive Certificate where
  | bound (y h : ℕ)
  | bad (p q : ℕ)
  | split (i : ℕ) (no yes : Certificate)
def verify : Certificate → Finset ℕ → Finset ℕ → Bool
  | .bound y h,lo,hi => decide ((∑ v∈hi,((1:ℚ)/v-1/17))+
      h*((5/6:ℚ)/(((lo.filter (·≤y)).card:ℚ)+1))+4/(2:ℚ)^h+y/16 ≤ 31/10)
  | .bad p q,lo,_ => decide (p≠q ∧ p∈lo ∧ q∈lo ∧ p+q∈lo)
  | .split i no yes,lo,hi => verify no lo (hi.erase i) && verify yes (insert i lo) hi

private def certificate : Certificate := (.split 1 (.split 2 (.split 3 (.split 4 (.split 5 (.split 6 (.bound 0 2) (.bound 6 2)) (.bound 5 2)) (.bound 4 2)) (.bound 3 2)) (.split 3 (.bound 2 3) (.bound 3 3))) (.split 2 (.split 3 (.split 4 (.split 5 (.split 6 (.bound 1 3) (.bound 6 3)) (.split 6 (.bound 5 3) (.bad 1 5))) (.split 5 (.split 6 (.bound 4 3) (.bound 6 3)) (.bad 1 4))) (.split 4 (.split 5 (.split 6 (.bound 3 3) (.split 7 (.bound 6 3) (.bad 1 6))) (.split 6 (.bound 5 4) (.bad 1 5))) (.bad 1 3))) (.split 3 (.split 4 (.split 5 (.split 6 (.split 7 (.bound 2 3) (.split 8 (.split 9 (.bound 2 3) (.bad 2 7)) (.bad 1 7))) (.split 7 (.split 8 (.split 9 (.bound 2 3) (.split 10 (.bound 2 3) (.bad 1 9))) (.bad 2 6)) (.bad 1 6))) (.split 6 (.split 7 (.split 8 (.split 9 (.bound 5 4) (.split 10 (.bound 5 4) (.bad 1 9))) (.split 9 (.split 10 (.bound 5 4) (.bad 2 8)) (.bad 1 8))) (.bad 2 5)) (.bad 1 5))) (.split 5 (.split 6 (.split 7 (.split 8 (.bound 4 4) (.split 9 (.split 10 (.bound 4 4) (.bad 2 8)) (.bad 1 8))) (.split 8 (.split 9 (.split 10 (.bound 4 4) (.split 11 (.bound 4 4) (.bad 1 10))) (.bad 2 7)) (.bad 1 7))) (.bad 2 4)) (.bad 1 4))) (.bad 1 2))))
lemma prefix_bound (A : Set ℕ) (hf : IsSubsetSumFree A) :
    ∃ y h : ℕ, (∑ v∈F A 16,((1:ℝ)/v-1/17))+
      h*((5/6:ℝ)/((C A y:ℝ)+1))+4/(2:ℝ)^h+y/16 ≤ 31/10 := by
  classical
  let S := F A 16
  have sound (c : Certificate) (lo hi : Finset ℕ) (hl : lo⊆S) (hu : S⊆hi) (hcap : hi ⊆ Icc 1 16)
      (hc : verify c lo hi=true) :
      ∃ y h : ℕ, (∑ v∈S,((1:ℝ)/v-1/17))+h*((5/6:ℝ)/((C A y:ℝ)+1))+4/(2:ℝ)^h+y/16 ≤ 31/10 := by
    induction c generalizing lo hi with
    | split i no yes ih0 ih1 =>
      change (_ && _)=true at hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨h0,h1⟩ := hc
      by_cases hz : i∈S
      · exact ih1 _ _ (insert_subset hz hl) hu hcap h1
      · exact ih0 _ _ hl (show S ⊆ hi.erase i by
          intro v hv; exact mem_erase.mpr ⟨fun (e : v=i) => hz (e ▸ hv),hu hv⟩)
          ((erase_subset ..).trans hcap) h0
    | bad p q =>
      have hh : p≠q ∧ p∈lo ∧ q∈lo ∧ p+q∈lo := of_decide_eq_true hc
      obtain ⟨hpq,hp,hq,hs⟩ := hh
      have pA := (memF.mp (hl hp)).2
      have qA := (memF.mp (hl hq)).2
      have sA := (memF.mp (hl hs)).2
      exact (no_sum hf (T:={p,q}) sA (by intro v hv; simp at hv; rcases hv with rfl|rfl <;> assumption)
        (by simp [hpq]) (by simp [hpq])).elim
    | bound y h =>
      let k := (lo.filter (·≤y)).card
      have hh : (∑ v∈hi,((1:ℚ)/v-1/17))+h*((5/6:ℚ)/((k:ℚ)+1))+4/(2:ℚ)^h+y/16 ≤ 31/10 := of_decide_eq_true hc
      have hh' : (∑ v∈hi,((1:ℝ)/v-1/17))+h*((5/6:ℝ)/((k:ℝ)+1))+4/(2:ℝ)^h+y/16 ≤ 31/10 := by
        have lift : ((_ : ℚ):ℝ) ≤ ((31/10:ℚ):ℝ) := Rat.cast_le.mpr hh
        push_cast at lift
        exact lift
      have hk : k ≤ C A y := card_le_card (show lo.filter (·≤y) ⊆ F A y by
        intro v hv
        obtain ⟨hv,hy⟩ := mem_filter.mp hv
        have hh := memF.mp (hl hv)
        exact memF.mpr ⟨⟨hh.1.1,hy⟩,hh.2⟩)
      have hf' := sum_le_sum_of_subset_of_nonneg (f:=fun v : ℕ => (1:ℝ)/v-1/17) hu (by
        intro i hi _
        obtain ⟨hmin,hmax⟩ := mem_Icc.mp (hcap hi)
        have h0 : (0:ℝ) < i := by exact_mod_cast (show 0 < i from hmin)
        exact sub_nonneg.mpr (one_div_le_one_div_of_le h0 (by exact_mod_cast (show i≤17 by omega))))
      have hdiv := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤5/6) (by positivity : (0:ℝ)<(k:ℝ)+1)
        (show (k:ℝ)+1 ≤ (C A y:ℝ)+1 by exact_mod_cast Nat.add_le_add_right hk 1)
      exact ⟨y,h,by linarith only [hh',hf',mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg h)]⟩
  exact sound certificate ∅ (Icc 1 16) (empty_subset _) (filter_subset _ _) (Subset.rfl) (by decide +kernel)
end LO876

namespace LO876
open Finset Erdos876
open scoped Classical
noncomputable def reserve (e : ℕ) : ℝ := (if e%2=0 then 7/8 else 5/8)/(2:ℝ)^(e/2)
noncomputable def early (e : ℕ) := reserve e - reserve (e+1)
lemma early_spec (e : ℕ) : 0 ≤ early e ∧ 2 ≤ (2*(L e:ℝ))*(early e)^2 := by
  let j := e/2
  have hj : 0 < (2:ℝ)^j := by positivity
  have he : e=2*j ∨ e=2*j+1 := by dsimp [j]; omega
  rcases he with he|he <;> rw [he] <;> simp [early,reserve,L,pow_add,pow_mul,
    show (2*j+1)/2=j by omega,show (2*j+1+1)/2=j+1 by omega,
    show (2*j+1)%2=1 by omega,show (2*j+1+1)%2=0 by omega]
  all_goals rw [show (4:ℝ)^j = ((2:ℝ)^j)^2 by rw [←pow_mul, mul_comm j 2,pow_mul]; norm_num] <;>
    constructor <;> field_simp <;> nlinarith [sq_pos_of_pos hj]
lemma early_sum (N : ℕ) : ∑ e∈range N,early e ≤ 7/8 := by
  have h : (∑ e∈range N,early e)+reserve N=reserve 0 := by
    induction N with
    | zero => simp
    | succ n ih => rw [sum_range_succ,show early n=reserve n-reserve (n+1) from rfl]; linarith
  have hp : 0 ≤ reserve N := by dsimp [reserve]; split <;> positivity
  rw [show reserve 0=7/8 by norm_num [reserve]] at h; linarith

lemma geom (N : ℕ) : ∑ e∈range N,1/(2:ℝ)^e = 2-2/(2:ℝ)^N := by
  induction N with
  | zero => norm_num
  | succ N ih => rw [sum_range_succ,ih,pow_succ]; ring

lemma late_sum (U : ℝ) (hU : 0≤U) (N h : ℕ) :
    ∑ e∈range N,min U (2/(2:ℝ)^e) ≤ h*U+4/(2:ℝ)^h := by
  by_cases hN : N≤h
  · apply (sum_le_sum (s:=range N) (fun e _ => min_le_left U (2/(2:ℝ)^e))).trans
    simp only [sum_const,card_range,nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hN) hU).trans (le_add_of_nonneg_right (by positivity))
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (by omega : h≤N)
  rw [hk,sum_range_add]
  apply add_le_add
  · simpa using sum_le_sum (s:=range h) (fun e _ => min_le_left U (2/(2:ℝ)^e))
  · apply (sum_le_sum (s:=range k) (fun e _ => min_le_right U (2/(2:ℝ)^(h+e)))).trans
    simp only [pow_add,div_mul_eq_div_div,div_eq_mul_one_div (2/(2:ℝ)^h)]
    rw [←mul_sum,geom]
    have hg := mul_le_mul_of_nonneg_left (show 2-2/(2:ℝ)^k ≤ 2 by exact sub_le_self _ (by positivity)) (by positivity : 0≤2/(2:ℝ)^h)
    linarith only [hg,show (2/(2:ℝ)^h)*2=4/(2:ℝ)^h by ring]

lemma high_gap (A : Set ℕ) (hf : IsSubsetSumFree A) {r s : ℕ} (hrs : r ≤ s) {t : ℝ}
    (ht : 0<t) (he : early r < t) (hr : t≤beta A r) (hs : t≤beta A s) :
    t ≤ 2/(2:ℝ)^(s-r) := by
  let d := 2*L r
  have hd : 0<(d:ℝ) := by dsimp [d,L]; positivity
  have hcr := hr.trans (beta_count A r)
  have hcr' : t*(d:ℝ) ≤ C A d := (le_div_iff₀ hd).mp (by simpa [d] using hcr)
  have hsq := pow_le_pow_left₀ (early_spec r).1 he.le 2
  have hdr : 2 ≤ (d:ℝ)*t^2 := by
    have hd' : 2 ≤ (d:ℝ)*(early r)^2 := by simpa [d] using (early_spec r).2
    exact hd'.trans (mul_le_mul_of_nonneg_left hsq hd.le)
  have hfirst : (5/6:ℝ)/((C A d:ℝ)+1) ≤ t/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hcr' ht.le,hdr,ht]
  have hsec : (d:ℝ)/(2*(L s:ℝ))=1/(2:ℝ)^(s-r) := by
    have hh : s=r+(s-r) := by omega
    have hp : (2:ℝ)^s=2^r*2^(s-r) := by conv_lhs => rw [hh,pow_add]
    dsimp [d,L]; push_cast; rw [hp]; field_simp
  have h := hs.trans (beta_bound A hf s d)
  rw [hsec] at h
  rw [div_eq_mul_one_div 2]
  linarith only [h,hfirst]

theorem tail (A : Set ℕ) (hf : IsSubsetSumFree A) (N y h : ℕ) :
    ∑ e∈range N,beta A e ≤ (7/8:ℝ)+h*((5/6)/((C A y:ℝ)+1))+4/(2:ℝ)^h+y/16 := by
  classical
  let U : ℝ := (5/6)/((C A y:ℝ)+1)
  let b (i : ℕ) := min U (beta A i)
  let c (i : ℕ) := min U (2/(2:ℝ)^i)
  have hU : 0≤U := by dsimp [U]; positivity
  have hh := compareTwo b early c N (fun i => (early_spec i).1) (fun i => le_min hU (by positivity)) (by
    intro t ht
    let S := (range N).filter (fun i => t≤b i)
    let E := (range N).filter (fun i => t≤early i)
    let G := S \ E
    have hpart : S.card ≤ E.card+G.card := by
      have := card_le_card (show S ⊆ E ∪ G by intro i hi; by_cases h : i∈E <;> simp [G,hi,h])
      exact this.trans (card_union_le ..)
    apply hpart.trans (Nat.add_le_add_left _ _)
    by_cases hn : G.Nonempty
    · let r := G.min' hn
      let s := G.max' hn
      have hv {i} (hi : i∈G) : i<N ∧ early i<t ∧ t≤U ∧ t≤beta A i := by
        obtain ⟨hiS,hiE⟩ := mem_sdiff.mp hi
        obtain ⟨hir,hb⟩ := mem_filter.mp hiS
        exact ⟨mem_range.mp hir,lt_of_not_ge (fun h => hiE (mem_filter.mpr ⟨hir,h⟩)),(le_min_iff.mp hb).1,(le_min_iff.mp hb).2⟩
      have hr := hv (G.min'_mem hn)
      have hs := hv (G.max'_mem hn)
      have hrs : r ≤ s := G.min'_le s (G.max'_mem hn)
      have hgap := high_gap A hf hrs ht hr.2.1 hr.2.2.2 hs.2.2.2
      have hcnum : G.card ≤ s+1-r := by
        simpa using card_le_card (show G ⊆ Icc r s from fun i hi => mem_Icc.mpr ⟨G.min'_le i hi,G.le_max' i hi⟩)
      have sub : range G.card ⊆ (range N).filter (fun i => t≤c i) := by
        intro i hi
        have hi' := mem_range.mp hi
        have hN := hs.1
        have hid : i ≤ s-r := by omega
        exact mem_filter.mpr ⟨mem_range.mpr (by omega),le_min hr.2.2.1 (hgap.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_right₀ (by norm_num) hid)))⟩
      simpa using card_le_card sub
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn])
  have bound (e : ℕ) : beta A e ≤ b e+(y:ℝ)/(2*L e) := by
    dsimp [b]; rw [←min_add_add_right]
    exact le_min (beta_bound A hf e y) (le_add_of_nonneg_right (by positivity))
  have hh' := sum_le_sum (s:=range N) (fun e _ => bound e)
  rw [sum_add_distrib] at hh'
  have hy : (∑ e∈range N,(y:ℝ)/(2*L e)) ≤ y/16 := by
    have eq (i : ℕ) : (y:ℝ)/(2*L i)=((y:ℝ)/32)*(1/(2:ℝ)^i) := by dsimp [L]; push_cast; ring
    simp_rw [eq]; rw [←mul_sum,geom]
    have hg := mul_le_mul_of_nonneg_left (show 2-2/(2:ℝ)^N ≤ 2 by exact sub_le_self _ (by positivity)) (by positivity : 0≤(y:ℝ)/32)
    linarith
  have hx := late_sum U hU N h
  change (∑ i∈range N,c i) ≤ h*U+4/(2:ℝ)^h at hx
  change _ ≤ 7/8+h*U+4/(2:ℝ)^h+y/16
  linarith only [early_sum N,hx,hh,hh',hy]
end LO876

namespace LO876
open Finset Erdos876
open scoped Classical
theorem finite_bound (S : Finset ℕ) (hf : IsSubsetSumFree (S:Set ℕ)) :
    ∑ a∈S,1/(a:ℝ) ≤ 399/100 := by
  classical
  let N := (∑ a∈S,a)+100*S.card+1
  have hN : N ≤ L N := by
    have h := (Nat.lt_two_pow_self (n:=N)).le
    dsimp [L]; omega
  have eq : F (S:Set ℕ) (L N)=S := by
    ext a
    rw [memF]
    constructor
    · exact fun h => h.2
    · intro ha
      have h := single_le_sum (s:=S) (f:=fun i : ℕ => i) (fun _ _ => Nat.zero_le _) ha
      refine ⟨⟨(hf a ha).1,?_⟩,ha⟩
      exact (show a≤N by dsimp [N]; omega).trans hN
  have hcount : 100*S.card ≤ L N := (show 100*S.card ≤ N by dsimp [N]; omega).trans hN
  have herr : (S.card:ℝ)/((L N:ℝ)+1) ≤ 1/100 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h : 100*(S.card:ℝ) ≤ L N := by exact_mod_cast hcount
    linarith
  obtain ⟨y,h,hp⟩ := prefix_bound (S:Set ℕ) hf
  have ht := tail (S:Set ℕ) hf N y h
  have he := abel (S:Set ℕ) (L N)
  rw [join_blocks,first] at he
  unfold C at he
  rw [eq] at he
  linarith only [he,hp,ht,herr]

theorem main : ∃ c : ℝ, c<4 ∧ ∀ A : Set ℕ, A.Infinite → IsSubsetSumFree A →
    ∀ s : ℝ, HasSum (fun a : A => (1:ℝ)/(a:ℕ)) s → s≤c := by
  classical
  refine ⟨399/100,by norm_num,?_⟩
  intro A _ hf s hs
  apply le_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro u
  let S := u.image (fun a : A => a.val)
  have inc : (S:Set ℕ) ⊆ A := by rintro _ hv; obtain ⟨a,_,rfl⟩ := mem_image.mp hv; exact a.property
  have free : IsSubsetSumFree (S:Set ℕ) := by
    intro a ha
    refine ⟨(hf a (inc ha)).1,fun bad => (hf a (inc ha)).2 ?_⟩
    exact subsetSums_mono (Set.inter_subset_inter_left _ inc) bad
  have H := finite_bound S free
  simpa [S,sum_image (f:=fun a : A => a.val) Subtype.val_injective.injOn] using H
end LO876

theorem OMA.solution : OMA.R_Erdos876_erdos_876_variants_recip_sum_bounds_R1.H1 := LO876.main
