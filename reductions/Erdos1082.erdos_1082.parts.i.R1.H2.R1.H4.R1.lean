import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1

/-!
# The small planar distance obstruction

At four distances a critical configuration would have ten points. The diameter has an
independent five-point subset. In any bipartite cut every diameter edge is a bridge, so this
subset admits a one-point exchange preserving diameter independence. A three-distance subset
is handled by the extension step. Two two-distance five-point subsets sharing four points
are handled by the uniqueness step. The four-distance maximum of nine is due to Erdős and
Fishburn (Discrete Mathematics 160, 1996, Theorem 1).
-/

open EuclideanGeometry OMA.R_Erdos1082_erdos_1082_parts_i_R1
open OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1.Erdos1082Diameter

namespace OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1

/-- The previously verified one-, two-, and three-distance bounds. -/
def H1 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) → distinctDistances A≤3 → A.card/2≤distinctDistances A

/-- No diameter-free, three-distance set of five vertices extends to four distances on ten vertices. -/
def H2 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) → A.card=10 → distinctDistances A=4 →
    ∀ M∈distanceSet A, ∀ B⊆A, B.card=5 → (∀ a∈B, ∀ b∈B, dist a b<M) → distinctDistances B=3 → False

/-- Two diameter-free two-distance five-sets cannot differ by exactly one vertex. -/
def H3 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) → A.card=10 → distinctDistances A=4 →
    ∀ M∈distanceSet A, ∀ B⊆A, B.card=5 → (∀ a∈B, ∀ b∈B, dist a b<M) → distinctDistances B≤2 →
    ∀ w∈A, w∉B → ∀ v∈B, (∀ a∈insert w (B.erase v), ∀ b∈insert w (B.erase v), dist a b<M) →
    distinctDistances (insert w (B.erase v))≤2 → False

set_option maxHeartbeats 800000 in
lemma separated_edges_card {V : Type*} [DecidableEq V] (T : Finset V) (E : Finset (V×V))
    (hT : T.Nonempty) (hE : ∀ e∈E, e.1∈T ∧ e.2∈T)
    (hcut : ∀ e∈E, ∃ f : V→Bool, f e.1≠f e.2 ∧ ∀ t∈E,t≠e → f t.1=f t.2) :
    E.card<T.card := by
  classical
  suffices hall : ∀ n : ℕ, ∀ (T : Finset V) (E : Finset (V×V)), T.card=n → T.Nonempty →
      (∀ e∈E, e.1∈T ∧ e.2∈T) → (∀ e∈E, ∃ f : V→Bool, f e.1≠f e.2 ∧ ∀ t∈E, t≠e → f t.1=f t.2) →
      E.card<n from hall _ T E rfl hT hE hcut
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T E hsize hT hinc hcut
    by_cases hne : E.Nonempty
    · obtain ⟨e,he⟩ := hne
      obtain ⟨f,hd,hs⟩ := hcut e he
      let B (b : Bool) := T.filter fun x => f x=b
      let F (b : Bool) := E.filter fun t => f t.1=b ∧ f t.2=b
      have hn (b : Bool) : (B b).Nonempty := by
        by_cases h : f e.1=b
        · exact ⟨e.1,Finset.mem_filter.mpr ⟨(hinc e he).1,h⟩⟩
        · refine ⟨e.2,Finset.mem_filter.mpr ⟨(hinc e he).2,?_⟩⟩
          have aux (p q w : Bool) (h₁ : p≠q) (h₂ : p≠w) : q=w := by
            cases p <;> cases q <;> cases w <;> simp_all
          exact aux _ _ _ hd h
      have hsum : (B false).card+(B true).card=T.card := by
        have hh := Finset.card_filter_add_card_filter_not (s:=T) (fun x => f x=false)
        simpa [B] using hh
      have hb (b : Bool) : (F b).card<(B b).card := by
        apply ih (B b).card (by have h0 := Finset.card_pos.mpr (hn false); have h1 := Finset.card_pos.mpr (hn true); cases b <;> omega)
          (B b) (F b) rfl (hn b)
        · intro t ht
          obtain ⟨ht,h₁,h₂⟩ := Finset.mem_filter.mp ht
          exact ⟨Finset.mem_filter.mpr ⟨(hinc t ht).1,h₁⟩,Finset.mem_filter.mpr ⟨(hinc t ht).2,h₂⟩⟩
        · intro t ht
          obtain ⟨g,hg,hgt⟩ := hcut t (Finset.mem_filter.mp ht).1
          exact ⟨g,hg,fun w hw hh => hgt w (Finset.mem_filter.mp hw).1 hh⟩
      have hsub : E.erase e ⊆ F false ∪ F true := by
        intro t ht
        obtain ⟨ht,hte⟩ := Finset.mem_erase.mp ht
        have hh := hs t hte ht
        cases h : f t.1
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hte,h,hh.symm.trans h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hte,h,hh.symm.trans h⟩)
      have hbound := (Finset.card_le_card hsub).trans (Finset.card_union_le ..)
      have hecard := Finset.card_erase_add_one he
      have := hb true; have := hb false; omega
    · have := Finset.card_pos.mpr hT
      rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
      omega


lemma diameter_bipartite_cut (A : Finset ℝ²) (M : ℝ) (hM : 0<M)
    (hm : ∀ x y : A, dist x.1 y.1≤M) (χ : A→Bool) (a b : A) (ha : χ a=false) (hb : χ b=true)
    (hab : dist a.1 b.1=M) :
    ∃ f : A→Bool, f a≠f b ∧ ∀ i j : A, χ i=false → χ j=true → dist i.1 j.1=M → (i,j)≠(a,b) → f i=f j := by
  classical
  have ab : a≠b := by intro h; simp [h,hb] at ha
  by_cases hax : ∃ x : A, χ x=true ∧ x≠b ∧ dist a.1 x.1=M
  · by_cases hby : ∃ y : A, χ y=false ∧ y≠a ∧ dist b.1 y.1=M
    · obtain ⟨x,hx,hxb,hax⟩ := hax
      obtain ⟨y,hy,hya,hby⟩ := hby
      have hxa : x≠a := by intro h; simp [h,ha] at hx
      have hyb : y≠b := by intro h; simp [h,hb] at hy
      obtain ⟨s,hs⟩ := diameter_sides A M hM hm a b hab
      have hxy := (hs x y hxa hxb hya hyb).2 hax hby
      let f (v : A) := if v=a then !(s x) else if v=b then s x else xor (s v) (χ v)
      refine ⟨f,by simp [f,ab,ab.symm],?_⟩
      intro i j hi hj hdist hne
      have hib : i≠b := by intro h; simp [h,hb] at hi
      have hja : j≠a := by intro h; simp [h,ha] at hj
      by_cases hia : i=a
      · subst i
        have hjb : j≠b := by rintro rfl; exact hne rfl
        have hs' := (hs j y hja hjb hya hyb).2 hdist hby
        simp [f,hja,hjb,hj,hs',hxy]
      by_cases hjb : j=b
      · subst j
        have hs' := (hs x i hxa hxb hia hib).2 hax ((dist_comm b.1 i.1).trans hdist)
        simp [f,hia,hib,hi,ab.symm,hs']
      have hs' := (hs i j hia hib hja hjb).1 hdist
      simp only [f,if_neg hia,if_neg hib,if_neg hja,if_neg hjb,hi,hj]
      cases h₁ : s i <;> cases h₂ : s j <;> simp_all
    · let f (v : A) := decide (v=b)
      refine ⟨f,by simp [f,ab],?_⟩
      intro i j hi hj hdist hne
      have hib : i≠b := by intro h; simp [h,hb] at hi
      have hjb : j≠b := by
        rintro rfl
        exact hby ⟨i,hi,by rintro rfl; exact hne rfl,(dist_comm _ _).trans hdist⟩
      simp [f,hib,hjb]
  · let f (v : A) := decide (v=a)
    refine ⟨f,by simp [f,ab.symm],?_⟩
    intro i j hi hj hdist hne
    have hja : j≠a := by intro h; simp [h,ha] at hj
    have hia : i≠a := by
      rintro rfl
      exact hax ⟨j,hj,by rintro rfl; exact hne rfl,hdist⟩
    simp [f,hia,hja]

lemma bipartite_diameter_sparse (A : Finset ℝ²) (M : ℝ) (hM : 0<M) (hA : A.Nonempty)
    (hm : ∀ x y : A, dist x.1 y.1≤M) (χ : A→Bool) :
    ((A.attach ×ˢ A.attach).filter fun e : A×A => χ e.1=false ∧ χ e.2=true ∧ dist e.1.1 e.2.1=M).card<A.card := by
  classical
  rw [←Finset.card_attach (s:=A)]
  apply separated_edges_card A.attach _ (Finset.attach_nonempty_iff.mpr hA)
  · intro e he
    exact Finset.mem_product.mp (Finset.mem_filter.mp he).1
  · rintro ⟨a,b⟩ he
    obtain ⟨ha,hb,hab⟩ := (Finset.mem_filter.mp he).2
    obtain ⟨f,hf,hother⟩ := diameter_bipartite_cut A M hM hm χ a b ha hb hab
    refine ⟨f,hf,?_⟩
    rintro ⟨i,j⟩ ht hne
    obtain ⟨hi,hj,hd⟩ := (Finset.mem_filter.mp ht).2
    exact hother i j hi hj hd hne


lemma diameter_exchange (A B : Finset ℝ²) (M : ℝ) (hp : 0<M) (ha : B⊆A)
    (hm : ∀ x∈A, ∀ y∈A, dist x y≤M) (hb : ∀ x∈B, ∀ y∈B, dist x y<M)
    (hn : A.card = 2*B.card) (hpos : 0<B.card) :
    ∃ w∈A, w∉B ∧ ∃ v∈B, ∀ x∈insert w (B.erase v), ∀ y∈insert w (B.erase v), dist x y<M := by
  classical
  let C := A\B
  let E := (C ×ˢ B).filter fun e : ℝ²×ℝ² => dist e.1 e.2=M
  let χ (x : A) := decide (x.1∈B)
  let F := (A.attach ×ˢ A.attach).filter fun e : A×A => χ e.1=false ∧ χ e.2=true ∧ dist e.1.1 e.2.1=M
  have hnA : A.Nonempty := Finset.card_pos.mp (by omega)
  have hF : F.card<A.card := bipartite_diameter_sparse A M hp hnA (fun x y => hm x x.2 y y.2) χ
  have hEF : E⊆F.image (fun e : A×A => (e.1.1,e.2.1)) := by
    rintro ⟨x,y⟩ h
    obtain ⟨h,hd⟩ := Finset.mem_filter.mp h
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp h
    obtain ⟨hxA,hxB⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_image.mpr ⟨(⟨x,hxA⟩,⟨y,ha hy⟩),Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_attach ..,Finset.mem_attach ..⟩,by simp [χ,hxB,hy,hd]⟩,rfl⟩
  have hecard := (Finset.card_le_card hEF).trans (Finset.card_image_le)
  have hc : C.card=B.card := by dsimp [C]; rw [Finset.card_sdiff_of_subset ha]; omega
  let N (w : ℝ²) := B.filter fun b => dist w b=M
  have hlow : ∃ w∈C, (N w).card≤1 := by
    by_contra! hf
    have hsum := Finset.card_eq_sum_card_fiberwise (f:=Prod.fst) (s:=E) (t:=C)
      (fun e he => (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1)
    have hdeg (w : ℝ²) (hw : w∈C) : (N w).card≤(E.filter fun e => e.1=w).card := by
      let f (b : ℝ²) := (w,b)
      have h : (N w).image f⊆E.filter fun e => e.1=w := by
        intro e he
        obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp he
        obtain ⟨hb,hd⟩ := Finset.mem_filter.mp hb
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hw,hb⟩,hd⟩,rfl⟩
      have hcard : ((N w).image f).card=(N w).card :=
        Finset.card_image_of_injective _ (show Function.Injective f from fun x y e => congrArg Prod.snd e)
      exact hcard.ge.trans (Finset.card_le_card h)
    have hh := Finset.sum_le_sum (s:=C) (f:=fun _ => 2) (g:=fun w => (E.filter fun e => e.1=w).card)
      (fun w hw => (hf w hw).trans_le (hdeg w hw))
    simp only [Finset.sum_const,smul_eq_mul,←hsum] at hh
    omega
  obtain ⟨w,hw,hwN⟩ := hlow
  obtain ⟨hwA,hwB⟩ := Finset.mem_sdiff.mp hw
  have hex : ∃ v∈B, ∀ b∈N w, b=v := by
    by_cases hN : (N w).Nonempty
    · obtain ⟨v,hv⟩ := hN
      exact ⟨v,(Finset.mem_filter.mp hv).1,fun b h => Finset.card_le_one.mp hwN b h v hv⟩
    · obtain ⟨v,hv⟩ := Finset.card_pos.mp hpos
      exact ⟨v,hv,fun b h => False.elim (hN ⟨b,h⟩)⟩
  obtain ⟨v,hv,hvN⟩ := hex
  refine ⟨w,hwA,hwB,v,hv,?_⟩
  have hs (b : ℝ²) (hb' : b∈B.erase v) : dist w b<M := by
    obtain ⟨hne,hb'⟩ := Finset.mem_erase.mp hb'
    exact (hm w hwA b (ha hb')).lt_of_ne (fun he => hne (hvN b (Finset.mem_filter.mpr ⟨hb',he⟩)))
  intro x hx y hy
  rcases Finset.mem_insert.mp hx with ex|hx'
  · rcases Finset.mem_insert.mp hy with ey|hy'
    · simpa [ex,ey] using hp
    · simpa [ex] using hs y hy'
  · rcases Finset.mem_insert.mp hy with ey|hy'
    · rw [ey,dist_comm]; exact hs x hx'
    · exact hb _ (Finset.mem_erase.mp hx').2 _ (Finset.mem_erase.mp hy').2



theorem main : H1 → H2 → H3 → OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1.H4 := by
  classical
  intro hsmall hthree htwo A hn hcard hd
  by_cases hb : distinctDistances A≤3
  · have := hsmall A hn hb
    omega
  have hcount : distinctDistances A=4 := by omega
  have hsize : A.card=10 := by omega
  have hne : (distanceSet A).Nonempty := Finset.card_pos.mp (show 0<distinctDistances A by omega)
  let M := (distanceSet A).max' hne
  have hM : M∈distanceSet A := Finset.max'_mem ..
  have hmax (d : ℝ) (h : d∈distanceSet A) : d≤M := Finset.le_max' _ _ h
  have hpos : 0<M := by
    obtain ⟨⟨x,y⟩,hxy,he⟩ := Finset.mem_image.mp hM
    exact (dist_pos.mpr (Finset.mem_offDiag.mp hxy).2.2).trans_eq he
  have hbound (x : ℝ²) (hx : x∈A) (y : ℝ²) (hy : y∈A) : dist x y≤M := by
    by_cases he : x=y
    · simpa [he] using hpos.le
    · exact hmax _ (dist_mem hx hy he)
  obtain ⟨S,hSA,hs,hD⟩ := avoid_diameter A M hM hmax
  obtain ⟨B,hBS,hB⟩ := Finset.exists_subset_card_eq (s:=S) (show 5≤S.card by omega)
  have few (T : Finset ℝ²) (hTA : T⊆A) (hT : T.card=5) (hf : ∀ x∈T, ∀ y∈T, dist x y<M) : distinctDistances T≤2 := by
    have hsub : distanceSet T⊆(distanceSet A).erase M := by
      intro d h
      apply Finset.mem_erase.mpr
      refine ⟨?_,distanceSet_mono hTA h⟩
      obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hx,hy,_⟩ := Finset.mem_offDiag.mp hxy
      exact (hf x hx y hy).ne
    have bound := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hM] at bound
    change distinctDistances T≤distinctDistances A-1 at bound
    by_contra! hh
    exact hthree A hn hsize hcount M hM T hTA hT hf (by omega)
  have hBA := hBS.trans hSA
  have hdB (u : ℝ²) (hu : u∈B) (v : ℝ²) (hv : v∈B) : dist u v<M := hD u (hBS hu) v (hBS hv)
  obtain ⟨w,hw,hwB,v,hv,ht⟩ := diameter_exchange A B M hpos hBA hbound hdB (by omega) (by omega)
  let T := insert w (B.erase v)
  have hT : T.card=5 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem (fun h => hwB (Finset.mem_erase.mp h).2),Finset.card_erase_of_mem hv,hB]
  have hTA : T⊆A := by
    intro u hu
    rcases Finset.mem_insert.mp hu with he|h
    · exact he ▸ hw
    · exact hBA (Finset.mem_erase.mp h).2
  exact htwo A hn hsize hcount M hM B hBA hB hdB (few B hBA hB hdB) w hw hwB v hv ht (few T hTA hT ht)

end OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1
