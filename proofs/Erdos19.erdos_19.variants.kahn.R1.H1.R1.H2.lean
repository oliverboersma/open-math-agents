import OMAReductions.R_Erdos19_erdos_19_variants_kahn_R1_H1_R1
import Mathlib
/-! Finite regularization of a linear hypergraph. At each round take two
copies of the current hypergraph and join the two copies of every
deficient vertex. These new size-two edges form a matching. -/
open Finset
namespace Double19
variable {V : Type} [DecidableEq V]
def Linear (H : Finset (Finset V)) : Prop :=
  ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1
def Rank (H : Finset (Finset V)) (r : ℕ) : Prop :=
  ∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ r
def deg (H : Finset (Finset V)) (i : V) := (H.filter (fun A => i ∈ A)).card

def emb (b : Bool) : V ↪ Bool × V := ⟨(b,·),fun _ _ h => congrArg Prod.snd h⟩
def vertical (i : V) : Finset (Bool × V) := {(false,i),(true,i)}
omit [DecidableEq V] in
lemma in_copy (z : Bool × V) (b : Bool) (A : Finset V) :
    z ∈ A.map (emb b) ↔ z.1=b ∧ z.2 ∈ A := by
  constructor
  · rintro h
    obtain ⟨i,hi,rfl⟩ := mem_map.mp h
    exact ⟨rfl,hi⟩
  · obtain ⟨b',i⟩ := z
    rintro ⟨rfl,hi⟩
    exact mem_map.mpr ⟨i,hi,rfl⟩
lemma in_vertical (z : Bool × V) (i : V) : z ∈ vertical i ↔ z.2=i := by
  obtain ⟨b,x⟩ := z; cases b <;> simp [vertical]
lemma not_vertical (i : V) (b : Bool) (A : Finset V) : vertical i ≠ A.map (emb b) := by
  intro h
  have hi : (!b,i) ∈ vertical i := (in_vertical ..).2 rfl
  rw [h,in_copy] at hi
  cases b <;> simp at hi

lemma step [Fintype V] {H : Finset (Finset V)} {r D l : ℕ} (hr : 2≤r)
    (hH : Linear H) (hrank : Rank H r) (hl : l < D)
    (hd : ∀ i, l ≤ deg H i ∧ deg H i ≤ D) :
    ∃ G : Finset (Finset (Bool × V)), (∀ A ∈ H, A.map (emb false) ∈ G) ∧
      Linear G ∧ Rank G r ∧ ∀ z, l+1 ≤ deg G z ∧ deg G z ≤ D := by
  classical
  let S := univ.filter (fun i : V => deg H i < D)
  let C (b : Bool) := H.image (fun A => A.map (emb b))
  let G := C false ∪ C true ∪ S.image vertical
  have split (A : Finset (Bool × V)) : A ∈ G ↔
      (∃ b : Bool, ∃ B ∈ H, B.map (emb b)=A) ∨ (∃ i ∈ S, vertical i=A) := by
    simp only [G,C,mem_union,mem_image]
    constructor
    · rintro ((⟨B,h,e⟩|⟨B,h,e⟩)|h)
      · exact Or.inl ⟨false,B,h,e⟩
      · exact Or.inl ⟨true,B,h,e⟩
      · exact Or.inr h
    · rintro (⟨b,B,h,e⟩|h)
      · cases b
        · exact Or.inl (Or.inl ⟨_,h,e⟩)
        · exact Or.inl (Or.inr ⟨_,h,e⟩)
      · exact Or.inr h
  have mixed (b : Bool) (A : Finset V) (i : V) : (A.map (emb b) ∩ vertical i).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨hx1,hx2⟩ := mem_inter.mp hx
    obtain ⟨hy1,hy2⟩ := mem_inter.mp hy
    exact Prod.ext (((in_copy ..).mp hx1).1.trans ((in_copy ..).mp hy1).1.symm)
      (((in_vertical ..).mp hx2).trans ((in_vertical ..).mp hy2).symm)
  refine ⟨G,fun A hA => (split _).mpr (Or.inl ⟨false,A,hA,rfl⟩),?_,?_,?_⟩
  · intro A hA B hB hne
    rcases (split A).mp hA with ⟨a,A,hAA,rfl⟩|⟨i,_,rfl⟩ <;>
      rcases (split B).mp hB with ⟨b,B,hBB,rfl⟩|⟨j,_,rfl⟩
    · by_cases hab : a=b
      · subst b
        rw [←map_inter,card_map]
        exact hH _ hAA _ hBB (fun h => hne (congrArg (map (emb a)) h))
      · apply card_le_one.mpr
        intro x hx _ _
        obtain ⟨h1,h2⟩ := mem_inter.mp hx
        exact (hab (((in_copy ..).mp h1).1.symm.trans ((in_copy ..).mp h2).1)).elim
    · exact mixed _ _ _
    · rw [inter_comm]; exact mixed _ _ _
    · apply card_le_one.mpr
      intro x hx _ _
      obtain ⟨h1,h2⟩ := mem_inter.mp hx
      exact (hne (congrArg vertical (((in_vertical ..).mp h1).symm.trans ((in_vertical ..).mp h2)))).elim
  · intro A hA
    rcases (split A).mp hA with ⟨b,A,hAA,rfl⟩|⟨i,_,rfl⟩
    · simpa using hrank _ hAA
    · simpa [vertical] using hr
  · rintro ⟨b,i⟩
    let T := (H.filter (fun A => i ∈ A)).image (fun A => A.map (emb b))
    have cardT : T.card=deg H i := card_image_of_injective _ (map_injective _)
    have count : G.filter (fun A => (b,i) ∈ A) = (if i ∈ S then insert (vertical i) T else T) := by
      ext A
      simp only [mem_filter,split]
      constructor
      · rintro ⟨⟨c,E,he,rfl⟩|⟨j,hj,rfl⟩,h⟩
        · obtain ⟨hc,hi⟩ := (in_copy ..).mp h
          change b=c at hc; subst c
          have mem : E.map (emb b) ∈ T := mem_image.mpr ⟨_,mem_filter.mpr ⟨he,hi⟩,rfl⟩
          split <;> simp [mem]
        · obtain rfl : i=j := (in_vertical ..).mp h
          simp [hj]
      · have inc (h : A ∈ T) : ((∃ b, ∃ B ∈ H, B.map (emb b)=A) ∨ ∃ j ∈ S, vertical j=A) ∧ (b,i) ∈ A := by
          obtain ⟨E,hE,rfl⟩ := mem_image.mp h
          obtain ⟨hH,hi⟩ := mem_filter.mp hE
          exact ⟨Or.inl ⟨_,E,hH,rfl⟩,(in_copy ..).mpr ⟨rfl,hi⟩⟩
        split
        · rename_i h
          intro hA
          rcases mem_insert.mp hA with rfl | hA
          · exact ⟨Or.inr ⟨_,h,rfl⟩,(in_vertical ..).mpr rfl⟩
          · exact inc hA
        · exact inc
    have ne : vertical i ∉ T := by
      intro h; obtain ⟨E,_,e⟩ := mem_image.mp h; exact not_vertical _ _ _ e.symm
    have h := hd i
    unfold deg
    rw [count]
    by_cases hS : i ∈ S
    · rw [if_pos hS,card_insert_of_notMem ne,cardT]
      have : deg H i < D := (mem_filter.mp hS).2
      omega
    · rw [if_neg hS,cardT]
      have : ¬deg H i < D := fun hlt => hS (mem_filter.mpr ⟨mem_univ _,hlt⟩)
      omega
end Double19
namespace Double19
open Finset
lemma finish (r D n : ℕ) (hr : 2≤r) (H : Finset (Finset (Fin n))) (hH : Linear H)
    (hR : Rank H r) (hD : ∀ i, deg H i ≤ D) :
    ∃ n' : ℕ, ∃ f : Fin n ↪ Fin n', ∃ G : Finset (Finset (Fin n')),
      (∀ A ∈ H, A.map f ∈ G) ∧ Linear G ∧ Rank G r ∧ ∀ i, deg G i = D := by
  classical
  have stages (l : ℕ) (hl : l ≤ D) : ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (f : Fin n ↪ V) (G : Finset (Finset V)), (∀ A ∈ H, A.map f ∈ G) ∧
      Linear G ∧ Rank G r ∧ ∀ i, l ≤ deg G i ∧ deg G i ≤ D := by
    induction l with
    | zero =>
      exact ⟨Fin n,inferInstance,inferInstance,Function.Embedding.refl _,H,
        fun A h => by simpa using h,hH,hR,fun i => ⟨Nat.zero_le _,hD i⟩⟩
    | succ l ih =>
      obtain ⟨V,hV,dV,f,G,inc,lin,rk,ds⟩ := ih (by omega)
      let := hV
      let := dV
      obtain ⟨K,hK,lin',rk',ds'⟩ := step hr lin rk (by omega : l < D) ds
      refine ⟨Bool × V,inferInstance,inferInstance,f.trans (emb false),K,?_,lin',rk',ds'⟩
      intro A hA
      rw [←map_map]
      exact hK _ (inc A hA)
  obtain ⟨V,hV,dV,f,G,inc,lin,rk,ds⟩ := stages D le_rfl
  let := hV
  let := dV
  let e := Fintype.equivFin V
  let g := e.toEmbedding
  let K := G.map (mapEmbedding g).toEmbedding
  refine ⟨_,f.trans g,K,?_,?_,?_,?_⟩
  · intro A hA
    rw [←map_map]
    exact mem_map.mpr ⟨_,inc A hA,rfl⟩
  · intro A hA B hB hne
    obtain ⟨A,hAA,rfl⟩ := mem_map.mp hA
    obtain ⟨B,hBB,rfl⟩ := mem_map.mp hB
    change (A.map g ∩ B.map g).card ≤ 1
    rw [←map_inter,card_map]
    exact lin A hAA B hBB (fun eq => hne (congrArg _ eq))
  · intro A hA
    obtain ⟨A,hAA,rfl⟩ := mem_map.mp hA
    simpa [mapEmbedding_apply] using rk _ hAA
  · intro i
    have h := ds (e.symm i)
    have eq : deg G (e.symm i)=D := by omega
    rw [←eq]
    unfold deg
    rw [show K=G.map (mapEmbedding g).toEmbedding by rfl,filter_map,card_map]
    congr 1
    ext A
    simp [g,mem_map_equiv,Function.comp_def]
end Double19

theorem OMA.solution : OMA.R_Erdos19_erdos_19_variants_kahn_R1_H1_R1.H2 :=
  Double19.finish
