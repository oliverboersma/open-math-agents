import FormalConjectures.ErdosProblems.«210»
import Mathlib

/-!
A line with m points of a configuration and t points outside it gives at
least t(m−t+1) ordinary lines when m ≥ t. For a fixed outside point, the
m secants to the core are distinct. At most t−1 are blocked by a second
outside point. Ordinary lines counted from different outside points are
distinct. Compare Green and Tao, arXiv:1208.4714, Section 2.
-/

open Finset Filter EuclideanGeometry
open scoped Classical

namespace OMA.R_Erdos210_erdos_210_variants_green_tao_R1

/-- A secant from outside an affine subspace meets that subspace in at
most one point. -/
lemma unique_core (L : AffineSubspace ℝ ℝ²) {p a b : ℝ²}
    (hp : p ∉ L) (ha : a ∈ L) (hb : b ∈ L) (h : b ∈ line[ℝ,p,a]) : b = a := by
  by_contra hba
  have e := affineSpan_pair_eq_of_mem_of_mem_of_ne h
    (right_mem_affineSpan_pair ℝ p a) hba
  have hline : line[ℝ,b,a] ≤ L := affineSpan_pair_le_of_mem_of_mem hb ha
  rw [e] at hline
  exact hp (hline (left_mem_affineSpan_pair ℝ p a))

/-- Count all unblocked mixed secants before specializing the sizes. -/
lemma mixed (s : Finset ℝ²) (L : AffineSubspace ℝ ℝ²) :
    let A := s.filter (· ∈ L)
    let T := s.filter (· ∉ L)
    T.card * (A.card - (T.card-1)) ≤ (ordinaryLines s).card := by
  classical
  let A := s.filter (· ∈ L)
  let T := s.filter (· ∉ L)
  let lines (p : ℝ²) := A.image (fun a => line[ℝ,p,a])
  let blocked (p : ℝ²) := (T.erase p).image (fun q => line[ℝ,p,q])
  let G (p : ℝ²) := lines p \ blocked p
  have core {a : ℝ²} (ha : a ∈ A) : a ∈ s ∧ a ∈ L := mem_filter.mp ha
  have off {p : ℝ²} (hp : p ∈ T) : p ∈ s ∧ p ∉ L := mem_filter.mp hp
  have good {p : ℝ²} (hp : p ∈ T) {l : AffineSubspace ℝ ℝ²} (hl : l ∈ G p) :
      ∃ a ∈ A, line[ℝ,p,a] = l ∧ ∀ q ∈ T, q ∈ l → q = p := by
    obtain ⟨h₁,h₂⟩ := mem_sdiff.mp hl
    obtain ⟨a,ha,he⟩ := mem_image.mp h₁
    refine ⟨a,ha,he,?_⟩
    intro q hq hql
    by_contra hqp
    apply h₂
    refine mem_image.mpr ⟨q,mem_erase.mpr ⟨hqp,hq⟩,?_⟩
    rw [←he] at hql ⊢
    exact affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair ℝ p a) hql (Ne.symm hqp)
  have ordinary {p : ℝ²} (hp : p ∈ T) {l : AffineSubspace ℝ ℝ²} (hl : l ∈ G p) :
      l ∈ ordinaryLines s := by
    obtain ⟨a,ha,he,honly⟩ := good hp hl
    have hpa : p ≠ a := fun e => (off hp).2 (e ▸ (core ha).2)
    apply mem_ordinaryLines.mpr
    refine ⟨⟨p,(off hp).1,a,(core ha).1,hpa,he⟩,?_⟩
    have hpair : s.filter (· ∈ l) = {p,a} := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxs,hxl⟩ := mem_filter.mp hx
        by_cases h : x ∈ L
        · have eq := unique_core L (off hp).2 (core ha).2 h (he.symm ▸ hxl)
          simp [eq]
        · have eq := honly x (mem_filter.mpr ⟨hxs,h⟩) hxl
          simp [eq]
      · intro hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact mem_filter.mpr ⟨(off hp).1,he ▸ left_mem_affineSpan_pair ℝ x a⟩
        · obtain rfl := Finset.mem_singleton.mp hx
          exact mem_filter.mpr ⟨(core ha).1,he ▸ right_mem_affineSpan_pair ℝ p x⟩
    rw [hpair]; simp [hpa]
  have size (p : ℝ²) (hp : p ∈ T) : A.card - (T.card-1) ≤ (G p).card := by
    have hinj : Set.InjOn (fun a => line[ℝ,p,a]) (A : Set ℝ²) := by
      intro a ha b hb eq
      exact unique_core L (off hp).2 (core hb).2 (core ha).2
        (by change line[ℝ,p,a] = line[ℝ,p,b] at eq; rw [←eq]; exact right_mem_affineSpan_pair ℝ p a)
    have hs₁ : (lines p).card = A.card := card_image_of_injOn hinj
    have hs₂ : (blocked p).card ≤ T.card-1 := calc
      _ ≤ (T.erase p).card := card_image_le
      _ = _ := card_erase_of_mem hp
    have hl := le_card_sdiff (blocked p) (lines p)
    dsimp only [G]
    omega
  have disj : (T : Set ℝ²).PairwiseDisjoint G := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro l hl hl'
    obtain ⟨a,ha,he,honly⟩ := good hp hl
    obtain ⟨b,hb,he',_⟩ := good hq hl'
    exact hpq (honly q hq (he' ▸ left_mem_affineSpan_pair ℝ q b)).symm
  change T.card * (A.card - (T.card-1)) ≤ _
  calc
    _ = ∑ _p ∈ T, (A.card-(T.card-1)) := by simp
    _ ≤ ∑ p ∈ T,(G p).card := sum_le_sum size
    _ = (T.biUnion G).card := (card_biUnion disj).symm
    _ ≤ _ := card_le_card (fun l hl => by
      obtain ⟨p,hp,hG⟩ := mem_biUnion.mp hl
      exact ordinary hp hG)

/-- In the low-ordinary-line range, the structural classification supplies
a line containing at least floor(n/2) points. This is the line component
in the Böröczky families of Green and Tao's Theorem 2.4. -/
def H1 : Prop := ∃ C N : ℕ, ∀ s : Finset ℝ², N ≤ s.card →
  ¬ Collinear ℝ (s : Set ℝ²) → (ordinaryLines s).card+C ≤ s.card →
  ∃ a b : ℝ², ∃ p ∈ s, p ∉ line[ℝ,a,b] ∧ s.card ≤ 2*(s.filter (· ∈ line[ℝ,a,b])).card+1

/-- Only the odd case with exactly one more point outside the line than
on it remains. The odd estimate is the one supplied by Theorem 2.2. -/
def H2 : Prop := ∃ N : ℕ, ∀ (s : Finset ℝ²) (a b : ℝ²), N ≤ s.card →
  ¬ Collinear ℝ (s : Set ℝ²) → s.card = 2*(s.filter (· ∈ line[ℝ,a,b])).card+1 →
  3*(s.card/4) ≤ (ordinaryLines s).card

theorem main : H1 → H2 → type_of% @Erdos210.erdos_210.variants.green_tao := by
  rintro ⟨C,N,hstructure⟩ ⟨M,oddCase⟩
  apply Erdos210.green_tao_iff.mpr
  refine ⟨max 8 (max (2*C) (max N M)),by omega,?_⟩
  intro s hs hcol
  by_contra! few
  obtain ⟨a,b,p,hp,hoff,hsize⟩ := hstructure s (by omega) hcol (by omega)
  let L := line[ℝ,a,b]
  let A := s.filter (· ∈ L)
  let T := s.filter (· ∉ L)
  change s.card ≤ 2*A.card+1 at hsize
  have hsplit : A.card + T.card = s.card := card_filter_add_card_filter_not _
  have hT : 0<T.card := card_pos.mpr ⟨p,mem_filter.mpr ⟨hp,hoff⟩⟩
  by_cases hm : A.card < T.card
  · have heq : s.card = 2*A.card+1 := by omega
    have hodd := oddCase s a b (by omega) hcol heq
    omega
  · have hmix := mixed s L
    change T.card*(A.card-(T.card-1)) ≤ _ at hmix
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hm)
    have hsub : A.card-(T.card-1) = d+1 := by omega
    rw [hsub] at hmix
    have hp₁ := Nat.mul_le_mul_right d (show 1 ≤ T.card by omega)
    nlinarith only [hsplit,hd,hmix,hp₁,few]

end OMA.R_Erdos210_erdos_210_variants_green_tao_R1
