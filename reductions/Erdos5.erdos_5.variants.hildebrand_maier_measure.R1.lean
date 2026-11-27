import FormalConjectures.ErdosProblems.«5»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_measure_R1

open Filter MeasureTheory Real Set Erdos5
open scoped Topology

-- Choose a point near the left end of the remaining set. Its forbidden
-- successors cost at most one translated copy of the difference set and ε.
private lemma selectPoint {T ε : ℝ} {S A : Set ℝ} (he : 0 < ε)
    (ha : A ⊆ Icc 0 T) (hp : 0 < volume.real A) :
    ∃ x ∈ A, ∃ B ⊆ A, (∀ y ∈ B, x < y ∧ y-x ∉ S) ∧
      volume.real A - ε - volume.real (S ∩ Icc 0 T) ≤ volume.real B := by
  have hn : A.Nonempty := by
    by_contra! h
    simp [h] at hp
  have hb : BddBelow A := ⟨0, fun y hy => (ha hy).1⟩
  obtain ⟨x,hx,hsmall⟩ := exists_lt_of_csInf_lt hn (show sInf A < sInf A + ε by linarith)
  let I := Icc (sInf A) x
  let D := (fun y : ℝ => y + -x) ⁻¹' (S ∩ Icc 0 T)
  let B := (A \ I) \ D
  have hμ : volume D = volume (S ∩ Icc 0 T) := measure_preimage_add_right _ _ _
  have hD : volume D ≠ ⊤ := hμ ▸ measure_ne_top_of_subset inter_subset_right (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hI : volume I ≠ ⊤ := by dsimp [I]; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hi : volume.real I ≤ ε := by
    rw [Real.volume_real_Icc_of_le (csInf_le hb hx)]
    linarith
  refine ⟨x,hx,B,fun _ hy => hy.1.1,?_,?_⟩
  · intro y hy
    obtain ⟨⟨hya,hyi⟩,hyd⟩ := hy
    have hxy : x < y := lt_of_not_ge fun h => hyi ⟨csInf_le hb hya,h⟩
    refine ⟨hxy,fun hs => hyd ?_⟩
    change y + -x ∈ S ∩ Icc 0 T
    rw [← sub_eq_add_neg]
    exact ⟨hs,sub_nonneg.mpr hxy.le,by linarith [(ha hx).1,(ha hya).2]⟩
  · have h₁ := le_measureReal_sdiff (s₁ := A) hI
    have h₂ := le_measureReal_sdiff (s₁ := A \ I) hD
    have hr : volume.real D = volume.real (S ∩ Icc 0 T) := congrArg ENNReal.toReal hμ
    dsimp [B]
    linarith

private lemma pack {S : Set ℝ} {T ε : ℝ} (he : 0 < ε) (n : ℕ) {A : Set ℝ}
    (ha : A ⊆ Icc 0 T)
    (hp : n * (ε + volume.real (S ∩ Icc 0 T)) < volume.real A) :
    ∃ β : Fin (n+1) → ℝ, (∀ i, β i ∈ A) ∧
      ∀ i j, i < j → β i < β j ∧ β j - β i ∉ S := by
  induction n generalizing A with
  | zero =>
    obtain ⟨x,hx⟩ : A.Nonempty := by
      by_contra! h
      simp [h] at hp
    exact ⟨fun _ => x,fun _ => hx,fun i j hij => by omega⟩
  | succ n ih =>
    have hμ := measureReal_nonneg (μ := volume) (s := S ∩ Icc 0 T)
    have hpos : 0 < volume.real A := (mul_nonneg (Nat.cast_nonneg _) (by linarith)).trans_lt hp
    obtain ⟨x,hx,B,hBA,avoid,hB⟩ := selectPoint (S := S) he ha hpos
    obtain ⟨β,hβ,havoid⟩ := ih (hBA.trans ha) (by push_cast at hp; nlinarith)
    refine ⟨Fin.cons x β,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun t => ?_) i
      · exact hx
      · exact hBA (hβ t)
    · intro i j
      refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
      · intro h; exact (lt_irrefl _ h).elim
      · intro _; exact avoid _ (hβ b)
      · intro h; exact (Fin.not_lt_zero _ h).elim
      · intro h; exact havoid a b (Fin.succ_lt_succ_iff.mp h)

-- A finite-shift sieve can choose a different pair at each precision.
def H1 : Prop := ∃ m : ℕ, 0 < m ∧ ∀ β : Fin (m+1) → ℝ,
    (∀ i, 0 ≤ β i) → StrictMono β → ∀ ε > (0:ℝ), ∀ N : ℕ,
    ∃ n ≥ N, ∃ i j, i < j ∧
      |(primeGap n:ℝ) / log (Nat.nth Nat.Prime n) - (β j - β i)| < ε

-- Chebyshev bounds suffice for the change of normalization.
def H2 : Prop := Tendsto (fun n : ℕ => log (Nat.nth Nat.Prime n) / log n) atTop (𝓝 1)

lemma findLimit {m : ℕ} (β : Fin (m+1) → ℝ)
    (h : ∀ ε > (0:ℝ), ∀ N : ℕ, ∃ n ≥ N, ∃ i j, i < j ∧
      |(primeGap n:ℝ) / log (Nat.nth Nat.Prime n) - (β j - β i)| < ε) (scale : H2) :
    ∃ i j, i < j ∧ β j - β i ∈ limitPointSet := by
  let g (n : ℕ) := (primeGap n : ℝ) / log (Nat.nth Nat.Prime n)
  let S : Finset ℝ := (Finset.univ.filter (fun p : Fin (m+1) × Fin (m+1) => p.1<p.2)).image
    (fun p => β p.2-β p.1)
  have hit (k : ℕ) : ∃ z ∈ S, ∃ n ≥ k, |g n-z| < 1/((k:ℝ)+1) := by
    obtain ⟨n,hn,i,j,hij,hg⟩ := h (1/((k:ℝ)+1)) (by positivity) k
    exact ⟨_,Finset.mem_image.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩,rfl⟩,n,hn,hg⟩
  obtain ⟨z,hz,hfreq⟩ := (frequently_exists_finset (l := (atTop : Filter ℕ)) S).mp
    (Eventually.of_forall hit).frequently
  obtain ⟨p,hp,hz'⟩ := Finset.mem_image.mp hz
  have cluster : MapClusterPt z atTop g := by
    rw [Metric.nhds_basis_ball.mapClusterPt_iff_frequently]
    intro ε hε
    rw [frequently_atTop]
    intro N
    have hs := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hε
    obtain ⟨k,⟨n,hn,hg⟩,hk,hnk⟩ := (hfreq.and_eventually (hs.and (eventually_ge_atTop N))).exists
    exact ⟨n,hnk.trans hn,by simpa [Metric.mem_ball,Real.dist_eq] using hg.trans hk⟩
  obtain ⟨n,hn,hlim⟩ := cluster.tendsto_subseq
  refine ⟨p.1,p.2,(Finset.mem_filter.mp hp).2,?_⟩
  rw [hz']
  apply (mem_limitPointSet_iff _).2
  refine ⟨n,hn,?_⟩
  have hh := hlim.mul (scale.comp hn.tendsto_atTop)
  rw [mul_one] at hh
  apply hh.congr
  intro k
  have hp : 0 < log (Nat.nth Nat.Prime (n k)) :=
    Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime (n k)).one_lt)
  simp [g,normalizedGap,div_mul_div_cancel₀,hp.ne']

theorem main : H1 → H2 → type_of% @Erdos5.erdos_5.variants.hildebrand_maier_measure := by
  rintro ⟨m,hm,sieve⟩ scale
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  refine ⟨(m:ℝ)⁻¹,inv_pos.mpr mp,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  let S := limitPointSet ∩ Icc 0 T
  have hS : volume S ≠ ⊤ := measure_ne_top_of_subset inter_subset_right (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  apply (ENNReal.ofReal_le_iff_le_toReal hS).2
  change (m:ℝ)⁻¹*T ≤ volume.real S
  by_contra! short
  have short' : (m:ℝ)*volume.real S < T := by
    rw [← div_eq_inv_mul,lt_div_iff₀ mp] at short
    linarith
  let ε := (T/(m:ℝ)-volume.real S)/2
  have he : 0 < ε := by dsimp [ε]; rw [div_pos_iff_of_pos_right (by norm_num)]; rw [sub_pos,lt_div_iff₀ mp]; linarith
  have hvol : volume.real (Icc 0 T) = T := by rw [Real.volume_real_Icc_of_le hT.le,sub_zero]
  obtain ⟨β,hβ,avoid⟩ := pack (S := limitPointSet) he m
    (Set.Subset.rfl : Icc 0 T ⊆ Icc 0 T) (by
      rw [hvol]; change (m:ℝ)*(ε+volume.real S)<T; dsimp [ε]; field_simp; nlinarith)
  obtain ⟨i,j,hij,hit⟩ := findLimit β (sieve β (fun i => (hβ i).1) (fun i j h => (avoid i j h).1)) scale
  exact (avoid i j hij).2 hit

end OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_measure_R1
