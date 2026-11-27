import FormalConjectures.ErdosProblems.«803»
import Mathlib

/-! The coefficient in the stated bound may depend on k. We take a matching
with exactly k+1 edges. All its vertices have degree one and its size is fixed
before the host graph is chosen. -/
namespace OMA.FixedMatching803
open Finset SimpleGraph Filter Real
open scoped Classical

lemma freshEdge {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Fin n))
    (large : S.ncard * n < G.edgeSet.ncard) :
    ∃ u ∉ S, ∃ v ∉ S, G.Adj u v := by
  classical
  by_contra! cover
  let pairs := S.toFinset ×ˢ (univ : Finset (Fin n))
  let edge (z : Fin n × Fin n) : Sym2 (Fin n) := s(z.1,z.2)
  have covered : G.edgeFinset ⊆ pairs.image edge := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      have adj : G.Adj u v := by simpa using he
      by_cases hu : u ∈ S
      · exact mem_image.mpr ⟨(u,v),by simpa [pairs] using hu,rfl⟩
      · have hv : v ∈ S := by
          by_contra out
          exact cover u hu v out adj
        exact mem_image.mpr ⟨(v,u),by simpa [pairs] using hv,Sym2.eq_swap⟩
  have bound := (card_le_card covered).trans card_image_le
  have eq : G.edgeFinset.card = G.edgeSet.ncard := by rw [G.edgeFinset_card,Set.fintypeCard_eq_ncard]
  have pc : pairs.card = S.ncard*n := by simp [pairs,Set.ncard_eq_toFinset_card']
  omega

lemma matching {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ)
    (large : (2*t)*n < G.edgeSet.ncard) :
    ∃ H : G.Subgraph, H.IsMatching ∧ H.verts.ncard = 2*t := by
  classical
  induction t with
  | zero =>
    exact ⟨⊥,by intro v hv; simp at hv,by simp⟩
  | succ t ih =>
    have less : 2*t*n ≤ (2*(t+1))*n := Nat.mul_le_mul_right _ (by omega)
    obtain ⟨H,hH,count⟩ := ih (less.trans_lt large)
    obtain ⟨u,hu,v,hv,adj⟩ := freshEdge G H.verts (by rw [count]; exact less.trans_lt large)
    let E := G.subgraphOfAdj adj
    have eH := Subgraph.IsMatching.subgraphOfAdj adj
    have outside : Disjoint H.verts E.verts := by
      rw [Set.disjoint_left]
      intro w hw he
      change w ∈ (G.subgraphOfAdj adj).verts at he
      rw [subgraphOfAdj_verts] at he
      rcases he with eq | eq
      · exact hu (eq ▸ hw)
      · exact hv ((Set.mem_singleton_iff.mp eq) ▸ hw)
    have countE : E.verts.ncard = 2 := by
      change (G.subgraphOfAdj adj).verts.ncard = _
      rw [subgraphOfAdj_verts,Set.ncard_pair adj.ne]
    refine ⟨H ⊔ E,hH.sup eH (by rwa [hH.support_eq_verts,eH.support_eq_verts]),?_⟩
    rw [Subgraph.verts_sup,Set.ncard_union_eq outside,count,countE]
    omega

end OMA.FixedMatching803

open SimpleGraph Filter Real in
theorem OMA.solution : type_of% @Erdos803.erdos_803.variants.janzer_sudakov := by
  classical
  refine ⟨1,?_⟩
  intro k
  let m := 2*(k+1)
  let a := (√(log (m : ℝ)) / (log (log (m:ℝ)))^(3/2:ℝ)) * m
  let c := (|a|+1)⁻¹
  have den : 0 < |a|+1 := by positivity
  refine ⟨c,inv_pos.mpr den,?_⟩
  have grow := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop (m:ℝ)
  filter_upwards [grow,eventually_ge_atTop 1] with n hn hn1
  intro G e
  change (m:ℝ) < log (n:ℝ) at hn
  have nr : (0:ℝ) < n := by exact_mod_cast hn1
  have lower : m*n < G.edgeSet.ncard := by
    exact_mod_cast (show (m:ℝ)*n < G.edgeSet.ncard from
      (mul_lt_mul_of_pos_right hn nr).trans_le (by simpa [mul_comm] using e))
  obtain ⟨H,hm,hsize⟩ := FixedMatching803.matching G (k+1) lower
  change H.verts.ncard = m at hsize
  have hp : H.verts.Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by rw [hsize]; dsimp [m]; omega)
  let : Nonempty H.verts := hp.to_subtype
  have deg (w : H.verts) (inst : Fintype (H.coe.neighborSet w)) :
      @SimpleGraph.degree _ H.coe w inst = 1 := by
    apply (@SimpleGraph.degree_eq_one_iff_existsUnique_adj _ H.coe w inst).mpr
    obtain ⟨z,hz,unique⟩ := hm w.property
    exact ⟨⟨z,H.edge_vert hz.symm⟩,hz,fun j hj => Subtype.ext (unique j hj)⟩
  have balanced : IsBalanced H.coe 1 := by
    obtain ⟨u,hu⟩ := H.coe.exists_maximal_degree_vertex
    obtain ⟨v,hv⟩ := H.coe.exists_minimal_degree_vertex
    have hi : H.coe.maxDegree = 1 := hu.trans (deg u _)
    have lo : H.coe.minDegree = 1 := hv.trans (deg v _)
    simp [IsBalanced,hi,lo]
  obtain ⟨u,hu⟩ := hp
  obtain ⟨v,hv,_⟩ := hm hu
  have posE : 0 < H.edgeSet.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨s(u,v),hv⟩
  refine ⟨H,by rw [hsize]; dsimp [m]; omega,balanced,?_⟩
  rw [hsize,mul_assoc]
  change c*a ≤ (H.edgeSet.ncard:ℝ)
  have one : c*a ≤ 1 := by
    change (|a|+1)⁻¹*a ≤ 1
    rw [← div_eq_inv_mul,div_le_iff₀ den,one_mul]
    linarith [le_abs_self a]
  exact one.trans (by exact_mod_cast posE)
