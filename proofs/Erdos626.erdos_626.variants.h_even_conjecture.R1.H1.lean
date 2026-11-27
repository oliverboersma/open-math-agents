import OMAReductions.R_Erdos626_erdos_626_variants_h_even_conjecture_R1
import Mathlib

/-! The upper half of the even case: h^(m)(n) <= n^(2/m + eps) for even m >= 2.

Girth greater than m implies girth greater than m - 1, so h^(m)(n) <= h^(m-1)(n), and for the odd
number m - 1 the bound of Erdős gives the exponent 2 / ((m - 1) + 1) = 2 / m.

Credit: the bound for odd m is the solved catalogue variant
Erdos626.erdos_626.variants.h_upper_odd, and everything up to GirthFleet.target below is the
merged proof of that variant by @senamakel (pull request 1471 of open-math-agents), reused
unchanged. Only the two final declarations (the monotonicity in m and the deduction of the even
case) are new. -/

-- Reference: P. Erdős, Graph theory and probability (1959).

/-!
# Chromatic number of graphs of large girth, odd case

Write `m = 2k - 1` and `D = ⌈n ^ (1/k)⌉`. A graph with no cycle of length at most `2k - 1` in
which every vertex of a set `T` has at least `D + 1` neighbours in `T` contains, inside `T`, an
independent set of size `D ^ (k - 1)`: the endpoints of the paths of length `k - 1` from a fixed
vertex. Two such paths cannot share an endpoint, and endpoints cannot be adjacent, since either
would close a cycle of length at most `2k - 1`. Removing such sets (one new colour each) or
vertices of degree at most `D` (coloured greedily) colours the graph with `2D + 1` colours.
-/

open SimpleGraph

namespace GirthFleet
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

/-- Two distinct paths with the same endpoints give a cycle of length at most the sum. -/
lemma short_cycle_of_two_paths : ∀ {x v : V} (P Q : G.Walk x v), P.IsPath → Q.IsPath → P ≠ Q →
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ c.length ≤ P.length + Q.length := by
  intro x v P
  induction P with
  | nil =>
    intro Q _ hQ hne
    exact absurd (Walk.isPath_iff_eq_nil.mp hQ).symm hne
  | @cons x u v h P' ih =>
    intro Q hP hQ hne
    cases Q with
    | nil => exact absurd (Walk.isPath_iff_eq_nil.mp hP) (by simp)
    | @cons _ w _ h2 Q' =>
      rw [Walk.cons_isPath_iff] at hP hQ
      by_cases huw : u = w
      · subst huw
        have hne' : P' ≠ Q' := by rintro rfl; exact hne rfl
        obtain ⟨z, c, hc, hl⟩ := ih Q' hP.1 hQ.1 hne'
        exact ⟨z, c, hc, by simp only [Walk.length_cons]; omega⟩
      · let W : G.Walk u x := P'.append (Q'.reverse.concat h2.symm)
        have hW : s(x, u) ∉ W.edges := by
          intro hmem
          simp only [W, Walk.edges_append, Walk.edges_concat, Walk.edges_reverse, List.mem_append,
            List.concat_eq_append, List.mem_reverse, List.mem_singleton] at hmem
          rcases hmem with h1 | h1 | h1
          · exact hP.2 (P'.fst_mem_support_of_mem_edges h1)
          · exact hQ.2 (Q'.fst_mem_support_of_mem_edges h1)
          · rw [Sym2.eq_iff] at h1
            rcases h1 with ⟨-, h3⟩ | ⟨-, h3⟩
            · exact G.ne_of_adj h h3.symm
            · exact huw h3
        refine ⟨x, Walk.cons h W.bypass, ?_, ?_⟩
        · rw [Walk.cons_isCycle_iff]
          exact ⟨W.bypass_isPath, fun hm => hW (W.edges_bypass_subset_edges hm)⟩
        · have h1 := W.length_bypass_le_length
          have h2 : W.length = P'.length + Q'.length + 1 := by
            simp only [W, Walk.length_append, Walk.length_concat, Walk.length_reverse]; omega
          simp only [Walk.length_cons]
          omega


section Indep
variable [Fintype V]
open Classical

/-- `G` restricted to the vertex set `T`. -/
def restr (G : SimpleGraph V) (T : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ T ∧ b ∈ T
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.irrefl h.1⟩

omit [DecidableEq V] [Fintype V] in
lemma restr_adj {T : Finset V} {a b : V} :
    (restr G T).Adj a b ↔ G.Adj a b ∧ a ∈ T ∧ b ∈ T := Iff.rfl

lemma big_indep (k D : ℕ) (hk : 1 ≤ k)
    (hgirth : ∀ (u : V) (c : G.Walk u u), c.IsCycle → 2 * k ≤ c.length)
    (T : Finset V) (hT : T.Nonempty) (hdeg : ∀ v ∈ T, D + 1 ≤ (T.filter (G.Adj v)).card) :
    ∃ I ⊆ T, D ^ (k - 1) ≤ I.card ∧ ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y := by
  obtain ⟨v, hv⟩ := hT
  let H := restr G T
  have hle : H ≤ G := fun a b h => (restr_adj.mp h).1
  have hHg : ∀ (u : V) (c : H.Walk u u), c.IsCycle → 2 * k ≤ c.length := fun u c hc => by
    have := hgirth u (c.mapLe hle) (hc.mapLe hle); rwa [Walk.length_mapLe] at this
  have huniq : ∀ {x : V} (P Q : H.Walk x v), P.IsPath → Q.IsPath →
      P.length + Q.length < 2 * k → P = Q := by
    intro x P Q hP hQ hl
    by_contra hne
    obtain ⟨u, c, hc, hcl⟩ := short_cycle_of_two_paths P Q hP hQ hne
    have := hHg u c hc; omega
  let S : ℕ → Finset V := fun j => T.filter (fun x => ∃ p : H.Walk x v, p.IsPath ∧ p.length = j)
  have hadjH : ∀ x ∈ T, ∀ y ∈ T, G.Adj x y → H.Adj x y := fun x hx y hy h => restr_adj.mpr ⟨h, hx, hy⟩
  have grow : ∀ j, j + 2 ≤ k → D * (S j).card ≤ (S (j + 1)).card := by
    intro j hj
    have hch : ∀ x ∈ S j, ∃ p : H.Walk x v, p.IsPath ∧ p.length = j :=
      fun x hx => (Finset.mem_filter.mp hx).2
    choose pth hpth using hch
    let E : {x // x ∈ S j} → Finset V := fun x =>
      (T.filter (G.Adj x.1)).filter (fun y => y ∉ (pth x.1 x.2).support)
    have hEsub : (S j).attach.biUnion E ⊆ S (j + 1) := by
      intro y hy
      simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, E, Finset.mem_filter] at hy
      obtain ⟨⟨x, hx⟩, ⟨hyT, hxy⟩, hns⟩ := hy
      have hxT : x ∈ T := (Finset.mem_filter.mp hx).1
      refine Finset.mem_filter.mpr ⟨hyT, Walk.cons (hadjH y hyT x hxT hxy.symm) (pth x hx), ?_, ?_⟩
      · rw [Walk.cons_isPath_iff]; exact ⟨(hpth x hx).1, hns⟩
      · rw [Walk.length_cons, (hpth x hx).2]
    have hEdisj : ∀ a ∈ (S j).attach, ∀ b ∈ (S j).attach, a ≠ b → Disjoint (E a) (E b) := by
      intro a _ b _ hab
      rw [Finset.disjoint_left]
      intro y hya hyb
      simp only [E, Finset.mem_filter] at hya hyb
      apply hab
      have hyT := hya.1.1
      have haT : a.1 ∈ T := (Finset.mem_filter.mp a.2).1
      have hbT : b.1 ∈ T := (Finset.mem_filter.mp b.2).1
      let Pa := Walk.cons (hadjH y hyT a.1 haT hya.1.2.symm) (pth a.1 a.2)
      let Pb := Walk.cons (hadjH y hyT b.1 hbT hyb.1.2.symm) (pth b.1 b.2)
      have hPa : Pa.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨(hpth _ _).1, hya.2⟩
      have hPb : Pb.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨(hpth _ _).1, hyb.2⟩
      have heq : Pa = Pb := huniq Pa Pb hPa hPb (by
        simp only [Pa, Pb, Walk.length_cons, (hpth _ _).2]; omega)
      have := congrArg (fun w => w.getVert 1) heq
      simp only [Pa, Pb, Walk.getVert_cons_succ, Walk.getVert_zero] at this
      exact Subtype.ext this
    have hEcard : ∀ x, D ≤ (E x).card := by
      rintro ⟨x, hx⟩
      have hxT : x ∈ T := (Finset.mem_filter.mp hx).1
      have hp := hpth x hx
      have hone : ((T.filter (G.Adj x)).filter (fun y => y ∈ (pth x hx).support)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        suffices hh : ∀ y ∈ (T.filter (G.Adj x)).filter (fun y => y ∈ (pth x hx).support),
            y = (pth x hx).getVert 1 by
          intro a ha b hb; rw [hh a ha, hh b hb]
        intro y hy
        simp only [Finset.mem_filter] at hy
        obtain ⟨⟨hyT, hxy⟩, hys⟩ := hy
        have hq : ((pth x hx).dropUntil y hys).IsPath := hp.1.dropUntil hys
        have hxq : x ∉ ((pth x hx).dropUntil y hys).support := by
          intro hxq
          have hnd := hp.1.support_nodup
          rw [← (pth x hx).take_spec hys, Walk.support_append] at hnd
          rw [← Walk.cons_tail_support] at hxq
          rcases List.mem_cons.mp hxq with h | h
          · exact G.ne_of_adj hxy h
          · exact List.disjoint_of_nodup_append hnd
              ((pth x hx).takeUntil y hys).start_mem_support h
        let Q := Walk.cons (hadjH x hxT y hyT hxy) ((pth x hx).dropUntil y hys)
        have hQ : Q.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hq, hxq⟩
        have hql : ((pth x hx).dropUntil y hys).length ≤ j :=
          hp.2 ▸ (pth x hx).length_dropUntil_le_length hys
        have := huniq Q (pth x hx) hQ hp.1 (by simp only [Q, Walk.length_cons]; omega)
        have h2 := congrArg (fun w => w.getVert 1) this
        simp only [Q, Walk.getVert_cons_succ, Walk.getVert_zero] at h2
        exact h2
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := T.filter (G.Adj x)) (fun y => y ∈ (pth x hx).support)
      have := hdeg x hxT
      show D ≤ ((T.filter (G.Adj x)).filter (fun y => y ∉ (pth x hx).support)).card
      omega
    calc D * (S j).card = ∑ x ∈ (S j).attach, D := by simp [mul_comm]
      _ ≤ ∑ x ∈ (S j).attach, (E x).card := Finset.sum_le_sum (fun x _ => hEcard x)
      _ = ((S j).attach.biUnion E).card := (Finset.card_biUnion hEdisj).symm
      _ ≤ _ := Finset.card_le_card hEsub
  have size : ∀ j, j + 1 ≤ k → D ^ j ≤ (S j).card := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [pow_zero]
      exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, Walk.nil, Walk.IsPath.nil, rfl⟩⟩
    | succ j ih =>
      intro hj
      calc D ^ (j + 1) = D * D ^ j := by ring
        _ ≤ D * (S j).card := Nat.mul_le_mul_left _ (ih (by omega))
        _ ≤ _ := grow j (by omega)
  refine ⟨S (k - 1), Finset.filter_subset _ _, size (k - 1) (by omega), ?_⟩
  intro x hx y hy hxy
  obtain ⟨hxT, px, hpx, hlx⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyT, py, hpy, hly⟩ := Finset.mem_filter.mp hy
  have hxyH := hadjH x hxT y hyT hxy
  by_cases hxs : x ∈ py.support
  · have hq : (py.dropUntil x hxs).IsPath := hpy.dropUntil hxs
    have hlen : (py.dropUntil x hxs).length + 1 ≤ py.length := by
      have h1 := congrArg Walk.length (py.take_spec hxs)
      rw [Walk.length_append] at h1
      have h2 : (py.takeUntil x hxs).length ≠ 0 := fun h0 =>
        G.ne_of_adj hxy (Walk.eq_of_length_eq_zero h0).symm
      omega
    have := huniq (py.dropUntil x hxs) px hq hpx (by omega)
    rw [this] at hlen
    omega
  · let Q := Walk.cons hxyH py
    have hQ : Q.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hpy, hxs⟩
    have := huniq Q px hQ hpx (by simp only [Q, Walk.length_cons]; omega)
    have h3 := congrArg Walk.length this
    simp only [Q, Walk.length_cons] at h3
    omega

end Indep


section Color
variable [Fintype V]
open Classical

lemma color_bound (k D : ℕ) (hk : 1 ≤ k)
    (hgirth : ∀ (u : V) (c : G.Walk u u), c.IsCycle → 2 * k ≤ c.length) :
    ∀ r (T : Finset V), T.card ≤ D ^ (k - 1) * r →
      ∃ c : V → Fin (r + D + 1), ∀ u ∈ T, ∀ w ∈ T, G.Adj u w → c u ≠ c w := by
  intro r
  induction r with
  | zero =>
    intro T hT
    have : T = ∅ := Finset.card_eq_zero.mp (by simpa using hT)
    exact ⟨fun _ => 0, by simp [this]⟩
  | succ r ihr =>
    intro T
    induction T using Finset.strongInduction with
    | H T ih =>
      intro hT
      by_cases hsp : ∃ v ∈ T, (T.filter (G.Adj v)).card ≤ D
      · obtain ⟨v, hvT, hv⟩ := hsp
        obtain ⟨c, hc⟩ := ih (T.erase v) (Finset.erase_ssubset hvT)
          (le_trans (Finset.card_le_card (Finset.erase_subset _ _)) hT)
        have hlt : ((T.filter (G.Adj v)).image c).card <
            (Finset.univ : Finset (Fin (r + 1 + D + 1))).card := by
          calc _ ≤ (T.filter (G.Adj v)).card := Finset.card_image_le
            _ ≤ D := hv
            _ < r + 1 + D + 1 := by omega
            _ = _ := by simp
        obtain ⟨col, -, hcol⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
        refine ⟨Function.update c v col, ?_⟩
        intro u hu w hw huw
        by_cases huv : u = v
        · subst huv
          have hwv : w ≠ u := (G.ne_of_adj huw).symm
          rw [Function.update_self, Function.update_of_ne hwv]
          intro h; apply hcol; rw [h]
          exact Finset.mem_image_of_mem _ (by simp [hw, huw])
        by_cases hwv : w = v
        · subst hwv
          rw [Function.update_self, Function.update_of_ne huv]
          intro h; apply hcol; rw [← h]
          exact Finset.mem_image_of_mem _ (by simp [hu, huw.symm])
        rw [Function.update_of_ne huv, Function.update_of_ne hwv]
        exact hc u (by simp [hu, huv]) w (by simp [hw, hwv]) huw
      · push Not at hsp
        rcases T.eq_empty_or_nonempty with rfl | hne
        · exact ⟨fun _ => 0, by simp⟩
        obtain ⟨I, hIT, hIcard, hI⟩ := big_indep k D hk hgirth T hne (fun v hv => hsp v hv)
        have hcard : (T \ I).card ≤ D ^ (k - 1) * r := by
          have := Finset.card_sdiff_add_card_eq_card hIT
          rw [Nat.mul_succ] at hT
          omega
        obtain ⟨c, hc⟩ := ihr (T \ I) hcard
        refine ⟨fun x => if x ∈ I then Fin.last _ else (Fin.castSucc (c x)).cast (by omega), ?_⟩
        intro u hu w hw huw
        by_cases huI : u ∈ I <;> by_cases hwI : w ∈ I
        · exact absurd huw (hI u huI w hwI)
        · simp only [huI, hwI, if_true, if_false]
          intro h; have := congrArg Fin.val h
          simp at this; have := (c w).isLt; omega
        · simp only [huI, hwI, if_true, if_false]
          intro h; have := congrArg Fin.val h
          simp at this; have := (c u).isLt; omega
        · simp only [huI, hwI, if_false]
          intro h
          apply hc u (by simp [hu, huI]) w (by simp [hw, hwI]) huw
          have := congrArg Fin.val h
          simp at this
          exact Fin.ext this

end Color

end GirthFleet


namespace GirthFleet

lemma h_le (k n D : ℕ) (hk : 1 ≤ k) (hD : n ≤ D ^ k) :
    Erdos626.h (2 * k - 1) n ≤ 2 * D + 1 := by
  classical
  unfold Erdos626.h
  by_cases hne : {c : ℕ | ∃ G : SimpleGraph (Fin n), ((2 * k - 1 : ℕ) : ℕ∞) < G.egirth ∧
      G.chromaticNumber = c}.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
  apply csSup_le hne
  rintro c ⟨G, hG, hc⟩
  have hgirth : ∀ (u : Fin n) (w : G.Walk u u), w.IsCycle → 2 * k ≤ w.length := by
    intro u w hw
    have h1 : ((2 * k : ℕ) : ℕ∞) ≤ G.egirth := by
      obtain ⟨j, hj⟩ : ∃ j, 2 * k = j + 1 := ⟨2 * k - 1, by omega⟩
      rw [show 2 * k - 1 = j by omega] at hG
      have := Order.add_one_le_of_lt hG
      rw [hj]; push_cast; exact this
    have := le_egirth.mp h1 u w hw
    exact_mod_cast this
  obtain ⟨col, hcol⟩ := color_bound (G := G) k D hk hgirth D Finset.univ (by
    rw [Finset.card_univ, Fintype.card_fin]
    calc n ≤ D ^ k := hD
      _ = D ^ (k - 1) * D := by rw [← pow_succ]; congr 1; omega)
  have hcolor : G.Colorable (D + D + 1) :=
    ⟨Coloring.mk col (fun {u w} huw => hcol u (by simp) w (by simp) huw)⟩
  have := hcolor.chromaticNumber_le
  rw [hc] at this
  have : c ≤ D + D + 1 := by exact_mod_cast this
  omega


open Filter in
theorem target : ∀ m : ℕ, Odd m → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (Erdos626.h m n : ℝ) ≤ (n : ℝ) ^ (2 / ((m : ℝ) + 1) + ε) := by
  intro m hm ε hε
  obtain ⟨j, rfl⟩ := hm
  have hev : ∀ᶠ n : ℕ in atTop, (5 : ℝ) ≤ (n : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 5
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hk : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hexp : 2 / (((2 * j + 1 : ℕ) : ℝ) + 1) = 1 / ((j + 1 : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  rw [hexp]
  set a : ℝ := (n : ℝ) ^ (1 / ((j + 1 : ℕ) : ℝ)) with ha
  set D : ℕ := ⌈a⌉₊ with hDdef
  have ha1 : 1 ≤ a := Real.one_le_rpow (by exact_mod_cast hn1) (by positivity)
  have hD : n ≤ D ^ (j + 1) := by
    have h1 : (n : ℝ) = a ^ (j + 1) := by
      rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      rw [show 1 / ((j + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) = 1 by field_simp]
      simp
    have h2 : a ^ (j + 1) ≤ (D : ℝ) ^ (j + 1) :=
      pow_le_pow_left₀ (by linarith) (Nat.le_ceil a) _
    have : (n : ℝ) ≤ ((D ^ (j + 1) : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hh := h_le (j + 1) n D (by omega) hD
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at hh
  have hDa : (D : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith)
  have hhR : (Erdos626.h (2 * j + 1) n : ℝ) ≤ 2 * D + 1 := by exact_mod_cast hh
  rw [Real.rpow_add hn0]
  calc (Erdos626.h (2 * j + 1) n : ℝ) ≤ 2 * D + 1 := hhR
    _ ≤ 5 * a := by linarith
    _ ≤ (n : ℝ) ^ ε * a := by nlinarith
    _ = a * (n : ℝ) ^ ε := by ring

end GirthFleet

lemma OMA.h_anti (m n : ℕ) : Erdos626.h m n ≤ Erdos626.h (m - 1) n := by
  unfold Erdos626.h
  apply csSup_le_csSup'
  · refine ⟨n, ?_⟩
    rintro c ⟨G, -, hc⟩
    have h := G.chromaticNumber_le_card
    rw [hc, Fintype.card_fin] at h
    exact_mod_cast h
  · rintro c ⟨G, hg, hc⟩
    refine ⟨G, lt_of_le_of_lt ?_ hg, hc⟩
    exact_mod_cast Nat.sub_le m 1

theorem OMA.solution : OMA.R_Erdos626_erdos_626_variants_h_even_conjecture_R1.H1 := by
  unfold OMA.R_Erdos626_erdos_626_variants_h_even_conjecture_R1.H1
  intro m hm hm2 ε hε
  have hodd : Odd (m - 1) := by
    obtain ⟨k, hk⟩ := hm
    exact ⟨k - 1, by omega⟩
  have key := GirthFleet.target (m - 1) hodd ε hε
  filter_upwards [key] with n hn
  have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hcast] at hn
  have hle : (Erdos626.h m n : ℝ) ≤ (Erdos626.h (m - 1) n : ℝ) := by
    exact_mod_cast OMA.h_anti m n
  exact le_trans hle hn
