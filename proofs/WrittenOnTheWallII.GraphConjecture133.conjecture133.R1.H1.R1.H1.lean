import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1

namespace OMA.Gap133H1Proof

open SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- Two common neighbours of two distinct vertices coincide in a C4-free graph. -/
lemma common_eq (G : SimpleGraph α)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    {x p s t : α} (hs : G.Adj x s) (hsp : G.Adj s p) (ht : G.Adj x t) (htp : G.Adj t p)
    (hxp : x ≠ p) : s = t := by
  by_contra hst
  exact hC4 ⟨x, s, p, t, G.ne_of_adj hs, hxp, G.ne_of_adj ht, G.ne_of_adj hsp, hst,
    (G.ne_of_adj htp).symm, hs, hsp, htp.symm, ht.symm⟩

omit [Fintype α] [DecidableEq α] in
lemma exists_parent (G : SimpleGraph α) (hconn : G.Connected) (c x : α) (hx : x ≠ c) :
    ∃ p, G.Adj p x ∧ G.dist c p + 1 = G.dist c x := by
  obtain ⟨w, hw⟩ := hconn.exists_walk_length_eq_dist x c
  cases w with
  | nil => exact absurd rfl hx
  | @cons _ u _ h q =>
    refine ⟨u, h.symm, ?_⟩
    have h1 := dist_le q
    have h3 : G.dist c x ≤ G.dist c u + 1 := dist_le_of_adj G hconn (v := c) h.symm
    rw [Walk.length_cons] at hw
    rw [dist_comm (u := x)] at hw
    rw [dist_comm (u := c) (v := u)]
    rw [dist_comm (u := c) (v := u)] at h3
    omega

/-- Local bound at a non-root vertex. -/
lemma indep_le_one_add (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hconn : G.Connected) (c x : α) (hx : x ≠ c)
    (hU : ∀ x, x ≠ c → ∀ p q, G.Adj p x → G.Adj q x → G.dist c p + 1 = G.dist c x →
      G.dist c q + 1 = G.dist c x → p = q)
    (hS : ∀ x y p, G.Adj x y → G.dist c x = G.dist c y → G.Adj p x →
      G.dist c p + 1 = G.dist c x → G.Adj p y) :
    indepNeighborsCard G x ≤
      1 + (Finset.univ.filter (fun y => G.Adj x y ∧ G.dist c y = G.dist c x + 1)).card := by
  obtain ⟨S, hSadj, hSI, hSc⟩ :=
    OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G x
  obtain ⟨p, hpx, hpd⟩ := exists_parent G hconn c x hx
  rw [← hSc]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (fun y => G.dist c y = G.dist c x + 1)
  have hup : (S.filter (fun y => G.dist c y = G.dist c x + 1)).card ≤
      (Finset.univ.filter (fun y => G.Adj x y ∧ G.dist c y = G.dist c x + 1)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact ⟨hSadj y hy.1, hy.2⟩
  have key : ∀ y, G.Adj x y → ¬ G.dist c y = G.dist c x + 1 → y = p ∨ G.Adj p y := by
    intro y hy hny
    have h1 := dist_le_of_adj G hconn (v := c) hy
    have h2 := dist_le_of_adj G hconn (v := c) hy.symm
    rcases (by omega : G.dist c y + 1 = G.dist c x ∨ G.dist c y = G.dist c x) with h | h
    · left
      exact hU x hx y p hy.symm hpx h hpd
    · right
      exact hS x y p hy h.symm hpx hpd
  have hrest : (S.filter (fun y => ¬ G.dist c y = G.dist c x + 1)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro s hs t ht
    simp only [Finset.mem_filter] at hs ht
    by_contra hst
    rcases key s (hSadj s hs.1) hs.2 with rfl | hps <;>
      rcases key t (hSadj t ht.1) ht.2 with rfl | hpt
    · exact hst rfl
    · exact hSI hs.1 ht.1 hst hpt
    · exact hSI hs.1 ht.1 hst hps.symm
    · exact hst (common_eq G hC4 (hSadj s hs.1) hps.symm (hSadj t ht.1) hpt.symm
        (G.ne_of_adj hpx).symm)
  omega

/-- The counting lemma. -/
lemma sum_indep_le (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hconn : G.Connected) (c : α)
    (hU : ∀ x, x ≠ c → ∀ p q, G.Adj p x → G.Adj q x → G.dist c p + 1 = G.dist c x →
      G.dist c q + 1 = G.dist c x → p = q)
    (hS : ∀ x y p, G.Adj x y → G.dist c x = G.dist c y → G.Adj p x →
      G.dist c p + 1 = G.dist c x → G.Adj p y) :
    ∑ x, indepNeighborsCard G x + 2 ≤ 2 * Fintype.card α := by
  set ch : α → ℕ := fun x =>
    (Finset.univ.filter (fun y => G.Adj x y ∧ G.dist c y = G.dist c x + 1)).card with hch
  have hloc : ∀ x, indepNeighborsCard G x ≤ ch x + (if x = c then 0 else 1) := by
    intro x
    by_cases hx : x = c
    · subst hx
      simp only [if_true, add_zero, hch]
      obtain ⟨S, hSadj, -, hSc⟩ :=
        OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G x
      rw [← hSc]
      apply Finset.card_le_card
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.dist_self, zero_add]
      exact ⟨hSadj y hy, dist_eq_one_iff_adj.mpr (hSadj y hy)⟩
    · simp only [hx, if_false]
      have := indep_le_one_add G hC4 hconn c x hx hU hS
      simp only [hch]
      omega
  have hsum_ch : ∑ x, ch x + 1 = Fintype.card α := by
    have h1 : ∑ x, ch x = ∑ y, (Finset.univ.filter
        (fun x => G.Adj x y ∧ G.dist c y = G.dist c x + 1)).card := by
      simp only [hch, Finset.card_filter]
      exact Finset.sum_comm
    have h2 : ∀ y, (Finset.univ.filter
        (fun x => G.Adj x y ∧ G.dist c y = G.dist c x + 1)).card = if y = c then 0 else 1 := by
      intro y
      by_cases hy : y = c
      · subst hy
        simp only [if_true, SimpleGraph.dist_self]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _ h
        omega
      · simp only [hy, if_false]
        obtain ⟨p, hpy, hpd⟩ := exists_parent G hconn c y hy
        rw [Finset.card_eq_one]
        refine ⟨p, ?_⟩
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hxy, hxd⟩
          exact hU y hy x p hxy hpy hxd.symm hpd
        · rintro rfl
          exact ⟨hpy, hpd.symm⟩
    rw [h1, Finset.sum_congr rfl (fun y _ => h2 y)]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α)) (fun y => y = c)
    rw [Finset.filter_eq' Finset.univ c] at this
    simp only [Finset.mem_univ, if_true, Finset.card_singleton, Finset.card_univ] at this
    omega
  calc ∑ x, indepNeighborsCard G x + 2
      ≤ ∑ x, (ch x + (if x = c then 0 else 1)) + 2 := by
        have := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hloc x)
        omega
    _ = ∑ x, ch x + ∑ x : α, (if x = c then 0 else 1) + 2 := by rw [Finset.sum_add_distrib]
    _ ≤ 2 * Fintype.card α := by
        have : ∑ x : α, (if x = c then 0 else 1) + 1 = Fintype.card α := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul,
            mul_one]
          have := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset α)) (fun y => y = c)
          rw [Finset.filter_eq' Finset.univ c] at this
          simp only [Finset.mem_univ, if_true, Finset.card_singleton, Finset.card_univ] at this
          omega
        omega


/-- Five vertices forming an induced path give `path ≥ 5`. -/
lemma path5 (G : SimpleGraph α) (a b c d e : α)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e)
    (nac : ¬ G.Adj a c) (nad : ¬ G.Adj a d) (nae : ¬ G.Adj a e) (nbd : ¬ G.Adj b d)
    (nbe : ¬ G.Adj b e) (nce : ¬ G.Adj c e)
    (dac : a ≠ c) (dad : a ≠ d) (dae : a ≠ e) (dbd : b ≠ d) (dbe : b ≠ e) (dce : c ≠ e) :
    5 ≤ SimpleGraph.path G := by
  have dab := G.ne_of_adj hab
  have dbc := G.ne_of_adj hbc
  have dcd := G.ne_of_adj hcd
  have dde := G.ne_of_adj hde
  let f : ℕ → α := fun i => match i with
    | 0 => a | 1 => b | 2 => c | 3 => d | _ => e
  have nca : ¬ G.Adj c a := fun h => nac h.symm
  have nda : ¬ G.Adj d a := fun h => nad h.symm
  have nea : ¬ G.Adj e a := fun h => nae h.symm
  have ndb : ¬ G.Adj d b := fun h => nbd h.symm
  have neb : ¬ G.Adj e b := fun h => nbe h.symm
  have nec : ¬ G.Adj e c := fun h => nce h.symm
  apply le_path_of_fun G f 5
  · intro i j hi hj h
    interval_cases i <;> interval_cases j <;> first
      | rfl
      | (exfalso; simp only [f] at h; first
          | exact dab h | exact dac h | exact dad h | exact dae h | exact dbc h
          | exact dbd h | exact dbe h | exact dcd h | exact dce h | exact dde h
          | exact dab h.symm | exact dac h.symm | exact dad h.symm | exact dae h.symm
          | exact dbc h.symm | exact dbd h.symm | exact dbe h.symm | exact dcd h.symm
          | exact dce h.symm | exact dde h.symm)
  · intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      simp [f, hab, hbc, hcd, hde, hab.symm, hbc.symm, hcd.symm, hde.symm, nac, nad, nae, nbd,
        nbe, nce, nca, nda, nea, ndb, neb, nec]

/-- An induced 5-cycle. -/
def IC5 (G : SimpleGraph α) (u0 u1 u2 u3 u4 : α) : Prop :=
  G.Adj u0 u1 ∧ G.Adj u1 u2 ∧ G.Adj u2 u3 ∧ G.Adj u3 u4 ∧ G.Adj u4 u0 ∧
    ¬ G.Adj u0 u2 ∧ ¬ G.Adj u0 u3 ∧ ¬ G.Adj u1 u3 ∧ ¬ G.Adj u1 u4 ∧ ¬ G.Adj u2 u4

omit [Fintype α] [DecidableEq α] in
lemma IC5.rot {G : SimpleGraph α} {u0 u1 u2 u3 u4 : α} (h : IC5 G u0 u1 u2 u3 u4) :
    IC5 G u1 u2 u3 u4 u0 := by
  obtain ⟨h1, h2, h3, h4, h5, n1, n2, n3, n4, n5⟩ := h
  exact ⟨h2, h3, h4, h5, h1, n3, n4, n5, fun h => n1 h.symm, fun h => n2 h.symm⟩

omit [Fintype α] [DecidableEq α] in
lemma IC5.distinct {G : SimpleGraph α} {u0 u1 u2 u3 u4 : α} (h : IC5 G u0 u1 u2 u3 u4) :
    u0 ≠ u2 ∧ u0 ≠ u3 := by
  obtain ⟨h1, h2, h3, h4, h5, n1, n2, n3, n4, n5⟩ := h
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact n2 h3
  · rintro rfl
    exact n1 h3.symm

/-- A vertex outside an induced 5-cycle adjacent to `u0` gives an induced path on 5 vertices. -/
lemma path5_of_IC5 (G : SimpleGraph α)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    {u0 u1 u2 u3 u4 w : α} (h : IC5 G u0 u1 u2 u3 u4)
    (w0 : w ≠ u0) (w1 : w ≠ u1) (w2 : w ≠ u2) (w3 : w ≠ u3) (w4 : w ≠ u4)
    (hw : G.Adj w u0) : 5 ≤ SimpleGraph.path G := by
  have hd := h.distinct
  have hd1 := h.rot.distinct
  have hd2 := h.rot.rot.distinct
  have hd3 := h.rot.rot.rot.distinct
  have hd4 := h.rot.rot.rot.rot.distinct
  obtain ⟨h1, h2, h3, h4, h5, n1, n2, n3, n4, n5⟩ := h
  have nw2 : ¬ G.Adj w u2 := fun hw2 => hC4 ⟨w, u0, u1, u2, w0, w1, w2, G.ne_of_adj h1,
    hd.1, G.ne_of_adj h2, hw, h1, h2, hw2.symm⟩
  have nw3 : ¬ G.Adj w u3 := fun hw3 => hC4 ⟨w, u0, u4, u3, w0, w4, w3, (G.ne_of_adj h5).symm,
    hd.2, (G.ne_of_adj h4).symm, hw, h5.symm, h4.symm, hw3.symm⟩
  by_cases hw1 : G.Adj w u1
  · have nw4 : ¬ G.Adj w u4 := fun hw4 => hC4 ⟨w, u1, u0, u4, w1, w0, w4,
      (G.ne_of_adj h1).symm, hd1.2, G.ne_of_adj h5.symm, hw1, h1.symm, h5.symm, hw4.symm⟩
    exact path5 G w u0 u4 u3 u2 hw h5.symm h4.symm h3.symm nw4 nw3 nw2 n2 n1
      (fun h => n5 h.symm) w4 w3 w2 hd.2 hd.1 hd2.1.symm
  · exact path5 G w u0 u1 u2 u3 hw h1 h2 h3 hw1 nw2 nw3 n1 n2 n3 w1 w2 w3 hd.1 hd.2 hd1.1

/-- With a vertex whose neighbourhood has three independent vertices, a connected C4-free graph
containing an induced 5-cycle has an induced path on 5 vertices. -/
lemma path5_of_IC5' (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    {u0 u1 u2 u3 u4 : α} (h : IC5 G u0 u1 u2 u3 u4)
    (hv : ∃ v : α, 3 ≤ indepNeighborsCard G v) : 5 ≤ SimpleGraph.path G := by
  classical
  let T : Finset α := {u0, u1, u2, u3, u4}
  by_cases hall : ∀ z, z ∈ T
  · exfalso
    obtain ⟨v, hv⟩ := hv
    obtain ⟨S, -, hSI, hSc⟩ :=
      OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G v
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp (by omega : 2 < S.card)
    have nab : ¬ G.Adj a b := hSI ha hb hab
    have nac : ¬ G.Adj a c := hSI ha hc hac
    have nbc : ¬ G.Adj b c := hSI hb hc hbc
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
    have ma := hall a
    have mb := hall b
    have mc := hall c
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at ma mb mc
    rcases ma with rfl | rfl | rfl | rfl | rfl <;> rcases mb with rfl | rfl | rfl | rfl | rfl <;>
      rcases mc with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact hab rfl | exact hac rfl | exact hbc rfl
        | exact nab h1 | exact nab h2 | exact nab h3 | exact nab h4 | exact nab h5
        | exact nab h1.symm | exact nab h2.symm | exact nab h3.symm | exact nab h4.symm
        | exact nab h5.symm
        | exact nac h1 | exact nac h2 | exact nac h3 | exact nac h4 | exact nac h5
        | exact nac h1.symm | exact nac h2.symm | exact nac h3.symm | exact nac h4.symm
        | exact nac h5.symm
        | exact nbc h1 | exact nbc h2 | exact nbc h3 | exact nbc h4 | exact nbc h5
        | exact nbc h1.symm | exact nbc h2.symm | exact nbc h3.symm | exact nbc h4.symm
        | exact nbc h5.symm
  · push Not at hall
    obtain ⟨z, hz⟩ := hall
    have hu0 : u0 ∈ (T : Set α) := by simp [T]
    obtain ⟨d, -, hd1, hd2⟩ := (hconn u0 z).some.exists_boundary_dart (T : Set α) hu0 hz
    have hadj := d.adj
    set x := d.fst
    set w := d.snd
    simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hd1 hd2
    obtain ⟨w0, w1, w2, w3, w4⟩ := hd2
    rcases hd1 with hx | hx | hx | hx | hx <;> rw [hx] at hadj
    · exact path5_of_IC5 G hC4 h w0 w1 w2 w3 w4 hadj.symm
    · exact path5_of_IC5 G hC4 h.rot w1 w2 w3 w4 w0 hadj.symm
    · exact path5_of_IC5 G hC4 h.rot.rot w2 w3 w4 w0 w1 hadj.symm
    · exact path5_of_IC5 G hC4 h.rot.rot.rot w3 w4 w0 w1 w2 hadj.symm
    · exact path5_of_IC5 G hC4 h.rot.rot.rot.rot w4 w0 w1 w2 w3 hadj.symm

/-- The gap-2 bound when the radius is at most 2. -/
theorem small_radius {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hP : SimpleGraph.path G = G.radius.toNat + 2)
    (hv : ∃ v : α, 3 ≤ indepNeighborsCard G v)
    (hr : G.radius.toNat ≤ 2) : SimpleGraph.l G ≤ 2 := by
  classical
  obtain ⟨c, hc⟩ := G.exists_eccent_eq_radius
  have hrtop : G.radius ≠ ⊤ := radius_ne_top_iff.mpr hconn
  have hecc : ∀ y, G.dist c y ≤ 2 := by
    intro y
    have hle : G.edist c y ≤ G.radius := hc ▸ edist_le_eccent
    have := ENat.toNat_le_toNat hle hrtop
    exact le_trans this hr
  have hd0 : ∀ y, G.dist c y = 0 → y = c := fun y h => ((hconn.dist_eq_zero_iff).mp h).symm
  have hd1 : ∀ y, G.dist c y = 1 → G.Adj c y := fun y h => dist_eq_one_iff_adj.mp h
  have hU : ∀ x, x ≠ c → ∀ p q, G.Adj p x → G.Adj q x → G.dist c p + 1 = G.dist c x →
      G.dist c q + 1 = G.dist c x → p = q := by
    intro x hx p q hp hq hpd hqd
    have h2 := hecc x
    rcases (by omega : G.dist c x = 1 ∨ G.dist c x = 2) with h | h
    · rw [hd0 p (by omega), hd0 q (by omega)]
    · exact common_eq G hC4 (hd1 p (by omega)) hp (hd1 q (by omega)) hq (Ne.symm hx)
  have hS : ∀ x y p, G.Adj x y → G.dist c x = G.dist c y → G.Adj p x →
      G.dist c p + 1 = G.dist c x → G.Adj p y := by
    intro x y p hxy hd hpx hpd
    have h2 := hecc x
    rcases (by omega : G.dist c x = 1 ∨ G.dist c x = 2) with h | h
    · rw [hd0 p (by omega)]
      exact hd1 y (by omega)
    · have hyc : y ≠ c := by
        rintro rfl
        rw [SimpleGraph.dist_self] at hd
        omega
      have hxc : x ≠ c := by
        rintro rfl
        rw [SimpleGraph.dist_self] at h
        omega
      obtain ⟨q, hqy, hqd⟩ := exists_parent G hconn c y hyc
      by_cases hpq : p = q
      · rw [hpq]
        exact hqy
      exfalso
      have hcp := hd1 p (by omega)
      have hcq := hd1 q (by omega)
      have ncx : ¬ G.Adj c x := fun hh => by
        have := dist_eq_one_iff_adj.mpr hh
        omega
      have ncy : ¬ G.Adj c y := fun hh => by
        have := dist_eq_one_iff_adj.mpr hh
        omega
      have npy : ¬ G.Adj p y := fun hh => hpq (hU y hyc p q hh hqy (by omega) hqd)
      have nqx : ¬ G.Adj x q := fun hh => hpq (hU x hxc q p hh.symm hpx (by omega) hpd).symm
      have npq : ¬ G.Adj p q := by
        intro hh
        apply hC4
        refine ⟨p, x, y, q, G.ne_of_adj hpx, ?_, hpq, G.ne_of_adj hxy, ?_, G.ne_of_adj hqy.symm,
          hpx, hxy, hqy.symm, hh.symm⟩
        · rintro rfl
          omega
        · rintro rfl
          omega
      have hic : IC5 G c p x y q := ⟨hcp, hpx, hxy, hqy.symm, hcq.symm, ncx, ncy, npy, npq, nqx⟩
      have := path5_of_IC5' G hconn hC4 hic hv
      omega
  have hsum := sum_indep_le G hC4 hconn c hU hS
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  unfold SimpleGraph.l averageIndepNeighbors indepNeighbors
  rw [div_le_iff₀ hn]
  have : (∑ x, (indepNeighborsCard G x : ℝ)) + 2 ≤ 2 * Fintype.card α := by exact_mod_cast hsum
  linarith

/-! ### Radius at least 3 -/

lemma le_path_of_fun' (G : SimpleGraph α) (f : ℕ → α) (n : ℕ)
    (hadj : ∀ i, i + 1 < n → G.Adj (f i) (f (i + 1)))
    (hfar : ∀ i j, j < n → i + 2 ≤ j → ¬ G.Adj (f i) (f j) ∧ f i ≠ f j) :
    n ≤ SimpleGraph.path G := by
  apply le_path_of_fun G f n
  · intro i j hi hj hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · by_cases h1 : i + 1 = j
      · subst h1
        exact G.ne_of_adj (hadj i hj) hij
      · exact (hfar i j hj (by omega)).2 hij
    · by_cases h1 : j + 1 = i
      · subst h1
        exact G.ne_of_adj (hadj j hi) hij.symm
      · exact (hfar j i hi (by omega)).2 hij.symm
  · intro i j hi hj
    constructor
    · intro h
      by_contra hc
      rcases Nat.lt_trichotomy i j with hl | rfl | hl
      · exact (hfar i j hj (by omega)).1 h
      · exact G.irrefl h
      · exact (hfar j i hi (by omega)).1 h.symm
    · rintro (h | h)
      · subst h
        exact hadj i hj
      · subst h
        exact (hadj j hi).symm

lemma glue (G : SimpleGraph α) (h : ℕ → α) (K : ℕ) (hK : 1 ≤ K) (t : ℕ → α) (s m : ℕ)
    (hsm : s ≤ m)
    (hHa : ∀ i, i + 1 < K → G.Adj (h i) (h (i + 1)))
    (hHf : ∀ i j, j < K → i + 2 ≤ j → ¬ G.Adj (h i) (h j) ∧ h i ≠ h j)
    (hTa : ∀ b, s ≤ b → b < m → G.Adj (t b) (t (b + 1)))
    (hTf : ∀ a b, s ≤ a → b ≤ m → a + 2 ≤ b → ¬ G.Adj (t a) (t b) ∧ t a ≠ t b)
    (hlast : G.Adj (h (K - 1)) (t s))
    (hX : ∀ i b, i < K → s ≤ b → b ≤ m → (i + 1 < K ∨ s < b) → ¬ G.Adj (h i) (t b))
    (hXne : ∀ i b, i < K → s ≤ b → b ≤ m → h i ≠ t b) :
    K + (m + 1 - s) ≤ SimpleGraph.path G := by
  let f : ℕ → α := fun i => if i < K then h i else t (i - K + s)
  apply le_path_of_fun' G f
  · intro i hi
    by_cases h1 : i + 1 < K
    · simp only [f, if_pos h1, if_pos (by omega : i < K)]
      exact hHa i h1
    · by_cases h2 : i < K
      · have hi' : i = K - 1 := by omega
        simp only [f, if_pos h2, if_neg h1]
        rw [show i + 1 - K + s = s by omega, hi']
        exact hlast
      · simp only [f, if_neg h2, if_neg h1]
        rw [show i + 1 - K + s = (i - K + s) + 1 by omega]
        exact hTa _ (by omega) (by omega)
  · intro i j hj hij
    by_cases hjK : j < K
    · simp only [f, if_pos hjK, if_pos (by omega : i < K)]
      exact hHf i j hjK hij
    · by_cases hiK : i < K
      · simp only [f, if_pos hiK, if_neg hjK]
        exact ⟨hX i _ hiK (by omega) (by omega) (by omega), hXne i _ hiK (by omega) (by omega)⟩
      · simp only [f, if_neg hiK, if_neg hjK]
        exact hTf _ _ (by omega) (by omega) (by omega)

omit [Fintype α] [DecidableEq α] in
lemma exists_geodesic2 (G : SimpleGraph α) (hconn : G.Connected) (v z : α) :
    ∃ f : ℕ → α, f 0 = v ∧ f (G.dist v z) = z ∧ (∀ i, i ≤ G.dist v z → G.dist v (f i) = i) ∧
      (∀ i, i ≤ G.dist v z → G.dist (f i) z = G.dist v z - i) ∧
      (∀ i, i < G.dist v z → G.Adj (f i) (f (i + 1))) := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v z
  have key : ∀ i, i ≤ G.dist v z →
      G.dist v (p.getVert i) = i ∧ G.dist (p.getVert i) z = G.dist v z - i := by
    intro i hi
    have h1 : G.dist v (p.getVert i) ≤ i := by
      have := dist_le (p.take i)
      rw [Walk.take_length] at this
      omega
    have h2 : G.dist (p.getVert i) z ≤ G.dist v z - i := by
      have := dist_le (p.drop i)
      rw [Walk.drop_length] at this
      omega
    have h3 := hconn.dist_triangle (u := v) (v := p.getVert i) (w := z)
    omega
  refine ⟨p.getVert, p.getVert_zero, ?_, fun i hi => (key i hi).1, fun i hi => (key i hi).2, ?_⟩
  · rw [← hp]
    exact p.getVert_length
  · intro i hi
    exact p.adj_getVert_succ (by omega)

omit [Fintype α] [DecidableEq α] in
lemma nadj_of_dist (G : SimpleGraph α) (hconn : G.Connected) (v : α) {x y : α}
    (h : G.dist v x + 2 ≤ G.dist v y) : ¬ G.Adj x y := by
  intro hxy
  have := dist_le_of_adj G hconn (v := v) hxy
  omega

omit [Fintype α] [DecidableEq α] in
lemma ne_of_dist (G : SimpleGraph α) (v : α) {x y : α}
    (h : G.dist v x ≠ G.dist v y) : x ≠ y := by
  rintro rfl
  exact h rfl

omit [Fintype α] [DecidableEq α] in
lemma dist_chain_le (G : SimpleGraph α) (hconn : G.Connected) (f : ℕ → α) (d : ℕ)
    (ha : ∀ i, i < d → G.Adj (f i) (f (i + 1))) (i k : ℕ) (hk : i + k ≤ d) :
    G.dist (f i) (f (i + k)) ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 := dist_le_of_adj G hconn (v := f i) (ha (i + k) (by omega))
    rw [show i + (k + 1) = i + k + 1 by omega]
    omega

/-- Three independent neighbours of `v`: one of them avoids the closed neighbourhoods of two
given neighbours `u`, `w` of `v`. -/
lemma exists_free (G : SimpleGraph α)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (v u w a1 a2 a3 : α) (hu : G.Adj v u) (hw : G.Adj v w)
    (h1 : G.Adj v a1) (h2 : G.Adj v a2) (h3 : G.Adj v a3)
    (d12 : a1 ≠ a2) (d13 : a1 ≠ a3) (d23 : a2 ≠ a3)
    (n12 : ¬ G.Adj a1 a2) (n13 : ¬ G.Adj a1 a3) (n23 : ¬ G.Adj a2 a3) :
    ∃ b, G.Adj v b ∧ b ≠ u ∧ ¬ G.Adj b u ∧ b ≠ w ∧ ¬ G.Adj b w := by
  -- two distinct independent neighbours of `v` cannot both lie in `N[x]` for a neighbour `x`
  have two : ∀ x a b, G.Adj v x → G.Adj v a → G.Adj v b → a ≠ b → ¬ G.Adj a b →
      (a = x ∨ G.Adj a x) → (b = x ∨ G.Adj b x) → False := by
    intro x a b hx ha hb hab nab hax hbx
    rcases hax with rfl | hax <;> rcases hbx with rfl | hbx
    · exact hab rfl
    · exact nab hbx.symm
    · exact nab hax
    · exact hab (common_eq G hC4 ha hax hb hbx (G.ne_of_adj hx))
  by_cases b1 : (a1 = u ∨ G.Adj a1 u) ∨ (a1 = w ∨ G.Adj a1 w)
  · by_cases b2 : (a2 = u ∨ G.Adj a2 u) ∨ (a2 = w ∨ G.Adj a2 w)
    · by_cases b3 : (a3 = u ∨ G.Adj a3 u) ∨ (a3 = w ∨ G.Adj a3 w)
      · exfalso
        rcases b1 with b1 | b1 <;> rcases b2 with b2 | b2 <;> rcases b3 with b3 | b3
        · exact two u a1 a2 hu h1 h2 d12 n12 b1 b2
        · exact two u a1 a2 hu h1 h2 d12 n12 b1 b2
        · exact two u a1 a3 hu h1 h3 d13 n13 b1 b3
        · exact two w a2 a3 hw h2 h3 d23 n23 b2 b3
        · exact two u a2 a3 hu h2 h3 d23 n23 b2 b3
        · exact two w a1 a3 hw h1 h3 d13 n13 b1 b3
        · exact two w a1 a2 hw h1 h2 d12 n12 b1 b2
        · exact two w a1 a2 hw h1 h2 d12 n12 b1 b2
      · push Not at b3
        exact ⟨a3, h3, b3.1.1, b3.1.2, b3.2.1, b3.2.2⟩
    · push Not at b2
      exact ⟨a2, h2, b2.1.1, b2.1.2, b2.2.1, b2.2.2⟩
  · push Not at b1
    exact ⟨a1, h1, b1.1.1, b1.1.2, b1.2.1, b1.2.2⟩

theorem large_radius (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (r : ℕ) (hr3 : 3 ≤ r) (v a1 a2 a3 : α)
    (h1 : G.Adj v a1) (h2 : G.Adj v a2) (h3 : G.Adj v a3)
    (d12 : a1 ≠ a2) (d13 : a1 ≠ a3) (d23 : a2 ≠ a3)
    (n12 : ¬ G.Adj a1 a2) (n13 : ¬ G.Adj a1 a3) (n23 : ¬ G.Adj a2 a3)
    (hecc : ∀ x, G.dist v x ≤ r) (z : α) (hz : G.dist v z = r)
    (hcent : ∀ u, ∃ y, r ≤ G.dist u y) : r + 3 ≤ SimpleGraph.path G := by
  obtain ⟨p, hp0, -, hpd, -, hpa⟩ := exists_geodesic2 G hconn v z
  rw [hz] at hpd hpa
  obtain ⟨y, hy⟩ := hcent (p 1)
  obtain ⟨t, ht0, -, htd, hty', hta⟩ := exists_geodesic2 G hconn v y
  set m := G.dist v y with hm
  have hmr : m ≤ r := hecc y
  have hp1d : G.dist v (p 1) = 1 := hpd 1 (by omega)
  have hmr' : r ≤ m + 1 := by
    have e : G.dist (p 1) v = 1 := by rw [dist_comm]; exact hp1d
    have := hconn.dist_triangle (u := p 1) (v := v) (w := y)
    omega
  have key : ∀ b, b ≤ m → r ≤ G.dist (p 1) (t b) + (m - b) := by
    intro b hb
    have := hconn.dist_triangle (u := p 1) (v := t b) (w := y)
    rw [hty' b hb] at this
    omega
  have hpp : ∀ a, 1 ≤ a → a ≤ r → G.dist (p 1) (p a) ≤ a - 1 := by
    intro a ha1 har
    have := dist_chain_le G hconn p r hpa 1 (a - 1) (by omega)
    rwa [show 1 + (a - 1) = a by omega] at this
  have chord : ∀ a b, 1 ≤ a → a ≤ r → b ≤ m → G.Adj (p a) (t b) →
      r + b ≤ a + m ∧ a ≤ b + 1 ∧ b ≤ a + 1 := by
    intro a b ha1 har hbm hadj
    have k := key b hbm
    have c1 := hpp a ha1 har
    have c2 := hconn.dist_triangle (u := p 1) (v := p a) (w := t b)
    rw [dist_eq_one_iff_adj.mpr hadj] at c2
    have l1 := dist_le_of_adj G hconn (v := v) hadj
    have l2 := dist_le_of_adj G hconn (v := v) hadj.symm
    rw [hpd a har, htd b hbm] at l1 l2
    omega
  have hdis : ∀ a b, a ≤ r → 1 ≤ b → b ≤ m → p a ≠ t b := by
    intro a b har hb1 hbm heq
    have e1 := hpd a har
    rw [heq, htd b hbm] at e1
    have k := key b hbm
    have c1 := hpp a (by omega) har
    rw [heq] at c1
    omega
  have hv_t : ∀ b, 2 ≤ b → b ≤ m → ¬ G.Adj v (t b) := by
    intro b hb2 hbm
    exact nadj_of_dist G hconn v (by rw [SimpleGraph.dist_self, htd b hbm]; omega)
  have hvp1 : G.Adj v (p 1) := by
    have := hpa 0 (by omega)
    rwa [hp0] at this
  have hvt1 : G.Adj v (t 1) := by
    have := hta 0 (by omega)
    rwa [ht0] at this
  have ht1d : G.dist v (t 1) = 1 := htd 1 (by omega)
  have hp2d : G.dist v (p 2) = 2 := hpd 2 (by omega)
  have hp3d : G.dist v (p 3) = 3 := hpd 3 (by omega)
  have ht2d : G.dist v (t 2) = 2 := htd 2 (by omega)
  obtain ⟨b, hvb, hb1, nb1, hbt, nbt⟩ :=
    exists_free G hC4 v (p 1) (t 1) a1 a2 a3 hvp1 hvt1 h1 h2 h3 d12 d13 d23 n12 n13 n23
  have hbd : G.dist v b = 1 := dist_eq_one_iff_adj.mpr hvb
  have hv0 : G.dist v v = 0 := SimpleGraph.dist_self
  have e_12 : G.Adj (p 1) (p 2) := hpa 1 (by omega)
  have e_23 : G.Adj (p 2) (p 3) := hpa 2 (by omega)
  have e_bv : G.Adj b v := hvb.symm
  have e_v1 : G.Adj v (p 1) := hvp1
  have q_12 : p 1 ≠ p 2 := G.ne_of_adj e_12
  have q_23 : p 2 ≠ p 3 := G.ne_of_adj e_23
  have q_bv : b ≠ v := (G.ne_of_adj hvb).symm
  have q_v1 : v ≠ p 1 := G.ne_of_adj hvp1
  have q_b1 : b ≠ p 1 := hb1
  have q_b2 : b ≠ p 2 := ne_of_dist G v (by omega)
  have q_b3 : b ≠ p 3 := ne_of_dist G v (by omega)
  have q_v2 : v ≠ p 2 := ne_of_dist G v (by omega)
  have q_v3 : v ≠ p 3 := ne_of_dist G v (by omega)
  have q_13 : p 1 ≠ p 3 := ne_of_dist G v (by omega)
  have n_b1 : ¬ G.Adj b (p 1) := nb1
  have n_b2 : ¬ G.Adj b (p 2) := fun hh => hC4 ⟨v, b, p 2, p 1, q_bv.symm, q_v2, q_v1, q_b2,
    q_b1, q_12.symm, hvb, hh, e_12.symm, hvp1.symm⟩
  have n_b3 : ¬ G.Adj b (p 3) := nadj_of_dist G hconn v (by omega)
  have n_v2 : ¬ G.Adj v (p 2) := nadj_of_dist G hconn v (by omega)
  have n_v3 : ¬ G.Adj v (p 3) := nadj_of_dist G hconn v (by omega)
  have n_13 : ¬ G.Adj (p 1) (p 3) := nadj_of_dist G hconn v (by omega)
  have nbt' : ∀ k, 1 ≤ k → k ≤ m → ¬ G.Adj b (t k) := by
    intro k hk1 hkm hh
    rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk
    · exact nbt hh
    · have q_t12 : t 1 ≠ t 2 := G.ne_of_adj (hta 1 (by omega))
      exact hC4 ⟨v, b, t 2, t 1, q_bv.symm, ne_of_dist G v (by omega), G.ne_of_adj hvt1,
        ne_of_dist G v (by omega), hbt, q_t12.symm, hvb, hh, (hta 1 (by omega)).symm,
        hvt1.symm⟩
    · exact nadj_of_dist G hconn v (by rw [htd k hkm]; omega) hh
  have nebt : ∀ k, 1 ≤ k → k ≤ m → b ≠ t k := by
    intro k hk1 hkm
    rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk
    · exact hbt
    · exact ne_of_dist G v (by rw [htd k hkm]; omega)
  have np2t1 : ¬ G.Adj (p 2) (t 1) := fun hh => hC4 ⟨v, p 1, p 2, t 1, q_v1, q_v2,
    G.ne_of_adj hvt1, q_12, hdis 1 1 (by omega) le_rfl (by omega),
    hdis 2 1 (by omega) le_rfl (by omega), hvp1, e_12, hh, hvt1.symm⟩
  rcases (by omega : m + 1 = r ∨ m = r) with hmc | hmc
  · by_cases hc : G.Adj (p 3) (t 2)
    · let H : ℕ → α := fun i => match i with | 0 => b | 1 => v | 2 => p 1 | 3 => p 2 | _ => p 3
      have hg := glue G H 5 (by omega) t 2 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · omega
      · intro i hi
        have hi' : i < 4 := by omega
        interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
      · intro i j hj hij
        have hi' : i < 5 := by omega
        interval_cases j <;> interval_cases i <;> try omega
        all_goals simp only [H]
        all_goals first
            | exact ⟨n_b1, q_b1⟩
            | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
            | exact ⟨n_b2, q_b2⟩
            | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
            | exact ⟨n_b3, q_b3⟩
            | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
            | exact ⟨n_v2, q_v2⟩
            | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
            | exact ⟨n_v3, q_v3⟩
            | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
            | exact ⟨n_13, q_13⟩
            | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
      · intro b' h1' h2'
        exact hta b' (by omega)
      · intro a' b' h1' h2' h3'
        exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
          ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
      · simp only [H]
        exact hc
      · intro i b' hi hb1' hb2' hor
        interval_cases i <;> simp only [H]
        · exact nbt' b' (by omega) hb2'
        · exact hv_t b' (by omega) hb2'
        · intro hh
          have cc := chord 1 b' (by omega) (by omega) hb2' hh
          omega
        · intro hh
          have cc := chord 2 b' (by omega) (by omega) hb2' hh
          omega
        · intro hh
          have cc := chord 3 b' (by omega) (by omega) hb2' hh
          omega
      · intro i b' hi hb1' hb2'
        interval_cases i <;> simp only [H]
        · exact nebt b' (by omega) hb2'
        · exact ne_of_dist G v (by rw [SimpleGraph.dist_self, htd b' hb2']; omega)
        · exact hdis 1 b' (by omega) (by omega) hb2'
        · exact hdis 2 b' (by omega) (by omega) hb2'
        · exact hdis 3 b' (by omega) (by omega) hb2'
    · let H : ℕ → α := fun i => match i with | 0 => p 3 | 1 => p 2 | 2 => p 1 | _ => v
      have hg := glue G H 4 (by omega) t 1 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · omega
      · intro i hi
        have hi' : i < 3 := by omega
        interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
      · intro i j hj hij
        have hi' : i < 4 := by omega
        interval_cases j <;> interval_cases i <;> try omega
        all_goals simp only [H]
        all_goals first
            | exact ⟨n_b1, q_b1⟩
            | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
            | exact ⟨n_b2, q_b2⟩
            | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
            | exact ⟨n_b3, q_b3⟩
            | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
            | exact ⟨n_v2, q_v2⟩
            | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
            | exact ⟨n_v3, q_v3⟩
            | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
            | exact ⟨n_13, q_13⟩
            | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
      · intro b' h1' h2'
        exact hta b' (by omega)
      · intro a' b' h1' h2' h3'
        exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
          ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
      · simp only [H]
        exact hvt1
      · intro i b' hi hb1' hb2' hor
        interval_cases i <;> simp only [H]
        · intro hh
          have cc := chord 3 b' (by omega) (by omega) hb2' hh
          have : b' = 2 := by omega
          subst this
          exact hc hh
        · intro hh
          have cc := chord 2 b' (by omega) (by omega) hb2' hh
          have : b' = 1 := by omega
          subst this
          exact np2t1 hh
        · intro hh
          have cc := chord 1 b' (by omega) (by omega) hb2' hh
          omega
        · exact hv_t b' (by omega) hb2'
      · intro i b' hi hb1' hb2'
        interval_cases i <;> simp only [H]
        · exact hdis 3 b' (by omega) (by omega) hb2'
        · exact hdis 2 b' (by omega) (by omega) hb2'
        · exact hdis 1 b' (by omega) (by omega) hb2'
        · exact ne_of_dist G v (by rw [SimpleGraph.dist_self, htd b' hb2']; omega)
  · by_cases hq : G.Adj (p 1) (t 1)
    · have np2t2 : ¬ G.Adj (p 2) (t 2) := fun hh => hC4 ⟨p 1, p 2, t 2, t 1, q_12,
        hdis 1 2 (by omega) (by omega) (by omega), hdis 1 1 (by omega) le_rfl (by omega),
        hdis 2 2 (by omega) (by omega) (by omega), hdis 2 1 (by omega) le_rfl (by omega),
        ne_of_dist G v (by omega), e_12, hh, (hta 1 (by omega)).symm, hq.symm⟩
      by_cases h33 : G.Adj (p 3) (t 3)
      · let H : ℕ → α := fun i => match i with | 0 => b | 1 => v | 2 => p 1 | 3 => p 2 | _ => p 3
        have hg := glue G H 5 (by omega) t 3 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · intro i hi
          have hi' : i < 4 := by omega
          interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
        · intro i j hj hij
          have hi' : i < 5 := by omega
          interval_cases j <;> interval_cases i <;> try omega
          all_goals simp only [H]
          all_goals first
              | exact ⟨n_b1, q_b1⟩
              | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
              | exact ⟨n_b2, q_b2⟩
              | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
              | exact ⟨n_b3, q_b3⟩
              | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
              | exact ⟨n_v2, q_v2⟩
              | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
              | exact ⟨n_v3, q_v3⟩
              | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
              | exact ⟨n_13, q_13⟩
              | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
        · intro b' h1' h2'
          exact hta b' (by omega)
        · intro a' b' h1' h2' h3'
          exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
            ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
        · simp only [H]
          exact h33
        · intro i b' hi hb1' hb2' hor
          interval_cases i <;> simp only [H]
          · exact nbt' b' (by omega) hb2'
          · exact hv_t b' (by omega) hb2'
          · intro hh
            have cc := chord 1 b' (by omega) (by omega) hb2' hh
            omega
          · intro hh
            have cc := chord 2 b' (by omega) (by omega) hb2' hh
            omega
          · intro hh
            have cc := chord 3 b' (by omega) (by omega) hb2' hh
            omega
        · intro i b' hi hb1' hb2'
          interval_cases i <;> simp only [H]
          · exact nebt b' (by omega) hb2'
          · exact ne_of_dist G v (by rw [SimpleGraph.dist_self, htd b' hb2']; omega)
          · exact hdis 1 b' (by omega) (by omega) hb2'
          · exact hdis 2 b' (by omega) (by omega) hb2'
          · exact hdis 3 b' (by omega) (by omega) hb2'
      · by_cases h32 : G.Adj (p 3) (t 2)
        · let H : ℕ → α := fun i => match i with | 0 => b | 1 => v | 2 => p 1 | 3 => p 2 | _ => p 3
          have hg := glue G H 5 (by omega) t 2 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · omega
          · intro i hi
            have hi' : i < 4 := by omega
            interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
          · intro i j hj hij
            have hi' : i < 5 := by omega
            interval_cases j <;> interval_cases i <;> try omega
            all_goals simp only [H]
            all_goals first
                | exact ⟨n_b1, q_b1⟩
                | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
                | exact ⟨n_b2, q_b2⟩
                | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
                | exact ⟨n_b3, q_b3⟩
                | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
                | exact ⟨n_v2, q_v2⟩
                | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
                | exact ⟨n_v3, q_v3⟩
                | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
                | exact ⟨n_13, q_13⟩
                | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
          · intro b' h1' h2'
            exact hta b' (by omega)
          · intro a' b' h1' h2' h3'
            exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
              ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
          · simp only [H]
            exact h32
          · intro i b' hi hb1' hb2' hor
            interval_cases i <;> simp only [H]
            · exact nbt' b' (by omega) hb2'
            · exact hv_t b' (by omega) hb2'
            · intro hh
              have cc := chord 1 b' (by omega) (by omega) hb2' hh
              omega
            · intro hh
              have cc := chord 2 b' (by omega) (by omega) hb2' hh
              have : b' = 2 := by omega
              subst this
              exact np2t2 hh
            · intro hh
              have cc := chord 3 b' (by omega) (by omega) hb2' hh
              have : b' = 3 := by omega
              subst this
              exact h33 hh
          · intro i b' hi hb1' hb2'
            interval_cases i <;> simp only [H]
            · exact nebt b' (by omega) hb2'
            · exact ne_of_dist G v (by rw [SimpleGraph.dist_self, htd b' hb2']; omega)
            · exact hdis 1 b' (by omega) (by omega) hb2'
            · exact hdis 2 b' (by omega) (by omega) hb2'
            · exact hdis 3 b' (by omega) (by omega) hb2'
        · let H : ℕ → α := fun i => match i with | 0 => p 3 | 1 => p 2 | _ => p 1
          have hg := glue G H 3 (by omega) t 1 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · omega
          · intro i hi
            have hi' : i < 2 := by omega
            interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
          · intro i j hj hij
            have hi' : i < 3 := by omega
            interval_cases j <;> interval_cases i <;> try omega
            all_goals simp only [H]
            all_goals first
                | exact ⟨n_b1, q_b1⟩
                | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
                | exact ⟨n_b2, q_b2⟩
                | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
                | exact ⟨n_b3, q_b3⟩
                | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
                | exact ⟨n_v2, q_v2⟩
                | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
                | exact ⟨n_v3, q_v3⟩
                | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
                | exact ⟨n_13, q_13⟩
                | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
          · intro b' h1' h2'
            exact hta b' (by omega)
          · intro a' b' h1' h2' h3'
            exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
              ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
          · simp only [H]
            exact hq
          · intro i b' hi hb1' hb2' hor
            interval_cases i <;> simp only [H]
            · intro hh
              have cc := chord 3 b' (by omega) (by omega) hb2' hh
              rcases (by omega : b' = 2 ∨ b' = 3) with rfl | rfl
              · exact h32 hh
              · exact h33 hh
            · intro hh
              have cc := chord 2 b' (by omega) (by omega) hb2' hh
              rcases (by omega : b' = 1 ∨ b' = 2) with rfl | rfl
              · exact np2t1 hh
              · exact np2t2 hh
            · intro hh
              have cc := chord 1 b' (by omega) (by omega) hb2' hh
              omega
          · intro i b' hi hb1' hb2'
            interval_cases i <;> simp only [H]
            · exact hdis 3 b' (by omega) (by omega) hb2'
            · exact hdis 2 b' (by omega) (by omega) hb2'
            · exact hdis 1 b' (by omega) (by omega) hb2'
    · by_cases h22 : G.Adj (p 2) (t 2)
      · let H : ℕ → α := fun i => match i with | 0 => b | 1 => v | 2 => p 1 | _ => p 2
        have hg := glue G H 4 (by omega) t 2 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · intro i hi
          have hi' : i < 3 := by omega
          interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
        · intro i j hj hij
          have hi' : i < 4 := by omega
          interval_cases j <;> interval_cases i <;> try omega
          all_goals simp only [H]
          all_goals first
              | exact ⟨n_b1, q_b1⟩
              | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
              | exact ⟨n_b2, q_b2⟩
              | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
              | exact ⟨n_b3, q_b3⟩
              | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
              | exact ⟨n_v2, q_v2⟩
              | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
              | exact ⟨n_v3, q_v3⟩
              | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
              | exact ⟨n_13, q_13⟩
              | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
        · intro b' h1' h2'
          exact hta b' (by omega)
        · intro a' b' h1' h2' h3'
          exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
            ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
        · simp only [H]
          exact h22
        · intro i b' hi hb1' hb2' hor
          interval_cases i <;> simp only [H]
          · exact nbt' b' (by omega) hb2'
          · exact hv_t b' (by omega) hb2'
          · intro hh
            have cc := chord 1 b' (by omega) (by omega) hb2' hh
            omega
          · intro hh
            have cc := chord 2 b' (by omega) (by omega) hb2' hh
            omega
        · intro i b' hi hb1' hb2'
          interval_cases i <;> simp only [H]
          · exact nebt b' (by omega) hb2'
          · exact ne_of_dist G v (by rw [SimpleGraph.dist_self, htd b' hb2']; omega)
          · exact hdis 1 b' (by omega) (by omega) hb2'
          · exact hdis 2 b' (by omega) (by omega) hb2'
      · let H : ℕ → α := fun i => match i with | 0 => p 2 | 1 => p 1 | _ => v
        have hg := glue G H 3 (by omega) t 1 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · intro i hi
          have hi' : i < 2 := by omega
          interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
        · intro i j hj hij
          have hi' : i < 3 := by omega
          interval_cases j <;> interval_cases i <;> try omega
          all_goals simp only [H]
          all_goals first
              | exact ⟨n_b1, q_b1⟩
              | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
              | exact ⟨n_b2, q_b2⟩
              | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
              | exact ⟨n_b3, q_b3⟩
              | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
              | exact ⟨n_v2, q_v2⟩
              | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
              | exact ⟨n_v3, q_v3⟩
              | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
              | exact ⟨n_13, q_13⟩
              | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
        · intro b' h1' h2'
          exact hta b' (by omega)
        · intro a' b' h1' h2' h3'
          exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
            ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
        · simp only [H]
          exact hvt1
        · intro i b' hi hb1' hb2' hor
          interval_cases i <;> simp only [H]
          · intro hh
            have cc := chord 2 b' (by omega) (by omega) hb2' hh
            rcases (by omega : b' = 1 ∨ b' = 2) with rfl | rfl
            · exact np2t1 hh
            · exact h22 hh
          · intro hh
            have cc := chord 1 b' (by omega) (by omega) hb2' hh
            have : b' = 1 := by omega
            subst this
            exact hq hh
          · exact hv_t b' (by omega) hb2'
        · intro i b' hi hb1' hb2'
          interval_cases i <;> simp only [H]
          · exact hdis 2 b' (by omega) (by omega) hb2'
          · exact hdis 1 b' (by omega) (by omega) hb2'
          · exact ne_of_dist G v (by rw [SimpleGraph.dist_self, htd b' hb2']; omega)

theorem gap2 {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hP : SimpleGraph.path G = G.radius.toNat + 2)
    (hv : ∃ v : α, 3 ≤ indepNeighborsCard G v) : SimpleGraph.l G ≤ 2 := by
  classical
  by_cases hr : G.radius.toNat ≤ 2
  · exact small_radius G hconn hC4 hP hv hr
  exfalso
  set r := G.radius.toNat with hrdef
  have hfar : ∀ v : α, ∃ z, r ≤ G.dist v z := by
    intro v
    obtain ⟨z, hz⟩ := G.exists_edist_eq_eccent_of_finite v
    refine ⟨z, ?_⟩
    have hle : G.radius ≤ G.edist v z := hz ▸ radius_le_eccent
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v z
    have h2 : G.edist v z ≤ (G.dist v z : ℕ∞) := by
      rw [← hp]
      exact edist_le p
    have := ENat.toNat_le_toNat (le_trans hle h2) (by simp)
    simpa [hrdef] using this
  obtain ⟨v, hv3⟩ := hv
  have hecc : ∀ x, G.dist v x ≤ r := by
    intro x
    by_cases hx : G.dist v x = 0
    · omega
    obtain ⟨f, hf0, hd, ha⟩ := exists_geodesic G hconn v x
    have hv1 : G.Adj v (f 1) := by
      have := ha 0 (by omega)
      rwa [hf0] at this
    obtain ⟨c, hvc, hc1, hcn⟩ := exists_escape G hC4 v (f 1) hv1 (by omega)
    have := add_two_le_path G hconn hC4 v x c f hf0 hd ha (by omega) hvc hc1 hcn
    omega
  obtain ⟨z, hz⟩ := hfar v
  have hz' : G.dist v z = r := le_antisymm (hecc z) hz
  obtain ⟨S, hSadj, hSI, hSc⟩ :=
    OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G v
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp (by omega : 2 < S.card)
  have := large_radius G hconn hC4 r (by omega) v a b c (hSadj a ha) (hSadj b hb) (hSadj c hc)
    hab hac hbc (hSI ha hb hab) (hSI ha hc hac) (hSI hb hc hbc) hecc z hz' hfar
  omega


end OMA.Gap133H1Proof

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1.H1 := by
  intro α _ _ _ G hconn hC4 hP hv _
  exact OMA.Gap133H1Proof.gap2 G hconn hC4 hP hv
