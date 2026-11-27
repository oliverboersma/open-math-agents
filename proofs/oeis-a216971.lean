import OMAStatements.S_oeis_a216971
import Mathlib

namespace OMA.S_oeis_a216971

open Classical in
private noncomputable def perFinset {n : ℕ} (f : Fin n → Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => x ∈ Function.periodicPts f

open Classical in
private noncomputable def depth1Card {n : ℕ} (f : Fin n → Fin n) : ℕ :=
  (Finset.univ.filter fun x => x ∉ Function.periodicPts f ∧ f x ∈ Function.periodicPts f).card

open Classical in
private noncomputable def goodFuns (n k : ℕ) : Finset (Fin n → Fin n) :=
  Finset.univ.filter fun f => depth1Card f = k

private lemma ncard_eq_goodFuns_card (n k : ℕ) :
    {f : Fin n → Fin n |
      {x : Fin n | x ∉ Function.periodicPts f ∧ f x ∈ Function.periodicPts f}.ncard = k}.ncard =
    (goodFuns n k).card := by
  classical
  have hinner : ∀ f : Fin n → Fin n,
      {x : Fin n | x ∉ Function.periodicPts f ∧ f x ∈ Function.periodicPts f}.ncard =
        depth1Card f := by
    intro f
    have hset : {x : Fin n | x ∉ Function.periodicPts f ∧ f x ∈ Function.periodicPts f} =
        ((Finset.univ.filter fun x =>
          x ∉ Function.periodicPts f ∧ f x ∈ Function.periodicPts f : Finset (Fin n)) :
          Set (Fin n)) := by
      ext x; simp
    rw [hset, Set.ncard_coe_finset]
    rfl
  have houter : {f : Fin n → Fin n |
      {x : Fin n | x ∉ Function.periodicPts f ∧ f x ∈ Function.periodicPts f}.ncard = k} =
      (goodFuns n k : Set (Fin n → Fin n)) := by
    ext f
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, goodFuns, Finset.mem_filter,
      Finset.mem_univ, true_and, hinner]
  rw [houter, Set.ncard_coe_finset]

private lemma perFinset_nonempty {n : ℕ} (hn : 0 < n) (f : Fin n → Fin n) :
    (perFinset f).Nonempty := by
  classical
  let x0 : Fin n := ⟨0, hn⟩
  have hlt : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by simp
  obtain ⟨i, j, hij, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun m : Fin (n + 1) => f^[m.1] x0) hlt
  have hpair : ∃ a b : ℕ, a < b ∧ f^[a] x0 = f^[b] x0 := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h1 | h2
    · exact ⟨i.1, j.1, h1, heq⟩
    · exact ⟨j.1, i.1, h2, heq.symm⟩
  rcases hpair with ⟨a, b, hab, hfab⟩
  refine ⟨f^[a] x0, ?_⟩
  rw [perFinset, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, b - a, by omega, ?_⟩
  change f^[b - a] (f^[a] x0) = f^[a] x0
  rw [← Function.iterate_add_apply, show b - a + a = b by omega, hfab]

private lemma mem_periodicPts_conj {n : ℕ} (π : Equiv.Perm (Fin n)) (f : Fin n → Fin n)
    (x : Fin n) :
    π x ∈ Function.periodicPts (fun y => π (f (π.symm y))) ↔ x ∈ Function.periodicPts f := by
  have hiter : ∀ t : ℕ, ∀ y : Fin n,
      (fun z => π (f (π.symm z)))^[t] (π y) = π (f^[t] y) := by
    intro t
    induction t with
    | zero => intro y; simp
    | succ t ih =>
      intro y
      rw [Function.iterate_succ_apply', ih, Equiv.symm_apply_apply, Function.iterate_succ_apply']
  constructor
  · rintro ⟨p, hp, hfix⟩
    refine ⟨p, hp, ?_⟩
    change f^[p] x = x
    have h1 : (fun z => π (f (π.symm z)))^[p] (π x) = π x := hfix
    rw [hiter p x] at h1
    exact π.injective h1
  · rintro ⟨p, hp, hfix⟩
    refine ⟨p, hp, ?_⟩
    change (fun z => π (f (π.symm z)))^[p] (π x) = π x
    rw [hiter p x]
    exact congrArg π hfix

private lemma perFinset_conj {n : ℕ} (π : Equiv.Perm (Fin n)) (f : Fin n → Fin n) :
    perFinset (fun y => π (f (π.symm y))) = (perFinset f).map π.toEmbedding := by
  classical
  ext y
  simp only [perFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.coe_toEmbedding]
  constructor
  · intro hy
    refine ⟨π.symm y, ?_, π.apply_symm_apply y⟩
    have h := mem_periodicPts_conj π f (π.symm y)
    rw [π.apply_symm_apply] at h
    exact h.mp hy
  · rintro ⟨x, hx, rfl⟩
    exact (mem_periodicPts_conj π f x).mpr hx

private lemma depth1Card_conj {n : ℕ} (π : Equiv.Perm (Fin n)) (f : Fin n → Fin n) :
    depth1Card (fun y => π (f (π.symm y))) = depth1Card f := by
  classical
  unfold depth1Card
  refine Finset.card_bij (fun y _ => π.symm y) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have h1 := mem_periodicPts_conj π f (π.symm y)
    rw [π.apply_symm_apply] at h1
    have h2 := mem_periodicPts_conj π f (f (π.symm y))
    exact ⟨fun h => hy.1 (h1.mpr h), h2.mp hy.2⟩
  · intro y1 _ y2 _ heq
    exact π.symm.injective heq
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨π x, ?_, π.symm_apply_apply x⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := mem_periodicPts_conj π f x
    have h2 := mem_periodicPts_conj π f (f x)
    rw [π.symm_apply_apply]
    exact ⟨fun h => hx.1 (h1.mp h), h2.mpr hx.2⟩

private lemma exists_perm_map_eq {n : ℕ} {P1 P2 : Finset (Fin n)} (hcard : P1.card = P2.card) :
    ∃ π : Equiv.Perm (Fin n), P1.map π.toEmbedding = P2 := by
  classical
  have h1 : Fintype.card {x : Fin n // x ∈ P1} = Fintype.card {x : Fin n // x ∈ P2} := by
    simp [hcard]
  have h2 : Fintype.card {x : Fin n // x ∉ P1} = Fintype.card {x : Fin n // x ∉ P2} := by
    have hc1 : (Finset.univ.filter (fun x : Fin n => x ∉ P1)).card = n - P1.card := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (· ∈ P1)
      simp at this; omega
    have hc2 : (Finset.univ.filter (fun x : Fin n => x ∉ P2)).card = n - P2.card := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (· ∈ P2)
      simp at this; omega
    rw [Fintype.card_subtype, Fintype.card_subtype, hc1, hc2, hcard]
  let e1 : {x : Fin n // x ∈ P1} ≃ {x : Fin n // x ∈ P2} := Fintype.equivOfCardEq h1
  let e2 : {x : Fin n // x ∉ P1} ≃ {x : Fin n // x ∉ P2} := Fintype.equivOfCardEq h2
  let s1 : Fin n ≃ {x : Fin n // x ∈ P1} ⊕ {x : Fin n // x ∉ P1} :=
    (Equiv.sumCompl (· ∈ P1)).symm
  let s2 : {x : Fin n // x ∈ P2} ⊕ {x : Fin n // x ∉ P2} ≃ Fin n :=
    Equiv.sumCompl (· ∈ P2)
  let π : Equiv.Perm (Fin n) := s1.trans ((Equiv.sumCongr e1 e2).trans s2)
  refine ⟨π, ?_⟩
  ext y
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change s2 (Equiv.sumCongr e1 e2 (s1 x)) ∈ P2
    have hs1 : s1 x = Sum.inl ⟨x, hx⟩ := by
      simp [s1, Equiv.sumCompl, hx]
    rw [hs1]
    exact (e1 ⟨x, hx⟩).2
  · intro hy
    refine ⟨(e1.symm ⟨y, hy⟩).1, (e1.symm ⟨y, hy⟩).2, ?_⟩
    change s2 (Equiv.sumCongr e1 e2 (s1 (e1.symm ⟨y, hy⟩).1)) = y
    have hs1 : s1 (e1.symm ⟨y, hy⟩).1 = Sum.inl (e1.symm ⟨y, hy⟩) := by
      simp [s1, Equiv.sumCompl, (e1.symm ⟨y, hy⟩).2]
    rw [hs1]
    simp [s2, Equiv.sumCompl]

private lemma card_fiber_eq_of_card_eq {n k : ℕ} {P1 P2 : Finset (Fin n)}
    (hcard : P1.card = P2.card) :
    ((goodFuns n k).filter (fun f => perFinset f = P1)).card =
      ((goodFuns n k).filter (fun f => perFinset f = P2)).card := by
  classical
  obtain ⟨π, hπ⟩ := exists_perm_map_eq hcard
  refine Finset.card_bij (fun f _ => fun y => π (f (π.symm y))) ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_filter, goodFuns, Finset.mem_univ, true_and] at hf ⊢
    exact ⟨by rw [depth1Card_conj]; exact hf.1, by rw [perFinset_conj, hf.2, hπ]⟩
  · intro f1 _ f2 _ heq
    funext x
    have := congrFun heq (π x)
    simp only [Equiv.symm_apply_apply] at this
    exact π.injective this
  · intro g hg
    simp only [Finset.mem_filter, goodFuns, Finset.mem_univ, true_and] at hg
    let f : Fin n → Fin n := fun x => π.symm (g (π x))
    have hfg : (fun y => π (f (π.symm y))) = g := by
      funext y; simp [f]
    refine ⟨f, ?_, hfg⟩
    simp only [Finset.mem_filter, goodFuns, Finset.mem_univ, true_and]
    constructor
    · rw [← depth1Card_conj π f, hfg]; exact hg.1
    · have h1 : (perFinset f).map π.toEmbedding = P2 := by
        rw [← perFinset_conj π f, hfg]; exact hg.2
      rw [← hπ] at h1
      ext x
      have hx : π x ∈ (perFinset f).map π.toEmbedding ↔ π x ∈ P1.map π.toEmbedding := by
        rw [h1]
      simpa using hx

open Classical in
private noncomputable def extendMap {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm {x : Fin n // x ∈ P}) (g : {x : Fin n // x ∉ P} → Fin n) :
    Fin n → Fin n :=
  fun x => if hx : x ∈ P then (σ ⟨x, hx⟩).1 else g ⟨x, hx⟩

private lemma extendMap_iter_mem {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm {x : Fin n // x ∈ P}) (g : {x : Fin n // x ∉ P} → Fin n) :
    ∀ (t : ℕ) (x : {x : Fin n // x ∈ P}),
      (extendMap P σ g)^[t] x.1 = ((σ ^ t) x).1 := by
  intro t
  induction t with
  | zero => intro x; simp
  | succ t ih =>
    intro x
    rw [Function.iterate_succ_apply', ih x]
    unfold extendMap
    rw [dif_pos ((σ ^ t) x).2]
    rw [pow_succ']
    rfl

private lemma mem_periodicPts_extendMap_of_mem {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm {x : Fin n // x ∈ P}) (g : {x : Fin n // x ∉ P} → Fin n)
    {x : Fin n} (hx : x ∈ P) :
    x ∈ Function.periodicPts (extendMap P σ g) := by
  refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
  change (extendMap P σ g)^[orderOf σ] x = x
  have h := extendMap_iter_mem P σ g (orderOf σ) ⟨x, hx⟩
  rw [pow_orderOf_eq_one] at h
  exact h

private lemma mem_periodicPts_extendMap_iff {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm {x : Fin n // x ∈ P}) (g : {x : Fin n // x ∉ P} → Fin n) (x : Fin n) :
    x ∈ Function.periodicPts (extendMap P σ g) ↔ x ∈ Function.periodicPts (extendMap P 1 g) := by
  have hstay : ∀ (τ : Equiv.Perm {x : Fin n // x ∈ P}) {y : Fin n} {p : ℕ},
      0 < p → y ∉ P → (extendMap P τ g)^[p] y = y →
      ∀ t : ℕ, (extendMap P τ g)^[t] y ∉ P := by
    intro τ y p hp hy hfix t ht
    have hmul : ∀ m : ℕ, (extendMap P τ g)^[m * p] y = y := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
        rw [Nat.succ_mul, Function.iterate_add_apply, hfix, ihm]
    have hge : ∀ s : ℕ, (extendMap P τ g)^[t + s] y ∈ P := by
      intro s
      rw [add_comm, Function.iterate_add_apply]
      have h1 := extendMap_iter_mem P τ g s ⟨(extendMap P τ g)^[t] y, ht⟩
      rw [h1]
      exact ((τ ^ s) _).2
    have htp : t ≤ t * p := Nat.le_mul_of_pos_right t hp
    have hin : (extendMap P τ g)^[t * p] y ∈ P := by
      have := hge (t * p - t)
      rwa [show t + (t * p - t) = t * p by omega] at this
    rw [hmul t] at hin
    exact hy hin
  have hagree : ∀ (τ1 τ2 : Equiv.Perm {x : Fin n // x ∈ P}) (y : Fin n),
      (∀ t : ℕ, (extendMap P τ1 g)^[t] y ∉ P) →
      ∀ t : ℕ, (extendMap P τ2 g)^[t] y = (extendMap P τ1 g)^[t] y := by
    intro τ1 τ2 y hnot t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      have hz : (extendMap P τ1 g)^[t] y ∉ P := hnot t
      generalize (extendMap P τ1 g)^[t] y = z at hz ⊢
      unfold extendMap
      rw [dif_neg hz, dif_neg hz]
  by_cases hx : x ∈ P
  · exact ⟨fun _ => mem_periodicPts_extendMap_of_mem P 1 g hx,
      fun _ => mem_periodicPts_extendMap_of_mem P σ g hx⟩
  · constructor
    · rintro ⟨p, hp, hfix⟩
      refine ⟨p, hp, ?_⟩
      change (extendMap P 1 g)^[p] x = x
      rw [hagree σ 1 x (hstay σ hp hx hfix) p]
      exact hfix
    · rintro ⟨p, hp, hfix⟩
      refine ⟨p, hp, ?_⟩
      change (extendMap P σ g)^[p] x = x
      rw [hagree 1 σ x (hstay 1 hp hx hfix) p]
      exact hfix

private lemma perFinset_extendMap {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm {x : Fin n // x ∈ P}) (g : {x : Fin n // x ∉ P} → Fin n) :
    perFinset (extendMap P σ g) = perFinset (extendMap P 1 g) := by
  classical
  ext x
  simp only [perFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_periodicPts_extendMap_iff P σ g x

private lemma depth1Card_extendMap {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm {x : Fin n // x ∈ P}) (g : {x : Fin n // x ∉ P} → Fin n) :
    depth1Card (extendMap P σ g) = depth1Card (extendMap P 1 g) := by
  classical
  unfold depth1Card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hx : x ∈ P
  · have h1 := mem_periodicPts_extendMap_of_mem P σ g hx
    have h2 := mem_periodicPts_extendMap_of_mem P 1 g hx
    simp [h1, h2]
  · have hstep : extendMap P σ g x = extendMap P 1 g x := by
      unfold extendMap; rw [dif_neg hx, dif_neg hx]
    rw [mem_periodicPts_extendMap_iff P σ g x, hstep,
        mem_periodicPts_extendMap_iff P σ g (extendMap P 1 g x)]

private lemma factorial_dvd_fiber_card {n k : ℕ} (P : Finset (Fin n)) :
    P.card.factorial ∣ ((goodFuns n k).filter (fun f => perFinset f = P)).card := by
  classical
  let G : Finset ({x : Fin n // x ∉ P} → Fin n) :=
    Finset.univ.filter fun g => extendMap P 1 g ∈ goodFuns n k ∧ perFinset (extendMap P 1 g) = P
  have hbij : ((goodFuns n k).filter (fun f => perFinset f = P)).card =
      ((Finset.univ : Finset (Equiv.Perm {x : Fin n // x ∈ P})) ×ˢ G).card := by
    symm
    refine Finset.card_bij (fun p _ => extendMap P p.1 p.2) ?_ ?_ ?_
    · rintro ⟨σ, g⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, true_and, G, Finset.mem_filter,
        goodFuns] at hp ⊢
      rw [depth1Card_extendMap, perFinset_extendMap]
      exact hp
    · rintro ⟨σ1, g1⟩ _ ⟨σ2, g2⟩ _ heq
      apply Prod.ext
      · ext ⟨x, hx⟩
        have h := congrFun heq x
        unfold extendMap at h
        rw [dif_pos hx, dif_pos hx] at h
        exact congrArg Fin.val h
      · funext ⟨x, hx⟩
        have h := congrFun heq x
        unfold extendMap at h
        rw [dif_neg hx, dif_neg hx] at h
        exact h
    · intro f hf
      simp only [Finset.mem_filter, goodFuns, Finset.mem_univ, true_and] at hf
      have hmaps : ∀ x : {x : Fin n // x ∈ P}, f x.1 ∈ P := by
        intro ⟨x, hx⟩
        have hpx : x ∈ Function.periodicPts f := by
          have : x ∈ perFinset f := hf.2.symm ▸ hx
          exact (Finset.mem_filter.mp this).2
        rcases hpx with ⟨p, hp, hfix⟩
        have hpf : f x ∈ Function.periodicPts f := by
          refine ⟨p, hp, ?_⟩
          change f^[p] (f x) = f x
          rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
          exact congrArg f hfix
        change f x ∈ P
        rw [← hf.2, perFinset, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hpf⟩
      let fP : {x : Fin n // x ∈ P} → {x : Fin n // x ∈ P} := fun x => ⟨f x.1, hmaps x⟩
      have hinj : Function.Injective fP := by
        intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
        have hfxy : f x = f y := congrArg Subtype.val hxy
        have hpx : x ∈ Function.periodicPts f := (Finset.mem_filter.mp (hf.2.symm ▸ hx)).2
        have hpy : y ∈ Function.periodicPts f := (Finset.mem_filter.mp (hf.2.symm ▸ hy)).2
        rcases hpx with ⟨p, hp, hfix_x⟩
        rcases hpy with ⟨q, hq, hfix_y⟩
        have hiter_mul : ∀ (z : Fin n) (r m : ℕ), f^[r] z = z → f^[m * r] z = z := by
          intro z r m hz
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [Nat.succ_mul, Function.iterate_add_apply, hz, ihm]
        have hx_pq : f^[q * p] x = x := hiter_mul x p q hfix_x
        have hy_pq : f^[p * q] y = y := hiter_mul y q p hfix_y
        have hpos : 0 < p * q := Nat.mul_pos hp hq
        have hstep : f^[p * q] x = f^[p * q] y := by
          have h1 : p * q = (p * q - 1) + 1 := by omega
          rw [h1, Function.iterate_succ_apply, Function.iterate_succ_apply, hfxy]
        apply Subtype.ext
        change x = y
        rw [← hx_pq, mul_comm q p, hstep, hy_pq]
      let σ : Equiv.Perm {x : Fin n // x ∈ P} :=
        Equiv.ofBijective fP (Finite.injective_iff_bijective.mp hinj)
      let g : {x : Fin n // x ∉ P} → Fin n := fun x => f x.1
      have hext : extendMap P σ g = f := by
        funext x
        unfold extendMap
        by_cases hx : x ∈ P
        · rw [dif_pos hx]; rfl
        · rw [dif_neg hx]
      refine ⟨(σ, g), ?_, hext⟩
      simp only [Finset.mem_product, Finset.mem_univ, true_and, G, Finset.mem_filter, goodFuns]
      rw [← depth1Card_extendMap P σ g, ← perFinset_extendMap P σ g, hext]
      exact hf
  rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_perm, Fintype.card_coe]
  exact dvd_mul_right _ _

private lemma main_proof : ∀ n k : ℕ, 0 < n → k < n →
    n ∣ {f : Fin n → Fin n |
      {x : Fin n | x ∉ Function.periodicPts f ∧ f x ∈ Function.periodicPts f}.ncard = k}.ncard := by
  intro n k hn _
  classical
  rw [ncard_eq_goodFuns_card]
  -- Partition goodFuns n k by P = perFinset f, grouped by m = P.card ∈ Icc 1 n
  have hpart : (goodFuns n k).card =
      ∑ m ∈ Finset.Icc 1 n,
        ∑ P ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun P => P.card = m),
          ((goodFuns n k).filter (fun f => perFinset f = P)).card := by
    have h1 : (goodFuns n k).card =
        ∑ P : Finset (Fin n), ((goodFuns n k).filter (fun f => perFinset f = P)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext f
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
        exact ⟨fun hf => ⟨perFinset f, hf, rfl⟩, fun ⟨_, hf, _⟩ => hf⟩
      · intro P1 _ P2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro f h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [h1]
    have hzero : ∀ P : Finset (Fin n), P.card ∉ Finset.Icc 1 n →
        ((goodFuns n k).filter (fun f => perFinset f = P)).card = 0 := by
      intro P hP
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro f _ heq
      have hne := perFinset_nonempty hn f
      rw [heq] at hne
      have hpos : 1 ≤ P.card := Finset.card_pos.mpr hne
      have hle : P.card ≤ n := by
        have := Finset.card_le_univ P
        simpa using this
      exact hP (Finset.mem_Icc.mpr ⟨hpos, hle⟩)
    let s : Finset (Finset (Fin n)) :=
      (Finset.univ : Finset (Finset (Fin n))).filter (fun P => P.card ∈ Finset.Icc 1 n)
    have hsum_s : (∑ P : Finset (Fin n), ((goodFuns n k).filter (fun f => perFinset f = P)).card) =
        ∑ P ∈ s, ((goodFuns n k).filter (fun f => perFinset f = P)).card := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun P _ => ?_
      by_cases hP : P.card ∈ Finset.Icc 1 n
      · rw [if_pos hP]
      · rw [if_neg hP, hzero P hP]
    rw [hsum_s]
    rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.Icc 1 n)
      (s := s) (fun P hP => (Finset.mem_filter.mp hP).2)]
    refine Finset.sum_congr rfl fun m hm => ?_
    congr 1
    ext P
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hm, h⟩⟩
  rw [hpart]
  refine Finset.dvd_sum fun m hm => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hmn : m ≤ n := (Finset.mem_Icc.mp hm).2
  let P0 : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => x.1 < m)
  have hP0_card : P0.card = m := by
    have hbij : P0.card = (Finset.univ : Finset (Fin m)).card := by
      refine Finset.card_bij (fun x hx => ⟨x.1, (Finset.mem_filter.mp hx).2⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => Fin.ext (Fin.mk.inj h))
        (fun y _ => ⟨⟨y.1, lt_of_lt_of_le y.2 hmn⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2⟩, rfl⟩)
    simpa using hbij
  have hconst : ∀ P ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun P => P.card = m),
      ((goodFuns n k).filter (fun f => perFinset f = P)).card =
        ((goodFuns n k).filter (fun f => perFinset f = P0)).card := by
    intro P hP
    exact card_fiber_eq_of_card_eq ((Finset.mem_filter.mp hP).2.trans hP0_card.symm)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  have hchoose : ((Finset.univ : Finset (Finset (Fin n))).filter (fun P => P.card = m)).card =
      n.choose m := by
    have h1 : (Finset.univ : Finset (Finset (Fin n))).filter (fun P => P.card = m) =
        Finset.powersetCard m (Finset.univ : Finset (Fin n)) := by
      ext P; simp [Finset.mem_powersetCard]
    rw [h1, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [hchoose]
  rcases factorial_dvd_fiber_card (n := n) (k := k) P0 with ⟨c, hc⟩
  rw [hP0_card] at hc
  rw [hc, ← mul_assoc]
  have hdvd : n ∣ n.choose m * m.factorial := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [Nat.succ_descFactorial_succ]
    exact dvd_mul_right _ _
  exact dvd_mul_of_dvd_left hdvd c

end OMA.S_oeis_a216971

theorem OMA.solution : type_of% @OMA.S_oeis_a216971.main :=
  OMA.S_oeis_a216971.main_proof
