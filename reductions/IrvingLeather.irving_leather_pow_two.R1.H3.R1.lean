import OMAReductions.R_IrvingLeather_irving_leather_pow_two_R1
import Mathlib.Tactic

/-!
# Interval schedules for the Irving–Leather upper bound

Thurber, Concerning the maximum number of stable matchings, §4, considers profiles
whose two sides rank pairs in opposite directions on a common score matrix.
Here a stable pair receives an interval with length equal to its frequency among
stable matchings. The conflict-of-interest comparison identifies its starting point
on the two sides. Rows and columns therefore tile the same timeline, and every
stable matching is admissible in the resulting table.

Endpoint compression gives at most n² time steps. Conversely, scoring each used
pair by its start and placing unused pairs after the timeline realizes every
admissible matching of the table in a complete strict profile.
-/

open StableMarriage

namespace OMA.R_IrvingLeather_irving_leather_pow_two_R1_H3_R1

variable {n : ℕ}

private theorem opposite (p : Profile n) {a b : Matching n}
    (ha : IsStable p a) (hb : IsStable p b) (m : Fin n) :
    p.manRank m (a m) < p.manRank m (b m) ↔
      p.womanRank (b m) m < p.womanRank (b m) (a.symm (b m)) := by
  classical
  let S := Finset.univ.filter (fun i => p.manRank i (a i) < p.manRank i (b i))
  let T := Finset.univ.filter (fun w => p.womanRank w (b.symm w) < p.womanRank w (a.symm w))
  have hST : S.image a ⊆ T := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have h : p.manRank i (a i) < p.manRank i (b i) := (Finset.mem_filter.mp hi).2
    have hn : b i ≠ a i := fun e => (ne_of_lt h) (congrArg (p.manRank i) e.symm)
    have hne : i ≠ b.symm (a i) := by
      intro e
      exact hn (by simpa using congrArg b e)
    have hle := not_lt.mp (fun hl => hb i (a i) ⟨hn, h, hl⟩)
    have hlt := lt_of_le_of_ne hle (fun e => hne ((p.womanRank (a i)).injective e.symm))
    simpa [T] using hlt
  have hTS : T.image b.symm ⊆ S := by
    intro i hi
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
    have h : p.womanRank w (b.symm w) < p.womanRank w (a.symm w) := (Finset.mem_filter.mp hw).2
    have hn : a (b.symm w) ≠ w := by
      intro e
      have he : b.symm w = a.symm w := by simpa using congrArg a.symm e
      exact (ne_of_lt h) (congrArg (p.womanRank w) he)
    have hle := not_lt.mp (fun hl => ha (b.symm w) w ⟨hn, hl, h⟩)
    have hlt := lt_of_le_of_ne hle (fun e => hn ((p.manRank (b.symm w)).injective e))
    simpa [S] using hlt
  have hc := Finset.card_le_card hST
  rw [Finset.card_image_of_injective _ a.injective] at hc
  have he : T.image b.symm = S := Finset.eq_of_subset_of_card_le hTS
    ((Finset.card_image_of_injective _ b.symm.injective).symm ▸ hc)
  have hm : m ∈ S ↔ b m ∈ T := by
    rw [← he]
    constructor
    · intro h
      obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp h
      have hw' : w = b m := by simpa using congrArg b hew
      simpa only [hw'] using hw
    · intro h
      exact Finset.mem_image.mpr ⟨b m, h, b.symm_apply_apply _⟩
  simpa [S, T] using hm

private theorem bins_partition {α : Type*} (s : Finset α) (f : α → Fin n) (i : Fin n) :
    (s.filter (fun a => f a ≤ i)).card =
      (s.filter (fun a => f a < i)).card + (s.filter (fun a => f a = i)).card := by
  classical
  have h : s.filter (fun a => f a < i) ∪ s.filter (fun a => f a = i) =
      s.filter (fun a => f a ≤ i) := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    rw [← and_or_left, le_iff_lt_or_eq]
  rw [← h, Finset.card_union_of_disjoint]
  refine Finset.disjoint_left.mpr (fun a ha hb => ?_)
  exact (ne_of_lt (Finset.mem_filter.mp ha).2) (Finset.mem_filter.mp hb).2

private theorem bins_unique {α : Type*} (s : Finset α) (f : α → Fin n) {t : ℕ}
    (ht : t < s.card) :
    ∃! i : Fin n, (s.filter (fun a => f a < i)).card ≤ t ∧
      t < (s.filter (fun a => f a < i)).card + (s.filter (fun a => f a = i)).card := by
  classical
  have h : ∃ i : ℕ, t < (s.filter (fun a => (f a).val ≤ i)).card := by
    refine ⟨n, ?_⟩
    simpa only [Finset.filter_eq_self.mpr (fun a _ => (f a).isLt.le)] using ht
  let j := Nat.find h
  have hj : t < (s.filter (fun a => (f a).val ≤ j)).card := Nat.find_spec h
  have hpos : 0 < (s.filter (fun a => (f a).val ≤ j)).card := Nat.zero_lt_of_lt hj
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  have hupper : ∃ b ∈ s, j ≤ (f b).val := by
    by_contra! hn
    have hjpos : 0 < j := Nat.zero_lt_of_lt (hn a (Finset.mem_filter.mp ha).1)
    have hall : s.filter (fun b => (f b).val ≤ j - 1) = s := by
      refine Finset.filter_eq_self.mpr fun b hb => ?_
      have := hn b hb
      omega
    have hmin := Nat.find_min' h (show t < (s.filter (fun b => (f b).val ≤ j - 1)).card from
      hall.symm ▸ ht)
    change j ≤ j - 1 at hmin
    omega
  obtain ⟨b, _, hb⟩ := hupper
  let i : Fin n := ⟨j, hb.trans_lt (f b).isLt⟩
  have hleft : (s.filter (fun a => f a < i)).card ≤ t := by
    by_contra! hh
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hh)
    have hlt : (f a).val < j := (Finset.mem_filter.mp ha).2
    have he : s.filter (fun b => f b < i) = s.filter (fun b => (f b).val ≤ j - 1) := by
      ext b
      have : (f b).val < j ↔ (f b).val ≤ j - 1 := by omega
      simp only [Finset.mem_filter, Fin.lt_def, i, this]
    rw [he] at hh
    have hmin := Nat.find_min' h hh
    change j ≤ j - 1 at hmin
    omega
  have hright : t < (s.filter (fun a => f a < i)).card +
      (s.filter (fun a => f a = i)).card := by
    rw [← bins_partition]
    exact hj
  refine ⟨i, ⟨hleft, hright⟩, fun k hk => ?_⟩
  have horder {a b : Fin n} (hab : a < b) :
      (s.filter (fun x => f x < a)).card + (s.filter (fun x => f x = a)).card ≤
        (s.filter (fun x => f x < b)).card := by
    rw [← bins_partition]
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hx).1, ((Finset.mem_filter.mp hx).2).trans_lt hab⟩
  rcases lt_trichotomy k i with hki | he | hik
  · exact False.elim ((not_lt_of_ge ((horder hki).trans hleft)) hk.2)
  · exact he
  · exact False.elim ((not_lt_of_ge ((horder hik).trans hk.1)) hright)

private theorem strict_bin_start {α : Type*} (s : Finset α) (f : α → Fin n)
    {i j : Fin n} (h : i < j) (hi : ∃ a ∈ s, f a = i) :
    (s.filter (fun a => f a < i)).card < (s.filter (fun a => f a < j)).card := by
  classical
  apply Finset.card_lt_card
  have hs : s.filter (fun a => f a < i) ⊆ s.filter (fun a => f a < j) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, ((Finset.mem_filter.mp ha).2).trans h⟩
  obtain ⟨a, ha, hea⟩ := hi
  exact (Finset.ssubset_iff_of_subset hs).mpr ⟨a, by simp [ha, hea, h], by simp [hea]⟩

/-- Each attained pair occupies one common interval on its row and column. -/
theorem exists_interval_schedule (p : Profile n) :
    ∃ (T : ℕ) (start duration : Fin n → Fin n → ℕ),
      (∀ m w, start m w + duration m w ≤ T) ∧
      (∀ t < T,
        (∀ m, ∃! w, start m w ≤ t ∧ t < start m w + duration m w) ∧
        (∀ w, ∃! m, start m w ≤ t ∧ t < start m w + duration m w)) ∧
      numStableMatchings p ≤
        {a : Matching n | (∀ m, 0 < duration m (a m)) ∧
          ∀ m w, 0 < duration m w → start m w < start m (a m) →
            start m w ≤ start (a.symm w) w}.ncard := by
  classical
  let s : Finset (Matching n) := Finset.univ.filter (IsStable p)
  let row (m : Fin n) (a : Matching n) := p.manRank m (a m)
  let colRank (w : Fin n) : Equiv.Perm (Fin n) := (p.womanRank w).trans Fin.revPerm
  let col (w : Fin n) (a : Matching n) := colRank w (a.symm w)
  let start (m w : Fin n) := (s.filter (fun a => row m a < p.manRank m w)).card
  let duration (m w : Fin n) := (s.filter (fun a => a m = w)).card
  have hcount : s.card = numStableMatchings p := (Fintype.card_subtype (IsStable p)).symm
  have hrow (m w : Fin n) : s.filter (fun a => row m a = p.manRank m w) =
      s.filter (fun a => a m = w) := by
    ext a
    simp [row, (p.manRank m).injective.eq_iff]
  have hcol (m w : Fin n) : s.filter (fun a => col w a = colRank w m) =
      s.filter (fun a => a m = w) := by
    ext a
    simp only [Finset.mem_filter, col, (colRank w).injective.eq_iff, Equiv.symm_apply_eq,
      eq_comm (a := w) (b := a m)]
  have hstart {m w : Fin n} (h : 0 < duration m w) :
      start m w = (s.filter (fun a => col w a < colRank w m)).card := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp h
    obtain ⟨hb', he⟩ := Finset.mem_filter.mp hb
    have hbs : IsStable p b := (Finset.mem_filter.mp hb').2
    apply congrArg Finset.card
    ext a
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro ha
    have haa : IsStable p a := (Finset.mem_filter.mp ha).2
    subst w
    exact (opposite p haa hbs m).trans Fin.rev_lt_rev.symm
  refine ⟨s.card, start, duration, ?_, ?_, ?_⟩
  · intro m w
    change (s.filter (fun a => row m a < p.manRank m w)).card +
      (s.filter (fun a => a m = w)).card ≤ s.card
    rw [← hrow m w, ← bins_partition]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  · intro t ht
    constructor
    · intro m
      apply (Equiv.existsUnique_congr (p.manRank m) ?_).mpr (bins_unique s (row m) ht)
      intro w
      rw [hrow m w]
    · intro w
      apply (Equiv.existsUnique_congr (colRank w) ?_).mpr (bins_unique s (col w) ht)
      intro m
      by_cases h : 0 < duration m w
      · rw [hcol m w]
        rw [hstart h]
      · have hz : duration m w = 0 := Nat.eq_zero_of_not_pos h
        rw [hcol m w]
        change (start m w ≤ t ∧ t < start m w + duration m w) ↔
          (s.filter (fun a => col w a < colRank w m)).card ≤ t ∧
          t < (s.filter (fun a => col w a < colRank w m)).card + duration m w
        simp only [hz, Nat.add_zero]
        exact ⟨fun h' => (not_lt_of_ge h'.1 h'.2).elim,
          fun h' => (not_lt_of_ge h'.1 h'.2).elim⟩
  · rw [← hcount]
    have hc : (s : Set (Matching n)).ncard = s.card := by simp
    rw [← hc]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro a ha
    have has : IsStable p a := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hlen (m : Fin n) : 0 < duration m (a m) :=
      Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
    have hlen' (w : Fin n) : 0 < duration (a.symm w) w := by
      simpa only [a.apply_symm_apply] using hlen (a.symm w)
    refine ⟨hlen, ?_⟩
    intro m w hw hlt
    by_contra! hblock
    have hne : a m ≠ w := by
      intro e
      exact (lt_irrefl _) (e ▸ hlt)
    have hman : p.manRank m w < p.manRank m (a m) := by
      refine lt_of_not_ge fun hge => ?_
      have hstrict := lt_of_le_of_ne hge (fun h => hne ((p.manRank m).injective h))
      have hlt' := strict_bin_start s (row m) hstrict ⟨a, ha, rfl⟩
      exact not_lt_of_gt hlt' hlt
    have hwoman : p.womanRank w m < p.womanRank w (a.symm w) := by
      refine lt_of_not_ge fun hge => ?_
      have hneq : a.symm w ≠ m := by
        intro e
        exact hne ((a.symm_apply_eq.mp e).symm)
      have hstrict := lt_of_le_of_ne hge (fun h => hneq ((p.womanRank w).injective h))
      have hrev : colRank w m < colRank w (a.symm w) := Fin.rev_lt_rev.mpr hstrict
      have hlt' := strict_bin_start s (col w) hrev (by
        obtain ⟨b, hb⟩ := Finset.card_pos.mp hw
        obtain ⟨hb', he⟩ := Finset.mem_filter.mp hb
        exact ⟨b, hb', congrArg (colRank w) ((b.eq_symm_apply.mpr he).symm)⟩)
      rw [hstart hw, hstart (hlen' w)] at hblock
      exact not_lt_of_gt hlt' hblock
    exact has m w ⟨hne, hman, hwoman⟩

private theorem exists_sorted_rank {α : Type*} [LinearOrder α] (f : Fin n → α)
    (hf : Function.Injective f) :
    ∃ r : Equiv.Perm (Fin n), ∀ i j, r i < r j ↔ f i < f j := by
  classical
  let s := Finset.univ.image f
  have hs : s.card = n := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  let g : Fin n ≃ s := Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_image_of_mem f (Finset.mem_univ i)⟩)
    ⟨fun _ _ h => hf (congrArg Subtype.val h), by
      intro y
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp y.property
      exact ⟨i, Subtype.ext hi⟩⟩
  let order := (s.orderIsoOfFin hs).symm
  exact ⟨g.trans order.toEquiv, fun _ _ => order.lt_iff_lt⟩

private theorem lt_weighted_key {N a b i j : ℕ} (hi : i < N) (h : a < b) :
    a * N + i < b * N + j := by
  have hm := Nat.mul_le_mul_right N (Nat.succ_le_of_lt h)
  rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hm
  omega

private theorem exists_scored_profile (weight : Fin n × Fin n → ℕ) :
    ∃ p : Profile n,
      (∀ m w v, weight (m, w) < weight (m, v) → p.manRank m w < p.manRank m v) ∧
      (∀ w m i, weight (m, w) < weight (i, w) → p.womanRank w i < p.womanRank w m) := by
  classical
  let key (e : Fin n × Fin n) := weight e * (n * n) + (finProdFinEquiv e).val
  have hkey {e f : Fin n × Fin n} (h : weight e < weight f) : key e < key f :=
    lt_weighted_key (finProdFinEquiv e).isLt h
  have hinj : Function.Injective key := by
    intro e f h
    have hw : weight e = weight f :=
      le_antisymm (le_of_not_gt fun hl => (ne_of_lt (hkey hl)) h.symm)
        (le_of_not_gt fun hl => (ne_of_lt (hkey hl)) h)
    unfold key at h
    rw [hw] at h
    exact finProdFinEquiv.injective (Fin.ext (Nat.add_left_cancel h))
  have mr m := exists_sorted_rank (fun w : Fin n => key (m, w))
    (fun _ _ h => congrArg Prod.snd (hinj h))
  have wr w := exists_sorted_rank (fun m : Fin n => key (m, w))
    (fun _ _ h => congrArg Prod.fst (hinj h))
  choose mRank hm using mr
  choose wRank hw using wr
  refine ⟨⟨mRank, fun w => (wRank w).trans Fin.revPerm⟩, ?_, ?_⟩
  · intro m w v h
    exact (hm m w v).mpr (hkey h)
  · intro w m i h
    exact Fin.rev_lt_rev.mpr ((hw w m i).mpr (hkey h))

private theorem starts_ne {α : Type*} {T : ℕ} (start duration : α → ℕ)
    (hbound : ∀ a, start a + duration a ≤ T)
    (htiling : ∀ t < T, ∃! a, start a ≤ t ∧ t < start a + duration a)
    {a b : α} (ha : 0 < duration a) (hb : 0 < duration b) (hne : a ≠ b) :
    start a ≠ start b := by
  intro he
  have hta : start a < start a + duration a := Nat.lt_add_of_pos_right ha
  have htb : start b < start b + duration b := Nat.lt_add_of_pos_right hb
  obtain ⟨c, _, hu⟩ := htiling (start a) (hta.trans_le (hbound a))
  exact hne ((hu a ⟨le_rfl, hta⟩).trans (hu b ⟨he.ge, he ▸ htb⟩).symm)

/-- Every admissible matching of an interval schedule survives in a common-score profile. -/
theorem interval_schedule_realized {T : ℕ} (start duration : Fin n → Fin n → ℕ)
    (hbound : ∀ m w, start m w + duration m w ≤ T)
    (htiling : ∀ t < T,
      (∀ m, ∃! w, start m w ≤ t ∧ t < start m w + duration m w) ∧
      (∀ w, ∃! m, start m w ≤ t ∧ t < start m w + duration m w)) :
    ∃ p : Profile n,
      {a : Matching n | (∀ m, 0 < duration m (a m)) ∧
        ∀ m w, 0 < duration m w → start m w < start m (a m) →
          start m w ≤ start (a.symm w) w}.ncard ≤ numStableMatchings p := by
  classical
  let weight (e : Fin n × Fin n) := if 0 < duration e.1 e.2 then start e.1 e.2 else T
  obtain ⟨p, hm, hw⟩ := exists_scored_profile weight
  refine ⟨p, ?_⟩
  have hcount : {a : Matching n | IsStable p a}.ncard = numStableMatchings p := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    rfl
  rw [← hcount]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro a ha m w hab
  obtain ⟨hne, hmb, hwb⟩ := hab
  have hwa : 0 < duration (a.symm w) w := by simpa using ha.1 (a.symm w)
  have hwp : weight (m, a m) < T := by
    simpa [weight, ha.1 m] using
      (Nat.lt_add_of_pos_right (ha.1 m)).trans_le (hbound m (a m))
  have hwr : weight (m, w) ≤ weight (m, a m) :=
    le_of_not_gt (fun hgt => (not_lt_of_gt (hm m (a m) w hgt)) hmb)
  have hd : 0 < duration m w := by
    by_contra h
    have hz : weight (m, w) = T := by simp [weight, h]
    exact (ne_of_lt (hwr.trans_lt hwp)) hz
  have hrle : start m w ≤ start m (a m) := by simpa [weight, hd, ha.1 m] using hwr
  have hrne := starts_ne (start m) (duration m) (hbound m)
    (fun t ht => (htiling t ht).1 m) hd (ha.1 m) hne.symm
  have hcle : start (a.symm w) w ≤ start m w := by
    refine le_of_not_gt (fun hgt => (not_lt_of_gt (hw w m (a.symm w) ?_)) hwb)
    simpa [weight, hd, hwa] using hgt
  have hcne : a.symm w ≠ m := fun h => hne (a.eq_symm_apply.mp h.symm)
  have hdne := starts_ne (fun i => start i w) (fun i => duration i w) (fun i => hbound i w)
    (fun t ht => (htiling t ht).2 w) hwa hd hcne
  exact (not_lt_of_ge (ha.2 m w hd (lt_of_le_of_ne hrle hrne))) (lt_of_le_of_ne hcle hdne)

/-- Relabel endpoints in their increasing order. With at most one start per cell, the new
time horizon is at most the number of cells. -/
private theorem compress_intervals {T : ℕ} (start duration : Fin n → Fin n → ℕ)
    (hbound : ∀ m w, start m w + duration m w ≤ T)
    (htiling : ∀ t < T,
      (∀ m, ∃! w, start m w ≤ t ∧ t < start m w + duration m w) ∧
      (∀ w, ∃! m, start m w ≤ t ∧ t < start m w + duration m w)) :
    ∃ (U : ℕ) (s d : Fin n → Fin n → ℕ),
      U ≤ n * n ∧
      (∀ m w, s m w + d m w ≤ U) ∧
      (∀ t < U,
        (∀ m, ∃! w, s m w ≤ t ∧ t < s m w + d m w) ∧
        (∀ w, ∃! m, s m w ≤ t ∧ t < s m w + d m w)) ∧
      {a : Matching n | (∀ m, 0 < duration m (a m)) ∧
        ∀ m w, 0 < duration m w → start m w < start m (a m) →
          start m w ≤ start (a.symm w) w} =
      {a : Matching n | (∀ m, 0 < d m (a m)) ∧
        ∀ m w, 0 < d m w → s m w < s m (a m) → s m w ≤ s (a.symm w) w} := by
  classical
  let cells := Finset.univ.filter (fun e : Fin n × Fin n => 0 < duration e.1 e.2)
  let points := insert T (cells.image (fun e => start e.1 e.2))
  have hT : T ∈ points := Finset.mem_insert_self _ _
  have hs {m w} (h : 0 < duration m w) : start m w ∈ points :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem
      (fun e => start e.1 e.2) (Finset.mem_filter.mpr ⟨Finset.mem_univ (m, w), h⟩))
  have he {m w} (h : 0 < duration m w) : start m w + duration m w ∈ points := by
    let t := start m w + duration m w
    change t ∈ points
    by_cases ht : t = T
    · exact ht.symm ▸ hT
    have ht' : t < T := lt_of_le_of_ne (hbound m w) ht
    obtain ⟨v, hv, _⟩ := (htiling t ht').1 m
    have hnv : v ≠ w := by
      intro hvw
      have hv' := hv.2
      rw [hvw] at hv'
      exact (lt_irrefl t) hv'
    have hvs : start m v = t := by
      refine le_antisymm hv.1 (le_of_not_gt fun hlt => ?_)
      have hu : t - 1 < T := by omega
      obtain ⟨u, _, huniq⟩ := (htiling (t - 1) hu).1 m
      have hv' : start m v ≤ t - 1 ∧ t - 1 < start m v + duration m v :=
        ⟨by omega, by have := hv.2; omega⟩
      have hw' : start m w ≤ t - 1 ∧ t - 1 < start m w + duration m w := by
        dsimp [t]
        omega
      exact hnv ((huniq v hv').trans (huniq w hw').symm)
    have hd : 0 < duration m v := by have := hv.2; omega
    exact hvs ▸ hs hd
  have hcard : points.card ≤ n * n + 1 := by
    calc
      points.card ≤ (cells.image (fun e => start e.1 e.2)).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ cells.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ n * n + 1 := Nat.add_le_add_right (by simpa using Finset.card_le_univ cells) 1
  let order := points.orderIsoOfFin (k := points.card) rfl
  let rank (t : ℕ) := if h : t ∈ points then (order.symm ⟨t, h⟩).val else 0
  have hrank {t} (h : t ∈ points) : rank t = (order.symm ⟨t, h⟩).val := by simp [rank, h]
  have hrank_lt {t u} (ht : t ∈ points) (hu : u ∈ points) : rank t < rank u ↔ t < u := by
    rw [hrank ht, hrank hu]
    exact order.symm.lt_iff_lt
  have hrank_le {t u} (ht : t ∈ points) (hu : u ∈ points) : rank t ≤ rank u ↔ t ≤ u := by
    simpa only [not_lt] using not_congr (hrank_lt hu ht)
  have htop : rank T < points.card := (hrank hT).symm ▸ (order.symm ⟨T, hT⟩).isLt
  let s (m w : Fin n) := if 0 < duration m w then rank (start m w) else 0
  let d (m w : Fin n) := if 0 < duration m w then
    rank (start m w + duration m w) - rank (start m w) else 0
  have hvals {m w} (h : 0 < duration m w) :
      s m w = rank (start m w) ∧ s m w + d m w = rank (start m w + duration m w) ∧
        0 < d m w := by
    have hlt := (hrank_lt (hs h) (he h)).mpr (Nat.lt_add_of_pos_right h)
    simp only [s, d, if_pos h]
    exact ⟨True.intro, Nat.add_sub_of_le hlt.le, Nat.sub_pos_of_lt hlt⟩
  have hpos {m w} : 0 < d m w ↔ 0 < duration m w := by
    by_cases h : 0 < duration m w
    · exact iff_of_true (hvals h).2.2 h
    · simp [d, h]
  have hactive {t} (ht : t ∈ points) (m w : Fin n) :
      (s m w ≤ rank t ∧ rank t < s m w + d m w) ↔
      (start m w ≤ t ∧ t < start m w + duration m w) := by
    by_cases hd : 0 < duration m w
    · rw [(hvals hd).2.1, (hvals hd).1, hrank_le (hs hd) ht, hrank_lt ht (he hd)]
    · have hz : duration m w = 0 := Nat.eq_zero_of_not_pos hd
      simp only [s, d, if_neg hd, hz, Nat.add_zero]
      omega
  refine ⟨rank T, s, d, by omega, ?_, ?_, ?_⟩
  · intro m w
    by_cases h : 0 < duration m w
    · rw [(hvals h).2.1, hrank_le (he h) hT]
      exact hbound m w
    · simp [s, d, h]
  · intro u hu
    let j : Fin points.card := ⟨u, hu.trans htop⟩
    let t := order j
    have ht : rank t.val = u := by rw [hrank t.property]; simp [t, j]
    have ht' : t.val < T := (hrank_lt t.property hT).mp (ht.symm ▸ hu)
    rw [← ht]
    simpa only [hactive t.property] using htiling t.val ht'
  · ext a
    simp only [Set.mem_ofPred_eq, hpos]
    apply and_congr_right
    intro ha
    refine forall_congr' (fun m => forall_congr' (fun w => imp_congr_right (fun hd => ?_)))
    have hw : 0 < duration (a.symm w) w := by simpa using ha (a.symm w)
    rw [(hvals hd).1, (hvals (ha m)).1, (hvals hw).1, hrank_lt (hs hd) (hs (ha m)),
      hrank_le (hs hd) (hs hw)]

/-- The schedule bound at size eight. -/
def H1 : Prop :=
  ∀ (T : ℕ) (start duration : Fin 8 → Fin 8 → ℕ), T ≤ 64 →
    (∀ m w, start m w + duration m w ≤ T) →
    (∀ t < T,
      (∀ m, ∃! w, start m w ≤ t ∧ t < start m w + duration m w) ∧
      (∀ w, ∃! m, start m w ≤ t ∧ t < start m w + duration m w)) →
    {a : Matching 8 | (∀ m, 0 < duration m (a m)) ∧
      ∀ m w, 0 < duration m w → start m w < start m (a m) →
        start m w ≤ start (a.symm w) w}.ncard ≤ 268

/-- The schedule bound at the larger powers of two. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∀ (T : ℕ) (start duration : Fin (2 ^ k) → Fin (2 ^ k) → ℕ),
      T ≤ (2 ^ k) * (2 ^ k) →
      (∀ m w, start m w + duration m w ≤ T) →
      (∀ t < T,
        (∀ m, ∃! w, start m w ≤ t ∧ t < start m w + duration m w) ∧
        (∀ w, ∃! m, start m w ≤ t ∧ t < start m w + duration m w)) →
      {a : Matching (2 ^ k) | (∀ m, 0 < duration m (a m)) ∧
        ∀ m w, 0 < duration m w → start m w < start m (a m) →
          start m w ≤ start (a.symm w) w}.ncard ≤ IrvingLeather.irvingLeatherCount k

theorem main : H1 → H2 → OMA.R_IrvingLeather_irving_leather_pow_two_R1.H3 := by
  intro h1 h2 k hk p
  obtain ⟨T, start, duration, hb, ht, hc⟩ := exists_interval_schedule p
  obtain ⟨U, s, d, hU, hb', ht', he⟩ := compress_intervals start duration hb ht
  rw [he] at hc
  by_cases h : k = 3
  · subst k
    exact hc.trans (h1 U s d hU hb' ht')
  · exact hc.trans (h2 k (by omega) U s d hU hb' ht')

/-- A violation of either schedule bound gives a preference profile violating the same bound. -/
theorem interval_bounds_iff :
    (H1 ∧ H2) ↔ OMA.R_IrvingLeather_irving_leather_pow_two_R1.H3 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact main h1 h2
  · intro h
    constructor
    · intro T start duration _ hb ht
      obtain ⟨p, hp⟩ := interval_schedule_realized start duration hb ht
      exact hp.trans (h 3 (by decide) p)
    · intro k hk T start duration _ hb ht
      obtain ⟨p, hp⟩ := interval_schedule_realized start duration hb ht
      exact hp.trans (h k (by omega) p)

end OMA.R_IrvingLeather_irving_leather_pow_two_R1_H3_R1
