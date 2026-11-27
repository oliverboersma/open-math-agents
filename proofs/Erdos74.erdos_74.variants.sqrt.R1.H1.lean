import OMAReductions.R_Erdos74_erdos_74_variants_sqrt_R1
import Mathlib

-- Step Erdos74.erdos_74.variants.sqrt.R1.H1: hypothesis H1 of reduction Erdos74.erdos_74.variants.sqrt.R1
-- Credit: @preternatural-tocsin
-- Proved via the Expanding Cone over S^1 (odd cycle base, exponential doubling layers, apex).

namespace H1Proof

lemma add_mod_eq (a b n : ℕ) (ha : a < n) (hb : b ≤ n) :
    (a + b) % n = if a + b < n then a + b else a + b - n := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

def layerSize (M j : ℕ) : ℕ := 2 ^ j * M

abbrev ExpV (M R : ℕ) := Option (Σ j : Fin (R + 1), Fin (layerSize M j.1))

lemma layerSize_pos {M : ℕ} (hM : 0 < M) (j : ℕ) : 0 < layerSize M j :=
  Nat.mul_pos (by positivity) hM

lemma layerSize_succ (M j : ℕ) : layerSize M (j + 1) = 2 * layerSize M j := by
  simp [layerSize, pow_succ, mul_comm, mul_left_comm]

def betweenAdj (L : ℕ) (i : Fin L) (k : Fin (2 * L)) : Prop :=
  k.1 = (2 * i.1 + L - 1) % (2 * L) ∨
  k.1 = (2 * i.1 + L) % (2 * L) ∨
  k.1 = (2 * i.1 + L + 1) % (2 * L)

def baseAdj (m : ℕ) (i j : Fin (2 * m + 1)) : Prop :=
  j.1 = (i.1 + m) % (2 * m + 1) ∨ j.1 = (i.1 + m + 1) % (2 * m + 1)

lemma baseAdj_symm (m : ℕ) (i j : Fin (2 * m + 1)) (h : baseAdj m i j) : baseAdj m j i := by
  have hi := i.2
  have hj := j.2
  have h1 : (i.1 + m) % (2 * m + 1) = if i.1 + m < 2 * m + 1 then i.1 + m else i.1 + m - (2 * m + 1) :=
    add_mod_eq i.1 m (2 * m + 1) hi (by omega)
  have h2 : (i.1 + m + 1) % (2 * m + 1) =
      if i.1 + (m + 1) < 2 * m + 1 then i.1 + (m + 1) else i.1 + (m + 1) - (2 * m + 1) := by
    rw [Nat.add_assoc]; exact add_mod_eq i.1 (m + 1) (2 * m + 1) hi (by omega)
  have h3 : (j.1 + m) % (2 * m + 1) = if j.1 + m < 2 * m + 1 then j.1 + m else j.1 + m - (2 * m + 1) :=
    add_mod_eq j.1 m (2 * m + 1) hj (by omega)
  have h4 : (j.1 + m + 1) % (2 * m + 1) =
      if j.1 + (m + 1) < 2 * m + 1 then j.1 + (m + 1) else j.1 + (m + 1) - (2 * m + 1) := by
    rw [Nat.add_assoc]; exact add_mod_eq j.1 (m + 1) (2 * m + 1) hj (by omega)
  rcases h with h | h
  · right; rw [h4]; rw [h1] at h; split_ifs at h ⊢ <;> omega
  · left; rw [h3]; rw [h2] at h; split_ifs at h ⊢ <;> omega

lemma baseAdj_irrefl (m : ℕ) (hm : 1 ≤ m) (i : Fin (2 * m + 1)) : ¬ baseAdj m i i := by
  have hi := i.2
  have h1 : (i.1 + m) % (2 * m + 1) = if i.1 + m < 2 * m + 1 then i.1 + m else i.1 + m - (2 * m + 1) :=
    add_mod_eq i.1 m (2 * m + 1) hi (by omega)
  have h2 : (i.1 + m + 1) % (2 * m + 1) =
      if i.1 + (m + 1) < 2 * m + 1 then i.1 + (m + 1) else i.1 + (m + 1) - (2 * m + 1) := by
    rw [Nat.add_assoc]; exact add_mod_eq i.1 (m + 1) (2 * m + 1) hi (by omega)
  rintro (h | h)
  · rw [h1] at h; split_ifs at h <;> omega
  · rw [h2] at h; split_ifs at h <;> omega

def expGraph (m R : ℕ) (hm : 1 ≤ m) : SimpleGraph (ExpV (2 * m + 1) R) where
  Adj u v := match u, v with
    | none, none => False
    | none, some ⟨j, _⟩ => j.1 = R
    | some ⟨j, _⟩, none => j.1 = R
    | some ⟨j1, i1⟩, some ⟨j2, i2⟩ =>
      if h0 : j1.1 = 0 ∧ j2.1 = 0 then
        baseAdj m
          ⟨i1.1, lt_of_lt_of_eq i1.2 (by rw [h0.1]; simp [layerSize])⟩
          ⟨i2.1, lt_of_lt_of_eq i2.2 (by rw [h0.2]; simp [layerSize])⟩
      else if h12 : j2.1 = j1.1 + 1 then
        betweenAdj (layerSize (2 * m + 1) j1.1) i1
          ⟨i2.1, lt_of_lt_of_eq i2.2 (by rw [h12, layerSize_succ])⟩
      else if h21 : j1.1 = j2.1 + 1 then
        betweenAdj (layerSize (2 * m + 1) j2.1) i2
          ⟨i1.1, lt_of_lt_of_eq i1.2 (by rw [h21, layerSize_succ])⟩
      else False
  symm := by
    constructor
    intro u v huv
    match u, v with
    | none, none => exact huv
    | none, some ⟨j, _⟩ => exact huv
    | some ⟨j, _⟩, none => exact huv
    | some ⟨j1, i1⟩, some ⟨j2, i2⟩ =>
      dsimp only at huv ⊢
      split_ifs at huv with h0 h12 h21
      · have h0' : j2.1 = 0 ∧ j1.1 = 0 := ⟨h0.2, h0.1⟩
        rw [dif_pos h0']
        exact baseAdj_symm m _ _ huv
      · have h0' : ¬ (j2.1 = 0 ∧ j1.1 = 0) := by omega
        have h12' : ¬ (j1.1 = j2.1 + 1) := by omega
        rw [dif_neg h0', dif_neg h12', dif_pos h12]
        exact huv
      · have h0' : ¬ (j2.1 = 0 ∧ j1.1 = 0) := by omega
        rw [dif_neg h0', dif_pos h21]
        exact huv
  loopless := by
    constructor
    intro u hu
    match u with
    | none => exact hu
    | some ⟨j, i⟩ =>
      dsimp only at hu
      split_ifs at hu with h0 h12
      · exact baseAdj_irrefl m hm _ hu
      · omega

def delta (a b : Fin 3) : ℤ :=
  if a = b then 0
  else if (a.1 + 1) % 3 = b.1 then 1
  else -1

lemma delta_antisymm (a b : Fin 3) : delta a b = - delta b a := by
  fin_cases a <;> fin_cases b <;> decide

lemma delta_identity (a u v : Fin 3) (hu : a ≠ u) (hv : a ≠ v) :
    2 * delta u v = delta a u - delta a v := by
  fin_cases a <;> fin_cases u <;> fin_cases v <;> simp_all [delta]

lemma delta_odd_of_ne (a b : Fin 3) (h : a ≠ b) : delta a b % 2 = 1 := by
  fin_cases a <;> fin_cases b <;> simp_all [delta]

def nextFin {L : ℕ} (hL : 0 < L) (i : Fin L) : Fin L :=
  ⟨(i.1 + 1) % L, Nat.mod_lt _ hL⟩

def wind {L : ℕ} (hL : 0 < L) (f : Fin L → Fin 3) : ℤ :=
  ∑ i : Fin L, delta (f i) (f (nextFin hL i))

lemma nextFin_bijective {L : ℕ} (hL : 0 < L) : Function.Bijective (nextFin hL) := by
  rw [← Finite.injective_iff_bijective]
  intro a b hab
  ext
  have ha := a.2; have hb := b.2
  have hval : (a.1 + 1) % L = (b.1 + 1) % L := congrArg Fin.val hab
  rw [add_mod_eq a.1 1 L ha (by omega), add_mod_eq b.1 1 L hb (by omega)] at hval
  split_ifs at hval <;> omega

lemma sum_sub_nextFin {L : ℕ} (hL : 0 < L) (g : Fin L → ℤ) :
    ∑ i : Fin L, (g i - g (nextFin hL i)) = 0 := by
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact (Fintype.sum_equiv (Equiv.ofBijective (nextFin hL) (nextFin_bijective hL))
    (fun i => g (nextFin hL i)) g (fun _ => rfl)).symm

lemma wind_eq_zero_of_avoid {L : ℕ} (hL : 0 < L) (f : Fin L → Fin 3) (c0 : Fin 3)
    (havoid : ∀ i, c0 ≠ f i) : wind hL f = 0 := by
  have h2 : 2 * wind hL f = 0 := by
    unfold wind
    rw [Finset.mul_sum]
    calc ∑ i : Fin L, 2 * delta (f i) (f (nextFin hL i))
        = ∑ i : Fin L, (delta c0 (f i) - delta c0 (f (nextFin hL i))) :=
          Finset.sum_congr rfl fun i _ =>
            delta_identity c0 (f i) (f (nextFin hL i)) (havoid i) (havoid _)
      _ = 0 := sum_sub_nextFin hL (fun i => delta c0 (f i))
  omega

lemma wind_step {L : ℕ} (hL : 0 < L) (f0 : Fin L → Fin 3) (f1 : Fin (2 * L) → Fin 3)
    (hadj : ∀ (i : Fin L) (k : Fin (2 * L)), betweenAdj L i k → f0 i ≠ f1 k) :
    wind (by omega : 0 < 2 * L) f1 = wind hL f0 := by
  have h2L : 0 < 2 * L := by omega
  let x : Fin L → Fin (2 * L) := fun i => ⟨(2 * i.1 + L - 1) % (2 * L), Nat.mod_lt _ h2L⟩
  let y : Fin L → Fin (2 * L) := fun i => ⟨(2 * i.1 + L) % (2 * L), Nat.mod_lt _ h2L⟩
  let z : Fin L → Fin (2 * L) := fun i => ⟨(2 * i.1 + L + 1) % (2 * L), Nat.mod_lt _ h2L⟩
  have hx_val : ∀ i : Fin L, (x i).1 =
      if 2 * i.1 + L - 1 < 2 * L then 2 * i.1 + L - 1 else 2 * i.1 + L - 1 - 2 * L := by
    intro i; dsimp [x]; have hi := i.2
    have hsub : 2 * i.1 + L - 1 = 2 * i.1 + (L - 1) := by omega
    rw [hsub]; exact add_mod_eq (2 * i.1) (L - 1) (2 * L) (by omega) (by omega)
  have hy_val : ∀ i : Fin L, (y i).1 =
      if 2 * i.1 + L < 2 * L then 2 * i.1 + L else 2 * i.1 + L - 2 * L := by
    intro i; dsimp [y]; have hi := i.2
    exact add_mod_eq (2 * i.1) L (2 * L) (by omega) (by omega)
  have hz_val : ∀ i : Fin L, (z i).1 =
      if 2 * i.1 + L + 1 < 2 * L then 2 * i.1 + L + 1 else 2 * i.1 + L + 1 - 2 * L := by
    intro i; dsimp [z]; have hi := i.2
    have ha : 2 * i.1 + L + 1 = 2 * i.1 + (L + 1) := by omega
    rw [ha]; exact add_mod_eq (2 * i.1) (L + 1) (2 * L) (by omega) (by omega)
  have hx_next : ∀ i, nextFin h2L (x i) = y i := by
    intro i; ext; dsimp [nextFin]
    rw [add_mod_eq (x i).1 1 (2 * L) (x i).2 (by omega), hx_val i, hy_val i]
    have hi := i.2; split_ifs <;> omega
  have hy_next : ∀ i, nextFin h2L (y i) = z i := by
    intro i; ext; dsimp [nextFin]
    rw [add_mod_eq (y i).1 1 (2 * L) (y i).2 (by omega), hy_val i, hz_val i]
    have hi := i.2; split_ifs <;> omega
  have hz_eq : ∀ i, z i = x (nextFin hL i) := by
    intro i; ext
    rw [hz_val i, hx_val (nextFin hL i)]
    have hn : (nextFin hL i).1 = if i.1 + 1 < L then i.1 + 1 else 0 := by
      dsimp [nextFin]
      rw [add_mod_eq i.1 1 L i.2 (by omega)]
      have hi := i.2; split_ifs <;> omega
    rw [hn]; have hi := i.2; split_ifs <;> omega
  have hsum1 : wind h2L f1 =
      ∑ i : Fin L, (delta (f1 (x i)) (f1 (y i)) + delta (f1 (y i)) (f1 (z i))) := by
    unfold wind
    rw [Finset.sum_add_distrib]
    let e : Fin L ⊕ Fin L ≃ Fin (2 * L) :=
      Equiv.ofBijective (Sum.elim x y) ((Fintype.bijective_iff_injective_and_card (Sum.elim x y)).mpr ⟨by
        rintro (a | a) (b | b) h
        · congr; ext
          have hval : (x a).1 = (x b).1 := congrArg Fin.val h
          rw [hx_val a, hx_val b] at hval; have ha := a.2; have hb := b.2; split_ifs at hval <;> omega
        · exfalso
          have hval : (x a).1 = (y b).1 := congrArg Fin.val h
          rw [hx_val a, hy_val b] at hval; have ha := a.2; have hb := b.2; split_ifs at hval <;> omega
        · exfalso
          have hval : (y a).1 = (x b).1 := congrArg Fin.val h
          rw [hy_val a, hx_val b] at hval; have ha := a.2; have hb := b.2; split_ifs at hval <;> omega
        · congr; ext
          have hval : (y a).1 = (y b).1 := congrArg Fin.val h
          rw [hy_val a, hy_val b] at hval; have ha := a.2; have hb := b.2; split_ifs at hval <;> omega,
        by simp [two_mul]⟩)
    rw [← Fintype.sum_equiv e (fun p => delta (f1 (e p)) (f1 (nextFin h2L (e p))))
      (fun k => delta (f1 k) (f1 (nextFin h2L k))) (fun _ => rfl)]
    rw [Fintype.sum_sum_type]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => by simp [e, hx_next]
    · refine Finset.sum_congr rfl fun i _ => by simp [e, hy_next]
  have hdiff : 2 * wind h2L f1 - 2 * wind hL f0 = 0 := by
    rw [hsum1]
    unfold wind
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc ∑ i : Fin L, (2 * (delta (f1 (x i)) (f1 (y i)) + delta (f1 (y i)) (f1 (z i))) -
            2 * delta (f0 i) (f0 (nextFin hL i)))
        = ∑ i : Fin L, (delta (f0 i) (f1 (x i)) - delta (f0 (nextFin hL i)) (f1 (x (nextFin hL i)))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hax : f0 i ≠ f1 (x i) := hadj i (x i) (Or.inl rfl)
          have hay : f0 i ≠ f1 (y i) := hadj i (y i) (Or.inr (Or.inl rfl))
          have haz : f0 i ≠ f1 (z i) := hadj i (z i) (Or.inr (Or.inr rfl))
          have hbz : f0 (nextFin hL i) ≠ f1 (z i) := by
            rw [hz_eq i]
            exact hadj (nextFin hL i) (x (nextFin hL i)) (Or.inl rfl)
          have h1 := delta_identity (f0 i) (f1 (x i)) (f1 (y i)) hax hay
          have h2 := delta_identity (f0 i) (f1 (y i)) (f1 (z i)) hay haz
          have h3 := delta_identity (f1 (z i)) (f0 i) (f0 (nextFin hL i)) haz.symm hbz.symm
          have h4 := delta_antisymm (f1 (z i)) (f0 i)
          have h5 := delta_antisymm (f1 (z i)) (f0 (nextFin hL i))
          rw [← hz_eq i]
          linarith
      _ = 0 := sum_sub_nextFin hL (fun i => delta (f0 i) (f1 (x i)))
  omega

lemma wind_base_odd (m : ℕ) (f0 : Fin (2 * m + 1) → Fin 3)
    (hadj : ∀ i j, baseAdj m i j → f0 i ≠ f0 j) :
    wind (by omega : 0 < 2 * m + 1) f0 % 2 = 1 := by
  have hM : 0 < 2 * m + 1 := by omega
  let stepM : Fin (2 * m + 1) → Fin (2 * m + 1) :=
    fun i => ⟨(i.1 + m) % (2 * m + 1), Nat.mod_lt _ hM⟩
  let stepM1 : Fin (2 * m + 1) → Fin (2 * m + 1) :=
    fun i => ⟨(i.1 + m + 1) % (2 * m + 1), Nat.mod_lt _ hM⟩
  have hsm_val : ∀ i : Fin (2 * m + 1), (stepM i).1 =
      if i.1 + m < 2 * m + 1 then i.1 + m else i.1 + m - (2 * m + 1) :=
    fun i => add_mod_eq i.1 m (2 * m + 1) i.2 (by omega)
  have hsm1_val : ∀ i : Fin (2 * m + 1), (stepM1 i).1 =
      if i.1 + (m + 1) < 2 * m + 1 then i.1 + (m + 1) else i.1 + (m + 1) - (2 * m + 1) := by
    intro i; dsimp [stepM1]; rw [Nat.add_assoc]; exact add_mod_eq i.1 (m + 1) (2 * m + 1) i.2 (by omega)
  have hstep_eq : ∀ i, stepM (nextFin hM i) = stepM1 i := by
    intro i; ext; rw [hsm_val, hsm1_val]
    have hn : (nextFin hM i).1 = if i.1 + 1 < 2 * m + 1 then i.1 + 1 else 0 := by
      dsimp [nextFin]; rw [add_mod_eq i.1 1 (2 * m + 1) i.2 (by omega)]; have hi := i.2; split_ifs <;> omega
    rw [hn]; have hi := i.2; split_ifs <;> omega
  have hstep_inv : ∀ i, stepM (stepM1 i) = i := by
    intro i; ext; rw [hsm_val, hsm1_val]; have hi := i.2; split_ifs <;> omega
  have h2 : 2 * wind hM f0 = 2 * ∑ i : Fin (2 * m + 1), delta (f0 i) (f0 (stepM i)) := by
    unfold wind
    rw [Finset.mul_sum]
    have hpt : ∀ i : Fin (2 * m + 1),
        2 * delta (f0 i) (f0 (nextFin hM i)) =
          delta (f0 (nextFin hM i)) (f0 (stepM (nextFin hM i))) +
          delta (f0 (stepM1 i)) (f0 (stepM (stepM1 i))) := by
      intro i
      have ha : f0 (stepM1 i) ≠ f0 i :=
        (hadj i (stepM1 i) (Or.inr rfl)).symm
      have hb : f0 (stepM1 i) ≠ f0 (nextFin hM i) := by
        rw [← hstep_eq i]
        exact (hadj (nextFin hM i) (stepM (nextFin hM i)) (Or.inl rfl)).symm
      have hid := delta_identity (f0 (stepM1 i)) (f0 i) (f0 (nextFin hM i)) ha hb
      have hanti := delta_antisymm (f0 (stepM1 i)) (f0 (nextFin hM i))
      rw [hstep_inv i, hstep_eq i]
      linarith
    simp_rw [hpt]
    rw [Finset.sum_add_distrib]
    have hs1 : ∑ i : Fin (2 * m + 1), delta (f0 (nextFin hM i)) (f0 (stepM (nextFin hM i))) =
        ∑ i : Fin (2 * m + 1), delta (f0 i) (f0 (stepM i)) :=
      Fintype.sum_equiv (Equiv.ofBijective (nextFin hM) (nextFin_bijective hM))
        (fun i => delta (f0 (nextFin hM i)) (f0 (stepM (nextFin hM i))))
        (fun i => delta (f0 i) (f0 (stepM i))) (fun _ => rfl)
    have hs2 : ∑ i : Fin (2 * m + 1), delta (f0 (stepM1 i)) (f0 (stepM (stepM1 i))) =
        ∑ i : Fin (2 * m + 1), delta (f0 i) (f0 (stepM i)) := by
      refine Fintype.sum_equiv (Equiv.ofBijective stepM1 ?_)
        (fun i => delta (f0 (stepM1 i)) (f0 (stepM (stepM1 i))))
        (fun i => delta (f0 i) (f0 (stepM i))) (fun _ => rfl)
      rw [← Finite.injective_iff_bijective]
      intro a b h; ext
      have hv : (stepM1 a).1 = (stepM1 b).1 := congrArg Fin.val h
      rw [hsm1_val a, hsm1_val b] at hv; have ha := a.2; have hb := b.2; split_ifs at hv <;> omega
    rw [hs1, hs2]; ring
  have hW : wind hM f0 = ∑ i : Fin (2 * m + 1), delta (f0 i) (f0 (stepM i)) := by omega
  rw [hW]
  have hmod : (∑ i : Fin (2 * m + 1), delta (f0 i) (f0 (stepM i))) % 2 =
      (∑ _i : Fin (2 * m + 1), (1 : ℤ)) % 2 := by
    rw [Finset.sum_int_mod, Finset.sum_int_mod]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have := delta_odd_of_ne (f0 i) (f0 (stepM i)) (hadj i (stepM i) (Or.inl rfl))
    omega
  rw [hmod]
  simp

theorem expGraph_not_colorable_three (m R : ℕ) (hm : 1 ≤ m) :
    ¬ (expGraph m R hm).Colorable 3 := by
  rintro ⟨c⟩
  have hM : 0 < 2 * m + 1 := by omega
  let fj : ∀ j : Fin (R + 1), Fin (layerSize (2 * m + 1) j.1) → Fin 3 :=
    fun j i => c (some ⟨j, i⟩)
  have hconst : ∀ j : ℕ, ∀ hj : j ≤ R,
      wind (layerSize_pos hM j) (fj ⟨j, Nat.lt_succ_of_le hj⟩) =
      wind (layerSize_pos hM 0) (fj ⟨0, Nat.zero_lt_succ R⟩) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hk' : k ≤ R := Nat.le_of_succ_le hk
      rw [← ih hk']
      let e : Fin (layerSize (2 * m + 1) (k + 1)) ≃ Fin (2 * layerSize (2 * m + 1) k) :=
        finCongr (layerSize_succ (2 * m + 1) k)
      have hwind_eq : wind (layerSize_pos hM (k + 1)) (fj ⟨k + 1, Nat.lt_succ_of_le hk⟩) =
          wind (by have := layerSize_pos hM k; omega : 0 < 2 * layerSize (2 * m + 1) k)
            (fun x => fj ⟨k + 1, Nat.lt_succ_of_le hk⟩ (e.symm x)) := by
        unfold wind
        refine (Fintype.sum_equiv e
          (fun i => delta (fj ⟨k + 1, Nat.lt_succ_of_le hk⟩ i)
            (fj ⟨k + 1, Nat.lt_succ_of_le hk⟩ (nextFin (layerSize_pos hM (k + 1)) i)))
          (fun x => delta (fj ⟨k + 1, Nat.lt_succ_of_le hk⟩ (e.symm x))
            (fj ⟨k + 1, Nat.lt_succ_of_le hk⟩ (e.symm (nextFin (by have := layerSize_pos hM k; omega) x))))
          fun i => ?_)
        have hi1 : i = e.symm (e i) := (Equiv.symm_apply_apply e i).symm
        have hi2 : nextFin (layerSize_pos hM (k + 1)) i =
            e.symm (nextFin (by have := layerSize_pos hM k; omega) (e i)) := by
          ext; simp [e, nextFin, layerSize_succ]
        rw [← hi1, ← hi2]
      rw [hwind_eq]
      apply wind_step (layerSize_pos hM k)
      intro i x hbx
      have hadj : (expGraph m R hm).Adj
          (some ⟨⟨k, Nat.lt_succ_of_le hk'⟩, i⟩)
          (some ⟨⟨k + 1, Nat.lt_succ_of_le hk⟩, e.symm x⟩) := by
        dsimp [expGraph]
        have h0 : ¬ (k = 0 ∧ k + 1 = 0) := by omega
        rw [dif_neg h0, dif_pos rfl]
        simpa [e] using hbx
      exact c.valid hadj
  have hR : wind (layerSize_pos hM R) (fj ⟨R, Nat.lt_succ_self R⟩) = 0 := by
    apply wind_eq_zero_of_avoid (layerSize_pos hM R) _ (c none)
    intro i
    exact c.valid (by dsimp [expGraph])
  have h0_eq : wind (layerSize_pos hM 0) (fj ⟨0, Nat.zero_lt_succ R⟩) = 0 := by
    rw [← hconst R le_rfl, hR]
  have h0_odd : wind (layerSize_pos hM 0) (fj ⟨0, Nat.zero_lt_succ R⟩) % 2 = 1 := by
    let e0 : Fin (layerSize (2 * m + 1) 0) ≃ Fin (2 * m + 1) :=
      finCongr (by simp [layerSize])
    have hwe : wind (layerSize_pos hM 0) (fj ⟨0, Nat.zero_lt_succ R⟩) =
        wind hM (fun i => fj ⟨0, Nat.zero_lt_succ R⟩ (e0.symm i)) := by
      unfold wind
      refine Fintype.sum_equiv e0
        (fun i => delta (fj ⟨0, Nat.zero_lt_succ R⟩ i)
          (fj ⟨0, Nat.zero_lt_succ R⟩ (nextFin (layerSize_pos hM 0) i)))
        (fun i => delta (fj ⟨0, Nat.zero_lt_succ R⟩ (e0.symm i))
          (fj ⟨0, Nat.zero_lt_succ R⟩ (e0.symm (nextFin hM i))))
        fun i => ?_
      have hi1 : i = e0.symm (e0 i) := (Equiv.symm_apply_apply e0 i).symm
      have hi2 : nextFin (layerSize_pos hM 0) i = e0.symm (nextFin hM (e0 i)) := by
        ext; change (i.1 + 1) % layerSize (2 * m + 1) 0 = (i.1 + 1) % (2 * m + 1)
        simp [layerSize]
      rw [← hi1, ← hi2]
    rw [hwe]
    apply wind_base_odd m
    intro i j hbij
    have hadj : (expGraph m R hm).Adj
        (some ⟨⟨0, Nat.zero_lt_succ R⟩, e0.symm i⟩)
        (some ⟨⟨0, Nat.zero_lt_succ R⟩, e0.symm j⟩) := by
      dsimp only [expGraph]
      rw [dif_pos ⟨rfl, rfl⟩]
      simpa [e0] using hbij
    exact c.valid hadj
  omega

-- =========================================================================
-- PART 2: Bipartization bound ≤ ε * √|S|
-- =========================================================================

lemma card_mono_meridian {H d : ℕ} (hH : 0 < H) (hd : d ≤ H) (a b : ℕ)
    (ha : a < 2 * H) (hb : b < 2 * H)
    (hdist : (b + 2 * H - a) % (2 * H) = H - d ∨ (b + 2 * H - a) % (2 * H) = H + d) :
    (Finset.univ.filter fun θ : Fin (2 * H) =>
      decide ((a + 2 * H - θ.1) % (2 * H) < H) =
      decide ((b + 2 * H - θ.1) % (2 * H) < H)).card ≤ 2 * d := by
  let P := 2 * H
  have hP : 0 < P := by omega
  let shift : Fin P → Fin P := fun θ => ⟨(a + P - θ.1) % P, Nat.mod_lt _ hP⟩
  have hshift_val : ∀ θ : Fin P, (shift θ).1 =
      if θ.1 ≤ a then a - θ.1 else a + P - θ.1 := by
    intro θ; dsimp [shift, P]; have hθ := θ.2
    split_ifs with h
    · rw [show a + 2 * H - θ.1 = (a - θ.1) + 2 * H by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  have hshift_bij : Function.Bijective shift := by
    rw [← Finite.injective_iff_bijective]
    intro θ1 θ2 h; ext
    have hv := congrArg Fin.val h
    rw [hshift_val θ1, hshift_val θ2] at hv
    have h1 := θ1.2; have h2 := θ2.2
    split_ifs at hv <;> omega
  let e : Fin P ≃ Fin P := Equiv.ofBijective shift hshift_bij
  have hrel : ∀ θ : Fin P, (b + P - θ.1) % P = ((shift θ).1 + (b + P - a) % P) % P := by
    intro θ
    have hΔ : (b + P - a) % P = if a ≤ b then b - a else b + P - a := by
      dsimp [P]; split_ifs with h
      · rw [show b + 2 * H - a = (b - a) + 2 * H by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · exact Nat.mod_eq_of_lt (by omega)
    have hθb : (b + P - θ.1) % P = if θ.1 ≤ b then b - θ.1 else b + P - θ.1 := by
      dsimp [P]; have hθ := θ.2; split_ifs with h
      · rw [show b + 2 * H - θ.1 = (b - θ.1) + 2 * H by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · exact Nat.mod_eq_of_lt (by omega)
    rw [hθb, hshift_val θ, hΔ]
    have hθ := θ.2
    have hmod_le : ∀ u v : ℕ, u < P → v < P → (u + v) % P = if u + v < P then u + v else u + v - P :=
      fun u v hu hv => add_mod_eq u v P hu (by omega)
    split_ifs <;> (rw [hmod_le _ _ (by omega) (by omega)]; split_ifs <;> omega)
  let Δ := (b + P - a) % P
  have hcard_eq : (Finset.univ.filter fun θ : Fin P =>
      decide ((a + P - θ.1) % P < H) = decide ((b + P - θ.1) % P < H)).card =
      (Finset.univ.filter fun x : Fin P =>
        decide (x.1 < H) = decide ((x.1 + Δ) % P < H)).card := by
    refine Finset.card_bij (fun θ _ => e θ) ?_ ?_ ?_
    · intro θ hθ
      rw [Finset.mem_filter] at hθ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 := hθ.2
      rw [hrel θ] at h1
      exact h1
    · intro θ1 _ θ2 _ h; exact e.injective h
    · intro x hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hrel (e.symm x)]
      have heq : (shift (e.symm x)).1 = x.1 := congrArg Fin.val (e.apply_symm_apply x)
      have heq' : (a + P - (e.symm x).1) % P = x.1 := heq
      rw [heq', heq]
      exact hx.2
  rw [hcard_eq]
  rcases hdist with hΔ | hΔ
  · let bad : Finset (Fin P) := Finset.univ.filter fun x : Fin P =>
      x.1 < d ∨ (H ≤ x.1 ∧ x.1 < H + d)
    have hsub : (Finset.univ.filter fun x : Fin P =>
        decide (x.1 < H) = decide ((x.1 + Δ) % P < H)) ⊆ bad := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 : decide (x.1 < H) = decide ((x.1 + (H - d)) % (2 * H) < H) := by
        simpa [Δ, P, hΔ] using hx.2
      have hxm : (x.1 + (H - d)) % (2 * H) =
          if x.1 + (H - d) < 2 * H then x.1 + (H - d) else x.1 + (H - d) - 2 * H :=
        add_mod_eq x.1 (H - d) (2 * H) x.2 (by omega)
      rw [hxm] at h1
      have hx2 := x.2
      dsimp [P] at hx2
      by_cases hlt : x.1 < H <;> split_ifs at h1 <;> simp_all <;> omega
    calc (Finset.univ.filter fun x : Fin P =>
            decide (x.1 < H) = decide ((x.1 + Δ) % P < H)).card
        ≤ bad.card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter fun x : Fin P => x.1 < d).card +
          (Finset.univ.filter fun x : Fin P => H ≤ x.1 ∧ x.1 < H + d).card := by
            refine (Finset.card_le_card fun x hx => ?_).trans (Finset.card_union_le _ _)
            rw [Finset.mem_filter] at hx
            rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
            rcases hx.2 with h | h
            · left; exact ⟨hx.1, h⟩
            · right; exact ⟨hx.1, h⟩
      _ ≤ d + d := by
            gcongr
            · refine (Finset.card_le_card_of_injOn (t := Finset.range d) (fun x : Fin P => x.1)
                (fun x hx => Finset.mem_range.mpr (Finset.mem_filter.mp hx).2)
                (fun x _ y _ h => Fin.ext h)).trans (by simp)
            · refine (Finset.card_le_card_of_injOn (t := Finset.range d) (fun x : Fin P => x.1 - H)
                (fun x hx => Finset.mem_range.mpr (by
                  have := (Finset.mem_filter.mp hx).2; dsimp only; omega))
                (fun x hx y hy h => by
                  have hx' := (Finset.mem_filter.mp hx).2
                  have hy' := (Finset.mem_filter.mp hy).2
                  dsimp only at h
                  ext; omega)).trans (by simp)
      _ = 2 * d := by omega
  · let bad : Finset (Fin P) := Finset.univ.filter fun x : Fin P =>
      (H - d ≤ x.1 ∧ x.1 < H) ∨ (2 * H - d ≤ x.1 ∧ x.1 < 2 * H)
    have hsub : (Finset.univ.filter fun x : Fin P =>
        decide (x.1 < H) = decide ((x.1 + Δ) % P < H)) ⊆ bad := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 : decide (x.1 < H) = decide ((x.1 + (H + d)) % (2 * H) < H) := by
        simpa [Δ, P, hΔ] using hx.2
      have hxm : (x.1 + (H + d)) % (2 * H) =
          if x.1 + (H + d) < 2 * H then x.1 + (H + d) else x.1 + (H + d) - 2 * H :=
        add_mod_eq x.1 (H + d) (2 * H) x.2 (by omega)
      rw [hxm] at h1
      have hx2 := x.2
      dsimp [P] at hx2
      by_cases hlt : x.1 < H <;> split_ifs at h1 <;> simp_all <;> omega
    calc (Finset.univ.filter fun x : Fin P =>
            decide (x.1 < H) = decide ((x.1 + Δ) % P < H)).card
        ≤ bad.card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter fun x : Fin P => H - d ≤ x.1 ∧ x.1 < H).card +
          (Finset.univ.filter fun x : Fin P => 2 * H - d ≤ x.1 ∧ x.1 < 2 * H).card := by
            refine (Finset.card_le_card fun x hx => ?_).trans (Finset.card_union_le _ _)
            rw [Finset.mem_filter] at hx
            rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
            rcases hx.2 with h | h
            · left; exact ⟨hx.1, h⟩
            · right; exact ⟨hx.1, h⟩
      _ ≤ d + d := by
            gcongr
            · refine (Finset.card_le_card_of_injOn (t := Finset.range d) (fun x : Fin P => x.1 - (H - d))
                (fun x hx => Finset.mem_range.mpr (by
                  have := (Finset.mem_filter.mp hx).2; dsimp only; omega))
                (fun x hx y hy h => by
                  have hx' := (Finset.mem_filter.mp hx).2
                  have hy' := (Finset.mem_filter.mp hy).2
                  dsimp only at h
                  ext; omega)).trans (by simp)
            · refine (Finset.card_le_card_of_injOn (t := Finset.range d) (fun x : Fin P => x.1 - (2 * H - d))
                (fun x hx => Finset.mem_range.mpr (by
                  have := (Finset.mem_filter.mp hx).2; dsimp only; omega))
                (fun x hx y hy h => by
                  have hx' := (Finset.mem_filter.mp hx).2
                  have hy' := (Finset.mem_filter.mp hy).2
                  dsimp only at h
                  ext; omega)).trans (by simp)
      _ = 2 * d := by omega

lemma weighted_layer_sum_le (M R : ℕ) (hM : 0 < M) (f : Fin (R + 1) → ℕ)
    (hf : ∀ j : Fin (R + 1), f j ≤ 2 ^ j.1 * M) :
    ∑ j : Fin (R + 1), (f j : ℝ) / ((2 : ℝ) ^ j.1 * (M : ℝ)) ≤
      Real.sqrt (2 / (M : ℝ)) * Real.sqrt (∑ j : Fin (R + 1), f j : ℕ) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hstep1 : ∑ j : Fin (R + 1), (f j : ℝ) / ((2 : ℝ) ^ j.1 * (M : ℝ)) ≤
      ∑ j : Fin (R + 1), (1 / Real.sqrt ((2 : ℝ) ^ j.1 * (M : ℝ))) * Real.sqrt (f j) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hdenom : (0 : ℝ) < (2 : ℝ) ^ j.1 * (M : ℝ) := by positivity
    let s := Real.sqrt ((2 : ℝ) ^ j.1 * (M : ℝ))
    have hspos : 0 < s := Real.sqrt_pos.mpr hdenom
    have hs_sq : s * s = (2 : ℝ) ^ j.1 * (M : ℝ) := Real.mul_self_sqrt hdenom.le
    have hfj : (f j : ℝ) ≤ (2 : ℝ) ^ j.1 * (M : ℝ) := by exact_mod_cast hf j
    have hsqrt_le : Real.sqrt (f j) ≤ s := Real.sqrt_le_sqrt hfj
    rw [div_le_iff₀ hdenom]
    calc (f j : ℝ) = Real.sqrt (f j) * Real.sqrt (f j) := (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
      _ ≤ s * Real.sqrt (f j) := mul_le_mul_of_nonneg_right hsqrt_le (Real.sqrt_nonneg _)
      _ = 1 / s * Real.sqrt (f j) * (s * s) := by field_simp
      _ = 1 / s * Real.sqrt (f j) * ((2 : ℝ) ^ j.1 * (M : ℝ)) := by rw [hs_sq]
  have hgeom : ∀ k : ℕ, ∑ j ∈ Finset.range (k + 1), (1 : ℝ) / (2 : ℝ) ^ j = 2 - (1 : ℝ) / (2 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp; norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  have hwt : ∑ j : Fin (R + 1), (1 / Real.sqrt ((2 : ℝ) ^ j.1 * (M : ℝ))) ^ 2 ≤ 2 / (M : ℝ) := by
    have h1 : ∑ j : Fin (R + 1), (1 / Real.sqrt ((2 : ℝ) ^ j.1 * (M : ℝ))) ^ 2 =
        (1 / (M : ℝ)) * ∑ j ∈ Finset.range (R + 1), (1 : ℝ) / (2 : ℝ) ^ j := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (1 / Real.sqrt ((2 : ℝ) ^ j * (M : ℝ))) ^ 2) (R + 1)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ j * (M : ℝ) := by positivity
      rw [div_pow, one_pow, Real.sq_sqrt hpos]
      ring
    rw [h1, hgeom R]
    have hle : 2 - (1 : ℝ) / (2 : ℝ) ^ R ≤ 2 := by
      have : (0 : ℝ) ≤ (1 : ℝ) / (2 : ℝ) ^ R := by positivity
      linarith
    calc (1 / (M : ℝ)) * (2 - (1 : ℝ) / (2 : ℝ) ^ R)
        ≤ (1 / (M : ℝ)) * 2 := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 2 / (M : ℝ) := by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (R + 1)))
    (fun j => 1 / Real.sqrt ((2 : ℝ) ^ j.1 * (M : ℝ)))
    (fun j => Real.sqrt (f j))
  have hsqf : ∑ j : Fin (R + 1), (Real.sqrt (f j)) ^ 2 = ((∑ j : Fin (R + 1), f j : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun j _ => Real.sq_sqrt (Nat.cast_nonneg _)
  have hnonneg : 0 ≤ ∑ j : Fin (R + 1), (1 / Real.sqrt ((2 : ℝ) ^ j.1 * (M : ℝ))) * Real.sqrt (f j) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hsq_bound :
      (∑ j : Fin (R + 1), (1 / Real.sqrt ((2 : ℝ) ^ j.1 * (M : ℝ))) * Real.sqrt (f j)) ^ 2 ≤
        (2 / (M : ℝ)) * ((∑ j : Fin (R + 1), f j : ℕ) : ℝ) := by
    calc _ ≤ (∑ j : Fin (R + 1), (1 / Real.sqrt ((2 : ℝ) ^ j.1 * (M : ℝ))) ^ 2) *
              ((∑ j : Fin (R + 1), f j : ℕ) : ℝ) := by simpa [hsqf] using hcs
      _ ≤ (2 / (M : ℝ)) * ((∑ j : Fin (R + 1), f j : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hwt (Nat.cast_nonneg _)
  refine hstep1.trans ?_
  rw [← Real.sqrt_mul (by positivity)]
  exact (Real.le_sqrt hnonneg (by positivity)).mpr hsq_bound

lemma fin_cast_heq {a b : ℕ} (h : a = b) (x : Fin a) : HEq (Fin.cast h x) x := by
  subst h; rfl

def upNbr (M R : ℕ) (hM : 0 < M) (j : Fin (R + 1)) (off : Fin 3)
    (i : Fin (layerSize M j.1)) : Fin (layerSize M (j.1 + 1)) :=
  let L := layerSize M j.1
  have hL2 : layerSize M (j.1 + 1) = 2 * L := layerSize_succ M j.1
  have hpos : 0 < 2 * L := by have := layerSize_pos hM j.1; omega
  let k : ℕ := match off.1 with
    | 0 => (2 * i.1 + L - 1) % (2 * L)
    | 1 => (2 * i.1 + L) % (2 * L)
    | _ => (2 * i.1 + L + 1) % (2 * L)
  ⟨k, lt_of_lt_of_eq (by
    dsimp [k]; split <;> exact Nat.mod_lt _ hpos) hL2.symm⟩

set_option maxHeartbeats 800000 in
/-- Main bipartization bound on ExpV (2*m+1) R for suitable m and R. -/
theorem expGraph_bipartize (m R : ℕ) (hm : 1 ≤ m) (hR : 1 ≤ R)
    (ε : ℝ) (hε : 0 < ε)
    (hm_bound : 4 * Real.sqrt (2 / ((2 * m + 1 : ℕ) : ℝ)) ≤ ε / 2)
    (hR_bound : 3 * ((2 * m + 1 : ℕ) : ℝ) / (R : ℝ) ≤ ε ^ 2 / 2) :
    ∀ S : Finset (ExpV (2 * m + 1) R),
      ∃ (c : ExpV (2 * m + 1) R → Bool) (E : Finset (Sym2 (ExpV (2 * m + 1) R))),
        (E.card : ℝ) ≤ ε * Real.sqrt S.card ∧
        ∀ u ∈ S, ∀ v ∈ S, (expGraph m R hm).Adj u v → s(u, v) ∉ E → c u ≠ c v := by
  let M := 2 * m + 1
  have hM : 0 < M := by omega
  let e0 : Fin (layerSize M 0) ≃ Fin M := finCongr (by simp [layerSize])
  let stepM : Fin M → Fin M := fun i => ⟨(i.1 + m) % M, Nat.mod_lt _ hM⟩
  intro S
  by_cases hbig : (M : ℝ) ≤ ε * Real.sqrt S.card
  · -- Case 1: delete all M edges of layer 0, color by layer parity
    let c : ExpV M R → Bool := fun v => match v with
      | none => decide ((R + 1) % 2 = 0)
      | some ⟨j, _⟩ => decide (j.1 % 2 = 0)
    let E0 : Finset (Sym2 (ExpV M R)) :=
      Finset.univ.image fun i : Fin M =>
        s(some ⟨⟨0, Nat.zero_lt_succ R⟩, e0.symm i⟩,
          some ⟨⟨0, Nat.zero_lt_succ R⟩, e0.symm (stepM i)⟩)
    refine ⟨c, E0, ?_, ?_⟩
    · have hcard : E0.card ≤ M := (Finset.card_image_le).trans (by simp)
      exact (Nat.cast_le.mpr hcard).trans hbig
    · intro u _ v _ hadj hnotE
      match u, v with
      | none, none => exact False.elim hadj
      | none, some ⟨j, i⟩ =>
        have hj : j.1 = R := hadj
        dsimp [c]; rw [hj]; intro heq; simp only [decide_eq_decide] at heq; omega
      | some ⟨j, i⟩, none =>
        have hj : j.1 = R := hadj
        dsimp [c]; rw [hj]; intro heq; simp only [decide_eq_decide] at heq; omega
      | some ⟨j1, i1⟩, some ⟨j2, i2⟩ =>
        dsimp [expGraph] at hadj
        split_ifs at hadj with h0 h12 h21
        · exfalso
          apply hnotE
          have hj1 : j1 = ⟨0, Nat.zero_lt_succ R⟩ := Fin.ext h0.1
          have hj2 : j2 = ⟨0, Nat.zero_lt_succ R⟩ := Fin.ext h0.2
          subst hj1; subst hj2
          have hi1_lt : i1.1 < M := by have := i1.2; dsimp [layerSize] at this; omega
          have hi2_lt : i2.1 < M := by have := i2.2; dsimp [layerSize] at this; omega
          rcases hadj with h | h
          · refine Finset.mem_image.mpr ⟨e0 i1, Finset.mem_univ _, ?_⟩
            have hi2 : e0.symm (stepM (e0 i1)) = i2 := by
              ext; simpa [e0, stepM, M] using h.symm
            rw [hi2, Equiv.symm_apply_apply]
          · refine Finset.mem_image.mpr ⟨e0 i2, Finset.mem_univ _, ?_⟩
            have hi1 : e0.symm (stepM (e0 i2)) = i1 := by
              ext
              have h1 := add_mod_eq i1.1 (m + 1) M hi1_lt (by omega)
              have h2 := add_mod_eq i2.1 m M hi2_lt (by omega)
              have hv : i2.1 = (i1.1 + m + 1) % M := h
              dsimp [e0, stepM, M] at h1 h2 hv ⊢
              rw [Nat.add_assoc] at hv
              rw [h2, hv, h1]
              split_ifs <;> omega
            rw [hi1, Equiv.symm_apply_apply, Sym2.eq_swap]
        · dsimp [c]; rw [h12]; intro heq; simp only [decide_eq_decide] at heq; omega
        · dsimp [c]; rw [h21]; intro heq; simp only [decide_eq_decide] at heq; omega
  · -- Case 2: ε * √|S| < M, use layer transition + averaged meridian cut
    push Not at hbig
    let layerS : ∀ j : Fin (R + 1), Finset (Fin (layerSize M j.1)) :=
      fun j => Finset.univ.filter fun i => some ⟨j, i⟩ ∈ S
    have hlayer_le : ∀ j : Fin (R + 1), (layerS j).card ≤ 2 ^ j.1 * M := fun j =>
      (Finset.card_le_univ _).trans_eq (by rw [Fintype.card_fin]; rfl)
    have hlayer_sum : ∑ j : Fin (R + 1), (layerS j).card ≤ S.card := by
      rw [← Finset.card_sigma]
      refine Finset.card_le_card_of_injOn (fun p => some ⟨p.1, p.2⟩) ?_ ?_
      · intro p hp
        have hp' := Finset.mem_sigma.mp (Finset.mem_coe.mp hp)
        exact Finset.mem_coe.mpr (Finset.mem_filter.mp hp'.2).2
      · rintro ⟨j1, i1⟩ _ ⟨j2, i2⟩ _ h
        exact Option.some.inj h
    -- Pigeonhole on t ∈ Fin R
    have hsumR : ∑ t : Fin R, (layerS ⟨t.1, by omega⟩).card ≤ S.card := by
      calc ∑ t : Fin R, (layerS ⟨t.1, by omega⟩).card
          ≤ ∑ j : Fin (R + 1), (layerS j).card := by
            let emb : Fin R ↪ Fin (R + 1) :=
              ⟨fun t => ⟨t.1, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
            have h1 : ∑ t : Fin R, (layerS ⟨t.1, by omega⟩).card =
                ∑ j ∈ Finset.univ.map emb, (layerS j).card := by
              rw [Finset.sum_map]; rfl
            rw [h1]
            exact Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
        _ ≤ S.card := hlayer_sum
    have hex_t : ∃ t : Fin R, R * (layerS ⟨t.1, by omega⟩).card ≤ S.card := by
      by_contra hno
      push Not at hno
      have hgt : R * S.card < R * ∑ t : Fin R, (layerS ⟨t.1, by omega⟩).card := by
        rw [Finset.mul_sum]
        calc R * S.card = ∑ _t : Fin R, S.card := by simp
          _ < ∑ t : Fin R, R * (layerS ⟨t.1, by omega⟩).card :=
              Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hR⟩⟩) (fun t _ => hno t)
      have hle : R * ∑ t : Fin R, (layerS ⟨t.1, by omega⟩).card ≤ R * S.card :=
        Nat.mul_le_mul_left R hsumR
      omega
    obtain ⟨t, ht_card⟩ := hex_t
    let t0 : Fin (R + 1) := ⟨t.1, by omega⟩
    let t1 : Fin (R + 1) := ⟨t.1 + 1, by omega⟩
    let upN : ∀ (j : Fin (R + 1)), j.1 < R → Fin 3 → Fin (layerSize M j.1) →
        Fin (layerSize M (j.1 + 1)) := fun j _ => upNbr M R hM j
    -- Transition edges from layer t to layer t+1
    let fTrans : Fin 3 → Finset (Sym2 (ExpV M R)) := fun off =>
      (layerS t0).image fun i => s(some ⟨t0, i⟩, some ⟨t1, upN t0 t.2 off i⟩)
    let E_trans : Finset (Sym2 (ExpV M R)) := (Finset.univ : Finset (Fin 3)).biUnion fTrans
    have hEtrans_card : E_trans.card ≤ 3 * (layerS t0).card := by
      calc E_trans.card
          ≤ ∑ off : Fin 3, (fTrans off).card := Finset.card_biUnion_le
        _ ≤ ∑ _off : Fin 3, (layerS t0).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ = 3 * (layerS t0).card := by simp
    have hEtrans_real : (E_trans.card : ℝ) ≤ (ε / 2) * Real.sqrt S.card := by
      have hRpos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr hR
      have h1 : (E_trans.card : ℝ) ≤ 3 * (S.card : ℝ) / (R : ℝ) := by
        rw [le_div_iff₀ hRpos]
        have : (E_trans.card : ℝ) * (R : ℝ) ≤ 3 * ((R : ℝ) * ((layerS t0).card : ℝ)) := by
          have h1' : (E_trans.card : ℝ) ≤ 3 * ((layerS t0).card : ℝ) := by exact_mod_cast hEtrans_card
          nlinarith
        have h2' : (R : ℝ) * ((layerS t0).card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast ht_card
        linarith
      have hsqrt_le : Real.sqrt S.card ≤ (M : ℝ) / ε := by
        rw [le_div_iff₀ hε]; linarith
      calc (E_trans.card : ℝ) ≤ 3 * (S.card : ℝ) / (R : ℝ) := h1
        _ = (3 * Real.sqrt S.card / (R : ℝ)) * Real.sqrt S.card := by
            rw [div_mul_eq_mul_div, mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
        _ ≤ (3 * ((M : ℝ) / ε) / (R : ℝ)) * Real.sqrt S.card := by
            gcongr
        _ = (3 * (M : ℝ) / (R : ℝ)) / ε * Real.sqrt S.card := by ring
        _ ≤ (ε ^ 2 / 2) / ε * Real.sqrt S.card := by gcongr
        _ = (ε / 2) * Real.sqrt S.card := by field_simp
    -- Meridian colorings indexed by θ : Fin (2 * H) where H = 2^R * M
    let H := 2 ^ R * M
    let P := 2 * H
    have hH : 0 < H := Nat.mul_pos (by positivity) hM
    have hP : 0 < P := by omega
    let pos : ∀ (j : Fin (R + 1)), Fin (layerSize M j.1) → ℕ :=
      fun j i => i.1 * 2 ^ (R + 1 - j.1)
    have hpos_lt : ∀ (j : Fin (R + 1)) (i : Fin (layerSize M j.1)), pos j i < P := by
      intro j i
      have hi : i.1 < 2 ^ j.1 * M := i.2
      have hpow : 2 ^ j.1 * 2 ^ (R + 1 - j.1) = 2 ^ (R + 1) := by
        rw [← pow_add, Nat.add_sub_of_le (by omega)]
      have hPeq : P = 2 ^ (R + 1) * M := by dsimp [P, H]; rw [pow_succ]; ring
      calc i.1 * 2 ^ (R + 1 - j.1)
          < (2 ^ j.1 * M) * 2 ^ (R + 1 - j.1) := Nat.mul_lt_mul_of_pos_right hi (by positivity)
        _ = (2 ^ j.1 * 2 ^ (R + 1 - j.1)) * M := by ring
        _ = P := by rw [hpow, hPeq]
    let cθ : Fin P → ExpV M R → Bool := fun θ v => match v with
      | none => decide ((R + 1) % 2 = 0)
      | some ⟨j, i⟩ =>
        if j.1 ≤ t.1 then decide ((pos j i + P - θ.1) % P < H)
        else decide (j.1 % 2 = 0)
    let j0 : Fin (R + 1) := ⟨0, Nat.zero_lt_succ R⟩
    let E_mer0 : Fin P → Finset (Sym2 (ExpV M R)) := fun θ =>
      ((layerS j0).filter fun i =>
        cθ θ (some ⟨j0, i⟩) = cθ θ (some ⟨j0, e0.symm (stepM (e0 i))⟩)).image fun i =>
        s(some ⟨j0, i⟩, some ⟨j0, e0.symm (stepM (e0 i))⟩)
    let E_merUp : Fin P → ∀ (j : Fin (R + 1)), j.1 < t.1 → Fin 3 → Finset (Sym2 (ExpV M R)) :=
      fun θ j hj off =>
        ((layerS j).filter fun i =>
          cθ θ (some ⟨j, i⟩) = cθ θ (some ⟨⟨j.1 + 1, by omega⟩, upN j (by omega) off i⟩)).image fun i =>
          s(some ⟨j, i⟩, some ⟨⟨j.1 + 1, by omega⟩, upN j (by omega) off i⟩)
    let belowT : Finset (Fin (R + 1)) := Finset.univ.filter fun j : Fin (R + 1) => j.1 < t.1
    let E_mer : Fin P → Finset (Sym2 (ExpV M R)) := fun θ =>
      E_mer0 θ ∪ belowT.attach.biUnion fun ⟨j, hj⟩ =>
        (Finset.univ : Finset (Fin 3)).biUnion fun off =>
          E_merUp θ j (Finset.mem_filter.mp hj).2 off
    -- Bound sum over θ of (E_mer0 θ).card
    have hsum_mer0 : ∑ θ : Fin P, (E_mer0 θ).card ≤ (layerS j0).card * (2 * 2 ^ R) := by
      calc ∑ θ : Fin P, (E_mer0 θ).card
          ≤ ∑ θ : Fin P, ((layerS j0).filter fun i =>
              cθ θ (some ⟨j0, i⟩) = cθ θ (some ⟨j0, e0.symm (stepM (e0 i))⟩)).card :=
            Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ = ∑ i ∈ layerS j0, (Finset.univ.filter fun θ : Fin P =>
              cθ θ (some ⟨j0, i⟩) = cθ θ (some ⟨j0, e0.symm (stepM (e0 i))⟩)).card := by
            simp_rw [Finset.card_filter]
            exact Finset.sum_comm
        _ ≤ ∑ _i ∈ layerS j0, (2 * 2 ^ R) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hle : (Finset.univ.filter fun θ : Fin P =>
                cθ θ (some ⟨j0, i⟩) = cθ θ (some ⟨j0, e0.symm (stepM (e0 i))⟩)).card ≤ 2 * 2 ^ R := by
              have h0t : j0.1 ≤ t.1 := Nat.zero_le _
              simp only [cθ, if_pos h0t]
              apply card_mono_meridian (H := H) (d := 2 ^ R) hH
                (Nat.le_mul_of_pos_right _ hM) (pos j0 i) (pos j0 (e0.symm (stepM (e0 i))))
                (hpos_lt j0 i) (hpos_lt j0 _)
              left
              have hi : i.1 < M := by have := i.2; dsimp [j0, layerSize] at this; omega
              have hsm : (e0.symm (stepM (e0 i))).1 = (i.1 + m) % M := by simp [e0, stepM]
              dsimp [pos, j0]
              rw [hsm, add_mod_eq i.1 m M hi (by omega)]
              have hPeq : 2 * H = M * 2 ^ (R + 1) := by dsimp [H]; rw [pow_succ]; ring
              have hHsplit : H = m * 2 ^ (R + 1) + 2 ^ R := by dsimp [H, M]; rw [pow_succ]; ring
              have hHeq : H - 2 ^ R = m * 2 ^ (R + 1) := by omega
              have hm2H : m * 2 ^ (R + 1) < 2 * H := by
                have hpos2 : 0 < 2 ^ (R + 1) := by positivity
                omega
              rw [hHeq]
              split_ifs with hlt
              · have hmul : (i.1 + m) * 2 ^ (R + 1) = i.1 * 2 ^ (R + 1) + m * 2 ^ (R + 1) := by ring
                have hsub : (i.1 + m) * 2 ^ (R + 1) + 2 * H - i.1 * 2 ^ (R + 1) =
                    m * 2 ^ (R + 1) + 2 * H := by omega
                rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt hm2H]
              · have h1 : (i.1 + m - M) * 2 ^ (R + 1) + M * 2 ^ (R + 1) =
                    (i.1 + m) * 2 ^ (R + 1) := by
                  rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
                have hmul : (i.1 + m) * 2 ^ (R + 1) = i.1 * 2 ^ (R + 1) + m * 2 ^ (R + 1) := by ring
                have hsub : (i.1 + m - M) * 2 ^ (R + 1) + 2 * H - i.1 * 2 ^ (R + 1) =
                    m * 2 ^ (R + 1) := by omega
                rw [hsub, Nat.mod_eq_of_lt hm2H]
            exact hle
        _ = (layerS j0).card * (2 * 2 ^ R) := by simp
    -- Bound sum over θ of (E_merUp θ j hj off).card for each j < t and off : Fin 3
    have hsum_merUp : ∀ (j : Fin (R + 1)) (hj : j.1 < t.1) (off : Fin 3),
        ∑ θ : Fin P, (E_merUp θ j hj off).card ≤ (layerS j).card * (2 * 2 ^ (R - j.1)) := by
      intro j hj off
      calc ∑ θ : Fin P, (E_merUp θ j hj off).card
          ≤ ∑ θ : Fin P, ((layerS j).filter fun i =>
              cθ θ (some ⟨j, i⟩) = cθ θ (some ⟨⟨j.1 + 1, by omega⟩, upN j (by omega) off i⟩)).card :=
            Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ = ∑ i ∈ layerS j, (Finset.univ.filter fun θ : Fin P =>
              cθ θ (some ⟨j, i⟩) = cθ θ (some ⟨⟨j.1 + 1, by omega⟩, upN j (by omega) off i⟩)).card := by
            simp_rw [Finset.card_filter]
            exact Finset.sum_comm
        _ ≤ ∑ _i ∈ layerS j, (2 * 2 ^ (R - j.1)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hj1t : j.1 + 1 ≤ t.1 := by omega
            have hjt : j.1 ≤ t.1 := by omega
            simp only [cθ, if_pos hjt, if_pos hj1t]
            have hle_H : 2 ^ (R - j.1) ≤ H := by
              dsimp [H]
              calc 2 ^ (R - j.1) ≤ 2 ^ R := Nat.pow_le_pow_right (by omega) (Nat.sub_le R j.1)
                _ ≤ 2 ^ R * M := Nat.le_mul_of_pos_right _ hM
            have hpow1 : 2 ^ (R + 1 - j.1) = 2 * 2 ^ (R - j.1) := by
              rw [show R + 1 - j.1 = (R - j.1) + 1 by omega, pow_succ, mul_comm]
            have hpowL : layerSize M j.1 * 2 ^ (R - j.1) = H := by
              dsimp [layerSize, H]
              rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le (by omega)]
            have hLpos : 0 < layerSize M j.1 := layerSize_pos hM j.1
            have hi : i.1 < layerSize M j.1 := i.2
            have hsub_pos : R + 1 - (j.1 + 1) = R - j.1 := by omega
            fin_cases off
            · -- off = 0: d = -1, dist = H - 2^(R - j)
              apply card_mono_meridian (H := H) (d := 2 ^ (R - j.1)) hH hle_H
                (pos j i) (pos ⟨j.1 + 1, by omega⟩ (upN j (by omega) 0 i))
                (hpos_lt j i) (hpos_lt ⟨j.1 + 1, by omega⟩ (upN j (by omega) 0 i))
              left
              simp only [pos, upN, upNbr, Fin.val_zero]
              rw [hsub_pos, hpow1]
              have hmod : (2 * i.1 + layerSize M j.1 - 1) % (2 * layerSize M j.1) =
                  if 2 * i.1 + (layerSize M j.1 - 1) < 2 * layerSize M j.1
                  then 2 * i.1 + (layerSize M j.1 - 1)
                  else 2 * i.1 + (layerSize M j.1 - 1) - 2 * layerSize M j.1 := by
                rw [show 2 * i.1 + layerSize M j.1 - 1 = 2 * i.1 + (layerSize M j.1 - 1) by omega]
                exact add_mod_eq (2 * i.1) (layerSize M j.1 - 1) (2 * layerSize M j.1) (by omega) (by omega)
              rw [hmod]
              split_ifs with hlt
              · have hcalc : (2 * i.1 + (layerSize M j.1 - 1)) * 2 ^ (R - j.1) + 2 * H -
                    i.1 * (2 * 2 ^ (R - j.1)) = (H - 2 ^ (R - j.1)) + 2 * H := by
                  have h1 : (layerSize M j.1 - 1) * 2 ^ (R - j.1) + 2 ^ (R - j.1) = H := by
                    rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega), hpowL]
                  have h2 : (2 * i.1 + (layerSize M j.1 - 1)) * 2 ^ (R - j.1) =
                      i.1 * (2 * 2 ^ (R - j.1)) + (layerSize M j.1 - 1) * 2 ^ (R - j.1) := by ring
                  omega
                rw [hcalc, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              · have hcalc : (2 * i.1 + (layerSize M j.1 - 1) - 2 * layerSize M j.1) * 2 ^ (R - j.1) + 2 * H -
                    i.1 * (2 * 2 ^ (R - j.1)) = H - 2 ^ (R - j.1) := by
                  have h1 : (layerSize M j.1 - 1) * 2 ^ (R - j.1) + 2 ^ (R - j.1) = H := by
                    rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega), hpowL]
                  have h2 : (2 * i.1 + (layerSize M j.1 - 1) - 2 * layerSize M j.1) * 2 ^ (R - j.1) + 2 * H =
                      (2 * i.1 + (layerSize M j.1 - 1)) * 2 ^ (R - j.1) := by
                    have h2H : 2 * H = (2 * layerSize M j.1) * 2 ^ (R - j.1) := by rw [← hpowL]; ring
                    rw [h2H, ← Nat.add_mul, Nat.sub_add_cancel (by omega)]
                  have h3 : (2 * i.1 + (layerSize M j.1 - 1)) * 2 ^ (R - j.1) =
                      i.1 * (2 * 2 ^ (R - j.1)) + (layerSize M j.1 - 1) * 2 ^ (R - j.1) := by ring
                  omega
                rw [hcalc, Nat.mod_eq_of_lt (by omega)]
            · -- off = 1: d = 0, dist = H (0 bad θ's ≤ 2 * 2^(R - j)!)
              refine (card_mono_meridian (H := H) (d := 0) hH (Nat.zero_le H)
                (pos j i) (pos ⟨j.1 + 1, by omega⟩ (upN j (by omega) 1 i))
                (hpos_lt j i) (hpos_lt ⟨j.1 + 1, by omega⟩ (upN j (by omega) 1 i)) ?_).trans (Nat.zero_le _)
              left
              simp only [pos, upN, upNbr, Fin.val_one]
              rw [hsub_pos, hpow1, Nat.sub_zero]
              have hmod := add_mod_eq (2 * i.1) (layerSize M j.1) (2 * layerSize M j.1) (by omega) (by omega)
              rw [hmod]
              split_ifs with hlt
              · have hcalc : (2 * i.1 + layerSize M j.1) * 2 ^ (R - j.1) + 2 * H -
                    i.1 * (2 * 2 ^ (R - j.1)) = H + 2 * H := by
                  have h2 : (2 * i.1 + layerSize M j.1) * 2 ^ (R - j.1) =
                      i.1 * (2 * 2 ^ (R - j.1)) + H := by rw [← hpowL]; ring
                  omega
                rw [hcalc, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              · have hcalc : (2 * i.1 + layerSize M j.1 - 2 * layerSize M j.1) * 2 ^ (R - j.1) + 2 * H -
                    i.1 * (2 * 2 ^ (R - j.1)) = H := by
                  have h2 : (2 * i.1 + layerSize M j.1 - 2 * layerSize M j.1) * 2 ^ (R - j.1) + 2 * H =
                      (2 * i.1 + layerSize M j.1) * 2 ^ (R - j.1) := by
                    have h2H : 2 * H = (2 * layerSize M j.1) * 2 ^ (R - j.1) := by rw [← hpowL]; ring
                    rw [h2H, ← Nat.add_mul, Nat.sub_add_cancel (by omega)]
                  have h3 : (2 * i.1 + layerSize M j.1) * 2 ^ (R - j.1) =
                      i.1 * (2 * 2 ^ (R - j.1)) + H := by rw [← hpowL]; ring
                  omega
                rw [hcalc, Nat.mod_eq_of_lt (by omega)]
            · -- off = 2: d = +1, dist = H + 2^(R - j)
              apply card_mono_meridian (H := H) (d := 2 ^ (R - j.1)) hH hle_H
                (pos j i) (pos ⟨j.1 + 1, by omega⟩ (upN j (by omega) 2 i))
                (hpos_lt j i) (hpos_lt ⟨j.1 + 1, by omega⟩ (upN j (by omega) 2 i))
              right
              have hlt_H : 2 ^ (R - j.1) < H := by
                have h2pos : 0 < 2 ^ (R - j.1) := by positivity
                have hLgt : 1 < layerSize M j.1 := by
                  dsimp [layerSize, M]
                  have : 1 ≤ 2 ^ j.1 := Nat.one_le_pow _ _ (by omega)
                  nlinarith
                nlinarith
              simp only [pos, upN, upNbr, Fin.val_two]
              rw [hsub_pos, hpow1]
              have hmod : (2 * i.1 + layerSize M j.1 + 1) % (2 * layerSize M j.1) =
                  if 2 * i.1 + (layerSize M j.1 + 1) < 2 * layerSize M j.1
                  then 2 * i.1 + (layerSize M j.1 + 1)
                  else 2 * i.1 + (layerSize M j.1 + 1) - 2 * layerSize M j.1 := by
                rw [show 2 * i.1 + layerSize M j.1 + 1 = 2 * i.1 + (layerSize M j.1 + 1) by omega]
                exact add_mod_eq (2 * i.1) (layerSize M j.1 + 1) (2 * layerSize M j.1) (by omega) (by omega)
              rw [hmod]
              split_ifs with hlt
              · have hcalc : (2 * i.1 + (layerSize M j.1 + 1)) * 2 ^ (R - j.1) + 2 * H -
                    i.1 * (2 * 2 ^ (R - j.1)) = (H + 2 ^ (R - j.1)) + 2 * H := by
                  have h2 : (2 * i.1 + (layerSize M j.1 + 1)) * 2 ^ (R - j.1) =
                      i.1 * (2 * 2 ^ (R - j.1)) + H + 2 ^ (R - j.1) := by rw [← hpowL]; ring
                  omega
                rw [hcalc, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              · have hcalc : (2 * i.1 + (layerSize M j.1 + 1) - 2 * layerSize M j.1) * 2 ^ (R - j.1) + 2 * H -
                    i.1 * (2 * 2 ^ (R - j.1)) = H + 2 ^ (R - j.1) := by
                  have h2 : (2 * i.1 + (layerSize M j.1 + 1) - 2 * layerSize M j.1) * 2 ^ (R - j.1) + 2 * H =
                      (2 * i.1 + (layerSize M j.1 + 1)) * 2 ^ (R - j.1) := by
                    have h2H : 2 * H = (2 * layerSize M j.1) * 2 ^ (R - j.1) := by rw [← hpowL]; ring
                    rw [h2H, ← Nat.add_mul, Nat.sub_add_cancel (by omega)]
                  have h3 : (2 * i.1 + (layerSize M j.1 + 1)) * 2 ^ (R - j.1) =
                      i.1 * (2 * 2 ^ (R - j.1)) + H + 2 ^ (R - j.1) := by rw [← hpowL]; ring
                  omega
                rw [hcalc, Nat.mod_eq_of_lt (by omega)]
        _ = (layerS j).card * (2 * 2 ^ (R - j.1)) := by simp
    -- Combine sum over θ of (E_mer θ).card
    have hsum_mer_nat : ∑ θ : Fin P, (E_mer θ).card ≤
        ∑ j : Fin (R + 1), (layerS j).card * (4 * 2 ^ (R + 1 - j.1)) := by
      have hpt : ∀ θ : Fin P, (E_mer θ).card ≤
          (E_mer0 θ).card + ∑ p ∈ belowT.attach, ∑ off : Fin 3,
            (E_merUp θ p.1 (Finset.mem_filter.mp p.2).2 off).card := by
        intro θ
        calc (E_mer θ).card
            ≤ (E_mer0 θ).card + (belowT.attach.biUnion fun ⟨j, hj⟩ =>
                (Finset.univ : Finset (Fin 3)).biUnion fun off =>
                  E_merUp θ j (Finset.mem_filter.mp hj).2 off).card := Finset.card_union_le _ _
          _ ≤ (E_mer0 θ).card + ∑ p ∈ belowT.attach,
                ((Finset.univ : Finset (Fin 3)).biUnion fun off =>
                  E_merUp θ p.1 (Finset.mem_filter.mp p.2).2 off).card := by
              gcongr; exact Finset.card_biUnion_le
          _ ≤ (E_mer0 θ).card + ∑ p ∈ belowT.attach, ∑ off : Fin 3,
                (E_merUp θ p.1 (Finset.mem_filter.mp p.2).2 off).card := by
              gcongr; exact Finset.card_biUnion_le
      calc ∑ θ : Fin P, (E_mer θ).card
          ≤ ∑ θ : Fin P, ((E_mer0 θ).card + ∑ p ∈ belowT.attach, ∑ off : Fin 3,
              (E_merUp θ p.1 (Finset.mem_filter.mp p.2).2 off).card) :=
            Finset.sum_le_sum fun θ _ => hpt θ
        _ = (∑ θ : Fin P, (E_mer0 θ).card) +
            ∑ p ∈ belowT.attach, ∑ off : Fin 3,
              ∑ θ : Fin P, (E_merUp θ p.1 (Finset.mem_filter.mp p.2).2 off).card := by
            rw [Finset.sum_add_distrib]
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
        _ ≤ (layerS j0).card * (2 * 2 ^ R) +
            ∑ p ∈ belowT.attach, ∑ _off : Fin 3, (layerS p.1).card * (2 * 2 ^ (R - p.1.1)) := by
            gcongr
            exact hsum_merUp p.1 (Finset.mem_filter.mp p.2).2 _
        _ = (layerS j0).card * (2 * 2 ^ R) +
            ∑ j ∈ belowT, (layerS j).card * (3 * (2 * 2 ^ (R - j.1))) := by
            congr 1
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
            rw [← Finset.sum_attach belowT (fun j => (layerS j).card * (3 * (2 * 2 ^ (R - j.1))))]
            refine Finset.sum_congr rfl fun p _ => by ring
        _ ≤ (layerS j0).card * (2 ^ (R + 1 - j0.1)) +
            ∑ j : Fin (R + 1), (layerS j).card * (3 * 2 ^ (R + 1 - j.1)) := by
            gcongr
            · dsimp [j0]; rw [pow_succ]; omega
            · refine (Finset.sum_le_sum fun j hj => ?_).trans
                (Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _)
              have hlt : j.1 < R := by have := (Finset.mem_filter.mp hj).2; omega
              have hpow : 2 ^ (R + 1 - j.1) = 2 * 2 ^ (R - j.1) := by
                rw [show R + 1 - j.1 = (R - j.1) + 1 by omega, pow_succ, mul_comm]
              rw [hpow]
        _ ≤ (∑ j : Fin (R + 1), (layerS j).card * (2 ^ (R + 1 - j.1))) +
            ∑ j : Fin (R + 1), (layerS j).card * (3 * 2 ^ (R + 1 - j.1)) := by
            gcongr
            exact Finset.single_le_sum (f := fun j : Fin (R + 1) => (layerS j).card * 2 ^ (R + 1 - j.1))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ j0)
        _ = ∑ j : Fin (R + 1), (layerS j).card * (4 * 2 ^ (R + 1 - j.1)) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun j _ => by ring
    -- Divide by P = 2^(R+1) * M and apply weighted_layer_sum_le
    have hP_eq : (P : ℝ) = (2 : ℝ) ^ (R + 1) * (M : ℝ) := by
      dsimp [P, H]; push_cast; rw [pow_succ]; ring
    have hP_pos : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.mpr hP
    have havg : (∑ θ : Fin P, ((E_mer θ).card : ℝ)) / (P : ℝ) ≤ (ε / 2) * Real.sqrt S.card := by
      have hcast : ∑ θ : Fin P, ((E_mer θ).card : ℝ) ≤
          ∑ j : Fin (R + 1), ((layerS j).card : ℝ) * (4 * (2 : ℝ) ^ (R + 1 - j.1)) := by
        simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
          (Nat.cast_le (α := ℝ)).mpr hsum_mer_nat
      have hdiv_eq : (∑ j : Fin (R + 1), ((layerS j).card : ℝ) * (4 * (2 : ℝ) ^ (R + 1 - j.1))) / (P : ℝ) =
          4 * ∑ j : Fin (R + 1), ((layerS j).card : ℝ) / ((2 : ℝ) ^ j.1 * (M : ℝ)) := by
        rw [Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hpow : (2 : ℝ) ^ (R + 1) = (2 : ℝ) ^ j.1 * (2 : ℝ) ^ (R + 1 - j.1) := by
          rw [← pow_add, Nat.add_sub_of_le (by omega)]
        rw [hP_eq, hpow]
        have h2p : (2 : ℝ) ^ (R + 1 - j.1) ≠ 0 := by positivity
        rw [show (2 : ℝ) ^ j.1 * (2 : ℝ) ^ (R + 1 - j.1) * (M : ℝ) =
            ((2 : ℝ) ^ j.1 * (M : ℝ)) * (2 : ℝ) ^ (R + 1 - j.1) by ring]
        rw [show ((layerS j).card : ℝ) * (4 * (2 : ℝ) ^ (R + 1 - j.1)) =
            (4 * ((layerS j).card : ℝ)) * (2 : ℝ) ^ (R + 1 - j.1) by ring]
        rw [mul_div_mul_right _ _ h2p, mul_div_assoc]
      calc (∑ θ : Fin P, ((E_mer θ).card : ℝ)) / (P : ℝ)
          ≤ (∑ j : Fin (R + 1), ((layerS j).card : ℝ) * (4 * (2 : ℝ) ^ (R + 1 - j.1))) / (P : ℝ) :=
            div_le_div_of_nonneg_right hcast hP_pos.le
        _ = 4 * ∑ j : Fin (R + 1), ((layerS j).card : ℝ) / ((2 : ℝ) ^ j.1 * (M : ℝ)) := hdiv_eq
        _ ≤ 4 * (Real.sqrt (2 / (M : ℝ)) * Real.sqrt (∑ j : Fin (R + 1), (layerS j).card : ℕ)) :=
            mul_le_mul_of_nonneg_left
              (weighted_layer_sum_le M R hM (fun j => (layerS j).card) hlayer_le) (by norm_num)
        _ ≤ 4 * (Real.sqrt (2 / (M : ℝ)) * Real.sqrt S.card) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr hlayer_sum)) (Real.sqrt_nonneg _))
              (by norm_num)
        _ = (4 * Real.sqrt (2 / (M : ℝ))) * Real.sqrt S.card := by ring
        _ ≤ (ε / 2) * Real.sqrt S.card :=
            mul_le_mul_of_nonneg_right hm_bound (Real.sqrt_nonneg _)
    -- Pigeonhole: there exists θ : Fin P with (E_mer θ).card ≤ (ε / 2) * √|S|
    have hex_θ : ∃ θ : Fin P, ((E_mer θ).card : ℝ) ≤ (ε / 2) * Real.sqrt S.card := by
      by_contra hno
      push Not at hno
      have hgt : (P : ℝ) * ((ε / 2) * Real.sqrt S.card) < ∑ θ : Fin P, ((E_mer θ).card : ℝ) := by
        calc (P : ℝ) * ((ε / 2) * Real.sqrt S.card)
            = ∑ _θ : Fin P, ((ε / 2) * Real.sqrt S.card) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ < ∑ θ : Fin P, ((E_mer θ).card : ℝ) :=
              Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hP⟩⟩) (fun θ _ => hno θ)
      have hle : ∑ θ : Fin P, ((E_mer θ).card : ℝ) ≤ (P : ℝ) * ((ε / 2) * Real.sqrt S.card) := by
        have := (div_le_iff₀ hP_pos).mp havg
        linarith
      linarith
    obtain ⟨θ, hθ_bound⟩ := hex_θ
    refine ⟨cθ θ, E_trans ∪ E_mer θ, ?_, ?_⟩
    · calc ((E_trans ∪ E_mer θ).card : ℝ)
          ≤ (E_trans.card : ℝ) + ((E_mer θ).card : ℝ) := by exact_mod_cast Finset.card_union_le _ _
        _ ≤ (ε / 2) * Real.sqrt S.card + (ε / 2) * Real.sqrt S.card := add_le_add hEtrans_real hθ_bound
        _ = ε * Real.sqrt S.card := by ring
    · -- Check every edge u ~ v in S not in E_trans ∪ E_mer θ is properly colored by cθ θ
      intro u hu v hv hadj hnotE
      have hnotT : s(u, v) ∉ E_trans := fun h => hnotE (Finset.mem_union_left _ h)
      have hnotM : s(u, v) ∉ E_mer θ := fun h => hnotE (Finset.mem_union_right _ h)
      have hup_mem : ∀ (j : Fin (R + 1)) (hj : j.1 < R) (i : Fin (layerSize M j.1))
          (k : Fin (layerSize M (j.1 + 1))),
          betweenAdj (layerSize M j.1) i ⟨k.1, lt_of_lt_of_eq k.2 (layerSize_succ M j.1)⟩ →
          ∃ off : Fin 3, upN j hj off i = k := by
        intro j hj i k hbk
        rcases hbk with h | h | h
        · exact ⟨0, Fin.ext h.symm⟩
        · exact ⟨1, Fin.ext h.symm⟩
        · exact ⟨2, Fin.ext h.symm⟩
      rcases u with _ | ⟨j1, i1⟩ <;> rcases v with _ | ⟨j2, i2⟩
      · exact False.elim hadj
      · have hj : j2.1 = R := hadj
        have hnotle : ¬ (j2.1 ≤ t.1) := by omega
        dsimp [cθ]; rw [if_neg hnotle, hj]
        intro heq; simp only [decide_eq_decide] at heq; omega
      · have hj : j1.1 = R := hadj
        have hnotle : ¬ (j1.1 ≤ t.1) := by omega
        dsimp [cθ]; rw [if_neg hnotle, hj]
        intro heq; simp only [decide_eq_decide] at heq; omega
      · dsimp [expGraph] at hadj
        split_ifs at hadj with h0 h12 h21
        · -- Both in layer 0
          intro heq
          apply hnotM
          apply Finset.mem_union_left
          have hj1 : j1 = j0 := Fin.ext h0.1
          have hj2 : j2 = j0 := Fin.ext h0.2
          subst hj1; subst hj2
          have hi1_lt : i1.1 < M := by have := i1.2; dsimp [j0, layerSize] at this; omega
          have hi2_lt : i2.1 < M := by have := i2.2; dsimp [j0, layerSize] at this; omega
          rcases hadj with h | h
          · have hi2 : e0.symm (stepM (e0 i1)) = i2 := by
              ext; simpa [e0, stepM, M] using h.symm
            refine Finset.mem_image.mpr ⟨i1, Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, ?_⟩, ?_⟩
            · rw [hi2]; exact heq
            · rw [hi2]
          · have hi1 : e0.symm (stepM (e0 i2)) = i1 := by
              ext
              have h1 := add_mod_eq i1.1 (m + 1) M hi1_lt (by omega)
              have h2 := add_mod_eq i2.1 m M hi2_lt (by omega)
              have hv : i2.1 = (i1.1 + m + 1) % M := h
              dsimp [e0, stepM, M] at h1 h2 hv ⊢
              rw [Nat.add_assoc] at hv
              rw [h2, hv, h1]
              split_ifs <;> omega
            refine Finset.mem_image.mpr ⟨i2, Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, ?_⟩, ?_⟩
            · rw [hi1]; exact heq.symm
            · rw [hi1, Sym2.eq_swap]
        · -- j2 = j1 + 1
          by_cases hlt : j1.1 < t.1
          · intro heq
            apply hnotM
            apply Finset.mem_union_right
            have hj2_eq : j2 = ⟨j1.1 + 1, by omega⟩ := Fin.ext h12
            let i2' : Fin (layerSize M (j1.1 + 1)) := Fin.cast (by rw [h12]) i2
            have hsig : (⟨j2, i2⟩ : Σ j : Fin (R + 1), Fin (layerSize M j.1)) =
                ⟨⟨j1.1 + 1, by omega⟩, i2'⟩ := by
              refine Sigma.ext hj2_eq ?_
              dsimp [i2']
              exact (fin_cast_heq (by rw [h12]) i2).symm
            have hbk : betweenAdj (layerSize M j1.1) i1
                ⟨i2'.1, lt_of_lt_of_eq i2'.2 (layerSize_succ M j1.1)⟩ := hadj
            obtain ⟨off, hoff⟩ := hup_mem j1 (by omega) i1 i2' hbk
            rw [hsig]
            rw [Finset.mem_biUnion]
            refine ⟨⟨j1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩⟩, Finset.mem_attach _ _, ?_⟩
            rw [Finset.mem_biUnion]
            refine ⟨off, Finset.mem_univ _, Finset.mem_image.mpr ⟨i1, ?_, ?_⟩⟩
            · rw [Finset.mem_filter]
              refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, ?_⟩
              rw [hoff, ← hsig]; exact heq
            · rw [hoff]
          · by_cases heqt : j1.1 = t.1
            · exfalso
              apply hnotT
              have hj1_eq : j1 = t0 := Fin.ext heqt
              have hj2_eq : j2 = t1 := Fin.ext (by dsimp [t1]; omega)
              subst hj1_eq; subst hj2_eq
              obtain ⟨off, hoff⟩ := hup_mem t0 t.2 i1 i2 hadj
              rw [Finset.mem_biUnion]
              refine ⟨off, Finset.mem_univ _, Finset.mem_image.mpr
                ⟨i1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, ?_⟩⟩
              rw [hoff]
            · have h1gt : ¬ (j1.1 ≤ t.1) := by omega
              have h2gt : ¬ (j2.1 ≤ t.1) := by omega
              dsimp [cθ]; rw [if_neg h1gt, if_neg h2gt, h12]
              intro heq; simp only [decide_eq_decide] at heq; omega
        · -- j1 = j2 + 1
          by_cases hlt : j2.1 < t.1
          · intro heq
            apply hnotM
            apply Finset.mem_union_right
            have hj1_eq : j1 = ⟨j2.1 + 1, by omega⟩ := Fin.ext h21
            let i1' : Fin (layerSize M (j2.1 + 1)) := Fin.cast (by rw [h21]) i1
            have hsig : (⟨j1, i1⟩ : Σ j : Fin (R + 1), Fin (layerSize M j.1)) =
                ⟨⟨j2.1 + 1, by omega⟩, i1'⟩ := by
              refine Sigma.ext hj1_eq ?_
              dsimp [i1']
              exact (fin_cast_heq (by rw [h21]) i1).symm
            have hbk : betweenAdj (layerSize M j2.1) i2
                ⟨i1'.1, lt_of_lt_of_eq i1'.2 (layerSize_succ M j2.1)⟩ := hadj
            obtain ⟨off, hoff⟩ := hup_mem j2 (by omega) i2 i1' hbk
            rw [hsig]
            rw [Finset.mem_biUnion]
            refine ⟨⟨j2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩⟩, Finset.mem_attach _ _, ?_⟩
            rw [Finset.mem_biUnion]
            refine ⟨off, Finset.mem_univ _, Finset.mem_image.mpr ⟨i2, ?_, ?_⟩⟩
            · rw [Finset.mem_filter]
              refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, ?_⟩
              rw [hoff, ← hsig]; exact heq.symm
            · rw [hoff, Sym2.eq_swap]
          · by_cases heqt : j2.1 = t.1
            · exfalso
              apply hnotT
              have hj2_eq : j2 = t0 := Fin.ext heqt
              have hj1_eq : j1 = t1 := Fin.ext (by dsimp [t1]; omega)
              subst hj2_eq; subst hj1_eq
              obtain ⟨off, hoff⟩ := hup_mem t0 t.2 i2 i1 hadj
              rw [Finset.mem_biUnion]
              refine ⟨off, Finset.mem_univ _, Finset.mem_image.mpr
                ⟨i2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, ?_⟩⟩
              rw [hoff, Sym2.eq_swap]
            · have h1gt : ¬ (j1.1 ≤ t.1) := by omega
              have h2gt : ¬ (j2.1 ≤ t.1) := by omega
              dsimp [cθ]; rw [if_neg h1gt, if_neg h2gt, h21]
              intro heq; simp only [decide_eq_decide] at heq; omega

/-- Full proof of H1! -/
theorem H1_proof :
    ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (G : SimpleGraph (Fin N)), ¬ G.Colorable 3 ∧
      ∀ S : Finset (Fin N), ∃ (c : Fin N → Bool) (E : Finset (Sym2 (Fin N))),
        (E.card : ℝ) ≤ ε * Real.sqrt S.card ∧
        ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → s(u, v) ∉ E → c u ≠ c v := by
  intro ε hε
  let m : ℕ := Nat.ceil (100 / ε ^ 2) + 1
  have hm : 1 ≤ m := by omega
  let M : ℕ := 2 * m + 1
  have hM_ge : 128 / ε ^ 2 ≤ (M : ℝ) := by
    have hceil : 100 / ε ^ 2 ≤ (Nat.ceil (100 / ε ^ 2) : ℝ) := Nat.le_ceil _
    have hMcast : (M : ℝ) = 2 * ((Nat.ceil (100 / ε ^ 2) : ℝ) + 1) + 1 := by
      dsimp [M, m]; push_cast; ring
    have h128 : 128 / ε ^ 2 ≤ 2 * (100 / ε ^ 2) := by
      rw [← mul_div_assoc]; gcongr; norm_num
    linarith
  have hm_bound : 4 * Real.sqrt (2 / (M : ℝ)) ≤ ε / 2 := by
    have hMpos : (0 : ℝ) < (M : ℝ) := by dsimp [M]; positivity
    have hsq : 2 / (M : ℝ) ≤ (ε / 8) ^ 2 := by
      rw [div_le_iff₀ hMpos]
      have h1 : 128 ≤ (M : ℝ) * ε ^ 2 := (div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).mp hM_ge
      nlinarith
    calc 4 * Real.sqrt (2 / (M : ℝ))
        ≤ 4 * Real.sqrt ((ε / 8) ^ 2) := by gcongr
      _ = 4 * (ε / 8) := by rw [Real.sqrt_sq (by positivity)]
      _ = ε / 2 := by ring
  let R : ℕ := Nat.ceil (6 * (M : ℝ) / ε ^ 2) + 1
  have hR : 1 ≤ R := by omega
  have hR_bound : 3 * (M : ℝ) / (R : ℝ) ≤ ε ^ 2 / 2 := by
    have hRpos : (0 : ℝ) < (R : ℝ) := by dsimp [R]; positivity
    have hceil : 6 * (M : ℝ) / ε ^ 2 ≤ (R : ℝ) := by
      have := Nat.le_ceil (6 * (M : ℝ) / ε ^ 2)
      have hRcast : (R : ℝ) = (Nat.ceil (6 * (M : ℝ) / ε ^ 2) : ℝ) + 1 := by dsimp [R]; push_cast; ring
      linarith
    rw [div_le_iff₀ hRpos]
    have h1 : 6 * (M : ℝ) ≤ (R : ℝ) * ε ^ 2 := (div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).mp hceil
    linarith
  let e : ExpV M R ≃ Fin (Fintype.card (ExpV M R)) := Fintype.equivFin (ExpV M R)
  let G0 := expGraph m R hm
  let G : SimpleGraph (Fin (Fintype.card (ExpV M R))) :=
    { Adj := fun x y => G0.Adj (e.symm x) (e.symm y)
      symm := ⟨fun _ _ h => G0.symm.symm _ _ h⟩
      loopless := ⟨fun x h => G0.loopless.irrefl (e.symm x) h⟩ }
  refine ⟨Fintype.card (ExpV M R), G, ?_, ?_⟩
  · rintro ⟨f⟩
    apply expGraph_not_colorable_three m R hm
    refine ⟨SimpleGraph.Coloring.mk (fun v => f (e v)) ?_⟩
    intro u v huv
    apply f.valid
    show G0.Adj (e.symm (e u)) (e.symm (e v))
    simpa using huv
  · intro S
    let S0 : Finset (ExpV M R) := S.image e.symm
    have hScard : S0.card = S.card := Finset.card_image_of_injective S e.symm.injective
    obtain ⟨c0, E0, hE0_card, hE0_col⟩ := expGraph_bipartize m R hm hR ε hε hm_bound hR_bound S0
    refine ⟨fun x => c0 (e.symm x), E0.image (Sym2.map e), ?_, ?_⟩
    · calc ((E0.image (Sym2.map e)).card : ℝ)
          ≤ (E0.card : ℝ) := by exact_mod_cast Finset.card_image_le
        _ ≤ ε * Real.sqrt S0.card := hE0_card
        _ = ε * Real.sqrt S.card := by rw [hScard]
    · intro u hu v hv hadj hnotE
      apply hE0_col (e.symm u) (Finset.mem_image_of_mem _ hu)
        (e.symm v) (Finset.mem_image_of_mem _ hv) hadj
      intro hmem
      apply hnotE
      refine Finset.mem_image.mpr ⟨s(e.symm u, e.symm v), hmem, ?_⟩
      simp

end H1Proof

theorem OMA.solution : OMA.R_Erdos74_erdos_74_variants_sqrt_R1.H1 :=
  H1Proof.H1_proof
