import OMAReductions.R_Erdos1186_erdos_1186_variants_prs_bounds_R1

-- Adapted from the merged proof of Erdos1186.erdos_1186.variants.prs_bounds by @dk8827.

open Finset
open scoped BigOperators

namespace OMA.PRSBoxBound

def count (n : ℕ) (c : ℕ → Bool) : ℕ :=
  ((Icc 1 n ×ˢ Icc 1 n).filter
    (fun p => c p.1 ≠ c p.2 ∧ p.1 + 1 ≤ 2 * p.2 ∧ 2 * p.2 ≤ p.1 + n)).card

private theorem count_mono {n m : ℕ} (hn : n ≤ m) (c : ℕ → Bool) :
    count n c ≤ count m c := by
  apply card_le_card
  intro p hp
  obtain ⟨ht, hdiff, hlo, hhi⟩ := mem_filter.1 hp
  obtain ⟨hp₁, hp₂⟩ := mem_product.1 ht
  rw [mem_Icc] at hp₁ hp₂
  exact mem_filter.2 ⟨mem_product.2 ⟨mem_Icc.2 ⟨hp₁.1, hp₁.2.trans hn⟩,
    mem_Icc.2 ⟨hp₂.1, hp₂.2.trans hn⟩⟩, hdiff, hlo,
    hhi.trans (Nat.add_le_add_left hn _)⟩

private theorem count_cells_nat :
    (∑ i : Fin 128, ∑ j : Fin 128,
      if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then 1 else 0 : ℕ) = 8192 := by
  have he (i : Fin 128) : (∑ j : Fin 128, if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128
      then 1 else 0 : ℕ) +
      (∑ j : Fin 128, if j.val ≤ 2*((i+64 : Fin 128).val) ∧
        2*((i+64 : Fin 128).val) < j.val+128 then 1 else 0 : ℕ) = 128 := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _ : Fin 128, (1 : ℕ) := by
        apply sum_congr rfl
        intro j _
        have hi := i.isLt
        have hj := j.isLt
        have hval : (i + 64 : Fin 128).val = (i.val+64)%128 := rfl
        rw [hval]
        by_cases h : i.val < 64
        · rw [Nat.mod_eq_of_lt (by omega : i.val + 64 < 128)]
          split_ifs <;> omega
        · rw [Nat.mod_eq_sub_mod (by omega : 128 ≤ i.val + 64),
            Nat.mod_eq_of_lt (by omega : i.val + 64 - 128 < 128)]
          split_ifs <;> omega
      _ = 128 := by simp
  let f (i : Fin 128) := ∑ j : Fin 128,
    if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then (1 : ℕ) else 0
  have hperm : (∑ i, f (i+64)) = ∑ i, f i := by
    exact Fintype.sum_equiv (Equiv.addRight (64 : Fin 128)) (fun i => f (i+64)) f (fun _ => rfl)
  have h := calc
    (∑ i, f i) + (∑ i, f i) = (∑ i, f i) + (∑ i, f (i+64)) := by rw [hperm]
    _ = ∑ i, (f i + f (i+64)) := (sum_add_distrib ..).symm
    _ = ∑ _ : Fin 128, (128 : ℕ) := sum_congr rfl (fun i _ => he i)
    _ = 16384 := by simp
  change (∑ i, f i) = 8192
  omega

set_option maxHeartbeats 1300000 in
theorem all_sizes
    (boxes : ∀ (q : ℕ) (c : ℕ → Bool), 0 < q →
      ∃ x : Fin 128 → ℝ, (∀ i, |x i| ≤ 2*(q : ℝ)) ∧
      (count (256*q) c : ℝ) ≤
        32*(2*(q : ℝ))^2 + ∑ i, ∑ j,
          if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128
          then ((2*(q : ℝ))^2 - x i*x j)/2 else 0)
    (quad : ∀ (Q : ℝ) (x : Fin 128 → ℝ), 0 ≤ Q → (∀ i, |x i| ≤ Q) →
      -682*Q^2 ≤ ∑ i, ∑ j,
        if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then x i*x j else 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (c : ℕ → Bool),
    (count n c : ℝ) ≤ (4469 / 16384 : ℝ) * (n : ℝ) ^ 2 + C * n := by
  refine ⟨18000, by norm_num, ?_⟩
  intro n c
  by_cases hn : n = 0
  · subst n
    simp [count]
  let q := (n+255)/256
  let m := 256*q
  have hq : 0 < q := by dsimp only [q]; omega
  have hnm : n ≤ m := by dsimp only [q,m]; omega
  have hmn : m ≤ n + 255 := by dsimp only [q,m]; omega
  obtain ⟨x, hx, hb⟩ := boxes q c hq
  let Q := 2*(q : ℝ)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hquad := quad Q x hQ hx
  change (count m c : ℝ) ≤ 32*Q^2 + ∑ i : Fin 128, ∑ j : Fin 128,
    if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then (Q^2-x i*x j)/2 else 0 at hb
  have hsum : (∑ i : Fin 128, ∑ j : Fin 128,
      if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then (1 : ℝ) else 0) = 8192 := by
    exact_mod_cast count_cells_nat
  have he (i j : Fin 128) : (if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128
      then (Q^2-x i*x j)/2 else 0) =
      (Q^2/2)*(if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then 1 else 0) -
      (1/2 : ℝ)*(if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then x i*x j else 0) := by
    split_ifs <;> ring
  simp only [he, sum_sub_distrib, ← mul_sum, hsum] at hb
  have hbound : (count m c : ℝ) ≤ 4469*Q^2 := by linarith only [hb,hquad]
  have hmQ : (m : ℝ) = 128*Q := by dsimp only [m,Q]; push_cast; ring
  have hc : (count n c : ℝ) ≤ count m c := by exact_mod_cast count_mono hnm c
  have hmr : (m : ℝ) ≤ (n : ℝ)+255 := by exact_mod_cast hmn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsq : (m : ℝ)^2 ≤ ((n : ℝ)+255)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hmr 2
  have herror : (4469 / 16384 : ℝ)*((n : ℝ)+255)^2 ≤
      (4469 / 16384 : ℝ)*(n : ℝ)^2 + 18000*n := by nlinarith only [hnr]
  calc
    (count n c : ℝ) ≤ (count m c : ℝ) := hc
    _ ≤ 4469*Q^2 := hbound
    _ = (4469/16384 : ℝ)*(m : ℝ)^2 := by rw [hmQ]; ring
    _ ≤ (4469/16384 : ℝ)*((n : ℝ)+255)^2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ ≤ _ := herror

end OMA.PRSBoxBound

open Finset
open scoped BigOperators

namespace OMA.PRSTriangular

def below (q : ℕ) : Finset (ℕ × ℕ) :=
  ((range (2*q) ×ˢ range (2*q)).filter (fun p => 2*p.2 < p.1))

def above (q : ℕ) : Finset (ℕ × ℕ) :=
  ((range (2*q) ×ˢ range (2*q)).filter (fun p => p.1 + 2*q ≤ 2*p.2))

private def key (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.1 % 2 = 0 then (p.2, p.1 / 2) else (p.1 / 2, p.2)

private theorem key_facts {q : ℕ} {p : ℕ × ℕ} (hp : p ∈ below q) :
    (key p).1 < q ∧ (key p).2 < q ∧
    ((key p).1 < (key p).2 ↔ p.1 % 2 = 0) := by
  obtain ⟨hp', hp₀⟩ := mem_filter.1 hp
  obtain ⟨h₁,h₂⟩ := mem_product.1 hp'
  have h₁' := mem_range.1 h₁
  have h₂' := mem_range.1 h₂
  unfold key
  by_cases h : p.1 % 2 = 0
  · rw [if_pos h]
    change p.2 < q ∧ p.1 / 2 < q ∧ (p.2 < p.1 / 2 ↔ p.1 % 2 = 0)
    omega
  · rw [if_neg h]
    change p.1 / 2 < q ∧ p.2 < q ∧ (p.1 / 2 < p.2 ↔ p.1 % 2 = 0)
    omega

theorem below_card (q : ℕ) : (below q).card ≤ q^2 := by
  have hT : (range q ×ˢ range q).card = q^2 := by simp [pow_two]
  rw [← hT]
  apply card_le_card_of_injOn key
  · intro p hp
    obtain ⟨h₁,h₂,_⟩ := key_facts hp
    exact mem_product.2 ⟨mem_range.2 h₁, mem_range.2 h₂⟩
  · intro p hp r hr he
    have hpar : p.1 % 2 = 0 ↔ r.1 % 2 = 0 := by
      rw [← (key_facts hp).2.2, ← (key_facts hr).2.2, he]
    by_cases h : p.1 % 2 = 0
    · have h' := hpar.1 h
      simp only [key, if_pos h, if_pos h', Prod.mk.injEq] at he
      exact Prod.ext (by omega) he.1
    · have h' : r.1 % 2 ≠ 0 := fun e => h (hpar.2 e)
      simp only [key, if_neg h, if_neg h', Prod.mk.injEq] at he
      exact Prod.ext (by omega) he.2

private def reflect (q : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (2*q-1-p.1, 2*q-1-p.2)

theorem above_card (q : ℕ) : (above q).card ≤ q^2 := by
  refine (card_le_card_of_injOn (reflect q) ?_ ?_).trans (below_card q)
  · intro p hp
    obtain ⟨h, hs⟩ := mem_filter.1 hp
    obtain ⟨h₁,h₂⟩ := mem_product.1 h
    have he₁ := mem_range.1 h₁
    have he₂ := mem_range.1 h₂
    change p.1 + 2*q ≤ 2*p.2 at hs
    unfold reflect
    have h₁' : 2*q-1-p.1 < 2*q := by omega
    have h₂' : 2*q-1-p.2 < 2*q := by omega
    have h₃' : 2*(2*q-1-p.2) < 2*q-1-p.1 := by omega
    exact mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 h₁', mem_range.2 h₂'⟩, h₃'⟩
  · intro p hp r hr he
    obtain ⟨hp₁,hp₂⟩ := mem_product.1 (mem_filter.1 hp).1
    obtain ⟨hr₁,hr₂⟩ := mem_product.1 (mem_filter.1 hr).1
    have hp₁' := mem_range.1 hp₁
    have hp₂' := mem_range.1 hp₂
    have hr₁' := mem_range.1 hr₁
    have hr₂' := mem_range.1 hr₂
    have he₁ : 2*q-1-p.1 = 2*q-1-r.1 := congrArg Prod.fst he
    have he₂ : 2*q-1-p.2 = 2*q-1-r.2 := congrArg Prod.snd he
    exact Prod.ext (by omega) (by omega)

end OMA.PRSTriangular

namespace OMA.PRSBoxGeometry

open PRSTriangular

private def directed (i j : Fin 128) : Prop :=
  j.val ≤ 2*i.val ∧ 2*i.val < j.val+128

private def boundary (k : Fin 128 × Fin 128) : Prop :=
  k.1.val = 2*k.2.val + 1 ∨ 2*k.2.val = k.1.val + 128

private instance (k : Fin 128 × Fin 128) : Decidable (boundary k) := by
  unfold boundary
  infer_instance

set_option maxRecDepth 10000 in
private theorem boundary_card :
    ((univ : Finset (Fin 128 × Fin 128)).filter boundary).card ≤ 128 := by
  classical
  calc
    _ ≤ (univ : Finset (Fin 128)).card := by
      apply card_le_card_of_injOn (fun k : Fin 128 × Fin 128 => k.2)
      · intro k hk
        exact mem_univ k.2
      · intro k hk l hl h
        have hk' : boundary k := (mem_filter.1 hk).2
        have hl' : boundary l := (mem_filter.1 hl).2
        unfold boundary at hk' hl'
        have hk₁ := k.1.isLt
        have hl₁ := l.1.isLt
        have he : k.2.val = l.2.val := congrArg Fin.val h
        apply Prod.ext _ h
        apply Fin.ext
        rcases hk' with hk' | hk' <;> rcases hl' with hl' | hl' <;> omega
    _ = 128 := by simp

private theorem quot_geometry (q i j r s : ℕ) (hq : 0 < q)
    (hr : r < 2*q) (hs : s < 2*q)
    (hlo : i*(2*q)+r ≤ 2*(j*(2*q)+s))
    (hhi : 2*(j*(2*q)+s) < i*(2*q)+r+128*(2*q)) :
    (i ≤ 2*j ∧ 2*j < i+128) ∨
      (i = 2*j+1 ∧ r+2*q ≤ 2*s) ∨
      (2*j = i+128 ∧ 2*s < r) := by
  let Q := 2*q
  have hQ : 0 < Q := by omega
  have hmul : 2*(j*Q+s) = (2*j)*Q+2*s := by ring
  change i*Q+r ≤ 2*(j*Q+s) at hlo
  change 2*(j*Q+s) < i*Q+r+128*Q at hhi
  rw [hmul] at hlo hhi
  by_cases low : 2*j < i
  · have hli : i ≤ 2*j+1 := by
      by_contra! hn
      have hm : (2*j+2)*Q ≤ i*Q := Nat.mul_le_mul_right Q (by omega)
      rw [add_mul] at hm
      omega
    have he : i = 2*j+1 := by omega
    rw [he, add_mul, one_mul] at hlo
    exact Or.inr (Or.inl ⟨he, by omega⟩)
  by_cases high : i+128 ≤ 2*j
  · have hji : 2*j ≤ i+128 := by
      by_contra! hn
      have hm : (i+128+1)*Q ≤ (2*j)*Q := Nat.mul_le_mul_right Q (by omega)
      simp only [add_mul, one_mul] at hm
      omega
    have he : 2*j = i+128 := by omega
    rw [he, add_mul] at hhi
    exact Or.inr (Or.inr ⟨he, by omega⟩)
  exact Or.inl ⟨by omega, by omega⟩

private theorem imbalance (P : Finset ℕ) (c : ℕ → Bool) :
    let R := P.filter fun x => c x = true
    let B := P.filter fun x => c x = false
    R.card + B.card = P.card := by
  dsimp only
  simp [← card_filter_add_card_filter_not (s := P) (p := fun x => c x = true)]

set_option maxHeartbeats 3500000 in
set_option maxRecDepth 8000 in
theorem box_geometry (q : ℕ) (c : ℕ → Bool) (hq : 0 < q) :
    let X := ((Icc 1 (256*q) ×ˢ Icc 1 (256*q)).filter
      (fun p => c p.1 ≠ c p.2 ∧ p.1 + 1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1+256*q)).card
    ∃ x : Fin 128 → ℝ, (∀ i, |x i| ≤ 2*(q : ℝ)) ∧
    (X : ℝ) ≤ 32 * (2*(q : ℝ))^2 + ∑ i, ∑ j,
      if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then ((2*(q : ℝ))^2-x i*x j)/2 else 0 := by
  classical
  dsimp only
  let Q := 2*q
  let N := 256*q
  have hQ : 0 < Q := by omega
  have hN : N = 128*Q := by omega
  let X : Finset (ℕ × ℕ) := (Icc 1 N ×ˢ Icc 1 N).filter
      (fun p => c p.1 ≠ c p.2 ∧ p.1 + 1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1+N)
  let key (p : ℕ × ℕ) : Fin 128 × Fin 128 :=
    (⟨((p.1-1)/Q)%128, Nat.mod_lt _ (by decide)⟩,
      ⟨((p.2-1)/Q)%128, Nat.mod_lt _ (by decide)⟩)
  let fine (p : ℕ × ℕ) : ℕ × ℕ := ((p.1-1)%Q, (p.2-1)%Q)
  let fiber (k : Fin 128 × Fin 128) := X.filter (fun p => key p = k)
  let R (i : Fin 128) := (range Q).filter (fun r => c (i.val*Q+r+1) = true)
  let B (i : Fin 128) := (range Q).filter (fun r => c (i.val*Q+r+1) = false)
  let C (k : Fin 128 × Fin 128) := (R k.1 ×ˢ B k.2) ∪ (B k.1 ×ˢ R k.2)
  let x (i : Fin 128) : ℝ := (R i).card - (B i).card
  have hsum (i : Fin 128) : (R i).card + (B i).card = Q := by
    simpa [R,B] using imbalance (range Q) (fun r => c (i.val*Q+r+1))
  have hsumr (i : Fin 128) : ((R i).card : ℝ) + (B i).card = Q := by exact_mod_cast hsum i
  have hQr : (Q : ℝ) = 2*(q : ℝ) := by exact_mod_cast rfl
  have hx (i : Fin 128) : |x i| ≤ (Q : ℝ) := by
    have ha : 0 ≤ ((R i).card : ℝ) := by positivity
    have hb : 0 ≤ ((B i).card : ℝ) := by positivity
    change |((R i).card : ℝ) - (B i).card| ≤ _
    rw [abs_le]
    constructor <;> linarith only [hsumr i, ha, hb]
  refine ⟨x, fun i => hQr ▸ hx i, ?_⟩
  change (X.card : ℝ) ≤ 32*(2*(q : ℝ))^2 + _
  have facts (k : Fin 128 × Fin 128) (p : ℕ × ℕ) (hp : p ∈ fiber k) :
      p.1 = k.1.val*Q+(fine p).1+1 ∧ p.2 = k.2.val*Q+(fine p).2+1 ∧
      (fine p).1 < Q ∧ (fine p).2 < Q ∧ fine p ∈ C k ∧
      (directed k.2 k.1 ∨
        (k.1.val = 2*k.2.val+1 ∧ fine p ∈ above q) ∨
        (2*k.2.val = k.1.val+128 ∧ fine p ∈ below q)) := by
    obtain ⟨hpX,hpk⟩ := mem_filter.1 hp
    obtain ⟨hpI, hpC, hpL, hpH⟩ := mem_filter.1 hpX
    obtain ⟨hp₁,hp₂⟩ := mem_product.1 hpI
    have hp₁' := mem_Icc.1 hp₁
    have hp₂' := mem_Icc.1 hp₂
    have h₁ : (p.1-1)/Q < 128 := (Nat.div_lt_iff_lt_mul hQ).2 (by omega)
    have h₂ : (p.2-1)/Q < 128 := (Nat.div_lt_iff_lt_mul hQ).2 (by omega)
    have hkey₁ : ((p.1-1)/Q)%128 = k.1.val := congrArg (fun k => k.1.val) hpk
    have hkey₂ : ((p.2-1)/Q)%128 = k.2.val := congrArg (fun k => k.2.val) hpk
    rw [Nat.mod_eq_of_lt h₁] at hkey₁
    rw [Nat.mod_eq_of_lt h₂] at hkey₂
    have hr : (fine p).1 < Q := Nat.mod_lt _ hQ
    have hs : (fine p).2 < Q := Nat.mod_lt _ hQ
    have h₃ : (fine p).1 + Q*k.1.val = p.1-1 := by rw [← hkey₁]; exact Nat.mod_add_div _ _
    have h₄ : (fine p).2 + Q*k.2.val = p.2-1 := by rw [← hkey₂]; exact Nat.mod_add_div _ _
    rw [mul_comm Q] at h₃ h₄
    have he₁ : p.1 = k.1.val*Q+(fine p).1+1 := by omega
    have he₂ : p.2 = k.2.val*Q+(fine p).2+1 := by omega
    refine ⟨he₁,he₂,hr,hs,?_,?_⟩
    · cases hcr : c p.1 <;> cases hcs : c p.2
      · exact (hpC (hcr.trans hcs.symm)).elim
      · exact mem_union_right _ (mem_product.2
            ⟨mem_filter.2 ⟨mem_range.2 hr, he₁ ▸ hcr⟩, mem_filter.2 ⟨mem_range.2 hs, he₂ ▸ hcs⟩⟩)
      · exact mem_union_left _ (mem_product.2
            ⟨mem_filter.2 ⟨mem_range.2 hr, he₁ ▸ hcr⟩, mem_filter.2 ⟨mem_range.2 hs, he₂ ▸ hcs⟩⟩)
      · exact (hpC (hcr.trans hcs.symm)).elim
    · change p.1 + 1 ≤ 2*p.2 at hpL
      change 2*p.2 ≤ p.1+N at hpH
      have hlo : k.1.val*Q+(fine p).1 ≤ 2*(k.2.val*Q+(fine p).2) := by omega
      have hhi : 2*(k.2.val*Q+(fine p).2) < k.1.val*Q+(fine p).1+128*Q := by omega
      rcases quot_geometry q k.1.val k.2.val (fine p).1 (fine p).2 hq hr hs hlo hhi with
        h | ⟨he,h⟩ | ⟨he,h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨he,mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 hr, mem_range.2 hs⟩,h⟩⟩)
      · exact Or.inr (Or.inr ⟨he,mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 hr, mem_range.2 hs⟩,h⟩⟩)
  have hinj (k : Fin 128 × Fin 128) : (fiber k : Set (ℕ × ℕ)).InjOn fine := by
    intro p hp r hr h
    have he₁ : (fine p).1 = (fine r).1 := congrArg Prod.fst h
    have he₂ : (fine p).2 = (fine r).2 := congrArg Prod.snd h
    have hp₁ := (facts k p hp).1
    have hp₂ := (facts k p hp).2.1
    have hr₁ := (facts k r hr).1
    have hr₂ := (facts k r hr).2.1
    exact Prod.ext (by omega) (by omega)
  let interior (k : Fin 128 × Fin 128) : ℝ :=
    if directed k.2 k.1 then ((Q : ℝ)^2-x k.1*x k.2)/2 else 0
  let border (k : Fin 128 × Fin 128) : ℝ :=
    if boundary k then (q : ℝ)^2 else 0
  have hcell (k : Fin 128 × Fin 128) : (fiber k).card ≤ interior k+border k := by
    have hb₀ : 0 ≤ border k := by unfold border; split_ifs <;> positivity
    by_cases hi : directed k.2 k.1
    · apply (le_add_of_nonneg_right hb₀).trans' 
      have hsub : (fiber k).card ≤ (C k).card :=
        card_le_card_of_injOn fine (fun p hp => (facts k p hp).2.2.2.2.1) (hinj k)
      have hcard : (C k).card ≤ (R k.1).card*(B k.2).card + (B k.1).card*(R k.2).card := by
        simpa only [C,card_product] using card_union_le (R k.1 ×ˢ B k.2) (B k.1 ×ˢ R k.2)
      have hreal : ((fiber k).card : ℝ) ≤
          (R k.1).card*(B k.2).card + (B k.1).card*(R k.2).card := by
        exact_mod_cast hsub.trans hcard
      unfold interior
      rw [if_pos hi]
      change _ ≤ ((Q : ℝ)^2 - (((R k.1).card : ℝ)-(B k.1).card) *
        (((R k.2).card : ℝ)-(B k.2).card))/2
      have hp := congrArg₂ (· * ·) (hsumr k.1) (hsumr k.2)
      nlinarith only [hreal,hp]
    · unfold interior border
      rw [if_neg hi,zero_add]
      by_cases he : k.1.val = 2*k.2.val+1
      · rw [if_pos (show boundary k from Or.inl he)]
        have hsub : (fiber k).card ≤ (above q).card := by
          apply card_le_card_of_injOn fine _ (hinj k)
          intro p hp
          rcases (facts k p hp).2.2.2.2.2 with h | h | h
          · exact (hi h).elim
          · exact h.2
          · omega
        exact_mod_cast hsub.trans (above_card q)
      · by_cases hf : 2*k.2.val = k.1.val+128
        · rw [if_pos (show boundary k from Or.inr hf)]
          have hsub : (fiber k).card ≤ (below q).card := by
            apply card_le_card_of_injOn fine _ (hinj k)
            intro p hp
            rcases (facts k p hp).2.2.2.2.2 with h | h | h
            · exact (hi h).elim
            · exact (he h.1).elim
            · exact h.2
          exact_mod_cast hsub.trans (below_card q)
        · rw [if_neg (show ¬boundary k from not_or.2 ⟨he,hf⟩)]
          have hempty : fiber k = ∅ := by
            apply eq_empty_iff_forall_notMem.2
            intro p hp
            rcases (facts k p hp).2.2.2.2.2 with h | h | h
            · exact hi h
            · exact he h.1
            · exact hf h.1
          simp [hempty]
  have hfibers : X.card = ∑ k, (fiber k).card := by
    exact card_eq_sum_card_fiberwise (f := key) (s := X) (t := univ) (fun _ _ => mem_univ _)
  have hreal : (X.card : ℝ) = ∑ k, ((fiber k).card : ℝ) := by exact_mod_cast hfibers
  have hborder : (∑ k, border k) ≤ 128*(q : ℝ)^2 := by
    have hc : (((univ : Finset (Fin 128 × Fin 128)).filter boundary).card : ℝ) ≤ 128 := by
      exact_mod_cast boundary_card
    unfold border
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have hinterior : (∑ k, interior k) = ∑ i : Fin 128, ∑ j : Fin 128,
      if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then ((2*(q : ℝ))^2-x i*x j)/2 else 0 := by
    rw [Fintype.sum_prod_type, sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    simp only [interior, directed, hQr, mul_comm (x j) (x i)]
  calc
    (X.card : ℝ) = ∑ k, ((fiber k).card : ℝ) := hreal
    _ ≤ ∑ k, (interior k+border k) := sum_le_sum (fun k _ => hcell k)
    _ = (∑ k, border k) + ∑ k, interior k := by rw [sum_add_distrib, add_comm]
    _ ≤ _ := by rw [hinterior]; exact add_le_add (by nlinarith only [hborder]) le_rfl

end OMA.PRSBoxGeometry

open Finset
open scoped BigOperators

namespace OMA.PRSGram

private theorem nonnegative_of_entry_bound {m : ℕ} (R : Fin m → Fin m → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ i, (m : ℝ)*B ≤ R i i)
    (ho : ∀ i j, i ≠ j → |R i j| ≤ B)
    (x : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, R i j * x i * x j := by
  have hentry (i j : Fin m) :
      (if i = j then (m : ℝ)*B * (x i ^ 2) else 0) -
          B * (x i ^ 2 + x j ^ 2) / 2 ≤ R i j * x i * x j := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      have h := mul_le_mul_of_nonneg_right (hd i) (sq_nonneg (x i))
      have hb := mul_nonneg hB (sq_nonneg (x i))
      linear_combination h + hb
    · rw [if_neg hij, zero_sub]
      have hm : -(B * |x i * x j|) ≤ R i j * (x i * x j) :=
        calc
          _ = -(B * |x i * x j|) := rfl
          _ ≤ -(|R i j| * |x i * x j|) :=
            neg_le_neg (mul_le_mul_of_nonneg_right (ho i j hij) (abs_nonneg _))
          _ = -|R i j * (x i * x j)| := by rw [abs_mul (R i j) (x i * x j)]
          _ ≤ _ := neg_abs_le _
      have hsq : 2 * |x i * x j| ≤ x i^2+x j^2 := by
        have h : |x i * x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
          apply abs_le.2
          constructor
          · linarith only [sq_nonneg (x i + x j)]
          · linarith only [sq_nonneg (x i - x j)]
        linarith only [h]
      have hb := mul_le_mul_of_nonneg_left hsq hB
      nlinarith only [hm, hb]
  have ha := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin m))) =>
    sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin m))) => hentry i j
  have hconst : ∑ i : Fin m, ∑ j : Fin m,
      B * (x i ^ 2 + x j ^ 2) / 2 =
      ∑ i : Fin m, (m : ℝ) * B * x i^2 := by
    have he (i j : Fin m) : B * (x i^2 + x j^2) / 2 =
        (B/2)*x i^2 + (B/2)*x j^2 := by ring
    simp_rw [he, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intros
    ring
  have hdiag : (∑ i : Fin m, ∑ j : Fin m,
      if i = j then (m : ℝ)*B*x i^2 else 0) =
      ∑ i : Fin m, (m : ℝ)*B*x i^2 := by simp
  have hzero : (∑ i : Fin m, ∑ j : Fin m,
      ((if i = j then (m : ℝ)*B * (x i ^ 2) else 0) -
          B * (x i ^ 2 + x j ^ 2) / 2)) = 0 := by
    simp only [sum_sub_distrib, hdiag, hconst, sub_self]
  rw [hzero] at ha
  exact ha

private theorem gram (m : ℕ) (g : Fin m → Fin m → ℝ) (x : Fin m → ℝ) :
    (∑ i, ∑ j, (∑ k, g i k * g j k) * x i * x j) =
      ∑ k, (∑ i, g i k * x i)^2 := by
  simp only [sum_mul]
  have he (i j k : Fin m) : g i k * g j k * x i * x j = (g i k*x i)*(g j k*x j) := by ring
  simp_rw [he]
  calc
    _ = ∑ i, ∑ k, ∑ j, (g i k*x i)*(g j k*x j) := by
      apply sum_congr rfl
      intro i _
      exact sum_comm
    _ = ∑ k, ∑ i, ∑ j, (g i k*x i)*(g j k*x j) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro k _
      rw [pow_two, sum_mul]
      apply sum_congr rfl
      intro i _
      rw [mul_sum]

theorem nonnegative {m : ℕ} (A g R : Fin m → Fin m → ℝ)
    (S B : ℝ) (hS : 0 < S) (hB : 0 ≤ B)
    (hd : ∀ i, (m : ℝ)*B ≤ R i i)
    (ho : ∀ i j, i ≠ j → |R i j| ≤ B)
    (hA : ∀ i j, S * A i j = (∑ k, g i k * g j k) + R i j)
    (x : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, A i j * x i * x j := by
  apply nonneg_of_mul_nonneg_right _ hS
  have he (i j : Fin m) : S * (A i j * x i * x j) =
      (∑ k, g i k * g j k) * x i * x j + R i j * x i * x j := by
    calc
      _ = (S * A i j) * x i * x j := by ring
      _ = _ := by rw [hA, add_mul, add_mul]
  simp_rw [mul_sum, he, sum_add_distrib, gram]
  exact add_nonneg (sum_nonneg fun i _ => sq_nonneg _) (nonnegative_of_entry_bound R B hB hd ho x)

end OMA.PRSGram

namespace OMA.PRSGramData

private def correction : List ℕ :=
  [27, 22, 14, 14, 13, 11, 5, 2, 9, 14, 20, 24, 26, 29, 28, 26,
   26, 26, 26, 25, 24, 23, 23, 21, 22, 21, 27, 30, 37, 41, 48, 50,
   54, 53, 53, 53, 53, 55, 59, 65, 70, 76, 79, 83, 84, 86, 84, 81,
   74, 69, 61, 53, 49, 50, 56, 61, 66, 65, 61, 51, 46, 46, 41, 37,
   37, 41, 46, 46, 51, 61, 65, 66, 61, 56, 50, 49, 53, 61, 69, 74,
   81, 84, 86, 84, 83, 79, 76, 70, 65, 59, 55, 53, 53, 53, 53, 54,
   50, 48, 41, 37, 30, 27, 21, 22, 21, 23, 23, 24, 25, 26, 26, 26,
   26, 28, 29, 26, 24, 20, 14, 9, 2, 5, 11, 13, 14, 14, 22, 27]

def directed (i j : ℕ) : Bool :=
  decide (j ≤ 2*i ∧ 2*i < j + 128)

def entry (i j : ℕ) : ℤ :=
  4 * ((directed i j).toNat + (directed j i).toNat) +
    if i = j then ((correction[i]?.getD 0 : ℕ) : ℤ) else 0

private def rowData0 : List ℕ :=
  [1183212576]

private def rowData1 : List ℕ :=
  [135225068, 1087063100]

private def rowData2 : List ℕ :=
  [135225068, 277549832, 885817290]

private def rowData3 : List ℕ :=
  [135225068, 130364264, 299758884, 868824466]

private def rowData4 : List ℕ :=
  [135225068, 130364264, 299758884, 224284604, 815200814]

private def rowData5 : List ℕ :=
  [135225068, 130364264, 119134728, 286602940, 226603086, 759623626]

private def rowData6 : List ℕ :=
  [135225068, 130364264, 119134728, 286602940, 226603086, 180399934, 551800612]

private def rowData7 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 277269806, 234767210, 246434540, 383795374]

private def rowData8 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 277269806, 234767210, 246434540, 175371810, 629717094]

private def rowData9 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 293316648, 307893736, 241888428, 80060156, 753464896]

private def rowData10 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 293316648, 307893736, 241888428, 80060156, 10242480, 898668148]

private def rowData11 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 376755114, 326515144, 108069880, 33955326, 28081956, 971827148]

private def rowData12 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 376755114, 326515144, 108069880, 33955326, 28081956, 15994607, 1012023802]

private def rowData13 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 512697982, 169692616, 86124722, 71227430, 23940194, 23367676, 1045861842]

private def rowData14 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 512697982, 169692616, 86124722, 71227430, 23940194, 23367676, 63263619, 1024609540]

private def rowData15 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 285793238, 207624140, 171710676, 143947352, 140504922, 100051594, 108304448, 1026372074]

private def rowData16 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 285793238, 207624140, 171710676, 143947352, 140504922, 100051594, 108304448, 13102106, 1026288444]

private def rowData17 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 234621910, 194038548, 170613534, 166533396, 136341042, 147587266, 59668766, 58911866, 1035357048]

private def rowData18 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 234621910, 194038548, 170613534, 166533396, 136341042, 147587266, 59668766, 58911866, 30880380, 1034896430]

private def rowData19 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 196458812, 177963118, 173707220, 153334498, 165982444, 96610014, 95384514, 67118648, 65145762, 1024562114]

private def rowData20 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 196458812, 177963118, 173707220, 153334498, 165982444, 96610014, 95384514, 67118648, 65145762, 48543202, 1003678774]

private def rowData21 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 183107806, 178728874, 165229866, 178859014, 122468776, 120915258, 92485328, 89766812, 69028702, 67126376, 983771372]

private def rowData22 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 183107806, 178728874, 165229866, 178859014, 122468776, 120915258, 92485328, 89766812, 69028702, 67126376, 48602870, 982570036]

private def rowData23 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 176126834, 169056640, 183001442, 145105140, 143264480, 116363486, 112943096, 89570182, 87101764, 65594764, 62430314, 939656134]

private def rowData24 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 176126834, 169056640, 183001442, 145105140, 143264480, 116363486, 112943096, 89570182, 87101764, 65594764, 62430314, 45720606, 959616212]

private def rowData25 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 172589044, 186825222, 166000234, 163894520, 138404850, 134336574, 108531534, 105540570, 81279578, 77358456, 56697734, 52817072, 932513980]

private def rowData26 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 172589044, 186825222, 166000234, 163894520, 138404850, 134336574, 108531534, 105540570, 81279578, 77358456, 56697734, 52817072, 31731772, 1052889080]

private def rowData27 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 177379366, 181909970, 179602440, 158086342, 153439550, 127490606, 123977160, 98598484, 93841858, 70655708, 65819696, 41917084, 35861482, 1104153430]

private def rowData28 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 177379366, 181909970, 179602440, 158086342, 153439550, 127490606, 123977160, 98598484, 93841858, 70655708, 65819696, 41917084, 35861482, 17355194, 1224276764]

private def rowData29 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 198387914, 195871362, 178470750, 173224778, 147126794, 143072202, 116535928, 110913956, 85112186, 79286704, 52466160, 44886574, 21526838, 19109512, 1280571666]

private def rowData30 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 198387914, 195871362, 178470750, 173224778, 147126794, 143072202, 116535928, 110913956, 85112186, 79286704, 52466160, 44886574, 21526838, 19109512, 100115, 1385591492]

private def rowData31 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 197861518, 187341558, 181834838, 160512308, 156088834, 132250778, 125870684, 102175020, 95181676, 69730458, 59656764, 35563266, 31569738, 11862122, 10963898, 1415468192]

private def rowData32 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 197861518, 187341558, 181834838, 160512308, 156088834, 132250778, 125870684, 102175020, 95181676, 69730458, 59656764, 35563266, 31569738, 11862122, 10963898, 2513800, 1470899006]

private def rowData33 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 196212366, 190444896, 173897824, 169105464, 147965628, 140827412, 119237852, 111076648, 86994754, 74426954, 49599694, 44029964, 23824358, 22020332, 11684814, 11224502, 1456809946]

private def rowData34 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 196212366, 190444896, 173897824, 169105464, 147965628, 140827412, 119237852, 111076648, 86994754, 74426954, 49599694, 44029964, 23824358, 22020332, 11684814, 11224502, 1581002, 1456809088]

private def rowData35 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 195056114, 183728218, 178664948, 160730902, 152976858, 134299280, 125107200, 103209894, 88299554, 63837252, 56668732, 36878236, 34085744, 22847154, 21947114, 11623658, 11611050, 1457767970]

private def rowData36 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 195056114, 183728218, 178664948, 160730902, 152976858, 134299280, 125107200, 103209894, 88299554, 63837252, 56668732, 36878236, 34085744, 22847154, 21947114, 11623658, 11611050, 3495382, 1457763780]

private def rowData37 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 193558614, 188224432, 173496176, 165126306, 149360708, 139137752, 119425032, 102172154, 78074808, 69307502, 49932114, 46151156, 34009496, 32669724, 21666314, 21642814, 12285730, 12256306, 1484592558]

private def rowData38 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 193558614, 188224432, 173496176, 165126306, 149360708, 139137752, 119425032, 102172154, 78074808, 69307502, 49932114, 46151156, 34009496, 32669724, 21666314, 21642814, 12285730, 12256306, 2709876, 1537532998]

private def rowData39 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 195777360, 183938456, 175064824, 162157266, 151058454, 133557672, 114263104, 91022358, 80801124, 62238534, 57525710, 45322000, 43536586, 32655590, 32620170, 22805804, 22751186, 12435916, 11985804, 1614311782]

private def rowData40 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 195777360, 183938456, 175064824, 162157266, 151058454, 133557672, 114263104, 91022358, 80801124, 62238534, 57525710, 45322000, 43536586, 32655590, 32620170, 22805804, 22751186, 12435916, 11985804, 3723278, 1675108554]

private def rowData41 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 194815836, 185417454, 175487020, 163475856, 148279174, 126857846, 104509392, 92773648, 75057726, 69374208, 57105864, 54856236, 44102756, 44054918, 33764220, 33683358, 22567212, 21750402, 12249534, 11777720, 1745078824]

private def rowData42 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 194815836, 185417454, 175487020, 163475856, 148279174, 126857846, 104509392, 92773648, 75057726, 69374208, 57105864, 54856236, 44102756, 44054918, 33764220, 33683358, 22567212, 21750402, 12249534, 11777720, 3041756, 1779126430]

private def rowData43 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 193462420, 186305918, 173554258, 160559096, 137363734, 116248500, 103194528, 86594320, 80037228, 68373238, 65679742, 55681820, 55621424, 45500560, 45391592, 34084252, 32850586, 22532794, 21664900, 12154364, 11900982, 1824302538]

private def rowData44 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 193462420, 186305918, 173554258, 160559096, 137363734, 116248500, 103194528, 86594320, 80037228, 68373238, 65679742, 55681820, 55621424, 45500560, 45391592, 34084252, 32850586, 22532794, 21664900, 12154364, 11900982, 4433338, 1835227532]

private def rowData45 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 197124816, 183632660, 172839016, 147869622, 127987606, 113615408, 98130914, 90700248, 79640612, 76503250, 67260884, 67187930, 57236902, 57099826, 45601290, 43950772, 32816052, 31552078, 21266972, 20823620, 12532964, 12428082, 1856992858]

private def rowData46 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 197124816, 183632660, 172839016, 147869622, 127987606, 113615408, 98130914, 90700248, 79640612, 76503250, 67260884, 67187930, 57236902, 57099826, 45601290, 43950772, 32816052, 31552078, 21266972, 20823620, 12532964, 12428082, 4539852, 1835320644]

private def rowData47 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 191745360, 182732402, 156333748, 137749558, 122281154, 107950370, 99776156, 89951078, 86407544, 78504824, 78419672, 69299594, 69133628, 58081992, 55979740, 44520762, 42805958, 32194064, 31522916, 22766304, 22575780, 14275758, 14409020, 1803562854]

private def rowData48 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 191745360, 182732402, 156333748, 137749558, 122281154, 107950370, 99776156, 89951078, 86407544, 78504824, 78419672, 69299594, 69133628, 58081992, 55979740, 44520762, 42805958, 32194064, 31522916, 22766304, 22575780, 14275758, 14409020, 7123104, 1724177552]

private def rowData49 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 192176084, 164413138, 147067778, 130552998, 117323484, 108439518, 99792880, 95861638, 89237670, 89140878, 80813978, 80620436, 69995384, 67461932, 55693432, 53548292, 42624466, 41735876, 32534486, 32262218, 23569118, 23789130, 16090966, 16765356, 1665713946]

private def rowData50 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 192176084, 164413138, 147067778, 130552998, 117323484, 108439518, 99792880, 95861638, 89237670, 89140878, 80813978, 80620436, 69995384, 67461932, 55693432, 53548292, 42624466, 41735876, 32534486, 32262218, 23569118, 23789130, 16090966, 16765356, 8771584, 1566692698]

private def rowData51 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 169584160, 153413508, 136186142, 123981246, 114593142, 107638944, 103398614, 98510296, 98403446, 91455226, 91236200, 81638264, 78683404, 67135806, 64549940, 53799482, 52677926, 43439206, 43075680, 34382978, 34703936, 26943298, 28072522, 20068834, 21224904, 1462796516]

private def rowData52 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 169584160, 153413508, 136186142, 123981246, 114593142, 107638944, 103398614, 98510296, 98403446, 91455226, 91236200, 81638264, 78683404, 67135806, 64549940, 53799482, 52677926, 43439206, 43075680, 34382978, 34703936, 26943298, 28072522, 20068834, 21224904, 13523170, 1406979308]

private def rowData53 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 17621334, 158349066, 140567468, 129159494, 119379284, 113741426, 109260696, 105722322, 105607650, 99731736, 99492888, 90693818, 87411196, 76035410, 73106760, 62491140, 61188390, 51920638, 51486134, 42793740, 43193210, 35383982, 36866964, 28855566, 30517796, 22669628, 23351080, 1421590270]

private def rowData54 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 17621334, 158349066, 140567468, 129159494, 119379284, 113741426, 109260696, 105722322, 105607650, 99731736, 99492888, 90693818, 87411196, 76035410, 73106760, 62491140, 61188390, 51920638, 51486134, 42793740, 43193210, 35383982, 36866964, 28855566, 30517796, 22669628, 23351080, 14720766, 1503563166]

private def rowData55 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 17621334, 13441668, 142621658, 131564782, 121602438, 117298994, 112678116, 110466064, 110346246, 105701930, 105448786, 97675010, 94139708, 83275410, 80067896, 69902546, 68445292, 59463404, 58965778, 50571772, 51043850, 43484024, 45306488, 37598256, 39764112, 32107976, 33073146, 23797516, 22267106, 1569550978]

private def rowData56 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 17621334, 13441668, 142621658, 131564782, 121602438, 117298994, 112678116, 110466064, 110346246, 105701930, 105448786, 97675010, 94139708, 83275410, 80067896, 69902546, 68445292, 59463404, 58965778, 50571772, 51043850, 43484024, 45306488, 37598256, 39764112, 32107976, 33073146, 23797516, 22267106, 14971334, 1631951632]

private def rowData57 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 17621334, 13441668, 11932254, 133515014, 123404994, 120183506, 115448994, 114312336, 114188346, 110542622, 110277884, 103335430, 99595250, 89145672, 85712054, 75911788, 74329258, 65579154, 65030346, 56878278, 57409226, 50051618, 52149336, 44686914, 47261114, 39760682, 40955894, 31157034, 29153336, 20993942, 19998604, 1619754322]

private def rowData58 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 17621334, 13441668, 11932254, 133515014, 123404994, 120183506, 115448994, 114312336, 114188346, 110542622, 110277884, 103335430, 99595250, 89145672, 85712054, 75911788, 74329258, 65579154, 65030346, 56878278, 57409226, 50051618, 52149336, 44686914, 47261114, 39760682, 40955894, 31157034, 29153336, 20993942, 19998604, 14577558, 1569519530]

private def rowData59 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 17621334, 13441668, 11932254, 8570816, 123395966, 121230652, 116454890, 116339634, 116213444, 113639790, 113367634, 107381656, 103495024, 93677238, 90069078, 80836176, 79150988, 70839280, 70246452, 62531108, 63114824, 56155556, 58509098, 51495866, 54462296, 47342938, 48766074, 38642060, 36157002, 27244490, 25952808, 20167770, 20625952, 1436846870]

private def rowData60 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 17621334, 13441668, 11932254, 8570816, 123395966, 121230652, 116454890, 116339634, 116213444, 113639790, 113367634, 107381656, 103495024, 93677238, 90069078, 80836176, 79150988, 70839280, 70246452, 62531108, 63114824, 56155556, 58509098, 51495866, 54462296, 47342938, 48766074, 38642060, 36157002, 27244490, 25952808, 20167770, 20625952, 17076926, 1365370758]

private def rowData61 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 17621334, 13441668, 11932254, 8570816, 7921816, 122125088, 117314090, 118071282, 117943216, 116285284, 116006792, 110837804, 106826080, 97547948, 93790700, 85042422, 83269546, 75332300, 74701872, 67359564, 67988352, 61369332, 63941390, 57311842, 60613302, 53819444, 55437266, 45035514, 42139296, 32583494, 31038688, 24942738, 25509402, 21881114, 22752904, 1365070082]

private def rowData62 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 17621334, 13441668, 11932254, 8570816, 7921816, 122125088, 117314090, 118071282, 117943216, 116285284, 116006792, 110837804, 106826080, 97547948, 93790700, 85042422, 83269546, 75332300, 74701872, 67359564, 67988352, 61369332, 63941390, 57311842, 60613302, 53819444, 55437266, 45035514, 42139296, 32583494, 31038688, 24942738, 25509402, 21881114, 22752904, 17159798, 1289620824]

private def rowData63 : List ℕ :=
  [135225068, 130364264, 119134728, 102446064, 80999148, 82686022, 86795306, 95809164, 31710886, 22269616, 18417564, 18469474, 18027786, 19605166, 21222318, 42499028, 41959928, 41676304, 40451270, 37394338, 36363808, 32176422, 30624154, 26849762, 25012036, 20596888, 17621334, 13441668, 11932254, 8570816, 7921816, 9088284, 117507274, 118976442, 118847394, 118039548, 117756856, 113367678, 109264386, 100592640, 96718118, 88517698, 86672374, 79210472, 78547590, 71672770, 72341822, 66195172, 68969484, 62860240, 66481318, 60211568, 62021538, 51518518, 48205378, 38150376, 36341640, 30049438, 30732120, 27167906, 28250332, 22220954, 23225316, 1225906594]

private def rowData64 : List ℕ :=
  [0, 147185568, 134507050, 115664996, 91450720, 93355256, 97994772, 108171716, 35802640, 25143134, 20794038, 20852648, 20353966, 22134882, 23960700, 47982808, 47374146, 47053928, 45670824, 42219446, 41055942, 36328244, 34575682, 30314270, 28239416, 23254568, 19895068, 15176088, 13471910, 9676734, 8943994, 10260974, 118633766, 120264908, 120134462, 119543634, 119257340, 115035052, 110871410, 102309906, 98369242, 90265472, 88383712, 81021466, 80343426, 73569920, 74256680, 68243742, 71103914, 65145450, 68898166, 62813638, 64701826, 54133610, 50652294, 40412026, 38496062, 32137212, 32867324, 29372786, 30543058, 24373514, 25475170, 20861168, 1219815716]

private def rowData65 : List ℕ :=
  [0, 0, 0, 184156876, 145603936, 97713912, 102570044, 136910074, 45314454, 42939522, 35512124, 31447032, 30694992, 25602930, 27714812, 55412870, 54709958, 54329868, 52732896, 51497742, 50078544, 46438930, 44198606, 40301532, 37543104, 32554878, 27851798, 21620484, 19192640, 14193664, 13118892, 14076422, 13521896, 124487452, 124352426, 124339136, 124041356, 120239036, 115887038, 107864988, 103710360, 96086756, 94083640, 87388092, 86656774, 80542016, 81293860, 76174958, 79367536, 74387668, 78672784, 73870458, 76091016, 65667686, 61444620, 50654078, 48252532, 41807174, 42756974, 39743456, 41326918, 34647226, 36213244, 31439708, 18266480, 1269985816]

private def rowData66 : List ℕ :=
  [0, 0, 0, 0, 0, 210630626, 221098430, 146079264, 48349268, 12027135, 9946759, 7253702, 7080234, 39871078, 43159884, 86793492, 85692516, 85155826, 82652754, 65032142, 63239956, 47159528, 44884438, 32939736, 30685184, 18489528, 15818416, 10515478, 9334656, 5018252, 4638260, 9350806, 8982440, 123443890, 123309996, 127125348, 126820896, 126686580, 122101216, 115590306, 111138122, 104879456, 102693038, 96097580, 95293376, 89303184, 90136812, 84368086, 87904046, 82284434, 87024446, 80477812, 82896990, 70421050, 65892296, 53204500, 50682036, 42902444, 43877126, 39581266, 41158266, 33246450, 34749154, 28972220, 16396686, 8080171, 1323532454]

private def rowData67 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 416888818, 137981730, 63855106, 52809868, 5470720, 5339890, 82868785, 89704299, 72845764, 71921716, 101013532, 98044338, 100057986, 97300540, 93384786, 88879680, 74344862, 69256348, 53246114, 45553852, 15759642, 13989934, 10603301, 9800397, 9630949, 9251547, 9244835, 100594270, 104899630, 104648408, 105671750, 101847008, 99843552, 95997884, 93908988, 91951272, 90856384, 90096040, 89349598, 90183660, 90067726, 93842564, 94182584, 99607992, 99959230, 102964020, 94695956, 88606090, 75772050, 72179644, 65004590, 66481400, 62359972, 64844522, 54954108, 57437974, 49804680, 36967806, 98989, 15190443, 1276323710]

private def rowData68 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 212352296, 175620986, 152144060, 148505610, 116735874, 126364948, 17169738, 16951940, 10795925, 10478589, 26502738, 25772362, 50797220, 48346642, 71048764, 66185848, 84800706, 72549870, 79101742, 70219118, 76278734, 70502758, 63466370, 60966176, 55291224, 165060330, 154362266, 153992584, 138801848, 133777978, 118491394, 113927468, 99620992, 97544198, 87621800, 86888524, 77688172, 78413376, 73186026, 76253332, 71144370, 75242656, 74095140, 76322452, 68994088, 64557100, 58086840, 55332900, 52344432, 53533622, 56354854, 58600148, 56029676, 58562156, 58511876, 50087416, 24222602, 35302368, 37896072, 1372998982]

private def rowData69 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 164638332, 160701088, 145624698, 157636694, 79969748, 78955330, 50809024, 49315542, 31634364, 30762568, 16426450, 15633998, 35358364, 32938270, 50012044, 42786996, 54057614, 47987286, 57764022, 53390018, 55698552, 53504364, 56593502, 56532118, 165583612, 165187056, 159261778, 153497370, 140264696, 134862128, 122382250, 119830954, 107626486, 106725800, 95408954, 96299578, 88251542, 91950262, 83959302, 88795794, 83510834, 86021182, 74360344, 69578254, 59459198, 56640196, 50974024, 52132080, 52242574, 54324026, 49504468, 51742018, 49897846, 41437630, 19358292, 6153720, 40084526, 58747555, 1519806584]

private def rowData70 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 152983878, 165602902, 123501206, 121934592, 96728544, 93885304, 71137196, 69176762, 49103156, 46734302, 29847972, 27805034, 11134884, 9526270, 19873096, 17641472, 26382104, 24384400, 32103162, 30838490, 38695280, 38653310, 153966266, 153597532, 154163920, 148584026, 141208354, 135769442, 128653476, 125971444, 118303270, 117313234, 110370540, 111400828, 104436144, 108813180, 102041734, 107919868, 99640832, 102636054, 87041520, 81443908, 66994652, 63818388, 55161236, 56414420, 53343708, 55469032, 47451052, 49595788, 44668188, 35622864, 12504012, 14409203, 11955884, 18503723, 58355791, 1571267038]

private def rowData71 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 155888886, 153911436, 136794444, 132773506, 109732454, 106708394, 84359506, 80289802, 58262426, 54274668, 31869272, 27265240, 8085170, 7177258, 8670931, 8014351, 1644912, 1580112, 10794164, 10782456, 20089208, 129798248, 135419106, 130517672, 129118182, 124144944, 122535148, 119980664, 117604810, 116620618, 114737528, 115808580, 113915432, 118689754, 117287508, 124043880, 121488880, 125140856, 112551148, 105313020, 89034840, 84813634, 75489484, 77204496, 72368572, 75251884, 63722512, 66602702, 58525502, 48529142, 19535178, 8442763, 35125721, 22526934, 17482285, 55068057, 1579264328]

private def rowData72 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 154536060, 149993626, 136503486, 132741656, 115789208, 110203258, 92388092, 86064612, 66397866, 56805620, 36158026, 32097710, 15253544, 14098516, 2596530, 2494242, 8404537, 8395421, 65761, 109691546, 114968870, 110807624, 111436374, 107144186, 107437562, 105197816, 105577590, 104694050, 105406806, 106390758, 108000890, 112527328, 114770104, 121381460, 123961896, 127688212, 119262390, 111592664, 98421268, 93755046, 87044592, 89022120, 87671306, 91164312, 81581930, 85269344, 77962302, 68222742, 37491772, 17567808, 25914539, 22999878, 1755858, 26831133, 66732213, 1517704766]

private def rowData73 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 156164276, 151860626, 141319756, 134502152, 122510946, 114125716, 98828146, 84550820, 64633142, 57375248, 41361298, 38229340, 24921210, 23939464, 11680774, 11668106, 629132, 627626, 97561490, 94030296, 95599600, 91917396, 93112702, 91171586, 93444630, 92662628, 95146062, 96034232, 100434742, 104644074, 109775490, 116099130, 123155666, 126857746, 122315060, 114449018, 104604754, 99645368, 95611654, 97783814, 99999692, 103983886, 96708364, 101079478, 96637040, 87409160, 57317398, 46403072, 48004, 18191394, 19938806, 3935192, 31480487, 59645745, 1454422418]

private def rowData74 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 162639414, 154793300, 148637258, 138463820, 127682286, 109236514, 91067724, 80841396, 66486910, 61452392, 48017580, 46125974, 34117216, 34080210, 22107624, 22054678, 117418826, 113168904, 96452782, 92737716, 77177378, 75568466, 77910374, 77258372, 79756248, 80500758, 85676692, 89267496, 95136778, 100617152, 109566220, 112859798, 111094448, 103950000, 97471758, 92850554, 91101510, 93171206, 97865234, 101764388, 97100832, 101489686, 99941272, 91583518, 64802842, 59398856, 23925212, 8610710, 19773428, 18303980, 3716865, 28620313, 54545307, 1378351126]

private def rowData75 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170275056, 158620622, 152242130, 130248288, 114545938, 101683156, 89560098, 82778432, 70552328, 67772988, 57275346, 57213220, 45580304, 45471144, 32679228, 135559224, 117848130, 113308980, 96782750, 94765126, 80828948, 80152520, 67090642, 67716922, 73151914, 76217792, 82294660, 87035262, 97106100, 100025126, 100283562, 93834358, 90095346, 85823862, 85884360, 87835528, 94480518, 98244816, 95798310, 100128288, 101110248, 93598642, 70623306, 67112060, 46891106, 6256684, 15939460, 26922334, 18151086, 969499, 23458773, 40953033, 1368984618]

private def rowData76 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 171579198, 146791804, 133626110, 118620744, 108752668, 100517702, 90704596, 87131378, 79252132, 79166170, 69157380, 68991756, 57073320, 159070384, 140725510, 135305194, 118140246, 115677382, 100830470, 99986656, 86119908, 86923820, 74616750, 77744020, 65214964, 68971686, 77584010, 79916198, 80605056, 75421372, 73553716, 70066482, 70999492, 72612498, 79594990, 82766220, 82051890, 85760548, 88454874, 81844532, 63697052, 58880044, 58073898, 1474716, 4380300, 18644016, 24809680, 16748828, 4238548, 9894541, 31888915, 1430787756]

private def rowData77 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144907398, 128635214, 120588680, 111457468, 104653142, 100530434, 95736784, 95632942, 88075140, 87864208, 77771756, 74956842, 161840124, 155606538, 139293506, 136389660, 122055346, 121033910, 107727708, 108733326, 96973910, 101038194, 89198282, 94336568, 82639984, 85124156, 68074688, 63696826, 62132450, 59186706, 59984738, 61347506, 67673796, 70370060, 70141698, 73312026, 76425886, 70311012, 55338532, 46663294, 58318336, 4460478, 884063, 5666932, 19589240, 20823992, 18124058, 12573500, 3473575, 24357251, 1540262552]

private def rowData78 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 124944198, 115483178, 111095220, 106718734, 104326796, 104213638, 98886026, 98649204, 90413366, 87140896, 174950386, 168211834, 152714152, 149530528, 135713860, 134578122, 121812248, 122949342, 111641544, 116320566, 105029632, 111079886, 99731040, 102728972, 84510956, 79076084, 61990862, 59051830, 48270678, 49367318, 54020442, 56172728, 55604424, 58117684, 60570672, 54652406, 41314498, 29465208, 44567332, 3506794, 8891611, 9691031, 3849608, 12335968, 18394610, 19817662, 9377694, 11225525, 33622473, 1636361390]

private def rowData79 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 113036804, 108583830, 108085744, 107968508, 104628688, 104378112, 97915740, 94371724, 84239218, 176510780, 162539024, 159150580, 146679526, 145452020, 134009482, 135260434, 125318588, 130570828, 120783036, 127740768, 117944532, 121489964, 103033862, 96407788, 77962204, 74265960, 62975340, 64406050, 58457966, 60787052, 49487730, 51724520, 53167742, 47154982, 33647254, 19620506, 29200312, 7901710, 8471119, 16227459, 10443011, 729924, 11270266, 19139180, 16256240, 657488, 21076561, 39728819, 1693496550]

private def rowData80 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 109829014, 109709886, 108007270, 107748604, 102788088, 99067720, 90103066, 182148770, 169232150, 165704176, 154148600, 152858588, 142316396, 143644892, 134612794, 140254566, 131468838, 139042130, 130255290, 134170786, 115519642, 108090612, 88683606, 84479052, 72810466, 74464614, 68639934, 71374690, 59235140, 61912504, 52340680, 46113354, 22294286, 6962126, 11023052, 5155414, 13712985, 26481957, 26882019, 16241191, 2017093, 10825004, 13467144, 2249628, 18207423, 37826673, 54218773, 1765497876]

private def rowData81 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 109756836, 109493980, 105961440, 102126214, 94445198, 90807458, 175216766, 171564030, 161597372, 160245024, 151247236, 152659100, 145354652, 151446626, 144528458, 152854050, 146217566, 150612890, 132425936, 123909668, 103839882, 98916760, 87233154, 89214966, 84176514, 87530278, 74690278, 78066198, 68226122, 61629066, 35772092, 19387324, 5771396, 13500426, 13161069, 29966583, 38372445, 33838479, 19527331, 2419763, 7098080, 3772070, 12647379, 31086227, 48482639, 65526419, 1791357798]

private def rowData82 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 107773678, 103872858, 97511978, 93756116, 179367178, 175627918, 166866872, 165470426, 157643206, 159114774, 153131504, 159549416, 154057174, 162931670, 157954406, 162702542, 144923446, 135603466, 115099870, 109642902, 97991830, 100218064, 95814694, 99632150, 86312332, 90213556, 80217678, 73354010, 45984528, 29032444, 9186272, 25681090, 656533, 20225397, 42160337, 42329061, 38021005, 17938249, 3774193, 721353, 13378481, 30214739, 48008207, 65918599, 86779037, 1801309786]

private def rowData83 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99113444, 95295898, 90347516, 178395822, 171287882, 169854438, 163622994, 165150382, 161084636, 167835872, 164396094, 173866166, 171439256, 176592750, 159831016, 149552334, 129019490, 122902584, 111669848, 114206826, 111050936, 115475434, 101932180, 106539404, 96782966, 89690176, 60716720, 44234646, 17104602, 39530312, 16302690, 4647571, 32487167, 37884033, 38916789, 16318197, 5165831, 5199802, 10061783, 24107543, 41568293, 59459423, 81795713, 104830197, 1769514430]

private def rowData84 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 91686402, 179706798, 173626312, 172173300, 166932320, 168490600, 165634768, 172576704, 170429584, 180247216, 179451950, 184846306, 168788122, 157933412, 137470084, 130952530, 120038848, 122765958, 120448598, 125247520, 111633660, 116679380, 107146872, 99934586, 70052182, 54005230, 22639334, 47873480, 26820652, 5391826, 25762435, 34318129, 38661139, 15617881, 1151117, 13659102, 963190, 11616665, 34797005, 52593311, 80867585, 104726241, 130802751, 1745723278]

private def rowData85 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 175409502, 173941566, 169973642, 171560312, 170319092, 177457356, 177028156, 187225900, 188674532, 194346120, 179409482, 167871716, 147761956, 140756458, 130431886, 133395112, 132349146, 137622210, 124122770, 129732984, 120715276, 113417858, 82628202, 67572688, 31621664, 57835210, 40314458, 19412290, 14946797, 27302827, 35886413, 15637629, 2811574, 23382610, 14568382, 4373796, 18129653, 35488257, 64237835, 88205717, 119767689, 145595841, 1690375030]

private def rowData86 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87704752, 86970782, 171147626, 172745256, 172496068, 179725570, 180348284, 190737284, 193604250, 199424026, 185273416, 173358542, 153606834, 146324226, 136451490, 139551474, 139377620, 144930712, 131616772, 137565706, 128991844, 121686858, 90543802, 76198874, 38249046, 63714386, 48292020, 28361084, 7249699, 21614003, 32596575, 14159361, 4632766, 28606072, 22407212, 13910218, 7854949, 24706863, 53434845, 77224113, 108942071, 134616295, 168319753, 1651663048]

private def rowData87 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87182650, 85577328, 86376176, 174967846, 182300942, 184451692, 195077072, 200048652, 206062148, 193152518, 180730942, 161640752, 153977250, 144851882, 148142710, 149329220, 155278804, 142349638, 148783688, 140983050, 133711578, 102257074, 89047760, 49002276, 72034316, 59595834, 41723770, 5004632, 11958551, 26228585, 10523267, 6673714, 35464208, 33302790, 27508554, 7139296, 8738181, 37122497, 60407075, 92063093, 117270161, 151056337, 175766143, 1572704992]

private def rowData88 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87182650, 85577328, 86376176, 86254552, 89869576, 186238990, 196967326, 203404566, 209518942, 197570554, 184864856, 166408818, 158519256, 150017578, 153425762, 155652968, 161854504, 149341296, 156091360, 148992440, 141810538, 110465676, 98050026, 57832284, 77728964, 67067984, 51113598, 14661418, 3473543, 19519059, 5654259, 9569714, 39143226, 39964524, 36282744, 17301118, 2423000, 25256793, 47821163, 78987079, 103508909, 136863173, 160774107, 192021733, 1505568494]

private def rowData89 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 86160806, 86965100, 87336522, 90996894, 91834206, 97124334, 208646516, 214918466, 204523766, 191370908, 173955878, 165708506, 158221804, 161816376, 165728436, 172331398, 160506934, 167761674, 161816734, 154791402, 123691888, 112489450, 72245938, 87098664, 79174306, 66169016, 30311756, 10459864, 8276097, 2713976, 15761238, 44944966, 50552200, 50281906, 33591886, 20374660, 6082453, 27412625, 57698835, 81048117, 113606087, 140755033, 171493921, 199633595, 1420853936]

private def rowData90 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 86160806, 86965100, 87336522, 90996894, 91834206, 97124334, 99266984, 102250966, 208118684, 194734640, 178465304, 170004136, 163514430, 167229244, 172659888, 179539014, 168538070, 176155808, 171448370, 164682634, 134465762, 124020362, 86386424, 95222838, 88659924, 78209428, 44822610, 25046608, 5426816, 14491446, 24868666, 50981250, 57394894, 60223448, 46137596, 34869396, 10326132, 9256955, 37922895, 59605249, 90518061, 115685527, 144205589, 169539501, 207604585, 1369857366]

private def rowData91 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87178228, 88016810, 91705692, 93036594, 98395986, 101226054, 104268926, 98004466, 91701830, 184182864, 175450624, 170150428, 174016002, 181277182, 188499640, 178466678, 186533178, 183300440, 176839304, 147647682, 138047142, 103365098, 105464850, 100542504, 92837144, 62231354, 42483924, 21769522, 28560570, 35786602, 60223794, 66022768, 72557494, 61547008, 52587104, 30289456, 12773916, 13995137, 33710829, 62702631, 85522111, 116162809, 138883495, 174906111, 202312251, 1344436376]

private def rowData92 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87178228, 88016810, 91705692, 93036594, 98395986, 101226054, 104268926, 98004466, 91701830, 82242882, 78343688, 172670640, 176593470, 184891702, 192258168, 182893128, 191159698, 188890540, 182683464, 154522854, 145085960, 113576614, 111772194, 106931986, 100363862, 72264808, 53709596, 33554344, 39681462, 45388788, 67150548, 71102294, 78015164, 69067862, 61705324, 41220460, 25313922, 187016, 18002285, 45273923, 66241063, 94587155, 114611783, 147818499, 173152713, 202529279, 1349707856]

private def rowData93 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 88713294, 92431366, 94267610, 99697916, 103231768, 106334932, 100498254, 94035244, 84819836, 80798466, 76608114, 78348540, 190974308, 198583118, 190013968, 198602392, 197537228, 191614230, 164509832, 155449570, 126756936, 120736918, 116552898, 111497840, 85641100, 67886894, 47736552, 52675728, 56289570, 76963596, 80281742, 86913862, 80471590, 75035974, 56584952, 42533610, 19206938, 2770780, 22648733, 41482351, 72152505, 89822351, 120875999, 144715069, 174162087, 192388347, 1351682966]

private def rowData94 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 88713294, 92431366, 94267610, 99697916, 103231768, 106334932, 100498254, 94035244, 84819836, 80798466, 76608114, 78348540, 79619366, 82791566, 193728916, 202485252, 202532470, 196954188, 171350084, 162051526, 137475324, 128938362, 123877200, 119161304, 96018852, 80756832, 62549784, 67697652, 70264100, 87695254, 88317830, 93110330, 87510818, 83979408, 67906114, 55950114, 34879898, 20417208, 2610729, 18994163, 46457147, 60480623, 87351857, 107825913, 135249491, 151824791, 175624341, 1367787352]

private def rowData95 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 92797868, 95120900, 100600360, 104833946, 107985272, 102607508, 96008854, 87096202, 82966908, 79074316, 80870772, 82638446, 85930932, 79856768, 83466206, 210801838, 205645280, 181780534, 172392736, 152010006, 140745000, 135127438, 131132394, 110609916, 97915840, 81539950, 86568540, 87529462, 101972874, 100977722, 104509364, 98839362, 97757006, 84589094, 75239126, 56891894, 44879080, 24705116, 11370086, 12216659, 26965379, 49824953, 67176547, 93180763, 108405483, 132288849, 141990493, 1395668476]

private def rowData96 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 92797868, 95120900, 100600360, 104833946, 107985272, 102607508, 96008854, 87096202, 82966908, 79074316, 80870772, 82638446, 85930932, 79856768, 83466206, 80286184, 76709992, 186866078, 176878106, 160891282, 150560490, 142990154, 138106548, 119757526, 110757806, 98092146, 104692020, 105638080, 116691508, 112275954, 112964130, 106176628, 105524988, 95167442, 88300516, 72779028, 63108340, 45954782, 35606038, 16121552, 5932996, 11283931, 23765431, 46056417, 58339413, 80251265, 91744557, 108017021, 1358710200]

private def rowData97 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96054908, 101588172, 106587682, 109791726, 104916290, 98169156, 89587900, 85340474, 81773810, 83631594, 85943116, 89367266, 83510472, 87285054, 84471738, 80942352, 65170076, 59924762, 164047966, 158927338, 149239104, 143062056, 125630334, 119640236, 110545522, 118808400, 120103618, 129550906, 123941878, 122854792, 115322426, 113636474, 105660396, 100988318, 88114090, 80656316, 66364278, 58878118, 43347696, 31846980, 19145584, 10755090, 8205921, 17701101, 37489477, 49652717, 70136619, 81411865, 1339406800]

private def rowData98 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96054908, 101588172, 106587682, 109791726, 104916290, 98169156, 89587900, 85340474, 81773810, 83631594, 85943116, 89367266, 83510472, 87285054, 84471738, 80942352, 65170076, 59924762, 38687920, 45854168, 148174644, 142644812, 124428662, 119154308, 111933722, 121753176, 125062358, 134917650, 129094240, 126572602, 118054166, 114867612, 107074750, 103552872, 92287304, 86037096, 73511874, 67653610, 54650038, 45892904, 37250100, 33074176, 18552530, 12669870, 3364001, 13698961, 34342637, 47320769, 63446145, 1247195884]

private def rowData99 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102125962, 107897704, 111141128, 106811420, 99942412, 91766126, 87415428, 84219650, 86133000, 89031720, 92578928, 87002052, 90934452, 88559108, 85104954, 69530218, 64688466, 43905672, 48879634, 46718296, 41883774, 125124794, 122404710, 117985934, 128256792, 131024906, 138322308, 132646926, 129694202, 121632212, 118162704, 110713130, 108958214, 100010354, 95568312, 85492742, 81829208, 71980914, 66550938, 55867160, 54729374, 43133504, 39627460, 25924820, 16135550, 5905175, 21335689, 40891933, 47463355, 1186020526]

private def rowData100 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102125962, 107897704, 111141128, 106811420, 99942412, 91766126, 87415428, 84219650, 86133000, 89031720, 92578928, 87002052, 90934452, 88559108, 85104954, 69530218, 64688466, 43905672, 48879634, 46718296, 41883774, 23811798, 12527714, 111287002, 125436990, 132091234, 141389396, 135573700, 130945390, 121185622, 115650168, 106318222, 103566074, 95034864, 90738558, 81306764, 78101488, 69386848, 65053892, 56765292, 58612772, 51072682, 50723676, 41011714, 34579316, 15895560, 2905924, 15563383, 21741493, 35986595, 1077493634]

private def rowData101 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 109379534, 112667500, 108955092, 101948226, 94230022, 89762510, 86986256, 88962460, 92525390, 96211792, 90951548, 95062458, 93182528, 89813472, 74462186, 70076918, 49807722, 52301884, 51039516, 47514076, 30088058, 18422454, 6377270, 9054524, 129409200, 142461578, 141380732, 138628710, 129360994, 123141028, 112460866, 108063618, 99805866, 95801110, 86582810, 83897600, 75995014, 72903392, 58965978, 61942942, 55937666, 57321554, 49587102, 45529356, 29106734, 18795138, 2138950, 2580655, 15577471, 14581815, 1024553778]

private def rowData102 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 109379534, 112667500, 108955092, 101948226, 94230022, 89762510, 86986256, 88962460, 92525390, 96211792, 90951548, 95062458, 93182528, 89813472, 74462186, 70076918, 49807722, 52301884, 51039516, 47514076, 30088058, 18422454, 6377270, 9054524, 12534258, 28030198, 139307574, 138470896, 130497824, 124188506, 113216640, 107859908, 99871760, 96701428, 88512878, 86547198, 79681200, 77665552, 65503778, 70705764, 67438274, 71373474, 66580890, 65196830, 50933462, 42707518, 27052728, 23131178, 9953068, 11841444, 4287011, 910964508]

private def rowData103 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 113718802, 110682062, 103564134, 96396314, 91826096, 89528792, 91562758, 95855204, 99674274, 94809642, 99094934, 97809490, 94565142, 79637870, 75616278, 56600700, 56204672, 55596330, 53298196, 37058958, 25429810, 12960042, 14712328, 16909394, 30929982, 38716356, 43334424, 132887950, 127828018, 118411964, 113786316, 106933168, 105747340, 100120302, 100345900, 96574226, 97703728, 89706008, 89593724, 88035772, 93337512, 89919144, 88461062, 72678728, 62403852, 44597588, 39796496, 24244154, 27256392, 11678050, 2599588, 925699748]

private def rowData104 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 113718802, 110682062, 103564134, 96396314, 91826096, 89528792, 91562758, 95855204, 99674274, 94809642, 99094934, 97809490, 94565142, 79637870, 75616278, 56600700, 56204672, 55596330, 53298196, 37058958, 25429810, 12960042, 14712328, 16909394, 30929982, 38716356, 43334424, 38408868, 34300552, 112433752, 107557652, 100925662, 99945702, 95665888, 96689840, 94482394, 96865638, 91471618, 94081326, 96202448, 104118840, 104150354, 105170308, 91834788, 83065154, 66229912, 62042982, 46720516, 49778456, 35076202, 24837984, 6327237, 910469314]

private def rowData105 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 112550010, 105311956, 98739448, 94058140, 92278882, 94375326, 99456842, 103419408, 98982682, 103456592, 102814164, 99704706, 85236060, 81607830, 63948210, 60426058, 60525132, 59554490, 44598912, 33009198, 20080184, 20831994, 21641686, 34066484, 42271874, 48500128, 44927718, 41832132, 31642060, 23864300, 101555616, 100640648, 97825612, 99982168, 99600032, 103732732, 101120044, 96889762, 100619628, 109703392, 111438606, 113723368, 101719372, 93998738, 78242164, 75235450, 60660250, 65020274, 51822604, 42105200, 9065348, 985272, 950521130]

private def rowData106 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 112550010, 105311956, 98739448, 94058140, 92278882, 94375326, 99456842, 103419408, 98982682, 103456592, 102814164, 99704706, 85236060, 81607830, 63948210, 60426058, 60525132, 59554490, 44598912, 33009198, 20080184, 20831994, 21641686, 34066484, 42271874, 48500128, 44927718, 41832132, 31642060, 23864300, 11135330, 2213124, 82941302, 84479100, 83805418, 87198992, 84878428, 81640582, 88049660, 99010868, 104031652, 110366916, 104475210, 102851224, 92927828, 94021968, 84166800, 90032132, 78847844, 71141172, 39698150, 27786820, 6303634, 961088520]

private def rowData107 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106413886, 100430296, 95668826, 94382220, 96526450, 102334438, 106411654, 102410230, 107039060, 107032152, 104073872, 90181766, 86796738, 70981216, 64437026, 64899418, 64969106, 51607728, 40447836, 27483714, 27509664, 27116006, 37844924, 45015042, 52718638, 50503496, 48439546, 39348962, 32555198, 20791706, 12806756, 117789, 9321297, 76862348, 80207158, 78266804, 76048272, 74884076, 86045408, 92238524, 100696954, 98755478, 101647240, 96803784, 102128530, 97044866, 106046078, 98064822, 94416640, 65913132, 54070604, 31668576, 23352654, 983415708]

private def rowData108 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106413886, 100430296, 95668826, 94382220, 96526450, 102334438, 106411654, 102410230, 107039060, 107032152, 104073872, 90181766, 86796738, 70981216, 64437026, 64899418, 64969106, 51607728, 40447836, 27483714, 27509664, 27116006, 37844924, 45015042, 52718638, 50503496, 48439546, 39348962, 32555198, 20791706, 12806756, 117789, 9321297, 24873197, 39040445, 49232956, 46179782, 45503460, 57369542, 65222290, 78202668, 84048728, 96100570, 100330212, 112605978, 115947642, 128569780, 124235086, 126229592, 104607084, 92601062, 68765120, 48901298, 23259292, 1000457648]

private def rowData109 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 101939984, 97106936, 96260200, 98447094, 104903720, 109083300, 105470538, 110237692, 110798212, 107974912, 94597574, 91429688, 77260682, 68018246, 68805028, 69803584, 57865598, 47089476, 34094006, 33471866, 32003790, 41218530, 47464300, 56485162, 55481866, 54339020, 46230120, 40314926, 29413468, 22265350, 10234402, 2033816, 12326065, 25053733, 47994933, 71360993, 18632028, 29618514, 36906070, 52303342, 62840560, 81933756, 93461160, 112536150, 122764296, 140630894, 139649866, 148702420, 133825710, 125763896, 102197422, 76688486, 44759206, 8997616, 1006057220]

private def rowData110 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 101939984, 97106936, 96260200, 98447094, 104903720, 109083300, 105470538, 110237692, 110798212, 107974912, 94597574, 91429688, 77260682, 68018246, 68805028, 69803584, 57865598, 47089476, 34094006, 33471866, 32003790, 41218530, 47464300, 56485162, 55481866, 54339020, 46230120, 40314926, 29413468, 22265350, 10234402, 2033816, 12326065, 25053733, 47994933, 71360993, 100376949, 106783449, 2157536, 20933120, 37815142, 65882822, 86507858, 113602010, 132225838, 155671964, 158235154, 175104154, 167606838, 163448228, 138941866, 105570848, 63824322, 11101956, 40895643, 970313548]

private def rowData111 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 98042122, 97569916, 99786566, 106782132, 111036552, 107770898, 112642026, 113703304, 111012034, 98170500, 95087656, 82567454, 71296078, 72125548, 73715108, 63079834, 52923290, 40218402, 39251226, 36993902, 44818262, 50104054, 59321432, 59390342, 59077624, 51910802, 46831778, 36783722, 30428848, 19291842, 12053890, 1113519, 12440085, 33917903, 56207215, 84839737, 98666819, 109305793, 106282253, 15168000, 46917920, 72191510, 104685708, 128450722, 157664840, 164300930, 188861250, 186617636, 188862300, 165640384, 132274142, 86203000, 26652618, 33953341, 104467363, 937791288]

private def rowData112 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 98042122, 97569916, 99786566, 106782132, 111036552, 107770898, 112642026, 113703304, 111012034, 98170500, 95087656, 82567454, 71296078, 72125548, 73715108, 63079834, 52923290, 40218402, 39251226, 36993902, 44818262, 50104054, 59321432, 59390342, 59077624, 51910802, 46831778, 36783722, 30428848, 19291842, 12053890, 1113519, 12440085, 33917903, 56207215, 84839737, 98666819, 109305793, 106282253, 99472403, 79954693, 58476910, 96017540, 124777832, 159202552, 169858050, 201892648, 205148720, 213252464, 191317192, 157605600, 107459120, 41023000, 27808063, 107197505, 183469053, 888874328]

private def rowData113 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 98780412, 101024562, 108518238, 112841830, 109896988, 114864212, 116388312, 113819070, 101472748, 98468506, 87472198, 74325590, 75194510, 77330302, 67899050, 58315148, 45878828, 44592756, 41605976, 48145284, 52543824, 61942832, 63002720, 63457242, 57161126, 52854930, 43595622, 37973896, 27663112, 21314864, 9249588, 782021, 20907319, 42201455, 70479591, 91165087, 102921479, 101697325, 97605595, 80959737, 64421799, 43198353, 108623436, 147929114, 163309644, 202653170, 209333342, 225279004, 206908340, 180749110, 132652320, 70177678, 1066326, 75559353, 153454123, 249151253, 902013876]

private def rowData114 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 98780412, 101024562, 108518238, 112841830, 109896988, 114864212, 116388312, 113819070, 101472748, 98468506, 87472198, 74325590, 75194510, 77330302, 67899050, 58315148, 45878828, 44592756, 41605976, 48145284, 52543824, 61942832, 63002720, 63457242, 57161126, 52854930, 43595622, 37973896, 27663112, 21314864, 9249588, 782021, 20907319, 42201455, 70479591, 91165087, 102921479, 101697325, 97605595, 80959737, 64421799, 43198353, 26281481, 5069255, 159081002, 206096016, 217415090, 240691710, 225968506, 206083434, 159950060, 100110486, 30641748, 42930609, 119512403, 209757587, 300477109, 885872164]

private def rowData115 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 101942026, 109891564, 114269870, 111638956, 116684916, 118657206, 116216354, 104414114, 101401622, 92035978, 77352258, 78066568, 80550280, 72321848, 63514830, 51590494, 50175216, 46607838, 51859884, 55285050, 64095326, 66117040, 67328204, 61935220, 58425574, 50003422, 45134992, 35707692, 30282410, 19395650, 10721492, 7909291, 28047723, 55747499, 75945061, 94975309, 95621993, 94398957, 80935401, 67139717, 47610163, 32772541, 11676713, 3438071, 23064830, 211619490, 244178492, 235946734, 229381462, 191725896, 144599708, 82902506, 24486772, 41188303, 109500879, 187674613, 287696083, 843413212]

private def rowData116 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 101942026, 109891564, 114269870, 111638956, 116684916, 118657206, 116216354, 104414114, 101401622, 92035978, 77352258, 78066568, 80550280, 72321848, 63514830, 51590494, 50175216, 46607838, 51859884, 55285050, 64095326, 66117040, 67328204, 61935220, 58425574, 50003422, 45134992, 35707692, 30282410, 19395650, 10721492, 7909291, 28047723, 55747499, 75945061, 94975309, 95621993, 94398957, 80935401, 67139717, 47610163, 32772541, 11676713, 3438071, 23064830, 38777270, 67243792, 237778576, 241624270, 212689182, 177837112, 125662780, 82595760, 31939112, 10354393, 67271457, 132541745, 219105931, 865567322]

private def rowData117 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 111354942, 115791552, 113495152, 118625010, 121074882, 118770838, 107548358, 104527074, 96899024, 80577398, 81126958, 83981404, 77034664, 69055478, 57676698, 56123740, 51937690, 55818062, 58206028, 66388970, 69435580, 71453004, 67022372, 64361508, 56831408, 52765668, 44279790, 39837994, 30207030, 22979336, 5941070, 12965877, 40049365, 59726997, 86508077, 89148277, 90982047, 80909469, 70035861, 52311275, 39689245, 18717449, 10208225, 15969970, 29974578, 59403064, 62721850, 74069228, 223270678, 204919090, 167011920, 144461788, 112266574, 100901388, 70092144, 47492380, 15375465, 72456891, 831058230]

private def rowData118 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 111354942, 115791552, 113495152, 118625010, 121074882, 118770838, 107548358, 104527074, 96899024, 80577398, 81126958, 83981404, 77034664, 69055478, 57676698, 56123740, 51937690, 55818062, 58206028, 66388970, 69435580, 71453004, 67022372, 64361508, 56831408, 52765668, 44279790, 39837994, 30207030, 22979336, 5941070, 12965877, 40049365, 59726997, 86508077, 89148277, 90982047, 80909469, 70035861, 52311275, 39689245, 18717449, 10208225, 15969970, 29974578, 59403064, 62721850, 74069228, 60572442, 48774796, 175646788, 157314066, 133404066, 133959878, 119960828, 122432428, 89141414, 38546214, 57064047, 698028152]

private def rowData119 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 117184288, 115256880, 120466364, 123443758, 121303188, 110792188, 107657898, 101981970, 84466740, 84600338, 87615624, 81956070, 75158746, 64701528, 63247538, 58564786, 60907302, 62016956, 69327500, 72773772, 75694218, 72391168, 70723972, 64263944, 61134076, 53782346, 50502494, 42392454, 36893968, 21839114, 4527944, 21595973, 40490675, 67016463, 80029411, 85545299, 79728961, 72568791, 57263857, 47483971, 26983819, 18206521, 7374826, 19240996, 49378708, 53930202, 70551744, 61310422, 57369202, 31146374, 9266462, 137976420, 141908776, 136356210, 152065656, 141300954, 106290458, 8200164, 38025261, 553749228]

private def rowData120 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 117184288, 115256880, 120466364, 123443758, 121303188, 110792188, 107657898, 101981970, 84466740, 84600338, 87615624, 81956070, 75158746, 64701528, 63247538, 58564786, 60907302, 62016956, 69327500, 72773772, 75694218, 72391168, 70723972, 64263944, 61134076, 53782346, 50502494, 42392454, 36893968, 21839114, 4527944, 21595973, 40490675, 67016463, 80029411, 85545299, 79728961, 72568791, 57263857, 47483971, 26983819, 18206521, 7374826, 19240996, 49378708, 53930202, 70551744, 61310422, 57369202, 31146374, 9266462, 32637233, 73309865, 47883776, 48079848, 49869784, 64067916, 65410012, 88012818, 90899242, 319975656]

private def rowData121 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 117210100, 122507868, 126070124, 124110796, 114388610, 111129030, 107617414, 88778840, 88451260, 91644870, 87412416, 81925414, 72489930, 71145666, 65912220, 66549722, 66242116, 72585438, 76474810, 80396436, 78343534, 77778012, 72504368, 70412096, 64317792, 62326182, 55902388, 52321064, 39465212, 23923278, 1136767, 19163441, 45406185, 69919357, 79517597, 78420135, 75377039, 62754767, 56125955, 36148713, 27074201, 2154573, 7340714, 38264742, 44182938, 66651924, 62128618, 66897786, 47262674, 35376746, 9354, 30344639, 81466291, 134790519, 15788643, 19055570, 73403994, 142665584, 191355642, 118747378, 384531386]

private def rowData122 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 117210100, 122507868, 126070124, 124110796, 114388610, 111129030, 107617414, 88778840, 88451260, 91644870, 87412416, 81925414, 72489930, 71145666, 65912220, 66549722, 66242116, 72585438, 76474810, 80396436, 78343534, 77778012, 72504368, 70412096, 64317792, 62326182, 55902388, 52321064, 39465212, 23923278, 1136767, 19163441, 45406185, 69919357, 79517597, 78420135, 75377039, 62754767, 56125955, 36148713, 27074201, 2154573, 7340714, 38264742, 44182938, 66651924, 62128618, 66897786, 47262674, 35376746, 9354, 30344639, 81466291, 134790519, 205493995, 213815475, 49591078, 177804624, 287227484, 162908134, 201648229, 439564586]

private def rowData123 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 124067476, 128165142, 126384406, 117457250, 113977046, 112480420, 93061646, 92071932, 95173792, 92115976, 88102794, 79929736, 78943360, 73397196, 72450508, 70709442, 75983284, 79527232, 84378164, 83535952, 84036522, 79935854, 78843948, 73997444, 73262700, 68519798, 66828386, 56215692, 42534928, 18734746, 1716654, 24017893, 49602685, 72207995, 75942561, 77165183, 67448403, 64117709, 44991897, 35704285, 11676587, 4625351, 26615084, 33771676, 61813226, 62097518, 75614676, 62910998, 61306564, 34166994, 14981008, 29989889, 72085629, 143432941, 171639269, 151515407, 106387615, 209630882, 305172634, 20736527, 256570169, 510578066]

private def rowData124 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 124067476, 128165142, 126384406, 117457250, 113977046, 112480420, 93061646, 92071932, 95173792, 92115976, 88102794, 79929736, 78943360, 73397196, 72450508, 70709442, 75983284, 79527232, 84378164, 83535952, 84036522, 79935854, 78843948, 73997444, 73262700, 68519798, 66828386, 56215692, 42534928, 18734746, 1716654, 24017893, 49602685, 72207995, 75942561, 77165183, 67448403, 64117709, 44991897, 35704285, 11676587, 4625351, 26615084, 33771676, 61813226, 62097518, 75614676, 62910998, 61306564, 34166994, 14981008, 29989889, 72085629, 143432941, 171639269, 151515407, 106387615, 79308571, 112782981, 252118516, 212303950, 107279168, 604043274]

private def rowData125 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 130515654, 128935288, 120900116, 117172384, 117936478, 97866746, 96134150, 99133074, 97393144, 95033516, 88276840, 87691996, 81794978, 79070906, 75721566, 79795504, 82951904, 88845472, 89361596, 91058266, 88273622, 88304080, 84857548, 85532944, 82675926, 83104902, 75008926, 63416302, 41029628, 25143116, 21259, 26808357, 64006973, 73162841, 79171393, 72714439, 73084073, 54913525, 45386823, 22359829, 18050699, 13544726, 22090740, 56384440, 62062624, 85394608, 80467662, 90398572, 72490218, 65834200, 27764154, 1733763, 73803429, 124319597, 161142723, 150408613, 150694747, 77372379, 73640755, 151982009, 54832067, 10992439, 653235994]

private def rowData126 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 130515654, 128935288, 120900116, 117172384, 117936478, 97866746, 96134150, 99133074, 97393144, 95033516, 88276840, 87691996, 81794978, 79070906, 75721566, 79795504, 82951904, 88845472, 89361596, 91058266, 88273622, 88304080, 84857548, 85532944, 82675926, 83104902, 75008926, 63416302, 41029628, 25143116, 21259, 26808357, 64006973, 73162841, 79171393, 72714439, 73084073, 54913525, 45386823, 22359829, 18050699, 13544726, 22090740, 56384440, 62062624, 85394608, 80467662, 90398572, 72490218, 65834200, 27764154, 1733763, 73803429, 124319597, 161142723, 150408613, 150694747, 77372379, 73640755, 151982009, 368202365, 220218997, 233847171, 714906122]

private def rowData127 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 131167354, 124099050, 120021260, 122998962, 103077974, 100373980, 102973768, 102356078, 101814260, 96849300, 96995090, 91019368, 86557600, 81483578, 84161788, 86785346, 92930072, 94858470, 97800502, 96412300, 97606248, 95646902, 97802440, 96964010, 99645128, 94303626, 85063262, 64415752, 49909274, 25611324, 2177261, 42636001, 68891343, 80181651, 77471985, 81953999, 65193353, 55534853, 33857761, 32544309, 1020645, 8868650, 49524804, 61067100, 94920724, 98695848, 121277530, 113895222, 122699064, 93237030, 78723848, 7451240, 67179275, 167961515, 196494935, 227980681, 34461641, 31369048, 69252846, 206591647, 338757691, 433048041, 727041501, 24738476]


private def data : List (List ℕ) :=
  [rowData0, rowData1, rowData2, rowData3, rowData4, rowData5, rowData6, rowData7,
   rowData8, rowData9, rowData10, rowData11, rowData12, rowData13, rowData14, rowData15,
   rowData16, rowData17, rowData18, rowData19, rowData20, rowData21, rowData22, rowData23,
   rowData24, rowData25, rowData26, rowData27, rowData28, rowData29, rowData30, rowData31,
   rowData32, rowData33, rowData34, rowData35, rowData36, rowData37, rowData38, rowData39,
   rowData40, rowData41, rowData42, rowData43, rowData44, rowData45, rowData46, rowData47,
   rowData48, rowData49, rowData50, rowData51, rowData52, rowData53, rowData54, rowData55,
   rowData56, rowData57, rowData58, rowData59, rowData60, rowData61, rowData62, rowData63,
   rowData64, rowData65, rowData66, rowData67, rowData68, rowData69, rowData70, rowData71,
   rowData72, rowData73, rowData74, rowData75, rowData76, rowData77, rowData78, rowData79,
   rowData80, rowData81, rowData82, rowData83, rowData84, rowData85, rowData86, rowData87,
   rowData88, rowData89, rowData90, rowData91, rowData92, rowData93, rowData94, rowData95,
   rowData96, rowData97, rowData98, rowData99, rowData100, rowData101, rowData102, rowData103,
   rowData104, rowData105, rowData106, rowData107, rowData108, rowData109, rowData110, rowData111,
   rowData112, rowData113, rowData114, rowData115, rowData116, rowData117, rowData118, rowData119,
   rowData120, rowData121, rowData122, rowData123, rowData124, rowData125, rowData126, rowData127]

private def compressedRow (i : ℕ) : List ℤ :=
  (data[i]?.getD []).map fun v =>
    if v % 2 = 0 then Int.ofNat (v/2) else Int.negSucc (v/2)

private def row (i : ℕ) : List ℤ :=
  (compressedRow i ++ List.replicate 128 0).take 128

private def gram (i j : ℕ) : ℤ :=
  ((row i).zipWith (· * ·) (row j)).sum

private def error (i j : ℕ) : ℤ :=
  10000000000000000 * entry i j - gram i j

private def checkRow (i : ℕ) : Bool :=
  decide (128 * 1000000000 ≤ error i i) &&
    (List.range i).all (fun j => decide (|error i j| ≤ 1000000000))



private theorem use_chunk {start i : ℕ} (hc : (List.range' start 4).all checkRow = true)
    (hi : start ≤ i ∧ i < start+4) : checkRow i = true :=
  List.all_eq_true.1 hc i (List.mem_range'_1.2 hi)



set_option maxHeartbeats 110000000 in
set_option maxRecDepth 24000 in
private theorem check_at (i : ℕ) (hi : i < 128) : checkRow i = true := by
  have check_0 : ((List.range' 0 4).all checkRow) = true := by
    decide +kernel
  have check_4 : ((List.range' 4 4).all checkRow) = true := by
    decide +kernel
  have check_8 : ((List.range' 8 4).all checkRow) = true := by
    decide +kernel
  have check_12 : ((List.range' 12 4).all checkRow) = true := by
    decide +kernel
  have check_16 : ((List.range' 16 4).all checkRow) = true := by
    decide +kernel
  have check_20 : ((List.range' 20 4).all checkRow) = true := by
    decide +kernel
  have check_24 : ((List.range' 24 4).all checkRow) = true := by
    decide +kernel
  have check_28 : ((List.range' 28 4).all checkRow) = true := by
    decide +kernel
  have check_32 : ((List.range' 32 4).all checkRow) = true := by
    decide +kernel
  have check_36 : ((List.range' 36 4).all checkRow) = true := by
    decide +kernel
  have check_40 : ((List.range' 40 4).all checkRow) = true := by
    decide +kernel
  have check_44 : ((List.range' 44 4).all checkRow) = true := by
    decide +kernel
  have check_48 : ((List.range' 48 4).all checkRow) = true := by
    decide +kernel
  have check_52 : ((List.range' 52 4).all checkRow) = true := by
    decide +kernel
  have check_56 : ((List.range' 56 4).all checkRow) = true := by
    decide +kernel
  have check_60 : ((List.range' 60 4).all checkRow) = true := by
    decide +kernel
  have check_64 : ((List.range' 64 4).all checkRow) = true := by
    decide +kernel
  have check_68 : ((List.range' 68 4).all checkRow) = true := by
    decide +kernel
  have check_72 : ((List.range' 72 4).all checkRow) = true := by
    decide +kernel
  have check_76 : ((List.range' 76 4).all checkRow) = true := by
    decide +kernel
  have check_80 : ((List.range' 80 4).all checkRow) = true := by
    decide +kernel
  have check_84 : ((List.range' 84 4).all checkRow) = true := by
    decide +kernel
  have check_88 : ((List.range' 88 4).all checkRow) = true := by
    decide +kernel
  have check_92 : ((List.range' 92 4).all checkRow) = true := by
    decide +kernel
  have check_96 : ((List.range' 96 4).all checkRow) = true := by
    decide +kernel
  have check_100 : ((List.range' 100 4).all checkRow) = true := by
    decide +kernel
  have check_104 : ((List.range' 104 4).all checkRow) = true := by
    decide +kernel
  have check_108 : ((List.range' 108 4).all checkRow) = true := by
    decide +kernel
  have check_112 : ((List.range' 112 4).all checkRow) = true := by
    decide +kernel
  have check_116 : ((List.range' 116 4).all checkRow) = true := by
    decide +kernel
  have check_120 : ((List.range' 120 4).all checkRow) = true := by
    decide +kernel
  have check_124 : ((List.range' 124 4).all checkRow) = true := by
    decide +kernel
  have hq : i / 4 < 32 := by omega
  interval_cases h : i / 4
  · exact use_chunk check_0 (by omega)
  · exact use_chunk check_4 (by omega)
  · exact use_chunk check_8 (by omega)
  · exact use_chunk check_12 (by omega)
  · exact use_chunk check_16 (by omega)
  · exact use_chunk check_20 (by omega)
  · exact use_chunk check_24 (by omega)
  · exact use_chunk check_28 (by omega)
  · exact use_chunk check_32 (by omega)
  · exact use_chunk check_36 (by omega)
  · exact use_chunk check_40 (by omega)
  · exact use_chunk check_44 (by omega)
  · exact use_chunk check_48 (by omega)
  · exact use_chunk check_52 (by omega)
  · exact use_chunk check_56 (by omega)
  · exact use_chunk check_60 (by omega)
  · exact use_chunk check_64 (by omega)
  · exact use_chunk check_68 (by omega)
  · exact use_chunk check_72 (by omega)
  · exact use_chunk check_76 (by omega)
  · exact use_chunk check_80 (by omega)
  · exact use_chunk check_84 (by omega)
  · exact use_chunk check_88 (by omega)
  · exact use_chunk check_92 (by omega)
  · exact use_chunk check_96 (by omega)
  · exact use_chunk check_100 (by omega)
  · exact use_chunk check_104 (by omega)
  · exact use_chunk check_108 (by omega)
  · exact use_chunk check_112 (by omega)
  · exact use_chunk check_116 (by omega)
  · exact use_chunk check_120 (by omega)
  · exact use_chunk check_124 (by omega)

private theorem row_length (i : ℕ) : (row i).length = 128 := by
  simp [row]

private def factor (i k : Fin 128) : ℤ := (row i.val)[k.val]?.getD 0

set_option maxRecDepth 3200 in
private theorem gram_eq (i j : Fin 128) :
    gram i.val j.val = ∑ k : Fin 128, factor i k * factor j k := by
  unfold gram
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_zipWith, row_length, min_self, List.length_ofFn]
  · intro k h₁ h₂
    rw [List.getElem_zipWith, List.getElem_ofFn]
    have hk : k < 128 := by simpa only [List.length_ofFn] using h₂
    have hi' : k < (row i.val).length := by rwa [row_length]
    have hj' : k < (row j.val).length := by rwa [row_length]
    rw [factor, factor, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj']
    rfl

private theorem error_comm (i j : Fin 128) : error i.val j.val = error j.val i.val := by
  unfold error
  rw [gram_eq i j, gram_eq j i]
  have hg : ∑ k : Fin 128, factor i k * factor j k = ∑ k : Fin 128, factor j k * factor i k :=
    sum_congr rfl (fun _ _ => mul_comm ..)
  rw [hg]
  by_cases h : i.val = j.val
  · simp only [h]
  · unfold entry
    simp only [if_neg h, if_neg (Ne.symm h), add_zero]
    rw [add_comm ((directed i.val j.val).toNat : ℤ)]

private theorem diagonal_bound (i : Fin 128) :
    128 * (1000000000 : ℤ) ≤ error i.val i.val := by
  have h := check_at i.val i.isLt
  simp only [checkRow, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

private theorem off_diagonal_bound (i j : Fin 128) (hij : i ≠ j) :
    |error i.val j.val| ≤ (1000000000 : ℤ) := by
  have lower (a b : Fin 128) (hb : b.val < a.val) : |error a.val b.val| ≤ (1000000000 : ℤ) := by
    have h := check_at a.val a.isLt
    simp only [checkRow, Bool.and_eq_true] at h
    exact of_decide_eq_true (List.all_eq_true.1 h.2 b.val (List.mem_range.2 hb))
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [error_comm i j]
    exact lower j i h
  · exact (hij (Fin.ext h)).elim
  · exact lower i j h

private def correctionAt (i : Fin 128) : ℤ := correction[i.val]?.getD 0

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 11000 in
private theorem correction_sum : (∑ i : Fin 128, correctionAt i) = 5456 := by
  decide +kernel

private theorem correction_nonneg (i : Fin 128) : 0 ≤ correctionAt i := by
  exact Int.natCast_nonneg _

private theorem gram_certificate (x : Fin 128 → ℝ) :
    0 ≤ ∑ i, ∑ j, (entry i.val j.val : ℝ) * x i*x j := by
  apply OMA.PRSGram.nonnegative (g := fun i j => (factor i j : ℝ))
    (R := fun i j => (error i.val j.val : ℝ)) (S := 10000000000000000) (B := 1000000000)
  · norm_num
  · norm_num
  · intro i
    exact_mod_cast diagonal_bound i
  · intro i j hij
    exact_mod_cast off_diagonal_bound i j hij
  · intro i j
    have h := sub_add_cancel (10000000000000000 * entry i.val j.val) (gram i.val j.val)
    rw [add_comm, ← error, gram_eq i j] at h
    exact_mod_cast h.symm

private theorem entry_eq (i j : Fin 128) :
    (entry i.val j.val : ℝ) =
    4 * ((if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then (1 : ℝ) else 0) +
        (if i.val ≤ 2*j.val ∧ 2*j.val < i.val+128 then 1 else 0)) +
      (if i = j then (correctionAt i : ℝ) else 0) := by
  have hd (a b : ℕ) : (directed a b).toNat =
      if b ≤ 2*a ∧ 2*a < b+128 then 1 else 0 := by
    unfold directed
    by_cases hb : b ≤ 2*a ∧ 2*a < b+128
    · rw [decide_eq_true hb, if_pos hb]
      rfl
    · rw [decide_eq_false hb, if_neg hb]
      rfl
  unfold entry correctionAt
  rw [hd i.val j.val, hd j.val i.val]
  push_cast
  by_cases h : i = j
  · subst j
    simp only [if_true]
  · have hv : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [if_neg hv, if_neg h]

private theorem expanded (x : Fin 128 → ℝ) :
    (∑ i, ∑ j, (entry i.val j.val : ℝ) * x i*x j) =
    8*(∑ i, ∑ j, if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then x i*x j else 0) +
      ∑ i, (correctionAt i : ℝ)*x i^2 := by
  have hentry (i j : Fin 128) :
      (entry i.val j.val : ℝ)*x i*x j =
        4*((if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then x i*x j else 0) +
          (if i.val ≤ 2*j.val ∧ 2*j.val < i.val+128 then x j*x i else 0)) +
        (if i = j then (correctionAt i : ℝ)*x i^2 else 0) := by
    rw [entry_eq]
    by_cases hij : i = j
    · subst j
      simp only [if_true]
      split_ifs <;> ring
    · simp only [if_neg hij]
      split_ifs <;> ring
  simp_rw [hentry, sum_add_distrib, ← mul_sum]
  have hs : (∑ i : Fin 128, ∑ j : Fin 128,
      if i.val ≤ 2*j.val ∧ 2*j.val < i.val+128 then x j*x i else 0) =
      ∑ i : Fin 128, ∑ j : Fin 128,
      if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then x i*x j else 0 := sum_comm
  simp only [sum_add_distrib, hs]
  simp only [Fintype.sum_ite_eq]
  ring

theorem vector_bound (Q : ℝ) (x : Fin 128 → ℝ) (_hQ : 0 ≤ Q) (hx : ∀ i, |x i| ≤ Q) :
    -682*Q^2 ≤ ∑ i, ∑ j,
      if j.val ≤ 2*i.val ∧ 2*i.val < j.val+128 then x i*x j else 0 := by
  have h := gram_certificate x
  rw [expanded] at h
  have hterm (i : Fin 128) : (correctionAt i : ℝ)*x i^2 ≤ (correctionAt i : ℝ)*Q^2 := by
    have hi := abs_le.1 (hx i)
    have hs : x i^2 ≤ Q^2 := by
      nlinarith only [mul_nonneg (sub_nonneg.2 hi.2) (by linarith only [hi.1] : 0 ≤ Q+x i)]
    exact mul_le_mul_of_nonneg_left hs (by exact_mod_cast correction_nonneg i)
  have hsum : (∑ i : Fin 128, (correctionAt i : ℝ)) = 5456 := by exact_mod_cast correction_sum
  have hu : (∑ i : Fin 128, (correctionAt i : ℝ)*x i^2) ≤ 5456*Q^2 := by
    rw [← hsum, sum_mul]
    exact sum_le_sum (fun i _ => hterm i)
  linarith only [h,hu]

end OMA.PRSGramData

theorem OMA.solution : OMA.R_Erdos1186_erdos_1186_variants_prs_bounds_R1.H2 :=
  OMA.PRSBoxBound.all_sizes OMA.PRSBoxGeometry.box_geometry OMA.PRSGramData.vector_bound
