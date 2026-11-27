import FormalConjectures.ErdosProblems.«1110»
import Mathlib

/-!
Port of the public Lean proof in Apiros3/erdos1110, used under Apache-2.0.
Source: https://github.com/Apiros3/erdos1110/tree/6d66854a3d940490c25a802b9aed54fe896ec8ec
The proof establishes the Yu–Chen range and treats (5,2), (9,2), and (5,3)
by constructing infinite pairwise-coprime sequences of nonrepresentable integers.
The coordinate antichains are related to finite antichains of term values in
ValuePredicateBridge. Adapted by @marcusbuffett for the pinned statement.
-/

-- ===== source module Apiros1110.Basic =====

section

/-
# Basic definitions and antichain lemmas
-/

namespace Apiros1110

abbrev Point := Nat × Nat

def Term (p q : Nat) (x : Point) : Nat :=
  p ^ x.1 * q ^ x.2

def CoordLe (x y : Point) : Prop :=
  x.1 ≤ y.1 ∧ x.2 ≤ y.2

def IsAntichain (A : List Point) : Prop :=
  A.Nodup ∧ ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → x ≠ y → ¬ CoordLe x y

def SumTerms (p q : Nat) (A : List Point) : Nat :=
  (A.map (Term p q)).sum

def Representable (p q n : Nat) : Prop :=
  ∃ A : List Point, IsAntichain A ∧ SumTerms p q A = n

def Nonrepresentable (p q n : Nat) : Prop :=
  ¬ Representable p q n

def PairwiseCoprimeOn (P : Nat → Prop) : Prop :=
  ∀ F : List Nat, ∃ n : Nat, 0 < n ∧ P n ∧ ∀ m, m ∈ F → Nat.Coprime n m

def PairwiseCoprimeNonrepSeq (p q : Nat) (f : Nat → Nat) : Prop :=
  (∀ n, 1 < f n ∧ Nonrepresentable p q (f n) ∧ Nat.Coprime (f n) (p * q)) ∧
  (∀ ⦃m n⦄, m ≠ n → Nat.Coprime (f m) (f n))

def Apiros1110Conclusion (p q : Nat) : Prop :=
  ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq p q f

theorem mem_term_le_sum
    {p q : Nat} {x : Point} :
    ∀ {A : List Point}, x ∈ A → Term p q x ≤ SumTerms p q A
  | [], hx => nomatch hx
  | y :: ys, hx => by
      rw [List.mem_cons] at hx
      cases hx with
      | inl hxy =>
          subst x
          simp [SumTerms]
      | inr hxys =>
          have ih : Term p q x ≤ SumTerms p q ys := mem_term_le_sum hxys
          dsimp [SumTerms] at ih ⊢
          simp
          exact Nat.le_trans ih (Nat.le_add_left _ _)

theorem antichain_not_coordLe
    {A : List Point} (hA : IsAntichain A)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A) (hne : x ≠ y) :
    ¬ CoordLe x y :=
  hA.2 hx hy hne

theorem antichain_incomparable
    {A : List Point} (hA : IsAntichain A)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A) (hne : x ≠ y) :
    ¬ CoordLe x y ∧ ¬ CoordLe y x :=
  ⟨hA.2 hx hy hne, hA.2 hy hx (fun hyx => hne hyx.symm)⟩

theorem antichain_same_first_eq
    {A : List Point} (hA : IsAntichain A)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A)
    (hfirst : x.1 = y.1) :
    x = y := by
  by_cases hxy : x = y
  · exact hxy
  have hle_or : x.2 ≤ y.2 ∨ y.2 ≤ x.2 := Nat.le_total x.2 y.2
  cases hle_or with
  | inl hxy2 =>
      have hcoord : CoordLe x y := by
        constructor
        · rw [hfirst]
        · exact hxy2
      exact False.elim ((hA.2 hx hy hxy) hcoord)
  | inr hyx2 =>
      have hcoord : CoordLe y x := by
        constructor
        · rw [hfirst]
        · exact hyx2
      exact False.elim ((hA.2 hy hx (fun hyx => hxy hyx.symm)) hcoord)

theorem antichain_same_second_eq
    {A : List Point} (hA : IsAntichain A)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A)
    (hsecond : x.2 = y.2) :
    x = y := by
  by_cases hxy : x = y
  · exact hxy
  have hle_or : x.1 ≤ y.1 ∨ y.1 ≤ x.1 := Nat.le_total x.1 y.1
  cases hle_or with
  | inl hxy1 =>
      have hcoord : CoordLe x y := by
        constructor
        · exact hxy1
        · rw [hsecond]
      exact False.elim ((hA.2 hx hy hxy) hcoord)
  | inr hyx1 =>
      have hcoord : CoordLe y x := by
        constructor
        · exact hyx1
        · rw [hsecond]
      exact False.elim ((hA.2 hy hx (fun hyx => hxy hyx.symm)) hcoord)

theorem antichain_second_strictAnti_of_first_lt
    {A : List Point} (hA : IsAntichain A)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A)
    (hfirst : x.1 < y.1) :
    y.2 < x.2 := by
  have hxy_ne : x ≠ y := by
    intro hxy
    rw [hxy] at hfirst
    exact (Nat.lt_irrefl y.1) hfirst
  exact Nat.lt_of_not_le fun hxy2 =>
    hA.2 hx hy hxy_ne ⟨Nat.le_of_lt hfirst, hxy2⟩

theorem antichain_first_strictAnti_of_second_lt
    {A : List Point} (hA : IsAntichain A)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A)
    (hsecond : x.2 < y.2) :
    y.1 < x.1 := by
  have hxy_ne : x ≠ y := by
    intro hxy
    rw [hxy] at hsecond
    exact (Nat.lt_irrefl y.2) hsecond
  exact Nat.lt_of_not_le fun hxy1 =>
    hA.2 hx hy hxy_ne ⟨hxy1, Nat.le_of_lt hsecond⟩

theorem coordLe_term_dvd
    {p q : Nat} {x y : Point}
    (hxy : CoordLe x y) :
    Term p q x ∣ Term p q y := by
  exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p hxy.1) (Nat.pow_dvd_pow q hxy.2)

theorem pow_mul_pow_dvd_first_le
    {r s i j i' j' : Nat}
    (hr : 1 < r) (hrs : Nat.Coprime r s)
    (hdiv : r ^ i * s ^ j ∣ r ^ i' * s ^ j') :
    i ≤ i' := by
  by_cases hle : i ≤ i'
  · exact hle
  have hi'i : i' < i := Nat.lt_of_not_ge hle
  let d := i - i'
  have hdpos : 0 < d := Nat.sub_pos_of_lt hi'i
  have hr_pos : 0 < r := Nat.lt_trans Nat.zero_lt_one hr
  have hi'_le_i : i' ≤ i := Nat.le_of_lt hi'i
  have hsplit : r ^ i = r ^ i' * r ^ d := by
    have hadd : i' + d = i := Nat.add_sub_of_le hi'_le_i
    rw [← hadd, Nat.pow_add]
  have hri_dvd_target : r ^ i ∣ r ^ i' * s ^ j' :=
    Nat.dvd_trans (Nat.dvd_mul_right _ _) hdiv
  have hcancel : r ^ d ∣ s ^ j' := by
    have hri'_pos : 0 < r ^ i' := (Nat.pow_pos hr_pos : 0 < r ^ i')
    exact (Nat.mul_dvd_mul_iff_left hri'_pos).mp (by
      simpa [hsplit] using hri_dvd_target)
  have hcop : Nat.Coprime (r ^ d) (s ^ j') :=
    (hrs.pow_left d).pow_right j'
  have hgcd_left : Nat.gcd (r ^ d) (s ^ j') = r ^ d :=
    Nat.gcd_eq_left hcancel
  have hgcd_one : Nat.gcd (r ^ d) (s ^ j') = 1 :=
    Nat.Coprime.gcd_eq_one hcop
  have hrd_eq_one : r ^ d = 1 := hgcd_left.symm.trans hgcd_one
  have hone_lt : 1 < r ^ d := Nat.one_lt_pow (Nat.ne_of_gt hdpos) hr
  rw [hrd_eq_one] at hone_lt
  exact False.elim ((Nat.lt_irrefl 1) hone_lt)

theorem term_dvd_coordLe
    {p q : Nat} {x y : Point}
    (hp : 1 < p) (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hdiv : Term p q x ∣ Term p q y) :
    CoordLe x y := by
  constructor
  · exact pow_mul_pow_dvd_first_le hp hpq (by simpa [Term] using hdiv)
  · have hdiv' : q ^ x.2 * p ^ x.1 ∣ q ^ y.2 * p ^ y.1 := by
      simpa [Term, Nat.mul_comm] using hdiv
    exact pow_mul_pow_dvd_first_le hq hpq.symm hdiv'

theorem term_dvd_iff_coordLe
    {p q : Nat} {x y : Point}
    (hp : 1 < p) (hq : 1 < q) (hpq : Nat.Coprime p q) :
    Term p q x ∣ Term p q y ↔ CoordLe x y :=
  ⟨term_dvd_coordLe hp hq hpq, coordLe_term_dvd⟩

theorem antichain_filter
    {A : List Point} (hA : IsAntichain A) (P : Point → Bool) :
    IsAntichain (A.filter P) := by
  constructor
  · exact List.pairwise_filter.mpr
      (hA.1.imp (fun hxy _ _ => hxy))
  · intro x hx y hy hne hcoord
    have hxA : x ∈ A := (List.mem_filter.mp hx).1
    have hyA : y ∈ A := (List.mem_filter.mp hy).1
    exact hA.2 hxA hyA hne hcoord

theorem filter_eq_nil_of_forall_not (P : Point → Bool) :
    ∀ A : List Point, (∀ x, x ∈ A → ¬ P x = true) → A.filter P = []
  | [], _ => rfl
  | z :: zs, hnot => by
      have hz : ¬ P z = true := hnot z List.mem_cons_self
      have hzs : zs.filter P = [] := filter_eq_nil_of_forall_not P zs (by
        intro y hy
        exact hnot y (List.mem_cons_of_mem z hy))
      rw [List.filter_cons_of_neg hz, hzs]

theorem filter_eq_singleton_of_unique (P : Point → Bool) :
    ∀ {A : List Point} {w : Point},
      A.Nodup → w ∈ A → P w = true →
      (∀ y, y ∈ A → P y = true → y = w) →
      A.filter P = [w]
  | [], _, _, hw, _, _ => by
      exact False.elim (List.not_mem_nil hw)
  | z :: zs, w, hnodup, hw, hPw, huniq => by
      have hz_not_tail : ¬ z ∈ zs := (List.nodup_cons.mp hnodup).1
      have hzs_nodup : zs.Nodup := (List.nodup_cons.mp hnodup).2
      by_cases hzP : P z = true
      · have hzw : z = w := huniq z List.mem_cons_self hzP
        subst w
        have hfilter_tail : zs.filter P = [] := by
          apply filter_eq_nil_of_forall_not
          intro y hy hyP
          have hyz : y = z := huniq y (List.mem_cons_of_mem z hy) hyP
          subst y
          exact hz_not_tail hy
        rw [List.filter_cons_of_pos hzP, hfilter_tail]
      · have hw_tail : w ∈ zs := by
          cases List.mem_cons.mp hw with
          | inl hwz =>
              subst w
              exact False.elim (hzP hPw)
          | inr hwt => exact hwt
        have huniq_tail : ∀ y, y ∈ zs → P y = true → y = w := by
          intro y hy hyP
          exact huniq y (List.mem_cons_of_mem z hy) hyP
        rw [List.filter_cons_of_neg hzP]
        exact filter_eq_singleton_of_unique P hzs_nodup hw_tail hPw huniq_tail

theorem list_eq_nil_of_forall_not_mem :
    ∀ A : List Point, (∀ x, x ∈ A → False) → A = []
  | [], _ => rfl
  | z :: _, h => by
      exact False.elim (h z List.mem_cons_self)

theorem list_eq_singleton_of_mem_unique
    {A : List Point} {w : Point}
    (hnodup : A.Nodup)
    (hw : w ∈ A)
    (huniq : ∀ y, y ∈ A → y = w) :
    A = [w] := by
  cases A with
  | nil =>
      exact False.elim (List.not_mem_nil hw)
  | cons z zs =>
      have hz_not : ¬ z ∈ zs := (List.nodup_cons.mp hnodup).1
      have hzw : z = w := huniq z List.mem_cons_self
      subst z
      have hzs_nil : zs = [] := by
        apply list_eq_nil_of_forall_not_mem
        intro y hy
        have hyw : y = w := huniq y (List.mem_cons_of_mem w hy)
        subst y
        exact hz_not hy
      rw [hzs_nil]

end Apiros1110

end

-- ===== source module Apiros1110.LowRows =====

section

/-
# Low-row infrastructure
-/

namespace Apiros1110

def highRows (M : Nat) (A : List Point) : List Point :=
  A.filter (fun x => decide (M ≤ x.2))

def lowRows (M : Nat) (A : List Point) : List Point :=
  A.filter (fun x => decide (x.2 < M))

def shiftSecondDown (M : Nat) (x : Point) : Point :=
  (x.1, x.2 - M)

def shiftedHighRows (M : Nat) (A : List Point) : List Point :=
  (highRows M A).map (shiftSecondDown M)

theorem mem_highRows_le
    {M : Nat} {A : List Point} {x : Point}
    (hx : x ∈ highRows M A) :
    M ≤ x.2 :=
  of_decide_eq_true (List.mem_filter.mp hx).2

theorem mem_lowRows_lt
    {M : Nat} {A : List Point} {x : Point}
    (hx : x ∈ lowRows M A) :
    x.2 < M :=
  of_decide_eq_true (List.mem_filter.mp hx).2

theorem lowRows_one_eq_singleton_of_unique_second_zero
    {A : List Point} {x : Point}
    (hnodup : A.Nodup)
    (hx : x ∈ A)
    (hx0 : x.2 = 0)
    (huniq : ∀ y, y ∈ A → y.2 = 0 → y = x) :
    lowRows 1 A = [x] := by
  dsimp [lowRows]
  apply filter_eq_singleton_of_unique
  · exact hnodup
  · exact hx
  · exact decide_eq_true (by rw [hx0]; decide : x.2 < 1)
  · intro y hy hyP
    have hylt : y.2 < 1 := of_decide_eq_true hyP
    exact huniq y hy (Nat.lt_one_iff.mp hylt)

theorem lowRows_antichain
    {A : List Point} (hA : IsAntichain A) (M : Nat) :
    IsAntichain (lowRows M A) :=
  antichain_filter hA (fun x => decide (x.2 < M))

theorem highRows_antichain
    {A : List Point} (hA : IsAntichain A) (M : Nat) :
    IsAntichain (highRows M A) :=
  antichain_filter hA (fun x => decide (M ≤ x.2))

theorem shiftSecondDown_injective_on_high
    {M : Nat} {x y : Point}
    (hx : M ≤ x.2) (hy : M ≤ y.2)
    (h : shiftSecondDown M x = shiftSecondDown M y) :
    x = y := by
  cases x with
  | mk xi xj =>
      cases y with
      | mk yi yj =>
          dsimp [shiftSecondDown] at h hx hy ⊢
          injection h with hfirst hsecond
          subst yi
          have hadd : xj - M + M = yj - M + M := by rw [hsecond]
          rw [Nat.sub_add_cancel hx, Nat.sub_add_cancel hy] at hadd
          rw [hadd]

theorem shiftSecondDown_reflects_coordLe_on_high
    {M : Nat} {x y : Point}
    (hx : M ≤ x.2) (hy : M ≤ y.2)
    (h : CoordLe (shiftSecondDown M x) (shiftSecondDown M y)) :
    CoordLe x y := by
  cases x with
  | mk xi xj =>
      cases y with
      | mk yi yj =>
          dsimp [CoordLe, shiftSecondDown] at hx hy h ⊢
          constructor
          · exact h.1
          · have hadd : xj - M + M ≤ yj - M + M :=
              Nat.add_le_add_right h.2 M
            rw [Nat.sub_add_cancel hx, Nat.sub_add_cancel hy] at hadd
            exact hadd

theorem nodup_map_of_injective_on
    {α β : Type} {f : α → β} {l : List α}
    (hinj : ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y)
    (hnodup : l.Nodup) :
    (l.map f).Nodup := by
  induction l with
  | nil =>
      simp
  | cons a as ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.map, List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨b, hb, hfb⟩
        have hab : a = b :=
          hinj List.mem_cons_self (List.mem_cons_of_mem a hb) hfb.symm
        subst b
        exact hnodup.1 hb
      · apply ih
        · intro x hx y hy hxy
          exact hinj (List.mem_cons_of_mem a hx) (List.mem_cons_of_mem a hy) hxy
        · exact hnodup.2

theorem shiftedHighRows_antichain
    {A : List Point} (hA : IsAntichain A) (M : Nat) :
    IsAntichain (shiftedHighRows M A) := by
  let H := highRows M A
  have hH : IsAntichain H := antichain_filter hA (fun x => decide (M ≤ x.2))
  constructor
  · dsimp [shiftedHighRows]
    apply nodup_map_of_injective_on
    · intro x hx y hy hxy
      exact shiftSecondDown_injective_on_high
        (mem_highRows_le hx) (mem_highRows_le hy) hxy
    · exact hH.1
  · intro u hu v hv huv hcoord
    dsimp [shiftedHighRows] at hu hv
    rcases List.mem_map.mp hu with ⟨x, hxH, hxu⟩
    rcases List.mem_map.mp hv with ⟨y, hyH, hyv⟩
    subst u
    subst v
    have hxy_ne : x ≠ y := by
      intro hxy
      exact huv (by rw [hxy])
    have hxy_coord : CoordLe x y :=
      shiftSecondDown_reflects_coordLe_on_high
        (mem_highRows_le hxH) (mem_highRows_le hyH) hcoord
    exact hH.2 hxH hyH hxy_ne hxy_coord

theorem term_eq_qpow_mul_shifted
    {p q M : Nat} {x : Point}
    (hx : M ≤ x.2) :
    Term p q x = q ^ M * Term p q (shiftSecondDown M x) := by
  cases x with
  | mk i j =>
      dsimp [Term, shiftSecondDown] at hx ⊢
      have hadd : M + (j - M) = j := Nat.add_sub_of_le hx
      calc
        p ^ i * q ^ j = p ^ i * q ^ (M + (j - M)) := by rw [hadd]
        _ = q ^ M * (p ^ i * q ^ (j - M)) := by
          rw [Nat.pow_add]
          ac_rfl

theorem sumTerms_eq_qpow_mul_shifted
    {p q M : Nat} :
    ∀ {A : List Point},
      (∀ x, x ∈ A → M ≤ x.2) →
      SumTerms p q A = q ^ M * SumTerms p q (A.map (shiftSecondDown M))
  | [], _ => by
      simp [SumTerms]
  | x :: xs, hall => by
      have hx : M ≤ x.2 := hall x List.mem_cons_self
      have hxs : ∀ y, y ∈ xs → M ≤ y.2 := by
        intro y hy
        exact hall y (List.mem_cons_of_mem x hy)
      have ih := sumTerms_eq_qpow_mul_shifted (p := p) (q := q) (M := M) hxs
      dsimp [SumTerms] at ih ⊢
      rw [List.map_map] at ih
      simp [List.map_map]
      rw [term_eq_qpow_mul_shifted hx, ih]
      rw [Nat.mul_add]

theorem highRows_sum_factor
    (p q M : Nat) (A : List Point) :
    SumTerms p q (highRows M A) =
      q ^ M * SumTerms p q (shiftedHighRows M A) := by
  exact sumTerms_eq_qpow_mul_shifted (p := p) (q := q) (M := M)
    (fun x hx => mem_highRows_le hx)

theorem term_first_zeroSecond
    (p q a : Nat) :
    Term p q (a, 0) = p ^ a := by
  simp [Term]

theorem sumTerms_lowRows_add_highRows
    (p q M : Nat) :
    ∀ A : List Point,
      SumTerms p q A = SumTerms p q (lowRows M A) + SumTerms p q (highRows M A)
  | [] => by
      simp [SumTerms, lowRows, highRows]
  | x :: xs => by
      have ih := sumTerms_lowRows_add_highRows p q M xs
      dsimp [SumTerms, lowRows, highRows] at ih
      by_cases hlow : x.2 < M
      · have hnot_high : ¬ M ≤ x.2 := Nat.not_le_of_gt hlow
        simp [SumTerms, lowRows, highRows, hlow, hnot_high]
        rw [ih]
        ac_rfl
      · have hhigh : M ≤ x.2 := Nat.le_of_not_gt hlow
        simp [SumTerms, lowRows, highRows, hlow, hhigh]
        rw [ih]
        ac_rfl

theorem sumTerms_eq_zeroSecond_term_add_highRows_one
    {p q : Nat} {A : List Point} {x : Point}
    (hnodup : A.Nodup)
    (hx : x ∈ A)
    (hx0 : x.2 = 0)
    (huniq : ∀ y, y ∈ A → y.2 = 0 → y = x) :
    SumTerms p q A = Term p q x + SumTerms p q (highRows 1 A) := by
  have hsplit := sumTerms_lowRows_add_highRows p q 1 A
  have hlow : lowRows 1 A = [x] :=
    lowRows_one_eq_singleton_of_unique_second_zero hnodup hx hx0 huniq
  rw [hsplit, hlow]
  simp [SumTerms]

theorem first_coord_le_of_term_lt_pow_succ
    {p q a : Nat} {x : Point}
    (hp : 1 < p) (hq : 0 < q)
    (hterm : Term p q x < p ^ (a + 1)) :
    x.1 ≤ a := by
  by_cases hxle : x.1 ≤ a
  · exact hxle
  have hax : a < x.1 := Nat.lt_of_not_ge hxle
  have hsucc_le : a + 1 ≤ x.1 := Nat.succ_le_of_lt hax
  have hp_pos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hpow_le : p ^ (a + 1) ≤ p ^ x.1 :=
    Nat.pow_le_pow_right hp_pos hsucc_le
  have hqpow_pos : 0 < q ^ x.2 := (Nat.pow_pos hq : 0 < q ^ x.2)
  have hpx_le_term : p ^ x.1 ≤ Term p q x :=
    Nat.le_mul_of_pos_right _ hqpow_pos
  have hbad : p ^ (a + 1) < p ^ (a + 1) :=
    Nat.lt_of_le_of_lt (Nat.le_trans hpow_le hpx_le_term) hterm
  exact False.elim ((Nat.lt_irrefl _) hbad)

theorem embedded_lt_pow_succ
    {p q c a M : Nat}
    (hp_pos : 0 < p)
    (hright : c * q ^ M < (p - 1) * p ^ a) :
    p ^ a + c * q ^ M < p ^ (a + 1) := by
  have h1 : p ^ a + c * q ^ M < p ^ a + (p - 1) * p ^ a :=
    Nat.add_lt_add_left hright (p ^ a)
  have hsum : p ^ a + (p - 1) * p ^ a = p * p ^ a := by
    have hp_eq : p = (p - 1) + 1 := by
      exact (Nat.succ_pred_eq_of_pos hp_pos).symm
    rw [hp_eq]
    simp [Nat.add_mul]
    ac_rfl
  have hpow : p ^ (a + 1) = p * p ^ a := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [hsum, ← hpow] at h1
  exact h1

theorem q_dvd_term_of_second_pos
    {p q : Nat} {x : Point}
    (hpos : 0 < x.2) :
    q ∣ Term p q x := by
  have hq_dvd_qpow : q ∣ q ^ x.2 :=
    by simpa using Nat.pow_dvd_pow q hpos
  exact Nat.dvd_trans hq_dvd_qpow (Nat.dvd_mul_left _ _)

theorem dvd_sumTerms_of_dvd_each
    {p q d : Nat} :
    ∀ {A : List Point},
      (∀ x, x ∈ A → d ∣ Term p q x) →
      d ∣ SumTerms p q A
  | [], _ => by
      simp [SumTerms]
  | x :: xs, hall => by
      have hx : d ∣ Term p q x := hall x List.mem_cons_self
      have hxs : d ∣ SumTerms p q xs := by
        apply dvd_sumTerms_of_dvd_each
        intro y hy
        exact hall y (List.mem_cons_of_mem x hy)
      change d ∣ Term p q x + SumTerms p q xs
      exact Nat.dvd_add hx hxs

theorem q_dvd_sumTerms_of_all_second_pos
    {p q : Nat} {A : List Point}
    (hall : ∀ x, x ∈ A → 0 < x.2) :
    q ∣ SumTerms p q A := by
  apply dvd_sumTerms_of_dvd_each
  intro x hx
  exact q_dvd_term_of_second_pos (hall x hx)

theorem not_dvd_coprime_pow
    {p q a : Nat}
    (hq : 1 < q) (hpq : Nat.Coprime p q) :
    ¬ q ∣ p ^ a := by
  intro hdiv
  have hcop : Nat.Coprime q (p ^ a) :=
    hpq.symm.pow_right a
  have hgcd_left : Nat.gcd q (p ^ a) = q :=
    Nat.gcd_eq_left hdiv
  have hgcd_one : Nat.gcd q (p ^ a) = 1 :=
    Nat.Coprime.gcd_eq_one hcop
  have hq_eq_one : q = 1 := hgcd_left.symm.trans hgcd_one
  rw [hq_eq_one] at hq
  exact (Nat.lt_irrefl 1) hq

theorem q_dvd_qpow_mul_of_pos
    {q M u : Nat}
    (hM : 0 < M) :
    q ∣ q ^ M * u := by
  have hq : q ∣ q ^ M := by
    simpa using Nat.pow_dvd_pow q hM
  exact Nat.dvd_trans hq (Nat.dvd_mul_right _ _)

theorem dvd_pow_of_lowrow_congruence_and_dvd_sum
    {p q a M S u v : Nat}
    (hM : 0 < M)
    (hS : q ∣ S)
    (heq : S + q ^ M * u = p ^ a + q ^ M * v) :
    q ∣ p ^ a := by
  have hqu : q ∣ q ^ M * u := q_dvd_qpow_mul_of_pos hM
  have hqv : q ∣ q ^ M * v := q_dvd_qpow_mul_of_pos hM
  have hleft : q ∣ S + q ^ M * u := Nat.dvd_add hS hqu
  have hright : q ∣ p ^ a + q ^ M * v := by
    rwa [heq] at hleft
  exact (Nat.dvd_add_left hqv).mp hright

theorem not_all_second_pos_of_lowrow_congruence
    {p q a M : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hM : 0 < M)
    (hall_pos : ∀ x, x ∈ A → 0 < x.2)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    False := by
  rcases hcong with ⟨u, v, heq⟩
  have hS : q ∣ SumTerms p q A :=
    q_dvd_sumTerms_of_all_second_pos hall_pos
  have hdiv : q ∣ p ^ a :=
    dvd_pow_of_lowrow_congruence_and_dvd_sum hM hS heq
  exact not_dvd_coprime_pow hq hpq hdiv

theorem exists_second_zero_of_lowrow_congruence
    {p q a M : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hM : 0 < M)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    ∃ x, x ∈ A ∧ x.2 = 0 := by
  by_cases hzero : ∃ x, x ∈ A ∧ x.2 = 0
  · exact hzero
  · have hall_pos : ∀ x, x ∈ A → 0 < x.2 := by
      intro x hx
      by_cases hx0 : x.2 = 0
      · exact False.elim (hzero ⟨x, hx, hx0⟩)
      · exact Nat.pos_of_ne_zero hx0
    exact False.elim
      (not_all_second_pos_of_lowrow_congruence hq hpq hM hall_pos hcong)

theorem second_zero_unique_of_antichain
    {A : List Point} (hA : IsAntichain A)
    {x y : Point}
    (hx : x ∈ A) (hy : y ∈ A)
    (hx0 : x.2 = 0) (hy0 : y.2 = 0) :
    x = y := by
  apply antichain_same_second_eq hA hx hy
  rw [hx0, hy0]

theorem exists_unique_second_zero_of_lowrow_congruence
    {p q a M : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hM : 0 < M)
    (hA : IsAntichain A)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    ∃ x, x ∈ A ∧ x.2 = 0 ∧
      ∀ y, y ∈ A → y.2 = 0 → y = x := by
  rcases exists_second_zero_of_lowrow_congruence hq hpq hM hcong with
    ⟨x, hx, hx0⟩
  refine ⟨x, hx, hx0, ?_⟩
  intro y hy hy0
  exact second_zero_unique_of_antichain hA hy hx hy0 hx0

theorem exists_min_positive_second :
    ∀ A : List Point,
      (∃ x, x ∈ A ∧ 0 < x.2) →
      ∃ x, x ∈ A ∧ 0 < x.2 ∧
        ∀ y, y ∈ A → 0 < y.2 → x.2 ≤ y.2
  | [], h => by
      rcases h with ⟨x, hx, _⟩
      exact False.elim (List.not_mem_nil hx)
  | z :: zs, h => by
      by_cases hzpos : 0 < z.2
      · by_cases htail : ∃ x, x ∈ zs ∧ 0 < x.2
        · rcases exists_min_positive_second zs htail with ⟨m, hm, hmpos, hmin⟩
          cases Nat.le_total z.2 m.2 with
          | inl hz_le_m =>
              refine ⟨z, List.mem_cons_self, hzpos, ?_⟩
              intro y hy hypos
              cases List.mem_cons.mp hy with
              | inl hyz =>
                  subst y
                  exact Nat.le_refl z.2
              | inr hyzs =>
                  exact Nat.le_trans hz_le_m (hmin y hyzs hypos)
          | inr hm_le_z =>
              refine ⟨m, List.mem_cons_of_mem z hm, hmpos, ?_⟩
              intro y hy hypos
              cases List.mem_cons.mp hy with
              | inl hyz =>
                  subst y
                  exact hm_le_z
              | inr hyzs =>
                  exact hmin y hyzs hypos
        · refine ⟨z, List.mem_cons_self, hzpos, ?_⟩
          intro y hy hypos
          cases List.mem_cons.mp hy with
          | inl hyz =>
              subst y
              exact Nat.le_refl z.2
          | inr hyzs =>
              exact False.elim (htail ⟨y, hyzs, hypos⟩)
      · have htail : ∃ x, x ∈ zs ∧ 0 < x.2 := by
          rcases h with ⟨x, hx, hxpos⟩
          cases List.mem_cons.mp hx with
          | inl hxz =>
              subst x
              exact False.elim (hzpos hxpos)
          | inr hxzs =>
              exact ⟨x, hxzs, hxpos⟩
        rcases exists_min_positive_second zs htail with ⟨m, hm, hmpos, hmin⟩
        refine ⟨m, List.mem_cons_of_mem z hm, hmpos, ?_⟩
        intro y hy hypos
        cases List.mem_cons.mp hy with
        | inl hyz =>
            subst y
            exact False.elim (hzpos hypos)
        | inr hyzs =>
            exact hmin y hyzs hypos

theorem qpow_dvd_term_of_second_ge
    {p q k : Nat} {x : Point}
    (hk : k ≤ x.2) :
    q ^ k ∣ Term p q x := by
  have hq : q ^ k ∣ q ^ x.2 := Nat.pow_dvd_pow q hk
  exact Nat.dvd_trans hq (Nat.dvd_mul_left _ _)

theorem qpow_dvd_sumTerms_of_all_second_ge
    {p q k : Nat} :
    ∀ {A : List Point},
      (∀ x, x ∈ A → k ≤ x.2) →
      q ^ k ∣ SumTerms p q A
  | [], _ => by
      simp [SumTerms]
  | x :: xs, hall => by
      have hx : q ^ k ∣ Term p q x :=
        qpow_dvd_term_of_second_ge (hall x List.mem_cons_self)
      have hxs : q ^ k ∣ SumTerms p q xs := by
        apply qpow_dvd_sumTerms_of_all_second_ge
        intro y hy
        exact hall y (List.mem_cons_of_mem x hy)
      change q ^ k ∣ Term p q x + SumTerms p q xs
      exact Nat.dvd_add hx hxs

theorem exists_qpow_factor_sumTerms_of_all_second_ge
    {p q k : Nat} {A : List Point}
    (hall : ∀ x, x ∈ A → k ≤ x.2) :
    ∃ U, SumTerms p q A = q ^ k * U := by
  rcases qpow_dvd_sumTerms_of_all_second_ge (p := p) (q := q) (k := k) hall with
    ⟨U, hU⟩
  exact ⟨U, hU⟩

theorem sumTerms_factor_at_strict_second_min
    {p q : Nat} :
    ∀ {A : List Point} {x : Point},
      A.Nodup →
      x ∈ A →
      (∀ y, y ∈ A → y ≠ x → x.2 < y.2) →
      ∃ U, SumTerms p q A = q ^ x.2 * (p ^ x.1 + q * U)
  | [], _, _, hx, _ => by
      exact False.elim (List.not_mem_nil hx)
  | z :: zs, x, hnodup, hx, hstrict => by
      have hz_not : ¬ z ∈ zs := (List.nodup_cons.mp hnodup).1
      have hzs_nodup : zs.Nodup := (List.nodup_cons.mp hnodup).2
      cases List.mem_cons.mp hx with
      | inl hxz =>
          subst x
          have htail_ge : ∀ y, y ∈ zs → z.2 + 1 ≤ y.2 := by
            intro y hy
            have hy_ne : y ≠ z := by
              intro hyz
              subst y
              exact hz_not hy
            exact Nat.succ_le_of_lt (hstrict y (List.mem_cons_of_mem z hy) hy_ne)
          rcases exists_qpow_factor_sumTerms_of_all_second_ge
              (p := p) (q := q) (k := z.2 + 1) htail_ge with
            ⟨U, hU⟩
          refine ⟨U, ?_⟩
          change Term p q z + SumTerms p q zs = q ^ z.2 * (p ^ z.1 + q * U)
          rw [hU]
          dsimp [Term]
          rw [Nat.pow_succ]
          simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      | inr hxzs =>
          have hz_ne_x : z ≠ x := by
            intro hzx
            subst x
            exact hz_not hxzs
          have hz_ge : x.2 + 1 ≤ z.2 :=
            Nat.succ_le_of_lt (hstrict z List.mem_cons_self hz_ne_x)
          have hstrict_tail : ∀ y, y ∈ zs → y ≠ x → x.2 < y.2 := by
            intro y hy hyne
            exact hstrict y (List.mem_cons_of_mem z hy) hyne
          rcases sumTerms_factor_at_strict_second_min
              (p := p) (q := q) hzs_nodup hxzs hstrict_tail with
            ⟨U, hU⟩
          rcases qpow_dvd_term_of_second_ge
              (p := p) (q := q) (k := x.2 + 1) (x := z) hz_ge with
            ⟨V, hV⟩
          refine ⟨V + U, ?_⟩
          change Term p q z + SumTerms p q zs =
            q ^ x.2 * (p ^ x.1 + q * (V + U))
          rw [hV, hU]
          rw [Nat.pow_succ]
          simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          ac_rfl

theorem not_q_dvd_p_pow_add_q_mul
    {p q i U : Nat}
    (hq : 1 < q) (hpq : Nat.Coprime p q) :
    ¬ q ∣ p ^ i + q * U := by
  intro hdiv
  have hqU : q ∣ q * U := Nat.dvd_mul_right q U
  have hqpi : q ∣ p ^ i := (Nat.dvd_add_left hqU).mp hdiv
  have hcop : Nat.Coprime q (p ^ i) := hpq.symm.pow_right i
  have hgcd_left : Nat.gcd q (p ^ i) = q := Nat.gcd_eq_left hqpi
  have hgcd_one : Nat.gcd q (p ^ i) = 1 := Nat.Coprime.gcd_eq_one hcop
  have hqeq : q = 1 := hgcd_left.symm.trans hgcd_one
  rw [hqeq] at hq
  exact (Nat.lt_irrefl 1) hq

theorem not_qpow_succ_dvd_sumTerms_at_strict_second_min
    {p q : Nat} {A : List Point} {x : Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hnodup : A.Nodup) (hx : x ∈ A)
    (hstrict : ∀ y, y ∈ A → y ≠ x → x.2 < y.2) :
    ¬ q ^ (x.2 + 1) ∣ SumTerms p q A := by
  rcases sumTerms_factor_at_strict_second_min
      (p := p) (q := q) hnodup hx hstrict with
    ⟨U, hU⟩
  intro hdiv
  rw [hU] at hdiv
  rw [Nat.pow_succ] at hdiv
  have hqpos : 0 < q := Nat.lt_trans Nat.zero_lt_one hq
  have hqjpos : 0 < q ^ x.2 := (Nat.pow_pos hqpos : 0 < q ^ x.2)
  have hq_dvd : q ∣ p ^ x.1 + q * U :=
    (Nat.mul_dvd_mul_iff_left hqjpos).mp hdiv
  exact not_q_dvd_p_pow_add_q_mul hq hpq hq_dvd

theorem false_of_zero_at_a_and_positive_second_of_lowrow_congruence
    {p q a M : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (_hM : 0 < M)
    (hA : IsAntichain A)
    (hrow : ∀ x, x ∈ A → x.2 < M)
    (hzero : (a, 0) ∈ A)
    (huniq_zero : ∀ y, y ∈ A → y.2 = 0 → y = (a, 0))
    (hpos_exists : ∃ x, x ∈ A ∧ 0 < x.2)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    False := by
  let Pos := highRows 1 A
  have hdecomp : SumTerms p q A = p ^ a + SumTerms p q Pos := by
    dsimp [Pos]
    rw [sumTerms_eq_zeroSecond_term_add_highRows_one hA.1 hzero rfl huniq_zero]
    simp [Term]
  have hqM_dvd_pos : q ^ M ∣ SumTerms p q Pos := by
    rcases hcong with ⟨u, v, heq⟩
    have heq' : p ^ a + (SumTerms p q Pos + q ^ M * u) =
        p ^ a + q ^ M * v := by
      rw [← Nat.add_assoc]
      rw [← hdecomp]
      exact heq
    have hcancel : SumTerms p q Pos + q ^ M * u = q ^ M * v :=
      Nat.add_left_cancel heq'
    have hleft : q ^ M ∣ SumTerms p q Pos + q ^ M * u := by
      rw [hcancel]
      exact Nat.dvd_mul_right _ _
    exact (Nat.dvd_add_left (Nat.dvd_mul_right _ _)).mp hleft
  have hpos_mem : ∃ x, x ∈ Pos ∧ 0 < x.2 := by
    rcases hpos_exists with ⟨x, hxA, hxpos⟩
    refine ⟨x, ?_, hxpos⟩
    dsimp [Pos, highRows]
    rw [List.mem_filter]
    exact ⟨hxA, decide_eq_true (Nat.succ_le_of_lt hxpos)⟩
  rcases exists_min_positive_second Pos hpos_mem with ⟨m, hmPos, hmpos, hmin⟩
  have hmA : m ∈ A := (List.mem_filter.mp hmPos).1
  have hstrict : ∀ y, y ∈ Pos → y ≠ m → m.2 < y.2 := by
    intro y hyPos hyne
    have hypos : 0 < y.2 :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_highRows_le hyPos)
    have hmle : m.2 ≤ y.2 := hmin y hyPos hypos
    have hne_second : m.2 ≠ y.2 := by
      intro hsec
      have hyA : y ∈ A := (List.mem_filter.mp hyPos).1
      have hyeq : y = m := antichain_same_second_eq hA hyA hmA hsec.symm
      exact hyne hyeq
    exact Nat.lt_of_le_of_ne hmle hne_second
  have hnot : ¬ q ^ (m.2 + 1) ∣ SumTerms p q Pos :=
    not_qpow_succ_dvd_sumTerms_at_strict_second_min hq hpq
      (highRows_antichain hA 1).1 hmPos hstrict
  have hsucc_le_M : m.2 + 1 ≤ M := Nat.succ_le_of_lt (hrow m hmA)
  have hpow_dvd_qM : q ^ (m.2 + 1) ∣ q ^ M :=
    Nat.pow_dvd_pow q hsucc_le_M
  have hdiv : q ^ (m.2 + 1) ∣ SumTerms p q Pos :=
    Nat.dvd_trans hpow_dvd_qM hqM_dvd_pos
  exact hnot hdiv

theorem eq_singleton_of_zero_at_a_and_no_positive_second
    {a : Nat} {A : List Point}
    (hA : IsAntichain A)
    (hzero : (a, 0) ∈ A)
    (huniq_zero : ∀ y, y ∈ A → y.2 = 0 → y = (a, 0))
    (hno_pos : ¬ ∃ x, x ∈ A ∧ 0 < x.2) :
    A = [(a, 0)] := by
  apply list_eq_singleton_of_mem_unique hA.1 hzero
  intro y hy
  by_cases hy0 : y.2 = 0
  · exact huniq_zero y hy hy0
  · have hypos : 0 < y.2 := Nat.pos_of_ne_zero hy0
    exact False.elim (hno_pos ⟨y, hy, hypos⟩)

theorem eq_singleton_of_zero_at_a_of_lowrow_congruence
    {p q a M : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hM : 0 < M)
    (hA : IsAntichain A)
    (hrow : ∀ x, x ∈ A → x.2 < M)
    (hzero : (a, 0) ∈ A)
    (huniq_zero : ∀ y, y ∈ A → y.2 = 0 → y = (a, 0))
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    A = [(a, 0)] := by
  by_cases hpos : ∃ x, x ∈ A ∧ 0 < x.2
  · exact False.elim
      (false_of_zero_at_a_and_positive_second_of_lowrow_congruence
        hq hpq hM hA hrow hzero huniq_zero hpos hcong)
  · exact eq_singleton_of_zero_at_a_and_no_positive_second
      hA hzero huniq_zero hpos

end Apiros1110

end

-- ===== source module Apiros1110.CanonicalMinColumn =====

section

/-
# Canonical minimum-column representations

This file implements the source-level minimum-column recursion using the
repository's list-based representation semantics.
-/

namespace Apiros1110

def ColumnsBelow (A : List Point) (B : Nat) : Prop :=
  ∀ x, x ∈ A → x.1 < B

def Represents (p q n : Nat) (A : List Point) : Prop :=
  IsAntichain A ∧ SumTerms p q A = n

def RepresentsWithin (p q n B : Nat) (A : List Point) : Prop :=
  IsAntichain A ∧ SumTerms p q A = n ∧ ColumnsBelow A B

def RepWithin (p q n B : Nat) : Prop :=
  ∃ A : List Point, RepresentsWithin p q n B A

def IsMinBound (p q n B : Nat) : Prop :=
  RepWithin p q n B ∧ ∀ C : Nat, RepWithin p q n C → B ≤ C

/-- A representation with column bound zero exists exactly for zero. -/
theorem repWithin_zero_bound_iff {p q n : Nat} :
    RepWithin p q n 0 ↔ n = 0 := by
  constructor
  · rintro ⟨A, _hanti, hsum, hcols⟩
    have hnil : A = [] := by
      apply list_eq_nil_of_forall_not_mem
      intro x hx
      exact Nat.not_lt_zero x.1 (hcols x hx)
    subst A
    simpa [SumTerms] using hsum.symm
  · rintro rfl
    refine ⟨[], ?_⟩
    simp [RepresentsWithin, IsAntichain, SumTerms, ColumnsBelow]

/-- A positive natural has no representation with column bound zero. -/
theorem not_repWithin_pos_zero {p q n : Nat} (hn : 0 < n) :
    ¬ RepWithin p q n 0 := by
  rw [repWithin_zero_bound_iff]
  exact Nat.ne_of_gt hn

def shiftUpCoord (x : Point) : Point :=
  (x.1, x.2 + 1)

def shiftUp (A : List Point) : List Point :=
  A.map shiftUpCoord

def shiftDownCoord (x : Point) : Point :=
  (x.1, x.2 - 1)

def shiftDown (A : List Point) : List Point :=
  A.map shiftDownCoord

theorem representsWithin_represents
    {p q n B : Nat} {A : List Point}
    (h : RepresentsWithin p q n B A) :
    Represents p q n A :=
  ⟨h.1, h.2.1⟩

theorem repWithin_mono
    {p q n B C : Nat}
    (h : RepWithin p q n B) (hBC : B ≤ C) :
    RepWithin p q n C := by
  rcases h with ⟨A, hA, hsum, hcols⟩
  refine ⟨A, hA, hsum, ?_⟩
  intro x hx
  exact Nat.lt_of_lt_of_le (hcols x hx) hBC

theorem antichain_shiftUp
    {A : List Point} (hA : IsAntichain A) :
    IsAntichain (shiftUp A) := by
  constructor
  · dsimp [shiftUp]
    apply nodup_map_of_injective_on
    · intro x _hx y _hy hxy
      cases x with
      | mk xi xj =>
          cases y with
          | mk yi yj =>
              dsimp [shiftUpCoord] at hxy ⊢
              injection hxy with hfirst hsecond
              exact Prod.ext hfirst (Nat.succ.inj hsecond)
    · exact hA.1
  · intro u hu v hv huv hcoord
    dsimp [shiftUp] at hu hv
    rcases List.mem_map.mp hu with ⟨x, hxA, hxu⟩
    rcases List.mem_map.mp hv with ⟨y, hyA, hyv⟩
    subst u
    subst v
    have hxy_ne : x ≠ y := by
      intro hxy
      exact huv (by rw [hxy])
    have hcoord_xy : CoordLe x y := by
      cases x with
      | mk xi xj =>
          cases y with
          | mk yi yj =>
              dsimp [CoordLe, shiftUpCoord] at hcoord ⊢
              exact ⟨hcoord.1, Nat.succ_le_succ_iff.mp hcoord.2⟩
    exact hA.2 hxA hyA hxy_ne hcoord_xy

theorem shiftDown_injective_on_pos
    {x y : Point}
    (hx : 0 < x.2) (hy : 0 < y.2)
    (h : shiftDownCoord x = shiftDownCoord y) :
    x = y := by
  cases x with
  | mk xi xj =>
      cases y with
      | mk yi yj =>
          dsimp [shiftDownCoord] at h hx hy ⊢
          injection h with hfirst hsecond
          have hx1 : xj - 1 + 1 = xj := Nat.sub_add_cancel hx
          have hy1 : yj - 1 + 1 = yj := Nat.sub_add_cancel hy
          apply Prod.ext hfirst
          have : xj - 1 + 1 = yj - 1 + 1 := by rw [hsecond]
          simpa [hx1, hy1] using this

theorem shiftDown_reflects_coordLe_on_pos
    {x y : Point}
    (hx : 0 < x.2) (hy : 0 < y.2)
    (h : CoordLe (shiftDownCoord x) (shiftDownCoord y)) :
    CoordLe x y := by
  cases x with
  | mk xi xj =>
      cases y with
      | mk yi yj =>
          dsimp [CoordLe, shiftDownCoord] at hx hy h ⊢
          constructor
          · exact h.1
          · have hadd : xj - 1 + 1 ≤ yj - 1 + 1 :=
              Nat.add_le_add_right h.2 1
            simpa [Nat.sub_add_cancel hx, Nat.sub_add_cancel hy] using hadd

theorem antichain_shiftDown
    {A : List Point}
    (hpos : ∀ x, x ∈ A → 0 < x.2)
    (hA : IsAntichain A) :
    IsAntichain (shiftDown A) := by
  constructor
  · dsimp [shiftDown]
    apply nodup_map_of_injective_on
    · intro x hx y hy hxy
      exact shiftDown_injective_on_pos (hpos x hx) (hpos y hy) hxy
    · exact hA.1
  · intro u hu v hv huv hcoord
    dsimp [shiftDown] at hu hv
    rcases List.mem_map.mp hu with ⟨x, hxA, hxu⟩
    rcases List.mem_map.mp hv with ⟨y, hyA, hyv⟩
    subst u
    subst v
    have hxy_ne : x ≠ y := by
      intro hxy
      exact huv (by rw [hxy])
    have hcoord_xy : CoordLe x y :=
      shiftDown_reflects_coordLe_on_pos (hpos x hxA) (hpos y hyA) hcoord
    exact hA.2 hxA hyA hxy_ne hcoord_xy

theorem columnsBelow_shiftUp
    {A : List Point} {B : Nat} :
    ColumnsBelow (shiftUp A) B ↔ ColumnsBelow A B := by
  constructor
  · intro h x hx
    exact h (shiftUpCoord x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro h y hy
    dsimp [shiftUp] at hy
    rcases List.mem_map.mp hy with ⟨x, hx, hxy⟩
    subst y
    exact h x hx

theorem columnsBelow_shiftDown
    {A : List Point} {B : Nat} :
    ColumnsBelow (shiftDown A) B ↔ ColumnsBelow A B := by
  constructor
  · intro h x hx
    exact h (shiftDownCoord x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro h y hy
    dsimp [shiftDown] at hy
    rcases List.mem_map.mp hy with ⟨x, hx, hxy⟩
    subst y
    exact h x hx

theorem term_shiftUpCoord
    (p q : Nat) (x : Point) :
    Term p q (shiftUpCoord x) = q * Term p q x := by
  cases x with
  | mk i j =>
      dsimp [shiftUpCoord, Term]
      rw [Nat.pow_succ]
      ac_rfl

theorem sourceSum_shiftUp
    (p q : Nat) :
    ∀ A : List Point, SumTerms p q (shiftUp A) = q * SumTerms p q A
  | [] => by
      simp [shiftUp, SumTerms]
  | x :: xs => by
      calc
        SumTerms p q (shiftUp (x :: xs))
            = SumTerms p q (shiftUp xs) + Term p q (shiftUpCoord x) := by
                simp [shiftUp, SumTerms, Nat.add_comm]
        _ = q * SumTerms p q xs + q * Term p q x := by
                rw [sourceSum_shiftUp p q xs, term_shiftUpCoord]
        _ = q * SumTerms p q (x :: xs) := by
                simp [SumTerms, Nat.mul_add]
                ac_rfl

theorem term_shiftDownCoord_mul
    {p q : Nat} {x : Point}
    (hx : 0 < x.2) :
    q * Term p q (shiftDownCoord x) = Term p q x := by
  cases x with
  | mk i j =>
      dsimp [shiftDownCoord, Term] at hx ⊢
      have hsucc : (j - 1) + 1 = j := Nat.sub_add_cancel hx
      calc
        q * (p ^ i * q ^ (j - 1))
            = p ^ i * q ^ ((j - 1) + 1) := by
                rw [Nat.pow_succ]
                ac_rfl
        _ = p ^ i * q ^ j := by rw [hsucc]

theorem sourceSum_shiftDown_mul
    {p q : Nat} :
    ∀ {A : List Point},
      (∀ x, x ∈ A → 0 < x.2) →
      q * SumTerms p q (shiftDown A) = SumTerms p q A
  | [], _ => by
      simp [shiftDown, SumTerms]
  | x :: xs, hpos => by
      have hx : 0 < x.2 := hpos x List.mem_cons_self
      have hxs : ∀ y, y ∈ xs → 0 < y.2 := by
        intro y hy
        exact hpos y (List.mem_cons_of_mem x hy)
      have ih := sourceSum_shiftDown_mul (p := p) (q := q) hxs
      calc
        q * SumTerms p q (shiftDown (x :: xs))
            = q * (SumTerms p q (shiftDown xs) + Term p q (shiftDownCoord x)) := by
                simp [shiftDown, SumTerms, Nat.add_comm]
        _ = q * SumTerms p q (shiftDown xs) + q * Term p q (shiftDownCoord x) := by
                rw [Nat.mul_add]
        _ = SumTerms p q xs + Term p q x := by
                rw [ih, term_shiftDownCoord_mul hx]
        _ = SumTerms p q (x :: xs) := by
                simp [SumTerms, Nat.add_comm]

theorem representsWithin_shiftUp
    {p q m B : Nat} {A : List Point}
    (hA : RepresentsWithin p q m B A) :
    RepresentsWithin p q (q * m) B (shiftUp A) := by
  refine ⟨antichain_shiftUp hA.1, ?_, ?_⟩
  · rw [sourceSum_shiftUp, hA.2.1]
  · exact columnsBelow_shiftUp.mpr hA.2.2

theorem row_zero_unique
    {A : List Point} (hA : IsAntichain A)
    {x y : Point}
    (hx : x ∈ A) (hy : y ∈ A)
    (hx0 : x.2 = 0) (hy0 : y.2 = 0) :
    x = y :=
  second_zero_unique_of_antichain hA hx hy hx0 hy0

theorem no_row_zero_of_q_dvd_sumTerms
    {p q : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hA : IsAntichain A)
    (hdiv : q ∣ SumTerms p q A) :
    ∀ x, x ∈ A → x.2 ≠ 0 := by
  intro x hx hx0
  have huniq : ∀ y, y ∈ A → y.2 = 0 → y = x := by
    intro y hy hy0
    exact row_zero_unique hA hy hx hy0 hx0
  have hsplit :
      SumTerms p q A = Term p q x + SumTerms p q (highRows 1 A) :=
    sumTerms_eq_zeroSecond_term_add_highRows_one hA.1 hx hx0 huniq
  have hhigh : q ∣ SumTerms p q (highRows 1 A) := by
    apply q_dvd_sumTerms_of_all_second_pos
    intro y hy
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_highRows_le hy)
  have hterm_dvd : q ∣ Term p q x := by
    rw [hsplit] at hdiv
    exact (Nat.dvd_add_left hhigh).mp hdiv
  cases x with
  | mk i j =>
      dsimp [Term] at hterm_dvd hx0
      rw [hx0] at hterm_dvd
      simp at hterm_dvd
      exact not_dvd_coprime_pow hq hpq hterm_dvd

theorem represented_multiple_has_positive_rows
    {p q m : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hA : IsAntichain A) (hsum : SumTerms p q A = q * m) :
    ∀ x, x ∈ A → 0 < x.2 := by
  have hdiv : q ∣ SumTerms p q A := by
    rw [hsum]
    exact Nat.dvd_mul_right q m
  intro x hx
  exact Nat.pos_of_ne_zero (no_row_zero_of_q_dvd_sumTerms hq hpq hA hdiv x hx)

theorem representsWithin_shiftDown_of_mul_q
    {p q m B : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hA : RepresentsWithin p q (q * m) B A) :
    RepresentsWithin p q m B (shiftDown A) := by
  have hpos : ∀ x, x ∈ A → 0 < x.2 :=
    represented_multiple_has_positive_rows hq hpq hA.1 hA.2.1
  refine ⟨antichain_shiftDown hpos hA.1, ?_, ?_⟩
  · have hmul := sourceSum_shiftDown_mul (p := p) (q := q) hpos
    rw [hA.2.1] at hmul
    have hqpos : 0 < q := Nat.lt_trans Nat.zero_lt_one hq
    exact Nat.mul_left_cancel hqpos hmul
  · exact columnsBelow_shiftDown.mpr hA.2.2

theorem repWithin_mul_q_iff
    {p q m B : Nat}
    (_hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q) :
    RepWithin p q (q * m) B ↔ RepWithin p q m B := by
  constructor
  · intro h
    rcases h with ⟨A, hA⟩
    exact ⟨shiftDown A, representsWithin_shiftDown_of_mul_q hq hpq hA⟩
  · intro h
    rcases h with ⟨A, hA⟩
    exact ⟨shiftUp A, representsWithin_shiftUp hA⟩

theorem exists_row_zero_of_not_q_dvd_sumTerms
    {p q : Nat} {A : List Point}
    (hnot : ¬ q ∣ SumTerms p q A) :
    ∃ x, x ∈ A ∧ x.2 = 0 := by
  by_contra hzero
  have hpos : ∀ x, x ∈ A → 0 < x.2 := by
    intro x hx
    by_cases hx0 : x.2 = 0
    · exact False.elim (hzero ⟨x, hx, hx0⟩)
    · exact Nat.pos_of_ne_zero hx0
  exact hnot (q_dvd_sumTerms_of_all_second_pos hpos)

theorem exists_unique_row_zero_of_not_q_dvd
    {p q n : Nat} {A : List Point}
    (hA : IsAntichain A) (hsum : SumTerms p q A = n)
    (hnot : ¬ q ∣ n) :
    ∃ e : Nat, (e, 0) ∈ A ∧
      ∀ y, y ∈ A → y.2 = 0 → y = (e, 0) := by
  have hnot_sum : ¬ q ∣ SumTerms p q A := by
    intro hdiv
    exact hnot (by simpa [hsum] using hdiv)
  rcases exists_row_zero_of_not_q_dvd_sumTerms hnot_sum with ⟨x, hx, hx0⟩
  rcases x with ⟨i, j⟩
  dsimp at hx0
  subst j
  refine ⟨i, hx, ?_⟩
  intro y hy hy0
  exact row_zero_unique hA hy hx hy0 rfl

theorem highRows_one_columns_below_row_zero
    {A : List Point} {e : Nat}
    (hA : IsAntichain A)
    (hzero : (e, 0) ∈ A) :
    ColumnsBelow (highRows 1 A) e := by
  intro x hxH
  have hxA : x ∈ A := (List.mem_filter.mp hxH).1
  have hxpos : 0 < x.2 :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_highRows_le hxH)
  have hx_ne : (e, 0) ≠ x := by
    intro h
    have : x.2 = 0 := by rw [← h]
    omega
  have hnot : ¬ CoordLe (e, 0) x :=
    hA.2 hzero hxA hx_ne
  exact Nat.lt_of_not_ge fun he_le =>
    hnot ⟨he_le, Nat.zero_le x.2⟩

theorem shiftedHighRows_one_columns_below_row_zero
    {A : List Point} {e : Nat}
    (hA : IsAntichain A)
    (hzero : (e, 0) ∈ A) :
    ColumnsBelow (shiftedHighRows 1 A) e := by
  intro y hy
  dsimp [shiftedHighRows] at hy
  rcases List.mem_map.mp hy with ⟨x, hxH, hxy⟩
  subst y
  exact highRows_one_columns_below_row_zero hA hzero x hxH

theorem source_decomp_not_q_dvd
    {p q n B : Nat} {A : List Point}
    (hnot : ¬ q ∣ n)
    (hA : RepresentsWithin p q n B A) :
    ∃ e m : Nat,
      e < B ∧
      n = p ^ e + q * m ∧
      RepWithin p q m e ∧
      (e, 0) ∈ A := by
  rcases exists_unique_row_zero_of_not_q_dvd hA.1 hA.2.1 hnot with
    ⟨e, heA, huniq⟩
  let C := shiftedHighRows 1 A
  let m := SumTerms p q C
  refine ⟨e, m, hA.2.2 (e, 0) heA, ?_, ?_, heA⟩
  · have hsplit :
        SumTerms p q A = p ^ e + SumTerms p q (highRows 1 A) := by
      have hs := sumTerms_eq_zeroSecond_term_add_highRows_one (p := p) (q := q)
        hA.1.1 heA rfl huniq
      simpa [Term] using hs
    have hfactor := highRows_sum_factor p q 1 A
    dsimp [C, m]
    rw [← hA.2.1, hsplit, hfactor]
    simp
  · refine ⟨C, shiftedHighRows_antichain hA.1 1, rfl, ?_⟩
    dsimp [C]
    exact shiftedHighRows_one_columns_below_row_zero hA.1 heA

theorem parent_antichain
    {A : List Point} {e : Nat}
    (hA : IsAntichain A)
    (hcols : ColumnsBelow A e) :
    IsAntichain ((e, 0) :: shiftUp A) := by
  have hshift : IsAntichain (shiftUp A) := antichain_shiftUp hA
  constructor
  · rw [List.nodup_cons]
    constructor
    · intro hmem
      dsimp [shiftUp] at hmem
      rcases List.mem_map.mp hmem with ⟨x, hxA, hxeq⟩
      have hsecond : (shiftUpCoord x).2 = 0 := by simp [hxeq]
      dsimp [shiftUpCoord] at hsecond
      omega
    · exact hshift.1
  · intro x hx y hy hne hcoord
    rw [List.mem_cons] at hx hy
    cases hx with
    | inl hxhead =>
        subst x
        cases hy with
        | inl hyhead =>
            subst y
            exact False.elim (hne rfl)
        | inr hyshift =>
            dsimp [shiftUp] at hyshift
            rcases List.mem_map.mp hyshift with ⟨z, hzA, hzy⟩
            subst y
            dsimp [CoordLe, shiftUpCoord] at hcoord
            exact Nat.not_le_of_gt (hcols z hzA) hcoord.1
    | inr hxshift =>
        cases hy with
        | inl hyhead =>
            subst y
            dsimp [shiftUp] at hxshift
            rcases List.mem_map.mp hxshift with ⟨z, hzA, hzx⟩
            subst x
            dsimp [CoordLe, shiftUpCoord] at hcoord
            omega
        | inr hyshift =>
            exact hshift.2 hxshift hyshift hne hcoord

theorem parent_columnsBelow
    {A : List Point} {e B : Nat}
    (hcols : ColumnsBelow A e) (heB : e < B) :
    ColumnsBelow ((e, 0) :: shiftUp A) B := by
  intro x hx
  rw [List.mem_cons] at hx
  cases hx with
  | inl hxhead =>
      subst x
      exact heB
  | inr hxshift =>
      dsimp [shiftUp] at hxshift
      rcases List.mem_map.mp hxshift with ⟨y, hyA, hyx⟩
      subst x
      exact Nat.lt_trans (hcols y hyA) heB

theorem parent_sum
    (p q e : Nat) :
    ∀ A : List Point,
      SumTerms p q ((e, 0) :: shiftUp A) =
        p ^ e + q * SumTerms p q A
  | A => by
      calc
        SumTerms p q ((e, 0) :: shiftUp A)
            = SumTerms p q (shiftUp A) + Term p q (e, 0) := by
                simp [SumTerms, Nat.add_comm]
        _ = q * SumTerms p q A + p ^ e := by
                rw [sourceSum_shiftUp, term_first_zeroSecond]
        _ = p ^ e + q * SumTerms p q A := by
                ac_rfl

theorem parent_representsWithin
    {p q m e B : Nat} {A : List Point}
    (hA : RepresentsWithin p q m e A)
    (heB : e < B) :
    RepresentsWithin p q (p ^ e + q * m) B ((e, 0) :: shiftUp A) := by
  refine ⟨parent_antichain hA.1 hA.2.2, ?_, parent_columnsBelow hA.2.2 heB⟩
  rw [parent_sum, hA.2.1]

/-- If an attachment has minimum column bound `e + 1`, then an algebraically
equal attachment at a lower column `f` cannot have its child represented
within `f`. -/
theorem not_repWithin_lower_child_of_isMinBound
    {p q e m f r : Nat}
    (hmin : IsMinBound p q (p ^ e + q * m) (e + 1))
    (hf : f < e)
    (heq : p ^ e + q * m = p ^ f + q * r) :
    ¬ RepWithin p q r f := by
  intro hr
  rcases hr with ⟨A, hA⟩
  have hlower : RepWithin p q (p ^ e + q * m) (f + 1) := by
    refine ⟨(f, 0) :: shiftUp A, ?_⟩
    rw [heq]
    exact parent_representsWithin hA (Nat.lt_succ_self f)
  have hle := hmin.2 (f + 1) hlower
  omega

theorem repWithin_not_dvd_iff
    {p q n B : Nat}
    (_hp : 1 < p) (_hq : 1 < q)
    (_hpq : Nat.Coprime p q)
    (hqn : ¬ q ∣ n) :
    RepWithin p q n B ↔
      ∃ e : Nat, e < B ∧
      ∃ m : Nat, n = p ^ e + q * m ∧
        RepWithin p q m e := by
  constructor
  · intro h
    rcases h with ⟨A, hA⟩
    rcases source_decomp_not_q_dvd hqn hA with
      ⟨e, m, heB, heq, hm, _heA⟩
    exact ⟨e, heB, m, heq, hm⟩
  · intro h
    rcases h with ⟨e, heB, m, heq, hm⟩
    rcases hm with ⟨A, hA⟩
    refine ⟨(e, 0) :: shiftUp A, ?_⟩
    rw [heq]
    exact parent_representsWithin hA heB

theorem source_columnsBound_exists :
    ∀ A : List Point, ∃ B : Nat, ColumnsBelow A B
  | [] => by
      exact ⟨0, by intro x hx; cases hx⟩
  | x :: xs => by
      rcases source_columnsBound_exists xs with ⟨B, hB⟩
      refine ⟨max (x.1 + 1) B, ?_⟩
      intro y hy
      rw [List.mem_cons] at hy
      cases hy with
      | inl hyx =>
          subst y
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self x.1) (Nat.le_max_left _ _)
      | inr hyxs =>
          exact Nat.lt_of_lt_of_le (hB y hyxs) (Nat.le_max_right _ _)

theorem representable_iff_exists_repWithin
    {p q n : Nat} :
    Representable p q n ↔ ∃ B : Nat, RepWithin p q n B := by
  constructor
  · intro h
    rcases h with ⟨A, hA, hsum⟩
    rcases source_columnsBound_exists A with ⟨B, hB⟩
    exact ⟨B, A, hA, hsum, hB⟩
  · intro h
    rcases h with ⟨_B, A, hA, hsum, _hcols⟩
    exact ⟨A, hA, hsum⟩

theorem exists_minBound
    {p q n : Nat}
    (hn : Representable p q n) :
    ∃ B : Nat, IsMinBound p q n B := by
  classical
  have hex : ∃ B : Nat, RepWithin p q n B :=
    representable_iff_exists_repWithin.mp hn
  let B := Nat.find hex
  have hB : RepWithin p q n B := Nat.find_spec hex
  refine ⟨B, hB, ?_⟩
  intro C hC
  exact Nat.find_min' hex hC

theorem minBound_unique
    {p q n B C : Nat}
    (hB : IsMinBound p q n B)
    (hC : IsMinBound p q n C) :
    B = C :=
  Nat.le_antisymm (hB.2 C hC.1) (hC.2 B hB.1)

theorem exists_unique_minBound
    {p q n : Nat}
    (hn : Representable p q n) :
    ∃! B : Nat, IsMinBound p q n B := by
  rcases exists_minBound hn with ⟨B, hB⟩
  exact ⟨B, hB, fun C hC => minBound_unique hC hB⟩

theorem minBound_mul_q
    {p q m B : Nat}
    (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (hmin : IsMinBound p q m B) :
    IsMinBound p q (q * m) B := by
  constructor
  · exact (repWithin_mul_q_iff hp hq hpq).mpr hmin.1
  · intro C hC
    exact hmin.2 C ((repWithin_mul_q_iff hp hq hpq).mp hC)

theorem minBound_of_mul_q
    {p q m B : Nat}
    (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (hmin : IsMinBound p q (q * m) B) :
    IsMinBound p q m B := by
  constructor
  · exact (repWithin_mul_q_iff hp hq hpq).mp hmin.1
  · intro C hC
    exact hmin.2 C ((repWithin_mul_q_iff hp hq hpq).mpr hC)

theorem repWithin_of_row_zero
    {p q n B e : Nat} {A : List Point}
    (hnot : ¬ q ∣ n)
    (hA : RepresentsWithin p q n B A)
    (he : (e, 0) ∈ A) :
    ∃ m : Nat, n = p ^ e + q * m ∧ RepWithin p q m e := by
  rcases source_decomp_not_q_dvd hnot hA with
    ⟨e', m, _heB, heq, hm, heA'⟩
  have heq' : (e, 0) = (e', 0) :=
    row_zero_unique hA.1 he heA' rfl rfl
  injection heq' with hee
  subst e'
  exact ⟨m, heq, hm⟩

theorem rowZero_exp_eq_of_minBound
    {p q n B : Nat} {A : List Point} {e : Nat}
    (_hp : 1 < p) (_hq : 1 < q)
    (_hpq : Nat.Coprime p q)
    (hqn : ¬ q ∣ n)
    (hmin : IsMinBound p q n B)
    (hrep : RepresentsWithin p q n B A)
    (he : (e, 0) ∈ A) :
    e + 1 = B := by
  rcases repWithin_of_row_zero hqn hrep he with ⟨m, heq, hm⟩
  have hparent : RepWithin p q n (e + 1) := by
    rw [heq]
    rcases hm with ⟨C, hC⟩
    exact ⟨(e, 0) :: shiftUp C, parent_representsWithin hC (Nat.lt_succ_self e)⟩
  have hB_le : B ≤ e + 1 := hmin.2 (e + 1) hparent
  have he_lt_B : e < B := hrep.2.2 (e, 0) he
  exact Nat.le_antisymm (Nat.succ_le_of_lt he_lt_B) hB_le

end Apiros1110

end

-- ===== source module Apiros1110.Canonical =====

section

/-
# Recursive canonical sources and reverse extensions
-/

namespace Apiros1110

inductive IsCanonicalSource (p q : Nat) :
    Nat → List Point → Prop
  | zero :
      IsCanonicalSource p q 0 []
  | scale
      {m : Nat} {A : List Point}
      (hm : 0 < m)
      (hcan : IsCanonicalSource p q m A) :
      IsCanonicalSource p q (q * m) (shiftUp A)
  | attach
      {e m : Nat} {A : List Point}
      (hnot : ¬ q ∣ (p ^ e + q * m))
      (hmin : IsMinBound p q (p ^ e + q * m) (e + 1))
      (hcan : IsCanonicalSource p q m A)
      (hcols : ColumnsBelow A e) :
      IsCanonicalSource p q
        (p ^ e + q * m)
        ((e, 0) :: shiftUp A)

theorem represents_shiftUp
    {p q m : Nat} {A : List Point}
    (hA : Represents p q m A) :
    Represents p q (q * m) (shiftUp A) := by
  exact ⟨antichain_shiftUp hA.1, by rw [sourceSum_shiftUp, hA.2]⟩

theorem canonical_represents
    {p q n : Nat} {A : List Point}
    (hcan : IsCanonicalSource p q n A) :
    Represents p q n A := by
  induction hcan with
  | zero =>
      simp [Represents, IsAntichain, SumTerms]
  | scale hm hcan ih =>
      exact represents_shiftUp ih
  | attach hnot hmin hcan hcols ih =>
      exact ⟨parent_antichain ih.1 hcols, by rw [parent_sum, ih.2]⟩

theorem canonical_target_eq_sourceSum
    {p q n : Nat} {A : List Point}
    (hcan : IsCanonicalSource p q n A) :
    SumTerms p q A = n :=
  (canonical_represents hcan).2

theorem canonical_same_source_target_eq
    {p q n n' : Nat} {A : List Point}
    (hcan : IsCanonicalSource p q n A)
    (hcan' : IsCanonicalSource p q n' A) :
    n = n' := by
  rw [← canonical_target_eq_sourceSum hcan,
    ← canonical_target_eq_sourceSum hcan']

theorem zero_minBound (p q : Nat) :
    IsMinBound p q 0 0 := by
  constructor
  · refine ⟨[], ?_, ?_, ?_⟩
    · simp [IsAntichain]
    · simp [SumTerms]
    · intro x hx
      cases hx
  · intro C _hC
    exact Nat.zero_le C

theorem canonical_has_minBound
    {p q n : Nat} {A : List Point}
    (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (hcan : IsCanonicalSource p q n A) :
    ∃ B : Nat,
      IsMinBound p q n B ∧
      ColumnsBelow A B := by
  induction hcan with
  | zero =>
      exact ⟨0, zero_minBound p q, by intro x hx; cases hx⟩
  | scale hm hcan ih =>
      rcases ih with ⟨B, hmin, hcols⟩
      exact ⟨B, minBound_mul_q hp hq hpq hmin,
        columnsBelow_shiftUp.mpr hcols⟩
  | attach hnot hmin hcan hcols ih =>
      exact ⟨_, hmin, parent_columnsBelow hcols (Nat.lt_succ_self _)⟩

theorem representable_of_canonical
    {p q n : Nat} {A : List Point}
    (hcan : IsCanonicalSource p q n A) :
    Representable p q n := by
  exact ⟨A, (canonical_represents hcan).1, (canonical_represents hcan).2⟩

theorem mul_child_lt
    {q m : Nat} (hq : 1 < q) (hm : 0 < m) :
    m < q * m := by
  exact (Nat.lt_mul_iff_one_lt_left hm).2 hq

theorem attach_child_lt
    {p q e m : Nat} (hp : 1 < p) (hq : 1 < q) :
    m < p ^ e + q * m := by
  have hp_pos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hpow_pos : 0 < p ^ e := Nat.pow_pos hp_pos
  have hq_pos : 0 < q := Nat.lt_trans Nat.zero_lt_one hq
  have hm_le_qm : m ≤ q * m := by
    rw [Nat.mul_comm]
    exact Nat.le_mul_of_pos_right m hq_pos
  exact Nat.lt_of_le_of_lt hm_le_qm (Nat.lt_add_of_pos_left hpow_pos)

theorem exists_canonical_of_representable
    {p q n : Nat}
    (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (hn : Representable p q n) :
    ∃ A B,
      IsCanonicalSource p q n A ∧
      IsMinBound p q n B ∧
      ColumnsBelow A B := by
  classical
  revert hn
  refine Nat.strong_induction_on n ?_
  intro n ih hn
  by_cases hnzero : n = 0
  · subst n
    exact ⟨[], 0, IsCanonicalSource.zero, zero_minBound p q,
      by intro x hx; cases hx⟩
  · by_cases hdiv : q ∣ n
    · rcases hdiv with ⟨m, hmEq⟩
      subst n
      have hmpos : 0 < m := by
        by_cases hm0 : m = 0
        · subst m
          simp at hnzero
        · exact Nat.pos_of_ne_zero hm0
      have hm_lt : m < q * m := mul_child_lt hq hmpos
      rcases representable_iff_exists_repWithin.mp hn with ⟨B, hB⟩
      have hmWithin : RepWithin p q m B :=
        (repWithin_mul_q_iff hp hq hpq).mp hB
      have hmRep : Representable p q m :=
        representable_iff_exists_repWithin.mpr ⟨B, hmWithin⟩
      rcases ih m hm_lt hmRep with ⟨A, D, hcan, hmin, hcols⟩
      exact ⟨shiftUp A, D, IsCanonicalSource.scale hmpos hcan,
        minBound_mul_q hp hq hpq hmin, columnsBelow_shiftUp.mpr hcols⟩
    · rcases exists_minBound hn with ⟨B, hmin⟩
      rcases hmin.1 with ⟨A0, hA0⟩
      rcases source_decomp_not_q_dvd hdiv hA0 with
        ⟨e, m, _heB, hnEq, hmWithin, heA0⟩
      have hB_eq : e + 1 = B :=
        rowZero_exp_eq_of_minBound hp hq hpq hdiv hmin hA0 heA0
      have hmRep : Representable p q m :=
        representable_iff_exists_repWithin.mpr ⟨e, hmWithin⟩
      have hm_lt : m < n := by
        rw [hnEq]
        exact attach_child_lt hp hq
      rcases ih m hm_lt hmRep with ⟨C, D, hcanC, hminC, hcolsC⟩
      have hD_le_e : D ≤ e := hminC.2 e hmWithin
      have hcols_e : ColumnsBelow C e := by
        intro x hx
        exact Nat.lt_of_lt_of_le (hcolsC x hx) hD_le_e
      have htarget_not : ¬ q ∣ p ^ e + q * m := by
        intro hqdiv
        exact hdiv (by simpa [hnEq] using hqdiv)
      have htarget_min :
          IsMinBound p q (p ^ e + q * m) (e + 1) := by
        rw [← hnEq, hB_eq]
        exact hmin
      refine ⟨(e, 0) :: shiftUp C, e + 1, ?_, ?_, ?_⟩
      · simpa [hnEq] using
          IsCanonicalSource.attach htarget_not htarget_min hcanC hcols_e
      · simpa [hnEq] using htarget_min
      · exact parent_columnsBelow hcols_e (Nat.lt_succ_self e)

theorem term_pos_of_pos_bases
    {p q : Nat}
    (hp : 0 < p) (hq : 0 < q)
    (x : Point) :
    0 < Term p q x := by
  cases x with
  | mk i j =>
      exact Nat.mul_pos
        (Nat.pow_pos hp : 0 < p ^ i)
        (Nat.pow_pos hq : 0 < q ^ j)

theorem canonical_zero_eq_empty
    {p q : Nat} {A : List Point}
    (hp : 1 < p) (hq : 1 < q)
    (hcan : IsCanonicalSource p q 0 A) :
    A = [] := by
  apply list_eq_nil_of_forall_not_mem
  intro x hx
  have hsum : SumTerms p q A = 0 := canonical_target_eq_sourceSum hcan
  have hle : Term p q x ≤ SumTerms p q A := mem_term_le_sum hx
  rw [hsum] at hle
  have hp_pos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hq_pos : 0 < q := Nat.lt_trans Nat.zero_lt_one hq
  have hterm_pos : 0 < Term p q x := term_pos_of_pos_bases hp_pos hq_pos x
  exact (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hterm_pos hle))

theorem canonical_scale_cases
    {p q n : Nat} {A : List Point}
    (_hq : 1 < q)
    (hnpos : 0 < n)
    (hdiv : q ∣ n)
    (hcan : IsCanonicalSource p q n A) :
    ∃ m C,
      0 < m ∧
      n = q * m ∧
      IsCanonicalSource p q m C ∧
      A = shiftUp C := by
  cases hcan with
  | zero =>
      omega
  | scale hm hcan =>
      exact ⟨_, _, hm, rfl, hcan, rfl⟩
  | attach hnot hmin hcan hcols =>
      exact False.elim (hnot hdiv)

theorem canonical_attach_cases
    {p q n : Nat} {A : List Point}
    (hnotn : ¬ q ∣ n)
    (hcan : IsCanonicalSource p q n A) :
    ∃ e m C,
      n = p ^ e + q * m ∧
      ¬ q ∣ p ^ e + q * m ∧
      IsMinBound p q (p ^ e + q * m) (e + 1) ∧
      IsCanonicalSource p q m C ∧
      ColumnsBelow C e ∧
      A = ((e, 0) :: shiftUp C) := by
  cases hcan with
  | zero =>
      exact False.elim (hnotn (Nat.dvd_zero q))
  | scale hm hcan =>
      exact False.elim (hnotn (Nat.dvd_mul_right q _))
  | attach hnot hmin hcan hcols =>
      exact ⟨_, _, _, rfl, hnot, hmin, hcan, hcols, rfl⟩

theorem canonical_unique_aux
    {p q : Nat}
    (hp : 1 < p) (hq : 1 < q)
    (_hpq : Nat.Coprime p q) :
    ∀ n : Nat, ∀ A A' : List Point,
      IsCanonicalSource p q n A →
      IsCanonicalSource p q n A' →
      A = A' := by
  classical
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih A A' hA hA'
  by_cases hnzero : n = 0
  · subst n
    rw [canonical_zero_eq_empty hp hq hA, canonical_zero_eq_empty hp hq hA']
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
    by_cases hdiv : q ∣ n
    · rcases canonical_scale_cases hq hnpos hdiv hA with
        ⟨m, C, hmpos, hmEq, hcanC, hAeq⟩
      rcases canonical_scale_cases hq hnpos hdiv hA' with
        ⟨m', C', hmpos', hmEq', hcanC', hAeq'⟩
      have hqpos : 0 < q := Nat.lt_trans Nat.zero_lt_one hq
      have hmm' : m = m' := by
        apply Nat.mul_left_cancel hqpos
        rw [← hmEq, ← hmEq']
      subst m'
      have hm_lt : m < n := by
        rw [hmEq]
        exact mul_child_lt hq hmpos
      have hCC' : C = C' := ih m hm_lt C C' hcanC hcanC'
      rw [hAeq, hAeq', hCC']
    · rcases canonical_attach_cases hdiv hA with
        ⟨e, m, C, hnEq, hnot, hmin, hcanC, hcols, hAeq⟩
      rcases canonical_attach_cases hdiv hA' with
        ⟨e', m', C', hnEq', hnot', hmin', hcanC', hcols', hAeq'⟩
      have hminN : IsMinBound p q n (e + 1) := by
        simpa [hnEq] using hmin
      have hminN' : IsMinBound p q n (e' + 1) := by
        simpa [hnEq'] using hmin'
      have hsucc : e + 1 = e' + 1 := minBound_unique hminN hminN'
      have heq : e = e' := Nat.succ.inj hsucc
      subst e'
      have hmm' : m = m' := by
        have hadd : q * m = q * m' := by
          have hbig : p ^ e + q * m = p ^ e + q * m' := by
            rw [← hnEq, ← hnEq']
          exact Nat.add_left_cancel hbig
        have hqpos : 0 < q := Nat.lt_trans Nat.zero_lt_one hq
        exact Nat.mul_left_cancel hqpos hadd
      subst m'
      have hm_lt : m < n := by
        rw [hnEq]
        exact attach_child_lt hp hq
      have hCC' : C = C' := ih m hm_lt C C' hcanC hcanC'
      rw [hAeq, hAeq', hCC']

theorem canonical_unique
    {p q n : Nat} {A A' : List Point}
    (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (hA : IsCanonicalSource p q n A)
    (hA' : IsCanonicalSource p q n A') :
    A = A' :=
  canonical_unique_aux hp hq hpq n A A' hA hA'

theorem representable_iff_existsUnique_canonical
    {p q n : Nat}
    (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q) :
    Representable p q n ↔
      ∃! A : List Point, IsCanonicalSource p q n A := by
  constructor
  · intro hn
    rcases exists_canonical_of_representable hp hq hpq hn with
      ⟨A, _B, hcan, _hmin, _hcols⟩
    exact ⟨A, hcan, fun A' hcan' => canonical_unique hp hq hpq hcan' hcan⟩
  · intro h
    rcases h with ⟨A, hcan, _huniq⟩
    exact representable_of_canonical hcan

theorem not_q_dvd_attach_target
    {p q e m : Nat}
    (hq : 1 < q) (hpq : Nat.Coprime p q) :
    ¬ q ∣ p ^ e + q * m :=
  not_q_dvd_p_pow_add_q_mul hq hpq

theorem minBound_attach_iff
    {p q e m : Nat}
    (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (hm : RepWithin p q m e) :
    IsMinBound p q (p ^ e + q * m) (e + 1) ↔
      ∀ f : Nat, f < e →
      ∀ r : Nat, p ^ e + q * m = p ^ f + q * r →
        ¬ RepWithin p q r f := by
  constructor
  · intro hmin f hf r heq hr
    rcases hr with ⟨R, hR⟩
    have hsmall : RepWithin p q (p ^ e + q * m) (f + 1) := by
      rw [heq]
      exact ⟨(f, 0) :: shiftUp R,
        parent_representsWithin hR (Nat.lt_succ_self f)⟩
    have hle : e + 1 ≤ f + 1 := hmin.2 (f + 1) hsmall
    omega
  · intro hexcl
    have hnot : ¬ q ∣ p ^ e + q * m :=
      not_q_dvd_attach_target hq hpq
    constructor
    · rcases hm with ⟨A, hA⟩
      exact ⟨(e, 0) :: shiftUp A,
        parent_representsWithin hA (Nat.lt_succ_self e)⟩
    · intro C hC
      rcases (repWithin_not_dvd_iff hp hq hpq hnot).mp hC with
        ⟨f, hfC, r, heq, hr⟩
      by_cases hCe : C ≤ e
      · have hfe : f < e := Nat.lt_of_lt_of_le hfC hCe
        exact False.elim ((hexcl f hfe r heq) hr)
      · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hCe)

end Apiros1110

end

-- ===== source module Apiros1110.Density.Basic =====

section

/-
# Counting representable integers

This file contains the finite counting object used in the Yu--Chen argument,
together with the symmetry and finite-injection lemmas needed downstream.
-/

namespace Apiros1110

noncomputable def representableCount (p q X : Nat) : Nat := by
  classical
  exact ((List.range (X + 1)).filter
    (fun n => decide (0 < n ∧ Representable p q n))).length

def swapPoint (x : Point) : Point :=
  (x.2, x.1)

def swapPoints (A : List Point) : List Point :=
  A.map swapPoint

theorem swapPoint_injective :
    Function.Injective swapPoint := by
  intro x y h
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp [swapPoint] at h
  exact Prod.ext h.2 h.1

theorem coordLe_swapPoint_iff
    {x y : Point} :
    CoordLe (swapPoint x) (swapPoint y) ↔ CoordLe x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp [swapPoint, CoordLe, and_comm]

theorem isAntichain_swapPoints
    {A : List Point}
    (hA : IsAntichain A) :
    IsAntichain (swapPoints A) := by
  constructor
  · exact List.Nodup.map swapPoint_injective hA.1
  · intro sx hsx sy hsy hne hle
    dsimp [swapPoints] at hsx hsy
    rw [List.mem_map] at hsx hsy
    rcases hsx with ⟨x, hx, rfl⟩
    rcases hsy with ⟨y, hy, rfl⟩
    exact hA.2 hx hy
      (by
        intro hxy
        exact hne (by rw [hxy]))
      ((coordLe_swapPoint_iff).mp hle)

theorem term_swapPoint
    (p q : Nat) (x : Point) :
    Term q p (swapPoint x) = Term p q x := by
  rcases x with ⟨x₁, x₂⟩
  simp [swapPoint, Term, Nat.mul_comm]

theorem sumTerms_swapPoints
    (p q : Nat) :
    ∀ A : List Point,
      SumTerms q p (swapPoints A) = SumTerms p q A
  | [] => by
      simp [swapPoints, SumTerms]
  | x :: xs => by
      change Term q p (swapPoint x) + SumTerms q p (swapPoints xs) =
        Term p q x + SumTerms p q xs
      rw [term_swapPoint, sumTerms_swapPoints]

theorem representable_swap
    {p q n : Nat}
    (h : Representable p q n) :
    Representable q p n := by
  rcases h with ⟨A, hA, hsum⟩
  exact ⟨swapPoints A, isAntichain_swapPoints hA,
    by rw [sumTerms_swapPoints, hsum]⟩

theorem representable_comm
    {p q n : Nat} :
    Representable p q n ↔ Representable q p n :=
  ⟨representable_swap, representable_swap⟩

theorem representableCount_comm
    (p q X : Nat) :
    representableCount p q X = representableCount q p X := by
  classical
  unfold representableCount
  congr 1
  apply List.filter_congr
  intro n hn
  apply Bool.decide_congr
  constructor
  · intro h
    exact ⟨h.1, representable_swap h.2⟩
  · intro h
    exact ⟨h.1, representable_swap h.2⟩

namespace DensityDecoderCert

noncomputable def representedFinset (P Q X : Nat) : Finset Nat := by
  classical
  exact ((List.range (X + 1)).filter
    (fun n => decide (0 < n ∧ Representable P Q n))).toFinset

theorem representedFinset_card (P Q X : Nat) :
    (representedFinset P Q X).card = representableCount P Q X := by
  classical
  dsimp [representedFinset, representableCount]
  exact List.toFinset_card_of_nodup
    (List.Nodup.filter _ (List.nodup_range (n := X + 1)))

theorem mem_representedFinset_of
    {P Q X n : Nat}
    (hpos : 0 < n) (hbound : n ≤ X) (hrep : Representable P Q n) :
    n ∈ representedFinset P Q X := by
  classical
  dsimp [representedFinset]
  simp [List.mem_range, Nat.lt_succ_of_le hbound, hpos, hrep]

theorem card_le_representableCount_of_injOn
    {α : Type} [DecidableEq α]
    {P Q X : Nat} (s : Finset α) (value : α → Nat)
    (hvalue :
      ∀ a ∈ s, 0 < value a ∧ value a ≤ X ∧ Representable P Q (value a))
    (hinj : Set.InjOn value (s : Set α)) :
    s.card ≤ representableCount P Q X := by
  classical
  have hmaps :
      Set.MapsTo value (s : Set α) (representedFinset P Q X : Set Nat) := by
    intro a ha
    exact mem_representedFinset_of (hvalue a ha).1 (hvalue a ha).2.1
      (hvalue a ha).2.2
  exact (Finset.card_le_card_of_injOn value hmaps hinj).trans_eq
    (representedFinset_card P Q X)

end DensityDecoderCert

end Apiros1110

end

-- ===== source module Apiros1110.Providers =====

section

/-
# Provider interfaces
-/

namespace Apiros1110

structure ValidBases (p q : Nat) : Prop where
  one_lt_p : 1 < p
  one_lt_q : 1 < q
  coprime : Nat.Coprime p q

theorem validBases_mul_gt_one
    {p q : Nat} (hb : ValidBases p q) :
    1 < p * q := by
  have hqpos : 0 < q := Nat.lt_trans Nat.zero_lt_one hb.one_lt_q
  have hp_le_pm : p ≤ p * q := Nat.le_mul_of_pos_right p hqpos
  exact Nat.lt_of_lt_of_le hb.one_lt_p hp_le_pm

theorem positive_of_coprime_mul_validBases
    {p q D : Nat}
    (hb : ValidBases p q)
    (hD : Nat.Coprime D (p * q)) :
    0 < D := by
  by_cases hzero : D = 0
  · subst D
    rw [Nat.Coprime, Nat.gcd_zero_left] at hD
    have hpq_gt : 1 < p * q := validBases_mul_gt_one hb
    rw [hD] at hpq_gt
    exact False.elim ((Nat.lt_irrefl 1) hpq_gt)
  · exact Nat.pos_of_ne_zero hzero

def SupportCoprimeWithin (u v : Nat) : Prop :=
  ∀ D : Nat, Nat.Coprime D v → Nat.Coprime u D

structure GoodSeed (p q c : Nat) : Prop where
  c_pos : 0 < c
  c_lt : c < p - 1
  nonrep : Nonrepresentable p q c
  coprime_pq : Nat.Coprime c (p * q)
  support_succ : SupportCoprimeWithin (c + 1) (p * q)

def FreshExtension (p q D N : Nat) : Prop :=
  1 < N ∧ Nonrepresentable p q N ∧ Nat.Coprime N (p * q) ∧ Nat.Coprime N D

def FreshExtensionProvider (p q _c : Nat) : Prop :=
  ∀ D : Nat, Nat.Coprime D (p * q) → ∃ N : Nat, FreshExtension p q D N

def CongruentExtension (p q c D N : Nat) : Prop :=
  1 < N ∧
  Nonrepresentable p q N ∧
  Nat.Coprime N (p * q) ∧
  ∃ k : Nat, N = (c + 1) + D * k

def CongruentExtensionProvider (p q c : Nat) : Prop :=
  ∀ D : Nat, Nat.Coprime D (p * q) → ∃ N : Nat, CongruentExtension p q c D N

def CoprimeBasePeriodProvider (b : Nat) : Prop :=
  ∀ D : Nat, Nat.Coprime b D →
    ∃ L : Nat, 0 < L ∧ ∃ r : Nat, b ^ L = 1 + D * r

def BasicPeriodProvider (p q : Nat) : Prop :=
  ∀ D : Nat, Nat.Coprime D (p * q) →
    ∃ L : Nat,
      0 < L ∧
      (∃ r : Nat, p ^ L = 1 + D * r) ∧
      (∃ r : Nat, q ^ L = 1 + D * r)

def PeriodProvider (p q : Nat) : Prop :=
  ∀ D : Nat, Nat.Coprime D (p * q) →
    ∃ L : Nat,
      0 < L ∧
      (∀ a : Nat, L ∣ a → ∃ r : Nat, p ^ a = 1 + D * r) ∧
      (∀ M : Nat, L ∣ M → ∃ r : Nat, q ^ M = 1 + D * r)

def PowerWindowProvider (p q c : Nat) : Prop :=
  ∀ L : Nat, 0 < L →
    ∃ a M : Nat,
      0 < a ∧ 0 < M ∧
      L ∣ a ∧ L ∣ M ∧
      p ^ a < q ^ M ∧
      c * q ^ M < (p - 1) * p ^ a

def LowRowSyncProvider (p q : Nat) : Prop :=
  ∀ a M : Nat, ∀ A : List Point,
    1 < p →
    1 < q →
    Nat.Coprime p q →
    0 < M →
    p ^ a < q ^ M →
    IsAntichain A →
    (∀ x, x ∈ A → x.1 ≤ a) →
    (∀ x, x ∈ A → x.2 < M) →
    (∃ u v : Nat, SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) →
      A = [(a, 0)]

def LowRowResidualProvider (p q : Nat) : Prop :=
  ∀ a M : Nat, ∀ A : List Point, ∀ t : Nat,
    1 < p →
    1 < q →
    Nat.Coprime p q →
    0 < M →
    p ^ a < q ^ M →
    IsAntichain A →
    (∀ x, x ∈ A → x.1 ≤ a) →
    (∀ x, x ∈ A → x.2 < M) →
    (t, 0) ∈ A →
    t < a →
    (∃ u v : Nat, SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) →
      False

end Apiros1110

end

-- ===== source module Apiros1110.Period =====

section

/-
# Finite-period providers
-/

namespace Apiros1110

theorem exists_duplicate_get_of_not_nodup {α : Type} :
    ∀ (l : List α), ¬ l.Nodup →
      ∃ i j : Fin l.length, i ≠ j ∧ l.get i = l.get j
  | [], hnot => by
      exact False.elim (hnot List.nodup_nil)
  | a :: as, hnot => by
      by_cases ha : a ∈ as
      · rcases List.get_of_mem ha with ⟨j, hj⟩
        refine ⟨0, j.succ, ?_, ?_⟩
        · intro hzero
          exact Fin.succ_ne_zero j hzero.symm
        · simpa [List.get_eq_getElem] using hj.symm
      · have hnot_as : ¬ as.Nodup := by
          intro has
          exact hnot ((List.nodup_cons).mpr ⟨ha, has⟩)
        rcases exists_duplicate_get_of_not_nodup as hnot_as with
          ⟨i, j, hij, hget⟩
        refine ⟨i.succ, j.succ, ?_, ?_⟩
        · intro hs
          exact hij ((Fin.succ_inj).mp hs)
        · simpa [List.get_eq_getElem] using hget

theorem not_mem_erase_self_of_nodup {α : Type} [BEq α] [LawfulBEq α]
    {a : α} : ∀ {l : List α}, l.Nodup → ¬ a ∈ l.erase a
  | [], _ => by
      simp [List.erase]
  | x :: xs, hnod => by
      by_cases hxa : x = a
      · subst x
        rw [List.erase_cons_head]
        exact (List.nodup_cons.mp hnod).1
      · have hb : ¬ (x == a) = true := by
          intro hbtrue
          exact hxa ((beq_iff_eq.mp hbtrue))
        rw [List.erase_cons_tail hb]
        intro hmem
        cases List.mem_cons.mp hmem with
        | inl hx =>
            exact hxa hx.symm
        | inr htail =>
            exact not_mem_erase_self_of_nodup (List.nodup_cons.mp hnod).2 htail

theorem nodup_length_le_of_all_lt :
    ∀ (D : Nat) (l : List Nat), l.Nodup →
      (∀ x, x ∈ l → x < D) → l.length ≤ D
  | 0, [], _hnod, _hall => by
      simp
  | 0, x :: _xs, _hnod, hall => by
      have hx : x < 0 := hall x List.mem_cons_self
      omega
  | D + 1, l, hnod, hall => by
      by_cases hDmem : D ∈ l
      · have hnod_erase : (l.erase D).Nodup := List.Nodup.erase D hnod
        have hall_erase : ∀ x, x ∈ l.erase D → x < D := by
          intro x hx
          have hx_l : x ∈ l := List.mem_of_mem_erase hx
          have hx_lt_succ : x < D + 1 := hall x hx_l
          have hx_ne : x ≠ D := by
            intro hxeq
            subst x
            exact not_mem_erase_self_of_nodup hnod hx
          omega
        have hle : (l.erase D).length ≤ D :=
          nodup_length_le_of_all_lt D (l.erase D) hnod_erase hall_erase
        have hlen_eq : (l.erase D).length = l.length - 1 :=
          List.length_erase_of_mem hDmem
        have hlen_pos : 0 < l.length := List.length_pos_of_mem hDmem
        omega
      · have hall_lt : ∀ x, x ∈ l → x < D := by
          intro x hx
          have hx_lt_succ : x < D + 1 := hall x hx
          have hx_ne : x ≠ D := by
            intro hxeq
            subst x
            exact hDmem hx
          omega
        have hle : l.length ≤ D :=
          nodup_length_le_of_all_lt D l hnod hall_lt
        omega

theorem exists_duplicate_get_of_length_gt_bound
    {D : Nat} {l : List Nat}
    (hlen : D < l.length)
    (hall : ∀ x, x ∈ l → x < D) :
    ∃ i j : Fin l.length, i ≠ j ∧ l.get i = l.get j := by
  by_cases hnod : l.Nodup
  · have hle : l.length ≤ D := nodup_length_le_of_all_lt D l hnod hall
    omega
  · exact exists_duplicate_get_of_not_nodup l hnod

theorem get_power_residues {b D : Nat}
    (i : Fin ((List.range (D + 1)).map (fun n => b ^ n % D)).length) :
    ((List.range (D + 1)).map (fun n => b ^ n % D)).get i = b ^ i.1 % D := by
  rw [List.get_eq_getElem]
  rw [List.getElem_map]
  rw [List.getElem_range]

theorem exists_power_mod_repeat
    {b D : Nat} (hDpos : 0 < D) :
    ∃ i j : Nat, i < j ∧ j ≤ D ∧ b ^ i % D = b ^ j % D := by
  let residues := (List.range (D + 1)).map (fun n => b ^ n % D)
  have hlen : residues.length = D + 1 := by
    simp [residues, List.length_map, List.length_range]
  have hall : ∀ x, x ∈ residues → x < D := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨n, _hn, hnx⟩
    subst x
    exact Nat.mod_lt _ hDpos
  have hgt : D < residues.length := by
    omega
  rcases exists_duplicate_get_of_length_gt_bound hgt hall with ⟨i, j, hij, hget⟩
  have hi_get : residues.get i = b ^ i.1 % D := by
    simp [residues]
  have hj_get : residues.get j = b ^ j.1 % D := by
    simp [residues]
  have hmod : b ^ i.1 % D = b ^ j.1 % D := by
    rw [← hi_get, ← hj_get]
    exact hget
  have hval_ne : i.1 ≠ j.1 := by
    intro hval
    exact hij (Fin.ext hval)
  cases Nat.lt_or_gt_of_ne hval_ne with
  | inl hlt =>
      refine ⟨i.1, j.1, hlt, ?_, hmod⟩
      have hj_lt : j.1 < D + 1 := by omega
      omega
  | inr hgtij =>
      refine ⟨j.1, i.1, hgtij, ?_, hmod.symm⟩
      have hi_lt : i.1 < D + 1 := by omega
      omega

theorem dvd_sub_of_mod_eq_of_le {D x y : Nat}
    (hyx : y ≤ x) (hmod : x % D = y % D) :
    D ∣ x - y := by
  rcases Nat.mod_eq_mod_iff.mp hmod with ⟨k1, k2, h⟩
  rcases Nat.exists_eq_add_of_le hyx with ⟨t, ht⟩
  subst x
  have hcancel : t + k1 * D = k2 * D := by
    omega
  have ht_eq : t = k2 * D - k1 * D := Nat.eq_sub_of_add_eq hcancel
  refine ⟨k2 - k1, ?_⟩
  rw [Nat.add_sub_cancel_left]
  rw [ht_eq]
  rw [← Nat.mul_sub_right_distrib]
  rw [Nat.mul_comm]

theorem one_plus_mul_of_dvd_sub_one {D x : Nat}
    (hx : 1 ≤ x) (hdiv : D ∣ x - 1) :
    ∃ r : Nat, x = 1 + D * r := by
  rcases hdiv with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  have hx_eq : x = D * r + 1 := (Nat.sub_eq_iff_eq_add hx).mp hr
  rw [hx_eq, Nat.add_comm]

theorem dvd_pow_period_sub_one_of_mod_repeat
    {b D i j : Nat}
    (hcop : Nat.Coprime b D)
    (hbpos : 0 < b)
    (hij : i < j)
    (hmod : b ^ i % D = b ^ j % D) :
    D ∣ b ^ (j - i) - 1 := by
  have hile : i ≤ j := Nat.le_of_lt hij
  have hpow_le : b ^ i ≤ b ^ j := Nat.pow_le_pow_right hbpos hile
  have hdiv_diff : D ∣ b ^ j - b ^ i :=
    dvd_sub_of_mod_eq_of_le hpow_le hmod.symm
  have hdiff_eq : b ^ j - b ^ i = b ^ i * (b ^ (j - i) - 1) := by
    have hpow : b ^ (j - i) * b ^ i = b ^ j := Nat.pow_sub_mul_pow b hile
    calc
      b ^ j - b ^ i = b ^ (j - i) * b ^ i - 1 * b ^ i := by
        rw [hpow, Nat.one_mul]
      _ = (b ^ (j - i) - 1) * b ^ i := by
        rw [← Nat.mul_sub_right_distrib]
      _ = b ^ i * (b ^ (j - i) - 1) := by
        rw [Nat.mul_comm]
  rw [hdiff_eq] at hdiv_diff
  have hcop_factor : Nat.Coprime D (b ^ i) := hcop.symm.pow_right i
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop_factor hdiv_diff

theorem coprimeBasePeriodProvider_of_pos {b : Nat}
    (hbpos : 0 < b) :
    CoprimeBasePeriodProvider b := by
  intro D hcop
  by_cases hDzero : D = 0
  · subst D
    have hb_eq_one : b = 1 := by
      rw [Nat.Coprime, Nat.gcd_zero_right] at hcop
      exact hcop
    subst b
    exact ⟨1, by decide, ⟨0, by simp⟩⟩
  · by_cases hDone : D = 1
    · subst D
      refine ⟨1, by decide, ⟨b - 1, ?_⟩⟩
      simp
      omega
    · have hDpos : 0 < D := Nat.pos_of_ne_zero hDzero
      rcases exists_power_mod_repeat (b := b) (D := D) hDpos with
        ⟨i, j, hij, _hjD, hmod⟩
      let L := j - i
      have hLpos : 0 < L := Nat.sub_pos_of_lt hij
      have hdiv : D ∣ b ^ L - 1 := by
        dsimp [L]
        exact dvd_pow_period_sub_one_of_mod_repeat hcop hbpos hij hmod
      have hone : 1 ≤ b ^ L := Nat.one_le_pow L b hbpos
      rcases one_plus_mul_of_dvd_sub_one hone hdiv with ⟨r, hr⟩
      exact ⟨L, hLpos, ⟨r, hr⟩⟩

theorem pow_one_plus_mul_congruent
    {D r k : Nat} :
    ∃ s : Nat, (1 + D * r) ^ k = 1 + D * s := by
  induction k with
  | zero =>
      exact ⟨0, by simp⟩
  | succ k ih =>
      rcases ih with ⟨s, hs⟩
      refine ⟨r + s + D * r * s, ?_⟩
      rw [Nat.pow_succ, hs]
      simp [Nat.mul_add, Nat.add_mul]
      ac_rfl

theorem period_all_multiples_of_basic
    {b D L : Nat}
    (hL : ∃ r : Nat, b ^ L = 1 + D * r) :
    ∀ a : Nat, L ∣ a → ∃ r : Nat, b ^ a = 1 + D * r := by
  intro a hdiv
  rcases hdiv with ⟨k, hk⟩
  rcases hL with ⟨r, hr⟩
  rcases pow_one_plus_mul_congruent (D := D) (r := r) (k := k) with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rw [hk, Nat.pow_mul, hr]
  exact hs

theorem periodProvider_of_basicPeriodProvider
    {p q : Nat}
    (basic : BasicPeriodProvider p q) :
    PeriodProvider p q := by
  intro D hD
  rcases basic D hD with ⟨L, hLpos, hpL, hqL⟩
  exact ⟨L, hLpos,
    period_all_multiples_of_basic hpL,
    period_all_multiples_of_basic hqL⟩

theorem basicPeriodProvider_of_coprimeBasePeriodProviders
    {p q : Nat}
    (p_period : CoprimeBasePeriodProvider p)
    (q_period : CoprimeBasePeriodProvider q) :
    BasicPeriodProvider p q := by
  intro D hD
  have hDp : Nat.Coprime D p := (Nat.coprime_mul_iff_right.mp hD).1
  have hDq : Nat.Coprime D q := (Nat.coprime_mul_iff_right.mp hD).2
  rcases p_period D hDp.symm with ⟨Lp, hLp_pos, hpLp⟩
  rcases q_period D hDq.symm with ⟨Lq, hLq_pos, hqLq⟩
  refine ⟨Lp * Lq, Nat.mul_pos hLp_pos hLq_pos, ?_, ?_⟩
  · exact period_all_multiples_of_basic hpLp (Lp * Lq) ⟨Lq, rfl⟩
  · exact period_all_multiples_of_basic hqLq (Lp * Lq)
      ⟨Lp, Nat.mul_comm Lp Lq⟩

theorem basicPeriodProvider_of_pos
    {p q : Nat}
    (hp_pos : 0 < p)
    (hq_pos : 0 < q) :
    BasicPeriodProvider p q :=
  basicPeriodProvider_of_coprimeBasePeriodProviders
    (coprimeBasePeriodProvider_of_pos hp_pos)
    (coprimeBasePeriodProvider_of_pos hq_pos)

theorem periodProvider_of_coprimeBasePeriodProviders
    {p q : Nat}
    (p_period : CoprimeBasePeriodProvider p)
    (q_period : CoprimeBasePeriodProvider q) :
    PeriodProvider p q :=
  periodProvider_of_basicPeriodProvider
    (basicPeriodProvider_of_coprimeBasePeriodProviders p_period q_period)

theorem periodProvider_of_pos
    {p q : Nat}
    (hp_pos : 0 < p)
    (hq_pos : 0 < q) :
    PeriodProvider p q :=
  periodProvider_of_basicPeriodProvider
    (basicPeriodProvider_of_pos hp_pos hq_pos)

end Apiros1110

end

-- ===== source module Apiros1110.LowRowResidual =====

section

/-
# Low-row residual induction
-/

namespace Apiros1110

def firstGE (i : Nat) (A : List Point) : List Point :=
  A.filter (fun x => decide (i ≤ x.1))

def firstGT (i : Nat) (A : List Point) : List Point :=
  A.filter (fun x => decide (i < x.1))

def firstLT (i : Nat) (A : List Point) : List Point :=
  A.filter (fun x => decide (x.1 < i))

def firstEQ (i : Nat) (A : List Point) : List Point :=
  A.filter (fun x => decide (x.1 = i))

theorem mem_firstLT
    {i : Nat} {A : List Point} {x : Point}
    (hx : x ∈ firstLT i A) :
    x.1 < i :=
  of_decide_eq_true (List.mem_filter.mp hx).2

theorem firstGE_eq_firstEQ_add_firstGT_sum
    (p q i : Nat) :
    ∀ A : List Point,
      SumTerms p q (firstGE i A) =
        SumTerms p q (firstEQ i A) + SumTerms p q (firstGT i A)
  | [] => by
      simp [SumTerms, firstGE, firstEQ, firstGT]
  | x :: xs => by
      have ih := firstGE_eq_firstEQ_add_firstGT_sum p q i xs
      dsimp [SumTerms, firstGE, firstEQ, firstGT] at ih ⊢
      by_cases hlt : i < x.1
      · have hge : i ≤ x.1 := Nat.le_of_lt hlt
        have hne : ¬ x.1 = i := by
          intro h
          rw [h] at hlt
          exact (Nat.lt_irrefl i) hlt
        simp [hge, hlt, hne]
        rw [ih]
        ac_rfl
      · by_cases heq : x.1 = i
        · have _hge : i ≤ x.1 := by
            rw [heq]
          simp [heq]
          rw [ih]
          ac_rfl
        · have hge_not : ¬ i ≤ x.1 := by
            intro hge
            have hle : x.1 ≤ i := Nat.le_of_not_gt hlt
            have hxeq : x.1 = i := Nat.le_antisymm hle hge
            exact heq hxeq
          simp [hge_not, hlt, heq]
          exact ih

theorem sumTerms_firstGE_zero
    (p q : Nat) (A : List Point) :
    SumTerms p q (firstGE 0 A) = SumTerms p q A := by
  induction A with
  | nil =>
      simp [SumTerms, firstGE]
  | cons x xs ih =>
      dsimp [SumTerms, firstGE] at ih ⊢
      simp

theorem sumTerms_firstGE_add_firstLT
    (p q i : Nat) :
    ∀ A : List Point,
      SumTerms p q A =
        SumTerms p q (firstGE i A) + SumTerms p q (firstLT i A)
  | [] => by
      simp [SumTerms, firstGE, firstLT]
  | x :: xs => by
      have ih := sumTerms_firstGE_add_firstLT p q i xs
      dsimp [SumTerms, firstGE, firstLT] at ih ⊢
      by_cases hge : i ≤ x.1
      · have hnlt : ¬ x.1 < i := Nat.not_lt_of_ge hge
        simp [hge, hnlt]
        rw [ih]
        ac_rfl
      · have hlt : x.1 < i := Nat.lt_of_not_ge hge
        simp [hge, hlt]
        rw [ih]
        ac_rfl

theorem sumTerms_firstGE_succ_eq_firstGT
    (p q i : Nat) :
    ∀ A : List Point,
      SumTerms p q (firstGE (i + 1) A) = SumTerms p q (firstGT i A)
  | [] => by
      simp [SumTerms, firstGE, firstGT]
  | x :: xs => by
      have ih := sumTerms_firstGE_succ_eq_firstGT p q i xs
      dsimp [SumTerms, firstGE, firstGT] at ih ⊢
      by_cases hx : i < x.1
      · have hs : i + 1 ≤ x.1 := Nat.succ_le_of_lt hx
        simp [hx, hs]
      · have hs : ¬ i + 1 ≤ x.1 := by
          intro h
          exact hx (Nat.lt_of_succ_le h)
        simp [hx, hs]

theorem firstEQ_eq_singleton_of_antichain
    {i : Nat} {A : List Point} {x : Point}
    (hA : IsAntichain A)
    (hx : x ∈ A)
    (hxfirst : x.1 = i) :
    firstEQ i A = [x] := by
  dsimp [firstEQ]
  apply filter_eq_singleton_of_unique
  · exact hA.1
  · exact hx
  · exact decide_eq_true hxfirst
  · intro y hy hyP
    have hyfirst : y.1 = i := of_decide_eq_true hyP
    exact antichain_same_first_eq hA hy hx (hyfirst.trans hxfirst.symm)

theorem firstEQ_eq_nil_of_no_first
    {i : Nat} {A : List Point}
    (hno : ∀ x, x ∈ A → x.1 ≠ i) :
    firstEQ i A = [] := by
  dsimp [firstEQ]
  apply filter_eq_nil_of_forall_not
  intro x hx hP
  exact hno x hx (of_decide_eq_true hP)

theorem firstGE_eq_nil_of_zero_before
    {a t : Nat} {A : List Point}
    (hA : IsAntichain A)
    (hcol : ∀ x, x ∈ A → x.1 ≤ a)
    (hzero : (t, 0) ∈ A)
    (ht : t < a) :
    firstGE a A = [] := by
  dsimp [firstGE]
  apply filter_eq_nil_of_forall_not
  intro x hx hP
  have hage : a ≤ x.1 := of_decide_eq_true hP
  have hxa : x.1 = a := Nat.le_antisymm (hcol x hx) hage
  have hx_ne_zero : x ≠ (t, 0) := by
    intro h
    have hfirst : x.1 = t := by rw [h]
    rw [hxa] at hfirst
    rw [hfirst] at ht
    exact (Nat.lt_irrefl t) ht
  have hcoord : CoordLe (t, 0) x := by
    constructor
    · rw [hxa]
      exact Nat.le_of_lt ht
    · exact Nat.zero_le x.2
  exact hA.2 hzero hx (fun h => hx_ne_zero h.symm) hcoord

def ResidualInvariant (p q a : Nat) (A : List Point) (i : Nat) : Prop :=
  ∃ X : Nat, 0 < X ∧ p ^ i * X + SumTerms p q (firstGE i A) = p ^ a

theorem residualInvariant_top
    {p q a t : Nat} {A : List Point}
    (hA : IsAntichain A)
    (hcol : ∀ x, x ∈ A → x.1 ≤ a)
    (hzero : (t, 0) ∈ A)
    (ht : t < a) :
    ResidualInvariant p q a A a := by
  refine ⟨1, by decide, ?_⟩
  rw [firstGE_eq_nil_of_zero_before hA hcol hzero ht]
  simp [SumTerms]

theorem residualInvariant_step_empty
    {p q a i : Nat} {A : List Point}
    (hp_pos : 0 < p)
    (hinv : ResidualInvariant p q a A (i + 1))
    (hno : ∀ x, x ∈ A → x.1 ≠ i) :
    ResidualInvariant p q a A i := by
  rcases hinv with ⟨X, hXpos, hEq⟩
  refine ⟨p * X, ?_, ?_⟩
  · exact Nat.mul_pos hp_pos hXpos
  · have hEqCol : firstEQ i A = [] := firstEQ_eq_nil_of_no_first hno
    have hsplit := firstGE_eq_firstEQ_add_firstGT_sum p q i A
    have hsucc := sumTerms_firstGE_succ_eq_firstGT p q i A
    calc
      p ^ i * (p * X) + SumTerms p q (firstGE i A)
          = p ^ (i + 1) * X + SumTerms p q (firstGE (i + 1) A) := by
              rw [hsplit, hEqCol, hsucc]
              simp [SumTerms]
              rw [Nat.pow_succ]
              ac_rfl
      _ = p ^ a := hEq

theorem qpow_dvd_sumTerms_firstLT_of_selected
    {p q i j : Nat} {A : List Point}
    (hA : IsAntichain A)
    (hx : (i, j) ∈ A) :
    q ^ j ∣ SumTerms p q (firstLT i A) := by
  apply qpow_dvd_sumTerms_of_all_second_ge
  intro y hy
  have hyA : y ∈ A := (List.mem_filter.mp hy).1
  have hylt : y.1 < i := mem_firstLT hy
  have hsecond : j < y.2 := by
    have hstrict := antichain_second_strictAnti_of_first_lt hA hyA hx hylt
    simpa using hstrict
  exact Nat.le_of_lt hsecond

theorem qpow_dvd_qpow_mul_of_le
    {q j M u : Nat}
    (hle : j ≤ M) :
    q ^ j ∣ q ^ M * u := by
  have hpow : q ^ j ∣ q ^ M := Nat.pow_dvd_pow q hle
  exact Nat.dvd_trans hpow (Nat.dvd_mul_right _ _)

theorem residualInvariant_step_selected
    {p q a M i j : Nat} {A : List Point}
    (hp : 1 < p)
    (_hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (hA : IsAntichain A)
    (hrow : ∀ x, x ∈ A → x.2 < M)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v)
    (hinv : ResidualInvariant p q a A (i + 1))
    (hx : (i, j) ∈ A) :
    ResidualInvariant p q a A i := by
  rcases hinv with ⟨X, hXpos, hEq⟩
  have hp_pos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hjM : j < M := hrow (i, j) hx
  have hjleM : j ≤ M := Nat.le_of_lt hjM
  have hEqCol : firstEQ i A = [(i, j)] :=
    firstEQ_eq_singleton_of_antichain hA hx rfl
  have hsplitGE := firstGE_eq_firstEQ_add_firstGT_sum p q i A
  have hsucc := sumTerms_firstGE_succ_eq_firstGT p q i A
  have hSuffix :
      SumTerms p q (firstGE i A) =
        Term p q (i, j) + SumTerms p q (firstGE (i + 1) A) := by
    calc
      SumTerms p q (firstGE i A)
          = SumTerms p q (firstEQ i A) + SumTerms p q (firstGT i A) := hsplitGE
      _ = Term p q (i, j) + SumTerms p q (firstGE (i + 1) A) := by
          rw [hEqCol, ← hsucc]
          simp [SumTerms]
  have hAll :
      SumTerms p q A =
        SumTerms p q (firstGE (i + 1) A) +
          Term p q (i, j) + SumTerms p q (firstLT i A) := by
    have hsplitAll := sumTerms_firstGE_add_firstLT p q i A
    calc
      SumTerms p q A
          = SumTerms p q (firstGE i A) + SumTerms p q (firstLT i A) := hsplitAll
      _ = (Term p q (i, j) + SumTerms p q (firstGE (i + 1) A)) +
            SumTerms p q (firstLT i A) := by rw [hSuffix]
      _ = SumTerms p q (firstGE (i + 1) A) +
            Term p q (i, j) + SumTerms p q (firstLT i A) := by ac_rfl
  have hqj_dvd_term : q ^ j ∣ Term p q (i, j) :=
    qpow_dvd_term_of_second_ge (p := p) (q := q) (k := j) (x := (i, j))
      (Nat.le_refl j)
  have hqj_dvd_lower : q ^ j ∣ SumTerms p q (firstLT i A) :=
    qpow_dvd_sumTerms_firstLT_of_selected hA hx
  have hqj_dvd_X : q ^ j ∣ X := by
    rcases hcong with ⟨u, v, heq⟩
    have hqj_dvd_qMu : q ^ j ∣ q ^ M * u :=
      qpow_dvd_qpow_mul_of_le hjleM
    have hqj_dvd_qMv : q ^ j ∣ q ^ M * v :=
      qpow_dvd_qpow_mul_of_le hjleM
    have hcancel :
        Term p q (i, j) + SumTerms p q (firstLT i A) + q ^ M * u =
          p ^ (i + 1) * X + q ^ M * v := by
      have hbig :
          SumTerms p q (firstGE (i + 1) A) +
              (Term p q (i, j) + SumTerms p q (firstLT i A) + q ^ M * u) =
            SumTerms p q (firstGE (i + 1) A) +
              (p ^ (i + 1) * X + q ^ M * v) := by
        calc
          SumTerms p q (firstGE (i + 1) A) +
              (Term p q (i, j) + SumTerms p q (firstLT i A) + q ^ M * u)
              = SumTerms p q A + q ^ M * u := by
                  rw [hAll]
                  ac_rfl
          _ = p ^ a + q ^ M * v := heq
          _ = (p ^ (i + 1) * X + SumTerms p q (firstGE (i + 1) A)) +
                q ^ M * v := by rw [hEq]
          _ = SumTerms p q (firstGE (i + 1) A) +
                (p ^ (i + 1) * X + q ^ M * v) := by ac_rfl
      exact Nat.add_left_cancel hbig
    have hleft :
        q ^ j ∣ Term p q (i, j) + SumTerms p q (firstLT i A) + q ^ M * u :=
      Nat.dvd_add (Nat.dvd_add hqj_dvd_term hqj_dvd_lower) hqj_dvd_qMu
    have hright :
        q ^ j ∣ p ^ (i + 1) * X + q ^ M * v := by
      rwa [hcancel] at hleft
    have hpX : q ^ j ∣ p ^ (i + 1) * X :=
      (Nat.dvd_add_left hqj_dvd_qMv).mp hright
    have hcop : Nat.Coprime (q ^ j) (p ^ (i + 1)) :=
      (hpq.symm.pow_left j).pow_right (i + 1)
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop hpX
  have hqj_le_X : q ^ j ≤ X := Nat.le_of_dvd hXpos hqj_dvd_X
  have hX_lt_pX : X < p * X :=
    (Nat.lt_mul_iff_one_lt_left hXpos).2 hp
  have hqj_lt_pX : q ^ j < p * X :=
    Nat.lt_of_le_of_lt hqj_le_X hX_lt_pX
  have hqj_le_pX : q ^ j ≤ p * X := Nat.le_of_lt hqj_lt_pX
  refine ⟨p * X - q ^ j, Nat.sub_pos_of_lt hqj_lt_pX, ?_⟩
  have hmul_cancel :
      p ^ i * (p * X - q ^ j) + p ^ i * q ^ j = p ^ i * (p * X) := by
    rw [Nat.mul_sub_left_distrib]
    exact Nat.sub_add_cancel (Nat.mul_le_mul_left (p ^ i) hqj_le_pX)
  calc
    p ^ i * (p * X - q ^ j) + SumTerms p q (firstGE i A)
        = p ^ i * (p * X - q ^ j) +
            (Term p q (i, j) + SumTerms p q (firstGE (i + 1) A)) := by
            rw [hSuffix]
    _ = p ^ i * (p * X - q ^ j) +
          (p ^ i * q ^ j + SumTerms p q (firstGE (i + 1) A)) := by
            simp [Term]
    _ = (p ^ i * (p * X - q ^ j) + p ^ i * q ^ j) +
          SumTerms p q (firstGE (i + 1) A) := by ac_rfl
    _ = p ^ i * (p * X) + SumTerms p q (firstGE (i + 1) A) := by
            rw [hmul_cancel]
    _ = p ^ (i + 1) * X + SumTerms p q (firstGE (i + 1) A) := by
            rw [Nat.pow_succ]
            ac_rfl
    _ = p ^ a := hEq

theorem residualInvariant_zero_of_zero_before
    {p q a M t : Nat} {A : List Point}
    (hp : 1 < p)
    (hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (hA : IsAntichain A)
    (hcol : ∀ x, x ∈ A → x.1 ≤ a)
    (hrow : ∀ x, x ∈ A → x.2 < M)
    (hzero : (t, 0) ∈ A)
    (ht : t < a)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    ResidualInvariant p q a A 0 := by
  have hp_pos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hdesc :
      ∀ n : Nat, n ≤ a → ResidualInvariant p q a A (a - n) := by
    intro n hn
    induction n with
    | zero =>
        simpa using residualInvariant_top (p := p) (q := q)
          hA hcol hzero ht
    | succ n ih =>
        have hnle : n ≤ a := by omega
        have hprev : ResidualInvariant p q a A (a - n) := ih hnle
        have hidx : a - (n + 1) + 1 = a - n := by omega
        have hprev' :
            ResidualInvariant p q a A ((a - (n + 1)) + 1) := by
          simpa [hidx] using hprev
        by_cases hex : ∃ x, x ∈ A ∧ x.1 = a - (n + 1)
        · rcases hex with ⟨x, hxA, hxfirst⟩
          cases x with
          | mk xi j =>
              dsimp at hxfirst
              rw [hxfirst] at hxA
              exact residualInvariant_step_selected
                (p := p) (q := q) (a := a) (M := M)
                (i := a - (n + 1)) (j := j) hp hq hpq hA hrow hcong hprev' hxA
        · apply residualInvariant_step_empty (p := p) (q := q)
            (a := a) (i := a - (n + 1)) (A := A) hp_pos hprev'
          intro x hxA hxfirst
          exact hex ⟨x, hxA, hxfirst⟩
  simpa using hdesc a (Nat.le_refl a)

theorem false_of_zero_before_of_lowrow_congruence
    {p q a M t : Nat} {A : List Point}
    (hp : 1 < p)
    (hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (hpow : p ^ a < q ^ M)
    (hA : IsAntichain A)
    (hcol : ∀ x, x ∈ A → x.1 ≤ a)
    (hrow : ∀ x, x ∈ A → x.2 < M)
    (hzero : (t, 0) ∈ A)
    (ht : t < a)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    False := by
  rcases residualInvariant_zero_of_zero_before
      hp hq hpq hA hcol hrow hzero ht hcong with
    ⟨X, hXpos, hEq0⟩
  have hfirstGE0 := sumTerms_firstGE_zero p q A
  have hXS : X + SumTerms p q A = p ^ a := by
    simpa [hfirstGE0] using hEq0
  have hX_le_pa : X ≤ p ^ a := by
    rw [← hXS]
    exact Nat.le_add_right X (SumTerms p q A)
  have hX_lt_qM : X < q ^ M := Nat.lt_of_le_of_lt hX_le_pa hpow
  have hqM_dvd_X : q ^ M ∣ X := by
    rcases hcong with ⟨u, v, heq⟩
    have hcancel : q ^ M * u = X + q ^ M * v := by
      have hbig :
          SumTerms p q A + q ^ M * u =
            SumTerms p q A + (X + q ^ M * v) := by
        calc
          SumTerms p q A + q ^ M * u
              = p ^ a + q ^ M * v := heq
          _ = (X + SumTerms p q A) + q ^ M * v := by rw [hXS]
          _ = SumTerms p q A + (X + q ^ M * v) := by ac_rfl
      exact Nat.add_left_cancel hbig
    have hdiv : q ^ M ∣ X + q ^ M * v := by
      rw [← hcancel]
      exact Nat.dvd_mul_right _ _
    exact (Nat.dvd_add_left (Nat.dvd_mul_right _ _)).mp hdiv
  exact (Nat.not_dvd_of_pos_of_lt hXpos hX_lt_qM) hqM_dvd_X

theorem lowRowResidualProvider_core
    {p q : Nat} :
    LowRowResidualProvider p q := by
  intro a M A t hp hq hpq _hM hpow hA hcol hrow hzero ht hcong
  exact false_of_zero_before_of_lowrow_congruence
    hp hq hpq hpow hA hcol hrow hzero ht hcong

end Apiros1110

end

-- ===== source module Apiros1110.Embedding =====

section

/-
# Embedding providers
-/

namespace Apiros1110

def EmbeddingNonrepProvider (p q c : Nat) : Prop :=
  ∀ a M : Nat,
    0 < a → 0 < M →
    p ^ a < q ^ M →
    c * q ^ M < (p - 1) * p ^ a →
      Nonrepresentable p q (p ^ a + c * q ^ M)

def EmbeddingCoprimeProvider (p q c : Nat) : Prop :=
  ∀ a M : Nat,
    0 < a → 0 < M →
    p ^ a < q ^ M →
    c * q ^ M < (p - 1) * p ^ a →
      Nat.Coprime (p ^ a + c * q ^ M) (p * q)

def EmbeddingProvider (p q c : Nat) : Prop :=
  ∀ a M : Nat,
    0 < a → 0 < M →
    p ^ a < q ^ M →
    c * q ^ M < (p - 1) * p ^ a →
      Nonrepresentable p q (p ^ a + c * q ^ M) ∧
      Nat.Coprime (p ^ a + c * q ^ M) (p * q)

def PeriodWindowEmbeddingAmplification : Prop :=
  ∀ ⦃p q c : Nat⦄,
    ValidBases p q → GoodSeed p q c →
      PeriodProvider p q ∧ PowerWindowProvider p q c ∧ EmbeddingProvider p q c

def PeriodWindowAmplification : Prop :=
  ∀ ⦃p q c : Nat⦄,
    ValidBases p q → GoodSeed p q c →
      PeriodProvider p q ∧ PowerWindowProvider p q c

def WindowAmplification : Prop :=
  ∀ ⦃p q c : Nat⦄,
    ValidBases p q → GoodSeed p q c →
      PowerWindowProvider p q c

def PeriodWindowLowRowAmplification : Prop :=
  ∀ ⦃p q c : Nat⦄,
    ValidBases p q → GoodSeed p q c →
      PeriodProvider p q ∧ PowerWindowProvider p q c ∧ LowRowSyncProvider p q

def FreshExtensionAmplification : Prop :=
  ∀ ⦃p q c : Nat⦄,
    ValidBases p q → GoodSeed p q c → FreshExtensionProvider p q c

def GoodSeedAmplification : Prop :=
  ∀ ⦃p q c : Nat⦄,
    ValidBases p q → GoodSeed p q c →
      ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq p q f

theorem lowRowSyncProvider_of_residual
    {p q : Nat}
    (residual : LowRowResidualProvider p q) :
    LowRowSyncProvider p q := by
  intro a M A hp hq hpq hM hpow hA hcol hrow hcong
  rcases exists_unique_second_zero_of_lowrow_congruence hq hpq hM hA hcong with
    ⟨x, hxA, hx0, huniq⟩
  cases x with
  | mk t j =>
      dsimp at hx0 huniq hxA hcol hrow
      subst j
      by_cases hta : t = a
      · subst t
        have huniq_zero : ∀ y, y ∈ A → y.2 = 0 → y = (a, 0) := by
          intro y hy hy0
          exact huniq y hy hy0
        exact eq_singleton_of_zero_at_a_of_lowrow_congruence
          hq hpq hM hA hrow hxA huniq_zero hcong
      · have ht_le_a : t ≤ a := hcol (t, 0) hxA
        have ht_lt_a : t < a := Nat.lt_of_le_of_ne ht_le_a hta
        exact False.elim
          (residual a M A t hp hq hpq hM hpow hA hcol hrow hxA ht_lt_a hcong)

theorem lowRowSyncProvider_core
    {p q : Nat} :
    LowRowSyncProvider p q :=
  lowRowSyncProvider_of_residual lowRowResidualProvider_core

theorem embeddingProvider_of_nonrep_and_coprime
    {p q c : Nat}
    (hnrep : EmbeddingNonrepProvider p q c)
    (hcop : EmbeddingCoprimeProvider p q c) :
    EmbeddingProvider p q c := by
  intro a M ha hM hleft hright
  exact ⟨hnrep a M ha hM hleft hright, hcop a M ha hM hleft hright⟩

theorem embeddingNonrepProvider_of_lowRowSync
    {p q c : Nat}
    (hb : ValidBases p q)
    (sync : LowRowSyncProvider p q)
    (hc_nonrep : Nonrepresentable p q c) :
    EmbeddingNonrepProvider p q c := by
  intro a M ha hM hleft hright
  intro hrepr
  rcases hrepr with ⟨A, hA, hsum⟩
  have hp_pos : 0 < p := Nat.lt_trans Nat.zero_lt_one hb.one_lt_p
  have hq_pos : 0 < q := Nat.lt_trans Nat.zero_lt_one hb.one_lt_q
  have hNlt : p ^ a + c * q ^ M < p ^ (a + 1) :=
    embedded_lt_pow_succ hp_pos hright
  have hcolA : ∀ x, x ∈ A → x.1 ≤ a := by
    intro x hx
    have hx_le_sum : Term p q x ≤ SumTerms p q A := mem_term_le_sum hx
    have hx_lt : Term p q x < p ^ (a + 1) := by
      rw [hsum] at hx_le_sum
      exact Nat.lt_of_le_of_lt hx_le_sum hNlt
    exact first_coord_le_of_term_lt_pow_succ hb.one_lt_p hq_pos hx_lt
  let Low := lowRows M A
  let HighShift := shiftedHighRows M A
  have hlow_anti : IsAntichain Low := by
    dsimp [Low]
    exact lowRows_antichain hA M
  have hlow_col : ∀ x, x ∈ Low → x.1 ≤ a := by
    intro x hx
    exact hcolA x (List.mem_filter.mp hx).1
  have hlow_row : ∀ x, x ∈ Low → x.2 < M := by
    intro x hx
    exact mem_lowRows_lt hx
  have hcong : ∃ u v : Nat,
      SumTerms p q Low + q ^ M * u = p ^ a + q ^ M * v := by
    refine ⟨SumTerms p q HighShift, c, ?_⟩
    dsimp [Low, HighShift]
    have hsplit := sumTerms_lowRows_add_highRows p q M A
    have hfactor := highRows_sum_factor p q M A
    calc
      SumTerms p q (lowRows M A) + q ^ M * SumTerms p q (shiftedHighRows M A)
          = SumTerms p q (lowRows M A) + SumTerms p q (highRows M A) := by
              rw [hfactor]
      _ = SumTerms p q A := hsplit.symm
      _ = p ^ a + c * q ^ M := hsum
      _ = p ^ a + q ^ M * c := by rw [Nat.mul_comm c (q ^ M)]
  have hlow_eq : Low = [(a, 0)] :=
    sync a M Low hb.one_lt_p hb.one_lt_q hb.coprime hM
      hleft hlow_anti hlow_col hlow_row hcong
  have hhigh_sum_eq : SumTerms p q HighShift = c := by
    have hsplit := sumTerms_lowRows_add_highRows p q M A
    have hfactor := highRows_sum_factor p q M A
    dsimp [Low, HighShift] at hlow_eq ⊢
    have hmain :
        p ^ a + q ^ M * SumTerms p q (shiftedHighRows M A) =
          p ^ a + q ^ M * c := by
      calc
        p ^ a + q ^ M * SumTerms p q (shiftedHighRows M A)
            = SumTerms p q (lowRows M A) + q ^ M * SumTerms p q (shiftedHighRows M A) := by
                rw [hlow_eq]
                simp [SumTerms, Term]
        _ = SumTerms p q (lowRows M A) + SumTerms p q (highRows M A) := by
                rw [hfactor]
        _ = SumTerms p q A := hsplit.symm
        _ = p ^ a + c * q ^ M := hsum
        _ = p ^ a + q ^ M * c := by rw [Nat.mul_comm c (q ^ M)]
    have hcancel_add :
        q ^ M * SumTerms p q (shiftedHighRows M A) = q ^ M * c :=
      Nat.add_left_cancel hmain
    have hqM_pos : 0 < q ^ M := (Nat.pow_pos hq_pos : 0 < q ^ M)
    exact Nat.mul_left_cancel hqM_pos hcancel_add
  exact hc_nonrep ⟨HighShift, shiftedHighRows_antichain hA M, hhigh_sum_eq⟩

theorem embeddingProvider_of_lowRowSync_and_coprime
    {p q c : Nat}
    (hb : ValidBases p q)
    (sync : LowRowSyncProvider p q)
    (hc_nonrep : Nonrepresentable p q c)
    (hcop : EmbeddingCoprimeProvider p q c) :
    EmbeddingProvider p q c :=
  embeddingProvider_of_nonrep_and_coprime
    (embeddingNonrepProvider_of_lowRowSync hb sync hc_nonrep)
    hcop

theorem embeddingCoprimeProvider_of_goodSeed
    {p q c : Nat}
    (hb : ValidBases p q)
    (hs : GoodSeed p q c) :
    EmbeddingCoprimeProvider p q c := by
  intro a M ha hM _hleft _hright
  apply Nat.coprime_mul_iff_right.mpr
  constructor
  · have hc_p : Nat.Coprime c p :=
      (Nat.coprime_mul_iff_right.mp hs.coprime_pq).1
    have hqM_p : Nat.Coprime (q ^ M) p :=
      hb.coprime.symm.pow_left M
    have hprod_p : Nat.Coprime (c * q ^ M) p :=
      Nat.Coprime.mul_left hc_p hqM_p
    rw [Nat.coprime_iff_gcd_eq_one]
    have hpow : p ^ a = p * p ^ (a - 1) := by
      have hsucc : (a - 1).succ = a := Nat.succ_pred_eq_of_pos ha
      rw [← hsucc, Nat.pow_succ]
      ac_rfl
    rw [hpow]
    rw [Nat.add_comm]
    rw [Nat.gcd_add_mul_left_left]
    exact Nat.Coprime.gcd_eq_one hprod_p
  · have hpowa_q : Nat.Coprime (p ^ a) q :=
      hb.coprime.pow_left a
    rw [Nat.coprime_iff_gcd_eq_one]
    have hqpow : q ^ M = q * q ^ (M - 1) := by
      have hsucc : (M - 1).succ = M := Nat.succ_pred_eq_of_pos hM
      rw [← hsucc, Nat.pow_succ]
      ac_rfl
    rw [hqpow]
    have hmul : c * (q * q ^ (M - 1)) = q * (c * q ^ (M - 1)) := by
      ac_rfl
    rw [hmul]
    rw [Nat.gcd_add_mul_left_left]
    exact Nat.Coprime.gcd_eq_one hpowa_q

theorem embeddingProvider_of_lowRowSync
    {p q c : Nat}
    (hb : ValidBases p q)
    (hs : GoodSeed p q c)
    (sync : LowRowSyncProvider p q) :
    EmbeddingProvider p q c :=
  embeddingProvider_of_lowRowSync_and_coprime hb sync hs.nonrep
    (embeddingCoprimeProvider_of_goodSeed hb hs)

theorem embeddingProvider_core
    {p q c : Nat}
    (hb : ValidBases p q)
    (hs : GoodSeed p q c) :
    EmbeddingProvider p q c :=
  embeddingProvider_of_lowRowSync hb hs lowRowSyncProvider_core

end Apiros1110

end

-- ===== source module Apiros1110.Sequence =====

section

/-
# Infinite sequence construction, amplification bridges, and infinitude consequences
-/

namespace Apiros1110

abbrev PQCoprimeState (p q : Nat) :=
  {D : Nat // Nat.Coprime D (p * q)}

noncomputable def nextFresh
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (D : PQCoprimeState p q) : Nat :=
  Classical.choose (fresh D.1 D.2)

theorem nextFresh_spec
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (D : PQCoprimeState p q) :
    FreshExtension p q D.1 (nextFresh fresh D) :=
  Classical.choose_spec (fresh D.1 D.2)

theorem coprime_of_eq_seed_succ_add_mul
    {p q c D N k : Nat}
    (hs : GoodSeed p q c)
    (hD : Nat.Coprime D (p * q))
    (hN : N = (c + 1) + D * k) :
    Nat.Coprime N D := by
  have hseedD : Nat.Coprime (c + 1) D := hs.support_succ D hD
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [hN]
  rw [Nat.gcd_add_mul_left_left]
  exact Nat.Coprime.gcd_eq_one hseedD

theorem freshExtensionProvider_of_congruentExtensionProvider
    {p q c : Nat}
    (hs : GoodSeed p q c)
    (provider : CongruentExtensionProvider p q c) :
    FreshExtensionProvider p q c := by
  intro D hD
  rcases provider D hD with ⟨N, hN⟩
  rcases hN with ⟨hgt, hnrep, hcop_pq, k, hcong⟩
  exact ⟨N, hgt, hnrep, hcop_pq,
    coprime_of_eq_seed_succ_add_mul hs hD hcong⟩

theorem congruentExtensionProvider_of_period_window_embedding
    {p q c : Nat}
    (hb : ValidBases p q)
    (period : PeriodProvider p q)
    (window : PowerWindowProvider p q c)
    (embed : EmbeddingProvider p q c) :
    CongruentExtensionProvider p q c := by
  intro D hD
  rcases period D hD with ⟨L, hLpos, hp_period, hq_period⟩
  rcases window L hLpos with
    ⟨a, M, ha_pos, hM_pos, hLa, hLM, hleft, hright⟩
  let N := p ^ a + c * q ^ M
  have hemb := embed a M ha_pos hM_pos hleft hright
  rcases hp_period a hLa with ⟨rp, hp_cong⟩
  rcases hq_period M hLM with ⟨rq, hq_cong⟩
  refine ⟨N, ?_, ?_, ?_, rp + c * rq, ?_⟩
  · dsimp [N]
    have hpowa : 1 < p ^ a := Nat.one_lt_pow (Nat.ne_of_gt ha_pos) hb.one_lt_p
    exact Nat.lt_add_right (c * q ^ M) hpowa
  · simpa [N] using hemb.1
  · simpa [N] using hemb.2
  · dsimp [N]
    rw [hp_cong, hq_cong]
    simp [Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm]
    ac_rfl

theorem nextFresh_gt_one
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (D : PQCoprimeState p q) :
    1 < nextFresh fresh D :=
  (nextFresh_spec fresh D).1

theorem nextFresh_nonrep
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (D : PQCoprimeState p q) :
    Nonrepresentable p q (nextFresh fresh D) :=
  (nextFresh_spec fresh D).2.1

theorem nextFresh_coprime_pq
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (D : PQCoprimeState p q) :
    Nat.Coprime (nextFresh fresh D) (p * q) :=
  (nextFresh_spec fresh D).2.2.1

theorem nextFresh_coprime_state
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (D : PQCoprimeState p q) :
    Nat.Coprime (nextFresh fresh D) D.1 :=
  (nextFresh_spec fresh D).2.2.2

noncomputable def states
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c) :
    Nat → PQCoprimeState p q
  | 0 => ⟨1, Nat.coprime_one_left (p * q)⟩
  | n + 1 =>
      let D := states fresh n
      let N := nextFresh fresh D
      ⟨D.1 * N, Nat.Coprime.mul_left D.2 (nextFresh_coprime_pq fresh D)⟩

noncomputable def nonrepSeq
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) : Nat :=
  nextFresh fresh (states fresh n)

theorem nonrepSeq_gt_one
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    1 < nonrepSeq fresh n :=
  nextFresh_gt_one fresh (states fresh n)

theorem nonrepSeq_nonrep
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    Nonrepresentable p q (nonrepSeq fresh n) :=
  nextFresh_nonrep fresh (states fresh n)

theorem nonrepSeq_coprime_pq
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    Nat.Coprime (nonrepSeq fresh n) (p * q) :=
  nextFresh_coprime_pq fresh (states fresh n)

theorem nonrepSeq_coprime_state
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    Nat.Coprime (nonrepSeq fresh n) (states fresh n).1 :=
  nextFresh_coprime_state fresh (states fresh n)

theorem state_succ_val
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    (states fresh (n + 1)).1 = (states fresh n).1 * nonrepSeq fresh n := by
  rfl

theorem seq_dvd_state_succ
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    nonrepSeq fresh n ∣ (states fresh (n + 1)).1 := by
  rw [state_succ_val]
  exact Nat.dvd_mul_left _ _

theorem state_dvd_state_succ
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    (states fresh n).1 ∣ (states fresh (n + 1)).1 := by
  rw [state_succ_val]
  exact Nat.dvd_mul_right _ _

theorem seq_dvd_later_state
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c) :
    ∀ {m n : Nat}, m < n → nonrepSeq fresh m ∣ (states fresh n).1
  | m, 0, h => False.elim ((Nat.not_lt_zero m) h)
  | m, n + 1, h => by
      have hmle : m ≤ n := Nat.le_of_lt_succ h
      cases Nat.lt_or_eq_of_le hmle with
      | inl hmn =>
          have hdiv : nonrepSeq fresh m ∣ (states fresh n).1 :=
            seq_dvd_later_state fresh hmn
          exact Nat.dvd_trans hdiv (state_dvd_state_succ fresh n)
      | inr hmn =>
          subst m
          exact seq_dvd_state_succ fresh n

theorem nonrepSeq_pairwise_coprime
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c) :
    ∀ ⦃m n : Nat⦄, m ≠ n → Nat.Coprime (nonrepSeq fresh m) (nonrepSeq fresh n) := by
  intro m n hne
  cases Nat.lt_or_ge m n with
  | inl hmn =>
      have hdiv : nonrepSeq fresh m ∣ (states fresh n).1 :=
        seq_dvd_later_state fresh hmn
      have hcop : Nat.Coprime (nonrepSeq fresh n) (states fresh n).1 :=
        nonrepSeq_coprime_state fresh n
      exact Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right hdiv hcop)
  | inr hge =>
      have hnm : n < m := Nat.lt_of_le_of_ne hge (fun h => hne h.symm)
      have hdiv : nonrepSeq fresh n ∣ (states fresh m).1 :=
        seq_dvd_later_state fresh hnm
      have hcop : Nat.Coprime (nonrepSeq fresh m) (states fresh m).1 :=
        nonrepSeq_coprime_state fresh m
      exact Nat.Coprime.coprime_dvd_right hdiv hcop

theorem infinite_pairwise_nonrep_of_freshExtensionProvider
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq p q f := by
  refine ⟨nonrepSeq fresh, ?_, ?_⟩
  · intro n
    exact ⟨nonrepSeq_gt_one fresh n, nonrepSeq_nonrep fresh n,
      nonrepSeq_coprime_pq fresh n⟩
  · exact nonrepSeq_pairwise_coprime fresh

theorem goodSeedAmplification_of_congruentExtensionProvider
    {p q c : Nat}
    (_hb : ValidBases p q)
    (hs : GoodSeed p q c)
    (provider : CongruentExtensionProvider p q c) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq p q f :=
  infinite_pairwise_nonrep_of_freshExtensionProvider
    (freshExtensionProvider_of_congruentExtensionProvider hs provider)

theorem goodSeedAmplification_of_period_window_embedding
    {p q c : Nat}
    (hb : ValidBases p q)
    (hs : GoodSeed p q c)
    (period : PeriodProvider p q)
    (window : PowerWindowProvider p q c)
    (embed : EmbeddingProvider p q c) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq p q f :=
  goodSeedAmplification_of_congruentExtensionProvider hb hs
    (congruentExtensionProvider_of_period_window_embedding hb period window embed)

theorem goodSeedAmplification_of_window
    {p q c : Nat}
    (hb : ValidBases p q)
    (hs : GoodSeed p q c)
    (window : PowerWindowProvider p q c) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq p q f :=
  goodSeedAmplification_of_period_window_embedding hb hs
    (periodProvider_of_pos
      (Nat.lt_trans Nat.zero_lt_one hb.one_lt_p)
      (Nat.lt_trans Nat.zero_lt_one hb.one_lt_q))
    window
    (embeddingProvider_core hb hs)

theorem freshExtensionAmplification_of_periodWindowEmbeddingAmplification
    (amp : PeriodWindowEmbeddingAmplification) :
    FreshExtensionAmplification := by
  intro p q c hb hs
  rcases amp hb hs with ⟨period, window, embed⟩
  exact freshExtensionProvider_of_congruentExtensionProvider hs
    (congruentExtensionProvider_of_period_window_embedding hb period window embed)

theorem periodWindowEmbeddingAmplification_of_periodWindowAmplification
    (amp : PeriodWindowAmplification) :
    PeriodWindowEmbeddingAmplification := by
  intro p q c hb hs
  rcases amp hb hs with ⟨period, window⟩
  exact ⟨period, window, embeddingProvider_core hb hs⟩

theorem periodWindowAmplification_of_windowAmplification
    (amp : WindowAmplification) :
    PeriodWindowAmplification := by
  intro p q c hb hs
  exact ⟨periodProvider_of_pos
      (Nat.lt_trans Nat.zero_lt_one hb.one_lt_p)
      (Nat.lt_trans Nat.zero_lt_one hb.one_lt_q),
    amp hb hs⟩

theorem periodWindowLowRowAmplification_of_periodWindowAmplification
    (amp : PeriodWindowAmplification) :
    PeriodWindowLowRowAmplification := by
  intro p q c hb hs
  rcases amp hb hs with ⟨period, window⟩
  exact ⟨period, window, lowRowSyncProvider_core⟩

theorem periodWindowEmbeddingAmplification_of_periodWindowLowRowAmplification
    (amp : PeriodWindowLowRowAmplification) :
    PeriodWindowEmbeddingAmplification := by
  intro p q c hb hs
  rcases amp hb hs with ⟨period, window, sync⟩
  exact ⟨period, window, embeddingProvider_of_lowRowSync hb hs sync⟩

theorem freshExtensionAmplification_of_periodWindowAmplification
    (amp : PeriodWindowAmplification) :
    FreshExtensionAmplification :=
  freshExtensionAmplification_of_periodWindowEmbeddingAmplification
    (periodWindowEmbeddingAmplification_of_periodWindowAmplification amp)

theorem freshExtensionAmplification_of_windowAmplification
    (amp : WindowAmplification) :
    FreshExtensionAmplification :=
  freshExtensionAmplification_of_periodWindowAmplification
    (periodWindowAmplification_of_windowAmplification amp)

theorem freshExtensionAmplification_of_periodWindowLowRowAmplification
    (amp : PeriodWindowLowRowAmplification) :
    FreshExtensionAmplification :=
  freshExtensionAmplification_of_periodWindowEmbeddingAmplification
    (periodWindowEmbeddingAmplification_of_periodWindowLowRowAmplification amp)

theorem goodSeedAmplification_of_freshExtensionAmplification
    (freshAmp : FreshExtensionAmplification) :
    GoodSeedAmplification := by
  intro p q c hb hs
  exact infinite_pairwise_nonrep_of_freshExtensionProvider (freshAmp hb hs)

theorem goodSeedAmplification_of_periodWindowEmbeddingAmplification
    (amp : PeriodWindowEmbeddingAmplification) :
    GoodSeedAmplification :=
  goodSeedAmplification_of_freshExtensionAmplification
    (freshExtensionAmplification_of_periodWindowEmbeddingAmplification amp)

theorem goodSeedAmplification_of_periodWindowAmplification
    (amp : PeriodWindowAmplification) :
    GoodSeedAmplification :=
  goodSeedAmplification_of_freshExtensionAmplification
    (freshExtensionAmplification_of_periodWindowAmplification amp)

theorem goodSeedAmplification_of_windowAmplification
    (amp : WindowAmplification) :
    GoodSeedAmplification := by
  intro p q c hb hs
  exact goodSeedAmplification_of_window hb hs (amp hb hs)

theorem goodSeedAmplification_of_periodWindowLowRowAmplification
    (amp : PeriodWindowLowRowAmplification) :
    GoodSeedAmplification :=
  goodSeedAmplification_of_freshExtensionAmplification
    (freshExtensionAmplification_of_periodWindowLowRowAmplification amp)

/- ## Explicit infinitude consequences -/

/-- A pairwise-coprime nonrepresentable sequence is injective. -/
theorem pairwiseCoprimeNonrepSeq_injective
    {p q : Nat} {f : Nat → Nat}
    (hf : PairwiseCoprimeNonrepSeq p q f) :
    Function.Injective f := by
  intro m n hmn
  apply Classical.byContradiction
  intro hne
  have hcop := hf.2 hne
  rw [hmn] at hcop
  have hself : f n = 1 := by simpa using hcop
  exact (Nat.ne_of_gt (hf.1 n).1) hself

/-- The sequence conclusion witnesses infinitely many distinct positive
nonrepresentables coprime to both bases. -/
theorem infinite_coprime_nonrepresentables_of_erdos1110Conclusion
    {p q : Nat} (h : Apiros1110Conclusion p q) :
    Set.Infinite (fun n : Nat =>
      1 < n ∧ Nonrepresentable p q n ∧ Nat.Coprime n (p * q)) := by
  rcases h with ⟨f, hf⟩
  have hinfinite : Set.Infinite (Set.range f) :=
    Set.infinite_range_of_injective (pairwiseCoprimeNonrepSeq_injective hf)
  apply hinfinite.mono
  intro n hn
  rcases hn with ⟨i, rfl⟩
  exact hf.1 i

/-- In particular, the set of all nonrepresentable integers is infinite. -/
theorem infinite_nonrepresentables_of_erdos1110Conclusion
    {p q : Nat} (h : Apiros1110Conclusion p q) :
    Set.Infinite (fun n : Nat => Nonrepresentable p q n) := by
  exact (infinite_coprime_nonrepresentables_of_erdos1110Conclusion h).mono
    (by intro n hn; exact hn.2.1)

end Apiros1110

end

-- ===== source module Apiros1110.Density.Zero =====

section

/-
# Quantitative zero density and coprime nonrepresentables

`RepresentableDensityZero` is an entirely arithmetic formulation of natural
density zero.  It says that, for every positive denominator `K`, the counting
function is eventually at most `X / K`.  This avoids making the main theorem
depend on a particular real-valued presentation of asymptotic density.

The main result of this file is stronger than the infinitude assertion used by
Yu--Chen: zero density supplies a fresh nonrepresentable in the residue class
`1` modulo any prescribed product.  The existing product-state construction
then gives an infinite *pairwise-coprime* sequence.
-/

namespace Apiros1110

def RepresentableDensityZero (p q : Nat) : Prop :=
  ∀ K : Nat, 0 < K →
    ∃ X₀ : Nat, ∀ X ≥ X₀,
      K * representableCount p q X ≤ X

theorem representableDensityZero_comm
    {p q : Nat} :
    RepresentableDensityZero p q ↔ RepresentableDensityZero q p := by
  constructor <;> intro h K hK
  · rcases h K hK with ⟨X₀, hX₀⟩
    refine ⟨X₀, ?_⟩
    intro X hX
    simpa [representableCount_comm] using hX₀ X hX
  · rcases h K hK with ⟨X₀, hX₀⟩
    refine ⟨X₀, ?_⟩
    intro X hX
    simpa [representableCount_comm] using hX₀ X hX

private theorem residue_one_coprime
    {M t : Nat} :
    Nat.Coprime (1 + M * (t + 1)) M := by
  rw [Nat.coprime_iff_gcd_eq_one]
  simp

theorem freshExtensionProvider_of_densityZero
    {p q c : Nat}
    (hb : ValidBases p q)
    (hzero : RepresentableDensityZero p q) :
    FreshExtensionProvider p q c := by
  intro D hD
  have hDpos : 0 < D := positive_of_coprime_mul_validBases hb hD
  have hpqpos : 0 < p * q :=
    Nat.lt_trans Nat.zero_lt_one (validBases_mul_gt_one hb)
  let M := D * (p * q)
  have hMpos : 0 < M := Nat.mul_pos hDpos hpqpos
  let K := M + 1
  have hKpos : 0 < K := Nat.zero_lt_succ M
  rcases hzero K hKpos with ⟨X₀, hX₀⟩
  let T := X₀ + 2
  let X := 1 + M * T
  have hXX₀ : X₀ ≤ X := by
    calc
      X₀ ≤ T := by simp [T]
      _ ≤ M * T := Nat.le_mul_of_pos_left T hMpos
      _ ≤ X := by simp [X]
  have hcount : K * representableCount p q X ≤ X := hX₀ X hXX₀
  by_contra hnone
  have hnone' : ∀ t : Nat, t < T → Representable p q (1 + M * (t + 1)) := by
    intro t ht
    by_contra hnrep
    let N := 1 + M * (t + 1)
    have hNM : Nat.Coprime N M := by
      exact residue_one_coprime
    have hDdvd : D ∣ M := by
      exact ⟨p * q, rfl⟩
    have hpqdvd : p * q ∣ M := by
      refine ⟨D, ?_⟩
      simp [M, Nat.mul_comm]
    have hND : Nat.Coprime N D :=
      Nat.Coprime.coprime_dvd_right hDdvd hNM
    have hNpq : Nat.Coprime N (p * q) :=
      Nat.Coprime.coprime_dvd_right hpqdvd hNM
    have hNgt : 1 < N := by
      have : 0 < M * (t + 1) := Nat.mul_pos hMpos (Nat.succ_pos t)
      simp [N, this]
    exact hnone ⟨N, hNgt, hnrep, hNpq, hND⟩
  have hTcount : T ≤ representableCount p q X := by
    classical
    simpa using
      (DensityDecoderCert.card_le_representableCount_of_injOn
        (s := Finset.range T)
        (P := p) (Q := q) (X := X)
        (value := fun t => 1 + M * (t + 1))
        (by
          intro t ht
          have htT : t < T := Finset.mem_range.mp ht
          refine ⟨by omega, ?_, hnone' t htT⟩
          dsimp [X]
          have hmul : M * (t + 1) ≤ M * T :=
            Nat.mul_le_mul_left M (Nat.succ_le_of_lt htT)
          omega)
        (by
          intro a _ha b _hb hab
          have hmul : M * (a + 1) = M * (b + 1) := Nat.add_left_cancel hab
          have hab' : a + 1 = b + 1 := Nat.mul_left_cancel hMpos hmul
          omega))
  have hlarge : K * T ≤ X :=
    (Nat.mul_le_mul_left K hTcount).trans hcount
  dsimp [K, X, T] at hlarge
  rw [Nat.add_mul] at hlarge
  simp only [Nat.one_mul] at hlarge
  omega

theorem erdos1110Conclusion_of_densityZero
    {p q : Nat}
    (hb : ValidBases p q)
    (hzero : RepresentableDensityZero p q) :
    Apiros1110Conclusion p q := by
  exact infinite_pairwise_nonrep_of_freshExtensionProvider
    (freshExtensionProvider_of_densityZero (c := 0) hb hzero)

end Apiros1110

end

-- ===== source module Apiros1110.Density.YuChen =====

section

/-
# Yu--Chen counting and point-nine-nine bounds

The binomial (monotone-path) encoding gives the sharp count needed when the
second base is two.  Its binary corollary gives coefficient-one eventual
`X^0.99` bounds, and hence density zero, in the remaining quantitative
Yu--Chen ranges.
-/

namespace Apiros1110

private abbrev PointLex (x y : Point) : Prop :=
  Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a ≤ b) x y

private def sourceSort (A : List Point) : List Point :=
  A.toFinset.sort PointLex

private theorem sourceSort_pairwise (A : List Point) :
    (sourceSort A).Pairwise PointLex :=
  Finset.pairwise_sort A.toFinset PointLex

private theorem sourceSort_nodup (A : List Point) :
    (sourceSort A).Nodup :=
  Finset.sort_nodup A.toFinset PointLex

private theorem mem_sourceSort_iff {A : List Point} {x : Point} :
    x ∈ sourceSort A ↔ x ∈ A := by
  simp [sourceSort]

private theorem first_sortedLT_aux
    {A : List Point} (hA : IsAntichain A) :
    ∀ {L : List Point},
      L.Pairwise PointLex → L.Nodup → (∀ x, x ∈ L → x ∈ A) →
        (L.map Prod.fst).SortedLT
  | [], _, _, _ => List.Pairwise.sortedLT List.Pairwise.nil
  | x :: xs, hsorted, hnodup, hmem => by
      rw [List.pairwise_cons] at hsorted
      rw [List.map_cons]
      have hn := List.nodup_cons.mp hnodup
      apply List.Pairwise.sortedLT
      constructor
      · intro i hi
        rcases List.mem_map.mp hi with ⟨y, hy, rfl⟩
        have hxA : x ∈ A := hmem x List.mem_cons_self
        have hyA : y ∈ A := hmem y (List.mem_cons_of_mem x hy)
        have hxy : x ≠ y := by
          intro h
          subst y
          exact hn.1 hy
        have hfirst : x.1 ≠ y.1 := by
          intro h
          exact hxy (antichain_same_first_eq hA hxA hyA h)
        rcases Prod.lex_iff.mp (hsorted.1 y hy) with hlt | heq
        · exact hlt
        · exact False.elim (hfirst heq.1)
      · exact (first_sortedLT_aux hA hsorted.2 hn.2
          (fun y hy => hmem y (List.mem_cons_of_mem x hy))).pairwise

private theorem second_sortedGT_aux
    {A : List Point} (hA : IsAntichain A) :
    ∀ {L : List Point},
      L.Pairwise PointLex → L.Nodup → (∀ x, x ∈ L → x ∈ A) →
        (L.map Prod.snd).SortedGT
  | [], _, _, _ => List.Pairwise.sortedGT List.Pairwise.nil
  | x :: xs, hsorted, hnodup, hmem => by
      rw [List.pairwise_cons] at hsorted
      rw [List.map_cons]
      have hn := List.nodup_cons.mp hnodup
      apply List.Pairwise.sortedGT
      constructor
      · intro j hj
        rcases List.mem_map.mp hj with ⟨y, hy, rfl⟩
        have hxA : x ∈ A := hmem x List.mem_cons_self
        have hyA : y ∈ A := hmem y (List.mem_cons_of_mem x hy)
        have hxy : x ≠ y := by
          intro h
          subst y
          exact hn.1 hy
        have hfirst_ne : x.1 ≠ y.1 := by
          intro h
          exact hxy (antichain_same_first_eq hA hxA hyA h)
        have hfirst : x.1 < y.1 := by
          rcases Prod.lex_iff.mp (hsorted.1 y hy) with hlt | heq
          · exact hlt
          · exact False.elim (hfirst_ne heq.1)
        exact antichain_second_strictAnti_of_first_lt hA hxA hyA hfirst
      · exact (second_sortedGT_aux hA hsorted.2 hn.2
          (fun y hy => hmem y (List.mem_cons_of_mem x hy))).pairwise

private theorem sourceSort_first_sortedLT
    {A : List Point} (hA : IsAntichain A) :
    (sourceSort A).map Prod.fst |>.SortedLT := by
  exact first_sortedLT_aux hA (sourceSort_pairwise A) (sourceSort_nodup A)
    (fun x hx => mem_sourceSort_iff.mp hx)

private theorem sourceSort_second_sortedGT
    {A : List Point} (hA : IsAntichain A) :
    (sourceSort A).map Prod.snd |>.SortedGT := by
  exact second_sortedGT_aux hA (sourceSort_pairwise A) (sourceSort_nodup A)
    (fun x hx => mem_sourceSort_iff.mp hx)

private theorem point_list_eq_of_map_eq
    {A B : List Point}
    (hfst : A.map Prod.fst = B.map Prod.fst)
    (hsnd : A.map Prod.snd = B.map Prod.snd) : A = B := by
  induction A generalizing B with
  | nil => cases B <;> simp_all
  | cons x xs ih =>
      cases B with
      | nil => simp_all
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at hfst hsnd
          have hxy : x = y := Prod.ext hfst.1 hsnd.1
          subst y
          exact congrArg (List.cons x) (ih hfst.2 hsnd.2)

private def firstSet (A : List Point) : Finset Nat :=
  A.toFinset.image Prod.fst

private def secondSet (A : List Point) : Finset Nat :=
  A.toFinset.image Prod.snd

private theorem firstSet_eq_toFinset_sort_map (A : List Point) :
    firstSet A = ((sourceSort A).map Prod.fst).toFinset := by
  ext i
  simp [firstSet, sourceSort]

private theorem secondSet_eq_toFinset_sort_map (A : List Point) :
    secondSet A = ((sourceSort A).map Prod.snd).toFinset := by
  ext j
  simp [secondSet, sourceSort]

private theorem sourceSort_eq_of_coordinate_sets_eq
    {A B : List Point} (hA : IsAntichain A) (hB : IsAntichain B)
    (hfirst : firstSet A = firstSet B)
    (hsecond : secondSet A = secondSet B) :
    sourceSort A = sourceSort B := by
  have hfst : (sourceSort A).map Prod.fst = (sourceSort B).map Prod.fst := by
    apply List.SortedLT.eq_of_mem_iff (sourceSort_first_sortedLT hA)
      (sourceSort_first_sortedLT hB)
    rw [firstSet_eq_toFinset_sort_map, firstSet_eq_toFinset_sort_map] at hfirst
    intro i
    simpa using Finset.ext_iff.mp hfirst i
  have hsnd : (sourceSort A).map Prod.snd = (sourceSort B).map Prod.snd := by
    apply List.SortedGT.eq_of_mem_iff (sourceSort_second_sortedGT hA)
      (sourceSort_second_sortedGT hB)
    rw [secondSet_eq_toFinset_sort_map, secondSet_eq_toFinset_sort_map] at hsecond
    intro j
    simpa using Finset.ext_iff.mp hsecond j
  exact point_list_eq_of_map_eq hfst hsnd

private theorem sumTerms_eq_of_coordinate_sets_eq
    {p q : Nat} {A B : List Point}
    (hA : IsAntichain A) (hB : IsAntichain B)
    (hfirst : firstSet A = firstSet B)
    (hsecond : secondSet A = secondSet B) :
    SumTerms p q A = SumTerms p q B := by
  have hsort := sourceSort_eq_of_coordinate_sets_eq hA hB hfirst hsecond
  have hpermA : List.Perm (sourceSort A) A := by
    exact (Finset.sort_perm_toList A.toFinset PointLex).trans
      (List.toFinset_toList hA.1)
  have hpermB : List.Perm (sourceSort B) B := by
    exact (Finset.sort_perm_toList B.toFinset PointLex).trans
      (List.toFinset_toList hB.1)
  dsimp [SumTerms]
  calc
    (A.map (Term p q)).sum = ((sourceSort A).map (Term p q)).sum := by
      exact (List.Perm.sum_eq (hpermA.map (Term p q))).symm
    _ = ((sourceSort B).map (Term p q)).sum := by rw [hsort]
    _ = (B.map (Term p q)).sum := List.Perm.sum_eq (hpermB.map (Term p q))

/- A pair of equally sized coordinate sets is encoded as one fixed-size
subset: first coordinates occupy the left block and the complement of the
second coordinates occupies the right block. -/
private def pathKey (a b : Nat) (A : List Point) : Finset Nat :=
  firstSet A ∪ ((Finset.range (b + 1) \ secondSet A).image fun j => a + 1 + j)

private theorem firstSet_card
    {A : List Point} (hA : IsAntichain A) :
    (firstSet A).card = A.length := by
  rw [firstSet, Finset.card_image_iff.mpr]
  · exact List.toFinset_card_of_nodup hA.1
  · intro x hx y hy hxy
    exact antichain_same_first_eq hA (by simpa using hx) (by simpa using hy) hxy

private theorem secondSet_card
    {A : List Point} (hA : IsAntichain A) :
    (secondSet A).card = A.length := by
  rw [secondSet, Finset.card_image_iff.mpr]
  · exact List.toFinset_card_of_nodup hA.1
  · intro x hx y hy hxy
    exact antichain_same_second_eq hA (by simpa using hx) (by simpa using hy) hxy

private theorem firstSet_subset_range
    {a : Nat} {A : List Point} (hbound : ∀ x ∈ A, x.1 ≤ a) :
    firstSet A ⊆ Finset.range (a + 1) := by
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨x, hx, rfl⟩
  have := hbound x (by simpa using hx)
  rw [Finset.mem_range]
  omega

private theorem secondSet_subset_range
    {b : Nat} {A : List Point} (hbound : ∀ x ∈ A, x.2 ≤ b) :
    secondSet A ⊆ Finset.range (b + 1) := by
  intro j hj
  rcases Finset.mem_image.mp hj with ⟨x, hx, rfl⟩
  have := hbound x (by simpa using hx)
  rw [Finset.mem_range]
  omega

private theorem pathKey_subset_range
    {a b : Nat} {A : List Point}
    (hfirst : ∀ x ∈ A, x.1 ≤ a) :
    pathKey a b A ⊆ Finset.range (a + b + 2) := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · have hi' := firstSet_subset_range hfirst hi
    simp only [Finset.mem_range] at hi' ⊢
    omega
  · rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    have hj' : j < b + 1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
    simp only [Finset.mem_range]
    omega

private theorem pathKey_card
    {a b : Nat} {A : List Point} (hA : IsAntichain A)
    (hfirst : ∀ x ∈ A, x.1 ≤ a)
    (hsecond : ∀ x ∈ A, x.2 ≤ b) :
    (pathKey a b A).card = b + 1 := by
  have hfirstSub := firstSet_subset_range hfirst
  have hsecondSub := secondSet_subset_range hsecond
  have hdisj : Disjoint (firstSet A)
      ((Finset.range (b + 1) \ secondSet A).image fun j => a + 1 + j) := by
    rw [Finset.disjoint_left]
    intro i hiFirst hiRight
    rcases Finset.mem_image.mp hiRight with ⟨j, _hj, hij⟩
    have hiRange := hfirstSub hiFirst
    simp only [Finset.mem_range] at hiRange
    omega
  rw [pathKey, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun _ _ h => by omega),
    Finset.card_sdiff_of_subset hsecondSub, Finset.card_range,
    firstSet_card hA, secondSet_card hA]
  have hlen : A.length ≤ b + 1 := by
    rw [← secondSet_card hA, ← Finset.card_range (b + 1)]
    exact Finset.card_le_card hsecondSub
  omega

private theorem coordinate_sets_eq_of_pathKey_eq
    {a b : Nat} {A B : List Point}
    (hAfirst : ∀ x ∈ A, x.1 ≤ a) (hAsecond : ∀ x ∈ A, x.2 ≤ b)
    (hBfirst : ∀ x ∈ B, x.1 ≤ a) (hBsecond : ∀ x ∈ B, x.2 ≤ b)
    (hkey : pathKey a b A = pathKey a b B) :
    firstSet A = firstSet B ∧ secondSet A = secondSet B := by
  have hAf := firstSet_subset_range hAfirst
  have hAs := secondSet_subset_range hAsecond
  have hBf := firstSet_subset_range hBfirst
  have hBs := secondSet_subset_range hBsecond
  constructor
  · ext i
    have hiA : i ∈ firstSet A ↔ i ∈ pathKey a b A ∧ i < a + 1 := by
      constructor
      · intro hi
        exact ⟨Finset.mem_union_left _ hi, Finset.mem_range.mp (hAf hi)⟩
      · rintro ⟨hi, hilow⟩
        rcases Finset.mem_union.mp hi with hi | hi
        · exact hi
        · rcases Finset.mem_image.mp hi with ⟨j, _hj, rfl⟩
          omega
    have hiB : i ∈ firstSet B ↔ i ∈ pathKey a b B ∧ i < a + 1 := by
      constructor
      · intro hi
        exact ⟨Finset.mem_union_left _ hi, Finset.mem_range.mp (hBf hi)⟩
      · rintro ⟨hi, hilow⟩
        rcases Finset.mem_union.mp hi with hi | hi
        · exact hi
        · rcases Finset.mem_image.mp hi with ⟨j, _hj, rfl⟩
          omega
    rw [hiA, hiB, hkey]
  · ext j
    by_cases hj : j < b + 1
    · have hshiftA : a + 1 + j ∈ pathKey a b A ↔ j ∉ secondSet A := by
        constructor
        · intro h
          rcases Finset.mem_union.mp h with hleft | hright
          · have := Finset.mem_range.mp (hAf hleft)
            omega
          · rcases Finset.mem_image.mp hright with ⟨k, hk, heq⟩
            have hkj : k = j := by omega
            subst k
            exact (Finset.mem_sdiff.mp hk).2
        · intro hnot
          apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          exact ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hj, hnot⟩, rfl⟩
      have hshiftB : a + 1 + j ∈ pathKey a b B ↔ j ∉ secondSet B := by
        constructor
        · intro h
          rcases Finset.mem_union.mp h with hleft | hright
          · have := Finset.mem_range.mp (hBf hleft)
            omega
          · rcases Finset.mem_image.mp hright with ⟨k, hk, heq⟩
            have hkj : k = j := by omega
            subst k
            exact (Finset.mem_sdiff.mp hk).2
        · intro hnot
          apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          exact ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hj, hnot⟩, rfl⟩
      have hnot : j ∉ secondSet A ↔ j ∉ secondSet B := by
        rw [← hshiftA, ← hshiftB, hkey]
      tauto
    · have hnA : j ∉ secondSet A := fun h => hj (Finset.mem_range.mp (hAs h))
      have hnB : j ∉ secondSet B := fun h => hj (Finset.mem_range.mp (hBs h))
      simp [hnA, hnB]

private theorem sumTerms_eq_of_pathKey_eq
    {p q a b : Nat} {A B : List Point}
    (hA : IsAntichain A) (hB : IsAntichain B)
    (hAfirst : ∀ x ∈ A, x.1 ≤ a) (hAsecond : ∀ x ∈ A, x.2 ≤ b)
    (hBfirst : ∀ x ∈ B, x.1 ≤ a) (hBsecond : ∀ x ∈ B, x.2 ≤ b)
    (hkey : pathKey a b A = pathKey a b B) :
    SumTerms p q A = SumTerms p q B := by
  rcases coordinate_sets_eq_of_pathKey_eq hAfirst hAsecond hBfirst hBsecond hkey with
    ⟨hfirst, hsecond⟩
  exact sumTerms_eq_of_coordinate_sets_eq hA hB hfirst hsecond

private noncomputable def sourceWitness (p q n : Nat) : List Point := by
  classical
  exact if h : Representable p q n then Classical.choose h else []

private theorem sourceWitness_spec
    {p q n : Nat} (h : Representable p q n) :
    IsAntichain (sourceWitness p q n) ∧ SumTerms p q (sourceWitness p q n) = n := by
  classical
  simp only [sourceWitness, dif_pos h]
  exact Classical.choose_spec h

private theorem sourceWitness_first_le_log
    {p q n X : Nat} (hp : 1 < p) (hq : 1 < q) (hnX : n ≤ X)
    (hrep : Representable p q n) :
    ∀ x ∈ sourceWitness p q n, x.1 ≤ Nat.log p X := by
  intro x hx
  have hterm : Term p q x ≤ n := by
    rw [← (sourceWitness_spec hrep).2]
    exact mem_term_le_sum hx
  have hpow : p ^ x.1 ≤ X := by
    calc
      p ^ x.1 ≤ p ^ x.1 * q ^ x.2 :=
        Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.zero_lt_of_lt hq))
      _ = Term p q x := rfl
      _ ≤ n := hterm
      _ ≤ X := hnX
  exact Nat.le_log_of_pow_le hp hpow

private theorem sourceWitness_second_le_log
    {p q n X : Nat} (hp : 1 < p) (hq : 1 < q) (hnX : n ≤ X)
    (hrep : Representable p q n) :
    ∀ x ∈ sourceWitness p q n, x.2 ≤ Nat.log q X := by
  intro x hx
  have hterm : Term p q x ≤ n := by
    rw [← (sourceWitness_spec hrep).2]
    exact mem_term_le_sum hx
  have hpow : q ^ x.2 ≤ X := by
    calc
      q ^ x.2 ≤ p ^ x.1 * q ^ x.2 :=
        Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.zero_lt_of_lt hp))
      _ = Term p q x := rfl
      _ ≤ n := hterm
      _ ≤ X := hnX
  exact Nat.le_log_of_pow_le hq hpow

private noncomputable def representedPathKey (p q X n : Nat) : Finset Nat :=
  pathKey (Nat.log p X) (Nat.log q X) (sourceWitness p q n)

theorem representableCount_le_choose
    {p q X : Nat} (hp : 1 < p) (hq : 1 < q) :
    representableCount p q X ≤
      (Nat.log p X + Nat.log q X + 2).choose (Nat.log q X + 1) := by
  classical
  let s := DensityDecoderCert.representedFinset p q X
  let t := (Finset.range (Nat.log p X + Nat.log q X + 2)).powersetCard
    (Nat.log q X + 1)
  have hcard : s.card ≤ t.card := by
    apply Finset.card_le_card_of_injOn (representedPathKey p q X)
    · intro n hn
      dsimp [s, DensityDecoderCert.representedFinset] at hn
      simp at hn
      have hnX : n ≤ X := hn.1
      have hrep : Representable p q n := hn.2.2
      apply Finset.mem_powersetCard.mpr
      constructor
      · exact pathKey_subset_range
          (sourceWitness_first_le_log hp hq hnX hrep)
      · exact pathKey_card (sourceWitness_spec hrep).1
          (sourceWitness_first_le_log hp hq hnX hrep)
          (sourceWitness_second_le_log hp hq hnX hrep)
    · intro n hn m hm hkey
      dsimp [s, DensityDecoderCert.representedFinset] at hn hm
      simp at hn hm
      have hnX : n ≤ X := hn.1
      have hmX : m ≤ X := hm.1
      have hnrep : Representable p q n := hn.2.2
      have hmrep : Representable p q m := hm.2.2
      have hsum := sumTerms_eq_of_pathKey_eq (p := p) (q := q)
        (sourceWitness_spec hnrep).1 (sourceWitness_spec hmrep).1
        (sourceWitness_first_le_log hp hq hnX hnrep)
        (sourceWitness_second_le_log hp hq hnX hnrep)
        (sourceWitness_first_le_log hp hq hmX hmrep)
        (sourceWitness_second_le_log hp hq hmX hmrep) hkey
      rw [(sourceWitness_spec hnrep).2, (sourceWitness_spec hmrep).2] at hsum
      exact hsum
  simpa [s, t, DensityDecoderCert.representedFinset_card,
    Finset.card_powersetCard, Finset.card_range] using hcard

private theorem choose_mul_weights_le_add_pow
    (u v n k : Nat) :
    n.choose k * u ^ k * v ^ (n - k) ≤ (u + v) ^ n := by
  by_cases hk : k ≤ n
  · rw [add_pow]
    have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hterm := Finset.single_le_sum
      (fun i _hi => Nat.zero_le (u ^ i * v ^ (n - i) * n.choose i)) hmem
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hterm
  · have : n.choose k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)
    simp [this]

private theorem weighted_choose_pow_bound
    {p q u v D a b n k : Nat}
    (hu : 0 < u) (hv : 0 < v) (hk : k ≤ n)
    (hA : (u + v) ^ D ≤ p ^ a * v ^ D)
    (hB : (u + v) ^ D ≤ q ^ b * u ^ D) :
    (n.choose k) ^ D ≤ p ^ (a * (n - k)) * q ^ (b * k) := by
  have hterm := Nat.pow_le_pow_left (choose_mul_weights_le_add_pow u v n k) D
  have hterm' :
      (n.choose k) ^ D * (u ^ (D * k) * v ^ (D * (n - k))) ≤
        (u + v) ^ (D * n) := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hterm
  have hsplit : n - k + k = n := Nat.sub_add_cancel hk
  have hright : (u + v) ^ (D * n) ≤
      (p ^ a * v ^ D) ^ (n - k) * (q ^ b * u ^ D) ^ k := by
    calc
      (u + v) ^ (D * n) = ((u + v) ^ D) ^ n := pow_mul _ _ _
      _ = ((u + v) ^ D) ^ (n - k) * ((u + v) ^ D) ^ k := by
        rw [← pow_add, hsplit]
      _ ≤ (p ^ a * v ^ D) ^ (n - k) * (q ^ b * u ^ D) ^ k :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hA _) (Nat.pow_le_pow_left hB _)
  have hweighted :
      (n.choose k) ^ D * (u ^ (D * k) * v ^ (D * (n - k))) ≤
        (p ^ (a * (n - k)) * q ^ (b * k)) *
          (u ^ (D * k) * v ^ (D * (n - k))) := by
    calc
      _ ≤ (u + v) ^ (D * n) := hterm'
      _ ≤ (p ^ a * v ^ D) ^ (n - k) * (q ^ b * u ^ D) ^ k := hright
      _ = _ := by
        simp only [mul_pow, ← pow_mul]
        ac_rfl
  exact (Nat.mul_le_mul_right_iff
    (Nat.mul_pos (Nat.pow_pos hu) (Nat.pow_pos hv))).mp hweighted

/-- Integer-power formulation of an eventual `X^0.99` upper bound. -/
def RepresentableCountPoint99Bound (p q : Nat) : Prop :=
  ∃ X₀ : Nat, ∀ X : Nat, X₀ ≤ X →
    (representableCount p q X) ^ 100 ≤ X ^ 99

private theorem point99_certificate_eleven_left :
    241 ^ 99 ≤ 11 ^ 61 * 55 ^ 99 := by
  norm_num

private theorem point99_certificate_two_right :
    241 ^ 99 ≤ 2 ^ 37 * 186 ^ 99 := by
  norm_num

private theorem choose_logs_pow_99_le
    {p X : Nat} (hp : 11 ≤ p) (hX : X ≠ 0) :
    ((Nat.log p X + Nat.log 2 X + 2).choose (Nat.log 2 X + 1)) ^ 99 ≤
      (p ^ 61 * 2 ^ 37) * X ^ 98 := by
  let A := Nat.log p X
  let B := Nat.log 2 X
  have hk : B + 1 ≤ A + B + 2 := by omega
  have hsub : A + B + 2 - (B + 1) = A + 1 := by omega
  have hleft : 241 ^ 99 ≤ p ^ 61 * 55 ^ 99 := by
    exact point99_certificate_eleven_left.trans
      (Nat.mul_le_mul_right (55 ^ 99) (Nat.pow_le_pow_left hp 61))
  have hweighted := weighted_choose_pow_bound
    (p := p) (q := 2) (u := 186) (v := 55)
    (D := 99) (a := 61) (b := 37)
    (n := A + B + 2) (k := B + 1)
    (by decide) (by decide) hk hleft point99_certificate_two_right
  rw [hsub] at hweighted
  have hpLog : p ^ A ≤ X := by
    exact Nat.pow_log_le_self p hX
  have htwoLog : 2 ^ B ≤ X := by
    exact Nat.pow_log_le_self 2 hX
  have hpPart : p ^ (61 * (A + 1)) ≤ p ^ 61 * X ^ 61 := by
    calc
      p ^ (61 * (A + 1)) = p ^ 61 * (p ^ A) ^ 61 := by
        rw [show 61 * (A + 1) = 61 + A * 61 by omega, pow_add, pow_mul]
      _ ≤ p ^ 61 * X ^ 61 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpLog 61)
  have htwoPart : 2 ^ (37 * (B + 1)) ≤ 2 ^ 37 * X ^ 37 := by
    calc
      2 ^ (37 * (B + 1)) = 2 ^ 37 * (2 ^ B) ^ 37 := by
        rw [show 37 * (B + 1) = 37 + B * 37 by omega, pow_add, pow_mul]
      _ ≤ 2 ^ 37 * X ^ 37 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htwoLog 37)
  calc
    ((Nat.log p X + Nat.log 2 X + 2).choose (Nat.log 2 X + 1)) ^ 99
        ≤ p ^ (61 * (A + 1)) * 2 ^ (37 * (B + 1)) := by
          simpa [A, B] using hweighted
    _ ≤ (p ^ 61 * X ^ 61) * (2 ^ 37 * X ^ 37) :=
      Nat.mul_le_mul hpPart htwoPart
    _ = (p ^ 61 * 2 ^ 37) * X ^ 98 := by
      rw [show 98 = 61 + 37 by norm_num, pow_add]
      ac_rfl

private theorem representableCount_pow_99_le
    {p X : Nat} (hp : 11 ≤ p) (hX : X ≠ 0) :
    (representableCount p 2 X) ^ 99 ≤
      (p ^ 61 * 2 ^ 37) * X ^ 98 := by
  exact (Nat.pow_le_pow_left
    (representableCount_le_choose (X := X) (by omega) (by decide)) 99).trans
      (choose_logs_pow_99_le hp hX)

/-- Yu--Chen's coefficient-one eventual `X^0.99` bound when `q = 2`. -/
theorem representableCount_point99_two_of_eleven_le
    {p : Nat} (hp : 11 ≤ p) :
    RepresentableCountPoint99Bound p 2 := by
  let C := p ^ 61 * 2 ^ 37
  have hC : 0 < C := by positivity
  refine ⟨C ^ 100, ?_⟩
  intro X hX
  have hXpos : 0 < X := (Nat.pow_pos hC).trans_le hX
  have hcount := representableCount_pow_99_le hp (Nat.ne_of_gt hXpos)
  apply (Nat.pow_le_pow_iff_left (by decide : 99 ≠ 0)).mp
  calc
    ((representableCount p 2 X) ^ 100) ^ 99 =
        ((representableCount p 2 X) ^ 99) ^ 100 := by
      simp only [← pow_mul]
    _ ≤ (C * X ^ 98) ^ 100 := Nat.pow_le_pow_left hcount 100
    _ = C ^ 100 * X ^ 9800 := by
      rw [mul_pow, ← pow_mul]
    _ ≤ X * X ^ 9800 := Nat.mul_le_mul_right _ hX
    _ = X ^ 9801 := by
      rw [show 9801 = 1 + 9800 by norm_num, pow_add]
      simp
    _ = (X ^ 99) ^ 99 := by rw [← pow_mul]

private theorem representableDensityZero_of_point99Bound
    {p q : Nat} (hpoint99 : RepresentableCountPoint99Bound p q) :
    RepresentableDensityZero p q := by
  intro K hK
  rcases hpoint99 with ⟨X₀, hX₀⟩
  refine ⟨max X₀ (K ^ 100), ?_⟩
  intro X hX
  have hpoint := hX₀ X ((Nat.le_max_left _ _).trans hX)
  have hKX : K ^ 100 ≤ X := (Nat.le_max_right _ _).trans hX
  apply (Nat.pow_le_pow_iff_left (by decide : 100 ≠ 0)).mp
  calc
    (K * representableCount p q X) ^ 100 =
        K ^ 100 * (representableCount p q X) ^ 100 := mul_pow _ _ _
    _ ≤ K ^ 100 * X ^ 99 := Nat.mul_le_mul_left _ hpoint
    _ ≤ X * X ^ 99 := Nat.mul_le_mul_right _ hKX
    _ = X ^ 100 := by
      rw [show 100 = 1 + 99 by norm_num, pow_add]
      simp

/-- The sharp binary endpoint of the Yu--Chen zero-density range. -/
theorem representableDensityZero_two_of_eleven_le
    {p : Nat} (hp : 11 ≤ p) :
    RepresentableDensityZero p 2 :=
  representableDensityZero_of_point99Bound
    (representableCount_point99_two_of_eleven_le hp)

/- ## The remaining Yu--Chen ranges -/

theorem representableCount_le_binary_source_keys
    {p q X : Nat} (hp : 1 < p) (hq : 1 < q) :
    representableCount p q X ≤
      2 ^ (Nat.log p X + Nat.log q X + 2) :=
  (representableCount_le_choose (X := X) hp hq).trans
    (Nat.choose_le_two_pow _ _)

private theorem binary_log_product_pow_le
    {p q X D r s : Nat}
    (hX : X ≠ 0) (hadd : r + s + 1 = D)
    (hpCert : 2 ^ D ≤ p ^ r) (hqCert : 2 ^ D ≤ q ^ s) :
    (2 ^ (Nat.log p X + Nat.log q X)) ^ D ≤ X ^ (D - 1) := by
  let a := Nat.log p X
  let b := Nat.log q X
  have hpLog : p ^ a ≤ X := Nat.pow_log_le_self p hX
  have hqLog : q ^ b ≤ X := Nat.pow_log_le_self q hX
  calc
    (2 ^ (Nat.log p X + Nat.log q X)) ^ D =
        (2 ^ D) ^ a * (2 ^ D) ^ b := by
      dsimp [a, b]
      simp only [← Nat.pow_mul, ← Nat.pow_add]
      apply congrArg (fun e : Nat => 2 ^ e)
      simp [Nat.mul_add, Nat.mul_comm]
    _ ≤ (p ^ r) ^ a * (q ^ s) ^ b :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hpCert a)
        (Nat.pow_le_pow_left hqCert b)
    _ = (p ^ a) ^ r * (q ^ b) ^ s := by
      simp only [← Nat.pow_mul]
      simp [Nat.mul_comm]
    _ ≤ X ^ r * X ^ s :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hpLog r)
        (Nat.pow_le_pow_left hqLog s)
    _ = X ^ (D - 1) := by
      rw [← Nat.pow_add]
      apply congrArg (fun e : Nat => X ^ e)
      omega

private theorem representableCountPoint99Bound_of_binary_power_cert
    {p q D r s : Nat}
    (hp : 1 < p) (hq : 1 < q) (hD : 0 < D) (hDlt : D < 100)
    (hadd : r + s + 1 = D)
    (hpCert : 2 ^ D ≤ p ^ r) (hqCert : 2 ^ D ≤ q ^ s) :
    RepresentableCountPoint99Bound p q := by
  let C := 4 ^ D
  have hC : 0 < C := by positivity
  refine ⟨C ^ 100, ?_⟩
  intro X hX
  have hXpos : 0 < X := (Nat.pow_pos hC).trans_le hX
  have hcore := binary_log_product_pow_le
    (p := p) (q := q) (X := X) (D := D) (r := r) (s := s)
    (Nat.ne_of_gt hXpos) hadd hpCert hqCert
  have hcountD : (representableCount p q X) ^ D ≤ C * X ^ (D - 1) := by
    calc
      (representableCount p q X) ^ D ≤
          (2 ^ (Nat.log p X + Nat.log q X + 2)) ^ D :=
        Nat.pow_le_pow_left
          (representableCount_le_binary_source_keys
            (p := p) (q := q) (X := X) hp hq) D
      _ = C * (2 ^ (Nat.log p X + Nat.log q X)) ^ D := by
        dsimp [C]
        rw [Nat.pow_add, mul_pow]
        norm_num [Nat.pow_two]
        ac_rfl
      _ ≤ C * X ^ (D - 1) := Nat.mul_le_mul_left C hcore
  apply (Nat.pow_le_pow_iff_left (Nat.ne_of_gt hD)).mp
  calc
    ((representableCount p q X) ^ 100) ^ D =
        ((representableCount p q X) ^ D) ^ 100 := by
      simp only [← pow_mul]
      rw [Nat.mul_comm]
    _ ≤ (C * X ^ (D - 1)) ^ 100 := Nat.pow_le_pow_left hcountD 100
    _ = C ^ 100 * X ^ (100 * (D - 1)) := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul]
      apply congrArg (fun e : Nat => X ^ e)
      omega
    _ ≤ X * X ^ (100 * (D - 1)) := Nat.mul_le_mul_right _ hX
    _ = X ^ (1 + 100 * (D - 1)) := by rw [pow_add]; simp
    _ ≤ X ^ (99 * D) := Nat.pow_le_pow_right hXpos (by omega)
    _ = (X ^ 99) ^ D := by rw [← pow_mul]

/-- Yu--Chen's coefficient-one eventual `X^0.99` bound when `4 ≤ q < p`. -/
theorem representableCount_point99_of_four_le_lt
    {p q : Nat} (hq : 4 ≤ q) (hpq : q < p) :
    RepresentableCountPoint99Bound p q := by
  apply representableCountPoint99Bound_of_binary_power_cert
    (D := 16) (r := 7) (s := 8)
  · omega
  · omega
  · norm_num
  · norm_num
  · norm_num
  · exact (show 2 ^ 16 ≤ 5 ^ 7 by norm_num).trans
      (Nat.pow_le_pow_left (by omega : 5 ≤ p) 7)
  · exact (show 2 ^ 16 ≤ 4 ^ 8 by norm_num).trans
      (Nat.pow_le_pow_left hq 8)

/-- Yu--Chen's coefficient-one eventual `X^0.99` bound when `q = 3` and
`p ≥ 7`. -/
theorem representableCount_point99_of_seven_le_three
    {p : Nat} (hp : 7 ≤ p) :
    RepresentableCountPoint99Bound p 3 := by
  apply representableCountPoint99Bound_of_binary_power_cert
    (D := 84) (r := 30) (s := 53)
  · omega
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact (show 2 ^ 84 ≤ 7 ^ 30 by norm_num).trans
      (Nat.pow_le_pow_left hp 30)
  · norm_num

/-- The coefficient-one `X^0.99` bound throughout the quantitative
Yu--Chen range with second base at least three. -/
theorem representableCount_point99_yuChen_q_ge_three
    {p q : Nat} (hq : 3 ≤ q) (hpq : q < p)
    (hq3 : q = 3 → 7 ≤ p) :
    RepresentableCountPoint99Bound p q := by
  by_cases h : q = 3
  · subst q
    exact representableCount_point99_of_seven_le_three (hq3 rfl)
  · exact representableCount_point99_of_four_le_lt (by omega) hpq

theorem representableDensityZero_of_four_le_lt
    {p q : Nat} (hq : 4 ≤ q) (hpq : q < p) :
    RepresentableDensityZero p q :=
  representableDensityZero_of_point99Bound
    (representableCount_point99_of_four_le_lt hq hpq)

theorem representableDensityZero_of_seven_le_three
    {p : Nat} (hp : 7 ≤ p) :
    RepresentableDensityZero p 3 :=
  representableDensityZero_of_point99Bound
    (representableCount_point99_of_seven_le_three hp)

theorem representableDensityZero_yuChen_q_ge_three
    {p q : Nat} (hq : 3 ≤ q) (hpq : q < p)
    (hq3 : q = 3 → 7 ≤ p) :
    RepresentableDensityZero p q :=
  representableDensityZero_of_point99Bound
    (representableCount_point99_yuChen_q_ge_three hq hpq hq3)

end Apiros1110

end

-- ===== source module Apiros1110.YuChenSmallRangeObstructions =====

section

/-
# Residue obstructions for the two small Yu--Chen ranges

Only the forbidden residue layers used for `(4, 3)` and `(7, 2)` are retained
here.  They follow from the canonical-source envelope.
-/

namespace Apiros1110

namespace LocalEnvelope

/-- A positive integer lies in the coarse `Q`-adic local envelope when, after
removing an exact power of `Q`, its unit part is a power of `P` modulo `Q`. -/
def InEnvelope (P Q n : Nat) : Prop :=
  ∃ j i u : Nat, n = Q ^ j * (P ^ i + Q * u)

private theorem envelope_or_zero_of_canonical
    {P Q n : Nat} {A : List Point}
    (hcan : IsCanonicalSource P Q n A) :
    n = 0 ∨ InEnvelope P Q n := by
  induction hcan with
  | zero => exact Or.inl rfl
  | @scale m A hm hcan ih =>
      rcases ih with hmzero | ⟨j, i, u, hfac⟩
      · exact False.elim (Nat.ne_of_gt hm hmzero)
      · right
        refine ⟨j + 1, i, u, ?_⟩
        rw [hfac, Nat.pow_succ]
        ac_rfl
  | @attach e m A hnot hmin hcan hcols ih =>
      right
      exact ⟨0, e, m, by simp⟩

/-- Every positive representable integer is in its local envelope. -/
theorem inEnvelope_of_representable
    {P Q n : Nat}
    (hP : 1 < P) (hQ : 1 < Q) (hPQ : Nat.Coprime P Q)
    (hn : 0 < n) (hrep : Representable P Q n) :
    InEnvelope P Q n := by
  rcases exists_canonical_of_representable hP hQ hPQ hrep with
    ⟨A, B, hcan, hmin, hcols⟩
  rcases envelope_or_zero_of_canonical hcan with hzero | henv
  · exact False.elim (Nat.ne_of_gt hn hzero)
  · exact henv

/-- Representability is symmetric in the two bases. -/
theorem representable_comm (P Q n : Nat) :
    Representable P Q n ↔ Representable Q P n := by
  simpa using (Apiros1110.representable_comm (p := P) (q := Q) (n := n))

theorem nonrepresentable_comm (P Q n : Nat) :
    Nonrepresentable P Q n ↔ Nonrepresentable Q P n := by
  simp only [Nonrepresentable, representable_comm P Q n]

/-- The elementary residue class in the `j`-th exact `Q`-adic layer. -/
def InLayer (Q r j n : Nat) : Prop :=
  ∃ k : Nat, n = Q ^ j * (r + Q * k)

private theorem exact_factor_exponent_unique
    {Q j j' a b : Nat}
    (hQ : 0 < Q) (ha : ¬ Q ∣ a) (hb : ¬ Q ∣ b)
    (h : Q ^ j * a = Q ^ j' * b) :
    j = j' := by
  rcases lt_trichotomy j j' with hj | hj | hj
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hj)
    have hd : 0 < d := by omega
    rw [Nat.pow_add, Nat.mul_assoc] at h
    have heq : a = Q ^ d * b := by
      exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hQ) h
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    exfalso
    apply ha
    rw [Nat.pow_succ] at heq
    refine ⟨Q ^ e * b, ?_⟩
    calc
      a = Q ^ e * Q * b := heq
      _ = Q * (Q ^ e * b) := by ac_rfl
  · exact hj
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hj)
    have hd : 0 < d := by omega
    rw [Nat.pow_add, Nat.mul_assoc] at h
    have heq : Q ^ d * a = b := by
      exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hQ) h
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    exfalso
    apply hb
    rw [Nat.pow_succ] at heq
    refine ⟨Q ^ e * a, ?_⟩
    calc
      b = Q ^ e * Q * a := heq.symm
      _ = Q * (Q ^ e * a) := by ac_rfl

/-- A residue excluded from the power orbit modulo `Q` gives an entire
geometric family of nonrepresentable integers. -/
theorem nonrepresentable_of_layer
    {P Q r j n : Nat}
    (hP : 1 < P) (hQ : 1 < Q) (hPQ : Nat.Coprime P Q)
    (hrpos : 0 < r) (hrunit : ¬ Q ∣ r)
    (hforbid : ∀ i : Nat, P ^ i % Q ≠ r % Q)
    (hn : InLayer Q r j n) :
    Nonrepresentable P Q n := by
  rintro hrep
  rcases hn with ⟨k, rfl⟩
  have hnpos : 0 < Q ^ j * (r + Q * k) := by positivity
  rcases inEnvelope_of_representable hP hQ hPQ hnpos hrep with
    ⟨j', i, u, henv⟩
  have hr_not : ¬ Q ∣ r + Q * k := by
    intro hdiv
    exact hrunit ((Nat.dvd_add_left (Nat.dvd_mul_right Q k)).mp hdiv)
  have hp_not : ¬ Q ∣ P ^ i + Q * u :=
    not_q_dvd_p_pow_add_q_mul hQ hPQ
  have hj : j = j' := exact_factor_exponent_unique
    (Nat.lt_trans Nat.zero_lt_one hQ) hr_not hp_not henv
  subst j'
  have hunit : r + Q * k = P ^ i + Q * u :=
    Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.lt_trans Nat.zero_lt_one hQ)) henv
  have hmod := congrArg (fun z : Nat => z % Q) hunit
  exact hforbid i (by simpa [Nat.add_mod, Nat.mul_mod] using hmod.symm)

private theorem pow_two_mod_seven : ∀ i : Nat,
    2 ^ i % 7 = 1 ∨ 2 ^ i % 7 = 2 ∨ 2 ^ i % 7 = 4
  | 0 => by simp
  | i + 1 => by
      rw [Nat.pow_succ, Nat.mul_mod]
      rcases pow_two_mod_seven i with h | h | h <;> rw [h] <;> norm_num

private theorem pow_four_mod_three : ∀ i : Nat, 4 ^ i % 3 = 1
  | 0 => by simp
  | i + 1 => by
      rw [Nat.pow_succ, Nat.mul_mod, pow_four_mod_three i]

theorem nonrepresentable_7_2_layer_three {j k : Nat} :
    Nonrepresentable 7 2 (7 ^ j * (3 + 7 * k)) := by
  rw [nonrepresentable_comm]
  apply nonrepresentable_of_layer (P := 2) (Q := 7) (r := 3)
      (j := j) (hP := by decide) (hQ := by decide) (hPQ := by decide)
      (hrpos := by decide) (hrunit := by decide)
  · intro i hi
    rcases pow_two_mod_seven i with hi' | hi' | hi' <;> omega
  · exact ⟨k, rfl⟩

theorem nonrepresentable_4_3_layer_two {j k : Nat} :
    Nonrepresentable 4 3 (3 ^ j * (2 + 3 * k)) := by
  apply nonrepresentable_of_layer (P := 4) (Q := 3) (r := 2)
      (j := j) (hP := by decide) (hQ := by decide) (hPQ := by decide)
      (hrpos := by decide) (hrunit := by decide)
  · intro i hi
    rw [pow_four_mod_three i] at hi
    omega
  · exact ⟨k, rfl⟩

end LocalEnvelope

end Apiros1110

end

-- ===== source module Apiros1110.YuChenSmallRanges =====

section

/-
# The two small nonexceptional Yu--Chen ranges

The local-envelope obstruction supplies a forbidden residue layer.  For each
accumulated product `D`, explicit polynomial values in that layer are also
coprime to `D`, hence give fresh extensions.
-/

namespace Apiros1110

private theorem coprime_three_of_coprime_twelve
    {D : Nat} (hD : Nat.Coprime D (4 * 3)) :
    Nat.Coprime D 3 :=
  hD.coprime_dvd_right (by norm_num)

private theorem coprime_seven_of_coprime_fourteen
    {D : Nat} (hD : Nat.Coprime D (7 * 2)) :
    Nat.Coprime D 7 :=
  hD.coprime_dvd_right (by norm_num)

private theorem square_mod_three_eq_one
    {D : Nat} (hD : Nat.Coprime D (4 * 3)) :
    D ^ 2 % 3 = 1 := by
  have hnot : ¬ 3 ∣ D := by
    intro hdvd
    have hgcd : 3 ∣ Nat.gcd D 3 := Nat.dvd_gcd hdvd (Nat.dvd_refl 3)
    rw [(coprime_three_of_coprime_twelve hD).gcd_eq_one] at hgcd
    norm_num at hgcd
  have hmodne : D % 3 ≠ 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using hnot
  have hmodlt : D % 3 < 3 := Nat.mod_lt D (by decide)
  have hcases : D % 3 = 1 ∨ D % 3 = 2 := by omega
  rcases hcases with h | h
  · norm_num [Nat.pow_two, Nat.mul_mod, h]
  · norm_num [Nat.pow_two, Nat.mul_mod, h]

private theorem sixth_power_mod_seven_eq_one
    {D : Nat} (hD : Nat.Coprime D (7 * 2)) :
    D ^ 6 % 7 = 1 := by
  have hnot : ¬ 7 ∣ D := by
    intro hdvd
    have hgcd : 7 ∣ Nat.gcd D 7 := Nat.dvd_gcd hdvd (Nat.dvd_refl 7)
    rw [(coprime_seven_of_coprime_fourteen hD).gcd_eq_one] at hgcd
    norm_num at hgcd
  have hmodne : D % 7 ≠ 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using hnot
  have hmodlt : D % 7 < 7 := Nat.mod_lt D (by decide)
  have hcases : D % 7 = 1 ∨ D % 7 = 2 ∨ D % 7 = 3 ∨
      D % 7 = 4 ∨ D % 7 = 5 ∨ D % 7 = 6 := by omega
  have hreduce (r : Nat) (hr : r < 7) (hDr : D % 7 = r) :
      D ^ 6 % 7 = r ^ 6 % 7 := by
    have hm : Nat.ModEq 7 D r := by
      rw [Nat.ModEq, hDr, Nat.mod_eq_of_lt hr]
    exact hm.pow 6
  rcases hcases with h | h | h | h | h | h
  all_goals
    have hh := hreduce _ (by omega) h
    norm_num at hh
    exact hh

private theorem four_three_layer_witness
    {D : Nat} (hD : Nat.Coprime D (4 * 3)) :
    ∃ k : Nat, 1 + 4 * D ^ 2 = 2 + 3 * k := by
  have hmod : D ^ 2 % 3 = 1 := square_mod_three_eq_one hD
  have hdiv := Nat.mod_add_div (D ^ 2) 3
  rw [hmod] at hdiv
  refine ⟨1 + 4 * (D ^ 2 / 3), ?_⟩
  calc
    1 + 4 * D ^ 2 = 1 + 4 * (1 + 3 * (D ^ 2 / 3)) := by rw [hdiv]
    _ = 2 + 3 * (1 + 4 * (D ^ 2 / 3)) := by ring

private theorem seven_two_layer_witness
    {D : Nat} (hD : Nat.Coprime D (7 * 2)) :
    ∃ k : Nat, 1 + 2 * D ^ 6 = 3 + 7 * k := by
  have hmod : D ^ 6 % 7 = 1 := sixth_power_mod_seven_eq_one hD
  have hdiv := Nat.mod_add_div (D ^ 6) 7
  rw [hmod] at hdiv
  refine ⟨2 * (D ^ 6 / 7), ?_⟩
  calc
    1 + 2 * D ^ 6 = 1 + 2 * (1 + 7 * (D ^ 6 / 7)) := by rw [hdiv]
    _ = 3 + 7 * (2 * (D ^ 6 / 7)) := by ring

private theorem one_add_four_square_coprime_self (D : Nat) :
    Nat.Coprime (1 + 4 * D ^ 2) D := by
  have h : Nat.Coprime (1 + D * (4 * D)) D := by simp
  convert h using 1
  ring

private theorem one_add_two_sixth_coprime_self (D : Nat) :
    Nat.Coprime (1 + 2 * D ^ 6) D := by
  have h : Nat.Coprime (1 + D * (2 * D ^ 5)) D := by simp
  convert h using 1
  ring

theorem freshExtensionProvider_4_3 :
    FreshExtensionProvider 4 3 0 := by
  intro D hD
  let N := 1 + 4 * D ^ 2
  rcases four_three_layer_witness hD with ⟨k, hlayer⟩
  have hDpos : 0 < D := by
    exact positive_of_coprime_mul_validBases
      ({ one_lt_p := by decide, one_lt_q := by decide,
         coprime := by decide } : ValidBases 4 3) hD
  have hnonrep : Nonrepresentable 4 3 N := by
    rw [show N = 2 + 3 * k by exact hlayer]
    simpa using (LocalEnvelope.nonrepresentable_4_3_layer_two (j := 0) (k := k))
  have hcopFour : Nat.Coprime N 4 := by
    dsimp [N]
    simp
  have hcopThree : Nat.Coprime N 3 := by
    rw [show N = 2 + 3 * k by exact hlayer]
    simpa using (by decide : Nat.Coprime 2 3)
  refine ⟨N, ?_, hnonrep, hcopFour.mul_right hcopThree, ?_⟩
  · dsimp [N]
    have : 0 < 4 * D ^ 2 := by positivity
    omega
  · exact one_add_four_square_coprime_self D

theorem freshExtensionProvider_7_2 :
    FreshExtensionProvider 7 2 0 := by
  intro D hD
  let N := 1 + 2 * D ^ 6
  rcases seven_two_layer_witness hD with ⟨k, hlayer⟩
  have hDpos : 0 < D := by
    exact positive_of_coprime_mul_validBases
      ({ one_lt_p := by decide, one_lt_q := by decide,
         coprime := by decide } : ValidBases 7 2) hD
  have hnonrep : Nonrepresentable 7 2 N := by
    rw [show N = 3 + 7 * k by exact hlayer]
    simpa using (LocalEnvelope.nonrepresentable_7_2_layer_three (j := 0) (k := k))
  have hcopSeven : Nat.Coprime N 7 := by
    rw [show N = 3 + 7 * k by exact hlayer]
    simpa using (by decide : Nat.Coprime 3 7)
  have hcopTwo : Nat.Coprime N 2 := by
    dsimp [N]
    simp
  refine ⟨N, ?_, hnonrep, hcopSeven.mul_right hcopTwo, ?_⟩
  · dsimp [N]
    have : 0 < 2 * D ^ 6 := by positivity
    omega
  · exact one_add_two_sixth_coprime_self D

theorem erdos1110Conclusion_4_3 :
    Apiros1110Conclusion 4 3 :=
  infinite_pairwise_nonrep_of_freshExtensionProvider freshExtensionProvider_4_3

theorem erdos1110Conclusion_7_2 :
    Apiros1110Conclusion 7 2 :=
  infinite_pairwise_nonrep_of_freshExtensionProvider freshExtensionProvider_7_2

end Apiros1110

end

-- ===== source module Apiros1110.Exceptional =====

section

/-
# Exceptional seed certificates
-/

namespace Apiros1110

theorem corrected_embedding_bound_for_examples :
    (5 ^ 2 < 2 ^ 5 ∧ 3 * 2 ^ 5 < 4 * 5 ^ 2) ∧
    (9 ^ 2 < 2 ^ 7 ∧ 5 * 2 ^ 7 < 8 * 9 ^ 2) ∧
    (5 < 3 ^ 2 ∧ 3 ^ 2 < 2 * 5) := by
  decide

theorem supplied_embedding_bound_is_false_for_5_2 :
    ¬ (5 ^ 2 < 2 ^ 5 ∧ 4 * 2 ^ 5 < 3 * 5 ^ 2) := by
  decide

theorem supplied_embedding_bound_is_false_for_9_2 :
    ¬ (9 ^ 2 < 2 ^ 7 ∧ 8 * 2 ^ 7 < 5 * 9 ^ 2) := by
  decide

private theorem one_le_of_pos {n : Nat} (h : 0 < n) : 1 ≤ n :=
  h

private theorem first_coord_zero_of_small_term
    {p q c : Nat} {x : Point}
    (hp : 1 < p)
    (hq : 0 < q)
    (hcp : c < p)
    (hterm : Term p q x ≤ c) :
    x.1 = 0 := by
  by_cases hxzero : x.1 = 0
  · exact hxzero
  have hxpos : 0 < x.1 := Nat.pos_of_ne_zero hxzero
  have hile : 1 ≤ x.1 := one_le_of_pos hxpos
  have hp_pos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hp_le_pow : p ≤ p ^ x.1 := by
    simpa using Nat.pow_le_pow_right hp_pos hile
  have hqpow_pos : 0 < q ^ x.2 := (Nat.pow_pos hq : 0 < q ^ x.2)
  have hp_le_term : p ≤ Term p q x := by
    exact Nat.le_trans hp_le_pow (Nat.le_mul_of_pos_right _ hqpow_pos)
  exact False.elim ((Nat.not_le_of_gt hcp) (Nat.le_trans hp_le_term hterm))

private theorem second_point_contradiction
    {A_tail : List Point} {x y : Point}
    (hanti : IsAntichain (x :: y :: A_tail))
    (hx0 : x.1 = 0)
    (hy0 : y.1 = 0) :
    False := by
  have hnodup : (x :: y :: A_tail).Nodup := hanti.1
  have hx_not_mem_tail : ¬ x ∈ y :: A_tail := (List.nodup_cons.mp hnodup).1
  have hxy_ne : x ≠ y := by
    intro hxy
    exact hx_not_mem_tail (by rw [hxy]; exact List.mem_cons_self)
  have hle_or : x.2 ≤ y.2 ∨ y.2 ≤ x.2 := Nat.le_total x.2 y.2
  cases hle_or with
  | inl hxy2 =>
      have hcoord : CoordLe x y := by
        constructor
        · simp [hx0, hy0]
        · exact hxy2
      exact hanti.2 List.mem_cons_self
        (List.mem_cons_of_mem x List.mem_cons_self) hxy_ne hcoord
  | inr hyx2 =>
      have hcoord : CoordLe y x := by
        constructor
        · simp [hx0, hy0]
        · exact hyx2
      exact hanti.2 (List.mem_cons_of_mem x List.mem_cons_self)
        List.mem_cons_self (fun hyx => hxy_ne hyx.symm) hcoord

theorem c_lt_p_and_not_q_power_nonrepresentable
    {p q c : Nat}
    (hp : 1 < p)
    (hq : 0 < q)
    (hcpos : 0 < c)
    (hcp : c < p)
    (hnotpow : ∀ j : Nat, c ≠ q ^ j) :
    Nonrepresentable p q c := by
  intro hrepr
  rcases hrepr with ⟨A, hA, hsum⟩
  cases A with
  | nil =>
      change 0 = c at hsum
      exact Nat.ne_of_gt hcpos hsum.symm
  | cons x xs =>
      have hx_mem : x ∈ x :: xs := List.mem_cons_self
      have hx_le_c : Term p q x ≤ c := by
        rw [← hsum]
        exact mem_term_le_sum hx_mem
      have hx0 : x.1 = 0 := first_coord_zero_of_small_term hp hq hcp hx_le_c
      cases xs with
      | nil =>
          change Term p q x = c at hsum
          have : c = q ^ x.2 := by
            rw [← hsum]
            dsimp [Term]
            rw [hx0]
            simp
          exact hnotpow x.2 this
      | cons y ys =>
          have hy_mem : y ∈ x :: y :: ys :=
            List.mem_cons_of_mem x List.mem_cons_self
          have hy_le_c : Term p q y ≤ c := by
            rw [← hsum]
            exact mem_term_le_sum hy_mem
          have hy0 : y.1 = 0 := first_coord_zero_of_small_term hp hq hcp hy_le_c
          exact second_point_contradiction hA hx0 hy0

private theorem two_pow_ne_three : ∀ j : Nat, 3 ≠ 2 ^ j
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      intro h
      have hle : 4 ≤ 2 ^ (n + 2) := by
        have hpow : 2 ^ 2 ≤ 2 ^ (n + 2) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (by simp : 2 ≤ n + 2)
        simpa using hpow
      rw [← h] at hle
      exact (by decide : ¬ 4 ≤ 3) hle

private theorem two_pow_ne_five : ∀ j : Nat, 5 ≠ 2 ^ j
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | n + 3 => by
      intro h
      have hle : 8 ≤ 2 ^ (n + 3) := by
        have hpow : 2 ^ 3 ≤ 2 ^ (n + 3) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (by simp : 3 ≤ n + 3)
        simpa using hpow
      rw [← h] at hle
      exact (by decide : ¬ 8 ≤ 5) hle

private theorem three_pow_ne_two : ∀ j : Nat, 2 ≠ 3 ^ j
  | 0 => by decide
  | n + 1 => by
      intro h
      have hle : 3 ≤ 3 ^ (n + 1) := by
        have hpow : 3 ^ 1 ≤ 3 ^ (n + 1) :=
          Nat.pow_le_pow_right (by decide : 0 < 3) (by simp : 1 ≤ n + 1)
        simpa using hpow
      rw [← h] at hle
      exact (by decide : ¬ 3 ≤ 2) hle

theorem c3_nonrepresentable_5_2 : Nonrepresentable 5 2 3 := by
  apply c_lt_p_and_not_q_power_nonrepresentable
  · decide
  · decide
  · decide
  · decide
  · exact two_pow_ne_three

theorem c5_nonrepresentable_9_2 : Nonrepresentable 9 2 5 := by
  apply c_lt_p_and_not_q_power_nonrepresentable
  · decide
  · decide
  · decide
  · decide
  · exact two_pow_ne_five

theorem c2_nonrepresentable_5_3 : Nonrepresentable 5 3 2 := by
  apply c_lt_p_and_not_q_power_nonrepresentable
  · decide
  · decide
  · decide
  · decide
  · exact three_pow_ne_two

theorem support_4_within_10 : SupportCoprimeWithin 4 10 := by
  intro D hD
  have hD10 : Nat.Coprime D (2 * 5) := by simpa using hD
  have hD2 : Nat.Coprime D 2 := (Nat.coprime_mul_iff_right.mp hD10).1
  have h2D : Nat.Coprime 2 D := Nat.Coprime.symm hD2
  simpa using h2D.pow_left 2

theorem support_6_within_18 : SupportCoprimeWithin 6 18 := by
  intro D hD
  have hD6 : Nat.Coprime D 6 := by
    have h : Nat.Coprime D (6 * 3) := by simpa using hD
    exact (Nat.coprime_mul_iff_right.mp h).1
  exact Nat.Coprime.symm hD6

theorem support_3_within_15 : SupportCoprimeWithin 3 15 := by
  intro D hD
  have hD3 : Nat.Coprime D 3 := by
    have h : Nat.Coprime D (3 * 5) := by simpa using hD
    exact (Nat.coprime_mul_iff_right.mp h).1
  exact Nat.Coprime.symm hD3

theorem validBases_5_2 : ValidBases 5 2 where
  one_lt_p := by decide
  one_lt_q := by decide
  coprime := by decide

theorem validBases_9_2 : ValidBases 9 2 where
  one_lt_p := by decide
  one_lt_q := by decide
  coprime := by decide

theorem validBases_5_3 : ValidBases 5 3 where
  one_lt_p := by decide
  one_lt_q := by decide
  coprime := by decide

theorem seed_5_2 : GoodSeed 5 2 3 where
  c_pos := by decide
  c_lt := by decide
  nonrep := c3_nonrepresentable_5_2
  coprime_pq := by decide
  support_succ := by simpa using support_4_within_10

theorem seed_9_2 : GoodSeed 9 2 5 where
  c_pos := by decide
  c_lt := by decide
  nonrep := c5_nonrepresentable_9_2
  coprime_pq := by decide
  support_succ := by simpa using support_6_within_18

theorem seed_5_3 : GoodSeed 5 3 2 where
  c_pos := by decide
  c_lt := by decide
  nonrep := c2_nonrepresentable_5_3
  coprime_pq := by decide
  support_succ := by simpa using support_3_within_15

theorem exceptional_5_2_from_goodSeed_amplification
    (amplify : GoodSeedAmplification) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  amplify validBases_5_2 seed_5_2

theorem exceptional_9_2_from_goodSeed_amplification
    (amplify : GoodSeedAmplification) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  amplify validBases_9_2 seed_9_2

theorem exceptional_5_3_from_goodSeed_amplification
    (amplify : GoodSeedAmplification) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  amplify validBases_5_3 seed_5_3

theorem exceptional_cases_from_goodSeed_amplification
    (amplify : GoodSeedAmplification) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) := by
  exact ⟨exceptional_5_2_from_goodSeed_amplification amplify,
    exceptional_9_2_from_goodSeed_amplification amplify,
    exceptional_5_3_from_goodSeed_amplification amplify⟩

theorem exceptional_5_2_from_freshExtension_amplification
    (freshAmp : FreshExtensionAmplification) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  exceptional_5_2_from_goodSeed_amplification
    (goodSeedAmplification_of_freshExtensionAmplification freshAmp)

theorem exceptional_9_2_from_freshExtension_amplification
    (freshAmp : FreshExtensionAmplification) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  exceptional_9_2_from_goodSeed_amplification
    (goodSeedAmplification_of_freshExtensionAmplification freshAmp)

theorem exceptional_5_3_from_freshExtension_amplification
    (freshAmp : FreshExtensionAmplification) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  exceptional_5_3_from_goodSeed_amplification
    (goodSeedAmplification_of_freshExtensionAmplification freshAmp)

theorem exceptional_cases_from_freshExtension_amplification
    (freshAmp : FreshExtensionAmplification) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  exceptional_cases_from_goodSeed_amplification
    (goodSeedAmplification_of_freshExtensionAmplification freshAmp)

theorem exceptional_5_2_from_period_window
    (period : PeriodProvider 5 2)
    (window : PowerWindowProvider 5 2 3) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  goodSeedAmplification_of_period_window_embedding
    validBases_5_2 seed_5_2 period window
    (embeddingProvider_core validBases_5_2 seed_5_2)

theorem exceptional_9_2_from_period_window
    (period : PeriodProvider 9 2)
    (window : PowerWindowProvider 9 2 5) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  goodSeedAmplification_of_period_window_embedding
    validBases_9_2 seed_9_2 period window
    (embeddingProvider_core validBases_9_2 seed_9_2)

theorem exceptional_5_3_from_period_window
    (period : PeriodProvider 5 3)
    (window : PowerWindowProvider 5 3 2) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  goodSeedAmplification_of_period_window_embedding
    validBases_5_3 seed_5_3 period window
    (embeddingProvider_core validBases_5_3 seed_5_3)

theorem exceptional_cases_from_period_window
    (period_5_2 : PeriodProvider 5 2)
    (window_5_2 : PowerWindowProvider 5 2 3)
    (period_9_2 : PeriodProvider 9 2)
    (window_9_2 : PowerWindowProvider 9 2 5)
    (period_5_3 : PeriodProvider 5 3)
    (window_5_3 : PowerWindowProvider 5 3 2) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  ⟨exceptional_5_2_from_period_window period_5_2 window_5_2,
    exceptional_9_2_from_period_window period_9_2 window_9_2,
    exceptional_5_3_from_period_window period_5_3 window_5_3⟩

theorem exceptional_5_2_from_basic_period_window
    (period : BasicPeriodProvider 5 2)
    (window : PowerWindowProvider 5 2 3) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  exceptional_5_2_from_period_window
    (periodProvider_of_basicPeriodProvider period) window

theorem exceptional_9_2_from_basic_period_window
    (period : BasicPeriodProvider 9 2)
    (window : PowerWindowProvider 9 2 5) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  exceptional_9_2_from_period_window
    (periodProvider_of_basicPeriodProvider period) window

theorem exceptional_5_3_from_basic_period_window
    (period : BasicPeriodProvider 5 3)
    (window : PowerWindowProvider 5 3 2) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  exceptional_5_3_from_period_window
    (periodProvider_of_basicPeriodProvider period) window

theorem exceptional_cases_from_basic_period_window
    (period_5_2 : BasicPeriodProvider 5 2)
    (window_5_2 : PowerWindowProvider 5 2 3)
    (period_9_2 : BasicPeriodProvider 9 2)
    (window_9_2 : PowerWindowProvider 9 2 5)
    (period_5_3 : BasicPeriodProvider 5 3)
    (window_5_3 : PowerWindowProvider 5 3 2) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  ⟨exceptional_5_2_from_basic_period_window period_5_2 window_5_2,
    exceptional_9_2_from_basic_period_window period_9_2 window_9_2,
    exceptional_5_3_from_basic_period_window period_5_3 window_5_3⟩

theorem exceptional_5_2_from_base_period_window
    (period5 : CoprimeBasePeriodProvider 5)
    (period2 : CoprimeBasePeriodProvider 2)
    (window : PowerWindowProvider 5 2 3) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  exceptional_5_2_from_period_window
    (periodProvider_of_coprimeBasePeriodProviders period5 period2) window

theorem exceptional_9_2_from_base_period_window
    (period9 : CoprimeBasePeriodProvider 9)
    (period2 : CoprimeBasePeriodProvider 2)
    (window : PowerWindowProvider 9 2 5) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  exceptional_9_2_from_period_window
    (periodProvider_of_coprimeBasePeriodProviders period9 period2) window

theorem exceptional_5_3_from_base_period_window
    (period5 : CoprimeBasePeriodProvider 5)
    (period3 : CoprimeBasePeriodProvider 3)
    (window : PowerWindowProvider 5 3 2) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  exceptional_5_3_from_period_window
    (periodProvider_of_coprimeBasePeriodProviders period5 period3) window

theorem exceptional_cases_from_base_period_window
    (period2 : CoprimeBasePeriodProvider 2)
    (period3 : CoprimeBasePeriodProvider 3)
    (period5 : CoprimeBasePeriodProvider 5)
    (period9 : CoprimeBasePeriodProvider 9)
    (window_5_2 : PowerWindowProvider 5 2 3)
    (window_9_2 : PowerWindowProvider 9 2 5)
    (window_5_3 : PowerWindowProvider 5 3 2) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  ⟨exceptional_5_2_from_base_period_window period5 period2 window_5_2,
    exceptional_9_2_from_base_period_window period9 period2 window_9_2,
    exceptional_5_3_from_base_period_window period5 period3 window_5_3⟩

theorem exceptional_5_2_from_window
    (window : PowerWindowProvider 5 2 3) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  exceptional_5_2_from_period_window
    (periodProvider_of_pos (p := 5) (q := 2) (by decide) (by decide))
    window

theorem exceptional_9_2_from_window
    (window : PowerWindowProvider 9 2 5) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  exceptional_9_2_from_period_window
    (periodProvider_of_pos (p := 9) (q := 2) (by decide) (by decide))
    window

theorem exceptional_5_3_from_window
    (window : PowerWindowProvider 5 3 2) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  exceptional_5_3_from_period_window
    (periodProvider_of_pos (p := 5) (q := 3) (by decide) (by decide))
    window

theorem exceptional_cases_from_window
    (window_5_2 : PowerWindowProvider 5 2 3)
    (window_9_2 : PowerWindowProvider 9 2 5)
    (window_5_3 : PowerWindowProvider 5 3 2) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  ⟨exceptional_5_2_from_window window_5_2,
    exceptional_9_2_from_window window_9_2,
    exceptional_5_3_from_window window_5_3⟩

theorem exceptional_cases_from_window_amplification
    (amp : WindowAmplification) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  exceptional_cases_from_goodSeed_amplification
    (goodSeedAmplification_of_windowAmplification amp)

theorem exceptional_cases_from_periodWindow_amplification
    (amp : PeriodWindowAmplification) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  exceptional_cases_from_goodSeed_amplification
    (goodSeedAmplification_of_periodWindowAmplification amp)

theorem exceptional_cases_from_periodWindowLowRow_amplification
    (amp : PeriodWindowLowRowAmplification) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  exceptional_cases_from_goodSeed_amplification
    (goodSeedAmplification_of_periodWindowLowRowAmplification amp)

end Apiros1110

end

-- ===== source module Apiros1110.YuChenBridge =====

section

/-
# Yu-Chen range bridge
-/

namespace Apiros1110

def MissingPair (p q : Nat) : Prop :=
  (p = 5 ∧ q = 2) ∨ (p = 9 ∧ q = 2) ∨ (p = 5 ∧ q = 3)

def YuChenRange (p q : Nat) : Prop :=
  q > 3 ∨ (q = 3 ∧ p ≠ 5) ∨ (q = 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 9)

private theorem nat_cases_ge2_le3 {q : Nat} (hq : q ≥ 2) (hqle : q ≤ 3) :
    q = 2 ∨ q = 3 := by
  cases q with
  | zero => exact False.elim ((by decide : ¬ 0 ≥ 2) hq)
  | succ q1 =>
      cases q1 with
      | zero => exact False.elim ((by decide : ¬ 1 ≥ 2) hq)
      | succ q2 =>
          cases q2 with
          | zero => exact Or.inl rfl
          | succ q3 =>
              cases q3 with
              | zero => exact Or.inr rfl
              | succ q4 =>
                  have h1 : Nat.succ (Nat.succ (Nat.succ q4)) ≤ 2 :=
                    Nat.le_of_succ_le_succ hqle
                  have h2 : Nat.succ (Nat.succ q4) ≤ 1 :=
                    Nat.le_of_succ_le_succ h1
                  have h3 : Nat.succ q4 ≤ 0 :=
                    Nat.le_of_succ_le_succ h2
                  exact False.elim (Nat.not_succ_le_zero q4 h3)

theorem range_split
    {p q : Nat}
    (hpq : p > q)
    (hq : q ≥ 2)
    (hnot32 : ¬ (p = 3 ∧ q = 2)) :
    YuChenRange p q ∨ MissingPair p q := by
  by_cases hq3lt : q > 3
  · exact Or.inl (Or.inl hq3lt)
  · have hqle3 : q ≤ 3 := Nat.le_of_not_gt hq3lt
    cases nat_cases_ge2_le3 hq hqle3 with
    | inl hq2 =>
        subst q
        by_cases hp3 : p = 3
        · exact False.elim (hnot32 ⟨hp3, rfl⟩)
        · by_cases hp5 : p = 5
          · exact Or.inr (Or.inl ⟨hp5, rfl⟩)
          · by_cases hp9 : p = 9
            · exact Or.inr (Or.inr (Or.inl ⟨hp9, rfl⟩))
            · exact Or.inl (Or.inr (Or.inr ⟨rfl, hp3, hp5, hp9⟩))
    | inr hq3 =>
        subst q
        by_cases hp5 : p = 5
        · exact Or.inr (Or.inr (Or.inr ⟨hp5, rfl⟩))
        · exact Or.inl (Or.inr (Or.inl ⟨rfl, hp5⟩))

theorem erdos1110_unconditional_bridge
    (yuChen : ∀ ⦃p q : Nat⦄,
      Nat.Coprime p q → p > q → q ≥ 2 → YuChenRange p q →
        Apiros1110Conclusion p q)
    (exceptional : ∀ ⦃p q : Nat⦄,
      Nat.Coprime p q → p > q → q ≥ 2 → MissingPair p q →
        Apiros1110Conclusion p q)
    {p q : Nat}
    (hpq_coprime : Nat.Coprime p q)
    (hpq : p > q)
    (hq : q ≥ 2)
    (hnot32 : ¬ (p = 3 ∧ q = 2)) :
    Apiros1110Conclusion p q := by
  cases range_split hpq hq hnot32 with
  | inl hYC => exact yuChen hpq_coprime hpq hq hYC
  | inr hMissing => exact exceptional hpq_coprime hpq hq hMissing

end Apiros1110

end

-- ===== source module Apiros1110.PowerWindow =====

section

namespace Apiros1110

open Set
open scoped Topology

noncomputable section

private theorem coprime_pow_eq_pow_absurd
    {p q a b : Nat}
    (hp : 1 < p)
    (hc : Nat.Coprime p q)
    (hb : 0 < b)
    (h : p ^ b = q ^ a) :
    False := by
  have hcop : Nat.Coprime (p ^ b) (q ^ a) :=
    (hc.pow_left b).pow_right a
  have hself : Nat.Coprime (p ^ b) (p ^ b) := by
    simpa [h] using hcop
  have hgcd : Nat.gcd (p ^ b) (p ^ b) = 1 :=
    Nat.Coprime.gcd_eq_one hself
  rw [Nat.gcd_self] at hgcd
  have hpgt : 1 < p ^ b :=
    Nat.one_lt_pow (Nat.ne_of_gt hb) hp
  omega

theorem irrational_log_nat_div_log_nat
    {p q : Nat}
    (hp : 1 < p)
    (hq : 1 < q)
    (hc : Nat.Coprime p q) :
    Irrational (Real.log (p : Real) / Real.log (q : Real)) := by
  intro hrat
  rcases hrat with ⟨r, hr⟩
  have hpR : (1 : Real) < p := by exact_mod_cast hp
  have hqR : (1 : Real) < q := by exact_mod_cast hq
  have hlogp_pos : 0 < Real.log (p : Real) := Real.log_pos hpR
  have hlogq_pos : 0 < Real.log (q : Real) := Real.log_pos hqR
  have hratio_pos : 0 < Real.log (p : Real) / Real.log (q : Real) :=
    div_pos hlogp_pos hlogq_pos
  have hr_pos : 0 < r := by
    exact (Rat.cast_pos (K := Real)).mp (by simpa [hr] using hratio_pos)
  have hnum_pos : 0 < r.num := by
    exact (Rat.num_pos (a := r)).mpr hr_pos
  have hden_pos : 0 < r.den := r.den_pos
  have hden_ne : ((r.den : Nat) : Real) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hlogq_ne : Real.log (q : Real) ≠ 0 := hlogq_pos.ne'
  have hratio :
      (r.num : Real) / (r.den : Real) =
        Real.log (p : Real) / Real.log (q : Real) := by
    simpa [Rat.cast_def] using hr
  have hmul :
      (r.den : Real) * Real.log (p : Real) =
        (r.num : Real) * Real.log (q : Real) := by
    field_simp [hden_ne, hlogq_ne] at hratio
    linarith
  let a : Nat := r.num.natAbs
  have hnum_nonneg : 0 ≤ r.num := le_of_lt hnum_pos
  have hnum_cast_int : ((a : Nat) : Int) = r.num := by
    dsimp [a]
    exact Int.natAbs_of_nonneg hnum_nonneg
  have hnum_cast_real : (a : Real) = (r.num : Real) := by
    exact_mod_cast hnum_cast_int
  have hlogeq :
      Real.log ((p : Real) ^ r.den) = Real.log ((q : Real) ^ a) := by
    rw [Real.log_pow (p : Real) r.den, Real.log_pow (q : Real) a]
    rw [hnum_cast_real]
    exact hmul
  have hp_pow_pos : 0 < (p : Real) ^ r.den := pow_pos (lt_trans zero_lt_one hpR) _
  have hq_pow_pos : 0 < (q : Real) ^ a := pow_pos (lt_trans zero_lt_one hqR) _
  have hpow_real : (p : Real) ^ r.den = (q : Real) ^ a :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr hp_pow_pos) (Set.mem_Ioi.mpr hq_pow_pos) hlogeq
  have hpow_nat : p ^ r.den = q ^ a := by
    apply Nat.cast_injective (R := Real)
    simpa only [Nat.cast_pow] using hpow_real
  exact coprime_pow_eq_pow_absurd hp hc hden_pos hpow_nat

private theorem circle_arc_open
    {δ : Real} (hδlt : δ < 1) :
    IsOpen (((↑) : Real → AddCircle (1 : Real)) '' Set.Ioo (1 - δ) 1) := by
  let e : OpenPartialHomeomorph Real (AddCircle (1 : Real)) :=
    AddCircle.openPartialHomeomorphCoe (p := (1 : Real)) (a := 0)
  have hsub : Set.Ioo (1 - δ) 1 ⊆ e.source := by
    intro x hx
    change x ∈ Set.Ioo (0 : Real) (0 + 1)
    constructor
    · linarith [hx.1, hδlt]
    · simpa using hx.2
  have hopen : IsOpen (e '' Set.Ioo (1 - δ) 1) :=
    e.isOpen_image_of_subset_source isOpen_Ioo hsub
  simpa [e, AddCircle.openPartialHomeomorphCoe] using hopen

theorem exists_pos_nat_one_sided_sub_mul_lt
    {α ε : Real}
    (hirr : Irrational α)
    (hαpos : 0 < α)
    (hε : 0 < ε) :
    ∃ n m : Nat,
      0 < n ∧ 0 < m ∧
      0 < (m : Real) - (n : Real) * α ∧
      (m : Real) - (n : Real) * α < ε := by
  let δ : Real := min ε (1 / 2)
  have hδpos : 0 < δ := lt_min hε (by norm_num)
  have hδleε : δ ≤ ε := min_le_left _ _
  have hδlt1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let U : Set (AddCircle (1 : Real)) :=
    ((↑) : Real → AddCircle (1 : Real)) '' Set.Ioo (1 - δ) 1
  have hUopen : IsOpen U := circle_arc_open hδlt1
  have hUne : U.Nonempty := by
    refine ⟨((1 - δ / 2 : Real) : AddCircle (1 : Real)), ?_⟩
    refine ⟨1 - δ / 2, ?_, rfl⟩
    constructor <;> linarith
  have hdZ : DenseRange (fun z : Int => z • (α : AddCircle (1 : Real))) := by
    simpa using
      (AddCircle.denseRange_zsmul_coe_iff (a := α) (p := (1 : Real))).mpr
        (by simpa using hirr)
  have hdN : DenseRange (fun n : Nat => n • (α : AddCircle (1 : Real))) :=
    (_root_.denseRange_zsmul_iff_nsmul.mp hdZ)
  rcases hdN.exists_mem_open hUopen hUne with ⟨n, hnU⟩
  rcases hnU with ⟨x, hxI, hxEq⟩
  have hxIco : x ∈ Set.Ico (0 : Real) (0 + 1) := by
    constructor
    · have hx0 : 0 < x := by
        have hleft : 1 - δ < x := hxI.1
        linarith
      exact le_of_lt hx0
    · simpa using hxI.2
  have hzero_not : (x : AddCircle (1 : Real)) ≠ 0 := by
    intro hxzero
    have hxeq0 : x = 0 := by
      have h0mem : (0 : Real) ∈ Set.Ico (0 : Real) (0 + 1) := by
        constructor <;> norm_num
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hxIco h0mem).mp (by simpa using hxzero)
    have hx0 : 0 < x := by
      have hleft : 1 - δ < x := hxI.1
      linarith
    linarith
  have hn_pos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have : (x : AddCircle (1 : Real)) = 0 := by
      simpa [hn0] using hxEq
    exact hzero_not this
  have hxEq' : (x : AddCircle (1 : Real)) =
      (((n : Real) * α : Real) : AddCircle (1 : Real)) := by
    calc
      (x : AddCircle (1 : Real)) = n • (α : AddCircle (1 : Real)) := hxEq
      _ = (((n • α : Real)) : AddCircle (1 : Real)) := by
        exact (AddCircle.coe_nsmul (p := (1 : Real)) (n := n) (x := α)).symm
      _ = (((n : Real) * α : Real) : AddCircle (1 : Real)) := by
        simp [nsmul_eq_mul]
  have hzero :
      (((x - (n : Real) * α : Real)) : AddCircle (1 : Real)) = 0 := by
    rw [AddCircle.coe_sub]
    exact sub_eq_zero.mpr hxEq'
  rcases (AddCircle.coe_eq_zero_iff (p := (1 : Real)) (x := x - (n : Real) * α)).mp hzero
    with ⟨z, hz⟩
  have hzreal : (z : Real) = x - (n : Real) * α := by
    simpa [zsmul_eq_mul] using hz
  have hnα_nonneg : 0 ≤ (n : Real) * α :=
    mul_nonneg (Nat.cast_nonneg n) (le_of_lt hαpos)
  have hzlt1R : (z : Real) < 1 := by
    rw [hzreal]
    linarith [hxI.2, hnα_nonneg]
  have hzlt1 : z < (1 : Int) := by exact_mod_cast hzlt1R
  have hzle0 : z ≤ 0 := by omega
  have hmInt_nonneg : 0 ≤ (1 : Int) - z := by omega
  let m : Nat := ((1 : Int) - z).toNat
  have hmcast : (m : Real) = (((1 : Int) - z : Int) : Real) := by
    dsimp [m]
    exact_mod_cast (Int.toNat_of_nonneg hmInt_nonneg)
  have hdiff : (m : Real) - (n : Real) * α = 1 - x := by
    calc
      (m : Real) - (n : Real) * α =
          (((1 : Int) - z : Int) : Real) - (n : Real) * α := by
            rw [hmcast]
      _ = (1 - (z : Real)) - (n : Real) * α := by norm_num
      _ = 1 - x := by
            rw [hzreal]
            ring
  have hdiff_pos : 0 < (m : Real) - (n : Real) * α := by
    rw [hdiff]
    linarith [hxI.2]
  have hm_pos : 0 < m := by
    have hnα_pos : 0 < (n : Real) * α :=
      mul_pos (Nat.cast_pos.mpr hn_pos) hαpos
    have hmR : 0 < (m : Real) := by linarith
    exact Nat.cast_pos.mp hmR
  refine ⟨n, m, hn_pos, hm_pos, hdiff_pos, ?_⟩
  rw [hdiff]
  have : 1 - x < δ := by linarith [hxI.1]
  exact lt_of_lt_of_le this hδleε

private theorem real_pow_lt_of_log_lt
    {p q a M : Nat}
    (hp : 1 < p)
    (hq : 1 < q)
    (hlog : (a : Real) * Real.log (p : Real) < (M : Real) * Real.log (q : Real)) :
    p ^ a < q ^ M := by
  have hpRpos : 0 < (p : Real) := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hp)
  have hqRpos : 0 < (q : Real) := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hq)
  have hpowa_pos : 0 < (p : Real) ^ a := pow_pos hpRpos _
  have hqM_pos : 0 < (q : Real) ^ M := pow_pos hqRpos _
  have hreal : (p : Real) ^ a < (q : Real) ^ M := by
    rw [← Real.log_lt_log_iff hpowa_pos hqM_pos]
    rw [Real.log_pow, Real.log_pow]
    exact hlog
  exact_mod_cast hreal

theorem powerWindowProvider_of_validBases_goodSeed
    {p q c : Nat}
    (hb : ValidBases p q)
    (hs : GoodSeed p q c) :
    PowerWindowProvider p q c := by
  intro L hL
  let rho : Real := ((p - 1 : Nat) : Real) / (c : Real)
  have hcRpos : 0 < (c : Real) := by exact_mod_cast hs.c_pos
  have hρgt1 : 1 < rho := by
    have hc_ltR : (c : Real) < ((p - 1 : Nat) : Real) := by exact_mod_cast hs.c_lt
    rw [one_lt_div hcRpos]
    simpa [rho] using hc_ltR
  have hlogρ_pos : 0 < Real.log rho := Real.log_pos hρgt1
  have hpR : (1 : Real) < p := by exact_mod_cast hb.one_lt_p
  have hqR : (1 : Real) < q := by exact_mod_cast hb.one_lt_q
  have hlogp_pos : 0 < Real.log (p : Real) := Real.log_pos hpR
  have hlogq_pos : 0 < Real.log (q : Real) := Real.log_pos hqR
  let α : Real := Real.log (p : Real) / Real.log (q : Real)
  have hαpos : 0 < α := div_pos hlogp_pos hlogq_pos
  have hαirr : Irrational α :=
    irrational_log_nat_div_log_nat hb.one_lt_p hb.one_lt_q hb.coprime
  let eps : Real := Real.log rho / ((L : Real) * Real.log (q : Real))
  have hLposR : 0 < (L : Real) := Nat.cast_pos.mpr hL
  have heps_pos : 0 < eps :=
    div_pos hlogρ_pos (mul_pos hLposR hlogq_pos)
  rcases exists_pos_nat_one_sided_sub_mul_lt hαirr hαpos heps_pos with
    ⟨n, m, hn_pos, hm_pos, hdiff_pos, hdiff_lt⟩
  let a : Nat := L * n
  let M : Nat := L * m
  refine ⟨a, M, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos hL hn_pos
  · exact Nat.mul_pos hL hm_pos
  · exact ⟨n, rfl⟩
  · exact ⟨m, rfl⟩
  · have hleft0 :
        (n : Real) * (Real.log (p : Real) / Real.log (q : Real)) < (m : Real) :=
      sub_pos.mp (by simpa [α] using hdiff_pos)
    have hleft1 : (n : Real) * Real.log (p : Real) <
        (m : Real) * Real.log (q : Real) := by
      have h := mul_lt_mul_of_pos_right hleft0 hlogq_pos
      have hcancel :
          (Real.log (p : Real) / Real.log (q : Real)) * Real.log (q : Real) =
            Real.log (p : Real) :=
        div_mul_cancel₀ _ hlogq_pos.ne'
      calc
        (n : Real) * Real.log (p : Real) =
            (n : Real) * ((Real.log (p : Real) / Real.log (q : Real)) *
              Real.log (q : Real)) := by rw [hcancel]
        _ = ((n : Real) * (Real.log (p : Real) / Real.log (q : Real))) *
              Real.log (q : Real) := by ring
        _ < (m : Real) * Real.log (q : Real) := h
    have hleftlog : (a : Real) * Real.log (p : Real) <
        (M : Real) * Real.log (q : Real) := by
      have h := mul_lt_mul_of_pos_left hleft1 hLposR
      dsimp [a, M]
      simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h
    exact real_pow_lt_of_log_lt hb.one_lt_p hb.one_lt_q hleftlog
  · have hden_pos : 0 < (L : Real) * Real.log (q : Real) :=
      mul_pos hLposR hlogq_pos
    have hupper0 :
        ((m : Real) - (n : Real) * (Real.log (p : Real) / Real.log (q : Real))) *
            ((L : Real) * Real.log (q : Real)) < Real.log rho := by
      have h := mul_lt_mul_of_pos_right (by simpa [α, eps] using hdiff_lt) hden_pos
      have hcancel :
          Real.log rho / ((L : Real) * Real.log (q : Real)) *
            ((L : Real) * Real.log (q : Real)) = Real.log rho :=
        div_mul_cancel₀ _ hden_pos.ne'
      simpa [eps, hcancel] using h
    have hupper :
        (M : Real) * Real.log (q : Real) -
            (a : Real) * Real.log (p : Real) < Real.log rho := by
      have hcancel :
          (Real.log (p : Real) / Real.log (q : Real)) * Real.log (q : Real) =
            Real.log (p : Real) :=
        div_mul_cancel₀ _ hlogq_pos.ne'
      have hexpr :
          ((m : Real) - (n : Real) *
              (Real.log (p : Real) / Real.log (q : Real))) *
              ((L : Real) * Real.log (q : Real)) =
            (M : Real) * Real.log (q : Real) -
              (a : Real) * Real.log (p : Real) := by
        dsimp [a, M]
        rw [Nat.cast_mul, Nat.cast_mul]
        field_simp [hlogq_pos.ne']
      calc
        (M : Real) * Real.log (q : Real) -
            (a : Real) * Real.log (p : Real) =
              ((m : Real) - (n : Real) *
                (Real.log (p : Real) / Real.log (q : Real))) *
                ((L : Real) * Real.log (q : Real)) := hexpr.symm
        _ < Real.log rho := hupper0
    have hpRpos : 0 < (p : Real) := lt_trans zero_lt_one hpR
    have hqRpos : 0 < (q : Real) := lt_trans zero_lt_one hqR
    have hpowa_pos : 0 < (p : Real) ^ a := pow_pos hpRpos _
    have hqM_pos : 0 < (q : Real) ^ M := pow_pos hqRpos _
    have hlog_ratio :
        Real.log (((q : Real) ^ M) / ((p : Real) ^ a)) < Real.log rho := by
      rw [Real.log_div hqM_pos.ne' hpowa_pos.ne', Real.log_pow, Real.log_pow]
      exact hupper
    have hratio :
        ((q : Real) ^ M) / ((p : Real) ^ a) < rho :=
      (Real.log_lt_log_iff (div_pos hqM_pos hpowa_pos) (lt_trans zero_lt_one hρgt1)).mp
        hlog_ratio
    have hq_lt : (q : Real) ^ M < rho * (p : Real) ^ a := by
      have h := mul_lt_mul_of_pos_right hratio hpowa_pos
      field_simp [hpowa_pos.ne'] at h
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hright_real :
        (c : Real) * (q : Real) ^ M <
          ((p - 1 : Nat) : Real) * (p : Real) ^ a := by
      calc
        (c : Real) * (q : Real) ^ M
            < (c : Real) * (rho * (p : Real) ^ a) :=
              mul_lt_mul_of_pos_left hq_lt hcRpos
        _ = ((p - 1 : Nat) : Real) * (p : Real) ^ a := by
              dsimp [rho]
              field_simp [hcRpos.ne']
    have hright_cast :
        ((c * q ^ M : Nat) : Real) <
          (((p - 1) * p ^ a : Nat) : Real) := by
      simpa only [Nat.cast_mul, Nat.cast_pow] using hright_real
    exact_mod_cast hright_cast

theorem powerWindow_5_2 : PowerWindowProvider 5 2 3 :=
  powerWindowProvider_of_validBases_goodSeed validBases_5_2 seed_5_2

theorem powerWindow_9_2 : PowerWindowProvider 9 2 5 :=
  powerWindowProvider_of_validBases_goodSeed validBases_9_2 seed_9_2

theorem powerWindow_5_3 : PowerWindowProvider 5 3 2 :=
  powerWindowProvider_of_validBases_goodSeed validBases_5_3 seed_5_3

theorem exceptional_5_2_unconditional :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  exceptional_5_2_from_window powerWindow_5_2

theorem exceptional_9_2_unconditional :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  exceptional_9_2_from_window powerWindow_9_2

theorem exceptional_5_3_unconditional :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  exceptional_5_3_from_window powerWindow_5_3

theorem exceptional_cases_unconditional :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  exceptional_cases_from_window powerWindow_5_2 powerWindow_9_2 powerWindow_5_3

theorem missingPair_unconditional
    {p q : Nat} (hMissing : MissingPair p q) :
    Apiros1110Conclusion p q := by
  rcases hMissing with h52 | hRest
  · rcases h52 with ⟨rfl, rfl⟩
    exact exceptional_5_2_unconditional
  · rcases hRest with h92 | h53
    · rcases h92 with ⟨rfl, rfl⟩
      exact exceptional_9_2_unconditional
    · rcases h53 with ⟨rfl, rfl⟩
      exact exceptional_5_3_unconditional

theorem erdos1110_from_yuChen
    (yuChen : ∀ ⦃p q : Nat⦄,
      Nat.Coprime p q → p > q → q ≥ 2 → YuChenRange p q →
        Apiros1110Conclusion p q)
    {p q : Nat}
    (hpq_coprime : Nat.Coprime p q)
    (hpq : p > q)
    (hq : q ≥ 2)
    (hnot32 : ¬ (p = 3 ∧ q = 2)) :
    Apiros1110Conclusion p q :=
  erdos1110_unconditional_bridge yuChen
    (fun {p q} _ _ _ hMissing =>
      missingPair_unconditional (p := p) (q := q) hMissing)
    hpq_coprime hpq hq hnot32

end

end Apiros1110

end

-- ===== source module Apiros1110.YuChen =====

section

/-
# Unconditional Yu--Chen and all-pairs assembly

This file contains only the final case splits.  The quantitative ranges are
discharged by zero density; `(4,3)` and `(7,2)` use their explicit fresh
extension providers; the three missing pairs use the existing unconditional
exceptional-case theorem.
-/

namespace Apiros1110

/-- Every pair in `YuChenRange` has the stronger pairwise-coprime conclusion. -/
theorem yuChenRange_unconditional
    {p q : Nat}
    (hpq_coprime : Nat.Coprime p q)
    (hpq : p > q)
    (hq : q ≥ 2)
    (hRange : YuChenRange p q) :
    Apiros1110Conclusion p q := by
  rcases hRange with hqgt3 | hq3 | hq2
  · have hb : ValidBases p q :=
      { one_lt_p := by omega
        one_lt_q := by omega
        coprime := hpq_coprime }
    exact erdos1110Conclusion_of_densityZero hb
      (representableDensityZero_of_four_le_lt (by omega) hpq)
  · rcases hq3 with ⟨rfl, hp5⟩
    by_cases hp4 : p = 4
    · subst p
      exact erdos1110Conclusion_4_3
    · have hp6 : p ≠ 6 := by
        intro h
        subst p
        exact (by decide : ¬ Nat.Coprime 6 3) hpq_coprime
      have hp7 : 7 ≤ p := by omega
      have hb : ValidBases p 3 :=
        { one_lt_p := by omega
          one_lt_q := by decide
          coprime := hpq_coprime }
      exact erdos1110Conclusion_of_densityZero hb
        (representableDensityZero_of_seven_le_three hp7)
  · rcases hq2 with ⟨rfl, hp3, hp5, hp9⟩
    by_cases hp7 : p = 7
    · subst p
      exact erdos1110Conclusion_7_2
    · have hp4 : p ≠ 4 := by
        intro h
        subst p
        exact (by decide : ¬ Nat.Coprime 4 2) hpq_coprime
      have hp6 : p ≠ 6 := by
        intro h
        subst p
        exact (by decide : ¬ Nat.Coprime 6 2) hpq_coprime
      have hp8 : p ≠ 8 := by
        intro h
        subst p
        exact (by decide : ¬ Nat.Coprime 8 2) hpq_coprime
      have hp10 : p ≠ 10 := by
        intro h
        subst p
        exact (by decide : ¬ Nat.Coprime 10 2) hpq_coprime
      have hp11 : 11 ≤ p := by omega
      have hb : ValidBases p 2 :=
        { one_lt_p := by omega
          one_lt_q := by decide
          coprime := hpq_coprime }
      exact erdos1110Conclusion_of_densityZero hb
        (representableDensityZero_two_of_eleven_le hp11)

/-- Erdős 1110 for every admissible coprime pair other than `(3,2)`. -/
theorem erdos1110_unconditional
    {p q : Nat}
    (hpq_coprime : Nat.Coprime p q)
    (hpq : p > q)
    (hq : q ≥ 2)
    (hnot32 : ¬ (p = 3 ∧ q = 2)) :
    Apiros1110Conclusion p q := by
  rcases range_split hpq hq hnot32 with hRange | hMissing
  · exact yuChenRange_unconditional hpq_coprime hpq hq hRange
  · exact missingPair_unconditional hMissing

end Apiros1110

end

-- ===== source module Apiros1110.Unordered =====

section

/-
# Erdős 1110 for unordered coprime bases

The main case split normalizes the larger base to the first coordinate.
Swapping the exponent coordinates preserves both the antichain sum and the
same pairwise-coprime nonrepresentable sequence.
-/

namespace Apiros1110

/-- A witness sequence also works after the two bases are exchanged. -/
theorem erdos1110Conclusion_swap {p q : Nat}
    (h : Apiros1110Conclusion p q) : Apiros1110Conclusion q p := by
  rcases h with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  constructor
  · intro n
    rcases hf.1 n with ⟨hpos, hnonrep, hcop⟩
    refine ⟨hpos, ?_, ?_⟩
    · intro hrep
      exact hnonrep (representable_swap hrep)
    · simpa [Nat.mul_comm] using hcop
  · intro m n hne
    exact hf.2 hne

/-- The unordered version: every coprime pair of bases at least two, apart
from `{2,3}`, has an infinite pairwise-coprime nonrepresentable sequence. -/
theorem erdos1110_unordered
    {p q : Nat}
    (hpq_coprime : Nat.Coprime p q)
    (hp : 2 ≤ p)
    (hq : 2 ≤ q)
    (hnot23 : ¬ ((p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2))) :
    Apiros1110Conclusion p q := by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · have hnot32 : ¬ (q = 3 ∧ p = 2) := by
      intro h
      exact hnot23 (Or.inl ⟨h.2, h.1⟩)
    exact erdos1110Conclusion_swap
      (erdos1110_unconditional hpq_coprime.symm hlt hp hnot32)
  · subst q
    have hself : Nat.gcd p p = 1 := hpq_coprime
    have hpone : p = 1 := by simpa using hself
    omega
  · exact erdos1110_unconditional hpq_coprime hgt hq
      (fun h => hnot23 (Or.inr h))

end Apiros1110

end

-- ===== source module Apiros1110.SetConclusion =====

section

/-
# Set form of the Erdős 1110 conclusion

The original question asks for an infinite set of pairwise-coprime
nonrepresentable integers.  The stronger sequence conclusion supplies that
set as the range of its injective witness.
-/

namespace Apiros1110

/-- Convert a sequence witness to the infinite pairwise-coprime set used in
the statement of the problem. -/
theorem erdos1110_setConclusion_of_sequence {p q : Nat}
    (h : Apiros1110Conclusion p q) :
    ∃ A : Set Nat, A.Infinite ∧ A.Pairwise Nat.Coprime ∧
      ∀ n ∈ A, ¬ Representable p q n := by
  rcases h with ⟨f, hf⟩
  refine ⟨Set.range f,
    Set.infinite_range_of_injective (pairwiseCoprimeNonrepSeq_injective hf),
    ?_, ?_⟩
  · intro a ha b hb hne
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    apply hf.2
    intro hij
    subst j
    exact hne rfl
  · intro n hn
    rcases hn with ⟨i, rfl⟩
    exact (hf.1 i).2.1

/-- The set-form theorem for either order of the bases. -/
theorem erdos1110_setConclusion_unordered
    {p q : Nat}
    (hpq_coprime : Nat.Coprime p q)
    (hp : 2 ≤ p)
    (hq : 2 ≤ q)
    (hnot23 : ¬ ((p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2))) :
    ∃ A : Set Nat, A.Infinite ∧ A.Pairwise Nat.Coprime ∧
      ∀ n ∈ A, ¬ Representable p q n :=
  erdos1110_setConclusion_of_sequence
    (erdos1110_unordered hpq_coprime hp hq hnot23)

end Apiros1110

end

-- ===== source module Apiros1110.ValuePredicateBridge =====

section

/-
# Finite value-antichain to exponent-source bridge

`ValueRepresentable` mirrors the predicate in Formal Conjectures' Erdős 1110
file, using the same finite set of values, gamma membership, divisibility
antichain, and sum.  This local module does not import that external project.
-/

namespace Apiros1110.ValuePredicateBridge

open Apiros1110

def ValueGamma (p q : Nat) : Set Nat :=
  {v | ∃ i j : Nat, v = p ^ i * q ^ j}

def ValueRepresentable (p q n : Nat) : Prop :=
  ∃ s : Finset Nat,
    (s : Set Nat) ⊆ ValueGamma p q ∧
    _root_.IsAntichain (· ∣ ·) (s : Set Nat) ∧
    s.sum id = n

private theorem sum_toList_map (s : Finset α) (f : α → Nat) :
    (s.toList.map f).sum = s.sum f := by
  calc
    (s.toList.map f).sum =
        (Multiset.map f (s.toList : Multiset α)).sum := by
          rw [Multiset.map_coe, Multiset.sum_coe]
    _ = (Multiset.map f s.val).sum := by
      change (Multiset.map f ((s.val.toList : List α) : Multiset α)).sum =
        (Multiset.map f s.val).sum
      rw [Multiset.coe_toList]
    _ = s.sum f := (Finset.sum_eq_multiset_sum s f).symm

/-- A divisibility antichain of exponential values yields exactly the
repository's list-of-coordinate antichain representation. -/
theorem representable_of_valueRepresentable
    {p q n : Nat} (h : ValueRepresentable p q n) :
    Representable p q n := by
  classical
  rcases h with ⟨s, hsub, hanti, hsum⟩
  have hex : ∀ z : {v : Nat // v ∈ s},
      ∃ x : Point, Term p q x = z.1 := by
    intro z
    have hzset : z.1 ∈ (s : Set Nat) := z.2
    rcases hsub hzset with ⟨i, j, hz⟩
    exact ⟨(i, j), by simpa [Term] using hz.symm⟩
  let choosePoint : {v : Nat // v ∈ s} → Point :=
    fun z => Classical.choose (hex z)
  have hterm (z : {v : Nat // v ∈ s}) :
      Term p q (choosePoint z) = z.1 :=
    Classical.choose_spec (hex z)
  have hinj : Function.Injective choosePoint := by
    intro u v huv
    apply Subtype.ext
    calc
      u.1 = Term p q (choosePoint u) := (hterm u).symm
      _ = Term p q (choosePoint v) := congrArg (Term p q) huv
      _ = v.1 := hterm v
  let A : List Point := s.attach.toList.map choosePoint
  refine ⟨A, ?_, ?_⟩
  · constructor
    · exact (Finset.nodup_toList s.attach).map hinj
    · intro x hx y hy hxy hcoord
      change x ∈ s.attach.toList.map choosePoint at hx
      change y ∈ s.attach.toList.map choosePoint at hy
      rcases List.mem_map.mp hx with ⟨u, _hu, rfl⟩
      rcases List.mem_map.mp hy with ⟨v, _hv, rfl⟩
      have hdiv : u.1 ∣ v.1 := by
        simpa only [hterm u, hterm v] using
          (coordLe_term_dvd (p := p) (q := q) hcoord)
      have huv : u.1 = v.1 := hanti.eq u.2 v.2 hdiv
      have huv' : u = v := Subtype.ext huv
      exact hxy (congrArg choosePoint huv')
  · have hmap :
        (s.attach.toList.map choosePoint).map (Term p q) =
          s.attach.toList.map Subtype.val := by
      rw [List.map_map]
      exact List.map_congr_left (fun z _hz => hterm z)
    change ((s.attach.toList.map choosePoint).map (Term p q)).sum = n
    rw [hmap, sum_toList_map]
    have hsumAttach : s.attach.sum Subtype.val = s.sum id := by
      simpa [id] using (Finset.sum_attach s id)
    rw [hsumAttach]
    exact hsum

private theorem sum_toFinset_of_nodup (l : List Nat) (hl : l.Nodup) :
    l.toFinset.sum id = l.sum := by
  classical
  induction l with
  | nil => simp
  | cons a as ih =>
      have ha : a ∉ as := (List.nodup_cons.mp hl).1
      have has : as.Nodup := (List.nodup_cons.mp hl).2
      have haFin : a ∉ as.toFinset := by simpa using ha
      rw [List.toFinset_cons, Finset.sum_insert haFin]
      simpa [id] using congrArg (a + ·) (ih has)

/-- For coprime bases above one, distinct exponent pairs have distinct
term values. -/
theorem term_injective_of_coprime
    {p q : Nat} (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q) :
    Function.Injective (Term p q) := by
  intro x y hxy
  have hdivxy : Term p q x ∣ Term p q y := by rw [hxy]
  have hdivyx : Term p q y ∣ Term p q x := by rw [← hxy]
  have hcxy : CoordLe x y := term_dvd_coordLe hp hq hpq hdivxy
  have hcyx : CoordLe y x := term_dvd_coordLe hp hq hpq hdivyx
  exact Prod.ext (Nat.le_antisymm hcxy.1 hcyx.1)
    (Nat.le_antisymm hcxy.2 hcyx.2)

/-- Reverse bridge: a coordinate antichain becomes a finite divisibility
antichain of distinct term values, with the same sum. -/
theorem valueRepresentable_of_representable
    {p q n : Nat} (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (h : Representable p q n) : ValueRepresentable p q n := by
  classical
  rcases h with ⟨A, hanti, hsum⟩
  let values : List Nat := A.map (Term p q)
  let s : Finset Nat := values.toFinset
  have hvaluesNodup : values.Nodup :=
    hanti.1.map (term_injective_of_coprime hp hq hpq)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro v hv
    have hvList : v ∈ values := by simpa [s] using hv
    rcases List.mem_map.mp hvList with ⟨x, _hx, rfl⟩
    exact ⟨x.1, x.2, by simp [Term]⟩
  · change (s : Set Nat).Pairwise (fun v w => ¬ v ∣ w)
    intro v hv w hw hvw hdiv
    have hvList : v ∈ values := by simpa [s] using hv
    have hwList : w ∈ values := by simpa [s] using hw
    rcases List.mem_map.mp hvList with ⟨x, hx, rfl⟩
    rcases List.mem_map.mp hwList with ⟨y, hy, rfl⟩
    have hxy : x ≠ y := by
      intro h
      exact hvw (congrArg (Term p q) h)
    exact hanti.2 hx hy hxy (term_dvd_coordLe hp hq hpq hdiv)
  · have hsumValues : s.sum id = values.sum :=
      sum_toFinset_of_nodup values hvaluesNodup
    exact hsumValues.trans hsum

/-- The local finite-value predicate and the repository's coordinate-source
predicate agree for valid coprime bases. -/
theorem valueRepresentable_iff_representable
    {p q n : Nat} (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q) :
    ValueRepresentable p q n ↔ Representable p q n :=
  ⟨representable_of_valueRepresentable,
    valueRepresentable_of_representable hp hq hpq⟩

end Apiros1110.ValuePredicateBridge

end

-- ===== source module Apiros1110.ValueSetConclusion =====

section

/-
# Set conclusion for finite antichains of term values

`ValueRepresentable` has the finite-value Gamma, divisibility-antichain, and
sum structure of the public Formal Conjectures statement.  The one-way source
bridge transfers nonrepresentability from the repository's coordinate-list
predicate to that finite-value predicate.
-/

namespace Apiros1110

open ValuePredicateBridge

/-- Transfer a sequence witness to an infinite pairwise-coprime set whose
members are nonrepresentable under the finite-value predicate. -/
theorem erdos1110_valueSetConclusion_of_sequence {p q : Nat}
    (h : Apiros1110Conclusion p q) :
    ∃ A : Set Nat, A.Infinite ∧ A.Pairwise Nat.Coprime ∧
      ∀ n ∈ A, ¬ ValueRepresentable p q n := by
  rcases erdos1110_setConclusion_of_sequence h with
    ⟨A, hAinf, hApair, hAnot⟩
  refine ⟨A, hAinf, hApair, ?_⟩
  intro n hn hv
  exact hAnot n hn (representable_of_valueRepresentable hv)

/-- The normalized conditions and conclusion in the public statement of
Erdős Problem 1110, expressed with the locally mirrored value predicate. -/
theorem erdos1110_valueSetConclusion_normalized
    (p q : Nat) (hqp : q < p) (hq : 2 ≤ q)
    (hpq_coprime : Nat.Coprime p q)
    (hnot32 : ¬ (p = 3 ∧ q = 2)) :
    ∃ A : Set Nat, A.Infinite ∧ A.Pairwise Nat.Coprime ∧
      ∀ n ∈ A, ¬ ValueRepresentable p q n :=
  erdos1110_valueSetConclusion_of_sequence
    (erdos1110_unconditional hpq_coprime hqp hq hnot32)

/-- The same finite-value conclusion for either base order. -/
theorem erdos1110_valueSetConclusion_unordered
    {p q : Nat}
    (hpq_coprime : Nat.Coprime p q)
    (hp : 2 ≤ p)
    (hq : 2 ≤ q)
    (hnot23 : ¬ ((p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2))) :
    ∃ A : Set Nat, A.Infinite ∧ A.Pairwise Nat.Coprime ∧
      ∀ n ∈ A, ¬ ValueRepresentable p q n :=
  erdos1110_valueSetConclusion_of_sequence
    (erdos1110_unordered hpq_coprime hp hq hnot23)

end Apiros1110

end

theorem OMA.solution : type_of% @Erdos1110.erdos_1110 :=
  Apiros1110.erdos1110_valueSetConclusion_normalized
