import OMAReductions.R_Erdos675_erdos_675_variants_brun_R1
import Mathlib

/-!
Hypothesis H1 of the reduction imported above, proved by a lower-bound sieve of Brun-Hooley
type for pairwise coprime moduli, with Chebyshev-type sparsity from lcm(1..n) in place of
Mertens estimates. Sources: P. Erdos, Some unconventional problems in number theory,
Math. Mag. 52 (1979), item 5; C. Hooley, On an almost-pure sieve, Acta Arith. 66 (1994),
359-368; K. Ford and H. Halberstam, The Brun-Hooley sieve, J. Number Theory 81 (2000), 335-350.
-/
-- Credit: @LordMike

namespace OMA.Brun

open Finset

/- ## Definitions (fixed) -/

/-- `W` is an admissible set of moduli: pairwise coprime, larger than `N`, coprime to `M`. -/
def Adm (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) : Prop :=
  A ⊆ Icc 1 N ∧ (W : Set ℕ).Pairwise Nat.Coprime ∧ ∀ b ∈ W, N < b ∧ Nat.Coprime M b

/-- Indicator that every modulus in `S` divides some `a + M * k` with `a ∈ A`. -/
noncomputable def ind (A : Finset ℕ) (M : ℕ) (S : Finset ℕ) (k : ℕ) : ℝ :=
  if ∀ b ∈ S, ∃ a ∈ A, b ∣ a + M * k then 1 else 0

/-- Weight of a block `P`; the coefficient of `S ⊆ P` is `c S.card`. -/
noncomputable def phi (A : Finset ℕ) (M : ℕ) (P : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, c S.card * ind A M S k

/-- Density of a block weight. -/
noncomputable def dens (g : ℝ) (P : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ S ∈ P.powerset, c S.card * ∏ b ∈ S, (g / (b : ℝ))

/-- Mass of a block weight (bounds the remainder). -/
noncomputable def mass (g : ℝ) (P : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ S ∈ P.powerset, |c S.card| * g ^ S.card

/-- Number of moduli in `P` that divide some `a + M * k` with `a ∈ A`. -/
def nu (A : Finset ℕ) (M : ℕ) (P : Finset ℕ) (k : ℕ) : ℕ :=
  (P.filter (fun b => ∃ a ∈ A, b ∣ a + M * k)).card

/-- Coefficients of the inclusion-exclusion sum truncated at order `m`. -/
noncomputable def cU (m : ℕ) (i : ℕ) : ℝ := if i ≤ m then (-1) ^ i else 0

/-- Coefficients of the first omitted term of order `m + 1`. -/
noncomputable def cE (m : ℕ) (i : ℕ) : ℝ := if i = m + 1 then 1 else 0

/-- Elementary symmetric sum of degree `i` of the numbers `t b`, `b ∈ P`. -/
noncomputable def esym (t : ℕ → ℝ) (P : Finset ℕ) (i : ℕ) : ℝ :=
  ∑ S ∈ P.powersetCard i, ∏ b ∈ S, t b

/-- Lower end (exclusive) of block `j`. -/
def lo (j : ℕ) : ℕ := if j = 0 then 0 else 2 ^ 2 ^ j

/-- Upper end (inclusive) of block `j`. -/
def hi (j : ℕ) : ℕ := 2 ^ 2 ^ (j + 1)

/-- Block `j` of the moduli: those in `(lo j, hi j]`. -/
def blk (W : Finset ℕ) (j : ℕ) : Finset ℕ := W.filter (fun b => lo j < b ∧ b ≤ hi j)

/-- Truncation order of block `j` when there are `n` blocks. Always even. -/
def mm (a n j : ℕ) : ℕ := 2 * (a + (n - j))

/-- The integers `k ∈ [1, x]` such that no modulus in `W` divides any `a + M * k`. -/
def sift (A : Finset ℕ) (M : ℕ) (W : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun k => ∀ b ∈ W, ∀ a ∈ A, ¬ b ∣ a + M * k)

/- ## Block C: counting solutions by the Chinese remainder theorem -/

theorem adm_card_lt (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W) :
    ∀ b ∈ W, A.card < b := by
  intro b hb
  have h1 : A.card ≤ N := by
    have := Finset.card_le_card hadm.1
    simpa using this
  have h2 := (hadm.2.2 b hb).1
  omega

theorem adm_mono (A : Finset ℕ) (N M : ℕ) (W S : Finset ℕ) (hadm : Adm A N M W) (hS : S ⊆ W) :
    Adm A N M S :=
  ⟨hadm.1, Set.Pairwise.mono (Finset.coe_subset.mpr hS) hadm.2.1, fun b hb => hadm.2.2 b (hS hb)⟩

theorem hit_mod (b a M k : ℕ) : b ∣ a + M * (k % b) ↔ b ∣ a + M * k :=
  Nat.ModEq.dvd_iff (((Nat.mod_modEq k b).mul_left M).add_left a) dvd_rfl

theorem hit_mod_of_dvd (b d a M k : ℕ) (hbd : b ∣ d) :
    b ∣ a + M * (k % d) ↔ b ∣ a + M * k :=
  Nat.ModEq.dvd_iff ((((Nat.mod_modEq k d).of_dvd hbd).mul_left M).add_left a) dvd_rfl

theorem hit_unique (A : Finset ℕ) (N M b k a a' : ℕ) (hA : A ⊆ Icc 1 N) (hb : N < b)
    (ha : a ∈ A) (ha' : a' ∈ A) (h : b ∣ a + M * k) (h' : b ∣ a' + M * k) : a = a' := by
  have hA1 := Finset.mem_Icc.mp (hA ha)
  have hA2 := Finset.mem_Icc.mp (hA ha')
  rcases le_total a a' with hle | hle
  · have key : b ∣ a' + M * k - (a + M * k) := Nat.dvd_sub h' h
    have e : a' + M * k - (a + M * k) = a' - a := by omega
    rw [e] at key
    have := Nat.eq_zero_of_dvd_of_lt key (by omega)
    omega
  · have key : b ∣ a + M * k - (a' + M * k) := Nat.dvd_sub h h'
    have e : a + M * k - (a' + M * k) = a - a' := by omega
    rw [e] at key
    have := Nat.eq_zero_of_dvd_of_lt key (by omega)
    omega

theorem hit_exists (M b a : ℕ) (hb : 0 < b) (hc : Nat.Coprime M b) :
    ∃ r, r < b ∧ b ∣ a + M * r := by
  have : NeZero b := ⟨hb.ne'⟩
  refine ⟨(-(a : ZMod b) * ((ZMod.unitOfCoprime M hc)⁻¹ : (ZMod b)ˣ)).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime M hc, mul_comm (-(a : ZMod b)) _,
    Units.mul_inv_cancel_left]
  exact add_neg_cancel _

theorem hit_inj (M b a r r' : ℕ) (hc : Nat.Coprime M b) (hr : r < b) (hr' : r' < b)
    (h : b ∣ a + M * r) (h' : b ∣ a + M * r') : r = r' := by
  rcases le_total r r' with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have e : a + M * (r + d) = (a + M * r) + M * d := by ring
    rw [e] at h'
    have h2 : b ∣ M * d := (Nat.dvd_add_right h).mp h'
    have h3 : b ∣ d := Nat.Coprime.dvd_of_dvd_mul_left hc.symm h2
    have := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have e : a + M * (r' + d) = (a + M * r') + M * d := by ring
    rw [e] at h
    have h2 : b ∣ M * d := (Nat.dvd_add_right h').mp h
    have h3 : b ∣ d := Nat.Coprime.dvd_of_dvd_mul_left hc.symm h2
    have := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega

theorem res_card (A : Finset ℕ) (N M b : ℕ) (hA : A ⊆ Icc 1 N) (hb : N < b)
    (hc : Nat.Coprime M b) :
    ((range b).filter (fun r => ∃ a ∈ A, b ∣ a + M * r)).card = A.card := by
  choose f hf using fun a => hit_exists M b a (by omega) hc
  have himg : (range b).filter (fun r => ∃ a ∈ A, b ∣ a + M * r) = A.image f := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hr, a, ha, hdvd⟩
      exact ⟨a, ha, (hit_inj M b a r (f a) hc hr (hf a).1 hdvd (hf a).2).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(hf a).1, a, ha, (hf a).2⟩
  rw [himg, Finset.card_image_of_injOn]
  intro a ha a' ha' heq
  have h1 := (hf a).2
  rw [heq] at h1
  exact hit_unique A N M b (f a') a a' hA hb ha ha' h1 (hf a').2

theorem crt_card (m n : ℕ) (h : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] :
    ((range (m * n)).filter (fun k => P (k % m) ∧ Q (k % n))).card =
      ((range m).filter P).card * ((range n).filter Q).card := by
  rw [← Finset.card_product]
  apply Finset.card_bij (fun k _ => (k % m, k % n))
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨Nat.mod_lt _ hm, hk.2.1⟩, Nat.mod_lt _ hn, hk.2.2⟩
  · intro k hk k' hk' heq
    simp only [Finset.mem_filter, Finset.mem_range] at hk hk'
    simp only [Prod.mk.injEq] at heq
    have h1 : k ≡ k' [MOD m] := heq.1
    have h2 : k ≡ k' [MOD n] := heq.2
    have h3 : k ≡ k' [MOD m * n] := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨h1, h2⟩
    unfold Nat.ModEq at h3
    rwa [Nat.mod_eq_of_lt hk.1, Nat.mod_eq_of_lt hk'.1] at h3
  · rintro ⟨r, s⟩ hrs
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hrs
    obtain ⟨⟨hrm, hPr⟩, hsn, hQs⟩ := hrs
    have hex : ∃ c, c < m * n ∧ c % m = r ∧ c % n = s := by
      refine ⟨(Nat.chineseRemainder h r s).1, Nat.chineseRemainder_lt_mul h r s hm.ne' hn.ne', ?_, ?_⟩
      · have := (Nat.chineseRemainder h r s).2.1
        unfold Nat.ModEq at this
        exact this.trans (Nat.mod_eq_of_lt hrm)
      · have := (Nat.chineseRemainder h r s).2.2
        unfold Nat.ModEq at this
        exact this.trans (Nat.mod_eq_of_lt hsn)
    obtain ⟨c, hlt, hcm, hcn⟩ := hex
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, by rw [hcm, hcn]; exact ⟨hPr, hQs⟩⟩,
      by simp [hcm, hcn]⟩

theorem period_card (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W)
    (S : Finset ℕ) (hS : S ⊆ W) :
    ((range (∏ b ∈ S, b)).filter (fun k => ∀ b ∈ S, ∃ a ∈ A, b ∣ a + M * k)).card =
      A.card ^ S.card := by
  revert hS
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | @insert b S hbS ih =>
    intro hS
    have hbW : b ∈ W := hS (Finset.mem_insert_self b S)
    have hSW : S ⊆ W := fun x hx => hS (Finset.mem_insert_of_mem hx)
    have ih' := ih hSW
    have hbN := (hadm.2.2 b hbW).1
    have hc : Nat.Coprime M b := (hadm.2.2 b hbW).2
    have hbpos : 0 < b := by omega
    have hSpos : 0 < ∏ x ∈ S, x := Finset.prod_pos (fun x hx => by
      have := (hadm.2.2 x (hSW hx)).1
      omega)
    have hcop : Nat.Coprime b (∏ x ∈ S, x) := by
      apply Nat.Coprime.prod_right
      intro x hx
      apply hadm.2.1 (Finset.mem_coe.mpr hbW) (Finset.mem_coe.mpr (hSW hx))
      rintro rfl
      exact hbS hx
    have hfilt : (range (b * ∏ x ∈ S, x)).filter (fun k => ∀ y ∈ insert b S, ∃ a ∈ A, y ∣ a + M * k) =
        (range (b * ∏ x ∈ S, x)).filter (fun k => (∃ a ∈ A, b ∣ a + M * (k % b)) ∧
          (∀ y ∈ S, ∃ a ∈ A, y ∣ a + M * (k % ∏ x ∈ S, x))) := by
      apply Finset.filter_congr
      intro k _
      have hb' : (∃ a ∈ A, b ∣ a + M * k) ↔ (∃ a ∈ A, b ∣ a + M * (k % b)) := by
        simp only [hit_mod]
      have hS' : (∀ y ∈ S, ∃ a ∈ A, y ∣ a + M * k) ↔
          (∀ y ∈ S, ∃ a ∈ A, y ∣ a + M * (k % ∏ x ∈ S, x)) := by
        constructor
        · intro h y hy
          obtain ⟨a, ha, hd⟩ := h y hy
          have hdv : y ∣ ∏ x ∈ S, x := Finset.dvd_prod_of_mem (fun c => c) hy
          exact ⟨a, ha, (hit_mod_of_dvd y _ a M k hdv).mpr hd⟩
        · intro h y hy
          obtain ⟨a, ha, hd⟩ := h y hy
          have hdv : y ∣ ∏ x ∈ S, x := Finset.dvd_prod_of_mem (fun c => c) hy
          exact ⟨a, ha, (hit_mod_of_dvd y _ a M k hdv).mp hd⟩
      simp only [Finset.forall_mem_insert]
      exact and_congr hb' hS'
    have hcrt : ((range (b * ∏ x ∈ S, x)).filter (fun k => (∃ a ∈ A, b ∣ a + M * (k % b)) ∧
          (∀ y ∈ S, ∃ a ∈ A, y ∣ a + M * (k % ∏ x ∈ S, x)))).card =
        ((range b).filter (fun r => ∃ a ∈ A, b ∣ a + M * r)).card *
          ((range (∏ x ∈ S, x)).filter (fun r => ∀ y ∈ S, ∃ a ∈ A, y ∣ a + M * r)).card :=
      crt_card b (∏ x ∈ S, x) hcop hbpos hSpos (fun r => ∃ a ∈ A, b ∣ a + M * r)
        (fun r => ∀ y ∈ S, ∃ a ∈ A, y ∣ a + M * r)
    rw [Finset.prod_insert hbS, Finset.card_insert_of_notMem hbS, pow_succ', hfilt, hcrt,
      res_card A N M b hadm.1 hbN hc, ih']

theorem periodic_count_mul_aux1 (P : ℕ → Prop) [DecidablePred P] (d : ℕ)
    (hper : ∀ k, P (k + d) ↔ P k) (s : ℕ) :
    ((Ico s (s + d)).filter P).card = ((range d).filter P).card := by
  have hP : Function.Periodic P d := fun k => propext (hper k)
  rw [Nat.filter_Ico_card_eq_of_periodic s d P hP, Nat.count_eq_card_filter_range]

theorem periodic_count_mul (P : ℕ → Prop) [DecidablePred P] (d : ℕ)
    (hper : ∀ k, P (k + d) ↔ P k) (q : ℕ) :
    ((Ico 1 (1 + q * d)).filter P).card = q * ((range d).filter P).card := by
  induction q with
  | zero => simp
  | succ q ih =>
    have e : 1 + (q + 1) * d = (1 + q * d) + d := by ring
    have hle1 : 1 ≤ 1 + q * d := Nat.le_add_right 1 _
    have hle2 : 1 + q * d ≤ 1 + q * d + d := Nat.le_add_right _ _
    rw [e, ← Finset.Ico_union_Ico_eq_Ico hle1 hle2, Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ih, periodic_count_mul_aux1 P d hper (1 + q * d)]
    ring

theorem periodic_window (P : ℕ → Prop) [DecidablePred P] (d : ℕ)
    (hper : ∀ k, P (k + d) ↔ P k) (s r : ℕ) (hr : r ≤ d) :
    ((Ico s (s + r)).filter P).card ≤ ((range d).filter P).card := by
  rw [← periodic_count_mul_aux1 P d hper s]
  exact Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.Ico_subset_Ico_right (by omega)))

theorem periodic_count_nat (P : ℕ → Prop) [DecidablePred P] (d : ℕ) (hd : 0 < d)
    (hper : ∀ k, P (k + d) ↔ P k) (x : ℕ) :
    x / d * ((range d).filter P).card ≤ ((Icc 1 x).filter P).card ∧
      ((Icc 1 x).filter P).card ≤
        x / d * ((range d).filter P).card + ((range d).filter P).card := by
  have hI : Icc 1 x = Ico 1 (1 + x / d * d) ∪ Ico (1 + x / d * d) (1 + x / d * d + x % d) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]
    have h := Nat.div_add_mod' x d
    omega
  have hsplit : (Icc 1 x).filter P = (Ico 1 (1 + x / d * d)).filter P ∪
      (Ico (1 + x / d * d) (1 + x / d * d + x % d)).filter P := by
    rw [hI, Finset.filter_union]
  have hA := periodic_count_mul P d hper (x / d)
  have hB := periodic_window P d hper (1 + x / d * d) (x % d) (Nat.mod_lt x hd).le
  have hU := Finset.card_union_le ((Ico 1 (1 + x / d * d)).filter P)
    ((Ico (1 + x / d * d) (1 + x / d * d + x % d)).filter P)
  have hL := Finset.card_le_card (Finset.subset_union_left
    (s₁ := (Ico 1 (1 + x / d * d)).filter P)
    (s₂ := (Ico (1 + x / d * d) (1 + x / d * d + x % d)).filter P))
  rw [← hsplit] at hU hL
  constructor <;> omega

theorem periodic_count (P : ℕ → Prop) [DecidablePred P] (d : ℕ) (hd : 0 < d)
    (hper : ∀ k, P (k + d) ↔ P k) (x : ℕ) :
    |(((Icc 1 x).filter P).card : ℝ) - x * ((((range d).filter P).card : ℝ) / d)| ≤
      (((range d).filter P).card : ℝ) := by
  obtain ⟨h1, h2⟩ := periodic_count_nat P d hd hper x
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := hdR.ne'
  have hq := Nat.div_add_mod' x d
  have hr := Nat.mod_lt x hd
  have h1R : ((x / d : ℕ) : ℝ) * (((range d).filter P).card : ℝ) ≤
      (((Icc 1 x).filter P).card : ℝ) := by
    exact_mod_cast h1
  have h2R : (((Icc 1 x).filter P).card : ℝ) ≤
      ((x / d : ℕ) : ℝ) * (((range d).filter P).card : ℝ) + (((range d).filter P).card : ℝ) := by
    exact_mod_cast h2
  have hxR : (x : ℝ) = ((x / d : ℕ) : ℝ) * d + ((x % d : ℕ) : ℝ) := by
    exact_mod_cast hq.symm
  have hcd : (((range d).filter P).card : ℝ) ≤ d := by
    have := Finset.card_filter_le (range d) P
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hrd : ((x % d : ℕ) : ℝ) ≤ d := by exact_mod_cast hr.le
  have hr0 : (0 : ℝ) ≤ ((x % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcdiv0 : (0 : ℝ) ≤ (((range d).filter P).card : ℝ) / d :=
    div_nonneg (Nat.cast_nonneg _) hdR.le
  have hE : (d : ℝ) * ((((range d).filter P).card : ℝ) / d) = (((range d).filter P).card : ℝ) := by
    field_simp
  have he0 : 0 ≤ ((x % d : ℕ) : ℝ) * ((((range d).filter P).card : ℝ) / d) :=
    mul_nonneg hr0 hcdiv0
  have he1 : ((x % d : ℕ) : ℝ) * ((((range d).filter P).card : ℝ) / d) ≤
      (((range d).filter P).card : ℝ) := by
    have := mul_le_mul_of_nonneg_right hrd hcdiv0
    linarith
  have hkey : (x : ℝ) * ((((range d).filter P).card : ℝ) / d) =
      ((x / d : ℕ) : ℝ) * (((range d).filter P).card : ℝ) +
        ((x % d : ℕ) : ℝ) * ((((range d).filter P).card : ℝ) / d) := by
    rw [hxR]
    linear_combination ((x / d : ℕ) : ℝ) * hE
  rw [abs_le]
  constructor <;> linarith

theorem cnt_bound (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W)
    (S : Finset ℕ) (hS : S ⊆ W) (x : ℕ) :
    |∑ k ∈ Icc 1 x, ind A M S k - x * ∏ b ∈ S, ((A.card : ℝ) / (b : ℝ))| ≤
      (A.card : ℝ) ^ S.card := by
  have hdpos : 0 < ∏ b ∈ S, b := Finset.prod_pos (fun b hb => by
    have := (hadm.2.2 b (hS hb)).1
    omega)
  have key : ∀ k, ∀ b ∈ S, ∀ a, b ∣ a + M * (k + ∏ c ∈ S, c) ↔ b ∣ a + M * k := by
    intro k b hb a
    have hbd : b ∣ ∏ c ∈ S, c := Finset.dvd_prod_of_mem (fun c => c) hb
    have h := hit_mod_of_dvd b (∏ c ∈ S, c) a M (k + ∏ c ∈ S, c) hbd
    rw [Nat.add_mod_right, hit_mod_of_dvd b (∏ c ∈ S, c) a M k hbd] at h
    exact h.symm
  have hper : ∀ k, (∀ b ∈ S, ∃ a ∈ A, b ∣ a + M * (k + ∏ c ∈ S, c)) ↔
      (∀ b ∈ S, ∃ a ∈ A, b ∣ a + M * k) := by
    intro k
    constructor
    · intro h b hb
      obtain ⟨a, ha, hd⟩ := h b hb
      exact ⟨a, ha, (key k b hb a).mp hd⟩
    · intro h b hb
      obtain ⟨a, ha, hd⟩ := h b hb
      exact ⟨a, ha, (key k b hb a).mpr hd⟩
  have hpc := periodic_count (fun k => ∀ b ∈ S, ∃ a ∈ A, b ∣ a + M * k) (∏ c ∈ S, c) hdpos hper x
  have hcard : ((((range (∏ b ∈ S, b)).filter (fun k => ∀ b ∈ S, ∃ a ∈ A, b ∣ a + M * k)).card : ℕ) : ℝ) =
      (A.card : ℝ) ^ S.card := by
    rw [period_card A N M W hadm S hS]
    push_cast
    ring
  have hprod : ∏ b ∈ S, ((A.card : ℝ) / (b : ℝ)) =
      (A.card : ℝ) ^ S.card / ((∏ b ∈ S, b : ℕ) : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Nat.cast_prod]
  simp only [ind, Finset.sum_boole]
  rw [hprod]
  rw [hcard] at hpc
  exact hpc

/- ## Block P: sums of products of block weights -/

theorem ind_union (A : Finset ℕ) (M : ℕ) (R S : Finset ℕ) (k : ℕ) :
    ind A M (R ∪ S) k = ind A M R k * ind A M S k := by
  simp only [ind, Finset.forall_mem_union]
  split_ifs <;> simp_all

theorem block_lhs (A : Finset ℕ) (M : ℕ) (R P : Finset ℕ) (c : ℕ → ℝ) (F : ℕ → ℝ) (x : ℕ) :
    ∑ k ∈ Icc 1 x, ind A M R k * (F k * phi A M P c k) =
      ∑ S ∈ P.powerset, c S.card * ∑ k ∈ Icc 1 x, ind A M (R ∪ S) k * F k := by
  have h : ∀ k, ind A M R k * (F k * phi A M P c k) =
      ∑ S ∈ P.powerset, c S.card * (ind A M (R ∪ S) k * F k) := by
    intro k
    simp only [phi, Finset.mul_sum, ind_union]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    ring
  simp only [h, Finset.mul_sum]
  exact Finset.sum_comm

theorem block_rhs (g : ℝ) (R P : Finset ℕ) (hRP : Disjoint R P) (c : ℕ → ℝ) (δ X : ℝ) :
    X * (∏ b ∈ R, (g / (b : ℝ))) * (δ * dens g P c) =
      ∑ S ∈ P.powerset, c S.card * (X * (∏ b ∈ R ∪ S, (g / (b : ℝ))) * δ) := by
  simp only [dens, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [Finset.prod_union (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hS) hRP)]
  ring

theorem block_err (g : ℝ) (R P : Finset ℕ) (hRP : Disjoint R P) (c : ℕ → ℝ) (E : ℝ) :
    ∑ S ∈ P.powerset, |c S.card| * (g ^ (R ∪ S).card * E) = g ^ R.card * (E * mass g P c) := by
  simp only [mass, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hS) hRP),
    pow_add]
  ring

theorem block_step (A : Finset ℕ) (M : ℕ) (R P : Finset ℕ) (hRP : Disjoint R P) (c : ℕ → ℝ)
    (F : ℕ → ℝ) (δ E : ℝ) (x : ℕ)
    (h : ∀ S, S ⊆ P → |∑ k ∈ Icc 1 x, ind A M (R ∪ S) k * F k
        - x * (∏ b ∈ R ∪ S, ((A.card : ℝ) / (b : ℝ))) * δ| ≤ (A.card : ℝ) ^ (R ∪ S).card * E) :
    |∑ k ∈ Icc 1 x, ind A M R k * (F k * phi A M P c k)
        - x * (∏ b ∈ R, ((A.card : ℝ) / (b : ℝ))) * (δ * dens A.card P c)| ≤
      (A.card : ℝ) ^ R.card * (E * mass A.card P c) := by
  rw [block_lhs, block_rhs _ _ _ hRP, ← block_err _ _ _ hRP, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S hS => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (h S (Finset.mem_powerset.mp hS)) (abs_nonneg _)

theorem prod_main (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W)
    (P : ℕ → Finset ℕ) (hPW : ∀ j, P j ⊆ W) (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (c : ℕ → ℕ → ℝ) (x n : ℕ) (R : Finset ℕ) (hR : R ⊆ W) (hRP : ∀ j, j < n → Disjoint R (P j)) :
    |∑ k ∈ Icc 1 x, ind A M R k * ∏ j ∈ range n, phi A M (P j) (c j) k
        - x * (∏ b ∈ R, ((A.card : ℝ) / (b : ℝ))) * ∏ j ∈ range n, dens A.card (P j) (c j)| ≤
      (A.card : ℝ) ^ R.card * ∏ j ∈ range n, mass A.card (P j) (c j) := by
  induction n generalizing R with
  | zero =>
    simp only [Finset.prod_range_zero, mul_one]
    exact cnt_bound A N M W hadm R hR x
  | succ n ih =>
    simp only [Finset.prod_range_succ]
    exact block_step A M R (P n) (hRP n (Nat.lt_succ_self n)) (c n)
      (fun k => ∏ j ∈ range n, phi A M (P j) (c j) k)
      (∏ j ∈ range n, dens A.card (P j) (c j)) (∏ j ∈ range n, mass A.card (P j) (c j)) x
      (fun S hS => ih (R ∪ S) (Finset.union_subset hR (hS.trans (hPW n)))
        (fun j hj => Finset.disjoint_union_left.mpr
          ⟨hRP j (by omega), Finset.disjoint_of_subset_left hS (hdisj n j (by omega))⟩))

theorem sum_prod_phi (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W)
    (P : ℕ → Finset ℕ) (hPW : ∀ j, P j ⊆ W) (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (c : ℕ → ℕ → ℝ) (x n : ℕ) :
    |∑ k ∈ Icc 1 x, ∏ j ∈ range n, phi A M (P j) (c j) k
        - x * ∏ j ∈ range n, dens A.card (P j) (c j)| ≤
      ∏ j ∈ range n, mass A.card (P j) (c j) := by
  have h := prod_main A N M W hadm P hPW hdisj c x n ∅ (Finset.empty_subset _)
    (fun j _ => Finset.disjoint_empty_left _)
  simpa [ind] using h

/- ## Block B: pointwise Bonferroni and Hooley inequalities -/

theorem phi_eq_sum (A : Finset ℕ) (M : ℕ) (P : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    phi A M P c k =
      ∑ S ∈ (P.filter (fun b => ∃ a ∈ A, b ∣ a + M * k)).powerset, c S.card := by
  simp only [phi, ind, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    exact ⟨h1 hx, h2 x hx⟩
  · intro h
    exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩

theorem phi_eq_choose (A : Finset ℕ) (M : ℕ) (P : Finset ℕ) (c : ℕ → ℝ) (k L : ℕ)
    (hL : nu A M P k ≤ L) :
    phi A M P c k = ∑ i ∈ range (L + 1), c i * ((nu A M P k).choose i : ℝ) := by
  have hc : (P.filter (fun b => ∃ a ∈ A, b ∣ a + M * k)).card = nu A M P k := rfl
  have hsub : Finset.range (nu A M P k + 1) ⊆ Finset.range (L + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [phi_eq_sum, Finset.sum_powerset_apply_card, hc, Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [nsmul_eq_mul, mul_comm]
  · intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (show nu A M P k < i by omega), zero_smul]

theorem phiU_eq (A : Finset ℕ) (M : ℕ) (P : Finset ℕ) (m k : ℕ) :
    phi A M P (cU m) k = ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * ((nu A M P k).choose i : ℝ) := by
  have hL : nu A M P k ≤ nu A M P k + m := Nat.le_add_right _ _
  rw [phi_eq_choose A M P (cU m) k (nu A M P k + m) hL]
  have hsub : Finset.range (m + 1) ⊆ Finset.range (nu A M P k + m + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i ≤ m := by
      rw [Finset.mem_range] at hi
      omega
    simp only [cU, if_pos hi']
  · intro i _ hi
    have hi' : ¬ i ≤ m := by
      rw [Finset.mem_range, not_lt] at hi
      omega
    simp only [cU, if_neg hi', zero_mul]

theorem phiE_eq (A : Finset ℕ) (M : ℕ) (P : Finset ℕ) (m k : ℕ) :
    phi A M P (cE m) k = ((nu A M P k).choose (m + 1) : ℝ) := by
  rw [phi_eq_choose A M P (cE m) k (nu A M P k + (m + 1)) (Nat.le_add_right _ _)]
  rw [Finset.sum_eq_single (m + 1)]
  · simp [cE]
  · intro i _ hi
    simp [cE, hi]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range]
    omega

theorem alt_choose_bounds (m n : ℕ) (hm : Even m) :
    (if n = 0 then (1 : ℝ) else 0) ≤ ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * (n.choose i : ℝ) ∧
      ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * (n.choose i : ℝ) ≤
        (if n = 0 then (1 : ℝ) else 0) + (n.choose (m + 1) : ℝ) := by
  rcases n with _ | n
  · have hs : ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * ((0 : ℕ).choose i : ℝ) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb
        rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb)]
        simp
      · intro h
        exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h
    rw [hs]
    simp
  · have hs : ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * ((n + 1).choose i : ℝ) = (n.choose m : ℝ) := by
      have h2 := congrArg (Int.cast : ℤ → ℝ) (Int.alternating_sum_range_choose_eq_choose (n := n) (m := m))
      push_cast at h2
      simpa [hm.neg_one_pow] using h2
    rw [hs, Nat.choose_succ_succ', if_neg (by omega : ¬ (n + 1 = 0))]
    have h0 : (0 : ℝ) ≤ (n.choose m : ℝ) := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ (n.choose (m + 1) : ℝ) := Nat.cast_nonneg _
    push_cast
    constructor <;> linarith

theorem phiU_bounds (A : Finset ℕ) (M : ℕ) (P : Finset ℕ) (m k : ℕ) (hm : Even m) :
    (if nu A M P k = 0 then (1 : ℝ) else 0) ≤ phi A M P (cU m) k ∧
      phi A M P (cU m) k ≤ (if nu A M P k = 0 then (1 : ℝ) else 0) + phi A M P (cE m) k := by
  rw [phiU_eq, phiE_eq]
  exact alt_choose_bounds m _ hm

theorem sum_prod_ite_succ (n : ℕ) (e u : ℕ → ℝ) :
    ∑ j ∈ range (n + 1), ∏ i ∈ range (n + 1), (if i = j then e i else u i) =
      (∑ j ∈ range n, ∏ i ∈ range n, (if i = j then e i else u i)) * u n
        + (∏ i ∈ range n, u i) * e n := by
  have h1 : ∀ j ∈ range n, (∏ i ∈ range (n + 1), (if i = j then e i else u i)) =
      (∏ i ∈ range n, (if i = j then e i else u i)) * u n := by
    intro j hj
    have hj' : j < n := Finset.mem_range.mp hj
    rw [Finset.prod_range_succ, if_neg (show ¬ (n = j) by omega)]
  have h2 : ∏ i ∈ range (n + 1), (if i = n then e i else u i) = (∏ i ∈ range n, u i) * e n := by
    rw [Finset.prod_range_succ, if_pos rfl]
    congr 1
    exact Finset.prod_congr rfl (fun i hi => if_neg (show ¬ (i = n) by
      have := Finset.mem_range.mp hi
      omega))
  rw [Finset.sum_range_succ, Finset.sum_congr rfl h1, ← Finset.sum_mul, h2]

theorem prod_ite_mul (n j : ℕ) (hj : j < n) (e u : ℕ → ℝ) :
    (∏ i ∈ range n, (if i = j then e i else u i)) * u j = e j * ∏ i ∈ range n, u i := by
  have hmem : j ∈ range n := Finset.mem_range.mpr hj
  have h1 : ∏ i ∈ (range n).erase j, (if i = j then e i else u i) =
      ∏ i ∈ (range n).erase j, u i :=
    Finset.prod_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))
  rw [← Finset.mul_prod_erase (range n) (fun i => if i = j then e i else u i) hmem,
    ← Finset.mul_prod_erase (range n) u hmem, h1, if_pos rfl]
  ring

theorem hooley (n : ℕ) (t u e : ℕ → ℝ) (h0 : ∀ j, 0 ≤ t j) (h1 : ∀ j, t j ≤ u j)
    (h2 : ∀ j, u j ≤ t j + e j) :
    ∏ j ∈ range n, u j - ∑ j ∈ range n, ∏ i ∈ range n, (if i = j then e i else u i) ≤
      ∏ j ∈ range n, t j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu : ∀ j, 0 ≤ u j := fun j => le_trans (h0 j) (h1 j)
    have he : ∀ j, 0 ≤ e j := fun j => by linarith [h0 j, h1 j, h2 j]
    have hU : 0 ≤ ∏ i ∈ range n, u i := Finset.prod_nonneg (fun i _ => hu i)
    have hS : 0 ≤ ∑ j ∈ range n, ∏ i ∈ range n, (if i = j then e i else u i) :=
      Finset.sum_nonneg (fun j _ => Finset.prod_nonneg (fun i _ => by
        split_ifs
        · exact he i
        · exact hu i))
    rw [sum_prod_ite_succ, Finset.prod_range_succ u n, Finset.prod_range_succ t n]
    nlinarith [mul_le_mul_of_nonneg_right ih (h0 n), mul_nonneg hU (sub_nonneg.mpr (h2 n)),
      mul_nonneg hS (sub_nonneg.mpr (h1 n))]

theorem ind_sift (A : Finset ℕ) (M : ℕ) (W : Finset ℕ) (P : ℕ → Finset ℕ) (n : ℕ)
    (hPW : ∀ j, P j ⊆ W) (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ P j) (k : ℕ) :
    (if ∀ b ∈ W, ∀ a ∈ A, ¬ b ∣ a + M * k then (1 : ℝ) else 0) =
      ∏ j ∈ range n, (if nu A M (P j) k = 0 then (1 : ℝ) else 0) := by
  have hiff : (∀ b ∈ W, ∀ a ∈ A, ¬ b ∣ a + M * k) ↔ (∀ j ∈ range n, nu A M (P j) k = 0) := by
    constructor
    · intro h j hj
      unfold nu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b hb hex
      obtain ⟨a, ha, hdiv⟩ := hex
      exact h b (hPW j hb) a ha hdiv
    · intro h b hb a ha hdiv
      obtain ⟨j, hj, hbj⟩ := hcov b hb
      have h0 := h j (Finset.mem_range.mpr hj)
      have hpos : 0 < nu A M (P j) k := by
        unfold nu
        apply Finset.card_pos.mpr
        exact ⟨b, Finset.mem_filter.mpr ⟨hbj, a, ha, hdiv⟩⟩
      omega
  rw [Finset.prod_boole]
  by_cases h : ∀ b ∈ W, ∀ a ∈ A, ¬ b ∣ a + M * k
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

theorem sift_pointwise (A : Finset ℕ) (M : ℕ) (W : Finset ℕ) (P : ℕ → Finset ℕ) (n : ℕ)
    (hPW : ∀ j, P j ⊆ W) (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ P j)
    (m : ℕ → ℕ) (hm : ∀ j, Even (m j)) (k : ℕ) :
    ∏ j ∈ range n, phi A M (P j) (cU (m j)) k
        - ∑ j ∈ range n, ∏ i ∈ range n,
            phi A M (P i) (if i = j then cE (m i) else cU (m i)) k ≤
      (if ∀ b ∈ W, ∀ a ∈ A, ¬ b ∣ a + M * k then (1 : ℝ) else 0) := by
  rw [ind_sift A M W P n hPW hcov k]
  have h0 : ∀ j, (0 : ℝ) ≤ (if nu A M (P j) k = 0 then (1 : ℝ) else 0) := fun j => by
    split_ifs <;> norm_num
  have h1 : ∀ j, (if nu A M (P j) k = 0 then (1 : ℝ) else 0) ≤ phi A M (P j) (cU (m j)) k :=
    fun j => (phiU_bounds A M (P j) (m j) k (hm j)).1
  have h2 : ∀ j, phi A M (P j) (cU (m j)) k ≤
      (if nu A M (P j) k = 0 then (1 : ℝ) else 0) + phi A M (P j) (cE (m j)) k :=
    fun j => (phiU_bounds A M (P j) (m j) k (hm j)).2
  have key : ∏ j ∈ range n, phi A M (P j) (cU (m j)) k
      - ∑ j ∈ range n, ∏ i ∈ range n,
          (if i = j then phi A M (P i) (cE (m i)) k else phi A M (P i) (cU (m i)) k)
      ≤ ∏ j ∈ range n, (if nu A M (P j) k = 0 then (1 : ℝ) else 0) :=
    hooley n (fun j => if nu A M (P j) k = 0 then (1 : ℝ) else 0)
      (fun j => phi A M (P j) (cU (m j)) k) (fun j => phi A M (P j) (cE (m j)) k) h0 h1 h2
  have hc : ∑ j ∈ range n, ∏ i ∈ range n, phi A M (P i) (if i = j then cE (m i) else cU (m i)) k
      = ∑ j ∈ range n, ∏ i ∈ range n,
          (if i = j then phi A M (P i) (cE (m i)) k else phi A M (P i) (cU (m i)) k) := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> rfl
  rw [hc]
  exact key

theorem sieve_sum (A : Finset ℕ) (M : ℕ) (W : Finset ℕ) (P : ℕ → Finset ℕ) (n : ℕ)
    (hPW : ∀ j, P j ⊆ W) (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ P j)
    (m : ℕ → ℕ) (hm : ∀ j, Even (m j)) (x : ℕ) :
    ∑ k ∈ Icc 1 x, ∏ j ∈ range n, phi A M (P j) (cU (m j)) k
        - ∑ j ∈ range n, ∑ k ∈ Icc 1 x, ∏ i ∈ range n,
            phi A M (P i) (if i = j then cE (m i) else cU (m i)) k ≤
      ((sift A M W x).card : ℝ) := by
  unfold sift
  rw [Finset.natCast_card_filter]
  have h : ∑ j ∈ range n, ∑ k ∈ Icc 1 x, ∏ i ∈ range n, phi A M (P i) (if i = j then cE (m i) else cU (m i)) k
      = ∑ k ∈ Icc 1 x, ∑ j ∈ range n, ∏ i ∈ range n, phi A M (P i) (if i = j then cE (m i) else cU (m i)) k :=
    Finset.sum_comm
  rw [h, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k _
  exact sift_pointwise A M W P n hPW hcov m hm k

theorem sieve_lower (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W)
    (P : ℕ → Finset ℕ) (n : ℕ) (hPW : ∀ j, P j ⊆ W)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ P j)
    (m : ℕ → ℕ) (hm : ∀ j, Even (m j)) (x : ℕ) :
    x * (∏ j ∈ range n, dens A.card (P j) (cU (m j))
          - ∑ j ∈ range n, ∏ i ∈ range n,
              dens A.card (P i) (if i = j then cE (m i) else cU (m i)))
        - (∏ j ∈ range n, mass A.card (P j) (cU (m j))
          + ∑ j ∈ range n, ∏ i ∈ range n,
              mass A.card (P i) (if i = j then cE (m i) else cU (m i))) ≤
      ((sift A M W x).card : ℝ) := by
  have h0 : |∑ k ∈ Icc 1 x, ∏ j ∈ range n, phi A M (P j) (cU (m j)) k
      - x * ∏ j ∈ range n, dens A.card (P j) (cU (m j))| ≤
        ∏ j ∈ range n, mass A.card (P j) (cU (m j)) :=
    sum_prod_phi A N M W hadm P hPW hdisj (fun j => cU (m j)) x n
  have h1 : ∀ j, |∑ k ∈ Icc 1 x, ∏ i ∈ range n, phi A M (P i) (if i = j then cE (m i) else cU (m i)) k
      - x * ∏ i ∈ range n, dens A.card (P i) (if i = j then cE (m i) else cU (m i))| ≤
        ∏ i ∈ range n, mass A.card (P i) (if i = j then cE (m i) else cU (m i)) :=
    fun j => sum_prod_phi A N M W hadm P hPW hdisj (fun i => if i = j then cE (m i) else cU (m i)) x n
  have hs := sieve_sum A M W P n hPW hcov m hm x
  have hl : x * ∏ j ∈ range n, dens A.card (P j) (cU (m j))
      - ∏ j ∈ range n, mass A.card (P j) (cU (m j))
      ≤ ∑ k ∈ Icc 1 x, ∏ j ∈ range n, phi A M (P j) (cU (m j)) k := by
    have := (abs_le.mp h0).1
    linarith
  have hu : ∀ j, ∑ k ∈ Icc 1 x, ∏ i ∈ range n, phi A M (P i) (if i = j then cE (m i) else cU (m i)) k
      ≤ x * ∏ i ∈ range n, dens A.card (P i) (if i = j then cE (m i) else cU (m i))
        + ∏ i ∈ range n, mass A.card (P i) (if i = j then cE (m i) else cU (m i)) := by
    intro j
    have := (abs_le.mp (h1 j)).2
    linarith
  have hsumu : ∑ j ∈ range n, ∑ k ∈ Icc 1 x, ∏ i ∈ range n, phi A M (P i) (if i = j then cE (m i) else cU (m i)) k
      ≤ ∑ j ∈ range n, (x * ∏ i ∈ range n, dens A.card (P i) (if i = j then cE (m i) else cU (m i))
        + ∏ i ∈ range n, mass A.card (P i) (if i = j then cE (m i) else cU (m i))) :=
    Finset.sum_le_sum (fun j _ => hu j)
  have hsplit : ∑ j ∈ range n, (x * ∏ i ∈ range n, dens A.card (P i) (if i = j then cE (m i) else cU (m i))
        + ∏ i ∈ range n, mass A.card (P i) (if i = j then cE (m i) else cU (m i)))
      = x * ∑ j ∈ range n, ∏ i ∈ range n, dens A.card (P i) (if i = j then cE (m i) else cU (m i))
        + ∑ j ∈ range n, ∏ i ∈ range n, mass A.card (P i) (if i = j then cE (m i) else cU (m i)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hD : x * (∏ j ∈ range n, dens A.card (P j) (cU (m j))
      - ∑ j ∈ range n, ∏ i ∈ range n, dens A.card (P i) (if i = j then cE (m i) else cU (m i)))
      = x * ∏ j ∈ range n, dens A.card (P j) (cU (m j))
        - x * ∑ j ∈ range n, ∏ i ∈ range n, dens A.card (P i) (if i = j then cE (m i) else cU (m i)) :=
    mul_sub _ _ _
  linarith

/- ## Block R: the remainder -/

theorem mass_nonneg (g : ℝ) (hg : 0 ≤ g) (P : Finset ℕ) (c : ℕ → ℝ) : 0 ≤ mass g P c := by
  unfold mass
  exact Finset.sum_nonneg (fun S _ => mul_nonneg (abs_nonneg _) (pow_nonneg hg _))

theorem mass_eq (g : ℝ) (P : Finset ℕ) (c : ℕ → ℝ) :
    mass g P c = ∑ i ∈ range (P.card + 1), (P.card.choose i : ℝ) * (|c i| * g ^ i) := by
  unfold mass
  rw [Finset.sum_powerset_apply_card (fun i => |c i| * g ^ i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [nsmul_eq_mul]

theorem choose_sum_le (p m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∑ i ∈ range (m + 2), (p.choose i : ℝ) * t ^ i ≤ (1 + t * p) ^ (m + 1) := by
  rw [add_comm 1, add_pow (t * (p : ℝ)) 1 (m + 1)]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ m + 1 := by
    rw [Finset.mem_range] at hi
    omega
  have h1 : (p.choose i : ℝ) ≤ (p : ℝ) ^ i := by exact_mod_cast Nat.choose_le_pow p i
  have h2 : (1 : ℝ) ≤ ((m + 1).choose i : ℝ) := by exact_mod_cast Nat.choose_pos hi'
  have h3 : 0 ≤ t ^ i := pow_nonneg ht i
  have h4 : (p.choose i : ℝ) * t ^ i ≤ (p : ℝ) ^ i * t ^ i := mul_le_mul_of_nonneg_right h1 h3
  have h5 : t ^ i * (p : ℝ) ^ i * 1 ≤ t ^ i * (p : ℝ) ^ i * ((m + 1).choose i : ℝ) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg h3 (pow_nonneg (Nat.cast_nonneg p) i))
  rw [one_pow, mul_one, mul_pow]
  nlinarith [h4, h5]

theorem mass_le (g : ℝ) (hg : 0 ≤ g) (P : Finset ℕ) (m : ℕ) :
    mass g P (cU m) + mass g P (cE m) ≤ (1 + g * P.card) ^ (m + 1) := by
  have hterm : ∀ i, (P.card.choose i : ℝ) * (|cU m i| * g ^ i) + (P.card.choose i : ℝ) * (|cE m i| * g ^ i)
      = if i ≤ m + 1 then (P.card.choose i : ℝ) * g ^ i else 0 := by
    intro i
    unfold cU cE
    by_cases h1 : i ≤ m
    · have h2 : i ≠ m + 1 := by omega
      have h3 : i ≤ m + 1 := by omega
      simp [h1, h2, h3, abs_pow]
    · by_cases h2 : i = m + 1
      · subst h2
        simp [abs_pow]
      · have h3 : ¬ i ≤ m + 1 := by omega
        simp [h1, h2, h3]
  rw [mass_eq, mass_eq, ← Finset.sum_add_distrib]
  calc ∑ i ∈ range (P.card + 1), ((P.card.choose i : ℝ) * (|cU m i| * g ^ i) + (P.card.choose i : ℝ) * (|cE m i| * g ^ i))
      = ∑ i ∈ range (P.card + 1), (if i ≤ m + 1 then (P.card.choose i : ℝ) * g ^ i else 0) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ∑ i ∈ (range (P.card + 1)).filter (fun i => i ≤ m + 1), (P.card.choose i : ℝ) * g ^ i :=
        (Finset.sum_filter _ _).symm
    _ ≤ ∑ i ∈ range (m + 2), (P.card.choose i : ℝ) * g ^ i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          omega
        · intro i _ _
          exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hg _)
    _ ≤ (1 + g * (P.card : ℝ)) ^ (m + 1) := choose_sum_le P.card m g hg

theorem prod_add_ge (n : ℕ) (a b : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    ∏ j ∈ range n, a j + ∑ j ∈ range n, ∏ i ∈ range n, (if i = j then b i else a i) ≤
      ∏ j ∈ range n, (a j + b j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hS : 0 ≤ ∑ j ∈ range n, ∏ i ∈ range n, (if i = j then b i else a i) := by
      apply Finset.sum_nonneg
      intro j _
      apply Finset.prod_nonneg
      intro i _
      split_ifs
      · exact hb i
      · exact ha i
    rw [sum_prod_ite_succ n b a]
    simp only [Finset.prod_range_succ]
    nlinarith [mul_le_mul_of_nonneg_right ih (add_nonneg (ha n) (hb n)), mul_nonneg hS (hb n)]

theorem one_add_le (g Z : ℕ) (hZ : 2 ≤ Z) : 1 + g * Z ≤ Z ^ (g + 1) := by
  induction g with
  | zero => simp <;> omega
  | succ g ih =>
    have h1 : Z ≤ Z ^ (g + 1) := le_self_pow (by omega) (by omega)
    have h3 : 2 * Z ^ (g + 1) ≤ Z * Z ^ (g + 1) := Nat.mul_le_mul_right _ hZ
    have h4 : Z ^ (g + 1 + 1) = Z * Z ^ (g + 1) := by ring
    rw [h4]
    nlinarith [ih, h1, h3]

theorem wsum_le (c n : ℕ) :
    ∑ j ∈ range n, 2 ^ (j + 1) * (c + 2 * (n - j)) ≤ 2 ^ (n + 1) * (c + 4) := by
  have key : ∀ n : ℕ, (∑ j ∈ range n, 2 ^ (j + 1) * (c + 2 * (n - j))) + 2 * c + 4 * n + 8
      = 2 ^ (n + 1) * (c + 4) := by
    intro n
    induction n with
    | zero => simp <;> ring
    | succ n ih =>
      rw [Finset.sum_range_succ']
      have h : ∀ j ∈ range n, 2 ^ (j + 1 + 1) * (c + 2 * (n + 1 - (j + 1)))
          = 2 * (2 ^ (j + 1) * (c + 2 * (n - j))) := by
        intro j _
        have hj : n + 1 - (j + 1) = n - j := by omega
        rw [hj]
        ring
      rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
      simp only [Nat.sub_zero, zero_add, pow_one]
      rw [pow_succ 2 (n + 1)]
      nlinarith [ih]
  linarith [key n]

theorem mm_even (a n j : ℕ) : Even (mm a n j) := by
  unfold mm
  exact even_two_mul _

theorem rem_factor (g a n j : ℕ) (P : Finset ℕ) (hP : P.card ≤ hi j) :
    (1 + (g : ℝ) * P.card) ^ (mm a n j + 1) ≤
      (2 : ℝ) ^ ((g + 1) * (2 ^ (j + 1) * ((2 * a + 1) + 2 * (n - j)))) := by
  have h2 : 2 ≤ hi j := by
    unfold hi
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  have hn : 1 + g * P.card ≤ (hi j) ^ (g + 1) :=
    le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left g hP) 1) (one_add_le g (hi j) h2)
  have hR : (1 + (g : ℝ) * P.card) ≤ ((hi j : ℕ) : ℝ) ^ (g + 1) := by exact_mod_cast hn
  have hmm : mm a n j + 1 = (2 * a + 1) + 2 * (n - j) := by
    unfold mm
    omega
  have hhi : ((hi j : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ (j + 1)) := by
    unfold hi
    norm_num
  calc (1 + (g : ℝ) * P.card) ^ (mm a n j + 1)
      ≤ (((hi j : ℕ) : ℝ) ^ (g + 1)) ^ (mm a n j + 1) :=
        pow_le_pow_left₀ (by positivity) hR _
    _ = (2 : ℝ) ^ (2 ^ (j + 1) * ((g + 1) * (mm a n j + 1))) := by
        rw [hhi, ← pow_mul, ← pow_mul]
    _ ≤ (2 : ℝ) ^ ((g + 1) * (2 ^ (j + 1) * ((2 * a + 1) + 2 * (n - j)))) := by
        apply pow_le_pow_right₀ (by norm_num)
        rw [← hmm]
        apply le_of_eq
        ring

theorem rem_bound (g a n : ℕ) (P : ℕ → Finset ℕ) (hP : ∀ j, (P j).card ≤ hi j) :
    ∏ j ∈ range n, (1 + (g : ℝ) * (P j).card) ^ (mm a n j + 1) ≤
      ((2 : ℝ) ^ 2 ^ n) ^ (2 * (g + 1) * (2 * a + 5)) := by
  have hE : ∑ j ∈ range n, (g + 1) * (2 ^ (j + 1) * ((2 * a + 1) + 2 * (n - j)))
      ≤ 2 ^ n * (2 * (g + 1) * (2 * a + 5)) := by
    rw [← Finset.mul_sum]
    calc (g + 1) * ∑ j ∈ range n, 2 ^ (j + 1) * ((2 * a + 1) + 2 * (n - j))
        ≤ (g + 1) * (2 ^ (n + 1) * (2 * a + 1 + 4)) :=
          Nat.mul_le_mul_left _ (wsum_le (2 * a + 1) n)
      _ = 2 ^ n * (2 * (g + 1) * (2 * a + 5)) := by ring
  calc ∏ j ∈ range n, (1 + (g : ℝ) * (P j).card) ^ (mm a n j + 1)
      ≤ ∏ j ∈ range n, (2 : ℝ) ^ ((g + 1) * (2 ^ (j + 1) * ((2 * a + 1) + 2 * (n - j)))) :=
        Finset.prod_le_prod (fun j _ => by positivity)
          (fun j _ => rem_factor g a n j (P j) (hP j))
    _ = (2 : ℝ) ^ (∑ j ∈ range n, (g + 1) * (2 ^ (j + 1) * ((2 * a + 1) + 2 * (n - j)))) := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ (2 : ℝ) ^ (2 ^ n * (2 * (g + 1) * (2 * a + 5))) :=
        pow_le_pow_right₀ (by norm_num) hE
    _ = ((2 : ℝ) ^ 2 ^ n) ^ (2 * (g + 1) * (2 * a + 5)) := by rw [← pow_mul]

/- ## Block M: the main term -/

theorem esym_zero (t : ℕ → ℝ) (P : Finset ℕ) : esym t P 0 = 1 := by
  unfold esym
  simp

theorem esym_insert (t : ℕ → ℝ) (P : Finset ℕ) (b : ℕ) (hb : b ∉ P) (i : ℕ) :
    esym t (insert b P) (i + 1) = esym t P (i + 1) + t b * esym t P i := by
  have hdisj : Disjoint (P.powersetCard (i + 1)) ((P.powersetCard i).image (insert b)) := by
    rw [Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS'
    exact hb ((Finset.mem_powersetCard.mp hS).1 (Finset.mem_insert_self b T))
  have hinj : Set.InjOn (insert b) ((P.powersetCard i : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    intro T hT T' hT' h
    have hTb : b ∉ T := fun h' => hb ((Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT)).1 h')
    have hT'b : b ∉ T' := fun h' => hb ((Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT')).1 h')
    have h1 : (insert b T).erase b = (insert b T').erase b := by rw [h]
    rwa [Finset.erase_insert hTb, Finset.erase_insert hT'b] at h1
  unfold esym
  rw [Finset.powersetCard_succ_insert hb, Finset.sum_union hdisj, Finset.sum_image hinj,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  have hTb : b ∉ T := fun h' => hb ((Finset.mem_powersetCard.mp hT).1 h')
  rw [Finset.prod_insert hTb]

theorem esym_nonneg (t : ℕ → ℝ) (P : Finset ℕ) (ht : ∀ b ∈ P, 0 ≤ t b) (i : ℕ) :
    0 ≤ esym t P i := by
  unfold esym
  apply Finset.sum_nonneg
  intro S hS
  apply Finset.prod_nonneg
  intro b hb
  exact ht b ((Finset.mem_powersetCard.mp hS).1 hb)

theorem dens_eq (g : ℝ) (P : Finset ℕ) (c : ℕ → ℝ) :
    dens g P c = ∑ i ∈ range (P.card + 1), c i * esym (fun b => g / (b : ℝ)) P i := by
  unfold dens esym
  have hmaps : ∀ S ∈ P.powerset, S.card ∈ range (P.card + 1) := fun S hS => by
    rw [Finset.mem_range]
    have := Finset.card_le_card (Finset.mem_powerset.mp hS)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.powersetCard_eq_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [(Finset.mem_powersetCard.mp hS).2]

theorem dens_cU (g : ℝ) (P : Finset ℕ) (m : ℕ) :
    dens g P (cU m) = ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym (fun b => g / (b : ℝ)) P i := by
  have hz : ∀ x, P.card < x → esym (fun b => g / (b : ℝ)) P x = 0 := by
    intro x hx
    unfold esym
    rw [Finset.powersetCard_eq_empty.mpr hx, Finset.sum_empty]
  rw [dens_eq]
  calc ∑ i ∈ range (P.card + 1), cU m i * esym (fun b => g / (b : ℝ)) P i
      = ∑ i ∈ range (P.card + m + 2), cU m i * esym (fun b => g / (b : ℝ)) P i := by
        apply Finset.sum_subset
        · intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega
        · intro x _ hx
          simp only [Finset.mem_range, not_lt] at hx
          rw [hz x (by omega), mul_zero]
    _ = ∑ i ∈ range (m + 1), cU m i * esym (fun b => g / (b : ℝ)) P i := by
        symm
        apply Finset.sum_subset
        · intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega
        · intro x _ hx
          simp only [Finset.mem_range, not_lt] at hx
          simp [cU, show ¬ x ≤ m by omega]
    _ = ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym (fun b => g / (b : ℝ)) P i := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx' : x ≤ m := by
          simp only [Finset.mem_range] at hx
          omega
        simp [cU, hx']

theorem dens_cE (g : ℝ) (P : Finset ℕ) (m : ℕ) :
    dens g P (cE m) = esym (fun b => g / (b : ℝ)) P (m + 1) := by
  rw [dens_eq, Finset.sum_eq_single (m + 1)]
  · simp [cE]
  · intro i _ hi
    simp [cE, hi]
  · intro hn
    have hn' : P.card < m + 1 := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    unfold esym
    rw [Finset.powersetCard_eq_empty.mpr hn', Finset.sum_empty]
    simp

theorem altsum_insert (t : ℕ → ℝ) (P : Finset ℕ) (b : ℕ) (hb : b ∉ P) (m : ℕ) :
    ∑ i ∈ range (m + 2), (-1 : ℝ) ^ i * esym t (insert b P) i =
      ∑ i ∈ range (m + 2), (-1 : ℝ) ^ i * esym t P i
        - t b * ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t P i := by
  have e1 : ∑ i ∈ range (m + 1), (-1 : ℝ) ^ (i + 1) * esym t (insert b P) (i + 1)
      = ∑ i ∈ range (m + 1), (-1 : ℝ) ^ (i + 1) * esym t P (i + 1)
        - t b * ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t P i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [esym_insert t P b hb i]
    ring
  rw [show m + 2 = m + 1 + 1 from rfl]
  rw [Finset.sum_range_succ' (fun i => (-1 : ℝ) ^ i * esym t (insert b P) i) (m + 1),
    Finset.sum_range_succ' (fun i => (-1 : ℝ) ^ i * esym t P i) (m + 1)]
  rw [e1]
  simp only [esym_zero]
  ring

theorem bonf_aux1 (t : ℕ → ℝ) (i : ℕ) : esym t ∅ (i + 1) = 0 := by
  unfold esym
  rw [Finset.powersetCard_eq_empty.mpr (show (∅ : Finset ℕ).card < i + 1 by simp)]
  simp

theorem bonf_aux2 (t : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t ∅ i = 1 := by
  rw [Finset.sum_range_succ']
  simp [bonf_aux1, esym_zero]

theorem bonf (t : ℕ → ℝ) (P : Finset ℕ) (ht : ∀ b ∈ P, 0 ≤ t b ∧ t b ≤ 1) (m : ℕ) :
    (Even m → ∏ b ∈ P, (1 - t b) ≤ ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t P i) ∧
      (Odd m → ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t P i ≤ ∏ b ∈ P, (1 - t b)) := by
  revert ht m
  refine Finset.induction_on P ?_ ?_
  · intro ht m
    rw [Finset.prod_empty, bonf_aux2]
    exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  · intro b P hb ih ht m
    have htb : 0 ≤ t b ∧ t b ≤ 1 := ht b (Finset.mem_insert_self b P)
    have hPt : ∀ c ∈ P, 0 ≤ t c ∧ t c ≤ 1 := fun c hc => ht c (Finset.mem_insert_of_mem hc)
    rw [Finset.prod_insert hb]
    have hP1 : ∏ c ∈ P, (1 - t c) ≤ 1 :=
      Finset.prod_le_one (fun c hc => by linarith [(hPt c hc).2])
        (fun c hc => by linarith [(hPt c hc).1])
    have hP0 : 0 ≤ ∏ c ∈ P, (1 - t c) :=
      Finset.prod_nonneg (fun c hc => by linarith [(hPt c hc).2])
    cases m with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, esym_zero, pow_zero, one_mul]
      refine ⟨fun _ => ?_, fun h => absurd (Nat.odd_iff.mp h) (by norm_num)⟩
      nlinarith [mul_nonneg htb.1 hP0]
    | succ m' =>
      have hA : ∑ i ∈ range (m' + 1 + 1), (-1 : ℝ) ^ i * esym t (insert b P) i =
          ∑ i ∈ range (m' + 1 + 1), (-1 : ℝ) ^ i * esym t P i
            - t b * ∑ i ∈ range (m' + 1), (-1 : ℝ) ^ i * esym t P i :=
        altsum_insert t P b hb m'
      have ihA := ih hPt (m' + 1)
      have ihB := ih hPt m'
      rw [hA]
      rcases Nat.even_or_odd m' with he | ho
      · have hodd : Odd (m' + 1) := he.add_one
        refine ⟨fun h => absurd h (Nat.not_even_iff_odd.mpr hodd), fun _ => ?_⟩
        nlinarith [ihA.2 hodd, ihB.1 he, mul_nonneg htb.1 (sub_nonneg.2 (ihB.1 he))]
      · have hev : Even (m' + 1) := ho.add_one
        refine ⟨fun _ => ?_, fun h => absurd h (Nat.not_odd_iff_even.mpr hev)⟩
        nlinarith [ihA.1 hev, ihB.2 ho, mul_nonneg htb.1 (sub_nonneg.2 (ihB.2 ho))]

theorem pow_succ_add_le (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) (i : ℕ) :
    s ^ (i + 1) + (i + 1) * u * s ^ i ≤ (s + u) ^ (i + 1) := by
  induction i with
  | zero => simp
  | succ k ih =>
    push_cast
    have h1 := mul_le_mul_of_nonneg_right ih (add_nonneg hs hu)
    have h2 : 0 ≤ ((k : ℝ) + 1) * u * u * s ^ k := by positivity
    have e1 : (s + u) ^ (k + 1 + 1) = (s + u) ^ (k + 1) * (s + u) := pow_succ _ _
    have e2 : s ^ (k + 1 + 1) = s ^ k * s * s := by ring
    have e3 : s ^ (k + 1) = s ^ k * s := by ring
    rw [e3] at h1
    rw [e1, e2, e3]
    nlinarith [h1, h2]

theorem esym_le (t : ℕ → ℝ) (P : Finset ℕ) (ht : ∀ b ∈ P, 0 ≤ t b) (i : ℕ) :
    esym t P i ≤ (∑ b ∈ P, t b) ^ i / (i.factorial : ℝ) := by
  revert ht i
  refine Finset.induction_on P ?_ ?_
  · intro ht i
    cases i with
    | zero => simp [esym_zero]
    | succ k =>
      rw [bonf_aux1]
      simp
  · intro b P hb ih ht i
    have htb : 0 ≤ t b := ht b (Finset.mem_insert_self b P)
    have hPt : ∀ c ∈ P, 0 ≤ t c := fun c hc => ht c (Finset.mem_insert_of_mem hc)
    have hS : 0 ≤ ∑ c ∈ P, t c := Finset.sum_nonneg hPt
    rw [Finset.sum_insert hb]
    cases i with
    | zero => simp [esym_zero]
    | succ k =>
      rw [esym_insert t P b hb k]
      have ih1 := ih hPt (k + 1)
      have ih0 := ih hPt k
      have key := pow_succ_add_le (∑ c ∈ P, t c) (t b) hS htb k
      have hF : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
      have hk : (0 : ℝ) < (k.factorial : ℝ) := by positivity
      have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have eq1 : (∑ c ∈ P, t c) ^ (k + 1) / ((k + 1).factorial : ℝ)
          + t b * ((∑ c ∈ P, t c) ^ k / (k.factorial : ℝ))
          = ((∑ c ∈ P, t c) ^ (k + 1) + ((k : ℝ) + 1) * t b * (∑ c ∈ P, t c) ^ k)
              / ((k + 1).factorial : ℝ) := by
        rw [hfac]
        field_simp
      have hle : ((∑ c ∈ P, t c) ^ (k + 1) + ((k : ℝ) + 1) * t b * (∑ c ∈ P, t c) ^ k)
            / ((k + 1).factorial : ℝ)
          ≤ (t b + ∑ c ∈ P, t c) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ hF.le
        rw [add_comm (t b) (∑ c ∈ P, t c)]
        exact key
      calc esym t P (k + 1) + t b * esym t P k
          ≤ (∑ c ∈ P, t c) ^ (k + 1) / ((k + 1).factorial : ℝ)
              + t b * ((∑ c ∈ P, t c) ^ k / (k.factorial : ℝ)) :=
            add_le_add ih1 (mul_le_mul_of_nonneg_left ih0 htb)
        _ = _ := eq1
        _ ≤ _ := hle

theorem one_sub_ge_exp (G t : ℝ) (hG : 0 ≤ G) (ht : 0 ≤ t) (h : t * (G + 1) ≤ G) :
    Real.exp (-((G + 1) * t)) ≤ 1 - t := by
  have h1 : 0 ≤ 1 - t := by nlinarith
  have h2 := Real.add_one_le_exp ((G + 1) * t)
  have key : 1 ≤ (1 - t) * Real.exp ((G + 1) * t) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 h1, mul_nonneg ht (sub_nonneg.mpr h)]
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  linarith

theorem V_ge_exp (G : ℝ) (hG : 0 ≤ G) (t : ℕ → ℝ) (P : Finset ℕ)
    (ht : ∀ b ∈ P, 0 ≤ t b ∧ t b * (G + 1) ≤ G) :
    Real.exp (-((G + 1) * ∑ b ∈ P, t b)) ≤ ∏ b ∈ P, (1 - t b) := by
  have hsum : -((G + 1) * ∑ b ∈ P, t b) = ∑ b ∈ P, -((G + 1) * t b) := by
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hsum, Real.exp_sum]
  exact Finset.prod_le_prod (fun b _ => Real.exp_nonneg _)
    (fun b hb => one_sub_ge_exp G (t b) hG (ht b hb).1 (ht b hb).2)

theorem block_V (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W) (P : Finset ℕ)
    (hP : P ⊆ W) (m : ℕ) (hm : Even m) :
    0 < ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) ∧
      ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) ≤ dens A.card P (cU m) := by
  have hbd : ∀ b ∈ P, (A.card : ℝ) < (b : ℝ) ∧ 0 < (b : ℝ) := by
    intro b hb
    have h1 : A.card < b := adm_card_lt A N M W hadm b (hP hb)
    have h2 : (A.card : ℝ) < (b : ℝ) := by exact_mod_cast h1
    exact ⟨h2, lt_of_le_of_lt (Nat.cast_nonneg _) h2⟩
  constructor
  · apply Finset.prod_pos
    intro b hb
    have h3 : (A.card : ℝ) / (b : ℝ) < 1 := (div_lt_one (hbd b hb).2).mpr (hbd b hb).1
    linarith
  · rw [dens_cU]
    exact (bonf (fun b => (A.card : ℝ) / (b : ℝ)) P
      (fun b hb => ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
        (div_le_one (hbd b hb).2).mpr (hbd b hb).1.le⟩) m).1 hm

theorem block_eps_num (g : ℝ) (hg : 0 ≤ g) (P : Finset ℕ)
    (hsum : ∑ b ∈ P, (1 / (b : ℝ)) ≤ 18) (m : ℕ) :
    0 ≤ dens g P (cE m) ∧
      dens g P (cE m) ≤ (18 * g) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  have hnn : ∀ b ∈ P, 0 ≤ g / (b : ℝ) := fun b _ => div_nonneg hg (Nat.cast_nonneg _)
  rw [dens_cE]
  refine ⟨esym_nonneg _ P hnn (m + 1), ?_⟩
  have e : ∑ b ∈ P, g / (b : ℝ) = g * ∑ b ∈ P, 1 / (b : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hs : ∑ b ∈ P, g / (b : ℝ) ≤ 18 * g := by
    rw [e]
    have := mul_le_mul_of_nonneg_left hsum hg
    linarith
  have hs0 : 0 ≤ ∑ b ∈ P, g / (b : ℝ) := Finset.sum_nonneg hnn
  calc esym (fun b => g / (b : ℝ)) P (m + 1)
      ≤ (∑ b ∈ P, g / (b : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) := esym_le _ P hnn (m + 1)
    _ ≤ (18 * g) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
      gcongr

theorem block_V_exp (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W)
    (P : Finset ℕ) (hP : P ⊆ W) (hsum : ∑ b ∈ P, (1 / (b : ℝ)) ≤ 18) :
    Real.exp (-(((A.card : ℝ) + 1) * (18 * (A.card : ℝ)))) ≤
      ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) := by
  have hcond : ∀ b ∈ P, 0 ≤ (A.card : ℝ) / (b : ℝ) ∧
      (A.card : ℝ) / (b : ℝ) * ((A.card : ℝ) + 1) ≤ (A.card : ℝ) := by
    intro b hb
    have h1 : A.card < b := adm_card_lt A N M W hadm b (hP hb)
    have h3 : (A.card : ℝ) < (b : ℝ) := by exact_mod_cast h1
    have h2 : (A.card : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast h1
    have hb0 : (0 : ℝ) < (b : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg _) h3
    refine ⟨div_nonneg (Nat.cast_nonneg _) hb0.le, ?_⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ hb0]
    exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  have hV := V_ge_exp (A.card : ℝ) (Nat.cast_nonneg _) (fun b => (A.card : ℝ) / (b : ℝ)) P hcond
  have hsum' : ∑ b ∈ P, (A.card : ℝ) / (b : ℝ) ≤ 18 * (A.card : ℝ) := by
    have e : ∑ b ∈ P, (A.card : ℝ) / (b : ℝ) = (A.card : ℝ) * ∑ b ∈ P, 1 / (b : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) A.card)
    linarith
  have hle : Real.exp (-(((A.card : ℝ) + 1) * (18 * (A.card : ℝ)))) ≤
      Real.exp (-(((A.card : ℝ) + 1) * ∑ b ∈ P, (A.card : ℝ) / (b : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hsum' (by positivity : (0 : ℝ) ≤ (A.card : ℝ) + 1)
    linarith
  exact le_trans hle hV

theorem block_eps (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W) (P : Finset ℕ)
    (hP : P ⊆ W) (hsum : ∑ b ∈ P, (1 / (b : ℝ)) ≤ 18) (m : ℕ) :
    0 ≤ dens A.card P (cE m) ∧
      dens A.card P (cE m) / ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) ≤
        (18 * (A.card : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) *
          Real.exp (((A.card : ℝ) + 1) * (18 * (A.card : ℝ))) := by
  obtain ⟨h0, hle⟩ := block_eps_num (A.card : ℝ) (Nat.cast_nonneg _) P hsum m
  have hV := block_V A N M W hadm P hP 0 ⟨0, rfl⟩
  have hVe := block_V_exp A N M W hadm P hP hsum
  refine ⟨h0, ?_⟩
  have h1 : Real.exp (((A.card : ℝ) + 1) * (18 * (A.card : ℝ))) *
      Real.exp (-(((A.card : ℝ) + 1) * (18 * (A.card : ℝ)))) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h2 : 1 ≤ Real.exp (((A.card : ℝ) + 1) * (18 * (A.card : ℝ))) *
      ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hVe (Real.exp_pos (((A.card : ℝ) + 1) * (18 * (A.card : ℝ)))).le
    linarith
  have hQ : 0 ≤ (18 * (A.card : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) := by positivity
  rw [div_le_iff₀ hV.1]
  calc dens (A.card : ℝ) P (cE m)
      ≤ (18 * (A.card : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) := hle
    _ ≤ (18 * (A.card : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) *
          (Real.exp (((A.card : ℝ) + 1) * (18 * (A.card : ℝ))) *
            ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ))) := le_mul_of_one_le_right hQ h2
    _ = (18 * (A.card : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ) *
          Real.exp (((A.card : ℝ) + 1) * (18 * (A.card : ℝ))) *
            ∏ b ∈ P, (1 - (A.card : ℝ) / (b : ℝ)) := by ring

theorem main_term (n : ℕ) (sg V ε : ℕ → ℝ) (hV : ∀ j, 0 < V j) (hsg : ∀ j, V j ≤ sg j)
    (hε : ∀ j, 0 ≤ ε j) (hsum : ∑ j ∈ range n, ε j / V j ≤ 1 / 2) :
    1 / 2 * ∏ j ∈ range n, V j ≤
      ∏ j ∈ range n, sg j - ∑ j ∈ range n, ∏ i ∈ range n, (if i = j then ε i else sg i) := by
  have hP0 : 0 ≤ ∏ i ∈ range n, sg i :=
    Finset.prod_nonneg (fun i _ => le_trans (hV i).le (hsg i))
  have hX : ∀ j ∈ range n, (∏ i ∈ range n, (if i = j then ε i else sg i)) ≤
      ε j / V j * ∏ i ∈ range n, sg i := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hXnn : 0 ≤ ∏ i ∈ range n, (if i = j then ε i else sg i) :=
      Finset.prod_nonneg (fun i _ => by
        split_ifs
        · exact hε i
        · exact le_trans (hV i).le (hsg i))
    have hkey := prod_ite_mul n j hjn ε sg
    have hm : (∏ i ∈ range n, (if i = j then ε i else sg i)) * V j ≤
        (∏ i ∈ range n, (if i = j then ε i else sg i)) * sg j :=
      mul_le_mul_of_nonneg_left (hsg j) hXnn
    rw [div_mul_eq_mul_div, le_div_iff₀ (hV j)]
    linarith
  have hXsum : ∑ j ∈ range n, (∏ i ∈ range n, (if i = j then ε i else sg i)) ≤
      ∑ j ∈ range n, ε j / V j * ∏ i ∈ range n, sg i := Finset.sum_le_sum hX
  rw [← Finset.sum_mul] at hXsum
  have h2 : (∑ j ∈ range n, ε j / V j) * ∏ i ∈ range n, sg i ≤ 1 / 2 * ∏ i ∈ range n, sg i :=
    mul_le_mul_of_nonneg_right hsum hP0
  have hV' : ∏ i ∈ range n, V i ≤ ∏ i ∈ range n, sg i :=
    Finset.prod_le_prod (fun i _ => (hV i).le) (fun i _ => hsg i)
  linarith

/- ## Block D: pairwise coprime moduli are sparse -/

theorem lcmUpto_le (n : ℕ) : (Nat.lcmUpto n : ℝ) ≤ Real.exp (6 * (n : ℝ)) := by
  have hpos : (0 : ℝ) < (Nat.lcmUpto n : ℝ) := by exact_mod_cast Nat.lcmUpto_pos n
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) n)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h4 : Real.log 4 + 4 ≤ 6 := by
    have : (0.6931471808 : ℝ) < 1 := by norm_num
    linarith
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith [mul_le_mul_of_nonneg_right h4 hn]

theorem prod_dvd_lcmUpto (W : Finset ℕ) (hco : (W : Set ℕ).Pairwise Nat.Coprime) (n : ℕ)
    (hW : ∀ b ∈ W, 1 ≤ b ∧ b ≤ n) : (∏ b ∈ W, b) ∣ Nat.lcmUpto n := by
  have hrel : (W : Set ℕ).Pairwise (fun a b : ℕ => IsRelPrime a b) := fun a ha b hb hab =>
    Nat.coprime_iff_isRelPrime.mp (hco ha hb hab)
  have hdvd : ∀ b ∈ W, (fun b : ℕ => b) b ∣ Nat.lcmUpto n := by
    intro b hb
    unfold Nat.lcmUpto
    exact Finset.dvd_lcm (Finset.mem_Icc.mpr (hW b hb))
  exact Finset.prod_dvd_of_isRelPrime hrel hdvd

theorem dyadic_card (W : Finset ℕ) (hco : (W : Set ℕ).Pairwise Nat.Coprime) (i : ℕ)
    (hW : ∀ b ∈ W, 2 ^ i < b ∧ b ≤ 2 ^ (i + 1)) : (W.card : ℝ) * i ≤ 18 * 2 ^ i := by
  have hW' : ∀ b ∈ W, 1 ≤ b ∧ b ≤ 2 ^ (i + 1) := fun b hb =>
    ⟨Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) (hW b hb).1), (hW b hb).2⟩
  have hnat : (2 ^ i) ^ W.card ≤ Nat.lcmUpto (2 ^ (i + 1)) := by
    calc (2 ^ i) ^ W.card ≤ ∏ b ∈ W, b :=
          Finset.pow_card_le_prod W (fun b => b) (2 ^ i) (fun b hb => (hW b hb).1.le)
      _ ≤ Nat.lcmUpto (2 ^ (i + 1)) :=
          Nat.le_of_dvd (Nat.lcmUpto_pos _) (prod_dvd_lcmUpto W hco _ hW')
  have hreal : ((2 : ℝ) ^ i) ^ W.card ≤ Real.exp (6 * (2 : ℝ) ^ (i + 1)) := by
    have h2 : (((2 ^ i) ^ W.card : ℕ) : ℝ) ≤ (Nat.lcmUpto (2 ^ (i + 1)) : ℝ) := by
      exact_mod_cast hnat
    have h3 := lcmUpto_le (2 ^ (i + 1))
    push_cast at h2 h3
    exact le_trans h2 h3
  have hlog := Real.log_le_log (by positivity) hreal
  rw [Real.log_pow, Real.log_exp, Real.log_pow] at hlog
  have e : (2 : ℝ) ^ (i + 1) = 2 * 2 ^ i := by ring
  rw [e] at hlog
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hc : 0 ≤ (W.card : ℝ) * i := by positivity
  have h3 : (W.card : ℝ) * i * (2 / 3) ≤ (W.card : ℝ) * i * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2.le hc
  nlinarith

theorem dyadic_sum (W : Finset ℕ) (hco : (W : Set ℕ).Pairwise Nat.Coprime) (i : ℕ) (hi : 1 ≤ i)
    (hW : ∀ b ∈ W, 2 ^ i < b ∧ b ≤ 2 ^ (i + 1)) : ∑ b ∈ W, (1 / (b : ℝ)) ≤ 18 / i := by
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hc := dyadic_card W hco i hW
  have hpos : (0 : ℝ) < 2 ^ i := by positivity
  have hle : ∀ b ∈ W, 1 / (b : ℝ) ≤ 1 / (2 : ℝ) ^ i := by
    intro b hb
    have h1 : (2 : ℝ) ^ i < b := by exact_mod_cast (hW b hb).1
    exact one_div_le_one_div_of_le hpos h1.le
  have hsum := Finset.sum_le_card_nsmul W (fun b => 1 / (b : ℝ)) (1 / (2 : ℝ) ^ i) hle
  rw [nsmul_eq_mul] at hsum
  have hfin : (W.card : ℝ) * (1 / (2 : ℝ) ^ i) ≤ 18 / i := by
    rw [mul_one_div, div_le_div_iff₀ hpos (by linarith)]
    linarith
  exact le_trans hsum hfin

theorem dyadic_cover (j b : ℕ) (h1 : 2 ^ 2 ^ j < b) (h2 : b ≤ 2 ^ 2 ^ (j + 1)) :
    ∃ i, i ∈ Ico (2 ^ j) (2 ^ (j + 1)) ∧ 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) := by
  have hp1 : 1 ≤ 2 ^ 2 ^ j := Nat.one_le_two_pow
  have hx1 : 2 ^ 2 ^ j ≤ b - 1 := by omega
  have hx0 : b - 1 ≠ 0 := by omega
  have hA : 2 ^ Nat.log 2 (b - 1) ≤ b - 1 := Nat.pow_log_le_self 2 hx0
  have hB : b - 1 < 2 ^ (Nat.log 2 (b - 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hi1 : 2 ^ j < Nat.log 2 (b - 1) + 1 :=
    (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp (lt_of_le_of_lt hx1 hB)
  have hi2 : Nat.log 2 (b - 1) < 2 ^ (j + 1) :=
    (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp
      (lt_of_le_of_lt hA (lt_of_lt_of_le (by omega) h2))
  exact ⟨Nat.log 2 (b - 1), Finset.mem_Ico.mpr ⟨by omega, hi2⟩, by omega, by omega⟩

theorem dyadic_split (j b : ℕ) (h1 : 2 ^ 2 ^ j < b) (h2 : b ≤ 2 ^ 2 ^ (j + 1)) (f : ℝ)
    (hf : 0 ≤ f) :
    f ≤ ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)), (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then f else 0) := by
  obtain ⟨i, hI, hlt, hle⟩ := dyadic_cover j b h1 h2
  calc f = (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then f else 0) := by rw [if_pos ⟨hlt, hle⟩]
    _ ≤ ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)), (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then f else 0) :=
      Finset.single_le_sum (f := fun i => if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then f else 0)
        (fun k _ => by split_ifs <;> linarith) hI

theorem superdyadic_sum (W : Finset ℕ) (hco : (W : Set ℕ).Pairwise Nat.Coprime) (j : ℕ)
    (hW : ∀ b ∈ W, 2 ^ 2 ^ j < b ∧ b ≤ 2 ^ 2 ^ (j + 1)) : ∑ b ∈ W, (1 / (b : ℝ)) ≤ 18 := by
  have hstep : ∀ b ∈ W, (1 / (b : ℝ)) ≤ ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)),
      (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then (1 / (b : ℝ)) else 0) := by
    intro b hb
    have hb1 : 0 ≤ 1 / (b : ℝ) := by positivity
    exact dyadic_split j b (hW b hb).1 (hW b hb).2 _ hb1
  have hsum : ∑ b ∈ W, (1 / (b : ℝ)) ≤ ∑ b ∈ W, ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)),
      (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then (1 / (b : ℝ)) else 0) :=
    Finset.sum_le_sum hstep
  rw [Finset.sum_comm] at hsum
  have hblock : ∀ i ∈ Ico (2 ^ j) (2 ^ (j + 1)),
      ∑ b ∈ W, (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then (1 / (b : ℝ)) else 0) ≤ 18 / 2 ^ j := by
    intro i hI
    have hI' : 2 ^ j ≤ i := (Finset.mem_Ico.mp hI).1
    have hpos : 1 ≤ i := le_trans Nat.one_le_two_pow hI'
    have hd := dyadic_sum (W.filter (fun b => 2 ^ i < b ∧ b ≤ 2 ^ (i + 1)))
      (Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hco) i hpos
      (fun b hb => (Finset.mem_filter.mp hb).2)
    rw [← Finset.sum_filter]
    have hcast : (2 : ℝ) ^ j ≤ (i : ℝ) := by exact_mod_cast hI'
    calc ∑ b ∈ W.filter (fun b => 2 ^ i < b ∧ b ≤ 2 ^ (i + 1)), (1 / (b : ℝ))
        ≤ 18 / (i : ℝ) := hd
      _ ≤ 18 / 2 ^ j := div_le_div_of_nonneg_left (by norm_num) (by positivity) hcast
  have hc : 2 ^ (j + 1) - 2 ^ j = 2 ^ j := by rw [pow_succ]; omega
  calc ∑ b ∈ W, (1 / (b : ℝ))
      ≤ ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)), ∑ b ∈ W,
          (if 2 ^ i < b ∧ b ≤ 2 ^ (i + 1) then (1 / (b : ℝ)) else 0) := hsum
    _ ≤ ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)), (18 / 2 ^ j : ℝ) := Finset.sum_le_sum hblock
    _ = 18 := by
      rw [Finset.sum_const, Nat.card_Ico, hc, nsmul_eq_mul]
      push_cast
      field_simp

theorem blk_sum (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W) (j : ℕ) :
    ∑ b ∈ blk W j, (1 / (b : ℝ)) ≤ 18 := by
  have hsub : blk W j ⊆ W := Finset.filter_subset _ _
  have hco : (blk W j : Set ℕ).Pairwise Nat.Coprime :=
    Set.Pairwise.mono (Finset.coe_subset.mpr hsub) hadm.2.1
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have hlo0 : lo 0 = 0 := by unfold lo; rw [if_pos rfl]
    have hhi0 : hi 0 = 4 := by unfold hi; norm_num
    have hI : blk W 0 ⊆ Icc 1 4 := by
      intro b hb
      unfold blk at hb
      obtain ⟨hbW, hb1, hb2⟩ := Finset.mem_filter.mp hb
      rw [hlo0] at hb1
      rw [hhi0] at hb2
      have hN := (hadm.2.2 b hbW).1
      exact Finset.mem_Icc.mpr ⟨by omega, hb2⟩
    have hcard : (blk W 0).card ≤ 4 := by
      have h := Finset.card_le_card hI
      rw [Nat.card_Icc] at h
      omega
    have hle1 : ∀ b ∈ blk W 0, 1 / (b : ℝ) ≤ 1 := by
      intro b hb
      have hbW := hsub hb
      have hN := (hadm.2.2 b hbW).1
      have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h := Finset.sum_le_card_nsmul (blk W 0) (fun b => 1 / (b : ℝ)) 1 hle1
    rw [nsmul_eq_mul, mul_one] at h
    have hc : ((blk W 0).card : ℝ) ≤ 4 := by exact_mod_cast hcard
    linarith
  · have hlo : lo j = 2 ^ 2 ^ j := by unfold lo; rw [if_neg (by omega)]
    refine superdyadic_sum (blk W j) hco j (fun b hb => ?_)
    unfold blk at hb
    obtain ⟨_, hb1, hb2⟩ := Finset.mem_filter.mp hb
    rw [hlo] at hb1
    exact ⟨hb1, hb2⟩

theorem blk_sub (W : Finset ℕ) (j : ℕ) : blk W j ⊆ W := by
  unfold blk
  exact Finset.filter_subset _ _

theorem blk_disj (W : Finset ℕ) (i j : ℕ) (hij : i ≠ j) : Disjoint (blk W i) (blk W j) := by
  have key : ∀ p q : ℕ, p < q → Disjoint (blk W p) (blk W q) := by
    intro p q hpq
    rw [Finset.disjoint_left]
    intro b hbp hbq
    unfold blk at hbp hbq
    have h1 := (Finset.mem_filter.mp hbp).2.2
    have h2 := (Finset.mem_filter.mp hbq).2.1
    have hq : q ≠ 0 := by omega
    have hlo : lo q = 2 ^ 2 ^ q := by unfold lo; rw [if_neg hq]
    have hle : hi p ≤ lo q := by
      rw [hlo]
      unfold hi
      have h3 : 2 ^ (p + 1) ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact Nat.pow_le_pow_right (by norm_num) h3
    omega
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem blk_cover_aux1 (b : ℕ) (hb : 1 ≤ b) (m : ℕ) :
    b ≤ 2 ^ 2 ^ (m + 1) → ∃ j, j < m + 1 ∧ lo j < b ∧ b ≤ hi j := by
  induction m with
  | zero =>
    intro hm
    refine ⟨0, by norm_num, ?_, hm⟩
    show (if (0 : ℕ) = 0 then 0 else 2 ^ 2 ^ 0) < b
    rw [if_pos rfl]
    omega
  | succ m ih =>
    intro hm
    by_cases h : b ≤ 2 ^ 2 ^ (m + 1)
    · obtain ⟨j, hj, h1, h2⟩ := ih h
      exact ⟨j, by omega, h1, h2⟩
    · refine ⟨m + 1, by omega, ?_, hm⟩
      unfold lo
      rw [if_neg (by omega)]
      omega
theorem blk_cover (W : Finset ℕ) (n : ℕ) (hn : 1 ≤ n) (hW : ∀ b ∈ W, 1 ≤ b ∧ b ≤ 2 ^ 2 ^ n) :
    ∀ b ∈ W, ∃ j, j < n ∧ b ∈ blk W j := by
  intro b hb
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, hj, h1, h2⟩ := blk_cover_aux1 b (hW b hb).1 m (hW b hb).2
  exact ⟨j, hj, by unfold blk; exact Finset.mem_filter.mpr ⟨hb, h1, h2⟩⟩

theorem blk_card (W : Finset ℕ) (j : ℕ) : (blk W j).card ≤ hi j := by
  have hsub : blk W j ⊆ Ioc (lo j) (hi j) := by
    intro b hb
    unfold blk at hb
    rw [Finset.mem_filter] at hb
    rw [Finset.mem_Ioc]
    exact hb.2
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at h1
  omega

theorem prod_blk (W : Finset ℕ) (n : ℕ) (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ blk W j)
    (f : ℕ → ℝ) : ∏ j ∈ range n, ∏ b ∈ blk W j, f b = ∏ b ∈ W, f b := by
  have hU : (range n).biUnion (blk W) = W := by
    ext b
    constructor
    · intro hb
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hb
      exact blk_sub W j hj
    · intro hb
      obtain ⟨j, hj, hbj⟩ := hcov b hb
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hbj⟩
  have hdisj : ((range n : Finset ℕ) : Set ℕ).PairwiseDisjoint (blk W) :=
    fun i _ j _ hij => blk_disj W i j hij
  conv_rhs => rw [← hU]
  rw [Finset.prod_biUnion hdisj]

/- ## Block N: numerics -/

theorem pow_fact_le (s : ℝ) (hs : 0 ≤ s) (q0 q : ℕ) (h0 : 2 * s ≤ q0) (hq : q0 ≤ q) :
    s ^ q / (q.factorial : ℝ) ≤ Real.exp s * 2 ^ q0 / 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base =>
    have h := Real.pow_div_factorial_le_exp s hs q0
    have e : Real.exp s * 2 ^ q0 / 2 ^ q0 = Real.exp s := by field_simp
    rw [e]
    exact h
  | succ q hq ih =>
    have hfac : s ^ (q + 1) / ((q + 1).factorial : ℝ) = s ^ q / (q.factorial : ℝ) * (s / ((q : ℝ) + 1)) := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    have hqR : (q0 : ℝ) ≤ q := by exact_mod_cast hq
    have hratio : s / ((q : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hnn : 0 ≤ s / ((q : ℝ) + 1) := by positivity
    have hE : 0 ≤ Real.exp s * 2 ^ q0 / 2 ^ q := by positivity
    rw [hfac]
    calc s ^ q / (q.factorial : ℝ) * (s / ((q : ℝ) + 1))
        ≤ (Real.exp s * 2 ^ q0 / 2 ^ q) * (1 / 2) := mul_le_mul ih hratio hnn hE
      _ = Real.exp s * 2 ^ q0 / 2 ^ (q + 1) := by
        rw [pow_succ]
        field_simp

theorem geom_tail (n : ℕ) : ∑ j ∈ range n, (1 / 4 : ℝ) ^ (n - j) ≤ 1 / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : ∑ j ∈ range (n + 1), (1 / 4 : ℝ) ^ (n + 1 - j)
        = 1 / 4 * ∑ j ∈ range n, (1 / 4 : ℝ) ^ (n - j) + 1 / 4 := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        have hsub : n + 1 - j = (n - j) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      · simp
    rw [key]
    linarith

theorem ratio_term (s G : ℝ) (hs : 0 ≤ s) (q0 a n j : ℕ) (h0 : 2 * s ≤ q0)
    (ha1 : q0 ≤ 2 * a + 1) (ha2 : Real.exp ((G + 2) * s) * 2 ^ q0 ≤ 2 ^ (2 * a)) :
    s ^ (mm a n j + 1) / ((mm a n j + 1).factorial : ℝ) * Real.exp ((G + 1) * s) ≤
      1 / 2 * (1 / 4 : ℝ) ^ (n - j) := by
  have hmm : mm a n j + 1 = 2 * a + 2 * (n - j) + 1 := by unfold mm; omega
  have hq : q0 ≤ mm a n j + 1 := by unfold mm; omega
  have h1 := pow_fact_le s hs q0 (mm a n j + 1) h0 hq
  have hE : Real.exp s * Real.exp ((G + 1) * s) = Real.exp ((G + 2) * s) := by
    rw [← Real.exp_add]
    ring_nf
  have hpos : 0 ≤ Real.exp ((G + 1) * s) := (Real.exp_pos _).le
  have h4 : (4 : ℝ) ^ (n - j) = 2 ^ (2 * (n - j)) := by
    rw [pow_mul]
    norm_num
  have hpow : (2 : ℝ) ^ (mm a n j + 1) = 2 ^ (2 * a) * 2 * 4 ^ (n - j) := by
    rw [hmm, h4]
    ring
  calc s ^ (mm a n j + 1) / ((mm a n j + 1).factorial : ℝ) * Real.exp ((G + 1) * s)
      ≤ (Real.exp s * 2 ^ q0 / 2 ^ (mm a n j + 1)) * Real.exp ((G + 1) * s) :=
        mul_le_mul_of_nonneg_right h1 hpos
    _ = (Real.exp s * Real.exp ((G + 1) * s)) * 2 ^ q0 / 2 ^ (mm a n j + 1) := by ring
    _ = Real.exp ((G + 2) * s) * 2 ^ q0 / 2 ^ (mm a n j + 1) := by rw [hE]
    _ ≤ 2 ^ (2 * a) / 2 ^ (mm a n j + 1) := by gcongr
    _ = 1 / 2 * (1 / 4 : ℝ) ^ (n - j) := by
      rw [hpow, one_div_pow]
      field_simp

theorem ratio_sum (s G : ℝ) (hs : 0 ≤ s) (q0 a n : ℕ) (h0 : 2 * s ≤ q0) (ha1 : q0 ≤ 2 * a + 1)
    (ha2 : Real.exp ((G + 2) * s) * 2 ^ q0 ≤ 2 ^ (2 * a)) :
    ∑ j ∈ range n, s ^ (mm a n j + 1) / ((mm a n j + 1).factorial : ℝ) * Real.exp ((G + 1) * s) ≤
      1 / 2 := by
  calc ∑ j ∈ range n, s ^ (mm a n j + 1) / ((mm a n j + 1).factorial : ℝ) * Real.exp ((G + 1) * s)
      ≤ ∑ j ∈ range n, 1 / 2 * (1 / 4 : ℝ) ^ (n - j) :=
        Finset.sum_le_sum (fun j _ => ratio_term s G hs q0 a n j h0 ha1 ha2)
    _ = 1 / 2 * ∑ j ∈ range n, (1 / 4 : ℝ) ^ (n - j) := by rw [Finset.mul_sum]
    _ ≤ 1 / 2 * (1 / 3) := mul_le_mul_of_nonneg_left (geom_tail n) (by norm_num)
    _ ≤ 1 / 2 := by norm_num

theorem exists_params (g : ℕ) :
    ∃ q0 a : ℕ, 2 * (18 * (g : ℝ)) ≤ q0 ∧ q0 ≤ 2 * a + 1 ∧
      Real.exp (((g : ℝ) + 2) * (18 * (g : ℝ))) * 2 ^ q0 ≤ 2 ^ (2 * a) := by
  obtain ⟨a0, ha0⟩ := pow_unbounded_of_one_lt
    (Real.exp (((g : ℝ) + 2) * (18 * (g : ℝ))) * 2 ^ (36 * g)) (by norm_num : (1 : ℝ) < 4)
  refine ⟨36 * g, a0 + 36 * g, ?_, by omega, ?_⟩
  · push_cast
    linarith
  · have h4 : (4 : ℝ) ^ a0 ≤ 4 ^ (a0 + 36 * g) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : (2 : ℝ) ^ (2 * (a0 + 36 * g)) = 4 ^ (a0 + 36 * g) := by
      rw [pow_mul]
      norm_num
    rw [e]
    linarith

theorem exists_n (y : ℕ) (hy : 2 ≤ y) : ∃ n : ℕ, 1 ≤ n ∧ y ≤ 2 ^ 2 ^ n ∧ 2 ^ 2 ^ n ≤ y ^ 2 := by
  classical
  have h1 : y ≤ 2 ^ y := (@Nat.lt_two_pow_self y).le
  have hex : ∃ n, y ≤ 2 ^ 2 ^ n := ⟨y, le_trans h1 (Nat.pow_le_pow_right (by norm_num) h1)⟩
  have hspec : y ≤ 2 ^ 2 ^ (Nat.find hex) := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0] at hspec
    norm_num at hspec
    have hy2 : y = 2 := by omega
    subst hy2
    exact ⟨1, le_refl _, by norm_num, by norm_num⟩
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin : ¬ y ≤ 2 ^ 2 ^ k := Nat.find_min hex (by omega)
    have hlt : 2 ^ 2 ^ k < y := not_le.mp hmin
    rw [hk] at hspec
    refine ⟨k + 1, by omega, hspec, ?_⟩
    have heq : 2 ^ 2 ^ (k + 1) = (2 ^ 2 ^ k) ^ 2 := by rw [← pow_mul, ← pow_succ]
    rw [heq]
    exact Nat.pow_le_pow_left hlt.le 2

theorem floor_facts (x D : ℕ) (hD : 2 ≤ D) (hx : 2 ^ D ≤ x) :
    2 ≤ ⌊(x : ℝ) ^ ((D : ℝ)⁻¹)⌋₊ ∧ ⌊(x : ℝ) ^ ((D : ℝ)⁻¹)⌋₊ ^ D ≤ x := by
  have hD0 : D ≠ 0 := by omega
  have hxr : (2 : ℝ) ^ D ≤ (x : ℝ) := by exact_mod_cast hx
  have hr0 : (0 : ℝ) ≤ (x : ℝ) ^ ((D : ℝ)⁻¹) := Real.rpow_nonneg (Nat.cast_nonneg x) _
  constructor
  · apply Nat.le_floor
    have h2 : ((2 : ℝ) ^ D) ^ ((D : ℝ)⁻¹) = 2 := Real.pow_rpow_inv_natCast (by positivity) hD0
    have h3 : ((2 : ℝ) ^ D) ^ ((D : ℝ)⁻¹) ≤ (x : ℝ) ^ ((D : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) hxr (by positivity)
    rw [h2] at h3
    exact_mod_cast h3
  · have hle : ((⌊(x : ℝ) ^ ((D : ℝ)⁻¹)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) ^ ((D : ℝ)⁻¹) :=
      Nat.floor_le hr0
    have hpow : ((⌊(x : ℝ) ^ ((D : ℝ)⁻¹)⌋₊ : ℕ) : ℝ) ^ D ≤ (x : ℝ) := by
      calc ((⌊(x : ℝ) ^ ((D : ℝ)⁻¹)⌋₊ : ℕ) : ℝ) ^ D ≤ ((x : ℝ) ^ ((D : ℝ)⁻¹)) ^ D :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hle D
        _ = (x : ℝ) := Real.rpow_inv_natCast_pow (Nat.cast_nonneg x) hD0
    exact_mod_cast hpow

theorem prod_Ioc_choose (g y : ℕ) (hgy : g ≤ y) :
    (∏ b ∈ Ioc g y, (1 - (g : ℝ) / (b : ℝ))) * (y.choose g : ℝ) = 1 := by
  induction y, hgy using Nat.le_induction with
  | base => simp
  | succ y hgy ih =>
    have hyne : (y : ℝ) + 1 ≠ 0 := by positivity
    have hc : (y.choose g : ℝ) * ((y : ℝ) + 1) = ((y + 1).choose g : ℝ) * ((y : ℝ) + 1 - g) := by
      have h := Nat.choose_mul_succ_eq y g
      have h' : ((y.choose g * (y + 1) : ℕ) : ℝ) = (((y + 1).choose g * (y + 1 - g) : ℕ) : ℝ) := by
        rw [h]
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : g ≤ y + 1)] at h'
      push_cast at h'
      linear_combination h'
    rw [Finset.prod_Ioc_succ_top hgy]
    have key : (1 - (g : ℝ) / ((y + 1 : ℕ) : ℝ)) * ((y + 1).choose g : ℝ) = (y.choose g : ℝ) := by
      push_cast
      rw [one_sub_div hyne, div_mul_eq_mul_div, div_eq_iff hyne]
      linear_combination (-1 : ℝ) * hc
    calc (∏ b ∈ Ioc g y, (1 - (g : ℝ) / (b : ℝ))) * (1 - (g : ℝ) / ((y + 1 : ℕ) : ℝ))
          * ((y + 1).choose g : ℝ)
        = (∏ b ∈ Ioc g y, (1 - (g : ℝ) / (b : ℝ))) *
            ((1 - (g : ℝ) / ((y + 1 : ℕ) : ℝ)) * ((y + 1).choose g : ℝ)) := by ring
      _ = 1 := by rw [key]; exact ih

theorem V_ge (g y : ℕ) (hy : 1 ≤ y) (W : Finset ℕ) (hW : ∀ b ∈ W, g < b ∧ b ≤ y) :
    1 ≤ (y : ℝ) ^ g * ∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ)) := by
  by_cases hgy : g ≤ y
  · have hsub : W ⊆ Ioc g y := fun b hb => Finset.mem_Ioc.mpr (hW b hb)
    have hfac : ∀ b : ℕ, g < b → 0 ≤ 1 - (g : ℝ) / (b : ℝ) := by
      intro b hb
      have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
      have hgb : (g : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.le
      have : (g : ℝ) / (b : ℝ) ≤ 1 := (div_le_one hbpos).mpr hgb
      linarith
    have hprod : ∏ b ∈ Ioc g y, (1 - (g : ℝ) / (b : ℝ)) ≤ ∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ)) := by
      apply Finset.prod_le_prod_of_subset_of_le_one hsub
      · intro b hb
        exact hfac b (Finset.mem_Ioc.mp hb).1
      · intro b _ _
        have : (0 : ℝ) ≤ (g : ℝ) / (b : ℝ) := by positivity
        linarith
    have hPW0 : 0 ≤ ∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ)) :=
      Finset.prod_nonneg fun b hb => hfac b (hW b hb).1
    have hC := prod_Ioc_choose g y hgy
    have hCle : ((y.choose g : ℕ) : ℝ) ≤ (y : ℝ) ^ g := by
      exact_mod_cast Nat.choose_le_pow y g
    have hC0 : (0 : ℝ) ≤ (y.choose g : ℝ) := Nat.cast_nonneg _
    have h1 : (∏ b ∈ Ioc g y, (1 - (g : ℝ) / (b : ℝ))) * (y.choose g : ℝ) ≤
        (∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ))) * (y.choose g : ℝ) :=
      mul_le_mul_of_nonneg_right hprod hC0
    have h2 : (∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ))) * (y.choose g : ℝ) ≤
        (∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ))) * (y : ℝ) ^ g :=
      mul_le_mul_of_nonneg_left hCle hPW0
    rw [hC] at h1
    linarith
  · have hempty : ∏ b ∈ W, (1 - (g : ℝ) / (b : ℝ)) = 1 := by
      apply Finset.prod_eq_one
      intro b hb
      exfalso
      have := hW b hb
      omega
    rw [hempty, mul_one]
    exact one_le_pow₀ (by exact_mod_cast hy)

theorem final_num (x y g E : ℕ) (V T : ℝ) (hx : 16 ≤ x) (hyD : y ^ (2 * (E + g)) ≤ x)
    (hV : 1 ≤ (y : ℝ) ^ g * V) (hT : 1 / 2 * x * V - (y : ℝ) ^ E ≤ T) :
    1 / 4 * x * V ≤ T := by
  have hyg : (0 : ℝ) ≤ (y : ℝ) ^ g := by positivity
  have hyE : (0 : ℝ) ≤ (y : ℝ) ^ E := by positivity
  have hV0 : 0 < V := by
    by_contra h
    have h' : V ≤ 0 := not_lt.mp h
    nlinarith
  have hyE' : (y : ℝ) ^ E ≤ (y : ℝ) ^ (E + g) * V := by
    have h1 : (y : ℝ) ^ E ≤ (y : ℝ) ^ E * ((y : ℝ) ^ g * V) := le_mul_of_one_le_right hyE hV
    calc (y : ℝ) ^ E ≤ (y : ℝ) ^ E * ((y : ℝ) ^ g * V) := h1
      _ = (y : ℝ) ^ (E + g) * V := by ring
  have hyD' : (y : ℝ) ^ (2 * (E + g)) ≤ (x : ℝ) := by exact_mod_cast hyD
  have hYY : (y : ℝ) ^ (E + g) * (y : ℝ) ^ (E + g) ≤ (x : ℝ) := by
    calc (y : ℝ) ^ (E + g) * (y : ℝ) ^ (E + g) = (y : ℝ) ^ (2 * (E + g)) := by ring
      _ ≤ (x : ℝ) := hyD'
  have hY0 : (0 : ℝ) ≤ (y : ℝ) ^ (E + g) := by positivity
  have hx16 : (16 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h4 : 4 * (y : ℝ) ^ (E + g) ≤ (x : ℝ) := by
    rcases le_total ((y : ℝ) ^ (E + g)) 4 with h | h
    · linarith
    · nlinarith
  have h4V : 4 * ((y : ℝ) ^ (E + g) * V) ≤ (x : ℝ) * V := by
    have := mul_le_mul_of_nonneg_right h4 hV0.le
    linarith
  linarith

/- ## Block F: assembly -/

theorem eps_sum (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W) (n q0 a : ℕ)
    (h0 : 2 * (18 * (A.card : ℝ)) ≤ q0) (ha1 : q0 ≤ 2 * a + 1)
    (ha2 : Real.exp (((A.card : ℝ) + 2) * (18 * (A.card : ℝ))) * 2 ^ q0 ≤ 2 ^ (2 * a)) :
    ∑ j ∈ range n, dens A.card (blk W j) (cE (mm a n j)) /
        ∏ b ∈ blk W j, (1 - (A.card : ℝ) / (b : ℝ)) ≤ 1 / 2 := by
  refine le_trans (Finset.sum_le_sum fun j _ =>
    (block_eps A N M W hadm (blk W j) (blk_sub W j) (blk_sum A N M W hadm j) (mm a n j)).2) ?_
  exact ratio_sum (18 * (A.card : ℝ)) (A.card : ℝ) (by positivity) q0 a n h0 ha1 ha2

theorem main_part (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W) (n q0 a : ℕ)
    (hn : 1 ≤ n) (hWn : ∀ b ∈ W, b ≤ 2 ^ 2 ^ n)
    (h0 : 2 * (18 * (A.card : ℝ)) ≤ q0) (ha1 : q0 ≤ 2 * a + 1)
    (ha2 : Real.exp (((A.card : ℝ) + 2) * (18 * (A.card : ℝ))) * 2 ^ q0 ≤ 2 ^ (2 * a)) :
    1 / 2 * ∏ b ∈ W, (1 - (A.card : ℝ) / (b : ℝ)) ≤
      ∏ j ∈ range n, dens A.card (blk W j) (cU (mm a n j))
        - ∑ j ∈ range n, ∏ i ∈ range n,
            dens A.card (blk W i) (if i = j then cE (mm a n i) else cU (mm a n i)) := by
  have hn' : ∀ b ∈ W, 1 ≤ b ∧ b ≤ 2 ^ 2 ^ n := fun b hb =>
    ⟨by have := (hadm.2.2 b hb).1; omega, hWn b hb⟩
  have hcov := blk_cover W n hn hn'
  have hWeq : ∏ b ∈ W, (1 - (A.card : ℝ) / (b : ℝ)) =
      ∏ j ∈ range n, ∏ b ∈ blk W j, (1 - (A.card : ℝ) / (b : ℝ)) :=
    (prod_blk W n hcov _).symm
  have hV : ∀ j, 0 < ∏ b ∈ blk W j, (1 - (A.card : ℝ) / (b : ℝ)) := fun j =>
    (block_V A N M W hadm (blk W j) (blk_sub W j) (mm a n j) (mm_even a n j)).1
  have hsg : ∀ j, ∏ b ∈ blk W j, (1 - (A.card : ℝ) / (b : ℝ)) ≤
      dens A.card (blk W j) (cU (mm a n j)) := fun j =>
    (block_V A N M W hadm (blk W j) (blk_sub W j) (mm a n j) (mm_even a n j)).2
  have hε : ∀ j, 0 ≤ dens A.card (blk W j) (cE (mm a n j)) := fun j =>
    (block_eps A N M W hadm (blk W j) (blk_sub W j) (blk_sum A N M W hadm j) (mm a n j)).1
  have hmt := main_term n (fun j => dens A.card (blk W j) (cU (mm a n j)))
    (fun j => ∏ b ∈ blk W j, (1 - (A.card : ℝ) / (b : ℝ)))
    (fun j => dens A.card (blk W j) (cE (mm a n j))) hV hsg hε
    (eps_sum A N M W hadm n q0 a h0 ha1 ha2)
  have hkey : ∀ j, ∏ i ∈ range n, dens A.card (blk W i) (if i = j then cE (mm a n i) else cU (mm a n i))
      = ∏ i ∈ range n, (if i = j then dens A.card (blk W i) (cE (mm a n i))
          else dens A.card (blk W i) (cU (mm a n i))) := by
    intro j
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> rfl
  rw [hWeq, Finset.sum_congr rfl fun j _ => hkey j]
  exact hmt

theorem rem_part (A : Finset ℕ) (W : Finset ℕ) (y n a : ℕ) (hny : 2 ^ 2 ^ n ≤ y ^ 2) :
    ∏ j ∈ range n, mass A.card (blk W j) (cU (mm a n j))
        + ∑ j ∈ range n, ∏ i ∈ range n,
            mass A.card (blk W i) (if i = j then cE (mm a n i) else cU (mm a n i)) ≤
      (y : ℝ) ^ (4 * (A.card + 1) * (2 * a + 5)) := by
  have hg : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hkey : ∀ j, ∏ i ∈ range n, mass A.card (blk W i)
      (if i = j then cE (mm a n i) else cU (mm a n i)) =
      ∏ i ∈ range n, (if i = j then mass A.card (blk W i) (cE (mm a n i))
          else mass A.card (blk W i) (cU (mm a n i))) := by
    intro j
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> rfl
  simp only [hkey]
  have hP := prod_add_ge n (fun j => mass A.card (blk W j) (cU (mm a n j)))
    (fun j => mass A.card (blk W j) (cE (mm a n j)))
    (fun j => mass_nonneg _ hg _ _) (fun j => mass_nonneg _ hg _ _)
  refine le_trans hP ?_
  have h1 : ∏ j ∈ range n, (mass A.card (blk W j) (cU (mm a n j)) + mass A.card (blk W j) (cE (mm a n j)))
      ≤ ∏ j ∈ range n, (1 + (A.card : ℝ) * ((blk W j).card : ℝ)) ^ (mm a n j + 1) := by
    apply Finset.prod_le_prod
    · intro j _
      exact add_nonneg (mass_nonneg _ hg _ _) (mass_nonneg _ hg _ _)
    · intro j _
      exact mass_le _ hg _ _
  have h2 := rem_bound A.card a n (blk W) (fun j => blk_card W j)
  have h3 : ((2 : ℝ) ^ 2 ^ n) ^ (2 * (A.card + 1) * (2 * a + 5)) ≤
      (y : ℝ) ^ (4 * (A.card + 1) * (2 * a + 5)) := by
    have hny' : (2 : ℝ) ^ 2 ^ n ≤ (y : ℝ) ^ 2 := by exact_mod_cast hny
    calc ((2 : ℝ) ^ 2 ^ n) ^ (2 * (A.card + 1) * (2 * a + 5))
        ≤ ((y : ℝ) ^ 2) ^ (2 * (A.card + 1) * (2 * a + 5)) :=
          pow_le_pow_left₀ (by positivity) hny' _
      _ = (y : ℝ) ^ (4 * (A.card + 1) * (2 * a + 5)) := by
          rw [← pow_mul]
          congr 1
          ring
  exact le_trans h1 (le_trans h2 h3)

theorem core (A : Finset ℕ) (N M : ℕ) (W : Finset ℕ) (hadm : Adm A N M W) (y n q0 a : ℕ)
    (hWy : ∀ b ∈ W, b ≤ y) (hn : 1 ≤ n) (hyn : y ≤ 2 ^ 2 ^ n) (hny : 2 ^ 2 ^ n ≤ y ^ 2)
    (h0 : 2 * (18 * (A.card : ℝ)) ≤ q0) (ha1 : q0 ≤ 2 * a + 1)
    (ha2 : Real.exp (((A.card : ℝ) + 2) * (18 * (A.card : ℝ))) * 2 ^ q0 ≤ 2 ^ (2 * a))
    (x : ℕ) :
    1 / 2 * x * ∏ b ∈ W, (1 - (A.card : ℝ) / (b : ℝ))
        - (y : ℝ) ^ (4 * (A.card + 1) * (2 * a + 5)) ≤
      ((sift A M W x).card : ℝ) := by
  have hn' : ∀ b ∈ W, 1 ≤ b ∧ b ≤ 2 ^ 2 ^ n := fun b hb =>
    ⟨by have := (hadm.2.2 b hb).1; omega, le_trans (hWy b hb) hyn⟩
  have hcov := blk_cover W n hn hn'
  have hS := sieve_lower A N M W hadm (blk W) n (blk_sub W) (blk_disj W) hcov
    (fun j => mm a n j) (fun j => mm_even a n j) x
  have hMP := main_part A N M W hadm n q0 a hn (fun b hb => le_trans (hWy b hb) hyn) h0 ha1 ha2
  have hR := rem_part A W y n a hny
  have hx : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hxM := mul_le_mul_of_nonneg_left hMP hx
  linarith

end OMA.Brun

theorem OMA.solution : OMA.R_Erdos675_erdos_675_variants_brun_R1.H1 := by
  classical
  intro B A N M hB hA hM hcop
  obtain ⟨q0, a, h0, ha1, ha2⟩ := OMA.Brun.exists_params A.card
  have hD : 2 ≤ 2 * (4 * (A.card + 1) * (2 * a + 5) + A.card) := by
    have h1 : 0 < 4 * (A.card + 1) * (2 * a + 5) := Nat.mul_pos (by omega) (by omega)
    omega
  refine ⟨2 * (4 * (A.card + 1) * (2 * a + 5) + A.card), hD, 1 / 4, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop
    (max 16 (2 ^ (2 * (4 * (A.card + 1) * (2 * a + 5) + A.card))))] with x hx
  intro y T V
  have hx16 : 16 ≤ x := le_trans (le_max_left _ _) hx
  have hxD : 2 ^ (2 * (4 * (A.card + 1) * (2 * a + 5) + A.card)) ≤ x :=
    le_trans (le_max_right _ _) hx
  obtain ⟨hy2, hyD⟩ := OMA.Brun.floor_facts x _ hD hxD
  have hadm : OMA.Brun.Adm A N M ((Finset.Ioc N y).filter (fun b => b ∈ B)) := by
    refine ⟨hA, ?_, ?_⟩
    · intro b hb b' hb' hne
      exact hB (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb')).2 hne
    · intro b hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
      exact ⟨(Finset.mem_Ioc.mp hb1).1, hcop b hb2 (Finset.mem_Ioc.mp hb1).1⟩
  have hWy : ∀ b ∈ (Finset.Ioc N y).filter (fun b => b ∈ B), b ≤ y := fun b hb =>
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1).2
  obtain ⟨n, hn1, hyn, hny⟩ := OMA.Brun.exists_n y hy2
  have hcore := OMA.Brun.core A N M _ hadm y n q0 a hWy hn1 hyn hny h0 ha1 ha2 x
  have hV := OMA.Brun.V_ge A.card y (le_trans (by norm_num) hy2) _
    (fun b hb => ⟨OMA.Brun.adm_card_lt A N M _ hadm b hb, hWy b hb⟩)
  have hTeq : T = OMA.Brun.sift A M ((Finset.Ioc N y).filter (fun b => b ∈ B)) x := by
    ext k
    simp only [T, OMA.Brun.sift, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hk, h⟩
      exact ⟨hk, fun b hb => h b hb.2 hb.1.1 hb.1.2⟩
    · rintro ⟨hk, h⟩
      exact ⟨hk, fun b hbB hbN hby => h b ⟨⟨hbN, hby⟩, hbB⟩⟩
  rw [hTeq]
  exact OMA.Brun.final_num x y A.card _ V _ hx16 hyD hV hcore
