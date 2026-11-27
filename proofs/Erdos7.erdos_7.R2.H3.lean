import OMAReductions.R_Erdos7_erdos_7_R2
import Mathlib

-- Step Erdos7.erdos_7.R2.H3: hypothesis H3 of reduction Erdos7.erdos_7.R2
-- Credit: @ivillar. Base-p digit cascade: modulus p covers digit 0, moduli p^(j+1) cover digit 0 after
-- j leading ones, each class i gets p - 2 private divisor columns d (moduli p^(j+1) d, digits 2..p-1),
-- and one spare divisor column closes class i at depth i + 1. Residues come from the CRT.

/-! Covering residue classes modulo M by distinct odd moduli divisible by a prime. -/

open Finset

namespace P7E7H3

/-- The base-`p` repunit `1 + p + ... + p^(j-1)`. -/
def R (p j : ℕ) : ℤ := ∑ t ∈ range j, (p : ℤ) ^ t

lemma R_succ (p j : ℕ) : R p (j + 1) = R p j + (p : ℤ) ^ j := by
  simp [R, Finset.sum_range_succ]

/-- Walk along the base-`p` digits of `z`: either some digit among the first `L` differs from
`1` (the earlier ones being `1`), or the first `L` digits are all `1`. -/
lemma digit_walk (p : ℕ) (hp : 0 < p) (z : ℤ) (L : ℕ) :
    (∃ j < L, ∃ r : ℕ, r < p ∧ r ≠ 1 ∧ (p : ℤ) ^ (j + 1) ∣ z - (R p j + r * (p : ℤ) ^ j)) ∨
      (p : ℤ) ^ L ∣ z - R p L := by
  induction L with
  | zero => right; simp
  | succ L ih =>
    rcases ih with ⟨j, hj, r, hr, hr1, hd⟩ | ⟨w, hw⟩
    · exact Or.inl ⟨j, by omega, r, hr, hr1, hd⟩
    · have hp' : (0 : ℤ) < p := by exact_mod_cast hp
      have h0 : 0 ≤ w % (p : ℤ) := Int.emod_nonneg _ hp'.ne'
      have hlt : w % (p : ℤ) < p := Int.emod_lt_of_pos _ hp'
      have hdecomp : w % (p : ℤ) + p * (w / p) = w := Int.emod_add_mul_ediv w p
      obtain ⟨r, hrz⟩ : ∃ r : ℕ, (r : ℤ) = w % (p : ℤ) := ⟨_, Int.toNat_of_nonneg h0⟩
      have hrp : r < p := by omega
      by_cases h1 : r = 1
      · right
        refine ⟨w / p, ?_⟩
        have hm1 : w % (p : ℤ) = 1 := by rw [← hrz, h1]; rfl
        rw [R_succ]
        linear_combination hw - (p : ℤ) ^ L * hdecomp + (p : ℤ) ^ L * hm1
      · left
        refine ⟨L, by omega, r, hrp, h1, w / p, ?_⟩
        linear_combination hw - (p : ℤ) ^ L * hdecomp - (p : ℤ) ^ L * hrz

lemma crt (m d : ℕ) (A B : ℤ) :
    ∃ a : ℤ, m.Coprime d → (m : ℤ) ∣ a - A ∧ (d : ℤ) ∣ a - B := by
  by_cases hco : m.Coprime d
  · obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr hco
    refine ⟨A * y * d + B * x * m, fun _ => ⟨⟨x * (B - A), ?_⟩, ⟨y * (A - B), ?_⟩⟩⟩
    · linear_combination A * hxy
    · linear_combination B * hxy
  · exact ⟨0, fun h => absurd h hco⟩

lemma pow_mul_inj {p a b c c' : ℕ} (hp : 2 ≤ p) (hc : p.Coprime c) (hc' : p.Coprime c')
    (h : p ^ a * c = p ^ b * c') : a = b ∧ c = c' := by
  have key : ∀ a b c c', p.Coprime c → a < b → p ^ a * c = p ^ b * c' → False := by
    intro a b c c' hc hab h
    have h2 : p ^ b = p ^ a * p ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [h2, mul_assoc] at h
    have h3 := Nat.eq_of_mul_eq_mul_left (by positivity) h
    have hdvd : p ∣ c := h3 ▸ dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) c'
    have := Nat.Coprime.eq_one_of_dvd hc hdvd
    omega
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact (key a b c c' hc hab h).elim
  · exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩
  · exact (key b a c' c hc' hab h.symm).elim

theorem cover_lemma (M p h : ℕ) (u : Fin h → ℤ) (hp : p.Prime) (hp3 : 3 ≤ p) (hodd : Odd M)
    (hcop : p.Coprime M) (budget : (p - 2) * h < (M.divisors.erase 1).card) :
    ∃ S : Finset ℕ, ∃ a : ℕ → ℤ,
      (∀ d ∈ S, 1 < d ∧ Odd d ∧ p ∣ d ∧
        ∀ q : ℕ, q.Prime → q ≠ p → q.Coprime M → ¬ q ∣ d) ∧
      ∀ z : ℤ, (∃ i : Fin h, (M : ℤ) ∣ z - u i) → ∃ d ∈ S, (d : ℤ) ∣ z - a d := by
  classical
  have hM0 : M ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hodd)
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  -- columns: distinct divisors of `M` greater than `1`
  obtain ⟨T, hTD, hTc⟩ := Finset.exists_subset_card_eq (show (p - 2) * h + 1 ≤
    (M.divisors.erase 1).card by omega)
  let e := (T.equivFinOfCardEq hTc).symm
  let col : Fin ((p - 2) * h + 1) → ℕ := fun x => (e x).val
  have col_inj : Function.Injective col := fun x y hxy => e.injective (Subtype.ext hxy)
  have col_mem : ∀ x, col x ∈ M.divisors.erase 1 := fun x => hTD (e x).prop
  have col_dvd : ∀ x, col x ∣ M := fun x => (Nat.mem_divisors.mp (Finset.mem_erase.mp (col_mem x)).2).1
  have col_gt : ∀ x, 1 < col x := by
    intro x
    have h1 := (Finset.mem_erase.mp (col_mem x)).1
    have h0 : col x ≠ 0 := fun h0 => hM0 (Nat.eq_zero_of_zero_dvd (h0 ▸ col_dvd x))
    omega
  have col_cop : ∀ x, p.Coprime (col x) := fun x => Nat.Coprime.coprime_dvd_right (col_dvd x) hcop
  let pcol : Fin h → Fin (p - 2) → Fin ((p - 2) * h + 1) := fun i k =>
    ⟨i.val * (p - 2) + k.val, by
      have := i.isLt; have := k.isLt
      nlinarith⟩
  let spare : Fin ((p - 2) * h + 1) := ⟨(p - 2) * h, by omega⟩
  have pcol_inj : ∀ i k i' k', pcol i k = pcol i' k' → i = i' ∧ k = k' := by
    intro i k i' k' hk
    have hv : i.val * (p - 2) + k.val = i'.val * (p - 2) + k'.val := congrArg Fin.val hk
    have hk1 := k.isLt
    have hk2 := k'.isLt
    have hi : i.val = i'.val := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have : (i.val + 1) * (p - 2) ≤ i'.val * (p - 2) := Nat.mul_le_mul_right _ hlt
        nlinarith
      · have : (i'.val + 1) * (p - 2) ≤ i.val * (p - 2) := Nat.mul_le_mul_right _ hlt
        nlinarith
    refine ⟨Fin.ext hi, Fin.ext ?_⟩
    rw [hi] at hv
    omega
  have pcol_ne : ∀ i k, pcol i k ≠ spare := by
    intro i k hk
    have hv : i.val * (p - 2) + k.val = (p - 2) * h := congrArg Fin.val hk
    have hk1 := k.isLt
    have hi := i.isLt
    have : (i.val + 1) * (p - 2) ≤ h * (p - 2) := Nat.mul_le_mul_right _ hi
    nlinarith
  -- residues
  choose cr hcr using crt
  let mod : Fin h ⊕ (Fin h × Fin h × Fin (p - 2)) ⊕ Fin h → ℕ :=
    Sum.elim (fun j => p ^ (j.val + 1))
      (Sum.elim (fun t => p ^ (t.2.1.val + 1) * col (pcol t.1 t.2.2))
        (fun i => p ^ (i.val + 1) * col spare))
  let res : Fin h ⊕ (Fin h × Fin h × Fin (p - 2)) ⊕ Fin h → ℤ :=
    Sum.elim (fun j => R p j.val)
      (Sum.elim (fun t => cr (p ^ (t.2.1.val + 1)) (col (pcol t.1 t.2.2))
          (R p t.2.1.val + ((t.2.2.val + 2 : ℕ) : ℤ) * (p : ℤ) ^ t.2.1.val) (u t.1))
        (fun i => cr (p ^ (i.val + 1)) (col spare) (R p (i.val + 1)) (u i)))
  have hp2 : 2 ≤ p := by omega
  have cop1 : p.Coprime 1 := Nat.coprime_one_right p
  have mod_inj : Function.Injective mod := by
    intro x y hxy
    rcases x with j | ⟨i, j, k⟩ | i <;> rcases y with j' | ⟨i', j', k'⟩ | i' <;>
      simp only [mod, Sum.elim_inl, Sum.elim_inr] at hxy
    · have := pow_mul_inj hp2 cop1 cop1 (by simpa using hxy)
      rw [Fin.ext (by omega : j.val = j'.val)]
    · have := (pow_mul_inj hp2 cop1 (col_cop _) (by simpa using hxy)).2
      have := col_gt (pcol i' k'); omega
    · have := (pow_mul_inj hp2 cop1 (col_cop _) (by simpa using hxy)).2
      have := col_gt spare; omega
    · have := (pow_mul_inj hp2 (col_cop _) cop1 (by simpa using hxy)).2
      have := col_gt (pcol i k); omega
    · obtain ⟨h1, h2⟩ := pow_mul_inj hp2 (col_cop _) (col_cop _) hxy
      obtain ⟨rfl, rfl⟩ := pcol_inj i k i' k' (col_inj h2)
      rw [Fin.ext (by omega : j.val = j'.val)]
    · have := col_inj (pow_mul_inj hp2 (col_cop _) (col_cop _) hxy).2
      exact (pcol_ne i k this).elim
    · have := (pow_mul_inj hp2 (col_cop _) cop1 (by simpa using hxy)).2
      have := col_gt spare; omega
    · have := col_inj (pow_mul_inj hp2 (col_cop _) (col_cop _) hxy).2
      exact (pcol_ne i' k' this.symm).elim
    · have := (pow_mul_inj hp2 (col_cop _) (col_cop _) hxy).1
      rw [Fin.ext (by omega : i.val = i'.val)]
  let a : ℕ → ℤ := fun m => if hm : ∃ x, mod x = m then res hm.choose else 0
  have ha : ∀ x, a (mod x) = res x := by
    intro x
    have hm : ∃ y, mod y = mod x := ⟨x, rfl⟩
    simp only [a, dif_pos hm]
    rw [mod_inj hm.choose_spec]
  refine ⟨Finset.univ.image mod, a, ?_, ?_⟩
  · -- validity of the moduli
    intro d hd
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨j, c, hjc, hc1, hcM⟩ : ∃ j c : ℕ, mod x = p ^ (j + 1) * c ∧ 1 ≤ c ∧ c ∣ M := by
      rcases x with j | ⟨i, j, k⟩ | i
      · exact ⟨j.val, 1, by simp [mod], le_rfl, one_dvd M⟩
      · exact ⟨j.val, _, rfl, (col_gt _).le, col_dvd _⟩
      · exact ⟨i.val, _, rfl, (col_gt _).le, col_dvd _⟩
    rw [hjc]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : p ≤ p ^ (j + 1) := Nat.le_self_pow (by omega) p
      nlinarith
    · exact (hpodd.pow).mul (hodd.of_dvd_nat hcM)
    · exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) c
    · intro q hq hqp hqM hdvd
      rcases (Nat.Prime.dvd_mul hq).mp hdvd with h1 | h1
      · exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h1))
      · have := Nat.Coprime.eq_one_of_dvd hqM (dvd_trans h1 hcM)
        exact hq.one_lt.ne' this
  · -- covering
    rintro z ⟨i, hi⟩
    have hdvdM : ∀ c : ℕ, c ∣ M → (c : ℤ) ∣ z - u i :=
      fun c hc => dvd_trans (Int.natCast_dvd_natCast.mpr hc) hi
    have combine : ∀ (j c : ℕ) (A B res' : ℤ), p.Coprime c → (p : ℤ) ^ (j + 1) ∣ z - A →
        (c : ℤ) ∣ z - B → ((p ^ (j + 1) : ℕ) : ℤ) ∣ res' - A → (c : ℤ) ∣ res' - B →
        (((p ^ (j + 1) * c : ℕ)) : ℤ) ∣ z - res' := by
      intro j c A B res' hpc h1 h2 h3 h4
      have hco : IsCoprime ((p ^ (j + 1) : ℕ) : ℤ) (c : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left _ hpc)
      have e1 : ((p ^ (j + 1) : ℕ) : ℤ) ∣ z - res' := by
        have : z - res' = (z - A) - (res' - A) := by ring
        rw [this]
        push_cast at h3 ⊢
        exact dvd_sub h1 h3
      have e2 : (c : ℤ) ∣ z - res' := by
        have : z - res' = (z - B) - (res' - B) := by ring
        rw [this]
        exact dvd_sub h2 h4
      have := hco.mul_dvd e1 e2
      push_cast at this ⊢
      exact this
    rcases digit_walk p (by omega) z (i.val + 1) with ⟨j, hj, r, hr, hr1, hd⟩ | hd
    · have hjh : j < h := by have := i.isLt; omega
      rcases Nat.lt_or_ge r 2 with hr2 | hr2
      · have hr0 : r = 0 := by omega
        subst hr0
        refine ⟨mod (Sum.inl ⟨j, hjh⟩), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
        rw [ha]
        simp only [mod, res, Sum.elim_inl]
        push_cast
        simpa using hd
      · let x : Fin h ⊕ (Fin h × Fin h × Fin (p - 2)) ⊕ Fin h :=
          Sum.inr (Sum.inl (i, ⟨j, hjh⟩, ⟨r - 2, by omega⟩))
        refine ⟨mod x, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
        rw [ha]
        simp only [x, mod, res, Sum.elim_inr, Sum.elim_inl]
        have hr' : ((r - 2 + 2 : ℕ) : ℤ) = (r : ℤ) := by
          congr 1
          omega
        have hc := hcr (p ^ (j + 1)) (col (pcol i ⟨r - 2, by omega⟩))
          (R p j + ((r - 2 + 2 : ℕ) : ℤ) * (p : ℤ) ^ j) (u i)
          (Nat.Coprime.pow_left _ (col_cop _))
        apply combine j _ (R p j + ((r - 2 + 2 : ℕ) : ℤ) * (p : ℤ) ^ j) (u i) _ (col_cop _)
          (by rw [hr']; exact hd) (hdvdM _ (col_dvd _)) hc.1 hc.2
    · let x : Fin h ⊕ (Fin h × Fin h × Fin (p - 2)) ⊕ Fin h := Sum.inr (Sum.inr i)
      refine ⟨mod x, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
      rw [ha]
      simp only [x, mod, res, Sum.elim_inr]
      have hc := hcr (p ^ (i.val + 1)) (col spare) (R p (i.val + 1)) (u i)
        (Nat.Coprime.pow_left _ (col_cop _))
      exact combine i.val _ (R p (i.val + 1)) (u i) _ (col_cop _) hd
        (hdvdM _ (col_dvd _)) hc.1 hc.2

end P7E7H3

theorem OMA.solution : OMA.R_Erdos7_erdos_7_R2.H3 := by
  unfold OMA.R_Erdos7_erdos_7_R2.H3
  intro M p q h₂ v hp hq hp3 hq3 hpq hodd hcopP hcopQ budget
  obtain ⟨S, a, hS, hcov⟩ := P7E7H3.cover_lemma M q h₂ v hq hq3 hodd hcopQ budget
  refine ⟨S, a, fun d hd => ?_, hcov⟩
  obtain ⟨h1, h2, h3, -⟩ := hS d hd
  exact ⟨h1, h2, h3⟩
