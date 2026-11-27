import FormalConjectures.OEIS.«111291»
import Mathlib

/-!
# Colton's pointwise conjecture on refactorable numbers

Colton asks whether the count of refactorable numbers is always at least half
the prime count. This reduction verifies the statement through 4096 in the
kernel and proves that Zelinsky's disjoint prime-generator products, explicit
prime estimates, and finite generator data suffice for every subsequent index.
The grid comparisons and the two numerical generator bounds remain hypotheses.

The generator argument is due to Joshua Zelinsky (J. Integer Sequences 5,
Article 02.2.8). The finite family and the use of Dusart's explicit estimates
follow Leandre Jack, A proof of Colton’s conjecture on refactorable numbers,
doi:10.5281/zenodo.23874061. The grid, the seed cutoff, the kernel-checked seed
computation, and the connections to the pinned definitions were developed here.
The prime-interval counting step adapts @Genbox's merged proof of the related
asymptotic statement (PR 1176). Credit: @marcusbuffett.
-/

open Nat Finset OeisA111291

namespace OMA.R_OeisA111291_colton_conjecture_R1

/-- The first 317 integer comparisons, ending at 10,222,860. -/
def H1 : Prop := ∀ j < 317,
    let x := (fun m : ℕ => m + m / 40)^[j] 4096
    let G := ((Icc 1 (min 10000 (x/2))).filter (fun k : ℕ => 0 < k ∧ 2 * k.divisors.card ∣ k))
    (x + x/40).primeCounting ≤ 2 * (307 + (∑ k ∈ G, ((x/k).primeCounting - (max (k.primeFactors.sup id) (4096/k)).primeCounting)))

/-- The remaining 610 comparisons, ending at 35,573,728,066,487. -/
def H2 : Prop := ∀ j : ℕ, 317 ≤ j → j < 927 →
    let x := (fun m : ℕ => m + m / 40)^[j] 4096
    let G := ((Icc 1 (min 500000 (x/2))).filter (fun k : ℕ => 0 < k ∧ 2 * k.divisors.card ∣ k))
    (x + x/40).primeCounting ≤ 2 * (307 + (∑ k ∈ G, ((x/k).primeCounting - (max (k.primeFactors.sup id) (4096/k)).primeCounting)))

/-- Finite harmonic mass and excluded prime counts of Zelinsky’s generators. -/
def H3 : Prop :=
  let G := ((Icc 1 20000000).filter (fun k : ℕ => 0 < k ∧ 2 * k.divisors.card ∣ k))
  (251/500 : ℚ) ≤ ∑ k ∈ G, 1/(k:ℚ) ∧
    ∑ k ∈ G, (k.primeFactors.sup id).primeCounting ≤ 2000000000

/-- Dusart's explicit prime-counting estimates, theorem 6.9, equation (6.6). -/
def H4 : Prop :=
  (∀ x : ℝ, 5393 ≤ x → x / (Real.log x - 1) ≤ (⌊x⌋₊.primeCounting : ℝ)) ∧
  (∀ x : ℝ, 60184 ≤ x → (⌊x⌋₊.primeCounting : ℝ) ≤ x / (Real.log x - 11/10))


private theorem prime_le_top {p k : ℕ} (hp : p.Prime) (hd : p ∣ k) (hk : k ≠ 0) :
    p ≤ (k.primeFactors.sup id) :=
  Finset.le_sup (f := id) (hp.mem_primeFactors hd hk)

private theorem product_good {k p : ℕ} (hk : (0 < k ∧ 2 * k.divisors.card ∣ k)) (hp : p.Prime)
    (hlt : (k.primeFactors.sup id) < p) : (k * p).IsRefactorable := by
  have hnd : ¬p ∣ k := fun h => hlt.not_ge (prime_le_top hp h hk.1.ne')
  have hc : k.Coprime p := hp.coprime_iff_not_dvd.mpr hnd |>.symm
  refine ⟨Nat.mul_pos hk.1 hp.pos, ?_⟩
  rw [Nat.Coprime.card_divisors_mul hc, hp.divisors]
  simpa [hp.ne_one, Ne.symm hp.ne_one, Nat.mul_comm] using dvd_mul_of_dvd_left hk.2 p

private theorem maxPrime_inj {k p l q : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hp : p.Prime) (hq : q.Prime) (hkp : (k.primeFactors.sup id) < p) (hlq : (l.primeFactors.sup id) < q)
    (h : k * p = l * q) : k = l ∧ p = q := by
  have step {u v r s : ℕ} (hu : 0 < u) (hr : r.Prime) (hs : s.Prime)
      (hus : (u.primeFactors.sup id) < s) (heq : v * r = u * s) : r ≤ s := by
    have hd : r ∣ u * s := heq ▸ dvd_mul_left r v
    rcases hr.dvd_mul.mp hd with hdu | hds
    · exact (prime_le_top hr hdu hu.ne').trans hus.le
    · exact Nat.le_of_dvd hs.pos hds
  have he := le_antisymm (step hl hp hq hlq h) (step hk hq hp hkp h.symm)
  subst q
  exact ⟨Nat.eq_of_mul_eq_mul_right hp.pos h, rfl⟩

/-- Count all refactorables up to the seed cutoff, then count the larger products.
The prime exceeding every prime divisor of its generator uniquely identifies the pair. -/
theorem seed_add_generated {B n : ℕ} (hBn : B ≤ n) (G : Finset ℕ)
    (hG : ∀ k ∈ G, (0 < k ∧ 2 * k.divisors.card ∣ k)) :
    countRefactorableNat B + (∑ k ∈ G, ((n/k).primeCounting - (max (k.primeFactors.sup id) (B/k)).primeCounting)) ≤ countRefactorableNat n := by
  classical
  let seed := (Icc 1 B).filter IsRefactorable
  let choices (k : ℕ) := primesLE (n / k) \ primesLE ((max (k.primeFactors.sup id) (B/k)))
  have specs {k p : ℕ} (hp : p ∈ choices k) :
      p.Prime ∧ (max (k.primeFactors.sup id) (B/k)) < p ∧ p ≤ n / k := by
    obtain ⟨hp₁, hp₂⟩ := mem_sdiff.mp hp
    obtain ⟨hp₃, hp₄⟩ := mem_primesLE.mp hp₁
    exact ⟨hp₄, lt_of_not_ge (fun h => hp₂ (mem_primesLE.mpr ⟨h, hp₄⟩)), hp₃⟩
  have hs (k : ℕ) : (n / k).primeCounting - ((max (k.primeFactors.sup id) (B/k))).primeCounting ≤ (choices k).card := by
    rw [← primesLE_card_eq_primeCounting, ← primesLE_card_eq_primeCounting,
      show (choices k).card = _ from Finset.card_sdiff ..]
    exact Nat.sub_le_sub_left (Finset.card_le_card Finset.inter_subset_left) _
  let products := G.sigma choices
  have hpgt {k p : ℕ} (hk : 0 < k) (hp : (max (k.primeFactors.sup id) (B/k)) < p) : B < k * p := by
    have h := (Nat.div_lt_iff_lt_mul hk).mp ((le_max_right _ _).trans_lt hp)
    simpa [Nat.mul_comm] using h
  let f : ℕ ⊕ (Σ _k : ℕ, ℕ) → ℕ := Sum.elim id (fun t => t.1 * t.2)
  calc
    _ ≤ seed.card + products.card := by
      dsimp only [products]
      rw [Finset.card_sigma]
      exact Nat.add_le_add_left (Finset.sum_le_sum (fun k _ => hs k)) _
    _ = (seed.disjSum products).card := (Finset.card_disjSum _ _).symm
    _ ≤ _ := by
      unfold countRefactorableNat
      apply Finset.card_le_card_of_injOn f
      · rintro (a | ⟨k, p⟩) h
        · have ha := Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp h)
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp ha.1).1, (mem_Icc.mp ha.1).2.trans hBn⟩, ha.2⟩
        · obtain ⟨hk, hp⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp h)
          obtain ⟨hpp, hpl, hpu⟩ := specs hp
          have hgen := hG k hk
          have hgood := product_good hgen hpp ((le_max_left _ _).trans_lt hpl)
          refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hgood.1, ?_⟩, hgood⟩
          change k * p ≤ n
          simpa only [Nat.mul_comm p k] using (Nat.le_div_iff_mul_le hgen.1).mp hpu
      · rintro (a | ⟨k, p⟩) ha (b | ⟨l, q⟩) hb heq
        · exact congrArg Sum.inl heq
        · have ha' := (mem_Icc.mp (mem_filter.mp (Finset.inl_mem_disjSum.mp ha)).1).2
          obtain ⟨hl, hq⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp hb)
          have hgt : B < l * q := hpgt (hG l hl).1 (specs hq).2.1
          change a = l * q at heq
          omega
        · have hb' := (mem_Icc.mp (mem_filter.mp (Finset.inl_mem_disjSum.mp hb)).1).2
          obtain ⟨hk, hp⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp ha)
          have hgt : B < k * p := hpgt (hG k hk).1 (specs hp).2.1
          change k * p = b at heq
          omega
        · obtain ⟨hk, hp⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp ha)
          obtain ⟨hl, hq⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp hb)
          obtain ⟨rfl, rfl⟩ := maxPrime_inj (hG k hk).1 (hG l hl).1 (specs hp).1 (specs hq).1
            ((le_max_left _ _).trans_lt (specs hp).2.1) ((le_max_left _ _).trans_lt (specs hq).2.1) heq
          rfl





private theorem row_refactorable (fs : List ℕ) (hp : ∀ p ∈ fs, p.Prime)
    (ht : fs.toFinset.prod (fun p => fs.count p + 1) ∣ fs.prod) :
    fs.prod.IsRefactorable := by
  have hn := List.prod_pos (s := fs) (fun p h => (hp p h).pos)
  have hperm := Nat.primeFactorsList_unique (n := fs.prod) rfl hp
  have hset : fs.toFinset = fs.prod.primeFactors := by
    rw [← Nat.toFinset_factors]
    ext p
    simp only [List.mem_toFinset]
    exact hperm.mem_iff
  refine ⟨hn, ?_⟩
  rw [Nat.card_divisors hn.ne', ← hset]
  convert ht using 1
  congr 1
  funext p
  rw [← Nat.primeFactorsList_count_eq, hperm.count_eq p]

private theorem seed_count_succ (n : ℕ) : countRefactorableNat (n+1) =
    countRefactorableNat n + if (n+1).IsRefactorable then 1 else 0 := by
  have he : Icc 1 (n+1) = insert (n+1) (Icc 1 n) := by ext i; simp; omega
  have hnot : n+1 ∉ (Icc 1 n).filter IsRefactorable := by simp
  by_cases h : (n+1).IsRefactorable <;> simp [countRefactorableNat, he, h, hnot, Finset.filter_insert]

/-- Each entry gives a proper divisor of a composite, or zero for a possible prime.
A factor list with the specified product certifies a contribution to the lower count. -/
private theorem seed_block (b p r e q t : ℕ) (rows : List (ℕ × List ℕ))
    (hb : b.primeCounting ≤ p ∧ r ≤ countRefactorableNat b ∧
      ∀ n ≤ b, n.primeCounting ≤ 2 * countRefactorableNat n)
    (cert : rows.foldr (fun row next n u v =>
      let m := n+1
      let d := row.1
      let fs := row.2
      let u' := u + if d = 0 then 1 else 0
      let v' := v + if fs.prod = m then 1 else 0
      decide (m = 1 ∨ d = 0 ∨ (1 < d ∧ d < m ∧ d ∣ m)) &&
        (if fs.prod = m then fs.all (fun a => decide a.Prime) &&
          decide (fs.toFinset.prod (fun a => fs.count a + 1) ∣ m) else true) &&
        decide (u' ≤ 2*v') && next m u' v')
      (fun n u v => decide (n = e ∧ u = q ∧ v = t)) b p r = true) :
    e.primeCounting ≤ q ∧ t ≤ countRefactorableNat e ∧
      ∀ n ≤ e, n.primeCounting ≤ 2 * countRefactorableNat n := by
  induction rows generalizing b p r with
  | nil =>
    simp only [List.foldr_nil, decide_eq_true_eq] at cert
    obtain ⟨rfl,rfl,rfl⟩ := cert
    exact hb
  | cons row rows ih =>
    rcases row with ⟨d,fs⟩
    simp only [List.foldr_cons, Bool.and_eq_true, decide_eq_true_eq] at cert
    obtain ⟨⟨⟨hd,hfs⟩,hgap⟩,hnext⟩ := cert
    apply ih _ _ _ _ hnext
    have hπ : (b+1).primeCounting ≤ p + if d = 0 then 1 else 0 := by
      have he : (b+1).primeCounting = b.primeCounting + if (b+1).Prime then 1 else 0 :=
        Nat.count_succ _ _
      rw [he]
      apply Nat.add_le_add hb.1
      by_cases hpr : (b+1).Prime
      · have hz : d = 0 := by
          rcases hd with hone | hz | ⟨hd₂,hdm,hdvd⟩
          · have := hpr.two_le
            omega
          · exact hz
          · rcases hpr.eq_one_or_self_of_dvd d hdvd with he | he <;> omega
        simp [hpr,hz]
      · simp [hpr]
    have hT : r + (if fs.prod = b+1 then 1 else 0) ≤ countRefactorableNat (b+1) := by
      rw [seed_count_succ]
      apply Nat.add_le_add hb.2.1
      by_cases he : fs.prod = b+1
      · simp only [if_pos he, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hfs
        have hgood := row_refactorable fs hfs.1 (he ▸ hfs.2)
        simp [he, he ▸ hgood]
      · simp [he]
    refine ⟨hπ,hT,?_⟩
    intro n hn
    by_cases h : n ≤ b
    · exact hb.2.2 n h
    · have : n = b+1 := by omega
      subst n
      exact (hπ.trans hgap).trans (Nat.mul_le_mul_left _ hT)


private theorem seed_0 : (0 : ℕ).primeCounting ≤ 0 ∧ 0 ≤ countRefactorableNat 0 ∧
    ∀ n ≤ 0, n.primeCounting ≤ 2 * countRefactorableNat n := by
  simp [countRefactorableNat, Nat.primeCounting, Nat.primeCounting', Nat.count_one, Nat.not_prime_zero]

private theorem seed_32 : (32 : ℕ).primeCounting ≤ 11 ∧ 7 ≤ countRefactorableNat 32 ∧
    ∀ n ≤ 32, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 0 0 0 _ _ _ [
    (1,[]), (0,[2]), (0,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2]),
    (3,[3,3]), (2,[]), (0,[]), (2,[2,2,3]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[2,3,3]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[])] seed_0
  decide +kernel

private theorem seed_64 : (64 : ℕ).primeCounting ≤ 18 ∧ 11 ≤ countRefactorableNat 64 ∧
    ∀ n ≤ 64, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 32 11 7 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,5]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[2,2,2,7]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,5]), (0,[]), (2,[]), (3,[]), (2,[])] seed_32
  decide +kernel

private theorem seed_96 : (96 : ℕ).primeCounting ≤ 24 ∧ 16 ≤ countRefactorableNat 96 ∧
    ∀ n ≤ 96, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 64 18 11 _ _ _ [
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3]),
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[2,2,2,2,5]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,7]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,11]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,3])] seed_64
  decide +kernel

private theorem seed_128 : (128 : ℕ).primeCounting ≤ 31 ∧ 19 ≤ countRefactorableNat 128 ∧
    ∀ n ≤ 128, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 96 24 16 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,13]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,3]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (11,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,2])] seed_96
  decide +kernel

private theorem seed_160 : (160 : ℕ).primeCounting ≤ 37 ∧ 23 ≤ countRefactorableNat 160 ∧
    ∀ n ≤ 160, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 128 31 19 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,11]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,17]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,19]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,13]), (0,[]), (2,[]), (3,[]), (2,[])] seed_128
  decide +kernel

private theorem seed_192 : (192 : ℕ).primeCounting ≤ 43 ∧ 25 ≤ countRefactorableNat 192 ∧
    ∀ n ≤ 192, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 160 37 23 _ _ _ [
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,5]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,23]),
    (5,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[])] seed_160
  decide +kernel

private theorem seed_224 : (224 : ℕ).primeCounting ≤ 48 ∧ 26 ≤ countRefactorableNat 224 ∧
    ∀ n ≤ 224, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 192 43 25 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,17]), (5,[]), (2,[]), (3,[]), (2,[]),
    (11,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (0,[]), (2,[])] seed_192
  decide +kernel

private theorem seed_256 : (256 : ℕ).primeCounting ≤ 54 ∧ 32 ≤ countRefactorableNat 256 ∧
    ∀ n ≤ 256, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 224 48 26 _ _ _ [
    (3,[3,3,5,5]), (2,[]), (0,[]), (2,[2,2,3,19]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,29]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,3,5]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (13,[]), (2,[2,2,2,31]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,7]), (11,[]), (2,[]), (3,[]), (2,[])] seed_224
  decide +kernel

private theorem seed_288 : (288 : ℕ).primeCounting ≤ 61 ∧ 34 ≤ countRefactorableNat 288 ∧
    ∀ n ≤ 288, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 256 54 32 _ _ _ [
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,23]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[2,2,2,2,2,3,3])] seed_256
  decide +kernel

private theorem seed_320 : (320 : ℕ).primeCounting ≤ 66 ∧ 35 ≤ countRefactorableNat 320 ∧
    ∀ n ≤ 320, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 288 61 34 _ _ _ [
    (17,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[2,2,2,37]),
    (3,[]), (2,[]), (13,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[])] seed_288
  decide +kernel

private theorem seed_352 : (352 : ℕ).primeCounting ≤ 70 ∧ 38 ≤ countRefactorableNat 352 ∧
    ∀ n ≤ 352, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 320 66 35 _ _ _ [
    (3,[]), (2,[]), (17,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,41]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (7,[]), (2,[2,2,2,43]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,29]), (0,[]), (2,[]), (3,[]), (2,[])] seed_320
  decide +kernel

private theorem seed_384 : (384 : ℕ).primeCounting ≤ 76 ∧ 42 ≤ countRefactorableNat 384 ∧
    ∀ n ≤ 384, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 352 70 38 _ _ _ [
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,5]),
    (19,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,31]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,47]),
    (13,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,2,3])] seed_352
  decide +kernel

private theorem seed_416 : (416 : ℕ).primeCounting ≤ 80 ∧ 43 ≤ countRefactorableNat 416 ∧
    ∀ n ≤ 416, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 384 76 42 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (17,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,11]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (5,[]), (2,[])] seed_384
  decide +kernel

private theorem seed_448 : (448 : ℕ).primeCounting ≤ 86 ∧ 47 ≤ countRefactorableNat 448 ∧
    ∀ n ≤ 448, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 416 80 43 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,53]),
    (5,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]), (0,[]), (2,[]),
    (3,[3,3,7,7]), (2,[]), (0,[]), (2,[2,2,3,37]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,7])] seed_416
  decide +kernel

private theorem seed_480 : (480 : ℕ).primeCounting ≤ 92 ∧ 51 ≤ countRefactorableNat 480 ∧
    ∀ n ≤ 480, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 448 86 47 _ _ _ [
    (0,[]), (2,[2,3,3,5,5]), (11,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,13]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,59]),
    (11,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,5])] seed_448
  decide +kernel

private theorem seed_512 : (512 : ℕ).primeCounting ≤ 97 ∧ 54 ≤ countRefactorableNat 512 ∧
    ∀ n ≤ 512, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 480 92 51 _ _ _ [
    (13,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[2,2,2,61]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,41]), (17,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,7]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[])] seed_480
  decide +kernel

private theorem seed_544 : (544 : ℕ).primeCounting ≤ 100 ∧ 56 ≤ countRefactorableNat 544 ∧
    ∀ n ≤ 544, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 512 97 54 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,43]), (11,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]),
    (23,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (5,[]), (2,[2,2,2,67]),
    (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_512
  decide +kernel

private theorem seed_576 : (576 : ℕ).primeCounting ≤ 105 ∧ 59 ≤ countRefactorableNat 576 ∧
    ∀ n ≤ 576, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 544 100 56 _ _ _ [
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (13,[]), (2,[2,2,2,2,5,7]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,47]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,71]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[])] seed_544
  decide +kernel

private theorem seed_608 : (608 : ℕ).primeCounting ≤ 111 ∧ 61 ≤ countRefactorableNat 608 ∧
    ∀ n ≤ 608, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 576 105 59 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (11,[]), (2,[2,2,2,73]),
    (3,[]), (2,[]), (0,[]), (2,[]), (19,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,5,5]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[])] seed_576
  decide +kernel

private theorem seed_640 : (640 : ℕ).primeCounting ≤ 115 ∧ 66 ≤ countRefactorableNat 640 ∧
    ∀ n ≤ 640, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 608 111 61 _ _ _ [
    (3,[]), (2,[]), (13,[]), (2,[2,2,3,3,17]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (5,[5,5,5,5]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]), (0,[]), (2,[2,2,2,79]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,53]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,2,5])] seed_608
  decide +kernel

private theorem seed_672 : (672 : ℕ).primeCounting ≤ 121 ∧ 68 ≤ countRefactorableNat 672 ∧
    ∀ n ≤ 672, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 640 115 66 _ _ _ [
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,83]),
    (5,[]), (2,[]), (23,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[2,2,2,2,2,3,7])] seed_640
  decide +kernel

private theorem seed_704 : (704 : ℕ).primeCounting ≤ 126 ∧ 69 ≤ countRefactorableNat 704 ∧
    ∀ n ≤ 704, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 672 121 68 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,19]), (5,[]), (2,[]), (3,[]), (2,[]),
    (13,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (17,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (19,[]), (2,[])] seed_672
  decide +kernel

private theorem seed_736 : (736 : ℕ).primeCounting ≤ 130 ∧ 73 ≤ countRefactorableNat 736 ∧
    ∀ n ≤ 736, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 704 126 69 _ _ _ [
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,59]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,89]),
    (23,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,3,3,5]),
    (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (17,[]), (2,[2,2,3,61]), (0,[]), (2,[]), (3,[]), (2,[])] seed_704
  decide +kernel

private theorem seed_768 : (768 : ℕ).primeCounting ≤ 135 ∧ 73 ≤ countRefactorableNat 768 ∧
    ∀ n ≤ 768, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 736 130 73 _ _ _ [
    (11,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[])] seed_736
  decide +kernel

private theorem seed_800 : (800 : ℕ).primeCounting ≤ 139 ∧ 75 ≤ countRefactorableNat 800 ∧
    ∀ n ≤ 800, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 768 135 73 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[2,2,2,97]),
    (3,[]), (2,[]), (19,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[2,2,2,3,3,11]),
    (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (17,[]), (2,[])] seed_768
  decide +kernel

private theorem seed_832 : (832 : ℕ).primeCounting ≤ 145 ∧ 79 ≤ countRefactorableNat 832 ∧
    ∀ n ≤ 832, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 800 139 75 _ _ _ [
    (3,[]), (2,[]), (11,[]), (2,[2,2,3,67]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,101]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (19,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,103]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,23]), (0,[]), (2,[]), (3,[]), (2,[])] seed_800
  decide +kernel

private theorem seed_864 : (864 : ℕ).primeCounting ≤ 150 ∧ 82 ≤ countRefactorableNat 864 ∧
    ∀ n ≤ 864, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 832 145 79 _ _ _ [
    (7,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (29,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (23,[]), (2,[2,2,3,71]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,107]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,3,3])] seed_832
  decide +kernel

private theorem seed_896 : (896 : ℕ).primeCounting ≤ 154 ∧ 87 ≤ countRefactorableNat 896 ∧
    ∀ n ≤ 896, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 864 150 82 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (13,[]), (2,[2,2,2,109]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,73]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,2,5,11]),
    (0,[]), (2,[2,3,3,7,7]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,2,2,7])] seed_864
  decide +kernel

private theorem seed_928 : (928 : ℕ).primeCounting ≤ 157 ∧ 88 ≤ countRefactorableNat 928 ∧
    ∀ n ≤ 928, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 896 154 87 _ _ _ [
    (3,[]), (2,[]), (29,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[2,2,2,113]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (11,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (13,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[])] seed_896
  decide +kernel

private theorem seed_960 : (960 : ℕ).primeCounting ≤ 162 ∧ 90 ≤ countRefactorableNat 960 ∧
    ∀ n ≤ 960, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 928 157 88 _ _ _ [
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,3,3,13]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (23,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,79]), (13,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[])] seed_928
  decide +kernel

private theorem seed_992 : (992 : ℕ).primeCounting ≤ 167 ∧ 91 ≤ countRefactorableNat 992 ∧
    ∀ n ≤ 992, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 960 162 90 _ _ _ [
    (31,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,3,3,3]), (7,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (23,[]), (2,[]), (0,[]), (2,[])] seed_960
  decide +kernel

private theorem seed_1024 : (1024 : ℕ).primeCounting ≤ 172 ∧ 93 ≤ countRefactorableNat 1024 ∧
    ∀ n ≤ 1024, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 992 167 91 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,83]), (0,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[2,2,2,127]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_992
  decide +kernel

private theorem seed_1056 : (1056 : ℕ).primeCounting ≤ 177 ∧ 97 ≤ countRefactorableNat 1056 ∧
    ∀ n ≤ 1056, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1024 172 93 _ _ _ [
    (5,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]), (0,[]), (2,[2,2,2,2,5,13]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,3,29]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,131]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,3,11])] seed_1024
  decide +kernel

private theorem seed_1088 : (1088 : ℕ).primeCounting ≤ 181 ∧ 98 ≤ countRefactorableNat 1088 ∧
    ∀ n ≤ 1088, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1056 177 97 _ _ _ [
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (11,[]), (2,[2,2,3,89]), (0,[]), (2,[]), (3,[]), (2,[]),
    (29,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]),
    (23,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[])] seed_1056
  decide +kernel

private theorem seed_1120 : (1120 : ℕ).primeCounting ≤ 187 ∧ 102 ≤ countRefactorableNat 1120 ∧
    ∀ n ≤ 1120, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1088 181 98 _ _ _ [
    (3,[3,3,11,11]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,137]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[2,2,2,139]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,31]), (0,[]), (2,[]), (3,[]), (2,[])] seed_1088
  decide +kernel

private theorem seed_1152 : (1152 : ℕ).primeCounting ≤ 190 ∧ 103 ≤ countRefactorableNat 1152 ∧
    ∀ n ≤ 1152, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1120 187 102 _ _ _ [
    (19,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (17,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (31,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,2,3,3])] seed_1120
  decide +kernel

private theorem seed_1184 : (1184 : ℕ).primeCounting ≤ 194 ∧ 105 ≤ countRefactorableNat 1184 ∧
    ∀ n ≤ 1184, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1152 190 103 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (19,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,97]), (5,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,3,7,7]),
    (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[])] seed_1152
  decide +kernel

private theorem seed_1216 : (1216 : ℕ).primeCounting ≤ 198 ∧ 109 ≤ countRefactorableNat 1216 ∧
    ∀ n ≤ 1216, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1184 194 105 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[]), (29,[]), (2,[]), (3,[]), (2,[2,2,2,149]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[2,2,2,2,3,5,5]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (17,[]), (2,[2,2,2,151]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,101]), (0,[]), (2,[]), (3,[]), (2,[])] seed_1184
  decide +kernel

private theorem seed_1248 : (1248 : ℕ).primeCounting ≤ 203 ∧ 112 ≤ countRefactorableNat 1248 ∧
    ∀ n ≤ 1248, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1216 198 109 _ _ _ [
    (0,[]), (2,[]), (23,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,17]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,103]), (0,[]), (2,[]), (3,[]), (2,[]),
    (17,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (29,[]), (2,[2,2,2,2,2,3,13])] seed_1216
  decide +kernel

private theorem seed_1280 : (1280 : ℕ).primeCounting ≤ 207 ∧ 115 ≤ countRefactorableNat 1280 ∧
    ∀ n ≤ 1280, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1248 203 112 _ _ _ [
    (0,[]), (2,[2,5,5,5,5]), (3,[]), (2,[]), (7,[]), (2,[]), (5,[]), (2,[2,2,2,157]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,5,7]), (13,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]),
    (19,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[])] seed_1248
  decide +kernel

private theorem seed_1312 : (1312 : ℕ).primeCounting ≤ 214 ∧ 118 ≤ countRefactorableNat 1312 ∧
    ∀ n ≤ 1312, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1280 207 115 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,107]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,163]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,109]), (7,[]), (2,[]), (3,[]), (2,[])] seed_1280
  decide +kernel

private theorem seed_1344 : (1344 : ℕ).primeCounting ≤ 217 ∧ 121 ≤ countRefactorableNat 1344 ∧
    ∀ n ≤ 1344, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1312 214 118 _ _ _ [
    (13,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (11,[]), (2,[2,2,3,3,37]), (31,[]), (2,[]), (3,[]), (2,[2,2,2,167]),
    (7,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[2,2,2,2,2,2,3,7])] seed_1312
  decide +kernel

private theorem seed_1376 : (1376 : ℕ).primeCounting ≤ 220 ∧ 124 ≤ countRefactorableNat 1376 ∧
    ∀ n ≤ 1376, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1344 217 121 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,113]), (23,[]), (2,[]), (3,[]), (2,[2,2,2,2,5,17]),
    (0,[]), (2,[]), (29,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,19]),
    (37,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[])] seed_1344
  decide +kernel

private theorem seed_1408 : (1408 : ℕ).primeCounting ≤ 222 ∧ 126 ≤ countRefactorableNat 1408 ∧
    ∀ n ≤ 1408, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1376 220 124 _ _ _ [
    (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,173]),
    (5,[]), (2,[]), (19,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (23,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,2,11])] seed_1376
  decide +kernel

private theorem seed_1440 : (1440 : ℕ).primeCounting ≤ 228 ∧ 128 ≤ countRefactorableNat 1440 ∧
    ∀ n ≤ 1440, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1408 222 126 _ _ _ [
    (0,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (13,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,179]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,3,5])] seed_1408
  decide +kernel

private theorem seed_1472 : (1472 : ℕ).primeCounting ≤ 233 ∧ 129 ≤ countRefactorableNat 1472 ∧
    ∀ n ≤ 1472, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1440 228 128 _ _ _ [
    (11,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[2,2,2,181]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (31,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (0,[]), (2,[])] seed_1440
  decide +kernel

private theorem seed_1504 : (1504 : ℕ).primeCounting ≤ 239 ∧ 130 ≤ countRefactorableNat 1504 ∧
    ∀ n ≤ 1504, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1472 233 129 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,41]), (7,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (19,[]), (2,[]), (3,[]), (2,[])] seed_1472
  decide +kernel

private theorem seed_1536 : (1536 : ℕ).primeCounting ≤ 242 ∧ 134 ≤ countRefactorableNat 1536 ∧
    ∀ n ≤ 1536, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1504 239 130 _ _ _ [
    (5,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (17,[]), (2,[]), (3,[]), (2,[]), (37,[]), (2,[]), (7,[]), (2,[2,2,2,2,5,19]),
    (3,[3,3,13,13]), (2,[]), (0,[]), (2,[2,2,3,127]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,191]),
    (11,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[])] seed_1504
  decide +kernel

private theorem seed_1568 : (1568 : ℕ).primeCounting ≤ 247 ∧ 136 ≤ countRefactorableNat 1568 ∧
    ∀ n ≤ 1568, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1536 242 134 _ _ _ [
    (29,[]), (2,[]), (3,[]), (2,[]), (23,[]), (2,[]), (0,[]), (2,[2,2,2,193]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,3,43]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[])] seed_1536
  decide +kernel

private theorem seed_1600 : (1600 : ℕ).primeCounting ≤ 251 ∧ 139 ≤ countRefactorableNat 1600 ∧
    ∀ n ≤ 1600, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1568 247 136 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,131]), (11,[]), (2,[]), (3,[]), (2,[2,2,2,197]),
    (19,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (37,[]), (2,[2,2,2,199]),
    (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_1568
  decide +kernel

private theorem seed_1632 : (1632 : ℕ).primeCounting ≤ 258 ∧ 141 ≤ countRefactorableNat 1632 ∧
    ∀ n ≤ 1632, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1600 251 139 _ _ _ [
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,3,3,5]), (0,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[2,2,2,2,2,3,17])] seed_1600
  decide +kernel

private theorem seed_1664 : (1664 : ℕ).primeCounting ≤ 261 ∧ 144 ≤ countRefactorableNat 1664 ∧
    ∀ n ≤ 1664, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1632 258 141 _ _ _ [
    (23,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[]),
    (3,[]), (2,[]), (31,[]), (2,[2,2,3,137]), (5,[]), (2,[]), (3,[]), (2,[]),
    (17,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,3,3,23]),
    (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,2,13])] seed_1632
  decide +kernel

private theorem seed_1696 : (1696 : ℕ).primeCounting ≤ 264 ∧ 148 ≤ countRefactorableNat 1696 ∧
    ∀ n ≤ 1696, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1664 261 144 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,139]), (0,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (23,[]), (2,[2,2,2,2,3,5,7]),
    (41,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (7,[]), (2,[2,2,2,211]),
    (3,[]), (2,[]), (19,[]), (2,[2,2,3,3,47]), (0,[]), (2,[]), (3,[]), (2,[])] seed_1664
  decide +kernel

private theorem seed_1728 : (1728 : ℕ).primeCounting ≤ 269 ∧ 148 ≤ countRefactorableNat 1728 ∧
    ∀ n ≤ 1728, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1696 264 148 _ _ _ [
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (29,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[])] seed_1696
  decide +kernel

private theorem seed_1760 : (1760 : ℕ).primeCounting ≤ 274 ∧ 148 ≤ countRefactorableNat 1760 ∧
    ∀ n ≤ 1760, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1728 269 148 _ _ _ [
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (37,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[])] seed_1728
  decide +kernel

private theorem seed_1792 : (1792 : ℕ).primeCounting ≤ 278 ∧ 150 ≤ countRefactorableNat 1792 ∧
    ∀ n ≤ 1792, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1760 274 148 _ _ _ [
    (3,[]), (2,[]), (41,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]),
    (29,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (0,[]), (2,[2,2,2,223]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,149]), (0,[]), (2,[]), (3,[]), (2,[])] seed_1760
  decide +kernel

private theorem seed_1824 : (1824 : ℕ).primeCounting ≤ 281 ∧ 154 ≤ countRefactorableNat 1824 ∧
    ∀ n ≤ 1824, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1792 278 150 _ _ _ [
    (11,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[2,2,2,3,3,5,5]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (13,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,151]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,227]),
    (23,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,19])] seed_1792
  decide +kernel

private theorem seed_1856 : (1856 : ℕ).primeCounting ≤ 283 ∧ 156 ≤ countRefactorableNat 1856 ∧
    ∀ n ≤ 1856, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1824 281 154 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]), (0,[]), (2,[2,2,2,229]),
    (3,[]), (2,[]), (5,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[2,2,2,2,5,23]),
    (7,[]), (2,[]), (19,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (43,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]), (5,[]), (2,[])] seed_1824
  decide +kernel

private theorem seed_1888 : (1888 : ℕ).primeCounting ≤ 289 ∧ 158 ≤ countRefactorableNat 1888 ∧
    ∀ n ≤ 1888, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1856 283 156 _ _ _ [
    (3,[]), (2,[]), (11,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,233]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,157]), (5,[]), (2,[]), (3,[]), (2,[])] seed_1856
  decide +kernel

private theorem seed_1920 : (1920 : ℕ).primeCounting ≤ 293 ∧ 161 ≤ countRefactorableNat 1920 ∧
    ∀ n ≤ 1920, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1888 289 158 _ _ _ [
    (0,[]), (2,[]), (31,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,53]), (23,[]), (2,[]), (3,[]), (2,[2,2,2,239]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[2,2,2,2,2,2,2,3,5])] seed_1888
  decide +kernel

private theorem seed_1952 : (1952 : ℕ).primeCounting ≤ 297 ∧ 163 ≤ countRefactorableNat 1952 ∧
    ∀ n ≤ 1952, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1920 293 161 _ _ _ [
    (17,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (41,[]), (2,[2,2,2,241]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (13,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (29,[]), (2,[2,2,2,3,3,3,3,3]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[])] seed_1920
  decide +kernel

private theorem seed_1984 : (1984 : ℕ).primeCounting ≤ 299 ∧ 165 ≤ countRefactorableNat 1984 ∧
    ∀ n ≤ 1984, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1952 297 163 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,163]), (19,[]), (2,[]), (3,[]), (2,[]),
    (37,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,5,11]), (7,[]), (2,[]), (3,[]), (2,[])] seed_1952
  decide +kernel

private theorem seed_2016 : (2016 : ℕ).primeCounting ≤ 305 ∧ 169 ≤ countRefactorableNat 2016 ∧
    ∀ n ≤ 2016, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1984 299 165 _ _ _ [
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,2,5,5,5]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,167]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,251]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,3,3,7])] seed_1984
  decide +kernel

private theorem seed_2048 : (2048 : ℕ).primeCounting ≤ 309 ∧ 170 ≤ countRefactorableNat 2048 ∧
    ∀ n ≤ 2048, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2016 305 169 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (43,[]), (2,[]), (7,[]), (2,[]),
    (3,[3,3,3,3,5,5]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (19,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (13,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (23,[]), (2,[])] seed_2016
  decide +kernel

private theorem seed_2080 : (2080 : ℕ).primeCounting ≤ 312 ∧ 172 ≤ countRefactorableNat 2080 ∧
    ∀ n ≤ 2080, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2048 309 170 _ _ _ [
    (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,257]),
    (11,[]), (2,[]), (29,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (19,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,173]), (31,[]), (2,[]), (3,[]), (2,[])] seed_2048
  decide +kernel

private theorem seed_2112 : (2112 : ℕ).primeCounting ≤ 318 ∧ 174 ≤ countRefactorableNat 2112 ∧
    ∀ n ≤ 2112, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2080 312 172 _ _ _ [
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,29]),
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[2,2,2,263]),
    (5,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[])] seed_2080
  decide +kernel

private theorem seed_2144 : (2144 : ℕ).primeCounting ≤ 324 ∧ 175 ≤ countRefactorableNat 2144 ∧
    ∀ n ≤ 2144, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2112 318 174 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (29,[]), (2,[]), (13,[]), (2,[]),
    (3,[]), (2,[]), (11,[]), (2,[2,2,3,3,59]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[])] seed_2112
  decide +kernel

private theorem seed_2176 : (2176 : ℕ).primeCounting ≤ 326 ∧ 181 ≤ countRefactorableNat 2176 ∧
    ∀ n ≤ 2176, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2144 324 175 _ _ _ [
    (3,[]), (2,[]), (19,[]), (2,[2,2,3,179]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,269]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[2,2,2,2,3,3,3,5]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (11,[]), (2,[2,2,2,271]),
    (3,[]), (2,[]), (13,[]), (2,[2,2,3,181]), (41,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,2,17])] seed_2144
  decide +kernel

private theorem seed_2208 : (2208 : ℕ).primeCounting ≤ 329 ∧ 184 ≤ countRefactorableNat 2208 ∧
    ∀ n ≤ 2208, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2176 326 181 _ _ _ [
    (7,[]), (2,[2,3,3,11,11]), (0,[]), (2,[]), (3,[]), (2,[]), (37,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,61]), (13,[]), (2,[]), (3,[]), (2,[]),
    (31,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,23])] seed_2176
  decide +kernel

private theorem seed_2240 : (2240 : ℕ).primeCounting ≤ 333 ∧ 187 ≤ countRefactorableNat 2240 ∧
    ∀ n ≤ 2240, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2208 329 184 _ _ _ [
    (47,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[2,2,2,277]),
    (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[]), (23,[]), (2,[2,2,2,3,3,31]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,5,7])] seed_2208
  decide +kernel

private theorem seed_2272 : (2272 : ℕ).primeCounting ≤ 337 ∧ 189 ≤ countRefactorableNat 2272 ∧
    ∀ n ≤ 2272, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2240 333 187 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,281]),
    (13,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (37,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (31,[]), (2,[2,2,2,283]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_2240
  decide +kernel

private theorem seed_2304 : (2304 : ℕ).primeCounting ≤ 342 ∧ 190 ≤ countRefactorableNat 2304 ∧
    ∀ n ≤ 2304, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2272 337 189 _ _ _ [
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (43,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (29,[]), (2,[2,2,3,191]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[])] seed_2272
  decide +kernel

private theorem seed_2336 : (2336 : ℕ).primeCounting ≤ 345 ∧ 192 ≤ countRefactorableNat 2336 ∧
    ∀ n ≤ 2336, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2304 342 190 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,193]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,2,5,29]),
    (11,[]), (2,[]), (23,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]),
    (17,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[])] seed_2304
  decide +kernel

private theorem seed_2368 : (2368 : ℕ).primeCounting ≤ 350 ∧ 195 ≤ countRefactorableNat 2368 ∧
    ∀ n ≤ 2368, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2336 345 192 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,5,13]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,293]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (17,[]), (2,[2,2,3,197]), (5,[]), (2,[]), (3,[]), (2,[])] seed_2336
  decide +kernel

private theorem seed_2400 : (2400 : ℕ).primeCounting ≤ 357 ∧ 196 ≤ countRefactorableNat 2400 ∧
    ∀ n ≤ 2400, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2368 350 195 _ _ _ [
    (23,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,199]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[])] seed_2368
  decide +kernel

private theorem seed_2432 : (2432 : ℕ).primeCounting ≤ 360 ∧ 198 ≤ countRefactorableNat 2432 ∧
    ∀ n ≤ 2432, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2400 357 196 _ _ _ [
    (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (29,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,67]), (19,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (41,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (11,[]), (2,[2,2,2,2,2,2,2,19])] seed_2400
  decide +kernel

private theorem seed_2464 : (2464 : ℕ).primeCounting ≤ 364 ∧ 199 ≤ countRefactorableNat 2464 ∧
    ∀ n ≤ 2464, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2432 360 198 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (31,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (5,[]), (2,[2,2,2,307]),
    (3,[]), (2,[]), (0,[]), (2,[]), (23,[]), (2,[]), (3,[]), (2,[])] seed_2432
  decide +kernel

private theorem seed_2496 : (2496 : ℕ).primeCounting ≤ 367 ∧ 201 ≤ countRefactorableNat 2496 ∧
    ∀ n ≤ 2496, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2464 364 199 _ _ _ [
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (37,[]), (2,[2,2,2,2,5,31]),
    (3,[]), (2,[]), (13,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,311]),
    (19,[]), (2,[]), (47,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[])] seed_2464
  decide +kernel

private theorem seed_2528 : (2528 : ℕ).primeCounting ≤ 369 ∧ 202 ≤ countRefactorableNat 2528 ∧
    ∀ n ≤ 2528, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2496 367 201 _ _ _ [
    (11,[]), (2,[]), (3,[]), (2,[]), (41,[]), (2,[]), (0,[]), (2,[2,2,2,313]),
    (3,[]), (2,[]), (23,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (7,[]), (2,[])] seed_2496
  decide +kernel

private theorem seed_2560 : (2560 : ℕ).primeCounting ≤ 375 ∧ 206 ≤ countRefactorableNat 2560 ∧
    ∀ n ≤ 2560, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2528 369 202 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,211]), (17,[]), (2,[]), (3,[]), (2,[2,2,2,317]),
    (43,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,71]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,2,2,2,5])] seed_2528
  decide +kernel

private theorem seed_2592 : (2592 : ℕ).primeCounting ≤ 377 ∧ 206 ≤ countRefactorableNat 2592 ∧
    ∀ n ≤ 2592, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2560 375 206 _ _ _ [
    (13,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (29,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[])] seed_2560
  decide +kernel

private theorem seed_2624 : (2624 : ℕ).primeCounting ≤ 381 ∧ 207 ≤ countRefactorableNat 2624 ∧
    ∀ n ≤ 2624, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2592 377 206 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (23,[]), (2,[]),
    (3,[3,3,17,17]), (2,[]), (19,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (43,[]), (2,[])] seed_2592
  decide +kernel

private theorem seed_2656 : (2656 : ℕ).primeCounting ≤ 383 ∧ 210 ≤ countRefactorableNat 2656 ∧
    ∀ n ≤ 2656, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2624 381 207 _ _ _ [
    (3,[]), (2,[]), (37,[]), (2,[2,2,3,3,73]), (11,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[2,2,2,2,3,5,11]),
    (19,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[2,2,2,331]),
    (3,[]), (2,[]), (11,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[])] seed_2624
  decide +kernel

private theorem seed_2688 : (2688 : ℕ).primeCounting ≤ 390 ∧ 213 ≤ countRefactorableNat 2688 ∧
    ∀ n ≤ 2688, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2656 383 210 _ _ _ [
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,37]),
    (5,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,223]), (0,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,2,3,7])] seed_2656
  decide +kernel

private theorem seed_2720 : (2720 : ℕ).primeCounting ≤ 397 ∧ 215 ≤ countRefactorableNat 2720 ∧
    ∀ n ≤ 2720, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2688 390 213 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[2,2,2,337]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,3,5,5]), (37,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (0,[]), (2,[])] seed_2688
  decide +kernel

private theorem seed_2752 : (2752 : ℕ).primeCounting ≤ 401 ∧ 217 ≤ countRefactorableNat 2752 ∧
    ∀ n ≤ 2752, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2720 397 215 _ _ _ [
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,227]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (13,[]), (2,[]),
    (3,[]), (2,[]), (41,[]), (2,[2,2,3,229]), (0,[]), (2,[]), (3,[]), (2,[])] seed_2720
  decide +kernel

private theorem seed_2784 : (2784 : ℕ).primeCounting ≤ 404 ∧ 220 ≤ countRefactorableNat 2784 ∧
    ∀ n ≤ 2784, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2752 401 217 _ _ _ [
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]),
    (11,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (17,[]), (2,[2,2,3,3,7,11]), (47,[]), (2,[]), (3,[]), (2,[2,2,2,347]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[2,2,2,2,2,3,29])] seed_2752
  decide +kernel

private theorem seed_2816 : (2816 : ℕ).primeCounting ≤ 409 ∧ 222 ≤ countRefactorableNat 2816 ∧
    ∀ n ≤ 2816, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2784 404 220 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,349]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,233]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (53,[]), (2,[]), (3,[]), (2,[]), (29,[]), (2,[]), (5,[]), (2,[])] seed_2784
  decide +kernel

private theorem seed_2848 : (2848 : ℕ).primeCounting ≤ 413 ∧ 224 ≤ countRefactorableNat 2848 ∧
    ∀ n ≤ 2848, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2816 409 222 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,353]),
    (5,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (17,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,79]), (5,[]), (2,[]), (3,[]), (2,[])] seed_2816
  decide +kernel

private theorem seed_2880 : (2880 : ℕ).primeCounting ≤ 417 ∧ 226 ≤ countRefactorableNat 2880 ∧
    ∀ n ≤ 2880, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2848 413 224 _ _ _ [
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (47,[]), (2,[2,2,3,239]), (19,[]), (2,[]), (3,[]), (2,[2,2,2,359]),
    (13,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[])] seed_2848
  decide +kernel

private theorem seed_2912 : (2912 : ℕ).primeCounting ≤ 421 ∧ 228 ≤ countRefactorableNat 2912 ∧
    ∀ n ≤ 2912, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2880 417 226 _ _ _ [
    (43,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,241]), (11,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,11,11]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (41,[]), (2,[])] seed_2880
  decide +kernel

private theorem seed_2944 : (2944 : ℕ).primeCounting ≤ 424 ∧ 230 ≤ countRefactorableNat 2944 ∧
    ∀ n ≤ 2944, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2912 421 228 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (23,[]), (2,[]), (37,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (29,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (5,[]), (2,[2,2,2,367]),
    (3,[]), (2,[]), (0,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,2,23])] seed_2912
  decide +kernel

private theorem seed_2976 : (2976 : ℕ).primeCounting ≤ 429 ∧ 233 ≤ countRefactorableNat 2976 ∧
    ∀ n ≤ 2976, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2944 424 230 _ _ _ [
    (5,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[2,2,2,3,3,41]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[2,2,2,2,5,37]),
    (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,3,31])] seed_2944
  decide +kernel

private theorem seed_3008 : (3008 : ℕ).primeCounting ≤ 431 ∧ 235 ≤ countRefactorableNat 3008 ∧
    ∀ n ≤ 3008, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2976 429 233 _ _ _ [
    (13,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (19,[]), (2,[2,2,2,373]),
    (3,[]), (2,[]), (29,[]), (2,[2,2,3,3,83]), (7,[]), (2,[]), (3,[]), (2,[]),
    (41,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (31,[]), (2,[])] seed_2976
  decide +kernel

private theorem seed_3040 : (3040 : ℕ).primeCounting ≤ 435 ∧ 237 ≤ countRefactorableNat 3040 ∧
    ∀ n ≤ 3040, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3008 431 235 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,251]), (23,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (7,[]), (2,[2,2,2,379]),
    (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_3008
  decide +kernel

private theorem seed_3072 : (3072 : ℕ).primeCounting ≤ 439 ∧ 240 ≤ countRefactorableNat 3072 ∧
    ∀ n ≤ 3072, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3040 435 237 _ _ _ [
    (0,[]), (2,[2,3,3,13,13]), (17,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (43,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,3,5,17]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,383]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (37,[]), (2,[])] seed_3040
  decide +kernel

private theorem seed_3104 : (3104 : ℕ).primeCounting ≤ 442 ∧ 242 ≤ countRefactorableNat 3104 ∧
    ∀ n ≤ 3104, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3072 439 240 _ _ _ [
    (7,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,257]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,3,3,43]),
    (19,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (29,[]), (2,[])] seed_3072
  decide +kernel

private theorem seed_3136 : (3136 : ℕ).primeCounting ≤ 445 ∧ 244 ≤ countRefactorableNat 3136 ∧
    ∀ n ≤ 3136, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3104 442 242 _ _ _ [
    (3,[]), (2,[]), (13,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,389]),
    (11,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,3,5,13]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (53,[]), (2,[]),
    (3,[]), (2,[]), (31,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[])] seed_3104
  decide +kernel

private theorem seed_3168 : (3168 : ℕ).primeCounting ≤ 448 ∧ 246 ≤ countRefactorableNat 3168 ∧
    ∀ n ≤ 3168, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3136 445 244 _ _ _ [
    (0,[]), (2,[]), (43,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (47,[]), (2,[]), (23,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,263]), (7,[]), (2,[]), (3,[]), (2,[]),
    (29,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,3,11])] seed_3136
  decide +kernel

private theorem seed_3200 : (3200 : ℕ).primeCounting ≤ 452 ∧ 247 ≤ countRefactorableNat 3200 ∧
    ∀ n ≤ 3200, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3168 448 246 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]), (5,[]), (2,[2,2,2,397]),
    (3,[]), (2,[]), (11,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (31,[]), (2,[]), (3,[]), (2,[]), (23,[]), (2,[]), (7,[]), (2,[])] seed_3168
  decide +kernel

private theorem seed_3232 : (3232 : ℕ).primeCounting ≤ 457 ∧ 250 ≤ countRefactorableNat 3232 ∧
    ∀ n ≤ 3232, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3200 452 247 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,89]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,401]),
    (0,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,269]), (0,[]), (2,[]), (3,[]), (2,[])] seed_3200
  decide +kernel

private theorem seed_3264 : (3264 : ℕ).primeCounting ≤ 461 ∧ 253 ≤ countRefactorableNat 3264 ∧
    ∀ n ≤ 3264, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3232 457 250 _ _ _ [
    (53,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (41,[]), (2,[2,2,2,3,3,3,3,5]),
    (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (17,[]), (2,[]),
    (3,[3,3,19,19]), (2,[]), (0,[]), (2,[2,2,3,271]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[])] seed_3232
  decide +kernel

private theorem seed_3296 : (3296 : ℕ).primeCounting ≤ 462 ∧ 256 ≤ countRefactorableNat 3296 ∧
    ∀ n ≤ 3296, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3264 461 253 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[2,2,2,409]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,7,13]), (29,[]), (2,[]), (3,[]), (2,[2,2,2,2,5,41]),
    (17,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]),
    (11,[]), (2,[]), (3,[]), (2,[]), (37,[]), (2,[]), (5,[]), (2,[])] seed_3264
  decide +kernel

private theorem seed_3328 : (3328 : ℕ).primeCounting ≤ 468 ∧ 257 ≤ countRefactorableNat 3328 ∧
    ∀ n ≤ 3328, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3296 462 256 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,277]), (5,[]), (2,[]), (3,[]), (2,[])] seed_3296
  decide +kernel

private theorem seed_3360 : (3360 : ℕ).primeCounting ≤ 473 ∧ 259 ≤ countRefactorableNat 3360 ∧
    ∀ n ≤ 3360, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3328 468 257 _ _ _ [
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (47,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[2,2,2,419]),
    (7,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,5,7])] seed_3328
  decide +kernel

private theorem seed_3392 : (3392 : ℕ).primeCounting ≤ 478 ∧ 262 ≤ countRefactorableNat 3392 ∧
    ∀ n ≤ 3392, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3360 473 259 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (7,[]), (2,[2,2,2,421]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,281]), (0,[]), (2,[]), (3,[]), (2,[]),
    (11,[]), (2,[]), (31,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[2,2,2,3,3,47]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[])] seed_3360
  decide +kernel

private theorem seed_3424 : (3424 : ℕ).primeCounting ≤ 480 ∧ 264 ≤ countRefactorableNat 3424 ∧
    ∀ n ≤ 3424, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3392 478 262 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,283]), (43,[]), (2,[]), (3,[]), (2,[]),
    (19,[]), (2,[]), (41,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (13,[]), (2,[2,2,3,3,5,19]), (11,[]), (2,[]), (3,[]), (2,[])] seed_3392
  decide +kernel

private theorem seed_3456 : (3456 : ℕ).primeCounting ≤ 482 ∧ 267 ≤ countRefactorableNat 3456 ∧
    ∀ n ≤ 3456, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3424 480 264 _ _ _ [
    (5,[]), (2,[]), (23,[]), (2,[]), (3,[]), (2,[]), (47,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (19,[]), (2,[2,2,2,2,5,43]),
    (3,[]), (2,[]), (11,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,431]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,2,2,3,3,3])] seed_3424
  decide +kernel

private theorem seed_3488 : (3488 : ℕ).primeCounting ≤ 487 ∧ 268 ≤ countRefactorableNat 3488 ∧
    ∀ n ≤ 3488, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3456 482 267 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,433]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (23,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (59,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (11,[]), (2,[])] seed_3456
  decide +kernel

private theorem seed_3520 : (3520 : ℕ).primeCounting ≤ 491 ∧ 271 ≤ countRefactorableNat 3520 ∧
    ∀ n ≤ 3520, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3488 487 268 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,97]), (7,[]), (2,[]), (3,[]), (2,[]),
    (13,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (0,[]), (2,[2,2,2,439]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,293]), (0,[]), (2,[]), (3,[]), (2,[])] seed_3488
  decide +kernel

private theorem seed_3552 : (3552 : ℕ).primeCounting ≤ 497 ∧ 274 ≤ countRefactorableNat 3552 ∧
    ∀ n ≤ 3552, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3520 491 271 _ _ _ [
    (7,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,7,7]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,443]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (53,[]), (2,[2,2,2,2,2,3,37])] seed_3520
  decide +kernel

private theorem seed_3584 : (3584 : ℕ).primeCounting ≤ 502 ∧ 274 ≤ countRefactorableNat 3584 ∧
    ∀ n ≤ 3584, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3552 497 274 _ _ _ [
    (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]),
    (43,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[])] seed_3552
  decide +kernel

private theorem seed_3616 : (3616 : ℕ).primeCounting ≤ 505 ∧ 276 ≤ countRefactorableNat 3616 ∧
    ∀ n ≤ 3616, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3584 502 274 _ _ _ [
    (3,[]), (2,[]), (17,[]), (2,[]), (37,[]), (2,[]), (3,[]), (2,[2,2,2,449]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (59,[]), (2,[2,2,2,2,3,3,5,5]),
    (13,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (23,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_3584
  decide +kernel

private theorem seed_3648 : (3648 : ℕ).primeCounting ≤ 510 ∧ 277 ≤ countRefactorableNat 3648 ∧
    ∀ n ≤ 3648, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3616 505 276 _ _ _ [
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,101]), (0,[]), (2,[]), (3,[]), (2,[]),
    (11,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[])] seed_3616
  decide +kernel

private theorem seed_3680 : (3680 : ℕ).primeCounting ≤ 514 ∧ 278 ≤ countRefactorableNat 3680 ∧
    ∀ n ≤ 3680, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3648 510 277 _ _ _ [
    (41,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (5,[]), (2,[2,2,2,457]),
    (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (19,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (13,[]), (2,[])] seed_3648
  decide +kernel

private theorem seed_3712 : (3712 : ℕ).primeCounting ≤ 518 ∧ 283 ≤ countRefactorableNat 3712 ∧
    ∀ n ≤ 3712, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3680 514 278 _ _ _ [
    (3,[]), (2,[]), (29,[]), (2,[2,2,3,307]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,461]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[2,2,2,463]),
    (3,[]), (2,[]), (11,[]), (2,[2,2,3,3,103]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,2,29])] seed_3680
  decide +kernel

private theorem seed_3744 : (3744 : ℕ).primeCounting ≤ 522 ∧ 286 ≤ countRefactorableNat 3744 ∧
    ∀ n ≤ 3744, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3712 518 283 _ _ _ [
    (47,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (61,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,311]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,467]),
    (37,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[2,2,2,2,2,3,3,13])] seed_3712
  decide +kernel

private theorem seed_3776 : (3776 : ℕ).primeCounting ≤ 525 ∧ 288 ≤ countRefactorableNat 3776 ∧
    ∀ n ≤ 3776, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3744 522 286 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (23,[]), (2,[]), (11,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,313]), (13,[]), (2,[]), (3,[]), (2,[2,2,2,2,5,47]),
    (0,[]), (2,[]), (53,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (5,[]), (2,[])] seed_3744
  decide +kernel

private theorem seed_3808 : (3808 : ℕ).primeCounting ≤ 529 ∧ 289 ≤ countRefactorableNat 3808 ∧
    ∀ n ≤ 3808, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3776 525 288 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[]), (19,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (29,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,317]), (5,[]), (2,[]), (3,[]), (2,[])] seed_3776
  decide +kernel

private theorem seed_3840 : (3840 : ℕ).primeCounting ≤ 532 ∧ 291 ≤ countRefactorableNat 3840 ∧
    ∀ n ≤ 3840, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3808 529 289 _ _ _ [
    (13,[]), (2,[]), (37,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,3,3,53]),
    (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (43,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,479]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[])] seed_3808
  decide +kernel

private theorem seed_3872 : (3872 : ℕ).primeCounting ≤ 536 ∧ 292 ≤ countRefactorableNat 3872 ∧
    ∀ n ≤ 3872, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3840 532 291 _ _ _ [
    (23,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,107]), (0,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (53,[]), (2,[]), (7,[]), (2,[])] seed_3840
  decide +kernel

private theorem seed_3904 : (3904 : ℕ).primeCounting ≤ 539 ∧ 293 ≤ countRefactorableNat 3904 ∧
    ∀ n ≤ 3904, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3872 536 292 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]), (5,[]), (2,[2,2,2,487]),
    (3,[]), (2,[]), (7,[]), (2,[]), (47,[]), (2,[]), (3,[]), (2,[])] seed_3872
  decide +kernel

private theorem seed_3936 : (3936 : ℕ).primeCounting ≤ 546 ∧ 296 ≤ countRefactorableNat 3936 ∧
    ∀ n ≤ 3936, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3904 539 293 _ _ _ [
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,109]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,491]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,3,41])] seed_3904
  decide +kernel

private theorem seed_3968 : (3968 : ℕ).primeCounting ≤ 549 ∧ 297 ≤ countRefactorableNat 3968 ∧
    ∀ n ≤ 3968, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3936 546 296 _ _ _ [
    (31,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]),
    (59,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (37,[]), (2,[]),
    (17,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,2,31])] seed_3936
  decide +kernel

private theorem seed_4000 : (4000 : ℕ).primeCounting ≤ 550 ∧ 299 ≤ countRefactorableNat 4000 ∧
    ∀ n ≤ 4000, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3968 549 297 _ _ _ [
    (3,[]), (2,[]), (11,[]), (2,[2,2,3,331]), (29,[]), (2,[]), (3,[]), (2,[]),
    (41,[]), (2,[]), (23,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (13,[]), (2,[2,2,2,499]),
    (3,[]), (2,[]), (5,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[])] seed_3968
  decide +kernel

private theorem seed_4032 : (4032 : ℕ).primeCounting ≤ 557 ∧ 301 ≤ countRefactorableNat 4032 ∧
    ∀ n ≤ 4032, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 4000 550 299 _ _ _ [
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (19,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,503]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (29,[]), (2,[2,2,2,2,2,2,3,3,7])] seed_4000
  decide +kernel

private theorem seed_4064 : (4064 : ℕ).primeCounting ≤ 560 ∧ 304 ≤ countRefactorableNat 4064 ∧
    ∀ n ≤ 4064, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 4032 557 301 _ _ _ [
    (37,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (13,[]), (2,[2,2,3,337]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[2,3,3,3,3,5,5]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,3,13,13]),
    (0,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]), (17,[]), (2,[])] seed_4032
  decide +kernel

private theorem seed_4096 : (4096 : ℕ).primeCounting ≤ 564 ∧ 307 ≤ countRefactorableNat 4096 ∧
    ∀ n ≤ 4096, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 4064 560 304 _ _ _ [
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,3,113]), (13,[]), (2,[]), (3,[]), (2,[2,2,2,509]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,3,5,17]),
    (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (61,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_4064
  decide +kernel

private theorem initial_certificate : 307 ≤ countRefactorableNat 4096 ∧
    ∀ n ≤ 4096, n.primeCounting ≤ 2 * countRefactorableNat n := seed_4096.2



private theorem log_large {x : ℝ} (hx : 4 ≤ x) : (11/10 : ℝ) < Real.log x := by
  have h := Real.log_le_log (by norm_num : (0:ℝ) < 2 ^ 2) (show (2:ℝ)^2 ≤ x by linarith)
  rw [Real.log_pow] at h
  exact (show (11/10 : ℝ) < 2 * 0.6931471803 by norm_num).trans_le
    ((mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num : (0:ℝ) ≤ 2)).trans h)

private theorem pi_cutoff (hL : H4) :
    (1000000000000 : ℝ) ≤ ((2^45 : ℕ).primeCounting : ℝ) := by
  have h := hL.1 ((2^45 : ℕ) : ℝ) (by norm_num)
  rw [Nat.floor_natCast] at h
  have hlog : Real.log ((2^45 : ℕ) : ℝ) = 45 * Real.log 2 := by
    rw [show ((2^45 : ℕ) : ℝ) = (2 : ℝ)^45 by norm_num, Real.log_pow]
    norm_num
  have hp := log_large (x := ((2^45 : ℕ) : ℝ)) (by norm_num)
  apply le_trans _ h
  apply (le_div_iff₀ (sub_pos.mpr ((by norm_num : (1:ℝ) < 11/10).trans hp))).mpr
  rw [hlog]
  norm_num
  linarith [Real.log_two_lt_d9]

private theorem pi_scale (hL : H4) {n k : ℕ} (hn : (2^45 : ℕ) ≤ n)
    (hk2 : 2 ≤ k) (hkM : k ≤ 20000000) :
    (n.primeCounting : ℝ) / k ≤ ((n / k).primeCounting : ℝ) := by
  have hlarge : 35184372088832 ≤ (n : ℝ) := by exact_mod_cast hn
  have hk : 2 ≤ (k : ℝ) := by exact_mod_cast hk2
  have hmax : (k : ℝ) ≤ 20000000 := by exact_mod_cast hkM
  have hkpos : 0 < (k : ℝ) := by linarith
  have hx : 5393 ≤ (n : ℝ) / k := (le_div_iff₀ hkpos).mpr (by linarith)
  have hlo := hL.1 _ hx
  rw [Nat.floor_div_natCast, Nat.floor_natCast] at hlo
  have hup := hL.2 (n : ℝ) (by linarith)
  rw [Nat.floor_natCast] at hup
  have hd := log_large (x := (n : ℝ)/k) (by linarith)
  have hlogk := Real.log_le_log (by norm_num : (0:ℝ)<2) hk
  calc
    _ ≤ (n : ℝ) / (Real.log n - 11/10) / k := div_le_div_of_nonneg_right hup hkpos.le
    _ = ((n : ℝ)/k) / (Real.log n - 11/10) := div_right_comm ..
    _ ≤ ((n : ℝ)/k) / (Real.log ((n:ℝ)/k) - 1) := by
      apply div_le_div_of_nonneg_left (by positivity) (by linarith)
      rw [Real.log_div (by positivity) (by positivity)]
      linarith [Real.log_two_gt_d9]
    _ ≤ _ := hlo

private theorem tail (hG : H3) (hL : H4) (n : ℕ) (hn : (2^45 : ℕ) ≤ n) :
    n.primeCounting ≤ 2 * countRefactorableNat n := by
  let S := ((Icc 1 20000000).filter (fun k : ℕ => 0 < k ∧ 2 * k.divisors.card ∣ k))
  have hs (k : ℕ) (hk : k ∈ S) : (0 < k ∧ 2 * k.divisors.card ∣ k) := (mem_filter.mp hk).2
  have hscale (k : ℕ) (hk : k ∈ S) :
      (n.primeCounting : ℝ) * (1 / (k : ℝ)) ≤
      ((((n/k).primeCounting - ((k.primeFactors.sup id)).primeCounting : ℕ) : ℝ) + ((k.primeFactors.sup id)).primeCounting) := by
    have hd : 2 ∣ k := dvd_trans (dvd_mul_right 2 k.divisors.card) (hs k hk).2
    have hk2 := Nat.le_of_dvd (hs k hk).1 hd
    have hu := (mem_Icc.mp (mem_filter.mp hk).1).2
    calc
      _ = (n.primeCounting : ℝ) / k := by ring
      _ ≤ ((n/k).primeCounting : ℝ) := pi_scale hL hn hk2 hu
      _ ≤ _ := by
        exact_mod_cast (show (n/k).primeCounting ≤ ((n/k).primeCounting - ((k.primeFactors.sup id)).primeCounting) + ((k.primeFactors.sup id)).primeCounting by omega)
  have hsum := Finset.sum_le_sum hscale
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hrec : (251/500 : ℝ) ≤ ∑ k ∈ S, 1/(k:ℝ) := by
    have hv := (Rat.cast_le (K := ℝ)).mpr hG.1
    push_cast at hv
    exact hv
  have herror : (∑ k ∈ S, (((k.primeFactors.sup id)).primeCounting : ℝ)) ≤ 2000000000 := by
    exact_mod_cast hG.2
  have hgen := seed_add_generated (zero_le n) S hs
  have hnum : (∑ k ∈ S, ((((n/k).primeCounting - ((k.primeFactors.sup id)).primeCounting : ℕ) : ℝ))) ≤
      (countRefactorableNat n : ℝ) := by
    exact_mod_cast (show (∑ k ∈ S, ((n/k).primeCounting - ((k.primeFactors.sup id)).primeCounting)) ≤
        countRefactorableNat n by simpa [countRefactorableNat] using hgen)
  have hbig : (1000000000000 : ℝ) ≤ (n.primeCounting : ℝ) :=
    (pi_cutoff hL).trans (by exact_mod_cast Nat.monotone_primeCounting hn)
  have ht := (mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg n.primeCounting)).trans hsum
  exact_mod_cast (show (n.primeCounting : ℝ) ≤ 2 * countRefactorableNat n by linarith)



private theorem count_mono : Monotone countRefactorableNat := by
  intro m n h
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right h)

private theorem reaches (x : ℕ → ℕ) (hzero : x 0 = 4096)
    (hsucc : ∀ j, x (j+1) = x j + x j / 40) : 2^45 ≤ x 927 := by
  have hlo (j : ℕ) : 40 ≤ x j := by
    induction j with
    | zero => omega
    | succ j ih => rw [hsucc]; omega
  have hstep (j : ℕ) : 41 * (x j - 40) ≤ 40 * (x (j+1) - 40) := by
    rw [hsucc]
    have := hlo j
    omega
  have hg (j : ℕ) : 41^j * 4056 ≤ 40^j * (x j - 40) := by
    induction j with
    | zero => simp [hzero]
    | succ j ih =>
      calc
        41^(j+1) * 4056 = 41 * (41^j * 4056) := by ring
        _ ≤ 41 * (40^j * (x j - 40)) := Nat.mul_le_mul_left _ ih
        _ = 40^j * (41 * (x j - 40)) := by ring
        _ ≤ 40^j * (40 * (x (j+1) - 40)) := Nat.mul_le_mul_left _ (hstep j)
        _ = 40^(j+1) * (x (j+1) - 40) := by ring
  have cert : 40^927 * (2^45 - 40 : ℕ) ≤ 41^927 * 4056 := by decide +kernel
  have h : (2^45-40 : ℕ) ≤ x 927 - 40 :=
    Nat.le_of_mul_le_mul_left (cert.trans (hg 927)) (pow_pos (by decide) _)
  calc
    2^45 = (2^45-40)+40 := by decide
    _ ≤ (x 927-40)+40 := Nat.add_le_add_right h 40
    _ = x 927 := Nat.sub_add_cancel (hlo 927)

theorem main : H1 → H2 → H3 → H4 → type_of% @OeisA111291.colton_conjecture := by
  intro h₁ h₂ h₃ h₄ n
  by_cases hn : n ≤ 2^45
  · let f (m : ℕ) := m + m/40
    let x (j : ℕ) := f^[j] 4096
    have hx (j : ℕ) : x (j+1) = x j + x j/40 := Function.iterate_succ_apply' f j 4096
    have lower (j : ℕ) : 4096 ≤ x j := by
      induction j with
      | zero => exact le_rfl
      | succ j ih => rw [hx]; omega
    have upto (j : ℕ) (hj : j ≤ 927) : ∀ m ≤ x j, m.primeCounting ≤ 2 * countRefactorableNat m := by
      induction j with
      | zero => exact initial_certificate.2
      | succ j ih =>
        intro m hm
        by_cases hmj : m ≤ x j
        · exact ih (by omega) m hmj
        · let G := ((Icc 1 (min (if j < 317 then 10000 else 500000) (x j/2))).filter (fun k : ℕ => 0 < k ∧ 2 * k.divisors.card ∣ k))
          have hcount := seed_add_generated (lower j) G (fun _ hk => (mem_filter.mp hk).2)
          have hbudget := (Nat.add_le_add_right initial_certificate.1 _).trans hcount
          have hgrid : (x (j+1)).primeCounting ≤ 2 * (307 + (∑ k ∈ G, (((x j)/k).primeCounting - (max (k.primeFactors.sup id) (4096/k)).primeCounting))) := by
            rw [hx]
            by_cases hs : j < 317
            · simpa only [G, if_pos hs] using h₁ j hs
            · simpa only [G, if_neg hs] using h₂ j (by omega) (by omega)
          exact ((Nat.monotone_primeCounting hm).trans hgrid).trans
            (Nat.mul_le_mul_left 2 (hbudget.trans (count_mono (by omega))))
    exact upto 927 le_rfl n (hn.trans (reaches x rfl hx))
  · exact tail h₃ h₄ n (by omega)

end OMA.R_OeisA111291_colton_conjecture_R1
