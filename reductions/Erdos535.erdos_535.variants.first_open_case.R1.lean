import FormalConjectures.ErdosProblems.«535»

/-!
Erdős's 1964 prime-power reduction of the first open case `r = 3` of Problem 535.

- `H1`: the three-petal sunflower bound `C ^ k` for `k`-uniform families of finite sets of naturals.
- `H2`: inside one class of a partition of `{1, …, N}` by the exponents of the primes up to `t`,
  integers can be coded by `K`-element sets so that equal intersections of codes force equal gcds.

`main` combines them: each class has at most `C ^ K` elements, there are at most
`(log₂ N + 1) ^ (t + 1)` classes, and the choice `t = ⌊(log N) ^ (1/4)⌋`,
`K = ⌊4 log N / log log N⌋` gives `f 3 N ≤ N ^ ((4 + 4 log C) / log log N)`.
-/

namespace OMA.R_Erdos535_erdos_535_variants_first_open_case_R1

open Erdos535 Filter Real

def H1 : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧
    ∀ (k : ℕ) (F : Finset (Finset ℕ)),
      (∀ A ∈ F, A.card = k) → C ^ k < F.card →
      ∃ G ⊆ F, G.card = 3 ∧ ∃ K : Finset ℕ,
        ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K

def H2 : Prop :=
  ∀ t K N : ℕ,
    (∀ n ∈ Finset.Icc 1 N, ∑ p ∈ n.primeFactors.filter (t < ·), n.factorization p ≤ K) →
    ∃ (g : ℕ → Fin (t + 1) → Fin (Nat.log 2 N + 1)) (enc : ℕ → Finset ℕ),
      (∀ n ∈ Finset.Icc 1 N, (enc n).card = K) ∧
      ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N, ∀ c ∈ Finset.Icc 1 N, ∀ d ∈ Finset.Icc 1 N,
        g a = g b → g a = g c → g a = g d →
        enc a ∩ enc b = enc c ∩ enc d → Nat.gcd a b = Nat.gcd c d

/-- A class of integers coded by `K`-sets has at most `C ^ K` members when it has no
constant-gcd `r`-subset. -/
lemma classBound {r C K : ℕ}
    (hsun : ∀ (k : ℕ) (F : Finset (Finset ℕ)),
      (∀ A ∈ F, A.card = k) → C ^ k < F.card →
      ∃ G ⊆ F, G.card = r ∧ ∃ L : Finset ℕ,
        ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = L)
    (hr : 3 ≤ r) {B : Finset ℕ} (enc : ℕ → Finset ℕ)
    (hfree : ∀ S ⊆ B, S.card = r → ¬ ∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)
    (hcard : ∀ n ∈ B, (enc n).card = K)
    (hgcd : ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B,
      enc a ∩ enc b = enc c ∩ enc d → Nat.gcd a b = Nat.gcd c d) :
    B.card ≤ C ^ K := by
  classical
  have hinj : Set.InjOn enc (B : Set ℕ) := by
    intro a ha b hb heq
    have h1 := hgcd a ha b hb a ha a ha (by simp [heq])
    have h2 := hgcd a ha b hb b hb b hb (by simp [heq])
    rw [Nat.gcd_self] at h1 h2
    exact h1.symm.trans h2
  by_contra! hlarge
  let F := B.image enc
  have hFcard : F.card = B.card := Finset.card_image_of_injOn hinj
  obtain ⟨G, hGF, hGcard, core, hcore⟩ := hsun K F (by
    intro S hS
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hS
    exact hcard n hn) (hFcard ▸ hlarge)
  let S := B.filter fun n => enc n ∈ G
  have hSB : S ⊆ B := Finset.filter_subset _ _
  have hSimage : S.image enc = G := by
    ext T
    constructor
    · intro hT
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hT
      exact (Finset.mem_filter.mp hn).2
    · intro hT
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (hGF hT)
      exact Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr ⟨hn, hT⟩, rfl⟩
  have hScard : S.card = r := by
    rw [← hGcard, ← hSimage, Finset.card_image_of_injOn]
    exact hinj.mono (by exact_mod_cast hSB)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  have hInter {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : enc x ∩ enc y = core :=
    hcore _ (Finset.mem_filter.mp hx).2 _ (Finset.mem_filter.mp hy).2
      (fun h => hxy (hinj (hSB hx) (hSB hy) h))
  refine hfree S hSB hScard ⟨a.gcd b, ?_⟩
  intro x hx y hy hxy
  exact hgcd x (hSB hx) y (hSB hy) a (hSB ha) b (hSB hb)
    ((hInter hx hy hxy).trans (hInter ha hb hab).symm)

/-- Summing the class bound over all classes. -/
lemma countBound {r C : ℕ} (hr : 3 ≤ r)
    (hsun : ∀ (k : ℕ) (F : Finset (Finset ℕ)),
      (∀ A ∈ F, A.card = k) → C ^ k < F.card →
      ∃ G ⊆ F, G.card = r ∧ ∃ L : Finset ℕ,
        ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = L)
    (h₂ : H2) {N t K : ℕ}
    (hK : ∀ n ∈ Finset.Icc 1 N, ∑ p ∈ n.primeFactors.filter (t < ·), n.factorization p ≤ K) :
    f r N ≤ (Nat.log 2 N + 1) ^ (t + 1) * C ^ K := by
  classical
  obtain ⟨g, enc, hcard, hgcd⟩ := h₂ t K N hK
  apply csSup_le
  · refine ⟨0, ∅, Finset.empty_subset _, ?_, Finset.card_empty⟩
    intro S hS hS'
    have : S = ∅ := Finset.subset_empty.mp hS
    simp [this] at hS'
    omega
  rintro k ⟨A, hA, hfree, rfl⟩
  have hcount (v : Fin (t + 1) → Fin (Nat.log 2 N + 1)) :
      (A.filter (fun n => g n = v)).card ≤ C ^ K := by
    have hBA : A.filter (fun n => g n = v) ⊆ A := Finset.filter_subset _ _
    apply classBound hsun hr enc (fun S hS => hfree S (hS.trans hBA))
      (fun n hn => hcard n (hA (hBA hn)))
    intro a ha b hb c hc d hd
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hc' := (Finset.mem_filter.mp hc).2
    have hd' := (Finset.mem_filter.mp hd).2
    exact hgcd a (hA (hBA ha)) b (hA (hBA hb)) c (hA (hBA hc)) d (hA (hBA hd))
      (ha'.trans hb'.symm) (ha'.trans hc'.symm) (ha'.trans hd'.symm)
  calc
    A.card = ∑ v, (A.filter (fun n => g n = v)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _v : Fin (t + 1) → Fin (Nat.log 2 N + 1), C ^ K :=
      Finset.sum_le_sum (fun v _ => hcount v)
    _ = _ := by simp

lemma roughLogBound {t n : ℕ} {L : ℝ} (hL : ∀ p : ℕ, t < p → L ≤ log p) :
    ((∑ p ∈ n.primeFactors.filter (t < ·), n.factorization p : ℕ) : ℝ) * L ≤ log n := by
  rw [Nat.cast_sum, Finset.sum_mul, Real.log_nat_eq_sum_factorization,
    Finsupp.sum, Nat.support_factorization]
  calc
    _ ≤ ∑ p ∈ n.primeFactors.filter (t < ·), (n.factorization p : ℝ) * log p :=
      Finset.sum_le_sum fun p hp =>
        mul_le_mul_of_nonneg_left (hL p (Finset.mem_filter.mp hp).2) (by positivity)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => mul_nonneg (by positivity) (Real.log_natCast_nonneg p))

lemma castNatLogLe {N : ℕ} (hN : 0 < N) :
    (Nat.log 2 N : ℝ) ≤ log (N : ℝ) / log 2 := by
  have hp : ((2 : ℝ) ^ Nat.log 2 N) ≤ (N : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hN.ne'
  have h := Real.log_le_log (show 0 < (2 : ℝ) ^ Nat.log 2 N by positivity) hp
  rw [Real.log_pow] at h
  exact (le_div_iff₀ (Real.log_pos (by norm_num : 1 < (2 : ℝ)))).mpr h

theorem main : H1 → H2 → type_of% @Erdos535.erdos_535.variants.first_open_case := by
  intro h₁ h₂
  obtain ⟨C, hC, hsun⟩ := h₁
  have hr : 3 ≤ 3 := le_rfl
  have hCLog : 0 ≤ log (C : ℝ) := log_natCast_nonneg _
  refine ⟨4 + 4 * log (C : ℝ), by linarith, ?_⟩
  have logTwoPos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hxTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrootEvent : ∀ᶠ x : ℝ in atTop, log x ≤ x ^ (1 / 4 : ℝ) := by
    filter_upwards [(isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).bound
      (show 0 < (1 : ℝ) by norm_num), eventually_ge_atTop (0 : ℝ)] with x hb hx
    have hh : |log x| ≤ |x ^ (1 / 4 : ℝ)| := by
      simpa only [Real.norm_eq_abs, one_mul] using hb
    exact (le_abs_self (log x)).trans
      (by simpa only [abs_of_nonneg (Real.rpow_nonneg hx _)] using hh)
  filter_upwards [hxTop.eventually_ge_atTop (1 + 1 / log (2 : ℝ)),
    hxTop.eventually hrootEvent] with N hlarge hlog
  let x := log (N : ℝ)
  change 1 + 1 / log (2 : ℝ) ≤ x at hlarge
  change log x ≤ x ^ (1 / 4 : ℝ) at hlog
  have hx : 1 < x := (lt_add_of_pos_right 1 (one_div_pos.mpr logTwoPos)).trans_le hlarge
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hN : 0 < N := by
    by_contra! hz
    have : N = 0 := Nat.eq_zero_of_le_zero hz
    simp [x, this] at hx0
  have hlogx : 0 < log x := Real.log_pos hx
  let t := ⌊x ^ (1 / 4 : ℝ)⌋₊
  let K := ⌊4 * x / log x⌋₊
  have hpLog (p : ℕ) (hp : t < p) : log x / 4 ≤ log (p : ℝ) := by
    have hp' : (t : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hp
    have ht : x ^ (1 / 4 : ℝ) < (t : ℝ) + 1 := Nat.lt_floor_add_one _
    have hl := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) (ht.le.trans hp')
    rw [Real.log_rpow hx0] at hl
    linarith
  have hK : ∀ n ∈ Finset.Icc 1 N,
      ∑ p ∈ n.primeFactors.filter (t < ·), n.factorization p ≤ K := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    have h := (roughLogBound (t := t) (n := n) hpLog).trans (Real.log_le_log hnR hnN)
    apply Nat.le_floor
    apply (le_div_iff₀ hlogx).mpr
    linarith
  have htc : ((t : ℝ) + 1) ≤ 2 * x ^ (1 / 4 : ℝ) := by
    have ht : (t : ℝ) ≤ x ^ (1 / 4 : ℝ) := Nat.floor_le (by positivity)
    have hp : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx.le (by norm_num)
    linarith
  let M : ℝ := (Nat.log 2 N : ℝ) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMLogNonneg : 0 ≤ log M := by
    apply Real.log_nonneg
    dsimp [M]
    linarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 N)]
  have hMLog : log M ≤ 2 * log x := by
    have h0 : (Nat.log 2 N : ℝ) ≤ x / log (2 : ℝ) := castNatLogLe hN
    have h1 : x / log (2 : ℝ) + 1 ≤ x ^ 2 := by
      have hprod := mul_le_mul_of_nonneg_left (show 1 / log (2 : ℝ) + 1 ≤ x by linarith) hx0.le
      calc
        _ ≤ x / log (2 : ℝ) + x := add_le_add_right hx.le _
        _ = x * (1 / log (2 : ℝ) + 1) := by ring
        _ ≤ x * x := hprod
        _ = _ := by ring
    have h2 := Real.log_le_log hM (show M ≤ x ^ 2 by dsimp [M]; linarith)
    rw [Real.log_pow] at h2
    norm_num at h2 ⊢
    exact h2
  have hquarter : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0.le _
  have hthree : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) ≤ x := by
    calc
      _ = x ^ ((1 / 4 : ℝ) + 1 / 4 + 1 / 4) := by rw [Real.rpow_add hx0, Real.rpow_add hx0]
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
      _ = x := Real.rpow_one x
  have hsmall : ((t : ℝ) + 1) * log M ≤ 4 * x / log x := by
    apply (le_div_iff₀ hlogx).mpr
    calc
      _ ≤ (2 * x ^ (1 / 4 : ℝ)) * (2 * log x) * log x := by gcongr
      _ ≤ (2 * x ^ (1 / 4 : ℝ)) * (2 * x ^ (1 / 4 : ℝ)) * x ^ (1 / 4 : ℝ) := by gcongr
      _ ≤ _ := by linarith only [hthree]
  have hbig : (K : ℝ) * log (C : ℝ) ≤ (4 * x / log x) * log (C : ℝ) :=
    mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hCLog
  have htotal := countBound hr hsun h₂ hK
  have htotalR : (f 3 N : ℝ) ≤ M ^ (t + 1) * (C : ℝ) ^ K := by
    dsimp only [M]
    exact_mod_cast htotal
  refine htotalR.trans ?_
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast (show 0 < C by omega)
  apply (Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hNreal _)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_rpow hNreal]
  change (↑(t + 1) : ℝ) * log M + (K : ℝ) * log (C : ℝ) ≤
    ((4 + 4 * log (C : ℝ)) / log x) * x
  push_cast
  calc
    _ ≤ 4 * x / log x + (4 * x / log x) * log (C : ℝ) := add_le_add hsmall hbig
    _ = _ := by ring

end OMA.R_Erdos535_erdos_535_variants_first_open_case_R1
