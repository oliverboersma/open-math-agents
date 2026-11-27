import FormalConjectures.ErdosProblems.«785»

/-!
Imre Z. Ruzsa, *Exact additive complements* (arXiv:1510.00812).
The block counting argument for Ruzsa's upper bound is
adapted from OrangeHeadz's proof of Danzer's theorem in project PR 2119.
For the small excess, we construct complete residue systems at dyadic stages.
At intermediate stages a slightly smaller odd modulus suffices. The Chinese
remainder theorem lets the same sparse sequence satisfy both requirements.
-/

namespace Ruzsa785
open Finset
open scoped Pointwise

def dyad (k : ℕ) := 2 ^ Nat.log 2 k
def oddMod (k : ℕ) := 2 * ((k - k.sqrt - 1) / 2) + 1
def md (k : ℕ) := if k = 0 then 0 else max (dyad k) (oddMod k)

lemma dyad_pos (k : ℕ) : 0 < dyad k := by unfold dyad; positivity

lemma md_pos {k : ℕ} (hk : 2 ≤ k) : 0 < md k := by
  simp only [md, if_neg (by omega : k ≠ 0)]
  exact (dyad_pos k).trans_le (le_max_left ..)

lemma md_le (k : ℕ) : md k ≤ k := by
  by_cases hk : k = 0
  · simp [md,hk]
  simp only [md, if_neg hk, max_le_iff]
  refine ⟨Nat.pow_log_le_self 2 hk, ?_⟩
  unfold oddMod
  omega

lemma md_le_succ (k : ℕ) : md k ≤ md (k+1) := by
  cases k with
  | zero => simp [md]
  | succ k =>
    simp only [md, Nat.succ_ne_zero, if_false]
    apply max_le_max
    · exact Nat.pow_le_pow_right (by decide) (Nat.log_mono_right (by omega))
    · unfold oddMod
      have hs : (k+1+1).sqrt ≤ (k+1).sqrt + 1 := Nat.sqrt_succ_le_succ_sqrt (k+1)
      have hs0 := Nat.sqrt_le_self (k+1)
      change 2 * ((k+1-(k+1).sqrt-1)/2)+1 ≤ 2*((k+1+1-(k+1+1).sqrt-1)/2)+1
      omega

lemma md_lower (k : ℕ) : k ≤ md k + k.sqrt + 1 := by
  by_cases hk : k = 0
  · omega
  have h : oddMod k ≤ md k := by simp [md,hk]
  unfold oddMod at h
  omega

lemma md_pow (e : ℕ) : md (2^e) = 2^e := by
  apply le_antisymm (md_le _)
  simp [md, dyad, Nat.log_pow]

def oddProduct (i : ℕ) := ∏ d ∈ (range (i^2+1)).filter Odd, d

lemma product_odd (i : ℕ) : Odd (oddProduct i) := by
  unfold oddProduct
  apply Finset.prod_induction (p := Odd)
  · exact fun _ _ => Odd.mul
  · exact odd_one
  · intro d hd
    exact (mem_filter.mp hd).2

lemma odd_dvd {d i : ℕ} (ho : Odd d) (h : d ≤ i^2) : d ∣ oddProduct i :=
  Finset.dvd_prod_of_mem id (mem_filter.mpr ⟨mem_range.mpr (by omega), ho⟩)

/-- Choose the next sparse element above the growth threshold with both required residues. -/
def nextValue (i parent lower : ℕ) : ℕ :=
  let q := oddProduct i
  let e := Nat.log 2 (i-1) + 1
  let z := Nat.chineseRemainder ((product_odd i).coprime_two_right.pow_right e)
    i (parent + dyad (i-1))
  z.val + (q * 2^e) * (lower+1)

lemma next_spec (i parent lower : ℕ) :
    lower < nextValue i parent lower ∧
    nextValue i parent lower ≡ i [MOD oddProduct i] ∧
    nextValue i parent lower ≡ parent + dyad (i-1) [MOD 2^(Nat.log 2 (i-1)+1)] := by
  let q := oddProduct i
  let e := Nat.log 2 (i-1) + 1
  let z := Nat.chineseRemainder ((product_odd i).coprime_two_right.pow_right e)
    i (parent + dyad (i-1))
  change lower < z.val + (q*2^e)*(lower+1) ∧
    z.val + (q*2^e)*(lower+1) ≡ i [MOD q] ∧
    z.val + (q*2^e)*(lower+1) ≡ parent + dyad (i-1) [MOD 2^e]
  have hq : 0 < q := by obtain ⟨j,h⟩ := product_odd i; change 0 < oddProduct i; omega
  have h := Nat.le_mul_of_pos_left (lower+1) (show 0 < q*2^e by positivity)
  refine ⟨by omega, ?_, ?_⟩
  · exact (Nat.modEq_iff_dvd.mpr (by push_cast; exact ⟨-((2:ℤ)^e*(lower+1)),by ring⟩) :
      z.val + (q*2^e)*(lower+1) ≡ z.val [MOD q]).trans z.prop.1
  · exact (Nat.modEq_iff_dvd.mpr (by push_cast; exact ⟨-((q:ℤ)*(lower+1)),by ring⟩) :
      z.val + (q*2^e)*(lower+1) ≡ z.val [MOD 2^e]).trans z.prop.2

def thresh (t : ℕ → ℕ) (k a : ℕ) := max ((k+1)*a) (t (k*((k+1)*a))) + k
def seq (t : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => nextValue (k+1) (seq t (k+1-dyad k))
      (max ((k+1)^3 * seq t k) (thresh t k (seq t k)))
termination_by i => i
decreasing_by all_goals first | omega | have := dyad_pos k; omega

lemma seq_step (t : ℕ → ℕ) (k : ℕ) :
    max ((k+1)^3 * seq t k) (thresh t k (seq t k)) < seq t (k+1) ∧
    seq t (k+1) ≡ k+1 [MOD oddProduct (k+1)] ∧
    seq t (k+1) ≡ seq t (k+1-dyad k) + dyad k [MOD 2^(Nat.log 2 k+1)] := by
  have h := next_spec (k+1) (seq t (k+1-dyad k))
    (max ((k+1)^3*seq t k) (thresh t k (seq t k)))
  simpa only [Nat.add_sub_cancel, seq.eq_2] using h

/-- Each old residue acquires its other lift when the dyadic modulus doubles. -/
lemma sibling (t : ℕ → ℕ) (e j : ℕ) (h1 : 1 ≤ j) (hj : j ≤ 2^e) :
    seq t (j+2^e) ≡ seq t j + 2^e [MOD 2^(e+1)] := by
  let k := j+2^e-1
  have hk : k+1 = j+2^e := by dsimp [k]; omega
  have hp : 0 < (2:ℕ)^e := by positivity
  have hl : Nat.log 2 k = e := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · dsimp [k]; omega
    · rw [pow_succ]; dsimp [k]; omega
  have hs := (seq_step t k).2.2
  simpa only [hk, dyad, hl, Nat.add_sub_cancel] using hs

lemma pair_residues (a n b : ℕ) (hb : 0 < b) (h : a ≡ n [MOD b]) :
    a ≡ n [MOD 2*b] ∨ a+b ≡ n [MOD 2*b] := by
  change a % b = n % b at h
  change a % (2*b) = n % (2*b) ∨ (a+b) % (2*b) = n % (2*b)
  have ha := Nat.mod_add_div a b
  have hn := Nat.mod_add_div n b
  have decomp (x : ℕ) : x % (2*b) = x%b + b*((x/b)%2) := by
    rw [mul_comm 2 b, Nat.mod_mul]
  rw [decomp, decomp, decomp, Nat.add_mod_right, Nat.add_div_right _ hb, h]
  have first := Nat.mod_lt (a/b) (by decide : 0<2)
  have second := Nat.mod_lt (n/b) (by decide : 0<2)
  rcases eq_or_ne ((a/b)%2) ((n/b)%2) with eq|ne
  · exact Or.inl (by rw [eq])
  · exact Or.inr (by rw [show (a/b+1)%2 = (n/b)%2 by omega])

lemma dyad_cover (t : ℕ → ℕ) (e n : ℕ) :
    ∃ i, 1 ≤ i ∧ i ≤ 2^e ∧ seq t i ≡ n [MOD 2^e] := by
  induction e with
  | zero => exact ⟨1,by decide,by decide,Nat.modEq_one⟩
  | succ e ih =>
    obtain ⟨i,hi,hle,he⟩ := ih
    have hp : 0 < (2:ℕ)^e := by positivity
    have h2 : (2:ℕ)^(e+1) = 2*2^e := by rw [pow_succ, Nat.mul_comm]
    rcases pair_residues _ _ _ hp he with keep|flip
    · exact ⟨i,hi,by rw [h2]; omega,by rwa [h2]⟩
    · exact ⟨i+2^e,by omega,by rw [h2]; omega,(sibling t e i hi hle).trans (by rwa [h2])⟩

/-- The first `k` sparse elements cover all residue classes of the current block modulus. -/
lemma coverage (t : ℕ → ℕ) {k : ℕ} (hk : 4 ≤ k) (n : ℕ) :
    ∃ i, 1 ≤ i ∧ i ≤ k ∧ seq t i ≡ n [MOD md k] := by
  have hk0 : k ≠ 0 := by omega
  by_cases hd : oddMod k ≤ dyad k
  · have hm : md k = dyad k := by simp [md, hk0, max_eq_left hd]
    obtain ⟨i,hi,hle,he⟩ := dyad_cover t (Nat.log 2 k) n
    exact ⟨i,hi,hle.trans (Nat.pow_log_le_self 2 hk0), by rwa [hm]⟩
  have hm : md k = oddMod k := by simp [md, hk0, max_eq_right (le_of_not_ge hd)]
  let m := oddMod k
  have oddm : Odd m := ⟨_,rfl⟩
  have ms : 0 < m := by dsimp [m, oddMod]; omega
  have hs := Nat.sqrt_lt_self (by omega : 1 < k)
  have size : m ≤ k-k.sqrt := by dsimp [m, oddMod]; omega
  let start := k.sqrt + 1
  let i := start + (n + m - start % m) % m
  have hi : start ≤ i := Nat.le_add_right _ _
  have hr := Nat.mod_lt (n + m - start % m) ms
  have hki : i ≤ k := by
    have upper : i < start+m := Nat.add_lt_add_left hr start
    dsimp [start] at upper
    omega
  have hsq : m ≤ i^2 := by
    have h := Nat.lt_succ_sqrt' k
    exact (size.trans (Nat.sub_le ..)).trans (h.le.trans (Nat.pow_le_pow_left hi 2))
  have hi0 : 1 ≤ i := by dsimp [start] at hi; omega
  have hdiv := odd_dvd oddm hsq
  have hseq : seq t i ≡ i [MOD m] := by
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
    rw [hj] at hdiv ⊢
    exact ((seq_step t j).2.1).of_dvd hdiv
  have hass : start % m ≤ n + m := (Nat.mod_lt _ ms).le.trans (Nat.le_add_left _ _)
  have hmod : i ≡ n [MOD m] := calc
    i ≡ start % m + (n+m-start%m) [MOD m] :=
      (Nat.mod_modEq _ _).symm.add (Nat.mod_modEq _ _)
    _ = n+m := by omega
    _ ≡ n [MOD m] := Nat.add_modEq_right
  exact ⟨i,hi0,hki, by rw [hm]; exact hseq.trans hmod⟩

def X (t : ℕ → ℕ) (k : ℕ) : ℕ := k * (seq t) k

def Y (t : ℕ → ℕ) (k : ℕ) : ℕ := (k + 1) * (seq t) k

def Bset (t : ℕ → ℕ) : Set ℕ := {b | ∃ k, 4 ≤ k ∧ md k ∣ b ∧ (X t) k ≤ b ∧ b < (Y t) (k + 1)}

def Aset (t : ℕ → ℕ) : Set ℕ := Set.range fun i : ℕ => (seq t) (i + 1)


lemma av_lt_succ (t : ℕ → ℕ) (i : ℕ) : (seq t) i < (seq t) (i+1) := by
  have h := (seq_step t i).1
  have hi : 0 < (i+1)^3 := by positivity
  exact (Nat.le_mul_of_pos_left _ hi).trans_lt ((le_max_left ..).trans_lt h)

lemma av_strictMono (t : ℕ → ℕ) : StrictMono (seq t) := strictMono_nat_of_lt_succ (av_lt_succ t)
lemma le_av (t : ℕ → ℕ) (i : ℕ) : i ≤ (seq t) i := (av_strictMono t).id_le i
lemma av_pos (t : ℕ → ℕ) (i : ℕ) : 0 < (seq t) i := by
  have h := (av_strictMono t).monotone (show 0 ≤ i by omega)
  change seq t 0 ≤ seq t i at h
  rw [seq.eq_1] at h
  omega
lemma av_growth (t : ℕ → ℕ) (j : ℕ) (_hj : 1 ≤ j) : (j+1)^3 * (seq t) j ≤ (seq t) (j+1) :=
  (le_max_left ..).trans (seq_step t j).1.le
lemma Y_eq (t : ℕ → ℕ) (k : ℕ) : (Y t) k = (X t) k + (seq t) k := by unfold X Y; ring

lemma X_lt_succ (t : ℕ → ℕ) (k : ℕ) : (X t) k < (X t) (k + 1) := by
  unfold X
  have h1 := ((av_lt_succ t) k).le
  have h2 := (av_pos t) (k + 1)
  calc k * (seq t) k ≤ k * (seq t) (k + 1) := Nat.mul_le_mul_left _ h1
    _ < k * (seq t) (k + 1) + (seq t) (k + 1) := by omega
    _ = (k + 1) * (seq t) (k + 1) := by ring

lemma X_strictMono (t : ℕ → ℕ) : StrictMono (X t) := strictMono_nat_of_lt_succ (X_lt_succ t)

lemma Y_le_X_succ (t : ℕ → ℕ) (k : ℕ) : (Y t) k ≤ (X t) (k + 1) := by
  unfold X Y
  exact Nat.mul_le_mul_left _ ((av_lt_succ t) k).le

lemma Y_lt_succ (t : ℕ → ℕ) (k : ℕ) : (Y t) k < (Y t) (k + 1) := by
  have h1 := (Y_le_X_succ t) k
  have h2 := (Y_eq t) (k + 1)
  have h3 := (av_pos t) (k + 1)
  omega

lemma Y_strictMono (t : ℕ → ℕ) : StrictMono (Y t) := strictMono_nat_of_lt_succ (Y_lt_succ t)

lemma le_X (t : ℕ → ℕ) (k : ℕ) : k ≤ (X t) k := by
  unfold X
  exact Nat.le_mul_of_pos_right _ ((av_pos t) k)

lemma stage (f : ℕ → ℕ) (hf : StrictMono f) {K x : ℕ} (hx : f K ≤ x) :
    ∃ k, K ≤ k ∧ f k ≤ x ∧ x < f (k + 1) := by
  have hid : ∀ n, n ≤ f n := hf.id_le
  have hKx : K ≤ x := (hid K).trans hx
  refine ⟨Nat.findGreatest (fun j => f j ≤ x) x, Nat.le_findGreatest hKx hx,
    Nat.findGreatest_spec (P := fun j => f j ≤ x) hKx hx, ?_⟩
  by_contra hcon
  have h1 : f (Nat.findGreatest (fun j => f j ≤ x) x + 1) ≤ x := Nat.le_of_not_lt hcon
  have h2 : Nat.findGreatest (fun j => f j ≤ x) x + 1 ≤ x := (hid _).trans h1
  have h3 := Nat.le_findGreatest (P := fun j => f j ≤ x) h2 h1
  omega

/-- Counting multiples of `m` in `(L, U]`. -/
lemma card_mul (m L U : ℕ) (hLU : L ≤ U) :
    ((Finset.Ioc L U).filter (fun b => m ∣ b)).card + L / m = U / m := by
  have h1 := Nat.Ioc_filter_dvd_card_eq_div U m
  have h2 := Nat.Ioc_filter_dvd_card_eq_div L m
  have hunion : (Finset.Ioc 0 U).filter (fun b => m ∣ b) =
      (Finset.Ioc 0 L).filter (fun b => m ∣ b) ∪ (Finset.Ioc L U).filter (fun b => m ∣ b) := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le L) hLU]
  have hdisj : Disjoint ((Finset.Ioc 0 L).filter (fun b => m ∣ b))
      ((Finset.Ioc L U).filter (fun b => m ∣ b)) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [Finset.mem_filter, Finset.mem_Ioc] at hb1 hb2
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj, h2] at h1
  omega

/- The sum set. -/


lemma mem_add_of_large (t : ℕ → ℕ) {n : ℕ} (hn : (Y t) 4 ≤ n) : n ∈ (Aset t) + (Bset t) := by
  obtain ⟨k,hk,hy,hy'⟩ := stage (Y t) (Y_strictMono t) hn
  obtain ⟨i,hi,hik,he⟩ := coverage t hk n
  have hb := (Y_eq t) k
  have hai : (seq t) i ≤ (seq t) k := (av_strictMono t).monotone hik
  have han : (seq t) i ≤ n := by omega
  refine Set.mem_add.mpr ⟨(seq t) i,⟨i-1, by show (seq t) (i-1+1) = (seq t) i; rw [Nat.sub_add_cancel hi]⟩,
    n-(seq t) i, ⟨k,hk,(Nat.modEq_iff_dvd' han).mp he,by omega,by omega⟩,by omega⟩

lemma countA_bounds (t : ℕ → ℕ) {k x : ℕ} (hk : 1 ≤ k) (h1 : (X t) k ≤ x) (h2 : x < (X t) (k + 1)) :
    k ≤ ((Aset t) ∩ Set.Icc 1 x).ncard ∧ ((Aset t) ∩ Set.Icc 1 x).ncard ≤ k + 1 := by
  constructor
  · have hsub : (((Finset.Icc 1 k).image (seq t) : Finset ℕ) : Set ℕ) ⊆ (Aset t) ∩ Set.Icc 1 x := by
      intro b hb
      rw [Finset.mem_coe, Finset.mem_image] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      rw [Finset.mem_Icc] at hi
      refine ⟨⟨i - 1, ?_⟩, (av_pos t) i, ?_⟩
      · show (seq t) (i - 1 + 1) = (seq t) i
        rw [Nat.sub_add_cancel hi.1]
      · have h3 : (seq t) i ≤ (seq t) k := (av_strictMono t).monotone hi.2
        have h4 : (seq t) k ≤ (X t) k := by
          unfold X
          exact Nat.le_mul_of_pos_left _ (by omega)
        omega
    have hfin : ((Aset t) ∩ Set.Icc 1 x).Finite := (Set.finite_Icc 1 x).inter_of_right _
    have h := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ (av_strictMono t).injective,
      Nat.card_Icc] at h
    omega
  · have hsub : (Aset t) ∩ Set.Icc 1 x ⊆ (((Finset.Icc 1 (k + 1)).image (seq t) : Finset ℕ) : Set ℕ) := by
      rintro b ⟨⟨i, rfl⟩, -, hbx⟩
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨i + 1, ?_, rfl⟩
      rw [Finset.mem_Icc]
      refine ⟨by omega, ?_⟩
      by_contra hcon
      have h3 : (seq t) (k + 1 + 1) ≤ (seq t) (i + 1) := (av_strictMono t).monotone (by omega)
      have h4 := (av_growth t) (k + 1) (by omega)
      have h5 : (k + 1) * (seq t) (k + 1) < (k + 1 + 1) ^ 3 * (seq t) (k + 1) := by
        apply Nat.mul_lt_mul_of_pos_right _ ((av_pos t) _)
        calc k + 1 < k + 1 + 1 := by omega
          _ ≤ (k + 1 + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      have h6 : (X t) (k + 1) = (k + 1) * (seq t) (k + 1) := rfl
      simp only [] at hbx
      omega
    have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h
    have h' := Finset.card_image_le (s := Finset.Icc 1 (k + 1)) (f := (seq t))
    rw [Nat.card_Icc] at h'
    omega

/- Counting the dense set. -/

lemma countB_upper (t : ℕ → ℕ) {j x : ℕ} (hj : 4 ≤ j) (h1 : (X t) (j + 1) ≤ x) (h2 : x < (X t) (j + 2)) :
    md j * ((Bset t) ∩ Set.Icc 1 x).ncard ≤ md j * (Y t) j + x + (seq t) (j + 1) + md (j + 1) := by
  obtain ⟨F1, hF1⟩ : ∃ F : Finset ℕ, F = Finset.Ioc 0 ((Y t) j) := ⟨_, rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F : Finset ℕ, F = (Finset.Ioc 0 ((Y t) (j + 1))).filter (fun b => md j ∣ b) :=
    ⟨_, rfl⟩
  obtain ⟨F3, hF3⟩ : ∃ F : Finset ℕ,
      F = (Finset.Ioc ((X t) (j + 1) - 1) x).filter (fun b => md (j + 1) ∣ b) := ⟨_, rfl⟩
  have hXpos : 0 < (X t) (j + 1) := lt_of_lt_of_le (by omega) ((le_X t) (j + 1))
  have hsub : (Bset t) ∩ Set.Icc 1 x ⊆ ((F1 ∪ F2 ∪ F3 : Finset ℕ) : Set ℕ) := by
    rintro b ⟨⟨i, hi4, hdvd, hXi, hYi⟩, hb1, hbx⟩
    have hilt : i < j + 2 := (X_strictMono t).lt_iff_lt.1 (by omega)
    rw [Finset.mem_coe, Finset.mem_union, Finset.mem_union]
    rcases Nat.lt_or_ge i j with hij | hij
    · left; left
      rw [hF1, Finset.mem_Ioc]
      have h3 : (Y t) (i + 1) ≤ (Y t) j := (Y_strictMono t).monotone (by omega)
      exact ⟨hb1, by omega⟩
    · rcases Nat.eq_or_lt_of_le hij with rfl | hij'
      · left; right
        rw [hF2, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hb1, hYi.le⟩, hdvd⟩
      · have hi : i = j + 1 := by omega
        subst hi
        right
        rw [hF3, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨by omega, hbx⟩, hdvd⟩
  have hc := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hc
  have hc1 : (F1 ∪ F2 ∪ F3).card ≤ F1.card + F2.card + F3.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hcard1 : F1.card = (Y t) j := by rw [hF1, Nat.card_Ioc]; omega
  have hcard2 : F2.card = (Y t) (j + 1) / md j := by
    rw [hF2]; exact Nat.Ioc_filter_dvd_card_eq_div _ _
  have hcard3 : F3.card + ((X t) (j + 1) - 1) / md (j + 1) = x / md (j + 1) := by
    rw [hF3]; exact card_mul _ _ _ (by omega)
  have hm' : 0 < md j := md_pos (by omega)
  have hm : 0 < md (j + 1) := md_pos (by omega)
  have hmm : md j ≤ md (j + 1) := md_le_succ j
  obtain ⟨c, hcdef⟩ : ∃ c, c = ((Bset t) ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  rw [← hcdef] at hc ⊢
  obtain ⟨q1, hq1⟩ : ∃ q, q = (Y t) (j + 1) / md j := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q, q = x / md (j + 1) := ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ q, q = ((X t) (j + 1) - 1) / md (j + 1) := ⟨_, rfl⟩
  rw [← hq1] at hcard2
  rw [← hq2, ← hq3] at hcard3
  have b1 : md j * q1 ≤ (Y t) (j + 1) := by rw [hq1]; exact Nat.mul_div_le _ _
  have b2 : md (j + 1) * q2 ≤ x := by rw [hq2]; exact Nat.mul_div_le _ _
  have b3 : (X t) (j + 1) - 1 < md (j + 1) * q3 + md (j + 1) := by
    have := Nat.lt_mul_div_succ ((X t) (j + 1) - 1) hm
    rw [← hq3] at this
    calc (X t) (j + 1) - 1 < md (j + 1) * (q3 + 1) := this
      _ = md (j + 1) * q3 + md (j + 1) := by ring
  have e1 : md (j + 1) * F3.card + md (j + 1) * q3 = md (j + 1) * q2 := by
    rw [← Nat.mul_add, hcard3]
  have e2 : md j * F3.card ≤ md (j + 1) * F3.card := Nat.mul_le_mul_right _ hmm
  have e3 : md j * c ≤ md j * (Y t) j + md j * q1 + md j * F3.card := by
    calc md j * c ≤ md j * ((Y t) j + q1 + F3.card) := Nat.mul_le_mul_left _ (by omega)
      _ = md j * (Y t) j + md j * q1 + md j * F3.card := by ring
  have hYeq := (Y_eq t) (j + 1)
  omega

lemma countB_lower (t : ℕ → ℕ) {j x : ℕ} (hj : 4 ≤ j) (h1 : (X t) (j + 1) ≤ x) (h2 : x < (X t) (j + 2)) :
    x ≤ md (j + 1) * ((Bset t) ∩ Set.Icc 1 x).ncard + (X t) j + 2 * md (j + 1) := by
  obtain ⟨G1, hG1⟩ : ∃ F : Finset ℕ,
      F = (Finset.Ioc ((X t) j - 1) ((X t) (j + 1) - 1)).filter (fun b => md j ∣ b) := ⟨_, rfl⟩
  obtain ⟨F3, hF3⟩ : ∃ F : Finset ℕ,
      F = (Finset.Ioc ((X t) (j + 1) - 1) x).filter (fun b => md (j + 1) ∣ b) := ⟨_, rfl⟩
  have hXj : j ≤ (X t) j := (le_X t) j
  have hXlt : (X t) j < (X t) (j + 1) := (X_lt_succ t) j
  have hYeq1 := (Y_eq t) (j + 1)
  have hYeq2 := (Y_eq t) (j + 2)
  have hsub : ((G1 ∪ F3 : Finset ℕ) : Set ℕ) ⊆ (Bset t) ∩ Set.Icc 1 x := by
    intro b hb
    rw [Finset.mem_coe, Finset.mem_union] at hb
    rcases hb with hb | hb
    · rw [hG1, Finset.mem_filter, Finset.mem_Ioc] at hb
      exact ⟨⟨j, hj, hb.2, by omega, by omega⟩, by omega, by omega⟩
    · rw [hF3, Finset.mem_filter, Finset.mem_Ioc] at hb
      exact ⟨⟨j + 1, by omega, hb.2, by omega, (show b < (Y t) (j + 2) by omega)⟩, by omega, hb.1.2⟩
  have hdisj : Disjoint G1 F3 := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [hG1, Finset.mem_filter, Finset.mem_Ioc] at hb1
    rw [hF3, Finset.mem_filter, Finset.mem_Ioc] at hb2
    omega
  have hfin : ((Bset t) ∩ Set.Icc 1 x).Finite := (Set.finite_Icc 1 x).inter_of_right _
  have hc := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj] at hc
  have hm' : 0 < md j := md_pos (by omega)
  have hm : 0 < md (j + 1) := md_pos (by omega)
  have hmm : md j ≤ md (j + 1) := md_le_succ j
  obtain ⟨c, hcdef⟩ : ∃ c, c = ((Bset t) ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  rw [← hcdef] at hc ⊢
  obtain ⟨q2, hq2⟩ : ∃ q, q = x / md (j + 1) := ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ q, q = ((X t) (j + 1) - 1) / md (j + 1) := ⟨_, rfl⟩
  obtain ⟨q4, hq4⟩ : ∃ q, q = ((X t) (j + 1) - 1) / md j := ⟨_, rfl⟩
  obtain ⟨q5, hq5⟩ : ∃ q, q = ((X t) j - 1) / md j := ⟨_, rfl⟩
  have hcard3 : F3.card + q3 = q2 := by
    rw [hF3, hq3, hq2]; exact card_mul _ _ _ (by omega)
  have hcard1 : G1.card + q5 = q4 := by
    rw [hG1, hq5, hq4]; exact card_mul _ _ _ (by omega)
  have b2 : x < md (j + 1) * q2 + md (j + 1) := by
    have := Nat.lt_mul_div_succ x hm
    rw [← hq2] at this
    calc x < md (j + 1) * (q2 + 1) := this
      _ = md (j + 1) * q2 + md (j + 1) := by ring
  have b3 : md (j + 1) * q3 ≤ (X t) (j + 1) - 1 := by rw [hq3]; exact Nat.mul_div_le _ _
  have b4 : (X t) (j + 1) - 1 < md j * q4 + md j := by
    have := Nat.lt_mul_div_succ ((X t) (j + 1) - 1) hm'
    rw [← hq4] at this
    calc (X t) (j + 1) - 1 < md j * (q4 + 1) := this
      _ = md j * q4 + md j := by ring
  have b5 : md j * q5 ≤ (X t) j - 1 := by rw [hq5]; exact Nat.mul_div_le _ _
  have e1 : md (j + 1) * F3.card + md (j + 1) * q3 = md (j + 1) * q2 := by
    rw [← Nat.mul_add, hcard3]
  have e2 : md j * G1.card + md j * q5 = md j * q4 := by
    rw [← Nat.mul_add, hcard1]
  have e3 : md j * G1.card ≤ md (j + 1) * G1.card := Nat.mul_le_mul_right _ hmm
  have e4 : md (j + 1) * G1.card + md (j + 1) * F3.card ≤ md (j + 1) * c := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hc
  omega

/- The product of the two counts. -/

lemma ratio_bounds (t : ℕ → ℕ) {j x T : ℕ} (hj : 4 ≤ j) (hT : (12 * T + 16) ^ 2 ≤ j)
    (h1 : (X t) (j + 1) ≤ x) (h2 : x < (X t) (j + 2)) :
    T * x ≤ (T + 1) * (((Aset t) ∩ Set.Icc 1 x).ncard * ((Bset t) ∩ Set.Icc 1 x).ncard) ∧
      (T + 1) * (((Aset t) ∩ Set.Icc 1 x).ncard * ((Bset t) ∩ Set.Icc 1 x).ncard) ≤ (T + 2) * x := by
  obtain ⟨hA1, hA2⟩ := countA_bounds (k := j + 1) t (by omega) h1 h2
  have hU := (countB_upper t) hj h1 h2
  have hL := (countB_lower t) hj h1 h2
  obtain ⟨cA, hcA⟩ : ∃ c, c = ((Aset t) ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = ((Bset t) ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  rw [← hcA] at hA1 hA2 ⊢
  rw [← hc] at hU hL ⊢
  obtain ⟨α, hα⟩ : ∃ α, α = (seq t) (j + 1) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = (Y t) j := ⟨_, rfl⟩
  obtain ⟨m', hm'⟩ : ∃ m, m = md j := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = md (j + 1) := ⟨_, rfl⟩
  rw [← hα, ← hP, ← hm', ← hm] at hU
  rw [← hm] at hL
  have hm'pos : 0 < m' := by rw [hm']; exact md_pos (by omega)
  have hm'j : m' ≤ j := by rw [hm']; exact md_le j
  have hmj : m ≤ j + 1 := by rw [hm]; exact md_le (j + 1)
  have hαj : j + 1 ≤ α := by rw [hα]; exact (le_av t) (j + 1)
  have hxα : (j + 1) * α ≤ x := by rw [hα]; exact h1
  have hPα : (j + 1) ^ 2 * P ≤ α := by
    have := (av_growth t) j (by omega)
    rw [hP, hα]
    calc (j + 1) ^ 2 * (Y t) j = (j + 1) ^ 3 * (seq t) j := by unfold Y; ring
      _ ≤ (seq t) (j + 1) := this
  have hXP : (X t) j ≤ P := by
    rw [hP]; unfold X Y
    exact Nat.mul_le_mul_right _ (by omega)
  -- auxiliary products
  have p1 : (j + 1) * P ≤ α := by
    calc (j + 1) * P ≤ (j + 1) * ((j + 1) * P) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      _ = (j + 1) ^ 2 * P := by ring
      _ ≤ α := hPα
  have p2 : m' * P ≤ α := (Nat.mul_le_mul_right _ (by omega)).trans p1
  have p3 : α ≤ (j + 1) * α := Nat.le_mul_of_pos_left _ (by omega)
  -- upper bound
  have hUp : m' * (cA * c) ≤ (j + 8) * x := by
    have s1 : m' * (cA * c) ≤ (j + 2) * (m' * P + x + α + m) := by
      calc m' * (cA * c) = cA * (m' * c) := by ring
        _ ≤ (j + 2) * (m' * P + x + α + m) := Nat.mul_le_mul hA2 hU
    have s2 : (j + 2) * (m' * P + α + m) ≤ 6 * x := by
      calc (j + 2) * (m' * P + α + m) ≤ (2 * (j + 1)) * (3 * α) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 6 * ((j + 1) * α) := by ring
        _ ≤ 6 * x := Nat.mul_le_mul_left _ hxα
    calc m' * (cA * c) ≤ (j + 2) * (m' * P + x + α + m) := s1
      _ = (j + 2) * x + (j + 2) * (m' * P + α + m) := by ring
      _ ≤ (j + 2) * x + 6 * x := Nat.add_le_add_left s2 _
      _ = (j + 8) * x := by ring
  -- lower bound
  have hLo : (j + 1) * x ≤ (j + 1) * (cA * c) + 3 * x := by
    have s1 : (j + 1) * x ≤ (j + 1) * (m * c + (X t) j + 2 * m) := Nat.mul_le_mul_left _ hL
    have s2 : (j + 1) * ((X t) j + 2 * m) ≤ 3 * x := by
      have t1 : (j + 1) * (X t) j ≤ α := (Nat.mul_le_mul_left _ hXP).trans p1
      have t2 : (j + 1) * (2 * m) ≤ 2 * ((j + 1) * α) := by
        calc (j + 1) * (2 * m) ≤ (j + 1) * (2 * α) := Nat.mul_le_mul_left _ (by omega)
          _ = 2 * ((j + 1) * α) := by ring
      have t3 : (j + 1) * ((X t) j + 2 * m) = (j + 1) * (X t) j + (j + 1) * (2 * m) := by ring
      omega
    have s3 : (j + 1) * (m * c) ≤ (j + 1) * (cA * c) := by
      calc (j + 1) * (m * c) = m * ((j + 1) * c) := by ring
        _ ≤ (j + 1) * (cA * c) := by
            calc m * ((j + 1) * c) ≤ (j + 1) * ((j + 1) * c) := Nat.mul_le_mul_right _ hmj
              _ ≤ (j + 1) * (cA * c) :=
                  Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hA1)
    have s4 : (j + 1) * (m * c + (X t) j + 2 * m) = (j + 1) * (m * c) + (j + 1) * ((X t) j + 2 * m) := by
      ring
    omega
  -- the size of `j`
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt j := ⟨_, rfl⟩
  have hs1 : 12 * T + 16 ≤ s := by
    rw [hs, Nat.le_sqrt']
    exact hT
  have hs2 : s * s ≤ j := by rw [hs]; exact Nat.sqrt_le j
  have hms : j ≤ m' + s + 1 := by simpa [hm',hs] using md_lower j
  have hTs : T ≤ T * s := Nat.le_mul_of_pos_right _ (by omega)
  have hss : s * (12 * T + 16) ≤ s * s := Nat.mul_le_mul_left _ hs1
  have hss' : s * (12 * T + 16) = 12 * (T * s) + 16 * s := by ring
  have hbig : (s + 9) * (T + 1) ≤ m' := by
    have e : (s + 9) * (T + 1) = T * s + s + 9 * T + 9 := by ring
    omega
  have hjT : (j + 8) * (T + 1) ≤ m' * (T + 2) := by
    have e1 : (j + 8) * (T + 1) ≤ m' * (T + 1) + (s + 9) * (T + 1) := by
      rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
    have e2 : m' * (T + 2) = m' * (T + 1) + m' := by ring
    omega
  have hj3 : 3 * (T + 1) ≤ j + 1 := by
    have : 12 * T + 16 ≤ s * s := (Nat.le_mul_self _).trans (Nat.mul_le_mul hs1 hs1)
    omega
  constructor
  · -- lower
    have t1 : (j + 1) * (T * x) ≤ (j + 1) * ((T + 1) * (cA * c)) := by
      have u1 : (T + 1) * ((j + 1) * x) ≤ (T + 1) * ((j + 1) * (cA * c) + 3 * x) :=
        Nat.mul_le_mul_left _ hLo
      have u2 : 3 * (T + 1) * x ≤ (j + 1) * x := Nat.mul_le_mul_right _ hj3
      have u3 : (T + 1) * ((j + 1) * x) = (j + 1) * (T * x) + (j + 1) * x := by ring
      have u4 : (T + 1) * ((j + 1) * (cA * c) + 3 * x) =
          (j + 1) * ((T + 1) * (cA * c)) + 3 * (T + 1) * x := by ring
      omega
    exact Nat.le_of_mul_le_mul_left t1 (by omega)
  · -- upper
    have t1 : m' * ((T + 1) * (cA * c)) ≤ m' * ((T + 2) * x) := by
      calc m' * ((T + 1) * (cA * c)) = (T + 1) * (m' * (cA * c)) := by ring
        _ ≤ (T + 1) * ((j + 8) * x) := Nat.mul_le_mul_left _ hUp
        _ = (j + 8) * (T + 1) * x := by ring
        _ ≤ m' * (T + 2) * x := Nat.mul_le_mul_right _ hjT
        _ = m' * ((T + 2) * x) := by ring
    exact Nat.le_of_mul_le_mul_left t1 hm'pos

theorem complements (t : ℕ → ℕ) : (Aset t).Infinite ∧ (Bset t).Infinite ∧ 0 ∉ (Aset t) ∧ 0 ∉ (Bset t) ∧ Erdos785.IsExactAdditiveComplement (Aset t) (Bset t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `A` is infinite
    apply Set.infinite_range_of_injective
    intro a b h
    have := (av_strictMono t).injective h
    omega
  · -- `B` is infinite
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨k, hk⟩ : ∃ k, k = N + 4 := ⟨_, rfl⟩
    have hm : 0 < md k := md_pos (by omega)
    refine ⟨md k * ((X t) k / md k + 1),
      ⟨k, by omega, dvd_mul_right _ _, (Nat.lt_mul_div_succ _ hm).le, ?_⟩, ?_⟩
    · have h1 : md k * ((X t) k / md k + 1) =
          md k * ((X t) k / md k) + md k := by ring
      have h2 := Nat.mul_div_le ((X t) k) (md k)
      have h3 := md_le k
      have h4 := (X_lt_succ t) k
      have h5 := (Y_eq t) (k + 1)
      have h6 := (le_av t) (k + 1)
      omega
    · have h1 := Nat.lt_mul_div_succ ((X t) k) hm
      have h2 := (le_X t) k
      omega
  · -- `0 ∉ A`
    rintro ⟨i, hi⟩
    have := (av_pos t) (i + 1)
    simp only [] at hi
    omega
  · -- `0 ∉ B`
    rintro ⟨k, hk, -, hX, -⟩
    have := (le_X t) k
    omega
  · -- `A + B` contains all large integers
    exact Filter.eventually_atTop.2 ⟨(Y t) 4, fun n hn => (mem_add_of_large t) hn⟩
  · -- the counting functions
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T, hT⟩ := exists_nat_one_div_lt hε
    refine ⟨(X t) ((12 * T + 16) ^ 2 + 5), fun x hx => ?_⟩
    obtain ⟨k, hk, hXk, hxk⟩ := stage (X t) (X_strictMono t) hx
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨hlo, hhi⟩ := ratio_bounds (j := j) (x := x) (T := T) t (by omega) (by omega)
      hXk hxk
    unfold Erdos785.counting
    obtain ⟨N, hN⟩ : ∃ N : ℕ,
        N = ((Aset t) ∩ Set.Icc 1 x).ncard * ((Bset t) ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
    rw [← hN] at hlo hhi
    have hxpos : (0 : ℝ) < x := by
      have h1 := (le_X t) (j + 1)
      have h2 : 0 < x := by omega
      exact_mod_cast h2
    have hNr : (((Aset t) ∩ Set.Icc 1 x).ncard : ℝ) * (((Bset t) ∩ Set.Icc 1 x).ncard : ℝ)
        = (N : ℝ) := by
      rw [hN]; push_cast; ring
    rw [hNr, Real.dist_eq, div_sub_one hxpos.ne', abs_div, abs_of_pos hxpos, div_lt_iff₀ hxpos]
    have h1 : (T : ℝ) * x ≤ ((T : ℝ) + 1) * N := by exact_mod_cast hlo
    have h2 : ((T : ℝ) + 1) * N ≤ ((T : ℝ) + 2) * x := by exact_mod_cast hhi
    have hTpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    have h3 : (1 : ℝ) < ε * ((T : ℝ) + 1) := by
      rw [div_lt_iff₀ hTpos] at hT
      exact hT
    have h4 : (x : ℝ) < ε * ((T : ℝ) + 1) * x := by nlinarith
    rw [abs_lt]
    constructor
    · have h5 : ((T : ℝ) + 1) * (-(ε * x)) < ((T : ℝ) + 1) * ((N : ℝ) - x) := by nlinarith
      exact lt_of_mul_lt_mul_left h5 hTpos.le
    · have h5 : ((T : ℝ) + 1) * ((N : ℝ) - x) < ((T : ℝ) + 1) * (ε * x) := by nlinarith
      exact lt_of_mul_lt_mul_left h5 hTpos.le

lemma sparse_count (t : ℕ → ℕ) (k x : ℕ) (hx : x < seq t (k+1)) :
    Erdos785.counting (Aset t) x ≤ k := by
  have hsub : Aset t ∩ Set.Icc 1 x ⊆ ((Icc 1 k).image (seq t) : Finset ℕ) := by
    rintro b ⟨⟨i,rfl⟩,_,hi⟩
    apply mem_image.mpr
    refine ⟨i+1,mem_Icc.mpr ⟨by omega,?_⟩,rfl⟩
    have h : seq t (i+1) < seq t (k+1) := lt_of_le_of_lt hi hx
    have := (av_strictMono t).lt_iff_lt.mp h
    omega
  have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h
  exact h.trans (card_image_le.trans (by simp))

/-- At a stage of full modulus, only multiples of `k` contribute above the earlier blocks. -/
lemma dense_count (t : ℕ → ℕ) {k x : ℕ}
    (hm : md k = k) (hx : x < seq t (k+1)) :
    Erdos785.counting (Bset t) x ≤ Y t k + x/k := by
  let small := Ioc 0 (Y t k)
  let mult := (Ioc 0 x).filter fun b => k ∣ b
  have hsub : Bset t ∩ Set.Icc 1 x ⊆ (↑(small ∪ mult) : Set ℕ) := by
    rintro b ⟨⟨j,h4,hdiv,hl,hu⟩,hb1,hx'⟩
    apply mem_union.mpr
    rcases lt_trichotomy j k with ltj|eq|gtj
    · exact Or.inl (mem_Ioc.mpr ⟨hb1,(hu.le.trans ((Y_strictMono t).monotone ltj))⟩)
    · exact Or.inr (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hb1,hx'⟩,by simpa [eq,hm] using hdiv⟩)
    · have h1 : seq t (k+1) ≤ seq t j := (av_strictMono t).monotone gtj
      have h2 : seq t j ≤ X t j := Nat.le_mul_of_pos_left _ (by omega)
      omega
  have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h
  exact h.trans ((card_union_le _ _).trans (by
    simp [small,mult,Nat.Ioc_filter_dvd_card_eq_div]))

end Ruzsa785

open Ruzsa785 Filter in
theorem OMA.solution : type_of% @Erdos785.erdos_785.variants.ruzsa_upper_bound := by
  intro w hw
  have thresholds (b : ℕ) : ∃ t : ℕ, ∀ x ≥ t, (b : ℝ) < w x :=
    eventually_atTop.mp (hw.eventually_gt_atTop (b : ℝ))
  choose t ht using thresholds
  obtain ⟨ha,hb,ha0,hb0,hex⟩ := complements t
  refine ⟨Aset t,Bset t,ha,hb,ha0,hb0,hex,frequently_atTop.mpr ?_⟩
  intro N
  let k : ℕ := 2^(N+2)
  have hNk : N ≤ k := (show N ≤ N+2 by omega).trans (Nat.lt_two_pow_self (n := N+2)).le
  let x := thresh t k (seq t k)
  have hx : x < seq t (k+1) := (le_max_right ..).trans_lt (seq_step t k).1
  have hn : k ≤ x := by dsimp [x,thresh]; omega
  have ht' : t (k * Y t k) ≤ x := by
    change t (k*((k+1)*seq t k)) ≤ max _ _ + k
    exact (le_max_right ..).trans (Nat.le_add_right ..)
  have hA := sparse_count t k x hx
  have hB := dense_count t (md_pow (N+2)) hx
  have bound : Erdos785.counting (Aset t) x * Erdos785.counting (Bset t) x ≤ k * Y t k + x := calc
    _ ≤ k*(Y t k + x/k) := Nat.mul_le_mul hA hB
    _ ≤ k*Y t k + x := by rw [Nat.mul_add]; exact Nat.add_le_add_left (Nat.mul_div_le ..) _
  have hreal : (Erdos785.counting (Aset t) x : ℝ) * Erdos785.counting (Bset t) x ≤
      (k * Y t k : ℕ) + (x : ℝ) := by exact_mod_cast bound
  exact ⟨x,hNk.trans hn,(by linarith [ht (k*Y t k) x ht'])⟩
