import OMAReductions.R_Erdos50_erdos_50_singular_R1
import Mathlib
/-! The finite prime-product approximation and its concentration estimate are adapted from @Genbox’s merged proof of Schoenberg’s theorem. The cutoff is chosen uniformly in the threshold. -/
open Filter Set Topology

namespace OMA50

open scoped Classical

noncomputable def cnt (S : Set ℕ) (b : ℕ) : ℕ := ((Finset.range b).filter (· ∈ S)).card

lemma pd_eq (S : Set ℕ) (b : ℕ) : S.partialDensity Set.univ b = (cnt S b : ℝ) / b := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  have h1 : S ∩ Iio b = ↑((Finset.range b).filter (· ∈ S)) := by
    ext n; simp [and_comm]
  rw [h1, Set.ncard_coe_finset, Nat.ncard_Iio]
  simp [cnt]

lemma hasDensity_iff (S : Set ℕ) (d : ℝ) :
    S.HasDensity d ↔ Tendsto (fun b => (cnt S b : ℝ) / b) atTop (𝓝 d) := by
  simp only [Set.HasDensity, pd_eq]

lemma cnt_succ (S : Set ℕ) (n : ℕ) :
    cnt S (n + 1) = cnt S n + (if n ∈ S then 1 else 0) := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma cnt_le (S : Set ℕ) (n : ℕ) : cnt S n ≤ n := by
  unfold cnt
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma cnt_mono {S T : Set ℕ} (h : S ⊆ T) (n : ℕ) : cnt S n ≤ cnt T n := by
  unfold cnt
  exact Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, h hx.2⟩)

lemma cnt_union_le (S T : Set ℕ) (n : ℕ) : cnt (S ∪ T) n ≤ cnt S n + cnt T n := by
  unfold cnt
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union] at hx ⊢
  tauto

lemma cnt_split (S X : Set ℕ) (n : ℕ) : cnt S n = cnt (S ∩ X) n + cnt (S \ X) n := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_union, Set.mem_inter_iff,
      Set.mem_sdiff]; tauto
  · rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_filter, Set.mem_inter_iff, Set.mem_sdiff] at h1 h2; tauto

def Per (Y : Set ℕ) (N : ℕ) : Prop := ∀ n, n ∈ Y ↔ n + N ∈ Y

lemma Per.mem_add_mul {Y : Set ℕ} {N : ℕ} (h : Per Y N) (n k : ℕ) :
    n ∈ Y ↔ n + N * k ∈ Y := by
  induction k with
  | zero => simp
  | succ k ih => rw [ih, h (n + N * k)]; ring_nf

lemma Per.mem_mod {Y : Set ℕ} {N : ℕ} (h : Per Y N) (n : ℕ) : n ∈ Y ↔ n % N ∈ Y := by
  rw [h.mem_add_mul (n % N) (n / N), Nat.mod_add_div]

lemma Per.cnt_add {Y : Set ℕ} {N : ℕ} (h : Per Y N) (n : ℕ) :
    cnt Y (n + N) = cnt Y n + cnt Y N := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    rw [show n + 1 + N = (n + N) + 1 by ring, cnt_succ, ih, cnt_succ]
    have := h n
    by_cases hn : n ∈ Y
    · rw [if_pos hn, if_pos (this.1 hn)]; omega
    · rw [if_neg hn, if_neg (fun h' => hn (this.2 h'))]; omega

lemma Per.cnt_approx {Y : Set ℕ} {N : ℕ} (h : Per Y N) (hN : 0 < N) (n : ℕ) :
    |(cnt Y n : ℝ) - n * (cnt Y N) / N| ≤ N := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < N
    · have h1 : (cnt Y n : ℝ) ≤ n := by exact_mod_cast cnt_le Y n
      have h2 : (cnt Y N : ℝ) ≤ N := by exact_mod_cast cnt_le Y N
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have h3 : (n : ℝ) * cnt Y N / N ≤ n := by
        rw [div_le_iff₀ hN']; exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : (0 : ℝ) ≤ n * cnt Y N / N := by positivity
      have h5 : (n : ℝ) ≤ N := by exact_mod_cast hn.le
      rw [abs_le]; constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (cnt Y n)]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + N := ⟨n - N, by omega⟩
      have := ih m (by omega)
      rw [h.cnt_add]
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have e : ((cnt Y m + cnt Y N : ℕ) : ℝ) - ((m + N : ℕ) : ℝ) * cnt Y N / N
          = (cnt Y m : ℝ) - m * cnt Y N / N := by
        push_cast; field_simp; ring
      rw [e]; exact this

lemma Per.hasDensity {Y : Set ℕ} {N : ℕ} (h : Per Y N) (hN : 0 < N) :
    Y.HasDensity ((cnt Y N : ℝ) / N) := by
  rw [hasDensity_iff, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n0, hn0⟩ := exists_nat_gt ((N : ℝ) / ε)
  refine ⟨n0 + 1, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn' : (N : ℝ) / ε < n := lt_of_lt_of_le hn0 (by exact_mod_cast (show n0 ≤ n by omega))
  rw [Real.dist_eq]
  have e : (cnt Y n : ℝ) / n - cnt Y N / N = ((cnt Y n : ℝ) - n * cnt Y N / N) / n := by
    field_simp
  rw [e, abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos]
  refine lt_of_le_of_lt (h.cnt_approx hN n) ?_
  rwa [div_lt_iff₀ hε, mul_comm] at hn'

lemma HasDensity.unique {S : Set ℕ} {a b : ℝ} (ha : S.HasDensity a) (hb : S.HasDensity b) :
    a = b := tendsto_nhds_unique ha hb

lemma HasDensity.diff {S X : Set ℕ} {a b : ℝ} (ha : S.HasDensity a)
    (hb : (S ∩ X).HasDensity b) : (S \ X).HasDensity (a - b) := by
  rw [hasDensity_iff] at *
  refine (ha.sub hb).congr (fun n => ?_)
  rw [cnt_split S X n]; push_cast; ring

/-- Key CRT counting: multiples of a coprime `p` in a periodic set. -/
lemma Per.cnt_dvd {Y : Set ℕ} {N p : ℕ} (h : Per Y N) (hN : 0 < N) (hp : 0 < p)
    (hc : Nat.Coprime p N) : cnt (Y ∩ {n | p ∣ n}) (p * N) = cnt Y N := by
  unfold cnt
  have e1 : (Finset.range (p * N)).filter (· ∈ Y ∩ {n | p ∣ n}) =
      ((Finset.range N).filter (fun k => p * k ∈ Y)).image (p * ·) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff, Set.mem_setOf_eq,
      Finset.mem_image]
    constructor
    · rintro ⟨h1, h2, k, rfl⟩
      exact ⟨k, ⟨by nlinarith, h2⟩, rfl⟩
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      exact ⟨by nlinarith, h2, dvd_mul_right _ _⟩
  refine Eq.trans (b := (((Finset.range N).filter (fun k => p * k ∈ Y)).image (p * ·)).card)
    (by convert congrArg Finset.card e1) ?_
  rw [Finset.card_image_of_injective _ (fun a b hab => by
    simpa [hp.ne'] using hab)]
  -- bijection k ↦ p*k % N
  have hinj : ∀ a ∈ Finset.range N, ∀ b ∈ Finset.range N, p * a % N = p * b % N → a = b := by
    intro a ha b hb hab
    simp only [Finset.mem_range] at ha hb
    have h1 : p * a ≡ p * b [MOD N] := hab
    have h2 := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) h1
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  have himg : (Finset.range N).image (fun k => p * k % N) = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨k, -, rfl⟩ := hx; exact Nat.mod_lt _ hN
    · rw [Finset.card_image_of_injOn (fun a ha b hb hab => hinj a ha b hb hab)]
  apply Finset.card_nbij (fun k => p * k % N)
  · intro k hk
    have hk' := Finset.mem_filter.1 hk
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hN), (h.mem_mod _).1 hk'.2⟩
  · intro a ha b hb hab
    have ha' := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
    have hb' := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
    exact hinj a ha'.1 b hb'.1 hab
  · intro m hm
    have hm' := Finset.mem_filter.1 (Finset.mem_coe.1 hm)
    have : m ∈ (Finset.range N).image (fun k => p * k % N) := by
      rw [himg]; exact hm'.1
    obtain ⟨k, hk, hkm⟩ := Finset.mem_image.1 this
    refine ⟨k, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hk, ?_⟩), hkm⟩
    rw [h.mem_mod, hkm]; exact hm'.2

lemma Per.inter_dvd {Y : Set ℕ} {N p : ℕ} (h : Per Y N) :
    Per (Y ∩ {n | p ∣ n}) (p * N) := by
  intro n
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [h.mem_add_mul n p, mul_comm N p, Nat.dvd_add_left (dvd_mul_right p N)]

lemma Per.hasDensity_dvd {Y : Set ℕ} {N p : ℕ} (h : Per Y N) (hN : 0 < N) (hp : 0 < p)
    (hc : Nat.Coprime p N) {d : ℝ} (hd : Y.HasDensity d) :
    (Y ∩ {n | p ∣ n}).HasDensity (d / p) := by
  have e := HasDensity.unique hd (h.hasDensity hN)
  have := (h.inter_dvd (p := p)).hasDensity (Nat.mul_pos hp hN)
  rw [h.cnt_dvd hN hp hc] at this
  convert this using 1
  rw [e]; push_cast; field_simp

/-- Cauchy criterion for densities. -/
lemma exists_hasDensity (S : Set ℕ)
    (h : ∀ ε > 0, ∃ d : ℝ, ∀ᶠ n in atTop, |(cnt S n : ℝ) / n - d| ≤ ε) :
    ∃ L, S.HasDensity L := by
  have hc : CauchySeq (fun n => (cnt S n : ℝ) / n) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨d, hd⟩ := h (ε / 3) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hd
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm
    have h2 := hN n hn
    rw [Real.dist_eq]
    calc |(cnt S m : ℝ) / m - cnt S n / n|
        = |((cnt S m : ℝ) / m - d) - ((cnt S n : ℝ) / n - d)| := by ring_nf
      _ ≤ |(cnt S m : ℝ) / m - d| + |(cnt S n : ℝ) / n - d| := abs_sub _ _
      _ < ε := by linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨L, (hasDensity_iff S L).2 hL⟩


/-! ## The finite model -/

def status (Q : Finset ℕ) (n : ℕ) : Finset ℕ := Q.filter (· ∣ n)

noncomputable def g (D : Finset ℕ) : ℝ := ∏ p ∈ D, (1 - 1 / (p : ℝ))

noncomputable def w (Q D : Finset ℕ) : ℝ :=
  (∏ p ∈ D, 1 / (p : ℝ)) * ∏ p ∈ Q \ D, (1 - 1 / (p : ℝ))

lemma one_sub_nonneg' (p : ℕ) : 0 ≤ 1 - 1 / (p : ℝ) := by
  rcases Nat.eq_zero_or_pos p with h | h
  · simp [h]
  · have : (1 : ℝ) / p ≤ 1 := by
      rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast h
    linarith

lemma g_nonneg (D : Finset ℕ) : 0 ≤ g D := Finset.prod_nonneg fun p _ => one_sub_nonneg' p

lemma g_insert {p : ℕ} {E : Finset ℕ} (h : p ∉ E) : g (insert p E) = (1 - 1 / (p : ℝ)) * g E := by
  unfold g; rw [Finset.prod_insert h]

lemma status_per (Q : Finset ℕ) (R : Finset ℕ → Prop) :
    Per {n | R (status Q n)} (∏ p ∈ Q, p) := by
  intro n
  simp only [Set.mem_setOf_eq]
  have : status Q (n + ∏ p ∈ Q, p) = status Q n := by
    unfold status
    refine Finset.filter_congr fun p hp => ?_
    exact Nat.dvd_add_left (Finset.dvd_prod_of_mem _ hp)
  rw [this]

lemma prod_pos_of_primes (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) : 0 < ∏ p ∈ Q, p :=
  Finset.prod_pos fun p hp => (hQ p hp).pos

lemma status_insert {p : ℕ} {Q : Finset ℕ} (n : ℕ) :
    status (insert p Q) n = if p ∣ n then insert p (status Q n) else status Q n := by
  unfold status; rw [Finset.filter_insert]

lemma density_status (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    ∀ D ⊆ Q, {n | status Q n = D}.HasDensity (w Q D) := by
  induction Q using Finset.induction_on with
  | empty =>
    intro D hD
    rw [Finset.subset_empty] at hD
    subst hD
    have : {n | status ∅ n = (∅ : Finset ℕ)} = Set.univ := by
      ext n; simp [status]
    rw [this]
    simp [w]
  | insert p Q hpQ ih =>
    intro D hD
    have hp : p.Prime := hQ p (Finset.mem_insert_self p Q)
    have hQ' : ∀ q ∈ Q, q.Prime := fun q hq => hQ q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ Q, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact (Nat.coprime_primes hp (hQ' q hq)).2 (fun h => hpQ (h ▸ hq))
    have hN := prod_pos_of_primes Q hQ'
    have hpS : ∀ n, p ∉ status Q n := fun n h => hpQ (Finset.mem_filter.1 h).1
    by_cases hpD : p ∈ D
    · have hE : D.erase p ⊆ Q := by
        intro x hx
        have := Finset.mem_erase.1 hx
        rcases Finset.mem_insert.1 (hD this.2) with h | h
        · exact absurd h this.1
        · exact h
      have hset : {n | status (insert p Q) n = D} =
          {n | status Q n = D.erase p} ∩ {n | p ∣ n} := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, status_insert]
        by_cases hn : p ∣ n
        · rw [if_pos hn]
          constructor
          · intro h; refine ⟨?_, hn⟩; rw [← h, Finset.erase_insert (hpS n)]
          · intro h; rw [h.1, Finset.insert_erase hpD]
        · rw [if_neg hn]
          constructor
          · intro h; exact absurd (h ▸ hpD) (hpS n)
          · intro h; exact absurd h.2 hn
      rw [hset]
      have := (status_per Q (· = D.erase p)).hasDensity_dvd hN hp.pos hcop (ih hQ' _ hE)
      convert this using 1
      unfold w
      rw [← Finset.mul_prod_erase D _ hpD]
      have : insert p Q \ D = Q \ D.erase p := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact absurd (h1 ▸ hpD) h2
          · exact ⟨h1, fun h => h2 h.2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨Or.inr h1, fun h => h2 ⟨?_, h⟩⟩
          rintro rfl; exact hpQ h1
      rw [this]; ring
    · have hD' : D ⊆ Q := by
        intro x hx
        rcases Finset.mem_insert.1 (hD hx) with h | h
        · exact absurd (h ▸ hx) hpD
        · exact h
      have hset : {n | status (insert p Q) n = D} =
          {n | status Q n = D} \ {n | p ∣ n} := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_sdiff, status_insert]
        by_cases hn : p ∣ n
        · rw [if_pos hn]
          constructor
          · intro h; exact absurd (h ▸ Finset.mem_insert_self p _) hpD
          · intro h; exact absurd hn h.2
        · rw [if_neg hn]; tauto
      rw [hset]
      have h1 := ih hQ' D hD'
      have h2 := (status_per Q (· = D)).hasDensity_dvd hN hp.pos hcop h1
      have := HasDensity.diff h1 h2
      convert this using 1
      unfold w
      have : insert p Q \ D = insert p (Q \ D) := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact Or.inl h1
          · exact Or.inr ⟨h1, h2⟩
        · rintro (h1 | ⟨h1, h2⟩)
          · exact ⟨Or.inl h1, h1 ▸ hpD⟩
          · exact ⟨Or.inr h1, h2⟩
      rw [this, Finset.prod_insert (fun h => hpQ (Finset.mem_sdiff.1 h).1)]
      ring

lemma density_pred (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (R : Finset ℕ → Prop) :
    {n | R (status Q n)}.HasDensity (∑ D ∈ Q.powerset.filter R, w Q D) := by
  have hc : ∀ b, cnt {n | R (status Q n)} b =
      ∑ D ∈ Q.powerset.filter R, cnt {n | status Q n = D} b := by
    intro b
    unfold cnt
    rw [Finset.card_eq_sum_card_fiberwise (f := status Q) (t := Q.powerset.filter R)]
    · refine Finset.sum_congr rfl fun D hD => ?_
      congr 1
      ext n
      simp only [Finset.mem_filter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ (Finset.mem_filter.1 hD).2⟩, h3⟩
    · intro n hn
      have hn' := (Finset.mem_filter.1 hn).2
      exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _), hn'⟩
  rw [hasDensity_iff]
  have := tendsto_finset_sum (Q.powerset.filter R) (fun D hD =>
    (hasDensity_iff _ _).1 (density_status Q hQ D (Finset.mem_powerset.1 (Finset.mem_filter.1 hD).1)))
  refine this.congr fun b => ?_
  rw [hc b]; push_cast; rw [Finset.sum_div]

lemma sum_w (Q : Finset ℕ) : ∑ D ∈ Q.powerset, w Q D = 1 := by
  unfold w
  rw [← Finset.prod_add]
  simp

/-! ## Anti-concentration via toggling -/

def tog (p : ℕ) (D : Finset ℕ) : Finset ℕ := if p ∈ D then D.erase p else insert p D

lemma tog_tog (p : ℕ) (D : Finset ℕ) : tog p (tog p D) = D := by
  unfold tog
  by_cases h : p ∈ D
  · rw [if_pos h, if_neg (Finset.notMem_erase p D), Finset.insert_erase h]
  · rw [if_neg h, if_pos (Finset.mem_insert_self p D), Finset.erase_insert h]

lemma tog_subset {p : ℕ} {Q D : Finset ℕ} (hp : p ∈ Q) (hD : D ⊆ Q) : tog p D ⊆ Q := by
  unfold tog
  split_ifs
  · exact (Finset.erase_subset p D).trans hD
  · exact Finset.insert_subset hp hD

lemma w_insert {p : ℕ} {Q E : Finset ℕ} (hp : p ∈ Q) (hE : E ⊆ Q) (hpE : p ∉ E) :
    ∃ C ≥ (0 : ℝ), w Q (insert p E) = (1 / p) * C ∧ w Q E = (1 - 1 / (p : ℝ)) * C := by
  refine ⟨(∏ q ∈ E, 1 / (q : ℝ)) * ∏ q ∈ Q \ insert p E, (1 - 1 / (q : ℝ)), ?_, ?_, ?_⟩
  · exact mul_nonneg (Finset.prod_nonneg fun q _ => by positivity)
      (Finset.prod_nonneg fun q _ => one_sub_nonneg' q)
  · unfold w; rw [Finset.prod_insert hpE]; ring
  · unfold w
    have : Q \ E = insert p (Q \ insert p E) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hx : x = p
        · exact Or.inl hx
        · exact Or.inr ⟨h1, fun h => h.elim hx h2⟩
      · rintro (h1 | ⟨h1, h2⟩)
        · exact ⟨h1 ▸ hp, h1 ▸ hpE⟩
        · exact ⟨h1, fun h => h2 (Or.inr h)⟩
    rw [this, Finset.prod_insert (by simp)]; ring

lemma w_tog {p : ℕ} {Q D : Finset ℕ} (hpr : p.Prime) (hp : p ∈ Q) (hD : D ⊆ Q) :
    w Q D / p ≤ w Q (tog p D) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  unfold tog
  by_cases hpD : p ∈ D
  · rw [if_pos hpD]
    obtain ⟨C, hC, h1, h3⟩ := w_insert hp ((Finset.erase_subset p D).trans hD)
      (Finset.notMem_erase p D)
    rw [Finset.insert_erase hpD] at h1
    rw [h1, h3]
    have : 1 / (p : ℝ) / p ≤ 1 - 1 / p := by
      rw [div_div, div_le_iff₀ (by positivity)]
      have e : (1 - 1 / (p : ℝ)) * (p * p) = p * p - p := by field_simp
      nlinarith
    calc 1 / (p : ℝ) * C / p = (1 / p / p) * C := by ring
      _ ≤ (1 - 1 / p) * C := mul_le_mul_of_nonneg_right this hC
  · rw [if_neg hpD]
    obtain ⟨C, hC, h1, h3⟩ := w_insert hp hD hpD
    rw [h1, h3]
    have : 0 ≤ 1 / (p : ℝ) := by positivity
    have h4 : (1 - 1 / (p : ℝ)) / p ≤ 1 / p := by
      rw [div_le_div_iff_of_pos_right hp0]; linarith
    calc (1 - 1 / (p : ℝ)) * C / p = ((1 - 1 / p) / p) * C := by ring
      _ ≤ 1 / p * C := mul_le_mul_of_nonneg_right h4 hC

lemma sep_out {p q : ℕ} {F : Finset ℕ} {x η : ℝ} (hη : 0 ≤ η)
    (hsep : (1 + η) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ))
    (hp1 : x ≤ (1 - 1 / (p : ℝ)) * g F) (hq2 : (1 - 1 / (q : ℝ)) * g F < x * (1 + η)) : False := by
  have hg := g_nonneg F
  have h1 : (1 + η) * x ≤ (1 + η) * ((1 - 1 / (p : ℝ)) * g F) :=
    mul_le_mul_of_nonneg_left hp1 (by linarith)
  have h2 : (1 + η) * (1 - 1 / (p : ℝ)) * g F ≤ (1 - 1 / (q : ℝ)) * g F :=
    mul_le_mul_of_nonneg_right hsep hg
  nlinarith

lemma sep_in {p q : ℕ} {u v x η : ℝ} (hp2 : 2 ≤ p)
    (hsep : (1 + η) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ))
    (huv : (1 - 1 / (p : ℝ)) * u = (1 - 1 / (q : ℝ)) * v)
    (hu : u < x * (1 + η)) (hv : x ≤ v) (hv0 : 0 ≤ v) (hη : 0 ≤ η) : False := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have h3 : (1 + η) * (1 - 1 / (p : ℝ)) * v ≤ (1 - 1 / (q : ℝ)) * v :=
    mul_le_mul_of_nonneg_right hsep hv0
  have h4 : (1 - 1 / (p : ℝ)) * ((1 + η) * v) ≤ (1 - 1 / (p : ℝ)) * u := by nlinarith
  have h5 : (1 + η) * v ≤ u := le_of_mul_le_mul_left h4 hpos
  nlinarith

lemma card_tog_le (Q P F : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q) (x η : ℝ)
    (hη : 0 ≤ η)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p < q → (1 + η) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ)) :
    (P.filter (fun p => x ≤ g (tog p F) ∧ g (tog p F) < x * (1 + η))).card ≤ 2 := by
  set s := P.filter (fun p => x ≤ g (tog p F) ∧ g (tog p F) < x * (1 + η))
  have hsub : s ⊆ s.filter (· ∈ F) ∪ s.filter (· ∉ F) := by
    intro p hp; by_cases h : p ∈ F
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hp, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hp, h⟩)
  have hA : (s.filter (· ∈ F)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [s, Finset.mem_filter] at ha hb
    have key : ∀ p q, p ∈ P → q ∈ P → p ∈ F → q ∈ F → p < q →
        (x ≤ g (tog p F) ∧ g (tog p F) < x * (1 + η)) →
        (x ≤ g (tog q F) ∧ g (tog q F) < x * (1 + η)) → False := by
      intro p q hp hq hpF hqF hpq h1 h2
      unfold tog at h1 h2
      rw [if_pos hpF] at h1
      rw [if_pos hqF] at h2
      have ep := g_insert (Finset.notMem_erase p F)
      have eq := g_insert (Finset.notMem_erase q F)
      rw [Finset.insert_erase hpF] at ep
      rw [Finset.insert_erase hqF] at eq
      exact sep_in (hQ p (hPQ hp)).two_le (hsep p hp q hq hpq) (ep.symm.trans eq) h1.2 h2.1
        (g_nonneg _) hη
    rcases lt_trichotomy a b with h | h | h
    · exact (key a b ha.1.1 hb.1.1 ha.2 hb.2 h ha.1.2 hb.1.2).elim
    · exact h
    · exact (key b a hb.1.1 ha.1.1 hb.2 ha.2 h hb.1.2 ha.1.2).elim
  have hB : (s.filter (· ∉ F)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [s, Finset.mem_filter] at ha hb
    have key : ∀ p q, p ∈ P → q ∈ P → p ∉ F → q ∉ F → p < q →
        (x ≤ g (tog p F) ∧ g (tog p F) < x * (1 + η)) →
        (x ≤ g (tog q F) ∧ g (tog q F) < x * (1 + η)) → False := by
      intro p q hp hq hpF hqF hpq h1 h2
      unfold tog at h1 h2
      rw [if_neg hpF, g_insert hpF] at h1
      rw [if_neg hqF, g_insert hqF] at h2
      exact sep_out hη (hsep p hp q hq hpq) h1.1 h2.2
    rcases lt_trichotomy a b with h | h | h
    · exact (key a b ha.1.1 hb.1.1 ha.2 hb.2 h ha.1.2 hb.1.2).elim
    · exact h
    · exact (key b a hb.1.1 ha.1.1 hb.2 ha.2 h hb.1.2 ha.1.2).elim
  calc s.card ≤ (s.filter (· ∈ F) ∪ s.filter (· ∉ F)).card := Finset.card_le_card hsub
    _ ≤ (s.filter (· ∈ F)).card + (s.filter (· ∉ F)).card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

theorem anti (Q P : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q) (x η : ℝ) (hη : 0 ≤ η)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p < q → (1 + η) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ)) :
    (∑ D ∈ Q.powerset.filter (fun D => x ≤ g D ∧ g D < x * (1 + η)), w Q D) *
      (∑ p ∈ P, 1 / (p : ℝ)) ≤ 2 := by
  set W := Q.powerset.filter (fun D => x ≤ g D ∧ g D < x * (1 + η))
  have hW : ∀ D ∈ W, D ⊆ Q := fun D hD => Finset.mem_powerset.1 (Finset.mem_filter.1 hD).1
  have step1 : (∑ D ∈ W, w Q D) * (∑ p ∈ P, 1 / (p : ℝ)) = ∑ p ∈ P, ∑ D ∈ W, w Q D / p := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun D _ => by ring
  have step2 : ∀ p ∈ P, ∑ D ∈ W, w Q D / p ≤ ∑ D ∈ W, w Q (tog p D) := fun p hp =>
    Finset.sum_le_sum fun D hD => w_tog (hQ p (hPQ hp)) (hPQ hp) (hW D hD)
  have step3 : ∀ p ∈ P, ∑ D ∈ W, w Q (tog p D) =
      ∑ F ∈ Q.powerset, if tog p F ∈ W then w Q F else 0 := by
    intro p hp
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (tog p) (tog p) ?_ ?_ ?_ ?_ ?_
    · intro D hD
      exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (tog_subset (hPQ hp) (hW D hD)),
        by rw [tog_tog]; exact hD⟩
    · intro F hF
      exact (Finset.mem_filter.1 hF).2
    · intro D _; exact tog_tog p D
    · intro F _; exact tog_tog p F
    · intro D _; rfl
  have step4 : ∀ F ∈ Q.powerset, (∑ p ∈ P, if tog p F ∈ W then w Q F else 0) ≤ 2 * w Q F := by
    intro F hF
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hw : 0 ≤ w Q F := by
      unfold w
      exact mul_nonneg (Finset.prod_nonneg fun q _ => by positivity)
        (Finset.prod_nonneg fun q _ => one_sub_nonneg' q)
    have hcard : (P.filter (fun p => tog p F ∈ W)).card ≤ 2 := by
      have := card_tog_le Q P F hQ hPQ x η hη hsep
      refine le_trans (Finset.card_le_card fun p hp => ?_) this
      simp only [Finset.mem_filter, W] at hp ⊢
      exact ⟨hp.1, hp.2.2⟩
    have : ((P.filter (fun p => tog p F ∈ W)).card : ℝ) ≤ 2 := by exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_right this hw
  rw [step1]
  calc ∑ p ∈ P, ∑ D ∈ W, w Q D / p ≤ ∑ p ∈ P, ∑ D ∈ W, w Q (tog p D) :=
        Finset.sum_le_sum step2
    _ = ∑ p ∈ P, ∑ F ∈ Q.powerset, if tog p F ∈ W then w Q F else 0 :=
        Finset.sum_congr rfl step3
    _ = ∑ F ∈ Q.powerset, ∑ p ∈ P, if tog p F ∈ W then w Q F else 0 := Finset.sum_comm
    _ ≤ ∑ F ∈ Q.powerset, 2 * w Q F := Finset.sum_le_sum step4
    _ = 2 := by rw [← Finset.mul_sum, sum_w]; ring


/-! ## Number theory bridge -/

lemma phi_eq {n : ℕ} (hn : n ≠ 0) :
    (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  simpa [one_div] using h

noncomputable def hK (K n : ℕ) : ℝ := ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), 1 / (p : ℝ)

noncomputable def QK (K : ℕ) : Finset ℕ := (Finset.range (K + 1)).filter Nat.Prime

lemma QK_prime (K : ℕ) : ∀ p ∈ QK K, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2

lemma prod_ge (s : Finset ℕ) : 1 - ∑ p ∈ s, 1 / (p : ℝ) ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0 := one_sub_nonneg' a
    have hy : 0 ≤ ∑ p ∈ s, 1 / (p : ℝ) := Finset.sum_nonneg fun p _ => by positivity
    have hx : 0 ≤ 1 / (a : ℝ) := by positivity
    have : (1 - 1 / (a : ℝ)) * (1 - ∑ p ∈ s, 1 / (p : ℝ)) ≤
        (1 - 1 / (a : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) := mul_le_mul_of_nonneg_left ih h0
    nlinarith

lemma phi_split {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (Nat.totient n : ℝ) = n * (g (status (QK K) n) *
      ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), (1 - 1 / (p : ℝ))) := by
  rw [phi_eq hn, ← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ≤ K)]
  congr 2
  unfold g status QK
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2, _⟩, h4⟩; exact ⟨⟨by omega, h1⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3, hn⟩, by omega⟩

lemma lower_incl {n : ℕ} (hn : n ≠ 0) (K : ℕ) {c : ℝ} (h : g (status (QK K) n) < c) :
    (Nat.totient n : ℝ) < c * n := by
  rw [phi_split hn K]
  have hR : ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), (1 - 1 / (p : ℝ)) ≤ 1 :=
    Finset.prod_le_one (fun p _ => one_sub_nonneg' p) (fun p _ => by
      have : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith)
  have hR0 : 0 ≤ ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), (1 - 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p _ => one_sub_nonneg' p
  have hg := g_nonneg (status (QK K) n)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have : g (status (QK K) n) * ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K),
      (1 - 1 / (p : ℝ)) < c := by nlinarith
  nlinarith

lemma upper_incl {n : ℕ} (K : ℕ) {c δ : ℝ} (hδ : δ < 1) (h : (Nat.totient n : ℝ) < c * n)
    (hb : hK K n ≤ δ) : g (status (QK K) n) < c / (1 - δ) := by
  have hn : n ≠ 0 := by rintro rfl; simp at h
  rw [phi_split hn K] at h
  have hR := prod_ge (n.primeFactors.filter (fun p => ¬ p ≤ K))
  unfold hK at hb
  have hg := g_nonneg (status (QK K) n)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [lt_div_iff₀ (by linarith)]
  have h1 : g (status (QK K) n) * ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K),
      (1 - 1 / (p : ℝ)) < c := by
    by_contra hc
    have hc' := le_of_not_gt hc
    nlinarith [mul_le_mul_of_nonneg_left hc' hn'.le]
  have h2 : g (status (QK K) n) * (1 - δ) ≤ g (status (QK K) n) *
      ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), (1 - 1 / (p : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hg
  linarith

/-! ## The bad set -/

lemma tail_sq (K : ℕ) (hK : 1 ≤ K) (N : ℕ) :
    ∑ m ∈ (Finset.range N).filter (fun m => ¬ m ≤ K), 1 / (m : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
  have key : ∀ j : ℕ, ∑ m ∈ (Finset.range (j + K + 1)).filter (fun m => ¬ m ≤ K),
      1 / (m : ℝ) ^ 2 ≤ 1 / (K : ℝ) - 1 / ((j + K : ℕ) : ℝ) := by
    intro j
    induction j with
    | zero =>
      have : (Finset.range (0 + K + 1)).filter (fun m => ¬ m ≤ K) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro m hm; simp only [Finset.mem_range] at hm; omega
      rw [this]; simp
    | succ j ih =>
      rw [show j + 1 + K + 1 = (j + K + 1) + 1 by ring, Finset.range_add_one,
        Finset.filter_insert, if_pos (by omega),
        Finset.sum_insert (by simp)]
      have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have hjK : (0 : ℝ) < (j + K : ℕ) := by push_cast; positivity
      have e : 1 / (((j + K + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / ((j + K : ℕ) : ℝ) - 1 / ((j + 1 + K : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
  have hsub : (Finset.range N).filter (fun m => ¬ m ≤ K) ⊆
      (Finset.range (N + K + 1)).filter (fun m => ¬ m ≤ K) :=
    Finset.filter_subset_filter _ (Finset.range_subset_range.2 (by omega))
  calc _ ≤ ∑ m ∈ (Finset.range (N + K + 1)).filter (fun m => ¬ m ≤ K), 1 / (m : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 1 / (K : ℝ) - 1 / ((N + K : ℕ) : ℝ) := key N
    _ ≤ 1 / (K : ℝ) := by
        have : (0 : ℝ) ≤ 1 / ((N + K : ℕ) : ℝ) := by positivity
        linarith

lemma card_mult_le (p N : ℕ) (hp : 0 < p) :
    (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) ≤ N / p := by
  have h : (Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0) ⊆
      (Finset.Icc 1 (N / p)).image (p * ·) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, ⟨k, rfl⟩, hn0⟩ := hn
    simp only [Finset.mem_image, Finset.mem_Icc]
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · simp [h] at hn0
      · exact h
    · rw [Nat.le_div_iff_mul_le hp]; linarith
  have h1 := Finset.card_le_card h
  have h2 := Finset.card_image_le (s := Finset.Icc 1 (N / p)) (f := (p * ·))
  simp only [Nat.card_Icc, add_tsub_cancel_right] at h2
  have h3 : ((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card ≤ N / p := h1.trans h2
  calc (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) ≤ ((N / p : ℕ) : ℝ) := by
        exact_mod_cast h3
    _ ≤ N / p := Nat.cast_div_le

lemma sum_hK (K N : ℕ) (hK1 : 1 ≤ K) : ∑ n ∈ Finset.range N, hK K n ≤ N / K := by
  have e1 : ∀ n ∈ Finset.range N, hK K n = ∑ p ∈ Finset.range N,
      if (p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0) then 1 / (p : ℝ) else 0 := by
    intro n hn
    rw [← Finset.sum_filter]
    unfold hK
    congr 1
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range] at hn ⊢
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h2) hn, ⟨h1, h4⟩, h2, h3⟩
    · rintro ⟨_, ⟨h1, h4⟩, h2, h3⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  have e2 : ∀ p ∈ Finset.range N, (∑ n ∈ Finset.range N,
      if (p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0) then 1 / (p : ℝ) else 0) ≤
      if ¬ p ≤ K then N * (1 / (p : ℝ) ^ 2) else 0 := by
    intro p _
    by_cases hp : p.Prime ∧ ¬ p ≤ K
    · have hiff : ∀ n, ((p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0)) ↔ (p ∣ n ∧ n ≠ 0) :=
        fun n => ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩
      rw [if_pos hp.2, Finset.sum_congr rfl (fun n _ => if_congr (hiff n) rfl rfl),
        ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have := card_mult_le p N hp.1.pos
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
      calc (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) * (1 / p)
          ≤ (N / p) * (1 / p) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = N * (1 / (p : ℝ) ^ 2) := by field_simp
    · have : ∀ n, ¬ ((p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0)) := fun n h => hp h.1
      simp only [this, if_false, Finset.sum_const_zero]
      split_ifs <;> positivity
  calc _ ≤ ∑ p ∈ Finset.range N, (if ¬ p ≤ K then N * (1 / (p : ℝ) ^ 2) else 0) :=
        Finset.sum_le_sum e2
    _ = N * ∑ m ∈ (Finset.range N).filter (fun m => ¬ m ≤ K), 1 / (m : ℝ) ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_filter]
    _ ≤ N * (1 / K) := mul_le_mul_of_nonneg_left (tail_sq K hK1 N) (by positivity)
    _ = N / K := by ring

lemma cnt_bad (K N : ℕ) (hK1 : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) :
    (cnt {n | δ < hK K n} N : ℝ) ≤ N / (K * δ) := by
  have hnn : ∀ n, 0 ≤ hK K n := fun n => Finset.sum_nonneg fun p _ => by positivity
  have h1 : (cnt {n | δ < hK K n} N : ℝ) * δ ≤ ∑ n ∈ Finset.range N, hK K n := by
    unfold cnt
    calc (((Finset.range N).filter (· ∈ {n | δ < hK K n})).card : ℝ) * δ
        = ∑ n ∈ (Finset.range N).filter (· ∈ {n | δ < hK K n}), δ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ (Finset.range N).filter (· ∈ {n | δ < hK K n}), hK K n :=
          Finset.sum_le_sum fun n hn => (Finset.mem_filter.1 hn).2.le
      _ ≤ ∑ n ∈ Finset.range N, hK K n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => hnn n)
  have h2 := sum_hK K N hK1
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK1
  have h3 : (cnt {n | δ < hK K n} N : ℝ) * δ ≤ N / K := h1.trans h2
  rw [le_div_iff₀ hK'] at h3
  rw [le_div_iff₀ (by positivity)]
  calc (cnt {n | δ < hK K n} N : ℝ) * (K * δ) = cnt {n | δ < hK K n} N * δ * K := by ring
    _ ≤ N := h3

/-! ## Divergence of the prime harmonic series -/

lemma diverge (R : ℝ) : ∃ L, R ≤ ∑ p ∈ (Finset.range L).filter Nat.Prime, 1 / (p : ℝ) := by
  by_contra h
  push Not at h
  apply not_summable_one_div_on_primes
  refine summable_of_sum_range_le (c := R) (fun n => ?_) (fun n => ?_)
  · exact Set.indicator_nonneg (fun p _ => by positivity) _
  · rw [show ∑ i ∈ Finset.range n, Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i =
        ∑ p ∈ (Finset.range n).filter Nat.Prime, 1 / (p : ℝ) by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Set.indicator_apply]]
    exact (h n).le


/-! ## Assembly -/

lemma cnt_zero_le (N : ℕ) : cnt {0} N ≤ 1 := by
  unfold cnt
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Set.mem_singleton_iff] at ha hb
  rw [ha.2, hb.2]

lemma w_nonneg (Q D : Finset ℕ) : 0 ≤ w Q D := mul_nonneg
  (Finset.prod_nonneg fun q _ => by positivity) (Finset.prod_nonneg fun q _ => one_sub_nonneg' q)

lemma sep_of_le (L : ℕ) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpL : p ≤ L) (hqL : q ≤ L)
    (hpq : p < q) :
    (1 + 1 / (L : ℝ) ^ 2) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
  have hpL' : (p : ℝ) ≤ L := by exact_mod_cast hpL
  have hqL' : (q : ℝ) ≤ L := by exact_mod_cast hqL
  have hpq' : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
  have hη0 : 0 ≤ 1 / (L : ℝ) ^ 2 := by positivity
  have h1 : 1 / (L : ℝ) ^ 2 * (1 - 1 / (p : ℝ)) ≤ 1 / (L : ℝ) ^ 2 := by
    have : 0 ≤ 1 / (p : ℝ) := by positivity
    nlinarith
  have h2 : 1 / (L : ℝ) ^ 2 ≤ 1 / ((p : ℝ) * q) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h3 : 1 / ((p : ℝ) * q) ≤ 1 / (p : ℝ) - 1 / q := by
    rw [div_sub_div _ _ (by positivity) (by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  nlinarith

lemma diff_le (Q P : Finset ℕ) (hQp : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q) (c η δ ε : ℝ)
    (hc0 : 0 ≤ c) (hη0 : 0 ≤ η) (hδ1 : δ < 1) (hε : 0 < ε)
    (hcc : c ≤ c / (1 - δ)) (hcη : c / (1 - δ) ≤ c * (1 + η))
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p < q → (1 + η) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ))
    (hL : 6 / ε ≤ ∑ p ∈ P, 1 / (p : ℝ)) :
    (∑ D ∈ Q.powerset.filter (fun D => g D < c / (1 - δ)), w Q D) -
      (∑ D ∈ Q.powerset.filter (fun D => g D < c), w Q D) ≤ ε / 3 := by
  have e : (∑ D ∈ Q.powerset.filter (fun D => g D < c / (1 - δ)), w Q D) =
      (∑ D ∈ Q.powerset.filter (fun D => g D < c), w Q D) +
      ∑ D ∈ (Q.powerset.filter (fun D => g D < c / (1 - δ))).filter
        (fun D => ¬ g D < c), w Q D := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun D => g D < c), Finset.filter_filter]
    congr 2
    ext D
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, lt_of_lt_of_le h3 hcc, h3⟩
  have hsub : (Q.powerset.filter (fun D => g D < c / (1 - δ))).filter (fun D => ¬ g D < c) ⊆
      Q.powerset.filter (fun D => c ≤ g D ∧ g D < c * (1 + η)) := by
    intro D hD
    simp only [Finset.mem_filter] at hD ⊢
    exact ⟨hD.1.1, le_of_not_gt hD.2, lt_of_lt_of_le hD.1.2 hcη⟩
  have ha := anti Q P hQp hPQ c η hη0 hsep
  have hW := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D _ _ => w_nonneg Q D)
  have hWnn : 0 ≤ ∑ D ∈ Q.powerset.filter (fun D => c ≤ g D ∧ g D < c * (1 + η)), w Q D :=
    Finset.sum_nonneg fun D _ => w_nonneg Q D
  have : (∑ D ∈ Q.powerset.filter (fun D => c ≤ g D ∧ g D < c * (1 + η)), w Q D) ≤ ε / 3 := by
    have h7 : (∑ D ∈ Q.powerset.filter (fun D => c ≤ g D ∧ g D < c * (1 + η)), w Q D) *
        (6 / ε) ≤ 2 := le_trans (mul_le_mul_of_nonneg_left hL hWnn) ha
    rw [mul_div_assoc', div_le_iff₀ hε] at h7
    linarith
  linarith

lemma choose_params (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∃ δ : ℝ, 1 ≤ K ∧ 0 < δ ∧ δ < 1 ∧ 3 / ε ≤ K * δ ∧ ∀ c : ℝ, 0 ≤ c →
      (∑ D ∈ (QK K).powerset.filter (fun D => g D < c / (1 - δ)), w (QK K) D) -
      (∑ D ∈ (QK K).powerset.filter (fun D => g D < c), w (QK K) D) ≤ ε / 3 := by
  obtain ⟨L, hL⟩ := diverge (6 / ε)
  have h6 : 0 < 6 / ε := by positivity
  have hL1 : 1 ≤ L := by
    by_contra h
    have : L = 0 := by omega
    subst this
    simp at hL
    linarith
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / (L : ℝ) ^ 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  obtain ⟨K0, hK0⟩ := exists_nat_gt (3 / (δ * ε))
  obtain ⟨K, hK⟩ : ∃ K, K = max (max K0 L) 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := hK ▸ le_max_right _ _
  have hLK : L ≤ K := hK ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hK0K : (K0 : ℝ) ≤ K := by
    exact_mod_cast (hK ▸ le_trans (le_max_left _ _) (le_max_left _ _) : K0 ≤ K)
  have hPQ : (Finset.range L).filter Nat.Prime ⊆ QK K := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    simp only [QK, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  have hsep : ∀ p ∈ (Finset.range L).filter Nat.Prime, ∀ q ∈ (Finset.range L).filter Nat.Prime,
      p < q → (1 + η) * (1 - 1 / (p : ℝ)) ≤ 1 - 1 / (q : ℝ) := by
    intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_range] at hp hq
    rw [hη]
    exact sep_of_le L p q hp.2 hq.2 hp.1.le hq.1.le hpq
  have hKδ : 3 / ε ≤ K * δ := by
    have : 3 / (δ * ε) < K := lt_of_lt_of_le hK0 hK0K
    rw [div_lt_iff₀ (by positivity)] at this
    rw [div_le_iff₀ hε]; nlinarith
  refine ⟨K,δ,hK1,hδ0,hδ1,hKδ,?_⟩
  intro c hc0
  have hcc : c ≤ c / (1 - δ) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hδ0.le hc0]
  have hcη : c / (1 - δ) ≤ c * (1 + η) := by
    rw [div_le_iff₀ (by linarith)]
    have : 1 ≤ (1 + η) * (1 - δ) := by rw [hδ]; nlinarith
    calc c = c * 1 := by ring
      _ ≤ c * ((1 + η) * (1 - δ)) := mul_le_mul_of_nonneg_left this hc0
      _ = c * (1 + η) * (1 - δ) := by ring
  exact diff_le (QK K) _ (QK_prime K) hPQ c η δ ε hc0 hη0.le hδ1 hε hcc hcη hsep hL

lemma eventually_close (c : ℝ) (ε : ℝ) (hε : 0 < ε) (K : ℕ) (δ : ℝ) (hK1 : 1 ≤ K)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hKδ : 3 / ε ≤ K * δ)
    (hd : (∑ D ∈ (QK K).powerset.filter (fun D => g D < c / (1 - δ)), w (QK K) D) -
      (∑ D ∈ (QK K).powerset.filter (fun D => g D < c), w (QK K) D) ≤ ε / 3) :
    ∀ᶠ N in atTop, |(cnt {n : ℕ | (Nat.totient n : ℝ) < c * n} N : ℝ) / N -
      ∑ D ∈ (QK K).powerset.filter (fun D => g D < c), w (QK K) D| ≤ ε := by
  have h1 := (hasDensity_iff _ _).1 (density_pred (QK K) (QK_prime K) (fun D => g D < c))
  have h2 := (hasDensity_iff _ _).1
    (density_pred (QK K) (QK_prime K) (fun D => g D < c / (1 - δ)))
  have e1 := (tendsto_order.1 h1).1 _ (sub_lt_self _ (by positivity : 0 < ε / 3))
  have e2 := (tendsto_order.1 h2).2 _ (lt_add_of_pos_right _ (by positivity : 0 < ε / 6))
  obtain ⟨N3, hN3⟩ := exists_nat_gt (3 / ε)
  filter_upwards [e1, e2, eventually_ge_atTop (N3 + 1)] with N hN1 hN2 hN3'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have c1 : cnt {n | g (status (QK K) n) < c} N ≤
      cnt {n : ℕ | (Nat.totient n : ℝ) < c * n} N + 1 := by
    have hsub : {n | g (status (QK K) n) < c} ⊆ {n : ℕ | (Nat.totient n : ℝ) < c * n} ∪ {0} := by
      intro n hn
      by_cases h0 : n = 0
      · exact Or.inr h0
      · exact Or.inl (lower_incl h0 K hn)
    have := (cnt_mono hsub N).trans (cnt_union_le _ {0} N)
    have := cnt_zero_le N
    omega
  have c2 : cnt {n : ℕ | (Nat.totient n : ℝ) < c * n} N ≤
      cnt {n | g (status (QK K) n) < c / (1 - δ)} N + cnt {n | δ < hK K n} N := by
    have hsub : {n : ℕ | (Nat.totient n : ℝ) < c * n} ⊆
        {n | g (status (QK K) n) < c / (1 - δ)} ∪ {n | δ < hK K n} := by
      intro n hn
      by_cases hb : δ < hK K n
      · exact Or.inr hb
      · exact Or.inl (upper_incl K hδ1 hn (le_of_not_gt hb))
    exact (cnt_mono hsub N).trans (cnt_union_le _ _ N)
  have c3 := cnt_bad K N hK1 hδ0
  have c3' : (cnt {n | δ < hK K n} N : ℝ) / N ≤ ε / 3 := by
    rw [div_le_iff₀ hNpos]
    have hKδ0 : 0 < (K : ℝ) * δ := by
      have : (0 : ℝ) < K := by exact_mod_cast hK1
      positivity
    calc (cnt {n | δ < hK K n} N : ℝ) ≤ N / (K * δ) := c3
      _ ≤ ε / 3 * N := by
        rw [div_le_iff₀ hKδ0]
        have h4 : ε / 3 * (3 / ε) = 1 := by field_simp
        have h5 : 1 ≤ ε / 3 * (K * δ) := h4 ▸ mul_le_mul_of_nonneg_left hKδ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left h5 hNpos.le]
  have hinvN : 1 / (N : ℝ) ≤ ε / 3 := by
    have : 3 / ε < N := lt_of_lt_of_le hN3 (by exact_mod_cast (show N3 ≤ N by omega))
    rw [div_le_iff₀ hNpos]
    rw [div_lt_iff₀ hε] at this
    linarith
  have c1' : (cnt {n | g (status (QK K) n) < c} N : ℝ) / N ≤
      cnt {n : ℕ | (Nat.totient n : ℝ) < c * n} N / N + 1 / N := by
    rw [← add_div]; apply div_le_div_of_nonneg_right _ hNpos.le; exact_mod_cast c1
  have c2' : (cnt {n : ℕ | (Nat.totient n : ℝ) < c * n} N : ℝ) / N ≤
      cnt {n | g (status (QK K) n) < c / (1 - δ)} N / N + cnt {n | δ < hK K n} N / N := by
    rw [← add_div]; apply div_le_div_of_nonneg_right _ hNpos.le; exact_mod_cast c2
  rw [abs_le]
  constructor <;> linarith

end OMA50


namespace OMA50
open Filter Set Topology Finset
open scoped Classical

noncomputable def F (K : ℕ) (c : ℝ) := ∑ D ∈ (QK K).powerset.filter (fun D => g D < c), w (QK K) D

lemma monoF (K : ℕ) : Monotone (F K) := by
  intro a b hab
  apply sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => w_nonneg _ _)
  intro D hD
  exact mem_filter.mpr ⟨(mem_filter.mp hD).1, (mem_filter.mp hD).2.trans_le hab⟩

lemma near_zero (K : ℕ) : ∃ t : ℝ, 0<t ∧ ∀ c : ℝ, c<t → F K c=0 := by
  classical
  let T := (QK K).powerset.image g
  have hT : T.Nonempty := Finset.Nonempty.image ((QK K).powerset_nonempty) _
  let t := T.min' hT
  obtain ⟨D,hD,he⟩ := mem_image.mp (min'_mem T hT)
  have hp : 0<t := by
    change 0<T.min' hT
    rw [← he]
    exact prod_pos (fun p hp => sub_pos.mpr ((div_lt_one (by exact_mod_cast
      (QK_prime K p ((mem_powerset.mp hD) hp)).pos : 0 < (p:ℝ))).mpr
        (by exact_mod_cast (QK_prime K p ((mem_powerset.mp hD) hp)).one_lt)))
  refine ⟨t,hp,fun c hc => ?_⟩
  have empty : (QK K).powerset.filter (fun D => g D < c) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro D h
    obtain ⟨hD,hg⟩ := mem_filter.mp h
    have lo : t ≤ g D := min'_le _ _ (mem_image_of_mem g hD)
    linarith
  simp [F,empty]

theorem cont {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f) :
    ContinuousOn f (Set.Icc 0 1) := by
  classical
  intro c hc
  rw [Metric.continuousWithinAt_iff]
  intro e he
  let h := e/8
  have hh : 0<h := by dsimp [h]; positivity
  obtain ⟨K,δ,hK,hδ,hδ1,hKδ,hd⟩ := choose_params h hh
  change ∀ c : ℝ, 0≤c → F K (c/(1-δ)) - F K c ≤ h/3 at hd
  have approx (x : ℝ) (hx : x∈Set.Icc 0 1) : |f x-F K x| ≤ h := by
    have tending := (hasDensity_iff _ _).mp (hf x hx)
    exact le_of_tendsto ((tending.sub_const (F K x)).abs)
      (eventually_close x h hh K δ hK hδ hδ1 hKδ (hd x hx.1))
  have conclude {x : ℝ} (hx : x∈Set.Icc 0 1) (d : |F K x-F K c| ≤ h) : dist (f x) (f c)<e := by
    rw [Real.dist_eq,abs_lt]
    obtain ⟨a,b⟩ := abs_le.mp (approx x hx)
    obtain ⟨a',b'⟩ := abs_le.mp (approx c hc)
    obtain ⟨a'',b''⟩ := abs_le.mp d
    dsimp [h] at *; constructor <;> linarith
  rcases hc.1.eq_or_lt with e0|hp
  · subst c
    obtain ⟨t,ht,hn⟩ := near_zero K
    refine ⟨t,ht,fun x hx hdist => conclude hx ?_⟩
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hx.1] at hdist
    simp only [hn x hdist,hn 0 ht,sub_self,abs_zero]
    exact hh.le
  have h1 : 0<1-δ := by linarith
  have less : c*(1-δ)<c := by nlinarith [mul_pos hp hδ]
  have greater : c<c/(1-δ) := (lt_div_iff₀ h1).mpr less
  refine ⟨min (c-c*(1-δ)) (c/(1-δ)-c),lt_min (by linarith) (by linarith),?_⟩
  intro x hx hdist
  apply conclude hx
  rw [Real.dist_eq,abs_lt] at hdist
  have hn := min_le_left (c-c*(1-δ)) (c/(1-δ)-c)
  have hn' := min_le_right (c-c*(1-δ)) (c/(1-δ)-c)
  have hlow := monoF K (show c*(1-δ)≤x by linarith [hdist.1])
  have hhigh := monoF K (show x≤c/(1-δ) by linarith [hdist.2])
  have hdl := hd (c*(1-δ)) (mul_nonneg hp.le h1.le)
  rw [mul_div_cancel_right₀ _ h1.ne'] at hdl
  have hdh := hd c hp.le
  rw [abs_le]; constructor <;> linarith

end OMA50

theorem OMA.solution : OMA.R_Erdos50_erdos_50_singular_R1.H1 := fun _ hf => OMA50.cont hf
