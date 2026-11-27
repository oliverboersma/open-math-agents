import OMAReductions.R_Erdos1162_erdos_1162_variants_pyber_R1

/-!
For Ming Kao's Pyber reduction (PR 4676).
The Sylow subgroup count, factorial valuation estimate and primorial argument
are adapted from Michael Bisbjerg's proof of Pyber's theorem (PR 4693).
Here the contribution of primes below 128 is computed exactly over the
rationals. A telescoping dyadic bound treats all larger primes.
Together these give a uniform bound for every symmetric group.
-/

namespace OMA

theorem exists_gen_list {G : Type*} [Group G] (H : Subgroup G) [Finite H] (k : ℕ) :
    ∃ l : List G, l.length = k ∧ (∀ x ∈ l, x ∈ H) ∧
      (Subgroup.closure {x | x ∈ l} = H ∨ 2 ^ k ≤ Nat.card (Subgroup.closure {x | x ∈ l})) := by
  induction k with
  | zero =>
    refine ⟨[], rfl, by simp, Or.inr ?_⟩
    simp
  | succ k ih =>
    obtain ⟨l, hl, hmem, h⟩ := ih
    have hle : Subgroup.closure {x | x ∈ l} ≤ H := (Subgroup.closure_le H).2 fun x hx => hmem x hx
    by_cases hC : Subgroup.closure {x | x ∈ l} = H
    · refine ⟨1 :: l, by simp [hl], ?_, Or.inl ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact H.one_mem
        · exact hmem x hx
      · apply le_antisymm
        · refine (Subgroup.closure_le H).2 fun x hx => ?_
          rcases List.mem_cons.1 hx with rfl | hx
          · exact H.one_mem
          · exact hmem x hx
        · rw [← hC]
          exact Subgroup.closure_mono fun x hx => List.mem_cons_of_mem _ hx
    · have h2 : 2 ^ k ≤ Nat.card (Subgroup.closure {x | x ∈ l}) := h.resolve_left hC
      obtain ⟨x, hxH, hxC⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hC)
      have hmem' : ∀ y ∈ x :: l, y ∈ H := by
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hxH
        · exact hmem y hy
      have hle' : Subgroup.closure {y | y ∈ x :: l} ≤ H :=
        (Subgroup.closure_le H).2 fun y hy => hmem' y hy
      have hCC : Subgroup.closure {y | y ∈ l} ≤ Subgroup.closure {y | y ∈ x :: l} :=
        Subgroup.closure_mono fun y hy => List.mem_cons_of_mem _ hy
      have : Finite (Subgroup.closure {y | y ∈ x :: l}) :=
        Finite.of_injective (Subgroup.inclusion hle') (Subgroup.inclusion_injective hle')
      refine ⟨x :: l, by simp [hl], hmem', Or.inr ?_⟩
      obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hCC
      have hpos : 0 < Nat.card (Subgroup.closure {y | y ∈ x :: l}) := Nat.card_pos
      have hm2 : 2 ≤ m := by
        rcases Nat.lt_or_ge m 2 with hlt | hge
        · exfalso
          interval_cases m
          · rw [hm, Nat.mul_zero] at hpos
            exact lt_irrefl _ hpos
          · have : Subgroup.closure {y | y ∈ l} = Subgroup.closure {y | y ∈ x :: l} :=
              Subgroup.eq_of_le_of_card_ge hCC (by rw [hm]; simp)
            apply hxC
            rw [this]
            exact Subgroup.subset_closure (List.mem_cons_self)
        · exact hge
      calc 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        _ ≤ Nat.card (Subgroup.closure {y | y ∈ l}) * m := Nat.mul_le_mul h2 hm2
        _ = _ := hm.symm

theorem exists_gen_fun {G : Type*} [Group G] (H P : Subgroup G) [Finite P] (hHP : H ≤ P)
    (L : ℕ) (hL : Nat.card P < 2 ^ L) :
    ∃ v : Fin L → P, Subgroup.closure (Set.range fun i => (v i : G)) = H := by
  have : Finite H := Finite.of_injective (Subgroup.inclusion hHP) (Subgroup.inclusion_injective hHP)
  obtain ⟨l, hl, hmem, h⟩ := exists_gen_list H L
  have hle : Subgroup.closure {x | x ∈ l} ≤ H := (Subgroup.closure_le H).2 fun x hx => hmem x hx
  have hcl : Subgroup.closure {x | x ∈ l} = H := by
    rcases h with h | h
    · exact h
    · exfalso
      have h1 : Nat.card (Subgroup.closure {x | x ∈ l}) ≤ Nat.card P :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le (hle.trans hHP))
      omega
  refine ⟨fun i => ⟨l.get (i.cast hl.symm), hHP (hmem _ (List.get_mem _ _))⟩, ?_⟩
  rw [← hcl]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, rfl⟩
    exact List.get_mem _ _
  · intro hx
    obtain ⟨i, rfl⟩ := List.get_of_mem hx
    exact ⟨i.cast hl, by simp⟩

/-- number of `p`-subgroups of a finite group -/
theorem card_pgroups_le {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (L : ℕ)
    (hL : p ^ (Nat.card G).factorization p < 2 ^ L) :
    Nat.card {Q : Subgroup G // IsPGroup p Q} ≤
      Nat.card G * (p ^ (Nat.card G).factorization p) ^ L := by
  classical
  let P₀ : Sylow p G := default
  have hP₀ : Nat.card (P₀ : Subgroup G) = p ^ (Nat.card G).factorization p := P₀.card_eq_multiplicity
  have key : ∀ Q : {Q : Subgroup G // IsPGroup p Q}, ∃ gv : G × (Fin L → (P₀ : Subgroup G)),
      (Subgroup.closure (Set.range fun i => ((gv.2 i : G)))).map
        (MulAut.conj gv.1).toMonoidHom = Q.1 := by
    rintro ⟨Q, hQ⟩
    obtain ⟨P, hP⟩ := hQ.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
    have hQ' : Q.map (MulAut.conj g⁻¹).toMonoidHom ≤ (P₀ : Subgroup G) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxP : x ∈ ((g • P₀ : Sylow p G) : Subgroup G) := by rw [hg]; exact hP hx
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxP
      simpa [MulAut.smul_def, MulAut.conj_apply] using hxP
    obtain ⟨v, hv⟩ := exists_gen_fun _ (P₀ : Subgroup G) hQ' L (by rw [hP₀]; exact hL)
    refine ⟨(g, v), ?_⟩
    simp only
    rw [hv, Subgroup.map_map]
    have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [this, Subgroup.map_id]
  choose c hc using key
  have hinj : Function.Injective c := by
    intro Q Q' h
    apply Subtype.ext
    rw [← hc Q, ← hc Q', h]
  calc Nat.card {Q : Subgroup G // IsPGroup p Q} ≤ Nat.card (G × (Fin L → (P₀ : Subgroup G))) :=
        Nat.card_le_card_of_injective c hinj
    _ = Nat.card G * (p ^ (Nat.card G).factorization p) ^ L := by
        rw [Nat.card_prod, Nat.card_fun, hP₀, Nat.card_fin]

theorem eq_iSup_of_card {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (Q : (Nat.card G).primeFactors → Subgroup G) (hle : ∀ p, Q p ≤ H)
    (hcard : ∀ p, Nat.card (Q p) = p.1 ^ (Nat.card H).factorization p.1) :
    (⨆ p, Q p) = H := by
  have hK : (⨆ p, Q p) ≤ H := iSup_le hle
  refine Subgroup.eq_of_le_of_card_ge hK (Nat.le_of_dvd Nat.card_pos ?_)
  rw [← Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
  intro p hp
  by_cases hpS : p ∈ (Nat.card G).primeFactors
  · rw [← hp.pow_dvd_iff_le_factorization Nat.card_pos.ne', ← hcard ⟨p, hpS⟩]
    exact Subgroup.card_dvd_of_le (le_iSup Q ⟨p, hpS⟩)
  · have : ¬ p ∣ Nat.card H := fun h =>
      hpS (Nat.mem_primeFactors.2 ⟨hp, h.trans (Subgroup.card_subgroup_dvd_card H),
        Nat.card_pos.ne'⟩)
    rw [Nat.factorization_eq_zero_of_not_dvd this]
    exact Nat.zero_le _

theorem card_subgroup_le {G : Type*} [Group G] [Finite G] (L : ℕ → ℕ)
    (hL : ∀ p ∈ (Nat.card G).primeFactors, p ^ (Nat.card G).factorization p < 2 ^ L p) :
    Nat.card (Subgroup G) ≤
      ∏ p ∈ (Nat.card G).primeFactors, (Nat.card G * (p ^ (Nat.card G).factorization p) ^ L p) := by
  classical
  have key : ∀ (H : Subgroup G) (p : (Nat.card G).primeFactors),
      ∃ Q : {Q : Subgroup G // IsPGroup p.1 Q}, Q.1 ≤ H ∧
        Nat.card Q.1 = p.1 ^ (Nat.card H).factorization p.1 := by
    intro H p
    haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    let P : Sylow p.1 H := default
    refine ⟨⟨(P : Subgroup H).map H.subtype, P.isPGroup'.map H.subtype⟩, ?_, ?_⟩
    · exact Subgroup.map_subtype_le _
    · rw [← P.card_eq_multiplicity]
      exact Nat.card_congr ((P : Subgroup H).equivMapOfInjective H.subtype
        H.subtype_injective).symm.toEquiv
  choose Φ hΦle hΦcard using key
  have hinj : Function.Injective Φ := by
    intro H H' h
    rw [← eq_iSup_of_card H (fun p => (Φ H p).1) (hΦle H) (hΦcard H),
      ← eq_iSup_of_card H' (fun p => (Φ H' p).1) (hΦle H') (hΦcard H'), h]
  calc Nat.card (Subgroup G)
      ≤ Nat.card ((p : (Nat.card G).primeFactors) → {Q : Subgroup G // IsPGroup p.1 Q}) :=
        Nat.card_le_card_of_injective Φ hinj
    _ = ∏ p : (Nat.card G).primeFactors, Nat.card {Q : Subgroup G // IsPGroup p.1 Q} :=
        Nat.card_pi
    _ ≤ ∏ p : (Nat.card G).primeFactors,
          (Nat.card G * (p.1 ^ (Nat.card G).factorization p.1) ^ L p.1) := by
        refine Finset.prod_le_prod' fun p _ => ?_
        haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
        exact card_pgroups_le p.1 (L p.1) (hL p.1 p.2)
    _ = _ := Finset.prod_coe_sort (Nat.card G).primeFactors
        (fun p => Nat.card G * (p ^ (Nat.card G).factorization p) ^ L p)

theorem fact_pow_card_le (n : ℕ) :
    (n.factorial) ^ (n.factorial).primeFactors.card ≤ 2 ^ (6 * n ^ 2) := by
  classical
  set s := Nat.sqrt n with hs
  set S := (n.factorial).primeFactors with hS
  have hSp : ∀ p ∈ S, p.Prime ∧ p ≤ n := by
    intro p hp
    have h := Nat.mem_primeFactors.1 hp
    exact ⟨h.1, (h.1.dvd_factorial).1 h.2.1⟩
  have h1 : s ^ 2 ≤ n := Nat.sqrt_le' n
  have h2 : n < (s + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have h3 : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  have hN : n.factorial ≤ ((s + 1) ^ 2) ^ n :=
    (Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left h2.le n)
  set b := (S.filter (fun p => s < p)).card with hb
  have hcard : S.card ≤ s + b := by
    have h0 : (S.filter (fun p => s < p)).card + (S.filter (fun p => ¬ s < p)).card = S.card :=
      Finset.card_filter_add_card_filter_not _
    have h' : (S.filter (fun p => ¬ s < p)).card ≤ s := by
      calc (S.filter (fun p => ¬ s < p)).card ≤ (Finset.Icc 1 s).card := by
            apply Finset.card_le_card
            intro p hp
            rw [Finset.mem_filter] at hp
            rw [Finset.mem_Icc]
            exact ⟨(hSp p hp.1).1.one_le, not_lt.1 hp.2⟩
        _ = s := by simp
    omega
  have hB : (s + 1) ^ b ≤ 4 ^ n := by
    calc (s + 1) ^ b ≤ ∏ p ∈ S.filter (fun p => s < p), p := by
          apply Finset.pow_card_le_prod
          intro p hp
          rw [Finset.mem_filter] at hp
          omega
      _ ≤ primorial n := by
          unfold primorial
          apply Finset.prod_le_prod_of_subset_of_one_le'
          · intro p hp
            rw [Finset.mem_filter] at hp
            rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨Nat.lt_succ_of_le (hSp p hp.1).2, (hSp p hp.1).1⟩
          · intro p hp _
            exact (Finset.mem_filter.1 hp).2.one_le
      _ ≤ 4 ^ n := primorial_le_four_pow n
  have hA1 : n.factorial ^ s ≤ 2 ^ (2 * n ^ 2) := by
    calc n.factorial ^ s ≤ (((2 ^ s) ^ 2) ^ n) ^ s :=
          Nat.pow_le_pow_left (hN.trans (Nat.pow_le_pow_left (Nat.pow_le_pow_left h3 2) n)) s
      _ = 2 ^ (s * 2 * n * s) := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ ≤ 2 ^ (2 * n ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hB1 : n.factorial ^ b ≤ 2 ^ (4 * n ^ 2) := by
    calc n.factorial ^ b ≤ (((s + 1) ^ 2) ^ n) ^ b := Nat.pow_le_pow_left hN b
      _ = ((s + 1) ^ b) ^ (2 * n) := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ ≤ (4 ^ n) ^ (2 * n) := Nat.pow_le_pow_left hB _
      _ = 2 ^ (4 * n ^ 2) := by
          have : (4 : ℕ) = 2 ^ 2 := by norm_num
          rw [this, ← pow_mul, ← pow_mul]
          congr 1
          ring
  calc n.factorial ^ S.card ≤ n.factorial ^ (s + b) :=
        Nat.pow_le_pow_right (Nat.factorial_pos n) hcard
    _ = n.factorial ^ s * n.factorial ^ b := pow_add _ _ _
    _ ≤ 2 ^ (2 * n ^ 2) * 2 ^ (4 * n ^ 2) := Nat.mul_le_mul hA1 hB1
    _ = 2 ^ (6 * n ^ 2) := by
        rw [← pow_add]
        congr 1
        ring

private noncomputable def primeWeight (p : ℕ) : ℝ :=
  ((Nat.log 2 p : ℝ) + 1) ^ 2 / ((p : ℝ) - 1) ^ 2

private noncomputable def tailBound (j : ℕ) : ℝ :=
  17 / 8 * ((j : ℝ) ^ 2 + 4 * j + 6) / 2 ^ j

private theorem dyadic_block {j : ℕ} (hj : 7 ≤ j) :
    ∑ p ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), primeWeight p ≤
      tailBound j - tailBound (j + 1) := by
  have hx : 0 < (2 : ℝ) ^ j := by positivity
  have h128 : (128 : ℝ) ≤ 2 ^ j := by
    calc (128 : ℝ) = 2 ^ 7 := by norm_num
         _ ≤ _ := pow_le_pow_right₀ (by norm_num) hj
  let w := (((j : ℝ) + 1) / (2 ^ j)) ^ 2
  have hterm : ∀ p ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), primeWeight p ≤ 17 / 16 * w := by
    intro p hp
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hp
    have hp' : (2 : ℝ) ^ j ≤ (p : ℝ) := by exact_mod_cast hlo
    have hd : 0 < (p : ℝ) - 1 := by linarith
    have hd' : (2 : ℝ) ^ j ≤ 65 / 64 * ((p : ℝ) - 1) := by linarith
    have he : ((j : ℝ) + 1) / ((p : ℝ) - 1) ≤
        65 / 64 * (((j : ℝ) + 1) / 2 ^ j) := by
      rw [div_le_iff₀ hd]
      field_simp [hx.ne']
      nlinarith [mul_le_mul_of_nonneg_left hd' (show 0 ≤ (j : ℝ) + 1 by positivity)]
    have hs := pow_le_pow_left₀ (show 0 ≤ ((j : ℝ) + 1) / ((p : ℝ) - 1) from div_nonneg (by positivity) hd.le) he 2
    unfold primeWeight
    rw [Nat.log_eq_of_pow_le_of_lt_pow hlo hhi, ← div_pow]
    dsimp [w]
    nlinarith [sq_nonneg (((j : ℝ) + 1) / 2 ^ j)]
  have hc : (Finset.Ico (2 ^ j) (2 ^ (j + 1))).card = 2 ^ j := by
    rw [Nat.card_Ico, pow_succ]
    omega
  calc
    _ ≤ _ := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = tailBound j - tailBound (j + 1) := by
      rw [hc, nsmul_eq_mul]
      dsimp [w, tailBound]
      push_cast
      rw [pow_succ (2 : ℝ) j]
      field_simp
      ring

private theorem dyadic_tail (J : ℕ) :
    ∑ p ∈ Finset.Ico 128 (2 ^ (7 + J)), primeWeight p ≤
      tailBound 7 - tailBound (7 + J) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    have hlo : 128 ≤ 2 ^ (7 + J) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 7 ≤ 7 + J by omega)
    have hhi : 2 ^ (7 + J) ≤ 2 ^ (7 + J + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [← Nat.add_assoc, ← Finset.sum_Ico_consecutive _ hlo hhi]
    linarith [dyadic_block (show 7 ≤ 7 + J by omega)]

set_option maxRecDepth 10000 in
private theorem small_primes :
    ∑ p ∈ (Finset.range 128).filter Nat.Prime, primeWeight p ≤ 33 / 5 := by
  have h : ∑ p ∈ (Finset.range 128).filter Nat.Prime,
      ((Nat.log 2 p : ℚ) + 1) ^ 2 / ((p : ℚ) - 1) ^ 2 ≤ 33 / 5 := by decide +kernel
  have hc := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hc
  exact hc

private theorem prime_series_bound (n : ℕ) :
    ∑ p ∈ n.factorial.primeFactors, primeWeight p ≤ 8 := by
  let low := (Finset.range 128).filter Nat.Prime
  let high := Finset.Ico 128 (2 ^ (7 + n))
  have hd : Disjoint low high := by
    refine Finset.disjoint_left.mpr fun p hp hq => ?_
    exact (Finset.mem_range.mp (Finset.mem_filter.mp hp).1).not_ge (Finset.mem_Ico.mp hq).1
  have hsub : n.factorial.primeFactors ⊆ low ∪ high := by
    intro p hp
    have ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    by_cases h : p < 128
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hprime⟩)
    · apply Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, ?_⟩)
      exact ((hprime.dvd_factorial.mp hdvd).trans_lt (Nat.lt_two_pow_self (n := n))).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := primeWeight) hsub
    (fun p _ _ => by unfold primeWeight; positivity)
  rw [Finset.sum_union hd] at h
  have ht := dyadic_tail n
  have hn : 0 ≤ tailBound (7 + n) := by unfold tailBound; positivity
  have h7 : tailBound 7 ≤ 7 / 5 := by norm_num [tailBound]
  change (∑ p ∈ n.factorial.primeFactors, primeWeight p) ≤
    (∑ p ∈ (Finset.range 128).filter Nat.Prime, primeWeight p) +
      ∑ p ∈ Finset.Ico 128 (2 ^ (7 + n)), primeWeight p at h
  linarith [small_primes]

theorem exp_bound (n : ℕ) :
    ((∑ p ∈ (n.factorial).primeFactors,
      ((Nat.log 2 p + 1) * (n.factorial).factorization p) *
        ((Nat.log 2 p + 1) * (n.factorial).factorization p + 1) : ℕ) : ℝ) ≤ 12 * (n : ℝ) ^ 2 := by
  push_cast
  have hterm : ∀ p ∈ (n.factorial).primeFactors,
      (((Nat.log 2 p : ℝ) + 1) * ((n.factorial).factorization p : ℝ)) *
        (((Nat.log 2 p : ℝ) + 1) * ((n.factorial).factorization p : ℝ) + 1) ≤
      (3 / 2) * (n : ℝ) ^ 2 * (((Nat.log 2 p : ℝ) + 1) ^ 2 / ((p : ℝ) - 1) ^ 2) := by
    intro p hp
    have h := Nat.mem_primeFactors.1 hp
    haveI : Fact p.Prime := ⟨h.1⟩
    have hv : (p - 1) * (n.factorial).factorization p ≤ n := by
      rw [Nat.factorization_def _ h.1, sub_one_mul_padicValNat_factorial]
      exact Nat.sub_le _ _
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.1.two_le
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hvR : ((p : ℝ) - 1) * ((n.factorial).factorization p : ℝ) ≤ (n : ℝ) := by
      have : (((p - 1) * (n.factorial).factorization p : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hv
      rw [Nat.cast_mul, Nat.cast_sub h.1.one_le] at this
      simpa using this
    set v : ℝ := ((n.factorial).factorization p : ℝ) with hvdef
    set j : ℝ := (Nat.log 2 p : ℝ) + 1 with hj
    have hv0 : 0 ≤ v := Nat.cast_nonneg _
    have hj0 : 0 ≤ j := by positivity
    have hvle : v ≤ (n : ℝ) / ((p : ℝ) - 1) := by
      rw [le_div_iff₀ hp1]
      linarith
    have hv2 : v ^ 2 ≤ (n : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2 := by
      rw [← div_pow]
      exact pow_le_pow_left₀ hv0 hvle 2
    have hlog : 1 ≤ Nat.log 2 p :=
      Nat.le_log_of_pow_le (by decide) (by simpa using h.1.two_le)
    have hvone : 1 ≤ v := by
      change (1 : ℝ) ≤ (n.factorial.factorization p : ℝ)
      exact_mod_cast (show 1 ≤ n.factorial.factorization p from
        h.1.factorization_pos_of_dvd n.factorial_ne_zero h.2.1)
    have hjtwo : 2 ≤ j := by
      dsimp [j]
      exact_mod_cast (show 2 ≤ Nat.log 2 p + 1 by omega)
    have hjv : 2 ≤ j * v := by
      simpa using mul_le_mul hjtwo hvone (by norm_num : (0 : ℝ) ≤ 1) hj0
    calc j * v * (j * v + 1) = (j * v) ^ 2 + j * v := by ring
      _ ≤ (3 / 2) * (j * v) ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hjv) (mul_nonneg hj0 hv0)]
      _ = (3 / 2) * j ^ 2 * v ^ 2 := by ring
      _ ≤ (3 / 2) * j ^ 2 * ((n : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hv2 (by positivity)
      _ = (3 / 2) * (n : ℝ) ^ 2 * (j ^ 2 / ((p : ℝ) - 1) ^ 2) := by ring
  calc _ ≤ ∑ p ∈ (n.factorial).primeFactors,
        (3 / 2) * (n : ℝ) ^ 2 * (((Nat.log 2 p : ℝ) + 1) ^ 2 / ((p : ℝ) - 1) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = (3 / 2) * (n : ℝ) ^ 2 * ∑ p ∈ (n.factorial).primeFactors,
        (((Nat.log 2 p : ℝ) + 1) ^ 2 / ((p : ℝ) - 1) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (3 / 2) * (n : ℝ) ^ 2 * 8 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact prime_series_bound n
    _ = 12 * (n : ℝ) ^ 2 := by ring

theorem upper (n : ℕ) : Real.log (Erdos1162.f n) ≤ 18 * Real.log 2 * (n : ℝ) ^ 2 := by
  have hcard : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  set E : ℕ := ∑ p ∈ (n.factorial).primeFactors,
      ((Nat.log 2 p + 1) * (n.factorial).factorization p) *
        ((Nat.log 2 p + 1) * (n.factorial).factorization p + 1) with hE
  have hpow : ∀ p : ℕ, p ^ (n.factorial).factorization p ≤
      2 ^ ((Nat.log 2 p + 1) * (n.factorial).factorization p) := by
    intro p
    rw [pow_mul]
    exact Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by norm_num) p).le _
  have h1 := card_subgroup_le (G := Equiv.Perm (Fin n))
    (fun p => (Nat.log 2 p + 1) * (n.factorial).factorization p + 1) (by
      intro p _
      rw [hcard]
      exact lt_of_le_of_lt (hpow p) (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)))
  rw [hcard] at h1
  have h2 : Erdos1162.f n ≤ 2 ^ (6 * n ^ 2 + E) := by
    unfold Erdos1162.f
    calc _ ≤ _ := h1
      _ ≤ ∏ p ∈ (n.factorial).primeFactors, (n.factorial *
          2 ^ (((Nat.log 2 p + 1) * (n.factorial).factorization p) *
            ((Nat.log 2 p + 1) * (n.factorial).factorization p + 1))) := by
          refine Finset.prod_le_prod' fun p _ => Nat.mul_le_mul_left _ ?_
          rw [pow_mul]
          exact Nat.pow_le_pow_left (hpow p) _
      _ = n.factorial ^ (n.factorial).primeFactors.card * 2 ^ E := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
      _ ≤ 2 ^ (6 * n ^ 2) * 2 ^ E := Nat.mul_le_mul_right _ (fact_pow_card_le n)
      _ = 2 ^ (6 * n ^ 2 + E) := (pow_add _ _ _).symm
  have h3 : (Erdos1162.f n : ℝ) ≤ (2 : ℝ) ^ (6 * n ^ 2 + E) := by exact_mod_cast h2
  have hpos : (0 : ℝ) < Erdos1162.f n := by exact_mod_cast Erdos1162.f_pos n
  have h4 := Real.log_le_log hpos h3
  rw [Real.log_pow] at h4
  have h5 := exp_bound n
  rw [← hE] at h5
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  push_cast at h4
  nlinarith [mul_le_mul_of_nonneg_right h5 hlog2]

end OMA

theorem OMA.solution : OMA.R_Erdos1162_erdos_1162_variants_pyber_R1.H2 := by
  exact ⟨18 * Real.log 2, Filter.Eventually.of_forall OMA.upper⟩
