import OMAReductions.R_Erdos535_erdos_535_variants_first_open_case_R1

/-
Step `H2` of `Erdos535.erdos_535.R1`. Integers in one class (same exponents at all primes
`p ≤ t`) are coded by their rough prime-power layers `(p, i)` with `t < p`, `i < v_p(n)`,
padded with private elements up to `K`. Intersections of codes record the minimum exponents
at the rough primes, so equal intersections force equal gcds.
-/

namespace OMA.Erdos535FirstOpenCaseR1H2

def roughLayers (t n : ℕ) : Finset (ℕ × ℕ) :=
  (n.primeFactors.filter (t < ·)).biUnion fun p =>
    (Finset.range (n.factorization p)).map ⟨Prod.mk p, fun _ _ h => congrArg Prod.snd h⟩

@[simp] theorem memRoughLayers {t n p i : ℕ} :
    (p, i) ∈ roughLayers t n ↔ t < p ∧ i < n.factorization p := by
  simp only [roughLayers, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_map, Finset.mem_range]
  constructor
  · rintro ⟨q, ⟨_, ht⟩, j, hj, he⟩
    change (q, j) = (p, i) at he
    cases he
    exact ⟨ht, hj⟩
  · rintro ⟨ht, hi⟩
    refine ⟨p, ⟨?_, ht⟩, i, hi, rfl⟩
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega

theorem cardRoughLayers (t n : ℕ) :
    (roughLayers t n).card = ∑ p ∈ n.primeFactors.filter (t < ·), n.factorization p := by
  classical
  rw [roughLayers, Finset.card_biUnion]
  · simp
  · intro a _ b _ hab
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨p, i⟩ ha hb
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp ha
    obtain ⟨k, _, hk⟩ := Finset.mem_map.mp hb
    change (a, j) = (p, i) at hj
    change (b, k) = (p, i) at hk
    exact hab (congrArg Prod.fst (hj.trans hk.symm))

def padded (t K n : ℕ) : Finset ((ℕ × ℕ) ⊕ (ℕ × ℕ)) :=
  (roughLayers t n).disjSum
    ((Finset.range (K - (roughLayers t n).card)).map
      ⟨Prod.mk n, fun _ _ h => congrArg Prod.snd h⟩)

theorem cardPadded {t K n : ℕ} (h : (roughLayers t n).card ≤ K) :
    (padded t K n).card = K := by
  simp [padded, Nat.add_sub_of_le h]

theorem gcdEqOfIntersection {t K a b c d : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hac : ∀ p ≤ t, a.factorization p = c.factorization p)
    (hbd : ∀ p ≤ t, b.factorization p = d.factorization p)
    (hinter : padded t K a ∩ padded t K b = padded t K c ∩ padded t K d) :
    a.gcd b = c.gcd d := by
  have hab : a.gcd b ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha))
  have hcd : c.gcd d ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left d (Nat.pos_of_ne_zero hc))
  apply Nat.factorization_inj hab hcd
  ext p
  rw [Nat.factorization_gcd ha hb, Nat.factorization_gcd hc hd]
  change min (a.factorization p) (b.factorization p) = min (c.factorization p) (d.factorization p)
  by_cases hp : p ≤ t
  · rw [hac p hp, hbd p hp]
  have h (i : ℕ) : i < min (a.factorization p) (b.factorization p) ↔
      i < min (c.factorization p) (d.factorization p) := by
    simpa [padded, Nat.lt_of_not_ge hp, lt_min_iff] using
      (show Sum.inl (p, i) ∈ padded t K a ∩ padded t K b ↔
        Sum.inl (p, i) ∈ padded t K c ∩ padded t K d by rw [hinter])
  have := (h (min (a.factorization p) (b.factorization p))).mpr
  have := (h (min (c.factorization p) (d.factorization p))).mp
  omega

theorem factorizationLeLog {n N p : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    n.factorization p ≤ Nat.log 2 N := by
  by_cases hzero : n.factorization p = 0
  · simp [hzero]
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hzero)
  apply Nat.le_log_of_pow_le (by decide : 1 < 2)
  exact ((Nat.pow_le_pow_left hp.two_le _).trans
    (Nat.le_of_dvd hn (Nat.ordProj_dvd n p))).trans hnN

def smallCode (t M n : ℕ) : Fin (t + 1) → Fin (M + 1) :=
  fun p => ⟨n.factorization p % (M + 1), Nat.mod_lt _ (Nat.succ_pos M)⟩

theorem exponentsEqOfCodeEq {t N a b : ℕ}
    (ha : a ∈ Finset.Icc 1 N) (hb : b ∈ Finset.Icc 1 N)
    (heq : smallCode t (Nat.log 2 N) a = smallCode t (Nat.log 2 N) b) :
    ∀ p ≤ t, a.factorization p = b.factorization p := by
  intro p hp
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
  have hla := factorizationLeLog (p := p) (by omega) ha2
  have hlb := factorizationLeLog (p := p) (by omega) hb2
  have h := congrArg (fun f => (f ⟨p, Nat.lt_succ_of_le hp⟩).val) heq
  simpa [smallCode, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hla),
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le hlb)] using h

def embed : (ℕ × ℕ) ⊕ (ℕ × ℕ) ↪ ℕ := ⟨Encodable.encode, Encodable.encode_injective⟩

end OMA.Erdos535FirstOpenCaseR1H2

open OMA.Erdos535FirstOpenCaseR1H2 in
theorem OMA.solution : OMA.R_Erdos535_erdos_535_variants_first_open_case_R1.H2 := by
  intro t K N hK
  refine ⟨smallCode t (Nat.log 2 N), fun n => (padded t K n).map embed, ?_, ?_⟩
  · intro n hn
    rw [Finset.card_map]
    exact cardPadded (by rw [cardRoughLayers]; exact hK n hn)
  · intro a ha b hb c hc d hd hab hac had hinter
    rw [← Finset.map_inter, ← Finset.map_inter] at hinter
    have hpos {n : ℕ} (hn : n ∈ Finset.Icc 1 N) : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    exact gcdEqOfIntersection (t := t) (K := K) (hpos ha) (hpos hb) (hpos hc) (hpos hd)
      (exponentsEqOfCodeEq ha hc hac) (exponentsEqOfCodeEq hb hd (hab.symm.trans had))
      (Finset.map_injective embed hinter)
