import OMAReductions.R_Erdos436_erdos_436_variants_six_two_R1_H2_R1

/-!
We only need to examine odd zero scores, since every consecutive pair has
one odd member. A size bound leaves 19 possible prime factors, and the
reflected search visits all their sorted products up to the cutoff.
The labels are from equation (13) of Lehmer, Lehmer and Mills,
https://doi.org/10.4153/CJM-1963-020-4.
The odd-factor search adapts Marcus Buffett's seventh-power lower certificate
(#3368).
-/

namespace SexticLower436

/-- Negatives of the labels in equation (13), represented by natural numbers. -/
private def mark (p : ℕ) : ℕ :=
  if p ∈ ([3, 43, 61] : List ℕ) then 0 else
    if p ∈ ([71, 101, 331, 733, 1423, 4877, 5413, 6043] : List ℕ) then 2 else 1

private def score (s : List ℕ) : ℕ := (s.map mark).sum

private theorem mark_le_two (p : ℕ) : mark p ≤ 2 := by unfold mark; split_ifs <;> decide

private theorem cost (p : ℕ) (hp : p.Prime) (hne : p ≠ 2) : 5 ^ mark p ≤ p := by
  by_cases h : p < 25
  · have tab : ∀ i : Fin 25, i.val.Prime → i.val ≠ 2 → 5 ^ mark i.val ≤ i.val := by
      decide +kernel
    exact tab ⟨p, h⟩ hp hne
  · exact (Nat.pow_le_pow_right (by decide) (mark_le_two p)).trans (by omega)

private theorem prod_lb (b : ℕ) (v : ℕ → ℕ) (s : List ℕ)
    (h : ∀ p ∈ s, b ^ v p ≤ p) : b ^ (s.map v).sum ≤ s.prod := by
  induction s with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons, pow_add]
    exact Nat.mul_le_mul (h p (by simp)) (ih fun q hq => h q (by simp [hq]))

private def candidates : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 71, 101]

/-- Every odd prime costs at least `5 ^ mark p`. If a positive-label prime
occurs in a zero-score factorization, the remaining score is at least
`6 - mark p`, which bounds the possible prime factors. -/
private theorem candidate_of_mem {n p : ℕ} (hn : 0 < n) (hN : n ≤ 202124) (ho : Odd n)
    (hz : score n.primeFactorsList % 6 = 0) (hp : p ∈ n.primeFactorsList) :
    p ∈ candidates := by
  by_cases hzero : p ∈ ([3, 43, 61] : List ℕ)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hzero
    rcases hzero with rfl | rfl | rfl <;> decide
  · have hpos : 0 < mark p := by
      simp only [mark, if_neg hzero]
      split <;> decide
    have hOddPrime {q : ℕ} (hq : q ∈ n.primeFactorsList) : q ≠ 2 :=
      fun e => ho.not_two_dvd_nat (e ▸ Nat.dvd_of_mem_primeFactorsList hq)
    let tail := n.primeFactorsList.erase p
    have perm : n.primeFactorsList.Perm (p :: tail) := List.perm_cons_erase hp
    have hscore : score n.primeFactorsList = mark p + score tail := by
      simpa [score] using (perm.map mark).sum_eq
    have hprod : n = p * tail.prod := by
      simpa [Nat.prod_primeFactorsList hn.ne'] using perm.prod_eq
    have htail : 5 ^ score tail ≤ tail.prod :=
      prod_lb 5 mark tail fun q hq => cost q
        (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_erase hq))
        (hOddPrime (List.mem_of_mem_erase hq))
    have hneed : 6 - mark p ≤ score tail := by omega
    have hbudget : p * 5 ^ (6 - mark p) ≤ 202124 := by
      calc
        _ ≤ p * tail.prod := Nat.mul_le_mul_left _
          ((Nat.pow_le_pow_right (by decide) hneed).trans htail)
        _ = n := hprod.symm
        _ ≤ _ := hN
    have hpow : 625 ≤ 5 ^ (6 - mark p) :=
      Nat.pow_le_pow_right (by decide : 0 < 5) (show 4 ≤ 6 - mark p by
        have := mark_le_two p
        omega)
    have hsmall : p < 324 := by
      have h := (Nat.mul_le_mul_left p hpow).trans hbudget
      omega
    have tab : ∀ i : Fin 324, i.val.Prime → i.val ≠ 2 →
        i.val * 5 ^ (6 - mark i.val) ≤ 202124 → i.val ∈ candidates := by decide +kernel
    exact tab ⟨p, hsmall⟩ (Nat.prime_of_mem_primeFactorsList hp) (hOddPrime hp) hbudget

private def nonzeroScore (n : ℕ) : Bool := score n.primeFactorsList % 6 != 0

private def neighbors (x w : ℕ) : Bool :=
  (w % 6 != 0) ||
    ((decide (x ≤ 1) || nonzeroScore (x - 1)) &&
      (decide (202124 ≤ x) || nonzeroScore (x + 1)))

/-- Enumerate sorted candidate prime factors, truncating branches at the cutoff. -/
private def check : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, x, w, _ => neighbors x w
  | k + 1, x, w, low =>
    neighbors x w && candidates.all fun p =>
      if low ≤ p ∧ x * p ≤ 202124 then check k (x * p) (w + mark p) p else true

private theorem check_sound (k x w low : ℕ) (s : List ℕ) (hcheck : check k x w low = true)
    (hlen : s.length ≤ k) (hmem : ∀ p ∈ s, p ∈ candidates)
    (hlow : ∀ p ∈ s, low ≤ p) (hsort : s.Pairwise (· ≤ ·))
    (hpos : ∀ p ∈ s, 0 < p) (hN : x * s.prod ≤ 202124) :
    neighbors (x * s.prod) (w + score s) = true := by
  induction k generalizing x w low s with
  | zero =>
    have hs : s = [] := List.length_eq_zero_iff.1 (by omega)
    simpa [hs, score, check] using hcheck
  | succ k ih =>
    obtain ⟨hhere, hall⟩ := Bool.and_eq_true_iff.1 hcheck
    cases s with
    | nil => simpa [score] using hhere
    | cons p ps =>
      have hN' : (x * p) * ps.prod ≤ 202124 := by simpa [Nat.mul_assoc] using hN
      have hbound : x * p ≤ 202124 :=
        (Nat.le_mul_of_pos_right _ (List.prod_pos fun q hq => hpos q (by simp [hq]))).trans hN'
      have hrecur := List.all_eq_true.1 hall p (hmem p (by simp))
      rw [if_pos ⟨hlow p (by simp), hbound⟩] at hrecur
      have hsorted := List.pairwise_cons.1 hsort
      have hlen' : ps.length ≤ k := by simp at hlen; omega
      have h := ih (x * p) (w + mark p) p ps hrecur hlen'
        (fun q hq => hmem q (by simp [hq])) hsorted.1 hsorted.2
        (fun q hq => hpos q (by simp [hq])) hN'
      simpa [score, Nat.mul_assoc, Nat.add_assoc] using h

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
private theorem checked : check 11 1 0 0 = true := by decide +kernel

private theorem odd_neighbors (n : ℕ) (hn : 0 < n) (hN : n ≤ 202124) (ho : Odd n)
    (hz : score n.primeFactorsList % 6 = 0) :
    (n ≤ 1 ∨ nonzeroScore (n - 1) = true) ∧
      (202124 ≤ n ∨ nonzeroScore (n + 1) = true) := by
  let s := n.primeFactorsList
  have hs : s.prod = n := Nat.prod_primeFactorsList hn.ne'
  have hprime {p : ℕ} (hp : p ∈ s) : p.Prime := Nat.prime_of_mem_primeFactorsList hp
  have h3 {p : ℕ} (hp : p ∈ s) : 3 ≤ p := by
    have h2 := (hprime hp).two_le
    have hne : p ≠ 2 := fun e => ho.not_two_dvd_nat (e ▸ Nat.dvd_of_mem_primeFactorsList hp)
    omega
  have hpows : 3 ^ s.length ≤ s.prod := by
    simpa [List.map_const', List.sum_replicate, smul_eq_mul] using
      prod_lb 3 (fun _ => 1) s (fun p hp => by simpa using h3 hp)
  have hlen : s.length ≤ 11 := by
    by_contra! h
    have := (Nat.pow_le_pow_right (by decide : 0 < 3) h).trans (hpows.trans (hs ▸ hN))
    norm_num at this
  have h := check_sound 11 1 0 0 s checked hlen
    (fun p hp => candidate_of_mem hn hN ho hz hp) (fun _ _ => Nat.zero_le _)
    (Nat.primeFactorsList_sorted n).pairwise
    (fun p hp => (hprime hp).pos) (by simpa [hs] using hN)
  simpa [neighbors, hs, s, hz] using h

private theorem no_earlier_pair (n : ℕ) (hn : 1 ≤ n) (hN : n < 202124)
    (hz : score n.primeFactorsList % 6 = 0)
    (hz' : score (n + 1).primeFactorsList % 6 = 0) : False := by
  by_cases ho : Odd n
  · have h := (odd_neighbors n hn hN.le ho hz).2
    simp [nonzeroScore, hz', Nat.not_le_of_gt hN] at h
  · have h := (odd_neighbors (n + 1) (by omega) (by omega)
        (Nat.odd_add_one.mpr ho) hz').1
    simp [nonzeroScore, hz] at h
    omega

private theorem score_zero_of_mod_cast_zero (f : ℕ → ZMod 6)
    (hf : ∀ p, f p = -(mark p : ZMod 6)) (n : ℕ)
    (hz : (n.primeFactorsList.map f).sum = 0) :
    score n.primeFactorsList % 6 = 0 := by
  have hsum (s : List ℕ) : (s.map f).sum = -((score s : ℕ) : ZMod 6) := by
    induction s with
    | nil => simp [score]
    | cons p ps ih => simp [score, hf, ih, add_comm]
  rw [hsum, neg_eq_zero, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at hz
  exact hz

end SexticLower436

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_six_two_R1_H2_R1.H1 := by
  intro n hn hlt
  by_contra! h
  let f (q : ℕ) : ZMod 6 := if q ∈ ([3, 43, 61] : List ℕ) then 0 else
    if q ∈ ([71, 101, 331, 733, 1423, 4877, 5413, 6043] : List ℕ) then 4 else 5
  have hf (q : ℕ) : f q = -(SexticLower436.mark q : ZMod 6) := by
    simp only [f, SexticLower436.mark]
    split_ifs <;> decide
  exact SexticLower436.no_earlier_pair n hn hlt
    (SexticLower436.score_zero_of_mod_cast_zero f hf n h.1)
    (SexticLower436.score_zero_of_mod_cast_zero f hf (n + 1) h.2)
