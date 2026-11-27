import OMAReductions.R_OeisA1146_conjecture_R1_H2_R1

/-! Complete classification of semiprime predecessors with a factor at most 61.
For each prime p the table lists the complete factorization, with multiplicity,
of 2^(p+1)−1. For each listed q the last two entries encode a prime-power
obstruction for p*q+1, except for the genuine solution 16. All product,
primality and modular tests are proved in Lean. Proof by @Deldor14. -/

namespace OMA.HaslerSemiprime
open OMA.Hasler

private theorem factor_cofactor {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (passed : (p*q+1)^4-1 ∣ 2^(p*q+1)-1) : q ∣ 2^(p+1)-1 := by
  let k := p*q+1
  have hpos := Nat.mul_pos hp.pos hq.pos
  have hk : 1 < k := by dsimp [k]; omega
  have hd : q ∣ k-1 := by simp [k]
  have hd4 : q ∣ k^4-1 := hd.trans (by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow k 1 4)
  let g := k.gcd (q-1)
  have hg1 : g ∣ k := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ p*(q-1) := (Nat.gcd_dvd_right k (q-1)).trans (dvd_mul_left _ _)
  have hj : p*(q-1)+(p+1) = k := by
    change p*(q-1)+(p+1) = p*q+1
    have eq := Nat.mul_add p (q-1) 1
    rw [Nat.sub_add_cancel (by have := hq.pos; omega),mul_one] at eq
    omega
  have hgd := Nat.dvd_sub hg1 hg2
  rw [← hj] at hgd
  have hg : g ∣ p+1 := by simpa using hgd
  have hlocal := (localIff hk).mp passed q 1 hq (by simpa using hd4)
  simp only [pow_one] at hlocal
  exact hlocal.trans ((mersenneIff g (p+1)).mpr hg)

private abbrev Entry := ℕ × ℕ × ℕ
private def rows : Array (List Entry) := #[
  [],
  [],
  [(7, 2, 1)],
  [(3, 3, 2), (5, 2, 1)],
  [],
  [(3, 2, 1), (3, 2, 1), (7, 1297, 1)],
  [],
  [(3, 5, 1), (5, 1297, 1), (17, 11, 2)],
  [],
  [],
  [],
  [(3, 5, 1), (3, 5, 1), (5, 11, 1), (7, 5, 1), (13, 11, 1)],
  [],
  [(3, 13, 1), (43, 13, 1), (127, 13, 1)],
  [],
  [],
  [],
  [(3, 17, 1), (3, 17, 1), (3, 17, 1), (7, 11, 2), (19, 5, 2), (73, 5, 1)],
  [],
  [(3, 5, 1), (5, 19, 1), (5, 19, 1), (11, 19, 1), (31, 13, 1), (41, 19, 1)],
  [],
  [],
  [],
  [(3, 13, 1), (3, 13, 1), (5, 3, 2), (7, 5, 1), (13, 23, 1), (17, 23, 1), (241, 41, 1)],
  [],
  [],
  [],
  [],
  [],
  [(3, 29, 1), (3, 29, 1), (7, 29, 1), (11, 13, 1), (31, 17, 1), (151, 29, 1), (331, 29, 1)],
  [],
  [(3, 5, 1), (5, 31, 1), (17, 23, 2), (257, 5, 2), (65537, 13, 2)],
  [],
  [],
  [],
  [],
  [],
  [(3, 13, 1), (174763, 5, 2), (524287, 37, 1)],
  [],
  [],
  [],
  [(3, 5, 2), (3, 5, 2), (7, 17, 2), (7, 17, 2), (43, 17, 1), (127, 41, 1), (337, 5, 1), (5419, 5167, 1)],
  [],
  [(3, 43, 1), (5, 31, 1), (23, 17, 1), (89, 43, 1), (397, 3, 2), (683, 43, 1), (2113, 977, 1)],
  [],
  [],
  [],
  [(3, 5, 1), (3, 5, 1), (5, 47, 1), (7, 13, 1), (13, 47, 1), (17, 3, 2), (97, 47, 1), (241, 37, 1), (257, 47, 1), (673, 5, 2)],
  [],
  [],
  [],
  [],
  [],
  [(3, 7, 1), (3, 7, 1), (3, 7, 1), (3, 7, 1), (7, 53, 1), (19, 53, 1), (73, 7, 2), (87211, 53, 1), (262657, 5, 1)],
  [],
  [],
  [],
  [],
  [],
  [(3, 5, 1), (3, 5, 1), (5, 3, 2), (5, 3, 2), (7, 5, 1), (11, 7, 1), (13, 5, 2), (31, 59, 1), (41, 3, 2), (61, 59, 1), (151, 13, 1), (331, 37, 1), (1321, 29, 1)],
  [],
  [(3, 37, 1), (715827883, 7, 1), (2147483647, 3, 2)]
]
private def atRow (p : ℕ) : List Entry := rows[p]?.getD []


private theorem mem_of_prime_dvd_prod {q : ℕ} (hq : q.Prime) (l : List ℕ)
    (primes : ∀ x ∈ l, Nat.Prime x) (hd : q ∣ l.prod) : q ∈ l := by
  induction l with
  | nil => exact (hq.not_dvd_one (by simpa using hd)).elim
  | cons a l ih =>
    rcases hq.dvd_mul.mp (show q ∣ a * l.prod from hd) with left | right
    · have eq := ((Nat.dvd_prime (primes a List.mem_cons_self)).mp left).resolve_left hq.ne_one
      exact List.mem_cons.mpr (Or.inl eq)
    · exact List.mem_cons_of_mem _ (ih (fun x h => primes x (List.mem_cons_of_mem _ h)) right)

private theorem certified715827883 : Nat.Prime 715827883 := by
  apply lucas_primality _ (5 : ZMod 715827883)
  · change (5 : ZMod 715827883)^715827882 = 1
    reduce_mod_char
  · intro q hq hd
    have mem := mem_of_prime_dvd_prod hq [2, 3, 7, 11, 31, 151, 331] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1) hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 715827883)^357913941 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (5 : ZMod 715827883)^238609294 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (5 : ZMod 715827883)^102261126 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (5 : ZMod 715827883)^65075262 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (5 : ZMod 715827883)^23091222 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (5 : ZMod 715827883)^4740582 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (5 : ZMod 715827883)^2162622 ≠ 1
      reduce_mod_char
      decide +kernel

private theorem certified2147483647 : Nat.Prime 2147483647 := by
  apply lucas_primality _ (7 : ZMod 2147483647)
  · change (7 : ZMod 2147483647)^2147483646 = 1
    reduce_mod_char
  · intro q hq hd
    have mem := mem_of_prime_dvd_prod hq [2, 3, 3, 7, 11, 31, 151, 331] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1) hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2147483647)^1073741823 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (7 : ZMod 2147483647)^715827882 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (7 : ZMod 2147483647)^715827882 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (7 : ZMod 2147483647)^306783378 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (7 : ZMod 2147483647)^195225786 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (7 : ZMod 2147483647)^69273666 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (7 : ZMod 2147483647)^14221746 ≠ 1
      reduce_mod_char
      decide +kernel
    · change (7 : ZMod 2147483647)^6487866 ≠ 1
      reduce_mod_char
      decide +kernel

private def primeTable : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 73, 89, 97, 127, 151, 241, 257, 331, 337, 397, 673, 683, 977, 1297, 1321, 2113, 5167, 5419, 65537, 87211, 174763, 262657, 524287, 715827883, 2147483647]

private theorem primeTable_sound (t : ℕ) (h : t ∈ primeTable) : Nat.Prime t := by
  simp only [primeTable, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact certified715827883 | exact certified2147483647 | norm_num1

private def ok (p : ℕ) (e : Entry) : Bool :=
  let k := p*e.1+1
  let r := e.2.1
  let j := e.2.2
  decide (e.1 ∈ primeTable ∧ (k=16 ∨
    (r ∈ primeTable ∧ r^j ∣ k^4-1 ∧ ¬ r^j ∣ 2^(k.gcd (r-1))-1)))

private def valid (p : ℕ) : Bool :=
  decide (p.Prime → ((atRow p).map Prod.fst).prod = 2^(p+1)-1) &&
    (atRow p).all (ok p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem verified : (List.range 62).all valid = true := by decide +kernel

private theorem prime_entry {q : ℕ} (hq : q.Prime) (l : List Entry)
    (primes : ∀ e ∈ l, e.1.Prime) (dv : q ∣ (l.map Prod.fst).prod) :
    ∃ e ∈ l, q = e.1 := by
  induction l with
  | nil => exact (hq.not_dvd_one (by simpa using dv)).elim
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons] at dv
    rcases hq.dvd_mul.mp dv with left | right
    · exact ⟨a, List.mem_cons_self, ((Nat.dvd_prime (primes a List.mem_cons_self)).mp left).resolve_left hq.ne_one⟩
    · obtain ⟨e, he, h⟩ := ih (fun e he => primes e (List.mem_cons_of_mem _ he)) right
      exact ⟨e, List.mem_cons_of_mem _ he, h⟩

theorem classify {p q : ℕ} (hp : p.Prime) (bound : p ≤ 61) (hq : q.Prime)
    (pass : (p*q+1)^4-1 ∣ 2^(p*q+1)-1) : p*q+1 = 16 := by
  have v := List.all_eq_true.mp verified p (List.mem_range.mpr (by omega))
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at v
  have dv := factor_cofactor hp hq pass
  rw [← v.1 hp] at dv
  have data (e : Entry) (he : e ∈ atRow p) := of_decide_eq_true (List.all_eq_true.mp v.2 e he)
  obtain ⟨e, he, rfl⟩ := prime_entry hq _ (fun x h => primeTable_sound _ (data x h).1) dv
  rcases (data e he).2 with found | ⟨hr,hd,hbad⟩
  · exact found
  · have pos := Nat.mul_pos hp.pos hq.pos
    exact (hbad ((localIff (by omega)).mp pass e.2.1 e.2.2 (primeTable_sound _ hr) hd)).elim

end OMA.HaslerSemiprime

theorem OMA.solution : OMA.R_OeisA1146_conjecture_R1_H2_R1.H1 :=
  fun _ _ hp hb hq pass => OMA.HaslerSemiprime.classify hp hb hq pass
