import OMAStatements.S_oeis_a033188
import Mathlib

namespace OMA.R_oeis_a033188_R1

open OMA.S_oeis_a033188

/-- The prime-tuple existence direction, conditional on absence of local obstructions. -/
def H1 : Prop := ∀ n : ℕ, 8 ≤ n →
    (∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ i : Fin n, ¬ p ∣ r+(i:ℕ)*primorial n) →
    ∃ a : ℕ, ∀ i : Fin n, (a+(i:ℕ)*primorial n).Prime

/-- The only potentially smaller steps have this form and must start at n itself. -/
def H2 : Prop := ∀ p : ℕ, 97 < p → p.Prime → ∀ k : ℕ, 0 < k → k < p →
    ∃ i : Fin p, ¬ (p+(i:ℕ)*(primorial (p-1)*k)).Prime

lemma primorial_dvd_of_all {m d : ℕ} (h : ∀ q : ℕ, q.Prime → q ≤ m → q ∣ d) :
    primorial m ∣ d := by
  unfold primorial
  exact Finset.prod_primes_dvd _ (fun q hq => (Finset.mem_filter.mp hq).2.prime)
    (fun q hq => h q (Finset.mem_filter.mp hq).2
      (by simpa using (Finset.mem_filter.mp hq).1))

lemma hit {p a d : ℕ} (hp : p.Prime) (hd : ¬ p ∣ d) :
    ∃ j : ℕ, j < p ∧ p ∣ a+j*d := by
  let _ : Fact p.Prime := ⟨hp⟩
  let u : ZMod p := -(a : ZMod p) / (d : ZMod p)
  have hn : (d : ZMod p) ≠ 0 := fun h => hd ((ZMod.natCast_eq_zero_iff ..).mp h)
  refine ⟨u.val, u.val_lt, (ZMod.natCast_eq_zero_iff ..).mp ?_⟩
  rw [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val]
  simp [u,hn]

lemma forced_start {p n a d : ℕ} (hp : p.Prime) (hd : ¬ p ∣ d) (hn : p ≤ n)
    (hsize : p < a+d) (allPr : ∀ i : Fin n, (a+(i:ℕ)*d).Prime) : a=p := by
  obtain ⟨j,hj,hdj⟩ := hit (a := a) hp hd
  have he := (Nat.prime_dvd_prime_iff_eq hp (allPr ⟨j,hj.trans_le hn⟩)).mp hdj
  change p = a+j*d at he
  have hz : j=0 := by
    by_contra! h
    have hle := Nat.mul_le_mul_right d (show 1 ≤ j by omega)
    omega
  simpa [hz] using he.symm

lemma forced_difference {n a d : ℕ} (hd : 0 < d)
    (allPr : ∀ i : Fin n, (a+(i:ℕ)*d).Prime) :
    ∀ p : ℕ, p < n → p.Prime → p ∣ d := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro hpn hp
    by_contra hnot
    have base : primorial (p-1) ∣ d := primorial_dvd_of_all fun q hq hle =>
      ih q (by have := hp.two_le; omega) (by omega) hq
    have hsize := (le_primorial_self (n := p-1)).trans (Nat.le_of_dvd hd base)
    have ha : a.Prime := by simpa using allPr ⟨0,by omega⟩
    have he := forced_start hp hnot hpn.le (by have := ha.two_le; omega) allPr
    have hlast := allPr ⟨p,hpn⟩
    change (a+p*d).Prime at hlast
    rw [he] at hlast
    have hdv : p ∣ p+p*d := dvd_add dvd_rfl (dvd_mul_right _ _)
    have same := (Nat.prime_dvd_prime_iff_eq hp hlast).mp hdv
    have : 0 < p*d := Nat.mul_pos hp.pos hd
    omega

lemma admissible {n p : ℕ} (hp : p.Prime) :
    ∃ r : ℕ, ∀ i : Fin n, ¬ p ∣ r+(i:ℕ)*primorial n := by
  by_cases h : p ≤ n
  · refine ⟨1,fun i he => hp.not_dvd_one ?_⟩
    have hd : p ∣ (i:ℕ)*primorial n := dvd_mul_of_dvd_right (hp.dvd_primorial_iff.mpr h) _
    exact (Nat.dvd_add_iff_left hd).mpr he
  · refine ⟨primorial n,fun i he => ?_⟩
    rw [show primorial n+(i:ℕ)*primorial n = ((i:ℕ)+1)*primorial n by ring] at he
    rcases hp.dvd_mul.mp he with h1|h2
    · have := Nat.le_of_dvd (Nat.succ_pos _) h1
      have := i.isLt
      omega
    · exact h (hp.dvd_primorial_iff.mp h2)

lemma boundary {n : ℕ} (hn : 0<n) (hp : n.Prime) :
    primorial n = n * primorial (n-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  change primorial (k+1) = (k+1)*primorial k
  unfold primorial
  rw [show Finset.range (k+1+1) = insert (k+1) (Finset.range (k+1)) from Finset.range_add_one,
    Finset.filter_insert, if_pos hp,
    Finset.prod_insert (by simp)]


set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
lemma small_cert : ∀ p : Fin 98, 8 ≤ p.val → p.val.Prime → ∀ k : Fin p.val,
    0 < k.val → ∃ j : Fin p.val,
      let z := p.val+j.val*(primorial (p.val-1)*k.val)
      (1 < z.gcd 23984823528925228172706521638692258396210 ∧
        z.gcd 23984823528925228172706521638692258396210 < z) ∨
      (1 < z.gcd 17 ∧ z.gcd 17 < z) := by
  decide +kernel

lemma small {p k : ℕ} (hlo : 8 ≤ p) (hhi : p ≤ 97) (hp : p.Prime) (hk : 0 < k) (hkp : k < p) :
    ∃ i : Fin p, ¬ (p+(i:ℕ)*(primorial (p-1)*k)).Prime := by
  obtain ⟨i, hi⟩ := small_cert ⟨p,by omega⟩ hlo hp ⟨k,hkp⟩ hk
  refine ⟨i, fun hpr => ?_⟩
  let z := p+(i:ℕ)*(primorial (p-1)*k)
  change z.Prime at hpr
  have excludes (t : ℕ) (h : 1 < z.gcd t ∧ z.gcd t < z) : False := by
    rcases (Nat.dvd_prime hpr).mp (Nat.gcd_dvd_left z t) with h'|h' <;> omega
  rcases hi with h|h
  · exact excludes _ h
  · exact excludes _ h

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a033188.main := by
  intro tuple prime_start n hn
  refine ⟨⟨primorial_pos _, tuple n hn (fun _ hp => admissible hp)⟩, ?_⟩
  rintro d ⟨hd,a,hpr⟩
  have forced := forced_difference hd hpr
  by_contra! hlt
  have hnot : ¬ primorial n ∣ d := fun h => (Nat.not_le.mpr hlt) (Nat.le_of_dvd hd h)
  have hfailure : ∃ q : ℕ, q.Prime ∧ q ≤ n ∧ ¬q ∣ d := by
    by_contra! hall
    exact hnot (primorial_dvd_of_all hall)
  obtain ⟨q,hq,hqn,hqd⟩ := hfailure
  have heq : q = n := by
    by_contra h
    exact hqd (forced q (by omega) hq)
  subst q
  have base : primorial (n-1) ∣ d :=
    primorial_dvd_of_all fun q hp hle => forced q (by omega) hp
  have hsz := (le_primorial_self (n := n-1)).trans (Nat.le_of_dvd hd base)
  have hpa : a.Prime := by simpa using hpr ⟨0,by omega⟩
  have ha := forced_start hq hqd le_rfl (by have := hpa.two_le; omega) hpr
  obtain ⟨k, hk⟩ := base
  have hkpos : 0 < k := by
    by_contra! hh
    simp [show k=0 by omega] at hk
    omega
  have hkn : k < n := by
    rw [hk,boundary (by omega) hq,mul_comm n] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt
  have obs : ∃ i : Fin n, ¬ (n+(i:ℕ)*(primorial (n-1)*k)).Prime := by
    by_cases hs : n ≤ 97
    · exact small hn hs hq hkpos hkn
    · exact prime_start n (by omega) hq k hkpos hkn
  obtain ⟨i,hi⟩ := obs
  exact hi (by simpa only [ha,hk] using hpr i)

end OMA.R_oeis_a033188_R1

