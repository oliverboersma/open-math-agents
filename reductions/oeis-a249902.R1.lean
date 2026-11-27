import OMAStatements.S_oeis_a249902

-- Credit: @physbuzz
namespace OMA.R_oeis_a249902_R1
open ArithmeticFunction Finset

lemma sigma_ge (n : ℕ) (hn : 0 < n) : n ≤ sigma 1 n := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors.mpr ⟨dvd_refl n,hn.ne'⟩)

lemma power_of_sigma_prime (n : ℕ) (hs : (sigma 1 n).Prime) : IsPrimePow n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk => exact (isPrimePow_nat_iff _).mpr ⟨p,k,hp,hk,rfl⟩
  | zero => exact False.elim (Nat.not_prime_zero (by simpa using hs))
  | one => exact False.elim (Nat.not_prime_one (by simpa using hs))
  | coprime a b ha hb hab _ _ =>
    rw [isMultiplicative_sigma.map_mul_of_coprime hab] at hs
    have A := sigma_ge a (by omega)
    have B := sigma_ge b (by omega)
    exact False.elim (Nat.not_prime_mul (by omega) (by omega) hs)

lemma three_dvd (n : ℕ) (hn : 2 < n) (l : (2*n-1).Prime) (r : (2*n+1).Prime) :
    3 ∣ n := by
  have hd (x : ℕ) (hx : x.Prime) (gt : 3 < x) : ¬3 ∣ x := by
    intro div
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hx).mp div
    omega
  have nl := hd _ l (by omega)
  have nr := hd _ r (by omega)
  obtain ⟨t, ht⟩ : ∃ t, n = 3*t + n%3 := ⟨n/3, (Nat.div_add_mod n 3).symm⟩
  by_cases h : n%3 = 0
  · exact Nat.dvd_of_mod_eq_zero h
  have lim := Nat.mod_lt n (by decide : 0<3)
  rcases (by omega : n%3 = 1 ∨ n%3 = 2) with h1|h2
  · exact (nr ⟨2*t+1,by omega⟩).elim
  · exact (nl ⟨2*t+1,by omega⟩).elim

lemma sum_gt_one (x n : ℕ) (hx : 2 ≤ x) (hn : 2 ≤ n) :
    1 < ∑ i ∈ range n, x^i := by
  have le := Finset.single_le_sum (f := fun i : ℕ => x^i) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : 1 < n))
  simpa using lt_of_lt_of_le (by simpa using (show 1 < x by omega) : 1 < x^1) le

lemma prime_length (k : ℕ) (hk : 1 ≤ k) (hs : (sigma 1 (3^k)).Prime) : (k+1).Prime := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)] at hs
  by_contra no
  let a := (k+1).minFac
  let b := (k+1)/a
  have ha : a.Prime := Nat.minFac_prime (by omega)
  have hab : a*b = k+1 := Nat.mul_div_cancel' (Nat.minFac_dvd _)
  have hb : 2 ≤ b := ha.two_le.trans (Nat.minFac_le_div (by omega) no)
  have A := geom_sum_mul_add (2 : ℕ) a
  have C := geom_sum_mul_add (2 : ℕ) (k+1)
  have B := geom_sum_mul_of_one_le (x := (3:ℕ)^a) (Nat.one_le_pow _ _ (by decide)) b
  change (∑ i ∈ range a, 3^i) * 2 + 1 = 3^a at A
  change (∑ i ∈ range (k+1), 3^i) * 2 + 1 = 3^(k+1) at C
  rw [← pow_mul,hab,← A,← C] at B
  simp only [Nat.add_sub_cancel] at B
  have fac : (∑ i ∈ range (k+1), 3^i) =
      (∑ i ∈ range a, 3^i)*(∑ j ∈ range b, (3^a)^j) := by
    rw [A] at B
    nlinarith only [B]
  have pgt : 2 ≤ 3^a := (by decide : 2 ≤ 3).trans (Nat.le_self_pow ha.ne_zero _)
  rw [fac] at hs
  exact Nat.not_prime_mul (by have := sum_gt_one 3 a (by decide) ha.two_le; omega)
    (by have := sum_gt_one (3^a) b pgt hb; omega) hs

lemma root_shape (n : ℕ) (hn : 2 < n) (l : (2*n-1).Prime) (r : (2*n+1).Prime)
    (s : (sigma 1 n).Prime) : ∃ k : ℕ, 0 < k ∧ n = 3^k ∧ (k+1).Prime := by
  obtain ⟨p,k,hp,hk,eq⟩ := (isPrimePow_nat_iff _).mp (power_of_sigma_prime n s)
  have d := three_dvd n hn l r
  rw [← eq] at d
  have same := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp
    ((by decide : Nat.Prime 3).dvd_of_dvd_pow d)
  subst p
  exact ⟨k,hk,eq.symm,prime_length k hk (eq.symm ▸ s)⟩


lemma transport_coprime {a b m : ℕ} (eq : a ≡ b [MOD m]) (h : a.Coprime m) : b.Coprime m := by
  change a % m = b % m at eq
  change Nat.gcd a m = 1 at h
  change Nat.gcd b m = 1
  rwa [Nat.gcd_comm b m, Nat.gcd_rec, ← eq, ← Nat.gcd_rec, Nat.gcd_comm]

lemma exponent_mod (k : ℕ) (big : 1000 < k) (pe : (k+1).Prime)
    (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) : k%30 = 0 ∨ k%30 = 12 := by
  let t := k%30
  have unit : 3^30 ≡ 1 [MOD 2387] := by decide +kernel
  have per : 3^k ≡ 3^t [MOD 2387] := by
    have eq := (unit.pow (k/30)).mul_right (3^t)
    simpa only [← pow_mul,← pow_add, Nat.div_add_mod, one_pow,one_mul,t] using eq
  have size : 2387 < 2*3^k-1 := by
    have low : (3:ℕ)^8 ≤ 3^k := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at low
    omega
  have cop (x m : ℕ) (h : x.Prime) (hm : 0 < m) (hx : m < x) : x.Coprime m :=
    h.coprime_iff_not_dvd.mpr fun d => (not_le_of_gt hx) (Nat.le_of_dvd hm d)
  have ca := transport_coprime (m:=30) ((Nat.mod_modEq k 30).symm.add_right 1)
    (cop _ _ pe (by decide) (by omega))
  have hkt : 1 ≤ 2*3^k := by have := Nat.one_le_pow k 3 (by decide); omega
  have htt : 1 ≤ 2*3^t := by have := Nat.one_le_pow t 3 (by decide); omega
  have subeq : 2*3^k-1 ≡ 2*3^t-1 [MOD 2387] := Nat.ModEq.sub hkt htt (per.mul_left 2) Nat.ModEq.rfl
  have cb := transport_coprime subeq (cop _ 2387 l (by decide) size)
  have cc := transport_coprime ((per.mul_left 2).add_right 1) (cop _ 2387 r (by decide) (by omega))
  have wheel : ∀ j : Fin 30, (j.val+1).Coprime 30 → (2*3^j.val-1).Coprime 2387 →
      (2*3^j.val+1).Coprime 2387 → j.val = 0 ∨ j.val = 12 := by decide +kernel
  exact wheel ⟨t,Nat.mod_lt _ (by decide)⟩ ca cb cc

private lemma obstruct {x q : ℕ} (hp : x.Prime) (w : 1 < q ∧ q < x ∧ x%q=0) : False := by
  rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero w.2.2) with e | e <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude0 (k : ℕ) (lo : 0 ≤ k) (hi : k < 64) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [1,2,1,2,7,2,31,2,3,2,7,2,353,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,683,2,3,2,5,2,31,2,3,2,7,2,17,2,3,2,7,2,7,2,3,2,7,2,5,2,3,2,7,2,18121,2,3,2]
  have cert : ∀ t : Fin 64, let j := 0+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-0,by omega⟩
  have eq : 0+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude64 (k : ℕ) (lo : 64 ≤ k) (hi : k < 128) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [5,2,17,2,3,2,7,2,89,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,7,2,3,2,5,2,31,2,3,2,7,2,131,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,11,2,3,2,5,2,31,2]
  have cert : ∀ t : Fin 64, let j := 64+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-64,by omega⟩
  have eq : 64+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude128 (k : ℕ) (lo : 128 ≤ k) (hi : k < 192) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [3,2,7,2,7,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,1511,2,3,2,5,2,31,2,3,2,7,2,17,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,23,2,3,2,5,2,11,2,3,2,7,2]
  have cert : ∀ t : Fin 64, let j := 128+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-128,by omega⟩
  have eq : 128+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude192 (k : ℕ) (lo : 192 ≤ k) (hi : k < 256) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [179,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,17,2,3,2,5,2,7,2,3,2,7,2,110573161913,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,107,2,3,2,5,2,13,2,3,2,7,2,11,2,3,2]
  have cert : ∀ t : Fin 64, let j := 192+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-192,by omega⟩
  have eq : 192+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude256 (k : ℕ) (lo : 256 ≤ k) (hi : k < 320) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [7,2,7,2,3,2,7,2,5,2,3,2,7,2,3253,2,3,2,5,2,31,2,3,2,7,2,17,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,7,2,3,2,5,2,17,2,3,2,7,2,23,2,3,2,7,2,11,2]
  have cert : ∀ t : Fin 64, let j := 256+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-256,by omega⟩
  have eq : 256+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude320 (k : ℕ) (lo : 320 ≤ k) (hi : k < 384) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [3,2,7,2,5,2,3,2,7,2,17,2,3,2,5,2,31,2,3,2,7,2,7,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,19,2,3,2,5,2,31,2,3,2,7,2,43,2,3,2,7,2,11,2,3,2,7,2]
  have cert : ∀ t : Fin 64, let j := 320+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-320,by omega⟩
  have eq : 320+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude384 (k : ℕ) (lo : 384 ≤ k) (hi : k < 448) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [5,2,3,2,7,2,17,2,3,2,5,2,31,2,3,2,7,2,13,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,47,2,3,2,5,2,7,2,3,2,7,2,127,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2]
  have cert : ∀ t : Fin 64, let j := 384+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-384,by omega⟩
  have eq : 384+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude448 (k : ℕ) (lo : 448 ≤ k) (hi : k < 512) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [7,2,11,2,3,2,5,2,31,2,3,2,7,2,521,2,3,2,7,2,7,2,3,2,7,2,5,2,3,2,7,2,13,2,3,2,5,2,31,2,3,2,7,2,17,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,7,2]
  have cert : ∀ t : Fin 64, let j := 448+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-448,by omega⟩
  have eq : 448+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude512 (k : ℕ) (lo : 512 ≤ k) (hi : k < 576) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [3,2,5,2,11,2,3,2,7,2,17,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,43,2,3,2,5,2,17,2,3,2,7,2,7,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,17,2,3,2,5,2]
  have cert : ∀ t : Fin 64, let j := 512+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-512,by omega⟩
  have eq : 512+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude576 (k : ℕ) (lo : 576 ≤ k) (hi : k < 640) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [23,2,3,2,7,2,11,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,89,2,3,2,5,2,31,2,3,2,7,2,1777,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,1399,2,3,2,5,2,7,2,3,2]
  have cert : ∀ t : Fin 64, let j := 576+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-576,by omega⟩
  have eq : 576+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude640 (k : ℕ) (lo : 640 ≤ k) (hi : k < 704) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [7,2,17,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,113,2,3,2,5,2,17,2,3,2,7,2,2657,2,3,2,7,2,7,2,3,2,7,2,5,2,3,2,7,2,17,2,3,2,5,2,17,2,3,2,7,2,19,2]
  have cert : ∀ t : Fin 64, let j := 640+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-640,by omega⟩
  have eq : 640+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude704 (k : ℕ) (lo : 704 ≤ k) (hi : k < 768) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,7,2,3,2,5,2,31,2,3,2,7,2,89,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,43,2,3,2,5,2,31,2,3,2,7,2,7,2,3,2,7,2]
  have cert : ∀ t : Fin 64, let j := 704+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-704,by omega⟩
  have eq : 704+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude768 (k : ℕ) (lo : 768 ≤ k) (hi : k < 832) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [11,2,3,2,7,2,5,2,3,2,7,2,11,2,3,2,5,2,17,2,3,2,7,2,13,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,17,2,3,2,5,2,19,2,3,2,7,2,7079,2,3,2,7,2,11,2,3,2]
  have cert : ∀ t : Fin 64, let j := 768+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-768,by omega⟩
  have eq : 768+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude832 (k : ℕ) (lo : 832 ≤ k) (hi : k < 896) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [7,2,5,2,3,2,7,2,23,2,3,2,5,2,7,2,3,2,7,2,59,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,13,2,3,2,5,2,31,2,3,2,7,2,17,2,3,2,7,2,7,2,3,2,7,2,5,2]
  have cert : ∀ t : Fin 64, let j := 832+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-832,by omega⟩
  have eq : 832+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude896 (k : ℕ) (lo : 896 ≤ k) (hi : k < 960) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [3,2,7,2,17,2,3,2,5,2,17,2,3,2,7,2,11,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,7,2,3,2,5,2,31,2,3,2,7,2,23,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2]
  have cert : ∀ t : Fin 64, let j := 896+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 64 := ⟨k-896,by omega⟩
  have eq : 896+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private lemma exclude960 (k : ℕ) (lo : 960 ≤ k) (hi : k < 1001) (pos : 0 < k) (diff : k ≠ 2)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : False := by
  let factors : List ℕ := [31,2,3,2,5,2,31,2,3,2,7,2,7,2,3,2,7,2,11,2,3,2,7,2,5,2,3,2,7,2,3251,2,3,2,5,2,31,2,3,2,7]
  have cert : ∀ t : Fin 41, let j := 960+t.val; let q := factors[t.val]!;
      0 < j → j ≠ 2 → (1 < q ∧ q < j+1 ∧ (j+1)%q=0) ∨
      (1 < q ∧ q < 2*3^j-1 ∧ (2*3^j-1)%q=0) ∨ (1 < q ∧ q < 2*3^j+1 ∧ (2*3^j+1)%q=0) ∨
      (1 < q ∧ q < (3^(j+1)-1)/2 ∧ ((3^(j+1)-1)/2)%q=0) := by decide +kernel
  let t : Fin 41 := ⟨k-960,by omega⟩
  have eq : 960+t.val = k := by dsimp [t]; omega
  specialize cert t
  simp only [eq] at cert
  rcases cert pos diff with w|w|w|w
  · exact obstruct he w
  · exact obstruct l w
  · exact obstruct r w
  · exact obstruct s w
lemma finite_exponents (k : ℕ) (pos : 0 < k) (lim : k ≤ 1000)
    (he : (k+1).Prime) (l : (2*3^k-1).Prime) (r : (2*3^k+1).Prime) (s : ((3^(k+1)-1)/2).Prime) : k = 2 := by
  by_contra diff
  by_cases h8 : k < 512
  · by_cases h4 : k < 256
    · by_cases h2 : k < 128
      · by_cases h1 : k < 64
        · exact exclude0 k (by omega) (by omega) pos diff he l r s
        · exact exclude64 k (by omega) (by omega) pos diff he l r s
      · by_cases h3 : k < 192
        · exact exclude128 k (by omega) (by omega) pos diff he l r s
        · exact exclude192 k (by omega) (by omega) pos diff he l r s
    · by_cases h6 : k < 384
      · by_cases h5 : k < 320
        · exact exclude256 k (by omega) (by omega) pos diff he l r s
        · exact exclude320 k (by omega) (by omega) pos diff he l r s
      · by_cases h7 : k < 448
        · exact exclude384 k (by omega) (by omega) pos diff he l r s
        · exact exclude448 k (by omega) (by omega) pos diff he l r s
  · by_cases h12 : k < 768
    · by_cases h10 : k < 640
      · by_cases h9 : k < 576
        · exact exclude512 k (by omega) (by omega) pos diff he l r s
        · exact exclude576 k (by omega) (by omega) pos diff he l r s
      · by_cases h11 : k < 704
        · exact exclude640 k (by omega) (by omega) pos diff he l r s
        · exact exclude704 k (by omega) (by omega) pos diff he l r s
    · by_cases h14 : k < 896
      · by_cases h13 : k < 832
        · exact exclude768 k (by omega) (by omega) pos diff he l r s
        · exact exclude832 k (by omega) (by omega) pos diff he l r s
      · by_cases h15 : k < 960
        · exact exclude896 k (by omega) (by omega) pos diff he l r s
        · exact exclude960 k (by omega) (by omega) pos diff he l r s

/-- Both subproblems concern ternary repunits with prime length, subject to the two
neighboring primality conditions. The length is 1 or 13 modulo 30, respectively. -/
def H1 : Prop := ∀ k : ℕ, 1000 < k → k%30 = 0 → (k+1).Prime →
    (2*3^k-1).Prime → (2*3^k+1).Prime → ¬((3^(k+1)-1)/2).Prime

def H2 : Prop := ∀ k : ℕ, 1000 < k → k%30 = 12 → (k+1).Prime →
    (2*3^k-1).Prime → (2*3^k+1).Prime → ¬((3^(k+1)-1)/2).Prime

lemma sigma_three (k : ℕ) : sigma 1 (3^k) = (3^(k+1)-1)/2 := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
  have h := geom_sum_mul_add (2 : ℕ) (k+1)
  change (∑ i ∈ range (k+1), 3^i)*2+1 = 3^(k+1) at h
  omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a249902.main := by
  intro h₁ h₂
  ext n
  change (0 < n ∧ (2*n-1).Prime ∧ (2*n+1).Prime ∧ (sigma 1 n).Prime) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨pos,l,r,s⟩
    by_cases small : n ≤ 2
    · by_cases two : n=2
      · exact Or.inl two
      · have one : n=1 := by omega
        subst n
        exact False.elim (Nat.not_prime_one l)
    obtain ⟨k,hk,eq,he⟩ := root_shape n (by omega) l r s
    subst n
    rw [sigma_three] at s
    by_cases large : 1000 < k
    · obtain h|h := exponent_mod k large he l r
      · exact False.elim (h₁ k large h he l r s)
      · exact False.elim (h₂ k large h he l r s)
    · have eq := finite_exponents k hk (by omega) he l r s
      subst k
      decide
  · rintro (rfl|rfl)
    · norm_num [sigma_one_apply, Nat.divisors] <;> decide +kernel
    · norm_num [sigma_one_apply, Nat.divisors] <;> decide +kernel

end OMA.R_oeis_a249902_R1
