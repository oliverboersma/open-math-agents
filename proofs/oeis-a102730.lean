import OMAStatements.S_oeis_a102730

namespace OMA.S_oeis_a102730

-- Choose one of the dyadic rescalings of p between x and 2*x.
private theorem dyadic (p x : ℕ) (hp : 0 < p) (hpx : p ≤ x) :
    ∃ e : ℕ, x ≤ p*2^e ∧ p*2^e ≤ 2*x := by
  have hex : ∃ e : ℕ, x ≤ p*2^e := by
    refine ⟨x, (Nat.lt_pow_self (a := 2) (n := x) (by decide)).le.trans ?_⟩
    exact Nat.le_mul_of_pos_left _ hp
  let e := Nat.find hex
  refine ⟨e,Nat.find_spec hex,?_⟩
  cases he : e with
  | zero => simp; omega
  | succ j =>
    have hm := Nat.find_min hex (show j < e by omega)
    change ¬ x ≤ p*2^j at hm
    rw [pow_succ, ← mul_assoc]
    omega

-- A factorial larger than any prescribed index has binary prefix p.
-- Divide successive factorials by successive powers of a fixed dyadic L.
-- In this scale the factorials double over H steps, while a single step
-- multiplies by at most (p+1)/p. They cannot skip the requested interval.
private theorem factorial_block (p K : ℕ) (hp : 0 < p) :
    ∃ n ≥ K, ∃ shift : ℕ, n.factorial / 2^shift = p := by
  let H := (2:ℕ)^(2*p)
  let D := (2:ℕ)^(H+K)
  let L := H*D
  let N := L+D
  let A := N.factorial
  have hH : 2*p ≤ H := (Nat.lt_pow_self (by decide : 1<2)).le
  have hD : H+K ≤ D := (Nat.lt_pow_self (by decide : 1<2)).le
  have hHpos : 0 < H := by dsimp [H]; positivity
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hLpos : 0 < L := Nat.mul_pos hHpos hDpos
  have hHL : H ≤ L := Nat.le_mul_of_pos_right _ hDpos
  have hPN : p ≤ N := by dsimp only [N]; omega
  obtain ⟨e,hlo,hhi⟩ := dyadic p A hp (hPN.trans (Nat.self_le_factorial _))
  have lower (i : ℕ) : A*L^i*(H+i) ≤ (N+i).factorial*H := by
    induction i with
    | zero => simp [A]
    | succ i ih =>
      calc
        A*L^(i+1)*(H+(i+1)) = (A*L^i)*((H+i+1)*L) := by ring
        _ ≤ (A*L^i)*((H+i)*(N+i+1)) := by
          apply Nat.mul_le_mul_left
          dsimp only [N,L]
          nlinarith only [Nat.zero_le (i*D), Nat.zero_le ((H+i)*(i+1))]
        _ = (A*L^i*(H+i))*(N+i+1) := by ring
        _ ≤ ((N+i).factorial*H)*(N+i+1) := Nat.mul_le_mul_right _ ih
        _ = (N+(i+1)).factorial*H := by rw [← Nat.add_assoc, Nat.factorial_succ]; ring
  have hdouble : 2*A*L^H ≤ (N+H).factorial := by
    have hh := lower H
    have eq : A*L^H*(H+H) = (2*A*L^H)*H := by ring
    rw [eq] at hh
    exact Nat.le_of_mul_le_mul_right hh hHpos
  have hend : p*2^e*L^H ≤ (N+H).factorial :=
    (Nat.mul_le_mul_right _ hhi).trans hdouble
  have hex : ∃ i : ℕ, p*2^e*L^i ≤ (N+i).factorial := ⟨H,hend⟩
  let i := Nat.find hex
  have hi : i ≤ H := Nat.find_min' hex hend
  have hit : p*2^e*L^i ≤ (N+i).factorial := Nat.find_spec hex
  have upper : (N+i).factorial < (p+1)*2^e*L^i := by
    cases hh : i with
    | zero =>
      simp only [Nat.add_zero,pow_zero,mul_one]
      exact hlo.trans_lt (Nat.mul_lt_mul_of_pos_right (by omega) (by positivity))
    | succ j =>
      have hprev := Nat.find_min hex (show j < i by omega)
      have hprev' : (N+j).factorial < p*2^e*L^j := Nat.lt_of_not_ge hprev
      have hj : j+1 ≤ D := by omega
      have ratio : p*(N+j+1) ≤ (p+1)*L := by
        calc
          p*(N+j+1) = p*L+p*(D+(j+1)) := by dsimp only [N]; ring
          _ ≤ p*L+p*(D+D) := by gcongr
          _ = p*L+(2*p)*D := by ring
          _ ≤ p*L+H*D := by gcongr
          _ = (p+1)*L := by dsimp only [L]; ring
      calc
        (N+(j+1)).factorial = (N+j+1)*(N+j).factorial := Nat.factorial_succ _
        _ < (N+j+1)*(p*2^e*L^j) := Nat.mul_lt_mul_of_pos_left hprev' (by omega)
        _ = (2^e*L^j)*(p*(N+j+1)) := by ring
        _ ≤ (2^e*L^j)*((p+1)*L) := Nat.mul_le_mul_left _ ratio
        _ = (p+1)*2^e*L^(j+1) := by ring
  let E := 2*p+(H+K)
  have hL : 2^E = L := by simp only [E,L,H,D,pow_add]
  have hpow : 2^(e+E*i) = 2^e*L^i := by rw [pow_add,pow_mul,hL]
  refine ⟨N+i, by dsimp only [N]; omega, e+E*i, ?_⟩
  apply Nat.le_antisymm
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa [hpow,Nat.mul_assoc] using upper
  · apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    simpa [hpow,Nat.mul_assoc] using hit

-- Gather the first factorial words in a single binary word.
private theorem pattern (k : ℕ) : ∃ p > 0, ∀ m ≤ k,
    (Nat.digits 2 m.factorial).IsInfix (Nat.digits 2 p) := by
  induction k with
  | zero =>
    refine ⟨1,by decide,?_⟩
    intro m hm
    have : m = 0 := by omega
    subst m
    exact ⟨[],[],by simp⟩
  | succ k ih =>
    obtain ⟨p,hp,hall⟩ := ih
    let f := (k+1).factorial
    let q := p+2^(Nat.digits 2 p).length*f
    have hw : Nat.digits 2 p ++ Nat.digits 2 f = Nat.digits 2 q :=
      Nat.digits_append_digits (by decide)
    refine ⟨q, by dsimp only [q]; omega, ?_⟩
    intro m hm
    by_cases hmk : m ≤ k
    · apply (hall m hmk).trans
      exact ⟨[], Nat.digits 2 f, by simpa using hw⟩
    · have hm' : m = k+1 := by omega
      subst m
      exact ⟨Nat.digits 2 p, [], by simpa only [List.append_nil] using hw⟩

private theorem prefix_infix (x p shift : ℕ) (hp : 0 < p) (hdiv : x/2^shift=p) :
    (Nat.digits 2 p).IsInfix (Nat.digits 2 x) := by
  let r := x%2^shift
  have hlen : (Nat.digits 2 r).length ≤ shift :=
    (Nat.digits_length_le_iff (by decide : 1 < 2) r).mpr (Nat.mod_lt _ (by positivity))
  obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le hlen
  have h := Nat.digits_append_zeroes_append_digits (b:=2) (n:=r) (m:=p) (k:=z) (by decide) hp
  rw [← hz, ← hdiv, Nat.mod_add_div] at h
  exact ⟨Nat.digits 2 r ++ List.replicate z 0, [], by simpa only [List.append_nil, hdiv] using h⟩

end OMA.S_oeis_a102730

open OMA.S_oeis_a102730 in
theorem OMA.solution : type_of% @OMA.S_oeis_a102730.main := by
  classical
  intro k
  obtain ⟨p,hp,hall⟩ := pattern k
  obtain ⟨n,hn,shift,hdiv⟩ := factorial_block p k hp
  refine ⟨n, ?_⟩
  have hs : Finset.range (k+1) ⊆ (Finset.range (n+1)).filter (fun m => occurs m n) := by
    intro m hm
    have hm' : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      (hall m hm').trans (prefix_infix _ _ _ hp hdiv)⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_range] at hc
  exact hc
