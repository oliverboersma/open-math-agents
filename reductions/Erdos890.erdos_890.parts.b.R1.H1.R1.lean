import OMAReductions.R_Erdos890_erdos_890_parts_b_R1

/-!
Remove primes at most the block length and assign each remaining prime its
unique offset. A large count then gives a finite Chinese remainder problem
with polynomially bounded prime moduli. The one-variable factorial estimate
is taken from the parent reduction.
-/
namespace OMA.R_Erdos890_erdos_890_parts_b_R1_H1_R1
open Filter Finset Real
open scoped Classical BigOperators Topology

/-- The upper-bound half of the prime number theorem, at a real cutoff. -/
def H1 : Prop := ∀ ε : ℝ, 0<ε → ∀ᶠ y : ℝ in atTop,
    ((Nat.primesLE ⌊y⌋₊).card:ℝ)*(log y/y) ≤ 1+ε

/-- Integer-only lower bound on exceptional least positive CRT representatives.
Only mixed offsets, prime moduli polynomial in their count, and representatives
smaller than the product minus the block length are involved. -/
def H2 : Prop := ∀ k D u : ℕ, 2 ≤ k → 1 ≤ D → 1 ≤ u → ∀ᶠ t : ℕ in atTop,
    ∀ (S : Finset ℕ) (w : ℕ → ℕ) (r : ℕ), S.card=t → 0 < r →
    (∀ p∈S, p.Prime ∧ k < p ∧ p ≤ t^D ∧ w p < k ∧ p∣r+w p) →
    (∃ p∈S, ∃ q∈S, w p≠w q) → (∃ p∈S, r < 3^p) →
    r+k<∏ p ∈ S,p → t.factorial^u ≤ (r+k)^(u+1)


private theorem product_dvd (S : Finset ℕ) {m : ℕ} (pr : ∀ p∈S,p.Prime)
    (dv : ∀ p∈S,p∣m) : (∏ p ∈ S,p) ∣ m := by
  by_cases h : m=0
  · simp [h]
  have sub : S ⊆ m.primeFactors := fun p hp => Nat.mem_primeFactors.mpr ⟨pr p hp,dv p hp,h⟩
  exact (Finset.prod_dvd_prod_of_subset _ _ _ sub).trans (Nat.prod_primeFactors_dvd m)

/-- Each assignment of offsets describes at most one representative in the
interval from zero to the product of the primes, excluding the right endpoint. -/
theorem uniqueRepresentative (S : Finset ℕ) (w : ℕ → ℕ) (pr : ∀ p∈S,p.Prime)
    {a b : ℕ} (ha : a < ∏ p ∈ S,p) (hb : b < ∏ p ∈ S,p)
    (ad : ∀ p∈S,p∣a+w p) (bd : ∀ p∈S,p∣b+w p) : a=b := by
  have diff {a b : ℕ} (ab : a < b) (small : b < ∏ p ∈ S,p)
      (aH : ∀ p∈S,p∣a+w p) (bH : ∀ p∈S,p∣b+w p) : False := by
    have d := product_dvd S pr (m:=b-a) (by
      intro p hp
      simpa only [Nat.add_sub_add_right] using Nat.dvd_sub (bH p hp) (aH p hp))
    have := Nat.le_of_dvd (by omega : 0 < b-a) d
    omega
  rcases lt_trichotomy a b with h|h|h
  · exact (diff h hb ad bd).elim
  · exact h
  · exact (diff h ha bd ad).elim

private theorem blockCount (n k : ℕ) (F : ℕ → Finset ℕ)
    (prime : ∀ i∈range k, ∀ p∈F i, p.Prime ∧ p∣n+i) :
    let G := fun i => (F i).filter (fun p => k < p)
    (∑ i ∈ range k,(F i).card) ≤ ((range k).biUnion G).card+k^2 := by
  classical
  let G i := (F i).filter (fun p => k < p)
  have dis : ((range k : Finset ℕ) : Set ℕ).PairwiseDisjoint G := by
    intro i hi j hj ne
    apply disjoint_left.mpr
    intro p pi pj
    obtain ⟨fi,large⟩ := mem_filter.mp pi
    obtain ⟨fj,_⟩ := mem_filter.mp pj
    have ai := (prime i hi p fi).2
    have aj := (prime j hj p fj).2
    have iv := mem_range.mp hi
    have jv := mem_range.mp hj
    rcases lt_or_gt_of_ne ne with lt|lt
    · have d := Nat.dvd_sub aj ai
      rw [Nat.add_sub_add_left] at d
      have := Nat.le_of_dvd (by omega : 0 < j-i) d; omega
    · have d := Nat.dvd_sub ai aj
      rw [Nat.add_sub_add_left] at d
      have := Nat.le_of_dvd (by omega : 0 < i-j) d; omega
  change _ ≤ ((range k).biUnion G).card+k^2
  rw [card_biUnion dis]
  have row (i) (hi : i∈range k) : (F i).card ≤ (G i).card+k := by
    have sub : F i ⊆ G i ∪ Icc 1 k := by
      intro p hp
      by_cases lt : k < p
      · exact mem_union_left _ (mem_filter.mpr ⟨hp,lt⟩)
      · exact mem_union_right _ (mem_Icc.mpr ⟨(prime i hi p hp).1.pos,by omega⟩)
    have sz := (card_le_card sub).trans (card_union_le _ _)
    simpa using sz
  calc (∑ i ∈ range k,(F i).card) ≤ ∑ i ∈ range k,((G i).card+k) := sum_le_sum row
    _ = _ := by simp [sum_add_distrib,pow_two]


/-- Convert the integer factorial bound to the sharp logarithmic normalization. -/
private theorem factorialCase (k u : ℕ) (hu : 1 ≤ u) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (ua : 1 ≤ (u:ℝ)*a) : ∀ᶠ n : ℕ in atTop, ∀ t : ℕ,
    t.factorial^u ≤ (n+k)^(u+1) →
    (t:ℝ)*(log (log n)/log n) ≤ 1+7*a := by
  obtain ⟨Y,threshold⟩ := eventually_atTop.mp (Erdos890OmegaFC.upper_aux ha)
  have grows : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (max k 2),grows.eventually_ge_atTop (max Y (log 2/a))] with n hn hL
  intro t bound
  let L := log (n:ℝ)
  have kn := (le_max_left ..).trans hn
  have two := (le_max_right ..).trans hn
  have nr : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have lp : 0 < L := log_pos (by exact_mod_cast (by omega : 1 < n))
  have y : Y ≤ L := (le_max_left ..).trans hL
  have big : log 2/a ≤ L := (le_max_right ..).trans hL
  have ls : log ((n:ℝ)+k) ≤ (1+a)*L := by
    have kn' : (k:ℝ) ≤ n := by exact_mod_cast kn
    calc log ((n:ℝ)+k) ≤ log (2*(n:ℝ)) := log_le_log (by positivity) (by linarith)
      _ = log 2+L := log_mul (by norm_num) nr.ne'
      _ ≤ _ := by have := (div_le_iff₀ ha).mp big; linarith
  have ur : (0:ℝ) < u := by exact_mod_cast hu
  have lg : 0 ≤ log ((n:ℝ)+k) := log_nonneg (by
    have : (2:ℝ) ≤ n := by exact_mod_cast two
    have := Nat.cast_nonneg (α:=ℝ) k; linarith)
  have br : (t.factorial:ℝ)^u ≤ ((n:ℝ)+k)^(u+1) := by exact_mod_cast bound
  have logged := log_le_log (by positivity) br
  rw [log_pow,log_pow,Nat.cast_add,Nat.cast_one] at logged
  have fac : log (t.factorial:ℝ) ≤ (1+a)*log ((n:ℝ)+k) := by
    apply le_of_mul_le_mul_left (a:=(u:ℝ)) _ ur
    nlinarith only [logged,mul_nonneg (sub_nonneg.mpr ua) lg]
  have scal : (1+a)*(1+a) ≤ 1+3*a := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha1)]
  have fq : log (t.factorial:ℝ) ≤ (1+3*a)*L := calc
    _ ≤ _ := fac
    _ ≤ (1+a)*((1+a)*L) := mul_le_mul_of_nonneg_left ls (by positivity)
    _ ≤ _ := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right scal lp.le
  have inc : L ≤ (1+3*a)*L := by nlinarith [mul_nonneg ha.le lp.le]
  have upper := threshold _ (y.trans inc) t ((Erdos890OmegaFC.mul_log_sub_le_log_factorial t).trans fq)
  have logInc := log_le_log lp inc
  have positive : 0 < (1+3*a)*L := by positivity
  rw [←mul_div_assoc,div_le_iff₀ positive] at upper
  change (t:ℝ)*(log L/L) ≤ _
  rw [←mul_div_assoc,div_le_iff₀ lp]
  have lhs := mul_le_mul_of_nonneg_left logInc (Nat.cast_nonneg t)
  have hmul : (1+a)*(1+3*a) ≤ 1+7*a := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha1)]
  nlinarith only [upper,lhs,mul_le_mul_of_nonneg_right hmul lp.le]


theorem main : H1 → H2 → OMA.R_Erdos890_erdos_890_parts_b_R1.H1 := by
  classical
  intro pnt crt k hk B hB ε he
  let a := min 1 (ε/10)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1 := min_le_left .. 
  have ea : a ≤ ε/10 := min_le_right ..
  obtain ⟨u,hu⟩ := exists_nat_ge (1/a)
  have ua := (div_le_iff₀ ha).mp hu
  have up : 1 ≤ u := by
    by_contra! h; obtain rfl : u=0 := by omega
    norm_num at ua
  obtain ⟨T,gap⟩ := eventually_atTop.mp (crt k (2*B) u hk (by omega) up)
  have grows : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have vanish : Tendsto (fun x : ℝ => (k:ℝ)^2*(log x/x)) atTop (𝓝 0) := by
    simpa using (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul ((k:ℝ)^2))
  have sqroot : ∀ᶠ x : ℝ in atTop, log x ≤ sqrt x := by
    have little := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).bound (by norm_num : (0:ℝ) < 1)
    filter_upwards [little,eventually_ge_atTop (1:ℝ)] with x h hx
    change ‖log x‖ ≤ 1*‖x^((1:ℝ)/2)‖ at h
    simpa [Real.norm_of_nonneg (log_nonneg hx),Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _),
      Real.sqrt_eq_rpow] using h
  filter_upwards [eventually_ge_atTop (2:ℕ),grows.eventually_ge_atTop (max 1 ((T:ℝ)^2)),
    grows.eventually (pnt a ha),grows.eventually sqroot,
    grows.eventually (vanish.eventually_lt_const ha),factorialCase k u up a ha ha1 ua] with n hn size density sq tiny factorial
  let L := log (n:ℝ)
  let m := log L/L
  have big : 1 ≤ L := (le_max_left (1:ℝ) ((T:ℝ)^2)).trans size
  have cutoff : (T:ℝ)^2 ≤ L := (le_max_right (1:ℝ) ((T:ℝ)^2)).trans size
  have lp : 0 < L := by linarith
  have mp : 0 ≤ m := div_nonneg (log_nonneg big) lp.le
  let F (i : ℕ) := (n+i).primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ L^B)
  let G (i : ℕ) := (F i).filter (fun p => k < p)
  let S := (range k).biUnion G
  let t := S.card
  have prF i (_ : i∈range k) p (h : p∈F i) : p.Prime ∧ p∣n+i :=
    ⟨Nat.prime_of_mem_primeFactors (mem_filter.mp h).1,Nat.dvd_of_mem_primeFactors (mem_filter.mp h).1⟩
  have cnt : ∑ i ∈ range k,(F i).card ≤ t+k^2 := blockCount n k F prF
  have info p (h : p∈S) : p.Prime ∧ k < p ∧ (p:ℝ) ≤ L^B ∧ ∃ i < k, p∣n+i := by
    obtain ⟨i,hi,mem⟩ := mem_biUnion.mp h
    obtain ⟨fi,pbig⟩ := mem_filter.mp mem
    exact ⟨(prF i hi p fi).1,pbig,(mem_filter.mp fi).2,i,mem_range.mp hi,(prF i hi p fi).2⟩
  have sBound : (t:ℝ)*m ≤ 1+7*a := by
    by_cases few : (t:ℝ)^2 < L
    · have ts : (t:ℝ) ≤ sqrt L := by nlinarith [Real.sq_sqrt lp.le,Real.sqrt_nonneg L,Nat.cast_nonneg (α:=ℝ) t]
      have prod := mul_le_mul ts sq (log_nonneg big) (Real.sqrt_nonneg L)
      change (t:ℝ)*(log L/L) ≤ _
      rw [←mul_div_assoc,div_le_iff₀ lp]
      nlinarith [Real.mul_self_sqrt lp.le,mul_nonneg ha.le lp.le]
    have many : L ≤ (t:ℝ)^2 := le_of_not_gt few
    have tT : T ≤ t := by
      have : (T:ℝ) ≤ t := by nlinarith [Nat.cast_nonneg (α:=ℝ) T,Nat.cast_nonneg (α:=ℝ) t]
      exact_mod_cast this
    by_cases small : ∀ p∈S, (p:ℝ) ≤ L
    · have sub : S ⊆ Nat.primesLE ⌊L⌋₊ := by
        intro p h
        exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff lp.le).mpr (small p h),(info p h).1⟩
      have ct : (t:ℝ) ≤ (Nat.primesLE ⌊L⌋₊).card := by exact_mod_cast card_le_card sub
      have bound := (mul_le_mul_of_nonneg_right ct mp).trans density
      linarith
    push Not at small
    obtain ⟨p,hp,large⟩ := small
    obtain ⟨w,hw⟩ : ∃ w : ℕ → ℕ, ∀ q∈S, w q < k ∧ q∣n+w q := by
      have ex (q : ℕ) : ∃ i : ℕ, q∈S → i < k ∧ q∣n+i := by
        by_cases h : q∈S
        · obtain ⟨i,hi,d⟩ := (info q h).2.2.2; exact ⟨i,fun _ => ⟨hi,d⟩⟩
        · exact ⟨0,fun e => (h e).elim⟩
      choose w hw using ex
      exact ⟨w,hw⟩
    have pos : 0 < n := by omega
    let Q := ∏ q ∈ S,q
    have facQ : t.factorial ≤ Q := Erdos890OmegaFC.factorial_card_le_prod S (fun q h => (info q h).1.pos)
    apply factorial t
    by_cases largeQ : n+k < Q
    swap
    · have f := Nat.pow_le_pow_left (facQ.trans (le_of_not_gt largeQ)) u
      exact f.trans (Nat.pow_le_pow_right (by omega : 0 < n+k) (by omega))
    have mixed : ∃ i∈S, ∃ j∈S, w i≠w j := by
      by_contra no
      have alld (q) (h : q∈S) : q∣n+w p := by
        have eq : w q=w p := by by_contra ne; exact no ⟨q,h,p,hp,ne⟩
        simpa [eq] using (hw q h).2
      have bound := Nat.le_of_dvd (by omega : 0 < n+w p) (product_dvd S (fun q h => (info q h).1) alld)
      have := (hw p hp).1
      change n+k < ∏ q ∈ S,q at largeQ
      omega
    have hi : n < 3^p := by
      have nr : (0:ℝ) < n := by exact_mod_cast pos
      have y : log (n:ℝ) < log ((3:ℝ)^p) := by
        rw [log_pow]
        have one : 1 ≤ log 3 := by linarith [Real.log_three_gt_d9]
        exact large.trans_le (by simpa using mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (α:=ℝ) p))
      have z : (n:ℝ) < (3:ℝ)^p := (log_lt_log_iff nr (by positivity)).mp y
      exact_mod_cast z
    apply gap t tT S w n rfl pos _ mixed ⟨p,hp,hi⟩ largeQ
    intro q h
    obtain ⟨prime,lo,hi,_⟩ := info q h
    have cap : (q:ℝ) ≤ (t:ℝ)^(2*B) := by
      rw [pow_mul]; exact hi.trans (pow_le_pow_left₀ lp.le many B)
    exact ⟨prime,lo,by exact_mod_cast cap,(hw q h).1,(hw q h).2⟩
  change (∑ i ∈ range k,((F i).card:ℝ))*m ≤ 1+ε
  have raw : (∑ i ∈ range k,((F i).card:ℝ)) ≤ (t:ℝ)+(k:ℝ)^2 := by exact_mod_cast cnt
  have totals := mul_le_mul_of_nonneg_right raw mp
  change (k:ℝ)^2*m < a at tiny
  rw [add_mul] at totals
  linarith only [sBound,tiny,totals,ea,ha]

end OMA.R_Erdos890_erdos_890_parts_b_R1_H1_R1
