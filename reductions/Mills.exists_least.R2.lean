import FormalConjectures.Wikipedia.Mills
import Mathlib

/-!
A bounded number of sparse cubic intervals per dyadic block suffices to
construct a Mills prime chain. The prime-count input is a fixed-threshold
specialization of Matomäki's exceptional-interval theorem at exponent 2/3,
as stated by Saito in Theorem 3.7 of Mills' constant is irrational.
The nested interval and infimum arguments below are from the first reduction.
-/
namespace OMA.R_Mills_exists_least_R2

open Set Filter Real Topology Mills Finset

/-- Only disjoint intervals starting at cubes of primes are needed. For any
fixed prime-count threshold, the bound on the number of exceptions is uniform. -/
def H1 : Prop := ∃ B : ℕ, ∀ K : ℕ, ∃ N : ℕ, ∀ X ≥ N, ∀ s : Finset ℕ,
    (∀ q ∈ s, q.Prime ∧ X ≤ q^3 ∧ q^3+q^2 ≤ 2*X ∧
      ((Finset.Icc (q^3) (q^3+q^2)).filter Nat.Prime).card ≤ K) →
    s.card ≤ B

/-- Arbitrarily large dyadic intervals contain arbitrarily many primes. -/
def H2 : Prop := ∀ B N : ℕ, ∃ t ≥ N,
    B < ((Finset.Icc t (2*t)).filter Nat.Prime).card


/-- Dropping the largest base accounts for a possible interval that crosses
the right edge of a dyadic block. All earlier cubic intervals end inside it. -/
theorem startsBound {B K N : ℕ}
    (bound : ∀ X ≥ N, ∀ s : Finset ℕ,
      (∀ q ∈ s, q.Prime ∧ X ≤ q^3 ∧ q^3+q^2 ≤ 2*X ∧
        ((Finset.Icc (q^3) (q^3+q^2)).filter Nat.Prime).card ≤ K) → s.card ≤ B)
    {X : ℕ} (hX : N ≤ X) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime ∧ X ≤ q^3 ∧ q^3 ≤ 2*X ∧
      ((Finset.Icc (q^3) (q^3+q^2)).filter Nat.Prime).card ≤ K) : s.card ≤ B+1 := by
  classical
  by_cases ne : s.Nonempty
  · let m := s.max' ne
    have hm : m ∈ s := s.max'_mem ne
    have small := bound X hX (s.erase m) (by
      intro q hq
      obtain ⟨hne,hq⟩ := Finset.mem_erase.mp hq
      obtain ⟨pq,lo,_,cnt⟩ := hs q hq
      have below : q+1 ≤ m := lt_of_le_of_ne (s.le_max' q hq) hne
      have cubes : (q+1)^3 ≤ m^3 := Nat.pow_le_pow_left below 3
      exact ⟨pq,lo,(show q^3+q^2 ≤ (q+1)^3 by nlinarith).trans
        (cubes.trans (hs m hm).2.2.1),cnt⟩)
    have one := Finset.card_erase_add_one hm
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp ne]

/-- Three dyadic blocks of cube values cover all bases in a dyadic interval. -/
private theorem baseBound {B K N : ℕ}
    (bound : ∀ X ≥ N, ∀ s : Finset ℕ,
      (∀ q ∈ s, q.Prime ∧ X ≤ q^3 ∧ q^3+q^2 ≤ 2*X ∧
        ((Finset.Icc (q^3) (q^3+q^2)).filter Nat.Prime).card ≤ K) → s.card ≤ B)
    {t : ℕ} (ht : N ≤ t) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime ∧ t ≤ q ∧ q ≤ 2*t ∧
      ((Finset.Icc (q^3) (q^3+q^2)).filter Nat.Prime).card ≤ K) : s.card ≤ 3*(B+1) := by
  classical
  let X := t^3
  have hX : N ≤ X := ht.trans (Nat.le_self_pow (by decide : 3 ≠ 0) _)
  let block (y : ℕ) := s.filter (fun q => y ≤ q^3 ∧ q^3 ≤ 2*y)
  have each (y : ℕ) (h : N ≤ y) : (block y).card ≤ B+1 := by
    apply startsBound bound h
    intro q hq
    obtain ⟨mem,lo,hi⟩ := Finset.mem_filter.mp hq
    exact ⟨(hs q mem).1,lo,hi,(hs q mem).2.2.2⟩
  have cover : s ⊆ (block X ∪ block (2*X)) ∪ block (4*X) := by
    intro q hq
    obtain ⟨_,l,u,_⟩ := hs q hq
    have low : X ≤ q^3 := Nat.pow_le_pow_left l _
    have high : q^3 ≤ 8*X := calc
      q^3 ≤ (2*t)^3 := Nat.pow_le_pow_left u _
      _ = 8*X := by dsimp [X]; ring
    simp only [Finset.mem_union,block,Finset.mem_filter,hq,true_and]
    omega
  have a := Finset.card_le_card cover
  have b := Finset.card_union_le (block X ∪ block (2*X)) (block (4*X))
  have c := Finset.card_union_le (block X) (block (2*X))
  have d := each X hX
  have e := each (2*X) (by omega)
  have f := each (4*X) (by omega)
  omega


set_option maxHeartbeats 700000 in
/-- Chebyshev's elementary counting bound forces dyadic prime counts to be
unbounded, even when the initial finitely many intervals are omitted. -/
theorem dyadicRich : H2 := by
  intro B N
  by_contra! sparse
  let M := B+2*N+1
  have all (t : ℕ) : ((Finset.Icc t (2*t)).filter Nat.Prime).card ≤ M := by
    by_cases hn : N ≤ t
    · exact (sparse t hn).trans (by dsimp [M]; omega)
    · have sub : (Finset.Icc t (2*t)).filter Nat.Prime ⊆ Finset.range (2*N+1) := by
        intro p hp
        have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
        exact Finset.mem_range.mpr (by omega)
      have v := Finset.card_le_card sub
      simp only [Finset.card_range] at v
      dsimp [M]
      omega
  have count (n : ℕ) : (Nat.primesLE (2^n)).card ≤ 1+n*M := by
    induction n with
    | zero => norm_num [Nat.primesLE]
    | succ n ih =>
      let t := 2^n
      have incl : Nat.primesLE (2*t) ⊆ Nat.primesLE t ∪ (Finset.Icc t (2*t)).filter Nat.Prime := by
        intro p hp
        obtain ⟨le,pr⟩ := Nat.mem_primesLE.mp hp
        by_cases lh : p ≤ t
        · exact Finset.mem_union_left _ (Nat.mem_primesLE.mpr ⟨lh,pr⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,le⟩,pr⟩)
      have u := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
      have v := all t
      change (Nat.primesLE t).card ≤ 1+n*M at ih
      rw [pow_succ, Nat.mul_comm (2^n) 2, Nat.succ_mul n M]
      change (Nat.primesLE (2*t)).card ≤ _
      omega
  have cube (n : ℕ) (hn : 10 ≤ n) : n^3 ≤ 2^n := by
    induction n, hn using Nat.le_induction with
    | base => decide
    | succ n hn ih =>
      have a := Nat.mul_le_mul_right (n^2) (by omega : 5 ≤ n)
      have b := Nat.mul_le_mul_right n (by omega : 5 ≤ n)
      have c : (n+1)^3 ≤ 2*n^3 := by nlinarith only [a,b,hn]
      rw [pow_succ 2]
      omega
  let n := M+12
  let y := 2^n
  have npos : 0 < n := by dsimp [n]; omega
  have ybig : 1 < y := one_lt_pow₀ (by decide) npos.ne'
  have hy : (1:ℝ) < y := by exact_mod_cast ybig
  have log2 : 0 < log 2 := log_pos (by norm_num)
  have atY := (div_le_iff₀ (log_pos hy)).mp (Chebyshev.pi_ge y)
  have logY : log (y:ℝ) = (n:ℝ)*log 2 := by simp [y,Real.log_pow]
  have up : log ((y:ℝ)+1) ≤ ((n:ℝ)+1)*log 2 := calc
    _ ≤ log ((2:ℝ)^(n+1)) := by
      apply Real.log_le_log (by positivity)
      rw [pow_succ]
      have eqy : (y:ℝ)=(2:ℝ)^n := by simp [y]
      linarith [hy,eqy]
    _ = _ := by rw [Real.log_pow]; push_cast; rfl
  rw [logY] at atY
  have lc : (y:ℝ) ≤ (y.primeCounting:ℝ)*n+(n+1) := by
    apply (le_of_mul_le_mul_right _ log2)
    nlinarith only [atY,up]
  have lcN : y ≤ y.primeCounting*n+(n+1) := by exact_mod_cast lc
  have c := count n
  rw [Nat.primesLE_card_eq_primeCounting] at c
  have cc : y.primeCounting*n ≤ (1+n*M)*n := Nat.mul_le_mul_right n c
  have v := cube n (by dsimp [n]; omega)
  change n^3 ≤ y at v
  have gap : (1+n*M)*n+(n+1) < n^3 := by
    dsimp [n]
    ring_nf
    omega
  omega

-- The floors at the infimum agree individually with floors just to its right.
lemma least_of_exists (existsM : ∃ x > (1:ℝ), IsMills x) : ∃ x, IsMinMills x := by
  let S : Set ℝ := {x | x > 1 ∧ IsMills x}
  have non : S.Nonempty := existsM
  have lower : ∀ x ∈ S, 5/4 ≤ x := by
    intro x hx
    have h := (Nat.prime_iff.mpr (hx.2 (1:ℕ+))).two_le
    have hfloor : 2 ≤ ⌊x^3⌋₊ := by simpa using h
    have hpow : (2:ℝ) ≤ x^3 := by
      simpa using (Nat.le_floor_iff (pow_nonneg (by linarith [hx.1] : 0≤x) 3)).mp hfloor
    by_contra! no
    have upper : x^3 ≤ (5/4:ℝ)^3 := pow_le_pow_left₀ (zero_le_one.trans hx.1.le) no.le 3
    linarith
  have bd : BddBelow S := ⟨5/4, lower⟩
  let b := sInf S
  have hb : 5/4 ≤ b := le_csInf non lower
  have bp : 0 < b := by linarith
  refine ⟨b,⟨⟨by linarith,?_⟩,fun x hx => csInf_le bd hx⟩⟩
  intro n
  let m := 3^(n:ℕ)
  let k := ⌊b^m⌋₊
  have below : b^m < (k:ℝ)+1 := Nat.lt_floor_add_one (b^m)
  have near : {x : ℝ | x^m < (k:ℝ)+1} ∈ 𝓝 b :=
    ((continuous_id.pow m).continuousAt.eventually_lt continuousAt_const below)
  obtain ⟨x,hx,hS⟩ := mem_closure_iff_nhds.mp (csInf_mem_closure non bd) _ near
  have lo : b^m ≤ x^m := pow_le_pow_left₀ bp.le (csInf_le bd hS) m
  have same : ⌊x^m⌋₊ = k := Nat.le_antisymm
    (Nat.lt_succ_iff.mp ((Nat.floor_lt (pow_nonneg (by linarith [hS.1] : (0:ℝ)≤x) m)).mpr (by simpa using hx)))
    (Nat.floor_mono lo)
  change Prime k
  rw [← same]
  exact hS.2 n

lemma exists_of_chain (q : ℕ → ℕ) (pr : ∀ n, (q n).Prime)
    (lo : ∀ n, q n ^ 3 ≤ q (n+1)) (hi : ∀ n, q (n+1)+1 < (q n + 1)^3) :
    ∃ A > (1:ℝ), IsMills A := by
  let d (n : ℕ) := 3^(n+1)
  let l (n : ℕ) := (q n:ℝ)^((d n:ℝ)⁻¹)
  let u (n : ℕ) := ((q n:ℝ)+1)^((d n:ℝ)⁻¹)
  have dpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have lpos (n : ℕ) : 0 ≤ l n := rpow_nonneg (by positivity) _
  have upos (n : ℕ) : 0 ≤ u n := rpow_nonneg (by positivity) _
  have lp (n : ℕ) : l n ^ d n = (q n:ℝ) := rpow_inv_natCast_pow (by positivity) (dpos n).ne'
  have up (n : ℕ) : u n ^ d n = (q n:ℝ)+1 := rpow_inv_natCast_pow (by positivity) (dpos n).ne'
  have deq (n : ℕ) : d (n+1) = d n * 3 := by dsimp [d]; rw [pow_succ 3 (n+1)]
  have increasing : Monotone l := monotone_nat_of_le_succ fun n => by
    apply (pow_le_pow_iff_left₀ (lpos n) (lpos (n+1)) (dpos (n+1)).ne').mp
    rw [lp (n+1), deq, pow_mul, lp]
    exact_mod_cast lo n
  have decreasing : StrictAnti u := strictAnti_nat_of_succ_lt fun n => by
    apply (pow_lt_pow_iff_left₀ (upos (n+1)) (upos n) (dpos (n+1)).ne').mp
    rw [up (n+1), deq, pow_mul, up]
    exact_mod_cast hi n
  have sep (n : ℕ) : l n < u n :=
    rpow_lt_rpow (by positivity) (lt_add_one _) (inv_pos.mpr (by exact_mod_cast dpos n))
  have all (m n : ℕ) : l m ≤ u n := by
    rcases le_total m n with h | h
    · exact (increasing h).trans (sep n).le
    · exact (sep m).le.trans (decreasing.antitone h)
  have bounded : BddAbove (Set.range l) := ⟨u 0, by rintro _ ⟨m,rfl⟩; exact all m 0⟩
  let A := sSup (Set.range l)
  have low (n : ℕ) : l n ≤ A := le_csSup bounded ⟨n,rfl⟩
  have high (n : ℕ) : A < u n := (csSup_le (Set.range_nonempty _) (by
    rintro _ ⟨m,rfl⟩
    exact all m (n+1))).trans_lt (decreasing (Nat.lt_succ_self n))
  have first : 1 < l 0 := one_lt_rpow (by exact_mod_cast (pr 0).one_lt) (by
    exact inv_pos.mpr (by exact_mod_cast dpos 0))
  have hA := first.trans_le (low 0)
  refine ⟨A,hA,?_⟩
  intro n
  obtain ⟨j,hj⟩ := n
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  change Prime ⌊A^(d k)⌋₊
  have lw := pow_le_pow_left₀ (lpos k) (low k) (d k)
  have hw := pow_lt_pow_left₀ (high k) (zero_le_one.trans hA.le) (dpos k).ne'
  rw [lp] at lw
  rw [up] at hw
  have val : ⌊A^(d k)⌋₊ = q k := Nat.le_antisymm
    (Nat.lt_succ_iff.mp ((Nat.floor_lt (by positivity)).mpr (by simpa using hw)))
    (Nat.le_floor lw)
  rw [val]
  exact (pr k).prime



/-- A rich set of prime bases contains a prime with a rich set of children.
The same counting argument supplies both the seed and every successor. -/
theorem main : H1 → H2 → type_of% @Mills.exists_least := by
  classical
  intro exc rich
  obtain ⟨B,uniform⟩ := exc
  let K := 3*(B+1)
  obtain ⟨N,bound⟩ := uniform K
  let children (p : ℕ) := (Finset.Icc (p^3) (p^3+p^2)).filter Nat.Prime
  have pick {t : ℕ} (ht : N ≤ t) (s : Finset ℕ) (hs : K < s.card)
      (loc : ∀ q ∈ s, q.Prime ∧ t ≤ q ∧ q ≤ 2*t) :
      ∃ q ∈ s, K < (children q).card := by
    by_contra! fail
    apply (Nat.not_le_of_gt hs)
    apply baseBound bound ht
    intro q hq
    exact ⟨(loc q hq).1,(loc q hq).2.1,(loc q hq).2.2,fail q hq⟩
  obtain ⟨t,ht,full⟩ := rich K N
  obtain ⟨p,hp,good⟩ := pick ht _ full (by
    intro q hq
    obtain ⟨ii,pq⟩ := Finset.mem_filter.mp hq
    exact ⟨pq,(Finset.mem_Icc.mp ii).1,(Finset.mem_Icc.mp ii).2⟩)
  obtain ⟨pi,pp⟩ := Finset.mem_filter.mp hp
  let S := {q : ℕ // q.Prime ∧ N ≤ q ∧ K < (children q).card}
  let seed : S := ⟨p,pp,ht.trans (Finset.mem_Icc.mp pi).1,good⟩
  have succ (a : S) : ∃ b : S, a.val^3 ≤ b.val ∧ b.val+1 < (a.val+1)^3 := by
    let q := a.val
    have q1 : 1 ≤ q := le_trans (by decide : 1 ≤ 2) a.prop.1.two_le
    have grow : q ≤ q^3 := Nat.le_self_pow (by decide : 3 ≠ 0) _
    have sq : q^2 ≤ q^3 := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3)
    obtain ⟨r,hr,large⟩ := pick (a.prop.2.1.trans grow) (children q) a.prop.2.2 (by
      intro r hr
      obtain ⟨ii,pr⟩ := Finset.mem_filter.mp hr
      obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp ii
      exact ⟨pr,lo,by omega⟩)
    obtain ⟨ii,pr⟩ := Finset.mem_filter.mp hr
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp ii
    refine ⟨⟨r,pr,(a.prop.2.1.trans grow).trans lo,large⟩,lo,?_⟩
    change r+1 < (q+1)^3
    nlinarith
  let F (a : S) := (succ a).choose
  let chain (n : ℕ) := (F^[n]) seed
  have next (n : ℕ) : chain (n+1) = F (chain n) := Function.iterate_succ_apply' ..
  apply least_of_exists
  apply exists_of_chain (fun n => (chain n).val) (fun n => (chain n).prop.1)
  · intro n
    rw [next]
    exact ((succ (chain n)).choose_spec).1
  · intro n
    rw [next]
    exact ((succ (chain n)).choose_spec).2

end OMA.R_Mills_exists_least_R2
