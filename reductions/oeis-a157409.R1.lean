import OMAStatements.S_oeis_a157409
import Mathlib

/-!
Luschny's conjecture (OEIS A157409). Reduction by @physbuzz.
For positive exponents the failure condition is exactly avoidance of adjacent
ternary digits 12 in the preceding power of two. This gives Erdős's ternary
digit conjecture as a necessary step. See Jeffrey Lagarias, Ternary expansions
of powers of 2 (2009), and Roger Saye, On Two Conjectures Concerning the Ternary
Digits of Powers of Two (2022). A separate unconditional counting argument
shows that exceptional exponents have asymptotic density zero.
-/
namespace OMA.R_oeis_a157409_R1
/-- An arithmetic witness for twice x exists exactly when the adjacent digits 12 occur in x. -/
lemma adjacent (x : ℕ) :
    (∃ k : ℕ, 0<k ∧ 2*x/3^k%6=3) ↔ ∃ j : ℕ, x/3^j%9=5 := by
  have half (j : ℕ) : 2*x/3^j/2=x/3^j := by
    rw [Nat.div_div_eq_div_mul,Nat.mul_comm (3^j) 2,← Nat.div_div_eq_div_mul]
    simp
  constructor
  · rintro ⟨k,pk,eq⟩
    induction k with
    | zero => omega
    | succ j ih =>
      rw [pow_succ,←Nat.div_div_eq_div_mul] at eq
      by_cases prev : 2*x/3^j%6=3
      · apply ih _ prev
        by_contra! zero
        have : j=0 := by omega
        simp [this] at prev
        omega
      · exact ⟨j,by rw [←half]; omega⟩
  · rintro ⟨j,h⟩
    rw [←half] at h
    exact ⟨j+1,by omega,by rw [pow_succ,←Nat.div_div_eq_div_mul]; omega⟩
private lemma period_dvd {m t : ℕ} (h : 2^t ≡ 1 [MOD 3^(m+1)]) :
    2*3^m ∣ t := by
  have hm : 3 ∣ 3^(m+1) := by simp [pow_succ]
  have mod3 := h.of_dvd hm
  have par : Even t := by
    rcases Nat.even_or_odd t with et | ⟨u,rfl⟩
    · exact et
    · exfalso
      have four : 4^u ≡ 1 [MOD 3] := by simpa using (show 4 ≡ 1 [MOD 3] by decide).pow u
      have eq : 2^(2*u+1) ≡ 2 [MOD 3] := by
        rw [pow_succ,pow_mul]
        simpa using four.mul_right 2
      exact (by decide : ¬ 2 ≡ 1 [MOD 3]) (eq.symm.trans mod3)
  obtain ⟨u,e⟩ := par
  by_cases zero : u=0
  · simp [e,zero]
  have hu : 0<u := by omega
  have form : 2^t = 4^u := by rw [e,show u+u=2*u by omega,pow_mul]; rfl
  have val : padicValNat 3 (4^u-1) = 1 + padicValNat 3 u := by
    simpa using padicValNat.pow_sub_pow (p := 3) (by decide) (x := 4) (y := 1)
      (by decide) (by decide) (by decide) zero
  have nz : 4^u-1≠0 := by have := one_lt_pow' (by decide : 1<4) zero; omega
  rw [form] at h
  have divis := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by decide) : 1≤4^u)).mp h.symm
  have le := (padicValNat_dvd_iff_le (p := 3) nz).mp divis
  have sub := (padicValNat_dvd_iff_le (p := 3) zero).mpr (show m≤padicValNat 3 u by omega)
  obtain ⟨v,hv⟩ := sub
  exact ⟨v,by rw [e,hv]; ring⟩

lemma pow_injective (m : ℕ) : Set.InjOn (fun i : ℕ => 2^(i+1)%(2*3^(m+1)))
    (Set.Iio (2*3^m)) := by
  intro a ha b hb eq
  have increasing (a b : ℕ) (small : a<b) (lim : b<2*3^m)
      (same : 2^(a+1)%(2*3^(m+1))=2^(b+1)%(2*3^(m+1))) : False := by
    have eq3 : 2^(a+1) ≡ 2^(b+1) [MOD 3^(m+1)] :=
      (show 2^(a+1) ≡ 2^(b+1) [MOD 2*3^(m+1)] from same).of_dvd (dvd_mul_left _ _)
    have e : b+1=(a+1)+(b-a) := by omega
    rw [e,pow_add 2 (a+1) (b-a)] at eq3
    have cop : Nat.Coprime (3^(m+1)) (2^(a+1)) := (by decide : Nat.Coprime 3 2).pow_left _ |>.pow_right _
    have hp := Nat.ModEq.cancel_left_of_coprime cop (show 2^(a+1)*2^(b-a) ≡ 2^(a+1)*1 [MOD 3^(m+1)] by simpa only [Nat.mul_one] using eq3.symm)
    have d := period_dvd hp
    have := Nat.le_of_dvd (show 0<b-a by omega) d
    omega
  rcases lt_trichotomy a b with lt | eq | gt
  · exact (increasing _ _ lt hb eq).elim
  · exact eq
  · exact (increasing _ _ gt ha eq.symm).elim
private lemma lengths (survivors : ℕ → List ℕ × List ℕ)
    (start : survivors 0=(([2],[4]) : List ℕ × List ℕ))
    (step : ∀ j : ℕ,survivors (j+1) =
    let d := 3^(j+1)
    let (low,high) := survivors j
    (low ++ low.map (·+2*d) ++ high, low.map (·+4*d) ++ high.map (·+4*d)))
    (j : ℕ) : (survivors j).1.length=Nat.fib (2*j+2) ∧
    (survivors j).2.length=Nat.fib (2*j+1) := by
  induction j with
  | zero => rw [start]; decide
  | succ j ih =>
    obtain ⟨l,h⟩ := ih
    simp only [step,List.length_append,List.length_map,l,h]
    have f := @Nat.fib_add_two (2*j+1)
    have g := @Nat.fib_add_two (2*j+2)
    rw [show 2*(j+1)+2=(2*j+2)+2 by omega,show 2*(j+1)+1=(2*j+1)+2 by omega]
    simp only [Nat.add_assoc] at f g ⊢
    norm_num at f g ⊢
    omega

private lemma covers (survivors : ℕ → List ℕ × List ℕ)
    (start : survivors 0=(([2],[4]) : List ℕ × List ℕ))
    (step : ∀ j : ℕ,survivors (j+1) =
    let d := 3^(j+1)
    let (low,high) := survivors j
    (low ++ low.map (·+2*d) ++ high, low.map (·+4*d) ++ high.map (·+4*d)))
    (j x : ℕ) (initial : x%6=2 ∨ x%6=4)
    (safe : ∀ k : ℕ, 0<k → x/3^k%6≠3) :
    let d := 3^(j+1)
    let r := x%(2*d)
    (r<d ∧ r∈(survivors j).1) ∨ (d≤r ∧ r∈(survivors j).2) := by
  induction j with
  | zero =>
    rw [start]
    rcases initial with h | h
    · left
      change x%6<3 ∧ x%6∈[2]
      simp [h]
    · right
      change 3≤x%6 ∧ x%6∈[4]
      simp [h]
  | succ j ih =>
    let d := 3^(j+1)
    let r := x%(2*d)
    let z := x%(6*d)
    have dp : 0<d := by dsimp [d]; positivity
    have next : 3^(j+1+1)=3*d := by dsimp [d]; ring
    have size : 0≤r ∧ r<2*d := ⟨Nat.zero_le _,Nat.mod_lt _ (by omega)⟩
    have small : z<6*d := Nat.mod_lt _ (by omega)
    have eq : z%(2*d)=r := by
      exact Nat.mod_mod_of_dvd _ (show 2*d ∣ 6*d from ⟨3,by ring⟩)
    have decomp := Nat.mod_add_div z (2*d)
    rw [eq] at decomp
    have digit : z/d≠3 := by
      have h := safe (j+1) (by omega)
      change x/d%6≠3 at h
      rwa [← Nat.mod_mul_right_div_self, Nat.mul_comm d 6] at h
    have two : z/(2*d)<3 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    dsimp only
    rw [next,show 2*(3*d)=6*d by ring]
    change (z<3*d ∧ z∈(survivors (j+1)).1) ∨ (3*d≤z ∧ z∈(survivors (j+1)).2)
    rcases ih with ⟨hr,mem⟩ | ⟨hr,mem⟩
    · change r<d at hr
      change r∈(survivors j).1 at mem
      interval_cases off : z/(2*d)
      · left; constructor
        · omega
        · simp only [step,List.mem_append,List.mem_map]
          exact Or.inl (Or.inl (by simpa [←decomp] using mem))
      · left; constructor
        · omega
        · simp only [step,List.mem_append,List.mem_map]
          exact Or.inl (Or.inr ⟨r,mem,by dsimp [d] at decomp ⊢; omega⟩)
      · right; constructor
        · omega
        · simp only [step,List.mem_append,List.mem_map]
          exact Or.inl ⟨r,mem,by dsimp [d] at decomp ⊢; omega⟩
    · change d≤r at hr
      change r∈(survivors j).2 at mem
      interval_cases off : z/(2*d)
      · left; constructor
        · omega
        · simp only [step,List.mem_append,List.mem_map]
          exact Or.inr (by simpa [←decomp] using mem)
      · exact False.elim (digit (Nat.div_eq_of_lt_le (by omega) (by omega)))
      · right; constructor
        · omega
        · simp only [step,List.mem_append,List.mem_map]
          exact Or.inr ⟨r,mem,by dsimp [d] at decomp ⊢; omega⟩
open Finset Filter
open scoped Topology

lemma fib_count (j N : ℕ) (lim : N≤2*3^j) (s : Finset ℕ)
    (range : ∀ i∈s, i<N)
    (safe : ∀ i∈s, ∀ k : ℕ,0<k → 2^(i+1)/3^k%6≠3) :
    s.card≤Nat.fib (2*j+3) := by
  let survivors : ℕ → List ℕ × List ℕ := Nat.rec (([2],[4]) : List ℕ × List ℕ) (fun j prev =>
      let d := 3^(j+1)
      let (low,high) := prev
      (low ++ low.map (·+2*d) ++ high, low.map (·+4*d) ++ high.map (·+4*d)))
  have start : survivors 0=(([2],[4]) : List ℕ × List ℕ) := rfl
  have step (j : ℕ) : survivors (j+1) =
    let d := 3^(j+1)
    let (low,high) := survivors j
    (low ++ low.map (·+2*d) ++ high, low.map (·+4*d) ++ high.map (·+4*d)) := rfl
  let f := fun i : ℕ => 2^(i+1)%(2*3^(j+1))
  let xs := (survivors j).1 ++ (survivors j).2
  have maps : Set.MapsTo f s xs.toFinset := by
    intro i hi
    have initial : 2^(i+1)%6=2 ∨ 2^(i+1)%6=4 := by
      clear hi
      induction i with
      | zero => decide
      | succ i ih =>
        rw [pow_succ,Nat.mul_mod]
        rcases ih with a | a <;> simp [a]
    obtain ⟨_,h⟩ | ⟨_,h⟩ := covers survivors start step j _ initial (safe i hi)
    · exact List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl h))
    · exact List.mem_toFinset.mpr (List.mem_append.mpr (Or.inr h))
  have inj : Set.InjOn f s := (pow_injective j).mono (fun i hi => lt_of_lt_of_le (range i hi) lim)
  have card := (Finset.card_le_card_of_injOn f maps inj).trans (List.toFinset_card_le xs)
  change s.card≤((survivors j).1 ++ (survivors j).2).length at card
  rw [List.length_append,(lengths survivors start step j).1,(lengths survivors start step j).2] at card
  have e := @Nat.fib_add_two (2*j+1)
  have : Nat.fib (2*j+3)=Nat.fib (2*j+1)+Nat.fib (2*j+2) := e
  omega

lemma fib_growth (j : ℕ) : Nat.fib (4*j+3) ≤ 2*8^j := by
  induction j with
  | zero => decide
  | succ j ih =>
    have a := @Nat.fib_add_two (4*j+1)
    have b := @Nat.fib_add_two (4*j+2)
    have c := @Nat.fib_add_two (4*j+3)
    have d := @Nat.fib_add_two (4*j+4)
    have e := @Nat.fib_add_two (4*j+5)
    simp only [Nat.add_assoc] at a b c d e
    norm_num at a b c d e
    rw [pow_succ,show 4*(j+1)+3=4*j+7 by omega]
    omega

open scoped Classical in
lemma quantitative (N : ℕ) : ((Finset.range N).filter (fun i => ∀ k : ℕ,0<k → 2^(i+1)/3^k%6≠3)).card≤16*8^(Nat.log 9 N) := by
  classical
  let j := Nat.log 9 N
  have bound : N≤2*3^(2*(j+1)) := by
    have raw := Nat.lt_pow_succ_log_self (by decide : 1<9) N
    rw [pow_mul]; change N≤2*9^(j+1); change N<9^(j+1) at raw; omega
  have hc := fib_count (2*(j+1)) N bound ((Finset.range N).filter (fun i => ∀ k : ℕ,0<k → 2^(i+1)/3^k%6≠3))
    (fun i hi => Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  have g := fib_growth (j+1)
  rw [show 2*(2*(j+1))+3=4*(j+1)+3 by ring] at hc
  rw [pow_succ] at g
  change ((Finset.range N).filter (fun i => ∀ k : ℕ,0<k → 2^(i+1)/3^k%6≠3)).card≤16*8^j
  omega

open scoped Classical in
theorem density_zero : Tendsto (fun N : ℕ => (((Finset.range N).filter (fun i => ∀ k : ℕ,0<k → 2^(i+1)/3^k%6≠3)).card : ℝ)/N) atTop (𝓝 0) := by
  have ltlog : Tendsto (Nat.log 9) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (9^b)] with n hn
    exact (Nat.le_log_iff_pow_le (by decide) (by have := Nat.one_le_pow b 9 (by decide); omega)).mpr hn
  have decay : Tendsto (fun n : ℕ => (8/9:ℝ)^(Nat.log 9 n)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp ltlog
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have q : (((Finset.range n).filter (fun i => ∀ k : ℕ,0<k → 2^(i+1)/3^k%6≠3)).card:ℝ)≤16*(8:ℝ)^(Nat.log 9 n) := by exact_mod_cast quantitative n
    have p : (9:ℝ)^(Nat.log 9 n)≤n := by exact_mod_cast Nat.pow_log_le_self 9 (by omega : n≠0)
    have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    calc
      _ ≤ (16*(8:ℝ)^(Nat.log 9 n))/(9:ℝ)^(Nat.log 9 n) :=
        div_le_div₀ (by positivity) q (by positivity) p
      _ = 16*(8/9:ℝ)^(Nat.log 9 n) := by rw [div_pow]; ring
  · simpa using (tendsto_const_nhds (x := (16:ℝ))).mul decay
/-- Erdős's ternary-digit conjecture for powers of two. -/
def H1 : Prop := ∀ m : ℕ, (∀ j : ℕ, 2^m/3^j%3≠2) → m=0 ∨ m=2 ∨ m=8

/-- Beyond the finite exceptions, a power containing the digit 2 has an adjacent 12. -/
def H2 : Prop := ∀ m : ℕ, 25 < m → (∃ j : ℕ, 2^m/3^j%3=2) →
    ∃ j : ℕ, 2^m/3^j%9=5

private lemma small_exact {n : ℕ} (lim : n≤26) :
    (¬∃ k : ℕ,0<k ∧ 2^n/3^k%6=3) ↔ n∈({0,1,2,3,4,7,9,10,14,15,17,26} : Set ℕ) := by
  have check : ∀ n : Fin 27, (∀ k : Fin 27,0<k.val → 2^n.val/3^k.val%6≠3) ↔
      n.val∈({0,1,2,3,4,7,9,10,14,15,17,26} : Set ℕ) := by decide +kernel
  have finite := check ⟨n,by omega⟩
  constructor
  · intro h
    exact finite.mp (fun k pos eq => h ⟨k,pos,eq⟩)
  · intro h ⟨k,pos,eq⟩
    by_cases small : k<27
    · exact (finite.mpr h) ⟨k,small⟩ pos eq
    · have bound := Nat.pow_le_pow_right (by decide : 0<2) lim
      have grow := Nat.pow_le_pow_right (by decide : 0<3) (show 27≤k by omega)
      have gap : 2^26<3^27 := by decide
      rw [Nat.div_eq_of_lt (lt_of_le_of_lt bound (lt_of_lt_of_le gap grow))] at eq
      contradiction

/-- Conversely, Luschny's predicted large-n witnesses imply both steps, including Erdős's conjecture. -/
lemma both_necessary (large : ∀ n : ℕ,26<n → ∃ k : ℕ,0<k ∧ 2^n/3^k%6=3) : H1 ∧ H2 := by
  have hasPair (m : ℕ) (hm : 25 < m) : ∃ j, 2^m/3^j%9=5 := by
    apply (adjacent (2^m)).mp
    simpa only [pow_succ',Nat.mul_comm] using large (m+1) (by omega)
  constructor
  · intro m missing
    by_cases small : m≤25
    · have finite : ∀ m : Fin 26, (∀ j : Fin 26,2^m.val/3^j.val%3≠2) →
          m.val=0 ∨ m.val=2 ∨ m.val=8 := by decide +kernel
      exact finite ⟨m,by omega⟩ (fun j => missing j.val)
    · obtain ⟨j,pair⟩ := hasPair m (by omega)
      exact False.elim (missing j (by omega))
  · exact fun m hm _ => hasPair m hm

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a157409.main := by
  intro h1 h2
  ext n
  change (¬ ∃ k : ℕ,0<k ∧ 2^n/3^k%6=3) ↔ _
  by_cases small : n≤26
  · exact small_exact small
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    have two : ∃ j : ℕ,2^m/3^j%3=2 := by
      by_contra! no
      rcases h1 m no with a | a | a <;> omega
    have pair := h2 m (by omega) two
    have w := (adjacent (2^m)).mpr pair
    rw [←pow_succ'] at w
    constructor
    · intro no
      exact (no w).elim
    · intro mem
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at mem
      omega

end OMA.R_oeis_a157409_R1
