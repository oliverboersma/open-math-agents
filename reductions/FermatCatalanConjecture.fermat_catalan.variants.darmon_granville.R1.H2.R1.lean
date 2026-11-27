import OMAReductions.R_FermatCatalanConjecture_fermat_catalan_variants_darmon_granville_R1
import Mathlib

/-! Elementary normalization of the rational parameter in the generalized
Fermat equation. Set-based pairwise coprimality permits coincident bases.
The rational conditions are the ramification conditions away from the
exceptional primes dividing the product of the exponents; see Hugo
Chapdelaine, Non-abelian descent and the generalized Fermat equation.
Fermat's quartic descent eliminates an entire family in the positive branch. -/
namespace FermatParameter

lemma diagonal {d m n k : ℕ} (pos : 0 < d) (h : d^m+d^n=d^k) : d ≤ 2 := by
  by_contra! large
  have ordered {i j : ℕ} (le : i ≤ j) (e : d^i + d^j = d^k) : False := by
    have ip : 0 < d^i := pow_pos pos _
    have jp : 0 < d^j := pow_pos pos _
    have ik : i < k := by
      by_contra! low
      have u := Nat.pow_le_pow_right pos low
      omega
    have red : 1+d^(j-i)=d^(k-i) := by
      apply Nat.eq_of_mul_eq_mul_left ip
      rw [Nat.mul_add,Nat.mul_one,←pow_add,←pow_add,
        Nat.add_sub_of_le le,Nat.add_sub_of_le ik.le]
      exact e
    have dr : d ∣ d^(k-i) := dvd_pow_self d (by omega)
    by_cases eq : j=i
    · subst j
      simp at red
      have two : d ∣ 2 := red ▸ dr
      exact (Nat.le_of_dvd (by decide : 0 < 2) two).not_gt large
    · have dl : d ∣ d^(j-i) := dvd_pow_self d (by omega)
      rw [←red] at dr
      have one := (Nat.dvd_add_iff_left dl).mpr dr
      have := Nat.le_of_dvd Nat.zero_lt_one one
      omega
  rcases le_total m n with le|le
  · exact ordered le h
  · exact ordered le ((Nat.add_comm ..).trans h)

lemma primitive_or_small {a b c m n k : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (eq : a^m+b^n=c^k)
    (pair : ({a,b,c} : Set ℕ).Pairwise Nat.Coprime) :
    (a.Coprime c ∧ b.Coprime c ∧ a.Coprime b) ∨ (a ≤ 2 ∧ b ≤ 2 ∧ c ≤ 2) := by
  by_cases same : a=b ∧ b=c
  · obtain ⟨rfl,rfl⟩ := same
    have u := diagonal ha eq
    exact Or.inr ⟨u,u,u⟩
  left
  have raw {u v : ℕ} (hu : u∈({a,b,c} : Set ℕ)) (hv : v∈({a,b,c} : Set ℕ))
      (ne : u≠v) : u.Coprime v := pair hu hv ne
  have ac : a.Coprime c := by
    by_cases e : a=c
    · subst c
      have ab : a ≠ b := by rintro rfl; exact same ⟨rfl,rfl⟩
      have da : a ∣ a^m := dvd_pow_self _ (by omega)
      have dk : a ∣ a^k := dvd_pow_self _ (by omega)
      rw [←eq] at dk
      have one := ((raw (by simp) (by simp) ab).pow_right n).eq_one_of_dvd ((Nat.dvd_add_iff_right da).mpr dk)
      simp [one]
    · exact raw (by simp) (by simp) e
  have bc : b.Coprime c := by
    by_cases e : b=c
    · subst c
      have ba : b ≠ a := by rintro rfl; exact same ⟨rfl,rfl⟩
      have db : b ∣ b^n := dvd_pow_self _ (by omega)
      have dk : b ∣ b^k := dvd_pow_self _ (by omega)
      rw [←eq] at dk
      have one := ((raw (by simp) (by simp) ba).pow_right m).eq_one_of_dvd ((Nat.dvd_add_iff_left db).mpr dk)
      simp [one]
    · exact raw (by simp) (by simp) e
  refine ⟨ac,bc,?_⟩
  by_cases e : a=b
  · subst b
    have dv : a ∣ c^k := eq ▸ dvd_add (dvd_pow_self _ (by omega)) (dvd_pow_self _ (by omega))
    simp [(ac.pow_right k).eq_one_of_dvd dv]
  · exact raw (by simp) (by simp) e

lemma coordinates {x y : ℕ} (hy : y>0) (h : x.Coprime y) :
    ((x:ℚ)/y).num.natAbs = x ∧ ((x:ℚ)/y).den = y := by
  have pos : 0 < (y:ℤ) := by exact_mod_cast hy
  have cop : (x:ℤ).natAbs.Coprime (y:ℤ).natAbs := h
  have num := Rat.num_div_eq_of_coprime pos cop
  have den := Rat.den_div_eq_of_coprime pos cop
  constructor
  · simpa using congrArg Int.natAbs num
  · simpa using congrArg Int.toNat den

end FermatParameter

namespace FermatParameter

lemma fourths {a b c m n k : ℕ} (ha : 0<a) (hb : 0<b)
    (hm : 4 ∣ m) (hn : 4 ∣ n) (hk : 2 ∣ k) :
    a^m + b^n ≠ c^k := by
  obtain ⟨u,rfl⟩ := hm
  obtain ⟨v,rfl⟩ := hn
  obtain ⟨w,rfl⟩ := hk
  intro e
  have e' : ((a^u : ℕ):ℤ)^4 + ((b^v : ℕ):ℤ)^4 = ((c^w : ℕ):ℤ)^2 := by
    exact_mod_cast (show (a^u)^4+(b^v)^4=(c^w)^2 by simpa [← pow_mul,Nat.mul_comm] using e)
  exact not_fermat_42 (by positivity) (by positivity) e'

lemma power_valuation (a n p : ℕ) : n ∣ (a^n).factorization p := by
  simp [Nat.factorization_pow,Finsupp.smul_apply]

lemma bound {S : Set ℚ} (h : S.Finite) :
    ∃ M : ℕ, ∀ t ∈ S, t.num.natAbs ≤ M ∧ t.den ≤ M := by
  obtain ⟨M,hM⟩ := (h.image (fun t => t.num.natAbs + t.den)).bddAbove
  exact ⟨M,fun t ht => by have := hM (Set.mem_image_of_mem _ ht); omega⟩

end FermatParameter

namespace OMA.R_FermatCatalanConjecture_fermat_catalan_variants_darmon_granville_R1_H2_R1
open FermatParameter

/-- The square is on the right of the positive equation. The quartic-quartic
subcase has already been eliminated by Fermat's descent. -/
def H1 : Prop := ∀ m n : ℕ, 2 ≤ m → 2 ≤ n → 1/(m:ℝ)+1/n+1/2<1 →
    ¬(4 ∣ m ∧ 4 ∣ n) →
    {t : ℚ | 0<t ∧ t<1 ∧ ∀ p : ℕ, p.Prime → ¬p ∣ 2*m*n →
      m ∣ t.num.natAbs.factorization p ∧
      n ∣ (1-t).num.natAbs.factorization p ∧ 2 ∣ t.den.factorization p}.Finite

/-- Invert the parameter when the square is a summand. This places the
ramification of order two at infinity in both branches. -/
def H2 : Prop := ∀ m n : ℕ, 2 ≤ m → 2 ≤ n → 1/(m:ℝ)+1/n+1/2<1 →
    {t : ℚ | 1<t ∧ ∀ p : ℕ, p.Prime → ¬p ∣ 2*m*n →
      m ∣ t.num.natAbs.factorization p ∧
      n ∣ (t-1).num.natAbs.factorization p ∧ 2 ∣ t.den.factorization p}.Finite

lemma rhs_height (input : H1) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hyper : 1/(m:ℝ)+1/n+1/2<1) :
    ∃ M : ℕ, ∀ a b c : ℕ, 0<a → 0<b → 0<c → a.Coprime c → b.Coprime c →
      a^m+b^n=c^2 → c^2 ≤ M := by
  by_cases four : 4 ∣ m ∧ 4 ∣ n
  · exact ⟨0,fun a b c ha hb _ _ _ e => (fourths ha hb four.1 four.2 (dvd_refl 2) e).elim⟩
  obtain ⟨M,hM⟩ := bound (input m n hm hn hyper four)
  refine ⟨M,?_⟩
  intro a b c ha hb hc ac bc eq
  let t : ℚ := (a^m : ℕ)/(c^2 : ℚ)
  have cr : (0:ℚ)<c^2 := by positivity
  have eqr : (a:ℚ)^m+b^n=c^2 := by exact_mod_cast eq
  have coord := coordinates (pow_pos hc 2) ((ac.pow_left m).pow_right 2)
  have ct : t.num.natAbs=a^m ∧ t.den=c^2 := by simpa [t] using coord
  have other : 1-t=(b^n:ℕ)/(c^2:ℚ) := by
    dsimp [t]; push_cast; field_simp; linarith
  have cy : (1-t).num.natAbs=b^n := by
    rw [other]
    simpa using (coordinates (pow_pos hc 2) ((bc.pow_left n).pow_right 2)).1
  have pos : 0<t := by dsimp [t]; positivity
  have lt : t<1 := by
    dsimp [t]
    apply (div_lt_one cr).mpr
    push_cast
    linarith [show (0:ℚ)<b^n by positivity]
  have h := hM t ⟨pos,lt,fun p _ _ => by
    rw [ct.1,ct.2,cy]; exact ⟨power_valuation ..,power_valuation ..,power_valuation ..⟩⟩
  exact ct.2 ▸ h.2

lemma lhs_height (input : H2) {k n : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n)
    (hyper : 1/(k:ℝ)+1/n+1/2<1) :
    ∃ M : ℕ, ∀ a b c : ℕ, 0<a → 0<b → 0<c → c.Coprime a → b.Coprime a →
      a^2+b^n=c^k → c^k ≤ M := by
  obtain ⟨M,hM⟩ := bound (input k n hk hn hyper)
  refine ⟨M,?_⟩
  intro a b c ha hb hc ca ba eq
  let t : ℚ := (c^k:ℕ)/(a^2:ℚ)
  have ar : (0:ℚ)<a^2 := by positivity
  have eqr : (a:ℚ)^2+b^n=c^k := by exact_mod_cast eq
  have ct : t.num.natAbs=c^k ∧ t.den=a^2 := by
    simpa [t] using coordinates (pow_pos ha 2) ((ca.pow_left k).pow_right 2)
  have other : t-1=(b^n:ℕ)/(a^2:ℚ) := by
    dsimp [t]; push_cast; field_simp; linarith
  have cy : (t-1).num.natAbs=b^n := by
    rw [other]
    simpa using (coordinates (pow_pos ha 2) ((ba.pow_left n).pow_right 2)).1
  have lt : 1<t := by
    dsimp [t]
    apply (one_lt_div ar).mpr
    push_cast
    linarith [show (0:ℚ)<b^n by positivity]
  have h := hM t ⟨lt,fun p _ _ => by
    rw [ct.1,ct.2,cy]; exact ⟨power_valuation ..,power_valuation ..,power_valuation ..⟩⟩
  exact ct.1 ▸ h.1

theorem main : H1 → H2 → OMA.R_FermatCatalanConjecture_fermat_catalan_variants_darmon_granville_R1.H2 := by
  intro one two m n k hm hn hk sq hyper
  obtain ⟨M,height⟩ : ∃ M : ℕ, ∀ a b c : ℕ, 0<a → 0<b → 0<c →
      a.Coprime c → b.Coprime c → a.Coprime b → a^m+b^n=c^k → c^k ≤ M := by
    rcases sq with rfl|rfl|rfl
    · push_cast at hyper
      obtain ⟨M,h⟩ := lhs_height two hk hn (by linarith)
      exact ⟨M,fun a b c ha hb hc ac _ ab eq => h a b c ha hb hc ac.symm ab.symm eq⟩
    · push_cast at hyper
      obtain ⟨M,h⟩ := lhs_height two hk hm (by linarith)
      exact ⟨M,fun a b c ha hb hc _ bc ab eq => h b a c hb ha hc bc.symm ab ((Nat.add_comm ..).trans eq)⟩
    · push_cast at hyper
      obtain ⟨M,h⟩ := rhs_height one hm hn hyper
      exact ⟨M,fun a b c ha hb hc ac bc _ eq => h a b c ha hb hc ac bc eq⟩
  let box := Set.Iic (max M 2)
  apply ((Set.finite_Iic _).prod ((Set.finite_Iic _).prod (Set.finite_Iic _)) :
    (box ×ˢ box ×ˢ box).Finite).subset
  rintro ⟨a,b,c⟩ ⟨ha,hb,hc,e,pair⟩
  change a ≤ max M 2 ∧ b ≤ max M 2 ∧ c ≤ max M 2
  rcases primitive_or_small ha hb hc (by omega) (by omega) (by omega) e pair with ⟨ac,bc,ab⟩|small
  · have H := height a b c ha hb hc ac bc ab e
    have h₁ := Nat.le_pow (a:=a) (by omega : 0 < m)
    have h₂ := Nat.le_pow (a:=b) (by omega : 0 < n)
    have h₃ := Nat.le_pow (a:=c) (by omega : 0 < k)
    omega
  · omega

end OMA.R_FermatCatalanConjecture_fermat_catalan_variants_darmon_granville_R1_H2_R1
