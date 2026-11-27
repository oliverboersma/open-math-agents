import FormalConjectures.ErdosProblems.«387»
import Mathlib

/-! The covering progression, lower-bound sieve and mixed-divisor error of
Bui–Naprienko–Pratt–Zaharescu, arXiv:2605.21221, Theorem 5.1 and Section 6.
For Guy's question one may fix the covering weight at two. A divisor in the
top half-interval must use at least two reduced numerator factors. -/
namespace OMA.R_Erdos387_erdos_387_variants_guy_R1
open Finset Filter Real
open scoped Classical

/-- A covering progression of weight two, extended to avoid all primes up to 2k. -/
def H1 : Prop := ∃ᶠ k : ℕ in atTop, ∃ γ : ℕ, ∃ g : ℕ → ℕ,
    (∀ i<k, 2≤g i) ∧ (∏ i ∈ range k,g i) = k.factorial ∧
    ∀ n : ℕ, k<n → n ≡ γ [MOD (∏ p ∈ (2*k).primesLE, p^(Nat.log p k+1))] →
      (∀ i<k, g i ∣ n-i) ∧ ∀ p : ℕ, p.Prime → p≤2*k → ¬p∣n.choose k

/-- The positive lower-bound sieve on long dyadic intervals in a covering class. -/
def H2 : Prop := ∀ᶠ k : ℕ in atTop, ∀ γ : ℕ, ∀ g : ℕ → ℕ, ((∀ i<k, 2≤g i) ∧ (∏ i ∈ range k,g i) = k.factorial ∧
    ∀ n : ℕ, k<n → n ≡ γ [MOD (∏ p ∈ (2*k).primesLE, p^(Nat.log p k+1))] →
      (∀ i<k, g i ∣ n-i) ∧ ∀ p : ℕ, p.Prime → p≤2*k → ¬p∣n.choose k) →
  ∃ᶠ x : ℕ in atTop, ((Ioc x (2*x)).filter (fun n => n ≡ γ [MOD (∏ p ∈ (2*k).primesLE,p^(Nat.log p k+1))] ∧
      ∀ p : ℕ, p.Prime → p∣n.choose k → (x:ℝ)^((3:ℝ)^k)⁻¹ ≤ p)).Nonempty

/-- On a covered progression, the mixed-divisor exceptions occupy at most
nine tenths of the sifted sample once k and then x are sufficiently large. -/
def H3 : Prop := ∀ᶠ k : ℕ in atTop, ∀ γ : ℕ, ∀ g : ℕ → ℕ, ((∀ i<k, 2≤g i) ∧ (∏ i ∈ range k,g i) = k.factorial ∧
    ∀ n : ℕ, k<n → n ≡ γ [MOD (∏ p ∈ (2*k).primesLE, p^(Nat.log p k+1))] →
      (∀ i<k, g i ∣ n-i) ∧ ∀ p : ℕ, p.Prime → p≤2*k → ¬p∣n.choose k) →
  ∀ᶠ x : ℕ in atTop,
    let S := (Ioc x (2*x)).filter (fun n => n ≡ γ [MOD (∏ p ∈ (2*k).primesLE,p^(Nat.log p k+1))] ∧
      ∀ p : ℕ, p.Prime → p∣n.choose k → (x:ℝ)^((3:ℝ)^k)⁻¹ ≤ p)
    10*(S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i<k, f i∣(n-i)/g i) ∧
      (∃ i<k, ∃ j<k, i≠j ∧ 1<f i ∧ 1<f j) ∧
      n < 2*(∏ i ∈ range k,f i) ∧ (∏ i ∈ range k,f i)≤n)).card ≤ 9*S.card

lemma split_divisor {s : Finset ℕ} {a : ℕ → ℕ} {d : ℕ} (hd : d ∣ ∏ i ∈ s,a i) :
    ∃ f : ℕ → ℕ, (∀ i∈s, f i∣a i) ∧ (∏ i ∈ s,f i)=d := by
  induction s using Finset.induction_on generalizing d with
  | empty =>
    have e : d=1 := Nat.dvd_one.mp (by simpa using hd)
    exact ⟨fun _=>1,by simp,by simp [e]⟩
  | @insert t s ht ih =>
    rw [prod_insert ht] at hd
    obtain ⟨b,c,bt,cs,he⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    obtain ⟨f,hf,ef⟩ := ih cs
    let h (i : ℕ) := if i=t then b else f i
    refine ⟨h,?_,?_⟩
    · intro i hi
      rcases mem_insert.mp hi with rfl | hm
      · simpa [h] using bt
      · simpa [h,ne_of_mem_of_not_mem hm ht] using hf i hm
    · have rest : (∏ i ∈ s,h i)=c := by
        rw [←ef]
        exact prod_congr rfl (fun i hi => if_neg (ne_of_mem_of_not_mem hi ht))
      rw [prod_insert ht,rest]
      simpa [h] using he.symm

lemma two_factors {n k d : ℕ} (kn : k<n) (k1 : 1≤k) (hi : n<2*d) (upper : d≤n)
    (hd : d∣n.choose k) (g : ℕ → ℕ) (g2 : ∀ i<k,2≤g i)
    (fact : (∏ i ∈ range k,g i)=k.factorial) (gd : ∀ i<k,g i∣n-i) :
    ∃ f : ℕ → ℕ, (∀ i<k, f i∣(n-i)/g i) ∧
      (∃ i<k, ∃ j<k, i≠j ∧ 1<f i ∧ 1<f j) ∧
      n < 2*(∏ i ∈ range k,f i) ∧ (∏ i ∈ range k,f i)≤n := by
  let a (i : ℕ) := (n-i)/g i
  have ep : (∏ i ∈ range k,a i)=n.choose k := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k)
    rw [←Nat.descFactorial_eq_factorial_mul_choose,Nat.descFactorial_eq_prod_range,←fact,←prod_mul_distrib]
    exact prod_congr rfl (fun i hm => Nat.mul_div_cancel' (gd i (mem_range.mp hm)))
  obtain ⟨f,hf,ef⟩ := split_divisor (a:=a) (s:=range k) (ep ▸ hd)
  have pos (i : ℕ) (ik : i<k) : 0<a i := Nat.div_pos
    (Nat.le_of_dvd (by omega) (gd i ik)) (by have := g2 i ik; omega)
  have le (i : ℕ) (ik : i<k) : 2*f i≤n := by
    have f_le := Nat.le_of_dvd (pos i ik) (hf i (mem_range.mpr ik))
    calc
      _ ≤ g i*a i := Nat.mul_le_mul (g2 i ik) f_le
      _ = n-i := Nat.mul_div_cancel' (gd i ik)
      _ ≤ n := Nat.sub_le _ _
  have more : ∃ i<k, 1<f i := by
    by_contra! bad
    have bound : (∏ i ∈ range k,f i) ≤ ∏ _i ∈ range k,(1:ℕ) :=
      prod_le_prod' fun i hm => bad i (mem_range.mp hm)
    simp only [prod_const_one,ef] at bound
    omega
  obtain ⟨i,ik,fi⟩ := more
  have next : ∃ j<k, i≠j ∧ 1<f j := by
    by_contra! bad
    have e : (∏ j ∈ range k,f j)=f i := by
      apply prod_eq_single_of_mem i (mem_range.mpr ik)
      intro j hj ji
      have b := bad j (mem_range.mp hj) ji.symm
      have p := Nat.pos_of_dvd_of_pos (hf j hj) (pos j (mem_range.mp hj))
      omega
    have l := le i ik
    omega
  obtain ⟨j,jk,ne,fj⟩ := next
  exact ⟨f,(fun i h => hf i (mem_range.mpr h)),⟨i,ik,j,jk,ne,fi,fj⟩,ef ▸ hi,ef ▸ upper⟩

theorem main : H1 → H2 → H3 → type_of% @Erdos387.erdos_387.variants.guy := by
  intro cover sieve mix all
  obtain ⟨k,⟨γ,g,hg⟩,hv,hw,k1⟩ := (cover.and_eventually (sieve.and (mix.and (eventually_ge_atTop 1)))).exists
  have hits := hv γ g hg
  have scarce := hw γ g hg
  obtain ⟨M,hM⟩ := eventually_atTop.mp (all (1/2) (by norm_num))
  obtain ⟨x,non,bd,Mx,kx⟩ := (hits.and_eventually (scarce.and ((eventually_ge_atTop M).and
    (eventually_ge_atTop k)))).exists
  let S := (Ioc x (2*x)).filter (fun n => n ≡ γ [MOD (∏ p ∈ (2*k).primesLE,p^(Nat.log p k+1))] ∧
      ∀ p : ℕ, p.Prime → p∣n.choose k → (x:ℝ)^((3:ℝ)^k)⁻¹ ≤ p)
  let B := S.filter (fun n => ∃ f : ℕ → ℕ, (∀ i<k, f i∣(n-i)/g i) ∧
      (∃ i<k, ∃ j<k, i≠j ∧ 1<f i ∧ 1<f j) ∧
      n < 2*(∏ i ∈ range k,f i) ∧ (∏ i ∈ range k,f i)≤n)
  change 10*B.card ≤ 9*S.card at bd
  change S.Nonempty at non
  have sub : S ⊆ B := by
    intro n hn
    obtain ⟨xn,modn⟩ := mem_filter.mp hn
    have xlt := (mem_Ioc.mp xn).1
    have kn := kx.trans_lt xlt
    obtain ⟨d,interval,dvd⟩ := hM n (Mx.trans xlt.le) k k1 kn
    have upper : d≤n := by exact_mod_cast interval.2
    have lower : n<2*d := by
      have hl := interval.1
      change (1/2:ℝ)*n < d at hl
      exact_mod_cast (show (n:ℝ)<2*d by linarith)
    exact mem_filter.mpr ⟨hn,two_factors kn k1 lower upper dvd g hg.1 hg.2.1 ((hg.2.2 n kn modn.1).1)⟩
  have := card_le_card sub
  have := card_pos.mpr non
  omega

end OMA.R_Erdos387_erdos_387_variants_guy_R1
