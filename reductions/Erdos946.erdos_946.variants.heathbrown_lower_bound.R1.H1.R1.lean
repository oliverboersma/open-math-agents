import OMAReductions.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1

/-! Remove the additional prescribed valuations from the sieve. The second input
constructs a single CRT progression on which the divided forms are admissible.
The remaining analytic input is the fixed-coefficient seven-dimensional
lower-bound sieve in Hildebrand, Pacific J. Math. 129 (1987), Lemma 2. -/

namespace OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1
open Finset Filter Real
open scoped Classical

/-- Seven-dimensional lower-bound sieve for seven nonproportional affine
forms with no fixed prime divisor, in the squarefree 27-factor range. -/
def H1 : Prop := ∀ s c : Fin 7 → ℕ, (∀ i, 0 < s i) →
    (∀ i j, i ≠ j → s i*c j ≠ s j*c i) →
    (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p ∣ s i*t+c i) →
    ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∃ U : Finset ℕ, x / (log x)^7 ≤ C * U.card ∧ ∀ n ∈ U, 0 < n ∧ (n:ℝ) ≤ x ∧
        let v := fun i => s i*n+c i
        (∀ i, 1 < v i ∧ Squarefree (v i) ∧ ∀ p ∈ (v i).primeFactors, B < p) ∧
        (∑ i, (v i).primeFactors.card) ≤ 27

/-- The Chinese remainder progression and the admissibility of the divided forms. -/
def H2 : Prop := ∀ a q e : Fin 7 → ℕ, StrictMono a → (∀ i, 0 < a i) →
    Function.Injective q → (∀ i, (q i).Prime) → (∀ i j, a i < q j) →
    ∃ h M : ℕ, ∃ s c : Fin 7 → ℕ, 0<M ∧ (∀ i, 0<s i) ∧
      (∀ i t, q i^e i * (s i*t+c i) = a i*(h+M*t)+1) ∧
      (∀ i j, i≠j → s i*c j ≠ s j*c i) ∧
      ∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p∣s i*t+c i

theorem main : H1 → H2 → OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1.H1 := by
  classical
  intro sieve forms a q e mono ap qi qp aq B
  obtain ⟨h,M,s,c,mp,sp,formula,cross,localGood⟩ := forms a q e mono ap qi qp aq
  obtain ⟨C,Cp,many⟩ := sieve s c sp cross localGood B
  let K := h+M
  have kp : 0<K := by dsimp [K]; omega
  have K1 : (1:ℝ)≤K := by exact_mod_cast kp
  refine ⟨(K:ℝ)*C,by positivity,?_⟩
  have kt : Tendsto (fun x : ℝ => x/(K:ℝ)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  filter_upwards [kt.eventually many,kt.eventually (eventually_gt_atTop (1:ℝ))] with x many large
  obtain ⟨U,rate,rows⟩ := many
  let f (t : ℕ) := h+M*t
  have inj : Function.Injective f := by
    intro t u eq
    exact Nat.eq_of_mul_eq_mul_left mp (Nat.add_left_cancel eq)
  refine ⟨U.image f,?_,?_⟩
  · rw [card_image_of_injective _ inj]
    have xp : 0<x := by have := (lt_div_iff₀ (by positivity : (0:ℝ)<K)).mp large; linarith
    have logpos := Real.log_pos large
    have logle : log (x/K)≤log x := Real.log_le_log (by positivity) (div_le_self xp.le K1)
    calc
      _ ≤ x/(log (x/K))^7 := div_le_div_of_nonneg_left xp.le (by positivity)
        (pow_le_pow_left₀ logpos.le logle _)
      _ = (K:ℝ)*(x/K/(log (x/K))^7) := by field_simp
      _ ≤ (K:ℝ)*(C*U.card) := by gcongr
      _ = _ := by ring
  · intro n hn
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hn
    obtain ⟨tp,tx,parts,total⟩ := rows t ht
    have bp (i) : 0<q i^e i := pow_pos (qp i).pos _
    have val (i) : (a i*f t+1)/(q i^e i)=s i*t+c i := by
      change (a i*(h+M*t)+1)/(q i^e i)=_
      rw [←formula i t,Nat.mul_div_cancel_left _ (bp i)]
    have dp (i) : q i^e i ∣ a i*f t+1 := ⟨_,(formula i t).symm⟩
    have limit : f t≤K*t := by
      dsimp [f,K]
      nlinarith only [Nat.mul_le_mul_left h (show 1≤t from tp)]
    have ft : 0 < f t := by dsimp [f]; positivity
    refine ⟨ft,?_,?_,?_⟩
    · calc
        _ ≤ (K:ℝ)*t := by exact_mod_cast limit
        _ ≤ x := by rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp tx
    · intro i
      exact ⟨dp i,by simpa only [val] using parts i⟩
    · simpa only [val] using total

end OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1
