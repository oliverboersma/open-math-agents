import OMAReductions.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1
import Mathlib

/-! The de la Vallée Poussin argument for Eisenstein angular characters.
The two angular frequencies k and 2k leave sufficient positivity to
exclude a zero on the boundary. Only the prime coefficients are needed
for this argument because higher prime powers converge there absolutely. -/
namespace OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1
open OeisA218585 Filter Real ArithmeticFunction
open scoped Topology Classical

/-- Continuation and the logarithmic derivative in the open half-plane. -/
def H1 : Prop := let z (p : ℕ) : ℂ := ⟨(xp p:ℝ)+(yp p:ℝ)/2,√3*(yp p:ℝ)/2⟩
  ∀ k : ℕ, k ≠ 0 → ∃ (L : ℂ → ℂ) (a : ℕ → ℂ),
    (∀ s : ℂ, 1 ≤ s.re → AnalyticAt ℂ L s) ∧ (∀ s : ℂ, 1 < s.re → L s ≠ 0) ∧
    (∀ n, ‖a n‖ ≤ Λ n) ∧ (∀ p : ℕ, p.Prime → a p =
      ((Λ p*(if p%3 = 1 then cos ((k:ℝ)*(6*(z p).arg)) else 0):ℝ):ℂ)) ∧
    ∀ s : ℂ, 1 < s.re → LSeries a s = -deriv L s/(2*L s)

/-- The three-four-one trigonometric estimate for split prime coefficients.
The limiting lower bound is -3/2, so -7/4 leaves a fixed margin. -/
def H2 : Prop := ∀ (θ : ℕ → ℝ) (a b : ℕ → ℂ), (∀ n, ‖a n‖ ≤ Λ n) → (∀ n, ‖b n‖ ≤ Λ n) →
  (∀ p : ℕ, p.Prime → a p = ((Λ p*(if p%3 = 1 then cos (θ p) else 0):ℝ):ℂ)) →
  (∀ p : ℕ, p.Prime → b p = ((Λ p*(if p%3 = 1 then cos (2*θ p) else 0):ℝ):ℂ)) →
  ∀ t : ℝ, ∀ᶠ h : ℝ in 𝓝[>] 0, -(7/4:ℝ) ≤ h *
    (4*(LSeries a ((⟨1,t⟩:ℂ)+h)).re + (LSeries b ((⟨1,2*t⟩:ℂ)+h)).re)

lemma horizontal_order {L : ℂ → ℂ} {a : ℕ → ℂ} {s : ℂ} (sr : s.re = 1)
    (an : AnalyticAt ℂ L s) (nz : ∀ z : ℂ, 1 < z.re → L z ≠ 0)
    (eq : ∀ z : ℂ, 1 < z.re → LSeries a z = -deriv L z/(2*L z)) :
    ∃ m : ℕ, (L s = 0 → 0 < m) ∧
      Tendsto (fun h : ℝ => h*(LSeries a (s+h)).re) (𝓝[>] 0) (𝓝 (-(m:ℝ)/2)) := by
  let z (h : ℝ) := s+(h:ℂ)
  have zl : Tendsto z (𝓝[>] 0) (𝓝 s) := by
    have hc : ContinuousAt (fun h : ℝ => s+(h:ℂ)) 0 := by fun_prop
    simpa [z] using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have half (h : ℝ) (hp : 0 < h) : 1 < (z h).re := by simp [z,sr,hp]
  have good : analyticOrderAt L s ≠ ⊤ := by
    intro top
    obtain ⟨h,zero,hp⟩ := ((zl.eventually (analyticOrderAt_eq_top.mp top)).and
      (self_mem_nhdsWithin : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h)).exists
    exact nz (z h) (half h hp) zero
  let m := analyticOrderNatAt L s
  obtain ⟨g,ga,gn,eg⟩ := (an.analyticOrderNatAt_eq_iff good).mp (rfl : analyticOrderNatAt L s = m)
  have prodEq : L =ᶠ[𝓝 s] (fun w => (w-s)^m*g w) := by
    filter_upwards [eg] with w hw
    simpa [m,smul_eq_mul] using hw
  refine ⟨m,?_,?_⟩
  · intro ls
    by_contra! bad
    have em : m = 0 := by omega
    have h := prodEq.self_of_nhds
    simp [ls,em] at h
    exact gn h.symm
  have hg : ContinuousAt (logDeriv g) s := ga.deriv.continuousAt.div ga.continuousAt gn
  have ht0 : Tendsto (fun h : ℝ => (h:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have li : Tendsto (fun h : ℝ => (m:ℂ)+(h:ℂ)*logDeriv g (z h)) (𝓝[>] 0) (𝓝 (m:ℂ)) := by
    simpa using (tendsto_const_nhds (x:=(m:ℂ))).add (ht0.mul (hg.tendsto.comp zl))
  have inC : Tendsto (fun h : ℝ => (h:ℂ)*LSeries a (z h)) (𝓝[>] 0) (𝓝 (-(m:ℂ)/2)) := by
    apply (li.neg.div_const 2).congr'
    filter_upwards [self_mem_nhdsWithin,zl.eventually prodEq,zl.eventually prodEq.deriv,
      zl.eventually ga.eventually_analyticAt,zl.eventually (ga.continuousAt.eventually_ne gn)] with h hp val der dg gne
    change 0 < h at hp
    have hc : (h:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have diff : z h-s ≠ 0 := by simpa [z] using hc
    have ld : logDeriv L (z h)= (m:ℂ)/(h:ℂ)+logDeriv g (z h) := by
      calc
        _ = logDeriv (fun w => (w-s)^m*g w) (z h) := by simp only [logDeriv_apply,der,val]
        _ = logDeriv (fun w : ℂ => (w-s)^m) (z h)+logDeriv g (z h) :=
          logDeriv_mul _ (pow_ne_zero _ diff) gne (by fun_prop) dg.differentiableAt
        _ = _ := by rw [logDeriv_fun_pow (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w-s) (z h)) m]
                    simp [logDeriv_apply,z,div_eq_mul_inv]
    change -((m:ℂ)+(h:ℂ)*logDeriv g (z h))/2 = (h:ℂ)*LSeries a (z h)
    rw [eq _ (half h hp)]
    have conv : -deriv L (z h)/(2*L (z h))= -logDeriv L (z h)/2 := by rw [logDeriv_apply]; ring
    rw [conv,ld]
    field_simp
    <;> ring
  simpa [Function.comp_def,z,Complex.mul_re,Complex.div_ofNat_re] using (Complex.continuous_re.continuousAt.tendsto.comp inC)

theorem main : H1 → H2 → OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1.H1 := by
  intro data positivity k hk
  obtain ⟨L,a,an,nz,ab,ap,ae⟩ := data k hk
  obtain ⟨F,b,fan,fnz,bb,bp,be⟩ := data (2*k) (by omega)
  refine ⟨L,a,fun s hs => ⟨an s hs,?_⟩,ab,ap,ae⟩
  rcases hs.lt_or_eq with inside | boundary
  · exact nz s inside
  · intro bad
    let t := s.im
    let u : ℂ := ⟨1,2*t⟩
    have es : s = (⟨1,t⟩:ℂ) := Complex.ext boundary.symm rfl
    obtain ⟨m,mpos,lm⟩ := horizontal_order boundary.symm (an s boundary.le) nz ae
    obtain ⟨j,_,lj⟩ := horizontal_order (s:=u) rfl (fan u le_rfl) fnz be
    let θ := fun p : ℕ => (k:ℝ)*(6*(⟨(xp p:ℝ)+(yp p:ℝ)/2,√3*(yp p:ℝ)/2⟩:ℂ).arg)
    have bprime (p : ℕ) (pp : p.Prime) :
        b p = ((Λ p*(if p%3 = 1 then cos (2*θ p) else 0):ℝ):ℂ) := by
      convert bp p pp using 1
      dsimp [θ]
      push_cast
      ring_nf
    have eventual := positivity θ a b ab bb ap bprime t
    have lim := (lm.const_mul 4).add lj
    have cmp : -(7/4:ℝ) ≤ 4*(-(m:ℝ)/2)+(-(j:ℝ)/2) := by
      apply ge_of_tendsto lim
      filter_upwards [eventual] with h H
      rw [es]
      dsimp [u] at *
      linarith only [H]
    have hm : (1:ℝ) ≤ m := by exact_mod_cast mpos bad
    have hj := Nat.cast_nonneg j (α:=ℝ)
    linarith

end OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1
