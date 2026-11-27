import OMAReductions.R_Green92_green_92_variants_chase_lower_R1_H1_R1
import Mathlib

/-! Concentration of two deletion-trace statistics. The Boolean-cube McDiarmid estimate is adapted from @TheWaler, commit 193d9dd. -/
open Finset Filter BigOperators
open scoped Classical
section McDiarmid

private lemma cosh_le_exp_half_sq (x : ℝ) :
    (Real.exp x + Real.exp (-x)) / 2 ≤ Real.exp (x ^ 2 / 2) := by
  suffices hpos : ∀ t : ℝ, 0 ≤ t → (Real.exp t + Real.exp (-t)) / 2 ≤ Real.exp (t ^ 2 / 2) by
    rcases le_total 0 x with hx | hx
    · exact hpos x hx
    · have h := hpos (-x) (by linarith); simp only [neg_neg, neg_sq] at h; linarith
  intro t ht
  have hderiv_neg_exp : ∀ s : ℝ, HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-s)) s := by
    intro s
    have h := (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)
    simpa [Function.comp_def] using h
  let h1 : ℝ → ℝ := fun s => s * (Real.exp s + Real.exp (-s)) - (Real.exp s - Real.exp (-s))
  have hh1_deriv : ∀ s : ℝ, HasDerivAt h1 (s * (Real.exp s - Real.exp (-s))) s := by
    intro s
    have d1 := Real.hasDerivAt_exp s
    have d2 := hderiv_neg_exp s
    have d3 := (hasDerivAt_id s).mul (d1.add d2)
    have d4 := d3.sub (d1.sub d2)
    have hEq : s * (Real.exp s - Real.exp (-s)) =
        (1 * (Real.exp s + Real.exp (-s)) + s * (Real.exp s + -Real.exp (-s))) -
        (Real.exp s - -Real.exp (-s)) := by ring
    rw [hEq]; exact d4
  have hh1_mono : MonotoneOn h1 (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hh1_deriv s).continuousAt.continuousWithinAt)
      (fun s _ => (hh1_deriv s).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    rw [interior_Ici] at hs
    rw [(hh1_deriv s).deriv]
    have hexp : Real.exp (-s) ≤ Real.exp s := Real.exp_le_exp.mpr (by linarith [Set.mem_Ioi.mp hs])
    exact mul_nonneg (Set.mem_Ioi.mp hs).le (by linarith)
  have hh1_nonneg : ∀ s : ℝ, 0 ≤ s → 0 ≤ h1 s := by
    intro s hs
    have h0 : h1 0 = 0 := by simp [h1]
    rw [← h0]
    exact hh1_mono (Set.mem_Ici.mpr le_rfl) hs hs
  let h2 : ℝ → ℝ := fun s => Real.exp (-(s ^ 2 / 2)) * (Real.exp s + Real.exp (-s))
  have hh2_deriv : ∀ s : ℝ, HasDerivAt h2 (-Real.exp (-(s ^ 2 / 2)) * h1 s) s := by
    intro s
    have dsq : HasDerivAt (fun u : ℝ => -(u ^ 2 / 2)) (-s) s := by
      have h := ((hasDerivAt_pow 2 s).div_const (2 : ℝ)).neg
      have hEq : -s = -(((2 : ℕ) : ℝ) * s ^ (2 - 1) / 2) := by norm_num
      rw [hEq]; exact h
    have de : HasDerivAt (fun u : ℝ => Real.exp (-(u ^ 2 / 2)))
        (Real.exp (-(s ^ 2 / 2)) * (-s)) s := by
      simpa [Function.comp_def] using (Real.hasDerivAt_exp (-(s ^ 2 / 2))).comp s dsq
    have dm := de.mul ((Real.hasDerivAt_exp s).add (hderiv_neg_exp s))
    have hEq : -Real.exp (-(s ^ 2 / 2)) * h1 s =
        Real.exp (-(s ^ 2 / 2)) * (-s) * (Real.exp s + Real.exp (-s)) +
        Real.exp (-(s ^ 2 / 2)) * (Real.exp s + -Real.exp (-s)) := by
      simp only [h1]; ring
    rw [hEq]; exact dm
  have hh2_anti : AntitoneOn h2 (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun s _ => (hh2_deriv s).continuousAt.continuousWithinAt)
      (fun s _ => (hh2_deriv s).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    rw [interior_Ici] at hs
    rw [(hh2_deriv s).deriv]
    have h1s := hh1_nonneg s (Set.mem_Ioi.mp hs).le
    have hex : 0 ≤ Real.exp (-(s ^ 2 / 2)) := (Real.exp_pos _).le
    nlinarith
  have ht_le : h2 t ≤ h2 0 := hh2_anti (Set.mem_Ici.mpr le_rfl) ht ht
  have h20 : h2 0 = 2 := by simp [h2]; norm_num
  rw [h20] at ht_le
  have hmul : Real.exp (t ^ 2 / 2) * h2 t ≤ Real.exp (t ^ 2 / 2) * 2 :=
    mul_le_mul_of_nonneg_left ht_le (Real.exp_pos _).le
  have hcancel : Real.exp (t ^ 2 / 2) * h2 t = Real.exp t + Real.exp (-t) := by
    simp only [h2, ← mul_assoc, ← Real.exp_add]; simp
  linarith

private lemma mgf_mcdiarmid_fin :
    ∀ (k : ℕ) (f : (Fin k → Bool) → ℝ) (c : Fin k → ℝ),
      (∀ ω i, |f ω - f (Function.update ω i (!ω i))| ≤ c i) →
      ∀ s : ℝ,
        (∑ ω : Fin k → Bool, Real.exp (s * (f ω - (∑ ω' : Fin k → Bool, f ω') / (2 : ℝ) ^ k))) /
            (2 : ℝ) ^ k ≤
          Real.exp (s ^ 2 / 8 * ∑ i : Fin k, (c i) ^ 2)
  | 0, f, c, _, s => by
    simp
  | k + 1, f, c, hdiff, s => by
    let e : (Fin (k + 1) → Bool) ≃ Bool × (Fin k → Bool) :=
      { toFun := fun ω => (ω 0, Fin.tail ω)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun ω => Fin.cons_self_tail ω
        right_inv := fun ⟨b, ω'⟩ => Prod.ext (by simp) (by simp) }
    have hsplit : ∀ F : (Fin (k + 1) → Bool) → ℝ,
        ∑ ω : Fin (k + 1) → Bool, F ω =
          ∑ ω' : Fin k → Bool, (F (Fin.cons true ω') + F (Fin.cons false ω')) := by
      intro F
      rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [e, Equiv.coe_fn_symm_mk]
      rw [← Finset.sum_add_distrib]
    let g : (Fin k → Bool) → ℝ := fun ω' => (f (Fin.cons true ω') + f (Fin.cons false ω')) / 2
    let δ : (Fin k → Bool) → ℝ := fun ω' => (f (Fin.cons true ω') - f (Fin.cons false ω')) / 2
    let μ : ℝ := (∑ ω : Fin (k + 1) → Bool, f ω) / (2 : ℝ) ^ (k + 1)
    have hμg : (∑ ω' : Fin k → Bool, g ω') / (2 : ℝ) ^ k = μ := by
      simp only [μ, g, hsplit f, ← Finset.sum_div, pow_succ]; ring
    have hδ_le : ∀ ω' : Fin k → Bool, |δ ω'| ≤ c 0 / 2 := by
      intro ω'
      have hupd : Function.update (Fin.cons (α := fun _ => Bool) true ω') 0
            (!(Fin.cons (α := fun _ => Bool) true ω' 0)) =
          Fin.cons (α := fun _ => Bool) false ω' := by
        ext i; refine Fin.cases (by simp) (fun j => by simp [Fin.succ_ne_zero]) i
      have h0 := hdiff (Fin.cons (α := fun _ => Bool) true ω') 0
      rw [hupd] at h0
      simp only [δ, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hg_diff : ∀ ω' j, |g ω' - g (Function.update ω' j (!ω' j))| ≤ c j.succ := by
      intro ω' j
      have hup : ∀ b : Bool,
          Fin.cons (α := fun _ => Bool) b (Function.update ω' j (!ω' j)) =
            Function.update (Fin.cons (α := fun _ => Bool) b ω') j.succ
              (!(Fin.cons (α := fun _ => Bool) b ω' j.succ)) := by
        intro b; ext i
        refine Fin.cases (by simp [Ne.symm (Fin.succ_ne_zero _)]) (fun m => ?_) i
        simp only [Fin.cons_succ]
        by_cases hm : m = j
        · subst hm; simp
        · have hms : m.succ ≠ j.succ := fun h => hm (Fin.succ_injective _ h)
          simp [hm, hms]
      have ht := hdiff (Fin.cons true ω') j.succ
      have hf := hdiff (Fin.cons false ω') j.succ
      rw [← hup true] at ht; rw [← hup false] at hf
      have hsub : g ω' - g (Function.update ω' j (!ω' j)) =
          ((f (Fin.cons true ω') - f (Fin.cons true (Function.update ω' j (!ω' j)))) +
           (f (Fin.cons false ω') - f (Fin.cons false (Function.update ω' j (!ω' j))))) / 2 := by
        simp only [g]; ring
      rw [hsub, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have htri := abs_add_le
        (f (Fin.cons true ω') - f (Fin.cons true (Function.update ω' j (!ω' j))))
        (f (Fin.cons false ω') - f (Fin.cons false (Function.update ω' j (!ω' j))))
      linarith
    have hstep : ∀ ω' : Fin k → Bool,
        (Real.exp (s * (f (Fin.cons true ω') - μ)) +
         Real.exp (s * (f (Fin.cons false ω') - μ))) / 2 ≤
          Real.exp (s ^ 2 / 8 * (c 0) ^ 2) * Real.exp (s * (g ω' - μ)) := by
      intro ω'
      have ht : s * (f (Fin.cons true ω') - μ) = s * (g ω' - μ) + s * δ ω' := by
        simp only [g, δ]; ring
      have hf : s * (f (Fin.cons false ω') - μ) = s * (g ω' - μ) + -(s * δ ω') := by
        simp only [g, δ]; ring
      rw [ht, hf, Real.exp_add, Real.exp_add, ← mul_add, mul_div_assoc]
      have hc0 := cosh_le_exp_half_sq (s * δ ω')
      have hsq_le : (s * δ ω') ^ 2 / 2 ≤ s ^ 2 / 8 * (c 0) ^ 2 := by
        have h1 : (δ ω') ^ 2 ≤ (c 0 / 2) ^ 2 := by
          rw [← sq_abs (δ ω')]
          exact sq_le_sq' (by linarith [abs_nonneg (δ ω'), hδ_le ω']) (hδ_le ω')
        nlinarith [sq_nonneg s]
      have hexp_le : Real.exp ((s * δ ω') ^ 2 / 2) ≤ Real.exp (s ^ 2 / 8 * (c 0) ^ 2) :=
        Real.exp_le_exp.mpr hsq_le
      calc Real.exp (s * (g ω' - μ)) * ((Real.exp (s * δ ω') + Real.exp (-(s * δ ω'))) / 2)
          ≤ Real.exp (s * (g ω' - μ)) * Real.exp (s ^ 2 / 8 * (c 0) ^ 2) :=
            mul_le_mul_of_nonneg_left (le_trans hc0 hexp_le) (Real.exp_pos _).le
        _ = Real.exp (s ^ 2 / 8 * (c 0) ^ 2) * Real.exp (s * (g ω' - μ)) := mul_comm _ _
    have hIH := mgf_mcdiarmid_fin k g (fun j => c j.succ) hg_diff s
    rw [hμg] at hIH
    have hsum_step :
        (∑ ω : Fin (k + 1) → Bool, Real.exp (s * (f ω - μ))) / (2 : ℝ) ^ (k + 1) =
          (∑ ω' : Fin k → Bool,
            (Real.exp (s * (f (Fin.cons true ω') - μ)) +
             Real.exp (s * (f (Fin.cons false ω') - μ))) / 2) / (2 : ℝ) ^ k := by
      rw [hsplit, ← Finset.sum_div, pow_succ]; ring
    rw [hsum_step]
    calc (∑ ω' : Fin k → Bool,
            (Real.exp (s * (f (Fin.cons true ω') - μ)) +
             Real.exp (s * (f (Fin.cons false ω') - μ))) / 2) / (2 : ℝ) ^ k
        ≤ (∑ ω' : Fin k → Bool,
            Real.exp (s ^ 2 / 8 * (c 0) ^ 2) * Real.exp (s * (g ω' - μ))) / (2 : ℝ) ^ k := by
            gcongr with ω' _; exact hstep ω'
      _ = Real.exp (s ^ 2 / 8 * (c 0) ^ 2) *
            ((∑ ω' : Fin k → Bool, Real.exp (s * (g ω' - μ))) / (2 : ℝ) ^ k) := by
            rw [← Finset.mul_sum, mul_div_assoc]
      _ ≤ Real.exp (s ^ 2 / 8 * (c 0) ^ 2) *
            Real.exp (s ^ 2 / 8 * ∑ j : Fin k, (c j.succ) ^ 2) :=
            mul_le_mul_of_nonneg_left hIH (Real.exp_pos _).le
      _ = Real.exp (s ^ 2 / 8 * ∑ i : Fin (k + 1), (c i) ^ 2) := by
            rw [← Real.exp_add, Fin.sum_univ_succ]; congr 1; ring

private lemma mcdiarmid_lower_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (c : ι → ℝ)
    (hdiff : ∀ ω i, |f ω - f (Function.update ω i (!ω i))| ≤ c i)
    {lam : ℝ} (hlam : 0 ≤ lam) (hS2 : 0 < ∑ i : ι, (c i) ^ 2) :
    ((Finset.univ.filter (fun ω : ι → Bool =>
        f ω ≤ (∑ ω' : ι → Bool, f ω') / (2 : ℝ) ^ Fintype.card ι - lam)).card : ℝ) /
        (2 : ℝ) ^ Fintype.card ι ≤
      Real.exp (-2 * lam ^ 2 / ∑ i : ι, (c i) ^ 2) := by
  let μ : ℝ := (∑ ω' : ι → Bool, f ω') / (2 : ℝ) ^ Fintype.card ι
  let e := Fintype.equivFin ι
  let k := Fintype.card ι
  let f' : (Fin k → Bool) → ℝ := fun ω => f (ω ∘ e)
  let c' : Fin k → ℝ := fun j => c (e.symm j)
  have hdiff' : ∀ ω j, |f' ω - f' (Function.update ω j (!ω j))| ≤ c' j := by
    intro ω j
    have hupd : Function.update ω j (!ω j) ∘ e =
        Function.update (ω ∘ e) (e.symm j) (!((ω ∘ e) (e.symm j))) := by
      ext x; simp only [Function.comp_apply]
      by_cases hx : x = e.symm j
      · subst hx; simp
      · have hex : e x ≠ j := fun h => hx (by rw [← h, Equiv.symm_apply_apply])
        simp [hx, hex]
    simpa only [f', c', hupd] using hdiff (ω ∘ e) (e.symm j)
  let eFun : (Fin k → Bool) ≃ (ι → Bool) := Equiv.arrowCongr e.symm (Equiv.refl Bool)
  have heFun_apply : ∀ (ω : Fin k → Bool), eFun ω = ω ∘ e := fun ω => by ext x; simp [eFun]
  have hμ' : (∑ ω : Fin k → Bool, f' ω) / (2 : ℝ) ^ k = μ := by
    simp only [μ, f', k]; congr 1
    rw [← Equiv.sum_comp eFun]
    exact Finset.sum_congr rfl (fun ω _ => by rw [heFun_apply])
  have hS2' : ∑ j : Fin k, (c' j) ^ 2 = ∑ i : ι, (c i) ^ 2 :=
    Equiv.sum_comp e.symm (fun i => (c i) ^ 2)
  let S2 : ℝ := ∑ i : ι, (c i) ^ 2
  let s : ℝ := -4 * lam / S2
  have hs_le : s ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hS2.le
  have hmgf : (∑ ω : ι → Bool, Real.exp (s * (f ω - μ))) / (2 : ℝ) ^ k ≤
      Real.exp (s ^ 2 / 8 * S2) := by
    have h := mgf_mcdiarmid_fin k f' c' hdiff' s
    rw [hμ', hS2'] at h
    have hsum_eq : ∑ ω : Fin k → Bool, Real.exp (s * (f' ω - μ)) =
        ∑ ω : ι → Bool, Real.exp (s * (f ω - μ)) := by
      rw [← Equiv.sum_comp eFun]
      exact Finset.sum_congr rfl (fun ω _ => by simp only [f', heFun_apply])
    rwa [hsum_eq] at h
  let B := Finset.univ.filter (fun ω : ι → Bool => f ω ≤ μ - lam)
  have hmarkov : (B.card : ℝ) * Real.exp (4 * lam ^ 2 / S2) ≤
      ∑ ω : ι → Bool, Real.exp (s * (f ω - μ)) := by
    calc (B.card : ℝ) * Real.exp (4 * lam ^ 2 / S2)
        = ∑ _ω ∈ B, Real.exp (4 * lam ^ 2 / S2) := by simp
      _ ≤ ∑ ω ∈ B, Real.exp (s * (f ω - μ)) := by
          refine Finset.sum_le_sum (fun ω hω => Real.exp_le_exp.mpr ?_)
          have hf : f ω - μ ≤ -lam := by linarith [(Finset.mem_filter.mp hω).2]
          have h1 : s * (-lam) ≤ s * (f ω - μ) := mul_le_mul_of_nonpos_left hf hs_le
          have h2 : s * (-lam) = 4 * lam ^ 2 / S2 := by simp only [s]; ring
          linarith
      _ ≤ ∑ ω : ι → Bool, Real.exp (s * (f ω - μ)) :=
          Finset.sum_le_univ_sum_of_nonneg (fun ω => (Real.exp_pos _).le)
  have hdiv : ((B.card : ℝ) / (2 : ℝ) ^ k) * Real.exp (4 * lam ^ 2 / S2) ≤
      Real.exp (s ^ 2 / 8 * S2) := by
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ h2pos]
    have hmgf' := (div_le_iff₀ h2pos).mp hmgf
    linarith
  have hexp_pos : 0 < Real.exp (4 * lam ^ 2 / S2) := Real.exp_pos _
  calc (B.card : ℝ) / (2 : ℝ) ^ k
      ≤ Real.exp (s ^ 2 / 8 * S2) / Real.exp (4 * lam ^ 2 / S2) := (le_div_iff₀ hexp_pos).mpr hdiv
    _ = Real.exp (s ^ 2 / 8 * S2 - 4 * lam ^ 2 / S2) := (Real.exp_sub _ _).symm
    _ = Real.exp (-2 * lam ^ 2 / S2) := by
        congr 1; simp only [s]; field_simp [hS2.ne']; ring

end McDiarmid
open Finset Filter Real
open scoped Topology

namespace Green92Typical

private def rises : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a::b::xs => (if a=false ∧ b=true then 1 else 0)+rises (b::xs)

private lemma rise_zip (xs : List Bool) : (xs.zip xs.tail).count (false,true)=rises xs := by
  match xs with
  | [] | [_] => simp [rises]
  | a::b::xs =>
    have ih := rise_zip (b::xs)
    cases a <;> cases b <;> simp_all [List.zip_cons_cons,List.count_cons,rises,Nat.add_comm]

private def head1 : List Bool → ℝ
  | true :: _ => 1
  | _ => 0

private lemma head_bounds (w : List Bool) : 0 ≤ head1 w ∧ head1 w ≤ 1 := by
  cases w with
  | nil => norm_num [head1]
  | cons b w => cases b <;> norm_num [head1]
private noncomputable def pot (w:List Bool) : ℝ := (rises w:ℝ) + head1 w/3

private noncomputable def avg : List Bool → (List Bool → ℝ) → ℝ
  | [],F => F []
  | b::bs,F => avg bs (fun z => (F z+F (b::z))/2)

private lemma avg_translate (w:List Bool) (F:List Bool→ℝ) (c:ℝ) :
    avg w (fun z => F z+c)=avg w F+c := by
  induction w generalizing F with
  | nil => rfl
  | cons b w ih =>
    rw [avg,avg,←ih]
    congr 1
    funext z; ring

private lemma avg_mono (w:List Bool) (F G:List Bool→ℝ) (h:∀z,F z≤G z) :
    avg w F ≤ avg w G := by
  induction w generalizing F G with
  | nil => exact h _
  | cons b w ih =>
    apply ih
    intro z
    exact div_le_div_of_nonneg_right (add_le_add (h z) (h (b::z))) (by norm_num)

private lemma pair_pot (w:List Bool) :
    avg (false::true::w) pot=avg w pot+1/3 := by
  rw [avg,avg,←avg_translate]
  congr 1
  funext z
  cases z with
  | nil => norm_num [pot,head1,rises,avg]
  | cons a z =>
    cases a <;> simp [pot,head1,rises] <;> ring

private lemma extra_pot (w:List Bool) :
    avg w pot≤avg (true::w) pot ∧ avg (true::w) pot≤avg w pot+1/6 := by
  rw [avg,←avg_translate]
  constructor <;> apply avg_mono <;> intro z <;>
    cases z with
    | nil => norm_num [pot,head1,rises]
    | cons a z => cases a <;> simp [pot,head1,rises] <;> linarith

private def pairs : ℕ→List Bool→List Bool
  | 0,z => z
  | n+1,z => false::true::pairs n z

private lemma avg_pairs (n:ℕ) (z:List Bool) : avg (pairs n z) pot=avg z pot+(n:ℝ)/3 := by
  induction n with
  | zero => simp [pairs]
  | succ n ih => rw [pairs,pair_pot,ih]; push_cast; ring

private lemma rise_mean (a b:ℕ) :
    |avg (pairs a (true::pairs b [])) (fun w => (rises w:ℝ)) - (a+b:ℕ)/3|≤1 := by
  let w := pairs a (true::pairs b [])
  have hp := avg_pairs a (true::pairs b [])
  have he := extra_pot (pairs b [])
  rw [avg_pairs] at he
  have ep : avg [] pot=0 := by norm_num [avg,pot,rises,head1]
  rw [ep] at he
  have low : avg w (fun z => (rises z:ℝ))≤avg w pot := by
    apply avg_mono
    intro z
    dsimp [pot]
    linarith [(head_bounds z).1,(head_bounds z).2]
  have up : avg w pot≤avg w (fun z => (rises z:ℝ))+1/3 := by
    rw [←avg_translate]
    apply avg_mono
    intro z
    dsimp [pot]
    linarith [(head_bounds z).1,(head_bounds z).2]
  change avg w pot=_ at hp
  change |avg w (fun z => (rises z:ℝ)) - _|≤1
  push_cast
  rw [abs_le]
  constructor <;> linarith [he.1,he.2]

private lemma length_mean (w:List Bool) :
    avg w (fun z => (z.length:ℝ))=(w.length:ℝ)/2 := by
  induction w with
  | nil => simp [avg]
  | cons b w ih =>
    rw [avg]
    have id : (fun z:List Bool => ((z.length:ℝ)+((b::z).length:ℝ))/2) =
      fun z => (z.length:ℝ)+1/2 := by funext z; simp; ring
    rw [id,avg_translate,ih]; simp; ring

private lemma rise_insert (a b:List Bool) (x:Bool) :
    rises (a++x::b)=rises (a++b) ∨ rises (a++x::b)=rises (a++b)+1 := by
  induction a with
  | nil =>
    cases b with
    | nil => simp [rises]
    | cons y b => cases x <;> cases y <;> simp [rises,Nat.add_comm]
  | cons h a ih =>
    cases a with
    | nil =>
      cases b with
      | nil => cases h <;> cases x <;> simp [rises]
      | cons y b => cases h <;> cases x <;> cases y <;> simp [rises,Nat.add_comm]
    | cons y a =>
      simp only [List.cons_append,rises] at ih ⊢
      omega

private def maskTrace {n:ℕ} (W ω : Fin n → Bool) : List Bool :=
  ((List.finRange n).filter ω).map W

private lemma trace_cons {n:ℕ} (W:Fin (n+1)→Bool) (b:Bool) (ω:Fin n→Bool) :
    maskTrace W (Fin.cons b ω) =
      if b then W 0 :: maskTrace (Fin.tail W) ω else maskTrace (Fin.tail W) ω := by
  cases b <;> simp [maskTrace,List.finRange_succ,List.filter_map,List.map_map,Fin.tail,Function.comp_def]

private lemma avg_mask {n:ℕ} (W:Fin n→Bool) (F:List Bool→ℝ) :
    (∑ ω : Fin n → Bool,F (maskTrace W ω))/(2:ℝ)^n = avg (List.ofFn W) F := by
  induction n generalizing F with
  | zero => simp [avg,maskTrace]
  | succ n ih =>
    let e : (Fin (n+1)→Bool) ≃ Bool × (Fin n→Bool) := {
      toFun := fun ω => (ω 0,Fin.tail ω)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := Fin.cons_self_tail
      right_inv := fun ⟨b,ω⟩ => Prod.ext (by simp) (by simp) }
    rw [←Equiv.sum_comp e.symm,Fintype.sum_prod_type,Fintype.sum_bool]
    simp only [e,Equiv.coe_fn_symm_mk,trace_cons,if_true,if_false,Bool.false_eq_true]
    rw [←sum_add_distrib,List.ofFn_succ,avg,←ih _ (fun z => (F z+F (W 0::z))/2)]
    simp only [←sum_div,pow_succ,div_div]
    rw [mul_comm (2:ℝ) (2^n)]
    congr 1
    apply sum_congr rfl
    intro j _
    exact add_comm _ _

private lemma flip_lists {ι:Type*} [DecidableEq ι] (l:List ι) (nd:l.Nodup) (W ω:ι→Bool) (i:ι) :
    let g := fun σ : ι→Bool => (l.filter σ).map W
    g ω=g (Function.update ω i (!ω i)) ∨ ∃ a b:List Bool,
    (g ω=a++W i::b ∧ g (Function.update ω i (!ω i))=a++b) ∨
    (g ω=a++b ∧ g (Function.update ω i (!ω i))=a++W i::b) := by
  intro g
  by_cases hi : i∈l
  · obtain ⟨u,v,h⟩ := List.append_of_mem hi
    subst l
    simp only [List.nodup_append,List.nodup_cons] at nd
    have hu : i∉u := fun h => nd.2.2 i h i (by simp) rfl
    have hv := nd.2.1.1
    have filter_eq (t:List ι) (nt:i∉t) (b:Bool) : t.filter (Function.update ω i b)=t.filter ω := by
      apply List.filter_congr
      intro x hx
      rw [Function.update_of_ne (show x≠i by intro he; subst x; exact nt hx)]
    right
    refine ⟨(u.filter ω).map W,(v.filter ω).map W,?_⟩
    cases hω : ω i <;> simp [g,List.filter_append,List.map_append,filter_eq u hu,filter_eq v hv,hω]
  · left
    dsimp only [g]
    congr 1
    apply List.filter_congr
    intro j hj
    rw [Function.update_of_ne (show j≠i by intro he; subst j; exact hi hj)]

end Green92Typical

namespace Green92Typical
private lemma pairs_len (a:ℕ) (z:List Bool) : (pairs a z).length=2*a+z.length := by
  induction a with
  | zero => simp [pairs]
  | succ a ih => simp only [pairs,List.length_cons,ih]; omega

private lemma idx_pairs (a:ℕ) (z:List Bool) (j:ℕ) (hj:j<2*a) :
    (pairs a z)[j]? = some (decide (j%2=1)) := by
  induction a generalizing j with
  | zero => omega
  | succ a ih =>
    cases j with
    | zero => simp [pairs]
    | succ j =>
      cases j with
      | zero => simp [pairs]
      | succ j =>
        simp only [pairs,List.getElem?_cons_succ]
        rw [ih j (by omega)]
        simp [show (j+1+1)%2 = j%2 by omega]

private lemma idx_tail (a:ℕ) (z:List Bool) (j:ℕ) :
    (pairs a z)[2*a+j]? = z[j]? := by
  induction a with
  | zero => simp [pairs]
  | succ a ih =>
    rw [show 2*(a+1)+j=(2*a+j)+1+1 by omega]
    simpa only [pairs,List.getElem?_cons_succ] using ih

private lemma word_shape (n b:ℕ) (hm:n%4=3) (hb:b≤2*(n/4)+1) :
    let W (i:Fin n) : Bool := decide (i.val%2=if i.val<2*b then 1 else 0)
    List.ofFn W = pairs b (true::pairs (2*(n/4)+1-b) []) := by
  intro W
  let c := 2*(n/4)+1-b
  have nn : n=2*b+1+2*c := by dsimp [c]; omega
  change _ = pairs b (true::pairs c [])
  apply List.ext_getElem
  · simp only [List.length_ofFn,pairs_len,List.length_cons,List.length_nil]; omega
  · intro j hj₁ hj₂
    rw [List.getElem_ofFn]
    change decide (j%2=if j<2*b then 1 else 0)=_
    apply Option.some.inj
    rw [←List.getElem?_eq_getElem hj₂]
    by_cases jj : j<2*b
    · rw [if_pos jj,idx_pairs b _ j jj]
    · rw [if_neg jj]
      by_cases je : j=2*b
      · subst j
        rw [←Nat.add_zero (2*b),idx_tail]
        simp
      · obtain ⟨l,el⟩ : ∃ l, j=2*b+(l+1) := ⟨j-2*b-1,by omega⟩
        have hl : l<2*c := by rw [List.length_ofFn] at hj₁; omega
        rw [el,idx_tail,List.getElem?_cons_succ,idx_pairs c [] l hl]
        simp; omega

private lemma lip {n:ℕ} (W:Fin n→Bool) (ω:Fin n→Bool) (i:Fin n) :
    |((maskTrace W ω).length:ℝ)-((maskTrace W (Function.update ω i (!ω i))).length:ℝ)|≤1 ∧
    |(rises (maskTrace W ω):ℝ)-(rises (maskTrace W (Function.update ω i (!ω i))):ℝ)|≤1 := by
  have a := flip_lists (List.finRange n) (List.nodup_finRange n) W ω i
  change maskTrace W ω=maskTrace W (Function.update ω i (!ω i)) ∨ _ at a
  rcases a with e|⟨u,v,e|e⟩
  · simp [e]
  all_goals
    rcases e with ⟨e₁,e₂⟩
    dsimp only at e₁ e₂
    change maskTrace W ω=_ at e₁
    change maskTrace W (Function.update ω i (!ω i))=_ at e₂
    rw [e₁,e₂]
    simp only [List.length_append,List.length_cons,Nat.cast_add,Nat.cast_one]
    rcases rise_insert u v (W i) with e|e <;> rw [e] <;> push_cast <;> constructor <;> rw [abs_le] <;> constructor <;> linarith

private lemma tails {n:ℕ} (hn:0<n) (f:(Fin n→Bool)→ℝ) (c d:ℝ) (hd:4≤d)
    (hdiff:∀ ω i,|f ω-f (Function.update ω i (!ω i))|≤1)
    (cent: |(∑ ω:Fin n→Bool,f ω)/(2:ℝ)^n-c|≤2) :
    ((univ.filter (fun ω : Fin n→Bool => d < |f ω-c|)).card:ℝ)/(2:ℝ)^n ≤
      2*exp (-2*(d/2)^2/n) := by
  classical
  let μ := (∑ ω:Fin n→Bool,f ω)/(2:ℝ)^n
  let A := univ.filter (fun ω:Fin n→Bool => f ω≤μ-d/2)
  let B := univ.filter (fun ω:Fin n→Bool => -f ω≤ -μ-d/2)
  have s2 : (∑ _i:Fin n,(1:ℝ)^2)=n := by simp
  have s2p : 0<(∑ _i:Fin n,(1:ℝ)^2) := by rw [s2]; exact_mod_cast hn
  have left : (A.card:ℝ)/(2:ℝ)^n≤exp (-2*(d/2)^2/n) := by
    simpa only [A,μ,Fintype.card_fin,s2] using mcdiarmid_lower_tail f (fun _=>1) hdiff
      (by linarith : 0≤d/2) s2p
  have flip : ∀ ω i,|-f ω- -f (Function.update ω i (!ω i))|≤1 := by
    intro ω i
    rw [show -f ω- -f (Function.update ω i (!ω i)) = -(f ω-f (Function.update ω i (!ω i))) by ring, abs_neg]; exact hdiff ω i
  have right : (B.card:ℝ)/(2:ℝ)^n≤exp (-2*(d/2)^2/n) := by
    simpa only [B,μ,Fintype.card_fin,s2,sum_neg_distrib,neg_div] using
      mcdiarmid_lower_tail (fun ω=> -f ω) (fun _=>1) flip (by linarith : 0≤d/2) s2p
  have sub : univ.filter (fun ω:Fin n→Bool => d < |f ω-c|) ⊆ A∪B := by
    intro ω h
    have o := (mem_filter.mp h).2
    change |μ-c|≤2 at cent
    rw [abs_le] at cent
    rw [lt_abs] at o
    apply mem_union.mpr
    rcases o with o|o
    · right; exact mem_filter.mpr ⟨mem_univ _,by linarith⟩
    · left; exact mem_filter.mpr ⟨mem_univ _,by linarith⟩
  have count := (card_le_card sub).trans (card_union_le A B)
  have vv := (Nat.cast_le (α:=ℝ)).mpr count
  rw [Nat.cast_add] at vv
  have v := div_le_div_of_nonneg_right vv (show 0≤(2:ℝ)^n by positivity)
  rw [add_div] at v
  linarith

end Green92Typical


namespace Green92Typical
private noncomputable def subsets {n:ℕ} : (Fin n→Bool) ≃ Finset (Fin n) where
  toFun ω := univ.filter (fun i => ω i = true)
  invFun S i := decide (i∈S)
  left_inv ω := by funext i; simp
  right_inv S := by ext i; simp

private lemma masks {n:ℕ} (W:Fin n→Bool) (A:Finset (List Bool)) :
    (∑ w∈A,((univ.filter (fun S : Finset (Fin n) => Green92.trace W S=w)).card:ℝ)/Fintype.card (Finset (Fin n))) =
      ((univ.filter (fun ω:Fin n→Bool => maskTrace W ω∈A)).card:ℝ)/(2:ℝ)^n := by
  classical
  rw [←sum_div,←Nat.cast_sum,sum_card_fiberwise_eq_card_filter]
  have eq (ω:Fin n→Bool) : Green92.trace W (subsets ω)=maskTrace W ω := by
    simp [subsets,Green92.trace,maskTrace]
  have ex : ((univ.filter (fun ω : Fin n→Bool => maskTrace W ω∈A)).map subsets.toEmbedding) =
      univ.filter (fun S : Finset (Fin n) => Green92.trace W S∈A) := by
    ext S
    simp only [Finset.mem_map,mem_filter,mem_univ,true_and,Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨ω,h,rfl⟩; rwa [eq]
    · intro h; refine ⟨subsets.symm S,?_,subsets.apply_symm_apply S⟩
      simpa only [←eq,Equiv.apply_symm_apply] using h
  rw [←ex,card_map]
  simp

private lemma decay (n k:ℕ) (kn:n=4*k+3) (hk:100≤log (k:ℝ)) (k7:7≤k) :
    let d := sqrt k*log k
    4≤d ∧ exp (-2*(d/2)^2/n) ≤ 1/(n:ℝ)^2 ∧
      1/(n:ℝ)^2 ≤ (log n)^7/(n:ℝ)^(3/2:ℝ) := by
  intro d
  have kpos : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have npos : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have kk : (7:ℝ)≤k := by exact_mod_cast k7
  have nn : (n:ℝ)≤(k:ℝ)^2 := by
    rw [kn]; push_cast; nlinarith [mul_nonneg (show 0≤(k:ℝ)-7 by linarith) kpos.le]
  have n7 : (n:ℝ)≤7*(k:ℝ) := by rw [kn]; push_cast; linarith
  have ln : log (n:ℝ)≤2*log (k:ℝ) := by
    simpa [log_pow] using Real.log_le_log npos nn
  have log1 : 1≤log (n:ℝ) := by
    have nk : (k:ℝ)≤n := by exact_mod_cast (by omega : k≤n)
    linarith [log_le_log kpos nk]
  have s1 : 1 ≤ Real.sqrt (k:ℝ) := (Real.one_le_sqrt).mpr (by linarith)
  have dlo : 4≤d := by dsimp [d]; nlinarith [mul_le_mul_of_nonneg_right s1 (by linarith : 0≤log (k:ℝ))]
  refine ⟨dlo,?_,?_⟩
  · have upper : 2*log (n:ℝ) * n ≤ 2*(d/2)^2 := by
      calc _ ≤ (4*log (k:ℝ))*(7*(k:ℝ)) := by exact mul_le_mul (by linarith) n7 npos.le (by linarith)
           _ ≤ _ := by
              dsimp [d]
              have x : 56*log (k:ℝ) ≤ log (k:ℝ)^2 := by nlinarith [mul_nonneg (show 0≤log (k:ℝ)-56 by linarith) (show 0≤log (k:ℝ) by linarith)]
              have y := mul_le_mul_of_nonneg_right x kpos.le
              rw [div_pow,mul_pow,Real.sq_sqrt kpos.le]
              linarith
    calc exp (-2*(d/2)^2/n) ≤ exp (-(2*log (n:ℝ))) := by
          apply exp_le_exp.mpr
          apply (div_le_iff₀ npos).mpr
          linarith
         _ = _ := by rw [Real.exp_neg,show 2*log (n:ℝ)=log ((n:ℝ)^2) by rw [log_pow]; norm_num,
            Real.exp_log (by positivity),one_div]
  · have nr : 1≤(n:ℝ) := by exact_mod_cast (by omega : 1≤n)
    have nr2 : (n:ℝ)^(3/2:ℝ)≤(n:ℝ)^2 := by
      rw [←Real.rpow_natCast (n:ℝ) 2]
      apply Real.rpow_le_rpow_of_exponent_le nr
      norm_num
    exact div_le_div₀ (pow_nonneg (by linarith) 7) (one_le_pow₀ log1) (by positivity) nr2

private theorem typical :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ n:ℕ in atTop,n%4=3 →
    let k := n/4
    let W (b:ℕ) (i:Fin n) : Bool := decide (i.val%2=if i.val<2*b then 1 else 0)
    let p (b:ℕ) (w:List Bool) := ((univ.filter (fun S:Finset (Fin n) => Green92.trace (W b) S=w)).card:ℝ)/Fintype.card (Finset (Fin n))
    let T := univ.image (Green92.trace (W k)) ∪ univ.image (Green92.trace (W (k+1)))
    let E (w:List Bool) := |(w.length:ℝ)-2*k|≤ sqrt k*log k ∧
      |(((w.zip w.tail).count (false,true):ℕ):ℝ)-2*k/3|≤ sqrt k*log k
    ∑ w∈T.filter (fun w=>¬E w),(p k w+p (k+1) w) ≤ C*(log n)^7/(n:ℝ)^(3/2:ℝ) := by
  classical
  refine ⟨8,by norm_num,?_⟩
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 100)
  filter_upwards [eventually_ge_atTop (4*(K+7))] with n hn
  intro hm k W p T E
  let d := sqrt k*log k
  have kn : n=4*k+3 := by dsimp [k]; omega
  have hk : 100≤log (k:ℝ) := hK k (by omega)
  have h7 : 7≤k := by omega
  obtain ⟨dlo,small,smaller⟩ := decay n k kn hk h7
  have h (b:ℕ) (hb:b≤2*k+1) :
      ∑ w∈T.filter (fun w=>¬E w),p b w ≤ 4*(1/(n:ℝ)^2) := by
    rw [show (∑ w∈T.filter (fun w=>¬E w),p b w)=_ from masks (W b) (T.filter (fun w=>¬E w))]
    let g (ω:Fin n→Bool) := maskTrace (W b) ω
    let f (ω:Fin n→Bool) := ((g ω).length:ℝ)
    let a (ω:Fin n→Bool) := (rises (g ω):ℝ)
    have lf : |(∑ ω,f ω)/(2:ℝ)^n-2*k|≤2 := by
      change |(∑ ω:Fin n→Bool,((maskTrace (W b) ω).length:ℝ))/(2:ℝ)^n-2*k|≤2
      rw [avg_mask (W b) (fun z => (z.length:ℝ)),length_mean,List.length_ofFn,kn]
      push_cast
      rw [abs_le]; constructor <;> linarith
    have ar : |(∑ ω,a ω)/(2:ℝ)^n-2*k/3|≤2 := by
      change |(∑ ω:Fin n→Bool,(rises (maskTrace (W b) ω):ℝ))/(2:ℝ)^n-2*k/3|≤2
      rw [avg_mask (W b) (fun z => (rises z:ℝ)),word_shape n b hm hb]
      have hh := rise_mean b (2*k+1-b)
      change _≤2
      have eq : b + (2*k+1-b) = 2*k+1 := by omega
      rw [eq,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hh
      rw [abs_le] at hh ⊢
      constructor <;> linarith [hh.1,hh.2]
    have L := tails (by omega : 0<n) f (2*k) d dlo (fun ω i => (lip (W b) ω i).1) lf
    have A := tails (by omega : 0<n) a (2*k/3) d dlo (fun ω i => (lip (W b) ω i).2) ar
    let X := univ.filter (fun ω:Fin n→Bool=>d < |f ω-2*k|)
    let Y := univ.filter (fun ω:Fin n→Bool=>d < |a ω-2*k/3|)
    have sub : univ.filter (fun ω:Fin n→Bool=>g ω∈T.filter (fun w=>¬E w)) ⊆ X∪Y := by
      intro ω hω
      have he := (mem_filter.mp (mem_filter.mp hω).2).2
      dsimp only [E] at he
      rw [rise_zip] at he
      change ¬(|f ω-2*k|≤d ∧ |a ω-2*k/3|≤d) at he
      apply mem_union.mpr
      by_cases hl : |f ω-2*k|≤d
      · exact Or.inr (mem_filter.mpr ⟨mem_univ _,lt_of_not_ge (fun hz => he ⟨hl,hz⟩)⟩)
      · exact Or.inl (mem_filter.mpr ⟨mem_univ _,lt_of_not_ge hl⟩)
    have count := (card_le_card sub).trans (card_union_le X Y)
    have vv := (Nat.cast_le (α:=ℝ)).mpr count
    rw [Nat.cast_add] at vv
    have cb := div_le_div_of_nonneg_right vv (show 0≤(2:ℝ)^n by positivity)
    rw [add_div] at cb
    change (X.card:ℝ)/_≤_ at L
    change (Y.card:ℝ)/_≤_ at A
    exact cb.trans (by linarith only [L,A,small])
  rw [sum_add_distrib]
  calc _ ≤ 4*(1/(n:ℝ)^2)+4*(1/(n:ℝ)^2) := add_le_add (h k (by omega)) (h (k+1) (by omega))
       _ ≤ 8*((log n)^7/(n:ℝ)^(3/2:ℝ)) := by linarith
       _ = _ := by ring

end Green92Typical

theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1.H1 := Green92Typical.typical
