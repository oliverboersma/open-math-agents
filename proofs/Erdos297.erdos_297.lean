import FormalConjectures.ErdosProblems.«297»
import Mathlib

/-!
The exact unit-target result follows from the general reciprocal-sum theorem
and the normalization identity proved below in PartitionLimit.unit_entropy_value.

This proof assembles contributions already accepted in this repository. The four
reductions are PRs #3382, #4177, #4531 and #4678. Their six leaf proofs are PRs
#3616 (calibration), #3634 (partition limit), #4409 (bounded counting), #4570
(integer representation), #4958 (reservoir density) and #5072 (modular
correction). The source for each is pinned at upstream commit
5203c7710d8af69baf3cda42828fa176ea0df365. The namespaces isolate the six
original solution declarations so their results can be applied together.
-/

section


/-! Tilt the independent subset choices by their reciprocal mass. On the fiber of rational
sum x the tilt is constant, so the combinatorial loss is exactly its probability. -/
namespace OMA.R_Erdos297_erdos_297_variants_general_R1
open Filter Real Finset Erdos297
open scoped Topology

/-- Calibration of the reciprocal mass fixes the critical parameter. -/
def H1 : Prop := ∀ x : ℚ, 0 < x → ∃! l : ℝ, massIntegral l = x

/-- Riemann-sum limit of the tilted partition function, with entropy in bits. -/
def H2 : Prop := ∀ (x : ℚ) (l : ℝ), 0 < x → massIntegral l = x →
    Tendsto (fun N : ℕ => l * x + log (∏ n ∈ Icc 1 N, (1 + exp (-l * (N : ℝ) / n))) / N) atTop
      (𝓝 (exponentOf x * log 2))

/-- Under the calibrated independent choices the exact rational fiber has subexponential cost. -/
def H3 : Prop := ∀ (x : ℚ) (l : ℝ), 0 < x → massIntegral l = x →
    ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, exp (-η * N) ≤ ((∑ A ∈ ((Icc 1 N).powerset.filter fun (A : Finset ℕ) => (∑ n ∈ A, (1 : ℚ) / n) = x), ∏ n ∈ A, exp (-l * N / n)) / (∏ n ∈ Icc 1 N, (1 + exp (-l * (N : ℝ) / n))))

theorem main : H1 → H2 → H3 → type_of% @Erdos297.erdos_297.variants.general := by
  intro h1 h2 h3 x hx
  let partition (l : ℝ) (N : ℕ) : ℝ :=
    ∏ n ∈ Icc 1 N, (1 + exp (-l * N / n))

  let prob (l : ℝ) (x : ℚ) (N : ℕ) : ℝ :=
    (∑ A ∈ ((Icc 1 N).powerset.filter fun (A : Finset ℕ) => (∑ n ∈ A, (1 : ℚ) / n) = x),
      ∏ n ∈ A, exp (-l * N / n)) / partition l N

  have part_pos (l : ℝ) (N : ℕ) : 0 < partition l N :=
    prod_pos fun _ _ => by positivity

  have prob_le_one (l : ℝ) (x : ℚ) (N : ℕ) : prob l x N ≤ 1 := by
    apply (div_le_iff₀ (part_pos l N)).2
    rw [one_mul]
    dsimp only [partition]
    rw [prod_one_add]
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intros
    positivity

  have exact_fiber (l : ℝ) (x : ℚ) (N : ℕ) :
      prob l x N = (count x N : ℝ) * exp (-l * N * x) / partition l N := by
    unfold prob count
    congr 1
    calc
      _ = ∑ _A ∈ ((Icc 1 N).powerset.filter fun (A : Finset ℕ) => (∑ n ∈ A, (1 : ℚ) / n) = x),
            exp (-l * N * x) := by
        apply sum_congr rfl
        intro A hA
        have hs : (∑ n ∈ A, (1 : ℝ) / n) = x := by
          have hrat : (∑ n ∈ A, (1 : ℚ) / n) = x := (mem_filter.1 hA).2
          simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using congrArg (fun t : ℚ => (t : ℝ)) hrat
        rw [← Real.exp_sum, ← hs, mul_sum]
        simp [div_eq_mul_inv]
      _ = _ := by simp
  refine ⟨h1 x hx, ?_⟩
  obtain ⟨l, hl, _⟩ := h1 x hx
  have hp : Tendsto (fun N : ℕ => log (prob l x N) / N) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [h3 x l hx hl (ε/2) (by positivity), eventually_gt_atTop 0] with N hN hNp
    have hpos : 0 < prob l x N := (exp_pos _).trans_le hN
    have hcast : (0 : ℝ) < N := by exact_mod_cast hNp
    have hlo := Real.log_le_log (exp_pos _) hN
    rw [Real.log_exp] at hlo
    have hhi := Real.log_nonpos hpos.le (prob_le_one l x N)
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨(lt_div_iff₀ hcast).2 (by nlinarith), lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg hhi hcast.le) hε⟩
  have hpart : Tendsto (fun N : ℕ => l * x + log (partition l N) / N) atTop (𝓝 (exponentOf x * log 2)) := h2 x l hx hl
  have hlim := (hpart.add hp).div_const (log 2)
  have htwo : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  simp only [add_zero, mul_div_cancel_right₀ _ htwo] at hlim
  apply hlim.congr'
  filter_upwards [h3 x l hx hl 1 zero_lt_one, eventually_gt_atTop 0] with N hN hn
  have hpos : 0 < prob l x N := (exp_pos _).trans_le hN
  rw [exact_fiber] at hpos ⊢
  have hc : (0 : ℝ) < count x N := by
    by_contra! h
    have hzero : (count x N : ℝ) = 0 := le_antisymm h (by positivity)
    simp [hzero] at hpos
  rw [log_div (mul_pos hc (exp_pos _)).ne' (part_pos l N).ne',
    log_mul hc.ne' (exp_pos _).ne', log_exp, logb]
  have hn' : (N : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  <;> ring

end OMA.R_Erdos297_erdos_297_variants_general_R1

end

section



/-! # Passing from a sublevel count to an exact Egyptian fraction

The sublevel entropy estimate only counts sums below a fixed threshold. The
arithmetic input reserves a small complement in which each partial sum can
be completed. Restricting a subset to the dense part loses at most one bit
per deleted denominator, since the deleted trace and any completion recover
the original set. The calibrated weight is constant on every exact fiber.
This follows the entropy and absorption split in Conlon et al., arXiv:2404.16016,
Sections 2 and 4. -/

namespace OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1

open Finset Real Filter Topology Erdos297
open scoped Classical

-- A strictly smaller sublevel has almost all the exponential entropy
-- required at the calibrated tilt. A sublevel uses an inequality only.
def H1 : Prop := ∀ (x : ℚ) (l : ℝ), 0 < x → massIntegral l = x → ∀ ε > (0:ℝ),
    ∃ d : ℚ, 0 < d ∧ ∀ᶠ N : ℕ in atTop,
      exp (-ε*N) * (∏ n ∈ Icc 1 N, (1+exp (-l*(N:ℝ)/n))) ≤
      (((Icc 1 N).powerset.filter (fun A : Finset ℕ => (∑ n ∈ A, (1:ℚ)/n) ≤ x-d)).card:ℝ) *
        exp (-l*N*(x:ℝ))

-- A small set of reserved denominators can complete every eligible partial
-- sum. Taking the intersection with U recovers the partial choice exactly.
def H2 : Prop := ∀ (x d : ℚ), 0 < x → 0 < d → ∀ δ > (0:ℝ), ∀ᶠ N : ℕ in atTop,
    ∃ U ⊆ Icc 1 N, (((Icc 1 N) \ U).card:ℝ) ≤ δ*N ∧
      ∀ A ⊆ U, (∑ n ∈ A, (1:ℚ)/n) ≤ x-d → ∃ B ⊆ Icc 1 N,
        B ∩ U = A ∧ (∑ n ∈ B, (1:ℚ)/n) = x

lemma trace_count {α : Type*} [DecidableEq α] (P U : Finset α) (F G : Finset (Finset α))
    (contained : ∀ A ∈ F, A ⊆ P) (complete : ∀ A ∈ F, ∃ B ∈ G, B ∩ U = A ∩ U) :
    F.card ≤ G.card * 2^(P \ U).card := by
  classical
  choose C good trace using complete
  let f (A : F) : G × (P \ U).powerset :=
    (⟨C A.val A.property,good A.val A.property⟩,⟨A.val \ U,mem_powerset.mpr
      (fun a h => mem_sdiff.mpr ⟨contained _ A.property (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩)⟩)
  have inj : Function.Injective f := by
    intro A B eq
    have e₁ := congrArg (fun w : G × (P \ U).powerset => (w.1:Finset α)) eq
    have e₂ := congrArg (fun w : G × (P \ U).powerset => (w.2:Finset α)) eq
    change C A.val A.property = C B.val B.property at e₁
    change A.val \ U = B.val \ U at e₂
    have e₃ : A.val ∩ U = B.val ∩ U := by rw [←trace _ A.property,←trace _ B.property,e₁]
    apply Subtype.ext
    ext a
    by_cases mem : a ∈ U
    · simpa [mem] using Finset.ext_iff.mp e₃ a
    · simpa [mem] using Finset.ext_iff.mp e₂ a
  simpa using Fintype.card_le_of_injective f inj

lemma exact_weight {N : ℕ} {x : ℚ} (l : ℝ) (A : Finset ℕ) (h : ∑ n ∈ A,(1:ℚ)/n=x) :
    ∏ n ∈ A, exp (-l*(N:ℝ)/n) = exp (-l*N*(x:ℝ)) := by
  have hs : ∑ n ∈ A,(1:ℝ)/n=(x:ℝ) := by
    simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using congrArg (fun r : ℚ => (r:ℝ)) h
  rw [←Real.exp_sum,←hs,mul_sum]
  congr 1
  apply sum_congr rfl
  intro n _
  ring

theorem main : H1 → H2 → OMA.R_Erdos297_erdos_297_variants_general_R1.H3 := by
  intro entropy absorb x l hx calibration η hη
  have ep : 0 < η/2 := by positivity
  obtain ⟨d,hd,many⟩ := entropy x l hx calibration (η/2) ep
  filter_upwards [many,absorb x d hx hd (η/2) ep] with N hmany hreservoir
  classical
  let P := Icc 1 N
  let F := P.powerset.filter (fun A : Finset ℕ => (∑ n ∈ A,(1:ℚ)/n) ≤ x-d)
  let G := P.powerset.filter (fun A : Finset ℕ => (∑ n ∈ A,(1:ℚ)/n) = x)
  let Z := ∏ n ∈ P, (1+exp (-l*(N:ℝ)/n))
  let X := exp (-l*N*(x:ℝ))
  obtain ⟨U,hU,deleted,complete⟩ := hreservoir
  have traces (A : Finset ℕ) (mem : A ∈ F) : ∃ B ∈ G, B ∩ U = A ∩ U := by
    have small := (mem_filter.mp mem).2
    have tr : (∑ n ∈ A ∩ U,(1:ℚ)/n) ≤ x-d :=
      (sum_le_sum_of_subset_of_nonneg inter_subset_left (fun n _ _ => by positivity)).trans small
    obtain ⟨B,subB,e,s⟩ := complete (A ∩ U) inter_subset_right tr
    exact ⟨B,mem_filter.mpr ⟨mem_powerset.mpr subB,s⟩,e⟩
  have cnt := trace_count P U F G (fun A h => mem_powerset.mp (mem_filter.mp h).1) traces
  have cr : (F.card:ℝ) ≤ G.card * (2:ℝ)^(P \ U).card := by exact_mod_cast cnt
  let E := exp ((η/2)*(N:ℝ))
  have bound : (2:ℝ)^(P \ U).card ≤ E := calc
    _ ≤ (exp 1)^(P \ U).card := by
      apply pow_le_pow_left₀ (by norm_num)
      linarith [Real.add_one_le_exp (1:ℝ)]
    _ = exp ((P \ U).card:ℝ) := by rw [←Real.exp_nat_mul]; simp
    _ ≤ E := Real.exp_le_exp.mpr deleted
  have Zpos : 0<Z := prod_pos (fun n _ => by positivity)
  have Xpos : 0<X := exp_pos _
  have countLoss : (F.card:ℝ)*X ≤ ((G.card:ℝ)*X)*E := calc
    _ ≤ ((G.card:ℝ)*E)*X := by gcongr; exact cr.trans (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg _))
    _ = _ := by ring
  have weighted : (∑ A ∈ G, ∏ n ∈ A, exp (-l*(N:ℝ)/n)) = G.card*X := calc
    _ = ∑ _A ∈ G,X := by
      apply sum_congr rfl; intro A hA
      exact exact_weight l A (mem_filter.mp hA).2
    _ = _ := by simp
  change exp (-η*(N:ℝ)) ≤ (∑ A ∈ G, ∏ n ∈ A, exp (-l*(N:ℝ)/n))/Z
  rw [weighted,le_div_iff₀ Zpos]
  apply le_of_mul_le_mul_right _ (show 0<E from exp_pos _)
  have id : exp (-η*(N:ℝ))*Z*E=exp (-(η/2)*N)*Z := by
    dsimp [E]
    rw [mul_right_comm,←exp_add]
    congr 2
    ring
  rw [id]
  exact hmany.trans countLoss

end OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1

end

section



/-! Conlon, Fox, He, Mubayi, Pham, Suk and Verstraëte, A question of Erdős
and Graham on Egyptian fractions, Section 4. The prime-power corrections
leave an integer multiple of a fixed reciprocal. For a fixed target x,
only finitely many such integers occur, so all their representations fit
in the reserved progression once N is large enough. -/
namespace OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1

open Finset Filter
open scoped Topology

/-- Prime-power cleaning with the multiples of K reserved. The correction
only has to control the denominator of the positive residual. -/
def H1 : Prop := ∀ (x d : ℚ), 0 < x → 0 < d → ∀ δ > (0:ℝ),
  ∃ K : ℕ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
    ∃ U ⊆ Icc 1 N, (((Icc 1 N) \ U).card:ℝ) ≤ δ*N ∧ (∀ u ∈ U, ¬ K ∣ u) ∧
      ∀ A ⊆ U, (∑ n ∈ A, (1:ℚ)/n) ≤ x-d → ∃ P ⊆ Icc 1 N,
        Disjoint P U ∧ (∀ p ∈ P, ¬ K ∣ p) ∧
        ∃ j : ℕ, 0 < j ∧ (j:ℚ)/K = x-(∑ n ∈ A, (1:ℚ)/n)-(∑ n ∈ P, (1:ℚ)/n)

/-- Each positive integer has a finite representation by distinct unit fractions. -/
def H2 : Prop := ∀ j : ℕ, 0 < j → ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n) ∧
  (∑ n ∈ S, (1:ℚ)/n) = j

lemma scale_set (S : Finset ℕ) {K : ℕ} (hk : 0 < K) :
    (∑ n ∈ S.image (K*·), (1:ℚ)/n) = (∑ n ∈ S, (1:ℚ)/n)/K := by
  rw [sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hk hab),sum_div]
  apply sum_congr rfl
  intro n hn
  push_cast
  ring

theorem main : H1 → H2 → OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1.H2 := by
  classical
  intro clean integers x d hx hd δ hδ
  obtain ⟨K,hk,hn⟩ := clean x d hx hd δ hδ
  have allj (j : ℕ) : ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n) ∧ (∑ n ∈ S, (1:ℚ)/n) = j := by
    rcases j.eq_zero_or_pos with rfl|hj
    · exact ⟨∅,by simp,by simp⟩
    · exact integers j hj
  choose S pos total using allj
  let J := ⌈x*K⌉₊
  let cutoff := (range (J+1)).sup (fun j => (S j).sup id)
  filter_upwards [hn,eventually_ge_atTop (K*cutoff)] with N hclean hN
  obtain ⟨U,hU,small,skip,correct⟩ := hclean
  refine ⟨U,hU,small,?_⟩
  intro A hA low
  obtain ⟨P,hP,apart,avoid,j,hj,eq⟩ := correct A hA low
  have hK : (0:ℚ)<K := by exact_mod_cast hk
  have jle : j ≤ J := by
    have ha : 0 ≤ ∑ n ∈ A, (1:ℚ)/n := by positivity
    have hp : 0 ≤ ∑ n ∈ P, (1:ℚ)/n := by positivity
    apply (Nat.cast_le (α := ℚ)).mp
    apply le_trans _ (Nat.le_ceil (x*K))
    exact (div_le_iff₀ hK).mp (by linarith only [eq,ha,hp])
  let V := (S j).image (K*·)
  have bound : V ⊆ Icc 1 N := by
    intro v hv
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
    have H : b ≤ cutoff := (Finset.le_sup (f := id) hb).trans
      (Finset.le_sup (f := fun i => (S i).sup id) (mem_range.mpr (by omega : j < J+1)))
    exact mem_Icc.mpr ⟨Nat.mul_pos hk (pos j b hb),(Nat.mul_le_mul_left K H).trans hN⟩
  have mult : ∀ v ∈ V, K ∣ v := by
    intro v hv
    obtain ⟨b,_,rfl⟩ := mem_image.mp hv
    exact dvd_mul_right K b
  have dPU : Disjoint A P := (apart.mono_right hA).symm
  have dV : Disjoint (A ∪ P) V := by
    apply Finset.disjoint_left.mpr
    intro v hv hV
    rcases mem_union.mp hv with a|p
    · exact skip v (hA a) (mult v hV)
    · exact avoid v p (mult v hV)
  refine ⟨(A ∪ P) ∪ V, union_subset (union_subset (hA.trans hU) hP) bound,?_,?_⟩
  · ext b
    simp only [mem_inter,mem_union]
    constructor
    · rintro ⟨(hb|hb)|hb,hu⟩
      · exact hb
      · exact (Finset.disjoint_left.mp apart hb hu).elim
      · exact (skip b hu (mult b hb)).elim
    · exact fun hb => ⟨Or.inl (Or.inl hb),hA hb⟩
  · rw [sum_union dV,sum_union dPU,show (∑ n ∈ V, (1:ℚ)/n) = (j:ℚ)/K by
        rw [scale_set _ hk,total]]
    linarith only [eq]

end OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1

end

section


 /-! Conlon, Fox, He, Mubayi, Pham, Suk and Verstraëte,
A question of Erdős and Graham on Egyptian fractions, sections 3 and 4.
The dense powersmooth set avoids the correction denominators. For each
prime power one can choose a small subset of its reserved denominators
to remove that prime power from the denominator of the current rational.
The descent, its sum of costs, disjointness, and positivity are proved here. -/
namespace OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1_H1_R1
open Finset Filter
open scoped Classical

def H1 : Prop := ∀ (x : ℚ), 0 < x → ∀ δ > (0:ℝ),
  ∃ ε : ℝ, 0 < ε ∧ ε < 1/2 ∧ ∀ L₀ : ℕ, ∃ L ≥ L₀,
    let J (i : ℕ) := (Icc 1 i).lcm id
    let K := J L
    let R (i : ℕ) := (Icc 1 (i*i)).filter fun n => IsPrimePow i ∧ i∣n ∧ Nat.Coprime i (n/i) ∧
        (i:ℝ)^ε ≤ (n/i:ℕ) ∧ ((n/i:ℕ):ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬ K ∣ n
    ∀ᶠ N : ℕ in atTop, ∃ B ≥ L, ∃ U ⊆ Icc 1 N,
      (((Icc 1 N) \ U).card:ℝ) ≤ δ*N ∧ x.den ∣ J B ∧
      (∀ u ∈ U, u ∣ J B ∧ ¬ K ∣ u) ∧
      (∀ i ∈ Ioc L B, R i ⊆ Icc 1 N ∧ Disjoint U (R i)) ∧
      (∀ i ∈ Ioc L B, ∀ j ∈ Ioc L B, i < j → Disjoint (R i) (R j))

def H2 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1/2 → ∀ d : ℚ, 0 < d →
  ∃ L₀ : ℕ, ∀ L ≥ L₀,
    let J (i : ℕ) := (Icc 1 i).lcm id
    let K := J L
    let R (i : ℕ) := (Icc 1 (i*i)).filter fun n => IsPrimePow i ∧ i∣n ∧ Nat.Coprime i (n/i) ∧
        (i:ℝ)^ε ≤ (n/i:ℕ) ∧ ((n/i:ℕ):ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬ K ∣ n
    ∃ cost : ℕ → ℚ, (∀ B, ∑ i ∈ Ioc L B, cost i < d) ∧
      ∀ i : ℕ, L < i → ∀ z : ℤ, ∃ V ⊆ R i,
        (∑ n ∈ V, (1:ℚ)/n) ≤ cost i ∧ ∃ a : ℤ,
        (a:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V, (1:ℚ)/n

lemma descend (J : ℕ → ℕ) (R : ℕ → Finset ℕ) (cost : ℕ → ℚ)
    (L : ℕ) (step : ∀ i, L < i → ∀ z : ℤ, ∃ V ⊆ R i,
      (∑ n ∈ V, (1:ℚ)/n) ≤ cost i ∧ ∃ a : ℤ,
        (a:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V, (1:ℚ)/n)
    (B : ℕ) (hB : L ≤ B) (apart : ∀ i ∈ Ioc L B, ∀ j ∈ Ioc L B,
      i < j → Disjoint (R i) (R j)) (z : ℤ) :
    ∃ P ⊆ (Ioc L B).biUnion R, (∑ n ∈ P, (1:ℚ)/n) ≤ ∑ i ∈ Ioc L B, cost i ∧
    ∃ a : ℤ, (a:ℚ)/J L = (z:ℚ)/J B - ∑ n ∈ P, (1:ℚ)/n := by
  induction B,hB using Nat.le_induction generalizing z with
  | base => exact ⟨∅,empty_subset _,by simp,z,by simp⟩
  | succ b hb ih =>
    have last : b+1 ∈ Ioc L (b+1) := mem_Ioc.mpr ⟨by omega,le_rfl⟩
    have sub : Ioc L b ⊆ Ioc L (b+1) := fun i hi => mem_Ioc.mpr
      ⟨(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2.trans (Nat.le_succ _)⟩
    obtain ⟨V,hV,hv,a,ha⟩ := step (b+1) (by omega) z
    obtain ⟨P,hP,hp,j,hj⟩ := ih (fun i hi k hk => apart i (sub hi) k (sub hk)) a
    have dj : Disjoint P V := by
      apply disjoint_left.mpr
      intro n hn hnV
      obtain ⟨i,hi,hnR⟩ := mem_biUnion.mp (hP hn)
      exact disjoint_left.mp (apart i (sub hi) _ last (Nat.lt_succ_of_le (mem_Ioc.mp hi).2)) hnR (hV hnV)
    have eq : Ioc L (b+1) = insert (b+1) (Ioc L b) := by
      ext i; simp only [mem_Ioc,mem_insert]; omega
    refine ⟨P∪V,union_subset (fun n hn => ?_) (fun n hn => mem_biUnion.mpr ⟨_,last,hV hn⟩),?_,j,?_⟩
    · obtain ⟨i,hi,hh⟩ := mem_biUnion.mp (hP hn)
      exact mem_biUnion.mpr ⟨_,sub hi,hh⟩
    · rw [sum_union dj,eq,sum_insert (by simp)]
      linarith
    · simp only [Nat.add_sub_cancel] at ha
      rw [sum_union dj,hj,ha]
      ring

lemma grid {T : ℕ} (hT : T ≠ 0) (x : ℚ) (hx : x.den ∣ T)
    (A : Finset ℕ) (hA : ∀ n ∈ A, n∣T) :
    ∃ z : ℤ, (z:ℚ)/T = x-∑ n ∈ A, (1:ℚ)/n := by
  have denom (n : ℕ) (hn : n∣T) : ((T/n:ℕ):ℚ)*(n:ℚ) = T := by
    exact_mod_cast Nat.div_mul_cancel hn
  have rep (n : ℕ) (hn : n∣T) : ((T/n:ℕ):ℚ)/T = 1/n := by
    have nz : n ≠ 0 := fun e => hT (by simpa [e] using hn)
    apply (div_eq_div_iff (by exact_mod_cast hT) (by exact_mod_cast nz)).mpr
    simpa using denom n hn
  refine ⟨x.num*Int.ofNat (T/x.den) - ∑ n ∈ A, (T/n:ℕ),?_⟩
  push_cast
  rw [sub_div,sum_div]
  congr 1
  · conv_rhs => rw [← Rat.num_div_den x]
    apply (div_eq_div_iff (by exact_mod_cast hT) (by exact_mod_cast x.den_nz)).mpr
    rw [mul_assoc,Int.ofNat_eq_natCast,Int.cast_natCast,denom _ hx]
  · exact sum_congr rfl (fun n hn => rep _ (hA _ hn))

theorem main : H1 → H2 → OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1.H1 := by
  intro dense cancel x d hx hd δ hδ
  obtain ⟨ε,hε,he,dense⟩ := dense x hx δ hδ
  obtain ⟨L₀,threshold⟩ := cancel ε hε he d hd
  obtain ⟨L,hL,supply⟩ := dense L₀
  let J (i : ℕ) := (Icc 1 i).lcm id
  let K := J L
  let R (i : ℕ) := (Icc 1 (i*i)).filter fun n => IsPrimePow i ∧ i∣n ∧ Nat.Coprime i (n/i) ∧
        (i:ℝ)^ε ≤ (n/i:ℕ) ∧ ((n/i:ℕ):ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬ K ∣ n
  have pos (i : ℕ) : 0 < J i := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr
    (fun n hn => Nat.ne_of_gt (mem_Icc.mp hn).1))
  obtain ⟨cost,small,step⟩ := threshold L hL
  refine ⟨K,pos L,?_⟩
  filter_upwards [supply] with N data
  obtain ⟨B,hB,U,hU,size,den,divs,space,apart⟩ := data
  refine ⟨U,hU,size,(fun n hn => (divs n hn).2),?_⟩
  intro A hA low
  obtain ⟨z,hz⟩ := grid (pos B).ne' x den A (fun n hn => (divs n (hA hn)).1)
  obtain ⟨P,hP,budget,a,ha⟩ := descend J R cost L step B hB apart z
  have location {n : ℕ} (hn : n ∈ P) : n ∈ Icc 1 N ∧ n ∉ U ∧ ¬K∣n := by
    obtain ⟨i,hi,hh⟩ := mem_biUnion.mp (hP hn)
    exact ⟨(space i hi).1 hh,fun h => disjoint_left.mp (space i hi).2 h hh,(mem_filter.mp hh).2.2.2.2.2.2⟩
  have hpos : (0:ℚ) < (a:ℚ)/K := by
    rw [ha,hz]
    linarith [small B]
  have apos : 0 < a := by
    exact_mod_cast (div_pos_iff_of_pos_right (show (0:ℚ)<K by exact_mod_cast pos L)).mp hpos
  refine ⟨P,(fun n hn => (location hn).1),disjoint_left.mpr (by intro n hn h; exact (location hn).2.1 h),
    (fun n hn => (location hn).2.2),a.toNat,by omega,?_⟩
  rw [show (a.toNat:ℚ) = a by exact_mod_cast Int.toNat_of_nonneg apos.le,ha,hz]
end OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1_H1_R1

end

namespace Calibration



/-! For l <= 0 the integrand is at least 1/(2y), so the integral is undefined and equals 0.
For l > 0 the integrand is bounded by 1/l; dominated convergence gives continuity, the
integrand decreases strictly in l, the value is at least -log l/(1+e) for l < 1 and at most
1/l, and the intermediate value theorem gives the unique solution. -/

open Filter Real Finset Erdos297 MeasureTheory intervalIntegral
open scoped Topology

namespace E297P2

noncomputable def g (l y : ℝ) : ℝ := 1 / (y * (1 + Real.exp (l / y)))

theorem mass_eq (l : ℝ) : massIntegral l = ∫ y in (0:ℝ)..1, g l y := rfl

theorem g_meas (l : ℝ) : Measurable (g l) := by
  unfold g; fun_prop

theorem g_nonneg (l : ℝ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ g l y :=
  div_nonneg zero_le_one (mul_nonneg hy (by positivity))

theorem g_le (l : ℝ) (hl : 0 < l) {y : ℝ} (hy : 0 ≤ y) : g l y ≤ 1 / l := by
  rcases hy.eq_or_lt with h | h
  · subst h; simp [g]; positivity
  · unfold g
    apply one_div_le_one_div_of_le hl
    have e := Real.add_one_le_exp (l / y)
    have : y * (l / y) = l := by field_simp
    nlinarith

theorem g_int (l : ℝ) (hl : 0 < l) : IntervalIntegrable (g l) volume 0 1 := by
  refine (intervalIntegrable_const (c := 1 / l)).mono_fun (g_meas l).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_uIoc (fun y hy => ?_)
  rw [Set.uIoc_of_le zero_le_one] at hy
  show ‖g l y‖ ≤ ‖1 / l‖
  rw [Real.norm_of_nonneg (g_nonneg l hy.1.le), Real.norm_of_nonneg (by positivity)]
  exact g_le l hl hy.1.le

theorem g_int' (l : ℝ) (hl : 0 < l) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    IntervalIntegrable (g l) volume a b :=
  (g_int l hl).mono_set (by
    rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc ha hb)

theorem strict_anti : StrictAntiOn massIntegral (Set.Ioi 0) := by
  intro l1 h1 l2 h2 h12
  simp only [Set.mem_Ioi] at h1 h2
  rw [mass_eq, mass_eq, ← sub_pos, ← intervalIntegral.integral_sub (g_int l1 h1) (g_int l2 h2)]
  apply intervalIntegral_pos_of_pos_on ((g_int l1 h1).sub (g_int l2 h2)) _ zero_lt_one
  intro y hy
  rw [sub_pos]
  unfold g
  apply one_div_lt_one_div_of_lt (by have := hy.1; positivity)
  apply mul_lt_mul_of_pos_left _ hy.1
  have : l1 / y < l2 / y := div_lt_div_of_pos_right h12 hy.1
  linarith [Real.exp_lt_exp.mpr this]

theorem cont : ContinuousOn massIntegral (Set.Ioi 0) := by
  intro l0 hl0
  simp only [Set.mem_Ioi] at hl0
  apply ContinuousAt.continuousWithinAt
  have hev : ∀ᶠ l in 𝓝 l0, l0 / 2 < l := lt_mem_nhds (by linarith)
  show ContinuousAt (fun l => ∫ y in (0:ℝ)..1, g l y) l0
  apply continuousAt_of_dominated_interval (bound := fun _ => 2 / l0)
  · exact Eventually.of_forall (fun l => (g_meas l).aestronglyMeasurable)
  · filter_upwards [hev] with l hl
    refine Eventually.of_forall (fun y hy => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hy
    have hlp : 0 < l := by linarith
    show ‖g l y‖ ≤ 2 / l0
    rw [Real.norm_of_nonneg (g_nonneg l hy.1.le)]
    calc g l y ≤ 1 / l := g_le l hlp hy.1.le
      _ ≤ 2 / l0 := by rw [div_le_div_iff₀ hlp hl0]; linarith
  · exact intervalIntegrable_const
  · refine Eventually.of_forall (fun y hy => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hy
    have hy0 : y ≠ 0 := hy.1.ne'
    show ContinuousAt (fun l => 1 / (y * (1 + Real.exp (l / y)))) l0
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    exact mul_ne_zero hy0 (by positivity)

theorem nonpos (l : ℝ) (hl : l ≤ 0) : massIntegral l = 0 := by
  rw [mass_eq]
  apply intervalIntegral.integral_undef
  intro hint
  have h2 : IntervalIntegrable (fun y : ℝ => y⁻¹) volume 0 1 := by
    have : IntervalIntegrable (fun y => 2 * g l y) volume 0 1 := hint.const_mul 2
    refine this.mono_fun (by fun_prop) ?_
    refine ae_restrict_of_forall_mem measurableSet_uIoc (fun y hy => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hy
    have hy0 := hy.1
    show ‖y⁻¹‖ ≤ ‖2 * g l y‖
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hy0.le),
      Real.norm_of_nonneg (mul_nonneg zero_le_two (g_nonneg l hy0.le))]
    unfold g
    have he : Real.exp (l / y) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg hl hy0.le)
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    rw [inv_mul_eq_div, div_le_iff₀ hy0]
    nlinarith [Real.exp_pos (l / y)]
  rw [intervalIntegrable_inv_iff] at h2
  rcases h2 with h | h
  · norm_num at h
  · exact h (by simp)

theorem small (l : ℝ) (hl : 0 < l) (hl1 : l < 1) :
    (- Real.log l) / (1 + Real.exp 1) ≤ massIntegral l := by
  rw [mass_eq, ← intervalIntegral.integral_add_adjacent_intervals
    (g_int' l hl le_rfl hl1.le hl.le) (g_int' l hl hl.le le_rfl hl1.le)]
  have h0 : 0 ≤ ∫ y in (0:ℝ)..l, g l y :=
    intervalIntegral.integral_nonneg hl.le (fun y hy => g_nonneg l hy.1)
  have hc : (0:ℝ) < 1 + Real.exp 1 := by positivity
  have hinv : IntervalIntegrable (fun y : ℝ => (1 + Real.exp 1)⁻¹ * y⁻¹) volume l 1 := by
    apply IntervalIntegrable.const_mul
    rw [intervalIntegrable_inv_iff]
    right
    rw [Set.uIcc_of_le hl1.le]
    intro h; exact absurd h.1 (not_le.mpr hl)
  have hmono : ∫ y in l..1, (1 + Real.exp 1)⁻¹ * y⁻¹ ≤ ∫ y in l..1, g l y := by
    apply intervalIntegral.integral_mono_on hl1.le hinv (g_int' l hl hl.le le_rfl hl1.le)
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hl hy.1
    unfold g
    have : l / y ≤ 1 := (div_le_one hy0).mpr hy.1
    have he : Real.exp (l / y) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
    rw [← mul_inv, one_div]
    apply inv_anti₀ (by positivity)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) hy0.le
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hl one_pos, one_div,
    Real.log_inv] at hmono
  rw [div_eq_inv_mul]
  linarith

theorem big (l : ℝ) (hl : 0 < l) : massIntegral l ≤ 1 / l := by
  rw [mass_eq]
  calc ∫ y in (0:ℝ)..1, g l y ≤ ∫ y in (0:ℝ)..1, 1 / l :=
        intervalIntegral.integral_mono_on zero_le_one (g_int l hl) intervalIntegrable_const
          (fun y hy => g_le l hl hy.1)
    _ = 1 / l := by simp

end E297P2

open E297P2 in
theorem checked_leaf : OMA.R_Erdos297_erdos_297_variants_general_R1.H1 := by
  unfold OMA.R_Erdos297_erdos_297_variants_general_R1.H1
  intro x hx
  have hxR : (0:ℝ) < x := by exact_mod_cast hx
  set ls := Real.exp (-((x:ℝ) + 1) * (1 + Real.exp 1)) with hls
  have hc : (0:ℝ) < 1 + Real.exp 1 := by positivity
  have ls0 : 0 < ls := Real.exp_pos _
  have ls1 : ls < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hFs : (x:ℝ) + 1 ≤ massIntegral ls := by
    have := small ls ls0 ls1
    have hlog : -Real.log ls = ((x:ℝ) + 1) * (1 + Real.exp 1) := by rw [hls, Real.log_exp]; ring
    rw [hlog, mul_div_assoc, div_self hc.ne', mul_one] at this
    exact this
  set lb := 2 / (x:ℝ) with hlb
  have lb0 : 0 < lb := by positivity
  have hFb : massIntegral lb ≤ (x:ℝ) / 2 := by
    have := big lb lb0
    rw [hlb, one_div_div] at this
    exact this
  have hlt : ls < lb := by
    by_contra h
    replace h := not_lt.mp h
    rcases h.eq_or_lt with h | h
    · rw [h] at hFb; linarith
    · have := strict_anti lb0 ls0 h
      linarith
  have hivt := intermediate_value_Icc' hlt.le (cont.mono (fun y hy => lt_of_lt_of_le ls0 hy.1))
  obtain ⟨l, hl, hFl⟩ := hivt
    (show (x:ℝ) ∈ Set.Icc (massIntegral lb) (massIntegral ls) from ⟨by linarith, by linarith⟩)
  have hl0 : 0 < l := lt_of_lt_of_le ls0 hl.1
  refine ⟨l, hFl, fun l' hl' => ?_⟩
  have hl'' : massIntegral l' = x := hl'
  have hl'0 : 0 < l' := by
    by_contra h
    replace h := not_lt.mp h
    rw [nonpos l' h] at hl''
    linarith
  exact strict_anti.injOn hl'0 hl0 (hl''.trans hFl.symm)



end Calibration

namespace PartitionLimit



/-! The right endpoint Riemann sum is squeezed between the integral and the
integral plus one mesh width times the total variation. Calibration identifies
the entropy using the binary entropy identity for the logistic function. -/

open Filter Real MeasureTheory Erdos297
open scoped Topology

namespace E297

private noncomputable def w (l y : ℝ) := 1/(y*(1+exp (l/y)))

private lemma lambda_eq {x l : ℝ} (hx : 0 < x) (hl : massIntegral l = x) :
    lambdaOf x = l := by
  have uniq {u v : ℝ} (hu : massIntegral u = x) (hv : massIntegral v = x) (hlt : u < v) : False := by
    have iu : IntervalIntegrable (w u) volume 0 1 := intervalIntegral.intervalIntegrable_of_integral_ne_zero
      (show massIntegral u ≠ 0 by simpa [hu] using hx.ne')
    have iv : IntervalIntegrable (w v) volume 0 1 := intervalIntegral.intervalIntegrable_of_integral_ne_zero
      (show massIntegral v ≠ 0 by simpa [hv] using hx.ne')
    have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on (iu.sub iv) (by
      intro y hy
      have hy0 := hy.1
      apply sub_pos.mpr
      exact one_div_lt_one_div_of_lt (by positivity)
        (mul_lt_mul_of_pos_left (add_lt_add_right (exp_lt_exp.mpr (div_lt_div_of_pos_right hlt hy.1)) 1) hy.1))
      zero_lt_one
    rw [intervalIntegral.integral_sub iu iv] at hpos
    change 0 < massIntegral u - massIntegral v at hpos
    linarith
  have hs : {u : ℝ | massIntegral u = x} = {l} := by
    ext u
    change massIntegral u = x ↔ u = l
    constructor
    · intro hu
      exact le_antisymm (le_of_not_gt (uniq hl hu)) (le_of_not_gt (uniq hu hl))
    · rintro rfl
      exact hl
  rw [lambdaOf, hs, csInf_singleton]

private lemma calibration_pos {x l : ℝ} (hx : 0 < x) (hl : massIntegral l = x) : 0 < l := by
  have iw : IntervalIntegrable (w l) volume 0 1 := intervalIntegral.intervalIntegrable_of_integral_ne_zero
    (show massIntegral l ≠ 0 by simpa [hl] using hx.ne')
  by_contra! h
  have hi : IntervalIntegrable (fun y : ℝ => y⁻¹) volume 0 1 := by
    apply (iw.const_mul 2).mono_fun' (by fun_prop)
    rw [Set.uIoc_of_le zero_le_one]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy0 := hy.1
    have he : exp (l/y) ≤ 1 := exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg h hy0.le)
    change ‖y⁻¹‖ ≤ 2*(1/(y*(1+exp (l/y))))
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy0)]
    field_simp
    linarith
  simpa [intervalIntegrable_inv_iff] using hi

private noncomputable def F (l y : ℝ) := if 0 < y then log (1+exp (-l/y)) else 0

private lemma F_mono {l : ℝ} (hl : 0 < l) : Monotone (F l) := by
  intro u v huv
  by_cases hu : 0 < u
  · have hv := hu.trans_le huv
    simp only [F, if_pos hu, if_pos hv]
    apply log_le_log (by positivity)
    apply add_le_add_right
    apply exp_le_exp.mpr
    rw [neg_div, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_left hl.le hu huv)
  · simp only [F, if_neg hu]
    split_ifs
    · apply log_nonneg
      linarith [exp_pos (-l/v)]
    · rfl

private lemma riemann (g : ℝ → ℝ) (hg : Monotone g) :
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, g ((i+1 : ℕ)/(n : ℝ))) / n)
      atTop (𝓝 (∫ y in (0:ℝ)..1, g y)) := by
  let J := ∫ y in (0:ℝ)..1, g y
  have squeeze (n : ℕ) (hn : 0 < n) : J ≤ (∑ i ∈ Finset.range n, g ((i+1 : ℕ)/(n : ℝ))) / n ∧
      (∑ i ∈ Finset.range n, g ((i+1 : ℕ)/(n : ℝ))) / n ≤ J + (g 1-g 0)/n := by
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    let h (t : ℝ) := g (t/n)
    have mono : Monotone h := fun _ _ hxy => hg (div_le_div_of_nonneg_right hxy hn'.le)
    have lo := MonotoneOn.sum_le_integral (x₀ := (0:ℝ)) (a := n) (f := h) (mono.monotoneOn _)
    have hi := MonotoneOn.integral_le_sum (x₀ := (0:ℝ)) (a := n) (f := h) (mono.monotoneOn _)
    simp only [zero_add] at lo hi
    have I : (∫ y in (0:ℝ)..n, h y) = n*J := by
      simp [h, J, intervalIntegral.integral_comp_div g hn'.ne', hn'.ne']
    rw [I] at lo hi
    have e := Eq.trans (Finset.sum_range_succ' (fun i : ℕ => h i) n).symm (Finset.sum_range_succ (fun i : ℕ => h i) n)
    simp only [Nat.cast_zero] at e
    have h₀ : h 0 = g 0 := by simp [h]
    have h₁ : h n = g 1 := by simp [h,hn'.ne']
    rw [h₀,h₁] at e
    refine ⟨(le_div_iff₀ hn').mpr (by simpa [h,mul_comm] using hi), ?_⟩
    apply (div_le_iff₀ hn').mpr
    rw [add_mul, div_mul_cancel₀ _ hn'.ne']
    change (∑ i ∈ Finset.range n, h (i+1 : ℕ)) ≤ _
    linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => J)
    (h := fun n : ℕ => J + (g 1-g 0)/n) tendsto_const_nhds
  · simpa [div_eq_mul_inv] using tendsto_const_nhds.add ((tendsto_one_div_atTop_nhds_zero_nat).const_mul (g 1-g 0))
  · filter_upwards [eventually_gt_atTop 0] with n hn using (squeeze n hn).1
  · filter_upwards [eventually_gt_atTop 0] with n hn using (squeeze n hn).2


private lemma logistic_entropy (a : ℝ) :
    binEntropy (1/(1+exp a)) = a/(1+exp a) + log (1+exp (-a)) := by
  have he := exp_pos a
  have he' := exp_pos (-a)
  have hlog : log (1+exp a) = a + log (1+exp (-a)) := by
    calc
      _ = log (exp a*(1+exp (-a))) := by
        congr 1
        rw [exp_neg]
        field_simp
        <;> ring
      _ = _ := by rw [log_mul he.ne' (by positivity), log_exp]
  have hc : 1-1/(1+exp a) = 1/(1+exp (-a)) := by
    rw [exp_neg]
    field_simp
    ring
  rw [binEntropy, hc]
  simp only [one_div, inv_inv, hlog]
  rw [← one_div, ← one_div, ← hc]
  ring

end E297

open E297 in
theorem checked_leaf : OMA.R_Erdos297_erdos_297_variants_general_R1.H2 := by
  classical
  intro x l hx hm
  have hx' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hl := calibration_pos hx' hm
  have hmono := F_mono hl
  have iw : IntervalIntegrable (w l) volume 0 1 :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero
      (show massIntegral l ≠ 0 by simpa [hm] using hx'.ne')
  have ig : IntervalIntegrable (F l) volume 0 1 := hmono.intervalIntegrable
  have ident : exponentOf x * log 2 = l*x + ∫ y in (0:ℝ)..1, F l y := by
    rw [exponentOf, lambda_eq hx' hm, intervalIntegral.integral_div,
      div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne']
    rw [← hm]
    change _ = l * (∫ y in (0:ℝ)..1, w l y) + _
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (iw.const_mul l) ig]
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le zero_le_one]
    filter_upwards with y hy
    have hy0 : 0 < y := hy.1
    rw [logistic_entropy, F, if_pos hy0, neg_div]
    dsimp [w]
    rw [mul_comm y, one_div, mul_inv_rev]
    ring
  rw [ident]
  apply (Tendsto.const_add ((l:ℝ)*x) (riemann (F l) hmono)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  congr 2
  rw [Real.log_prod (fun (p : ℕ) _ => (by positivity : (0 : ℝ) < 1 + exp (-l * N / (p : ℝ))).ne')]
  rw [show Finset.Icc 1 N = Finset.Ico 1 (N+1) by ext i; simp, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i hi
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hir : (0:ℝ) < (i:ℝ)+1 := by positivity
  simp only [Nat.cast_succ, Nat.cast_add, Nat.cast_one, F, if_pos (div_pos hir hNr)]
  congr 3
  rw [div_div_eq_mul_div]
  ring

open E297 in
theorem unit_entropy_value (l : ℝ) (hm : massIntegral l = 1) :
    exponentOf 1 = erdos_297.answer := by
  have hl := calibration_pos zero_lt_one hm
  have iw : IntervalIntegrable (w l) volume 0 1 :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero (show massIntegral l ≠ 0 by rw [hm]; norm_num)
  have ig : IntervalIntegrable (F l) volume 0 1 := (F_mono hl).intervalIntegrable
  have hF : (∫ y in (0:ℝ)..1, F l y) = ∫ y in (0:ℝ)..1, log (1 + exp (-l/y)) := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le zero_le_one]
    filter_upwards with y hy
    simp [F,hy.1]
  rw [erdos_297.answer,lambda_eq zero_lt_one hm,← hF]
  apply (eq_div_iff (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne').2
  rw [exponentOf,lambda_eq zero_lt_one hm,intervalIntegral.integral_div,
    div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne']
  calc
    _ = l * (∫ y in (0:ℝ)..1, w l y) + ∫ y in (0:ℝ)..1, F l y := by
      rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_add (iw.const_mul l) ig]
      apply intervalIntegral.integral_congr_ae
      rw [Set.uIoc_of_le zero_le_one]
      filter_upwards with y hy
      rw [logistic_entropy,F,if_pos hy.1,neg_div]
      dsimp [w]
      rw [mul_comm y,one_div,mul_inv_rev]
      ring
    _ = _ := by
      change l * massIntegral l + _ = _
      rw [hm,mul_one]

end PartitionLimit

namespace BoundedCount


/-! A thinned product measure concentrates in a strictly smaller reciprocal-sum window. Its cost is bounded exponentially in the thinning parameter. The nonintegrability argument is adapted from @marcusbuffett, Erdős 297 R1.H1. -/
open Filter Real Finset Erdos297 MeasureTheory intervalIntegral
open scoped Topology

namespace E297P2

noncomputable def g (l y : ℝ) : ℝ := 1 / (y * (1 + Real.exp (l / y)))

theorem mass_eq (l : ℝ) : massIntegral l = ∫ y in (0:ℝ)..1, g l y := rfl

theorem g_nonneg (l : ℝ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ g l y :=
  div_nonneg zero_le_one (mul_nonneg hy (by positivity))

theorem nonpos (l : ℝ) (hl : l ≤ 0) : massIntegral l = 0 := by
  rw [mass_eq]
  apply intervalIntegral.integral_undef
  intro hint
  have h2 : IntervalIntegrable (fun y : ℝ => y⁻¹) volume 0 1 := by
    have : IntervalIntegrable (fun y => 2 * g l y) volume 0 1 := hint.const_mul 2
    refine this.mono_fun (by fun_prop) ?_
    refine ae_restrict_of_forall_mem measurableSet_uIoc (fun y hy => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hy
    have hy0 := hy.1
    show ‖y⁻¹‖ ≤ ‖2 * g l y‖
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hy0.le),
      Real.norm_of_nonneg (mul_nonneg zero_le_two (g_nonneg l hy0.le))]
    unfold g
    have he : Real.exp (l / y) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg hl hy0.le)
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    rw [inv_mul_eq_div, div_le_iff₀ hy0]
    nlinarith [Real.exp_pos (l / y)]
  rw [intervalIntegrable_inv_iff] at h2
  rcases h2 with h | h
  · norm_num at h
  · exact h (by simp)

end E297P2
open Finset Real Filter MeasureTheory intervalIntegral Erdos297
open scoped Topology
namespace Thick297
noncomputable section

lemma endpoints (f : ℝ → ℝ) (hc : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => (∑ n∈Icc 1 N, f (n/(N:ℝ)))/N) atTop
      (𝓝 (∫ y in (0:ℝ)..1,f y)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  obtain ⟨δ,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) (ε/2) (by positivity)
  filter_upwards [tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const hd,eventually_gt_atTop 0] with N hδ hN
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  let a (i : ℕ) : ℝ := i/(N:ℝ)
  have a0 : a 0=0 := by simp [a]
  have aN : a N=1 := by simp [a,hn.ne']
  have diff (i : ℕ) : a (i+1)-a i=1/N := by simp [a,add_div]
  have geo (i : ℕ) (hi : i<N) : 0≤a i ∧ a i ≤ a (i+1) ∧ a (i+1) ≤ 1 := by
    refine ⟨by dsimp [a]; positivity,by linarith [diff i,one_div_pos.mpr hn],?_⟩
    change (↑(i+1):ℝ)/N ≤ 1
    apply (div_le_one hn).mpr
    exact_mod_cast (show i+1≤N by omega)
  have intg (i : ℕ) (hi : i<N) : IntervalIntegrable f volume (a i) (a (i+1)) :=
    ContinuousOn.intervalIntegrable_of_Icc (geo i hi).2.1 (hc.mono (Set.Icc_subset_Icc (geo i hi).1 (geo i hi).2.2))
  have err (i : ℕ) (hi : i<N) :
      |f (a (i+1))/N - ∫ y in a i..a (i+1), f y| ≤ (ε/2)/N := by
    obtain ⟨lo,inc,up⟩ := geo i hi
    have bound := intervalIntegral.norm_integral_le_of_norm_le_const (a := a i) (b := a (i+1))
      (f := fun y => f (a (i+1))-f y) (C := ε/2) (fun y hy => by
        rw [Set.uIoc_of_le inc] at hy
        have hdxy : dist (a (i+1)) y < δ := by
          rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hy.2)]
          linarith [diff i,hy.1]
        exact (hclose _ ⟨lo.trans inc,up⟩ _ ⟨lo.trans hy.1.le,hy.2.trans up⟩ hdxy).le)
    rw [intervalIntegral.integral_sub intervalIntegrable_const (intg i hi),intervalIntegral.integral_const,smul_eq_mul,
      diff,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hn)] at bound
    simpa [div_eq_mul_inv,mul_comm] using bound
  have eq := sum_integral_adjacent_intervals intg
  rw [a0,aN] at eq
  rw [Real.dist_eq,←eq,show Icc 1 N = Ico 1 (N+1) by ext; simp, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,Nat.add_comm 1]
  change |(∑ i ∈ range N, f (a (i+1)))/N - _| < ε
  rw [Finset.sum_div,←sum_sub_distrib]
  apply lt_of_le_of_lt ((abs_sum_le_sum_abs ..).trans (sum_le_sum fun i h => err i (mem_range.mp h)))
  simp [hn.ne',div_eq_mul_inv,mul_left_comm,mul_comm,mul_assoc]
  linarith

def profile (l y : ℝ) : ℝ := 1/(y*(1+exp (l/y)))

lemma exp_quadratic (z : ℝ) (hz : 0≤z) : z^2 ≤ 2*exp z := by
  have h := Real.pow_div_factorial_le_exp z hz 2
  norm_num at h
  linarith

lemma profile_le {l y : ℝ} (hl : 0<l) (hy : 0≤y) : profile l y ≤ 2*y/l^2 := by
  rcases hy.eq_or_lt with h|h
  · subst y; simp [profile]
  · rw [profile,div_le_div_iff₀ (by positivity) (by positivity)]
    have hh := exp_quadratic (l/y) (by positivity)
    rw [div_pow,div_le_iff₀ (by positivity)] at hh
    nlinarith [sq_nonneg y]

lemma profile_cont (l : ℝ) (hl : 0<l) : ContinuousOn (profile l) (Set.Icc 0 1) := by
  intro y hy
  rcases hy.1.eq_or_lt with h|h
  · subst y
    rw [ContinuousWithinAt,show profile l 0=0 by simp [profile]]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ => 0) (h := fun y : ℝ => 2*y/l^2) tendsto_const_nhds
    · have hh : Continuous (fun y : ℝ => 2*y/l^2) := by fun_prop
      simpa using (hh.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Icc 0 1))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact div_nonneg zero_le_one (mul_nonneg hy.1 (by positivity))
    · filter_upwards [self_mem_nhdsWithin] with y hy using profile_le hl hy.1
  · apply ContinuousAt.continuousWithinAt
    unfold profile
    fun_prop (disch := first | positivity | exact h.ne')

lemma mean_limit (l : ℝ) (hl : 0<l) :
    Tendsto (fun N : ℕ => ∑ n∈Icc 1 N,(1/(n:ℝ))*(exp (-l*N/n)/(1+exp (-l*N/n))))
      atTop (𝓝 (massIntegral l)) := by
  refine (endpoints (profile l) (profile_cont l hl)).congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro n hn
  have hp : (0:ℝ)<n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  unfold profile
  rw [show l/(n/(N:ℝ))=l*N/n by field_simp,show -l*N/n= -(l*N/n) by ring,exp_neg]
  field_simp <;> ring

end
end Thick297
open Finset Real Filter MeasureTheory intervalIntegral
open scoped Topology

namespace Thick297
noncomputable section

def part (P : Finset ℕ) (v : ℕ → ℝ) := ∏ n∈P, (1+v n)
def mean (P : Finset ℕ) (v b : ℕ → ℝ) := ∑ n∈P, b n*(v n/(1+v n))
def variance (P : Finset ℕ) (v b : ℕ → ℝ) := ∑ n∈P, (b n)^2*(v n/(1+v n)^2)
def wt (v : ℕ → ℝ) (A : Finset ℕ) := ∏ n∈A,v n
def mass (b : ℕ → ℝ) (A : Finset ℕ) := ∑ n∈A,b n

lemma second (P : Finset ℕ) (v b : ℕ → ℝ) (hv : ∀ n,0≤v n) (z : ℝ) :
    (∑ A∈P.powerset, wt v A * (mass b A-z)^2) =
      part P v * ((mean P v b-z)^2 + variance P v b) := by
  classical
  induction P using Finset.induction_on generalizing z with
  | empty => simp [wt,mass,part,mean,variance]
  | @insert n P hn ih =>
    rw [sum_powerset_insert hn,ih z]
    have eq : (∑ A∈P.powerset, wt v (insert n A)*(mass b (insert n A)-z)^2)
        = v n*∑ A∈P.powerset, wt v A*(mass b A-(z-b n))^2 := by
      rw [mul_sum]; apply sum_congr rfl
      intro A h
      have h' : n∉A := fun hm => hn ((mem_powerset.mp h) hm)
      simp only [wt,mass,prod_insert h',sum_insert h']
      ring
    rw [eq,ih (z-b n)]
    simp only [part,mean,variance,prod_insert hn,sum_insert hn]
    have hn' : 1+v n ≠ 0 := by linarith [hv n]
    field_simp
    <;> ring

lemma central (P : Finset ℕ) (v b : ℕ → ℝ) (hv : ∀ n, 0≤v n) (d : ℝ) (hd : 0<d)
    (small : variance P v b ≤ d^2/2) :
    part P v/2 ≤ ∑ A∈P.powerset.filter (fun A => |mass b A-mean P v b|≤d), wt v A := by
  classical
  let μ := mean P v b
  let good (A : Finset ℕ) := |mass b A-μ|≤d
  have zz : 0≤part P v := prod_nonneg fun n _ => by linarith [hv n]
  have ww (A : Finset ℕ) : 0 ≤ wt v A := prod_nonneg fun n _ => hv n
  have all : (∑ A∈P.powerset,wt v A) = part P v := (prod_one_add (f := v) P).symm
  have est := calc
    (∑ A∈P.powerset.filter (fun A => ¬good A), wt v A)*d^2
        = ∑ A∈P.powerset.filter (fun A => ¬good A), wt v A*d^2 := sum_mul ..
    _ ≤ ∑ A∈P.powerset.filter (fun A => ¬good A), wt v A*(mass b A-μ)^2 := by
      apply sum_le_sum
      intro A hA
      have h : d < |mass b A-μ| := lt_of_not_ge (mem_filter.mp hA).2
      exact mul_le_mul_of_nonneg_left (by simpa only [sq_abs] using (sq_le_sq₀ hd.le (abs_nonneg _) |>.mpr h.le)) (ww A)
    _ ≤ ∑ A∈P.powerset, wt v A*(mass b A-μ)^2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun A _ _ => mul_nonneg (ww A) (sq_nonneg _))
    _ = part P v*variance P v b := by rw [second P v b hv]; simp [μ]
    _ ≤ part P v*(d^2/2) := mul_le_mul_of_nonneg_left small zz
  have hsum := sum_filter_add_sum_filter_not P.powerset good (wt v)
  rw [all] at hsum
  change part P v/2 ≤ ∑ A∈P.powerset.filter good,wt v A
  have hbad : (∑ A∈P.powerset.filter (fun A => ¬good A),wt v A) ≤ part P v/2 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp
    nlinarith only [est]
  linarith
end
end Thick297
namespace Thick297
open Real Finset Filter Erdos297
open scoped Topology
noncomputable section

def odds (l : ℝ) (N n : ℕ) := exp (-l*N/n)
def thin (a w : ℝ) := a*w/(1+(1-a)*w)
lemma thin_id {a w : ℝ} (ha : 0≤a) (ha' : a≤1) (hw : 0≤w) :
    1+thin a w = (1+w)/(1+(1-a)*w) ∧
    thin a w/(1+thin a w) = a*(w/(1+w)) := by
  have h : 0 < 1+(1-a)*w := by nlinarith [mul_nonneg (sub_nonneg.mpr ha') hw]
  have id : 1+thin a w = (1+w)/(1+(1-a)*w) := by
    apply (eq_div_iff h.ne').mpr
    rw [add_mul,thin,div_mul_cancel₀ _ h.ne',one_mul]
    ring
  refine ⟨id,?_⟩
  rw [id,thin,div_div_div_cancel_right₀ h.ne',mul_div_assoc]

lemma thin_range {a w : ℝ} (ha : 0≤a) (ha' : a≤1) (hw : 0≤w) : 0≤thin a w ∧ thin a w≤w := by
  have z := mul_nonneg (sub_nonneg.mpr ha') hw
  have q : 0 < 1+(1-a)*w := by linarith
  refine ⟨div_nonneg (mul_nonneg ha hw) q.le,(div_le_iff₀ q).mpr ?_⟩
  nlinarith [mul_nonneg hw z]

lemma window_cost (l a : ℝ) (hl : 0<l) (ha : 0<a) (ha' : a<1) (N : ℕ) :
    exp (-(1-a)*N) * part (Icc 1 N) (odds l N) ≤
      part (Icc 1 N) (fun n => thin a (odds l N n)) := by
  have card : (Icc 1 N).card=N := by simp
  have rewrite_exp : exp (-(1-a)*N) = ∏ _n∈Icc 1 N, exp (-(1-a)) := by
    rw [prod_const,card,←Real.exp_nat_mul]; congr 1; ring
  rw [rewrite_exp,part,part,←prod_mul_distrib]
  apply prod_le_prod (fun n _ => by dsimp [odds]; positivity)
  intro n hn
  let w := odds l N n
  have hw : 0<w := exp_pos _
  have hw' : w≤1 := exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  rw [(thin_id ha.le ha'.le hw.le).1,exp_neg]
  have hh : 1+(1-a)*w ≤ exp (1-a) := by
    linarith [mul_le_mul_of_nonneg_left hw' (sub_nonneg.mpr ha'.le),Real.add_one_le_exp (1-a)]
  change (exp (1-a))⁻¹*(1+w) ≤ (1+w)/(1+(1-a)*w)
  rw [mul_comm,←div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (by linarith) (by positivity) hh

lemma thin_var (l a : ℝ) (hl : 0<l) (ha : 0≤a) (ha' : a≤1) (N : ℕ) (hN : 0<N) :
    variance (Icc 1 N) (fun n => thin a (odds l N n)) (fun n => 1/(n:ℝ)) ≤ (2/l^2)/N := by
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  calc
    _ ≤ ∑ _n∈Icc 1 N, 2/(l^2*(N:ℝ)^2) := by
      apply sum_le_sum
      intro n hn
      have hn' : (0:ℝ)<n := by exact_mod_cast (mem_Icc.mp hn).1
      let w := odds l N n
      let v := thin a w
      have hw : 0<w := exp_pos _
      obtain ⟨hv,hvw⟩ := thin_range ha ha' hw.le
      have hd : 1 ≤ (1+v)^2 := by change 1 ≤ (1+thin a w)^2; nlinarith [sq_nonneg (thin a w)]
      have bb : v/(1+v)^2 ≤ w := (div_le_self hv hd).trans hvw
      refine (mul_le_mul_of_nonneg_left bb (sq_nonneg _)).trans ?_
      change (1/(n:ℝ))^2*exp (-l*N/n) ≤ _
      rw [show -l*N/n= -(l*N/n) by ring,exp_neg]
      have z := exp_quadratic (l*N/n) (by positivity)
      rw [div_pow,div_le_iff₀ (by positivity)] at z
      field_simp
      nlinarith only [z]
    _ = _ := by simp; field_simp

lemma main (x : ℚ) (l : ℝ) (hx : 0<x) (hm : massIntegral l=x) (hl : 0<l) (ε : ℝ) (he : 0<ε) :
    ∃ d : ℚ, 0<d ∧ ∀ᶠ N : ℕ in atTop, exp (-ε*N) * (∏ n∈Icc 1 N, (1+exp (-l*N/n))) ≤
      (((Icc 1 N).powerset.filter (fun A : Finset ℕ => (∑ n∈A,(1:ℚ)/n) ≤ x-d)).card:ℝ) * exp (-l*N*(x:ℝ)) := by
  classical
  have x0 : (0:ℝ)<x := by exact_mod_cast hx
  let c : ℝ := 2/(x:ℝ)+3*l
  have cp : 0<c := by dsimp [c]; positivity
  obtain ⟨d,d0,hd⟩ := exists_rat_btwn (show (0:ℝ) < min ((x:ℝ)/4) (ε/(2*c)) from lt_min (by positivity) (by positivity))
  have hd₁ := lt_of_lt_of_le hd (min_le_left ..)
  have hd₂ := lt_of_lt_of_le hd (min_le_right ..)
  have cheap : (d:ℝ)*c < ε/2 := by rw [lt_div_iff₀ (by positivity)] at hd₂; linarith
  let a : ℝ := 1-2*(d:ℝ)/x
  have ax : a*(x:ℝ)=(x:ℝ)-2*d := by dsimp [a]; field_simp
  have ap : 0<a := by dsimp [a]; rw [sub_pos,div_lt_one x0]; linarith
  have au : a<1 := by dsimp [a]; linarith [div_pos (by positivity : 0<2*(d:ℝ)) x0]
  have loss : 1-a+3*l*d<ε/2 := by dsimp [c] at cheap; dsimp [a]; convert cheap using 1 <;> ring
  let b (n : ℕ) : ℝ := 1/n
  let v (N n : ℕ) := thin a (odds l N n)
  let P (N : ℕ) := Icc 1 N
  have mlim : Tendsto (fun N => mean (P N) (v N) b) atTop (𝓝 (a*(x:ℝ))) := by
    rw [←hm]
    apply ((mean_limit l hl).const_mul a).congr'
    filter_upwards with N
    rw [mean,mul_sum]
    apply sum_congr rfl
    intro n _
    dsimp only [v,b,odds]
    rw [(thin_id ap.le au.le (exp_pos _).le).2]
    ring
  have vlim : Tendsto (fun N : ℕ => (2/l^2)/(N:ℝ)) atTop (𝓝 0) := by
    have u : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    let K : ℝ := 2/l^2
    change Tendsto (fun n : ℕ => K/(n:ℝ)) atTop (𝓝 0)
    simpa only [div_eq_mul_inv,one_mul,mul_zero] using (show Tendsto (fun n : ℕ => K*(1/(n:ℝ))) atTop (𝓝 (K*0)) from u.const_mul K)
  have decay : Tendsto (fun N : ℕ => exp (-(ε/2)*(N:ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith)
  refine ⟨d,by exact_mod_cast d0,?_⟩
  filter_upwards [Metric.tendsto_nhds.mp mlim ((d:ℝ)/2) (by positivity),
    vlim.eventually_lt_const (show 0<((d:ℝ)/2)^2/2 by positivity),
    decay.eventually_lt_const (show (0:ℝ)<1/2 by norm_num),eventually_gt_atTop (0:ℕ)] with N hμ hvar hdec hN
  let μ := mean (P N) (v N) b
  let good := (P N).powerset.filter (fun A => |mass b A-μ|≤(d:ℝ)/2)
  let sub := (P N).powerset.filter (fun A : Finset ℕ => (∑ n∈A,(1:ℚ)/n) ≤ x-d)
  have center := central (P N) (v N) b (fun n => (thin_range ap.le au.le (exp_pos _).le).1)
    ((d:ℝ)/2) (by positivity) ((thin_var l a hl ap.le au.le N hN).trans hvar.le)
  have band {A : Finset ℕ} (h : A∈good) : (x:ℝ)-3*d ≤ mass b A ∧ mass b A ≤ x-d := by
    obtain ⟨low,up⟩ := abs_le.mp (mem_filter.mp h).2
    rw [Real.dist_eq,ax,abs_lt] at hμ
    change -((d:ℝ)/2) ≤ mass b A-μ at low
    change mass b A-μ ≤ (d:ℝ)/2 at up
    change _ < μ-((x:ℝ)-2*d) ∧ μ-((x:ℝ)-2*d) < _ at hμ
    constructor <;> linarith
  have incl : good ⊆ sub := by
    intro A h
    refine mem_filter.mpr ⟨(mem_filter.mp h).1,?_⟩
    have hh := (band h).2
    dsimp [mass,b] at hh
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Rat.cast_sub] using hh
  have wbound {A : Finset ℕ} (h : A∈good) : wt (v N) A ≤ exp (-l*N*((x:ℝ)-3*d)) := by
    calc
      _ ≤ ∏ n∈A,odds l N n := prod_le_prod
        (fun n _ => (thin_range ap.le au.le (exp_pos _).le).1)
        (fun n _ => (thin_range ap.le au.le (exp_pos _).le).2)
      _ = exp (-l*N*mass b A) := by
        unfold odds
        rw [←Real.exp_sum,mass,mul_sum]
        congr 1; apply sum_congr rfl; intro n _; dsimp [b]; ring
      _ ≤ _ := exp_le_exp.mpr (mul_le_mul_of_nonpos_left (band h).1 (by nlinarith [Nat.cast_nonneg (α := ℝ) N]))
  have H : exp (-(1-a)*N)*part (P N) (odds l N)/2 ≤ (sub.card:ℝ)*exp (-l*N*((x:ℝ)-3*d)) := calc
    _ ≤ part (P N) (v N)/2 := by linarith [window_cost l a hl ap au N]
    _ ≤ ∑ A∈good,wt (v N) A := center
    _ ≤ ∑ _A∈good,exp (-l*N*((x:ℝ)-3*d)) := sum_le_sum fun _ h => wbound h
    _ ≤ _ := by simp only [sum_const,nsmul_eq_mul]; gcongr
  have hleft : exp (-ε*N) ≤ exp (-(1-a)*N)/2 * exp (-(3*l*d)*N) := by
    rw [div_mul_eq_mul_div,← Real.exp_add]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have e := mul_le_mul_of_nonneg_left hdec.le (exp_pos (-ε/2*N)).le
    rw [← Real.exp_add] at e
    have E : -ε/2*N + -(ε/2)*N = -ε*N := by ring
    rw [E] at e
    have q : -ε/2*N ≤ -(1-a)*N + -(3*l*d)*N := by
      nlinarith [mul_le_mul_of_nonneg_right loss.le (Nat.cast_nonneg (α := ℝ) N)]
    nlinarith [exp_le_exp.mpr q]
  have pair := mul_le_mul_of_nonneg_right H (exp_pos (-(3*l*d)*N)).le
  have fix : exp (-l*N*((x:ℝ)-3*d))*exp (-(3*l*d)*N) = exp (-l*N*x) := by rw [←exp_add]; congr 1; ring
  rw [mul_assoc (sub.card:ℝ),fix] at pair
  change exp (-ε*N)*part (P N) (odds l N) ≤ (sub.card:ℝ)*exp (-l*N*x)
  refine le_trans ?_ pair
  have hh := mul_le_mul_of_nonneg_right hleft (show 0≤part (P N) (odds l N) from prod_nonneg fun n _ => by dsimp [odds]; positivity)
  linarith
end
end Thick297
theorem checked_leaf : OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1.H1 := by
  intro x l hx hm
  have xl : (0:ℝ)<(x:ℝ) := by exact_mod_cast hx
  exact Thick297.main x l hx hm (lt_of_not_ge (fun h => (ne_of_gt xl) (hm.symm.trans (E297P2.nonpos l h))))


end BoundedCount

namespace IntegerSums



-- Step Erdos297.erdos_297.variants.general.R1.H3.R1.H2.R1.H2: hypothesis H2 of reduction Erdos297.erdos_297.variants.general.R1.H3.R1.H2.R1
-- Credit: @ivillar

/-! Every positive integer `j` is a sum of distinct unit fractions: take the last harmonic number
`H_K < j` (the harmonic series diverges), then expand the remainder `j - H_K < 1 / K` by the
greedy (Fibonacci–Sylvester) algorithm, whose denominators all exceed `K`; the greedy step lowers
the numerator, which drives a strong induction. -/

namespace O2E297
open Finset

lemma greedy : ∀ a : ℕ, ∀ b M : ℕ, 0 < a → 0 < b → 1 ≤ M → (a:ℚ) / b < 1 / M →
    ∃ S : Finset ℕ, (∀ n ∈ S, M < n) ∧ ∑ n ∈ S, (1:ℚ) / n = a / b := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b M ha hb hM hr
  have hbq : (0:ℚ) < b := by exact_mod_cast hb
  have hMq : (0:ℚ) < M := by exact_mod_cast hM
  have hab : a * M < b := by
    rw [div_lt_div_iff₀ hbq hMq, one_mul] at hr
    exact_mod_cast hr
  have hab' : a < b := lt_of_le_of_lt (Nat.le_mul_of_pos_right a hM) hab
  by_cases hdvd : a ∣ b
  · obtain ⟨n, rfl⟩ := hdvd
    refine ⟨{n}, fun x hx => ?_, ?_⟩
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact Nat.lt_of_mul_lt_mul_left hab
    · have hn : 0 < n := Nat.pos_of_mul_pos_left hb
      rw [Finset.sum_singleton]
      push_cast
      field_simp
  · set n := b / a + 1 with hn
    have hdiv := Nat.div_add_mod b a
    have hmodpos : 0 < b % a := Nat.pos_of_ne_zero (fun h => hdvd (Nat.dvd_of_mod_eq_zero h))
    have hmodlt : b % a < a := Nat.mod_lt b ha
    have han : a * n = b + (a - b % a) := by rw [hn, mul_add, mul_one]; omega
    have hMn : M < n := by
      have : a * M < a * n := by omega
      exact Nat.lt_of_mul_lt_mul_left this
    set a' := a - b % a with ha'
    have ha'pos : 0 < a' := by omega
    have ha'lt : a' < a := by omega
    have hnpos : 0 < n := by omega
    have hr' : (a':ℚ) / (b * n : ℕ) < 1 / n := by
      have hnq : (0:ℚ) < n := by exact_mod_cast hnpos
      rw [div_lt_div_iff₀ (by positivity) hnq, one_mul]
      have : a' * n < b * n := Nat.mul_lt_mul_of_pos_right (by omega) hnpos
      exact_mod_cast this
    obtain ⟨S, hS, hsum⟩ := ih a' ha'lt (b * n) n ha'pos (Nat.mul_pos hb hnpos) hnpos hr'
    have hnS : n ∉ S := fun h => lt_irrefl n (hS n h)
    refine ⟨insert n S, fun x hx => ?_, ?_⟩
    · rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hMn
      · exact lt_trans hMn (hS x hx)
    · rw [Finset.sum_insert hnS, hsum]
      have hnq : (0:ℚ) < n := by exact_mod_cast hnpos
      have hcast : (a':ℚ) = (a:ℚ) * n - b := by
        have : (a' : ℤ) = (a:ℤ) * n - b := by rw [ha']; push_cast [Nat.cast_sub hmodlt.le]; omega
        exact_mod_cast this
      rw [hcast]
      push_cast
      field_simp
      ring

theorem main_H2 : OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1.H2 := by
  intro j hj
  have hex : ∃ N : ℕ, (j:ℚ) ≤ harmonic N := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, Real.exp j ≤ N := exists_nat_ge _
    refine ⟨N, ?_⟩
    have h1 : (j:ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
      rw [Real.le_log_iff_exp_le (by positivity)]; push_cast; linarith
    have h2 := log_add_one_le_harmonic N
    exact_mod_cast h1.trans h2
  classical
  have hN0 : (j:ℚ) ≤ harmonic (Nat.find hex) := Nat.find_spec hex
  have hjq : (0:ℚ) < j := by exact_mod_cast hj
  have hN0pos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, harmonic_zero] at hN0; linarith
    · exact h
  obtain ⟨K, hK⟩ : ∃ K, Nat.find hex = K + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hKlt : harmonic K < j := by
    have := Nat.find_min hex (show K < Nat.find hex by omega)
    push Not at this
    exact this
  rw [hK, harmonic_succ] at hN0
  have hIcc : ∀ m : ℕ, ∑ n ∈ Icc 1 m, (1:ℚ) / n = harmonic m := by
    intro m; rw [harmonic_eq_sum_Icc]; simp [one_div]
  by_cases hreq : (j:ℚ) - harmonic K = (↑(K + 1))⁻¹
  · refine ⟨Icc 1 (K + 1), fun n hn => by rw [Finset.mem_Icc] at hn; omega, ?_⟩
    rw [hIcc, harmonic_succ]
    linarith
  · have hrlt : (j:ℚ) - harmonic K < (↑(K + 1))⁻¹ := lt_of_le_of_ne (by linarith) hreq
    have hK1 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with h | h
      · exfalso
        rw [h, harmonic_zero] at hrlt
        have : (1:ℚ) ≤ j := by exact_mod_cast hj
        norm_num at hrlt
        linarith
      · exact h
    set r : ℚ := (j:ℚ) - harmonic K with hr
    have hr0 : 0 < r := by linarith
    have hKq : (0:ℚ) < K := by exact_mod_cast hK1
    have hrK : r < 1 / K := by
      have : (↑(K + 1) : ℚ)⁻¹ ≤ 1 / K := by
        rw [one_div]; apply inv_anti₀ hKq; push_cast; linarith
      linarith
    have hnum : 0 < r.num := Rat.num_pos.mpr hr0
    have hrdef : (r.num.toNat : ℚ) / r.den = r := by
      have : ((r.num.toNat : ℤ) : ℚ) = (r.num : ℚ) := by rw [Int.toNat_of_nonneg hnum.le]
      push_cast at this
      rw [this]
      exact Rat.num_div_den r
    obtain ⟨S, hS, hsum⟩ := greedy r.num.toNat r.den K (by omega) r.den_pos hK1 (by rw [hrdef]; exact hrK)
    have hdisj : Disjoint (Icc 1 K) S := by
      rw [Finset.disjoint_left]
      intro x hx hxS
      rw [Finset.mem_Icc] at hx
      have := hS x hxS
      omega
    refine ⟨Icc 1 K ∪ S, fun n hn => ?_, ?_⟩
    · rw [Finset.mem_union, Finset.mem_Icc] at hn
      rcases hn with hn | hn
      · omega
      · have := hS n hn; omega
    · rw [Finset.sum_union hdisj, hIcc, hsum, hrdef, hr]
      ring

end O2E297

theorem checked_leaf : OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1.H2 := O2E297.main_H2


end IntegerSums

namespace ReservoirDensity


/-! Mertens estimates from @senamakel via @marcusbuffett’s merged Erdős 377 and 299 proofs. The square-divisor exceptional set and prime window are adapted from the latter. -/

section
open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith


theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr


theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

theorem log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
    Real.log ⌊x⌋₊ ≤ Real.log x ∧ Real.log x ≤ Real.log ⌊x⌋₊ + Real.log 2 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
  have hN : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  constructor
  · exact Real.log_le_log (by linarith) hle
  · rw [← Real.log_mul (by linarith) (by norm_num)]
    apply Real.log_le_log (by linarith)
    linarith

/-- **Mertens' first theorem.** For real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + log 2 + 1 + primePowerConst`. -/
theorem abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
  have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' first theorem**, existential form. -/
theorem mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
  ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

theorem sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

theorem recip_step (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
        Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [sum_succ_eq, sum_succ_eq]
  split_ifs with h
  · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast h.one_lt)
    field_simp
    ring
  · simp


/-- Elementary comparison of `log b - log a` with `(b - a) / b`, for `0 < a ≤ b ≤ a + 1`. -/
theorem abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
  have hb : 0 < b := by linarith
  have hq : 0 < b / a := div_pos hb ha
  have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hup := Real.log_le_sub_one_of_pos hq
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at hlo
  rw [hlog]
  have e1 : (b - a) / b = 1 - a / b := by field_simp
  have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
  have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
  have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
    have : b - a ≤ 1 := by linarith
    nlinarith
  rw [abs_le, e2, e1]
  constructor <;> nlinarith

/-- Partial sums used in the proof of Mertens' second theorem. -/
noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

theorem mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N with ha_def
  set b := Real.log ((N + 1 : ℕ) : ℝ) with hb_def
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
    linarith
  set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
  set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
  set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
  have hstep : F1 - F0 = (S1 - S0) / b := recip_step N
  have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
  have hdiff : mertensG (N + 1) - mertensG N =
      (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
    have e : mertensG (N + 1) - mertensG N =
        (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
      simp only [mertensG]
      ring
    rw [e, hstep]
    field_simp
    ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]
      gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring


end OMALib.Mertens
end

section
open Filter Finset Real Asymptotics
open scoped Topology BigOperators
open OMALib.Mertens
namespace Mass377
noncomputable abbrev S (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1:ℝ)/p
lemma Cpos : 0 ≤ mertens1Const := by
  exact (abs_nonneg _).trans (abs_sum_log_div_sub_log_le_nat 2)
lemma Gdiff (m n : ℕ) (hm : 2 ≤ m) (hn : m ≤ n) :
    |mertensG n - mertensG m| ≤ (mertens1Const+1)*(1/log m-1/log n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    calc |mertensG (n+1)-mertensG m| =
        |(mertensG (n+1)-mertensG n)+(mertensG n-mertensG m)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (mertensG_step n (hm.trans hn)) ih
      _ = _ := by ring
lemma logTop : Tendsto (fun n : ℕ => log n) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
lemma natMertens : ∃ b : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ Nat.primesLE n, (1:ℝ)/p) -
    log (log n)) atTop (𝓝 b) := by
  have hC : CauchySeq mertensG := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => (mertens1Const+1)/log n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop logTop
    obtain ⟨m,hm,he⟩ := ((eventually_ge_atTop 2).and (hlim.eventually_lt_const hε)).exists
    refine ⟨m,fun n hn => ?_⟩
    rw [Real.dist_eq]
    apply (Gdiff m n hm hn).trans_lt
    have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hp : 0≤(mertens1Const+1)*(1/log n) := mul_nonneg (by linarith [Cpos]) (by positivity [log_pos hn'])
    rw [mul_sub,←div_eq_mul_one_div]
    linarith
  obtain ⟨b,hb⟩ := cauchySeq_tendsto_of_complete hC
  let R (n : ℕ) := ((∑ p ∈ Nat.primesLE n, log p / p)-log n)/log n
  have hR : Tendsto R atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (show Tendsto (fun n : ℕ => mertens1Const/log n) atTop (𝓝 0) from tendsto_const_nhds.div_atTop logTop)
    filter_upwards [logTop.eventually_gt_atTop 0] with n hn
    dsimp only [R]
    rw [Real.norm_eq_abs, abs_div,abs_of_pos hn]
    exact div_le_div_of_nonneg_right (abs_sum_log_div_sub_log_le_nat n) hn.le
  refine ⟨b,?_⟩
  simpa [R,mertensG] using hb.add hR
lemma realMertens : ∃ b : ℝ, Tendsto (fun x : ℝ => S x-log (log x)) atTop (𝓝 b) := by
  obtain ⟨b,hb⟩ := natMertens
  have he := (isEquivalent_nat_floor (R:=ℝ)).log tendsto_id
  have hz := tendsto_log_atTop.eventually_ne_atTop 0
  have ht := ((isEquivalent_iff_tendsto_one hz).1 he).log (by norm_num)
  have hfloor : Tendsto (fun x : ℝ => log (⌊x⌋₊:ℝ)) atTop atTop := logTop.comp tendsto_nat_floor_atTop
  have hdiff : Tendsto (fun x : ℝ => log (log (⌊x⌋₊:ℝ)) - log (log x)) atTop (𝓝 0) := by
    rw [Real.log_one] at ht
    apply ht.congr'
    filter_upwards [hz,hfloor.eventually_ne_atTop 0] with x hx hf
    exact log_div hf hx
  refine ⟨b,?_⟩
  have h := (hb.comp tendsto_nat_floor_atTop).add hdiff
  simpa [S,Function.comp_def,sub_add_sub_cancel] using h
end Mass377
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299
noncomputable abbrev cutoff (N : ℕ) (c : ℝ) := (N:ℝ)^c
lemma cut_top {c : ℝ} (hc : 0<c) : Tendsto (fun N : ℕ => cutoff N c) atTop atTop :=
  (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
lemma prime_window (δ : ℝ) (hδ : 0<δ) : ∃ c : ℝ, 0<c ∧ c<1 ∧ ∀ᶠ N : ℕ in atTop,
    (∑ p ∈ Nat.primesLE N \ Nat.primesLE ⌊cutoff N c⌋₊, (1:ℝ)/p) ≤ δ := by
  let c := exp (-δ/2)
  have hc : 0<c := exp_pos _
  have hc1 : c < 1 := exp_lt_one_iff.mpr (by linarith)
  obtain ⟨b,hb⟩ := Mass377.realMertens
  have hN := hb.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hY := hb.comp (cut_top hc)
  have lim := (hN.sub hY).sub (tendsto_const_nhds (x := log c))
  have goal : Tendsto (fun N : ℕ => Mass377.S N - Mass377.S (cutoff N c)) atTop (𝓝 (-log c)) := by
    simp only [sub_self,zero_sub] at lim
    apply lim.congr'
    filter_upwards [eventually_ge_atTop 2] with N h
    have hr : (1:ℝ) < N := by exact_mod_cast (show 1<N by omega)
    dsimp only [Function.comp_apply,Function.comp_def, Pi.sub_apply, cutoff]
    rw [Real.log_rpow (by linarith),Real.log_mul hc.ne' (Real.log_pos hr).ne']
    ring
  have he : -log c < δ := by dsimp [c]; rw [log_exp]; linarith
  refine ⟨c,hc,hc1,?_⟩
  filter_upwards [goal.eventually_lt_const he,eventually_ge_atTop 1] with N h hN
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hy : cutoff N c ≤ N := by simpa using rpow_le_rpow_of_exponent_le hNr hc1.le
  have sub : Nat.primesLE ⌊cutoff N c⌋₊ ⊆ Nat.primesLE N := by
    intro p hp
    obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hle.trans (Nat.floor_le_of_le hy),hpr⟩
  have eq := sum_sdiff sub (f:=fun p : ℕ => (1:ℝ)/p)
  simp only [Mass377.S,Nat.floor_natCast] at h
  linarith

lemma mult_union (N : ℕ) (D : Finset ℕ) :
    (((D.biUnion fun d => (Ioc 0 N).filter (d ∣ ·)).card):ℝ) ≤
      N * ∑ d ∈ D, (1:ℝ)/d := by
  calc _ ≤ ((∑ d ∈ D, ((Ioc 0 N).filter (d ∣ ·)).card : ℕ):ℝ) := by exact_mod_cast card_biUnion_le
       _ = ∑ d ∈ D, ((N/d:ℕ):ℝ) := by simp [Nat.Ioc_filter_dvd_card_eq_div]
       _ ≤ ∑ d ∈ D, (N:ℝ)/d := sum_le_sum fun _ _ => Nat.cast_div_le
       _ = _ := by simp [mul_sum, div_eq_mul_inv]

lemma square_tail (δ : ℝ) (hδ : 0<δ) : ∃ A : ℕ, ∀ N : ℕ,
    (∑ a ∈ Icc A N, (1:ℝ)/(a:ℝ)^2) ≤ δ := by
  have hs : Summable (fun a : ℕ => (1:ℝ)/(a:ℝ)^2) := by
    simpa only [one_div] using (Real.summable_nat_pow_inv.mpr (by decide : 1<2))
  let s := ∑' a : ℕ, (1:ℝ)/(a:ℝ)^2
  obtain ⟨A,hA⟩ := (hs.hasSum.tendsto_sum_nat.eventually_const_lt (show s-δ < s by linarith)).exists
  refine ⟨A,fun N => ?_⟩
  have hd : Disjoint (range A) (Icc A N) := by
    rw [Finset.disjoint_left]; intro x hx hy
    exact (mem_range.mp hx).not_ge (mem_Icc.mp hy).1
  have h := hs.sum_le_tsum (range A ∪ Icc A N) (fun a _ => by positivity)
  rw [sum_union hd] at h
  change _ ≤ s at h
  linarith

lemma square_mult (N A : ℕ) :
    ((((Icc A N).biUnion fun a => (Ioc 0 N).filter (a^2 ∣ ·)).card):ℝ) ≤
      N * ∑ a ∈ Icc A N, (1:ℝ)/(a:ℝ)^2 := by
  calc _ ≤ ((∑ a ∈ Icc A N, ((Ioc 0 N).filter (a^2 ∣ ·)).card:ℕ):ℝ) := by exact_mod_cast card_biUnion_le
       _ = ∑ a ∈ Icc A N, ((N/a^2:ℕ):ℝ) := by simp [Nat.Ioc_filter_dvd_card_eq_div]
       _ ≤ ∑ a ∈ Icc A N, (N:ℝ)/(a^2:ℕ) := sum_le_sum fun _ _ => Nat.cast_div_le
       _ = _ := by simp [mul_sum, div_eq_mul_inv]
end Regular299
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299

lemma smooth (δ : ℝ) (hδ : 0<δ) : ∃ c : ℝ, 0<c ∧ c<1 ∧ ∀ᶠ N : ℕ in atTop, ∃ E : Finset ℕ,
    (E.card:ℝ) ≤ 2*δ*N ∧ ∀ n ∈ Ioc 0 N, n ∉ E → ∀ q : ℕ, IsPrimePow q → q ∣ n →
    (q:ℝ) ≤ cutoff N c := by
  classical
  obtain ⟨c,hc,hc1,hwin⟩ := prime_window δ hδ
  obtain ⟨A,hA⟩ := square_tail δ hδ
  refine ⟨c,hc,hc1,?_⟩
  filter_upwards [hwin,(cut_top hc).eventually_ge_atTop ((A:ℝ)^3),
    eventually_ge_atTop 1] with N hwin hcut hN
  let P := Nat.primesLE N \ Nat.primesLE ⌊cutoff N c⌋₊
  let U := P.biUnion fun p => (Ioc 0 N).filter (p ∣ ·)
  let V := (Icc A N).biUnion fun a => (Ioc 0 N).filter (a^2 ∣ ·)
  have hd1 := (mult_union N P).trans (mul_le_mul_of_nonneg_left hwin (Nat.cast_nonneg N))
  have hd2 := (square_mult N A).trans (mul_le_mul_of_nonneg_left (hA N) (Nat.cast_nonneg N))
  refine ⟨U ∪ V, ?_, fun n hn hex q hq hqn => ?_⟩
  · have h : ((U ∪ V).card:ℝ) ≤ U.card + V.card := by exact_mod_cast card_union_le U V
    change (U.card:ℝ) ≤ _ at hd1
    change (V.card:ℝ) ≤ _ at hd2
    linarith
  apply le_of_not_gt
  intro hgt
  have hqbig := hgt
  have hqN := (Nat.le_of_dvd (mem_Ioc.mp hn).1 hqn).trans (mem_Ioc.mp hn).2
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff q).mp hq
  by_cases hk1 : k=1
  · subst k
    simp only [pow_one] at *
    apply hex (mem_union_left _ (mem_biUnion.mpr ?_))
    refine ⟨p,mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hqN,hp⟩,?_⟩,mem_filter.mpr ⟨hn,hqn⟩⟩
    intro hh
    have hl := (Nat.mem_primesLE.mp hh).1
    exact hqbig.not_ge ((Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) c)).mp hl)
  · let a := p^(k/2)
    have ha2 : a^2 ∣ p^k := by
      dsimp [a]; rw [← pow_mul]; exact pow_dvd_pow p (by omega)
    have h3 : p^k ≤ a^3 := by
      dsimp [a]; rw [← pow_mul]; exact Nat.pow_le_pow_right hp.pos (by omega)
    have haA : A ≤ a := by
      by_contra! h
      have : a^3 ≤ A^3 := Nat.pow_le_pow_left h.le 3
      have hh : ((p^k:ℕ):ℝ) ≤ (A:ℝ)^3 := by exact_mod_cast h3.trans this
      linarith
    have haN : a ≤ N := (Nat.le_of_dvd (mem_Ioc.mp hn).1 ((dvd_pow_self a (by decide : 2≠0)).trans (ha2.trans hqn))).trans (mem_Ioc.mp hn).2
    exact hex (mem_union_right _ (mem_biUnion.mpr ⟨a,mem_Icc.mpr ⟨haA,haN⟩,
      mem_filter.mpr ⟨hn,ha2.trans hqn⟩⟩))


end Regular299
end

namespace OMA.DenominatorReserve
open Finset Real Filter
open scoped Classical Topology

def J (B : ℕ) := (Icc 1 B).lcm id

noncomputable def reserve (ε : ℝ) (K i : ℕ) := (Icc 1 (i*i)).filter fun n => IsPrimePow i ∧ i∣n ∧
  Nat.Coprime i (n/i) ∧ (i:ℝ)^ε ≤ (n/i:ℕ) ∧ ((n/i:ℕ):ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬ K ∣ n

lemma member_dvd {v B : ℕ} (hv : 0<v) (hB : v≤B) : v ∣ J B :=
  Finset.dvd_lcm (f:=id) (mem_Icc.mpr ⟨hv,hB⟩)

lemma Jpos (B : ℕ) : 0 < J B := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr
  fun p hp => (Nat.ne_of_gt (mem_Icc.mp hp).1 : p ≠ 0))

lemma smooth_dvd {n B : ℕ} (h : ∀ q : ℕ, IsPrimePow q → q ∣ n → q ≤ B) : n ∣ J B := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
  intro p k hp hd
  rcases k.eq_zero_or_pos with rfl|hk
  · simp
  · exact member_dvd (pow_pos hp.pos _) (h _ (hp.isPrimePow.pow hk.ne') hd)

lemma reserve_disjoint {ε : ℝ} (hε : ε < 1/2) {K i j : ℕ} (hi : 16 ≤ i) (hij : i < j) :
    Disjoint (reserve ε K i) (reserve ε K j) := by
  rw [Finset.disjoint_left]
  intro n hni hnj
  obtain ⟨hin,_,hd,hcop,_,hup,_⟩ := mem_filter.mp hni
  obtain ⟨_,hpj,hdj,_⟩ := mem_filter.mp hnj
  have hn := (mem_Icc.mp hin).1
  have hh := (hcop.isPrimePow_dvd_mul hpj).mp
    (show j ∣ i*(n/i) by rwa [Nat.mul_div_cancel' hd])
  have hir : (16:ℝ) ≤ i := by exact_mod_cast hi
  have sqrt4 : 4 ≤ √(i:ℝ) := by rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
  have hsqrt : (i:ℝ)^ε ≤ √(i:ℝ) := by
    rw [Real.sqrt_eq_rpow]; exact rpow_le_rpow_of_exponent_le (by linarith) hε.le
  have strict : (n/i:ℕ) < i := by
    have : ((n/i:ℕ):ℝ) < i := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg i),
        mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0:ℝ)≤2)]
    exact_mod_cast this
  rcases hh with h | h
  · exact hij.not_ge (Nat.le_of_dvd (by omega) h)
  · have p : 0<n/i := Nat.div_pos (Nat.le_of_dvd hn hd) (by omega)
    exact (show ¬ j ≤ n/i by omega) (Nat.le_of_dvd p h)

lemma small_scale {s η : ℝ} (hs : s<1) (hη : 0<η) :
    ∀ᶠ N : ℕ in atTop, 2*(N:ℝ)^s ≤ η*N := by
  have ht := ((tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_lt_const (show 0<η/2 by positivity)
  filter_upwards [ht,eventually_ge_atTop 1] with N h hN
  change (N:ℝ)^(-(1-s)) < η/2 at h
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have eq : (N:ℝ)^s = (N:ℝ)^(-(1-s))*N := by
    conv_rhs => rhs; rw [← Real.rpow_one (N:ℝ)]
    rw [← rpow_add hn]; congr 1; ring
  rw [eq]; nlinarith only [mul_le_mul_of_nonneg_right h.le hn.le]

lemma reserve_small {c ε : ℝ} (hε : 0<ε) {N i K : ℕ} (hN : 0<N) (hi : i≤⌊(N:ℝ)^c⌋₊)
    {n : ℕ} (hn : n ∈ reserve ε K i) : (n:ℝ) ≤ 2*(N:ℝ)^(c*(1+ε)) := by
  obtain ⟨_,_,hd,_,_,hup,_⟩ := mem_filter.mp hn
  have hcast : (n:ℝ) = (i:ℝ)*((n/i:ℕ):ℝ) := by exact_mod_cast (Nat.mul_div_cancel' hd).symm
  have hbound : (i:ℝ) ≤ (N:ℝ)^c := (Nat.le_floor_iff (rpow_nonneg (Nat.cast_nonneg _) _)).mp hi
  calc
    _ = _ := hcast
    _ ≤ (N:ℝ)^c*(2*((N:ℝ)^c)^ε) := mul_le_mul hbound
      (hup.trans (mul_le_mul_of_nonneg_left (rpow_le_rpow (Nat.cast_nonneg _) hbound hε.le) (by norm_num)))
      (by positivity) (by positivity)
    _ = _ := by
      rw [← rpow_mul (Nat.cast_nonneg N), mul_add,mul_one]
      rw [rpow_add (Nat.cast_pos.mpr hN)]; ring

end OMA.DenominatorReserve

open Filter Finset Real OMA.DenominatorReserve
open scoped Classical Topology

theorem checked_leaf : OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1_H1_R1.H1 := by
  classical
  intro x _ δ hδ
  let η := min (δ/8) (1/8)
  have hη : 0<η := lt_min (by positivity) (by norm_num)
  have hη1 : η≤1 := (min_le_right ..).trans (by norm_num)
  obtain ⟨c,hc,hc1,sm⟩ := Regular299.smooth η hη
  let ε := (1-c)/4
  have hε : 0<ε := by dsimp [ε]; linarith
  have hε2 : ε<1/2 := by dsimp [ε]; linarith
  have hs : c*(1+ε)<1 := by dsimp [ε]; nlinarith [sq_nonneg (1-c)]
  refine ⟨ε,hε,hε2,?_⟩
  intro L₀
  let L := max (max L₀ 16) ⌈1/η⌉₊
  have hL : 16 ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  have hL' : ⌈1/η⌉₊ ≤ L := le_max_right _ _
  have hKL : L ≤ J L := Nat.le_of_dvd (Jpos _) (member_dvd (by omega) le_rfl)
  have hK : 1/η ≤ (J L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hL'.trans hKL)
  have hK' : 1 / (J L : ℝ) ≤ η := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Jpos L))).mpr
    have := (div_le_iff₀ hη).mp hK
    linarith
  refine ⟨L,(le_max_left _ _).trans (le_max_left _ _),?_⟩
  have Btop := tendsto_nat_floor_atTop.comp (Regular299.cut_top hc)
  filter_upwards [sm, small_scale hs hη,Btop.eventually_ge_atTop (max L x.den),
    eventually_ge_atTop 1] with N ⟨E,ec,smooth⟩ sc bbig hN
  let B := ⌊(N:ℝ)^c⌋₊
  change max L x.den ≤ B at bbig
  let V := (Ioc 0 N).filter (J L ∣ ·)
  let W := Icc 1 ⌊η*N⌋₊
  let T := Icc 1 N
  let U := T \ (E ∪ V ∪ W)
  refine ⟨B,(le_max_left ..).trans bbig,U,sdiff_subset,?_,
    member_dvd x.den_pos ((le_max_right ..).trans bbig),?_,?_,?_⟩
  · have sub : T \ U ⊆ E ∪ V ∪ W := by
      intro n hn
      obtain ⟨ht,hu⟩ := mem_sdiff.mp hn
      exact of_not_not (fun h => hu (mem_sdiff.mpr ⟨ht,h⟩))
    have card : (T \ U).card ≤ E.card + V.card + W.card := (card_le_card sub).trans
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    have hV : (V.card : ℝ) ≤ η*N := by
      change (((Ioc 0 N).filter (J L ∣ ·)).card : ℝ) ≤ _
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      exact (Nat.cast_div_le).trans (by simpa [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_right hK' (Nat.cast_nonneg N))
    have hW : (W.card : ℝ) ≤ η*N := by simpa [W] using Nat.floor_le (mul_nonneg hη.le (Nat.cast_nonneg N))
    have h := mul_le_mul_of_nonneg_right (min_le_left (δ/8) (1/8:ℝ)) (Nat.cast_nonneg N)
    change η*N ≤ _ at h
    have cc : ((T \ U).card:ℝ) ≤ E.card + V.card + W.card := by exact_mod_cast card
    linarith
  · intro u hu
    obtain ⟨ht,hrest⟩ := mem_sdiff.mp hu
    have hu' := mem_Icc.mp ht
    have huN : u∈Ioc 0 N := mem_Ioc.mpr hu'
    have hE : u∉E := fun hm => hrest (mem_union_left _ (mem_union_left _ hm))
    exact ⟨smooth_dvd (fun q hp hd => Nat.le_floor (smooth u huN hE q hp hd)),
      fun hd => hrest (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨huN,hd⟩)))⟩
  · intro i hi
    have loc {n : ℕ} (hn : n∈reserve ε (J L) i) : n∈W := mem_Icc.mpr
      ⟨(mem_Icc.mp (mem_filter.mp hn).1).1,Nat.le_floor ((reserve_small hε hN (mem_Ioc.mp hi).2 hn).trans sc)⟩
    refine ⟨fun n hn => ?_,Finset.disjoint_left.mpr (fun n hu hn => (mem_sdiff.mp hu).2
      (mem_union_right _ (loc hn)))⟩
    obtain ⟨p,q⟩ := mem_Icc.mp (loc hn)
    exact mem_Icc.mpr ⟨p,q.trans (Nat.floor_le_of_le (by simpa using mul_le_mul_of_nonneg_right hη1 (Nat.cast_nonneg N)))⟩
  · intro i hi j _ hij
    exact reserve_disjoint hε2 (hL.trans (mem_Ioc.mp hi).1.le) hij


end ReservoirDensity

namespace ModularCorrection



/-!
The modular subset-sum theorem and the prime count in a fixed-ratio interval come
from Will Howe (@H0W4RD-dev), H0W4RD-dev/croot-unit-fractions at
c58a7d45114c3af27e6abb19dcfca9d82b49b4a1, used under Apache-2.0 and adapted
from the @marcusbuffett port in open-math-agents at 5f7f37a. The Fourier
argument is Croot's Lemma 1 (Acta Arithmetica 99, 2001).

Partition the prime interval at five thirds of its lower endpoint. One part
still contains enough primes after removing the prime dividing the modulus.
Multiplying its primes by a common integer coprime to the modulus, two and
three moves all denominators into the required window. Inversion multiplies
the subset sums by a unit, so they still cover every residue. The lcm grid
and tail budget then lift the modular identities to rational ones.
-/
namespace Croot

open Real Finset Filter

/-- For every `n` and every `ε > 0`, eventually `(log x) ^ n ≤ ε √x`. -/
lemma eventually_log_pow_le_mul_sqrt (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ n ≤ ε * √x := by
  have h := (isLittleO_log_rpow_rpow_atTop (n : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound hε
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have e1 : ‖Real.log x ^ (n : ℝ)‖ = Real.log x ^ n := by
    rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog n)]
  have e2 : ‖x ^ (1 / 2 : ℝ)‖ = √x := by
    rw [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hx' : ‖Real.log x ^ (n : ℝ)‖ ≤ ε * ‖x ^ (1 / 2 : ℝ)‖ := hx
  rw [e1, e2] at hx'
  exact hx'

/-- For large `x` there are at least `x / (5 log x)` primes in `(x, 2.7 x]`. -/
theorem eventually_card_primes_Ioc_ge : ∀ᶠ x : ℝ in atTop,
    x / (5 * Real.log x) ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) := by
  filter_upwards [eventually_ge_atTop (10 : ℝ),
    eventually_log_pow_le_mul_sqrt 1 (ε := 1 / 2000) (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)] with x hx hlogx hL2
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hl2lo : (693 / 1000 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hfl : ⌊x⌋₊ ≤ ⌊(27 / 10 : ℝ) * x⌋₊ := Nat.floor_le_floor (by linarith)
  have hsplit : Chebyshev.theta ((27 / 10 : ℝ) * x) = Chebyshev.theta x +
      ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p := by
    simp only [Chebyshev.theta, Finset.sum_filter]
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
  have hsum : ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) *
        Real.log ((27 / 10 : ℝ) * x) := by
    have h := Finset.sum_le_card_nsmul ((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime)
      (fun p : ℕ => Real.log p) (Real.log ((27 / 10 : ℝ) * x)) (by
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hpI := Finset.mem_Ioc.mp hp'.1
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
        have hp_le : (p : ℝ) ≤ (27 / 10 : ℝ) * x :=
          le_trans (by exact_mod_cast hpI.2) (Nat.floor_le (by linarith))
        exact Real.log_le_log hp_pos hp_le)
    rw [nsmul_eq_mul] at h
    exact h
  have hlow := Chebyshev.theta_ge' (x := (27 / 10 : ℝ) * x) (by linarith)
  have hup := Chebyshev.theta_le_log4_mul_x hx0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  rw [hlog4] at hup
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hss : √x * √x = x := Real.mul_self_sqrt hx0
  have hs3 : 3 ≤ √x := Real.le_sqrt_of_sq_le (by linarith)
  have hlogx' : Real.log x ≤ 1 / 2000 * √x := by simpa using hlogx
  have hlog27 : Real.log ((27 / 10 : ℝ) * x) ≤ Real.log x + 17 / 10 := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log (27 / 10 : ℝ) ≤ 27 / 10 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlog27' : 0 ≤ Real.log ((27 / 10 : ℝ) * x) := Real.log_nonneg (by linarith)
  have hlogx2 : Real.log ((27 / 10 : ℝ) * x + 2) ≤ Real.log x + 2 := by
    have h3x := Real.log_le_log (by linarith) (show (27 / 10 : ℝ) * x + 2 ≤ 3 * x by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3x
    have : Real.log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hsqrt27 : √((27 / 10 : ℝ) * x) ≤ 2 * √x := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hx0]
  have hprod : √((27 / 10 : ℝ) * x) * Real.log ((27 / 10 : ℝ) * x) ≤
      (2 * √x) * (2 * Real.log x) :=
    mul_le_mul hsqrt27 (by linarith) hlog27' (by positivity)
  have hsL : √x * Real.log x ≤ √x * (1 / 2000 * √x) := mul_le_mul_of_nonneg_left hlogx' hs0
  have hsL3 : 3 ≤ √x * Real.log x := by nlinarith
  have hLsL : Real.log x ≤ √x * Real.log x := by nlinarith
  have hx2 : 693 / 1000 * x ≤ Real.log 2 * x := mul_le_mul_of_nonneg_right hl2lo.le hx0
  have hdiff : (48 / 100 : ℝ) * x ≤
      ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p := by
    linarith [hsplit, hlow, hup, hlogx2, hprod, hsL, hss, hsL3, hLsL, hx2]
  have hcard0 : (0 : ℝ) ≤ (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) := by
    positivity
  have hc1 := mul_le_mul_of_nonneg_left hlog27 hcard0
  have hc2 := mul_nonneg hcard0 (show (0 : ℝ) ≤ 5 / 2 * Real.log x - 17 / 4 by linarith)
  rw [div_le_iff₀ (by linarith)]
  linarith [hsum, hdiff, hc1, hc2]
lemma eventually_L_conds (x₀ : ℝ) : ∀ᶠ L : ℝ in atTop,
    1 ≤ L ∧ x₀ ≤ L ^ 4 / 4 ∧ 2 ≤ L ^ 4 / 4 ∧
    L ^ (39 / 10 : ℝ) ≤ L ^ 4 / (80 * Real.log L) - 18 * L - 1 := by
  have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).bound
    (by norm_num : (0 : ℝ) < 1 / 320)
  filter_upwards [h1, eventually_ge_atTop (4 * |x₀| + 8)] with L hL hL'
  have hx0 : x₀ ≤ |x₀| := le_abs_self x₀
  have habs : 0 ≤ |x₀| := abs_nonneg x₀
  have hL8 : 8 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hL4 : L ≤ L ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  have hu : 0 < L ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hv : 0 < L ^ (39 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have huv : L ^ (1 / 10 : ℝ) * L ^ (39 / 10 : ℝ) = L ^ 4 := by
    rw [← Real.rpow_add hL0, show (1 / 10 : ℝ) + 39 / 10 = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hlog' : Real.log L ≤ L ^ (1 / 10 : ℝ) / 320 := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogL, abs_of_pos hu] at hL
    linarith
  have hv3 : L ^ 3 ≤ L ^ (39 / 10 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ L by linarith)
      (show ((3 : ℕ) : ℝ) ≤ 39 / 10 by norm_num)
    rwa [Real.rpow_natCast] at this
  have hL3 : 9 * L ≤ L ^ 3 := by
    have : L ^ 3 = L * L ^ 2 := by ring
    nlinarith
  have key : 4 * L ^ (39 / 10 : ℝ) ≤ L ^ 4 / (80 * Real.log L) := by
    rw [le_div_iff₀ (by positivity), ← huv]
    nlinarith [mul_le_mul_of_nonneg_left hlog' hv.le]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
end Croot
namespace Croot

open Real Finset Filter

namespace Lemma1Aux

/-! ### Step 1: the Fourier-analytic existence criterion -/

section Fourier

variable {n : ℕ} [NeZero n]

/-- An additive character turns finite sums into products. -/
lemma stdAddChar_sum {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → ZMod n) :
    ZMod.stdAddChar (∑ i ∈ T, f i) = ∏ i ∈ T, ZMod.stdAddChar (f i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- Fourier criterion: if every nontrivial frequency `h` gives a product of norm at most
`2^|R| / n`, then every residue class is a subset sum of the `u i`. -/
theorem exists_subset_sum_of_norm_prod_le {ι : Type*} [DecidableEq ι] (R : Finset ι)
    (u : ι → ZMod n)
    (hbound : ∀ h : ZMod n, h ≠ 0 →
      ‖∏ i ∈ R, (1 + ZMod.stdAddChar (h * u i))‖ ≤ 2 ^ R.card / n)
    (c : ZMod n) : ∃ T ⊆ R, ∑ i ∈ T, u i = c := by
  by_contra hne
  push Not at hne
  set F : ZMod n → ℂ := fun h =>
    ZMod.stdAddChar (-(h * c)) * ∏ i ∈ R, (1 + ZMod.stdAddChar (h * u i)) with hF
  have hexpand : ∀ h : ZMod n,
      F h = ∑ T ∈ R.powerset, ZMod.stdAddChar (h * (∑ i ∈ T, u i - c)) := by
    intro h
    simp only [hF]
    rw [Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← stdAddChar_sum T (fun i => h * u i), ← AddChar.map_add_eq_mul]
    congr 1
    rw [mul_sub, Finset.mul_sum]
    ring
  have key : ∑ h : ZMod n, F h = 0 := by
    rw [Finset.sum_congr rfl fun h _ => hexpand h, Finset.sum_comm]
    refine Finset.sum_eq_zero fun T hT => ?_
    have hT' : ∑ i ∈ T, u i - c ≠ 0 := sub_ne_zero.2 (hne T (Finset.mem_powerset.1 hT))
    have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod n) ℂ))
      (∑ i ∈ T, u i - c) (ZMod.isPrimitive_stdAddChar n)
    rw [if_neg hT', Nat.cast_zero] at this
    exact this
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ (0 : ZMod n))] at key
  have h0 : F 0 = 2 ^ R.card := by
    simp only [hF, zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul, Finset.prod_const]
    norm_num
  rw [h0] at key
  set S := ∑ h ∈ Finset.univ.erase (0 : ZMod n), F h with hS
  have hn : (0 : ℝ) < n := by exact_mod_cast (NeZero.pos n)
  have hSnorm : ‖S‖ ≤ ((n : ℝ) - 1) * (2 ^ R.card / n) := by
    calc ‖S‖ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod n), ‖F h‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod n), (2 ^ R.card / n : ℝ) := by
        refine Finset.sum_le_sum fun h hh => ?_
        simp only [hF]
        rw [norm_mul, AddChar.norm_apply, one_mul]
        exact hbound h (Finset.ne_of_mem_erase hh)
    _ = ((n : ℝ) - 1) * (2 ^ R.card / n) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          ZMod.card, nsmul_eq_mul, Nat.cast_sub NeZero.one_le, Nat.cast_one]
  have hSeq : S = -(2 : ℂ) ^ R.card := by linear_combination key
  rw [hSeq, norm_neg, norm_pow, Complex.norm_two] at hSnorm
  have h2 : (0 : ℝ) < 2 ^ R.card := by positivity
  have hlt : ((n : ℝ) - 1) * (2 ^ R.card / n) < 2 ^ R.card := by
    rw [mul_div_assoc', div_lt_iff₀ hn]
    nlinarith
  linarith

/-- `‖1 + e(x/n)‖² ≤ 4 - 16 (t/n)²`, where `t` is the least absolute residue of `x`. -/
lemma norm_one_add_stdAddChar_sq_le (x : ZMod n) :
    ‖1 + ZMod.stdAddChar x‖ ^ 2 ≤ 4 - 16 * ((x.valMinAbs : ℝ) / n) ^ 2 := by
  set t := x.valMinAbs with ht
  have hx : ((t : ℤ) : ZMod n) = x := ZMod.coe_valMinAbs x
  have hn : (0 : ℝ) < n := by exact_mod_cast (NeZero.pos n)
  set θ : ℝ := 2 * π * t / n with hθ
  have hpsi : ZMod.stdAddChar x = Complex.exp (θ * Complex.I) := by
    rw [← hx, ZMod.stdAddChar_coe]
    congr 1
    rw [hθ]
    push_cast
    ring
  have hθbound : |θ| ≤ π := by
    obtain ⟨h1, h2⟩ := ZMod.valMinAbs_mem_Ioc x
    have h1' : -(n : ℝ) < t * 2 := by exact_mod_cast h1
    have h2' : (t : ℝ) * 2 ≤ n := by exact_mod_cast h2
    rw [abs_le]
    constructor
    · rw [hθ, le_div_iff₀ hn]
      nlinarith [pi_pos]
    · rw [hθ, div_le_iff₀ hn]
      nlinarith [pi_pos]
  have hcos := Real.cos_le_one_sub_mul_cos_sq hθbound
  have hnorm : ‖1 + Complex.exp (θ * Complex.I)‖ ^ 2 = 2 + 2 * Real.cos θ := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [show (1 : ℂ) + (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I)
        = ↑(1 + Real.cos θ) + ↑(Real.sin θ) * Complex.I by push_cast; ring]
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
    linear_combination Real.sin_sq_add_cos_sq θ
  rw [hpsi, hnorm]
  have : 2 / π ^ 2 * θ ^ 2 = 8 * ((t : ℝ) / n) ^ 2 := by
    rw [hθ]
    field_simp
    ring
  linarith

end Fourier

/-! ### Step 2: few primes of size `≥ y` divide a nonzero integer -/

lemma pow_card_le_of_primes_dvd (A : Finset ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hA : ∀ a ∈ A, a.Prime ∧ y ≤ a) (z : ℤ) (hz : z ≠ 0) (hdvd : ∀ a ∈ A, (a : ℤ) ∣ z) :
    y ^ A.card ≤ |(z : ℝ)| := by
  have h1 : ∏ a ∈ A, a ∣ z.natAbs := by
    apply Finset.prod_primes_dvd
    · intro a ha
      exact (hA a ha).1.prime
    · intro a ha
      exact Int.ofNat_dvd_left.1 (hdvd a ha)
  have h2 : ∏ a ∈ A, a ≤ z.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hz) h1
  calc y ^ A.card = ∏ a ∈ A, y := (Finset.prod_const y).symm
  _ ≤ ∏ a ∈ A, (a : ℝ) := Finset.prod_le_prod (fun _ _ => hy) (fun a ha => (hA a ha).2)
  _ = ((∏ a ∈ A, a : ℕ) : ℝ) := by push_cast; rfl
  _ ≤ (z.natAbs : ℝ) := by exact_mod_cast h2
  _ = |(z : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]

/-- The pigeonhole step: few `r` have `|r t_r|` small. -/
lemma card_bad_le (n H : ℕ) (hH0 : 0 < H) (hHn : H < n)
    (R : Finset ℕ) (y : ℝ) (hy : 1 ≤ y) (hR : ∀ r ∈ R, r.Prime ∧ y ≤ r)
    (t : ℕ → ℤ) (ht : ∀ r ∈ R, (n : ℤ) ∣ r * t r - H)
    (L : ℝ) (hL : 0 ≤ L) (m : ℕ) (hm : (L + 2) * n < y ^ (m + 1)) :
    ((R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card : ℝ) ≤ (2 * (L + 1) + 1) * m := by
  set M : ℤ := ⌊L + 1⌋ with hM
  have hM0 : 0 ≤ M := Int.floor_nonneg.2 (by linarith)
  have hML : (M : ℝ) ≤ L + 1 := Int.floor_le _
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hHn)
  have hHnR : (H : ℝ) < n := by exact_mod_cast hHn
  have hH0R : (0 : ℝ) < H := by exact_mod_cast hH0
  -- each fibre is small
  have hfib : ∀ v ∈ Finset.Icc (-M) M,
      (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card ≤ m := by
    intro v hv
    rw [Finset.mem_Icc] at hv
    have hvR : |(v : ℝ)| ≤ L + 1 := by
      rw [abs_le]
      have h1 : ((-M : ℤ) : ℝ) ≤ v := by exact_mod_cast hv.1
      have h2 : (v : ℝ) ≤ (M : ℝ) := by exact_mod_cast hv.2
      push_cast at h1
      constructor <;> linarith
    have hz : (H : ℤ) + n * v ≠ 0 := by
      intro h0
      have h0' : (H : ℝ) + n * v = 0 := by exact_mod_cast h0
      rcases le_or_gt 0 (v : ℝ) with hv0 | hv0
      · nlinarith
      · have : (v : ℝ) ≤ -1 := by
          have : v ≤ -1 := by
            have : v < 0 := by exact_mod_cast hv0
            omega
          exact_mod_cast this
        nlinarith
    have hzabs : |(((H : ℤ) + n * v : ℤ) : ℝ)| < (L + 2) * n := by
      push_cast
      calc |(H : ℝ) + n * v| ≤ |(H : ℝ)| + |(n : ℝ) * v| := abs_add_le _ _
      _ = H + n * |(v : ℝ)| := by
          rw [abs_mul, abs_of_nonneg hH0R.le, abs_of_nonneg hn.le]
      _ < n + n * (L + 1) := by nlinarith
      _ = (L + 2) * n := by ring
    have hpow := pow_card_le_of_primes_dvd (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)) y
      (by linarith)
      (fun r hr => hR r (Finset.mem_filter.1 hr).1) _ hz (fun r hr => (Finset.mem_filter.1 hr).2)
    by_contra hcon
    push Not at hcon
    have : y ^ (m + 1) ≤ y ^ (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card :=
      pow_le_pow_right₀ hy hcon
    linarith
  -- the bad set is covered by the fibres
  have hsub : R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n) ⊆
      (Finset.Icc (-M) M).biUnion (fun v => R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrR, hrbad⟩ := hr
    obtain ⟨v, hv⟩ := ht r hrR
    have hvR : ((r : ℝ) * t r - H) = n * v := by exact_mod_cast hv
    rw [Finset.mem_biUnion]
    refine ⟨v, ?_, ?_⟩
    · have h1 : (n : ℝ) * |(v : ℝ)| < (L + 1) * n := by
        calc (n : ℝ) * |(v : ℝ)| = |(n : ℝ) * v| := by rw [abs_mul, abs_of_pos hn]
        _ = |(r : ℝ) * t r - H| := by rw [hvR]
        _ ≤ |(r : ℝ) * t r| + |(H : ℝ)| := abs_sub _ _
        _ < L * n + n := by rw [abs_of_nonneg hH0R.le]; linarith
        _ = (L + 1) * n := by ring
      have h2 : |(v : ℝ)| < L + 1 := by
        by_contra hcon
        push Not at hcon
        nlinarith
      rw [abs_lt] at h2
      rw [Finset.mem_Icc]
      constructor
      · have : -v ≤ M := Int.le_floor.2 (by push_cast; linarith)
        linarith
      · exact Int.le_floor.2 (by linarith)
    · rw [Finset.mem_filter]
      refine ⟨hrR, ⟨t r, ?_⟩⟩
      linear_combination -hv
  have hcard : (R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card ≤ (2 * M.toNat + 1) * m := by
    calc (R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card
        ≤ ((Finset.Icc (-M) M).biUnion
            (fun v => R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v))).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ Finset.Icc (-M) M, (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ v ∈ Finset.Icc (-M) M, m := Finset.sum_le_sum hfib
    _ = (2 * M.toNat + 1) * m := by
        rw [Finset.sum_const, Int.card_Icc, smul_eq_mul]
        congr 1
        omega
  have hMnat : ((M.toNat : ℕ) : ℝ) = (M : ℝ) := by
    have : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hM0
    exact_mod_cast this
  calc ((R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card : ℝ)
      ≤ (((2 * M.toNat + 1) * m : ℕ) : ℝ) := by exact_mod_cast hcard
  _ = (2 * (M : ℝ) + 1) * m := by push_cast; rw [hMnat]
  _ ≤ (2 * (L + 1) + 1) * m := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      linarith

/-! ### Step 3: elementary inequalities for large `w` -/

lemma ineq_bad (w : ℝ) (hw : 10 ≤ w) :
    (2 * (w ^ 28 + 1) + 1) * (2 * w ^ 10) ≤ w ^ 39 / 2 := by
  have h10 : 0 < w ^ 10 := by positivity
  have h28 : 6 ≤ w ^ 28 := by
    calc (6 : ℝ) ≤ 10 ^ 28 := by norm_num
    _ ≤ w ^ 28 := pow_le_pow_left₀ (by norm_num) hw 28
  have e1 : w ^ 38 = w ^ 28 * w ^ 10 := by ring
  have e2 : w ^ 39 = w * w ^ 38 := by ring
  have h38 : 6 * w ^ 10 ≤ w ^ 38 := by rw [e1]; nlinarith
  have h38' : 0 ≤ w ^ 38 := by positivity
  have h39 : 10 * w ^ 38 ≤ w ^ 39 := by rw [e2]; nlinarith
  have : (2 * (w ^ 28 + 1) + 1) * (2 * w ^ 10) = 4 * w ^ 38 + 6 * w ^ 10 := by ring
  rw [this]
  linarith

lemma ineq_good (w : ℝ) (hw : 10 ≤ w) :
    2 * w ^ 10 ≤ (w ^ 39 / 2) * (4 / (9 * w ^ 24)) := by
  have hw0 : 0 < w := by linarith
  have e : (w ^ 39 / 2) * (4 / (9 * w ^ 24)) = 2 / 9 * w ^ 15 := by
    field_simp
    ring
  rw [e]
  have h5 : 9 ≤ w ^ 5 := by
    calc (9 : ℝ) ≤ 10 ^ 5 := by norm_num
    _ ≤ w ^ 5 := pow_le_pow_left₀ (by norm_num) hw 5
  have e2 : w ^ 15 = w ^ 5 * w ^ 10 := by ring
  rw [e2]
  have h10 : 0 < w ^ 10 := by positivity
  nlinarith

lemma ineq_exp (w : ℝ) (hw : 10 ≤ w) : w ^ 28 + 2 ≤ Real.exp (w ^ 10) := by
  have h := Real.pow_div_factorial_le_exp (w ^ 10) (by positivity) 3
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf] at h
  have e : (w ^ 10) ^ 3 = w ^ 2 * w ^ 28 := by ring
  rw [e] at h
  have h2 : 100 ≤ w ^ 2 := by nlinarith
  have h28 : 1 ≤ w ^ 28 := one_le_pow₀ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ w ^ 28)]

lemma ineq_e (w : ℝ) (hw : 10 ≤ w) : Real.exp 1 ≤ w ^ 40 / 4 := by
  have h := Real.exp_one_lt_three
  have : (10 : ℝ) ^ 40 ≤ w ^ 40 := pow_le_pow_left₀ (by norm_num) hw 40
  have h' : (3 : ℝ) ≤ 10 ^ 40 / 4 := by norm_num
  linarith

/-! ### Step 4: the bound on each nontrivial Fourier coefficient -/

theorem norm_prod_le (n : ℕ) [NeZero n] (w : ℝ) (hw : 10 ≤ w)
    (hn_exp : (n : ℝ) = Real.exp (w ^ 10))
    (R : Finset ℕ) (hR : ∀ r ∈ R, r.Prime ∧ ¬ r ∣ n ∧ w ^ 40 / 4 ≤ r ∧ (r : ℝ) ≤ 3 * w ^ 40)
    (hk : w ^ 39 ≤ R.card) (h : ZMod n) (hh : h ≠ 0) :
    ‖∏ r ∈ R, (1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹))‖ ≤ 2 ^ R.card / n := by
  have hw0 : 0 < w := by linarith
  have hnpos : (0 : ℝ) < n := by rw [hn_exp]; exact Real.exp_pos _
  set H := h.val with hHdef
  have hH0 : 0 < H := ZMod.val_pos.2 hh
  have hHn : H < n := ZMod.val_lt h
  set t : ℕ → ℤ := fun r => (h * ((r : ZMod n))⁻¹).valMinAbs with htdef
  have hdiv : ∀ r ∈ R, (n : ℤ) ∣ r * t r - H := by
    intro r hr
    have hcop : Nat.Coprime r n := ((hR r hr).1.coprime_iff_not_dvd).2 (hR r hr).2.1
    have h1 : (((r : ℤ) * t r : ℤ) : ZMod n) = ((H : ℤ) : ZMod n) := by
      push_cast
      simp only [htdef, ZMod.coe_valMinAbs, hHdef, ZMod.natCast_zmod_val]
      rw [mul_left_comm, ZMod.coe_mul_inv_eq_one r hcop, mul_one]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).1 h1.symm
  set L : ℝ := w ^ 28 with hLdef
  set B := R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n) with hBdef
  set G := R.filter (fun r : ℕ => ¬ |(r : ℝ) * t r| ≤ L * n) with hGdef
  have hBG : B.card + G.card = R.card := Finset.card_filter_add_card_filter_not _
  -- few bad primes
  have hBcard : (B.card : ℝ) ≤ (2 * (L + 1) + 1) * ⌊2 * w ^ 10⌋₊ := by
    have he := ineq_e w hw
    apply card_bad_le n H hH0 hHn R (w ^ 40 / 4) _ _ t hdiv L (by positivity)
    · -- (L + 2) * n < y ^ (m + 1)
      have hL2 : L + 2 ≤ n := by rw [hn_exp, hLdef]; exact ineq_exp w hw
      have h1 : (L + 2) * n ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_right hL2 hnpos.le
      have h2 : (n : ℝ) * n = Real.exp (2 * w ^ 10) := by
        rw [hn_exp, ← Real.exp_add]; ring_nf
      have h3 : Real.exp (2 * w ^ 10) < Real.exp ((⌊2 * w ^ 10⌋₊ + 1 : ℕ) : ℝ) := by
        rw [Real.exp_lt_exp]
        push_cast
        exact Nat.lt_floor_add_one _
      have h4 : Real.exp ((⌊2 * w ^ 10⌋₊ + 1 : ℕ) : ℝ) = Real.exp 1 ^ (⌊2 * w ^ 10⌋₊ + 1) :=
        (Real.exp_one_pow _).symm
      have h5 : Real.exp 1 ^ (⌊2 * w ^ 10⌋₊ + 1) ≤ (w ^ 40 / 4) ^ (⌊2 * w ^ 10⌋₊ + 1) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le he _
      linarith
    · have : (1 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp 0
        simp at this
        linarith [Real.add_one_le_exp 1]
      linarith
    · intro r hr
      exact ⟨(hR r hr).1, (hR r hr).2.2.1⟩
  have hBhalf : (B.card : ℝ) ≤ R.card / 2 := by
    have h1 : (⌊2 * w ^ 10⌋₊ : ℝ) ≤ 2 * w ^ 10 := Nat.floor_le (by positivity)
    have h2 : (2 * (L + 1) + 1) * (⌊2 * w ^ 10⌋₊ : ℝ) ≤ (2 * (L + 1) + 1) * (2 * w ^ 10) := by
      apply mul_le_mul_of_nonneg_left h1
      positivity
    have h3 : (2 * (L + 1) + 1) * (2 * w ^ 10) ≤ w ^ 39 / 2 := by
      rw [hLdef]; exact ineq_bad w hw
    linarith
  have hGcard : w ^ 39 / 2 ≤ (G.card : ℝ) := by
    have : (B.card : ℝ) + G.card = R.card := by exact_mod_cast hBG
    linarith
  -- per-factor bounds
  have hfac : ∀ r ∈ R, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
      ≤ 4 - 16 * ((t r : ℝ) / n) ^ 2 :=
    fun r _ => norm_one_add_stdAddChar_sq_le _
  set a : ℝ := 4 / (9 * w ^ 24) with hadef
  have hgood : ∀ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
      ≤ 4 * Real.exp (-a) := by
    intro r hr
    rw [hGdef, Finset.mem_filter] at hr
    obtain ⟨hrR, hrgood⟩ := hr
    push Not at hrgood
    have hr3 : (r : ℝ) ≤ 3 * w ^ 40 := (hR r hrR).2.2.2
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (hR r hrR).1.pos
    have key : (n : ℝ) < 3 * w ^ 12 * |(t r : ℝ)| := by
      rw [abs_mul, abs_of_pos hrpos] at hrgood
      have : w ^ 28 * n < w ^ 28 * (3 * w ^ 12 * |(t r : ℝ)|) := by
        calc w ^ 28 * (n : ℝ) = L * n := by rw [hLdef]
        _ < r * |(t r : ℝ)| := hrgood
        _ ≤ 3 * w ^ 40 * |(t r : ℝ)| := mul_le_mul_of_nonneg_right hr3 (abs_nonneg _)
        _ = w ^ 28 * (3 * w ^ 12 * |(t r : ℝ)|) := by ring
      exact lt_of_mul_lt_mul_left this (by positivity)
    have key2 : 1 / (9 * w ^ 24) ≤ ((t r : ℝ) / n) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (n : ℝ) ^ 2 < (3 * w ^ 12 * |(t r : ℝ)|) ^ 2 :=
        pow_lt_pow_left₀ key hnpos.le (by norm_num)
      calc 1 * (n : ℝ) ^ 2 ≤ (3 * w ^ 12 * |(t r : ℝ)|) ^ 2 := by linarith
      _ = (t r : ℝ) ^ 2 * (9 * w ^ 24) := by rw [mul_pow, mul_pow, sq_abs]; ring
    have hexp : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
    calc ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ 4 - 16 * ((t r : ℝ) / n) ^ 2 := hfac r hrR
    _ ≤ 4 - 16 * (1 / (9 * w ^ 24)) := by linarith
    _ = 4 * (1 - a) := by rw [hadef]; ring
    _ ≤ 4 * Real.exp (-a) := by linarith
  have hbad : ∀ r ∈ R, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ 4 := by
    intro r hr
    have := hfac r hr
    nlinarith [sq_nonneg ((t r : ℝ) / n)]
  -- the product
  have hprod : ‖∏ r ∈ R, (1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹))‖ ^ 2
      ≤ 4 ^ R.card * Real.exp (-(2 * w ^ 10)) := by
    rw [norm_prod, ← Finset.prod_pow,
      ← Finset.prod_filter_mul_prod_filter_not R (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)]
    have hB' : ∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ 4 ^ B.card := by
      calc ∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ ∏ r ∈ B, (4 : ℝ) :=
            Finset.prod_le_prod (fun _ _ => by positivity)
              (fun r hr => hbad r (Finset.mem_filter.1 hr).1)
      _ = 4 ^ B.card := Finset.prod_const _
    have hG' : ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ (4 * Real.exp (-a)) ^ G.card := by
      calc ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
          ≤ ∏ r ∈ G, (4 * Real.exp (-a)) :=
            Finset.prod_le_prod (fun _ _ => by positivity) hgood
      _ = (4 * Real.exp (-a)) ^ G.card := Finset.prod_const _
    have hexpG : Real.exp (-a) ^ G.card ≤ Real.exp (-(2 * w ^ 10)) := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      have ha : 0 ≤ a := by positivity
      have : 2 * w ^ 10 ≤ G.card * a := by
        calc 2 * w ^ 10 ≤ (w ^ 39 / 2) * a := by rw [hadef]; exact ineq_good w hw
        _ ≤ G.card * a := mul_le_mul_of_nonneg_right hGcard ha
      linarith
    calc (∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2) *
          ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ 4 ^ B.card * (4 * Real.exp (-a)) ^ G.card :=
          mul_le_mul hB' hG' (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
    _ = 4 ^ R.card * Real.exp (-a) ^ G.card := by
          rw [mul_pow, ← mul_assoc, ← pow_add, hBG]
    _ ≤ 4 ^ R.card * Real.exp (-(2 * w ^ 10)) :=
          mul_le_mul_of_nonneg_left hexpG (by positivity)
  have hfinal : (2 ^ R.card / (n : ℝ)) ^ 2 = 4 ^ R.card * Real.exp (-(2 * w ^ 10)) := by
    have e1 : Real.exp (w ^ 10) ^ 2 = Real.exp (2 * w ^ 10) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hn_exp, div_pow, e1, Real.exp_neg, div_eq_mul_inv, ← pow_mul, mul_comm R.card 2,
      pow_mul]
    norm_num
  rw [← hfinal] at hprod
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hprod

end Lemma1Aux

/-! ### Step 5: Croot's Lemma 1 -/

theorem lemma1 : ∀ᶠ n : ℕ in atTop, ∀ R : Finset ℕ,
    (∀ r ∈ R, r.Prime ∧ ¬ r ∣ n ∧ (Real.log n) ^ 4 / 4 ≤ r ∧ (r : ℝ) ≤ 3 * (Real.log n) ^ 4) →
    (Real.log n) ^ (39 / 10 : ℝ) ≤ R.card →
    ∀ c : ZMod n, ∃ T ⊆ R, ∑ r ∈ T, ((r : ZMod n))⁻¹ = c := by
  have hw : ∀ᶠ n : ℕ in atTop, (10 : ℝ) ≤ (Real.log n) ^ (1 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 10
  filter_upwards [hw, eventually_ge_atTop 2] with n hwn hn2 R hR hk c
  have : NeZero n := ⟨by omega⟩
  set w := (Real.log n) ^ (1 / 10 : ℝ) with hwdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogpos : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlog : Real.log n = w ^ 10 := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hlogpos]
    norm_num
  have hn_exp : (n : ℝ) = Real.exp (w ^ 10) := by
    rw [← hlog, Real.exp_log hnpos]
  have h4 : (Real.log n) ^ 4 = w ^ 40 := by rw [hlog]; ring
  have h39 : (Real.log n) ^ (39 / 10 : ℝ) = w ^ 39 := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hlogpos]
    norm_num
  refine Lemma1Aux.exists_subset_sum_of_norm_prod_le R (fun r => ((r : ZMod n))⁻¹) ?_ c
  intro h hh
  refine Lemma1Aux.norm_prod_le n w hwn hn_exp R ?_ ?_ h hh
  · intro r hr
    obtain ⟨h1, h2, h3, h5⟩ := hR r hr
    rw [h4] at h3 h5
    exact ⟨h1, h2, h3, h5⟩
  · rw [← h39]
    exact hk

end Croot

open Finset Filter Real
open scoped BigOperators

private lemma split297 (P : Finset ℕ) (x b : ℝ)
    (h : ∀ r ∈ P, x ≤ r ∧ (r:ℝ) ≤ 27/10*x) (hc : 2*b ≤ P.card)
    (hx : 0≤x) :
    ∃ (a : ℝ) (S : Finset ℕ), S ⊆ P ∧ b ≤ S.card ∧ x ≤ a ∧ a ≤ 2*x ∧
      ∀ r ∈ S, a ≤ r ∧ (r:ℝ) ≤ (5/3)*a := by
  classical
  let Q := P.filter fun r : ℕ => (r:ℝ) ≤ 5/3*x
  by_cases first : b ≤ Q.card
  · refine ⟨x,Q,filter_subset _ _,first,le_rfl,by linarith,?_⟩
    intro r hr
    obtain ⟨hP,hm⟩ := mem_filter.mp hr
    exact ⟨(h r hP).1,hm⟩
  · have hcard := card_sdiff_add_card_eq_card (show Q ⊆ P from filter_subset _ _)
    have hc' : ((P\Q).card:ℝ) + Q.card = P.card := by exact_mod_cast hcard
    refine ⟨5/3*x,P\Q,sdiff_subset,by push_neg at first; linarith,by linarith,by linarith,?_⟩
    intro r hr
    obtain ⟨hP,hm⟩ := mem_sdiff.mp hr
    have hl : ¬ (r:ℝ) ≤ 5/3*x := fun he => hm (mem_filter.mpr ⟨hP,he⟩)
    exact ⟨by linarith,by linarith [(h r hP).2]⟩

theorem shortPrimes297 (ε : ℝ) (he : 0<ε) :
    ∀ᶠ i : ℕ in atTop, ∀ p : ℕ, p.Prime →
      ∃ (a : ℝ) (S : Finset ℕ), 0<a ∧ 100*a ≤ (i:ℝ)^ε ∧
        (S.card:ℝ) ≤ (i:ℝ)^(ε/2) ∧ (log i)^(39/10:ℝ) ≤ S.card ∧
        ∀ r ∈ S, r.Prime ∧ r ≠ p ∧ 3<r ∧ (log i)^4/4 ≤ r ∧ (r:ℝ) ≤ 3*(log i)^4 ∧
          a ≤ r ∧ (r:ℝ) ≤ 5/3*a := by
  have Ltop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have Xtop : Tendsto (fun i : ℕ => (log i)^4) atTop atTop :=
    (tendsto_pow_atTop (by decide : 4 ≠ 0)).comp Ltop
  have ho := ((isLittleO_log_rpow_rpow_atTop (4:ℝ) (show 0 < ε/2 by linarith)).bound
    (show (0:ℝ)<1/500 by norm_num))
  filter_upwards [Xtop.eventually Croot.eventually_card_primes_Ioc_ge,
    Ltop.eventually (Croot.eventually_L_conds 10),
    tendsto_natCast_atTop_atTop.eventually ho, eventually_ge_atTop 2] with i hP hL hrate hi
  intro p hp
  let L := log (i:ℝ)
  let X := L^4
  let P := (Ioc ⌊X⌋₊ ⌊27/10*X⌋₊).filter Nat.Prime
  have L1 : 1 ≤ L := hL.1
  have Xbig : 10 ≤ X/4 := hL.2.1
  have hXp : 0<X := by linarith
  have Lbig : 1<L := by
    by_contra! h
    have e : L=1 := le_antisymm h L1
    simp [X,e] at Xbig
    norm_num at Xbig
  have ll : 0<log L := log_pos Lbig
  have hlogx : log X = 4 * log L := by simp [X,Real.log_pow]
  change X/(5*log X) ≤ (P.card:ℝ) at hP
  rw [hlogx] at hP
  have hc := hL.2.2.2
  change L^(39/10:ℝ) ≤ X/(80*log L)-18*L-1 at hc
  have frac : X/(5*(4*log L)) = 4*(X/(80*log L)) := by ring
  rw [frac] at hP
  have hecard : P.card ≤ (P.erase p).card + 1 := by
    by_cases hpm : p∈P
    · exact (card_erase_add_one hpm).ge
    · simp [erase_eq_of_notMem hpm]
  have hecard' : (P.card:ℝ) ≤ ((P.erase p).card:ℝ)+1 := by exact_mod_cast hecard
  have count : 2*L^(39/10:ℝ) ≤ ((P.erase p).card:ℝ) := by
    have hpos := Real.rpow_nonneg (by linarith : 0≤L) (39/10:ℝ)
    linarith
  have props (r : ℕ) (hr : r ∈ P.erase p) :
      r.Prime ∧ r ≠ p ∧ X ≤ r ∧ (r:ℝ) ≤ 27/10*X := by
    obtain ⟨ne, hP⟩ := mem_erase.mp hr
    obtain ⟨mem,pr⟩ := mem_filter.mp hP
    obtain ⟨lo,up⟩ := mem_Ioc.mp mem
    exact ⟨pr,ne,(Nat.lt_of_floor_lt lo).le, (Nat.le_floor_iff (by positivity)).mp up⟩
  obtain ⟨a,S,sub,num,ax,au,mem⟩ := split297 (P.erase p) X (L^(39/10:ℝ))
    (fun r h => (props r h).2.2) count hXp.le
  have ip : 1 ≤ (i:ℝ) := by exact_mod_cast (show 1 ≤ i from by omega)
  have hhalf : (i:ℝ)^(ε/2) ≤ (i:ℝ)^ε := Real.rpow_le_rpow_of_exponent_le ip (by linarith)
  have xx : X ≤ 1/500 * (i:ℝ)^(ε/2) := by
    simpa [X,L,Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg ip),
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0≤(i:ℝ)) (ε/2))] using hrate
  have bound : S.card ≤ ⌊27/10*X⌋₊ := by
    calc
      _ ≤ (Ioc ⌊X⌋₊ ⌊27/10*X⌋₊).card :=
        card_le_card (sub.trans ((erase_subset _ _).trans (filter_subset _ _)))
      _ ≤ _ := by rw [Nat.card_Ioc]; omega
  have bc := (Nat.le_floor_iff (by positivity : 0 ≤ 27/10*X)).mp bound
  refine ⟨a,S,by linarith,by linarith,by linarith,num,?_⟩
  intro r hr
  obtain ⟨pr,ne,lo,up⟩ := props r (sub hr)
  have r3 : (3:ℝ)<r := by linarith
  exact ⟨pr,ne,by exact_mod_cast r3,by linarith,by linarith,mem r hr⟩


open Finset Real
open scoped BigOperators

private lemma multiplier297 {p : ℕ} (hp : p.Prime) (x : ℝ) (hx : 100 ≤ x) :
    ∃ u : ℕ, x ≤ u ∧ (u:ℝ) ≤ 6/5*x ∧ p.Coprime u ∧ ¬2∣u ∧ ¬3∣u := by
  let c := ⌈x/6⌉₊
  let v := 6*c+1
  let u := if p ∣ v then v+6 else v
  have vl : v ≤ u ∧ u ≤ v+6 := by dsimp [u]; split <;> omega
  have lo : x/6 ≤ (c:ℝ) := Nat.le_ceil _
  have up : (c:ℝ) < x/6+1 := Nat.ceil_lt_add_one (by linarith)
  have vdef : (v:ℝ) = 6*(c:ℝ)+1 := by dsimp [v]; push_cast; ring
  have l' : (v:ℝ) ≤ u := by exact_mod_cast vl.1
  have u' : (u:ℝ) ≤ (v:ℝ)+6 := by exact_mod_cast vl.2
  refine ⟨u,by linarith,by linarith,hp.coprime_iff_not_dvd.mpr ?_,?_,?_⟩
  · dsimp only [u]
    split_ifs with hd
    · intro h
      have hs := (Nat.dvd_add_right hd).mp h
      have hv : p ∣ 6*c := dvd_mul_of_dvd_left hs _
      exact hp.not_dvd_one ((Nat.dvd_add_right hv).mp hd)
    · exact hd
  · dsimp only [u,v]; split <;> omega
  · dsimp only [u,v]; split <;> omega

lemma rescale297 {p k : ℕ} (hp : p.Prime) {a Y : ℝ} (ha : 0 < a) (hY : 100*a ≤ Y)
    (S : Finset ℕ) (mem : ∀ r∈S, r.Prime ∧ r ≠ p ∧ 3<r ∧ a ≤ r ∧ (r:ℝ) ≤ 5/3*a)
    (full : ∀ c : ZMod (p^k), ∃ T ⊆ S, ∑ r ∈ T, (r : ZMod (p^k))⁻¹ = c)
    (z : ZMod (p^k)) :
    ∃ M : Finset ℕ, M.card ≤ S.card ∧
      (∀ m∈M, (p^k).Coprime m ∧ Y ≤ m ∧ (m:ℝ) ≤ 2*Y ∧ ¬6∣p^k*m) ∧
      ∑ m ∈ M, (m : ZMod (p^k))⁻¹ = z := by
  obtain ⟨u,lo,up,cop,u2,u3⟩ := multiplier297 hp (Y/a) ((le_div_iff₀ ha).mpr hY)
  have ua : Y ≤ (u:ℝ)*a := (div_le_iff₀ ha).mp lo
  have ub : (u:ℝ)*a ≤ 6/5*Y := (le_div_iff₀ ha).mp (show (u:ℝ) ≤ (6/5*Y)/a by
    convert up using 1 <;> ring)
  have upos : 0<u := by
    have h : (0:ℝ) < Y/a := by apply div_pos _ ha; nlinarith
    exact_mod_cast h.trans_le lo
  obtain ⟨T,hTS,hT⟩ := full ((u:ZMod (p^k))*z)
  have cu := ZMod.coe_mul_inv_eq_one (n := p^k) u (cop.pow_left k).symm
  refine ⟨T.image (u*·),card_image_le.trans (card_le_card hTS),?_,?_⟩
  · intro m hm
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hm
    obtain ⟨pr,ne,r3,ar,ra⟩ := mem r (hTS hr)
    have cr := (Nat.coprime_primes hp pr).mpr ne.symm
    have u0 : (0:ℝ) ≤ u := by positivity
    have low := mul_le_mul_of_nonneg_left ar u0
    have high := mul_le_mul_of_nonneg_left ra u0
    push_cast
    refine ⟨(cop.mul_right cr).pow_left _,by linarith,by linarith,?_⟩
    intro bad
    have nr2 : ¬2∣r := fun h => by have := (Nat.dvd_prime pr).mp h; omega
    have nr3 : ¬3∣r := fun h => by have := (Nat.dvd_prime pr).mp h; omega
    have go (q : ℕ) (hq : q.Prime) (h6 : q∣6) (hu : ¬q∣u) (hr : ¬q∣r) : q∣p := by
      have h := hq.dvd_mul.mp (h6.trans bad)
      exact hq.dvd_of_dvd_pow (h.resolve_right (fun h => (hq.dvd_mul.mp h).elim hu hr))
    have := (Nat.dvd_prime hp).mp (go 2 Nat.prime_two (by decide) u2 nr2)
    have := (Nat.dvd_prime hp).mp (go 3 Nat.prime_three (by decide) u3 nr3)
    omega
  · rw [sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left upos h)]
    have per (r : ℕ) (hr : r∈T) :
        ((u*r:ℕ):ZMod (p^k))⁻¹ = (u:ZMod (p^k))⁻¹ * (r:ZMod (p^k))⁻¹ := by
      obtain ⟨pr,ne,_⟩ := mem r (hTS hr)
      have cr := ZMod.coe_mul_inv_eq_one (n := p^k) r (((Nat.coprime_primes pr hp).mpr ne).pow_right k)
      apply ZMod.inv_eq_of_mul_eq_one
      push_cast
      calc
        _ = ((u:ZMod (p^k))*(u:ZMod (p^k))⁻¹) * ((r:ZMod (p^k))*(r:ZMod (p^k))⁻¹) := by ring
        _ = _ := by rw [cu, cr, mul_one]
    rw [sum_congr rfl per, ← mul_sum, hT, ← mul_assoc, mul_comm ((u:ZMod (p^k))⁻¹), cu, one_mul]


open Finset Filter Real

theorem sparse297 (ε : ℝ) (he : 0<ε) :
    ∀ᶠ i : ℕ in atTop, IsPrimePow i → ∀ z : ZMod i, ∃ M : Finset ℕ,
      (M.card:ℝ) ≤ (i:ℝ)^(ε/2) ∧
      (∀ m ∈ M, i.Coprime m ∧ (i:ℝ)^ε ≤ m ∧ (m:ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬6∣i*m) ∧
      ∑ m ∈ M, (m:ZMod i)⁻¹ = z := by
  filter_upwards [shortPrimes297 ε he,Croot.lemma1] with i window full
  intro pp z
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff _).mp pp
  obtain ⟨a,S,ha,hY,card,count,mem⟩ := window p hp
  have good (r : ℕ) (hr : r∈S) :
      r.Prime ∧ ¬ r∣p^k ∧ (log (p^k:ℕ))^4/4 ≤ r ∧ (r:ℝ) ≤ 3*(log (p^k:ℕ))^4 := by
    obtain ⟨pr,ne,_,lo,hi,_⟩ := mem r hr
    refine ⟨pr,fun h => ?_,lo,hi⟩
    exact ne ((Nat.dvd_prime hp).mp (pr.dvd_of_dvd_pow h) |>.resolve_left pr.ne_one)
  have Sgood (r : ℕ) (hr : r∈S) := mem r hr
  obtain ⟨M,mc,md,ms⟩ := rescale297 (k := k) hp ha hY S
    (fun r hr => ⟨(Sgood r hr).1,(Sgood r hr).2.1,(Sgood r hr).2.2.1,(Sgood r hr).2.2.2.2.2⟩)
    (full S good count) z
  exact ⟨M,(show (M.card:ℝ) ≤ S.card by exact_mod_cast mc).trans card,md,ms⟩


open Finset Filter Nat
open scoped Classical
namespace Egyptian

lemma ongrid {m i : ℕ} (hm : 0 < m) (hmi : m ≤ i) : m ∣ lcmUpto i :=
  Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨hm,hmi⟩)

lemma unchanged {i : ℕ} (hi : 1 < i) (h : ¬ IsPrimePow i) :
    lcmUpto i = lcmUpto (i-1) := by
  have nz : i ≠ 0 := by omega
  have last : i ∣ lcmUpto (i-1) := by
    apply (Nat.factorization_prime_le_iff_dvd nz (lcmUpto_ne_zero _)).mp
    intro p hp
    apply (hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero _)).mp
    have hd := (hp.pow_dvd_iff_le_factorization nz).mpr (le_refl (i.factorization p))
    apply ongrid (pow_pos hp.pos _)
    have hl := Nat.le_of_dvd (by omega : 0 < i) hd
    by_contra! hf
    have eq : p ^ i.factorization p = i := by omega
    have he : 0 < i.factorization p := by
      by_contra! e
      simp [Nat.eq_zero_of_le_zero e] at eq
      omega
    exact h ((isPrimePow_nat_iff _).mpr ⟨p,_,hp,he,eq⟩)
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro n hn
    obtain ⟨hn,hle⟩ := mem_Icc.mp hn
    by_cases e : n = i
    · simpa [e] using last
    · exact ongrid (m := n) hn (by omega)
  · apply Finset.lcm_dvd
    intro n hn
    exact ongrid (m := n) (mem_Icc.mp hn).1 (by have := (mem_Icc.mp hn).2; omega)

lemma complement {i : ℕ} (hi : IsPrimePow i) :
    i.Coprime (lcmUpto i / i) := by
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff _).mp hi
  apply (hp.coprime_iff_not_dvd.mpr ?_).pow_left
  have hi := pow_pos hp.pos k
  have dvd := ongrid hi le_rfl
  have nz : lcmUpto (p^k) / p^k ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (lcmUpto_pos _) dvd) hi)
  intro h
  have hf := hp.factorization_pos_of_dvd nz h
  rw [Nat.factorization_div dvd] at hf
  simpa [Finsupp.coe_tsub, factorization_lcmUpto _ hp, Nat.log_pow hp.one_lt, hp.factorization_pow] using hf

lemma complement_dvd {i : ℕ} (hi : 0 < i) : lcmUpto i / i ∣ lcmUpto (i-1) := by
  apply (Nat.mul_dvd_mul_iff_left hi).mp
  rw [Nat.mul_div_cancel' (ongrid hi le_rfl)]
  apply Finset.lcm_dvd
  intro n hn
  obtain ⟨hn,hle⟩ := mem_Icc.mp hn
  by_cases e : n = i
  · subst n
    exact dvd_mul_right _ _
  · exact dvd_trans (ongrid hn (show n ≤ i-1 by omega)) (dvd_mul_left _ _)

lemma cancel {i : ℕ} (hi : 0 < i) {M : Finset ℕ}
    (adm : ∀ m ∈ M, 0 < m ∧ m ≤ i ∧ i.Coprime m)
    (hc : i.Coprime (lcmUpto i / i)) (z : ℤ)
    (res : ∑ m ∈ M, (m : ZMod i)⁻¹ = (z : ZMod i) * ((lcmUpto i / i : ℕ) : ZMod i)⁻¹) :
    ∃ a : ℤ, (a:ℚ)/lcmUpto (i-1) = (z:ℚ)/lcmUpto i - ∑ m ∈ M, (1:ℚ)/((i:ℚ)*m) := by
  let D := lcmUpto i / i
  have he : i*D = lcmUpto i := Nat.mul_div_cancel' (ongrid hi le_rfl)
  have dvd (m : ℕ) (hm : m ∈ M) : m ∣ D :=
    (adm m hm).2.2.symm.dvd_of_dvd_mul_left (he.symm ▸ ongrid (adm m hm).1 (adm m hm).2.1)
  have hmz (m : ℕ) (hm : m ∈ M) : ((D/m : ℕ) : ZMod i) = (D : ZMod i) * (m : ZMod i)⁻¹ := by
    have hh : ((D/m : ℕ):ZMod i)*(m:ZMod i) = D := by rw [← Nat.cast_mul, Nat.div_mul_cancel (dvd m hm)]
    rw [← hh, mul_assoc, ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr (adm m hm).2.2.symm), mul_one]
  have modzero : ((z - ∑ m ∈ M, ((D/m:ℕ):ℤ) : ℤ) : ZMod i) = 0 := by
    simp only [Int.cast_sub,Int.cast_sum,Int.cast_natCast]
    rw [sum_congr rfl hmz, ← mul_sum, res]
    change (z:ZMod i) - (D:ZMod i)*((z:ZMod i)*(D:ZMod i)⁻¹) = 0
    rw [mul_left_comm, ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr hc.symm), mul_one, sub_self]
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp modzero
  obtain ⟨c,hc'⟩ := complement_dvd hi
  refine ⟨b*c,?_⟩
  have rat (m : ℕ) (hm : m ∈ M) : (1:ℚ)/((i:ℚ)*m) = ((D/m:ℕ):ℚ)/lcmUpto i := by
    have mm : (m:ℚ) ≠ 0 := by exact_mod_cast (adm m hm).1.ne'
    apply (div_eq_div_iff (mul_ne_zero (by exact_mod_cast hi.ne') mm) (by exact_mod_cast lcmUpto_ne_zero i)).mpr
    have ff : ((D/m:ℕ):ℚ)*(m:ℚ) = D := by exact_mod_cast Nat.div_mul_cancel (dvd m hm)
    have gg : (i:ℚ)*D = lcmUpto i := by exact_mod_cast he
    linear_combination gg*(-1) + ((i:ℚ)*ff)*(-1)
  rw [sum_congr rfl rat, ← sum_div, ← sub_div]
  have rb : (z:ℚ) - ∑ m ∈ M, ((D/m:ℕ):ℚ) = (i:ℚ)*b := by simpa only [Int.cast_sub,Int.cast_sum,Int.cast_natCast,Int.cast_mul] using congrArg (Int.cast : ℤ → ℚ) hb
  rw [rb]
  push_cast
  have eq : (i:ℚ)*D = lcmUpto i := by exact_mod_cast he
  have eq' : (lcmUpto (i-1):ℚ) = (D:ℚ)*c := by exact_mod_cast hc'
  apply (div_eq_div_iff (by exact_mod_cast lcmUpto_ne_zero (i-1)) (by exact_mod_cast lcmUpto_ne_zero i)).mpr
  rw [← eq,eq']; ring

lemma budget {ε : ℝ} (he : 0 < ε) (d : ℚ) (hd : 0 < d) :
    let cost (i : ℕ) : ℚ := (⌊(i:ℝ)^(ε/2)⌋₊ : ℚ)/((i:ℚ)*⌈(i:ℝ)^ε⌉₊)
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ B, ∑ i ∈ Ioc L B, cost i < d := by
  dsimp only
  have sm := Real.summable_nat_rpow.mpr (show -1-ε/2 < -1 by linarith)
  obtain ⟨s,hs⟩ := summable_iff_vanishing_norm.mp sm (d:ℝ) (by exact_mod_cast hd)
  refine ⟨s.sup id,?_⟩
  intro L hL B
  have dj : Disjoint (Ioc L B) s := by
    apply disjoint_left.mpr
    intro i hi hs
    have : i ≤ s.sup id := le_sup (f := id) hs
    have := (mem_Ioc.mp hi).1
    omega
  have tail := hs _ dj
  have bound (i : ℕ) (hi : i ∈ Ioc L B) :
      (⌊(i:ℝ)^(ε/2)⌋₊:ℝ)/((i:ℝ)*⌈(i:ℝ)^ε⌉₊) ≤ (i:ℝ)^(-1-ε/2) := by
    have hp : 0 < (i:ℝ) := by exact_mod_cast (Nat.zero_le L).trans_lt (mem_Ioc.mp hi).1
    have v := Real.rpow_pos_of_pos hp ε
    have fl := Nat.floor_le (Real.rpow_nonneg hp.le (ε/2))
    have cl := Nat.le_ceil ((i:ℝ)^ε)
    calc
      _ ≤ (i:ℝ)^(ε/2)/((i:ℝ)*(i:ℝ)^ε) := by
        apply div_le_div₀ (Real.rpow_nonneg hp.le _) fl (mul_pos hp v) (mul_le_mul_of_nonneg_left cl hp.le)
      _ = _ := by
        rw [show (i:ℝ)*(i:ℝ)^ε = (i:ℝ)^(1+ε) by rw [Real.rpow_add hp, Real.rpow_one], ← Real.rpow_sub hp]
        congr 1; ring
  have est := sum_le_sum bound
  have pos : 0 ≤ ∑ i ∈ Ioc L B, (i:ℝ)^(-1-ε/2) := sum_nonneg fun i _ => Real.rpow_nonneg (by positivity) _
  rw [Real.norm_eq_abs,abs_of_nonneg pos] at tail
  apply (Rat.cast_lt (K := ℝ)).mp
  push_cast
  exact est.trans_lt tail

def Goal : Prop := ∀ ε : ℝ, 0 < ε → ε < 1/2 → ∀ d : ℚ, 0 < d →
  ∃ L₀ : ℕ, ∀ L ≥ L₀,
    let J (i : ℕ) := (Icc 1 i).lcm id
    let K := J L
    let R (i : ℕ) := (Icc 1 (i*i)).filter fun n => IsPrimePow i ∧ i∣n ∧ Nat.Coprime i (n/i) ∧
        (i:ℝ)^ε ≤ (n/i:ℕ) ∧ ((n/i:ℕ):ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬ K ∣ n
    ∃ cost : ℕ → ℚ, (∀ B, ∑ i ∈ Ioc L B, cost i < d) ∧
      ∀ i : ℕ, L < i → ∀ z : ℤ, ∃ V ⊆ R i,
        (∑ n ∈ V, (1:ℚ)/n) ≤ cost i ∧ ∃ a : ℤ,
        (a:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V, (1:ℚ)/n


theorem full297 : Goal := by
  intro ε he hsmall d hd
  let cost (i : ℕ) : ℚ := (⌊(i:ℝ)^(ε/2)⌋₊:ℚ)/((i:ℚ)*⌈(i:ℝ)^ε⌉₊)
  obtain ⟨L₁,small⟩ := budget he d hd
  have grows (a : ℝ) (ha : 0 < a) (b : ℝ) : ∀ᶠ i : ℕ in atTop, b ≤ (i:ℝ)^a :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨L₂,large⟩ := eventually_atTop.mp ((sparse297 ε he).and
    ((grows ε he 100).and (grows (1-ε) (by linarith) 2)))
  refine ⟨max 6 (max L₁ L₂),?_⟩
  intro L hL
  have h6 : 6 ≤ L := by omega
  refine ⟨cost,small L (by omega),?_⟩
  intro i hLi z
  have hi : 0 < i := by omega
  have hpos : 0 < (i:ℝ) := by exact_mod_cast hi
  obtain ⟨mod,hr,hr'⟩ := large i (by omega)
  have upper : 2*(i:ℝ)^ε ≤ i := calc
    _ ≤ (i:ℝ)^(1-ε)*(i:ℝ)^ε := mul_le_mul_of_nonneg_right hr' (Real.rpow_nonneg hpos.le _)
    _ = _ := by rw [← Real.rpow_add hpos,sub_add_cancel,Real.rpow_one]
  by_cases pp : IsPrimePow i
  · obtain ⟨M,card,data,res⟩ := mod pp
      ((z:ZMod i)*((Nat.lcmUpto i / i : ℕ):ZMod i)⁻¹)
    have adm (m : ℕ) (hm : m ∈ M) : 0 < m ∧ m ≤ i ∧ i.Coprime m := by
      obtain ⟨cop,lo,up,_⟩ := data m hm
      exact ⟨by exact_mod_cast (Real.rpow_pos_of_pos hpos ε).trans_le lo,by exact_mod_cast up.trans upper,cop⟩
    have inj : Function.Injective (fun m : ℕ => i*m) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hi h
    have imageSum : ∑ n ∈ M.image (i*·), (1:ℚ)/n = ∑ m ∈ M, (1:ℚ)/((i:ℚ)*m) := by
      rw [sum_image (fun _ _ _ _ eq => inj eq)]
      simp
    refine ⟨M.image (i*·),?_,?_,?_⟩
    · intro n hn
      obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
      obtain ⟨mp,mi,cp⟩ := adm m hm
      obtain ⟨_,lo,up,avoid⟩ := data m hm
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hi mp,Nat.mul_le_mul_left _ mi⟩,pp,dvd_mul_right _ _,?_⟩
      simp only [Nat.mul_div_cancel_left _ hi]
      exact ⟨cp,lo,up,fun h => avoid (dvd_trans (ongrid (by decide : 0 < 6) h6) h)⟩
    · rw [imageSum]
      have count : M.card ≤ ⌊(i:ℝ)^(ε/2)⌋₊ := Nat.le_floor card
      have ceilpos : 0 < ⌈(i:ℝ)^ε⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hpos _)
      have cpos : 0 < (i:ℚ)*(⌈(i:ℝ)^ε⌉₊:ℕ) := by positivity
      calc
        _ ≤ ∑ _m ∈ M, (1:ℚ)/((i:ℚ)*⌈(i:ℝ)^ε⌉₊) := by
          apply sum_le_sum
          intro m hm
          have lower := Nat.ceil_le.mpr (data m hm).2.1
          exact one_div_le_one_div_of_le cpos (mul_le_mul_of_nonneg_left (by exact_mod_cast lower) (by positivity))
        _ = (M.card:ℚ)/((i:ℚ)*⌈(i:ℝ)^ε⌉₊) := by simp [div_eq_mul_inv]
        _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast count) cpos.le
    · rw [imageSum]
      exact cancel hi adm (complement pp) z res
  · refine ⟨∅,empty_subset _,by simp [cost]; positivity,z,?_⟩
    simp only [sum_empty,sub_zero]
    change (z:ℚ)/(Nat.lcmUpto (i-1)) = (z:ℚ)/Nat.lcmUpto i
    rw [unchanged (by omega) pp]

end Egyptian

theorem checked_leaf : OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1_H1_R1.H2 := Egyptian.full297


end ModularCorrection

theorem assembled_general : type_of% @Erdos297.erdos_297.variants.general := OMA.R_Erdos297_erdos_297_variants_general_R1.main Calibration.checked_leaf PartitionLimit.checked_leaf (OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1.main BoundedCount.checked_leaf (OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1.main (OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1_H1_R1.main ReservoirDensity.checked_leaf ModularCorrection.checked_leaf) IntegerSums.checked_leaf))

open Erdos297 in
theorem OMA.solution : type_of% @Erdos297.erdos_297 := by
  obtain ⟨hu,ht⟩ := assembled_general (1 : ℚ) (by norm_num)
  have hex : ∃! l : ℝ, massIntegral l = 1 := by simpa only [Rat.cast_one] using hu
  obtain ⟨l,hl,_⟩ := hex
  refine ⟨by simpa only [Rat.cast_one] using hu,?_⟩
  simpa only [Rat.cast_one,PartitionLimit.unit_entropy_value l hl] using ht
