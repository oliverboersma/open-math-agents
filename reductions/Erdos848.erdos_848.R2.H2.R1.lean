import OMAReductions.R_Erdos848_erdos_848_R2
import Mathlib
/-!
A finite Hall reduction for Erdős 848. The underlying Hall-cut formulation
is due to Alex Chengyu Li (https://github.com/crabsatellite/erdos-848-squarefree-product).
We restrict mixed obstructions to sets minimal under deletion. Kernel-verified
certificates are available for the prefix and the explicit tail.
-/
namespace Erdos848Hall
open Finset Erdos848
variable (gamma : Finset ℕ → Finset ℕ → Finset ℕ)
variable (gamma_eq : ∀ base X, gamma base X = base.filter (fun a => ∃ b∈X, Squarefree (a*b+1)))
include gamma_eq

theorem gamma_mono {base X Y : Finset ℕ} (sub : X⊆Y) : gamma base X ⊆ gamma base Y := by
  rw [gamma_eq,gamma_eq]
  intro a h
  obtain ⟨aB,b,bX,e⟩ := mem_filter.mp h
  exact mem_filter.mpr ⟨aB,b,sub bX,e⟩

theorem minimal_obstruction {base Y : Finset ℕ} (bad : (gamma base Y).card < Y.card) :
    ∃ X⊆Y, (X.Nonempty ∧ (gamma base X).card+1=X.card ∧ (∀ a∈gamma base X, ∃ b∈X, ∃ c∈X, b≠c ∧ Squarefree (a*b+1) ∧ Squarefree (a*c+1))) := by
  classical
  let failures := Y.powerset.filter (fun X => (gamma base X).card<X.card)
  have member : Y∈failures := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl,bad⟩
  obtain ⟨X,hX,m⟩ := failures.exists_min_image Finset.card ⟨Y,member⟩
  obtain ⟨sX,bX⟩ := mem_filter.mp hX
  have sub := mem_powerset.mp sX
  have non : X.Nonempty := card_pos.mp (Nat.zero_lt_of_lt bX)
  have good (b : ℕ) (hb : b∈X) : (X.erase b).card≤(gamma base (X.erase b)).card := by
    by_contra! defect
    have e : X.erase b∈failures := mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset ..).trans sub),defect⟩
    have m' := m _ e
    exact (card_erase_lt_of_mem hb).not_ge m'
  have eq (b : ℕ) (hb : b∈X) : gamma base (X.erase b)=gamma base X := by
    apply Finset.eq_of_subset_of_card_le (gamma_mono gamma gamma_eq (erase_subset ..))
    have size := good b hb
    have card := card_erase_add_one hb
    omega
  refine ⟨X,sub,non,?_,?_⟩
  · obtain ⟨b,hb⟩ := non
    have size := good b hb
    rw [eq b hb] at size
    have card := card_erase_add_one hb
    omega
  · intro a ha
    obtain ⟨_,b,hb,ab⟩ := mem_filter.mp ((gamma_eq _ _) ▸ ha)
    have h' : a∈gamma base (X.erase b) := (eq b hb).symm ▸ ha
    obtain ⟨_,c,hc,ac⟩ := mem_filter.mp ((gamma_eq _ _) ▸ h')
    exact ⟨b,hb,c,(mem_erase.mp hc).2,(mem_erase.mp hc).1.symm,ab,ac⟩

theorem critical_of_counterexample {N : ℕ} {A : Finset ℕ}
    (sub : A ⊆ range N) (adm : NonSquarefreeProductProp A) (bad : (A₇ N).card < A.card) :
    ∃ X ⊆ range N \ A₇ N, NonSquarefreeProductProp X ∧ (X.Nonempty ∧ (gamma (A₇ N) X).card+1=X.card ∧ (∀ a∈gamma (A₇ N) X, ∃ b∈X, ∃ c∈X, b≠c ∧ Squarefree (a*b+1) ∧ Squarefree (a*c+1))) := by
  classical
  let base := A₇ N
  let Y := A \ base
  have Ysub : Y⊆A := sdiff_subset
  have gammaSep : Disjoint (gamma base Y) (A∩base) := by
    apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨_,b,hy,ab⟩ := mem_filter.mp ((gamma_eq _ _) ▸ ha)
    exact adm a (mem_inter.mp hb).1 b (Ysub hy) ab
  have union_sub : gamma base Y ∪ (A∩base) ⊆ base :=
    union_subset (by rw [gamma_eq]; exact filter_subset ..) inter_subset_right
  have counts := card_le_card union_sub
  rw [card_union_of_disjoint gammaSep] at counts
  have split := card_sdiff_add_card_inter A base
  have fail : (gamma base Y).card<Y.card := by
    change base.card<A.card at bad
    dsimp only [Y] at counts ⊢
    omega
  obtain ⟨X,hX,w⟩ := minimal_obstruction gamma gamma_eq fail
  refine ⟨X,?_,?_,w⟩
  · intro a ha
    have ay := mem_sdiff.mp (hX ha)
    exact mem_sdiff.mpr ⟨sub ay.1,ay.2⟩
  · exact fun a ha b hb => adm a (Ysub (hX ha)) b (Ysub (hX hb))


end Erdos848Hall

namespace OMA.R_Erdos848_erdos_848_R2_H2_R1
open Finset Erdos848 Erdos848Hall


/-- Finite prefix, for which an explicit coloring certificate is available. -/
def H1 : Prop := ∀ N : ℕ, N ≤ 210007 → Erdos848For N

/-- Hall's condition from the opposite residue class at the remaining endpoints. -/
def H2 : Prop := ∀ k : ℕ, 210007<25*k+7 → 25*k+7<10^13 →
  ∀ X⊆(range (25*k+7)).filter (fun x => x%25=18), X.card ≤
    ((A₇ (25*k+7)).filter (fun a => ∃ b∈X,Squarefree (a*b+1))).card

/-- Every mixed, compatible outside set with a Hall defect contains a minimal
obstruction with deficit one and at least two edges to every one of its neighbors. -/
def H3 : Prop := ∀ k : ℕ, 210007<25*k+7 → 25*k+7<10^13 →
  ∀ X⊆range (25*k+7) \ A₇ (25*k+7), NonSquarefreeProductProp X →
    (∃ x∈X, x%25≠18) →
      let Γ := (A₇ (25*k+7)).filter (fun a => ∃ b∈X, Squarefree (a*b+1))
      ¬ (X.Nonempty ∧ Γ.card+1=X.card ∧
        ∀ a∈Γ, ∃ b∈X, ∃ c∈X, b≠c ∧ Squarefree (a*b+1) ∧ Squarefree (a*c+1))

/-- Explicit analytic tail proved using the two-stage prime-counting estimate,
the Pell gap and the complementary-divisor bound for quadratic congruences. -/
def H4 : Prop := ∀ N : ℕ, 10^13 ≤ N → Erdos848For N

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos848_erdos_848_R2.H2 := by
  intro initial pure mixed tail k _ _ B sub cardB _ _
  by_contra! adm
  have compatible : NonSquarefreeProductProp B := adm
  let N := 25*k+7
  have base : (A₇ N).card=k := by
    rw [A₇,OMA.R_Erdos848_erdos_848_R2.card_range_filter_mod25_eq 7 (by decide)]
    dsimp [N]
    omega
  have falsebound : ¬ Erdos848For N := by
    intro atN
    have := atN B sub compatible
    omega
  have small : 210007 < N := lt_of_not_ge (fun low => falsebound (initial N low))
  have large : N < 10^13 := lt_of_not_ge (fun high => falsebound (tail N high))
  let gamma (base X : Finset ℕ) := base.filter (fun a => ∃ b∈X,Squarefree (a*b+1))
  obtain ⟨X,xsub,xadm,crit⟩ := critical_of_counterexample gamma (fun _ _ => rfl) (N:=N) sub compatible (by omega)
  by_cases alt : ∀ x∈X, x%25=18
  · have incl : X ⊆ (range N).filter (fun n => n%25=18) := fun x hx =>
      mem_filter.mpr ⟨(mem_sdiff.mp (xsub hx)).1,alt x hx⟩
    have bound := pure k small large X incl
    have defic := crit.2.1
    change X.card ≤ (gamma (A₇ N) X).card at bound
    omega
  · exact (mixed k small large X xsub xadm (by push_neg at alt; exact alt)) crit

end OMA.R_Erdos848_erdos_848_R2_H2_R1
