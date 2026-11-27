import OMAReductions.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic.Linarith

/-! # A restricted sumset and the local interval argument

For each orientation of a long interval, Claim 5.9 of Pokrovskiy
(arXiv:1308.2176) supplies negative prefix sums at ordinary integer lifts of
a restricted sumset. The global sparse-window count bounds the number of
residues containing a bad vertex in either orientation. Transport by two and
three periods then sends most of the seeds to the same central block.
-/

namespace OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1_H2_R1
open Finset Fin.CommRing

/-- The cyclic restricted sumset estimate from Claim 5.10. -/
def H1 : Prop := ∀ (k : ℕ) [NeZero k] (A B : Finset (Fin k)) (S : Finset (Fin k × Fin k)),
    S ⊆ A ×ˢ B → (∀ u, u ∈ A ∨ -u ∈ A) → (∀ u, u ∈ B ∨ -u ∈ B) →
    10000*(A ×ˢ B \ S).card ≤ k^2 → 3*k ≤ 5*(S.image (fun p => p.1+p.2)).card

/-- Localization and the short prefixes from Claims 5.2 and 5.9. The first
vertex of the arc is s, its length is m, and F is its actual prefix-sum
function. D may include the residues of all bad vertices in this orientation. -/
def H2 : Prop := ∀ (n k : ℕ), (hk : 2 ≤ k) → (hl : 10^46*k ≤ n) → n < 8*k^2 → ∀ (hn : 2*k ≤ n)
    (x : Fin n → ℝ), 
    let E := fun a : Fin n × Fin (k-1) × Fin (k-1) =>
      univ.image (fun t : Fin k => a.1 + (⟨if t.val ≤ a.2.1.val then t.val else t.val+a.2.2.val+1,
        by have := t.isLt; have := a.2.2.isLt; split <;> omega⟩ : Fin n))
    (univ.filter (fun a => 0 ≤ ∑ v ∈ E a, x v)).card < k*(k-1)^2 →
    letI : NeZero n := ⟨by omega⟩
    letI : NeZero k := ⟨by omega⟩
    ∃ (s : Fin n) (m : ℕ), 64*k ≤ m ∧ m ≤ n ∧
      let F := fun t : ℕ => ∑ j ∈ range t, x (s + Fin.ofNat n j)
      (∑ v, x v) ≤ F m ∧ ∀ rev : Bool,
        let f := fun t => if rev then F m - F (m-t) else F t
        ∃ (A B D : Finset (Fin k)) (S : Finset (Fin k × Fin k)),
          S ⊆ A ×ˢ B ∧ (∀ u, u ∈ A ∨ -u ∈ A) ∧ (∀ u, u ∈ B ∨ -u ∈ B) ∧
          10000*(A ×ˢ B \ S).card ≤ k^2 ∧ 100*D.card ≤ k ∧
          (∀ p ∈ S, f (13*k+p.1.val+p.2.val) < 0) ∧
          (∀ u : ℕ, Fin.ofNat k u ∉ D → ∀ d : ℕ, d = 2 ∨ d = 3 →
            u+d*k ≤ m → f (u+d*k) < f u)

/-- Reach every cut in the same residue at distance at least two periods, using
only two-period and three-period decreases. -/
theorem transport {k m s t : ℕ} [NeZero k] (f : ℕ → ℝ) (D : Finset (Fin k))
    (jump : ∀ u : ℕ, (u : Fin k) ∉ D → ∀ d : ℕ, d = 2 ∨ d = 3 →
      u + d*k ≤ m → f (u+d*k) < f u)
    (hs : f s < 0) (good : (s : Fin k) ∉ D)
    (congruent : (s : Fin k) = (t : Fin k)) (gap : s+2*k ≤ t) (ht : t ≤ m) :
    f t < 0 := by
  have hk := NeZero.pos k
  have hmod : s ≡ t [MOD k] := congrArg Fin.val congruent
  obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' (by omega : s ≤ t)).mp hmod
  have htq : t = s+q*k := by rw [Nat.mul_comm] at hq; omega
  have h2 : 2 ≤ q := Nat.le_of_mul_le_mul_right (by omega : 2*k ≤ q*k) hk
  rw [htq] at ht ⊢
  clear hq htq hmod congruent gap
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases base : q ≤ 3
    · exact lt_trans (jump s good q (by omega) ht) hs
    · let p := q-2
      have hq : q = p+2 := by dsimp [p]; omega
      have e : s+q*k = (s+p*k)+2*k := by rw [hq, Nat.add_mul, Nat.add_assoc]
      have pfit : s+p*k ≤ m := by omega
      have pge : 2 ≤ p := by dsimp [p]; omega
      have prev := ih p (by dsimp [p]; omega) pfit pge
      have hp : ((s+p*k : ℕ) : Fin k) = (s : Fin k) := by simp
      exact e ▸ lt_trans (jump _ (hp ▸ good) 2 (Or.inl rfl) (by omega)) prev

/-- A nearly complete collection of negative double-interval seeds forces a
strict majority of negative values at any aligned block of k interior cuts. -/
theorem negative_majority {k m : ℕ} [NeZero k] (bound : H1) (f : ℕ → ℝ)
    (A B D : Finset (Fin k)) (S : Finset (Fin k × Fin k)) (sub : S ⊆ A ×ˢ B)
    (antiA : ∀ u, u ∈ A ∨ -u ∈ A) (antiB : ∀ u, u ∈ B ∨ -u ∈ B)
    (deleted : 10000*(A ×ˢ B \ S).card ≤ k^2) (few : 100*D.card ≤ k)
    (seeds : ∀ p ∈ S, f (13*k+p.1.val+p.2.val) < 0)
    (jump : ∀ u : ℕ, (u : Fin k) ∉ D → ∀ d : ℕ, d = 2 ∨ d = 3 →
      u+d*k ≤ m → f (u+d*k) < f u)
    (T : Fin k → ℕ) (e : Fin k ≃ Fin k) (align : ∀ i, (T i : Fin k) = e i)
    (inside : ∀ i, 17*k ≤ T i ∧ T i ≤ m) :
    k < 2*(univ.filter (fun i => f (T i) < 0)).card := by
  classical
  let U := S.image (fun p => p.1+p.2)
  have size : 3*k ≤ 5*U.card := bound k A B S sub antiA antiB deleted
  have rem : U.card ≤ (U \ D).card + D.card := card_le_card_sdiff_add_card
  have inj := card_le_card_of_injOn (s := U \ D) (t := univ.filter (fun i => f (T i) < 0))
    e.symm (by
      intro r hr
      obtain ⟨hr, hd⟩ := mem_sdiff.mp hr
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hr
      have eqn : ((13*k+p.1.val+p.2.val : ℕ) : Fin k) = p.1+p.2 := by simp
      have he := align (e.symm (p.1+p.2))
      rw [Equiv.apply_symm_apply] at he
      obtain ⟨lo,hi⟩ := inside (e.symm (p.1+p.2))
      have h₁ := p.1.isLt
      have h₂ := p.2.isLt
      exact mem_filter.mpr ⟨mem_univ _, transport f D jump (seeds p hp) (eqn ▸ hd)
        (eqn.trans he.symm) (by omega) hi⟩) e.symm.injective.injOn
  have hk := NeZero.pos k
  omega

theorem main : H1 → H2 → OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1.H2 := by
  classical
  intro bound localize n k hk hl hu hn x hx
  dsimp only
  by_contra! few
  let : NeZero k := ⟨by omega⟩
  let : NeZero n := ⟨by omega⟩
  obtain ⟨s,m,hm,_,mass,orient⟩ := localize n k hk hl hu hn x few
  let F := fun t : ℕ => ∑ j ∈ range t, x (s + Fin.ofNat n j)
  change (∑ v, x v) ≤ F m at mass
  rw [hx] at mass
  let cut := fun i : Fin k => 32*k+i.val
  have near (i : Fin k) : 17*k ≤ cut i ∧ cut i ≤ m ∧ 17*k ≤ m-cut i := by
    dsimp [cut]
    have := i.isLt
    omega
  have forward (i : Fin k) : (cut i : Fin k) = i := by simp [cut]
  have backward (i : Fin k) : ((m-cut i : ℕ) : Fin k) = (m : Fin k)-i := by
    apply eq_sub_iff_add_eq.mpr
    calc
      _ = ((m-cut i : ℕ) : Fin k) + (cut i : Fin k) := congrArg _ (forward i).symm
      _ = _ := by rw [← Nat.cast_add, Nat.sub_add_cancel (near i).2.1]
  let L := univ.filter (fun i => F (cut i) < 0)
  let R := univ.filter (fun i => F m - F (cut i) < 0)
  have leftSize : k < 2*L.card := by
    obtain ⟨A,B,D,S,hS,hA,hB,hd,hD,hseed,hjump⟩ := orient false
    exact negative_majority bound F A B D S hS hA hB hd hD hseed hjump cut
      (Equiv.refl _) forward (fun i => ⟨(near i).1,(near i).2.1⟩)
  have rightSize : k < 2*R.card := by
    obtain ⟨A,B,D,S,hS,hA,hB,hd,hD,hseed,hjump⟩ := orient true
    have h := negative_majority bound (fun t => F m-F (m-t)) A B D S hS hA hB hd hD hseed hjump
      (fun i => m-cut i) (Equiv.subLeft (m : Fin k)) backward
      (fun i => ⟨(near i).2.2, Nat.sub_le ..⟩)
    simpa only [Nat.sub_sub_self (near _).2.1, R] using h
  have dis : Disjoint L R := disjoint_left.mpr (by
    intro i hi hj
    have hL := (mem_filter.mp hi).2
    have hR := (mem_filter.mp hj).2
    change F (cut i) < 0 at hL
    change F m - F (cut i) < 0 at hR
    linarith)
  have maxSize := card_le_univ (L ∪ R)
  rw [card_union_of_disjoint dis, Fintype.card_fin] at maxSize
  omega

end OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1_H2_R1
