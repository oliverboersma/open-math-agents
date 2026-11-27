import OMAReductions.R_Erdos28_erdos_28_R1

/-!
# Finite bases in the Erdős–Turán problem on additive representations

TheWaler's reduction in PR 4711 asks for a finite obstruction at every
ordered representation bound. Claude's proof for @anmolspace in PR 5250
settled the separate finite-edit lemma. Here a degree bound D for globally
capped finite bases gives a prefix obstruction by 2D+1.

Grekos, Haddad, Helou and Pihko, On the Erdős–Turán conjecture, J. Number
Theory 102 (2003), §6.4, give the sharp endpoint 70 for the cap of five.
Borwein, Choi and Chu, An old conjecture of Erdős–Turán on additive bases,
Math. Comp. 75 (2006), define globally capped bases and study their degrees
and lengths. The finite truncation here uses their degree viewpoint. The
first step asks for the published cap-five instance. The second asks whether
bounded lengths persist when the odd cap increases by two. The latter is
open. The reduction also proves a prefix inequality that counts unordered
pairs and discards pairs too large to represent any sum in the prefix.

Formalization and assembly: @anmolspace with OpenAI Codex.
-/

namespace OMA.Erdos28Capacity

/-- In a prefix every represented sum consumes an unordered pair. Two elements
in its upper half cannot supply such a pair, even when they are equal. -/
theorem prefix_capacity (S : Finset ℕ) (t : ℕ)
    (cover : ∀ n ≤ t, ∃ a ∈ S, ∃ b ∈ S, a+b=n) :
    let A := S.filter (fun a => a ≤ t)
    let B := A.filter (fun a => t < 2*a)
    t+1 + Nat.choose (B.card+1) 2 ≤ Nat.choose (A.card+1) 2 := by
  classical
  let A := S.filter (fun a => a ≤ t)
  let B := A.filter (fun a => t < 2*a)
  let pairSum : Sym2 ℕ → ℕ := Sym2.lift ⟨Nat.add, Nat.add_comm⟩
  change t+1 + Nat.choose (B.card+1) 2 ≤ Nat.choose (A.card+1) 2
  have incl : Finset.Iic t ⊆ (A.sym2 \ B.sym2).image pairSum := by
    intro n hn
    have hnt := Finset.mem_Iic.mp hn
    obtain ⟨a, ha, b, hb, hab⟩ := cover n hnt
    have ha' : a ∈ A := Finset.mem_filter.mpr ⟨ha, by omega⟩
    have hb' : b ∈ A := Finset.mem_filter.mpr ⟨hb, by omega⟩
    refine Finset.mem_image.mpr ⟨Sym2.mk a b, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mk_mem_sym2_iff.mpr ⟨ha',hb'⟩
    · intro h
      obtain ⟨h₁,h₂⟩ := Finset.mk_mem_sym2_iff.mp h
      have first : t < 2*a := (Finset.mem_filter.mp h₁).2
      have second : t < 2*b := (Finset.mem_filter.mp h₂).2
      omega
    · simpa [pairSum] using hab
  have h := (Finset.card_le_card incl).trans Finset.card_image_le
  rw [Nat.card_Iic] at h
  have hb : B ⊆ A := Finset.filter_subset _ _
  have size := Finset.card_sdiff_add_card_eq_card (Finset.sym2_mono hb)
  rw [Finset.card_sym2, Finset.card_sym2] at size
  omega

end OMA.Erdos28Capacity

namespace OMA.Erdos28Transfer

private theorem two_when_each_pair_uses (A : Set ℕ) (d n : ℕ)
    (uses : ∀ a ∈ A, ∀ b ∈ A, a+b=n → a=d ∨ b=d) :
    AdditiveCombinatorics.sumRep A n ≤ 2 := by
  classical
  rw [AdditiveCombinatorics.sumRep_def]
  refine le_trans ?_ (Finset.card_le_two (a := (d,n-d)) (b := (n-d,d)))
  apply Finset.card_le_card
  rintro ⟨a,b⟩ hp
  obtain ⟨diag,ha,hb⟩ := Finset.mem_filter.mp hp
  have hs : a+b=n := Finset.HasAntidiagonal.mem_antidiagonal.mp diag
  rcases uses a ha b hb hs with h | h
  · have eqb : b=n-d := by omega
    simp [h,eqb]
  · have eqa : a=n-d := by omega
    simp [h,eqa]

/-- For globally bounded finite prefixes which cover through their last element,
a degree bound D yields a local obstruction at 2D+1. -/
theorem obstruction_of_degree_bound (g D : ℕ) (hg : 2 ≤ g)
    (bounds : ∀ (d : ℕ) (T : Finset ℕ), d ∈ T → T ⊆ Finset.Iic d →
      (∀ n ≤ d, ∃ a ∈ T, ∃ b ∈ T, a + b = n) →
      (∀ n, AdditiveCombinatorics.sumRep (T : Set ℕ) n ≤ g) → d ≤ D)
    (S : Finset ℕ) (hS : S ⊆ Finset.Iic (2 * D + 1))
    (covers : ∀ n ≤ 2 * D + 1, ∃ a ∈ S, ∃ b ∈ S, a + b = n) :
    ∃ n ≤ 2 * D + 1, g < AdditiveCombinatorics.sumRep (S : Set ℕ) n := by
  classical
  by_contra! capped
  let U := S.filter (D < ·)
  have hex : U.Nonempty := by
    obtain ⟨a, ha, b, hb, hab⟩ := covers (2 * D + 1) le_rfl
    by_cases high : D < a
    · exact ⟨a, Finset.mem_filter.mpr ⟨ha, high⟩⟩
    · exact ⟨b, Finset.mem_filter.mpr ⟨hb, by omega⟩⟩
  let d := U.min' hex
  have hdU : d ∈ U := U.min'_mem hex
  obtain ⟨hdS, hDd⟩ := Finset.mem_filter.mp hdU
  have hdL := Finset.mem_Iic.mp (hS hdS)
  let T := S.filter (· ≤ d)
  have ht (x : ℕ) (hx : x ∈ T) : x ≤ D ∨ x = d := by
    obtain ⟨hxS, hxd⟩ := Finset.mem_filter.mp hx
    by_cases small : x ≤ D
    · exact Or.inl small
    · have hxU : x ∈ U := Finset.mem_filter.mpr ⟨hxS, by omega⟩
      exact Or.inr (le_antisymm hxd (U.min'_le x hxU))
  have hcov : ∀ n ≤ d, ∃ a ∈ T, ∃ b ∈ T, a + b = n := by
    intro n hn
    obtain ⟨a, ha, b, hb, he⟩ := covers n (le_trans hn hdL)
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, by omega⟩, b, Finset.mem_filter.mpr ⟨hb, by omega⟩, he⟩
  have hglobal (n : ℕ) : AdditiveCombinatorics.sumRep (T : Set ℕ) n ≤ g := by
    by_cases hn : n ≤ 2 * D + 1
    · have sub : (T : Set ℕ) ⊆ (S : Set ℕ) := fun _ hx => (Finset.mem_filter.mp hx).1
      exact (OMA.R_Erdos28_erdos_28_R1.monotone_count sub n).trans (capped n hn)
    · apply le_trans (two_when_each_pair_uses (T : Set ℕ) d n ?_) hg
      intro a ha b hb hsum
      rcases ht a ha with low | same
      · rcases ht b hb with low' | same
        · omega
        · exact Or.inr same
      · exact Or.inl same
  have hbd := bounds d T (Finset.mem_filter.mpr ⟨hdS, le_rfl⟩)
    (fun x hx => Finset.mem_Iic.mpr (Finset.mem_filter.mp hx).2) hcov hglobal
  omega

end OMA.Erdos28Transfer

namespace OMA.R_Erdos28_erdos_28_R1_H1_R1

open AdditiveCombinatorics

/-- The sharp published endpoint for a cap of five ordered pairs. -/
def H1 : Prop := ∀ S : Finset ℕ, S ⊆ Finset.Iic 70 →
  (∀ n ≤ 70, ∃ a ∈ S, ∃ b ∈ S, a+b=n) → ∃ n ≤ 70, 5 < sumRep (S : Set ℕ) n

/-- Increasing the ordered cap by two preserves bounded length for finite
exact bases. Odd caps suffice because they exceed every natural bound in turn. -/
def H2 : Prop :=
  let boundedLength := fun g : ℕ => ∃ K : ℕ, ∀ (d : ℕ) (T : Finset ℕ),
    d ∈ T → T ⊆ Finset.Iic d → (∀ n ≤ d, ∃ a ∈ T, ∃ b ∈ T, a+b=n) →
    (∀ n, sumRep (T : Set ℕ) n ≤ g) → T.card ≤ K
  ∀ r : ℕ, 2 ≤ r → boundedLength (2*r+1) → boundedLength (2*(r+1)+1)

theorem initial_length (base : H1) : ∃ K : ℕ, ∀ (d : ℕ) (T : Finset ℕ),
    d ∈ T → T ⊆ Finset.Iic d → (∀ n ≤ d, ∃ a ∈ T, ∃ b ∈ T, a+b=n) →
    (∀ n, sumRep (T : Set ℕ) n ≤ 5) → T.card ≤ K := by
  classical
  refine ⟨70, ?_⟩
  intro d T _ hTd cover cap
  by_cases hd : d < 70
  · have ht := Finset.card_le_card hTd
    rw [Nat.card_Iic] at ht
    omega
  · let S := T.filter (· ≤ 70)
    have hs : S ⊆ Finset.Iic 70 := fun _ hx => Finset.mem_Iic.mpr (Finset.mem_filter.mp hx).2
    have hc : ∀ n ≤ 70, ∃ a ∈ S, ∃ b ∈ S, a+b=n := by
      intro n hn
      obtain ⟨a,ha,b,hb,hab⟩ := cover n (by omega)
      exact ⟨a,Finset.mem_filter.mpr ⟨ha,by omega⟩,b,Finset.mem_filter.mpr ⟨hb,by omega⟩,hab⟩
    obtain ⟨n,_,hn⟩ := base S hs hc
    have sub : (S : Set ℕ) ⊆ (T : Set ℕ) := fun _ hx => (Finset.mem_filter.mp hx).1
    have mono := OMA.R_Erdos28_erdos_28_R1.monotone_count sub n
    have hbound := cap n
    omega

theorem main : H1 → H2 → OMA.R_Erdos28_erdos_28_R1.H1 := by
  classical
  intro base step g
  let boundedLength := fun c : ℕ => ∃ K : ℕ, ∀ (d : ℕ) (T : Finset ℕ),
    d ∈ T → T ⊆ Finset.Iic d → (∀ n ≤ d, ∃ a ∈ T, ∃ b ∈ T, a+b=n) →
    (∀ n, sumRep (T : Set ℕ) n ≤ c) → T.card ≤ K
  have lengths (t : ℕ) : boundedLength (2*(t+2)+1) := by
    induction t with
    | zero => exact initial_length base
    | succ t ih => exact step (t+2) (by omega) ih
  let G := 2*(g+2)+1
  obtain ⟨K, hK⟩ := lengths g
  let D := Nat.choose (K+1) 2 - 1
  refine ⟨2*D+1, ?_⟩
  intro S hS cov
  have degrees (d : ℕ) (T : Finset ℕ) (hd : d ∈ T) (hT : T ⊆ Finset.Iic d)
      (hc : ∀ n ≤ d, ∃ a ∈ T, ∃ b ∈ T, a+b=n)
      (cap : ∀ n, sumRep (T : Set ℕ) n ≤ G) : d ≤ D := by
    have hk := hK d T hd hT hc cap
    have size := OMA.Erdos28Capacity.prefix_capacity T d hc
    have hfilter : T.filter (fun a => a ≤ d) = T :=
      Finset.filter_true_of_mem (fun a ha => Finset.mem_Iic.mp (hT ha))
    dsimp only at size
    rw [hfilter] at size
    have hchoose : Nat.choose (T.card+1) 2 ≤ Nat.choose (K+1) 2 :=
      Nat.choose_le_choose 2 (by omega)
    dsimp [D]
    omega
  obtain ⟨n, hn, hbig⟩ := OMA.Erdos28Transfer.obstruction_of_degree_bound G D
    (by dsimp [G]; omega) degrees S hS cov
  exact ⟨n, hn, by dsimp [G] at hbig; omega⟩

end OMA.R_Erdos28_erdos_28_R1_H1_R1
