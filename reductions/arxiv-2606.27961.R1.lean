import OMAStatements.S_arxiv_2606_27961

namespace OMA.R_arxiv_2606_27961_R1

open OMA.S_arxiv_2606_27961
open scoped Pointwise BigOperators

/-- Sections having independent two-point directions, as in Lemma 6.4. -/
def H1 : Prop := ∀ (p : ℕ) [NeZero p], p.Prime → Odd p →
    ∀ s : Plane p → Plane (p^2), Function.RightInverse s (reduce p) →
    let c := fun u => (Set.range (fun x : Plane p => s (x+u) - s x)).ncard
    (∃ u v : Plane p, u.1*v.2 ≠ u.2*v.1 ∧ c u = 2 ∧ c v = 2) →
    (2*p-1)^2 ≤ ∑ u, c u

/-- In the complementary case, compare the losses below four with
    the surpluses above four, ignoring the zero direction. -/
def H2 : Prop := ∀ (p : ℕ) [NeZero p], p.Prime → Odd p →
    ∀ s : Plane p → Plane (p^2), Function.RightInverse s (reduce p) →
    let c := fun u => (Set.range (fun x : Plane p => s (x+u) - s x)).ncard
    (∀ u v : Plane p, c u = 2 → c v = 2 → u.1*v.2 = u.2*v.1) →
    (∑ u ∈ Finset.univ.erase 0, (4 - c u)) ≤
      4*(p-1) + ∑ u ∈ Finset.univ.erase 0, (c u - 4)

lemma box (p : ℕ) [NeZero p] (hp : 2 ≤ p) :
    ∃ T : Set (Plane (p^2)), Set.BijOn (reduce p) T Set.univ ∧
      (T-T).ncard = (2*p-1)^2 := by
  classical
  let lift (x : ZMod p) : ZMod (p^2) := x.val
  let A := Set.range lift
  have hpp : p ≤ p^2 := by nlinarith
  have hw : 2*p-1 ≤ p^2 := by
    have : 2*p ≤ p^2 := by nlinarith
    omega
  have inv (x : ZMod p) : ((lift x).val : ZMod p) = x := by
    dsimp [lift]
    rw [ZMod.val_natCast_of_lt (x.val_lt.trans_le hpp), ZMod.natCast_zmod_val]
  have hb : Set.BijOn (fun z : ZMod (p^2) => (z.val : ZMod p)) A Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ he
      exact congrArg lift ((inv x).symm.trans (he.trans (inv y)))
    · intro y _
      exact ⟨lift y, ⟨y, rfl⟩, inv y⟩
  refine ⟨A ×ˢ A, ?_, ?_⟩
  · unfold OMA.S_arxiv_2606_27961.reduce
    simpa only [Prod.map, Set.univ_prod_univ] using hb.prodMap hb
  have hm (i : ℕ) (hi : i < p) : (i : ZMod (p^2)) ∈ A :=
    ⟨(i : ZMod p), by dsimp only [lift]; rw [ZMod.val_natCast_of_lt hi]⟩
  let shift (i : ℕ) : ZMod (p^2) := (i : ZMod (p^2)) - ((p-1 : ℕ) : ZMod (p^2))
  let I := Finset.range (2*p-1)
  have repr : A-A = shift '' (I : Set ℕ) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩
      have hx := x.val_lt
      have hy := y.val_lt
      let k := x.val + (p-1-y.val)
      have hsum : k+y.val = x.val+(p-1) := by dsimp [k]; omega
      refine ⟨k, Finset.mem_range.mpr (by dsimp [k]; omega), ?_⟩
      have hh := congrArg (fun n : ℕ => (n : ZMod (p^2))) hsum
      push_cast at hh
      dsimp [shift,lift]
      linear_combination hh
    · rintro ⟨i, hi, rfl⟩
      have hi' := Finset.mem_range.mp hi
      by_cases h : i < p
      · exact ⟨_, hm i h, _, hm (p-1) (by omega), rfl⟩
      · have hd : i-(p-1) < p := by omega
        refine ⟨_, hm _ hd, _, hm 0 (by omega), ?_⟩
        simp [shift, Nat.cast_sub (show p-1 ≤ i by omega)]
  have inj : Set.InjOn shift (I : Set ℕ) := by
    intro i hi j hj he
    have hh : (i : ZMod (p^2)) = j := by simpa only [shift, sub_left_inj] using he
    have := congrArg ZMod.val hh
    rwa [ZMod.val_natCast_of_lt ((Finset.mem_range.mp hi).trans_le hw),
      ZMod.val_natCast_of_lt ((Finset.mem_range.mp hj).trans_le hw)] at this
  rw [Set.prod_sub_prod_comm, Set.ncard_prod, repr, inj.ncard_image, Set.ncard_coe_finset]
  simp [I,pow_two]

lemma reduce_sub (p : ℕ) [NeZero p] (a b : Plane (p^2)) :
    reduce p (a-b) = reduce p a - reduce p b := by
  have hd : p ∣ p^2 := by simp [pow_two]
  unfold OMA.S_arxiv_2606_27961.reduce
  apply Prod.ext
  · exact (by simpa only [Prod.fst_sub, Prod.snd_sub, ZMod.cast_eq_val] using
      (ZMod.cast_sub (R := ZMod p) hd a.1 b.1))
  · exact (by simpa only [Prod.fst_sub, Prod.snd_sub, ZMod.cast_eq_val] using
      (ZMod.cast_sub (R := ZMod p) hd a.2 b.2))

lemma fiber_count (p : ℕ) [NeZero p] (s : Plane p → Plane (p^2))
    (hs : Function.RightInverse s (reduce p)) :
    (Set.range s - Set.range s).ncard =
      ∑ u, (Set.range (fun x : Plane p => s (x+u) - s x)).ncard := by
  classical
  let D := (Set.range s - Set.range s).toFinset
  have hf (u : Plane p) : D.filter (fun t => reduce p t = u) =
      (Set.range (fun x : Plane p => s (x+u) - s x)).toFinset := by
    ext t
    simp only [Finset.mem_filter, D, Set.mem_toFinset, Set.mem_range, Set.mem_sub]
    constructor
    · rintro ⟨⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩, he⟩
      rw [reduce_sub, hs a, hs b] at he
      exact ⟨b, by rw [← he]; abel_nf⟩
    · rintro ⟨x, rfl⟩
      refine ⟨⟨_, ⟨x+u, rfl⟩, _, ⟨x, rfl⟩, rfl⟩, ?_⟩
      rw [reduce_sub, hs _, hs _]
      abel
  have h := Finset.card_eq_sum_card_fiberwise (f := reduce p) (s := D)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  simpa only [hf, D, ← Set.ncard_eq_toFinset_card'] using h

lemma compensation (p : ℕ) [NeZero p] (hp : 2 ≤ p) (c : Plane p → ℕ) (hz : c 0 = 1)
    (h : (∑ u ∈ Finset.univ.erase 0, (4 - c u)) ≤
      4*(p-1) + ∑ u ∈ Finset.univ.erase 0, (c u - 4)) :
    (2*p-1)^2 ≤ ∑ u, c u := by
  classical
  let U := (Finset.univ : Finset (Plane p)).erase 0
  have bal : (∑ u ∈ U, c u) + (∑ u ∈ U, (4-c u)) =
      (∑ _u ∈ U, (4 : ℕ)) + ∑ u ∈ U, (c u-4) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => by omega)
  have hcard : U.card = p*p-1 := by simp [U,Plane,Fintype.card_prod,ZMod.card]
  have tot := Finset.sum_erase_add (Finset.univ : Finset (Plane p)) c (Finset.mem_univ 0)
  change (∑ u ∈ U, c u) + c 0 = _ at tot
  change (∑ u ∈ U, (4-c u)) ≤ 4*(p-1) + ∑ u ∈ U, (c u-4) at h
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at bal
  have pp : 1 ≤ p*p := by nlinarith
  have sq : (2*p-1)^2 + 4*(p-1) = (p*p-1)*4 + 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
    simp only [Nat.mul_add]
    have e : 2*2+2*k-1 = 3+2*k := by omega
    have f : 2+k-1 = 1+k := by omega
    have g : (2+k)*2+(2+k)*k-1 = 3+4*k+k*k := by
      have := Nat.zero_le (k*k)
      nlinarith [Nat.sub_add_cancel (show 1 ≤ (2+k)*2+(2+k)*k by omega)]
    rw [e,f,g]
    ring
  rw [hz] at tot
  change (∑ u ∈ U, c u) + (∑ u ∈ U, (4-c u)) =
    (p*p-1)*4 + ∑ u ∈ U, (c u-4) at bal
  have bound : (2*p-1)^2 + 4*(p-1) ≤ (∑ u, c u) + 4*(p-1) := by
    rw [sq, ← tot]
    omega
  exact Nat.le_of_add_le_add_right bound

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2606_27961.main := by
  intro known residual p hp ho
  classical
  let _ : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨box p hp.two_le, ?_⟩
  rintro _ ⟨T, hT, rfl⟩
  have allLift (x : Plane p) : ∃ t ∈ T, reduce p t = x := hT.surjOn (Set.mem_univ x)
  choose s hmem hs using allLift
  have hT' : T = Set.range s := by
    ext t
    constructor
    · intro ht
      exact ⟨reduce p t, hT.injOn (hmem _) ht (hs _)⟩
    · rintro ⟨x, rfl⟩
      exact hmem x
  rw [hT', fiber_count p s hs]
  let c (u : Plane p) := (Set.range (fun x : Plane p => s (x+u) - s x)).ncard
  change (2*p-1)^2 ≤ ∑ u, c u
  by_cases hex : ∃ u v : Plane p, u.1*v.2 ≠ u.2*v.1 ∧ c u = 2 ∧ c v = 2
  · exact known p hp ho s hs hex
  · have line (u v : Plane p) (hu : c u = 2) (hv : c v = 2) : u.1*v.2 = u.2*v.1 := by
      by_contra h
      exact hex ⟨u,v,h,hu,hv⟩
    apply compensation p hp.two_le c _ (residual p hp ho s hs line)
    simp [c]

end OMA.R_arxiv_2606_27961_R1

