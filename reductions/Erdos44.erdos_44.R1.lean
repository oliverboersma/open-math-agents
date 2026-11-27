import FormalConjectures.ErdosProblems.«44»

-- Credit: @marcusbuffett
-- Adapted from @ldy985's Ruzsa construction in this repository at
-- e8a0e64a4a00af42527fb800a06bebb557aa3156. The affine coefficients below
-- interpolate two prescribed starting points; the remaining prefix may be deleted.

namespace OMA.R_Erdos44_erdos_44_R1
open Finset

private theorem anchored_ruzsa (q x y : ℕ) (hp : (q+1).Prime)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hxq : x ≤ q) (hyq : y ≤ q) (hxy : x ≠ y) :
    ∃ S : Finset ℕ, S ⊆ Icc 1 ((q+1)*q) ∧ IsSidon (S : Set ℕ) ∧ S.card=q ∧ x∈S ∧ y∈S := by
  have : Fact (q + 1).Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ : ∃ g : (ZMod (q + 1))ˣ, orderOf g = q := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (q + 1))ˣ)
    refine ⟨g, ?_⟩
    rw [hg, Nat.card_eq_fintype_card, ZMod.card_units (q + 1)]
    simp
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ZMod (q + 1), ∀ i, u i = ((g ^ i : (ZMod (q + 1))ˣ) : ZMod (q + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hu_inj : ∀ a b, a < q → b < q → u a = u b → a = b := by
    intro a b ha hb hab
    rw [hu, hu] at hab
    have h1 : g ^ a = g ^ b := Units.ext hab
    have h2 : a ≡ b [MOD orderOf g] := pow_eq_pow_iff_modEq.1 h1
    rw [hg] at h2
    exact Nat.ModEq.eq_of_lt_of_lt h2 ha hb
  let a := x-1
  let b := y-1
  have ha : a < q := by dsimp [a]; omega
  have hb : b < q := by dsimp [b]; omega
  have hex : a+1=x := by dsimp [a]; omega
  have hey : b+1=y := by dsimp [b]; omega
  have hne : u a ≠ u b := fun h => hxy (by have := hu_inj a b ha hb h; omega)
  have hres : (x : ZMod (q+1)) ≠ (y : ZMod (q+1)) := by
    intro h
    have := congrArg ZMod.val h
    apply hxy
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : x<q+1),
      Nat.mod_eq_of_lt (by omega : y<q+1)] using this
  let D : ZMod (q+1) := (x-y : ZMod (q+1)) / (u a-u b)
  let C : ZMod (q+1) := x - D * u a
  let v (i : ℕ) := C+D*u i
  have hD : D ≠ 0 := div_ne_zero (sub_ne_zero.mpr hres) (sub_ne_zero.mpr hne)
  have hva : v a = x := by dsimp only [v,C]; ring
  have hvb : v b = y := by
    have h := div_mul_cancel₀ ((x:ZMod (q+1))-y) (sub_ne_zero.mpr hne)
    change D * (u a-u b) = x-y at h
    dsimp only [v,C]
    linear_combination -h
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ℕ, ∀ i, k i = (1+i + (q + 1) - (v i).val) % (q + 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = 1 + i + q * k i := ⟨_, fun _ => rfl⟩
  have hk_lt : ∀ i, k i < q + 1 := fun i => by
    rw [hk]
    exact Nat.mod_lt _ (Nat.succ_pos q)
  have hqcast : ((q : ℕ) : ZMod (q + 1)) = -1 := by
    have h0 : ((q + 1 : ℕ) : ZMod (q + 1)) = 0 := ZMod.natCast_self (q + 1)
    push_cast at h0
    linear_combination h0
  have hkcast : ∀ i, ((k i : ℕ) : ZMod (q + 1)) = 1+(i : ZMod (q + 1)) - v i := by
    intro i
    have hval : (v i).val ≤ 1+i + (q + 1) := (ZMod.val_lt (v i)).le.trans (Nat.le_add_left _ _)
    have h0 : ((q + 1 : ℕ) : ZMod (q + 1)) = 0 := ZMod.natCast_self (q + 1)
    rw [hk, ZMod.natCast_mod, Nat.cast_sub hval, Nat.cast_add, h0, ZMod.natCast_zmod_val]
    push_cast
    ring
  have hfcast : ∀ i, ((f i : ℕ) : ZMod (q + 1)) = v i := by
    intro i
    rw [hf]
    push_cast
    rw [hqcast, hkcast]
    ring
  have hf_mod : ∀ i, f i % q = (1 + i) % q := by
    intro i
    rw [hf]
    exact Nat.add_mul_mod_self_left _ _ _
  have hit (j z : ℕ) (hj : j<q) (hz : z<q+1) (he : j+1=z) (hv : v j=z) :
      z ∈ (Finset.range q).image f := by
    refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, ?_⟩
    have hval : (v j).val=z := by rw [hv,ZMod.val_natCast,Nat.mod_eq_of_lt hz]
    rw [hf,hk,hval,show 1+j+(q+1)-z=q+1 by omega,Nat.mod_self]
    omega
  refine ⟨(Finset.range q).image f, ?_, ?_, ?_, hit a x ha (by omega) hex hva,
    hit b y hb (by omega) hey hvb⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    have hi' := Finset.mem_range.1 hi
    have hki := hk_lt i
    rw [Finset.mem_Icc, hf]
    refine ⟨by omega, ?_⟩
    have h1 : q * k i ≤ q * q := Nat.mul_le_mul_left q (by omega)
    have h2 : (q + 1) * q = q * q + q := by ring
    omega
  · intro x hx y hy z hz w hw hsum
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw)
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    have hc' := Finset.mem_range.1 hc
    have hd' := Finset.mem_range.1 hd
    -- the sum of the exponents is determined modulo q
    have hmod : a + c ≡ b + d [MOD q] := by
      have e : a + c + q * (k a + k c + 0) + 2 = b + d + q * (k b + k d + 0) + 2 := by
        have := hsum
        rw [hf a, hf b, hf c, hf d] at this
        simp only [Nat.mul_add, Nat.add_zero]
        omega
      have e' : a + c + q * (k a + k c + 0) = b + d + q * (k b + k d + 0) := by omega
      have e2 := congrArg (· % q) e'
      simp only [Nat.add_mul_mod_self_left] at e2
      exact e2
    have hgpow : g ^ (a + c) = g ^ (b + d) := pow_eq_pow_iff_modEq.2 (by rw [hg]; exact hmod)
    have hprod : u a * u c = u b * u d := by
      rw [hu, hu, hu, hu, ← Units.val_mul, ← Units.val_mul, ← pow_add, ← pow_add, hgpow]
    have hadd : u a + u c = u b + u d := by
      have e := congrArg (Nat.cast : ℕ → ZMod (q + 1)) hsum
      rw [Nat.cast_add, Nat.cast_add, hfcast, hfcast, hfcast, hfcast] at e
      apply mul_left_cancel₀ hD
      dsimp only [v] at e
      linear_combination e
    have hzero : (u a - u b) * (u a - u d) = 0 := by
      linear_combination (u a) * hadd - hprod
    rcases mul_eq_zero.1 hzero with h | h
    · have hab : a = b := hu_inj a b ha' hb' (sub_eq_zero.1 h)
      have hcd : c = d := by
        apply hu_inj c d hc' hd'
        rw [hab] at hadd
        exact add_left_cancel hadd
      exact Or.inl ⟨by rw [hab], by rw [hcd]⟩
    · have had : a = d := hu_inj a d ha' hd' (sub_eq_zero.1 h)
      have hcb : c = b := by
        apply hu_inj c b hc' hb'
        rw [had] at hadd
        have : u d + u c = u d + u b := by rw [hadd]; ring
        exact add_left_cancel this
      exact Or.inr ⟨by rw [had], by rw [hcb]⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hi' : i < q := Finset.mem_range.1 (Finset.mem_coe.1 hi)
    have hj' : j < q := Finset.mem_range.1 (Finset.mem_coe.1 hj)
    have h1 : (1 + i) % q = (1 + j) % q := by rw [← hf_mod, ← hf_mod, hij]
    have h2 : (1 + i) ≡ (1 + j) [MOD q] := h1
    have h3 : i ≡ j [MOD q] := Nat.ModEq.add_left_cancel' 1 h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 hi' hj'

/-- Almost maximal Sidon sets containing the prescribed points, at arbitrarily
large cutoffs. Extra points below the original cutoff are permitted. -/
private def Embedded (A : Finset ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ L : ℕ, ∃ M ≥ L, ∃ S : Finset ℕ,
    S ⊆ Icc 1 M ∧ A ⊆ S ∧ IsSidon (S : Set ℕ) ∧ (1-δ)*Real.sqrt M ≤ S.card

private lemma seed_pair {A : Finset ℕ} {N : ℕ} (hs : A ⊆ Icc 1 N) (hc : A.card ≤ 2) :
    ∃ x y : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ x ≤ N+2 ∧ y ≤ N+2 ∧ x ≠ y ∧ A ⊆ {x,y} := by
  rcases lt_or_eq_of_le hc with ht | ht
  · by_cases hz : A = ∅
    · subst A
      exact ⟨1,2,by omega,by omega,by omega,by omega,by omega,by simp⟩
    · have hc₁ : A.card = 1 := by
        have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
        omega
      obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp hc₁
      have hx := Finset.mem_Icc.mp (hs (Finset.mem_singleton_self x))
      exact ⟨x,N+1,hx.1,by omega,by omega,by omega,by omega,by simp⟩
  · obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp ht
    have hx := Finset.mem_Icc.mp (hs (by simp : x ∈ ({x,y} : Finset ℕ)))
    have hy := Finset.mem_Icc.mp (hs (by simp : y ∈ ({x,y} : Finset ℕ)))
    exact ⟨x,y,hx.1,hy.1,by omega,by omega,hxy,Subset.rfl⟩

private theorem pair_embedded {A : Finset ℕ} {N : ℕ} (hs : A ⊆ Icc 1 N) (hc : A.card ≤ 2) :
    Embedded A := by
  obtain ⟨x,y,hx,hy,hxN,hyN,hxy,hA⟩ := seed_pair hs hc
  intro δ hδ L
  obtain ⟨K,hK⟩ := exists_nat_gt (1/δ)
  obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes (K+N+L+4)
  obtain ⟨q,rfl⟩ : ∃ q, p=q+1 := ⟨p-1,by omega⟩
  obtain ⟨S,hsub,hsid,hcard,hX,hY⟩ := anchored_ruzsa q x y hprime hx hy (by omega) (by omega) hxy
  have hq : 1 ≤ q := by omega
  have hbig : q ≤ (q+1)*q := Nat.le_mul_of_pos_left q (by omega)
  refine ⟨(q+1)*q,by omega,S,hsub,?_,hsid,?_⟩
  · intro z hz
    rcases Finset.mem_insert.mp (hA hz) with rfl | hz'
    · exact hX
    · rwa [Finset.mem_singleton.mp hz']
  · rw [hcard]
    have hroot : Real.sqrt ((q+1)*q : ℕ) ≤ (q+1:ℕ) := by
      apply (Real.sqrt_le_iff).2
      push_cast
      constructor <;> nlinarith
    by_cases hd : 1 ≤ δ
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)).trans (by positivity)
    have hbound : 1 ≤ δ*(q+1 : ℕ) := by
      have hle : 1/δ ≤ (q+1:ℕ) := hK.le.trans (by exact_mod_cast (by omega : K ≤ q+1))
      exact (div_le_iff₀ hδ).mp hle |> fun h => by simpa [mul_comm] using h
    have h := mul_le_mul_of_nonneg_left hroot (by linarith : 0 ≤ 1-δ)
    push_cast at h hbound ⊢
    linarith

private lemma absorb_loss (c : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ M ≥ K, ∀ x y : ℕ, (1-ε/2)*Real.sqrt M ≤ x → x ≤ y+c →
      (1-ε)*Real.sqrt M ≤ y := by
  obtain ⟨j,hj⟩ := exists_nat_gt ((c:ℝ)/(ε/2))
  refine ⟨j^2,?_⟩
  intro M hM x y hsize hc
  have hroot : (j:ℝ) ≤ Real.sqrt M := (Real.le_sqrt (by positivity) (by positivity)).2
    (by exact_mod_cast hM)
  have hscale := (div_lt_iff₀ (by positivity : 0<ε/2)).mp hj
  have hterm := mul_le_mul_of_nonneg_right hroot (le_of_lt (by positivity : 0<ε/2))
  have hcard : (x:ℝ) ≤ (y:ℝ)+c := by exact_mod_cast hc
  nlinarith

/-- Three prescribed points in arbitrarily large near-extremal Sidon sets. -/
def H1 : Prop := ∀ A : Finset ℕ, 0 ∉ A → IsSidon (A : Set ℕ) → A.card = 3 → Embedded A

/-- One-point extension beyond a realizable seed of size at least three.
Only the mixed equation t+a=b+c has to be excluded. -/
def H2 : Prop := ∀ (A : Finset ℕ) (t : ℕ), 0 ∉ A → 3 ≤ A.card →
  (∀ a ∈ A, a < t) → IsSidon ((insert t A : Finset ℕ) : Set ℕ) → Embedded A →
  ∀ δ : ℝ, 0 < δ → ∀ L : ℕ, ∃ M ≥ L, ∃ S : Finset ℕ,
    S ⊆ Icc 1 M ∧ A ⊆ S ∧ IsSidon (S : Set ℕ) ∧ (1-δ)*Real.sqrt M ≤ S.card ∧
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, t+a ≠ b+c

theorem extend (h₂ : H2) {A : Finset ℕ} {t : ℕ} (ht : 1≤t)
    (hz : 0 ∉ A) (h₃ : 3≤A.card) (hlt : ∀ a ∈ A, a<t)
    (hins : IsSidon ((insert t A : Finset ℕ) : Set ℕ)) (hold : Embedded A) :
    Embedded (insert t A) := by
  classical
  intro ε hε L
  obtain ⟨K,hK⟩ := absorb_loss (2*t+1) hε
  obtain ⟨M,hM,S,hS,hAS,hSid,hsize,hmix⟩ :=
    h₂ A t hz h₃ hlt hins hold (ε/2) (by positivity) (K+L+t)
  let U := A ∪ (S \ range (2*t+1))
  have hUS : U ⊆ S := Finset.union_subset hAS Finset.sdiff_subset
  have hAu : A ⊆ U := Finset.subset_union_left
  have hSidU : IsSidon (U : Set ℕ) := Set.IsSidon.subset hSid hUS
  have htA : t ∉ A := fun h => (hlt t h).false
  have hpair (a b : ℕ) (ha : a ∈ U) (hb : b ∈ U) : t+t ≠ a+b := by
    intro h
    have keep (x : ℕ) (hx : x ∈ U) (hle : x≤2*t) : x∈A := by
      rcases Finset.mem_union.mp hx with h | hh
      · exact h
      · exact ((Finset.mem_sdiff.mp hh).2 (Finset.mem_range.mpr (by omega))).elim
    have ha' := keep a ha (by omega)
    have hb' := keep b hb (by omega)
    rcases hins t (by simp) a (by simp [ha']) t (by simp) b (by simp [hb']) h with h | h
    · exact htA (h.1.symm ▸ ha')
    · exact htA (h.1.symm ▸ hb')
  have hinsU : IsSidon ((insert t U : Finset ℕ) : Set ℕ) := by
    rw [Finset.coe_insert, ← Set.union_singleton]
    apply (Set.IsSidon.insert hSidU).2
    exact Or.inr fun a ha b hb => ⟨hpair a b ha hb,fun c hc => hmix a (hUS ha) b (hUS hb) c (hUS hc)⟩
  refine ⟨M,by omega,insert t U,?_,Finset.insert_subset_insert _ hAu,hinsU,?_⟩
  · exact Finset.insert_subset (Finset.mem_Icc.mpr ⟨ht,by omega⟩) (hUS.trans hS)
  · have hI : (S ∩ range (2*t+1)).card ≤ 2*t+1 := by
      simpa using Finset.card_le_card (Finset.inter_subset_right (s₁:=S) (s₂:=range (2*t+1)))
    have hB := Finset.card_sdiff_add_card_inter S (range (2*t+1))
    have hsub : S \ range (2*t+1) ⊆ insert t U :=
      (Finset.subset_union_right (s₁:=A) (s₂:=S \ range (2*t+1))).trans (Finset.subset_insert _ _)
    have hcard := Finset.card_le_card hsub
    exact hK M (by omega) _ _ hsize (by omega)

theorem main : H1 → H2 → type_of% @Erdos44.erdos_44 := by
  intro h₃ h₄ N hN A hA hSid ε hε
  have build (m : ℕ) : ∀ T : Finset ℕ, T.card=m → T ⊆ A → Embedded T := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro T hm hTA
      have hT := hTA.trans hA
      have hz : 0 ∉ T := fun h => by have := (Finset.mem_Icc.mp (hT h)).1; omega
      have hsT := Set.IsSidon.subset hSid (show (T : Set ℕ) ⊆ A from hTA)
      by_cases hp : T.card ≤ 2
      · exact pair_embedded hT hp
      by_cases hthree : T.card=3
      · exact h₃ T hz hsT hthree
      have hne : T.Nonempty := Finset.card_pos.mp (by omega)
      let t := T.max' hne
      have ht : t ∈ T := Finset.max'_mem _ _
      have her := Finset.card_erase_of_mem ht
      have hold := ih (T.erase t).card (by omega) (T.erase t) rfl (Finset.erase_subset _ _ |>.trans hTA)
      have heq : insert t (T.erase t) = T := Finset.insert_erase ht
      rw [← heq]
      apply extend h₄ (Finset.mem_Icc.mp (hT ht)).1 (fun h => hz (Finset.mem_of_mem_erase h))
        (by omega) _ (heq.symm ▸ hsT) hold
      intro a ha
      exact lt_of_le_of_ne (Finset.le_max' T a (Finset.mem_of_mem_erase ha)) (Finset.ne_of_mem_erase ha)
  obtain ⟨K,hK⟩ := absorb_loss N hε
  obtain ⟨M,hM,S,hS,hAS,hSidS,hSz⟩ := build A.card A rfl Subset.rfl (ε/2) (by positivity) (K+N+1)
  let B := S \ Icc 1 N
  refine ⟨M,by omega,B,?_,?_,?_⟩
  · intro x hx
    obtain ⟨hs,hn⟩ := Finset.mem_sdiff.mp hx
    have hh := Finset.mem_Icc.mp (hS hs)
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · apply Set.IsSidon.subset hSidS
    intro x hx
    rcases hx with h | h
    · exact hAS h
    · exact (Finset.mem_sdiff.mp h).1
  · have hI : (S ∩ Icc 1 N).card ≤ N := by
      simpa using Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := Icc 1 N))
    have hB := Finset.card_sdiff_add_card_inter S (Icc 1 N)
    have hU := Finset.card_le_card (Finset.subset_union_right (s₁ := A) (s₂ := B))
    apply hK M (by omega) _ _ hSz
    change (S \ Icc 1 N).card ≤ (A ∪ B).card at hU
    omega

end OMA.R_Erdos44_erdos_44_R1
