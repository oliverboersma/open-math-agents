import FormalConjectures.ErdosProblems.«1199»

-- Credit: @senamakel
import Mathlib

/-
Adapted from github.com/hongjin-he/erdos-lean (commit efede9693a3192e324bc092e5510f16a2aff1804), (c) 2026 HongJin HE, Apache-2.0.
Licensed under the Apache License, Version 2.0; see http://www.apache.org/licenses/LICENSE-2.0.
Mathematics: Huang, Lian, Shao, Xiao, Xu, Zhang, arXiv 2607.17333. Modified: namespaces renamed, Lean/Mathlib drift fixes, statement reshaped to the target.
-/




namespace OMA.Port3

open Filter

/-- Mathlib only provides the additive semigroup structure on `Ultrafilter M` as a local
instance (in `Mathlib/Combinatorics/Hindman.lean`); we make it a global instance for `βℕ`. -/
noncomputable instance instAddSemigroupUltrafilterNat : AddSemigroup (Ultrafilter ℕ) :=
  Ultrafilter.addSemigroup

/-- A nonprincipal ultrafilter on `ℕ` (an element of `ℕ* = βℕ \ ℕ`). -/
def Nonprincipal (p : Ultrafilter ℕ) : Prop := (p : Filter ℕ) ≤ Filter.cofinite

/-- `D p`: the image of `p` under `n ↦ 2n`, so `A ∈ dbl p ↔ {n | 2n ∈ A} ∈ p`. -/
noncomputable def dbl (p : Ultrafilter ℕ) : Ultrafilter ℕ := p.map (fun n => 2 * n)

/-- Coordinates: `(k, R)` encodes the affine map `n ↦ (k+1) n + R`. -/
abbrev Idx : Type := ℕ × ℤ

/-- Points of the symbolic space `2^Idx`. -/
abbrev Pt : Type := Idx → Bool

/-- The stride `k + 1` of the coordinate `(k, R)`. -/
def stride (i : Idx) : ℤ := (i.1 : ℤ) + 1

open Classical in
/-- The `βℕ`-action `p · x = p-lim_n Tⁿ x`, where `(Tⁿ x)(k, R) = x(k, R + (k+1) n)`. -/
noncomputable def act (p : Ultrafilter ℕ) (x : Pt) : Pt :=
  fun i => decide ({n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true} ∈ p)

/-- Colour complementation `J` (a fixed-point-free involution commuting with the action). -/
def cmpl (x : Pt) : Pt := fun i => !(x i)

/-- The dilation `Δ₂`: `(Δ₂ x)(k, R) = x(2k+1, R)` (stride `k+1 ↦ 2(k+1)`). -/
def dil (x : Pt) : Pt := fun i => x (2 * i.1 + 1, i.2)

/-- The encoded point `𝐜` of a colouring `c : ℤ → Bool`: `𝐜(k, R) = c(R)`, so that
`(Tⁿ 𝐜)(k, R) = c((k+1) n + R)`. -/
def encode (c : ℤ → Bool) : Pt := fun i => c i.2

/-- `c(z) = b(2z)` for `z ≥ 0` (and `b 0` for `z < 0`, an arbitrary choice). -/
def ext2 (b : ℕ → Bool) : ℤ → Bool := fun z => b (2 * z.toNat)

/-- `B + B` (including the doubles `2x`) is monochromatic for the colouring `col`. -/
def IsMonoSumset (col : ℕ → Bool) (B : Set ℕ) : Prop :=
  ∃ γ : Bool, ∀ x ∈ B, ∀ y ∈ B, col (x + y) = γ

/-- The Owings property for `b`: an infinite set of positive integers `B` with `B + B`
monochromatic. -/
def Owings (b : ℕ → Bool) : Prop :=
  ∃ B : Set ℕ, B.Infinite ∧ (∀ x ∈ B, 0 < x) ∧ IsMonoSumset b B

/-- `ω(x) = {p · x : p ∈ ℕ*}` (the omega-limit set, via Lemma 2.8 of the paper). -/
def Omega (x : Pt) : Set Pt := {y | ∃ p : Ultrafilter ℕ, Nonprincipal p ∧ act p x = y}

/-- `M` is a minimal subsystem of `ω(x)`, in the form used in the proof:
nonempty, closed, contained in `ω(x)`, invariant under the `βℕ`-action, and every point of `M`
reaches every other point of `M` under the action. -/
def IsMinimalSub (x : Pt) (M : Set Pt) : Prop :=
  M.Nonempty ∧ IsClosed M ∧ M ⊆ Omega x ∧
    (∀ p : Ultrafilter ℕ, ∀ y ∈ M, act p y ∈ M) ∧
    (∀ y ∈ M, ∀ z ∈ M, ∃ q : Ultrafilter ℕ, act q y = z)

end OMA.Port3




namespace OMA.Port3

open Filter

/-- Membership in a sum of ultrafilters (paper eq. (2.1)). -/
theorem mem_add_iff (A : Set ℕ) (p q : Ultrafilter ℕ) :
    A ∈ p + q ↔ {m : ℕ | {m' : ℕ | m + m' ∈ A} ∈ q} ∈ p := by
  exact Iff.rfl

/-- Membership in `D p` (paper eq. (2.4)). -/
theorem mem_dbl_iff (A : Set ℕ) (p : Ultrafilter ℕ) :
    A ∈ dbl p ↔ {n : ℕ | 2 * n ∈ A} ∈ p := by
  exact Iff.rfl

/-- `βℕ` is a right-topological semigroup: `p ↦ p + q` is continuous. -/
theorem continuous_add_const (q : Ultrafilter ℕ) :
    Continuous (fun p : Ultrafilter ℕ => p + q) := by
  exact Ultrafilter.continuous_add_left q

/-- Lemma 2.7(ii), first half: `p + q ∈ ℕ*` whenever `q ∈ ℕ*`. -/
theorem nonprincipal_add {p q : Ultrafilter ℕ} (hq : Nonprincipal q) :
    Nonprincipal (p + q) := by
  intro S hS
  have hS' : Sᶜ.Finite := hS
  show S ∈ (p + q)
  rw [mem_add_iff]
  refine Filter.mem_of_superset Filter.univ_mem fun m _ => ?_
  apply hq
  show {m' : ℕ | m + m' ∈ S}ᶜ.Finite
  refine (hS'.preimage (f := fun m' => m + m') (fun a _ b _ h => by simpa using h)).subset ?_
  intro m' hm'
  exact hm'

/-- Lemma 2.7(ii), second half: `D p ∈ ℕ*` whenever `p ∈ ℕ*`. -/
theorem nonprincipal_dbl {p : Ultrafilter ℕ} (hp : Nonprincipal p) :
    Nonprincipal (dbl p) := by
  unfold Nonprincipal dbl
  rw [Ultrafilter.coe_map]
  exact (Filter.map_mono hp).trans
    (Function.Injective.tendsto_cofinite (fun a b h => by simpa using h))

/-- `ℕ*` is closed in `βℕ`. -/
theorem isClosed_nonprincipal : IsClosed {p : Ultrafilter ℕ | Nonprincipal p} := by
  have : {p : Ultrafilter ℕ | Nonprincipal p} = ⋂ x : ℕ, {p : Ultrafilter ℕ | {x}ᶜ ∈ p} := by
    ext p
    simp only [Set.mem_iInter]
    exact Filter.le_cofinite_iff_compl_singleton_mem
  rw [this]
  exact isClosed_iInter fun x => ultrafilter_isClosed_basic _

/-- Every infinite set belongs to some nonprincipal ultrafilter. -/
theorem exists_nonprincipal_mem {B : Set ℕ} (hB : B.Infinite) :
    ∃ p : Ultrafilter ℕ, Nonprincipal p ∧ B ∈ p := by
  have : (Filter.cofinite ⊓ Filter.principal B).NeBot :=
    Filter.frequently_mem_iff_neBot.mp hB.frequently_cofinite
  refine ⟨Ultrafilter.of (Filter.cofinite ⊓ Filter.principal B), ?_, ?_⟩
  · exact (Ultrafilter.of_le _).trans inf_le_left
  · exact Ultrafilter.of_le _ (Filter.mem_inf_of_right (Filter.mem_principal_self B))

/-- A set in a nonprincipal ultrafilter has elements beyond every bound. -/
theorem Nonprincipal.exists_ge {p : Ultrafilter ℕ} (hp : Nonprincipal p) {S : Set ℕ}
    (hS : S ∈ p) (N : ℕ) : ∃ n ∈ S, N ≤ n := by
  have hN : {n : ℕ | N ≤ n} ∈ p := hp (by
    show {n : ℕ | N ≤ n}ᶜ.Finite
    exact (Set.finite_lt_nat N).subset fun n hn => by simpa using hn)
  obtain ⟨n, hnS, hnN⟩ := Ultrafilter.nonempty_of_mem (p.inter_mem hS hN)
  exact ⟨n, hnS, hnN⟩

end OMA.Port3




namespace OMA.Port3

open Filter

open Classical in
theorem act_apply_eq_true_iff (p : Ultrafilter ℕ) (x : Pt) (i : Idx) :
    act p x i = true ↔ {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true} ∈ p := by
  unfold act; exact decide_eq_true_iff

/-- Eq. (2.2): `(p + q) · x = p · (q · x)`. -/
theorem act_add (p q : Ultrafilter ℕ) (x : Pt) : act (p + q) x = act p (act q x) := by
  funext i
  rw [Bool.eq_iff_iff, act_apply_eq_true_iff, act_apply_eq_true_iff, mem_add_iff]
  have hset : {m : ℕ | {m' : ℕ | m + m' ∈
        {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true}} ∈ q} =
      {m : ℕ | act q x (i.1, i.2 + stride i * (m : ℤ)) = true} := by
    ext m
    show {m' : ℕ | m + m' ∈ {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true}} ∈ q ↔
      act q x (i.1, i.2 + stride i * (m : ℤ)) = true
    rw [act_apply_eq_true_iff]
    have : {m' : ℕ | m + m' ∈ {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true}} =
        {m' : ℕ | x ((i.1, i.2 + stride i * (m : ℤ)).1, (i.1, i.2 + stride i * (m : ℤ)).2 +
          stride (i.1, i.2 + stride i * (m : ℤ)) * (m' : ℤ)) = true} := by
      ext m'
      change x _ = true ↔ x _ = true
      have h2 : i.2 + stride i * ((m + m' : ℕ) : ℤ) =
          i.2 + stride i * (m : ℤ) + stride (i.1, i.2 + stride i * (m : ℤ)) * (m' : ℤ) := by
        simp only [stride]; push_cast; ring
      rw [h2]
    rw [this]
  rw [hset]

/-- The principal ultrafilter acts as the shift `Tⁿ`. -/
theorem act_pure_apply (n : ℕ) (x : Pt) (i : Idx) :
    act (pure n) x i = x (i.1, i.2 + stride i * (n : ℤ)) := by
  rw [Bool.eq_iff_iff, act_apply_eq_true_iff, Ultrafilter.mem_pure]
  exact Iff.rfl

/-- Eq. (2.3) for `J`: `p · (J x) = J (p · x)`. -/
theorem act_cmpl (p : Ultrafilter ℕ) (x : Pt) : act p (cmpl x) = cmpl (act p x) := by
  funext i
  have e : cmpl (act p x) i = !(act p x i) := rfl
  rw [e, Bool.eq_iff_iff, act_apply_eq_true_iff, Bool.not_eq_true', ← Bool.not_eq_true,
    act_apply_eq_true_iff, ← Ultrafilter.compl_mem_iff_notMem]
  have : {n : ℕ | cmpl x (i.1, i.2 + stride i * (n : ℤ)) = true} =
      {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true}ᶜ := by
    ext n; simp [cmpl]
  rw [this]

theorem cmpl_cmpl (x : Pt) : cmpl (cmpl x) = x := by
  funext i; simp [cmpl]

/-- `J` has no fixed points. -/
theorem cmpl_ne_self (x : Pt) : cmpl x ≠ x := by
  intro h
  have := congrFun h (0, 0)
  simp [cmpl] at this

/-- Lemma 3.1, eq. (3.4): `Δ₂ (p · x) = (D p) · (Δ₂ x)`. -/
theorem dil_act (p : Ultrafilter ℕ) (x : Pt) : dil (act p x) = act (dbl p) (dil x) := by
  funext i
  have e : dil (act p x) i = act p x (2 * i.1 + 1, i.2) := rfl
  rw [e, Bool.eq_iff_iff, act_apply_eq_true_iff, act_apply_eq_true_iff, mem_dbl_iff]
  have : {n : ℕ | x (((2 * i.1 + 1, i.2) : Idx).1, ((2 * i.1 + 1, i.2) : Idx).2 +
        stride ((2 * i.1 + 1, i.2) : Idx) * (n : ℤ)) = true} =
      {n : ℕ | 2 * n ∈ {n : ℕ | dil x (i.1, i.2 + stride i * (n : ℤ)) = true}} := by
    ext n
    change x _ = true ↔ x _ = true
    have h2 : i.2 + stride ((2 * i.1 + 1, i.2) : Idx) * (n : ℤ) =
        i.2 + stride i * ((2 * n : ℕ) : ℤ) := by
      simp only [stride]; push_cast; ring
    simp only [h2]
  rw [this]

/-- Lemma 3.1: `Δ₂ J = J Δ₂`. -/
theorem dil_cmpl (x : Pt) : dil (cmpl x) = cmpl (dil x) := rfl

/-- Lemma 3.1: `Δ₂ 𝐜 = 𝐜`. -/
theorem dil_encode (c : ℤ → Bool) : dil (encode c) = encode c := rfl

/-- `p ↦ p · x` is continuous from `βℕ` to `Pt` (product topology). -/
theorem continuous_act (x : Pt) : Continuous (fun p : Ultrafilter ℕ => act p x) := by
  refine continuous_pi fun i => ?_
  rw [continuous_bool_rng true]
  have : ((fun p : Ultrafilter ℕ => act p x i) ⁻¹' {true}) =
      {u : Ultrafilter ℕ | {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true} ∈ u} := by
    ext u
    exact act_apply_eq_true_iff u x i
  rw [this]
  exact ⟨ultrafilter_isClosed_basic _, ultrafilter_isOpen_basic _⟩

end OMA.Port3




namespace OMA.Port3

open Filter

/-- Lemma 3.4: if `A ∈ p + p` and `A ∈ D p` for a nonprincipal `p`, then there is a strictly
increasing sequence `v` with `v i + v j ∈ A` for all `i ≤ j`. -/
theorem diagonal_recursion {p : Ultrafilter ℕ} (hp : Nonprincipal p) {A : Set ℕ}
    (h1 : A ∈ p + p) (h2 : A ∈ dbl p) :
    ∃ v : ℕ → ℕ, StrictMono v ∧ ∀ i j, i ≤ j → v i + v j ∈ A := by
  classical
  set K : Set ℕ := {m : ℕ | {m' : ℕ | m + m' ∈ A} ∈ p} with hKdef
  set H : Set ℕ := {n : ℕ | 2 * n ∈ A} with hHdef
  have hK : K ∈ p := (mem_add_iff A p p).1 h1
  have hH : H ∈ p := (mem_dbl_iff A p).1 h2
  let E : Finset ℕ → Set ℕ := fun F =>
    H ∩ K ∩ ⋂ x ∈ F, {n : ℕ | x ∈ K → x + n ∈ A}
  have hE : ∀ F : Finset ℕ, E F ∈ p := by
    intro F
    refine Filter.inter_mem (Filter.inter_mem hH hK) ?_
    refine (Filter.biInter_finset_mem F).2 ?_
    intro x _
    by_cases hx : x ∈ K
    · exact Filter.mem_of_superset (show {m' : ℕ | x + m' ∈ A} ∈ p from hx)
        (fun n hn _ => hn)
    · exact Filter.mem_of_superset Filter.univ_mem (fun n _ h => absurd h hx)
  have hstep : ∀ F : Finset ℕ, ∃ n ∈ E F, F.sup id + 1 ≤ n :=
    fun F => hp.exists_ge (hE F) _
  choose f hfE hfle using hstep
  let g : ℕ → Finset ℕ := fun s => Nat.rec (∅ : Finset ℕ) (fun _ F => insert (f F) F) s
  have hg : ∀ s, g (s + 1) = insert (f (g s)) (g s) := fun s => rfl
  have hmem : ∀ i j, i < j → f (g i) ∈ g j := by
    intro i j hij
    induction j with
    | zero => exact absurd hij (Nat.not_lt_zero _)
    | succ j ih =>
      rw [hg]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact Finset.mem_insert_of_mem (ih h)
      · subst h; exact Finset.mem_insert_self _ _
  have hlt : ∀ i j, i < j → f (g i) < f (g j) := by
    intro i j hij
    have h1 : f (g i) ≤ (g j).sup id := Finset.le_sup (f := id) (hmem i j hij)
    have h2 := hfle (g j)
    omega
  refine ⟨fun s => f (g s), fun i j hij => hlt i j hij, ?_⟩
  intro i j hij
  rcases lt_or_eq_of_le hij with h | h
  · have hj := hfE (g j)
    have hi := hfE (g i)
    have hiK : f (g i) ∈ K := hi.1.2
    have := Set.mem_iInter₂.1 hj.2 (f (g i)) (hmem i j h)
    exact this hiK
  · subst h
    have hi := (hfE (g i)).1.1
    have : f (g i) + f (g i) = 2 * f (g i) := by ring
    simp only
    rw [this]
    exact hi

end OMA.Port3




namespace OMA.Port3

open Filter

/-- Core of Proposition 3.2: if some colour class `A` of the sampled sequence
`n ↦ ext2 b (R + s n)` lies in both `p + p` and `D p`, then `b` has the Owings property. -/
theorem owings_of_mem_add_mem_dbl (b : ℕ → Bool) {p : Ultrafilter ℕ} (hp : Nonprincipal p)
    (R s : ℤ) (hs : 1 ≤ s) (γ : Bool)
    (h1 : {n : ℕ | ext2 b (R + s * (n : ℤ)) = γ} ∈ p + p)
    (h2 : {n : ℕ | ext2 b (R + s * (n : ℤ)) = γ} ∈ dbl p) : Owings b := by
  obtain ⟨v, hv, hvA⟩ := diagonal_recursion hp h1 h2
  set i0 : ℕ := (-R).toNat + 1 with hi0
  let f : ℕ → ℤ := fun i => 2 * (s * (v (i + i0) : ℤ)) + R
  have hvge : ∀ i, i ≤ v i := hv.id_le
  have fpos : ∀ i, 0 < f i := by
    intro i
    have h := hvge (i + i0)
    have h' : ((i + i0 : ℕ) : ℤ) ≤ (v (i + i0) : ℤ) := by exact_mod_cast h
    have h'' : (v (i + i0) : ℤ) ≤ s * (v (i + i0) : ℤ) := by
      have : (0 : ℤ) ≤ (v (i + i0) : ℤ) := by positivity
      nlinarith
    simp only [f]
    omega
  have fmono : StrictMono f := by
    intro i j hij
    have h := hv (show i + i0 < j + i0 by omega)
    have h' : (v (i + i0) : ℤ) < v (j + i0) := by exact_mod_cast h
    simp only [f]
    nlinarith
  refine ⟨Set.range (fun i => (f i).toNat), ?_, ?_, γ, ?_⟩
  · apply Set.infinite_range_of_injective
    intro i j hij
    apply fmono.injective
    have := fpos i
    have := fpos j
    simp only at hij
    omega
  · rintro _ ⟨i, rfl⟩
    have := fpos i
    show 0 < (f i).toNat
    omega
  · have key : ∀ i j, i ≤ j → b ((f i).toNat + (f j).toNat) = γ := by
      intro i j hij
      have hA := hvA (i + i0) (j + i0) (by omega)
      simp only [Set.mem_ofPred_eq, ext2] at hA
      rw [← hA]
      congr 1
      have hi := fpos i
      have hj := fpos j
      simp only [f] at hi hj ⊢
      push_cast
      rw [mul_add]
      generalize s * (v (i + i0) : ℤ) = a at hi hj ⊢
      generalize s * (v (j + i0) : ℤ) = c at hi hj ⊢
      omega
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rcases le_total i j with h | h
    · exact key i j h
    · rw [add_comm]; exact key j i h

/-- Proposition 3.2: if `b` has no infinite set of positive integers with monochromatic `B + B`,
then for `c(n) = b(2n)` and every nonprincipal `p`, `(p + p) · 𝐜 = J ((D p) · 𝐜)`. -/
theorem key_identity (b : ℕ → Bool) (hb : ¬ Owings b) {p : Ultrafilter ℕ}
    (hp : Nonprincipal p) :
    act (p + p) (encode (ext2 b)) = cmpl (act (dbl p) (encode (ext2 b))) := by
  funext i
  obtain ⟨k, R⟩ := i
  have hs : (1 : ℤ) ≤ stride (k, R) := by
    simp only [stride]; omega
  have hT : ∀ γ : Bool, {n : ℕ | ext2 b (R + stride (k, R) * (n : ℤ)) = γ} ∈ p + p →
      {n : ℕ | ext2 b (R + stride (k, R) * (n : ℤ)) = γ} ∈ dbl p → False :=
    fun γ h1 h2 => hb (owings_of_mem_add_mem_dbl b hp R _ hs γ h1 h2)
  have hcompl : ∀ q : Ultrafilter ℕ,
      {n : ℕ | ext2 b (R + stride (k, R) * (n : ℤ)) = true} ∉ q →
      {n : ℕ | ext2 b (R + stride (k, R) * (n : ℤ)) = false} ∈ q := by
    intro q hq
    have := (Ultrafilter.compl_mem_iff_notMem (f := q)).2 hq
    convert this using 1
    ext n
    simp
  simp only [act, cmpl, encode]
  by_cases h1 : {n : ℕ | ext2 b (R + stride (k, R) * (n : ℤ)) = true} ∈ p + p <;>
    by_cases h2 : {n : ℕ | ext2 b (R + stride (k, R) * (n : ℤ)) = true} ∈ dbl p
  · exact (hT true h1 h2).elim
  · simp [h1, h2]
  · simp [h1, h2]
  · exact (hT false (hcompl _ h1) (hcompl _ h2)).elim

end OMA.Port3




namespace OMA.Port3

open Filter

/-- `ω(x)` is closed. -/
theorem isClosed_omega (x : Pt) : IsClosed (Omega x) := by
  have hc : IsCompact {p : Ultrafilter ℕ | Nonprincipal p} :=
    isClosed_nonprincipal.isCompact
  have : Omega x = (fun p : Ultrafilter ℕ => act p x) '' {p | Nonprincipal p} := by
    ext y; simp [Omega]
  rw [this]
  exact (hc.image (continuous_act x)).isClosed

/-- `ω(x)` is nonempty. -/
theorem omega_nonempty (x : Pt) : (Omega x).Nonempty := by
  obtain ⟨p, hp, -⟩ := exists_nonprincipal_mem (Set.infinite_univ (α := ℕ))
  exact ⟨act p x, p, hp, rfl⟩

/-- `ω(x)` is invariant. -/
theorem omega_invariant (x : Pt) (p : Ultrafilter ℕ) {y : Pt} (hy : y ∈ Omega x) :
    act p y ∈ Omega x := by
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨p + q, nonprincipal_add hq, act_add p q x⟩

/-- Every `ω(x)` contains a minimal subsystem (in the sense of `IsMinimalSub`). -/
theorem exists_minimal (x : Pt) : ∃ M : Set Pt, IsMinimalSub x M := by
  let S : Set (Set Pt) := {K | K.Nonempty ∧ IsClosed K ∧ K ⊆ Omega x ∧
    ∀ p : Ultrafilter ℕ, ∀ y ∈ K, act p y ∈ K}
  have hΩ : Omega x ∈ S :=
    ⟨omega_nonempty x, isClosed_omega x, le_rfl, fun p y hy => omega_invariant x p hy⟩
  obtain ⟨M, -, hM⟩ := zorn_superset_nonempty S (by
    intro c hcS hchain hcne
    have : Nonempty c := hcne.to_subtype
    refine ⟨⋂₀ c, ⟨?_, ?_, ?_, ?_⟩, fun s hs => Set.sInter_subset_of_mem hs⟩
    · exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun a ha b hb => (hchain.total ha hb).elim
          (fun h => ⟨a, ha, subset_rfl, h⟩) (fun h => ⟨b, hb, h, subset_rfl⟩)) (fun U hU => (hcS hU).1)
        (fun U hU => (hcS hU).2.1.isCompact) (fun U hU => (hcS hU).2.1)
    · exact isClosed_sInter fun U hU => (hcS hU).2.1
    · obtain ⟨U, hU⟩ := hcne
      exact (Set.sInter_subset_of_mem hU).trans (hcS hU).2.2.1
    · intro p y hy
      exact Set.mem_sInter.2 fun U hU => (hcS hU).2.2.2 p y (Set.mem_sInter.1 hy U hU))
    (Omega x) hΩ
  obtain ⟨hne, hcl, hsub, hinv⟩ := hM.prop
  refine ⟨M, hne, hcl, hsub, hinv, ?_⟩
  intro y hy z hz
  let K : Set Pt := Set.range fun q : Ultrafilter ℕ => act q y
  have hKM : K ⊆ M := by
    rintro _ ⟨q, rfl⟩; exact hinv q y hy
  have hKS : K ∈ S := by
    refine ⟨⟨y, ?_⟩, ?_, hKM.trans hsub, ?_⟩
    · -- `y = act (pure 0) y`
      refine ⟨pure 0, ?_⟩
      funext i
      show act (pure 0) y i = y i
      rw [act_pure_apply]
      simp
    · exact (isCompact_range (continuous_act y)).isClosed
    · rintro p _ ⟨q, rfl⟩
      exact ⟨p + q, act_add p q y⟩
  have hMK : M ⊆ K := hM.2 hKS hKM
  obtain ⟨q, hq⟩ := hMK hz
  exact ⟨q, hq⟩

end OMA.Port3




namespace OMA.Port3

open Filter

/-- Proposition 3.6: if `Δ₂ x = x` and `(p+p) x = J((D p) x)` for all `p ∈ ℕ*`, then no
minimal subsystem `M ⊆ ω(x)` meets its image `J M`. -/
theorem disjoint_minimal (x : Pt) (hdil : dil x = x)
    (hkey : ∀ p : Ultrafilter ℕ, Nonprincipal p → act (p + p) x = cmpl (act (dbl p) x))
    (M : Set Pt) (hM : IsMinimalSub x M) :
    ∀ y ∈ M, cmpl y ∉ M := by
  intro y₀ hy₀ hJy₀
  obtain ⟨_, hMcl, hMΩ, hMinv, hMreach⟩ := hM
  -- Step 1: the compact subsemigroup `I = {p ∈ ℕ* | p x ∈ M}` and an idempotent in it.
  set I : Set (Ultrafilter ℕ) := {p | Nonprincipal p} ∩ (fun p => act p x) ⁻¹' M with hI
  have hIcl : IsClosed I :=
    isClosed_nonprincipal.inter (hMcl.preimage (continuous_act x))
  have hIne : I.Nonempty := by
    obtain ⟨p, hp, hpx⟩ := hMΩ hy₀
    exact ⟨p, hp, by simp [hpx, hy₀]⟩
  have hIadd : ∀ a ∈ I, ∀ b ∈ I, a + b ∈ I := by
    intro a ha b hb
    refine ⟨nonprincipal_add hb.1, ?_⟩
    show act (a + b) x ∈ M
    rw [act_add]
    exact hMinv a _ hb.2
  obtain ⟨e, heI, hee⟩ := exists_idempotent_in_compact_add_subsemigroup
    continuous_add_const I hIne hIcl.isCompact hIadd
  -- Step 2
  set y := act e x with hy
  have hyM : y ∈ M := heI.2
  have hDe : act (dbl e) x = cmpl y := by
    have h := hkey e heI.1
    rw [hee] at h
    rw [hy, h, cmpl_cmpl]
  -- Step 3
  obtain ⟨q₁, hq₁⟩ := hMreach y₀ hy₀ y hyM
  have hJyM : cmpl y ∈ M := by
    have := hMinv q₁ _ hJy₀
    rwa [act_cmpl, hq₁] at this
  obtain ⟨s, hs⟩ := hMreach y hyM (cmpl y) hJyM
  -- Step 4
  have hq : Nonprincipal (s + e) := nonprincipal_add heI.1
  have hqx : act (s + e) x = cmpl y := by rw [act_add, ← hy, hs]
  have hey : act e y = y := by rw [hy, ← act_add, hee]
  have hqq : act ((s + e) + (s + e)) x = y := by
    rw [act_add, hqx, act_add, act_cmpl, hey, act_cmpl, hs, cmpl_cmpl]
  -- Step 5
  have hdily : dil y = cmpl y := by rw [hy, dil_act, hdil, hDe]
  have hDq : act (dbl (s + e)) x = y := by
    conv_lhs => rw [← hdil]
    rw [← dil_act, hqx, dil_cmpl, hdily, cmpl_cmpl]
  -- Step 6
  have h := hkey (s + e) hq
  rw [hqq, hDq] at h
  exact cmpl_ne_self y h.symm

end OMA.Port3




namespace OMA.Port3

open Filter

/-- If `M` is closed and `J y ∉ M` for all `y ∈ M`, there is `G : Pt → Bool` depending only on
finitely many coordinates, with `G (J u) = ¬ G u` for every `u`, and `G ≡ true` on `M`.
(`H = G⁻¹(true)` is then a clopen set with `Pt = H ⊔ J H` and `M ⊆ H`.) -/
theorem finite_separation (M : Set Pt) (hM : IsClosed M) (hdisj : ∀ y ∈ M, cmpl y ∉ M) :
    ∃ (G : Pt → Bool) (F : Finset Idx),
      (∀ u v : Pt, (∀ i ∈ F, u i = v i) → G u = G v) ∧
      (∀ u : Pt, G (cmpl u) = !(G u)) ∧
      (∀ y ∈ M, G y = true) := by
  classical
  have hMc : IsCompact M := hM.isCompact
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : Finset Idx, ∀ y ∈ M, ∀ z ∈ M, ∃ i ∈ F₀, y i = z i := by
    have hK : IsCompact (M ×ˢ M) := hMc.prod hMc
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : Idx => {p : Pt × Pt | p.1 i = p.2 i})
      (fun i => (isOpen_discrete {q : Bool × Bool | q.1 = q.2}).preimage
        (by fun_prop : Continuous fun p : Pt × Pt => (p.1 i, p.2 i)))
      (by
        rintro ⟨y, z⟩ ⟨hy, hz⟩
        by_contra h
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at h
        apply hdisj z hz
        have hyz : y = cmpl z := funext fun i => by
          have hi := h i
          simp only [cmpl]
          cases hyi : y i <;> cases hzi : z i <;> simp_all
        exact hyz ▸ hy)
    refine ⟨t, fun y hy z hz => ?_⟩
    have hmem := ht (Set.mk_mem_prod hy hz)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hmem
    obtain ⟨i, hi, h⟩ := hmem
    exact ⟨i, hi, h⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Pt → Prop, A = fun u => ∃ y ∈ M, ∀ i ∈ F₀, y i = u i := ⟨_, rfl⟩
  let i₀ : Idx := (0, 0)
  have hcc : ∀ u, cmpl (cmpl u) = u := fun u => funext fun i => by simp [cmpl]
  have hexcl : ∀ u, A u → ¬ A (cmpl u) := by
    intro u h1 h2
    rw [hAdef] at h1 h2
    obtain ⟨y, hy, hyu⟩ := h1
    obtain ⟨y', hy', hyu'⟩ := h2
    obtain ⟨i, hi, h⟩ := hF₀ y hy y' hy'
    have e1 := hyu i hi
    have e2 := hyu' i hi
    simp only [cmpl] at e2
    rw [e1, e2] at h
    cases u i <;> simp at h
  have hAcongr : ∀ u v : Pt, (∀ i ∈ F₀, u i = v i) → (A u ↔ A v) := by
    intro u v huv
    rw [hAdef]
    refine exists_congr fun y => and_congr_right fun _ => forall₂_congr fun i hi => ?_
    rw [huv i hi]
  refine ⟨fun u => if A u then true else if A (cmpl u) then false else u i₀,
    insert i₀ F₀, ?_, ?_, ?_⟩
  · intro u v huv
    have hA : A u ↔ A v := hAcongr u v fun i hi => huv i (Finset.mem_insert_of_mem hi)
    have hA' : A (cmpl u) ↔ A (cmpl v) := hAcongr _ _ fun i hi => by
      simp only [cmpl]; rw [huv i (Finset.mem_insert_of_mem hi)]
    have h0 : u i₀ = v i₀ := huv i₀ (Finset.mem_insert_self _ _)
    simp only [hA, hA', h0]
  · intro u
    simp only [hcc]
    by_cases h1 : A u
    · simp [h1, hexcl u h1]
    · by_cases h2 : A (cmpl u)
      · simp [h1, h2]
      · simp [h1, h2, cmpl]
  · intro y hy
    have : A y := by rw [hAdef]; exact ⟨y, hy, fun _ _ => rfl⟩
    simp [this]

end OMA.Port3




namespace OMA.Port3

open Filter

/-- If `G` depends only on the coordinates in `F`, then `h n = G (Tⁿ x)` satisfies
`{n | h n} ∈ q ↔ G (q · x)` for every ultrafilter `q`. -/
theorem coding (G : Pt → Bool) (F : Finset Idx)
    (hF : ∀ u v : Pt, (∀ i ∈ F, u i = v i) → G u = G v) (x : Pt) (q : Ultrafilter ℕ) :
    {n : ℕ | G (act (pure n) x) = true} ∈ q ↔ G (act q x) = true := by
  classical
  set W : Set ℕ := {n | ∀ i ∈ F, act (pure n) x i = act q x i} with hWdef
  have hW : W ∈ q := by
    have : W = ⋂ i ∈ F, {n : ℕ | act (pure n) x i = act q x i} := by
      ext n; simp [hWdef]
    rw [this]
    show _ ∈ (q : Filter ℕ)
    rw [Filter.biInter_finset_mem F]
    intro i _
    by_cases hA : {n : ℕ | x (i.1, i.2 + stride i * (n : ℤ)) = true} ∈ q
    · refine Filter.mem_of_superset hA ?_
      intro n hn
      simp only [Set.mem_ofPred_eq] at hn ⊢
      simp only [act, Ultrafilter.mem_pure, Set.mem_ofPred_eq, hn, hA, decide_true]
    · have hc := (Ultrafilter.compl_mem_iff_notMem).2 hA
      refine Filter.mem_of_superset hc ?_
      intro n hn
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hn ⊢
      simp only [act, Ultrafilter.mem_pure, Set.mem_ofPred_eq, hn, hA, decide_false, Bool.false_eq_true, decide_false]
  have hEq : ∀ n ∈ W, G (act (pure n) x) = G (act q x) := fun n hn => hF _ _ hn
  constructor
  · intro hS
    obtain ⟨n, hn1, hn2⟩ := (q.inter_mem hS hW |> Ultrafilter.nonempty_of_mem)
    rw [← hEq n hn2]; exact hn1
  · intro hG
    refine Filter.mem_of_superset hW ?_
    intro n hn
    simp only [Set.mem_ofPred_eq]
    rw [hEq n hn]; exact hG

end OMA.Port3




namespace OMA.Port3

open Filter

/-- If `G ≡ true` on a minimal subsystem `M ⊆ ω(x)` and `h n = G (Tⁿ x)` codes `G` along
ultrafilters, then `h` has arbitrarily long runs of `true` arbitrarily far to the right. -/
theorem thick_of_minimal (x : Pt) (M : Set Pt) (hM : IsMinimalSub x M) (G : Pt → Bool)
    (hG : ∀ y ∈ M, G y = true)
    (hcode : ∀ q : Ultrafilter ℕ,
      {n : ℕ | G (act (pure n) x) = true} ∈ q ↔ G (act q x) = true) :
    ∀ L N : ℕ, ∃ n, N ≤ n ∧ ∀ j ≤ L, G (act (pure (n + j)) x) = true := by
  intro L N
  obtain ⟨y, hyM⟩ := hM.1
  obtain ⟨p, hp, rfl⟩ := hM.2.2.1 hyM
  have hj : ∀ j : ℕ, {m : ℕ | G (act (pure (m + j)) x) = true} ∈ p := by
    intro j
    have h1 : G (act (pure j + p) x) = true := by
      rw [act_add]; exact hG _ (hM.2.2.2.1 _ _ hyM)
    have h2 := (hcode (pure j + p)).2 h1
    rw [mem_add_iff, Ultrafilter.mem_pure] at h2
    simpa [Nat.add_comm] using h2
  have hall : (⋂ j ∈ Finset.range (L + 1), {m : ℕ | G (act (pure (m + j)) x) = true}) ∈ p :=
    (Filter.biInter_finset_mem _).2 fun j _ => hj j
  obtain ⟨n, hn, hNn⟩ := hp.exists_ge hall N
  refine ⟨n, hNn, fun j hjL => ?_⟩
  simp only [Set.mem_iInter, Finset.mem_range] at hn
  exact hn j (by omega)

end OMA.Port3




namespace OMA.Port3

open Filter

/-- If for every `p ∈ ℕ*` exactly one of `p + p`, `D p` contains `{n | h n = true}`, then no
infinite `B ⊆ ℕ` has `B + B` monochromatic under `h`. -/
theorem no_mono_of_identity (h : ℕ → Bool)
    (hid : ∀ p : Ultrafilter ℕ, Nonprincipal p →
      ({n : ℕ | h n = true} ∈ p + p ↔ {n : ℕ | h n = true} ∉ dbl p)) :
    ¬ ∃ B : Set ℕ, B.Infinite ∧ IsMonoSumset h B := by
  rintro ⟨B, hB, γ, hγ⟩
  obtain ⟨p, hp, hBp⟩ := exists_nonprincipal_mem hB
  have hD : {n : ℕ | h n = γ} ∈ dbl p := by
    rw [mem_dbl_iff]
    exact Filter.mem_of_superset hBp fun n hn => by
      show h (2 * n) = γ
      rw [two_mul]; exact hγ n hn n hn
  have hS : {n : ℕ | h n = γ} ∈ p + p := by
    rw [mem_add_iff]
    exact Filter.mem_of_superset hBp fun u hu =>
      Filter.mem_of_superset hBp fun m hm => hγ u hu m hm
  cases γ with
  | false =>
    have e : {n : ℕ | h n = false} = {n : ℕ | h n = true}ᶜ := by
      ext n; simp
    rw [e, Ultrafilter.compl_mem_iff_notMem] at hD hS
    exact hS ((hid p hp).2 hD)
  | true => exact (hid p hp).1 hS hD

end OMA.Port3




namespace OMA.Port3

open Filter

/-- Infinite Ramsey for pairs: any finite colouring `χ` of pairs `i < j` of an infinite set
`S ⊆ ℕ` has an infinite homogeneous subsequence. -/
theorem ramsey_pairs {κ : Type*} [Finite κ] (χ : ℕ → ℕ → κ) (S : Set ℕ) (hS : S.Infinite) :
    ∃ (k : κ) (u : ℕ → ℕ), StrictMono u ∧ (∀ i, u i ∈ S) ∧
      ∀ i j, i < j → χ (u i) (u j) = k := by
  have := hS.cofinite_inf_principal_neBot
  let U : Ultrafilter ℕ := Ultrafilter.of (cofinite ⊓ 𝓟 S)
  have hUle : (U : Filter ℕ) ≤ cofinite ⊓ 𝓟 S := Ultrafilter.of_le _
  have hSU : S ∈ U := (le_trans hUle inf_le_right) (mem_principal_self S)
  have hIoi : ∀ n : ℕ, Set.Ioi n ∈ U := fun n =>
    (le_trans hUle inf_le_left) (Nat.cofinite_eq_atTop ▸ Ioi_mem_atTop n)
  -- typical colour at each point
  have hc : ∀ i, ∃ a : κ, U.map (χ i) = pure a := fun i => Ultrafilter.eq_pure_of_finite _
  choose c hc using hc
  have hcU : ∀ i, {j | χ i j = c i} ∈ U := by
    intro i
    have : ({c i} : Set κ) ∈ U.map (χ i) := by rw [hc i]; exact Ultrafilter.mem_pure.2 rfl
    exact this
  obtain ⟨k, hk⟩ := Ultrafilter.eq_pure_of_finite (U.map c)
  have hA : {i | c i = k} ∈ U := by
    have : ({k} : Set κ) ∈ U.map c := by rw [hk]; exact Ultrafilter.mem_pure.2 rfl
    exact this
  let A : Set ℕ := S ∩ {i | c i = k}
  have hAU : A ∈ U := Filter.inter_mem hSU hA
  -- recursion on U-large subsets of A
  let T := {B : Set ℕ // B ∈ U ∧ B ⊆ A}
  have hne : ∀ B : T, B.1.Nonempty := fun B => Ultrafilter.nonempty_of_mem B.2.1
  let pick : T → ℕ := fun B => (hne B).some
  have hpick : ∀ B : T, pick B ∈ B.1 := fun B => (hne B).some_mem
  let step : T → T := fun B =>
    ⟨B.1 ∩ {j | χ (pick B) j = k} ∩ Set.Ioi (pick B), by
      refine ⟨Filter.inter_mem (Filter.inter_mem B.2.1 ?_) (hIoi _), fun x hx => B.2.2 hx.1.1⟩
      have hp : c (pick B) = k := (B.2.2 (hpick B)).2
      simpa [hp] using hcU (pick B)⟩
  let Bs : ℕ → T := fun n => step^[n] ⟨A, hAU, le_rfl⟩
  have hBs : ∀ n, Bs (n + 1) = step (Bs n) := fun n => by
    simp only [Bs]; rw [Function.iterate_succ_apply']
  let u : ℕ → ℕ := fun n => pick (Bs n)
  have hsub : ∀ m n, m ≤ n → (Bs n).1 ⊆ (Bs m).1 := by
    intro m n hmn
    induction hmn with
    | refl => exact le_rfl
    | step _ ih =>
      rw [hBs]
      exact fun x hx => ih hx.1.1
  have key : ∀ i j, i < j → χ (u i) (u j) = k ∧ u i < u j := by
    intro i j hij
    have h1 : u j ∈ (Bs (i + 1)).1 := hsub _ _ hij (hpick _)
    rw [hBs] at h1
    exact ⟨h1.1.2, h1.2⟩
  refine ⟨k, u, fun i j hij => (key i j hij).2, fun i => ((Bs i).2.2 (hpick _)).1,
    fun i j hij => (key i j hij).1⟩

end OMA.Port3





namespace OMA.Port3

/-- Lemma A.1 (`m = ℓ = 1`): if no infinite `B` has `B + B ⊆ c⁻¹(j)`, there is `C` such that
whenever the even block `Q(K, M) = {2(K+s) : s < M}` contains at most one point of colour `¬j`,
and `C < x`, `2K < x`, `x + C < 2(K + M)`, then `c(2x) = ¬j`. -/
theorem hindman_local (c : ℕ → Bool) (j : Bool)
    (hno : ¬ ∃ B : Set ℕ, B.Infinite ∧ ∀ x ∈ B, ∀ y ∈ B, c (x + y) = j) :
    ∃ C : ℕ, ∀ K M x : ℕ,
      ((Finset.range M).filter (fun s => c (2 * (K + s)) = !j)).card ≤ 1 →
      C < x → 2 * K < x → x + C < 2 * (K + M) → c (2 * x) = !j := by
  by_contra hcon
  push Not at hcon
  choose K M X hcard hC hK hM hc using hcon
  let idx : ℕ → ℕ := fun r => Nat.rec 0 (fun _ i => X i + 1) r
  have hidx_succ : ∀ r, idx (r + 1) = X (idx r) + 1 := fun r => rfl
  let x : ℕ → ℕ := fun r => X (idx r)
  have hlt : ∀ r, idx r < x r := fun r => hC _
  have hidx_mono : StrictMono idx := strictMono_nat_of_lt_succ (fun r => by
    rw [hidx_succ]; have := hlt r; simp only [x] at this; omega)
  have key : ∀ t r, t < r → x t < idx r := fun t r htr => by
    have h1 : idx (t + 1) ≤ idx r := hidx_mono.monotone htr
    rw [hidx_succ] at h1; simp only [x]; omega
  have xmono : StrictMono x := fun t r htr => lt_trans (key t r htr) (hlt r)
  have hcj : ∀ r, c (2 * x r) = j := fun r => by
    have := hc (idx r)
    simp only [x]
    cases h : c (2 * X (idx r)) <;> cases j <;> simp_all
  obtain ⟨⟨k1, k2⟩, u, hu, -, hhom⟩ := ramsey_pairs (κ := Bool × Bool)
    (fun t r => (c (x t + x r), decide (Even (x t + x r)))) Set.univ Set.infinite_univ
  simp only [Prod.mk.injEq] at hhom
  cases k2
  · have h01 := (hhom 0 1 (by norm_num)).2
    have h12 := (hhom 1 2 (by norm_num)).2
    have h02 := (hhom 0 2 (by norm_num)).2
    simp only [decide_eq_false_iff_not, Nat.not_even_iff_odd, Nat.odd_iff] at h01 h12 h02
    omega
  · by_cases hk : k1 = j
    · apply hno
      refine ⟨Set.range (x ∘ u), Set.infinite_range_of_injective (xmono.comp hu).injective, ?_⟩
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rcases lt_trichotomy a b with hab | rfl | hab
      · exact (hhom a b hab).1.trans hk
      · simp only [Function.comp_apply]; rw [← two_mul]; exact hcj _
      · simp only [Function.comp_apply]; rw [add_comm]; exact (hhom b a hab).1.trans hk
    · have hk' : k1 = !j := by cases k1 <;> cases j <;> simp_all
      obtain ⟨c02, e02⟩ := hhom 0 2 (by norm_num)
      obtain ⟨c12, e12⟩ := hhom 1 2 (by norm_num)
      simp only [decide_eq_true_eq] at e02 e12
      obtain ⟨m1, hm1⟩ := e02
      obtain ⟨m2, hm2⟩ := e12
      have hab : x (u 0) < x (u 1) := xmono (hu (by norm_num))
      have k0 := key (u 0) (u 2) (hu (by norm_num))
      have k1' := key (u 1) (u 2) (hu (by norm_num))
      have hK2 := hK (idx (u 2))
      have hM2 := hM (idx (u 2))
      have hcard2 := hcard (idx (u 2))
      set KK := K (idx (u 2))
      set MM := M (idx (u 2))
      have hxr : X (idx (u 2)) = x (u 2) := rfl
      rw [hxr] at hK2 hM2
      set I := idx (u 2)
      have mem1 : m1 - KK ∈ (Finset.range MM).filter (fun s => c (2 * (KK + s)) = !j) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have : 2 * (KK + (m1 - KK)) = x (u 0) + x (u 2) := by omega
        rw [this, c02, hk']
      have mem2 : m2 - KK ∈ (Finset.range MM).filter (fun s => c (2 * (KK + s)) = !j) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have : 2 * (KK + (m2 - KK)) = x (u 1) + x (u 2) := by omega
        rw [this, c12, hk']
      have hne : m1 - KK ≠ m2 - KK := by omega
      have := Finset.one_lt_card.mpr ⟨_, mem1, _, mem2, hne⟩
      omega

end OMA.Port3




namespace OMA.Port3

/-- `a` is *good* (for colour `γ₀` and length `L`): the even block `{2(a+s) : s < L}` contains at
most one point of colour `γ₀`. -/
private def HTGood (c : ℕ → Bool) (γ₀ : Bool) (L a : ℕ) : Prop :=
  ((Finset.range L).filter (fun s => c (2 * (a + s)) = γ₀)).card ≤ 1

/-- Proposition A.2 (`m = ℓ = 1`): if the colour class `c⁻¹(γ₀)` contains arbitrarily long
intervals arbitrarily far to the right, then some infinite `B ⊆ ℕ` has `B + B`
monochromatic. -/
theorem hindman_thick (c : ℕ → Bool) (γ₀ : Bool)
    (hthick : ∀ L N : ℕ, ∃ n, N ≤ n ∧ ∀ j ≤ L, c (n + j) = γ₀) :
    ∃ B : Set ℕ, B.Infinite ∧ IsMonoSumset c B := by
  classical
  by_contra hcon
  have hno : ∀ j : Bool, ¬ ∃ B : Set ℕ, B.Infinite ∧ ∀ x ∈ B, ∀ y ∈ B, c (x + y) = j :=
    fun j ⟨B, hB, h⟩ => hcon ⟨B, hB, j, h⟩
  obtain ⟨C₀, hC₀⟩ := hindman_local c γ₀ (hno γ₀)
  obtain ⟨C₁, hC₁⟩ := hindman_local c (!γ₀) (hno (!γ₀))
  simp only [Bool.not_not] at hC₁
  obtain ⟨L, hL⟩ : ∃ L, L = C₁ + 1 := ⟨_, rfl⟩
  -- Step 1: long even blocks of colour `γ₀`
  have hblk : ∀ N M : ℕ, ∃ K, N ≤ K ∧ ∀ s < M, c (2 * (K + s)) = γ₀ := by
    intro N M
    obtain ⟨n, hn, hc⟩ := hthick (2 * M) (2 * N)
    refine ⟨(n + 1) / 2, by omega, fun s hs => ?_⟩
    have := hc (2 * ((n + 1) / 2 + s) - n) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this
  choose blk hblkN hblkc using hblk
  obtain ⟨K, hKc, hK0, hKs⟩ : ∃ K : ℕ → ℕ,
      (∀ n, ∀ s < n + L + C₀ + 1, c (2 * (K n + s)) = γ₀) ∧ C₀ + C₁ + 1 ≤ K 0 ∧
        ∀ n, L + 3 + 2 * K n ≤ K (n + 1) := by
    refine ⟨fun n => Nat.rec (motive := fun _ => ℕ) (blk (C₀ + C₁ + 1) (0 + L + C₀ + 1))
      (fun n Kn => blk (L + 3 + 2 * Kn) (n + 1 + L + C₀ + 1)) n, fun n => ?_,
      hblkN _ _, fun n => hblkN _ _⟩
    cases n <;> exact hblkc _ _
  have hKlb : ∀ n, C₀ + C₁ + 1 ≤ K n := by
    intro n; induction n with
    | zero => exact hK0
    | succ n ih => have := hKs n; omega
  -- Step 2: `X_n = 2 K_n + 1` is good
  have hX : ∀ n, HTGood c γ₀ L (2 * K n + 1) := by
    intro n
    unfold HTGood
    have : (Finset.range L).filter (fun s => c (2 * (2 * K n + 1 + s)) = γ₀) = ∅ := by
      apply Finset.filter_false_of_mem
      intro s hs
      have hs' := Finset.mem_range.1 hs
      have hKn := hKlb n
      have hcard : ((Finset.range (n + L + C₀ + 1)).filter
          (fun s => c (2 * (K n + s)) = !γ₀)).card ≤ 1 := by
        rw [Finset.filter_false_of_mem]
        · simp
        · intro t ht
          simp [hKc n t (Finset.mem_range.1 ht)]
      have h := hC₀ (K n) (n + L + C₀ + 1) (2 * K n + 1 + s) hcard (by omega) (by omega)
        (by omega)
      simp [h]
    rw [this]; simp
  -- Step 3: `a_n` = greatest good integer below `K_{n+1}`
  obtain ⟨a, ha_good, ha_lt, ha_ge, ha_max⟩ : ∃ a : ℕ → ℕ, (∀ n, HTGood c γ₀ L (a n)) ∧
      (∀ n, a n < K (n + 1)) ∧ (∀ n, 2 * K n + 1 ≤ a n) ∧
      (∀ n b, a n < b → b < K (n + 1) → ¬ HTGood c γ₀ L b) := by
    refine ⟨fun n => Nat.findGreatest (HTGood c γ₀ L) (K (n + 1) - 1), fun n => ?_, fun n => ?_,
      fun n => ?_, fun n b h1 h2 => ?_⟩
    · have := hKs n
      exact Nat.findGreatest_spec (P := HTGood c γ₀ L) (m := 2 * K n + 1) (by omega) (hX n)
    · have := hKs n
      have := Nat.findGreatest_le (P := HTGood c γ₀ L) (K (n + 1) - 1)
      show Nat.findGreatest (HTGood c γ₀ L) (K (n + 1) - 1) < K (n + 1)
      omega
    · have := hKs n
      exact Nat.le_findGreatest (P := HTGood c γ₀ L) (by omega) (hX n)
    · exact Nat.findGreatest_is_greatest h1 (by omega)
  -- Step 4: `z_n = 2 a_n + 1`
  have hz : ∀ n, ∀ s < L, c (2 * (2 * a n + 1 + s)) = γ₀ := by
    intro n s hs
    have h1 := ha_ge n
    have h2 := hKlb n
    exact hC₁ (a n) L (2 * a n + 1 + s) (ha_good n) (by omega) (by omega) (by omega)
  have hamono : StrictMono a := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    have := ha_lt n
    have := ha_ge (n + 1)
    omega
  let z : ℕ → ℕ := fun n => 2 * a n + 1
  have hzmono : StrictMono z := fun m n h => by
    have := hamono h
    show 2 * a m + 1 < 2 * a n + 1
    omega
  -- Step 5: Ramsey
  obtain ⟨τ, u, hu, -, hχ⟩ := ramsey_pairs (κ := Fin L → Bool)
    (fun r t => fun s : Fin L => c (z r + z t + 2 * (s : ℕ))) Set.univ Set.infinite_univ
  by_cases hτ : ∃ s : Fin L, τ s = γ₀
  · obtain ⟨s, hs⟩ := hτ
    apply hno γ₀
    refine ⟨Set.range (fun i => z (u i) + s), Set.infinite_range_of_injective ?_, ?_⟩
    · intro i k hik
      exact (hzmono.comp hu).injective (by simpa using hik)
    · rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩
      rcases lt_trichotomy i k with h | rfl | h
      · have := congrFun (hχ i k h) s
        rw [← hs, ← this]
        congr 1; ring
      · have := hz (u i) s s.2
        rw [← this]
        congr 1; simp only [z]; ring
      · have := congrFun (hχ k i h) s
        rw [← hs, ← this]
        congr 1; ring
  · simp only [not_exists] at hτ
    -- Step 6
    set D := a (u 0) + 1 with hD
    set n := u (D + 1) with hn
    have hnD : D + 1 ≤ n := hu.id_le (D + 1)
    set α := a n + D with hα
    have hcol : ∀ s < L, c (2 * (α + s)) ≠ γ₀ := by
      intro s hs
      have := congrFun (hχ 0 (D + 1) (by omega)) ⟨s, hs⟩
      simp only at this
      have e : z (u 0) + z (u (D + 1)) + 2 * s = 2 * (α + s) := by
        simp only [z, hα, hD, hn]; ring
      rw [← e, this]
      exact hτ _
    have hgood : HTGood c γ₀ L α := by
      unfold HTGood
      rw [Finset.filter_false_of_mem]
      · simp
      · intro s hs
        exact hcol s (Finset.mem_range.1 hs)
    have hge : K (n + 1) ≤ α := by
      by_contra hlt
      exact ha_max n α (by omega) (by omega) hgood
    have hlt := ha_lt n
    have hmem := hKc (n + 1) (α - K (n + 1)) (by omega)
    rw [Nat.add_sub_cancel' hge] at hmem
    have hL1 : 0 < L := by omega
    exact hcol 0 hL1 (by simpa using hmem)

end OMA.Port3




namespace OMA.Port3

open Filter Pointwise

/-- Theorem 1.1 for Boolean colourings: every `b : ℕ → Bool` has an infinite set `B` of
positive integers with `B + B` monochromatic. -/
theorem owings_bool (b : ℕ → Bool) : Owings b := by
  by_contra H
  -- the encoded point `𝐜` of `c(n) = b(2n)`
  have hkey : ∀ p : Ultrafilter ℕ, Nonprincipal p →
      act (p + p) (encode (ext2 b)) = cmpl (act (dbl p) (encode (ext2 b))) :=
    fun p hp => key_identity b H hp
  have hdil : dil (encode (ext2 b)) = encode (ext2 b) := dil_encode _
  -- a minimal subsystem `M ⊆ ω(𝐜)` with `M ∩ J M = ∅`
  obtain ⟨M, hM⟩ := exists_minimal (encode (ext2 b))
  have hdisj := disjoint_minimal (encode (ext2 b)) hdil hkey M hM
  -- a finitely determined `J`-odd `G` with `G ≡ true` on `M`
  obtain ⟨G, F, hF, hGc, hGM⟩ := finite_separation M hM.2.1 hdisj
  have hcode := coding G F hF (encode (ext2 b))
  -- the new colouring `h n = G (Tⁿ 𝐜)` satisfies `(p+p) h = J (D p) h`
  have hid : ∀ p : Ultrafilter ℕ, Nonprincipal p →
      ({n : ℕ | G (act (pure n) (encode (ext2 b))) = true} ∈ p + p ↔
        {n : ℕ | G (act (pure n) (encode (ext2 b))) = true} ∉ dbl p) := by
    intro p hp
    rw [hcode (p + p), hcode (dbl p), hkey p hp, hGc]
    cases G (act (dbl p) (encode (ext2 b))) <;> simp
  -- so `h` has no monochromatic `B + B` ...
  have hno := no_mono_of_identity (fun n => G (act (pure n) (encode (ext2 b)))) hid
  -- ... but its colour class `true` is thick, so Hindman's theorem gives one.
  have hthick := thick_of_minimal (encode (ext2 b)) M hM G hGM hcode
  exact hno (hindman_thick (fun n => G (act (pure n) (encode (ext2 b)))) true hthick)

theorem erdos_1199_main : ∀ (color : ℕ → Fin 2), ∃ (A : Set ℕ),
    A.Infinite ∧ ∀ n ∈ (A + A), ∀ m ∈ (A + A), color n = color m := by
  intro color
  obtain ⟨B, hBinf, hBpos, γ, hγ⟩ := owings_bool (fun n => decide (color n = 1))
  refine ⟨B, hBinf, ?_⟩
  have key : ∀ n ∈ B + B, decide (color n = 1) = γ := by
    rintro n ⟨a, ha, a', ha', rfl⟩
    exact hγ a ha a' ha'
  intro n hn m hm
  have hnm : decide (color n = 1) = decide (color m = 1) := (key n hn).trans (key m hm).symm
  have two : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  rcases two (color n) with h | h <;> rcases two (color m) with h' | h' <;>
    simp [h, h'] at hnm ⊢

end OMA.Port3

theorem OMA.solution : type_of% @Erdos1199.erdos_1199 := OMA.Port3.erdos_1199_main
