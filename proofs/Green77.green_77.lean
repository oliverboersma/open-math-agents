import FormalConjectures.GreensOpenProblems.«77»
import Mathlib
/-
# Ben Green's Open Problem 77 is false

Heilbronn triangle construction: OpenAI, https://github.com/openai/math, commit
3344da59991ed94f9ba711217b29c1d760badfa6, lean/OAI/Geometry/HeilbronnTriangle
(theorem OAI.Problem355.heilbronn_power_lower_bound, family 191, "A power improvement in the
Heilbronn triangle lower bound"). Licensed under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0 . Modified: modules merged into one file, internal
identifiers shortened, several sub-arguments re-proved more compactly; the mathematics and the
final statement are those of the source. Distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND.

Bridge (new): the source gives arbitrarily large n-point sets in [0,1]^2 with every triangle of
area at least n^(-2+η), η > 0. Translating by (-1/2,-1/2) puts them in the closed unit disc, so
Erdos507.α n ≥ n^(-2+η) along a sequence n → ∞, which contradicts α ≪ n^(-2+o(1)).
-/section
namespace OAI
noncomputable section
namespace Problem355
abbrev Point := ℝ × ℝ
def ZaL (p q r : Point) : ℝ :=
 abs ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) / 2
def Zbf (p : Point) : Prop :=
 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1
def Zaz (P : Finset Point) : Prop := by
 classical
 exact ∀ p, p ∈ P → Zbf p
def Zal (P : Finset Point) (a : ℝ) : Prop := by
 classical
 exact ∀ p, p ∈ P → ∀ q, q ∈ P → ∀ r, r ∈ P →
  p ≠ q → p ≠ r → q ≠ r → a ≤ ZaL p q r
def Zae : ℕ := 41
def ZaH : ℕ := Nat.choose (4 * Zae - 1) Zae
def Zam : ℕ := ZaH ^ 3
def Za : ℕ := Zam ^ 2 + 1
def heilbronnExponent : ℝ :=
 1 / (100000 * (Za : ℝ))
end Problem355
end
end OAI
end
section
namespace OAI
namespace Problem355.ZcL
variable {G U X : Type*} [Group G] [Group U] [MulAction G X]
theorem ZkB (H N : Subgroup G) :
  H.relIndex N * N.index = H.index * N.relIndex H := by
 calc
  H.relIndex N * N.index = (H ⊓ N).index := by
   rw [← Subgroup.inf_relIndex_right H N]
   exact Subgroup.relIndex_mul_index inf_le_right
  _ = N.relIndex H * H.index := by
   rw [← Subgroup.inf_relIndex_left H N]
   exact (Subgroup.relIndex_mul_index inf_le_left).symm
  _ = H.index * N.relIndex H := Nat.mul_comm _ _
theorem stabilizer_subgroup (N : Subgroup G) (x : X) :
  (MulAction.stabilizer G x).subgroupOf N = MulAction.stabilizer N x := by
 ext g
 rfl
theorem ZiI (f : G →* U) (hf : Function.Surjective f) (x : X) :
  Nat.card (MulAction.orbit f.ker x) * Nat.card U =
   Nat.card (MulAction.orbit G x) * Nat.card ((MulAction.stabilizer G x).map f) := by
 have h := ZkB (MulAction.stabilizer G x) f.ker
 rw [Subgroup.relIndex, stabilizer_subgroup, MulAction.index_stabilizer,
  Subgroup.index_ker, f.range_eq_top_of_surjective hf,
  Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup U) ≃* U).toEquiv,
  MulAction.index_stabilizer, Subgroup.relIndex_ker] at h
 exact h
def Zjr (x : X) (g : G) :
  {a : G // a • x = g • x} ≃ MulAction.stabilizer G x where
 toFun a := ⟨g⁻¹ * a.1, by
  change (g⁻¹ * a.1) • x = x
  rw [mul_smul, a.2, inv_smul_smul]⟩
 invFun a := ⟨g * a.1, by
  rw [mul_smul, a.2]⟩
 left_inv a := by
  apply Subtype.ext
  simp
 right_inv a := by
  apply Subtype.ext
  simp
theorem ZoY (x y : X) (hy : y ∈ MulAction.orbit G x) :
  Nat.card {g : G // g • x = y} = Nat.card (MulAction.stabilizer G x) := by
 obtain ⟨g, rfl⟩ := hy
 exact Nat.card_congr (Zjr x g)
theorem Zby (x : X) :
  Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) =
   Nat.card G := by
 rw [← Nat.card_prod]
 exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)
theorem Zfz
  {o small total stab image u h D E c : ℝ}
  (ho : 0 ≤ o) (hu : 0 < u) (hh : 0 < h) (hD : 0 < D) (hE : 0 < E)
  (horbit : o * stab = total) (hkernel : small * u = o * image)
  (htotal : c * h ^ 9 ≤ total) (hstab : stab ≤ D ^ 3 * E ^ 3)
  (himage : E * u ≤ h * image) :
  c * h ^ 8 / (D ^ 3 * E ^ 2) ≤ small := by
 have hmul : (c * h ^ 8) * (h * E * u) ≤
   (small * (D ^ 3 * E ^ 2)) * (h * E * u) := by
  calc
   (c * h ^ 8) * (h * E * u) = c * h ^ 9 * (E * u) := by ring
   _ ≤ total * (E * u) := mul_le_mul_of_nonneg_right htotal (by positivity)
   _ = o * stab * (E * u) := by rw [horbit]
   _ ≤ o * (D ^ 3 * E ^ 3) * (E * u) := by
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hstab ho
    · positivity
   _ ≤ o * (D ^ 3 * E ^ 3) * (h * image) :=
    mul_le_mul_of_nonneg_left himage (by positivity)
   _ = (o * image) * (D ^ 3 * E ^ 3) * h := by ring
   _ = (small * u) * (D ^ 3 * E ^ 3) * h := by rw [hkernel]
   _ = (small * (D ^ 3 * E ^ 2)) * (h * E * u) := by ring
 apply (div_le_iff₀ (show 0 < D ^ 3 * E ^ 2 by positivity)).2
 exact le_of_mul_le_mul_right hmul (by positivity)
theorem ZnS [Finite G] [Finite U]
  (f : G →* U) (hf : Function.Surjective f) (x : X)
  {h D E c : ℝ} (hh : 0 < h) (hD : 0 < D) (hE : 0 < E)
  (htotal : c * h ^ 9 ≤ (Nat.card G : ℝ))
  (hstab : (Nat.card (MulAction.stabilizer G x) : ℝ) ≤ D ^ 3 * E ^ 3)
  (himage : E * (Nat.card U : ℝ) ≤
   h * (Nat.card ((MulAction.stabilizer G x).map f) : ℝ)) :
  c * h ^ 8 / (D ^ 3 * E ^ 2) ≤ (Nat.card (MulAction.orbit f.ker x) : ℝ) := by
 have hu : (0 : ℝ) < Nat.card U := by exact_mod_cast Nat.card_pos (α := U)
 have horbit : (Nat.card (MulAction.orbit G x) : ℝ) *
   Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  exact_mod_cast Zby (G := G) x
 have hkernel : (Nat.card (MulAction.orbit f.ker x) : ℝ) * Nat.card U =
   (Nat.card (MulAction.orbit G x) : ℝ) *
    Nat.card ((MulAction.stabilizer G x).map f) := by
  exact_mod_cast ZiI f hf x
 exact Zfz (Nat.cast_nonneg _) hu hh hD hE
  horbit hkernel htotal hstab himage
end Problem355.ZcL
end OAI
end
section
namespace OAI
namespace Problem355.Zkv
variable {G X : Type*} [Group G] [MulAction G X]
theorem ZkC [Finite G] (x y : X)
  (hy : y ∈ MulAction.orbit G x) :
  (Nat.card {g : G // g • x = y} : ℝ) / Nat.card G =
   1 / Nat.card (MulAction.orbit G x) := by
 rw [ZcL.ZoY x y hy,
  ← ZcL.Zby (G := G) x, Nat.cast_mul]
 have hs : (Nat.card (MulAction.stabilizer G x) : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer G x)).ne'
 rw [mul_comm (Nat.card (MulAction.orbit G x) : ℝ), div_mul_eq_div_div,
  div_self hs]
theorem ZfA [Fintype G] [DecidableEq X] (x y : X) :
  (∑ g : G, if g • x = y then (1 / (Nat.card G : ℝ)) else 0) =
   (Nat.card {g : G // g • x = y} : ℝ) / Nat.card G := by
 classical
 rw [Finset.sum_ite]
 simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
  mul_one_div]
 simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
theorem Zjs [Fintype G] [DecidableEq X] (x y : X)
  (hy : y ∈ MulAction.orbit G x) :
  (∑ g : G, if g • x = y then (1 / (Nat.card G : ℝ)) else 0) =
   1 / Nat.card (MulAction.orbit G x) := by
 rw [ZfA]
 exact ZkC x y hy
theorem Zho [Fintype G] [DecidableEq X] (x y : X)
  (hy : y ∉ MulAction.orbit G x) :
  (∑ g : G, if g • x = y then (1 / (Nat.card G : ℝ)) else 0) = 0 := by
 apply Finset.sum_eq_zero
 intro g _
 apply if_neg
 intro hg
 exact hy ⟨g, hg⟩
end Problem355.Zkv
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.CRT
def Zqy (N : ℕ) (t : ℤ) : Fin N ≃ Set.Ico t (t + N) where
 toFun j := ⟨t + j.val, by constructor <;> omega⟩
 invFun x := ⟨(x.val - t).toNat, by
  have hx : t ≤ x.val ∧ x.val < t + N := x.property
  omega⟩
 left_inv j := by
  apply Fin.ext
  simp
 right_inv x := by
  apply Subtype.ext
  have hx : t ≤ x.val ∧ x.val < t + N := x.property
  change t + ↑(x.val - t).toNat = x.val
  omega
def ZmB (m t : ℕ) [NeZero m] (r : ZMod m) :
  {x : Fin (t * m) // (x.val : ZMod m) = r} ≃ Fin t where
 toFun x := x.val.divNat
 invFun y := ⟨finProdFinEquiv (y, ⟨r.val, r.val_lt⟩), by
  change ((r.val + m * y.val : ℕ) : ZMod m) = r
  simp⟩
 left_inv x := by
  apply Subtype.ext
  apply Fin.ext
  change r.val + m * (x.val.val / m) = x.val.val
  have hr : x.val.val % m = r.val := by
   simpa using congrArg ZMod.val x.property
  rw [← hr]
  exact Nat.mod_add_div _ _
 right_inv y := by
  apply Fin.ext
  change (r.val + m * y.val) / m = y.val
  rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero (NeZero.ne m)),
   Nat.div_eq_of_lt r.val_lt, Nat.zero_add]
def ZpB (h q t : ℕ) [NeZero h] [NeZero q]
  (hc : h.Coprime q) (s : ℤ) (a : ZMod h) (b : ZMod q) :
  {x : Set.Ico s (s + (t * (h * q) : ℕ)) //
   (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b} ≃ Fin t := by
 let c := (ZMod.chineseRemainder hc).symm (a,b) - (s : ZMod (h*q))
 refine ((Zqy _ s).subtypeEquiv (p := fun x => (x.val : ZMod (h*q)) = c) ?_).symm.trans (ZmB _ _ c)
 intro x
 change ((x.val : ZMod (h*q)) = c) ↔ (((s + x.val : ℤ) : ZMod h) = a ∧ ((s + x.val : ℤ) : ZMod q) = b)
 rw [show c = _ from rfl, eq_sub_iff_add_eq, ← (ZMod.chineseRemainder hc).injective.eq_iff]
 simp [Prod.ext_iff, add_comm]
end Problem355.CRT
end
end OAI
end
section
namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem355.Zb
theorem Zij {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
  (f : X → Y) (M : ℕ)
  (hf : ∀ y, (Finset.univ.filter (fun x => f x = y)).card = M)
  (p : Y → ℝ) :
  (∑ x, p (f x)) = (M : ℝ) * ∑ y, p y := by
 classical
 simpa [hf, Finset.mul_sum] using (Finset.sum_fiberwise' Finset.univ f p).symm
abbrev ZmC {B : Type*} (V : Finset B) (b : Fin 3 → B) : Prop :=
 ∀ i, b i ∈ V
def Zbb {Ω B : Type*} [Fintype Ω]
   (w : Ω → ℝ) (V : Ω → Finset B) (b : Fin 3 → B) : ℝ := by
  classical
  exact ∑ ω, if ZmC (V ω) b then w ω else 0
 theorem ZgG {Ω B : Type*} [Fintype Ω]
   (w : Ω → ℝ) (V : Ω → Finset B) (hw : ∀ ω, 0 ≤ w ω) (b : Fin 3 → B) :
   0 ≤ Zbb w V b := by
  classical
  unfold Zbb
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp_all
def ZdL {A : Type*} (O : Finset A) (a : A) : ℝ := by
 classical
 exact if a ∈ O then 1 / (O.card : ℝ) else 0
theorem ZpC {A : Type*} (O : Finset A) (a : A) : 0 ≤ ZdL O a := by
 classical
 unfold ZdL
 split_ifs <;> positivity
def ZaI {X A Ω B : Type*} [Fintype Ω]
  (f : X → A) (g : X → (Fin 3 → B))
  (O : Finset A) (w : Ω → ℝ) (V : Ω → Finset B) (s M : ℕ) (x : X) : ℝ :=
 ZdL O (f x) * (Zbb w V (g x) / (s : ℝ)^3) / M
theorem Zow {X A Ω B : Type*} [Fintype Ω]
  (f : X → A) (g : X → (Fin 3 → B))
  (O : Finset A) (w : Ω → ℝ) (V : Ω → Finset B) (s M : ℕ)
  (hw : ∀ ω, 0 ≤ w ω) (x : X) :
  0 ≤ ZaI f g O w V s M x :=
 div_nonneg (mul_nonneg (ZpC ..) (div_nonneg (ZgG w V hw _) (by positivity))) (by positivity)
def Zk {Ω B : Type*} [Fintype Ω]
  (q s : ℕ) (w : Ω → ℝ) (V : Ω → Finset B) (b : Fin 3 → B) : ℝ :=
 (((q : ℝ) ^ 3) / (s : ℝ)) ^ 3 * Zbb w V b
theorem ZkY {X A Ω B : Type*} [Fintype Ω] [DecidableEq A]
  (f : X → A) (g : X → (Fin 3 → B))
  (O : Finset A) (hO : O.Nonempty) (w : Ω → ℝ) (V : Ω → Finset B)
  (s h q L : ℕ) (hs : 0 < s) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L)
  (E : Finset X) :
  (∑ x ∈ E, ZaI f g O w V s (L ^ 9) x) =
   (h : ℝ) ^ 9 / ((L * (h * q) : ℕ) ^ 9 * (O.card : ℝ)) *
    ∑ x ∈ E.filter (fun x => f x ∈ O), Zk q s w V (g x) := by
 classical
 rw [Finset.sum_filter, Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro x hx
 simp only [ZaI, ZdL, Zk, Nat.cast_mul, Nat.cast_pow]
 split_ifs <;> field_simp <;> simp
def Zaf {X A B : Type*}
  (f : X → A) (g : X → B) (a : A) (V : Finset B) (s L : ℕ) (x : X) : ℝ := by
 classical
 exact if f x = a ∧ g x ∈ V then 1 / ((s : ℝ) * (L : ℝ) ^ 3) else 0
theorem ZhI {X A B : Type*}
  (f : X → A) (g : X → B) (a : A) (V : Finset B) (s L : ℕ) (x : X) :
  0 ≤ Zaf f g a V s L x := by
 classical
 unfold Zaf
 split_ifs <;> positivity
theorem Zhp {X A B : Type*} [DecidableEq A] [DecidableEq B]
  (f : X → A) (g : X → B) (a : Fin 3 → A) (V : Finset B) (s L : ℕ)
  (x : Fin 3 → X) :
  (∏ i, Zaf f g (a i) V s L (x i)) =
   if (fun i => f (x i)) = a ∧ ZmC V (fun i => g (x i)) then
    1 / ((s : ℝ) ^ 3 * (L : ℝ) ^ 9) else 0 := by
 classical
 simp [Zaf, Fintype.prod_ite_zero, funext_iff, forall_and, ZmC, mul_pow, ← pow_mul]
theorem ZiJ {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]
  (ρ : Θ → ℝ) (w : Ω → ℝ) (P : Θ → Prop) (Q : Ω → Prop)
  [DecidablePred P] [DecidablePred Q] (K : ℝ) :
  (∑ θ, ρ θ * ∑ ω, w ω * (if P θ ∧ Q ω then K else 0)) =
   (∑ θ, if P θ then ρ θ else 0) * (∑ ω, if Q ω then w ω else 0) * K := by
 classical
 calc
  (∑ θ, ρ θ * ∑ ω, w ω * (if P θ ∧ Q ω then K else 0)) =
     ∑ θ, (if P θ then ρ θ else 0) * ((∑ ω, if Q ω then w ω else 0) * K) := by
   apply Finset.sum_congr rfl
   intro θ hθ
   by_cases hP : P θ
   · simp only [hP, true_and, ite_true]
     congr 1
     rw [Finset.sum_mul]
     apply Finset.sum_congr rfl
     intro ω hω
     by_cases hQ : Q ω <;> simp [hQ]
   · simp [hP]
  _ = _ := by rw [← Finset.sum_mul, mul_assoc]
def Zew {Θ A : Type*} [Fintype Θ]
  (ρ : Θ → ℝ) (F : Θ → A) (a : A) : ℝ := by
 classical
 exact ∑ θ, if a = F θ then ρ θ else 0
theorem ZgH
  {X A B Θ Ω : Type*} [Fintype Θ] [Fintype Ω]
  (f : X → A) (g : X → B) (F : Θ → (Fin 3 → A))
  (ρ : Θ → ℝ) (w : Ω → ℝ) (V : Ω → Finset B)
  (O : Finset (Fin 3 → A)) (s L : ℕ)
  (hpush : ∀ a, Zew ρ F a = ZdL O a)
  (x : Fin 3 → X) :
  (∑ θ, ρ θ * ∑ ω, w ω *
   ∏ i, Zaf f g (F θ i) (V ω) s L (x i)) =
   ZaI (fun x i => f (x i)) (fun x i => g (x i))
    O w V s (L ^ 9) x := by
 classical
 simp_rw [Zhp]
 rw [ZiJ]
 have H := hpush (fun i => f (x i))
 unfold Zew at H
 simp only [ZaI, Zbb]
 rw [← H]
 simp only [Nat.cast_pow, div_eq_mul_inv, mul_inv_rev]
 ring
end Problem355.Zb
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zc
abbrev Box (N d : ℕ) (shift : Fin d → ℤ) :=
 (i : Fin d) → Set.Ico (shift i) (shift i + N)
def residue (m : ℕ) {N d : ℕ} {shift : Fin d → ℤ} (x : Box N d shift) :
 Fin d → ZMod m := fun i => ((x i).val : ZMod m)
theorem ZjU (h q L d : ℕ) [NeZero h] [NeZero q]
  (hc : h.Coprime q) (shift : Fin d → ℤ)
  (r : (Fin d → ZMod h) × (Fin d → ZMod q)) :
  (Finset.univ.filter (fun x : Box (L * (h * q)) d shift =>
   (residue h x, residue q x) = r)).card = L ^ d := by
 classical
 rw [← Fintype.card_subtype]
 suffices e : Nonempty ({x : Box (L*(h*q)) d shift // (residue h x,residue q x) = r} ≃ (Fin d → Fin L)) by simpa using Fintype.card_congr e.some
 refine ⟨(Equiv.subtypeEquivRight (q := fun x => ∀ i, ((x i).val : ZMod h) = r.1 i ∧ ((x i).val : ZMod q) = r.2 i) ?_).trans (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight fun i => CRT.ZpB h q L hc _ _ _))⟩
 intro x
 simp only [Prod.ext_iff, residue, funext_iff, forall_and]
def ZeJ (h q L : ℕ) (shift : Fin 3 → ℤ)
   (a : Fin 3 → ZMod h) (V : Finset (Fin 3 → ZMod q)) (s : ℕ)
   (x : Box (L * (h * q)) 3 shift) : ℝ :=
  Zb.Zaf (residue h) (residue q) a V s L x
 theorem ZjV (h q L : ℕ) (shift : Fin 3 → ℤ)
   (a : Fin 3 → ZMod h) (V : Finset (Fin 3 → ZMod q)) (s : ℕ)
   (x : Box (L * (h * q)) 3 shift) : 0 ≤ ZeJ h q L shift a V s x :=
  Zb.ZhI (residue h) (residue q) a V s L x
theorem Zqz (h q L : ℕ) [NeZero h] [NeZero q]
  (hc : h.Coprime q) (hL : 0 < L) (shift : Fin 3 → ℤ)
  (a : Fin 3 → ZMod h) (V : Finset (Fin 3 → ZMod q)) (s : ℕ)
  (hs : 0 < s) (hV : V.card = s) :
  (∑ x, ZeJ h q L shift a V s x) = 1 := by
 classical
 let p : (Fin 3 → ZMod h) × (Fin 3 → ZMod q) → ℝ := fun r => if r.1 = a ∧ r.2 ∈ V then 1 / ((s : ℝ)*L^3) else 0
 suffices H : ∑ x : Box (L*(h*q)) 3 shift, p (residue h x,residue q x) = 1 by simpa [p,ZeJ,Zb.Zaf] using H
 rw [Zb.Zij _ _ (ZjU h q L 3 hc shift) p, Fintype.sum_prod_type]
 simp [p, ite_and, hV, Nat.cast_pow]
 field_simp
def Zm (N : ℕ) : Fin 3 → ℤ := ![0, 0, (N : ℤ)]
def project {N : ℕ} (x : Box N 3 (Zm N)) : Point :=
 (((x 0).val : ℝ) / ((x 2).val : ℝ), ((x 1).val : ℝ) / ((x 2).val : ℝ))
theorem ZlN {N : ℕ} (hN : 0 < N)
  (x : Box N 3 (Zm N)) : Zbf (project x) := by
 have hx : 0 ≤ (x 0).val ∧ (x 0).val < (N : ℤ) := by
  simpa [Zm] using (x 0).property
 have hy : 0 ≤ (x 1).val ∧ (x 1).val < (N : ℤ) := by
  simpa [Zm] using (x 1).property
 have hz : (N : ℤ) ≤ (x 2).val ∧ (x 2).val < (N : ℤ) + N := by
  exact (x 2).property
 have hzpos : 0 < ((x 2).val : ℝ) := by
  have : (0 : ℤ) < (x 2).val := lt_of_lt_of_le (by exact_mod_cast hN) hz.1
  exact_mod_cast this
 unfold Zbf project
 exact ⟨div_nonneg (by exact_mod_cast hx.1) hzpos.le,
  (div_le_one hzpos).mpr (by exact_mod_cast hx.2.le.trans hz.1),
  div_nonneg (by exact_mod_cast hy.1) hzpos.le,
  (div_le_one hzpos).mpr (by exact_mod_cast hy.2.le.trans hz.1)⟩
end Problem355.Zc
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZD
def Zt (G : Type*) {X : Type*} [Group G] [MulAction G X] [Fintype X]
   (x : X) : Finset X := by
  classical
  exact Finset.univ.filter (fun y => y ∈ MulAction.orbit G x)
 theorem Zcc {G X : Type*} [Group G] [MulAction G X] [Fintype X]
   (x y : X) : y ∈ Zt G x ↔ y ∈ MulAction.orbit G x := by
  classical
  simp [Zt]
 theorem ZmD {G X : Type*} [Group G] [MulAction G X] [Fintype X]
   (x : X) : (Zt G x).Nonempty := by
  exact ⟨x, (Zcc x x).mpr (MulAction.mem_orbit_self x)⟩
 theorem ZjW {G X : Type*} [Group G] [MulAction G X] [Fintype X]
   (x : X) : (Zt G x).card = Nat.card (MulAction.orbit G x) := by
  classical
  simp only [Zt, Nat.card_eq_fintype_card, Fintype.card_subtype]
theorem Znq {G X : Type*} [Group G] [Fintype G]
   [MulAction G X] [Fintype X] (x y : X) :
   Zb.Zew (fun _ : G => 1 / (Nat.card G : ℝ))
    (fun g => g • x) y = Zb.ZdL (Zt G x) y := by
 classical
 unfold Zb.Zew
 simp_rw [eq_comm (a := y)]
 by_cases hy : y ∈ MulAction.orbit G x
 · rw [Zkv.Zjs x y hy]
   have hym := (Zcc x y).mpr hy
   simp [Zb.ZdL, hym, ZjW]
 · rw [Zkv.Zho x y hy]
   have hym : y ∉ Zt G x := mt (Zcc x y).mp hy
   simp [Zb.ZdL, hym]
abbrev Zz (h : ℕ) := Matrix.SpecialLinearGroup (Fin 3) (ZMod h)
theorem ZfB {Ω : Type*} [Fintype Ω]
  (h q L : ℕ) [NeZero h] [NeZero q] (shift : Fin 3 → ℤ)
  (C : Fin 3 → Fin 3 → ZMod h) (w : Ω → ℝ)
  (V : Ω → Finset (Fin 3 → ZMod q)) (s : ℕ)
  (x : Fin 3 → Zc.Box (L * (h * q)) 3 shift) :
  (∑ G : Zz h, (1 / (Nat.card (Zz h) : ℝ)) *
   ∑ ω, w ω * ∏ i,
    Zc.ZeJ h q L shift ((G • C) i) (V ω) s (x i)) =
   Zb.ZaI
    (fun x i => Zc.residue h (x i))
    (fun x i => Zc.residue q (x i))
    (Zt (Zz h) C) w V s (L ^ 9) x := by
 classical
 exact Zb.ZgH
  (Zc.residue h) (Zc.residue q)
  (fun G : Zz h => G • C) (fun _ => 1 / (Nat.card (Zz h) : ℝ))
  w V (Zt (Zz h) C) s L (Znq C) x
theorem ZbN (h : ℕ) (G : Zz h)
  (C : Fin 3 → Fin 3 → ZMod h) :
  Matrix.transpose (G • C) = G.val * Matrix.transpose C := by
 ext i j
 rfl
def Zg {N : ℕ} {shift : Fin 3 → ℤ}
  (x : Fin 3 → Zc.Box N 3 shift) : Matrix (Fin 3) (Fin 3) ℤ :=
 fun i j => (x j i).val
theorem ZeE (h q L : ℕ) [NeZero h]
  (shift : Fin 3 → ℤ) (C : Fin 3 → Fin 3 → ZMod h)
  (x : Fin 3 → Zc.Box (L * (h * q)) 3 shift)
  (hx : (fun i => Zc.residue h (x i)) ∈ Zt (Zz h) C) :
  ∃ G : Zz h, (Zg x).map (Int.cast : ℤ → ZMod h) =
   G.val * Matrix.transpose C := by
 obtain ⟨G, hG⟩ := (Zcc C _).mp hx
 refine ⟨G, ?_⟩
 change Matrix.transpose (fun i => Zc.residue h (x i)) = G.val * Matrix.transpose C
 rw [← hG, ZbN]
end Problem355.ZD
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Homogeneous
abbrev ZaA := Fin 3 → ℝ
def project (u : ZaA) : ℝ × ℝ := (u 0 / u 2, u 1 / u 2)
def Zcd (u v w : ZaA) : Matrix (Fin 3) (Fin 3) ℝ :=
 !![u 0, v 0, w 0; u 1, v 1, w 1; u 2, v 2, w 2]
theorem ZoZ (u v w : ZaA)
  (hu : u 2 ≠ 0) (hv : v 2 ≠ 0) (hw : w 2 ≠ 0) :
  ((v 0 / v 2 - u 0 / u 2) * (w 1 / w 2 - u 1 / u 2) -
   (v 1 / v 2 - u 1 / u 2) * (w 0 / w 2 - u 0 / u 2)) =
   (Zcd u v w).det / (u 2 * v 2 * w 2) := by
 simp [Zcd, Matrix.det_fin_three]
 field_simp
 ring
theorem ZpD (u v w : ZaA)
  (hu : 0 < u 2) (hv : 0 < v 2) (hw : 0 < w 2) :
  ZaL (project u) (project v) (project w) =
   |(Zcd u v w).det| / (2 * u 2 * v 2 * w 2) := by
 unfold ZaL project
 dsimp only
 rw [ZoZ u v w (ne_of_gt hu) (ne_of_gt hv) (ne_of_gt hw),
  abs_div, abs_of_pos (mul_pos (mul_pos hu hv) hw), div_div]
 congr 1
 ring
def ZaX (N : ℝ) (u : ZaA) : Prop :=
 0 ≤ u 0 ∧ u 0 < N ∧ 0 ≤ u 1 ∧ u 1 < N ∧ N ≤ u 2 ∧ u 2 < 2 * N
theorem ZjX {N τ : ℝ} (hN : 0 < N) (hτ : 0 ≤ τ)
  (u v w : ZaA)
  (hu : N ≤ u 2) (hu' : u 2 ≤ 2 * N)
  (hv : N ≤ v 2) (hv' : v 2 ≤ 2 * N)
  (hw : N ≤ w 2) (hw' : w 2 ≤ 2 * N)
  (hdet : τ ≤ |(Zcd u v w).det|) :
  τ / (16 * N ^ 3) ≤ ZaL (project u) (project v) (project w) := by
 have hu0 : 0 < u 2 := lt_of_lt_of_le hN hu
 have hv0 : 0 < v 2 := lt_of_lt_of_le hN hv
 have hw0 : 0 < w 2 := lt_of_lt_of_le hN hw
 have hden0 : 0 < 2 * u 2 * v 2 * w 2 := by positivity
 have hden : 2 * u 2 * v 2 * w 2 ≤ 16 * N ^ 3 := by
  calc
   2 * u 2 * v 2 * w 2 ≤ 2 * (2 * N) * (2 * N) * (2 * N) := by gcongr
   _ = 16 * N ^ 3 := by ring
 rw [ZpD u v w hu0 hv0 hw0]
 exact (div_le_div_of_nonneg_left hτ hden0 hden).trans
  (div_le_div_of_nonneg_right hdet hden0.le)
theorem Zgt {N τ : ℝ} (hN : 0 < N) (hτ : 0 ≤ τ)
  {u v w : ZaA} (hu : ZaX N u) (hv : ZaX N v) (hw : ZaX N w)
  (hdet : τ ≤ |(Zcd u v w).det|) :
  τ / (16 * N ^ 3) ≤ ZaL (project u) (project v) (project w) :=
 ZjX hN hτ u v w hu.2.2.2.2.1 hu.2.2.2.2.2.le
  hv.2.2.2.2.1 hv.2.2.2.2.2.le hw.2.2.2.2.1 hw.2.2.2.2.2.le hdet
end Problem355.Homogeneous
end
end OAI
end
section
namespace OAI
namespace Problem355.ZaW
theorem ZhJ {α : Type*} (S : Finset α)
   (F : Finset (Finset α)) (hne : ∀ B ∈ F, B.Nonempty) :
   ∃ T : Finset α, T ⊆ S ∧ S.card ≤ T.card + F.card ∧
    ∀ B ∈ F, ¬ B ⊆ T := by
 classical
 let chooseVertex (B : {B // B ∈ F}) : α := (hne B.1 B.2).choose
 have chooseVertex_mem (B : {B // B ∈ F}) : chooseVertex B ∈ B.1 :=
   (hne B.1 B.2).choose_spec
 let D : Finset α := F.attach.image chooseVertex
 have hD : D.card ≤ F.card := by
   calc
    D.card ≤ F.attach.card := Finset.card_image_le
    _ = F.card := Finset.card_attach
 refine ⟨S \ D, Finset.sdiff_subset, ?_, ?_⟩
 · exact (Finset.card_le_card_sdiff_add_card (s := S) (t := D)).trans (Nat.add_le_add_left hD _)
 · intro B hB hBT
   let b : {B // B ∈ F} := ⟨B, hB⟩
   have hbD : chooseVertex b ∈ D := Finset.mem_image.mpr ⟨b, Finset.mem_attach _ _, rfl⟩
   exact (Finset.mem_sdiff.mp (hBT (chooseVertex_mem b))).2 hbD
theorem ZgI {α : Type*} (S : Finset α)
  (F : Finset (Finset α)) (hne : ∀ B ∈ F, B.Nonempty)
  (n : ℕ) (hbudget : n + F.card ≤ S.card) :
  ∃ T : Finset α, T ⊆ S ∧ T.card = n ∧ ∀ B ∈ F, ¬ B ⊆ T := by
 obtain ⟨U, hUS, hcard, havoid⟩ := ZhJ S F hne
 have hnU : n ≤ U.card := by omega
 obtain ⟨T, hTU, hTcard⟩ := Finset.exists_subset_card_eq hnU
 exact ⟨T, hTU.trans hUS, hTcard, fun B hB hBT => havoid B hB (hBT.trans hTU)⟩
theorem Zik {Ω I : Type*} [Fintype Ω] (W : Ω → ℝ) (E : Finset I)
  (bad : Ω → I → Prop) [∀ z, DecidablePred (bad z)] (b : ℝ)
  (h : ∀ i ∈ E, (∑ z, if bad z i then W z else 0) ≤ b) :
  (∑ z, W z * (E.filter (bad z)).card) ≤ E.card * b := by
 classical
 calc
  _ = ∑ z, ∑ i ∈ E, if bad z i then W z else 0 := by
   apply Finset.sum_congr rfl
   intro z _
   rw [← Finset.sum_filter]
   simp [mul_comm]
  _ = _ := Finset.sum_comm
  _ ≤ ∑ _ ∈ E, b := Finset.sum_le_sum h
  _ = _ := by simp
theorem ZfY {Ω : Type*} (outcomes : Finset Ω)
  (weight : Ω → ℝ) (g : Ω → ℕ) (m : ℕ)
  (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω)
  (hnorm : ∑ ω ∈ outcomes, weight ω = 1)
  (hmean : (∑ ω ∈ outcomes, weight ω * g ω) < (m : ℝ)) :
  ∃ ω ∈ outcomes, g ω < m := by
 by_contra hnone
 push Not at hnone
 have hle : (m : ℝ) ≤ ∑ ω ∈ outcomes, weight ω * g ω := by
  calc
   (m : ℝ) = ∑ ω ∈ outcomes, weight ω * m := by
    rw [← Finset.sum_mul, hnorm, one_mul]
   _ ≤ _ := Finset.sum_le_sum fun ω hω =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast hnone ω hω) (hweight ω hω)
 exact (not_lt_of_ge hle) hmean
def Zbo (a : ℝ) (p q r : Point) : Prop :=
 p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ ZaL p q r < a
theorem Znr {ι : Type*} (T : Finset ι) (f : ι → Point) (a : ℝ)
   (hinj : Set.InjOn f (T : Set ι))
   (hsquare : ∀ i ∈ T, Zbf (f i))
   (hgood : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,
    i ≠ j → i ≠ k → j ≠ k → ¬ Zbo a (f i) (f j) (f k)) :
   ∃ P : Finset Point, P.card = T.card ∧ Zaz P ∧
    Zal P a := by
 classical
 refine ⟨T.image f, Finset.card_image_of_injOn hinj, ?_, ?_⟩
 · intro p hp
   obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
   exact hsquare i hi
 · intro p hp q hq r hr hpq hpr hqr
   obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
   obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
   obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
   have hij : i ≠ j := fun h => hpq (congrArg f h)
   have hik : i ≠ k := fun h => hpr (congrArg f h)
   have hjk : j ≠ k := fun h => hqr (congrArg f h)
   apply le_of_not_gt
   intro harea
   exact hgood i hi j hj k hk hij hik hjk ⟨hpq, hpr, hqr, harea⟩
end Problem355.ZaW
end OAI
end
section
namespace OAI
namespace Problem355.ZiD
lemma Zox {h τ a b : ℤ} (hwidth : 2 * τ < h)
  (ha : |a| ≤ τ) (hb : |b| ≤ τ) (hab : a ≡ b [ZMOD h]) : a = b := by
 have ha' := abs_le.mp ha
 have hb' := abs_le.mp hb
 have hdist : |b - a| < h := by
  rw [abs_lt]
  omega
 have hz := Int.eq_zero_of_abs_lt_dvd (Int.modEq_iff_dvd.mp hab) hdist
 omega
lemma Zns {h : ℕ} {τ a b : ℤ} (hwidth : 2 * τ < h)
  (ha : |a| ≤ τ) (hb : |b| ≤ τ) (hab : (a : ZMod h) = b) : a = b :=
 Zox hwidth ha hb ((ZMod.intCast_eq_intCast_iff a b h).mp hab)
lemma ZlO {α : Type*} [DecidableEq α] (s : Finset α)
   (d : α → ℤ) {h : ℕ} {τ : ℤ} (hwidth : 2 * τ < h)
   (c : ZMod h) (hres : ∀ x ∈ s, (d x : ZMod h) = c)
   {a : α} (ha : a ∈ s) (hasmall : |d a| ≤ τ) :
   s.filter (fun x => |d x| ≤ τ) = s.filter (fun x => d x = d a) := by
 ext x
 simp only [Finset.mem_filter]
 constructor
 · rintro ⟨hx, hsmall⟩
   exact ⟨hx, Zns hwidth hsmall hasmall
    ((hres x hx).trans (hres a ha).symm)⟩
 · rintro ⟨hx, heq⟩
   exact ⟨hx, heq ▸ hasmall⟩
lemma Zil {α : Type*} [DecidableEq α]
   (s : Finset α) (d : α → ℤ) (w : α → ℝ) {h : ℕ} {τ : ℤ}
   (hwidth : 2 * τ < h) (c : ZMod h)
   (hres : ∀ x ∈ s, (d x : ZMod h) = c) {B : ℝ} (hB : 0 ≤ B)
   (hfiber : ∀ t : ℤ, |t| ≤ τ → ∑ x ∈ s.filter (fun x => d x = t), w x ≤ B) :
   ∑ x ∈ s.filter (fun x => |d x| ≤ τ), w x ≤ B := by
 by_cases hempty : (s.filter (fun x => |d x| ≤ τ)).Nonempty
 · obtain ⟨a, ha⟩ := hempty
   have hamem := (Finset.mem_filter.mp ha).1
   have hasmall := (Finset.mem_filter.mp ha).2
   rw [ZlO s d hwidth c hres hamem hasmall]
   exact hfiber (d a) hasmall
 · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
   simpa using hB
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma cast_det (h : ℕ) (A : Matrix ι ι ℤ) :
  (A.det : ZMod h) = (A.map (Int.castRingHom (ZMod h))).det := by
 exact (Int.castRingHom (ZMod h)).map_det A
end Problem355.ZiD
end OAI
end
section
namespace OAI
namespace Problem355.Zkw
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem ZkZ (f : α → α → α → ℝ) (M : ℝ)
  (hM : 0 ≤ M) (hbound : ∀ a b c, f a b c ≤ M)
  (hzero : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → f a b c = 0) :
  (∑ a, ∑ b, ∑ c, f a b c) ≤ 3 * (Fintype.card α : ℝ) ^ 2 * M := by
 have hpoint (a b c : α) : f a b c ≤
    (if a = b then M else 0) + (if a = c then M else 0) +
     (if b = c then M else 0) := by
  have hf := hbound a b c
  by_cases hab : a = b
  · simp only [if_pos hab]
    split_ifs <;> linarith
  by_cases hac : a = c
  · simp only [if_neg hab, if_pos hac, zero_add]
    split_ifs <;> linarith
  by_cases hbc : b = c
  · simp only [if_neg hab, if_neg hac, if_pos hbc, zero_add]
    exact hf
  simp only [if_neg hab, if_neg hac, if_neg hbc, add_zero,
    hzero a b c hab hac hbc, le_refl]
 calc
  (∑ a, ∑ b, ∑ c, f a b c) ≤
     ∑ a : α, ∑ b : α, ∑ c : α,
      ((if a = b then M else 0) + (if a = c then M else 0) +
       (if b = c then M else 0)) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    exact Finset.sum_le_sum fun c hc => hpoint a b c
  _ = 3 * (Fintype.card α : ℝ) ^ 2 * M := by
    simp only [Finset.sum_add_distrib]
    simp
    ring
theorem ZiK [Nonempty α]
  (f : α → α → α → ℝ) (M : ℝ)
  (hM : 0 ≤ M) (hbound : ∀ a b c, f a b c ≤ M)
  (hzero : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → f a b c = 0) :
  (∑ a, ∑ b, ∑ c, f a b c) / (Fintype.card α : ℝ) ^ 3 ≤
   3 * M / (Fintype.card α : ℝ) := by
 have hcard : 0 < (Fintype.card α : ℝ) := by
  exact_mod_cast Fintype.card_pos
 apply (div_le_iff₀ (pow_pos hcard 3)).2
 calc
  (∑ a, ∑ b, ∑ c, f a b c) ≤
    3 * (Fintype.card α : ℝ) ^ 2 * M :=
   ZkZ f M hM hbound hzero
  _ = 3 * M / (Fintype.card α : ℝ) * (Fintype.card α : ℝ) ^ 3 := by
   field_simp
end Problem355.Zkw
end OAI
end
section
namespace OAI
namespace Problem355.Zkw
open Finset
variable {α Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype Ω]
theorem ZhK
  {h N D E orbit c₀ C L mass : ℝ}
  (hh : 0 < h) (hN : 0 < N) (hD : 0 < D) (hE : 0 < E)
  (ho : 0 < orbit) (hc₀ : 0 < c₀)
  (hmass : 0 ≤ mass)
  (horbit : c₀ * h ^ 8 / (D ^ 3 * E ^ 2) ≤ orbit)
  (hcount : mass ≤ C * L ^ 2 * N ^ 6 / (D ^ 2 * E ^ 2)) :
  h ^ 9 / (N ^ 9 * orbit) * mass ≤
   (C / c₀) * L ^ 2 * h * D / N ^ 3 := by
 have hinv : 1 / orbit ≤ (D ^ 3 * E ^ 2) / (c₀ * h ^ 8) := by
  apply (div_le_div_iff₀ ho (by positivity)).2
  have hl := (div_le_iff₀ (by positivity : 0 < D ^ 3 * E ^ 2)).1 horbit
  simpa only [one_mul, mul_one, mul_comm] using hl
 calc
  h ^ 9 / (N ^ 9 * orbit) * mass = (h ^ 9 / N ^ 9) * (1 / orbit) * mass := by
   ring
  _ ≤ (h ^ 9 / N ^ 9) * ((D ^ 3 * E ^ 2) / (c₀ * h ^ 8)) * mass :=
   mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinv (by positivity)) hmass
  _ ≤ (h ^ 9 / N ^ 9) * ((D ^ 3 * E ^ 2) / (c₀ * h ^ 8)) *
    (C * L ^ 2 * N ^ 6 / (D ^ 2 * E ^ 2)) :=
   mul_le_mul_of_nonneg_left hcount (by positivity)
  _ = (C / c₀) * L ^ 2 * h * D / N ^ 3 := by
   field_simp
end Problem355.Zkw
end OAI
end
section
namespace OAI
namespace Problem355.Zcn
open Finset
theorem ZkD {h τ s x : ℤ}
   (hh : 0 < h) (hτ : 2 * τ < h)
   (hs : 2 * |s| < h) (hsτ : τ < |s|)
   (hx : x ≡ s [ZMOD h]) : τ < |x| := by
 by_contra hn
 have hxτ : |x| ≤ τ := le_of_not_gt hn
 obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp hx
 by_cases hm0 : m = 0
 · subst m
   simp only [mul_zero, sub_eq_zero] at hm
   subst s
   omega
 · have hm1 : 1 ≤ |m| := Int.one_le_abs hm0
   have htri : |s - x| ≤ |s| + |x| := abs_sub s x
   rw [hm, abs_mul, abs_of_pos hh] at htri
   have hsmall : 2 * |x| < h :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hxτ (by omega)) hτ
   nlinarith only [hsmall, hs, htri, hm1, hh]
theorem Zjm (B : ℤ) (hB : 2 ≤ B) (E : ℕ → ℤ)
   (k : ℕ) (hE : ∀ i < k, 50 * |E i| ≤ 3 * (B - 1)) :
   50 * |∑ i ∈ range k, E i * B ^ i| ≤ 3 * (B ^ k - 1) := by
 induction k with
 | zero => simp
 | succ k ih =>
   have hprev := ih (fun i hi => hE i (Nat.lt_succ_of_lt hi))
   have hk := hE k (Nat.lt_succ_self k)
   have hpow : 0 ≤ B ^ k := pow_nonneg (by omega) k
   have htri := abs_add_le (∑ i ∈ range k, E i * B ^ i) (E k * B ^ k)
   rw [abs_mul, abs_of_nonneg hpow] at htri
   rw [sum_range_succ, pow_succ]
   nlinarith
theorem Zjt (B : ℤ) (hB : 2 ≤ B) (E : ℕ → ℤ)
  (k : ℕ) (hE : ∀ i < k, 50 * |E i| ≤ 3 * (B - 1))
  (hk : E k ≠ 0) :
  47 * B ^ k + 3 ≤ 50 * |∑ i ∈ range (k + 1), E i * B ^ i| := by
 have hprev := Zjm B hB E k hE
 have hpow : 0 ≤ B ^ k := pow_nonneg (by omega) k
 have hk1 : 1 ≤ |E k| := Int.one_le_abs hk
 have htri := abs_sub (∑ i ∈ range (k + 1), E i * B ^ i)
  (∑ i ∈ range k, E i * B ^ i)
 rw [sum_range_succ, add_sub_cancel_left, abs_mul, abs_of_nonneg hpow] at htri
 rw [sum_range_succ]
 nlinarith
theorem Zoy (B : ℤ) (hB : 2 ≤ B) (E : ℕ → ℤ)
   (k : ℕ) (hE : ∀ i < k + 1, 50 * |E i| ≤ 3 * (B - 1))
   (hk : E k ≠ 0) {x : ℤ}
   (hx : x ≡ ∑ i ∈ range (k + 1), E i * B ^ i [ZMOD B ^ (k + 1)]) :
   B ^ k / 2 < |x| := by
 have hfull := Zjm B hB E (k + 1) hE
 have hlead := Zjt B hB E k
   (fun i hi => hE i (Nat.lt_succ_of_lt hi)) hk
 have hp : 0 < B ^ k := pow_pos (by omega) k
 have hh : 0 < B ^ (k + 1) := pow_pos (by omega) (k + 1)
 have hdiv : 2 * (B ^ k / 2) ≤ B ^ k := by omega
 have hsmall : 2 * (B ^ k / 2) < B ^ (k + 1) := by
   rw [pow_succ]
   nlinarith
 apply ZkD hh hsmall _ _ hx
 · nlinarith
 · nlinarith
theorem Zpa (B : ℤ) (E : ℕ → ℤ) (k m : ℕ) (hkm : k ≤ m) :
   (∑ i ∈ range m, E i * B ^ i) ≡
    (∑ i ∈ range k, E i * B ^ i) [ZMOD B ^ k] := by
 induction m, hkm using Nat.le_induction with
 | base => exact Int.ModEq.refl _
 | succ m hkm ih =>
   rw [sum_range_succ]
   have hdvd : B ^ k ∣ E m * B ^ m :=
    dvd_mul_of_dvd_right (pow_dvd_pow B hkm) _
   simpa using ih.add hdvd.modEq_zero_int
theorem ZhL (p : Polynomial ℤ) (B : ℤ) (k : ℕ) :
  p.eval B ≡ (∑ i ∈ range k, p.coeff i * B ^ i) [ZMOD B ^ k] := by
 rw [Polynomial.eval_eq_sum_range' (n := max (p.natDegree + 1) k)
  (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))]
 exact Zpa B p.coeff k _ (le_max_right _ _)
theorem Zla (p : Polynomial ℤ) (B : ℤ) (hB : 2 ≤ B)
  (k : ℕ) (hE : ∀ i ≤ k, 50 * |p.coeff i| ≤ 3 * (B - 1))
  (hk : p.coeff k ≠ 0) {x : ℤ}
  (hx : x ≡ p.eval B [ZMOD B ^ (k + 1)]) : B ^ k / 2 < |x| := by
 exact Zoy B hB p.coeff k
  (fun i hi => hE i (Nat.lt_succ_iff.mp hi)) hk
  (hx.trans (ZhL p B (k + 1)))
theorem ZhM {B L k e : ℤ}
  (hbase : 100 * k ^ 2 * L ^ 3 < B)
  (he : |e| ≤ 6 * k ^ 2 * L ^ 3) :
  50 * |e| ≤ 3 * (B - 1) := by
 have hbase' : 100 * k ^ 2 * L ^ 3 ≤ B - 1 := by omega
 nlinarith
theorem Zfp {ι : Type*} [Fintype ι] [DecidableEq ι]
  (h : ℕ) (G : Matrix.SpecialLinearGroup ι (ZMod h))
  (A C : Matrix ι ι ℤ)
  (hAC : A.map (Int.castRingHom (ZMod h)) =
   (G : Matrix ι ι (ZMod h)) * C.map (Int.castRingHom (ZMod h))) :
  A.det ≡ C.det [ZMOD h] := by
 rw [← ZMod.intCast_eq_intCast_iff, Int.cast_det, Int.cast_det]
 change (A.map (Int.castRingHom (ZMod h))).det =
  (C.map (Int.castRingHom (ZMod h))).det
 rw [hAC, Matrix.det_mul, G.det_coe, one_mul]
end Problem355.Zcn
end OAI
end
section
namespace OAI
namespace Problem355.Zb
open Finset
noncomputable section
 theorem ZfC {Ω B : Type*} [Fintype Ω]
   (q s : ℕ) (w : Ω → ℝ) (V : Ω → Finset B)
   (hw : ∀ ω, 0 ≤ w ω) (b : Fin 3 → B) :
   0 ≤ Zk q s w V b := by
  unfold Zk
  exact mul_nonneg (by positivity) (ZgG w V hw b)
theorem Zci
  {X A Ω B : Type*} [DecidableEq X] [Fintype Ω]
  (f : X → A) (g : X → (Fin 3 → B)) (d : X → ℤ)
  (O : Finset A) (w : Ω → ℝ) (V : Ω → Finset B)
  (s M : ℕ) (S : Finset X) (τ : ℤ)
  (hlarge : ∀ x ∈ S, f x ∈ O → τ < |d x|) :
  (∑ x ∈ S.filter (fun x => |d x| ≤ τ), ZaI f g O w V s M x) = 0 := by
 classical
 apply Finset.sum_eq_zero
 intro x hx
 have hxS := (Finset.mem_filter.mp hx).1
 have hxτ := (Finset.mem_filter.mp hx).2
 have hnot : f x ∉ O := fun hf => (not_lt_of_ge hxτ) (hlarge x hxS hf)
 simp [ZaI, ZdL, hnot]
theorem ZlP
   {X A Ω B : Type*} [DecidableEq X] [DecidableEq A] [Fintype Ω]
   (f : X → A) (g : X → (Fin 3 → B)) (d : X → ℤ)
   (O : Finset A) (hO : O.Nonempty) (w : Ω → ℝ) (V : Ω → Finset B)
   (s h q L : ℕ) (hs : 0 < s) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L)
   (hw : ∀ ω, 0 ≤ w ω) (S : Finset X)
   {τ : ℤ} (hwidth : 2 * τ < h) (c : ZMod h)
   (hres : ∀ x ∈ S, f x ∈ O → (d x : ZMod h) = c)
   {D E c₀ C R : ℝ} (hD : 0 < D) (hE : 0 < E) (hc₀ : 0 < c₀) (hC : 0 ≤ C)
   (horbit : c₀ * (h : ℝ) ^ 8 / (D ^ 3 * E ^ 2) ≤ (O.card : ℝ))
   (hcount : ∀ t : ℤ, |t| ≤ τ →
     (∑ x ∈ (S.filter (fun x => f x ∈ O)).filter (fun x => d x = t),
      Zk q s w V (g x)) ≤
       C * R ^ 2 * ((L * (h * q) : ℕ) : ℝ) ^ 6 / (D ^ 2 * E ^ 2)) :
   (∑ x ∈ S.filter (fun x => |d x| ≤ τ), ZaI f g O w V s (L ^ 9) x) ≤
     (C / c₀) * R ^ 2 * (h : ℝ) * D / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
 classical
 rw [ZkY f g O hO w V s h q L hs hh hq hL]
 rw [Finset.filter_comm]
 apply Zkw.ZhK
 · exact_mod_cast hh
 · exact_mod_cast (Nat.mul_pos hL (Nat.mul_pos hh hq))
 · exact hD
 · exact hE
 · exact_mod_cast Finset.card_pos.mpr hO
 · exact hc₀
 · exact Finset.sum_nonneg fun x hx => ZfC q s w V hw (g x)
 · exact horbit
 · apply ZiD.Zil
     (S.filter (fun x => f x ∈ O)) d (fun x => Zk q s w V (g x))
     hwidth c
   · intro x hx
     exact hres x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
   · positivity
   · exact hcount
end
end Problem355.Zb
end OAI
end
section
namespace OAI
namespace Problem355.Homogeneous
open Finset
noncomputable section
noncomputable local instance zCPD1 (p : Prop) : Decidable p := Classical.propDecidable p
def ZbH (u v w : ZaA) : Prop :=
 project u ≠ project v ∧ project u ≠ project w ∧ project v ≠ project w
def ZN (A : Matrix (Fin 3) (Fin 3) ℤ) (j : Fin 3) : ZaA :=
  fun i => (A i j : ℝ)
 theorem Znt (A : Matrix (Fin 3) (Fin 3) ℤ) :
   (Zcd (ZN A 0) (ZN A 1) (ZN A 2)).det =
    (A.det : ℝ) := by
  simp [Zcd, ZN, Matrix.det_fin_three]
theorem Zhq {N τ : ℝ} (hN : 0 < N) (hτ : 0 ≤ τ)
  {u v w : ZaA} (hu : ZaX N u) (hv : ZaX N v) (hw : ZaX N w)
  (hsmall : ZaW.Zbo (τ / (16 * N ^ 3))
   (project u) (project v) (project w)) :
  ZbH u v w ∧ |(Zcd u v w).det| < τ := by
 refine ⟨⟨hsmall.1, hsmall.2.1, hsmall.2.2.1⟩, ?_⟩
 by_contra hn
 have hbound := Zgt hN hτ hu hv hw (le_of_not_gt hn)
 exact (not_le_of_gt hsmall.2.2.2) hbound
theorem ZfD {N : ℝ} {τ : ℤ}
  (hN : 0 < N) (hτ : 0 ≤ τ) {u v w : ZaA}
  (hu : ZaX N u) (hv : ZaX N v) (hw : ZaX N w)
  (d : ℤ) (hd : (Zcd u v w).det = (d : ℝ))
  (hsmall : ZaW.Zbo ((τ : ℝ) / (16 * N ^ 3))
   (project u) (project v) (project w)) :
  ZbH u v w ∧ |d| ≤ τ := by
 have h := Zhq hN (by exact_mod_cast hτ) hu hv hw hsmall
 refine ⟨h.1, ?_⟩
 have hreal : |(d : ℝ)| < (τ : ℝ) := by simpa only [hd] using h.2
 have hint : |d| < τ := by exact_mod_cast hreal
 exact hint.le
end
end Problem355.Homogeneous
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZbR
noncomputable local instance zCPD2 (p : Prop) : Decidable p := Classical.propDecidable p
open Finset Matrix
open Zc ZD
abbrev Zi := Matrix (Fin 3) (Fin 3) ℤ
theorem ZjY {N : ℕ} {shift : Fin 3 → ℤ} :
  Function.Injective (@Zg N shift) := by
 intro x y h
 funext j i
 apply Subtype.ext
 exact congrFun (congrFun h i) j
def ZaX (N : ℕ) (shift : Fin 3 → ℤ) (A : Zi) : Prop :=
 ∀ i j, shift i ≤ A i j ∧ A i j < shift i + N
def Znu (N : ℕ) (shift : Fin 3 → ℤ) :
  (Fin 3 → Box N 3 shift) ≃ {A : Zi // ZaX N shift A} where
 toFun x := ⟨Zg x, fun i j => (x j i).property⟩
 invFun A := fun j i => ⟨A.val i j, A.property i j⟩
 left_inv _ := rfl
 right_inv _ := rfl
def ZfZ (N : ℕ) (shift : Fin 3 → ℤ) : Finset Zi := by
 classical
 exact Finset.univ.image (@Zg N shift)
@[simp] theorem Zsc {N : ℕ} {shift : Fin 3 → ℤ} {A : Zi} :
   A ∈ ZfZ N shift ↔ ZaX N shift A := by
 classical
 constructor
 · intro h
   obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
   exact fun i j => (x j i).property
 · intro h
   exact Finset.mem_image.mpr
    ⟨(Znu N shift).symm ⟨A, h⟩, Finset.mem_univ _, rfl⟩
@[simp] theorem Zra {N : ℕ} {shift : Fin 3 → ℤ}
 (m : ℕ) (x : Fin 3 → Box N 3 shift) :
 (Zg x).map (Int.cast : ℤ → ZMod m) =
  Matrix.transpose (fun j => residue m (x j)) := rfl
@[simp] theorem Zlb {N : ℕ}
 (x : Fin 3 → Box N 3 (Zm N)) (j : Fin 3) :
 Homogeneous.project (Homogeneous.ZN (Zg x) j) =
  Zc.project (x j) := rfl
theorem ZjZ {N : ℕ} {shift : Fin 3 → ℤ}
  (S : Finset (Fin 3 → Box N 3 shift)) (W : Zi → ℝ) :
  (∑ x ∈ S, W (Zg x)) =
   ∑ A ∈ S.image Zg, W A := by
 classical
 rw [Finset.sum_image]
 exact fun x _ y _ h => ZjY h
theorem ZnT {N : ℕ} {shift : Fin 3 → ℤ}
   (P : Zi → Prop) :
   ((Finset.univ : Finset (Fin 3 → Box N 3 shift)).filter
    (fun x => P (Zg x))).image Zg =
    (ZfZ N shift).filter P := by
 classical
 ext A
 simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
   ZfZ]
 constructor
 · rintro ⟨x, hx, rfl⟩
   exact ⟨⟨x, rfl⟩, hx⟩
 · rintro ⟨⟨x, rfl⟩, hx⟩
   exact ⟨x, hx, rfl⟩
theorem Zpb {N : ℕ} {shift : Fin 3 → ℤ}
  (P : Zi → Prop) (W : Zi → ℝ) :
  (∑ x ∈ (Finset.univ : Finset (Fin 3 → Box N 3 shift)).filter
   (fun x => P (Zg x)), W (Zg x)) =
   ∑ A ∈ (ZfZ N shift).filter P, W A := by
 classical
 rw [ZjZ, ZnT]
def Zdo {Ω : Type*} [Fintype Ω] (q s : ℕ)
  (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q)) (A : Zi) : ℝ :=
 Zb.Zk q s w V
  (fun j i => (A i j : ZMod q))
@[simp] theorem Zqu {Ω : Type*} [Fintype Ω]
 {N : ℕ} {shift : Fin 3 → ℤ} (q s : ℕ)
 (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
 (x : Fin 3 → Box N 3 shift) :
 Zdo q s w V (Zg x) =
  Zb.Zk q s w V
   (fun j => residue q (x j)) := rfl
theorem Zju {Ω : Type*} [Fintype Ω]
  {N : ℕ} {shift : Fin 3 → ℤ} (q s : ℕ)
  (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
  (P : Zi → Prop) :
  (∑ x ∈ (Finset.univ : Finset (Fin 3 → Box N 3 shift)).filter
   (fun x => P (Zg x)),
   Zb.Zk q s w V (fun j => residue q (x j))) =
   ∑ A ∈ (ZfZ N shift).filter P, Zdo q s w V A := by
 exact Zpb P (Zdo q s w V)
end Problem355.ZbR
end
end OAI
end
section
namespace OAI
namespace Problem355
theorem Zdp (m d : ℕ) [NeZero m] :
  Nat.card {x : ZMod m // (d : ZMod m) * x = 0} = Nat.gcd m d := by
 simpa only [Nat.card_zmod, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply,
  nsmul_eq_mul] using IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) d
theorem ZhN (m d : ℕ) [NeZero m] (hd : d ∣ m) :
  Nat.card {x : ZMod m // (d : ZMod m) * x = 0} = d := by
 rw [Zdp, Nat.gcd_eq_right hd]
theorem Zcr (B k e : ℕ) [NeZero B] (he : e ≤ k) :
  Nat.card {x : ZMod (B ^ k) // (B ^ e : ZMod (B ^ k)) * x = 0} = B ^ e := by
 simpa only [Nat.cast_pow] using
  ZhN (B ^ k) (B ^ e) (pow_dvd_pow B he)
def Zka {ι R : Type*} [Fintype ι] [DecidableEq ι]
  [Ring R] (d : ι → R) :
  {A : Matrix ι ι R // A * Matrix.diagonal d = Matrix.diagonal d} ≃
   (ι → (j : ι) → {x : R // x * d j = 0}) where
 toFun A i j := ⟨(A.1 - 1) i j, by
  have hzero : (A.1 - 1) * Matrix.diagonal d = 0 := by
   rw [Matrix.sub_mul, A.2, Matrix.one_mul, sub_self]
  simpa only [Matrix.mul_diagonal, Matrix.zero_apply] using
   congrArg (fun M : Matrix ι ι R => M i j) hzero⟩
 invFun f := ⟨(Matrix.of (fun i j => (f i j).1)) + 1, by
  have hzero : (Matrix.of (fun i j => (f i j).1)) * Matrix.diagonal d = 0 := by
   ext i j
   simpa only [Matrix.mul_diagonal, Matrix.zero_apply, Matrix.of_apply] using (f i j).2
  rw [Matrix.add_mul, hzero, Matrix.one_mul, zero_add]⟩
 left_inv A := by
  apply Subtype.ext
  exact sub_add_cancel A.1 1
 right_inv f := by
  funext i j
  apply Subtype.ext
  change ((Matrix.of (fun i j => (f i j).1)) + 1 - 1) i j = (f i j).1
  rw [add_sub_cancel_right]
  rfl
theorem ZiL {ι : Type*} [Fintype ι] [DecidableEq ι]
  (m : ℕ) [NeZero m] (d : ι → ℕ) :
  Nat.card {A : Matrix ι ι (ZMod m) //
   A * Matrix.diagonal (fun j => (d j : ZMod m)) =
    Matrix.diagonal (fun j => (d j : ZMod m))} =
   (∏ j, Nat.gcd m (d j)) ^ Fintype.card ι := by
 rw [Nat.card_congr (Zka (fun j => (d j : ZMod m)))]
 rw [Nat.card_fun, Nat.card_pi, Nat.card_eq_fintype_card]
 congr 1
 apply Finset.prod_congr rfl
 intro j _
 simpa only [mul_comm] using Zdp m (d j)
theorem Zga (m D E : ℕ) [NeZero m]
  (hD : D ∣ m) (hE : E ∣ m) :
  Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod m) //
   A * Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)] =
    Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)]} = D ^ 3 * E ^ 3 := by
 have hv : (fun j : Fin 3 => (![1, D, E] j : ZMod m)) =
   ![1, (D : ZMod m), (E : ZMod m)] := by
  funext j
  fin_cases j <;> simp
 have hc := ZiL (ι := Fin 3) m ![1, D, E]
 rw [hv] at hc
 simpa [Fin.prod_univ_succ, Nat.gcd_eq_right hD, Nat.gcd_eq_right hE,
  mul_pow] using hc
theorem ZdM (m D E : ℕ) [NeZero m]
  (hD : D ∣ m) (hE : E ∣ m) :
  Nat.card {A : (Matrix (Fin 3) (Fin 3) (ZMod m))ˣ //
   (A : Matrix (Fin 3) (Fin 3) (ZMod m)) *
     Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)] =
    Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)]} ≤ D ^ 3 * E ^ 3 := by
 rw [← Zga m D E hD hE]
 apply Nat.card_le_card_of_injective (fun A => ⟨(A.1 : Matrix _ _ _), A.2⟩)
 intro A B h
 apply Subtype.ext
 apply Units.ext
 exact congrArg Subtype.val h
end Problem355
end OAI
end
section
namespace OAI
namespace Problem355
def ZkE {M : Type*} [Monoid M] (P Q : Mˣ) (D : M) :
  {A : Mˣ // (A : M) * D = D} ≃
    {A : Mˣ // (A : M) * ((P : M) * D * (Q : M)) =
     (P : M) * D * (Q : M)} :=
 (MulAut.conj P).toEquiv.subtypeEquiv fun A => by
  change (A : M) * D = D ↔
    ((P : M) * (A : M) * ((P⁻¹ : Mˣ) : M)) *
     ((P : M) * D * (Q : M)) = (P : M) * D * (Q : M)
  constructor
  · intro h
    simpa only [mul_assoc, Units.inv_mul_cancel_left] using
     congrArg (fun x : M => (P : M) * x * (Q : M)) h
  · intro h
    have hh := congrArg (fun x : M => ((P⁻¹ : Mˣ) : M) * x * ((Q⁻¹ : Mˣ) : M)) h
    simpa only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, one_mul, mul_one] using hh
theorem ZhO {M : Type*} [Monoid M]
  (P Q : Mˣ) (D : M) :
  Nat.card {A : Mˣ // (A : M) * ((P : M) * D * (Q : M)) =
   (P : M) * D * (Q : M)} =
   Nat.card {A : Mˣ // (A : M) * D = D} :=
 (Nat.card_congr (ZkE P Q D)).symm
theorem ZcA
  (m D E : ℕ) [NeZero m] (hD : D ∣ m) (hE : E ∣ m)
  (C : Matrix (Fin 3) (Fin 3) (ZMod m))
  (P Q : (Matrix (Fin 3) (Fin 3) (ZMod m))ˣ)
  (hC : C = (P : Matrix _ _ _) *
   Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)] * (Q : Matrix _ _ _)) :
  Nat.card {A : (Matrix (Fin 3) (Fin 3) (ZMod m))ˣ //
   (A : Matrix (Fin 3) (Fin 3) (ZMod m)) * C = C} ≤ D ^ 3 * E ^ 3 := by
 subst C
 rw [ZhO]
 exact ZdM m D E hD hE
end Problem355
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zkx
open Matrix
variable {R : Type*} [CommRing R]
def ZfT (D E : R) : Matrix (Fin 3) (Fin 3) R :=
 Matrix.diagonal ![1, D, E]
def Zco (u : Rˣ) : Matrix.GeneralLinearGroup (Fin 3) R :=
 Matrix.GeneralLinearGroup.mk'' (Matrix.diagonal ![1, 1, (u : R)]) (by
  simp [Matrix.det_diagonal, Fin.prod_univ_succ])
@[simp] theorem ZlQ (u : Rˣ) :
  (Zco u : Matrix (Fin 3) (Fin 3) R) =
   Matrix.diagonal ![1, 1, (u : R)] := by
 simp [Zco]
@[simp] theorem Zrl (u : Rˣ) :
  Matrix.GeneralLinearGroup.det (Zco u) = u := by
 apply Units.ext
 simp [Matrix.GeneralLinearGroup.det, Matrix.det_diagonal, Fin.prod_univ_succ]
theorem ZkF (D E : R) (u : Rˣ)
  (hu : ((u : R) - 1) * E = 0) :
  (Zco u : Matrix (Fin 3) (Fin 3) R) * ZfT D E =
   ZfT D E := by
 have huE : (u : R) * E = E := by
  simpa [sub_mul, sub_eq_zero] using hu
 rw [ZlQ, ZfT, Matrix.diagonal_mul_diagonal]
 congr 1
 funext i
 fin_cases i <;> simp [huE]
theorem ZcD
  {p k e : ℕ} (hp : p.Prime) (he : e ≤ k)
  (D : ZMod (p ^ k))
  (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
  (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
  (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))) *
   ZfT D ((p ^ e : ℕ) : ZMod (p ^ k)) *
   (Q : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))) :
  p ^ e * Nat.card (ZMod (p ^ k))ˣ ≤
   p ^ k * Nat.card
    ((MulAction.stabilizer
     (Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))) C).map
      Matrix.GeneralLinearGroup.det) := by
 let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
 let R := ZMod (p ^ k)
 let E : R := (p ^ e : ℕ)
 let f : R →+ R := nsmulAddMonoidHom (p ^ e)
 let H := MulAction.stabilizer Rˣ E
 have hor : Nat.card (MulAction.orbit Rˣ E) ≤ Nat.card f.range := by
  apply Nat.card_mono (s := MulAction.orbit Rˣ E) (t := (f.range : Set R)) (Set.toFinite _)
  rintro y ⟨u, rfl⟩
  exact ⟨(u : R), by simp [f, E, nsmul_eq_mul, Units.smul_def, mul_comm]⟩
 have hk := f.ker.card_mul_index
 rw [AddSubgroup.index_ker] at hk
 have hker : Nat.card f.ker = p ^ e := by
  rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod, Nat.gcd_eq_right (pow_dvd_pow p he)]
 rw [hker, Nat.card_zmod] at hk
 have him : H ≤ (MulAction.stabilizer (GL (Fin 3) R) C).map GeneralLinearGroup.det := by
  intro u hu
  let g := Zco u
  refine ⟨P * g * P⁻¹, ?_, by simp [g, mul_comm]⟩
  change (↑(P * g * P⁻¹) : Matrix _ _ _) * C = C
  have hfix := ZkF D E u (by rw [sub_mul, one_mul]; exact sub_eq_zero.mpr hu)
  rw [hC]
  simp only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  rw [← Matrix.mul_assoc (↑g : Matrix (Fin 3) (Fin 3) R)]; rw [hfix]
 rw [← ZcL.Zby (G := Rˣ) E, ← mul_assoc]
 exact Nat.mul_le_mul ((Nat.mul_le_mul_left (p ^ e) hor).trans hk.le) (Nat.card_le_card_of_injective (Subgroup.inclusion him) (Subgroup.inclusion_injective him))
end Problem355.Zkx
end
end OAI
end
section
namespace OAI
namespace Problem355.Zou
open Matrix
theorem ZiM (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
  (x : ZMod (p ^ k)) :
  IsUnit (ZMod.castHom (dvd_pow_self p (Nat.ne_zero_of_lt hk)) (ZMod p) x) ↔
   IsUnit x := by
 have hp0 : p ≠ 0 := hp.ne_zero
 have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp0⟩
 conv_rhs => rw [← ZMod.natCast_zmod_val x]
 conv_lhs => rw [← ZMod.natCast_zmod_val x]
 simp only [map_natCast]
 rw [ZMod.isUnit_iff_coprime, ZMod.isUnit_iff_coprime,
  Nat.coprime_pow_right_iff hk]
theorem Zrb (F : Type*) [Field F] [Fintype F] :
  (21 / 64 : ℝ) * (Fintype.card F : ℝ) ^ 9 ≤ (Nat.card (GL (Fin 3) F) : ℝ) := by
 have h : 2 ≤ Fintype.card F := Fintype.one_lt_card
 obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h
 simp [Matrix.card_GL_field, Fin.prod_univ_succ, ht]
 push_cast [Nat.cast_sub (by exact Nat.one_le_pow _ _ (by omega) : 1 ≤ (2+t)^3),
  Nat.cast_sub (Nat.le_pow (by decide : 0 < 3) : 2+t ≤ (2+t)^3),
  Nat.cast_sub (Nat.pow_le_pow_right (by positivity : 0 < 2+t) (by decide : 2 ≤ 3))]
 rw [← sub_nonneg]
 ring_nf
 positivity
theorem Zgu (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 9 ≤
      (Nat.card (GL (Fin 3) (ZMod (p ^ k))) : ℝ) := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have : Fact p.Prime := ⟨hp⟩
  let f := ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p)
  let e : Fin (p ^ k) × Fin p ≃ ZMod (p ^ (k+1)) :=
    finProdFinEquiv.trans (ZMod.finEquiv _).toEquiv
  have low (d : Fin (p ^ k)) (a : Fin p) : f (e (d,a)) = ZMod.finEquiv p a := by
    change f (ZMod.finEquiv _ (finProdFinEquiv (d,a))) = _
    have hn {n : ℕ} [NeZero n] (x : Fin n) : ZMod.finEquiv n x = (x.val : ZMod n) := by
      cases n with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n => apply Fin.ext; exact (Nat.mod_eq_of_lt x.isLt).symm
    rw [hn (n := p^(k+1)) (finProdFinEquiv (d,a)), hn a, map_natCast]
    change ((a.val + p * d.val : ℕ) : ZMod p) = _
    simp
  let lift (A : GL (Fin 3) (ZMod p)) (D : Fin 3 → Fin 3 → Fin (p ^ k)) :
      Matrix (Fin 3) (Fin 3) (ZMod (p^(k+1))) :=
    fun i j => e (D i j, (ZMod.finEquiv p).symm (A.1 i j))
  have unit A D : IsUnit (lift A D) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← ZiM p _ hp (Nat.succ_pos k), RingHom.map_det]
    have h : f.mapMatrix (lift A D) = A.1 := by
      ext i j
      change f (e (_, _)) = _
      rw [low, RingEquiv.apply_symm_apply]
    change IsUnit (f.mapMatrix (lift A D)).det
    rw [h, ← Matrix.isUnit_iff_isUnit_det]
    exact A.isUnit
  have count := Nat.card_le_card_of_injective
    (fun x : GL (Fin 3) (ZMod p) × (Fin 3 → Fin 3 → Fin (p^k)) => (unit x.1 x.2).unit)
    (by rintro ⟨A,D⟩ ⟨B,E⟩ h
        have hm : lift A D = lift B E := congrArg Units.val h
        have he (i j : Fin 3) := e.injective (congrFun (congrFun hm i) j)
        exact Prod.ext (Units.ext (Matrix.ext fun i j => (ZMod.finEquiv p).symm.injective (congrArg Prod.snd (he i j))))
          (funext fun i => funext fun j => congrArg Prod.fst (he i j)))
  simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin, ← pow_mul] at count
  have H := Zrb (ZMod p)
  rw [ZMod.card] at H
  calc
    _ = (21 / 64 * (p : ℝ)^9) * ((p^k : ℕ) : ℝ)^9 := by rw [pow_succ p k, Nat.cast_mul, mul_pow]; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right H (by positivity)).trans (by exact_mod_cast (by simpa [← pow_mul, Nat.mul_assoc] using count : Nat.card (GL (Fin 3) (ZMod p)) * (p^k)^9 ≤ _))
end Problem355.Zou
end OAI
end
section
namespace OAI
namespace Problem355.ZS
open Matrix
variable {R : Type*} [CommRing R]
def Zbl (C : Matrix (Fin 3) (Fin 3) R) : Set (Matrix (Fin 3) (Fin 3) R) :=
 Set.range fun g : Matrix.SpecialLinearGroup (Fin 3) R => (g : Matrix _ _ _) * C
theorem ZkG (C : Matrix (Fin 3) (Fin 3) R) :
   Zbl C = MulAction.orbit
    (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 3) R →* Rˣ).ker C := by
 ext M
 constructor
 · rintro ⟨g, rfl⟩
   refine ⟨⟨Matrix.SpecialLinearGroup.toGL g, ?_⟩, rfl⟩
   exact Matrix.SpecialLinearGroup.coeToGL_det g
 · rintro ⟨g, rfl⟩
   have hd : (g.1 : Matrix (Fin 3) (Fin 3) R).det = 1 := by
    exact congrArg Units.val g.2
   exact ⟨⟨g.1.val, hd⟩, rfl⟩
theorem ZeK
   {p k b e : ℕ} (hp : p.Prime) (hb : b ≤ k) (he : e ≤ k)
   (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
   (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
   (hC : C = (P : Matrix _ _ _) *
    Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)), ((p ^ e : ℕ) : ZMod (p ^ k))] *
    (Q : Matrix _ _ _))
   {c : ℝ}
   (hGL : c * ((p ^ k : ℕ) : ℝ) ^ 9 ≤
    (Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))) : ℝ)) :
   c * ((p ^ k : ℕ) : ℝ) ^ 8 /
    (((p ^ b : ℕ) : ℝ) ^ 3 * ((p ^ e : ℕ) : ℝ) ^ 2) ≤
     (Nat.card (Zbl C) : ℝ) := by
 let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
 have hs := Problem355.ZcA
   (p ^ k) (p ^ b) (p ^ e) (pow_dvd_pow p hb) (pow_dvd_pow p he) C P Q hC
 have hi := Zkx.ZcD
   hp he ((p ^ b : ℕ) : ZMod (p ^ k)) P Q C hC
 rw [ZkG]
 apply ZcL.ZnS Matrix.GeneralLinearGroup.det
    Matrix.GeneralLinearGroup.det_surjective C
    (by exact_mod_cast pow_pos hp.pos k)
    (by exact_mod_cast pow_pos hp.pos b)
    (by exact_mod_cast pow_pos hp.pos e) hGL
 · exact_mod_cast hs
 · exact_mod_cast hi
theorem Znv
  {p k b e : ℕ} (hp : p.Prime) (hk : 0 < k) (hb : b ≤ k) (he : e ≤ k)
  (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
  (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
  (hC : C = (P : Matrix _ _ _) *
   Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)), ((p ^ e : ℕ) : ZMod (p ^ k))] *
   (Q : Matrix _ _ _)) :
  (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 8 /
   (((p ^ b : ℕ) : ℝ) ^ 3 * ((p ^ e : ℕ) : ℝ) ^ 2) ≤
    (Nat.card (Zbl C) : ℝ) :=
 ZeK hp hb he C P Q hC
  (Zou.Zgu p k hp hk)
end Problem355.ZS
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZaG
open Matrix
variable {R : Type*} [CommRing R]
def Zad (D E : R) : Matrix (Fin 3) (Fin 3) R :=
 Matrix.diagonal ![1, D, E]
abbrev Ann (a : R) := {x : R // x * a = 0}
end Problem355.ZaG
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zah
open Matrix ZaG
variable {R : Type*} [CommRing R]
abbrev Zim (C : Matrix (Fin 3) (Fin 3) R) :=
 {v : Fin 3 → R // v ᵥ* C = 0}
def Zbz (C : Matrix (Fin 3) (Fin 3) R) : AddSubgroup (Fin 3 → R) :=
 C.vecMulLinear.toAddMonoidHom.range
lemma Zhr [Finite R] (C : Matrix (Fin 3) (Fin 3) R) :
  (Zbz C).index = Nat.card (Zim C) := by
 exact AddSubgroup.index_range
def Zeo (D E : R) :
  Zim (Zad D E) ≃ Ann D × Ann E where
 toFun v :=
  (⟨v.val 1, by
    have h := congrFun v.property 1
    simpa [Zad, Matrix.vecMul_diagonal] using h⟩,
   ⟨v.val 2, by
    have h := congrFun v.property 2
    simpa [Zad, Matrix.vecMul_diagonal] using h⟩)
 invFun v := ⟨![0, v.1.val, v.2.val], by
  funext i
  fin_cases i
  · simp [Zad, Matrix.vecMul_diagonal]
  · simpa [Zad, Matrix.vecMul_diagonal] using v.1.property
  · simpa [Zad, Matrix.vecMul_diagonal] using v.2.property⟩
 left_inv v := by
  apply Subtype.ext
  funext i
  fin_cases i
  · have h := congrFun v.property 0
    simpa [Zad, Matrix.vecMul_diagonal] using h.symm
  · rfl
  · rfl
 right_inv v := by
  apply Prod.ext <;> apply Subtype.ext <;> rfl
lemma ZmE (D E : R) :
  Nat.card (Zim (Zad D E)) = Nat.card (Ann D) * Nat.card (Ann E) := by
 rw [Nat.card_congr (Zeo D E), Nat.card_prod]
def Zjv {C D : Matrix (Fin 3) (Fin 3) R}
  (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
  (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * D *
   (Q : Matrix (Fin 3) (Fin 3) R)) : Zim C ≃ Zim D where
 toFun v := ⟨v.val ᵥ* P.val, by
  apply Matrix.vecMul_injective_of_isUnit Q.isUnit
  simpa only [Matrix.vecMul_vecMul, hC, Matrix.zero_vecMul] using v.property⟩
 invFun v := ⟨v.val ᵥ* (P⁻¹).val, by
  calc
   (v.val ᵥ* (P⁻¹).val) ᵥ* C =
     (((v.val ᵥ* (P⁻¹).val) ᵥ* P.val) ᵥ* D) ᵥ* Q.val := by
    simp only [Matrix.vecMul_vecMul, hC, Matrix.mul_assoc]
   _ = 0 := by
    have hp : (v.val ᵥ* (P⁻¹).val) ᵥ* P.val = v.val := by
     rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
    rw [hp, v.property, Matrix.zero_vecMul]⟩
 left_inv v := by
  apply Subtype.ext
  simp only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
 right_inv v := by
  apply Subtype.ext
  simp only [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
lemma Zgv [Finite R]
  (C : Matrix (Fin 3) (Fin 3) R) (D E : R)
  (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
  (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * Zad D E *
   (Q : Matrix (Fin 3) (Fin 3) R)) :
  (Zbz C).index = Nat.card (Ann D) * Nat.card (Ann E) := by
 rw [Zhr,
  Nat.card_congr (Zjv P Q hC), ZmE]
def reduction (h : ℕ) : (Fin 3 → ℤ) →+ (Fin 3 → ZMod h) where
 toFun v i := (v i : ZMod h)
 map_zero' := by ext i; simp
 map_add' v w := by ext i; simp
lemma ZmF (h : ℕ) : Function.Surjective (reduction h) := by
 intro v
 choose w hw using fun i : Fin 3 => ZMod.intCast_surjective (v i)
 exact ⟨w, funext hw⟩
def ZZ (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
  AddSubgroup (Fin 3 → ℤ) :=
 (Zbz C).comap (reduction h)
lemma Zfm (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
  (ZZ h C).index = (Zbz C).index := by
 exact AddSubgroup.index_comap_of_surjective _ (ZmF h)
theorem Zce
  (B k b e : ℕ) [NeZero B] (hb : b ≤ k) (he : e ≤ k)
  (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
  (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
  (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
   Zad (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
   (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))) :
  (ZZ (B ^ k) C).index = B ^ b * B ^ e := by
 have hD : Nat.card (Ann (R := ZMod (B ^ k)) (B ^ b)) = B ^ b := by
  simpa only [Ann, mul_comm] using Zcr B k b hb
 have hE : Nat.card (Ann (R := ZMod (B ^ k)) (B ^ e)) = B ^ e := by
  simpa only [Ann, mul_comm] using Zcr B k e he
 rw [Zfm, Zgv C _ _ P Q hC, hD, hE]
lemma ZiN (D E : R) (hDE : D ∣ E) (v : Fin 3 → R) :
  E • v ∈ Zbz (Zad D E) := by
 obtain ⟨a, ha⟩ := hDE
 refine ⟨![E * v 0, a * v 1, v 2], ?_⟩
 change ![E * v 0, a * v 1, v 2] ᵥ* Zad D E = E • v
 funext i
 fin_cases i <;> simp [Zad, Matrix.vecMul_diagonal, ha] <;> ring
lemma Zfq
  (C : Matrix (Fin 3) (Fin 3) R) (D E : R) (hDE : D ∣ E)
  (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
  (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * Zad D E *
   (Q : Matrix (Fin 3) (Fin 3) R)) (v : Fin 3 → R) :
  E • v ∈ Zbz C := by
 obtain ⟨w, hw⟩ := ZiN D E hDE (v ᵥ* (Q⁻¹).val)
 change w ᵥ* Zad D E = E • (v ᵥ* (Q⁻¹).val) at hw
 refine ⟨w ᵥ* (P⁻¹).val, ?_⟩
 change (w ᵥ* (P⁻¹).val) ᵥ* C = E • v
 calc
  (w ᵥ* (P⁻¹).val) ᵥ* C = (w ᵥ* Zad D E) ᵥ* Q.val := by
   simp only [hC, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Units.inv_mul, one_mul]
  _ = (E • (v ᵥ* (Q⁻¹).val)) ᵥ* Q.val := by rw [hw]
  _ = E • v := by
   rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
theorem ZbK
  (B k b e : ℕ) (hbe : b ≤ e)
  (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
  (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
  (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
   Zad (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
   (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))) (v : Fin 3 → ℤ) :
  (B ^ e) • v ∈ ZZ (B ^ k) C := by
 change reduction (B ^ k) ((B ^ e) • v) ∈ Zbz C
 have hv := Zfq C
  (B ^ b : ZMod (B ^ k)) (B ^ e : ZMod (B ^ k))
  (pow_dvd_pow (B : ZMod (B ^ k)) hbe) P Q hC (reduction (B ^ k) v)
 have hcast : reduction (B ^ k) ((B ^ e) • v) =
   (B ^ e : ZMod (B ^ k)) • reduction (B ^ k) v := by
  ext i
  simp [reduction, nsmul_eq_mul]
 rw [hcast]
 exact hv
instance Zqk (h : ℕ) [NeZero h]
  (C : Matrix (Fin 3) (Fin 3) (ZMod h)) : (ZZ h C).FiniteIndex where
 index_ne_zero := by
  rw [Zfm]
  exact AddSubgroup.FiniteIndex.index_ne_zero
lemma ZdE (h : ℕ)
  (A : Matrix (Fin 3) (Fin 3) ℤ)
  (C G : Matrix (Fin 3) (Fin 3) (ZMod h))
  (hA : A.map (Int.castRingHom (ZMod h)) = G * C) (i : Fin 3) :
  A.row i ∈ ZZ h C := by
 change reduction h (A.row i) ∈ Zbz C
 refine ⟨G.row i, ?_⟩
 have hrow := congrArg (fun M : Matrix (Fin 3) (Fin 3) (ZMod h) => M.row i) hA
 exact hrow.symm
end Problem355.Zah
end
end OAI
end
section
namespace OAI
namespace Problem355.ZeB
open Matrix
variable {R : Type*} [CommRing R]
theorem Zlc
   (P : Matrix.GeneralLinearGroup (Fin 3) R) (C : Matrix (Fin 3) (Fin 3) R) :
   Zah.Zbz ((P : Matrix _ _ _) * C) = Zah.Zbz C := by
 ext y
 constructor
 · rintro ⟨v, hv⟩
   refine ⟨v ᵥ* (P : Matrix _ _ _), ?_⟩
   change v ᵥ* (P.val * C) = y at hv
   change (v ᵥ* P.val) ᵥ* C = y
   rw [Matrix.vecMul_vecMul]
   exact hv
 · rintro ⟨v, hv⟩
   refine ⟨v ᵥ* ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 3) R) : Matrix _ _ _), ?_⟩
   change (v ᵥ* (P⁻¹).val) ᵥ* (P.val * C) = y
   calc
    (v ᵥ* (P⁻¹).val) ᵥ* (P.val * C) = v ᵥ* C := by
     rw [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    _ = y := hv
theorem ZiO
  {C A : Matrix (Fin 3) (Fin 3) R} (hA : A ∈ ZS.Zbl C) :
  Zah.Zbz A = Zah.Zbz C := by
 obtain ⟨g, rfl⟩ := hA
 exact Zlc (Matrix.SpecialLinearGroup.toGL g) C
theorem Zpc (C : Matrix (Fin 3) (Fin 3) R) (i : Fin 3) :
  C i ∈ Zah.Zbz C := by
 refine ⟨Pi.single i 1, ?_⟩
 ext j
 simp [Matrix.single_vecMul]
theorem ZaV
  (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h))
  (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hA : A.map (Int.castRingHom (ZMod h)) ∈ ZS.Zbl C) (i : Fin 3) :
  A i ∈ Zah.ZZ h C := by
 change (fun j => (A i j : ZMod h)) ∈ Zah.Zbz C
 rw [← ZiO hA]
 exact Zpc (A.map (Int.castRingHom (ZMod h))) i
theorem ZlR
  {C A : Matrix (Fin 3) (Fin 3) R} (hA : A ∈ ZS.Zbl C) :
  A.det = C.det := by
 obtain ⟨g, rfl⟩ := hA
 rw [Matrix.det_mul, g.property, one_mul]
theorem ZeL
  (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h))
  (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hA : A.map (Int.castRingHom (ZMod h)) ∈ ZS.Zbl C) :
  (A.det : ZMod h) = C.det := by
 have hd := ZlR hA
 change (Int.castRingHom (ZMod h)) A.det = C.det
 rw [RingHom.map_det]
 exact hd
end Problem355.ZeB
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZbR
open Finset Matrix Zc ZD
noncomputable local instance zCPD3 (p : Prop) : Decidable p := Classical.propDecidable p
def Zbr (h : ℕ) [NeZero h]
  (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ) (A : Zi) : Prop :=
 Homogeneous.ZbH (Homogeneous.ZN A 0)
   (Homogeneous.ZN A 1) (Homogeneous.ZN A 2) ∧
  (fun j i => (A i j : ZMod h)) ∈ Zt (Zz h) C ∧ A.det = t
def ZdX (N h : ℕ) [NeZero h]
  (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ) : Finset Zi :=
 (ZfZ N (Zm N)).filter (Zbr h C t)
theorem ZnU {Ω : Type*} [Fintype Ω]
  (N h q s : ℕ) [NeZero h]
  (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ)
  (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q)) :
  (∑ x ∈ (Finset.univ : Finset (Fin 3 → Box N 3 (Zm N))).filter
   (fun x => Zbr h C t (Zg x)),
   Zb.Zk q s w V (fun j => residue q (x j))) =
   ∑ A ∈ ZdX N h C t, Zdo q s w V A := by
 exact Zju q s w V (Zbr h C t)
theorem Zgw {N h : ℕ} [NeZero h]
  (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ)
  (x : Fin 3 → Box N 3 (Zm N)) :
  Zbr h C t (Zg x) ↔
   Homogeneous.ZbH (Homogeneous.ZN (Zg x) 0)
    (Homogeneous.ZN (Zg x) 1)
    (Homogeneous.ZN (Zg x) 2) ∧
   (fun j => residue h (x j)) ∈ Zt (Zz h) C ∧
   (Zg x).det = t := by
 rfl
theorem ZiP {h : ℕ} [NeZero h]
  {C : Fin 3 → Fin 3 → ZMod h} {t : ℤ} {A : Zi}
  (hA : Zbr h C t A) :
  A.map (Int.castRingHom (ZMod h)) ∈ ZS.Zbl (Matrix.transpose C) := by
 obtain ⟨G, hG⟩ := (Zcc C _).mp hA.2.1
 refine ⟨G, ?_⟩
 change G.val * Matrix.transpose C = A.map (Int.castRingHom (ZMod h))
 rw [← ZbN]
 exact congrArg Matrix.transpose hG
theorem Zjw {N h : ℕ} [NeZero h]
   {C : Fin 3 → Fin 3 → ZMod h} {t : ℤ} {A : Zi}
   (hA : A ∈ ZdX N h C t) (i j : Fin 3) (hij : i ≠ j) :
   Homogeneous.project (Homogeneous.ZN A i) ≠
    Homogeneous.project (Homogeneous.ZN A j) := by
 obtain ⟨h01, h02, h12⟩ := (Finset.mem_filter.mp hA).2.1
 fin_cases i <;> fin_cases j
 · exact False.elim (hij rfl)
 · exact h01
 · exact h02
 · exact h01.symm
 · exact False.elim (hij rfl)
 · exact h12
 · exact h02.symm
 · exact h12.symm
 · exact False.elim (hij rfl)
theorem Zjx {Ω : Type*} [Fintype Ω]
   (N h q s : ℕ) [NeZero h]
   (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ)
   (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q)) :
   (∑ x ∈ (((Finset.univ : Finset (Fin 3 → Box N 3 (Zm N))).filter
    (fun x => project (x 0) ≠ project (x 1) ∧
     project (x 0) ≠ project (x 2) ∧ project (x 1) ≠ project (x 2))).filter
    (fun x => (fun j => residue h (x j)) ∈ Zt (Zz h) C)).filter
    (fun x => (Zg x).det = t),
    Zb.Zk q s w V (fun j => residue q (x j))) =
    ∑ A ∈ ZdX N h C t, Zdo q s w V A := by
 rw [← ZnU N h q s C t w V]
 apply Finset.sum_congr
 · ext x
   simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Zgw, Homogeneous.ZbH,
    Zlb]
   tauto
 · intro x hx
   rfl
end Problem355.ZbR
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zhi
theorem Zoz (k r : ℕ) (hk : 0 < k) (hr : 0 < r) :
  ∃ B : ℕ, B.Prime ∧ 100 * k ^ 2 * r ^ 30 < B ∧
   B ≤ 200 * k ^ 2 * r ^ 30 := by
 obtain ⟨B, hB, hlo, hhi⟩ :=
  Nat.exists_prime_lt_and_le_two_mul (100 * k ^ 2 * r ^ 30) (by positivity)
 refine ⟨B, hB, hlo, ?_⟩
 nlinarith only [hhi]
theorem Zkb (k r : ℕ) (hk : 0 < k)
  (hr : 200 * k ^ 2 ≤ r) :
  ∃ B : ℕ, B.Prime ∧ 100 * k ^ 2 * r ^ 30 < B ∧
   B ≤ 200 * k ^ 2 * r ^ 30 ∧ B ≤ r ^ 31 := by
 have hk2 : 0 < k ^ 2 := by positivity
 have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
 obtain ⟨B, hB, hlo, hhi⟩ := Zoz k r hk hr0
 refine ⟨B, hB, hlo, hhi, hhi.trans ?_⟩
 calc
  200 * k ^ 2 * r ^ 30 ≤ r * r ^ 30 := Nat.mul_le_mul_right _ hr
  _ = r ^ 31 := by ring
theorem Zld (h : ℕ) (hh : 2 ≤ h) :
   ∃ q : ℕ, q.Prime ∧ h ^ 100 < q ∧ q ≤ 2 * h ^ 100 ∧
    q ≤ h ^ 101 ∧ h.Coprime q := by
 have hh0 : 0 < h := by omega
 obtain ⟨q, hq, hlo, hhi⟩ :=
   Nat.exists_prime_lt_and_le_two_mul (h ^ 100) (by positivity)
 have hhpow : h ≤ h ^ 100 := by
   simpa using (Nat.pow_le_pow_right (by omega : 0 < h) (by norm_num : 1 ≤ 100))
 refine ⟨q, hq, hlo, hhi, ?_, ?_⟩
 · calc
    q ≤ 2 * h ^ 100 := hhi
    _ ≤ h * h ^ 100 := Nat.mul_le_mul_right _ hh
    _ = h ^ 101 := by ring
 · exact (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hh0 (hhpow.trans_lt hlo))).symm
theorem ZlS (h q : ℕ) (hh : 2 ≤ h) (hq : h ^ 100 < q) :
  2000 * (h ^ 2) ^ 2 ≤ q := by
 have hpow : 2000 ≤ h ^ 96 := by
  calc
   2000 ≤ 2 ^ 96 := by norm_num
   _ ≤ h ^ 96 := Nat.pow_le_pow_left hh 96
 have hprod : 2000 * h ^ 4 ≤ h ^ 96 * h ^ 4 :=
  Nat.mul_le_mul_right _ hpow
 have heq : h ^ 96 * h ^ 4 = h ^ 100 := by ring
 have heq' : (h ^ 2) ^ 2 = h ^ 4 := by ring
 rw [heq']
 exact (hprod.trans_eq heq).trans hq.le
theorem ZkH (k r : ℕ) (hk : 0 < k)
  (hr : 200 * k ^ 2 ≤ r) :
  ∃ B q : ℕ, B.Prime ∧ q.Prime ∧
   100 * k ^ 2 * r ^ 30 < B ∧ B ≤ 200 * k ^ 2 * r ^ 30 ∧
   B ≤ r ^ 31 ∧ (B ^ k) ^ 100 < q ∧ q ≤ 2 * (B ^ k) ^ 100 ∧
   q ≤ (B ^ k) ^ 101 ∧ (B ^ k).Coprime q ∧
   2000 * ((B ^ k) ^ 2) ^ 2 ≤ q := by
 obtain ⟨B, hB, hlo, hhi, hpoly⟩ := Zkb k r hk hr
 have hBk : 2 ≤ B ^ k := by
  calc
   2 ≤ B := hB.two_le
   _ ≤ B ^ k := by
    simpa using Nat.pow_le_pow_right hB.pos hk
 obtain ⟨q, hq, hqlo, hqhi, hqpoly, hcop⟩ := Zld (B ^ k) hBk
 exact ⟨B, q, hB, hq, hlo, hhi, hpoly, hqlo, hqhi, hqpoly, hcop,
  ZlS (B ^ k) q hBk hqlo⟩
theorem ZgJ (k r B : ℕ) (hk : 0 < k)
  (hr : 400 * k ^ 2 ≤ r) (hB : B ≤ 200 * k ^ 2 * r ^ 30) :
  (B : ℝ) * ((r : ℝ) / (r : ℝ) ^ 10) ^ 4 ≤ 1 / 2 := by
 have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr
 have hr0 : 0 < (r : ℝ) := by exact_mod_cast hrpos
 have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast hrpos
 have hc : (400 : ℝ) * (k : ℝ) ^ 2 ≤ (r : ℝ) ^ 6 := by
  calc
   (400 : ℝ) * (k : ℝ) ^ 2 ≤ (r : ℝ) := by exact_mod_cast hr
   _ ≤ (r : ℝ) ^ 6 := by
    simpa using pow_le_pow_right₀ hr1 (by norm_num : 1 ≤ 6)
 have hb : (B : ℝ) ≤ 200 * (k : ℝ) ^ 2 * (r : ℝ) ^ 30 := by exact_mod_cast hB
 have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (r : ℝ) ^ 30)
 have heq : (r : ℝ) ^ 6 * (r : ℝ) ^ 30 = (r : ℝ) ^ 36 := by ring
 rw [heq] at hm
 have hid : (B : ℝ) * ((r : ℝ) / (r : ℝ) ^ 10) ^ 4 =
   (B : ℝ) / (r : ℝ) ^ 36 := by
  field_simp
 rw [hid]
 apply (div_le_iff₀ (by positivity : 0 < (r : ℝ) ^ 36)).2
 nlinarith only [hb, hm]
end Problem355.Zhi
end
end OAI
end
section
namespace OAI
namespace Problem355
lemma Znw : 3 ≤ ZaH := by
 have h : Nat.choose (41 + 1) 41 ≤ Nat.choose (4 * 41 - 1) 41 :=
  Nat.choose_le_choose 41 (by norm_num)
 rw [Nat.choose_succ_self_right] at h
 exact le_trans (by norm_num : 3 ≤ 42) h
lemma Zql : 0 < Zam := by
 exact pow_pos (lt_of_lt_of_le (by decide : 0 < 3) Znw) 3
private def Zkc (t : ℕ) : ℕ := t ^ 2 + 1
private lemma Zpd (t : ℕ) : Zkc t = t ^ 2 + 1 := rfl
lemma ZqA : Za = Zam ^ 2 + 1 := by
 with_unfolding_all exact Zpd Zam
private lemma ZpE {t : ℕ} (ht : 0 < t) : 2 ≤ Zkc t := by
 unfold Zkc
 nlinarith
lemma Zjn : 2 ≤ Za := by
 with_unfolding_all exact ZpE (t := Zam) Zql
lemma Zfb : 0 < Za :=
 lt_of_lt_of_le (by norm_num : 0 < 2) Zjn
end Problem355
namespace Problem355.Parameters
def threshold (B k : ℕ) : ℕ := B ^ (k - 1) / 2
lemma Zdc {B k : ℕ} (hB : 1 ≤ B) (hk : 2 ≤ k) :
  B ≤ B ^ (k - 1) := by
 have h : 1 ≤ k - 1 := by omega
 simpa using (pow_le_pow_right' hB h)
lemma ZqB {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
  0 < threshold B k := by
 have h := Zdc (by omega : 1 ≤ B) hk
 unfold threshold
 omega
lemma ZfE {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
  B ^ (k - 1) ≤ 3 * threshold B k := by
 have h := Zdc (by omega : 1 ≤ B) hk
 unfold threshold
 omega
lemma Zkd {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
  2 * threshold B k < B ^ k := by
 have hm := Zdc (by omega : 1 ≤ B) hk
 have he : k = (k - 1) + 1 := by omega
 have hpowe : B ^ k = B ^ (k - 1) * B := by nth_rw 1 [he]; rw [pow_succ]
 rw [hpowe]
 unfold threshold
 have hd : 2 * (B ^ (k - 1) / 2) ≤ B ^ (k - 1) := by omega
 have hp : 0 < B ^ (k - 1) := by omega
 nlinarith
lemma Zhs {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
  B ^ k ≤ 3 * B * threshold B k := by
 have h := ZfE hB hk
 have he : k = (k - 1) + 1 := by omega
 calc
  B ^ k = B ^ (k - 1) * B := by nth_rw 1 [he]; rw [pow_succ]
  _ ≤ (3 * threshold B k) * B := Nat.mul_le_mul_right B h
  _ = 3 * B * threshold B k := by ring
lemma ZmG {B r q k : ℕ}
  (hB : B ≤ r ^ 31) (hq : q ≤ (B ^ k) ^ 101) :
  (B ^ k * q) ^ 10 ≤ r ^ (31620 * k) := by
 calc
  (B ^ k * q) ^ 10 ≤ (B ^ k * (B ^ k) ^ 101) ^ 10 := by gcongr
  _ = B ^ (1020 * k) := by ring
  _ ≤ (r ^ 31) ^ (1020 * k) := Nat.pow_le_pow_left hB _
  _ = r ^ (31620 * k) := by rw [← pow_mul]; congr 1; ring
end Problem355.Parameters
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Parameters
structure Zf (k r : ℕ) where
 two_le_k : 2 ≤ k
 large_r : 200 * k ^ 2 ≤ r
 large_for_moment : 400 * k ^ 2 ≤ r
 B : ℕ
 q : ℕ
 base_prime : B.Prime
 auxiliary_prime : q.Prime
 base_lower : 100 * k ^ 2 * r ^ 30 < B
 base_upper : B ≤ 200 * k ^ 2 * r ^ 30
 base_polynomial : B ≤ r ^ 31
 auxiliary_lower : (B ^ k) ^ 100 < q
 auxiliary_upper : q ≤ 2 * (B ^ k) ^ 100
 auxiliary_polynomial : q ≤ (B ^ k) ^ 101
 coprime : (B ^ k).Coprime q
 auxiliary_large : 2000 * ((B ^ k) ^ 2) ^ 2 ≤ q
lemma Zjy {k r : ℕ} (hk : 2 ≤ k)
  (hr : 400 * k ^ 2 ≤ r) : Nonempty (Zf k r) := by
 have hr' : 200 * k ^ 2 ≤ r := by nlinarith only [hr]
 obtain ⟨B, q, hB, hq, hlo, hhi, hpoly, hqlo, hqhi, hqpoly, hcop, hlarge⟩ :=
  Zhi.ZkH k r (by omega) hr'
 exact ⟨⟨hk, hr', hr, B, q, hB, hq, hlo, hhi, hpoly, hqlo, hqhi, hqpoly, hcop, hlarge⟩⟩
namespace Zf
variable {k r : ℕ} (P : Zf k r)
def h : ℕ := P.B ^ k
def M : ℕ := P.h * P.q
def N : ℕ := P.M ^ 10
def tau : ℕ := threshold P.B k
include P in
lemma r_pos : 0 < r := by
 have hk := P.two_le_k
 have hp : 0 < 200 * k ^ 2 := by positivity
 exact lt_of_lt_of_le hp P.large_r
lemma ZdY : 3 ≤ P.B := by
 have hk : 0 < k := by have := P.two_le_k; omega
 have hr := P.r_pos
 have hp : 1 ≤ k ^ 2 * r ^ 30 := Nat.succ_le_of_lt (by positivity)
 have hc : 100 ≤ 100 * k ^ 2 * r ^ 30 := by
  calc
   100 = 100 * 1 := by norm_num
   _ ≤ 100 * (k ^ 2 * r ^ 30) := Nat.mul_le_mul_left 100 hp
   _ = 100 * k ^ 2 * r ^ 30 := by ring
 have := P.base_lower
 omega
lemma Zqv : P.B ≤ P.h := by
 unfold h
 simpa using (Nat.pow_le_pow_right P.base_prime.pos (show 1 ≤ k by have := P.two_le_k; omega))
lemma ZpF : 3 ≤ P.h := P.ZdY.trans P.Zqv
lemma Zrw : P.h ≤ P.M := by
 unfold M
 exact Nat.le_mul_of_pos_right _ P.auxiliary_prime.pos
lemma Zrx : r ≤ P.M := by
 have hr := P.r_pos
 have hk : 0 < k := by have := P.two_le_k; omega
 have hc : 1 ≤ 100 * k ^ 2 := Nat.succ_le_of_lt (by positivity)
 have hpow : r ≤ r ^ 30 := by
  simpa using Nat.pow_le_pow_right hr (by norm_num : 1 ≤ 30)
 calc
  r ≤ r ^ 30 := hpow
  _ ≤ 100 * k ^ 2 * r ^ 30 := Nat.le_mul_of_pos_left _ hc
  _ ≤ P.B := P.base_lower.le
  _ ≤ P.h := P.Zqv
  _ ≤ P.M := P.Zrw
lemma M_pos : 0 < P.M := lt_of_lt_of_le P.r_pos P.Zrx
lemma Zry : P.M ≤ P.N := by
 unfold N
 simpa using Nat.pow_le_pow_right P.M_pos (by norm_num : 1 ≤ 10)
lemma N_pos : 0 < P.N := lt_of_lt_of_le P.M_pos P.Zry
lemma Zqm : 0 < P.tau := ZqB P.ZdY P.two_le_k
lemma ZlT : 2 * P.tau < P.h :=
 Zkd P.ZdY P.two_le_k
lemma ZqO : P.tau < P.h := by
 have h := P.ZlT
 omega
lemma Zrc : P.tau ≤ P.N ^ 3 := by
 calc
  P.tau ≤ P.h := P.ZqO.le
  _ ≤ P.M := P.Zrw
  _ ≤ P.N := P.Zry
  _ ≤ P.N ^ 3 := by
   simpa using Nat.pow_le_pow_right P.N_pos (by norm_num : 1 ≤ 3)
lemma ZlU : P.N ≤ r ^ (31620 * k) :=
 ZmG P.base_polynomial P.auxiliary_polynomial
lemma Znx : 100 * k ^ 2 * (r ^ 10) ^ 3 < P.B := by
 convert P.base_lower using 1; ring
lemma ZrL : P.tau < P.q := by
 calc
  P.tau < P.h := P.ZqO
  _ ≤ P.h ^ 100 := by
   simpa using Nat.pow_le_pow_right (by have := P.ZpF; omega : 0 < P.h)
    (by norm_num : 1 ≤ 100)
  _ < P.q := P.auxiliary_lower
lemma Zpe : r ^ 10 < P.B := by
 have hk : 0 < k := by have := P.two_le_k; omega
 have hc : 1 ≤ 100 * k ^ 2 := Nat.succ_le_of_lt (by positivity)
 calc
  r ^ 10 ≤ r ^ 30 := Nat.pow_le_pow_right P.r_pos (by norm_num)
  _ ≤ 100 * k ^ 2 * r ^ 30 := Nat.le_mul_of_pos_left _ hc
  _ < P.B := P.base_lower
lemma ZnV :
  (P.B : ℝ) * ((r : ℝ) / (r : ℝ) ^ 10) ^ 4 ≤ 1 / 2 :=
 Zhi.ZgJ k r P.B
  (by have := P.two_le_k; omega) P.large_for_moment P.base_upper
def ZbA (P : Zf k r) : ℕ :=
 ⌊(r : ℝ) * Real.sqrt ((P.N : ℝ) ^ 3 / (P.tau : ℝ))⌋₊
lemma ZgK (D : Zf k r) : r ≤ D.ZbA := by
 have ht : (0 : ℝ) < D.tau := by exact_mod_cast D.Zqm
 have h : (1 : ℝ) ≤ (D.N : ℝ) ^ 3 / D.tau := (le_div_iff₀ ht).2 (by
  rw [one_mul]; exact_mod_cast D.Zrc)
 apply Nat.le_floor
 simpa using mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (Nat.cast_nonneg r)
lemma ZlV (D : Zf k r) (hr : 64 ≤ r) :
  Real.rpow (D.ZbA : ℝ) (-2 + 1 / (100000 * (k : ℝ))) ≤
   D.tau / (16 * (D.N : ℝ) ^ 3) := by
 let x := Real.sqrt ((D.N : ℝ) ^ 3 / D.tau)
 let n : ℝ := D.ZbA
 have hk := D.two_le_k
 have hN : (1 : ℝ) ≤ D.N := by exact_mod_cast D.N_pos
 have ht : (1 : ℝ) ≤ D.tau := by exact_mod_cast D.Zqm
 have hbox : (D.N : ℝ) ≤ (r : ℝ) ^ (31620 * k) := by exact_mod_cast D.ZlU
 have hr' : (64 : ℝ) ≤ r := by exact_mod_cast hr
 have hn : (r : ℝ) ≤ n := by dsimp [n]; exact_mod_cast D.ZgK
 have hn0 : 0 < n := by linarith
 have hx : x ^ 2 = (D.N : ℝ) ^ 3 / D.tau := Real.sq_sqrt (by positivity)
 have hxN : x ≤ (D.N : ℝ) ^ 2 := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨sq_nonneg _, ?_⟩
  exact (div_le_self (by positivity) ht).trans (by rw [← pow_mul]; exact pow_le_pow_right₀ hN (by norm_num))
 have hsize : n ≤ (r : ℝ) ^ (100000 * (k : ℝ)) := by
  rw [show 100000 * (k : ℝ) = ((100000 * k : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
  calc
   n ≤ r * x := Nat.floor_le (by positivity)
   _ ≤ r * ((r : ℝ) ^ (31620 * k)) ^ 2 := by gcongr; exact hxN.trans (by gcongr)
   _ = (r : ℝ) ^ (31620 * k * 2 + 1) := by rw [← pow_mul, pow_succ, mul_comm]
   _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
 have hA : 0 < 100000 * (k : ℝ) := by positivity
 have hroot := Real.rpow_le_rpow hn0.le hsize (one_div_pos.mpr hA).le
 rw [← Real.rpow_mul (Nat.cast_nonneg r), mul_one_div_cancel hA.ne', Real.rpow_one] at hroot
 have hf : (r : ℝ) * x < n + 1 := Nat.lt_floor_add_one _
 have hs : ((r : ℝ) * x) ^ 2 ≤ (2 * n) ^ 2 := by
  exact pow_le_pow_left₀ (by dsimp [x]; positivity) (by linarith) _
 rw [mul_pow, hx, ← mul_div_assoc, div_le_iff₀ (by linarith)] at hs
 simp only [Real.rpow_eq_pow]
 rw [show -2 + 1 / (100000 * (k : ℝ)) = 1 / (100000 * (k : ℝ)) - 2 by ring,
  Real.rpow_sub hn0, Real.rpow_two, div_le_div_iff₀ (by positivity) (by positivity)]
 calc
  _ ≤ (r : ℝ) * (16 * (D.N : ℝ) ^ 3) := by gcongr
  _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) * (r - 64) by exact mul_nonneg (Nat.cast_nonneg r) (by linarith)) (show 0 ≤ (D.N : ℝ) ^ 3 by positivity)]
end Zf
theorem ZbO
  (hconstruction : ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → r.Prime → Odd r →
   ∀ D : Zf Za r, ∃ P : Finset Point,
    P.card = D.ZbA ∧ Zaz P ∧
    Zal P (D.tau / (16 * (D.N : ℝ) ^ 3))) :
  0 < heilbronnExponent ∧
   ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
    Filter.Tendsto n Filter.atTop Filter.atTop ∧
    ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ Zaz (P j) ∧
     Zal (P j)
      (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
 obtain ⟨r0, hc⟩ := hconstruction
 have witness (j : ℕ) : ∃ n : ℕ, ∃ P : Finset Point, j ≤ n ∧ 3 ≤ n ∧ P.card = n ∧
   Zaz P ∧ Zal P (Real.rpow (n : ℝ) (-2 + heilbronnExponent)) := by
  obtain ⟨r, hr, hp⟩ := Nat.exists_infinite_primes (j + 64 + r0 + 400 * Za ^ 2)
  obtain ⟨D⟩ := Zjy Zjn (r := r) (by omega)
  obtain ⟨P, hcard, hs, ha⟩ := hc r (by omega) hp (hp.odd_of_ne_two (by omega)) D
  have hn := D.ZgK
  refine ⟨_, P, by omega, by omega, hcard, hs, ?_⟩
  intro p hp q hq s hs hpq hps hqs
  exact (D.ZlV (by omega)).trans (ha p hp q hq s hs hpq hps hqs)
 choose n P hn h using witness
 have hk : 0 < (Za : ℝ) := by exact_mod_cast Zfb
 exact ⟨one_div_pos.mpr (mul_pos (by norm_num) hk), n, P,
  Filter.tendsto_atTop_mono hn Filter.tendsto_id, h⟩
end Problem355.Parameters
end
end OAI
end
section
namespace OAI
namespace Problem355.Zu
noncomputable section
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
def Zh (μ : α → ℝ) (x : ι → α) : ℝ := ∏ i, μ (x i)
lemma Zjo (μ : α → ℝ) (hμ : ∑ a, μ a = 1) :
  ∑ x : ι → α, Zh μ x = 1 := by
 classical
 have h := (Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset α))
  (fun _ a => μ a)).symm
 simpa [Zh, hμ] using h
omit [Fintype α] [DecidableEq ι] in
lemma ZgL (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (x : ι → α) :
  0 ≤ Zh μ x :=
 Finset.prod_nonneg fun i _ => hμ (x i)
omit [Fintype α] [DecidableEq ι] in
lemma Zny (μ : α → ℝ) (p : ι → Prop) [DecidablePred p]
  (x : ι → α) : Zh μ x =
   Zh μ (fun i : {i // p i} => x i) *
    Zh μ (fun i : {i // ¬p i} => x i) := by
 exact (Fintype.prod_subtype_mul_prod_subtype p (fun i => μ (x i))).symm
lemma ZiQ (μ : α → ℝ) (hμ : ∑ a, μ a = 1)
  (p : ι → Prop) [DecidablePred p] (F : ({i // p i} → α) → ℝ) :
  (∑ x : ι → α, Zh μ x * F (fun i => x i)) =
   ∑ y : {i // p i} → α, Zh μ y * F y := by
 classical
 let e := Equiv.piEquivPiSubtypeProd p (fun _ : ι => α)
 calc
  (∑ x : ι → α, Zh μ x * F (fun i => x i)) =
    ∑ yz : ({i // p i} → α) × ({i // ¬p i} → α),
     (Zh μ yz.1 * Zh μ yz.2) * F yz.1 := by
   apply Fintype.sum_equiv e
   intro x
   rw [Zny μ p x]
   rfl
  _ = ∑ y : {i // p i} → α, Zh μ y * F y := by
   rw [Fintype.sum_prod_type]
   apply Finset.sum_congr rfl
   intro y _
   calc
    (∑ z : {i // ¬p i} → α,
      (Zh μ y * Zh μ z) * F y) =
      ∑ z : {i // ¬p i} → α,
       (Zh μ y * F y) * Zh μ z := by
     apply Finset.sum_congr rfl
     intro z _
     ring
    _ = Zh μ y * F y := by
     rw [← Finset.mul_sum, Zjo μ hμ, mul_one]
lemma Zle {κ : Type*} [Fintype κ] [DecidableEq κ]
  (μ : α → ℝ) (hμ : ∑ a, μ a = 1) (e : κ → ι)
  (he : Function.Injective e) (F : (κ → α) → ℝ) :
  (∑ x : ι → α, Zh μ x * F (x ∘ e)) =
   ∑ y : κ → α, Zh μ y * F y := by
 classical
 let : Fintype (Set.range e) := Subtype.fintype _
 let er : κ ≃ Set.range e := Equiv.ofInjective e he
 let ar := Equiv.piCongrLeft (fun _ : Set.range e => α) er
 have hrestrict := ZiQ μ hμ
  (fun i => i ∈ Set.range e) (fun y => F (fun j => y (er j)))
 change (∑ x : ι → α, Zh μ x * F (x ∘ e)) = _ at hrestrict
 rw [hrestrict]
 apply Fintype.sum_equiv ar.symm
 intro y
 have hprod : Zh μ y = Zh μ (ar.symm y) := by
  exact (er.prod_comp (fun i => μ (y i))).symm
 rw [hprod]
 rfl
variable {Θ : Type*}
def Zak (ρ : Θ → ℝ) (μ : Θ → α → ℝ) (z : Θ × (ι → α)) : ℝ :=
 ρ z.1 * Zh (μ z.1) z.2
omit [Fintype α] [DecidableEq ι] in
lemma Znz (ρ : Θ → ℝ) (μ : Θ → α → ℝ)
  (hρ : ∀ θ, 0 ≤ ρ θ) (hμ : ∀ θ a, 0 ≤ μ θ a) (z : Θ × (ι → α)) :
  0 ≤ Zak ρ μ z :=
 mul_nonneg (hρ z.1) (ZgL (μ z.1) (hμ z.1) z.2)
lemma Zpf [Fintype Θ] (ρ : Θ → ℝ) (μ : Θ → α → ℝ)
  (hρ : ∑ θ, ρ θ = 1) (hμ : ∀ θ, ∑ a, μ θ a = 1) :
  ∑ z : Θ × (ι → α), Zak ρ μ z = 1 := by
 classical
 simp only [Zak, Fintype.sum_prod_type]
 simp_rw [← Finset.mul_sum, Zjo _ (hμ _), mul_one]
 exact hρ
lemma ZkV [Fintype Θ] {κ : Type*} [Fintype κ] [DecidableEq κ]
  (ρ : Θ → ℝ) (μ : Θ → α → ℝ) (hμ : ∀ θ, ∑ a, μ θ a = 1)
  (e : κ → ι) (he : Function.Injective e) (F : Θ → (κ → α) → ℝ) :
  (∑ z : Θ × (ι → α), Zak ρ μ z * F z.1 (z.2 ∘ e)) =
   ∑ z : Θ × (κ → α), Zak ρ μ z * F z.1 z.2 := by
 classical
 simp only [Zak, Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro θ _
 rw [Zle (μ θ) (hμ θ) e he (F θ)]
lemma ZmH [Fintype Θ]
  (ρ : Θ → ℝ) (μ : Θ → α → ℝ) (hμ : ∀ θ, ∑ a, μ θ a = 1)
  {i j : ι} (hij : i ≠ j) (F : Θ → α → α → ℝ) :
  (∑ z : Θ × (ι → α), Zak ρ μ z * F z.1 (z.2 i) (z.2 j)) =
   ∑ z : Θ × (Fin 2 → α), Zak ρ μ z * F z.1 (z.2 0) (z.2 1) := by
 have he : Function.Injective (![i, j] : Fin 2 → ι) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all
 simpa using ZkV ρ μ hμ (![i, j] : Fin 2 → ι) he
  (fun θ x => F θ (x 0) (x 1))
lemma Zlf [Fintype Θ]
  (ρ : Θ → ℝ) (μ : Θ → α → ℝ) (hμ : ∀ θ, ∑ a, μ θ a = 1)
  {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
  (F : Θ → α → α → α → ℝ) :
  (∑ z : Θ × (ι → α), Zak ρ μ z * F z.1 (z.2 i) (z.2 j) (z.2 k)) =
   ∑ z : Θ × (Fin 3 → α),
    Zak ρ μ z * F z.1 (z.2 0) (z.2 1) (z.2 2) := by
 have he : Function.Injective (![i, j, k] : Fin 3 → ι) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all
 simpa using ZkV ρ μ hμ (![i, j, k] : Fin 3 → ι) he
  (fun θ x => F θ (x 0) (x 1) (x 2))
end
end Problem355.Zu
end OAI
end
section
namespace OAI
open Finset
noncomputable section
namespace Problem355.ZV
lemma Zlg (p q r : Point) : ZaL p q r = ZaL q p r := by
 unfold ZaL
 have h : (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) =
  -((p.1 - q.1) * (r.2 - q.2) - (p.2 - q.2) * (r.1 - q.1)) := by ring
 rw [h, abs_neg]
lemma ZkI (p q r : Point) : ZaL p q r = ZaL p r q := by
 unfold ZaL
 have h : (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) =
  -((r.1 - p.1) * (q.2 - p.2) - (r.2 - p.2) * (q.1 - p.1)) := by ring
 rw [h, abs_neg]
variable {Θ X : Type*} [Fintype Θ] [Fintype X]
def Zgb (ρ : Θ → ℝ) (μ : Θ → X → ℝ) (point : Θ → X → Point) : ℝ := by
 classical
 exact ∑ z : Θ × (Fin 2 → X),
  if point z.1 (z.2 0) = point z.1 (z.2 1)
   then Zu.Zak ρ μ z else 0
def Zjz (ρ : Θ → ℝ) (μ : Θ → X → ℝ) (point : Θ → X → Point) (a : ℝ) : ℝ := by
 classical
 exact ∑ z : Θ × (Fin 3 → X),
  if ZaW.Zbo a (point z.1 (z.2 0)) (point z.1 (z.2 1))
    (point z.1 (z.2 2))
   then Zu.Zak ρ μ z else 0
theorem exists_configuration (m n : ℕ) (hn : n ≤ m) (a p q : ℝ)
   (ρ : Θ → ℝ) (μ : Θ → X → ℝ) (point : Θ → X → Point)
   (hρ0 : ∀ θ, 0 ≤ ρ θ) (hρ1 : ∑ θ, ρ θ = 1)
   (hμ0 : ∀ θ x, 0 ≤ μ θ x) (hμ1 : ∀ θ, ∑ x, μ θ x = 1)
   (hsquare : ∀ θ x, Zbf (point θ x))
   (hpair : Zgb ρ μ point ≤ p) (htriple : Zjz ρ μ point a ≤ q)
   (hbudget : (Nat.choose m 2 : ℝ) * p + (Nat.choose m 3 : ℝ) * q <
    ((m - n + 1 : ℕ) : ℝ)) :
   ∃ P : Finset Point, P.card = n ∧ Zaz P ∧ Zal P a := by
 classical
 let W : Θ × (Fin m → X) → ℝ := Zu.Zak ρ μ
 let f : (Θ × (Fin m → X)) → Fin m → Point := fun z i => point z.1 (z.2 i)
 let E (d : ℕ) := (univ : Finset (Fin m)).powersetCard d
 let B (z : Θ × (Fin m → X)) (e : Finset (Fin m)) := ∃ i ∈ e, ∃ j ∈ e, i ≠ j ∧ f z i = f z j
 let C (z : Θ × (Fin m → X)) (e : Finset (Fin m)) := ∃ i ∈ e, ∃ j ∈ e, ∃ k ∈ e,
   i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ZaW.Zbo a (f z i) (f z j) (f z k)
 have hb := ZaW.Zik W (E 2) B p (by
   intro e he
   obtain ⟨i,j,hij,rfl⟩ := card_eq_two.mp (mem_powersetCard.mp he).2
   have hiff z : B z {i,j} ↔ f z i = f z j := by
    simp [B, hij, Ne.symm hij, eq_comm]
   simp_rw [hiff]
   apply le_trans _ hpair
   exact le_of_eq (by simpa [W, f, Zgb, mul_ite] using
    (Zu.ZmH ρ μ hμ1 hij
     (fun θ x y => if point θ x = point θ y then (1:ℝ) else 0))))
 have hc := ZaW.Zik W (E 3) C q (by
   intro e he
   obtain ⟨i,j,k,hij,hik,hjk,rfl⟩ := card_eq_three.mp (mem_powersetCard.mp he).2
   have hiff z : C z {i,j,k} ↔ ZaW.Zbo a (f z i) (f z j) (f z k) := by
    simp [C, *, ne_comm, ZaW.Zbo, Zlg, ZkI]
    tauto
   simp_rw [hiff]
   apply le_trans _ htriple
   exact le_of_eq (by simpa [W, f, Zjz, mul_ite] using
    (Zu.Zlf ρ μ hμ1 hij hik hjk (fun θ x y z =>
     if ZaW.Zbo a (point θ x) (point θ y) (point θ z) then (1:ℝ) else 0))))
 let P z := (E 2).filter (B z)
 let Q z := (E 3).filter (C z)
 obtain ⟨z, _, hz⟩ := ZaW.ZfY univ W
   (fun z => (P z).card + (Q z).card) (m - n + 1)
   (fun z _ => Zu.Znz ρ μ hρ0 hμ0 z)
   (Zu.Zpf ρ μ hρ1 hμ1) (by
    simp only [Nat.cast_add, mul_add, sum_add_distrib]
    exact (add_le_add hb hc).trans_lt (by simpa [E] using hbudget))
 obtain ⟨T, _, hT, hav⟩ := ZaW.ZgI univ (P z ∪ Q z) (by
   intro e he
   rcases mem_union.mp he with h | h <;>
    have hh := (mem_powersetCard.mp (mem_filter.mp h).1).2 <;> exact card_pos.mp (by omega)) n (by
   simp only [card_univ, Fintype.card_fin]; have := card_union_le (P z) (Q z); omega)
 rw [← hT]
 apply ZaW.Znr T (f z) a _ (fun i _ => hsquare _ _) _
 · intro i hi j hj he
   by_contra hij
   apply hav {i,j} (mem_union_left _ (mem_filter.mpr ⟨mem_powersetCard.mpr
    ⟨subset_univ _, card_pair hij⟩, i, by simp, j, by simp, hij, he⟩))
   simpa [insert_subset_iff] using And.intro hi hj
 · intro i hi j hj k hk hij hik hjk he
   apply hav {i,j,k} (mem_union_right _ (mem_filter.mpr ⟨mem_powersetCard.mpr
    ⟨subset_univ _, card_triple_eq_three_iff.mpr ⟨hij,hik,hjk⟩⟩,
    i, by simp, j, by simp, k, by simp, hij,hik,hjk,he⟩))
   simpa [insert_subset_iff] using And.intro hi (And.intro hj hk)
end Problem355.ZV
end
end OAI
end
section
namespace OAI
namespace Problem355.Zmw
lemma Zht {r N : ℝ} {m : ℕ}
   (hr : 1 ≤ r) (hN1 : 1 ≤ N) (hN : N ≤ r ^ m) :
   0 ≤ Real.log (2 * N) ∧ Real.log (2 * N) ≤ (m + 1 : ℝ) * r := by
 have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
 have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN1
 have hlogr : Real.log r ≤ r := Real.log_le_self hr0.le
 have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
   have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
   linarith
 have hlogN : Real.log N ≤ (m : ℝ) * Real.log r := by
   simpa only [Real.log_pow] using Real.log_le_log hN0 hN
 constructor
 · apply Real.log_nonneg
   linarith
 · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne']
   have hm : (m : ℝ) * Real.log r ≤ (m : ℝ) * r :=
    mul_le_mul_of_nonneg_left hlogr (Nat.cast_nonneg m)
   nlinarith
lemma ZqC {r H n : ℝ} (hr : 1 ≤ r) (hH : r ≤ H)
  (hn : n ≤ r * H ^ 15) :
  n * H ^ 6 / (H ^ 10) ^ 3 ≤ 1 / r ^ 8 := by
 have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
 have hH0 : 0 < H := hr0.trans_le hH
 calc
  n * H ^ 6 / (H ^ 10) ^ 3 ≤
    (r * H ^ 15) * H ^ 6 / (H ^ 10) ^ 3 := by
   gcongr
  _ = r / H ^ 9 := by field_simp
  _ ≤ r / r ^ 9 := by gcongr
  _ = 1 / r ^ 8 := by field_simp
lemma ZpG {r N n τ h B L A : ℝ}
  (hr : 1 ≤ r) (hN : 0 < N) (ht : 0 < τ)
  (hh0 : 0 ≤ h)
  (hn : n ^ 2 * τ ≤ r ^ 2 * N ^ 3)
  (hh : h ≤ 3 * B * τ) (hB : B ≤ r ^ 31)
  (hL : L ^ 2 ≤ A ^ 2 * r ^ 2) :
  n ^ 2 * L ^ 2 * h / (N ^ 3 * r ^ 41) ≤ 3 * A ^ 2 / r ^ 6 := by
 have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
 have hn' : n ^ 2 ≤ r ^ 2 * N ^ 3 / τ := (le_div_iff₀ ht).mpr hn
 calc
  n ^ 2 * L ^ 2 * h / (N ^ 3 * r ^ 41) ≤
    (r ^ 2 * N ^ 3 / τ) * (A ^ 2 * r ^ 2) * (3 * B * τ) /
     (N ^ 3 * r ^ 41) := by
   gcongr
  _ ≤ (r ^ 2 * N ^ 3 / τ) * (A ^ 2 * r ^ 2) * (3 * r ^ 31 * τ) /
     (N ^ 3 * r ^ 41) := by
   gcongr
  _ = 3 * A ^ 2 / r ^ 6 := by field_simp
lemma ZpH {r H n τ : ℝ} (hr : 1 ≤ r) (hH : r ≤ H)
  (ht : 1 ≤ τ) (hn : n ^ 2 * τ ≤ r ^ 2 * (H ^ 10) ^ 3) :
  n ≤ r * H ^ 15 := by
 have hr0 : 0 ≤ r := le_trans (by norm_num) hr
 have hH0 : 0 ≤ H := hr0.trans hH
 have hnn : n ^ 2 ≤ n ^ 2 * τ := le_mul_of_one_le_right (sq_nonneg n) ht
 have heq : (r * H ^ 15) ^ 2 = r ^ 2 * (H ^ 10) ^ 3 := by ring
 have hpos : 0 ≤ r * H ^ 15 := by positivity
 nlinarith
lemma ZnA {r H n τ h B : ℝ} {m : ℕ}
  (hr : 1 ≤ r) (hH : r ≤ H) (ht : 1 ≤ τ) (hh0 : 0 ≤ h)
  (hn : n ^ 2 * τ ≤ r ^ 2 * (H ^ 10) ^ 3)
  (hh : h ≤ 3 * B * τ) (hB : B ≤ r ^ 31)
  (hpoly : H ^ 10 ≤ r ^ m) :
  n ^ 2 * (Real.log (2 * H ^ 10)) ^ 2 * h /
   ((H ^ 10) ^ 3 * r ^ 41) ≤ 3 * (m + 1 : ℝ) ^ 2 / r ^ 6 := by
 have hH1 : 1 ≤ H := hr.trans hH
 have hN1 : 1 ≤ H ^ 10 := one_le_pow₀ hH1
 have hlog := Zht hr hN1 hpoly
 apply ZpG hr (lt_of_lt_of_le (by norm_num) hN1)
  (lt_of_lt_of_le (by norm_num) ht) hh0 hn hh hB
 simpa only [mul_pow] using (sq_le_sq₀ hlog.1 (by positivity)).mpr hlog.2
lemma ZqP {r A Cpair Ctriple epair etriple : ℝ}
  (hr : 1 ≤ r) (hCp : 0 ≤ Cpair) (hCt : 0 ≤ Ctriple)
  (hp : epair ≤ 1 / r ^ 8) (ht : etriple ≤ 3 * A ^ 2 / r ^ 6)
  (hlarge : 4 * Cpair + 24 * Ctriple * A ^ 2 < r) :
  4 * Cpair * epair + 8 * Ctriple * etriple < 1 := by
 have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
 have hr8 : r ≤ r ^ 8 := by
  simpa only [pow_one] using (pow_le_pow_right₀ hr (by norm_num : 1 ≤ 8))
 have hr6 : r ≤ r ^ 6 := by
  simpa only [pow_one] using (pow_le_pow_right₀ hr (by norm_num : 1 ≤ 6))
 calc
  4 * Cpair * epair + 8 * Ctriple * etriple ≤
    4 * Cpair * (1 / r ^ 8) + 8 * Ctriple * (3 * A ^ 2 / r ^ 6) :=
   add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
    (mul_le_mul_of_nonneg_left ht (by positivity))
  _ = (4 * Cpair) / r ^ 8 + (24 * Ctriple * A ^ 2) / r ^ 6 := by ring
  _ ≤ (4 * Cpair) / r + (24 * Ctriple * A ^ 2) / r :=
   add_le_add (div_le_div_of_nonneg_left (by positivity) hr0 hr8)
    (div_le_div_of_nonneg_left (by positivity) hr0 hr6)
  _ = (4 * Cpair + 24 * Ctriple * A ^ 2) / r := by ring
  _ < 1 := (div_lt_one hr0).mpr hlarge
theorem Zdq {r H n τ h B Cpair Ctriple : ℝ} {m : ℕ}
  (hr : 1 ≤ r) (hH : r ≤ H) (ht : 1 ≤ τ) (hh0 : 0 ≤ h)
  (hn : n ^ 2 * τ ≤ r ^ 2 * (H ^ 10) ^ 3)
  (hh : h ≤ 3 * B * τ) (hB : B ≤ r ^ 31)
  (hpoly : H ^ 10 ≤ r ^ m)
  (hCp : 0 ≤ Cpair) (hCt : 0 ≤ Ctriple)
  (hlarge : 4 * Cpair + 24 * Ctriple * (m + 1 : ℝ) ^ 2 < r) :
  4 * Cpair * (n * H ^ 6 / (H ^ 10) ^ 3) +
   8 * Ctriple * (n ^ 2 * (Real.log (2 * H ^ 10)) ^ 2 * h /
    ((H ^ 10) ^ 3 * r ^ 41)) < 1 := by
 exact ZqP hr hCp hCt
  (ZqC hr hH (ZpH hr hH ht hn))
  (ZnA hr hH ht hh0 hn hh hB hpoly) hlarge
end Problem355.Zmw
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Znk
open Finset
lemma ZpI {n : ℕ} {p q : ℝ} (hn : 0 < n)
  (hp : 0 ≤ p) (hq : 0 ≤ q)
  (hrelative : 4 * (n : ℝ) * p + 8 * (n : ℝ) ^ 2 * q < 1) :
  (Nat.choose (2 * n) 2 : ℝ) * p + (Nat.choose (2 * n) 3 : ℝ) * q <
   ((2 * n - n + 1 : ℕ) : ℝ) := by
 have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
 have hc2 : (Nat.choose (2 * n) 2 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
  have hc : (Nat.choose (2 * n) 2 : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ 2 := by
   exact_mod_cast Nat.choose_le_pow (2 * n) 2
  norm_num [mul_pow] at hc
  exact hc
 have hc3 : (Nat.choose (2 * n) 3 : ℝ) ≤ 8 * (n : ℝ) ^ 3 := by
  have hc : (Nat.choose (2 * n) 3 : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ 3 := by
   exact_mod_cast Nat.choose_le_pow (2 * n) 3
  norm_num [mul_pow] at hc
  exact hc
 calc
  (Nat.choose (2 * n) 2 : ℝ) * p + (Nat.choose (2 * n) 3 : ℝ) * q ≤
    4 * (n : ℝ) ^ 2 * p + 8 * (n : ℝ) ^ 3 * q :=
   add_le_add (mul_le_mul_of_nonneg_right hc2 hp)
    (mul_le_mul_of_nonneg_right hc3 hq)
  _ = (4 * (n : ℝ) * p + 8 * (n : ℝ) ^ 2 * q) * n := by ring
  _ < (n : ℝ) := by simpa using mul_lt_mul_of_pos_right hrelative hn0
  _ < ((2 * n - n + 1 : ℕ) : ℝ) := by
   exact_mod_cast (show n < 2 * n - n + 1 by omega)
end Problem355.Znk
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZaD
open Parameters Parameters.Zf
structure ZaY where
 Environment : Type
 ZaA : Type
 environmentFintype : Fintype Environment
 columnFintype : Fintype ZaA
 rho : Environment → ℝ
 mu : Environment → ZaA → ℝ
 point : Environment → ZaA → Point
 rho_nonneg : ∀ θ, 0 ≤ rho θ
 rho_sum : @Finset.sum Environment ℝ _ Finset.univ rho = 1
 mu_nonneg : ∀ θ x, 0 ≤ mu θ x
 mu_sum : ∀ θ, @Finset.sum ZaA ℝ _ Finset.univ (mu θ) = 1
 in_square : ∀ θ x, Zbf (point θ x)
instance ZaY.Zsh (L : ZaY) : Fintype L.Environment := L.environmentFintype
instance ZaY.Zsi (L : ZaY) : Fintype L.ZaA := L.columnFintype
def ZaY.ZbB (L : ZaY) : ℝ :=
 ZV.Zgb L.rho L.mu L.point
def ZaY.Zav (L : ZaY) (a : ℝ) : ℝ :=
 ZV.Zjz L.rho L.mu L.point a
lemma Zdq {k r : ℕ} (D : Zf k r)
  {Cp Ct : ℝ} (hCp : 0 ≤ Cp) (hCt : 0 ≤ Ct)
  (hlarge : 4 * Cp + 24 * Ct * (31620 * k + 1 : ℝ) ^ 2 < r) :
  4 * (D.ZbA : ℝ) * (Cp * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3) +
   8 * (D.ZbA : ℝ) ^ 2 *
    (Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
     ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41)) < 1 := by
 have hr : (1 : ℝ) ≤ r := by exact_mod_cast D.r_pos
 have hM : (r : ℝ) ≤ D.M := by exact_mod_cast D.Zrx
 have ht : (1 : ℝ) ≤ D.tau := by exact_mod_cast D.Zqm
 have hN : (D.N : ℝ) = (D.M : ℝ) ^ 10 := by simp only [N, Nat.cast_pow]
 have hs : (D.ZbA : ℝ) ^ 2 * D.tau ≤ (r : ℝ) ^ 2 * ((D.M : ℝ) ^ 10) ^ 3 := by
  rw [← hN]
  calc
   _ ≤ ((r : ℝ) * Real.sqrt ((D.N : ℝ) ^ 3 / D.tau)) ^ 2 * D.tau := by
    gcongr; exact Nat.floor_le (by positivity)
   _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]; field_simp
 have hh : (D.h : ℝ) ≤ 3 * (D.B : ℝ) * D.tau := by
  exact_mod_cast Zhs D.ZdY D.two_le_k
 have hb : (D.B : ℝ) ≤ (r : ℝ) ^ 31 := by exact_mod_cast D.base_polynomial
 have hp : (D.M : ℝ) ^ 10 ≤ (r : ℝ) ^ (31620 * k) := by
  rw [← hN]
  exact_mod_cast D.ZlU
 have hl : 4 * Cp + 24 * Ct * ((31620 * k : ℕ) + 1 : ℝ) ^ 2 < r := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlarge
 have he := Zmw.Zdq hr hM ht (Nat.cast_nonneg D.h)
  hs hh hb hp hCp hCt hl
 rw [← hN] at he
 convert he using 1; ring
theorem ZmI {k r : ℕ} (D : Zf k r)
  (L : ZaY) {Cp Ct : ℝ} (hCp : 0 ≤ Cp) (hCt : 0 ≤ Ct)
  (hlarge : 4 * Cp + 24 * Ct * (31620 * k + 1 : ℝ) ^ 2 < r)
  (hpair : L.ZbB ≤ Cp * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3)
  (htriple : L.Zav (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
   Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h / ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41)) :
  ∃ P : Finset Point, P.card = D.ZbA ∧ Zaz P ∧
   Zal P (D.tau / (16 * (D.N : ℝ) ^ 3)) := by
 have hn : 0 < D.ZbA := D.r_pos.trans_le D.ZgK
 have hbudget := Znk.ZpI hn
  (show 0 ≤ Cp * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 by positivity)
  (show 0 ≤ Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
   ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) by positivity)
  (Zdq D hCp hCt hlarge)
 exact ZV.exists_configuration (2 * D.ZbA) D.ZbA
  (by omega) _ _ _ L.rho L.mu L.point L.rho_nonneg L.rho_sum L.mu_nonneg L.mu_sum
  L.in_square hpair htriple hbudget
theorem ZdF
  (Cp Ct : ℝ) (hCp : 0 ≤ Cp) (hCt : 0 ≤ Ct)
  (hconstruction : ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → r.Prime → Odd r →
   ∀ D : Zf Za r, ∃ L : ZaY,
    L.ZbB ≤ Cp * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 ∧
    L.Zav (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
     Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
      ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41)) :
  0 < heilbronnExponent ∧
   ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
    Filter.Tendsto n Filter.atTop Filter.atTop ∧
    ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ Zaz (P j) ∧
     Zal (P j)
      (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
 obtain ⟨r0, hc⟩ := hconstruction
 obtain ⟨r1, hr1⟩ := exists_nat_gt
  (4 * Cp + 24 * Ct * (31620 * (Za : ℝ) + 1) ^ 2)
 apply ZbO
 refine ⟨max r0 r1, ?_⟩
 intro r hr hp ho D
 obtain ⟨L, hpair, htriple⟩ := hc r ((le_max_left _ _).trans hr) hp ho D
 have hlarge : 4 * Cp + 24 * Ct * (31620 * (Za : ℝ) + 1) ^ 2 < r :=
  hr1.trans_le (by exact_mod_cast (le_max_right r0 r1).trans hr)
 exact ZmI D L hCp hCt hlarge hpair htriple
end Problem355.ZaD
end
end OAI
end
section
namespace OAI
namespace Problem355.Zu
noncomputable section
variable {α β ι : Type*}
def Zbp [Fintype β] (p : β → ℝ) (ν : β → α → ℝ) (a : α) : ℝ :=
 ∑ b, p b * ν b a
lemma ZmJ [Fintype β] (p : β → ℝ) (ν : β → α → ℝ)
  (hp : ∀ b, 0 ≤ p b) (hν : ∀ b a, 0 ≤ ν b a) (a : α) :
  0 ≤ Zbp p ν a :=
 Finset.sum_nonneg fun b _ => mul_nonneg (hp b) (hν b a)
lemma ZoA [Fintype α] [Fintype β]
  (p : β → ℝ) (ν : β → α → ℝ)
  (hp : ∑ b, p b = 1) (hν : ∀ b, ∑ a, ν b a = 1) :
  ∑ a, Zbp p ν a = 1 := by
 unfold Zbp
 rw [Finset.sum_comm]
 simp_rw [← Finset.mul_sum, hν, mul_one]
 exact hp
lemma ZlW [Fintype ι] [DecidableEq ι] [Fintype β]
  (p : β → ℝ) (ν : β → α → ℝ) (x : ι → α) :
  Zh (Zbp p ν) x =
   ∑ labels : ι → β, Zh p labels * ∏ i, ν (labels i) (x i) := by
 classical
 unfold Zh Zbp
 have h := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset β))
  (fun i b => p b * ν b (x i))
 simpa [Finset.prod_mul_distrib] using h
lemma ZfF
  [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
  (p : β → ℝ) (ν : β → α → ℝ) (F : (ι → α) → ℝ) :
  (∑ x : ι → α, Zh (Zbp p ν) x * F x) =
   ∑ labels : ι → β, Zh p labels *
    ∑ x : ι → α, (∏ i, ν (labels i) (x i)) * F x := by
 simp_rw [ZlW, Finset.sum_mul]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro labels _
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro x _
 ring
end
end Problem355.Zu
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zas
open Zc Zu ZaD
def ZnW {Θ D : Type} [Fintype Θ] [Fintype D]
  (h q L s : ℕ) [NeZero h] [NeZero q]
  (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
  (rho : Θ → ℝ) (p : D → ℝ)
  (a : Θ → D → Fin 3 → ZMod h)
  (V : Θ → Finset (Fin 3 → ZMod q))
  (hrho : ∀ θ, 0 ≤ rho θ) (hsum : ∑ θ, rho θ = 1)
  (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
  (hV : ∀ θ, (V θ).card = s) : ZaY where
 Environment := Θ
 ZaA := Box (L * (h * q)) 3 (Zm (L * (h * q)))
 environmentFintype := inferInstance
 columnFintype := inferInstance
 rho := rho
 mu := fun θ => Zbp p (fun d => ZeJ h q L
  (Zm (L * (h * q))) (a θ d) (V θ) s)
 point := fun _ x => project x
 rho_nonneg := hrho
 rho_sum := hsum
 mu_nonneg := fun θ x => ZmJ p _ hp
  (fun d x => ZjV h q L _ (a θ d) (V θ) s x) x
 mu_sum := fun θ => ZoA p _ hpsum
  (fun d => Zqz h q L hc hL _ (a θ d) (V θ) s hs (hV θ))
 in_square := fun _ x => ZlN
  (mul_pos hL (mul_pos (NeZero.pos h) (NeZero.pos q))) x
def Zcs {Θ Ω D : Type}
  [Fintype Θ] [Fintype Ω] [Fintype D]
  (h q L s : ℕ) [NeZero h] [NeZero q]
  (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
  (rho : Θ → ℝ) (w : Ω → ℝ) (p : D → ℝ)
  (a : Θ → D → Fin 3 → ZMod h)
  (V : Ω → Finset (Fin 3 → ZMod q))
  (hrho : ∀ θ, 0 ≤ rho θ) (hsum : ∑ θ, rho θ = 1)
  (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
  (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
  (hV : ∀ ω, (V ω).card = s) : ZaY :=
 ZnW h q L s hc hL hs (fun z : Θ × Ω => rho z.1 * w z.2) p
  (fun z d => a z.1 d) (fun z => V z.2)
  (fun z => mul_nonneg (hrho z.1) (hw z.2))
  (by
   rw [Fintype.sum_prod_type]
   simp_rw [← Finset.mul_sum, hwsum, mul_one]
   exact hsum)
  hp hpsum (fun z => hV z.2)
def ZaB {Ω D : Type} [Fintype Ω] [Fintype D]
   (h q L s : ℕ) [NeZero h] [NeZero q]
   (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
   (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
   (V : Ω → Finset (Fin 3 → ZMod q))
   (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
   (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
   (hV : ∀ ω, (V ω).card = s) : ZaY := by
 classical
 let G := Matrix.SpecialLinearGroup (Fin 3) (ZMod h)
 apply Zcs h q L s hc hL hs
   (fun _ : G => 1 / (Nat.card G : ℝ)) w p (fun g d => g • c d) V
 · intro g
   positivity
 · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]
   exact mul_one_div_cancel (by positivity)
 · exact hw
 · exact hwsum
 · exact hp
 · exact hpsum
 · exact hV
end Problem355.Zas
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zas
open Zc Zu ZaD
open Finset
noncomputable local instance zCPD4 (p : Prop) : Decidable p := Classical.propDecidable p
theorem ZiR {Θ D X : Type*}
  [Fintype Θ] [Fintype D] [Fintype X]
  (rho : Θ → ℝ) (p : D → ℝ) (nu : Θ → D → X → ℝ)
  (F : (Fin 3 → X) → ℝ) :
  (∑ θ, rho θ * ∑ x : Fin 3 → X,
   Zh (Zbp p (nu θ)) x * F x) =
  ∑ d : Fin 3 → D, Zh p d *
   ∑ x : Fin 3 → X, (∑ θ, rho θ * ∏ i, nu θ (d i) (x i)) * F x := by
 simp_rw [ZfF, Finset.mul_sum]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro d _
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro x _
 rw [Finset.sum_mul, Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro θ _
 ring
theorem Zin {Ω D : Type} [Fintype Ω] [Fintype D]
  (h q L s : ℕ) [NeZero h] [NeZero q]
  (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
  (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
  (V : Ω → Finset (Fin 3 → ZMod q))
  (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
  (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
  (hV : ∀ ω, (V ω).card = s)
  (F : (Fin 3 → Box (L * (h * q)) 3 (Zm (L * (h * q)))) → ℝ) :
  let law := ZaB h q L s hc hL hs w p c V hw hwsum hp hpsum hV
  (∑ z : law.Environment × (Fin 3 → law.ZaA),
   Zak law.rho law.mu z * F z.2) =
  ∑ d : Fin 3 → D, Zh p d *
   ∑ x, Zb.ZaI
    (fun x i => residue h (x i)) (fun x i => residue q (x i))
    (ZD.Zt (ZD.Zz h) (fun i => c (d i)))
    w V s (L ^ 9) x * F x := by
 classical
 dsimp only
 change (∑ z : (ZD.Zz h × Ω) ×
   (Fin 3 → Box (L * (h * q)) 3 (Zm (L * (h * q)))),
  ((1 / (Nat.card (ZD.Zz h) : ℝ)) * w z.1.2) *
   Zh (Zbp p (fun d => ZeJ h q L
    (Zm (L * (h * q))) (z.1.1 • c d) (V z.1.2) s)) z.2 * F z.2) = _
 rw [Fintype.sum_prod_type]
 simp_rw [mul_assoc]
 conv_lhs =>
  arg 2
  ext θ
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_assoc]
 rw [ZiR]
 apply Finset.sum_congr rfl
 intro d _
 congr 1
 apply Finset.sum_congr rfl
 intro x _
 congr 1
 rw [Fintype.sum_prod_type]
 simpa only [Finset.mul_sum, mul_assoc, Pi.smul_apply] using
  (ZD.ZfB h q L
   (Zm (L * (h * q))) (fun i => c (d i)) w V s x)
def ZfU {N : ℕ} (a : ℝ)
  (x : Fin 3 → Box N 3 (Zm N)) : Prop :=
 ZaW.Zbo a (project (x 0)) (project (x 1)) (project (x 2))
def ZcM {N : ℕ} (τ : ℤ)
  (x : Fin 3 → Box N 3 (Zm N)) : Prop :=
 project (x 0) ≠ project (x 1) ∧ project (x 0) ≠ project (x 2) ∧
  project (x 1) ≠ project (x 2) ∧ |(ZD.Zg x).det| ≤ τ
theorem ZnX {N : ℕ} (x : Box N 3 (Zm N)) :
  Homogeneous.ZaX (N : ℝ) (fun i => ((x i).val : ℝ)) := by
 have hx : 0 ≤ (x 0).val ∧ (x 0).val < (N : ℤ) := by
  simpa [Zm] using (x 0).property
 have hy : 0 ≤ (x 1).val ∧ (x 1).val < (N : ℤ) := by
  simpa [Zm] using (x 1).property
 have hz : (N : ℤ) ≤ (x 2).val ∧ (x 2).val < (N : ℤ) + N :=
  (x 2).property
 unfold Homogeneous.ZaX
 dsimp only
 refine ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2,
  by exact_mod_cast hy.1, by exact_mod_cast hy.2,
  by exact_mod_cast hz.1, ?_⟩
 have hh : ((x 2).val : ℝ) < (N : ℝ) + N := by exact_mod_cast hz.2
 linarith
theorem ZdG {N : ℕ} (hN : 0 < N)
  {τ : ℤ} (hτ : 0 ≤ τ) (x : Fin 3 → Box N 3 (Zm N))
  (hx : ZfU ((τ : ℝ) / (16 * (N : ℝ) ^ 3)) x) :
  ZcM τ x := by
 have hcol (j : Fin 3) : Homogeneous.ZaX (N : ℝ)
   (Homogeneous.ZN (ZD.Zg x) j) :=
  ZnX (x j)
 have he := Homogeneous.ZfD
  (by exact_mod_cast hN) hτ (hcol 0) (hcol 1) (hcol 2)
  (ZD.Zg x).det
  (Homogeneous.Znt (ZD.Zg x)) hx
 exact ⟨he.1.1, he.1.2.1, he.1.2.2, he.2⟩
theorem ZeM {Ω D : Type} [Fintype Ω] [Fintype D]
  (h q L s : ℕ) [NeZero h] [NeZero q]
  (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
  (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
  (V : Ω → Finset (Fin 3 → ZMod q))
  (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
  (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
  (hV : ∀ ω, (V ω).card = s) (a : ℝ) :
  (ZaB h q L s hc hL hs w p c V hw hwsum hp hpsum hV).Zav a =
  ∑ d : Fin 3 → D, Zh p d *
   ∑ x ∈ (Finset.univ : Finset (Fin 3 → Box (L * (h * q)) 3
    (Zm (L * (h * q))))).filter (ZfU a), Zb.ZaI
    (fun x i => residue h (x i)) (fun x i => residue q (x i))
    (ZD.Zt (ZD.Zz h) (fun i => c (d i)))
    w V s (L ^ 9) x := by
 classical
 have he := Zin h q L s hc hL hs w p c V
  hw hwsum hp hpsum hV (fun x => if ZfU a x then 1 else 0)
 unfold ZaY.Zav ZV.Zjz
 change (∑ z : (ZD.Zz h × Ω) ×
   (Fin 3 → Box (L * (h * q)) 3 (Zm (L * (h * q)))),
  if ZfU a z.2 then
   Zak (ZaB h q L s hc hL hs w p c V hw hwsum hp hpsum hV).rho
    (ZaB h q L s hc hL hs w p c V hw hwsum hp hpsum hV).mu z
  else 0) = _
 simp only [ZaB, Zcs, ZnW,
  Finset.sum_filter, mul_ite, mul_one, mul_zero] at he ⊢
 convert he using 1
 all_goals congr 1
theorem Zcp {Ω D : Type}
   [Fintype Ω] [Fintype D]
   (h q L s : ℕ) [NeZero h] [NeZero q]
   (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
   (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
   (V : Ω → Finset (Fin 3 → ZMod q))
   (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
   (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
   (hV : ∀ ω, (V ω).card = s) {τ : ℤ} (hτ : 0 ≤ τ) :
   (ZaB h q L s hc hL hs w p c V hw hwsum hp hpsum hV).Zav
    ((τ : ℝ) / (16 * ((L * (h * q) : ℕ) : ℝ) ^ 3)) ≤
   ∑ d : Fin 3 → D, Zh p d *
    ∑ x ∈ (Finset.univ : Finset (Fin 3 → Box (L * (h * q)) 3
     (Zm (L * (h * q))))).filter (ZcM τ),
     Zb.ZaI
      (fun x i => residue h (x i)) (fun x i => residue q (x i))
      (ZD.Zt (ZD.Zz h) (fun i => c (d i)))
      w V s (L ^ 9) x := by
 classical
 rw [ZeM]
 apply Finset.sum_le_sum
 intro d _
 apply mul_le_mul_of_nonneg_left _ (ZgL p hp d)
 apply Finset.sum_le_sum_of_subset_of_nonneg
 · intro x hx
   refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
   exact ZdG
    (mul_pos hL (mul_pos (NeZero.pos h) (NeZero.pos q))) hτ x
    (Finset.mem_filter.mp hx).2
 · intro x _ _
   exact Zb.Zow _ _ _ w V s (L ^ 9) hw x
end Problem355.Zas
end
end OAI
end
section
namespace OAI
namespace Problem355.Zo
open Matrix
open scoped Matrix
abbrev Vector := Fin 3 → ℤ
def ZcE (v : Vector) : ℕ :=
 Int.gcd (Int.gcd (v 0) (v 1) : ℤ) (v 2)
def IsPrimitive (v : Vector) : Prop := ZcE v = 1
lemma ZgM (v : Vector) : ZcE v = 0 ↔ v = 0 := by
 rw [ZcE, Int.gcd_eq_zero_iff]
 constructor
 · rintro ⟨h01, h2⟩
   have h01' : Int.gcd (v 0) (v 1) = 0 := by exact_mod_cast h01
   obtain ⟨h0, h1⟩ := Int.gcd_eq_zero_iff.mp h01'
   ext i
   fin_cases i <;> simp_all
 · intro h
   subst v
   simp
lemma ZgN (v : Vector) (i : Fin 3) : (ZcE v : ℤ) ∣ v i := by
 have h01 := Int.gcd_dvd_left (Int.gcd (v 0) (v 1) : ℤ) (v 2)
 have h2 := Int.gcd_dvd_right (Int.gcd (v 0) (v 1) : ℤ) (v 2)
 fin_cases i
 · exact dvd_trans h01 (Int.gcd_dvd_left _ _)
 · exact dvd_trans h01 (Int.gcd_dvd_right _ _)
 · exact h2
lemma ZfG (v : Vector) :
  ∃ z : Vector, v ⬝ᵥ z = (ZcE v : ℤ) := by
 let d : ℤ := Int.gcd (v 0) (v 1)
 refine ⟨![Int.gcdA (v 0) (v 1) * Int.gcdA d (v 2),
  Int.gcdB (v 0) (v 1) * Int.gcdA d (v 2), Int.gcdB d (v 2)], ?_⟩
 have h01 := Int.gcd_eq_gcd_ab (v 0) (v 1)
 have h2 := Int.gcd_eq_gcd_ab d (v 2)
 simp only [vec3_dotProduct]
 dsimp only [Matrix.cons_val]
 change _ = (Int.gcd d (v 2) : ℤ)
 rw [h2]
 change _ = (Int.gcd (v 0) (v 1) : ℤ) * _ + _
 rw [h01]
 ring
lemma ZB (v : Vector) :
   IsPrimitive v ↔ ∃ z : Vector, v ⬝ᵥ z = 1 := by
 constructor
 · intro h
   obtain ⟨z, hz⟩ := ZfG v
   change ZcE v = 1 at h
   exact ⟨z, by simpa [h] using hz⟩
 · rintro ⟨z, hz⟩
   have hd : (ZcE v : ℤ) ∣ v ⬝ᵥ z := by
    rw [vec3_dotProduct]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left (ZgN v 0) _)
     (dvd_mul_of_dvd_left (ZgN v 1) _))
     (dvd_mul_of_dvd_left (ZgN v 2) _)
   rw [hz] at hd
   have hd' : ZcE v ∣ 1 := by exact_mod_cast hd
   exact Nat.dvd_one.mp hd'
lemma IsPrimitive.ne_zero {v : Vector} (h : IsPrimitive v) : v ≠ 0 := by
 intro hv
 have hg := (ZgM v).mpr hv
 unfold IsPrimitive at h
 omega
theorem ZcP (v : Vector) (hv : v ≠ 0) :
  ∃ g : ℤ, 0 < g ∧ ∃ w : Vector, IsPrimitive w ∧ v = g • w := by
 let g : ℤ := ZcE v
 have hg : 0 < g := by
  have : ZcE v ≠ 0 := by simpa [ZgM] using hv
  change (0 : ℤ) < (ZcE v : ℤ)
  exact_mod_cast Nat.pos_of_ne_zero this
 let w : Vector := fun i => v i / g
 have hscale : v = g • w := by
  ext i
  exact (Int.mul_ediv_cancel' (ZgN v i)).symm
 obtain ⟨z, hz⟩ := ZfG v
 have hw : w ⬝ᵥ z = 1 := by
  apply mul_left_cancel₀ (ne_of_gt hg)
  calc
   g * (w ⬝ᵥ z) = (g • w) ⬝ᵥ z := by rw [smul_dotProduct, smul_eq_mul]
   _ = v ⬝ᵥ z := by rw [← hscale]
   _ = g := hz
   _ = g * 1 := by ring
 exact ⟨g, hg, w, (ZB w).mpr ⟨z, hw⟩, hscale⟩
lemma Zio {v w : Vector} {g : ℤ}
  (hg : 0 < g) (hscale : v = g • w) (i : Fin 3) : |w i| ≤ |v i| := by
 have hg1 : 1 ≤ g := hg
 rw [hscale, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hg]
 nlinarith [abs_nonneg (w i)]
def Zct (A : Matrix (Fin 3) (Fin 3) ℤ) : Fin 3 → Vector :=
 ![A 1 ⨯₃ A 2, A 2 ⨯₃ A 0, A 0 ⨯₃ A 1]
lemma ZoB (A : Matrix (Fin 3) (Fin 3) ℤ) (i j : Fin 3) :
  (A *ᵥ Zct A i) j = if j = i then A.det else 0 := by
 fin_cases i <;> fin_cases j <;>
  simp [Zct, mulVec, vecHead, vecTail, cross_apply, det_fin_three] <;> ring
lemma Zke (A : Matrix (Fin 3) (Fin 3) ℤ)
   (h : (fun j => A j 0) ⨯₃ (fun j => A j 1) ≠ 0) :
   ∃ i : Fin 3, Zct A i ≠ 0 := by
 by_contra hn
 push Not at hn
 apply h
 ext i
 fin_cases i
 · simpa [Zct, cross_apply, mul_comm] using congrFun (hn 0) 2
 · simpa [Zct, cross_apply, mul_comm] using congrFun (hn 1) 2
 · simpa [Zct, cross_apply, mul_comm] using congrFun (hn 2) 2
lemma Zbg (u v : Vector) (h : u ⨯₃ v ≠ 0)
  (a b : ℤ) (hab : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
 have ha : a • (u ⨯₃ v) = 0 := by
  calc
   a • (u ⨯₃ v) = (a • u + b • v) ⨯₃ v := by
    ext i
    fin_cases i <;> simp [cross_apply, Pi.smul_apply] <;> ring
   _ = 0 := by rw [hab]; simp
 have hb : b • (u ⨯₃ v) = 0 := by
  calc
   b • (u ⨯₃ v) = u ⨯₃ (a • u + b • v) := by
    ext i
    fin_cases i <;> simp [cross_apply, Pi.smul_apply] <;> ring
   _ = 0 := by rw [hab]; simp
 exact ⟨(smul_eq_zero.mp ha).resolve_right h, (smul_eq_zero.mp hb).resolve_right h⟩
lemma ZiS (A : Matrix (Fin 3) (Fin 3) ℤ)
   (hpair : ∀ i j : Fin 3, i ≠ j → Aᵀ i ⨯₃ Aᵀ j ≠ 0)
   (w : Vector) (hw : w ≠ 0) (hk : A *ᵥ w = 0) :
   ∀ i : Fin 3, w i ≠ 0 := by
 have hrow (j : Fin 3) : A j 0 * w 0 + A j 1 * w 1 + A j 2 * w 2 = 0 := by
   simpa only [mulVec, vec3_dotProduct, Pi.zero_apply] using congrFun hk j
 intro i hi
 fin_cases i
 · change w 0 = 0 at hi
   have hrel : w 1 • Aᵀ 1 + w 2 • Aᵀ 2 = 0 := by
    ext j
    simpa [hi, mul_comm] using hrow j
   obtain ⟨h1, h2⟩ := Zbg _ _ (hpair 1 2 (by decide)) _ _ hrel
   apply hw
   ext j
   fin_cases j <;> simp [hi, h1, h2]
 · change w 1 = 0 at hi
   have hrel : w 0 • Aᵀ 0 + w 2 • Aᵀ 2 = 0 := by
    ext j
    simpa [hi, mul_comm] using hrow j
   obtain ⟨h0, h2⟩ := Zbg _ _ (hpair 0 2 (by decide)) _ _ hrel
   apply hw
   ext j
   fin_cases j <;> simp [hi, h0, h2]
 · change w 2 = 0 at hi
   have hrel : w 0 • Aᵀ 0 + w 1 • Aᵀ 1 = 0 := by
    ext j
    simpa [hi, mul_comm] using hrow j
   obtain ⟨h0, h1⟩ := Zbg _ _ (hpair 0 1 (by decide)) _ _ hrel
   apply hw
   ext j
   fin_cases j <;> simp [hi, h0, h1]
lemma ZqQ (a b c d X : ℤ) (hX : 0 ≤ X)
  (ha : |a| ≤ X) (hb : |b| ≤ X) (hc : |c| ≤ X) (hd : |d| ≤ X) :
  |a * b - c * d| ≤ 2 * X ^ 2 := by
 calc
  |a * b - c * d| ≤ |a * b| + |c * d| := by simpa using abs_sub_le (a * b) 0 (c * d)
  _ = |a| * |b| + |c| * |d| := by rw [abs_mul, abs_mul]
  _ ≤ X * X + X * X := add_le_add
   (mul_le_mul ha hb (abs_nonneg _) hX)
   (mul_le_mul hc hd (abs_nonneg _) hX)
  _ = 2 * X ^ 2 := by ring
lemma Zlh (u v : Vector) (X : ℤ) (hX : 0 ≤ X)
  (hu : ∀ i, |u i| ≤ X) (hv : ∀ i, |v i| ≤ X) (i : Fin 3) :
  |(u ⨯₃ v) i| ≤ 2 * X ^ 2 := by
 fin_cases i <;> simp only [cross_apply] <;>
  apply ZqQ _ _ _ _ X hX <;> first | apply hu | apply hv
theorem Zip (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hdet : A.det = 0)
  (hpair : ∀ i j : Fin 3, i ≠ j → Aᵀ i ⨯₃ Aᵀ j ≠ 0)
  (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ i j, |A i j| ≤ X) :
  ∃ w : Vector, IsPrimitive w ∧ A *ᵥ w = 0 ∧
   (∀ i, w i ≠ 0) ∧ (∀ i, |w i| ≤ 2 * X ^ 2) := by
 obtain ⟨i, hi⟩ := Zke A (hpair 0 1 (by decide))
 obtain ⟨g, hg, w, hw, hscale⟩ := ZcP (Zct A i) hi
 have hk : A *ᵥ w = 0 := by
  ext j
  have hj : A j ⬝ᵥ Zct A i = 0 := by
   simpa [hdet, mulVec] using ZoB A i j
  rw [hscale, dotProduct_smul, smul_eq_mul] at hj
  exact (mul_eq_zero.mp hj).resolve_left (ne_of_gt hg)
 refine ⟨w, hw, hk, ZiS A hpair w hw.ne_zero hk, ?_⟩
 intro j
 apply le_trans (Zio hg hscale j)
 fin_cases i <;> simp only [Zct] <;>
  apply Zlh _ _ X hX <;> apply hbound
lemma ZgO (u v : Vector)
   (hu : u 2 ≠ 0) (hv : v 2 ≠ 0)
   (hproj : ((u 0 : ℝ) / u 2, (u 1 : ℝ) / u 2) ≠
    ((v 0 : ℝ) / v 2, (v 1 : ℝ) / v 2)) : u ⨯₃ v ≠ 0 := by
 intro hc
 have h0 : u 1 * v 2 - u 2 * v 1 = 0 := by
   simpa [cross_apply] using congrFun hc 0
 have h1 : u 2 * v 0 - u 0 * v 2 = 0 := by
   simpa [cross_apply] using congrFun hc 1
 have huR : (u 2 : ℝ) ≠ 0 := by exact_mod_cast hu
 have hvR : (v 2 : ℝ) ≠ 0 := by exact_mod_cast hv
 apply hproj
 apply Prod.ext
 · apply (div_eq_div_iff huR hvR).mpr
   have h1R : (u 2 : ℝ) * v 0 - (u 0 : ℝ) * v 2 = 0 := by exact_mod_cast h1
   nlinarith
 · apply (div_eq_div_iff huR hvR).mpr
   have h0R : (u 1 : ℝ) * v 2 - (u 2 : ℝ) * v 1 = 0 := by exact_mod_cast h0
   nlinarith
theorem Zdr (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hdet : A.det = 0) (hheight : ∀ i, A 2 i ≠ 0)
  (hproj : ∀ i j : Fin 3, i ≠ j →
   ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
   ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
  (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ i j, |A i j| ≤ X) :
  ∃ w : Vector, IsPrimitive w ∧ A *ᵥ w = 0 ∧
   (∀ i, w i ≠ 0) ∧ (∀ i, |w i| ≤ 2 * X ^ 2) := by
 apply Zip A hdet _ X hX hbound
 intro i j hij
 exact ZgO _ _ (hheight i) (hheight j) (hproj i j hij)
def toEuclidean (v : Vector) : EuclideanSpace ℝ (Fin 3) :=
 WithLp.toLp 2 (fun i => (v i : ℝ))
lemma ZeF (v : Vector) (R : ℝ)
  (hR : 0 ≤ R) (h : ∀ i, |(v i : ℝ)| ≤ R) : ‖toEuclidean v‖ ≤ 3 * R := by
 rw [EuclideanSpace.norm_eq]
 apply Real.sqrt_le_iff.mpr
 refine ⟨by positivity, ?_⟩
 have h0 := sq_le_sq₀ (abs_nonneg (v 0 : ℝ)) hR |>.mpr (h 0)
 have h1 := sq_le_sq₀ (abs_nonneg (v 1 : ℝ)) hR |>.mpr (h 1)
 have h2 := sq_le_sq₀ (abs_nonneg (v 2 : ℝ)) hR |>.mpr (h 2)
 simp only [sq_abs] at h0 h1 h2
 simp [toEuclidean, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
 nlinarith [sq_nonneg R]
lemma Zli (v : Vector) (hv : v ≠ 0) : 1 ≤ ‖toEuclidean v‖ := by
 obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
  by_contra! h
  exact hv (funext h)
 have hi1 : (1 : ℤ) ≤ |v i| := abs_pos.mpr hi
 calc
  (1 : ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast hi1
  _ = ‖(toEuclidean v).ofLp i‖ := by simp [toEuclidean]
  _ ≤ ‖toEuclidean v‖ := PiLp.norm_apply_le _ _
end Problem355.Zo
end OAI
end
section
namespace OAI
namespace Problem355.Zii
open Matrix
open scoped Matrix
open Zo
lemma Zjp (g : ℤ) (w : Vector) :
  toEuclidean (g • w) = (g : ℝ) • toEuclidean w := by
 ext i
 simp [Zo.toEuclidean, Pi.smul_apply, smul_eq_mul]
theorem ZqD (u v : Vector) :
  ‖toEuclidean (u ⨯₃ v)‖ ≤ ‖toEuclidean u‖ * ‖toEuclidean v‖ := by
 let d : ℝ := ∑ i : Fin 3, (u i : ℝ) * (v i : ℝ)
 have hlagrange : ‖toEuclidean (u ⨯₃ v)‖ ^ 2 + d ^ 2 =
   ‖toEuclidean u‖ ^ 2 * ‖toEuclidean v‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  simp [Zo.toEuclidean, d, Fin.sum_univ_three, cross_apply]
  ring
 apply (sq_le_sq₀ (norm_nonneg _)
  (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
 calc
  ‖toEuclidean (u ⨯₃ v)‖ ^ 2 ≤
    ‖toEuclidean u‖ ^ 2 * ‖toEuclidean v‖ ^ 2 := by nlinarith [sq_nonneg d]
  _ = (‖toEuclidean u‖ * ‖toEuclidean v‖) ^ 2 := by ring
theorem ZdZ {v w : Vector} {g : ℤ}
  (hg : 0 < g) (hscale : v = g • w) : ‖toEuclidean w‖ ≤ ‖toEuclidean v‖ := by
 have hgR : (0 : ℝ) < g := by exact_mod_cast hg
 have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
 rw [hscale, Zjp, norm_smul, Real.norm_eq_abs, abs_of_pos hgR]
 nlinarith [norm_nonneg (toEuclidean w)]
theorem Zex {u v w : Vector} {g : ℤ}
  (hscale : u ⨯₃ v = g • w) (x : Vector) :
  Matrix.det ![x, u, v] = g * (x ⬝ᵥ w) := by
 rw [← triple_product_eq_det, hscale, dotProduct_smul, smul_eq_mul]
theorem Zep {u v w : Vector} {g : ℤ}
   (hg : g ≠ 0) (hscale : u ⨯₃ v = g • w) (x z : Vector) :
   Matrix.det ![x, u, v] = Matrix.det ![z, u, v] ↔ (x - z) ⬝ᵥ w = 0 := by
 rw [Zex hscale, Zex hscale,
   sub_dotProduct, sub_eq_zero]
 constructor
 · exact mul_left_cancel₀ hg
 · intro h
   rw [h]
theorem ZeG (u v : Vector) (huv : u ⨯₃ v ≠ 0) :
   ∃ g : ℤ, 0 < g ∧ ∃ w : Vector, IsPrimitive w ∧ u ⨯₃ v = g • w ∧
    u ⬝ᵥ w = 0 ∧ v ⬝ᵥ w = 0 ∧
    ‖toEuclidean w‖ ≤ ‖toEuclidean u‖ * ‖toEuclidean v‖ ∧
    (∀ x z : Vector, Matrix.det ![x, u, v] = Matrix.det ![z, u, v] ↔
     (x - z) ⬝ᵥ w = 0) := by
 obtain ⟨g, hg, w, hw, hscale⟩ := ZcP (u ⨯₃ v) huv
 have horth (x : Vector) (hx : x ⬝ᵥ u ⨯₃ v = 0) : x ⬝ᵥ w = 0 := by
   rw [hscale, dotProduct_smul, smul_eq_mul] at hx
   exact (mul_eq_zero.mp hx).resolve_left (ne_of_gt hg)
 refine ⟨g, hg, w, hw, hscale, horth u (dot_self_cross u v),
   horth v (dot_cross_self u v), ?_, ?_⟩
 · exact (ZdZ hg hscale).trans (ZqD u v)
 · exact Zep (ne_of_gt hg) hscale
end Problem355.Zii
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zs
open Finset
def box (d N : ℕ) : Finset (Fin d → ℤ) :=
 Fintype.piFinset (fun _ => Finset.Icc (-(N : ℤ)) N)
@[simp] theorem mem_box {d N : ℕ} {v : Fin d → ℤ} :
  v ∈ box d N ↔ ∀ i, |v i| ≤ (N : ℤ) := by
 simp [box, abs_le]
@[simp] theorem card_box (d N : ℕ) :
  (box d N).card = (2 * N + 1) ^ d := by
 simp [box, Int.card_Icc]
 congr 1
 omega
theorem Zlj {d N : ℕ} (S : Finset (Fin d → ℤ))
  (hS : ∀ v ∈ S, ∀ i, |v i| ≤ (N : ℤ)) :
  S.card ≤ (2 * N + 1) ^ d := by
 rw [← card_box]
 exact Finset.card_le_card (fun v hv => mem_box.mpr (hS v hv))
theorem Zpg {a : ℤ} {R : ℝ} (h : |(a : ℝ)| ≤ R) :
  |a| ≤ (⌊R⌋₊ : ℤ) := by
 have hcast : (a.natAbs : ℝ) = |(a : ℝ)| := by
  simpa only [Int.cast_natCast, Int.cast_abs] using
   congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs a)
 have hn : a.natAbs ≤ ⌊R⌋₊ := Nat.le_floor (hcast ▸ h)
 rw [← Int.natCast_natAbs]
 exact_mod_cast hn
theorem Ziq {d : ℕ} {R : ℝ} (hR : 0 ≤ R)
  (S : Finset (Fin d → ℤ))
  (hS : ∀ v ∈ S, ∀ i, |(v i : ℝ)| ≤ R) :
  (S.card : ℝ) ≤ (2 * R + 1) ^ d := by
 have hcount := Zlj S
  (fun v hv i => Zpg (hS v hv i))
 calc
  (S.card : ℝ) ≤ ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) ^ d := by exact_mod_cast hcount
  _ = (2 * (⌊R⌋₊ : ℝ) + 1) ^ d := by norm_cast
  _ ≤ (2 * R + 1) ^ d := by
   gcongr
   exact Nat.floor_le hR
theorem ZbU {R : ℝ} (hR : 1 ≤ R)
  (S : Finset (Fin 3 → ℤ))
  (hS : ∀ v ∈ S, ∀ i, |(v i : ℝ)| ≤ 2 * R) :
  (S.card : ℝ) ≤ 125 * R ^ 3 := by
 calc
  (S.card : ℝ) ≤ (2 * (2 * R) + 1) ^ 3 :=
   Ziq (by linarith) S hS
  _ ≤ (5 * R) ^ 3 := by gcongr; linarith
  _ = 125 * R ^ 3 := by ring
def Zw {d : ℕ} (v : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
 WithLp.toLp 2 (fun i => (v i : ℝ))
theorem Zfr {d : ℕ} (v : Fin d → ℤ) (i : Fin d) :
  |(v i : ℝ)| ≤ ‖Zw v‖ := by
 simpa [Zw, Real.norm_eq_abs] using PiLp.norm_apply_le (Zw v) i
theorem Zir {R : ℝ} (hR : 1 ≤ R)
  (S : Finset (Fin 3 → ℤ))
  (hS : ∀ v ∈ S, ‖Zw v‖ ≤ 2 * R) :
  (S.card : ℝ) ≤ 125 * R ^ 3 :=
 ZbU hR S
  (fun v hv i => (Zfr v i).trans (hS v hv))
end Problem355.Zs
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zs
open Finset
theorem Zdd {d : ℕ} {v : Fin d → ℤ} (hv : v ≠ 0) :
  1 ≤ ‖Zw v‖ := by
 obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
  by_contra h
  apply hv
  ext i
  simpa using not_exists.mp h i
 have ha : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
 have har : (1 : ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast ha
 exact har.trans (Zfr v i)
end Problem355.Zs
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Anisotropic
open Matrix
open scoped Matrix
open Zo
abbrev Zv := Fin 3 → ℤ
abbrev length (v : Zv) : ℝ := ‖Zs.Zw v‖
end Problem355.Anisotropic
end
end OAI
end
section
namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem355.Anisotropic
theorem Zde (S : Finset ℕ) {R : ℝ} (hR : 1 ≤ R)
  (hS : ∀ i ∈ S, (2 : ℝ) ^ i ≤ R) :
  (S.card : ℝ) ≤ Real.log (2 * R) / Real.log 2 := by
 have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
 have hquot : 0 ≤ Real.log R / Real.log 2 := div_nonneg hlogR hlog2.le
 have hi (i : ℕ) (hi : i ∈ S) : i ≤ ⌊Real.log R / Real.log 2⌋₊ := by
  apply Nat.le_floor
  apply (le_div_iff₀ hlog2).mpr
  calc
   (i : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ i) := (Real.log_pow 2 i).symm
   _ ≤ Real.log R := Real.log_le_log (by positivity) (hS i hi)
 have hs : S ⊆ Finset.range (⌊Real.log R / Real.log 2⌋₊ + 1) := by
  intro i hmem
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hi i hmem))
 have hc : (S.card : ℝ) ≤ (⌊Real.log R / Real.log 2⌋₊ : ℝ) + 1 := by
  exact_mod_cast (show S.card ≤ ⌊Real.log R / Real.log 2⌋₊ + 1 by
   simpa using Finset.card_le_card hs)
 calc
  (S.card : ℝ) ≤ (⌊Real.log R / Real.log 2⌋₊ : ℝ) + 1 := hc
  _ ≤ Real.log R / Real.log 2 + 1 := by
   linarith [Nat.floor_le hquot]
  _ = Real.log (2 * R) / Real.log 2 := by
   rw [Real.log_mul (by norm_num) (by linarith : R ≠ 0)]
   field_simp
   ring
theorem ZmK (S : Finset (ℕ × ℕ)) {R T : ℝ}
  (hR : 1 ≤ R) (hT : 1 ≤ T)
  (hS : ∀ p ∈ S, (2 : ℝ) ^ p.1 ≤ R ∧ (2 : ℝ) ^ p.2 ≤ T) :
  (S.card : ℝ) ≤
   (Real.log (2 * R) / Real.log 2) * (Real.log (2 * T) / Real.log 2) := by
 have hfst : ∀ i ∈ S.image Prod.fst, (2 : ℝ) ^ i ≤ R := by
  intro i hi
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
  exact (hS p hp).1
 have hsnd : ∀ i ∈ S.image Prod.snd, (2 : ℝ) ^ i ≤ T := by
  intro i hi
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
  exact (hS p hp).2
 have hsub : S ⊆ (S.image Prod.fst) ×ˢ (S.image Prod.snd) := by
  intro p hp
  exact Finset.mem_product.mpr
   ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
 have hc : (S.card : ℝ) ≤
   ((S.image Prod.fst).card : ℝ) * ((S.image Prod.snd).card : ℝ) := by
  exact_mod_cast (show S.card ≤ (S.image Prod.fst).card * (S.image Prod.snd).card by
   simpa using Finset.card_le_card hsub)
 exact hc.trans (mul_le_mul (Zde _ hR hfst)
  (Zde _ hT hsnd) (by positivity)
  ((Nat.cast_nonneg _).trans (Zde _ hR hfst)))
theorem ZkJ {α : Type*} [DecidableEq α]
  (S : Finset α) (index : α → ℕ × ℕ) (weight : α → ℝ)
  {R T A : ℝ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hA : 0 ≤ A)
  (hindex : ∀ x ∈ S, (2 : ℝ) ^ (index x).1 ≤ R ∧
   (2 : ℝ) ^ (index x).2 ≤ T)
  (hgroup : ∀ p ∈ S.image index,
   ∑ x ∈ S with index x = p, weight x ≤ A) :
  ∑ x ∈ S, weight x ≤
   A * (Real.log (2 * R) / Real.log 2) * (Real.log (2 * T) / Real.log 2) := by
 have hscales : ∀ p ∈ S.image index,
   (2 : ℝ) ^ p.1 ≤ R ∧ (2 : ℝ) ^ p.2 ≤ T := by
  intro p hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
  exact hindex x hx
 calc
  ∑ x ∈ S, weight x = ∑ p ∈ S.image index,
    ∑ x ∈ S with index x = p, weight x := by
   symm
   exact Finset.sum_fiberwise_of_maps_to
    (fun x hx => Finset.mem_image_of_mem index hx) weight
  _ ≤ ∑ _p ∈ S.image index, A := Finset.sum_le_sum hgroup
  _ = A * ((S.image index).card : ℝ) := by simp [mul_comm]
  _ ≤ A * ((Real.log (2 * R) / Real.log 2) *
    (Real.log (2 * T) / Real.log 2)) :=
   mul_le_mul_of_nonneg_left (ZmK _ hR hT hscales) hA
  _ = _ := by ring
theorem ZjA {U Y R₁ R₂ R₃ C : ℝ}
  (hU : 0 < U) (hY : 0 < Y) (hR : 0 ≤ R₃) (hUR : U ≤ R₃)
  (hC : 0 ≤ C) :
  C * U ^ 2 * Y ^ 2 * (R₁ ^ 2 / Y) *
    (R₂ ^ 2 / Y) * (R₃ / U) ≤ C * (R₁ * R₂ * R₃) ^ 2 := by
 have heq : C * U ^ 2 * Y ^ 2 * (R₁ ^ 2 / Y) *
   (R₂ ^ 2 / Y) * (R₃ / U) = C * R₁ ^ 2 * R₂ ^ 2 * R₃ * U := by
  field_simp
 rw [heq]
 have hmul := mul_le_mul_of_nonneg_left hUR
  (show 0 ≤ C * R₁ ^ 2 * R₂ ^ 2 * R₃ by positivity)
 nlinarith
theorem ZlX {R₁ R₂ R₃ : ℝ}
  (h₂ : 1 ≤ R₂) (h₃ : 1 ≤ R₃) (h₂₁ : R₂ ≤ R₁) (h₃₁ : R₃ ≤ R₁) :
  (Real.log (2 * R₃) / Real.log 2) *
   (Real.log (2 * (R₂ * R₃)) / Real.log 2) ≤
    2 * (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
 have h₁ : 1 ≤ R₁ := h₂.trans h₂₁
 have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have hL : 0 ≤ Real.log (2 * R₁) / Real.log 2 := by
  apply div_nonneg _ hlog2.le
  exact Real.log_nonneg (by linarith)
 have hleft : Real.log (2 * R₃) / Real.log 2 ≤
   Real.log (2 * R₁) / Real.log 2 := by
  apply div_le_div_of_nonneg_right _ hlog2.le
  exact Real.log_le_log (by linarith) (by linarith)
 have hmul : R₂ * R₃ ≤ R₁ * R₁ :=
  mul_le_mul h₂₁ h₃₁ (by linarith) (by linarith)
 have hright : Real.log (2 * (R₂ * R₃)) / Real.log 2 ≤
   2 * (Real.log (2 * R₁) / Real.log 2) := by
  have hp : 0 < 2 * (R₂ * R₃) := by positivity
  have hr : Real.log (2 * (R₂ * R₃)) ≤ 2 * Real.log (2 * R₁) := by
   calc
    Real.log (2 * (R₂ * R₃)) ≤ Real.log ((2 * R₁) ^ 2) :=
     Real.log_le_log hp (by nlinarith [sq_nonneg R₁])
    _ = _ := by rw [Real.log_pow]; norm_num
  have := div_le_div_of_nonneg_right hr hlog2.le
  simpa [mul_div_assoc] using this
 have hright0 : 0 ≤ Real.log (2 * (R₂ * R₃)) / Real.log 2 := by
  apply div_nonneg _ hlog2.le
  apply Real.log_nonneg
  nlinarith
 have hprod := mul_le_mul hleft hright hright0 hL
 nlinarith
theorem ZcF {α : Type*} [DecidableEq α]
   (S : Finset α) (u v weight : α → ℝ) {R T A : ℝ}
   (hR : 1 ≤ R) (hT : 1 ≤ T) (hA : 0 ≤ A)
   (hweight : ∀ x ∈ S, 0 ≤ weight x)
   (hvalue : ∀ x ∈ S, 1 ≤ u x ∧ u x ≤ R ∧ 1 ≤ v x ∧ v x ≤ T)
   (hshell : ∀ i j : ℕ,
     ∑ x ∈ S with ((2 : ℝ) ^ i ≤ u x ∧ u x < 2 ^ (i + 1) ∧
      (2 : ℝ) ^ j ≤ v x ∧ v x < 2 ^ (j + 1)), weight x ≤ A) :
   ∑ x ∈ S, weight x ≤
     A * (Real.log (2 * R) / Real.log 2) * (Real.log (2 * T) / Real.log 2) := by
 classical
 have hex : ∀ x : α, ∃ p : ℕ × ℕ, x ∈ S →
     (2 : ℝ) ^ p.1 ≤ u x ∧ u x < 2 ^ (p.1 + 1) ∧
     (2 : ℝ) ^ p.2 ≤ v x ∧ v x < 2 ^ (p.2 + 1) := by
   intro x
   by_cases hx : x ∈ S
   · obtain ⟨i, hi, hi'⟩ := exists_nat_pow_near (hvalue x hx).1 (by norm_num : (1 : ℝ) < 2)
     obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near (hvalue x hx).2.2.1 (by norm_num : (1 : ℝ) < 2)
     exact ⟨(i,j), fun _ => ⟨hi, hi', hj, hj'⟩⟩
   · exact ⟨(0,0), fun h => (hx h).elim⟩
 choose index hindex using hex
 apply ZkJ S index weight hR hT hA
 · intro x hx
   exact ⟨(hindex x hx).1.trans (hvalue x hx).2.1,
     (hindex x hx).2.2.1.trans (hvalue x hx).2.2.2⟩
 · intro p hp
   have hsub : (S.filter fun x => index x = p) ⊆
      (S.filter fun x => (2 : ℝ) ^ p.1 ≤ u x ∧ u x < 2 ^ (p.1 + 1) ∧
       (2 : ℝ) ^ p.2 ≤ v x ∧ v x < 2 ^ (p.2 + 1)) := by
     intro x hx
     obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
     apply Finset.mem_filter.mpr
     refine ⟨hxS, ?_⟩
     simpa [hxp] using hindex x hxS
   exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
     (fun x hx _ => hweight x (Finset.mem_filter.mp hx).1)).trans (hshell p.1 p.2)
theorem Zea {α : Type*} [DecidableEq α]
  (S : Finset α) (u weight : α → ℝ) {R A : ℝ}
  (hR : 1 ≤ R) (hA : 0 ≤ A)
  (hweight : ∀ x ∈ S, 0 ≤ weight x)
  (hvalue : ∀ x ∈ S, 1 ≤ u x ∧ u x ≤ R)
  (hshell : ∀ i : ℕ,
    ∑ x ∈ S with ((2 : ℝ) ^ i ≤ u x ∧ u x < 2 ^ (i + 1)), weight x ≤ A) :
  ∑ x ∈ S, weight x ≤ A * (Real.log (2 * R) / Real.log 2) := by
 have h := ZcF S u (fun _ => 1) weight
  hR (by norm_num : (1 : ℝ) ≤ 1) hA hweight
  (fun x hx => ⟨(hvalue x hx).1, (hvalue x hx).2, le_rfl, le_rfl⟩)
 have hs : ∀ i j : ℕ,
    ∑ x ∈ S with ((2 : ℝ) ^ i ≤ u x ∧ u x < 2 ^ (i + 1) ∧
     (2 : ℝ) ^ j ≤ 1 ∧ (1 : ℝ) < 2 ^ (j + 1)), weight x ≤ A := by
  intro i j
  apply le_trans _ (hshell i)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨hxS, hx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxS, hx.1, hx.2.1⟩
  · intro x hx _
    exact hweight x (Finset.mem_filter.mp hx).1
 simpa [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))] using h hs
end Problem355.Anisotropic
end
end OAI
end
section
namespace OAI
namespace Problem355.ZdW
theorem ZeN {α β : Type*} [DecidableEq β]
  (S : Finset α) (Y : Finset β) (f : α → β) (bound : β → ℝ)
  (hf : ∀ x ∈ S, f x ∈ Y)
  (hbound : ∀ y ∈ Y, ((S.filter (fun x => f x = y)).card : ℝ) ≤ bound y) :
  (S.card : ℝ) ≤ ∑ y ∈ Y, bound y := by
 classical
 have hcard := Finset.card_eq_sum_card_fiberwise hf
 calc
  (S.card : ℝ) = ∑ y ∈ Y, ((S.filter (fun x => f x = y)).card : ℝ) := by
   exact_mod_cast hcard
  _ ≤ _ := Finset.sum_le_sum hbound
theorem Zds {α β : Type*} [DecidableEq β]
  (S : Finset α) (Y : Finset β) (f : α → β) (bound : ℝ)
  (hf : ∀ x ∈ S, f x ∈ Y)
  (hbound : ∀ y ∈ Y, ((S.filter (fun x => f x = y)).card : ℝ) ≤ bound) :
  (S.card : ℝ) ≤ (Y.card : ℝ) * bound := by
 simpa using ZeN S Y f (fun _ => bound) hf hbound
theorem ZnB {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
  (S : Finset (α × β × γ)) (Y : Finset β) (Z : Finset γ)
  (B₁ B₂ B₃ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
  (hY : (Y.card : ℝ) ≤ B₂) (hZ : (Z.card : ℝ) ≤ B₃)
  (hproj : ∀ x ∈ S, x.2.1 ∈ Y ∧ x.2.2 ∈ Z)
  (hfirst : ∀ y ∈ Y, ∀ z ∈ Z,
   ((S.filter (fun x => x.2 = (y, z))).card : ℝ) ≤ B₁) :
  (S.card : ℝ) ≤ B₁ * B₂ * B₃ := by
 have hcount := Zds S (Y.product Z)
  (fun x => x.2) B₁ (fun x hx => Finset.mem_product.mpr (hproj x hx))
  (fun yz hyz => hfirst yz.1 (Finset.mem_product.mp hyz).1
   yz.2 (Finset.mem_product.mp hyz).2)
 have hprod : ((Y.product Z).card : ℝ) = (Y.card : ℝ) * (Z.card : ℝ) := by
  exact_mod_cast Finset.card_product Y Z
 have hcount' : (S.card : ℝ) ≤ (Y.card : ℝ) * (Z.card : ℝ) * B₁ := by
  rwa [hprod] at hcount
 calc
  (S.card : ℝ) ≤ (Y.card : ℝ) * (Z.card : ℝ) * B₁ := hcount'
  _ ≤ B₂ * B₃ * B₁ := by
   apply mul_le_mul_of_nonneg_right _ hB₁
   exact mul_le_mul hY hZ (Nat.cast_nonneg _) hB₂
  _ = B₁ * B₂ * B₃ := by ring
end Problem355.ZdW
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Ze
open Module Matrix
abbrev ZI := EuclideanSpace ℝ (Fin 3)
def stdBasis : Basis (Fin 3) ℝ ZI := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
def ZE : Submodule ℤ ZI := Submodule.span ℤ (Set.range stdBasis)
instance : DiscreteTopology ZE := by
 unfold ZE
 infer_instance
def Zp (x : Fin 3 → ℤ) : ZI := WithLp.toLp 2 (fun i => (x i : ℝ))
@[simp] lemma Znd (x : Fin 3 → ℤ) (i : Fin 3) : Zp x i = (x i : ℝ) := rfl
lemma ZqE (v : ZI) (i : Fin 3) : stdBasis.repr v i = v i := rfl
lemma Zeq (v : ZI) :
  v ∈ ZE ↔ ∀ i, ∃ z : ℤ, (z : ℝ) = v i := by
 change v ∈ Submodule.span ℤ (Set.range stdBasis) ↔ _
 rw [stdBasis.mem_span_iff_repr_mem ℤ v]
 simp [ZqE]
lemma Zig (x : Fin 3 → ℤ) : Zp x ∈ ZE :=
 (Zeq _).mpr (fun i => ⟨x i, rfl⟩)
def Zbm (x : Fin 3 → ℤ) : ZI →ₗ[ℝ] ℝ where
 toFun v := ∑ i, (x i : ℝ) * v i
 map_add' v w := by simp [Finset.sum_add_distrib, mul_add]
 map_smul' t v := by simp [Finset.mul_sum, mul_left_comm]
@[simp] lemma ZrZ (x : Fin 3 → ℤ) (v : ZI) :
 Zbm x v = ∑ i, (x i : ℝ) * v i := rfl
@[simp] lemma Zcf (x z : Fin 3 → ℤ) :
  Zbm x (Zp z) = (x ⬝ᵥ z : ℤ) := by
 simp [Zbm, Zp, dotProduct]
def ZQ (x : Fin 3 → ℤ) : Submodule ℝ ZI := (Zbm x).ker
def lattice (x : Fin 3 → ℤ) : Submodule ℤ (ZQ x) :=
 ZE.comap ((ZQ x).subtype.restrictScalars ℤ)
instance ZrM (x : Fin 3 → ℤ) : DiscreteTopology (lattice x) := by
 let : DiscreteTopology (ZE : Set ZI) :=
  inferInstanceAs (DiscreteTopology ZE)
 exact DiscreteTopology.preimage_of_continuous_injective (ZE : Set ZI)
  (LinearMap.continuous_of_finiteDimensional (ZQ x).subtype) (Submodule.injective_subtype _)
lemma Zph (x : Fin 3 → ℤ) (i : Fin 3) : Zbm x (stdBasis i) = (x i : ℝ) := by
 simp [Zbm, stdBasis, EuclideanSpace.basisFun_apply]
def projection (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) : ZI →ₗ[ℝ] ZQ x :=
 (LinearMap.id - (Zbm x).smulRight (Zp z)).codRestrict (ZQ x) (by
  intro v
  change Zbm x (v - Zbm x v • Zp z) = 0
  rw [map_sub, map_smul, Zcf, hz]
  simp)
lemma ZnC (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) (v : ZQ x) :
  projection x z hz v = v := by
 apply Subtype.ext
 change (v : ZI) - Zbm x v • Zp z = v
 have hv : Zbm x v = 0 := v.property
 simp [hv]
lemma ZmL (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) (i : Fin 3) :
   projection x z hz (stdBasis i) ∈ lattice x := by
 change stdBasis i - Zbm x (stdBasis i) • Zp z ∈ ZE
 rw [Zph]
 apply ZE.sub_mem
 · exact Submodule.subset_span ⟨i, rfl⟩
 · rw [Int.cast_smul_eq_zsmul ℝ]
   exact ZE.smul_mem _ (Zig z)
lemma Zne (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) :
  Submodule.span ℝ (lattice x : Set (ZQ x)) = ⊤ := by
 apply top_unique
 intro v hv
 rw [← ZnC x z hz v, ← stdBasis.sum_repr (v : ZI), map_sum]
 apply Submodule.sum_mem
 intro i hi
 rw [map_smul]
 exact Submodule.smul_mem _ _ (Submodule.subset_span (ZmL x z hz i))
lemma Zrm (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) : IsZLattice ℝ (lattice x) :=
 ⟨Zne x z hz⟩
lemma Zeb (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) :
  finrank ℝ (ZQ x) = 2 := by
 have hn : Zbm x ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun h (Zp z)
  change Zbm x (Zp z) = 0 at he
  rw [Zcf, hz] at he
  norm_num at he
 have h := Module.Dual.finrank_ker_add_one_of_ne_zero hn
 change finrank ℝ (ZQ x) + 1 = finrank ℝ ZI at h
 norm_num [ZI] at h
 omega
def ZjB (x : Fin 3 → ℤ) : (Fin 3 → ℤ) →ₗ[ℤ] ℤ where
 toFun v := x ⬝ᵥ v
 map_add' v w := by simp [dotProduct, mul_add, Finset.sum_add_distrib]
 map_smul' t v := by simp [dotProduct, Finset.mul_sum, mul_left_comm]
def ZnY (x : Fin 3 → ℤ) : Submodule ℤ (Fin 3 → ℤ) := (ZjB x).ker
def ZjC : (Fin 3 → ℤ) →ₗ[ℤ] ZI where
 toFun := Zp
 map_add' v w := by ext i; simp [Zp]
 map_smul' t v := by ext i; simp [Zp]
lemma ZgP : Function.Injective ZjC := by
 intro v w h
 funext i
 have hi := congrArg (fun u : ZI => u i) h
 change (v i : ℝ) = (w i : ℝ) at hi
 exact_mod_cast hi
def Zaw (L : Submodule ℤ (Fin 3 → ℤ)) : Submodule ℤ ZI := L.map ZjC
lemma ZbM (L : Submodule ℤ (Fin 3 → ℤ)) :
  Zaw L ≤ ZE := by
 rintro y ⟨v, hv, rfl⟩
 exact Zig v
lemma ZgQ : Zaw ⊤ = ZE := by
 apply le_antisymm (ZbM _)
 intro v hv
 choose z hz using (Zeq v).mp hv
 refine ⟨z, trivial, ?_⟩
 ext i
 exact hz i
instance Zrn (L : Submodule ℤ (Fin 3 → ℤ)) :
  DiscreteTopology (Zaw L) := by
 exact DiscreteTopology.of_subset (inferInstanceAs (DiscreteTopology ZE))
  (ZbM L)
def ZG (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
 Submodule ℤ (ZQ x) := (Zaw L).comap ((ZQ x).subtype.restrictScalars ℤ)
instance Zrz (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
  DiscreteTopology (ZG x L) := by
 let : DiscreteTopology (Zaw L : Set ZI) :=
  inferInstanceAs (DiscreteTopology (Zaw L))
 exact DiscreteTopology.preimage_of_continuous_injective (Zaw L : Set ZI)
  (LinearMap.continuous_of_finiteDimensional (ZQ x).subtype) (Submodule.injective_subtype _)
lemma ZpJ (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
  (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
  (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
  Submodule.span ℝ (ZG x L : Set (ZQ x)) = ⊤ := by
 apply top_unique
 rw [← Zne x z hz]
 apply Submodule.span_le.mpr
 intro v hv
 change (v : ZI) ∈ ZE at hv
 rw [← ZgQ] at hv
 obtain ⟨u, _, hu⟩ := hv
 have hm : E • v ∈ ZG x L := by
  exact ⟨E • u, hL _, by rw [map_smul, hu]; rfl⟩
 have hs : (E : ℝ) • v ∈ Submodule.span ℝ (ZG x L : Set (ZQ x)) := by
  rw [Int.cast_smul_eq_zsmul ℝ]
  exact Submodule.subset_span hm
 exact (Submodule.smul_mem_iff _ (by exact_mod_cast hE : (E : ℝ) ≠ 0)).mp hs
lemma ZbC (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
  (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
  (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) : IsZLattice ℝ (ZG x L) :=
 ⟨ZpJ x z hz L E hE hL⟩
lemma ZoD (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
  (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
  (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) : finrank ℤ (ZG x L) = 2 := by
 let := ZbC x z hz L E hE hL
 rw [ZLattice.rank ℝ (ZG x L), Zeb x z hz]
def ZrV (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
  (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
  (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) : Basis (Fin 2) ℤ (ZG x L) := by
 letI := ZbC x z hz L E hE hL
 exact (Module.finBasis ℤ (ZG x L)).reindex
  (finCongr (ZoD x z hz L E hE hL))
def Zaq (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
 Submodule ℤ (Fin 3 → ℤ) := L ⊓ ZnY x
def Zlk (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
  Zaq x L →ₗ[ℤ] ZG x L where
 toFun v := ⟨⟨Zp v, by
  change Zbm x (Zp v) = 0
  rw [Zcf]
  have hv : x ⬝ᵥ (v : Fin 3 → ℤ) = 0 := v.property.2
  exact_mod_cast hv⟩, ⟨v.val, v.property.1, rfl⟩⟩
 map_add' v w := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  simp [Zp]
 map_smul' t v := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  simp [Zp]
lemma ZlY (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
  Function.Injective (Zlk x L) := by
 intro u v h
 apply Subtype.ext
 funext i
 have he := congrArg (fun w : ZG x L => ((w : ZQ x) : ZI) i) h
 change (u.val i : ℝ) = (v.val i : ℝ) at he
 exact_mod_cast he
lemma Zll (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
  Function.Surjective (Zlk x L) := by
 intro y
 obtain ⟨v, hv, he⟩ := y.property
 have hvker : v ∈ ZnY x := by
  have hyker : Zbm x ((y : ZQ x) : ZI) = 0 := (y : ZQ x).property
  change Zp v = ((y : ZQ x) : ZI) at he
  rw [← he, Zcf] at hyker
  change x ⬝ᵥ v = 0
  exact_mod_cast hyker
 refine ⟨⟨v, hv, hvker⟩, ?_⟩
 apply Subtype.ext
 apply Subtype.ext
 exact he
def Zbq (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
  Zaq x L ≃ₗ[ℤ] ZG x L :=
 LinearEquiv.ofBijective (Zlk x L)
  ⟨ZlY x L, Zll x L⟩
def Zqn (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
  (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
  (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
  Basis (Fin 2) ℤ (Zaq x L) :=
 (ZrV x z hz L E hE hL).map (Zbq x L).symm
end Problem355.Ze
end
end OAI
end
section
namespace OAI
open MeasureTheory MeasureTheory.Measure Set
open scoped Pointwise ENNReal
namespace Problem355.Zfj
open Module
set_option maxHeartbeats 2000000 in
theorem Zbh {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (hdim : finrank ℝ E = 2)
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (v : Fin 2 → E) (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ L)
  (A : Finset L) (R : ℝ) (hR : 0 ≤ R)
  (hA : ∀ a ∈ A, ‖(a : E)‖ ≤ R) (hvn : ∀ i, ‖v i‖ ≤ R) :
  (A.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume L := by
 classical
 let o := (stdOrthonormalBasis ℝ E).reindex (finCongr hdim)
 let S := A.image ((↑) : L → E) ∪ Finset.univ.image v
 have hS (x) (hx : x ∈ S) : x ∈ L ∧ ‖x‖ ≤ R := by
  rcases Finset.mem_union.mp hx with h | h <;> obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
  · exact ⟨a.property,hA a ha⟩
  · exact ⟨hvL a,hvn a⟩
 let T := Fintype.piFinset (fun _ : Fin 2 => S)
 have hvT : v ∈ T := Fintype.mem_piFinset.mpr fun i => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
 obtain ⟨w,hw,hm⟩ := Finset.exists_max_image T (fun (t : Fin 2 → E) => |o.toBasis.det t|) ⟨v,hvT⟩
 have hp : 0 < |o.toBasis.det w| := by
  apply lt_of_lt_of_le _ (hm v hvT)
  let bv := basisOfLinearIndependentOfCardEqFinrank hv (by simpa using hdim.symm)
  simpa only [bv,coe_basisOfLinearIndependentOfCardEqFinrank] using abs_pos.mpr (o.toBasis.isUnit_det bv).ne_zero
 obtain ⟨hli,hspan⟩ := (o.toBasis.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr (abs_pos.mp hp))
 let b := Basis.mk hli hspan.ge
 have hc (x) (hx : x ∈ S) (i) : |b.repr x i| ≤ 1 := by
  have hu : Function.update w i x ∈ T := Fintype.mem_piFinset.mpr (by
    intro j; by_cases h : j = i
    · simpa [h] using hx
    · simpa [Function.update_of_ne h] using Fintype.mem_piFinset.mp hw j)
  have he := LinearMap.congr_fun (o.toBasis.det_smul_mk_coord_eq_det_update hli hspan.ge i) x
  change o.toBasis.det w * b.repr x i = o.toBasis.det (Function.update w i x) at he
  have h := hm _ hu
  rw [← he, abs_mul] at h
  exact (mul_le_mul_iff_right₀ hp).mp (by simpa using h)
 let u := Units.mk0 (3 : ℝ) (by norm_num)
 let d := b.unitsSMul (fun _ => u)
 let H := Submodule.span ℤ (range d)
 have hd (i) : d i = (3 : ℝ) • w i := by simp [d, Basis.unitsSMul_apply, u, Units.smul_def, b]
 have hHL : H ≤ L := Submodule.span_le.mpr (by
  rintro _ ⟨i,rfl⟩; rw [hd, show (3:ℝ) = ((3:ℤ):ℝ) by norm_num, Int.cast_smul_eq_zsmul]
  exact L.smul_mem _ (hS _ (Fintype.mem_piFinset.mp hw i)).1)
 have hr := ZLattice.covolume_div_covolume_eq_relIndex' H L hHL
 let Q := L ⧸ H.toAddSubgroup.addSubgroupOf L.toAddSubgroup
 let : Finite Q := AddSubgroup.index_ne_zero_iff_finite.mp (by
  intro hz; change H.toAddSubgroup.relIndex L.toAddSubgroup = 0 at hz; rw [hz,Nat.cast_zero] at hr
  exact (div_pos (ZLattice.covolume_pos H volume) (ZLattice.covolume_pos L volume)).ne' hr)
 let f : A → Q := fun a => QuotientAddGroup.mk a.val
 have hf : Function.Injective f := by
  intro a e he
  have hh : (a.val : E) - e.val ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp he
  apply Subtype.ext; apply Subtype.ext; apply b.ext_elem; intro i
  obtain ⟨z,hz⟩ := (d.mem_span_iff_repr_mem ℤ _).mp hh i
  have h1 := abs_le.mp (hc _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ a.property)) i)
  have h2 := abs_le.mp (hc _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ e.property)) i)
  simp [d,Basis.repr_unitsSMul,Units.smul_def,u] at hz
  have : z = 0 := by
    rcases lt_trichotomy z 0 with h|h|h
    · have : (z:ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
      linarith
    · exact h
    · have : (1:ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by omega)
      linarith
  subst z; norm_num at hz; linarith
 have hcard : (A.card : ℝ) ≤ ZLattice.covolume H / ZLattice.covolume L := by
  rw [hr]; exact_mod_cast (show A.card ≤ Nat.card Q by simpa using Nat.card_le_card_of_injective f hf)
 have hvold : ZLattice.covolume H = |o.toBasis.det d| := by
  rw [ZLattice.covolume_eq_det_mul_measureReal H volume (d.restrictScalars ℤ) o.toBasis,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
  simp [Measure.real, o.volume_parallelepiped, Function.comp_def]
  exact congrArg (fun t => |o.toBasis.det t|) (funext (d.restrictScalars_apply ℤ))
 let : Fact (finrank ℝ E = 2) := ⟨hdim⟩
 have hdet := o.toBasis.orientation.abs_volumeForm_apply_le d
 rw [o.toBasis.orientation.volumeForm_robust' o] at hdet
 have hn (i) : ‖d i‖ ≤ 3 * R := by
  rw [hd, norm_smul]; norm_num; linarith [(hS _ (Fintype.mem_piFinset.mp hw i)).2]
 apply hcard.trans; apply div_le_div_of_nonneg_right _ (ZLattice.covolume_pos L volume).le
 rw [hvold]; apply hdet.trans
 rw [Fin.prod_univ_two]; nlinarith [mul_le_mul (hn 0) (hn 1) (norm_nonneg _) (by positivity : 0 ≤ 3*R), mul_nonneg (sq_nonneg R) (show 0 ≤ Real.pi-1 by linarith [Real.pi_gt_three])]
theorem ZnZ {α : Type*} [DecidableEq α] {m : ℕ}
  (A : Finset (Fin m → α)) (C : ℝ)
  (hA : ∀ i, ((A.image (fun a => a i)).card : ℝ) ≤ C) :
  (A.card : ℝ) ≤ C ^ m := by
 classical
 let B : Fin m → Finset α := fun i => A.image (fun a => a i)
 have hsub : A ⊆ Fintype.piFinset B := by
  intro a ha
  exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
 have hcard : A.card ≤ ∏ i, (B i).card := by
  simpa only [Fintype.card_piFinset] using Finset.card_le_card hsub
 exact calc
  (A.card : ℝ) ≤ ∏ i, ((B i).card : ℝ) := by
   simpa only [Nat.cast_prod] using (Nat.cast_le (α := ℝ)).mpr hcard
  _ ≤ ∏ _i : Fin m, C :=
   Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hA i)
  _ = C ^ m := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
theorem ZcU {E : Type*}
   [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
   [MeasurableSpace E] [BorelSpace E] (hdim : Module.finrank ℝ E = 2)
   (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
   (A : Finset (Fin 3 → L)) (R : ℝ) (hR : 0 ≤ R)
   (hA : ∀ a ∈ A, ∀ i, ‖(a i : E)‖ ≤ R)
   (hpair : ∀ a ∈ A, ∃ i j : Fin 3,
    LinearIndependent ℝ ![(a i : E), (a j : E)]) :
   (A.card : ℝ) ≤ (9 * Real.pi * R ^ 2 / ZLattice.covolume L) ^ 3 := by
 classical
 by_cases hne : A.Nonempty
 · obtain ⟨a, ha⟩ := hne
   obtain ⟨i, j, hij⟩ := hpair a ha
   let v : Fin 2 → E := ![(a i : E), (a j : E)]
   have hvL : ∀ k, v k ∈ L := by
    intro k
    fin_cases k <;> exact Subtype.coe_prop _
   have hvn : ∀ k, ‖v k‖ ≤ R := by
    intro k
    fin_cases k
    · exact hA a ha i
    · exact hA a ha j
   let B : Fin 3 → Finset L := fun k => A.image (fun t => t k)
   have hB (k : Fin 3) : ((B k).card : ℝ) ≤
      9 * Real.pi * R ^ 2 / ZLattice.covolume L := by
    apply Zbh hdim L v hij hvL (B k) R hR _ hvn
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hA t ht k
   exact ZnZ A _ hB
 · have hzero : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
   subst A
   simp only [Finset.card_empty, Nat.cast_zero]
   exact pow_nonneg (div_nonneg (by positivity) (ZLattice.covolume_pos L volume).le) 3
theorem Zro {P E : Type*}
   [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
   [MeasurableSpace P] [BorelSpace P]
   [NormedAddCommGroup E] [NormedSpace ℝ E]
   (e : P →ₗᵢ[ℝ] E) (hdim : Module.finrank ℝ P = 2)
   (L : Submodule ℤ P) [DiscreteTopology L] [IsZLattice ℝ L]
   (v : Fin 2 → P) (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ L)
   (A : Finset E) (R : ℝ) (hR : 0 ≤ R)
   (hA : ∀ a ∈ A, ‖a‖ ≤ R) (hvn : ∀ i, ‖v i‖ ≤ R)
   (hdiff : ∀ a ∈ A, ∀ b ∈ A, ∃ u : L, e (u : P) = a - b) :
   (A.card : ℝ) ≤ 36 * Real.pi * R ^ 2 / ZLattice.covolume L := by
 classical
 rcases A.eq_empty_or_nonempty with hzero | ⟨a0, ha0⟩
 · subst A
   simp only [Finset.card_empty, Nat.cast_zero]
   exact div_nonneg (by positivity) (ZLattice.covolume_pos L volume).le
 choose u hu using fun a : {a // a ∈ A} => hdiff a.1 a.2 a0 ha0
 have hinj : Function.Injective u := by
   intro a b hab
   have h := congrArg (fun w : L => e (w : P)) hab
   rw [hu a, hu b] at h
   exact Subtype.ext (sub_left_inj.mp h)
 let B : Finset L := A.attach.image u
 have hcard : B.card = A.card :=
   (Finset.card_image_of_injective _ hinj).trans Finset.card_attach
 have hB : ∀ b ∈ B, (b : P) ∈ Metric.closedBall 0 (2 * R) := by
   intro b hb
   obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
   rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, ← e.norm_map (u a : P), hu a]
   exact (norm_sub_le _ _).trans (by linarith [hA a.1 a.2, hA a0 ha0])
 have hvn' : ∀ i, ‖v i‖ ≤ 2 * R := fun i => (hvn i).trans (by linarith)
 have hbound := Zbh hdim L v hv hvL B (2 * R)
   (by positivity) (by simpa only [Metric.mem_closedBall, dist_zero_right] using hB) hvn'
 exact calc
   (A.card : ℝ) = (B.card : ℝ) := by rw [hcard]
   _ ≤ 9 * Real.pi * (2 * R) ^ 2 / ZLattice.covolume L := hbound
   _ = 36 * Real.pi * R ^ 2 / ZLattice.covolume L := by ring
end Problem355.Zfj
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Znl
theorem ZiT {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (v : E) (hv : v ≠ 0) (R : ℝ) (hR : 0 ≤ R) (S : Finset E)
  (hline : ∀ p ∈ S, ∃ z : ℤ, p = (z : ℝ) • v)
  (hball : ∀ p ∈ S, ‖p‖ ≤ R) :
  (S.card : ℝ) ≤ 1 + 2 * R / ‖v‖ := by
 classical
 have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
 let T : ℝ := R / ‖v‖
 let Q : Finset ℤ := Finset.Icc (-⌊T⌋) ⌊T⌋
 have hT : 0 ≤ T := div_nonneg hR hvnorm.le
 have hf : (0 : ℤ) ≤ ⌊T⌋ := Int.le_floor.mpr (by simpa using hT)
 have hsubset : S ⊆ Q.image (fun z : ℤ => (z : ℝ) • v) := by
  intro p hp
  obtain ⟨z, hz⟩ := hline p hp
  have hzabs : |(z : ℝ)| ≤ T := by
   apply (le_div_iff₀ hvnorm).mpr
   simpa only [hz, norm_smul, Real.norm_eq_abs] using hball p hp
  have hzu : z ≤ ⌊T⌋ := Int.le_floor.mpr ((le_abs_self _).trans hzabs)
  have hzl : -z ≤ ⌊T⌋ := Int.le_floor.mpr (by
   simpa only [Int.cast_neg] using (neg_le_abs (z : ℝ)).trans hzabs)
  apply Finset.mem_image.mpr
  refine ⟨z, ?_, hz.symm⟩
  change z ∈ Finset.Icc (-⌊T⌋) ⌊T⌋
  simp only [Finset.mem_Icc]
  omega
 have hcard : S.card ≤ Q.card :=
  (Finset.card_le_card hsubset).trans Finset.card_image_le
 have hnat : 0 ≤ ⌊T⌋ + 1 - (-⌊T⌋) := by omega
 calc
  (S.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hcard
  _ = 2 * (⌊T⌋ : ℝ) + 1 := by
   dsimp [Q]
   rw [Int.card_Icc]
   have heq := Int.toNat_of_nonneg hnat
   have heqR : (((⌊T⌋ + 1 - (-⌊T⌋)).toNat : ℕ) : ℝ) =
    ((⌊T⌋ + 1 - (-⌊T⌋) : ℤ) : ℝ) := by exact_mod_cast heq
   rw [heqR]
   push_cast
   ring
  _ ≤ 1 + 2 * T := by linarith [Int.floor_le T]
  _ = 1 + 2 * R / ‖v‖ := by dsimp [T]; ring
theorem Zqo {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : AddSubgroup E) {v w : E} (hv : v ≠ 0) (hvL : v ∈ L)
  (hshort : ∀ u ∈ L, u ≠ 0 → ‖v‖ ≤ ‖u‖)
  (hwL : w ∈ L) (hline : ∃ r : ℝ, w = r • v) :
  ∃ z : ℤ, w = (z : ℝ) • v := by
 obtain ⟨r, hr⟩ := hline
 let u : E := (r - (⌊r⌋ : ℝ)) • v
 have humem : u ∈ L := by
  change (r - (⌊r⌋ : ℝ)) • v ∈ L
  rw [sub_smul, ← hr, Int.cast_smul_eq_zsmul]
  exact L.sub_mem hwL (L.zsmul_mem hvL _)
 have hnonneg : 0 ≤ r - (⌊r⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le r)
 have hlt : r - (⌊r⌋ : ℝ) < 1 := by linarith [Int.lt_floor_add_one r]
 have hunorm : ‖u‖ < ‖v‖ := by
  change ‖(r - (⌊r⌋ : ℝ)) • v‖ < ‖v‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  nlinarith [norm_pos_iff.mpr hv]
 have hu : u = 0 := by
  by_contra hne
  exact (not_lt_of_ge (hshort u humem hne)) hunorm
 refine ⟨⌊r⌋, sub_eq_zero.mp ?_⟩
 calc
  w - (⌊r⌋ : ℝ) • v = u := by rw [hr, ← sub_smul]
  _ = 0 := hu
end Problem355.Znl
end
end OAI
end
section
namespace OAI
namespace Problem355.ZbJ
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
theorem Zhu (L : Submodule ℤ E) [DiscreteTopology L]
   (P : E → Prop) (hP : ∃ v ∈ L, P v) :
   ∃ v ∈ L, P v ∧ ∀ w ∈ L, P w → ‖v‖ ≤ ‖w‖ := by
 classical
 obtain ⟨x, hxL, hxP⟩ := hP
 have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
 have hf : (Metric.closedBall (0 : E) ‖x‖ ∩ (L : Set E)).Finite :=
   Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    Metric.isBounded_closedBall (AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup))
 let S : Set E := {v | v ∈ L ∧ P v ∧ ‖v‖ ≤ ‖x‖}
 have hSfin : S.Finite := hf.subset (by
   intro v hv
   exact ⟨by simpa using hv.2.2, hv.1⟩)
 obtain ⟨v, hv, hmin⟩ := Set.exists_min_image S norm hSfin ⟨x, hxL, hxP, le_rfl⟩
 refine ⟨v, hv.1, hv.2.1, ?_⟩
 intro w hwL hwP
 by_cases hw : ‖w‖ ≤ ‖x‖
 · exact hmin w ⟨hwL, hwP, hw⟩
 · exact hv.2.2.trans (le_of_not_ge hw)
variable [NormedSpace ℝ E]
theorem ZkK (L : Submodule ℤ E) [DiscreteTopology L]
  [IsZLattice ℝ L] (W : Submodule ℝ E) (hW : W ≠ ⊤) :
  ∃ v ∈ L, v ∉ W ∧ 0 < ‖v‖ ∧
   ∀ w ∈ L, w ∉ W → ‖v‖ ≤ ‖w‖ := by
 have hex : ∃ v ∈ L, v ∉ W := by
  by_contra h
  have hle : Submodule.span ℝ (L : Set E) ≤ W := by
   apply Submodule.span_le.mpr
   intro v hv
   by_contra hvW
   exact h ⟨v, hv, hvW⟩
  rw [IsZLattice.span_top] at hle
  exact hW (top_le_iff.mp hle)
 obtain ⟨v, hvL, hvW, hmin⟩ := Zhu L (fun v => v ∉ W) hex
 refine ⟨v, hvL, hvW, norm_pos_iff.mpr ?_, hmin⟩
 intro hv0
 exact hvW (hv0 ▸ W.zero_mem)
def ZlZ {n : ℕ} (v : Fin n → E) (i : Fin n) : Set E :=
 v '' {j | j < i}
omit [NormedAddCommGroup E] [ProperSpace E] [NormedSpace ℝ E] in
lemma Zma {n : ℕ} (v : Fin n → E) (x : E) (i : Fin n) :
   ZlZ (Fin.snoc v x) i.castSucc = ZlZ v i := by
 ext y
 constructor
 · rintro ⟨j, hj, rfl⟩
   revert hj
   refine Fin.lastCases ?_ (fun k hj => ?_) j
   · intro hj
     exact (not_lt_of_ge (Fin.le_last _) hj).elim
   · exact ⟨k, hj, by simp⟩
 · rintro ⟨j, hj, rfl⟩
   exact ⟨j.castSucc, hj, by simp⟩
omit [NormedAddCommGroup E] [ProperSpace E] [NormedSpace ℝ E] in
lemma ZoE {n : ℕ} (v : Fin n → E) (x : E) :
   ZlZ (Fin.snoc v x) (Fin.last n) = Set.range v := by
 ext y
 constructor
 · rintro ⟨j, hj, rfl⟩
   revert hj
   refine Fin.lastCases ?_ (fun k _ => ?_) j
   · intro hj
     simp at hj
   · exact ⟨k, by simp⟩
 · rintro ⟨j, rfl⟩
   exact ⟨j.castSucc, Fin.castSucc_lt_last j, by simp⟩
structure Zdt (L : Submodule ℤ E) {n : ℕ} (v : Fin n → E) : Prop where
 mem_lattice : ∀ i, v i ∈ L
 independent : LinearIndependent ℝ v
 minimal : ∀ i, ∀ w ∈ L, w ∉ Submodule.span ℝ (ZlZ v i) → ‖v i‖ ≤ ‖w‖
theorem ZoF (L : Submodule ℤ E) [DiscreteTopology L]
   [IsZLattice ℝ L] [FiniteDimensional ℝ E] (n : ℕ)
   (hn : n ≤ Module.finrank ℝ E) :
   ∃ v : Fin n → E, Zdt L v := by
 induction n with
 | zero =>
   refine ⟨Fin.elim0, ?_⟩
   exact ⟨by intro i; exact i.elim0, linearIndependent_empty_type, by intro i; exact i.elim0⟩
 | succ n ih =>
   obtain ⟨v, hv⟩ := ih (Nat.le_of_succ_le hn)
   have hW : Submodule.span ℝ (Set.range v) ≠ ⊤ := by
     intro htop
     have hdim := finrank_span_eq_card hv.independent
     rw [htop] at hdim
     have hdim' : Module.finrank ℝ E = n := by simpa using hdim
     omega
   obtain ⟨x, hxL, hxW, _, hxmin⟩ := ZkK L _ hW
   refine ⟨Fin.snoc v x, ?_⟩
   refine ⟨?_, linearIndependent_finSnoc.mpr ⟨hv.independent, hxW⟩, ?_⟩
   · intro i
     refine Fin.lastCases ?_ (fun j => ?_) i
     · simpa using hxL
     · simpa using hv.mem_lattice j
   · intro i
     refine Fin.lastCases ?_ (fun j => ?_) i
     · simpa only [ZoE, Fin.snoc_last] using hxmin
     · simpa only [Zma, Fin.snoc_castSucc] using hv.minimal j
omit [ProperSpace E] in
theorem Zdt.Znf {L : Submodule ℤ E} {n : ℕ} {v : Fin n → E}
  (hv : Zdt L v) : Monotone (fun i => ‖v i‖) := by
 intro i j hij
 apply hv.minimal i (v j) (hv.mem_lattice j)
 exact hv.independent.notMem_span_image (not_lt_of_ge hij)
end Problem355.ZbJ
end OAI
end
section
namespace OAI
noncomputable section
open MeasureTheory Module Submodule
open scoped BigOperators
namespace Problem355.ZhG
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 {n : ℕ}
theorem ZdN (o : OrthonormalBasis (Fin n) ℝ E) :
  volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
 rw [measureReal_def,
  measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
 change (volume (parallelepiped o)).toReal = 1
 rw [o.volume_parallelepiped]
 simp
end Problem355.ZhG
end
end OAI
end
section
namespace OAI
namespace Problem355.Znm
open MeasureTheory Set Module InnerProductSpace
open scoped BigOperators
theorem ZqF {ι : Type*} [Fintype ι]
  (L : AddSubgroup (ι → ℝ)) [Countable L] (F : Set (ι → ℝ))
  (hF : IsAddFundamentalDomain L F volume) (w : ι → ℝ)
  (hempty : ∀ x : L, (∀ i, |(x : ι → ℝ) i| < w i) → x = 0) :
  (∏ i, ENNReal.ofReal (2 * w i)) ≤ volume F * 2 ^ Fintype.card ι := by
 let S : Set (ι → ℝ) := Set.pi Set.univ (fun i => Set.Ioo (-w i) (w i))
 have hsymm : ∀ x ∈ S, -x ∈ S := by
  intro x hx i hi
  have hxi := hx i hi
  change -w i < -x i ∧ -x i < w i
  constructor <;> linarith [hxi.1, hxi.2]
 have hconv : Convex ℝ S := convex_pi (by intro i hi; exact convex_Ioo _ _)
 have hvol : volume S ≤ volume F * 2 ^ Module.finrank ℝ (ι → ℝ) := by
  by_contra h
  obtain ⟨x, hx, hxS⟩ :=
   exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    hF hsymm hconv (lt_of_not_ge h)
  apply hx
  apply hempty x
  intro i
  exact abs_lt.mpr (hxS i (Set.mem_univ i))
 simpa [S, Real.volume_pi_Ioo, sub_neg_eq_add, ← two_mul,
  Module.finrank_pi] using hvol
theorem Zpi {ι : Type*} [Fintype ι]
  (L : AddSubgroup (ι → ℝ)) [Countable L] (F : Set (ι → ℝ))
  (hF : IsAddFundamentalDomain L F volume) (hfinite : volume F ≠ ⊤)
  (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
  (hempty : ∀ x : L, (∀ i, |(x : ι → ℝ) i| < w i) → x = 0) :
  (∏ i, w i) ≤ volume.real F := by
 have he := ZqF L F hF w hempty
 have ht : volume F * 2 ^ Fintype.card ι ≠ ⊤ := by finiteness
 have hr := ENNReal.toReal_mono ht he
 have hreal (i : ι) : (ENNReal.ofReal (2 * w i)).toReal = 2 * w i :=
  ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hw i))
 simp only [ENNReal.toReal_prod, ENNReal.toReal_mul, ENNReal.toReal_pow,
  ENNReal.toReal_ofNat, hreal] at hr
 rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at hr
 have hp : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
 change (∏ i, w i) ≤ (volume F).toReal
 nlinarith
theorem Zec
   {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
   [FiniteDimensional ℝ E] {n : ℕ} (hdim : finrank ℝ E = Fintype.card (Fin n))
   (v : Fin n → E) (j : Fin n) {x : E}
   (hx : x ∈ Submodule.span ℝ (v '' Set.Iio j)) :
   (gramSchmidtOrthonormalBasis hdim v).repr x j = 0 := by
 induction hx using Submodule.span_induction with
 | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact gramSchmidtOrthonormalBasis_inv_triangular' hdim v hi
 | zero => simp
 | add x y hx hy hx' hy' => simp [map_add, hx', hy']
 | smul a x hx hx' => simp [map_smul, hx']
theorem ZiU
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (hdim : finrank ℝ E = Fintype.card (Fin 3))
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (v : Fin 3 → E)
  (hmin : ∀ j (x : E), x ∈ L → x ∉ Submodule.span ℝ (v '' Set.Iio j) →
   ‖v j‖ ≤ ‖x‖) :
  (∏ i, ‖v i‖) ≤ 8 * ZLattice.covolume L := by
 classical
 let b := gramSchmidtOrthonormalBasis hdim v
 let f : (Fin 3 → ℝ) ≃L[ℝ] E :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.trans b.repr.toContinuousLinearEquiv.symm
 have hf : MeasurePreserving f :=
  b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp (Fin 3))
 let L' := ZLattice.comap ℝ L f.toLinearMap
 let b' := IsZLattice.basis L'
 let : Countable L'.toAddSubgroup := b'.equivFun.injective.countable
 let F := ZSpan.fundamentalDomain (b'.ofZLatticeBasis ℝ)
 have hF : IsAddFundamentalDomain L'.toAddSubgroup F volume :=
  ZLattice.isAddFundamentalDomain b' volume
 have hfinite : volume F ≠ ⊤ :=
  (ZSpan.fundamentalDomain_isBounded (b'.ofZLatticeBasis ℝ)).measure_lt_top.ne
 have hh := Zpi L'.toAddSubgroup F hF hfinite (fun i => ‖v i‖ / 2) (fun _ => by positivity) (by
  intro x hx
  by_contra hzero
  have hxmem : f (x : Fin 3 → ℝ) ≠ 0 := fun h => hzero (Subtype.ext (f.map_eq_zero_iff.mp h))
  have hp := norm_pos_iff.mpr hxmem
  have hsmall (j : Fin 3) : |(x : Fin 3 → ℝ) j| < ‖f x‖ / 2 := by
   by_cases hxj : (x : Fin 3 → ℝ) j = 0
   · simpa [hxj] using half_pos hp
   apply (hx j).trans_le
   apply div_le_div_of_nonneg_right _ (by norm_num)
   apply hmin j _ x.property
   intro h
   have hz := Zec hdim v j h
   change b.repr (f (x : Fin 3 → ℝ)) j = 0 at hz
   exact hxj (by simpa [f] using hz)
  have hsq (j : Fin 3) := sq_lt_sq.mpr (show |(x : Fin 3 → ℝ) j| < |‖f x‖ / 2| by simpa [abs_of_pos (half_pos hp)] using hsmall j)
  have hnorm : ‖f x‖ ^ 2 = ∑ i, (x : Fin 3 → ℝ) i ^ 2 := by
   calc
     _ = ‖b.repr (f x)‖ ^ 2 := by simp
     _ = _ := by simp [EuclideanSpace.real_norm_sq_eq, f]
  rw [Fin.sum_univ_three] at hnorm
  nlinarith [hsq 0, hsq 1, hsq 2])
 have hcov : volume.real F = ZLattice.covolume L := by
  rw [← ZLattice.covolume_eq_measure_fundamentalDomain L' volume
   (ZLattice.isAddFundamentalDomain b' volume)]
  exact ZLattice.covolume_comap L volume volume hf
 rw [hcov, Finset.prod_div_distrib] at hh
 norm_num at hh
 linarith
end Problem355.Znm
end OAI
end
section
namespace OAI
namespace Problem355.Zar
open scoped BigOperators
variable {ι : Type*} [Fintype ι]
def toEuclidean (x : ι → ℤ) : EuclideanSpace ℝ ι :=
 WithLp.toLp 2 (fun i => (x i : ℝ))
end Problem355.Zar
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZdC
open Module Matrix Ze
abbrev Vec := Fin 3 → ℤ
@[simp] lemma Zsd : Zp (0 : Vec) = 0 := by
 ext i
 simp [Zp]
def toLattice (y v : Vec) (hv : y ⬝ᵥ v = 0) : lattice y :=
 ⟨⟨Zp v, by change Zbm y (Zp v) = 0; rw [Zcf, hv]; norm_num⟩, Zig v⟩
@[simp] lemma Zsa (y v : Vec) (hv : y ⬝ᵥ v = 0) :
 ((toLattice y v hv : ZQ y) : ZI) = Zp v := rfl
@[simp] lemma ZrW (y v : Vec) (hv : y ⬝ᵥ v = 0) :
 ‖(toLattice y v hv : ZQ y)‖ = ‖Zs.Zw v‖ := rfl
lemma ZnD (y v w : Vec) (hv : y ⬝ᵥ v = 0) (hw : y ⬝ᵥ w = 0)
  (h : toLattice y v hv = toLattice y w hw) : v = w := by
 exact ZgP (congrArg (fun a : lattice y => ((a : ZQ y) : ZI)) h)
def ZjD (y : Vec) (S : Finset Vec) (hS : ∀ v ∈ S, y ⬝ᵥ v = 0) :
  Finset (lattice y) :=
 S.attach.map ⟨fun v : {v // v ∈ S} => toLattice y v (hS v v.property), by
  intro v w h
  apply Subtype.ext
  exact ZnD y v w _ _ h⟩
@[simp] lemma ZpK (y : Vec) (S : Finset Vec)
 (hS : ∀ v ∈ S, y ⬝ᵥ v = 0) :
 (ZjD y S hS).card = S.card := by simp [ZjD]
lemma Zoa (y : Vec) (S : Finset Vec)
  (hS : ∀ v ∈ S, y ⬝ᵥ v = 0) (R : ℝ)
  (hR : ∀ v ∈ S, ‖Zs.Zw v‖ ≤ R) :
  ∀ a ∈ ZjD y S hS, ‖(a : ZQ y)‖ ≤ R := by
 intro a ha
 obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp ha
 exact hR v v.property
end Problem355.ZdC
end
end OAI
end
section
namespace OAI
namespace Problem355.Zky
open Module
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
def Zgi (L : Submodule R M) (f : M →ₗ[R] R) :
  LinearMap.ker (f.comp L.subtype) ≃ₗ[R] ↥(L ⊓ LinearMap.ker f) where
 toFun x := ⟨x.1.1, x.1.2, x.2⟩
 invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
 left_inv _ := rfl
 right_inv _ := rfl
 map_add' _ _ := rfl
 map_smul' _ _ := rfl
end Problem355.Zky
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Lattice
open Module MeasureTheory
open scoped BigOperators Matrix
theorem ZkL
  {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (b : Basis ι ℤ L) (o : OrthonormalBasis ι ℝ E) :
  ZLattice.covolume L ^ 2 = (Matrix.gram ℝ (fun i => (b i : E))).det := by
 have hvol : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
  simp [Measure.real, o.volume_parallelepiped]
 have hcov := ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis
 rw [hvol, mul_one] at hcov
 rw [hcov, sq_abs, Matrix.gram_eq_conjTranspose_mul o,
  Matrix.det_mul, Matrix.det_conjTranspose]
 simp only [Basis.det_apply, pow_two, star_trivial]
 rfl
theorem Zhv
  (u v w y : Fin 3 → ℝ)
  (hu : u ⬝ᵥ y = 0) (hv : v ⬝ᵥ y = 0) :
  (y ⬝ᵥ w) • (u ⨯₃ v) = (Matrix.det ![u, v, w]) • y := by
 have hz : (u ⨯₃ v) ⨯₃ y = 0 := by
  rw [cross_cross_eq_smul_sub_smul, hu, hv, zero_smul, zero_smul, sub_self]
 have h := cross_cross_eq_smul_sub_smul (u ⨯₃ v) y w
 rw [hz] at h
 have ht : (u ⨯₃ v) ⬝ᵥ w = Matrix.det ![u, v, w] := by
  rw [dotProduct_comm, triple_product_permutation, triple_product_eq_det]
 have hzero : (Matrix.det ![u, v, w]) • y - (y ⬝ᵥ w) • (u ⨯₃ v) = 0 := by
  simpa only [map_zero, LinearMap.zero_apply, ht] using h.symm
 exact (sub_eq_zero.mp hzero).symm
theorem ZgR
  (u v : EuclideanSpace ℝ (Fin 3)) :
  (Matrix.gram ℝ ![u, v]).det =
   ‖WithLp.toLp 2 (u.ofLp ⨯₃ v.ofLp)‖ ^ 2 := by
 rw [Matrix.det_fin_two, ← real_inner_self_eq_norm_sq]
 simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
  EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
 rw [cross_dot_cross]
 rw [dotProduct_comm v.ofLp u.ofLp]
theorem Zlm
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (b : Basis (Fin 2) ℤ L) (o : OrthonormalBasis (Fin 2) ℝ E)
  (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
  ZLattice.covolume L =
   ‖WithLp.toLp 2 ((f (b 0)).ofLp ⨯₃ (f (b 1)).ofLp)‖ := by
 apply (sq_eq_sq₀ (ZLattice.covolume_pos L volume).le (norm_nonneg _)).mp
 rw [ZkL L b o, ← ZgR]
 congr 1
 ext i j
 fin_cases i <;> fin_cases j <;> simp [Matrix.gram_apply, f.inner_map_map]
theorem ZiV
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (L : Submodule ℤ (ι → ℤ)) (b : Basis ι ℤ L) :
  |(Matrix.of (fun i j => ((b i : ι → ℤ) j : ℝ))).det| =
   (L.toAddSubgroup.index : ℝ) := by
 have h : L.toAddSubgroup.index =
   (Matrix.of (fun i => (b i : ι → ℤ))).det.natAbs := by
  simpa only [Pi.basisFun_det_apply] using
   AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ ι) L.toAddSubgroup b
 rw [h, Nat.cast_natAbs, Int.cast_abs, Int.cast_det]
 rfl
theorem ZiW
  (L : Submodule ℤ (Fin 3 → ℤ)) (b : Basis (Fin 2 ⊕ Unit) ℤ L) :
  |(Matrix.det ![(fun j => ((b (Sum.inl 0) : Fin 3 → ℤ) j : ℝ)),
   (fun j => ((b (Sum.inl 1) : Fin 3 → ℤ) j : ℝ)),
   (fun j => ((b (Sum.inr ()) : Fin 3 → ℤ) j : ℝ))])| =
    (L.toAddSubgroup.index : ℝ) := by
 let e : Fin 2 ⊕ Unit ≃ Fin 3 :=
  (Equiv.sumCongr (Equiv.refl (Fin 2)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv
 have h := ZiV L (b.reindex e)
 convert h using 1
 congr 2
 ext i j
 fin_cases i <;> simp [e, Basis.reindex_apply, finSumFinEquiv, Fin.addCases]
end Problem355.Lattice
namespace Problem355.Ze
open Module
open scoped BigOperators Matrix
theorem Zis
  (y z : Fin 3 → ℤ) (hyz : y ⬝ᵥ z = 1)
  (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
  (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L)
  (g : ℤ) (hg : 0 < g)
  (hdiv : ∀ v : L, g ∣ y ⬝ᵥ (v : Fin 3 → ℤ))
  (u : L) (hu : y ⬝ᵥ (u : Fin 3 → ℤ) = g) :
  ZLattice.covolume (ZG y L) =
   (L.toAddSubgroup.index : ℝ) * ‖Zp y‖ / (g : ℝ) := by
 let := ZbC y z hyz L E hE hL
 let f := (ZjB y).comp L.subtype
 let e : f.ker ≃ₗ[ℤ] ZG y L :=
  (Zky.Zgi L (ZjB y)).trans (Zbq y L)
 let bZ : Basis (Fin 2) ℤ f.ker :=
  (Zqn y z hyz L E hE hL).map
   (Zky.Zgi L (ZjB y)).symm
 let b : Basis (Fin 2) ℤ (ZG y L) := bZ.map e
 let emb := (ZQ y).subtypeₗᵢ
 have hb (i : Fin 2) : emb (b i) = Zp ((bZ i : L) : Fin 3 → ℤ) := by
  rfl
 have hdet : |Matrix.det ![(emb (b 0)).ofLp, (emb (b 1)).ofLp,
   (Zp (u : Fin 3 → ℤ)).ofLp]| = (L.toAddSubgroup.index : ℝ) := by
  rw [hb 0, hb 1]
  let F := f.ker.subtype.coprod (LinearMap.toSpanSingleton ℤ L u)
  have hF : Function.Bijective F := by
   constructor
   · apply (LinearMap.ker_eq_bot.mp ?_)
     apply LinearMap.ker_eq_bot'.mpr
     rintro ⟨w,t⟩ h
     change (w : L) + t • u = 0 at h
     have h' := congrArg f h
     have hw : f w = 0 := w.property
     have hfu : f u = g := hu
     simp [map_add, hw, hfu, hg.ne'] at h'
     subst t
     simpa using h
   · intro w
     obtain ⟨t,ht⟩ := hdiv w
     have ht' : f w = g*t := ht
     refine ⟨(⟨w - t • u, ?_⟩,t), sub_add_cancel _ _⟩
     change f (w - t • u) = 0
     simp [ht', show f u = g from hu, mul_comm]
  let B := (bZ.prod (Basis.singleton Unit ℤ)).map (LinearEquiv.ofBijective F hF)
  simpa [B, F, Zp, LinearMap.coprod_apply] using Lattice.ZiW L B
 have hzero (i : Fin 2) : (emb (b i)).ofLp ⬝ᵥ (Zp y).ofLp = 0 := by
  rw [dotProduct_comm]
  exact (b i : ZQ y).property
 have hheight : (Zp y).ofLp ⬝ᵥ (Zp (u : Fin 3 → ℤ)).ofLp = (g : ℝ) := by
  change (∑ i, (y i : ℝ) * ((u : Fin 3 → ℤ) i : ℝ)) = (g : ℝ)
  exact_mod_cast hu
 let o := (stdOrthonormalBasis ℝ (ZQ y)).reindex (finCongr (Zeb y z hyz))
 rw [Lattice.Zlm _ b o emb, eq_div_iff (by exact_mod_cast hg.ne')]
 have h := congrArg (fun v : Fin 3 → ℝ => ‖WithLp.toLp 2 v‖)
  (Lattice.Zhv _ _ (Zp (u : Fin 3 → ℤ)).ofLp _ (hzero 0) (hzero 1))
 simpa only [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, hdet, hheight,
  abs_of_pos (show 0 < (g : ℝ) by exact_mod_cast hg), WithLp.toLp_ofLp, mul_comm] using h
theorem Zpj (y z : Fin 3 → ℤ) (hyz : y ⬝ᵥ z = 1) :
  ZLattice.covolume (lattice y) = ‖Zp y‖ := by
 have h := Zis y z hyz ⊤ 1 one_ne_zero (fun _ => trivial) 1 zero_lt_one
  (fun _ => one_dvd _) ⟨z,trivial⟩ hyz
 simpa [ZG, ZgQ, lattice] using h
end Problem355.Ze
end
end OAI
end
section
namespace OAI
namespace Problem355.ZiE
theorem Zbx {ι : Type*} [Fintype ι]
   (u v : EuclideanSpace ℝ ι) (i j : ι)
   (hu : u i ≠ 0) (hv : v i = 0) (hvj : v j ≠ 0) :
   LinearIndependent ℝ ![u, v] := by
 apply linearIndependent_fin2.mpr
 change v ≠ 0 ∧ ∀ a : ℝ, a • v ≠ u
 constructor
 · intro h
   apply hvj
   simp only [h, PiLp.zero_apply]
 · intro a h
   have hi := congrArg (fun x : EuclideanSpace ℝ ι => x i) h
   simp only [PiLp.smul_apply, smul_eq_mul, hv, mul_zero] at hi
   exact hu hi.symm
theorem Zkf (x : Fin 3 → ℤ) (hx : x ≠ 0) :
    ∃ u v : Fin 3 → ℤ,
      dotProduct x u = 0 ∧ dotProduct x v = 0 ∧
      LinearIndependent ℝ ![Zar.toEuclidean u, Zar.toEuclidean v] ∧
      ‖Zar.toEuclidean u‖ ≤ ‖Zar.toEuclidean x‖ ∧
      ‖Zar.toEuclidean v‖ ≤ ‖Zar.toEuclidean x‖ := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by simpa [funext_iff] using hx
  have hR : (x i : ℝ) ≠ 0 := by exact_mod_cast hi
  fin_cases i
  · refine ⟨![-x 1, x 0, 0], ![-x 2, 0, x 0], ?_, ?_, ?_, ?_, ?_⟩ <;> try apply Zbx _ _ 1 2
    all_goals first | solve | simp_all [Zar.toEuclidean, dotProduct, Fin.sum_univ_three] <;> ring
                    | apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
                      simp [EuclideanSpace.real_norm_sq_eq, Zar.toEuclidean, Fin.sum_univ_three]
                      nlinarith only [sq_nonneg (x 0 : ℝ), sq_nonneg (x 1 : ℝ), sq_nonneg (x 2 : ℝ)]
  · refine ⟨![x 1, -x 0, 0], ![0, -x 2, x 1], ?_, ?_, ?_, ?_, ?_⟩ <;> try apply Zbx _ _ 0 2
    all_goals first | solve | simp_all [Zar.toEuclidean, dotProduct, Fin.sum_univ_three] <;> ring
                    | apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
                      simp [EuclideanSpace.real_norm_sq_eq, Zar.toEuclidean, Fin.sum_univ_three]
                      nlinarith only [sq_nonneg (x 0 : ℝ), sq_nonneg (x 1 : ℝ), sq_nonneg (x 2 : ℝ)]
  · refine ⟨![x 2, 0, -x 0], ![0, x 2, -x 1], ?_, ?_, ?_, ?_, ?_⟩ <;> try apply Zbx _ _ 0 1
    all_goals first | solve | simp_all [Zar.toEuclidean, dotProduct, Fin.sum_univ_three] <;> ring
                    | apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
                      simp [EuclideanSpace.real_norm_sq_eq, Zar.toEuclidean, Fin.sum_univ_three]
                      nlinarith only [sq_nonneg (x 0 : ℝ), sq_nonneg (x 1 : ℝ), sq_nonneg (x 2 : ℝ)]
end Problem355.ZiE
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Anisotropic
open Matrix
open scoped Matrix
open Zo ZdC
lemma Zed (u v : Zv)
  (huv : u ⨯₃ v ≠ 0) :
  LinearIndependent ℝ (fun i : Fin 2 => Zs.Zw (![u, v] i)) := by
 let uR : Fin 3 → ℝ := fun i => (u i : ℝ)
 let vR : Fin 3 → ℝ := fun i => (v i : ℝ)
 have hcross : uR ⨯₃ vR ≠ 0 := by
  intro h
  apply huv
  ext i
  have hi := congrFun h i
  fin_cases i <;>
   simp [cross_apply, uR, vR] at hi ⊢ <;> exact_mod_cast hi
 have hind := crossProduct_ne_zero_iff_linearIndependent.mp hcross
 apply LinearIndependent.of_comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
 have he : (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap ∘ (fun i : Fin 2 => Zs.Zw (![u,v] i)) = ![uR,vR] := by
  funext i
  fin_cases i <;> rfl
 rw [he]
 exact hind
end Problem355.Anisotropic
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Anisotropic
open Matrix
open scoped Matrix
open Zo
abbrev Triple := Zv × Zv × Zv
open Ze ZdC in
private theorem ZpL (y u v : Zv) (hp : IsPrimitive y) (R : ℝ)
  (hu : y ⬝ᵥ u = 0) (hv : y ⬝ᵥ v = 0)
  (hind : LinearIndependent ℝ ![Zs.Zw u,Zs.Zw v])
  (hun : length u ≤ R) (hvn : length v ≤ R) (S : Finset Zv)
  (hs : ∀ w ∈ S, w ⬝ᵥ y = 0 ∧ length w ≤ R) : (S.card : ℝ) ≤ 9*Real.pi*R^2/length y := by
 obtain ⟨z,hz⟩ := (ZB y).mp hp
 let := Zrm y z hz
 let b : Fin 2 → ZQ y := ![(toLattice y u hu : ZQ y),(toLattice y v hv : ZQ y)]
 have hi : LinearIndependent ℝ b := by
  apply LinearIndependent.of_comp (ZQ y).subtype
  convert hind using 1; funext i; fin_cases i <;> rfl
 have ha (w) (hw : w ∈ S) : y ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact (hs w hw).1
 have k := Zfj.Zbh (Zeb y z hz) (lattice y)
  b hi (by intro i; fin_cases i; exact (toLattice y u hu).property; exact (toLattice y v hv).property)
  (ZjD y S ha) R ((norm_nonneg _).trans hun) (by
   intro a hab
   exact Zoa y S ha R (fun w hw => (hs w hw).2) a hab)
  (by intro i; fin_cases i; exact hun; exact hvn)
 rwa [ZpK, Zpj y z hz] at k
private theorem Zob (S : Finset (Zv × Zv)) (U Y : ℝ)
  (hU : 1 ≤ U) (hUY : U ≤ Y)
  (hs : ∀ p ∈ S, IsPrimitive p.1 ∧ U ≤ length p.1 ∧ length p.1 ≤ 2*U ∧
   length p.2 ≤ 2*Y ∧ p.2 ⬝ᵥ p.1 = 0) :
  (S.card : ℝ) ≤ 4500 * Real.pi * U^2 * Y^2 := by
 classical
 have hU0 : 0 < U := by linarith
 let X := S.image Prod.fst
 have hx := Zs.Zir hU X (by
  rintro z hz; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz; exact (hs p hp).2.2.1)
 have h := ZdW.Zds S X Prod.fst
  (9*Real.pi*(2*Y)^2/U) (fun p hp => Finset.mem_image_of_mem _ hp) (by
   intro z hz
   obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
   let F := S.filter (fun q => q.1 = p.1)
   obtain ⟨u,v,hu,hv,hi,nu,nv⟩ := ZiE.Zkf p.1 (hs p hp).1.ne_zero
   have hc : (F.image Prod.snd).card = F.card := Finset.card_image_of_injOn (by
     intro q hq r hr he
     exact Prod.ext ((Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hr).2.symm) he)
   change (F.card : ℝ) ≤ _; rw [← hc]
   apply (ZpL p.1 u v (hs p hp).1 (2*Y) hu hv hi (nu.trans (by change length p.1 ≤ 2*Y; linarith [(hs p hp).2.2.1])) (nv.trans (by change length p.1 ≤ 2*Y; linarith [(hs p hp).2.2.1])) _ ?_).trans
   · exact div_le_div_of_nonneg_left (by positivity) hU0 (hs p hp).2.1
   · rintro _ hv; obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
     obtain ⟨hq,e⟩ := Finset.mem_filter.mp hq
     exact ⟨e ▸ (hs q hq).2.2.2.2, (hs q hq).2.2.2.1⟩)
 apply h.trans
 calc
  _ ≤ (125*U^3)*(9*Real.pi*(2*Y)^2/U) := mul_le_mul_of_nonneg_right hx (by positivity)
  _ = _ := by field_simp; ring
private theorem ZrA (S : Finset (Zv × Zv)) (U Y : ℝ)
   (hU : 1 ≤ U) (hY : 1 ≤ Y)
   (hs : ∀ p ∈ S, IsPrimitive p.1 ∧ IsPrimitive p.2 ∧ p.2 ⬝ᵥ p.1 = 0 ∧
    U ≤ length p.1 ∧ length p.1 ≤ 2*U ∧ Y ≤ length p.2 ∧ length p.2 ≤ 2*Y) :
   (S.card : ℝ) ≤ 4500 * Real.pi * U^2 * Y^2 := by
 classical
 rcases le_total U Y with h|h
 · apply Zob S U Y hU h
   intro p hp; obtain ⟨a,b,c,d,e,f,g⟩ := hs p hp; exact ⟨a,d,e,g,c⟩
 · have k := Zob (S.image Prod.swap) Y U hY h (by
    intro q hq; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨a,b,c,d,e,f,g⟩ := hs p hp
    exact ⟨b,f,g,e,by rwa [dotProduct_comm]⟩)
   simpa [Finset.card_image_of_injective _ Prod.swap_injective, mul_right_comm] using k
private theorem Zrd (y : Zv)
   (S : Finset Zv) (center : EuclideanSpace ℝ (Fin 3))
   (R : ℝ) (hR0 : 0 ≤ R) (bound : ∀ T : Finset Zv, (∀ v ∈ T, v ⬝ᵥ y = 0 ∧ length v ≤ 2*R) → (T.card : ℝ) ≤ 9*Real.pi*(2*R)^2/length y)
   (hsize : ∀ v ∈ S, ‖Zs.Zw v - center‖ ≤ R)
   (hplane : ∀ v ∈ S, ∀ w ∈ S, (v - w) ⬝ᵥ y = 0) :
   (S.card : ℝ) ≤ 36 * Real.pi * R ^ 2 / length y := by
 classical
 by_cases hS : S.Nonempty
 · obtain ⟨w, hw⟩ := hS
   let T := S.image (fun v => v - w)
   have hcard : T.card = S.card := Finset.card_image_of_injective _
    (fun _ _ h => sub_left_inj.mp h)
   have hT (v : Zv) (hv : v ∈ T) :
     v ⬝ᵥ y = 0 ∧ length v ≤ 2 * R := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    refine ⟨hplane u hu w hw, ?_⟩
    have hcast : Zs.Zw (u - w) =
      Zs.Zw u - Zs.Zw w := by
     ext i
     simp [Zs.Zw]
    change ‖Zs.Zw (u - w)‖ ≤ 2 * R
    rw [hcast]
    rw [show Zs.Zw u - Zs.Zw w =
     (Zs.Zw u - center) - (Zs.Zw w - center) by abel]
    exact (norm_sub_le _ _).trans (by linarith [hsize u hu, hsize w hw])
   have h := bound T hT
   rw [hcard] at h
   convert h using 1; ring
 · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
   rw [hzero]
   simp only [Finset.card_empty, Nat.cast_zero]
   positivity
private theorem ZrN
   (S : Finset Triple) (y : Zv) (t : ℤ) (R₁ R₂ R₃ B₁ B₂ B₃ : ℝ)
   (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
   (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
   (hcross : ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • y)
   (hplane : ∀ x ∈ S, x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0)
   (hnorm : ∀ x ∈ S, ‖Zs.Zw x.1‖ ≤ R₁ ∧
     ‖Zs.Zw x.2.1‖ ≤ R₂ ∧ ‖Zs.Zw x.2.2‖ ≤ R₃)
   (hcount₁ : ∀ T : Finset Zv, (∀ v ∈ T, length v ≤ R₁) →
     (∀ v ∈ T, ∀ w ∈ T, (v - w) ⬝ᵥ y = 0) → (T.card : ℝ) ≤ B₁)
   (hcount₂ : ∀ T : Finset Zv,
     (∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖Zs.Zw z‖ ≤ R₂) → (T.card : ℝ) ≤ B₂)
   (hcount₃ : ∀ T : Finset Zv, T ⊆ S.image (fun x => x.2.2) →
     (∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖Zs.Zw z‖ ≤ R₃) → (T.card : ℝ) ≤ B₃) :
   (S.card : ℝ) ≤ B₁ * B₂ * B₃ := by
 classical
 let Y := S.image (fun x => x.2.1)
 let Z := S.image (fun x => x.2.2)
 have hY : (Y.card : ℝ) ≤ B₂ := by
   apply hcount₂
   intro v hv
   obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
   exact ⟨(hplane x hx).1, (hnorm x hx).2.1⟩
 have hZ : (Z.card : ℝ) ≤ B₃ := by
   apply hcount₃ _ (Finset.Subset.refl _)
   intro w hw
   obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
   exact ⟨(hplane x hx).2, (hnorm x hx).2.2⟩
 apply ZdW.ZnB S Y Z B₁ B₂ B₃ hB₁ hB₂ hY hZ
 · intro x hx
   exact ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
 · intro v _ w _
   let F := S.filter (fun x => x.2 = (v, w))
   let U := F.image Prod.fst
   have eqtail {x : Triple} (hx : x ∈ F) : x.2 = (v,w) := (Finset.mem_filter.mp hx).2
   have mem {x : Triple} (hx : x ∈ F) : x ∈ S := (Finset.mem_filter.mp hx).1
   have hc : U.card = F.card := Finset.card_image_of_injOn (by
     intro x hx z hz he
     exact Prod.ext he ((eqtail hx).trans (eqtail hz).symm))
   change (F.card : ℝ) ≤ _
   rw [← hc]
   apply hcount₁
   · rintro _ hv
     obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
     exact (hnorm x (mem hx)).1
   · intro u hu z hz
     obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
     obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hz
     obtain ⟨a,ha,he⟩ := hcross x (mem hx)
     rw [eqtail hx] at he
     have det {c : Triple} (hc : c ∈ F) : c.1 ⬝ᵥ (v ⨯₃ w) = t := by
      simpa only [eqtail hc] using hdet c (mem hc)
     have same := (det hx).trans (det hb).symm
     rw [he, dotProduct_smul, dotProduct_smul] at same
     rw [sub_dotProduct, mul_left_cancel₀ ha same, sub_self]
private theorem ZrB
  {α : Type*} [DecidableEq α] (S : Finset α) (length first weight : α → ℝ)
  (R₁ R₂ R₃ U Y C₀ C₁ : ℝ)
  (hU : 0 < U) (hY : 0 < Y) (hR₃ : 0 ≤ R₃) (hUR : U ≤ R₃)
  (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
  (hcard : (S.card : ℝ) ≤ C₀ * U ^ 2 * Y ^ 2)
  (hrange : ∀ y ∈ S, U ≤ first y ∧ Y ≤ length y)
  (hweight : ∀ y ∈ S, weight y ≤
   C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (length y ^ 2 * first y)) :
  ∑ y ∈ S, weight y ≤ C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2 := by
 have hB : 0 ≤ C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (Y ^ 2 * U) := by positivity
 calc
  ∑ y ∈ S, weight y ≤
    ∑ _y ∈ S, C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (Y ^ 2 * U) := by
   apply Finset.sum_le_sum
   intro y hy
   apply (hweight y hy).trans
   apply div_le_div_of_nonneg_left (by positivity) (by positivity)
   exact mul_le_mul (pow_le_pow_left₀ hY.le (hrange y hy).2 2)
    (hrange y hy).1 hU.le (sq_nonneg _)
  _ = (S.card : ℝ) * (C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (Y ^ 2 * U)) := by simp
  _ ≤ (C₀ * U ^ 2 * Y ^ 2) *
    (C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (Y ^ 2 * U)) :=
   mul_le_mul_of_nonneg_right hcard hB
  _ = (C₀ * C₁) * U ^ 2 * Y ^ 2 * (R₁ ^ 2 / Y) *
    (R₂ ^ 2 / Y) * (R₃ / U) := by field_simp
  _ ≤ (C₀ * C₁) * (R₁ * R₂ * R₃) ^ 2 :=
   ZjA hU hY hR₃ hUR (mul_nonneg hC₀ hC₁)
private theorem ZrX
  {α : Type*} [DecidableEq α] (S : Finset α) (length first weight : α → ℝ)
  (R₁ R₂ R₃ C₀ C₁ : ℝ)
  (h₂ : 1 ≤ R₂) (h₃ : 1 ≤ R₃)
  (h₂₁ : R₂ ≤ R₁) (h₃₁ : R₃ ≤ R₁)
  (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
  (hweight0 : ∀ y ∈ S, 0 ≤ weight y)
  (hrange : ∀ y ∈ S, 1 ≤ first y ∧ first y ≤ R₃ ∧
   1 ≤ length y ∧ length y ≤ R₂ * R₃)
  (hweight : ∀ y ∈ S, weight y ≤
   C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (length y ^ 2 * first y))
  (hgroup : ∀ (T : Finset α), T ⊆ S → ∀ U Y : ℝ,
   1 ≤ U → 1 ≤ Y →
   (∀ y ∈ T, U ≤ first y ∧ first y ≤ 2 * U ∧
     Y ≤ length y ∧ length y ≤ 2 * Y) →
   (T.card : ℝ) ≤ C₀ * U ^ 2 * Y ^ 2) :
  ∑ y ∈ S, weight y ≤
   2 * C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2 *
     (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
 classical
 have hprod : 1 ≤ R₂ * R₃ := by nlinarith
 have hA : 0 ≤ C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2 := by positivity
 have h := ZcF S first length weight h₃ hprod hA
  hweight0 hrange (by
   intro i j
   let T := S.filter fun y => (2 : ℝ) ^ i ≤ first y ∧ first y < 2 ^ (i + 1) ∧
     (2 : ℝ) ^ j ≤ length y ∧ length y < 2 ^ (j + 1)
   have hU : 1 ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
   have hY : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
   have hTS : T ⊆ S := Finset.filter_subset _ _
   have hT (y : α) (hy : y ∈ T) :
      (2 : ℝ) ^ i ≤ first y ∧ first y ≤ 2 * 2 ^ i ∧
      (2 : ℝ) ^ j ≤ length y ∧ length y ≤ 2 * 2 ^ j := by
     obtain ⟨_, h₁, h₂, h₃, h₄⟩ := Finset.mem_filter.mp hy
     exact ⟨h₁, by simpa [pow_succ, mul_comm] using h₂.le,
      h₃, by simpa [pow_succ, mul_comm] using h₄.le⟩
   change ∑ y ∈ T, weight y ≤ _
   by_cases hne : T.Nonempty
   · obtain ⟨y, hy⟩ := hne
     exact ZrB T length first weight R₁ R₂ R₃ _ _ C₀ C₁
      (by positivity) (by positivity) (by linarith)
      ((hT y hy).1.trans (hrange y (hTS hy)).2.1) hC₀ hC₁
      (hgroup T hTS _ _ hU hY hT)
      (fun z hz => ⟨(hT z hz).1, (hT z hz).2.2.1⟩)
      (fun z hz => hweight z (hTS hz))
   · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
     simpa using hA)
 calc
  ∑ y ∈ S, weight y ≤
     (C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2) *
      ((Real.log (2 * R₃) / Real.log 2) *
      (Real.log (2 * (R₂ * R₃)) / Real.log 2)) := by
   simpa only [mul_assoc] using h
  _ ≤ (C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2) *
     (2 * (Real.log (2 * R₁) / Real.log 2) ^ 2) :=
   mul_le_mul_of_nonneg_left (ZlX h₂ h₃ h₂₁ h₃₁) hA
  _ = _ := by ring
private theorem ZrC (S : Finset Triple) (v y : Zv) (hp : IsPrimitive y)
   (t : ℤ) (ht : t ≠ 0) (R₁ R₂ R₃ : ℝ) (h₂₁ : R₂ ≤ R₁) (h₃₂ : R₃ ≤ R₂)
   (hv : 0 < length v) (hvr : length v ≤ R₃)
   (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
   (hc : ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • y)
   (hplane : ∀ x ∈ S, x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0)
   (hline : ∀ x ∈ S, ∃ a : ℤ, x.2.2 = a • v)
   (hn : ∀ x ∈ S, length x.1 ≤ R₁ ∧ length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
   (S.card : ℝ) ≤ 972 * Real.pi^2 * R₁^2 * R₂^2 * R₃ / (length y^2 * length v) := by
 classical
 have hR : 0 ≤ R₃ := hv.le.trans hvr
 obtain he|hne := S.eq_empty_or_nonempty
 · subst S; simp only [Finset.card_empty, Nat.cast_zero]; positivity
 obtain ⟨a,ha⟩ := hne
 have hc0 : a.2.1 ⨯₃ a.2.2 ≠ 0 := by intro h; apply ht; simpa [h] using (hdet a ha).symm
 have hi : LinearIndependent ℝ ![Zs.Zw a.2.1,Zs.Zw a.2.2] := by
   convert Zed _ _ hc0 using 1; funext i; fin_cases i <;> rfl
 have count (R : ℝ) (h : R₂ ≤ R) := ZpL y a.2.1 a.2.2 hp R
   (by rw [dotProduct_comm]; exact (hplane a ha).1) (by rw [dotProduct_comm]; exact (hplane a ha).2)
   hi ((hn a ha).2.1.trans h) ((hn a ha).2.2.trans (h₃₂.trans h))
 have k := ZrN S y t R₁ R₂ R₃ (36*Real.pi*R₁^2/length y)
   (9*Real.pi*R₂^2/length y) (3*R₃/length v) (by positivity) (by positivity)
   hdet hc hplane hn (fun T hn' hd => Zrd y T 0 R₁ (by linarith) (count _ (by linarith))
    (by simpa using hn') hd) (count R₂ le_rfl) (by
    intro T hT hb
    let f := @Zs.Zw 3
    have hi : Function.Injective f := by intro a b e; ext i; have h := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w i) e; change (a i : ℝ) = (b i : ℝ) at h; exact_mod_cast h
    have k := Znl.ZiT (f v) (norm_pos_iff.mp hv) R₃ hR
     (T.image f) (by
      rintro _ ht0; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ht0
      obtain ⟨x,hxs,rfl⟩ := Finset.mem_image.mp (hT hw)
      obtain ⟨a,ha⟩ := hline x hxs; exact ⟨a,ha ▸ Zii.Zjp a v⟩)
     (by rintro _ hx; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx; exact (hb w hw).2)
    rw [Finset.card_image_of_injective _ hi] at k
    apply k.trans; change 1 + 2*R₃/length v ≤ _; apply (le_div_iff₀ hv).mpr; field_simp; nlinarith)
 convert k using 1; ring
theorem ZoG
  (S : Finset Triple) (t : ℤ) (ht : t ≠ 0)
  (R₁ R₂ R₃ : ℝ) (h₃ : 1 ≤ R₃) (h₃₂ : R₃ ≤ R₂) (h₂₁ : R₂ ≤ R₁)
  (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
  (hnorm : ∀ x ∈ S, length x.1 ≤ R₁ ∧
    length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
  (S.card : ℝ) ≤ (35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2) *
    (R₁ * R₂ * R₃) ^ 2 * Real.log (2 * R₁) ^ 2 := by
 classical
 let good (x : Triple) (p : Zv × Zv) : Prop :=
  IsPrimitive p.1 ∧ IsPrimitive p.2 ∧ p.2 ⬝ᵥ p.1 = 0 ∧ length p.1 ≤ R₃ ∧
  length p.2 ≤ R₂*R₃ ∧ (∃ a : ℤ, x.2.2 = a • p.1) ∧
  (∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • p.2) ∧
  x.2.1 ⬝ᵥ p.2 = 0 ∧ x.2.2 ⬝ᵥ p.2 = 0
 have ex (x : Triple) : ∃ p, x ∈ S → good x p := by
  by_cases hx : x ∈ S
  · have hc : x.2.1 ⨯₃ x.2.2 ≠ 0 := by intro h; apply ht; simpa [h] using (hdet x hx).symm
    have hw : x.2.2 ≠ 0 := by intro h; apply hc; simp [h]
    obtain ⟨g,hg,v,hv,ev⟩ := ZcP _ hw
    obtain ⟨k,hk,y,hy,ey,eb,ec,hyn,_⟩ := Zii.ZeG _ _ hc
    have hd := ec; rw [ev, smul_dotProduct, smul_eq_mul] at hd
    exact ⟨(v,y),fun _ => ⟨hv,hy,by rw [dotProduct_comm]; exact (mul_eq_zero.mp hd).resolve_left hg.ne',
     (Zii.ZdZ hg ev).trans (hnorm x hx).2.2,
     hyn.trans (mul_le_mul (hnorm x hx).2.1 (hnorm x hx).2.2 (norm_nonneg _) (by linarith)),
     ⟨g,ev⟩,⟨k,hk.ne',ey⟩,eb,ec⟩⟩
  · exact ⟨0,fun h => (hx h).elim⟩
 choose f hf using ex
 let P := S.image f
 let F (p : Zv × Zv) := S.filter fun x => f x = p
 have hG {p} {x} (hx : x ∈ F p) : good x p := (Finset.mem_filter.mp hx).2 ▸ hf x (Finset.mem_filter.mp hx).1
 have mem {p} {x} (hx : x ∈ F p) := (Finset.mem_filter.mp hx).1
 have prop {p} (hp : p ∈ P) : IsPrimitive p.1 ∧ IsPrimitive p.2 ∧ p.2 ⬝ᵥ p.1 = 0 ∧ length p.1 ≤ R₃ ∧ length p.2 ≤ R₂*R₃ := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨a,b,c,d,e,_⟩ := hf x hx; exact ⟨a,b,c,d,e⟩
 have h₂ := h₃.trans h₃₂
 have bound := ZrX P (fun p => length p.2) (fun p => length p.1) (fun p => ((F p).card : ℝ))
  R₁ R₂ R₃ (4500*Real.pi) (972*Real.pi^2) h₂ h₃ h₂₁ (h₃₂.trans h₂₁)
  (by positivity) (by positivity) (fun _ _ => Nat.cast_nonneg _) (by
    intro p hp; obtain ⟨a,b,c,d,e⟩ := prop hp
    exact ⟨Zs.Zdd a.ne_zero,d,Zs.Zdd b.ne_zero,e⟩) (by
    intro p hp; obtain ⟨a,b,c,d,e⟩ := prop hp
    apply ZrC _ _ _ b t ht _ _ _ h₂₁ h₃₂ ((by norm_num : (0:ℝ)<1).trans_le (Zs.Zdd a.ne_zero)) d
     (fun x hx => hdet x (mem hx)) (fun x hx => (hG hx).2.2.2.2.2.2.1)
     (fun x hx => (hG hx).2.2.2.2.2.2.2) (fun x hx => (hG hx).2.2.2.2.2.1) (fun x hx => hnorm x (mem hx))) (by
    intro T hT U Y hu hy hr
    exact ZrA T U Y hu hy (fun p hp => ⟨(prop (hT hp)).1,(prop (hT hp)).2.1,(prop (hT hp)).2.2.1,hr p hp⟩))
 have hc := ZdW.ZeN S P f (fun p => ((F p).card : ℝ))
  (fun x hx => Finset.mem_image_of_mem _ hx) (fun _ _ => le_rfl)
 apply (hc.trans bound).trans
 have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
 apply (le_of_eq (by ring : 2*(4500*Real.pi)*(972*Real.pi^2)*(R₁*R₂*R₃)^2*(Real.log (2*R₁)/Real.log 2)^2 =
  8748000 * (Real.pi^3 / (Real.log 2)^2 * (R₁*R₂*R₃)^2 * Real.log (2*R₁)^2))).trans
 calc
  _ ≤ 35721000 * (Real.pi^3 / (Real.log 2)^2 * (R₁*R₂*R₃)^2 * Real.log (2*R₁)^2) := by gcongr; norm_num
  _ = _ := by ring
theorem Zkg :
  0 < 35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2 := by
 have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
 positivity
end Problem355.Anisotropic
end
end OAI
end
section
namespace OAI
namespace Problem355.ZeZ
open scoped BigOperators
open Matrix
theorem ZcG {n : Type*} [Fintype n] [DecidableEq n] (v : EuclideanSpace ℝ n) (B : ℝ)
  (hB : 0 ≤ B) (hv : ∀ i, |v i| ≤ B) :
  ‖v‖ ≤ Real.sqrt (Fintype.card n) * B := by
 have hsum : (∑ i, ‖v i‖ ^ 2) ≤ (Fintype.card n : ℝ) * B ^ 2 := by
  calc
   (∑ i, ‖v i‖ ^ 2) ≤ ∑ _i : n, B ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
   _ = (Fintype.card n : ℝ) * B ^ 2 := by simp
 rw [EuclideanSpace.norm_eq]
 calc
  Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤
    Real.sqrt ((Fintype.card n : ℝ) * B ^ 2) := Real.sqrt_le_sqrt hsum
  _ = Real.sqrt (Fintype.card n) * B := by
   rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB]
end Problem355.ZeZ
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZaS
open scoped BigOperators
def radius (X : ℝ) (ℓ : Fin 3 → ℝ) (j : Fin 3) : ℝ := 1000 * X / ℓ j
lemma Zkh (X r : ℝ) (hX : 1 ≤ X) (hr : 1 ≤ r)
  (hrX : r ≤ 1000 * X) :
  Real.log (2 * r) ≤ 12 * Real.log (2 * X) := by
 have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
 have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
 have hlog2 : Real.log 2 ≤ Real.log (2 * X) :=
  Real.log_le_log (by norm_num) (by nlinarith)
 have hlogX : Real.log X ≤ Real.log (2 * X) :=
  Real.log_le_log hXp (by nlinarith)
 have hlog2000 : Real.log 2000 ≤ 11 * Real.log 2 := by
  have h := Real.log_le_log (show (0 : ℝ) < 2000 by norm_num)
   (show (2000 : ℝ) ≤ 2 ^ 11 by norm_num)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h
 calc
  Real.log (2 * r) ≤ Real.log (2000 * X) :=
   Real.log_le_log (by positivity) (by nlinarith)
  _ = Real.log 2000 + Real.log X := Real.log_mul (by norm_num) hXp.ne'
  _ ≤ 11 * Real.log (2 * X) + Real.log (2 * X) :=
   add_le_add (hlog2000.trans (mul_le_mul_of_nonneg_left hlog2 (by norm_num))) hlogX
  _ = 12 * Real.log (2 * X) := by ring
lemma ZpM (X : ℝ) (ℓ : Fin 3 → ℝ) (hX : 0 ≤ X)
  (hℓ : ∀ j, 0 < ℓ j) (hmono : Monotone ℓ) : Antitone (radius X ℓ) := by
 intro i j hij
 exact div_le_div_of_nonneg_left (by positivity) (hℓ i) (hmono hij)
lemma Zng (X : ℝ) (ℓ : Fin 3 → ℝ) (hℓ : ∀ j, 0 < ℓ j)
  (hℓX : ∀ j, ℓ j ≤ X) (j : Fin 3) : 1 ≤ radius X ℓ j := by
 apply (le_div_iff₀ (hℓ j)).mpr
 have hXp : 0 < X := lt_of_lt_of_le (hℓ j) (hℓX j)
 nlinarith [hℓX j]
lemma ZmM (X I : ℝ) (ℓ : Fin 3 → ℝ)
  (hX : 0 ≤ X) (hI : 0 < I) (hℓ : ∀ j, 0 < ℓ j)
  (hIℓ : I ≤ ∏ j, ℓ j) :
  (∏ j, radius X ℓ j) ≤ (1000 * X) ^ 3 / I := by
 have hprod : 0 < ∏ j, ℓ j := Finset.prod_pos fun j hj => hℓ j
 calc
  (∏ j, radius X ℓ j) = (1000 * X) ^ 3 / (∏ j, ℓ j) := by
   simp [radius, Finset.prod_div_distrib]
  _ ≤ (1000 * X) ^ 3 / I :=
   div_le_div_of_nonneg_left (by positivity) hI hIℓ
theorem ZjE (X I : ℝ) (ℓ : Fin 3 → ℝ)
  (hX : 1 ≤ X) (hI : 0 < I) (hℓ1 : ∀ j, 1 ≤ ℓ j)
  (hℓX : ∀ j, ℓ j ≤ X) (hIℓ : I ≤ ∏ j, ℓ j) :
  (∏ j, radius X ℓ j) ^ 2 * Real.log (2 * radius X ℓ 0) ^ 2 ≤
   (1000 : ℝ) ^ 6 * 144 * (X ^ 6 / I ^ 2) * Real.log (2 * X) ^ 2 := by
 have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
 have hℓ : ∀ j, 0 < ℓ j := fun j => lt_of_lt_of_le zero_lt_one (hℓ1 j)
 have hr : ∀ j, 1 ≤ radius X ℓ j := Zng X ℓ hℓ hℓX
 have hrX : radius X ℓ 0 ≤ 1000 * X := by
  apply (div_le_iff₀ (hℓ 0)).mpr
  nlinarith [hℓ1 0]
 have hlog := Zkh X (radius X ℓ 0) hX (hr 0) hrX
 have hlognonneg : 0 ≤ Real.log (2 * radius X ℓ 0) :=
  Real.log_nonneg (by nlinarith [hr 0])
 have hprodnonneg : 0 ≤ ∏ j, radius X ℓ j :=
  Finset.prod_nonneg fun j hj => le_trans zero_le_one (hr j)
 have hprod := ZmM X I ℓ hXp.le hI hℓ hIℓ
 calc
  (∏ j, radius X ℓ j) ^ 2 * Real.log (2 * radius X ℓ 0) ^ 2 ≤
    ((1000 * X) ^ 3 / I) ^ 2 * (12 * Real.log (2 * X)) ^ 2 :=
   mul_le_mul (pow_le_pow_left₀ hprodnonneg hprod 2)
    (pow_le_pow_left₀ hlognonneg hlog 2) (sq_nonneg _) (sq_nonneg _)
  _ = (1000 : ℝ) ^ 6 * 144 * (X ^ 6 / I ^ 2) * Real.log (2 * X) ^ 2 := by
   ring
def ZbP (a : ℝ) : Prop :=
 ∀ (r : Fin 3 → ℝ) (u : ℤ) (T : Finset (Matrix (Fin 3) (Fin 3) ℤ)),
  Antitone r → 1 ≤ r 2 → u ≠ 0 →
  (∀ Q ∈ T, Q.det = u ∧ ∀ j,
   ‖(WithLp.toLp 2 (fun i => (Q i j : ℝ)) : EuclideanSpace ℝ (Fin 3))‖ ≤ r j) →
  (T.card : ℝ) ≤ a * (∏ j, r j) ^ 2 * Real.log (2 * r 0) ^ 2
end Problem355.ZaS
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZkX
open Module Submodule MeasureTheory
open scoped BigOperators
abbrev E := EuclideanSpace ℝ (Fin 3)
open ZaS
theorem Zfc
   (a : ℝ) (ha : 0 ≤ a) (hanis : ZaS.ZbP a)
   (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
   (hunit : ∀ x ∈ L, x ≠ 0 → 1 ≤ ‖x‖)
   (b : Basis (Fin 3) ℝ E) (hb : ZbJ.Zdt L b)
   (X : ℝ) (hX : 1 ≤ X) (hlast : ‖b 2‖ ≤ X)
   (S : Finset (Matrix (Fin 3) (Fin 3) ℝ))
   (hrows : ∀ A ∈ S, ∀ i, (WithLp.toLp 2 (A i) : E) ∈ L)
   (hnorm : ∀ A ∈ S, ∀ i, ‖(WithLp.toLp 2 (A i) : E)‖ ≤ X)
   (t : ℝ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
   (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
    ZLattice.covolume L ^ 2 := by
 classical
 let ℓ := fun i => ‖b i‖
 let H := Submodule.span ℤ (Set.range b)
 let m := H.toAddSubgroup.relIndex L.toAddSubgroup
 let V : Matrix (Fin 3) (Fin 3) ℝ := fun i j => b i j
 let o := EuclideanSpace.basisFun (Fin 3) ℝ
 have detRows (U : Matrix (Fin 3) (Fin 3) ℝ) :
    o.toBasis.det (fun i => WithLp.toLp 2 (U i)) = U.det := by
   rw [Basis.det_apply, ← Matrix.det_transpose U]; rfl
 have vol : ZLattice.covolume H = |V.det| := by
   rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume o.toBasis,
    ZhG.ZdN, mul_one]; exact congrArg abs (detRows V)
 have hI := ZLattice.covolume_pos L volume
 have hd : 0 < |V.det| := vol ▸ ZLattice.covolume_pos H volume
 have ratio : (m : ℝ) * ZLattice.covolume L = |V.det| := by
   rw [← vol]; apply (eq_div_iff hI.ne').mp
   exact (ZLattice.covolume_div_covolume_eq_relIndex' H L (Submodule.span_le.mpr
    (Set.range_subset_iff.mpr hb.mem_lattice))).symm
 have hm : (0:ℝ) < m := by by_contra! h; nlinarith [mul_nonpos_of_nonpos_of_nonneg h hI.le]
 have hℓ (i) : 0 < ℓ i := norm_pos_iff.mpr (b.ne_zero i)
 have h1 (i) : 1 ≤ ℓ i := hunit _ (hb.mem_lattice i) (b.ne_zero i)
 have hX' (i) : ℓ i ≤ X := (hb.Znf (Fin.le_last i)).trans hlast
 have hp := Znm.ZiU (Module.finrank_eq_card_basis b) L b hb.minimal
 let row (A : S) i : E := WithLp.toLp 2 (A.val i)
 choose q hq using fun (A : S) i => (Submodule.mem_span_range_iff_exists_fun ℤ).mp
   (H.toAddSubgroup.nsmul_relIndex_mem (K := L.toAddSubgroup) (hrows A A.property i))
 let f (A : S) : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of (q A)
 have mul (A : S) : (f A).map (Int.castRingHom ℝ) * V = (m:ℝ) • A.val := by
   ext i j
   rw [Matrix.mul_apply]
   simpa [f,V, nsmul_eq_mul,zsmul_eq_mul,m] using congrArg (fun x : E => x j) (hq A i)
 have inj : Function.Injective f := fun A B e => Subtype.ext (smul_right_injective _ hm.ne'
   ((mul A).symm.trans (e ▸ mul B)))
 have det (A : S) : ((f A).det : ℝ) * V.det = (m:ℝ)^3*t := by
   have k := congrArg Matrix.det (mul A)
   rw [Matrix.det_mul, show ((f A).map (Int.castRingHom ℝ)).det = ((f A).det : ℝ) from ((Int.castRingHom ℝ).map_det _).symm, Matrix.det_smul, hdet A A.property] at k; exact k
 obtain he | ⟨A,hA⟩ := S.eq_empty_or_nonempty
 · subst S; simp only [Finset.card_empty,Nat.cast_zero]; positivity
 let B : S := ⟨A,hA⟩
 have hu : (f B).det ≠ 0 := by intro h; have k := det B; rw [h,Int.cast_zero,zero_mul] at k; exact (mul_ne_zero (pow_ne_zero _ hm.ne') ht) k.symm
 have hpos : 0 ≤ X := le_trans zero_le_one hX
 have count := hanis (radius X ℓ) (f B).det (Finset.univ.image f)
   (ZpM X ℓ hpos hℓ hb.Znf) (Zng X ℓ hℓ hX' 2) hu (by
    rintro _ h; obtain ⟨C,_,rfl⟩ := Finset.mem_image.mp h
    refine ⟨by exact_mod_cast mul_right_cancel₀ (abs_pos.mp hd) ((det C).trans (det B).symm), ?_⟩
    intro j
    apply (ZeZ.ZcG _ (8*X/ℓ j) (by positivity) ?_).trans
    · norm_num [radius, ← mul_div_assoc]; apply div_le_div_of_nonneg_right _ (hℓ j).le
      have hs : Real.sqrt 3 ≤ 2 := by norm_num [Real.sqrt_le_iff]
      nlinarith [mul_le_mul_of_nonneg_right hs (show 0 ≤ 8*X by positivity)]
    intro i
    let u := ((m:ℝ) • C.val) i
    have e : ∑ k, (f C i k : ℝ) • V k = u := by
      ext k; simpa [Matrix.mul_apply,u] using congrFun (congrFun (mul C) i) k
    let U := V.updateRow j u
    let : Fact (finrank ℝ E = 3) := ⟨by simp [E]⟩
    have k := o.toBasis.orientation.abs_volumeForm_apply_le (fun i => WithLp.toLp 2 (U i))
    rw [o.toBasis.orientation.volumeForm_robust' o, detRows, show U.det = (f C i j : ℝ)*V.det by
      dsimp only [U]; rw [← e,Matrix.det_updateRow_sum,smul_eq_mul], abs_mul] at k
    have eqn : (fun i => ‖(WithLp.toLp 2 (U i) : E)‖) = Function.update ℓ j ‖(m:ℝ) • row C i‖ := by
      funext l; by_cases h : l = j
      · subst l; rw [Function.update_self]; dsimp only [U]; rw [Matrix.updateRow_self]; rfl
      · rw [Function.update_of_ne h]; dsimp only [U]; rw [Matrix.updateRow_ne h]
    rw [eqn,Finset.prod_update_of_mem (Finset.mem_univ j),Finset.sdiff_singleton_eq_erase,
      norm_smul,Real.norm_eq_abs,abs_of_pos hm] at k
    apply (le_div_iff₀ (hℓ j)).mpr
    apply (mul_le_mul_iff_left₀ hd).mp
    calc
      _ = (|(f C i j : ℝ)| * |V.det|) * ℓ j := by ring
      _ ≤ ((m:ℝ) * ‖row C i‖) * (∏ l ∈ Finset.univ.erase j, ℓ l) * ℓ j := by gcongr
      _ = (m:ℝ) * ‖row C i‖ * ∏ l, ℓ l := by rw [mul_assoc, mul_comm _ (ℓ j),Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
      _ ≤ (m:ℝ)*X*(8*ZLattice.covolume L) := by gcongr; exact hnorm C C.property i
      _ = _ := by rw [← ratio]; ring)
 rw [Finset.card_image_of_injective _ inj] at count
 let : Fact (finrank ℝ E = 3) := ⟨by simp [E]⟩
 have had := o.toBasis.orientation.abs_volumeForm_apply_le (fun i => WithLp.toLp 2 (V i))
 rw [o.toBasis.orientation.volumeForm_robust' o, detRows] at had
 have hm1 : 1 ≤ m := by exact_mod_cast (show 0 < m by exact_mod_cast hm)
 have hlower : ZLattice.covolume L ≤ ∏ i, ℓ i := by
   apply le_trans _ had
   rw [← ratio]; exact le_mul_of_one_le_left hI.le (by exact_mod_cast hm1)
 have bound := ZjE X _ ℓ hX hI h1 hX' hlower
 simp only [Finset.card_univ,Fintype.card_coe,mul_assoc] at count
 apply count.trans
 convert mul_le_mul_of_nonneg_left bound ha using 1 <;> ring
lemma Zln (L : Submodule ℤ E)
  (b : Basis (Fin 3) ℝ E) (hb : ZbJ.Zdt L b)
  (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.det ≠ 0)
  (hrows : ∀ i, (WithLp.toLp 2 (A i) : E) ∈ L)
  (X : ℝ) (hnorm : ∀ i, ‖(WithLp.toLp 2 (A i) : E)‖ ≤ X) :
  ‖b 2‖ ≤ X := by
 classical
 let v : Fin 3 → E := fun i => WithLp.toLp 2 (A i)
 have hv : LinearIndependent ℝ v := by
  convert! (Matrix.linearIndependent_rows_of_det_ne_zero hA).map'
    (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.injective) using 1
 let c : Basis (Fin 3) ℝ E :=
  basisOfLinearIndependentOfCardEqFinrank' v hv (by simp [E])
 let W := Submodule.span ℝ (ZbJ.ZlZ b 2)
 have hbW : b 2 ∉ W :=
  hb.independent.notMem_span_image (by simp)
 have hex : ∃ i, v i ∉ W := by
  by_contra h
  have hall : ∀ i, v i ∈ W := by simpa using h
  have hle : Submodule.span ℝ (Set.range c) ≤ W := by
   apply Submodule.span_le.mpr
   rintro _ ⟨i, rfl⟩
   convert! hall i using 1
   exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' v hv (by simp [E])) i
  rw [c.span_eq] at hle
  exact hbW (hle (by trivial))
 obtain ⟨i, hi⟩ := hex
 exact (hb.minimal 2 (v i) (hrows i) hi).trans (hnorm i)
theorem ZgS
   (a : ℝ) (ha : 0 ≤ a) (hanis : ZaS.ZbP a)
   (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
   (hunit : ∀ x ∈ L, x ≠ 0 → 1 ≤ ‖x‖)
   (X : ℝ) (hX : 1 ≤ X)
   (S : Finset (Matrix (Fin 3) (Fin 3) ℝ))
   (hrows : ∀ A ∈ S, ∀ i, (WithLp.toLp 2 (A i) : E) ∈ L)
   (hnorm : ∀ A ∈ S, ∀ i, ‖(WithLp.toLp 2 (A i) : E)‖ ≤ X)
   (t : ℝ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
   (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
    ZLattice.covolume L ^ 2 := by
 classical
 by_cases hS : S.Nonempty
 · obtain ⟨A, hA⟩ := hS
   have hex : ∃ b : Basis (Fin 3) ℝ E, ZbJ.Zdt L b := by
    obtain ⟨v, hv⟩ := ZbJ.ZoF L 3 (by simp [E])
    refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hv.independent (by simp [E]), ?_⟩
    simpa only [coe_basisOfLinearIndependentOfCardEqFinrank'] using hv
   obtain ⟨b, hb⟩ := hex
   have hlast : ‖b 2‖ ≤ X :=
    Zln L b hb A (by simpa only [hdet A hA] using ht)
     (hrows A hA) X (hnorm A hA)
   exact Zfc a ha hanis L hunit b hb X hX hlast
    S hrows hnorm t ht hdet
 · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
   rw [hempty]
   simp only [Finset.card_empty, Nat.cast_zero]
   positivity
theorem ZkM
   (a : ℝ) (ha : 0 ≤ a) (hanis : ZaS.ZbP a)
   (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
   (hunit : ∀ x ∈ L, x ≠ 0 → 1 ≤ ‖x‖)
   (X : ℝ) (hX : 1 ≤ X)
   (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
   (hrows : ∀ A ∈ S, ∀ i, (WithLp.toLp 2 (fun j => (A i j : ℝ)) : E) ∈ L)
   (hnorm : ∀ A ∈ S, ∀ i, ‖(WithLp.toLp 2 (fun j => (A i j : ℝ)) : E)‖ ≤ X)
   (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
   (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
    ZLattice.covolume L ^ 2 := by
 classical
 let f : Matrix (Fin 3) (Fin 3) ℤ → Matrix (Fin 3) (Fin 3) ℝ :=
   fun A => A.map (Int.castRingHom ℝ)
 have hf : Function.Injective f := by
   intro A B h
   ext i j
   have hh := congrArg (fun C => C i j) h
   change (A i j : ℝ) = (B i j : ℝ) at hh
   exact_mod_cast hh
 have hcard : (S.image f).card = S.card := Finset.card_image_of_injective S hf
 rw [← hcard]
 refine ZgS a ha hanis L hunit X hX (S.image f) ?_ ?_ (t : ℝ)
   (by exact_mod_cast ht) ?_
 · intro A hA i
   obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
   exact hrows B hB i
 · intro A hA i
   obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
   exact hnorm B hB i
 · intro A hA
   obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
   change (B.map (Int.castRingHom ℝ)).det = (t : ℝ)
   have hd := (Int.castRingHom ℝ).map_det B
   change (B.det : ℝ) = (B.map (Int.castRingHom ℝ)).det at hd
   rw [← hd, hdet B hB]
end Problem355.ZkX
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Ze
open Module MeasureTheory
instance ZqG : IsZLattice ℝ ZE := by
 unfold ZE
 infer_instance
lemma ZoH (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
  (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
  Submodule.span ℝ (Zaw L : Set ZI) = ⊤ := by
 apply top_unique
 rw [← stdBasis.span_eq]
 apply Submodule.span_le.mpr
 rintro v ⟨i, rfl⟩
 have hi : Zp (Pi.single i 1) = stdBasis i := by
  ext j
  simp [Zp, stdBasis, EuclideanSpace.basisFun_apply, Pi.single_apply]
 have hm : E • stdBasis i ∈ Zaw L := by
  refine ⟨E • Pi.single i 1, hL _, ?_⟩
  rw [map_smul]
  exact congrArg (fun u : ZI => E • u) hi
 have hs : (E : ℝ) • stdBasis i ∈ Submodule.span ℝ (Zaw L : Set ZI) := by
  rw [Int.cast_smul_eq_zsmul ℝ]
  exact Submodule.subset_span hm
 exact (Submodule.smul_mem_iff _ (by exact_mod_cast hE : (E : ℝ) ≠ 0)).mp hs
lemma ZfH (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
  (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) : IsZLattice ℝ (Zaw L) :=
 ⟨ZoH L E hE hL⟩
lemma Zki : ZLattice.covolume ZE = 1 := by
 rw [ZLattice.covolume_eq_measure_fundamentalDomain ZE volume
  (ZSpan.isAddFundamentalDomain stdBasis volume)]
 rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped stdBasis volume)]
 change (volume (parallelepiped (EuclideanSpace.basisFun (Fin 3) ℝ))).toReal = 1
 rw [OrthonormalBasis.volume_parallelepiped]
 simp
lemma ZmN (L : Submodule ℤ (Fin 3 → ℤ)) :
  (Zaw L).toAddSubgroup.relIndex ZE.toAddSubgroup =
   L.toAddSubgroup.index := by
 rw [← ZgQ]
 change (L.toAddSubgroup.map ZjC.toAddMonoidHom).relIndex
   ((⊤ : AddSubgroup (Fin 3 → ℤ)).map ZjC.toAddMonoidHom) = _
 rw [AddSubgroup.relIndex_map_map_of_injective _ _ ZgP]
 simp
lemma Zfs (v : ZI) (hv : v ∈ ZE)
  (hv0 : v ≠ 0) : 1 ≤ ‖v‖ := by
 have hi : ∃ i, v i ≠ 0 := by
  by_contra h
  apply hv0
  ext i
  exact not_not.mp (fun hn => h ⟨i, hn⟩)
 obtain ⟨i, hi⟩ := hi
 obtain ⟨z, hz⟩ := (Zeq v).mp hv i
 have hz0 : z ≠ 0 := by
  intro h
  apply hi
  simpa [h] using hz.symm
 have ha : (1 : ℝ) ≤ |(z : ℝ)| := by
  exact_mod_cast Int.one_le_abs hz0
 calc
  (1 : ℝ) ≤ |v i| := by simpa [hz] using ha
  _ ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
lemma ZgT (L : Submodule ℤ (Fin 3 → ℤ))
  (v : ZI) (hv : v ∈ Zaw L) (hv0 : v ≠ 0) : 1 ≤ ‖v‖ :=
 Zfs v (ZbM L hv) hv0
lemma ZmO (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
  (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
  ZLattice.covolume (Zaw L) = (L.toAddSubgroup.index : ℝ) := by
 let := ZfH L E hE hL
 have h := ZLattice.covolume_div_covolume_eq_relIndex'
  (Zaw L) ZE (ZbM L)
 simpa [Zki, ZmN] using h
end Problem355.Ze
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZhH
open Ze
theorem ZgS
  (a : ℝ) (ha : 0 ≤ a) (hanis : ZaS.ZbP a)
  (L : Submodule ℤ (Fin 3 → ℤ)) (m : ℤ) (hm : m ≠ 0)
  (hL : ∀ v, m • v ∈ L)
  (X : ℝ) (hX : 1 ≤ X) (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
  (hrows : ∀ A ∈ S, ∀ i, A i ∈ L)
  (hnorm : ∀ A ∈ S, ∀ i, ‖Zp (A i)‖ ≤ X)
  (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
  (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
   (L.toAddSubgroup.index : ℝ) ^ 2 := by
 let := ZfH L m hm hL
 have h := ZkX.ZkM a ha hanis (Zaw L)
  (ZgT L) X hX S
  (fun A hA i => ⟨A i, hrows A hA i, rfl⟩) hnorm t ht hdet
 rw [ZmO L m hm hL] at h
 exact h
end Problem355.ZhH
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZP
open Matrix
open scoped BigOperators Matrix
abbrev Zi := Matrix (Fin 3) (Fin 3) ℤ
def Zdu (A : Zi) : Anisotropic.Triple :=
 (A.col 0, A.col 1, A.col 2)
lemma Zlo : Function.Injective Zdu := by
 intro A B h
 have h0 := congrArg Prod.fst h
 have h1 := congrArg (fun x : Anisotropic.Triple => x.2.1) h
 have h2 := congrArg (fun x : Anisotropic.Triple => x.2.2) h
 ext i j
 fin_cases j
 · exact congrFun h0 i
 · exact congrFun h1 i
 · exact congrFun h2 i
lemma Zpk (A : Zi) :
  (Zdu A).1 ⬝ᵥ ((Zdu A).2.1 ⨯₃ (Zdu A).2.2) = A.det := by
 simp [Zdu, Matrix.det_fin_three, dotProduct, Fin.sum_univ_succ,
  crossProduct, Matrix.col]
 ring
def ZbQ : ℝ := 35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2
lemma Zfn : 0 < ZbQ :=
 Anisotropic.Zkg
theorem ZgU :
  ZaS.ZbP ZbQ := by
 classical
 intro r u T hr hr2 hu hT
 have hcount := Anisotropic.ZoG (T.image Zdu) u hu
  (r 0) (r 1) (r 2) hr2 (hr (by decide : (1 : Fin 3) ≤ 2))
  (hr (by decide : (0 : Fin 3) ≤ 1))
  (by
   intro x hx
   obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
   rw [Zpk]
   exact (hT A hA).1)
  (by
   intro x hx
   obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
   exact ⟨(hT A hA).2 0, (hT A hA).2 1, (hT A hA).2 2⟩)
 simpa [ZbQ, Finset.card_image_of_injective _ Zlo,
  Fin.prod_univ_succ, mul_assoc] using hcount
def Zbi : ℝ := ZbQ * 1000 ^ 6 * 144
lemma ZhD : 0 < Zbi := by
 unfold Zbi
 exact mul_pos (mul_pos Zfn (by positivity)) (by norm_num)
theorem ZqH
  (L : Submodule ℤ (Fin 3 → ℤ)) (m : ℤ) (hm : m ≠ 0)
  (hL : ∀ v, m • v ∈ L)
  (X : ℝ) (hX : 1 ≤ X) (S : Finset Zi)
  (hrows : ∀ A ∈ S, ∀ i, A i ∈ L)
  (hnorm : ∀ A ∈ S, ∀ i, ‖Ze.Zp (A i)‖ ≤ X)
  (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
  (S.card : ℝ) ≤ Zbi * Real.log (2 * X) ^ 2 * X ^ 6 /
   (L.toAddSubgroup.index : ℝ) ^ 2 :=
 ZhH.ZgS ZbQ Zfn.le
  ZgU L m hm hL X hX S hrows hnorm t ht hdet
theorem Zlp
  (L : Submodule ℤ (Fin 3 → ℤ)) (m : ℤ) (hm : m ≠ 0)
  (hL : ∀ v, m • v ∈ L)
  (X : ℝ) (hX : 1 ≤ X) (S : Finset Zi)
  (hrows : ∀ A ∈ S, ∀ i, A i ∈ L)
  (hnorm : ∀ A ∈ S, ∀ i, ‖Ze.Zp (A i)‖ ≤ X)
  (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t)
  (W : Zi → ℝ) (w : ℝ) (hw : 0 ≤ w)
  (hW : ∀ A ∈ S, W A ≤ w) :
  (∑ A ∈ S, W A) ≤ (w * Zbi) * Real.log (2 * X) ^ 2 * X ^ 6 /
   (L.toAddSubgroup.index : ℝ) ^ 2 := by
 calc
  (∑ A ∈ S, W A) ≤ ∑ _A ∈ S, w := Finset.sum_le_sum hW
  _ = w * (S.card : ℝ) := by simp [mul_comm]
  _ ≤ w * (Zbi * Real.log (2 * X) ^ 2 * X ^ 6 /
    (L.toAddSubgroup.index : ℝ) ^ 2) :=
   mul_le_mul_of_nonneg_left (ZqH L m hm hL X hX S hrows hnorm t ht hdet) hw
  _ = _ := by ring
def Zcw : ℝ := Zbi * 144 * 4 ^ 6
lemma ZkW : 0 < Zcw := by
 unfold Zcw
 exact mul_pos (mul_pos ZhD (by norm_num)) (by positivity)
theorem Zoc
  (L : Submodule ℤ (Fin 3 → ℤ)) (m : ℤ) (hm : m ≠ 0)
  (hL : ∀ v, m • v ∈ L)
  (N : ℝ) (hN : 1 ≤ N) (S : Finset Zi)
  (hrows : ∀ A ∈ S, ∀ i, A i ∈ L)
  (hnorm : ∀ A ∈ S, ∀ i, ‖Ze.Zp (A i)‖ ≤ 4 * N)
  (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t)
  (W : Zi → ℝ) (w : ℝ) (hw : 0 ≤ w)
  (hW : ∀ A ∈ S, W A ≤ w) :
  (∑ A ∈ S, W A) ≤ (w * Zcw) * Real.log (2 * N) ^ 2 * N ^ 6 /
   (L.toAddSubgroup.index : ℝ) ^ 2 := by
 have hcount := Zlp L m hm hL (4 * N) (by linarith)
  S hrows hnorm t ht hdet W w hw hW
 have hlog := ZaS.Zkh N (4 * N) hN
  (by linarith) (by nlinarith)
 have hlog0 : 0 ≤ Real.log (2 * (4 * N)) := Real.log_nonneg (by linarith)
 have hlog2 := pow_le_pow_left₀ hlog0 hlog 2
 have hfactor : 0 ≤ w * Zbi := mul_nonneg hw ZhD.le
 calc
  (∑ A ∈ S, W A) ≤ _ := hcount
  _ ≤ (w * Zbi) * (12 * Real.log (2 * N)) ^ 2 * (4 * N) ^ 6 /
    (L.toAddSubgroup.index : ℝ) ^ 2 := by
   exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
     (mul_le_mul_of_nonneg_left hlog2 hfactor) (by positivity)) (sq_nonneg _)
  _ = _ := by unfold Zcw; ring
lemma ZmP (A : Zi) (N : ℝ) (hN : 0 ≤ N)
  (hbox : ∀ j, Homogeneous.ZaX N (fun i => (A i j : ℝ))) (i : Fin 3) :
  ‖Ze.Zp (A i)‖ ≤ 4 * N := by
 have hcoord : ∀ j, |(Ze.Zp (A i)) j| ≤ 2 * N := by
  intro j
  have hj := hbox j
  fin_cases i
  · change |(A 0 j : ℝ)| ≤ 2 * N
    rw [abs_of_nonneg hj.1]
    linarith [hj.2.1]
  · change |(A 1 j : ℝ)| ≤ 2 * N
    rw [abs_of_nonneg hj.2.2.1]
    linarith [hj.2.2.2.1]
  · change |(A 2 j : ℝ)| ≤ 2 * N
    rw [abs_of_nonneg (hN.trans hj.2.2.2.2.1)]
    exact hj.2.2.2.2.2.le
 have h := ZeZ.ZcG
  (Ze.Zp (A i)) (2 * N) (by positivity) hcoord
 have hs : Real.sqrt (3 : ℝ) ≤ 2 := by norm_num [Real.sqrt_le_iff]
 simp only [Fintype.card_fin] at h
 apply h.trans
 calc
  Real.sqrt (3 : ℝ) * (2 * N) ≤ 2 * (2 * N) :=
    mul_le_mul_of_nonneg_right hs (by positivity)
  _ = 4 * N := by ring
theorem ZdO
  (B k b e : ℕ) (hB : 0 < B) (hb : b ≤ k) (he : e ≤ k) (hbe : b ≤ e)
  (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
  (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
  (hC : C = (P : Matrix _ _ _) *
   ZaG.Zad (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
    (Q : Matrix _ _ _))
  (N : ℝ) (hN : 1 ≤ N) (S : Finset Zi)
  (horbit : ∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
   ZS.Zbl C)
  (hbox : ∀ A ∈ S, ∀ j, Homogeneous.ZaX N (fun i => (A i j : ℝ)))
  (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t)
  (W : Zi → ℝ) (w : ℝ) (hw : 0 ≤ w)
  (hW : ∀ A ∈ S, W A ≤ w) :
  (∑ A ∈ S, W A) ≤ (w * Zcw) * Real.log (2 * N) ^ 2 * N ^ 6 /
   ((B : ℝ) ^ b * (B : ℝ) ^ e) ^ 2 := by
 let : NeZero B := ⟨ne_of_gt hB⟩
 let L := (Zah.ZZ (B ^ k) C).toIntSubmodule
 have hL : ∀ v, (B ^ e : ℤ) • v ∈ L := by
  intro v
  change (B ^ e : ℤ) • v ∈ Zah.ZZ (B ^ k) C
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact Zah.ZbK B k b e hbe C P Q hC v
 have hm : (B ^ e : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero e (ne_of_gt hB)
 have hc := Zoc L (B ^ e : ℤ) hm hL N hN S
  (fun A hA i => ZeB.ZaV
   (B ^ k) C A (horbit A hA) i)
  (fun A hA i => ZmP A N (by linarith) (hbox A hA) i)
  t ht hdet W w hw hW
 have hi : L.toAddSubgroup.index = B ^ b * B ^ e :=
  Zah.Zce B k b e hb he C P Q hC
 simpa only [hi, Nat.cast_mul, Nat.cast_pow] using hc
end Problem355.ZP
end
end OAI
end
section
namespace OAI
namespace Problem355.Znn
open scoped BigOperators
section Action
variable {G X : Type*} [Group G] [Fintype G] [finiteAction : Fintype X] [DecidableEq X]
 [MulAction G X] [MulAction.IsPretransitive G X]
theorem ZnE {G X : Type*} [Group G] [Fintype G] [Fintype X]
  [DecidableEq X] [MulAction G X] [MulAction.IsPretransitive G X] (x y z : X) :
  Fintype.card {g : G // g • x = y} =
    Fintype.card {g : G // g • x = z} := by
 classical
 obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G y z
 apply Fintype.card_congr
 exact
  { toFun := fun g => ⟨h * g.1, by rw [mul_smul, g.2, hh]⟩
    invFun := fun g => ⟨h⁻¹ * g.1, by
     rw [mul_smul, g.2, ← hh, inv_smul_smul]⟩
    left_inv := fun g => by ext; simp
    right_inv := fun g => by ext; simp }
theorem ZqI (x : X) (S : Finset X) :
  (Finset.univ.filter (fun g : G => g • x ∈ S)).card * Fintype.card X =
   Fintype.card G * S.card := by
 classical
 let c := (Finset.univ.filter (fun g : G => g • x = x)).card
 have hc (y : X) :
   (Finset.univ.filter (fun g : G => g • x = y)).card = c := by
  simpa only [Fintype.card_subtype] using ZnE (G := G) x y x
 have hs := Finset.sum_card_fiberwise_eq_card_filter
  (Finset.univ : Finset G) S (fun g => g • x)
 simp_rw [hc] at hs
 simp only [Finset.sum_const, smul_eq_mul] at hs
 have ht := Finset.sum_card_fiberwise_eq_card_filter
  (Finset.univ : Finset G) (Finset.univ : Finset X) (fun g => g • x)
 simp_rw [hc] at ht
 simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ,
  Finset.mem_univ, Finset.filter_true] at ht
 rw [← hs, ← ht]
 ring
theorem Zpl (x : X) (S : Finset X) :
  ((Finset.univ.filter (fun g : G => g • x ∈ S)).card : ℝ) /
   Fintype.card G = (S.card : ℝ) / Fintype.card X := by
 classical
 let : Nonempty X := ⟨x⟩
 have hG : (Fintype.card G : ℝ) ≠ 0 := by positivity
 have hX : (Fintype.card X : ℝ) ≠ 0 := by positivity
 apply (div_eq_div_iff hG hX).2
 exact_mod_cast (ZqI (G := G) x S).trans (Nat.mul_comm _ _)
end Action
section Conditioning
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
theorem Zlq (A E : Finset Ω) (hA : A.Nonempty)
  (K : ℝ) (hsize : (Fintype.card Ω : ℝ) ≤ K * A.card) :
  ((A ∩ E).card : ℝ) / A.card ≤
   K * ((E.card : ℝ) / Fintype.card Ω) := by
 let : Nonempty Ω := ⟨hA.choose⟩
 have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
 have hNp : (0 : ℝ) < Fintype.card Ω := by positivity
 have hi : ((A ∩ E).card : ℝ) ≤ E.card := by
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : A ∩ E ⊆ E)
 have h1 := mul_le_mul_of_nonneg_right hi hNp.le
 have h2 := mul_le_mul_of_nonneg_left hsize (show (0 : ℝ) ≤ E.card by positivity)
 rw [← mul_div_assoc]
 apply (div_le_div_iff₀ hAp hNp).2
 nlinarith
theorem ZiX (A E : Finset Ω) (hA : A.Nonempty)
  (hsize : Fintype.card Ω ≤ 2 * A.card) :
  ((A ∩ E).card : ℝ) / A.card ≤
   2 * ((E.card : ℝ) / Fintype.card Ω) := by
 apply Zlq A E hA 2
 exact_mod_cast hsize
end Conditioning
variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
 [DecidableEq G] [DecidableEq X] [MulAction G X]
 [MulAction.IsPretransitive G X]
theorem Zit (x : X) (S : Finset X) (A : Finset G)
  (hA : A.Nonempty) (hsize : Fintype.card G ≤ 2 * A.card) :
  ((A.filter (fun g => g • x ∈ S)).card : ℝ) / A.card ≤
   2 * ((S.card : ℝ) / Fintype.card X) := by
 have h := ZiX A
  (Finset.univ.filter (fun g : G => g • x ∈ S)) hA hsize
 simpa only [Finset.inter_filter, Finset.inter_univ, Zpl] using h
open scoped Pointwise in
theorem Zgx (x : X) (S : Finset X) (A : Finset G)
  (hA : A.Nonempty) (hsize : Fintype.card G ≤ 2 * A.card) :
  ((A.filter (fun g => g⁻¹ • x ∈ S)).card : ℝ) / A.card ≤
   2 * ((S.card : ℝ) / Fintype.card X) := by
 have hAi : A⁻¹.Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨a⁻¹, Finset.inv_mem_inv ha⟩
 have h := Zit x S A⁻¹ hAi (by simpa using hsize)
 have hc : (A⁻¹.filter (fun g => g • x ∈ S)).card =
   (A.filter (fun g => g⁻¹ • x ∈ S)).card := by
  rw [← Finset.card_inv (A.filter (fun g => g⁻¹ • x ∈ S))]
  congr 1
  ext g
  simp
 simpa only [hc, Finset.card_inv] using h
end Problem355.Znn
end OAI
end
section
namespace OAI
namespace Problem355.ZR
open Affine
variable {F V P ι : Type*} [Field F] [AddCommGroup V] [Module F V]
theorem ZfI [Finite ι] {u v : ι → V}
  (hu : LinearIndependent F u) (hv : LinearIndependent F v) :
  ∃ g : V ≃ₗ[F] V, ∀ i, g (u i) = v i := by
 classical
 let f := hu.linearCombinationEquiv.symm.trans hv.linearCombinationEquiv
 let : FiniteDimensional F (Submodule.span F (Set.range u)) :=
  FiniteDimensional.span_of_finite F (Set.finite_range u)
 obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
 refine ⟨g, fun i => ?_⟩
 have hi := hg (hu.linearCombinationEquiv (Finsupp.single i 1))
 simpa [f] using hi.symm
instance Zrp :
  MulAction (V ≃ₗ[F] V) {u : ι → V // LinearIndependent F u} where
 smul g u := ⟨g ∘ u.1, u.2.map' g.toLinearMap (LinearMap.ker_eq_bot.mpr g.injective)⟩
 one_smul _ := rfl
 mul_smul _ _ _ := rfl
@[simp] theorem Zre
 (g : V ≃ₗ[F] V) (u : {u : ι → V // LinearIndependent F u}) (i : ι) :
 (g • u).1 i = g (u.1 i) := rfl
instance ZqR [Finite ι] :
  MulAction.IsPretransitive (V ≃ₗ[F] V) {u : ι → V // LinearIndependent F u} where
 exists_smul_eq u v := by
  obtain ⟨g, hg⟩ := ZfI u.2 v.2
  exact ⟨g, Subtype.ext (funext hg)⟩
theorem Zlr [Finite ι] [AffineSpace V P]
   {p q : ι → P} (hp : AffineIndependent F p) (hq : AffineIndependent F q)
   (i0 : ι) : ∃ g : P ≃ᵃ[F] P, ∀ i, g (p i) = q i := by
 classical
 have hp' := (affineIndependent_iff_linearIndependent_vsub F p i0).mp hp
 have hq' := (affineIndependent_iff_linearIndependent_vsub F q i0).mp hq
 obtain ⟨g, hg⟩ := ZfI hp' hq'
 refine ⟨AffineEquiv.ofLinearEquiv g (p i0) (q i0), ?_⟩
 intro i
 by_cases hi : i = i0
 · subst i
   simp [AffineEquiv.ofLinearEquiv_apply]
 · rw [AffineEquiv.ofLinearEquiv_apply, hg ⟨i, hi⟩]
   exact vsub_vadd (q i) (q i0)
instance Zrq [AffineSpace V P] :
  MulAction (P ≃ᵃ[F] P) {p : ι → P // AffineIndependent F p} where
 smul g p := ⟨g ∘ p.1, g.affineIndependent_iff.mpr p.2⟩
 one_smul _ := rfl
 mul_smul _ _ _ := rfl
@[simp] theorem Zls [AffineSpace V P]
 (g : P ≃ᵃ[F] P) (p : {p : ι → P // AffineIndependent F p}) (i : ι) :
 (g • p).1 i = g (p.1 i) := rfl
instance ZqS [Finite ι] [Nonempty ι] [AffineSpace V P] :
  MulAction.IsPretransitive (P ≃ᵃ[F] P) {p : ι → P // AffineIndependent F p} where
 exists_smul_eq p q := by
  classical
  obtain ⟨g, hg⟩ := Zlr p.2 q.2 (Classical.arbitrary ι)
  exact ⟨g, Subtype.ext (funext hg)⟩
noncomputable def ZF :
  (V ≃ᵃ[F] V) ≃ (V ≃ₗ[F] V) × V where
 toFun e := (e.linear, e.linear.symm (e 0))
 invFun u := AffineEquiv.ofLinearEquiv u.1 0 (u.1 u.2)
 left_inv e := by
  apply AffineEquiv.ext
  intro x
  simp only [AffineEquiv.ofLinearEquiv_apply, vsub_eq_sub, sub_zero,
    vadd_eq_add, LinearEquiv.apply_symm_apply]
  simpa using (e.map_vadd 0 x).symm
 right_inv u := by
  apply Prod.ext
  · rfl
  · simp [AffineEquiv.ofLinearEquiv_apply]
@[simp] theorem ZiY (g : V ≃ₗ[F] V) (a x : V) :
  (ZF.symm (g, a)) x = g (a + x) := by
 simp [ZF, AffineEquiv.ofLinearEquiv_apply, map_add, add_comm]
noncomputable def ZjF (A : Set V) :
  {e : V ≃ᵃ[F] V // (ZF e).2 ∈ A} ≃ (V ≃ₗ[F] V) × A where
 toFun e := ((ZF e.1).1, ⟨(ZF e.1).2, e.2⟩)
 invFun u := ⟨ZF.symm (u.1, u.2.1), by simp⟩
 left_inv e := by
  apply Subtype.ext
  exact ZF.symm_apply_apply e.1
 right_inv u := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [ZF, AffineEquiv.ofLinearEquiv_apply]
theorem ZjG (A : Set V) :
  Nat.card {e : V ≃ᵃ[F] V // (ZF e).2 ∈ A} =
   Nat.card (V ≃ₗ[F] V) * Nat.card A := by
 rw [Nat.card_congr (ZjF A), Nat.card_prod]
theorem Zpm :
  Nat.card (V ≃ᵃ[F] V) = Nat.card (V ≃ₗ[F] V) * Nat.card V := by
 rw [Nat.card_congr (ZF (F := F) (V := V)), Nat.card_prod]
theorem Zft (A : Set V)
  (hA : Nat.card V ≤ 2 * Nat.card A) :
  Nat.card (V ≃ᵃ[F] V) ≤
   2 * Nat.card {e : V ≃ᵃ[F] V // (ZF e).2 ∈ A} := by
 rw [Zpm, ZjG]
 simpa [mul_assoc, mul_left_comm] using Nat.mul_le_mul_left (Nat.card (V ≃ₗ[F] V)) hA
end Problem355.ZR
end OAI
end
section
namespace OAI
open scoped BigOperators
namespace Problem355.Zhj
variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
theorem Zey {n : ℕ} (p : Fin (n+1) → V) :
  AffineIndependent K p ↔
   LinearIndependent K (fun i : Fin n => p i.succ - p 0) := by
 rw [affineIndependent_iff_linearIndependent_vsub K p 0]
 simpa [Function.comp_def, finSuccAboveEquiv_apply, Fin.succAbove_zero] using
  (linearIndependent_equiv (finSuccAboveEquiv (0 : Fin (n+1)))
   (f := fun i : {x : Fin (n+1) // x ≠ 0} => p i -ᵥ p 0)).symm
def Zpn (n : ℕ) :
  {p : Fin (n+1) → V // AffineIndependent K p} ≃
    V × {v : Fin n → V // LinearIndependent K v} where
 toFun p := (p.val 0, ⟨fun i => p.val i.succ - p.val 0,
  (Zey K V p.val).mp p.property⟩)
 invFun xv := ⟨Fin.cons xv.1 (fun i => xv.2.val i + xv.1), by
  apply (Zey K V _).mpr
  simpa using xv.2.property⟩
 left_inv p := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp
 right_inv xv := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    funext i
    simp
variable [Fintype K] [Finite V]
theorem Zlt {n : ℕ} (hn : n ≤ Module.finrank K V) :
  Nat.card {p : Fin (n+1) → V // AffineIndependent K p} =
   Nat.card V * ∏ i : Fin n,
    (Fintype.card K ^ Module.finrank K V - Fintype.card K ^ i.val) := by
 rw [Nat.card_congr (Zpn K V n), Nat.card_prod, card_linearIndependent hn]
end Problem355.Zhj
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZY
open scoped BigOperators
noncomputable local instance zCPD5 (p : Prop) : Decidable p := Classical.propDecidable p
section Families
variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]
theorem ZmQ (Q : (ι → V) → Prop) (S : Finset V) :
  Fintype.card {p : {v : ι → V // Q v} // ∀ i, p.1 i ∈ S} ≤
   S.card ^ Fintype.card ι := by
 let f : {p : {v : ι → V // Q v} // ∀ i, p.1 i ∈ S} → (ι → S) :=
  fun p i => ⟨p.1.1 i, p.2 i⟩
 have hf : Function.Injective f := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun hpq i)
 have h := Fintype.card_le_of_injective f hf
 simpa only [Fintype.card_fun, Fintype.card_coe] using h
end Families
section Affine
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
abbrev ZbW (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V] :=
 {p : ι → V // AffineIndependent K p}
end Affine
section AffineInverse
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
theorem ZeO [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq V] [Fintype (V ≃ᵃ[K] V)]
  (p : ZbW K V ι) (S : Finset V) (A : Finset (V ≃ᵃ[K] V))
  (hA : A.Nonempty) (hsize : Fintype.card (V ≃ᵃ[K] V) ≤ 2 * A.card) :
  ((A.filter (fun e => ∀ i, e.symm (p.1 i) ∈ S)).card : ℝ) / A.card ≤
   2 * ((S.card : ℝ) ^ Fintype.card ι /
    Nat.card (ZbW K V ι)) := by
 classical
 let T : Finset (ZbW K V ι) :=
  Finset.univ.filter (fun q => ∀ i, q.1 i ∈ S)
 have h := Znn.Zgx p T A hA hsize
 have hT : T.card ≤ S.card ^ Fintype.card ι := by
  simpa only [T, Fintype.card_subtype] using
   ZmQ (ι := ι) (AffineIndependent K) S
 have hTr : (T.card : ℝ) ≤ (S.card : ℝ) ^ Fintype.card ι := by
  exact_mod_cast hT
 calc
  _ ≤ 2 * ((T.card : ℝ) / Fintype.card (ZbW K V ι)) := by
   simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and,
    ZR.Zls, AffineEquiv.inv_def] using h
  _ ≤ _ := by
   rw [Nat.card_eq_fintype_card]
   exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hTr (by positivity)) (by norm_num)
end AffineInverse
section Linear
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
end Linear
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
 [Fintype V] [DecidableEq V] [Fintype (V ≃ᵃ[K] V)]
def ZbD (A : Finset V) : Finset (V ≃ᵃ[K] V) :=
 Finset.univ.filter (fun e => (ZR.ZF e).2 ∈ A)
theorem ZbX (A : Finset V)
  (hA : Fintype.card V ≤ 2 * A.card) :
  Fintype.card (V ≃ᵃ[K] V) ≤ 2 * (ZbD (K := K) A).card := by
 classical
 have h := ZR.Zft (F := K)
  (A : Set V) (by simpa [Nat.card_eq_fintype_card] using hA)
 simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
  Finset.mem_coe, ZbD] using h
theorem ZfJ (A : Finset V)
  (hA : Fintype.card V ≤ 2 * A.card) :
  (ZbD (K := K) A).Nonempty := by
 have h := ZbX (K := K) A hA
 have hp : 0 < Fintype.card (V ≃ᵃ[K] V) := Fintype.card_pos
 apply Finset.card_pos.mp
 omega
end Problem355.ZY
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZY
open scoped BigOperators
noncomputable local instance zCPD6 (p : Prop) : Decidable p := Classical.propDecidable p
theorem Zmb {Ω : Type*} (A : Finset Ω) (P : Ω → Prop) :
  (∑ a : A, (A.card : ℝ)⁻¹ * (if P a.1 then 1 else 0)) =
   ((A.filter P).card : ℝ) / A.card := by
 classical
 rw [Finset.sum_coe_sort A (fun a : Ω => (A.card : ℝ)⁻¹ * (if P a then 1 else 0)),
  ← Finset.mul_sum, Finset.sum_boole]
 ring
variable {K : Type*} [Field K] [Fintype K] [Fintype ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))]
def Zaa
  (S : Finset (Fin 3 → K))
  (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
  (p : Fin 3 → (Fin 3 → K)) : ℝ :=
 ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
  (((A.filter (fun e => ∀ i, e.symm (p i) ∈ S)).card : ℝ) / A.card)
theorem ZeP {K : Type*} [Field K] [Fintype K]
  [Fintype ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))]
  (S : Finset (Fin 3 → K))
  (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
  (p : Fin 3 → (Fin 3 → K)) :
  Zaa S A p =
    ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
     (∑ e : A, (A.card : ℝ)⁻¹ *
      (if ∀ i, p i ∈ S.image (fun x => e.1 x) then 1 else 0)) := by
 classical
 have he (e : (Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) :
    (∀ i, p i ∈ S.image e) ↔ (∀ i, e.symm (p i) ∈ S) := by
  constructor
  · intro h i
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp (h i)
    simpa only [← hxe, e.symm_apply_apply] using hx
  · intro h i
    exact Finset.mem_image.mpr ⟨e.symm (p i), h i, e.apply_symm_apply (p i)⟩
 have hf : A.filter (fun e : (Fin 3 → K) ≃ᵃ[K] (Fin 3 → K) =>
    ∀ i, p i ∈ S.image (fun x => e x)) =
    A.filter (fun e => ∀ i, e.symm (p i) ∈ S) := by
  ext e
  simp only [Finset.mem_filter, he]
 simp_rw [he]
 unfold Zaa
 congr 1
 convert (Zmb A
  (fun e : (Fin 3 → K) ≃ᵃ[K] (Fin 3 → K) =>
    ∀ i, e.symm (p i) ∈ S)).symm using 4 ; try simp
 ext e
 simp
private theorem Zod {n : ℕ} (hn : n ≤ 2)
  (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
  (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))) (hA : A.Nonempty)
  (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card)
  (p : Fin 3 → Fin 3 → K) (j : Fin (n+1) → Fin 3)
  (hj : AffineIndependent K (p ∘ j)) :
  Zaa S A p ≤ 2 ^ (n+1) * ((Fintype.card K : ℝ)^3 / S.card)^(2-n) := by
 classical
 let q := Fintype.card K
 let Q := q^3
 let d := Nat.card (ZbW K (Fin 3 → K) (Fin (n+1)))
 have hq : 2 ≤ q := Fintype.one_lt_card
 have hfac (i : Fin n) : Q ≤ 2 * (Q - q^i.val) := by
  have hi : i.val ≤ 1 := by omega
  have hpow := Nat.pow_le_pow_right (by omega : 0 < q) hi
  simp only [pow_one] at hpow
  dsimp [Q]; have := Nat.pow_le_pow_right (by omega : 0 < q) (by decide : 2 ≤ 3)
  nlinarith [Nat.sub_add_cancel (show q^i.val ≤ q^3 by nlinarith)]
 have hd : Q^(n+1) ≤ 2^n * d := by
  dsimp [d, ZbW]
  rw [Zhj.Zlt K (Fin 3 → K) (by simpa using hn.trans (by decide : 2 ≤ 3))]
  have ht := Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin n))) (fun i _ => hfac i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib] at ht
  simpa [Q, q, pow_succ, mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_right Q ht
 have hQ : 0 < Q := pow_pos (by omega : 0 < q) _
 have hd' : 0 < d := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hd; omega
 have hr : (Q : ℝ)^(n+1) ≤ 2^n * d := by exact_mod_cast hd
 have hs : (0:ℝ) < S.card := by exact_mod_cast hS.card_pos
 have hp := ZeO (⟨_, hj⟩ : ZbW K _ _) S A hA hsize
 change _ ≤ 2 * ((S.card : ℝ)^Fintype.card (Fin (n+1)) / d) at hp
 rw [Fintype.card_fin] at hp
 have hsub := Finset.card_le_card (show A.filter (fun e => ∀ i, e.symm (p i) ∈ S) ⊆ A.filter (fun e => ∀ i, e.symm ((⟨p ∘ j, hj⟩ : ZbW K _ _).1 i) ∈ S) from fun e he => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1, fun i => (Finset.mem_filter.mp he).2 (j i)⟩)
 unfold Zaa
 simp only [← Nat.cast_pow]
 change ((Q:ℝ) / S.card)^3 * _ ≤ _
 calc
  _ ≤ ((Q:ℝ) / S.card)^3 * (2 * ((S.card:ℝ)^(n+1) / d)) := by
   gcongr
   exact le_trans (div_le_div_of_nonneg_right (by convert (Nat.cast_le (α := ℝ)).mpr hsub using 2 <;> congr 1 <;> ext e <;> simp) (by positivity)) hp
  _ ≤ _ := by
   have hDr : (0:ℝ) < d := by exact_mod_cast hd'
   change _ ≤ 2^(n+1) * ((Q:ℝ)/S.card)^(2-n)
   have hQr : (0:ℝ) < Q := by exact_mod_cast hQ
   have hsplit : 3 = n+1+(2-n) := by omega
   rw [show ((Q:ℝ)/S.card)^3 = ((Q:ℝ)/S.card)^(n+1) * ((Q:ℝ)/S.card)^(2-n) by rw [← pow_add, ← hsplit], mul_right_comm]
   apply mul_le_mul_of_nonneg_right _ (by positivity)
   rw [div_pow]; field_simp; rw [pow_succ (2:ℝ)]; linarith
theorem ZcV
  (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
  (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))) (hA : A.Nonempty)
  (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card)
  (p : Fin 3 → (Fin 3 → K)) (hp : AffineIndependent K p) :
  Zaa S A p ≤ 8 := by
 simpa [show (2:ℝ)^3 = 8 by norm_num, show (2:ℝ)^2 = 4 by norm_num] using Zod (n := 2) (by decide) S hS A hA hsize p id hp
theorem Zfd
  (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
  (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))) (hA : A.Nonempty)
  (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card)
  (p : Fin 3 → (Fin 3 → K)) (i j : Fin 3) (hp : p i ≠ p j) :
  Zaa S A p ≤ 4 * ((Fintype.card K : ℝ) ^ 3 / S.card) := by
 have hj : AffineIndependent K (p ∘ ![i,j]) := by
  convert affineIndependent_of_ne K hp using 1; funext k; fin_cases k <;> rfl
 simpa [show (2:ℝ)^3 = 8 by norm_num, show (2:ℝ)^2 = 4 by norm_num] using Zod (n := 1) (by decide) S hS A hA hsize p ![i,j] hj
theorem ZhP
  (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
  (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))) (hA : A.Nonempty)
  (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card)
  (p : Fin 3 → (Fin 3 → K)) :
  Zaa S A p ≤ 2 * ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 2 := by
 simpa [show (2:ℝ)^3 = 8 by norm_num, show (2:ℝ)^2 = 4 by norm_num] using Zod (n := 0) (by decide) S hS A hA hsize p (fun _ => 0) (affineIndependent_of_subsingleton (ι := Fin 1) K _)
end Problem355.ZY
end
end OAI
end
section
namespace OAI
namespace Problem355.ZjT
end Problem355.ZjT
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zdi
theorem Zez {q : ℕ} {t : ℤ}
  (ht : t ≠ 0) (hsmall : |t| < (q : ℤ)) : (t : ZMod q) ≠ 0 := by
 intro hzero
 have hdvd : (q : ℤ) ∣ t := (ZMod.intCast_zmod_eq_zero_iff_dvd t q).mp hzero
 have hle := Int.le_abs_of_dvd ht hdvd
 omega
theorem ZpN {q : ℕ} (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hdet : A.det ≠ 0) (hsmall : |A.det| < (q : ℤ)) :
  (A.map (Int.castRingHom (ZMod q))).det ≠ 0 := by
 have hd := (Int.castRingHom (ZMod q)).map_det A
 change (A.det : ZMod q) = (A.map (Int.castRingHom (ZMod q))).det at hd
 rw [← hd]
 exact Zez hdet hsmall
theorem ZeA {q : ℕ} [Fact q.Prime]
  (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hdet : A.det ≠ 0) (hsmall : |A.det| < (q : ℤ)) :
  AffineIndependent (ZMod q) (fun j i => (A i j : ZMod q)) := by
 exact (Matrix.linearIndependent_cols_of_det_ne_zero
  (ZpN A hdet hsmall)).affineIndependent
theorem ZcW {q : ℕ} [Fact q.Prime]
  [Fintype ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q))]
  (S : Finset (Fin 3 → ZMod q)) (hS : S.Nonempty)
  (T : Finset ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)))
  (hT : T.Nonempty)
  (hsize : Fintype.card ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)) ≤
   2 * T.card)
  (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hdet : A.det ≠ 0) (hsmall : |A.det| < (q : ℤ)) :
  ZY.Zaa S T (fun j i => (A i j : ZMod q)) ≤ 8 :=
 ZY.ZcV S hS T hT hsize _
  (ZeA A hdet hsmall)
abbrev Space (q : ℕ) := Fin 3 → ZMod q
abbrev Zrf (q : ℕ) := Space q ≃ᵃ[ZMod q] Space q
variable (q : ℕ) [Fact q.Prime] [Fintype (Zrf q)]
end Problem355.Zdi
end
end OAI
end
section
namespace OAI
namespace Problem355.ZiF
variable {R : Type*} [CommRing R]
variable {m n : Type*}
def Zab (A : Matrix m n R) : Prop :=
 ∀ i k j l, A i j * A k l = A i l * A k j
end Problem355.ZiF
end OAI
end
section
namespace OAI
namespace Problem355.ZiF
open Matrix
variable {R : Type*} [CommRing R]
variable {m n l : Type*}
theorem Zab.mul_left [Fintype m]
  {A : Matrix m n R} (hA : Zab A) (P : Matrix l m R) :
  Zab (P * A) := by
 intro i k j t
 simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro a _
 apply Finset.sum_congr rfl
 intro b _
 calc
  (P i b * A b j) * (P k a * A a t) =
   (P i b * P k a) * (A b j * A a t) := by ring
  _ = (P i b * P k a) * (A b t * A a j) := by rw [hA b a j t]
  _ = (P i b * A b t) * (P k a * A a j) := by ring
theorem Zee (A : Matrix m n R) :
   Zab A.transpose ↔ Zab A := by
 constructor <;> intro h i k j t
 · simpa only [Matrix.transpose_apply, mul_comm] using h j t i k
 · simpa only [Matrix.transpose_apply, mul_comm] using h j t i k
theorem Zab.mul_right [Fintype n]
  {A : Matrix m n R} (hA : Zab A) (Q : Matrix n l R) :
  Zab (A * Q) := by
 apply (Zee _).mp
 rw [Matrix.transpose_mul]
 exact ((Zee A).mpr hA).mul_left Q.transpose
theorem ZjH [Fintype m] [DecidableEq m]
   (P : Matrix.GeneralLinearGroup m R) (A : Matrix m n R) :
   Zab ((P : Matrix m m R) * A) ↔ Zab A := by
 constructor
 · intro h
   have hh := h.mul_left (↑(P⁻¹) : Matrix m m R)
   simpa only [← Matrix.mul_assoc, P.inv_mul, Matrix.one_mul] using hh
 · exact fun h => h.mul_left _
theorem ZjI [Fintype n] [DecidableEq n]
   (A : Matrix m n R) (Q : Matrix.GeneralLinearGroup n R) :
   Zab (A * (Q : Matrix n n R)) ↔ Zab A := by
 constructor
 · intro h
   have hh := h.mul_right (↑(Q⁻¹) : Matrix n n R)
   simpa only [Matrix.mul_assoc, Q.mul_inv, Matrix.mul_one] using hh
 · exact fun h => h.mul_right _
theorem Ziu [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]
  (P : Matrix.GeneralLinearGroup m R) (Q : Matrix.GeneralLinearGroup n R)
  (A : Matrix m n R) :
  Zab ((P : Matrix m m R) * A * (Q : Matrix n n R)) ↔
   Zab A := by
 rw [ZjI, ZjH]
theorem Zgy (D E : R) :
   Zab (Matrix.diagonal ![1, D, E]) ↔ D = 0 ∧ E = 0 := by
 constructor
 · intro h
   exact ⟨by simpa using h 0 1 0 1, by simpa using h 0 2 0 2⟩
 · rintro ⟨rfl, rfl⟩ i k j l
   fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;> simp
theorem ZeH
  {S : Type*} [CommRing S] (f : R →+* S)
  (D E : R) (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
  (C : Matrix (Fin 3) (Fin 3) R)
  (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * Matrix.diagonal ![1, D, E] *
   (Q : Matrix (Fin 3) (Fin 3) R)) :
  Zab (C.map f) ↔ f D = 0 ∧ f E = 0 := by
 have hd : (Matrix.diagonal ![1, D, E]).map f = Matrix.diagonal ![1, f D, f E] := by
  rw [Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  fin_cases i <;> simp
 have hmap : C.map f =
   (Matrix.GeneralLinearGroup.map f P : Matrix (Fin 3) (Fin 3) S) *
    Matrix.diagonal ![1, f D, f E] *
    (Matrix.GeneralLinearGroup.map f Q : Matrix (Fin 3) (Fin 3) S) := by
  rw [hC, Matrix.map_mul, Matrix.map_mul]
  rw [hd]
  rfl
 rw [hmap, Ziu, Zgy]
theorem Zfe
  {p k b e j : ℕ} (hp : p.Prime) (hbe : b ≤ e) (hjk : j ≤ k)
  (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
  (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
  (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))) *
   Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)),
    ((p ^ e : ℕ) : ZMod (p ^ k))] *
   (Q : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))) :
  Zab (C.map (ZMod.castHom (Nat.pow_dvd_pow p hjk) (ZMod (p ^ j)))) ↔
   j ≤ b := by
 rw [ZeH _ _ _ P Q C hC]
 simp only [map_natCast, ZMod.natCast_eq_zero_iff,
  Nat.pow_dvd_pow_iff_le_right hp.one_lt]
 omega
end Problem355.ZiF
end OAI
end
section
namespace OAI
namespace Problem355.Zfy
theorem ZhE {p : ℕ} (hp : p.Prime) (k : ℕ)
  (x : ZMod (p ^ k)) :
  ∃ e ≤ k, ∃ u : (ZMod (p ^ k))ˣ,
   x = (p : ZMod (p ^ k)) ^ e * (u : ZMod (p ^ k)) := by
 obtain ⟨d, hd, v, hv, hx⟩ := ZMod.eq_unit_mul_divisor x
 obtain ⟨e, he, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
 obtain ⟨u, rfl⟩ := hv
 exact ⟨e, he, u, by simpa [Nat.cast_pow, mul_comm] using hx⟩
theorem ZjJ {ι : Type*} [Fintype ι] [Nonempty ι]
  {p : ℕ} (hp : p.Prime) (k : ℕ) (x : ι → ZMod (p ^ k)) :
  ∃ i : ι, ∃ e ≤ k, ∃ u : (ZMod (p ^ k))ˣ,
   x i = (p : ZMod (p ^ k)) ^ e * (u : ZMod (p ^ k)) ∧
   ∀ j, (p : ZMod (p ^ k)) ^ e ∣ x j := by
 classical
 choose e he u hu using fun i => ZhE hp k (x i)
 obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
 refine ⟨i, e i, he i, u i, hu i, ?_⟩
 intro j
 rw [hu j]
 exact dvd_mul_of_dvd_left (pow_dvd_pow _ (hmin j (Finset.mem_univ j))) _
end Problem355.Zfy
end OAI
end
section
namespace OAI
namespace Problem355.Zno
theorem Ziv {p : ℕ} (hp : p.Prime) (k : ℕ)
   (A : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k))) :
   ∃ b e : ℕ, b ≤ e ∧ e ≤ k ∧
     ∃ P Q : (Matrix (Fin 2) (Fin 2) (ZMod (p ^ k)))ˣ,
      A = (P : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k))) *
       Matrix.diagonal ![(p : ZMod (p ^ k)) ^ b, (p : ZMod (p ^ k)) ^ e] *
       (Q : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k))) := by
 classical
 let R := ZMod (p ^ k)
 obtain ⟨ij, b, hb, u, pivot, divides⟩ := Zfy.ZjJ hp k
   (fun ij : Fin 2 × Fin 2 => A ij.1 ij.2)
 let ZbZ := Equiv.swap 0 ij.1
 let cols := Equiv.swap 0 ij.2
 let block := A.submatrix ZbZ cols
 have h00 : block 0 0 = (p : R)^b * ↑u := by simpa [block, ZbZ, cols] using pivot
 have hd (i j) : (p : R)^b ∣ block i j := divides (ZbZ i, cols j)
 obtain ⟨s, hs⟩ := hd 0 1
 obtain ⟨t, ht⟩ := hd 1 0
 obtain ⟨w, hw⟩ := hd 1 1
 let upper : R := ↑u⁻¹ * s
 have hu : (u : R) * upper = s := by simp [upper, ← mul_assoc]
 obtain ⟨f, _, v, hv⟩ := Zfy.ZhE hp k (w - t * upper)
 let e := min (b + f) k
 have hpow : (p : R)^e = (p : R)^b * (p : R)^f := by
   rw [← pow_add]
   by_cases h : b + f ≤ k
   · simp [e, h]
   · have zero (n : ℕ) (hn : k ≤ n) : (p : R)^n = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; exact pow_dvd_pow _ hn
     simp [e, min_eq_right (by omega : k ≤ b + f), zero _ (le_refl k), zero _ (by omega : k ≤ b + f)]
 let L : Matrix (Fin 2) (Fin 2) R := !![↑u, 0; t, ↑v]
 let U : Matrix (Fin 2) (Fin 2) R := !![1, upper; 0, 1]
 have fac : block = L * Matrix.diagonal ![(p : R)^b, (p : R)^e] * U := by
   ext i j
   fin_cases i <;> fin_cases j <;>
     simp [L, U, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.diagonal_apply, h00, hs, ht, hw, hpow] <;>
     first | (solve | ring) | linear_combination -(p : R)^b * hu | linear_combination (p : R)^b * hv
 let S := ZbZ.permMatrix R
 let T := cols.permMatrix R
 have perms : S * block * T = A := by
   rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
   ext i j; simp [block, ZbZ, cols, Matrix.submatrix_apply]
 refine ⟨b, e, le_min (by omega) hb, min_le_right _ _,
   Matrix.GeneralLinearGroup.mk'' (S * L) ?_, Matrix.GeneralLinearGroup.mk'' (U * T) ?_, ?_⟩
 · rw [Matrix.det_mul]; apply IsUnit.mul
   · rw [Matrix.det_permutation]; exact (Equiv.Perm.sign ZbZ).isUnit.map (Int.castRingHom R)
   · simp [L, Matrix.det_fin_two]
 · rw [Matrix.det_mul]; apply IsUnit.mul
   · simp [U, Matrix.det_fin_two]
   · rw [Matrix.det_permutation]; exact (Equiv.Perm.sign cols).isUnit.map (Int.castRingHom R)
 · rw [← perms, fac]; simp [mul_assoc]
end Problem355.Zno
end OAI
end
section
namespace OAI
namespace Problem355.ZcS
open Matrix
variable {R : Type*} [CommRing R]
theorem Ziw
   (C : Matrix (Fin 3) (Fin 3) R) (h : IsUnit (C 0 0)) :
   ∃ P Q : Matrix (Fin 3) (Fin 3) R,
    IsUnit P.det ∧ IsUnit Q.det ∧
    ∃ a b c d : R, P * C * Q = !![1, 0, 0; 0, a, b; 0, c, d] := by
 obtain ⟨u, hu⟩ := h
 let v : R := ↑u⁻¹
 have huv : C 0 0 * v = 1 := by simp [v, ← hu]
 have hvu : v * C 0 0 = 1 := by simp [v, ← hu]
 have hvux (x : R) : v * (C 0 0 * x) = x := by rw [← mul_assoc, hvu, one_mul]
 let P : Matrix (Fin 3) (Fin 3) R :=
   !![v, 0, 0; -(C 1 0 * v), 1, 0; -(C 2 0 * v), 0, 1]
 let Q : Matrix (Fin 3) (Fin 3) R :=
   !![1, -(v * C 0 1), -(v * C 0 2); 0, 1, 0; 0, 0, 1]
 refine ⟨P, Q, ?_, ?_,
   C 1 1 - C 1 0 * v * C 0 1,
   C 1 2 - C 1 0 * v * C 0 2,
   C 2 1 - C 2 0 * v * C 0 1,
   C 2 2 - C 2 0 * v * C 0 2, ?_⟩
 · simp [P, v, Matrix.det_fin_three]
 · simp [Q, Matrix.det_fin_three]
 · ext i j
   fin_cases i <;> fin_cases j <;>
    simp [P, Q, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, add_mul,
     mul_assoc, hvu] <;> ring_nf <;>
    simp [pow_two, mul_assoc, hvux] <;> ring
def ZdP (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
 !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]
theorem ZqT (A B : Matrix (Fin 2) (Fin 2) R) :
  ZdP (A * B) = ZdP A * ZdP B := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp [ZdP, Matrix.mul_apply, Fin.sum_univ_succ]
theorem ZqU (A : Matrix (Fin 2) (Fin 2) R) :
  (ZdP A).det = A.det := by
 simp [ZdP, Matrix.det_fin_three, Matrix.det_fin_two]
theorem ZoI (a b : R) :
  ZdP (Matrix.diagonal ![a, b]) = Matrix.diagonal ![1, a, b] := by
 ext i j
 fin_cases i <;> fin_cases j <;> simp [ZdP, Matrix.diagonal]
end Problem355.ZcS
end OAI
end
section
namespace OAI
namespace Problem355
structure Zj (p k : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))) where
 b : ℕ
 e : ℕ
 b_le_e : b ≤ e
 e_le_k : e ≤ k
 left : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))
 right : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))
 diagonalization : C = (left : Matrix _ _ _) *
  Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)),
   ((p ^ e : ℕ) : ZMod (p ^ k))] * (right : Matrix _ _ _)
namespace Zj
variable {p k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))}
theorem Zpo (hp : p.Prime) (hunit : IsUnit (C 0 0)) :
  Nonempty (Zj p k C) := by
 obtain ⟨P, Q, hP, hQ, a, c, d, g, hblock⟩ := ZcS.Ziw C hunit
 let A := !![a, c; d, g]
 obtain ⟨b, e, hbe, hek, L, U, hA⟩ := Zno.Ziv hp k A
 let embed := ZcS.ZdP (R := ZMod (p ^ k))
 have lifted := congrArg embed hA
 change embed A = _ at lifted
 rw [show embed A = P * C * Q from hblock.symm] at lifted
 simp only [embed, ZcS.ZqT, ZcS.ZoI] at lifted
 obtain ⟨left, hl⟩ := (Matrix.isUnit_iff_isUnit_det P).2 hP
 obtain ⟨right, hr⟩ := (Matrix.isUnit_iff_isUnit_det Q).2 hQ
 let asUnit (V : Matrix.GeneralLinearGroup (Fin 2) (ZMod (p ^ k))) :=
  Matrix.GeneralLinearGroup.mk'' (embed V) (by
   rw [show (embed V).det = _ from ZcS.ZqU _]; exact Matrix.isUnits_det_units V)
 refine ⟨⟨b, e, hbe, hek, left⁻¹ * asUnit L, asUnit U * right⁻¹, ?_⟩⟩
 rw [← hl, ← hr] at lifted
 have eqn := congrArg (fun X : Matrix _ _ (ZMod (p ^ k)) => (↑left⁻¹ : Matrix _ _ _) * X * (↑right⁻¹ : Matrix _ _ _)) lifted
 simpa [asUnit, embed, Nat.cast_pow, ← mul_assoc] using eqn
noncomputable def ofUnit (hp : p.Prime) (hunit : IsUnit (C 0 0)) :
  Zj p k C :=
 Classical.choice (Zpo hp hunit)
lemma ZpO (d : Zj p k C) : d.b ≤ k :=
 d.b_le_e.trans d.e_le_k
theorem ZoJ (d : Zj p k C) (hp : p ≠ 0) :
  (Zah.ZZ (p ^ k) C).index = p ^ d.b * p ^ d.e := by
 let : NeZero p := ⟨hp⟩
 apply Zah.Zce p k d.b d.e
  d.ZpO d.e_le_k C d.left d.right
 simpa only [ZaG.Zad, Nat.cast_pow] using d.diagonalization
theorem Zkj (d : Zj p k C) (v : Fin 3 → ℤ) :
  (p ^ d.e) • v ∈ Zah.ZZ (p ^ k) C := by
 apply Zah.ZbK p k d.b d.e
  d.b_le_e C d.left d.right _ v
 simpa only [ZaG.Zad, Nat.cast_pow] using d.diagonalization
theorem ZoK (d : Zj p k C) (hp : p.Prime) (hk : 0 < k) :
  (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 8 /
   (((p ^ d.b : ℕ) : ℝ) ^ 3 * ((p ^ d.e : ℕ) : ℝ) ^ 2) ≤
    (Nat.card (ZS.Zbl C) : ℝ) :=
 ZS.Znv hp hk d.ZpO d.e_le_k
  C d.left d.right d.diagonalization
end Zj
end Problem355
end OAI
end
section
namespace OAI
namespace Problem355.Zac
variable {F : Type*} [Field F]
def ZhQ (η x y : F) : F := x ^ 2 - η * y ^ 2
theorem Zpp {η : F} (hη : ¬ IsSquare η) (x y : F) :
   ZhQ η x y = 0 ↔ x = 0 ∧ y = 0 := by
 constructor
 · intro h
   have hy : y = 0 := by
    by_contra hy
    apply hη
    refine ⟨x / y, ?_⟩
    have hxy : x ^ 2 = η * y ^ 2 := sub_eq_zero.mp h
    have heq : η = (x / y) ^ 2 := by
     rw [div_pow, eq_div_iff (pow_ne_zero 2 hy)]
     exact hxy.symm
    simpa [pow_two] using heq
   refine ⟨?_, hy⟩
   simpa [ZhQ, hy] using h
 · rintro ⟨rfl, rfl⟩
   simp [ZhQ]
def graph (η : F) : Set (Fin 3 → F) :=
 {p | p 2 = ZhQ η (p 0) (p 1)}
def Zcx (p q : Fin 3 → F) (t : F) : Fin 3 → F :=
 fun i => p i + t * (q i - p i)
theorem ZkN {η : F} (hη : ¬ IsSquare η)
   {p q : Fin 3 → F} (hp : p ∈ graph η) (hq : q ∈ graph η)
   (hpq : p ≠ q) (t : F) :
   Zcx p q t ∈ graph η ↔ t = 0 ∨ t = 1 := by
 constructor
 · intro ht
   have hqdiff : ZhQ η (q 0 - p 0) (q 1 - p 1) ≠ 0 := by
     intro hzero
     obtain ⟨hx, hy⟩ := (Zpp hη _ _).mp hzero
     have hx' : p 0 = q 0 := (sub_eq_zero.mp hx).symm
     have hy' : p 1 = q 1 := (sub_eq_zero.mp hy).symm
     apply hpq
     funext i
     fin_cases i
     · exact hx'
     · exact hy'
     · exact hp.trans ((congrArg₂ (ZhQ η) hx' hy').trans hq.symm)
   have hprod : t * (t - 1) * ZhQ η (q 0 - p 0) (q 1 - p 1) = 0 := by
     calc
       t * (t - 1) * ZhQ η (q 0 - p 0) (q 1 - p 1) =
        ZhQ η (Zcx p q t 0) (Zcx p q t 1) -
         Zcx p q t 2 := by
          change p 2 = ZhQ η (p 0) (p 1) at hp
          change q 2 = ZhQ η (q 0) (q 1) at hq
          dsimp [Zcx]
          rw [hp, hq]
          dsimp [ZhQ]
          ring
       _ = 0 := sub_eq_zero.mpr ht.symm
   rcases (mul_eq_zero.mp hprod).resolve_right hqdiff with h
   rcases mul_eq_zero.mp h with h | h
   · exact Or.inl h
   · exact Or.inr (sub_eq_zero.mp h)
 · rintro (rfl | rfl)
   · simpa [graph, Zcx] using hp
   · simpa [graph, Zcx] using hq
theorem ZmR (p q : Fin 3 → F) (t : F) :
  Zcx p q t = AffineMap.lineMap p q t := by
 ext i
 simp [Zcx, AffineMap.lineMap_apply, add_comm]
theorem ZnF {η : F} (hη : ¬ IsSquare η)
   {p q r : Fin 3 → F} (hp : p ∈ graph η) (hq : q ∈ graph η)
   (hr : r ∈ graph η) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
   ¬ Collinear F ({p, q, r} : Set (Fin 3 → F)) := by
 intro hcol
 have hrline := hcol.mem_affineSpan_of_mem_of_ne
   (by simp : p ∈ ({p, q, r} : Set (Fin 3 → F)))
   (by simp : q ∈ ({p, q, r} : Set (Fin 3 → F)))
   (by simp : r ∈ ({p, q, r} : Set (Fin 3 → F))) hpq
 obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hrline
 have htgraph : Zcx p q t ∈ graph η := by
   rw [ZmR, ht]
   exact hr
 rcases (ZkN hη hp hq hpq t).mp htgraph with ht0 | ht1
 · subst t
   exact hpr (by simpa using ht)
 · subst t
   exact hqr (by simpa using ht)
def Zbc (S : Set (Fin 3 → F)) : Prop :=
 ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
  ¬ Collinear F ({p, q, r} : Set (Fin 3 → F))
theorem Zbc.mono {S T : Set (Fin 3 → F)} (hS : Zbc S) (hTS : T ⊆ S) :
  Zbc T := by
 intro p hp q hq r hr hpq hpr hqr
 exact hS p (hTS hp) q (hTS hq) r (hTS hr) hpq hpr hqr
theorem Zbc.image {S : Set (Fin 3 → F)} (hS : Zbc S)
  (f : (Fin 3 → F) →ᵃ[F] (Fin 3 → F)) (hf : Function.Injective f) :
  Zbc (f '' S) := by
 rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ _ ⟨r, hr, rfl⟩ hpq hpr hqr
 have hcol := hS p hp q hq r hr
  (fun h => hpq (congrArg f h)) (fun h => hpr (congrArg f h))
  (fun h => hqr (congrArg f h))
 have hai := (affineIndependent_iff_not_collinear_set).mpr hcol
 have himage := hai.map' f hf
 apply (affineIndependent_iff_not_collinear_set).mp
 convert himage using 1
 funext i
 fin_cases i <;> rfl
theorem Zbc.translate {S : Set (Fin 3 → F)} (hS : Zbc S) (a : Fin 3 → F) :
  Zbc ((fun p => a + p) '' S) := by
 exact hS.image (AffineEquiv.constVAdd F (Fin 3 → F) a).toAffineMap
  (AffineEquiv.constVAdd F (Fin 3 → F) a).injective
theorem Zrg {η : F} (hη : ¬ IsSquare η) : Zbc (graph η) := by
 intro p hp q hq r hr hpq hpr hqr
 exact ZnF hη hp hq hr hpq hpr hqr
theorem ZpP {q w : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hw : w ≤ q) :
   ∃ S : Finset (Fin 3 → ZMod q), (∀ p ∈ S, (p 0).val < w) ∧
    S.card = w * q ∧ Zbc (S : Set (Fin 3 → ZMod q)) := by
 classical
 obtain ⟨η, hη⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by simpa only [ZMod.ringChar_zmod_n] using hq)
 let f (z : Fin w × ZMod q) : Fin 3 → ZMod q := ![(z.1.val : ZMod q), z.2, ZhQ η z.1.val z.2]
 have hf (z : Fin w × ZMod q) : (f z 0).val = z.1.val :=
   ZMod.val_natCast_of_lt (z.1.isLt.trans_le hw)
 refine ⟨Finset.univ.image f, ?_, ?_, (Zrg hη).mono ?_⟩
 · intro p hp; obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hp
   simpa [hf] using z.1.isLt
 · rw [Finset.card_image_of_injective _ (show Function.Injective f from fun x y h =>
    Prod.ext (Fin.ext ((hf x).symm.trans ((congrArg (fun p : Fin 3 → ZMod q => (p 0).val) h).trans (hf y)))) (congrFun h 1))]; simp
 · intro p hp; obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hp; rfl
end Problem355.Zac
end OAI
end
section
namespace OAI
namespace Problem355.Zmx
open scoped BigOperators
theorem Zez {q : ℕ} {x : ℤ}
  (hx : x ≠ 0) (hbound : |x| < (q : ℤ)) : (x : ZMod q) ≠ 0 := by
 intro hcast
 exact hx (Int.eq_zero_of_abs_lt_dvd
  ((ZMod.intCast_zmod_eq_zero_iff_dvd x q).1 hcast) hbound)
theorem Zgz
  {ι V : Type*} [Fintype ι] {q : ℕ}
  [AddCommGroup V] [Module (ZMod q) V]
  {p : ι → V} (hp : AffineIndependent (ZMod q) p)
  {x : ι → ℤ} (hsum : ∑ i, x i = 0)
  (hshort : ∀ i, |x i| < (q : ℤ)) (hne : x ≠ 0) :
  (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
 classical
 intro hrel
 have hsum' : ∑ i, (x i : ZMod q) = 0 := by
  simpa only [Int.cast_sum, Int.cast_zero] using
   congrArg (fun z : ℤ => (z : ZMod q)) hsum
 have hz : ∀ i, (x i : ZMod q) = 0 := by
  intro i
  exact hp.eq_zero_of_sum_eq_zero hsum' hrel i (Finset.mem_univ i)
 apply hne
 funext i
 exact Int.eq_zero_of_abs_lt_dvd
  ((ZMod.intCast_zmod_eq_zero_iff_dvd (x i) q).1 (hz i)) (hshort i)
theorem ZdQ
  {ι V : Type*} [Fintype ι] {q H : ℕ}
  [AddCommGroup V] [Module (ZMod q) V]
  {p : ι → V} (hp : AffineIndependent (ZMod q) p)
  {x : ι → ℤ} (hsum : ∑ i, x i = 0)
  (hshort : ∀ i, |x i| ≤ (H : ℤ)) (hHq : H < q) (hne : x ≠ 0) :
  (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
 apply Zgz hp hsum ?_ hne
 intro i
 exact lt_of_le_of_lt (hshort i) (by exact_mod_cast hHq)
end Problem355.Zmx
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zda
open Finset
def Zmc {q : ℕ} (H w : ℕ) (a : Fin 3 → ZMod q) : Prop :=
 ∀ m z : ℤ, m ≠ 0 → |m| ≤ 3 * H → |z| ≤ 3 * H * w → (m : ZMod q) * a 0 ≠ z
lemma ZqJ {q H w : ℕ} [Fact q.Prime] (hH : 1 ≤ H)
   (hq : 2000 * H ^ 2 ≤ q) (hw : 1000 * H ^ 2 * w ≤ q) :
   ∃ A : Finset (Fin 3 → ZMod q), q ^ 3 < 2 * A.card ∧ ∀ a ∈ A, Zmc H w a := by
 classical
 let window (n : ℕ) := Icc (-(n : ℤ)) (n : ℤ)
 have hc (n : ℕ) : (window n).card = 2*n+1 := by simp only [window, Int.card_Icc]; omega
 let pairs := (window (3*H)).product (window (3*H*w))
 let bad := pairs.image fun p => (p.2 : ZMod q) / (p.1 : ZMod q)
 let S := univ \ bad
 have hb : bad.card ≤ (6*H+1)*(6*H*w+1) := by
   apply card_image_le.trans
   simp [pairs, hc, card_product]; ring_nf; rfl
 have hs := card_sdiff_add_card_eq_card (subset_univ bad)
 change S.card + bad.card = _ at hs
 rw [card_univ, ZMod.card] at hs
 have hsq : H ≤ H^2 := by nlinarith
 have hsqw : H*w ≤ H^2*w := Nat.mul_le_mul_right _ hsq
 have hd : q < 2*S.card := by nlinarith
 let A := Fintype.piFinset ![S, univ, univ]
 refine ⟨A, ?_, ?_⟩
 · have h := Nat.mul_lt_mul_of_pos_right hd (pow_pos (Fact.out : q.Prime).pos 2)
   simpa [A, Fin.prod_univ_succ, pow_succ, mul_assoc] using h
 · intro a ha m z hm hmH hz he
   have ha0 : a 0 ∈ S := Fintype.mem_piFinset.mp ha 0
   apply (mem_sdiff.mp ha0).2
   have hmq : |m| < (q : ℤ) := by exact lt_of_le_of_lt hmH (by exact_mod_cast (show 3*H < q by omega))
   have hn : (m : ZMod q) ≠ 0 := fun h => hm (Int.eq_zero_of_abs_lt_dvd
     ((ZMod.intCast_zmod_eq_zero_iff_dvd m q).mp h) hmq)
   refine mem_image.mpr ⟨(m,z), mem_product.mpr ⟨?_, ?_⟩, ?_⟩
   · apply mem_Icc.mpr; simpa using abs_le.mp hmH
   · apply mem_Icc.mpr; simpa using abs_le.mp hz
   · exact (div_eq_iff hn).mpr (by simpa [mul_comm] using he.symm)
lemma Zkk (f : Fin 3 → ℤ) (B : ℤ)
  (hf : ∀ i, |f i| ≤ B) : |∑ i, f i| ≤ 3 * B := by
 calc
  |∑ i, f i| ≤ ∑ i, |f i| := abs_sum_le_sum_abs _ _
  _ ≤ ∑ _i : Fin 3, B := sum_le_sum fun i _ => hf i
  _ = 3 * B := by simp
end Problem355.Zda
end
end OAI
end
section
namespace OAI
namespace Problem355.ZaN
open scoped BigOperators
variable {F : Type*} [Field F]
theorem Zdv
  {S : Set (Fin 3 → F)} (hS : Zac.Zbc S)
  {p : Fin 3 → (Fin 3 → F)} (hp : ∀ i, p i ∈ S)
  (hinj : Function.Injective p) : AffineIndependent F p := by
 have hcol := hS (p 0) (hp 0) (p 1) (hp 1) (p 2) (hp 2)
  (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
 have h := affineIndependent_iff_not_collinear_set.mpr hcol
 convert h using 1
 funext i
 fin_cases i <;> rfl
noncomputable def ZaO (S : Finset (Fin 3 → F)) (a : Fin 3 → F)
  (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) : Finset (Fin 3 → F) := by
 classical
 exact S.image (fun v => G (a + v))
@[simp] theorem ZgV (S : Finset (Fin 3 → F)) (a : Fin 3 → F)
  (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) (u : Fin 3 → F) :
  u ∈ ZaO S a G ↔ ∃ v ∈ S, G (a + v) = u := by
 classical
 simp [ZaO]
@[simp] theorem Zpq (S : Finset (Fin 3 → F)) (a : Fin 3 → F)
  (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :
  (ZaO S a G).card = S.card := by
 classical
 apply Finset.card_image_iff.mpr
 intro v hv w hw heq
 exact add_left_cancel (G.injective heq)
theorem Zjq {S : Finset (Fin 3 → F)}
   (hS : Zac.Zbc (S : Set (Fin 3 → F)))
   (a : Fin 3 → F) (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :
   Zac.Zbc (ZaO S a G : Set (Fin 3 → F)) := by
 have h := (hS.translate a).image G.toAffineEquiv.toAffineMap G.injective
 convert h using 1
 ext v
 simp only [Finset.mem_coe, ZgV, Set.mem_image]
 constructor
 · rintro ⟨w, hw, rfl⟩
   exact ⟨a + w, ⟨w, hw, rfl⟩, rfl⟩
 · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
   exact ⟨w, hw, rfl⟩
theorem Zgc
  {q H : ℕ} [Fact q.Prime]
  {S : Finset (Fin 3 → ZMod q)}
  (hS : Zac.Zbc (S : Set (Fin 3 → ZMod q)))
  (a : Fin 3 → ZMod q)
  (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q))
  {p : Fin 3 → (Fin 3 → ZMod q)}
  (hp : ∀ i, p i ∈ ZaO S a G) (hinj : Function.Injective p)
  {x : Fin 3 → ℤ} (hsum : ∑ i, x i = 0)
  (hshort : ∀ i, |x i| ≤ (H : ℤ)) (hHq : H < q) (hne : x ≠ 0) :
  (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
 exact Zmx.ZdQ
  (Zdv (Zjq hS a G) hp hinj)
  hsum hshort hHq hne
theorem Zcg
   {q H w : ℕ} [Fact q.Prime]
   {S : Finset (Fin 3 → ZMod q)}
   (hbox : ∀ v ∈ S, (v 0).val < w)
   (a : Fin 3 → ZMod q)
   (ha : Zda.Zmc H w a)
   (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q))
   {p : Fin 3 → (Fin 3 → ZMod q)}
   (hp : ∀ i, p i ∈ ZaO S a G)
   {x : Fin 3 → ℤ} (hsum : ∑ i, x i ≠ 0)
   (hshort : ∀ i, |x i| ≤ (H : ℤ)) :
   (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
 classical
 choose v hv heq using fun i => (ZgV S a G (p i)).mp (hp i)
 intro hrel
 have h : ∑ i, (x i : ZMod q) • (a + v i) = 0 := G.injective (by
   simpa only [map_sum, map_smul, heq, map_zero] using hrel)
 let z (i : Fin 3) : ℤ := (v i 0).val
 apply ha (∑ i, x i) (-(∑ i, x i * z i)) hsum (Zda.Zkk _ _ hshort)
 · rw [abs_neg, mul_assoc]
   apply Zda.Zkk
   intro i
   rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
   exact mul_le_mul (hshort i) (by exact_mod_cast (hbox _ (hv i)).le)
    (Int.natCast_nonneg _) (by positivity)
 · push_cast
   rw [eq_neg_iff_add_eq_zero]
   simpa [z, Finset.sum_apply, Finset.sum_mul, mul_add, Finset.sum_add_distrib] using congrFun h 0
theorem ZkO
  {q H w : ℕ} [Fact q.Prime] (hH : 1 ≤ H)
  {S : Finset (Fin 3 → ZMod q)}
  (hbox : ∀ v ∈ S, (v 0).val < w)
  (a : Fin 3 → ZMod q)
  (ha : Zda.Zmc H w a)
  (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q)) :
  (0 : Fin 3 → ZMod q) ∉ ZaO S a G := by
 intro hzero
 have h := Zcg hbox a ha G
  (p := fun _ => 0) (fun _ => hzero) (x := ![1, 0, 0])
  (by norm_num [Fin.sum_univ_succ])
  (by
   intro i
   fin_cases i
   · simpa using (show (1 : ℤ) ≤ H by exact_mod_cast hH)
   · simp
   · simp)
 exact h (by simp)
theorem ZkP
   {q H w : ℕ} [Fact q.Prime]
   {S : Finset (Fin 3 → ZMod q)}
   (hS : Zac.Zbc (S : Set (Fin 3 → ZMod q)))
   (hbox : ∀ v ∈ S, (v 0).val < w)
   (a : Fin 3 → ZMod q)
   (ha : Zda.Zmc H w a)
   (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q))
   {p : Fin 3 → (Fin 3 → ZMod q)}
   (hp : ∀ i, p i ∈ ZaO S a G) (hinj : Function.Injective p)
   {x : Fin 3 → ℤ} (hshort : ∀ i, |x i| ≤ (H : ℤ))
   (hHq : H < q) (hne : x ≠ 0) :
   (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
 by_cases hsum : ∑ i, x i = 0
 · exact Zgc hS a G hp hinj hsum hshort hHq hne
 · exact Zcg hbox a ha G hp hsum hshort
theorem Zlu
  {q H w : ℕ} [Fact q.Prime] (hH : 1 ≤ H) (hHq : H < q)
  {S : Finset (Fin 3 → ZMod q)}
  (hS : Zac.Zbc (S : Set (Fin 3 → ZMod q)))
  (hbox : ∀ v ∈ S, (v 0).val < w)
  (a : Fin 3 → ZMod q)
  (ha : Zda.Zmc H w a)
  (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q)) :
  (ZaO S a G).card = S.card ∧
   (0 : Fin 3 → ZMod q) ∉ ZaO S a G ∧
   Zac.Zbc (ZaO S a G : Set (Fin 3 → ZMod q)) ∧
   ∀ p : Fin 3 → (Fin 3 → ZMod q),
    (∀ i, p i ∈ ZaO S a G) → Function.Injective p →
    ∀ x : Fin 3 → ℤ, (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
     (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
 refine ⟨Zpq S a G, ZkO hH hbox a ha G,
  Zjq hS a G, ?_⟩
 intro p hp hinj x hx hne
 exact ZkP hS hbox a ha G hp hinj hx hHq hne
theorem Zpr {q d : ℕ} (hd : 0 < d) (hdq : d ≤ q) :
  q ≤ 2 * d * (q / d) := by
 have hquot : 1 ≤ q / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdq)
 have hrem := Nat.mod_lt q hd
 have hsplit := Nat.mod_add_div q d
 have hprod : d ≤ d * (q / d) := by
  simpa using Nat.mul_le_mul_left d hquot
 nlinarith
end Problem355.ZaN
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZJ
open scoped BigOperators
structure Law (q H : ℕ) [Fact q.Prime] where
 Outcome : Type
 outcomeFintype : Fintype Outcome
 weight : Outcome → ℝ
 sets : Outcome → Finset (Fin 3 → ZMod q)
 size : ℕ
 size_pos : 0 < size
 weight_nonneg : ∀ ω, 0 ≤ weight ω
 weight_sum : @Finset.sum Outcome ℝ _ (@Finset.univ Outcome outcomeFintype) weight = 1
 sets_card : ∀ ω, (sets ω).card = size
 size_lower : q ^ 2 ≤ 2000 ^ 3 * H ^ 6 * size
 zero_not_mem : ∀ ω, (0 : Fin 3 → ZMod q) ∉ sets ω
 isCap : ∀ ω, Zac.Zbc (sets ω : Set (Fin 3 → ZMod q))
 short_relation : ∀ ω (p : Fin 3 → (Fin 3 → ZMod q)),
  (∀ i, p i ∈ sets ω) → Function.Injective p →
  ∀ x : Fin 3 → ℤ, (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
   (∑ i, (x i : ZMod q) • p i) ≠ 0
 ZcW : ∀ p : Fin 3 → (Fin 3 → ZMod q),
  AffineIndependent (ZMod q) p →
  @Zb.Zk Outcome (Fin 3 → ZMod q) outcomeFintype
   q size weight sets p ≤ 8
 weight_le_four : ∀ (p : Fin 3 → (Fin 3 → ZMod q)) (i j : Fin 3), p i ≠ p j →
  @Zb.Zk Outcome (Fin 3 → ZMod q) outcomeFintype
   q size weight sets p ≤ 4 * ((q : ℝ) ^ 3 / size)
 weight_le_two : ∀ p : Fin 3 → (Fin 3 → ZMod q),
  @Zb.Zk Outcome (Fin 3 → ZMod q) outcomeFintype
   q size weight sets p ≤ 2 * ((q : ℝ) ^ 3 / size) ^ 2
instance Law.Zsj {q H : ℕ} [Fact q.Prime] (L : Law q H) : Fintype L.Outcome := L.outcomeFintype
private theorem Zfo {q : ℕ} [Fact q.Prime]
  (e : (Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q))
  (x : Fin 3 → ZMod q) :
  e x = (ZR.ZF e).1
   ((ZR.ZF e).2 + x) := by
 have h := congrArg
  (fun f : (Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q) => f x)
  (ZR.ZF.symm_apply_apply e)
 exact h.symm.trans (ZR.ZiY
  (ZR.ZF e).1 (ZR.ZF e).2 x)
theorem ZnG {q H w : ℕ} [Fact q.Prime]
   (hH : 1 ≤ H) (hHq : H < q)
   (S : Finset (Fin 3 → ZMod q)) (hS : S.Nonempty)
   (hcap : Zac.Zbc (S : Set (Fin 3 → ZMod q)))
   (hbox : ∀ v ∈ S, (v 0).val < w)
   (hsize : q ^ 2 ≤ 2000 ^ 3 * H ^ 6 * S.card)
   (A : Finset (Fin 3 → ZMod q)) (hA : q ^ 3 ≤ 2 * A.card)
   (hallowed : ∀ a ∈ A, Zda.Zmc H w a) :
   Nonempty (Law q H) := by
 classical
 let Aff := (Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)
 let : Finite Aff := Finite.of_injective
   (fun e : Aff => (e : (Fin 3 → ZMod q) → (Fin 3 → ZMod q)))
   DFunLike.coe_injective
 let : Fintype Aff := Fintype.ofFinite Aff
 let T : Finset Aff := ZY.ZbD A
 have hA' : Fintype.card (Fin 3 → ZMod q) ≤ 2 * A.card := by
   simpa using hA
 have hT : T.Nonempty := ZY.ZfJ A hA'
 have hTsize : Fintype.card Aff ≤ 2 * T.card :=
   ZY.ZbX A hA'
 let μ : T → ℝ := fun _ => (T.card : ℝ)⁻¹
 let V : T → Finset (Fin 3 → ZMod q) := fun e => S.image e.1
 have hV (e : T) : V e = ZaN.ZaO S
     (ZR.ZF e.1).2
     (ZR.ZF e.1).1 := by
   ext y
   simp only [V, Finset.mem_image, ZaN.ZgV]
   constructor
   · rintro ⟨x, hx, rfl⟩
     exact ⟨x, hx, (Zfo e.1 x).symm⟩
   · rintro ⟨x, hx, rfl⟩
     exact ⟨x, hx, Zfo e.1 x⟩
 have hall (e : T) := hallowed _ (Finset.mem_filter.mp e.2).2
 have hprops (e : T) := ZaN.Zlu hH hHq hcap hbox
   (ZR.ZF e.1).2 (hall e)
   (ZR.ZF e.1).1
 have hW (p : Fin 3 → (Fin 3 → ZMod q)) :
     Zb.Zk q S.card μ V p =
      ZY.Zaa S T p := by
   rw [ZY.ZeP]
   simp only [Zb.Zk, Zb.Zbb,
     ZMod.card]
   congr 1
   apply Finset.sum_congr rfl
   intro e he
   simp only [Zb.ZmC, μ, V, Finset.mem_image]
   split_ifs <;> simp_all
 refine ⟨{
   Outcome := T
   outcomeFintype := inferInstance
   weight := μ
   sets := V
   size := S.card
   size_pos := hS.card_pos
   weight_nonneg := ?_
   weight_sum := ?_
   sets_card := ?_
   size_lower := hsize
   zero_not_mem := ?_
   isCap := ?_
   short_relation := ?_
   ZcW := ?_
   weight_le_four := ?_
   weight_le_two := ?_ }⟩
 · intro e
   dsimp [μ]
   positivity
 · simp only [μ, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
   exact mul_inv_cancel₀ (by exact_mod_cast hT.card_pos.ne')
 · intro e
   rw [hV]
   exact (hprops e).1
 · intro e
   rw [hV]
   exact (hprops e).2.1
 · intro e
   rw [hV]
   exact (hprops e).2.2.1
 · intro e p hp hinj x hx hne
   exact (hprops e).2.2.2 p (fun i => hV e ▸ hp i) hinj x hx hne
 · intro p hp
   rw [hW]
   exact ZY.ZcV S hS T hT hTsize p hp
 · intro p i j hp
   rw [hW]
   simpa only [ZMod.card] using
     ZY.Zfd S hS T hT hTsize p i j hp
 · intro p
   rw [hW]
   simpa only [ZMod.card] using
     ZY.ZhP S hS T hT hTsize p
theorem ZqV {q H : ℕ} [Fact q.Prime]
  (hH : 1 ≤ H) (hq : 2000 * H ^ 2 ≤ q) : Nonempty (Law q H) := by
 classical
 let w := q / (1000 * H ^ 2)
 have hd : 0 < 1000 * H ^ 2 := by positivity
 have hdq : 1000 * H ^ 2 ≤ q := by omega
 have hwq : w ≤ q := Nat.div_le_self _ _
 have hq2 : q ≠ 2 := by
  have hHsq : 1 ≤ H ^ 2 := by nlinarith
  omega
 obtain ⟨S, hbox, hsize, hcap⟩ := Zac.ZpP hq2 hwq
 have hfloor : q ≤ 2000 * H ^ 2 * w := by
  calc
   q ≤ 2 * (1000 * H ^ 2) * w := ZaN.Zpr hd hdq
   _ = 2000 * H ^ 2 * w := by ring
 have hc : q ^ 2 ≤ 2000 ^ 3 * H ^ 6 * S.card := by
  rw [hsize]; have hH6 : H ^ 2 ≤ H ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
  calc
   q ^ 2 = q * q := by ring
   _ ≤ (2000 * H ^ 2 * w) * q := Nat.mul_le_mul_right _ hfloor
   _ ≤ _ := by rw [← Nat.mul_assoc]; gcongr <;> norm_num
 have hS : S.Nonempty := by
  apply Finset.card_pos.mp
  by_contra hn
  have hz : S.card = 0 := by omega
  have hp : 0 < q ^ 2 := pow_pos (Fact.out : q.Prime).pos 2
  simp only [hz, mul_zero] at hc
  omega
 obtain ⟨A, hA, ha⟩ := Zda.ZqJ hH hq (show 1000 * H ^ 2 * w ≤ q from Nat.mul_div_le _ _)
 have : H ≤ H ^ 2 := by nlinarith
 exact ZnG hH (by omega) S hS hcap hbox hc A hA.le ha
end Problem355.ZJ
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zmy
open ZP
open scoped BigOperators
def ZO : ℝ := 8 * Zcw
theorem ZdO
   {B k q : ℕ} (hB : 0 < B) [Fact q.Prime]
   [Fintype ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q))]
   (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) (d : Zj B k C)
   (U : Finset (Fin 3 → ZMod q)) (hU : U.Nonempty)
   (T : Finset ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)))
   (hT : T.Nonempty)
   (hsize : Fintype.card ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)) ≤
    2 * T.card)
   (N : ℝ) (hN : 1 ≤ N) (S : Finset Zi)
   (horbit : ∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
    ZS.Zbl C)
   (hbox : ∀ A ∈ S, ∀ j, Homogeneous.ZaX N (fun i => (A i j : ℝ)))
   (t : ℤ) (ht : t ≠ 0) (htq : |t| < (q : ℤ)) (hdet : ∀ A ∈ S, A.det = t) :
   (∑ A ∈ S, ZY.Zaa U T
    (fun j i => (A i j : ZMod q))) ≤
     ZO * Real.log (2 * N) ^ 2 * N ^ 6 /
      ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
 apply ZP.ZdO B k d.b d.e hB d.ZpO d.e_le_k
   d.b_le_e C d.left d.right _ N hN S horbit hbox t ht hdet _ 8 (by norm_num)
 · intro A hA
   exact Zdi.ZcW U hU T hT hsize A
    (by simpa only [hdet A hA] using ht) (by simpa only [hdet A hA] using htq)
 · simpa only [ZaG.Zad, Nat.cast_pow] using d.diagonalization
end Problem355.Zmy
end
end OAI
end
section
namespace OAI
namespace Problem355.Zo
open Matrix
open scoped Matrix BigOperators
noncomputable def Zbt (X : ℤ) : Finset Vector := by
 classical
 exact (Finset.Icc (fun _ => -(2 * X ^ 2)) (fun _ => 2 * X ^ 2)).filter
  (fun w => IsPrimitive w ∧ ∀ i, w i ≠ 0)
lemma ZfV (X : ℤ) (w : Vector) : w ∈ Zbt X ↔
   IsPrimitive w ∧ (∀ i, w i ≠ 0) ∧ (∀ i, |w i| ≤ 2 * X ^ 2) := by
 simp only [Zbt, Finset.mem_filter, Finset.mem_Icc]
 constructor
 · rintro ⟨⟨hlo, hhi⟩, hp, hn⟩
   exact ⟨hp, hn, fun i => abs_le.mpr ⟨hlo i, hhi i⟩⟩
 · rintro ⟨hp, hn, hb⟩
   exact ⟨⟨fun i => (abs_le.mp (hb i)).1, fun i => (abs_le.mp (hb i)).2⟩, hp, hn⟩
lemma Zmd {X : ℤ} {w : Vector} (hw : w ∈ Zbt X) :
  1 ≤ ‖toEuclidean w‖ ∧ ‖toEuclidean w‖ ≤ 6 * (X : ℝ) ^ 2 := by
 obtain ⟨hp, _, hb⟩ := (ZfV X w).mp hw
 refine ⟨Zli w hp.ne_zero, ?_⟩
 have h := ZeF w (2 * (X : ℝ) ^ 2)
  (by positivity) (fun i => by exact_mod_cast hb i)
 nlinarith
lemma ZkQ (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hdet : A.det = 0) (hheight : ∀ i, A 2 i ≠ 0)
  (hproj : ∀ i j : Fin 3, i ≠ j →
   ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
   ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
  (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ i j, |A i j| ≤ X) :
  ∃ w ∈ Zbt X, A *ᵥ w = 0 := by
 obtain ⟨w, hp, hk, hn, hb⟩ :=
  Zdr A hdet hheight hproj X hX hbound
 exact ⟨w, (ZfV X w).mpr ⟨hp, hn, hb⟩, hk⟩
theorem Zff
  (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
  (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ) (hW : ∀ A ∈ S, 0 ≤ W A)
  (hdet : ∀ A ∈ S, A.det = 0) (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
  (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
   ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
   ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
  (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X) :
  (∑ A ∈ S, W A) ≤
   ∑ w ∈ Zbt X, ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A := by
 classical
 calc
  (∑ A ∈ S, W A) ≤ ∑ A ∈ S, ∑ w ∈ Zbt X,
    if A *ᵥ w = 0 then W A else 0 := by
   apply Finset.sum_le_sum
   intro A hA
   obtain ⟨w, hw, hk⟩ := ZkQ A (hdet A hA) (hheight A hA)
    (hproj A hA) X hX (hbound A hA)
   have hs := Finset.single_le_sum (s := Zbt X)
    (f := fun w => if A *ᵥ w = 0 then W A else 0)
    (fun x hx => by split_ifs <;> first | exact hW A hA | rfl) hw
   simpa [hk] using hs
  _ = ∑ w ∈ Zbt X, ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A := by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro w hw
   rw [Finset.sum_filter]
end Problem355.Zo
end OAI
end
section
namespace OAI
namespace Problem355.Zo
open Matrix
open scoped Matrix BigOperators
theorem Zef
  (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
  (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ) (hW : ∀ A ∈ S, 0 ≤ W A)
  (hdet : ∀ A ∈ S, A.det = 0) (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
  (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
   ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
   ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
  (X : ℤ) (hX : 1 ≤ X) (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X)
  {K : ℝ} (hK : 0 ≤ K)
  (hshell : ∀ i : ℕ,
   ∑ w ∈ (Zbt X).filter (fun w =>
    (2 : ℝ) ^ i ≤ ‖toEuclidean w‖ ∧ ‖toEuclidean w‖ < 2 ^ (i + 1)),
    ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A ≤ K) :
  ∑ A ∈ S, W A ≤ K * (Real.log (12 * (X : ℝ) ^ 2) / Real.log 2) := by
 classical
 have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
 have hR : (1 : ℝ) ≤ 6 * (X : ℝ) ^ 2 := by nlinarith
 have hagg := Anisotropic.Zea
  (Zbt X) (fun w => ‖toEuclidean w‖)
  (fun w => ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A)
  hR hK
  (fun w _ => Finset.sum_nonneg (fun A hA => hW A (Finset.mem_filter.mp hA).1))
  (fun w hw => Zmd hw) hshell
 have hcover := Zff S W hW hdet hheight hproj
  X (by omega) hbound
 simpa only [show (2 : ℝ) * (6 * (X : ℝ) ^ 2) = 12 * (X : ℝ) ^ 2 by ring] using
  hcover.trans hagg
lemma ZnH {X : ℝ} (hX : 1 ≤ X) :
  Real.log (12 * X ^ 2) / Real.log 2 ≤
   4 * (Real.log (2 * X) / Real.log 2) := by
 have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
 have hpos : 0 < 12 * X ^ 2 := by positivity
 have hsq : 1 ≤ X ^ 2 := by nlinarith
 have hfour : 12 * X ^ 2 ≤ (2 * X) ^ 4 := by
  nlinarith [sq_nonneg (X ^ 2 - 1)]
 have hlog := Real.log_le_log hpos hfour
 rw [Real.log_pow] at hlog
 have hquot := div_le_div_of_nonneg_right hlog hlog2.le
 simpa [mul_div_assoc] using hquot
theorem Zdj
  (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
  (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ) (hW : ∀ A ∈ S, 0 ≤ W A)
  (hdet : ∀ A ∈ S, A.det = 0) (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
  (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
   ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
   ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
  (X : ℤ) (hX : 1 ≤ X) (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X)
  {K : ℝ} (hK : 0 ≤ K)
  (hshell : ∀ i : ℕ,
   ∑ w ∈ (Zbt X).filter (fun w =>
    (2 : ℝ) ^ i ≤ ‖toEuclidean w‖ ∧ ‖toEuclidean w‖ < 2 ^ (i + 1)),
    ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A ≤ K) :
  ∑ A ∈ S, W A ≤ 4 * K * (Real.log (2 * (X : ℝ)) / Real.log 2) := by
 have h := Zef S W hW hdet hheight hproj
  X hX hbound hK hshell
 have hxR : (1 : ℝ) ≤ X := by exact_mod_cast hX
 have hmul := mul_le_mul_of_nonneg_left (ZnH hxR) hK
 calc
  _ ≤ K * (Real.log (12 * (X : ℝ) ^ 2) / Real.log 2) := h
  _ ≤ K * (4 * (Real.log (2 * (X : ℝ)) / Real.log 2)) := hmul
  _ = _ := by ring
end Problem355.Zo
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZfQ
open Matrix
open scoped BigOperators Matrix
noncomputable local instance zCPD7 (p : Prop) : Decidable p := Classical.propDecidable p
theorem ZgA {N : ℝ} (hN : 1 ≤ N) :
  Real.log (4 * N) ≤ 2 * Real.log (2 * N) := by
 have hpos : 0 < 4 * N := by positivity
 have hscale : 4 * N ≤ (2 * N) ^ 2 := by nlinarith
 have h := Real.log_le_log hpos hscale
 simpa only [Real.log_pow, Nat.cast_ofNat] using h
theorem ZjK {N : ℝ} (hN : 1 ≤ N) :
  Real.log (4 * N) / Real.log 2 ≤
   (2 / (Real.log 2) ^ 2) * (Real.log (2 * N)) ^ 2 := by
 have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
 have hlower : Real.log (2 : ℝ) ≤ Real.log (2 * N) :=
  Real.log_le_log (by norm_num) (by linarith)
 have hratio : 1 ≤ Real.log (2 * N) / Real.log 2 :=
  (le_div_iff₀ hlog2).mpr (by simpa using hlower)
 calc
  Real.log (4 * N) / Real.log 2 ≤
    (2 * Real.log (2 * N)) / Real.log 2 :=
   div_le_div_of_nonneg_right (ZgA hN) hlog2.le
  _ = 2 * (Real.log (2 * N) / Real.log 2) := by ring
  _ ≤ 2 * (Real.log (2 * N) / Real.log 2) ^ 2 := by nlinarith
  _ = (2 / (Real.log 2) ^ 2) * (Real.log (2 * N)) ^ 2 := by ring
end Problem355.ZfQ
end
end OAI
end
section
namespace OAI
namespace Problem355.Zkz
open Finset
theorem ZhR (R q : ℕ) (hq : 0 < q) :
  ((R : ℤ) / q + 1 - (-(R : ℤ)) / q).toNat ≤ 2 * (R / q) + 2 := by
 have hqz : (0 : ℤ) < q := by exact_mod_cast hq
 apply Int.toNat_le.mpr
 rw [Int.neg_ediv]
 have hs : (q : ℤ).sign = 1 := Int.sign_eq_one_of_pos hqz
 rw [hs]
 push_cast
 rw [← Int.natCast_ediv]
 split_ifs <;> omega
theorem ZgW {d : ℕ}
  (s : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q)
  (T : Finset (Fin d → ZMod q))
  (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
  (hres : ∀ x ∈ s, (fun i => (x i : ZMod q)) ∈ T) :
  s.card ≤ (2 * (R / q) + 2) ^ d * T.card := by
 classical
 let : NeZero q := ⟨by omega⟩
 have hqz : (0 : ℤ) < q := by exact_mod_cast hq
 let F (x : ↥s) : (Fin d → ↥(Icc ((-(R : ℤ)) / q) ((R : ℤ) / q))) × ↥T :=
  (fun i => ⟨x.val i / q, mem_Icc.mpr ⟨Int.ediv_le_ediv hqz (hbox _ x.prop i).1,
   Int.ediv_le_ediv hqz (hbox _ x.prop i).2⟩⟩, ⟨_, hres _ x.prop⟩)
 have hinj : Function.Injective F := by
  intro x y h
  apply Subtype.ext
  funext i
  have hd : x.val i / q = y.val i / q := congrArg Subtype.val (congrFun (congrArg Prod.fst h) i)
  have hr := congrFun (congrArg (fun p => (p.2 : Fin d → ZMod q)) h) i
  have hm : x.val i % q = y.val i % q := by
   simpa only [← ZMod.val_intCast] using congrArg (fun z : ZMod q => (z.val : ℤ)) hr
  calc
   _ = _ := (Int.ediv_mul_add_emod (x.val i) q).symm
   _ = y.val i := by rw [hd, hm, Int.ediv_mul_add_emod]
 have hc := Fintype.card_le_of_injective F hinj
 simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, Int.card_Icc] at hc
 exact hc.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (ZhR R q hq) d))
theorem Zfg {d : ℕ}
  (s : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q) (hqR : q ≤ R)
  (T : Finset (Fin d → ZMod q))
  (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
  (hres : ∀ x ∈ s, (fun i => (x i : ZMod q)) ∈ T) :
  (s.card : ℝ) ≤ (4 * (R : ℝ) / (q : ℝ)) ^ d * (T.card : ℝ) := by
 have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
 have hratio : 1 ≤ (R : ℝ) / (q : ℝ) := by
  apply (le_div_iff₀ hq0).mpr
  simpa using (show (q : ℝ) ≤ R by exact_mod_cast hqR)
 have hdiv : ((R / q : ℕ) : ℝ) ≤ (R : ℝ) / (q : ℝ) := Nat.cast_div_le
 have hfactor : ((2 * (R / q) + 2 : ℕ) : ℝ) ≤ 4 * (R : ℝ) / (q : ℝ) := by
  push_cast
  rw [mul_div_assoc]
  linarith
 have hcount : (s.card : ℝ) ≤
   ((2 * (R / q) + 2 : ℕ) : ℝ) ^ d * (T.card : ℝ) := by
  exact_mod_cast ZgW s R q hq T hbox hres
 exact hcount.trans (mul_le_mul_of_nonneg_right
  (pow_le_pow_left₀ (by positivity) hfactor d) (by positivity))
theorem ZbE {d : ℕ}
  (s : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q) (hqR : q ≤ R)
  (T : Finset (Fin d → ZMod q)) (D : ℝ) (hD : 0 < D)
  (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
  (hres : ∀ x ∈ s, (fun i => (x i : ZMod q)) ∈ T)
  (hT : (T.card : ℝ) ≤ (q : ℝ) ^ d / D) :
  (s.card : ℝ) ≤ 4 ^ d * (R : ℝ) ^ d / D := by
 have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
 calc
  (s.card : ℝ) ≤ (4 * (R : ℝ) / (q : ℝ)) ^ d * (T.card : ℝ) :=
   Zfg s R q hq hqR T hbox hres
  _ ≤ (4 * (R : ℝ) / (q : ℝ)) ^ d * ((q : ℝ) ^ d / D) :=
   mul_le_mul_of_nonneg_left hT (by positivity)
  _ = 4 ^ d * (R : ℝ) ^ d / D := by
   rw [div_pow, mul_pow]
   field_simp
end Problem355.Zkz
end OAI
end
section
namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem355.Zqj
theorem Zps {B : ℝ} (hB : 2 ≤ B) (e : ℕ) :
   ∑ j ∈ Finset.range (e + 1), B ^ j ≤ 2 * B ^ e := by
 induction e with
 | zero => simp
 | succ e ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hp : 0 ≤ B ^ e := pow_nonneg (by linarith) _
    nlinarith
theorem ZpQ {B : ℝ} (hB : 2 ≤ B) (b e : ℕ) :
  ∑ j ∈ Finset.range (e + 1), B ^ (2 * j - (j - b)) ≤
   2 * B ^ (b + e) := by
 have hB1 : 1 ≤ B := by linarith
 calc
  ∑ j ∈ Finset.range (e + 1), B ^ (2 * j - (j - b)) ≤
    ∑ j ∈ Finset.range (e + 1), B ^ (b + j) := by
   apply Finset.sum_le_sum
   intro j hj
   exact pow_le_pow_right₀ hB1 (by omega)
  _ = B ^ b * ∑ j ∈ Finset.range (e + 1), B ^ j := by
   simp_rw [pow_add]
   rw [Finset.mul_sum]
  _ ≤ B ^ b * (2 * B ^ e) :=
   mul_le_mul_of_nonneg_left (Zps hB e) (by positivity)
  _ = 2 * B ^ (b + e) := by rw [pow_add]; ring
theorem ZmS {α : Type*} [DecidableEq α]
  (S : Finset α) (v : α → ℕ) {B A : ℝ} (b e : ℕ)
  (hB : 2 ≤ B) (hA : 0 ≤ A)
  (hv : ∀ x ∈ S, v x ≤ e)
  (htail : ∀ j ≤ e,
   ((S.filter fun x => j ≤ v x).card : ℝ) ≤ A / B ^ (j + (j - b))) :
  ∑ x ∈ S, B ^ (3 * v x) ≤ 2 * A * B ^ (b + e) := by
 have hB0 : 0 < B := by linarith
 have hterm (x : α) (hx : x ∈ S) :
   B ^ (3 * v x) ≤ ∑ j ∈ Finset.range (e + 1),
    if j ≤ v x then B ^ (3 * j) else 0 := by
  have hmem : v x ∈ Finset.range (e + 1) := by
   simpa using Nat.lt_succ_of_le (hv x hx)
  simpa using Finset.single_le_sum
   (f := fun j => if j ≤ v x then B ^ (3 * j) else 0)
   (fun j hj => by split_ifs <;> positivity) hmem
 calc
  ∑ x ∈ S, B ^ (3 * v x) ≤
    ∑ x ∈ S, ∑ j ∈ Finset.range (e + 1),
     if j ≤ v x then B ^ (3 * j) else 0 :=
   Finset.sum_le_sum hterm
  _ = ∑ j ∈ Finset.range (e + 1),
    B ^ (3 * j) * ((S.filter fun x => j ≤ v x).card : ℝ) := by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro j hj
   rw [← Finset.sum_filter]
   simp [mul_comm]
  _ ≤ ∑ j ∈ Finset.range (e + 1),
    B ^ (3 * j) * (A / B ^ (j + (j - b))) := by
   apply Finset.sum_le_sum
   intro j hj
   apply mul_le_mul_of_nonneg_left (htail j (by simpa using hj))
   positivity
  _ = A * ∑ j ∈ Finset.range (e + 1), B ^ (2 * j - (j - b)) := by
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro j hj
   have he : 3 * j - (j + (j - b)) = 2 * j - (j - b) := by omega
   rw [← he, pow_sub₀ B hB0.ne' (by omega)]
   simp only [div_eq_mul_inv]
   ring
  _ ≤ A * (2 * B ^ (b + e)) :=
   mul_le_mul_of_nonneg_left (ZpQ hB b e) hA
  _ = 2 * A * B ^ (b + e) := by ring
end Problem355.Zqj
end
end OAI
end
section
namespace OAI
namespace Problem355.ZcT
open Finset
theorem ZgX
  (S : Finset (Fin 3 → ℤ)) (v : (Fin 3 → ℤ) → ℕ)
  (B R b e : ℕ) (hB : 2 ≤ B) (hR : B ^ e ≤ R)
  (T : ∀ j : ℕ, Finset (Fin 3 → ZMod (B ^ j)))
  (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
  (hv : ∀ x ∈ S, v x ≤ e)
  (hres : ∀ j ≤ e, ∀ x ∈ S, j ≤ v x →
   (fun i => (x i : ZMod (B ^ j))) ∈ T j)
  (hT : ∀ j ≤ e, ((T j).card : ℝ) ≤
   (B : ℝ) ^ (3 * j) / (B : ℝ) ^ (j + (j - b))) :
  ∑ x ∈ S, (B : ℝ) ^ (3 * v x) ≤
   128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
 classical
 have hB0 : 0 < B := by omega
 have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
 have htail : ∀ j ≤ e,
   ((S.filter fun x => j ≤ v x).card : ℝ) ≤
    (64 * (R : ℝ) ^ 3) / (B : ℝ) ^ (j + (j - b)) := by
  intro j hj
  have hq : 0 < B ^ j := pow_pos hB0 _
  have hqR : B ^ j ≤ R :=
   (Nat.pow_le_pow_right (by omega : 1 ≤ B) hj).trans hR
  have hdensity : ((T j).card : ℝ) ≤
    ((B ^ j : ℕ) : ℝ) ^ 3 / (B : ℝ) ^ (j + (j - b)) := by
   simpa only [Nat.cast_pow, ← pow_mul, Nat.mul_comm j 3] using hT j hj
  have hc := Zkz.ZbE
   (S.filter fun x => j ≤ v x) R (B ^ j) hq hqR (T j)
   ((B : ℝ) ^ (j + (j - b))) (by positivity)
   (fun x hx i => hbox x (mem_filter.mp hx).1 i)
   (fun x hx => hres j hj x (mem_filter.mp hx).1 (mem_filter.mp hx).2)
   hdensity
  norm_num only [show (4 : ℝ) ^ 3 = 64 by norm_num] at hc
  exact hc
 calc
  ∑ x ∈ S, (B : ℝ) ^ (3 * v x) ≤
    2 * (64 * (R : ℝ) ^ 3) * (B : ℝ) ^ (b + e) :=
   Zqj.ZmS S v b e hBR (by positivity) hv htail
  _ = 128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by ring
theorem Zer
  (S : Finset (Fin 3 → ℤ)) (g : (Fin 3 → ℤ) → ℕ)
  (B R b e : ℕ) (hB : B.Prime) (hR : B ^ e ≤ R)
  (T : ∀ j : ℕ, Finset (Fin 3 → ZMod (B ^ j)))
  (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
  (hg : ∀ x ∈ S, g x ∣ B ^ e)
  (hres : ∀ j ≤ e, ∀ x ∈ S, B ^ j ∣ g x →
    (fun i => (x i : ZMod (B ^ j))) ∈ T j)
  (hT : ∀ j ≤ e, ((T j).card : ℝ) ≤
    (B : ℝ) ^ (3 * j) / (B : ℝ) ^ (j + (j - b))) :
  ∑ x ∈ S, (g x : ℝ) ^ 3 ≤
    128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
 classical
 have hex : ∀ x : Fin 3 → ℤ, ∃ a ≤ e, x ∈ S → g x = B ^ a := by
  intro x
  by_cases hx : x ∈ S
  · obtain ⟨a, ha, hga⟩ := (Nat.dvd_prime_pow hB).mp (hg x hx)
    exact ⟨a, ha, fun _ => hga⟩
  · exact ⟨0, Nat.zero_le _, fun h => (hx h).elim⟩
 choose v hv hgv using hex
 have hm := ZgX S v B R b e hB.two_le hR T hbox
  (fun x _ => hv x) (fun j hj x hx hjv => hres j hj x hx (by
    rw [hgv x hx]
    exact Nat.pow_dvd_pow B hjv)) hT
 calc
  ∑ x ∈ S, (g x : ℝ) ^ 3 = ∑ x ∈ S, (B : ℝ) ^ (3 * v x) := by
    apply sum_congr rfl
    intro x hx
    rw [hgv x hx, Nat.cast_pow, ← pow_mul, Nat.mul_comm (v x) 3]
  _ ≤ 128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := hm
end Problem355.ZcT
end OAI
end
section
namespace OAI
namespace Problem355.Zfk
open scoped BigOperators Matrix
variable {R ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]
abbrev Kernel (A : Matrix ι ι R) := {x : ι → R // A.mulVec x = 0}
def Zeo (d : ι → R) :
  Kernel (Matrix.diagonal d) ≃ (∀ i, {x : R // d i * x = 0}) where
 toFun x i := ⟨x.1 i, by
  have h := congrFun x.2 i
  simpa only [Matrix.mulVec_diagonal, Pi.zero_apply] using h⟩
 invFun x := ⟨fun i => (x i).1, by
  funext i
  simpa only [Matrix.mulVec_diagonal, Pi.zero_apply] using (x i).2⟩
 left_inv x := by rfl
 right_inv x := by rfl
def ZpR (Q : (Matrix ι ι R)ˣ) : (ι → R) ≃ (ι → R) where
 toFun := (Q : Matrix ι ι R).mulVec
 invFun := ((Q⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R).mulVec
 left_inv x := by
  rw [Matrix.mulVec_mulVec]
  simp
 right_inv x := by
  rw [Matrix.mulVec_mulVec]
  simp
def ZoL (A : Matrix ι ι R) (P Q : (Matrix ι ι R)ˣ) :
  Kernel ((P : Matrix ι ι R) * A * (Q : Matrix ι ι R)) ≃ Kernel A := by
 apply Equiv.subtypeEquiv (ZpR Q)
 intro x
 change (((P : Matrix ι ι R) * A * (Q : Matrix ι ι R)).mulVec x = 0) ↔
  A.mulVec ((Q : Matrix ι ι R).mulVec x) = 0
 rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
 exact (Matrix.mulVec_injective_of_isUnit P.isUnit).eq_iff' (by simp)
theorem Zme (A : Matrix ι ι R) (P Q : (Matrix ι ι R)ˣ) :
  Nat.card (Kernel ((P : Matrix ι ι R) * A * (Q : Matrix ι ι R))) =
   Nat.card (Kernel A) :=
 Nat.card_congr (ZoL A P Q)
section Cardinality
variable [Fintype R] [DecidableEq R]
theorem ZmT (d : ι → R) :
  Fintype.card (Kernel (Matrix.diagonal d)) =
   ∏ i, Fintype.card {x : R // d i * x = 0} := by
 classical
 rw [Fintype.card_congr (Zeo d), Fintype.card_pi]
theorem ZiZ (D E : R) :
  Fintype.card (Kernel (Matrix.diagonal ![1, D, E])) =
   Fintype.card {x : R // D * x = 0} *
    Fintype.card {x : R // E * x = 0} := by
 rw [ZmT]
 simp [Fin.prod_univ_succ]
 exact Or.inl rfl
end Cardinality
theorem ZgY (B j b : ℕ) [NeZero B] :
   Nat.card {x : ZMod (B ^ j) // (B : ZMod (B ^ j)) ^ b * x = 0} =
    B ^ min b j := by
 rcases le_total b j with h | h
 · simpa only [Nat.min_eq_left h] using Zcr B j b h
 · simpa only [Nat.cast_pow, Nat.gcd_eq_left (pow_dvd_pow B h),
    Nat.min_eq_right h] using Zdp (B ^ j) (B ^ b)
theorem Zgd (B j b e : ℕ) [NeZero B]
  (hje : j ≤ e) :
  Nat.card (Kernel (Matrix.diagonal
   ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e])) =
    B ^ (j + min b j) := by
 classical
 rw [Nat.card_eq_fintype_card, ZiZ,
  ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
  ZgY, ZgY,
  Nat.min_eq_right hje, pow_add]
 exact Nat.mul_comm _ _
theorem ZdR (B j b e : ℕ) [NeZero B]
  (hje : j ≤ e) :
  Nat.card (Kernel (Matrix.diagonal
   ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e])) *
    B ^ (j + (j - b)) = (B ^ j) ^ 3 := by
 rw [Zgd B j b e hje, ← pow_add, ← pow_mul]
 congr 1
 omega
theorem ZgB (B j b e : ℕ) [NeZero B]
  (hje : j ≤ e) (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ j)))
  (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ j)))ˣ)
  (hC : C = (P : Matrix _ _ _) *
   Matrix.diagonal ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e] *
    (Q : Matrix _ _ _)) :
  Nat.card (Kernel C) * B ^ (j + (j - b)) = (B ^ j) ^ 3 := by
 rw [hC, Zme]
 exact ZdR B j b e hje
theorem Zhw (B k j b e : ℕ) [NeZero B]
  (hjk : j ≤ k) (hje : j ≤ e)
  (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
  (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
  (hC : C = (P : Matrix _ _ _) *
    Matrix.diagonal ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
     (Q : Matrix _ _ _)) :
  Nat.card (Kernel (C.map
    (ZMod.castHom (pow_dvd_pow B hjk) (ZMod (B ^ j))))) *
     B ^ (j + (j - b)) = (B ^ j) ^ 3 := by
 let f : ZMod (B ^ k) →+* ZMod (B ^ j) :=
  ZMod.castHom (pow_dvd_pow B hjk) (ZMod (B ^ j))
 have hd : (Matrix.diagonal
    ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e]).map f =
    Matrix.diagonal ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e] := by
  ext i l
  by_cases h : i = l
  · subst l
    fin_cases i <;> simp
  · simp [h]
 apply ZgB B j b e hje (C.map f)
  (Units.map f.mapMatrix.toMonoidHom P) (Units.map f.mapMatrix.toMonoidHom Q)
 change C.map f = (P : Matrix _ _ _).map f *
  Matrix.diagonal ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e] *
    (Q : Matrix _ _ _).map f
 simpa only [Matrix.map_mul, hd] using congrArg (fun A => A.map f) hC
end Problem355.Zfk
end OAI
end
section
namespace OAI
namespace Problem355.ZcT
theorem ZgC {m d : ℕ}
  (C : Matrix (Fin m) (Fin d) ℤ) (x : Fin d → ℤ) (g q : ℕ)
  (hqg : q ∣ g) (hrows : ∀ i, (g : ℤ) ∣ (C.mulVec x) i) :
  (C.map (Int.castRingHom (ZMod q))).mulVec (fun i => (x i : ZMod q)) = 0 := by
 ext i
 have hqgz : (q : ℤ) ∣ (g : ℤ) := by exact_mod_cast hqg
 have hz : ((C.mulVec x) i : ZMod q) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hqgz.trans (hrows i))
 simpa [Matrix.mulVec, dotProduct] using hz
theorem ZeI
   (S : Finset (Fin 3 → ℤ)) (g : (Fin 3 → ℤ) → ℕ)
   (C : Matrix (Fin 3) (Fin 3) ℤ)
   (B R b e k : ℕ) (hB : B.Prime) (hR : B ^ e ≤ R) (hek : e ≤ k)
   (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
   (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
    (P : Matrix _ _ _) * Matrix.diagonal
     ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
      (Q : Matrix _ _ _))
   (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
   (hg : ∀ x ∈ S, g x ∣ B ^ e)
   (hrows : ∀ x ∈ S, ∀ i, (g x : ℤ) ∣ (C.mulVec x) i) :
   ∑ x ∈ S, (g x : ℝ) ^ 3 ≤
    128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
 classical
 let : NeZero B := ⟨hB.ne_zero⟩
 have hBpos : (0 : ℝ) < B := by exact_mod_cast hB.pos
 let T : ∀ j : ℕ, Finset (Fin 3 → ZMod (B ^ j)) := fun j =>
   Finset.univ.filter fun x => (C.map (Int.castRingHom (ZMod (B ^ j)))).mulVec x = 0
 apply Zer S g B R b e hB hR T hbox hg
 · intro j hj x hx hjg
   exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ZgC C x (g x) (B ^ j) hjg (hrows x hx)⟩
 · intro j hj
   have hc := Zfk.Zhw B k j b e
    (hj.trans hek) hj (C.map (Int.castRingHom (ZMod (B ^ k)))) P Q hC
   have hmap : (C.map (Int.castRingHom (ZMod (B ^ k)))).map
     (ZMod.castHom (pow_dvd_pow B (hj.trans hek)) (ZMod (B ^ j))) =
     C.map (Int.castRingHom (ZMod (B ^ j))) := by
    ext i l
    simp
   rw [hmap] at hc
   have htc : (T j).card = Nat.card
     (Zfk.Kernel (C.map (Int.castRingHom (ZMod (B ^ j))))) := by
    simp [T, Zfk.Kernel, Nat.card_eq_fintype_card, Fintype.card_subtype]
   have hc' : (T j).card * B ^ (j + (j - b)) = B ^ (3 * j) := by
    rw [htc]
    simpa only [← pow_mul, Nat.mul_comm j 3] using hc
   apply (le_div_iff₀ (by positivity : (0 : ℝ) < (B : ℝ) ^ (j + (j - b)))).mpr
   exact_mod_cast hc'.le
end Problem355.ZcT
end OAI
end
section
namespace OAI
namespace Problem355.ZcC
variable {ι : Type*} [Fintype ι]
def ZgZ (x : ι → ℤ) : (ι → ℤ) →+ ℤ :=
 (dotProductBilin ℤ ℤ x).toAddMonoidHom
@[simp] theorem Zse (x v : ι → ℤ) : ZgZ x v = dotProduct x v := rfl
theorem Zlv
   (L : AddSubgroup (ι → ℤ)) (x z : ι → ℤ) (hprimitive : dotProduct x z = 1)
   (E : ℕ) (hE : 0 < E) (hcontain : ∀ v : ι → ℤ, E • v ∈ L) :
   ∃ g : ℕ, 0 < g ∧ g ∣ E ∧
    L.map (ZgZ x) = AddSubgroup.zmultiples (g : ℤ) ∧
    (∀ v ∈ L, (g : ℤ) ∣ dotProduct x v) ∧
    ∃ u ∈ L, dotProduct x u = (g : ℤ) := by
 have hEimage : (E : ℤ) ∈ L.map (ZgZ x) := by
   apply AddSubgroup.mem_map.mpr
   refine ⟨E • z, hcontain z, ?_⟩
   change dotProduct x (E • z) = (E : ℤ)
   rw [dotProduct_smul, hprimitive]
   simp
 obtain ⟨a, ha⟩ :=
   (L.map (ZgZ x)).isAddCyclic_iff_exists_zmultiples_eq_top.mp inferInstance
 have ha0 : a ≠ 0 := by
   intro hz
   have hbad := hEimage
   rw [← ha, hz] at hbad
   have heq : (E : ℤ) = 0 := by simpa using hbad
   exact (Nat.ne_of_gt hE) (by exact_mod_cast heq)
 have hmap : L.map (ZgZ x) = AddSubgroup.zmultiples (a.natAbs : ℤ) :=
   ((Int.zmultiples_natAbs a).trans ha).symm
 have hdivE : (a.natAbs : ℤ) ∣ (E : ℤ) := by
   apply Int.mem_zmultiples_iff.mp
   rw [← hmap]
   exact hEimage
 refine ⟨a.natAbs, Int.natAbs_pos.mpr ha0, by exact_mod_cast hdivE, hmap, ?_, ?_⟩
 · intro v hv
   apply Int.mem_zmultiples_iff.mp
   rw [← hmap]
   exact AddSubgroup.mem_map.mpr ⟨v, hv, rfl⟩
 · have hgmem : (a.natAbs : ℤ) ∈ L.map (ZgZ x) := by
    rw [hmap]
    exact AddSubgroup.mem_zmultiples _
   obtain ⟨u, hu, heq⟩ := AddSubgroup.mem_map.mp hgmem
   exact ⟨u, hu, heq⟩
theorem ZeQ (H : AddSubgroup ℤ) :
  H = AddSubgroup.zmultiples (H.index : ℤ) := by
 obtain ⟨a, ha⟩ := H.isAddCyclic_iff_exists_zmultiples_eq_top.mp inferInstance
 have hindex : H.index = a.natAbs := by rw [← ha, Int.index_zmultiples]
 rw [hindex, Int.zmultiples_natAbs]
 exact ha.symm
noncomputable def ZM (L : AddSubgroup (ι → ℤ)) (x : ι → ℤ) : ℕ :=
 (L.map (ZgZ x)).index
theorem Znh (L : AddSubgroup (ι → ℤ)) (x : ι → ℤ) :
  L.map (ZgZ x) = AddSubgroup.zmultiples (ZM L x : ℤ) :=
 ZeQ _
theorem Zeg (L : AddSubgroup (ι → ℤ)) (x v : ι → ℤ)
  (hv : v ∈ L) : (ZM L x : ℤ) ∣ dotProduct x v := by
 apply Int.mem_zmultiples_iff.mp
 rw [← Znh]
 exact AddSubgroup.mem_map.mpr ⟨v, hv, rfl⟩
theorem ZjL (L : AddSubgroup (ι → ℤ)) (x : ι → ℤ) :
  ∃ u ∈ L, dotProduct x u = (ZM L x : ℤ) := by
 have hgmem : (ZM L x : ℤ) ∈ L.map (ZgZ x) := by
  rw [Znh]
  exact AddSubgroup.mem_zmultiples _
 exact AddSubgroup.mem_map.mp hgmem
theorem ZaM
  (L : AddSubgroup (ι → ℤ)) (x z : ι → ℤ) (hprimitive : dotProduct x z = 1)
  (E : ℕ) (hE : 0 < E) (hcontain : ∀ v : ι → ℤ, E • v ∈ L) :
  0 < ZM L x ∧ ZM L x ∣ E := by
 obtain ⟨g, hg, hdiv, himage, _, _⟩ :=
  Zlv L x z hprimitive E hE hcontain
 have heq : ZM L x = g := by
  unfold ZM
  rw [himage, Int.index_zmultiples, Int.natAbs_natCast]
 exact heq.symm ▸ ⟨hg, hdiv⟩
end Problem355.ZcC
end OAI
end
section
namespace OAI
namespace Problem355.ZcT
open ZcC
theorem Zeh
   (S : Finset (Fin 3 → ℤ)) (L : AddSubgroup (Fin 3 → ℤ))
   (C : Matrix (Fin 3) (Fin 3) ℤ)
   (B R b e k : ℕ) (hB : B.Prime) (hR : B ^ e ≤ R) (hek : e ≤ k)
   (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
   (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
    (P : Matrix _ _ _) * Matrix.diagonal
     ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
      (Q : Matrix _ _ _))
   (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
   (hprimitive : ∀ x ∈ S, ∃ z : Fin 3 → ℤ, dotProduct x z = 1)
   (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
   (hrows : ∀ i, C i ∈ L) :
   ∑ x ∈ S, (ZM L x : ℝ) ^ 3 ≤
    128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
 apply ZeI S (ZM L) C
   B R b e k hB hR hek P Q hC hbox
 · intro x hx
   obtain ⟨z, hz⟩ := hprimitive x hx
   exact (ZaM L x z hz (B ^ e)
    (pow_pos hB.pos _) hcontain).2
 · intro x hx i
   simpa only [Matrix.mulVec, dotProduct_comm] using
    Zeg L x (C i) (hrows i)
end Problem355.ZcT
end OAI
end
section
namespace OAI
namespace Problem355.Zqx
open scoped BigOperators
theorem ZnI {α : Type*} (S : Finset α)
  (f g len J : α → ℝ) (R I A C : ℝ)
  (hR : 0 < R) (hI : 0 < I) (hA : 0 ≤ A)
  (hg : ∀ x ∈ S, 0 < g x) (hlen : ∀ x ∈ S, R ≤ len x)
  (hJ : ∀ x ∈ S, J x = I * len x / g x)
  (hf : ∀ x ∈ S, f x ≤ A / (J x) ^ 3)
  (hmoment : ∑ x ∈ S, (g x) ^ 3 ≤ C * R ^ 3 * I) :
  ∑ x ∈ S, f x ≤ A * C / I ^ 2 := by
 have hpoint : ∀ x ∈ S, f x ≤ (A / (I ^ 3 * R ^ 3)) * (g x) ^ 3 := by
  intro x hx
  have hgx := hg x hx
  have hlx : 0 < len x := lt_of_lt_of_le hR (hlen x hx)
  have hlen3 : R ^ 3 ≤ (len x) ^ 3 := pow_le_pow_left₀ hR.le (hlen x hx) 3
  have hden : I ^ 3 * R ^ 3 ≤ I ^ 3 * (len x) ^ 3 :=
   mul_le_mul_of_nonneg_left hlen3 (pow_nonneg hI.le 3)
  calc
   f x ≤ A / (J x) ^ 3 := hf x hx
   _ = (A * (g x) ^ 3) / (I ^ 3 * (len x) ^ 3) := by
    rw [hJ x hx]
    field_simp
   _ ≤ (A * (g x) ^ 3) / (I ^ 3 * R ^ 3) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
   _ = (A / (I ^ 3 * R ^ 3)) * (g x) ^ 3 := by ring
 calc
  (∑ x ∈ S, f x) ≤ ∑ x ∈ S, (A / (I ^ 3 * R ^ 3)) * (g x) ^ 3 :=
   Finset.sum_le_sum hpoint
  _ = (A / (I ^ 3 * R ^ 3)) * ∑ x ∈ S, (g x) ^ 3 := by rw [Finset.mul_sum]
  _ ≤ (A / (I ^ 3 * R ^ 3)) * (C * R ^ 3 * I) :=
   mul_le_mul_of_nonneg_left hmoment (by positivity)
  _ = A * C / I ^ 2 := by
   field_simp
end Problem355.Zqx
end OAI
end
section
namespace OAI
namespace Problem355.Zdb
open scoped BigOperators Matrix
open ZcC Zo
theorem Zha
  (S : Finset (Fin 3 → ℤ)) (L : AddSubgroup (Fin 3 → ℤ))
  (C : Matrix (Fin 3) (Fin 3) ℤ)
  (B R b e k : ℕ) (hB : B.Prime) (hR : B ^ e ≤ 2 * R) (hek : e ≤ k)
  (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
  (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
   (P : Matrix _ _ _) * Matrix.diagonal
    ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
     (Q : Matrix _ _ _))
  (hnorm : ∀ x ∈ S, ‖toEuclidean x‖ < 2 * (R : ℝ))
  (hprimitive : ∀ x ∈ S, IsPrimitive x)
  (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
  (hrows : ∀ i, C i ∈ L) :
  ∑ x ∈ S, (ZM L x : ℝ) ^ 3 ≤
   1024 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
 have hbox : ∀ x ∈ S, ∀ i, -((2 * R : ℕ) : ℤ) ≤ x i ∧
   x i ≤ ((2 * R : ℕ) : ℤ) := by
  intro x hx i
  have hcoord : |(x i : ℝ)| ≤ ‖toEuclidean x‖ := by
   change ‖(toEuclidean x).ofLp i‖ ≤ ‖toEuclidean x‖
   exact PiLp.norm_apply_le _ _
  have hbound : |(x i : ℝ)| ≤ (2 * R : ℕ) := by
   push_cast
   exact hcoord.trans (hnorm x hx).le
  have hz : |x i| ≤ ((2 * R : ℕ) : ℤ) := by exact_mod_cast hbound
  exact abs_le.mp hz
 have hm := ZcT.Zeh
  S L C B (2 * R) b e k hB hR hek P Q hC hbox
  (fun x hx => (ZB x).mp (hprimitive x hx))
  hcontain hrows
 convert hm using 1
 push_cast
 ring
private lemma Zoe (W N J : ℝ) :
  W * (9 * Real.pi * (4 * N) ^ 2 / J) ^ 3 =
   (W * (144 * Real.pi) ^ 3 * N ^ 6) / J ^ 3 := by
 ring
theorem ZhS {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (hdim : Module.finrank ℝ E = 2)
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (T : Finset (Fin 3 → L)) (W : (Fin 3 → L) → ℝ)
  (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
  (hW : ∀ a ∈ T, W a ≤ W₀)
  (hshort : ∀ a ∈ T, ∀ i, ‖(a i : E)‖ ≤ 4 * N)
  (hpair : ∀ a ∈ T, ∃ i j : Fin 3,
   LinearIndependent ℝ ![(a i : E), (a j : E)]) :
  (∑ a ∈ T, W a) ≤ (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) /
   ZLattice.covolume L ^ 3 := by
 have hc := Zfj.ZcU hdim L T (4 * N)
  (by positivity) hshort hpair
 generalize hJ : ZLattice.covolume L MeasureTheory.volume = J at hc ⊢
 calc
  (∑ a ∈ T, W a) ≤ ∑ _a ∈ T, W₀ := Finset.sum_le_sum hW
  _ = W₀ * (T.card : ℝ) := by simp [mul_comm]
  _ ≤ W₀ * (9 * Real.pi * (4 * N) ^ 2 / J) ^ 3 :=
   mul_le_mul_of_nonneg_left hc hW₀
  _ = _ := Zoe W₀ N (J)
theorem ZjM
  (x z : Fin 3 → ℤ) (hz : dotProduct x z = 1)
  (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℕ) (hE : 0 < E)
  (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L)
  (T : Finset (Fin 3 → Ze.ZG x L))
  (W : (Fin 3 → Ze.ZG x L) → ℝ)
  (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
  (hW : ∀ a ∈ T, W a ≤ W₀)
  (hshort : ∀ a ∈ T, ∀ i,
   ‖(a i : Ze.ZQ x)‖ ≤ 4 * N)
  (hpair : ∀ a ∈ T, ∃ i j : Fin 3,
   LinearIndependent ℝ ![(a i : Ze.ZQ x),
    (a j : Ze.ZQ x)]) :
  (∑ a ∈ T, W a) ≤ (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) /
   ZLattice.covolume (Ze.ZG x L) ^ 3 := by
 let := Ze.ZbC x z hz L
  (E : ℤ) (by exact_mod_cast Nat.ne_of_gt hE)
  (by simpa only [Nat.cast_smul_eq_nsmul] using hcontain)
 exact ZhS (Ze.Zeb x z hz)
  (Ze.ZG x L) T W N W₀ hN hW₀ hW hshort hpair
theorem Zei
  (x : Fin 3 → ℤ) (hx : IsPrimitive x)
  (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℕ) (hE : 0 < E)
  (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
  ZLattice.covolume (Ze.ZG x L) =
   (L.toAddSubgroup.index : ℝ) * ‖toEuclidean x‖ /
    (ZM L.toAddSubgroup x : ℝ) := by
 obtain ⟨z, hz⟩ := (ZB x).mp hx
 have hg := (ZaM L.toAddSubgroup x z hz E hE hcontain).1
 obtain ⟨u, hu, hval⟩ := ZjL L.toAddSubgroup x
 have hc := Ze.Zis x z hz L (E : ℤ)
  (by exact_mod_cast Nat.ne_of_gt hE)
  (by simpa only [Nat.cast_smul_eq_nsmul] using hcontain)
  (ZM L.toAddSubgroup x : ℤ) (by exact_mod_cast hg)
  (fun v => Zeg L.toAddSubgroup x v v.property)
  ⟨u, hu⟩ hval
 simpa only [Int.cast_natCast, Ze.Zp,
  Zo.toEuclidean] using hc
end Problem355.Zdb
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZaE
open Matrix Zo ZcC
def Zem {h : ℕ} (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
  Matrix (Fin 3) (Fin 3) ℤ :=
 C.map (fun z => (z.val : ℤ))
@[simp] theorem Zgj {h : ℕ} [NeZero h]
  (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
  (Zem C).map (Int.castRingHom (ZMod h)) = C := by
 ext i j
 simp [Zem]
abbrev Zix {h : ℕ} (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
  Submodule ℤ (Fin 3 → ℤ) :=
 (Zah.ZZ h C).toIntSubmodule
variable {B k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}
theorem ZnJ (hB : B.Prime) (i : Fin 3) :
  Zem C i ∈ Zix C := by
 let : NeZero B := ⟨hB.ne_zero⟩
 exact Zah.ZdE (B ^ k)
  (Zem C) C 1 (by simpa only [Matrix.one_mul] using Zgj C) i
theorem Ziy (d : Zj B k C) (hB : B.Prime) :
  (Zem C).map (Int.castRingHom (ZMod (B ^ k))) =
   (d.left : Matrix _ _ _) * Matrix.diagonal
    ![1, (B : ZMod (B ^ k)) ^ d.b, (B : ZMod (B ^ k)) ^ d.e] *
     (d.right : Matrix _ _ _) := by
 let : NeZero B := ⟨hB.ne_zero⟩
 rw [Zgj]
 simpa only [Nat.cast_pow] using d.diagonalization
theorem ZpS (d : Zj B k C) (hB : B.Prime) :
  (Zix C).toAddSubgroup.index = B ^ (d.b + d.e) := by
 change (Zah.ZZ (B ^ k) C).index = _
 rw [d.ZoJ hB.ne_zero, pow_add]
theorem Zkl (d : Zj B k C) (v : Fin 3 → ℤ) :
  (B ^ d.e) • v ∈ Zix C :=
 d.Zkj v
theorem Zmf (d : Zj B k C) {q : ℕ}
  (hcop : (B ^ k).Coprime q) :
  IsUnit (((B ^ d.e : ℕ) : ℤ) : ZMod q) := by
 have he : (B ^ d.e).Coprime q :=
  hcop.of_dvd_left (Nat.pow_dvd_pow B d.e_le_k)
 simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime (B ^ d.e) q).mpr he
theorem Zqp (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hA : A.map (Int.castRingHom (ZMod (B ^ k))) ∈ ZS.Zbl C)
  (i : Fin 3) : A i ∈ Zix C :=
 ZeB.ZaV (B ^ k) C A hA i
end Problem355.ZaE
end
end OAI
end
section
namespace OAI
namespace Problem355.Zmz
variable {ι : Type*} [DecidableEq ι]
theorem ZkR {R : Type*} [CommRing R]
  (v : ι → R) (i j k : ι) (hki : k ≠ i) (hkj : k ≠ j)
  (hv : v ∈ Submodule.span R {Pi.single i (1 : R) - Pi.single j 1}) :
  v k = 0 := by
 obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
 have hk := congrFun ha k
 simpa [hki, hkj, Ne.symm hki, Ne.symm hkj] using hk.symm
theorem Zlw (q : ℕ) (x : ι → ℤ)
  (i j k : ι) (hki : k ≠ i) (hkj : k ≠ j)
  (hx : (fun t => (x t : ZMod q)) ∈
   Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1}) :
  (q : ℤ) ∣ x k := by
 exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x k) q).mp
  (ZkR _ i j k hki hkj hx)
theorem ZjN (q : ℕ) (x : ι → ℤ)
  (i j k : ι) (hki : k ≠ i) (hkj : k ≠ j) (hxk : x k ≠ 0)
  (hx : (fun t => (x t : ZMod q)) ∈
   Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1}) :
  q ≤ (x k).natAbs := by
 simpa using Int.natAbs_le_of_dvd_ne_zero
  (Zlw q x i j k hki hkj hx) hxk
theorem Ziz
   (S : Finset (Fin 3 → ℤ)) (R q : ℕ) (hq : 0 < q)
   (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
   (hbox : ∀ x ∈ S, ∀ t, -(R : ℤ) ≤ x t ∧ x t ≤ (R : ℤ))
   (hnonzero : ∀ x ∈ S, x k ≠ 0)
   (hline : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
    Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1}) :
   (S.card : ℝ) ≤ 64 * (R : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
 classical
 rcases S.eq_empty_or_nonempty with hS | ⟨x, hx⟩
 · simp [hS]; positivity
 have hheight : (x k).natAbs ≤ R := by
   have h := abs_le.mpr (hbox x hx k)
   rw [← Int.natCast_natAbs] at h
   exact_mod_cast h
 have hqR : q ≤ R :=
   (ZjN q x i j k hki hkj (hnonzero x hx) (hline x hx)).trans hheight
 let : NeZero q := ⟨by omega⟩
 let v : Fin 3 → ZMod q := Pi.single i (1 : ZMod q) - Pi.single j 1
 let T := Finset.univ.image (fun a : ZMod q => a • v)
 have hc : T.card ≤ q := Finset.card_image_le.trans_eq (by simp)
 have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
 have h := Zkz.ZbE S R q hq hqR T
   ((q : ℝ)^2) (by positivity) hbox (fun y hy => by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hline y hy)
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩) (by
     rw [show (q : ℝ)^3 / q^2 = q by field_simp]
     exact_mod_cast hc)
 norm_num at h ⊢
 exact h
end Problem355.Zmz
end OAI
end
section
namespace OAI
noncomputable section
open MeasureTheory
namespace Problem355.ZcN
theorem Zrh {X I h q r g W : ℝ}
  (hI : 0 < I) (hq : 0 < q) (hr : 0 < r) (hg : 0 < g)
  (hW : 0 ≤ W) (hpairing : g ^ 3 ≤ I * h ^ 2) :
  W * (9 * Real.pi * X ^ 2 / (q * (I * r / g))) ^ 3 ≤
   W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2 * r ^ 3) := by
 have hid : W * (9 * Real.pi * X ^ 2 / (q * (I * r / g))) ^ 3 =
   (W * (9 * Real.pi) ^ 3 * X ^ 6 / (q ^ 3 * I ^ 3 * r ^ 3)) * g ^ 3 := by
  field_simp
 rw [hid]
 calc
  (W * (9 * Real.pi) ^ 3 * X ^ 6 / (q ^ 3 * I ^ 3 * r ^ 3)) * g ^ 3 ≤
    (W * (9 * Real.pi) ^ 3 * X ^ 6 / (q ^ 3 * I ^ 3 * r ^ 3)) * (I * h ^ 2) :=
   mul_le_mul_of_nonneg_left hpairing (by positivity)
  _ = W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2 * r ^ 3) := by
   field_simp
theorem ZpT (S : Finset (Fin 3 → ℤ)) (R X I h q W : ℝ)
  (hR : 1 ≤ R) (hI : 0 < I) (hq : 0 < q) (hW : 0 ≤ W)
  (g F : (Fin 3 → ℤ) → ℝ)
  (hshell : ∀ x ∈ S, R ≤ ‖Zs.Zw x‖ ∧
   ‖Zs.Zw x‖ ≤ 2 * R)
  (hg : ∀ x ∈ S, 0 < g x)
  (hpairing : ∀ x ∈ S, g x ^ 3 ≤ I * h ^ 2)
  (hF : ∀ x ∈ S, F x ≤
   W * (9 * Real.pi * X ^ 2 /
    (q * (I * ‖Zs.Zw x‖ / g x))) ^ 3) :
  ∑ x ∈ S, F x ≤
   125 * W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2) := by
 have hRp : 0 < R := by linarith
 let C := W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 /
  (q ^ 3 * I ^ 2 * R ^ 3)
 have hC : 0 ≤ C := by dsimp [C]; positivity
 have hbound (x : Fin 3 → ℤ) (hx : x ∈ S) : F x ≤ C := by
  have hr : 0 < ‖Zs.Zw x‖ := hRp.trans_le (hshell x hx).1
  refine (hF x hx).trans ((Zrh hI hq hr (hg x hx) hW (hpairing x hx)).trans ?_)
  dsimp [C]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr
  exact (hshell x hx).1
 have hc : (S.card : ℝ) ≤ 125 * R ^ 3 :=
  Zs.ZbU hR S
   (fun x hx i => (Zs.Zfr x i).trans (hshell x hx).2)
 calc
  ∑ x ∈ S, F x ≤ ∑ _x ∈ S, C := Finset.sum_le_sum hbound
  _ = (S.card : ℝ) * C := by simp
  _ ≤ (125 * R ^ 3) * C := mul_le_mul_of_nonneg_right hc hC
  _ = 125 * W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2) := by
   dsimp [C]
   field_simp
end Problem355.ZcN
end
end OAI
end
section
namespace OAI
namespace Problem355.Zfl
open scoped BigOperators
variable {ι : Type*} [Fintype ι]
theorem ZpU (q : ℕ) (x z : ι → ℤ)
   (hz : ∑ i, x i * z i = 1) (v : ι → ZMod q)
   (hv : ∑ i, (x i : ZMod q) * v i = 0) :
   ∃ w : ι → ℤ, (∑ i, x i * w i = 0) ∧
    ∀ i, (w i : ZMod q) = v i := by
 classical
 choose a ha using fun i => ZMod.intCast_surjective (v i)
 let t : ℤ := ∑ i, x i * a i
 have ht : (t : ZMod q) = 0 := by
   simpa [t, ha] using hv
 refine ⟨fun i => a i - t * z i, ?_, ?_⟩
 · calc
    (∑ i, x i * (a i - t * z i)) =
     (∑ i, x i * a i) - t * (∑ i, x i * z i) := by
      simp only [mul_sub, Finset.sum_sub_distrib,
       Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by rw [hz]; simp [t]
 · intro i
   simp [ht, ha]
theorem Zlx (q : ℕ) (x z : ι → ℤ)
  (hz : ∑ i, x i * z i = 1) (E : ℤ)
  (hE : IsUnit (E : ZMod q)) (v : ι → ZMod q)
  (hv : ∑ i, (x i : ZMod q) * v i = 0) :
  ∃ w : ι → ℤ, (∑ i, x i * w i = 0) ∧
   ∀ i, ((E * w i : ℤ) : ZMod q) = v i := by
 obtain ⟨u, hu⟩ := hE
 let v' : ι → ZMod q := fun i => (↑(u⁻¹) : ZMod q) * v i
 have hv' : ∑ i, (x i : ZMod q) * v' i = 0 := by
  calc
   (∑ i, (x i : ZMod q) * v' i) =
    (↑(u⁻¹) : ZMod q) * ∑ i, (x i : ZMod q) * v i := by
     simp only [v', Finset.mul_sum]
     apply Finset.sum_congr rfl
     intro i hi
     ring
   _ = 0 := by rw [hv, mul_zero]
 obtain ⟨w, hw, hred⟩ := ZpU q x z hz v' hv'
 refine ⟨w, hw, ?_⟩
 intro i
 rw [Int.cast_mul, hred, ← hu]
 simp [v', ← mul_assoc]
theorem ZnK (q : ℕ) (x z : ι → ℤ)
   (hz : ∑ i, x i * z i = 1) (E : ℤ)
   (hE : IsUnit (E : ZMod q)) (Λ : Submodule ℤ (ι → ℤ))
   (hΛ : ∀ w : ι → ℤ, E • w ∈ Λ) (v : ι → ZMod q)
   (hv : ∑ i, (x i : ZMod q) * v i = 0) :
   ∃ w : ι → ℤ, w ∈ Λ ∧ (∑ i, x i * w i = 0) ∧
    ∀ i, (w i : ZMod q) = v i := by
 obtain ⟨w, hw, hred⟩ := Zlx q x z hz E hE v hv
 refine ⟨E • w, hΛ w, ?_, ?_⟩
 · change (∑ i, x i * (E * w i)) = 0
   calc
    (∑ i, x i * (E * w i)) = E * ∑ i, x i * w i := by
     rw [Finset.mul_sum]
     apply Finset.sum_congr rfl
     intro i hi
     ring
    _ = 0 := by rw [hw, mul_zero]
 · exact hred
theorem ZeR (q : ℕ) [Nontrivial (ZMod q)]
  (x z : ι → ℤ) (hz : ∑ i, x i * z i = 1) :
  (fun i => (x i : ZMod q)) ≠ 0 := by
 intro hx
 have hcast : (∑ i, (x i : ZMod q) * (z i : ZMod q)) = 1 := by
  simpa using congrArg (fun a : ℤ => (a : ZMod q)) hz
 have hxi : ∀ i, (x i : ZMod q) = 0 := fun i => congrFun hx i
 simp [hxi] at hcast
end Problem355.Zfl
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZL
variable {ι K : Type*} [Fintype ι] [Field K]
theorem Zkm (x d : ι → K) (hx : x ≠ 0)
   (hd : ¬ ∃ a : K, d = a • x) :
   ∃ v : ι → K, dotProduct x v = 0 ∧ dotProduct d v = 1 := by
 classical
 obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
   by_contra! h
   apply hx
   funext i
   exact h i
 obtain ⟨j, hj⟩ : ∃ j, d j ≠ (d i / x i) * x j := by
   by_contra! h
   apply hd
   refine ⟨d i / x i, ?_⟩
   funext j
   exact h j
 let u : ι → K := Pi.single j 1 - (x j / x i) • Pi.single i 1
 have hxu : dotProduct x u = 0 := by
   dsimp only [u]
   rw [dotProduct_sub, dotProduct_smul]
   simp only [dotProduct_single, mul_one, smul_eq_mul]
   rw [div_mul_cancel₀ _ hi, sub_self]
 have hduval : dotProduct d u = d j - (d i / x i) * x j := by
   dsimp only [u]
   rw [dotProduct_sub, dotProduct_smul]
   simp only [dotProduct_single, mul_one, smul_eq_mul]
   ring
 have hdu : dotProduct d u ≠ 0 := by
   rw [hduval]
   exact sub_ne_zero.mpr hj
 refine ⟨(dotProduct d u)⁻¹ • u, ?_, ?_⟩
 · rw [dotProduct_smul, hxu, smul_zero]
 · rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hdu]
def Zja (q : ℕ) (d : ι → ZMod q) : (ι → ℤ) →+ ZMod q where
 toFun u := dotProduct d (fun i => (u i : ZMod q))
 map_zero' := by simp [dotProduct]
 map_add' u v := by
  simp only [Pi.add_apply, Int.cast_add, dotProduct, mul_add, Finset.sum_add_distrib]
theorem ZdH (q : ℕ) [Fact q.Prime]
  (x d : ι → ZMod q) (hx : x ≠ 0)
  (hd : ¬ ∃ a : ZMod q, d = a • x)
  (L : AddSubgroup (ι → ℤ))
  (hL : ∀ v : ι → ZMod q, dotProduct x v = 0 →
   ∃ w : L, ∀ i, ((w : ι → ℤ) i : ZMod q) = v i) :
  Function.Surjective ((Zja q d).comp L.subtype) := by
 obtain ⟨v, hxv, hdv⟩ := Zkm x d hx hd
 intro a
 have hxa : dotProduct x (a • v) = 0 := by
  rw [dotProduct_smul, hxv, smul_zero]
 obtain ⟨w, hw⟩ := hL (a • v) hxa
 refine ⟨w, ?_⟩
 change dotProduct d (fun i => ((w : ι → ℤ) i : ZMod q)) = a
 simp only [hw]
 rw [dotProduct_smul, hdv, smul_eq_mul, mul_one]
theorem Zly (q : ℕ) [Fact q.Prime]
  (x d : ι → ZMod q) (hx : x ≠ 0)
  (hd : ¬ ∃ a : ZMod q, d = a • x)
  (L : AddSubgroup (ι → ℤ))
  (hL : ∀ v : ι → ZMod q, dotProduct x v = 0 →
   ∃ w : L, ∀ i, ((w : ι → ℤ) i : ZMod q) = v i) :
  (((Zja q d).comp L.subtype).ker).index = q := by
 rw [AddSubgroup.index_ker,
  AddMonoidHom.range_eq_top.mpr
   (ZdH q x d hx hd L hL),
  AddSubgroup.card_top]
 simpa only [Nat.card_eq_fintype_card] using ZMod.card q
end Problem355.ZL
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZL
variable {ι K : Type*} [Fintype ι] [Field K]
def ZC (i j : ι) : ι → K := by
 classical
 exact Pi.single i 1 - Pi.single j 1
@[simp] theorem Zkn (i j : ι) (v : ι → K) :
  dotProduct (ZC i j) v = v i - v j := by
 classical
 simp only [ZC, sub_dotProduct, single_dotProduct, one_mul]
omit [Fintype ι] in
theorem ZhT {i j : ι} (hij : i ≠ j) :
  (ZC i j : ι → K) ≠ 0 := by
 classical
 intro h
 have hi := congrFun h i
 simp [ZC, hij] at hi
omit [Fintype ι] in
theorem ZmU (x d : ι → K) (hd : d ≠ 0)
  (hx : ¬ ∃ a : K, x = a • d) : ¬ ∃ a : K, d = a • x := by
 rintro ⟨a, ha⟩
 have hapos : a ≠ 0 := by
  intro hz
  apply hd
  simpa [hz] using ha
 apply hx
 refine ⟨a⁻¹, ?_⟩
 rw [ha, smul_smul, inv_mul_cancel₀ hapos, one_smul]
def Zbe (q : ℕ) [Fact q.Prime] (L : AddSubgroup (ι → ℤ)) (i j : ι) :
  AddSubgroup L :=
 ((Zja q (ZC i j)).comp L.subtype).ker
@[simp] theorem ZiA (q : ℕ) [Fact q.Prime] (L : AddSubgroup (ι → ℤ))
  (i j : ι) (v : L) :
  v ∈ Zbe q L i j ↔
   (((v : ι → ℤ) i : ℤ) : ZMod q) = (((v : ι → ℤ) j : ℤ) : ZMod q) := by
 change dotProduct (ZC i j)
  (fun a => (((v : ι → ℤ) a : ℤ) : ZMod q)) = 0 ↔ _
 rw [Zkn, sub_eq_zero]
theorem Zhx (q : ℕ) [Fact q.Prime]
  (x : ι → ZMod q) (hx : x ≠ 0) (i j : ι) (hij : i ≠ j)
  (hspan : ¬ ∃ a : ZMod q, x = a • ZC i j)
  (L : AddSubgroup (ι → ℤ))
  (hL : ∀ v : ι → ZMod q, dotProduct x v = 0 →
   ∃ w : L, ∀ a, ((w : ι → ℤ) a : ZMod q) = v a) :
  (Zbe q L i j).index = q := by
 exact Zly q x (ZC i j) hx
  (ZmU x (ZC i j)
   (ZhT hij) hspan) L hL
end Problem355.ZL
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Znc
open scoped LinearAlgebra.Projectivization
variable {K V A : Type*} [Field K] [Finite K]
 [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 [AddCommGroup A]
def Zqw (x : Fin 3 → K) : (Fin 3 → K) →ₗ[K] K := dotProductBilin K K x
end Problem355.Znc
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZfR
abbrev Vector := Fin 3 → ℤ
def Zmg (x : Vector) : Vector →ₗ[ℤ] ℤ := dotProductBilin ℤ ℤ x
def ZfW (Λ : Submodule ℤ Vector) (x : Vector) : Submodule ℤ Vector :=
 Λ ⊓ (Zmg x).ker
def Zcj (q : ℕ) (x : Vector) : Fin 3 → ZMod q := fun i => (x i : ZMod q)
@[simp] theorem ZrJ (Λ : Submodule ℤ Vector) (x v : Vector) :
 v ∈ ZfW Λ x ↔ v ∈ Λ ∧ dotProduct x v = 0 := Iff.rfl
def ZqW (q : ℕ) [Fact q.Prime] (Λ : Submodule ℤ Vector) (x : Vector) :
  ZfW Λ x →+ (Znc.Zqw (Zcj q x)).ker where
 toFun v := ⟨fun i => ((v : Vector) i : ZMod q), by
  change dotProduct (Zcj q x) (fun i => ((v : Vector) i : ZMod q)) = 0
  have h := congrArg (fun z : ℤ => (z : ZMod q)) v.property.2
  simpa [Zmg, Zcj, dotProduct] using h⟩
 map_zero' := by ext i; simp
 map_add' u v := by ext i; simp
@[simp] theorem ZrD (q : ℕ) [Fact q.Prime] (Λ : Submodule ℤ Vector) (x : Vector)
 (v : ZfW Λ x) (i : Fin 3) :
 ((ZqW q Λ x v : (Znc.Zqw (Zcj q x)).ker) :
  Fin 3 → ZMod q) i = ((v : Vector) i : ZMod q) := rfl
theorem Zmh (q : ℕ) [Nontrivial (ZMod q)] (x z : Vector)
  (hz : dotProduct x z = 1) : Zcj q x ≠ 0 :=
 Zfl.ZeR q x z hz
open scoped LinearAlgebra.Projectivization
theorem Zmi (q : ℕ) [Fact q.Prime] (Λ : Submodule ℤ Vector)
  (x z : Vector) (hz : dotProduct x z = 1) (E : ℤ) (hE : IsUnit (E : ZMod q))
  (hΛ : ∀ w : Vector, E • w ∈ Λ) (i j : Fin 3) (hij : i ≠ j)
  (hspan : ¬ ∃ a : ZMod q,
   Zcj q x = a • ZL.ZC i j) :
  (ZL.Zbe q (ZfW Λ x).toAddSubgroup i j).index = q := by
 apply ZL.Zhx q (Zcj q x)
  (Zmh q x z hz) i j hij hspan
 intro v hv
 obtain ⟨w, hwΛ, hwx, hwred⟩ :=
  Zfl.ZnK q x z hz E hE Λ hΛ v hv
 exact ⟨⟨w, hwΛ, hwx⟩, hwred⟩
end Problem355.ZfR
end
end OAI
end
section
namespace OAI
namespace Problem355.ZkA
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E]
theorem Zqq (Γ L : Submodule ℤ E) [DiscreteTopology L]
  (hΓL : Γ ≤ L) : DiscreteTopology Γ := by
 apply DiscreteTopology.of_continuous_injective
  (f := Submodule.inclusion hΓL) _ (Submodule.inclusion_injective hΓL)
 change Continuous (fun x : Γ => (⟨x.1, hΓL x.2⟩ : L))
 fun_prop
theorem Zof (Γ L : Submodule ℤ E) (x : E) (hx : x ∈ L) :
  Γ.toAddSubgroup.relIndex L.toAddSubgroup • x ∈ Γ := by
 exact (Γ.toAddSubgroup.addSubgroupOf L.toAddSubgroup).nsmul_index_mem
  (⟨x, hx⟩ : L.toAddSubgroup)
theorem Zhb [NormedSpace ℝ E] (Γ L : Submodule ℤ E)
  [DiscreteTopology Γ] [DiscreteTopology L] [IsZLattice ℝ L]
  (hindex : Γ.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
  IsZLattice ℝ Γ := by
 constructor
 apply top_unique
 rw [← IsZLattice.span_top (K := ℝ) (L := L)]
 apply Submodule.span_le.mpr
 intro x hx
 change x ∈ Submodule.span ℝ (Γ : Set E)
 have hmem := Submodule.subset_span (R := ℝ) (Zof Γ L x hx)
 have hreal : (Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≠ 0 := by
  exact_mod_cast hindex
 have hscaled := (Submodule.span ℝ (Γ : Set E)).smul_mem
  (Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ)⁻¹ hmem
 simpa only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
  inv_mul_cancel₀ hreal, one_smul] using hscaled
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 [MeasurableSpace E] [BorelSpace E]
theorem Zmj (Γ L : Submodule ℤ E)
  [DiscreteTopology Γ] [DiscreteTopology L] [IsZLattice ℝ Γ] [IsZLattice ℝ L]
  (hΓL : Γ ≤ L) :
  ZLattice.covolume Γ =
   (Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L := by
 have hvol := ZLattice.covolume_pos L volume
 exact (div_eq_iff hvol.ne').mp
  (ZLattice.covolume_div_covolume_eq_relIndex' Γ L hΓL)
theorem Zko (hdim : Module.finrank ℝ E = 2)
  (Γ L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (hΓL : Γ ≤ L) (m : ℕ) (hm : 0 < m)
  (hindex : Γ.toAddSubgroup.relIndex L.toAddSubgroup = m)
  (A : Finset (Fin 3 → Γ)) (R : ℝ) (hR : 0 ≤ R)
  (hA : ∀ a ∈ A, ∀ i, ‖(a i : E)‖ ≤ R)
  (hpair : ∀ a ∈ A, ∃ i j : Fin 3,
   LinearIndependent ℝ ![(a i : E), (a j : E)]) :
  (A.card : ℝ) ≤
   (9 * Real.pi * R ^ 2 / ((m : ℝ) * ZLattice.covolume L)) ^ 3 := by
 let : DiscreteTopology Γ := Zqq Γ L hΓL
 let : IsZLattice ℝ Γ := Zhb Γ L (by omega)
 have h := Zfj.ZcU hdim Γ A R hR hA hpair
 rwa [Zmj Γ L hΓL, hindex] at h
end Problem355.ZkA
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZfS
open Ze
abbrev Vector := Fin 3 → ℤ
def embedding (x : Vector) (L : Submodule ℤ Vector) :
  Zaq x L →ₗ[ℤ] ZQ x :=
 (ZG x L).subtype.comp (Zbq x L).toLinearMap
theorem embedding_injective (x : Vector) (L : Submodule ℤ Vector) :
  Function.Injective (embedding x L) :=
 (Submodule.subtype_injective _).comp (Zbq x L).injective
@[simp] theorem Zsb (x : Vector) (L : Submodule ℤ Vector)
 (v : Zaq x L) :
 ((embedding x L v : ZQ x) : ZI) = Zp v := rfl
def Zdw (q : ℕ) [Fact q.Prime] (x : Vector)
  (L : Submodule ℤ Vector) (i j : Fin 3) : Submodule ℤ (ZQ x) :=
 ((ZL.Zbe q (Zaq x L).toAddSubgroup i j).map
  (embedding x L).toAddMonoidHom).toIntSubmodule
theorem ZpV (q : ℕ) [Fact q.Prime] (x : Vector)
  (L : Submodule ℤ Vector) (i j : Fin 3) :
  Zdw q x L i j ≤ ZG x L := by
 rintro v ⟨w, hw, rfl⟩
 exact (Zbq x L w).property
theorem Zmk (q : ℕ) [Fact q.Prime]
  (x z : Vector) (hz : dotProduct x z = 1)
  (L : Submodule ℤ Vector) (E : ℤ) (hE : IsUnit (E : ZMod q))
  (hL : ∀ v : Vector, E • v ∈ L) (i j : Fin 3) (hij : i ≠ j)
  (hspan : ¬ ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
    a • ZL.ZC i j) :
  (Zdw q x L i j).toAddSubgroup.relIndex (ZG x L).toAddSubgroup = q := by
 have htop : (⊤ : AddSubgroup (Zaq x L)).map
    (embedding x L).toAddMonoidHom = (ZG x L).toAddSubgroup := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (Zbq x L w).property
  · intro hv
    refine ⟨(Zbq x L).symm ⟨v, hv⟩, trivial, ?_⟩
    exact congrArg (fun w : ZG x L => (w : ZQ x))
     ((Zbq x L).apply_symm_apply ⟨v, hv⟩)
 change ((ZL.Zbe q
  (Zaq x L).toAddSubgroup i j).map (embedding x L).toAddMonoidHom).relIndex
    (ZG x L).toAddSubgroup = q
 rw [← htop, AddSubgroup.relIndex_map_map_of_injective _ _ (embedding_injective x L),
  AddSubgroup.relIndex_top_right]
 exact ZfR.Zmi q L x z hz E hE hL i j hij hspan
def row (q : ℕ) [Fact q.Prime] (x : Vector) (L : Submodule ℤ Vector)
  (i j : Fin 3) (v : Zaq x L)
  (hv : ((v : Vector) i : ZMod q) = ((v : Vector) j : ZMod q)) :
  Zdw q x L i j :=
 ⟨embedding x L v, ⟨v,
  (ZL.ZiA q
   (Zaq x L).toAddSubgroup i j v).mpr hv, rfl⟩⟩
theorem Zpt (q : ℕ) [Fact q.Prime]
  (x z : Vector) (hz : dotProduct x z = 1)
  (L : Submodule ℤ Vector) (E : ℤ) (hE : IsUnit (E : ZMod q))
  (hL : ∀ v : Vector, E • v ∈ L) (i j : Fin 3) (hij : i ≠ j)
  (hspan : ¬ ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
   a • ZL.ZC i j)
  (A : Finset (Fin 3 → Vector)) (R : ℝ) (hR : 0 ≤ R)
  (hrow : ∀ a ∈ A, ∀ k, a k ∈ Zaq x L)
  (hcoord : ∀ a ∈ A, ∀ k, (a k i : ZMod q) = (a k j : ZMod q))
  (hnorm : ∀ a ∈ A, ∀ k, ‖Zp (a k)‖ ≤ R)
  (hpair : ∀ a ∈ A, ∃ k l : Fin 3,
   LinearIndependent ℝ ![Zp (a k), Zp (a l)]) :
  (A.card : ℝ) ≤
   (9 * Real.pi * R ^ 2 / ((q : ℝ) * ZLattice.covolume (ZG x L))) ^ 3 := by
 classical
 have hEne : E ≠ 0 := by
  intro he
  have hu := hE.ne_zero
  simp [he] at hu
 let : IsZLattice ℝ (ZG x L) := ZbC x z hz L E hEne hL
 let T : {a // a ∈ A} → Fin 3 → Zdw q x L i j := fun a k =>
  row q x L i j ⟨a.val k, hrow a.val a.property k⟩ (hcoord a.val a.property k)
 have hTinj : Function.Injective T := by
  intro a b hab
  apply Subtype.ext
  funext k t
  have he := congrArg
   (fun v : Zdw q x L i j => ((v : ZQ x) : ZI) t)
   (congrFun hab k)
  change (a.val k t : ℝ) = (b.val k t : ℝ) at he
  exact_mod_cast he
 have hcard : (A.attach.image T).card = A.card := by
  rw [Finset.card_image_of_injective _ hTinj, Finset.card_attach]
 have hbound := ZkA.Zko
  (Zeb x z hz) (Zdw q x L i j) (ZG x L)
  (ZpV q x L i j) q (Fact.out : q.Prime).pos
  (Zmk q x z hz L E hE hL i j hij hspan)
  (A.attach.image T) R hR
  (by
   intro b hb k
   obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
   exact hnorm a.val a.property k)
  (by
   intro b hb
   obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
   obtain ⟨k, l, hkl⟩ := hpair a.val a.property
   refine ⟨k, l, LinearIndependent.of_comp (ZQ x).subtype ?_⟩
   convert hkl using 1
   ext t
   fin_cases t <;> rfl)
 rwa [hcard] at hbound
end Problem355.ZfS
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZcN
open Ze
theorem ZbY
  (q : ℕ) [Fact q.Prime] (L : Submodule ℤ (Fin 3 → ℤ))
  (E : ℤ) (hE : IsUnit (E : ZMod q)) (hL : ∀ v, E • v ∈ L)
  (i j : Fin 3) (hij : i ≠ j)
  (S : Finset (Fin 3 → ℤ)) (z : (Fin 3 → ℤ) → (Fin 3 → ℤ))
  (hz : ∀ x ∈ S, dotProduct x (z x) = 1)
  (hspan : ∀ x ∈ S, ¬ ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
   a • ZL.ZC i j)
  (A : (Fin 3 → ℤ) → Finset (Fin 3 → Fin 3 → ℤ))
  (weight : (Fin 3 → Fin 3 → ℤ) → ℝ)
  (R X I h W : ℝ) (hR : 1 ≤ R) (hX : 0 ≤ X) (hI : 0 < I) (hW : 0 ≤ W)
  (g : (Fin 3 → ℤ) → ℝ)
  (hshell : ∀ x ∈ S, R ≤ ‖Zs.Zw x‖ ∧
   ‖Zs.Zw x‖ ≤ 2 * R)
  (hg : ∀ x ∈ S, 0 < g x)
  (hpairing : ∀ x ∈ S, g x ^ 3 ≤ I * h ^ 2)
  (hcovol : ∀ x ∈ S, ZLattice.covolume (ZG x L) =
   I * ‖Zs.Zw x‖ / g x)
  (hrow : ∀ x ∈ S, ∀ a ∈ A x, ∀ k, a k ∈ Zaq x L)
  (hcoord : ∀ x ∈ S, ∀ a ∈ A x, ∀ k, (a k i : ZMod q) = (a k j : ZMod q))
  (hnorm : ∀ x ∈ S, ∀ a ∈ A x, ∀ k, ‖Zp (a k)‖ ≤ X)
  (hpair : ∀ x ∈ S, ∀ a ∈ A x, ∃ k l : Fin 3,
   LinearIndependent ℝ ![Zp (a k), Zp (a l)])
  (hweight : ∀ x ∈ S, ∀ a ∈ A x, weight a ≤ W) :
  ∑ x ∈ S, ∑ a ∈ A x, weight a ≤
   125 * W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / ((q : ℝ) ^ 3 * I ^ 2) := by
 have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
 apply ZpT S R X I h q W hR hI hq hW g
  (fun x => ∑ a ∈ A x, weight a) hshell hg hpairing
 intro x hx
 have hc := ZfS.Zpt q x (z x) (hz x hx)
  L E hE hL i j hij (hspan x hx) (A x) X hX
  (hrow x hx) (hcoord x hx) (hnorm x hx) (hpair x hx)
 rw [hcovol x hx] at hc
 calc
  ∑ a ∈ A x, weight a ≤ ∑ _a ∈ A x, W := Finset.sum_le_sum (hweight x hx)
  _ = W * ((A x).card : ℝ) := by simp [mul_comm]
  _ ≤ W * (9 * Real.pi * X ^ 2 /
    ((q : ℝ) * (I * ‖Zs.Zw x‖ / g x))) ^ 3 :=
   mul_le_mul_of_nonneg_left hc hW
end Problem355.ZcN
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zl
open Matrix Ze
abbrev Zi := Matrix (Fin 3) (Fin 3) ℤ
abbrev Zck (x : Fin 3 → ℤ) := {A : Zi // A *ᵥ x = 0}
def ZbZ (x : Fin 3 → ℤ) (A : Zck x) (i : Fin 3) : lattice x :=
 ⟨⟨Zp (A.val i), by
  change Zbm x (Zp (A.val i)) = 0
  rw [Zcf]
  have hi : A.val i ⬝ᵥ x = 0 := congrFun A.property i
  rw [dotProduct_comm] at hi
  exact_mod_cast hi⟩, Zig _⟩
@[simp] theorem ZrT (x : Fin 3 → ℤ) (A : Zck x)
 (i j : Fin 3) : (((ZbZ x A i : lattice x) : ZQ x) : ZI) j =
  (A.val i j : ℝ) := rfl
theorem Zcq (u v : ZI) (s t : Fin 3)
   (hminor : u s * v t - u t * v s ≠ 0) :
   LinearIndependent ℝ ![u, v] := by
 rw [linearIndependent_fin2]
 constructor
 · intro hv
   have hv' : v = 0 := hv
   apply hminor
   simp [hv']
 · intro a ha
   have ha' : a • v = u := ha
   have hs := congrArg (fun w : ZI => w s) ha'
   have ht := congrArg (fun w : ZI => w t) ha'
   change a * v s = u s at hs
   change a * v t = u t at ht
   apply hminor
   rw [← hs, ← ht]
   ring
theorem ZeS
  (x : Fin 3 → ℤ) (A : Zck x) (i j s t : Fin 3)
  (hminor : A.val i s * A.val j t - A.val i t * A.val j s ≠ 0) :
  LinearIndependent ℝ ![(ZbZ x A i : ZQ x), (ZbZ x A j : ZQ x)] := by
 have hm : Zp (A.val i) s * Zp (A.val j) t -
   Zp (A.val i) t * Zp (A.val j) s ≠ 0 := by
  simp only [Znd]
  exact_mod_cast hminor
 apply LinearIndependent.of_comp (ZQ x).subtype
 convert Zcq (Zp (A.val i))
  (Zp (A.val j)) s t hm using 1
 ext a
 fin_cases a <;> rfl
@[simp] theorem ZrE (x : Fin 3 → ℤ) (A : Zck x) (i : Fin 3) :
 ‖ZbZ x A i‖ = ‖Zp (A.val i)‖ := rfl
theorem ZfK
  (x : Fin 3 → ℤ) (A : Zck x) (i : Fin 3)
  {R : ℝ} (hR : 0 ≤ R) (hA : ∀ j, |(A.val i j : ℝ)| ≤ R) :
  ‖ZbZ x A i‖ ≤ Real.sqrt 3 * R := by
 rw [ZrE]
 apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hR)).mp
 rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
 rw [EuclideanSpace.norm_sq_eq]
 calc
  ∑ j, ‖(Zp (A.val i)).ofLp j‖ ^ 2 ≤ ∑ _j : Fin 3, R ^ 2 := by
   apply Finset.sum_le_sum
   intro j _
   apply (sq_le_sq₀ (norm_nonneg _) hR).mpr
   simpa only [Real.norm_eq_abs, Zp, WithLp.ofLp_toLp] using hA j
  _ = 3 * R ^ 2 := by simp
def ZA (A : Zi) (j : Fin 3) : ℝ × ℝ :=
 ((A 0 j : ℝ) / (A 2 j : ℝ), (A 1 j : ℝ) / (A 2 j : ℝ))
theorem Zca
   (A : Zi) (s t : Fin 3)
   (hs : A 2 s ≠ 0) (ht : A 2 t ≠ 0)
   (hne : ZA A s ≠ ZA A t) :
   ∃ i : Fin 3, i ≠ 2 ∧ A i s * A 2 t - A i t * A 2 s ≠ 0 := by
 by_contra h
 push Not at h
 have h₀ := sub_eq_zero.mp (h 0 (by decide))
 have h₁ := sub_eq_zero.mp (h 1 (by decide))
 have hsR : (A 2 s : ℝ) ≠ 0 := by exact_mod_cast hs
 have htR : (A 2 t : ℝ) ≠ 0 := by exact_mod_cast ht
 apply hne
 apply Prod.ext
 · apply (div_eq_div_iff hsR htR).mpr
   exact_mod_cast h₀
 · apply (div_eq_div_iff hsR htR).mpr
   exact_mod_cast h₁
theorem Zgk
  (x : Fin 3 → ℤ) (A : Zck x) (i : Fin 3)
  {N : ℝ} (hN : 0 ≤ N) (hA : ∀ j, |(A.val i j : ℝ)| ≤ 2 * N) :
  ‖ZbZ x A i‖ ≤ 4 * N := by
 have hrow := ZfK x A i (by positivity) hA
 have hsqrt : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
 have hm := mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ 2 * N by positivity)
 exact hrow.trans (by nlinarith)
abbrev ZpW (x : Fin 3 → ℤ) (Γ : Submodule ℤ (ZQ x)) :=
 {A : Zck x // ∀ i, (ZbZ x A i : ZQ x) ∈ Γ}
def Zsf (x : Fin 3 → ℤ) (Γ : Submodule ℤ (ZQ x))
  (A : ZpW x Γ) (i : Fin 3) : Γ :=
 ⟨(ZbZ x A.val i : ZQ x), A.property i⟩
@[simp] theorem Zsk (x : Fin 3 → ℤ) (Γ : Submodule ℤ (ZQ x))
 (A : ZpW x Γ) (i : Fin 3) :
 (Zsf x Γ A i : ZQ x) = (ZbZ x A.val i : ZQ x) := rfl
end Problem355.Zl
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zhk
open Matrix Ze Zo ZcC
open scoped BigOperators
theorem ZbY
  (q : ℕ) [Fact q.Prime] (L : Submodule ℤ (Fin 3 → ℤ))
  (E : ℕ) (hE : 0 < E) (hEq : IsUnit (E : ZMod q))
  (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L)
  (i j : Fin 3) (hij : i ≠ j)
  (S : Finset (Fin 3 → ℤ))
  (hprimitive : ∀ x ∈ S, IsPrimitive x)
  (hspan : ∀ x ∈ S, ¬ ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
   a • ZL.ZC i j)
  (F : (Fin 3 → ℤ) → Finset (Matrix (Fin 3) (Fin 3) ℤ))
  (hF : ∀ x ∈ S, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ k, A k ∈ L)
  (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ)
  (R N I h W₀ : ℝ) (hR : 1 ≤ R) (hN : 0 ≤ N)
  (hI : 0 < I) (hW₀ : 0 ≤ W₀)
  (hindex : (L.toAddSubgroup.index : ℝ) = I)
  (hEbound : (E : ℝ) ^ 3 ≤ I * h ^ 2)
  (hshell : ∀ x ∈ S, R ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ ≤ 2 * R)
  (hequal : ∀ x ∈ S, ∀ A ∈ F x, ∀ k, (A k i : ZMod q) = (A k j : ZMod q))
  (hcoord : ∀ x ∈ S, ∀ A ∈ F x, ∀ k l, |(A k l : ℝ)| ≤ 2 * N)
  (hproj : ∀ x ∈ S, ∀ A ∈ F x, ∃ s t : Fin 3,
   A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
   Zl.ZA A s ≠ Zl.ZA A t)
  (hW : ∀ x ∈ S, ∀ A ∈ F x, W A ≤ W₀) :
  (∑ x ∈ S, ∑ A ∈ F x, W A) ≤
   125 * (144 * Real.pi) ^ 3 * W₀ * N ^ 6 * h ^ 2 /
    ((q : ℝ) ^ 3 * I ^ 2) := by
 classical
 let z : (Fin 3 → ℤ) → Fin 3 → ℤ := fun x =>
  if hx : IsPrimitive x then
   Classical.choose ((ZB x).mp hx)
  else 0
 have hz : ∀ x ∈ S, dotProduct x (z x) = 1 := by
  intro x hx
  dsimp [z]
  rw [dif_pos (hprimitive x hx)]
  exact Classical.choose_spec ((ZB x).mp
   (hprimitive x hx))
 let g : (Fin 3 → ℤ) → ℝ := fun x => (ZM L.toAddSubgroup x : ℝ)
 have hgdata (x : Fin 3 → ℤ) (hx : x ∈ S) :
   0 < ZM L.toAddSubgroup x ∧ ZM L.toAddSubgroup x ∣ E :=
  ZaM L.toAddSubgroup x (z x) (hz x hx) E hE hcontain
 have hg : ∀ x ∈ S, 0 < g x := by
  intro x hx
  dsimp [g]
  exact_mod_cast (hgdata x hx).1
 have hg3 : ∀ x ∈ S, g x ^ 3 ≤ I * h ^ 2 := by
  intro x hx
  have hle : g x ≤ (E : ℝ) := by
   dsimp [g]
   exact_mod_cast Nat.le_of_dvd hE (hgdata x hx).2
  exact (pow_le_pow_left₀ (hg x hx).le hle 3).trans hEbound
 have hcov : ∀ x ∈ S, ZLattice.covolume (ZG x L) =
   I * ‖Zs.Zw x‖ / g x := by
  intro x hx
  have hc := Zdb.Zei x (hprimitive x hx)
   L E hE hcontain
  rw [hindex] at hc
  exact hc
 have hrow : ∀ x ∈ S, ∀ A ∈ F x, ∀ k, A k ∈ Zaq x L := by
  intro x hx A hA k
  refine ⟨(hF x hx A hA).2 k, ?_⟩
  change x ⬝ᵥ A k = 0
  rw [dotProduct_comm]
  exact congrFun (hF x hx A hA).1 k
 have hnorm : ∀ x ∈ S, ∀ A ∈ F x, ∀ k, ‖Zp (A k)‖ ≤ 4 * N := by
  intro x hx A hA k
  exact Zl.Zgk x
   ⟨A, (hF x hx A hA).1⟩ k hN (hcoord x hx A hA k)
 have hpair : ∀ x ∈ S, ∀ A ∈ F x, ∃ k l : Fin 3,
   LinearIndependent ℝ ![Zp (A k), Zp (A l)] := by
  intro x hx A hA
  obtain ⟨s, t, hs, ht, hne⟩ := hproj x hx A hA
  obtain ⟨k, _, hk⟩ := Zl.Zca
   A s t hs ht hne
  refine ⟨k, 2, Zl.Zcq
   (Zp (A k)) (Zp (A 2)) s t ?_⟩
  simp only [Znd]
  exact_mod_cast hk
 have hb := ZcN.ZbY q L (E : ℤ)
  (by simpa using hEq) (by simpa only [Nat.cast_smul_eq_nsmul] using hcontain)
  i j hij S z hz hspan F W R (4 * N) I h W₀ hR (by positivity) hI hW₀
  g hshell hg hg3 hcov hrow hequal hnorm hpair hW
 calc
  _ ≤ 125 * W₀ * (9 * Real.pi) ^ 3 * (4 * N) ^ 6 * h ^ 2 /
    ((q : ℝ) ^ 3 * I ^ 2) := hb
  _ = _ := by ring
end Problem355.Zhk
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZlM
open scoped BigOperators
open ZL
variable {K V : Type*} [Field K]
end Problem355.ZlM
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zap
open Matrix Zo
open scoped Matrix BigOperators
noncomputable local instance zCPD8 (p : Prop) : Decidable p := Classical.propDecidable p
abbrev Zi := Matrix (Fin 3) (Fin 3) ℤ
abbrev Zv := Fin 3 → ℤ
structure ZW where
 B : ℕ
 b : ℕ
 e : ℕ
 k : ℕ
 prime : B.Prime
 e_le_k : e ≤ k
 L : Submodule ℤ Zv
 C : Zi
 P : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ
 Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ
 diagonal : C.map (Int.castRingHom (ZMod (B ^ k))) =
  (P : Matrix _ _ _) * Matrix.diagonal
   ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
   (Q : Matrix _ _ _)
 contains : ∀ v : Zv, (B ^ e) • v ∈ L
 ZbZ : ∀ i, C i ∈ L
 index_eq : L.toAddSubgroup.index = B ^ (b + e)
def ZW.h (D : ZW) : ℝ := (D.B : ℝ) ^ D.k
def ZW.I (D : ZW) : ℕ := D.B ^ (D.b + D.e)
def ZW.E (D : ZW) : ℕ := D.B ^ D.e
lemma ZW.h_one (D : ZW) : 1 ≤ D.h := one_le_pow₀ (by exact_mod_cast D.prime.one_le)
lemma ZW.I_pos (D : ZW) : 0 < D.I := pow_pos D.prime.pos _
lemma ZW.Zov (D : ZW) : 0 < D.E := pow_pos D.prime.pos _
lemma ZW.Zsg (D : ZW) : (D.E : ℝ) ^ 3 ≤ (D.I : ℝ) * D.h ^ 2 := by
 have he := D.e_le_k
 have hb : (1 : ℝ) ≤ D.B := by exact_mod_cast D.prime.one_le
 simp only [ZW.E, ZW.I, ZW.h, Nat.cast_pow, ← pow_mul, ← pow_add]
 apply pow_le_pow_right₀ hb
 omega
def Zx : ℝ := (144 * Real.pi) ^ 3
lemma ZmV : 0 ≤ Zx := by unfold Zx; positivity
open ZcC Ze
private theorem Zni (D : ZW) (T : Finset Zv) (R N w K : ℝ)
    (hR : 0 < R) (hN : 0 ≤ N) (hw : 0 ≤ w)
    (hp : ∀ x ∈ T, IsPrimitive x) (hr : ∀ x ∈ T, R ≤ ‖toEuclidean x‖)
    (F : Zv → Finset Zap.Zi)
    (hf : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : Zap.Zi → ℝ) (hW : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ w)
    (hc : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2*N)
    (hj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3, A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      Zl.ZA A s ≠ Zl.ZA A t)
    (hm : ∑ x ∈ T, (ZM D.L.toAddSubgroup x : ℝ)^3 ≤ K * R^3 * D.I) :
    (∑ x ∈ T, ∑ A ∈ F x, W A) ≤ (w * Zx * N^6) * K / (D.I : ℝ)^2 := by
  classical
  apply Zqx.ZnI T _ _ _ (fun x => ZLattice.covolume (ZG x D.L))
    R D.I _ K hR (by exact_mod_cast D.I_pos) (by have := ZmV; positivity) _ hr _ _ hm
  · intro x hx
    obtain ⟨z,hz⟩ := (ZB x).mp (hp x hx)
    exact_mod_cast (ZaM D.L.toAddSubgroup x z hz D.E D.Zov D.contains).1
  · intro x hx
    rw [Zdb.Zei x (hp x hx) D.L D.E D.Zov D.contains, D.index_eq]; rfl
  · intro x hx
    obtain ⟨z,hz⟩ := (ZB x).mp (hp x hx)
    let row (A : {A // A ∈ F x}) (i : Fin 3) : ZG x D.L :=
      Zbq x D.L ⟨A.val i, (hf x _ A.property).2 i, by
        change x ⬝ᵥ A.val i = 0
        rw [dotProduct_comm]; exact congrFun (hf x _ A.property).1 i⟩
    have inj : Function.Injective row := by
      intro A B h; apply Subtype.ext; funext i j
      have e := congrArg (fun u : ZG x D.L => ((u : ZQ x) : ZI) j) (congrFun h i)
      change (A.val i j : ℝ) = (B.val i j : ℝ) at e
      exact_mod_cast e
    let S := (F x).attach.image row
    have hb := Zdb.ZjM x z hz D.L D.E D.Zov D.contains
      S (fun _ => w) N w hN hw (fun _ _ => le_rfl)
      (by rintro u hu i; obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hu
          exact Zl.Zgk x ⟨A.val,(hf x _ A.property).1⟩ i hN (hc x hx _ A.property i))
      (by rintro u hu; obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨s,t,hs,ht,hn⟩ := hj x hx _ A.property
          obtain ⟨i,_,hi⟩ := Zl.Zca _ s t hs ht hn
          exact ⟨i,2,Zl.ZeS x ⟨A.val,(hf x _ A.property).1⟩ i 2 s t hi⟩)
    exact (Finset.sum_le_sum (hW x hx)).trans (by simpa [S, Zx, Finset.card_image_of_injective _ inj] using hb)
theorem ZpX (D : ZW) (q R : ℕ)
   (T : Finset Zv) (hR : 0 < R)
   (hprimitive : ∀ x ∈ T, IsPrimitive x)
   (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
     ‖toEuclidean x‖ < 2 * (R : ℝ))
   (F : Zv → Finset Zi)
   (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
   (W : Zi → ℝ) (N Ca : ℝ) (hN : 0 ≤ N) (hCa : 0 ≤ Ca)
   (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
   (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
     A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
     Zl.ZA A s ≠ Zl.ZA A t)
   (hweight : ∀ x ∈ T, ∀ A ∈ F x,
     AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col → W A ≤ Ca)
   (hexclude : ∀ x ∈ T, ∀ A ∈ F x,
     AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col →
     0 < W A → D.h ^ 2 < ‖toEuclidean x‖) :
   (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A =>
     AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col), W A) ≤
     1024 * Zx * Ca * N ^ 6 / (D.I : ℝ) ^ 2 := by
 classical
 let F' := fun x => (F x).filter (fun A =>
   AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col)
 by_cases hR' : D.E ≤ 2 * R
 · have hm := Zdb.Zha T D.L.toAddSubgroup D.C D.B R D.b D.e D.k
     D.prime hR' D.e_le_k D.P D.Q D.diagonal (fun x hx => (hnorm x hx).2) hprimitive D.contains D.ZbZ
   have hb := Zni D T R N Ca 1024 (by exact_mod_cast hR) hN hCa hprimitive
     (fun x hx => (hnorm x hx).1) F' (fun x A hA => hF x A (Finset.mem_filter.mp hA).1) W
     (fun x hx A hA => hweight x hx A (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2)
     (fun x hx A hA => hcoord x hx A (Finset.mem_filter.mp hA).1)
     (fun x hx A hA => hproj x hx A (Finset.mem_filter.mp hA).1) (by simpa [ZW.I] using hm)
   exact hb.trans_eq (by ring)
 · apply le_trans (b := 0) (Finset.sum_nonpos fun x hx => Finset.sum_nonpos fun A hA => ?_)
   · unfold Zx; positivity
   · apply le_of_not_gt; intro hw
     have hl := hexclude x hx A (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2 hw
     have hs := (hnorm x hx).2
     have he : (D.E : ℝ) ≤ D.h := by
      simp only [ZW.h, ZW.E, Nat.cast_pow]; exact pow_le_pow_right₀ (by exact_mod_cast D.prime.one_le) D.e_le_k
     have hr : 2 * (R : ℝ) < D.E := by exact_mod_cast Nat.lt_of_not_ge hR'
     nlinarith [D.h_one]
theorem ZnL (D : ZW) (q : ℕ) [Fact q.Prime]
  (hEq : IsUnit (D.E : ZMod q)) (hparam : D.h ^ 26 ≤ (q : ℝ))
  (i j : Fin 3) (hij : i ≠ j) (T : Finset Zv)
  (hprimitive : ∀ x ∈ T, IsPrimitive x)
  (hspan : ∀ x ∈ T, ¬ ∃ a : ZMod q, (fun s => (x s : ZMod q)) =
   a • ZL.ZC i j)
  (F : Zv → Finset Zi)
  (hF : ∀ x ∈ T, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
  (W : Zi → ℝ) (R N Cg : ℝ) (hR : 1 ≤ R)
  (hN : 0 ≤ N) (hCg : 0 ≤ Cg)
  (hnorm : ∀ x ∈ T, R ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ ≤ 2 * R)
  (hequal : ∀ x ∈ T, ∀ A ∈ F x, ∀ s, (A s i : ZMod q) = (A s j : ZMod q))
  (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
  (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
   A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
   Zl.ZA A s ≠ Zl.ZA A t)
  (hweight : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24) :
  (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
   125 * Zx * Cg * N ^ 6 / (D.I : ℝ) ^ 2 := by
 have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
 have hI : (0 : ℝ) < D.I := by exact_mod_cast D.I_pos
 have hb := Zhk.ZbY q D.L D.E D.Zov
  hEq D.contains i j hij T hprimitive hspan F hF W R N D.I D.h
  (Cg * (q : ℝ) ^ 2 * D.h ^ 24) hR hN hI (by positivity)
  (by rw [D.index_eq]; rfl) D.Zsg hnorm hequal hcoord hproj hweight
 have hratio : D.h ^ 26 / (q : ℝ) ≤ 1 := (div_le_one hq).mpr hparam
 calc
  _ ≤ 125 * (144 * Real.pi) ^ 3 * (Cg * (q : ℝ) ^ 2 * D.h ^ 24) *
    N ^ 6 * D.h ^ 2 / ((q : ℝ) ^ 3 * (D.I : ℝ) ^ 2) := hb
  _ = (125 * Zx * Cg * N ^ 6 / (D.I : ℝ) ^ 2) *
    (D.h ^ 26 / (q : ℝ)) := by
   unfold Zx
   field_simp
  _ ≤ (125 * Zx * Cg * N ^ 6 / (D.I : ℝ) ^ 2) * 1 :=
   mul_le_mul_of_nonneg_left hratio (by unfold Zx; positivity)
  _ = _ := mul_one _
theorem Zpu (D : ZW) (q R : ℕ) (hq : 0 < q) (hR : 0 < R)
  (T : Finset Zv) (hprimitive : ∀ x ∈ T, IsPrimitive x)
  (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
   ‖toEuclidean x‖ < 2 * (R : ℝ))
  (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
  (hnonzero : ∀ x ∈ T, x k ≠ 0)
  (hline : ∀ x ∈ T, (fun t => (x t : ZMod q)) ∈
   Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1})
  (F : Zv → Finset Zi)
  (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
  (W : Zi → ℝ) (N Cd : ℝ) (hN : 0 ≤ N) (hCd : 0 ≤ Cd)
  (hparam : D.h ^ 14 ≤ (q : ℝ))
  (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
  (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
   A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
   Zl.ZA A s ≠ Zl.ZA A t)
  (hweight : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cd * (q : ℝ) * D.h ^ 12) :
  (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
   512 * Zx * Cd * N ^ 6 / (D.I : ℝ) ^ 2 := by
 have hbox : ∀ x ∈ T, ∀ t,
   -((2 * R : ℕ) : ℤ) ≤ x t ∧ x t ≤ ((2 * R : ℕ) : ℤ) := by
  intro x hx t
  have hc : |(x t : ℝ)| ≤ ‖toEuclidean x‖ := by
   change ‖(toEuclidean x).ofLp t‖ ≤ ‖toEuclidean x‖
   exact PiLp.norm_apply_le _ _
  have hb : |(x t : ℝ)| ≤ (2 * R : ℕ) := by
   push_cast
   exact hc.trans (hnorm x hx).2.le
  exact abs_le.mp (show |x t| ≤ ((2 * R : ℕ) : ℤ) by exact_mod_cast hb)
 have hq' : (0 : ℝ) < q := by exact_mod_cast hq
 have hI : (0 : ℝ) < D.I := by exact_mod_cast D.I_pos
 have hcard := Zmz.Ziz T (2*R) q hq i j k hki hkj hbox hnonzero hline
 push_cast at hcard
 let K := 512 * D.h^2 / (q : ℝ)^2
 have hm : (∑ x ∈ T, (ZM D.L.toAddSubgroup x : ℝ)^3) ≤ K * (R : ℝ)^3 * D.I := by
  calc
   _ ≤ ∑ _x ∈ T, (D.I : ℝ) * D.h^2 := Finset.sum_le_sum fun x hx => by
    obtain ⟨z,hz⟩ := (ZB x).mp (hprimitive x hx)
    have hd := (ZaM D.L.toAddSubgroup x z hz D.E D.Zov D.contains).2
    apply le_trans _ D.Zsg
    exact_mod_cast Nat.pow_le_pow_left (Nat.le_of_dvd D.Zov hd) 3
   _ = (T.card : ℝ) * (D.I * D.h^2) := by simp
   _ ≤ _ := (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq (by dsimp [K]; ring)
 have hb := Zni D T R N _ K (by exact_mod_cast hR) hN (by positivity) hprimitive
  (fun x hx => (hnorm x hx).1) F hF W hweight hcoord hproj hm
 apply hb.trans
 calc
  _ = (512 * Zx * Cd * N^6 / (D.I : ℝ)^2) * (D.h^14 / q) := by dsimp [K]; field_simp
  _ ≤ _ := mul_le_of_le_one_right (by unfold Zx; positivity) ((div_le_one hq').mpr hparam)
end Problem355.Zap
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zj
open Zap
variable {B k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}
def ZbL (d : Zj B k C) (hB : B.Prime) : ZW where
 B := B
 b := d.b
 e := d.e
 k := k
 prime := hB
 e_le_k := d.e_le_k
 L := ZaE.Zix C
 C := ZaE.Zem C
 P := d.left
 Q := d.right
 diagonal := ZaE.Ziy d hB
 contains := ZaE.Zkl d
 ZbZ := ZaE.ZnJ hB
 index_eq := ZaE.ZpS d hB
@[simp] theorem ZrU (d : Zj B k C) (hB : B.Prime) :
 (d.ZbL hB).L =
  (Zah.ZZ (B ^ k) C).toIntSubmodule := rfl
@[simp] theorem ZpY (d : Zj B k C) (hB : B.Prime) :
 (d.ZbL hB).h = (B : ℝ) ^ k := rfl
@[simp] theorem ZpZ (d : Zj B k C) (hB : B.Prime) :
 (d.ZbL hB).I = B ^ (d.b + d.e) := rfl
@[simp] theorem Zqa (d : Zj B k C) (hB : B.Prime) :
 (d.ZbL hB).E = B ^ d.e := rfl
theorem Zkp (d : Zj B k C) (hB : B.Prime) :
  ((d.ZbL hB).I : ℝ) = (B : ℝ) ^ d.b * (B : ℝ) ^ d.e := by
 simp only [ZpZ, pow_add, Nat.cast_mul, Nat.cast_pow]
theorem ZhU (d : Zj B k C) (hB : B.Prime)
  (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hA : A.map (Int.castRingHom (ZMod (B ^ k))) ∈ ZS.Zbl C)
  (i : Fin 3) : A i ∈ (d.ZbL hB).L :=
 ZaE.Zqp A hA i
theorem Zlz (d : Zj B k C) (hB : B.Prime)
  {q : ℕ} (hcop : (B ^ k).Coprime q) :
  IsUnit ((d.ZbL hB).E : ZMod q) := by
 simpa only [Zqa, Int.cast_natCast] using
  ZaE.Zmf d hcop
end Problem355.Zj
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZdD
open scoped BigOperators
noncomputable local instance zCPD9 (p : Prop) : Decidable p := Classical.propDecidable p
def Zan : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]
def Zaj {F : Type*} (v : Fin 3 → (Fin 3 → F)) (p : Fin 3) : Prop :=
 v (Zan p).1 = v (Zan p).2
theorem Zjb {F : Type*} [Field F]
   (v : Fin 3 → (Fin 3 → F)) (T : Set (Fin 3 → F))
   (hT : Zac.Zbc T) (hv : ∀ i, v i ∈ T) :
   AffineIndependent F v ∨ ∃ p : Fin 3, Zaj v p := by
 by_cases h01 : v 0 = v 1
 · exact Or.inr ⟨0, h01⟩
 by_cases h02 : v 0 = v 2
 · exact Or.inr ⟨1, h02⟩
 by_cases h12 : v 1 = v 2
 · exact Or.inr ⟨2, h12⟩
 left
 have h := (affineIndependent_iff_not_collinear_set).mpr
   (hT (v 0) (hv 0) (v 1) (hv 1) (v 2) (hv 2) h01 h02 h12)
 convert h using 1
 funext i
 fin_cases i <;> rfl
theorem Zml {α : Type*}
  (S : Finset α) (W : α → ℝ)
  (affine : α → Prop) (equalPair : Fin 3 → α → Prop)
  (exceptional : Fin 3 → Prop) (lowRank : α → Prop)
  (hW : ∀ a ∈ S, 0 ≤ W a)
  (hsupport : ∀ a ∈ S, 0 < W a → affine a ∨ ∃ p, equalPair p a) :
  (∑ a ∈ S, W a) ≤
    (∑ a ∈ S.filter affine, W a) +
    ∑ p : Fin 3,
      ((∑ a ∈ S.filter (fun a => equalPair p a ∧ ¬ exceptional p), W a) +
       (∑ a ∈ S.filter (fun a => equalPair p a ∧ exceptional p ∧ ¬ lowRank a), W a) +
       (∑ a ∈ S.filter (fun a => equalPair p a ∧ exceptional p ∧ lowRank a), W a)) := by
 classical
 have hpoint (a : α) (ha : a ∈ S) :
    W a ≤ (if affine a then W a else 0) +
      ∑ p : Fin 3, if equalPair p a then W a else 0 := by
  have hnonneg (p : Fin 3) : 0 ≤ if equalPair p a then W a else 0 := by
    split_ifs <;> first | exact hW a ha | rfl
  by_cases hw : 0 < W a
  · rcases hsupport a ha hw with haf | ⟨p, hp⟩
    · simp only [if_pos haf]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun p _ => hnonneg p)
    · have hs := Finset.single_le_sum
        (s := Finset.univ) (f := fun p => if equalPair p a then W a else 0)
        (fun p _ => hnonneg p) (Finset.mem_univ p)
      have hs' : W a ≤ ∑ p : Fin 3, if equalPair p a then W a else 0 := by
        simpa only [if_pos hp] using hs
      exact hs'.trans (le_add_of_nonneg_left (by split_ifs <;> positivity))
  · have hz : W a = 0 := le_antisymm (not_lt.mp hw) (hW a ha)
    simp [hz]
 have hsplit (p : Fin 3) (a : α) :
    (if equalPair p a then W a else 0) =
      (if equalPair p a ∧ ¬ exceptional p then W a else 0) +
      (if equalPair p a ∧ exceptional p ∧ ¬ lowRank a then W a else 0) +
      (if equalPair p a ∧ exceptional p ∧ lowRank a then W a else 0) := by
  by_cases he : equalPair p a <;> by_cases hx : exceptional p <;>
    by_cases hl : lowRank a <;> simp [he, hx, hl]
 calc
  (∑ a ∈ S, W a) ≤ ∑ a ∈ S,
      ((if affine a then W a else 0) +
        ∑ p : Fin 3, if equalPair p a then W a else 0) :=
    Finset.sum_le_sum hpoint
  _ = _ := by
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    simp only [Finset.sum_add_distrib, ← Finset.sum_filter]
abbrev Zi := Matrix (Fin 3) (Fin 3) ℤ
def Zd (q : ℕ) (A : Zi) : Fin 3 → (Fin 3 → ZMod q) :=
 fun j i => (A i j : ZMod q)
def ZlA (q : ℕ) (x : Fin 3 → ℤ) (p : Fin 3) : Prop :=
 (fun i => (x i : ZMod q)) ∈ Submodule.span (ZMod q)
  {Pi.single (Zan p).1 (1 : ZMod q) - Pi.single (Zan p).2 1}
end Problem355.ZdD
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZiG
open ZdD
open scoped BigOperators
noncomputable local instance zCPD10 (p : Prop) : Decidable p := Classical.propDecidable p
def Zn {F : Type*} [Field F] (x : Fin 3 → F) (p : Fin 3) : Prop :=
 x ∈ Submodule.span F
  {Pi.single (Zan p).1 (1 : F) - Pi.single (Zan p).2 1}
theorem Zkq {F : Type*} [Field F]
  (x : Fin 3 → F) (hx : x ≠ 0) :
  ¬ (Zn x 0 ∧ Zn x 1) := by
 rintro ⟨h0, h1⟩
 obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h0
 obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h1
 have ha2 := congrFun ha 2
 have hb2 := congrFun hb 2
 simp [Zan] at ha2 hb2
 have hb0 : b = 0 := by simpa [← ha2] using hb2
 apply hx
 rw [← hb, hb0, zero_smul]
theorem Zmm {F : Type*} [Field F]
   (x : Fin 3 → F) (hx : x ≠ 0) :
   ∃ p : Fin 3, ¬ Zn x p := by
 by_cases h0 : Zn x 0
 · exact ⟨1, fun h1 => Zkq x hx ⟨h0, h1⟩⟩
 · exact ⟨0, h0⟩
theorem Zpv {F : Type*} [Field F]
   (x : Fin 3 → F) (hx : x ≠ 0) (v : Fin 3 → (Fin 3 → F))
   (hsupport : AffineIndependent F v ∨ ∃ p : Fin 3, Zaj v p) :
   AffineIndependent F v ∨
     (∃ p : Fin 3, Zaj v p ∧ ¬ Zn x p) ∨
     (∃ p : Fin 3, Zaj v p ∧ Zn x p ∧
      ∃ i j : Fin 3, v i ≠ v j) := by
 rcases hsupport with ha | ⟨p, hp⟩
 · exact Or.inl ha
 right
 by_cases he : Zn x p
 · by_cases hn : ∃ i j : Fin 3, v i ≠ v j
   · exact Or.inr ⟨p, hp, he, hn⟩
   · obtain ⟨p', hp'⟩ := Zmm x hx
     left
     refine ⟨p', ?_, hp'⟩
     exact not_not.mp (fun h => hn ⟨(Zan p').1, (Zan p').2, h⟩)
 · exact Or.inl ⟨p, hp, he⟩
theorem ZlB {F α : Type*} [Field F]
  (x : Fin 3 → F) (hx : x ≠ 0) (S : Finset α) (W : α → ℝ)
  (v : α → Fin 3 → (Fin 3 → F))
  (hW : ∀ a ∈ S, 0 ≤ W a)
  (hsupport : ∀ a ∈ S, 0 < W a →
    AffineIndependent F (v a) ∨ ∃ p : Fin 3, Zaj (v a) p) :
  (∑ a ∈ S, W a) ≤
    (∑ a ∈ S.filter (fun a => AffineIndependent F (v a)), W a) +
    ∑ p : Fin 3,
     ((∑ a ∈ S.filter (fun a => Zaj (v a) p ∧
       ¬ Zn x p), W a) +
      (∑ a ∈ S.filter (fun a => Zaj (v a) p ∧
       Zn x p ∧ ∃ i j : Fin 3, v a i ≠ v a j), W a)) := by
 classical
 let eq' := fun p a => Zaj (v a) p ∧
  (¬ Zn x p ∨ ∃ i j : Fin 3, v a i ≠ v a j)
 have hcover : ∀ a ∈ S, 0 < W a →
    AffineIndependent F (v a) ∨ ∃ p : Fin 3, eq' p a := by
  intro a ha hw
  rcases Zpv x hx (v a) (hsupport a ha hw) with
    h | ⟨p, he, hp⟩ | ⟨p, he, hp, hn⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, he, Or.inl hp⟩
  · exact Or.inr ⟨p, he, Or.inr hn⟩
 have H := Zml S W
  (fun a => AffineIndependent F (v a)) eq' (Zn x)
  (fun _ => False) hW hcover
 have heq (p : Fin 3) (a : α) :
    (eq' p a ∧ ¬ Zn x p) ↔
     (Zaj (v a) p ∧ ¬ Zn x p) := by
  simp only [eq']
  tauto
 have hne (p : Fin 3) (a : α) :
    (eq' p a ∧ Zn x p ∧ ¬ False) ↔
     (Zaj (v a) p ∧ Zn x p ∧
       ∃ i j : Fin 3, v a i ≠ v a j) := by
  simp only [eq']
  tauto
 simp_rw [heq, hne] at H
 simpa only [and_false, Finset.filter_false, Finset.sum_empty, add_zero] using H
@[simp] theorem ZdI (q : ℕ) [Fact q.Prime]
 (x : Fin 3 → ℤ) (p : Fin 3) :
 Zn (fun i => (x i : ZMod q)) p ↔ ZlA q x p := Iff.rfl
theorem Zhy
  (q : ℕ) [Fact q.Prime] (x : Fin 3 → ℤ) (hx : Zo.IsPrimitive x)
  (S : Finset Zi) (W : Zi → ℝ)
  (hW : ∀ A ∈ S, 0 ≤ W A)
  (hcap : ∀ A ∈ S, 0 < W A → ∃ T : Set (Fin 3 → ZMod q),
   Zac.Zbc T ∧ ∀ i, Zd q A i ∈ T) :
  (∑ A ∈ S, W A) ≤
   (∑ A ∈ S.filter (fun A => AffineIndependent (ZMod q) (Zd q A)), W A) +
   ∑ p : Fin 3,
    ((∑ A ∈ S.filter (fun A => Zaj (Zd q A) p ∧
      ¬ ZlA q x p), W A) +
     (∑ A ∈ S.filter (fun A => Zaj (Zd q A) p ∧
      ZlA q x p ∧ ∃ i j : Fin 3, Zd q A i ≠ Zd q A j), W A)) := by
 obtain ⟨z, hz⟩ := (Zo.ZB x).mp hx
 have hnormal := Zfl.ZeR q x z hz
 have hs : ∀ A ∈ S, 0 < W A → AffineIndependent (ZMod q) (Zd q A) ∨
   ∃ p : Fin 3, Zaj (Zd q A) p := by
  intro A hA hp
  obtain ⟨T, hT, hcols⟩ := hcap A hA hp
  exact Zjb (Zd q A) T hT hcols
 have H := ZlB (fun i => (x i : ZMod q)) hnormal S W
  (Zd q) hW hs
 simpa only [ZdI] using H
end Problem355.ZiG
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zap
open Matrix Zo ZdD ZiG
open scoped BigOperators Matrix
noncomputable local instance zCPD11 (p : Prop) : Decidable p := Classical.propDecidable p
private theorem Zmn (D : ZW) (q R : ℕ) [Fact q.Prime]
  (hEq : IsUnit (D.E : ZMod q)) (hparam : D.h ^ 26 ≤ (q : ℝ))
  (T : Finset Zv) (hR : 0 < R)
  (hprimitive : ∀ x ∈ T, IsPrimitive x)
  (_ : ∀ x ∈ T, ∀ i, x i ≠ 0)
  (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
   ‖toEuclidean x‖ < 2 * (R : ℝ))
  (F : Zv → Finset Zi)
  (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
  (W : Zi → ℝ) (N Ca Cg Cd : ℝ)
  (hN : 0 ≤ N) (_ : 0 ≤ Ca) (hCg : 0 ≤ Cg) (_ : 0 ≤ Cd)
  (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
  (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
   A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
   Zl.ZA A s ≠ Zl.ZA A t)
  (_ : ∀ x ∈ T, ∀ A ∈ F x, 0 ≤ W A)
  (_ : ∀ x ∈ T, ∀ A ∈ F x, 0 < W A →
   ∃ C : Set (Fin 3 → ZMod q), Zac.Zbc C ∧
     ∀ i, Zd q A i ∈ C)
  (_ : ∀ x ∈ T, ∀ A ∈ F x,
   AffineIndependent (ZMod q) (Zd q A) → W A ≤ Ca)
  (_ : ∀ x ∈ T, ∀ A ∈ F x,
   AffineIndependent (ZMod q) (Zd q A) →
   0 < W A → D.h ^ 2 < ‖toEuclidean x‖)
  (hwall : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24)
  (_ : ∀ x ∈ T, ∀ A ∈ F x,
   (∃ i j : Fin 3, Zd q A i ≠ Zd q A j) →
   W A ≤ Cd * (q : ℝ) * D.h ^ 12) (p : Fin 3) :
  (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A =>
   Zaj (Zd q A) p ∧
     ¬ Zn (fun i => (x i : ZMod q)) p), W A) ≤
  125 * Zx * Cg * N ^ 6 / (D.I : ℝ) ^ 2 := by
 let T' := T.filter (fun x => ¬ Zn (fun i => (x i : ZMod q)) p)
 let F' := fun x => (F x).filter (fun A => Zaj (Zd q A) p)
 have hij : (Zan p).1 ≠ (Zan p).2 := by
  fin_cases p <;> decide
 have hspan : ∀ x ∈ T', ¬ ∃ a : ZMod q,
   (fun s => (x s : ZMod q)) =
     a • ZL.ZC (Zan p).1 (Zan p).2 := by
  intro x hx he
  apply (Finset.mem_filter.mp hx).2
  obtain ⟨a, ha⟩ := he
  apply Submodule.mem_span_singleton.mpr
  refine ⟨a, ?_⟩
  rw [ha]
  congr 1
  ext t
  simp only [ZL.ZC, Pi.single_apply, Pi.sub_apply]
  split_ifs <;> rfl
 have hb := ZnL D q hEq hparam (Zan p).1 (Zan p).2
  hij T' (fun x hx => hprimitive x (Finset.mem_filter.mp hx).1) hspan F'
  (fun x hx A hA => hF x A (Finset.mem_filter.mp hA).1) W (R : ℝ) N Cg
  (by exact_mod_cast hR) hN hCg
  (fun x hx => ⟨(hnorm x (Finset.mem_filter.mp hx).1).1,
   (hnorm x (Finset.mem_filter.mp hx).1).2.le⟩)
  (fun x hx A hA s => congrFun (Finset.mem_filter.mp hA).2 s)
  (fun x hx A hA => hcoord x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
  (fun x hx A hA => hproj x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
  (fun x hx A hA => hwall x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
 calc
  _ = ∑ x ∈ T', ∑ A ∈ F' x, W A := by
   simp only [T', F', Finset.sum_filter]
   apply Finset.sum_congr rfl
   intro x hx
   by_cases hp : Zn (fun i => (x i : ZMod q)) p
   · simp [hp]
   · simp [hp]
  _ ≤ _ := hb
private theorem Zog (D : ZW) (q R : ℕ) [Fact q.Prime]
  (_ : IsUnit (D.E : ZMod q)) (hparam : D.h ^ 26 ≤ (q : ℝ))
  (T : Finset Zv) (hR : 0 < R)
  (hprimitive : ∀ x ∈ T, IsPrimitive x)
  (hnonzero : ∀ x ∈ T, ∀ i, x i ≠ 0)
  (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
    ‖toEuclidean x‖ < 2 * (R : ℝ))
  (F : Zv → Finset Zi)
  (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
  (W : Zi → ℝ) (N Ca Cg Cd : ℝ)
  (hN : 0 ≤ N) (_ : 0 ≤ Ca) (_ : 0 ≤ Cg) (hCd : 0 ≤ Cd)
  (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
  (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
    A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
    Zl.ZA A s ≠ Zl.ZA A t)
  (_ : ∀ x ∈ T, ∀ A ∈ F x, 0 ≤ W A)
  (_ : ∀ x ∈ T, ∀ A ∈ F x, 0 < W A →
    ∃ C : Set (Fin 3 → ZMod q), Zac.Zbc C ∧
     ∀ i, Zd q A i ∈ C)
  (_ : ∀ x ∈ T, ∀ A ∈ F x,
    AffineIndependent (ZMod q) (Zd q A) → W A ≤ Ca)
  (_ : ∀ x ∈ T, ∀ A ∈ F x,
    AffineIndependent (ZMod q) (Zd q A) →
    0 < W A → D.h ^ 2 < ‖toEuclidean x‖)
  (_ : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24)
  (hwdist : ∀ x ∈ T, ∀ A ∈ F x,
    (∃ i j : Fin 3, Zd q A i ≠ Zd q A j) →
    W A ≤ Cd * (q : ℝ) * D.h ^ 12) (p : Fin 3) :
  (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A =>
    Zaj (Zd q A) p ∧
     Zn (fun i => (x i : ZMod q)) p ∧
     ∃ i j : Fin 3, Zd q A i ≠ Zd q A j), W A) ≤
  512 * Zx * Cd * N ^ 6 / (D.I : ℝ) ^ 2 := by
 let T' := T.filter (fun x => Zn (fun i => (x i : ZMod q)) p)
 let F' := fun x => (F x).filter (fun A => Zaj (Zd q A) p ∧
  ∃ i j : Fin 3, Zd q A i ≠ Zd q A j)
 let l : Fin 3 := ![2, 1, 0] p
 have hli : l ≠ (Zan p).1 := by fin_cases p <;> decide
 have hlj : l ≠ (Zan p).2 := by fin_cases p <;> decide
 have h14 : D.h ^ 14 ≤ (q : ℝ) :=
  (pow_le_pow_right₀ D.h_one (by norm_num : 14 ≤ 26)).trans hparam
 have hb := Zpu D q R (Fact.out : q.Prime).pos hR T'
  (fun x hx => hprimitive x (Finset.mem_filter.mp hx).1)
  (fun x hx => hnorm x (Finset.mem_filter.mp hx).1)
  (Zan p).1 (Zan p).2 l hli hlj
  (fun x hx => hnonzero x (Finset.mem_filter.mp hx).1 l)
  (fun x hx => (Finset.mem_filter.mp hx).2) F'
  (fun x A hA => hF x A (Finset.mem_filter.mp hA).1) W N Cd hN hCd h14
  (fun x hx A hA => hcoord x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
  (fun x hx A hA => hproj x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
  (fun x hx A hA => hwdist x (Finset.mem_filter.mp hx).1 A
    (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2.2)
 have heq : (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A =>
    Zaj (Zd q A) p ∧
     Zn (fun i => (x i : ZMod q)) p ∧
     ∃ i j : Fin 3, Zd q A i ≠ Zd q A j), W A) =
    ∑ x ∈ T', ∑ A ∈ F' x, W A := by
  simp only [T', F', Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : Zn (fun i => (x i : ZMod q)) p
  · simp [hp]
  · simp [hp]
 rw [heq]
 exact hb
private theorem ZnM (D : ZW) (q : ℕ) [Fact q.Prime]
  (T : Finset Zv) (hprimitive : ∀ x ∈ T, IsPrimitive x)
  (F : Zv → Finset Zi) (W : Zi → ℝ) (N Ca Cg Cd : ℝ)
  (hW : ∀ x ∈ T, ∀ A ∈ F x, 0 ≤ W A)
  (hcap : ∀ x ∈ T, ∀ A ∈ F x, 0 < W A →
   ∃ C : Set (Fin 3 → ZMod q), Zac.Zbc C ∧
    ∀ i, Zd q A i ∈ C)
  (haff : (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A => AffineIndependent (ZMod q)
   (A.map (Int.castRingHom (ZMod q))).col), W A) ≤
   1024 * Zx * Ca * N ^ 6 / (D.I : ℝ) ^ 2)
  (hadd : ∀ p : Fin 3,
   (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A => Zaj (Zd q A) p ∧
    ¬ Zn (fun i => (x i : ZMod q)) p), W A) ≤
   125 * Zx * Cg * N ^ 6 / (D.I : ℝ) ^ 2)
  (hspecial : ∀ p : Fin 3,
   (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A => Zaj (Zd q A) p ∧
    Zn (fun i => (x i : ZMod q)) p ∧
    ∃ i j : Fin 3, Zd q A i ≠ Zd q A j), W A) ≤
   512 * Zx * Cd * N ^ 6 / (D.I : ℝ) ^ 2) :
  (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
   (1024 * Ca + 3 * (125 * Cg + 512 * Cd)) * Zx * N ^ 6 /
    (D.I : ℝ) ^ 2 := by
 let faff := fun x => ∑ A ∈ (F x).filter
  (fun A => AffineIndependent (ZMod q) (Zd q A)), W A
 let fadd := fun p x => ∑ A ∈ (F x).filter (fun A =>
  Zaj (Zd q A) p ∧
   ¬ Zn (fun i => (x i : ZMod q)) p), W A
 let fspecial := fun p x => ∑ A ∈ (F x).filter (fun A =>
  Zaj (Zd q A) p ∧
   Zn (fun i => (x i : ZMod q)) p ∧
   ∃ i j : Fin 3, Zd q A i ≠ Zd q A j), W A
 have hpoint (x : Zv) (hx : x ∈ T) :
   (∑ A ∈ F x, W A) ≤ faff x + ∑ p : Fin 3, (fadd p x + fspecial p x) := by
  have hh := Zhy q x (hprimitive x hx) (F x) W
   (hW x hx) (hcap x hx)
  simpa only [faff, fadd, fspecial, ZdI] using hh
 have haff' : (∑ x ∈ T, faff x) ≤
   1024 * Zx * Ca * N ^ 6 / (D.I : ℝ) ^ 2 := by
  calc
   _ = ∑ x ∈ T, ∑ A ∈ (F x).filter (fun A => AffineIndependent (ZMod q)
      (A.map (Int.castRingHom (ZMod q))).col), W A := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr
    · apply Finset.filter_congr
      intro A hA
      rfl
    · intro A hA
      rfl
   _ ≤ _ := haff
 calc
  (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
    ∑ x ∈ T, (faff x + ∑ p : Fin 3, (fadd p x + fspecial p x)) :=
   Finset.sum_le_sum hpoint
  _ = (∑ x ∈ T, faff x) + ∑ p : Fin 3,
    ((∑ x ∈ T, fadd p x) + (∑ x ∈ T, fspecial p x)) := by
   rw [Finset.sum_add_distrib]
   congr 1
   rw [Finset.sum_comm]
   simp only [Finset.sum_add_distrib]
  _ ≤ (1024 * Zx * Ca * N ^ 6 / (D.I : ℝ) ^ 2) +
    ∑ _p : Fin 3, ((125 * Zx * Cg * N ^ 6 / (D.I : ℝ) ^ 2) +
      (512 * Zx * Cd * N ^ 6 / (D.I : ℝ) ^ 2)) := by
   apply add_le_add haff'
   exact Finset.sum_le_sum fun p _ => add_le_add (hadd p) (hspecial p)
  _ = _ := by simp; ring
theorem ZoM (D : ZW) (q R : ℕ) [Fact q.Prime]
  (hEq : IsUnit (D.E : ZMod q)) (hparam : D.h ^ 26 ≤ (q : ℝ))
  (T : Finset Zv) (hR : 0 < R)
  (hprimitive : ∀ x ∈ T, IsPrimitive x)
  (hnonzero : ∀ x ∈ T, ∀ i, x i ≠ 0)
  (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
   ‖toEuclidean x‖ < 2 * (R : ℝ))
  (F : Zv → Finset Zi)
  (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
  (W : Zi → ℝ) (N Ca Cg Cd : ℝ)
  (hN : 0 ≤ N) (hCa : 0 ≤ Ca) (hCg : 0 ≤ Cg) (hCd : 0 ≤ Cd)
  (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
  (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
   A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
   Zl.ZA A s ≠ Zl.ZA A t)
  (hW : ∀ x ∈ T, ∀ A ∈ F x, 0 ≤ W A)
  (hcap : ∀ x ∈ T, ∀ A ∈ F x, 0 < W A →
   ∃ C : Set (Fin 3 → ZMod q), Zac.Zbc C ∧
    ∀ i, Zd q A i ∈ C)
  (hwaff : ∀ x ∈ T, ∀ A ∈ F x,
   AffineIndependent (ZMod q) (Zd q A) → W A ≤ Ca)
  (hexclude : ∀ x ∈ T, ∀ A ∈ F x,
   AffineIndependent (ZMod q) (Zd q A) →
   0 < W A → D.h ^ 2 < ‖toEuclidean x‖)
  (hwall : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24)
  (hwdist : ∀ x ∈ T, ∀ A ∈ F x,
   (∃ i j : Fin 3, Zd q A i ≠ Zd q A j) →
   W A ≤ Cd * (q : ℝ) * D.h ^ 12) :
  (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
   (1024 * Ca + 3 * (125 * Cg + 512 * Cd)) * Zx * N ^ 6 /
    (D.I : ℝ) ^ 2 := by
 have haff := ZpX D q R T hR hprimitive hnorm F hF W N Ca hN hCa
  hcoord hproj hwaff hexclude
 have hadd := Zmn D q R hEq hparam T hR hprimitive hnonzero hnorm F hF W N Ca Cg Cd hN hCa hCg hCd hcoord hproj hW hcap hwaff hexclude hwall hwdist
 have hspecial := Zog D q R hEq hparam T hR hprimitive hnonzero hnorm F hF W N Ca Cg Cd hN hCa hCg hCd hcoord hproj hW hcap hwaff hexclude hwall hwdist
 exact ZnM D q T hprimitive F W N Ca Cg Cd hW hcap haff hadd hspecial
end Problem355.Zap
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZeC
open Matrix Zo Zap
open scoped BigOperators
noncomputable local instance zCPD12 (p : Prop) : Decidable p := Classical.propDecidable p
def ZO (Ca Cg Cd : ℝ) : ℝ :=
 4 * (1024 * Ca + 3 * (125 * Cg + 512 * Cd)) * Zx
lemma ZaJ {Ca Cg Cd : ℝ}
  (ha : 0 ≤ Ca) (hg : 0 ≤ Cg) (hd : 0 ≤ Cd) :
  0 ≤ ZO Ca Cg Cd := by
 unfold ZO Zx
 positivity
theorem Zdx
  (D : ZW) (q N : ℕ) [Fact q.Prime]
  (hN : 1 ≤ N) (hEq : IsUnit (D.E : ZMod q))
  (hparam : D.h ^ 26 ≤ (q : ℝ))
  (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
  (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ)
  (Ca Cg Cd : ℝ) (hCa : 0 ≤ Ca) (hCg : 0 ≤ Cg) (hCd : 0 ≤ Cd)
  (hW : ∀ A ∈ S, 0 ≤ W A)
  (hdet : ∀ A ∈ S, A.det = 0)
  (hrows : ∀ A ∈ S, ∀ i, A i ∈ D.L)
  (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
  (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
   ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
   ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
  (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ (2 * N : ℕ))
  (hcap : ∀ A ∈ S, 0 < W A → ∃ T : Set (Fin 3 → ZMod q),
   Zac.Zbc T ∧ ∀ i, (A.map (Int.castRingHom (ZMod q))).col i ∈ T)
  (haffine : ∀ A ∈ S,
   AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col → W A ≤ Ca)
  (hwide : ∀ A ∈ S, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24)
  (hdistinct : ∀ A ∈ S,
   (∃ i j : Fin 3, (A.map (Int.castRingHom (ZMod q))).col i ≠
    (A.map (Int.castRingHom (ZMod q))).col j) →
   W A ≤ Cd * (q : ℝ) * D.h ^ 12)
  (hexclude : ∀ A ∈ S, ∀ x : Fin 3 → ℤ, IsPrimitive x → A *ᵥ x = 0 →
   AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col →
   0 < W A → D.h ^ 2 < ‖toEuclidean x‖) :
  (∑ A ∈ S, W A) ≤ ZO Ca Cg Cd * (N : ℝ) ^ 6 /
   (D.I : ℝ) ^ 2 * (Real.log (4 * (N : ℝ)) / Real.log 2) := by
 classical
 let K : ℝ := (1024 * Ca + 3 * (125 * Cg + 512 * Cd)) *
  Zx * (N : ℝ) ^ 6 / (D.I : ℝ) ^ 2
 have hK : 0 ≤ K := by dsimp [K, Zx]; positivity
 have htotal := Zo.Zdj
  S W hW hdet hheight hproj (2 * N) (by omega)
  (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound) hK
 have hshell : ∀ i : ℕ,
   ∑ x ∈ (Zbt (2 * N)).filter (fun x =>
    (2 : ℝ) ^ i ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ < 2 ^ (i + 1)),
    ∑ A ∈ S.filter (fun A => A *ᵥ x = 0), W A ≤ K := by
  intro i
  let T := (Zbt (2 * N)).filter (fun x =>
   (2 : ℝ) ^ i ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ < 2 ^ (i + 1))
  let F := fun x => S.filter (fun A => A *ᵥ x = 0)
  have hp : ∀ x ∈ T, IsPrimitive x := by
   intro x hx
   exact ((ZfV _ x).mp (Finset.mem_filter.mp hx).1).1
  have hxne : ∀ x ∈ T, ∀ j, x j ≠ 0 := by
   intro x hx
   exact ((ZfV _ x).mp (Finset.mem_filter.mp hx).1).2.1
  have hn : ∀ x ∈ T, ((2 ^ i : ℕ) : ℝ) ≤ ‖toEuclidean x‖ ∧
    ‖toEuclidean x‖ < 2 * ((2 ^ i : ℕ) : ℝ) := by
   intro x hx
   have hh := (Finset.mem_filter.mp hx).2
   simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_succ, mul_comm] using hh
  have hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ j, A j ∈ D.L := by
   intro x A hA
   exact ⟨(Finset.mem_filter.mp hA).2, hrows A (Finset.mem_filter.mp hA).1⟩
  have hc : ∀ x ∈ T, ∀ A ∈ F x, ∀ j k, |(A j k : ℝ)| ≤ 2 * (N : ℝ) := by
   intro x hx A hA j k
   exact_mod_cast hbound A (Finset.mem_filter.mp hA).1 j k
  have hpr : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
    A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
    Zl.ZA A s ≠ Zl.ZA A t := by
   intro x hx A hA
   have ha := (Finset.mem_filter.mp hA).1
   exact ⟨0, 1, hheight A ha 0, hheight A ha 1, hproj A ha 0 1 (by decide)⟩
  exact Zap.ZoM D q (2 ^ i) hEq hparam T
   (pow_pos (by decide) _) hp hxne hn F hF W (N : ℝ) Ca Cg Cd
   (Nat.cast_nonneg _) hCa hCg hCd
   hc hpr
   (fun x hx A hA => hW A (Finset.mem_filter.mp hA).1)
   (fun x hx A hA hw => hcap A (Finset.mem_filter.mp hA).1 hw)
   (fun x hx A hA ha => haffine A (Finset.mem_filter.mp hA).1 ha)
   (fun x hx A hA ha hw => hexclude A (Finset.mem_filter.mp hA).1 x
    (hp x hx) (Finset.mem_filter.mp hA).2 ha hw)
   (fun x hx A hA => hwide A (Finset.mem_filter.mp hA).1)
   (fun x hx A hA hne => hdistinct A (Finset.mem_filter.mp hA).1 hne)
 have hb := htotal hshell
 convert hb using 1 ; dsimp [K, ZO] ; push_cast ; ring_nf
end Problem355.ZeC
end
end OAI
end
section
namespace OAI
namespace Problem355.ZaN
open scoped BigOperators
end Problem355.ZaN
end OAI
end
section
namespace OAI
namespace Problem355.ZaN
open scoped BigOperators
theorem Zes
  {x : Zo.Vector} {H : ℕ}
  (hx : ‖Zo.toEuclidean x‖ ≤ (H : ℝ)) :
  ∀ i, |x i| ≤ (H : ℤ) := by
 intro i
 have hi := (PiLp.norm_apply_le (Zo.toEuclidean x) i).trans hx
 have hi' : |(x i : ℝ)| ≤ (H : ℝ) := by
  simpa [Zo.toEuclidean, Real.norm_eq_abs] using hi
 exact_mod_cast hi'
theorem ZnN {q : ℕ}
  {A : Matrix (Fin 3) (Fin 3) ℤ} {x : Fin 3 → ℤ}
  (hx : A.mulVec x = 0) :
  (A.map (Int.castRingHom (ZMod q))).mulVec (fun i => (x i : ZMod q)) = 0 := by
 funext i
 have hi := congrArg (fun z : ℤ => (z : ZMod q)) (congrFun hx i)
 simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using hi
end Problem355.ZaN
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZJ
open scoped BigOperators
open Zb
namespace Law
variable {q H : ℕ} [Fact q.Prime]
theorem Zdy (L : Law q H) (p : Fin 3 → Fin 3 → ZMod q)
  (hpositive : 0 < Zk q L.size L.weight L.sets p) :
  ∃ ω : L.Outcome, ∀ i, p i ∈ L.sets ω := by
 classical
 have hinc : 0 < Zbb L.weight L.sets p := by
  by_contra hn
  have hn' : Zbb L.weight L.sets p ≤ 0 := le_of_not_gt hn
  have hbad : Zk q L.size L.weight L.sets p ≤ 0 := by
   unfold Zk
   exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hn'
  exact (not_le_of_gt hpositive) hbad
 by_contra hn
 have hnone : ∀ ω : L.Outcome, ¬ (∀ i, p i ∈ L.sets ω) := by
  intro ω hω
  exact hn ⟨ω, hω⟩
 have hz : Zbb L.weight L.sets p = 0 := by
  unfold Zbb
  apply Finset.sum_eq_zero
  intro ω hω
  exact if_neg (hnone ω)
 exact (ne_of_gt hinc) hz
theorem Zmo (L : Law q H) (p : Fin 3 → Fin 3 → ZMod q)
   (hpositive : 0 < Zk q L.size L.weight L.sets p) :
   (∀ i, p i ≠ 0) ∧
     (AffineIndependent (ZMod q) p ∨ ∃ i j, i ≠ j ∧ p i = p j) ∧
     (AffineIndependent (ZMod q) p → ∀ x : Fin 3 → ℤ,
      (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
       (∑ i, (x i : ZMod q) • p i) ≠ 0) := by
 classical
 obtain ⟨ω, hω⟩ := L.Zdy p hpositive
 refine ⟨?_, ?_, ?_⟩
 · intro i hi
   exact L.zero_not_mem ω (hi ▸ hω i)
 · by_cases hinj : Function.Injective p
   · exact Or.inl (ZaN.Zdv (L.isCap ω) hω hinj)
   · right
     simp only [Function.Injective] at hinj
     push Not at hinj
     obtain ⟨i, j, heq, hne⟩ := hinj
     exact ⟨i, j, hne, heq⟩
 · intro hAI x hx hne
   exact L.short_relation ω p hω hAI.injective x hx hne
theorem ZhV (L : Law q H)
  (A : Matrix (Fin 3) (Fin 3) (ZMod q))
  (hpositive : 0 < Zk q L.size L.weight L.sets A.col)
  (hAI : AffineIndependent (ZMod q) A.col)
  (x : Fin 3 → ℤ) (hx : ∀ i, |x i| ≤ (H : ℤ)) (hne : x ≠ 0) :
  A.mulVec (fun i => (x i : ZMod q)) ≠ 0 := by
 intro hrel
 have hno := (L.Zmo A.col hpositive).2.2 hAI x hx hne
 apply hno
 funext i
 have hi := congrFun hrel i
 simpa [Matrix.mulVec, Matrix.col, dotProduct, Finset.sum_apply, mul_comm] using hi
theorem ZhW (L : Law q H)
  (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hpositive : 0 < Zk q L.size L.weight L.sets
   (A.map (Int.castRingHom (ZMod q))).col)
  (hAI : AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col)
  {x : Zo.Vector} (hne : x ≠ 0) (hkernel : A.mulVec x = 0) :
  (H : ℝ) < ‖Zo.toEuclidean x‖ := by
 by_contra hn
 have hx := ZaN.Zes (le_of_not_gt hn)
 have hno := L.ZhV (A.map (Int.castRingHom (ZMod q)))
  hpositive hAI x hx hne
 exact hno (ZaN.ZnN hkernel)
theorem Zjc {h : ℕ} (L : Law q (h ^ 2))
  (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hpositive : 0 < Zk q L.size L.weight L.sets
   (A.map (Int.castRingHom (ZMod q))).col)
  (hAI : AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col)
  {x : Zo.Vector} (hne : x ≠ 0) (hkernel : A.mulVec x = 0) :
  (h : ℝ) ^ 2 < ‖Zo.toEuclidean x‖ := by
 simpa only [Nat.cast_pow] using L.ZhW A hpositive hAI hne hkernel
end Law
end Problem355.ZJ
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZJ.Law
open scoped BigOperators
open Zb
variable {q h : ℕ} [Fact q.Prime]
theorem Zdz (L : Law q (h ^ 2)) :
  (q : ℝ) ^ 3 / L.size ≤ 2000 ^ 3 * (q : ℝ) * (h : ℝ) ^ 12 := by
 have hs : (q : ℝ) ^ 2 ≤ 2000 ^ 3 * ((h : ℝ) ^ 2) ^ 6 * L.size := by
  exact_mod_cast L.size_lower
 have hsize : (0 : ℝ) < L.size := by exact_mod_cast L.size_pos
 apply (div_le_iff₀ hsize).mpr
 calc
  (q : ℝ) ^ 3 = (q : ℝ) * (q : ℝ) ^ 2 := by ring
  _ ≤ (q : ℝ) * (2000 ^ 3 * ((h : ℝ) ^ 2) ^ 6 * L.size) :=
   mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg q)
  _ = _ := by ring
theorem ZjO (L : Law q (h ^ 2))
  (p : Fin 3 → Fin 3 → ZMod q) :
  Zk q L.size L.weight L.sets p ≤
   (2 * 2000 ^ 6) * (q : ℝ) ^ 2 * (h : ℝ) ^ 24 := by
 calc
  _ ≤ 2 * ((q : ℝ) ^ 3 / L.size) ^ 2 := L.weight_le_two p
  _ ≤ 2 * (2000 ^ 3 * (q : ℝ) * (h : ℝ) ^ 12) ^ 2 := by
   gcongr
   exact L.Zdz
  _ = _ := by ring
theorem Zjd (L : Law q (h ^ 2))
  (p : Fin 3 → Fin 3 → ZMod q) (hne : ∃ i j, p i ≠ p j) :
  Zk q L.size L.weight L.sets p ≤
   (4 * 2000 ^ 3) * (q : ℝ) * (h : ℝ) ^ 12 := by
 obtain ⟨i, j, hij⟩ := hne
 calc
  _ ≤ 4 * ((q : ℝ) ^ 3 / L.size) := L.weight_le_four p i j hij
  _ ≤ 4 * (2000 ^ 3 * (q : ℝ) * (h : ℝ) ^ 12) :=
   mul_le_mul_of_nonneg_left L.Zdz (by norm_num)
  _ = _ := by ring
end Problem355.ZJ.Law
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zbu
open Matrix Zo Zap Zb
open scoped BigOperators
def ZO : ℝ :=
 ZeC.ZO 8 (2 * 2000 ^ 6) (4 * 2000 ^ 3)
lemma ZaJ : 0 ≤ ZO :=
 ZeC.ZaJ (by norm_num) (by positivity) (by positivity)
theorem Zdx
   (D : ZW) (q N : ℕ) [Fact q.Prime]
   (hN : 1 ≤ N) (hEq : IsUnit (D.E : ZMod q))
   (hparam : D.h ^ 26 ≤ (q : ℝ))
   (L : ZJ.Law q ((D.B ^ D.k) ^ 2))
   (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
   (hdet : ∀ A ∈ S, A.det = 0)
   (hrows : ∀ A ∈ S, ∀ i, A i ∈ D.L)
   (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
   (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
    ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
    ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
   (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ (2 * N : ℕ)) :
   (∑ A ∈ S, Zk q L.size L.weight L.sets
    (A.map (Int.castRingHom (ZMod q))).col) ≤
    ZO * (N : ℝ) ^ 6 / (D.I : ℝ) ^ 2 *
     (Real.log (4 * (N : ℝ)) / Real.log 2) := by
 apply ZeC.Zdx D q N hN hEq hparam S
   (fun A => Zk q L.size L.weight L.sets
    (A.map (Int.castRingHom (ZMod q))).col)
   8 (2 * 2000 ^ 6) (4 * 2000 ^ 3)
   (by norm_num) (by positivity) (by positivity)
   (fun A _ => ZfC q L.size L.weight L.sets L.weight_nonneg _)
   hdet hrows hheight hproj hbound
 · intro A hA hpositive
   obtain ⟨ω, hω⟩ := L.Zdy
    (A.map (Int.castRingHom (ZMod q))).col hpositive
   exact ⟨L.sets ω, L.isCap ω, hω⟩
 · intro A hA hAI
   exact L.ZcW _ hAI
 · intro A hA
   simpa only [ZW.h, Nat.cast_pow] using
    L.ZjO (A.map (Int.castRingHom (ZMod q))).col
 · intro A hA hne
   simpa only [ZW.h, Nat.cast_pow] using
    L.Zjd (A.map (Int.castRingHom (ZMod q))).col hne
 · intro A hA x hx hkernel hAI hpositive
   simpa only [ZW.h, Nat.cast_pow] using
    L.Zjc A hpositive hAI hx.ne_zero hkernel
end Problem355.Zbu
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZaR
open Finset
lemma Zkr {N : ℝ} (hN : 1 ≤ N) :
  Real.log (4 * N) / Real.log 2 ≤
   (2 / (Real.log 2) ^ 2) * (Real.log (2 * N)) ^ 2 :=
 ZfQ.ZjK hN
def ZdA (Czero Cnonzero : ℝ) : ℝ :=
 Cnonzero + 2 * Czero / (Real.log 2) ^ 2
lemma Zmp {Czero Cnonzero : ℝ}
  (hzero : 0 ≤ Czero) (hnonzero : 0 ≤ Cnonzero) :
  0 ≤ ZdA Czero Cnonzero := by
 unfold ZdA
 positivity
lemma Zoh {N : ℕ} (hN : 1 ≤ N)
  (A : ZP.Zi)
  (hbox : ∀ j, Homogeneous.ZaX (N : ℝ) (fun i => (A i j : ℝ)))
  (j : Fin 3) : A 2 j ≠ 0 := by
 have hNp : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
 have hp : (0 : ℝ) < A 2 j := hNp.trans_le (hbox j).2.2.2.2.1
 intro hz
 simp only [hz, Int.cast_zero, lt_self_iff_false] at hp
lemma Zoi {N : ℕ} (A : ZP.Zi)
  (hbox : ∀ j, Homogeneous.ZaX (N : ℝ) (fun i => (A i j : ℝ)))
  (i j : Fin 3) : |A i j| ≤ (2 * N : ℕ) := by
 have hr : |(A i j : ℝ)| ≤ 2 * (N : ℝ) := by
  have hj := hbox j
  fin_cases i
  · change |(A 0 j : ℝ)| ≤ 2 * (N : ℝ)
    rw [abs_of_nonneg hj.1]
    linarith [hj.2.1, Nat.cast_nonneg (α := ℝ) N]
  · change |(A 1 j : ℝ)| ≤ 2 * (N : ℝ)
    rw [abs_of_nonneg hj.2.2.1]
    linarith [hj.2.2.2.1, Nat.cast_nonneg (α := ℝ) N]
  · change |(A 2 j : ℝ)| ≤ 2 * (N : ℝ)
    rw [abs_of_nonneg ((Nat.cast_nonneg N).trans hj.2.2.2.2.1)]
    exact hj.2.2.2.2.2.le
 exact_mod_cast hr
def ZO : ℝ :=
 ZdA Zbu.ZO (8 * ZP.Zcw)
lemma ZaJ : 0 ≤ ZO :=
 Zmp Zbu.ZaJ
  (mul_nonneg (by norm_num) ZP.ZkW.le)
theorem Zqb
   {B k q : ℕ} (hB : B.Prime) [Fact q.Prime]
   (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) (d : Zj B k C)
   (L : ZJ.Law q ((B ^ k) ^ 2))
   (hcop : (B ^ k).Coprime q) (hparam : ((B : ℝ) ^ k) ^ 26 ≤ (q : ℝ))
   (N : ℕ) (hN : 1 ≤ N) (S : Finset ZP.Zi)
   (horbit : ∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
    ZS.Zbl C)
   (hbox : ∀ A ∈ S, ∀ j, Homogeneous.ZaX (N : ℝ) (fun i => (A i j : ℝ)))
   (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
    Zl.ZA A i ≠ Zl.ZA A j)
   (t : ℤ) (htq : |t| < (q : ℤ)) :
   (∑ A ∈ S.filter (fun A => A.det = t),
    Zb.Zk q L.size L.weight L.sets
     (A.map (Int.castRingHom (ZMod q))).col) ≤
    ZO * Real.log (2 * (N : ℝ)) ^ 2 * (N : ℝ) ^ 6 /
     ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
 classical
 have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
 have hz0 := Zbu.ZaJ
 have hp := ZP.ZkW.le
 by_cases ht : t = 0
 · subst t
   have hz := Zbu.Zdx (d.ZbL hB) q N hN
    (d.Zlz hB hcop)
    (by simpa only [Zj.ZpY] using hparam) L
    (S.filter (fun A => A.det = 0))
    (fun A hA => (Finset.mem_filter.mp hA).2)
    (fun A hA i => d.ZhU hB A
     (horbit A (Finset.mem_filter.mp hA).1) i)
    (fun A hA => Zoh hN A (hbox A (Finset.mem_filter.mp hA).1))
    (fun A hA => hproj A (Finset.mem_filter.mp hA).1)
    (fun A hA => Zoi A (hbox A (Finset.mem_filter.mp hA).1))
   rw [d.Zkp hB] at hz
   apply hz.trans
   have hh := mul_le_mul_of_nonneg_left (Zkr hn)
    (show 0 ≤ Zbu.ZO * (N : ℝ)^6 /
     ((B : ℝ)^d.b * (B : ℝ)^d.e)^2 by positivity)
   apply hh.trans
   unfold ZO ZdA
   have ex : 0 ≤ 8 * ZP.Zcw * Real.log (2 * (N : ℝ))^2 *
     (N : ℝ)^6 / ((B : ℝ)^d.b * (B : ℝ)^d.e)^2 := by positivity
   simp only [div_eq_mul_inv] at ex ⊢
   nlinarith only [ex]
 · have hdiag : C = (d.left : Matrix _ _ _) *
     ZaG.Zad (R := ZMod (B ^ k)) (B ^ d.b) (B ^ d.e) *
     (d.right : Matrix _ _ _) := by
    simpa only [ZaG.Zad, Nat.cast_pow] using d.diagonalization
   have hb := ZP.ZdO B k d.b d.e hB.pos
    d.ZpO d.e_le_k d.b_le_e C d.left d.right hdiag N hn
    (S.filter fun A => A.det = t)
    (fun A h => horbit A (mem_filter.mp h).1) (fun A h => hbox A (mem_filter.mp h).1)
    t ht (fun A h => (mem_filter.mp h).2) _ 8 (by norm_num) (by
     intro A h
     have eq := (mem_filter.mp h).2
     exact L.ZcW _ (Zdi.ZeA A
      (eq ▸ ht) (eq ▸ htq)))
   apply hb.trans
   unfold ZO ZdA
   gcongr
   exact le_add_of_nonneg_right (by positivity)
end Problem355.ZaR
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zhl
open Matrix Zc ZD ZbR
open scoped BigOperators
noncomputable local instance zCPD13 (p : Prop) : Decidable p := Classical.propDecidable p
def ZdS (N h : ℕ) [NeZero h]
  (C : Fin 3 → Fin 3 → ZMod h) : Finset Zi :=
 (ZfZ N (Zm N)).filter (fun A =>
  Homogeneous.ZbH (Homogeneous.ZN A 0)
   (Homogeneous.ZN A 1) (Homogeneous.ZN A 2) ∧
  (fun j i => (A i j : ZMod h)) ∈ Zt (Zz h) C)
theorem Zgl (N h : ℕ) [NeZero h]
  (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ) :
  (ZdS N h C).filter (fun A => A.det = t) = ZdX N h C t := by
 ext A
 simp only [ZdS, ZdX, Zbr, Finset.mem_filter]
 tauto
theorem ZmW {N h : ℕ} [NeZero h]
  {C : Fin 3 → Fin 3 → ZMod h} {A : Zi}
  (hA : A ∈ ZdS N h C) :
  A.map (Int.castRingHom (ZMod h)) ∈ ZS.Zbl (transpose C) := by
 exact ZiP
  (show Zbr h C A.det A from ⟨(Finset.mem_filter.mp hA).2.1,
   (Finset.mem_filter.mp hA).2.2, rfl⟩)
theorem Zqr {N h : ℕ} [NeZero h]
  {C : Fin 3 → Fin 3 → ZMod h} {A : Zi}
  (hA : A ∈ ZdS N h C) (j : Fin 3) :
  Homogeneous.ZaX (N : ℝ) (fun i => (A i j : ℝ)) := by
 have hAm := (Finset.mem_filter.mp hA).1
 obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hAm
 exact Zas.ZnX (x j)
theorem ZlC {N h : ℕ} [NeZero h]
  {C : Fin 3 → Fin 3 → ZMod h} {A : Zi}
  (hA : A ∈ ZdS N h C) (i j : Fin 3) (hij : i ≠ j) :
  Homogeneous.project (Homogeneous.ZN A i) ≠
   Homogeneous.project (Homogeneous.ZN A j) := by
 apply Zjw (t := A.det) (h := h) (C := C) (N := N) _ i j hij
 rw [← Zgl]
 exact Finset.mem_filter.mpr ⟨hA, rfl⟩
end Problem355.Zhl
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZbT
open Matrix
def Zoj {K : Type*} [CommRing K] (x : K) : Fin 3 → K :=
 ![1, x, x ^ 2]
def ZcH {K : Type*} [CommRing K] (x y z : K) : Matrix (Fin 3) (Fin 3) K :=
 !![1, 1, 1; x, y, z; x ^ 2, y ^ 2, z ^ 2]
theorem Zpw {K : Type*} [CommRing K] (x y z : K) :
  (ZcH x y z).det = (y - x) * (z - x) * (z - y) := by
 rw [Matrix.det_fin_three]
 simp [ZcH]
 ring
theorem Zks {K : Type*} [CommRing K] [IsDomain K]
  {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
  (ZcH x y z).det ≠ 0 := by
 rw [Zpw]
 exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hxy.symm)
  (sub_ne_zero.mpr hxz.symm)) (sub_ne_zero.mpr hyz.symm)
theorem Zhz {F K : Type*} [Field F] [Field K]
  [Algebra F K] [Module.Finite F K]
  {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
  Algebra.norm F (ZcH x y z).det ≠ 0 := by
 exact Algebra.norm_ne_zero_iff.mpr (Zks hxy hxz hyz)
end Problem355.ZbT
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zbv
open scoped BigOperators
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
 [FiniteDimensional F K]
def Zay (P : MvPolynomial V K) : MvPolynomial V K :=
 ∏ σ : K ≃ₐ[F] K, MvPolynomial.map σ.toRingHom P
omit [FiniteDimensional F K] in
theorem Zqs (P : MvPolynomial V K) (x : V → F) (σ : K ≃ₐ[F] K) :
  MvPolynomial.eval (algebraMap F K ∘ x) (MvPolynomial.map σ.toRingHom P) =
   σ (MvPolynomial.eval (algebraMap F K ∘ x) P) := by
 simpa [Function.comp_def] using
  (MvPolynomial.map_eval σ.toRingHom (algebraMap F K ∘ x) P).symm
theorem Zok [IsGalois F K] (P : MvPolynomial V K) (x : V → F) :
  MvPolynomial.eval (algebraMap F K ∘ x) (Zay (F := F) P) =
   algebraMap F K (Algebra.norm F (MvPolynomial.eval (algebraMap F K ∘ x) P)) := by
 rw [Zay, map_prod, Algebra.norm_eq_prod_automorphisms]
 exact Finset.prod_congr rfl (fun σ _ => Zqs P x σ)
theorem ZoN (P : MvPolynomial V K) (τ : K ≃ₐ[F] K) :
  MvPolynomial.map τ.toRingHom (Zay (F := F) P) =
   Zay (F := F) P := by
 classical
 rw [Zay, map_prod]
 change (∏ σ : K ≃ₐ[F] K, MvPolynomial.map τ.toRingHom
  (MvPolynomial.map σ.toRingHom P)) = _
 simp_rw [MvPolynomial.map_map]
 exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)
theorem ZhA [IsGalois F K]
  (P : MvPolynomial V K) (m : V →₀ ℕ) :
  (Zay (F := F) P).coeff m ∈ Set.range (algebraMap F K) := by
 rw [IsGalois.mem_range_algebraMap_iff_fixed]
 intro τ
 have h := congrArg (fun polynomial : MvPolynomial V K => polynomial.coeff m) (ZoN P τ)
 simpa [MvPolynomial.coeff_map] using h
theorem ZhB {R S : Type*} [CommSemiring R] [CommSemiring S]
  (f : R →+* S) (P : MvPolynomial V S)
  (h : ∀ m, P.coeff m ∈ Set.range f) :
  ∃ Q : MvPolynomial V R, MvPolynomial.map f Q = P := by
 classical
 choose c hc using h
 refine ⟨∑ m ∈ P.support, MvPolynomial.monomial m (c m), ?_⟩
 simp only [map_sum, MvPolynomial.map_monomial, hc]
 exact MvPolynomial.support_sum_monomial_coeff P
theorem Zgm [IsGalois F K] (P : MvPolynomial V K) :
  ∃ Q : MvPolynomial V F,
   MvPolynomial.map (algebraMap F K) Q = Zay (F := F) P :=
 ZhB _ _ (ZhA P)
def ZcB [IsGalois F K] (P : MvPolynomial V K) : MvPolynomial V F :=
 Classical.choose (Zgm P)
@[simp] theorem ZcX [IsGalois F K] (P : MvPolynomial V K) :
  MvPolynomial.map (algebraMap F K) (ZcB (F := F) P) =
   Zay (F := F) P :=
 Classical.choose_spec (Zgm P)
theorem ZnO [IsGalois F K] (P : MvPolynomial V K) (x : V → F) :
  MvPolynomial.eval x (ZcB (F := F) P) =
   Algebra.norm F (MvPolynomial.eval (algebraMap F K ∘ x) P) := by
 apply (algebraMap F K).injective
 rw [MvPolynomial.eval₂_comp, ← MvPolynomial.eval_map, ZcX,
  Zok]
theorem ZiB [IsGalois F K]
  (hodd : Odd (Module.finrank F K)) (P : MvPolynomial V K) (f : V → V)
  (hP : MvPolynomial.rename f P = -P) :
  MvPolynomial.rename f (Zay (F := F) P) =
   -Zay (F := F) P := by
 classical
 rw [Zay, map_prod]
 simp_rw [← MvPolynomial.map_rename, hP, map_neg]
 rw [Finset.prod_neg]
 have hcard : Fintype.card (K ≃ₐ[F] K) = Module.finrank F K := by
  simpa only [Nat.card_eq_fintype_card] using IsGalois.card_aut_eq_finrank F K
 simp only [Finset.card_univ, hcard, hodd.neg_one_pow, neg_one_mul]
theorem ZhX [IsGalois F K]
  (hodd : Odd (Module.finrank F K)) (P : MvPolynomial V K) (f : V → V)
  (hP : MvPolynomial.rename f P = -P) :
  MvPolynomial.rename f (ZcB (F := F) P) =
   -ZcB (F := F) P := by
 apply MvPolynomial.map_injective (algebraMap F K) (algebraMap F K).injective
 rw [MvPolynomial.map_rename, ZcX, map_neg, ZcX]
 exact ZiB hodd P f hP
end Problem355.Zbv
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zbk
open Matrix
open scoped BigOperators
abbrev Zcy (ι : Type*) := Fin 3 × Fin 3 × ι
variable {ι K : Type*} [Fintype ι] [Field K]
def ZaP (β : ι → K) (j i : Fin 3) : MvPolynomial (Zcy ι) K :=
 ∑ ν, MvPolynomial.C (β ν) * MvPolynomial.X (j, i, ν)
def Zr (β : ι → K) : MvPolynomial (Zcy ι) K :=
 Matrix.det (Matrix.of (fun i j => ZaP β j i))
def Zdf (e : Equiv.Perm (Fin 3)) (v : Zcy ι) : Zcy ι :=
 (e v.1, v.2)
@[simp] theorem Zmq (β : ι → K) (e : Equiv.Perm (Fin 3))
  (j i : Fin 3) :
  MvPolynomial.rename (Zdf (ι := ι) e) (ZaP β j i) =
   ZaP β (e j) i := by
 simp [ZaP, Zdf]
theorem ZhY (β : ι → K) (e : Equiv.Perm (Fin 3)) :
  MvPolynomial.rename (Zdf (ι := ι) e) (Zr β) =
   Equiv.Perm.sign e * Zr β := by
 rw [Zr, AlgHom.map_det]
 change Matrix.det (Matrix.of (fun i j =>
  MvPolynomial.rename (Zdf (ι := ι) e) (ZaP β j i))) = _
 simp_rw [Zmq]
 exact Matrix.det_permute' e (Matrix.of (fun i j => ZaP β j i))
theorem Zje (β : ι → K) {a b : Fin 3} (hab : a ≠ b) :
  MvPolynomial.rename (Zdf (ι := ι) (Equiv.swap a b))
   (Zr β) = -Zr β := by
 rw [ZhY, Equiv.Perm.sign_swap hab]
 simp
theorem Zcl (β : ι → K) (x : Zcy ι → K) :
  MvPolynomial.eval x (Zr β) =
   Matrix.det (Matrix.of (fun i j => ∑ ν, β ν * x (j, i, ν))) := by
 rw [Zr, RingHom.map_det]
 congr 1
 ext i j
 simp [ZaP, RingHom.mapMatrix_apply]
variable {F : Type*} [Field F] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
def ZT (β : ι → K) : MvPolynomial (Zcy ι) F :=
 Zbv.ZcB (F := F) (Zr β)
theorem Zhc (β : ι → K)
  (hodd : Odd (Module.finrank F K)) {a b : Fin 3} (hab : a ≠ b) :
  MvPolynomial.rename (Zdf (ι := ι) (Equiv.swap a b))
   (ZT (F := F) β) =
    -ZT (F := F) β :=
 Zbv.ZhX hodd _ _
  (Zje β hab)
def ZbI (b : Module.Basis ι F K) (A : Matrix (Fin 3) (Fin 3) K)
  (v : Zcy ι) : F :=
 b.repr (A v.2.1 v.1) v.2.2
omit [FiniteDimensional F K] [IsGalois F K] in
theorem Zdg (b : Module.Basis ι F K)
  (A : Matrix (Fin 3) (Fin 3) K) :
  MvPolynomial.eval (algebraMap F K ∘ ZbI b A)
   (Zr b) = A.det := by
 rw [Zcl]
 congr 1
 ext i j
 simpa [ZbI, Function.comp_def, Algebra.smul_def, mul_comm] using
  b.sum_repr (A i j)
theorem ZcI (b : Module.Basis ι F K)
  (A : Matrix (Fin 3) (Fin 3) K) :
  MvPolynomial.eval (ZbI b A)
   (ZT (F := F) b) = Algebra.norm F A.det := by
 rw [ZT, Zbv.ZnO,
  Zdg]
theorem Zet (b : Module.Basis ι F K)
  {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
  MvPolynomial.eval (ZbI b (ZbT.ZcH x y z))
   (ZT (F := F) b) ≠ 0 := by
 rw [ZcI]
 exact ZbT.Zhz hxy hxz hyz
def Zge (b : Module.Basis ι F K) (x : K) (v : Fin 3 × ι) : F :=
 b.repr (ZbT.Zoj x v.1) v.2
def ZlD (b : Module.Basis ι F K) (x y z : K) (v : Zcy ι) : F :=
 Zge b (![x, y, z] v.1) v.2
omit [Fintype ι] [FiniteDimensional F K] [IsGalois F K] in
theorem Zgf (b : Module.Basis ι F K) (x y z : K) :
  ZlD b x y z = ZbI b (ZbT.ZcH x y z) := by
 funext v
 rcases v with ⟨j, i, ν⟩
 fin_cases j <;> fin_cases i <;>
  simp [ZlD, Zge, ZbI,
   ZbT.Zoj, ZbT.ZcH]
theorem ZcY (b : Module.Basis ι F K)
  {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
  MvPolynomial.eval (ZlD b x y z)
   (ZT (F := F) b) ≠ 0 := by
 rw [Zgf]
 exact Zet b hxy hxz hyz
end Problem355.Zbk
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zq
variable (p : ℕ) [Fact p.Prime]
abbrev Label := GaloisField p Zae
def ZjP : Module.Basis (Fin Zae) (ZMod p) (Label p) :=
 (Module.finBasis (ZMod p) (Label p)).reindex
  (finCongr (GaloisField.finrank p (by norm_num [Zae])))
theorem Zrr : Nat.card (Label p) = p ^ Zae :=
 GaloisField.card p Zae (by norm_num [Zae])
theorem Znj : Module.finrank (ZMod p) (Label p) = Zae :=
 GaloisField.finrank p (by norm_num [Zae])
def ZaU :
  MvPolynomial (Zbk.Zcy (Fin Zae)) (ZMod p) :=
 Zbk.ZT (F := ZMod p) (ZjP p)
def Zih (x : Label p) : Fin 3 × Fin Zae → ZMod p :=
 Zbk.Zge (ZjP p) x
theorem ZeT {a b : Fin 3} (hab : a ≠ b) :
  MvPolynomial.rename (Zbk.Zdf (Equiv.swap a b))
   (ZaU p) = -ZaU p := by
 apply Zbk.Zhc _ _ hab
 rw [Znj]
 norm_num [Zae]
theorem Zgg {x y z : Label p}
  (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
  MvPolynomial.eval (fun v => Zih p (![x, y, z] v.1) v.2)
   (ZaU p) ≠ 0 :=
 Zbk.ZcY (ZjP p)
  hxy hxz hyz
end Problem355.Zq
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zhm
open scoped BigOperators
open MvPolynomial
lemma ZjQ {R S V M : Type*} [CommSemiring R] [CommSemiring S]
  [AddCommMonoid M] (f : R →+* S) {w : V → M} {P : MvPolynomial V R} {d : M}
  (hP : P.IsWeightedHomogeneous w d) : (P.map f).IsWeightedHomogeneous w d := by
 intro m hm
 apply hP
 intro hz
 apply hm
 simp [MvPolynomial.coeff_map, hz]
lemma ZhZ {R S V M : Type*} [CommSemiring R] [CommSemiring S]
  [AddCommMonoid M] (f : R →+* S) (hf : Function.Injective f)
  {w : V → M} {P : MvPolynomial V R} {d : M}
  (hP : (P.map f).IsWeightedHomogeneous w d) : P.IsWeightedHomogeneous w d := by
 intro m hm
 apply hP
 intro hz
 apply hm
 apply hf
 simpa only [MvPolynomial.coeff_map, map_zero] using hz
open Zbk
variable {ι K : Type*} [Fintype ι] [Field K]
def Zdh (g : Fin 3) (v : Zcy ι) : ℕ := if v.1 = g then 1 else 0
lemma ZeU (β : ι → K) (g j i : Fin 3) :
  (ZaP β j i).IsWeightedHomogeneous (Zdh g)
   (if j = g then 1 else 0) := by
 classical
 apply IsWeightedHomogeneous.sum
 intro ν hν
 simpa only [Zdh] using
  (isWeightedHomogeneous_X (R := K) (Zdh g) (j, i, ν)).C_mul (β ν)
theorem Zdk (β : ι → K) (g : Fin 3) :
  (Zr β).IsWeightedHomogeneous (Zdh g) 1 := by
 classical
 rw [Zr, Matrix.det_apply']
 apply IsWeightedHomogeneous.sum
 intro σ hσ
 have hp : (∏ j : Fin 3, ZaP β j (σ j)).IsWeightedHomogeneous
   (Zdh g) 1 := by
  simpa using IsWeightedHomogeneous.prod Finset.univ
   (fun j : Fin 3 => ZaP β j (σ j))
   (fun j : Fin 3 => if j = g then 1 else 0)
   (fun j _ => ZeU β g j (σ j))
 simpa using hp.C_mul ((Equiv.Perm.sign σ : ℤ) : K)
variable {F : Type*} [Field F] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
theorem Zfh {V M : Type*} [AddCommMonoid M]
  {w : V → M} {P : MvPolynomial V K} {d : M}
  (hP : P.IsWeightedHomogeneous w d) :
  (Zbv.Zay (F := F) P).IsWeightedHomogeneous w
   (Module.finrank F K • d) := by
 classical
 have hcard : Fintype.card (K ≃ₐ[F] K) = Module.finrank F K := by
  simpa only [Nat.card_eq_fintype_card] using IsGalois.card_aut_eq_finrank F K
 unfold Zbv.Zay
 simpa only [Finset.sum_const, Finset.card_univ, hcard] using
  IsWeightedHomogeneous.prod Finset.univ
   (fun σ : K ≃ₐ[F] K => MvPolynomial.map σ.toRingHom P)
   (fun _ => d) (fun σ _ => ZjQ σ.toRingHom hP)
theorem ZeV {V M : Type*} [AddCommMonoid M]
  {w : V → M} {P : MvPolynomial V K} {d : M}
  (hP : P.IsWeightedHomogeneous w d) :
  (Zbv.ZcB (F := F) P).IsWeightedHomogeneous w
   (Module.finrank F K • d) := by
 apply ZhZ (algebraMap F K) (algebraMap F K).injective
 rw [Zbv.ZcX]
 exact Zfh hP
theorem ZcO (β : ι → K) (g : Fin 3) :
  (ZT (F := F) β).IsWeightedHomogeneous
   (Zdh g) (Module.finrank F K) := by
 simpa [ZT] using
  ZeV (F := F)
   (Zdk β g)
end Problem355.Zhm
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZiH
abbrev Zen (α : Type*) (d : ℕ) :=
 {m : α →₀ ℕ // m.degree = d}
instance ZrF (α : Type*) [Fintype α] [DecidableEq α] (d : ℕ) :
  Fintype (Zen α d) :=
 Fintype.ofEquiv (Sym α d) (Sym.equivNatSum α d)
theorem Zpx (α : Type*) [Fintype α] [DecidableEq α] (d : ℕ) :
  Fintype.card (Zen α d) = Nat.choose (Fintype.card α + d - 1) d := by
 let e : Sym α d ≃ Zen α d := Sym.equivNatSum α d
 rw [← Fintype.card_congr e, Sym.card_sym_eq_choose]
def Zkt (d : ℕ) :
  Zen (Fin 3 × Fin d) d ≃ Fin (Nat.choose (4 * d - 1) d) :=
 Fintype.equivFinOfCardEq (by
  rw [Zpx, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  congr 2
  omega)
def Zbs :
  Zen (Fin 3 × Fin Zae) Zae ≃ Fin ZaH :=
 Zkt Zae
abbrev ZrO (α : Type*) [LT α] :=
 {t : α × α × α // t.1 < t.2.1 ∧ t.2.1 < t.2.2}
end Problem355.ZiH
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZaC
open MvPolynomial
variable {σ R : Type*}
def combine (a b c : σ →₀ ℕ) : (Fin 3 × σ) →₀ ℕ :=
 (Finsupp.equivFunOnFinite.symm ![a, b, c]).uncurry
@[simp] lemma Zol (a b c : σ →₀ ℕ) (i : σ) :
 combine a b c (0, i) = a i := rfl
@[simp] lemma ZoO (a b c : σ →₀ ℕ) (i : σ) :
 combine a b c (1, i) = b i := rfl
@[simp] lemma ZoP (a b c : σ →₀ ℕ) (i : σ) :
 combine a b c (2, i) = c i := rfl
lemma ZoQ : Function.Injective
  (fun t : (σ →₀ ℕ) × (σ →₀ ℕ) × (σ →₀ ℕ) => combine t.1 t.2.1 t.2.2) := by
 intro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
 have ha : a = a' := by
  ext i
  exact congrArg (fun d => d (0, i)) h
 have hb : b = b' := by
  ext i
  exact congrArg (fun d => d (1, i)) h
 have hc : c = c' := by
  ext i
  exact congrArg (fun d => d (2, i)) h
 simp only [Prod.mk.injEq]
 exact ⟨ha, hb, hc⟩
def ZdJ (i j : Fin 3) : Equiv.Perm (Fin 3 × σ) :=
 Equiv.prodCongr (Equiv.swap i j) (Equiv.refl σ)
@[simp] lemma ZrG (a b c : σ →₀ ℕ) :
  (combine a b c).mapDomain (ZdJ (σ := σ) 0 1) = combine b a c := by
 ext ⟨i, s⟩
 rw [Finsupp.mapDomain_equiv_apply]
 fin_cases i <;> simp [ZdJ, combine, Finsupp.uncurry_apply, Equiv.swap_apply_def]
@[simp] lemma ZrH (a b c : σ →₀ ℕ) :
  (combine a b c).mapDomain (ZdJ (σ := σ) 1 2) = combine a c b := by
 ext ⟨i, s⟩
 rw [Finsupp.mapDomain_equiv_apply]
 fin_cases i <;> simp [ZdJ, combine, Finsupp.uncurry_apply, Equiv.swap_apply_def]
lemma ZqK (d : (Fin 3 × σ) →₀ ℕ) :
  combine (d.curry 0) (d.curry 1) (d.curry 2) = d := by
 ext ⟨i, s⟩
 fin_cases i <;> rfl
lemma ZkS {ι : Type*} (e : ι → σ →₀ ℕ)
  (he : Function.Injective e) : Function.Injective
   (fun t : ι × ι × ι => combine (e t.1) (e t.2.1) (e t.2.2)) := by
 intro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
 have h' : (e a, e b, e c) = (e a', e b', e c') :=
  @ZoQ σ (e a, e b, e c) (e a', e b', e c') h
 simp only [Prod.mk.injEq] at h' ⊢
 exact ⟨he h'.1, he h'.2.1, he h'.2.2⟩
lemma ZlE [Fintype σ] (d : (Fin 3 × σ) →₀ ℕ) (j : Fin 3) :
  (d.curry j).degree =
   Finsupp.weight (fun v : Fin 3 × σ => if v.1 = j then (1 : ℕ) else 0) d := by
 classical
 rw [Finsupp.degree_eq_sum, Finsupp.weight_apply,
  Finsupp.sum_fintype _ _ (by intro i; simp), Fintype.sum_prod_type]
 simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
 simp
section Expansion
variable [CommSemiring R]
lemma ZmX {ι : Type*} [Fintype ι]
  (P : MvPolynomial σ R) (e : ι → σ →₀ ℕ) (he : Function.Injective e)
  (hP : ∀ d ∈ P.support, d ∈ Set.range e) :
  P = ∑ i, monomial (e i) (P.coeff (e i)) := by
 classical
 calc
  P = ∑ d ∈ P.support, monomial d (P.coeff d) := P.as_sum
  _ = ∑ d ∈ Finset.univ.image e, monomial d (P.coeff d) := by
   apply Finset.sum_subset
   · intro d hd
     obtain ⟨i, rfl⟩ := hP d hd
     exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
   · intro d _ hd
     simp [MvPolynomial.notMem_support_iff.mp hd]
  _ = _ := Finset.sum_image (fun i _ j _ hij => he hij)
lemma Zmr {ι : Type*} [Fintype ι]
  (P : MvPolynomial (Fin 3 × σ) R) (e : ι → σ →₀ ℕ)
  (he : Function.Injective e)
  (hP : ∀ d ∈ P.support, ∀ j : Fin 3, d.curry j ∈ Set.range e) :
  P = ∑ a, ∑ b, ∑ c,
   monomial (combine (e a) (e b) (e c))
    (P.coeff (combine (e a) (e b) (e c))) := by
 classical
 have hsupport : ∀ d ∈ P.support, d ∈ Set.range
   (fun t : ι × ι × ι => combine (e t.1) (e t.2.1) (e t.2.2)) := by
  intro d hd
  obtain ⟨a, ha⟩ := hP d hd 0
  obtain ⟨b, hb⟩ := hP d hd 1
  obtain ⟨c, hc⟩ := hP d hd 2
  refine ⟨(a, b, c), ?_⟩
  simp only [ha, hb, hc]
  exact ZqK d
 simpa only [Fintype.sum_prod_type] using
  ZmX P _ (ZkS e he) hsupport
lemma Zms [Fintype σ] (a b c : σ →₀ ℕ) (r : R)
  (x : Fin 3 × σ → R) :
  eval x (monomial (combine a b c) r) =
   r * eval (fun s => x (0, s)) (monomial a 1) *
    eval (fun s => x (1, s)) (monomial b 1) *
    eval (fun s => x (2, s)) (monomial c 1) := by
 classical
 simp only [eval_monomial]
 repeat rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
 simp only [Fintype.prod_prod_type, Fin.prod_univ_three, Zol,
  ZoO, ZoP, one_mul, mul_assoc]
lemma Zjf [Fintype σ] {ι : Type*} [Fintype ι]
  (P : MvPolynomial (Fin 3 × σ) R) (e : ι → σ →₀ ℕ)
  (he : Function.Injective e)
  (hP : ∀ d ∈ P.support, ∀ j : Fin 3, d.curry j ∈ Set.range e)
  (x : Fin 3 × σ → R) :
  eval x P = ∑ a, ∑ b, ∑ c,
   P.coeff (combine (e a) (e b) (e c)) *
    eval (fun s => x (0, s)) (monomial (e a) 1) *
    eval (fun s => x (1, s)) (monomial (e b) 1) *
    eval (fun s => x (2, s)) (monomial (e c) 1) := by
 conv_lhs => rw [Zmr P e he hP]
 simp only [map_sum, Zms]
end Expansion
variable [CommRing R]
lemma ZfL (e : Equiv.Perm σ) (P : MvPolynomial σ R)
  (hP : rename e P = -P) (d : σ →₀ ℕ) :
  P.coeff (d.mapDomain e) = -P.coeff d := by
 have h := coeff_rename_mapDomain e e.injective P d
 rw [hP, coeff_neg] at h
 exact neg_eq_iff_eq_neg.mp h
def Zcz (P : MvPolynomial (Fin 3 × σ) R) (a b c : σ →₀ ℕ) : R :=
 P.coeff (combine a b c)
lemma Zom (P : MvPolynomial (Fin 3 × σ) R)
  (hP : rename (ZdJ (σ := σ) 0 1) P = -P) (a b c : σ →₀ ℕ) :
  Zcz P b a c = -Zcz P a b c := by
 simpa [Zcz] using
  ZfL (ZdJ 0 1) P hP (combine a b c)
lemma Zon (P : MvPolynomial (Fin 3 × σ) R)
  (hP : rename (ZdJ (σ := σ) 1 2) P = -P) (a b c : σ →₀ ℕ) :
  Zcz P a c b = -Zcz P a b c := by
 simpa [Zcz] using
  ZfL (ZdJ 1 2) P hP (combine a b c)
end Problem355.ZaC
end
end OAI
end
section
namespace OAI
namespace Problem355.Zdn
open scoped BigOperators
variable {ι R : Type*} [Fintype ι] [CommRing R]
private theorem Zia (f : ι → ι → ι → R) :
  (∑ i, ∑ j, ∑ k, f j i k) = ∑ i, ∑ j, ∑ k, f i j k := by
 rw [Finset.sum_comm]
private theorem ZfX (f : ι → ι → ι → R) :
  (∑ i, ∑ j, ∑ k, f i k j) = ∑ i, ∑ j, ∑ k, f i j k := by
 apply Finset.sum_congr rfl
 intro i _
 rw [Finset.sum_comm]
private theorem Zrs (f : ι → ι → ι → R) :
  (∑ i, ∑ j, ∑ k, f k i j) = ∑ i, ∑ j, ∑ k, f i j k := by
 calc
  (∑ i, ∑ j, ∑ k, f k i j) = ∑ i, ∑ j, ∑ k, f j i k :=
   ZfX (fun i j k => f j i k)
  _ = ∑ i, ∑ j, ∑ k, f i j k := Zia f
private theorem ZoV (f : ι → ι → ι → R) :
  (∑ i, ∑ j, ∑ k, f j k i) = ∑ i, ∑ j, ∑ k, f i j k := by
 calc
  (∑ i, ∑ j, ∑ k, f j k i) = ∑ i, ∑ j, ∑ k, f i k j :=
   Zia (fun i j k => f i k j)
  _ = ∑ i, ∑ j, ∑ k, f i j k := ZfX f
private theorem Zri (f : ι → ι → ι → R) :
  (∑ i, ∑ j, ∑ k, f k j i) = ∑ i, ∑ j, ∑ k, f i j k := by
 calc
  (∑ i, ∑ j, ∑ k, f k j i) = ∑ i, ∑ j, ∑ k, f j k i :=
   ZfX (fun i j k => f j k i)
  _ = ∑ i, ∑ j, ∑ k, f i j k := ZoV f
noncomputable def ZbZ {X : Type*} (c : ι → ι → ι → R) (m : ι → X → R)
  (t : ι × ι × ι) : Fin 3 → X → R :=
 ![fun x => c t.1 t.2.1 t.2.2 * m t.1 x, m t.2.1, m t.2.2]
theorem ZoR {X : Type*} (c : ι → ι → ι → R) (m : ι → X → R)
  (s : ∀ i j k, c j i k = -c i j k) (u : ∀ i j k, c i k j = -c i j k) (x y z : X) :
  (∑ t : ι × ι × ι, Matrix.det (fun i j => ZbZ c m t i (![x,y,z] j))) =
   6 * ∑ i, ∑ j, ∑ k, c i j k * m i x * m j y * m k z := by
 let f := fun i j k => c i j k * m i x * m j y * m k z
 have h (i j k : ι) : Matrix.det (fun a b => ZbZ c m (i,j,k) a (![x,y,z] b)) =
   f i j k + f j i k + f i k j + f k i j + f j k i + f k j i := by
  have a := s i j k
  have b := u i j k
  have d : c k i j = c i j k := by rw [s, b, neg_neg]
  have e : c j k i = c i j k := by rw [u, a, neg_neg]
  have g : c k j i = -c i j k := by rw [s, e]
  rw [Matrix.det_fin_three (fun a b => ZbZ c m (i,j,k) a (![x,y,z] b))]
  simp [ZbZ, f, a, b, d, e, g]
  <;> ring
 simp only [Fintype.sum_prod_type, h, Finset.sum_add_distrib]
 rw [Zia f, ZfX f, Zrs f, ZoV f, Zri f]
 change _ = 6 * ∑ i, ∑ j, ∑ k, f i j k
 ring
end Problem355.Zdn
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zfa
open scoped BigOperators
open MvPolynomial
abbrev ZmY := Fin 3 × Fin Zae
def ZaZ (i : Fin ZaH) : ZmY →₀ ℕ :=
 (ZiH.Zbs.symm i).val
theorem Zjg : Function.Injective ZaZ :=
 Subtype.val_injective.comp ZiH.Zbs.symm.injective
variable (p : ℕ) [Fact p.Prime]
theorem ZkT (d : (Fin 3 × ZmY) →₀ ℕ)
  (hd : d ∈ (Zq.ZaU p).support) (j : Fin 3) :
  d.curry j ∈ Set.range ZaZ := by
 have hdegree : (d.curry j).degree = Zae := by
  rw [ZaC.ZlE]
  change Finsupp.weight (Zhm.Zdh j) d = Zae
  have h := Zhm.ZcO
   (Zq.ZjP p) j
   (MvPolynomial.mem_support_iff.mp hd)
  simpa only [Zq.Znj] using h
 let m : ZiH.Zen ZmY Zae := ⟨d.curry j, hdegree⟩
 refine ⟨ZiH.Zbs m, ?_⟩
 simp [ZaZ, m]
def Zbj (i j k : Fin ZaH) : ZMod p :=
 ZaC.Zcz (Zq.ZaU p)
  (ZaZ i) (ZaZ j) (ZaZ k)
def ZcR (i : Fin ZaH) (x : Zq.Label p) : ZMod p :=
 MvPolynomial.eval (Zq.Zih p x) (monomial (ZaZ i) 1)
theorem ZlF (i j k : Fin ZaH) :
  Zbj p j i k = -Zbj p i j k := by
 apply ZaC.Zom
 exact Zq.ZeT p (by decide : (0 : Fin 3) ≠ 1)
theorem ZlG (i j k : Fin ZaH) :
  Zbj p i k j = -Zbj p i j k := by
 apply ZaC.Zon
 exact Zq.ZeT p (by decide : (1 : Fin 3) ≠ 2)
theorem ZgD (x y z : Zq.Label p) :
  MvPolynomial.eval (fun v => Zq.Zih p (![x, y, z] v.1) v.2)
   (Zq.ZaU p) =
   ∑ i, ∑ j, ∑ k, Zbj p i j k * ZcR p i x *
    ZcR p j y * ZcR p k z := by
 simpa [Zbj, ZaC.Zcz, ZcR] using
  ZaC.Zjf
   (Zq.ZaU p) ZaZ Zjg
   (ZkT p)
   (fun v => Zq.Zih p (![x, y, z] v.1) v.2)
private abbrev I := Fin ZaH
private def ZoW : Fin Zam ≃ I × I × I :=
 (Fintype.equivFinOfCardEq (by simp [Zam, I, pow_succ, mul_assoc] :
  Fintype.card (I × I × I) = Zam)).symm
def ZcJ (i : Fin 3) (a : Fin Zam)
  (x : Zq.Label p) : ZMod p :=
 Zdn.ZbZ (Zbj p) (ZcR p) (ZoW a) i x
theorem Zib (hp : 6 < p)
  {x y z : Zq.Label p} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
  (∑ a : Fin Zam,
   Matrix.det (fun i j => ZcJ p i a (![x, y, z] j))) ≠ 0 := by
 unfold ZcJ
 rw [ZoW.sum_comp (fun t => Matrix.det (fun i j =>
  Zdn.ZbZ (Zbj p) (ZcR p) t i (![x,y,z] j))),
  Zdn.ZoR _ _ (ZlF p) (ZlG p),
  ← ZgD]
 apply mul_ne_zero _ (Zq.Zgg p hxy hxz hyz)
 exact fun h => Nat.not_dvd_of_pos_of_lt (by decide) hp ((ZMod.natCast_eq_zero_iff 6 p).mp h)
end Problem355.Zfa
end
end OAI
end
section
namespace OAI
namespace Problem355.Zcn
theorem Zqc {T a b c : ℕ} (ha : a < T) (hc : c < T)
   (h : a + T * b = (T + 1) * c) : a = c ∧ b = c := by
 have h' : a + T * b = c + T * c := by nlinarith
 have hmod := congrArg (fun x : ℕ => x % T) h'
 have hac : a = c := by
   simpa [Nat.add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] using hmod
 subst a
 constructor
 · rfl
 · have hT : 0 < T := Nat.zero_lt_of_lt hc
   nlinarith
end Problem355.Zcn
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zch
open Polynomial
def position (T : ℕ) (i : Fin 3) (a : Fin T) : ℕ :=
 ![a.val, T * a.val, T ^ 2 - (T + 1) * a.val] i
theorem Zgn (T : ℕ) (v : Fin 3 → Fin T) :
   position T 0 (v 0) + position T 1 (v 1) + position T 2 (v 2) = T ^ 2 ↔
    v 0 = v 1 ∧ v 1 = v 2 := by
 have hle : (T + 1) * (v 2).val ≤ T ^ 2 := by
   have hv : (v 2).val + 1 ≤ T := (v 2).isLt
   have hh := Nat.mul_le_mul_left (T + 1) hv
   nlinarith
 have hsub := Nat.sub_add_cancel hle
 change (v 0).val + T * (v 1).val + (T ^ 2 - (T + 1) * (v 2).val) = T ^ 2 ↔
   v 0 = v 1 ∧ v 1 = v 2
 constructor
 · intro h
   have hm := Zcn.Zqc (v 0).isLt (v 2).isLt
    (show (v 0).val + T * (v 1).val = (T + 1) * (v 2).val by omega)
   exact ⟨Fin.ext (hm.1.trans hm.2.symm), Fin.ext hm.2⟩
 · rintro ⟨h01, h12⟩
   have hv0 : (v 0).val = (v 2).val := congrArg Fin.val (h01.trans h12)
   have hv1 : (v 1).val = (v 2).val := congrArg Fin.val h12
   rw [hv0, hv1]
   nlinarith
theorem ZqX {R : Type*} [AddCommMonoid R] (T : ℕ)
   (F : (Fin 3 → Fin T) → R) :
   (∑ v : Fin 3 → Fin T, if v 0 = v 1 ∧ v 1 = v 2 then F v else 0) =
    ∑ a : Fin T, F (fun _ => a) := by
 classical
 rw [← Finset.sum_filter]
 symm
 apply Finset.sum_bij (fun a _ => fun _ : Fin 3 => a)
 · intro a ha
   simp
 · intro a ha b hb hab
   exact congrFun hab 0
 · intro v hv
   rcases Finset.mem_filter.mp hv with ⟨_, h01, h12⟩
   refine ⟨v 0, Finset.mem_univ _, ?_⟩
   funext i
   fin_cases i <;> simp_all
 · intro a ha
   rfl
theorem ZoS {R : Type*} [CommRing R]
  (v : Fin 3 → ℕ) (A : Matrix (Fin 3) (Fin 3) R) :
  Matrix.det (Matrix.of (fun i j => monomial (v i) (A i j))) =
   monomial (v 0 + v 1 + v 2) A.det := by
 simp only [Matrix.det_fin_three, Matrix.of_apply, Polynomial.monomial_mul_monomial, map_add, map_sub]
def Zba {R : Type*} [CommRing R] (T : ℕ)
  (f : Fin 3 → Fin T → Fin 3 → R) : Matrix (Fin 3) (Fin 3) R[X] :=
 fun i j => ∑ a : Fin T, monomial (position T i a) (f i a j)
theorem ZlH {R : Type*} [CommRing R] (T : ℕ)
  (f : Fin 3 → Fin T → Fin 3 → R) :
  (Matrix.det (Zba T f)).coeff (T ^ 2) =
   ∑ a : Fin T, Matrix.det (Matrix.of (fun i j => f i a j)) := by
 classical
 have hm := (Matrix.detRowAlternating (n := Fin 3) (R := R[X])).toMultilinearMap.map_sum_finset
  (fun i (a : Fin T) j => monomial (position T i a) (f i a j))
  (fun _ => Finset.univ)
 change Matrix.det (Matrix.of (fun i => ∑ a : Fin T, fun j =>
  monomial (position T i a) (f i a j))) = _ at hm
 have hrows : (fun i => ∑ a : Fin T, fun j =>
   monomial (position T i a) (f i a j)) = Zba T f := by
  funext i j
  simp only [Finset.sum_apply, Zba]
 rw [hrows, Fintype.piFinset_univ] at hm
 change (Zba T f).det = _ at hm
 rw [hm, Polynomial.finsetSum_coeff]
 change (∑ v : Fin 3 → Fin T,
  (Matrix.det (Matrix.of (fun i j => monomial (position T i (v i)) (f i (v i) j)))).coeff
   (T ^ 2)) = _
 calc
  _ = ∑ v : Fin 3 → Fin T,
     if v 0 = v 1 ∧ v 1 = v 2 then Matrix.det (Matrix.of (fun i j => f i (v i) j)) else 0 := by
   apply Finset.sum_congr rfl
   intro v hv
   have hdet := ZoS (fun i => position T i (v i))
     (Matrix.of (fun i j => f i (v i) j))
   simp only [Matrix.of_apply] at hdet
   rw [hdet, Polynomial.coeff_monomial]
   by_cases h : v 0 = v 1 ∧ v 1 = v 2
   · have hp := (Zgn T v).mpr h
     rw [if_pos hp, if_pos h]
   · have hp : ¬ (position T 0 (v 0) + position T 1 (v 1) +
      position T 2 (v 2) = T ^ 2) := fun hp => h ((Zgn T v).mp hp)
     rw [if_neg hp, if_neg h]
  _ = _ := ZqX T (fun v => Matrix.det (Matrix.of (fun i j => f i (v i) j)))
theorem Zjh {R : Type*} [CommRing R] (φ : ℤ →+* R)
  (T : ℕ) (P : Matrix (Fin 3) (Fin 3) ℤ[X])
  (f : Fin 3 → Fin T → Fin 3 → R)
  (hmap : ∀ i j, (P i j).map φ = Zba T f i j) :
  φ (P.det.coeff (T ^ 2)) = ∑ a : Fin T, Matrix.det (Matrix.of (fun i j => f i a j)) := by
 have hm : P.det.map φ = Matrix.det (Matrix.of (fun i j => (P i j).map φ)) :=
  (Polynomial.mapRingHom φ).map_det P
 have hmatrix : (fun i j => (P i j).map φ) = Zba T f := by
  funext i j
  exact hmap i j
 rw [hmatrix] at hm
 rw [← Polynomial.coeff_map, hm]
 exact ZlH T f
theorem Zhd {R : Type*} [CommRing R] (φ : ℤ →+* R)
  (T : ℕ) (P : Matrix (Fin 3) (Fin 3) ℤ[X])
  (f : Fin 3 → Fin T → Fin 3 → R)
  (hmap : ∀ i j, (P i j).map φ = Zba T f i j)
  (hne : (∑ a : Fin T, Matrix.det (Matrix.of (fun i j => f i a j))) ≠ 0) :
  P.det.coeff (T ^ 2) ≠ 0 := by
 intro hz
 apply hne
 rw [← Zjh φ T P f hmap, hz, map_zero]
end Problem355.Zch
end
end OAI
end
section
namespace OAI
namespace Problem355.ZaF
noncomputable section
open scoped BigOperators
open Polynomial
def ZK (k : ℕ) (a : ℕ → ℤ) : ℤ[X] :=
 ∑ i ∈ Finset.range k, monomial i (a i)
lemma Zgo (k u : ℕ) (a : ℕ → ℤ) :
  (ZK k a).coeff u = if u < k then a u else 0 := by
 classical
 simp [ZK, Polynomial.coeff_monomial]
lemma Zic (k : ℕ) (a : ℕ → ℤ) (L : ℤ)
   (hL : 0 ≤ L) (ha : ∀ i < k, |a i| ≤ L) (u : ℕ) :
   |(ZK k a).coeff u| ≤ L := by
 rw [Zgo]
 split_ifs with h
 · exact ha u h
 · simpa using hL
lemma ZcK (k : ℕ) (a : ℕ → ℤ)
  (q : ℤ[X]) (L M : ℤ) (hL : 0 ≤ L) (hM : 0 ≤ M)
  (ha : ∀ i < k, |a i| ≤ L) (hq : ∀ i, |q.coeff i| ≤ M) (u : ℕ) :
  |(ZK k a * q).coeff u| ≤ (k : ℤ) * L * M := by
 classical
 unfold ZK
 rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
 calc
  |∑ i ∈ Finset.range k, ((monomial i (a i)) * q).coeff u| ≤
     ∑ i ∈ Finset.range k, |((monomial i (a i)) * q).coeff u| :=
   Finset.abs_sum_le_sum_abs _ _
  _ ≤ ∑ _i ∈ Finset.range k, L * M := by
   apply Finset.sum_le_sum
   intro i hi
   rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc,
     Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
   split_ifs with h
   · rw [abs_mul]
     exact mul_le_mul (ha i (Finset.mem_range.mp hi)) (hq (u-i))
      (abs_nonneg _) hL
   · simp only [mul_zero, abs_zero]
     exact mul_nonneg hL hM
  _ = (k : ℤ) * L * M := by simp; ring
lemma Zfi (k : ℕ) (a b c : ℕ → ℤ)
  (L : ℤ) (hL : 0 ≤ L)
  (ha : ∀ i < k, |a i| ≤ L) (hb : ∀ i < k, |b i| ≤ L)
  (hc : ∀ i < k, |c i| ≤ L) (u : ℕ) :
  |(ZK k a * ZK k b * ZK k c).coeff u|
   ≤ (k : ℤ)^2 * L^3 := by
 rw [mul_assoc]
 have hbc : ∀ i, |(ZK k b * ZK k c).coeff i|
   ≤ (k : ℤ) * L * L :=
  ZcK k b (ZK k c) L L hL hL hb
   (Zic k c L hL hc)
 have h := ZcK k a
  (ZK k b * ZK k c) L ((k : ℤ) * L * L)
  hL (by positivity) ha hbc u
 convert h using 1; ring
def Zr (k : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ) : ℤ[X] :=
 Matrix.det (Matrix.of (fun i j => ZK k (d i j)))
theorem Zfu (k : ℕ)
  (d : Fin 3 → Fin 3 → ℕ → ℤ) (L : ℤ) (hL : 0 ≤ L)
  (hd : ∀ i j v, v < k → |d i j v| ≤ L) (u : ℕ) :
  |(Zr k d).coeff u| ≤ 6 * (k : ℤ)^2 * L^3 := by
 have ht (i j m n s t : Fin 3) := abs_le.mp
  (Zfi k (d i j) (d m n) (d s t)
   L hL (hd i j) (hd m n) (hd s t) u)
 have h₁ := ht 0 0 1 1 2 2
 have h₂ := ht 0 0 1 2 2 1
 have h₃ := ht 0 1 1 0 2 2
 have h₄ := ht 0 1 1 2 2 0
 have h₅ := ht 0 2 1 0 2 1
 have h₆ := ht 0 2 1 1 2 0
 unfold Zr
 rw [Matrix.det_fin_three]
 simp only [Matrix.of_apply]
 simp only [Polynomial.coeff_add, Polynomial.coeff_sub]
 apply abs_le.mpr
 constructor <;> nlinarith
lemma ZmZ (k : ℕ) (a : ℕ → ℤ) (B : ℤ) :
  (ZK k a).eval B = ∑ i ∈ Finset.range k, a i * B^i := by
 simp [ZK, Polynomial.eval_finsetSum]
lemma Zcl (k : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ) (B : ℤ) :
  (Zr k d).eval B =
   Matrix.det (Matrix.of (fun i j => ∑ v ∈ Finset.range k, d i j v * B^v)) := by
 simp only [Zr, Matrix.det_fin_three, Matrix.of_apply, Polynomial.eval_sub,
  Polynomial.eval_add, Polynomial.eval_mul, ZmZ]
end
end Problem355.ZaF
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zch
open Polynomial
lemma Zrj (T : ℕ) (i : Fin 3) (a : Fin T) :
   position T i a < T ^ 2 + 1 := by
 have hT : 0 < T := Nat.zero_lt_of_lt a.isLt
 fin_cases i
 · change a.val < T ^ 2 + 1
   have ha := a.isLt
   nlinarith
 · change T * a.val < T ^ 2 + 1
   have ha := Nat.mul_lt_mul_of_pos_left a.isLt hT
   nlinarith
 · change T ^ 2 - (T + 1) * a.val < T ^ 2 + 1
   exact Nat.lt_succ_of_le (Nat.sub_le _ _)
end Problem355.Zch
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zjl
open Zch
def residue {R Λ : Type*} [AddCommMonoid R] (T : ℕ)
  (f : Fin 3 → Fin T → Λ → R) (i : Fin 3) (v : ℕ) (x : Λ) : R :=
 ∑ a : Fin T, if position T i a = v then f i a x else 0
theorem ZdT {R Λ : Type*} [CommRing R]
   (φ : ℤ →+* R) (T K : ℕ) (hK : K = T ^ 2 + 1)
   (B L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
   (hbase : 100 * (K : ℤ) ^ 2 * L ^ 3 < B)
   (f : Fin 3 → Fin T → Λ → R) (labels : Fin 3 → Λ)
   (d : Fin 3 → Fin 3 → ℕ → ℤ)
   (hd : ∀ i j v, v < K → |d i j v| ≤ L)
   (hresidue : ∀ i j v, v < K → φ (d i j v) = residue T f i v (labels j))
   (hne : (∑ a : Fin T, Matrix.det (fun i j => f i a (labels j))) ≠ 0)
   {x : ℤ} (hx : x ≡ (ZaF.Zr K d).eval B
     [ZMOD B ^ K]) : B ^ (K - 1) / 2 < |x| := by
 subst K
 rw [Nat.add_sub_cancel]
 apply Zcn.Zla (ZaF.Zr (T ^ 2 + 1) d)
   B hB (T ^ 2) _ _ hx
 · intro n _
   exact Zcn.ZhM hbase
     (ZaF.Zfu _ d L hL hd n)
 · apply Zhd φ T
     (fun i j => ZaF.ZK (T ^ 2 + 1) (d i j)) _ _ hne
   intro i j
   ext n
   rw [Polynomial.coeff_map, ZaF.Zgo]
   simp only [Zba, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
   by_cases hn : n < T ^ 2 + 1
   · simpa only [if_pos hn, residue] using hresidue i j n hn
   · rw [if_neg hn, map_zero]
     exact (Finset.sum_eq_zero fun a _ => if_neg (ne_of_lt (lt_of_lt_of_le
      (Zrj T i a) (Nat.le_of_not_lt hn)))).symm
end Problem355.Zjl
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zax
open Zq
variable (p : ℕ) [Fact p.Prime]
def Zdm (i : Fin 3) (v : ℕ) (x : Label p) : ZMod p :=
 Zjl.residue Zam (Zfa.ZcJ p) i v x
theorem Zoo (hp : 6 < p) (labels : Fin 3 → Label p)
  (hinj : Function.Injective labels) :
  (∑ a : Fin Zam,
   Matrix.det (fun i j => Zfa.ZcJ p i a (labels j))) ≠ 0 := by
 have h01 : labels 0 ≠ labels 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)
 have h02 : labels 0 ≠ labels 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h)
 have h12 : labels 1 ≠ labels 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h)
 have hlabels : (![labels 0, labels 1, labels 2] : Fin 3 → Label p) = labels := by
  funext i
  fin_cases i <;> rfl
 simpa only [hlabels] using Zfa.Zib p hp h01 h02 h12
theorem ZaK (hp : 6 < p)
  (B : ℕ) (L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
  (hbase : 100 * (Za : ℤ) ^ 2 * L ^ 3 < B)
  (labels : Fin 3 → Label p) (d : Fin 3 → Fin 3 → ℕ → ℤ)
  (hd : ∀ i j v, v < Za → |d i j v| ≤ L)
  (hresidue : ∀ i j v, v < Za →
   (Int.castRingHom (ZMod p)) (d i j v) = Zdm p i v (labels j))
  (A : Matrix (Fin 3) (Fin 3) ℤ)
  (h : ℕ) (hh : h = B ^ Za)
  (G : Matrix.SpecialLinearGroup (Fin 3) (ZMod h))
  (hAC : A.map (Int.castRingHom (ZMod h)) =
   (G : Matrix (Fin 3) (Fin 3) (ZMod h)) *
    (Matrix.map (fun i j => ∑ v ∈ Finset.range Za, d i j v * (B : ℤ) ^ v)
     (Int.castRingHom (ZMod h))))
  (hsmall : |A.det| ≤ (B : ℤ) ^ (Za - 1) / 2) :
  ∃ i j : Fin 3, i ≠ j ∧ labels i = labels j := by
 classical
 by_contra hn
 have hinj : Function.Injective labels := by
  intro i j hij
  by_contra hne
  exact hn ⟨i, j, hne, hij⟩
 have hmod := Zcn.Zfp h G A
  (fun i j => ∑ v ∈ Finset.range Za, d i j v * (B : ℤ) ^ v) hAC
 have hpoly : A.det ≡ (ZaF.Zr Za d).eval
   (B : ℤ) [ZMOD (B : ℤ) ^ Za] := by
  suffices ∀ (length modulus : ℕ), modulus = B ^ length →
    A.det ≡ Matrix.det (fun i j => ∑ v ∈ Finset.range length,
     d i j v * (B : ℤ) ^ v) [ZMOD modulus] →
    A.det ≡ (ZaF.Zr length d).eval
     (B : ℤ) [ZMOD (B : ℤ) ^ length] from this Za h hh hmod
  intro length modulus hmodulus hdet
  rw [ZaF.Zcl]
  change A.det ≡ Matrix.det (fun i j => ∑ v ∈ Finset.range length,
   d i j v * (B : ℤ) ^ v) [ZMOD (B : ℤ) ^ length]
  simpa only [hmodulus, Nat.cast_pow] using hdet
 have hout := Zjl.ZdT
  (Int.castRingHom (ZMod p)) Zam Za ZqA (B : ℤ) L (by exact_mod_cast hB) hL hbase
  (Zfa.ZcJ p) labels d hd hresidue
  (Zoo p hp labels hinj) hpoly
 apply (not_lt_of_ge hsmall)
 exact hout
def Zej (i : Fin 3) (v : Fin Za) (x : Label p) : ZMod p :=
 Zdm p i v.val x
end Problem355.Zax
end
end OAI
end
section
namespace OAI
namespace Problem355.ZqZ
theorem Zji {b j : ℕ} (hb : 1 < b)
   {A B : List ℕ} (hlen : A.length = B.length)
   (hA : ∀ a ∈ A, a < b) (hB : ∀ a ∈ B, a < b)
   (hmod : Nat.ofDigits b A % b ^ j = Nat.ofDigits b B % b ^ j) :
   A.take j = B.take j := by
 apply Nat.ofDigits_inj_of_len_eq hb
 · simp [hlen]
 · exact fun a ha => hA a (List.mem_of_mem_take ha)
 · exact fun a ha => hB a (List.mem_of_mem_take ha)
 · simpa only [Nat.ofDigits_mod_pow_eq_ofDigits_take j (by omega) A hA,
    Nat.ofDigits_mod_pow_eq_ofDigits_take j (by omega) B hB] using hmod
theorem Zhe (b : ℕ) {k : ℕ} (d : Fin k → ℕ) :
  Nat.ofDigits b (List.ofFn d) = ∑ i : Fin k, d i * b ^ i.val := by
 simp [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn,
  List.length_ofFn, Fin.val_cast, List.sum_ofFn]
theorem ZgE {b k j : ℕ} (hb : 1 < b)
  {d e : Fin k → ℕ} (hd : ∀ i, d i < b) (he : ∀ i, e i < b)
  (hmod : (∑ i : Fin k, d i * b ^ i.val) % b ^ j =
    (∑ i : Fin k, e i * b ^ i.val) % b ^ j) :
  ∀ i : Fin k, i.val < j → d i = e i := by
 have htake : (List.ofFn d).take j = (List.ofFn e).take j := by
  apply Zji hb (by simp)
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hd i
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact he i
  · simpa only [Zhe] using hmod
 intro i hi
 have hget := congrArg (fun l : List ℕ => l[i.val]?) htake
 simpa [List.getElem?_take, hi] using hget
end Problem355.ZqZ
end OAI
end
section
namespace OAI
open scoped BigOperators
namespace Problem355.Znp
theorem ZfM
  {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (b : Ω → ℕ)
  (B ρ : ℝ) (k : ℕ)
  (hp : ∀ ω, 0 ≤ p ω) (hB : 0 ≤ B)
  (hb : ∀ ω, b ω ≤ k)
  (htail : ∀ j, j ≤ k →
   (∑ ω, if j ≤ b ω then p ω else 0) ≤ ρ ^ j) :
  (∑ ω, p ω * B ^ b ω) ≤
   ∑ j ∈ Finset.range (k + 1), (B * ρ) ^ j := by
 classical
 calc
  (∑ ω, p ω * B ^ b ω) ≤
    ∑ ω, p ω * (∑ j ∈ Finset.range (k + 1),
     if j ≤ b ω then B ^ j else 0) := by
   apply Finset.sum_le_sum
   intro ω _
   apply mul_le_mul_of_nonneg_left _ (hp ω)
   have hsingle := Finset.single_le_sum
    (s := Finset.range (k + 1))
    (f := fun j => if j ≤ b ω then B ^ j else 0)
    (fun j _ => by split_ifs <;> positivity)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (hb ω)))
   simpa using hsingle
  _ = ∑ j ∈ Finset.range (k + 1),
    B ^ j * (∑ ω, if j ≤ b ω then p ω else 0) := by
   simp_rw [Finset.mul_sum]
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro j _
   apply Finset.sum_congr rfl
   intro ω _
   split_ifs <;> simp [mul_comm]
  _ ≤ ∑ j ∈ Finset.range (k + 1), B ^ j * ρ ^ j := by
   apply Finset.sum_le_sum
   intro j hj
   exact mul_le_mul_of_nonneg_left
    (htail j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    (pow_nonneg hB j)
  _ = ∑ j ∈ Finset.range (k + 1), (B * ρ) ^ j := by
   simp_rw [mul_pow]
theorem Zid
  {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (b : Ω → ℕ)
  (B ρ : ℝ) (k : ℕ)
  (hp : ∀ ω, 0 ≤ p ω) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
  (hb : ∀ ω, b ω ≤ k)
  (htail : ∀ j, j ≤ k →
   (∑ ω, if j ≤ b ω then p ω else 0) ≤ ρ ^ j)
  (hsmall : B * ρ < 1) :
  (∑ ω, p ω * B ^ b ω) ≤ 1 / (1 - B * ρ) := by
 apply (ZfM p b B ρ k hp hB hb htail).trans
 simpa using
  (geom_sum_Ico_le_of_lt_one (m := 0) (n := k + 1)
   (mul_nonneg hB hρ) hsmall)
theorem Zhf
   {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (b : Ω → ℕ)
   (B ρ : ℝ) (k : ℕ)
   (hp : ∀ ω, 0 ≤ p ω) (hmass : ∑ ω, p ω = 1)
   (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (hb : ∀ ω, b ω ≤ k)
   (htail : ∀ j, 1 ≤ j → j ≤ k →
    (∑ ω, if j ≤ b ω then p ω else 0) ≤ ρ ^ j)
   (hsmall : B * ρ < 1) :
   (∑ ω, p ω * B ^ b ω) ≤ 1 / (1 - B * ρ) := by
 apply Zid p b B ρ k hp hB hρ hb _ hsmall
 intro j hj
 rcases j with _ | j
 · simp [hmass]
 · exact htail (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) hj
theorem Zhg
  {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (b : Ω → ℕ)
  (B ρ : ℝ) (k : ℕ)
  (hp : ∀ ω, 0 ≤ p ω) (hmass : ∑ ω, p ω = 1)
  (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (hb : ∀ ω, b ω ≤ k)
  (htail : ∀ j, 1 ≤ j → j ≤ k →
   (∑ ω, if j ≤ b ω then p ω else 0) ≤ ρ ^ j)
  (hsmall : B * ρ ≤ 1 / 2) :
  (∑ ω, p ω * B ^ b ω) ≤ 2 := by
 have heta : B * ρ < 1 := lt_of_le_of_lt hsmall (by norm_num)
 apply (Zhf p b B ρ k hp hmass hB hρ hb
  htail heta).trans
 apply (div_le_iff₀ (sub_pos.mpr heta)).mpr
 nlinarith
end Problem355.Znp
end OAI
end
section
namespace OAI
namespace Problem355.ZaT
open scoped BigOperators
def ZaQ {X : Type*} {B k : ℕ}
  (Zao : Fin 3 → Fin 3 → Fin k → X → Fin B)
  (f : Fin 3 → Fin 3 → Fin k → X) (j : ℕ) :
  Matrix (Fin 3) (Fin 3) (ZMod (B ^ j)) :=
 fun a c => ((∑ v : Fin k, (Zao a c v (f a c v)).val * B ^ v.val : ℕ) : ZMod (B ^ j))
theorem Zmt {B k j : ℕ} (hB : B.Prime) (hk : 0 < k) (hj : 0 < j)
   (d : Fin k → Fin B) (hpos : ∀ v, 0 < (d v).val) :
   IsUnit (((∑ v : Fin k, (d v).val * B ^ v.val : ℕ)) : ZMod (B ^ j)) := by
 apply (ZMod.isUnit_natCast_iff_not_dvd_pow hB hj).mpr
 intro hdiv
 have hm := Nat.mod_eq_zero_of_dvd hdiv
 cases k with
 | zero => omega
 | succ k =>
   rw [← ZqZ.Zhe, Nat.ofDigits_mod_eq_head!, List.ofFn_succ] at hm
   have heq : (d 0).val % B = 0 := by simpa using hm
   rw [Nat.mod_eq_of_lt (d 0).isLt] at heq
   exact (Nat.ne_of_gt (hpos 0)) heq
theorem Zeu {X : Type*} [Fintype X] [Nonempty X]
   {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
   (Zao : Fin 3 → Fin 3 → Fin k → X → Fin B)
   (hinj : ∀ a c v, Function.Injective (Zao a c v))
   (hpos : ∀ a c v x, 0 < (Zao a c v x).val)
   (b : (Fin 3 → Fin 3 → Fin k → X) → ℕ) (hb : ∀ f, b f ≤ k)
   (hminor : ∀ j, 1 ≤ j → j ≤ k → ∀ f, j ≤ b f →
    ZiF.Zab (ZaQ Zao f j))
   (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
   (∑ f : Fin 3 → Fin 3 → Fin k → X,
    (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) * (B : ℝ) ^ b f) ≤ 2 := by
 classical
 let A := Fin 3 → Fin 3 → Fin k → X
 have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
 apply Znp.Zhg _ _ _ _ k (by intros; positivity) _
   (by positivity) (by positivity) hb _ hsmall
 · simp [Fintype.card_ne_zero]
 intro j hj hjk
 let bad := Finset.univ.filter (fun f : A => j ≤ b f)
 let T := (Fin 3 → Fin k → X) × (Fin 2 → Fin k → X) × (Fin 2 → Fin 2 → Fin (k-j) → X)
 let keep (f : A) : T := (f 0, fun i => f i.succ 0,
   fun i l v => f i.succ l.succ ⟨j + v.val, by omega⟩)
 have hc := Finset.card_le_card_of_injOn (s := bad) (t := Finset.univ) keep
   (by simp) (by
    intro f hf g hg h
    have row : f 0 = g 0 := congrArg Prod.fst h
    have col (i : Fin 2) : f i.succ 0 = g i.succ 0 := congrArg (fun t : T => t.2.1 i) h
    funext a c v
    refine Fin.cases (congrFun (congrFun row c) v) (fun i => ?_) a
    refine Fin.cases (congrFun (col i) v) (fun l => ?_) c
    by_cases hv : v.val < j
    · let M := fun f : A => ZaQ Zao f j
      have hr (c : Fin 3) : M f 0 c = M g 0 c := by simp only [M, ZaQ, row]
      have hc' : M f i.succ 0 = M g i.succ 0 := by simp only [M, ZaQ, col]
      have hu : IsUnit (M f 0 0) := Zmt hB hk hj _ (fun v => hpos 0 0 v _)
      have eq : M f i.succ l.succ = M g i.succ l.succ := by
       apply hu.mul_left_cancel
       calc
        _ = M f 0 l.succ * M f i.succ 0 := hminor j hj hjk f (Finset.mem_filter.mp hf).2 _ _ _ _
        _ = M g 0 l.succ * M g i.succ 0 := by rw [hr, hc']
        _ = _ := by rw [hr 0]; exact (hminor j hj hjk g (Finset.mem_filter.mp hg).2 _ _ _ _).symm
      apply hinj _ _ _
      apply Fin.ext
      exact ZqZ.ZgE hB.one_lt
       (fun u => (Zao _ _ u (f i.succ l.succ u)).isLt)
       (fun u => (Zao _ _ u (g i.succ l.succ u)).isLt)
       (by simpa only [M, ZaQ, ZMod.val_natCast] using congrArg ZMod.val eq) v hv
    · let w : Fin (k-j) := ⟨v.val-j, by omega⟩
      have hw : (⟨j+w.val, by dsimp [w]; omega⟩ : Fin k) = v := Fin.ext (by dsimp [w]; omega)
      simpa only [keep, hw] using congrArg (fun t : T => t.2.2 i l w) h)
 have count : bad.card ≤ Fintype.card X ^ (5*k + 4*(k-j)) := by
   simp only [Finset.card_univ, T, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ← pow_mul, ← pow_add] at hc
   rwa [show 5*k + 4*(k-j) = k*3 + (k*2 + (k-j)*2*2) by omega]
 rw [← Finset.sum_filter]
 change (∑ _ ∈ bad, (1 / (Fintype.card A : ℝ))) ≤ _
 simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div, A, Fintype.card_fun,
   Fintype.card_fin, Nat.cast_pow, one_div_pow, ← pow_mul]
 apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
 rw [one_mul]
 calc
   _ ≤ ((Fintype.card X : ℝ) ^ (5*k + 4*(k-j))) * (Fintype.card X : ℝ) ^ (4*j) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast count) (by positivity)
   _ = _ := by rw [← pow_add]; congr 1; omega
end Problem355.ZaT
end OAI
end
section
namespace OAI
namespace Problem355.Zai
noncomputable section
open scoped BigOperators
abbrev ZaA (X : Type*) (k : ℕ) := Fin 3 → Fin k → X
abbrev Zat (Λ X : Type*) (k : ℕ) := Λ × ZaA X k
abbrev Array (X : Type*) (k : ℕ) := Fin 3 → Fin 3 → Fin k → X
def Zy (α : Type*) [Fintype α] (_ : α) : ℝ := 1 / Fintype.card α
lemma Zcu (α : Type*) [Fintype α] (a : α) :
 0 ≤ Zy α a := by unfold Zy; positivity
lemma Zfv (α : Type*) [Fintype α] [Nonempty α] :
  ∑ a : α, Zy α a = 1 := by
 have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
 simp only [Zy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
 exact mul_one_div_cancel hcard.ne'
lemma Zmu {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
  (s : ι → α) :
  Zu.Zh (Zy α) s = Zy (ι → α) s := by
 simp [Zu.Zh, Zy]
def ZX {Λ X : Type*} {k : ℕ} :
  (Fin 3 → Zat Λ X k) ≃ ((Fin 3 → Λ) × Array X k) where
 toFun s := (fun c => (s c).1, fun a c v => (s c).2 a v)
 invFun t := fun c => (t.1 c, fun a v => t.2 a c v)
 left_inv s := by funext c; rfl
 right_inv t := by cases t; rfl
theorem Zop {Λ X : Type*} [Fintype Λ] [Fintype X] {k : ℕ}
  (F : (Fin 3 → Λ) → Array X k → ℝ) :
  (∑ s : Fin 3 → Zat Λ X k,
   Zu.Zh (Zy (Zat Λ X k)) s *
    F (ZX s).1 (ZX s).2) =
   ∑ labels : Fin 3 → Λ, Zy (Fin 3 → Λ) labels *
    ∑ f : Array X k, Zy (Array X k) f * F labels f := by
 simp_rw [Zmu]
 have hcard := Fintype.card_congr (ZX (Λ := Λ) (X := X) (k := k))
 have hsum := (ZX (Λ := Λ) (X := X) (k := k)).sum_comp
  (fun t => (1 / (Fintype.card (Fin 3 → Zat Λ X k) : ℝ)) * F t.1 t.2)
 change (∑ s : Fin 3 → Zat Λ X k,
  (1 / (Fintype.card (Fin 3 → Zat Λ X k) : ℝ)) *
   F (ZX s).1 (ZX s).2) = _
 rw [hsum, Fintype.sum_prod_type]
 apply Finset.sum_congr rfl
 intro labels _
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro f _
 rw [hcard]
 simp only [Zy, Fintype.card_prod, Nat.cast_mul, one_div, mul_inv_rev]
 ring
def ZqL {Λ X : Type*} {B k : ℕ}
  (Zao : Λ → Fin 3 → Fin k → X → Fin B)
  (x : Zat Λ X k) : Fin 3 → ZMod (B ^ k) :=
 fun a => ((∑ v : Fin k, (Zao x.1 a v (x.2 a v)).val * B ^ v.val : ℕ) : ZMod (B ^ k))
end
end Problem355.Zai
end OAI
end
section
namespace OAI
namespace Problem355.ZaT
open scoped BigOperators
theorem Zqd {X : Type*} {B k j : ℕ} (hjk : j ≤ k)
  (Zao : Fin 3 → Fin 3 → Fin k → X → Fin B)
  (f : Fin 3 → Fin 3 → Fin k → X) :
  (ZaQ Zao f k).map (ZMod.castHom (Nat.pow_dvd_pow B hjk) (ZMod (B ^ j))) =
   ZaQ Zao f j := by
 ext a c
 simp only [Matrix.map_apply, ZaQ, map_natCast]
theorem ZgF {X : Type*} [Fintype X] [Nonempty X]
  {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
  (Zao : Fin 3 → Fin 3 → Fin k → X → Fin B)
  (hinj : ∀ a c v, Function.Injective (Zao a c v))
  (hpos : ∀ a c v x, 0 < (Zao a c v x).val)
  (b e : (Fin 3 → Fin 3 → Fin k → X) → ℕ)
  (hbe : ∀ f, b f ≤ e f) (hek : ∀ f, e f ≤ k)
  (P Q : (Fin 3 → Fin 3 → Fin k → X) →
   Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
  (hdiag : ∀ f, ZaQ Zao f k =
   (P f : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
    Matrix.diagonal ![1, ((B ^ b f : ℕ) : ZMod (B ^ k)),
     ((B ^ e f : ℕ) : ZMod (B ^ k))] *
   (Q f : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
  (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
  (∑ f : Fin 3 → Fin 3 → Fin k → X,
   (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) * (B : ℝ) ^ b f) ≤ 2 := by
 apply Zeu hB hk Zao hinj hpos b
  (fun f => (hbe f).trans (hek f)) _ hsmall
 intro j hjpos hj f hbf
 have h := (ZiF.Zfe hB (hbe f) hj
  (P f) (Q f) (ZaQ Zao f k) (hdiag f)).mpr hbf
 simpa only [Zqd hj] using h
end Problem355.ZaT
end OAI
end
section
namespace OAI
namespace Problem355.Zj
open scoped BigOperators
noncomputable def ofArray {X : Type*} {B k : ℕ}
  (hB : B.Prime) (hk : 0 < k)
  (Zao : Fin 3 → Fin 3 → Fin k → X → Fin B)
  (hpos : ∀ a c v x, 0 < (Zao a c v x).val)
  (f : Fin 3 → Fin 3 → Fin k → X) :
  Zj B k (ZaT.ZaQ Zao f k) :=
 ofUnit hB (ZaT.Zmt hB hk hk
  (fun v => Zao 0 0 v (f 0 0 v)) (fun v => hpos 0 0 v (f 0 0 v)))
theorem Zeu {X : Type*} [Fintype X] [Nonempty X]
  {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
  (Zao : Fin 3 → Fin 3 → Fin k → X → Fin B)
  (hinj : ∀ a c v, Function.Injective (Zao a c v))
  (hpos : ∀ a c v x, 0 < (Zao a c v x).val)
  (d : ∀ f : Fin 3 → Fin 3 → Fin k → X,
   Zj B k (ZaT.ZaQ Zao f k))
  (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
  (∑ f : Fin 3 → Fin 3 → Fin k → X,
   (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) *
    (B : ℝ) ^ (d f).b) ≤ 2 := by
 exact ZaT.ZgF hB hk Zao hinj hpos
  (fun f => (d f).b) (fun f => (d f).e) (fun f => (d f).b_le_e)
  (fun f => (d f).e_le_k) (fun f => (d f).left) (fun f => (d f).right)
  (fun f => (d f).diagonalization) hsmall
end Problem355.Zj
end OAI
end
section
namespace OAI
noncomputable section
seal Problem355.Zam Problem355.ZaH
namespace Problem355.ZH
open Parameters Zq
open scoped BigOperators
variable {r : ℕ} [Fact r.Prime]
abbrev ZdB (r : ℕ) := Fin (r ^ 9)
abbrev Zat (r : ℕ) [Fact r.Prime] :=
 Zai.Zat (Label r) (ZdB r) Za
abbrev Array (r : ℕ) := Zai.Array (ZdB r) Za
variable (D : Zf Za r)
omit [Fact r.Prime] in
lemma Zqt : r * r ^ 9 < D.B := by
 convert D.Zpe using 1
 ring
private def Zgp {r m : ℕ} [NeZero r] (s : ZMod r) (x : Fin m) : ℕ :=
 r * x.val + (s - 1).val + 1
private lemma Zoq {r m : ℕ} [NeZero r] (s : ZMod r) (x : Fin m) :
  Zgp s x ≤ r * m := calc
 _ ≤ r * x.val + r := by unfold Zgp; have := (s - 1).val_lt; omega
 _ = r * (x.val + 1) := (Nat.mul_succ _ _).symm
 _ ≤ _ := Nat.mul_le_mul_left _ x.isLt
private lemma ZoT {r m : ℕ} [NeZero r] (s : ZMod r) (x : Fin m) :
 (Zgp s x : ZMod r) = s := by simp [Zgp]
def Zao (label : Label r) (a : Fin 3) (v : Fin Za)
  (x : ZdB r) : Fin D.B :=
 ⟨Zgp (Zax.Zej r a v label) x,
  lt_of_le_of_lt (Zoq _ _) (Zqt D)⟩
lemma Zqe (label : Label r) (a : Fin 3) (v : Fin Za) :
  Function.Injective (Zao D label a v) := by
 intro x y h
 apply Fin.ext
 have h' := congrArg Fin.val h
 simp only [Zao, Zgp, Nat.add_right_cancel_iff] at h'
 exact Nat.eq_of_mul_eq_mul_left (NeZero.pos r) h'
lemma Zmv (label : Label r) (a : Fin 3) (v : Fin Za)
 (x : ZdB r) : 0 < (Zao D label a v x).val := Nat.zero_lt_succ _
lemma ZrP (label : Label r) (a : Fin 3) (v : Fin Za)
  (x : ZdB r) : (Zao D label a v x).val ≤ r ^ 10 := by
 simpa only [Zao, pow_succ' r 9] using Zoq (Zax.Zej r a v label) x
lemma ZqM (label : Label r) (a : Fin 3) (v : Fin Za)
  (x : ZdB r) :
  ((Zao D label a v x).val : ZMod r) =
   Zax.Zej r a v label :=
 ZoT _ x
def ZiC (x : Zat r) : Fin 3 → ZMod (D.B ^ Za) :=
 @Zai.ZqL (Label r) (ZdB r) D.B Za (Zao D) x
def Zna (labels : Fin 3 → Label r) :
  Fin 3 → Fin 3 → Fin Za → ZdB r → Fin D.B :=
 fun a c v x => Zao D (labels c) a v x
def matrix (labels : Fin 3 → Label r) (f : Array r) :
  Matrix (Fin 3) (Fin 3) (ZMod (D.B ^ Za)) :=
 @ZaT.ZaQ (ZdB r) D.B Za
  (Zna D labels) f Za
def ZqN (labels : Fin 3 → Label r) (f : Array r) :
  Zj D.B Za (matrix D labels f) :=
 Zj.ofArray (X := ZdB r) (B := D.B) (k := Za)
  D.base_prime Zfb (Zna D labels)
  (fun a c v x => Zmv D (labels c) a v x) f
omit [Fact r.Prime] in
lemma Zpy :
  (D.B : ℝ) * (1 / (Fintype.card (ZdB r) : ℝ)) ^ 4 ≤ 1 / 2 := by
 have hr : (r : ℝ) ≠ 0 := by exact_mod_cast D.r_pos.ne'
 have hid : (r : ℝ) / (r : ℝ) ^ 10 = 1 / (r : ℝ) ^ 9 := by
  field_simp
 simpa only [ZdB, Fintype.card_fin, Nat.cast_pow, hid] using D.ZnV
theorem Zor (labels : Fin 3 → Label r) :
  (∑ f : Array r, Zai.Zy (Array r) f *
   (D.B : ℝ) ^ (ZqN D labels f).b) ≤ 2 := by
 let : NeZero (r ^ 9) := ⟨pow_ne_zero _ D.r_pos.ne'⟩
 exact Zj.Zeu (X := ZdB r) (B := D.B) (k := Za)
  D.base_prime Zfb
  (Zna D labels) (fun a c v => Zqe D (labels c) a v)
  (fun a c v x => Zmv D (labels c) a v x)
  (ZqN D labels) (Zpy D)
end Problem355.ZH
end
end OAI
end
section
namespace OAI
open Finset
noncomputable section
namespace Problem355.ZmA
abbrev ZaA := Fin 3 → ℤ
def ZaX (N : ℕ) (u : ZaA) : Prop :=
 0 ≤ u 0 ∧ u 0 < N ∧ 0 ≤ u 1 ∧ u 1 < N ∧ (N : ℤ) ≤ u 2 ∧ u 2 < 2 * N
def project (u : ZaA) : ℝ × ℝ :=
 ((u 0 : ℝ) / (u 2 : ℝ), (u 1 : ℝ) / (u 2 : ℝ))
theorem ZlI (a b x y : ℕ) (ha : 0 < a) (_hb : 0 < b)
   (hx : x < a) (hxy : a * y = b * x) :
   ∃ k < Nat.gcd a b,
    x = (a / Nat.gcd a b) * k ∧ y = (b / Nat.gcd a b) * k := by
 let g := Nat.gcd a b
 have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
 have hag : g * (a / g) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
 have hbg : g * (b / g) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
 have hap : 0 < a / g := by nlinarith
 have hxy' : (a / g) * y = (b / g) * x := by
   apply Nat.mul_left_cancel hg
   simpa only [← mul_assoc, hag, hbg] using hxy
 have hd : a / g ∣ x :=
   (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_left
    ⟨y, hxy'.symm⟩
 obtain ⟨k, hk⟩ := hd
 refine ⟨k, ?_, hk, ?_⟩
 · nlinarith
 · apply Nat.mul_left_cancel hap
   rw [hxy', hk]
   ring
private def ray (x y d k : ℕ) : ZaA := ![↑(k*x), ↑(k*y), ↑(k*d)]
private def Zrt (M : ℕ) := (Ioc 0 M).sigma fun d =>
 (range d ×ˢ range d) ×ˢ (Ioc 0 (M/d) ×ˢ Ioc 0 (M/d))
private def decode (p : Σ _ : ℕ, (ℕ × ℕ) × (ℕ × ℕ)) : ZaA × ZaA :=
 (ray p.2.1.1 p.2.1.2 p.1 p.2.2.1, ray p.2.1.1 p.2.1.2 p.1 p.2.2.2)
private lemma ZrI (M : ℕ) : (Zrt M).card ≤ M^3 := by
 simp only [Zrt, card_sigma, card_product, card_range, Nat.card_Ioc, Nat.sub_zero]
 calc
  _ ≤ ∑ _d ∈ Ioc 0 M, M^2 := sum_le_sum fun d _ => by
   calc
    _ = (d * (M / d))^2 := by ring
    _ ≤ _ := Nat.pow_le_pow_left (Nat.mul_div_le M d) 2
  _ = _ := by simp [pow_succ, mul_comm]
theorem Zhh (N : ℕ) (hN : 0 < N)
    (U V : Finset ZaA) (hU : ∀ u ∈ U, ZaX N u) (hV : ∀ v ∈ V, ZaX N v) :
    ((U ×ˢ V).filter fun p => project p.1 = project p.2).card ≤ 8 * N ^ 3 := by
  classical
  suffices H : ((U ×ˢ V).filter fun p => project p.1 = project p.2) ⊆
      (Zrt (2*N)).image decode by
    exact (card_le_card H).trans ((card_image_le.trans (ZrI _)).trans (le_of_eq (by ring)))
  rintro ⟨u,v⟩ hp
  obtain ⟨huv, he⟩ := mem_filter.mp hp
  obtain ⟨hu,hv⟩ := mem_product.mp huv
  obtain ⟨ux,hx,uy,hy,uz,hz⟩ := hU u hu
  obtain ⟨vx,ix,vy,iy,vz,iz⟩ := hV v hv
  let a := (u 2).toNat
  let b := (v 2).toNat
  let d := a.gcd b
  have ha : 0 < a := by dsimp [a]; omega
  have hb : 0 < b := by dsimp [b]; omega
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ ha
  have ha' : a / d * d = a := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have hb' : b / d * d = b := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have param (i : Fin 3) (hi : u i < u 2) (ui : 0 ≤ u i) (vi : 0 ≤ v i)
      (heq : (u i : ℝ) / u 2 = (v i : ℝ) / v 2) :
      ∃ k < d, (u i).toNat = a/d*k ∧ (v i).toNat = b/d*k := by
    have hu2 : (u 2 : ℝ) ≠ 0 := by exact_mod_cast (show u 2 ≠ 0 by omega)
    have hv2 : (v 2 : ℝ) ≠ 0 := by exact_mod_cast (show v 2 ≠ 0 by omega)
    have h := (div_eq_div_iff hu2 hv2).mp heq
    norm_cast at h
    apply ZlI a b _ _ ha hb (by dsimp [a]; omega)
    apply Int.ofNat_inj.mp
    push_cast
    simp only [a,b, Int.toNat_of_nonneg ui, Int.toNat_of_nonneg vi,
      Int.toNat_of_nonneg (show 0 ≤ u 2 by omega), Int.toNat_of_nonneg (show 0 ≤ v 2 by omega)]
    linarith [h]
  obtain ⟨x,xd,hux,hvx⟩ := param 0 (by omega) ux vx (congrArg Prod.fst he)
  obtain ⟨y,yd,huy,hvy⟩ := param 1 (by omega) uy vy (congrArg Prod.snd he)
  have aM : a ≤ 2*N := by dsimp [a]; omega
  have bM : b ≤ 2*N := by dsimp [b]; omega
  refine mem_image.mpr ⟨⟨d,(x,y),a/d,b/d⟩, ?_, ?_⟩
  · simp only [Zrt, mem_sigma, mem_Ioc, mem_product, mem_range]
    exact ⟨⟨hd,(Nat.gcd_le_left b ha).trans aM⟩, ⟨xd,yd⟩,
      ⟨by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at ha'; omega,
       Nat.div_le_div_right aM⟩, ⟨by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hb'; omega,
       Nat.div_le_div_right bM⟩⟩
  · have uc : 0 ≤ u 2 := by omega
    have vc : 0 ≤ v 2 := by omega
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      first | exact (congrArg Nat.cast hux.symm).trans (Int.toNat_of_nonneg ux)
            | exact (congrArg Nat.cast huy.symm).trans (Int.toNat_of_nonneg uy)
            | exact (congrArg Nat.cast ha').trans (Int.toNat_of_nonneg uc)
            | exact (congrArg Nat.cast hvx.symm).trans (Int.toNat_of_nonneg vx)
            | exact (congrArg Nat.cast hvy.symm).trans (Int.toNat_of_nonneg vy)
            | exact (congrArg Nat.cast hb').trans (Int.toNat_of_nonneg vc)
def Zm (N : ℕ) : Fin 3 → ℤ := ![0, 0, (N : ℤ)]
end Problem355.ZmA
end
end OAI
end
section
namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem355.Zcv
open ZmA
theorem Zku {X A B : Type*}
   (f : X → A) (g : X → B) (a : A) (V : Finset B)
   (s L : ℕ) (hs : 0 < s) (x : X) :
   Zb.Zaf f g a V s L x ≤ 1 / (L : ℝ) ^ 3 := by
 classical
 unfold Zb.Zaf
 split_ifs
 · have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
   by_cases hL : L = 0
   · simp [hL]
   · apply one_div_le_one_div_of_le (by positivity)
     nlinarith [pow_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L) 3]
 · positivity
theorem Zqf {I X : Type*} [Fintype I]
  (w : I → ℝ) (p : I → X → ℝ) (C : ℝ)
  (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
  (hp : ∀ i x, p i x ≤ C) (x : X) :
  (∑ i, w i * p i x) ≤ C := by
 calc
  (∑ i, w i * p i x) ≤ ∑ i, w i * C :=
   Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hp i x) (hw0 i))
  _ = C := by rw [← Finset.sum_mul, hw, one_mul]
def Zgq {N : ℕ} (x : Zc.Box N 3 (Zc.Zm N)) :
 ZaA := fun i => (x i).val
theorem ZhF (N : ℕ) :
  Function.Injective (@Zgq N) := by
 intro x y h
 funext i
 exact Subtype.ext (congrFun h i)
theorem Zqg {N : ℕ}
  (x : Zc.Box N 3 (Zc.Zm N)) :
  ZaX N (Zgq x) := by
 have hx := (x 0).property
 have hy := (x 1).property
 have hz : (N : ℤ) ≤ (x 2).val ∧ (x 2).val < (N : ℤ) + N := (x 2).property
 simp [Zc.Zm] at hx hy
 change 0 ≤ (x 0).val ∧ (x 0).val < N ∧ 0 ≤ (x 1).val ∧ (x 1).val < N ∧
  (N : ℤ) ≤ (x 2).val ∧ (x 2).val < 2 * N
 omega
@[simp] theorem ZrK {N : ℕ}
 (x : Zc.Box N 3 (Zc.Zm N)) :
 project (Zgq x) = Zc.project x := rfl
theorem ZkU (N Q L : ℕ)
  (hQ : 0 < Q) (hL : 0 < L) (hN : N = Q * L)
  (p : Zc.Box N 3 (Zc.Zm N) → ℝ)
  (hp0 : ∀ x, 0 ≤ p x) (hp : ∀ x, p x ≤ 1 / (L : ℝ) ^ 3) :
  (∑ x : Fin 2 → Zc.Box N 3 (Zc.Zm N),
    (∏ i, p (x i)) *
     (if Zc.project (x 0) = Zc.project (x 1) then 1 else 0)) ≤
    8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
 classical
 let U := Finset.univ.image (@Zgq N)
 let X := Zc.Box N 3 (Zc.Zm N)
 let S := Finset.univ.filter (fun x : Fin 2 → X => Zc.project (x 0) = Zc.project (x 1))
 let T := (U ×ˢ U).filter (fun u => project u.1 = project u.2)
 let F (x : Fin 2 → X) := (Zgq (x 0), Zgq (x 1))
 have hU : ∀ u ∈ U, ZaX N u := by simpa [U] using @Zqg N
 have hf : Set.MapsTo F ↑S ↑T := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
    Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, (Finset.mem_filter.mp hx).2⟩
 have hi : Function.Injective F := by
  intro x y h
  funext i
  fin_cases i
  · exact ZhF N (congrArg Prod.fst h)
  · exact ZhF N (congrArg Prod.snd h)
 have hcount : (S.card : ℝ) ≤ 8 * (N : ℝ)^3 := by
  exact_mod_cast (Finset.card_le_card_of_injOn F hf hi.injOn).trans
    (Zhh N (by rw [hN]; positivity) U U hU hU)
 simp only [Fin.prod_univ_two, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
 calc
  _ ≤ ∑ _ ∈ S, (1 / (L : ℝ)^3) * (1 / (L : ℝ)^3) := Finset.sum_le_sum fun x _ =>
    mul_le_mul (hp _) (hp _) (hp0 _) (by positivity)
  _ ≤ (8 * (N : ℝ)^3) * ((1 / (L : ℝ)^3) * (1 / (L : ℝ)^3)) := by
    simpa using mul_le_mul_of_nonneg_right hcount (show 0 ≤ (1 / (L : ℝ)^3) * (1 / (L : ℝ)^3) by positivity)
  _ = _ := by rw [hN]; push_cast; field_simp
end Problem355.Zcv
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zcv
theorem ZnP {Θ X : Type*} [Fintype Θ] [Fintype X]
  (rho : Θ → ℝ) (mu : Θ → X → ℝ) (point : Θ → X → Point) :
  ZV.Zgb rho mu point =
   ∑ θ, rho θ * ∑ x : Fin 2 → X, (∏ i, mu θ (x i)) *
    (if point θ (x 0) = point θ (x 1) then 1 else 0) := by
 classical
 simp [ZV.Zgb, Fintype.sum_prod_type, Zu.Zak,
  Zu.Zh, Finset.mul_sum, mul_ite]
theorem ZlJ {Θ : Type*} [Fintype Θ]
  (N Q L : ℕ) (hQ : 0 < Q) (hL : 0 < L) (hN : N = Q * L)
  (rho : Θ → ℝ)
  (mu : Θ → Zc.Box N 3 (Zc.Zm N) → ℝ)
  (hrho0 : ∀ θ, 0 ≤ rho θ) (hrho : ∑ θ, rho θ = 1)
  (hmu0 : ∀ θ x, 0 ≤ mu θ x)
  (hmu : ∀ θ x, mu θ x ≤ 1 / (L : ℝ) ^ 3) :
  ZV.Zgb rho mu (fun _ => Zc.project) ≤
   8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
 rw [ZnP]
 calc
  _ ≤ ∑ θ, rho θ * (8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3) := by
   apply Finset.sum_le_sum
   intro θ hθ
   apply mul_le_mul_of_nonneg_left _ (hrho0 θ)
   exact ZkU N Q L hQ hL hN (mu θ) (hmu0 θ) (hmu θ)
  _ = _ := by rw [← Finset.sum_mul, hrho, one_mul]
theorem ZeW {Θ I : Type*}
   [Fintype Θ] [Fintype I]
   (h q L : ℕ) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L)
   (rho : Θ → ℝ) (hrho0 : ∀ θ, 0 ≤ rho θ) (hrho : ∑ θ, rho θ = 1)
   (w : Θ → I → ℝ) (hw0 : ∀ θ i, 0 ≤ w θ i) (hw : ∀ θ, ∑ i, w θ i = 1)
   (a : Θ → I → Fin 3 → ZMod h)
   (V : Θ → I → Finset (Fin 3 → ZMod q))
   (s : Θ → I → ℕ) (hs : ∀ θ i, 0 < s θ i) :
   ZV.Zgb rho
    (fun θ x => ∑ i, w θ i * Zc.ZeJ h q L
     (Zc.Zm (L * (h * q))) (a θ i) (V θ i) (s θ i) x)
    (fun _ => Zc.project) ≤
    8 * ((h * q : ℕ) : ℝ) ^ 6 / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
 apply ZlJ _ (h * q) L (Nat.mul_pos hh hq) hL
   (Nat.mul_comm _ _) rho _ hrho0 hrho
 · intro θ x
   exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 θ i)
    (Zc.ZjV h q L _ (a θ i) (V θ i) (s θ i) x))
 · intro θ
   apply Zqf (w θ) _ _ (hw0 θ) (hw θ)
   intro i x
   exact Zku _ _ (a θ i) (V θ i) (s θ i) L (hs θ i) x
end Problem355.Zcv
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zas
open Zc Zu ZaD
theorem Zie {Θ D : Type} [Fintype Θ] [Fintype D]
  (h q L s : ℕ) [NeZero h] [NeZero q]
  (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
  (rho : Θ → ℝ) (p : D → ℝ)
  (a : Θ → D → Fin 3 → ZMod h)
  (V : Θ → Finset (Fin 3 → ZMod q))
  (hrho : ∀ θ, 0 ≤ rho θ) (hsum : ∑ θ, rho θ = 1)
  (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
  (hV : ∀ θ, (V θ).card = s) :
  (ZnW h q L s hc hL hs rho p a V hrho hsum hp hpsum hV).ZbB ≤
   8 * ((h * q : ℕ) : ℝ) ^ 6 / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
 exact Zcv.ZeW
  h q L (NeZero.pos h) (NeZero.pos q) hL rho hrho hsum
  (fun _ => p) (fun _ => hp) (fun _ => hpsum) a (fun θ _ => V θ)
  (fun _ _ => s) (fun _ _ => hs)
theorem Zfw {Ω D : Type}
  [Fintype Ω] [Fintype D]
  (h q L s : ℕ) [NeZero h] [NeZero q]
  (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
  (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
  (V : Ω → Finset (Fin 3 → ZMod q))
  (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
  (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
  (hV : ∀ ω, (V ω).card = s) :
  (ZaB h q L s hc hL hs w p c V hw hwsum hp hpsum hV).ZbB ≤
   8 * ((h * q : ℕ) : ℝ) ^ 6 / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
 unfold ZaB Zcs
 apply Zie
end Problem355.Zas
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Parameters.Zf
variable {k r : ℕ} (D : Zf k r)
def ZbS : ℕ := D.M ^ 9
lemma ZdU : 0 < D.ZbS :=
 pow_pos D.M_pos _
lemma ZdK :
  D.ZbS * (D.h * D.q) = D.N := by
 change D.M ^ 9 * D.M = D.M ^ 10
 exact (pow_succ D.M 9).symm
lemma h_pos : 0 < D.h := lt_of_lt_of_le (by norm_num : 0 < 3) D.ZpF
end Problem355.Parameters.Zf
namespace Problem355.Zev
open Parameters Parameters.Zf ZaD
variable {k r : ℕ}
def ZdV (D : Zf k r)
  {Ω Δ : Type} [Fintype Ω] [Fintype Δ]
  (s : ℕ) (hs : 0 < s)
  (w : Ω → ℝ) (p : Δ → ℝ)
  (c : Δ → Fin 3 → ZMod D.h)
  (V : Ω → Finset (Fin 3 → ZMod D.q))
  (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
  (hp : ∀ δ, 0 ≤ p δ) (hpsum : ∑ δ, p δ = 1)
  (hV : ∀ ω, (V ω).card = s) : ZaY := by
 letI : NeZero D.h := ⟨ne_of_gt D.h_pos⟩
 letI : NeZero D.q := ⟨D.auxiliary_prime.ne_zero⟩
 exact Zas.ZaB D.h D.q D.ZbS s
  D.coprime D.ZdU hs w p c V hw hwsum hp hpsum hV
theorem ZeX (D : Zf k r)
  {Ω Δ : Type} [Fintype Ω] [Fintype Δ]
  (s : ℕ) (hs : 0 < s)
  (w : Ω → ℝ) (p : Δ → ℝ)
  (c : Δ → Fin 3 → ZMod D.h)
  (V : Ω → Finset (Fin 3 → ZMod D.q))
  (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
  (hp : ∀ δ, 0 ≤ p δ) (hpsum : ∑ δ, p δ = 1)
  (hV : ∀ ω, (V ω).card = s) :
  (ZdV D s hs w p c V hw hwsum hp hpsum hV).ZbB ≤
   8 * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 := by
 let : NeZero D.h := ⟨ne_of_gt D.h_pos⟩
 let : NeZero D.q := ⟨D.auxiliary_prime.ne_zero⟩
 have hpair := Zas.Zfw
  D.h D.q D.ZbS s D.coprime D.ZdU hs
  w p c V hw hwsum hp hpsum hV
 simpa only [ZdV, D.ZdK, M] using hpair
end Problem355.Zev
end
end OAI
end
section
namespace OAI
noncomputable section
seal Problem355.Zam Problem355.ZaH
namespace Problem355.Zbd
open Parameters Zq
section WithAuxiliary
variable {r : ℕ} [Fact r.Prime] [Fintype (Label r)]
def Zek (D : Zf Za r)
  [Fact D.q.Prime] (A : ZJ.Law D.q (D.h ^ 2)) :
  ZaD.ZaY := by
 letI : NeZero (r ^ 9) := ⟨pow_ne_zero _ D.r_pos.ne'⟩
 exact Zev.ZdV D A.size A.size_pos A.weight
  (Zai.Zy (ZH.Zat r))
  (ZH.ZiC D) A.sets A.weight_nonneg A.weight_sum
  (Zai.Zcu _) (Zai.Zfv _)
  A.sets_card
theorem Zgh
  (D : Zf Za r)
  [Fact D.q.Prime] (A : ZJ.Law D.q (D.h ^ 2)) :
  (Zek D A).ZbB ≤
   8 * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 := by
 unfold Zek
 apply Zev.ZeX
end WithAuxiliary
variable {r : ℕ} [Fact r.Prime]
def ZdV (D : Zf Za r) : ZaD.ZaY := by
 letI : Fintype (Label r) := Fintype.ofFinite (Label r)
 letI : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
 have hH : 1 ≤ D.h ^ 2 := Nat.one_le_pow _ _ D.h_pos
 exact Zek D (Classical.choice
  (ZJ.ZqV hH D.auxiliary_large))
theorem ZeX (D : Zf Za r) :
  (ZdV D).ZbB ≤ 8 * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 := by
 let : Fintype (Label r) := Fintype.ofFinite (Label r)
 let : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
 unfold ZdV
 apply Zgh
end Problem355.Zbd
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zhn
open Zq Parameters
def Zbn {k : ℕ} (d : Fin k → ℕ) (v : ℕ) : ℤ :=
 if hv : v < k then d ⟨v, hv⟩ else 0
lemma Zqh {k : ℕ} (d : Fin k → ℕ) (v : Fin k) :
  Zbn d v.val = (d v : ℤ) := by
 simp only [Zbn, dif_pos v.isLt]
lemma Zpz {B k : ℕ} (d : Fin k → ℕ) :
  (∑ v ∈ Finset.range k, Zbn d v * (B : ℤ) ^ v) =
   ((∑ v : Fin k, d v * B ^ v.val : ℕ) : ℤ) := by
 rw [← Fin.sum_univ_eq_sum_range]
 simp only [Zqh, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
theorem Zel
   {r : ℕ} [Fact r.Prime] (hr : 6 < r)
   (D : Zf Za r)
   (h : ℕ) (hh : h = D.h)
   (labels : Fin 3 → Label r)
   (d : Fin 3 → Fin 3 → Fin Za → ℕ)
   (hd : ∀ i j v, d i j v ≤ r ^ 10)
   (hresidue : ∀ i j v, (d i j v : ZMod r) =
    Zax.Zej r i v (labels j))
   (A : Matrix (Fin 3) (Fin 3) ℤ)
   (G : Matrix.SpecialLinearGroup (Fin 3) (ZMod h))
   (hAC : A.map (Int.castRingHom (ZMod h)) =
    G.val * (Matrix.of (fun i j =>
     ((∑ v : Fin Za, d i j v * D.B ^ v.val : ℕ) : ZMod h)) :
      Matrix (Fin 3) (Fin 3) (ZMod h)))
   (hsmall : |A.det| ≤ (D.tau : ℤ)) :
   ∃ i j : Fin 3, i ≠ j ∧ labels i = labels j := by
 let ds : Fin 3 → Fin 3 → ℕ → ℤ := fun i j => Zbn (d i j)
 refine Zax.ZaK r hr D.B
   (r ^ 10 : ℕ) (by have := D.ZdY; omega) (by positivity)
   (by exact_mod_cast D.Znx) labels ds ?_ ?_ A h hh G ?_ ?_
 · intro i j v hv
   change |Zbn (d i j) v| ≤ ((r ^ 10 : ℕ) : ℤ)
   rw [show Zbn (d i j) v = (d i j ⟨v, hv⟩ : ℤ) by
    simp only [Zbn, dif_pos hv]]
   rw [abs_of_nonneg (Int.natCast_nonneg _)]
   exact_mod_cast hd i j ⟨v, hv⟩
 · intro i j v hv
   change ((Zbn (d i j) v : ℤ) : ZMod r) = _
   simpa only [Zbn, dif_pos hv, Int.cast_natCast,
    Zax.Zej] using hresidue i j ⟨v, hv⟩
 · have hmatrix :
     Matrix.map (fun i j => ∑ v ∈ Finset.range Za,
      ds i j v * (D.B : ℤ) ^ v) (Int.castRingHom (ZMod h)) =
      Matrix.of (fun i j =>
       ((∑ v : Fin Za, d i j v * D.B ^ v.val : ℕ) : ZMod h)) := by
    ext i j
    change (((∑ v ∈ Finset.range Za,
     Zbn (d i j) v * (D.B : ℤ) ^ v) : ℤ) : ZMod h) = _
    rw [Zpz]
    simp only [Int.cast_natCast, Matrix.of_apply]
   rw [hmatrix]
   exact hAC
 · simpa only [Zf.tau, threshold, Int.natCast_div,
    Nat.cast_pow, Nat.cast_ofNat] using hsmall
end Problem355.Zhn
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.ZbG
open ZD
def Zcm (h : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ) :
 Fin 3 → Fin 3 → ZMod h := fun j i => (A i j : ZMod h)
lemma ZfN (h : ℕ) [NeZero h]
  (C : Fin 3 → Fin 3 → ZMod h) (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hA : Zcm h A ∈ Zt (Zz h) C) :
  ∃ G : Zz h, A.map (Int.castRingHom (ZMod h)) =
   G.val * Matrix.transpose C := by
 obtain ⟨G, hG⟩ := (Zcc C _).mp hA
 refine ⟨G, ?_⟩
 change Matrix.transpose (Zcm h A) = G.val * Matrix.transpose C
 rw [← hG, ZbN]
def Zif (h B : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ) :
  Fin 3 → Fin 3 → ZMod h :=
 fun j i => ((∑ v ∈ Finset.range Za, d i j v * (B : ℤ) ^ v : ℤ) : ZMod h)
variable (p : ℕ) [Fact p.Prime]
theorem ZcZ (hp : 6 < p)
  (B : ℕ) (L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
  (hbase : 100 * (Za : ℤ) ^ 2 * L ^ 3 < B)
  (labels : Fin 3 → Zq.Label p)
  (d : Fin 3 → Fin 3 → ℕ → ℤ)
  (hd : ∀ i j v, v < Za → |d i j v| ≤ L)
  (hresidue : ∀ i j v, v < Za →
   (Int.castRingHom (ZMod p)) (d i j v) =
    Zax.Zdm p i v (labels j))
  (h : ℕ) [NeZero h] (hh : h = B ^ Za)
  (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hA : Zcm h A ∈ Zt (Zz h) (Zif h B d))
  (hsmall : |A.det| ≤ (B : ℤ) ^ (Za - 1) / 2) :
  ∃ i j : Fin 3, i ≠ j ∧ labels i = labels j := by
 obtain ⟨G, hG⟩ := ZfN h (Zif h B d) A hA
 exact Zax.ZaK p hp B L hB hL hbase
  labels d hd hresidue A h hh G hG hsmall
theorem ZbF (hp : 6 < p)
  (B : ℕ) (L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
  (hbase : 100 * (Za : ℤ) ^ 2 * L ^ 3 < B)
  (labels : Fin 3 → Zq.Label p) (hinj : Function.Injective labels)
  (d : Fin 3 → Fin 3 → ℕ → ℤ)
  (hd : ∀ i j v, v < Za → |d i j v| ≤ L)
  (hresidue : ∀ i j v, v < Za →
   (Int.castRingHom (ZMod p)) (d i j v) =
    Zax.Zdm p i v (labels j))
  (h : ℕ) [NeZero h] (hh : h = B ^ Za)
  (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hA : Zcm h A ∈ Zt (Zz h) (Zif h B d)) :
  (B : ℤ) ^ (Za - 1) / 2 < |A.det| := by
 by_contra hn
 obtain ⟨i, j, hij, heq⟩ := ZcZ p hp
  B L hB hL hbase labels d hd hresidue h hh A hA (le_of_not_gt hn)
 exact hij (hinj heq)
end Problem355.ZbG
end
end OAI
end
section
namespace OAI
noncomputable section
seal Problem355.Zam Problem355.ZaH
namespace Problem355.ZeD
open Parameters Zq ZH ZD
noncomputable local instance zCPD14 (p : Prop) : Decidable p := Classical.propDecidable p
variable {r : ℕ} [Fact r.Prime]
variable (D : Zf Za r)
def Zcd (h : ℕ) (labels : Fin 3 → Label r) (f : ZH.Array r) :
  Fin 3 → Fin 3 → ZMod h :=
 fun j i => ((∑ v : Fin Za,
  (Zao D (labels j) i v (f i j v)).val * D.B ^ v.val : ℕ) : ZMod h)
theorem ZaK (hr : 6 < r)
  (h : ℕ) [NeZero h] (hh : h = D.h)
  (labels : Fin 3 → Label r) (f : ZH.Array r)
  (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hA : ZbG.Zcm h A ∈
   Zt (Zz h) (Zcd D h labels f))
  (hsmall : |A.det| ≤ (D.tau : ℤ)) :
  ∃ i j : Fin 3, i ≠ j ∧ labels i = labels j := by
 obtain ⟨G, hG⟩ := ZbG.ZfN h
  (Zcd D h labels f) A hA
 exact Zhn.Zel hr D h hh labels
  (fun i j v => (Zao D (labels j) i v (f i j v)).val)
  (fun i j v => ZrP D (labels j) i v (f i j v))
  (fun i j v => ZqM D (labels j) i v (f i j v)) A G hG hsmall
theorem ZbF (hr : 6 < r)
  (h : ℕ) [NeZero h] (hh : h = D.h)
  (labels : Fin 3 → Label r) (hinj : Function.Injective labels)
  (f : ZH.Array r) (A : Matrix (Fin 3) (Fin 3) ℤ)
  (hA : ZbG.Zcm h A ∈
   Zt (Zz h) (Zcd D h labels f)) :
  (D.tau : ℤ) < |A.det| := by
 by_contra hn
 obtain ⟨i, j, hij, heq⟩ := ZaK D hr h hh labels f A hA
  (le_of_not_gt hn)
 exact hij (hinj heq)
theorem Zci
  {X Ω Y : Type*} [DecidableEq X] [Fintype Ω]
  (hr : 6 < r) (h : ℕ) [NeZero h] (hh : h = D.h)
  (labels : Fin 3 → Label r) (hinj : Function.Injective labels)
  (f : ZH.Array r)
  (A : X → Matrix (Fin 3) (Fin 3) ℤ) (g : X → Fin 3 → Y)
  (w : Ω → ℝ) (V : Ω → Finset Y) (s M : ℕ) (S : Finset X) :
  (∑ x ∈ S.filter (fun x => |(A x).det| ≤ (D.tau : ℤ)),
   Zb.ZaI
    (fun x => ZbG.Zcm h (A x)) g
    (Zt (Zz h) (Zcd D h labels f)) w V s M x) = 0 := by
 apply Zb.Zci
 intro x _ hx
 exact ZbF D hr h hh labels hinj f (A x) hx
end Problem355.ZeD
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zgs
open scoped BigOperators
open Zai
def ZrQ (Λ : Type*) : (Fin 3 → Λ) ≃ Λ × Λ × Λ where
 toFun l := (l 0, l 1, l 2)
 invFun t := ![t.1, t.2.1, t.2.2]
 left_inv l := by funext i; fin_cases i <;> rfl
 right_inv t := rfl
lemma ZpA {Λ : Type*} {a b c : Λ}
  (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
  Function.Injective (![a, b, c] : Fin 3 → Λ) := by
 intro i j hij
 fin_cases i <;> fin_cases j <;> simp_all
end Problem355.Zgs
namespace Problem355.Zai
open scoped BigOperators
def ZoX (Λ : Type*) : (Fin 3 → Λ) ≃ Λ × Λ × Λ where
 toFun l := (l 0, l 1, l 2)
 invFun t := ![t.1, t.2.1, t.2.2]
 left_inv l := by funext i; fin_cases i <;> rfl
 right_inv t := rfl
theorem ZfO
  {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]
  (F : (Fin 3 → Λ) → ℝ) (M : ℝ) (hM : 0 ≤ M)
  (hbound : ∀ l, F l ≤ M)
  (hzero : ∀ l, l 0 ≠ l 1 → l 0 ≠ l 2 → l 1 ≠ l 2 → F l = 0) :
  (∑ l : Fin 3 → Λ, Zy (Fin 3 → Λ) l * F l) ≤
   3 * M / (Fintype.card Λ : ℝ) := by
 have h := Zkw.ZiK
  (fun a b c => F ![a, b, c]) M hM
  (fun a b c => hbound _) (fun a b c hab hac hbc => hzero _ hab hac hbc)
 have hs : (∑ l : Fin 3 → Λ, F l) = ∑ a, ∑ b, ∑ c, F ![a, b, c] := by
  calc
   _ = ∑ t : Λ × Λ × Λ, F ((ZoX Λ).symm t) :=
    (ZoX Λ).symm.sum_comp F |>.symm
   _ = _ := by simp only [Fintype.sum_prod_type]; rfl
 have he : (∑ l : Fin 3 → Λ, Zy (Fin 3 → Λ) l * F l) =
   (∑ l : Fin 3 → Λ, F l) / (Fintype.card Λ : ℝ) ^ 3 := by
  unfold Zy
  rw [← Finset.mul_sum]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  ring
 rw [he, hs]
 exact h
theorem ZfP
  {Λ X : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] [Fintype X] {k : ℕ}
  (F : (Fin 3 → Λ) → Array X k → ℝ) (M : ℝ) (hM : 0 ≤ M)
  (hbound : ∀ l, (∑ f : Array X k, Zy (Array X k) f * F l f) ≤ M)
  (hzero : ∀ l f, l 0 ≠ l 1 → l 0 ≠ l 2 → l 1 ≠ l 2 → F l f = 0) :
  (∑ s : Fin 3 → Zat Λ X k,
   Zu.Zh (Zy (Zat Λ X k)) s *
    F (ZX s).1 (ZX s).2) ≤
   3 * M / (Fintype.card Λ : ℝ) := by
 rw [Zop]
 apply ZfO _ M hM hbound
 intro l hab hac hbc
 simp only [hzero l _ hab hac hbc, mul_zero, Finset.sum_const_zero]
theorem ZjR
  {Λ X : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] [Fintype X] {k : ℕ}
  (D : (Fin 3 → Λ) → Array X k → ℝ)
  (p : (Fin 3 → Zat Λ X k) → ℝ) (A : ℝ) (hA : 0 ≤ A)
  (hmoment : ∀ l, (∑ f : Array X k, Zy (Array X k) f * D l f) ≤ 2)
  (hbound : ∀ l f, p (ZX.symm (l, f)) ≤ A * D l f)
  (hzero : ∀ s, (s 0).1 ≠ (s 1).1 → (s 0).1 ≠ (s 2).1 →
   (s 1).1 ≠ (s 2).1 → p s = 0) :
  (∑ s : Fin 3 → Zat Λ X k,
   Zu.Zh (Zy (Zat Λ X k)) s * p s) ≤
   6 * A / (Fintype.card Λ : ℝ) := by
 have h := ZfP
  (fun l f => p (ZX.symm (l, f))) (A * 2) (by positivity)
  (by
   intro l
   calc
    _ ≤ ∑ f : Array X k, Zy (Array X k) f * (A * D l f) :=
     Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left
      (hbound l f) (Zcu _ f)
    _ = A * ∑ f : Array X k, Zy (Array X k) f * D l f := by
     rw [Finset.mul_sum]
     apply Finset.sum_congr rfl
     intro f _
     ring
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left (hmoment l) hA)
  (by intro l f hab hac hbc; exact hzero _ hab hac hbc)
 simpa only [Prod.mk.eta, Equiv.symm_apply_apply,
  show 3 * (A * 2) = 6 * A by ring] using h
end Problem355.Zai
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zbw
open ZD Zc Zb
def ZnQ (h : ℕ) (C : Fin 3 → Fin 3 → ZMod h) :
  MulAction.orbit (Zz h) C ≃ ZS.Zbl (Matrix.transpose C) where
 toFun A := ⟨Matrix.transpose A.val, by
  obtain ⟨G, hG⟩ := A.property
  exact ⟨G, by rw [← hG, ZbN]⟩⟩
 invFun A := ⟨Matrix.transpose A.val, by
  obtain ⟨G, hG⟩ := A.property
  refine ⟨G, ?_⟩
  have ht := (ZbN h G C).trans hG
  exact funext fun i => funext fun j => congrFun (congrFun ht j) i⟩
 left_inv A := by apply Subtype.ext; exact Matrix.transpose_transpose _
 right_inv A := by apply Subtype.ext; exact Matrix.transpose_transpose _
theorem ZnR (h : ℕ) [NeZero h]
  (C : Fin 3 → Fin 3 → ZMod h) :
  (Zt (Zz h) C).card =
   Nat.card (ZS.Zbl (Matrix.transpose C)) := by
 rw [ZjW]
 exact Nat.card_congr (ZnQ h C)
theorem Zjj {p k : ℕ} [NeZero (p ^ k)]
  (hp : p.Prime) (hk : 0 < k)
  (C : Fin 3 → Fin 3 → ZMod (p ^ k))
  (d : Zj p k (Matrix.transpose C)) :
  (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 8 /
   (((p ^ d.b : ℕ) : ℝ) ^ 3 * ((p ^ d.e : ℕ) : ℝ) ^ 2) ≤
    ((Zt (Zz (p ^ k)) C).card : ℝ) := by
 let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
 rw [ZnR]
 exact d.ZoK hp hk
theorem Znb (h q L : ℕ) [NeZero h]
  (shift : Fin 3 → ℤ) (C : Fin 3 → Fin 3 → ZMod h)
  (x : Fin 3 → Box (L * (h * q)) 3 shift)
  (hx : (fun i => residue h (x i)) ∈ Zt (Zz h) C) :
  ((Zg x).det : ZMod h) = (Matrix.transpose C).det := by
 obtain ⟨G, hG⟩ := ZeE h q L shift C x hx
 apply ZeB.ZeL h (Matrix.transpose C)
  (Zg x)
 exact ⟨G, hG.symm⟩
theorem ZjS {Ω : Type*} [Fintype Ω]
  {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
  (q L s : ℕ) (hq : 0 < q) (hL : 0 < L) (hs : 0 < s)
  (shift : Fin 3 → ℤ) (C : Fin 3 → Fin 3 → ZMod (p ^ k))
  (d : Zj p k (Matrix.transpose C))
  (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
  (hw : ∀ ω, 0 ≤ w ω)
  (S : Finset (Fin 3 → Box (L * (p ^ k * q)) 3 shift))
  {τ : ℤ} (hwidth : 2 * τ < (p ^ k : ℕ))
  {K R : ℝ} (hK : 0 ≤ K)
  (hcount : ∀ t : ℤ, |t| ≤ τ →
   (∑ x ∈ (S.filter (fun x =>
    (fun i => residue (p ^ k) (x i)) ∈ Zt (Zz (p ^ k)) C)).filter
     (fun x => (Zg x).det = t),
    Zk q s w V (fun i => residue q (x i))) ≤
     K * R ^ 2 * ((L * (p ^ k * q) : ℕ) : ℝ) ^ 6 /
      (((p ^ d.b : ℕ) : ℝ) ^ 2 * ((p ^ d.e : ℕ) : ℝ) ^ 2)) :
  (∑ x ∈ S.filter (fun x => |(Zg x).det| ≤ τ),
   ZaI (fun x i => residue (p ^ k) (x i))
    (fun x i => residue q (x i)) (Zt (Zz (p ^ k)) C)
    w V s (L ^ 9) x) ≤
   (K / (21 / 64)) * R ^ 2 * ((p ^ k : ℕ) : ℝ) * ((p ^ d.b : ℕ) : ℝ) /
    ((L * (p ^ k * q) : ℕ) : ℝ) ^ 3 := by
 classical
 let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
 exact ZlP (D := ((p ^ d.b : ℕ) : ℝ))
  (E := ((p ^ d.e : ℕ) : ℝ))
  (fun x i => residue (p ^ k) (x i)) (fun x i => residue q (x i))
  (fun x => (Zg x).det)
  (Zt (Zz (p ^ k)) C) (ZmD C) w V
  s (p ^ k) q L hs (pow_pos hp.pos _) hq hL hw S hwidth
  (Matrix.transpose C).det
  (fun x _ hxo => Znb (p ^ k) q L shift C x hxo)
  (by exact_mod_cast pow_pos hp.pos d.b)
  (by exact_mod_cast pow_pos hp.pos d.e)
  (by norm_num) hK (Zjj hp hk C d) hcount
end Problem355.Zbw
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zbw
open ZD Zc Zb Zai
def Zgr {Ω : Type*} [Fintype Ω]
  (h q L s : ℕ) [NeZero h] (shift : Fin 3 → ℤ)
  (C : Fin 3 → Fin 3 → ZMod h)
  (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
  (S : Finset (Fin 3 → Box (L * (h * q)) 3 shift)) (τ : ℤ) : ℝ := by
 classical
 exact ∑ x ∈ S.filter (fun x => |(Zg x).det| ≤ τ),
  ZaI (fun x i => residue h (x i)) (fun x i => residue q (x i))
   (Zt (Zz h) C) w V s (L ^ 9) x
theorem ZlK
  {Λ X Ω : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]
  [Fintype X] [Fintype Ω]
  {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
  (q L s : ℕ) (hq : 0 < q) (hL : 0 < L) (hs : 0 < s)
  (shift : Fin 3 → ℤ)
  (c : Zat Λ X k → Fin 3 → ZMod (p ^ k))
  (d : (z : Fin 3 → Zat Λ X k) →
   Zj p k (Matrix.transpose (fun j => c (z j))))
  (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
  (hw : ∀ ω, 0 ≤ w ω)
  (S : Finset (Fin 3 → Box (L * (p ^ k * q)) 3 shift))
  {τ : ℤ} (hwidth : 2 * τ < (p ^ k : ℕ))
  {K R : ℝ} (hK : 0 ≤ K)
  (hmoment : ∀ labels : Fin 3 → Λ,
   (∑ f : Array X k, Zy (Array X k) f *
    ((p ^ (d (ZX.symm (labels, f))).b : ℕ) : ℝ)) ≤ 2)
  (hseparate : ∀ z : Fin 3 → Zat Λ X k,
   (z 0).1 ≠ (z 1).1 → (z 0).1 ≠ (z 2).1 → (z 1).1 ≠ (z 2).1 →
   ∀ x ∈ S, (fun i => residue (p ^ k) (x i)) ∈
    Zt (Zz (p ^ k)) (fun j => c (z j)) →
     τ < |(Zg x).det|)
  (hcount : ∀ z : Fin 3 → Zat Λ X k, ∀ t : ℤ, |t| ≤ τ →
   (∑ x ∈ (S.filter (fun x => (fun i => residue (p ^ k) (x i)) ∈
    Zt (Zz (p ^ k)) (fun j => c (z j)))).filter
     (fun x => (Zg x).det = t),
    Zk q s w V (fun i => residue q (x i))) ≤
     K * R ^ 2 * ((L * (p ^ k * q) : ℕ) : ℝ) ^ 6 /
      (((p ^ (d z).b : ℕ) : ℝ) ^ 2 * ((p ^ (d z).e : ℕ) : ℝ) ^ 2)) :
  (∑ z : Fin 3 → Zat Λ X k,
   Zu.Zh (Zy (Zat Λ X k)) z *
    Zgr (p ^ k) q L s shift (fun j => c (z j)) w V S τ) ≤
   6 * (K / (21 / 64)) * R ^ 2 * ((p ^ k : ℕ) : ℝ) /
    (((L * (p ^ k * q) : ℕ) : ℝ) ^ 3 * (Fintype.card Λ : ℝ)) := by
 classical
 let A : ℝ := (K / (21 / 64)) * R ^ 2 * ((p ^ k : ℕ) : ℝ) /
  ((L * (p ^ k * q) : ℕ) : ℝ) ^ 3
 have hA : 0 ≤ A := by dsimp [A]; positivity
 have h := ZjR
  (fun labels f => ((p ^ (d (ZX.symm (labels, f))).b : ℕ) : ℝ))
  (fun z => Zgr (p ^ k) q L s shift (fun j => c (z j)) w V S τ)
  A hA hmoment (by
   intro labels f
   have hb := ZjS hp hk q L s hq hL hs shift
    (fun j => c ((ZX.symm (labels, f)) j))
    (d (ZX.symm (labels, f))) w V hw S hwidth hK
    (hcount (ZX.symm (labels, f)))
   unfold Zgr
   convert hb using 1; dsimp [A]; ring)
  (by
   intro z h01 h02 h12
   unfold Zgr
   exact Zci
    (fun x i => residue (p ^ k) (x i)) (fun x i => residue q (x i))
    (fun x => (Zg x).det)
    (Zt (Zz (p ^ k)) (fun j => c (z j)))
    w V s (L ^ 9) S τ (hseparate z h01 h02 h12))
 convert h using 1; dsimp [A]; ring
end Problem355.Zbw
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Problem355.Zas
open Zc Zu ZaD
open Zbw Zai ZD Zb
noncomputable local instance zCPD15 (p : Prop) : Decidable p := Classical.propDecidable p
def Zau (N : ℕ) :
  Finset (Fin 3 → Box N 3 (Zm N)) := by
 classical
 exact Finset.univ.filter fun x =>
  project (x 0) ≠ project (x 1) ∧ project (x 0) ≠ project (x 2) ∧
   project (x 1) ≠ project (x 2)
theorem Zjk (N : ℕ) (τ : ℤ) :
  Finset.univ.filter (ZcM (N := N) τ) =
   (Zau N).filter
    (fun x => |(ZD.Zg x).det| ≤ τ) := by
 classical
 ext x
 simp only [Zau, Finset.mem_filter, Finset.mem_univ,
  true_and, ZcM, and_assoc]
theorem ZcQ {Ω D : Type}
  [Fintype Ω] [Fintype D]
  (h q L s : ℕ) [NeZero h] [NeZero q]
  (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
  (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
  (V : Ω → Finset (Fin 3 → ZMod q))
  (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
  (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
  (hV : ∀ ω, (V ω).card = s) {τ : ℤ} (hτ : 0 ≤ τ) :
  (ZaB h q L s hc hL hs w p c V hw hwsum hp hpsum hV).Zav
   ((τ : ℝ) / (16 * ((L * (h * q) : ℕ) : ℝ) ^ 3)) ≤
   ∑ z : Fin 3 → D, Zh p z *
    Zgr h q L s (Zm (L * (h * q))) (fun j => c (z j))
     w V (Zau (L * (h * q))) τ := by
 classical
 have hbound := Zcp
  h q L s hc hL hs w p c V hw hwsum hp hpsum hV hτ
 simpa only [Zjk, Zgr] using hbound
theorem ZeY
  {Λ X Ω : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]
  [Fintype X] [Nonempty X] [Fintype Ω]
  {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
  (q L s : ℕ) [NeZero q] (hc : (p ^ k).Coprime q) (hq : 0 < q) (hL : 0 < L) (hs : 0 < s)
  (c : Zat Λ X k → Fin 3 → ZMod (p ^ k))
  (d : (z : Fin 3 → Zat Λ X k) →
   Zj p k (Matrix.transpose (fun j => c (z j))))
  (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
  (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
  (hV : ∀ ω, (V ω).card = s)
  {τ : ℤ} (hτ : 0 ≤ τ) (hwidth : 2 * τ < (p ^ k : ℕ))
  {K R : ℝ} (hK : 0 ≤ K)
  (hmoment : ∀ labels : Fin 3 → Λ,
   (∑ f : Array X k, Zy (Array X k) f *
    ((p ^ (d (ZX.symm (labels, f))).b : ℕ) : ℝ)) ≤ 2)
  (hseparate : ∀ z : Fin 3 → Zat Λ X k,
   (z 0).1 ≠ (z 1).1 → (z 0).1 ≠ (z 2).1 → (z 1).1 ≠ (z 2).1 →
   ∀ x ∈ Zau (L * (p ^ k * q)), (fun i => residue (p ^ k) (x i)) ∈
    Zt (Zz (p ^ k)) (fun j => c (z j)) →
     τ < |(Zg x).det|)
  (hcount : ∀ z : Fin 3 → Zat Λ X k, ∀ t : ℤ, |t| ≤ τ →
   (∑ x ∈ ((Zau (L * (p ^ k * q))).filter (fun x => (fun i => residue (p ^ k) (x i)) ∈
    Zt (Zz (p ^ k)) (fun j => c (z j)))).filter
     (fun x => (Zg x).det = t),
    Zk q s w V (fun i => residue q (x i))) ≤
     K * R ^ 2 * ((L * (p ^ k * q) : ℕ) : ℝ) ^ 6 /
      (((p ^ (d z).b : ℕ) : ℝ) ^ 2 * ((p ^ (d z).e : ℕ) : ℝ) ^ 2)) :
  (ZaB (p ^ k) q L s hc hL hs w
   (Zy (Zat Λ X k)) c V hw hwsum
   (Zcu _) (Zfv _) hV).Zav
   ((τ : ℝ) / (16 * ((L * (p ^ k * q) : ℕ) : ℝ) ^ 3)) ≤
   6 * (K / (21 / 64)) * R ^ 2 * ((p ^ k : ℕ) : ℝ) /
    (((L * (p ^ k * q) : ℕ) : ℝ) ^ 3 * (Fintype.card Λ : ℝ)) := by
 classical
 apply le_trans (ZcQ
  (p ^ k) q L s hc hL hs w (Zy (Zat Λ X k)) c V
  hw hwsum (Zcu _) (Zfv _) hV hτ)
 exact ZlK hp hk q L s hq hL hs
  (Zm (L * (p ^ k * q))) c d w V hw
  (Zau (L * (p ^ k * q))) hwidth hK
  hmoment hseparate hcount
end Problem355.Zas
end
end OAI
end
section
namespace OAI
noncomputable section
seal Problem355.Zam
 Problem355.ZaH
namespace Problem355.Zbd
open Parameters Zq Zai ZD Zc
open scoped BigOperators
variable {r : ℕ} [Fact r.Prime]
def ZbV (D : Zf Za r)
  (z : Fin 3 → ZH.Zat r) :
  Zj D.B Za
   (Matrix.transpose (fun j => ZH.ZiC D (z j))) :=
 ZH.ZqN D (ZX z).1 (ZX z).2
theorem Zos (D : Zf Za r)
  (labels : Fin 3 → Label r) :
  (∑ f : ZH.Array r,
   Zy (ZH.Array r) f *
    ((D.B ^ (ZbV D (ZX.symm (labels, f))).b : ℕ) : ℝ)) ≤ 2 := by
 change (∑ f : ZH.Array r,
  Zy (ZH.Array r) f *
   ((D.B ^ (ZH.ZqN D labels f).b : ℕ) : ℝ)) ≤ 2
 simpa only [Nat.cast_pow] using
  ZH.Zor D labels
theorem Zot {r : ℕ} [Fact r.Prime]
  (D : Zf Za r) : 6 < r := by
 have hk := D.two_le_k
 have hr := D.large_r
 have hk2 : 4 ≤ Za ^ 2 := by nlinarith
 omega
theorem ZoU (D : Zf Za r)
  [NeZero (D.B ^ Za)] (z : Fin 3 → ZH.Zat r)
  (h01 : (z 0).1 ≠ (z 1).1) (h02 : (z 0).1 ≠ (z 2).1)
  (h12 : (z 1).1 ≠ (z 2).1)
  {N : ℕ} {shift : Fin 3 → ℤ} (x : Fin 3 → Box N 3 shift)
  (hx : (fun i => residue (D.B ^ Za) (x i)) ∈
   Zt (Zz (D.B ^ Za)) (fun j => ZH.ZiC D (z j))) :
  (D.tau : ℤ) < |(Zg x).det| := by
 have hinj : Function.Injective (fun i => (z i).1) := by
  have hz : (![ (z 0).1, (z 1).1, (z 2).1 ] : Fin 3 → Label r) =
    (fun i => (z i).1) := by
   funext i
   fin_cases i <;> rfl
  rw [← hz]
  exact Zgs.ZpA h01 h02 h12
 exact ZeD.ZbF D
  (Zot D) (D.B ^ Za) rfl (ZX z).1 hinj
  (ZX z).2 (Zg x) hx
def Zcb (D : Zf Za r)
  [Fact D.q.Prime] (A : ZJ.Law D.q (D.h ^ 2)) (K : ℝ) : Prop := by
 classical
 letI : NeZero (D.B ^ Za) := ⟨pow_ne_zero _ D.base_prime.ne_zero⟩
 exact ∀ z : Fin 3 → ZH.Zat r, ∀ t : ℤ, |t| ≤ (D.tau : ℤ) →
  (∑ x ∈ ((Zas.Zau D.N).filter
   (fun x => (fun i => residue (D.B ^ Za) (x i)) ∈
    Zt (Zz (D.B ^ Za))
     (fun j => ZH.ZiC D (z j)))).filter
   (fun x => (Zg x).det = t),
   Zb.Zk D.q A.size A.weight A.sets
    (fun i => residue D.q (x i))) ≤
   K * (Real.log (2 * (D.N : ℝ))) ^ 2 * (D.N : ℝ) ^ 6 /
    (((D.B ^ (ZbV D z).b : ℕ) : ℝ) ^ 2 *
     ((D.B ^ (ZbV D z).e : ℕ) : ℝ) ^ 2)
theorem Zdl
  [Fintype (Label r)] (D : Zf Za r)
  [Fact D.q.Prime] (A : ZJ.Law D.q (D.h ^ 2))
  {K : ℝ} (hK : 0 ≤ K) (hcount : Zcb D A K) :
  (Zek D A).Zav
   (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
   ((128 / 7 : ℝ) * K) * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
    ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) := by
 classical
 let : NeZero (D.B ^ Za) := ⟨pow_ne_zero _ D.base_prime.ne_zero⟩
 let : NeZero (r ^ 9) := ⟨pow_ne_zero _ D.r_pos.ne'⟩
 let : NeZero D.q := ⟨D.auxiliary_prime.ne_zero⟩
 have hN : D.ZbS * (D.B ^ Za * D.q) = D.N :=
  D.ZdK
 have hwidth : 2 * (D.tau : ℤ) < (D.B ^ Za : ℕ) := by
  exact_mod_cast D.ZlT
 have hcard : Fintype.card (Label r) = r ^ 41 := by
  rw [← Nat.card_eq_fintype_card, Zq.Zrr]
  rfl
 have hb := Zas.ZeY
  (R := Real.log (2 * (D.N : ℝ)))
  D.base_prime Zfb D.q D.ZbS A.size
  D.coprime D.auxiliary_prime.pos D.ZdU A.size_pos
  (ZH.ZiC D) (ZbV D) A.weight A.sets
  A.weight_nonneg A.weight_sum A.sets_card
  (show (0 : ℤ) ≤ D.tau by positivity) hwidth hK
  (Zos D)
  (fun z h01 h02 h12 x _ hx => ZoU D z h01 h02 h12 x hx)
  (by
   unfold Zcb at hcount
   rw [hN]
   exact hcount)
 have hcardreal : (Fintype.card (Label r) : ℝ) = (r : ℝ) ^ 41 := by
  rw [hcard, Nat.cast_pow]
 rw [hN, hcardreal, Int.cast_natCast] at hb
 change (Zek D A).Zav
  (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
  6 * (K / (21 / 64)) * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
   ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) at hb
 convert hb using 1; ring
theorem ZhC
  (D : Zf Za r) {K : ℝ} (hK : 0 ≤ K)
  (hcount : ∀ A : @ZJ.Law D.q (D.h ^ 2) ⟨D.auxiliary_prime⟩,
   @Zcb r _ D ⟨D.auxiliary_prime⟩ A K) :
  (ZdV D).Zav (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
   ((128 / 7 : ℝ) * K) * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
    ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) := by
 let : Fintype (Label r) := Fintype.ofFinite (Label r)
 let : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
 unfold ZdV
 exact Zdl D _ hK (hcount _)
end Problem355.Zbd
end
end OAI
end
section
namespace OAI
noncomputable section
seal Problem355.Zam
 Problem355.ZaH
namespace Problem355.Zbd
open Matrix Parameters Zc ZD ZbR
open Zhl
open scoped BigOperators
noncomputable local instance zCPD16 (p : Prop) : Decidable p := Classical.propDecidable p
theorem Zfx (K : ℝ)
  (hraw : ∀ {B k q : ℕ} (_ : B.Prime) [Fact q.Prime],
   ∀ (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (d : Zj B k C)
    (L : ZJ.Law q ((B ^ k) ^ 2)),
   (B ^ k).Coprime q → ((B : ℝ) ^ k) ^ 26 ≤ (q : ℝ) →
   ∀ (N : ℕ), 1 ≤ N → ∀ (S : Finset Zi),
   (∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
    ZS.Zbl C) →
   (∀ A ∈ S, ∀ j, Homogeneous.ZaX (N : ℝ) (fun i => (A i j : ℝ))) →
   (∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
    Zl.ZA A i ≠ Zl.ZA A j) →
   ∀ t : ℤ, |t| < (q : ℤ) →
   (∑ A ∈ S.filter (fun A => A.det = t),
    Zb.Zk q L.size L.weight L.sets
     (A.map (Int.castRingHom (ZMod q))).col) ≤
    K * Real.log (2 * (N : ℝ)) ^ 2 * (N : ℝ) ^ 6 /
     ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2)
  {r : ℕ} [Fact r.Prime] (D : Zf Za r)
  [Fact D.q.Prime] (aux : ZJ.Law D.q (D.h ^ 2)) :
  Zcb D aux K := by
 classical
 let : NeZero D.B := ⟨D.base_prime.ne_zero⟩
 let : NeZero (D.B ^ Za) := ⟨pow_ne_zero _ D.base_prime.ne_zero⟩
 unfold Zcb
 intro z t ht
 have hparam : ((D.B : ℝ) ^ Za) ^ 26 ≤ (D.q : ℝ) := by
  exact_mod_cast (Nat.pow_le_pow_right (pow_pos D.base_prime.pos Za)
   (by norm_num : 26 ≤ 100)).trans D.auxiliary_lower.le
 have htq : |t| < (D.q : ℤ) :=
  ht.trans_lt (by exact_mod_cast D.ZrL)
 have hb := hraw D.base_prime
  (transpose (fun j => ZH.ZiC D (z j))) (ZbV D z) aux
  D.coprime hparam D.N D.N_pos
  (ZdS D.N (D.B ^ Za) (fun j => ZH.ZiC D (z j)))
  (fun A hA => ZmW hA)
  (fun A hA j => Zqr hA j)
  (fun A hA i j hij => ZlC hA i j hij) t htq
 change (∑ A ∈ (ZdS D.N (D.B ^ Za)
   (fun j => ZH.ZiC D (z j))).filter (fun A => A.det = t),
   Zdo D.q aux.size aux.weight aux.sets A) ≤ _ at hb
 rw [Zgl, ← Zjx] at hb
 have hden : ((D.B : ℝ) ^ (ZbV D z).b *
   (D.B : ℝ) ^ (ZbV D z).e) ^ 2 =
   (((D.B ^ (ZbV D z).b : ℕ) : ℝ) ^ 2 *
    ((D.B ^ (ZbV D z).e : ℕ) : ℝ) ^ 2) := by
  rw [Nat.cast_pow, Nat.cast_pow, mul_pow]
 rw [hden] at hb
 exact hb
end Problem355.Zbd
end
end OAI
end
section
namespace OAI
noncomputable section
seal Problem355.Zam
 Problem355.ZaH
namespace Problem355
theorem heilbronn_power_lower_bound :
  0 < heilbronnExponent ∧ ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point, Filter.Tendsto n Filter.atTop Filter.atTop ∧ ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ Zaz (P j) ∧ Zal (P j) (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
 let Ct : ℝ := (128 / 7 : ℝ) * ZaR.ZO
 have hCt : 0 ≤ Ct :=
  mul_nonneg (by norm_num) ZaR.ZaJ
 apply ZaD.ZdF
  8 Ct (by norm_num) hCt
 refine ⟨0, ?_⟩
 intro r _ hr _ D
 let : Fact r.Prime := ⟨hr⟩
 let : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
 refine ⟨Zbd.ZdV D, Zbd.ZeX D, ?_⟩
 exact Zbd.ZhC D
  ZaR.ZaJ
  (fun A => Zbd.Zfx
   ZaR.ZO
   @ZaR.Zqb D A)
end Problem355
end
end OAI
end
open Asymptotics Filter Topology Erdos507 OAI.Problem355
open scoped EuclideanGeometry
namespace Green77Port
noncomputable def center (p : ℝ × ℝ) : ℝ² := !₂[p.1 - 1/2, p.2 - 1/2]
lemma Zrk (p q r : ℝ × ℝ) :
  |EuclideanGeometry.triangle_area (center p) (center q) (center r)| =
   |(q.1-p.1)*(r.2-p.2)-(q.2-p.2)*(r.1-p.1)| / 2 := by
 rw [EuclideanGeometry.triangle_area_eq_det, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
 congr 2
 simp [Matrix.det_fin_three, center]
 <;> ring
lemma ZrR {f : ℕ → ℝ} {d : ℝ} (hd : 0 < d) {n : ℕ → ℕ}
  (hn : Tendsto n atTop atTop) (hl : ∀ j, (n j : ℝ)^(-2+d) ≤ f (n j)) :
  ¬ ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧ f =O[atTop] (fun k => (k:ℝ)^(-2+o k)) := by
 rintro ⟨o, ho, hb⟩
 obtain ⟨C, hC, h⟩ := hb.exists_pos
 have h1 := hn.eventually (eventually_ge_atTop 1)
 have h2 := (ho.comp hn).eventually_lt_const (show 0 < d/2 by linarith)
 have h3 := hn.eventually h.bound
 have h4 := ((tendsto_rpow_atTop (show 0 < d/2 by linarith)).comp (tendsto_natCast_atTop_atTop.comp hn)).eventually (eventually_gt_atTop C)
 obtain ⟨j,hj,hoj,hbj,hcj⟩ := (h1.and (h2.and (h3.and h4))).exists
 have hp : (1:ℝ) ≤ n j := by exact_mod_cast hj
 have hp' : (0:ℝ) < n j := by linarith
 change C < (n j : ℝ)^(d/2) at hcj
 change o (n j) < d/2 at hoj
 change ‖f (n j)‖ ≤ C * ‖(n j:ℝ)^(-2+o (n j))‖ at hbj
 rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp'.le _)] at hbj
 have hh := (hl j).trans ((le_abs_self _).trans hbj)
 have hu := hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp (show -2+o (n j) ≤ -2+d/2 by linarith)) hC.le)
 have hx : -2+d = (-2+d/2)+d/2 := by ring
 rw [hx, Real.rpow_add hp'] at hu
 nlinarith [Real.rpow_pos_of_pos hp' (-2+d/2), mul_pos (Real.rpow_pos_of_pos hp' (-2+d/2)) (sub_pos.mpr hcj)]
lemma Zqi : Function.Injective center := by
 intro p q h
 have h0 := congrArg (fun x : ℝ² => x 0) h
 have h1 := congrArg (fun x : ℝ² => x 1) h
 exact Prod.ext (by simpa [center] using h0) (by simpa [center] using h1)
lemma Zru {p : Point} (hp : Zbf p) : center p ∈ Metric.closedBall (0 : ℝ²) 1 := by
 obtain ⟨ha,hb,hc,hd⟩ := hp
 rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_le_left (by norm_num)]
 simp [center, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
 nlinarith [mul_nonneg ha (sub_nonneg.mpr hb), mul_nonneg hc (sub_nonneg.mpr hd)]
lemma ZqY {x : ℝ²} (hx : x ∈ Metric.closedBall (0 : ℝ²) 1) (i : Fin 2) : |x i| ≤ 1 := by
 rw [mem_closedBall_zero_iff] at hx
 exact (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i : |x i| ≤ ‖x‖).trans hx
lemma ZrY {a b c : ℝ²} (ha : a ∈ Metric.closedBall (0 : ℝ²) 1)
  (hb : b ∈ Metric.closedBall (0 : ℝ²) 1) (hc : c ∈ Metric.closedBall (0 : ℝ²) 1) :
  |EuclideanGeometry.triangle_area a b c| ≤ 3 := by
 rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
 simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
  Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
  Matrix.head_fin_const, Matrix.tail_cons]
 have h := fun (x y : ℝ²) (hx : x ∈ Metric.closedBall (0 : ℝ²) 1) (hy : y ∈ Metric.closedBall (0 : ℝ²) 1) =>
  abs_le.mp ((abs_mul (x 0) (y 1)).trans_le (mul_le_one₀ (ZqY hx 0) (abs_nonneg _) (ZqY hy 1)))
 have e1 := h a b ha hb; have e2 := h a c ha hc; have e3 := h b a hb ha
 have e4 := h b c hb hc; have e5 := h c a hc ha; have e6 := h c b hc hb
 rw [mul_one, mul_one, mul_one, mul_one, mul_one, mul_one, abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2), abs_le]; constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2]
lemma Zrv {S : Finset ℝ²} (hS : ↑S ⊆ Metric.closedBall (0 : ℝ²) 1) : minTriangleArea S ≤ 3 := by
 unfold minTriangleArea
 set A := {x | ∃ (p : Fin 3 → ℝ²) (_ : Function.Injective p) (_ : ∀ i, p i ∈ S),
    |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| = x}
 rcases A.eq_empty_or_nonempty with h | ⟨x, p, hi, hp, rfl⟩
 · rw [h, Real.sInf_empty]; norm_num
 · have hb : BddBelow A := ⟨0, by rintro _ ⟨q, -, -, rfl⟩; exact abs_nonneg _⟩
   exact (csInf_le hb ⟨p, hi, hp, rfl⟩).trans (ZrY (hS (hp 0)) (hS (hp 1)) (hS (hp 2)))
lemma ZlL {a b c : ℝ²} (h : Collinear ℝ ({a, b, c} : Set ℝ²)) :
  EuclideanGeometry.triangle_area a b c = 0 := by
 obtain ⟨p, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp h
 obtain ⟨r, rfl⟩ := hv a (by simp)
 obtain ⟨s, rfl⟩ := hv b (by simp)
 obtain ⟨t, rfl⟩ := hv c (by simp)
 rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
 simp
 ring
lemma ZrS (n : ℕ) (P : Finset Point) (a : ℝ) (ha : 0 < a) (h3 : 3 ≤ n) (hc : P.card = n)
   (hs : Zaz P) (ht : Zal P a) : a ≤ α n := by
 classical
 set S := P.image center
 have hS : ↑S ⊆ Metric.closedBall (0 : ℝ²) 1 := by
   intro x hx
   obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
   exact Zru (hs p hp)
 have key : ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, p ≠ q → p ≠ r → q ≠ r →
     a ≤ |EuclideanGeometry.triangle_area (center p) (center q) (center r)| := by
   intro p hp q hq r hr h1 h2 h3
   rw [Zrk]; exact ht p hp q hq r hr h1 h2 h3
 obtain ⟨p, hp, q, hq, r, hr, h1, h2, h3⟩ := Finset.two_lt_card.mp (by omega : 2 < P.card)
 have hcol : ¬ Collinear ℝ (S : Set ℝ²) := by
   intro hC
   have := ZlL (hC.subset (by
     intro x hx
     simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
     rcases hx with rfl | rfl | rfl
     exacts [Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hq, Finset.mem_image_of_mem _ hr]))
   linarith [key p hp q hq r hr h1 h2 h3, abs_nonneg (EuclideanGeometry.triangle_area (center p) (center q) (center r)), this ▸ (abs_zero : |(0:ℝ)| = 0)]
 have hmin : a ≤ minTriangleArea S := by
   unfold minTriangleArea
   apply le_csInf
   · refine ⟨_, ![center p, center q, center r], ?_, ?_, rfl⟩
     · intro i j hij
       fin_cases i <;> fin_cases j <;> simp_all [Zqi.eq_iff]
     · intro i; fin_cases i
       exacts [Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hq, Finset.mem_image_of_mem _ hr]
   · rintro _ ⟨f, hf, hm, rfl⟩
     obtain ⟨x, hx, ex⟩ := Finset.mem_image.mp (hm 0)
     obtain ⟨y, hy, ey⟩ := Finset.mem_image.mp (hm 1)
     obtain ⟨z, hz, ez⟩ := Finset.mem_image.mp (hm 2)
     rw [← ex, ← ey, ← ez]
     refine key x hx y hy z hz ?_ ?_ ?_ <;> rintro rfl
     · exact absurd (ex.symm.trans ey) (hf.ne (by decide))
     · exact absurd (ex.symm.trans ez) (hf.ne (by decide))
     · exact absurd (ey.symm.trans ez) (hf.ne (by decide))
 refine hmin.trans (le_csSup ⟨3, ?_⟩ ⟨S, ⟨?_, hS, hcol⟩, rfl⟩)
 · rintro _ ⟨T, ⟨-, hT, -⟩, rfl⟩; exact Zrv hT
 · rw [Finset.card_image_of_injective _ Zqi, hc]
end Green77Port
open Green77Port in
theorem OMA.disproof : ¬ (type_of% @Green77.green_77) := by
 obtain ⟨hd, n, P, hn, hP⟩ := heilbronn_power_lower_bound
 refine ZrR hd hn fun j => ?_
 obtain ⟨h3, hc, hs, ht⟩ := hP j
 exact ZrS _ _ _ (Real.rpow_pos_of_pos (by have := h3; positivity) _) h3 hc hs ht
