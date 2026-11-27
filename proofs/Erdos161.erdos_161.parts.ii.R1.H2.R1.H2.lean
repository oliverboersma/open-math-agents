import OMAReductions.R_Erdos161_erdos_161_parts_ii_R1_H2_R1
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-!
This is a Lean formalization of the uniform complete-hypergraph blow-up bound of
Dhruv Mubayi, *Large blow-ups of uniform hypergraphs*, Theorem 1 and Lemma 4,
arXiv:2611.33108v1, posted 24 November 2026. The paper is available at
https://arxiv.org/abs/2611.33108v1 under CC BY 4.0,
https://creativecommons.org/licenses/by/4.0/. This Lean adaptation specializes
Mubayi’s patterned-list argument and coordinate-copy inequality to cliques.
It uses a single vertex alphabet for all rows and recovers disjoint classes
from the joint injectivity of the transversal tuples. The formal dense-clique
predicate comes from open-math-agents PR 3566,
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3566.
-/

/- Partite -/
section

/-! From dense unordered hypergraph cliques to ordered transversal tuples on
full copies of the original ground set, and from a product of such tuples
back to disjoint vertex classes on that ground set. -/
namespace Erdos161Partite
open Finset
open scoped Classical
noncomputable section

def Trans {n d : ℕ} (t : ℕ) (G : Finset (Fin n) → Bool) (x : Fin d → Fin n) : Prop :=
  ∀ I : (univ : Finset (Fin d)).powersetCard t, (I.val.image x).card=t ∧ G (I.val.image x)=true

def cliques {n : ℕ} (d t : ℕ) (G : Finset (Fin n) → Bool) : Finset (Finset (Fin n)) :=
  ((univ : Finset (Fin n)).powersetCard d).filter (fun S => ∀ e⊆S, e.card=t → G e=true)

def transTuples {n d : ℕ} (t : ℕ) (G : Finset (Fin n) → Bool) : Finset (Fin d → Fin n) :=
  univ.filter (Trans t G)

/-- Sorting each clique canonically gives a distinct admissible ordered tuple. -/
theorem clique_to_trans {n : ℕ} (d t : ℕ) (G : Finset (Fin n) → Bool) :
    (cliques d t G).card ≤ (transTuples (d:=d) t G).card := by
  let K := cliques d t G
  let Q := transTuples (d:=d) t G
  have sz (S : K) : S.val.card=d := (mem_powersetCard.mp (mem_filter.mp S.property).1).2
  let x (S : K) := S.val.orderEmbOfFin (sz S)
  have orig (S : K) : univ.image (x S)=S.val := S.val.image_orderEmbOfFin_univ (sz S)
  have valid (S : K) : Trans t G (x S) := by
    intro I
    have hT : (I.val.image (x S)).card=t := by
      rw [card_image_of_injective _ (x S).injective]
      exact (mem_powersetCard.mp I.property).2
    refine ⟨hT,(mem_filter.mp S.property).2 _ ?_ hT⟩
    intro v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact S.val.orderEmbOfFin_mem (sz S) i
  let enc (S : K) : Q := ⟨x S,mem_filter.mpr ⟨mem_univ _,valid S⟩⟩
  have hinj : Function.Injective enc := by
    intro U V h
    apply Subtype.ext
    rw [←orig U,←orig V]
    exact congrArg (fun f : Fin d → Fin n => univ.image f) (congrArg Subtype.val h)
  simpa [K,Q] using Fintype.card_le_of_injective enc hinj

/-- The finite multiplicative loss depends only on the clique size. -/
theorem clique_to_trans_density {n d t : ℕ} (G : Finset (Fin n) → Bool) (hn : 2*d≤n)
    {δ : ℝ} (hδ : 0≤δ) (hG : δ*(n.choose d : ℝ)≤(cliques d t G).card) :
    (δ/((2:ℝ)^d*d.factorial))*(n:ℝ)^d ≤ (transTuples (d:=d) t G).card := by
  have hb : (n:ℝ)/2≤((n+1-d : ℕ):ℝ) := by
    have h : n≤2*(n+1-d) := by omega
    exact (div_le_iff₀ (by norm_num)).2 (by exact_mod_cast (by simpa [Nat.mul_comm] using h))
  have hh := Nat.pow_le_choose (α:=ℝ) d n
  have pow := pow_le_pow_left₀ (show 0≤(n:ℝ)/2 by positivity) hb d
  have df : 0 < (d.factorial:ℝ) := by exact_mod_cast d.factorial_pos
  have hq : (n:ℝ)^d/(2^d*d.factorial)≤(n.choose d : ℝ) := by
    rw [←div_div,←div_pow]
    exact (div_le_div_of_nonneg_right pow df.le).trans hh
  calc
    _ = δ*((n:ℝ)^d/(2^d*d.factorial)) := by ring
    _ ≤ δ*(n.choose d:ℝ) := mul_le_mul_of_nonneg_left hq hδ
    _ ≤ (cliques d t G).card := hG
    _ ≤ _ := by exact_mod_cast clique_to_trans d t G

/-- Each pair of indices occurs in some t-set. The cardinality part of the
transversal predicate therefore rules out every cross-class collision. -/
theorem trans_injective {n d t : ℕ} {G : Finset (Fin n) → Bool} {x : Fin d → Fin n}
    (ht : 2≤t) (hd : t≤d) (ok : Trans t G x) : Function.Injective x := by
  intro i j eq
  by_contra hij
  have hm : ({i,j}:Finset (Fin d)).card≤t := by simp [hij,ht]
  obtain ⟨I,sub,_,sz⟩ := exists_subsuperset_card_eq (subset_univ ({i,j}:Finset (Fin d))) hm
    (show t≤(univ:Finset (Fin d)).card by simpa using hd)
  have h := (ok ⟨I,mem_powersetCard.mpr ⟨subset_univ _,sz⟩⟩).1
  have inj := card_image_iff.mp (h.trans sz.symm)
  exact hij (inj (sub (by simp)) (sub (by simp)) eq)

theorem trans_subedge {n d t : ℕ} {G : Finset (Fin n) → Bool} {x : Fin d → Fin n}
    (inj : Function.Injective x) (ok : Trans t G x)
    (e : Finset (Fin n)) (hsize : e.card=t) (sub : e⊆univ.image x) : G e=true := by
  let I := univ.filter fun i=>x i∈e
  have img : I.image x=e := by
    ext v
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      exact (mem_filter.mp hi).2
    · intro h
      obtain ⟨i,_,hi⟩ := mem_image.mp (sub h)
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _, hi ▸ h⟩,hi⟩
  have sz : I.card=t := by rw [←card_image_of_injective I inj,img,hsize]
  simpa only [img] using (ok ⟨I,mem_powersetCard.mpr ⟨subset_univ _,sz⟩⟩).2

/-- Read a transversal cylinder as genuinely disjoint ground-set parts and
recover each t-edge satisfying the exact coverage/intersection constraints. -/
theorem cylinder_parts {n d t : ℕ} {G : Finset (Fin n) → Bool} (V : Fin d → Finset (Fin n))
    (ht : 2≤t) (hd : t≤d) (hne : ∀i,(V i).Nonempty)
    (box : ∀ x : Fin d → Fin n, (∀i,x i∈V i) → Trans t G x) :
    (∀ i j,i≠j → Disjoint (V i) (V j)) ∧
    ∀ e : Finset (Fin n), e.card=t → (∀v∈e,∃i,v∈V i) →
      (∀i,(e∩V i).card≤1) → G e=true := by
  let base (i : Fin d) := (hne i).choose
  have hm (i : Fin d) : base i∈V i := (hne i).choose_spec
  constructor
  · intro i j h
    apply Finset.disjoint_left.mpr
    intro v vi vj
    let x (a : Fin d) := if a=i ∨ a=j then v else base a
    have good (a : Fin d) : x a∈V a := by
      by_cases e : a=i ∨ a=j
      · rcases e with rfl|rfl <;> simp [x,vi,vj]
      · simp [x,e,hm]
    exact h (trans_injective ht hd (box x good) (by simp [x]))
  · intro e sz cover one
    let x (i : Fin d) := if h : (e∩V i).Nonempty then h.choose else base i
    have good (i : Fin d) : x i∈V i := by
      dsimp only [x]; split
      · rename_i h; exact (mem_inter.mp h.choose_spec).2
      · exact hm i
    apply trans_subedge (trans_injective ht hd (box x good)) (box x good) e sz
    intro v hv
    obtain ⟨i,hi⟩ := cover v hv
    have ne : (e∩V i).Nonempty := ⟨v,mem_inter.mpr ⟨hv,hi⟩⟩
    have hxe : x i∈e∩V i := by simp only [x,dif_pos ne]; exact ne.choose_spec
    exact mem_image.mpr ⟨i,mem_univ _,card_le_one.mp (one i) _ hxe _ (mem_inter.mpr ⟨hv,hi⟩)⟩

end
end Erdos161Partite

end

/- Growth -/
section

/-! The final comparison in Section 3 of Dhruv Mubayi,
*Large blow-ups of uniform hypergraphs*, arXiv:2611.33108v1 (2026).
We use 2s entries in each class and the elementary bound d(s²/N)^s
for the density of choices with a class containing fewer than s distinct entries. -/

namespace Mubayi.Growth
open Filter

private theorem class_size (d n : ℕ) (hd : 0 < d) (hn : d ≤ n) :
    (n : ℝ) ≤ 2 * (d : ℝ) * ((n/d : ℕ) : ℝ) := by
  have pos : 0 < n / d := Nat.div_pos hn hd
  have e : n ≤ 2 * d * (n/d) := calc
    n ≤ d * (n/d + 1) := (Nat.lt_mul_div_succ n hd).le
    _ ≤ d * (2 * (n/d)) := Nat.mul_le_mul_left d (by omega)
    _ = _ := by ring
  exact_mod_cast e

private theorem choose_succ (q d : ℕ) (hq : 0 < q) (hd : 0 < d) (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∃ s : ℕ, 1 ≤ s ∧
      c * (Real.log n) ^ (q : ℝ)⁻¹ ≤ (s : ℝ) ∧
      (d : ℝ) * ((s : ℝ)^2 / ((n/d : ℕ) : ℝ)) ^ s <
        (2 : ℝ) ^ (-(C * (2*(s : ℝ))^(q+1))) := by
  let L (n : ℕ) := Real.log (n : ℝ)
  let r : ℝ := (q : ℝ)⁻¹
  let D : ℝ := C * 2^(q+1) * Real.log 2
  let K : ℝ := 8*(D+1)
  have rpos : 0 < r := inv_pos.mpr (by exact_mod_cast hq)
  have Dpos : 0 < D := mul_pos (mul_pos hC (by positivity)) (Real.log_pos (by norm_num))
  have Kone : 1 ≤ K := by dsimp [K]; linarith
  have Kpos : 0 < K := lt_of_lt_of_le zero_lt_one Kone
  have Ltop : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have sizetop : Tendsto (fun n => (L n / K)^r) atTop atTop :=
    (tendsto_rpow_atTop rpos).comp (Ltop.atTop_div_const Kpos)
  have little : ∀ᶠ n : ℕ in atTop, ‖Real.log (L n)‖ ≤ (1/8 : ℝ)*‖L n‖ :=
    Ltop.eventually (Real.isLittleO_log_id_atTop.bound (by norm_num))
  refine ⟨(1/2 : ℝ) / K^r, div_pos (by norm_num) (Real.rpow_pos_of_pos Kpos r),?_⟩
  filter_upwards [eventually_ge_atTop d, Ltop.eventually_ge_atTop 1,
      Ltop.eventually_ge_atTop (8*Real.log (d:ℝ)), Ltop.eventually_ge_atTop (8*Real.log (2*(d:ℝ))),
      sizetop.eventually_ge_atTop 2, little] with n hn hL hld hl2 big small
  let s := ⌊(L n / K)^r⌋₊
  have Xnon : 0 ≤ L n := by linarith
  have s_upper : (s : ℝ) ≤ (L n/K)^r := Nat.floor_le (by positivity)
  have s_close : (L n/K)^r < (s : ℝ)+1 := Nat.lt_floor_add_one _
  have s_one : 1 ≤ s := by
    by_contra! h
    have : s = 0 := by omega
    rw [this] at s_close
    norm_num at s_close
    linarith
  have spos : (0 : ℝ) < s := by exact_mod_cast s_one
  have sone : (1 : ℝ) ≤ s := by exact_mod_cast s_one
  have scaling : (L n/K)^r = (L n)^r / K^r := Real.div_rpow Xnon Kpos.le r
  refine ⟨s,s_one,?_,?_⟩
  · change (1/2 : ℝ)/K^r * (L n)^r ≤ (s : ℝ)
    rw [show (1/2 : ℝ)/K^r * (L n)^r = ((L n)^r / K^r)/2 by ring, ← scaling]
    linarith
  · have pw : (s:ℝ)^q ≤ L n / K :=
      (pow_le_pow_left₀ spos.le s_upper q).trans_eq (Real.rpow_inv_natCast_pow (div_nonneg Xnon Kpos.le) hq.ne')
    have powbound := (le_div_iff₀ Kpos).mp pw
    have energy : D*(s:ℝ)^q ≤ L n/8 := by
      dsimp only [K] at powbound
      nlinarith [pow_nonneg spos.le q]
    have s_le_L : (s:ℝ) ≤ L n := calc
      (s:ℝ) = (s:ℝ)^1 := (pow_one _).symm
      _ ≤ (s:ℝ)^q := pow_le_pow_right₀ sone hq
      _ ≤ _ := pw.trans (div_le_self Xnon Kone)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg Xnon] at small
    have log_s : Real.log (s:ℝ) ≤ L n/8 := by
      have := Real.log_le_log spos s_le_L
      have := le_abs_self (Real.log (L n))
      linarith
    have dpos : (0 : ℝ) < d := by exact_mod_cast hd
    have npos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le hd hn
    have Npos : (0 : ℝ) < ((n / d : ℕ) : ℝ) := by exact_mod_cast Nat.div_pos hn hd
    have LN := Real.log_le_log npos (class_size d n hd hn)
    rw [Real.log_mul (mul_pos (by norm_num) dpos).ne' Npos.ne'] at LN
    change L n ≤ _ at LN
    have bracket : 2*Real.log (s:ℝ) - Real.log ((n/d : ℕ) : ℝ) ≤ -(L n/2) := by linarith
    have sLX : L n ≤ (s:ℝ)*L n := by nlinarith [mul_nonneg (sub_nonneg.mpr sone) Xnon]
    have left : Real.log (d:ℝ)+(s:ℝ)*(2*Real.log (s:ℝ)-Real.log ((n/d : ℕ) : ℝ)) <
        -(s:ℝ)*(D*(s:ℝ)^q) := by
      nlinarith only [hld,mul_le_mul_of_nonneg_left bracket spos.le,
        mul_le_mul_of_nonneg_left energy spos.le,sLX,hL]
    apply (Real.log_lt_log_iff (mul_pos dpos (pow_pos (div_pos (pow_pos spos _) Npos) _))
      (Real.rpow_pos_of_pos (by norm_num) _)).mp
    rw [Real.log_mul dpos.ne' (pow_pos (div_pos (pow_pos spos _) Npos) _).ne',Real.log_pow,
      Real.log_div (pow_pos spos _).ne' Npos.ne',Real.log_pow,Real.log_rpow (by norm_num : (0:ℝ) < 2)]
    push_cast
    convert left using 1 <;> dsimp only [D] <;> rw [mul_pow] <;> ring

/-- At the logarithmic blow-up scale the density of full lists exceeds the total
density of lists with a class of insufficient support. -/
theorem choose_size (t d : ℕ) (ht : 2 ≤ t) (hd : 0 < d) (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∃ s : ℕ, 1 ≤ s ∧
      c * (Real.log n) ^ (((t:ℝ)-1)⁻¹) ≤ (s : ℝ) ∧
      (d : ℝ) * ((s : ℝ)^2 / ((n/d : ℕ) : ℝ)) ^ s <
        (2 : ℝ) ^ (-(C * (2*(s : ℝ))^t)) := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  simpa using choose_succ q d (by omega) hd C hC

end Mubayi.Growth

end

/- BadList -/
section

/-! Counting deficient columns (rows of an array of lists) in Mubayi's
list-counting argument for blow-ups of hypergraphs, arXiv:2611.33108. -/

namespace Mubayi.BadList
open Finset

abbrev Lists (d m n : ℕ) := Fin d → Fin m → Fin n

def support {m n : ℕ} (x : Fin m → Fin n) : Finset (Fin n) :=
  univ.image x

noncomputable def rowIn {d m n : ℕ} (i : Fin d) (U : Finset (Fin n)) :
    Finset (Lists d m n) :=
  Fintype.piFinset (fun j => if j=i then Fintype.piFinset (fun _ : Fin m => U) else univ)

theorem mem_rowIn {d m n : ℕ} (x : Lists d m n) (i : Fin d) (U : Finset (Fin n)) :
    x ∈ rowIn i U ↔ ∀ k, x i k ∈ U := by
  classical
  simp only [rowIn,Fintype.mem_piFinset]
  constructor
  · intro h
    simpa using h i
  · intro h j
    by_cases hj : j=i
    · subst j
      simpa using h
    · simp [hj]

theorem card_rowIn {d m n : ℕ} (i : Fin d) (U : Finset (Fin n)) :
    (rowIn (m:=m) i U).card = U.card ^ m * (n ^ m) ^ (d - 1) := by
  classical
  unfold rowIn
  rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (mem_univ i)]
  congr 1
  · simp
  calc
    _ = ∏ _j ∈ (univ.erase i), n ^ m := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Finset.ne_of_mem_erase hj]
    _ = _ := by simp

/-- Any family whose lists have some deficient row satisfies this union bound;
the ambient family can, in particular, require that every transversal is a clique. -/
theorem card_le_of_deficient_row {d m n s : ℕ} (hsn : s ≤ n)
    (F : Finset (Lists d m n))
    (bad : ∀ x ∈ F, ∃ i, (support (x i)).card ≤ s) :
    F.card ≤ d * n.choose s * s ^ m * (n ^ m) ^ (d - 1) := by
  classical
  let palettes := (univ : Finset (Fin n)).powersetCard s
  let cover : Fin d → Finset (Lists d m n) := fun i => palettes.biUnion (rowIn i)
  have hsub : F ⊆ univ.biUnion cover := by
    intro x hx
    obtain ⟨i, hi⟩ := bad x hx
    obtain ⟨U, hU, _hU, hcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (support (x i))) hi (by simpa using hsn)
    apply Finset.mem_biUnion.mpr ⟨i,mem_univ i,?_⟩
    apply Finset.mem_biUnion.mpr ⟨U,(Finset.mem_powersetCard.mpr ⟨U.subset_univ,hcard⟩),?_⟩
    exact (mem_rowIn x i U).mpr (fun k => hU (mem_image_of_mem _ (mem_univ k)))
  have hrow (i : Fin d) :
      (cover i).card ≤ n.choose s * (s ^ m * (n ^ m) ^ (d - 1)) := by
    calc
      _ ≤ palettes.card * (s ^ m * (n ^ m) ^ (d - 1)) :=
        Finset.card_biUnion_le_card_mul _ _ _ (by
          intro U hU
          rw [card_rowIn, (mem_powersetCard.mp hU).2])
      _ = _ := by simp [palettes]
  calc
    _ ≤ (univ.biUnion cover).card := card_le_card hsub
    _ ≤ univ.card * (n.choose s * (s ^ m * (n ^ m) ^ (d - 1))) :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun i _ => hrow i)
    _ = _ := by simp [Nat.mul_assoc]


/-- Support of a full array contains a genuine balanced box as soon as each row
has at least s distinct entries. The choices in different rows are independent. -/
theorem box_of_full {d m n s : ℕ} (T : (Fin d → Fin n) → Prop)
    (x : Lists d m n)
    (full : ∀ j : Fin d → Fin m, T (fun i => x i (j i)))
    (large : ∀ i, s ≤ (support (x i)).card) :
    ∃ A : Fin d → Finset (Fin n), (∀ i, (A i).card = s) ∧
      ∀ a : Fin d → Fin n, (∀ i, a i ∈ A i) → T a := by
  classical
  choose A hsub hcard using fun i => Finset.exists_subset_card_eq (large i)
  refine ⟨A,hcard,?_⟩
  intro a ha
  have lift (i : Fin d) : ∃ j : Fin m, x i j = a i := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hsub i (ha i))
    exact ⟨j,hj⟩
  choose j hj using lift
  simpa only [show (fun i => x i (j i)) = a from funext hj] using full j

/-- With no balanced box of side s, the union bound for deficient lists applies
to every full array. Specializing m=2s is Mubayi's collision bound. -/
theorem card_full_le_of_no_box {d m n s : ℕ} (hsn : s ≤ n)
    (T : (Fin d → Fin n) → Prop) (F : Finset (Lists d m n))
    (full : ∀ x ∈ F, ∀ j : Fin d → Fin m, T (fun i => x i (j i)))
    (noBox : ¬∃ A : Fin d → Finset (Fin n), (∀ i, (A i).card = s) ∧
      ∀ a : Fin d → Fin n, (∀ i, a i ∈ A i) → T a) :
    F.card ≤ d * n.choose s * s ^ m * (n ^ m) ^ (d - 1) := by
  classical
  apply card_le_of_deficient_row hsn F
  intro x hx
  by_contra! h
  exact noBox (box_of_full T x (full x hx) (fun i => (h i).le))

end Mubayi.BadList

end

/- BadDensity -/
section

/-! Normalizing the deficient-list count by the size of the uniform sample space. -/
namespace Mubayi.BadList

theorem full_density_le {d n s : ℕ} (hd : 0 < d) (hn : 0 < n) (_hs : 1 ≤ s)
    (hsn : s ≤ n) (T : (Fin d → Fin n) → Prop) (F : Finset (Lists d (2*s) n))
    (full : ∀ x ∈ F, ∀ j : Fin d → Fin (2*s), T (fun i => x i (j i)))
    (noBox : ¬∃ A : Fin d → Finset (Fin n), (∀ i, (A i).card = s) ∧
      ∀ a : Fin d → Fin n, (∀ i, a i ∈ A i) → T a) :
    (F.card : ℝ) / (Fintype.card (Lists d (2*s) n) : ℝ) ≤
      (d : ℝ) * (((s : ℝ)^2)/(n : ℝ))^s := by
  have cnt := card_full_le_of_no_box hsn T F full noBox
  have natBound : F.card ≤ d * n^s * s^(2*s) * (n^(2*s))^(d-1) :=
    cnt.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left d (Nat.choose_le_pow n s))))
  have hnum : (F.card : ℝ) ≤ (d : ℝ) * (n : ℝ)^s * (s : ℝ)^(2*s) *
      ((n : ℝ)^(2*s))^(d-1) := by exact_mod_cast natBound
  have cardT : Fintype.card (Lists d (2*s) n) = (n^(2*s))^d := by simp [Lists]
  rw [cardT]
  push_cast
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ (by positivity)).2
  refine hnum.trans_eq ?_
  have hdPow : ((n : ℝ)^(2*s))^d = ((n : ℝ)^(2*s))^(d-1) * (n : ℝ)^(2*s) := by
    rw [←pow_succ, Nat.sub_add_cancel hd]
  have hnPow : (n : ℝ)^(2*s) = ((n:ℝ)^s)^2 := by rw [←pow_mul, Nat.mul_comm s 2]
  rw [div_pow, ←pow_mul, hdPow, hnPow]
  field_simp
  <;> ring

end Mubayi.BadList

end

/- Assembly -/
section

namespace Mubayi.Solution
open Filter Finset
open scoped Classical
noncomputable section

abbrev Array (d m n : ℕ) := Fin d → Fin m → Fin n

/-- The lower estimate on fully admissible lists, stated on copies of one common
vertex alphabet so that no partitioning or rounding loss is needed. -/
def LowerBound : Prop :=
  ∀ {n d t m : ℕ} (G : Finset (Fin n) → Bool), 0 < n → 0 < m → ∀ {p0 : ℝ}, 0 < p0 →
    p0*(n:ℝ)^d ≤ ((Erdos161Partite.transTuples (d:=d) t G).card:ℝ) →
    (2:ℝ)^(-(max 1 ((d.choose t : ℝ)/p0) * (m:ℝ)^t)) ≤
    ((univ.filter (fun X : Array d m n => ∀ a : Fin d → Fin m,
      Erdos161Partite.Trans t G (fun i => X i (a i)))).card:ℝ) /
      Fintype.card (Array d m n)

/-- Reusing the full alphabet both increases the class size and simplifies the
transversal-to-disjoint-classes conversion. -/
private theorem choose_alphabet (t d : ℕ) (ht : 2 ≤ t) (hd : 0 < d) (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∃ s : ℕ, 1 ≤ s ∧ s ≤ n ∧
      c * (Real.log n) ^ (((t:ℝ)-1)⁻¹) ≤ (s : ℝ) ∧
      (d : ℝ) * ((s : ℝ)^2 / (n:ℝ))^s < (2:ℝ)^(-(C*(2*(s:ℝ))^t)) := by
  obtain ⟨c,hc,event⟩ := Mubayi.Growth.choose_size t d ht hd C hC
  refine ⟨c,hc,?_⟩
  filter_upwards [event,eventually_ge_atTop d] with n h hn
  obtain ⟨s,hs,scale,gap⟩ := h
  have Npos : (0 : ℝ) < ((n/d : ℕ) : ℝ) := by exact_mod_cast Nat.div_pos hn hd
  have Nle : ((n/d : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n d
  have dpos : (0 : ℝ) < d := by exact_mod_cast hd
  have d_one : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have p0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have p1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have numerator : 0 ≤ (s:ℝ)^2 := sq_nonneg _
  have gap' : (d:ℝ)*((s:ℝ)^2 / n)^s < _ := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left numerator Npos Nle) s) dpos.le) gap
  refine ⟨s,hs,?_,scale,gap'⟩
  by_contra! h
  have ns : (n:ℝ) < s := by exact_mod_cast h
  have num : (n:ℝ) ≤ (s:ℝ)^2 := by nlinarith [mul_nonneg p0 (sub_nonneg.mpr p1)]
  have base : (1:ℝ) ≤ (s:ℝ)^2 / n := (one_le_div (Npos.trans_le Nle)).mpr num
  have lo : (1:ℝ) ≤ d*((s:ℝ)^2 / n)^s := one_le_mul_of_one_le_of_one_le d_one (one_le_pow₀ base)
  have epos : 0 ≤ C*(2*(s:ℝ))^t := by positivity
  have hi : (2:ℝ)^(-(C*(2*(s:ℝ))^t)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr epos)
  exact (not_lt_of_ge (lo.trans' hi)) gap'

theorem assemble (lower : LowerBound) (t d : ℕ) (ht : 4 ≤ t) (hd : t ≤ d)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ G : Finset (Fin n) → Bool,
      δ*(n.choose d : ℝ) ≤ ((Erdos161Partite.cliques d t G).card:ℝ) →
      ∃ (s : ℕ) (V : Fin d → Finset (Fin n)),
        1 ≤ s ∧ c*(Real.log n)^(((t:ℝ)-1)⁻¹) ≤ (s:ℝ) ∧
        (∀ i, (V i).card=s) ∧ (∀ i j, i≠j → Disjoint (V i) (V j)) ∧
        ∀ e : Finset (Fin n), e.card=t → (∀ x ∈ e, ∃ i, x ∈ V i) →
          (∀ i, (e ∩ V i).card ≤ 1) → G e=true := by
  classical
  let p0 : ℝ := δ / ((2:ℝ)^d*d.factorial)
  have hp0 : 0 < p0 := div_pos hδ (mul_pos (by positivity) (by exact_mod_cast d.factorial_pos))
  let C : ℝ := max 1 ((d.choose t:ℝ)/p0)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨c,hc,event⟩ := choose_alphabet t d (by omega) (by omega) C hC
  refine ⟨c,hc,?_⟩
  filter_upwards [event,eventually_ge_atTop (2*d)] with n bounds hn
  obtain ⟨s,hs,hsn,scale,gap⟩ := bounds
  intro G hG
  have dens := Erdos161Partite.clique_to_trans_density G hn hδ.le hG
  let T := Erdos161Partite.Trans (d:=d) t G
  let F := univ.filter (fun X : Array d (2*s) n => ∀ a : Fin d → Fin (2*s), T (fun i => X i (a i)))
  have good (X) (mem : X ∈ F) : ∀ a : Fin d → Fin (2*s), T (fun i => X i (a i)) := (mem_filter.mp mem).2
  have bot := lower (m:=2*s) G (by omega) (by omega) hp0 dens
  change (2:ℝ)^(-(C * ((2*s : ℕ):ℝ)^t)) ≤ (F.card:ℝ) / Fintype.card (Array d (2*s) n) at bot
  push_cast at bot
  have box : ∃ V : Fin d → Finset (Fin n), (∀ i, (V i).card=s) ∧
      ∀ x : Fin d → Fin n, (∀ i, x i∈V i) → T x := by
    by_contra hb
    have top := BadList.full_density_le (by omega : 0 < d) (by omega : 0 < n) hs hsn T F good hb
    exact (not_lt_of_ge (bot.trans top)) gap
  obtain ⟨V,size,boxV⟩ := box
  have nonempty (i) : (V i).Nonempty := Finset.card_pos.mp (by rw [size i]; omega)
  exact ⟨s,V,hs,scale,size,Erdos161Partite.cylinder_parts V (by omega) hd nonempty boxV⟩

end
end Mubayi.Solution

end

/- Records -/
section

/-! Local edge records in Theorem 1 of Dhruv Mubayi's
"Large blow-ups of uniform hypergraphs", arXiv:2611.33108v1, Section 3.
One bit for every choice of t rows and one list position in each gives a
complete description of a clique pattern. -/

namespace Erdos161Records

abbrev Scope (d t : ℕ) := ↥((Finset.univ : Finset (Fin d)).powersetCard t)
abbrev Cell (d t s : ℕ) := (I : Scope d t) × (I.1 → Fin s)

theorem scopeSize {d t : ℕ} (I : Scope d t) : I.1.card = t :=
  (Finset.mem_powersetCard.mp I.2).2

theorem card_cells (d t s : ℕ) : Fintype.card (Cell d t s) = d.choose t * s^t := by
  classical
  change Fintype.card (Σ I : Scope d t, (I.1 → Fin s)) = _
  rw [Fintype.card_sigma]
  simp [scopeSize,Scope]

variable {d t s n : ℕ}

def flag (G : Finset (Fin n) → Bool) (I : Scope d t) (v : I.1 → Fin n) : Bool :=
  decide ((Finset.univ.image v).card = t) && G (Finset.univ.image v)

def record (G : Finset (Fin n) → Bool) (L : Fin d → Fin s → Fin n) :
    Cell d t s → Bool := fun ⟨I,a⟩ => flag G I (fun i => L i.1 (a i))

noncomputable def decode (w : Cell d t s → Bool) : Finset (Fin d → Fin s) := by
  classical
  exact Finset.univ.filter (fun a => ∀ I : Scope d t, w ⟨I,fun i => a i.1⟩ = true)

def transverse (G : Finset (Fin n) → Bool) (x : Fin d → Fin n) : Prop :=
  ∀ I : Scope d t, (I.1.image x).card=t ∧ G (I.1.image x)=true

theorem cell_range (I : Scope d t) (x : Fin d → Fin n) :
    Finset.univ.image (fun i : I.1 => x i.1) = I.1.image x := by
  ext v
  simp

noncomputable def pattern (G : Finset (Fin n) → Bool) (L : Fin d → Fin s → Fin n) :
    Finset (Fin d → Fin s) := by
  classical
  exact Finset.univ.filter (fun a => transverse (t:=t) G (fun i => L i (a i)))

theorem replay (G : Finset (Fin n) → Bool) (L : Fin d → Fin s → Fin n) :
    pattern (t:=t) G L = decode (record (t:=t) G L) := by
  classical
  ext a
  simp only [pattern,decode,Finset.mem_filter,Finset.mem_univ,true_and]
  unfold transverse record flag
  have h (I : Scope d t) := cell_range I (fun i => L i (a i))
  simp only [h,Bool.and_eq_true,decide_eq_true_eq]

/-- The number of observed patterns is bounded by the number of binary records. -/
theorem pattern_count (G : Finset (Fin n) → Bool) :
    (Finset.univ.image (pattern (d:=d) (s:=s) (t:=t) G)).card ≤ 2^(d.choose t*s^t) := by
  classical
  have sub : Finset.univ.image (pattern (d:=d) (s:=s) (t:=t) G) ⊆
      Finset.univ.image (decode (d:=d) (t:=t) (s:=s)) := by
    intro S hS
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_image.mpr ⟨record G L,Finset.mem_univ _,(replay G L).symm⟩
  calc
    _ ≤ (Finset.univ.image (decode (d:=d) (t:=t) (s:=s))).card := Finset.card_le_card sub
    _ ≤ Fintype.card (Cell d t s → Bool) := Finset.card_image_le
    _ = _ := by rw [Fintype.card_fun, Fintype.card_bool, card_cells]

end Erdos161Records

end

/- Marginal -/
section

/-! Fixed-position marginals for the list experiment in Mubayi (2026), §3. -/
namespace Erdos161Sampling

variable {d s n : ℕ}

def pick (a : Fin d → Fin (s+1)) (L : Fin d → Fin (s+1) → Fin n) : Fin d → Fin n :=
  fun i => L i (a i)

def split (a : Fin d → Fin (s+1)) :
    (Fin d → Fin (s+1) → Fin n) ≃ (Fin d → Fin n) × (Fin d → Fin s → Fin n) where
  toFun L := (pick a L, fun i j => L i ((a i).succAbove j))
  invFun z := fun i => (a i).insertNth (z.1 i) (z.2 i)
  left_inv L := by
    funext i
    exact (Fin.insertNthEquiv (fun _ : Fin (s+1) => Fin n) (a i)).apply_symm_apply (L i)
  right_inv z := by
    rcases z with ⟨u,v⟩
    apply Prod.ext
    · funext i
      simp [pick]
    · funext i j
      simp

def hit_equiv (a : Fin d → Fin (s+1)) (T : Finset (Fin d → Fin n)) :
    {L : Fin d → Fin (s+1) → Fin n // pick a L ∈ T} ≃
        ↥T × (Fin d → Fin s → Fin n) := by
  let E := split (n:=n) a
  exact {
    toFun := fun L => (⟨(E L.1).1,L.2⟩,(E L.1).2)
    invFun := fun z => ⟨E.symm (z.1.1,z.2), by
      change (E (E.symm (z.1.1,z.2))).1 ∈ T
      simpa only [Equiv.apply_symm_apply] using z.1.2⟩
    left_inv := by intro L; apply Subtype.ext; exact E.symm_apply_apply _
    right_inv := by
      rintro ⟨⟨u,hu⟩,v⟩
      apply Prod.ext
      · apply Subtype.ext
        change (E (E.symm (u,v))).1 = u
        rw [Equiv.apply_symm_apply]
      · change (E (E.symm (u,v))).2 = v
        rw [Equiv.apply_symm_apply]
  }

theorem hits (a : Fin d → Fin (s+1)) (T : Finset (Fin d → Fin n)) :
    (Finset.univ.filter (fun L => pick a L ∈ T)).card =
    T.card * Fintype.card (Fin d → Fin s → Fin n) := by
  classical
  rw [← Fintype.card_coe, ← Fintype.card_coe T, ← Fintype.card_prod]
  apply Fintype.card_congr
  let e : ↥(Finset.univ.filter (fun L => pick a L ∈ T)) ≃ {L // pick a L ∈ T} :=
    Equiv.subtypeEquivRight (fun _ => by simp)
  exact e.trans (hit_equiv a T)

theorem hit_mass (nPos : 0 < n) (a : Fin d → Fin (s+1)) (T : Finset (Fin d → Fin n)) :
    ((Finset.univ.filter (fun L => pick a L ∈ T)).card : ℝ) =
      ((T.card:ℝ) / Fintype.card (Fin d → Fin n)) *
        Fintype.card (Fin d → Fin (s+1) → Fin n) := by
  have hc := Fintype.card_congr (split (n:=n) a)
  rw [Fintype.card_prod] at hc
  have h : 0 < Fintype.card (Fin d → Fin n) := by
    simpa using (pow_pos nPos d)
  rw [hits, hc]
  push_cast
  rw [← mul_assoc, div_mul_cancel₀ _ (show (Fintype.card (Fin d → Fin n) : ℝ) ≠ 0 by exact_mod_cast h.ne')]

end Erdos161Sampling

end

/- GraphSample -/
section

/-! The concrete list experiment for the clique blow-up theorem of Mubayi. -/
namespace Erdos161Lower
open Finset
open scoped Classical
noncomputable section

variable {n d m t : ℕ}

def obs (T : Finset (Fin d → Fin n)) (L : Fin d → Fin m → Fin n) :
    Finset (Fin d → Fin m) :=
  univ.filter (fun a => (fun i => L i (a i)) ∈ T)

def full (G : Finset (Fin n) → Bool) : Finset (Fin d → Fin m → Fin n) :=
  univ.filter (fun X => ∀ a : Fin d → Fin m, Erdos161Partite.Trans t G (fun i => X i (a i)))

theorem obs_eq (G : Finset (Fin n) → Bool) (L : Fin d → Fin m → Fin n) :
    obs (Erdos161Partite.transTuples t G) L = Erdos161Records.pattern (t:=t) G L := by
  ext a
  simp only [obs,Erdos161Records.pattern,Erdos161Partite.transTuples,mem_filter,mem_univ,true_and]
  rfl

theorem Q_bound (G : Finset (Fin n) → Bool) :
   (univ.image (obs (m:=m) (Erdos161Partite.transTuples (d:=d) t G))).card ≤
   2 ^ (d.choose t * m^t) := by
  simpa only [funext (obs_eq (d:=d) (m:=m) (t:=t) G)] using
    (Erdos161Records.pattern_count (s:=m) (d:=d) (t:=t) G)

theorem hit (hn : 0 < n) (hm : 0 < m) (T : Finset (Fin d → Fin n)) (a : Fin d → Fin m) :
    ((univ.filter (fun L => a ∈ obs T L)).card : ℝ) =
      ((T.card:ℝ) / Fintype.card (Fin d → Fin n)) *
        Fintype.card (Fin d → Fin m → Fin n) := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have sets : (univ.filter (fun L => a ∈ obs T L)) =
      (univ.filter (fun L => Erdos161Sampling.pick a L ∈ T)) := by
    ext L
    simp only [obs,mem_filter,mem_univ,true_and]
    rfl
  rw [sets]
  exact Erdos161Sampling.hit_mass hn a T

theorem mass_ge (hn : 0 < n) {p0 : ℝ} (T : Finset (Fin d → Fin n))
    (hT : p0*(n:ℝ)^d ≤ (T.card:ℝ)) :
    p0 ≤ (T.card:ℝ) / Fintype.card (Fin d → Fin n) := by
  have hp : 0 < (n:ℝ)^d := pow_pos (by exact_mod_cast hn) _
  simpa using (le_div_iff₀ hp).mpr hT

end
end Erdos161Lower

end

/- Loss -/
section

/-! The finite pattern count in Mubayi's Lemma 4 controls the exponential loss
by a constant depending only on the fixed density, uniformity, and number of parts. -/
namespace OMA.PatternEntropy

/-- If at most one binary choice is recorded for each of `choose d t * s^t` cells,
the lower bound on the full-pattern density is at least the stated base-two power. -/
theorem dyadic_loss (d t s : ℕ) (p₀ p Q : ℝ) (hp₀ : 0 < p₀) (hpp : p₀ ≤ p)
    (hq : 1 ≤ Q) (hqmax : Q ≤ (2 : ℝ) ^ (d.choose t * s^t)) :
    (2 : ℝ) ^ (-(max 1 ((d.choose t : ℝ) / p₀) * (s : ℝ)^t)) ≤ Q ^ (-(1:ℝ)/p) := by
  have hp := hp₀.trans_le hpp
  have he : -(1:ℝ)/p < 0 := div_neg_of_neg_of_pos (by norm_num) hp
  have base : 0 < (2 : ℝ) ^ (d.choose t * s^t) := by positivity
  have step := (Real.rpow_le_rpow_iff_of_neg base (lt_of_lt_of_le zero_lt_one hq) he).mpr hqmax
  refine le_trans ?_ step
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have ratio := (div_le_div_of_nonneg_left (Nat.cast_nonneg (d.choose t) : (0:ℝ) ≤ _) hp₀ hpp).trans
    (le_max_right 1 ((d.choose t : ℝ)/p₀))
  have scaled := mul_le_mul_of_nonneg_right ratio (pow_nonneg (Nat.cast_nonneg s : (0:ℝ) ≤ _) t)
  push_cast
  calc
    _ ≤ -(((d.choose t : ℝ) / p) * (s:ℝ)^t) := neg_le_neg scaled
    _ = _ := by ring

end OMA.PatternEntropy

end

/- CopyGrid -/
section

namespace Erdos161Cube

abbrev Grid (h s : ℕ) := Fin h → Fin s

/-- Copy the `u`-slice in coordinate `i` into every slice of the same coordinate. -/
def copy {h s : ℕ} (i : Fin h) (u : Fin s) (J : Finset (Grid h s)) : Finset (Grid h s) :=
  Finset.univ.filter (fun a => Function.update a i u ∈ J)

@[simp] theorem mem_copy {h s : ℕ} (i : Fin h) (u : Fin s) (J : Finset (Grid h s)) (a : Grid h s) :
    a∈copy i u J ↔ Function.update a i u∈J := by simp [copy]

end Erdos161Cube

end

/- CopyIteration -/
section

/-! Iterating coordinate copying, as in equation (12) of Dhruv Mubayi,
“Large blow-ups of uniform hypergraphs” (arXiv:2611.33108).
The proof works directly with integer powers and includes all zero parameters. -/
namespace Erdos161Cube

/-- Patch the coordinates in the supplied itinerary. Earlier positions take precedence
    when an itinerary contains the same coordinate twice. -/
private def patch {h s : ℕ} : {m : ℕ} → (Fin m → Fin h) → (Fin m → Fin s) → Grid h s → Grid h s
  | 0, _, _, a => a
  | _+1, I, z, a => Function.update (patch (Fin.tail I) (Fin.tail z) a) (I 0) (z 0)

private def copied {h s m : ℕ} (I : Fin m → Fin h) (z : Fin m → Fin s) (J : Finset (Grid h s)) :=
  Finset.univ.filter (fun a => patch I z a ∈ J)

private theorem patch_own {h s m : ℕ} (I : Fin m → Fin h) (inj : Function.Injective I)
    (z : Fin m → Fin s) (a : Grid h s) (t : Fin m) : patch I z a (I t) = z t := by
  induction m with
  | zero => exact t.elim0
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) t
    · simp [patch]
    · have diff : I j.succ ≠ I 0 := fun eq => Fin.succ_ne_zero j (inj eq)
      change Function.update (patch (Fin.tail I) (Fin.tail z) a) (I 0) (z 0) (I j.succ) = _
      rw [Function.update_of_ne diff]
      exact ih (Fin.tail I) (inj.comp (Fin.succ_injective m)) (Fin.tail z) j

private theorem copied_zero {h s : ℕ} (I : Fin 0 → Fin h) (z : Fin 0 → Fin s) (J : Finset (Grid h s)) :
    copied I z J = J := by
  ext a
  exact (Finset.mem_filter.trans (and_iff_right (Finset.mem_univ a)))

private theorem copied_cons {h s m : ℕ} (I : Fin (m+1) → Fin h) (u : Fin s) (v : Fin m → Fin s)
    (J : Finset (Grid h s)) :
    copied (Fin.tail I) v (copy (I 0) u J) = copied I (Fin.cons u v) J := by
  ext a
  simp [copied,patch]

private theorem copied_all {h s : ℕ} (z : Grid h s) (J : Finset (Grid h s)) :
    copied id z J = if z ∈ J then Finset.univ else ∅ := by
  have all (a : Grid h s) : patch id z a=z := funext (fun t => patch_own id Function.injective_id z a t)
  by_cases mem : z ∈ J <;> ext a <;> simp [copied,all,mem]

private theorem iterate {h s : ℕ} (rho : Finset (Grid h s) → ℝ) (nonneg : ∀ J, 0≤rho J)
    (step : ∀ J i, rho J ^ s ≤ ∏ u, rho (copy i u J))
    (m : ℕ) (I : Fin m → Fin h) (J : Finset (Grid h s)) :
    rho J ^ (s^m) ≤ ∏ z : Fin m → Fin s, rho (copied I z J) := by
  induction m generalizing J with
  | zero => simp [copied_zero]
  | succ m ih =>
    let F : (Fin (m+1) → Fin s) → ℝ := fun z => rho (copied I z J)
    have uniform (u : Fin s) := ih (Fin.tail I) (copy (I 0) u J)
    calc
      rho J ^ (s^(m+1)) = (rho J ^ s)^(s^m) := by rw [pow_succ',pow_mul]
      _ ≤ (∏ u, rho (copy (I 0) u J))^(s^m) :=
        pow_le_pow_left₀ (pow_nonneg (nonneg J) _) (step J (I 0)) _
      _ = ∏ u, rho (copy (I 0) u J)^(s^m) := by rw [Finset.prod_pow]
      _ ≤ ∏ u, ∏ v, rho (copied (Fin.tail I) v (copy (I 0) u J)) :=
        Finset.prod_le_prod (fun u _ => pow_nonneg (nonneg _) _) (fun u _ => uniform u)
      _ = ∏ u, ∏ v, F (Fin.cons u v) := by simp only [F,copied_cons]
      _ = ∏ z, F z := by
        rw [← Fintype.prod_prod_type']
        exact (Fin.consEquiv (fun _ : Fin (m+1) => Fin s)).prod_comp F

/-- After all h coordinates have been copied exactly |J| leaves are the full grid;
    the other leaves are the empty grid. This is the integer-power form of (12). -/
theorem full_bound {h s : ℕ} (rho : Finset (Grid h s) → ℝ) (nonneg : ∀ J, 0≤rho J)
    (empty : rho ∅=1) (step : ∀ J i, rho J ^ s ≤ ∏ u, rho (copy i u J))
    (J : Finset (Grid h s)) : rho J ^ (s^h) ≤ rho Finset.univ ^ J.card := by
  calc
    _ ≤ ∏ z : Grid h s, rho (copied id z J) := iterate rho nonneg step h id J
    _ = ∏ z : Grid h s, (if z∈J then rho Finset.univ else 1) := by
      apply Finset.prod_congr rfl
      intro z _
      rw [copied_all]
      split <;> simp_all
    _ = _ := by simp

end Erdos161Cube

end

/- PowerRoot -/
section

namespace Erdos161Cube

/-- Taking the positive grid-size root in the iterated coordinate-copy inequality. -/
theorem density_root {h s : ℕ} (hs : 0 < s) (rho : Finset (Grid h s) → ℝ)
    (nonneg : ∀ J, 0≤rho J) (empty : rho ∅=1)
    (step : ∀ J i, rho J ^ s ≤ ∏ u, rho (copy i u J)) (J : Finset (Grid h s)) :
    rho J ≤ (rho Finset.univ)^((J.card : ℝ)/(Fintype.card (Grid h s) : ℝ)) := by
  have hcard : Fintype.card (Grid h s)=s^h := by simp [Grid]
  rw [hcard]
  have hn : (0:ℝ) < (s^h : ℕ) := by exact_mod_cast pow_pos hs h
  apply (Real.rpow_le_rpow_iff (nonneg J) (Real.rpow_nonneg (nonneg _) _) hn).mp
  rw [Real.rpow_natCast,← Real.rpow_mul (nonneg _),div_mul_cancel₀ _ hn.ne',Real.rpow_natCast]
  exact full_bound rho nonneg empty step J

end Erdos161Cube

end

/- PatternEntropy -/
section

/-! The last averaging step in Dhruv Mubayi, arXiv:2611.33108v1, Lemma 4. -/
namespace OMA.PatternEntropy
open Finset Real

/-- A finite distribution of observed pattern types. Its weights sum to one, its exponents
average to a positive density, and the mass of each type is bounded by its containment density. -/
theorem full_density {ι : Type*} (S : Finset ι) (w a ρ : ι → ℝ) (F p Q : ℝ)
    (w0 : ∀ j ∈ S, 0 ≤ w j) (w1 : ∑ j ∈ S, w j = 1)
    (mean : ∑ j ∈ S, w j * a j = p) (hp : 0 < p) (hF : 0 ≤ F)
    (exact_le : ∀ j ∈ S, w j ≤ ρ j) (copy : ∀ j ∈ S, ρ j ≤ F ^ a j)
    (hQ : (S.card : ℝ) ≤ Q) :
    Q ^ (-(1:ℝ) / p) ≤ F := by
  have Fpos : 0 < F := by
    by_contra! h
    have z : F = 0 := le_antisymm h hF
    have hz (j) (hj : j ∈ S) : w j * a j = 0 := by
      by_cases ha : a j = 0
      · simp [ha]
      · have e := (exact_le j hj).trans (copy j hj)
        rw [z, Real.zero_rpow ha] at e
        rw [le_antisymm e (w0 j hj), zero_mul]
    have mean0 : ∑ j ∈ S, w j * a j = 0 := Finset.sum_eq_zero hz
    linarith
  have jensen := convexOn_exp.map_sum_le w0 w1
    (fun j _ => Set.mem_univ (-(Real.log F * a j)))
  simp only [smul_eq_mul] at jensen
  have sum_eq : ∑ j ∈ S, w j * -(Real.log F * a j) = -(Real.log F * p) := by
    rw [← mean, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [sum_eq] at jensen
  have term (j) (hj : j ∈ S) : w j * Real.exp (-(Real.log F * a j)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right ((exact_le j hj).trans (copy j hj))
      (Real.exp_pos (-(Real.log F * a j))).le
    simpa only [Real.rpow_def_of_pos Fpos, ← Real.exp_add, add_neg_cancel, Real.exp_zero] using h
  have cap : Real.exp (-(Real.log F * p)) ≤ Q := by
    calc
      Real.exp (-(Real.log F * p)) ≤ _ := jensen
      _ ≤ ∑ _j ∈ S, (1:ℝ) := Finset.sum_le_sum term
      _ ≤ Q := by simpa using hQ
  have Qpos := (Real.exp_pos _).trans_le cap
  have log_ineq := (Real.le_log_iff_exp_le Qpos).mpr cap
  rw [Real.rpow_def_of_pos Qpos, ← Real.exp_log Fpos]
  apply Real.exp_le_exp.mpr
  rw [mul_div_assoc', div_le_iff₀ hp]
  linarith


/-- Frequency among a uniform finite sample. -/
noncomputable def freq {X Γ : Type*} [Fintype X] [DecidableEq Γ] (obs : X → Finset Γ)
    (J : Finset Γ) : ℝ := ((Finset.univ.filter (fun x => obs x = J)).card : ℝ) / Fintype.card X

/-- Density of samples in which every specified position occurs. -/
noncomputable def containsDensity {X Γ : Type*} [Fintype X] [DecidableEq Γ] (obs : X → Finset Γ)
    (J : Finset Γ) : ℝ := ((Finset.univ.filter (fun x => J ⊆ obs x)).card : ℝ) / Fintype.card X

theorem empirical_sum {X Γ : Type*} [Fintype X] [DecidableEq Γ] (obs : X → Finset Γ)
    (g : Finset Γ → ℝ) :
    ∑ J ∈ Finset.univ.image obs, freq obs J * g J = (∑ x, g (obs x)) / Fintype.card X := by
  classical
  calc
    _ = ∑ J ∈ Finset.univ.image obs,
          (∑ _x ∈ Finset.univ.filter (fun x => obs x = J), g J) / Fintype.card X := by
      apply Finset.sum_congr rfl
      intro J hJ
      simp only [freq, Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := by
      rw [← Finset.sum_div]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to' (fun x hx => Finset.mem_image_of_mem obs hx) g

theorem observed_density {X Γ : Type*} [Fintype X] [Nonempty X] [Fintype Γ] [Nonempty Γ]
    [DecidableEq Γ] (obs : X → Finset Γ) (p Q : ℝ) (hp : 0 < p)
    (hits : ∀ g : Γ, ((Finset.univ.filter (fun x => g ∈ obs x)).card : ℝ) =
        p * Fintype.card X)
    (copy : ∀ J ∈ Finset.univ.image obs, containsDensity obs J ≤
        containsDensity obs Finset.univ ^ ((J.card : ℝ) / Fintype.card Γ))
    (hQ : ((Finset.univ.image obs).card : ℝ) ≤ Q) :
    Q ^ (-(1:ℝ) / p) ≤ containsDensity obs Finset.univ := by
  classical
  have nx : (0:ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have ng : (0:ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos
  apply full_density (Finset.univ.image obs) (freq obs) (fun J => (J.card : ℝ) / Fintype.card Γ)
    (containsDensity obs) _ p Q
  · intro J _
    exact div_nonneg (Nat.cast_nonneg _) nx.le
  · simpa [nx.ne'] using empirical_sum obs (fun _ => (1:ℝ))
  · rw [empirical_sum, ← Finset.sum_div]
    have counts : (∑ x : X, ((obs x).card : ℝ)) =
        ∑ g : Γ, ((Finset.univ.filter (fun x => g ∈ obs x)).card : ℝ) := by
      calc
        _ = ∑ x : X, ∑ g : Γ, if g ∈ obs x then (1:ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← Finset.sum_filter]
          simp
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro g _
          rw [← Finset.sum_filter]
          simp
    simp only [counts, hits, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · exact hp
  · exact div_nonneg (Nat.cast_nonneg _) nx.le
  · intro J _
    apply div_le_div_of_nonneg_right _ nx.le
    exact_mod_cast Finset.card_le_card (show
      (Finset.univ.filter (fun x => obs x = J)) ⊆ Finset.univ.filter (fun x => J ⊆ obs x) from by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hx).2.symm).subset⟩)
  · exact copy
  · exact hQ

end OMA.PatternEntropy

end

/- CubeEntropy -/
section

/-! Mubayi, “Large blow-ups of uniform hypergraphs”, arXiv:2611.33108v1,
Lemma 4 (11). Iterated coordinate copying and empirical pattern entropy. -/
namespace Erdos161Cube
open Finset OMA.PatternEntropy

/-- Conditional on the per-axis Hölder bound, the uniform one-position marginals, and
    the count of distinct patterns, the probability that all transversals hit is large. -/
theorem empirical_cube_lower {X : Type*} [Fintype X] [Nonempty X] {h s : ℕ} (hs : 0 < s)
    (obs : X → Finset (Grid h s)) (p Q : ℝ) (hp : 0 < p)
    (hits : ∀ g : Grid h s, ((univ.filter (fun x => g∈obs x)).card : ℝ) = p * Fintype.card X)
    (step : ∀ J i, containsDensity obs J ^ s ≤ ∏ u, containsDensity obs (copy i u J))
    (hQ : ((univ.image obs).card : ℝ) ≤ Q) :
    Q ^ (-(1:ℝ)/p) ≤ containsDensity obs univ := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  apply observed_density obs p Q hp hits _ hQ
  intro J _
  have denom : (Fintype.card X:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact density_root hs (containsDensity obs) (fun K => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (by simp [containsDensity,denom]) step J

end Erdos161Cube

end

/- PatternCount -/
section

/-! Complete-list factorization for Mubayi, arXiv:2611.33108v1, Lemma 4. -/
namespace Erdos161Holder

open Finset Erdos161Cube

abbrev Lists (h s N : ℕ) := Fin h → Fin s → Fin N

def fits {h s N : ℕ} (T : Finset (Fin h → Fin N)) (J : Finset (Grid h s))
    (X : Lists h s N) : Prop := ∀ a ∈ J, (fun j => X j (a j)) ∈ T

noncomputable def count {h s N : ℕ} (T : Finset (Fin h → Fin N)) (J : Finset (Grid h s)) : ℕ := by
  classical
  exact (Finset.univ.filter (fits T J)).card

noncomputable def rho {h s N : ℕ} (T : Finset (Fin h → Fin N)) (J : Finset (Grid h s)) : ℝ :=
  (count T J : ℝ) / (Fintype.card (Lists h s N) : ℝ)

abbrev Outside {h : ℕ} (i : Fin h) (s N : ℕ) := {j : Fin h // j≠i} → Fin s → Fin N

def plug {h s N : ℕ} {i : Fin h} (Y : Outside i s N) (v : Fin N) (a : Grid h s) (j : Fin h) : Fin N :=
  if hj : j=i then v else Y ⟨j,hj⟩ (a j)

private theorem plug_update {h s N : ℕ} {i : Fin h} (Y : Outside i s N)
    (v : Fin N) (a : Grid h s) (u : Fin s) :
    plug Y v (Function.update a i u) = plug Y v a := by
  funext j
  by_cases hj : j=i <;> simp [plug,hj, Function.update_of_ne]

noncomputable def link {h s N : ℕ} (T : Finset (Fin h → Fin N)) (J : Finset (Grid h s))
    (i : Fin h) (Y : Outside i s N) (u : Fin s) : Finset (Fin N) := by
  classical
  exact univ.filter (fun v => ∀ a ∈ J, a i=u → plug Y v a ∈ T)

private theorem mem_link {h s N : ℕ} (T : Finset (Fin h → Fin N)) (J : Finset (Grid h s))
    (i : Fin h) (Y : Outside i s N) (u : Fin s) (v : Fin N) :
    v ∈ link T J i Y u ↔ ∀ a ∈ J, a i=u → plug Y v a ∈ T := by
  classical
  simp [link]

private theorem eval_plug {h s N : ℕ} (i : Fin h) (X : Lists h s N) (a : Grid h s) :
    plug (i := i) (fun j => X j.val) (X i (a i)) a = (fun j => X j (a j)) := by
  funext j
  by_cases hj : j=i <;> simp [plug,hj]

theorem fits_iff {h s N : ℕ} (T : Finset (Fin h → Fin N)) (J : Finset (Grid h s))
    (i : Fin h) (X : Lists h s N) :
    fits T J X ↔ X i ∈ Fintype.piFinset (link T J i (fun j => X j.val)) := by
  classical
  rw [Fintype.mem_piFinset]
  constructor
  · intro good u
    apply (mem_link ..).mpr
    intro a ha hua
    rw [← hua,eval_plug]
    exact good a ha
  · intro good a ha
    rw [← eval_plug i X a]
    exact (mem_link ..).mp (good (a i)) a ha rfl

theorem count_factors {h s N : ℕ} (T : Finset (Fin h → Fin N)) (J : Finset (Grid h s)) (i : Fin h) :
    count T J = ∑ Y : Outside i s N, ∏ u, (link T J i Y u).card := by
  classical
  let e := Equiv.funSplitAt i (Fin s → Fin N)
  let q (p : (Fin s → Fin N) × Outside i s N) : ℕ :=
    if p.1 ∈ Fintype.piFinset (link T J i p.2) then 1 else 0
  rw [count,Finset.card_filter]
  calc
    _ = ∑ p, q p := Fintype.sum_equiv e _ q (fun X => by
      change (if fits T J X then 1 else 0) = if X i ∈ Fintype.piFinset _ then 1 else 0
      rw [fits_iff T J i]
      split <;> split <;> first | rfl | contradiction)
    _ = _ := by
      rw [Fintype.sum_prod_type_right]
      apply Finset.sum_congr rfl
      intro Y _
      change (∑ f, if f ∈ Fintype.piFinset (link T J i Y) then 1 else 0) = _
      rw [← Finset.card_filter]
      have heq : (Finset.univ.filter (fun f => f ∈ Fintype.piFinset (link T J i Y))) =
          Fintype.piFinset (link T J i Y) := by
        ext f
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rw [heq,Fintype.card_piFinset]

/-- Copying one link makes every slot have the same admissible vertex set. -/
theorem link_copy {h s N : ℕ} (T : Finset (Fin h → Fin N)) (J : Finset (Grid h s))
    (i : Fin h) (Y : Outside i s N) (u k : Fin s) :
    link T (copy i u J) i Y k = link T J i Y u := by
  classical
  ext v
  rw [mem_link,mem_link]
  constructor
  · intro good a ha hai
    let b := Function.update a i k
    have hbu : Function.update b i u = a := by
      funext j
      by_cases hji : j=i <;> simp_all [b,Function.update_of_ne]
    have hb : b ∈ copy i u J := (mem_copy ..).mpr (hbu ▸ ha)
    simpa only [b,plug_update] using good b hb (Function.update_self ..)
  · intro good a ha _
    have hm := (mem_copy ..).mp ha
    simpa only [plug_update] using good (Function.update a i u) hm (Function.update_self ..)

theorem copy_count {h s N : ℕ} (T : Finset (Fin h → Fin N)) (J : Finset (Grid h s))
    (i : Fin h) (u : Fin s) :
    count T (copy i u J) = ∑ Y : Outside i s N, (link T J i Y u).card ^ s := by
  rw [count_factors T _ i]
  simp only [link_copy,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end Erdos161Holder

end

/- Observation -/
section

/-! The full-list density bound from Lemma 4 of Dhruv Mubayi,
“Large blow-ups of uniform hypergraphs” (arXiv:2611.33108v1). -/
namespace Erdos161Cube
open Finset OMA.PatternEntropy Erdos161Holder

/-- The observed pattern of one list array for a given family of good transversals. -/
noncomputable def obs {d s N : ℕ} (T : Finset (Fin d → Fin N)) (X : Lists d s N) : Finset (Grid d s) := by
  classical
  exact univ.filter (fun a => (fun i => X i (a i))∈T)

@[simp] theorem mem_obs {d s N : ℕ} (T : Finset (Fin d → Fin N)) (X : Lists d s N)
    (a : Grid d s) : a∈obs T X ↔ (fun i => X i (a i))∈T := by classical simp [obs]

/-- The sample-space containment density is precisely the normalized Hölder count. -/
theorem contains_eq_rho {d s N : ℕ} (T : Finset (Fin d → Fin N)) (J : Finset (Grid d s)) :
    containsDensity (obs T) J = rho T J := by
  classical
  have fin : univ.filter (fun X : Lists d s N => J ⊆ obs T X) = univ.filter (fits T J) := by
    ext X
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro sub a ha
      exact (mem_obs ..).mp (sub ha)
    · intro fit a ha
      exact (mem_obs ..).mpr (fit a ha)
  unfold containsDensity rho count
  rw [fin]


end Erdos161Cube

end

/- FiniteHolder -/
section

/-! Equal-exponent finite Hölder, in the form used in Mubayi,
arXiv:2611.33108v1, Lemma 4, for nonnegative completion counts. -/
namespace Erdos161Holder

open Finset

theorem finite_holder {s : ℕ} (hs : 0 < s) {Y : Type*} [Fintype Y]
    (d : Fin s → Y → ℝ) (hd : ∀ u y, 0 ≤ d u y) :
    (∑ y, ∏ u, d u y)^s ≤ ∏ u, ∑ y, (d u y)^s := by
  classical
  let c (u : Fin s) : ℝ := ∑ y, (d u y)^s
  have hc (u) : 0 ≤ c u := sum_nonneg (fun y _ => pow_nonneg (hd u y) _)
  by_cases allpos : ∀ u, 0 < c u
  · let e : ℝ := (s : ℝ)⁻¹
    let D (u : Fin s) := (c u)^e
    let g (u : Fin s) (y : Y) := d u y / D u
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    have he : 0 ≤ e := by dsimp [e]; positivity
    have hD (u) : 0 < D u := Real.rpow_pos_of_pos (allpos u) _
    have hg (u y) : 0 ≤ g u y := div_nonneg (hd u y) (hD u).le
    have hDs (u) : D u ^ s = c u := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hc u)]
      simp [e,hs']
    have hnorm (u) : ∑ y, (g u y)^s = 1 := by
      simp only [g,div_pow,hDs,← Finset.sum_div]
      exact div_self (allpos u).ne'
    have heone : ∑ _u : Fin s, e = 1 := by simp [e,hs']
    have root (x : ℝ) (hx : 0 ≤ x) : (x^s)^e = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
      simp [e,hs']
    have ham (y) : (∏ u, g u y) ≤ ∑ u, e*(g u y)^s := by
      have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : Fin s => e)
        (fun u => (g u y)^s) (fun _ _ => he) heone (fun u _ => pow_nonneg (hg u y) _)
      simpa only [root _ (hg _ _)] using h
    have hgsum : (∑ y, ∏ u, g u y) ≤ 1 := by
      calc
        _ ≤ ∑ y, ∑ u, e*(g u y)^s := sum_le_sum fun y _ => ham y
        _ = 1 := by rw [Finset.sum_comm]; simp only [← Finset.mul_sum,hnorm,mul_one]; exact heone
    have factor (u y) : d u y = g u y * D u := by simp [g,(hD u).ne']
    have hsum : (∑ y, ∏ u, d u y) ≤ ∏ u, D u := by
      calc
        _ = (∑ y, ∏ u, g u y)*(∏ u, D u) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro y _
          conv_lhs => arg 2; ext u; rw [factor u y]
          exact Finset.prod_mul_distrib
        _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hgsum (prod_nonneg (fun u _ => (hD u).le))
    calc
      _ ≤ (∏ u, D u)^s := pow_le_pow_left₀ (sum_nonneg (fun y _ => prod_nonneg (fun u _ => hd u y))) hsum _
      _ = _ := by rw [← Finset.prod_pow]; simp only [hDs,c]
  · push Not at allpos
    obtain ⟨u,hu⟩ := allpos
    have hcu : c u = 0 := le_antisymm hu (hc u)
    have hz (y : Y) : d u y = 0 := by
      have hpow := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => pow_nonneg (hd u i) s)).mp hcu y
        (Finset.mem_univ _)
      by_contra hne
      exact pow_ne_zero s hne hpow
    have hp (y : Y) : (∏ v, d v y) = 0 := prod_eq_zero (mem_univ u) (hz y)
    simp only [hp,Finset.sum_const_zero,zero_pow hs.ne']
    exact prod_nonneg (fun v _ => hc v)

end Erdos161Holder

end

/- RhoCopy -/
section

namespace Erdos161Holder
open Erdos161Cube Finset

theorem rho_nonneg {h s N : ℕ} (T : Finset (Fin h → Fin N)) (J : Finset (Grid h s)) :
    0 ≤ rho T J := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem rho_empty {h s N : ℕ} (hN : 0 < N) (T : Finset (Fin h → Fin N)) :
    rho (s:=s) T ∅=1 := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have den : (Fintype.card (Lists h s N) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have fc : (Finset.univ.filter (fits T (∅ : Finset (Grid h s)))) = Finset.univ := by
    ext x
    simp [fits]
  simp only [rho,count,fc,Finset.card_univ,div_self den]

/-- Hölder on the nonnegative link counts; all lists have the same denominator. -/
theorem rho_copy {h s N : ℕ} (hs : 0 < s) (T : Finset (Fin h → Fin N))
    (J : Finset (Grid h s)) (i : Fin h) : rho T J ^ s ≤ ∏ u, rho T (copy i u J) := by
  classical
  have raw : count T J ^ s ≤ ∏ u, count T (copy i u J) := by
    simp_rw [copy_count T J i]
    rw [count_factors T J i]
    exact_mod_cast finite_holder hs (fun u Y => ((link T J i Y u).card : ℝ)) (fun _ _ => Nat.cast_nonneg _)
  have raw' : (count T J : ℝ)^s ≤ ∏ u, (count T (copy i u J) : ℝ) := by exact_mod_cast raw
  unfold rho
  rw [div_pow,Finset.prod_div_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact div_le_div_of_nonneg_right raw' (pow_nonneg (Nat.cast_nonneg _) _)

end Erdos161Holder

end

/- ListLower -/
section

namespace Erdos161Cube
open Finset OMA.PatternEntropy Erdos161Holder

/-- The probability that all transversals are good is at least Q^(-1/p). The one-cell
    marginals and number of distinct records are the only data needed from the host graph. -/
theorem list_cube_lower {d m N : ℕ} (hm : 0 < m) (hN : 0 < N) (T : Finset (Fin d → Fin N))
    (p Q : ℝ) (hp : 0 < p)
    (hits : ∀ a : Grid d m, ((univ.filter (fun X : Lists d m N => a∈obs T X)).card : ℝ) =
       p*Fintype.card (Lists d m N))
    (hQ : ((univ.image (obs (s:=m) T)).card:ℝ) ≤ Q) :
    Q^(-(1:ℝ)/p) ≤ rho T (univ : Finset (Grid d m)) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  rw [← contains_eq_rho]
  apply empirical_cube_lower hm (obs T) p Q hp hits _ hQ
  intro J i
  simp only [contains_eq_rho]
  exact rho_copy hm T J i

end Erdos161Cube

end

/- Lower -/
section

/-! Concrete full-pattern density bound in Theorem 1 of Dhruv Mubayi,
arXiv:2611.33108v1, specialised to the exact clique predicate in #3566. -/
namespace Erdos161Lower
open Finset
open scoped Classical
noncomputable section

theorem full_density_eq {n d t m : ℕ} (G : Finset (Fin n) → Bool) :
    Erdos161Holder.rho (Erdos161Partite.transTuples t G) (univ : Finset (Erdos161Cube.Grid d m)) =
      ((univ.filter (fun X : Fin d → Fin m → Fin n =>
        ∀ a : Fin d → Fin m, Erdos161Partite.Trans t G (fun i => X i (a i)))).card:ℝ) /
        Fintype.card (Fin d → Fin m → Fin n) := by
  unfold Erdos161Holder.rho Erdos161Holder.count
  congr 2
  apply congrArg Finset.card
  ext X
  constructor
  · intro h
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro a
    exact (mem_filter.mp ((mem_filter.mp h).2 a (mem_univ a))).2
  · intro h
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro a _
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2 a⟩

theorem lower_full_dense {n d t m : ℕ} (G : Finset (Fin n) → Bool) (hn : 0 < n) (hm : 0 < m)
    {p0 : ℝ} (hp0 : 0 < p0)
    (hT : p0*(n:ℝ)^d ≤ ((Erdos161Partite.transTuples (d:=d) t G).card:ℝ)) :
    (2:ℝ)^(-(max 1 ((d.choose t : ℝ)/p0) * (m:ℝ)^t)) ≤
      ((univ.filter (fun X : Fin d → Fin m → Fin n =>
        ∀ a : Fin d → Fin m, Erdos161Partite.Trans t G (fun i => X i (a i)))).card:ℝ) /
         Fintype.card (Fin d → Fin m → Fin n) := by
  let T := Erdos161Partite.transTuples (d:=d) t G
  let p : ℝ := (T.card:ℝ)/Fintype.card (Fin d → Fin n)
  let Q : ℝ := (2:ℝ)^(d.choose t*m^t)
  have lower : p0 ≤ p := mass_ge hn T hT
  have hQ : ((univ.image (Erdos161Cube.obs (s:=m) T)).card:ℝ) ≤ Q := by
    change ((univ.image (obs (m:=m) T)).card:ℝ) ≤ (2:ℝ)^(d.choose t*m^t)
    exact_mod_cast Q_bound (d:=d) (m:=m) (t:=t) G
  have h1Q : 1 ≤ Q := one_le_pow₀ (by norm_num : 1 ≤ (2:ℝ))
  apply (OMA.PatternEntropy.dyadic_loss d t m p0 p Q hp0 lower h1Q le_rfl).trans
  rw [← full_density_eq]
  apply Erdos161Cube.list_cube_lower hm hn T p Q (hp0.trans_le lower) _ hQ
  intro a
  exact hit hn hm T a

end
end Erdos161Lower

end

/- Main -/
section

/-- Formalization of Theorem 1 of Dhruv Mubayi, *Large blow-ups of uniform
hypergraphs*, arXiv:2611.33108v1 (24 November 2026), CC BY 4.0. The finite
list proof uses one ground set, explicit injectivity of transversal cliques,
and an elementary bound for deficient rows. -/
theorem OMA.solution : OMA.R_Erdos161_erdos_161_parts_ii_R1_H2_R1.H2 :=
  Mubayi.Solution.assemble (@Erdos161Lower.lower_full_dense)

end
