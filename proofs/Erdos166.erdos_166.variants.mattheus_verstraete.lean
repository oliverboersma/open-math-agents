import FormalConjectures.ErdosProblems.«166»

/-!
# Proof of Erdős Problem 166 (`Mattheus–Verstraëte 2024`)

We prove the Mattheus–Verstraëte lower bound
`R(4, k) ≥ C * k^3 / (log k)^4` for all sufficiently large `k`:

1. **Hermitian Unital & Base Graph `H_q`**: Over `Fq2 q = GaloisField q 2`, the Hermitian unital
   `Unital q` (`q^3 + 1` points) and its secants `Secant q` (`n = q^2 (q^2 - q + 1)` lines) form
   a Steiner `(q + 1)`-tuple system free of O'Nan configurations (via a `3 × 3` skew-symmetric Gram
   determinant). Hence every `K_4` in the secant intersection graph `H_q` puts at least `3`
   vertices into a single point-clique `C_p`, so replacing every clique `C_p` by any complete
   bipartite graph yields a `K_4`-free graph `bipGraph D col`.
2. **Clique Structure & Concentration**: Abstracting the unital into `UnitalData q`, for any vertex
   set `X` of size `m = 2^24 q^2`, Cauchy–Schwarz bounds the large cliques (`|X ∩ C_p| > √(2m)`)
   by `v(L) ≤ 2m`, forcing either small cliques (`≤ √(2m)/log n`) to carry `≥ m^2 / (64q)` edges
   or medium cliques to carry `≥ q m^(3/2) / (16 (log n)^2)` edges. A self-contained finite-hypercube
   McDiarmid inequality yields `col` such that every `X` with `|X| ≥ m` induces at least
   `|X|^2 / (128 q)` directed edges in `bipGraph D col`.
3. **Kleitman–Winston Containers & Vertex Sampling**: A deterministic max-degree fingerprint
   recursion bounds the number of independent sets of size `t = ⌈2^30 q (log q)^2⌉` by
   `(q / (log q)^2)^t`. Weighted finite-subset sampling with `p = (log q)^2 / q` and alteration
   produces a `K_4`-free induced subgraph on `≥ q^3 (log q)^2 / 2` vertices with no independent
   set of size `t`. Bertrand's postulate then yields `R(4, k) ≥ C k^3 / (log k)^4`.
-/

-- Problem: Erdős Problem 166 — mattheus verstraete
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/166.lean:65 (declaration Erdos166.erdos_166.variants.mattheus_verstraete)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos166MV

open Filter Finset BigOperators

open scoped Classical

/- Helper for `SimpleGraph.Copy` construction and `choose ≤ pow` in `ℕ` -/

private def mkCopy {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (f : α → β) (hinj : Function.Injective f) (hmap : ∀ {a b}, G.Adj a b → H.Adj (f a) (f b)) :
    G.Copy H :=
  ⟨⟨f, hmap⟩, hinj⟩

private lemma nat_choose_le_pow (n k : ℕ) : n.choose k ≤ n ^ k := by
  have h1 : k.factorial * n.choose k = n.descFactorial k :=
    (Nat.descFactorial_eq_factorial_mul_choose n k).symm
  have h2 : n.descFactorial k ≤ n ^ k := Nat.descFactorial_le_pow n k
  have h3 : 1 ≤ k.factorial := Nat.factorial_pos k
  exact le_trans (Nat.le_mul_of_pos_left _ h3) (h1.le.trans h2)

/- Abstract combinatorial interface for the Hermitian unital partial linear space -/

private def bipGraphOf {U W : Type*} (inc : U → W → Prop) (col : U × W → Bool) :
    SimpleGraph W where
  Adj u v := u ≠ v ∧ ∃ p : U, inc p u ∧ inc p v ∧ col (p, u) ≠ col (p, v)
  symm := ⟨fun _ _ ⟨hne, p, hu, hv, hc⟩ => ⟨hne.symm, p, hv, hu, hc.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private structure UnitalData (q : ℕ) where
  U : Type
  W : Type
  instFinU : Fintype U
  instFinW : Fintype W
  inc : U → W → Prop
  cardU : @Fintype.card U instFinU = q ^ 3 + 1
  cardW : @Fintype.card W instFinW = q ^ 2 * (q ^ 2 - q + 1)
  secantPts : ∀ w : W, (@Finset.univ U instFinU |>.filter (fun p => inc p w)).card = q + 1
  uniqueSecant : ∀ {p₁ p₂ : U}, p₁ ≠ p₂ → ∃! w : W, inc p₁ w ∧ inc p₂ w
  uniqueUnital : ∀ {w₁ w₂ : W}, w₁ ≠ w₂ → ∀ {p₁ p₂ : U},
    inc p₁ w₁ → inc p₁ w₂ → inc p₂ w₁ → inc p₂ w₂ → p₁ = p₂
  noK4 : ∀ col : U × W → Bool,
    ¬ (SimpleGraph.completeGraph (Fin 4)).IsContained (bipGraphOf inc col)

/- ========================================================================= -/
/- Part 1: Finite field `Fq2 q`, Hermitian unital, and O'Nan-free base graph -/
/- ========================================================================= -/

section Unital

variable {q : ℕ} [Fact q.Prime]

private abbrev Fq2 (q : ℕ) [Fact q.Prime] := GaloisField q 2

private noncomputable local instance instFintypeFq2 (q : ℕ) [Fact q.Prime] :
    Fintype (Fq2 q) := Fintype.ofFinite _

private lemma q_ge_two : 2 ≤ q := (Fact.out : q.Prime).two_le

private lemma fq2_card : Fintype.card (Fq2 q) = q ^ 2 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card q 2 (by norm_num)]

private lemma frob_add (x y : Fq2 q) : (x + y) ^ q = x ^ q + y ^ q :=
  add_pow_char x y q

private lemma frob_mul (x y : Fq2 q) : (x * y) ^ q = x ^ q * y ^ q :=
  mul_pow x y q

private lemma frob_zero : (0 : Fq2 q) ^ q = 0 :=
  zero_pow (Fact.out : q.Prime).ne_zero

private lemma frob_one : (1 : Fq2 q) ^ q = 1 := one_pow q

private lemma frob_neg (x : Fq2 q) : (-x) ^ q = -(x ^ q) := by
  have h : (-x) ^ q + x ^ q = 0 := by
    rw [← frob_add, neg_add_cancel, frob_zero]
  exact eq_neg_of_add_eq_zero_left h

private lemma frob_sub (x y : Fq2 q) : (x - y) ^ q = x ^ q - y ^ q := by
  rw [sub_eq_add_neg, frob_add, frob_neg, ← sub_eq_add_neg]

private lemma frob_invol (x : Fq2 q) : (x ^ q) ^ q = x := by
  have h := FiniteField.pow_card x
  rw [fq2_card, sq, pow_mul] at h
  exact h

private lemma frob_eq_zero_iff (x : Fq2 q) : x ^ q = 0 ↔ x = 0 :=
  pow_eq_zero_iff (Fact.out : q.Prime).ne_zero

private lemma frob_div (x y : Fq2 q) : (x / y) ^ q = x ^ q / y ^ q :=
  div_pow x y q

private lemma card_roots_pow_sub_X :
    (Finset.univ.filter (fun x : Fq2 q => x ^ q = x)).card ≤ q := by
  let P : Polynomial (Fq2 q) := Polynomial.X ^ q - Polynomial.X
  have hq : 2 ≤ q := q_ge_two
  have hPne : P ≠ 0 := by
    intro h0
    have hc : P.coeff q = 0 := by rw [h0]; simp
    simp only [P, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_true,
      Polynomial.coeff_X] at hc
    have hq1 : 1 ≠ q := by omega
    simp [hq1] at hc
  have hdeg : P.natDegree ≤ q := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    simp [Polynomial.natDegree_X]
    omega
  have hsub : Finset.univ.filter (fun x : Fq2 q => x ^ q = x) ⊆ P.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Polynomial.IsRoot.def]
    simp [P, hx]
  calc (Finset.univ.filter (fun x : Fq2 q => x ^ q = x)).card
      ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ q := hdeg

private lemma card_fixed :
    (Finset.univ.filter (fun x : Fq2 q => x ^ q = x)).card = q := by
  apply le_antisymm card_roots_pow_sub_X
  have hsub : Finset.image (algebraMap (ZMod q) (Fq2 q)) Finset.univ ⊆
      Finset.univ.filter (fun x : Fq2 q => x ^ q = x) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, _, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← map_pow, ZMod.pow_card]
  calc q = Fintype.card (ZMod q) := (ZMod.card q).symm
    _ = (Finset.image (algebraMap (ZMod q) (Fq2 q)) Finset.univ).card := by
        rw [Finset.card_image_of_injective _ (RingHom.injective _), Finset.card_univ]
    _ ≤ (Finset.univ.filter (fun x : Fq2 q => x ^ q = x)).card := Finset.card_le_card hsub

private lemma card_roots_pow_eq (c : Fq2 q) :
    (Finset.univ.filter (fun x : Fq2 q => x ^ (q + 1) = c)).card ≤ q + 1 := by
  let P : Polynomial (Fq2 q) := Polynomial.X ^ (q + 1) - Polynomial.C c
  have hPne : P ≠ 0 := by
    intro h0
    have hc : P.coeff (q + 1) = 0 := by rw [h0]; simp
    simp only [P, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_true,
      Polynomial.coeff_C] at hc
    simp at hc
  have hdeg : P.natDegree ≤ q + 1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    simp
  have hsub : Finset.univ.filter (fun x : Fq2 q => x ^ (q + 1) = c) ⊆ P.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Polynomial.IsRoot.def]
    simp [P, hx]
  calc (Finset.univ.filter (fun x : Fq2 q => x ^ (q + 1) = c)).card
      ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ q + 1 := hdeg

private lemma card_norm_fiber {c : Fq2 q} (hc0 : c ≠ 0) (hcf : c ^ q = c) :
    (Finset.univ.filter (fun x : Fq2 q => x ^ (q + 1) = c)).card = q + 1 := by
  let Fnz : Finset (Fq2 q) := (Finset.univ.filter (fun y : Fq2 q => y ^ q = y)).erase 0
  have h0F : (0 : Fq2 q) ∈ Finset.univ.filter (fun y : Fq2 q => y ^ q = y) := by
    simp [frob_zero]
  have hFnz_card : Fnz.card = q - 1 := by
    rw [Finset.card_erase_of_mem h0F, card_fixed]
  have hcFnz : c ∈ Fnz := by
    simp [Fnz, hc0, hcf]
  let S : Finset (Fq2 q) := Finset.univ.erase 0
  have hS_card : S.card = q ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, fq2_card]
  have hmaps : ∀ x ∈ S, x ^ (q + 1) ∈ Fnz := by
    intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
    simp only [Fnz, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨pow_ne_zero _ hx0, ?_⟩
    rw [pow_succ, frob_mul, frob_invol, mul_comm]
  have hsum : ∑ y ∈ Fnz, (S.filter (fun x => x ^ (q + 1) = y)).card = S.card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨fun ⟨_, _, hx, _⟩ => hx, fun hx => ⟨x ^ (q + 1), hmaps x hx, hx, rfl⟩⟩
    · intro y₁ _ y₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro x hx₁ hx₂
      simp only [Finset.mem_filter] at hx₁ hx₂
      exact hne (hx₁.2.symm.trans hx₂.2)
  have hle : ∀ y ∈ Fnz, (S.filter (fun x => x ^ (q + 1) = y)).card ≤ q + 1 := by
    intro y _
    exact le_trans (Finset.card_le_card (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.2)) (card_roots_pow_eq y)
  have htot : ∑ y ∈ Fnz, (S.filter (fun x => x ^ (q + 1) = y)).card =
      ∑ _y ∈ Fnz, (q + 1) := by
    rw [hsum, hS_card, Finset.sum_const, smul_eq_mul, hFnz_card]
    have hq := q_ge_two (q := q)
    have hq1 : 1 ≤ q := by omega
    have hq2 : 1 ≤ q ^ 2 := by nlinarith
    zify [hq1, hq2]
    ring
  have hall : ∀ y ∈ Fnz, (S.filter (fun x => x ^ (q + 1) = y)).card = q + 1 := by
    intro y hy
    by_contra hne
    have hlt : (S.filter (fun x => x ^ (q + 1) = y)).card < q + 1 :=
      lt_of_le_of_ne (hle y hy) hne
    have hstrict := Finset.sum_lt_sum hle ⟨y, hy, hlt⟩
    omega
  have heq : Finset.univ.filter (fun x : Fq2 q => x ^ (q + 1) = c) =
      S.filter (fun x => x ^ (q + 1) = c) := by
    ext x
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · intro hx
      refine ⟨?_, hx⟩
      intro hx0
      rw [hx0, zero_pow (by omega)] at hx
      exact hc0 hx.symm
    · exact And.right
  rw [heq]
  exact hall c hcFnz

private lemma exists_norm_neg_one : ∃ α : Fq2 q, α ^ (q + 1) = -1 := by
  have hcard : (Finset.univ.filter (fun x : Fq2 q => x ^ (q + 1) = -1)).card = q + 1 :=
    card_norm_fiber (by simp) (by rw [frob_neg, frob_one])
  have hne : (Finset.univ.filter (fun x : Fq2 q => x ^ (q + 1) = -1)).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases hne with ⟨α, hα⟩
  exact ⟨α, (Finset.mem_filter.mp hα).2⟩

private lemma exists_trace_ne_zero : ∃ μ : Fq2 q, μ + μ ^ q ≠ 0 := by
  let P : Polynomial (Fq2 q) := Polynomial.X ^ q + Polynomial.X
  have hq : 2 ≤ q := q_ge_two
  have hPne : P ≠ 0 := by
    intro h0
    have hc : P.coeff q = 0 := by rw [h0]; simp
    simp only [P, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_true,
      Polynomial.coeff_X] at hc
    have hq1 : 1 ≠ q := by omega
    simp [hq1] at hc
  have hdeg : P.natDegree ≤ q := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp [Polynomial.natDegree_X]
    omega
  have hcard_lt : (Finset.univ.filter (fun x : Fq2 q => x + x ^ q = 0)).card <
      (Finset.univ : Finset (Fq2 q)).card := by
    have hsub : Finset.univ.filter (fun x : Fq2 q => x + x ^ q = 0) ⊆ P.roots.toFinset := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Polynomial.IsRoot.def]
      simp [P, add_comm, hx]
    calc (Finset.univ.filter (fun x : Fq2 q => x + x ^ q = 0)).card
        ≤ P.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ ≤ q := hdeg
      _ < q ^ 2 := by nlinarith
      _ = (Finset.univ : Finset (Fq2 q)).card := by rw [Finset.card_univ, fq2_card]
  have hne : (Finset.univ \ Finset.univ.filter (fun x : Fq2 q => x + x ^ q = 0)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have hle := Finset.card_le_card hsub
    omega
  rcases hne with ⟨μ, hμ⟩
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hμ
  exact ⟨μ, hμ⟩

private abbrev Vec (q : ℕ) [Fact q.Prime] := Fin 3 → Fq2 q

private lemma vec_ext {u v : Vec q} (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) :
    u = v := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private noncomputable def herm (u v : Vec q) : Fq2 q :=
  u 0 * (v 0) ^ q + u 1 * (v 1) ^ q + u 2 * (v 2) ^ q

private noncomputable def det3 (u v w : Vec q) : Fq2 q :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
  u 1 * (v 0 * w 2 - v 2 * w 0) +
  u 2 * (v 0 * w 1 - v 1 * w 0)

private noncomputable def cross (u v : Vec q) : Vec q :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

private noncomputable def frobVec (u : Vec q) : Vec q := fun i => (u i) ^ q

private noncomputable def dualCross (u v : Vec q) : Vec q := frobVec (cross u v)

private lemma herm_symm (u v : Vec q) : herm v u = (herm u v) ^ q := by
  simp only [herm, frob_add, frob_mul, frob_invol]; ring

private lemma herm_self_fixed (u : Vec q) : (herm u u) ^ q = herm u u :=
  (herm_symm u u).symm

private lemma herm_add_left (u₁ u₂ v : Vec q) :
    herm (u₁ + u₂) v = herm u₁ v + herm u₂ v := by
  simp only [herm, Pi.add_apply]; ring

private lemma herm_add_right (u v₁ v₂ : Vec q) :
    herm u (v₁ + v₂) = herm u v₁ + herm u v₂ := by
  simp only [herm, Pi.add_apply, frob_add]; ring

private lemma herm_smul_left (c : Fq2 q) (u v : Vec q) :
    herm (c • u) v = c * herm u v := by
  simp only [herm, Pi.smul_apply, smul_eq_mul]; ring

private lemma herm_smul_right (c : Fq2 q) (u v : Vec q) :
    herm u (c • v) = c ^ q * herm u v := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, frob_mul]; ring

private lemma herm_zero_left (v : Vec q) : herm 0 v = 0 := by simp [herm]

private lemma herm_dualCross (x u v : Vec q) :
    herm x (dualCross u v) = det3 x u v := by
  simp only [herm, dualCross, frobVec, cross, det3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, frob_invol]
  ring

private lemma herm_left_dualCross (u v : Vec q) : herm u (dualCross u v) = 0 := by
  rw [herm_dualCross]; simp only [det3]; ring

private lemma herm_right_dualCross (u v : Vec q) : herm v (dualCross u v) = 0 := by
  rw [herm_dualCross]; simp only [det3]; ring

private lemma frobVec_eq_zero_iff (u : Vec q) : frobVec u = 0 ↔ u = 0 := by
  constructor
  · intro h; ext i; exact (frob_eq_zero_iff (u i)).mp (congrFun h i)
  · intro h; subst h; ext i; exact frob_zero

private lemma dualCross_eq_zero_iff (u v : Vec q) : dualCross u v = 0 ↔ cross u v = 0 :=
  frobVec_eq_zero_iff (cross u v)

private lemma det3_gram (u v w : Vec q) :
    det3 ![herm u u, herm u v, herm u w]
         ![herm v u, herm v v, herm v w]
         ![herm w u, herm w v, herm w w] = (det3 u v w) ^ (q + 1) := by
  let A : Matrix (Fin 3) (Fin 3) (Fq2 q) := Matrix.of ![u, v, w]
  let B : Matrix (Fin 3) (Fin 3) (Fq2 q) :=
    Matrix.transpose (Matrix.of ![frobVec u, frobVec v, frobVec w])
  have hAdet : A.det = det3 u v w := by
    rw [Matrix.det_fin_three]
    simp only [A, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, det3]
    ring
  have hBdet : B.det = (det3 u v w) ^ q := by
    rw [Matrix.det_transpose, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      frobVec, det3, frob_add, frob_sub, frob_mul]
    ring
  have hAB : (A * B).det =
      det3 ![herm u u, herm u v, herm u w]
           ![herm v u, herm v v, herm v w]
           ![herm w u, herm w v, herm w w] := by
    rw [Matrix.det_fin_three]
    simp only [A, B, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      frobVec, herm, det3]
    ring
  rw [← hAB, Matrix.det_mul, hAdet, hBdet, pow_succ, mul_comm]

private lemma cross_add_smul_left (c : Fq2 q) (u v : Vec q) :
    cross u (c • u + v) = cross u v := by
  apply vec_ext <;>
    simp only [cross, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> ring

private lemma cross_smul_right (c : Fq2 q) (u : Vec q) :
    cross u (c • u) = 0 := by
  apply vec_ext <;>
    simp only [cross, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> ring

private lemma cross_eq_zero_imp_smul {u v : Vec q} (hu : u ≠ 0) (hv : v ≠ 0)
    (hc : cross u v = 0) : ∃ c : Fq2 q, c ≠ 0 ∧ v = c • u := by
  have h0 : u 1 * v 2 - u 2 * v 1 = 0 := congrFun hc 0
  have h1 : u 2 * v 0 - u 0 * v 2 = 0 := congrFun hc 1
  have h2 : u 0 * v 1 - u 1 * v 0 = 0 := congrFun hc 2
  have hu_ex : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
    by_contra h; push Not at h; apply hu; exact vec_ext h.1 h.2.1 h.2.2
  rcases hu_ex with h0u | h1u | h2u
  · refine ⟨v 0 / u 0, ?_, ?_⟩
    · intro hdiv
      have hv0 : v 0 = 0 := (div_eq_zero_iff.mp hdiv).resolve_right h0u
      apply hv; apply vec_ext
      · exact hv0
      · have : u 0 * v 1 = 0 := by linear_combination h2 + u 1 * hv0
        exact (mul_eq_zero.mp this).resolve_left h0u
      · have : u 0 * v 2 = 0 := by linear_combination -h1 + u 2 * hv0
        exact (mul_eq_zero.mp this).resolve_left h0u
    · apply vec_ext <;> simp only [Pi.smul_apply, smul_eq_mul] <;> field_simp [h0u]
      · linear_combination h2
      · linear_combination -h1
  · refine ⟨v 1 / u 1, ?_, ?_⟩
    · intro hdiv
      have hv1 : v 1 = 0 := (div_eq_zero_iff.mp hdiv).resolve_right h1u
      apply hv; apply vec_ext
      · have : u 1 * v 0 = 0 := by linear_combination -h2 + u 0 * hv1
        exact (mul_eq_zero.mp this).resolve_left h1u
      · exact hv1
      · have : u 1 * v 2 = 0 := by linear_combination h0 + u 2 * hv1
        exact (mul_eq_zero.mp this).resolve_left h1u
    · apply vec_ext <;> simp only [Pi.smul_apply, smul_eq_mul] <;> field_simp [h1u]
      · linear_combination -h2
      · linear_combination h0
  · refine ⟨v 2 / u 2, ?_, ?_⟩
    · intro hdiv
      have hv2 : v 2 = 0 := (div_eq_zero_iff.mp hdiv).resolve_right h2u
      apply hv; apply vec_ext
      · have : u 2 * v 0 = 0 := by linear_combination h1 + u 0 * hv2
        exact (mul_eq_zero.mp this).resolve_left h2u
      · have : u 2 * v 1 = 0 := by linear_combination -h0 + u 1 * hv2
        exact (mul_eq_zero.mp this).resolve_left h2u
      · exact hv2
    · apply vec_ext <;> simp only [Pi.smul_apply, smul_eq_mul] <;> field_simp [h2u]
      · linear_combination h1
      · linear_combination -h0

private lemma det3_eq_zero_imp_span {u v w : Vec q} (hc : cross u v ≠ 0)
    (hd : det3 w u v = 0) : ∃ a b : Fq2 q, w = a • u + b • v := by
  have hc_ex : cross u v 0 ≠ 0 ∨ cross u v 1 ≠ 0 ∨ cross u v 2 ≠ 0 := by
    by_contra h; push Not at h; apply hc; exact vec_ext h.1 h.2.1 h.2.2
  simp only [cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hc_ex
  rcases hc_ex with hc0 | hc1 | hc2
  · let Δ := u 1 * v 2 - u 2 * v 1
    refine ⟨(w 1 * v 2 - w 2 * v 1) / Δ, (u 1 * w 2 - u 2 * w 1) / Δ, ?_⟩
    apply vec_ext <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
      field_simp [Δ, hc0]
    · simp only [det3] at hd; linear_combination hd
    · ring
    · ring
  · let Δ := u 2 * v 0 - u 0 * v 2
    refine ⟨(w 2 * v 0 - w 0 * v 2) / Δ, (u 2 * w 0 - u 0 * w 2) / Δ, ?_⟩
    apply vec_ext <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
      field_simp [Δ, hc1]
    · ring
    · simp only [det3] at hd; linear_combination hd
    · ring
  · let Δ := u 0 * v 1 - u 1 * v 0
    refine ⟨(w 0 * v 1 - w 1 * v 0) / Δ, (u 0 * w 1 - u 1 * w 0) / Δ, ?_⟩
    apply vec_ext <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
      field_simp [Δ, hc2]
    · ring
    · ring
    · simp only [det3] at hd; linear_combination hd

private lemma cramer3 {u v w x : Vec q} (hd : det3 u v w ≠ 0) :
    x = (det3 x v w / det3 u v w) • u +
        (det3 u x w / det3 u v w) • v +
        (det3 u v x / det3 u v w) • w := by
  apply vec_ext <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    field_simp [hd] <;> simp only [det3] <;> ring

private def isNorm (v : Vec q) : Prop :=
  v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)

private abbrev P2 (q : ℕ) [Fact q.Prime] := {v : Vec q // isNorm v}

private lemma p2_ne_zero (p : P2 q) : p.1 ≠ 0 := by
  intro h
  rcases p.2 with h0 | ⟨_, h1⟩ | ⟨_, _, h2⟩
  · have := congrFun h 0; simp [h0] at this
  · have := congrFun h 1; simp [h1] at this
  · have := congrFun h 2; simp [h2] at this

private noncomputable def normVec (v : Vec q) (hv : v ≠ 0) : P2 q :=
  if h0 : v 0 ≠ 0 then
    ⟨(v 0)⁻¹ • v, Or.inl (by simp [h0])⟩
  else if h1 : v 1 ≠ 0 then
    ⟨(v 1)⁻¹ • v, Or.inr (Or.inl ⟨by simp [not_not.mp h0], by simp [h1]⟩)⟩
  else
    ⟨(v 2)⁻¹ • v, Or.inr (Or.inr ⟨by simp [not_not.mp h0], by simp [not_not.mp h1], by
      have h2 : v 2 ≠ 0 := by
        intro hz; apply hv; exact vec_ext (not_not.mp h0) (not_not.mp h1) hz
      simp [h2]⟩)⟩

private lemma exists_scale_normVec (v : Vec q) (hv : v ≠ 0) :
    ∃ c : Fq2 q, c ≠ 0 ∧ v = c • (normVec v hv).1 := by
  unfold normVec
  split_ifs with h0 h1
  · exact ⟨v 0, h0, by simp [smul_smul, mul_inv_cancel₀ h0]⟩
  · exact ⟨v 1, h1, by simp [smul_smul, mul_inv_cancel₀ h1]⟩
  · have h2 : v 2 ≠ 0 := by
      intro hz; apply hv; exact vec_ext (not_not.mp h0) (not_not.mp h1) hz
    exact ⟨v 2, h2, by simp [smul_smul, mul_inv_cancel₀ h2]⟩

private lemma scale_of_normVec_eq {u v : Vec q} {hu : u ≠ 0} {hv : v ≠ 0}
    (hEq : normVec u hu = normVec v hv) : ∃ c : Fq2 q, c ≠ 0 ∧ v = c • u := by
  rcases exists_scale_normVec u hu with ⟨c₁, hc₁, h₁⟩
  rcases exists_scale_normVec v hv with ⟨c₂, hc₂, h₂⟩
  have h1' : (normVec u hu).1 = c₁⁻¹ • u := by
    have := congrArg (c₁⁻¹ • ·) h₁
    simpa [inv_smul_smul₀ hc₁] using this.symm
  refine ⟨c₂ * c₁⁻¹, mul_ne_zero hc₂ (inv_ne_zero hc₁), ?_⟩
  rw [h₂, ← hEq, h1', mul_smul]

private lemma p2_eq_of_smul {p₁ p₂ : P2 q} {c : Fq2 q} (hc : c ≠ 0)
    (heq : p₂.1 = c • p₁.1) : p₁ = p₂ := by
  have h0 : p₂.1 0 = c * p₁.1 0 := congrFun heq 0
  have h1 : p₂.1 1 = c * p₁.1 1 := congrFun heq 1
  have h2 : p₂.1 2 = c * p₁.1 2 := congrFun heq 2
  have hc1 : c = 1 := by
    rcases p₁.2 with a0 | ⟨a0, a1⟩ | ⟨a0, a1, a2⟩ <;>
    rcases p₂.2 with b0 | ⟨b0, b1⟩ | ⟨b0, b1, b2⟩
    · rw [a0, b0, mul_one] at h0; exact h0.symm
    · rw [a0, b0, mul_one] at h0; exact absurd h0.symm hc
    · rw [a0, b0, mul_one] at h0; exact absurd h0.symm hc
    · rw [a0, b0, mul_zero] at h0; exact absurd h0 one_ne_zero
    · rw [a1, b1, mul_one] at h1; exact h1.symm
    · rw [a1, b1, mul_one] at h1; exact absurd h1.symm hc
    · rw [a0, b0, mul_zero] at h0; exact absurd h0 one_ne_zero
    · rw [a1, b1, mul_zero] at h1; exact absurd h1 one_ne_zero
    · rw [a2, b2, mul_one] at h2; exact h2.symm
  subst hc1
  exact Subtype.ext (by simpa using heq.symm)

private lemma p2_ne_iff_cross_ne_zero (p₁ p₂ : P2 q) : p₁ ≠ p₂ ↔ cross p₁.1 p₂.1 ≠ 0 := by
  constructor
  · intro hne hc
    rcases cross_eq_zero_imp_smul (p2_ne_zero p₁) (p2_ne_zero p₂) hc with ⟨c, hc0, heq⟩
    exact hne (p2_eq_of_smul hc0 heq)
  · intro hc heq
    subst heq
    apply hc; apply vec_ext <;> simp only [cross, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Pi.zero_apply] <;> ring

private noncomputable def p2Equiv :
    P2 q ≃ (Fq2 q × Fq2 q) ⊕ Fq2 q ⊕ Unit where
  toFun p :=
    if p.1 0 = 1 then Sum.inl (p.1 1, p.1 2)
    else if p.1 1 = 1 then Sum.inr (Sum.inl (p.1 2))
    else Sum.inr (Sum.inr ())
  invFun s := match s with
    | Sum.inl (y, z) => ⟨![1, y, z], Or.inl rfl⟩
    | Sum.inr (Sum.inl z) => ⟨![0, 1, z], Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | Sum.inr (Sum.inr ()) => ⟨![0, 0, 1], Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
  left_inv p := by
    apply Subtype.ext
    rcases p.2 with h0 | ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
    · simp only [h0, ↓reduceIte]; apply vec_ext <;> simp [h0]
    · have h01 : (0 : Fq2 q) ≠ 1 := zero_ne_one
      simp only [h0, h01, ↓reduceIte, h1]; apply vec_ext <;> simp [h0, h1]
    · have h01 : (0 : Fq2 q) ≠ 1 := zero_ne_one
      simp only [h0, h01, ↓reduceIte, h1]; apply vec_ext <;> simp [h0, h1, h2]
  right_inv s := by
    rcases s with ⟨y, z⟩ | z | ⟨⟩ <;> simp [zero_ne_one]

private lemma p2_card : Fintype.card (P2 q) = q ^ 4 + q ^ 2 + 1 := by
  rw [Fintype.card_congr p2Equiv]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit, fq2_card]
  ring

private abbrev Unital (q : ℕ) [Fact q.Prime] := {p : P2 q // herm p.1 p.1 = 0}
private abbrev Secant (q : ℕ) [Fact q.Prime] := {w : P2 q // herm w.1 w.1 ≠ 0}

private lemma card_unital_add_secant :
    Fintype.card (Unital q) + Fintype.card (Secant q) = q ^ 4 + q ^ 2 + 1 := by
  rw [← p2_card]
  have h1 : Fintype.card (Secant q) = Fintype.card (P2 q) - Fintype.card (Unital q) :=
    Fintype.card_subtype_compl (fun p : P2 q => herm p.1 p.1 = 0)
  have h2 : Fintype.card (Unital q) ≤ Fintype.card (P2 q) :=
    Fintype.card_subtype_le (fun p : P2 q => herm p.1 p.1 = 0)
  omega

private lemma tangent_unique_unital {w p : P2 q} (hw : herm w.1 w.1 = 0)
    (hp : herm p.1 p.1 = 0) (hinc : herm p.1 w.1 = 0) : p = w := by
  by_contra hne
  have hwp : herm w.1 p.1 = 0 := by rw [herm_symm, hinc, frob_zero]
  have hc : cross w.1 p.1 ≠ 0 := (p2_ne_iff_cross_ne_zero w p).mp (Ne.symm hne)
  have hdet_ex : ∃ z : Vec q, det3 w.1 p.1 z ≠ 0 := by
    have hc_ex : cross w.1 p.1 0 ≠ 0 ∨ cross w.1 p.1 1 ≠ 0 ∨ cross w.1 p.1 2 ≠ 0 := by
      by_contra h; push Not at h; apply hc; exact vec_ext h.1 h.2.1 h.2.2
    rcases hc_ex with h0 | h1 | h2
    · refine ⟨![1, 0, 0], ?_⟩
      simp only [det3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      simp only [cross, Matrix.cons_val_zero] at h0
      intro hz; apply h0; linear_combination hz
    · refine ⟨![0, 1, 0], ?_⟩
      simp only [det3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      simp only [cross, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      intro hz; apply h1; linear_combination hz
    · refine ⟨![0, 0, 1], ?_⟩
      simp only [det3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      simp only [cross, Matrix.cons_val] at h2
      intro hz; apply h2; linear_combination hz
  rcases hdet_ex with ⟨z, hz⟩
  have hgram := det3_gram w.1 p.1 z
  rw [hw, hp, hinc, hwp] at hgram
  have h0 : det3 ![(0 : Fq2 q), 0, herm w.1 z] ![0, 0, herm p.1 z]
      ![herm z w.1, herm z p.1, herm z z] = 0 := by
    simp only [det3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
  rw [h0] at hgram
  exact pow_ne_zero (q + 1) hz hgram.symm

private lemma exists_line_basis (w : P2 q) :
    ∃ u v : Vec q, cross u v ≠ 0 ∧ herm u w.1 = 0 ∧ herm v w.1 = 0 := by
  rcases w.2 with h0 | ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
  · refine ⟨![-(w.1 1) ^ q, 1, 0], ![-(w.1 2) ^ q, 0, 1], ?_, ?_, ?_⟩
    · intro hc; have := congrFun hc 0; simp [cross] at this
    · simp [herm, h0]
    · simp [herm, h0]
  · refine ⟨![1, 0, 0], ![0, -(w.1 2) ^ q, 1], ?_, ?_, ?_⟩
    · intro hc; have := congrFun hc 1; simp [cross] at this
    · simp [herm, h0, frob_zero]
    · simp [herm, h0, h1]
  · refine ⟨![1, 0, 0], ![0, 1, 0], ?_, ?_, ?_⟩
    · intro hc; have := congrFun hc 2; simp [cross] at this
    · simp [herm, h0, h1, h2, frob_zero]
    · simp [herm, h0, h1, h2, frob_zero]

private lemma line_mem_iff_span {w : P2 q} {u v : Vec q} (hc : cross u v ≠ 0)
    (hu : herm u w.1 = 0) (hv : herm v w.1 = 0) (x : Vec q) :
    herm x w.1 = 0 ↔ ∃ a b : Fq2 q, x = a • u + b • v := by
  have hdc : dualCross u v ≠ 0 := mt (dualCross_eq_zero_iff u v).mp hc
  have hwdc : cross w.1 (dualCross u v) = 0 := by
    have h1 : (cross u v) 0 * (w.1 1) ^ q - (cross u v) 1 * (w.1 0) ^ q = 0 := by
      simp only [cross, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [herm] at hu hv
      linear_combination (v 2) * hu - (u 2) * hv
    have h2 : (cross u v) 0 * (w.1 2) ^ q - (cross u v) 2 * (w.1 0) ^ q = 0 := by
      simp only [cross, Matrix.cons_val_zero, Matrix.cons_val]
      simp only [herm] at hu hv
      linear_combination -(v 1) * hu + (u 1) * hv
    have h3 : (cross u v) 1 * (w.1 2) ^ q - (cross u v) 2 * (w.1 1) ^ q = 0 := by
      simp only [cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      simp only [herm] at hu hv
      linear_combination (v 0) * hu - (u 0) * hv
    apply vec_ext <;>
      simp only [cross, dualCross, frobVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Pi.zero_apply]
    · have := congrArg (· ^ q) h3
      rw [frob_sub, frob_mul, frob_mul, frob_invol, frob_invol, frob_zero] at this
      simp only [cross, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val] at this
      linear_combination -this
    · have := congrArg (· ^ q) h2
      rw [frob_sub, frob_mul, frob_mul, frob_invol, frob_invol, frob_zero] at this
      simp only [cross, Matrix.cons_val_zero, Matrix.cons_val] at this
      linear_combination this
    · have := congrArg (· ^ q) h1
      rw [frob_sub, frob_mul, frob_mul, frob_invol, frob_invol, frob_zero] at this
      simp only [cross, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      linear_combination -this
  rcases cross_eq_zero_imp_smul (p2_ne_zero w) hdc hwdc with ⟨c, hc0, hceq⟩
  constructor
  · intro hx
    have hdet : det3 x u v = 0 := by
      rw [← herm_dualCross, hceq, herm_smul_right, hx, mul_zero]
    exact det3_eq_zero_imp_span hc hdet
  · rintro ⟨a, b, rfl⟩
    rw [herm_add_left, herm_smul_left, herm_smul_left, hu, hv, mul_zero, mul_zero, add_zero]

private lemma card_dual_line (w : P2 q) :
    (Finset.univ.filter (fun p : P2 q => herm p.1 w.1 = 0)).card = q ^ 2 + 1 := by
  rcases exists_line_basis w with ⟨u, v, hc, hu, hv⟩
  have hu0 : u ≠ 0 := by intro h; subst h; apply hc; apply vec_ext <;> simp [cross]
  have hxu_ne : ∀ x : Fq2 q, x • u + v ≠ 0 := by
    intro x h0
    have : cross u (x • u + v) = 0 := by rw [h0]; apply vec_ext <;> simp [cross]
    rw [cross_add_smul_left] at this
    exact hc this
  let f : Option (Fq2 q) → P2 q := fun o => match o with
    | none => normVec u hu0
    | some x => normVec (x • u + v) (hxu_ne x)
  have hf_mem : ∀ o, f o ∈ Finset.univ.filter (fun p : P2 q => herm p.1 w.1 = 0) := by
    intro o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases o with
    | none =>
      rcases exists_scale_normVec u hu0 with ⟨c, hc0, hceq⟩
      have : c * herm (normVec u hu0).1 w.1 = 0 := by rw [← herm_smul_left, ← hceq, hu]
      exact (mul_eq_zero.mp this).resolve_left hc0
    | some x =>
      rcases exists_scale_normVec (x • u + v) (hxu_ne x) with ⟨c, hc0, hceq⟩
      have : c * herm (normVec (x • u + v) (hxu_ne x)).1 w.1 = 0 := by
        rw [← herm_smul_left, ← hceq, herm_add_left, herm_smul_left, hu, hv, mul_zero, add_zero]
      exact (mul_eq_zero.mp this).resolve_left hc0
  have hf_inj : Function.Injective f := by
    intro o₁ o₂ hEq
    cases o₁ with
    | none =>
      cases o₂ with
      | none => rfl
      | some x =>
        rcases scale_of_normVec_eq hEq with ⟨t, _, hsm⟩
        have : cross u (x • u + v) = 0 := by rw [hsm]; exact cross_smul_right _ u
        rw [cross_add_smul_left] at this; exact absurd this hc
    | some x =>
      cases o₂ with
      | none =>
        rcases scale_of_normVec_eq hEq.symm with ⟨t, _, hsm⟩
        have : cross u (x • u + v) = 0 := by rw [hsm]; exact cross_smul_right _ u
        rw [cross_add_smul_left] at this; exact absurd this hc
      | some y =>
        congr 1
        rcases scale_of_normVec_eq hEq with ⟨t, _, hsm⟩
        have hdiff : (y - t * x) • u + (1 - t) • v = 0 := by
          ext i
          have hi := congrFun hsm i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
          linear_combination hi
        have h1t : 1 - t = 0 := by
          by_contra hne
          have hvu : v = (-(y - t * x) / (1 - t)) • u := by
            ext i
            have hi := congrFun hdiff i
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
            field_simp [hne]; linear_combination hi
          rw [hvu] at hc; exact hc (cross_smul_right _ u)
        have ht1 : t = 1 := by linear_combination -h1t
        rw [ht1, one_mul, sub_self, zero_smul, add_zero] at hdiff
        by_contra hxy
        apply hu0; ext i
        have hi := congrFun hdiff i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
        exact (mul_eq_zero.mp hi).resolve_left (sub_ne_zero.mpr (Ne.symm hxy))
  have hsurj : Finset.image f Finset.univ =
      Finset.univ.filter (fun p : P2 q => herm p.1 w.1 = 0) := by
    ext p
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨o, rfl⟩; exact (Finset.mem_filter.mp (hf_mem o)).2
    · intro hp
      rcases (line_mem_iff_span hc hu hv p.1).mp hp with ⟨a, b, hab⟩
      by_cases hb : b = 0
      · subst hb
        simp only [zero_smul, add_zero] at hab
        have ha : a ≠ 0 := by intro h0; subst h0; simp at hab; exact p2_ne_zero p hab
        refine ⟨none, ?_⟩
        rcases exists_scale_normVec u hu0 with ⟨c, hc0, hceq⟩
        exact p2_eq_of_smul (mul_ne_zero ha hc0) (by rw [hab, hceq, mul_smul])
      · refine ⟨some (a / b), ?_⟩
        rcases exists_scale_normVec ((a / b) • u + v) (hxu_ne (a / b)) with ⟨c, hc0, hceq⟩
        refine p2_eq_of_smul (mul_ne_zero hb hc0) ?_
        ext i; have hi := congrFun hab i; have hi2 := congrFun hceq i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi hi2 ⊢
        rw [hi, mul_assoc, ← hi2]; field_simp [hb]
  rw [← hsurj, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_option,
    fq2_card]

private lemma card_clique (p : Unital q) :
    (Finset.univ.filter (fun w : Secant q => herm p.1.1 w.1.1 = 0)).card = q ^ 2 := by
  let L := Finset.univ.filter (fun w : P2 q => herm w.1 p.1.1 = 0)
  have hL : L.card = q ^ 2 + 1 := card_dual_line p.1
  have hpL : p.1 ∈ L := by simp [L, p.2]
  let L' := L.erase p.1
  have hL' : L'.card = q ^ 2 := by rw [Finset.card_erase_of_mem hpL, hL]; omega
  let S := Finset.univ.filter (fun w : Secant q => herm p.1.1 w.1.1 = 0)
  have himg : S.image Subtype.val = L' := by
    ext w
    simp only [S, L', L, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro ⟨⟨w, hw⟩, hinc, rfl⟩
      refine ⟨fun heq => hw (by rw [show w = p.1 from heq]; exact p.2), by rw [herm_symm, hinc, frob_zero]⟩
    · rintro ⟨hne, hinc⟩
      have hw : herm w.1 w.1 ≠ 0 := fun hw0 => hne (tangent_unique_unital p.2 hw0 hinc)
      exact ⟨⟨w, hw⟩, by rw [herm_symm, hinc, frob_zero], rfl⟩
  rw [← hL', ← himg, Finset.card_image_of_injective _ Subtype.val_injective]

private lemma card_secant_points (w : Secant q) :
    (Finset.univ.filter (fun p : Unital q => herm p.1.1 w.1.1 = 0)).card = q + 1 := by
  rcases exists_line_basis w.1 with ⟨e₁, e₂, hc, he₁, he₂⟩
  have hex_u : ∃ u : Vec q, herm u w.1.1 = 0 ∧ herm u u ≠ 0 := by
    by_cases h1 : herm e₁ e₁ ≠ 0
    · exact ⟨e₁, he₁, h1⟩
    · by_cases h2 : herm e₂ e₂ ≠ 0
      · exact ⟨e₂, he₂, h2⟩
      · push Not at h1 h2
        have h12 : herm e₁ e₂ ≠ 0 := by
          intro h12z
          have h21z : herm e₂ e₁ = 0 := by rw [herm_symm, h12z, frob_zero]
          have hw1 : herm w.1.1 e₁ = 0 := by rw [herm_symm, he₁, frob_zero]
          have hw2 : herm w.1.1 e₂ = 0 := by rw [herm_symm, he₂, frob_zero]
          have hdet : det3 w.1.1 e₁ e₂ ≠ 0 := by
            intro hd
            rcases det3_eq_zero_imp_span hc hd with ⟨a, b, hab⟩
            have hww : herm (a • e₁ + b • e₂) w.1.1 = 0 := by
              rw [herm_add_left, herm_smul_left, herm_smul_left, he₁, he₂,
                mul_zero, mul_zero, add_zero]
            rw [← hab] at hww
            exact w.2 hww
          have hgram := det3_gram w.1.1 e₁ e₂
          rw [h1, h2, h12z, h21z, he₁, he₂, hw1, hw2] at hgram
          have h0 : det3 ![herm w.1.1 w.1.1, 0, 0] ![(0 : Fq2 q), 0, 0] ![0, 0, 0] = 0 := by
            simp only [det3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
          rw [h0] at hgram
          exact pow_ne_zero (q + 1) hdet hgram.symm
        rcases exists_trace_ne_zero (q := q) with ⟨μ, hμ⟩
        let lam := μ / herm e₁ e₂
        refine ⟨lam • e₁ + e₂, ?_, ?_⟩
        · rw [herm_add_left, herm_smul_left, he₁, he₂, mul_zero, add_zero]
        · rw [herm_add_left, herm_add_right, herm_add_right,
            herm_smul_left, herm_smul_right, herm_smul_left, herm_smul_right,
            h1, h2, mul_zero, mul_zero, zero_add, add_zero, herm_symm e₁ e₂]
          have hl : lam * herm e₁ e₂ = μ := div_mul_cancel₀ μ h12
          have hr : lam ^ q * (herm e₁ e₂) ^ q = μ ^ q := by rw [← frob_mul, hl]
          rw [hl, hr]; exact hμ
  rcases hex_u with ⟨u, huw, huu⟩
  let v := dualCross w.1.1 u
  have hvw : herm v w.1.1 = 0 := by rw [herm_symm, herm_left_dualCross, frob_zero]
  have hvu : herm v u = 0 := by rw [herm_symm, herm_right_dualCross, frob_zero]
  have huv : herm u v = 0 := herm_right_dualCross w.1.1 u
  have hwu : herm w.1.1 u = 0 := by rw [herm_symm, huw, frob_zero]
  have hwv : herm w.1.1 v = 0 := herm_left_dualCross w.1.1 u
  have hcw : cross w.1.1 u ≠ 0 := by
    intro h0
    have hu0 : u ≠ 0 := by intro hz; subst hz; exact huu (herm_zero_left _)
    rcases cross_eq_zero_imp_smul (p2_ne_zero w.1) hu0 h0 with ⟨c, hc0, hceq⟩
    rw [hceq, herm_smul_left] at huw
    exact w.2 ((mul_eq_zero.mp huw).resolve_left hc0)
  have hv0 : v ≠ 0 := mt (dualCross_eq_zero_iff w.1.1 u).mp hcw
  have hdet_wuv : det3 w.1.1 u v ≠ 0 := by
    intro hd
    have hd' : det3 v w.1.1 u = 0 := by simp only [det3] at hd ⊢; linear_combination hd
    rcases det3_eq_zero_imp_span hcw hd' with ⟨a, b, hab⟩
    have ha : a = 0 := by
      have : herm v w.1.1 = a * herm w.1.1 w.1.1 := by
        rw [hab, herm_add_left, herm_smul_left, herm_smul_left, huw, mul_zero, add_zero]
      rw [hvw] at this; exact (mul_eq_zero.mp this.symm).resolve_right w.2
    have hb : b = 0 := by
      have : herm v u = b * herm u u := by
        rw [hab, ha, zero_smul, zero_add, herm_smul_left]
      rw [hvu] at this; exact (mul_eq_zero.mp this.symm).resolve_right huu
    rw [ha, hb, zero_smul, zero_smul, add_zero] at hab; exact hv0 hab
  have hvv : herm v v ≠ 0 := by
    intro hvv0
    have hgram := det3_gram w.1.1 u v
    rw [hwu, hwv, huw, huv, hvw, hvu, hvv0] at hgram
    have h0 : det3 ![herm w.1.1 w.1.1, 0, 0] ![0, herm u u, 0] ![(0 : Fq2 q), 0, 0] = 0 := by
      simp only [det3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    rw [h0] at hgram
    exact pow_ne_zero (q + 1) hdet_wuv hgram.symm
  have hcuv : cross u v ≠ 0 := by
    intro h0
    have hu0 : u ≠ 0 := by intro hz; subst hz; exact huu (herm_zero_left _)
    rcases cross_eq_zero_imp_smul hu0 hv0 h0 with ⟨c, hc0, hceq⟩
    rw [hceq, herm_smul_left] at hvu
    exact huu ((mul_eq_zero.mp hvu).resolve_left hc0)
  let c0 : Fq2 q := -(herm v v) / herm u u
  have hc0_ne : c0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hvv) huu
  have hc0_fix : c0 ^ q = c0 := by simp only [c0, frob_div, frob_neg, herm_self_fixed]
  let R := Finset.univ.filter (fun x : Fq2 q => x ^ (q + 1) = c0)
  have hR_card : R.card = q + 1 := card_norm_fiber hc0_ne hc0_fix
  have hvec_ne : ∀ x : Fq2 q, x • u + v ≠ 0 := by
    intro x h0
    have : herm (x • u + v) v = 0 := by rw [h0, herm_zero_left]
    rw [herm_add_left, herm_smul_left, huv, mul_zero, zero_add] at this
    exact hvv this
  have hvec_herm : ∀ x : Fq2 q, herm (x • u + v) (x • u + v) =
      x ^ (q + 1) * herm u u + herm v v := by
    intro x
    rw [herm_add_left, herm_add_right, herm_add_right,
      herm_smul_left, herm_smul_right, herm_smul_left, herm_smul_right,
      huv, hvu, mul_zero, mul_zero, add_zero, zero_add, pow_succ]
    ring
  let g : Fq2 q → P2 q := fun x => normVec (x • u + v) (hvec_ne x)
  have hg_inj : Function.Injective g := by
    intro x y hEq
    rcases scale_of_normVec_eq hEq with ⟨t, _, hsm⟩
    have hv_eq : herm (y • u + v) v = t * herm (x • u + v) v := by
      rw [hsm, herm_smul_left]
    rw [herm_add_left, herm_smul_left, huv, mul_zero, zero_add,
      herm_add_left, herm_smul_left, huv, mul_zero, zero_add] at hv_eq
    have ht1 : t = 1 := by
      have : (1 - t) * herm v v = 0 := by linear_combination hv_eq
      have := (mul_eq_zero.mp this).resolve_right hvv
      linear_combination -this
    rw [ht1, one_smul] at hsm
    have hu_eq : herm (y • u + v) u = herm (x • u + v) u := by rw [hsm]
    rw [herm_add_left, herm_smul_left, hvu, add_zero,
      herm_add_left, herm_smul_left, hvu, add_zero] at hu_eq
    have : (y - x) * herm u u = 0 := by linear_combination hu_eq
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right huu)).symm
  let U := Finset.univ.filter (fun p : Unital q => herm p.1.1 w.1.1 = 0)
  have himg : U.image Subtype.val = R.image g := by
    ext p
    simp only [U, R, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨p, hp⟩, hpw, rfl⟩
      rcases (line_mem_iff_span hcuv huw hvw p.1).mp hpw with ⟨a, b, hab⟩
      have hb : b ≠ 0 := by
        intro hb0; subst hb0; simp only [zero_smul, add_zero] at hab
        have ha : a ≠ 0 := by intro h0; subst h0; simp at hab; exact p2_ne_zero p hab
        rw [hab, herm_smul_left, herm_smul_right] at hp
        exact huu ((mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left ha)).resolve_left
          (mt (frob_eq_zero_iff a).mp ha))
      refine ⟨a / b, ?_, ?_⟩
      · have h0 : herm ((a / b) • u + v) ((a / b) • u + v) = 0 := by
          have : b • ((a / b) • u + v) = p.1 := by
            ext i; have hi := congrFun hab i
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
            rw [hi]; field_simp [hb]
          rw [← this, herm_smul_left, herm_smul_right] at hp
          exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hb)).resolve_left
            (mt (frob_eq_zero_iff b).mp hb)
        rw [hvec_herm] at h0
        simp only [c0]; field_simp [huu]; linear_combination h0
      · rcases exists_scale_normVec ((a / b) • u + v) (hvec_ne (a / b)) with ⟨c, hc0, hceq⟩
        refine p2_eq_of_smul (mul_ne_zero hb hc0) ?_
        ext i; have hi := congrFun hab i; have hi2 := congrFun hceq i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi hi2 ⊢
        rw [hi, mul_assoc, ← hi2]; field_simp [hb]
    · rintro ⟨x, hx, rfl⟩
      rcases exists_scale_normVec (x • u + v) (hvec_ne x) with ⟨c, hc0, hceq⟩
      have hp0 : herm (g x).1 (g x).1 = 0 := by
        have hsum : herm (x • u + v) (x • u + v) = 0 := by
          rw [hvec_herm, hx]; simp only [c0]; field_simp [huu]; ring
        rw [hceq, herm_smul_left, herm_smul_right] at hsum
        exact (mul_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left hc0)).resolve_left
          (mt (frob_eq_zero_iff c).mp hc0)
      have hpw : herm (g x).1 w.1.1 = 0 := by
        have h0 : herm (x • u + v) w.1.1 = 0 := by
          rw [herm_add_left, herm_smul_left, huw, hvw, mul_zero, add_zero]
        rw [hceq, herm_smul_left] at h0
        exact (mul_eq_zero.mp h0).resolve_left hc0
      exact ⟨⟨g x, hp0⟩, hpw, rfl⟩
  have hcard_eq : U.card = R.card := by
    have h1 := congrArg Finset.card himg
    rw [Finset.card_image_of_injective _ Subtype.val_injective,
        Finset.card_image_of_injective _ hg_inj] at h1
    exact h1
  rw [hcard_eq, hR_card]

private lemma unique_inter_p2 {a₁ a₂ : P2 q} (hne : a₁ ≠ a₂) {b₁ b₂ : P2 q}
    (h11 : herm b₁.1 a₁.1 = 0) (h12 : herm b₁.1 a₂.1 = 0)
    (h21 : herm b₂.1 a₁.1 = 0) (h22 : herm b₂.1 a₂.1 = 0) : b₁ = b₂ := by
  have hc : cross a₁.1 a₂.1 ≠ 0 := (p2_ne_iff_cross_ne_zero a₁ a₂).mp hne
  have hprop : ∀ b : P2 q, herm b.1 a₁.1 = 0 → herm b.1 a₂.1 = 0 →
      cross b.1 (dualCross a₁.1 a₂.1) = 0 := by
    intro b hb1 hb2
    have h1 : (cross (frobVec a₁.1) (frobVec a₂.1)) 0 * b.1 1 -
        (cross (frobVec a₁.1) (frobVec a₂.1)) 1 * b.1 0 = 0 := by
      simp only [cross, frobVec, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [herm] at hb1 hb2
      linear_combination (a₂.1 2) ^ q * hb1 - (a₁.1 2) ^ q * hb2
    have h2 : (cross (frobVec a₁.1) (frobVec a₂.1)) 0 * b.1 2 -
        (cross (frobVec a₁.1) (frobVec a₂.1)) 2 * b.1 0 = 0 := by
      simp only [cross, frobVec, Matrix.cons_val_zero, Matrix.cons_val]
      simp only [herm] at hb1 hb2
      linear_combination -(a₂.1 1) ^ q * hb1 + (a₁.1 1) ^ q * hb2
    have h3 : (cross (frobVec a₁.1) (frobVec a₂.1)) 1 * b.1 2 -
        (cross (frobVec a₁.1) (frobVec a₂.1)) 2 * b.1 1 = 0 := by
      simp only [cross, frobVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      simp only [herm] at hb1 hb2
      linear_combination (a₂.1 0) ^ q * hb1 - (a₁.1 0) ^ q * hb2
    have hcf : dualCross a₁.1 a₂.1 = cross (frobVec a₁.1) (frobVec a₂.1) := by
      apply vec_ext <;>
        simp only [dualCross, frobVec, cross, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val, frob_sub, frob_mul]
    rw [hcf]
    apply vec_ext <;>
      simp only [cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply]
    · simp only [cross, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val] at h3
      linear_combination -h3
    · simp only [cross, Matrix.cons_val_zero, Matrix.cons_val] at h2
      linear_combination h2
    · simp only [cross, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
      linear_combination -h1
  have hdc : dualCross a₁.1 a₂.1 ≠ 0 := mt (dualCross_eq_zero_iff a₁.1 a₂.1).mp hc
  rcases cross_eq_zero_imp_smul (p2_ne_zero b₁) hdc (hprop b₁ h11 h12) with ⟨c₁, hc₁, heq₁⟩
  rcases cross_eq_zero_imp_smul (p2_ne_zero b₂) hdc (hprop b₂ h21 h22) with ⟨c₂, hc₂, heq₂⟩
  have hsm : b₂.1 = (c₂⁻¹ * c₁) • b₁.1 := by
    rw [mul_smul, ← heq₁, heq₂, inv_smul_smul₀ hc₂]
  exact p2_eq_of_smul (mul_ne_zero (inv_ne_zero hc₂) hc₁) hsm

private lemma exists_unique_secant_of_unital {p₁ p₂ : Unital q} (hne : p₁ ≠ p₂) :
    ∃! w : Secant q, herm p₁.1.1 w.1.1 = 0 ∧ herm p₂.1.1 w.1.1 = 0 := by
  have hpne : p₁.1 ≠ p₂.1 := fun h => hne (Subtype.ext h)
  have hc : cross p₁.1.1 p₂.1.1 ≠ 0 := (p2_ne_iff_cross_ne_zero p₁.1 p₂.1).mp hpne
  have hdc : dualCross p₁.1.1 p₂.1.1 ≠ 0 := mt (dualCross_eq_zero_iff p₁.1.1 p₂.1.1).mp hc
  let w0 : P2 q := normVec (dualCross p₁.1.1 p₂.1.1) hdc
  rcases exists_scale_normVec (dualCross p₁.1.1 p₂.1.1) hdc with ⟨c, hc0, hceq⟩
  have h1 : herm p₁.1.1 w0.1 = 0 := by
    have h0 := herm_left_dualCross p₁.1.1 p₂.1.1
    rw [hceq, herm_smul_right] at h0
    exact (mul_eq_zero.mp h0).resolve_left (mt (frob_eq_zero_iff c).mp hc0)
  have h2 : herm p₂.1.1 w0.1 = 0 := by
    have h0 := herm_right_dualCross p₁.1.1 p₂.1.1
    rw [hceq, herm_smul_right] at h0
    exact (mul_eq_zero.mp h0).resolve_left (mt (frob_eq_zero_iff c).mp hc0)
  have hw_sec : herm w0.1 w0.1 ≠ 0 := by
    intro hw0
    exact hpne ((tangent_unique_unital hw0 p₁.2 h1).trans (tangent_unique_unital hw0 p₂.2 h2).symm)
  refine ⟨⟨w0, hw_sec⟩, ⟨h1, h2⟩, ?_⟩
  rintro ⟨w, hw⟩ ⟨hw1, hw2⟩
  apply Subtype.ext
  have h1' : herm w0.1 p₁.1.1 = 0 := by rw [herm_symm, h1, frob_zero]
  have h2' : herm w0.1 p₂.1.1 = 0 := by rw [herm_symm, h2, frob_zero]
  have hw1' : herm w.1 p₁.1.1 = 0 := by rw [herm_symm, hw1, frob_zero]
  have hw2' : herm w.1 p₂.1.1 = 0 := by rw [herm_symm, hw2, frob_zero]
  exact (unique_inter_p2 hpne h1' h2' hw1' hw2').symm

private lemma card_unital : Fintype.card (Unital q) = q ^ 3 + 1 := by
  rcases exists_norm_neg_one (q := q) with ⟨α, hα⟩
  let p0 : Unital q := ⟨⟨![1, α, 0], Or.inl rfl⟩, by
    simp only [herm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      frob_one, frob_zero, mul_zero, add_zero, one_mul]
    rw [← pow_succ', hα, add_neg_cancel]⟩
  let C0 : Finset (Secant q) := Finset.univ.filter (fun w : Secant q => herm p0.1.1 w.1.1 = 0)
  have hC0 : C0.card = q ^ 2 := card_clique p0
  have hpart : (Finset.univ.erase p0 : Finset (Unital q)) =
      C0.biUnion (fun w => (Finset.univ.filter (fun p : Unital q => herm p.1.1 w.1.1 = 0)).erase p0) := by
    ext p
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion,
      Finset.mem_filter, true_and, C0]
    constructor
    · intro hne
      rcases exists_unique_secant_of_unital hne with ⟨w, ⟨hpw, hp0w⟩, _⟩
      exact ⟨w, hp0w, hne, hpw⟩
    · rintro ⟨_, _, hne, _⟩; exact hne
  have hdisj : Set.PairwiseDisjoint (C0 : Set (Secant q))
      (fun w => (Finset.univ.filter (fun p : Unital q => herm p.1.1 w.1.1 = 0)).erase p0) := by
    intro w₁ hw₁ w₂ hw₂ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    simp only [Finset.mem_coe, C0, Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂
    rcases exists_unique_secant_of_unital hp₁.1 with ⟨w, _, huniq⟩
    exact hne ((huniq w₁ ⟨hp₁.2, hw₁⟩).trans (huniq w₂ ⟨hp₂.2, hw₂⟩).symm)
  have hcard_erase : (Finset.univ.erase p0 : Finset (Unital q)).card = q ^ 3 := by
    rw [hpart, Finset.card_biUnion hdisj]
    have heach : ∀ w ∈ C0,
        ((Finset.univ.filter (fun p : Unital q => herm p.1.1 w.1.1 = 0)).erase p0).card = q := by
      intro w hw
      have hp0in : p0 ∈ Finset.univ.filter (fun p : Unital q => herm p.1.1 w.1.1 = 0) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (Finset.mem_filter.mp hw).2
      rw [Finset.card_erase_of_mem hp0in, card_secant_points w]
      omega
    rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul, hC0]; ring
  rw [Finset.card_erase_of_mem (Finset.mem_univ p0), Finset.card_univ] at hcard_erase
  have hpos : 0 < Fintype.card (Unital q) := Fintype.card_pos_iff.mpr ⟨p0⟩
  omega

private lemma card_secant : Fintype.card (Secant q) = q ^ 2 * (q ^ 2 - q + 1) := by
  have h1 := card_unital_add_secant (q := q)
  rw [card_unital] at h1
  have hq : 2 ≤ q := q_ge_two
  have hqle : q ≤ q ^ 2 := by nlinarith
  zify [hqle] at h1 ⊢
  linarith

private lemma no_onan_vectors {a b c : Vec q} (hdet : det3 a b c ≠ 0)
    (ha : herm a a = 0) (hb : herm b b = 0) (hc : herm c c = 0)
    (hab : herm (a + b) (a + b) = 0) (hac : herm (a + c) (a + c) = 0)
    (habc : herm (a + b + c) (a + b + c) = 0) : False := by
  have h1 : herm b a = -herm a b := by
    rw [herm_add_left, herm_add_right, herm_add_right, ha, hb, zero_add, add_zero] at hab
    exact eq_neg_of_add_eq_zero_right hab
  have h2 : herm c a = -herm a c := by
    rw [herm_add_left, herm_add_right, herm_add_right, ha, hc, zero_add, add_zero] at hac
    exact eq_neg_of_add_eq_zero_right hac
  have h3 : herm c b = -herm b c := by
    have hexp : herm (a + b + c) (a + b + c) =
        herm (a + b) (a + b) + herm a c + herm c a + herm b c + herm c b + herm c c := by
      simp only [herm_add_left, herm_add_right]; ring
    rw [hexp, hab, hc, h2] at habc
    have hbc : herm b c + herm c b = 0 := by linear_combination habc
    exact eq_neg_of_add_eq_zero_right hbc
  have hgram := det3_gram a b c
  rw [ha, hb, hc, h1, h2, h3] at hgram
  have hzero : det3 ![(0 : Fq2 q), herm a b, herm a c]
      ![-herm a b, 0, herm b c] ![-herm a c, -herm b c, 0] = 0 := by
    simp only [det3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
  rw [hzero] at hgram
  exact pow_ne_zero (q + 1) hdet hgram.symm

private lemma four_secants_three_concurrent {w₁ w₂ w₃ w₄ : Secant q}
    (h13 : w₁ ≠ w₃) (h24 : w₂ ≠ w₄)
    (p12 p13 p14 p23 p24 p34 : Unital q)
    (hp12 : herm p12.1.1 w₁.1.1 = 0 ∧ herm p12.1.1 w₂.1.1 = 0)
    (hp13 : herm p13.1.1 w₁.1.1 = 0 ∧ herm p13.1.1 w₃.1.1 = 0)
    (hp14 : herm p14.1.1 w₁.1.1 = 0 ∧ herm p14.1.1 w₄.1.1 = 0)
    (hp23 : herm p23.1.1 w₂.1.1 = 0 ∧ herm p23.1.1 w₃.1.1 = 0)
    (hp24 : herm p24.1.1 w₂.1.1 = 0 ∧ herm p24.1.1 w₄.1.1 = 0)
    (hp34 : herm p34.1.1 w₃.1.1 = 0 ∧ herm p34.1.1 w₄.1.1 = 0) :
    (∃ p : Unital q, herm p.1.1 w₁.1.1 = 0 ∧ herm p.1.1 w₂.1.1 = 0 ∧ herm p.1.1 w₃.1.1 = 0) ∨
    (∃ p : Unital q, herm p.1.1 w₁.1.1 = 0 ∧ herm p.1.1 w₂.1.1 = 0 ∧ herm p.1.1 w₄.1.1 = 0) ∨
    (∃ p : Unital q, herm p.1.1 w₁.1.1 = 0 ∧ herm p.1.1 w₃.1.1 = 0 ∧ herm p.1.1 w₄.1.1 = 0) ∨
    (∃ p : Unital q, herm p.1.1 w₂.1.1 = 0 ∧ herm p.1.1 w₃.1.1 = 0 ∧ herm p.1.1 w₄.1.1 = 0) := by
  by_contra hnone
  push Not at hnone
  rcases hnone with ⟨hn123, hn124, hn134, hn234⟩
  have hab_ne : p12.1 ≠ p14.1 := by
    intro heq; have : p12 = p14 := Subtype.ext heq; subst this
    exact hn124 p12 hp12.1 hp12.2 hp14.2
  have hdet_abc : det3 p12.1.1 p14.1.1 p23.1.1 ≠ 0 := by
    intro hdet0
    have hdet' : det3 p23.1.1 p12.1.1 p14.1.1 = 0 := by
      simp only [det3] at hdet0 ⊢; linear_combination hdet0
    rcases det3_eq_zero_imp_span ((p2_ne_iff_cross_ne_zero p12.1 p14.1).mp hab_ne) hdet' with
      ⟨r, s, hrs⟩
    have hc_w1 : herm p23.1.1 w₁.1.1 = 0 := by
      rw [hrs, herm_add_left, herm_smul_left, herm_smul_left, hp12.1, hp14.1,
        mul_zero, mul_zero, add_zero]
    exact hn123 p23 hc_w1 hp23.1 hp23.2
  let α := det3 p34.1.1 p14.1.1 p23.1.1 / det3 p12.1.1 p14.1.1 p23.1.1
  let β := det3 p12.1.1 p34.1.1 p23.1.1 / det3 p12.1.1 p14.1.1 p23.1.1
  let γ := det3 p12.1.1 p14.1.1 p34.1.1 / det3 p12.1.1 p14.1.1 p23.1.1
  have hf_eq : p34.1.1 = α • p12.1.1 + β • p14.1.1 + γ • p23.1.1 := cramer3 hdet_abc
  have hα_ne : α ≠ 0 := by
    intro hα0
    rw [hα0, zero_smul, zero_add] at hf_eq
    have : herm p23.1.1 w₄.1.1 = 0 := by
      have h0 : herm p34.1.1 w₄.1.1 = 0 := hp34.2
      rw [hf_eq, herm_add_left, herm_smul_left, herm_smul_left, hp14.2, mul_zero, zero_add] at h0
      have hγ0 : γ ≠ 0 := by
        intro hz; rw [hz, zero_smul, add_zero] at hf_eq
        have hβ0 : β ≠ 0 := by intro hb0; rw [hb0, zero_smul] at hf_eq; exact p2_ne_zero p34.1 hf_eq
        have : p14 = p34 := Subtype.ext (p2_eq_of_smul hβ0 hf_eq); subst this
        exact hn134 p14 hp14.1 hp34.1 hp14.2
      exact (mul_eq_zero.mp h0).resolve_left hγ0
    exact hn234 p23 hp23.1 hp23.2 this
  have hβ_ne : β ≠ 0 := by
    intro hβ0; rw [hβ0, zero_smul, add_zero] at hf_eq
    have : herm p34.1.1 w₂.1.1 = 0 := by
      rw [hf_eq, herm_add_left, herm_smul_left, herm_smul_left, hp12.2, hp23.1,
        mul_zero, mul_zero, add_zero]
    exact hn234 p34 this hp34.1 hp34.2
  have hγ_ne : γ ≠ 0 := by
    intro hγ0; rw [hγ0, zero_smul, add_zero] at hf_eq
    have : herm p34.1.1 w₁.1.1 = 0 := by
      rw [hf_eq, herm_add_left, herm_smul_left, herm_smul_left, hp12.1, hp14.1,
        mul_zero, mul_zero, add_zero]
    exact hn134 p34 this hp34.1 hp34.2
  let a' : Vec q := α • p12.1.1
  let b' : Vec q := β • p14.1.1
  let c' : Vec q := γ • p23.1.1
  have hdet' : det3 a' b' c' ≠ 0 := by
    have hmul : det3 a' b' c' = α * β * γ * det3 p12.1.1 p14.1.1 p23.1.1 := by
      simp only [a', b', c', det3, Pi.smul_apply, smul_eq_mul]; ring
    rw [hmul]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hα_ne hβ_ne) hγ_ne) hdet_abc
  have ha' : herm a' a' = 0 := by rw [herm_smul_left, herm_smul_right, p12.2, mul_zero, mul_zero]
  have hb' : herm b' b' = 0 := by rw [herm_smul_left, herm_smul_right, p14.2, mul_zero, mul_zero]
  have hc' : herm c' c' = 0 := by rw [herm_smul_left, herm_smul_right, p23.2, mul_zero, mul_zero]
  have habc' : herm (a' + b' + c') (a' + b' + c') = 0 := by
    have : a' + b' + c' = p34.1.1 := hf_eq.symm
    rw [this, p34.2]
  have hab'_ne : a' + b' ≠ 0 := by
    intro h0
    have : p34.1.1 = c' := by rw [hf_eq]; change a' + b' + c' = c'; rw [h0, zero_add]
    have : p23 = p34 := Subtype.ext (p2_eq_of_smul hγ_ne this); subst this
    exact hn234 p23 hp23.1 hp23.2 hp34.2
  have hab'_w1 : herm (a' + b') w₁.1.1 = 0 := by
    rw [herm_add_left, herm_smul_left, herm_smul_left, hp12.1, hp14.1, mul_zero, mul_zero, add_zero]
  have hab'_w3 : herm (a' + b') w₃.1.1 = 0 := by
    have h0 : herm (a' + b' + c') w₃.1.1 = 0 := by
      change herm (α • p12.1.1 + β • p14.1.1 + γ • p23.1.1) w₃.1.1 = 0
      rw [← hf_eq, hp34.1]
    rw [herm_add_left, herm_smul_left, hp23.2, mul_zero, add_zero] at h0; exact h0
  have hab' : herm (a' + b') (a' + b') = 0 := by
    rcases exists_scale_normVec (a' + b') hab'_ne with ⟨s, hs0, hseq⟩
    have hnw1 : herm (normVec (a' + b') hab'_ne).1 w₁.1.1 = 0 := by
      rw [hseq, herm_smul_left] at hab'_w1; exact (mul_eq_zero.mp hab'_w1).resolve_left hs0
    have hnw3 : herm (normVec (a' + b') hab'_ne).1 w₃.1.1 = 0 := by
      rw [hseq, herm_smul_left] at hab'_w3; exact (mul_eq_zero.mp hab'_w3).resolve_left hs0
    have heq := unique_inter_p2 (fun h => h13 (Subtype.ext h)) hnw1 hnw3 hp13.1 hp13.2
    rw [hseq, heq, herm_smul_left, herm_smul_right, p13.2, mul_zero, mul_zero]
  have hac'_ne : a' + c' ≠ 0 := by
    intro h0
    have : p34.1.1 = b' := by
      rw [hf_eq]; change a' + b' + c' = b'
      calc a' + b' + c' = (a' + c') + b' := by abel
        _ = b' := by rw [h0, zero_add]
    have : p14 = p34 := Subtype.ext (p2_eq_of_smul hβ_ne this); subst this
    exact hn134 p14 hp14.1 hp34.1 hp14.2
  have hac'_w2 : herm (a' + c') w₂.1.1 = 0 := by
    rw [herm_add_left, herm_smul_left, herm_smul_left, hp12.2, hp23.1, mul_zero, mul_zero, add_zero]
  have hac'_w4 : herm (a' + c') w₄.1.1 = 0 := by
    have h0 : herm (a' + b' + c') w₄.1.1 = 0 := by
      change herm (α • p12.1.1 + β • p14.1.1 + γ • p23.1.1) w₄.1.1 = 0
      rw [← hf_eq, hp34.2]
    have heq2 : a' + b' + c' = (a' + c') + b' := by abel
    rw [heq2, herm_add_left, herm_smul_left, hp14.2, mul_zero, add_zero] at h0; exact h0
  have hac' : herm (a' + c') (a' + c') = 0 := by
    rcases exists_scale_normVec (a' + c') hac'_ne with ⟨s, hs0, hseq⟩
    have hnw2 : herm (normVec (a' + c') hac'_ne).1 w₂.1.1 = 0 := by
      rw [hseq, herm_smul_left] at hac'_w2; exact (mul_eq_zero.mp hac'_w2).resolve_left hs0
    have hnw4 : herm (normVec (a' + c') hac'_ne).1 w₄.1.1 = 0 := by
      rw [hseq, herm_smul_left] at hac'_w4; exact (mul_eq_zero.mp hac'_w4).resolve_left hs0
    have heq := unique_inter_p2 (fun h => h24 (Subtype.ext h)) hnw2 hnw4 hp24.1 hp24.2
    rw [hseq, heq, herm_smul_left, herm_smul_right, p24.2, mul_zero, mul_zero]
  exact no_onan_vectors hdet' ha' hb' hc' hab' hac' habc'

private lemma bool_three_ne_false {a b c : Bool} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) : False := by
  cases a <;> cases b <;> cases c <;> simp at h1 h2 h3

private lemma unital_noK4 (col : Unital q × Secant q → Bool) :
    ¬ (SimpleGraph.completeGraph (Fin 4)).IsContained
        (bipGraphOf (fun (p : Unital q) (w : Secant q) => herm p.1.1 w.1.1 = 0) col) := by
  let G := bipGraphOf (fun (p : Unital q) (w : Secant q) => herm p.1.1 w.1.1 = 0) col
  rintro ⟨f⟩
  let w : Fin 4 → Secant q := fun i => f i
  have hadj : ∀ i j : Fin 4, i ≠ j → G.Adj (w i) (w j) := fun i j hij => f.toHom.map_rel hij
  have hne : ∀ i j : Fin 4, i ≠ j → w i ≠ w j := fun i j hij => (hadj i j hij).1
  rcases (hadj 0 1 (by decide)).2 with ⟨p12, h12a, h12b, _⟩
  rcases (hadj 0 2 (by decide)).2 with ⟨p13, h13a, h13b, _⟩
  rcases (hadj 0 3 (by decide)).2 with ⟨p14, h14a, h14b, _⟩
  rcases (hadj 1 2 (by decide)).2 with ⟨p23, h23a, h23b, _⟩
  rcases (hadj 1 3 (by decide)).2 with ⟨p24, h24a, h24b, _⟩
  rcases (hadj 2 3 (by decide)).2 with ⟨p34, h34a, h34b, _⟩
  have hconc := four_secants_three_concurrent
    (hne 0 2 (by decide)) (hne 1 3 (by decide))
    p12 p13 p14 p23 p24 p34
    ⟨h12a, h12b⟩ ⟨h13a, h13b⟩ ⟨h14a, h14b⟩ ⟨h23a, h23b⟩ ⟨h24a, h24b⟩ ⟨h34a, h34b⟩
  have htri : ∀ (u₁ u₂ u₃ : Secant q) (p : Unital q),
      G.Adj u₁ u₂ → G.Adj u₁ u₃ → G.Adj u₂ u₃ →
      herm p.1.1 u₁.1.1 = 0 → herm p.1.1 u₂.1.1 = 0 → herm p.1.1 u₃.1.1 = 0 → False := by
    intro u₁ u₂ u₃ p a12 a13 a23 hu1 hu2 hu3
    rcases a12 with ⟨ne12, q12, hq12a, hq12b, c12⟩
    rcases a13 with ⟨ne13, q13, hq13a, hq13b, c13⟩
    rcases a23 with ⟨ne23, q23, hq23a, hq23b, c23⟩
    have e12 : q12 = p := Subtype.ext (unique_inter_p2 (fun h => ne12 (Subtype.ext h)) hq12a hq12b hu1 hu2)
    have e13 : q13 = p := Subtype.ext (unique_inter_p2 (fun h => ne13 (Subtype.ext h)) hq13a hq13b hu1 hu3)
    have e23 : q23 = p := Subtype.ext (unique_inter_p2 (fun h => ne23 (Subtype.ext h)) hq23a hq23b hu2 hu3)
    rw [e12] at c12; rw [e13] at c13; rw [e23] at c23
    exact bool_three_ne_false c12 c13 c23
  rcases hconc with ⟨p, h1, h2, h3⟩ | ⟨p, h1, h2, h3⟩ | ⟨p, h1, h2, h3⟩ | ⟨p, h1, h2, h3⟩
  · exact htri (w 0) (w 1) (w 2) p (hadj 0 1 (by decide)) (hadj 0 2 (by decide))
      (hadj 1 2 (by decide)) h1 h2 h3
  · exact htri (w 0) (w 1) (w 3) p (hadj 0 1 (by decide)) (hadj 0 3 (by decide))
      (hadj 1 3 (by decide)) h1 h2 h3
  · exact htri (w 0) (w 2) (w 3) p (hadj 0 2 (by decide)) (hadj 0 3 (by decide))
      (hadj 2 3 (by decide)) h1 h2 h3
  · exact htri (w 1) (w 2) (w 3) p (hadj 1 2 (by decide)) (hadj 1 3 (by decide))
      (hadj 2 3 (by decide)) h1 h2 h3

private noncomputable def hermitianUnital (q : ℕ) [Fact q.Prime] : UnitalData q where
  U := Unital q
  W := Secant q
  instFinU := inferInstance
  instFinW := inferInstance
  inc p w := herm p.1.1 w.1.1 = 0
  cardU := card_unital
  cardW := card_secant
  secantPts := card_secant_points
  uniqueSecant := exists_unique_secant_of_unital
  uniqueUnital := fun {_ _} hne {_ _} h11 h12 h21 h22 =>
    Subtype.ext (unique_inter_p2 (fun h => hne (Subtype.ext h)) h11 h12 h21 h22)
  noK4 := unital_noK4

end Unital

/- ========================================================================= -/
/- Part 2: Clique structure of `H_q` (Lemmas 1 & 2, abstract over UnitalData)-/
/- ========================================================================= -/

section CliqueStructure

private lemma secant_card_bounds {q : ℕ} (hq : 4 ≤ q) :
    (8 : ℝ) ≤ ((q ^ 2 * (q ^ 2 - q + 1) : ℕ) : ℝ) ∧
    ((q ^ 2 * (q ^ 2 - q + 1) : ℕ) : ℝ) ≤ (q : ℝ) ^ 4 := by
  have hqle : q ≤ q ^ 2 := by nlinarith
  have hsub : q ^ 2 - q + 1 ≤ q ^ 2 := by omega
  have h1 : 8 ≤ q ^ 2 * (q ^ 2 - q + 1) := by
    have : 1 ≤ q ^ 2 - q + 1 := by omega
    nlinarith
  have h2 : q ^ 2 * (q ^ 2 - q + 1) ≤ q ^ 4 := by
    calc q ^ 2 * (q ^ 2 - q + 1) ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul_left _ hsub
      _ = q ^ 4 := by ring
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

private noncomputable def clique {q : ℕ} (D : UnitalData q) (p : D.U) : Finset D.W :=
  @Finset.filter D.W (fun w => D.inc p w) _ (@Finset.univ D.W D.instFinW)

private noncomputable def tSize {q : ℕ} (D : UnitalData q) (X : Finset D.W) (p : D.U) : ℕ :=
  (X ∩ clique D p).card

private lemma sum_tSize {q : ℕ} (D : UnitalData q) (X : Finset D.W) :
    letI := D.instFinU; letI := D.instFinW
    ∑ p : D.U, tSize D X p = (q + 1) * X.card := by
  let := D.instFinU; let := D.instFinW
  have h1 : ∑ p : D.U, tSize D X p =
      ∑ p : D.U, ∑ w ∈ X, if D.inc p w then 1 else 0 := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [tSize, clique, Finset.card_eq_sum_ones]
    rw [← Finset.sum_filter]
    congr 1; ext w; simp [Finset.mem_inter, Finset.mem_filter]
  rw [h1, Finset.sum_comm]
  have h2 : ∀ w ∈ X, (∑ p : D.U, if D.inc p w then 1 else 0) = q + 1 := by
    intro w _
    rw [← Finset.card_filter]
    exact D.secantPts w
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

private lemma v_large_le {q : ℕ} (D : UnitalData q) (X : Finset D.W) :
    letI := D.instFinU; letI := D.instFinW
    let L := Finset.univ.filter (fun p : D.U => Real.sqrt (2 * (X.card : ℝ)) < (tSize D X p : ℝ))
    (∑ p ∈ L, (tSize D X p : ℝ)) ≤ 2 * (X.card : ℝ) := by
  let := D.instFinU; let := D.instFinW
  intro L
  let vL : ℝ := ∑ p ∈ L, (tSize D X p : ℝ)
  by_cases hX0 : X.card = 0
  · have hXe : X = ∅ := Finset.card_eq_zero.mp hX0
    have hL0 : L = ∅ := by ext p; simp [L, tSize, hXe]
    simp [hX0, hL0]
  have hXpos : (0 : ℝ) < (X.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hX0)
  let deg : D.W → ℕ := fun x => (L.filter (fun p => x ∈ clique D p)).card
  have hsum_deg : ∑ x ∈ X, deg x = ∑ p ∈ L, tSize D X p := by
    have h1 : ∑ x ∈ X, deg x = ∑ x ∈ X, ∑ p ∈ L, if x ∈ clique D p then 1 else 0 := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [deg, Finset.sum_boole, Nat.cast_id]
    have h2 : ∑ p ∈ L, tSize D X p = ∑ p ∈ L, ∑ x ∈ X, if x ∈ clique D p then 1 else 0 := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp only [tSize, Finset.sum_boole, Nat.cast_id]
      rfl
    rw [h1, h2, Finset.sum_comm]
  have hpairs : ∑ x ∈ X, deg x * (deg x - 1) ≤ L.card * L.card := by
    have h1 : ∑ x ∈ X, deg x * (deg x - 1) =
        ∑ x ∈ X, ((L.filter (fun p => x ∈ clique D p)).offDiag).card := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.offDiag_card]
      change deg x * (deg x - 1) = deg x * deg x - deg x
      cases deg x with
      | zero => simp
      | succ m => simp only [Nat.add_sub_cancel]; rw [Nat.mul_succ]; omega
    have h2 : ∑ x ∈ X, ((L.filter (fun p => x ∈ clique D p)).offDiag).card =
        ∑ uv ∈ L.offDiag, (X.filter (fun x => x ∈ clique D uv.1 ∧ x ∈ clique D uv.2)).card := by
      have hl : ∑ x ∈ X, ((L.filter (fun p => x ∈ clique D p)).offDiag).card =
          ∑ x ∈ X, ∑ uv ∈ L.offDiag, if x ∈ clique D uv.1 ∧ x ∈ clique D uv.2 then 1 else 0 := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_boole, Nat.cast_id]
        congr 1; ext uv; simp [Finset.mem_offDiag, Finset.mem_filter]; tauto
      rw [hl, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun uv _ => ?_)
      rw [Finset.sum_boole, Nat.cast_id]
    have h3 : ∀ uv ∈ L.offDiag,
        (X.filter (fun x => x ∈ clique D uv.1 ∧ x ∈ clique D uv.2)).card ≤ 1 := by
      intro uv huv
      have hne : uv.1 ≠ uv.2 := (Finset.mem_offDiag.mp huv).2.2
      rw [Finset.card_le_one]
      intro w₁ hw₁ w₂ hw₂
      simp only [Finset.mem_filter, clique, Finset.mem_univ, true_and] at hw₁ hw₂
      rcases D.uniqueSecant hne with ⟨w, _, huniq⟩
      exact (huniq w₁ hw₁.2).trans (huniq w₂ hw₂.2).symm
    calc ∑ x ∈ X, deg x * (deg x - 1)
        = ∑ uv ∈ L.offDiag, (X.filter (fun x => x ∈ clique D uv.1 ∧ x ∈ clique D uv.2)).card := by
            rw [h1, h2]
      _ ≤ ∑ _uv ∈ L.offDiag, 1 := Finset.sum_le_sum h3
      _ = L.offDiag.card := by simp
      _ ≤ L.card * L.card := by rw [Finset.offDiag_card]; exact Nat.sub_le _ _
  have hpairsR : ∑ x ∈ X, ((deg x : ℝ) ^ 2 - (deg x : ℝ)) ≤ (L.card : ℝ) ^ 2 := by
    have hcast : (∑ x ∈ X, (deg x * (deg x - 1) : ℕ) : ℝ) ≤ ((L.card * L.card : ℕ) : ℝ) := by
      exact_mod_cast hpairs
    have hl : (∑ x ∈ X, (deg x * (deg x - 1) : ℕ) : ℝ) =
        ∑ x ∈ X, ((deg x : ℝ) ^ 2 - (deg x : ℝ)) := by
      push_cast
      refine Finset.sum_congr rfl (fun x _ => ?_)
      cases deg x with
      | zero => simp
      | succ m => push_cast; ring
    rw [hl] at hcast
    push_cast at hcast
    linarith
  have hvL_eq : ∑ x ∈ X, (deg x : ℝ) = vL := by
    have : (∑ x ∈ X, deg x : ℝ) = (∑ p ∈ L, tSize D X p : ℝ) := by exact_mod_cast hsum_deg
    simpa [vL] using this
  have hcs : vL ^ 2 ≤ (X.card : ℝ) * ∑ x ∈ X, (deg x : ℝ) ^ 2 := by
    rw [← hvL_eq]; exact sq_sum_le_card_mul_sum_sq
  have hsum_sq : ∑ x ∈ X, (deg x : ℝ) ^ 2 ≤ (L.card : ℝ) ^ 2 + vL := by
    have hsplit : ∑ x ∈ X, ((deg x : ℝ) ^ 2 - (deg x : ℝ)) =
        (∑ x ∈ X, (deg x : ℝ) ^ 2) - ∑ x ∈ X, (deg x : ℝ) := Finset.sum_sub_distrib _ _
    linarith
  by_contra hgt
  push Not at hgt
  have hLne : L.Nonempty := by
    by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have : vL = 0 := by simp [vL, hemp]
    linarith
  have hvL_lower : (L.card : ℝ) * Real.sqrt (2 * (X.card : ℝ)) < vL := by
    have hstrict := Finset.sum_lt_sum_of_nonempty hLne (fun p hp => (Finset.mem_filter.mp hp).2)
    simpa [vL, Finset.sum_const, nsmul_eq_mul] using hstrict
  have hsq_lower : (L.card : ℝ) ^ 2 * (2 * (X.card : ℝ)) < vL ^ 2 := by
    have hnn : 0 ≤ (L.card : ℝ) * Real.sqrt (2 * (X.card : ℝ)) := by positivity
    have hsq := mul_self_lt_mul_self hnn hvL_lower
    have hsr : Real.sqrt (2 * (X.card : ℝ)) * Real.sqrt (2 * (X.card : ℝ)) = 2 * (X.card : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    nlinarith
  nlinarith

private lemma cliques_small_or_medium {q : ℕ} (D : UnitalData q) (hq : 4 ≤ q)
    (X : Finset D.W) (hX : X.card = 2 ^ 24 * q ^ 2) :
    letI := D.instFinU; letI := D.instFinW
    let n : ℕ := Fintype.card D.W
    let m : ℕ := 2 ^ 24 * q ^ 2
    let thrL : ℝ := Real.sqrt (2 * (m : ℝ))
    let thrS : ℝ := thrL / Real.log (n : ℝ)
    let T := Finset.univ.filter (fun p : D.U => 2 ≤ tSize D X p)
    let S := T.filter (fun p => (tSize D X p : ℝ) ≤ thrS)
    let M := T.filter (fun p => thrS < (tSize D X p : ℝ) ∧ (tSize D X p : ℝ) ≤ thrL)
    (∑ p ∈ S, (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2) ≥ (m : ℝ) ^ 2 / (64 * (q : ℝ)) ∨
    (∑ p ∈ M, (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2) ≥
      (q : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ) / (16 * (Real.log (n : ℝ)) ^ 2) := by
  let := D.instFinU; let := D.instFinW
  intro n m thrL thrS T S M
  let L := T.filter (fun p => thrL < (tSize D X p : ℝ))
  have hqR : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hmR : (m : ℝ) = (2 ^ 24 : ℝ) * (q : ℝ) ^ 2 := by simp only [m]; push_cast; ring
  have ⟨hn_ge, hn_le⟩ : (8 : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (q : ℝ) ^ 4 := by
    have : n = q ^ 2 * (q ^ 2 - q + 1) := D.cardW
    rw [this]; exact secant_card_bounds hq
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlogn_le : Real.log (n : ℝ) ≤ 4 * (q : ℝ) := by
    have h1 : Real.log (n : ℝ) ≤ Real.log ((q : ℝ) ^ 4) := Real.log_le_log (by linarith) hn_le
    rw [Real.log_pow] at h1
    push_cast at h1
    have h2 : Real.log (q : ℝ) ≤ (q : ℝ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    linarith
  have hvT : ((q : ℝ) + 1) * (m : ℝ) - ((q : ℝ) ^ 3 + 1) ≤ ∑ p ∈ T, (tSize D X p : ℝ) := by
    have hall : (∑ p : D.U, (tSize D X p : ℝ)) = ((q : ℝ) + 1) * (m : ℝ) := by
      have := sum_tSize D X; rw [hX] at this; exact_mod_cast this
    have hcomp : ∑ p ∈ Finset.univ \ T, (tSize D X p : ℝ) ≤ (q : ℝ) ^ 3 + 1 := by
      have hle1 : ∀ p ∈ Finset.univ \ T, (tSize D X p : ℝ) ≤ 1 := by
        intro p hp
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, T, Finset.mem_filter] at hp
        exact_mod_cast (show tSize D X p ≤ 1 by omega)
      calc ∑ p ∈ Finset.univ \ T, (tSize D X p : ℝ)
          ≤ ∑ _p ∈ Finset.univ \ T, (1 : ℝ) := Finset.sum_le_sum hle1
        _ = ((Finset.univ \ T).card : ℝ) := by simp
        _ ≤ (Fintype.card D.U : ℝ) := by exact_mod_cast Finset.card_le_univ _
        _ = (q : ℝ) ^ 3 + 1 := by rw [D.cardU]; push_cast; ring
    have hsplit : ∑ p ∈ Finset.univ \ T, (tSize D X p : ℝ) + ∑ p ∈ T, (tSize D X p : ℝ) =
        ∑ p : D.U, (tSize D X p : ℝ) := Finset.sum_sdiff (Finset.subset_univ T)
    linarith
  have hvL : ∑ p ∈ L, (tSize D X p : ℝ) ≤ 2 * (m : ℝ) := by
    have hsub : L ⊆ Finset.univ.filter (fun p : D.U => Real.sqrt (2 * (X.card : ℝ)) < (tSize D X p : ℝ)) := by
      intro p hp
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, thrL, hX] at hp ⊢
      exact hp.2
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p => (tSize D X p : ℝ)) hsub
      (fun p _ _ => Nat.cast_nonneg _)
    have hvl := v_large_le D X
    have hle' := le_trans hle hvl
    simpa only [hX] using hle'
  have hT_split : ∑ p ∈ T, (tSize D X p : ℝ) =
      (∑ p ∈ S, (tSize D X p : ℝ)) + (∑ p ∈ M, (tSize D X p : ℝ)) + (∑ p ∈ L, (tSize D X p : ℝ)) := by
    have hSM : Disjoint S M := by
      rw [Finset.disjoint_left]; intro p h1 h2
      simp only [S, M, Finset.mem_filter] at h1 h2; linarith
    have hSL : Disjoint S L := by
      rw [Finset.disjoint_left]; intro p h1 h2
      simp only [S, L, Finset.mem_filter] at h1 h2
      have hln1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
        have : Real.exp 1 ≤ (n : ℝ) := le_trans (le_trans Real.exp_one_lt_d9.le (by norm_num)) hn_ge
        have := Real.log_le_log (Real.exp_pos 1) this
        rwa [Real.log_exp] at this
      have hts_le : thrS ≤ thrL := div_le_self (Real.sqrt_nonneg _) hln1
      linarith
    have hML : Disjoint M L := by
      rw [Finset.disjoint_left]; intro p h1 h2
      simp only [M, L, Finset.mem_filter] at h1 h2; linarith
    have hunion : T = (S ∪ M) ∪ L := by
      ext p; simp only [Finset.mem_union, S, M, L, Finset.mem_filter]
      constructor
      · intro hp
        by_cases h1 : (tSize D X p : ℝ) ≤ thrS
        · exact Or.inl (Or.inl ⟨hp, h1⟩)
        · push Not at h1
          by_cases h2 : (tSize D X p : ℝ) ≤ thrL
          · exact Or.inl (Or.inr ⟨hp, h1, h2⟩)
          · push Not at h2; exact Or.inr ⟨hp, h2⟩
      · rintro ((⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩) <;> exact hp
    rw [hunion, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hSL, hML⟩), Finset.sum_union hSM]
  have hvSM : ((q : ℝ) - 1) * (m : ℝ) - ((q : ℝ) ^ 3 + 1) ≤
      (∑ p ∈ S, (tSize D X p : ℝ)) + (∑ p ∈ M, (tSize D X p : ℝ)) := by linarith
  have hhalf_ge : (0.37 : ℝ) * (q : ℝ) * (m : ℝ) ≤
      (((q : ℝ) - 1) * (m : ℝ) - ((q : ℝ) ^ 3 + 1)) / 2 := by
    rw [hmR]; nlinarith [sq_nonneg ((q : ℝ) - 4)]
  by_cases hcase : (0.37 : ℝ) * (q : ℝ) * (m : ℝ) ≤ ∑ p ∈ S, (tSize D X p : ℝ)
  · left
    let vS : ℝ := ∑ p ∈ S, (tSize D X p : ℝ)
    have hvS_ge : (0.37 : ℝ) * (q : ℝ) * (m : ℝ) ≤ vS := hcase
    have hS_le : (S.card : ℝ) ≤ (q : ℝ) ^ 3 + 1 := by
      have : S.card ≤ Fintype.card D.U := Finset.card_le_univ S
      rw [D.cardU] at this; exact_mod_cast this
    have hS_pos : (0 : ℝ) < (S.card : ℝ) := by
      by_contra h0; push Not at h0
      have hSc : S.card = 0 := Nat.cast_eq_zero.mp (le_antisymm h0 (Nat.cast_nonneg _))
      have : vS = 0 := by simp [vS, Finset.card_eq_zero.mp hSc]
      rw [hmR] at hvS_ge; nlinarith
    have hcs : vS ^ 2 ≤ (S.card : ℝ) * ∑ p ∈ S, (tSize D X p : ℝ) ^ 2 := sq_sum_le_card_mul_sum_sq
    have heS : ∑ p ∈ S, (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2 =
        ((∑ p ∈ S, (tSize D X p : ℝ) ^ 2) - vS) / 2 := by
      have : ∑ p ∈ S, (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2 =
          (∑ p ∈ S, ((tSize D X p : ℝ) ^ 2 - (tSize D X p : ℝ))) / 2 := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun p _ => by ring)
      rw [this, Finset.sum_sub_distrib]
    rw [heS]
    have hmain : 2 * (S.card : ℝ) * (m : ℝ) ^ 2 ≤ 64 * (q : ℝ) * (vS ^ 2 - (S.card : ℝ) * vS) := by
      have hvS_sub : (0.36 : ℝ) * (q : ℝ) * (m : ℝ) ≤ vS - (S.card : ℝ) := by
        rw [hmR] at hvS_ge ⊢; nlinarith [sq_nonneg ((q : ℝ) - 4)]
      have hS_bound : (S.card : ℝ) ≤ (2 : ℝ) * (q : ℝ) ^ 3 := by nlinarith
      have hprod : (0.37 * (q : ℝ) * (m : ℝ)) * (0.36 * (q : ℝ) * (m : ℝ)) ≤
          vS * (vS - (S.card : ℝ)) :=
        mul_le_mul hvS_ge hvS_sub (by positivity) (by linarith)
      have hvs2 : vS ^ 2 - (S.card : ℝ) * vS = vS * (vS - (S.card : ℝ)) := by ring
      rw [hvs2]; nlinarith [sq_nonneg (m : ℝ)]
    have h2 : (S.card : ℝ) * (2 * (m : ℝ) ^ 2) ≤
        (S.card : ℝ) * (64 * (q : ℝ) * ((∑ p ∈ S, (tSize D X p : ℝ) ^ 2) - vS)) := by nlinarith
    have h3 : 2 * (m : ℝ) ^ 2 ≤ 64 * (q : ℝ) * ((∑ p ∈ S, (tSize D X p : ℝ) ^ 2) - vS) :=
      le_of_mul_le_mul_left h2 hS_pos
    rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  · right
    push Not at hcase
    let vM : ℝ := ∑ p ∈ M, (tSize D X p : ℝ)
    have hvM_ge : (0.37 : ℝ) * (q : ℝ) * (m : ℝ) ≤ vM := by linarith
    have hm_pos : (0 : ℝ) < (m : ℝ) := by rw [hmR]; positivity
    have hsqrt2_lt : Real.sqrt 2 < (1.42 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hthrL_eq : thrL = Real.sqrt 2 * Real.sqrt (m : ℝ) :=
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (m : ℝ)
    have hvM_le : vM ≤ (M.card : ℝ) * thrL := by
      calc vM = ∑ p ∈ M, (tSize D X p : ℝ) := rfl
        _ ≤ ∑ _p ∈ M, thrL := Finset.sum_le_sum (fun p hp => (Finset.mem_filter.mp hp).2.2)
        _ = (M.card : ℝ) * thrL := by simp
    have hMcard : (q : ℝ) * Real.sqrt (m : ℝ) / 4 ≤ (M.card : ℝ) := by
      have hsr_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
      have h1 : (0.37 : ℝ) * (q : ℝ) * (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) ≤
          (M.card : ℝ) * (Real.sqrt 2 * Real.sqrt (m : ℝ)) := by
        rw [Real.mul_self_sqrt hm_pos.le, ← hthrL_eq]; exact le_trans hvM_ge hvM_le
      have h2 : (0.37 : ℝ) * (q : ℝ) * Real.sqrt (m : ℝ) ≤ (M.card : ℝ) * Real.sqrt 2 := by
        have h1' : ((0.37 : ℝ) * (q : ℝ) * Real.sqrt (m : ℝ)) * Real.sqrt (m : ℝ) ≤
            ((M.card : ℝ) * Real.sqrt 2) * Real.sqrt (m : ℝ) := by linarith
        exact le_of_mul_le_mul_right h1' hsr_pos
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
    have hthrS_ge2 : (2 : ℝ) ≤ thrS := by
      have hsqrtm : Real.sqrt (m : ℝ) = (2 ^ 12 : ℝ) * (q : ℝ) := by
        rw [hmR, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith)]
        have : Real.sqrt (2 ^ 24 : ℝ) = (2 ^ 12 : ℝ) := by
          rw [show (2 ^ 24 : ℝ) = (2 ^ 12 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [this]
      rw [show thrS = Real.sqrt 2 * Real.sqrt (m : ℝ) / Real.log (n : ℝ) by rw [← hthrL_eq]]
      rw [le_div_iff₀ hlogn_pos, hsqrtm]
      have hsq2 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      nlinarith
    have heach : ∀ p ∈ M, (m : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2) ≤
        (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2 := by
      intro p hp
      have ht : thrS < (tSize D X p : ℝ) := (Finset.mem_filter.mp hp).2.1
      have ht2 : (2 : ℝ) ≤ (tSize D X p : ℝ) := le_trans hthrS_ge2 ht.le
      have h1 : (tSize D X p : ℝ) ^ 2 / 4 ≤ (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2 := by
        have hdiff : (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2 - (tSize D X p : ℝ) ^ 2 / 4 =
            (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 2) / 4 := by ring
        have hnn : 0 ≤ (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 2) / 4 :=
          div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr ht2)) (by norm_num)
        linarith only [hdiff, hnn]
      have h2 : thrS ^ 2 / 4 ≤ (tSize D X p : ℝ) ^ 2 / 4 :=
        div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (le_trans (by norm_num : (0 : ℝ) ≤ 2) hthrS_ge2) ht.le 2) (by norm_num)
      have hthrS_sq : thrS ^ 2 / 4 = (m : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2) := by
        simp only [thrS, thrL]; rw [div_pow, Real.sq_sqrt (by positivity)]; ring
      rw [← hthrS_sq]
      exact le_trans h2 h1
    calc ∑ p ∈ M, (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2
        ≥ ∑ _p ∈ M, ((m : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2)) := Finset.sum_le_sum heach
      _ = (M.card : ℝ) * ((m : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2)) := by simp
      _ ≥ ((q : ℝ) * Real.sqrt (m : ℝ) / 4) * ((m : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2)) := by gcongr
      _ = (q : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ) / (8 * (Real.log (n : ℝ)) ^ 2) := by ring
      _ ≥ (q : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ) / (16 * (Real.log (n : ℝ)) ^ 2) := by
          have hnum : 0 ≤ (q : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ) := by positivity
          have hden : 0 < 8 * (Real.log (n : ℝ)) ^ 2 := by positivity
          rw [ge_iff_le, div_le_div_iff₀ (by positivity) hden]; nlinarith

end CliqueStructure

/- ========================================================================= -/
/- Part 3: Finite-hypercube McDiarmid inequality                             -/
/- ========================================================================= -/

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

/- ========================================================================= -/
/- Part 3b: Concentration in `H_q*` and existence of pseudorandom `G_q*`     -/
/- ========================================================================= -/

section Pseudorandom

private noncomputable def dirEdgesGraph {V : Type*} (G : SimpleGraph V) (X : Finset V) : ℕ :=
  (X.offDiag.filter (fun uv => G.Adj uv.1 uv.2)).card

private noncomputable def dirEdgesClique {q : ℕ} (D : UnitalData q) (col : D.U × D.W → Bool)
    (X : Finset D.W) (p : D.U) : ℕ :=
  ((X ∩ clique D p).offDiag.filter (fun uv => col (p, uv.1) ≠ col (p, uv.2))).card

private lemma sum_dirEdgesClique_le {q : ℕ} (D : UnitalData q) (col : D.U × D.W → Bool)
    (X : Finset D.W) (U : Finset D.U) :
    ∑ p ∈ U, dirEdgesClique D col X p ≤ dirEdgesGraph (bipGraphOf D.inc col) X := by
  let := D.instFinU; let := D.instFinW
  let F : D.U → Finset (D.W × D.W) :=
    fun p => (X ∩ clique D p).offDiag.filter (fun uv => col (p, uv.1) ≠ col (p, uv.2))
  have hdisj : Set.PairwiseDisjoint (U : Set D.U) F := by
    intro p₁ _ p₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left, F, Finset.mem_filter, Finset.mem_offDiag,
      Finset.mem_inter, clique, Finset.mem_univ, true_and]
    rintro ⟨u, v⟩ ⟨⟨⟨_, hu1⟩, ⟨_, hv1⟩, huv⟩, _⟩ ⟨⟨⟨_, hu2⟩, ⟨_, hv2⟩, _⟩, _⟩
    exact hne (D.uniqueUnital huv hu1 hv1 hu2 hv2)
  have hsub : U.biUnion F ⊆ X.offDiag.filter (fun uv => (bipGraphOf D.inc col).Adj uv.1 uv.2) := by
    intro uv huv
    rcases Finset.mem_biUnion.mp huv with ⟨p, _, hp⟩
    simp only [F, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_inter, clique,
      Finset.mem_univ, true_and] at hp
    rw [Finset.mem_filter, Finset.mem_offDiag]
    exact ⟨⟨hp.1.1.1, hp.1.2.1.1, hp.1.2.2⟩, hp.1.2.2, p, hp.1.1.2, hp.1.2.1.2, hp.2⟩
  calc ∑ p ∈ U, dirEdgesClique D col X p
      = (U.biUnion F).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (X.offDiag.filter (fun uv => (bipGraphOf D.inc col).Adj uv.1 uv.2)).card :=
        Finset.card_le_card hsub

private lemma sum_bool_ne_pair {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι} (hab : a ≠ b) :
    (∑ ω : ι → Bool, if ω a ≠ ω b then (1 : ℝ) else 0) = (2 : ℝ) ^ Fintype.card ι / 2 := by
  let flip : (ι → Bool) ≃ (ι → Bool) :=
    { toFun := fun ω => Function.update ω a (!ω a)
      invFun := fun ω => Function.update ω a (!ω a)
      left_inv := fun ω => by ext x; by_cases hx : x = a <;> simp [hx]
      right_inv := fun ω => by ext x; by_cases hx : x = a <;> simp [hx] }
  let S1 := ∑ ω : ι → Bool, if ω a ≠ ω b then (1 : ℝ) else 0
  let S2 := ∑ ω : ι → Bool, if ω a = ω b then (1 : ℝ) else 0
  have heq : S1 = S2 := by
    simp only [S1, S2]
    rw [← Equiv.sum_comp flip]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    have hb : flip ω b = ω b := by simp [flip, hab.symm]
    have ha : flip ω a = !ω a := by simp [flip]
    rw [ha, hb]
    cases ω a <;> cases ω b <;> simp
  have htot : S1 + S2 = (2 : ℝ) ^ Fintype.card ι := by
    simp only [S1, S2, ← Finset.sum_add_distrib]
    have h1 : ∀ ω : ι → Bool,
        (if ω a ≠ ω b then (1 : ℝ) else 0) + (if ω a = ω b then (1 : ℝ) else 0) = 1 := by
      intro ω; split_ifs <;> simp_all
    rw [Finset.sum_congr rfl (fun ω _ => h1 ω)]
    simp
  linarith

private lemma avg_zU {q : ℕ} (D : UnitalData q) (X : Finset D.W) (U : Finset D.U) :
    letI := D.instFinU; letI := D.instFinW
    (∑ col : D.U × D.W → Bool, (∑ p ∈ U, (dirEdgesClique D col X p : ℝ)) / 2) /
        (2 : ℝ) ^ Fintype.card (D.U × D.W) =
      (∑ p ∈ U, (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2) / 2 := by
  let := D.instFinU; let := D.instFinW
  have h1 : (∑ col : D.U × D.W → Bool, (∑ p ∈ U, (dirEdgesClique D col X p : ℝ)) / 2) =
      (∑ p ∈ U, ∑ col : D.U × D.W → Bool, (dirEdgesClique D col X p : ℝ)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_comm]
  rw [h1]
  have hp_avg : ∀ p ∈ U,
      (∑ col : D.U × D.W → Bool, (dirEdgesClique D col X p : ℝ)) =
        ((X ∩ clique D p).offDiag.card : ℝ) * ((2 : ℝ) ^ Fintype.card (D.U × D.W) / 2) := by
    intro p _
    have hcard : ∀ col : D.U × D.W → Bool,
        (dirEdgesClique D col X p : ℝ) =
          ∑ uv ∈ (X ∩ clique D p).offDiag, if col (p, uv.1) ≠ col (p, uv.2) then (1 : ℝ) else 0 := by
      intro col; simp only [dirEdgesClique, Finset.sum_boole]
    rw [Finset.sum_congr rfl (fun col _ => hcard col), Finset.sum_comm]
    have hpair : ∀ uv ∈ (X ∩ clique D p).offDiag,
        (∑ col : D.U × D.W → Bool, if col (p, uv.1) ≠ col (p, uv.2) then (1 : ℝ) else 0) =
          (2 : ℝ) ^ Fintype.card (D.U × D.W) / 2 := by
      intro uv huv
      have hne : (p, uv.1) ≠ (p, uv.2) := fun h => (Finset.mem_offDiag.mp huv).2.2 (Prod.mk.inj h).2
      exact sum_bool_ne_pair hne
    rw [Finset.sum_congr rfl hpair, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hp_avg, ← Finset.sum_mul]
  have h2pos : (2 : ℝ) ^ Fintype.card (D.U × D.W) ≠ 0 := by positivity
  have hoff : ∀ p ∈ U, ((X ∩ clique D p).offDiag.card : ℝ) =
      (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) := by
    intro p _
    rw [Finset.offDiag_card]
    change (((tSize D X p) * (tSize D X p) - (tSize D X p) : ℕ) : ℝ) = _
    have hle : tSize D X p ≤ tSize D X p * tSize D X p := Nat.le_mul_self _
    rw [Nat.cast_sub hle]; push_cast; ring
  rw [Finset.sum_congr rfl hoff]
  field_simp [h2pos]
  rw [← Finset.sum_div]; ring

private lemma zU_lipschitz {q : ℕ} (D : UnitalData q) (X : Finset D.W) (U : Finset D.U)
    (col : D.U × D.W → Bool) (x : D.U × D.W) :
    |(∑ p ∈ U, (dirEdgesClique D col X p : ℝ)) / 2 -
     (∑ p ∈ U, (dirEdgesClique D (Function.update col x (!col x)) X p : ℝ)) / 2| ≤
      if x.1 ∈ U ∧ x.2 ∈ X ∩ clique D x.1 then (tSize D X x.1 : ℝ) - 1 else 0 := by
  let col' := Function.update col x (!col x)
  have hother : ∀ p ∈ U, p ≠ x.1 → dirEdgesClique D col X p = dirEdgesClique D col' X p := by
    intro p _ hp
    simp only [dirEdgesClique]; congr 1; ext uv
    simp only [Finset.mem_filter, col']
    have h1 : (p, uv.1) ≠ x := fun h => hp (congrArg Prod.fst h)
    have h2 : (p, uv.2) ≠ x := fun h => hp (congrArg Prod.fst h)
    simp [h1, h2]
  by_cases hmem : x.1 ∈ U ∧ x.2 ∈ X ∩ clique D x.1
  · rw [if_pos hmem]
    have hdiff_sum : (∑ p ∈ U, (dirEdgesClique D col X p : ℝ)) -
        (∑ p ∈ U, (dirEdgesClique D col' X p : ℝ)) =
        (dirEdgesClique D col X x.1 : ℝ) - (dirEdgesClique D col' X x.1 : ℝ) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single x.1]
      · intro p hp hne; rw [hother p hp hne, sub_self]
      · intro h; exact absurd hmem.1 h
    have hZ : (∑ p ∈ U, (dirEdgesClique D col X p : ℝ)) / 2 -
        (∑ p ∈ U, (dirEdgesClique D col' X p : ℝ)) / 2 =
        ((dirEdgesClique D col X x.1 : ℝ) - (dirEdgesClique D col' X x.1 : ℝ)) / 2 := by
      linarith
    rw [hZ, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    let A := X ∩ clique D x.1
    have hx2A : x.2 ∈ A := hmem.2
    let touch := A.offDiag.filter (fun uv => uv.1 = x.2 ∨ uv.2 = x.2)
    have htouch_card : touch.card ≤ 2 * (A.card - 1) := by
      have hsub : touch ⊆ ((A.erase x.2).image (fun y => (x.2, y))) ∪
          ((A.erase x.2).image (fun y => (y, x.2))) := by
        rintro ⟨u, v⟩ huv
        simp only [touch, Finset.mem_filter, Finset.mem_offDiag] at huv
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_erase]
        rcases huv.2 with rfl | rfl
        · exact Or.inl ⟨v, ⟨huv.1.2.2.symm, huv.1.2.1⟩, rfl⟩
        · exact Or.inr ⟨u, ⟨huv.1.2.2, huv.1.1⟩, rfl⟩
      calc touch.card
          ≤ (((A.erase x.2).image (fun y => (x.2, y))) ∪
              ((A.erase x.2).image (fun y => (y, x.2)))).card := Finset.card_le_card hsub
        _ ≤ ((A.erase x.2).image (fun y => (x.2, y))).card +
              ((A.erase x.2).image (fun y => (y, x.2))).card := Finset.card_union_le _ _
        _ ≤ (A.erase x.2).card + (A.erase x.2).card := by gcongr <;> exact Finset.card_image_le
        _ = 2 * (A.card - 1) := by rw [Finset.card_erase_of_mem hx2A]; omega
    have hle_diff : ∀ (c₁ c₂ : D.U × D.W → Bool),
        (∀ u v, u ≠ x.2 → v ≠ x.2 → (c₁ (x.1, u) ≠ c₁ (x.1, v) ↔ c₂ (x.1, u) ≠ c₂ (x.1, v))) →
        (dirEdgesClique D c₁ X x.1 : ℝ) - (dirEdgesClique D c₂ X x.1 : ℝ) ≤ 2 * ((A.card : ℝ) - 1) := by
      intro c₁ c₂ hagree
      have hsub : A.offDiag.filter (fun uv => c₁ (x.1, uv.1) ≠ c₁ (x.1, uv.2)) ⊆
          (A.offDiag.filter (fun uv => c₂ (x.1, uv.1) ≠ c₂ (x.1, uv.2))) ∪ touch := by
        rintro ⟨u, v⟩ huv
        simp only [Finset.mem_filter, Finset.mem_union, touch] at huv ⊢
        by_cases h1 : u = x.2 ∨ v = x.2
        · exact Or.inr ⟨huv.1, h1⟩
        · push Not at h1; exact Or.inl ⟨huv.1, (hagree u v h1.1 h1.2).mp huv.2⟩
      have hcard := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
      have hcard' : dirEdgesClique D c₁ X x.1 ≤ dirEdgesClique D c₂ X x.1 + 2 * (A.card - 1) :=
        le_trans hcard (Nat.add_le_add_left htouch_card _)
      have hA1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨x.2, hx2A⟩
      have hcast : (dirEdgesClique D c₁ X x.1 : ℝ) ≤
          (dirEdgesClique D c₂ X x.1 : ℝ) + (2 * (A.card - 1) : ℕ) := by exact_mod_cast hcard'
      rw [Nat.cast_mul, Nat.cast_sub hA1] at hcast
      push_cast at hcast; linarith
    have hag : ∀ u v, u ≠ x.2 → v ≠ x.2 →
        (col (x.1, u) ≠ col (x.1, v) ↔ col' (x.1, u) ≠ col' (x.1, v)) := by
      intro u v hu hv
      have h1 : (x.1, u) ≠ x := fun h => hu (congrArg Prod.snd h)
      have h2 : (x.1, v) ≠ x := fun h => hv (congrArg Prod.snd h)
      simp [col', h1, h2]
    have h1 := hle_diff col col' hag
    have h2 := hle_diff col' col (fun u v hu hv => (hag u v hu hv).symm)
    rw [abs_le]
    have htA : (A.card : ℝ) = (tSize D X x.1 : ℝ) := rfl
    rw [htA] at h1 h2
    constructor <;> linarith
  · rw [if_neg hmem]
    have heq : (∑ p ∈ U, (dirEdgesClique D col X p : ℝ)) =
        (∑ p ∈ U, (dirEdgesClique D col' X p : ℝ)) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      by_cases hpx : p = x.1
      · subst hpx
        have hx2 : x.2 ∉ X ∩ clique D x.1 := fun h => hmem ⟨hp, h⟩
        congr 1; simp only [dirEdgesClique]; congr 1; ext uv
        simp only [Finset.mem_filter, Finset.mem_offDiag, col']
        constructor
        · rintro ⟨⟨hu, hv, huv⟩, hne⟩
          have h1 : (x.1, uv.1) ≠ x := fun h => hx2 (by rw [← congrArg Prod.snd h]; exact hu)
          have h2 : (x.1, uv.2) ≠ x := fun h => hx2 (by rw [← congrArg Prod.snd h]; exact hv)
          exact ⟨⟨hu, hv, huv⟩, by simpa [h1, h2] using hne⟩
        · rintro ⟨⟨hu, hv, huv⟩, hne⟩
          have h1 : (x.1, uv.1) ≠ x := fun h => hx2 (by rw [← congrArg Prod.snd h]; exact hu)
          have h2 : (x.1, uv.2) ≠ x := fun h => hx2 (by rw [← congrArg Prod.snd h]; exact hv)
          exact ⟨⟨hu, hv, huv⟩, by simpa [h1, h2] using hne⟩
      · rw [hother p hp hpx]
    rw [heq, sub_self, abs_zero]

private lemma log_cube_bound {q : ℕ} (hq : 2 ^ 90 ≤ q) :
    (2 ^ 16 : ℝ) * (Real.log (q : ℝ)) ^ 3 < (q : ℝ) := by
  have hqR : (2 ^ 90 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  let y : ℝ := Real.sqrt (Real.sqrt (q : ℝ))
  have hypos : 0 < y := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hqpos)
  have hy4 : y ^ 4 = (q : ℝ) := by
    have h1 : y ^ 2 = Real.sqrt (q : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (q : ℝ)) ^ 2 := by rw [h1]
      _ = (q : ℝ) := Real.sq_sqrt hqpos.le
  have hlogy : Real.log (q : ℝ) ≤ 4 * y := by
    have h0 : Real.log (q : ℝ) = Real.log (y ^ 4) := by rw [hy4]
    rw [h0, Real.log_pow]
    push_cast
    have h1 := Real.log_le_sub_one_of_pos hypos
    linarith
  have hygt : (2 ^ 22 : ℝ) < y := by
    by_contra hle; push Not at hle
    have h4 : y ^ 4 ≤ (2 ^ 22 : ℝ) ^ 4 := pow_le_pow_left₀ hypos.le hle 4
    have : (2 ^ 22 : ℝ) ^ 4 < (2 ^ 90 : ℝ) := by norm_num
    linarith
  have hlogpos : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
  have hcube : (Real.log (q : ℝ)) ^ 3 ≤ 64 * y ^ 3 := by
    have h := pow_le_pow_left₀ hlogpos hlogy 3
    linarith [show (4 * y) ^ 3 = 64 * y ^ 3 by ring]
  have hy3pos : 0 < y ^ 3 := pow_pos hypos 3
  calc (2 ^ 16 : ℝ) * (Real.log (q : ℝ)) ^ 3
      ≤ (2 ^ 16 : ℝ) * (64 * y ^ 3) := by gcongr
    _ = (2 ^ 22 : ℝ) * y ^ 3 := by ring
    _ < y * y ^ 3 := by gcongr
    _ = y ^ 4 := by ring
    _ = (q : ℝ) := hy4

private lemma concentration_fixed_X {q : ℕ} (D : UnitalData q) (hq : 2 ^ 90 ≤ q)
    (X : Finset D.W) (hX : X.card = 2 ^ 24 * q ^ 2) :
    letI := D.instFinU; letI := D.instFinW
    let n : ℕ := Fintype.card D.W
    let m : ℕ := 2 ^ 24 * q ^ 2
    ((Finset.univ.filter (fun col : D.U × D.W → Bool =>
        (dirEdgesGraph (bipGraphOf D.inc col) X : ℝ) ≤ (2 ^ 41 : ℝ) * (q : ℝ) ^ 3)).card : ℝ) /
        (2 : ℝ) ^ Fintype.card (D.U × D.W) <
      ((n : ℝ) ^ m)⁻¹ := by
  let := D.instFinU; let := D.instFinW
  intro n m
  have hq4 : 4 ≤ q := by omega
  have hqR : (2 ^ 90 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hmR : (m : ℝ) = (2 ^ 24 : ℝ) * (q : ℝ) ^ 2 := by simp only [m]; push_cast; ring
  have hmpos : (0 : ℝ) < (m : ℝ) := by rw [hmR]; positivity
  have hsqrtm : Real.sqrt (m : ℝ) = (2 ^ 12 : ℝ) * (q : ℝ) := by
    rw [hmR, Real.sqrt_mul (by norm_num), Real.sqrt_sq hqpos.le]
    have : Real.sqrt (2 ^ 24 : ℝ) = (2 ^ 12 : ℝ) := by
      rw [show (2 ^ 24 : ℝ) = (2 ^ 12 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
  have ⟨hn_ge, hn_le⟩ : (8 : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (q : ℝ) ^ 4 := by
    have : n = q ^ 2 * (q ^ 2 - q + 1) := D.cardW
    rw [this]; exact secant_card_bounds hq4
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlogn_le : Real.log (n : ℝ) ≤ 4 * Real.log (q : ℝ) := by
    have h1 := Real.log_le_log (by linarith) hn_le
    rw [Real.log_pow] at h1; push_cast at h1; exact h1
  have hlogq_ge1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
    have : Real.exp 1 ≤ (q : ℝ) := le_trans (le_trans Real.exp_one_lt_d9.le (by norm_num)) hqR
    have := Real.log_le_log (Real.exp_pos 1) this
    rwa [Real.log_exp] at this
  have hcube := log_cube_bound hq
  have htail_of_U : ∀ (U : Finset D.U) (cMax : ℝ),
      (0 < cMax) →
      (∀ p ∈ U, 2 ≤ tSize D X p ∧ (tSize D X p : ℝ) ≤ cMax) →
      (2 ^ 40 : ℝ) * (q : ℝ) ^ 3 ≤
        (∑ p ∈ U, (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2) / 4 →
      (m : ℝ) * Real.log (n : ℝ) <
        (∑ p ∈ U, (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2) / (16 * cMax) →
      ((Finset.univ.filter (fun col : D.U × D.W → Bool =>
          (dirEdgesGraph (bipGraphOf D.inc col) X : ℝ) ≤ (2 ^ 41 : ℝ) * (q : ℝ) ^ 3)).card : ℝ) /
          (2 : ℝ) ^ Fintype.card (D.U × D.W) <
        ((n : ℝ) ^ m)⁻¹ := by
    intro U cMax hcMax hU heU_ge hexp_gt
    let eU : ℝ := ∑ p ∈ U, (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2
    let Z : (D.U × D.W → Bool) → ℝ :=
      fun col => (∑ p ∈ U, (dirEdgesClique D col X p : ℝ)) / 2
    let c : D.U × D.W → ℝ :=
      fun x => if x.1 ∈ U ∧ x.2 ∈ X ∩ clique D x.1 then (tSize D X x.1 : ℝ) - 1 else 0
    have hS2_eq : ∑ x : D.U × D.W, (c x) ^ 2 =
        ∑ p ∈ U, (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) ^ 2 := by
      rw [Fintype.sum_prod_type]
      have h1 : ∀ p : D.U,
          (∑ v : D.W, (c (p, v)) ^ 2) =
            if p ∈ U then (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) ^ 2 else 0 := by
        intro p
        by_cases hp : p ∈ U
        · rw [if_pos hp]
          have h2 : ∀ v : D.W,
              (c (p, v)) ^ 2 = if v ∈ X ∩ clique D p then ((tSize D X p : ℝ) - 1) ^ 2 else 0 := by
            intro v; simp only [c, hp, true_and]; split_ifs <;> simp
          simp_rw [h2, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]; rfl
        · rw [if_neg hp]
          exact Finset.sum_eq_zero (fun v _ => by simp [c, hp])
      simp_rw [h1, Finset.sum_ite_mem, Finset.univ_inter]
    have hS2_le : ∑ x : D.U × D.W, (c x) ^ 2 ≤ 2 * cMax * eU := by
      rw [hS2_eq]
      have hsum : 2 * cMax * eU =
          ∑ p ∈ U, cMax * ((tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1)) := by
        simp only [eU, Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
      rw [hsum]
      refine Finset.sum_le_sum (fun p hp => ?_)
      have h2 : (2 : ℝ) ≤ (tSize D X p : ℝ) := by exact_mod_cast (hU p hp).1
      have hle : (tSize D X p : ℝ) ≤ cMax := (hU p hp).2
      have hstep : (tSize D X p : ℝ) - 1 ≤ cMax := by linarith
      nlinarith
    have heU_pos : 0 < eU := by linarith [show (0 : ℝ) < (2 ^ 40 : ℝ) * (q : ℝ) ^ 3 by positivity]
    have hS2_pos : 0 < ∑ x : D.U × D.W, (c x) ^ 2 := by
      rw [hS2_eq]
      have hUne : U.Nonempty := by
        by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have : eU = 0 := by simp [eU, hemp]
        linarith
      refine Finset.sum_pos (fun p hp => ?_) hUne
      have h2 : (2 : ℝ) ≤ (tSize D X p : ℝ) := by exact_mod_cast (hU p hp).1
      have hsub1 : 0 < (tSize D X p : ℝ) - 1 := by linarith
      have htpos : 0 < (tSize D X p : ℝ) := by linarith
      positivity
    have hsub : Finset.univ.filter (fun col : D.U × D.W → Bool =>
          (dirEdgesGraph (bipGraphOf D.inc col) X : ℝ) ≤ (2 ^ 41 : ℝ) * (q : ℝ) ^ 3) ⊆
        Finset.univ.filter (fun col : D.U × D.W → Bool =>
          Z col ≤ eU / 2 - eU / 4) := by
      intro col hcol
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcol ⊢
      have hle : ∑ p ∈ U, (dirEdgesClique D col X p : ℝ) ≤
          (dirEdgesGraph (bipGraphOf D.inc col) X : ℝ) := by
        exact_mod_cast sum_dirEdgesClique_le D col X U
      simp only [Z]; linarith
    have htail := mcdiarmid_lower_tail Z c (zU_lipschitz D X U) (by linarith : 0 ≤ eU / 4) hS2_pos
    have havg : (∑ col : D.U × D.W → Bool, Z col) / (2 : ℝ) ^ Fintype.card (D.U × D.W) = eU / 2 :=
      avg_zU D X U
    rw [havg] at htail
    have hcard_le : ((Finset.univ.filter (fun col : D.U × D.W → Bool =>
          (dirEdgesGraph (bipGraphOf D.inc col) X : ℝ) ≤ (2 ^ 41 : ℝ) * (q : ℝ) ^ 3)).card : ℝ) /
          (2 : ℝ) ^ Fintype.card (D.U × D.W) ≤
        Real.exp (-2 * (eU / 4) ^ 2 / ∑ x : D.U × D.W, (c x) ^ 2) := by
      refine le_trans ?_ htail; gcongr
    have hexp_le : -2 * (eU / 4) ^ 2 / (∑ x : D.U × D.W, (c x) ^ 2) <
        -((m : ℝ) * Real.log (n : ℝ)) := by
      have h1 : eU / (16 * cMax) ≤ 2 * (eU / 4) ^ 2 / ∑ x : D.U × D.W, (c x) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) hS2_pos]; nlinarith
      have hneg : -2 * (eU / 4) ^ 2 / (∑ x : D.U × D.W, (c x) ^ 2) =
          -(2 * (eU / 4) ^ 2 / (∑ x : D.U × D.W, (c x) ^ 2)) := by ring
      rw [hneg]
      linarith
    have hnm : Real.exp (-((m : ℝ) * Real.log (n : ℝ))) = ((n : ℝ) ^ m)⁻¹ := by
      rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity)]
    calc ((Finset.univ.filter (fun col : D.U × D.W → Bool =>
            (dirEdgesGraph (bipGraphOf D.inc col) X : ℝ) ≤ (2 ^ 41 : ℝ) * (q : ℝ) ^ 3)).card : ℝ) /
            (2 : ℝ) ^ Fintype.card (D.U × D.W)
        ≤ Real.exp (-2 * (eU / 4) ^ 2 / ∑ x : D.U × D.W, (c x) ^ 2) := hcard_le
      _ < Real.exp (-((m : ℝ) * Real.log (n : ℝ))) := Real.exp_lt_exp.mpr hexp_le
      _ = ((n : ℝ) ^ m)⁻¹ := hnm
  rcases cliques_small_or_medium D hq4 X hX with hS | hM
  · let T := Finset.univ.filter (fun p : D.U => 2 ≤ tSize D X p)
    let S := T.filter (fun p => (tSize D X p : ℝ) ≤ Real.sqrt (2 * (m : ℝ)) / Real.log (n : ℝ))
    have hS' : (m : ℝ) ^ 2 / (64 * (q : ℝ)) ≤
        ∑ p ∈ S, (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2 := hS
    refine htail_of_U S (Real.sqrt (2 * (m : ℝ)) / Real.log (n : ℝ)) (by positivity)
      (fun p hp => by simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hp; exact hp) ?_ ?_
    · have : (m : ℝ) ^ 2 / (64 * (q : ℝ)) / 4 = (2 ^ 40 : ℝ) * (q : ℝ) ^ 3 := by
        rw [hmR]; field_simp [hqpos.ne']; ring
      linarith
    · have hsqrt2 : Real.sqrt (2 * (m : ℝ)) = Real.sqrt 2 * ((2 ^ 12 : ℝ) * (q : ℝ)) := by
        rw [Real.sqrt_mul (by norm_num), hsqrtm]
      have hsq2_lt : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have hden_pos : 0 < 16 * (Real.sqrt (2 * (m : ℝ)) / Real.log (n : ℝ)) := by positivity
      rw [lt_div_iff₀ hden_pos]
      have h1 : (m : ℝ) * Real.log (n : ℝ) * (16 * (Real.sqrt (2 * (m : ℝ)) / Real.log (n : ℝ))) =
          16 * (m : ℝ) * Real.sqrt (2 * (m : ℝ)) := by field_simp [hlogn_pos.ne']
      rw [h1, hsqrt2]
      have h2 : 16 * (m : ℝ) * (Real.sqrt 2 * ((2 ^ 12 : ℝ) * (q : ℝ))) <
          (m : ℝ) ^ 2 / (64 * (q : ℝ)) := by
        rw [lt_div_iff₀ (by positivity), hmR]; nlinarith
      linarith
  · let T := Finset.univ.filter (fun p : D.U => 2 ≤ tSize D X p)
    let M := T.filter (fun p => Real.sqrt (2 * (m : ℝ)) / Real.log (n : ℝ) < (tSize D X p : ℝ) ∧
        (tSize D X p : ℝ) ≤ Real.sqrt (2 * (m : ℝ)))
    have hM' : (q : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ) / (16 * (Real.log (n : ℝ)) ^ 2) ≤
        ∑ p ∈ M, (tSize D X p : ℝ) * ((tSize D X p : ℝ) - 1) / 2 := hM
    refine htail_of_U M (Real.sqrt (2 * (m : ℝ))) (by positivity)
      (fun p hp => by simp only [M, T, Finset.mem_filter, Finset.mem_univ, true_and] at hp; exact ⟨hp.1, hp.2.2⟩) ?_ ?_
    · have h1 : (q : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ) / (16 * (Real.log (n : ℝ)) ^ 2) / 4 =
          (2 ^ 30 : ℝ) * (q : ℝ) ^ 4 / (Real.log (n : ℝ)) ^ 2 := by
        rw [hsqrtm, hmR]; ring
      have h2 : (Real.log (n : ℝ)) ^ 2 ≤ 16 * (Real.log (q : ℝ)) ^ 3 := by
        have hsq := mul_self_le_mul_self hlogn_pos.le hlogn_le
        have h3 : (Real.log (q : ℝ)) ^ 2 ≤ (Real.log (q : ℝ)) ^ 3 := by
          nlinarith [sq_nonneg (Real.log (q : ℝ))]
        nlinarith
      have h3 : (2 ^ 40 : ℝ) * (q : ℝ) ^ 3 ≤ (2 ^ 30 : ℝ) * (q : ℝ) ^ 4 / (Real.log (n : ℝ)) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [pow_pos hqpos 3]
      linarith
    · have hsqrt2 : Real.sqrt (2 * (m : ℝ)) = Real.sqrt 2 * Real.sqrt (m : ℝ) :=
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (m : ℝ)
      have hsq2_lt : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have hden_pos : 0 < 16 * Real.sqrt (2 * (m : ℝ)) := by positivity
      rw [lt_div_iff₀ hden_pos]
      have hlogn_cube : (Real.log (n : ℝ)) ^ 3 ≤ 64 * (Real.log (q : ℝ)) ^ 3 := by
        have h := pow_le_pow_left₀ hlogn_pos.le hlogn_le 3
        linarith [show (4 * Real.log (q : ℝ)) ^ 3 = 64 * (Real.log (q : ℝ)) ^ 3 by ring]
      have hq_gt : 512 * (Real.log (n : ℝ)) ^ 3 < (q : ℝ) := by linarith
      have hstep : (m : ℝ) * Real.log (n : ℝ) * (16 * Real.sqrt (2 * (m : ℝ))) <
          (q : ℝ) * (m : ℝ) * Real.sqrt (m : ℝ) / (16 * (Real.log (n : ℝ)) ^ 2) := by
        rw [lt_div_iff₀ (by positivity), hsqrt2]
        have hms : 0 < (m : ℝ) * Real.sqrt (m : ℝ) := by positivity
        have h1 : (m : ℝ) * Real.log (n : ℝ) * (16 * (Real.sqrt 2 * Real.sqrt (m : ℝ))) *
            (16 * (Real.log (n : ℝ)) ^ 2) =
            (256 * Real.sqrt 2 * (Real.log (n : ℝ)) ^ 3) * ((m : ℝ) * Real.sqrt (m : ℝ)) := by ring
        rw [h1]
        have h2 : 256 * Real.sqrt 2 * (Real.log (n : ℝ)) ^ 3 < (q : ℝ) := by
          have := pow_nonneg hlogn_pos.le 3; nlinarith
        nlinarith
      linarith

private lemma exists_pseudorandom_col {q : ℕ} (D : UnitalData q) (hq : 2 ^ 90 ≤ q) :
    ∃ col : D.U × D.W → Bool,
      ∀ X : Finset D.W, 2 ^ 24 * q ^ 2 ≤ X.card →
        (X.card : ℝ) ^ 2 / (128 * (q : ℝ)) ≤ (dirEdgesGraph (bipGraphOf D.inc col) X : ℝ) := by
  let := D.instFinU; let := D.instFinW
  let n : ℕ := Fintype.card D.W
  let m : ℕ := 2 ^ 24 * q ^ 2
  have hn_eq : n = q ^ 2 * (q ^ 2 - q + 1) := D.cardW
  have hm_le_n : m ≤ n := by
    rw [hn_eq]
    have hq_sq : 2 ^ 24 ≤ q ^ 2 - q + 1 := by
      have h1 : q ≤ q ^ 2 := by nlinarith
      have h2 : 2 ^ 24 + q ≤ q ^ 2 + 1 := by nlinarith
      omega
    have hmul := Nat.mul_le_mul_left (q ^ 2) hq_sq
    simpa only [m, mul_comm] using hmul
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  let bad : Finset D.W → Finset (D.U × D.W → Bool) := fun X =>
    Finset.univ.filter (fun col =>
      (dirEdgesGraph (bipGraphOf D.inc col) X : ℝ) ≤ (2 ^ 41 : ℝ) * (q : ℝ) ^ 3)
  let setsM := Finset.powersetCard m (Finset.univ : Finset D.W)
  have hsetsM_nonempty : setsM.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hc := congrArg Finset.card hemp
    rw [Finset.card_powersetCard, Finset.card_univ, Finset.card_empty] at hc
    exact (Nat.choose_pos hm_le_n).ne' hc
  have hsum_bad :
      (∑ X ∈ setsM, ((bad X).card : ℝ) / (2 : ℝ) ^ Fintype.card (D.U × D.W)) < 1 := by
    have hlt : ∑ X ∈ setsM, ((bad X).card : ℝ) / (2 : ℝ) ^ Fintype.card (D.U × D.W) <
        ∑ _X ∈ setsM, ((n : ℝ) ^ m)⁻¹ := by
      refine Finset.sum_lt_sum_of_nonempty hsetsM_nonempty (fun X hX => ?_)
      exact concentration_fixed_X D hq X (Finset.mem_powersetCard.mp hX).2
    have hchoose_le : (setsM.card : ℝ) ≤ (n : ℝ) ^ m := by
      rw [Finset.card_powersetCard, Finset.card_univ]
      exact_mod_cast nat_choose_le_pow n m
    have hnm_pos : (0 : ℝ) < (n : ℝ) ^ m := by
      have : 0 < n := lt_of_lt_of_le (by positivity) hm_le_n
      positivity
    calc ∑ X ∈ setsM, ((bad X).card : ℝ) / (2 : ℝ) ^ Fintype.card (D.U × D.W)
        < ∑ _X ∈ setsM, ((n : ℝ) ^ m)⁻¹ := hlt
      _ = (setsM.card : ℝ) * ((n : ℝ) ^ m)⁻¹ := by simp
      _ ≤ (n : ℝ) ^ m * ((n : ℝ) ^ m)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hnm_pos.ne'
  have hunion_lt : (setsM.biUnion bad).card < Fintype.card (D.U × D.W → Bool) := by
    have h1 : ((setsM.biUnion bad).card : ℝ) ≤ ∑ X ∈ setsM, ((bad X).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : (∑ X ∈ setsM, ((bad X).card : ℝ)) < (2 : ℝ) ^ Fintype.card (D.U × D.W) := by
      rw [← Finset.sum_div, div_lt_one (by positivity)] at hsum_bad; exact hsum_bad
    have hcard_fun : (Fintype.card (D.U × D.W → Bool) : ℝ) = (2 : ℝ) ^ Fintype.card (D.U × D.W) := by
      rw [Fintype.card_fun, Fintype.card_bool]; push_cast; rfl
    exact_mod_cast lt_of_le_of_lt h1 (hcard_fun ▸ h2)
  have hex_good : (Finset.univ \ setsM.biUnion bad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hle := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hemp)
    rw [Finset.card_univ] at hle; omega
  rcases hex_good with ⟨col, hcol⟩
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion, not_exists,
    not_and] at hcol
  have hgood_m : ∀ Y : Finset D.W, Y.card = m →
      (2 ^ 41 : ℝ) * (q : ℝ) ^ 3 ≤ (dirEdgesGraph (bipGraphOf D.inc col) Y : ℝ) := by
    intro Y hY
    have hnb := hcol Y (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ Y, hY⟩)
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnb
    exact hnb.le
  refine ⟨col, fun X hX => ?_⟩
  let subM := Finset.powersetCard m X
  let EX := X.offDiag.filter (fun uv => (bipGraphOf D.inc col).Adj uv.1 uv.2)
  have hdouble : ∑ Y ∈ subM, dirEdgesGraph (bipGraphOf D.inc col) Y =
      EX.card * (X.card - 2).choose (m - 2) := by
    have h1 : ∑ Y ∈ subM, dirEdgesGraph (bipGraphOf D.inc col) Y =
        ∑ Y ∈ subM, ∑ uv ∈ EX, if uv.1 ∈ Y ∧ uv.2 ∈ Y then 1 else 0 := by
      refine Finset.sum_congr rfl (fun Y hY => ?_)
      have hYX : Y ⊆ X := (Finset.mem_powersetCard.mp hY).1
      rw [Finset.sum_boole, Nat.cast_id]
      simp only [dirEdgesGraph]
      congr 1; ext uv
      simp only [EX, Finset.mem_filter, Finset.mem_offDiag]
      exact ⟨fun ⟨⟨h1, h2, hne⟩, hadj⟩ => ⟨⟨⟨hYX h1, hYX h2, hne⟩, hadj⟩, h1, h2⟩,
             fun ⟨⟨⟨_, _, hne⟩, hadj⟩, h1, h2⟩ => ⟨⟨h1, h2, hne⟩, hadj⟩⟩
    rw [h1, Finset.sum_comm]
    have heach : ∀ uv ∈ EX,
        (∑ Y ∈ subM, if uv.1 ∈ Y ∧ uv.2 ∈ Y then 1 else 0) = (X.card - 2).choose (m - 2) := by
      intro uv huv
      simp only [EX, Finset.mem_filter, Finset.mem_offDiag] at huv
      rcases huv with ⟨⟨huX, hvX, huv_ne⟩, _⟩
      rw [Finset.sum_boole, Nat.cast_id]
      let X' := (X.erase uv.1).erase uv.2
      have hX'_card : X'.card = X.card - 2 := by
        have hv1 : uv.2 ∈ X.erase uv.1 := Finset.mem_erase.mpr ⟨huv_ne.symm, hvX⟩
        rw [Finset.card_erase_of_mem hv1, Finset.card_erase_of_mem huX]; omega
      have hbij : (subM.filter (fun Y => uv.1 ∈ Y ∧ uv.2 ∈ Y)).card =
          (Finset.powersetCard (m - 2) X').card := by
        refine Finset.card_bij (fun Y _ => (Y.erase uv.1).erase uv.2) ?_ ?_ ?_
        · intro Y hY
          simp only [Finset.mem_filter, subM, Finset.mem_powersetCard] at hY
          rw [Finset.mem_powersetCard]
          refine ⟨fun z hz => ?_, ?_⟩
          · simp only [X', Finset.mem_erase] at hz ⊢; exact ⟨hz.1, hz.2.1, hY.1.1 hz.2.2⟩
          · have hvY : uv.2 ∈ Y.erase uv.1 := Finset.mem_erase.mpr ⟨huv_ne.symm, hY.2.2⟩
            rw [Finset.card_erase_of_mem hvY, Finset.card_erase_of_mem hY.2.1, hY.1.2]; omega
        · intro Y₁ hY₁ Y₂ hY₂ hEq
          simp only [Finset.mem_filter, subM, Finset.mem_powersetCard] at hY₁ hY₂
          ext z
          by_cases hz1 : z = uv.1
          · subst hz1; simp [hY₁.2.1, hY₂.2.1]
          · by_cases hz2 : z = uv.2
            · subst hz2; simp [hY₁.2.2, hY₂.2.2]
            · have := congrArg (z ∈ ·) hEq; simp [Finset.mem_erase, hz1, hz2] at this; exact this
        · intro Z hZ
          rw [Finset.mem_powersetCard] at hZ
          let Y := insert uv.1 (insert uv.2 Z)
          have h1Z : uv.1 ∉ Z := fun h => by have := hZ.1 h; simp [X'] at this
          have h2Z : uv.2 ∉ Z := fun h => by have := hZ.1 h; simp [X'] at this
          refine ⟨Y, ?_, ?_⟩
          · simp only [Finset.mem_filter, subM, Finset.mem_powersetCard]
            refine ⟨⟨fun z hz => ?_, ?_⟩, Finset.mem_insert_self _ _,
              Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
            · simp only [Y, Finset.mem_insert] at hz
              rcases hz with rfl | rfl | hz
              · exact huX
              · exact hvX
              · have := hZ.1 hz; simp only [X', Finset.mem_erase] at this; exact this.2.2
            · have h1i : uv.1 ∉ insert uv.2 Z := by simp [huv_ne, h1Z]
              rw [Finset.card_insert_of_notMem h1i, Finset.card_insert_of_notMem h2Z, hZ.2]
              have hm2 : 2 ≤ m := by simp only [m]; nlinarith
              omega
          · ext z; simp only [Y, Finset.mem_erase, Finset.mem_insert]
            constructor
            · rintro ⟨hz2, hz1, rfl | rfl | hz⟩
              · exact absurd rfl hz1
              · exact absurd rfl hz2
              · exact hz
            · intro hz; exact ⟨fun h => h2Z (h ▸ hz), fun h => h1Z (h ▸ hz), Or.inr (Or.inr hz)⟩
      rw [hbij, Finset.card_powersetCard, hX'_card]
    rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul]
  have hlower : ((X.card.choose m : ℕ) : ℝ) * ((2 ^ 41 : ℝ) * (q : ℝ) ^ 3) ≤
      (dirEdgesGraph (bipGraphOf D.inc col) X : ℝ) * (((X.card - 2).choose (m - 2) : ℕ) : ℝ) := by
    have hsum_ge : ((subM.card : ℕ) : ℝ) * ((2 ^ 41 : ℝ) * (q : ℝ) ^ 3) ≤
        ∑ Y ∈ subM, (dirEdgesGraph (bipGraphOf D.inc col) Y : ℝ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum (fun Y hY => hgood_m Y (Finset.mem_powersetCard.mp hY).2)
    rw [Finset.card_powersetCard] at hsum_ge
    have hsum_eq : (∑ Y ∈ subM, (dirEdgesGraph (bipGraphOf D.inc col) Y : ℝ)) =
        (dirEdgesGraph (bipGraphOf D.inc col) X : ℝ) * (((X.card - 2).choose (m - 2) : ℕ) : ℝ) := by
      have : (∑ Y ∈ subM, dirEdgesGraph (bipGraphOf D.inc col) Y : ℝ) =
          ((EX.card * (X.card - 2).choose (m - 2) : ℕ) : ℝ) := by exact_mod_cast hdouble
      simpa [dirEdgesGraph, EX] using this
    linarith
  have hm2 : 2 ≤ m := by simp only [m]; nlinarith
  have hX2 : 2 ≤ X.card := le_trans hm2 hX
  have hchoose_id : m * (m - 1) * X.card.choose m =
      X.card * (X.card - 1) * (X.card - 2).choose (m - 2) := by
    have hstep : ∀ a b : ℕ, (b + 1) * (a + 1).choose (b + 1) = (a + 1) * a.choose b := by
      intro a b
      by_cases hba : b ≤ a
      · rw [Nat.choose_succ_succ, mul_add, mul_comm (b + 1) (a.choose (b + 1)),
          Nat.choose_succ_right_eq, mul_comm (a.choose b) (a - b), ← add_mul]
        congr 1; omega
      · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp
    have h1 := hstep (X.card - 1) (m - 1)
    have h2 := hstep (X.card - 2) (m - 2)
    have hm1 : (m - 1) + 1 = m := by omega
    have hm2' : (m - 2) + 1 = m - 1 := by omega
    have hX1 : (X.card - 1) + 1 = X.card := by omega
    have hX2' : (X.card - 2) + 1 = X.card - 1 := by omega
    rw [hm1, hX1] at h1; rw [hm2', hX2'] at h2
    calc m * (m - 1) * X.card.choose m
        = (m * X.card.choose m) * (m - 1) := by ring
      _ = X.card * ((m - 1) * (X.card - 1).choose (m - 1)) := by rw [h1]; ring
      _ = X.card * (X.card - 1) * (X.card - 2).choose (m - 2) := by rw [h2]; ring
  have hchoose_pos : (0 : ℝ) < (((X.card - 2).choose (m - 2) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : m - 2 ≤ X.card - 2)
  have hratio : ((X.card : ℝ) ^ 2 / (m : ℝ) ^ 2) * (((X.card - 2).choose (m - 2) : ℕ) : ℝ) ≤
      ((X.card.choose m : ℕ) : ℝ) := by
    have hcast : (m : ℝ) * ((m : ℝ) - 1) * ((X.card.choose m : ℕ) : ℝ) =
        (X.card : ℝ) * ((X.card : ℝ) - 1) * (((X.card - 2).choose (m - 2) : ℕ) : ℝ) := by
      have : ((m * (m - 1) * X.card.choose m : ℕ) : ℝ) =
          ((X.card * (X.card - 1) * (X.card - 2).choose (m - 2) : ℕ) : ℝ) := by
        exact_mod_cast hchoose_id
      simp only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ m by omega),
        Nat.cast_sub (show 1 ≤ X.card by omega), Nat.cast_one] at this
      exact this
    have hXm : (m : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hX
    have hm_ge2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
    have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    have hineq : (X.card : ℝ) ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) ≤
        (m : ℝ) ^ 2 * ((X.card : ℝ) * ((X.card : ℝ) - 1)) := by
      have hdiff : (m : ℝ) ^ 2 * ((X.card : ℝ) * ((X.card : ℝ) - 1)) -
          (X.card : ℝ) ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) =
          (m : ℝ) * (X.card : ℝ) * ((X.card : ℝ) - (m : ℝ)) := by ring
      have hnn : 0 ≤ (m : ℝ) * (X.card : ℝ) * ((X.card : ℝ) - (m : ℝ)) :=
        mul_nonneg (mul_nonneg hm_pos.le (Nat.cast_nonneg _)) (sub_nonneg.mpr hXm)
      linarith
    have hstep : ((X.card : ℝ) ^ 2 / (m : ℝ) ^ 2) * (((X.card - 2).choose (m - 2) : ℕ) : ℝ) *
        ((m : ℝ) * ((m : ℝ) - 1)) ≤
        ((X.card.choose m : ℕ) : ℝ) * ((m : ℝ) * ((m : ℝ) - 1)) := by
      have h1 : ((X.card : ℝ) ^ 2 / (m : ℝ) ^ 2) * (((X.card - 2).choose (m - 2) : ℕ) : ℝ) *
          ((m : ℝ) * ((m : ℝ) - 1)) * (m : ℝ) ^ 2 ≤
          ((X.card.choose m : ℕ) : ℝ) * ((m : ℝ) * ((m : ℝ) - 1)) * (m : ℝ) ^ 2 := by
        have hl : ((X.card : ℝ) ^ 2 / (m : ℝ) ^ 2) * (((X.card - 2).choose (m - 2) : ℕ) : ℝ) *
            ((m : ℝ) * ((m : ℝ) - 1)) * (m : ℝ) ^ 2 =
            (X.card : ℝ) ^ 2 * ((m : ℝ) * ((m : ℝ) - 1)) * (((X.card - 2).choose (m - 2) : ℕ) : ℝ) := by
          field_simp [hm_pos.ne']
        have hr : ((X.card.choose m : ℕ) : ℝ) * ((m : ℝ) * ((m : ℝ) - 1)) * (m : ℝ) ^ 2 =
            (m : ℝ) ^ 2 * ((X.card : ℝ) * ((X.card : ℝ) - 1)) * (((X.card - 2).choose (m - 2) : ℕ) : ℝ) := by
          linear_combination (m : ℝ) ^ 2 * hcast
        rw [hl, hr]
        exact mul_le_mul_of_nonneg_right hineq hchoose_pos.le
      exact le_of_mul_le_mul_right h1 (pow_pos hm_pos 2)
    exact le_of_mul_le_mul_right hstep (mul_pos hm_pos hm1_pos)
  have hprod : ((X.card : ℝ) ^ 2 / (m : ℝ) ^ 2) * ((2 ^ 41 : ℝ) * (q : ℝ) ^ 3) *
      (((X.card - 2).choose (m - 2) : ℕ) : ℝ) ≤
      (dirEdgesGraph (bipGraphOf D.inc col) X : ℝ) * (((X.card - 2).choose (m - 2) : ℕ) : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hratio (by positivity : (0 : ℝ) ≤ (2 ^ 41 : ℝ) * (q : ℝ) ^ 3)
    linarith
  have hfin := le_of_mul_le_mul_right hprod hchoose_pos
  have heq_const : (X.card : ℝ) ^ 2 / (m : ℝ) ^ 2 * ((2 ^ 41 : ℝ) * (q : ℝ) ^ 3) =
      (X.card : ℝ) ^ 2 / (128 * (q : ℝ)) := by
    have hmR : (m : ℝ) = (2 ^ 24 : ℝ) * (q : ℝ) ^ 2 := by simp only [m]; push_cast; ring
    rw [hmR]; field_simp [hqpos.ne']; ring
  linarith

end Pseudorandom

/- ========================================================================= -/
/- Part 4: Kleitman–Winston graph container lemma (Proposition 4)            -/
/- ========================================================================= -/

section Containers

variable {V : Type*} [LinearOrder V]

private noncomputable def degIn (G : SimpleGraph V) (A : Finset V) (v : V) : ℕ :=
  (A.filter (fun u => G.Adj v u)).card

private lemma sum_degIn_eq_dirEdges (G : SimpleGraph V) (A : Finset V) :
    ∑ v ∈ A, degIn G A v = dirEdgesGraph G A := by
  simp only [degIn, dirEdgesGraph]
  have hpart : A.offDiag.filter (fun uv => G.Adj uv.1 uv.2) =
      A.biUnion (fun v => (A.filter (fun u => G.Adj v u)).image (fun u => (v, u))) := by
    ext ⟨v, u⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨⟨hv, hu, _⟩, hadj⟩; exact ⟨v, hv, u, ⟨hu, hadj⟩, rfl⟩
    · rintro ⟨v', hv', u', ⟨hu', hadj⟩, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      exact ⟨⟨hv', hu', G.ne_of_adj hadj⟩, hadj⟩
  have hdisj : Set.PairwiseDisjoint (A : Set V)
      (fun v => (A.filter (fun u => G.Adj v u)).image (fun u => (v, u))) := by
    intro v₁ _ v₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro ⟨a, b⟩ ⟨_, _, h1⟩ ⟨_, _, h2⟩
    exact hne ((Prod.mk.inj h1).1.trans (Prod.mk.inj h2).1.symm)
  rw [hpart, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl (fun v _ =>
    (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)).symm)

private noncomputable def maxDegVertex (G : SimpleGraph V) (A : Finset V) (hA : A.Nonempty) : V :=
  (A.filter (fun v => degIn G A v = A.sup' hA (degIn G A))).min' (by
    rcases Finset.exists_mem_eq_sup' hA (degIn G A) with ⟨v, hv, hveq⟩
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hveq.symm⟩⟩)

private lemma maxDegVertex_mem (G : SimpleGraph V) (A : Finset V) (hA : A.Nonempty) :
    maxDegVertex G A hA ∈ A := by
  unfold maxDegVertex
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1

private lemma degIn_le_maxDegVertex (G : SimpleGraph V) (A : Finset V) (hA : A.Nonempty)
    {u : V} (hu : u ∈ A) : degIn G A u ≤ degIn G A (maxDegVertex G A hA) := by
  have hmax : degIn G A (maxDegVertex G A hA) = A.sup' hA (degIn G A) := by
    unfold maxDegVertex
    exact (Finset.mem_filter.mp
      (Finset.min'_mem (A.filter (fun v => degIn G A v = A.sup' hA (degIn G A))) _)).2
  rw [hmax]
  exact Finset.le_sup' (degIn G A) hu

private noncomputable def kwFingerprint (G : SimpleGraph V) (R : ℕ) (I A : Finset V) : Finset V :=
  if h : A.card ≤ R then ∅
  else
    let hne : A.Nonempty := Finset.card_pos.mp (by omega)
    let v := maxDegVertex G A hne
    if v ∈ I then
      insert v (kwFingerprint G R I ((A.erase v) \ (A.filter (fun u => G.Adj v u))))
    else
      kwFingerprint G R I (A.erase v)
termination_by A.card
decreasing_by
  · exact lt_of_le_of_lt (Finset.card_le_card Finset.sdiff_subset)
      (Finset.card_erase_lt_of_mem (maxDegVertex_mem G A hne))
  · exact Finset.card_erase_lt_of_mem (maxDegVertex_mem G A hne)

private noncomputable def kwContainer (G : SimpleGraph V) (R : ℕ) (S A : Finset V) : Finset V :=
  if h : A.card ≤ R then A
  else
    let hne : A.Nonempty := Finset.card_pos.mp (by omega)
    let v := maxDegVertex G A hne
    if v ∈ S then
      kwContainer G R S ((A.erase v) \ (A.filter (fun u => G.Adj v u)))
    else
      kwContainer G R S (A.erase v)
termination_by A.card
decreasing_by
  · exact lt_of_le_of_lt (Finset.card_le_card Finset.sdiff_subset)
      (Finset.card_erase_lt_of_mem (maxDegVertex_mem G A hne))
  · exact Finset.card_erase_lt_of_mem (maxDegVertex_mem G A hne)

private lemma kwFingerprint_subset (G : SimpleGraph V) (R : ℕ) (I : Finset V) :
    ∀ A : Finset V, kwFingerprint G R I A ⊆ I ∩ A := by
  intro A
  induction hcard : A.card using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    unfold kwFingerprint
    by_cases hR : A.card ≤ R
    · simp only [hR, ↓reduceDIte]; exact Finset.empty_subset _
    · simp only [hR, ↓reduceDIte]
      let hne : A.Nonempty := Finset.card_pos.mp (by omega)
      let v := maxDegVertex G A hne
      by_cases hv : v ∈ I
      · simp only [v, hv, ↓reduceIte]
        let A' := (A.erase v) \ (A.filter (fun u => G.Adj v u))
        have hlt : A'.card < n := by
          rw [← hcard]
          exact lt_of_le_of_lt (Finset.card_le_card Finset.sdiff_subset)
            (Finset.card_erase_lt_of_mem (maxDegVertex_mem G A hne))
        have hsub := ih A'.card hlt A' rfl
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact Finset.mem_inter.mpr ⟨hv, maxDegVertex_mem G A hne⟩
        · have hmem := Finset.mem_inter.mp (hsub hx')
          exact Finset.mem_inter.mpr ⟨hmem.1, Finset.erase_subset v A (Finset.sdiff_subset hmem.2)⟩
      · simp only [v, hv, ↓reduceIte]
        have hlt : (A.erase v).card < n := by
          rw [← hcard]; exact Finset.card_erase_lt_of_mem (maxDegVertex_mem G A hne)
        have hsub := ih (A.erase v).card hlt (A.erase v) rfl
        intro x hx
        have hmem := Finset.mem_inter.mp (hsub hx)
        exact Finset.mem_inter.mpr ⟨hmem.1, Finset.erase_subset v A hmem.2⟩

private lemma kwContainer_card_le (G : SimpleGraph V) (R : ℕ) (S : Finset V) :
    ∀ A : Finset V, (kwContainer G R S A).card ≤ R := by
  intro A
  induction hcard : A.card using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    unfold kwContainer
    by_cases hR : A.card ≤ R
    · simp only [hR, ↓reduceDIte]
    · simp only [hR, ↓reduceDIte]
      let hne : A.Nonempty := Finset.card_pos.mp (by omega)
      let v := maxDegVertex G A hne
      by_cases hv : v ∈ S
      · simp only [v, hv, ↓reduceIte]
        let A' := (A.erase v) \ (A.filter (fun u => G.Adj v u))
        have hlt : A'.card < n := by
          rw [← hcard]
          exact lt_of_le_of_lt (Finset.card_le_card Finset.sdiff_subset)
            (Finset.card_erase_lt_of_mem (maxDegVertex_mem G A hne))
        exact ih A'.card hlt A' rfl
      · simp only [v, hv, ↓reduceIte]
        have hlt : (A.erase v).card < n := by
          rw [← hcard]; exact Finset.card_erase_lt_of_mem (maxDegVertex_mem G A hne)
        exact ih (A.erase v).card hlt (A.erase v) rfl

private lemma kw_indep_subset_container (G : SimpleGraph V) (R : ℕ) (I : Finset V)
    (hind : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) :
    ∀ (A S : Finset V), S ∩ A = kwFingerprint G R I A →
      (I ∩ A) \ S ⊆ kwContainer G R S A := by
  intro A
  induction hcard : A.card using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    intro S hSA
    unfold kwContainer
    by_cases hR : A.card ≤ R
    · simp only [hR, ↓reduceDIte]
      intro x hx; exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).2
    · simp only [hR, ↓reduceDIte]
      let hne : A.Nonempty := Finset.card_pos.mp (by omega)
      let v := maxDegVertex G A hne
      have hvA : v ∈ A := maxDegVertex_mem G A hne
      have hfp : kwFingerprint G R I A =
          if v ∈ I then insert v (kwFingerprint G R I ((A.erase v) \ (A.filter (fun u => G.Adj v u))))
          else kwFingerprint G R I (A.erase v) := by
        conv_lhs => unfold kwFingerprint
        simp only [hR, ↓reduceDIte, v]
      by_cases hvI : v ∈ I
      · rw [if_pos hvI] at hfp
        have hvS : v ∈ S := by
          have : v ∈ S ∩ A := by rw [hSA, hfp]; exact Finset.mem_insert_self _ _
          exact (Finset.mem_inter.mp this).1
        simp only [v, hvS, ↓reduceIte]
        let A' := (A.erase v) \ (A.filter (fun u => G.Adj v u))
        have hA'sub : A' ⊆ A := Finset.sdiff_subset.trans (Finset.erase_subset v A)
        have hvA' : v ∉ A' := fun h => (Finset.mem_erase.mp (Finset.sdiff_subset h)).1 rfl
        have hSA' : S ∩ A' = kwFingerprint G R I A' := by
          ext x
          have hsub' := kwFingerprint_subset G R I A'
          constructor
          · intro hx
            have hxSA : x ∈ S ∩ A := Finset.mem_inter.mpr
              ⟨(Finset.mem_inter.mp hx).1, hA'sub (Finset.mem_inter.mp hx).2⟩
            rw [hSA, hfp] at hxSA
            rcases Finset.mem_insert.mp hxSA with rfl | hx'
            · exact absurd (Finset.mem_inter.mp hx).2 hvA'
            · exact hx'
          · intro hx
            have hxA' : x ∈ A' := (Finset.mem_inter.mp (hsub' hx)).2
            have hxS : x ∈ S := by
              have : x ∈ S ∩ A := by rw [hSA, hfp]; exact Finset.mem_insert_of_mem hx
              exact (Finset.mem_inter.mp this).1
            exact Finset.mem_inter.mpr ⟨hxS, hxA'⟩
        have hlt : A'.card < n := by
          rw [← hcard]
          exact lt_of_le_of_lt (Finset.card_le_card Finset.sdiff_subset)
            (Finset.card_erase_lt_of_mem hvA)
        have hrec := ih A'.card hlt A' rfl S hSA'
        intro x hx
        refine hrec ?_
        simp only [Finset.mem_sdiff, Finset.mem_inter] at hx ⊢
        refine ⟨⟨hx.1.1, ?_⟩, hx.2⟩
        simp only [A', Finset.mem_sdiff, Finset.mem_erase, Finset.mem_filter]
        exact ⟨⟨fun h => hx.2 (h ▸ hvS), hx.1.2⟩, fun ⟨_, hadj⟩ => hind v hvI x hx.1.1 hadj⟩
      · rw [if_neg hvI] at hfp
        have hvS : v ∉ S := by
          intro hvs
          have : v ∈ kwFingerprint G R I (A.erase v) := by
            rw [← hfp, ← hSA]; exact Finset.mem_inter.mpr ⟨hvs, hvA⟩
          have := (Finset.mem_inter.mp (kwFingerprint_subset G R I (A.erase v) this)).2
          exact (Finset.mem_erase.mp this).1 rfl
        simp only [v, hvS, ↓reduceIte]
        have hSA' : S ∩ (A.erase v) = kwFingerprint G R I (A.erase v) := by
          ext x
          have hsub' := kwFingerprint_subset G R I (A.erase v)
          constructor
          · intro hx
            have hxSA : x ∈ S ∩ A := Finset.mem_inter.mpr
              ⟨(Finset.mem_inter.mp hx).1, Finset.erase_subset v A (Finset.mem_inter.mp hx).2⟩
            rwa [hSA, hfp] at hxSA
          · intro hx
            have hxA' : x ∈ A.erase v := (Finset.mem_inter.mp (hsub' hx)).2
            have hxS : x ∈ S := by
              have : x ∈ S ∩ A := by rw [hSA, hfp]; exact hx
              exact (Finset.mem_inter.mp this).1
            exact Finset.mem_inter.mpr ⟨hxS, hxA'⟩
        have hlt : (A.erase v).card < n := by
          rw [← hcard]; exact Finset.card_erase_lt_of_mem hvA
        have hrec := ih (A.erase v).card hlt (A.erase v) rfl S hSA'
        intro x hx
        refine hrec ?_
        simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_erase] at hx ⊢
        exact ⟨⟨hx.1.1, fun h => hvI (h ▸ hx.1.1), hx.1.2⟩, hx.2⟩

private lemma kwFingerprint_card_le (G : SimpleGraph V) (R : ℕ) (α : ℝ)
    (hα1 : α ≤ 1)
    (hden : ∀ X : Finset V, R ≤ X.card → α * (X.card : ℝ) ^ 2 ≤ (dirEdgesGraph G X : ℝ))
    (I : Finset V) :
    ∀ (A : Finset V) (k : ℕ), (1 - α) ^ k * (A.card : ℝ) ≤ (R : ℝ) →
      (kwFingerprint G R I A).card ≤ k := by
  intro A
  induction hcard : A.card using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    intro k hk
    rw [← hcard] at hk
    unfold kwFingerprint
    by_cases hR : A.card ≤ R
    · simp only [hR, ↓reduceDIte]; simp
    · simp only [hR, ↓reduceDIte]
      have hRA : R < A.card := by omega
      let hne : A.Nonempty := Finset.card_pos.mp (by omega)
      let v := maxDegVertex G A hne
      have hvA : v ∈ A := maxDegVertex_mem G A hne
      by_cases hv : v ∈ I
      · simp only [v, hv, ↓reduceIte]
        have hkpos : 0 < k := by
          by_contra hk0
          have hk0' : k = 0 := by omega
          subst hk0'
          simp only [pow_zero, one_mul] at hk
          have : (R : ℝ) < (A.card : ℝ) := by exact_mod_cast hRA
          linarith
        obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        let A' := (A.erase v) \ (A.filter (fun u => G.Adj v u))
        have hlt : A'.card < n := by
          rw [← hcard]
          exact lt_of_le_of_lt (Finset.card_le_card Finset.sdiff_subset)
            (Finset.card_erase_lt_of_mem hvA)
        have hdeg_ge : α * (A.card : ℝ) ≤ (degIn G A v : ℝ) := by
          have hsum : ∑ u ∈ A, degIn G A u ≤ A.card * degIn G A v := by
            calc ∑ u ∈ A, degIn G A u
                ≤ ∑ _u ∈ A, degIn G A v := Finset.sum_le_sum (fun u hu => degIn_le_maxDegVertex G A hne hu)
              _ = A.card * degIn G A v := by simp
          have hsumR : (dirEdgesGraph G A : ℝ) ≤ (A.card : ℝ) * (degIn G A v : ℝ) := by
            rw [← sum_degIn_eq_dirEdges]; exact_mod_cast hsum
          have hd := hden A (le_of_lt hRA)
          have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr (by omega)
          nlinarith
        have hNsub : A.filter (fun u => G.Adj v u) ⊆ A.erase v := by
          intro u hu
          simp only [Finset.mem_filter] at hu
          exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hu.2).symm, hu.1⟩
        have hA'card : A'.card = A.card - 1 - degIn G A v := by
          simp only [A', degIn]
          rw [Finset.card_sdiff_of_subset hNsub, Finset.card_erase_of_mem hvA]
        have hA'le : (A'.card : ℝ) ≤ (1 - α) * (A.card : ℝ) := by
          have hle1 : (A'.card : ℝ) + (degIn G A v : ℝ) ≤ (A.card : ℝ) := by
            have : A'.card + degIn G A v ≤ A.card := by
              have h1 : degIn G A v ≤ A.card - 1 := by
                simpa only [degIn, Finset.card_erase_of_mem hvA] using Finset.card_le_card hNsub
              omega
            exact_mod_cast this
          linarith
        have hk' : (1 - α) ^ k' * (A'.card : ℝ) ≤ (R : ℝ) := by
          have hnn : 0 ≤ (1 - α) ^ k' := pow_nonneg (by linarith) k'
          calc (1 - α) ^ k' * (A'.card : ℝ)
              ≤ (1 - α) ^ k' * ((1 - α) * (A.card : ℝ)) := mul_le_mul_of_nonneg_left hA'le hnn
            _ = (1 - α) ^ k'.succ * (A.card : ℝ) := by rw [pow_succ]; ring
            _ ≤ (R : ℝ) := hk
        have hrec := ih A'.card hlt A' rfl k' hk'
        exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right hrec 1)
      · simp only [v, hv, ↓reduceIte]
        have hlt : (A.erase v).card < n := by
          rw [← hcard]; exact Finset.card_erase_lt_of_mem hvA
        have hkle : (1 - α) ^ k * ((A.erase v).card : ℝ) ≤ (R : ℝ) := by
          have hnn : 0 ≤ (1 - α) ^ k := pow_nonneg (by linarith) k
          have hle : ((A.erase v).card : ℝ) ≤ (A.card : ℝ) := by
            exact_mod_cast Finset.card_le_card (Finset.erase_subset v A)
          exact le_trans (mul_le_mul_of_nonneg_left hle hnn) hk
        exact ih (A.erase v).card hlt (A.erase v) rfl k hkle

private lemma choose_mono_half {R a b : ℕ} (hab : a ≤ b) (hb : 2 * b ≤ R) :
    R.choose a ≤ R.choose b := by
  induction hab with
  | refl => exact le_rfl
  | @step m hm ih =>
    have hstep : R.choose m ≤ R.choose (m + 1) := by
      have hid := Nat.choose_succ_right_eq R m
      have hmul : R.choose m * (m + 1) ≤ R.choose (m + 1) * (m + 1) := by
        rw [hid]; exact Nat.mul_le_mul_left _ (by omega)
      exact Nat.le_of_mul_le_mul_right hmul (by omega)
    exact le_trans (ih (by omega)) hstep

private lemma card_indepSets_le [Fintype V] (G : SimpleGraph V) (R r t : ℕ) (α : ℝ)
    (hV : 0 < Fintype.card V)
    (hα1 : α ≤ 1)
    (hdecay : (1 - α) ^ r * (Fintype.card V : ℝ) ≤ (R : ℝ))
    (hden : ∀ X : Finset V, R ≤ X.card → α * (X.card : ℝ) ^ 2 ≤ (dirEdgesGraph G X : ℝ))
    (htR : 2 * t ≤ R) :
    ((Finset.powersetCard t (Finset.univ : Finset V)).filter
      (fun I => ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v)).card ≤
      (r + 1) * (Fintype.card V) ^ r * R.choose t := by
  let indT := (Finset.powersetCard t (Finset.univ : Finset V)).filter
    (fun I => ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v)
  let pairs := (Finset.range (r + 1)).biUnion (fun j =>
    (Finset.powersetCard j (Finset.univ : Finset V)).biUnion (fun S =>
      (Finset.powersetCard (t - j) (kwContainer G R S Finset.univ)).image (fun T => (S, T))))
  have hinj : Finset.card indT ≤ Finset.card pairs := by
    refine Finset.card_le_card_of_injOn (fun I => (kwFingerprint G R I Finset.univ,
      I \ kwFingerprint G R I Finset.univ)) ?_ ?_
    · intro I hI
      simp only [indT, Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and] at hI
      rcases hI with ⟨hIt, hind⟩
      let S := kwFingerprint G R I Finset.univ
      have hSsub : S ⊆ I := (kwFingerprint_subset G R I Finset.univ).trans Finset.inter_subset_left
      have hSr : S.card ≤ r := by
        have h1 : (1 - α) ^ r * ((Finset.univ : Finset V).card : ℝ) ≤ (R : ℝ) := by simpa using hdecay
        exact kwFingerprint_card_le G R α hα1 hden I Finset.univ r h1
      have hTsub : I \ S ⊆ kwContainer G R S Finset.univ := by
        have h := kw_indep_subset_container G R I hind Finset.univ S (by simp [S])
        simpa using h
      have hTcard : (I \ S).card = t - S.card := by rw [Finset.card_sdiff_of_subset hSsub, hIt]
      simp only [Finset.mem_coe, pairs, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_powersetCard, Finset.mem_image]
      exact ⟨S.card, by omega, S, ⟨Finset.subset_univ S, rfl⟩, I \ S, ⟨hTsub, hTcard⟩, rfl⟩
    · intro I₁ _ I₂ _ hEq
      simp only [Prod.mk.injEq] at hEq
      have hs1 : kwFingerprint G R I₁ Finset.univ ⊆ I₁ :=
        (kwFingerprint_subset G R I₁ Finset.univ).trans Finset.inter_subset_left
      have hs2 : kwFingerprint G R I₂ Finset.univ ⊆ I₂ :=
        (kwFingerprint_subset G R I₂ Finset.univ).trans Finset.inter_subset_left
      calc I₁ = kwFingerprint G R I₁ Finset.univ ∪ (I₁ \ kwFingerprint G R I₁ Finset.univ) :=
            (Finset.union_sdiff_of_subset hs1).symm
        _ = kwFingerprint G R I₂ Finset.univ ∪ (I₂ \ kwFingerprint G R I₂ Finset.univ) := by
            rw [hEq.2, hEq.1]
        _ = I₂ := Finset.union_sdiff_of_subset hs2
  have hpairs_le : pairs.card ≤ (r + 1) * (Fintype.card V) ^ r * R.choose t := by
    calc pairs.card
        ≤ ∑ j ∈ Finset.range (r + 1),
            ((Finset.powersetCard j (Finset.univ : Finset V)).biUnion (fun S =>
              (Finset.powersetCard (t - j) (kwContainer G R S Finset.univ)).image (fun T => (S, T)))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Finset.range (r + 1),
            ∑ S ∈ Finset.powersetCard j (Finset.univ : Finset V),
              ((Finset.powersetCard (t - j) (kwContainer G R S Finset.univ)).image (fun T => (S, T))).card :=
          Finset.sum_le_sum (fun j _ => Finset.card_biUnion_le)
      _ ≤ ∑ j ∈ Finset.range (r + 1),
            ∑ _S ∈ Finset.powersetCard j (Finset.univ : Finset V), R.choose t := by
          refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun S _ => ?_))
          calc ((Finset.powersetCard (t - j) (kwContainer G R S Finset.univ)).image (fun T => (S, T))).card
              ≤ (Finset.powersetCard (t - j) (kwContainer G R S Finset.univ)).card := Finset.card_image_le
            _ = (kwContainer G R S Finset.univ).card.choose (t - j) := Finset.card_powersetCard _ _
            _ ≤ R.choose (t - j) := Nat.choose_le_choose _ (kwContainer_card_le G R S Finset.univ)
            _ ≤ R.choose t := choose_mono_half (Nat.sub_le t j) htR
      _ = ∑ j ∈ Finset.range (r + 1), (Fintype.card V).choose j * R.choose t := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, Finset.card_univ]
      _ ≤ ∑ _j ∈ Finset.range (r + 1), (Fintype.card V) ^ r * R.choose t := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hch : (Fintype.card V).choose j ≤ (Fintype.card V) ^ r :=
            le_trans (nat_choose_le_pow _ j) (Nat.pow_le_pow_right hV hjr)
          exact Nat.mul_le_mul_right _ hch
      _ = (r + 1) * (Fintype.card V) ^ r * R.choose t := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_assoc]
  exact le_trans hinj hpairs_le

end Containers

/- ========================================================================= -/
/- Part 5: Weighted subset sampling & alteration in `G_q*`                   -/
/- ========================================================================= -/

section Sampling

private lemma choose_le_four_div_pow (R t : ℕ) (ht : 1 ≤ t) :
    (R.choose t : ℝ) ≤ (4 * (R : ℝ) / (t : ℝ)) ^ t := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have htfact_pos : (0 : ℝ) < (t.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos t
  have hdesc : (t.factorial : ℝ) * (R.choose t : ℝ) ≤ (R : ℝ) ^ t := by
    have h1 : R.descFactorial t = t.factorial * R.choose t := Nat.descFactorial_eq_factorial_mul_choose R t
    have h2 : R.descFactorial t ≤ R ^ t := Nat.descFactorial_le_pow R t
    exact_mod_cast (h1 ▸ h2 : t.factorial * R.choose t ≤ R ^ t)
  have hexp : (t : ℝ) ^ t / (t.factorial : ℝ) ≤ (Real.exp 1) ^ t := by
    have hsum := Real.sum_le_exp_of_nonneg htpos.le (t + 1)
    have hmem : t ∈ Finset.range (t + 1) := Finset.mem_range.mpr (Nat.lt_succ_self t)
    have hterm := Finset.single_le_sum (f := fun i : ℕ => (t : ℝ) ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) hmem
    have hexpt : Real.exp (t : ℝ) = (Real.exp 1) ^ t := by rw [← Real.exp_nat_mul, mul_one]
    linarith
  have he4 : Real.exp 1 ≤ 4 := le_trans Real.exp_one_lt_d9.le (by norm_num)
  have hstep : (R.choose t : ℝ) ≤ (Real.exp 1 * (R : ℝ) / (t : ℝ)) ^ t := by
    rw [div_pow, mul_pow, le_div_iff₀ (pow_pos htpos t)]
    have h1 : (R.choose t : ℝ) * (t : ℝ) ^ t =
        ((t.factorial : ℝ) * (R.choose t : ℝ)) * ((t : ℝ) ^ t / (t.factorial : ℝ)) := by
      field_simp [htfact_pos.ne']
    rw [h1]
    calc ((t.factorial : ℝ) * (R.choose t : ℝ)) * ((t : ℝ) ^ t / (t.factorial : ℝ))
        ≤ (R : ℝ) ^ t * (Real.exp 1) ^ t := mul_le_mul hdesc hexp (by positivity) (by positivity)
      _ = (Real.exp 1) ^ t * (R : ℝ) ^ t := mul_comm _ _
  refine le_trans hstep (pow_le_pow_left₀ (by positivity) ?_ t)
  gcongr

private lemma sum_bernoulli_weights {α : Type*} (A : Finset α) (p : ℝ) :
    ∑ U ∈ A.powerset, p ^ U.card * (1 - p) ^ (A.card - U.card) = 1 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have hpart : (insert a s).powerset = s.powerset ∪ s.powerset.image (insert a) :=
      Finset.powerset_insert s a
    have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
      rw [Finset.disjoint_left]
      intro U h1 h2
      rcases Finset.mem_image.mp h2 with ⟨V, _, rfl⟩
      exact has (Finset.mem_powerset.mp h1 (Finset.mem_insert_self a V))
    have hinj : Set.InjOn (insert a) (s.powerset : Set (Finset α)) := by
      intro U hU V hV hEq
      have haU : a ∉ U := fun h => has (Finset.mem_powerset.mp hU h)
      have haV : a ∉ V := fun h => has (Finset.mem_powerset.mp hV h)
      have := congrArg (fun W => W.erase a) hEq
      simpa [Finset.erase_insert haU, Finset.erase_insert haV] using this
    rw [hpart, Finset.sum_union hdisj, Finset.sum_image hinj, Finset.card_insert_of_notMem has]
    have hsum1 : ∑ U ∈ s.powerset, p ^ U.card * (1 - p) ^ (s.card + 1 - U.card) =
        (1 - p) * ∑ U ∈ s.powerset, p ^ U.card * (1 - p) ^ (s.card - U.card) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun U hU => ?_)
      have hle : U.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hU)
      rw [show s.card + 1 - U.card = (s.card - U.card) + 1 by omega, pow_succ]; ring
    have hsum2 : ∑ U ∈ s.powerset, p ^ (insert a U).card * (1 - p) ^ (s.card + 1 - (insert a U).card) =
        p * ∑ U ∈ s.powerset, p ^ U.card * (1 - p) ^ (s.card - U.card) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun U hU => ?_)
      have haU : a ∉ U := fun h => has (Finset.mem_powerset.mp hU h)
      rw [Finset.card_insert_of_notMem haU, pow_succ]
      rw [show s.card + 1 - (U.card + 1) = s.card - U.card by omega]; ring
    rw [hsum1, hsum2, ih]; ring

private lemma sum_bernoulli_supset {V : Type*} [Fintype V] (S : Finset V) (p : ℝ) :
    ∑ U ∈ (Finset.univ : Finset (Finset V)).filter (fun U => S ⊆ U),
      p ^ U.card * (1 - p) ^ (Fintype.card V - U.card) = p ^ S.card := by
  let comp := Finset.univ \ S
  have hbij : (Finset.univ : Finset (Finset V)).filter (fun U => S ⊆ U) =
      comp.powerset.image (fun U' => S ∪ U') := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_powerset, comp]
    constructor
    · intro hSU
      refine ⟨U \ S, ?_, Finset.union_sdiff_of_subset hSU⟩
      intro x hx; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢; exact hx.2
    · rintro ⟨U', _, rfl⟩; exact Finset.subset_union_left
  have hinj : Set.InjOn (fun U' => S ∪ U') (comp.powerset : Set (Finset V)) := by
    intro U₁ h₁ U₂ h₂ hEq
    have hd1 : Disjoint S U₁ := Finset.disjoint_left.mpr (fun x hx h1 =>
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp h₁ h1)).2 hx)
    have hd2 : Disjoint S U₂ := Finset.disjoint_left.mpr (fun x hx h2 =>
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp h₂ h2)).2 hx)
    have := congrArg (fun W => W \ S) hEq
    simpa [Finset.union_sdiff_cancel_left hd1, Finset.union_sdiff_cancel_left hd2] using this
  rw [hbij, Finset.sum_image hinj]
  have hcomp_card : comp.card = Fintype.card V - S.card := by
    simp only [comp, Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
  have hterm : ∑ U' ∈ comp.powerset,
      p ^ (S ∪ U').card * (1 - p) ^ (Fintype.card V - (S ∪ U').card) =
      p ^ S.card * ∑ U' ∈ comp.powerset, p ^ U'.card * (1 - p) ^ (comp.card - U'.card) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun U' hU' => ?_)
    have hd : Disjoint S U' := Finset.disjoint_left.mpr (fun x hx h1 =>
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hU' h1)).2 hx)
    rw [Finset.card_union_of_disjoint hd, pow_add, hcomp_card]
    rw [show Fintype.card V - (S.card + U'.card) = Fintype.card V - S.card - U'.card by omega]; ring
  rw [hterm, sum_bernoulli_weights comp p, mul_one]

private lemma exists_k4free_large_graph {q : ℕ} (D : UnitalData q) (hq : 2 ^ 90 ≤ q) :
    let t : ℕ := Nat.ceil ((2 ^ 30 : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ 2)
    ∃ (W : Finset D.W) (G : SimpleGraph W),
      (q : ℝ) ^ 3 * (Real.log (q : ℝ)) ^ 2 / 2 ≤ (W.card : ℝ) ∧
      ¬ (SimpleGraph.completeGraph (Fin 4)).IsContained G ∧
      ¬ (SimpleGraph.completeGraph (Fin t)).IsContained Gᶜ := by
  let := D.instFinU; let := D.instFinW
  intro t
  rcases exists_pseudorandom_col D hq with ⟨col, hcol⟩
  let G0 := bipGraphOf D.inc col
  let n : ℕ := Fintype.card D.W
  let R : ℕ := 2 ^ 24 * q ^ 2
  let r : ℕ := Nat.ceil (512 * (q : ℝ) * Real.log (q : ℝ))
  let α : ℝ := 1 / (128 * (q : ℝ))
  have hq4 : 4 ≤ q := by omega
  have hqR : (2 ^ 90 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hlogq_ge1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
    have : Real.exp 1 ≤ (q : ℝ) := le_trans (le_trans Real.exp_one_lt_d9.le (by norm_num)) hqR
    have := Real.log_le_log (Real.exp_pos 1) this
    rwa [Real.log_exp] at this
  have hcube := log_cube_bound hq
  have ⟨hn_ge8, hn_le⟩ : (8 : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (q : ℝ) ^ 4 := by
    have : n = q ^ 2 * (q ^ 2 - q + 1) := D.cardW
    rw [this]; exact secant_card_bounds hq4
  have hn_ge : (3 / 4 : ℝ) * (q : ℝ) ^ 4 ≤ (n : ℝ) := by
    have hn_eq : n = q ^ 2 * (q ^ 2 - q + 1) := D.cardW
    have hqle : q ≤ q ^ 2 := by nlinarith
    have hcast : (n : ℝ) = (q : ℝ) ^ 2 * ((q : ℝ) ^ 2 - (q : ℝ) + 1) := by
      rw [hn_eq, Nat.cast_mul, Nat.cast_add, Nat.cast_sub hqle]; push_cast; ring
    rw [hcast]; nlinarith [sq_nonneg ((q : ℝ) - 4)]
  have hα1 : α ≤ 1 := by simp only [α]; rw [div_le_one (by positivity)]; linarith
  have hdecay : (1 - α) ^ r * (Fintype.card D.W : ℝ) ≤ (R : ℝ) := by
    have h1 : 1 - α ≤ Real.exp (-α) := by linarith [Real.add_one_le_exp (-α)]
    have hpow : (1 - α) ^ r ≤ Real.exp (-(r : ℝ) * α) := by
      calc (1 - α) ^ r ≤ (Real.exp (-α)) ^ r := pow_le_pow_left₀ (by linarith) h1 r
        _ = Real.exp ((r : ℝ) * (-α)) := (Real.exp_nat_mul (-α) r).symm
        _ = Real.exp (-(r : ℝ) * α) := by ring_nf
    have hr_ge : 512 * (q : ℝ) * Real.log (q : ℝ) ≤ (r : ℝ) := Nat.le_ceil _
    have hralpha : 4 * Real.log (q : ℝ) ≤ (r : ℝ) * α := by
      simp only [α]; rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
    have hexp_le : Real.exp (-(r : ℝ) * α) ≤ ((q : ℝ) ^ 4)⁻¹ := by
      calc Real.exp (-(r : ℝ) * α)
          ≤ Real.exp (-(4 * Real.log (q : ℝ))) := Real.exp_le_exp.mpr (by linarith)
        _ = ((q : ℝ) ^ 4)⁻¹ := by
            rw [Real.exp_neg, show (4 : ℝ) * Real.log (q : ℝ) = ((4 : ℕ) : ℝ) * Real.log (q : ℝ) by norm_num,
              ← Real.log_pow, Real.exp_log (by positivity)]
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
      have : 1 ≤ R := by simp only [R]; nlinarith
      exact_mod_cast this
    calc (1 - α) ^ r * (Fintype.card D.W : ℝ)
        ≤ ((q : ℝ) ^ 4)⁻¹ * (q : ℝ) ^ 4 :=
          mul_le_mul (le_trans hpow hexp_le) hn_le (Nat.cast_nonneg _) (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
      _ ≤ (R : ℝ) := hR1
  have hden : ∀ X : Finset D.W, R ≤ X.card → α * (X.card : ℝ) ^ 2 ≤ (dirEdgesGraph G0 X : ℝ) := by
    intro X hX; simpa only [α, one_div_mul_eq_div, G0] using hcol X hX
  have ht_ge : (2 ^ 30 : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤ (t : ℝ) := Nat.le_ceil _
  have ht_le : (t : ℝ) ≤ (2 ^ 30 : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hr_le : (r : ℝ) ≤ 512 * (q : ℝ) * Real.log (q : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have htR : 2 * t ≤ R := by
    have hlog2 : (Real.log (q : ℝ)) ^ 2 ≤ (Real.log (q : ℝ)) ^ 3 := by
      nlinarith [sq_nonneg (Real.log (q : ℝ))]
    have hRR : (R : ℝ) = (2 ^ 24 : ℝ) * (q : ℝ) ^ 2 := by simp only [R]; push_cast; ring
    have : (2 * t : ℝ) ≤ (R : ℝ) := by rw [hRR]; nlinarith
    exact_mod_cast this
  let indT := (Finset.powersetCard t (Finset.univ : Finset D.W)).filter
    (fun I => ∀ u ∈ I, ∀ v ∈ I, ¬ G0.Adj u v)
  have hW_pos : 0 < Fintype.card D.W := by
    have : (0 : ℝ) < (Fintype.card D.W : ℝ) := by linarith
    exact_mod_cast this
  have hind_card : indT.card ≤ (r + 1) * n ^ r * R.choose t := by
    let linOrd : LinearOrder D.W :=
      LinearOrder.lift' (Fintype.equivFin D.W) (Fintype.equivFin D.W).injective
    have h := @card_indepSets_le D.W linOrd _ G0 R r t α hW_pos hα1 hdecay hden htR
    have heq : indT = @Finset.filter (Finset D.W) (fun I => ∀ u ∈ I, ∀ v ∈ I, ¬ G0.Adj u v)
        _ (Finset.powersetCard t (Finset.univ : Finset D.W)) := by
      ext I; simp only [indT, Finset.mem_filter]
    rw [heq]; exact h
  have ht1 : 1 ≤ t := by
    have : (1 : ℝ) ≤ (t : ℝ) := by nlinarith
    exact_mod_cast this
  have hind_bound : (indT.card : ℝ) ≤ ((q : ℝ) / (Real.log (q : ℝ)) ^ 2) ^ t := by
    have hcast : (indT.card : ℝ) ≤ ((r : ℝ) + 1) * (n : ℝ) ^ r * (R.choose t : ℝ) := by
      exact_mod_cast hind_card
    have hpow1 : ((r : ℝ) + 1) * (n : ℝ) ^ r ≤ (2 : ℝ) ^ t := by
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have h1 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
          have hsq : Real.exp 1 ≤ 4 := le_trans Real.exp_one_lt_d9.le (by norm_num)
          have h2 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
          nlinarith [Real.exp_pos (1 / 2 : ℝ)]
        have := Real.log_le_log (Real.exp_pos _) h1
        rwa [Real.log_exp] at this
      have hnr : (n : ℝ) ^ r ≤ (q : ℝ) ^ (4 * r) := by
        calc (n : ℝ) ^ r ≤ ((q : ℝ) ^ 4) ^ r := pow_le_pow_left₀ (Nat.cast_nonneg _) hn_le r
          _ = (q : ℝ) ^ (4 * r) := (pow_mul _ _ _).symm
      have hr1_le : (r : ℝ) + 1 ≤ Real.exp ((r : ℝ) + 1) := by linarith [Real.add_one_le_exp ((r : ℝ) + 1)]
      have hq4r : (q : ℝ) ^ (4 * r) = Real.exp ((4 * (r : ℝ)) * Real.log (q : ℝ)) := by
        rw [show (4 * (r : ℝ)) * Real.log (q : ℝ) = ((4 * r : ℕ) : ℝ) * Real.log (q : ℝ) by push_cast; ring,
          ← Real.log_pow, Real.exp_log (by positivity)]
      have hexp_sum : ((r : ℝ) + 1) * (q : ℝ) ^ (4 * r) ≤
          Real.exp (((r : ℝ) + 1) + 4 * (r : ℝ) * Real.log (q : ℝ)) := by
        rw [Real.exp_add, ← hq4r]
        exact mul_le_mul_of_nonneg_right hr1_le (by positivity)
      have hexp_le : ((r : ℝ) + 1) + 4 * (r : ℝ) * Real.log (q : ℝ) ≤ (t : ℝ) * Real.log 2 := by
        nlinarith [sq_nonneg (Real.log (q : ℝ))]
      have h2t : Real.exp ((t : ℝ) * Real.log 2) = (2 : ℝ) ^ t := by
        rw [← Real.log_pow, Real.exp_log (by positivity)]
      calc ((r : ℝ) + 1) * (n : ℝ) ^ r
          ≤ ((r : ℝ) + 1) * (q : ℝ) ^ (4 * r) := by gcongr
        _ ≤ Real.exp (((r : ℝ) + 1) + 4 * (r : ℝ) * Real.log (q : ℝ)) := hexp_sum
        _ ≤ Real.exp ((t : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hexp_le
        _ = (2 : ℝ) ^ t := h2t
    have hch : (R.choose t : ℝ) ≤ (4 * (R : ℝ) / (t : ℝ)) ^ t := choose_le_four_div_pow R t ht1
    have hratio : 2 * (4 * (R : ℝ) / (t : ℝ)) ≤ (q : ℝ) / (Real.log (q : ℝ)) ^ 2 := by
      have hRR : (R : ℝ) = (2 ^ 24 : ℝ) * (q : ℝ) ^ 2 := by simp only [R]; push_cast; ring
      have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
      rw [hRR, mul_div_assoc', div_le_div_iff₀ htpos (by positivity)]
      nlinarith
    calc (indT.card : ℝ)
        ≤ ((r : ℝ) + 1) * (n : ℝ) ^ r * (R.choose t : ℝ) := hcast
      _ ≤ (2 : ℝ) ^ t * (4 * (R : ℝ) / (t : ℝ)) ^ t :=
          mul_le_mul hpow1 hch (Nat.cast_nonneg _) (by positivity)
      _ = (2 * (4 * (R : ℝ) / (t : ℝ))) ^ t := (mul_pow _ _ _).symm
      _ ≤ ((q : ℝ) / (Real.log (q : ℝ)) ^ 2) ^ t := pow_le_pow_left₀ (by positivity) hratio t
  let p : ℝ := (Real.log (q : ℝ)) ^ 2 / (q : ℝ)
  have hp_pos : 0 < p := by positivity
  have hp_lt1 : p < 1 := by
    simp only [p]; rw [div_lt_one hqpos]
    have : (Real.log (q : ℝ)) ^ 2 ≤ (Real.log (q : ℝ)) ^ 3 := by nlinarith
    linarith
  let w : Finset D.W → ℝ := fun U => p ^ U.card * (1 - p) ^ (n - U.card)
  have hw_nonneg : ∀ U : Finset D.W, 0 ≤ w U := fun U => by
    simp only [w]; exact mul_nonneg (pow_nonneg hp_pos.le _) (pow_nonneg (by linarith) _)
  have hsum_w : ∑ U : Finset D.W, w U = 1 := by
    have h := sum_bernoulli_weights (Finset.univ : Finset D.W) p
    simpa only [Finset.powerset_univ, Finset.card_univ, w, n] using h
  have hE_card : ∑ U : Finset D.W, w U * (U.card : ℝ) = (n : ℝ) * p := by
    have h1 : ∀ U : Finset D.W, (U.card : ℝ) = ∑ v : D.W, if v ∈ U then (1 : ℝ) else 0 := by
      intro U; simp
    simp_rw [h1, Finset.mul_sum]; rw [Finset.sum_comm]
    have hv : ∀ v : D.W, (∑ U : Finset D.W, w U * (if v ∈ U then (1 : ℝ) else 0)) = p := by
      intro v
      have hite : ∀ U : Finset D.W,
          w U * (if v ∈ U then (1 : ℝ) else 0) = if ({v} : Finset D.W) ⊆ U then w U else 0 := by
        intro U; simp only [Finset.singleton_subset_iff]; split_ifs <;> ring
      simp_rw [hite, ← Finset.sum_filter]
      have hsup := sum_bernoulli_supset ({v} : Finset D.W) p
      simpa only [Finset.card_singleton, pow_one, w, n] using hsup
    rw [Finset.sum_congr rfl (fun v _ => hv v), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hE_ind : ∑ U : Finset D.W, w U * ((indT.filter (fun I => I ⊆ U)).card : ℝ) =
      (indT.card : ℝ) * p ^ t := by
    have h1 : ∀ U : Finset D.W,
        ((indT.filter (fun I => I ⊆ U)).card : ℝ) = ∑ I ∈ indT, if I ⊆ U then (1 : ℝ) else 0 := by
      intro U; simp [Finset.sum_boole]
    simp_rw [h1, Finset.mul_sum]; rw [Finset.sum_comm]
    have hI : ∀ I ∈ indT, (∑ U : Finset D.W, w U * (if I ⊆ U then (1 : ℝ) else 0)) = p ^ t := by
      intro I hImem
      have hIt : I.card = t := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hImem).1).2
      have hite : ∀ U : Finset D.W,
          w U * (if I ⊆ U then (1 : ℝ) else 0) = if I ⊆ U then w U else 0 := by
        intro U; split_ifs <;> ring
      simp_rw [hite, ← Finset.sum_filter]
      have hsup := sum_bernoulli_supset I p
      simpa only [hIt, w, n] using hsup
    rw [Finset.sum_congr rfl hI, Finset.sum_const, nsmul_eq_mul]
  have hE_ind_le1 : (indT.card : ℝ) * p ^ t ≤ 1 := by
    have hpinv : ((q : ℝ) / (Real.log (q : ℝ)) ^ 2) * p = 1 := by
      simp only [p]; field_simp [hqpos.ne', (show Real.log (q : ℝ) ≠ 0 by linarith)]
    calc (indT.card : ℝ) * p ^ t
        ≤ ((q : ℝ) / (Real.log (q : ℝ)) ^ 2) ^ t * p ^ t := by gcongr
      _ = (((q : ℝ) / (Real.log (q : ℝ)) ^ 2) * p) ^ t := (mul_pow _ _ _).symm
      _ = 1 := by rw [hpinv, one_pow]
  have hE_diff : (q : ℝ) ^ 3 * (Real.log (q : ℝ)) ^ 2 / 2 ≤
      ∑ U : Finset D.W, w U * ((U.card : ℝ) - ((indT.filter (fun I => I ⊆ U)).card : ℝ)) := by
    have hsub : ∑ U : Finset D.W, w U * ((U.card : ℝ) - ((indT.filter (fun I => I ⊆ U)).card : ℝ)) =
        (n : ℝ) * p - (indT.card : ℝ) * p ^ t := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, hE_card, hE_ind]
    rw [hsub]
    have hnp : (3 / 4 : ℝ) * (q : ℝ) ^ 3 * (Real.log (q : ℝ)) ^ 2 ≤ (n : ℝ) * p := by
      have : (3 / 4 : ℝ) * (q : ℝ) ^ 4 * p = (3 / 4 : ℝ) * (q : ℝ) ^ 3 * (Real.log (q : ℝ)) ^ 2 := by
        simp only [p]; field_simp [hqpos.ne']
      linarith [mul_le_mul_of_nonneg_right hn_ge hp_pos.le]
    have h1le : (1 : ℝ) ≤ (1 / 4 : ℝ) * (q : ℝ) ^ 3 * (Real.log (q : ℝ)) ^ 2 := by
      have hlog2 : (1 : ℝ) ≤ (Real.log (q : ℝ)) ^ 2 := by nlinarith only [hlogq_ge1]
      have hq3 : (4 : ℝ) ≤ (q : ℝ) ^ 3 := by
        have hq4R : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq4
        calc (4 : ℝ) ≤ (q : ℝ) := hq4R
          _ ≤ (q : ℝ) ^ 3 := le_self_pow₀ (by linarith only [hq4R]) (by omega)
      nlinarith only [hlog2, hq3]
    linarith only [hnp, hE_ind_le1, h1le]
  have hex_U : ∃ U : Finset D.W,
      (q : ℝ) ^ 3 * (Real.log (q : ℝ)) ^ 2 / 2 ≤
        (U.card : ℝ) - ((indT.filter (fun I => I ⊆ U)).card : ℝ) := by
    by_contra hnone; push Not at hnone
    have hlt : ∑ U : Finset D.W, w U * ((U.card : ℝ) - ((indT.filter (fun I => I ⊆ U)).card : ℝ)) <
        ∑ U : Finset D.W, w U * ((q : ℝ) ^ 3 * (Real.log (q : ℝ)) ^ 2 / 2) := by
      refine Finset.sum_lt_sum (fun U _ => mul_le_mul_of_nonneg_left (hnone U).le (hw_nonneg U)) ?_
      refine ⟨∅, Finset.mem_univ _, ?_⟩
      have hw0 : 0 < w ∅ := by simp only [w, Finset.card_empty, pow_zero, one_mul, Nat.sub_zero]; positivity
      exact mul_lt_mul_of_pos_left (hnone ∅) hw0
    rw [← Finset.sum_mul, hsum_w, one_mul] at hlt; linarith only [hlt, hE_diff]
  rcases hex_U with ⟨U, hU⟩
  let badI := indT.filter (fun I => I ⊆ U)
  have hU' : (q : ℝ) ^ 3 * (Real.log (q : ℝ)) ^ 2 / 2 ≤ (U.card : ℝ) - (badI.card : ℝ) := hU
  have hpick_ex : ∀ I ∈ badI, ∃ x : D.W, x ∈ I := by
    intro I hI
    have hIt : I.card = t := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).1).2
    exact Finset.card_pos.mp (by omega)
  let del : Finset D.W := badI.attach.image (fun I => (hpick_ex I.1 I.2).choose)
  let W : Finset D.W := U \ del
  have hW_card : (q : ℝ) ^ 3 * (Real.log (q : ℝ)) ^ 2 / 2 ≤ (W.card : ℝ) := by
    have hdel_le : del.card ≤ badI.card :=
      le_trans Finset.card_image_le (le_of_eq (Finset.card_attach))
    have hsub : U.card - badI.card ≤ W.card := by
      have hsub_u : U ⊆ W ∪ del := fun x hx => by
        by_cases hd : x ∈ del
        · exact Finset.mem_union_right _ hd
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hd⟩)
      have h1 : U.card ≤ W.card + del.card :=
        le_trans (Finset.card_le_card hsub_u) (Finset.card_union_le _ _)
      omega
    by_cases hUle : badI.card ≤ U.card
    · have hcast : ((U.card - badI.card : ℕ) : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hsub
      rw [Nat.cast_sub hUle] at hcast; linarith only [hU', hcast]
    · have hltU : (U.card : ℝ) < (badI.card : ℝ) := by exact_mod_cast (show U.card < badI.card by omega)
      have hpos : (0 : ℝ) < (q : ℝ) ^ 3 * (Real.log (q : ℝ)) ^ 2 / 2 := by positivity
      linarith only [hU', hltU, hpos]
  let GW : SimpleGraph W := G0.induce (W : Set D.W)
  refine ⟨W, GW, hW_card, ?_, ?_⟩
  · rintro ⟨f⟩
    exact D.noK4 col ⟨mkCopy (fun i => (f i).1)
      (fun i j h => f.injective (Subtype.ext h)) (fun hij => f.toHom.map_rel hij)⟩
  · rintro ⟨f⟩
    let I : Finset D.W := Finset.univ.image (fun i : Fin t => (f i).1)
    have hI_sub_W : I ⊆ W := by
      intro x hx; rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩; exact (f i).2
    have hI_card : I.card = t := by
      have hinj : Function.Injective (fun i : Fin t => (f i).1) :=
        fun i j h => f.injective (Subtype.ext h)
      simpa only [I, Finset.card_univ, Fintype.card_fin] using
        Finset.card_image_of_injective (Finset.univ : Finset (Fin t)) hinj
    have hI_ind : ∀ u ∈ I, ∀ v ∈ I, ¬ G0.Adj u v := by
      intro u hu v hv
      rcases Finset.mem_image.mp hu with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp hv with ⟨j, _, rfl⟩
      by_cases hij : i = j
      · subst hij; exact G0.loopless.irrefl _
      · exact (f.toHom.map_rel hij).2
    have hI_bad : I ∈ badI := by
      simp only [badI, indT, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact ⟨⟨hI_card, hI_ind⟩, hI_sub_W.trans Finset.sdiff_subset⟩
    let x := (hpick_ex I hI_bad).choose
    have hxI : x ∈ I := (hpick_ex I hI_bad).choose_spec
    have hxW : x ∈ W := hI_sub_W hxI
    have hxdel : x ∈ del := Finset.mem_image.mpr ⟨⟨I, hI_bad⟩, Finset.mem_attach _ _, rfl⟩
    exact (Finset.mem_sdiff.mp hxW).2 hxdel

end Sampling

/- ========================================================================= -/
/- Part 6: Ramsey bridge, Bertrand's postulate, and final asymptotics        -/
/- ========================================================================= -/

section RamseyBridge

private lemma exists_ramsey_nat :
    ∀ n : ℕ, ∀ s t : ℕ, s + t = n →
      ∃ N : ℕ, ∀ C : SimpleGraph (Fin N),
        (SimpleGraph.completeGraph (Fin s)).IsContained C ∨
        (SimpleGraph.completeGraph (Fin t)).IsContained Cᶜ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s t hst
    cases s with
    | zero =>
      exact ⟨0, fun C => Or.inl ⟨mkCopy Fin.elim0 (fun i => i.elim0) (fun {i} => i.elim0)⟩⟩
    | succ s' =>
      cases t with
      | zero =>
        exact ⟨0, fun C => Or.inr ⟨mkCopy Fin.elim0 (fun i => i.elim0) (fun {i} => i.elim0)⟩⟩
      | succ t' =>
        rcases ih (s' + (t' + 1)) (by omega) s' (t' + 1) rfl with ⟨N₁, hN₁⟩
        rcases ih ((s' + 1) + t') (by omega) (s' + 1) t' rfl with ⟨N₂, hN₂⟩
        refine ⟨N₁ + N₂ + 1, fun C => ?_⟩
        let v0 : Fin (N₁ + N₂ + 1) := ⟨0, by omega⟩
        let rest := (Finset.univ : Finset (Fin (N₁ + N₂ + 1))).erase v0
        let A := rest.filter (fun u => C.Adj v0 u)
        let B := rest.filter (fun u => ¬ C.Adj v0 u)
        have hAB : A.card + B.card = N₁ + N₂ := by
          have hAB_eq : A.card + B.card = rest.card := by
            rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1))]
            congr 1; ext u; simp only [Finset.mem_union, Finset.mem_filter]; tauto
          rw [hAB_eq, Finset.card_erase_of_mem (Finset.mem_univ v0), Finset.card_univ, Fintype.card_fin]
          omega
        by_cases hA : N₁ ≤ A.card
        · let eA : Fin A.card ≃ A := (Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm
          let emb : Fin N₁ ↪ Fin (N₁ + N₂ + 1) :=
            ⟨fun i => (eA (Fin.castLE hA i)).1,
             fun i j h => Fin.castLE_injective hA (eA.injective (Subtype.ext h))⟩
          rcases hN₁ (C.comap emb) with h1 | h2
          · obtain ⟨f⟩ : Nonempty _ := h1
            left
            refine ⟨mkCopy (fun i => Fin.cases v0 (fun j => emb (f j)) i) ?_ ?_⟩
            · intro i j
              refine Fin.cases ?_ (fun i' => ?_) i
              · refine Fin.cases (fun _ => rfl) (fun j' hEq => ?_) j
                simp only [Fin.cases_zero, Fin.cases_succ] at hEq
                have hmem : emb (f j') ∈ rest := (Finset.mem_filter.mp (eA _).2).1
                exact absurd hEq.symm (Finset.mem_erase.mp hmem).1
              · refine Fin.cases (fun hEq => ?_) (fun j' hEq => ?_) j
                · simp only [Fin.cases_zero, Fin.cases_succ] at hEq
                  have hmem : emb (f i') ∈ rest := (Finset.mem_filter.mp (eA _).2).1
                  exact absurd hEq (Finset.mem_erase.mp hmem).1
                · simp only [Fin.cases_succ] at hEq
                  exact congrArg Fin.succ (f.injective (emb.injective hEq))
            · intro i j
              refine Fin.cases ?_ (fun i' => ?_) i
              · refine Fin.cases (fun hij => absurd rfl hij) (fun j' _ => ?_) j
                simp only [Fin.cases_zero, Fin.cases_succ]
                exact (Finset.mem_filter.mp (eA _).2).2
              · refine Fin.cases (fun _ => ?_) (fun j' hij => ?_) j
                · simp only [Fin.cases_zero, Fin.cases_succ]
                  exact C.symm.1 _ _ (Finset.mem_filter.mp (eA _).2).2
                · simp only [Fin.cases_succ]
                  exact f.toHom.map_rel (fun h => hij (congrArg Fin.succ h))
          · obtain ⟨f⟩ : Nonempty _ := h2
            right
            refine ⟨mkCopy (fun i => emb (f i)) (fun i j h => f.injective (emb.injective h)) ?_⟩
            intro i j hij
            have hadj : (C.comap emb)ᶜ.Adj (f i) (f j) := f.toHom.map_rel hij
            exact ⟨fun h => hadj.1 (emb.injective h), hadj.2⟩
        · have hB : N₂ ≤ B.card := by omega
          let eB : Fin B.card ≃ B := (Fintype.equivFinOfCardEq (Fintype.card_coe B)).symm
          let emb : Fin N₂ ↪ Fin (N₁ + N₂ + 1) :=
            ⟨fun i => (eB (Fin.castLE hB i)).1,
             fun i j h => Fin.castLE_injective hB (eB.injective (Subtype.ext h))⟩
          rcases hN₂ (C.comap emb) with h1 | h2
          · obtain ⟨f⟩ : Nonempty _ := h1
            left
            exact ⟨mkCopy (fun i => emb (f i)) (fun i j h => f.injective (emb.injective h))
              (fun hij => f.toHom.map_rel hij)⟩
          · obtain ⟨f⟩ : Nonempty _ := h2
            right
            refine ⟨mkCopy (fun i => Fin.cases v0 (fun j => emb (f j)) i) ?_ ?_⟩
            · intro i j
              refine Fin.cases ?_ (fun i' => ?_) i
              · refine Fin.cases (fun _ => rfl) (fun j' hEq => ?_) j
                simp only [Fin.cases_zero, Fin.cases_succ] at hEq
                have hmem : emb (f j') ∈ rest := (Finset.mem_filter.mp (eB _).2).1
                exact absurd hEq.symm (Finset.mem_erase.mp hmem).1
              · refine Fin.cases (fun hEq => ?_) (fun j' hEq => ?_) j
                · simp only [Fin.cases_zero, Fin.cases_succ] at hEq
                  have hmem : emb (f i') ∈ rest := (Finset.mem_filter.mp (eB _).2).1
                  exact absurd hEq (Finset.mem_erase.mp hmem).1
                · simp only [Fin.cases_succ] at hEq
                  exact congrArg Fin.succ (f.injective (emb.injective hEq))
            · intro i j
              refine Fin.cases ?_ (fun i' => ?_) i
              · refine Fin.cases (fun hij => absurd rfl hij) (fun j' _ => ?_) j
                simp only [Fin.cases_zero, Fin.cases_succ]
                have hm := Finset.mem_filter.mp (eB (Fin.castLE hB (f j'))).2
                exact ⟨(Finset.mem_erase.mp hm.1).1.symm, hm.2⟩
              · refine Fin.cases (fun _ => ?_) (fun j' hij => ?_) j
                · simp only [Fin.cases_zero, Fin.cases_succ]
                  have hm := Finset.mem_filter.mp (eB (Fin.castLE hB (f i'))).2
                  exact ⟨(Finset.mem_erase.mp hm.1).1, fun h => hm.2 (C.symm.1 _ _ h)⟩
                · simp only [Fin.cases_succ]
                  have hadj : (C.comap emb)ᶜ.Adj (f i') (f j') :=
                    f.toHom.map_rel (fun h => hij (congrArg Fin.succ h))
                  exact ⟨fun h => hadj.1 (emb.injective h), hadj.2⟩

private lemma classicalRamsey_gt_of_graph {V : Type*} [Fintype V] {s t : ℕ}
    (G : SimpleGraph V)
    (hs : ¬ (SimpleGraph.completeGraph (Fin s)).IsContained G)
    (ht : ¬ (SimpleGraph.completeGraph (Fin t)).IsContained Gᶜ) :
    Fintype.card V < SimpleGraph.classicalRamsey s t := by
  have hne : {n : ℕ | ∀ C : SimpleGraph (Fin n),
      (SimpleGraph.completeGraph (Fin s)).IsContained C ∨
      (SimpleGraph.completeGraph (Fin t)).IsContained Cᶜ}.Nonempty :=
    exists_ramsey_nat (s + t) s t rfl
  have hmem := Nat.sInf_mem hne
  change ∀ C : SimpleGraph (Fin (SimpleGraph.classicalRamsey s t)),
      (SimpleGraph.completeGraph (Fin s)).IsContained C ∨
      (SimpleGraph.completeGraph (Fin t)).IsContained Cᶜ at hmem
  by_contra hle; push Not at hle
  let eV : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let emb : Fin (SimpleGraph.classicalRamsey s t) ↪ V :=
    ⟨fun i => eV (Fin.castLE hle i), fun i j h => Fin.castLE_injective hle (eV.injective h)⟩
  rcases hmem (G.comap emb) with h1 | h2
  · obtain ⟨f⟩ : Nonempty _ := h1
    exact hs ⟨mkCopy (fun i => emb (f i)) (fun i j h => f.injective (emb.injective h))
      (fun hij => f.toHom.map_rel hij)⟩
  · obtain ⟨f⟩ : Nonempty _ := h2
    apply ht
    refine ⟨mkCopy (fun i => emb (f i)) (fun i j h => f.injective (emb.injective h)) ?_⟩
    intro i j hij
    have hadj : (G.comap emb)ᶜ.Adj (f i) (f j) := f.toHom.map_rel hij
    exact ⟨fun h => hadj.1 (emb.injective h), hadj.2⟩

private lemma not_isContained_mono {V : Type*} {G : SimpleGraph V} {t k : ℕ} (htk : t ≤ k)
    (ht : ¬ (SimpleGraph.completeGraph (Fin t)).IsContained G) :
    ¬ (SimpleGraph.completeGraph (Fin k)).IsContained G := by
  rintro ⟨f⟩
  exact ht ⟨mkCopy (fun i => f (Fin.castLE htk i))
    (fun i j h => Fin.castLE_injective htk (f.injective h))
    (fun hij => f.toHom.map_rel (fun h => hij (Fin.castLE_injective htk h)))⟩

private lemma log_sq_le_sqrt_div {k : ℕ} (hk : 2 ^ 190 ≤ k) :
    (2 ^ 33 : ℝ) * (Real.log (k : ℝ)) ^ 2 < Real.sqrt (k : ℝ) := by
  have hkR : (2 ^ 190 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  let z : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (k : ℝ)))
  have hzpos : 0 < z := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hkpos))
  have hz4 : z ^ 4 = Real.sqrt (k : ℝ) := by
    have h1 : z ^ 2 = Real.sqrt (Real.sqrt (k : ℝ)) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc z ^ 4 = (z ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (Real.sqrt (k : ℝ))) ^ 2 := by rw [h1]
      _ = Real.sqrt (k : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hz8 : z ^ 8 = (k : ℝ) := by
    calc z ^ 8 = (z ^ 4) ^ 2 := by ring
      _ = (Real.sqrt (k : ℝ)) ^ 2 := by rw [hz4]
      _ = (k : ℝ) := Real.sq_sqrt hkpos.le
  have hlogz : Real.log (k : ℝ) ≤ 8 * z := by
    have h0 : Real.log (k : ℝ) = Real.log (z ^ 8) := by rw [hz8]
    rw [h0, Real.log_pow]; push_cast
    have h1 := Real.log_le_sub_one_of_pos hzpos; linarith
  have hzgt : (2 ^ 20 : ℝ) < z := by
    by_contra hle; push Not at hle
    have h8 : z ^ 8 ≤ (2 ^ 20 : ℝ) ^ 8 := pow_le_pow_left₀ hzpos.le hle 8
    have : (2 ^ 20 : ℝ) ^ 8 < (2 ^ 190 : ℝ) := by norm_num
    linarith
  have hlognn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have hsq : (Real.log (k : ℝ)) ^ 2 ≤ 64 * z ^ 2 := by
    have := pow_le_pow_left₀ hlognn hlogz 2
    linarith [show (8 * z) ^ 2 = 64 * z ^ 2 by ring]
  have hz2pos : 0 < z ^ 2 := pow_pos hzpos 2
  have hz2gt : (2 ^ 39 : ℝ) < z ^ 2 := by
    have : (2 ^ 20 : ℝ) ^ 2 < z ^ 2 := by nlinarith
    linarith [show (2 ^ 39 : ℝ) < (2 ^ 20 : ℝ) ^ 2 by norm_num]
  calc (2 ^ 33 : ℝ) * (Real.log (k : ℝ)) ^ 2
      ≤ (2 ^ 33 : ℝ) * (64 * z ^ 2) := by gcongr
    _ = (2 ^ 39 : ℝ) * z ^ 2 := by ring
    _ < z ^ 2 * z ^ 2 := by gcongr
    _ = z ^ 4 := by ring
    _ = Real.sqrt (k : ℝ) := hz4

private theorem mattheus_verstraete_main :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ (k : ℕ) in atTop,
      (SimpleGraph.classicalRamsey 4 k : ℝ) ≥ C * (k : ℝ) ^ 3 / (Real.log k) ^ 4 := by
  refine ⟨1 / (2 ^ 102 : ℝ), by positivity, Filter.eventually_atTop.mpr ⟨2 ^ 190, fun k hk => ?_⟩⟩
  have hkR : (2 ^ 190 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hlogk_ge1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by
    have : Real.exp 1 ≤ (k : ℝ) := le_trans (le_trans Real.exp_one_lt_d9.le (by norm_num)) hkR
    have := Real.log_le_log (Real.exp_pos 1) this
    rwa [Real.log_exp] at this
  have hlogk_pos : 0 < Real.log (k : ℝ) := by linarith
  have hls := log_sq_le_sqrt_div hk
  let x : ℝ := (k : ℝ) / ((2 ^ 32 : ℝ) * (Real.log (k : ℝ)) ^ 2)
  have hx_ge_2sqrt : 2 * Real.sqrt (k : ℝ) ≤ x := by
    simp only [x]; rw [le_div_iff₀ (by positivity)]
    have hsq : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) := Real.mul_self_sqrt hkpos.le
    nlinarith [Real.sqrt_pos.mpr hkpos]
  have hsqrtk_ge : (2 ^ 95 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hkpos.le]
    linarith [show (2 ^ 95 : ℝ) ^ 2 = (2 ^ 190 : ℝ) by norm_num]
  let M : ℕ := Nat.floor x
  have hM_ge_sqrt : Real.sqrt (k : ℝ) ≤ (M : ℝ) := by
    have hfl : x - 1 < (M : ℝ) := Nat.sub_one_lt_floor x; linarith
  have hM_ge_90 : 2 ^ 90 ≤ M := by
    have : (2 ^ 90 : ℝ) ≤ (M : ℝ) := by linarith [show (2 ^ 90 : ℝ) ≤ (2 ^ 95 : ℝ) by norm_num]
    exact_mod_cast this
  have hM_ne0 : M ≠ 0 := by omega
  rcases Nat.exists_prime_lt_and_le_two_mul M hM_ne0 with ⟨q, hq_prime, hMq, hq2M⟩
  have : Fact q.Prime := ⟨hq_prime⟩
  have hq90 : 2 ^ 90 ≤ q := by omega
  have hq_gt_M : (M : ℝ) < (q : ℝ) := by exact_mod_cast hMq
  have hq_le_2x : (q : ℝ) ≤ 2 * x := by
    have h1 : (q : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hq2M
    have h2 : (M : ℝ) ≤ x := Nat.floor_le (by positivity)
    linarith
  have hq_le_k : (q : ℝ) ≤ (k : ℝ) := by
    have h1 : 2 * x ≤ (k : ℝ) := by
      simp only [x]
      have : (2 : ℝ) ≤ (2 ^ 32 : ℝ) * (Real.log (k : ℝ)) ^ 2 := by nlinarith
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hlogq_le : Real.log (q : ℝ) ≤ Real.log (k : ℝ) := Real.log_le_log (by positivity) hq_le_k
  have hlogq_ge : Real.log (k : ℝ) / 2 ≤ Real.log (q : ℝ) := by
    have h1 : Real.log (Real.sqrt (k : ℝ)) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (Real.sqrt_pos.mpr hkpos) (le_trans hM_ge_sqrt hq_gt_M.le)
    rwa [Real.log_sqrt hkpos.le] at h1
  let t : ℕ := Nat.ceil ((2 ^ 30 : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ 2)
  have htk : t ≤ k := by
    have ht_le : (t : ℝ) ≤ (2 ^ 30 : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hlogq_sq : (Real.log (q : ℝ)) ^ 2 ≤ (Real.log (k : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hlogq_le 2
    have h1 : (2 ^ 30 : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤ (k : ℝ) / 2 := by
      have hq2x : (q : ℝ) * ((2 ^ 31 : ℝ) * (Real.log (k : ℝ)) ^ 2) ≤ (k : ℝ) := by
        have hx2 : 2 * x = (k : ℝ) / ((2 ^ 31 : ℝ) * (Real.log (k : ℝ)) ^ 2) := by simp only [x]; ring
        rw [hx2, le_div_iff₀ (by positivity)] at hq_le_2x; exact hq_le_2x
      have h2 : (2 ^ 30 : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤
          (2 ^ 30 : ℝ) * (q : ℝ) * (Real.log (k : ℝ)) ^ 2 := by gcongr
      linarith
    have : (t : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  rcases exists_k4free_large_graph (hermitianUnital q) hq90 with ⟨W, GW, hW_card, hno4, hnot⟩
  have hnok : ¬ (SimpleGraph.completeGraph (Fin k)).IsContained GWᶜ := not_isContained_mono htk hnot
  have hram : W.card < SimpleGraph.classicalRamsey 4 k := by
    have := classicalRamsey_gt_of_graph GW hno4 hnok
    simpa using this
  have hramR : (q : ℝ) ^ 3 * (Real.log (q : ℝ)) ^ 2 / 2 ≤ (SimpleGraph.classicalRamsey 4 k : ℝ) := by
    have : (W.card : ℝ) < (SimpleGraph.classicalRamsey 4 k : ℝ) := by exact_mod_cast hram
    linarith
  have hq_ge : (k : ℝ) / ((2 ^ 33 : ℝ) * (Real.log (k : ℝ)) ^ 2) ≤ (q : ℝ) := by
    have hfl : x - 1 < (M : ℝ) := Nat.sub_one_lt_floor x
    have hx_half : x / 2 ≤ x - 1 := by linarith
    have hx2 : x / 2 = (k : ℝ) / ((2 ^ 33 : ℝ) * (Real.log (k : ℝ)) ^ 2) := by simp only [x]; ring
    linarith
  have hq3 : ((k : ℝ) / ((2 ^ 33 : ℝ) * (Real.log (k : ℝ)) ^ 2)) ^ 3 ≤ (q : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hq_ge 3
  have hlog2 : (Real.log (k : ℝ) / 2) ^ 2 ≤ (Real.log (q : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlogq_ge 2
  have hprod : ((k : ℝ) / ((2 ^ 33 : ℝ) * (Real.log (k : ℝ)) ^ 2)) ^ 3 *
      (Real.log (k : ℝ) / 2) ^ 2 / 2 ≤ (q : ℝ) ^ 3 * (Real.log (q : ℝ)) ^ 2 / 2 := by
    have := mul_le_mul hq3 hlog2 (by positivity) (by positivity); linarith
  have hsimp : ((k : ℝ) / ((2 ^ 33 : ℝ) * (Real.log (k : ℝ)) ^ 2)) ^ 3 *
      (Real.log (k : ℝ) / 2) ^ 2 / 2 =
      1 / (2 ^ 102 : ℝ) * (k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ 4 := by
    field_simp [hlogk_pos.ne']
  rw [ge_iff_le]; linarith

end RamseyBridge

end Erdos166MV

theorem OMA.solution : type_of% @Erdos166.erdos_166.variants.mattheus_verstraete :=
  Erdos166MV.mattheus_verstraete_main
