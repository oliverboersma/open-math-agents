import OMAReductions.R_Constant14_c14_ge_4_R1
import Mathlib.Tactic

/-!
# Proof of `Constant14.c14_ge_4.R1.H3`

We prove semantic faithfulness of `Constant14.halts M` in the standard model `ZFSet.{0}`:
for any truth valuation `tr` satisfying Tarski's clauses on `ZFSet.{0}` and any non-halting
two-symbol Turing machine `M`, `¬ tr Fin.elim0 (Constant14.halts M)`.

The proof proceeds in four stages:
1. Structural induction on closed formulas (`Semisentence ℒₛₑₜ m`) shows that any `tr` obeying the
   nine Tarski clauses agrees with the canonical valuation `exEv.choose` from the `R1` reduction.
2. A lightweight `EvalTermAt` combinator layer evaluates formula-as-function (`nestFormulae` and
   `nestFormulaeFunc`) expressions directly to Lean operations on `ZFSet.{0}`.
3. We evaluate all set-theoretic encodings in `Constant14` (von Neumann numerals, `ω`, Kuratowski
   pairs and projections, set functions and application, encoded integers, transition tables,
   configurations, `nextConfig`, `nextStep`, `orbit`, and `halts`).
4. Instantiating `orbit` at the `ZFSet.range` of the encoded Lean simulation trajectory `extStep M`
   shows that if `Constant14.halts M` held in `ZFSet.{0}`, some step `k` would reach state code `n`
   (`none`), contradicting `¬ M.IsHalting` via `Machine.exists_of_not_haltsAfter`.
-/

namespace C14H3Proof

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver
open OMA.R_Constant14_c14_ge_4_R1
open scoped Classical

/- ## Section 1: Uniqueness of Tarski Truth Valuations on Closed Set-Theory Formulas -/

private noncomputable def stdTv {m : ℕ} (e : Fin m → ZFSet.{0})
    (t : Semiterm ℒₛₑₜ Empty m) : ZFSet.{0} :=
  exTv.choose e (Empty.elim : Empty → ZFSet.{0}) t

private def stdEv {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : Semisentence ℒₛₑₜ m) : Prop :=
  exEv.choose e (Empty.elim : Empty → ZFSet.{0}) φ

private lemma stdEv_and {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m) :
    stdEv e (φ ⋏ ψ) ↔ stdEv e φ ∧ stdEv e ψ :=
  ev_and' e Empty.elim φ ψ

private lemma stdEv_or {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m) :
    stdEv e (φ ⋎ ψ) ↔ stdEv e φ ∨ stdEv e ψ :=
  ev_or' e Empty.elim φ ψ

private lemma stdEv_imp {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m) :
    stdEv e (φ 🡒 ψ) ↔ (stdEv e φ → stdEv e ψ) :=
  ev_imp' e Empty.elim φ ψ

private lemma stdEv_iff {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m) :
    stdEv e (φ 🡘 ψ) ↔ (stdEv e φ ↔ stdEv e ψ) :=
  ev_iff' e Empty.elim φ ψ

private lemma stdEv_all {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : Semisentence ℒₛₑₜ (m + 1)) :
    stdEv e (∀¹ φ) ↔ ∀ d : ZFSet.{0}, stdEv (d :> e) φ :=
  ev_all' e Empty.elim φ

private lemma stdEv_exs {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : Semisentence ℒₛₑₜ (m + 1)) :
    stdEv e (∃¹ φ) ↔ ∃ d : ZFSet.{0}, stdEv (d :> e) φ :=
  ev_exs' e Empty.elim φ

private lemma stdEv_eq {m : ℕ} (e : Fin m → ZFSet.{0}) (t₁ t₂ : Semiterm ℒₛₑₜ Empty m) :
    stdEv e (op(=).operator ![t₁, t₂]) ↔ stdTv e t₁ = stdTv e t₂ :=
  ev_eq' e Empty.elim t₁ t₂

private lemma stdEv_mem {m : ℕ} (e : Fin m → ZFSet.{0}) (t₁ t₂ : Semiterm ℒₛₑₜ Empty m) :
    stdEv e (Semiformula.Operator.Mem.mem.operator ![t₁, t₂]) ↔ stdTv e t₁ ∈ stdTv e t₂ :=
  ev_mem' e Empty.elim t₁ t₂

private lemma stdEv_ballMem {m : ℕ} (e : Fin m → ZFSet.{0}) (t : Semiterm ℒₛₑₜ Empty m)
    (φ : Semisentence ℒₛₑₜ (m + 1)) :
    stdEv e (Semiformula.ballMem t φ) ↔ ∀ d ∈ stdTv e t, stdEv (d :> e) φ :=
  ev_ballMem e Empty.elim t φ

private lemma stdEv_bexsMem {m : ℕ} (e : Fin m → ZFSet.{0}) (t : Semiterm ℒₛₑₜ Empty m)
    (φ : Semisentence ℒₛₑₜ (m + 1)) :
    stdEv e (Semiformula.bexsMem t φ) ↔ ∃ d ∈ stdTv e t, stdEv (d :> e) φ :=
  ev_bexsMem e Empty.elim t φ

private lemma stdTv_bvar {m : ℕ} (e : Fin m → ZFSet.{0}) (i : Fin m) :
    stdTv e (#i) = e i :=
  tval_bvar e Empty.elim i

private lemma stdEv_subst1 {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : SetTheorySemisentence 1)
    (i₀ : Fin m) :
    stdEv e (φ ⇜ ![#i₀]) ↔ stdEv ![e i₀] φ := by
  unfold stdEv
  rw [ev_subst']
  refine ev_congr φ ?_ rfl
  funext k; fin_cases k; simp

private lemma stdEv_subst2 {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : SetTheorySemisentence 2)
    (i₀ i₁ : Fin m) :
    stdEv e (φ ⇜ ![#i₀, #i₁]) ↔ stdEv ![e i₀, e i₁] φ := by
  unfold stdEv
  rw [ev_subst']
  refine ev_congr φ ?_ rfl
  funext k; fin_cases k <;> simp

private lemma stdEv_subst3 {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : SetTheorySemisentence 3)
    (i₀ i₁ i₂ : Fin m) :
    stdEv e (φ ⇜ ![#i₀, #i₁, #i₂]) ↔ stdEv ![e i₀, e i₁, e i₂] φ := by
  unfold stdEv
  rw [ev_subst']
  refine ev_congr φ ?_ rfl
  funext k; fin_cases k <;> simp

private lemma closed_term_eq_bvar {m : ℕ} (t : Semiterm ℒₛₑₜ Empty m) :
    ∃ i : Fin m, t = Semiterm.bvar i := by
  cases t with
  | bvar i => exact ⟨i, rfl⟩
  | fvar x => exact x.elim
  | func f _ => exact (f : Empty).elim

private lemma closed_vec2_eq_bvars {m : ℕ} (v : Fin 2 → Semiterm ℒₛₑₜ Empty m) :
    ∃ i j : Fin m, v = ![Semiterm.bvar i, Semiterm.bvar j] := by
  obtain ⟨i, hi⟩ := closed_term_eq_bvar (v 0)
  obtain ⟨j, hj⟩ := closed_term_eq_bvar (v 1)
  refine ⟨i, j, ?_⟩
  funext k
  fin_cases k
  · exact hi
  · exact hj

private lemma tr_rel_iff_stdEv
    (tr : ∀ {m : ℕ}, (Fin m → ZFSet.{0}) → Semisentence ℒₛₑₜ m → Prop)
    (heq : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (i j : Fin m),
      tr e (Semiformula.rel Language.Set.Rel.eq ![Semiterm.bvar i, Semiterm.bvar j]) ↔ e i = e j)
    (hmem : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (i j : Fin m),
      tr e (Semiformula.rel Language.Set.Rel.mem ![Semiterm.bvar i, Semiterm.bvar j]) ↔ e i ∈ e j)
    {m k : ℕ} (e : Fin m → ZFSet.{0}) (r : Language.Set.Rel k)
    (v : Fin k → Semiterm ℒₛₑₜ Empty m) :
    tr e (Semiformula.rel r v) ↔ stdEv e (Semiformula.rel r v) := by
  cases r with
  | eq =>
    obtain ⟨i, j, rfl⟩ := closed_vec2_eq_bvars v
    unfold stdEv
    rw [heq e i j, ev_rel_eq_c]
    simp
  | mem =>
    obtain ⟨i, j, rfl⟩ := closed_vec2_eq_bvars v
    unfold stdEv
    rw [hmem e i j, ev_rel_mem_c]
    simp

private lemma tr_iff_stdEv
    (tr : ∀ {m : ℕ}, (Fin m → ZFSet.{0}) → Semisentence ℒₛₑₜ m → Prop)
    (hverum : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}), tr e Semiformula.verum)
    (hfalsum : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}), ¬ tr e Semiformula.falsum)
    (heq : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (i j : Fin m),
      tr e (Semiformula.rel Language.Set.Rel.eq ![Semiterm.bvar i, Semiterm.bvar j]) ↔ e i = e j)
    (hmem : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (i j : Fin m),
      tr e (Semiformula.rel Language.Set.Rel.mem ![Semiterm.bvar i, Semiterm.bvar j]) ↔ e i ∈ e j)
    (hnrel : ∀ {m k : ℕ} (e : Fin m → ZFSet.{0}) (r : Language.Set.Rel k)
      (v : Fin k → Semiterm ℒₛₑₜ Empty m),
      tr e (Semiformula.nrel r v) ↔ ¬ tr e (Semiformula.rel r v))
    (hand : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m),
      tr e (Semiformula.and φ ψ) ↔ tr e φ ∧ tr e ψ)
    (hor : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m),
      tr e (Semiformula.or φ ψ) ↔ tr e φ ∨ tr e ψ)
    (hall : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : Semisentence ℒₛₑₜ (m + 1)),
      tr e (Semiformula.all φ) ↔ ∀ d, tr (Matrix.vecCons d e) φ)
    (hexs : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : Semisentence ℒₛₑₜ (m + 1)),
      tr e (Semiformula.exs φ) ↔ ∃ d, tr (Matrix.vecCons d e) φ) :
    ∀ {m : ℕ} (φ : Semisentence ℒₛₑₜ m) (e : Fin m → ZFSet.{0}),
      tr e φ ↔ stdEv e φ := by
  intro m φ
  induction φ with
  | verum =>
    intro e
    unfold stdEv
    rw [ev_verum_c]
    exact ⟨fun _ => trivial, fun _ => hverum e⟩
  | falsum =>
    intro e
    unfold stdEv
    rw [ev_falsum_c]
    exact ⟨fun h => hfalsum e h, False.elim⟩
  | rel r v =>
    intro e
    exact tr_rel_iff_stdEv tr heq hmem e r v
  | nrel r v =>
    intro e
    unfold stdEv
    rw [hnrel e r v, ev_nrel_c]
    exact not_congr (tr_rel_iff_stdEv tr heq hmem e r v)
  | and φ ψ ih1 ih2 =>
    intro e
    unfold stdEv at *
    rw [hand e φ ψ, ev_and_c]
    exact and_congr (ih1 e) (ih2 e)
  | or φ ψ ih1 ih2 =>
    intro e
    unfold stdEv at *
    rw [hor e φ ψ, ev_or_c]
    exact or_congr (ih1 e) (ih2 e)
  | all φ ih =>
    intro e
    unfold stdEv at *
    rw [hall e φ, ev_all_c]
    exact forall_congr' fun d => ih (Matrix.vecCons d e)
  | exs φ ih =>
    intro e
    unfold stdEv at *
    rw [hexs e φ, ev_exs_c]
    exact exists_congr fun d => ih (Matrix.vecCons d e)

/- ## Section 2: `EvalTermAt` Combinators for Formula-as-Function Expressions -/

private def EvalTermAt {m : ℕ} (e : Fin m → ZFSet.{0}) (Ψ : SetTheorySemisentence (m + 1))
    (val : ZFSet.{0}) : Prop :=
  ∀ y : ZFSet.{0}, stdEv (y :> e) Ψ ↔ y = val

private def DefinesConst (Ψ : SetTheorySemisentence 1) (c : ZFSet.{0}) : Prop :=
  ∀ y : ZFSet.{0}, stdEv ![y] Ψ ↔ y = c

private lemma stdEv_e0 (e1 e2 : Fin 0 → ZFSet.{0}) (φ : SetTheorySemisentence 0) :
    stdEv e1 φ ↔ stdEv e2 φ := by
  rw [Subsingleton.elim e1 e2]

private lemma stdEv_e1 (y : ZFSet.{0}) (e : Fin 0 → ZFSet.{0}) (φ : SetTheorySemisentence 1) :
    stdEv (y :> e) φ ↔ stdEv ![y] φ := by
  rw [Subsingleton.elim e ![]]

private lemma et_bvar_succ {m : ℕ} (e : Fin m → ZFSet.{0}) (i : Fin m) :
    EvalTermAt e (op(=).operator (#0 :> #(i.succ) :> ![])) (e i) := by
  intro y
  unfold stdEv
  rw [ev_eq']
  simp [tval_bvar]

private lemma et_bvar1 {m : ℕ} (a : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    EvalTermAt (a :> e) (op(=).operator (#0 :> #1 :> ![])) a :=
  et_bvar_succ (a :> e) 0

private lemma et_bvar2 {m : ℕ} (a b : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    EvalTermAt (a :> b :> e) (op(=).operator (#0 :> #2 :> ![])) b :=
  et_bvar_succ (a :> b :> e) 1

private lemma et_bvar3 {m : ℕ} (a b c : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    EvalTermAt (a :> b :> c :> e) (op(=).operator (#0 :> #3 :> ![])) c :=
  et_bvar_succ (a :> b :> c :> e) 2

private lemma et_bvar4 {m : ℕ} (a b c d : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    EvalTermAt (a :> b :> c :> d :> e) (op(=).operator (#0 :> #4 :> ![])) d :=
  et_bvar_succ (a :> b :> c :> d :> e) 3

private lemma et_bvar5 {m : ℕ} (a b c d f : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    EvalTermAt (a :> b :> c :> d :> f :> e) (op(=).operator (#0 :> #5 :> ![])) f :=
  et_bvar_succ (a :> b :> c :> d :> f :> e) 4

private lemma et_bvar6 {m : ℕ} (a b c d f g : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    EvalTermAt (a :> b :> c :> d :> f :> g :> e) (op(=).operator (#0 :> #6 :> ![])) g :=
  et_bvar_succ (a :> b :> c :> d :> f :> g :> e) 5

private lemma ev_nestFunc0_raw {m : ℕ} (φ : SetTheorySemisentence 1) (y : ZFSet.{0})
    (e : Fin m → ZFSet.{0}) :
    stdEv (y :> e) (Semiformula.nestFormulaeFunc φ ![]) ↔ stdEv ![y] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj, stdEv]
  rw [ev_imp', ev_top', ev_subst']
  simp only [true_imp_iff]
  refine ev_congr φ ?_ rfl
  funext i
  fin_cases i
  simp [Fin.addNat, tval_bvar]

private lemma et_const0 {m : ℕ} {Ψ : SetTheorySemisentence 1} {c : ZFSet.{0}}
    (hΨ : DefinesConst Ψ c) (e : Fin m → ZFSet.{0}) :
    EvalTermAt e (Semiformula.nestFormulaeFunc Ψ ![]) c := by
  intro y
  rw [ev_nestFunc0_raw]
  exact hΨ y

private lemma ev_nestFunc1_raw {m : ℕ} (φ : SetTheorySemisentence 2)
    {e : Fin m → ZFSet.{0}} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : ZFSet.{0}}
    (h₀ : EvalTermAt e Ψ₀ v₀) (y : ZFSet.{0}) :
    stdEv (y :> e) (Semiformula.nestFormulaeFunc φ ![Ψ₀]) ↔ stdEv ![y, v₀] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj, stdEv]
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d₀ : ZFSet.{0}, d₀ = v₀ → stdEv ![y, d₀] φ).trans
    ⟨fun h => h v₀ rfl, fun h d₀ hd => hd ▸ h⟩
  refine forall_congr' fun d₀ => ?_
  rw [ev_imp', ev_and', ev_top', and_true, ev_subst', ev_subst']
  have he0 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> y :> e) Empty.elim
        ((#((0 : Fin 1).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 1)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast, tval_bvar]
    · simp [Fin.addNat, tval_bvar]
  have he1 : (fun k : Fin 2 =>
      exTv.choose (d₀ :> y :> e) Empty.elim
        ((#((0 : Fin (m + 1)).addNat 1) :> fun i : Fin 1 => #(i.addCast m.succ)) k)) =
      ![y, d₀] := by
    funext k
    fin_cases k <;> simp [Fin.addNat, Fin.addCast, tval_bvar]
  rw [he0, he1]
  exact imp_congr (h₀ d₀) Iff.rfl

private lemma et_comp1 {m : ℕ} {φ : SetTheorySemisentence 2} {G : ZFSet.{0} → ZFSet.{0}}
    (hφ : ∀ y x₀, stdEv ![y, x₀] φ ↔ y = G x₀)
    {e : Fin m → ZFSet.{0}} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : ZFSet.{0}}
    (h₀ : EvalTermAt e Ψ₀ v₀) :
    EvalTermAt e (Semiformula.nestFormulaeFunc φ ![Ψ₀]) (G v₀) := by
  intro y
  rw [ev_nestFunc1_raw φ h₀ y, hφ y v₀]

private lemma ev_nestFunc2_raw {m : ℕ} (φ : SetTheorySemisentence 3)
    {e : Fin m → ZFSet.{0}}
    {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : ZFSet.{0}}
    (h₀ : EvalTermAt e Ψ₀ v₀) (h₁ : EvalTermAt e Ψ₁ v₁) (y : ZFSet.{0}) :
    stdEv (y :> e) (Semiformula.nestFormulaeFunc φ ![Ψ₀, Ψ₁]) ↔ stdEv ![y, v₀, v₁] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj, stdEv]
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d₁ d₀ : ZFSet.{0}, (d₀ = v₀ ∧ d₁ = v₁) → stdEv ![y, d₀, d₁] φ).trans
    ⟨fun h => h v₁ v₀ ⟨rfl, rfl⟩, fun h d₁ d₀ ⟨hd0, hd1⟩ => by subst hd0 hd1; exact h⟩
  refine forall_congr' fun d₁ => ?_
  rw [ev_all']
  refine forall_congr' fun d₀ => ?_
  dsimp only [Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [ev_imp', ev_and', ev_and', ev_top', and_true, ev_subst', ev_subst', ev_subst']
  have he_psi0 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((0 : Fin 2).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 2)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast, tval_bvar]
    · simp [Fin.addNat, tval_bvar]
  have he_psi1 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((1 : Fin 2).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 2)) k)) =
      (d₁ :> e) := by
    have h1 : ((1 : Fin 2).addCast m.succ) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [h1, tval_bvar]
    · simp [Fin.addNat, tval_bvar]
  have he_phi : (fun k : Fin 3 =>
      exTv.choose (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((0 : Fin (m + 1)).addNat 2) :> fun i : Fin 2 => #(i.addCast m.succ)) k)) =
      ![y, d₀, d₁] := by
    have h1 : ((1 : Fin 2).addCast m.succ) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    fin_cases k
    · simp [Fin.addNat, tval_bvar]
    · simp [Fin.addCast, tval_bvar]
    · change exTv.choose (d₀ :> d₁ :> y :> e) Empty.elim (#((1 : Fin 2).addCast m.succ)) = d₁
      simp [h1, tval_bvar]
  rw [he_psi0, he_psi1, he_phi]
  exact imp_congr (and_congr (h₀ d₀) (h₁ d₁)) Iff.rfl

private lemma et_comp2 {m : ℕ} {φ : SetTheorySemisentence 3}
    {G : ZFSet.{0} → ZFSet.{0} → ZFSet.{0}}
    (hφ : ∀ y x₀ x₁, stdEv ![y, x₀, x₁] φ ↔ y = G x₀ x₁)
    {e : Fin m → ZFSet.{0}} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : ZFSet.{0}}
    (h₀ : EvalTermAt e Ψ₀ v₀) (h₁ : EvalTermAt e Ψ₁ v₁) :
    EvalTermAt e (Semiformula.nestFormulaeFunc φ ![Ψ₀, Ψ₁]) (G v₀ v₁) := by
  intro y
  rw [ev_nestFunc2_raw φ h₀ h₁ y, hφ y v₀ v₁]

private lemma ev_nest1 {m : ℕ} (φ : SetTheorySemisentence 1)
    {e : Fin m → ZFSet.{0}} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : ZFSet.{0}}
    (h₀ : EvalTermAt e Ψ₀ v₀) :
    stdEv e (Semiformula.nestFormulae φ ![Ψ₀]) ↔ stdEv ![v₀] φ := by
  dsimp only [Semiformula.nestFormulae, FFL.FirstOrder.allItr, Matrix.conj, stdEv]
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d₀ : ZFSet.{0}, d₀ = v₀ → stdEv ![d₀] φ).trans
    ⟨fun h => h v₀ rfl, fun h d₀ hd => hd ▸ h⟩
  refine forall_congr' fun d₀ => ?_
  rw [ev_imp', ev_and', ev_top', and_true, ev_subst', ev_subst']
  have he0 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> e) Empty.elim
        ((#((0 : Fin 1).addCast m) :> fun j : Fin m => #(j.addNat 1)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast, tval_bvar]
    · simp [Fin.addNat, tval_bvar]
  have he1 : (fun k : Fin 1 =>
      exTv.choose (d₀ :> e) Empty.elim (#(k.addCast m))) = ![d₀] := by
    funext k
    fin_cases k
    simp [Fin.addCast, tval_bvar]
  rw [he0, he1]
  exact imp_congr (h₀ d₀) Iff.rfl

private lemma ev_nest2 {m : ℕ} (φ : SetTheorySemisentence 2)
    {e : Fin m → ZFSet.{0}} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : ZFSet.{0}}
    (h₀ : EvalTermAt e Ψ₀ v₀) (h₁ : EvalTermAt e Ψ₁ v₁) :
    stdEv e (Semiformula.nestFormulae φ ![Ψ₀, Ψ₁]) ↔ stdEv ![v₀, v₁] φ := by
  dsimp only [Semiformula.nestFormulae, FFL.FirstOrder.allItr, Matrix.conj, stdEv]
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d₁ d₀ : ZFSet.{0}, (d₀ = v₀ ∧ d₁ = v₁) → stdEv ![d₀, d₁] φ).trans
    ⟨fun h => h v₁ v₀ ⟨rfl, rfl⟩, fun h d₁ d₀ ⟨hd0, hd1⟩ => by subst hd0 hd1; exact h⟩
  refine forall_congr' fun d₁ => ?_
  rw [ev_all']
  refine forall_congr' fun d₀ => ?_
  dsimp only [Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [ev_imp', ev_and', ev_and', ev_top', and_true, ev_subst', ev_subst', ev_subst']
  have he0 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> d₁ :> e) Empty.elim
        ((#((0 : Fin 2).addCast m) :> fun j : Fin m => #(j.addNat 2)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast, tval_bvar]
    · simp [Fin.addNat, tval_bvar]
  have he1 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> d₁ :> e) Empty.elim
        ((#((1 : Fin 2).addCast m) :> fun j : Fin m => #(j.addNat 2)) k)) =
      (d₁ :> e) := by
    have h1 : ((1 : Fin 2).addCast m) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [h1, tval_bvar]
    · simp [Fin.addNat, tval_bvar]
  have he_phi : (fun k : Fin 2 =>
      exTv.choose (d₀ :> d₁ :> e) Empty.elim (#(k.addCast m))) = ![d₀, d₁] := by
    have h1 : ((1 : Fin 2).addCast m) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    fin_cases k
    · simp [Fin.addCast, tval_bvar]
    · change exTv.choose (d₀ :> d₁ :> e) Empty.elim (#((1 : Fin 2).addCast m)) = d₁
      simp [h1, tval_bvar]
  rw [he0, he1, he_phi]
  exact imp_congr (and_congr (h₀ d₀) (h₁ d₁)) Iff.rfl

private lemma ev_faf_eq {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ZFSet.{0}} (h₁ : EvalTermAt e T₁ v₁) (h₂ : EvalTermAt (v₁ :> e) T₂ v₂) :
    stdEv e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 op(=).operator (#1 :> #0 :> ![])))) ↔ v₁ = v₂ := by
  unfold stdEv
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_all'] at hv1
    have hv2 := (ev_imp' _ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [ev_eq'] at hv2
    simpa [tval_bvar] using hv2
  · intro heq d₁
    rw [ev_imp']
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [ev_all']
    intro d₂
    rw [ev_imp']
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [ev_eq']
    simpa [tval_bvar] using heq

private lemma ev_faf_ne {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ZFSet.{0}} (h₁ : EvalTermAt e T₁ v₁) (h₂ : EvalTermAt (v₁ :> e) T₂ v₂) :
    stdEv e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 ∼op(=).operator (#1 :> #0 :> ![])))) ↔ v₁ ≠ v₂ := by
  unfold stdEv
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_all'] at hv1
    have hv2 := (ev_imp' _ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [ev_not', ev_eq'] at hv2
    simpa [tval_bvar] using hv2
  · intro hne d₁
    rw [ev_imp']
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [ev_all']
    intro d₂
    rw [ev_imp']
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [ev_not', ev_eq']
    simpa [tval_bvar] using hne

private lemma ev_faf_mem {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ZFSet.{0}} (h₁ : EvalTermAt e T₁ v₁) (h₂ : EvalTermAt (v₁ :> e) T₂ v₂) :
    stdEv e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) ↔
      v₁ ∈ v₂ := by
  unfold stdEv
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_all'] at hv1
    have hv2 := (ev_imp' _ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [ev_mem'] at hv2
    simpa [tval_bvar] using hv2
  · intro hmem d₁
    rw [ev_imp']
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [ev_all']
    intro d₂
    rw [ev_imp']
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [ev_mem']
    simpa [tval_bvar] using hmem

private lemma ev_faf_notMem {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ZFSet.{0}} (h₁ : EvalTermAt e T₁ v₁) (h₂ : EvalTermAt (v₁ :> e) T₂ v₂) :
    stdEv e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 ∼Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) ↔
      v₁ ∉ v₂ := by
  unfold stdEv
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_all'] at hv1
    have hv2 := (ev_imp' _ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [ev_not', ev_mem'] at hv2
    simpa [tval_bvar] using hv2
  · intro hnm d₁
    rw [ev_imp']
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [ev_all']
    intro d₂
    rw [ev_imp']
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [ev_not', ev_mem']
    simpa [tval_bvar] using hnm

private lemma ev_faf_ball {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {v₁ : ZFSet.{0}}
    (h₁ : EvalTermAt e T₁ v₁) (φ : SetTheorySemisentence (m + 2)) :
    stdEv e (∀¹ (T₁ 🡒 Semiformula.ballMem (#0) φ)) ↔
      ∀ x ∈ v₁, stdEv (x :> v₁ :> e) φ := by
  unfold stdEv
  rw [ev_all']
  constructor
  · intro h x hx
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_ballMem, tval_bvar] at hv1
    exact hv1 x hx
  · intro h d₁
    rw [ev_imp']
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [ev_ballMem, tval_bvar]
    exact h

private lemma ev_faf_bexs {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {v₁ : ZFSet.{0}}
    (h₁ : EvalTermAt e T₁ v₁) (φ : SetTheorySemisentence (m + 2)) :
    stdEv e (∀¹ (T₁ 🡒 Semiformula.bexsMem (#0) φ)) ↔
      ∃ x ∈ v₁, stdEv (x :> v₁ :> e) φ := by
  unfold stdEv
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_bexsMem, tval_bvar] at hv1
    exact hv1
  · intro h d₁
    rw [ev_imp']
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [ev_bexsMem, tval_bvar]
    exact h

private lemma ev_existsUnique {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : SetTheorySemisentence (m + 1)) :
    stdEv e (∃¹! φ) ↔ ∃! y, stdEv (y :> e) φ := by
  unfold Semiformula.existsUnique stdEv ExistsUnique
  rw [ev_exs']
  refine exists_congr fun y => ?_
  rw [ev_and', ev_subst', ev_all']
  have he1 : (fun k : Fin (m + 1) =>
      exTv.choose (y :> e) Empty.elim
        ((#0 :> fun x : Fin m => #(BinderNotation.finSuccItr x 1)) k)) = (y :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [tval_bvar]
    · simp [BinderNotation.finSuccItr, tval_bvar]
  rw [he1]
  refine and_congr Iff.rfl (forall_congr' fun z => ?_)
  rw [ev_imp', ev_subst', ev_eq']
  have he2 : (fun k : Fin (m + 1) =>
      exTv.choose (z :> y :> e) Empty.elim
        ((#0 :> fun x : Fin m => #(BinderNotation.finSuccItr x 2)) k)) = (z :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [tval_bvar]
    · simp [BinderNotation.finSuccItr, tval_bvar]
  rw [he2]
  simp [tval_bvar]

/- ## Section 3: Von Neumann Ordinals, Pairs, Projections, Functions, and Encoded Integers -/

private def vnNat : ℕ → ZFSet.{0}
  | 0 => ∅
  | k + 1 => insert (vnNat k) (vnNat k)

private noncomputable def vnOmega : ZFSet.{0} := ZFSet.range vnNat

private lemma mem_vnNat_iff {x : ZFSet.{0}} {m : ℕ} :
    x ∈ vnNat m ↔ ∃ k < m, x = vnNat k := by
  induction m with
  | zero =>
    simp [vnNat]
  | succ m ih =>
    simp only [vnNat, ZFSet.mem_insert_iff, ih]
    constructor
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hlt, rfl⟩

private lemma vnNat_lt_mem {a b : ℕ} (h : a < b) : vnNat a ∈ vnNat b :=
  mem_vnNat_iff.mpr ⟨a, h, rfl⟩

private lemma vnNat_injective : Function.Injective vnNat := by
  intro a b hab
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have hm : vnNat a ∈ vnNat b := vnNat_lt_mem hlt
    rw [← hab] at hm
    exact False.elim (ZFSet.mem_irrefl _ hm)
  · rfl
  · have hm : vnNat b ∈ vnNat a := vnNat_lt_mem hgt
    rw [hab] at hm
    exact False.elim (ZFSet.mem_irrefl _ hm)

private lemma mem_vnOmega_iff_inductive (x : ZFSet.{0}) :
    x ∈ vnOmega ↔ ∀ I : ZFSet.{0}, (∅ ∈ I ∧ ∀ y ∈ I, insert y y ∈ I) → x ∈ I := by
  unfold vnOmega
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨k, rfl⟩ I ⟨h0, hsucc⟩
    induction k with
    | zero => exact h0
    | succ k ih => exact hsucc (vnNat k) ih
  · intro h
    apply ZFSet.mem_range.mp
    refine h (ZFSet.range vnNat) ⟨⟨0, rfl⟩ |> ZFSet.mem_range.mpr, ?_⟩
    intro y hy
    obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hy
    exact ZFSet.mem_range.mpr ⟨k + 1, rfl⟩

/- Basic `SetTheory` definitions -/

private lemma ev_isEmpty (x : ZFSet.{0}) : stdEv ![x] SetTheory.isEmpty ↔ x = ∅ := by
  unfold SetTheory.isEmpty stdEv
  simp [ZFSet.eq_empty]

private lemma ev_isNonempty (x : ZFSet.{0}) : stdEv ![x] SetTheory.isNonempty ↔ x.Nonempty := by
  unfold SetTheory.isNonempty stdEv
  rw [ev_exs']
  refine exists_congr fun y => ?_
  rw [ev_mem']
  simp

private lemma ev_isSubsetOf (x y : ZFSet.{0}) : stdEv ![x, y] SetTheory.isSubsetOf ↔ x ⊆ y := by
  unfold SetTheory.isSubsetOf stdEv
  simp [ZFSet.subset_def]

private lemma ev_doubleton (p x y : ZFSet.{0}) :
    stdEv ![p, x, y] SetTheory.doubleton.dfn ↔ p = ({x, y} : ZFSet.{0}) := by
  unfold SetTheory.doubleton.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ p ↔ z = x ∨ z = y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [stdEv_iff, stdEv_mem, stdEv_or, stdEv_eq, stdEv_eq]
    simp only [stdTv_bvar]
    rfl
  · constructor
    · intro h
      ext z
      rw [h z, ZFSet.mem_insert_iff, ZFSet.mem_singleton]
    · rintro rfl z
      rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton]

private lemma ev_singleton (p x : ZFSet.{0}) :
    stdEv ![p, x] SetTheory.singleton.dfn ↔ p = ({x} : ZFSet.{0}) := by
  unfold SetTheory.singleton.dfn
  exact (stdEv_subst3 _ _ _ _ _).trans
    ((ev_doubleton p x x).trans (by rw [ZFSet.pair_eq_singleton]))

private lemma ev_sUnion (u x : ZFSet.{0}) :
    stdEv ![u, x] SetTheory.sUnion.dfn ↔ u = ZFSet.sUnion x := by
  unfold SetTheory.sUnion.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ u ↔ ∃ y ∈ x, z ∈ y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [stdEv_iff, stdEv_mem, stdEv_bexsMem]
    simp only [stdTv_bvar]
    exact iff_congr Iff.rfl (exists_congr fun y => and_congr_right fun _ => by
      rw [stdEv_mem]; simp only [stdTv_bvar]; rfl)
  · constructor
    · intro h
      ext z
      rw [h z, ZFSet.mem_sUnion]
    · rintro rfl z
      rw [ZFSet.mem_sUnion]

private lemma ev_union (u x y : ZFSet.{0}) :
    stdEv ![u, x, y] SetTheory.union.dfn ↔ u = x ∪ y := by
  unfold SetTheory.union.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ d : ZFSet.{0}, d = ({x, y} : ZFSet.{0}) → u = ZFSet.sUnion d).trans ?_
  · refine forall_congr' fun d => ?_
    rw [stdEv_imp]
    exact imp_congr
      ((stdEv_subst3 _ _ _ _ _).trans (ev_doubleton d x y))
      ((stdEv_subst2 _ _ _ _).trans (ev_sUnion u d))
  · rw [← ZFSet.sUnion_pair]
    exact ⟨fun h => h ({x, y} : ZFSet.{0}) rfl, fun h d hd => hd ▸ h⟩

private lemma ev_insert (u x y : ZFSet.{0}) :
    stdEv ![u, x, y] SetTheory.insert.dfn ↔ u = insert x y := by
  unfold SetTheory.insert.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ s : ZFSet.{0}, s = ({x} : ZFSet.{0}) → u = s ∪ y).trans ?_
  · refine forall_congr' fun s => ?_
    rw [stdEv_imp]
    exact imp_congr
      ((stdEv_subst2 _ _ _ _).trans (ev_singleton s x))
      ((stdEv_subst3 _ _ _ _ _).trans (ev_union u s y))
  · rw [ZFSet.insert_eq]
    exact ⟨fun h => h ({x} : ZFSet.{0}) rfl, fun h s hs => hs ▸ h⟩

private lemma ev_sInter (u x : ZFSet.{0}) :
    stdEv ![u, x] SetTheory.sInter.dfn ↔ u = ZFSet.sInter x := by
  unfold SetTheory.sInter.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ u ↔ x.Nonempty ∧ ∀ y ∈ x, z ∈ y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [stdEv_iff, stdEv_mem, stdEv_and, stdEv_ballMem]
    simp only [stdTv_bvar]
    refine iff_congr Iff.rfl (and_congr ((stdEv_subst1 _ _ _).trans (ev_isNonempty x)) ?_)
    exact forall₂_congr fun y _ => by rw [stdEv_mem]; simp only [stdTv_bvar]; rfl
  · rcases ZFSet.eq_empty_or_nonempty x with rfl | hne
    · simp only [ZFSet.not_nonempty_empty, false_and, iff_false, ZFSet.sInter_empty, ZFSet.eq_empty]
    · constructor
      · intro h
        ext z
        rw [h z, ZFSet.mem_sInter hne]
        exact ⟨And.right, fun hall => ⟨hne, hall⟩⟩
      · rintro rfl z
        rw [ZFSet.mem_sInter hne]
        exact ⟨fun hall => ⟨hne, hall⟩, And.right⟩

private lemma ev_kpair (k x y : ZFSet.{0}) :
    stdEv ![k, x, y] SetTheory.kpair.dfn ↔ k = ZFSet.pair x y := by
  unfold SetTheory.kpair.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ x' : ZFSet.{0}, x' = ({x} : ZFSet.{0}) →
      ∀ z : ZFSet.{0}, z = ({x, y} : ZFSet.{0}) → k = ({x', z} : ZFSet.{0})).trans ?_
  · refine forall_congr' fun x' => ?_
    rw [stdEv_imp, stdEv_all]
    refine imp_congr ((stdEv_subst2 _ _ _ _).trans (ev_singleton x' x)) (forall_congr' fun z => ?_)
    rw [stdEv_imp]
    exact imp_congr
      ((stdEv_subst3 _ _ _ _ _).trans (ev_doubleton z x y))
      ((stdEv_subst3 _ _ _ _ _).trans (ev_doubleton k x' z))
  · unfold ZFSet.pair
    exact ⟨fun h => h ({x} : ZFSet.{0}) rfl ({x, y} : ZFSet.{0}) rfl,
      fun h x' hx' z hz => by subst hx' hz; exact h⟩

private def pi1Val (w : ZFSet.{0}) : ZFSet.{0} := ZFSet.sUnion (ZFSet.sInter w)

private def pi2Val (w : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sUnion ((ZFSet.sUnion w).sep (fun z => z ∈ ZFSet.sInter w → ZFSet.sUnion w = ZFSet.sInter w))

private lemma sInter_kpair (a b : ZFSet.{0}) :
    ZFSet.sInter (ZFSet.pair a b) = ({a} : ZFSet.{0}) := by
  have hne : (ZFSet.pair a b).Nonempty := ⟨({a} : ZFSet.{0}), by simp [ZFSet.pair]⟩
  ext z
  rw [ZFSet.mem_sInter hne, ZFSet.mem_singleton]
  constructor
  · intro h
    exact ZFSet.mem_singleton.mp (h ({a} : ZFSet.{0}) (by simp [ZFSet.pair]))
  · intro hza y hy
    subst hza
    have hy' : y = ({z} : ZFSet.{0}) ∨ y = ({z, b} : ZFSet.{0}) := by
      simpa [ZFSet.pair] using hy
    rcases hy' with rfl | rfl <;> simp

private lemma sUnion_kpair (a b : ZFSet.{0}) :
    ZFSet.sUnion (ZFSet.pair a b) = ({a, b} : ZFSet.{0}) := by
  ext z
  simp only [ZFSet.pair, ZFSet.mem_sUnion, ZFSet.mem_insert_iff, ZFSet.mem_singleton]
  constructor
  · rintro ⟨w, (rfl | rfl), hz⟩
    · exact Or.inl (ZFSet.mem_singleton.mp hz)
    · simpa [ZFSet.mem_insert_iff, ZFSet.mem_singleton] using hz
  · rintro (hza | hzb)
    · subst hza
      exact ⟨({z} : ZFSet.{0}), Or.inl rfl, ZFSet.mem_singleton.mpr rfl⟩
    · subst hzb
      exact ⟨({a, z} : ZFSet.{0}), Or.inr rfl, by simp⟩

private lemma pi1Val_pair (a b : ZFSet.{0}) : pi1Val (ZFSet.pair a b) = a := by
  unfold pi1Val
  rw [sInter_kpair, ZFSet.sUnion_singleton]

private lemma pi2Val_pair (a b : ZFSet.{0}) : pi2Val (ZFSet.pair a b) = b := by
  unfold pi2Val
  rw [sUnion_kpair, sInter_kpair]
  by_cases hab : a = b
  · subst hab
    have hsep : ({a, a} : ZFSet.{0}).sep
        (fun z => z ∈ ({a} : ZFSet.{0}) → ({a, a} : ZFSet.{0}) = ({a} : ZFSet.{0})) =
        ({a} : ZFSet.{0}) := by
      ext z
      simp [ZFSet.pair_eq_singleton]
    rw [hsep, ZFSet.sUnion_singleton]
  · have hne_ui : ({a, b} : ZFSet.{0}) ≠ ({a} : ZFSet.{0}) := by
      intro heq
      have hb : b ∈ ({a} : ZFSet.{0}) := heq ▸ (by simp : b ∈ ({a, b} : ZFSet.{0}))
      exact hab (ZFSet.mem_singleton.mp hb).symm
    have hsep : ({a, b} : ZFSet.{0}).sep
        (fun z => z ∈ ({a} : ZFSet.{0}) → ({a, b} : ZFSet.{0}) = ({a} : ZFSet.{0})) =
        ({b} : ZFSet.{0}) := by
      ext z
      simp only [ZFSet.mem_sep, ZFSet.mem_insert_iff, ZFSet.mem_singleton, hne_ui, imp_false]
      exact ⟨fun ⟨h1, h2⟩ => h1.resolve_left h2,
        fun hz => ⟨Or.inr hz, fun hza => hab (hza.symm.trans hz)⟩⟩
    rw [hsep, ZFSet.sUnion_singleton]

private lemma ev_pi1 (p w : ZFSet.{0}) :
    stdEv ![p, w] SetTheory.kpair.π₁.dfn ↔ p = pi1Val w := by
  unfold SetTheory.kpair.π₁.dfn pi1Val
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ i : ZFSet.{0}, i = ZFSet.sInter w → p = ZFSet.sUnion i).trans
    ⟨fun h => h (ZFSet.sInter w) rfl, fun h i hi => hi ▸ h⟩
  refine forall_congr' fun i => ?_
  rw [stdEv_imp]
  exact imp_congr
    ((stdEv_subst2 _ _ _ _).trans (ev_sInter i w))
    ((stdEv_subst2 _ _ _ _).trans (ev_sUnion p i))

private lemma ev_pi2 (p w : ZFSet.{0}) :
    stdEv ![p, w] SetTheory.kpair.π₂.dfn ↔ p = pi2Val w := by
  unfold SetTheory.kpair.π₂.dfn pi2Val
  rw [stdEv_all]
  let u0 := ZFSet.sUnion w
  let i0 := ZFSet.sInter w
  let s0 := u0.sep (fun z => z ∈ i0 → u0 = i0)
  refine (?_ : _ ↔ ∀ u : ZFSet.{0}, u = u0 → ∀ i : ZFSet.{0}, i = i0 →
      ∀ s : ZFSet.{0}, (∀ z : ZFSet.{0}, z ∈ s ↔ z ∈ u ∧ (z ∈ i → u = i)) →
        p = ZFSet.sUnion s).trans ?_
  · refine forall_congr' fun u => ?_
    rw [stdEv_imp, stdEv_all]
    refine imp_congr ((stdEv_subst2 _ _ _ _).trans (ev_sUnion u w)) (forall_congr' fun i => ?_)
    rw [stdEv_imp, stdEv_all]
    refine imp_congr ((stdEv_subst2 _ _ _ _).trans (ev_sInter i w)) (forall_congr' fun s => ?_)
    rw [stdEv_imp, stdEv_all]
    refine imp_congr (forall_congr' fun z => ?_) ((stdEv_subst2 _ _ _ _).trans (ev_sUnion p s))
    rw [stdEv_iff, stdEv_mem, stdEv_and, stdEv_mem, stdEv_imp, stdEv_mem, stdEv_eq]
    simp only [stdTv_bvar]
    rfl
  · constructor
    · intro h
      exact h u0 rfl i0 rfl s0 (fun z => ZFSet.mem_sep)
    · intro hp u hu i hi s hs
      subst hu hi
      have hseq : s = s0 := by
        ext z
        rw [hs z, ZFSet.mem_sep]
      rw [hseq, hp]

private lemma ev_prod (p X Y : ZFSet.{0}) :
    stdEv ![p, X, Y] SetTheory.prod.dfn ↔ p = ZFSet.prod X Y := by
  unfold SetTheory.prod.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ p ↔ ∃ x ∈ X, ∃ y ∈ Y, z = ZFSet.pair x y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [stdEv_iff, stdEv_mem, stdEv_bexsMem]
    simp only [stdTv_bvar]
    refine iff_congr Iff.rfl (exists_congr fun x => and_congr_right fun _ => ?_)
    rw [stdEv_bexsMem]
    simp only [stdTv_bvar]
    refine exists_congr fun y => and_congr_right fun _ => ?_
    exact (stdEv_subst3 _ _ _ _ _).trans (ev_kpair z x y)
  · simp_rw [← ZFSet.mem_prod]
    exact ⟨fun h => ZFSet.ext h, fun h z => by rw [h]⟩

private lemma ev_succ (y x : ZFSet.{0}) :
    stdEv ![y, x] SetTheory.succ.dfn ↔ y = insert x x := by
  unfold SetTheory.succ.dfn SetTheory.isSucc
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ y ↔ z = x ∨ z ∈ x).trans ?_
  · refine forall_congr' fun z => ?_
    rw [stdEv_iff, stdEv_mem, stdEv_or, stdEv_eq, stdEv_mem]
    simp only [stdTv_bvar]
    rfl
  · constructor
    · intro h
      ext z
      rw [h z, ZFSet.mem_insert_iff]
    · rintro rfl z
      rw [ZFSet.mem_insert_iff]

private lemma ev_IsInductive (I : ZFSet.{0}) :
    stdEv ![I] SetTheory.IsInductive.dfn ↔ (∅ ∈ I ∧ ∀ y ∈ I, insert y y ∈ I) := by
  unfold SetTheory.IsInductive.dfn
  rw [stdEv_and, stdEv_all, stdEv_ballMem]
  simp only [stdTv_bvar]
  refine and_congr ?_ ?_
  · refine (?_ : _ ↔ ∀ e : ZFSet.{0}, e = ∅ → e ∈ I).trans
      ⟨fun h => h ∅ rfl, fun h e he => he.symm ▸ h⟩
    refine forall_congr' fun e => ?_
    rw [stdEv_imp, stdEv_mem]
    simp only [stdTv_bvar]
    exact imp_congr ((stdEv_subst1 _ _ _).trans (ev_isEmpty e)) Iff.rfl
  · refine forall₂_congr fun y _ => ?_
    rw [stdEv_all]
    refine (?_ : _ ↔ ∀ y' : ZFSet.{0}, y' = insert y y → y' ∈ I).trans
      ⟨fun h => h (insert y y) rfl, fun h y' hy' => hy'.symm ▸ h⟩
    refine forall_congr' fun y' => ?_
    rw [stdEv_imp, stdEv_mem]
    simp only [stdTv_bvar]
    exact imp_congr ((stdEv_subst2 _ _ _ _).trans (ev_succ y' y)) Iff.rfl

private lemma dc_isω : DefinesConst SetTheory.isω vnOmega := by
  intro w
  unfold SetTheory.isω
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ x : ZFSet.{0},
      x ∈ w ↔ ∀ I : ZFSet.{0}, (∅ ∈ I ∧ ∀ y ∈ I, insert y y ∈ I) → x ∈ I).trans ?_
  · refine forall_congr' fun x => ?_
    rw [stdEv_iff, stdEv_mem, stdEv_all]
    simp only [stdTv_bvar]
    refine iff_congr Iff.rfl (forall_congr' fun I => ?_)
    rw [stdEv_imp, stdEv_mem]
    simp only [stdTv_bvar]
    exact imp_congr ((stdEv_subst1 _ _ _).trans (ev_IsInductive I)) Iff.rfl
  · simp_rw [← mem_vnOmega_iff_inductive]
    exact ⟨fun h => ZFSet.ext h, fun h x => by rw [h]⟩

/- `range.dfn`, `function.dfn`, `IsFunction.dfn`, `value.dfn` -/

private def relRange (R : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.sUnion (ZFSet.sUnion R)).sep (fun y => ∃ x, ZFSet.pair x y ∈ R)

private lemma mem_relRange {R y : ZFSet.{0}} :
    y ∈ relRange R ↔ ∃ x, ZFSet.pair x y ∈ R := by
  unfold relRange
  rw [ZFSet.mem_sep]
  refine ⟨And.right, fun ⟨x, hx⟩ => ⟨?_, x, hx⟩⟩
  rw [ZFSet.mem_sUnion]
  refine ⟨({x, y} : ZFSet.{0}), ?_, by simp⟩
  rw [ZFSet.mem_sUnion]
  exact ⟨ZFSet.pair x y, hx, by simp [ZFSet.pair]⟩

private lemma ev_range (r R : ZFSet.{0}) :
    stdEv ![r, R] SetTheory.range.dfn ↔ r = relRange R := by
  unfold SetTheory.range.dfn
  change stdEv ![r, R] (∀¹ _) ↔ _
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ y : ZFSet.{0}, y ∈ r ↔ ∃ x, ZFSet.pair x y ∈ R).trans ?_
  · refine forall_congr' fun y => ?_
    rw [stdEv_iff]
    refine iff_congr ?_ ?_
    · exact ev_faf_mem (et_bvar1 y _) (et_bvar3 _ y r _)
    · rw [stdEv_exs]
      refine exists_congr fun x => ?_
      exact ev_faf_mem
        (et_comp2 ev_kpair (et_bvar1 x _) (et_bvar2 x y _))
        (et_bvar5 _ x y r R _)
  · simp_rw [← mem_relRange]
    exact ⟨fun h => ZFSet.ext h, fun h y => by rw [h]⟩

private lemma ev_function (F Y X : ZFSet.{0}) :
    stdEv ![F, Y, X] SetTheory.function.dfn ↔ F = ZFSet.funs X Y := by
  unfold SetTheory.function.dfn
  change stdEv ![F, Y, X] (∀¹ _) ↔ _
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ f : ZFSet.{0}, f ∈ F ↔ f ∈ ZFSet.funs X Y).trans
    ⟨fun h => ZFSet.ext h, fun h f => by rw [h]⟩
  refine forall_congr' fun f => ?_
  rw [stdEv_iff]
  refine iff_congr (ev_faf_mem (et_bvar1 f _) (et_bvar3 _ f F _)) ?_
  rw [stdEv_and, ZFSet.mem_funs, ZFSet.IsFunc]
  refine and_congr ?_ ?_
  · rw [ev_nest2 SetTheory.isSubsetOf (et_bvar1 f _)
      (et_comp2 ev_prod (et_bvar4 f F Y X _) (et_bvar3 f F Y _)), ev_isSubsetOf]
  · rw [ev_faf_ball (et_bvar4 f F Y X _)]
    refine forall₂_congr fun x _ => ?_
    rw [ev_existsUnique]
    refine existsUnique_congr fun y => ?_
    exact ev_faf_mem
      (et_comp2 ev_kpair (et_bvar2 y x _) (et_bvar1 y _))
      (et_bvar5 _ y x _ f _)

private lemma ev_IsFunction (f : ZFSet.{0}) :
    stdEv ![f] SetTheory.IsFunction.dfn ↔ ∃ X Y : ZFSet.{0}, f ∈ ZFSet.funs X Y := by
  unfold SetTheory.IsFunction.dfn
  change stdEv ![f] (∃¹ ∃¹ _) ↔ _
  rw [stdEv_exs]
  refine exists_congr fun X => ?_
  rw [stdEv_exs]
  refine exists_congr fun Y => ?_
  exact ev_faf_mem (et_bvar3 Y X f _)
    (et_comp2 ev_function (et_bvar2 _ Y _) (et_bvar3 _ Y X _))

private def zfcApp (f x : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.sUnion (relRange f)).sep (fun z => ∃ y, z ∈ y ∧ ZFSet.pair x y ∈ f)

private lemma ev_value (v f x : ZFSet.{0}) :
    stdEv ![v, f, x] SetTheory.value.dfn ↔ v = zfcApp f x := by
  unfold SetTheory.value.dfn
  change stdEv ![v, f, x] (∀¹ _) ↔ _
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ z : ZFSet.{0},
      z ∈ v ↔ z ∈ ZFSet.sUnion (relRange f) ∧ ∃ y, z ∈ y ∧ ZFSet.pair x y ∈ f).trans ?_
  · refine forall_congr' fun z => ?_
    rw [stdEv_iff]
    refine iff_congr (ev_faf_mem (et_bvar1 z _) (et_bvar3 _ z v _)) ?_
    rw [stdEv_and]
    refine and_congr ?_ ?_
    · exact ev_faf_mem (et_bvar1 z _)
        (et_comp1 ev_sUnion (et_comp1 ev_range (et_bvar4 _ z v f _)))
    · rw [stdEv_exs]
      refine exists_congr fun y => ?_
      rw [stdEv_and]
      refine and_congr
        (ev_faf_mem (et_bvar2 y z _) (et_bvar2 _ y _))
        (ev_faf_mem (et_comp2 ev_kpair (et_bvar5 y z v f x _) (et_bvar1 y _))
          (et_bvar5 _ y z v f _))
  · unfold zfcApp
    constructor
    · intro h
      ext z
      rw [h z, ZFSet.mem_sep]
    · rintro rfl z
      rw [ZFSet.mem_sep]

private lemma zfcApp_of_mem_funs {X Y f x y : ZFSet.{0}}
    (hf : f ∈ ZFSet.funs X Y) (_hx : x ∈ X) (hpair : ZFSet.pair x y ∈ f) :
    zfcApp f x = y := by
  rw [ZFSet.mem_funs] at hf
  obtain ⟨_, huniq⟩ := hf
  obtain ⟨y0, hy0_mem, hy0_eq⟩ := huniq x _hx
  have hy_eq : y = y0 := hy0_eq y hpair
  subst hy_eq
  ext z
  unfold zfcApp
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y', hz', hp'⟩
    have rfl' : y' = y := hy0_eq y' hp'
    rwa [← rfl']
  · intro hz
    refine ⟨?_, y, hz, hy0_mem⟩
    rw [ZFSet.mem_sUnion]
    exact ⟨y, mem_relRange.mpr ⟨x, hy0_mem⟩, hz⟩

private lemma zfcApp_mem_codomain {X Y f x : ZFSet.{0}}
    (hf : f ∈ ZFSet.funs X Y) (hx : x ∈ X) :
    zfcApp f x ∈ Y := by
  have hf' := ZFSet.mem_funs.mp hf
  obtain ⟨y, hy, _⟩ := hf'.2 x hx
  rw [zfcApp_of_mem_funs hf hx hy]
  exact (ZFSet.pair_mem_prod.mp (hf'.1 hy)).2

private lemma funs_ext {X Y f1 f2 : ZFSet.{0}}
    (hf1 : f1 ∈ ZFSet.funs X Y) (hf2 : f2 ∈ ZFSet.funs X Y)
    (heq : ∀ x ∈ X, zfcApp f1 x = zfcApp f2 x) : f1 = f2 := by
  obtain ⟨hsub1, huniq1⟩ := ZFSet.mem_funs.mp hf1
  obtain ⟨hsub2, huniq2⟩ := ZFSet.mem_funs.mp hf2
  ext p
  constructor
  · intro hp1
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.mp (hsub1 hp1)
    have ha1 := zfcApp_of_mem_funs hf1 hx hp1
    obtain ⟨y2, hy2, _⟩ := huniq2 x hx
    have ha2 := zfcApp_of_mem_funs hf2 hx hy2
    have hy_eq : y = y2 := by rw [← ha1, heq x hx, ha2]
    rwa [hy_eq]
  · intro hp2
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.mp (hsub2 hp2)
    have ha2 := zfcApp_of_mem_funs hf2 hx hp2
    obtain ⟨y1, hy1, _⟩ := huniq1 x hx
    have ha1 := zfcApp_of_mem_funs hf1 hx hy1
    have hy_eq : y = y1 := by rw [← ha2, ← heq x hx, ha1]
    rwa [hy_eq]

/- `Constant14` numerals, finite sets, and encoded integers -/

private lemma dc_zero : DefinesConst Constant14.zero ∅ := by
  intro z
  unfold Constant14.zero
  exact (stdEv_subst1 _ _ _).trans (ev_isEmpty z)

private lemma dc_numeral (k : ℕ) : DefinesConst (Constant14.numeral k) (vnNat k) := by
  induction k with
  | zero => exact dc_zero
  | succ k ih =>
    intro y
    unfold Constant14.numeral vnNat
    exact et_comp1 ev_succ ih y

private lemma dc_setPair {Ψ₁ Ψ₂ : SetTheorySemisentence 1} {v₁ v₂ : ZFSet.{0}}
    (h₁ : DefinesConst Ψ₁ v₁) (h₂ : DefinesConst Ψ₂ v₂) :
    DefinesConst (Constant14.setPair Ψ₁ Ψ₂) (ZFSet.pair v₁ v₂) := by
  intro y
  unfold Constant14.setPair
  have h := et_comp2 ev_kpair (h₁ ·) (h₂ ·) y
  rwa [stdEv_e1] at h

private lemma dc_setTriple {Ψ₁ Ψ₂ Ψ₃ : SetTheorySemisentence 1} {v₁ v₂ v₃ : ZFSet.{0}}
    (h₁ : DefinesConst Ψ₁ v₁) (h₂ : DefinesConst Ψ₂ v₂) (h₃ : DefinesConst Ψ₃ v₃) :
    DefinesConst (Constant14.setTriple Ψ₁ Ψ₂ Ψ₃) (ZFSet.pair v₁ (ZFSet.pair v₂ v₃)) :=
  dc_setPair h₁ (dc_setPair h₂ h₃)

private def listToZFSet : List ZFSet.{0} → ZFSet.{0}
  | [] => ∅
  | x :: xs => insert x (listToZFSet xs)

private lemma mem_listToZFSet {z : ZFSet.{0}} {xs : List ZFSet.{0}} :
    z ∈ listToZFSet xs ↔ z ∈ xs := by
  induction xs with
  | nil => simp [listToZFSet]
  | cons x xs ih => simp [listToZFSet, ih]

private lemma dc_finiteSet_map {α : Type*} (l : List α)
    (fForm : α → SetTheorySemisentence 1) (fVal : α → ZFSet.{0})
    (hf : ∀ a, DefinesConst (fForm a) (fVal a)) :
    DefinesConst (Constant14.finiteSet (l.map fForm)) (listToZFSet (l.map fVal)) := by
  induction l with
  | nil => exact dc_zero
  | cons a as ih =>
    intro y
    simp only [List.map_cons, Constant14.finiteSet, listToZFSet]
    have h := et_comp2 ev_insert (hf a ·) (ih ·) y
    rwa [stdEv_e1] at h

private noncomputable def intSet : ZFSet.{0} := ZFSet.prod (vnNat 2) vnOmega

private lemma dc_integers : DefinesConst Constant14.integers intSet := by
  intro y
  unfold Constant14.integers intSet
  exact ev_faf_eq (et_bvar1 y _)
    (et_comp2 ev_prod (et_const0 (dc_numeral 2) _) (et_const0 dc_isω _))

private def encodeInt : ℤ → ZFSet.{0}
  | Int.ofNat k => ZFSet.pair (vnNat 0) (vnNat k)
  | Int.negSucc k => ZFSet.pair (vnNat 1) (vnNat k)

private lemma encodeInt_mem (z : ℤ) : encodeInt z ∈ intSet := by
  unfold intSet
  cases z with
  | ofNat k =>
    exact ZFSet.pair_mem_prod.mpr
      ⟨vnNat_lt_mem (by decide : 0 < 2), ZFSet.mem_range.mpr ⟨k, rfl⟩⟩
  | negSucc k =>
    exact ZFSet.pair_mem_prod.mpr
      ⟨vnNat_lt_mem (by decide : 1 < 2), ZFSet.mem_range.mpr ⟨k, rfl⟩⟩

private lemma mem_intSet_iff {w : ZFSet.{0}} :
    w ∈ intSet ↔ ∃ z : ℤ, w = encodeInt z := by
  refine ⟨?_, fun ⟨z, hz⟩ => hz ▸ encodeInt_mem z⟩
  unfold intSet vnOmega
  intro hw
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hw
  obtain ⟨s, hs, rfl⟩ := mem_vnNat_iff.mp ha
  obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hb
  interval_cases s
  · exact ⟨Int.ofNat k, rfl⟩
  · exact ⟨Int.negSucc k, rfl⟩

private lemma encodeInt_injective : Function.Injective encodeInt := by
  intro z1 z2 heq
  cases z1 <;> cases z2 <;> simp only [encodeInt, ZFSet.pair_inj] at heq
  · rw [vnNat_injective heq.2]
  · exfalso; exact absurd (vnNat_injective heq.1) (by decide)
  · exfalso; exact absurd (vnNat_injective heq.1) (by decide)
  · rw [vnNat_injective heq.2]

private lemma dc_integerZero : DefinesConst Constant14.integerZero (encodeInt 0) := by
  intro y
  unfold Constant14.integerZero
  exact ev_faf_eq (et_bvar1 y _)
    (et_comp2 ev_kpair (et_const0 (dc_numeral 0) _) (et_const0 (dc_numeral 0) _))

private lemma ev_integerSucc_encode (z : ℤ) (w' : ZFSet.{0}) :
    stdEv ![w', encodeInt z] Constant14.integerSucc.dfn ↔ w' = encodeInt (z + 1) := by
  unfold Constant14.integerSucc.dfn
  rw [stdEv_or, stdEv_and, stdEv_and]
  rw [ev_faf_mem (et_bvar2 w' (encodeInt z) _) (et_const0 dc_integers _),
      ev_faf_notMem (et_bvar2 w' (encodeInt z) _) (et_const0 dc_integers _)]
  simp only [encodeInt_mem z, not_true_eq_false, false_and, or_false, true_and]
  refine (?_ : _ ↔
      ((pi1Val (encodeInt z) = vnNat 0 ∧
          w' = ZFSet.pair (vnNat 0) (insert (pi2Val (encodeInt z)) (pi2Val (encodeInt z)))) ∨
        (pi1Val (encodeInt z) = vnNat 1 ∧
          ((pi2Val (encodeInt z) = vnNat 0 ∧ w' = encodeInt 0) ∨
            ∃ m ∈ vnOmega, pi2Val (encodeInt z) = insert m m ∧
              w' = ZFSet.pair (vnNat 1) m)))).trans ?_
  · rw [stdEv_or, stdEv_and, stdEv_and, stdEv_or, stdEv_and]
    refine or_congr
      (and_congr
        (ev_faf_eq (et_comp1 ev_pi1 (et_bvar2 w' (encodeInt z) _)) (et_const0 (dc_numeral 0) _))
        (ev_faf_eq (et_bvar1 w' _)
          (et_comp2 ev_kpair (et_const0 (dc_numeral 0) _)
            (et_comp1 ev_succ (et_comp1 ev_pi2 (et_bvar3 _ w' (encodeInt z) _))))))
      (and_congr
        (ev_faf_eq (et_comp1 ev_pi1 (et_bvar2 w' (encodeInt z) _)) (et_const0 (dc_numeral 1) _))
        (or_congr
          (and_congr
            (ev_faf_eq (et_comp1 ev_pi2 (et_bvar2 w' (encodeInt z) _)) (et_const0 (dc_numeral 0) _))
            (ev_faf_eq (et_bvar1 w' _) (et_const0 dc_integerZero _)))
          ?_))
    rw [ev_faf_bexs (et_const0 dc_isω _)]
    refine exists_congr fun m => and_congr_right fun _ => ?_
    rw [stdEv_and]
    exact and_congr
      (ev_faf_eq (et_comp1 ev_pi2 (et_bvar4 m vnOmega w' (encodeInt z) _))
        (et_comp1 ev_succ (et_bvar2 _ m _)))
      (ev_faf_eq (et_bvar3 m vnOmega w' _)
        (et_comp2 ev_kpair (et_const0 (dc_numeral 1) _) (et_bvar2 _ m _)))
  · have h01 : vnNat 0 ≠ vnNat 1 := fun h => absurd (vnNat_injective h) (by decide)
    have h10 : vnNat 1 ≠ vnNat 0 := h01.symm
    cases z with
    | ofNat k =>
      simp only [encodeInt, pi1Val_pair, pi2Val_pair, h01, false_and, or_false, true_and]
      rfl
    | negSucc k =>
      simp only [encodeInt, pi1Val_pair, pi2Val_pair, h10, false_and, false_or, true_and]
      cases k with
      | zero =>
        have hno_pred : ¬ ∃ m ∈ vnOmega, vnNat 0 = insert m m ∧ w' = ZFSet.pair (vnNat 1) m := by
          rintro ⟨m, _, hm, _⟩
          have : m ∈ vnNat 0 := hm ▸ ZFSet.mem_insert m m
          exact ZFSet.notMem_empty m this
        simp only [true_and, hno_pred, or_false]
        rfl
      | succ k =>
        have hne0 : vnNat (k + 1) ≠ vnNat 0 := fun h => absurd (vnNat_injective h) (by omega)
        simp only [hne0, false_and, false_or]
        constructor
        · rintro ⟨m, hm, hsucc, rfl⟩
          obtain ⟨r, rfl⟩ := ZFSet.mem_range.mp hm
          have hr : k + 1 = r + 1 := vnNat_injective hsucc
          have hk : r = k := by omega
          subst hk
          rfl
        · rintro rfl
          exact ⟨vnNat k, ZFSet.mem_range.mpr ⟨k, rfl⟩, rfl, rfl⟩

private lemma ev_integerPred_encode (z : ℤ) (w' : ZFSet.{0}) :
    stdEv ![w', encodeInt z] Constant14.integerPred.dfn ↔ w' = encodeInt (z - 1) := by
  unfold Constant14.integerPred.dfn
  rw [stdEv_or, stdEv_and, stdEv_and, stdEv_and]
  rw [ev_faf_mem (et_bvar2 w' (encodeInt z) _) (et_const0 dc_integers _),
      ev_faf_mem (et_bvar1 w' _) (et_const0 dc_integers _),
      ev_nest2 Constant14.integerSucc.dfn (et_bvar2 w' (encodeInt z) _) (et_bvar1 w' _),
      ev_faf_notMem (et_bvar2 w' (encodeInt z) _) (et_const0 dc_integers _)]
  simp only [encodeInt_mem z, not_true_eq_false, false_and, or_false, true_and]
  constructor
  · rintro ⟨hw', hsucc⟩
    obtain ⟨u, rfl⟩ := mem_intSet_iff.mp hw'
    rw [ev_integerSucc_encode u (encodeInt z)] at hsucc
    have hzu : z = u + 1 := encodeInt_injective hsucc
    have hu : u = z - 1 := by omega
    rw [hu]
  · rintro rfl
    refine ⟨encodeInt_mem (z - 1), ?_⟩
    rw [ev_integerSucc_encode (z - 1) (encodeInt z)]
    congr 1
    omega

/- ## Section 4: Instruction Table, Configurations, `nextStep`, `orbit`, and `halts` -/

private noncomputable def cfgSetVal (N : ℕ) : ZFSet.{0} :=
  ZFSet.prod (vnNat N) (ZFSet.prod intSet (ZFSet.funs intSet (vnNat 2)))

private lemma dc_configSet (N : ℕ) : DefinesConst (Constant14.configSet N) (cfgSetVal N) := by
  intro y
  unfold Constant14.configSet cfgSetVal
  exact ev_faf_eq (et_bvar1 y _)
    (et_comp2 ev_prod (et_const0 (dc_numeral N) _)
      (et_comp2 ev_prod (et_const0 dc_integers _)
        (et_comp2 ev_function (et_const0 (dc_numeral 2) _) (et_const0 dc_integers _))))

private lemma mem_cfgSetVal_iff {N : ℕ} {z : ZFSet.{0}} :
    z ∈ cfgSetVal N ↔
      ∃ (qCode : ℕ) (pos : ℤ) (g : ZFSet.{0}),
        qCode < N ∧ g ∈ ZFSet.funs intSet (vnNat 2) ∧
          z = ZFSet.pair (vnNat qCode) (ZFSet.pair (encodeInt pos) g) := by
  unfold cfgSetVal
  constructor
  · intro hz
    obtain ⟨s, hs, p, hp, rfl⟩ := ZFSet.mem_prod.mp hz
    obtain ⟨qCode, hq, rfl⟩ := mem_vnNat_iff.mp hs
    obtain ⟨w, hw, g, hg, rfl⟩ := ZFSet.mem_prod.mp hp
    obtain ⟨pos, rfl⟩ := mem_intSet_iff.mp hw
    exact ⟨qCode, pos, g, hq, hg, rfl⟩
  · rintro ⟨qCode, pos, g, hq, hg, rfl⟩
    exact ZFSet.pair_mem_prod.mpr
      ⟨vnNat_lt_mem hq, ZFSet.pair_mem_prod.mpr ⟨encodeInt_mem pos, hg⟩⟩

private def entryForm (t : ℕ × ℕ × ℕ × ℕ × ℕ) : SetTheorySemisentence 1 :=
  Constant14.transitionEntry t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2

private def entryVal (t : ℕ × ℕ × ℕ × ℕ × ℕ) : ZFSet.{0} :=
  ZFSet.pair (ZFSet.pair (vnNat t.1) (vnNat t.2.1))
    (ZFSet.pair (vnNat t.2.2.1) (ZFSet.pair (vnNat t.2.2.2.1) (vnNat t.2.2.2.2)))

private lemma dc_entryForm (t : ℕ × ℕ × ℕ × ℕ × ℕ) :
    DefinesConst (entryForm t) (entryVal t) := by
  unfold entryForm Constant14.transitionEntry entryVal
  exact dc_setPair (dc_setPair (dc_numeral _) (dc_numeral _))
    (dc_setTriple (dc_numeral _) (dc_numeral _) (dc_numeral _))

private def transTuples {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (List.ofFn fun q : Fin n =>
    List.ofFn fun sym : Fin 2 =>
      let o := Constant14.transitionCode M q sym
      (q.val, sym.val, o.1, o.2.1, o.2.2)).flatten ++
  List.ofFn fun sym : Fin 2 =>
    (n, sym.val, n, sym.val, Constant14.directionCode none)

private def instrTableVal {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : ZFSet.{0} :=
  listToZFSet ((transTuples M).map entryVal)

private lemma dc_instructionTable {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    DefinesConst (Constant14.instructionTable M) (instrTableVal M) := by
  unfold Constant14.instructionTable instrTableVal
  have hmap : (transTuples M).map entryForm = Constant14.transitionEntries M := by
    simp [transTuples, Constant14.transitionEntries, entryForm, List.map_flatten,
      List.map_ofFn, Function.comp_def]
  rw [← hmap]
  exact dc_finiteSet_map (transTuples M) entryForm entryVal dc_entryForm

private def transLookup {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (qCode symCode : ℕ) : ℕ × ℕ × ℕ :=
  if hq : qCode < n then
    if hs : symCode < 2 then
      Constant14.transitionCode M ⟨qCode, hq⟩ ⟨symCode, hs⟩
    else (n, 0, 1)
  else (n, symCode, 1)

private lemma transitionCode_bounds {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (q : Fin n) (sym : Fin 2) :
    let o := Constant14.transitionCode M q sym
    o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
  dsimp only [Constant14.transitionCode]
  cases M q sym with
  | none =>
    dsimp only [Constant14.directionCode]
    exact ⟨Nat.lt_succ_self n, sym.isLt, by decide⟩
  | some p =>
    rcases p with ⟨q', ⟨sym', d⟩⟩
    dsimp only
    refine ⟨?_, sym'.isLt, ?_⟩
    · cases q' with
      | none => exact Nat.lt_succ_self n
      | some qv => exact Nat.lt_succ_of_lt qv.isLt
    · cases d <;> decide

private lemma instrTableVal_funs_and_app {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    instrTableVal M ∈ ZFSet.funs
        (ZFSet.prod (vnNat (n + 1)) (vnNat 2))
        (ZFSet.prod (vnNat (n + 1)) (ZFSet.prod (vnNat 2) (vnNat 3))) ∧
      ∀ (qCode symCode : ℕ), qCode < n + 1 → symCode < 2 →
        zfcApp (instrTableVal M) (ZFSet.pair (vnNat qCode) (vnNat symCode)) =
          let o := transLookup M qCode symCode
          ZFSet.pair (vnNat o.1) (ZFSet.pair (vnNat o.2.1) (vnNat o.2.2)) := by
  have hmem_iff : ∀ p : ZFSet.{0}, p ∈ instrTableVal M ↔
      (∃ (q : Fin n) (sym : Fin 2),
        let o := Constant14.transitionCode M q sym
        p = entryVal (q.val, sym.val, o.1, o.2.1, o.2.2)) ∨
      (∃ sym : Fin 2, p = entryVal (n, sym.val, n, sym.val, 1)) := by
    intro p
    unfold instrTableVal
    rw [mem_listToZFSet, List.mem_map]
    simp only [transTuples, List.mem_append, List.mem_flatten, List.mem_ofFn,
      Constant14.directionCode]
    constructor
    · rintro ⟨t, (⟨l, ⟨q, rfl⟩, ht⟩ | ⟨sym, rfl⟩), rfl⟩
      · obtain ⟨sym, rfl⟩ := List.mem_ofFn.mp ht
        exact Or.inl ⟨q, sym, rfl⟩
      · exact Or.inr ⟨sym, rfl⟩
    · rintro (⟨q, sym, rfl⟩ | ⟨sym, rfl⟩)
      · refine ⟨_, Or.inl ⟨_, ⟨q, rfl⟩, List.mem_ofFn.mpr ⟨sym, rfl⟩⟩, rfl⟩
      · exact ⟨_, Or.inr ⟨sym, rfl⟩, rfl⟩
  have hfuns : instrTableVal M ∈ ZFSet.funs
      (ZFSet.prod (vnNat (n + 1)) (vnNat 2))
      (ZFSet.prod (vnNat (n + 1)) (ZFSet.prod (vnNat 2) (vnNat 3))) := by
    rw [ZFSet.mem_funs, ZFSet.IsFunc]
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases (hmem_iff p).mp hp with ⟨q, sym, rfl⟩ | ⟨sym, rfl⟩
      · obtain ⟨hb1, hb2, hb3⟩ := transitionCode_bounds M q sym
        exact ZFSet.pair_mem_prod.mpr
          ⟨ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem (Nat.lt_succ_of_lt q.isLt), vnNat_lt_mem sym.isLt⟩,
           ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem hb1,
             ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem hb2, vnNat_lt_mem hb3⟩⟩⟩
      · exact ZFSet.pair_mem_prod.mpr
          ⟨ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem (Nat.lt_succ_self n), vnNat_lt_mem sym.isLt⟩,
           ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem (Nat.lt_succ_self n),
             ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem sym.isLt, vnNat_lt_mem (by decide : 1 < 3)⟩⟩⟩
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hx
      obtain ⟨qCode, hq, rfl⟩ := mem_vnNat_iff.mp ha
      obtain ⟨symCode, hs, rfl⟩ := mem_vnNat_iff.mp hb
      let o := transLookup M qCode symCode
      refine ⟨ZFSet.pair (vnNat o.1) (ZFSet.pair (vnNat o.2.1) (vnNat o.2.2)), ?_, ?_⟩
      · dsimp only
        rw [hmem_iff]
        by_cases hqn : qCode < n
        · left
          refine ⟨⟨qCode, hqn⟩, ⟨symCode, hs⟩, ?_⟩
          dsimp only [o, transLookup]; rw [dif_pos hqn, dif_pos hs]; rfl
        · have hqe : qCode = n := by omega
          subst qCode
          right
          refine ⟨⟨symCode, hs⟩, ?_⟩
          dsimp only [o, transLookup]; rw [dif_neg (Nat.lt_irrefl n)]; rfl
      · intro y hy
        rcases (hmem_iff _).mp hy with ⟨q, sym, heq⟩ | ⟨sym, heq⟩
        · obtain ⟨h1, rfl⟩ := ZFSet.pair_injective heq
          obtain ⟨hq1, hs1⟩ := ZFSet.pair_injective h1
          have hqc : qCode = q.val := vnNat_injective hq1
          have hsc : symCode = sym.val := vnNat_injective hs1
          subst qCode symCode
          dsimp only [o, transLookup]
          rw [dif_pos q.isLt, dif_pos sym.isLt]
        · obtain ⟨h1, rfl⟩ := ZFSet.pair_injective heq
          obtain ⟨hq1, hs1⟩ := ZFSet.pair_injective h1
          have hqc : qCode = n := vnNat_injective hq1
          have hsc : symCode = sym.val := vnNat_injective hs1
          subst qCode symCode
          dsimp only [o, transLookup]
          rw [dif_neg (Nat.lt_irrefl n)]
  refine ⟨hfuns, fun qCode symCode hq hs => ?_⟩
  have hx : ZFSet.pair (vnNat qCode) (vnNat symCode) ∈ ZFSet.prod (vnNat (n + 1)) (vnNat 2) :=
    ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem hq, vnNat_lt_mem hs⟩
  let o := transLookup M qCode symCode
  have hmem_pair : ZFSet.pair (ZFSet.pair (vnNat qCode) (vnNat symCode))
      (ZFSet.pair (vnNat o.1) (ZFSet.pair (vnNat o.2.1) (vnNat o.2.2))) ∈ instrTableVal M := by
    rw [hmem_iff]
    by_cases hqn : qCode < n
    · left; refine ⟨⟨qCode, hqn⟩, ⟨symCode, hs⟩, ?_⟩
      dsimp only [o, transLookup]; rw [dif_pos hqn, dif_pos hs]; rfl
    · have hqe : qCode = n := by omega
      subst qCode
      right; refine ⟨⟨symCode, hs⟩, ?_⟩
      dsimp only [o, transLookup]; rw [dif_neg (Nat.lt_irrefl n)]; rfl
  exact zfcApp_of_mem_funs hfuns hx hmem_pair

/- ZFC-level one-step configuration function `zfcStepFn` -/

private noncomputable def zfcUpdateTape (g posSet valSet : ZFSet.{0}) : ZFSet.{0} :=
  letI : ZFSet.Definable₁ (fun w => if w = posSet then valSet else zfcApp g w) :=
    Classical.allZFSetDefinable _
  ZFSet.map (fun w => if w = posSet then valSet else zfcApp g w) intSet

private lemma zfcUpdateTape_mem_funs {g posSet valSet : ZFSet.{0}}
    (hg : g ∈ ZFSet.funs intSet (vnNat 2)) (hval : valSet ∈ vnNat 2) :
    zfcUpdateTape g posSet valSet ∈ ZFSet.funs intSet (vnNat 2) := by
  let fn : ZFSet.{0} → ZFSet.{0} := fun w => if w = posSet then valSet else zfcApp g w
  let _ : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
  change ZFSet.map fn intSet ∈ ZFSet.funs intSet (vnNat 2)
  rw [ZFSet.mem_funs, ZFSet.map_isFunc]
  intro w hw
  dsimp [fn]
  split_ifs
  · exact hval
  · exact zfcApp_mem_codomain hg hw

private lemma zfcUpdateTape_app {g posSet valSet w : ZFSet.{0}}
    (hg : g ∈ ZFSet.funs intSet (vnNat 2)) (hval : valSet ∈ vnNat 2) (hw : w ∈ intSet) :
    zfcApp (zfcUpdateTape g posSet valSet) w =
      if w = posSet then valSet else zfcApp g w := by
  let fn : ZFSet.{0} → ZFSet.{0} := fun u => if u = posSet then valSet else zfcApp g u
  let _ : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
  have hfuns : zfcUpdateTape g posSet valSet ∈ ZFSet.funs intSet (vnNat 2) :=
    zfcUpdateTape_mem_funs hg hval
  have hmem : ZFSet.pair w (fn w) ∈ zfcUpdateTape g posSet valSet := by
    change ZFSet.pair w (fn w) ∈ ZFSet.map fn intSet
    exact ZFSet.mem_map.mpr ⟨w, hw, rfl⟩
  exact zfcApp_of_mem_funs hfuns hw hmem

private noncomputable def decodePos (w : ZFSet.{0}) : ℤ :=
  if hw : w ∈ intSet then Classical.choose (mem_intSet_iff.mp hw) else 0

private lemma decodePos_encodeInt (p : ℤ) : decodePos (encodeInt p) = p := by
  unfold decodePos
  rw [dif_pos (encodeInt_mem p)]
  exact encodeInt_injective (Classical.choose_spec (mem_intSet_iff.mp (encodeInt_mem p))).symm

private noncomputable def zfcStepFn {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (z : ZFSet.{0}) : ZFSet.{0} :=
  if z ∈ cfgSetVal (n + 1) then
    let qSet := pi1Val z
    let posSet := pi1Val (pi2Val z)
    let g := pi2Val (pi2Val z)
    let symSet := zfcApp g posSet
    let t := zfcApp (instrTableVal M) (ZFSet.pair qSet symSet)
    let qNext := pi1Val t
    let wrSet := pi1Val (pi2Val t)
    let dirSet := pi2Val (pi2Val t)
    let posVal := decodePos posSet
    let posNext : ZFSet.{0} :=
      if dirSet = vnNat 0 then encodeInt (posVal - 1)
      else if dirSet = vnNat 1 then encodeInt posVal
      else encodeInt (posVal + 1)
    let gNext := zfcUpdateTape g posSet wrSet
    ZFSet.pair qNext (ZFSet.pair posNext gNext)
  else ∅

private lemma zfcStepFn_of_cfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (qCode : ℕ) (pos : ℤ) (g : ZFSet.{0})
    (hq : qCode < n + 1) (hg : g ∈ ZFSet.funs intSet (vnNat 2))
    (symCode : ℕ) (hs : symCode < 2) (hsym : zfcApp g (encodeInt pos) = vnNat symCode) :
    let o := transLookup M qCode symCode
    let pos' : ℤ := if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1
    zfcStepFn M (ZFSet.pair (vnNat qCode) (ZFSet.pair (encodeInt pos) g)) =
      ZFSet.pair (vnNat o.1)
        (ZFSet.pair (encodeInt pos') (zfcUpdateTape g (encodeInt pos) (vnNat o.2.1))) := by
  let z := ZFSet.pair (vnNat qCode) (ZFSet.pair (encodeInt pos) g)
  have hz : z ∈ cfgSetVal (n + 1) := mem_cfgSetVal_iff.mpr ⟨qCode, pos, g, hq, hg, rfl⟩
  unfold zfcStepFn
  rw [if_pos hz]
  dsimp only
  have hp1 : pi1Val z = vnNat qCode := pi1Val_pair _ _
  have hp2 : pi2Val z = ZFSet.pair (encodeInt pos) g := pi2Val_pair _ _
  have hpos : pi1Val (pi2Val z) = encodeInt pos := by rw [hp2, pi1Val_pair]
  have hgv : pi2Val (pi2Val z) = g := by rw [hp2, pi2Val_pair]
  obtain ⟨_, happ⟩ := instrTableVal_funs_and_app M
  let o := transLookup M qCode symCode
  have ht : zfcApp (instrTableVal M)
      (ZFSet.pair (pi1Val z) (zfcApp (pi2Val (pi2Val z)) (pi1Val (pi2Val z)))) =
      ZFSet.pair (vnNat o.1) (ZFSet.pair (vnNat o.2.1) (vnNat o.2.2)) := by
    rw [hp1, hgv, hpos, hsym]
    exact happ qCode symCode hq hs
  rw [ht, pi1Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, hpos, hgv, decodePos_encodeInt]
  congr 1; congr 1
  have hd0 : (vnNat o.2.2 = vnNat 0) ↔ (o.2.2 = 0) := vnNat_injective.eq_iff
  have hd1 : (vnNat o.2.2 = vnNat 1) ↔ (o.2.2 = 1) := vnNat_injective.eq_iff
  simp only [hd0, hd1]
  dsimp only [o]
  split_ifs <;> rfl

private lemma zfcStepFn_mem_cfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    {z : ZFSet.{0}} (hz : z ∈ cfgSetVal (n + 1)) :
    zfcStepFn M z ∈ cfgSetVal (n + 1) := by
  obtain ⟨qCode, pos, g, hq, hg, rfl⟩ := mem_cfgSetVal_iff.mp hz
  have hsym_mem : zfcApp g (encodeInt pos) ∈ vnNat 2 :=
    zfcApp_mem_codomain hg (encodeInt_mem pos)
  obtain ⟨symCode, hs, hsym⟩ := mem_vnNat_iff.mp hsym_mem
  rw [zfcStepFn_of_cfg M qCode pos g hq hg symCode hs hsym]
  let o := transLookup M qCode symCode
  have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
    dsimp only [o, transLookup]
    by_cases hqn : qCode < n
    · rw [dif_pos hqn, dif_pos hs]
      exact transitionCode_bounds M ⟨qCode, hqn⟩ ⟨symCode, hs⟩
    · rw [dif_neg hqn]
      dsimp only
      exact ⟨Nat.lt_succ_self n, hs, by decide⟩
  exact mem_cfgSetVal_iff.mpr
    ⟨o.1, if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1,
     zfcUpdateTape g (encodeInt pos) (vnNat o.2.1),
     hob.1, zfcUpdateTape_mem_funs hg (vnNat_lt_mem hob.2.1), rfl⟩

private lemma ev_nextConfig_iff {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (z' z : ZFSet.{0}) :
    stdEv ![z', z] (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) ↔
      z ∈ cfgSetVal (n + 1) ∧ z' = zfcStepFn M z := by
  unfold Constant14.nextConfig
  rw [stdEv_and, stdEv_and]
  rw [ev_faf_mem (et_bvar2 z' z _) (et_const0 (dc_configSet (n + 1)) _),
      ev_faf_mem (et_bvar1 z' _) (et_const0 (dc_configSet (n + 1)) _)]
  by_cases hz : z ∈ cfgSetVal (n + 1)
  · simp only [hz, true_and]
    obtain ⟨qCode, pos, g, hq, hg, rfl⟩ := mem_cfgSetVal_iff.mp hz
    let z0 := ZFSet.pair (vnNat qCode) (ZFSet.pair (encodeInt pos) g)
    have hsym_mem : zfcApp g (encodeInt pos) ∈ vnNat 2 :=
      zfcApp_mem_codomain hg (encodeInt_mem pos)
    obtain ⟨symCode, hs, hsym⟩ := mem_vnNat_iff.mp hsym_mem
    let o := transLookup M qCode symCode
    have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
      dsimp only [o, transLookup]
      by_cases hqn : qCode < n
      · rw [dif_pos hqn, dif_pos hs]
        exact transitionCode_bounds M ⟨qCode, hqn⟩ ⟨symCode, hs⟩
      · rw [dif_neg hqn]
        dsimp only
        exact ⟨Nat.lt_succ_self n, hs, by decide⟩
    let tVal := ZFSet.pair (vnNat o.1) (ZFSet.pair (vnNat o.2.1) (vnNat o.2.2))
    let pos' : ℤ := if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1
    have hstep_val := zfcStepFn_of_cfg M qCode pos g hq hg symCode hs hsym
    change zfcStepFn M z0 = ZFSet.pair (vnNat o.1)
      (ZFSet.pair (encodeInt pos') (zfcUpdateTape g (encodeInt pos) (vnNat o.2.1))) at hstep_val
    obtain ⟨_, happ⟩ := instrTableVal_funs_and_app M
    have htVal_eq : zfcApp (instrTableVal M)
        (ZFSet.pair (pi1Val z0) (zfcApp (pi2Val (pi2Val z0)) (pi1Val (pi2Val z0)))) = tVal := by
      dsimp [z0, tVal]
      rw [pi1Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, hsym]
      exact happ qCode symCode hq hs
    rw [stdEv_exs]
    refine (and_congr Iff.rfl (exists_congr fun t => (?_ : _ ↔
        (t = tVal ∧
         pi1Val z' = pi1Val t ∧
         ((pi2Val (pi2Val t) = vnNat 0 ∧
             stdEv ![pi1Val (pi2Val z'), pi1Val (pi2Val z0)] Constant14.integerPred.dfn) ∨
           (pi2Val (pi2Val t) = vnNat 1 ∧ pi1Val (pi2Val z') = pi1Val (pi2Val z0)) ∨
           (pi2Val (pi2Val t) = vnNat 2 ∧
             stdEv ![pi1Val (pi2Val z'), pi1Val (pi2Val z0)] Constant14.integerSucc.dfn)) ∧
         zfcApp (pi2Val (pi2Val z')) (pi1Val (pi2Val z0)) = pi1Val (pi2Val t) ∧
         ∀ k ∈ intSet, k ≠ pi1Val (pi2Val z0) →
           zfcApp (pi2Val (pi2Val z')) k = zfcApp (pi2Val (pi2Val z0)) k)))).trans ?_
    · rw [stdEv_and, stdEv_and, stdEv_and, stdEv_and]
      refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
      · rw [ev_faf_eq (et_bvar1 t _)
          (et_comp2 ev_value (et_const0 (dc_instructionTable M) _)
            (et_comp2 ev_kpair
              (et_comp1 ev_pi1 (et_bvar4 _ t z' z0 _))
              (et_comp2 ev_value
                (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar4 _ t z' z0 _)))
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar4 _ t z' z0 _)))))),
          htVal_eq]
      · exact ev_faf_eq
          (et_comp1 ev_pi1 (et_bvar2 t z' _))
          (et_comp1 ev_pi1 (et_bvar2 _ t _))
      · rw [stdEv_or, stdEv_or, stdEv_and, stdEv_and, stdEv_and]
        refine or_congr
          (and_congr
            (ev_faf_eq (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar1 t _)))
              (et_const0 (dc_numeral 0) _))
            (ev_nest2 Constant14.integerPred.dfn
              (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar2 t z' _)))
              (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar3 t z' z0 _)))))
          (or_congr
            (and_congr
              (ev_faf_eq (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar1 t _)))
                (et_const0 (dc_numeral 1) _))
              (ev_faf_eq
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar2 t z' _)))
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar4 _ t z' z0 _)))))
            (and_congr
              (ev_faf_eq (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar1 t _)))
                (et_const0 (dc_numeral 2) _))
              (ev_nest2 Constant14.integerSucc.dfn
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar2 t z' _)))
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar3 t z' z0 _))))))
      · exact ev_faf_eq
          (et_comp2 ev_value
            (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar2 t z' _)))
            (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar3 t z' z0 _))))
          (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar2 _ t _)))
      · rw [ev_faf_ball (et_const0 dc_integers _)]
        refine forall₂_congr fun k _ => ?_
        rw [stdEv_imp]
        exact imp_congr
          (ev_faf_ne (et_bvar1 k _)
            (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar6 _ k intSet t z' z0 _))))
          (ev_faf_eq
            (et_comp2 ev_value
              (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar4 k intSet t z' _)))
              (et_bvar1 k _))
            (et_comp2 ev_value
              (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar6 _ k intSet t z' z0 _)))
              (et_bvar2 _ k _)))
    · constructor
      · rintro ⟨hz', t, rfl, hq_eq, hdir, hwr, hrest⟩
        obtain ⟨q2, pos2, g2, _, hg2, rfl⟩ := mem_cfgSetVal_iff.mp hz'
        dsimp [z0, tVal] at hq_eq hdir hwr hrest
        rw [pi1Val_pair, pi1Val_pair] at hq_eq
        rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, pi1Val_pair] at hdir
        rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, pi1Val_pair] at hwr
        simp only [pi2Val_pair, pi1Val_pair] at hrest
        rw [hstep_val, hq_eq]
        congr 1; congr 1
        · have hd2 := hob.2.2
          interval_cases hdv : o.2.2
          · have h01 : vnNat 0 ≠ vnNat 1 := fun h => absurd (vnNat_injective h) (by decide)
            have h02 : vnNat 0 ≠ vnNat 2 := fun h => absurd (vnNat_injective h) (by decide)
            simp only [true_and, h01, h02, false_and, or_false] at hdir
            rw [ev_integerPred_encode] at hdir
            dsimp [pos']; rw [hdv]; simpa using hdir
          · have h10 : vnNat 1 ≠ vnNat 0 := fun h => absurd (vnNat_injective h) (by decide)
            have h12 : vnNat 1 ≠ vnNat 2 := fun h => absurd (vnNat_injective h) (by decide)
            simp only [true_and, h10, h12, false_and, false_or, or_false] at hdir
            dsimp [pos']; rw [hdv]; simpa using hdir
          · have h20 : vnNat 2 ≠ vnNat 0 := fun h => absurd (vnNat_injective h) (by decide)
            have h21 : vnNat 2 ≠ vnNat 1 := fun h => absurd (vnNat_injective h) (by decide)
            simp only [true_and, h20, h21, false_and, false_or] at hdir
            rw [ev_integerSucc_encode] at hdir
            dsimp [pos']; rw [hdv]; simpa using hdir
        · refine funs_ext hg2 (zfcUpdateTape_mem_funs hg (vnNat_lt_mem hob.2.1)) fun k hk => ?_
          rw [zfcUpdateTape_app hg (vnNat_lt_mem hob.2.1) hk]
          by_cases hkp : k = encodeInt pos
          · rw [if_pos hkp, hkp, hwr]
          · rw [if_neg hkp, hrest k hk hkp]
      · rintro rfl
        refine ⟨zfcStepFn_mem_cfg M hz, tVal, rfl, ?_, ?_, ?_, ?_⟩
        · rw [hstep_val]; dsimp [tVal]; rw [pi1Val_pair, pi1Val_pair]
        · rw [hstep_val]; dsimp [z0, tVal]
          rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, pi1Val_pair]
          have hd2 := hob.2.2
          interval_cases hdv : o.2.2
          · left; refine ⟨rfl, ?_⟩
            rw [ev_integerPred_encode]; dsimp [pos']; rw [hdv]; rfl
          · right; left; refine ⟨rfl, ?_⟩
            dsimp [pos']; rw [hdv]; rfl
          · right; right; refine ⟨rfl, ?_⟩
            rw [ev_integerSucc_encode]; dsimp [pos']; rw [hdv]; rfl
        · rw [hstep_val]; dsimp [z0, tVal]
          rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, pi1Val_pair]
          rw [zfcUpdateTape_app hg (vnNat_lt_mem hob.2.1) (encodeInt_mem pos), if_pos rfl]
        · intro k hk hne
          dsimp [z0] at hne
          rw [pi2Val_pair, pi1Val_pair] at hne
          rw [hstep_val]; dsimp [z0]
          rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi2Val_pair]
          rw [zfcUpdateTape_app hg (vnNat_lt_mem hob.2.1) hk, if_neg hne]
  · simp [hz]

private noncomputable def nextStepVal {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ZFSet.{0} :=
  letI : ZFSet.Definable₁ (zfcStepFn M) := Classical.allZFSetDefinable _
  ZFSet.map (zfcStepFn M) (cfgSetVal (n + 1))

private lemma nextStepVal_funs_and_app {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    nextStepVal M ∈ ZFSet.funs (cfgSetVal (n + 1)) (cfgSetVal (n + 1)) ∧
      ∀ z ∈ cfgSetVal (n + 1), zfcApp (nextStepVal M) z = zfcStepFn M z := by
  let _ : ZFSet.Definable₁ (zfcStepFn M) := Classical.allZFSetDefinable _
  have hfuns : nextStepVal M ∈ ZFSet.funs (cfgSetVal (n + 1)) (cfgSetVal (n + 1)) := by
    change ZFSet.map (zfcStepFn M) (cfgSetVal (n + 1)) ∈ _
    rw [ZFSet.mem_funs, ZFSet.map_isFunc]
    exact fun _ hz => zfcStepFn_mem_cfg M hz
  refine ⟨hfuns, fun z hz => ?_⟩
  have hmem : ZFSet.pair z (zfcStepFn M z) ∈ nextStepVal M := by
    change ZFSet.pair z (zfcStepFn M z) ∈ ZFSet.map (zfcStepFn M) (cfgSetVal (n + 1))
    exact ZFSet.mem_map.mpr ⟨z, hz, rfl⟩
  exact zfcApp_of_mem_funs hfuns hz hmem

private lemma dc_nextStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    DefinesConst (Constant14.nextStep (n + 1) (Constant14.instructionTable M)) (nextStepVal M) := by
  let _ : ZFSet.Definable₁ (zfcStepFn M) := Classical.allZFSetDefinable _
  intro p
  unfold Constant14.nextStep
  change stdEv ![p] (∀¹ _) ↔ _
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ e : ZFSet.{0}, e ∈ p ↔ e ∈ nextStepVal M).trans
    ⟨fun h => ZFSet.ext h, fun h e => by rw [h]⟩
  refine forall_congr' fun e => ?_
  rw [stdEv_iff]
  refine iff_congr (ev_faf_mem (et_bvar1 e _) (et_bvar3 _ e p _)) ?_
  rw [ev_faf_bexs (et_const0 (dc_configSet (n + 1)) _)]
  refine (?_ : _ ↔ ∃ z ∈ cfgSetVal (n + 1),
      ∃ z' ∈ cfgSetVal (n + 1), e = ZFSet.pair z z' ∧ z' = zfcStepFn M z).trans ?_
  · refine exists_congr fun z => and_congr_right fun hz => ?_
    rw [ev_faf_bexs (et_const0 (dc_configSet (n + 1)) _)]
    refine exists_congr fun z' => and_congr_right fun _ => ?_
    rw [stdEv_and]
    rw [ev_faf_eq (et_bvar5 z' _ z _ e _)
          (et_comp2 ev_kpair (et_bvar4 _ z' _ z _) (et_bvar2 _ z' _)),
        ev_nest2 (Constant14.nextConfig (n + 1) (Constant14.instructionTable M))
          (et_bvar1 z' _) (et_bvar3 z' _ z _),
        ev_nextConfig_iff M z' z]
    exact and_congr Iff.rfl ⟨And.right, fun h => ⟨hz, h⟩⟩
  · change _ ↔ e ∈ ZFSet.map (zfcStepFn M) (cfgSetVal (n + 1))
    rw [ZFSet.mem_map]
    constructor
    · rintro ⟨z, hz, z', _, rfl, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, zfcStepFn M z, zfcStepFn_mem_cfg M hz, rfl, rfl⟩

/- ## Section 5: Encoded Lean Configurations, `orbit`, and Final Contradiction -/

private noncomputable def encodeTape (T : Tape (Fin 2)) (pos : ℤ) : ZFSet.{0} :=
  let fn : ZFSet.{0} → ZFSet.{0} := fun w => vnNat (T.nth (decodePos w - pos)).val
  letI : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
  ZFSet.map fn intSet

private lemma encodeTape_funs_and_app (T : Tape (Fin 2)) (pos : ℤ) :
    encodeTape T pos ∈ ZFSet.funs intSet (vnNat 2) ∧
      ∀ m : ℤ, zfcApp (encodeTape T pos) (encodeInt m) = vnNat (T.nth (m - pos)).val := by
  let fn : ZFSet.{0} → ZFSet.{0} := fun w => vnNat (T.nth (decodePos w - pos)).val
  let _ : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
  have hfn_eq (m : ℤ) : fn (encodeInt m) = vnNat (T.nth (m - pos)).val := by
    dsimp [fn]
    rw [decodePos_encodeInt]
  have hfuns : encodeTape T pos ∈ ZFSet.funs intSet (vnNat 2) := by
    change ZFSet.map fn intSet ∈ ZFSet.funs intSet (vnNat 2)
    rw [ZFSet.mem_funs, ZFSet.map_isFunc]
    intro w hw
    obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
    rw [hfn_eq m]
    exact vnNat_lt_mem (T.nth (m - pos)).isLt
  refine ⟨hfuns, fun m => ?_⟩
  have hmem : ZFSet.pair (encodeInt m) (fn (encodeInt m)) ∈ encodeTape T pos := by
    change ZFSet.pair (encodeInt m) (fn (encodeInt m)) ∈ ZFSet.map fn intSet
    exact ZFSet.mem_map.mpr ⟨encodeInt m, encodeInt_mem m, rfl⟩
  rw [zfcApp_of_mem_funs hfuns (encodeInt_mem m) hmem, hfn_eq m]

private lemma blank_tape_nth (i : ℤ) : (Tape.mk₁ ([] : List (Fin 2))).nth i = 0 := by
  cases i with
  | ofNat k =>
    cases k <;> simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', Fin.default_eq_zero]
  | negSucc k =>
    simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', Fin.default_eq_zero]

private lemma dc_emptyTape :
    DefinesConst Constant14.emptyTape (encodeTape (Tape.mk₁ []) 0) := by
  intro f
  unfold Constant14.emptyTape
  rw [stdEv_and]
  rw [ev_faf_mem (et_bvar1 f _)
        (et_comp2 ev_function (et_const0 (dc_numeral 2) _) (et_const0 dc_integers _)),
      ev_faf_ball (et_const0 dc_integers _)]
  refine (and_congr Iff.rfl (forall₂_congr fun i _ =>
      (?_ : _ ↔ zfcApp f i = vnNat 0))).trans ?_
  · exact ev_faf_eq
      (et_comp2 ev_value (et_bvar3 i intSet f _) (et_bvar1 i _))
      (et_const0 (dc_numeral 0) _)
  · obtain ⟨he_funs, he_app⟩ := encodeTape_funs_and_app (Tape.mk₁ []) 0
    constructor
    · rintro ⟨hf, hall⟩
      refine funs_ext hf he_funs fun w hw => ?_
      obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
      rw [hall (encodeInt m) hw, he_app m, blank_tape_nth]
      rfl
    · rintro rfl
      refine ⟨he_funs, fun w hw => ?_⟩
      obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
      rw [he_app m, blank_tape_nth]
      rfl

private abbrev ExtCfg (n : ℕ) := Option (Fin n) × ℤ × Tape (Fin 2)

private def extInit (n : ℕ) [NeZero n] : ExtCfg n :=
  (some 0, 0, Tape.mk₁ [])

private def extStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : ExtCfg n → ExtCfg n
  | (none, pos, T) => (none, pos, T)
  | (some q, pos, T) =>
    match M q T.head with
    | none => (none, pos, T)
    | some (q', Stmt.write sym d) =>
      let pos' := match d with
        | Dir.left => pos - 1
        | Dir.right => pos + 1
      (q', pos', (T.write sym).move d)

private noncomputable def encodeExtCfg {n : ℕ} (c : ExtCfg n) : ZFSet.{0} :=
  ZFSet.pair (vnNat (Constant14.stateCode c.1))
    (ZFSet.pair (encodeInt c.2.1) (encodeTape c.2.2 c.2.1))

private lemma encodeExtCfg_mem {n : ℕ} (c : ExtCfg n) :
    encodeExtCfg c ∈ cfgSetVal (n + 1) := by
  refine mem_cfgSetVal_iff.mpr ⟨Constant14.stateCode c.1, c.2.1, encodeTape c.2.2 c.2.1, ?_,
    (encodeTape_funs_and_app c.2.2 c.2.1).1, rfl⟩
  cases c.1 with
  | none => exact Nat.lt_succ_self n
  | some q => exact Nat.lt_succ_of_lt q.isLt

private lemma dc_initialConfig (n : ℕ) [NeZero n] :
    DefinesConst Constant14.initialConfig (encodeExtCfg (extInit n)) := by
  intro z
  unfold Constant14.initialConfig
  rw [ev_faf_eq (et_bvar1 z _)
    (et_comp2 ev_kpair (et_const0 (dc_numeral 0) _)
      (et_comp2 ev_kpair (et_const0 dc_integerZero _) (et_const0 dc_emptyTape _)))]
  rfl

private lemma zfcStepFn_encodeExtCfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (c : ExtCfg n) :
    zfcStepFn M (encodeExtCfg c) = encodeExtCfg (extStep M c) := by
  rcases c with ⟨qOpt, pos, T⟩
  obtain ⟨hg, happ⟩ := encodeTape_funs_and_app T pos
  have hsym : zfcApp (encodeTape T pos) (encodeInt pos) = vnNat T.head.val := by
    have h := happ pos
    rw [sub_self] at h
    exact h
  cases qOpt with
  | none =>
    have hstep := zfcStepFn_of_cfg M n pos (encodeTape T pos) (Nat.lt_succ_self n) hg
      T.head.val T.head.isLt hsym
    dsimp only [encodeExtCfg, Constant14.stateCode] at hstep
    dsimp only [encodeExtCfg, extStep, Constant14.stateCode]
    rw [hstep]
    have hlu : transLookup M n T.head.val = (n, T.head.val, 1) := by
      unfold transLookup; rw [dif_neg (Nat.lt_irrefl n)]
    rw [hlu]
    have h10 : (1 : ℕ) ≠ 0 := by decide
    simp only [h10, ↓reduceIte]
    congr 1; congr 1
    refine funs_ext (zfcUpdateTape_mem_funs hg (vnNat_lt_mem T.head.isLt)) hg fun w hw => ?_
    obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
    rw [zfcUpdateTape_app hg (vnNat_lt_mem T.head.isLt) hw]
    by_cases hmp : m = pos
    · subst hmp
      rw [if_pos rfl, happ m, sub_self]; rfl
    · have hne : encodeInt m ≠ encodeInt pos := fun h => hmp (encodeInt_injective h)
      rw [if_neg hne]
  | some q =>
    have hstep := zfcStepFn_of_cfg M q.val pos (encodeTape T pos) (Nat.lt_succ_of_lt q.isLt) hg
      T.head.val T.head.isLt hsym
    dsimp only [encodeExtCfg, Constant14.stateCode] at hstep
    change zfcStepFn M (ZFSet.pair (vnNat q.val) (ZFSet.pair (encodeInt pos) (encodeTape T pos))) =
      encodeExtCfg (extStep M (some q, pos, T))
    rw [hstep]
    have hlu : transLookup M q.val T.head.val = Constant14.transitionCode M q T.head := by
      unfold transLookup
      rw [dif_pos q.isLt, dif_pos T.head.isLt]
    rw [hlu]
    cases hM : M q T.head with
    | none =>
      rw [Constant14.transitionCode, extStep, hM]
      dsimp only [encodeExtCfg, Constant14.directionCode, Constant14.stateCode]
      refine congrArg (ZFSet.pair _) (congrArg₂ ZFSet.pair rfl ?_)
      refine funs_ext (zfcUpdateTape_mem_funs hg (vnNat_lt_mem T.head.isLt)) hg fun w hw => ?_
      obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
      rw [zfcUpdateTape_app hg (vnNat_lt_mem T.head.isLt) hw]
      by_cases hmp : m = pos
      · subst hmp; rw [if_pos rfl, happ m, sub_self]; rfl
      · have hne : encodeInt m ≠ encodeInt pos := fun h => hmp (encodeInt_injective h)
        rw [if_neg hne]
    | some pairOut =>
      rcases pairOut with ⟨q', ⟨sym, d⟩⟩
      cases d with
      | left =>
        rw [Constant14.transitionCode, extStep, hM]
        dsimp only [encodeExtCfg, Constant14.directionCode]
        refine congrArg (ZFSet.pair _) (congrArg₂ ZFSet.pair rfl ?_)
        obtain ⟨hg', happ'⟩ := encodeTape_funs_and_app ((T.write sym).move Dir.left) (pos - 1)
        refine funs_ext (zfcUpdateTape_mem_funs hg (vnNat_lt_mem sym.isLt)) hg' fun w hw => ?_
        obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
        rw [zfcUpdateTape_app hg (vnNat_lt_mem sym.isLt) hw, happ' m, Tape.move_left_nth]
        have hidx : m - (pos - 1) - 1 = m - pos := by omega
        rw [hidx, Tape.write_nth]
        by_cases hmp : m = pos
        · subst hmp; rw [if_pos rfl, sub_self, if_pos rfl]
        · have hne1 : encodeInt m ≠ encodeInt pos := fun h => hmp (encodeInt_injective h)
          have hne2 : m - pos ≠ 0 := by omega
          rw [if_neg hne1, if_neg hne2, happ m]
      | right =>
        rw [Constant14.transitionCode, extStep, hM]
        dsimp only [encodeExtCfg, Constant14.directionCode]
        refine congrArg (ZFSet.pair _) (congrArg₂ ZFSet.pair rfl ?_)
        obtain ⟨hg', happ'⟩ := encodeTape_funs_and_app ((T.write sym).move Dir.right) (pos + 1)
        refine funs_ext (zfcUpdateTape_mem_funs hg (vnNat_lt_mem sym.isLt)) hg' fun w hw => ?_
        obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
        rw [zfcUpdateTape_app hg (vnNat_lt_mem sym.isLt) hw, happ' m, Tape.move_right_nth]
        have hidx : m - (pos + 1) + 1 = m - pos := by omega
        rw [hidx, Tape.write_nth]
        by_cases hmp : m = pos
        · subst hmp; rw [if_pos rfl, sub_self, if_pos rfl]
        · have hne1 : encodeInt m ≠ encodeInt pos := fun h => hmp (encodeInt_injective h)
          have hne2 : m - pos ≠ 0 := by omega
          rw [if_neg hne1, if_neg hne2, happ m]

private lemma iterate_nextStepVal_eq {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    (zfcApp (nextStepVal M))^[k] (encodeExtCfg (extInit n)) =
      encodeExtCfg ((extStep M)^[k] (extInit n)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    obtain ⟨_, happ⟩ := nextStepVal_funs_and_app M
    rw [happ _ (encodeExtCfg_mem _), zfcStepFn_encodeExtCfg]

private lemma ev_orbit_range {f x0 : ZFSet.{0}}
    (hfunc : ∃ X Y : ZFSet.{0}, f ∈ ZFSet.funs X Y) :
    stdEv ![ZFSet.range (fun k : ℕ => (zfcApp f)^[k] x0), f, x0] Constant14.orbit := by
  let O := ZFSet.range (fun k : ℕ => (zfcApp f)^[k] x0)
  unfold Constant14.orbit
  rw [stdEv_and]
  refine ⟨?_, ?_⟩
  · rw [ev_nest1 SetTheory.IsFunction.dfn (et_bvar2 O f _), ev_IsFunction]
    exact hfunc
  · rw [stdEv_all]
    intro z
    rw [stdEv_iff]
    rw [ev_faf_mem (et_bvar1 z _) (et_bvar3 _ z O _)]
    rw [stdEv_all]
    have hO_iff : z ∈ O ↔ ∀ A : ZFSet.{0}, (x0 ∈ A ∧ ∀ y ∈ A, zfcApp f y ∈ A) → z ∈ A := by
      constructor
      · intro hzO A ⟨hx0, hclosed⟩
        obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hzO
        clear hzO
        induction k with
        | zero => exact hx0
        | succ k ih =>
          rw [Function.iterate_succ_apply']
          exact hclosed _ ih
      · intro hall
        refine hall O ⟨ZFSet.mem_range.mpr ⟨0, rfl⟩, ?_⟩
        intro y hy
        obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hy
        exact ZFSet.mem_range.mpr ⟨k + 1, Function.iterate_succ_apply' _ k x0⟩
    rw [hO_iff]
    symm
    refine forall_congr' fun A => ?_
    rw [stdEv_imp, stdEv_and]
    refine imp_congr (and_congr ?_ ?_)
      (ev_faf_mem (et_bvar2 A z _) (et_bvar2 _ A _))
    · exact ev_faf_mem (et_bvar5 A z O f x0 _) (et_bvar2 _ A _)
    · rw [ev_faf_ball (et_bvar1 A _)]
      refine forall₂_congr fun y _ => ?_
      exact ev_faf_mem
        (et_comp2 ev_value (et_bvar6 y A A z O f _) (et_bvar1 y _))
        (et_bvar4 _ y A A _)

private lemma multiStep_agrees_with_extStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∀ (k : ℕ) (qk : Fin n) (Tk : Tape (Fin 2)),
      M.multiStep (Machine.init []) k = some ⟨some qk, Tk⟩ →
        ((extStep M)^[k] (extInit n)).1 = some qk ∧
          ((extStep M)^[k] (extInit n)).2.2 = Tk := by
  intro k
  induction k with
  | zero =>
    intro qk Tk h0
    simp only [Machine.multiStep_zero, Machine.init, Fin.default_eq_zero, Option.some.injEq,
      Cfg.mk.injEq] at h0
    rcases h0 with ⟨hq, hT⟩
    subst hq hT
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro qk1 Tk1 hsucc
    rw [Machine.multiStep_succ] at hsucc
    cases hmk : M.multiStep (Machine.init []) k with
    | none =>
      rw [hmk] at hsucc; simp at hsucc
    | some cfg =>
      rw [hmk, Option.bind_some] at hsucc
      rcases cfg with ⟨qOpt, Tk⟩
      cases qOpt with
      | none =>
        simp [Machine.step] at hsucc
      | some qk =>
        obtain ⟨hq_ih, hT_ih⟩ := ih qk Tk hmk
        simp only [Machine.step] at hsucc
        cases hMq : M qk Tk.head with
        | none =>
          rw [hMq] at hsucc; simp at hsucc
        | some out =>
          rw [hMq, Option.map_some, Option.some.injEq] at hsucc
          rcases out with ⟨qNext, ⟨sym, d⟩⟩
          injection hsucc with hqN hTN
          subst hqN hTN
          rw [Function.iterate_succ_apply']
          rcases hext : (extStep M)^[k] (extInit n) with ⟨c1, posk, cT⟩
          rw [hext] at hq_ih hT_ih
          dsimp only at hq_ih hT_ih
          subst hq_ih hT_ih
          simp [extStep, hMq]

private lemma not_stdEv_halts {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (hM : ¬ M.IsHalting) :
    ¬ stdEv (Fin.elim0 : Fin 0 → ZFSet.{0}) (Constant14.halts M) := by
  intro hhalts
  rw [stdEv_e0 (Fin.elim0 : Fin 0 → ZFSet.{0}) ![]] at hhalts
  unfold Constant14.halts at hhalts
  rw [ev_faf_bexs (et_const0 dc_integers ![])] at hhalts
  obtain ⟨m, _, hm_body⟩ := hhalts
  rw [ev_faf_bexs
    (et_comp2 ev_function (et_const0 (dc_numeral 2) _) (et_const0 dc_integers _))] at hm_body
  obtain ⟨g, _, hg_body⟩ := hm_body
  let target := ZFSet.pair (vnNat n) (ZFSet.pair m g)
  let Fstep := nextStepVal M
  let x0 := encodeExtCfg (extInit n)
  let O := ZFSet.range (fun k : ℕ => (zfcApp Fstep)^[k] x0)
  have htarget : EvalTermAt (g :> ZFSet.funs intSet (vnNat 2) :> m :> intSet :> ![])
      (Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
        (Semiformula.nestFormulaeFunc (Constant14.numeral n) ![] :>
          Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
            (op(=).operator (#0 :> #3 :> ![]) :> op(=).operator (#0 :> #1 :> ![]) :> ![]) :> ![]))
      target :=
    et_comp2 ev_kpair (et_const0 (dc_numeral n) _)
      (et_comp2 ev_kpair (et_bvar3 g _ m _) (et_bvar1 g _))
  unfold stdEv at hg_body
  rw [ev_all'] at hg_body
  have hv1 := (ev_imp' _ _ _ _).mp (hg_body target) ((htarget target).mpr rfl)
  rw [ev_all'] at hv1
  have horbit_nest : stdEv (O :> target :> g :> ZFSet.funs intSet (vnNat 2) :> m :> intSet :> ![])
      (Semiformula.nestFormulaeFunc Constant14.orbit
        (Semiformula.nestFormulaeFunc (Constant14.nextStep (n + 1) (Constant14.instructionTable M)) ![] :>
          Semiformula.nestFormulaeFunc Constant14.initialConfig ![] :> ![])) := by
    rw [ev_nestFunc2_raw Constant14.orbit
      (et_const0 (dc_nextStep M) _) (et_const0 (dc_initialConfig n) _) O]
    exact ev_orbit_range ⟨cfgSetVal (n + 1), cfgSetVal (n + 1), (nextStepVal_funs_and_app M).1⟩
  have hmem_O := (ev_imp' _ _ _ _).mp (hv1 O) horbit_nest
  rw [ev_mem'] at hmem_O
  have htarget_in_O : target ∈ O := by simpa [tval_bvar] using hmem_O
  obtain ⟨k, hk⟩ := ZFSet.mem_range.mp htarget_in_O
  rw [iterate_nextStepVal_eq M k] at hk
  dsimp [encodeExtCfg, target] at hk
  obtain ⟨hq_eq, _⟩ := ZFSet.pair_injective hk
  have hcode_eq : Constant14.stateCode ((extStep M)^[k] (extInit n)).1 = n :=
    vnNat_injective hq_eq
  have hnot_after : ¬ M.HaltsAfter (Machine.init []) k :=
    fun ha => hM ((Machine.isHalting_iff_exists_haltsAt M).mpr ⟨k, ha⟩)
  obtain ⟨qk, Tk, hms⟩ := Machine.exists_of_not_haltsAfter M (Machine.init []) k hnot_after
  obtain ⟨hstate, _⟩ := multiStep_agrees_with_extStep M k qk Tk hms
  rw [hstate] at hcode_eq
  dsimp [Constant14.stateCode] at hcode_eq
  exact absurd hcode_eq (Nat.ne_of_lt qk.isLt)

theorem h3_main : OMA.R_Constant14_c14_ge_4_R1.H3 := by
  intro tr hverum hfalsum heq hmem hnrel hand hor hall hexs n hn M hM htr
  have hiff := tr_iff_stdEv tr hverum hfalsum heq hmem hnrel hand hor hall hexs
    (Constant14.halts M) (Fin.elim0 : Fin 0 → ZFSet.{0})
  exact not_stdEv_halts M hM (hiff.mp htr)

end C14H3Proof

theorem OMA.solution : OMA.R_Constant14_c14_ge_4_R1.H3 :=
  C14H3Proof.h3_main
