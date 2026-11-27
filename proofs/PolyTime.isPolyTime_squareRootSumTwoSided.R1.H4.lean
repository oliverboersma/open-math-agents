import OMAReductions.R_PolyTime_isPolyTime_squareRootSumTwoSided_R1
import Mathlib.Tactic

/-!
# Proof of PolyTime.isPolyTime_squareRootSumTwoSided.R1.H4

Polynomial-time list and binary natural operations via FinTM2 combinators.
-/

namespace PolyTimeSqrtH4Proof

open Computability Turing StateTransition BitstringEncoding ComplexityTheory BigOperators

local instance instKFin (M : FinTM2) : Fintype M.K := M.kFin
local instance instΛFin (M : FinTM2) : Fintype M.Λ := M.ΛFin
local instance instσFin (M : FinTM2) : Fintype M.σ := M.σFin
local instance instΓk₀Fin (M : FinTM2) : Fintype (M.Γ M.k₀) := M.Γk₀Fin

private lemma iterate_bind_none {σ : Type*} (step : σ → Option σ) (t : ℕ) :
    (flip bind step)^[t] none = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    exact ih

private lemma flip_bind_some {σ : Type*} (step : σ → Option σ) (x : σ) :
    flip bind step (some x) = step x := rfl

private def stmtPushes {K : Type*} {Γ : K → Type*} {Λ σ : Type*} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + stmtPushes q
  | .peek _ _ q => stmtPushes q
  | .pop _ _ q => stmtPushes q
  | .load _ q => stmtPushes q
  | .branch _ q₁ q₂ => max (stmtPushes q₁) (stmtPushes q₂)
  | .goto _ => 0
  | .halt => 0

private lemma stepAux_stk_length_le {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + stmtPushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, stmtPushes]
    have h1 := ih v (Function.update S k' (f v :: S k'))
    by_cases hk : k = k'
    · subst hk
      simp only [Function.update_self, List.length_cons] at h1
      omega
    · simp only [Function.update_of_ne hk] at h1
      omega
  | peek k' f q ih =>
    simp only [TM2.stepAux, stmtPushes]
    exact ih _ S
  | pop k' f q ih =>
    simp only [TM2.stepAux, stmtPushes]
    have h1 := ih (f v (S k').head?) (Function.update S k' (S k').tail)
    by_cases hk : k = k'
    · subst hk
      simp only [Function.update_self] at h1
      have htail : (S k).tail.length ≤ (S k).length := by cases S k <;> simp
      omega
    · simp only [Function.update_of_ne hk] at h1
      exact h1
  | load a q ih =>
    simp only [TM2.stepAux, stmtPushes]
    exact ih _ S
  | branch p q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, stmtPushes]
    cases p v
    · simp only [Bool.cond_false]
      have h2 := ih₂ v S
      omega
    · simp only [Bool.cond_true]
      have h1 := ih₁ v S
      omega
  | goto _ =>
    simp [stmtPushes]
  | halt =>
    simp [stmtPushes]

private def maxPushes (tm : FinTM2) : ℕ :=
  Finset.univ.sup fun l : tm.Λ => stmtPushes (tm.m l)

private lemma evals_stk_length_le (tm : FinTM2) (s : ℕ) (c c' : tm.Cfg)
    (heval : (flip bind tm.step)^[s] (some c) = some c') (k : tm.K) :
    (c'.stk k).length ≤ (c.stk k).length + s * maxPushes tm := by
  induction s generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq, zero_mul, add_zero] at heval ⊢
    rw [heval]
  | succ s ih =>
    rw [Function.iterate_succ_apply, flip_bind_some] at heval
    rcases c with ⟨l_opt, v, S⟩
    rcases l_opt with _ | l
    · change (flip bind tm.step)^[s] none = some c' at heval
      rw [iterate_bind_none] at heval
      cases heval
    · change (flip bind tm.step)^[s] (some (TM2.stepAux (tm.m l) v S)) = some c' at heval
      have hrec := ih (TM2.stepAux (tm.m l) v S) heval
      have hstep := stepAux_stk_length_le (tm.m l) v S k
      have hle : stmtPushes (tm.m l) ≤ maxPushes tm :=
        Finset.le_sup (f := fun l : tm.Λ => stmtPushes (tm.m l)) (Finset.mem_univ l)
      dsimp only
      rw [Nat.succ_mul]
      omega

private lemma initList_stk_length_le (tm : FinTM2) (L : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm L).stk k).length ≤ L.length := by
  by_cases hk : k = tm.k₀
  · subst hk
    simp [initList]
  · simp [initList, hk]

private lemma haltList_stk_k1 (tm : FinTM2) (L : List (tm.Γ tm.k₁)) :
    (haltList tm L).stk tm.k₁ = L := by
  simp [haltList]

private lemma poly_eval_mono (P : Polynomial ℕ) {a b : ℕ} (hab : a ≤ b) :
    P.eval a ≤ P.eval b := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

private def delimitRevAux : List Bool → List Bool → List Bool
  | [], acc => acc
  | b :: rest, acc => delimitRevAux rest (true :: b :: acc)

private lemma delimitRevAux_append (xs ys acc : List Bool) :
    delimitRevAux (xs ++ ys) acc = delimitRevAux ys (delimitRevAux xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons b xs ih => exact ih (true :: b :: acc)

private lemma delimitRevAux_reverse (L acc : List Bool) :
    delimitRevAux L.reverse (false :: acc) = delimit L ++ acc := by
  induction L with
  | nil => rfl
  | cons b l ih =>
    simp only [List.reverse_cons, delimitRevAux_append, ih, delimitRevAux, delimit,
      List.cons_append]

/- ### 1. Composition `x ↦ g (f x)` -/

private structure CompData where
  tmF : FinTM2
  tmG : FinTM2
  outF : tmF.Γ tmF.k₁ ≃ Bool
  inG : tmG.Γ tmG.k₀ ≃ Bool

private abbrev CompData.CK (C : CompData) : Type := Unit ⊕ C.tmF.K ⊕ C.tmG.K
private abbrev CompData.CΛ (C : CompData) : Type := Fin 2 ⊕ C.tmF.Λ ⊕ C.tmG.Λ
private abbrev CompData.Cσ (C : CompData) : Type := Option Bool × C.tmF.σ × C.tmG.σ

private abbrev CompData.cΓ (C : CompData) : C.CK → Type
  | Sum.inl _ => Bool
  | Sum.inr (Sum.inl kf) => C.tmF.Γ kf
  | Sum.inr (Sum.inr kg) => C.tmG.Γ kg

private def CompData.liftF (C : CompData) (next : C.CΛ) :
    TM2.Stmt C.tmF.Γ C.tmF.Λ C.tmF.σ → TM2.Stmt C.cΓ C.CΛ C.Cσ
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun v => f v.2.1) (C.liftF next q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (C.liftF next q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (C.liftF next q)
  | .load a q => .load (fun v => (v.1, a v.2.1, v.2.2)) (C.liftF next q)
  | .branch p q₁ q₂ => .branch (fun v => p v.2.1) (C.liftF next q₁) (C.liftF next q₂)
  | .goto l => .goto (fun v => Sum.inr (Sum.inl (l v.2.1)))
  | .halt => .goto (fun _ => next)

private def CompData.liftG (C : CompData) :
    TM2.Stmt C.tmG.Γ C.tmG.Λ C.tmG.σ → TM2.Stmt C.cΓ C.CΛ C.Cσ
  | .push k f q => .push (Sum.inr (Sum.inr k)) (fun v => f v.2.2) (C.liftG q)
  | .peek k f q => .peek (Sum.inr (Sum.inr k)) (fun v o => (v.1, v.2.1, f v.2.2 o)) (C.liftG q)
  | .pop k f q => .pop (Sum.inr (Sum.inr k)) (fun v o => (v.1, v.2.1, f v.2.2 o)) (C.liftG q)
  | .load a q => .load (fun v => (v.1, v.2.1, a v.2.2)) (C.liftG q)
  | .branch p q₁ q₂ => .branch (fun v => p v.2.2) (C.liftG q₁) (C.liftG q₂)
  | .goto l => .goto (fun v => Sum.inr (Sum.inr (l v.2.2)))
  | .halt => .halt

private def CompData.cStmt (C : CompData) : C.CΛ → TM2.Stmt C.cΓ C.CΛ C.Cσ
  | Sum.inl 0 =>
    .pop (Sum.inr (Sum.inl C.tmF.k₁)) (fun v o => (o.map C.outF.toFun, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl ()) (fun v => v.1.getD false)
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 0))))
        (.goto (fun _ => Sum.inl 1)))
  | Sum.inl 1 =>
    .pop (Sum.inl ()) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inr (Sum.inr C.tmG.k₀)) (fun v => C.inG.invFun (v.1.getD false))
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 1))))
        (.goto (fun _ => Sum.inr (Sum.inr C.tmG.main))))
  | Sum.inr (Sum.inl lf) => C.liftF (Sum.inl 0) (C.tmF.m lf)
  | Sum.inr (Sum.inr lg) => C.liftG (C.tmG.m lg)

private abbrev CompData.cTM (C : CompData) : FinTM2 where
  K := C.CK
  k₀ := Sum.inr (Sum.inl C.tmF.k₀)
  k₁ := Sum.inr (Sum.inr C.tmG.k₁)
  Γ := C.cΓ
  Λ := C.CΛ
  main := Sum.inr (Sum.inl C.tmF.main)
  σ := C.Cσ
  initialState := (none, C.tmF.initialState, C.tmG.initialState)
  Γk₀Fin := C.tmF.Γk₀Fin
  m := C.cStmt

private abbrev CompData.mkCfg (C : CompData) (l : Option C.CΛ) (v : C.Cσ)
    (S : ∀ k : C.CK, List (C.cΓ k)) : C.cTM.Cfg :=
  ⟨l, v, S⟩

private abbrev CompData.initVar (C : CompData) : C.Cσ :=
  (none, C.tmF.initialState, C.tmG.initialState)

@[simp]
private def CompData.mergeF (C : CompData)
    (Sf : ∀ kf, List (C.tmF.Γ kf)) : ∀ k : C.CK, List (C.cΓ k)
  | Sum.inr (Sum.inl kf) => Sf kf
  | _ => []

private def CompData.embedF (C : CompData) (next : C.CΛ) (v1 : Option Bool) (v3 : C.tmG.σ)
    (c : C.tmF.Cfg) : C.cTM.Cfg :=
  C.mkCfg
    (match c.l with
      | some lf => some (Sum.inr (Sum.inl lf))
      | none => some next)
    (v1, c.var, v3)
    (C.mergeF c.stk)

private lemma comp_stepAux_liftF (C : CompData) (next : C.CΛ) (v1 : Option Bool) (v3 : C.tmG.σ)
    (q : TM2.Stmt C.tmF.Γ C.tmF.Λ C.tmF.σ) (vf : C.tmF.σ) (Sf : ∀ kf, List (C.tmF.Γ kf)) :
    TM2.stepAux (C.liftF next q) (v1, vf, v3) (C.mergeF Sf) =
      C.embedF next v1 v3 (TM2.stepAux q vf Sf) := by
  induction q generalizing vf Sf with
  | push kf f q ih =>
    simp only [CompData.liftF, TM2.stepAux]
    have hupd : Function.update (C.mergeF Sf) (Sum.inr (Sum.inl kf))
        (f vf :: C.mergeF Sf (Sum.inr (Sum.inl kf))) =
        C.mergeF (Function.update Sf kf (f vf :: Sf kf)) := by
      funext k; rcases k with (_ | k' | _)
      · simp
      · by_cases hk : k' = kf
        · subst hk; simp
        · simp [hk]
      · simp
    rw [hupd]; exact ih vf _
  | peek _ _ _ ih => simp only [CompData.liftF, TM2.stepAux, CompData.mergeF]; exact ih _ Sf
  | pop kf f q ih =>
    simp only [CompData.liftF, TM2.stepAux]
    have hupd : Function.update (C.mergeF Sf) (Sum.inr (Sum.inl kf))
        (C.mergeF Sf (Sum.inr (Sum.inl kf))).tail =
        C.mergeF (Function.update Sf kf (Sf kf).tail) := by
      funext k; rcases k with (_ | k' | _)
      · simp
      · by_cases hk : k' = kf
        · subst hk; simp
        · simp [hk]
      · simp
    rw [hupd]; exact ih _ _
  | load _ _ ih => simp only [CompData.liftF, TM2.stepAux]; exact ih _ Sf
  | branch p _ _ ih₁ ih₂ =>
    simp only [CompData.liftF, TM2.stepAux]
    cases p vf
    · simp only [Bool.cond_false]; exact ih₂ vf Sf
    · simp only [Bool.cond_true]; exact ih₁ vf Sf
  | goto _ => rfl
  | halt => rfl

private lemma comp_sim_tmF (C : CompData) (v1 : Option Bool) (v3 : C.tmG.σ)
    (s : ℕ) (c c' : C.tmF.Cfg)
    (heval : (flip bind C.tmF.step)^[s] (some c) = some c') :
    (flip bind C.cTM.step)^[s] (some (C.embedF (Sum.inl 0) v1 v3 c)) =
      some (C.embedF (Sum.inl 0) v1 v3 c') := by
  induction s generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at heval ⊢
    rw [heval]
  | succ s ih =>
    rw [Function.iterate_succ_apply, flip_bind_some] at heval ⊢
    rcases c with ⟨_ | lf, vf, Sf⟩
    · change (flip bind C.tmF.step)^[s] none = some c' at heval
      rw [iterate_bind_none] at heval; cases heval
    · change (flip bind C.tmF.step)^[s] (some (TM2.stepAux (C.tmF.m lf) vf Sf)) = some c' at heval
      have hstep : C.cTM.step (C.embedF (Sum.inl 0) v1 v3 ⟨some lf, vf, Sf⟩) =
          some (C.embedF (Sum.inl 0) v1 v3 (TM2.stepAux (C.tmF.m lf) vf Sf)) :=
        congrArg some (comp_stepAux_liftF C (Sum.inl 0) v1 v3 (C.tmF.m lf) vf Sf)
      rw [hstep]; exact ih _ heval

@[simp]
private def CompData.mergeG (C : CompData)
    (Sg : ∀ kg, List (C.tmG.Γ kg)) : ∀ k : C.CK, List (C.cΓ k)
  | Sum.inr (Sum.inr kg) => Sg kg
  | _ => []

private def CompData.embedG (C : CompData) (v1 : Option Bool) (v2 : C.tmF.σ)
    (c : C.tmG.Cfg) : C.cTM.Cfg :=
  C.mkCfg (c.l.map fun lg => Sum.inr (Sum.inr lg)) (v1, v2, c.var) (C.mergeG c.stk)

private lemma comp_stepAux_liftG (C : CompData) (v1 : Option Bool) (v2 : C.tmF.σ)
    (q : TM2.Stmt C.tmG.Γ C.tmG.Λ C.tmG.σ) (vg : C.tmG.σ) (Sg : ∀ kg, List (C.tmG.Γ kg)) :
    TM2.stepAux (C.liftG q) (v1, v2, vg) (C.mergeG Sg) =
      C.embedG v1 v2 (TM2.stepAux q vg Sg) := by
  induction q generalizing vg Sg with
  | push kg f q ih =>
    simp only [CompData.liftG, TM2.stepAux]
    have hupd : Function.update (C.mergeG Sg) (Sum.inr (Sum.inr kg))
        (f vg :: C.mergeG Sg (Sum.inr (Sum.inr kg))) =
        C.mergeG (Function.update Sg kg (f vg :: Sg kg)) := by
      funext k; rcases k with (_ | _ | k')
      · simp
      · simp
      · by_cases hk : k' = kg
        · subst hk; simp
        · simp [hk]
    rw [hupd]; exact ih vg _
  | peek _ _ _ ih => simp only [CompData.liftG, TM2.stepAux, CompData.mergeG]; exact ih _ Sg
  | pop kg f q ih =>
    simp only [CompData.liftG, TM2.stepAux]
    have hupd : Function.update (C.mergeG Sg) (Sum.inr (Sum.inr kg))
        (C.mergeG Sg (Sum.inr (Sum.inr kg))).tail =
        C.mergeG (Function.update Sg kg (Sg kg).tail) := by
      funext k; rcases k with (_ | _ | k')
      · simp
      · simp
      · by_cases hk : k' = kg
        · subst hk; simp
        · simp [hk]
    rw [hupd]; exact ih _ _
  | load _ _ ih => simp only [CompData.liftG, TM2.stepAux]; exact ih _ Sg
  | branch p _ _ ih₁ ih₂ =>
    simp only [CompData.liftG, TM2.stepAux]
    cases p vg
    · simp only [Bool.cond_false]; exact ih₂ vg Sg
    · simp only [Bool.cond_true]; exact ih₁ vg Sg
  | goto _ => rfl
  | halt => rfl

private lemma comp_sim_tmG (C : CompData) (v1 : Option Bool) (v2 : C.tmF.σ)
    (s : ℕ) (c c' : C.tmG.Cfg)
    (heval : (flip bind C.tmG.step)^[s] (some c) = some c') :
    (flip bind C.cTM.step)^[s] (some (C.embedG v1 v2 c)) =
      some (C.embedG v1 v2 c') := by
  induction s generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at heval ⊢
    rw [heval]
  | succ s ih =>
    rw [Function.iterate_succ_apply, flip_bind_some] at heval ⊢
    rcases c with ⟨_ | lg, vg, Sg⟩
    · change (flip bind C.tmG.step)^[s] none = some c' at heval
      rw [iterate_bind_none] at heval; cases heval
    · change (flip bind C.tmG.step)^[s] (some (TM2.stepAux (C.tmG.m lg) vg Sg)) = some c' at heval
      have hstep : C.cTM.step (C.embedG v1 v2 ⟨some lg, vg, Sg⟩) =
          some (C.embedG v1 v2 (TM2.stepAux (C.tmG.m lg) vg Sg)) :=
        congrArg some (comp_stepAux_liftG C v1 v2 (C.tmG.m lg) vg Sg)
      rw [hstep]; exact ih _ heval

private lemma comp_phase0 (C : CompData) (ws : List Bool)
    (S : ∀ k : C.CK, List (C.cΓ k))
    (hw : S (Sum.inr (Sum.inl C.tmF.k₁)) = ws.map C.outF.invFun) :
    ∃ S₁ : ∀ k : C.CK, List (C.cΓ k),
      (flip bind C.cTM.step)^[ws.length + 1] (some (C.mkCfg (some (Sum.inl 0)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inl 1)) C.initVar S₁) ∧
      S₁ (Sum.inr (Sum.inl C.tmF.k₁)) = [] ∧
      S₁ (Sum.inl ()) = ws.reverse ++ S (Sum.inl ()) ∧
      ∀ k, k ≠ Sum.inr (Sum.inl C.tmF.k₁) → k ≠ Sum.inl () → S₁ k = S k := by
  induction ws generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inr (Sum.inl C.tmF.k₁)) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.cStmt ⟨some (Sum.inl 0), C.initVar, S⟩ =
        some ⟨some (Sum.inl 1), C.initVar, Function.update S (Sum.inr (Sum.inl C.tmF.k₁)) []⟩
      simp [CompData.cStmt, hw]
    · intro k hkf1 _
      exact Function.update_of_ne hkf1 _ _
  | cons b ws ih =>
    let S' : ∀ k : C.CK, List (C.cΓ k) := Function.update
      (Function.update S (Sum.inr (Sum.inl C.tmF.k₁)) (ws.map C.outF.invFun))
      (Sum.inl ()) (b :: S (Sum.inl ()))
    have hstep : C.cTM.step (C.mkCfg (some (Sum.inl 0)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 0)) C.initVar S') := by
      change TM2.step C.cStmt ⟨some (Sum.inl 0), C.initVar, S⟩ =
        some ⟨some (Sum.inl 0), C.initVar, S'⟩
      simp [CompData.cStmt, hw, S']
    have hS'kf1 : S' (Sum.inr (Sum.inl C.tmF.k₁)) = ws.map C.outF.invFun := by simp [S']
    have hS'0 : S' (Sum.inl ()) = b :: S (Sum.inl ()) := by simp [S']
    obtain ⟨S₁, heval, h1kf1, h10, h1other⟩ := ih S' hS'kf1
    refine ⟨S₁, ?_, h1kf1, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h10, hS'0, List.reverse_cons, List.append_assoc, List.singleton_append]
    · intro k hkf1 hk0
      rw [h1other k hkf1 hk0]
      simp [S', Function.update_of_ne hk0, Function.update_of_ne hkf1]

private lemma comp_phase1 (C : CompData) (zs : List Bool)
    (S : ∀ k : C.CK, List (C.cΓ k))
    (hz : S (Sum.inl ()) = zs) :
    ∃ S₂ : ∀ k : C.CK, List (C.cΓ k),
      (flip bind C.cTM.step)^[zs.length + 1] (some (C.mkCfg (some (Sum.inl 1)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inr (Sum.inr C.tmG.main))) C.initVar S₂) ∧
      S₂ (Sum.inl ()) = [] ∧
      S₂ (Sum.inr (Sum.inr C.tmG.k₀)) =
        zs.reverse.map C.inG.invFun ++ S (Sum.inr (Sum.inr C.tmG.k₀)) ∧
      ∀ k, k ≠ Sum.inl () → k ≠ Sum.inr (Sum.inr C.tmG.k₀) → S₂ k = S k := by
  induction zs generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl ()) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.cStmt ⟨some (Sum.inl 1), C.initVar, S⟩ =
        some ⟨some (Sum.inr (Sum.inr C.tmG.main)), C.initVar, Function.update S (Sum.inl ()) []⟩
      simp [CompData.cStmt, hz]
    · intro k hk0 _
      exact Function.update_of_ne hk0 _ _
  | cons b zs ih =>
    let S' : ∀ k : C.CK, List (C.cΓ k) := Function.update
      (Function.update S (Sum.inl ()) zs)
      (Sum.inr (Sum.inr C.tmG.k₀))
      (C.inG.invFun b :: S (Sum.inr (Sum.inr C.tmG.k₀)))
    have hstep : C.cTM.step (C.mkCfg (some (Sum.inl 1)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 1)) C.initVar S') := by
      change TM2.step C.cStmt ⟨some (Sum.inl 1), C.initVar, S⟩ =
        some ⟨some (Sum.inl 1), C.initVar, S'⟩
      simp [CompData.cStmt, hz, S']
    have hS'0 : S' (Sum.inl ()) = zs := by simp [S']
    have hS'kg0 : S' (Sum.inr (Sum.inr C.tmG.k₀)) =
        C.inG.invFun b :: S (Sum.inr (Sum.inr C.tmG.k₀)) := by simp [S']
    obtain ⟨S₂, heval, h20, h2kg0, h2other⟩ := ih S' hS'0
    refine ⟨S₂, ?_, h20, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h2kg0, hS'kg0, List.reverse_cons, List.map_append, List.append_assoc, List.map_singleton,
        List.singleton_append]
    · intro k hk0 hkg0
      rw [h2other k hk0 hkg0]
      simp [S', Function.update_of_ne hkg0, Function.update_of_ne hk0]

theorem isPolyTime_comp {α β γ : Type}
    [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    {f : α → β} {g : β → γ}
    (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => g (f x)) := by
  rcases hf with ⟨Mf⟩
  rcases hg with ⟨Mg⟩
  let C : CompData := {
    tmF := Mf.tm
    tmG := Mg.tm
    outF := Mf.outputAlphabet
    inG := Mg.inputAlphabet
  }
  let Bf : ℕ := maxPushes C.tmF
  let polyY : Polynomial ℕ := Polynomial.X + Mf.time * Polynomial.C Bf
  let totalTime : Polynomial ℕ :=
    Mf.time + Polynomial.C 2 * polyY + Polynomial.C 2 + Mg.time.comp polyY
  have hout : ∀ x : α, Nonempty (TM2OutputsInTime C.cTM
      (List.map Mf.inputAlphabet.invFun ((BitstringEncoding.toEncoding (α := α)).encode x))
      (some (List.map Mg.outputAlphabet.invFun
        ((BitstringEncoding.toEncoding (α := γ)).encode (g (f x)))))
      (totalTime.eval ((BitstringEncoding.toEncoding (α := α)).encode x).length)) := fun x => by
    let L : List Bool := bitEncode x
    let Y : List Bool := bitEncode (f x)
    let Z : List Bool := bitEncode (g (f x))
    change Nonempty (TM2OutputsInTime C.cTM (L.map Mf.inputAlphabet.invFun)
      (some (Z.map Mg.outputAlphabet.invFun)) (totalTime.eval L.length))
    have hMf_out : TM2OutputsInTime C.tmF (L.map Mf.inputAlphabet.invFun)
        (some (Y.map C.outF.invFun)) (Mf.time.eval L.length) := Mf.outputsFun x
    have hMg_out : TM2OutputsInTime C.tmG (Y.map C.inG.invFun)
        (some (Z.map Mg.outputAlphabet.invFun)) (Mg.time.eval Y.length) := Mg.outputsFun (f x)
    have hY_len : Y.length ≤ L.length + hMf_out.steps * Bf := by
      have hlen1 := evals_stk_length_le C.tmF hMf_out.steps _ _ hMf_out.evals_in_steps C.tmF.k₁
      rw [haltList_stk_k1, List.length_map] at hlen1
      have hlen0 := initList_stk_length_le C.tmF (L.map Mf.inputAlphabet.invFun) C.tmF.k₁
      rw [List.length_map] at hlen0
      exact le_trans hlen1 (Nat.add_le_add_right hlen0 _)
    have hY_poly : Y.length ≤ polyY.eval L.length := by
      have h1 : hMf_out.steps * Bf ≤ Mf.time.eval L.length * Bf :=
        Nat.mul_le_mul_right Bf hMf_out.steps_le_m
      simp only [polyY, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul,
        Polynomial.eval_C]
      omega
    have hMg_steps_le : hMg_out.steps ≤ (Mg.time.comp polyY).eval L.length := by
      rw [Polynomial.eval_comp]
      exact le_trans hMg_out.steps_le_m (poly_eval_mono Mg.time hY_poly)
    have hinit_eq : initList C.cTM (L.map Mf.inputAlphabet.invFun) =
        C.embedF (Sum.inl 0) none C.tmG.initialState
          (initList C.tmF (L.map Mf.inputAlphabet.invFun)) := by
      dsimp [CompData.embedF, CompData.mkCfg, initList, CompData.cTM]
      congr 1; funext k; rcases k with (_ | kf | _)
      · simp
      · by_cases hkf : kf = C.tmF.k₀
        · subst hkf; simp
        · simp [hkf]
      · simp
    have hp0 := comp_sim_tmF C none C.tmG.initialState hMf_out.steps _ _ hMf_out.evals_in_steps
    let c1 := C.embedF (Sum.inl 0) none C.tmG.initialState
      (haltList C.tmF (Y.map C.outF.invFun))
    have hc1_eq : c1 = C.mkCfg (some (Sum.inl 0)) C.initVar c1.stk := rfl
    have hc1_kf1 : c1.stk (Sum.inr (Sum.inl C.tmF.k₁)) = Y.map C.outF.invFun := by
      dsimp [c1, CompData.embedF]; simp [haltList]
    obtain ⟨S₁, hp1, hS1_kf1, hS1_0, hS1_other⟩ := comp_phase0 C Y c1.stk hc1_kf1
    have hc1_0 : c1.stk (Sum.inl ()) = [] := rfl
    rw [hc1_0, List.append_nil] at hS1_0
    obtain ⟨S₂, hp2, hS2_0, hS2_kg0, hS2_other⟩ := comp_phase1 C Y.reverse S₁ hS1_0
    have hS1_kg0 : S₁ (Sum.inr (Sum.inr C.tmG.k₀)) = [] := by
      rw [hS1_other _ (by simp) (by simp)]; rfl
    rw [List.reverse_reverse, hS1_kg0, List.append_nil] at hS2_kg0
    have hcfg3_eq : C.mkCfg (some (Sum.inr (Sum.inr C.tmG.main))) C.initVar S₂ =
        C.embedG none C.tmF.initialState (initList C.tmG (Y.map C.inG.invFun)) := by
      dsimp [CompData.embedG, CompData.mkCfg, CompData.initVar, initList]
      congr 1; funext k; rcases k with (_ | kf | kg)
      · simp [hS2_0]
      · simp only [CompData.mergeG]
        rw [hS2_other _ (by simp) (by simp)]
        by_cases hkf1 : kf = C.tmF.k₁
        · subst hkf1; exact hS1_kf1
        · rw [hS1_other _ (by simp [hkf1]) (by simp)]
          dsimp [c1, CompData.embedF, haltList]; simp [hkf1]
      · by_cases hkg0 : kg = C.tmG.k₀
        · subst hkg0; simp [hS2_kg0]
        · simp only [CompData.mergeG, hkg0, ↓reduceDIte]
          rw [hS2_other _ (by simp) (by simp [hkg0]), hS1_other _ (by simp) (by simp)]
          rfl
    have hp3 := comp_sim_tmG C none C.tmF.initialState hMg_out.steps _ _ hMg_out.evals_in_steps
    have hhalt_eq : C.embedG none C.tmF.initialState
        (haltList C.tmG (Z.map Mg.outputAlphabet.invFun)) =
        haltList C.cTM (Z.map Mg.outputAlphabet.invFun) := by
      dsimp [CompData.embedG, CompData.mkCfg, haltList, CompData.cTM]
      congr 1; funext k; rcases k with (_ | _ | kg)
      · simp
      · simp
      · by_cases hkg1 : kg = C.tmG.k₁
        · subst hkg1; simp
        · simp [hkg1]
    let e0 : EvalsTo C.cTM.step (initList C.cTM (L.map Mf.inputAlphabet.invFun)) (some c1) :=
      ⟨hMf_out.steps, by rw [hinit_eq]; exact hp0⟩
    let e1 : EvalsTo C.cTM.step c1
        (some (C.mkCfg (some (Sum.inr (Sum.inr C.tmG.main))) C.initVar S₂)) :=
      EvalsTo.trans C.cTM.step _ _ _
        ⟨Y.length + 1, by rw [hc1_eq]; exact hp1⟩
        ⟨Y.reverse.length + 1, hp2⟩
    let e2 : EvalsTo C.cTM.step (C.mkCfg (some (Sum.inr (Sum.inr C.tmG.main))) C.initVar S₂)
        (some (haltList C.cTM (Z.map Mg.outputAlphabet.invFun))) :=
      ⟨hMg_out.steps, by rw [hcfg3_eq, ← hhalt_eq]; exact hp3⟩
    let eAll := EvalsTo.trans C.cTM.step _ _ _ e0 (EvalsTo.trans C.cTM.step _ _ _ e1 e2)
    refine ⟨⟨eAll, ?_⟩⟩
    dsimp only [eAll, e0, e1, e2, EvalsTo.trans]
    have hMf_le := hMf_out.steps_le_m
    simp only [List.length_reverse, totalTime, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C]
    omega
  exact ⟨{
    tm := C.cTM
    inputAlphabet := Mf.inputAlphabet
    outputAlphabet := Mg.outputAlphabet
    time := totalTime
    outputsFun := fun x => Classical.choice (hout x)
  }⟩

/- ### 2. Pairing with identity `x ↦ (x, f x)` -/

private structure PairIdData where
  tmF : FinTM2
  inF : tmF.Γ tmF.k₀ ≃ Bool
  outF : tmF.Γ tmF.k₁ ≃ Bool

private abbrev PairIdData.PK (D : PairIdData) : Type := Fin 4 ⊕ D.tmF.K
private abbrev PairIdData.PΛ (D : PairIdData) : Type := Fin 5 ⊕ D.tmF.Λ
private abbrev PairIdData.Pσ (D : PairIdData) : Type := Option Bool × D.tmF.σ

private abbrev PairIdData.pΓ (D : PairIdData) : D.PK → Type
  | Sum.inl _ => Bool
  | Sum.inr kf => D.tmF.Γ kf

private def PairIdData.liftF (D : PairIdData) (next : D.PΛ) :
    TM2.Stmt D.tmF.Γ D.tmF.Λ D.tmF.σ → TM2.Stmt D.pΓ D.PΛ D.Pσ
  | .push k f q => .push (Sum.inr k) (fun v => f v.2) (D.liftF next q)
  | .peek k f q => .peek (Sum.inr k) (fun v o => (v.1, f v.2 o)) (D.liftF next q)
  | .pop k f q => .pop (Sum.inr k) (fun v o => (v.1, f v.2 o)) (D.liftF next q)
  | .load a q => .load (fun v => (v.1, a v.2)) (D.liftF next q)
  | .branch p q₁ q₂ => .branch (fun v => p v.2) (D.liftF next q₁) (D.liftF next q₂)
  | .goto l => .goto (fun v => Sum.inr (l v.2))
  | .halt => .goto (fun _ => next)

private def PairIdData.pStmt (D : PairIdData) : D.PΛ → TM2.Stmt D.pΓ D.PΛ D.Pσ
  | Sum.inl 0 =>
    .pop (Sum.inl 0) (fun v o => (o, v.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 1) (fun v => v.1.getD false)
          (.push (Sum.inl 2) (fun v => v.1.getD false)
            (.load (fun v => (none, v.2))
              (.goto (fun _ => Sum.inl 0)))))
        (.goto (fun _ => Sum.inl 1)))
  | Sum.inl 1 =>
    .pop (Sum.inl 1) (fun v o => (o, v.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inr D.tmF.k₀) (fun v => D.inF.invFun (v.1.getD false))
          (.load (fun v => (none, v.2))
            (.goto (fun _ => Sum.inl 1))))
        (.goto (fun _ => Sum.inr D.tmF.main)))
  | Sum.inl 2 =>
    .pop (Sum.inr D.tmF.k₁) (fun v o => (o.map D.outF.toFun, v.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 1) (fun v => v.1.getD false)
          (.load (fun v => (none, v.2))
            (.goto (fun _ => Sum.inl 2))))
        (.goto (fun _ => Sum.inl 3)))
  | Sum.inl 3 =>
    .pop (Sum.inl 1) (fun v o => (o, v.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 3) (fun v => v.1.getD false)
          (.load (fun v => (none, v.2))
            (.goto (fun _ => Sum.inl 3))))
        (.push (Sum.inl 3) (fun _ => false)
          (.goto (fun _ => Sum.inl 4))))
  | Sum.inl 4 =>
    .pop (Sum.inl 2) (fun v o => (o, v.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 3) (fun v => v.1.getD false)
          (.push (Sum.inl 3) (fun _ => true)
            (.load (fun v => (none, v.2))
              (.goto (fun _ => Sum.inl 4)))))
        .halt)
  | Sum.inr lf => D.liftF (Sum.inl 2) (D.tmF.m lf)

private abbrev PairIdData.pTM (D : PairIdData) : FinTM2 where
  K := D.PK
  k₀ := Sum.inl 0
  k₁ := Sum.inl 3
  Γ := D.pΓ
  Λ := D.PΛ
  main := Sum.inl 0
  σ := D.Pσ
  initialState := (none, D.tmF.initialState)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := D.pStmt

private abbrev PairIdData.mkCfg (D : PairIdData) (l : Option D.PΛ) (v : D.Pσ)
    (S : ∀ k : D.PK, List (D.pΓ k)) : D.pTM.Cfg :=
  ⟨l, v, S⟩

private abbrev PairIdData.initVar (D : PairIdData) : D.Pσ :=
  (none, D.tmF.initialState)

@[simp]
private def PairIdData.mergeF (D : PairIdData)
    (baseStk : ∀ k : D.PK, List (D.pΓ k))
    (Sf : ∀ kf, List (D.tmF.Γ kf)) : ∀ k : D.PK, List (D.pΓ k)
  | Sum.inr kf => Sf kf
  | other => baseStk other

private def PairIdData.embedF (D : PairIdData) (next : D.PΛ) (v1 : Option Bool)
    (baseStk : ∀ k : D.PK, List (D.pΓ k)) (c : D.tmF.Cfg) : D.pTM.Cfg :=
  D.mkCfg
    (match c.l with
      | some lf => some (Sum.inr lf)
      | none => some next)
    (v1, c.var)
    (D.mergeF baseStk c.stk)

private lemma pairId_stepAux_liftF (D : PairIdData) (next : D.PΛ) (v1 : Option Bool)
    (baseStk : ∀ k : D.PK, List (D.pΓ k))
    (q : TM2.Stmt D.tmF.Γ D.tmF.Λ D.tmF.σ) (vf : D.tmF.σ) (Sf : ∀ kf, List (D.tmF.Γ kf)) :
    TM2.stepAux (D.liftF next q) (v1, vf) (D.mergeF baseStk Sf) =
      D.embedF next v1 baseStk (TM2.stepAux q vf Sf) := by
  induction q generalizing vf Sf with
  | push kf f q ih =>
    simp only [PairIdData.liftF, TM2.stepAux]
    have hupd : Function.update (D.mergeF baseStk Sf) (Sum.inr kf)
        (f vf :: D.mergeF baseStk Sf (Sum.inr kf)) =
        D.mergeF baseStk (Function.update Sf kf (f vf :: Sf kf)) := by
      funext k; rcases k with (_ | k')
      · simp
      · by_cases hk : k' = kf
        · subst hk; simp
        · simp [hk]
    rw [hupd]; exact ih vf _
  | peek _ _ _ ih => simp only [PairIdData.liftF, TM2.stepAux, PairIdData.mergeF]; exact ih _ Sf
  | pop kf f q ih =>
    simp only [PairIdData.liftF, TM2.stepAux]
    have hupd : Function.update (D.mergeF baseStk Sf) (Sum.inr kf)
        (D.mergeF baseStk Sf (Sum.inr kf)).tail =
        D.mergeF baseStk (Function.update Sf kf (Sf kf).tail) := by
      funext k; rcases k with (_ | k')
      · simp
      · by_cases hk : k' = kf
        · subst hk; simp
        · simp [hk]
    rw [hupd]; exact ih _ _
  | load _ _ ih => simp only [PairIdData.liftF, TM2.stepAux]; exact ih _ Sf
  | branch p _ _ ih₁ ih₂ =>
    simp only [PairIdData.liftF, TM2.stepAux]
    cases p vf
    · simp only [Bool.cond_false]; exact ih₂ vf Sf
    · simp only [Bool.cond_true]; exact ih₁ vf Sf
  | goto _ => rfl
  | halt => rfl

private lemma pairId_sim_tmF (D : PairIdData) (v1 : Option Bool)
    (baseStk : ∀ k : D.PK, List (D.pΓ k))
    (s : ℕ) (c c' : D.tmF.Cfg)
    (heval : (flip bind D.tmF.step)^[s] (some c) = some c') :
    (flip bind D.pTM.step)^[s] (some (D.embedF (Sum.inl 2) v1 baseStk c)) =
      some (D.embedF (Sum.inl 2) v1 baseStk c') := by
  induction s generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at heval ⊢
    rw [heval]
  | succ s ih =>
    rw [Function.iterate_succ_apply, flip_bind_some] at heval ⊢
    rcases c with ⟨_ | lf, vf, Sf⟩
    · change (flip bind D.tmF.step)^[s] none = some c' at heval
      rw [iterate_bind_none] at heval; cases heval
    · change (flip bind D.tmF.step)^[s] (some (TM2.stepAux (D.tmF.m lf) vf Sf)) = some c' at heval
      have hstep : D.pTM.step (D.embedF (Sum.inl 2) v1 baseStk ⟨some lf, vf, Sf⟩) =
          some (D.embedF (Sum.inl 2) v1 baseStk (TM2.stepAux (D.tmF.m lf) vf Sf)) :=
        congrArg some (pairId_stepAux_liftF D (Sum.inl 2) v1 baseStk (D.tmF.m lf) vf Sf)
      rw [hstep]; exact ih _ heval

private lemma pairId_p0 (D : PairIdData) (xs : List Bool)
    (S : ∀ k : D.PK, List (D.pΓ k)) (h0 : S (Sum.inl 0) = xs) :
    ∃ S₁ : ∀ k : D.PK, List (D.pΓ k),
      (flip bind D.pTM.step)^[xs.length + 1] (some (D.mkCfg (some (Sum.inl 0)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inl 1)) D.initVar S₁) ∧
      S₁ (Sum.inl 0) = [] ∧
      S₁ (Sum.inl 1) = xs.reverse ++ S (Sum.inl 1) ∧
      S₁ (Sum.inl 2) = xs.reverse ++ S (Sum.inl 2) ∧
      ∀ k, k ≠ Sum.inl 0 → k ≠ Sum.inl 1 → k ≠ Sum.inl 2 → S₁ k = S k := by
  induction xs generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 0) [], ?_, by simp, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.pStmt ⟨some (Sum.inl 0), D.initVar, S⟩ =
        some ⟨some (Sum.inl 1), D.initVar, Function.update S (Sum.inl 0) []⟩
      simp [PairIdData.pStmt, h0]
    · intro k hk0 _ _
      exact Function.update_of_ne hk0 _ _
  | cons b xs ih =>
    let S' : ∀ k : D.PK, List (D.pΓ k) :=
      Function.update
        (Function.update (Function.update S (Sum.inl 0) xs) (Sum.inl 1) (b :: S (Sum.inl 1)))
        (Sum.inl 2) (b :: S (Sum.inl 2))
    have hstep : D.pTM.step (D.mkCfg (some (Sum.inl 0)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 0)) D.initVar S') := by
      change TM2.step D.pStmt ⟨some (Sum.inl 0), D.initVar, S⟩ =
        some ⟨some (Sum.inl 0), D.initVar, S'⟩
      simp [PairIdData.pStmt, h0, S']
    have hS'0 : S' (Sum.inl 0) = xs := by simp [S']
    have hS'1 : S' (Sum.inl 1) = b :: S (Sum.inl 1) := by simp [S']
    have hS'2 : S' (Sum.inl 2) = b :: S (Sum.inl 2) := by simp [S']
    obtain ⟨S₁, heval, h10, h11, h12, h1other⟩ := ih S' hS'0
    refine ⟨S₁, ?_, h10, ?_, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h11, hS'1, List.reverse_cons, List.append_assoc, List.singleton_append]
    · rw [h12, hS'2, List.reverse_cons, List.append_assoc, List.singleton_append]
    · intro k hk0 hk1 hk2
      rw [h1other k hk0 hk1 hk2]
      simp [S', Function.update_of_ne hk2, Function.update_of_ne hk1, Function.update_of_ne hk0]

private lemma pairId_p1 (D : PairIdData) (ys : List Bool)
    (S : ∀ k : D.PK, List (D.pΓ k)) (h1 : S (Sum.inl 1) = ys) :
    ∃ S₂ : ∀ k : D.PK, List (D.pΓ k),
      (flip bind D.pTM.step)^[ys.length + 1] (some (D.mkCfg (some (Sum.inl 1)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inr D.tmF.main)) D.initVar S₂) ∧
      S₂ (Sum.inl 1) = [] ∧
      S₂ (Sum.inr D.tmF.k₀) = ys.reverse.map D.inF.invFun ++ S (Sum.inr D.tmF.k₀) ∧
      ∀ k, k ≠ Sum.inl 1 → k ≠ Sum.inr D.tmF.k₀ → S₂ k = S k := by
  induction ys generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 1) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.pStmt ⟨some (Sum.inl 1), D.initVar, S⟩ =
        some ⟨some (Sum.inr D.tmF.main), D.initVar, Function.update S (Sum.inl 1) []⟩
      simp [PairIdData.pStmt, h1]
    · intro k hk1 _
      exact Function.update_of_ne hk1 _ _
  | cons b ys ih =>
    let S' : ∀ k : D.PK, List (D.pΓ k) := Function.update
      (Function.update S (Sum.inl 1) ys)
      (Sum.inr D.tmF.k₀) (D.inF.invFun b :: S (Sum.inr D.tmF.k₀))
    have hstep : D.pTM.step (D.mkCfg (some (Sum.inl 1)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 1)) D.initVar S') := by
      change TM2.step D.pStmt ⟨some (Sum.inl 1), D.initVar, S⟩ =
        some ⟨some (Sum.inl 1), D.initVar, S'⟩
      simp [PairIdData.pStmt, h1, S']
    have hS'1 : S' (Sum.inl 1) = ys := by simp [S']
    have hS'kf : S' (Sum.inr D.tmF.k₀) = D.inF.invFun b :: S (Sum.inr D.tmF.k₀) := by simp [S']
    obtain ⟨S₂, heval, h21, h2kf, h2other⟩ := ih S' hS'1
    refine ⟨S₂, ?_, h21, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h2kf, hS'kf, List.reverse_cons, List.map_append, List.append_assoc, List.map_singleton,
        List.singleton_append]
    · intro k hk1 hkf
      rw [h2other k hk1 hkf]
      simp [S', Function.update_of_ne hkf, Function.update_of_ne hk1]

private lemma pairId_p2 (D : PairIdData) (ws : List Bool)
    (S : ∀ k : D.PK, List (D.pΓ k)) (hw : S (Sum.inr D.tmF.k₁) = ws.map D.outF.invFun) :
    ∃ S₄ : ∀ k : D.PK, List (D.pΓ k),
      (flip bind D.pTM.step)^[ws.length + 1] (some (D.mkCfg (some (Sum.inl 2)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inl 3)) D.initVar S₄) ∧
      S₄ (Sum.inr D.tmF.k₁) = [] ∧
      S₄ (Sum.inl 1) = ws.reverse ++ S (Sum.inl 1) ∧
      ∀ k, k ≠ Sum.inr D.tmF.k₁ → k ≠ Sum.inl 1 → S₄ k = S k := by
  induction ws generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inr D.tmF.k₁) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.pStmt ⟨some (Sum.inl 2), D.initVar, S⟩ =
        some ⟨some (Sum.inl 3), D.initVar, Function.update S (Sum.inr D.tmF.k₁) []⟩
      simp [PairIdData.pStmt, hw]
    · intro k hkf1 _
      exact Function.update_of_ne hkf1 _ _
  | cons b ws ih =>
    let S' : ∀ k : D.PK, List (D.pΓ k) := Function.update
      (Function.update S (Sum.inr D.tmF.k₁) (ws.map D.outF.invFun))
      (Sum.inl 1) (b :: S (Sum.inl 1))
    have hstep : D.pTM.step (D.mkCfg (some (Sum.inl 2)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 2)) D.initVar S') := by
      change TM2.step D.pStmt ⟨some (Sum.inl 2), D.initVar, S⟩ =
        some ⟨some (Sum.inl 2), D.initVar, S'⟩
      simp [PairIdData.pStmt, hw, S']
    have hS'kf1 : S' (Sum.inr D.tmF.k₁) = ws.map D.outF.invFun := by simp [S']
    have hS'1 : S' (Sum.inl 1) = b :: S (Sum.inl 1) := by simp [S']
    obtain ⟨S₄, heval, h4kf1, h41, h4other⟩ := ih S' hS'kf1
    refine ⟨S₄, ?_, h4kf1, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h41, hS'1, List.reverse_cons, List.append_assoc, List.singleton_append]
    · intro k hkf1 hk1
      rw [h4other k hkf1 hk1]
      simp [S', Function.update_of_ne hk1, Function.update_of_ne hkf1]

private lemma pairId_p3 (D : PairIdData) (zs : List Bool)
    (S : ∀ k : D.PK, List (D.pΓ k)) (hz : S (Sum.inl 1) = zs) :
    ∃ S₅ : ∀ k : D.PK, List (D.pΓ k),
      (flip bind D.pTM.step)^[zs.length + 1] (some (D.mkCfg (some (Sum.inl 3)) D.initVar S)) =
        some (D.mkCfg (some (Sum.inl 4)) D.initVar S₅) ∧
      S₅ (Sum.inl 1) = [] ∧
      S₅ (Sum.inl 3) = false :: (zs.reverse ++ S (Sum.inl 3)) ∧
      ∀ k, k ≠ Sum.inl 1 → k ≠ Sum.inl 3 → S₅ k = S k := by
  induction zs generalizing S with
  | nil =>
    let S₅ : ∀ k : D.PK, List (D.pΓ k) := Function.update
      (Function.update S (Sum.inl 1) [])
      (Sum.inl 3) (false :: S (Sum.inl 3))
    refine ⟨S₅, ?_, by simp [S₅], by simp [S₅], ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.pStmt ⟨some (Sum.inl 3), D.initVar, S⟩ =
        some ⟨some (Sum.inl 4), D.initVar, S₅⟩
      simp [PairIdData.pStmt, hz, S₅]
    · intro k hk1 hk3
      simp [S₅, Function.update_of_ne hk3, Function.update_of_ne hk1]
  | cons b zs ih =>
    let S' : ∀ k : D.PK, List (D.pΓ k) := Function.update
      (Function.update S (Sum.inl 1) zs)
      (Sum.inl 3) (b :: S (Sum.inl 3))
    have hstep : D.pTM.step (D.mkCfg (some (Sum.inl 3)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 3)) D.initVar S') := by
      change TM2.step D.pStmt ⟨some (Sum.inl 3), D.initVar, S⟩ =
        some ⟨some (Sum.inl 3), D.initVar, S'⟩
      simp [PairIdData.pStmt, hz, S']
    have hS'1 : S' (Sum.inl 1) = zs := by simp [S']
    have hS'3 : S' (Sum.inl 3) = b :: S (Sum.inl 3) := by simp [S']
    obtain ⟨S₅, heval, h51, h53, h5other⟩ := ih S' hS'1
    refine ⟨S₅, ?_, h51, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h53, hS'3, List.reverse_cons, List.append_assoc, List.singleton_append]
    · intro k hk1 hk3
      rw [h5other k hk1 hk3]
      simp [S', Function.update_of_ne hk3, Function.update_of_ne hk1]

private lemma pairId_p4 (D : PairIdData) (rs acc : List Bool)
    (S : ∀ k : D.PK, List (D.pΓ k))
    (hr : S (Sum.inl 2) = rs) (hacc : S (Sum.inl 3) = acc) :
    ∃ S₆ : ∀ k : D.PK, List (D.pΓ k),
      (flip bind D.pTM.step)^[rs.length + 1] (some (D.mkCfg (some (Sum.inl 4)) D.initVar S)) =
        some (D.mkCfg none D.initVar S₆) ∧
      S₆ (Sum.inl 2) = [] ∧
      S₆ (Sum.inl 3) = delimitRevAux rs acc ∧
      ∀ k, k ≠ Sum.inl 2 → k ≠ Sum.inl 3 → S₆ k = S k := by
  induction rs generalizing acc S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 2) [], ?_, by simp, by simp [delimitRevAux, hacc], ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step D.pStmt ⟨some (Sum.inl 4), D.initVar, S⟩ =
        some ⟨none, D.initVar, Function.update S (Sum.inl 2) []⟩
      simp [PairIdData.pStmt, hr]
    · intro k hk2 _
      exact Function.update_of_ne hk2 _ _
  | cons b rs ih =>
    let S' : ∀ k : D.PK, List (D.pΓ k) := Function.update
      (Function.update S (Sum.inl 2) rs)
      (Sum.inl 3) (true :: b :: S (Sum.inl 3))
    have hstep : D.pTM.step (D.mkCfg (some (Sum.inl 4)) D.initVar S) =
        some (D.mkCfg (some (Sum.inl 4)) D.initVar S') := by
      change TM2.step D.pStmt ⟨some (Sum.inl 4), D.initVar, S⟩ =
        some ⟨some (Sum.inl 4), D.initVar, S'⟩
      simp [PairIdData.pStmt, hr, S']
    have hS'2 : S' (Sum.inl 2) = rs := by simp [S']
    have hS'3 : S' (Sum.inl 3) = true :: b :: acc := by simp [S', hacc]
    obtain ⟨S₆, heval, h62, h63, h6other⟩ := ih (true :: b :: acc) S' hS'2 hS'3
    refine ⟨S₆, ?_, h62, h63, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · intro k hk2 hk3
      rw [h6other k hk2 hk3]
      simp [S', Function.update_of_ne hk3, Function.update_of_ne hk2]

theorem isPolyTime_pairId {α β : Type}
    [BitstringEncoding α] [BitstringEncoding β]
    {f : α → β} (hf : IsPolyTime f) :
    IsPolyTime (fun x => (x, f x)) := by
  rcases hf with ⟨Mf⟩
  let D : PairIdData := {
    tmF := Mf.tm
    inF := Mf.inputAlphabet
    outF := Mf.outputAlphabet
  }
  let Bf : ℕ := maxPushes D.tmF
  let polyY : Polynomial ℕ := Polynomial.X + Mf.time * Polynomial.C Bf
  let totalTime : Polynomial ℕ :=
    Polynomial.C 3 * Polynomial.X + Polynomial.C 5 + Mf.time + Polynomial.C 2 * polyY
  have hout : ∀ x : α, Nonempty (TM2OutputsInTime D.pTM
      (List.map (Equiv.refl Bool).invFun ((BitstringEncoding.toEncoding (α := α)).encode x))
      (some (List.map (Equiv.refl Bool).invFun
        ((BitstringEncoding.toEncoding (α := α × β)).encode (x, f x))))
      (totalTime.eval ((BitstringEncoding.toEncoding (α := α)).encode x).length)) := fun x => by
    let L : List Bool := bitEncode x
    let Y : List Bool := bitEncode (f x)
    change Nonempty (TM2OutputsInTime D.pTM (List.map (Equiv.refl Bool).invFun L)
      (some (List.map (Equiv.refl Bool).invFun (delimit L ++ Y))) (totalTime.eval L.length))
    have hmapL : List.map (Equiv.refl Bool).invFun L = L := by simp [Equiv.refl]
    have hmapP : List.map (Equiv.refl Bool).invFun (delimit L ++ Y) = delimit L ++ Y := by
      simp [Equiv.refl]
    rw [hmapL, hmapP]
    have hMf_out : TM2OutputsInTime D.tmF (L.map D.inF.invFun)
        (some (Y.map D.outF.invFun)) (Mf.time.eval L.length) := Mf.outputsFun x
    have hY_len : Y.length ≤ L.length + hMf_out.steps * Bf := by
      have hlen1 := evals_stk_length_le D.tmF hMf_out.steps _ _ hMf_out.evals_in_steps D.tmF.k₁
      rw [haltList_stk_k1, List.length_map] at hlen1
      have hlen0 := initList_stk_length_le D.tmF (L.map D.inF.invFun) D.tmF.k₁
      rw [List.length_map] at hlen0
      exact le_trans hlen1 (Nat.add_le_add_right hlen0 _)
    have hY_poly : Y.length ≤ polyY.eval L.length := by
      have h1 : hMf_out.steps * Bf ≤ Mf.time.eval L.length * Bf :=
        Nat.mul_le_mul_right Bf hMf_out.steps_le_m
      simp only [polyY, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul,
        Polynomial.eval_C]
      omega
    let c0 := initList D.pTM L
    have hc0_eq : c0 = D.mkCfg (some (Sum.inl 0)) D.initVar c0.stk := rfl
    have hc0_in : c0.stk (Sum.inl 0) = L := by simp [c0, PairIdData.pTM, initList]
    have hc0_other : ∀ k : D.PK, k ≠ Sum.inl 0 → c0.stk k = [] := by
      intro k hk; simp [c0, PairIdData.pTM, initList, hk]
    obtain ⟨S₁, hp0, hS1_0, hS1_1, hS1_2, hS1_other⟩ := pairId_p0 D L c0.stk hc0_in
    rw [hc0_other (Sum.inl 1) (by simp), List.append_nil] at hS1_1
    rw [hc0_other (Sum.inl 2) (by simp), List.append_nil] at hS1_2
    obtain ⟨S₂, hp1, hS2_1, hS2_kf0, hS2_other⟩ := pairId_p1 D L.reverse S₁ hS1_1
    have hS1_kf0 : S₁ (Sum.inr D.tmF.k₀) = [] := by
      rw [hS1_other _ (by simp) (by simp) (by simp)]; exact hc0_other _ (by simp)
    rw [List.reverse_reverse, hS1_kf0, List.append_nil] at hS2_kf0
    have hcfg2_eq : D.mkCfg (some (Sum.inr D.tmF.main)) D.initVar S₂ =
        D.embedF (Sum.inl 2) none S₂ (initList D.tmF (L.map D.inF.invFun)) := by
      dsimp [PairIdData.embedF, PairIdData.mkCfg, PairIdData.initVar, initList]
      congr 1; funext k; rcases k with (_ | kf)
      · rfl
      · by_cases hkf : kf = D.tmF.k₀
        · subst hkf; simp [hS2_kf0]
        · simp only [PairIdData.mergeF, hkf, ↓reduceDIte]
          rw [hS2_other _ (by simp) (by simp [hkf]),
            hS1_other _ (by simp) (by simp) (by simp), hc0_other _ (by simp)]
    have hp2 := pairId_sim_tmF D none S₂ hMf_out.steps _ _ hMf_out.evals_in_steps
    let c3 := D.embedF (Sum.inl 2) none S₂ (haltList D.tmF (Y.map D.outF.invFun))
    have hc3_eq : c3 = D.mkCfg (some (Sum.inl 2)) D.initVar c3.stk := rfl
    have hc3_kf1 : c3.stk (Sum.inr D.tmF.k₁) = Y.map D.outF.invFun := by
      dsimp [c3, PairIdData.embedF]; simp [haltList]
    obtain ⟨S₄, hp3, hS4_kf1, hS4_1, hS4_other⟩ := pairId_p2 D Y c3.stk hc3_kf1
    have hc3_1 : c3.stk (Sum.inl 1) = [] := by
      dsimp [c3, PairIdData.embedF]; exact hS2_1
    rw [hc3_1, List.append_nil] at hS4_1
    obtain ⟨S₅, hp4, hS5_1, hS5_3, hS5_other⟩ := pairId_p3 D Y.reverse S₄ hS4_1
    have hS4_3 : S₄ (Sum.inl 3) = [] := by
      rw [hS4_other _ (by simp) (by simp)]
      dsimp [c3, PairIdData.embedF]
      rw [hS2_other _ (by simp) (by simp), hS1_other _ (by simp) (by simp) (by simp),
        hc0_other _ (by simp)]
    rw [List.reverse_reverse, hS4_3, List.append_nil] at hS5_3
    have hS5_2 : S₅ (Sum.inl 2) = L.reverse := by
      rw [hS5_other _ (by simp) (by simp), hS4_other _ (by simp) (by simp)]
      dsimp [c3, PairIdData.embedF]
      rw [hS2_other _ (by simp) (by simp)]; exact hS1_2
    obtain ⟨S₆, hp5, hS6_2, hS6_3, hS6_other⟩ :=
      pairId_p4 D L.reverse (false :: Y) S₅ hS5_2 hS5_3
    rw [delimitRevAux_reverse] at hS6_3
    have hhalt_eq : D.mkCfg none D.initVar S₆ = haltList D.pTM (delimit L ++ Y) := by
      dsimp [PairIdData.mkCfg, PairIdData.initVar, haltList, PairIdData.pTM]
      congr 1; funext k; rcases k with (i | kf)
      · fin_cases i
        · rw [hS6_other _ (by simp) (by simp), hS5_other _ (by simp) (by simp),
            hS4_other _ (by simp) (by simp)]
          dsimp [c3, PairIdData.embedF]
          rw [hS2_other _ (by simp) (by simp)]; exact hS1_0
        · rw [hS6_other _ (by simp) (by simp)]; exact hS5_1
        · exact hS6_2
        · simp [hS6_3]
      · simp only [show (Sum.inr kf : D.PK) ≠ Sum.inl 3 by simp, ↓reduceDIte]
        rw [hS6_other _ (by simp) (by simp), hS5_other _ (by simp) (by simp)]
        by_cases hkf1 : kf = D.tmF.k₁
        · subst hkf1; exact hS4_kf1
        · rw [hS4_other _ (by simp [hkf1]) (by simp)]
          dsimp [c3, PairIdData.embedF, haltList]; simp [hkf1]
    let e0 : EvalsTo D.pTM.step c0 (some (D.mkCfg (some (Sum.inl 1)) D.initVar S₁)) :=
      ⟨L.length + 1, by rw [hc0_eq]; exact hp0⟩
    let e1 : EvalsTo D.pTM.step (D.mkCfg (some (Sum.inl 1)) D.initVar S₁) (some c3) :=
      EvalsTo.trans D.pTM.step _ _ _
        ⟨L.reverse.length + 1, hp1⟩
        ⟨hMf_out.steps, by rw [hcfg2_eq]; exact hp2⟩
    let e2 : EvalsTo D.pTM.step c3 (some (D.mkCfg (some (Sum.inl 4)) D.initVar S₅)) :=
      EvalsTo.trans D.pTM.step _ _ _
        ⟨Y.length + 1, by rw [hc3_eq]; exact hp3⟩
        ⟨Y.reverse.length + 1, hp4⟩
    let e3 : EvalsTo D.pTM.step (D.mkCfg (some (Sum.inl 4)) D.initVar S₅)
        (some (haltList D.pTM (delimit L ++ Y))) :=
      ⟨L.reverse.length + 1, by rw [← hhalt_eq]; exact hp5⟩
    let eAll := EvalsTo.trans D.pTM.step _ _ _ e0
      (EvalsTo.trans D.pTM.step _ _ _ e1 (EvalsTo.trans D.pTM.step _ _ _ e2 e3))
    refine ⟨⟨eAll, ?_⟩⟩
    dsimp only [eAll, e0, e1, e2, e3, EvalsTo.trans]
    have hMf_le := hMf_out.steps_le_m
    simp only [List.length_reverse, totalTime, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    omega
  exact ⟨{
    tm := D.pTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := totalTime
    outputsFun := fun x => Classical.choice (hout x)
  }⟩

/- ### 3. `Prod.fst` and `dropFirst : ((x, u), v) ↦ (u, v)` -/

private abbrev fstTM : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m
    | 0 =>
      .pop 0 (fun _ o => o)
        (.branch (fun v => v.getD false)
          (.pop 0 (fun _ o => o)
            (.push 1 (fun v => v.getD false)
              (.load (fun _ => none) (.goto (fun _ => 0)))))
          (.load (fun _ => none) (.goto (fun _ => 1))))
    | 1 =>
      .pop 0 (fun _ o => o)
        (.branch (fun v => v.isSome)
          (.load (fun _ => none) (.goto (fun _ => 1)))
          (.goto (fun _ => 2)))
    | 2 =>
      .pop 1 (fun _ o => o)
        (.branch (fun v => v.isSome)
          (.push 0 (fun v => v.getD false)
            (.load (fun _ => none) (.goto (fun _ => 2))))
          .halt)

private abbrev mkFstCfg (l : Option (Fin 3)) (v : Option Bool) (s0 s1 : List Bool) :
    fstTM.Cfg :=
  ⟨l, v, fun i => if i = 0 then s0 else s1⟩

private lemma fst_phase0 (xs rest acc : List Bool) :
    (flip bind fstTM.step)^[xs.length + 1] (some (mkFstCfg (some 0) none (delimit xs ++ rest) acc)) =
      some (mkFstCfg (some 1) none rest (xs.reverse ++ acc)) := by
  induction xs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step fstTM.m ⟨some 0, none, _⟩ = some ⟨some 1, none, _⟩
    simp only [fstTM, delimit, List.singleton_append, TM2.step, TM2.stepAux, ↓reduceIte,
      List.head?_cons, Option.getD_some, Bool.cond_false, List.tail_cons, Option.some.injEq,
      TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b xs ih =>
    have hstep : fstTM.step (mkFstCfg (some 0) none (delimit (b :: xs) ++ rest) acc) =
        some (mkFstCfg (some 0) none (delimit xs ++ rest) (b :: acc)) := by
      change TM2.step fstTM.m ⟨some 0, none, _⟩ = some ⟨some 0, none, _⟩
      simp only [fstTM, delimit, List.cons_append, TM2.step, TM2.stepAux, ↓reduceIte,
        List.head?_cons, Option.getD_some, Bool.cond_true, List.tail_cons, Function.update_self,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma fst_phase1 (rest s1 : List Bool) :
    (flip bind fstTM.step)^[rest.length + 1] (some (mkFstCfg (some 1) none rest s1)) =
      some (mkFstCfg (some 2) none [] s1) := by
  induction rest with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step fstTM.m ⟨some 1, none, _⟩ = some ⟨some 2, none, _⟩
    simp only [fstTM, TM2.step, TM2.stepAux, ↓reduceIte, List.head?_nil, Option.isSome_none,
      Bool.cond_false, List.tail_nil, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b rest ih =>
    have hstep : fstTM.step (mkFstCfg (some 1) none (b :: rest) s1) =
        some (mkFstCfg (some 1) none rest s1) := by
      change TM2.step fstTM.m ⟨some 1, none, _⟩ = some ⟨some 1, none, _⟩
      simp only [fstTM, TM2.step, TM2.stepAux, ↓reduceIte, List.head?_cons, Option.isSome_some,
        Bool.cond_true, List.tail_cons, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih]

private lemma fst_phase2 (zs acc : List Bool) :
    (flip bind fstTM.step)^[zs.length + 1] (some (mkFstCfg (some 2) none acc zs)) =
      some (mkFstCfg none none (zs.reverse ++ acc) []) := by
  induction zs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step fstTM.m ⟨some 2, none, _⟩ = some ⟨none, none, _⟩
    simp only [fstTM, TM2.step, TM2.stepAux, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
      List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil, List.reverse_nil,
      List.nil_append, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b zs ih =>
    have hstep : fstTM.step (mkFstCfg (some 2) none acc (b :: zs)) =
        some (mkFstCfg (some 2) none (b :: acc) zs) := by
      change TM2.step fstTM.m ⟨some 2, none, _⟩ = some ⟨some 2, none, _⟩
      simp only [fstTM, TM2.step, TM2.stepAux, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
        List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons, Option.getD_some,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

theorem isPolyTime_fst {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    IsPolyTime (Prod.fst : α × β → α) := by
  refine ⟨{
    tm := fstTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.X + Polynomial.C 2
    outputsFun := fun p => ?_
  }⟩
  let X : List Bool := bitEncode p.1
  let U : List Bool := bitEncode p.2
  change TM2OutputsInTime fstTM (List.map (Equiv.refl Bool).invFun (delimit X ++ U))
    (some (List.map (Equiv.refl Bool).invFun X))
    ((Polynomial.X + Polynomial.C 2).eval (delimit X ++ U).length)
  simp only [Equiv.refl, List.map_id]
  have hinit : initList fstTM (delimit X ++ U) = mkFstCfg (some 0) none (delimit X ++ U) [] := rfl
  have hhalt : mkFstCfg none none X [] = haltList fstTM X := rfl
  have hp0 := fst_phase0 X U []
  rw [List.append_nil] at hp0
  have hp1 := fst_phase1 U X.reverse
  have hp2 := fst_phase2 X.reverse []
  rw [List.reverse_reverse, List.append_nil, hhalt] at hp2
  let e0 : EvalsTo fstTM.step (initList fstTM (delimit X ++ U))
      (some (mkFstCfg (some 1) none U X.reverse)) := ⟨X.length + 1, by rw [hinit]; exact hp0⟩
  let e1 : EvalsTo fstTM.step (mkFstCfg (some 1) none U X.reverse)
      (some (mkFstCfg (some 2) none [] X.reverse)) := ⟨U.length + 1, hp1⟩
  let e2 : EvalsTo fstTM.step (mkFstCfg (some 2) none [] X.reverse)
      (some (haltList fstTM X)) := ⟨X.reverse.length + 1, hp2⟩
  let eAll := EvalsTo.trans fstTM.step _ _ _ e0 (EvalsTo.trans fstTM.step _ _ _ e1 e2)
  refine ⟨eAll, ?_⟩
  dsimp only [eAll, e0, e1, e2, EvalsTo.trans]
  rw [List.length_reverse, List.length_append, length_delimit]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  omega

private abbrev dropFirstTM : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m _ :=
    .pop () (fun _ _ => none)
      (.pop () (fun _ o => o)
        (.branch (fun v => v.getD false)
          (.pop () (fun _ _ => none)
            (.pop () (fun _ _ => none)
              (.goto (fun _ => ()))))
          (.load (fun _ => none) .halt)))

private abbrev mkDropCfg (l : Option Unit) (s : List Bool) : dropFirstTM.Cfg :=
  ⟨l, none, fun _ => s⟩

private lemma dropFirst_eval (xs u v : List Bool) :
    (flip bind dropFirstTM.step)^[xs.length + 1]
      (some (mkDropCfg (some ()) (delimit (delimit xs ++ u) ++ v))) =
      some (mkDropCfg none (delimit u ++ v)) := by
  induction xs with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step dropFirstTM.m ⟨some (), none, _⟩ = some ⟨none, none, _⟩
    simp only [dropFirstTM, delimit, List.cons_append, TM2.step,
      TM2.stepAux, Function.update_self, List.head?_cons, List.tail_cons, Option.getD_some,
      Bool.cond_false, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    funext u'; cases u'; rfl
  | cons b xs ih =>
    have hstep : dropFirstTM.step
        (mkDropCfg (some ()) (delimit (delimit (b :: xs) ++ u) ++ v)) =
        some (mkDropCfg (some ()) (delimit (delimit xs ++ u) ++ v)) := by
      change TM2.step dropFirstTM.m ⟨some (), none, _⟩ = some ⟨some (), none, _⟩
      simp only [dropFirstTM, delimit, List.cons_append, TM2.step, TM2.stepAux,
        Function.update_self, List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext u'; cases u'; rfl
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih]

theorem isPolyTime_dropFirst {α β γ : Type}
    [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ] :
    IsPolyTime (fun p : (α × β) × γ => (p.1.2, p.2)) := by
  refine ⟨{
    tm := dropFirstTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.X + Polynomial.C 1
    outputsFun := fun p => ?_
  }⟩
  let X : List Bool := bitEncode p.1.1
  let U : List Bool := bitEncode p.1.2
  let V : List Bool := bitEncode p.2
  change TM2OutputsInTime dropFirstTM
    (List.map (Equiv.refl Bool).invFun (delimit (delimit X ++ U) ++ V))
    (some (List.map (Equiv.refl Bool).invFun (delimit U ++ V)))
    ((Polynomial.X + Polynomial.C 1).eval (delimit (delimit X ++ U) ++ V).length)
  simp only [Equiv.refl, List.map_id]
  have hinit : initList dropFirstTM (delimit (delimit X ++ U) ++ V) =
      mkDropCfg (some ()) (delimit (delimit X ++ U) ++ V) := rfl
  have hhalt : mkDropCfg none (delimit U ++ V) = haltList dropFirstTM (delimit U ++ V) := rfl
  refine ⟨⟨X.length + 1, by rw [hinit, Option.map_some, ← hhalt]; exact dropFirst_eval X U V⟩, ?_⟩
  simp only [List.length_append, length_delimit, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  omega

theorem isPolyTime_pair {α β γ : Type}
    [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    {a : α → β} {b : α → γ}
    (ha : IsPolyTime a) (hb : IsPolyTime b) :
    IsPolyTime (fun x => (a x, b x)) := by
  have hp1 : IsPolyTime (fun x => (x, a x)) := isPolyTime_pairId ha
  have hbfst : IsPolyTime (fun p : α × β => b p.1) := isPolyTime_comp isPolyTime_fst hb
  have hp2 : IsPolyTime (fun p : α × β => (p, b p.1)) := isPolyTime_pairId hbfst
  have hp12 : IsPolyTime (fun x => ((x, a x), b x)) := isPolyTime_comp hp1 hp2
  exact isPolyTime_comp hp12 isPolyTime_dropFirst

/- ### 4. Basic encoding lemmas, `snd`, `const`, `ite`, `singleton`, `append` -/

private def delimit2RevAux : List Bool → List Bool → List Bool
  | [], acc => acc
  | b :: rest, acc => delimit2RevAux rest (true :: true :: true :: b :: acc)

private lemma delimit2RevAux_append (xs ys acc : List Bool) :
    delimit2RevAux (xs ++ ys) acc = delimit2RevAux ys (delimit2RevAux xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons b xs ih => exact ih (true :: true :: true :: b :: acc)

private lemma delimit2RevAux_reverse (A B G : List Bool) :
    delimit2RevAux A.reverse (true :: false :: (delimit B ++ G)) =
      delimit (delimit A ++ B) ++ G := by
  induction A with
  | nil => rfl
  | cons b l ih =>
    simp only [List.reverse_cons, delimit2RevAux_append, ih, delimit2RevAux, delimit,
      List.cons_append]

private lemma bitEncode_pair {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (a : α) (b : β) :
    bitEncode (a, b) = delimit (bitEncode a) ++ bitEncode b := rfl

private lemma bitEncode_bool (b : Bool) : bitEncode b = [b] := rfl

private lemma bitEncode_nil {α : Type} [BitstringEncoding α] :
    bitEncode ([] : List α) = [] := rfl

private lemma bitEncode_cons {α : Type} [BitstringEncoding α] (a : α) (l : List α) :
    bitEncode (a :: l) = delimit (bitEncode a) ++ bitEncode l := rfl

private lemma bitEncode_singleton {α : Type} [BitstringEncoding α] (a : α) :
    bitEncode [a] = delimit (bitEncode a) := by
  simp [bitEncode_cons, bitEncode_nil]

private lemma bitEncode_append {α : Type} [BitstringEncoding α] (xs ys : List α) :
    bitEncode (xs ++ ys) = bitEncode xs ++ bitEncode ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append, bitEncode_cons, ih, List.append_assoc]

private lemma list_length_le_bitEncode_length {α : Type} [BitstringEncoding α] (xs : List α) :
    xs.length ≤ (bitEncode xs).length := by
  induction xs with
  | nil => simp [bitEncode_nil]
  | cons a xs ih =>
    rw [bitEncode_cons, List.length_append, length_delimit, List.length_cons]
    omega

private lemma elem_bitEncode_le_list_bitEncode {α : Type} [BitstringEncoding α]
    {a : α} {xs : List α} (ha : a ∈ xs) :
    (bitEncode a).length ≤ (bitEncode xs).length := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
    rw [bitEncode_cons, List.length_append, length_delimit]
    rcases List.mem_cons.mp ha with rfl | hmem
    · omega
    · have h1 := ih hmem; omega

private def evalsInTime_mono {σ : Type*} {f : σ → Option σ} {a : σ} {b : Option σ}
    {m₁ m₂ : ℕ} (h : EvalsToInTime f a b m₁) (hle : m₁ ≤ m₂) : EvalsToInTime f a b m₂ :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hle⟩

private abbrev sndTM : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m _ :=
    .pop () (fun _ o => o)
      (.branch (fun v => v.getD false)
        (.pop () (fun _ _ => none) (.goto (fun _ => ())))
        (.load (fun _ => none) .halt))

private abbrev mkSndCfg (l : Option Unit) (s : List Bool) : sndTM.Cfg :=
  ⟨l, none, fun _ => s⟩

private lemma snd_eval (xs u : List Bool) :
    (flip bind sndTM.step)^[xs.length + 1] (some (mkSndCfg (some ()) (delimit xs ++ u))) =
      some (mkSndCfg none u) := by
  induction xs with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step sndTM.m ⟨some (), none, _⟩ = some ⟨none, none, _⟩
    simp only [sndTM, delimit, List.singleton_append, TM2.step, TM2.stepAux, Function.update_self,
      List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_false, Option.some.injEq,
      TM2.Cfg.mk.injEq, true_and]
    funext u'; cases u'; rfl
  | cons b xs ih =>
    have hstep : sndTM.step (mkSndCfg (some ()) (delimit (b :: xs) ++ u)) =
        some (mkSndCfg (some ()) (delimit xs ++ u)) := by
      change TM2.step sndTM.m ⟨some (), none, _⟩ = some ⟨some (), none, _⟩
      simp only [sndTM, delimit, List.cons_append, TM2.step, TM2.stepAux, Function.update_self,
        List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true, Option.some.injEq,
        TM2.Cfg.mk.injEq, true_and]
      funext u'; cases u'; rfl
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih]

theorem isPolyTime_snd {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    IsPolyTime (Prod.snd : α × β → β) := by
  refine ⟨{
    tm := sndTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.X + Polynomial.C 1
    outputsFun := fun p => ?_
  }⟩
  let X : List Bool := bitEncode p.1
  let U : List Bool := bitEncode p.2
  change TM2OutputsInTime sndTM (List.map (Equiv.refl Bool).invFun (delimit X ++ U))
    (some (List.map (Equiv.refl Bool).invFun U))
    ((Polynomial.X + Polynomial.C 1).eval (delimit X ++ U).length)
  simp only [Equiv.refl, List.map_id]
  have hinit : initList sndTM (delimit X ++ U) = mkSndCfg (some ()) (delimit X ++ U) := rfl
  have hhalt : mkSndCfg none U = haltList sndTM U := rfl
  refine ⟨⟨X.length + 1, by rw [hinit, Option.map_some, ← hhalt]; exact snd_eval X U⟩, ?_⟩
  simp only [List.length_append, length_delimit, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  omega

private def pushFoldrStmt (zs : List Bool) :
    TM2.Stmt (fun _ : Unit => Bool) (Fin 2) (Option Bool) :=
  zs.foldr (fun b q => .push () (fun _ => b) q) .halt

private lemma stepAux_pushFoldr (zs : List Bool) (S : Unit → List Bool) :
    TM2.stepAux (pushFoldrStmt zs) none S = ⟨none, none, fun _ => zs.reverse ++ S ()⟩ := by
  induction zs generalizing S with
  | nil =>
    simp only [pushFoldrStmt, List.foldr_nil, TM2.stepAux, List.reverse_nil, List.nil_append]
  | cons b zs ih =>
    rw [pushFoldrStmt, List.foldr_cons]
    change TM2.stepAux (.push () (fun _ => b) (pushFoldrStmt zs)) none S = _
    rw [TM2.stepAux, ih]
    simp only [Function.update_self, List.reverse_cons, List.append_assoc, List.singleton_append]

private abbrev constTM (w : List Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Fin 2
  main := 0
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m
    | 0 =>
      .pop () (fun _ o => o)
        (.branch (fun v => v.isSome)
          (.load (fun _ => none) (.goto (fun _ => 0)))
          (.goto (fun _ => 1)))
    | 1 => pushFoldrStmt w.reverse

private abbrev mkConstCfg (w : List Bool) (l : Option (Fin 2)) (s : List Bool) : (constTM w).Cfg :=
  ⟨l, none, fun _ => s⟩

private lemma constTM_drain (w xs : List Bool) :
    (flip bind (constTM w).step)^[xs.length + 1] (some (mkConstCfg w (some 0) xs)) =
      some (mkConstCfg w (some 1) []) := by
  induction xs with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step (constTM w).m ⟨some 0, none, _⟩ = some ⟨some 1, none, _⟩
    simp only [constTM, TM2.step, TM2.stepAux, List.head?_nil, Option.isSome_none,
      Bool.cond_false, List.tail_nil, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    funext u; cases u; rfl
  | cons b xs ih =>
    have hstep : (constTM w).step (mkConstCfg w (some 0) (b :: xs)) =
        some (mkConstCfg w (some 0) xs) := by
      change TM2.step (constTM w).m ⟨some 0, none, _⟩ = some ⟨some 0, none, _⟩
      simp only [constTM, TM2.step, TM2.stepAux, List.head?_cons, Option.isSome_some,
        Bool.cond_true, List.tail_cons, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext u; cases u; rfl
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih]

theorem isPolyTime_const {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (c : β) :
    IsPolyTime (fun _ : α => c) := by
  let W : List Bool := bitEncode c
  refine ⟨{
    tm := constTM W
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.X + Polynomial.C 2
    outputsFun := fun x => ?_
  }⟩
  let L : List Bool := bitEncode x
  change TM2OutputsInTime (constTM W) (List.map (Equiv.refl Bool).invFun L)
    (some (List.map (Equiv.refl Bool).invFun W))
    ((Polynomial.X + Polynomial.C 2).eval L.length)
  simp only [Equiv.refl, List.map_id]
  have hinit : initList (constTM W) L = mkConstCfg W (some 0) L := rfl
  have hhalt : mkConstCfg W none W = haltList (constTM W) W := rfl
  have hp0 := constTM_drain W L
  rw [← hinit] at hp0
  have hp1 : (flip bind (constTM W).step)^[1] (some (mkConstCfg W (some 1) [])) =
      some (haltList (constTM W) W) := by
    rw [Function.iterate_one, flip_bind_some]
    change some (TM2.stepAux (pushFoldrStmt W.reverse) none (fun _ => [])) = _
    rw [stepAux_pushFoldr, List.reverse_reverse, List.append_nil]
    exact congrArg some hhalt
  let eAll := EvalsTo.trans (constTM W).step _ _ _ ⟨L.length + 1, hp0⟩ ⟨1, hp1⟩
  refine ⟨eAll, ?_⟩
  dsimp only [eAll, EvalsTo.trans]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  omega

private abbrev selectTM : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin 5
  main := 0
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m
    | 0 =>
      .pop 0 (fun _ _ => none)
        (.pop 0 (fun _ o => o)
          (.pop 0 (fun v _ => v)
            (.branch (fun v => v.getD false)
              (.load (fun _ => none) (.goto (fun _ => 1)))
              (.load (fun _ => none) (.goto (fun _ => 4))))))
    | 1 =>
      .pop 0 (fun _ o => o)
        (.branch (fun v => v.getD false)
          (.pop 0 (fun _ o => o)
            (.push 1 (fun v => v.getD false)
              (.load (fun _ => none) (.goto (fun _ => 1)))))
          (.load (fun _ => none) (.goto (fun _ => 2))))
    | 2 =>
      .pop 0 (fun _ o => o)
        (.branch (fun v => v.isSome)
          (.load (fun _ => none) (.goto (fun _ => 2)))
          (.goto (fun _ => 3)))
    | 3 =>
      .pop 1 (fun _ o => o)
        (.branch (fun v => v.isSome)
          (.push 0 (fun v => v.getD false)
            (.load (fun _ => none) (.goto (fun _ => 3))))
          .halt)
    | 4 =>
      .pop 0 (fun _ o => o)
        (.branch (fun v => v.getD false)
          (.pop 0 (fun _ _ => none) (.goto (fun _ => 4)))
          (.load (fun _ => none) .halt))

private abbrev mkSelCfg (l : Option (Fin 5)) (s0 s1 : List Bool) : selectTM.Cfg :=
  ⟨l, none, fun i => if i = 0 then s0 else s1⟩

private lemma sel_p1 (xs rest acc : List Bool) :
    (flip bind selectTM.step)^[xs.length + 1]
      (some (mkSelCfg (some 1) (delimit xs ++ rest) acc)) =
      some (mkSelCfg (some 2) rest (xs.reverse ++ acc)) := by
  induction xs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step selectTM.m ⟨some 1, none, _⟩ = some ⟨some 2, none, _⟩
    simp only [selectTM, delimit, List.singleton_append, TM2.step, TM2.stepAux, ↓reduceIte,
      List.head?_cons, Option.getD_some, Bool.cond_false, List.tail_cons, Option.some.injEq,
      TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b xs ih =>
    have hstep : selectTM.step (mkSelCfg (some 1) (delimit (b :: xs) ++ rest) acc) =
        some (mkSelCfg (some 1) (delimit xs ++ rest) (b :: acc)) := by
      change TM2.step selectTM.m ⟨some 1, none, _⟩ = some ⟨some 1, none, _⟩
      simp only [selectTM, delimit, List.cons_append, TM2.step, TM2.stepAux, ↓reduceIte,
        List.head?_cons, Option.getD_some, Bool.cond_true, List.tail_cons, Function.update_self,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma sel_p2 (rest s1 : List Bool) :
    (flip bind selectTM.step)^[rest.length + 1] (some (mkSelCfg (some 2) rest s1)) =
      some (mkSelCfg (some 3) [] s1) := by
  induction rest with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step selectTM.m ⟨some 2, none, _⟩ = some ⟨some 3, none, _⟩
    simp only [selectTM, TM2.step, TM2.stepAux, ↓reduceIte, List.head?_nil, Option.isSome_none,
      Bool.cond_false, List.tail_nil, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b rest ih =>
    have hstep : selectTM.step (mkSelCfg (some 2) (b :: rest) s1) =
        some (mkSelCfg (some 2) rest s1) := by
      change TM2.step selectTM.m ⟨some 2, none, _⟩ = some ⟨some 2, none, _⟩
      simp only [selectTM, TM2.step, TM2.stepAux, ↓reduceIte, List.head?_cons, Option.isSome_some,
        Bool.cond_true, List.tail_cons, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih]

private lemma sel_p3 (zs acc : List Bool) :
    (flip bind selectTM.step)^[zs.length + 1] (some (mkSelCfg (some 3) acc zs)) =
      some (mkSelCfg none (zs.reverse ++ acc) []) := by
  induction zs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step selectTM.m ⟨some 3, none, _⟩ = some ⟨none, none, _⟩
    simp only [selectTM, TM2.step, TM2.stepAux, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
      List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil, List.reverse_nil,
      List.nil_append, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b zs ih =>
    have hstep : selectTM.step (mkSelCfg (some 3) acc (b :: zs)) =
        some (mkSelCfg (some 3) (b :: acc) zs) := by
      change TM2.step selectTM.m ⟨some 3, none, _⟩ = some ⟨some 3, none, _⟩
      simp only [selectTM, TM2.step, TM2.stepAux, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
        List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons, Option.getD_some,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma sel_p4 (xs u : List Bool) :
    (flip bind selectTM.step)^[xs.length + 1] (some (mkSelCfg (some 4) (delimit xs ++ u) [])) =
      some (mkSelCfg none u []) := by
  induction xs with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step selectTM.m ⟨some 4, none, _⟩ = some ⟨none, none, _⟩
    simp only [selectTM, delimit, List.singleton_append, TM2.step, TM2.stepAux, ↓reduceIte,
      List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_false, Option.some.injEq,
      TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b xs ih =>
    have hstep : selectTM.step (mkSelCfg (some 4) (delimit (b :: xs) ++ u) []) =
        some (mkSelCfg (some 4) (delimit xs ++ u) []) := by
      change TM2.step selectTM.m ⟨some 4, none, _⟩ = some ⟨some 4, none, _⟩
      simp only [selectTM, delimit, List.cons_append, TM2.step, TM2.stepAux, Function.update_self,
        ↓reduceIte, List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih]

theorem isPolyTime_select {β : Type} [BitstringEncoding β] :
    IsPolyTime (fun p : Bool × (β × β) => if p.1 then p.2.1 else p.2.2) := by
  refine ⟨{
    tm := selectTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.X + Polynomial.C 4
    outputsFun := fun p => ?_
  }⟩
  rcases p with ⟨b, u, v⟩
  let U : List Bool := bitEncode u
  let V : List Bool := bitEncode v
  let inp : List Bool := true :: b :: false :: (delimit U ++ V)
  change TM2OutputsInTime selectTM (List.map (Equiv.refl Bool).invFun inp)
    (some (List.map (Equiv.refl Bool).invFun (bitEncode (if b then u else v))))
    ((Polynomial.X + Polynomial.C 4).eval inp.length)
  simp only [Equiv.refl, List.map_id]
  have hinit : initList selectTM inp = mkSelCfg (some 0) inp [] := rfl
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hhalt : mkSelCfg none V [] = haltList selectTM V := rfl
    have hp0 : (flip bind selectTM.step)^[1] (some (mkSelCfg (some 0) inp [])) =
        some (mkSelCfg (some 4) (delimit U ++ V) []) := by
      rw [Function.iterate_one, flip_bind_some]
      change TM2.step selectTM.m ⟨some 0, none, _⟩ = some ⟨some 4, none, _⟩
      simp only [selectTM, inp, TM2.step, TM2.stepAux, Function.update_self, ↓reduceIte,
        List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_false, Option.some.injEq,
        TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [← hinit] at hp0
    have hp4 := sel_p4 U V
    rw [hhalt] at hp4
    let eAll := EvalsTo.trans selectTM.step _ _ _ ⟨1, hp0⟩ ⟨U.length + 1, hp4⟩
    refine ⟨eAll, ?_⟩
    dsimp only [eAll, EvalsTo.trans]
    simp only [inp, List.length_cons, List.length_append, length_delimit, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    omega
  · simp only [↓reduceIte]
    have hhalt : mkSelCfg none U [] = haltList selectTM U := rfl
    have hp0 : (flip bind selectTM.step)^[1] (some (mkSelCfg (some 0) inp [])) =
        some (mkSelCfg (some 1) (delimit U ++ V) []) := by
      rw [Function.iterate_one, flip_bind_some]
      change TM2.step selectTM.m ⟨some 0, none, _⟩ = some ⟨some 1, none, _⟩
      simp only [selectTM, inp, TM2.step, TM2.stepAux, Function.update_self, ↓reduceIte,
        List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true, Option.some.injEq,
        TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [← hinit] at hp0
    have hp1 := sel_p1 U V []
    rw [List.append_nil] at hp1
    have hp2 := sel_p2 V U.reverse
    have hp3 := sel_p3 U.reverse []
    rw [List.reverse_reverse, List.append_nil, hhalt] at hp3
    let e01 := EvalsTo.trans selectTM.step _ _ _ ⟨1, hp0⟩ ⟨U.length + 1, hp1⟩
    let e23 := EvalsTo.trans selectTM.step _ _ _ ⟨V.length + 1, hp2⟩ ⟨U.reverse.length + 1, hp3⟩
    let eAll := EvalsTo.trans selectTM.step _ _ _ e01 e23
    refine ⟨eAll, ?_⟩
    dsimp only [eAll, e01, e23, EvalsTo.trans]
    simp only [inp, List.length_reverse, List.length_cons, List.length_append, length_delimit,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega

theorem isPolyTime_ite {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {c : α → Bool} {t e : α → β}
    (hc : IsPolyTime c) (ht : IsPolyTime t) (he : IsPolyTime e) :
    IsPolyTime (fun x => if c x then t x else e x) :=
  isPolyTime_comp (isPolyTime_pair hc (isPolyTime_pair ht he)) isPolyTime_select

private abbrev singletonTM : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin 2
  main := 0
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m
    | 0 =>
      .pop 0 (fun _ o => o)
        (.branch (fun v => v.isSome)
          (.push 1 (fun v => v.getD false)
            (.load (fun _ => none) (.goto (fun _ => 0))))
          (.push 0 (fun _ => false) (.goto (fun _ => 1))))
    | 1 =>
      .pop 1 (fun _ o => o)
        (.branch (fun v => v.isSome)
          (.push 0 (fun v => v.getD false)
            (.push 0 (fun _ => true)
              (.load (fun _ => none) (.goto (fun _ => 1)))))
          .halt)

private abbrev mkSingCfg (l : Option (Fin 2)) (s0 s1 : List Bool) : singletonTM.Cfg :=
  ⟨l, none, fun i => if i = 0 then s0 else s1⟩

private lemma sing_p0 (xs acc : List Bool) :
    (flip bind singletonTM.step)^[xs.length + 1] (some (mkSingCfg (some 0) xs acc)) =
      some (mkSingCfg (some 1) [false] (xs.reverse ++ acc)) := by
  induction xs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step singletonTM.m ⟨some 0, none, _⟩ = some ⟨some 1, none, _⟩
    simp only [singletonTM, TM2.step, TM2.stepAux, ↓reduceIte, List.head?_nil, Option.isSome_none,
      Bool.cond_false, List.tail_nil, List.reverse_nil, List.nil_append, Option.some.injEq,
      TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b xs ih =>
    have hstep : singletonTM.step (mkSingCfg (some 0) (b :: xs) acc) =
        some (mkSingCfg (some 0) xs (b :: acc)) := by
      change TM2.step singletonTM.m ⟨some 0, none, _⟩ = some ⟨some 0, none, _⟩
      simp only [singletonTM, TM2.step, TM2.stepAux, ↓reduceIte, List.head?_cons,
        Option.isSome_some, Bool.cond_true, List.tail_cons, Option.getD_some, Option.some.injEq,
        TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma sing_p1 (rs acc : List Bool) :
    (flip bind singletonTM.step)^[rs.length + 1] (some (mkSingCfg (some 1) acc rs)) =
      some (mkSingCfg none (delimitRevAux rs acc) []) := by
  induction rs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step singletonTM.m ⟨some 1, none, _⟩ = some ⟨none, none, _⟩
    simp only [singletonTM, TM2.step, TM2.stepAux, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
      List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil, delimitRevAux,
      Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b rs ih =>
    have hstep : singletonTM.step (mkSingCfg (some 1) acc (b :: rs)) =
        some (mkSingCfg (some 1) (true :: b :: acc) rs) := by
      change TM2.step singletonTM.m ⟨some 1, none, _⟩ = some ⟨some 1, none, _⟩
      simp only [singletonTM, TM2.step, TM2.stepAux, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
        List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons, Option.getD_some,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih, delimitRevAux]

theorem isPolyTime_singleton {α : Type} [BitstringEncoding α] :
    IsPolyTime (fun x : α => [x]) := by
  refine ⟨{
    tm := singletonTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
    outputsFun := fun x => ?_
  }⟩
  let X : List Bool := bitEncode x
  change TM2OutputsInTime singletonTM (List.map (Equiv.refl Bool).invFun X)
    (some (List.map (Equiv.refl Bool).invFun (bitEncode [x])))
    ((Polynomial.C 2 * Polynomial.X + Polynomial.C 2).eval X.length)
  rw [bitEncode_singleton]
  simp only [Equiv.refl, List.map_id]
  have hinit : initList singletonTM X = mkSingCfg (some 0) X [] := rfl
  have hhalt : mkSingCfg none (delimit X) [] = haltList singletonTM (delimit X) := rfl
  have hp0 := sing_p0 X []
  rw [List.append_nil, ← hinit] at hp0
  have hp1 := sing_p1 X.reverse [false]
  rw [delimitRevAux_reverse, List.append_nil, hhalt] at hp1
  let eAll := EvalsTo.trans singletonTM.step _ _ _ ⟨X.length + 1, hp0⟩ ⟨X.reverse.length + 1, hp1⟩
  refine ⟨eAll, ?_⟩
  dsimp only [eAll, EvalsTo.trans]
  simp only [List.length_reverse, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  omega

private abbrev appendTM : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin 2
  main := 0
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m
    | 0 =>
      .pop 0 (fun _ o => o)
        (.branch (fun v => v.getD false)
          (.pop 0 (fun _ o => o)
            (.push 1 (fun v => v.getD false)
              (.load (fun _ => none) (.goto (fun _ => 0)))))
          (.load (fun _ => none) (.goto (fun _ => 1))))
    | 1 =>
      .pop 1 (fun _ o => o)
        (.branch (fun v => v.isSome)
          (.push 0 (fun v => v.getD false)
            (.load (fun _ => none) (.goto (fun _ => 1))))
          .halt)

private abbrev mkAppCfg (l : Option (Fin 2)) (s0 s1 : List Bool) : appendTM.Cfg :=
  ⟨l, none, fun i => if i = 0 then s0 else s1⟩

private lemma app_p0 (xs rest acc : List Bool) :
    (flip bind appendTM.step)^[xs.length + 1]
      (some (mkAppCfg (some 0) (delimit xs ++ rest) acc)) =
      some (mkAppCfg (some 1) rest (xs.reverse ++ acc)) := by
  induction xs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step appendTM.m ⟨some 0, none, _⟩ = some ⟨some 1, none, _⟩
    simp only [appendTM, delimit, List.singleton_append, TM2.step, TM2.stepAux, ↓reduceIte,
      List.head?_cons, Option.getD_some, Bool.cond_false, List.tail_cons, Option.some.injEq,
      TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b xs ih =>
    have hstep : appendTM.step (mkAppCfg (some 0) (delimit (b :: xs) ++ rest) acc) =
        some (mkAppCfg (some 0) (delimit xs ++ rest) (b :: acc)) := by
      change TM2.step appendTM.m ⟨some 0, none, _⟩ = some ⟨some 0, none, _⟩
      simp only [appendTM, delimit, List.cons_append, TM2.step, TM2.stepAux, ↓reduceIte,
        List.head?_cons, Option.getD_some, Bool.cond_true, List.tail_cons, Function.update_self,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma app_p1 (zs acc : List Bool) :
    (flip bind appendTM.step)^[zs.length + 1] (some (mkAppCfg (some 1) acc zs)) =
      some (mkAppCfg none (zs.reverse ++ acc) []) := by
  induction zs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step appendTM.m ⟨some 1, none, _⟩ = some ⟨none, none, _⟩
    simp only [appendTM, TM2.step, TM2.stepAux, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
      List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil, List.reverse_nil,
      List.nil_append, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b zs ih =>
    have hstep : appendTM.step (mkAppCfg (some 1) acc (b :: zs)) =
        some (mkAppCfg (some 1) (b :: acc) zs) := by
      change TM2.step appendTM.m ⟨some 1, none, _⟩ = some ⟨some 1, none, _⟩
      simp only [appendTM, TM2.step, TM2.stepAux, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
        List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons, Option.getD_some,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

theorem isPolyTime_append {α : Type} [BitstringEncoding α] :
    IsPolyTime (fun p : List α × List α => p.1 ++ p.2) := by
  refine ⟨{
    tm := appendTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.X + Polynomial.C 2
    outputsFun := fun p => ?_
  }⟩
  let X : List Bool := bitEncode p.1
  let Y : List Bool := bitEncode p.2
  change TM2OutputsInTime appendTM (List.map (Equiv.refl Bool).invFun (delimit X ++ Y))
    (some (List.map (Equiv.refl Bool).invFun (bitEncode (p.1 ++ p.2))))
    ((Polynomial.X + Polynomial.C 2).eval (delimit X ++ Y).length)
  rw [bitEncode_append]
  simp only [Equiv.refl, List.map_id]
  have hinit : initList appendTM (delimit X ++ Y) = mkAppCfg (some 0) (delimit X ++ Y) [] := rfl
  have hhalt : mkAppCfg none (X ++ Y) [] = haltList appendTM (X ++ Y) := rfl
  have hp0 := app_p0 X Y []
  rw [List.append_nil, ← hinit] at hp0
  have hp1 := app_p1 X.reverse Y
  rw [List.reverse_reverse, hhalt] at hp1
  let eAll := EvalsTo.trans appendTM.step _ _ _ ⟨X.length + 1, hp0⟩ ⟨X.reverse.length + 1, hp1⟩
  refine ⟨eAll, ?_⟩
  dsimp only [eAll, EvalsTo.trans]
  simp only [List.length_reverse, List.length_append, length_delimit, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

/- ### 5. Bounded contextual list fold `isPolyTime_foldlCtx` and list combinators -/

private structure FoldData where
  tmI : FinTM2
  tmS : FinTM2
  inI : tmI.Γ tmI.k₀ ≃ Bool
  outI : tmI.Γ tmI.k₁ ≃ Bool
  inS : tmS.Γ tmS.k₀ ≃ Bool
  outS : tmS.Γ tmS.k₁ ≃ Bool

private abbrev FoldData.FK (C : FoldData) : Type := Fin 5 ⊕ C.tmI.K ⊕ C.tmS.K
private abbrev FoldData.FΛ (C : FoldData) : Type := Fin 12 ⊕ C.tmI.Λ ⊕ C.tmS.Λ
private abbrev FoldData.Fσ (C : FoldData) : Type := Option Bool × C.tmI.σ × C.tmS.σ

private abbrev FoldData.fΓ (C : FoldData) : C.FK → Type
  | Sum.inl _ => Bool
  | Sum.inr (Sum.inl ki) => C.tmI.Γ ki
  | Sum.inr (Sum.inr ks) => C.tmS.Γ ks

private def FoldData.liftI (C : FoldData) (next : C.FΛ) :
    TM2.Stmt C.tmI.Γ C.tmI.Λ C.tmI.σ → TM2.Stmt C.fΓ C.FΛ C.Fσ
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun v => f v.2.1) (C.liftI next q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (C.liftI next q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (C.liftI next q)
  | .load a q => .load (fun v => (v.1, a v.2.1, v.2.2)) (C.liftI next q)
  | .branch p q₁ q₂ => .branch (fun v => p v.2.1) (C.liftI next q₁) (C.liftI next q₂)
  | .goto l => .goto (fun v => Sum.inr (Sum.inl (l v.2.1)))
  | .halt => .goto (fun _ => next)

private def FoldData.liftS (C : FoldData) (next : C.FΛ) :
    TM2.Stmt C.tmS.Γ C.tmS.Λ C.tmS.σ → TM2.Stmt C.fΓ C.FΛ C.Fσ
  | .push k f q => .push (Sum.inr (Sum.inr k)) (fun v => f v.2.2) (C.liftS next q)
  | .peek k f q => .peek (Sum.inr (Sum.inr k)) (fun v o => (v.1, v.2.1, f v.2.2 o)) (C.liftS next q)
  | .pop k f q => .pop (Sum.inr (Sum.inr k)) (fun v o => (v.1, v.2.1, f v.2.2 o)) (C.liftS next q)
  | .load a q => .load (fun v => (v.1, v.2.1, a v.2.2)) (C.liftS next q)
  | .branch p q₁ q₂ => .branch (fun v => p v.2.2) (C.liftS next q₁) (C.liftS next q₂)
  | .goto l => .goto (fun v => Sum.inr (Sum.inr (l v.2.2)))
  | .halt => .goto (fun _ => next)

private def FoldData.fStmt (C : FoldData) : C.FΛ → TM2.Stmt C.fΓ C.FΛ C.Fσ
  | Sum.inl 0 =>
    .pop (Sum.inl 0) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.getD false)
        (.pop (Sum.inl 0) (fun v o => (o, v.2.1, v.2.2))
          (.push (Sum.inl 1) (fun v => v.1.getD false)
            (.push (Sum.inl 4) (fun v => v.1.getD false)
              (.load (fun v => (none, v.2.1, v.2.2))
                (.goto (fun _ => Sum.inl 0))))))
        (.load (fun v => (none, v.2.1, v.2.2))
          (.goto (fun _ => Sum.inl 1))))
  | Sum.inl 1 =>
    .pop (Sum.inl 4) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inr (Sum.inl C.tmI.k₀)) (fun v => C.inI.invFun (v.1.getD false))
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 1))))
        (.goto (fun _ => Sum.inr (Sum.inl C.tmI.main))))
  | Sum.inl 2 =>
    .pop (Sum.inr (Sum.inl C.tmI.k₁)) (fun v o => (o.map C.outI.toFun, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 2) (fun v => v.1.getD false)
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 2))))
        (.goto (fun _ => Sum.inl 3)))
  | Sum.inl 3 =>
    .peek (Sum.inl 0) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.load (fun v => (none, v.2.1, v.2.2)) (.goto (fun _ => Sum.inl 4)))
        (.load (fun v => (none, v.2.1, v.2.2)) (.goto (fun _ => Sum.inl 10))))
  | Sum.inl 4 =>
    .pop (Sum.inl 0) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.getD false)
        (.pop (Sum.inl 0) (fun v o => (o, v.2.1, v.2.2))
          (.push (Sum.inl 3) (fun v => v.1.getD false)
            (.load (fun v => (none, v.2.1, v.2.2))
              (.goto (fun _ => Sum.inl 4)))))
        (.load (fun v => (none, v.2.1, v.2.2))
          (.goto (fun _ => Sum.inl 5))))
  | Sum.inl 5 =>
    .pop (Sum.inl 3) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inr (Sum.inr C.tmS.k₀)) (fun v => C.inS.invFun (v.1.getD false))
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 5))))
        (.push (Sum.inr (Sum.inr C.tmS.k₀)) (fun _ => C.inS.invFun false)
          (.goto (fun _ => Sum.inl 6))))
  | Sum.inl 6 =>
    .pop (Sum.inl 2) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inr (Sum.inr C.tmS.k₀)) (fun v => C.inS.invFun (v.1.getD false))
          (.push (Sum.inr (Sum.inr C.tmS.k₀)) (fun _ => C.inS.invFun true)
            (.load (fun v => (none, v.2.1, v.2.2))
              (.goto (fun _ => Sum.inl 6)))))
        (.push (Sum.inr (Sum.inr C.tmS.k₀)) (fun _ => C.inS.invFun false)
          (.push (Sum.inr (Sum.inr C.tmS.k₀)) (fun _ => C.inS.invFun true)
            (.goto (fun _ => Sum.inl 7)))))
  | Sum.inl 7 =>
    .pop (Sum.inl 1) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 4) (fun v => v.1.getD false)
          (.push (Sum.inr (Sum.inr C.tmS.k₀)) (fun v => C.inS.invFun (v.1.getD false))
            (.push (Sum.inr (Sum.inr C.tmS.k₀)) (fun _ => C.inS.invFun true)
              (.push (Sum.inr (Sum.inr C.tmS.k₀)) (fun _ => C.inS.invFun true)
                (.push (Sum.inr (Sum.inr C.tmS.k₀)) (fun _ => C.inS.invFun true)
                  (.load (fun v => (none, v.2.1, v.2.2))
                    (.goto (fun _ => Sum.inl 7))))))))
        (.goto (fun _ => Sum.inl 8)))
  | Sum.inl 8 =>
    .pop (Sum.inl 4) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 1) (fun v => v.1.getD false)
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 8))))
        (.goto (fun _ => Sum.inr (Sum.inr C.tmS.main))))
  | Sum.inl 9 =>
    .pop (Sum.inr (Sum.inr C.tmS.k₁)) (fun v o => (o.map C.outS.toFun, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 2) (fun v => v.1.getD false)
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 9))))
        (.goto (fun _ => Sum.inl 3)))
  | Sum.inl 10 =>
    .pop (Sum.inl 1) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.load (fun v => (none, v.2.1, v.2.2))
          (.goto (fun _ => Sum.inl 10)))
        (.goto (fun _ => Sum.inl 11)))
  | Sum.inl 11 =>
    .pop (Sum.inl 2) (fun v o => (o, v.2.1, v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push (Sum.inl 0) (fun v => v.1.getD false)
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => Sum.inl 11))))
        .halt)
  | Sum.inr (Sum.inl li) => C.liftI (Sum.inl 2) (C.tmI.m li)
  | Sum.inr (Sum.inr ls) => C.liftS (Sum.inl 9) (C.tmS.m ls)

private abbrev FoldData.fTM (C : FoldData) : FinTM2 where
  K := C.FK
  k₀ := Sum.inl 0
  k₁ := Sum.inl 0
  Γ := C.fΓ
  Λ := C.FΛ
  main := Sum.inl 0
  σ := C.Fσ
  initialState := (none, C.tmI.initialState, C.tmS.initialState)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := C.fStmt

private abbrev FoldData.mkCfg (C : FoldData) (l : Option C.FΛ) (v : C.Fσ)
    (S : ∀ k : C.FK, List (C.fΓ k)) : C.fTM.Cfg :=
  ⟨l, v, S⟩

private abbrev FoldData.initVar (C : FoldData) : C.Fσ :=
  (none, C.tmI.initialState, C.tmS.initialState)

@[simp]
private def FoldData.mergeI (C : FoldData)
    (baseStk : ∀ k : C.FK, List (C.fΓ k))
    (Si : ∀ ki, List (C.tmI.Γ ki)) : ∀ k : C.FK, List (C.fΓ k)
  | Sum.inr (Sum.inl ki) => Si ki
  | other => baseStk other

private def FoldData.embedI (C : FoldData) (next : C.FΛ) (v1 : Option Bool) (v3 : C.tmS.σ)
    (baseStk : ∀ k : C.FK, List (C.fΓ k)) (c : C.tmI.Cfg) : C.fTM.Cfg :=
  C.mkCfg
    (match c.l with
      | some li => some (Sum.inr (Sum.inl li))
      | none => some next)
    (v1, c.var, v3)
    (C.mergeI baseStk c.stk)

private lemma fold_stepAux_liftI (C : FoldData) (next : C.FΛ) (v1 : Option Bool) (v3 : C.tmS.σ)
    (baseStk : ∀ k : C.FK, List (C.fΓ k))
    (q : TM2.Stmt C.tmI.Γ C.tmI.Λ C.tmI.σ) (vi : C.tmI.σ) (Si : ∀ ki, List (C.tmI.Γ ki)) :
    TM2.stepAux (C.liftI next q) (v1, vi, v3) (C.mergeI baseStk Si) =
      C.embedI next v1 v3 baseStk (TM2.stepAux q vi Si) := by
  induction q generalizing vi Si with
  | push ki f q ih =>
    simp only [FoldData.liftI, TM2.stepAux]
    have hupd : Function.update (C.mergeI baseStk Si) (Sum.inr (Sum.inl ki))
        (f vi :: C.mergeI baseStk Si (Sum.inr (Sum.inl ki))) =
        C.mergeI baseStk (Function.update Si ki (f vi :: Si ki)) := by
      funext k; rcases k with (_ | k' | _)
      · simp
      · by_cases hk : k' = ki
        · subst hk; simp
        · simp [hk]
      · simp
    rw [hupd]; exact ih vi _
  | peek _ _ _ ih => simp only [FoldData.liftI, TM2.stepAux, FoldData.mergeI]; exact ih _ Si
  | pop ki f q ih =>
    simp only [FoldData.liftI, TM2.stepAux]
    have hupd : Function.update (C.mergeI baseStk Si) (Sum.inr (Sum.inl ki))
        (C.mergeI baseStk Si (Sum.inr (Sum.inl ki))).tail =
        C.mergeI baseStk (Function.update Si ki (Si ki).tail) := by
      funext k; rcases k with (_ | k' | _)
      · simp
      · by_cases hk : k' = ki
        · subst hk; simp
        · simp [hk]
      · simp
    rw [hupd]; exact ih _ _
  | load _ _ ih => simp only [FoldData.liftI, TM2.stepAux]; exact ih _ Si
  | branch p _ _ ih₁ ih₂ =>
    simp only [FoldData.liftI, TM2.stepAux]
    cases p vi
    · simp only [Bool.cond_false]; exact ih₂ vi Si
    · simp only [Bool.cond_true]; exact ih₁ vi Si
  | goto _ => rfl
  | halt => rfl

private lemma fold_sim_tmI (C : FoldData) (v1 : Option Bool) (v3 : C.tmS.σ)
    (baseStk : ∀ k : C.FK, List (C.fΓ k)) (s : ℕ) (c c' : C.tmI.Cfg)
    (heval : (flip bind C.tmI.step)^[s] (some c) = some c') :
    (flip bind C.fTM.step)^[s] (some (C.embedI (Sum.inl 2) v1 v3 baseStk c)) =
      some (C.embedI (Sum.inl 2) v1 v3 baseStk c') := by
  induction s generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at heval ⊢
    rw [heval]
  | succ s ih =>
    rw [Function.iterate_succ_apply, flip_bind_some] at heval ⊢
    rcases c with ⟨_ | li, vi, Si⟩
    · change (flip bind C.tmI.step)^[s] none = some c' at heval
      rw [iterate_bind_none] at heval; cases heval
    · change (flip bind C.tmI.step)^[s] (some (TM2.stepAux (C.tmI.m li) vi Si)) = some c' at heval
      have hstep : C.fTM.step (C.embedI (Sum.inl 2) v1 v3 baseStk ⟨some li, vi, Si⟩) =
          some (C.embedI (Sum.inl 2) v1 v3 baseStk (TM2.stepAux (C.tmI.m li) vi Si)) :=
        congrArg some (fold_stepAux_liftI C (Sum.inl 2) v1 v3 baseStk (C.tmI.m li) vi Si)
      rw [hstep]; exact ih _ heval

@[simp]
private def FoldData.mergeS (C : FoldData)
    (baseStk : ∀ k : C.FK, List (C.fΓ k))
    (Ss : ∀ ks, List (C.tmS.Γ ks)) : ∀ k : C.FK, List (C.fΓ k)
  | Sum.inr (Sum.inr ks) => Ss ks
  | other => baseStk other

private def FoldData.embedS (C : FoldData) (next : C.FΛ) (v1 : Option Bool) (v2 : C.tmI.σ)
    (baseStk : ∀ k : C.FK, List (C.fΓ k)) (c : C.tmS.Cfg) : C.fTM.Cfg :=
  C.mkCfg
    (match c.l with
      | some ls => some (Sum.inr (Sum.inr ls))
      | none => some next)
    (v1, v2, c.var)
    (C.mergeS baseStk c.stk)

private lemma fold_stepAux_liftS (C : FoldData) (next : C.FΛ) (v1 : Option Bool) (v2 : C.tmI.σ)
    (baseStk : ∀ k : C.FK, List (C.fΓ k))
    (q : TM2.Stmt C.tmS.Γ C.tmS.Λ C.tmS.σ) (vs : C.tmS.σ) (Ss : ∀ ks, List (C.tmS.Γ ks)) :
    TM2.stepAux (C.liftS next q) (v1, v2, vs) (C.mergeS baseStk Ss) =
      C.embedS next v1 v2 baseStk (TM2.stepAux q vs Ss) := by
  induction q generalizing vs Ss with
  | push ks f q ih =>
    simp only [FoldData.liftS, TM2.stepAux]
    have hupd : Function.update (C.mergeS baseStk Ss) (Sum.inr (Sum.inr ks))
        (f vs :: C.mergeS baseStk Ss (Sum.inr (Sum.inr ks))) =
        C.mergeS baseStk (Function.update Ss ks (f vs :: Ss ks)) := by
      funext k; rcases k with (_ | _ | k')
      · simp
      · simp
      · by_cases hk : k' = ks
        · subst hk; simp
        · simp [hk]
    rw [hupd]; exact ih vs _
  | peek _ _ _ ih => simp only [FoldData.liftS, TM2.stepAux, FoldData.mergeS]; exact ih _ Ss
  | pop ks f q ih =>
    simp only [FoldData.liftS, TM2.stepAux]
    have hupd : Function.update (C.mergeS baseStk Ss) (Sum.inr (Sum.inr ks))
        (C.mergeS baseStk Ss (Sum.inr (Sum.inr ks))).tail =
        C.mergeS baseStk (Function.update Ss ks (Ss ks).tail) := by
      funext k; rcases k with (_ | _ | k')
      · simp
      · simp
      · by_cases hk : k' = ks
        · subst hk; simp
        · simp [hk]
    rw [hupd]; exact ih _ _
  | load _ _ ih => simp only [FoldData.liftS, TM2.stepAux]; exact ih _ Ss
  | branch p _ _ ih₁ ih₂ =>
    simp only [FoldData.liftS, TM2.stepAux]
    cases p vs
    · simp only [Bool.cond_false]; exact ih₂ vs Ss
    · simp only [Bool.cond_true]; exact ih₁ vs Ss
  | goto _ => rfl
  | halt => rfl

private lemma fold_sim_tmS (C : FoldData) (v1 : Option Bool) (v2 : C.tmI.σ)
    (baseStk : ∀ k : C.FK, List (C.fΓ k)) (s : ℕ) (c c' : C.tmS.Cfg)
    (heval : (flip bind C.tmS.step)^[s] (some c) = some c') :
    (flip bind C.fTM.step)^[s] (some (C.embedS (Sum.inl 9) v1 v2 baseStk c)) =
      some (C.embedS (Sum.inl 9) v1 v2 baseStk c') := by
  induction s generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at heval ⊢
    rw [heval]
  | succ s ih =>
    rw [Function.iterate_succ_apply, flip_bind_some] at heval ⊢
    rcases c with ⟨_ | ls, vs, Ss⟩
    · change (flip bind C.tmS.step)^[s] none = some c' at heval
      rw [iterate_bind_none] at heval; cases heval
    · change (flip bind C.tmS.step)^[s] (some (TM2.stepAux (C.tmS.m ls) vs Ss)) = some c' at heval
      have hstep : C.fTM.step (C.embedS (Sum.inl 9) v1 v2 baseStk ⟨some ls, vs, Ss⟩) =
          some (C.embedS (Sum.inl 9) v1 v2 baseStk (TM2.stepAux (C.tmS.m ls) vs Ss)) :=
        congrArg some (fold_stepAux_liftS C (Sum.inl 9) v1 v2 baseStk (C.tmS.m ls) vs Ss)
      rw [hstep]; exact ih _ heval

@[simp]
private def FoldData.loopStk (C : FoldData) (A rem B : List Bool) :
    ∀ k : C.FK, List (C.fΓ k)
  | Sum.inl 0 => rem
  | Sum.inl 1 => A.reverse
  | Sum.inl 2 => B.reverse
  | _ => []

private abbrev FoldData.loopCfg (C : FoldData) (A rem B : List Bool) : C.fTM.Cfg :=
  C.mkCfg (some (Sum.inl 3)) C.initVar (C.loopStk A rem B)

private lemma fold_p0 (C : FoldData) (xs rest : List Bool)
    (S : ∀ k : C.FK, List (C.fΓ k)) (h0 : S (Sum.inl 0) = delimit xs ++ rest) :
    ∃ S₁ : ∀ k : C.FK, List (C.fΓ k),
      (flip bind C.fTM.step)^[xs.length + 1] (some (C.mkCfg (some (Sum.inl 0)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inl 1)) C.initVar S₁) ∧
      S₁ (Sum.inl 0) = rest ∧
      S₁ (Sum.inl 1) = xs.reverse ++ S (Sum.inl 1) ∧
      S₁ (Sum.inl 4) = xs.reverse ++ S (Sum.inl 4) ∧
      ∀ k, k ≠ Sum.inl 0 → k ≠ Sum.inl 1 → k ≠ Sum.inl 4 → S₁ k = S k := by
  induction xs generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 0) rest, ?_, by simp, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.fStmt ⟨some (Sum.inl 0), C.initVar, S⟩ =
        some ⟨some (Sum.inl 1), C.initVar, Function.update S (Sum.inl 0) rest⟩
      simp [FoldData.fStmt, h0, delimit]
    · intro k hk0 _ _
      exact Function.update_of_ne hk0 _ _
  | cons b xs ih =>
    let S' : ∀ k : C.FK, List (C.fΓ k) :=
      Function.update
        (Function.update
          (Function.update S (Sum.inl 0) (delimit xs ++ rest))
          (Sum.inl 1) (b :: S (Sum.inl 1)))
        (Sum.inl 4) (b :: S (Sum.inl 4))
    have hstep : C.fTM.step (C.mkCfg (some (Sum.inl 0)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 0)) C.initVar S') := by
      change TM2.step C.fStmt ⟨some (Sum.inl 0), C.initVar, S⟩ =
        some ⟨some (Sum.inl 0), C.initVar, S'⟩
      simp [FoldData.fStmt, h0, delimit, S']
    obtain ⟨S₁, heval, h10, h11, h14, h1other⟩ := ih S' (by simp [S'])
    refine ⟨S₁, ?_, h10, ?_, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h11, show S' (Sum.inl 1) = b :: S (Sum.inl 1) by simp [S'], List.reverse_cons,
        List.append_assoc, List.singleton_append]
    · rw [h14, show S' (Sum.inl 4) = b :: S (Sum.inl 4) by simp [S'], List.reverse_cons,
        List.append_assoc, List.singleton_append]
    · intro k hk0 hk1 hk4
      rw [h1other k hk0 hk1 hk4]
      simp [S', Function.update_of_ne hk4, Function.update_of_ne hk1, Function.update_of_ne hk0]

private lemma fold_p1 (C : FoldData) (ys : List Bool)
    (S : ∀ k : C.FK, List (C.fΓ k)) (h4 : S (Sum.inl 4) = ys) :
    ∃ S₂ : ∀ k : C.FK, List (C.fΓ k),
      (flip bind C.fTM.step)^[ys.length + 1] (some (C.mkCfg (some (Sum.inl 1)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inr (Sum.inl C.tmI.main))) C.initVar S₂) ∧
      S₂ (Sum.inl 4) = [] ∧
      S₂ (Sum.inr (Sum.inl C.tmI.k₀)) =
        ys.reverse.map C.inI.invFun ++ S (Sum.inr (Sum.inl C.tmI.k₀)) ∧
      ∀ k, k ≠ Sum.inl 4 → k ≠ Sum.inr (Sum.inl C.tmI.k₀) → S₂ k = S k := by
  induction ys generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 4) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.fStmt ⟨some (Sum.inl 1), C.initVar, S⟩ =
        some ⟨some (Sum.inr (Sum.inl C.tmI.main)), C.initVar, Function.update S (Sum.inl 4) []⟩
      simp [FoldData.fStmt, h4]
    · intro k hk4 _; exact Function.update_of_ne hk4 _ _
  | cons b ys ih =>
    let S' : ∀ k : C.FK, List (C.fΓ k) := Function.update
      (Function.update S (Sum.inl 4) ys)
      (Sum.inr (Sum.inl C.tmI.k₀))
      (C.inI.invFun b :: S (Sum.inr (Sum.inl C.tmI.k₀)))
    have hstep : C.fTM.step (C.mkCfg (some (Sum.inl 1)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 1)) C.initVar S') := by
      change TM2.step C.fStmt ⟨some (Sum.inl 1), C.initVar, S⟩ =
        some ⟨some (Sum.inl 1), C.initVar, S'⟩
      simp [FoldData.fStmt, h4, S']
    obtain ⟨S₂, heval, h24, h2ki, h2other⟩ := ih S' (by simp [S'])
    have hS'ki : S' (Sum.inr (Sum.inl C.tmI.k₀)) =
        C.inI.invFun b :: S (Sum.inr (Sum.inl C.tmI.k₀)) := by simp [S']
    refine ⟨S₂, ?_, h24, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h2ki, hS'ki, List.reverse_cons,
        List.map_append, List.append_assoc, List.map_singleton, List.singleton_append]
    · intro k hk4 hki
      rw [h2other k hk4 hki]
      simp [S', Function.update_of_ne hki, Function.update_of_ne hk4]

private lemma fold_p2 (C : FoldData) (ws : List Bool)
    (S : ∀ k : C.FK, List (C.fΓ k))
    (hw : S (Sum.inr (Sum.inl C.tmI.k₁)) = ws.map C.outI.invFun) :
    ∃ S₃ : ∀ k : C.FK, List (C.fΓ k),
      (flip bind C.fTM.step)^[ws.length + 1] (some (C.mkCfg (some (Sum.inl 2)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inl 3)) C.initVar S₃) ∧
      S₃ (Sum.inr (Sum.inl C.tmI.k₁)) = [] ∧
      S₃ (Sum.inl 2) = ws.reverse ++ S (Sum.inl 2) ∧
      ∀ k, k ≠ Sum.inr (Sum.inl C.tmI.k₁) → k ≠ Sum.inl 2 → S₃ k = S k := by
  induction ws generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inr (Sum.inl C.tmI.k₁)) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.fStmt ⟨some (Sum.inl 2), C.initVar, S⟩ =
        some ⟨some (Sum.inl 3), C.initVar, Function.update S (Sum.inr (Sum.inl C.tmI.k₁)) []⟩
      simp [FoldData.fStmt, hw]
    · intro k hki1 _; exact Function.update_of_ne hki1 _ _
  | cons b ws ih =>
    let S' : ∀ k : C.FK, List (C.fΓ k) := Function.update
      (Function.update S (Sum.inr (Sum.inl C.tmI.k₁)) (ws.map C.outI.invFun))
      (Sum.inl 2) (b :: S (Sum.inl 2))
    have hstep : C.fTM.step (C.mkCfg (some (Sum.inl 2)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 2)) C.initVar S') := by
      change TM2.step C.fStmt ⟨some (Sum.inl 2), C.initVar, S⟩ =
        some ⟨some (Sum.inl 2), C.initVar, S'⟩
      simp [FoldData.fStmt, hw, S']
    obtain ⟨S₃, heval, h3ki1, h32, h3other⟩ := ih S' (by simp [S'])
    refine ⟨S₃, ?_, h3ki1, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h32, show S' (Sum.inl 2) = b :: S (Sum.inl 2) by simp [S'], List.reverse_cons,
        List.append_assoc, List.singleton_append]
    · intro k hki1 hk2
      rw [h3other k hki1 hk2]
      simp [S', Function.update_of_ne hk2, Function.update_of_ne hki1]

private lemma fold_p4 (C : FoldData) (gs rest : List Bool)
    (S : ∀ k : C.FK, List (C.fΓ k)) (h0 : S (Sum.inl 0) = delimit gs ++ rest) :
    ∃ S₁ : ∀ k : C.FK, List (C.fΓ k),
      (flip bind C.fTM.step)^[gs.length + 1] (some (C.mkCfg (some (Sum.inl 4)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inl 5)) C.initVar S₁) ∧
      S₁ (Sum.inl 0) = rest ∧
      S₁ (Sum.inl 3) = gs.reverse ++ S (Sum.inl 3) ∧
      ∀ k, k ≠ Sum.inl 0 → k ≠ Sum.inl 3 → S₁ k = S k := by
  induction gs generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 0) rest, ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.fStmt ⟨some (Sum.inl 4), C.initVar, S⟩ =
        some ⟨some (Sum.inl 5), C.initVar, Function.update S (Sum.inl 0) rest⟩
      simp [FoldData.fStmt, h0, delimit]
    · intro k hk0 _; exact Function.update_of_ne hk0 _ _
  | cons b gs ih =>
    let S' : ∀ k : C.FK, List (C.fΓ k) := Function.update
      (Function.update S (Sum.inl 0) (delimit gs ++ rest))
      (Sum.inl 3) (b :: S (Sum.inl 3))
    have hstep : C.fTM.step (C.mkCfg (some (Sum.inl 4)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 4)) C.initVar S') := by
      change TM2.step C.fStmt ⟨some (Sum.inl 4), C.initVar, S⟩ =
        some ⟨some (Sum.inl 4), C.initVar, S'⟩
      simp [FoldData.fStmt, h0, delimit, S']
    obtain ⟨S₁, heval, h10, h13, h1other⟩ := ih S' (by simp [S'])
    refine ⟨S₁, ?_, h10, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h13, show S' (Sum.inl 3) = b :: S (Sum.inl 3) by simp [S'], List.reverse_cons,
        List.append_assoc, List.singleton_append]
    · intro k hk0 hk3
      rw [h1other k hk0 hk3]
      simp [S', Function.update_of_ne hk3, Function.update_of_ne hk0]

private lemma fold_p5 (C : FoldData) (zs : List Bool)
    (S : ∀ k : C.FK, List (C.fΓ k)) (hz : S (Sum.inl 3) = zs) :
    ∃ S₁ : ∀ k : C.FK, List (C.fΓ k),
      (flip bind C.fTM.step)^[zs.length + 1] (some (C.mkCfg (some (Sum.inl 5)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inl 6)) C.initVar S₁) ∧
      S₁ (Sum.inl 3) = [] ∧
      S₁ (Sum.inr (Sum.inr C.tmS.k₀)) =
        C.inS.invFun false :: (zs.reverse.map C.inS.invFun ++ S (Sum.inr (Sum.inr C.tmS.k₀))) ∧
      ∀ k, k ≠ Sum.inl 3 → k ≠ Sum.inr (Sum.inr C.tmS.k₀) → S₁ k = S k := by
  induction zs generalizing S with
  | nil =>
    let S₁ : ∀ k : C.FK, List (C.fΓ k) := Function.update
      (Function.update S (Sum.inl 3) [])
      (Sum.inr (Sum.inr C.tmS.k₀))
      (C.inS.invFun false :: S (Sum.inr (Sum.inr C.tmS.k₀)))
    refine ⟨S₁, ?_, by simp [S₁], by simp [S₁], ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.fStmt ⟨some (Sum.inl 5), C.initVar, S⟩ =
        some ⟨some (Sum.inl 6), C.initVar, S₁⟩
      simp [FoldData.fStmt, hz, S₁]
    · intro k hk3 hks0
      simp [S₁, Function.update_of_ne hks0, Function.update_of_ne hk3]
  | cons b zs ih =>
    let S' : ∀ k : C.FK, List (C.fΓ k) := Function.update
      (Function.update S (Sum.inl 3) zs)
      (Sum.inr (Sum.inr C.tmS.k₀))
      (C.inS.invFun b :: S (Sum.inr (Sum.inr C.tmS.k₀)))
    have hstep : C.fTM.step (C.mkCfg (some (Sum.inl 5)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 5)) C.initVar S') := by
      change TM2.step C.fStmt ⟨some (Sum.inl 5), C.initVar, S⟩ =
        some ⟨some (Sum.inl 5), C.initVar, S'⟩
      simp [FoldData.fStmt, hz, S']
    obtain ⟨S₁, heval, h13, h1ks0, h1other⟩ := ih S' (by simp [S'])
    have hS'ks : S' (Sum.inr (Sum.inr C.tmS.k₀)) =
        C.inS.invFun b :: S (Sum.inr (Sum.inr C.tmS.k₀)) := by simp [S']
    refine ⟨S₁, ?_, h13, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h1ks0, hS'ks, List.reverse_cons,
        List.map_append, List.append_assoc, List.map_singleton, List.singleton_append]
    · intro k hk3 hks0
      rw [h1other k hk3 hks0]
      simp [S', Function.update_of_ne hks0, Function.update_of_ne hk3]

private lemma fold_p6 (C : FoldData) (rs acc : List Bool)
    (S : ∀ k : C.FK, List (C.fΓ k))
    (hr : S (Sum.inl 2) = rs)
    (hacc : S (Sum.inr (Sum.inr C.tmS.k₀)) = acc.map C.inS.invFun) :
    ∃ S₁ : ∀ k : C.FK, List (C.fΓ k),
      (flip bind C.fTM.step)^[rs.length + 1] (some (C.mkCfg (some (Sum.inl 6)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inl 7)) C.initVar S₁) ∧
      S₁ (Sum.inl 2) = [] ∧
      S₁ (Sum.inr (Sum.inr C.tmS.k₀)) =
        (true :: false :: delimitRevAux rs acc).map C.inS.invFun ∧
      ∀ k, k ≠ Sum.inl 2 → k ≠ Sum.inr (Sum.inr C.tmS.k₀) → S₁ k = S k := by
  induction rs generalizing acc S with
  | nil =>
    let S₁ : ∀ k : C.FK, List (C.fΓ k) := Function.update
      (Function.update S (Sum.inl 2) [])
      (Sum.inr (Sum.inr C.tmS.k₀))
      (C.inS.invFun true :: C.inS.invFun false :: S (Sum.inr (Sum.inr C.tmS.k₀)))
    refine ⟨S₁, ?_, by simp [S₁], by simp [S₁, delimitRevAux, hacc], ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.fStmt ⟨some (Sum.inl 6), C.initVar, S⟩ =
        some ⟨some (Sum.inl 7), C.initVar, S₁⟩
      simp [FoldData.fStmt, hr, S₁]
    · intro k hk2 hks0
      simp [S₁, Function.update_of_ne hks0, Function.update_of_ne hk2]
  | cons b rs ih =>
    let S' : ∀ k : C.FK, List (C.fΓ k) := Function.update
      (Function.update S (Sum.inl 2) rs)
      (Sum.inr (Sum.inr C.tmS.k₀))
      (C.inS.invFun true :: C.inS.invFun b :: S (Sum.inr (Sum.inr C.tmS.k₀)))
    have hstep : C.fTM.step (C.mkCfg (some (Sum.inl 6)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 6)) C.initVar S') := by
      change TM2.step C.fStmt ⟨some (Sum.inl 6), C.initVar, S⟩ =
        some ⟨some (Sum.inl 6), C.initVar, S'⟩
      simp [FoldData.fStmt, hr, S']
    obtain ⟨S₁, heval, h12, h1ks0, h1other⟩ :=
      ih (true :: b :: acc) S' (by simp [S']) (by simp [S', hacc])
    refine ⟨S₁, ?_, h12, h1ks0, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · intro k hk2 hks0
      rw [h1other k hk2 hks0]
      simp [S', Function.update_of_ne hks0, Function.update_of_ne hk2]

private lemma fold_p7 (C : FoldData) (rs acc : List Bool)
    (S : ∀ k : C.FK, List (C.fΓ k))
    (hr : S (Sum.inl 1) = rs)
    (hacc : S (Sum.inr (Sum.inr C.tmS.k₀)) = acc.map C.inS.invFun) :
    ∃ S₁ : ∀ k : C.FK, List (C.fΓ k),
      (flip bind C.fTM.step)^[rs.length + 1] (some (C.mkCfg (some (Sum.inl 7)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inl 8)) C.initVar S₁) ∧
      S₁ (Sum.inl 1) = [] ∧
      S₁ (Sum.inl 4) = rs.reverse ++ S (Sum.inl 4) ∧
      S₁ (Sum.inr (Sum.inr C.tmS.k₀)) = (delimit2RevAux rs acc).map C.inS.invFun ∧
      ∀ k, k ≠ Sum.inl 1 → k ≠ Sum.inl 4 → k ≠ Sum.inr (Sum.inr C.tmS.k₀) → S₁ k = S k := by
  induction rs generalizing acc S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 1) [], ?_, by simp, by simp,
      by simp [delimit2RevAux, hacc], ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.fStmt ⟨some (Sum.inl 7), C.initVar, S⟩ =
        some ⟨some (Sum.inl 8), C.initVar, Function.update S (Sum.inl 1) []⟩
      simp [FoldData.fStmt, hr]
    · intro k hk1 _ _; exact Function.update_of_ne hk1 _ _
  | cons b rs ih =>
    let S' : ∀ k : C.FK, List (C.fΓ k) :=
      Function.update
        (Function.update
          (Function.update S (Sum.inl 1) rs)
          (Sum.inl 4) (b :: S (Sum.inl 4)))
        (Sum.inr (Sum.inr C.tmS.k₀))
        (C.inS.invFun true :: C.inS.invFun true :: C.inS.invFun true :: C.inS.invFun b ::
          S (Sum.inr (Sum.inr C.tmS.k₀)))
    have hstep : C.fTM.step (C.mkCfg (some (Sum.inl 7)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 7)) C.initVar S') := by
      change TM2.step C.fStmt ⟨some (Sum.inl 7), C.initVar, S⟩ =
        some ⟨some (Sum.inl 7), C.initVar, S'⟩
      simp [FoldData.fStmt, hr, S']
    obtain ⟨S₁, heval, h11, h14, h1ks0, h1other⟩ :=
      ih (true :: true :: true :: b :: acc) S' (by simp [S']) (by simp [S', hacc])
    refine ⟨S₁, ?_, h11, ?_, h1ks0, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h14, show S' (Sum.inl 4) = b :: S (Sum.inl 4) by simp [S'], List.reverse_cons,
        List.append_assoc, List.singleton_append]
    · intro k hk1 hk4 hks0
      rw [h1other k hk1 hk4 hks0]
      simp [S', Function.update_of_ne hks0, Function.update_of_ne hk4, Function.update_of_ne hk1]

private lemma fold_p8 (C : FoldData) (ys : List Bool)
    (S : ∀ k : C.FK, List (C.fΓ k)) (h4 : S (Sum.inl 4) = ys) :
    ∃ S₁ : ∀ k : C.FK, List (C.fΓ k),
      (flip bind C.fTM.step)^[ys.length + 1] (some (C.mkCfg (some (Sum.inl 8)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inr (Sum.inr C.tmS.main))) C.initVar S₁) ∧
      S₁ (Sum.inl 4) = [] ∧
      S₁ (Sum.inl 1) = ys.reverse ++ S (Sum.inl 1) ∧
      ∀ k, k ≠ Sum.inl 4 → k ≠ Sum.inl 1 → S₁ k = S k := by
  induction ys generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 4) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.fStmt ⟨some (Sum.inl 8), C.initVar, S⟩ =
        some ⟨some (Sum.inr (Sum.inr C.tmS.main)), C.initVar, Function.update S (Sum.inl 4) []⟩
      simp [FoldData.fStmt, h4]
    · intro k hk4 _; exact Function.update_of_ne hk4 _ _
  | cons b ys ih =>
    let S' : ∀ k : C.FK, List (C.fΓ k) := Function.update
      (Function.update S (Sum.inl 4) ys)
      (Sum.inl 1) (b :: S (Sum.inl 1))
    have hstep : C.fTM.step (C.mkCfg (some (Sum.inl 8)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 8)) C.initVar S') := by
      change TM2.step C.fStmt ⟨some (Sum.inl 8), C.initVar, S⟩ =
        some ⟨some (Sum.inl 8), C.initVar, S'⟩
      simp [FoldData.fStmt, h4, S']
    obtain ⟨S₁, heval, h14, h11, h1other⟩ := ih S' (by simp [S'])
    refine ⟨S₁, ?_, h14, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h11, show S' (Sum.inl 1) = b :: S (Sum.inl 1) by simp [S'], List.reverse_cons,
        List.append_assoc, List.singleton_append]
    · intro k hk4 hk1
      rw [h1other k hk4 hk1]
      simp [S', Function.update_of_ne hk1, Function.update_of_ne hk4]

private lemma fold_p9 (C : FoldData) (ws : List Bool)
    (S : ∀ k : C.FK, List (C.fΓ k))
    (hw : S (Sum.inr (Sum.inr C.tmS.k₁)) = ws.map C.outS.invFun) :
    ∃ S₁ : ∀ k : C.FK, List (C.fΓ k),
      (flip bind C.fTM.step)^[ws.length + 1] (some (C.mkCfg (some (Sum.inl 9)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inl 3)) C.initVar S₁) ∧
      S₁ (Sum.inr (Sum.inr C.tmS.k₁)) = [] ∧
      S₁ (Sum.inl 2) = ws.reverse ++ S (Sum.inl 2) ∧
      ∀ k, k ≠ Sum.inr (Sum.inr C.tmS.k₁) → k ≠ Sum.inl 2 → S₁ k = S k := by
  induction ws generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inr (Sum.inr C.tmS.k₁)) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.fStmt ⟨some (Sum.inl 9), C.initVar, S⟩ =
        some ⟨some (Sum.inl 3), C.initVar, Function.update S (Sum.inr (Sum.inr C.tmS.k₁)) []⟩
      simp [FoldData.fStmt, hw]
    · intro k hks1 _; exact Function.update_of_ne hks1 _ _
  | cons b ws ih =>
    let S' : ∀ k : C.FK, List (C.fΓ k) := Function.update
      (Function.update S (Sum.inr (Sum.inr C.tmS.k₁)) (ws.map C.outS.invFun))
      (Sum.inl 2) (b :: S (Sum.inl 2))
    have hstep : C.fTM.step (C.mkCfg (some (Sum.inl 9)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 9)) C.initVar S') := by
      change TM2.step C.fStmt ⟨some (Sum.inl 9), C.initVar, S⟩ =
        some ⟨some (Sum.inl 9), C.initVar, S'⟩
      simp [FoldData.fStmt, hw, S']
    obtain ⟨S₁, heval, h1ks1, h12, h1other⟩ := ih S' (by simp [S'])
    refine ⟨S₁, ?_, h1ks1, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h12, show S' (Sum.inl 2) = b :: S (Sum.inl 2) by simp [S'], List.reverse_cons,
        List.append_assoc, List.singleton_append]
    · intro k hks1 hk2
      rw [h1other k hks1 hk2]
      simp [S', Function.update_of_ne hk2, Function.update_of_ne hks1]

private lemma fold_p10 (C : FoldData) (ys : List Bool)
    (S : ∀ k : C.FK, List (C.fΓ k)) (h1 : S (Sum.inl 1) = ys) :
    ∃ S₁ : ∀ k : C.FK, List (C.fΓ k),
      (flip bind C.fTM.step)^[ys.length + 1] (some (C.mkCfg (some (Sum.inl 10)) C.initVar S)) =
        some (C.mkCfg (some (Sum.inl 11)) C.initVar S₁) ∧
      S₁ (Sum.inl 1) = [] ∧
      ∀ k, k ≠ Sum.inl 1 → S₁ k = S k := by
  induction ys generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 1) [], ?_, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.fStmt ⟨some (Sum.inl 10), C.initVar, S⟩ =
        some ⟨some (Sum.inl 11), C.initVar, Function.update S (Sum.inl 1) []⟩
      simp [FoldData.fStmt, h1]
    · intro k hk1; exact Function.update_of_ne hk1 _ _
  | cons b ys ih =>
    let S' : ∀ k : C.FK, List (C.fΓ k) := Function.update S (Sum.inl 1) ys
    have hstep : C.fTM.step (C.mkCfg (some (Sum.inl 10)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 10)) C.initVar S') := by
      change TM2.step C.fStmt ⟨some (Sum.inl 10), C.initVar, S⟩ =
        some ⟨some (Sum.inl 10), C.initVar, S'⟩
      simp [FoldData.fStmt, h1, S']
    obtain ⟨S₁, heval, h11, h1other⟩ := ih S' (by simp [S'])
    refine ⟨S₁, ?_, h11, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · intro k hk1
      rw [h1other k hk1]
      exact Function.update_of_ne hk1 _ _

private lemma fold_p11 (C : FoldData) (zs : List Bool)
    (S : ∀ k : C.FK, List (C.fΓ k)) (h2 : S (Sum.inl 2) = zs) :
    ∃ S₁ : ∀ k : C.FK, List (C.fΓ k),
      (flip bind C.fTM.step)^[zs.length + 1] (some (C.mkCfg (some (Sum.inl 11)) C.initVar S)) =
        some (C.mkCfg none C.initVar S₁) ∧
      S₁ (Sum.inl 2) = [] ∧
      S₁ (Sum.inl 0) = zs.reverse ++ S (Sum.inl 0) ∧
      ∀ k, k ≠ Sum.inl 2 → k ≠ Sum.inl 0 → S₁ k = S k := by
  induction zs generalizing S with
  | nil =>
    refine ⟨Function.update S (Sum.inl 2) [], ?_, by simp, by simp, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step C.fStmt ⟨some (Sum.inl 11), C.initVar, S⟩ =
        some ⟨none, C.initVar, Function.update S (Sum.inl 2) []⟩
      simp [FoldData.fStmt, h2]
    · intro k hk2 _; exact Function.update_of_ne hk2 _ _
  | cons b zs ih =>
    let S' : ∀ k : C.FK, List (C.fΓ k) := Function.update
      (Function.update S (Sum.inl 2) zs)
      (Sum.inl 0) (b :: S (Sum.inl 0))
    have hstep : C.fTM.step (C.mkCfg (some (Sum.inl 11)) C.initVar S) =
        some (C.mkCfg (some (Sum.inl 11)) C.initVar S') := by
      change TM2.step C.fStmt ⟨some (Sum.inl 11), C.initVar, S⟩ =
        some ⟨some (Sum.inl 11), C.initVar, S'⟩
      simp [FoldData.fStmt, h2, S']
    obtain ⟨S₁, heval, h12, h10, h1other⟩ := ih S' (by simp [S'])
    refine ⟨S₁, ?_, h12, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep]; exact heval
    · rw [h10, show S' (Sum.inl 0) = b :: S (Sum.inl 0) by simp [S'], List.reverse_cons,
        List.append_assoc, List.singleton_append]
    · intro k hk2 hk0
      rw [h1other k hk2 hk0]
      simp [S', Function.update_of_ne hk0, Function.update_of_ne hk2]

private lemma fold_one_iter (C : FoldData) (ps : Polynomial ℕ) (N M : ℕ)
    (A G rem B B' : List Bool)
    (hA : A.length ≤ N) (hG : G.length ≤ N) (hB : B.length ≤ M) (hB' : B'.length ≤ M)
    (hMs : TM2OutputsInTime C.tmS ((delimit (delimit A ++ B) ++ G).map C.inS.invFun)
      (some (B'.map C.outS.invFun)) (ps.eval (delimit (delimit A ++ B) ++ G).length)) :
    Nonempty (EvalsToInTime C.fTM.step
      (C.loopCfg A (delimit G ++ rem) B)
      (some (C.loopCfg A rem B'))
      (4 * N + 2 * M + 8 + ps.eval (5 * N + 2 * M + 3))) := by
  have hp3 : (flip bind C.fTM.step)^[1] (some (C.loopCfg A (delimit G ++ rem) B)) =
      some (C.mkCfg (some (Sum.inl 4)) C.initVar (C.loopStk A (delimit G ++ rem) B)) := by
    rw [Function.iterate_one, flip_bind_some]
    change TM2.step C.fStmt ⟨some (Sum.inl 3), C.initVar, _⟩ = _
    cases G <;> (simp [FoldData.fStmt, delimit, FoldData.loopStk]; rfl)
  obtain ⟨S₄, hp4, hS4_0, hS4_3, hS4_other⟩ :=
    fold_p4 C G rem (C.loopStk A (delimit G ++ rem) B) rfl
  simp only [FoldData.loopStk, List.append_nil] at hS4_3
  obtain ⟨S₅, hp5, hS5_3, hS5_ks0, hS5_other⟩ := fold_p5 C G.reverse S₄ hS4_3
  have hS4_ks0 : S₄ (Sum.inr (Sum.inr C.tmS.k₀)) = [] := by
    rw [hS4_other _ (by simp) (by simp)]; rfl
  rw [List.reverse_reverse, hS4_ks0, List.append_nil] at hS5_ks0
  have hS5_ks0' : S₅ (Sum.inr (Sum.inr C.tmS.k₀)) = (false :: G).map C.inS.invFun := by
    simpa only [List.map_cons] using hS5_ks0
  have hS5_2 : S₅ (Sum.inl 2) = B.reverse := by
    rw [hS5_other _ (by simp) (by simp), hS4_other _ (by simp) (by simp)]; rfl
  obtain ⟨S₆, hp6, hS6_2, hS6_ks0, hS6_other⟩ := fold_p6 C B.reverse (false :: G) S₅ hS5_2 hS5_ks0'
  rw [delimitRevAux_reverse] at hS6_ks0
  have hS6_1 : S₆ (Sum.inl 1) = A.reverse := by
    rw [hS6_other _ (by simp) (by simp), hS5_other _ (by simp) (by simp),
      hS4_other _ (by simp) (by simp)]; rfl
  obtain ⟨S₇, hp7, hS7_1, hS7_4, hS7_ks0, hS7_other⟩ :=
    fold_p7 C A.reverse (true :: false :: (delimit B ++ G)) S₆ hS6_1 hS6_ks0
  rw [delimit2RevAux_reverse] at hS7_ks0
  have hS6_4 : S₆ (Sum.inl 4) = [] := by
    rw [hS6_other _ (by simp) (by simp), hS5_other _ (by simp) (by simp),
      hS4_other _ (by simp) (by simp)]; rfl
  rw [List.reverse_reverse, hS6_4, List.append_nil] at hS7_4
  obtain ⟨S₈, hp8, hS8_4, hS8_1, hS8_other⟩ := fold_p8 C A S₇ hS7_4
  rw [hS7_1, List.append_nil] at hS8_1
  let inpS := delimit (delimit A ++ B) ++ G
  have hcfg8 : C.mkCfg (some (Sum.inr (Sum.inr C.tmS.main))) C.initVar S₈ =
      C.embedS (Sum.inl 9) none C.tmI.initialState S₈ (initList C.tmS (inpS.map C.inS.invFun)) := by
    dsimp [FoldData.embedS, FoldData.mkCfg, FoldData.initVar, initList]
    congr 1; funext k; rcases k with (_ | _ | ks)
    · rfl
    · rfl
    · by_cases hks0 : ks = C.tmS.k₀
      · subst hks0
        dsimp [FoldData.mergeS]
        rw [hS8_other _ (by simp) (by simp), hS7_ks0]
        simp [inpS]
      · simp only [FoldData.mergeS, hks0, ↓reduceDIte]
        rw [hS8_other _ (by simp) (by simp), hS7_other _ (by simp) (by simp) (by simp [hks0]),
          hS6_other _ (by simp) (by simp [hks0]), hS5_other _ (by simp) (by simp [hks0]),
          hS4_other _ (by simp) (by simp)]
        rfl
  have hpS := fold_sim_tmS C none C.tmI.initialState S₈ hMs.steps _ _ hMs.evals_in_steps
  let c9 := C.embedS (Sum.inl 9) none C.tmI.initialState S₈ (haltList C.tmS (B'.map C.outS.invFun))
  have hc9_eq : c9 = C.mkCfg (some (Sum.inl 9)) C.initVar c9.stk := rfl
  have hc9_ks1 : c9.stk (Sum.inr (Sum.inr C.tmS.k₁)) = B'.map C.outS.invFun := by
    dsimp [c9, FoldData.embedS]; simp [haltList]
  obtain ⟨S₉, hp9, hS9_ks1, hS9_2, hS9_other⟩ := fold_p9 C B' c9.stk hc9_ks1
  have hc9_2 : c9.stk (Sum.inl 2) = [] := by
    dsimp [c9, FoldData.embedS]
    rw [hS8_other _ (by simp) (by simp), hS7_other _ (by simp) (by simp) (by simp)]
    exact hS6_2
  rw [hc9_2, List.append_nil] at hS9_2
  have hcfg9 : C.mkCfg (some (Sum.inl 3)) C.initVar S₉ = C.loopCfg A rem B' := by
    dsimp [FoldData.loopCfg, FoldData.mkCfg]
    congr 1; funext k; rcases k with (i | ki | ks)
    · fin_cases i
      · simp only [FoldData.loopStk]
        rw [hS9_other _ (by simp) (by simp)]
        dsimp [c9, FoldData.embedS]
        rw [hS8_other _ (by simp) (by simp), hS7_other _ (by simp) (by simp) (by simp),
          hS6_other _ (by simp) (by simp), hS5_other _ (by simp) (by simp)]
        exact hS4_0
      · simp only [FoldData.loopStk]
        rw [hS9_other _ (by simp) (by simp)]
        dsimp [c9, FoldData.embedS]
        exact hS8_1
      · exact hS9_2
      · simp only [FoldData.loopStk]
        rw [hS9_other _ (by simp) (by simp)]
        dsimp [c9, FoldData.embedS]
        rw [hS8_other _ (by simp) (by simp), hS7_other _ (by simp) (by simp) (by simp),
          hS6_other _ (by simp) (by simp)]
        exact hS5_3
      · simp only [FoldData.loopStk]
        rw [hS9_other _ (by simp) (by simp)]
        dsimp [c9, FoldData.embedS]
        exact hS8_4
    · simp only [FoldData.loopStk]
      rw [hS9_other _ (by simp) (by simp)]
      dsimp [c9, FoldData.embedS]
      rw [hS8_other _ (by simp) (by simp), hS7_other _ (by simp) (by simp) (by simp),
        hS6_other _ (by simp) (by simp), hS5_other _ (by simp) (by simp),
        hS4_other _ (by simp) (by simp)]
      rfl
    · simp only [FoldData.loopStk]
      by_cases hks1 : ks = C.tmS.k₁
      · subst hks1; exact hS9_ks1
      · rw [hS9_other _ (by simp [hks1]) (by simp)]
        dsimp [c9, FoldData.embedS, haltList]
        simp [hks1]
  have hinpS_len : inpS.length ≤ 5 * N + 2 * M + 3 := by
    simp only [inpS, List.length_append, length_delimit]
    omega
  have hMs_le : hMs.steps ≤ ps.eval (5 * N + 2 * M + 3) :=
    le_trans hMs.steps_le_m (poly_eval_mono ps hinpS_len)
  let e34 := EvalsTo.trans C.fTM.step _ _ _ ⟨1, hp3⟩ ⟨G.length + 1, hp4⟩
  let e56 := EvalsTo.trans C.fTM.step _ _ _ ⟨G.reverse.length + 1, hp5⟩ ⟨B.reverse.length + 1, hp6⟩
  let e78 := EvalsTo.trans C.fTM.step _ _ _ ⟨A.reverse.length + 1, hp7⟩ ⟨A.length + 1, hp8⟩
  rw [← hcfg8] at hpS
  rw [← hc9_eq, hcfg9] at hp9
  let eS9 := EvalsTo.trans C.fTM.step _ _ _ ⟨hMs.steps, hpS⟩ ⟨B'.length + 1, hp9⟩
  let eAll := EvalsTo.trans C.fTM.step _ _ _
    (EvalsTo.trans C.fTM.step _ _ _ e34 e56)
    (EvalsTo.trans C.fTM.step _ _ _ e78 eS9)
  refine ⟨⟨eAll, ?_⟩⟩
  dsimp only [eAll, e34, e56, e78, eS9, EvalsTo.trans]
  simp only [List.length_reverse]
  omega

theorem isPolyTime_foldlCtx {α β γ : Type}
    [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    {init : α → β} {step : (α × β) × γ → β}
    (hinit : IsPolyTime init) (hstep : IsPolyTime step)
    (B : Polynomial ℕ)
    (hB : ∀ (a : α) (done rem : List γ),
      (bitEncode (done.foldl (fun b g => step ((a, b), g)) (init a))).length ≤
        B.eval (bitEncode (a, done ++ rem)).length) :
    IsPolyTime (fun p : α × List γ => p.2.foldl (fun b g => step ((p.1, b), g)) (init p.1)) := by
  rcases hinit with ⟨Mi⟩
  rcases hstep with ⟨Ms⟩
  let C : FoldData := {
    tmI := Mi.tm
    tmS := Ms.tm
    inI := Mi.inputAlphabet
    outI := Mi.outputAlphabet
    inS := Ms.inputAlphabet
    outS := Ms.outputAlphabet
  }
  let polySIn : Polynomial ℕ := Polynomial.C 5 * Polynomial.X + Polynomial.C 2 * B + Polynomial.C 3
  let polyIter : Polynomial ℕ :=
    Polynomial.C 4 * Polynomial.X + Polynomial.C 2 * B + Polynomial.C 8 + Ms.time.comp polySIn
  let totalTime : Polynomial ℕ :=
    Polynomial.C 3 * Polynomial.X + Polynomial.C 2 * B + Polynomial.C 6 +
      Mi.time + Polynomial.X * polyIter
  have hout : ∀ p : α × List γ, Nonempty (TM2OutputsInTime C.fTM
      (List.map (Equiv.refl Bool).invFun ((BitstringEncoding.toEncoding (α := α × List γ)).encode p))
      (some (List.map (Equiv.refl Bool).invFun
        ((BitstringEncoding.toEncoding (α := β)).encode
          (p.2.foldl (fun b g => step ((p.1, b), g)) (init p.1)))))
      (totalTime.eval ((BitstringEncoding.toEncoding (α := α × List γ)).encode p).length)) :=
    fun ⟨a, gs⟩ => by
      let A : List Bool := bitEncode a
      let GS : List Bool := bitEncode gs
      let N : ℕ := (delimit A ++ GS).length
      let M : ℕ := B.eval N
      let fStep := fun (b : β) (g : γ) => step ((a, b), g)
      let res : β := gs.foldl fStep (init a)
      change Nonempty (TM2OutputsInTime C.fTM (List.map (Equiv.refl Bool).invFun (delimit A ++ GS))
        (some (List.map (Equiv.refl Bool).invFun (bitEncode res))) (totalTime.eval N))
      simp only [Equiv.refl, List.map_id]
      have hA_le : A.length ≤ N := by simp only [N, List.length_append, length_delimit]; omega
      have hGS_le : GS.length ≤ N := by simp only [N, List.length_append]; omega
      have hgs_len : gs.length ≤ N := le_trans (list_length_le_bitEncode_length gs) hGS_le
      let c0 := initList C.fTM (delimit A ++ GS)
      have hc0_eq : c0 = C.mkCfg (some (Sum.inl 0)) C.initVar c0.stk := rfl
      have hc0_in : c0.stk (Sum.inl 0) = delimit A ++ GS := by simp [c0, FoldData.fTM, initList]
      have hc0_other : ∀ k : C.FK, k ≠ Sum.inl 0 → c0.stk k = [] := by
        intro k hk; simp [c0, FoldData.fTM, initList, hk]
      obtain ⟨S₁, hp0, hS1_0, hS1_1, hS1_4, hS1_other⟩ := fold_p0 C A GS c0.stk hc0_in
      rw [hc0_other (Sum.inl 1) (by simp), List.append_nil] at hS1_1
      rw [hc0_other (Sum.inl 4) (by simp), List.append_nil] at hS1_4
      obtain ⟨S₂, hp1, hS2_4, hS2_ki0, hS2_other⟩ := fold_p1 C A.reverse S₁ hS1_4
      have hS1_ki0 : S₁ (Sum.inr (Sum.inl C.tmI.k₀)) = [] := by
        rw [hS1_other _ (by simp) (by simp) (by simp)]; exact hc0_other _ (by simp)
      rw [List.reverse_reverse, hS1_ki0, List.append_nil] at hS2_ki0
      have hMi_out : TM2OutputsInTime C.tmI (A.map C.inI.invFun)
          (some ((bitEncode (init a)).map C.outI.invFun)) (Mi.time.eval A.length) :=
        Mi.outputsFun a
      have hMi_le : hMi_out.steps ≤ Mi.time.eval N :=
        le_trans hMi_out.steps_le_m (poly_eval_mono Mi.time hA_le)
      have hcfg2 : C.mkCfg (some (Sum.inr (Sum.inl C.tmI.main))) C.initVar S₂ =
          C.embedI (Sum.inl 2) none C.tmS.initialState S₂ (initList C.tmI (A.map C.inI.invFun)) := by
        dsimp [FoldData.embedI, FoldData.mkCfg, FoldData.initVar, initList]
        congr 1; funext k; rcases k with (_ | ki | _)
        · rfl
        · by_cases hki0 : ki = C.tmI.k₀
          · subst hki0; simp [hS2_ki0]
          · simp only [FoldData.mergeI, hki0, ↓reduceDIte]
            rw [hS2_other _ (by simp) (by simp [hki0]),
              hS1_other _ (by simp) (by simp) (by simp), hc0_other _ (by simp)]
        · rfl
      have hpI := fold_sim_tmI C none C.tmS.initialState S₂ hMi_out.steps _ _ hMi_out.evals_in_steps
      let B₀ := bitEncode (init a)
      let c2 := C.embedI (Sum.inl 2) none C.tmS.initialState S₂
        (haltList C.tmI (B₀.map C.outI.invFun))
      have hc2_eq : c2 = C.mkCfg (some (Sum.inl 2)) C.initVar c2.stk := rfl
      have hc2_ki1 : c2.stk (Sum.inr (Sum.inl C.tmI.k₁)) = B₀.map C.outI.invFun := by
        dsimp [c2, FoldData.embedI]; simp [haltList]
      obtain ⟨S₃, hp2, hS3_ki1, hS3_2, hS3_other⟩ := fold_p2 C B₀ c2.stk hc2_ki1
      have hc2_2 : c2.stk (Sum.inl 2) = [] := by
        dsimp [c2, FoldData.embedI]
        rw [hS2_other _ (by simp) (by simp), hS1_other _ (by simp) (by simp) (by simp),
          hc0_other _ (by simp)]
      rw [hc2_2, List.append_nil] at hS3_2
      have hcfg3 : C.mkCfg (some (Sum.inl 3)) C.initVar S₃ = C.loopCfg A GS B₀ := by
        dsimp [FoldData.loopCfg, FoldData.mkCfg]
        congr 1; funext k; rcases k with (i | ki | ks)
        · fin_cases i
          · simp only [FoldData.loopStk]
            rw [hS3_other _ (by simp) (by simp)]
            dsimp [c2, FoldData.embedI]
            rw [hS2_other _ (by simp) (by simp)]; exact hS1_0
          · simp only [FoldData.loopStk]
            rw [hS3_other _ (by simp) (by simp)]
            dsimp [c2, FoldData.embedI]
            rw [hS2_other _ (by simp) (by simp)]; exact hS1_1
          · exact hS3_2
          · simp only [FoldData.loopStk]
            rw [hS3_other _ (by simp) (by simp)]
            dsimp [c2, FoldData.embedI]
            rw [hS2_other _ (by simp) (by simp), hS1_other _ (by simp) (by simp) (by simp),
              hc0_other _ (by simp)]
          · simp only [FoldData.loopStk]
            rw [hS3_other _ (by simp) (by simp)]
            dsimp [c2, FoldData.embedI]; exact hS2_4
        · simp only [FoldData.loopStk]
          by_cases hki1 : ki = C.tmI.k₁
          · subst hki1; exact hS3_ki1
          · rw [hS3_other _ (by simp [hki1]) (by simp)]
            dsimp [c2, FoldData.embedI, haltList]; simp [hki1]
        · simp only [FoldData.loopStk]
          rw [hS3_other _ (by simp) (by simp)]
          dsimp [c2, FoldData.embedI]
          rw [hS2_other _ (by simp) (by simp), hS1_other _ (by simp) (by simp) (by simp),
            hc0_other _ (by simp)]
      have hB0_le : B₀.length ≤ M := by
        have h1 := hB a [] gs
        rw [List.nil_append, List.foldl_nil] at h1
        exact h1
      let stepBound := 4 * N + 2 * M + 8 + Ms.time.eval (5 * N + 2 * M + 3)
      have hLoop : ∀ (rem done : List γ), done ++ rem = gs →
          Nonempty (EvalsToInTime C.fTM.step
            (C.loopCfg A (bitEncode rem) (bitEncode (done.foldl fStep (init a))))
            (some (C.loopCfg A [] (bitEncode res)))
            (rem.length * stepBound)) := by
        intro rem
        induction rem with
        | nil =>
          intro done hdone
          rw [List.append_nil] at hdone
          subst hdone
          simp only [bitEncode_nil, List.length_nil, zero_mul]
          exact ⟨EvalsToInTime.refl _ _⟩
        | cons g rem' ih =>
          intro done hdone
          let acc := done.foldl fStep (init a)
          let acc' := (done ++ [g]).foldl fStep (init a)
          have hacc' : acc' = step ((a, acc), g) := by
            simp [acc', acc, fStep]
          have hG_mem : g ∈ gs := by
            rw [← hdone]; exact List.mem_append_right _ List.mem_cons_self
          have hG_le : (bitEncode g).length ≤ N :=
            le_trans (elem_bitEncode_le_list_bitEncode hG_mem) hGS_le
          have hB_cur : (bitEncode acc).length ≤ M := by
            have h1 := hB a done (g :: rem')
            rw [hdone] at h1; exact h1
          have hdone' : (done ++ [g]) ++ rem' = gs := by
            rw [List.append_assoc, List.singleton_append]; exact hdone
          have hB_nxt : (bitEncode acc').length ≤ M := by
            have h1 := hB a (done ++ [g]) rem'
            rw [hdone'] at h1; exact h1
          have hMs_g : TM2OutputsInTime C.tmS
              ((delimit (delimit A ++ bitEncode acc) ++ bitEncode g).map C.inS.invFun)
              (some ((bitEncode acc').map C.outS.invFun))
              (Ms.time.eval (delimit (delimit A ++ bitEncode acc) ++ bitEncode g).length) := by
            rw [hacc']
            exact Ms.outputsFun ((a, acc), g)
          obtain ⟨hone⟩ := fold_one_iter C Ms.time N M A (bitEncode g) (bitEncode rem')
            (bitEncode acc) (bitEncode acc') hA_le hG_le hB_cur hB_nxt hMs_g
          rw [bitEncode_cons]
          obtain ⟨hrest⟩ := ih (done ++ [g]) hdone'
          have hcomb := EvalsToInTime.trans C.fTM.step _ _ _ _ _ hone hrest
          refine ⟨evalsInTime_mono hcomb ?_⟩
          have hmul : (g :: rem').length * stepBound = rem'.length * stepBound + stepBound := by
            rw [List.length_cons]; ring
          rw [hmul]
      obtain ⟨hLoop0⟩ := hLoop gs [] (List.nil_append gs)
      let B_fin := bitEncode res
      have hBfin_le : B_fin.length ≤ M := by
        have h1 := hB a gs []
        rw [List.append_nil] at h1; exact h1
      have hpEnd0 : (flip bind C.fTM.step)^[1] (some (C.loopCfg A [] B_fin)) =
          some (C.mkCfg (some (Sum.inl 10)) C.initVar (C.loopStk A [] B_fin)) := by
        rw [Function.iterate_one, flip_bind_some]
        change TM2.step C.fStmt ⟨some (Sum.inl 3), C.initVar, _⟩ = _
        simp [FoldData.fStmt, FoldData.loopStk]; rfl
      obtain ⟨S₁₀, hp10, hS10_1, hS10_other⟩ := fold_p10 C A.reverse (C.loopStk A [] B_fin) rfl
      have hS10_2 : S₁₀ (Sum.inl 2) = B_fin.reverse := by
        rw [hS10_other _ (by simp)]; rfl
      obtain ⟨S₁₁, hp11, hS11_2, hS11_0, hS11_other⟩ := fold_p11 C B_fin.reverse S₁₀ hS10_2
      have hS10_0 : S₁₀ (Sum.inl 0) = [] := by
        rw [hS10_other _ (by simp)]; rfl
      rw [List.reverse_reverse, hS10_0, List.append_nil] at hS11_0
      have hhalt : C.mkCfg none C.initVar S₁₁ = haltList C.fTM B_fin := by
        dsimp [FoldData.mkCfg, FoldData.initVar, haltList, FoldData.fTM]
        congr 1; funext k; rcases k with (i | ki | ks)
        · fin_cases i <;> dsimp only
          · simp [hS11_0]
          · rw [hS11_other _ (by simp) (by simp)]; exact hS10_1
          · exact hS11_2
          · rw [hS11_other _ (by simp) (by simp), hS10_other _ (by simp)]; rfl
          · rw [hS11_other _ (by simp) (by simp), hS10_other _ (by simp)]; rfl
        · rw [hS11_other _ (by simp) (by simp), hS10_other _ (by simp)]; rfl
        · rw [hS11_other _ (by simp) (by simp), hS10_other _ (by simp)]; rfl
      rw [← hc0_eq] at hp0
      rw [← hcfg2] at hpI
      rw [← hc2_eq, hcfg3] at hp2
      rw [hhalt] at hp11
      let eInit0 := EvalsTo.trans C.fTM.step _ _ _ ⟨A.length + 1, hp0⟩ ⟨A.reverse.length + 1, hp1⟩
      let eInit1 := EvalsTo.trans C.fTM.step _ _ _ ⟨hMi_out.steps, hpI⟩ ⟨B₀.length + 1, hp2⟩
      let eInit : EvalsToInTime C.fTM.step c0 (some (C.loopCfg A GS B₀))
          (2 * N + M + 3 + Mi.time.eval N) :=
        ⟨EvalsTo.trans C.fTM.step _ _ _ eInit0 eInit1, by
          dsimp only [eInit0, eInit1, EvalsTo.trans]
          simp only [List.length_reverse]; omega⟩
      let eEnd0 := EvalsTo.trans C.fTM.step _ _ _ ⟨1, hpEnd0⟩ ⟨A.reverse.length + 1, hp10⟩
      let eEnd : EvalsToInTime C.fTM.step (C.loopCfg A [] B_fin) (some (haltList C.fTM B_fin))
          (N + M + 3) :=
        ⟨EvalsTo.trans C.fTM.step _ _ _ eEnd0 ⟨B_fin.reverse.length + 1, hp11⟩,
          by dsimp only [eEnd0, EvalsTo.trans]; simp only [List.length_reverse]; omega⟩
      let eAll := EvalsToInTime.trans C.fTM.step _ _ _ _ _
        (EvalsToInTime.trans C.fTM.step _ _ _ _ _ eInit hLoop0) eEnd
      refine ⟨evalsInTime_mono eAll ?_⟩
      have hLoopBound : gs.length * stepBound ≤ N * polyIter.eval N := by
        refine Nat.mul_le_mul hgs_len ?_
        simp only [stepBound, polyIter, polySIn, M, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp]
        omega
      simp only [totalTime, M, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      omega
  exact ⟨{
    tm := C.fTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := totalTime
    outputsFun := fun p => Classical.choice (hout p)
  }⟩

private lemma foldl_append_flatMap {γ δ : Type} (h : γ → List δ) (xs : List γ) (acc : List δ) :
    xs.foldl (fun b g => b ++ h g) acc = acc ++ xs.flatMap h := by
  induction xs generalizing acc with
  | nil => simp
  | cons g xs ih =>
    simp only [List.foldl_cons, List.flatMap_cons, ih, List.append_assoc]

theorem isPolyTime_flatMap {γ δ : Type} [BitstringEncoding γ] [BitstringEncoding δ]
    {h : γ → List δ} (hh : IsPolyTime h) :
    IsPolyTime (fun xs : List γ => xs.flatMap h) := by
  rcases hh with ⟨Mh⟩
  have hh' : IsPolyTime h := ⟨Mh⟩
  let Bh : ℕ := maxPushes Mh.tm
  let polyH : Polynomial ℕ := Polynomial.X + Mh.time * Polynomial.C Bh
  let B : Polynomial ℕ := Polynomial.X * polyH
  have hStep : IsPolyTime (fun p : (Bool × List δ) × γ => p.1.2 ++ h p.2) :=
    isPolyTime_comp
      (isPolyTime_pair
        (isPolyTime_comp isPolyTime_fst isPolyTime_snd)
        (isPolyTime_comp isPolyTime_snd hh'))
      isPolyTime_append
  have hFold : IsPolyTime
      (fun p : Bool × List γ => p.2.foldl (fun b g => b ++ h g) ([] : List δ)) := by
    refine isPolyTime_foldlCtx (isPolyTime_const []) hStep B ?_
    intro a done rem
    rw [foldl_append_flatMap, List.nil_append]
    let N := (bitEncode (a, done ++ rem)).length
    have hrem_le : (bitEncode (done ++ rem)).length ≤ N := by
      simp only [N, bitEncode_pair, List.length_append]; omega
    have hdone_len : done.length ≤ N := by
      have h1 := list_length_le_bitEncode_length (done ++ rem)
      rw [List.length_append] at h1; omega
    have helem : ∀ g ∈ done, (bitEncode (h g)).length ≤ polyH.eval N := by
      intro g hg
      have hg_mem : g ∈ done ++ rem := List.mem_append_left _ hg
      have hg_len : (bitEncode g).length ≤ N :=
        le_trans (elem_bitEncode_le_list_bitEncode hg_mem) hrem_le
      have hout := Mh.outputsFun g
      have h1 := evals_stk_length_le Mh.tm hout.steps _ _ hout.evals_in_steps Mh.tm.k₁
      rw [haltList_stk_k1, List.length_map] at h1
      have h0 := initList_stk_length_le Mh.tm
        ((bitEncode g).map Mh.inputAlphabet.invFun) Mh.tm.k₁
      rw [List.length_map] at h0
      have h2 : (bitEncode (h g)).length ≤ (bitEncode g).length + hout.steps * Bh :=
        le_trans h1 (Nat.add_le_add_right h0 _)
      have h3 : hout.steps ≤ Mh.time.eval N :=
        le_trans hout.steps_le_m (poly_eval_mono Mh.time hg_len)
      have h4 : hout.steps * Bh ≤ Mh.time.eval N * Bh := Nat.mul_le_mul_right Bh h3
      simp only [polyH, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul,
        Polynomial.eval_C]
      omega
    have hsum : ∀ sub : List γ, (∀ g ∈ sub, (bitEncode (h g)).length ≤ polyH.eval N) →
        (bitEncode (sub.flatMap h)).length ≤ sub.length * polyH.eval N := by
      intro sub hsub
      induction sub with
      | nil => simp [bitEncode_nil]
      | cons g sub ih =>
        rw [List.flatMap_cons, bitEncode_append, List.length_append, List.length_cons,
          Nat.succ_mul]
        have hg1 := hsub g List.mem_cons_self
        have hg2 := ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
        omega
    have hbound := hsum done helem
    have hmul : done.length * polyH.eval N ≤ N * polyH.eval N :=
      Nat.mul_le_mul_right _ hdone_len
    simp only [B, Polynomial.eval_mul, Polynomial.eval_X]
    exact le_trans hbound hmul
  have hPair : IsPolyTime (fun xs : List γ => (false, xs)) :=
    isPolyTime_pair (isPolyTime_const false) isPolyTime_id
  have hComp := isPolyTime_comp hPair hFold
  have heq : (fun xs : List γ => xs.foldl (fun b g => b ++ h g) []) = (fun xs => xs.flatMap h) := by
    funext xs; rw [foldl_append_flatMap, List.nil_append]
  exact heq ▸ hComp

theorem isPolyTime_map {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {g : α → β} (hg : IsPolyTime g) :
    IsPolyTime (fun xs : List α => xs.map g) := by
  have h1 : IsPolyTime (fun xs : List α => xs.flatMap (fun a => [g a])) :=
    isPolyTime_flatMap (isPolyTime_comp hg isPolyTime_singleton)
  have heq : (fun xs : List α => xs.flatMap (fun a => [g a])) = List.map g := by
    funext xs; induction xs with
    | nil => rfl
    | cons a xs ih => simp [ih]
  exact heq ▸ h1

theorem isPolyTime_filter {α : Type} [BitstringEncoding α]
    {p : α → Bool} (hp : IsPolyTime p) :
    IsPolyTime (fun xs : List α => xs.filter p) := by
  have h1 : IsPolyTime (fun xs : List α => xs.flatMap (fun a => if p a then [a] else [])) :=
    isPolyTime_flatMap (isPolyTime_ite hp isPolyTime_singleton (isPolyTime_const []))
  have heq : (fun xs : List α => xs.flatMap (fun a => if p a then [a] else [])) = List.filter p := by
    funext xs; induction xs with
    | nil => rfl
    | cons a xs ih =>
      simp only [List.flatMap_cons, List.filter_cons, ih]
      cases p a <;> simp
  exact heq ▸ h1

private lemma foldl_append_mapPair {α β : Type} (a : α) (xs : List β) (acc : List (α × β)) :
    xs.foldl (fun b g => b ++ [(a, g)]) acc = acc ++ xs.map (fun g => (a, g)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons g xs ih => simp only [List.foldl_cons, List.map_cons, ih, List.append_assoc,
      List.singleton_append]

theorem isPolyTime_distribRight {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    IsPolyTime (fun p : α × List β => p.2.map (fun b => (p.1, b))) := by
  let B : Polynomial ℕ :=
    Polynomial.X * (Polynomial.C 6 * Polynomial.X + Polynomial.C 3)
  have hStep : IsPolyTime (fun q : (α × List (α × β)) × β => q.1.2 ++ [(q.1.1, q.2)]) :=
    isPolyTime_comp
      (isPolyTime_pair
        (isPolyTime_comp isPolyTime_fst isPolyTime_snd)
        (isPolyTime_comp
          (isPolyTime_pair (isPolyTime_comp isPolyTime_fst isPolyTime_fst) isPolyTime_snd)
          isPolyTime_singleton))
      isPolyTime_append
  have hFold := isPolyTime_foldlCtx (isPolyTime_const ([] : List (α × β))) hStep B ?_
  · have heq : (fun p : α × List β => p.2.foldl (fun b g => b ++ [(p.1, g)]) []) =
        (fun p : α × List β => p.2.map (fun b => (p.1, b))) := by
      funext ⟨a, xs⟩; rw [foldl_append_mapPair, List.nil_append]
    exact heq ▸ hFold
  · intro a done rem
    rw [foldl_append_mapPair, List.nil_append]
    let N := (bitEncode (a, done ++ rem)).length
    have hA_le : (bitEncode a).length ≤ N := by
      simp only [N, bitEncode_pair, List.length_append, length_delimit]; omega
    have hrem_le : (bitEncode (done ++ rem)).length ≤ N := by
      simp only [N, bitEncode_pair, List.length_append]; omega
    have hdone_len : done.length ≤ N := by
      have h1 := list_length_le_bitEncode_length (done ++ rem)
      rw [List.length_append] at h1; omega
    have hsum : ∀ sub : List β, (∀ g ∈ sub, (bitEncode g).length ≤ N) →
        (bitEncode (sub.map (fun g => (a, g)))).length ≤ sub.length * (6 * N + 3) := by
      intro sub hsub
      induction sub with
      | nil => simp [bitEncode_nil]
      | cons g sub ih =>
        rw [List.map_cons, bitEncode_cons, List.length_append, length_delimit, bitEncode_pair,
          List.length_append, length_delimit]
        have hmul : (g :: sub).length * (6 * N + 3) = sub.length * (6 * N + 3) + (6 * N + 3) := by
          rw [List.length_cons]; ring
        rw [hmul]
        have hg1 := hsub g List.mem_cons_self
        have hg2 := ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
        omega
    have hbound := hsum done (fun g hg =>
      le_trans (elem_bitEncode_le_list_bitEncode (List.mem_append_left _ hg)) hrem_le)
    have hmul : done.length * (6 * N + 3) ≤ N * (6 * N + 3) :=
      Nat.mul_le_mul_right _ hdone_len
    simp only [B, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    exact le_trans hbound hmul

/- ### 6. Canonical little-endian binary encoding of `ℕ` and arithmetic combinators -/

private def ofBitsLE : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * ofBitsLE bs

private lemma getLast?_cons_nonempty {α : Type*} (a : α) {l : List α} (hl : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  cases l with
  | nil => contradiction
  | cons _ _ => rfl

private lemma getLast?_ne_nil {α : Type*} {l : List α} {x : α} (h : l.getLast? = some x) :
    l ≠ [] := by
  intro h0; subst h0; cases h

private lemma bitEncode_nat_eq (n : ℕ) : bitEncode n = encodeNat n := rfl

private lemma ofBitsLE_encodePosNum (p : PosNum) : ofBitsLE (encodePosNum p) = (p : ℕ) := by
  induction p with
  | one => rfl
  | bit0 q ih =>
    change 0 + 2 * ofBitsLE (encodePosNum q) = (q : ℕ) + (q : ℕ)
    omega
  | bit1 q ih =>
    change 1 + 2 * ofBitsLE (encodePosNum q) = (q : ℕ) + (q : ℕ) + 1
    omega

private lemma ofBitsLE_encodeNat (n : ℕ) : ofBitsLE (encodeNat n) = n := by
  unfold encodeNat
  have hm : ((n : Num) : ℕ) = n := Num.to_of_nat n
  cases h : (n : Num) with
  | zero =>
    rw [h] at hm
    simpa [encodeNum, ofBitsLE] using hm
  | pos p =>
    rw [h] at hm
    simpa [encodeNum, ofBitsLE_encodePosNum] using hm

private lemma encodePosNum_getLast (p : PosNum) : (encodePosNum p).getLast? = some true := by
  induction p with
  | one => rfl
  | bit0 q ih =>
    rw [encodePosNum, getLast?_cons_nonempty _ (encodePosNum_nonempty q)]
    exact ih
  | bit1 q ih =>
    rw [encodePosNum, getLast?_cons_nonempty _ (encodePosNum_nonempty q)]
    exact ih

private lemma encodeNat_canonical (n : ℕ) :
    encodeNat n = [] ∨ (encodeNat n).getLast? = some true := by
  unfold encodeNat
  cases (n : Num) with
  | zero => exact Or.inl rfl
  | pos p => exact Or.inr (encodePosNum_getLast p)

private lemma ofBitsLE_pos_of_getLast_true {bs : List Bool} (h : bs.getLast? = some true) :
    0 < ofBitsLE bs := by
  induction bs with
  | nil => cases h
  | cons b bs ih =>
    cases bs with
    | nil =>
      cases b
      · cases h
      · simp [ofBitsLE]
    | cons c cs =>
      have h1 := ih h
      rw [ofBitsLE]
      omega

private lemma tail_canonical {b : Bool} {bs : List Bool}
    (h : (b :: bs).getLast? = some true) : bs = [] ∨ bs.getLast? = some true := by
  cases bs with
  | nil => exact Or.inl rfl
  | cons c cs => exact Or.inr h

private lemma ofBitsLE_inj_canonical {xs ys : List Bool}
    (hx : xs = [] ∨ xs.getLast? = some true)
    (hy : ys = [] ∨ ys.getLast? = some true)
    (heq : ofBitsLE xs = ofBitsLE ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    rcases hy with rfl | hyl
    · rfl
    · exfalso
      have hpos := ofBitsLE_pos_of_getLast_true hyl
      change 0 = ofBitsLE ys at heq
      omega
  | cons a xs ih =>
    have hxl : (a :: xs).getLast? = some true := hx.resolve_left (List.cons_ne_nil _ _)
    rcases hy with rfl | hyl
    · exfalso
      have hpos := ofBitsLE_pos_of_getLast_true hxl
      change ofBitsLE (a :: xs) = 0 at heq
      omega
    · cases ys with
      | nil => cases hyl
      | cons b ys =>
        rw [ofBitsLE, ofBitsLE] at heq
        have hab : a = b := by cases a <;> cases b <;> simp at heq ⊢ <;> omega
        have hrest : ofBitsLE xs = ofBitsLE ys := by cases a <;> cases b <;> simp at heq <;> omega
        rw [hab, ih (tail_canonical hxl) (tail_canonical hyl) hrest]

private lemma encodeNat_eq_of_ofBitsLE {n : ℕ} {bs : List Bool}
    (hbs : bs = [] ∨ bs.getLast? = some true) (hval : ofBitsLE bs = n) :
    encodeNat n = bs :=
  ofBitsLE_inj_canonical (encodeNat_canonical n) hbs (by rw [ofBitsLE_encodeNat, hval])

private lemma encodeNat_zero : encodeNat 0 = [] := rfl

private lemma encodeNat_ne_nil_of_pos {n : ℕ} (hn : n ≠ 0) : encodeNat n ≠ [] := by
  intro h
  have h0 := ofBitsLE_encodeNat n
  rw [h, ofBitsLE] at h0
  exact hn h0.symm

private lemma ofBitsLE_lt_two_pow (bs : List Bool) : ofBitsLE bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [ofBitsLE]
  | cons b bs ih =>
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    simp only [ofBitsLE, List.length_cons, Nat.pow_succ]
    omega

private lemma two_pow_pred_le_of_getLast_true {bs : List Bool} (h : bs.getLast? = some true) :
    2 ^ (bs.length - 1) ≤ ofBitsLE bs := by
  induction bs with
  | nil => cases h
  | cons b bs ih =>
    cases bs with
    | nil =>
      cases b
      · cases h
      · simp [ofBitsLE]
    | cons c cs =>
      have h1 := ih h
      simp only [List.length_cons, Nat.add_sub_cancel, ofBitsLE] at h1 ⊢
      rw [Nat.pow_succ]
      omega

private lemma encodeNat_length_le_of_lt_two_pow (n m : ℕ) (h : n < 2 ^ m) :
    (encodeNat n).length ≤ m := by
  rcases encodeNat_canonical n with h0 | hlast
  · rw [h0]; simp
  · have h1 := two_pow_pred_le_of_getLast_true hlast
    rw [ofBitsLE_encodeNat] at h1
    have hne : (encodeNat n).length ≠ 0 :=
      List.length_pos_iff.mpr (getLast?_ne_nil hlast) |> Nat.ne_of_gt
    have hlt : (encodeNat n).length - 1 < m :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (lt_of_le_of_lt h1 h)
    omega

private lemma ofBitsLE_replicate_false_append (k : ℕ) (bs : List Bool) :
    ofBitsLE (List.replicate k false ++ bs) = 2 ^ k * ofBitsLE bs := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, ofBitsLE, Bool.toNat_false, zero_add, ih,
      Nat.pow_succ]
    ring

private lemma getLast?_append_of_ne_nil {α : Type*} (xs : List α) {ys : List α} (hys : ys ≠ []) :
    (xs ++ ys).getLast? = ys.getLast? := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.cons_append, getLast?_cons_nonempty _ (List.append_ne_nil_of_right_ne_nil xs hys), ih]

private lemma encodeNat_pos_decomp {n : ℕ} (hn : n ≠ 0) :
    encodeNat n = List.replicate (padicValNat 2 n) false ++ encodeNat (n.divMaxPow 2) ∧
      ∃ tail, encodeNat (n.divMaxPow 2) = true :: tail := by
  let v := padicValNat 2 n
  let u := n.divMaxPow 2
  have hfac : 2 ^ v * u = n := Nat.pow_padicValNat_mul_divMaxPow 2 n
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hfac; exact hn hfac.symm
  have hodd : ¬ 2 ∣ u := Nat.not_dvd_divMaxPow (by decide : 1 < 2) hn
  have hne : encodeNat u ≠ [] := encodeNat_ne_nil_of_pos hu0
  cases hEu : encodeNat u with
  | nil => exact absurd hEu hne
  | cons b tail =>
    have hb_val : b.toNat + 2 * ofBitsLE tail = u := by
      rw [← ofBitsLE, ← hEu, ofBitsLE_encodeNat]
    have hb_true : b = true := by
      cases b
      · exfalso; apply hodd; refine ⟨ofBitsLE tail, ?_⟩; simp at hb_val; omega
      · rfl
    subst hb_true
    have hulast : (true :: tail).getLast? = some true := by
      have h1 := (encodeNat_canonical u).resolve_left hne
      rwa [hEu] at h1
    refine ⟨?_, tail, rfl⟩
    apply encodeNat_eq_of_ofBitsLE
    · right
      rw [getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      exact hulast
    · rw [ofBitsLE_replicate_false_append, ofBitsLE, hb_val]
      exact hfac

private lemma encodeNat_divMaxPow2 (n : ℕ) :
    encodeNat (n.divMaxPow 2) = (encodeNat n).dropWhile (!·) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [encodeNat_zero]
  · obtain ⟨hdec, tail, htail⟩ := encodeNat_pos_decomp hn
    rw [hdec, htail]
    induction (padicValNat 2 n) with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ, List.cons_append]
      dsimp only [List.dropWhile]
      exact ih

private lemma encodeNat_ones (m : ℕ) : encodeNat (2 ^ m - 1) = List.replicate m true := by
  apply encodeNat_eq_of_ofBitsLE
  · cases m with
    | zero => exact Or.inl rfl
    | succ k =>
      right
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [List.replicate_succ, getLast?_cons_nonempty _ (by simp)]
        exact ih
  · induction m with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ, ofBitsLE, Bool.toNat_true, ih, Nat.pow_succ]
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
      omega

/- #### 6a. `isPolyTime_addNat` -/

private def addBits : Bool → List Bool → List Bool → List Bool
  | false, [], [] => []
  | true, [], [] => [true]
  | c, x :: xs, [] => xor x c :: addBits (x && c) xs []
  | c, [], y :: ys => xor y c :: addBits (y && c) [] ys
  | c, x :: xs, y :: ys =>
    xor (xor x y) c :: addBits ((x && y) || (x && c) || (y && c)) xs ys

private lemma ofBitsLE_addBits (c : Bool) (xs ys : List Bool) :
    ofBitsLE (addBits c xs ys) = c.toNat + ofBitsLE xs + ofBitsLE ys := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addBits, ofBitsLE]
    | cons y ys ihy =>
      simp only [addBits, ofBitsLE, ihy]
      cases c <;> cases y <;> (simp; try omega)
  | cons x xs ihx =>
    cases ys with
    | nil =>
      simp only [addBits, ofBitsLE, ihx]
      cases c <;> cases x <;> (simp; try omega)
    | cons y ys =>
      simp only [addBits, ofBitsLE, ihx]
      cases c <;> cases x <;> cases y <;> (simp; try omega)

private lemma addBits_getLast_true (c : Bool) (xs ys : List Bool)
    (hne : c = true ∨ xs ≠ [] ∨ ys ≠ [])
    (hx : xs = [] ∨ xs.getLast? = some true)
    (hy : ys = [] ∨ ys.getLast? = some true) :
    (addBits c xs ys).getLast? = some true := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil =>
      rcases hne with rfl | h | h
      · simp [addBits]
      · contradiction
      · contradiction
    | cons y ys ihy =>
      have hyl : (y :: ys).getLast? = some true := hy.resolve_left (List.cons_ne_nil _ _)
      cases ys with
      | nil =>
        have hy_true : y = true := by cases y; cases hyl; rfl
        subst hy_true
        cases c <;> simp [addBits]
      | cons y2 ys2 =>
        have hrec := ihy (y && c) (Or.inr (Or.inr (List.cons_ne_nil _ _))) (Or.inr hyl)
        rw [addBits, getLast?_cons_nonempty _ (getLast?_ne_nil hrec)]
        exact hrec
  | cons x xs ihx =>
    have hxl : (x :: xs).getLast? = some true := hx.resolve_left (List.cons_ne_nil _ _)
    cases ys with
    | nil =>
      cases xs with
      | nil =>
        have hx_true : x = true := by cases x; cases hxl; rfl
        subst hx_true
        cases c <;> simp [addBits]
      | cons x2 xs2 =>
        have hrec := ihx (x && c) [] (Or.inr (Or.inl (List.cons_ne_nil _ _)))
          (Or.inr hxl) (Or.inl rfl)
        rw [addBits, getLast?_cons_nonempty _ (getLast?_ne_nil hrec)]
        exact hrec
    | cons y ys =>
      have hyl : (y :: ys).getLast? = some true := hy.resolve_left (List.cons_ne_nil _ _)
      cases xs with
      | nil =>
        cases ys with
        | nil =>
          have hx_true : x = true := by cases x; cases hxl; rfl
          have hy_true : y = true := by cases y; cases hyl; rfl
          subst hx_true; subst hy_true
          cases c <;> simp [addBits]
        | cons y2 ys2 =>
          have hrec := ihx ((x && y) || (x && c) || (y && c)) (y2 :: ys2)
            (Or.inr (Or.inr (List.cons_ne_nil _ _))) (Or.inl rfl) (Or.inr hyl)
          rw [addBits, getLast?_cons_nonempty _ (getLast?_ne_nil hrec)]
          exact hrec
      | cons x2 xs2 =>
        have hrec := ihx ((x && y) || (x && c) || (y && c)) ys
          (Or.inr (Or.inl (List.cons_ne_nil _ _))) (Or.inr hxl) (tail_canonical hyl)
        rw [addBits, getLast?_cons_nonempty _ (getLast?_ne_nil hrec)]
        exact hrec

private lemma encodeNat_add (a b : ℕ) :
    encodeNat (a + b) = addBits false (encodeNat a) (encodeNat b) := by
  by_cases hab : a = 0 ∧ b = 0
  · rcases hab with ⟨rfl, rfl⟩; simp [encodeNat_zero, addBits]
  · have hne : false = true ∨ encodeNat a ≠ [] ∨ encodeNat b ≠ [] := by
      rcases eq_or_ne a 0 with rfl | ha
      · have hb : b ≠ 0 := fun hb => hab ⟨rfl, hb⟩
        exact Or.inr (Or.inr (encodeNat_ne_nil_of_pos hb))
      · exact Or.inr (Or.inl (encodeNat_ne_nil_of_pos ha))
    apply encodeNat_eq_of_ofBitsLE
    · exact Or.inr (addBits_getLast_true false _ _ hne
        (encodeNat_canonical a) (encodeNat_canonical b))
    · rw [ofBitsLE_addBits, Bool.toNat_false, zero_add, ofBitsLE_encodeNat, ofBitsLE_encodeNat]

private abbrev addNatTM : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin 4
  main := 0
  σ := Option Bool × Option Bool × Bool
  initialState := (none, none, false)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m
    | 0 =>
      .pop 0 (fun v o => (o, v.2.1, v.2.2))
        (.branch (fun v => v.1.getD false)
          (.pop 0 (fun v o => (o, v.2.1, v.2.2))
            (.push 1 (fun v => v.1.getD false)
              (.load (fun _ => (none, none, false)) (.goto (fun _ => 0)))))
          (.load (fun _ => (none, none, false)) (.goto (fun _ => 1))))
    | 1 =>
      .pop 1 (fun v o => (o, v.2.1, v.2.2))
        (.branch (fun v => v.1.isSome)
          (.push 2 (fun v => v.1.getD false)
            (.load (fun _ => (none, none, false)) (.goto (fun _ => 1))))
          (.goto (fun _ => 2)))
    | 2 =>
      .pop 2 (fun v ox => (ox, v.2.1, v.2.2))
        (.pop 0 (fun v oy => (v.1, oy, v.2.2))
          (.branch (fun v => v.1.isSome || v.2.1.isSome)
            (.push 1 (fun v => xor (xor (v.1.getD false) (v.2.1.getD false)) v.2.2)
              (.load (fun v =>
                let x := v.1.getD false
                let y := v.2.1.getD false
                let c := v.2.2
                (none, none, (x && y) || (x && c) || (y && c)))
                (.goto (fun _ => 2))))
            (.branch (fun v => v.2.2)
              (.push 1 (fun _ => true)
                (.load (fun _ => (none, none, false)) (.goto (fun _ => 3))))
              (.load (fun _ => (none, none, false)) (.goto (fun _ => 3))))))
    | 3 =>
      .pop 1 (fun v o => (o, v.2.1, v.2.2))
        (.branch (fun v => v.1.isSome)
          (.push 0 (fun v => v.1.getD false)
            (.load (fun _ => (none, none, false)) (.goto (fun _ => 3))))
          .halt)

private abbrev mkAddCfg (l : Option (Fin 4)) (c : Bool) (s0 s1 s2 : List Bool) : addNatTM.Cfg :=
  ⟨l, (none, none, c), fun i => if i = 0 then s0 else if i = 1 then s1 else s2⟩

private lemma add_p0 (xs rest acc : List Bool) :
    (flip bind addNatTM.step)^[xs.length + 1]
      (some (mkAddCfg (some 0) false (delimit xs ++ rest) acc [])) =
      some (mkAddCfg (some 1) false rest (xs.reverse ++ acc) []) := by
  induction xs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step addNatTM.m ⟨some 0, _, _⟩ = some ⟨some 1, _, _⟩
    simp only [addNatTM, delimit, List.singleton_append, TM2.step, TM2.stepAux, ↓reduceIte,
      List.head?_cons, Option.getD_some, Bool.cond_false, List.tail_cons, Option.some.injEq,
      TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b xs ih =>
    have hstep : addNatTM.step (mkAddCfg (some 0) false (delimit (b :: xs) ++ rest) acc []) =
        some (mkAddCfg (some 0) false (delimit xs ++ rest) (b :: acc) []) := by
      change TM2.step addNatTM.m ⟨some 0, _, _⟩ = some ⟨some 0, _, _⟩
      simp only [addNatTM, delimit, List.cons_append, TM2.step, TM2.stepAux, Function.update_self,
        ↓reduceIte, List.head?_cons, Option.getD_some, Bool.cond_true, List.tail_cons,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma add_p1 (zs s0 acc : List Bool) :
    (flip bind addNatTM.step)^[zs.length + 1] (some (mkAddCfg (some 1) false s0 zs acc)) =
      some (mkAddCfg (some 2) false s0 [] (zs.reverse ++ acc)) := by
  induction zs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step addNatTM.m ⟨some 1, _, _⟩ = some ⟨some 2, _, _⟩
    simp only [addNatTM, TM2.step, TM2.stepAux, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte,
      List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil, List.reverse_nil,
      List.nil_append, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b zs ih =>
    have hstep : addNatTM.step (mkAddCfg (some 1) false s0 (b :: zs) acc) =
        some (mkAddCfg (some 1) false s0 zs (b :: acc)) := by
      change TM2.step addNatTM.m ⟨some 1, _, _⟩ = some ⟨some 1, _, _⟩
      simp only [addNatTM, TM2.step, TM2.stepAux, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte,
        List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons, Option.getD_some,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma add_p2 (c : Bool) (xs ys acc : List Bool) :
    (flip bind addNatTM.step)^[max xs.length ys.length + 1]
      (some (mkAddCfg (some 2) c ys acc xs)) =
      some (mkAddCfg (some 3) false [] ((addBits c xs ys).reverse ++ acc) []) := by
  induction xs generalizing c ys acc with
  | nil =>
    induction ys generalizing c acc with
    | nil =>
      rw [List.length_nil, max_self, zero_add, Function.iterate_one, flip_bind_some]
      cases c <;>
        (change TM2.step addNatTM.m ⟨some 2, _, _⟩ = some ⟨some 3, _, _⟩
         simp [addNatTM, addBits, TM2.step, TM2.stepAux]
         funext i; fin_cases i <;> simp)
    | cons y ys ihy =>
      have hstep : addNatTM.step (mkAddCfg (some 2) c (y :: ys) acc []) =
          some (mkAddCfg (some 2) (y && c) ys (xor y c :: acc) []) := by
        change TM2.step addNatTM.m ⟨some 2, _, _⟩ = some ⟨some 2, _, _⟩
        simp [addNatTM, TM2.step, TM2.stepAux]
        funext i; fin_cases i <;> simp
      rw [List.length_nil, List.length_cons, Nat.zero_max, Function.iterate_succ_apply,
        flip_bind_some, hstep]
      have hrec := ihy (y && c) (xor y c :: acc)
      rw [List.length_nil, Nat.zero_max] at hrec
      rw [hrec, addBits, List.reverse_cons, List.append_assoc, List.singleton_append]
  | cons x xs ihx =>
    cases ys with
    | nil =>
      have hstep : addNatTM.step (mkAddCfg (some 2) c [] acc (x :: xs)) =
          some (mkAddCfg (some 2) (x && c) [] (xor x c :: acc) xs) := by
        change TM2.step addNatTM.m ⟨some 2, _, _⟩ = some ⟨some 2, _, _⟩
        simp [addNatTM, TM2.step, TM2.stepAux]
        funext i; fin_cases i <;> simp
      rw [List.length_cons, List.length_nil, Nat.max_zero, Function.iterate_succ_apply,
        flip_bind_some, hstep]
      have hrec := ihx (x && c) [] (xor x c :: acc)
      rw [List.length_nil, Nat.max_zero] at hrec
      rw [hrec, addBits, List.reverse_cons, List.append_assoc, List.singleton_append]
    | cons y ys =>
      have hstep : addNatTM.step (mkAddCfg (some 2) c (y :: ys) acc (x :: xs)) =
          some (mkAddCfg (some 2) ((x && y) || (x && c) || (y && c)) ys
            (xor (xor x y) c :: acc) xs) := by
        change TM2.step addNatTM.m ⟨some 2, _, _⟩ = some ⟨some 2, _, _⟩
        simp [addNatTM, TM2.step, TM2.stepAux]
        funext i; fin_cases i <;> simp
      rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply,
        flip_bind_some, hstep, ihx, addBits, List.reverse_cons, List.append_assoc,
        List.singleton_append]

private lemma add_p3 (zs acc : List Bool) :
    (flip bind addNatTM.step)^[zs.length + 1] (some (mkAddCfg (some 3) false acc zs [])) =
      some (mkAddCfg none false (zs.reverse ++ acc) [] []) := by
  induction zs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step addNatTM.m ⟨some 3, _, _⟩ = some ⟨none, _, _⟩
    simp only [addNatTM, TM2.step, TM2.stepAux, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte,
      List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil, List.reverse_nil,
      List.nil_append, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b zs ih =>
    have hstep : addNatTM.step (mkAddCfg (some 3) false acc (b :: zs) []) =
        some (mkAddCfg (some 3) false (b :: acc) zs []) := by
      change TM2.step addNatTM.m ⟨some 3, _, _⟩ = some ⟨some 3, _, _⟩
      simp only [addNatTM, TM2.step, TM2.stepAux, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte,
        List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons, Option.getD_some,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma addBits_length_le (c : Bool) (xs ys : List Bool) :
    (addBits c xs ys).length ≤ max xs.length ys.length + 1 := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addBits]
    | cons y ys ihy =>
      have h1 := ihy (y && c)
      simp only [addBits, List.length_nil, List.length_cons, Nat.zero_max] at h1 ⊢
      omega
  | cons x xs ihx =>
    cases ys with
    | nil =>
      have h1 := ihx (x && c) []
      simp only [addBits, List.length_cons, List.length_nil, Nat.max_zero] at h1 ⊢
      omega
    | cons y ys =>
      have h1 := ihx ((x && y) || (x && c) || (y && c)) ys
      simp only [addBits, List.length_cons, Nat.succ_max_succ]
      omega

theorem isPolyTime_addNat : IsPolyTime (fun p : ℕ × ℕ => p.1 + p.2) := by
  refine ⟨{
    tm := addNatTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 5
    outputsFun := fun ⟨a, b⟩ => ?_
  }⟩
  let A := encodeNat a
  let B := encodeNat b
  let S := addBits false A B
  change TM2OutputsInTime addNatTM (List.map (Equiv.refl Bool).invFun (delimit A ++ B))
    (some (List.map (Equiv.refl Bool).invFun (encodeNat (a + b))))
    ((Polynomial.C 4 * Polynomial.X + Polynomial.C 5).eval (delimit A ++ B).length)
  rw [encodeNat_add]
  simp only [Equiv.refl, List.map_id]
  have hinit : initList addNatTM (delimit A ++ B) = mkAddCfg (some 0) false (delimit A ++ B) [] [] := by
    dsimp [initList, mkAddCfg, addNatTM]; congr 1; funext i; fin_cases i <;> rfl
  have hhalt : mkAddCfg none false S [] [] = haltList addNatTM S := by
    dsimp [haltList, mkAddCfg, addNatTM]; congr 1; funext i; fin_cases i <;> rfl
  have hp0 := add_p0 A B []
  rw [List.append_nil, ← hinit] at hp0
  have hp1 := add_p1 A.reverse B []
  rw [List.reverse_reverse, List.append_nil] at hp1
  have hp2 := add_p2 false A B []
  rw [List.append_nil] at hp2
  have hp3 := add_p3 S.reverse []
  rw [List.reverse_reverse, List.append_nil, hhalt] at hp3
  let e01 := EvalsTo.trans addNatTM.step _ _ _
    ⟨A.length + 1, hp0⟩ ⟨A.reverse.length + 1, hp1⟩
  let e23 := EvalsTo.trans addNatTM.step _ _ _
    ⟨max A.length B.length + 1, hp2⟩ ⟨S.reverse.length + 1, hp3⟩
  let eAll := EvalsTo.trans addNatTM.step _ _ _ e01 e23
  refine ⟨eAll, ?_⟩
  dsimp only [eAll, e01, e23, EvalsTo.trans]
  have hSlen : S.length ≤ max A.length B.length + 1 := addBits_length_le false A B
  simp only [List.length_reverse, List.length_append, length_delimit, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

/- #### 6b. `bitsMSB` and `isPolyTime_mulNat` -/

private abbrev bitsMSBTM : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m _ :=
    .pop 0 (fun _ o => o)
      (.branch (fun v => v.isSome)
        (.push 1 (fun _ => false)
          (.push 1 (fun v => v.getD false)
            (.push 1 (fun _ => true)
              (.load (fun _ => none) (.goto (fun _ => ()))))))
        .halt)

private abbrev mkMSB (l : Option Unit) (s0 s1 : List Bool) : bitsMSBTM.Cfg :=
  ⟨l, none, fun i => if i = 0 then s0 else s1⟩

private lemma msb_eval (xs : List Bool) (acc : List Bool) :
    (flip bind bitsMSBTM.step)^[xs.length + 1] (some (mkMSB (some ()) xs acc)) =
      some (mkMSB none [] (bitEncode xs.reverse ++ acc)) := by
  induction xs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step bitsMSBTM.m ⟨some (), none, _⟩ = some ⟨none, none, _⟩
    simp only [bitsMSBTM, TM2.step, TM2.stepAux, ↓reduceIte, List.head?_nil, Option.isSome_none,
      Bool.cond_false, List.tail_nil, List.reverse_nil, bitEncode_nil, List.nil_append,
      Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b xs ih =>
    have hstep : bitsMSBTM.step (mkMSB (some ()) (b :: xs) acc) =
        some (mkMSB (some ()) xs ([true, b, false] ++ acc)) := by
      change TM2.step bitsMSBTM.m ⟨some (), none, _⟩ = some ⟨some (), none, _⟩
      simp only [bitsMSBTM, TM2.step, TM2.stepAux, ↓reduceIte, List.head?_cons, Option.isSome_some,
        Bool.cond_true, List.tail_cons, Option.getD_some, List.cons_append, List.nil_append,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, bitEncode_append, List.append_assoc, bitEncode_singleton]
    rfl

theorem isPolyTime_bitsMSB : IsPolyTime (fun n : ℕ => (encodeNat n).reverse) := by
  refine ⟨{
    tm := bitsMSBTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.X + Polynomial.C 1
    outputsFun := fun n => ?_
  }⟩
  let X := encodeNat n
  change TM2OutputsInTime bitsMSBTM (List.map (Equiv.refl Bool).invFun X)
    (some (List.map (Equiv.refl Bool).invFun (bitEncode X.reverse)))
    ((Polynomial.X + Polynomial.C 1).eval X.length)
  simp only [Equiv.refl, List.map_id]
  have hinit : initList bitsMSBTM X = mkMSB (some ()) X [] := rfl
  have hhalt : mkMSB none [] (bitEncode X.reverse) = haltList bitsMSBTM (bitEncode X.reverse) := by
    dsimp [haltList, mkMSB, bitsMSBTM]; congr 1; funext i; fin_cases i <;> rfl
  have hp := msb_eval X []
  rw [List.append_nil, hhalt] at hp
  refine ⟨⟨X.length + 1, by rw [hinit]; exact hp⟩, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  omega

private def ofBitsMSB (bs : List Bool) : ℕ :=
  bs.foldl (fun q bit => 2 * q + bit.toNat) 0

private lemma foldl_horner_mul (a : ℕ) (bs : List Bool) (q : ℕ) :
    bs.foldl (fun acc bit => (acc + acc) + (if bit then a else 0)) (a * q) =
      a * bs.foldl (fun r bit => 2 * r + bit.toNat) q := by
  induction bs generalizing q with
  | nil => rfl
  | cons bit bs ih =>
    simp only [List.foldl_cons]
    have hstep : (a * q + a * q) + (if bit then a else 0) = a * (2 * q + bit.toNat) := by
      cases bit <;> simp <;> ring
    rw [hstep, ih]

private lemma ofBitsMSB_reverse (bs : List Bool) : ofBitsMSB bs.reverse = ofBitsLE bs := by
  unfold ofBitsMSB
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, ofBitsLE]
    omega

private lemma ofBitsMSB_lt_two_pow (bs : List Bool) : ofBitsMSB bs < 2 ^ bs.length := by
  unfold ofBitsMSB
  have hgen : ∀ (xs : List Bool) (q : ℕ), q < 2 ^ 0 →
      xs.foldl (fun r bit => 2 * r + bit.toNat) q < 2 ^ xs.length := by
    intro xs
    have haux : ∀ (ys : List Bool) (k q : ℕ), q < 2 ^ k →
        ys.foldl (fun r bit => 2 * r + bit.toNat) q < 2 ^ (k + ys.length) := by
      intro ys
      induction ys with
      | nil => intro k q hq; simpa using hq
      | cons b ys ih =>
        intro k q hq
        simp only [List.foldl_cons, List.length_cons]
        have hb : b.toNat ≤ 1 := by cases b <;> decide
        have hq' : 2 * q + b.toNat < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
        have hrec := ih (k + 1) (2 * q + b.toNat) hq'
        have heq : k + 1 + ys.length = k + (ys.length + 1) := by omega
        rwa [heq] at hrec
    intro q hq
    simpa using haux xs 0 q hq
  exact hgen bs 0 (by decide)

theorem isPolyTime_mulNat : IsPolyTime (fun p : ℕ × ℕ => p.1 * p.2) := by
  have hAcc2 : IsPolyTime (fun q : (ℕ × ℕ) × Bool => q.1.2 + q.1.2) :=
    isPolyTime_comp
      (isPolyTime_pair
        (isPolyTime_comp isPolyTime_fst isPolyTime_snd)
        (isPolyTime_comp isPolyTime_fst isPolyTime_snd))
      isPolyTime_addNat
  have hAddA : IsPolyTime (fun q : (ℕ × ℕ) × Bool => if q.2 then q.1.1 else 0) :=
    isPolyTime_ite isPolyTime_snd
      (isPolyTime_comp isPolyTime_fst isPolyTime_fst)
      (isPolyTime_const 0)
  have hStep : IsPolyTime
      (fun q : (ℕ × ℕ) × Bool => (q.1.2 + q.1.2) + (if q.2 then q.1.1 else 0)) :=
    isPolyTime_comp (isPolyTime_pair hAcc2 hAddA) isPolyTime_addNat
  have hFold : IsPolyTime (fun p : ℕ × List Bool =>
      p.2.foldl (fun acc bit => (acc + acc) + (if bit then p.1 else 0)) 0) := by
    refine isPolyTime_foldlCtx (isPolyTime_const 0) hStep Polynomial.X ?_
    intro a done rem
    let N := (bitEncode (a, done ++ rem)).length
    have hval : done.foldl (fun acc bit => (acc + acc) + (if bit then a else 0)) 0 =
        a * ofBitsMSB done := by
      simpa [ofBitsMSB] using foldl_horner_mul a done 0
    rw [hval, bitEncode_nat_eq]
    apply encodeNat_length_le_of_lt_two_pow
    simp only [Polynomial.eval_X]
    have ha : a < 2 ^ (encodeNat a).length := by
      have h1 := ofBitsLE_lt_two_pow (encodeNat a)
      rwa [ofBitsLE_encodeNat] at h1
    have hd : ofBitsMSB done < 2 ^ done.length := ofBitsMSB_lt_two_pow done
    have hmul : a * ofBitsMSB done < 2 ^ ((encodeNat a).length + done.length) := by
      rw [Nat.pow_add]
      exact Nat.mul_lt_mul'' ha hd
    have hlen : (encodeNat a).length + done.length ≤ N := by
      have h1 := list_length_le_bitEncode_length (done ++ rem)
      rw [List.length_append] at h1
      simp only [N, bitEncode_pair, bitEncode_nat_eq, List.length_append, length_delimit]
      omega
    exact lt_of_lt_of_le hmul (Nat.pow_le_pow_right (by decide : 0 < 2) hlen)
  have hMSB2 := isPolyTime_comp (isPolyTime_snd (α := ℕ) (β := ℕ)) isPolyTime_bitsMSB
  have hPrep : IsPolyTime (fun p : ℕ × ℕ => (p.1, (encodeNat p.2).reverse)) :=
    isPolyTime_pair isPolyTime_fst hMSB2
  have hComp := isPolyTime_comp hPrep hFold
  have heq : (fun p : ℕ × ℕ =>
      ((encodeNat p.2).reverse).foldl (fun acc bit => (acc + acc) + (if bit then p.1 else 0)) 0) =
      (fun p : ℕ × ℕ => p.1 * p.2) := by
    funext ⟨a, b⟩
    have h1 := foldl_horner_mul a (encodeNat b).reverse 0
    rw [Nat.mul_zero] at h1
    rw [h1, show (encodeNat b).reverse.foldl (fun r bit => 2 * r + bit.toNat) 0 =
      ofBitsMSB (encodeNat b).reverse from rfl, ofBitsMSB_reverse, ofBitsLE_encodeNat]
  exact heq ▸ hComp

/- #### 6c. `isPolyTime_leNat`, `divMaxPow2`, `padicValNat 2`, and `modOneNat` -/

private def leBits : Bool → List Bool → List Bool → Bool
  | res, [], [] => res
  | res, x :: xs, [] => leBits (if x == false then res else false) xs []
  | res, [], y :: ys => leBits (if false == y then res else y) [] ys
  | res, x :: xs, y :: ys => leBits (if x == y then res else y) xs ys

private lemma leBits_spec (xs ys : List Bool) :
    leBits true xs ys = decide (ofBitsLE xs ≤ ofBitsLE ys) ∧
      leBits false xs ys = decide (ofBitsLE xs < ofBitsLE ys) := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [leBits, ofBitsLE]
    | cons y ys ihy =>
      obtain ⟨ht, hf⟩ := ihy
      cases y
      · rw [leBits, leBits]; change leBits true [] ys = _ ∧ leBits false [] ys = _; rw [ht, hf]
        dsimp only [ofBitsLE, Bool.toNat, cond]
        exact ⟨decide_eq_decide.mpr (by omega), decide_eq_decide.mpr (by omega)⟩
      · rw [leBits, leBits]; change leBits true [] ys = _ ∧ leBits true [] ys = _; rw [ht]
        dsimp only [ofBitsLE, Bool.toNat, cond]
        exact ⟨decide_eq_decide.mpr (by omega), decide_eq_decide.mpr (by omega)⟩
  | cons x xs ihx =>
    cases ys with
    | nil =>
      obtain ⟨ht, hf⟩ := ihx []
      cases x
      · rw [leBits, leBits]; change leBits true xs [] = _ ∧ leBits false xs [] = _; rw [ht, hf]
        dsimp only [ofBitsLE, Bool.toNat, cond]
        exact ⟨decide_eq_decide.mpr (by omega), decide_eq_decide.mpr (by omega)⟩
      · rw [leBits, leBits]; change leBits false xs [] = _ ∧ leBits false xs [] = _; rw [hf]
        dsimp only [ofBitsLE, Bool.toNat, cond]
        exact ⟨decide_eq_decide.mpr (by omega), decide_eq_decide.mpr (by omega)⟩
    | cons y ys =>
      obtain ⟨ht, hf⟩ := ihx ys
      cases x <;> cases y
      · rw [leBits, leBits]; change leBits true xs ys = _ ∧ leBits false xs ys = _; rw [ht, hf]
        dsimp only [ofBitsLE, Bool.toNat, cond]
        exact ⟨decide_eq_decide.mpr (by omega), decide_eq_decide.mpr (by omega)⟩
      · rw [leBits, leBits]; change leBits true xs ys = _ ∧ leBits true xs ys = _; rw [ht]
        dsimp only [ofBitsLE, Bool.toNat, cond]
        exact ⟨decide_eq_decide.mpr (by omega), decide_eq_decide.mpr (by omega)⟩
      · rw [leBits, leBits]; change leBits false xs ys = _ ∧ leBits false xs ys = _; rw [hf]
        dsimp only [ofBitsLE, Bool.toNat, cond]
        exact ⟨decide_eq_decide.mpr (by omega), decide_eq_decide.mpr (by omega)⟩
      · rw [leBits, leBits]; change leBits true xs ys = _ ∧ leBits false xs ys = _; rw [ht, hf]
        dsimp only [ofBitsLE, Bool.toNat, cond]
        exact ⟨decide_eq_decide.mpr (by omega), decide_eq_decide.mpr (by omega)⟩

private abbrev leNatTM : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Option Bool × Option Bool × Bool
  initialState := (none, none, true)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m
    | 0 =>
      .pop 0 (fun v o => (o, v.2.1, v.2.2))
        (.branch (fun v => v.1.getD false)
          (.pop 0 (fun v o => (o, v.2.1, v.2.2))
            (.push 1 (fun v => v.1.getD false)
              (.load (fun _ => (none, none, true)) (.goto (fun _ => 0)))))
          (.load (fun _ => (none, none, true)) (.goto (fun _ => 1))))
    | 1 =>
      .pop 1 (fun v o => (o, v.2.1, v.2.2))
        (.branch (fun v => v.1.isSome)
          (.push 2 (fun v => v.1.getD false)
            (.load (fun _ => (none, none, true)) (.goto (fun _ => 1))))
          (.goto (fun _ => 2)))
    | 2 =>
      .pop 2 (fun v ox => (ox, v.2.1, v.2.2))
        (.pop 0 (fun v oy => (v.1, oy, v.2.2))
          (.branch (fun v => v.1.isSome || v.2.1.isSome)
            (.load (fun v =>
              let x := v.1.getD false
              let y := v.2.1.getD false
              (none, none, if x == y then v.2.2 else y))
              (.goto (fun _ => 2)))
            (.push 0 (fun v => v.2.2)
              (.load (fun _ => (none, none, true)) .halt))))

private abbrev mkLeCfg (l : Option (Fin 3)) (res : Bool) (s0 s1 s2 : List Bool) : leNatTM.Cfg :=
  ⟨l, (none, none, res), fun i => if i = 0 then s0 else if i = 1 then s1 else s2⟩

private lemma le_p0 (xs rest acc : List Bool) :
    (flip bind leNatTM.step)^[xs.length + 1]
      (some (mkLeCfg (some 0) true (delimit xs ++ rest) acc [])) =
      some (mkLeCfg (some 1) true rest (xs.reverse ++ acc) []) := by
  induction xs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step leNatTM.m ⟨some 0, _, _⟩ = some ⟨some 1, _, _⟩
    simp only [leNatTM, delimit, List.singleton_append, TM2.step, TM2.stepAux, ↓reduceIte,
      List.head?_cons, Option.getD_some, Bool.cond_false, List.tail_cons, Option.some.injEq,
      TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b xs ih =>
    have hstep : leNatTM.step (mkLeCfg (some 0) true (delimit (b :: xs) ++ rest) acc []) =
        some (mkLeCfg (some 0) true (delimit xs ++ rest) (b :: acc) []) := by
      change TM2.step leNatTM.m ⟨some 0, _, _⟩ = some ⟨some 0, _, _⟩
      simp only [leNatTM, delimit, List.cons_append, TM2.step, TM2.stepAux, Function.update_self,
        ↓reduceIte, List.head?_cons, Option.getD_some, Bool.cond_true, List.tail_cons,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma le_p1 (zs s0 acc : List Bool) :
    (flip bind leNatTM.step)^[zs.length + 1] (some (mkLeCfg (some 1) true s0 zs acc)) =
      some (mkLeCfg (some 2) true s0 [] (zs.reverse ++ acc)) := by
  induction zs generalizing acc with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step leNatTM.m ⟨some 1, _, _⟩ = some ⟨some 2, _, _⟩
    simp only [leNatTM, TM2.step, TM2.stepAux, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte,
      List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil, List.reverse_nil,
      List.nil_append, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b zs ih =>
    have hstep : leNatTM.step (mkLeCfg (some 1) true s0 (b :: zs) acc) =
        some (mkLeCfg (some 1) true s0 zs (b :: acc)) := by
      change TM2.step leNatTM.m ⟨some 1, _, _⟩ = some ⟨some 1, _, _⟩
      simp only [leNatTM, TM2.step, TM2.stepAux, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte,
        List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons, Option.getD_some,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma le_p2 (res : Bool) (xs ys : List Bool) :
    (flip bind leNatTM.step)^[max xs.length ys.length + 1]
      (some (mkLeCfg (some 2) res ys [] xs)) =
      some (mkLeCfg none true [leBits res xs ys] [] []) := by
  induction xs generalizing res ys with
  | nil =>
    induction ys generalizing res with
    | nil =>
      rw [List.length_nil, max_self, zero_add, Function.iterate_one, flip_bind_some]
      change TM2.step leNatTM.m ⟨some 2, _, _⟩ = some ⟨none, _, _⟩
      simp [leNatTM, leBits, TM2.step, TM2.stepAux]
      funext i; fin_cases i <;> simp
    | cons y ys ihy =>
      have hstep : leNatTM.step (mkLeCfg (some 2) res (y :: ys) [] []) =
          some (mkLeCfg (some 2) (if false == y then res else y) ys [] []) := by
        change TM2.step leNatTM.m ⟨some 2, _, _⟩ = some ⟨some 2, _, _⟩
        simp [leNatTM, TM2.step, TM2.stepAux]
        funext i; fin_cases i <;> simp
      rw [List.length_nil, List.length_cons, Nat.zero_max, Function.iterate_succ_apply,
        flip_bind_some, hstep]
      have hrec := ihy (if false == y then res else y)
      rw [List.length_nil, Nat.zero_max] at hrec
      rw [hrec, leBits]
  | cons x xs ihx =>
    cases ys with
    | nil =>
      have hstep : leNatTM.step (mkLeCfg (some 2) res [] [] (x :: xs)) =
          some (mkLeCfg (some 2) (if x == false then res else false) [] [] xs) := by
        change TM2.step leNatTM.m ⟨some 2, _, _⟩ = some ⟨some 2, _, _⟩
        simp [leNatTM, TM2.step, TM2.stepAux]
        funext i; fin_cases i <;> simp
      rw [List.length_cons, List.length_nil, Nat.max_zero, Function.iterate_succ_apply,
        flip_bind_some, hstep]
      have hrec := ihx (if x == false then res else false) []
      rw [List.length_nil, Nat.max_zero] at hrec
      rw [hrec, leBits]
    | cons y ys =>
      have hstep : leNatTM.step (mkLeCfg (some 2) res (y :: ys) [] (x :: xs)) =
          some (mkLeCfg (some 2) (if x == y then res else y) ys [] xs) := by
        change TM2.step leNatTM.m ⟨some 2, _, _⟩ = some ⟨some 2, _, _⟩
        simp [leNatTM, TM2.step, TM2.stepAux]
        funext i; fin_cases i <;> simp
      rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply,
        flip_bind_some, hstep, ihx, leBits]

theorem isPolyTime_leNat : IsPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
  refine ⟨{
    tm := leNatTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.C 3 * Polynomial.X + Polynomial.C 3
    outputsFun := fun ⟨a, b⟩ => ?_
  }⟩
  let A := encodeNat a
  let B := encodeNat b
  change TM2OutputsInTime leNatTM (List.map (Equiv.refl Bool).invFun (delimit A ++ B))
    (some (List.map (Equiv.refl Bool).invFun [decide (a ≤ b)]))
    ((Polynomial.C 3 * Polynomial.X + Polynomial.C 3).eval (delimit A ++ B).length)
  simp only [Equiv.refl, List.map_id]
  have hspec : leBits true A B = decide (a ≤ b) := by
    rw [(leBits_spec A B).1, ofBitsLE_encodeNat, ofBitsLE_encodeNat]
  rw [← hspec]
  have hinit : initList leNatTM (delimit A ++ B) = mkLeCfg (some 0) true (delimit A ++ B) [] [] := by
    dsimp [initList, mkLeCfg, leNatTM]; congr 1; funext i; fin_cases i <;> rfl
  have hhalt : mkLeCfg none true [leBits true A B] [] [] = haltList leNatTM [leBits true A B] := by
    dsimp [haltList, mkLeCfg, leNatTM]; congr 1; funext i; fin_cases i <;> rfl
  have hp0 := le_p0 A B []
  rw [List.append_nil, ← hinit] at hp0
  have hp1 := le_p1 A.reverse B []
  rw [List.reverse_reverse, List.append_nil] at hp1
  have hp2 := le_p2 true A B
  rw [hhalt] at hp2
  let e01 := EvalsTo.trans leNatTM.step _ _ _ ⟨A.length + 1, hp0⟩ ⟨A.reverse.length + 1, hp1⟩
  let eAll := EvalsTo.trans leNatTM.step _ _ _ e01 ⟨max A.length B.length + 1, hp2⟩
  refine ⟨eAll, ?_⟩
  dsimp only [eAll, e01, EvalsTo.trans]
  simp only [List.length_reverse, List.length_append, length_delimit, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

/- #### 6d. `listSum`, `listLength`, unary `pow2`, and binary-search `Nat.sqrt` -/

private lemma foldl_add_eq_sum (xs : List ℕ) (acc : ℕ) :
    xs.foldl (· + ·) acc = acc + xs.sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.sum_cons, ih]
    omega

theorem isPolyTime_listSum : IsPolyTime (fun xs : List ℕ => xs.sum) := by
  let B : Polynomial ℕ := Polynomial.C 2 * Polynomial.X
  have hStep : IsPolyTime (fun q : (Bool × ℕ) × ℕ => q.1.2 + q.2) :=
    isPolyTime_comp
      (isPolyTime_pair (isPolyTime_comp isPolyTime_fst isPolyTime_snd) isPolyTime_snd)
      isPolyTime_addNat
  have hFold : IsPolyTime (fun p : Bool × List ℕ => p.2.foldl (· + ·) 0) := by
    refine isPolyTime_foldlCtx (isPolyTime_const 0) hStep B ?_
    intro a done rem
    rw [foldl_add_eq_sum, zero_add, bitEncode_nat_eq]
    let N := (bitEncode (a, done ++ rem)).length
    apply encodeNat_length_le_of_lt_two_pow
    simp only [B, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have hrem_le : (bitEncode (done ++ rem)).length ≤ N := by
      simp only [N, bitEncode_pair, List.length_append]; omega
    have hdone_len : done.length ≤ N := by
      have h1 := list_length_le_bitEncode_length (done ++ rem)
      rw [List.length_append] at h1; omega
    have hsum_le : ∀ sub : List ℕ, (∀ g ∈ sub, g < 2 ^ N) → sub.sum ≤ sub.length * 2 ^ N := by
      intro sub hsub
      induction sub with
      | nil => simp
      | cons g sub ih =>
        rw [List.sum_cons, List.length_cons, Nat.succ_mul]
        have hg1 := hsub g List.mem_cons_self
        have hg2 := ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
        omega
    have helem : ∀ g ∈ done, g < 2 ^ N := by
      intro g hg
      have hg_len : (encodeNat g).length ≤ N :=
        le_trans (elem_bitEncode_le_list_bitEncode (List.mem_append_left _ hg)) hrem_le
      have hg_lt := ofBitsLE_lt_two_pow (encodeNat g)
      rw [ofBitsLE_encodeNat] at hg_lt
      exact lt_of_lt_of_le hg_lt (Nat.pow_le_pow_right (by decide : 0 < 2) hg_len)
    have h1 : done.sum ≤ done.length * 2 ^ N := hsum_le done helem
    have h2 : done.length < 2 ^ N := lt_of_le_of_lt hdone_len Nat.lt_two_pow_self
    have h3 : done.length * 2 ^ N < 2 ^ N * 2 ^ N :=
      Nat.mul_lt_mul_of_pos_right h2 (Nat.pow_pos (by decide : 0 < 2))
    rw [show 2 * N = N + N by omega, Nat.pow_add]
    exact lt_of_le_of_lt h1 h3
  have hPair : IsPolyTime (fun xs : List ℕ => (false, xs)) :=
    isPolyTime_pair (isPolyTime_const false) isPolyTime_id
  have hComp := isPolyTime_comp hPair hFold
  have heq : (fun xs : List ℕ => xs.foldl (· + ·) 0) = List.sum := by
    funext xs; rw [foldl_add_eq_sum, zero_add]
  exact heq ▸ hComp

theorem isPolyTime_listLength {α : Type} [BitstringEncoding α] :
    IsPolyTime (fun xs : List α => xs.length) := by
  have h1 : IsPolyTime (fun xs : List α => (xs.map (fun _ => (1 : ℕ))).sum) :=
    isPolyTime_comp (isPolyTime_map (isPolyTime_const (1 : ℕ))) isPolyTime_listSum
  have heq : (fun xs : List α => (xs.map (fun _ => (1 : ℕ))).sum) = List.length := by
    funext xs
    induction xs with
    | nil => rfl
    | cons _ xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
  exact heq ▸ h1

private def unaryBlocks : ℕ → List Bool
  | 0 => []
  | m + 1 => true :: true :: false :: unaryBlocks m

private lemma bitEncode_replicate_true (m : ℕ) :
    bitEncode (List.replicate m true) = unaryBlocks m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, bitEncode_cons, ih]
    rfl

private abbrev unarySuccTM : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m _ :=
    .pop 0 (fun _ o => o)
      (.branch (fun v => v.isSome)
        (.push 1 (fun _ => false)
          (.push 1 (fun _ => true)
            (.push 1 (fun _ => true)
              (.load (fun _ => none) (.goto (fun _ => ()))))))
        (.push 1 (fun _ => false)
          (.push 1 (fun _ => true)
            (.push 1 (fun _ => true)
              (.load (fun _ => none) .halt)))))

private abbrev mkUSCfg (l : Option Unit) (s0 s1 : List Bool) : unarySuccTM.Cfg :=
  ⟨l, none, fun i => if i = 0 then s0 else s1⟩

private lemma unarySucc_eval (xs : List Bool) (k : ℕ) :
    (flip bind unarySuccTM.step)^[xs.length + 1] (some (mkUSCfg (some ()) xs (unaryBlocks k))) =
      some (mkUSCfg none [] (unaryBlocks (xs.length + 1 + k))) := by
  induction xs generalizing k with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step unarySuccTM.m ⟨some (), none, _⟩ = some ⟨none, none, _⟩
    simp only [unarySuccTM, TM2.step, TM2.stepAux, ↓reduceIte, List.head?_nil, Option.isSome_none,
      Bool.cond_false, List.tail_nil, Nat.add_comm 1 k, unaryBlocks, Option.some.injEq,
      TM2.Cfg.mk.injEq, true_and]
    funext i; fin_cases i <;> simp
  | cons b xs ih =>
    have hstep : unarySuccTM.step (mkUSCfg (some ()) (b :: xs) (unaryBlocks k)) =
        some (mkUSCfg (some ()) xs (unaryBlocks (k + 1))) := by
      change TM2.step unarySuccTM.m ⟨some (), none, _⟩ = some ⟨some (), none, _⟩
      simp only [unarySuccTM, TM2.step, TM2.stepAux, ↓reduceIte, List.head?_cons,
        Option.isSome_some, Bool.cond_true, List.tail_cons, unaryBlocks, Option.some.injEq,
        TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih (k + 1)]
    have heq : xs.length + 1 + (k + 1) = xs.length + 1 + 1 + k := by omega
    rw [heq]

theorem isPolyTime_unaryBitLenSucc {α : Type} [BitstringEncoding α] :
    IsPolyTime (fun x : α => List.replicate ((bitEncode x).length + 1) true) := by
  refine ⟨{
    tm := unarySuccTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.X + Polynomial.C 1
    outputsFun := fun x => ?_
  }⟩
  let L := bitEncode x
  change TM2OutputsInTime unarySuccTM (List.map (Equiv.refl Bool).invFun L)
    (some (List.map (Equiv.refl Bool).invFun (bitEncode (List.replicate (L.length + 1) true))))
    ((Polynomial.X + Polynomial.C 1).eval L.length)
  rw [bitEncode_replicate_true]
  simp only [Equiv.refl, List.map_id]
  have hinit : initList unarySuccTM L = mkUSCfg (some ()) L (unaryBlocks 0) := rfl
  have hhalt : mkUSCfg none [] (unaryBlocks (L.length + 1)) =
      haltList unarySuccTM (unaryBlocks (L.length + 1)) := by
    dsimp [haltList, mkUSCfg, unarySuccTM]; congr 1; funext i; fin_cases i <;> rfl
  have hp := unarySucc_eval L 0
  rw [Nat.add_zero, ← hinit, hhalt] at hp
  refine ⟨⟨L.length + 1, hp⟩, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  omega

private lemma encodeNat_two_pow (m : ℕ) :
    encodeNat (2 ^ m) = List.replicate m false ++ [true] := by
  apply encodeNat_eq_of_ofBitsLE
  · right
    rw [getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    rfl
  · rw [ofBitsLE_replicate_false_append, ofBitsLE, ofBitsLE, Bool.toNat_true, mul_zero, add_zero,
      mul_one]

private abbrev pow2LenTM : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 2
  main := 0
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m
    | 0 => .push 1 (fun _ => true) (.goto (fun _ => 1))
    | 1 =>
      .pop 0 (fun _ o => o)
        (.branch (fun v => v.isSome)
          (.pop 0 (fun _ _ => none)
            (.pop 0 (fun _ _ => none)
              (.push 1 (fun _ => false) (.goto (fun _ => 1)))))
          .halt)

private abbrev mkPow2Cfg (l : Option (Fin 2)) (s0 s1 : List Bool) : pow2LenTM.Cfg :=
  ⟨l, none, fun i => if i = 0 then s0 else s1⟩

private lemma pow2Len_p1 (us : List Bool) (k : ℕ) :
    (flip bind pow2LenTM.step)^[us.length + 1]
      (some (mkPow2Cfg (some 1) (bitEncode us) (List.replicate k false ++ [true]))) =
      some (mkPow2Cfg none [] (List.replicate (us.length + k) false ++ [true])) := by
  induction us generalizing k with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one, flip_bind_some]
    change TM2.step pow2LenTM.m ⟨some 1, none, _⟩ = some ⟨none, none, _⟩
    simp only [pow2LenTM, bitEncode_nil, TM2.step, TM2.stepAux, ↓reduceIte, List.head?_nil,
      Option.isSome_none, Bool.cond_false, List.tail_nil, Option.some.injEq, TM2.Cfg.mk.injEq,
      true_and]
    funext i; fin_cases i <;> simp
  | cons b us ih =>
    have hstep : pow2LenTM.step
        (mkPow2Cfg (some 1) (bitEncode (b :: us)) (List.replicate k false ++ [true])) =
        some (mkPow2Cfg (some 1) (bitEncode us) (List.replicate (k + 1) false ++ [true])) := by
      change TM2.step pow2LenTM.m ⟨some 1, none, _⟩ = some ⟨some 1, none, _⟩
      have hcons : bitEncode (b :: us) = true :: b :: false :: bitEncode us := rfl
      rw [hcons]
      simp only [pow2LenTM, TM2.step, TM2.stepAux, Function.update_self, ↓reduceIte,
        List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons, List.replicate_succ,
        List.cons_append, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      funext i; fin_cases i <;> simp
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, hstep, ih (k + 1)]
    have heq : us.length + (k + 1) = us.length + 1 + k := by omega
    rw [heq]

theorem isPolyTime_pow2Len : IsPolyTime (fun us : List Bool => 2 ^ us.length) := by
  refine ⟨{
    tm := pow2LenTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.X + Polynomial.C 2
    outputsFun := fun us => ?_
  }⟩
  let U := bitEncode us
  change TM2OutputsInTime pow2LenTM (List.map (Equiv.refl Bool).invFun U)
    (some (List.map (Equiv.refl Bool).invFun (encodeNat (2 ^ us.length))))
    ((Polynomial.X + Polynomial.C 2).eval U.length)
  rw [encodeNat_two_pow]
  simp only [Equiv.refl, List.map_id]
  have hp0 : (flip bind pow2LenTM.step)^[1] (some (initList pow2LenTM U)) =
      some (mkPow2Cfg (some 1) U (List.replicate 0 false ++ [true])) := by
    rw [Function.iterate_one, flip_bind_some]
    change TM2.step pow2LenTM.m (initList pow2LenTM U) = _
    simp [pow2LenTM, initList, TM2.step, TM2.stepAux]
    dsimp [mkPow2Cfg]; congr 1; congr 1; funext i; fin_cases i <;> simp
  have hp1 := pow2Len_p1 us 0
  have hhalt : mkPow2Cfg none [] (List.replicate us.length false ++ [true]) =
      haltList pow2LenTM (List.replicate us.length false ++ [true]) := by
    dsimp [haltList, mkPow2Cfg, pow2LenTM]; congr 1; funext i; fin_cases i <;> rfl
  simp only [add_zero] at hp1
  rw [hhalt] at hp1
  let eAll := EvalsTo.trans pow2LenTM.step _ _ _ ⟨1, hp0⟩ ⟨us.length + 1, hp1⟩
  refine ⟨eAll, ?_⟩
  dsimp only [eAll, EvalsTo.trans]
  have hlen : us.length ≤ U.length := list_length_le_bitEncode_length us
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  omega

private lemma replicate_flatMap_replicate (a b : ℕ) :
    (List.replicate a true).flatMap (fun _ => List.replicate b true) =
      List.replicate (a * b) true := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, ← List.replicate_add, Nat.succ_mul,
      Nat.add_comm]

theorem isPolyTime_unaryPowSucc {α : Type} [BitstringEncoding α] (d : ℕ) :
    IsPolyTime (fun x : α => List.replicate (((bitEncode x).length + 1) ^ (d + 1)) true) := by
  induction d with
  | zero =>
    simpa only [zero_add, pow_one] using (isPolyTime_unaryBitLenSucc (α := α))
  | succ d ih =>
    have hBase : IsPolyTime (fun x : α => List.replicate ((bitEncode x).length + 1) true) :=
      isPolyTime_unaryBitLenSucc
    have hMul := isPolyTime_comp
      (isPolyTime_comp (isPolyTime_pair ih hBase) isPolyTime_distribRight)
      (isPolyTime_flatMap isPolyTime_fst)
    have heq : (fun x : α =>
        ((List.replicate ((bitEncode x).length + 1) true).map (fun b =>
          (List.replicate (((bitEncode x).length + 1) ^ (d + 1)) true, b))).flatMap Prod.fst) =
        (fun x : α => List.replicate (((bitEncode x).length + 1) ^ (d + 2)) true) := by
      funext x
      rw [List.flatMap_map, replicate_flatMap_replicate]
      congr 1; ring
    exact heq ▸ hMul

theorem isPolyTime_pow2BitLenPow {α : Type} [BitstringEncoding α] (d : ℕ) :
    IsPolyTime (fun x : α => 2 ^ (((bitEncode x).length + 1) ^ (d + 1))) := by
  have h1 := isPolyTime_comp (isPolyTime_unaryPowSucc (α := α) d) isPolyTime_pow2Len
  have heq : (fun x : α =>
      2 ^ (List.replicate (((bitEncode x).length + 1) ^ (d + 1)) true).length) =
      (fun x : α => 2 ^ (((bitEncode x).length + 1) ^ (d + 1))) := by
    funext x; rw [List.length_replicate]
  exact heq ▸ h1

/- #### 6e. Binary-search `isPolyTime_sqrtNat` -/

private def revPows : ℕ → List ℕ
  | 0 => []
  | k + 1 => 2 ^ k :: revPows k

private lemma foldl_build_revPows (bs : List Bool) :
    bs.foldl (fun st _ => (st.1 + st.1, [st.1] ++ st.2)) ((1 : ℕ), ([] : List ℕ)) =
      (2 ^ bs.length, revPows bs.length) := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs b ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, List.length_append,
      List.length_singleton, revPows, List.singleton_append, Nat.pow_succ]
    congr 1
    omega

private lemma bitEncode_revPows_len (k N : ℕ) (hk : k ≤ N) :
    (bitEncode (revPows k)).length ≤ k * (2 * N + 3) := by
  induction k with
  | zero => simp [revPows, bitEncode_nil]
  | succ k ih =>
    rw [revPows, bitEncode_cons, List.length_append, length_delimit, bitEncode_nat_eq,
      encodeNat_two_pow, List.length_append, List.length_replicate, List.length_singleton,
      Nat.succ_mul]
    have h1 := ih (by omega)
    nlinarith

theorem isPolyTime_powersDesc : IsPolyTime (fun n : ℕ => revPows (encodeNat n).length) := by
  let B : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C 1) * (Polynomial.C 2 * Polynomial.X + Polynomial.C 3)
  have hDouble : IsPolyTime (fun q : (Bool × (ℕ × List ℕ)) × Bool => q.1.2.1 + q.1.2.1) :=
    isPolyTime_comp
      (isPolyTime_pair
        (isPolyTime_comp (isPolyTime_comp isPolyTime_fst isPolyTime_snd) isPolyTime_fst)
        (isPolyTime_comp (isPolyTime_comp isPolyTime_fst isPolyTime_snd) isPolyTime_fst))
      isPolyTime_addNat
  have hCons : IsPolyTime (fun q : (Bool × (ℕ × List ℕ)) × Bool => [q.1.2.1] ++ q.1.2.2) :=
    isPolyTime_comp
      (isPolyTime_pair
        (isPolyTime_comp
          (isPolyTime_comp (isPolyTime_comp isPolyTime_fst isPolyTime_snd) isPolyTime_fst)
          isPolyTime_singleton)
        (isPolyTime_comp (isPolyTime_comp isPolyTime_fst isPolyTime_snd) isPolyTime_snd))
      isPolyTime_append
  have hStep := isPolyTime_pair hDouble hCons
  have hFold : IsPolyTime (fun p : Bool × List Bool =>
      p.2.foldl (fun st _ => (st.1 + st.1, [st.1] ++ st.2)) ((1 : ℕ), ([] : List ℕ))) := by
    refine isPolyTime_foldlCtx (isPolyTime_const ((1 : ℕ), ([] : List ℕ))) hStep B ?_
    intro a done rem
    let N := (bitEncode (a, done ++ rem)).length
    rw [foldl_build_revPows, bitEncode_pair, List.length_append, length_delimit, bitEncode_nat_eq,
      encodeNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
    have hdone_len : done.length ≤ N := by
      have h1 := list_length_le_bitEncode_length (done ++ rem)
      rw [List.length_append] at h1
      have h2 : (bitEncode (done ++ rem)).length ≤ N := by
        simp only [N, bitEncode_pair, List.length_append]; omega
      omega
    have hrev := bitEncode_revPows_len done.length N hdone_len
    have hmul : done.length * (2 * N + 3) ≤ N * (2 * N + 3) :=
      Nat.mul_le_mul_right _ hdone_len
    simp only [B, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    nlinarith
  have hPrep : IsPolyTime (fun n : ℕ => (false, (encodeNat n).reverse)) :=
    isPolyTime_pair (isPolyTime_const false) isPolyTime_bitsMSB
  have hComp := isPolyTime_comp (isPolyTime_comp hPrep hFold) isPolyTime_snd
  have heq : (fun n : ℕ =>
      (((encodeNat n).reverse).foldl (fun st _ => (st.1 + st.1, [st.1] ++ st.2))
        ((1 : ℕ), ([] : List ℕ))).2) =
      (fun n : ℕ => revPows (encodeNat n).length) := by
    funext n
    rw [foldl_build_revPows, List.length_reverse]
  exact heq ▸ hComp

private def sqrtStep (n r p : ℕ) : ℕ :=
  if decide ((r + p) * (r + p) ≤ n) then r + p else r

private lemma foldl_sqrtStep_sq_le (n : ℕ) (xs : List ℕ) (r : ℕ) (hr : r * r ≤ n) :
    (xs.foldl (sqrtStep n) r) * (xs.foldl (sqrtStep n) r) ≤ n := by
  induction xs generalizing r with
  | nil => exact hr
  | cons p xs ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold sqrtStep
    by_cases h : (r + p) * (r + p) ≤ n <;> simp [h, hr]

private lemma foldl_sqrtStep_spec (n k r : ℕ)
    (hlo : r * r ≤ n) (hhi : n < (r + 2 ^ k) * (r + 2 ^ k)) :
    (revPows k).foldl (sqrtStep n) r = Nat.sqrt n := by
  suffices h : (revPows k).foldl (sqrtStep n) r * (revPows k).foldl (sqrtStep n) r ≤ n ∧
      n < ((revPows k).foldl (sqrtStep n) r + 1) * ((revPows k).foldl (sqrtStep n) r + 1) from
    Nat.eq_sqrt.mpr h
  induction k generalizing r with
  | zero =>
    simpa [revPows] using And.intro hlo hhi
  | succ k ih =>
    rw [revPows, List.foldl_cons]
    unfold sqrtStep
    by_cases hle : (r + 2 ^ k) * (r + 2 ^ k) ≤ n
    · simp only [hle, decide_true, ↓reduceIte]
      apply ih (r + 2 ^ k) hle
      have heq : r + 2 ^ k + 2 ^ k = r + 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      rwa [heq]
    · simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih r hlo (lt_of_not_ge hle)

theorem isPolyTime_sqrtNat : IsPolyTime Nat.sqrt := by
  have hCand : IsPolyTime (fun q : (ℕ × ℕ) × ℕ => q.1.2 + q.2) :=
    isPolyTime_comp
      (isPolyTime_pair (isPolyTime_comp isPolyTime_fst isPolyTime_snd) isPolyTime_snd)
      isPolyTime_addNat
  have hCandSq : IsPolyTime (fun q : (ℕ × ℕ) × ℕ => (q.1.2 + q.2) * (q.1.2 + q.2)) :=
    isPolyTime_comp (isPolyTime_pair hCand hCand) isPolyTime_mulNat
  have hCond : IsPolyTime (fun q : (ℕ × ℕ) × ℕ => decide ((q.1.2 + q.2) * (q.1.2 + q.2) ≤ q.1.1)) :=
    isPolyTime_comp
      (isPolyTime_pair hCandSq (isPolyTime_comp isPolyTime_fst isPolyTime_fst))
      isPolyTime_leNat
  have hStep : IsPolyTime (fun q : (ℕ × ℕ) × ℕ => sqrtStep q.1.1 q.1.2 q.2) :=
    isPolyTime_ite hCond hCand (isPolyTime_comp isPolyTime_fst isPolyTime_snd)
  have hFold : IsPolyTime (fun p : ℕ × List ℕ => p.2.foldl (sqrtStep p.1) 0) := by
    refine isPolyTime_foldlCtx (isPolyTime_const 0) hStep Polynomial.X ?_
    intro n done rem
    let N := (bitEncode (n, done ++ rem)).length
    let r := done.foldl (sqrtStep n) 0
    have hr_sq : r * r ≤ n := foldl_sqrtStep_sq_le n done 0 (by simp)
    have hr_le : r ≤ n := le_trans (Nat.le_mul_self r) hr_sq
    have hn_lt : n < 2 ^ (encodeNat n).length := by
      have h1 := ofBitsLE_lt_two_pow (encodeNat n)
      rwa [ofBitsLE_encodeNat] at h1
    have hn_N : (encodeNat n).length ≤ N := by
      simp only [N, bitEncode_pair, bitEncode_nat_eq, List.length_append, length_delimit]
      omega
    rw [bitEncode_nat_eq]
    apply encodeNat_length_le_of_lt_two_pow
    simp only [Polynomial.eval_X]
    exact lt_of_le_of_lt hr_le
      (lt_of_lt_of_le hn_lt (Nat.pow_le_pow_right (by decide : 0 < 2) hn_N))
  have hPrep : IsPolyTime (fun n : ℕ => (n, revPows (encodeNat n).length)) :=
    isPolyTime_pair isPolyTime_id isPolyTime_powersDesc
  have hComp := isPolyTime_comp hPrep hFold
  have heq : (fun n : ℕ => (revPows (encodeNat n).length).foldl (sqrtStep n) 0) = Nat.sqrt := by
    funext n
    apply foldl_sqrtStep_spec n (encodeNat n).length 0 (by simp)
    rw [zero_add]
    have hn_lt : n < 2 ^ (encodeNat n).length := by
      have h1 := ofBitsLE_lt_two_pow (encodeNat n)
      rwa [ofBitsLE_encodeNat] at h1
    have hpow_le : 2 ^ (encodeNat n).length ≤ 2 ^ (encodeNat n).length * 2 ^ (encodeNat n).length :=
      Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide : 0 < 2))
    exact lt_of_lt_of_le hn_lt hpow_le
  exact heq ▸ hComp

/- ### 7. Proof of `H4` -/

theorem prove_H4 : OMA.R_PolyTime_isPolyTime_squareRootSumTwoSided_R1.H4 := by
  intro d
  let L1 : List ℕ × List ℕ → ℕ := fun x => x.1.length
  let L2 : List ℕ × List ℕ → ℕ := fun x => x.2.length
  have hL1 : IsPolyTime L1 := isPolyTime_comp isPolyTime_fst isPolyTime_listLength
  have hL2 : IsPolyTime L2 := isPolyTime_comp isPolyTime_snd isPolyTime_listLength
  have hCoef0 := isPolyTime_comp
    (isPolyTime_pair
      (isPolyTime_comp (isPolyTime_pair hL1 hL2) isPolyTime_addNat)
      (isPolyTime_const 1))
    isPolyTime_addNat
  have hCoef : IsPolyTime (fun x : List ℕ × List ℕ => x.1.length + x.2.length + 1) := hCoef0
  have hPow2 : IsPolyTime
      (fun x : List ℕ × List ℕ => 2 ^ (((bitEncode x).length + 1) ^ (d + 1))) :=
    isPolyTime_pow2BitLenPow d
  let scale : List ℕ × List ℕ → ℕ := fun x =>
    (x.1.length + x.2.length + 1) * 2 ^ (((bitEncode x).length + 1) ^ (d + 1))
  have hScale0 := isPolyTime_comp (isPolyTime_pair hCoef hPow2) isPolyTime_mulNat
  have hScale : IsPolyTime scale := hScale0
  have hTerm : IsPolyTime (fun q : ℕ × ℕ => Nat.sqrt (q.1 ^ 2 * q.2)) := by
    have hSq : IsPolyTime (fun q : ℕ × ℕ => q.1 ^ 2) := by
      have h1 := isPolyTime_comp
        (isPolyTime_pair (isPolyTime_fst (α := ℕ) (β := ℕ)) (isPolyTime_fst (α := ℕ) (β := ℕ)))
        isPolyTime_mulNat
      have heq : (fun q : ℕ × ℕ => q.1 * q.1) = (fun q : ℕ × ℕ => q.1 ^ 2) := by
        funext q; rw [sq]
      exact heq ▸ h1
    have hT0 := isPolyTime_comp
      (isPolyTime_comp (isPolyTime_pair hSq isPolyTime_snd) isPolyTime_mulNat)
      isPolyTime_sqrtNat
    exact hT0
  have hLowerPair : IsPolyTime
      (fun p : ℕ × List ℕ => (p.2.map (fun n => Nat.sqrt (p.1 ^ 2 * n))).sum) := by
    have h1 := isPolyTime_comp
      (isPolyTime_comp isPolyTime_distribRight (isPolyTime_map hTerm))
      isPolyTime_listSum
    have heq : (fun p : ℕ × List ℕ =>
        ((p.2.map (fun n => (p.1, n))).map (fun q => Nat.sqrt (q.1 ^ 2 * q.2))).sum) =
        (fun p : ℕ × List ℕ => (p.2.map (fun n => Nat.sqrt (p.1 ^ 2 * n))).sum) := by
      funext ⟨m, l⟩; simp [List.map_map, Function.comp_def]
    exact heq ▸ h1
  let lower (m : ℕ) (l : List ℕ) := (l.map (fun n => Nat.sqrt (m ^ 2 * n))).sum
  have hLow1_0 := isPolyTime_comp (isPolyTime_pair hScale isPolyTime_fst) hLowerPair
  have hLow1 : IsPolyTime (fun x : List ℕ × List ℕ => lower (scale x) x.1) := hLow1_0
  have hLow2_0 := isPolyTime_comp (isPolyTime_pair hScale isPolyTime_snd) hLowerPair
  have hLow2 : IsPolyTime (fun x : List ℕ × List ℕ => lower (scale x) x.2) := hLow2_0
  have hCmp1_0 := isPolyTime_comp
    (isPolyTime_pair
      (isPolyTime_comp (isPolyTime_pair hLow1 hL1) isPolyTime_addNat)
      hLow2)
    isPolyTime_leNat
  have hCmp1 : IsPolyTime
      (fun x : List ℕ × List ℕ => decide (lower (scale x) x.1 + x.1.length ≤ lower (scale x) x.2)) :=
    hCmp1_0
  have hCmp2_0 := isPolyTime_comp
    (isPolyTime_pair
      hLow1
      (isPolyTime_comp (isPolyTime_pair hLow2 hL2) isPolyTime_addNat))
    isPolyTime_leNat
  have hCmp2 : IsPolyTime
      (fun x : List ℕ × List ℕ => decide (lower (scale x) x.1 ≤ lower (scale x) x.2 + x.2.length)) :=
    hCmp2_0
  exact ⟨hCmp1, hCmp2⟩

end PolyTimeSqrtH4Proof

theorem OMA.solution : OMA.R_PolyTime_isPolyTime_squareRootSumTwoSided_R1.H4 :=
  PolyTimeSqrtH4Proof.prove_H4
