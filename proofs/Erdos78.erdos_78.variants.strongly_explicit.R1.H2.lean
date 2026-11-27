import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1

-- Step Erdos78.erdos_78.variants.strongly_explicit.R1.H2: hypothesis H2 of reduction Erdos78.erdos_78.variants.strongly_explicit.R1
-- Credit: @adammcarter
-- H2: composing two poly-time maps gives a poly-time map. Proved in general for any types with
-- a BitstringEncoding (a hand-built machine runs the first machine, moves its output onto the
-- second machine's input stack, then runs the second), then specialized.

open ComplexityTheory
open Turing Computability

namespace Erdos78Comp

/-! Reachability of a configuration within a step budget, as a Prop. -/

def RIn {σ : Type} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ n ≤ m, (flip bind f)^[n] (some a) = b

lemma RIn.single {σ : Type} {f : σ → Option σ} {a b : σ} (h : f a = some b) :
    RIn f a (some b) 1 :=
  ⟨1, le_rfl, h⟩

lemma RIn.trans {σ : Type} {f : σ → Option σ} {a b : σ} {c : Option σ} {m₁ m₂ : ℕ}
    (h₁ : RIn f a (some b) m₁) (h₂ : RIn f b c m₂) : RIn f a c (m₁ + m₂) := by
  obtain ⟨n₁, hn₁, e₁⟩ := h₁
  obtain ⟨n₂, hn₂, e₂⟩ := h₂
  refine ⟨n₂ + n₁, by omega, ?_⟩
  rw [Function.iterate_add_apply, e₁, e₂]

lemma RIn.mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : RIn f a b m) (hm : m ≤ m') : RIn f a b m' := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨n, hn.trans hm, e⟩

lemma eval_mono (q : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : q.eval a ≤ q.eval b := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

lemma iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-! Growth of stacks: one step pushes at most a bounded number of symbols. -/

def pushCount {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushCount q + 1
  | .peek _ _ q => pushCount q
  | .pop _ _ q => pushCount q
  | .load _ q => pushCount q
  | .branch _ q₁ q₂ => pushCount q₁ + pushCount q₂
  | .goto _ => 0
  | .halt => 0

lemma stepAux_len {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushCount q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, pushCount]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      simp only [Function.update_self, List.length_cons]
      omega
    · rw [Function.update_of_ne h]
      omega
  | peek k' f q ih =>
    simp only [TM2.stepAux, pushCount]
    exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux, pushCount]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      simp only [Function.update_self, List.length_tail]
      omega
    · rw [Function.update_of_ne h]
  | load a q ih =>
    simp only [TM2.stepAux, pushCount]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushCount]
    cases f v
    · exact (ih₂ v S).trans (by omega)
    · exact (ih₁ v S).trans (by omega)
  | goto f => simp [TM2.stepAux, pushCount]
  | halt => simp [TM2.stepAux, pushCount]

lemma exists_pushBound (M : FinTM2) : ∃ B : ℕ, ∀ l, pushCount (M.m l) ≤ B := by
  let _ : Fintype M.Λ := M.ΛFin
  exact ⟨Finset.univ.sup (fun l => pushCount (M.m l)),
    fun l => Finset.le_sup (f := fun l => pushCount (M.m l)) (Finset.mem_univ l)⟩

lemma step_len (M : FinTM2) {B : ℕ} (hB : ∀ l, pushCount (M.m l) ≤ B)
    {c c' : TM2.Cfg M.Γ M.Λ M.σ} (h : M.step c = some c') (k : M.K) :
    (c'.stk k).length ≤ (c.stk k).length + B := by
  rcases c with ⟨_ | l, v, S⟩
  · exact absurd h (by simp [FinTM2.step, TM2.step])
  · have h' : some (TM2.stepAux (M.m l) v S) = some c' := h
    injection h' with h'
    subst h'
    exact (stepAux_len (M.m l) v S k).trans (Nat.add_le_add_left (hB l) _)

lemma iterate_len (M : FinTM2) {B : ℕ} (hB : ∀ l, pushCount (M.m l) ≤ B) (n : ℕ)
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : (flip bind M.step)^[n] (some c) = some c') (k : M.K) :
    (c'.stk k).length ≤ (c.stk k).length + n * B := by
  induction n generalizing c with
  | zero =>
    have h' : some c = some c' := h
    injection h' with h'
    subst h'
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    change (flip bind M.step)^[n] (M.step c) = some c' at h
    cases hs : M.step c with
    | none =>
      rw [hs, iterate_none] at h
      exact absurd h (by simp)
    | some c₁ =>
      rw [hs] at h
      have h1 := ih c₁ h
      have h2 := step_len M hB hs k
      rw [Nat.succ_mul]
      omega

lemma initList_stk_len (M : FinTM2) (s : List (M.Γ M.k₀)) (k : M.K) :
    ((initList M s).stk k).length ≤ s.length := by
  by_cases h : k = M.k₀
  · subst h
    simp [initList]
  · simp [initList, h]

lemma haltList_stk_self (M : FinTM2) (s : List (M.Γ M.k₁)) :
    (haltList M s).stk M.k₁ = s := by
  simp [haltList]

lemma haltList_stk_update (M : FinTM2) (s : List (M.Γ M.k₁)) :
    Function.update (haltList M s).stk M.k₁ [] = fun _ => [] := by
  funext k
  by_cases h : k = M.k₁
  · subst h
    simp
  · simp [haltList, h]

lemma out_len (M : FinTM2) {B : ℕ} (hB : ∀ l, pushCount (M.m l) ≤ B)
    {s : List (M.Γ M.k₀)} {out : List (M.Γ M.k₁)} {T : ℕ}
    (h : TM2OutputsInTime M s (some out) T) : out.length ≤ s.length + T * B := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  have h1 := iterate_len M hB n (initList M s) (haltList M out) hn M.k₁
  rw [haltList_stk_self] at h1
  have h2 := initList_stk_len M s M.k₁
  have h3 : n * B ≤ T * B := Nat.mul_le_mul_right B hle
  omega

/-! The composed machine. Stacks: the stacks of M, the stacks of N and one helper stack. -/

variable (M N : FinTM2) (eo : M.Γ M.k₁ ≃ Bool) (ei : N.Γ N.k₀ ≃ Bool)

abbrev KK : Type := M.K ⊕ (N.K ⊕ Unit)

abbrev LL : Type := M.Λ ⊕ (N.Λ ⊕ Bool)

abbrev VV : Type := M.σ × N.σ × Option Bool

abbrev GG : KK M N → Type := fun k =>
  Sum.casesOn (motive := fun _ => Type) k M.Γ
    (fun k' => Sum.casesOn (motive := fun _ => Type) k' N.Γ (fun _ => Bool))

def liftM : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (GG M N) (LL M N) (VV M N)
  | .push k f q => .push (Sum.inl k) (fun v => f v.1) (liftM q)
  | .peek k f q => .peek (Sum.inl k) (fun v o => (f v.1 o, v.2)) (liftM q)
  | .pop k f q => .pop (Sum.inl k) (fun v o => (f v.1 o, v.2)) (liftM q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftM q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftM q₁) (liftM q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr false))

def liftN : TM2.Stmt N.Γ N.Λ N.σ → TM2.Stmt (GG M N) (LL M N) (VV M N)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun v => f v.2.1) (liftN q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftN q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftN q)
  | .load a q => .load (fun v => (v.1, a v.2.1, v.2.2)) (liftN q)
  | .branch f q₁ q₂ => .branch (fun v => f v.2.1) (liftN q₁) (liftN q₂)
  | .goto f => .goto (fun v => Sum.inr (Sum.inl (f v.2.1)))
  | .halt => .halt

def prog : LL M N → TM2.Stmt (GG M N) (LL M N) (VV M N)
  | Sum.inl l => liftM M N (M.m l)
  | Sum.inr (Sum.inl l) => liftN M N (N.m l)
  | Sum.inr (Sum.inr false) =>
    .pop (Sum.inl M.k₁) (fun v (o : Option (M.Γ M.k₁)) => (v.1, v.2.1, o.map eo)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inr ())) (fun v => v.2.2.getD false) <|
          .goto fun _ => Sum.inr (Sum.inr false))
        (.goto fun _ => Sum.inr (Sum.inr true))
  | Sum.inr (Sum.inr true) =>
    .pop (Sum.inr (Sum.inr ())) (fun v (o : Option Bool) => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inl N.k₀)) (fun v => ei.symm (v.2.2.getD false)) <|
          .goto fun _ => Sum.inr (Sum.inr true))
        (.goto fun _ => Sum.inr (Sum.inl N.main))

def Cmp : FinTM2 :=
  letI := M.kFin
  letI := N.kFin
  letI := M.ΛFin
  letI := N.ΛFin
  letI := M.σFin
  letI := N.σFin
  { K := KK M N
    k₀ := Sum.inl M.k₀
    k₁ := Sum.inr (Sum.inl N.k₁)
    Γ := GG M N
    Λ := LL M N
    main := Sum.inl M.main
    σ := VV M N
    initialState := (M.initialState, N.initialState, none)
    Γk₀Fin := M.Γk₀Fin
    m := prog M N eo ei }

def mk (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) :
    ∀ k : KK M N, List (GG M N k)
  | Sum.inl k => SM k
  | Sum.inr (Sum.inl k) => SN k
  | Sum.inr (Sum.inr _) => a

variable {M N} {eo} {ei}

lemma upd_M (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) (k : M.K)
    (v : List (GG M N (Sum.inl k))) :
    Function.update (mk M N SM SN a) (Sum.inl k) v = mk M N (Function.update SM k v) SN a := by
  funext k'
  rcases k' with k' | k' | k'
  · by_cases h : k' = k
    · subst h
      simp [Function.update, mk]
    · simp [Function.update, mk, h]
  · simp [Function.update, mk]
  · simp [Function.update, mk]

lemma upd_N (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) (k : N.K)
    (v : List (GG M N (Sum.inr (Sum.inl k)))) :
    Function.update (mk M N SM SN a) (Sum.inr (Sum.inl k)) v =
      mk M N SM (Function.update SN k v) a := by
  funext k'
  rcases k' with k' | k' | k'
  · simp [Function.update, mk]
  · by_cases h : k' = k
    · subst h
      simp [Function.update, mk]
    · simp [Function.update, mk, h]
  · simp [Function.update, mk]

lemma upd_A (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool)
    (v : List (GG M N (Sum.inr (Sum.inr ())))) :
    Function.update (mk M N SM SN a) (Sum.inr (Sum.inr ())) v = mk M N SM SN v := by
  funext k'
  rcases k' with k' | k' | k'
  · simp [Function.update, mk]
  · simp [Function.update, mk]
  · simp [Function.update, mk]

lemma mk_nil : mk M N (fun _ => []) (fun _ => []) [] = fun _ => [] := by
  funext k
  rcases k with k | k | k <;> rfl

def liftCfgM (c : TM2.Cfg M.Γ M.Λ M.σ) : (Cmp M N eo ei).Cfg :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl), (c.var, N.initialState, none),
    mk M N c.stk (fun _ => []) []⟩

def liftCfgN (c : TM2.Cfg N.Γ N.Λ N.σ) : (Cmp M N eo ei).Cfg :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (M.initialState, c.var, none),
    mk M N (fun _ => []) c.stk []⟩

def cfg (b : Bool) (o : Option Bool) (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k))
    (a : List Bool) : (Cmp M N eo ei).Cfg :=
  ⟨some (Sum.inr (Sum.inr b)), (M.initialState, N.initialState, o), mk M N SM SN a⟩

/-! Simulation of the first machine. -/

lemma stepAux_liftM (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftM M N q) (v, N.initialState, none) (mk M N S (fun _ => []) []) =
      liftCfgM (eo := eo) (ei := ei) (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [liftM, TM2.stepAux]
    rw [upd_M]
    exact ih _ _
  | peek k f q ih =>
    simp only [liftM, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    simp only [liftM, TM2.stepAux]
    rw [upd_M]
    exact ih _ _
  | load a q ih =>
    simp only [liftM, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftM, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma step_liftM {c c' : TM2.Cfg M.Γ M.Λ M.σ} (h : M.step c = some c') :
    (Cmp M N eo ei).step (liftCfgM c) = some (liftCfgM c') := by
  rcases c with ⟨_ | l, v, S⟩
  · exact absurd h (by simp [FinTM2.step, TM2.step])
  · have h' : some (TM2.stepAux (M.m l) v S) = some c' := h
    injection h' with h'
    subst h'
    show some (TM2.stepAux (liftM M N (M.m l)) (v, N.initialState, none)
      (mk M N S (fun _ => []) [])) = _
    exact congrArg some (stepAux_liftM (eo := eo) (ei := ei) (M.m l) v S)

lemma iterate_liftM (n : ℕ) (c c' : TM2.Cfg M.Γ M.Λ M.σ)
    (h : (flip bind M.step)^[n] (some c) = some c') :
    (flip bind (Cmp M N eo ei).step)^[n] (some (liftCfgM c)) = some (liftCfgM c') := by
  induction n generalizing c with
  | zero =>
    have h' : some c = some c' := h
    injection h' with h'
    subst h'
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind M.step)^[n] (M.step c) = some c' at h
    change (flip bind (Cmp M N eo ei).step)^[n] ((Cmp M N eo ei).step (liftCfgM c)) = _
    cases hs : M.step c with
    | none =>
      rw [hs, iterate_none] at h
      exact absurd h (by simp)
    | some c₁ =>
      rw [hs] at h
      rw [step_liftM hs]
      exact ih c₁ h

/-! Simulation of the second machine. -/

lemma stepAux_liftN (q : TM2.Stmt N.Γ N.Λ N.σ) (v : N.σ) (S : ∀ k, List (N.Γ k)) :
    TM2.stepAux (liftN M N q) (M.initialState, v, none) (mk M N (fun _ => []) S []) =
      liftCfgN (eo := eo) (ei := ei) (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [liftN, TM2.stepAux]
    rw [upd_N]
    exact ih _ _
  | peek k f q ih =>
    simp only [liftN, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    simp only [liftN, TM2.stepAux]
    rw [upd_N]
    exact ih _ _
  | load a q ih =>
    simp only [liftN, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftN, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma step_liftN (c : TM2.Cfg N.Γ N.Λ N.σ) :
    (Cmp M N eo ei).step (liftCfgN c) = (N.step c).map liftCfgN := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · show some (TM2.stepAux (liftN M N (N.m l)) (M.initialState, v, none)
      (mk M N (fun _ => []) S [])) = _
    rw [stepAux_liftN]
    rfl

lemma iterate_liftN (n : ℕ) (o : Option (TM2.Cfg N.Γ N.Λ N.σ)) :
    (flip bind (Cmp M N eo ei).step)^[n] (o.map liftCfgN) =
      ((flip bind N.step)^[n] o).map liftCfgN := by
  have hs : Function.Semiconj (Option.map (liftCfgN (M := M) (N := N) (eo := eo) (ei := ei)))
      (flip bind N.step) (flip bind (Cmp M N eo ei).step) := by
    intro o
    rcases o with _ | c
    · rfl
    · show (N.step c).map liftCfgN = (Cmp M N eo ei).step (liftCfgN c)
      rw [step_liftN]
  exact ((hs.iterate_right n) o).symm

/-! One step of each transfer phase. -/

lemma step_mv1_cons (o : Option Bool) (c : M.Γ M.k₁) (s : List (M.Γ M.k₁))
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool)
    (h : SM M.k₁ = c :: s) :
    (Cmp M N eo ei).step (cfg false o SM SN a) =
      some (cfg false (some (eo c)) (Function.update SM M.k₁ s) SN (eo c :: a)) := by
  show some (TM2.stepAux (prog M N eo ei (Sum.inr (Sum.inr false)))
    (M.initialState, N.initialState, o) (mk M N SM SN a)) = _
  simp [prog, TM2.stepAux, mk, upd_M, upd_A, cfg, h]
  rfl

lemma step_mv1_nil (o : Option Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool)
    (h : SM M.k₁ = []) :
    (Cmp M N eo ei).step (cfg false o SM SN a) =
      some (cfg true none (Function.update SM M.k₁ []) SN a) := by
  show some (TM2.stepAux (prog M N eo ei (Sum.inr (Sum.inr false)))
    (M.initialState, N.initialState, o) (mk M N SM SN a)) = _
  simp [prog, TM2.stepAux, mk, upd_M, upd_A, cfg, h]
  rfl

lemma step_mv2_cons (o : Option Bool) (c : Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) :
    (Cmp M N eo ei).step (cfg true o SM SN (c :: a)) =
      some (cfg true (some c) SM (Function.update SN N.k₀ (ei.symm c :: SN N.k₀)) a) := by
  show some (TM2.stepAux (prog M N eo ei (Sum.inr (Sum.inr true)))
    (M.initialState, N.initialState, o) (mk M N SM SN (c :: a))) = _
  simp [prog, TM2.stepAux, mk, upd_N, upd_A, cfg]
  rfl

lemma step_mv2_nil (o : Option Bool) (SN : ∀ k, List (N.Γ k)) :
    (Cmp M N eo ei).step (cfg true o (fun _ => []) SN []) =
      some (liftCfgN ⟨some N.main, N.initialState, SN⟩) := by
  show some (TM2.stepAux (prog M N eo ei (Sum.inr (Sum.inr true)))
    (M.initialState, N.initialState, o) (mk M N (fun _ => []) SN [])) = _
  simp [prog, TM2.stepAux, mk, upd_N, upd_A, liftCfgN]
  rfl

/-! The two transfer phases. -/

lemma mv1_run (s : List (M.Γ M.k₁)) (o : Option Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) (h : SM M.k₁ = s) :
    RIn (Cmp M N eo ei).step (cfg false o SM SN a)
      (some (cfg true none (Function.update SM M.k₁ []) SN ((s.map eo).reverse ++ a)))
      (s.length + 1) := by
  induction s generalizing o SM a with
  | nil => exact RIn.single (step_mv1_nil o SM SN a h)
  | cons c s ih =>
    have h1 := RIn.single (step_mv1_cons (eo := eo) (ei := ei) o c s SM SN a h)
    have h2 := ih (some (eo c)) (Function.update SM M.k₁ s) (eo c :: a)
      (Function.update_self _ _ _)
    have := RIn.trans h1 h2
    simp only [Function.update_idem] at this
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma mv2_run (a : List Bool) (o : Option Bool) (SN : ∀ k, List (N.Γ k)) :
    RIn (Cmp M N eo ei).step (cfg true o (fun _ => []) SN a)
      (some (liftCfgN ⟨some N.main, N.initialState,
        Function.update SN N.k₀ ((a.map ei.symm).reverse ++ SN N.k₀)⟩))
      (a.length + 1) := by
  induction a generalizing o SN with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
    exact RIn.single (step_mv2_nil o SN)
  | cons c a ih =>
    have := RIn.trans (RIn.single (step_mv2_cons (eo := eo) (ei := ei) o c (fun _ => []) SN a))
      (ih (some c) _)
    simp only [Function.update_self, Function.update_idem] at this
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

/-! Initial and final configurations. -/

lemma initList_stk (M : FinTM2) (s : List (M.Γ M.k₀)) :
    (initList M s).stk = Function.update (fun _ => []) M.k₀ s := by
  funext k
  by_cases h : k = M.k₀
  · subst h
    simp [initList]
  · simp [initList, h]

lemma initList_Cmp (s : List (M.Γ M.k₀)) :
    initList (Cmp M N eo ei) s = liftCfgM (initList M s) := by
  simp only [initList, liftCfgM]
  congr 1
  funext k
  rcases k with k | k | k
  · by_cases h : k = M.k₀
    · subst h
      simp [mk]
      split
      · rfl
      · rename_i hne
        exact absurd rfl hne
    · simp [mk, h]
      split
      · rename_i heq
        exact absurd (Sum.inl_injective (heq : (Sum.inl k : KK M N) = Sum.inl M.k₀)) h
      · rfl
  · rfl
  · rfl

lemma initList_N (s : List (N.Γ N.k₀)) :
    liftCfgN (eo := eo) (ei := ei)
      ⟨some N.main, N.initialState, Function.update (fun _ => []) N.k₀ s⟩ =
      liftCfgN (eo := eo) (ei := ei) (initList N s) := by
  have : (initList N s) = ⟨some N.main, N.initialState, (initList N s).stk⟩ := rfl
  rw [this, initList_stk]

lemma haltList_Cmp (s : List (N.Γ N.k₁)) :
    liftCfgN (eo := eo) (ei := ei) (haltList N s) = haltList (Cmp M N eo ei) s := by
  simp only [liftCfgN, haltList]
  congr 1
  funext k
  rcases k with k | k | k
  · rfl
  · by_cases h : k = N.k₁
    · subst h
      simp [mk]
      split
      · rfl
      · rename_i hne
        exact absurd rfl hne
    · simp [mk, h]
      split
      · rename_i heq
        exact absurd (Sum.inl_injective (Sum.inr_injective
          (heq : (Sum.inr (Sum.inl k) : KK M N) = Sum.inr (Sum.inl N.k₁)))) h
      · rfl
  · rfl

lemma run_M {s : List (M.Γ M.k₀)} {out : List (M.Γ M.k₁)} {T : ℕ}
    (h : TM2OutputsInTime M s (some out) T) :
    RIn (Cmp M N eo ei).step (initList (Cmp M N eo ei) s)
      (some (cfg false none (haltList M out).stk (fun _ => []) [])) T := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  refine ⟨n, hle, ?_⟩
  rw [initList_Cmp]
  exact iterate_liftM n (initList M s) (haltList M out) hn

lemma run_N {s : List (N.Γ N.k₀)} {out : List (N.Γ N.k₁)} {T : ℕ}
    (h : TM2OutputsInTime N s (some out) T) :
    RIn (Cmp M N eo ei).step (liftCfgN (initList N s))
      (some (haltList (Cmp M N eo ei) out)) T := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  refine ⟨n, hle, ?_⟩
  have := iterate_liftN (M := M) (N := N) (eo := eo) (ei := ei) n (some (initList N s))
  change (flip bind (Cmp M N eo ei).step)^[n] (Option.map liftCfgN (some (initList N s))) = _
  rw [this]
  refine (congrArg (Option.map liftCfgN) hn).trans ?_
  show some (liftCfgN (haltList N out)) = _
  rw [haltList_Cmp]

lemma transfer_run (out : List (M.Γ M.k₁)) :
    RIn (Cmp M N eo ei).step (cfg false none (haltList M out).stk (fun _ => []) [])
      (some (liftCfgN (initList N (List.map ei.symm (List.map eo out)))))
      ((out.length + 1) + (out.length + 1)) := by
  have h2 := mv1_run (eo := eo) (ei := ei) out none (haltList M out).stk (fun _ => []) []
    (haltList_stk_self M out)
  rw [haltList_stk_update] at h2
  have h3 := mv2_run (M := M) (eo := eo) (ei := ei) ((out.map eo).reverse ++ []) none
    (fun _ => [])
  have hcfg : (List.map ei.symm ((out.map eo).reverse ++ [])).reverse ++ [] =
      List.map ei.symm (List.map eo out) := by
    simp [List.map_reverse]
  rw [hcfg, initList_N] at h3
  have hlen : ((out.map eo).reverse ++ []).length = out.length := by simp
  rw [hlen] at h3
  exact h2.trans h3

/-- Composition of two machines: the composed machine computes the composite within the
sum of the time budgets. -/
lemma comp_run {s : List (M.Γ M.k₀)} {mid : List Bool} {out : List (N.Γ N.k₁)} {T₁ T₂ : ℕ}
    (h₁ : TM2OutputsInTime M s (some (List.map eo.symm mid)) T₁)
    (h₂ : TM2OutputsInTime N (List.map ei.symm mid) (some out) T₂) :
    RIn (Cmp M N eo ei).step (initList (Cmp M N eo ei) s)
      (some (haltList (Cmp M N eo ei) out))
      (T₁ + ((mid.length + 1) + (mid.length + 1)) + T₂) := by
  have a1 := run_M (N := N) (eo := eo) (ei := ei) h₁
  have a2 := transfer_run (M := M) (N := N) (eo := eo) (ei := ei) (List.map eo.symm mid)
  have a3 := run_N (M := M) (eo := eo) (ei := ei) h₂
  have hmid : List.map eo (List.map eo.symm mid) = mid := by simp
  have hlen : (List.map eo.symm mid).length = mid.length := by simp
  rw [hmid, hlen] at a2
  exact (a1.trans a2).trans a3

end Erdos78Comp

open Erdos78Comp in
/-- Polynomial-time computable functions are closed under composition. -/
theorem Erdos78Comp.comp_polyTime {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (f : α → β) (g : β → γ) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (g ∘ f) := by
  obtain ⟨M⟩ := hf
  obtain ⟨N⟩ := hg
  obtain ⟨B, hB⟩ := exists_pushBound M.tm
  refine ⟨{ tm := Cmp M.tm N.tm M.outputAlphabet N.inputAlphabet
            inputAlphabet := M.inputAlphabet
            outputAlphabet := N.outputAlphabet
            time := M.time + Polynomial.C 2 * (Polynomial.X + M.time * Polynomial.C B + 1) +
              N.time.comp (Polynomial.X + M.time * Polynomial.C B)
            outputsFun := fun a => ?_ }⟩
  have hM := M.outputsFun a
  have hN := N.outputsFun (f a)
  set x := (BitstringEncoding.toEncoding (α := α)).encode a with hx
  set y := (BitstringEncoding.toEncoding (α := β)).encode (f a) with hy
  have hlen : y.length ≤ x.length + M.time.eval x.length * B := by
    have := out_len M.tm hB hM
    simpa using this
  have hrun := comp_run (M := M.tm) (N := N.tm) (eo := M.outputAlphabet)
    (ei := N.inputAlphabet) (mid := y) hM hN
  have hb : M.time.eval x.length + ((y.length + 1) + (y.length + 1)) + N.time.eval y.length ≤
      (M.time + Polynomial.C 2 * (Polynomial.X + M.time * Polynomial.C B + 1) +
        N.time.comp (Polynomial.X + M.time * Polynomial.C B)).eval x.length := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_comp]
    have := eval_mono N.time hlen
    generalize M.time.eval x.length * B = W at *
    omega
  exact Classical.choice (by
    obtain ⟨n, hle, he⟩ := hrun.mono hb
    exact ⟨⟨⟨n, he⟩, hle⟩⟩)

/-- The composition fact used in the reduction of Erdos problem 78 (strongly explicit variant). -/
theorem erdos78_comp_polyTime (f : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (g : ℕ × ℕ × ℕ → Bool)
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (g ∘ f) :=
  Erdos78Comp.comp_polyTime f g hf hg

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1.H2 :=
  fun f g hf hg => erdos78_comp_polyTime f g hf hg
