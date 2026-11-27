import FormalConjectures.Paper.PudlakFiniteDomainConjectures

/-!
# Proof of `PudlakFiniteDomain.tfnp_no_complete_problem.variants.exists_of_NP_eq_coNP`

Under `NP = coNP`, we construct a complete total NP search problem `T : TFNPProblem`
by compiling arbitrary `FinTM2` verifiers to flat binary-stack programs (`PudlakMod1`),
building a polynomial-time universal flat-program verifier `U` (`PudlakMod2`),
providing polynomial-time instance encoding and tail extraction (`PudlakMod3`),
and combining `U` with a coNP witness verifier for non-existence (`PudlakMod3B`).
-/


namespace PudlakMod1

open Computability Turing ComplexityTheory

inductive FlatInstr where
  | jump (next : ℕ)
  | push (stk : ℕ) (bit : Bool) (next : ℕ)
  | pop (stk : ℕ) (onEmpty onFalse onTrue : ℕ)
  | halt

structure FlatCfg where
  pc : Option ℕ
  stks : List (List Bool)

def getStk : List (List Bool) → ℕ → List Bool
  | [], _ => []
  | s :: _, 0 => s
  | _ :: ss, k + 1 => getStk ss k

def pushStk : List (List Bool) → ℕ → Bool → List (List Bool)
  | [], 0, b => [[b]]
  | s :: ss, 0, b => (b :: s) :: ss
  | [], k + 1, b => [] :: pushStk [] k b
  | s :: ss, k + 1, b => s :: pushStk ss k b

def popStk : List (List Bool) → ℕ → Option Bool × List (List Bool)
  | [], 0 => (none, [])
  | [] :: ss, 0 => (none, [] :: ss)
  | (b :: s) :: ss, 0 => (some b, s :: ss)
  | [], k + 1 =>
    let p := popStk [] k
    (p.1, [] :: p.2)
  | s :: ss, k + 1 =>
    let p := popStk ss k
    (p.1, s :: p.2)

@[simp]
lemma getStk_nil (k : ℕ) : getStk [] k = [] := by
  cases k <;> rfl

lemma getStk_pushStk_self (stks : List (List Bool)) (k : ℕ) (b : Bool) :
    getStk (pushStk stks k b) k = b :: getStk stks k := by
  induction k generalizing stks with
  | zero => cases stks <;> rfl
  | succ k ih => cases stks <;> exact ih _

lemma getStk_pushStk_ne (stks : List (List Bool)) {k j : ℕ} (b : Bool) (hne : j ≠ k) :
    getStk (pushStk stks k b) j = getStk stks j := by
  induction k generalizing stks j with
  | zero =>
    cases j with
    | zero => exact (hne rfl).elim
    | succ j => cases stks <;> rfl
  | succ k ih =>
    cases j with
    | zero => cases stks <;> rfl
    | succ j =>
      have hne' : j ≠ k := fun h => hne (congr_arg Nat.succ h)
      cases stks <;> exact ih _ hne'

lemma fst_popStk (stks : List (List Bool)) (k : ℕ) :
    (popStk stks k).1 = (getStk stks k).head? := by
  induction k generalizing stks with
  | zero =>
    rcases stks with _ | ⟨_ | ⟨b, s⟩, ss⟩ <;> rfl
  | succ k ih =>
    cases stks with
    | nil => exact ih []
    | cons s ss => simp only [popStk, getStk]; exact ih ss

lemma getStk_popStk_self (stks : List (List Bool)) (k : ℕ) :
    getStk (popStk stks k).2 k = (getStk stks k).tail := by
  induction k generalizing stks with
  | zero =>
    rcases stks with _ | ⟨_ | ⟨b, s⟩, ss⟩ <;> rfl
  | succ k ih =>
    cases stks with
    | nil => exact ih []
    | cons s ss => simp only [popStk, getStk]; exact ih ss

lemma getStk_popStk_ne (stks : List (List Bool)) {k j : ℕ} (hne : j ≠ k) :
    getStk (popStk stks k).2 j = getStk stks j := by
  induction k generalizing stks j with
  | zero =>
    cases j with
    | zero => exact (hne rfl).elim
    | succ j =>
      rcases stks with _ | ⟨_ | ⟨b, s⟩, ss⟩ <;> rfl
  | succ k ih =>
    cases j with
    | zero =>
      cases stks <;> simp [popStk, getStk]
    | succ j =>
      have hne' : j ≠ k := fun h => hne (congr_arg Nat.succ h)
      cases stks with
      | nil => exact ih [] hne'
      | cons s ss => simp only [popStk, getStk]; exact ih ss hne'

def flatStep (prog : List FlatInstr) (c : FlatCfg) : FlatCfg :=
  match c.pc with
  | none => c
  | some idx =>
    match prog[idx]? with
    | none => ⟨none, c.stks⟩
    | some .halt => ⟨none, c.stks⟩
    | some (.jump next) => ⟨some next, c.stks⟩
    | some (.push k b next) => ⟨some next, pushStk c.stks k b⟩
    | some (.pop k onE onF onT) =>
      let res := popStk c.stks k
      match res.1 with
      | none => ⟨some onE, res.2⟩
      | some false => ⟨some onF, res.2⟩
      | some true => ⟨some onT, res.2⟩

lemma flatStep_halted (prog : List FlatInstr) (stks : List (List Bool)) (t : ℕ) :
    (flatStep prog)^[t] ⟨none, stks⟩ = ⟨none, stks⟩ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih]; rfl

lemma flatStep_add (prog : List FlatInstr) (t₁ t₂ : ℕ) (c₀ c₁ c₂ : FlatCfg)
    (h₁ : (flatStep prog)^[t₁] c₀ = c₁)
    (h₂ : (flatStep prog)^[t₂] c₁ = c₂) :
    (flatStep prog)^[t₁ + t₂] c₀ = c₂ := by
  rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]

def FlatReachesIn (prog : List FlatInstr) (c₁ c₂ : FlatCfg) (budget : ℕ) : Prop :=
  ∃ t ≤ budget, (flatStep prog)^[t] c₁ = c₂

lemma FlatReachesIn.refl (prog : List FlatInstr) (c : FlatCfg) :
    FlatReachesIn prog c c 0 := ⟨0, le_rfl, rfl⟩

lemma FlatReachesIn.step {prog : List FlatInstr} {c₁ c₂ : FlatCfg}
    (h : flatStep prog c₁ = c₂) : FlatReachesIn prog c₁ c₂ 1 :=
  ⟨1, le_rfl, h⟩

lemma FlatReachesIn.trans {prog : List FlatInstr} {c₁ c₂ c₃ : FlatCfg} {b₁ b₂ : ℕ}
    (h₁ : FlatReachesIn prog c₁ c₂ b₁) (h₂ : FlatReachesIn prog c₂ c₃ b₂) :
    FlatReachesIn prog c₁ c₃ (b₁ + b₂) := by
  obtain ⟨t₁, ht₁, he₁⟩ := h₁
  obtain ⟨t₂, ht₂, he₂⟩ := h₂
  exact ⟨t₁ + t₂, by omega, flatStep_add prog t₁ t₂ c₁ c₂ c₃ he₁ he₂⟩

lemma FlatReachesIn.mono {prog : List FlatInstr} {c₁ c₂ : FlatCfg} {b₁ b₂ : ℕ}
    (h : FlatReachesIn prog c₁ c₂ b₁) (hb : b₁ ≤ b₂) : FlatReachesIn prog c₁ c₂ b₂ := by
  obtain ⟨t, ht, he⟩ := h
  exact ⟨t, ht.trans hb, he⟩

lemma FlatReachesIn.to_exact_halted {prog : List FlatInstr} {c₀ : FlatCfg}
    {stks : List (List Bool)} {B : ℕ}
    (h : FlatReachesIn prog c₀ ⟨none, stks⟩ B) :
    (flatStep prog)^[B] c₀ = ⟨none, stks⟩ := by
  obtain ⟨t, ht, he⟩ := h
  have hrem : B = t + (B - t) := by omega
  rw [hrem]
  exact flatStep_add prog t (B - t) c₀ ⟨none, stks⟩ ⟨none, stks⟩ he
    (flatStep_halted prog stks (B - t))

def flatEval (prog : List FlatInstr) (inp : List Bool) (steps : ℕ) : Bool :=
  let c := (flatStep prog)^[steps] ⟨some 0, [inp]⟩
  c.pc.isNone && ((getStk c.stks 0).head?.getD false)

/- ### Micro-code emitters for pushing and popping unary-indexed symbols -/

lemma getElem?_append_singleton {α : Type*} (xs : List α) (x : α) :
    (xs ++ [x])[xs.length]? = some x := by
  rw [List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

def emitPushFalses (base stk : ℕ) : ℕ → ℕ → List FlatInstr → ℕ × List FlatInstr
  | 0, afterPc, code => (afterPc, code)
  | r + 1, afterPc, code =>
    let (nextPc, code') := emitPushFalses base stk r afterPc code
    let myPc := base + code'.length
    (myPc, code' ++ [.push stk false nextPc])

def emitPushSym (base stk r afterPc : ℕ) (code : List FlatInstr) : ℕ × List FlatInstr :=
  let (falsesPc, code') := emitPushFalses base stk r afterPc code
  let myPc := base + code'.length
  (myPc, code' ++ [.push stk true falsesPc])

lemma emitPushFalses_prefix (base stk r afterPc : ℕ) (code : List FlatInstr) :
    ∃ ext, (emitPushFalses base stk r afterPc code).2 = code ++ ext := by
  induction r generalizing afterPc code with
  | zero => exact ⟨[], by simp [emitPushFalses]⟩
  | succ r ih =>
    dsimp only [emitPushFalses]
    obtain ⟨ext, hext⟩ := ih afterPc code
    exact ⟨ext ++ [.push stk false (emitPushFalses base stk r afterPc code).1],
      by rw [hext, List.append_assoc]⟩

lemma emitPushSym_prefix (base stk r afterPc : ℕ) (code : List FlatInstr) :
    ∃ ext, (emitPushSym base stk r afterPc code).2 = code ++ ext := by
  dsimp only [emitPushSym]
  obtain ⟨ext, hext⟩ := emitPushFalses_prefix base stk r afterPc code
  exact ⟨ext ++ [.push stk true (emitPushFalses base stk r afterPc code).1],
    by rw [hext, List.append_assoc]⟩

lemma replicate_false_cons_comm (r : ℕ) (s : List Bool) :
    List.replicate r false ++ false :: s = false :: (List.replicate r false ++ s) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [List.replicate_succ, List.cons_append]
    rw [ih]

lemma pushStk_iter_false (prog : List FlatInstr) (base stk : ℕ) :
    ∀ (r afterPc : ℕ) (code : List FlatInstr) (stks : List (List Bool)),
      (∀ i < (emitPushFalses base stk r afterPc code).2.length,
        prog[base + i]? = (emitPushFalses base stk r afterPc code).2[i]?) →
      ∃ stks',
        FlatReachesIn prog ⟨some (emitPushFalses base stk r afterPc code).1, stks⟩
          ⟨some afterPc, stks'⟩ r ∧
        getStk stks' stk = List.replicate r false ++ getStk stks stk ∧
        ∀ j, j ≠ stk → getStk stks' j = getStk stks j
  | 0, afterPc, _, stks, _ =>
    ⟨stks, FlatReachesIn.refl _ _, by simp, fun _ _ => rfl⟩
  | r + 1, afterPc, code, stks, hprog => by
    dsimp only [emitPushFalses] at hprog ⊢
    let res := emitPushFalses base stk r afterPc code
    have hlen_lt : res.2.length < (res.2 ++ [FlatInstr.push stk false res.1]).length := by simp
    have hmy : prog[base + res.2.length]? = some (.push stk false res.1) := by
      rw [hprog res.2.length hlen_lt]
      exact getElem?_append_singleton res.2 _
    have hstep1 : flatStep prog ⟨some (base + res.2.length), stks⟩ =
        ⟨some res.1, pushStk stks stk false⟩ := by
      change (match prog[base + res.2.length]? with
        | none => _ | some .halt => _ | some (.jump _) => _
        | some (.push k b next) => _ | some (.pop _ _ _ _) => _) = _
      rw [hmy]
    have hprog_inner : ∀ i < res.2.length, prog[base + i]? = res.2[i]? := by
      intro i hi
      rw [hprog i (Nat.lt_trans hi hlen_lt), List.getElem?_append_left hi]
    obtain ⟨stks', hreach, hself, hother⟩ :=
      pushStk_iter_false prog base stk r afterPc code (pushStk stks stk false) hprog_inner
    refine ⟨stks', ?_, ?_, ?_⟩
    · have htr := (FlatReachesIn.step hstep1).trans hreach
      simpa [Nat.add_comm] using htr
    · rw [hself, getStk_pushStk_self, List.replicate_succ, List.cons_append,
        replicate_false_cons_comm]
    · intro j hj
      rw [hother j hj, getStk_pushStk_ne _ _ hj]

lemma emitPushSym_spec (prog : List FlatInstr) (base stk r afterPc : ℕ)
    (code : List FlatInstr) (stks : List (List Bool))
    (hprog : ∀ i < (emitPushSym base stk r afterPc code).2.length,
      prog[base + i]? = (emitPushSym base stk r afterPc code).2[i]?) :
    ∃ stks',
      FlatReachesIn prog ⟨some (emitPushSym base stk r afterPc code).1, stks⟩
        ⟨some afterPc, stks'⟩ (r + 1) ∧
      getStk stks' stk = (List.replicate r false ++ [true]) ++ getStk stks stk ∧
      ∀ j, j ≠ stk → getStk stks' j = getStk stks j := by
  dsimp only [emitPushSym] at hprog ⊢
  let res := emitPushFalses base stk r afterPc code
  have hlen_lt : res.2.length < (res.2 ++ [FlatInstr.push stk true res.1]).length := by simp
  have hmy : prog[base + res.2.length]? = some (.push stk true res.1) := by
    rw [hprog res.2.length hlen_lt]
    exact getElem?_append_singleton res.2 _
  have hstep1 : flatStep prog ⟨some (base + res.2.length), stks⟩ =
      ⟨some res.1, pushStk stks stk true⟩ := by
    change (match prog[base + res.2.length]? with
      | none => _ | some .halt => _ | some (.jump _) => _
      | some (.push k b next) => _ | some (.pop _ _ _ _) => _) = _
    rw [hmy]
  have hprog_inner : ∀ i < res.2.length, prog[base + i]? = res.2[i]? := by
    intro i hi
    rw [hprog i (Nat.lt_trans hi hlen_lt), List.getElem?_append_left hi]
  obtain ⟨stks', hreach, hself, hother⟩ :=
    pushStk_iter_false prog base stk r afterPc code (pushStk stks stk true) hprog_inner
  refine ⟨stks', ?_, ?_, ?_⟩
  · have htr := (FlatReachesIn.step hstep1).trans hreach
    simpa [Nat.add_comm] using htr
  · rw [hself, getStk_pushStk_self, List.append_assoc, List.singleton_append]
  · intro j hj
    rw [hother j hj, getStk_pushStk_ne _ _ hj]

def emitPopChain (base stk emptyPc : ℕ) : List ℕ → List FlatInstr → ℕ × List FlatInstr
  | [], code => (emptyPc, code)
  | t :: ts, code =>
    let (restPc, code') := emitPopChain base stk emptyPc ts code
    let myPc := base + code'.length
    (myPc, code' ++ [.pop stk emptyPc restPc t])

lemma emitPopChain_prefix (base stk emptyPc : ℕ) (targets : List ℕ) (code : List FlatInstr) :
    ∃ ext, (emitPopChain base stk emptyPc targets code).2 = code ++ ext := by
  induction targets generalizing code with
  | nil => exact ⟨[], by simp [emitPopChain]⟩
  | cons t ts ih =>
    dsimp only [emitPopChain]
    obtain ⟨ext, hext⟩ := ih code
    exact ⟨ext ++ [.pop stk emptyPc (emitPopChain base stk emptyPc ts code).1 t],
      by rw [hext, List.append_assoc]⟩

lemma emitPopChain_empty (prog : List FlatInstr) (base stk emptyPc : ℕ) :
    ∀ (targets : List ℕ) (code : List FlatInstr) (stks : List (List Bool)),
      getStk stks stk = [] →
      (∀ i < (emitPopChain base stk emptyPc targets code).2.length,
        prog[base + i]? = (emitPopChain base stk emptyPc targets code).2[i]?) →
      ∃ stks',
        FlatReachesIn prog ⟨some (emitPopChain base stk emptyPc targets code).1, stks⟩
          ⟨some emptyPc, stks'⟩ 1 ∧
        getStk stks' stk = [] ∧
        ∀ j, j ≠ stk → getStk stks' j = getStk stks j
  | [], _, stks, hemp, _ =>
    ⟨stks, (FlatReachesIn.refl _ _).mono (by omega), hemp, fun _ _ => rfl⟩
  | t :: ts, code, stks, hemp, hprog => by
    dsimp only [emitPopChain] at hprog ⊢
    let res := emitPopChain base stk emptyPc ts code
    have hlen_lt : res.2.length < (res.2 ++ [FlatInstr.pop stk emptyPc res.1 t]).length := by simp
    have hmy : prog[base + res.2.length]? = some (.pop stk emptyPc res.1 t) := by
      rw [hprog res.2.length hlen_lt]
      exact getElem?_append_singleton res.2 _
    have hfst : (popStk stks stk).1 = none := by rw [fst_popStk, hemp]; rfl
    refine ⟨(popStk stks stk).2, FlatReachesIn.step ?_, ?_, ?_⟩
    · change (match prog[base + res.2.length]? with
        | none => _ | some .halt => _ | some (.jump _) => _
        | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
      rw [hmy]
      dsimp only
      rw [hfst]
    · rw [getStk_popStk_self, hemp]; rfl
    · intro j hj; exact getStk_popStk_ne stks hj

lemma emitPopChain_sym (prog : List FlatInstr) (base stk emptyPc : ℕ) :
    ∀ (targets : List ℕ) (idx : ℕ) (hidx : idx < targets.length)
      (code : List FlatInstr) (stks : List (List Bool)) (restBits : List Bool),
      getStk stks stk = (List.replicate idx false ++ [true]) ++ restBits →
      (∀ i < (emitPopChain base stk emptyPc targets code).2.length,
        prog[base + i]? = (emitPopChain base stk emptyPc targets code).2[i]?) →
      ∃ stks',
        FlatReachesIn prog ⟨some (emitPopChain base stk emptyPc targets code).1, stks⟩
          ⟨some targets[idx], stks'⟩ (idx + 1) ∧
        getStk stks' stk = restBits ∧
        ∀ j, j ≠ stk → getStk stks' j = getStk stks j
  | [], _, hidx, _, _, _, _, _ => by simp at hidx
  | t :: ts, 0, _, code, stks, restBits, hstk, hprog => by
    dsimp only [emitPopChain] at hprog ⊢
    let res := emitPopChain base stk emptyPc ts code
    have hlen_lt : res.2.length < (res.2 ++ [FlatInstr.pop stk emptyPc res.1 t]).length := by simp
    have hmy : prog[base + res.2.length]? = some (.pop stk emptyPc res.1 t) := by
      rw [hprog res.2.length hlen_lt]
      exact getElem?_append_singleton res.2 _
    simp only [List.replicate_zero, List.nil_append, List.singleton_append] at hstk
    have hfst : (popStk stks stk).1 = some true := by rw [fst_popStk, hstk]; rfl
    refine ⟨(popStk stks stk).2, FlatReachesIn.step ?_, ?_, ?_⟩
    · change (match prog[base + res.2.length]? with
        | none => _ | some .halt => _ | some (.jump _) => _
        | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
      rw [hmy]
      dsimp only
      rw [hfst]
      rfl
    · rw [getStk_popStk_self, hstk]; rfl
    · intro j hj; exact getStk_popStk_ne stks hj
  | t :: ts, idx + 1, hidx, code, stks, restBits, hstk, hprog => by
    dsimp only [emitPopChain] at hprog ⊢
    let res := emitPopChain base stk emptyPc ts code
    have hlen_lt : res.2.length < (res.2 ++ [FlatInstr.pop stk emptyPc res.1 t]).length := by simp
    have hmy : prog[base + res.2.length]? = some (.pop stk emptyPc res.1 t) := by
      rw [hprog res.2.length hlen_lt]
      exact getElem?_append_singleton res.2 _
    rw [List.replicate_succ, List.cons_append, List.cons_append] at hstk
    have hfst : (popStk stks stk).1 = some false := by rw [fst_popStk, hstk]; rfl
    have hstep1 : flatStep prog ⟨some (base + res.2.length), stks⟩ =
        ⟨some res.1, (popStk stks stk).2⟩ := by
      change (match prog[base + res.2.length]? with
        | none => _ | some .halt => _ | some (.jump _) => _
        | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
      rw [hmy]
      dsimp only
      rw [hfst]
    have hstk' : getStk (popStk stks stk).2 stk =
        (List.replicate idx false ++ [true]) ++ restBits := by
      rw [getStk_popStk_self, hstk]; rfl
    have hprog_inner : ∀ i < res.2.length, prog[base + i]? = res.2[i]? := by
      intro i hi
      rw [hprog i (Nat.lt_trans hi hlen_lt), List.getElem?_append_left hi]
    have hidx' : idx < ts.length := by simp at hidx; omega
    obtain ⟨stks', hreach, hself, hother⟩ :=
      emitPopChain_sym prog base stk emptyPc ts idx hidx' code
        (popStk stks stk).2 restBits hstk' hprog_inner
    refine ⟨stks', ?_, hself, ?_⟩
    · have htr := (FlatReachesIn.step hstep1).trans hreach
      simpa [Nat.add_comm] using htr
    · intro j hj
      rw [hother j hj, getStk_popStk_ne stks hj]

/- ### Full compiler from `FinTM2` to `List FlatInstr` -/

section CompileFinTM2

open scoped Classical

noncomputable section

def stmtPushedSyms (M : FinTM2) {nσ : ℕ} (eσ : M.σ ≃ Fin nσ) (k : M.K) :
    TM2.Stmt M.Γ M.Λ M.σ → List (M.Γ k)
  | .push k' f q =>
    (if h : k' = k then (List.finRange nσ).map (fun i => h ▸ f (eσ.symm i)) else []) ++
      stmtPushedSyms M eσ k q
  | .peek _ _ q => stmtPushedSyms M eσ k q
  | .pop _ _ q => stmtPushedSyms M eσ k q
  | .load _ q => stmtPushedSyms M eσ k q
  | .branch _ q₁ q₂ => stmtPushedSyms M eσ k q₁ ++ stmtPushedSyms M eσ k q₂
  | .goto _ => []
  | .halt => []

lemma mem_stmtPushedSyms_push (M : FinTM2) {nσ : ℕ} (eσ : M.σ ≃ Fin nσ)
    (k : M.K) (f : M.σ → M.Γ k) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) :
    f v ∈ stmtPushedSyms M eσ k (.push k f q) := by
  simp only [stmtPushedSyms, ↓reduceDIte, List.mem_append, List.mem_map]
  left
  exact ⟨eσ v, List.mem_finRange _, by simp⟩

def encodeSymList {α : Type*} (syms : List α) (L : List α) : List Bool :=
  L.flatMap (fun a => List.replicate (syms.idxOf a) false ++ [true])

@[simp]
lemma encodeSymList_nil {α : Type*} (syms : List α) : encodeSymList syms [] = [] := rfl

lemma encodeSymList_cons {α : Type*} (syms : List α) (a : α) (L : List α) :
    encodeSymList syms (a :: L) =
      (List.replicate (syms.idxOf a) false ++ [true]) ++ encodeSymList syms L := rfl

def stmtDepth {K : Type*} {Γ : K → Type*} {Λ σ : Type*} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => stmtDepth q + 1
  | .peek _ _ q => stmtDepth q + 1
  | .pop _ _ q => stmtDepth q + 1
  | .load _ q => stmtDepth q + 1
  | .branch _ q₁ q₂ => max (stmtDepth q₁) (stmtDepth q₂) + 1
  | .goto _ => 1
  | .halt => 1

def compileSymBranches {α : Type*}
    (compileOne : α → List FlatInstr → ℕ × List FlatInstr) :
    List α → List FlatInstr → List ℕ × List FlatInstr
  | [], code => ([], code)
  | a :: as, code =>
    let (pc_a, code₁) := compileOne a code
    let (pcs, code₂) := compileSymBranches compileOne as code₁
    (pc_a :: pcs, code₂)

lemma compileSymBranches_length {α : Type*}
    (compileOne : α → List FlatInstr → ℕ × List FlatInstr)
    (as : List α) (code : List FlatInstr) :
    (compileSymBranches compileOne as code).1.length = as.length := by
  induction as generalizing code with
  | nil => rfl
  | cons a as ih => simp [compileSymBranches, ih]

lemma compileSymBranches_prefix {α : Type*}
    (compileOne : α → List FlatInstr → ℕ × List FlatInstr)
    (hpref : ∀ a c, ∃ ext, (compileOne a c).2 = c ++ ext)
    (as : List α) (code : List FlatInstr) :
    ∃ ext, (compileSymBranches compileOne as code).2 = code ++ ext := by
  induction as generalizing code with
  | nil => exact ⟨[], by simp [compileSymBranches]⟩
  | cons a as ih =>
    dsimp only [compileSymBranches]
    obtain ⟨ext₁, hext₁⟩ := hpref a code
    obtain ⟨ext₂, hext₂⟩ := ih (compileOne a code).2
    exact ⟨ext₁ ++ ext₂, by rw [hext₂, hext₁, List.append_assoc]⟩

lemma compileSymBranches_spec {α : Type*} (prog : List FlatInstr) (base : ℕ)
    (compileOne : α → List FlatInstr → ℕ × List FlatInstr)
    (hpref : ∀ a c, ∃ ext, (compileOne a c).2 = c ++ ext) :
    ∀ (as : List α) (idx : ℕ) (hidx : idx < as.length) (code : List FlatInstr),
      (∀ i < (compileSymBranches compileOne as code).2.length,
        prog[base + i]? = (compileSymBranches compileOne as code).2[i]?) →
      ∃ c_sub,
        (compileSymBranches compileOne as code).1[idx]'(by rw [compileSymBranches_length]; exact hidx) =
          (compileOne as[idx] c_sub).1 ∧
        ∀ i < (compileOne as[idx] c_sub).2.length,
          prog[base + i]? = (compileOne as[idx] c_sub).2[i]?
  | [], _, hidx, _, _ => by simp at hidx
  | a :: as, 0, _, code, hprog => by
    dsimp only [compileSymBranches, List.getElem_cons_zero] at hprog ⊢
    obtain ⟨ext₂, hext₂⟩ := compileSymBranches_prefix compileOne hpref as (compileOne a code).2
    refine ⟨code, rfl, ?_⟩
    intro i hi
    have hlen : i < (compileSymBranches compileOne as (compileOne a code).2).2.length := by
      rw [hext₂, List.length_append]
      omega
    rw [hprog i hlen]
    conv_lhs => rw [hext₂]
    exact List.getElem?_append_left hi
  | a :: as, idx + 1, hidx, code, hprog => by
    dsimp only [compileSymBranches] at hprog ⊢
    have hidx' : idx < as.length := by simp at hidx; omega
    exact compileSymBranches_spec prog base compileOne hpref as idx hidx'
      (compileOne a code).2 hprog

def compileStmt (M : FinTM2)
    {nK : ℕ} (eK : M.K ≃ Fin nK) (syms : ∀ k, List (M.Γ k))
    (trampPc : M.Λ → M.σ → ℕ) (epiloguePc base : ℕ) :
    TM2.Stmt M.Γ M.Λ M.σ → M.σ → List FlatInstr → ℕ × List FlatInstr
  | .halt, _, code => (epiloguePc, code)
  | .goto f, v, code => (trampPc (f v) v, code)
  | .load a q, v, code => compileStmt M eK syms trampPc epiloguePc base q (a v) code
  | .branch f q₁ q₂, v, code =>
    if f v then
      compileStmt M eK syms trampPc epiloguePc base q₁ v code
    else
      compileStmt M eK syms trampPc epiloguePc base q₂ v code
  | .push k f q, v, code =>
    let (afterPc, code₁) := compileStmt M eK syms trampPc epiloguePc base q v code
    let stk := 2 + (eK k).val
    let r := (syms k).idxOf (f v)
    emitPushSym base stk r afterPc code₁
  | .pop k f q, v, code =>
    let stk := 2 + (eK k).val
    let (emptyPc, code₁) := compileStmt M eK syms trampPc epiloguePc base q (f v none) code
    let (targets, code₂) := compileSymBranches
      (fun a c => compileStmt M eK syms trampPc epiloguePc base q (f v (some a)) c)
      (syms k) code₁
    emitPopChain base stk emptyPc targets code₂
  | .peek k f q, v, code =>
    let stk := 2 + (eK k).val
    let (emptyPc, code₁) := compileStmt M eK syms trampPc epiloguePc base q (f v none) code
    let (targets, code₂) := compileSymBranches
      (fun a c =>
        let (afterPc, c₁) := compileStmt M eK syms trampPc epiloguePc base q (f v (some a)) c
        emitPushSym base stk ((syms k).idxOf a) afterPc c₁)
      (syms k) code₁
    emitPopChain base stk emptyPc targets code₂

lemma compileStmt_prefix (M : FinTM2)
    {nK : ℕ} (eK : M.K ≃ Fin nK) (syms : ∀ k, List (M.Γ k))
    (trampPc : M.Λ → M.σ → ℕ) (epiloguePc base : ℕ) :
    ∀ (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (code : List FlatInstr),
      ∃ ext, (compileStmt M eK syms trampPc epiloguePc base q v code).2 = code ++ ext
  | .halt, _, _ => ⟨[], by simp [compileStmt]⟩
  | .goto _, _, _ => ⟨[], by simp [compileStmt]⟩
  | .load a q, v, code => compileStmt_prefix M eK syms trampPc epiloguePc base q (a v) code
  | .branch f q₁ q₂, v, code => by
    dsimp only [compileStmt]
    split_ifs
    · exact compileStmt_prefix M eK syms trampPc epiloguePc base q₁ v code
    · exact compileStmt_prefix M eK syms trampPc epiloguePc base q₂ v code
  | .push k f q, v, code => by
    dsimp only [compileStmt]
    obtain ⟨ext₁, hext₁⟩ := compileStmt_prefix M eK syms trampPc epiloguePc base q v code
    obtain ⟨ext₂, hext₂⟩ := emitPushSym_prefix base (2 + (eK k).val) ((syms k).idxOf (f v))
      (compileStmt M eK syms trampPc epiloguePc base q v code).1
      (compileStmt M eK syms trampPc epiloguePc base q v code).2
    exact ⟨ext₁ ++ ext₂, by rw [hext₂, hext₁, List.append_assoc]⟩
  | .pop k f q, v, code => by
    dsimp only [compileStmt]
    obtain ⟨ext₁, hext₁⟩ := compileStmt_prefix M eK syms trampPc epiloguePc base q (f v none) code
    obtain ⟨ext₂, hext₂⟩ := compileSymBranches_prefix
      (fun a c => compileStmt M eK syms trampPc epiloguePc base q (f v (some a)) c)
      (fun a c => compileStmt_prefix M eK syms trampPc epiloguePc base q (f v (some a)) c)
      (syms k) (compileStmt M eK syms trampPc epiloguePc base q (f v none) code).2
    obtain ⟨ext₃, hext₃⟩ := emitPopChain_prefix base (2 + (eK k).val) _ _ _
    exact ⟨ext₁ ++ ext₂ ++ ext₃, by rw [hext₃, hext₂, hext₁]; simp only [List.append_assoc]⟩
  | .peek k f q, v, code => by
    dsimp only [compileStmt]
    obtain ⟨ext₁, hext₁⟩ := compileStmt_prefix M eK syms trampPc epiloguePc base q (f v none) code
    have hbr : ∀ a c, ∃ ext,
        (let p := compileStmt M eK syms trampPc epiloguePc base q (f v (some a)) c
         emitPushSym base (2 + (eK k).val) ((syms k).idxOf a) p.1 p.2).2 = c ++ ext := by
      intro a c
      obtain ⟨e₁, he₁⟩ := compileStmt_prefix M eK syms trampPc epiloguePc base q (f v (some a)) c
      obtain ⟨e₂, he₂⟩ := emitPushSym_prefix base (2 + (eK k).val) ((syms k).idxOf a) _ _
      exact ⟨e₁ ++ e₂, by dsimp only; rw [he₂, he₁, List.append_assoc]⟩
    obtain ⟨ext₂, hext₂⟩ := compileSymBranches_prefix _ hbr (syms k) _
    obtain ⟨ext₃, hext₃⟩ := emitPopChain_prefix base (2 + (eK k).val) _ _ _
    exact ⟨ext₁ ++ ext₂ ++ ext₃, by rw [hext₃, hext₂, hext₁]; simp only [List.append_assoc]⟩

def cfgTargetPc (M : FinTM2) (trampPc : M.Λ → M.σ → ℕ) (epiloguePc : ℕ) (c : M.Cfg) : ℕ :=
  match c.l with
  | some l => trampPc l c.var
  | none => epiloguePc

def SimStacks (M : FinTM2) {nK : ℕ} (eK : M.K ≃ Fin nK) (syms : ∀ k, List (M.Γ k))
    (S : ∀ k, List (M.Γ k)) (stks : List (List Bool)) : Prop :=
  getStk stks 0 = [] ∧ getStk stks 1 = [] ∧
  (∀ k, ∀ a ∈ S k, a ∈ syms k) ∧
  (∀ k, getStk stks (2 + (eK k).val) = encodeSymList (syms k) (S k))

lemma compileStmt_spec (M : FinTM2) (prog : List FlatInstr)
    {nσ nK : ℕ} (eσ : M.σ ≃ Fin nσ) (eK : M.K ≃ Fin nK)
    (syms : ∀ k, List (M.Γ k)) (W : ℕ)
    (hW : ∀ k, (syms k).length ≤ W)
    (trampPc : M.Λ → M.σ → ℕ) (epiloguePc base : ℕ) :
    ∀ (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (code : List FlatInstr)
      (S : ∀ k, List (M.Γ k)) (stks : List (List Bool)),
      (∀ k a, a ∈ stmtPushedSyms M eσ k q → a ∈ syms k) →
      SimStacks M eK syms S stks →
      (∀ i < (compileStmt M eK syms trampPc epiloguePc base q v code).2.length,
        prog[base + i]? = (compileStmt M eK syms trampPc epiloguePc base q v code).2[i]?) →
      ∃ stks',
        FlatReachesIn prog ⟨some (compileStmt M eK syms trampPc epiloguePc base q v code).1, stks⟩
          ⟨some (cfgTargetPc M trampPc epiloguePc (TM2.stepAux q v S)), stks'⟩
          ((2 * W + 2) * stmtDepth q) ∧
        SimStacks M eK syms (TM2.stepAux q v S).stk stks'
  | .halt, _, _, _, stks, _, hsim, _ =>
    ⟨stks, (FlatReachesIn.refl _ _).mono (by omega), hsim⟩
  | .goto _, _, _, _, stks, _, hsim, _ =>
    ⟨stks, (FlatReachesIn.refl _ _).mono (by omega), hsim⟩
  | .load a q, v, code, S, stks, hpush, hsim, hprog => by
    dsimp only [compileStmt, TM2.stepAux, stmtDepth] at hprog ⊢
    obtain ⟨stks', hreach, hsim'⟩ :=
      compileStmt_spec M prog eσ eK syms W hW trampPc epiloguePc base
        q (a v) code S stks hpush hsim hprog
    exact ⟨stks', hreach.mono (Nat.mul_le_mul_left _ (by omega)), hsim'⟩
  | .branch f q₁ q₂, v, code, S, stks, hpush, hsim, hprog => by
    dsimp only [compileStmt, TM2.stepAux, stmtDepth] at hprog ⊢
    cases hfv : f v with
    | true =>
      simp only [hfv, ↓reduceIte, cond_true] at hprog ⊢
      have hp1 : ∀ k a, a ∈ stmtPushedSyms M eσ k q₁ → a ∈ syms k :=
        fun k a ha => hpush k a (by simp [stmtPushedSyms, ha])
      obtain ⟨stks', hreach, hsim'⟩ :=
        compileStmt_spec M prog eσ eK syms W hW trampPc epiloguePc base
          q₁ v code S stks hp1 hsim hprog
      exact ⟨stks', hreach.mono (Nat.mul_le_mul_left _ (by omega)), hsim'⟩
    | false =>
      simp only [hfv, Bool.false_eq_true, ↓reduceIte, cond_false] at hprog ⊢
      have hp2 : ∀ k a, a ∈ stmtPushedSyms M eσ k q₂ → a ∈ syms k :=
        fun k a ha => hpush k a (by simp [stmtPushedSyms, ha])
      obtain ⟨stks', hreach, hsim'⟩ :=
        compileStmt_spec M prog eσ eK syms W hW trampPc epiloguePc base
          q₂ v code S stks hp2 hsim hprog
      exact ⟨stks', hreach.mono (Nat.mul_le_mul_left _ (by omega)), hsim'⟩
  | .push k f q, v, code, S, stks, hpush, hsim, hprog => by
    dsimp only [compileStmt, TM2.stepAux, stmtDepth] at hprog ⊢
    let sub := compileStmt M eK syms trampPc epiloguePc base q v code
    let stk := 2 + (eK k).val
    let r := (syms k).idxOf (f v)
    obtain ⟨stks₁, hreach₁, hself₁, hother₁⟩ :=
      emitPushSym_spec prog base stk r sub.1 sub.2 stks hprog
    have hfv_mem : f v ∈ syms k :=
      hpush k (f v) (mem_stmtPushedSyms_push M eσ k f q v)
    have hr_lt : r < (syms k).length := List.idxOf_lt_length_of_mem hfv_mem
    have hr_le : r + 1 ≤ 2 * W + 2 := by have := hW k; omega
    have hsim₁ : SimStacks M eK syms (Function.update S k (f v :: S k)) stks₁ := by
      refine ⟨(hother₁ 0 (by omega)).trans hsim.1, (hother₁ 1 (by omega)).trans hsim.2.1, ?_, ?_⟩
      · intro k' a ha
        by_cases hk' : k' = k
        · subst hk'
          rw [Function.update_self, List.mem_cons] at ha
          exact ha.elim (fun h => h ▸ hfv_mem) (hsim.2.2.1 k' a)
        · rw [Function.update_of_ne hk'] at ha
          exact hsim.2.2.1 k' a ha
      · intro k'
        by_cases hk' : k' = k
        · subst hk'
          rw [Function.update_self, hself₁, hsim.2.2.2 k', encodeSymList_cons]
        · rw [Function.update_of_ne hk',
            hother₁ (2 + (eK k').val) (fun heq => hk' (eK.injective (Fin.ext (by omega))))]
          exact hsim.2.2.2 k'
    obtain ⟨ext_p, hext_p⟩ := emitPushSym_prefix base stk r sub.1 sub.2
    have hprog_sub : ∀ i < sub.2.length, prog[base + i]? = sub.2[i]? := by
      intro i hi
      have hlen : i < (emitPushSym base stk r sub.1 sub.2).2.length := by
        rw [hext_p, List.length_append]; omega
      rw [hprog i hlen, hext_p, List.getElem?_append_left hi]
    have hp_q : ∀ k' a, a ∈ stmtPushedSyms M eσ k' q → a ∈ syms k' :=
      fun k' a ha => hpush k' a (by simp [stmtPushedSyms, ha])
    obtain ⟨stks₂, hreach₂, hsim₂⟩ :=
      compileStmt_spec M prog eσ eK syms W hW trampPc epiloguePc base
        q v code (Function.update S k (f v :: S k)) stks₁ hp_q hsim₁ hprog_sub
    refine ⟨stks₂, (hreach₁.trans hreach₂).mono ?_, hsim₂⟩
    rw [Nat.mul_succ]
    omega
  | .pop k f q, v, code, S, stks, hpush, hsim, hprog => by
    dsimp only [compileStmt, TM2.stepAux, stmtDepth] at hprog ⊢
    let stk := 2 + (eK k).val
    let subNone := compileStmt M eK syms trampPc epiloguePc base q (f v none) code
    let compOne := fun a c => compileStmt M eK syms trampPc epiloguePc base q (f v (some a)) c
    let branches := compileSymBranches compOne (syms k) subNone.2
    have hp_q : ∀ k' a, a ∈ stmtPushedSyms M eσ k' q → a ∈ syms k' :=
      fun k' a ha => hpush k' a (by simp [stmtPushedSyms, ha])
    have hpref_one : ∀ a c, ∃ ext, (compOne a c).2 = c ++ ext :=
      fun a c => compileStmt_prefix M eK syms trampPc epiloguePc base q (f v (some a)) c
    obtain ⟨ext_pop, hext_pop⟩ := emitPopChain_prefix base stk subNone.1 branches.1 branches.2
    have hprog_br : ∀ i < branches.2.length, prog[base + i]? = branches.2[i]? := by
      intro i hi
      have hlen : i < (emitPopChain base stk subNone.1 branches.1 branches.2).2.length := by
        rw [hext_pop, List.length_append]; omega
      rw [hprog i hlen, hext_pop, List.getElem?_append_left hi]
    cases hSk : S k with
    | nil =>
      have hemp_stk : getStk stks stk = [] := by
        rw [hsim.2.2.2 k, hSk]; rfl
      obtain ⟨stks₁, hreach₁, hself₁, hother₁⟩ :=
        emitPopChain_empty prog base stk subNone.1 branches.1 branches.2 stks hemp_stk hprog
      obtain ⟨ext_br, hext_br⟩ := compileSymBranches_prefix compOne hpref_one (syms k) subNone.2
      have hprog_none : ∀ i < subNone.2.length, prog[base + i]? = subNone.2[i]? := by
        intro i hi
        have hlen : i < branches.2.length := by
          dsimp [branches]; rw [hext_br, List.length_append]; omega
        rw [hprog_br i hlen]
        dsimp [branches]
        rw [hext_br, List.getElem?_append_left hi]
      have hsim₁ : SimStacks M eK syms (Function.update S k []) stks₁ := by
        refine ⟨(hother₁ 0 (by omega)).trans hsim.1, (hother₁ 1 (by omega)).trans hsim.2.1, ?_, ?_⟩
        · intro k' a ha
          by_cases hk' : k' = k
          · subst hk'; simp at ha
          · rw [Function.update_of_ne hk'] at ha; exact hsim.2.2.1 k' a ha
        · intro k'
          by_cases hk' : k' = k
          · subst hk'; rw [Function.update_self, hself₁]; rfl
          · rw [Function.update_of_ne hk',
              hother₁ (2 + (eK k').val) (fun heq => hk' (eK.injective (Fin.ext (by omega))))]
            exact hsim.2.2.2 k'
      obtain ⟨stks₂, hreach₂, hsim₂⟩ :=
        compileStmt_spec M prog eσ eK syms W hW trampPc epiloguePc base
          q (f v none) code (Function.update S k []) stks₁ hp_q hsim₁ hprog_none
      simp only [List.head?_nil, List.tail_nil]
      refine ⟨stks₂, (hreach₁.trans hreach₂).mono ?_, hsim₂⟩
      rw [Nat.mul_succ]; omega
    | cons a rest =>
      have ha_mem : a ∈ syms k := hsim.2.2.1 k a (hSk ▸ List.mem_cons_self)
      let idx := (syms k).idxOf a
      have hidx_lt : idx < (syms k).length := List.idxOf_lt_length_of_mem ha_mem
      have hidx_br : idx < branches.1.length := by
        dsimp [branches]; rwa [compileSymBranches_length]
      have hget_a : (syms k)[idx] = a := List.getElem_idxOf hidx_lt
      have hstk_enc : getStk stks stk =
          (List.replicate idx false ++ [true]) ++ encodeSymList (syms k) rest := by
        rw [hsim.2.2.2 k, hSk, encodeSymList_cons]
      obtain ⟨stks₁, hreach₁, hself₁, hother₁⟩ :=
        emitPopChain_sym prog base stk subNone.1 branches.1 idx hidx_br branches.2
          stks (encodeSymList (syms k) rest) hstk_enc hprog
      obtain ⟨c_sub, htarget_eq, hprog_sub⟩ :=
        compileSymBranches_spec prog base compOne hpref_one (syms k) idx hidx_lt subNone.2 hprog_br
      have hsim₁ : SimStacks M eK syms (Function.update S k rest) stks₁ := by
        refine ⟨(hother₁ 0 (by omega)).trans hsim.1, (hother₁ 1 (by omega)).trans hsim.2.1, ?_, ?_⟩
        · intro k' x hx
          by_cases hk' : k' = k
          · subst hk'
            rw [Function.update_self] at hx
            exact hsim.2.2.1 k' x (hSk ▸ List.mem_cons_of_mem _ hx)
          · rw [Function.update_of_ne hk'] at hx; exact hsim.2.2.1 k' x hx
        · intro k'
          by_cases hk' : k' = k
          · subst hk'; rw [Function.update_self, hself₁]
          · rw [Function.update_of_ne hk',
              hother₁ (2 + (eK k').val) (fun heq => hk' (eK.injective (Fin.ext (by omega))))]
            exact hsim.2.2.2 k'
      rw [htarget_eq] at hreach₁
      dsimp only [compOne] at hreach₁ hprog_sub
      rw [hget_a] at hreach₁ hprog_sub
      obtain ⟨stks₂, hreach₂, hsim₂⟩ :=
        compileStmt_spec M prog eσ eK syms W hW trampPc epiloguePc base
          q (f v (some a)) c_sub (Function.update S k rest) stks₁ hp_q hsim₁ hprog_sub
      simp only [List.head?_cons, List.tail_cons]
      refine ⟨stks₂, (hreach₁.trans hreach₂).mono ?_, hsim₂⟩
      have hleW : idx ≤ W := by have := hW k; omega
      rw [Nat.mul_succ]; omega
  | .peek k f q, v, code, S, stks, hpush, hsim, hprog => by
    dsimp only [compileStmt, TM2.stepAux, stmtDepth] at hprog ⊢
    let stk := 2 + (eK k).val
    let subNone := compileStmt M eK syms trampPc epiloguePc base q (f v none) code
    let compOne := fun a c =>
      let p := compileStmt M eK syms trampPc epiloguePc base q (f v (some a)) c
      emitPushSym base stk ((syms k).idxOf a) p.1 p.2
    let branches := compileSymBranches compOne (syms k) subNone.2
    have hp_q : ∀ k' a, a ∈ stmtPushedSyms M eσ k' q → a ∈ syms k' :=
      fun k' a ha => hpush k' a (by simp [stmtPushedSyms, ha])
    have hpref_one : ∀ a c, ∃ ext, (compOne a c).2 = c ++ ext := by
      intro a c
      obtain ⟨e₁, he₁⟩ := compileStmt_prefix M eK syms trampPc epiloguePc base q (f v (some a)) c
      obtain ⟨e₂, he₂⟩ := emitPushSym_prefix base stk ((syms k).idxOf a) _ _
      exact ⟨e₁ ++ e₂, by dsimp only [compOne]; rw [he₂, he₁, List.append_assoc]⟩
    obtain ⟨ext_pop, hext_pop⟩ := emitPopChain_prefix base stk subNone.1 branches.1 branches.2
    have hprog_br : ∀ i < branches.2.length, prog[base + i]? = branches.2[i]? := by
      intro i hi
      have hlen : i < (emitPopChain base stk subNone.1 branches.1 branches.2).2.length := by
        rw [hext_pop, List.length_append]; omega
      rw [hprog i hlen, hext_pop, List.getElem?_append_left hi]
    cases hSk : S k with
    | nil =>
      have hemp_stk : getStk stks stk = [] := by
        rw [hsim.2.2.2 k, hSk]; rfl
      obtain ⟨stks₁, hreach₁, hself₁, hother₁⟩ :=
        emitPopChain_empty prog base stk subNone.1 branches.1 branches.2 stks hemp_stk hprog
      obtain ⟨ext_br, hext_br⟩ := compileSymBranches_prefix compOne hpref_one (syms k) subNone.2
      have hprog_none : ∀ i < subNone.2.length, prog[base + i]? = subNone.2[i]? := by
        intro i hi
        have hlen : i < branches.2.length := by
          dsimp [branches]; rw [hext_br, List.length_append]; omega
        rw [hprog_br i hlen]
        dsimp [branches]
        rw [hext_br, List.getElem?_append_left hi]
      have hsim₁ : SimStacks M eK syms S stks₁ := by
        refine ⟨(hother₁ 0 (by omega)).trans hsim.1, (hother₁ 1 (by omega)).trans hsim.2.1,
          hsim.2.2.1, ?_⟩
        intro k'
        by_cases hk' : k' = k
        · subst hk'; rw [hself₁, hSk]; rfl
        · rw [hother₁ (2 + (eK k').val) (fun heq => hk' (eK.injective (Fin.ext (by omega))))]
          exact hsim.2.2.2 k'
      obtain ⟨stks₂, hreach₂, hsim₂⟩ :=
        compileStmt_spec M prog eσ eK syms W hW trampPc epiloguePc base
          q (f v none) code S stks₁ hp_q hsim₁ hprog_none
      simp only [List.head?_nil]
      refine ⟨stks₂, (hreach₁.trans hreach₂).mono ?_, hsim₂⟩
      rw [Nat.mul_succ]; omega
    | cons a rest =>
      have ha_mem : a ∈ syms k := hsim.2.2.1 k a (hSk ▸ List.mem_cons_self)
      let idx := (syms k).idxOf a
      have hidx_lt : idx < (syms k).length := List.idxOf_lt_length_of_mem ha_mem
      have hidx_br : idx < branches.1.length := by
        dsimp [branches]; rwa [compileSymBranches_length]
      have hget_a : (syms k)[idx] = a := List.getElem_idxOf hidx_lt
      have hstk_enc : getStk stks stk =
          (List.replicate idx false ++ [true]) ++ encodeSymList (syms k) rest := by
        rw [hsim.2.2.2 k, hSk, encodeSymList_cons]
      obtain ⟨stks₁, hreach₁, hself₁, hother₁⟩ :=
        emitPopChain_sym prog base stk subNone.1 branches.1 idx hidx_br branches.2
          stks (encodeSymList (syms k) rest) hstk_enc hprog
      obtain ⟨c_sub, htarget_eq, hprog_sub⟩ :=
        compileSymBranches_spec prog base compOne hpref_one (syms k) idx hidx_lt subNone.2 hprog_br
      rw [htarget_eq] at hreach₁
      dsimp only [compOne] at hreach₁ hprog_sub
      rw [hget_a] at hreach₁ hprog_sub
      let subSome := compileStmt M eK syms trampPc epiloguePc base q (f v (some a)) c_sub
      obtain ⟨stks₂, hreach_push, hself₂, hother₂⟩ :=
        emitPushSym_spec prog base stk idx subSome.1 subSome.2 stks₁ hprog_sub
      have hsim₂ : SimStacks M eK syms S stks₂ := by
        refine ⟨(hother₂ 0 (by omega)).trans ((hother₁ 0 (by omega)).trans hsim.1),
          (hother₂ 1 (by omega)).trans ((hother₁ 1 (by omega)).trans hsim.2.1),
          hsim.2.2.1, ?_⟩
        intro k'
        by_cases hk' : k' = k
        · subst hk'
          rw [hself₂, hself₁, hSk, encodeSymList_cons]
        · have hne_k : 2 + (eK k').val ≠ stk :=
            fun heq => hk' (eK.injective (Fin.ext (by omega)))
          rw [hother₂ _ hne_k, hother₁ _ hne_k, hsim.2.2.2 k']
      obtain ⟨ext_ps, hext_ps⟩ := emitPushSym_prefix base stk idx subSome.1 subSome.2
      have hprog_some : ∀ i < subSome.2.length, prog[base + i]? = subSome.2[i]? := by
        intro i hi
        have hlen : i < (emitPushSym base stk idx subSome.1 subSome.2).2.length := by
          rw [hext_ps, List.length_append]; omega
        rw [hprog_sub i hlen, hext_ps, List.getElem?_append_left hi]
      obtain ⟨stks₃, hreach₃, hsim₃⟩ :=
        compileStmt_spec M prog eσ eK syms W hW trampPc epiloguePc base
          q (f v (some a)) c_sub S stks₂ hp_q hsim₂ hprog_some
      simp only [List.head?_cons]
      refine ⟨stks₃, ((hreach₁.trans hreach_push).trans hreach₃).mono ?_, hsim₃⟩
      have hleW : idx < W := lt_of_lt_of_le hidx_lt (hW k)
      rw [Nat.mul_succ]; omega

/- ### Prologue, Trampolines, Epilogue, and Full Machine Simulation -/

lemma le_foldr_max_of_mem : ∀ {l : List ℕ} {x init : ℕ}, x ∈ l → x ≤ l.foldr max init
  | [], _, _, h => by simp at h
  | _ :: _, _, _, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact (le_foldr_max_of_mem hmem).trans (Nat.le_max_right _ _)

lemma iterate_bind_none {σ : Type*} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ _ ih => rw [Function.iterate_succ_apply]; exact ih

lemma initList_stk_self (M : FinTM2) (s : List (M.Γ M.k₀)) :
    (initList M s).stk M.k₀ = s := by
  simp [initList]

lemma initList_stk_ne (M : FinTM2) (s : List (M.Γ M.k₀)) {k : M.K} (hk : k ≠ M.k₀) :
    (initList M s).stk k = [] := by
  simp [initList, hk]

lemma haltList_stk_self (M : FinTM2) (s : List (M.Γ M.k₁)) :
    (haltList M s).stk M.k₁ = s := by
  simp [haltList]

lemma prologueRev_spec (prog : List FlatInstr)
    (h0 : prog[0]? = some (.pop 0 3 1 2))
    (h1 : prog[1]? = some (.push 1 false 0))
    (h2 : prog[2]? = some (.push 1 true 0)) :
    ∀ (xs : List Bool) (stks : List (List Bool)),
      getStk stks 0 = xs →
      ∃ stks',
        FlatReachesIn prog ⟨some 0, stks⟩ ⟨some 3, stks'⟩ (2 * xs.length + 1) ∧
        getStk stks' 0 = [] ∧
        getStk stks' 1 = xs.reverse ++ getStk stks 1 ∧
        ∀ j, 2 ≤ j → getStk stks' j = getStk stks j
  | [], stks, hxs => by
    have hfst : (popStk stks 0).1 = none := by rw [fst_popStk, hxs]; rfl
    have hstep : flatStep prog ⟨some 0, stks⟩ = ⟨some 3, (popStk stks 0).2⟩ := by
      change (match prog[0]? with
        | none => _ | some .halt => _ | some (.jump _) => _
        | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
      rw [h0]; dsimp only; rw [hfst]
    refine ⟨(popStk stks 0).2, FlatReachesIn.step hstep, ?_, ?_, ?_⟩
    · rw [getStk_popStk_self, hxs]; rfl
    · simp only [List.reverse_nil, List.nil_append]
      exact getStk_popStk_ne stks (by omega)
    · intro j hj; exact getStk_popStk_ne stks (by omega)
  | b :: xs, stks, hxs => by
    have hfst : (popStk stks 0).1 = some b := by rw [fst_popStk, hxs]; rfl
    let stks₁ := (popStk stks 0).2
    have hstep0 : flatStep prog ⟨some 0, stks⟩ = ⟨some (if b then 2 else 1), stks₁⟩ := by
      change (match prog[0]? with
        | none => _ | some .halt => _ | some (.jump _) => _
        | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
      rw [h0]; dsimp only; rw [hfst]; cases b <;> rfl
    have hstep1 : flatStep prog ⟨some (if b then 2 else 1), stks₁⟩ =
        ⟨some 0, pushStk stks₁ 1 b⟩ := by
      cases b
      · change (match prog[1]? with
          | none => _ | some .halt => _ | some (.jump _) => _
          | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
        rw [h1]
      · change (match prog[2]? with
          | none => _ | some .halt => _ | some (.jump _) => _
          | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
        rw [h2]
    have hxs' : getStk (pushStk stks₁ 1 b) 0 = xs := by
      rw [getStk_pushStk_ne _ _ (by omega), getStk_popStk_self, hxs]; rfl
    obtain ⟨stks', hreach, hs0, hs1, hsj⟩ :=
      prologueRev_spec prog h0 h1 h2 xs (pushStk stks₁ 1 b) hxs'
    refine ⟨stks', ?_, hs0, ?_, ?_⟩
    · have htr := ((FlatReachesIn.step hstep0).trans (FlatReachesIn.step hstep1)).trans hreach
      refine htr.mono ?_
      simp only [List.length_cons]; omega
    · rw [hs1, getStk_pushStk_self, getStk_popStk_ne stks (by omega),
        List.reverse_cons, List.append_assoc, List.singleton_append]
    · intro j hj
      rw [hsj j hj, getStk_pushStk_ne _ _ (by omega), getStk_popStk_ne stks (by omega)]

lemma prologueEnc_spec (M : FinTM2) (eIn : M.Γ M.k₀ ≃ Bool)
    {nK : ℕ} (eK : M.K ≃ Fin nK) (syms : ∀ k, List (M.Γ k))
    (prog : List FlatInstr) (base startPc W : ℕ)
    (hW0 : (syms M.k₀).length ≤ W)
    (hmemF : eIn.symm false ∈ syms M.k₀)
    (hmemT : eIn.symm true ∈ syms M.k₀)
    (cF cT : List FlatInstr)
    (hprogF : ∀ i < (emitPushSym base (2 + (eK M.k₀).val)
        ((syms M.k₀).idxOf (eIn.symm false)) 3 cF).2.length,
      prog[base + i]? = (emitPushSym base (2 + (eK M.k₀).val)
        ((syms M.k₀).idxOf (eIn.symm false)) 3 cF).2[i]?)
    (hprogT : ∀ i < (emitPushSym base (2 + (eK M.k₀).val)
        ((syms M.k₀).idxOf (eIn.symm true)) 3 cT).2.length,
      prog[base + i]? = (emitPushSym base (2 + (eK M.k₀).val)
        ((syms M.k₀).idxOf (eIn.symm true)) 3 cT).2[i]?)
    (h3 : prog[3]? = some (.pop 1 startPc
      (emitPushSym base (2 + (eK M.k₀).val) ((syms M.k₀).idxOf (eIn.symm false)) 3 cF).1
      (emitPushSym base (2 + (eK M.k₀).val) ((syms M.k₀).idxOf (eIn.symm true)) 3 cT).1)) :
    ∀ (xs acc : List Bool) (stks : List (List Bool)),
      getStk stks 0 = [] →
      getStk stks 1 = xs →
      getStk stks (2 + (eK M.k₀).val) = encodeSymList (syms M.k₀) (acc.map eIn.symm) →
      (∀ j, j ≠ 1 → j ≠ 2 + (eK M.k₀).val → getStk stks j = []) →
      ∃ stks',
        FlatReachesIn prog ⟨some 3, stks⟩ ⟨some startPc, stks'⟩ ((W + 2) * xs.length + 1) ∧
        getStk stks' 0 = [] ∧
        getStk stks' 1 = [] ∧
        getStk stks' (2 + (eK M.k₀).val) =
          encodeSymList (syms M.k₀) ((xs.reverse ++ acc).map eIn.symm) ∧
        (∀ j, j ≠ 2 + (eK M.k₀).val → getStk stks' j = [])
  | [], acc, stks, hs0, hs1, hsk0, hsj => by
    have hfst : (popStk stks 1).1 = none := by rw [fst_popStk, hs1]; rfl
    have hstep : flatStep prog ⟨some 3, stks⟩ = ⟨some startPc, (popStk stks 1).2⟩ := by
      change (match prog[3]? with
        | none => _ | some .halt => _ | some (.jump _) => _
        | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
      rw [h3]; dsimp only; rw [hfst]
    refine ⟨(popStk stks 1).2, (FlatReachesIn.step hstep).mono (by simp), ?_, ?_, ?_, ?_⟩
    · rw [getStk_popStk_ne stks (by omega), hs0]
    · rw [getStk_popStk_self, hs1]; rfl
    · simp only [List.reverse_nil, List.nil_append]
      rw [getStk_popStk_ne stks (by omega), hsk0]
    · intro j hj
      by_cases hj1 : j = 1
      · subst hj1; rw [getStk_popStk_self, hs1]; rfl
      · rw [getStk_popStk_ne stks hj1, hsj j hj1 hj]
  | b :: xs, acc, stks, hs0, hs1, hsk0, hsj => by
    let stk₀ := 2 + (eK M.k₀).val
    let rF := (syms M.k₀).idxOf (eIn.symm false)
    let rT := (syms M.k₀).idxOf (eIn.symm true)
    have hfst : (popStk stks 1).1 = some b := by rw [fst_popStk, hs1]; rfl
    let stks₁ := (popStk stks 1).2
    have hpush_branch : ∃ stks₂,
        FlatReachesIn prog ⟨some 3, stks⟩ ⟨some 3, stks₂⟩ (W + 2) ∧
        getStk stks₂ 0 = [] ∧
        getStk stks₂ 1 = xs ∧
        getStk stks₂ stk₀ = encodeSymList (syms M.k₀) ((b :: acc).map eIn.symm) ∧
        (∀ j, j ≠ 1 → j ≠ stk₀ → getStk stks₂ j = []) := by
      cases b with
      | false =>
        have hstep3 : flatStep prog ⟨some 3, stks⟩ =
            ⟨some (emitPushSym base stk₀ rF 3 cF).1, stks₁⟩ := by
          change (match prog[3]? with
            | none => _ | some .halt => _ | some (.jump _) => _
            | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
          rw [h3]; dsimp only; rw [hfst]
        obtain ⟨stks₂, hrp, hself, hother⟩ :=
          emitPushSym_spec prog base stk₀ rF 3 cF stks₁ hprogF
        have hrF_lt : rF < (syms M.k₀).length := List.idxOf_lt_length_of_mem hmemF
        refine ⟨stks₂, ((FlatReachesIn.step hstep3).trans hrp).mono (by omega), ?_, ?_, ?_, ?_⟩
        · rw [hother 0 (by omega), getStk_popStk_ne stks (by omega), hs0]
        · rw [hother 1 (by omega), getStk_popStk_self, hs1]; rfl
        · rw [hself, getStk_popStk_ne stks (by omega), hsk0, List.map_cons, encodeSymList_cons]
        · intro j hj1 hj0
          rw [hother j hj0, getStk_popStk_ne stks hj1, hsj j hj1 hj0]
      | true =>
        have hstep3 : flatStep prog ⟨some 3, stks⟩ =
            ⟨some (emitPushSym base stk₀ rT 3 cT).1, stks₁⟩ := by
          change (match prog[3]? with
            | none => _ | some .halt => _ | some (.jump _) => _
            | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
          rw [h3]; dsimp only; rw [hfst]
        obtain ⟨stks₂, hrp, hself, hother⟩ :=
          emitPushSym_spec prog base stk₀ rT 3 cT stks₁ hprogT
        have hrT_lt : rT < (syms M.k₀).length := List.idxOf_lt_length_of_mem hmemT
        refine ⟨stks₂, ((FlatReachesIn.step hstep3).trans hrp).mono (by omega), ?_, ?_, ?_, ?_⟩
        · rw [hother 0 (by omega), getStk_popStk_ne stks (by omega), hs0]
        · rw [hother 1 (by omega), getStk_popStk_self, hs1]; rfl
        · rw [hself, getStk_popStk_ne stks (by omega), hsk0, List.map_cons, encodeSymList_cons]
        · intro j hj1 hj0
          rw [hother j hj0, getStk_popStk_ne stks hj1, hsj j hj1 hj0]
    obtain ⟨stks₂, hr_one, hs2_0, hs2_1, hs2_k0, hs2_j⟩ := hpush_branch
    obtain ⟨stks', hr_rest, hf0, hf1, hfk0, hfj⟩ :=
      prologueEnc_spec M eIn eK syms prog base startPc W hW0 hmemF hmemT cF cT hprogF hprogT h3
        xs (b :: acc) stks₂ hs2_0 hs2_1 hs2_k0 hs2_j
    refine ⟨stks', (hr_one.trans hr_rest).mono ?_, hf0, hf1, ?_, hfj⟩
    · simp only [List.length_cons]
      have hring : (W + 2) + ((W + 2) * xs.length + 1) = (W + 2) * (xs.length + 1) + 1 := by ring
      omega
    · simpa [List.reverse_cons, List.append_assoc] using hfk0

/-- Main compiler theorem: any `FinTM2` with `Bool` input/output alphabets compiles to a
    `List FlatInstr` program simulating its bounded runs with linear overhead. -/
theorem exists_compiled_flatProg (M : FinTM2)
    (eIn : M.Γ M.k₀ ≃ Bool) (eOut : M.Γ M.k₁ ≃ Bool) :
    ∃ (prog : List FlatInstr) (C_init C_step : ℕ),
      ∀ (inp : List Bool) (res : Bool) (t : ℕ),
        TM2OutputsInTime M (inp.map eIn.symm) (some [eOut.symm res]) t →
        ∀ steps, C_init * (inp.length + 1) + C_step * (t + 1) ≤ steps →
          flatEval prog inp steps = res := by
  let _ := M.kFin
  let _ := M.ΛFin
  let _ := M.σFin
  let nΛ := Fintype.card M.Λ
  let nσ := Fintype.card M.σ
  let nK := Fintype.card M.K
  let eΛ : M.Λ ≃ Fin nΛ := Fintype.equivFin M.Λ
  let eσ : M.σ ≃ Fin nσ := Fintype.equivFin M.σ
  let eK : M.K ≃ Fin nK := Fintype.equivFin M.K
  let ePair : M.Λ × M.σ ≃ Fin (nΛ * nσ) := (Equiv.prodCongr eΛ eσ).trans finProdFinEquiv
  let syms : ∀ k, List (M.Γ k) := fun k =>
    ((if h0 : k = M.k₀ then [h0 ▸ eIn.symm false, h0 ▸ eIn.symm true] else []) ++
      (if h1 : k = M.k₁ then [h1 ▸ eOut.symm false, h1 ▸ eOut.symm true] else []) ++
      ((List.finRange nΛ).flatMap (fun j => stmtPushedSyms M eσ k (M.m (eΛ.symm j))))).dedup
  let W : ℕ := ((List.finRange nK).map (fun i => (syms (eK.symm i)).length)).foldr max 0
  have hW : ∀ k, (syms k).length ≤ W := by
    intro k
    refine le_foldr_max_of_mem ?_
    rw [List.mem_map]
    exact ⟨eK k, List.mem_finRange _, by rw [eK.symm_apply_apply]⟩
  have hmem_in : ∀ b : Bool, eIn.symm b ∈ syms M.k₀ := by
    intro b
    simp only [syms, List.mem_dedup, List.mem_append, ↓reduceDIte]
    left; left; cases b <;> simp
  have hmem_out : ∀ b : Bool, eOut.symm b ∈ syms M.k₁ := by
    intro b
    simp only [syms, List.mem_dedup, List.mem_append, ↓reduceDIte]
    left; right; cases b <;> simp
  have hmem_push : ∀ (l : M.Λ) (k : M.K) (a : M.Γ k),
      a ∈ stmtPushedSyms M eσ k (M.m l) → a ∈ syms k := by
    intro l k a ha
    simp only [syms, List.mem_dedup, List.mem_append, List.mem_flatMap]
    right
    exact ⟨eΛ l, List.mem_finRange _, by simpa using ha⟩
  let base : ℕ := 4 + nΛ * nσ
  let trampPc : M.Λ → M.σ → ℕ := fun l v => 4 + (ePair (l, v)).val
  let stk₀ : ℕ := 2 + (eK M.k₀).val
  let stk₁ : ℕ := 2 + (eK M.k₁).val
  let rF : ℕ := (syms M.k₀).idxOf (eIn.symm false)
  let rT : ℕ := (syms M.k₀).idxOf (eIn.symm true)
  let pInF := emitPushSym base stk₀ rF 3 []
  let pInT := emitPushSym base stk₀ rT 3 pInF.2
  let haltPc : ℕ := base + pInT.2.length
  let cHalt : List FlatInstr := pInT.2 ++ [.halt]
  let outFalsePc : ℕ := base + cHalt.length
  let cOutF : List FlatInstr := cHalt ++ [.push 0 false haltPc]
  let outTruePc : ℕ := base + cOutF.length
  let cOutT : List FlatInstr := cOutF ++ [.push 0 true haltPc]
  let outTargets : List ℕ := (syms M.k₁).map (fun s => if eOut s then outTruePc else outFalsePc)
  let pEp := emitPopChain base stk₁ outFalsePc outTargets cOutT
  let epiloguePc : ℕ := pEp.1
  let pairs : List (M.Λ × M.σ) := (List.finRange (nΛ * nσ)).map ePair.symm
  let compLV : M.Λ × M.σ → List FlatInstr → ℕ × List FlatInstr :=
    fun lv c => compileStmt M eK syms trampPc epiloguePc base (M.m lv.1) lv.2 c
  let pBodies := compileSymBranches compLV pairs pEp.2
  let prologue : List FlatInstr :=
    [.pop 0 3 1 2, .push 1 false 0, .push 1 true 0,
     .pop 1 (trampPc M.main M.initialState) pInF.1 pInT.1]
  let tramps : List FlatInstr := pBodies.1.map FlatInstr.jump
  let prog : List FlatInstr := prologue ++ tramps ++ pBodies.2
  have htramps_len : tramps.length = nΛ * nσ := by
    simp [tramps, pBodies, compileSymBranches_length, pairs]
  have hpre_len : (prologue ++ tramps).length = base := by
    simp only [prologue, List.length_append, List.length_cons, List.length_nil, htramps_len, base]
  have hprog_body : ∀ i < pBodies.2.length, prog[base + i]? = pBodies.2[i]? := by
    intro i hi
    dsimp only [prog]
    rw [← hpre_len, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
  have hpref_lv : ∀ lv c, ∃ ext, (compLV lv c).2 = c ++ ext :=
    fun lv c => compileStmt_prefix M eK syms trampPc epiloguePc base (M.m lv.1) lv.2 c
  obtain ⟨ext_bodies, hext_bodies⟩ := compileSymBranches_prefix compLV hpref_lv pairs pEp.2
  have hprog_ep : ∀ i < pEp.2.length, prog[base + i]? = pEp.2[i]? := by
    intro i hi
    have hlen : i < pBodies.2.length := by
      dsimp only [pBodies]; rw [hext_bodies, List.length_append]; omega
    rw [hprog_body i hlen]
    dsimp only [pBodies]
    rw [hext_bodies, List.getElem?_append_left hi]
  obtain ⟨ext_ep, hext_ep⟩ := emitPopChain_prefix base stk₁ outFalsePc outTargets cOutT
  have hprog_outT : ∀ i < cOutT.length, prog[base + i]? = cOutT[i]? := by
    intro i hi
    have hlen : i < pEp.2.length := by
      dsimp only [pEp]; rw [hext_ep, List.length_append]; omega
    rw [hprog_ep i hlen]
    dsimp only [pEp]
    rw [hext_ep, List.getElem?_append_left hi]
  have hprog_outF : ∀ i < cOutF.length, prog[base + i]? = cOutF[i]? := by
    intro i hi
    have hlen : i < cOutT.length := by simp only [cOutT, List.length_append, List.length_singleton]; omega
    rw [hprog_outT i hlen]; dsimp [cOutT]; exact List.getElem?_append_left hi
  have hprog_halt : ∀ i < cHalt.length, prog[base + i]? = cHalt[i]? := by
    intro i hi
    have hlen : i < cOutF.length := by simp only [cOutF, List.length_append, List.length_singleton]; omega
    rw [hprog_outF i hlen]; dsimp [cOutF]; exact List.getElem?_append_left hi
  have hprog_inT : ∀ i < pInT.2.length, prog[base + i]? = pInT.2[i]? := by
    intro i hi
    have hlen : i < cHalt.length := by simp only [cHalt, List.length_append, List.length_singleton]; omega
    rw [hprog_halt i hlen]; dsimp [cHalt]; exact List.getElem?_append_left hi
  obtain ⟨ext_inT, hext_inT⟩ := emitPushSym_prefix base stk₀ rT 3 pInF.2
  have hprog_inF : ∀ i < pInF.2.length, prog[base + i]? = pInF.2[i]? := by
    intro i hi
    have hlen : i < pInT.2.length := by
      dsimp only [pInT]; rw [hext_inT, List.length_append]; omega
    rw [hprog_inT i hlen]
    dsimp only [pInT]
    rw [hext_inT, List.getElem?_append_left hi]
  have hprog0 : prog[0]? = some (.pop 0 3 1 2) := rfl
  have hprog1 : prog[1]? = some (.push 1 false 0) := rfl
  have hprog2 : prog[2]? = some (.push 1 true 0) := rfl
  have hprog3 : prog[3]? = some (.pop 1 (trampPc M.main M.initialState) pInF.1 pInT.1) := rfl
  have hprog_tramp : ∀ (l : M.Λ) (v : M.σ),
      prog[trampPc l v]? =
        some (.jump (pBodies.1[(ePair (l, v)).val]'(by
          simp only [pBodies, compileSymBranches_length, pairs, List.length_map, List.length_finRange]
          exact (ePair (l, v)).isLt))) := by
    intro l v
    let pIdx := (ePair (l, v)).val
    have hpIdx : pIdx < tramps.length := by rw [htramps_len]; exact (ePair (l, v)).isLt
    have hpre_lt : 4 + pIdx < (prologue ++ tramps).length := by
      rw [List.length_append]
      have hpro4 : prologue.length = 4 := rfl
      omega
    dsimp only [prog, trampPc]
    rw [List.getElem?_append_left hpre_lt]
    have hpro4 : prologue.length = 4 := rfl
    rw [← hpro4, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
    rw [List.getElem?_eq_getElem hpIdx]
    simp only [tramps, List.getElem_map]
    rfl
  have hhalt_at : prog[haltPc]? = some .halt := by
    dsimp only [haltPc]
    rw [hprog_halt pInT.2.length (by simp [cHalt])]
    exact getElem?_append_singleton pInT.2 .halt
  have houtF_at : prog[outFalsePc]? = some (.push 0 false haltPc) := by
    dsimp only [outFalsePc]
    rw [hprog_outF cHalt.length (by simp [cOutF])]
    exact getElem?_append_singleton cHalt _
  have houtT_at : prog[outTruePc]? = some (.push 0 true haltPc) := by
    dsimp only [outTruePc]
    rw [hprog_outT cOutF.length (by simp [cOutT])]
    exact getElem?_append_singleton cOutF _
  let maxD : ℕ := ((List.finRange nΛ).map (fun i => stmtDepth (M.m (eΛ.symm i)))).foldr max 1
  have hmaxD : ∀ l : M.Λ, stmtDepth (M.m l) ≤ maxD := by
    intro l
    refine le_foldr_max_of_mem ?_
    rw [List.mem_map]
    exact ⟨eΛ l, List.mem_finRange _, by rw [eΛ.symm_apply_apply]⟩
  let stepBudget : ℕ := 1 + (2 * W + 2) * maxD
  have hsim_steps : ∀ (n : ℕ) (c c_end : M.Cfg) (stks : List (List Bool)),
      (flip bind M.step)^[n] (some c) = some c_end →
      SimStacks M eK syms c.stk stks →
      ∃ stks',
        FlatReachesIn prog ⟨some (cfgTargetPc M trampPc epiloguePc c), stks⟩
          ⟨some (cfgTargetPc M trampPc epiloguePc c_end), stks'⟩ (stepBudget * n) ∧
        SimStacks M eK syms c_end.stk stks' := by
    intro n
    induction n with
    | zero =>
      intro c c_end stks hrun hsim
      injection hrun with hce
      subst hce
      exact ⟨stks, FlatReachesIn.refl _ _, hsim⟩
    | succ n ih =>
      intro c c_end stks hrun hsim
      rw [Function.iterate_succ_apply] at hrun
      rcases c with ⟨optL, v, S⟩
      cases optL with
      | none =>
        change (flip bind M.step)^[n] none = some c_end at hrun
        rw [iterate_bind_none] at hrun
        cases hrun
      | some l =>
        change (flip bind M.step)^[n] (some (TM2.stepAux (M.m l) v S)) = some c_end at hrun
        let pIdx := (ePair (l, v)).val
        have hpIdx_pairs : pIdx < pairs.length := by
          simp only [pairs, List.length_map, List.length_finRange]
          exact (ePair (l, v)).isLt
        have hstep_tr : flatStep prog
            ⟨some (cfgTargetPc M trampPc epiloguePc ⟨some l, v, S⟩), stks⟩ =
            ⟨some (pBodies.1[pIdx]'(by rw [compileSymBranches_length]; exact hpIdx_pairs)),
             stks⟩ := by
          dsimp only [cfgTargetPc]
          change (match prog[trampPc l v]? with
            | none => _ | some .halt => _ | some (.jump _) => _
            | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
          rw [hprog_tramp l v]
        obtain ⟨c_sub, hbody_eq, hprog_sub⟩ :=
          compileSymBranches_spec prog base compLV hpref_lv pairs pIdx hpIdx_pairs pEp.2 hprog_body
        have hpairs_get : pairs[pIdx] = (l, v) := by
          simp only [pairs, List.getElem_map, List.getElem_finRange]
          exact ePair.symm_apply_apply (l, v)
        rw [hbody_eq] at hstep_tr
        dsimp only [compLV] at hstep_tr hprog_sub
        rw [hpairs_get] at hstep_tr hprog_sub
        obtain ⟨stks₁, hreach_body, hsim₁⟩ :=
          compileStmt_spec M prog eσ eK syms W hW trampPc epiloguePc base
            (M.m l) v c_sub S stks (hmem_push l) hsim hprog_sub
        have h1step : FlatReachesIn prog
            ⟨some (cfgTargetPc M trampPc epiloguePc ⟨some l, v, S⟩), stks⟩
            ⟨some (cfgTargetPc M trampPc epiloguePc (TM2.stepAux (M.m l) v S)), stks₁⟩
            stepBudget := by
          refine ((FlatReachesIn.step hstep_tr).trans hreach_body).mono ?_
          dsimp only [stepBudget]
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hmaxD l)) 1
        obtain ⟨stks₂, hreach_rest, hsim₂⟩ := ih (TM2.stepAux (M.m l) v S) c_end stks₁ hrun hsim₁
        refine ⟨stks₂, (h1step.trans hreach_rest).mono ?_, hsim₂⟩
        rw [Nat.mul_succ, Nat.add_comm]
  refine ⟨prog, W + 6, stepBudget + W + 3, ?_⟩
  intro inp res t hout
  rcases hout with ⟨⟨n, heval⟩, hn_le⟩
  obtain ⟨stks_rev, hrev_reach, hrev0, hrev1, hrev_ge2⟩ :=
    prologueRev_spec prog hprog0 hprog1 hprog2 inp [inp] rfl
  simp only [getStk, List.append_nil] at hrev1
  have hrev_k0 : getStk stks_rev stk₀ = encodeSymList (syms M.k₀) ([].map eIn.symm) := by
    rw [hrev_ge2 stk₀ (by dsimp [stk₀]; omega)]
    have hstk0_eq : stk₀ = (eK M.k₀).val + 2 := by dsimp [stk₀]; omega
    rw [hstk0_eq]; rfl
  have hrev_other : ∀ j, j ≠ 1 → j ≠ stk₀ → getStk stks_rev j = [] := by
    intro j hj1 hjk0
    by_cases hj0 : j = 0
    · subst hj0; exact hrev0
    · rw [hrev_ge2 j (by omega)]
      rcases j with _ | _ | j'
      · omega
      · omega
      · rfl
  obtain ⟨stks_init, henc_reach, hi0, hi1, hik0, hi_other⟩ :=
    prologueEnc_spec M eIn eK syms prog base (trampPc M.main M.initialState) W
      (hW M.k₀) (hmem_in false) (hmem_in true) [] pInF.2
      hprog_inF hprog_inT hprog3 inp.reverse [] stks_rev hrev0 hrev1 hrev_k0 hrev_other
  rw [List.reverse_reverse, List.append_nil] at hik0
  rw [List.length_reverse] at henc_reach
  have hsim_init : SimStacks M eK syms (initList M (inp.map eIn.symm)).stk stks_init := by
    refine ⟨hi0, hi1, ?_, ?_⟩
    · intro k a ha
      by_cases hk : k = M.k₀
      · subst hk
        rw [initList_stk_self, List.mem_map] at ha
        obtain ⟨b, _, rfl⟩ := ha
        exact hmem_in b
      · rw [initList_stk_ne M _ hk] at ha; simp at ha
    · intro k
      by_cases hk : k = M.k₀
      · subst hk; rw [initList_stk_self, hik0]
      · rw [initList_stk_ne M _ hk, encodeSymList_nil]
        exact hi_other (2 + (eK k).val) (fun heq => hk (eK.injective (Fin.ext (by omega))))
  have htarget_init : cfgTargetPc M trampPc epiloguePc (initList M (inp.map eIn.symm)) =
      trampPc M.main M.initialState := rfl
  rw [← htarget_init] at henc_reach
  obtain ⟨stks_halt, hrun_reach, hsim_halt⟩ :=
    hsim_steps n (initList M (inp.map eIn.symm)) (haltList M [eOut.symm res]) stks_init
      heval hsim_init
  have htarget_halt : cfgTargetPc M trampPc epiloguePc (haltList M [eOut.symm res]) =
      epiloguePc := rfl
  rw [htarget_halt] at hrun_reach
  let idxOut := (syms M.k₁).idxOf (eOut.symm res)
  have hidxOut_lt : idxOut < (syms M.k₁).length := List.idxOf_lt_length_of_mem (hmem_out res)
  have hidxOut_targ : idxOut < outTargets.length := by simp [outTargets, hidxOut_lt]
  have hstk1_halt : getStk stks_halt stk₁ = (List.replicate idxOut false ++ [true]) ++ [] := by
    have hh := hsim_halt.2.2.2 M.k₁
    rw [haltList_stk_self] at hh
    exact hh
  obtain ⟨stks_ep, hep_reach, _, hep_other⟩ :=
    emitPopChain_sym prog base stk₁ outFalsePc outTargets idxOut hidxOut_targ cOutT
      stks_halt [] hstk1_halt hprog_ep
  have houtTarg_eq : outTargets[idxOut] = if res then outTruePc else outFalsePc := by
    dsimp [outTargets]
    rw [List.getElem_map, List.getElem_idxOf hidxOut_lt, eOut.apply_symm_apply]
  rw [houtTarg_eq] at hep_reach
  have hpush_out : flatStep prog ⟨some (if res then outTruePc else outFalsePc), stks_ep⟩ =
      ⟨some haltPc, pushStk stks_ep 0 res⟩ := by
    cases res
    · change (match prog[outFalsePc]? with
        | none => _ | some .halt => _ | some (.jump _) => _
        | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
      rw [houtF_at]
    · change (match prog[outTruePc]? with
        | none => _ | some .halt => _ | some (.jump _) => _
        | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
      rw [houtT_at]
  have hhalt_step : flatStep prog ⟨some haltPc, pushStk stks_ep 0 res⟩ =
      ⟨none, pushStk stks_ep 0 res⟩ := by
    change (match prog[haltPc]? with
      | none => _ | some .halt => _ | some (.jump _) => _
      | some (.push _ _ _) => _ | some (.pop _ _ _ _) => _) = _
    rw [hhalt_at]
  have htot_reach : FlatReachesIn prog ⟨some 0, [inp]⟩ ⟨none, pushStk stks_ep 0 res⟩
      ((W + 6) * (inp.length + 1) + (stepBudget + W + 3) * (t + 1)) := by
    have hc := ((((hrev_reach.trans henc_reach).trans hrun_reach).trans hep_reach).trans
      (FlatReachesIn.step hpush_out)).trans (FlatReachesIn.step hhalt_step)
    refine hc.mono ?_
    have hidxW : idxOut ≤ W := le_of_lt (lt_of_lt_of_le hidxOut_lt (hW M.k₁))
    have hstep_nt : stepBudget * n ≤ stepBudget * t := Nat.mul_le_mul_left _ hn_le
    have hring_init : (2 * inp.length + 1) + ((W + 2) * inp.length + 1) =
        (W + 4) * inp.length + 2 := by ring
    have hle_init : (W + 4) * inp.length + 2 ≤ (W + 6) * (inp.length + 1) := by
      have : (W + 6) * (inp.length + 1) = (W + 4) * inp.length + 2 * inp.length + W + 6 := by ring
      omega
    have hle_step : stepBudget * t + (idxOut + 1) + 1 + 1 ≤ (stepBudget + W + 3) * (t + 1) := by
      have : (stepBudget + W + 3) * (t + 1) =
          stepBudget * t + stepBudget + W * t + W + 3 * t + 3 := by ring
      omega
    omega
  intro steps hsteps
  have hexact := (htot_reach.mono hsteps).to_exact_halted
  dsimp [flatEval]
  rw [hexact]
  have hstk0_ep : getStk stks_ep 0 = [] := by
    rw [hep_other 0 (by dsimp [stk₁]; omega), hsim_halt.1]
  simp [getStk_pushStk_self, hstk0_ep]

end

end CompileFinTM2

end PudlakMod1

namespace PudlakMod3

open Computability Turing BitstringEncoding ComplexityTheory

noncomputable section

/- ### Shared Reachability & List Helpers -/

def RIn {σ : Type} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ n ≤ m, (flip bind f)^[n] (some a) = b

lemma RIn.refl {σ : Type} (f : σ → Option σ) (a : σ) : RIn f a (some a) 0 :=
  ⟨0, le_rfl, rfl⟩

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

lemma poly_eval_mono (P : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : P.eval a ≤ P.eval b := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

lemma replicate_append_cons {α : Type*} (k : ℕ) (x : α) (xs : List α) :
    List.replicate k x ++ x :: xs = List.replicate (k + 1) x ++ xs := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, ih]

lemma delimit_eq_flatMap (xs : List Bool) :
    delimit xs = xs.flatMap (fun b => [true, b]) ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [delimit, ih, List.flatMap_cons, List.cons_append, List.nil_append]

/- ### BitstringEncoding Equations for `List Bool` and Pairs -/

lemma bitEncode_bool (b : Bool) : bitEncode b = [b] := rfl

lemma bitEncode_list_nil : bitEncode ([] : List Bool) = [] := rfl

lemma bitEncode_list_cons (b : Bool) (xs : List Bool) :
    bitEncode (b :: xs) = true :: b :: false :: bitEncode xs := rfl

lemma bitEncode_list_append (xs ys : List Bool) :
    bitEncode (xs ++ ys) = bitEncode xs ++ bitEncode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.cons_append, bitEncode_list_cons, ih]

lemma length_bitEncode_list (xs : List Bool) :
    (bitEncode xs).length = 3 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih =>
    rw [bitEncode_list_cons]
    simp only [List.length_cons, ih]
    omega

lemma delimit_bitEncode_cons (b : Bool) (xs : List Bool) :
    delimit (bitEncode (b :: xs)) =
      true :: true :: true :: b :: true :: false :: delimit (bitEncode xs) := rfl

lemma bitEncode_pair (x w : List Bool) :
    bitEncode (x, w) = delimit (bitEncode x) ++ bitEncode w := rfl

lemma length_bitEncode_pair (x w : List Bool) :
    (bitEncode (x, w)).length = 6 * x.length + 3 * w.length + 1 := by
  rw [bitEncode_pair, List.length_append, length_delimit, length_bitEncode_list,
    length_bitEncode_list]
  omega

/- ### Machine 3A: `isPolyTime_snd_tail` -/

section SndTail

private def sndTailStmt : Fin 2 → TM2.Stmt (fun _ : Unit => Bool) (Fin 2) (Option Bool)
  | ⟨0, _⟩ =>
    .pop () (fun _ o => o)
      (.branch (fun v => v == some true)
        (.pop () (fun v _ => v) (.goto (fun _ => ⟨0, by decide⟩)))
        (.load (fun _ => none) (.goto (fun _ => ⟨1, by decide⟩))))
  | ⟨_ + 1, _⟩ =>
    .pop () (fun _ o => o)
      (.branch (fun v => v.isSome)
        (.pop () (fun _ _ => none) (.pop () (fun _ _ => none) .halt))
        (.load (fun _ => none) .halt))

private def sndTailTM : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Fin 2
  main := ⟨0, by decide⟩
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := sndTailStmt

private def stCfg (l : Option (Fin 2)) (v : Option Bool) (s : List Bool) : sndTailTM.Cfg :=
  ⟨l, v, fun _ => s⟩

private lemma upd_unit (s s' : List Bool) :
    Function.update (fun _ : Unit => s) () s' = (fun _ : Unit => s') := by
  funext u; cases u; rfl

private lemma sndTail_skip (xs rest : List Bool) (v : Option Bool) :
    RIn sndTailTM.step (stCfg (some ⟨0, by decide⟩) v (delimit xs ++ rest))
      (some (stCfg (some ⟨1, by decide⟩) none rest)) (xs.length + 1) := by
  induction xs generalizing v with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (sndTailStmt ⟨0, by decide⟩) v (fun _ => false :: rest)) = _
    simp only [sndTailStmt, TM2.stepAux, List.head?_cons, List.tail_cons, upd_unit]
    rfl
  | cons b xs ih =>
    have h1 : sndTailTM.step (stCfg (some ⟨0, by decide⟩) v (true :: b :: (delimit xs ++ rest))) =
        some (stCfg (some ⟨0, by decide⟩) (some true) (delimit xs ++ rest)) := by
      change some (TM2.stepAux (sndTailStmt ⟨0, by decide⟩) v
        (fun _ : Unit => true :: b :: (delimit xs ++ rest))) = _
      dsimp only [sndTailStmt, TM2.stepAux, List.head?_cons, List.tail_cons, cond]
      have hbeq : (some true == some true) = true := rfl
      rw [hbeq]
      dsimp only [cond]
      rw [upd_unit, List.tail_cons, upd_unit]
      rfl
    have htr := (RIn.single h1).trans (ih (some true))
    simpa [delimit, Nat.add_comm] using htr

private lemma sndTail_drop (w : List Bool) :
    RIn sndTailTM.step (stCfg (some ⟨1, by decide⟩) none (bitEncode w))
      (some (haltList sndTailTM (bitEncode w.tail))) 1 := by
  cases w with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (sndTailStmt ⟨1, by decide⟩) none (fun _ => [])) = _
    simp only [sndTailStmt, TM2.stepAux, List.head?_nil, List.tail_nil, upd_unit]
    rfl
  | cons b ws =>
    refine RIn.single ?_
    change some (TM2.stepAux (sndTailStmt ⟨1, by decide⟩) none
      (fun _ => true :: b :: false :: bitEncode ws)) = _
    simp only [sndTailStmt, TM2.stepAux, List.head?_cons, List.tail_cons, upd_unit]
    rfl

theorem isPolyTime_snd_tail : IsPolyTime (fun p : List Bool × List Bool => p.2.tail) := by
  let timePoly : Polynomial ℕ := Polynomial.X + 2
  have hout : ∀ p : List Bool × List Bool,
      Nonempty (TM2OutputsInTime sndTailTM
        (List.map (Equiv.refl Bool).invFun (bitEncode p))
        (some (List.map (Equiv.refl Bool).invFun (bitEncode p.2.tail)))
        (timePoly.eval (bitEncode p).length)) := by
    rintro ⟨x, w⟩
    have hinit : initList sndTailTM (bitEncode (x, w)) =
        stCfg (some ⟨0, by decide⟩) none (delimit (bitEncode x) ++ bitEncode w) := rfl
    have hrun := (sndTail_skip (bitEncode x) (bitEncode w) none).trans (sndTail_drop w)
    rw [← hinit] at hrun
    obtain ⟨n, hn, heval⟩ := hrun
    have heval' : (flip bind sndTailTM.step)^[n]
        (some (initList sndTailTM (List.map (Equiv.refl Bool).invFun (bitEncode (x, w))))) =
        Option.map (haltList sndTailTM)
          (some (List.map (Equiv.refl Bool).invFun (bitEncode w.tail))) :=
      ((congrArg (fun l : List Bool => (flip bind sndTailTM.step)^[n] (some (initList sndTailTM l)))
        (List.map_id (bitEncode (x, w)))).trans heval).trans
        (congrArg (fun l : List Bool => some (haltList sndTailTM l))
          (List.map_id (bitEncode w.tail)).symm)
    have hlen : (bitEncode x).length + 1 + 1 ≤ timePoly.eval (bitEncode (x, w)).length := by
      simp only [timePoly, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
        length_bitEncode_pair, length_bitEncode_list]
      omega
    exact ⟨⟨⟨n, heval'⟩, hn.trans hlen⟩⟩
  exact ⟨{
    tm := sndTailTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := timePoly
    outputsFun := fun p => Classical.choice (hout p)
  }⟩

end SndTail

/- ### Horner Polynomial Evaluation in Unary -/

def hornerAcc : List ℕ → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | c :: cs, n, acc => hornerAcc cs n (n * acc + c)

def polyCoeffsRev (P : Polynomial ℕ) : List ℕ :=
  ((List.range (P.natDegree + 1)).map P.coeff).reverse

lemma hornerAcc_range_rev (f : ℕ → ℕ) :
    ∀ (k n acc : ℕ),
      hornerAcc (((List.range k).map f).reverse) n acc =
        acc * n ^ k + ∑ i ∈ Finset.range k, f i * n ^ i
  | 0, _, acc => by simp [hornerAcc]
  | k + 1, n, acc => by
    rw [List.range_succ, List.map_append, List.map_singleton, List.reverse_append,
      List.reverse_singleton, List.singleton_append, hornerAcc,
      hornerAcc_range_rev f k n (n * acc + f k), Finset.sum_range_succ]
    ring

lemma hornerAcc_polyCoeffsRev (P : Polynomial ℕ) (n : ℕ) :
    hornerAcc (polyCoeffsRev P) n 0 = P.eval n := by
  dsimp [polyCoeffsRev]
  rw [hornerAcc_range_rev P.coeff (P.natDegree + 1) n 0, Nat.zero_mul, Nat.zero_add,
    Polynomial.eval_eq_sum_range]

def encodeCoeffs (cs : List ℕ) : List Bool :=
  (cs.map (fun c => List.replicate c true ++ [false])).flatten

def hornerTotalPoly : List ℕ → Polynomial ℕ → Polynomial ℕ
  | [], _ => 1
  | c :: cs, accP =>
    accP * (Polynomial.C 3 * Polynomial.X + Polynomial.C 4) +
      Polynomial.C (c + 5) +
      hornerTotalPoly cs (Polynomial.X * accP + Polynomial.C c)

/- ### Machine 3B: `isPolyTime_mkInstanceBits` -/

section InstanceEncoder

def mkInstanceBits (progBits : List Bool) (p_m p_t : Polynomial ℕ) (x : List Bool) : List Bool :=
  delimit progBits ++ delimit x ++
    delimit (List.replicate (p_m.eval x.length) true) ++
    List.replicate (p_t.eval x.length) true

private def mkEncStk (s0 s1 s2 s3 s4 s5 s6 : List Bool) : Fin 7 → List Bool
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | 3 => s3
  | 4 => s4
  | 5 => s5
  | 6 => s6

private lemma upd_enc0 (s0 s0' s1 s2 s3 s4 s5 s6 : List Bool) :
    Function.update (mkEncStk s0 s1 s2 s3 s4 s5 s6) 0 s0' = mkEncStk s0' s1 s2 s3 s4 s5 s6 := by
  funext i; fin_cases i <;> rfl

private lemma upd_enc1 (s0 s1 s1' s2 s3 s4 s5 s6 : List Bool) :
    Function.update (mkEncStk s0 s1 s2 s3 s4 s5 s6) 1 s1' = mkEncStk s0 s1' s2 s3 s4 s5 s6 := by
  funext i; fin_cases i <;> rfl

private lemma upd_enc2 (s0 s1 s2 s2' s3 s4 s5 s6 : List Bool) :
    Function.update (mkEncStk s0 s1 s2 s3 s4 s5 s6) 2 s2' = mkEncStk s0 s1 s2' s3 s4 s5 s6 := by
  funext i; fin_cases i <;> rfl

private lemma upd_enc3 (s0 s1 s2 s3 s3' s4 s5 s6 : List Bool) :
    Function.update (mkEncStk s0 s1 s2 s3 s4 s5 s6) 3 s3' = mkEncStk s0 s1 s2 s3' s4 s5 s6 := by
  funext i; fin_cases i <;> rfl

private lemma upd_enc4 (s0 s1 s2 s3 s4 s4' s5 s6 : List Bool) :
    Function.update (mkEncStk s0 s1 s2 s3 s4 s5 s6) 4 s4' = mkEncStk s0 s1 s2 s3 s4' s5 s6 := by
  funext i; fin_cases i <;> rfl

private lemma upd_enc5 (s0 s1 s2 s3 s4 s5 s5' s6 : List Bool) :
    Function.update (mkEncStk s0 s1 s2 s3 s4 s5 s6) 5 s5' = mkEncStk s0 s1 s2 s3 s4 s5' s6 := by
  funext i; fin_cases i <;> rfl

private lemma upd_enc6 (s0 s1 s2 s3 s4 s5 s6 s6' : List Bool) :
    Function.update (mkEncStk s0 s1 s2 s3 s4 s5 s6) 6 s6' = mkEncStk s0 s1 s2 s3 s4 s5 s6' := by
  funext i; fin_cases i <;> rfl

private def pushBitsStmt {Λ : Type} (stk : Fin 7) :
    List Bool → TM2.Stmt (fun _ : Fin 7 => Bool) Λ (Bool × Option Bool) →
      TM2.Stmt (fun _ : Fin 7 => Bool) Λ (Bool × Option Bool)
  | [], q => q
  | b :: bs, q => pushBitsStmt stk bs (.push stk (fun _ => b) q)

private abbrev el0 : Fin 12 := ⟨0, by decide⟩
private abbrev el1 : Fin 12 := ⟨1, by decide⟩
private abbrev el2 : Fin 12 := ⟨2, by decide⟩
private abbrev el3 : Fin 12 := ⟨3, by decide⟩
private abbrev el4 : Fin 12 := ⟨4, by decide⟩
private abbrev el5 : Fin 12 := ⟨5, by decide⟩
private abbrev el6 : Fin 12 := ⟨6, by decide⟩
private abbrev el7 : Fin 12 := ⟨7, by decide⟩
private abbrev el8 : Fin 12 := ⟨8, by decide⟩
private abbrev el9 : Fin 12 := ⟨9, by decide⟩
private abbrev el10 : Fin 12 := ⟨10, by decide⟩
private abbrev el11 : Fin 12 := ⟨11, by decide⟩

private def encProg (progBits : List Bool) (p_m p_t : Polynomial ℕ) :
    Fin 12 → TM2.Stmt (fun _ : Fin 7 => Bool) (Fin 12) (Bool × Option Bool)
  | ⟨0, _⟩ =>
    .pop 0 (fun _ o => (false, o))
      (.branch (fun v => v.2.isSome)
        (.pop 0 (fun _ o => (false, o))
          (.push 6 (fun v => v.2.getD false)
            (.push 1 (fun _ => true)
              (.pop 0 (fun _ _ => (false, none))
                (.goto (fun _ => el0))))))
        (pushBitsStmt 2 (encodeCoeffs (polyCoeffsRev p_t))
          (.load (fun _ => (false, none)) (.goto (fun _ => el1)))))
  | ⟨1, _⟩ =>
    .peek 2 (fun v o => (v.1, o))
      (.branch (fun v => v.2.isSome)
        (.load (fun v => (v.1, none)) (.goto (fun _ => el2)))
        (.branch (fun v => v.1)
          (.load (fun _ => (true, none)) (.goto (fun _ => el9)))
          (.load (fun _ => (false, none)) (.goto (fun _ => el7)))))
  | ⟨2, _⟩ =>
    .pop 3 (fun v o => (v.1, o))
      (.branch (fun v => v.2.isSome)
        (.load (fun v => (v.1, none)) (.goto (fun _ => el3)))
        (.load (fun v => (v.1, none)) (.goto (fun _ => el5))))
  | ⟨3, _⟩ =>
    .pop 1 (fun v o => (v.1, o))
      (.branch (fun v => v.2.isSome)
        (.push 5 (fun _ => true)
          (.push 4 (fun _ => true)
            (.load (fun v => (v.1, none)) (.goto (fun _ => el3)))))
        (.load (fun v => (v.1, none)) (.goto (fun _ => el4))))
  | ⟨4, _⟩ =>
    .pop 5 (fun v o => (v.1, o))
      (.branch (fun v => v.2.isSome)
        (.push 1 (fun _ => true)
          (.load (fun v => (v.1, none)) (.goto (fun _ => el4))))
        (.load (fun v => (v.1, none)) (.goto (fun _ => el2))))
  | ⟨5, _⟩ =>
    .pop 4 (fun v o => (v.1, o))
      (.branch (fun v => v.2.isSome)
        (.push 3 (fun _ => true)
          (.load (fun v => (v.1, none)) (.goto (fun _ => el5))))
        (.load (fun v => (v.1, none)) (.goto (fun _ => el6))))
  | ⟨6, _⟩ =>
    .pop 2 (fun v o => (v.1, o))
      (.branch (fun v => v.2.getD false)
        (.push 3 (fun _ => true)
          (.load (fun v => (v.1, none)) (.goto (fun _ => el6))))
        (.load (fun v => (v.1, none)) (.goto (fun _ => el1))))
  | ⟨7, _⟩ =>
    .pop 3 (fun _ o => (false, o))
      (.branch (fun v => v.2.isSome)
        (.push 0 (fun _ => false)
          (.push 0 (fun _ => true)
            (.push 0 (fun _ => true)
              (.load (fun _ => (false, none)) (.goto (fun _ => el7))))))
        (.load (fun _ => (true, none)) (.goto (fun _ => el8))))
  | ⟨8, _⟩ =>
    .push 0 (fun _ => false)
      (.push 0 (fun _ => false)
        (.push 0 (fun _ => true)
          (pushBitsStmt 2 (encodeCoeffs (polyCoeffsRev p_m))
            (.load (fun _ => (true, none)) (.goto (fun _ => el1))))))
  | ⟨9, _⟩ =>
    .pop 3 (fun _ o => (true, o))
      (.branch (fun v => v.2.isSome)
        (.push 0 (fun _ => false)
          (.push 0 (fun _ => true)
            (.push 0 (fun _ => true)
              (.push 0 (fun _ => false)
                (.push 0 (fun _ => true)
                  (.push 0 (fun _ => true)
                    (.load (fun _ => (true, none)) (.goto (fun _ => el9)))))))))
        (.load (fun _ => (false, none)) (.goto (fun _ => el10))))
  | ⟨10, _⟩ =>
    .pop 1 (fun _ o => (false, o))
      (.branch (fun v => v.2.isSome)
        (.load (fun _ => (false, none)) (.goto (fun _ => el10)))
        (.push 0 (fun _ => false)
          (.push 0 (fun _ => false)
            (.push 0 (fun _ => true)
              (.load (fun _ => (false, none)) (.goto (fun _ => el11)))))))
  | ⟨_ + 11, _⟩ =>
    .pop 6 (fun _ o => (false, o))
      (.branch (fun v => v.2.isSome)
        (.push 0 (fun _ => false)
          (.push 0 (fun v => v.2.getD false)
            (.push 0 (fun _ => true)
              (.push 0 (fun _ => false)
                (.push 0 (fun _ => true)
                  (.push 0 (fun _ => true)
                    (.load (fun _ => (false, none)) (.goto (fun _ => el11)))))))))
        (pushBitsStmt 0 (bitEncode (delimit progBits))
          (.load (fun _ => (false, none)) .halt)))

private def encTM (progBits : List Bool) (p_m p_t : Polynomial ℕ) : FinTM2 where
  K := Fin 7
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin 12
  main := el0
  σ := Bool × Option Bool
  initialState := (false, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := encProg progBits p_m p_t

private def encCfg (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (l : Option (Fin 12)) (v : Bool × Option Bool)
    (s0 s1 s2 s3 s4 s5 s6 : List Bool) : (encTM progBits p_m p_t).Cfg :=
  ⟨l, v, mkEncStk s0 s1 s2 s3 s4 s5 s6⟩

private lemma stepAux_pushBitsStmt {Λ : Type} (stk : Fin 7) (bs : List Bool)
    (q : TM2.Stmt (fun _ : Fin 7 => Bool) Λ (Bool × Option Bool))
    (v : Bool × Option Bool) (S : Fin 7 → List Bool) :
    TM2.stepAux (pushBitsStmt stk bs q) v S =
      TM2.stepAux q v (Function.update S stk (bs ++ S stk)) := by
  induction bs generalizing q with
  | nil => simp [pushBitsStmt]
  | cons b bs ih =>
    rw [pushBitsStmt, ih]
    simp only [TM2.stepAux, Function.update_idem, Function.update_self, List.cons_append]

private lemma enc_unpack (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (xs accN accX : List Bool) :
    RIn (encTM progBits p_m p_t).step
      (encCfg progBits p_m p_t (some el0) (false, none) (bitEncode xs) accN [] [] [] [] accX)
      (some (encCfg progBits p_m p_t (some el1) (false, none)
        [] (List.replicate xs.length true ++ accN) (encodeCoeffs (polyCoeffsRev p_t))
        [] [] [] (xs.reverse ++ accX)))
      (xs.length + 1) := by
  induction xs generalizing accN accX with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (encProg progBits p_m p_t el0) (false, none) _) = _
    dsimp only [encProg, el0, bitEncode_list_nil, TM2.stepAux, mkEncStk, Option.isSome, cond]
    rw [upd_enc0, stepAux_pushBitsStmt]
    simp only [mkEncStk, List.append_nil, upd_enc2, TM2.stepAux]
    rfl
  | cons b xs ih =>
    have h1 : (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el0) (false, none)
          (bitEncode (b :: xs)) accN [] [] [] [] accX) =
        some (encCfg progBits p_m p_t (some el0) (false, none)
          (bitEncode xs) (true :: accN) [] [] [] [] (b :: accX)) := by
      change some (TM2.stepAux (encProg progBits p_m p_t el0) (false, none) _) = _
      simp only [encProg, el0, bitEncode_list_cons, TM2.stepAux, mkEncStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true,
        upd_enc0, upd_enc6, upd_enc1]
      rfl
    have htr := (RIn.single h1).trans (ih (true :: accN) (b :: accX))
    rw [replicate_append_cons] at htr
    have hrev : xs.reverse ++ b :: accX = (b :: xs).reverse ++ accX := by
      simp [List.reverse_cons, List.append_assoc]
    rw [hrev] at htr
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma enc_copyN (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (pass : Bool) (s0 cStk s3 s4 s5 s6 : List Bool) (k : ℕ) :
    RIn (encTM progBits p_m p_t).step
      (encCfg progBits p_m p_t (some el3) (pass, none) s0 (List.replicate k true) cStk s3 s4 s5 s6)
      (some (encCfg progBits p_m p_t (some el4) (pass, none) s0 [] cStk s3
        (List.replicate k true ++ s4) (List.replicate k true ++ s5) s6))
      (k + 1) := by
  induction k generalizing s4 s5 with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (encProg progBits p_m p_t el3) (pass, none) _) = _
    simp only [encProg, el3, List.replicate_zero, List.nil_append, TM2.stepAux, mkEncStk,
      List.head?_nil, List.tail_nil, Option.isSome, cond_false, upd_enc1]
    rfl
  | succ k ih =>
    have h1 : (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el3) (pass, none)
          s0 (true :: List.replicate k true) cStk s3 s4 s5 s6) =
        some (encCfg progBits p_m p_t (some el3) (pass, none)
          s0 (List.replicate k true) cStk s3 (true :: s4) (true :: s5) s6) := by
      change some (TM2.stepAux (encProg progBits p_m p_t el3) (pass, none) _) = _
      simp only [encProg, el3, TM2.stepAux, mkEncStk, List.head?_cons, List.tail_cons,
        Option.isSome, cond_true, upd_enc1, upd_enc5, upd_enc4]
      rfl
    have htr := (RIn.single h1).trans (ih (true :: s4) (true :: s5))
    rw [replicate_append_cons, replicate_append_cons] at htr
    rw [List.replicate_succ]
    exact htr.mono (by omega)

private lemma enc_restoreN (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (pass : Bool) (s0 s1 cStk s3 s4 s6 : List Bool) (k : ℕ) :
    RIn (encTM progBits p_m p_t).step
      (encCfg progBits p_m p_t (some el4) (pass, none) s0 s1 cStk s3 s4 (List.replicate k true) s6)
      (some (encCfg progBits p_m p_t (some el2) (pass, none)
        s0 (List.replicate k true ++ s1) cStk s3 s4 [] s6))
      (k + 1) := by
  induction k generalizing s1 with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (encProg progBits p_m p_t el4) (pass, none) _) = _
    simp only [encProg, el4, List.replicate_zero, List.nil_append, TM2.stepAux, mkEncStk,
      List.head?_nil, List.tail_nil, Option.isSome, cond_false, upd_enc5]
    rfl
  | succ k ih =>
    have h1 : (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el4) (pass, none)
          s0 s1 cStk s3 s4 (true :: List.replicate k true) s6) =
        some (encCfg progBits p_m p_t (some el4) (pass, none)
          s0 (true :: s1) cStk s3 s4 (List.replicate k true) s6) := by
      change some (TM2.stepAux (encProg progBits p_m p_t el4) (pass, none) _) = _
      simp only [encProg, el4, TM2.stepAux, mkEncStk, List.head?_cons, List.tail_cons,
        Option.isSome, cond_true, upd_enc5, upd_enc1]
      rfl
    have htr := (RIn.single h1).trans (ih (true :: s1))
    rw [replicate_append_cons] at htr
    rw [List.replicate_succ]
    exact htr.mono (by omega)

private lemma enc_mulLoop (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (pass : Bool) (s0 cStk s4 s6 : List Bool) (n acc : ℕ) :
    RIn (encTM progBits p_m p_t).step
      (encCfg progBits p_m p_t (some el2) (pass, none)
        s0 (List.replicate n true) cStk (List.replicate acc true) s4 [] s6)
      (some (encCfg progBits p_m p_t (some el5) (pass, none)
        s0 (List.replicate n true) cStk [] (List.replicate (n * acc) true ++ s4) [] s6))
      (acc * (2 * n + 3) + 1) := by
  induction acc generalizing s4 with
  | zero =>
    simp only [List.replicate_zero, Nat.mul_zero, List.nil_append, Nat.zero_mul, Nat.zero_add]
    refine RIn.single ?_
    change some (TM2.stepAux (encProg progBits p_m p_t el2) (pass, none) _) = _
    simp only [encProg, TM2.stepAux, mkEncStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_enc3]
    rfl
  | succ acc ih =>
    have h1 : (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el2) (pass, none)
          s0 (List.replicate n true) cStk (true :: List.replicate acc true) s4 [] s6) =
        some (encCfg progBits p_m p_t (some el3) (pass, none)
          s0 (List.replicate n true) cStk (List.replicate acc true) s4 [] s6) := by
      change some (TM2.stepAux (encProg progBits p_m p_t el2) (pass, none) _) = _
      simp only [encProg, TM2.stepAux, mkEncStk, List.head?_cons, List.tail_cons,
        Option.isSome, cond_true, upd_enc3]
      rfl
    have hcopy := enc_copyN progBits p_m p_t pass s0 cStk (List.replicate acc true) s4 [] s6 n
    rw [List.append_nil] at hcopy
    have hrest := enc_restoreN progBits p_m p_t pass s0 [] cStk (List.replicate acc true)
      (List.replicate n true ++ s4) s6 n
    rw [List.append_nil] at hrest
    have hsub := ((RIn.single h1).trans hcopy).trans hrest
    have hfull := hsub.trans (ih (List.replicate n true ++ s4))
    rw [List.replicate_succ]
    have hrep_mul : List.replicate (n * acc) true ++ (List.replicate n true ++ s4) =
        List.replicate (n * (acc + 1)) true ++ s4 := by
      rw [← List.append_assoc, ← List.replicate_add, Nat.mul_succ, Nat.add_comm]
    rw [hrep_mul] at hfull
    refine hfull.mono ?_
    have hring : 1 + (n + 1) + (n + 1) + (acc * (2 * n + 3) + 1) =
        (acc + 1) * (2 * n + 3) + 1 := by ring
    omega

private lemma enc_move4to3 (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (pass : Bool) (s0 s1 cStk s3 s6 : List Bool) (k : ℕ) :
    RIn (encTM progBits p_m p_t).step
      (encCfg progBits p_m p_t (some el5) (pass, none)
        s0 s1 cStk s3 (List.replicate k true) [] s6)
      (some (encCfg progBits p_m p_t (some el6) (pass, none)
        s0 s1 cStk (List.replicate k true ++ s3) [] [] s6))
      (k + 1) := by
  induction k generalizing s3 with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (encProg progBits p_m p_t el5) (pass, none) _) = _
    simp only [encProg, el5, List.replicate_zero, List.nil_append, TM2.stepAux, mkEncStk,
      List.head?_nil, List.tail_nil, Option.isSome, cond_false, upd_enc4]
    rfl
  | succ k ih =>
    have h1 : (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el5) (pass, none)
          s0 s1 cStk s3 (true :: List.replicate k true) [] s6) =
        some (encCfg progBits p_m p_t (some el5) (pass, none)
          s0 s1 cStk (true :: s3) (List.replicate k true) [] s6) := by
      change some (TM2.stepAux (encProg progBits p_m p_t el5) (pass, none) _) = _
      simp only [encProg, el5, TM2.stepAux, mkEncStk, List.head?_cons, List.tail_cons,
        Option.isSome, cond_true, upd_enc4, upd_enc3]
      rfl
    have htr := (RIn.single h1).trans (ih (true :: s3))
    rw [replicate_append_cons] at htr
    rw [List.replicate_succ]
    exact htr.mono (by omega)

private lemma enc_addCoeff (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (pass : Bool) (s0 s1 restC s3 s6 : List Bool) (c : ℕ) :
    RIn (encTM progBits p_m p_t).step
      (encCfg progBits p_m p_t (some el6) (pass, none)
        s0 s1 (List.replicate c true ++ false :: restC) s3 [] [] s6)
      (some (encCfg progBits p_m p_t (some el1) (pass, none)
        s0 s1 restC (List.replicate c true ++ s3) [] [] s6))
      (c + 1) := by
  induction c generalizing s3 with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (encProg progBits p_m p_t el6) (pass, none) _) = _
    simp only [encProg, el6, List.replicate_zero, List.nil_append, TM2.stepAux, mkEncStk,
      List.head?_cons, List.tail_cons, Option.getD, cond_false, upd_enc2]
    rfl
  | succ c ih =>
    have h1 : (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el6) (pass, none)
          s0 s1 (true :: (List.replicate c true ++ false :: restC)) s3 [] [] s6) =
        some (encCfg progBits p_m p_t (some el6) (pass, none)
          s0 s1 (List.replicate c true ++ false :: restC) (true :: s3) [] [] s6) := by
      change some (TM2.stepAux (encProg progBits p_m p_t el6) (pass, none) _) = _
      simp only [encProg, el6, TM2.stepAux, mkEncStk, List.head?_cons, List.tail_cons,
        Option.getD, cond_true, upd_enc2, upd_enc3]
      rfl
    have htr := (RIn.single h1).trans (ih (true :: s3))
    rw [replicate_append_cons] at htr
    rw [List.replicate_succ, List.cons_append]
    exact htr.mono (by omega)

private lemma enc_hornerRun (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (pass : Bool) (s0 s6 : List Bool) (n : ℕ) :
    ∀ (cs : List ℕ) (accP : Polynomial ℕ),
      RIn (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el1) (pass, none)
          s0 (List.replicate n true) (encodeCoeffs cs)
          (List.replicate (accP.eval n) true) [] [] s6)
        (some (encCfg progBits p_m p_t (some (if pass then el9 else el7)) (pass, none)
          s0 (List.replicate n true) []
          (List.replicate (hornerAcc cs n (accP.eval n)) true) [] [] s6))
        ((hornerTotalPoly cs accP).eval n)
  | [], accP => by
    simp only [encodeCoeffs, List.map_nil, List.flatten_nil, hornerAcc, hornerTotalPoly,
      Polynomial.eval_one]
    cases pass <;> {
      refine RIn.single ?_
      change some (TM2.stepAux (encProg progBits p_m p_t el1) _ _) = _
      simp only [encProg, TM2.stepAux, mkEncStk, List.head?_nil, Option.isSome,
        cond_false, cond_true]
      rfl
    }
  | c :: cs, accP => by
    have hc_eq : encodeCoeffs (c :: cs) =
        List.replicate c true ++ false :: encodeCoeffs cs := by
      simp [encodeCoeffs, List.append_assoc]
    have hpeek : (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el1) (pass, none)
          s0 (List.replicate n true) (encodeCoeffs (c :: cs))
          (List.replicate (accP.eval n) true) [] [] s6) =
        some (encCfg progBits p_m p_t (some el2) (pass, none)
          s0 (List.replicate n true) (encodeCoeffs (c :: cs))
          (List.replicate (accP.eval n) true) [] [] s6) := by
      rw [hc_eq]
      change some (TM2.stepAux (encProg progBits p_m p_t el1) (pass, none) _) = _
      cases c <;> {
        simp only [encProg, List.replicate_zero, List.replicate_succ, List.nil_append,
          List.cons_append, TM2.stepAux, mkEncStk, List.head?_cons, Option.isSome, cond_true]
        rfl
      }
    have hmul := enc_mulLoop progBits p_m p_t pass s0 (encodeCoeffs (c :: cs)) [] s6 n (accP.eval n)
    rw [List.append_nil] at hmul
    have hmv := enc_move4to3 progBits p_m p_t pass s0 (List.replicate n true)
      (encodeCoeffs (c :: cs)) [] s6 (n * accP.eval n)
    rw [List.append_nil] at hmv
    have hadd := enc_addCoeff progBits p_m p_t pass s0 (List.replicate n true)
      (encodeCoeffs cs) (List.replicate (n * accP.eval n) true) s6 c
    rw [← hc_eq, ← List.replicate_add, Nat.add_comm c _] at hadd
    let accP' := Polynomial.X * accP + Polynomial.C c
    have heval' : accP'.eval n = n * accP.eval n + c := by
      simp [accP']
    rw [← heval'] at hadd
    have hih := enc_hornerRun progBits p_m p_t pass s0 s6 n cs accP'
    have h1234 := (((RIn.single hpeek).trans hmul).trans hmv).trans hadd
    have htot := h1234.trans hih
    rw [heval'] at htot
    dsimp only [accP'] at htot
    refine htot.mono ?_
    simp only [hornerTotalPoly, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
    have hring : 1 + (accP.eval n * (2 * n + 3) + 1) + (n * accP.eval n + 1) + (c + 1) =
        accP.eval n * (3 * n + 3) + (c + 4) := by ring
    have hmono_mul : accP.eval n * (3 * n + 3) ≤ accP.eval n * (3 * n + 4) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

private lemma enc_emitPt (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (s0 s1 s6 : List Bool) (k : ℕ) :
    RIn (encTM progBits p_m p_t).step
      (encCfg progBits p_m p_t (some el7) (false, none)
        s0 s1 [] (List.replicate k true) [] [] s6)
      (some (encCfg progBits p_m p_t (some el8) (true, none)
        (bitEncode (List.replicate k true) ++ s0) s1 [] [] [] [] s6))
      (k + 1) := by
  induction k generalizing s0 with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (encProg progBits p_m p_t el7) (false, none) _) = _
    simp only [encProg, el7, List.replicate_zero, bitEncode_list_nil, List.nil_append,
      TM2.stepAux, mkEncStk, List.head?_nil, List.tail_nil, Option.isSome, cond_false, upd_enc3]
    rfl
  | succ k ih =>
    have h1 : (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el7) (false, none)
          s0 s1 [] (true :: List.replicate k true) [] [] s6) =
        some (encCfg progBits p_m p_t (some el7) (false, none)
          (true :: true :: false :: s0) s1 [] (List.replicate k true) [] [] s6) := by
      change some (TM2.stepAux (encProg progBits p_m p_t el7) (false, none) _) = _
      simp only [encProg, el7, TM2.stepAux, mkEncStk, List.head?_cons, List.tail_cons,
        Option.isSome, cond_true, upd_enc3, upd_enc0]
      rfl
    have htr := (RIn.single h1).trans (ih (true :: true :: false :: s0))
    have hbe : bitEncode (List.replicate k true) ++ true :: true :: false :: s0 =
        bitEncode (List.replicate (k + 1) true) ++ s0 := by
      have hrep1 : List.replicate (k + 1) true = List.replicate k true ++ [true] := by
        simpa using (replicate_append_cons k true []).symm
      rw [hrep1, bitEncode_list_append, List.append_assoc]
      rfl
    rw [hbe] at htr
    rw [List.replicate_succ]
    exact htr.mono (by omega)

private lemma enc_emitPm_aux (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (s1 s6 : List Bool) :
    ∀ (m : ℕ) (acc0 : List Bool),
      RIn (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el9) (true, none)
          acc0 s1 [] (List.replicate m true) [] [] s6)
        (some (encCfg progBits p_m p_t (some el10) (false, none)
          (bitEncode ((List.replicate m true).flatMap (fun b => [true, b])) ++ acc0)
          s1 [] [] [] [] s6))
        (m + 1)
  | 0, acc0 => by
    refine RIn.single ?_
    change some (TM2.stepAux (encProg progBits p_m p_t el9) (true, none) _) = _
    simp only [encProg, el9, List.replicate_zero, List.flatMap_nil, bitEncode_list_nil,
      List.nil_append, TM2.stepAux, mkEncStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_enc3]
    rfl
  | m + 1, acc0 => by
    have h1 : (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el9) (true, none)
          acc0 s1 [] (true :: List.replicate m true) [] [] s6) =
        some (encCfg progBits p_m p_t (some el9) (true, none)
          (true :: true :: false :: true :: true :: false :: acc0)
          s1 [] (List.replicate m true) [] [] s6) := by
      change some (TM2.stepAux (encProg progBits p_m p_t el9) (true, none) _) = _
      simp only [encProg, el9, TM2.stepAux, mkEncStk, List.head?_cons, List.tail_cons,
        Option.isSome, cond_true, upd_enc3, upd_enc0]
      rfl
    have htr := (RIn.single h1).trans
      (enc_emitPm_aux progBits p_m p_t s1 s6 m
        (true :: true :: false :: true :: true :: false :: acc0))
    have hbe : bitEncode ((List.replicate m true).flatMap (fun b => [true, b])) ++
        true :: true :: false :: true :: true :: false :: acc0 =
        bitEncode ((List.replicate (m + 1) true).flatMap (fun b => [true, b])) ++ acc0 := by
      have hrep1 : List.replicate (m + 1) true = List.replicate m true ++ [true] := by
        simpa using (replicate_append_cons m true []).symm
      rw [hrep1, List.flatMap_append, bitEncode_list_append, List.append_assoc]
      rfl
    rw [hbe] at htr
    rw [List.replicate_succ]
    exact htr.mono (by omega)

private lemma enc_emitPm (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (s0 s1 s6 : List Bool) (k : ℕ) :
    RIn (encTM progBits p_m p_t).step
      (encCfg progBits p_m p_t (some el9) (true, none)
        (true :: false :: false :: s0) s1 [] (List.replicate k true) [] [] s6)
      (some (encCfg progBits p_m p_t (some el10) (false, none)
        (bitEncode (delimit (List.replicate k true)) ++ s0) s1 [] [] [] [] s6))
      (k + 1) := by
  have hh := enc_emitPm_aux progBits p_m p_t s1 s6 k (true :: false :: false :: s0)
  rw [delimit_eq_flatMap (List.replicate k true), bitEncode_list_append, List.append_assoc]
  exact hh

private lemma enc_drainN (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (s0 s1 s6 : List Bool) :
    RIn (encTM progBits p_m p_t).step
      (encCfg progBits p_m p_t (some el10) (false, none) s0 s1 [] [] [] [] s6)
      (some (encCfg progBits p_m p_t (some el11) (false, none)
        (true :: false :: false :: s0) [] [] [] [] [] s6))
      (s1.length + 1) := by
  induction s1 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (encProg progBits p_m p_t el10) (false, none) _) = _
    simp only [encProg, el10, TM2.stepAux, mkEncStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_enc1, upd_enc0]
    rfl
  | cons b s1 ih =>
    have h1 : (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el10) (false, none) s0 (b :: s1) [] [] [] [] s6) =
        some (encCfg progBits p_m p_t (some el10) (false, none) s0 s1 [] [] [] [] s6) := by
      change some (TM2.stepAux (encProg progBits p_m p_t el10) (false, none) _) = _
      simp only [encProg, el10, TM2.stepAux, mkEncStk, List.head?_cons, List.tail_cons,
        Option.isSome, cond_true, upd_enc1]
      rfl
    have htr := (RIn.single h1).trans ih
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma enc_emitX (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (s0 xRev : List Bool) :
    RIn (encTM progBits p_m p_t).step
      (encCfg progBits p_m p_t (some el11) (false, none) s0 [] [] [] [] [] xRev)
      (some (haltList (encTM progBits p_m p_t)
        (bitEncode (delimit progBits) ++
          bitEncode (xRev.reverse.flatMap (fun b => [true, b])) ++ s0)))
      (xRev.length + 1) := by
  induction xRev generalizing s0 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (encProg progBits p_m p_t el11) (false, none) _) = _
    dsimp only [encProg, el11, TM2.stepAux, mkEncStk, Option.isSome, cond]
    rw [upd_enc6, stepAux_pushBitsStmt]
    simp only [mkEncStk, upd_enc0, TM2.stepAux, List.reverse_nil, List.flatMap_nil,
      bitEncode_list_nil, List.append_nil]
    dsimp [haltList, encTM]
    congr 2; funext i; fin_cases i <;> rfl
  | cons b xr ih =>
    have h1 : (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el11) (false, none) s0 [] [] [] [] [] (b :: xr)) =
        some (encCfg progBits p_m p_t (some el11) (false, none)
          (true :: true :: false :: true :: b :: false :: s0) [] [] [] [] [] xr) := by
      change some (TM2.stepAux (encProg progBits p_m p_t el11) (false, none) _) = _
      simp only [encProg, el11, TM2.stepAux, mkEncStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_enc6, upd_enc0]
      rfl
    have htr := (RIn.single h1).trans
      (ih (true :: true :: false :: true :: b :: false :: s0))
    have hrev : (b :: xr).reverse.flatMap (fun c => [true, c]) =
        xr.reverse.flatMap (fun c => [true, c]) ++ [true, b] := by
      rw [List.reverse_cons, List.flatMap_append]
      rfl
    rw [hrev, bitEncode_list_append, List.append_assoc, List.append_assoc]
    have htb : bitEncode [true, b] ++ s0 =
        true :: true :: false :: true :: b :: false :: s0 := rfl
    rw [htb]
    have hlen_cons : (b :: xr).length = xr.length + 1 := rfl
    simp only [List.append_assoc] at htr ⊢
    exact htr.mono (by omega)

theorem isPolyTime_mkInstanceBits (progBits : List Bool) (p_m p_t : Polynomial ℕ) :
    IsPolyTime (mkInstanceBits progBits p_m p_t) := by
  let timePoly : Polynomial ℕ :=
    Polynomial.C 3 * Polynomial.X + Polynomial.C 10 +
      hornerTotalPoly (polyCoeffsRev p_t) 0 + p_t +
      hornerTotalPoly (polyCoeffsRev p_m) 0 + p_m
  have hout : ∀ x : List Bool,
      Nonempty (TM2OutputsInTime (encTM progBits p_m p_t)
        (List.map (Equiv.refl Bool).invFun (bitEncode x))
        (some (List.map (Equiv.refl Bool).invFun (bitEncode (mkInstanceBits progBits p_m p_t x))))
        (timePoly.eval (bitEncode x).length)) := by
    intro x
    have hinit : initList (encTM progBits p_m p_t) (bitEncode x) =
        encCfg progBits p_m p_t (some el0) (false, none) (bitEncode x) [] [] [] [] [] [] := by
      dsimp [initList, encTM, encCfg]
      congr 1; funext i; fin_cases i <;> rfl
    have s_unp := enc_unpack progBits p_m p_t x [] []
    simp only [List.append_nil] at s_unp
    have s_ht := enc_hornerRun progBits p_m p_t false [] x.reverse x.length (polyCoeffsRev p_t) 0
    simp only [Polynomial.eval_zero, List.replicate_zero, hornerAcc_polyCoeffsRev] at s_ht
    have s_ept := enc_emitPt progBits p_m p_t [] (List.replicate x.length true) x.reverse
      (p_t.eval x.length)
    rw [List.append_nil] at s_ept
    have hstep8 : (encTM progBits p_m p_t).step
        (encCfg progBits p_m p_t (some el8) (true, none)
          (bitEncode (List.replicate (p_t.eval x.length) true))
          (List.replicate x.length true) [] [] [] [] x.reverse) =
        some (encCfg progBits p_m p_t (some el1) (true, none)
          (true :: false :: false :: bitEncode (List.replicate (p_t.eval x.length) true))
          (List.replicate x.length true) (encodeCoeffs (polyCoeffsRev p_m)) [] [] [] x.reverse) := by
      change some (TM2.stepAux (encProg progBits p_m p_t el8) (true, none) _) = _
      dsimp only [encProg, el8, TM2.stepAux]
      rw [upd_enc0, upd_enc0, upd_enc0, stepAux_pushBitsStmt]
      simp only [mkEncStk, List.append_nil, upd_enc2, TM2.stepAux]
      rfl
    have s_hm := enc_hornerRun progBits p_m p_t true
      (true :: false :: false :: bitEncode (List.replicate (p_t.eval x.length) true))
      x.reverse x.length (polyCoeffsRev p_m) 0
    simp only [Polynomial.eval_zero, List.replicate_zero, hornerAcc_polyCoeffsRev] at s_hm
    have s_epm := enc_emitPm progBits p_m p_t
      (bitEncode (List.replicate (p_t.eval x.length) true))
      (List.replicate x.length true) x.reverse (p_m.eval x.length)
    have s_dr := enc_drainN progBits p_m p_t
      (bitEncode (delimit (List.replicate (p_m.eval x.length) true)) ++
        bitEncode (List.replicate (p_t.eval x.length) true))
      (List.replicate x.length true) x.reverse
    rw [List.length_replicate] at s_dr
    have s_ex := enc_emitX progBits p_m p_t
      (true :: false :: false ::
        (bitEncode (delimit (List.replicate (p_m.eval x.length) true)) ++
          bitEncode (List.replicate (p_t.eval x.length) true)))
      x.reverse
    rw [List.reverse_reverse, List.length_reverse] at s_ex
    have hout_eq : bitEncode (delimit progBits) ++
        bitEncode (x.flatMap (fun b => [true, b])) ++
        (true :: false :: false ::
          (bitEncode (delimit (List.replicate (p_m.eval x.length) true)) ++
            bitEncode (List.replicate (p_t.eval x.length) true))) =
        bitEncode (mkInstanceBits progBits p_m p_t x) := by
      dsimp [mkInstanceBits]
      rw [bitEncode_list_append, bitEncode_list_append, bitEncode_list_append,
        delimit_eq_flatMap x, bitEncode_list_append]
      simp only [List.append_assoc, bitEncode_list_cons, bitEncode_list_nil, List.cons_append,
        List.nil_append]
    rw [hout_eq] at s_ex
    have hcomb := ((((((s_unp.trans s_ht).trans s_ept).trans (RIn.single hstep8)).trans
      s_hm).trans s_epm).trans s_dr).trans s_ex
    rw [← hinit] at hcomb
    obtain ⟨steps, hsteps, heval⟩ := hcomb
    have hx_le : x.length ≤ (bitEncode x).length := by
      rw [length_bitEncode_list]; omega
    have h1 := poly_eval_mono (hornerTotalPoly (polyCoeffsRev p_t) 0) hx_le
    have h2 := poly_eval_mono p_t hx_le
    have h3 := poly_eval_mono (hornerTotalPoly (polyCoeffsRev p_m) 0) hx_le
    have h4 := poly_eval_mono p_m hx_le
    have heval' : (flip bind (encTM progBits p_m p_t).step)^[steps]
        (some (initList (encTM progBits p_m p_t) (List.map (Equiv.refl Bool).invFun (bitEncode x)))) =
        Option.map (haltList (encTM progBits p_m p_t))
          (some (List.map (Equiv.refl Bool).invFun (bitEncode (mkInstanceBits progBits p_m p_t x)))) :=
      ((congrArg (fun l : List Bool =>
          (flip bind (encTM progBits p_m p_t).step)^[steps]
            (some (initList (encTM progBits p_m p_t) l)))
        (List.map_id (bitEncode x))).trans heval).trans
        (congrArg (fun l : List Bool => some (haltList (encTM progBits p_m p_t) l))
          (List.map_id (bitEncode (mkInstanceBits progBits p_m p_t x))).symm)
    refine ⟨⟨⟨steps, heval'⟩, hsteps.trans ?_⟩⟩
    simp only [timePoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    omega
  exact ⟨{
    tm := encTM progBits p_m p_t
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := timePoly
    outputsFun := fun x => Classical.choice (hout x)
  }⟩

end InstanceEncoder

end

end PudlakMod3

namespace PudlakMod2

open Computability Turing BitstringEncoding ComplexityTheory

noncomputable section

/- ### 1. Core `FlatInstr` / `rawRun` / `U` definitions (matching Modules 1 and 3) -/

open PudlakMod1 (FlatInstr FlatCfg getStk pushStk popStk flatStep flatStep_halted flatEval)
open PudlakMod3 (mkInstanceBits)

def unary (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

def decodeUnary : List Bool → Option (ℕ × List Bool)
  | false :: rest => some (0, rest)
  | true :: rest => (decodeUnary rest).map fun p => (p.1 + 1, p.2)
  | [] => none

@[simp]
lemma decodeUnary_unary (n : ℕ) (rest : List Bool) :
    decodeUnary (unary n ++ rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [unary, List.replicate_succ, List.cons_append, decodeUnary]
    change Option.map (fun p => (p.1 + 1, p.2)) (decodeUnary (unary n ++ rest)) = some (n + 1, rest)
    rw [ih]; rfl

@[simp]
lemma decodeUnary_unary_nil (n : ℕ) :
    decodeUnary (unary n) = some (n, []) := by
  simpa using decodeUnary_unary n []

lemma decodeUnary_len {bs rest : List Bool} {n : ℕ}
    (h : decodeUnary bs = some (n, rest)) : n + 1 + rest.length = bs.length := by
  induction bs generalizing n with
  | nil => cases h
  | cons b bs ih =>
    cases b
    · simp only [decodeUnary, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩; simp; omega
    · simp only [decodeUnary, Option.map_eq_some_iff] at h
      rcases h with ⟨⟨m, r'⟩, hm, heq⟩
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      have := ih hm; simp; omega

def encodeInstr : FlatInstr → List Bool
  | .halt => [false, false]
  | .jump next => [false, true] ++ unary next
  | .push stk bit next => [true, false, bit] ++ unary stk ++ unary next
  | .pop stk onE onF onT =>
    [true, true] ++ unary stk ++ unary onE ++ unary onF ++ unary onT

def decodeInstr : List Bool → Option FlatInstr
  | false :: false :: _ => some .halt
  | false :: true :: r => (decodeUnary r).map fun p => .jump p.1
  | true :: false :: b :: r =>
    (decodeUnary r).bind fun p1 =>
      (decodeUnary p1.2).map fun p2 => .push p1.1 b p2.1
  | true :: true :: r =>
    (decodeUnary r).bind fun p1 =>
      (decodeUnary p1.2).bind fun p2 =>
        (decodeUnary p2.2).bind fun p3 =>
          (decodeUnary p3.2).map fun p4 => .pop p1.1 p2.1 p3.1 p4.1
  | _ => none

@[simp]
lemma decodeInstr_encodeInstr (ins : FlatInstr) :
    decodeInstr (encodeInstr ins) = some ins := by
  cases ins <;> simp [encodeInstr, decodeInstr, List.append_assoc]

def encodeProg (prog : List FlatInstr) : List Bool :=
  (prog.map (fun ins => delimit (encodeInstr ins))).flatten

def fetchBlock : List Bool → ℕ → Option (Option (List Bool))
  | [], _ => some none
  | b :: rest, 0 => (undelimit (b :: rest)).map fun p => some p.1
  | b :: rest, k + 1 => (undelimit (b :: rest)).bind fun p => fetchBlock p.2 k

lemma delimit_encodeInstr_cons (ins : FlatInstr) :
    ∃ b tail, delimit (encodeInstr ins) = b :: tail := by
  cases ins <;> exact ⟨true, _, rfl⟩

lemma fetchBlock_encodeProg (prog : List FlatInstr) (idx : ℕ) :
    fetchBlock (encodeProg prog) idx = some (prog[idx]?.map encodeInstr) := by
  induction prog generalizing idx with
  | nil => simp [encodeProg, fetchBlock]
  | cons ins ps ih =>
    obtain ⟨b, tail, hdel⟩ := delimit_encodeInstr_cons ins
    have henc : encodeProg (ins :: ps) = b :: (tail ++ encodeProg ps) := by
      simp only [encodeProg, List.map_cons, List.flatten_cons, hdel, List.cons_append]
    have hund : undelimit (b :: (tail ++ encodeProg ps)) = some (encodeInstr ins, encodeProg ps) := by
      rw [← List.cons_append, ← hdel, undelimit_delimit]
    cases idx with
    | zero =>
      rw [henc, fetchBlock, hund]; rfl
    | succ k =>
      rw [henc, fetchBlock, hund]; exact ih k

def rawRun (progBits : List Bool) : ℕ → ℕ → List (List Bool) → Bool
  | 0, _, _ => false
  | fuel + 1, pc, stks =>
    match fetchBlock progBits pc with
    | none => false
    | some none => (getStk stks 0).head?.getD false
    | some (some blk) =>
      match decodeInstr blk with
      | none => false
      | some .halt => (getStk stks 0).head?.getD false
      | some (.jump next) => rawRun progBits fuel next stks
      | some (.push k b next) => rawRun progBits fuel next (pushStk stks k b)
      | some (.pop k onE onF onT) =>
        let res := popStk stks k
        match res.1 with
        | none => rawRun progBits fuel onE res.2
        | some false => rawRun progBits fuel onF res.2
        | some true => rawRun progBits fuel onT res.2

lemma rawRun_encodeProg (prog : List FlatInstr) (t pc : ℕ) (stks : List (List Bool)) :
    rawRun (encodeProg prog) t pc stks =
      let c := (flatStep prog)^[t] ⟨some pc, stks⟩
      c.pc.isNone && ((getStk c.stks 0).head?.getD false) := by
  induction t generalizing pc stks with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    simp only [rawRun, fetchBlock_encodeProg, flatStep]
    rcases hp : prog[pc]? with _ | ins
    · simp [flatStep_halted]
    · cases ins with
      | halt => simp [flatStep_halted]
      | jump next => simpa using ih next stks
      | push k b next => simpa using ih next (pushStk stks k b)
      | pop k onE onF onT =>
        simp only [Option.map_some, decodeInstr_encodeInstr]
        cases hres : (popStk stks k).1 with
        | none => exact ih onE (popStk stks k).2
        | some bit =>
          cases bit
          · exact ih onF (popStk stks k).2
          · exact ih onT (popStk stks k).2

def parseZ (z : List Bool) : Option (List Bool × List Bool × List Bool × List Bool) :=
  match undelimit z with
  | none => none
  | some (progBits, r1) =>
    match undelimit r1 with
    | none => none
    | some (x, r2) =>
      match undelimit r2 with
      | none => none
      | some (mStr, tStr) => some (progBits, x, mStr, tStr)

def U (zy : List Bool × List Bool) : Bool :=
  match parseZ zy.1 with
  | none => false
  | some (progBits, x, mStr, tStr) =>
    if zy.2.length ≤ mStr.length then
      rawRun progBits tStr.length 0 [bitEncode (x, zy.2)]
    else
      false

theorem U_mkInstanceBits (prog : List FlatInstr) (p_m p_t : Polynomial ℕ) (x y : List Bool) :
    U (mkInstanceBits (encodeProg prog) p_m p_t x, y) =
      (decide (y.length ≤ p_m.eval x.length) &&
        flatEval prog (bitEncode (x, y)) (p_t.eval x.length)) := by
  have hp : parseZ (mkInstanceBits (encodeProg prog) p_m p_t x) =
      some (encodeProg prog, x,
        List.replicate (p_m.eval x.length) true,
        List.replicate (p_t.eval x.length) true) := by
    simp [parseZ, mkInstanceBits, List.append_assoc]
  simp only [U, hp, List.length_replicate]
  by_cases hle : y.length ≤ p_m.eval x.length
  · simp [hle, rawRun_encodeProg, flatEval]
  · simp [hle]

/- ### 2. Bank Encoding Algebra -/

def encodeBank (stks : List (List Bool)) : List Bool :=
  (stks.map delimit).flatten

def dropStks (stks : List (List Bool)) : ℕ → List (List Bool)
  | 0 => stks
  | k + 1 => match stks with
    | [] => []
    | _ :: ss => dropStks ss k

def skipAcc (stks : List (List Bool)) : ℕ → List Bool → List Bool
  | 0, acc => acc
  | k + 1, acc => match stks with
    | [] => skipAcc [] k (false :: acc)
    | s :: ss => skipAcc ss k ((delimit s).reverse ++ acc)

@[simp]
lemma dropStks_nil (k : ℕ) : dropStks [] k = [] := by
  cases k <;> rfl

lemma popStk_nil_fst (k : ℕ) : (popStk [] k).1 = none := by
  induction k with
  | zero => rfl
  | succ k ih => simp [popStk, ih]

lemma skipAcc_restore_push (stks : List (List Bool)) (k : ℕ) (acc : List Bool) (b : Bool) :
    (skipAcc stks k acc).reverse ++ encodeBank (pushStk (dropStks stks k) 0 b) =
      acc.reverse ++ encodeBank (pushStk stks k b) := by
  induction k generalizing stks acc with
  | zero => simp [skipAcc, dropStks]
  | succ k ih =>
    cases stks with
    | nil =>
      simp only [skipAcc, dropStks]
      have h := ih [] (false :: acc)
      rw [dropStks_nil] at h
      rw [h]
      simp [encodeBank, pushStk, delimit, List.append_assoc]
    | cons s ss =>
      simp only [skipAcc, dropStks]
      rw [ih ss ((delimit s).reverse ++ acc)]
      simp [encodeBank, pushStk, List.reverse_append, List.append_assoc]

lemma popStk_dropStks_fst (stks : List (List Bool)) (k : ℕ) :
    (popStk (dropStks stks k) 0).1 = (popStk stks k).1 := by
  induction k generalizing stks with
  | zero => simp [dropStks]
  | succ k ih =>
    cases stks with
    | nil => simp [dropStks, popStk, popStk_nil_fst]
    | cons s ss => simp [dropStks, popStk, ih ss]

lemma skipAcc_restore_pop (stks : List (List Bool)) (k : ℕ) (acc : List Bool) :
    (skipAcc stks k acc).reverse ++ encodeBank (popStk (dropStks stks k) 0).2 =
      acc.reverse ++ encodeBank (popStk stks k).2 := by
  induction k generalizing stks acc with
  | zero => simp [skipAcc, dropStks]
  | succ k ih =>
    cases stks with
    | nil =>
      simp only [skipAcc, dropStks]
      have h := ih [] (false :: acc)
      rw [dropStks_nil] at h
      rw [h]
      simp [encodeBank, popStk, delimit, List.append_assoc]
    | cons s ss =>
      simp only [skipAcc, dropStks]
      rw [ih ss ((delimit s).reverse ++ acc)]
      simp [encodeBank, popStk, List.reverse_append, List.append_assoc]

lemma skipAcc_len_bound (stks : List (List Bool)) (k : ℕ) (acc : List Bool) :
    (skipAcc stks k acc).length + (encodeBank (dropStks stks k)).length ≤
      acc.length + (encodeBank stks).length + k := by
  induction k generalizing stks acc with
  | zero => simp [skipAcc, dropStks]
  | succ k ih =>
    cases stks with
    | nil =>
      have h := ih [] (false :: acc)
      simp only [encodeBank, List.map_nil, List.flatten_nil, List.length_nil,
        List.length_cons, skipAcc, dropStks, dropStks_nil] at h ⊢
      omega
    | cons s ss =>
      have h := ih ss ((delimit s).reverse ++ acc)
      simp only [encodeBank, List.map_cons, List.flatten_cons, List.length_append,
        List.length_reverse, skipAcc, dropStks] at h ⊢
      omega

lemma encodeBank_push_len (stks : List (List Bool)) (k : ℕ) (b : Bool) :
    (encodeBank (pushStk stks k b)).length ≤ (encodeBank stks).length + k + 3 := by
  induction k generalizing stks with
  | zero =>
    cases stks with
    | nil => simp [encodeBank, pushStk, delimit]
    | cons s ss =>
      simp [encodeBank, pushStk, delimit, List.length_append]
  | succ k ih =>
    cases stks with
    | nil =>
      have h := ih []
      simp only [encodeBank, List.map_nil, List.flatten_nil, List.length_nil] at h
      simp only [encodeBank, pushStk, List.map_cons, List.flatten_cons, List.length_append,
        delimit, List.length_cons, List.length_nil]
      omega
    | cons s ss =>
      have h := ih ss
      simp only [encodeBank, pushStk, List.map_cons, List.flatten_cons, List.length_append] at h ⊢
      omega

lemma encodeBank_pop_len (stks : List (List Bool)) (k : ℕ) :
    (encodeBank (popStk stks k).2).length ≤ (encodeBank stks).length + k := by
  induction k generalizing stks with
  | zero =>
    cases stks with
    | nil => simp [popStk]
    | cons s ss =>
      cases s with
      | nil => simp [popStk]
      | cons b s' =>
        simp [encodeBank, popStk, delimit, List.length_append]; omega
  | succ k ih =>
    cases stks with
    | nil =>
      have h := ih []
      simp only [encodeBank, List.map_nil, List.flatten_nil, List.length_nil] at h
      simp only [encodeBank, popStk, List.map_cons, List.flatten_cons, List.length_append,
        delimit, List.length_cons, List.length_nil]
      omega
    | cons s ss =>
      have h := ih ss
      simp only [encodeBank, popStk, List.map_cons, List.flatten_cons, List.length_append] at h ⊢
      omega

/- ### 3. Step-reachability and BitstringEncoding Helpers -/

def RIn {σ : Type} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ n ≤ m, (flip bind f)^[n] (some a) = b

lemma RIn.refl {σ : Type} (f : σ → Option σ) (a : σ) : RIn f a (some a) 0 :=
  ⟨0, le_rfl, rfl⟩

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

lemma bitEncode_bool (b : Bool) : bitEncode b = [b] := rfl
lemma bitEncode_list_nil : bitEncode ([] : List Bool) = [] := rfl
lemma bitEncode_list_cons (b : Bool) (xs : List Bool) :
    bitEncode (b :: xs) = true :: b :: false :: bitEncode xs := rfl

lemma length_bitEncode_list (xs : List Bool) : (bitEncode xs).length = 3 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => rw [bitEncode_list_cons]; simp only [List.length_cons, ih]; omega

lemma bitEncode_pair (x w : List Bool) :
    bitEncode (x, w) = delimit (bitEncode x) ++ bitEncode w := rfl

lemma length_bitEncode_pair (x w : List Bool) :
    (bitEncode (x, w)).length = 6 * x.length + 3 * w.length + 1 := by
  rw [bitEncode_pair, List.length_append, length_delimit, length_bitEncode_list,
    length_bitEncode_list]
  omega

lemma delimit_bitEncode_cons (b : Bool) (xs : List Bool) :
    delimit (bitEncode (b :: xs)) =
      true :: true :: true :: b :: true :: false :: delimit (bitEncode xs) := rfl

lemma delimit_append (xs ys : List Bool) :
    delimit (xs ++ ys) = xs.flatMap (fun b => [true, b]) ++ delimit ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [delimit, ih]

lemma delimit_bitEncode_y_step (b : Bool) (ys : List Bool) :
    ([true, true, true, b, true, false] ++ delimit (bitEncode ys)) =
      delimit (bitEncode (b :: ys)) := by
  rfl

lemma delimit_bitEncode_pair_step (b : Bool) (xs : List Bool) (tail : List Bool) :
    [true, true, true, true, true, true, true, b, true, true, true, false] ++
      ((delimit (bitEncode xs)).flatMap (fun c => [true, c]) ++ tail) =
      (delimit (bitEncode (b :: xs))).flatMap (fun c => [true, c]) ++ tail := by
  rw [delimit_bitEncode_cons]
  simp [List.flatMap_cons]

/- ### 4. The Universal Evaluator FinTM2 `uTM` -/

section UTM

private abbrev uσ := Bool × Bool × Option Bool
private def uInitVar : uσ := (false, false, none)

private def mkUStk (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : List Bool) : Fin 10 → List Bool
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | 3 => s3
  | 4 => s4
  | 5 => s5
  | 6 => s6
  | 7 => s7
  | 8 => s8
  | 9 => s9

private lemma upd_u0 (s0 s0' s1 s2 s3 s4 s5 s6 s7 s8 s9 : List Bool) :
    Function.update (mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) 0 s0' =
      mkUStk s0' s1 s2 s3 s4 s5 s6 s7 s8 s9 := by
  funext i; fin_cases i <;> rfl

private lemma upd_u1 (s0 s1 s1' s2 s3 s4 s5 s6 s7 s8 s9 : List Bool) :
    Function.update (mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) 1 s1' =
      mkUStk s0 s1' s2 s3 s4 s5 s6 s7 s8 s9 := by
  funext i; fin_cases i <;> rfl

private lemma upd_u2 (s0 s1 s2 s2' s3 s4 s5 s6 s7 s8 s9 : List Bool) :
    Function.update (mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) 2 s2' =
      mkUStk s0 s1 s2' s3 s4 s5 s6 s7 s8 s9 := by
  funext i; fin_cases i <;> rfl

private lemma upd_u3 (s0 s1 s2 s3 s3' s4 s5 s6 s7 s8 s9 : List Bool) :
    Function.update (mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) 3 s3' =
      mkUStk s0 s1 s2 s3' s4 s5 s6 s7 s8 s9 := by
  funext i; fin_cases i <;> rfl

private lemma upd_u4 (s0 s1 s2 s3 s4 s4' s5 s6 s7 s8 s9 : List Bool) :
    Function.update (mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) 4 s4' =
      mkUStk s0 s1 s2 s3 s4' s5 s6 s7 s8 s9 := by
  funext i; fin_cases i <;> rfl

private lemma upd_u5 (s0 s1 s2 s3 s4 s5 s5' s6 s7 s8 s9 : List Bool) :
    Function.update (mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) 5 s5' =
      mkUStk s0 s1 s2 s3 s4 s5' s6 s7 s8 s9 := by
  funext i; fin_cases i <;> rfl

private lemma upd_u6 (s0 s1 s2 s3 s4 s5 s6 s6' s7 s8 s9 : List Bool) :
    Function.update (mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) 6 s6' =
      mkUStk s0 s1 s2 s3 s4 s5 s6' s7 s8 s9 := by
  funext i; fin_cases i <;> rfl

private lemma upd_u7 (s0 s1 s2 s3 s4 s5 s6 s7 s7' s8 s9 : List Bool) :
    Function.update (mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) 7 s7' =
      mkUStk s0 s1 s2 s3 s4 s5 s6 s7' s8 s9 := by
  funext i; fin_cases i <;> rfl

private lemma upd_u8 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s8' s9 : List Bool) :
    Function.update (mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) 8 s8' =
      mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8' s9 := by
  funext i; fin_cases i <;> rfl

private lemma upd_u9 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s9' : List Bool) :
    Function.update (mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) 9 s9' =
      mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9' := by
  funext i; fin_cases i <;> rfl

private def pushBitsU {Λ : Type} (stk : Fin 10) :
    List Bool → TM2.Stmt (fun _ : Fin 10 => Bool) Λ uσ →
      TM2.Stmt (fun _ : Fin 10 => Bool) Λ uσ
  | [], q => q
  | b :: bs, q => pushBitsU stk bs (.push stk (fun _ => b) q)

private lemma stepAux_pushBitsU {Λ : Type} (stk : Fin 10) (bs : List Bool)
    (q : TM2.Stmt (fun _ : Fin 10 => Bool) Λ uσ)
    (v : uσ) (S : Fin 10 → List Bool) :
    TM2.stepAux (pushBitsU stk bs q) v S =
      TM2.stepAux q v (Function.update S stk (bs ++ S stk)) := by
  induction bs generalizing q with
  | nil => simp [pushBitsU]
  | cons b bs ih =>
    rw [pushBitsU, ih]
    simp only [TM2.stepAux, Function.update_idem, Function.update_self, List.cons_append]

end UTM

section UTMProg

private abbrev ul0 : Fin 41 := ⟨0, by decide⟩
private abbrev ul1 : Fin 41 := ⟨1, by decide⟩
private abbrev ul2 : Fin 41 := ⟨2, by decide⟩
private abbrev ul3 : Fin 41 := ⟨3, by decide⟩
private abbrev ul4 : Fin 41 := ⟨4, by decide⟩
private abbrev ul5 : Fin 41 := ⟨5, by decide⟩
private abbrev ul6 : Fin 41 := ⟨6, by decide⟩
private abbrev ul7 : Fin 41 := ⟨7, by decide⟩
private abbrev ul8 : Fin 41 := ⟨8, by decide⟩
private abbrev ul9 : Fin 41 := ⟨9, by decide⟩
private abbrev ul10 : Fin 41 := ⟨10, by decide⟩
private abbrev ul11 : Fin 41 := ⟨11, by decide⟩
private abbrev ul12 : Fin 41 := ⟨12, by decide⟩
private abbrev ul13 : Fin 41 := ⟨13, by decide⟩
private abbrev ul14 : Fin 41 := ⟨14, by decide⟩
private abbrev ul15 : Fin 41 := ⟨15, by decide⟩
private abbrev ul16 : Fin 41 := ⟨16, by decide⟩
private abbrev ul17 : Fin 41 := ⟨17, by decide⟩
private abbrev ul18 : Fin 41 := ⟨18, by decide⟩
private abbrev ul19 : Fin 41 := ⟨19, by decide⟩
private abbrev ul20 : Fin 41 := ⟨20, by decide⟩
private abbrev ul21 : Fin 41 := ⟨21, by decide⟩
private abbrev ul22 : Fin 41 := ⟨22, by decide⟩
private abbrev ul23 : Fin 41 := ⟨23, by decide⟩
private abbrev ul24 : Fin 41 := ⟨24, by decide⟩
private abbrev ul25 : Fin 41 := ⟨25, by decide⟩
private abbrev ul26 : Fin 41 := ⟨26, by decide⟩
private abbrev ul27 : Fin 41 := ⟨27, by decide⟩
private abbrev ul28 : Fin 41 := ⟨28, by decide⟩
private abbrev ul29 : Fin 41 := ⟨29, by decide⟩
private abbrev ul30 : Fin 41 := ⟨30, by decide⟩
private abbrev ul31 : Fin 41 := ⟨31, by decide⟩
private abbrev ul32 : Fin 41 := ⟨32, by decide⟩ -- read output bit from s5
private abbrev ul33 : Fin 41 := ⟨33, by decide⟩ -- drainAll s0..s9, push v.2.1 to s0, halt
private abbrev ul34 : Fin 41 := ⟨34, by decide⟩ -- skipBank
private abbrev ul35 : Fin 41 := ⟨35, by decide⟩ -- skip inner block of s5 -> s6
private abbrev ul36 : Fin 41 := ⟨36, by decide⟩ -- restoreBank s6 -> s5 -> ul16
private abbrev ul37 : Fin 41 := ⟨37, by decide⟩ -- move s2 -> s7, drain s3, s9 -> ul36
private abbrev ul38 : Fin 41 := ⟨38, by decide⟩ -- move s3 -> s7, drain s2, s9 -> ul36
private abbrev ul39 : Fin 41 := ⟨39, by decide⟩ -- move s9 -> s7, drain s2, s3 -> ul36
private abbrev ul40 : Fin 41 := ⟨40, by decide⟩ -- abort -> ul33 with false

private def uProg : Fin 41 → TM2.Stmt (fun _ : Fin 10 => Bool) (Fin 41) uσ
  -- ul0: unpack delimit (bitEncode z) from s0 -> s6 (z.reverse)
  | ⟨0, _⟩ =>
    .pop 0 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.pop 0 (fun _ _ => uInitVar)
            (.pop 0 (fun _ _ => uInitVar)
              (.pop 0 (fun _ o => (false, false, o))
                (.push 6 (fun v => v.2.2.getD false)
                  (.pop 0 (fun _ _ => uInitVar)
                    (.pop 0 (fun _ _ => uInitVar)
                      (.goto (fun _ => ul0))))))))
          (.load (fun _ => uInitVar) (.goto (fun _ => ul1))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul1: rev s6 -> s2 (z)
  | ⟨1, _⟩ =>
    .pop 6 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 2 (fun v => v.2.2.getD false)
          (.load (fun _ => uInitVar) (.goto (fun _ => ul1))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul2))))
  -- ul2: unpack bitEncode y from s0 -> s6 (y.reverse)
  | ⟨2, _⟩ =>
    .pop 0 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.pop 0 (fun _ o => (false, false, o))
          (.push 6 (fun v => v.2.2.getD false)
            (.pop 0 (fun _ _ => uInitVar)
              (.goto (fun _ => ul2)))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul3))))
  -- ul3: rev s6 -> s9 (y)
  | ⟨3, _⟩ =>
    .pop 6 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 9 (fun v => v.2.2.getD false)
          (.load (fun _ => uInitVar) (.goto (fun _ => ul3))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul4))))
  -- ul4: undelimit z on s2 -> s6 (progBits.reverse)
  | ⟨4, _⟩ =>
    .pop 2 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.pop 2 (fun _ o => (false, false, o))
            (.branch (fun v => v.2.2.isSome)
              (.push 6 (fun v => v.2.2.getD false)
                (.load (fun _ => uInitVar) (.goto (fun _ => ul4))))
              (.load (fun _ => uInitVar) (.goto (fun _ => ul40)))))
          (.load (fun _ => uInitVar) (.goto (fun _ => ul5))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul5: rev s6 -> s1 (progBits)
  | ⟨5, _⟩ =>
    .pop 6 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 1 (fun v => v.2.2.getD false)
          (.load (fun _ => uInitVar) (.goto (fun _ => ul5))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul6))))
  -- ul6: undelimit r1 on s2 -> s6 (x.reverse)
  | ⟨6, _⟩ =>
    .pop 2 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.pop 2 (fun _ o => (false, false, o))
            (.branch (fun v => v.2.2.isSome)
              (.push 6 (fun v => v.2.2.getD false)
                (.load (fun _ => uInitVar) (.goto (fun _ => ul6))))
              (.load (fun _ => uInitVar) (.goto (fun _ => ul40)))))
          (.load (fun _ => uInitVar) (.goto (fun _ => ul7))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul7: rev s6 -> s8 (x)
  | ⟨7, _⟩ =>
    .pop 6 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 8 (fun v => v.2.2.getD false)
          (.load (fun _ => uInitVar) (.goto (fun _ => ul7))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul8))))
  -- ul8: undelimit r2 on s2 -> s6 (mStr.reverse)
  | ⟨8, _⟩ =>
    .pop 2 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.pop 2 (fun _ o => (false, false, o))
            (.branch (fun v => v.2.2.isSome)
              (.push 6 (fun v => v.2.2.getD false)
                (.load (fun _ => uInitVar) (.goto (fun _ => ul8))))
              (.load (fun _ => uInitVar) (.goto (fun _ => ul40)))))
          (.load (fun _ => uInitVar) (.goto (fun _ => ul9))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul9: move s2 (tStr) -> s4
  | ⟨9, _⟩ =>
    .pop 2 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 4 (fun v => v.2.2.getD false)
          (.load (fun _ => uInitVar) (.goto (fun _ => ul9))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul10))))
  -- ul10: move s6 (mStr.reverse) -> s3
  | ⟨10, _⟩ =>
    .pop 6 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 3 (fun v => v.2.2.getD false)
          (.load (fun _ => uInitVar) (.goto (fun _ => ul10))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul11))))
  -- ul11: move s8 (x) -> s2 (x.reverse)
  | ⟨11, _⟩ =>
    .pop 8 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 2 (fun v => v.2.2.getD false)
          (.load (fun _ => uInitVar) (.goto (fun _ => ul11))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul12))))
  -- ul12: compare s9 (y) vs s3 (mStr), copy s9 -> s6 (y.reverse)
  | ⟨12, _⟩ =>
    .pop 9 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 6 (fun v => v.2.2.getD false)
          (.pop 3 (fun _ o => (false, false, o))
            (.branch (fun v => v.2.2.isSome)
              (.load (fun _ => uInitVar) (.goto (fun _ => ul12)))
              (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul13))))
  -- ul13: drain s3, then push false onto s5
  | ⟨13, _⟩ =>
    .pop 3 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.load (fun _ => uInitVar) (.goto (fun _ => ul13)))
        (.push 5 (fun _ => false)
          (.load (fun _ => uInitVar) (.goto (fun _ => ul14)))))
  -- ul14: pop s6 (y.reverse), push [true, true, true, b, true, false] onto s5
  | ⟨14, _⟩ =>
    .pop 6 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (pushBitsU 5 [true, true, true, true, true, false]
            (.load (fun _ => uInitVar) (.goto (fun _ => ul14))))
          (pushBitsU 5 [true, true, true, false, true, false]
            (.load (fun _ => uInitVar) (.goto (fun _ => ul14)))))
        (pushBitsU 5 [true, false]
          (.load (fun _ => uInitVar) (.goto (fun _ => ul15)))))
  -- ul15: pop s2 (x.reverse), push [true, true, true, true, true, true, true, b, true, true, true, false] onto s5
  | ⟨15, _⟩ =>
    .pop 2 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (pushBitsU 5 [true, true, true, true, true, true, true, true, true, true, true, false]
            (.load (fun _ => uInitVar) (.goto (fun _ => ul15))))
          (pushBitsU 5 [true, true, true, true, true, true, true, false, true, true, true, false]
            (.load (fun _ => uInitVar) (.goto (fun _ => ul15)))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul16))))
  -- ul16: rawRun step: pop fuel s4
  | ⟨16, _⟩ =>
    .pop 4 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.load (fun _ => uInitVar) (.goto (fun _ => ul17)))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul17: fetchBlock outer loop
  | ⟨17, _⟩ =>
    .peek 1 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.pop 7 (fun _ o => (false, false, o))
          (.branch (fun v => v.2.2.isSome)
            (.load (fun _ => uInitVar) (.goto (fun _ => ul19)))
            (.load (fun _ => uInitVar) (.goto (fun _ => ul18)))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul32))))
  -- ul18: read block undelimit from s1 into s6 and s8
  | ⟨18, _⟩ =>
    .pop 1 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.push 6 (fun _ => true)
            (.pop 1 (fun _ o => (false, false, o))
              (.branch (fun v => v.2.2.isSome)
                (.push 6 (fun v => v.2.2.getD false)
                  (.push 8 (fun v => v.2.2.getD false)
                    (.load (fun _ => uInitVar) (.goto (fun _ => ul18)))))
                (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))))
          (.push 6 (fun _ => false)
            (.load (fun _ => uInitVar) (.goto (fun _ => ul20)))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul19: skip block undelimit from s1 into s6
  | ⟨19, _⟩ =>
    .pop 1 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.push 6 (fun _ => true)
            (.pop 1 (fun _ o => (false, false, o))
              (.branch (fun v => v.2.2.isSome)
                (.push 6 (fun v => v.2.2.getD false)
                  (.load (fun _ => uInitVar) (.goto (fun _ => ul19))))
                (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))))
          (.push 6 (fun _ => false)
            (.load (fun _ => uInitVar) (.goto (fun _ => ul17)))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul20: restore s6 -> s1
  | ⟨20, _⟩ =>
    .pop 6 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 1 (fun v => v.2.2.getD false)
          (.load (fun _ => uInitVar) (.goto (fun _ => ul20))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul21))))
  -- ul21: rev s8 -> s0 (blk)
  | ⟨21, _⟩ =>
    .pop 8 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 0 (fun v => v.2.2.getD false)
          (.load (fun _ => uInitVar) (.goto (fun _ => ul21))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul22))))
  -- ul22: decodeInstr blk on s0
  | ⟨22, _⟩ =>
    .pop 0 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.pop 0 (fun _ o => (false, false, o))
            (.branch (fun v => v.2.2.isSome)
              (.branch (fun v => v.2.2.getD false)
                (.load (fun _ => (true, false, none)) (.goto (fun _ => ul27)))
                (.pop 0 (fun _ o => (false, false, o))
                  (.branch (fun v => v.2.2.isSome)
                    (.load (fun v => (false, v.2.2.getD false, none)) (.goto (fun _ => ul25)))
                    (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))))
              (.load (fun _ => uInitVar) (.goto (fun _ => ul40)))))
          (.pop 0 (fun _ o => (false, false, o))
            (.branch (fun v => v.2.2.isSome)
              (.branch (fun v => v.2.2.getD false)
                (.load (fun _ => uInitVar) (.goto (fun _ => ul23)))
                (.load (fun _ => uInitVar) (.goto (fun _ => ul32))))
              (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul23: read unary next from s0 -> s7 (for jump)
  | ⟨23, _⟩ =>
    .pop 0 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.push 7 (fun _ => true)
            (.load (fun _ => uInitVar) (.goto (fun _ => ul23))))
          (.load (fun _ => uInitVar) (.goto (fun _ => ul24))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul24: drain s0 -> ul16
  | ⟨24, _⟩ =>
    .pop 0 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.load (fun _ => uInitVar) (.goto (fun _ => ul24)))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul16))))
  -- ul25: read unary k from s0 -> s8 (for push, preserve v.1=false, v.2.1=pushBit)
  | ⟨25, _⟩ =>
    .pop 0 (fun v o => (v.1, v.2.1, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.push 8 (fun _ => true)
            (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul25))))
          (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul26))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul26: read unary next from s0 -> s7 (for push)
  | ⟨26, _⟩ =>
    .pop 0 (fun v o => (v.1, v.2.1, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.push 7 (fun _ => true)
            (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul26))))
          (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul31))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul27: read unary k from s0 -> s8 (for pop, v.1=true)
  | ⟨27, _⟩ =>
    .pop 0 (fun v o => (v.1, v.2.1, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.push 8 (fun _ => true)
            (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul27))))
          (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul28))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul28: read unary onE from s0 -> s2
  | ⟨28, _⟩ =>
    .pop 0 (fun v o => (v.1, v.2.1, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.push 2 (fun _ => true)
            (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul28))))
          (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul29))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul29: read unary onF from s0 -> s3
  | ⟨29, _⟩ =>
    .pop 0 (fun v o => (v.1, v.2.1, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.push 3 (fun _ => true)
            (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul29))))
          (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul30))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul30: read unary onT from s0 -> s9
  | ⟨30, _⟩ =>
    .pop 0 (fun v o => (v.1, v.2.1, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.push 9 (fun _ => true)
            (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul30))))
          (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul31))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul31: drain s0 (preserving v.1, v.2.1) -> ul34
  | ⟨31, _⟩ =>
    .pop 0 (fun v o => (v.1, v.2.1, o))
      (.branch (fun v => v.2.2.isSome)
        (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul31)))
        (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul34))))
  -- ul32: read output bit from s5 -> ul33
  | ⟨32, _⟩ =>
    .pop 5 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.pop 5 (fun _ o => (false, false, o))
            (.load (fun v => (false, v.2.2.getD false, none)) (.goto (fun _ => ul33))))
          (.load (fun _ => (false, false, none)) (.goto (fun _ => ul33))))
        (.load (fun _ => (false, false, none)) (.goto (fun _ => ul33))))
  -- ul33: drain s0..s9, then push v.2.1 onto s0 and halt
  | ⟨33, _⟩ =>
    .pop 0 (fun v o => (v.1, v.2.1, o))
      (.branch (fun v => v.2.2.isSome) (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul33)))
        (.pop 1 (fun v o => (v.1, v.2.1, o))
          (.branch (fun v => v.2.2.isSome) (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul33)))
            (.pop 2 (fun v o => (v.1, v.2.1, o))
              (.branch (fun v => v.2.2.isSome) (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul33)))
                (.pop 3 (fun v o => (v.1, v.2.1, o))
                  (.branch (fun v => v.2.2.isSome) (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul33)))
                    (.pop 4 (fun v o => (v.1, v.2.1, o))
                      (.branch (fun v => v.2.2.isSome) (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul33)))
                        (.pop 5 (fun v o => (v.1, v.2.1, o))
                          (.branch (fun v => v.2.2.isSome) (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul33)))
                            (.pop 6 (fun v o => (v.1, v.2.1, o))
                              (.branch (fun v => v.2.2.isSome) (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul33)))
                                (.pop 7 (fun v o => (v.1, v.2.1, o))
                                  (.branch (fun v => v.2.2.isSome) (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul33)))
                                    (.pop 8 (fun v o => (v.1, v.2.1, o))
                                      (.branch (fun v => v.2.2.isSome) (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul33)))
                                        (.pop 9 (fun v o => (v.1, v.2.1, o))
                                          (.branch (fun v => v.2.2.isSome) (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul33)))
                                            (.push 0 (fun v => v.2.1) (.load (fun _ => uInitVar) .halt)))))))))))))))))))))
  -- ul34: skipBank (s8 counter, s5 bank, s6 acc)
  | ⟨34, _⟩ =>
    .pop 8 (fun v o => (v.1, v.2.1, o))
      (.branch (fun v => v.2.2.isSome)
        (.pop 5 (fun v o => (v.1, v.2.1, o))
          (.branch (fun v => v.2.2.isSome)
            (.branch (fun v => v.2.2.getD false)
              (.push 6 (fun _ => true)
                (.pop 5 (fun v o => (v.1, v.2.1, o))
                  (.branch (fun v => v.2.2.isSome)
                    (.push 6 (fun v => v.2.2.getD false)
                      (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul35))))
                    (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))))
              (.push 6 (fun _ => false)
                (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul34)))))
            (.push 6 (fun _ => false)
              (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul34))))))
        (.branch (fun v => v.1)
          -- pop
          (.pop 5 (fun v o => (v.1, v.2.1, o))
            (.branch (fun v => v.2.2.isSome)
              (.branch (fun v => v.2.2.getD false)
                (.pop 5 (fun v o => (v.1, v.2.1, o))
                  (.branch (fun v => v.2.2.isSome)
                    (.branch (fun v => v.2.2.getD false)
                      (.load (fun _ => uInitVar) (.goto (fun _ => ul39)))
                      (.load (fun _ => uInitVar) (.goto (fun _ => ul38))))
                    (.load (fun _ => uInitVar) (.goto (fun _ => ul40)))))
                (.push 5 (fun _ => false)
                  (.load (fun _ => uInitVar) (.goto (fun _ => ul37)))))
              (.load (fun _ => uInitVar) (.goto (fun _ => ul37)))))
          -- push
          (.peek 5 (fun v o => (v.1, v.2.1, o))
            (.branch (fun v => v.2.2.isSome)
              (.push 5 (fun v => v.2.1)
                (.push 5 (fun _ => true)
                  (.load (fun _ => uInitVar) (.goto (fun _ => ul36)))))
              (.push 5 (fun _ => false)
                (.push 5 (fun v => v.2.1)
                  (.push 5 (fun _ => true)
                    (.load (fun _ => uInitVar) (.goto (fun _ => ul36))))))))))
  -- ul35: skip inner block of s5 -> s6
  | ⟨35, _⟩ =>
    .pop 5 (fun v o => (v.1, v.2.1, o))
      (.branch (fun v => v.2.2.isSome)
        (.branch (fun v => v.2.2.getD false)
          (.push 6 (fun _ => true)
            (.pop 5 (fun v o => (v.1, v.2.1, o))
              (.branch (fun v => v.2.2.isSome)
                (.push 6 (fun v => v.2.2.getD false)
                  (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul35))))
                (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))))
          (.push 6 (fun _ => false)
            (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => ul34)))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul40))))
  -- ul36: restoreBank s6 -> s5 -> ul16
  | ⟨36, _⟩ =>
    .pop 6 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 5 (fun v => v.2.2.getD false)
          (.load (fun _ => uInitVar) (.goto (fun _ => ul36))))
        (.load (fun _ => uInitVar) (.goto (fun _ => ul16))))
  -- ul37: move s2 -> s7, drain s3, s9 -> ul36
  | ⟨37, _⟩ =>
    .pop 2 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 7 (fun v => v.2.2.getD false) (.load (fun _ => uInitVar) (.goto (fun _ => ul37))))
        (.pop 3 (fun _ o => (false, false, o))
          (.branch (fun v => v.2.2.isSome) (.load (fun _ => uInitVar) (.goto (fun _ => ul37)))
            (.pop 9 (fun _ o => (false, false, o))
              (.branch (fun v => v.2.2.isSome) (.load (fun _ => uInitVar) (.goto (fun _ => ul37)))
                (.load (fun _ => uInitVar) (.goto (fun _ => ul36))))))))
  -- ul38: move s3 -> s7, drain s2, s9 -> ul36
  | ⟨38, _⟩ =>
    .pop 3 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 7 (fun v => v.2.2.getD false) (.load (fun _ => uInitVar) (.goto (fun _ => ul38))))
        (.pop 2 (fun _ o => (false, false, o))
          (.branch (fun v => v.2.2.isSome) (.load (fun _ => uInitVar) (.goto (fun _ => ul38)))
            (.pop 9 (fun _ o => (false, false, o))
              (.branch (fun v => v.2.2.isSome) (.load (fun _ => uInitVar) (.goto (fun _ => ul38)))
                (.load (fun _ => uInitVar) (.goto (fun _ => ul36))))))))
  -- ul39: move s9 -> s7, drain s2, s3 -> ul36
  | ⟨39, _⟩ =>
    .pop 9 (fun _ o => (false, false, o))
      (.branch (fun v => v.2.2.isSome)
        (.push 7 (fun v => v.2.2.getD false) (.load (fun _ => uInitVar) (.goto (fun _ => ul39))))
        (.pop 2 (fun _ o => (false, false, o))
          (.branch (fun v => v.2.2.isSome) (.load (fun _ => uInitVar) (.goto (fun _ => ul39)))
            (.pop 3 (fun _ o => (false, false, o))
              (.branch (fun v => v.2.2.isSome) (.load (fun _ => uInitVar) (.goto (fun _ => ul39)))
                (.load (fun _ => uInitVar) (.goto (fun _ => ul36))))))))
  -- ul40: abort
  | ⟨40, _⟩ =>
    .load (fun _ => (false, false, none)) (.goto (fun _ => ul33))
  | ⟨_ + 41, h⟩ => absurd h (by omega)

private def uTM : FinTM2 where
  K := Fin 10
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin 41
  ΛFin := inferInstance
  main := ul0
  σ := uσ
  σFin := inferInstance
  initialState := uInitVar
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := uProg

private def uCfg (l : Option (Fin 41)) (v : uσ)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : List Bool) : uTM.Cfg :=
  ⟨l, v, mkUStk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9⟩

end UTMProg

section UTMLemmas

private lemma eq_delimit_append_of_undelimit :
    ∀ (l a b : List Bool), undelimit l = some (a, b) → l = delimit a ++ b
  | [], _, _, h => by simp [undelimit] at h
  | false :: rest, a, b, h => by
    simp only [undelimit, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | [true], _, _, h => by simp [undelimit] at h
  | true :: c :: rest, a, b, h => by
    simp only [undelimit, Option.map_eq_some_iff] at h
    rcases h with ⟨⟨a', b'⟩, h1, h2⟩
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [eq_delimit_append_of_undelimit rest a' b' h1]
    rfl

private lemma u_drainAll (outB : Bool) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul33) (false, outB, none) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9)
      (some (haltList uTM [outB]))
      (s0.length + s1.length + s2.length + s3.length + s4.length +
        s5.length + s6.length + s7.length + s8.length + s9.length + 1) := by
  generalize hn : s0.length + s1.length + s2.length + s3.length + s4.length +
    s5.length + s6.length + s7.length + s8.length + s9.length = n
  induction n generalizing s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 with
  | zero =>
    have h0 : s0 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h1 : s1 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : s2 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h3 : s3 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h4 : s4 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h5 : s5 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h6 : s6 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h7 : s7 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h8 : s8 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h9 : s9 = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul33) (false, outB, none) _) = _
    simp only [uProg, ul33, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u0, upd_u1, upd_u2, upd_u3, upd_u4, upd_u5,
      upd_u6, upd_u7, upd_u8, upd_u9]
    have hstk : mkUStk [outB] [] [] [] [] [] [] [] [] [] = (haltList uTM [outB]).stk := by
      funext i; fin_cases i <;> rfl
    exact congrArg (Option.some ∘ TM2.Cfg.mk none uInitVar) hstk
  | succ n ih =>
    cases s0 with
    | cons c0 s0' =>
      have hstep : uTM.step (uCfg (some ul33) (false, outB, none)
          (c0 :: s0') s1 s2 s3 s4 s5 s6 s7 s8 s9) =
          some (uCfg (some ul33) (false, outB, none) s0' s1 s2 s3 s4 s5 s6 s7 s8 s9) := by
        change some (TM2.stepAux (uProg ul33) (false, outB, none) _) = _
        simp only [uProg, ul33, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, cond_true, upd_u0]; rfl
      exact ((RIn.single hstep).trans (ih s0' s1 s2 s3 s4 s5 s6 s7 s8 s9
        (by simp [List.length_cons] at hn ⊢; omega))).mono (by omega)
    | nil => cases s1 with
      | cons c1 s1' =>
        have hstep : uTM.step (uCfg (some ul33) (false, outB, none)
            [] (c1 :: s1') s2 s3 s4 s5 s6 s7 s8 s9) =
            some (uCfg (some ul33) (false, outB, none) [] s1' s2 s3 s4 s5 s6 s7 s8 s9) := by
          change some (TM2.stepAux (uProg ul33) (false, outB, none) _) = _
          simp only [uProg, ul33, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
            List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true, upd_u0, upd_u1]; rfl
        exact ((RIn.single hstep).trans (ih [] s1' s2 s3 s4 s5 s6 s7 s8 s9 (by simp [List.length_nil, List.length_cons] at hn ⊢; omega))).mono (by omega)
      | nil => cases s2 with
        | cons c2 s2' =>
          have hstep : uTM.step (uCfg (some ul33) (false, outB, none)
              [] [] (c2 :: s2') s3 s4 s5 s6 s7 s8 s9) =
              some (uCfg (some ul33) (false, outB, none) [] [] s2' s3 s4 s5 s6 s7 s8 s9) := by
            change some (TM2.stepAux (uProg ul33) (false, outB, none) _) = _
            simp only [uProg, ul33, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
              List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true,
              upd_u0, upd_u1, upd_u2]; rfl
          exact ((RIn.single hstep).trans (ih [] [] s2' s3 s4 s5 s6 s7 s8 s9 (by simp [List.length_nil, List.length_cons] at hn ⊢; omega))).mono (by omega)
        | nil => cases s3 with
          | cons c3 s3' =>
            have hstep : uTM.step (uCfg (some ul33) (false, outB, none)
                [] [] [] (c3 :: s3') s4 s5 s6 s7 s8 s9) =
                some (uCfg (some ul33) (false, outB, none) [] [] [] s3' s4 s5 s6 s7 s8 s9) := by
              change some (TM2.stepAux (uProg ul33) (false, outB, none) _) = _
              simp only [uProg, ul33, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
                List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true,
                upd_u0, upd_u1, upd_u2, upd_u3]; rfl
            exact ((RIn.single hstep).trans (ih [] [] [] s3' s4 s5 s6 s7 s8 s9 (by simp [List.length_nil, List.length_cons] at hn ⊢; omega))).mono (by omega)
          | nil => cases s4 with
            | cons c4 s4' =>
              have hstep : uTM.step (uCfg (some ul33) (false, outB, none)
                  [] [] [] [] (c4 :: s4') s5 s6 s7 s8 s9) =
                  some (uCfg (some ul33) (false, outB, none) [] [] [] [] s4' s5 s6 s7 s8 s9) := by
                change some (TM2.stepAux (uProg ul33) (false, outB, none) _) = _
                simp only [uProg, ul33, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
                  List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true,
                  upd_u0, upd_u1, upd_u2, upd_u3, upd_u4]; rfl
              exact ((RIn.single hstep).trans (ih [] [] [] [] s4' s5 s6 s7 s8 s9 (by simp [List.length_nil, List.length_cons] at hn ⊢; omega))).mono (by omega)
            | nil => cases s5 with
              | cons c5 s5' =>
                have hstep : uTM.step (uCfg (some ul33) (false, outB, none)
                    [] [] [] [] [] (c5 :: s5') s6 s7 s8 s9) =
                    some (uCfg (some ul33) (false, outB, none) [] [] [] [] [] s5' s6 s7 s8 s9) := by
                  change some (TM2.stepAux (uProg ul33) (false, outB, none) _) = _
                  simp only [uProg, ul33, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
                    List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true,
                    upd_u0, upd_u1, upd_u2, upd_u3, upd_u4, upd_u5]; rfl
                exact ((RIn.single hstep).trans (ih [] [] [] [] [] s5' s6 s7 s8 s9 (by simp [List.length_nil, List.length_cons] at hn ⊢; omega))).mono (by omega)
              | nil => cases s6 with
                | cons c6 s6' =>
                  have hstep : uTM.step (uCfg (some ul33) (false, outB, none)
                      [] [] [] [] [] [] (c6 :: s6') s7 s8 s9) =
                      some (uCfg (some ul33) (false, outB, none) [] [] [] [] [] [] s6' s7 s8 s9) := by
                    change some (TM2.stepAux (uProg ul33) (false, outB, none) _) = _
                    simp only [uProg, ul33, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
                      List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true,
                      upd_u0, upd_u1, upd_u2, upd_u3, upd_u4, upd_u5, upd_u6]; rfl
                  exact ((RIn.single hstep).trans (ih [] [] [] [] [] [] s6' s7 s8 s9 (by simp [List.length_nil, List.length_cons] at hn ⊢; omega))).mono (by omega)
                | nil => cases s7 with
                  | cons c7 s7' =>
                    have hstep : uTM.step (uCfg (some ul33) (false, outB, none)
                        [] [] [] [] [] [] [] (c7 :: s7') s8 s9) =
                        some (uCfg (some ul33) (false, outB, none) [] [] [] [] [] [] [] s7' s8 s9) := by
                      change some (TM2.stepAux (uProg ul33) (false, outB, none) _) = _
                      simp only [uProg, ul33, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
                        List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true,
                        upd_u0, upd_u1, upd_u2, upd_u3, upd_u4, upd_u5, upd_u6, upd_u7]; rfl
                    exact ((RIn.single hstep).trans (ih [] [] [] [] [] [] [] s7' s8 s9 (by simp [List.length_nil, List.length_cons] at hn ⊢; omega))).mono (by omega)
                  | nil => cases s8 with
                    | cons c8 s8' =>
                      have hstep : uTM.step (uCfg (some ul33) (false, outB, none)
                          [] [] [] [] [] [] [] [] (c8 :: s8') s9) =
                          some (uCfg (some ul33) (false, outB, none) [] [] [] [] [] [] [] [] s8' s9) := by
                        change some (TM2.stepAux (uProg ul33) (false, outB, none) _) = _
                        simp only [uProg, ul33, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
                          List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true,
                          upd_u0, upd_u1, upd_u2, upd_u3, upd_u4, upd_u5, upd_u6, upd_u7, upd_u8]; rfl
                      exact ((RIn.single hstep).trans (ih [] [] [] [] [] [] [] [] s8' s9 (by simp [List.length_nil, List.length_cons] at hn ⊢; omega))).mono (by omega)
                    | nil => cases s9 with
                      | cons c9 s9' =>
                        have hstep : uTM.step (uCfg (some ul33) (false, outB, none)
                            [] [] [] [] [] [] [] [] [] (c9 :: s9')) =
                            some (uCfg (some ul33) (false, outB, none) [] [] [] [] [] [] [] [] [] s9') := by
                          change some (TM2.stepAux (uProg ul33) (false, outB, none) _) = _
                          simp only [uProg, ul33, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
                            List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true,
                            upd_u0, upd_u1, upd_u2, upd_u3, upd_u4, upd_u5, upd_u6, upd_u7, upd_u8,
                            upd_u9]; rfl
                        exact ((RIn.single hstep).trans (ih [] [] [] [] [] [] [] [] [] s9' (by simp [List.length_nil, List.length_cons] at hn ⊢; omega))).mono (by omega)
                      | nil =>
                        simp at hn

private lemma u_abort (v : uσ) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul40) v s0 s1 s2 s3 s4 s5 s6 s7 s8 s9)
      (some (haltList uTM [false]))
      (s0.length + s1.length + s2.length + s3.length + s4.length +
        s5.length + s6.length + s7.length + s8.length + s9.length + 2) := by
  have h1 : uTM.step (uCfg (some ul40) v s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) =
      some (uCfg (some ul33) (false, false, none) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) := rfl
  exact ((RIn.single h1).trans (u_drainAll false s0 s1 s2 s3 s4 s5 s6 s7 s8 s9)).mono (by omega)

private lemma u_readOut32 (s0 s1 s2 s3 s4 s6 s7 s8 s9 : List Bool) (stks : List (List Bool)) :
    RIn uTM.step (uCfg (some ul32) uInitVar s0 s1 s2 s3 s4 (encodeBank stks) s6 s7 s8 s9)
      (some (haltList uTM [(getStk stks 0).head?.getD false]))
      (s0.length + s1.length + s2.length + s3.length + s4.length +
        (encodeBank stks).length + s6.length + s7.length + s8.length + s9.length + 2) := by
  cases stks with
  | nil =>
    have h1 : uTM.step (uCfg (some ul32) uInitVar s0 s1 s2 s3 s4 [] s6 s7 s8 s9) =
        some (uCfg (some ul33) (false, false, none) s0 s1 s2 s3 s4 [] s6 s7 s8 s9) := by
      change some (TM2.stepAux (uProg ul32) uInitVar _) = _
      simp only [uProg, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
        Option.isSome, cond_false, upd_u5]; rfl
    exact ((RIn.single h1).trans (u_drainAll false s0 s1 s2 s3 s4 [] s6 s7 s8 s9)).mono (by simp [encodeBank]; omega)
  | cons s ss =>
    cases s with
    | nil =>
      have h1 : uTM.step (uCfg (some ul32) uInitVar s0 s1 s2 s3 s4 (false :: encodeBank ss) s6 s7 s8 s9) =
          some (uCfg (some ul33) (false, false, none) s0 s1 s2 s3 s4 (encodeBank ss) s6 s7 s8 s9) := by
        change some (TM2.stepAux (uProg ul32) uInitVar _) = _
        simp only [uProg, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true, cond_false, upd_u5]; rfl
      refine ((RIn.single h1).trans (u_drainAll false s0 s1 s2 s3 s4 (encodeBank ss) s6 s7 s8 s9)).mono ?_
      simp [encodeBank, delimit]; omega
    | cons b s' =>
      have h1 : uTM.step (uCfg (some ul32) uInitVar s0 s1 s2 s3 s4
            (true :: b :: delimit s' ++ encodeBank ss) s6 s7 s8 s9) =
          some (uCfg (some ul33) (false, b, none) s0 s1 s2 s3 s4
            (delimit s' ++ encodeBank ss) s6 s7 s8 s9) := by
        change some (TM2.stepAux (uProg ul32) uInitVar _) = _
        simp only [uProg, TM2.stepAux, mkUStk,
          Option.isSome, Option.getD, upd_u5]; rfl
      have hbank : encodeBank ((b :: s') :: ss) = true :: b :: delimit s' ++ encodeBank ss := by
        simp [encodeBank, delimit]
      rw [hbank]
      refine ((RIn.single h1).trans
        (u_drainAll b s0 s1 s2 s3 s4 (delimit s' ++ encodeBank ss) s6 s7 s8 s9)).mono ?_
      simp [List.length_append]; omega

/- ### Phase A Lemmas -/

private lemma u_ul0 (z rest0 acc6 : List Bool) :
    RIn uTM.step (uCfg (some ul0) uInitVar (delimit (bitEncode z) ++ rest0) [] [] [] [] [] acc6 [] [] [])
      (some (uCfg (some ul1) uInitVar rest0 [] [] [] [] [] (z.reverse ++ acc6) [] [] []))
      (z.length + 1) := by
  induction z generalizing acc6 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul0) uInitVar _) = _
    simp only [uProg, ul0, bitEncode_list_nil, delimit, List.singleton_append, TM2.stepAux,
      mkUStk, List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, cond_false,
      upd_u0]
    rfl
  | cons b zs ih =>
    have h1 : uTM.step (uCfg (some ul0) uInitVar
          (delimit (bitEncode (b :: zs)) ++ rest0) [] [] [] [] [] acc6 [] [] []) =
        some (uCfg (some ul0) uInitVar
          (delimit (bitEncode zs) ++ rest0) [] [] [] [] [] (b :: acc6) [] [] []) := by
      change some (TM2.stepAux (uProg ul0) uInitVar _) = _
      rw [delimit_bitEncode_cons]
      simp only [uProg, ul0, List.cons_append, TM2.stepAux, mkUStk, List.head?_cons,
        List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u0, upd_u6]
      rfl
    have htr := (RIn.single h1).trans (ih (b :: acc6))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul1 (s0 s2 s6 : List Bool) :
    RIn uTM.step (uCfg (some ul1) uInitVar s0 [] s2 [] [] [] s6 [] [] [])
      (some (uCfg (some ul2) uInitVar s0 [] (s6.reverse ++ s2) [] [] [] [] [] [] []))
      (s6.length + 1) := by
  induction s6 generalizing s2 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul1) uInitVar _) = _
    simp only [uProg, ul1, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u6]; rfl
  | cons b xs ih =>
    have h1 : uTM.step (uCfg (some ul1) uInitVar s0 [] s2 [] [] [] (b :: xs) [] [] []) =
        some (uCfg (some ul1) uInitVar s0 [] (b :: s2) [] [] [] xs [] [] []) := by
      change some (TM2.stepAux (uProg ul1) uInitVar _) = _
      simp only [uProg, ul1, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u6, upd_u2]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s2))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul2 (y s2 acc6 : List Bool) :
    RIn uTM.step (uCfg (some ul2) uInitVar (bitEncode y) [] s2 [] [] [] acc6 [] [] [])
      (some (uCfg (some ul3) uInitVar [] [] s2 [] [] [] (y.reverse ++ acc6) [] [] []))
      (y.length + 1) := by
  induction y generalizing acc6 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul2) uInitVar _) = _
    simp only [uProg, ul2, bitEncode_list_nil, TM2.stepAux, mkUStk, List.head?_nil,
      List.tail_nil, Option.isSome, cond_false, upd_u0]; rfl
  | cons b ys ih =>
    have h1 : uTM.step (uCfg (some ul2) uInitVar (bitEncode (b :: ys)) [] s2 [] [] [] acc6 [] [] []) =
        some (uCfg (some ul2) uInitVar (bitEncode ys) [] s2 [] [] [] (b :: acc6) [] [] []) := by
      change some (TM2.stepAux (uProg ul2) uInitVar _) = _
      simp only [uProg, ul2, bitEncode_list_cons, TM2.stepAux, mkUStk, List.head?_cons,
        List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u0, upd_u6]; rfl
    have htr := (RIn.single h1).trans (ih (b :: acc6))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul3 (s2 s6 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul3) uInitVar [] [] s2 [] [] [] s6 [] [] s9)
      (some (uCfg (some ul4) uInitVar [] [] s2 [] [] [] [] [] [] (s6.reverse ++ s9)))
      (s6.length + 1) := by
  induction s6 generalizing s9 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul3) uInitVar _) = _
    simp only [uProg, ul3, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u6]; rfl
  | cons b xs ih =>
    have h1 : uTM.step (uCfg (some ul3) uInitVar [] [] s2 [] [] [] (b :: xs) [] [] s9) =
        some (uCfg (some ul3) uInitVar [] [] s2 [] [] [] xs [] [] (b :: s9)) := by
      change some (TM2.stepAux (uProg ul3) uInitVar _) = _
      simp only [uProg, ul3, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u6, upd_u9]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s9))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

/- ### Phase B Lemmas -/

private lemma u_ul4_some (blk rest acc6 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul4) uInitVar [] [] (delimit blk ++ rest) [] [] [] acc6 [] [] s9)
      (some (uCfg (some ul5) uInitVar [] [] rest [] [] [] (blk.reverse ++ acc6) [] [] s9))
      (blk.length + 1) := by
  induction blk generalizing acc6 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul4) uInitVar _) = _
    simp only [uProg, ul4, delimit, List.singleton_append, TM2.stepAux, mkUStk,
      List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, cond_false, upd_u2]; rfl
  | cons b bs ih =>
    have h1 : uTM.step (uCfg (some ul4) uInitVar [] [] (delimit (b :: bs) ++ rest) [] [] [] acc6 [] [] s9) =
        some (uCfg (some ul4) uInitVar [] [] (delimit bs ++ rest) [] [] [] (b :: acc6) [] [] s9) := by
      change some (TM2.stepAux (uProg ul4) uInitVar _) = _
      simp only [uProg, ul4, delimit, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u2, upd_u6]; rfl
    have htr := (RIn.single h1).trans (ih (b :: acc6))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul4_none (s2 acc6 s9 : List Bool) (h : undelimit s2 = none) :
    RIn uTM.step (uCfg (some ul4) uInitVar [] [] s2 [] [] [] acc6 [] [] s9)
      (some (haltList uTM [false]))
      (2 * s2.length + acc6.length + s9.length + 3) := by
  generalize hn : s2.length = n
  induction n using Nat.strong_induction_on generalizing s2 acc6 with
  | h n ih =>
    cases s2 with
    | nil =>
      have h1 : uTM.step (uCfg (some ul4) uInitVar [] [] [] [] [] [] acc6 [] [] s9) =
          some (uCfg (some ul40) uInitVar [] [] [] [] [] [] acc6 [] [] s9) := by
        change some (TM2.stepAux (uProg ul4) uInitVar _) = _
        simp only [uProg, ul4, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
          Option.isSome, cond_false, upd_u2]; rfl
      exact ((RIn.single h1).trans (u_abort uInitVar [] [] [] [] [] [] acc6 [] [] s9)).mono (by simp; omega)
    | cons hd tl =>
      cases hd with
      | false => simp [undelimit] at h
      | true =>
        cases tl with
        | nil =>
          have h1 : uTM.step (uCfg (some ul4) uInitVar [] [] [true] [] [] [] acc6 [] [] s9) =
              some (uCfg (some ul40) uInitVar [] [] [] [] [] [] acc6 [] [] s9) := by
            change some (TM2.stepAux (uProg ul4) uInitVar _) = _
            simp only [uProg, ul4, TM2.stepAux, mkUStk, List.head?_cons, List.head?_nil,
              List.tail_cons, List.tail_nil, Option.isSome, Option.getD, cond_true, cond_false, upd_u2]; rfl
          exact ((RIn.single h1).trans (u_abort uInitVar [] [] [] [] [] [] acc6 [] [] s9)).mono (by simp; omega)
        | cons b tl' =>
          have hnone : undelimit tl' = none := by
            simp only [undelimit, Option.map_eq_none_iff] at h; exact h
          have h1 : uTM.step (uCfg (some ul4) uInitVar [] [] (true :: b :: tl') [] [] [] acc6 [] [] s9) =
              some (uCfg (some ul4) uInitVar [] [] tl' [] [] [] (b :: acc6) [] [] s9) := by
            change some (TM2.stepAux (uProg ul4) uInitVar _) = _
            simp only [uProg, ul4, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
              Option.isSome, Option.getD, cond_true, upd_u2, upd_u6]; rfl
          have htr := (RIn.single h1).trans (ih tl'.length (by subst hn; simp) tl' (b :: acc6) hnone rfl)
          refine htr.mono ?_
          have hlen1 : (b :: acc6).length = acc6.length + 1 := rfl
          have hlen2 : (true :: b :: tl').length = tl'.length + 2 := rfl
          omega

private lemma u_ul5 (s1 s2 s6 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul5) uInitVar [] s1 s2 [] [] [] s6 [] [] s9)
      (some (uCfg (some ul6) uInitVar [] (s6.reverse ++ s1) s2 [] [] [] [] [] [] s9))
      (s6.length + 1) := by
  induction s6 generalizing s1 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul5) uInitVar _) = _
    simp only [uProg, ul5, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u6]; rfl
  | cons b xs ih =>
    have h1 : uTM.step (uCfg (some ul5) uInitVar [] s1 s2 [] [] [] (b :: xs) [] [] s9) =
        some (uCfg (some ul5) uInitVar [] (b :: s1) s2 [] [] [] xs [] [] s9) := by
      change some (TM2.stepAux (uProg ul5) uInitVar _) = _
      simp only [uProg, ul5, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u6, upd_u1]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s1))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul6_some (s1 blk rest acc6 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul6) uInitVar [] s1 (delimit blk ++ rest) [] [] [] acc6 [] [] s9)
      (some (uCfg (some ul7) uInitVar [] s1 rest [] [] [] (blk.reverse ++ acc6) [] [] s9))
      (blk.length + 1) := by
  induction blk generalizing acc6 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul6) uInitVar _) = _
    simp only [uProg, ul6, delimit, List.singleton_append, TM2.stepAux, mkUStk,
      List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, cond_false, upd_u2]; rfl
  | cons b bs ih =>
    have h1 : uTM.step (uCfg (some ul6) uInitVar [] s1 (delimit (b :: bs) ++ rest) [] [] [] acc6 [] [] s9) =
        some (uCfg (some ul6) uInitVar [] s1 (delimit bs ++ rest) [] [] [] (b :: acc6) [] [] s9) := by
      change some (TM2.stepAux (uProg ul6) uInitVar _) = _
      simp only [uProg, ul6, delimit, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u2, upd_u6]; rfl
    have htr := (RIn.single h1).trans (ih (b :: acc6))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul6_none (s1 s2 acc6 s9 : List Bool) (h : undelimit s2 = none) :
    RIn uTM.step (uCfg (some ul6) uInitVar [] s1 s2 [] [] [] acc6 [] [] s9)
      (some (haltList uTM [false]))
      (s1.length + 2 * s2.length + acc6.length + s9.length + 3) := by
  generalize hn : s2.length = n
  induction n using Nat.strong_induction_on generalizing s2 acc6 with
  | h n ih =>
    cases s2 with
    | nil =>
      have h1 : uTM.step (uCfg (some ul6) uInitVar [] s1 [] [] [] [] acc6 [] [] s9) =
          some (uCfg (some ul40) uInitVar [] s1 [] [] [] [] acc6 [] [] s9) := by
        change some (TM2.stepAux (uProg ul6) uInitVar _) = _
        simp only [uProg, ul6, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
          Option.isSome, cond_false, upd_u2]; rfl
      exact ((RIn.single h1).trans (u_abort uInitVar [] s1 [] [] [] [] acc6 [] [] s9)).mono (by simp; omega)
    | cons hd tl =>
      cases hd with
      | false => simp [undelimit] at h
      | true =>
        cases tl with
        | nil =>
          have h1 : uTM.step (uCfg (some ul6) uInitVar [] s1 [true] [] [] [] acc6 [] [] s9) =
              some (uCfg (some ul40) uInitVar [] s1 [] [] [] [] acc6 [] [] s9) := by
            change some (TM2.stepAux (uProg ul6) uInitVar _) = _
            simp only [uProg, ul6, TM2.stepAux, mkUStk, List.head?_cons, List.head?_nil,
              List.tail_cons, List.tail_nil, Option.isSome, Option.getD, cond_true, cond_false, upd_u2]; rfl
          exact ((RIn.single h1).trans (u_abort uInitVar [] s1 [] [] [] [] acc6 [] [] s9)).mono (by simp; omega)
        | cons b tl' =>
          have hnone : undelimit tl' = none := by
            simp only [undelimit, Option.map_eq_none_iff] at h; exact h
          have h1 : uTM.step (uCfg (some ul6) uInitVar [] s1 (true :: b :: tl') [] [] [] acc6 [] [] s9) =
              some (uCfg (some ul6) uInitVar [] s1 tl' [] [] [] (b :: acc6) [] [] s9) := by
            change some (TM2.stepAux (uProg ul6) uInitVar _) = _
            simp only [uProg, ul6, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
              Option.isSome, Option.getD, cond_true, upd_u2, upd_u6]; rfl
          have htr := (RIn.single h1).trans (ih tl'.length (by subst hn; simp) tl' (b :: acc6) hnone rfl)
          refine htr.mono ?_
          have hlen1 : (b :: acc6).length = acc6.length + 1 := rfl
          have hlen2 : (true :: b :: tl').length = tl'.length + 2 := rfl
          omega

private lemma u_ul7 (s1 s2 s6 s8 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul7) uInitVar [] s1 s2 [] [] [] s6 [] s8 s9)
      (some (uCfg (some ul8) uInitVar [] s1 s2 [] [] [] [] [] (s6.reverse ++ s8) s9))
      (s6.length + 1) := by
  induction s6 generalizing s8 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul7) uInitVar _) = _
    simp only [uProg, ul7, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u6]; rfl
  | cons b xs ih =>
    have h1 : uTM.step (uCfg (some ul7) uInitVar [] s1 s2 [] [] [] (b :: xs) [] s8 s9) =
        some (uCfg (some ul7) uInitVar [] s1 s2 [] [] [] xs [] (b :: s8) s9) := by
      change some (TM2.stepAux (uProg ul7) uInitVar _) = _
      simp only [uProg, ul7, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u6, upd_u8]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s8))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul8_some (s1 blk rest acc6 s8 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul8) uInitVar [] s1 (delimit blk ++ rest) [] [] [] acc6 [] s8 s9)
      (some (uCfg (some ul9) uInitVar [] s1 rest [] [] [] (blk.reverse ++ acc6) [] s8 s9))
      (blk.length + 1) := by
  induction blk generalizing acc6 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul8) uInitVar _) = _
    simp only [uProg, ul8, delimit, List.singleton_append, TM2.stepAux, mkUStk,
      List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, cond_false, upd_u2]; rfl
  | cons b bs ih =>
    have h1 : uTM.step (uCfg (some ul8) uInitVar [] s1 (delimit (b :: bs) ++ rest) [] [] [] acc6 [] s8 s9) =
        some (uCfg (some ul8) uInitVar [] s1 (delimit bs ++ rest) [] [] [] (b :: acc6) [] s8 s9) := by
      change some (TM2.stepAux (uProg ul8) uInitVar _) = _
      simp only [uProg, ul8, delimit, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u2, upd_u6]; rfl
    have htr := (RIn.single h1).trans (ih (b :: acc6))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul8_none (s1 s2 acc6 s8 s9 : List Bool) (h : undelimit s2 = none) :
    RIn uTM.step (uCfg (some ul8) uInitVar [] s1 s2 [] [] [] acc6 [] s8 s9)
      (some (haltList uTM [false]))
      (s1.length + 2 * s2.length + acc6.length + s8.length + s9.length + 3) := by
  generalize hn : s2.length = n
  induction n using Nat.strong_induction_on generalizing s2 acc6 with
  | h n ih =>
    cases s2 with
    | nil =>
      have h1 : uTM.step (uCfg (some ul8) uInitVar [] s1 [] [] [] [] acc6 [] s8 s9) =
          some (uCfg (some ul40) uInitVar [] s1 [] [] [] [] acc6 [] s8 s9) := by
        change some (TM2.stepAux (uProg ul8) uInitVar _) = _
        simp only [uProg, ul8, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
          Option.isSome, cond_false, upd_u2]; rfl
      exact ((RIn.single h1).trans (u_abort uInitVar [] s1 [] [] [] [] acc6 [] s8 s9)).mono (by simp; omega)
    | cons hd tl =>
      cases hd with
      | false => simp [undelimit] at h
      | true =>
        cases tl with
        | nil =>
          have h1 : uTM.step (uCfg (some ul8) uInitVar [] s1 [true] [] [] [] acc6 [] s8 s9) =
              some (uCfg (some ul40) uInitVar [] s1 [] [] [] [] acc6 [] s8 s9) := by
            change some (TM2.stepAux (uProg ul8) uInitVar _) = _
            simp only [uProg, ul8, TM2.stepAux, mkUStk, List.head?_cons, List.head?_nil,
              List.tail_cons, List.tail_nil, Option.isSome, Option.getD, cond_true, cond_false, upd_u2]; rfl
          exact ((RIn.single h1).trans (u_abort uInitVar [] s1 [] [] [] [] acc6 [] s8 s9)).mono (by simp; omega)
        | cons b tl' =>
          have hnone : undelimit tl' = none := by
            simp only [undelimit, Option.map_eq_none_iff] at h; exact h
          have h1 : uTM.step (uCfg (some ul8) uInitVar [] s1 (true :: b :: tl') [] [] [] acc6 [] s8 s9) =
              some (uCfg (some ul8) uInitVar [] s1 tl' [] [] [] (b :: acc6) [] s8 s9) := by
            change some (TM2.stepAux (uProg ul8) uInitVar _) = _
            simp only [uProg, ul8, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
              Option.isSome, Option.getD, cond_true, upd_u2, upd_u6]; rfl
          have htr := (RIn.single h1).trans (ih tl'.length (by subst hn; simp) tl' (b :: acc6) hnone rfl)
          refine htr.mono ?_
          have hlen1 : (b :: acc6).length = acc6.length + 1 := rfl
          have hlen2 : (true :: b :: tl').length = tl'.length + 2 := rfl
          omega

private lemma u_ul9 (s1 s2 s4 s6 s8 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul9) uInitVar [] s1 s2 [] s4 [] s6 [] s8 s9)
      (some (uCfg (some ul10) uInitVar [] s1 [] [] (s2.reverse ++ s4) [] s6 [] s8 s9))
      (s2.length + 1) := by
  induction s2 generalizing s4 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul9) uInitVar _) = _
    simp only [uProg, ul9, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u2]; rfl
  | cons b xs ih =>
    have h1 : uTM.step (uCfg (some ul9) uInitVar [] s1 (b :: xs) [] s4 [] s6 [] s8 s9) =
        some (uCfg (some ul9) uInitVar [] s1 xs [] (b :: s4) [] s6 [] s8 s9) := by
      change some (TM2.stepAux (uProg ul9) uInitVar _) = _
      simp only [uProg, ul9, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u2, upd_u4]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s4))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul10 (s1 s3 s4 s6 s8 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul10) uInitVar [] s1 [] s3 s4 [] s6 [] s8 s9)
      (some (uCfg (some ul11) uInitVar [] s1 [] (s6.reverse ++ s3) s4 [] [] [] s8 s9))
      (s6.length + 1) := by
  induction s6 generalizing s3 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul10) uInitVar _) = _
    simp only [uProg, ul10, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u6]; rfl
  | cons b xs ih =>
    have h1 : uTM.step (uCfg (some ul10) uInitVar [] s1 [] s3 s4 [] (b :: xs) [] s8 s9) =
        some (uCfg (some ul10) uInitVar [] s1 [] (b :: s3) s4 [] xs [] s8 s9) := by
      change some (TM2.stepAux (uProg ul10) uInitVar _) = _
      simp only [uProg, ul10, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u6, upd_u3]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s3))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul11 (s1 s2 s3 s4 s8 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul11) uInitVar [] s1 s2 s3 s4 [] [] [] s8 s9)
      (some (uCfg (some ul12) uInitVar [] s1 (s8.reverse ++ s2) s3 s4 [] [] [] [] s9))
      (s8.length + 1) := by
  induction s8 generalizing s2 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul11) uInitVar _) = _
    simp only [uProg, ul11, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u8]; rfl
  | cons b xs ih =>
    have h1 : uTM.step (uCfg (some ul11) uInitVar [] s1 s2 s3 s4 [] [] [] (b :: xs) s9) =
        some (uCfg (some ul11) uInitVar [] s1 (b :: s2) s3 s4 [] [] [] xs s9) := by
      change some (TM2.stepAux (uProg ul11) uInitVar _) = _
      simp only [uProg, ul11, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u8, upd_u2]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s2))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul12_ok (s1 s2 s3 s4 acc6 s9 : List Bool) (hle : s9.length ≤ s3.length) :
    ∃ s3', s3'.length = s3.length - s9.length ∧
      RIn uTM.step (uCfg (some ul12) uInitVar [] s1 s2 s3 s4 [] acc6 [] [] s9)
        (some (uCfg (some ul13) uInitVar [] s1 s2 s3' s4 [] (s9.reverse ++ acc6) [] [] []))
        (s9.length + 1) := by
  induction s9 generalizing s3 acc6 with
  | nil =>
    refine ⟨s3, by simp, RIn.single ?_⟩
    change some (TM2.stepAux (uProg ul12) uInitVar _) = _
    simp only [uProg, ul12, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u9]; rfl
  | cons b ys ih =>
    cases s3 with
    | nil => simp at hle
    | cons c3 s3' =>
      have h1 : uTM.step (uCfg (some ul12) uInitVar [] s1 s2 (c3 :: s3') s4 [] acc6 [] [] (b :: ys)) =
          some (uCfg (some ul12) uInitVar [] s1 s2 s3' s4 [] (b :: acc6) [] [] ys) := by
        change some (TM2.stepAux (uProg ul12) uInitVar _) = _
        simp only [uProg, ul12, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true, upd_u9, upd_u6, upd_u3]; rfl
      obtain ⟨s3'', hlen, htr⟩ := ih s3' (b :: acc6) (by simp at hle; omega)
      refine ⟨s3'', by simp at hlen ⊢; omega, ?_⟩
      have hc := (RIn.single h1).trans htr
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      refine hc.mono ?_
      have : (b :: ys).length = ys.length + 1 := rfl
      omega

private lemma u_ul12_fail (s1 s2 s3 s4 acc6 s9 : List Bool) (hlt : s3.length < s9.length) :
    RIn uTM.step (uCfg (some ul12) uInitVar [] s1 s2 s3 s4 [] acc6 [] [] s9)
      (some (haltList uTM [false]))
      (s1.length + s2.length + s3.length + s4.length + acc6.length + s9.length + 4) := by
  induction s3 generalizing acc6 s9 with
  | nil =>
    cases s9 with
    | nil => simp at hlt
    | cons b ys =>
      have h1 : uTM.step (uCfg (some ul12) uInitVar [] s1 s2 [] s4 [] acc6 [] [] (b :: ys)) =
          some (uCfg (some ul40) uInitVar [] s1 s2 [] s4 [] (b :: acc6) [] [] ys) := by
        change some (TM2.stepAux (uProg ul12) uInitVar _) = _
        simp only [uProg, ul12, TM2.stepAux, mkUStk, List.head?_cons, List.head?_nil,
          List.tail_cons, List.tail_nil, Option.isSome, Option.getD, cond_true, cond_false,
          upd_u9, upd_u6, upd_u3]; rfl
      exact ((RIn.single h1).trans (u_abort uInitVar [] s1 s2 [] s4 [] (b :: acc6) [] [] ys)).mono
        (by simp; omega)
  | cons c3 s3' ih =>
    cases s9 with
    | nil => simp at hlt
    | cons b ys =>
      have h1 : uTM.step (uCfg (some ul12) uInitVar [] s1 s2 (c3 :: s3') s4 [] acc6 [] [] (b :: ys)) =
          some (uCfg (some ul12) uInitVar [] s1 s2 s3' s4 [] (b :: acc6) [] [] ys) := by
        change some (TM2.stepAux (uProg ul12) uInitVar _) = _
        simp only [uProg, ul12, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true, upd_u9, upd_u6, upd_u3]; rfl
      refine ((RIn.single h1).trans (ih (b :: acc6) ys (by simp at hlt; omega))).mono ?_
      have h1' : (b :: acc6).length = acc6.length + 1 := rfl
      have h2' : (c3 :: s3').length = s3'.length + 1 := rfl
      have h3' : (b :: ys).length = ys.length + 1 := rfl
      omega

private lemma u_ul13 (s1 s2 s3 s4 s6 : List Bool) :
    RIn uTM.step (uCfg (some ul13) uInitVar [] s1 s2 s3 s4 [] s6 [] [] [])
      (some (uCfg (some ul14) uInitVar [] s1 s2 [] s4 [false] s6 [] [] []))
      (s3.length + 1) := by
  induction s3 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul13) uInitVar _) = _
    simp only [uProg, ul13, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u3, upd_u5]; rfl
  | cons c3 s3' ih =>
    have h1 : uTM.step (uCfg (some ul13) uInitVar [] s1 s2 (c3 :: s3') s4 [] s6 [] [] []) =
        some (uCfg (some ul13) uInitVar [] s1 s2 s3' s4 [] s6 [] [] []) := by
      change some (TM2.stepAux (uProg ul13) uInitVar _) = _
      simp only [uProg, ul13, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, cond_true, upd_u3]; rfl
    exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)

/- ### Phase C Lemmas -/

private lemma u_ul14 (s1 s2 s4 yRev ysuf : List Bool) :
    RIn uTM.step (uCfg (some ul14) uInitVar [] s1 s2 [] s4 (delimit (bitEncode ysuf)) yRev [] [] [])
      (some (uCfg (some ul15) uInitVar [] s1 s2 [] s4
        ([true, false] ++ delimit (bitEncode (yRev.reverse ++ ysuf))) [] [] [] []))
      (yRev.length + 1) := by
  induction yRev generalizing ysuf with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul14) uInitVar _) = _
    dsimp only [uProg, ul14, List.reverse_nil, List.nil_append, TM2.stepAux, mkUStk,
      List.head?_nil, List.tail_nil, Option.isSome, cond_false]
    rw [upd_u6, stepAux_pushBitsU]
    simp only [mkUStk, upd_u5, TM2.stepAux, List.cons_append, List.nil_append]
    rfl
  | cons b yr ih =>
    have hstep : uTM.step (uCfg (some ul14) uInitVar [] s1 s2 [] s4
          (delimit (bitEncode ysuf)) (b :: yr) [] [] []) =
        some (uCfg (some ul14) uInitVar [] s1 s2 [] s4
          (delimit (bitEncode (b :: ysuf))) yr [] [] []) := by
      cases b
      · change some (TM2.stepAux (uProg ul14) uInitVar _) = _
        dsimp only [uProg, ul14, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true, cond_false]
        rw [upd_u6, stepAux_pushBitsU]
        simp only [mkUStk, upd_u5, TM2.stepAux, delimit_bitEncode_cons, List.cons_append,
          List.nil_append]
        rfl
      · change some (TM2.stepAux (uProg ul14) uInitVar _) = _
        dsimp only [uProg, ul14, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true]
        rw [upd_u6, stepAux_pushBitsU]
        simp only [mkUStk, upd_u5, TM2.stepAux, delimit_bitEncode_cons, List.cons_append,
          List.nil_append]
        rfl
    have htr := (RIn.single hstep).trans (ih (b :: ysuf))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul15 (s1 s4 xRev xsuf y : List Bool) :
    RIn uTM.step (uCfg (some ul15) uInitVar [] s1 xRev [] s4
        ((delimit (bitEncode xsuf)).flatMap (fun c => [true, c]) ++ delimit (bitEncode y))
        [] [] [] [])
      (some (uCfg (some ul16) uInitVar [] s1 [] [] s4
        ((delimit (bitEncode (xRev.reverse ++ xsuf))).flatMap (fun c => [true, c]) ++
          delimit (bitEncode y))
        [] [] [] []))
      (xRev.length + 1) := by
  induction xRev generalizing xsuf with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul15) uInitVar _) = _
    simp only [uProg, ul15, List.reverse_nil, List.nil_append, TM2.stepAux, mkUStk,
      List.head?_nil, List.tail_nil, Option.isSome, cond_false, upd_u2]; rfl
  | cons b xr ih =>
    have hstep : uTM.step (uCfg (some ul15) uInitVar [] s1 (b :: xr) [] s4
          ((delimit (bitEncode xsuf)).flatMap (fun c => [true, c]) ++ delimit (bitEncode y))
          [] [] [] []) =
        some (uCfg (some ul15) uInitVar [] s1 xr [] s4
          ((delimit (bitEncode (b :: xsuf))).flatMap (fun c => [true, c]) ++ delimit (bitEncode y))
          [] [] [] []) := by
      cases b
      · change some (TM2.stepAux (uProg ul15) uInitVar _) = _
        dsimp only [uProg, ul15, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true, cond_false]
        rw [upd_u2, stepAux_pushBitsU]
        simp only [mkUStk, upd_u5, TM2.stepAux]
        rw [delimit_bitEncode_pair_step false xsuf (delimit (bitEncode y))]
        rfl
      · change some (TM2.stepAux (uProg ul15) uInitVar _) = _
        dsimp only [uProg, ul15, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true]
        rw [upd_u2, stepAux_pushBitsU]
        simp only [mkUStk, upd_u5, TM2.stepAux]
        rw [delimit_bitEncode_pair_step true xsuf (delimit (bitEncode y))]
        rfl
    have htr := (RIn.single hstep).trans (ih (b :: xsuf))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

/- ### Phase D Lemmas -/

private lemma u_ul18_some (blk rest s4 s5 acc6 s8 : List Bool) :
    RIn uTM.step (uCfg (some ul18) uInitVar [] (delimit blk ++ rest) [] [] s4 s5 acc6 [] s8 [])
      (some (uCfg (some ul20) uInitVar [] rest [] [] s4 s5 ((delimit blk).reverse ++ acc6) []
        (blk.reverse ++ s8) []))
      (blk.length + 1) := by
  induction blk generalizing acc6 s8 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul18) uInitVar _) = _
    simp only [uProg, ul18, delimit, List.singleton_append, TM2.stepAux, mkUStk,
      List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, cond_false,
      upd_u1, upd_u6, List.reverse_cons, List.reverse_nil, List.nil_append]; rfl
  | cons b bs ih =>
    have h1 : uTM.step (uCfg (some ul18) uInitVar [] (delimit (b :: bs) ++ rest) [] [] s4 s5 acc6 [] s8 []) =
        some (uCfg (some ul18) uInitVar [] (delimit bs ++ rest) [] [] s4 s5 (b :: true :: acc6) []
          (b :: s8) []) := by
      change some (TM2.stepAux (uProg ul18) uInitVar _) = _
      simp only [uProg, ul18, delimit, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true,
        upd_u1, upd_u6, upd_u8]; rfl
    have htr := (RIn.single h1).trans (ih (b :: true :: acc6) (b :: s8))
    simp only [delimit, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul18_none (s1 s4 s5 acc6 s8 : List Bool) (h : undelimit s1 = none) :
    RIn uTM.step (uCfg (some ul18) uInitVar [] s1 [] [] s4 s5 acc6 [] s8 [])
      (some (haltList uTM [false]))
      (2 * s1.length + s4.length + s5.length + acc6.length + s8.length + 4) := by
  generalize hn : s1.length = n
  induction n using Nat.strong_induction_on generalizing s1 acc6 s8 with
  | h n ih =>
    cases s1 with
    | nil =>
      have h1 : uTM.step (uCfg (some ul18) uInitVar [] [] [] [] s4 s5 acc6 [] s8 []) =
          some (uCfg (some ul40) uInitVar [] [] [] [] s4 s5 acc6 [] s8 []) := by
        change some (TM2.stepAux (uProg ul18) uInitVar _) = _
        simp only [uProg, ul18, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
          Option.isSome, cond_false, upd_u1]; rfl
      exact ((RIn.single h1).trans (u_abort uInitVar [] [] [] [] s4 s5 acc6 [] s8 [])).mono
        (by simp; omega)
    | cons hd tl =>
      cases hd with
      | false => simp [undelimit] at h
      | true =>
        cases tl with
        | nil =>
          have h1 : uTM.step (uCfg (some ul18) uInitVar [] [true] [] [] s4 s5 acc6 [] s8 []) =
              some (uCfg (some ul40) uInitVar [] [] [] [] s4 s5 (true :: acc6) [] s8 []) := by
            change some (TM2.stepAux (uProg ul18) uInitVar _) = _
            simp only [uProg, ul18, TM2.stepAux, mkUStk, List.head?_cons, List.head?_nil,
              List.tail_cons, List.tail_nil, Option.isSome, Option.getD, cond_true, cond_false,
              upd_u1, upd_u6]; rfl
          exact ((RIn.single h1).trans (u_abort uInitVar [] [] [] [] s4 s5 (true :: acc6) [] s8 [])).mono
            (by simp; omega)
        | cons b tl' =>
          have hnone : undelimit tl' = none := by
            simp only [undelimit, Option.map_eq_none_iff] at h; exact h
          have h1 : uTM.step (uCfg (some ul18) uInitVar [] (true :: b :: tl') [] [] s4 s5 acc6 [] s8 []) =
              some (uCfg (some ul18) uInitVar [] tl' [] [] s4 s5 (b :: true :: acc6) [] (b :: s8) []) := by
            change some (TM2.stepAux (uProg ul18) uInitVar _) = _
            simp only [uProg, ul18, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
              Option.isSome, Option.getD, cond_true, upd_u1, upd_u6, upd_u8]; rfl
          have htr := (RIn.single h1).trans
            (ih tl'.length (by subst hn; simp) tl' (b :: true :: acc6) (b :: s8) hnone rfl)
          refine htr.mono ?_
          have h1' : (b :: true :: acc6).length = acc6.length + 2 := rfl
          have h2' : (b :: s8).length = s8.length + 1 := rfl
          have h3' : (true :: b :: tl').length = tl'.length + 2 := rfl
          omega

private lemma u_ul19_some (blk rest s4 s5 acc6 s7 : List Bool) :
    RIn uTM.step (uCfg (some ul19) uInitVar [] (delimit blk ++ rest) [] [] s4 s5 acc6 s7 [] [])
      (some (uCfg (some ul17) uInitVar [] rest [] [] s4 s5 ((delimit blk).reverse ++ acc6) s7 [] []))
      (blk.length + 1) := by
  induction blk generalizing acc6 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul19) uInitVar _) = _
    simp only [uProg, ul19, delimit, List.singleton_append, TM2.stepAux, mkUStk,
      List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, cond_false,
      upd_u1, upd_u6, List.reverse_cons, List.reverse_nil, List.nil_append]; rfl
  | cons b bs ih =>
    have h1 : uTM.step (uCfg (some ul19) uInitVar [] (delimit (b :: bs) ++ rest) [] [] s4 s5 acc6 s7 [] []) =
        some (uCfg (some ul19) uInitVar [] (delimit bs ++ rest) [] [] s4 s5 (b :: true :: acc6) s7 [] []) := by
      change some (TM2.stepAux (uProg ul19) uInitVar _) = _
      simp only [uProg, ul19, delimit, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true,
        upd_u1, upd_u6]; rfl
    have htr := (RIn.single h1).trans (ih (b :: true :: acc6))
    simp only [delimit, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul19_none (s1 s4 s5 acc6 s7 : List Bool) (h : undelimit s1 = none) :
    RIn uTM.step (uCfg (some ul19) uInitVar [] s1 [] [] s4 s5 acc6 s7 [] [])
      (some (haltList uTM [false]))
      (2 * s1.length + s4.length + s5.length + acc6.length + s7.length + 4) := by
  generalize hn : s1.length = n
  induction n using Nat.strong_induction_on generalizing s1 acc6 with
  | h n ih =>
    cases s1 with
    | nil =>
      have h1 : uTM.step (uCfg (some ul19) uInitVar [] [] [] [] s4 s5 acc6 s7 [] []) =
          some (uCfg (some ul40) uInitVar [] [] [] [] s4 s5 acc6 s7 [] []) := by
        change some (TM2.stepAux (uProg ul19) uInitVar _) = _
        simp only [uProg, ul19, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
          Option.isSome, cond_false, upd_u1]; rfl
      exact ((RIn.single h1).trans (u_abort uInitVar [] [] [] [] s4 s5 acc6 s7 [] [])).mono
        (by simp; omega)
    | cons hd tl =>
      cases hd with
      | false => simp [undelimit] at h
      | true =>
        cases tl with
        | nil =>
          have h1 : uTM.step (uCfg (some ul19) uInitVar [] [true] [] [] s4 s5 acc6 s7 [] []) =
              some (uCfg (some ul40) uInitVar [] [] [] [] s4 s5 (true :: acc6) s7 [] []) := by
            change some (TM2.stepAux (uProg ul19) uInitVar _) = _
            simp only [uProg, ul19, TM2.stepAux, mkUStk, List.head?_cons, List.head?_nil,
              List.tail_cons, List.tail_nil, Option.isSome, Option.getD, cond_true, cond_false,
              upd_u1, upd_u6]; rfl
          exact ((RIn.single h1).trans (u_abort uInitVar [] [] [] [] s4 s5 (true :: acc6) s7 [] [])).mono
            (by simp; omega)
        | cons b tl' =>
          have hnone : undelimit tl' = none := by
            simp only [undelimit, Option.map_eq_none_iff] at h; exact h
          have h1 : uTM.step (uCfg (some ul19) uInitVar [] (true :: b :: tl') [] [] s4 s5 acc6 s7 [] []) =
              some (uCfg (some ul19) uInitVar [] tl' [] [] s4 s5 (b :: true :: acc6) s7 [] []) := by
            change some (TM2.stepAux (uProg ul19) uInitVar _) = _
            simp only [uProg, ul19, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
              Option.isSome, Option.getD, cond_true, upd_u1, upd_u6]; rfl
          have htr := (RIn.single h1).trans
            (ih tl'.length (by subst hn; simp) tl' (b :: true :: acc6) hnone rfl)
          refine htr.mono ?_
          have h1' : (b :: true :: acc6).length = acc6.length + 2 := rfl
          have h2' : (true :: b :: tl').length = tl'.length + 2 := rfl
          omega

private lemma u_ul20 (s1 s4 s5 s6 s8 : List Bool) :
    RIn uTM.step (uCfg (some ul20) uInitVar [] s1 [] [] s4 s5 s6 [] s8 [])
      (some (uCfg (some ul21) uInitVar [] (s6.reverse ++ s1) [] [] s4 s5 [] [] s8 []))
      (s6.length + 1) := by
  induction s6 generalizing s1 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul20) uInitVar _) = _
    simp only [uProg, ul20, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u6]; rfl
  | cons b xs ih =>
    have h1 : uTM.step (uCfg (some ul20) uInitVar [] s1 [] [] s4 s5 (b :: xs) [] s8 []) =
        some (uCfg (some ul20) uInitVar [] (b :: s1) [] [] s4 s5 xs [] s8 []) := by
      change some (TM2.stepAux (uProg ul20) uInitVar _) = _
      simp only [uProg, ul20, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u6, upd_u1]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s1))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul21 (s0 s1 s4 s5 s8 : List Bool) :
    RIn uTM.step (uCfg (some ul21) uInitVar s0 s1 [] [] s4 s5 [] [] s8 [])
      (some (uCfg (some ul22) uInitVar (s8.reverse ++ s0) s1 [] [] s4 s5 [] [] [] []))
      (s8.length + 1) := by
  induction s8 generalizing s0 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul21) uInitVar _) = _
    simp only [uProg, ul21, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u8]; rfl
  | cons b xs ih =>
    have h1 : uTM.step (uCfg (some ul21) uInitVar s0 s1 [] [] s4 s5 [] [] (b :: xs) []) =
        some (uCfg (some ul21) uInitVar (b :: s0) s1 [] [] s4 s5 [] [] xs []) := by
      change some (TM2.stepAux (uProg ul21) uInitVar _) = _
      simp only [uProg, ul21, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u8, upd_u0]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s0))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul17_some_some (progBits s1_rem acc6 s4 : List Bool) (stks : List (List Bool))
    (pc : ℕ) (blk : List Bool)
    (hsplit : acc6.reverse ++ s1_rem = progBits)
    (hfetch : fetchBlock s1_rem pc = some (some blk)) :
    RIn uTM.step (uCfg (some ul17) uInitVar [] s1_rem [] [] s4 (encodeBank stks) acc6
        (List.replicate pc true) [] [])
      (some (uCfg (some ul22) uInitVar blk progBits [] [] s4 (encodeBank stks) [] [] [] []))
      (2 * s1_rem.length + progBits.length + 4 * blk.length + 6) := by
  induction pc generalizing s1_rem acc6 with
  | zero =>
    cases s1_rem with
    | nil => simp [fetchBlock] at hfetch
    | cons hd tl =>
      simp only [fetchBlock, Option.map_eq_some_iff] at hfetch
      rcases hfetch with ⟨⟨blk', rest⟩, hund, hblk⟩
      have hbeq : blk' = blk := Option.some.inj hblk
      subst blk'
      have hs1 : hd :: tl = delimit blk ++ rest := eq_delimit_append_of_undelimit (hd :: tl) blk rest hund
      have h1 : uTM.step (uCfg (some ul17) uInitVar [] (hd :: tl) [] [] s4 (encodeBank stks) acc6 [] [] []) =
          some (uCfg (some ul18) uInitVar [] (hd :: tl) [] [] s4 (encodeBank stks) acc6 [] [] []) := by
        change some (TM2.stepAux (uProg ul17) uInitVar _) = _
        simp only [uProg, TM2.stepAux, mkUStk, List.head?_cons, List.head?_nil,
          List.tail_nil, Option.isSome, cond_true, cond_false, upd_u7]; rfl
      have h18 := u_ul18_some blk rest s4 (encodeBank stks) acc6 []
      rw [← hs1, List.append_nil] at h18
      have h20 := u_ul20 rest s4 (encodeBank stks) ((delimit blk).reverse ++ acc6) blk.reverse
      rw [List.reverse_append, List.reverse_reverse, List.append_assoc, ← hs1, hsplit] at h20
      have h21 := u_ul21 [] progBits s4 (encodeBank stks) blk.reverse
      rw [List.reverse_reverse, List.append_nil] at h21
      have hc := (((RIn.single h1).trans h18).trans h20).trans h21
      have hacc_le : acc6.length + (hd :: tl).length = progBits.length := by
        rw [← hsplit, List.length_append, List.length_reverse]
      refine hc.mono ?_
      simp only [List.length_append, List.length_reverse, length_delimit]
      omega
  | succ pc ih =>
    cases s1_rem with
    | nil => simp [fetchBlock] at hfetch
    | cons hd tl =>
      simp only [fetchBlock, Option.bind_eq_some_iff] at hfetch
      rcases hfetch with ⟨⟨blk0, rest⟩, hund, hfetch'⟩
      have hs1 : hd :: tl = delimit blk0 ++ rest := eq_delimit_append_of_undelimit (hd :: tl) blk0 rest hund
      have h1 : uTM.step (uCfg (some ul17) uInitVar [] (hd :: tl) [] [] s4 (encodeBank stks) acc6
            (List.replicate (pc + 1) true) [] []) =
          some (uCfg (some ul19) uInitVar [] (hd :: tl) [] [] s4 (encodeBank stks) acc6
            (List.replicate pc true) [] []) := by
        change some (TM2.stepAux (uProg ul17) uInitVar _) = _
        simp only [uProg, List.replicate_succ, TM2.stepAux, mkUStk, List.head?_cons,
          List.tail_cons, Option.isSome, cond_true, upd_u7]; rfl
      have h19 := u_ul19_some blk0 rest s4 (encodeBank stks) acc6 (List.replicate pc true)
      rw [← hs1] at h19
      have hsplit' : ((delimit blk0).reverse ++ acc6).reverse ++ rest = progBits := by
        rw [List.reverse_append, List.reverse_reverse, List.append_assoc, ← hs1, hsplit]
      have hih := ih rest ((delimit blk0).reverse ++ acc6) hsplit' hfetch'
      have hc := ((RIn.single h1).trans h19).trans hih
      have hblk0_le : 2 * blk0.length + 1 + rest.length = (hd :: tl).length := by
        rw [hs1, List.length_append, length_delimit]
      refine hc.mono ?_
      omega

private lemma u_ul17_some_none (s1_rem acc6 s4 : List Bool) (stks : List (List Bool)) (pc : ℕ)
    (hfetch : fetchBlock s1_rem pc = some none) :
    RIn uTM.step (uCfg (some ul17) uInitVar [] s1_rem [] [] s4 (encodeBank stks) acc6
        (List.replicate pc true) [] [])
      (some (haltList uTM [(getStk stks 0).head?.getD false]))
      (2 * s1_rem.length + s4.length + (encodeBank stks).length + acc6.length + pc + 4) := by
  induction pc generalizing s1_rem acc6 with
  | zero =>
    cases s1_rem with
    | nil =>
      have h1 : uTM.step (uCfg (some ul17) uInitVar [] [] [] [] s4 (encodeBank stks) acc6 [] [] []) =
          some (uCfg (some ul32) uInitVar [] [] [] [] s4 (encodeBank stks) acc6 [] [] []) := by
        change some (TM2.stepAux (uProg ul17) uInitVar _) = _
        simp only [uProg, TM2.stepAux, mkUStk, List.head?_nil, Option.isSome,
          cond_false]; rfl
      exact ((RIn.single h1).trans (u_readOut32 [] [] [] [] s4 acc6 [] [] [] stks)).mono
        (by simp; omega)
    | cons hd tl =>
      simp only [fetchBlock, Option.map_eq_some_iff] at hfetch
      rcases hfetch with ⟨_, _, h⟩
      cases h
  | succ pc ih =>
    cases s1_rem with
    | nil =>
      have h1 : uTM.step (uCfg (some ul17) uInitVar [] [] [] [] s4 (encodeBank stks) acc6
            (List.replicate (pc + 1) true) [] []) =
          some (uCfg (some ul32) uInitVar [] [] [] [] s4 (encodeBank stks) acc6
            (List.replicate (pc + 1) true) [] []) := by
        change some (TM2.stepAux (uProg ul17) uInitVar _) = _
        simp only [uProg, TM2.stepAux, mkUStk, List.head?_nil, Option.isSome,
          cond_false]; rfl
      exact ((RIn.single h1).trans
        (u_readOut32 [] [] [] [] s4 acc6 (List.replicate (pc + 1) true) [] [] stks)).mono
        (by simp; omega)
    | cons hd tl =>
      simp only [fetchBlock, Option.bind_eq_some_iff] at hfetch
      rcases hfetch with ⟨⟨blk0, rest⟩, hund, hfetch'⟩
      have hs1 : hd :: tl = delimit blk0 ++ rest := eq_delimit_append_of_undelimit (hd :: tl) blk0 rest hund
      have h1 : uTM.step (uCfg (some ul17) uInitVar [] (hd :: tl) [] [] s4 (encodeBank stks) acc6
            (List.replicate (pc + 1) true) [] []) =
          some (uCfg (some ul19) uInitVar [] (hd :: tl) [] [] s4 (encodeBank stks) acc6
            (List.replicate pc true) [] []) := by
        change some (TM2.stepAux (uProg ul17) uInitVar _) = _
        simp only [uProg, List.replicate_succ, TM2.stepAux, mkUStk, List.head?_cons,
          List.tail_cons, Option.isSome, cond_true, upd_u7]; rfl
      have h19 := u_ul19_some blk0 rest s4 (encodeBank stks) acc6 (List.replicate pc true)
      rw [← hs1] at h19
      have hih := ih rest ((delimit blk0).reverse ++ acc6) hfetch'
      have hc := ((RIn.single h1).trans h19).trans hih
      have hblk0_le : 2 * blk0.length + 1 + rest.length = (hd :: tl).length := by
        rw [hs1, List.length_append, length_delimit]
      refine hc.mono ?_
      simp only [List.length_append, List.length_reverse, length_delimit]
      omega

private lemma u_ul17_none (s1_rem acc6 s4 : List Bool) (stks : List (List Bool)) (pc : ℕ)
    (hfetch : fetchBlock s1_rem pc = none) :
    RIn uTM.step (uCfg (some ul17) uInitVar [] s1_rem [] [] s4 (encodeBank stks) acc6
        (List.replicate pc true) [] [])
      (some (haltList uTM [false]))
      (2 * s1_rem.length + s4.length + (encodeBank stks).length + acc6.length + pc + 6) := by
  induction pc generalizing s1_rem acc6 with
  | zero =>
    cases s1_rem with
    | nil => simp [fetchBlock] at hfetch
    | cons hd tl =>
      simp only [fetchBlock, Option.map_eq_none_iff] at hfetch
      have h1 : uTM.step (uCfg (some ul17) uInitVar [] (hd :: tl) [] [] s4 (encodeBank stks) acc6 [] [] []) =
          some (uCfg (some ul18) uInitVar [] (hd :: tl) [] [] s4 (encodeBank stks) acc6 [] [] []) := by
        change some (TM2.stepAux (uProg ul17) uInitVar _) = _
        simp only [uProg, TM2.stepAux, mkUStk, List.head?_cons, List.head?_nil,
          List.tail_nil, Option.isSome, cond_true, cond_false, upd_u7]; rfl
      have h18 := u_ul18_none (hd :: tl) s4 (encodeBank stks) acc6 [] hfetch
      exact ((RIn.single h1).trans h18).mono (by simp; omega)
  | succ pc ih =>
    cases s1_rem with
    | nil => simp [fetchBlock] at hfetch
    | cons hd tl =>
      rcases hund : undelimit (hd :: tl) with _ | ⟨blk0, rest⟩
      · have h1 : uTM.step (uCfg (some ul17) uInitVar [] (hd :: tl) [] [] s4 (encodeBank stks) acc6
              (List.replicate (pc + 1) true) [] []) =
            some (uCfg (some ul19) uInitVar [] (hd :: tl) [] [] s4 (encodeBank stks) acc6
              (List.replicate pc true) [] []) := by
          change some (TM2.stepAux (uProg ul17) uInitVar _) = _
          simp only [uProg, List.replicate_succ, TM2.stepAux, mkUStk, List.head?_cons,
            List.tail_cons, Option.isSome, cond_true, upd_u7]; rfl
        have h19 := u_ul19_none (hd :: tl) s4 (encodeBank stks) acc6 (List.replicate pc true) hund
        refine ((RIn.single h1).trans h19).mono ?_
        simp only [List.length_replicate, List.length_cons] at h19 ⊢
        omega
      · simp only [fetchBlock, hund, Option.bind_some] at hfetch
        have hs1 : hd :: tl = delimit blk0 ++ rest := eq_delimit_append_of_undelimit (hd :: tl) blk0 rest hund
        have h1 : uTM.step (uCfg (some ul17) uInitVar [] (hd :: tl) [] [] s4 (encodeBank stks) acc6
              (List.replicate (pc + 1) true) [] []) =
            some (uCfg (some ul19) uInitVar [] (hd :: tl) [] [] s4 (encodeBank stks) acc6
              (List.replicate pc true) [] []) := by
          change some (TM2.stepAux (uProg ul17) uInitVar _) = _
          simp only [uProg, List.replicate_succ, TM2.stepAux, mkUStk, List.head?_cons,
            List.tail_cons, Option.isSome, cond_true, upd_u7]; rfl
        have h19 := u_ul19_some blk0 rest s4 (encodeBank stks) acc6 (List.replicate pc true)
        rw [← hs1] at h19
        have hih := ih rest ((delimit blk0).reverse ++ acc6) hfetch
        have hc := ((RIn.single h1).trans h19).trans hih
        have hblk0_le : 2 * blk0.length + 1 + rest.length = (hd :: tl).length := by
          rw [hs1, List.length_append, length_delimit]
        refine hc.mono ?_
        simp only [List.length_append, List.length_reverse, length_delimit]
        omega

/- ### Unary decoding & drain helpers for ul23..ul31 -/

private lemma eq_unary_append_of_decodeUnary :
    ∀ (l : List Bool) (n : ℕ) (rest : List Bool),
      decodeUnary l = some (n, rest) → l = unary n ++ rest
  | [], _, _, h => by simp [decodeUnary] at h
  | false :: rest, n, r', h => by
    simp only [decodeUnary, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; rfl
  | true :: tl, n, r', h => by
    simp only [decodeUnary, Option.map_eq_some_iff] at h
    rcases h with ⟨⟨m, r''⟩, hm, heq⟩
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    rw [eq_unary_append_of_decodeUnary tl m r'' hm]
    rfl

private lemma decodeUnary_eq_none_iff :
    ∀ (l : List Bool), decodeUnary l = none ↔ ∀ b ∈ l, b = true
  | [] => by simp [decodeUnary]
  | false :: _ => by simp [decodeUnary]
  | true :: tl => by
    simp only [decodeUnary, Option.map_eq_none_iff, List.mem_cons, forall_eq_or_imp,
      true_and]
    exact decodeUnary_eq_none_iff tl

private lemma u_ul23_some (n : ℕ) (rest s1 s4 s5 : List Bool) (acc : ℕ) :
    RIn uTM.step (uCfg (some ul23) uInitVar (unary n ++ rest) s1 [] [] s4 s5 []
        (List.replicate acc true) [] [])
      (some (uCfg (some ul24) uInitVar rest s1 [] [] s4 s5 [] (List.replicate (n + acc) true) [] []))
      (n + 1) := by
  induction n generalizing acc with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul23) uInitVar _) = _
    simp only [uProg, ul23, unary, List.replicate_zero, List.nil_append, List.singleton_append,
      TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons, Option.isSome, Option.getD,
      cond_true, cond_false, upd_u0, Nat.zero_add]; rfl
  | succ n ih =>
    have h1 : uTM.step (uCfg (some ul23) uInitVar (unary (n + 1) ++ rest) s1 [] [] s4 s5 []
          (List.replicate acc true) [] []) =
        some (uCfg (some ul23) uInitVar (unary n ++ rest) s1 [] [] s4 s5 []
          (List.replicate (acc + 1) true) [] []) := by
      change some (TM2.stepAux (uProg ul23) uInitVar _) = _
      simp only [uProg, ul23, unary, List.replicate_succ, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u0, upd_u7]
      rfl
    have htr := (RIn.single h1).trans (ih (acc + 1))
    have heq : n + (acc + 1) = n + 1 + acc := by omega
    rw [heq] at htr
    exact htr.mono (by omega)

private lemma u_ul23_none (s0 s1 s4 s5 s7 : List Bool) (h : decodeUnary s0 = none) :
    RIn uTM.step (uCfg (some ul23) uInitVar s0 s1 [] [] s4 s5 [] s7 [] [])
      (some (haltList uTM [false]))
      (2 * s0.length + s1.length + s4.length + s5.length + s7.length + 3) := by
  induction s0 generalizing s7 with
  | nil =>
    have h1 : uTM.step (uCfg (some ul23) uInitVar [] s1 [] [] s4 s5 [] s7 [] []) =
        some (uCfg (some ul40) uInitVar [] s1 [] [] s4 s5 [] s7 [] []) := by
      change some (TM2.stepAux (uProg ul23) uInitVar _) = _
      simp only [uProg, ul23, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
        Option.isSome, cond_false, upd_u0]; rfl
    exact ((RIn.single h1).trans (u_abort uInitVar [] s1 [] [] s4 s5 [] s7 [] [])).mono (by simp; omega)
  | cons b s0' ih =>
    cases b with
    | false => simp [decodeUnary] at h
    | true =>
      have hnone : decodeUnary s0' = none := by
        simp only [decodeUnary, Option.map_eq_none_iff] at h; exact h
      have h1 : uTM.step (uCfg (some ul23) uInitVar (true :: s0') s1 [] [] s4 s5 [] s7 [] []) =
          some (uCfg (some ul23) uInitVar s0' s1 [] [] s4 s5 [] (true :: s7) [] []) := by
        change some (TM2.stepAux (uProg ul23) uInitVar _) = _
        simp only [uProg, ul23, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true, upd_u0, upd_u7]; rfl
      exact ((RIn.single h1).trans (ih (true :: s7) hnone)).mono (by simp; omega)

private lemma u_ul24 (s0 s1 s4 s5 s7 : List Bool) :
    RIn uTM.step (uCfg (some ul24) uInitVar s0 s1 [] [] s4 s5 [] s7 [] [])
      (some (uCfg (some ul16) uInitVar [] s1 [] [] s4 s5 [] s7 [] []))
      (s0.length + 1) := by
  induction s0 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul24) uInitVar _) = _
    simp only [uProg, ul24, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u0]; rfl
  | cons c0 s0' ih =>
    have h1 : uTM.step (uCfg (some ul24) uInitVar (c0 :: s0') s1 [] [] s4 s5 [] s7 [] []) =
        some (uCfg (some ul24) uInitVar s0' s1 [] [] s4 s5 [] s7 [] []) := by
      change some (TM2.stepAux (uProg ul24) uInitVar _) = _
      simp only [uProg, ul24, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, cond_true, upd_u0]; rfl
    exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)

private lemma u_ul25_some (v1 v21 : Bool) (n : ℕ) (rest s1 s4 s5 : List Bool) (acc : ℕ) :
    RIn uTM.step (uCfg (some ul25) (v1, v21, none) (unary n ++ rest) s1 [] [] s4 s5 [] []
        (List.replicate acc true) [])
      (some (uCfg (some ul26) (v1, v21, none) rest s1 [] [] s4 s5 [] []
        (List.replicate (n + acc) true) []))
      (n + 1) := by
  induction n generalizing acc with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul25) (v1, v21, none) _) = _
    simp only [uProg, ul25, unary, List.replicate_zero, List.nil_append, List.singleton_append,
      TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons, Option.isSome, Option.getD,
      cond_true, cond_false, upd_u0, Nat.zero_add]; rfl
  | succ n ih =>
    have h1 : uTM.step (uCfg (some ul25) (v1, v21, none) (unary (n + 1) ++ rest) s1 [] [] s4 s5 [] []
          (List.replicate acc true) []) =
        some (uCfg (some ul25) (v1, v21, none) (unary n ++ rest) s1 [] [] s4 s5 [] []
          (List.replicate (acc + 1) true) []) := by
      change some (TM2.stepAux (uProg ul25) (v1, v21, none) _) = _
      simp only [uProg, ul25, unary, List.replicate_succ, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u0, upd_u8]; rfl
    have htr := (RIn.single h1).trans (ih (acc + 1))
    have heq : n + (acc + 1) = n + 1 + acc := by omega
    rw [heq] at htr
    exact htr.mono (by omega)

private lemma u_ul25_none (v1 v21 : Bool) (s0 s1 s4 s5 s8 : List Bool) (h : decodeUnary s0 = none) :
    RIn uTM.step (uCfg (some ul25) (v1, v21, none) s0 s1 [] [] s4 s5 [] [] s8 [])
      (some (haltList uTM [false]))
      (2 * s0.length + s1.length + s4.length + s5.length + s8.length + 3) := by
  induction s0 generalizing s8 with
  | nil =>
    have h1 : uTM.step (uCfg (some ul25) (v1, v21, none) [] s1 [] [] s4 s5 [] [] s8 []) =
        some (uCfg (some ul40) uInitVar [] s1 [] [] s4 s5 [] [] s8 []) := by
      change some (TM2.stepAux (uProg ul25) (v1, v21, none) _) = _
      simp only [uProg, ul25, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
        Option.isSome, cond_false, upd_u0]; rfl
    exact ((RIn.single h1).trans (u_abort uInitVar [] s1 [] [] s4 s5 [] [] s8 [])).mono (by simp; omega)
  | cons b s0' ih =>
    cases b with
    | false => simp [decodeUnary] at h
    | true =>
      have hnone : decodeUnary s0' = none := by
        simp only [decodeUnary, Option.map_eq_none_iff] at h; exact h
      have h1 : uTM.step (uCfg (some ul25) (v1, v21, none) (true :: s0') s1 [] [] s4 s5 [] [] s8 []) =
          some (uCfg (some ul25) (v1, v21, none) s0' s1 [] [] s4 s5 [] [] (true :: s8) []) := by
        change some (TM2.stepAux (uProg ul25) (v1, v21, none) _) = _
        simp only [uProg, ul25, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true, upd_u0, upd_u8]; rfl
      exact ((RIn.single h1).trans (ih (true :: s8) hnone)).mono (by simp; omega)

private lemma u_ul26_some (v1 v21 : Bool) (n : ℕ) (rest s1 s4 s5 s8 : List Bool) (acc : ℕ) :
    RIn uTM.step (uCfg (some ul26) (v1, v21, none) (unary n ++ rest) s1 [] [] s4 s5 []
        (List.replicate acc true) s8 [])
      (some (uCfg (some ul31) (v1, v21, none) rest s1 [] [] s4 s5 []
        (List.replicate (n + acc) true) s8 []))
      (n + 1) := by
  induction n generalizing acc with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul26) (v1, v21, none) _) = _
    simp only [uProg, ul26, unary, List.replicate_zero, List.nil_append, List.singleton_append,
      TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons, Option.isSome, Option.getD,
      cond_true, cond_false, upd_u0, Nat.zero_add]; rfl
  | succ n ih =>
    have h1 : uTM.step (uCfg (some ul26) (v1, v21, none) (unary (n + 1) ++ rest) s1 [] [] s4 s5 []
          (List.replicate acc true) s8 []) =
        some (uCfg (some ul26) (v1, v21, none) (unary n ++ rest) s1 [] [] s4 s5 []
          (List.replicate (acc + 1) true) s8 []) := by
      change some (TM2.stepAux (uProg ul26) (v1, v21, none) _) = _
      simp only [uProg, ul26, unary, List.replicate_succ, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u0, upd_u7]; rfl
    have htr := (RIn.single h1).trans (ih (acc + 1))
    have heq : n + (acc + 1) = n + 1 + acc := by omega
    rw [heq] at htr
    exact htr.mono (by omega)

private lemma u_ul26_none (v1 v21 : Bool) (s0 s1 s4 s5 s7 s8 : List Bool) (h : decodeUnary s0 = none) :
    RIn uTM.step (uCfg (some ul26) (v1, v21, none) s0 s1 [] [] s4 s5 [] s7 s8 [])
      (some (haltList uTM [false]))
      (2 * s0.length + s1.length + s4.length + s5.length + s7.length + s8.length + 3) := by
  induction s0 generalizing s7 with
  | nil =>
    have h1 : uTM.step (uCfg (some ul26) (v1, v21, none) [] s1 [] [] s4 s5 [] s7 s8 []) =
        some (uCfg (some ul40) uInitVar [] s1 [] [] s4 s5 [] s7 s8 []) := by
      change some (TM2.stepAux (uProg ul26) (v1, v21, none) _) = _
      simp only [uProg, ul26, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
        Option.isSome, cond_false, upd_u0]; rfl
    exact ((RIn.single h1).trans (u_abort uInitVar [] s1 [] [] s4 s5 [] s7 s8 [])).mono (by simp; omega)
  | cons b s0' ih =>
    cases b with
    | false => simp [decodeUnary] at h
    | true =>
      have hnone : decodeUnary s0' = none := by
        simp only [decodeUnary, Option.map_eq_none_iff] at h; exact h
      have h1 : uTM.step (uCfg (some ul26) (v1, v21, none) (true :: s0') s1 [] [] s4 s5 [] s7 s8 []) =
          some (uCfg (some ul26) (v1, v21, none) s0' s1 [] [] s4 s5 [] (true :: s7) s8 []) := by
        change some (TM2.stepAux (uProg ul26) (v1, v21, none) _) = _
        simp only [uProg, ul26, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true, upd_u0, upd_u7]; rfl
      exact ((RIn.single h1).trans (ih (true :: s7) hnone)).mono (by simp; omega)

private lemma u_ul27_some (v1 v21 : Bool) (n : ℕ) (rest s1 s4 s5 : List Bool) (acc : ℕ) :
    RIn uTM.step (uCfg (some ul27) (v1, v21, none) (unary n ++ rest) s1 [] [] s4 s5 [] []
        (List.replicate acc true) [])
      (some (uCfg (some ul28) (v1, v21, none) rest s1 [] [] s4 s5 [] []
        (List.replicate (n + acc) true) []))
      (n + 1) := by
  induction n generalizing acc with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul27) (v1, v21, none) _) = _
    simp only [uProg, ul27, unary, List.replicate_zero, List.nil_append, List.singleton_append,
      TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons, Option.isSome, Option.getD,
      cond_true, cond_false, upd_u0, Nat.zero_add]; rfl
  | succ n ih =>
    have h1 : uTM.step (uCfg (some ul27) (v1, v21, none) (unary (n + 1) ++ rest) s1 [] [] s4 s5 [] []
          (List.replicate acc true) []) =
        some (uCfg (some ul27) (v1, v21, none) (unary n ++ rest) s1 [] [] s4 s5 [] []
          (List.replicate (acc + 1) true) []) := by
      change some (TM2.stepAux (uProg ul27) (v1, v21, none) _) = _
      simp only [uProg, ul27, unary, List.replicate_succ, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u0, upd_u8]; rfl
    have htr := (RIn.single h1).trans (ih (acc + 1))
    have heq : n + (acc + 1) = n + 1 + acc := by omega
    rw [heq] at htr
    exact htr.mono (by omega)

private lemma u_ul27_none (v1 v21 : Bool) (s0 s1 s4 s5 s8 : List Bool) (h : decodeUnary s0 = none) :
    RIn uTM.step (uCfg (some ul27) (v1, v21, none) s0 s1 [] [] s4 s5 [] [] s8 [])
      (some (haltList uTM [false]))
      (2 * s0.length + s1.length + s4.length + s5.length + s8.length + 3) := by
  induction s0 generalizing s8 with
  | nil =>
    have h1 : uTM.step (uCfg (some ul27) (v1, v21, none) [] s1 [] [] s4 s5 [] [] s8 []) =
        some (uCfg (some ul40) uInitVar [] s1 [] [] s4 s5 [] [] s8 []) := by
      change some (TM2.stepAux (uProg ul27) (v1, v21, none) _) = _
      simp only [uProg, ul27, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
        Option.isSome, cond_false, upd_u0]; rfl
    exact ((RIn.single h1).trans (u_abort uInitVar [] s1 [] [] s4 s5 [] [] s8 [])).mono (by simp; omega)
  | cons b s0' ih =>
    cases b with
    | false => simp [decodeUnary] at h
    | true =>
      have hnone : decodeUnary s0' = none := by
        simp only [decodeUnary, Option.map_eq_none_iff] at h; exact h
      have h1 : uTM.step (uCfg (some ul27) (v1, v21, none) (true :: s0') s1 [] [] s4 s5 [] [] s8 []) =
          some (uCfg (some ul27) (v1, v21, none) s0' s1 [] [] s4 s5 [] [] (true :: s8) []) := by
        change some (TM2.stepAux (uProg ul27) (v1, v21, none) _) = _
        simp only [uProg, ul27, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true, upd_u0, upd_u8]; rfl
      exact ((RIn.single h1).trans (ih (true :: s8) hnone)).mono (by simp; omega)

private lemma u_ul28_some (v1 v21 : Bool) (n : ℕ) (rest s1 s4 s5 s8 : List Bool) (acc : ℕ) :
    RIn uTM.step (uCfg (some ul28) (v1, v21, none) (unary n ++ rest) s1
        (List.replicate acc true) [] s4 s5 [] [] s8 [])
      (some (uCfg (some ul29) (v1, v21, none) rest s1
        (List.replicate (n + acc) true) [] s4 s5 [] [] s8 []))
      (n + 1) := by
  induction n generalizing acc with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul28) (v1, v21, none) _) = _
    simp only [uProg, ul28, unary, List.replicate_zero, List.nil_append, List.singleton_append,
      TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons, Option.isSome, Option.getD,
      cond_true, cond_false, upd_u0, Nat.zero_add]; rfl
  | succ n ih =>
    have h1 : uTM.step (uCfg (some ul28) (v1, v21, none) (unary (n + 1) ++ rest) s1
          (List.replicate acc true) [] s4 s5 [] [] s8 []) =
        some (uCfg (some ul28) (v1, v21, none) (unary n ++ rest) s1
          (List.replicate (acc + 1) true) [] s4 s5 [] [] s8 []) := by
      change some (TM2.stepAux (uProg ul28) (v1, v21, none) _) = _
      simp only [uProg, ul28, unary, List.replicate_succ, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u0, upd_u2]; rfl
    have htr := (RIn.single h1).trans (ih (acc + 1))
    have heq : n + (acc + 1) = n + 1 + acc := by omega
    rw [heq] at htr
    exact htr.mono (by omega)

private lemma u_ul28_none (v1 v21 : Bool) (s0 s1 s2 s4 s5 s8 : List Bool) (h : decodeUnary s0 = none) :
    RIn uTM.step (uCfg (some ul28) (v1, v21, none) s0 s1 s2 [] s4 s5 [] [] s8 [])
      (some (haltList uTM [false]))
      (2 * s0.length + s1.length + s2.length + s4.length + s5.length + s8.length + 3) := by
  induction s0 generalizing s2 with
  | nil =>
    have h1 : uTM.step (uCfg (some ul28) (v1, v21, none) [] s1 s2 [] s4 s5 [] [] s8 []) =
        some (uCfg (some ul40) uInitVar [] s1 s2 [] s4 s5 [] [] s8 []) := by
      change some (TM2.stepAux (uProg ul28) (v1, v21, none) _) = _
      simp only [uProg, ul28, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
        Option.isSome, cond_false, upd_u0]; rfl
    exact ((RIn.single h1).trans (u_abort uInitVar [] s1 s2 [] s4 s5 [] [] s8 [])).mono (by simp; omega)
  | cons b s0' ih =>
    cases b with
    | false => simp [decodeUnary] at h
    | true =>
      have hnone : decodeUnary s0' = none := by
        simp only [decodeUnary, Option.map_eq_none_iff] at h; exact h
      have h1 : uTM.step (uCfg (some ul28) (v1, v21, none) (true :: s0') s1 s2 [] s4 s5 [] [] s8 []) =
          some (uCfg (some ul28) (v1, v21, none) s0' s1 (true :: s2) [] s4 s5 [] [] s8 []) := by
        change some (TM2.stepAux (uProg ul28) (v1, v21, none) _) = _
        simp only [uProg, ul28, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true, upd_u0, upd_u2]; rfl
      exact ((RIn.single h1).trans (ih (true :: s2) hnone)).mono (by simp; omega)

private lemma u_ul29_some (v1 v21 : Bool) (n : ℕ) (rest s1 s2 s4 s5 s8 : List Bool) (acc : ℕ) :
    RIn uTM.step (uCfg (some ul29) (v1, v21, none) (unary n ++ rest) s1 s2
        (List.replicate acc true) s4 s5 [] [] s8 [])
      (some (uCfg (some ul30) (v1, v21, none) rest s1 s2
        (List.replicate (n + acc) true) s4 s5 [] [] s8 []))
      (n + 1) := by
  induction n generalizing acc with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul29) (v1, v21, none) _) = _
    simp only [uProg, ul29, unary, List.replicate_zero, List.nil_append, List.singleton_append,
      TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons, Option.isSome, Option.getD,
      cond_true, cond_false, upd_u0, Nat.zero_add]; rfl
  | succ n ih =>
    have h1 : uTM.step (uCfg (some ul29) (v1, v21, none) (unary (n + 1) ++ rest) s1 s2
          (List.replicate acc true) s4 s5 [] [] s8 []) =
        some (uCfg (some ul29) (v1, v21, none) (unary n ++ rest) s1 s2
          (List.replicate (acc + 1) true) s4 s5 [] [] s8 []) := by
      change some (TM2.stepAux (uProg ul29) (v1, v21, none) _) = _
      simp only [uProg, ul29, unary, List.replicate_succ, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u0, upd_u3]; rfl
    have htr := (RIn.single h1).trans (ih (acc + 1))
    have heq : n + (acc + 1) = n + 1 + acc := by omega
    rw [heq] at htr
    exact htr.mono (by omega)

private lemma u_ul29_none (v1 v21 : Bool) (s0 s1 s2 s3 s4 s5 s8 : List Bool) (h : decodeUnary s0 = none) :
    RIn uTM.step (uCfg (some ul29) (v1, v21, none) s0 s1 s2 s3 s4 s5 [] [] s8 [])
      (some (haltList uTM [false]))
      (2 * s0.length + s1.length + s2.length + s3.length + s4.length + s5.length + s8.length + 3) := by
  induction s0 generalizing s3 with
  | nil =>
    have h1 : uTM.step (uCfg (some ul29) (v1, v21, none) [] s1 s2 s3 s4 s5 [] [] s8 []) =
        some (uCfg (some ul40) uInitVar [] s1 s2 s3 s4 s5 [] [] s8 []) := by
      change some (TM2.stepAux (uProg ul29) (v1, v21, none) _) = _
      simp only [uProg, ul29, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
        Option.isSome, cond_false, upd_u0]; rfl
    exact ((RIn.single h1).trans (u_abort uInitVar [] s1 s2 s3 s4 s5 [] [] s8 [])).mono (by simp; omega)
  | cons b s0' ih =>
    cases b with
    | false => simp [decodeUnary] at h
    | true =>
      have hnone : decodeUnary s0' = none := by
        simp only [decodeUnary, Option.map_eq_none_iff] at h; exact h
      have h1 : uTM.step (uCfg (some ul29) (v1, v21, none) (true :: s0') s1 s2 s3 s4 s5 [] [] s8 []) =
          some (uCfg (some ul29) (v1, v21, none) s0' s1 s2 (true :: s3) s4 s5 [] [] s8 []) := by
        change some (TM2.stepAux (uProg ul29) (v1, v21, none) _) = _
        simp only [uProg, ul29, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true, upd_u0, upd_u3]; rfl
      exact ((RIn.single h1).trans (ih (true :: s3) hnone)).mono (by simp; omega)

private lemma u_ul30_some (v1 v21 : Bool) (n : ℕ) (rest s1 s2 s3 s4 s5 s8 : List Bool) (acc : ℕ) :
    RIn uTM.step (uCfg (some ul30) (v1, v21, none) (unary n ++ rest) s1 s2 s3 s4 s5 [] [] s8
        (List.replicate acc true))
      (some (uCfg (some ul31) (v1, v21, none) rest s1 s2 s3 s4 s5 [] [] s8
        (List.replicate (n + acc) true)))
      (n + 1) := by
  induction n generalizing acc with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul30) (v1, v21, none) _) = _
    simp only [uProg, ul30, unary, List.replicate_zero, List.nil_append, List.singleton_append,
      TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons, Option.isSome, Option.getD,
      cond_true, cond_false, upd_u0, Nat.zero_add]; rfl
  | succ n ih =>
    have h1 : uTM.step (uCfg (some ul30) (v1, v21, none) (unary (n + 1) ++ rest) s1 s2 s3 s4 s5
          [] [] s8 (List.replicate acc true)) =
        some (uCfg (some ul30) (v1, v21, none) (unary n ++ rest) s1 s2 s3 s4 s5 [] [] s8
          (List.replicate (acc + 1) true)) := by
      change some (TM2.stepAux (uProg ul30) (v1, v21, none) _) = _
      simp only [uProg, ul30, unary, List.replicate_succ, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u0, upd_u9]; rfl
    have htr := (RIn.single h1).trans (ih (acc + 1))
    have heq : n + (acc + 1) = n + 1 + acc := by omega
    rw [heq] at htr
    exact htr.mono (by omega)

private lemma u_ul30_none (v1 v21 : Bool) (s0 s1 s2 s3 s4 s5 s8 s9 : List Bool) (h : decodeUnary s0 = none) :
    RIn uTM.step (uCfg (some ul30) (v1, v21, none) s0 s1 s2 s3 s4 s5 [] [] s8 s9)
      (some (haltList uTM [false]))
      (2 * s0.length + s1.length + s2.length + s3.length + s4.length + s5.length + s8.length + s9.length + 3) := by
  induction s0 generalizing s9 with
  | nil =>
    have h1 : uTM.step (uCfg (some ul30) (v1, v21, none) [] s1 s2 s3 s4 s5 [] [] s8 s9) =
        some (uCfg (some ul40) uInitVar [] s1 s2 s3 s4 s5 [] [] s8 s9) := by
      change some (TM2.stepAux (uProg ul30) (v1, v21, none) _) = _
      simp only [uProg, ul30, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
        Option.isSome, cond_false, upd_u0]; rfl
    exact ((RIn.single h1).trans (u_abort uInitVar [] s1 s2 s3 s4 s5 [] [] s8 s9)).mono (by simp; omega)
  | cons b s0' ih =>
    cases b with
    | false => simp [decodeUnary] at h
    | true =>
      have hnone : decodeUnary s0' = none := by
        simp only [decodeUnary, Option.map_eq_none_iff] at h; exact h
      have h1 : uTM.step (uCfg (some ul30) (v1, v21, none) (true :: s0') s1 s2 s3 s4 s5 [] [] s8 s9) =
          some (uCfg (some ul30) (v1, v21, none) s0' s1 s2 s3 s4 s5 [] [] s8 (true :: s9)) := by
        change some (TM2.stepAux (uProg ul30) (v1, v21, none) _) = _
        simp only [uProg, ul30, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
          Option.isSome, Option.getD, cond_true, upd_u0, upd_u9]; rfl
      exact ((RIn.single h1).trans (ih (true :: s9) hnone)).mono (by simp; omega)

private lemma u_ul31 (v1 v21 : Bool) (s0 s1 s2 s3 s4 s5 s7 s8 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul31) (v1, v21, none) s0 s1 s2 s3 s4 s5 [] s7 s8 s9)
      (some (uCfg (some ul34) (v1, v21, none) [] s1 s2 s3 s4 s5 [] s7 s8 s9))
      (s0.length + 1) := by
  induction s0 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul31) (v1, v21, none) _) = _
    simp only [uProg, ul31, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u0]; rfl
  | cons c0 s0' ih =>
    have h1 : uTM.step (uCfg (some ul31) (v1, v21, none) (c0 :: s0') s1 s2 s3 s4 s5 [] s7 s8 s9) =
        some (uCfg (some ul31) (v1, v21, none) s0' s1 s2 s3 s4 s5 [] s7 s8 s9) := by
      change some (TM2.stepAux (uProg ul31) (v1, v21, none) _) = _
      simp only [uProg, ul31, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, cond_true, upd_u0]; rfl
    exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)

/- ### Bank skip/restore & target-branch selection lemmas (ul34..ul39) -/

private lemma u_ul35_skip (v1 v21 : Bool) (s1 s2 s3 s4 s' rest5 acc6 s7 s8 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul35) (v1, v21, none) [] s1 s2 s3 s4 (delimit s' ++ rest5) acc6 s7 s8 s9)
      (some (uCfg (some ul34) (v1, v21, none) [] s1 s2 s3 s4 rest5 ((delimit s').reverse ++ acc6) s7 s8 s9))
      (s'.length + 1) := by
  induction s' generalizing acc6 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul35) (v1, v21, none) _) = _
    simp only [uProg, ul35, delimit, List.singleton_append, TM2.stepAux, mkUStk,
      List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true, cond_false,
      upd_u5, upd_u6, List.reverse_cons, List.reverse_nil, List.nil_append]; rfl
  | cons b bs ih =>
    have h1 : uTM.step (uCfg (some ul35) (v1, v21, none) [] s1 s2 s3 s4
          (delimit (b :: bs) ++ rest5) acc6 s7 s8 s9) =
        some (uCfg (some ul35) (v1, v21, none) [] s1 s2 s3 s4
          (delimit bs ++ rest5) (b :: true :: acc6) s7 s8 s9) := by
      change some (TM2.stepAux (uProg ul35) (v1, v21, none) _) = _
      simp only [uProg, ul35, delimit, List.cons_append, TM2.stepAux, mkUStk,
        List.head?_cons, List.tail_cons, Option.isSome, Option.getD, cond_true,
        upd_u5, upd_u6]; rfl
    have htr := (RIn.single h1).trans (ih (b :: true :: acc6))
    simp only [delimit, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul34_loop (v1 v21 : Bool) (s1 s2 s3 s4 s7 s9 : List Bool)
    (k : ℕ) (stks_rem : List (List Bool)) (acc6 : List Bool) :
    RIn uTM.step (uCfg (some ul34) (v1, v21, none) [] s1 s2 s3 s4
        (encodeBank stks_rem) acc6 s7 (List.replicate k true) s9)
      (some (uCfg (some ul34) (v1, v21, none) [] s1 s2 s3 s4
        (encodeBank (dropStks stks_rem k)) (skipAcc stks_rem k acc6) s7 [] s9))
      ((encodeBank stks_rem).length + k) := by
  induction k generalizing stks_rem acc6 with
  | zero =>
    rw [dropStks, skipAcc]
    exact (RIn.refl uTM.step _).mono (by omega)
  | succ k ih =>
    cases stks_rem with
    | nil =>
      have h1 : uTM.step (uCfg (some ul34) (v1, v21, none) [] s1 s2 s3 s4
            [] acc6 s7 (List.replicate (k + 1) true) s9) =
          some (uCfg (some ul34) (v1, v21, none) [] s1 s2 s3 s4
            [] (false :: acc6) s7 (List.replicate k true) s9) := by
        change some (TM2.stepAux (uProg ul34) (v1, v21, none) _) = _
        simp only [uProg, ul34, List.replicate_succ, TM2.stepAux, mkUStk, List.head?_cons,
          List.head?_nil, List.tail_cons, List.tail_nil, Option.isSome, cond_true, cond_false,
          upd_u8, upd_u5, upd_u6]; rfl
      have htr := (RIn.single h1).trans (ih [] (false :: acc6))
      rw [dropStks_nil] at htr
      rw [dropStks, skipAcc]
      refine htr.mono ?_
      have henc0 : (encodeBank []).length = 0 := rfl
      rw [henc0]; omega
    | cons s ss =>
      cases s with
      | nil =>
        have h1 : uTM.step (uCfg (some ul34) (v1, v21, none) [] s1 s2 s3 s4
              (false :: encodeBank ss) acc6 s7 (List.replicate (k + 1) true) s9) =
            some (uCfg (some ul34) (v1, v21, none) [] s1 s2 s3 s4
              (encodeBank ss) (false :: acc6) s7 (List.replicate k true) s9) := by
          change some (TM2.stepAux (uProg ul34) (v1, v21, none) _) = _
          simp only [uProg, ul34, List.replicate_succ, TM2.stepAux, mkUStk, List.head?_cons,
            List.tail_cons, Option.isSome, Option.getD, cond_true, cond_false,
            upd_u8, upd_u5, upd_u6]; rfl
        have htr := (RIn.single h1).trans (ih ss (false :: acc6))
        have hbank : encodeBank ([] :: ss) = false :: encodeBank ss := by simp [encodeBank, delimit]
        rw [hbank, dropStks, skipAcc]
        refine htr.mono ?_
        simp only [List.length_cons]
        omega
      | cons b s' =>
        have h1 : uTM.step (uCfg (some ul34) (v1, v21, none) [] s1 s2 s3 s4
              (true :: b :: delimit s' ++ encodeBank ss) acc6 s7 (List.replicate (k + 1) true) s9) =
            some (uCfg (some ul35) (v1, v21, none) [] s1 s2 s3 s4
              (delimit s' ++ encodeBank ss) (b :: true :: acc6) s7 (List.replicate k true) s9) := by
          change some (TM2.stepAux (uProg ul34) (v1, v21, none) _) = _
          simp only [uProg, ul34, List.replicate_succ, TM2.stepAux, mkUStk, List.head?_cons,
            List.tail_cons, Option.isSome, Option.getD, cond_true, upd_u8, upd_u5, upd_u6]; rfl
        have h35 := u_ul35_skip v1 v21 s1 s2 s3 s4 s' (encodeBank ss) (b :: true :: acc6)
          s7 (List.replicate k true) s9
        have hih := ih ss ((delimit s').reverse ++ b :: true :: acc6)
        have hc := ((RIn.single h1).trans h35).trans hih
        have hbank : encodeBank ((b :: s') :: ss) = true :: b :: delimit s' ++ encodeBank ss := by
          simp [encodeBank, delimit]
        rw [hbank, dropStks, skipAcc]
        have hrev : (delimit s').reverse ++ b :: true :: acc6 = (delimit (b :: s')).reverse ++ acc6 := by
          simp [delimit, List.reverse_cons, List.append_assoc]
        rw [hrev] at hc
        refine hc.mono ?_
        simp only [List.length_cons, List.length_append, length_delimit]
        omega

private lemma u_ul36 (s1 s4 s5 s6 s7 : List Bool) :
    RIn uTM.step (uCfg (some ul36) uInitVar [] s1 [] [] s4 s5 s6 s7 [] [])
      (some (uCfg (some ul16) uInitVar [] s1 [] [] s4 (s6.reverse ++ s5) [] s7 [] []))
      (s6.length + 1) := by
  induction s6 generalizing s5 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (uProg ul36) uInitVar _) = _
    simp only [uProg, ul36, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
      Option.isSome, cond_false, upd_u6]; rfl
  | cons b xs ih =>
    have h1 : uTM.step (uCfg (some ul36) uInitVar [] s1 [] [] s4 s5 (b :: xs) s7 [] []) =
        some (uCfg (some ul36) uInitVar [] s1 [] [] s4 (b :: s5) xs s7 [] []) := by
      change some (TM2.stepAux (uProg ul36) uInitVar _) = _
      simp only [uProg, ul36, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u6, upd_u5]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s5))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma u_ul37 (s1 s2 s3 s4 s5 s6 s7 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul37) uInitVar [] s1 s2 s3 s4 s5 s6 s7 [] s9)
      (some (uCfg (some ul36) uInitVar [] s1 [] [] s4 s5 s6 (s2.reverse ++ s7) [] []))
      (s2.length + s3.length + s9.length + 1) := by
  induction s2 generalizing s7 with
  | cons b s2' ih =>
    have h1 : uTM.step (uCfg (some ul37) uInitVar [] s1 (b :: s2') s3 s4 s5 s6 s7 [] s9) =
        some (uCfg (some ul37) uInitVar [] s1 s2' s3 s4 s5 s6 (b :: s7) [] s9) := by
      change some (TM2.stepAux (uProg ul37) uInitVar _) = _
      simp only [uProg, ul37, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u2, upd_u7]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s7))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)
  | nil =>
    induction s3 with
    | cons c3 s3' ih =>
      have h1 : uTM.step (uCfg (some ul37) uInitVar [] s1 [] (c3 :: s3') s4 s5 s6 s7 [] s9) =
          some (uCfg (some ul37) uInitVar [] s1 [] s3' s4 s5 s6 s7 [] s9) := by
        change some (TM2.stepAux (uProg ul37) uInitVar _) = _
        simp only [uProg, ul37, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
          List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true, upd_u2, upd_u3]; rfl
      exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)
    | nil =>
      induction s9 with
      | cons c9 s9' ih =>
        have h1 : uTM.step (uCfg (some ul37) uInitVar [] s1 [] [] s4 s5 s6 s7 [] (c9 :: s9')) =
            some (uCfg (some ul37) uInitVar [] s1 [] [] s4 s5 s6 s7 [] s9') := by
          change some (TM2.stepAux (uProg ul37) uInitVar _) = _
          simp only [uProg, ul37, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
            List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true,
            upd_u2, upd_u3, upd_u9]; rfl
        exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)
      | nil =>
        refine RIn.single ?_
        change some (TM2.stepAux (uProg ul37) uInitVar _) = _
        simp only [uProg, ul37, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
          Option.isSome, cond_false, upd_u2, upd_u3, upd_u9, List.reverse_nil, List.nil_append]; rfl

private lemma u_ul38 (s1 s2 s3 s4 s5 s6 s7 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul38) uInitVar [] s1 s2 s3 s4 s5 s6 s7 [] s9)
      (some (uCfg (some ul36) uInitVar [] s1 [] [] s4 s5 s6 (s3.reverse ++ s7) [] []))
      (s2.length + s3.length + s9.length + 1) := by
  induction s3 generalizing s7 with
  | cons b s3' ih =>
    have h1 : uTM.step (uCfg (some ul38) uInitVar [] s1 s2 (b :: s3') s4 s5 s6 s7 [] s9) =
        some (uCfg (some ul38) uInitVar [] s1 s2 s3' s4 s5 s6 (b :: s7) [] s9) := by
      change some (TM2.stepAux (uProg ul38) uInitVar _) = _
      simp only [uProg, ul38, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u3, upd_u7]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s7))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)
  | nil =>
    induction s2 with
    | cons c2 s2' ih =>
      have h1 : uTM.step (uCfg (some ul38) uInitVar [] s1 (c2 :: s2') [] s4 s5 s6 s7 [] s9) =
          some (uCfg (some ul38) uInitVar [] s1 s2' [] s4 s5 s6 s7 [] s9) := by
        change some (TM2.stepAux (uProg ul38) uInitVar _) = _
        simp only [uProg, ul38, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
          List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true, upd_u3, upd_u2]; rfl
      exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)
    | nil =>
      induction s9 with
      | cons c9 s9' ih =>
        have h1 : uTM.step (uCfg (some ul38) uInitVar [] s1 [] [] s4 s5 s6 s7 [] (c9 :: s9')) =
            some (uCfg (some ul38) uInitVar [] s1 [] [] s4 s5 s6 s7 [] s9') := by
          change some (TM2.stepAux (uProg ul38) uInitVar _) = _
          simp only [uProg, ul38, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
            List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true,
            upd_u3, upd_u2, upd_u9]; rfl
        exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)
      | nil =>
        refine RIn.single ?_
        change some (TM2.stepAux (uProg ul38) uInitVar _) = _
        simp only [uProg, ul38, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
          Option.isSome, cond_false, upd_u3, upd_u2, upd_u9, List.reverse_nil, List.nil_append]; rfl

private lemma u_ul39 (s1 s2 s3 s4 s5 s6 s7 s9 : List Bool) :
    RIn uTM.step (uCfg (some ul39) uInitVar [] s1 s2 s3 s4 s5 s6 s7 [] s9)
      (some (uCfg (some ul36) uInitVar [] s1 [] [] s4 s5 s6 (s9.reverse ++ s7) [] []))
      (s2.length + s3.length + s9.length + 1) := by
  induction s9 generalizing s7 with
  | cons b s9' ih =>
    have h1 : uTM.step (uCfg (some ul39) uInitVar [] s1 s2 s3 s4 s5 s6 s7 [] (b :: s9')) =
        some (uCfg (some ul39) uInitVar [] s1 s2 s3 s4 s5 s6 (b :: s7) [] s9') := by
      change some (TM2.stepAux (uProg ul39) uInitVar _) = _
      simp only [uProg, ul39, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, Option.getD, cond_true, upd_u9, upd_u7]; rfl
    have htr := (RIn.single h1).trans (ih (b :: s7))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact htr.mono (by simp only [List.length_cons]; omega)
  | nil =>
    induction s2 with
    | cons c2 s2' ih =>
      have h1 : uTM.step (uCfg (some ul39) uInitVar [] s1 (c2 :: s2') s3 s4 s5 s6 s7 [] []) =
          some (uCfg (some ul39) uInitVar [] s1 s2' s3 s4 s5 s6 s7 [] []) := by
        change some (TM2.stepAux (uProg ul39) uInitVar _) = _
        simp only [uProg, ul39, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
          List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true, upd_u9, upd_u2]; rfl
      exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)
    | nil =>
      induction s3 with
      | cons c3 s3' ih =>
        have h1 : uTM.step (uCfg (some ul39) uInitVar [] s1 [] (c3 :: s3') s4 s5 s6 s7 [] []) =
            some (uCfg (some ul39) uInitVar [] s1 [] s3' s4 s5 s6 s7 [] []) := by
          change some (TM2.stepAux (uProg ul39) uInitVar _) = _
          simp only [uProg, ul39, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
            List.tail_nil, List.tail_cons, Option.isSome, cond_false, cond_true,
            upd_u9, upd_u2, upd_u3]; rfl
        exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)
      | nil =>
        refine RIn.single ?_
        change some (TM2.stepAux (uProg ul39) uInitVar _) = _
        simp only [uProg, ul39, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
          Option.isSome, cond_false, upd_u9, upd_u2, upd_u3, List.reverse_nil, List.nil_append]; rfl

private lemma u_ul34_push (b : Bool) (s1 s4 s7 : List Bool) (stks : List (List Bool)) (k : ℕ) :
    RIn uTM.step (uCfg (some ul34) (false, b, none) [] s1 [] [] s4
        (encodeBank stks) [] s7 (List.replicate k true) [])
      (some (uCfg (some ul16) uInitVar [] s1 [] [] s4 (encodeBank (pushStk stks k b)) [] s7 [] []))
      (2 * (encodeBank stks).length + 2 * k + 3) := by
  have hloop := u_ul34_loop false b s1 [] [] s4 s7 [] k stks []
  have hlen := skipAcc_len_bound stks k []
  rw [List.length_nil, Nat.zero_add] at hlen
  have hstep : uTM.step (uCfg (some ul34) (false, b, none) [] s1 [] [] s4
        (encodeBank (dropStks stks k)) (skipAcc stks k []) s7 [] []) =
      some (uCfg (some ul36) uInitVar [] s1 [] [] s4
        (encodeBank (pushStk (dropStks stks k) 0 b)) (skipAcc stks k []) s7 [] []) := by
    cases hd : dropStks stks k with
    | nil =>
      change some (TM2.stepAux (uProg ul34) (false, b, none) _) = _
      simp only [uProg, ul34, encodeBank, List.map_nil, List.flatten_nil, pushStk,
        TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil, Option.isSome, cond_false, upd_u8, upd_u5]; rfl
    | cons s0 ss =>
      have hne : encodeBank (s0 :: ss) ≠ [] := by cases s0 <;> simp [encodeBank, delimit]
      obtain ⟨hd0, tl0, hhd⟩ := List.exists_cons_of_ne_nil hne
      change some (TM2.stepAux (uProg ul34) (false, b, none) _) = _
      simp only [uProg, ul34, pushStk]
      have hbk : encodeBank ((b :: s0) :: ss) = true :: b :: encodeBank (s0 :: ss) := by
        simp [encodeBank, delimit]
      rw [hbk, hhd]
      simp only [TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons, List.tail_nil,
        Option.isSome, cond_false, cond_true, upd_u8, upd_u5]; rfl
  have hrest := u_ul36 s1 s4 (encodeBank (pushStk (dropStks stks k) 0 b)) (skipAcc stks k []) s7
  rw [skipAcc_restore_push, List.reverse_nil, List.nil_append] at hrest
  exact ((hloop.trans (RIn.single hstep)).trans hrest).mono (by omega)

private lemma u_ul34_pop (s1 s4 : List Bool) (stks : List (List Bool)) (k onE onF onT : ℕ) :
    let res := popStk stks k
    let nextPc := match res.1 with | none => onE | some false => onF | some true => onT
    RIn uTM.step (uCfg (some ul34) (true, false, none) [] s1
        (List.replicate onE true) (List.replicate onF true) s4
        (encodeBank stks) [] [] (List.replicate k true) (List.replicate onT true))
      (some (uCfg (some ul16) uInitVar [] s1 [] [] s4
        (encodeBank res.2) [] (List.replicate nextPc true) [] []))
      (2 * (encodeBank stks).length + 2 * k + onE + onF + onT + 4) := by
  have hloop := u_ul34_loop true false s1 (List.replicate onE true) (List.replicate onF true) s4
    [] (List.replicate onT true) k stks []
  have hlen := skipAcc_len_bound stks k []
  rw [List.length_nil, Nat.zero_add] at hlen
  have hfst : (popStk (dropStks stks k) 0).1 = (popStk stks k).1 := popStk_dropStks_fst stks k
  cases hdrop : dropStks stks k with
  | nil =>
    have hres_none : (popStk stks k).1 = none := by rw [← hfst, hdrop]; rfl
    have hstep : uTM.step (uCfg (some ul34) (true, false, none) [] s1
          (List.replicate onE true) (List.replicate onF true) s4
          (encodeBank (dropStks stks k)) (skipAcc stks k []) [] [] (List.replicate onT true)) =
        some (uCfg (some ul37) uInitVar [] s1
          (List.replicate onE true) (List.replicate onF true) s4
          (encodeBank (popStk (dropStks stks k) 0).2) (skipAcc stks k []) [] []
          (List.replicate onT true)) := by
      rw [hdrop]
      change some (TM2.stepAux (uProg ul34) (true, false, none) _) = _
      simp only [uProg, ul34, encodeBank, List.map_nil, List.flatten_nil, popStk,
        TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil, Option.isSome, cond_true, cond_false,
        upd_u8, upd_u5]; rfl
    have h37 := u_ul37 s1 (List.replicate onE true) (List.replicate onF true) s4
      (encodeBank (popStk (dropStks stks k) 0).2) (skipAcc stks k []) [] (List.replicate onT true)
    rw [List.reverse_replicate, List.append_nil] at h37
    have h36 := u_ul36 s1 s4 (encodeBank (popStk (dropStks stks k) 0).2) (skipAcc stks k [])
      (List.replicate onE true)
    rw [skipAcc_restore_pop, List.reverse_nil, List.nil_append] at h36
    simp only [hres_none]
    refine (((hloop.trans (RIn.single hstep)).trans h37).trans h36).mono ?_
    simp only [List.length_replicate]; omega
  | cons s0 ss =>
    cases s0 with
    | nil =>
      have hres_none : (popStk stks k).1 = none := by rw [← hfst, hdrop]; rfl
      have hstep : uTM.step (uCfg (some ul34) (true, false, none) [] s1
            (List.replicate onE true) (List.replicate onF true) s4
            (encodeBank (dropStks stks k)) (skipAcc stks k []) [] [] (List.replicate onT true)) =
          some (uCfg (some ul37) uInitVar [] s1
            (List.replicate onE true) (List.replicate onF true) s4
            (encodeBank (popStk (dropStks stks k) 0).2) (skipAcc stks k []) [] []
            (List.replicate onT true)) := by
        rw [hdrop]
        change some (TM2.stepAux (uProg ul34) (true, false, none) _) = _
        simp only [uProg, ul34, encodeBank, List.map_cons, List.flatten_cons, delimit,
          List.singleton_append, popStk, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
          List.tail_nil, List.tail_cons, Option.isSome, Option.getD, cond_true, cond_false,
          upd_u8, upd_u5]; rfl
      have h37 := u_ul37 s1 (List.replicate onE true) (List.replicate onF true) s4
        (encodeBank (popStk (dropStks stks k) 0).2) (skipAcc stks k []) [] (List.replicate onT true)
      rw [List.reverse_replicate, List.append_nil] at h37
      have h36 := u_ul36 s1 s4 (encodeBank (popStk (dropStks stks k) 0).2) (skipAcc stks k [])
        (List.replicate onE true)
      rw [skipAcc_restore_pop, List.reverse_nil, List.nil_append] at h36
      simp only [hres_none]
      refine (((hloop.trans (RIn.single hstep)).trans h37).trans h36).mono ?_
      simp only [List.length_replicate]; omega
    | cons b s0' =>
      have hres_some : (popStk stks k).1 = some b := by rw [← hfst, hdrop]; rfl
      cases b with
      | false =>
        have hstep : uTM.step (uCfg (some ul34) (true, false, none) [] s1
              (List.replicate onE true) (List.replicate onF true) s4
              (encodeBank (dropStks stks k)) (skipAcc stks k []) [] [] (List.replicate onT true)) =
            some (uCfg (some ul38) uInitVar [] s1
              (List.replicate onE true) (List.replicate onF true) s4
              (encodeBank (popStk (dropStks stks k) 0).2) (skipAcc stks k []) [] []
              (List.replicate onT true)) := by
          rw [hdrop]
          change some (TM2.stepAux (uProg ul34) (true, false, none) _) = _
          simp only [uProg, ul34, encodeBank, List.map_cons, List.flatten_cons, delimit,
            List.cons_append, popStk, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
            List.tail_nil, List.tail_cons, Option.isSome, Option.getD, cond_true, cond_false,
            upd_u8, upd_u5]; rfl
        have h38 := u_ul38 s1 (List.replicate onE true) (List.replicate onF true) s4
          (encodeBank (popStk (dropStks stks k) 0).2) (skipAcc stks k []) [] (List.replicate onT true)
        rw [List.reverse_replicate, List.append_nil] at h38
        have h36 := u_ul36 s1 s4 (encodeBank (popStk (dropStks stks k) 0).2) (skipAcc stks k [])
          (List.replicate onF true)
        rw [skipAcc_restore_pop, List.reverse_nil, List.nil_append] at h36
        simp only [hres_some]
        refine (((hloop.trans (RIn.single hstep)).trans h38).trans h36).mono ?_
        simp only [List.length_replicate]; omega
      | true =>
        have hstep : uTM.step (uCfg (some ul34) (true, false, none) [] s1
              (List.replicate onE true) (List.replicate onF true) s4
              (encodeBank (dropStks stks k)) (skipAcc stks k []) [] [] (List.replicate onT true)) =
            some (uCfg (some ul39) uInitVar [] s1
              (List.replicate onE true) (List.replicate onF true) s4
              (encodeBank (popStk (dropStks stks k) 0).2) (skipAcc stks k []) [] []
              (List.replicate onT true)) := by
          rw [hdrop]
          change some (TM2.stepAux (uProg ul34) (true, false, none) _) = _
          simp only [uProg, ul34, encodeBank, List.map_cons, List.flatten_cons, delimit,
            List.cons_append, popStk, TM2.stepAux, mkUStk, List.head?_nil, List.head?_cons,
            List.tail_nil, List.tail_cons, Option.isSome, Option.getD, cond_true, cond_false,
            upd_u8, upd_u5]; rfl
        have h39 := u_ul39 s1 (List.replicate onE true) (List.replicate onF true) s4
          (encodeBank (popStk (dropStks stks k) 0).2) (skipAcc stks k []) [] (List.replicate onT true)
        rw [List.reverse_replicate, List.append_nil] at h39
        have h36 := u_ul36 s1 s4 (encodeBank (popStk (dropStks stks k) 0).2) (skipAcc stks k [])
          (List.replicate onT true)
        rw [skipAcc_restore_pop, List.reverse_nil, List.nil_append] at h36
        simp only [hres_some]
        refine (((hloop.trans (RIn.single hstep)).trans h39).trans h36).mono ?_
        simp only [List.length_replicate]; omega

/- ### Full `rawRun` Simulation Lemma -/

private lemma u_rawRun (progBits s4 : List Bool) (pc : ℕ) (stks : List (List Bool))
    (hpc : pc ≤ progBits.length) :
    RIn uTM.step (uCfg (some ul16) uInitVar [] progBits [] [] s4 (encodeBank stks) []
        (List.replicate pc true) [] [])
      (some (haltList uTM [rawRun progBits s4.length pc stks]))
      ((s4.length + 1) * (2 * (encodeBank stks).length + 2 * s4.length * (progBits.length + 3) +
        15 * progBits.length + 40)) := by
  induction s4 generalizing pc stks with
  | nil =>
    have h1 : uTM.step (uCfg (some ul16) uInitVar [] progBits [] [] [] (encodeBank stks) []
          (List.replicate pc true) [] []) =
        some (uCfg (some ul40) uInitVar [] progBits [] [] [] (encodeBank stks) []
          (List.replicate pc true) [] []) := by
      change some (TM2.stepAux (uProg ul16) uInitVar _) = _
      simp only [uProg, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
        Option.isSome, cond_false, upd_u4]; rfl
    simp only [List.length_nil, rawRun]
    refine ((RIn.single h1).trans
      (u_abort uInitVar [] progBits [] [] [] (encodeBank stks) [] (List.replicate pc true) [] [])).mono ?_
    simp only [List.length_nil, List.length_replicate]; omega
  | cons bf fuel ih =>
    have h1 : uTM.step (uCfg (some ul16) uInitVar [] progBits [] [] (bf :: fuel) (encodeBank stks) []
          (List.replicate pc true) [] []) =
        some (uCfg (some ul17) uInitVar [] progBits [] [] fuel (encodeBank stks) []
          (List.replicate pc true) [] []) := by
      change some (TM2.stepAux (uProg ul16) uInitVar _) = _
      simp only [uProg, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
        Option.isSome, cond_true, upd_u4]; rfl
    simp only [List.length_cons, rawRun]
    let M := 2 * (encodeBank stks).length + 2 * (fuel.length + 1) * (progBits.length + 3) +
      15 * progBits.length + 40
    have hM_mul : ∀ A B, A ≤ M → B ≤ (fuel.length + 1) * M → A + B ≤ (fuel.length + 2) * M := by
      intro A B hA hB
      have : M + (fuel.length + 1) * M = (fuel.length + 2) * M := by ring
      omega
    have hM_one : ∀ A, A ≤ M → A ≤ (fuel.length + 2) * M := by
      intro A hA
      have : M ≤ (fuel.length + 2) * M := Nat.le_mul_of_pos_left M (by omega)
      omega
    have hf_le : fuel.length ≤ 2 * (fuel.length + 1) * (progBits.length + 3) := by
      have hpos : 0 < progBits.length + 3 := by omega
      have hmul : 2 * (fuel.length + 1) ≤ 2 * (fuel.length + 1) * (progBits.length + 3) :=
        Nat.le_mul_of_pos_right _ hpos
      omega
    rcases hfb : fetchBlock progBits pc with _ | _ | blk
    · have h17 := u_ul17_none progBits [] fuel stks pc hfb
      refine ((RIn.single h1).trans h17).mono (hM_one _ ?_)
      simp only [List.length_nil]; dsimp [M]; omega
    · have h17 := u_ul17_some_none progBits [] fuel stks pc hfb
      refine ((RIn.single h1).trans h17).mono (hM_one _ ?_)
      simp only [List.length_nil]; dsimp [M]; omega
    · have h17 := u_ul17_some_some progBits progBits [] fuel stks pc blk (by simp) hfb
      have hblk_le : blk.length ≤ progBits.length := by
        clear h1 h17 ih hpc M hM_mul hM_one hf_le
        induction pc generalizing progBits with
        | zero =>
          cases progBits with
          | nil => simp [fetchBlock] at hfb
          | cons hd tl =>
            simp only [fetchBlock, Option.map_eq_some_iff] at hfb
            rcases hfb with ⟨⟨b', r'⟩, hund, hblk⟩
            have hbeq : b' = blk := Option.some.inj hblk
            subst b'
            have hs1 := eq_delimit_append_of_undelimit (hd :: tl) blk r' hund
            have hl := congrArg List.length hs1
            simp only [List.length_append, length_delimit] at hl
            omega
        | succ pc ihp =>
          cases progBits with
          | nil => simp [fetchBlock] at hfb
          | cons hd tl =>
            simp only [fetchBlock, Option.bind_eq_some_iff] at hfb
            rcases hfb with ⟨⟨b0, r0⟩, hund, hfb'⟩
            have hs1 := eq_delimit_append_of_undelimit (hd :: tl) b0 r0 hund
            have hl := congrArg List.length hs1
            simp only [List.length_append, length_delimit] at hl
            have hle := ihp r0 hfb'
            omega
      cases blk with
      | nil =>
        have h22 : uTM.step (uCfg (some ul22) uInitVar [] progBits [] [] fuel (encodeBank stks) [] [] [] []) =
            some (uCfg (some ul40) uInitVar [] progBits [] [] fuel (encodeBank stks) [] [] [] []) := by
          change some (TM2.stepAux (uProg ul22) uInitVar _) = _
          simp only [uProg, TM2.stepAux, mkUStk, List.head?_nil, List.tail_nil,
            Option.isSome, cond_false, upd_u0]; rfl
        refine (((RIn.single h1).trans h17).trans ((RIn.single h22).trans
          (u_abort uInitVar [] progBits [] [] fuel (encodeBank stks) [] [] [] []))).mono (hM_one _ ?_)
        simp only [List.length_nil] at h17 ⊢; dsimp [M]; omega
      | cons b0 blk1 =>
        cases blk1 with
        | nil =>
          have h22 : uTM.step (uCfg (some ul22) uInitVar [b0] progBits [] [] fuel (encodeBank stks) [] [] [] []) =
              some (uCfg (some ul40) uInitVar [] progBits [] [] fuel (encodeBank stks) [] [] [] []) := by
            cases b0 <;> (
              change some (TM2.stepAux (uProg ul22) uInitVar _) = _
              simp only [uProg, TM2.stepAux, mkUStk, List.head?_cons, List.head?_nil,
                List.tail_cons, List.tail_nil, Option.isSome, Option.getD, cond_true, cond_false, upd_u0]; rfl)
          have hchain := (((RIn.single h1).trans h17).trans ((RIn.single h22).trans
            (u_abort uInitVar [] progBits [] [] fuel (encodeBank stks) [] [] [] []))).mono
            (hM_one _ (by simp only [List.length_nil, List.length_cons] at h17 hblk_le ⊢; dsimp [M]; omega))
          cases b0 <;> exact hchain
        | cons b1 blk2 =>
          cases b0 with
          | false =>
            cases b1 with
            | false =>
              have h22 : uTM.step (uCfg (some ul22) uInitVar (false :: false :: blk2) progBits [] [] fuel
                    (encodeBank stks) [] [] [] []) =
                  some (uCfg (some ul32) uInitVar blk2 progBits [] [] fuel (encodeBank stks) [] [] [] []) := by
                change some (TM2.stepAux (uProg ul22) uInitVar _) = _
                simp only [uProg, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
                  Option.isSome, Option.getD, cond_true, cond_false, upd_u0]; rfl
              have h32 := u_readOut32 blk2 progBits [] [] fuel [] [] [] [] stks
              refine (((RIn.single h1).trans h17).trans ((RIn.single h22).trans h32)).mono (hM_one _ ?_)
              simp only [List.length_cons, List.length_nil] at h17 hblk_le ⊢; dsimp [M]; omega
            | true =>
              have h22 : uTM.step (uCfg (some ul22) uInitVar (false :: true :: blk2) progBits [] [] fuel
                    (encodeBank stks) [] [] [] []) =
                  some (uCfg (some ul23) uInitVar blk2 progBits [] [] fuel (encodeBank stks) [] [] [] []) := by
                change some (TM2.stepAux (uProg ul22) uInitVar _) = _
                simp only [uProg, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
                  Option.isSome, Option.getD, cond_true, cond_false, upd_u0]; rfl
              rcases hdu : decodeUnary blk2 with _ | ⟨next, rest2⟩
              · have h23 := u_ul23_none blk2 progBits fuel (encodeBank stks) [] hdu
                simp only [decodeInstr, hdu, Option.map_none]
                refine (((RIn.single h1).trans h17).trans ((RIn.single h22).trans h23)).mono (hM_one _ ?_)
                simp only [List.length_cons, List.length_nil] at h17 hblk_le ⊢; dsimp [M]; omega
              · have hlen := decodeUnary_len hdu
                have hblk2 := eq_unary_append_of_decodeUnary blk2 next rest2 hdu
                have hnext_le : next ≤ progBits.length := by simp at hblk_le; omega
                have h23 := u_ul23_some next rest2 progBits fuel (encodeBank stks) 0
                rw [← hblk2, Nat.add_zero] at h23
                have h24 := u_ul24 rest2 progBits fuel (encodeBank stks) (List.replicate next true)
                have hih := ih next stks hnext_le
                simp only [decodeInstr, hdu, Option.map_some]
                have hc := ((((RIn.single h1).trans h17).trans (RIn.single h22)).trans
                  (h23.trans h24)).trans hih
                have hmul_rhs : 2 * (encodeBank stks).length +
                    2 * fuel.length * (progBits.length + 3) + 15 * progBits.length + 40 ≤ M := by
                  dsimp [M]
                  have h2mul : 2 * (fuel.length + 1) * (progBits.length + 3) =
                      2 * fuel.length * (progBits.length + 3) + 2 * (progBits.length + 3) := by ring
                  omega
                refine hc.mono (hM_mul _ _ ?_ (Nat.mul_le_mul_left (fuel.length + 1) hmul_rhs))
                simp only [List.length_cons] at h17 hblk_le ⊢; dsimp [M]; omega
          | true =>
            cases b1 with
            | false =>
              cases blk2 with
              | nil =>
                have h22 : uTM.step (uCfg (some ul22) uInitVar [true, false] progBits [] [] fuel
                      (encodeBank stks) [] [] [] []) =
                    some (uCfg (some ul40) uInitVar [] progBits [] [] fuel (encodeBank stks) [] [] [] []) := by
                  change some (TM2.stepAux (uProg ul22) uInitVar _) = _
                  simp only [uProg, TM2.stepAux, mkUStk, List.head?_cons, List.head?_nil,
                    List.tail_cons, List.tail_nil, Option.isSome, Option.getD, cond_true, cond_false,
                    upd_u0]; rfl
                refine (((RIn.single h1).trans h17).trans ((RIn.single h22).trans
                  (u_abort uInitVar [] progBits [] [] fuel (encodeBank stks) [] [] [] []))).mono (hM_one _ ?_)
                simp only [List.length_nil, List.length_cons] at h17 hblk_le ⊢; dsimp [M]; omega
              | cons bPush blk3 =>
                have h22 : uTM.step (uCfg (some ul22) uInitVar (true :: false :: bPush :: blk3) progBits
                      [] [] fuel (encodeBank stks) [] [] [] []) =
                    some (uCfg (some ul25) (false, bPush, none) blk3 progBits [] [] fuel
                      (encodeBank stks) [] [] [] []) := by
                  change some (TM2.stepAux (uProg ul22) uInitVar _) = _
                  simp only [uProg, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
                    Option.isSome, Option.getD, cond_true, cond_false, upd_u0]; rfl
                rcases hdu1 : decodeUnary blk3 with _ | ⟨k, rest3⟩
                · have h25 := u_ul25_none false bPush blk3 progBits fuel (encodeBank stks) [] hdu1
                  simp only [decodeInstr, hdu1, Option.bind_none]
                  refine (((RIn.single h1).trans h17).trans ((RIn.single h22).trans h25)).mono (hM_one _ ?_)
                  simp only [List.length_cons, List.length_nil] at h17 hblk_le ⊢; dsimp [M]; omega
                · have hlen1 := decodeUnary_len hdu1
                  have hblk3 := eq_unary_append_of_decodeUnary blk3 k rest3 hdu1
                  have h25 := u_ul25_some false bPush k rest3 progBits fuel (encodeBank stks) 0
                  rw [← hblk3, Nat.add_zero] at h25
                  rcases hdu2 : decodeUnary rest3 with _ | ⟨next, rest4⟩
                  · have h26 := u_ul26_none false bPush rest3 progBits fuel (encodeBank stks) []
                      (List.replicate k true) hdu2
                    simp only [decodeInstr, hdu1, Option.bind_some, hdu2, Option.map_none]
                    refine (((((RIn.single h1).trans h17).trans (RIn.single h22)).trans h25).trans
                      h26).mono (hM_one _ ?_)
                    simp only [List.length_cons, List.length_nil, List.length_replicate] at h17 hblk_le ⊢
                    dsimp [M]; omega
                  · have hlen2 := decodeUnary_len hdu2
                    have hrest3 := eq_unary_append_of_decodeUnary rest3 next rest4 hdu2
                    have hk_le : k ≤ progBits.length := by simp at hblk_le; omega
                    have hnext_le : next ≤ progBits.length := by simp at hblk_le; omega
                    have h26 := u_ul26_some false bPush next rest4 progBits fuel (encodeBank stks)
                      (List.replicate k true) 0
                    rw [← hrest3, Nat.add_zero] at h26
                    have h31 := u_ul31 false bPush rest4 progBits [] [] fuel (encodeBank stks)
                      (List.replicate next true) (List.replicate k true) []
                    have h34 := u_ul34_push bPush progBits fuel (List.replicate next true) stks k
                    have hih := ih next (pushStk stks k bPush) hnext_le
                    have hpush_len := encodeBank_push_len stks k bPush
                    have hmul_rhs : 2 * (encodeBank (pushStk stks k bPush)).length +
                        2 * fuel.length * (progBits.length + 3) + 15 * progBits.length + 40 ≤ M := by
                      dsimp [M]
                      have h2mul : 2 * (fuel.length + 1) * (progBits.length + 3) =
                          2 * fuel.length * (progBits.length + 3) + 2 * (progBits.length + 3) := by ring
                      omega
                    simp only [decodeInstr, hdu1, Option.bind_some, hdu2, Option.map_some]
                    have hc := (((((((RIn.single h1).trans h17).trans (RIn.single h22)).trans
                      h25).trans h26).trans h31).trans h34).trans hih
                    refine hc.mono (hM_mul _ _ ?_ (Nat.mul_le_mul_left (fuel.length + 1) hmul_rhs))
                    simp only [List.length_cons] at h17 hblk_le ⊢; dsimp [M]; omega
            | true =>
              have h22 : uTM.step (uCfg (some ul22) uInitVar (true :: true :: blk2) progBits [] [] fuel
                    (encodeBank stks) [] [] [] []) =
                  some (uCfg (some ul27) (true, false, none) blk2 progBits [] [] fuel
                    (encodeBank stks) [] [] [] []) := by
                change some (TM2.stepAux (uProg ul22) uInitVar _) = _
                simp only [uProg, TM2.stepAux, mkUStk, List.head?_cons, List.tail_cons,
                  Option.isSome, Option.getD, cond_true, upd_u0]; rfl
              rcases hdu1 : decodeUnary blk2 with _ | ⟨k, r1⟩
              · have h27 := u_ul27_none true false blk2 progBits fuel (encodeBank stks) [] hdu1
                simp only [decodeInstr, hdu1, Option.bind_none]
                refine (((RIn.single h1).trans h17).trans ((RIn.single h22).trans h27)).mono (hM_one _ ?_)
                simp only [List.length_cons, List.length_nil] at h17 hblk_le ⊢; dsimp [M]; omega
              · have hlen1 := decodeUnary_len hdu1
                have hblk2 := eq_unary_append_of_decodeUnary blk2 k r1 hdu1
                have h27 := u_ul27_some true false k r1 progBits fuel (encodeBank stks) 0
                rw [← hblk2, Nat.add_zero] at h27
                rcases hdu2 : decodeUnary r1 with _ | ⟨onE, r2⟩
                · have h28 := u_ul28_none true false r1 progBits [] fuel (encodeBank stks)
                    (List.replicate k true) hdu2
                  simp only [decodeInstr, hdu1, Option.bind_some, hdu2, Option.bind_none]
                  refine (((((RIn.single h1).trans h17).trans (RIn.single h22)).trans h27).trans
                    h28).mono (hM_one _ ?_)
                  simp only [List.length_cons, List.length_nil, List.length_replicate] at h17 hblk_le ⊢
                  dsimp [M]; omega
                · have hlen2 := decodeUnary_len hdu2
                  have hr1 := eq_unary_append_of_decodeUnary r1 onE r2 hdu2
                  have h28 := u_ul28_some true false onE r2 progBits fuel (encodeBank stks)
                    (List.replicate k true) 0
                  rw [← hr1, Nat.add_zero] at h28
                  rcases hdu3 : decodeUnary r2 with _ | ⟨onF, r3⟩
                  · have h29 := u_ul29_none true false r2 progBits (List.replicate onE true) [] fuel
                      (encodeBank stks) (List.replicate k true) hdu3
                    simp only [decodeInstr, hdu1, Option.bind_some, hdu2, hdu3, Option.bind_none]
                    refine ((((((RIn.single h1).trans h17).trans (RIn.single h22)).trans h27).trans
                      h28).trans h29).mono (hM_one _ ?_)
                    simp only [List.length_cons, List.length_nil, List.length_replicate] at h17 hblk_le ⊢
                    dsimp [M]; omega
                  · have hlen3 := decodeUnary_len hdu3
                    have hr2 := eq_unary_append_of_decodeUnary r2 onF r3 hdu3
                    have h29 := u_ul29_some true false onF r3 progBits (List.replicate onE true)
                      fuel (encodeBank stks) (List.replicate k true) 0
                    rw [← hr2, Nat.add_zero] at h29
                    rcases hdu4 : decodeUnary r3 with _ | ⟨onT, r4⟩
                    · have h30 := u_ul30_none true false r3 progBits (List.replicate onE true)
                        (List.replicate onF true) fuel (encodeBank stks) (List.replicate k true) [] hdu4
                      simp only [decodeInstr, hdu1, Option.bind_some, hdu2, hdu3, hdu4, Option.map_none]
                      refine (((((((RIn.single h1).trans h17).trans (RIn.single h22)).trans h27).trans
                        h28).trans h29).trans h30).mono (hM_one _ ?_)
                      simp only [List.length_cons, List.length_nil, List.length_replicate] at h17 hblk_le ⊢
                      dsimp [M]; omega
                    · have hlen4 := decodeUnary_len hdu4
                      have hr3 := eq_unary_append_of_decodeUnary r3 onT r4 hdu4
                      have hk_le : k ≤ progBits.length := by simp at hblk_le; omega
                      have honE_le : onE ≤ progBits.length := by simp at hblk_le; omega
                      have honF_le : onF ≤ progBits.length := by simp at hblk_le; omega
                      have honT_le : onT ≤ progBits.length := by simp at hblk_le; omega
                      have h30 := u_ul30_some true false onT r4 progBits (List.replicate onE true)
                        (List.replicate onF true) fuel (encodeBank stks) (List.replicate k true) 0
                      rw [← hr3, Nat.add_zero] at h30
                      have h31 := u_ul31 true false r4 progBits (List.replicate onE true)
                        (List.replicate onF true) fuel (encodeBank stks) [] (List.replicate k true)
                        (List.replicate onT true)
                      have h34 := u_ul34_pop progBits fuel stks k onE onF onT
                      dsimp only at h34
                      have hpop_len := encodeBank_pop_len stks k
                      let nextPc := match (popStk stks k).1 with
                        | none => onE | some false => onF | some true => onT
                      have hnext_le : nextPc ≤ progBits.length := by
                        cases hpop : (popStk stks k).1 with
                        | none => simpa [nextPc, hpop] using honE_le
                        | some b => cases b <;> simpa [nextPc, hpop] using (by assumption)
                      have hih := ih nextPc (popStk stks k).2 hnext_le
                      have hmul_rhs : 2 * (encodeBank (popStk stks k).2).length +
                          2 * fuel.length * (progBits.length + 3) + 15 * progBits.length + 40 ≤ M := by
                        dsimp [M]
                        have h2mul : 2 * (fuel.length + 1) * (progBits.length + 3) =
                            2 * fuel.length * (progBits.length + 3) + 2 * (progBits.length + 3) := by ring
                        omega
                      simp only [decodeInstr, hdu1, Option.bind_some, hdu2, hdu3, hdu4, Option.map_some]
                      have hraw_eq : rawRun progBits fuel.length nextPc (popStk stks k).2 =
                          match (popStk stks k).1 with
                          | none => rawRun progBits fuel.length onE (popStk stks k).2
                          | some false => rawRun progBits fuel.length onF (popStk stks k).2
                          | some true => rawRun progBits fuel.length onT (popStk stks k).2 := by
                        dsimp only [nextPc]
                        cases (popStk stks k).1 with
                        | none => rfl
                        | some b => cases b <;> rfl
                      rw [← hraw_eq]
                      have hc := (((((((((RIn.single h1).trans h17).trans (RIn.single h22)).trans
                        h27).trans h28).trans h29).trans h30).trans h31).trans h34).trans hih
                      refine hc.mono (hM_mul _ _ ?_ ?_)
                      · simp only [List.length_cons] at h17 hblk_le ⊢; dsimp [M]; omega
                      · exact Nat.mul_le_mul_left (fuel.length + 1) hmul_rhs

end UTMLemmas

theorem isPolyTime_U : IsPolyTime U := by
  let timePoly : Polynomial ℕ :=
    Polynomial.C 4 * Polynomial.X ^ 3 + Polynomial.C 40 * Polynomial.X ^ 2 +
      Polynomial.C 200 * Polynomial.X + Polynomial.C 200
  have hout : ∀ zy : List Bool × List Bool,
      Nonempty (TM2OutputsInTime uTM
        (List.map (Equiv.refl Bool).invFun (bitEncode zy))
        (some (List.map (Equiv.refl Bool).invFun (bitEncode (U zy))))
        (timePoly.eval (bitEncode zy).length)) := by
    rintro ⟨z, y⟩
    have hinit : initList uTM (bitEncode (z, y)) =
        uCfg (some ul0) uInitVar (delimit (bitEncode z) ++ bitEncode y) [] [] [] [] [] [] [] [] [] := by
      dsimp [initList, uTM, uCfg, bitEncode_pair]
      congr 1; funext i; fin_cases i <;> rfl
    have h0 := u_ul0 z (bitEncode y) []
    rw [List.append_nil] at h0
    have h1 := u_ul1 (bitEncode y) [] z.reverse
    rw [List.reverse_reverse, List.append_nil] at h1
    have h2 := u_ul2 y z []
    rw [List.append_nil] at h2
    have h3 := u_ul3 z y.reverse []
    rw [List.reverse_reverse, List.append_nil] at h3
    have hA := ((h0.trans h1).trans h2).trans h3
    let N := (bitEncode (z, y)).length
    have hz_le : z.length ≤ N := by dsimp [N]; rw [length_bitEncode_pair]; omega
    have hy_le : y.length ≤ N := by dsimp [N]; rw [length_bitEncode_pair]; omega
    have hrun_all : RIn uTM.step (initList uTM (bitEncode (z, y)))
        (some (haltList uTM [U (z, y)])) (timePoly.eval N) := by
      rw [hinit]
      rcases hu1 : undelimit z with _ | ⟨progBits, r1⟩
      · have hpz : parseZ z = none := by simp [parseZ, hu1]
        simp only [U, hpz]
        have h4 := u_ul4_none z [] y hu1
        refine (hA.trans h4).mono ?_
        simp only [timePoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C, List.length_nil, List.length_reverse]
        nlinarith
      · have hz_eq := eq_delimit_append_of_undelimit z progBits r1 hu1
        have hp_le : progBits.length ≤ z.length := by
          have := congrArg List.length hz_eq; simp [length_delimit] at this; omega
        have hr1_le : r1.length ≤ z.length := by
          have := congrArg List.length hz_eq; simp [length_delimit] at this; omega
        have h4 := u_ul4_some progBits r1 [] y
        rw [← hz_eq, List.append_nil] at h4
        have h5 := u_ul5 [] r1 progBits.reverse y
        rw [List.reverse_reverse, List.append_nil] at h5
        rcases hu2 : undelimit r1 with _ | ⟨x, r2⟩
        · have hpz : parseZ z = none := by simp [parseZ, hu1, hu2]
          simp only [U, hpz]
          have h6 := u_ul6_none progBits r1 [] y hu2
          refine (((hA.trans h4).trans h5).trans h6).mono ?_
          simp only [timePoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_X, Polynomial.eval_C, List.length_nil, List.length_reverse]
          nlinarith
        · have hr1_eq := eq_delimit_append_of_undelimit r1 x r2 hu2
          have hx_le : x.length ≤ r1.length := by
            have := congrArg List.length hr1_eq; simp [length_delimit] at this; omega
          have hr2_le : r2.length ≤ r1.length := by
            have := congrArg List.length hr1_eq; simp [length_delimit] at this; omega
          have h6 := u_ul6_some progBits x r2 [] y
          rw [← hr1_eq, List.append_nil] at h6
          have h7 := u_ul7 progBits r2 x.reverse [] y
          rw [List.reverse_reverse, List.append_nil] at h7
          rcases hu3 : undelimit r2 with _ | ⟨mStr, tStr⟩
          · have hpz : parseZ z = none := by simp [parseZ, hu1, hu2, hu3]
            simp only [U, hpz]
            have h8 := u_ul8_none progBits r2 [] x y hu3
            refine (((((hA.trans h4).trans h5).trans h6).trans h7).trans h8).mono ?_
            simp only [timePoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
              Polynomial.eval_X, Polynomial.eval_C, List.length_nil, List.length_reverse]
            nlinarith
          · have hr2_eq := eq_delimit_append_of_undelimit r2 mStr tStr hu3
            have hm_le : mStr.length ≤ r2.length := by
              have := congrArg List.length hr2_eq; simp [length_delimit] at this; omega
            have ht_le : tStr.length ≤ r2.length := by
              have := congrArg List.length hr2_eq; simp [length_delimit] at this; omega
            have h8 := u_ul8_some progBits mStr tStr [] x y
            rw [← hr2_eq, List.append_nil] at h8
            have h9 := u_ul9 progBits tStr [] mStr.reverse x y
            rw [List.append_nil] at h9
            have h10 := u_ul10 progBits [] tStr.reverse mStr.reverse x y
            rw [List.reverse_reverse, List.append_nil] at h10
            have h11 := u_ul11 progBits [] mStr tStr.reverse x y
            rw [List.append_nil] at h11
            have hB := (((((((hA.trans h4).trans h5).trans h6).trans h7).trans h8).trans h9).trans
              h10).trans h11
            have hpz : parseZ z = some (progBits, x, mStr, tStr) := by
              simp [parseZ, hu1, hu2, hu3]
            simp only [U, hpz]
            by_cases hle : y.length ≤ mStr.length
            · simp only [hle, ↓reduceIte]
              obtain ⟨s3', hs3'_len, h12⟩ := u_ul12_ok progBits x.reverse mStr tStr.reverse [] y hle
              rw [List.append_nil] at h12
              have h13 := u_ul13 progBits x.reverse s3' tStr.reverse y.reverse
              have h14 := u_ul14 progBits x.reverse tStr.reverse y.reverse []
              rw [List.append_nil, List.reverse_reverse] at h14
              have h15 := u_ul15 progBits tStr.reverse x.reverse [] y
              rw [List.append_nil, List.reverse_reverse] at h15
              have hbank_eq : (delimit (bitEncode x)).flatMap (fun c => [true, c]) ++
                  delimit (bitEncode y) = encodeBank [bitEncode (x, y)] := by
                simp only [encodeBank, List.map_cons, List.map_nil, List.flatten_cons,
                  List.flatten_nil, List.append_nil, bitEncode_pair, delimit_append]
              have hinit_flat : ([true, false] ++ delimit (bitEncode y)) =
                  ((delimit (bitEncode ([] : List Bool))).flatMap (fun c => [true, c]) ++ delimit (bitEncode y)) := by
                simp [bitEncode_list_nil, delimit]
              rw [hinit_flat] at h14
              rw [hbank_eq] at h15
              have hraw := u_rawRun progBits tStr.reverse 0 [bitEncode (x, y)] (Nat.zero_le _)
              rw [List.length_reverse] at hraw
              have hbank_len : (encodeBank [bitEncode (x, y)]).length ≤ 2 * N + 1 := by
                simp only [encodeBank, List.map_cons, List.map_nil, List.flatten_cons,
                  List.flatten_nil, List.append_nil, length_delimit, length_bitEncode_pair]
                dsimp [N]; rw [length_bitEncode_pair]; omega
              have hC := (((hB.trans h12).trans h13).trans h14).trans h15
              refine (hC.trans hraw).mono ?_
              simp only [List.length_reverse, timePoly, Polynomial.eval_add, Polynomial.eval_mul,
                Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
              have ht_N : tStr.length ≤ N := by omega
              have hp_N : progBits.length ≤ N := by omega
              have hq1 : (tStr.length + 1) * (2 * (encodeBank [bitEncode (x, y)]).length +
                    2 * tStr.length * (progBits.length + 3) + 15 * progBits.length + 40) ≤
                  (N + 1) * (2 * (2 * N + 1) + 2 * N * (N + 3) + 15 * N + 40) := by
                apply Nat.mul_le_mul (by omega)
                have : 2 * tStr.length * (progBits.length + 3) ≤ 2 * N * (N + 3) :=
                  Nat.mul_le_mul (by omega) (by omega)
                omega
              have hq2 : (N + 1) * (2 * (2 * N + 1) + 2 * N * (N + 3) + 15 * N + 40) =
                  2 * N ^ 3 + 27 * N ^ 2 + 67 * N + 42 := by ring
              have h4 : 4 * N ^ 3 + 40 * N ^ 2 + 200 * N + 200 ≥
                  2 * N ^ 3 + 27 * N ^ 2 + 67 * N + 42 + 60 * N + 60 := by omega
              omega
            · simp only [hle, ↓reduceIte]
              have hlt : mStr.length < y.length := Nat.lt_of_not_le hle
              have h12 := u_ul12_fail progBits x.reverse mStr tStr.reverse [] y hlt
              refine (hB.trans h12).mono ?_
              simp only [List.length_reverse, List.length_nil, timePoly, Polynomial.eval_add,
                Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
              nlinarith
    obtain ⟨steps, hsteps, heval⟩ := hrun_all
    have heval' : (flip bind uTM.step)^[steps]
        (some (initList uTM (List.map (Equiv.refl Bool).invFun (bitEncode (z, y))))) =
        Option.map (haltList uTM)
          (some (List.map (Equiv.refl Bool).invFun (bitEncode (U (z, y))))) :=
      ((congrArg (fun l : List Bool => (flip bind uTM.step)^[steps] (some (initList uTM l)))
        (List.map_id (bitEncode (z, y)))).trans heval).trans
        (congrArg (fun l : List Bool => some (haltList uTM l))
          (List.map_id [U (z, y)]).symm)
    exact ⟨⟨⟨steps, heval'⟩, hsteps⟩⟩
  exact ⟨{
    tm := uTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := timePoly
    outputsFun := fun zy => Classical.choice (hout zy)
  }⟩

end

end PudlakMod2

namespace PudlakMod3B

open Computability Turing BitstringEncoding ComplexityTheory

noncomputable section

def RIn {σ : Type} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ n ≤ m, (flip bind f)^[n] (some a) = b

lemma RIn.refl {σ : Type} (f : σ → Option σ) (a : σ) : RIn f a (some a) 0 :=
  ⟨0, le_rfl, rfl⟩

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

lemma iterate_bind_none {σ : Type*} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ _ ih => rw [Function.iterate_succ_apply]; exact ih

lemma poly_eval_mono (P : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : P.eval a ≤ P.eval b := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

lemma replicate_append_cons {α : Type*} (k : ℕ) (x : α) (xs : List α) :
    List.replicate k x ++ x :: xs = List.replicate (k + 1) x ++ xs := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, ih]

lemma delimit_eq_flatMap (xs : List Bool) :
    delimit xs = xs.flatMap (fun b => [true, b]) ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [delimit, ih, List.flatMap_cons, List.cons_append, List.nil_append]

lemma bitEncode_bool (b : Bool) : bitEncode b = [b] := rfl

lemma bitEncode_list_nil : bitEncode ([] : List Bool) = [] := rfl

lemma bitEncode_list_cons (b : Bool) (xs : List Bool) :
    bitEncode (b :: xs) = true :: b :: false :: bitEncode xs := rfl

lemma bitEncode_list_append (xs ys : List Bool) :
    bitEncode (xs ++ ys) = bitEncode xs ++ bitEncode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.cons_append, bitEncode_list_cons, ih]

lemma length_bitEncode_list (xs : List Bool) :
    (bitEncode xs).length = 3 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => rw [bitEncode_list_cons]; simp only [List.length_cons, ih]; omega

lemma delimit_bitEncode_cons (b : Bool) (xs : List Bool) :
    delimit (bitEncode (b :: xs)) =
      true :: true :: true :: b :: true :: false :: delimit (bitEncode xs) := rfl

lemma bitEncode_pair (x w : List Bool) :
    bitEncode (x, w) = delimit (bitEncode x) ++ bitEncode w := rfl

lemma length_bitEncode_pair (x w : List Bool) :
    (bitEncode (x, w)).length = 6 * x.length + 3 * w.length + 1 := by
  rw [bitEncode_pair, List.length_append, length_delimit, length_bitEncode_list,
    length_bitEncode_list]
  omega

def hornerAcc : List ℕ → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | c :: cs, n, acc => hornerAcc cs n (n * acc + c)

def polyCoeffsRev (P : Polynomial ℕ) : List ℕ :=
  ((List.range (P.natDegree + 1)).map P.coeff).reverse

lemma hornerAcc_range_rev (f : ℕ → ℕ) :
    ∀ (k n acc : ℕ),
      hornerAcc (((List.range k).map f).reverse) n acc =
        acc * n ^ k + ∑ i ∈ Finset.range k, f i * n ^ i
  | 0, _, acc => by simp [hornerAcc]
  | k + 1, n, acc => by
    rw [List.range_succ, List.map_append, List.map_singleton, List.reverse_append,
      List.reverse_singleton, List.singleton_append, hornerAcc,
      hornerAcc_range_rev f k n (n * acc + f k), Finset.sum_range_succ]
    ring

lemma hornerAcc_polyCoeffsRev (P : Polynomial ℕ) (n : ℕ) :
    hornerAcc (polyCoeffsRev P) n 0 = P.eval n := by
  dsimp [polyCoeffsRev]
  rw [hornerAcc_range_rev P.coeff (P.natDegree + 1) n 0, Nat.zero_mul, Nat.zero_add,
    Polynomial.eval_eq_sum_range]

def encodeCoeffs (cs : List ℕ) : List Bool :=
  (cs.map (fun c => List.replicate c true ++ [false])).flatten

def hornerTotalPoly : List ℕ → Polynomial ℕ → Polynomial ℕ
  | [], _ => 1
  | c :: cs, accP =>
    accP * (Polynomial.C 3 * Polynomial.X + Polynomial.C 4) +
      Polynomial.C (c + 5) +
      hornerTotalPoly cs (Polynomial.X * accP + Polynomial.C c)

def trRel (U V_no : List Bool × List Bool → Bool) (q : Polynomial ℕ)
    (zw : List Bool × List Bool) : Bool :=
  match zw.2 with
  | [] => false
  | true :: payload => decide (payload.length ≤ zw.1.length) && U (zw.1, payload)
  | false :: payload => decide (payload.length ≤ q.eval zw.1.length) && V_no (zw.1, payload)

section TRMachine

variable (M_U M_V : FinTM2)
  (eIn_U : M_U.Γ M_U.k₀ ≃ Bool) (eOut_U : M_U.Γ M_U.k₁ ≃ Bool)
  (eIn_V : M_V.Γ M_V.k₀ ≃ Bool) (eOut_V : M_V.Γ M_V.k₁ ≃ Bool)
  (q : Polynomial ℕ)

private abbrev TRK := Fin 7 ⊕ M_U.K ⊕ M_V.K

private abbrev TRΓ : TRK M_U M_V → Type
  | Sum.inl _ => Bool
  | Sum.inr (Sum.inl k) => M_U.Γ k
  | Sum.inr (Sum.inr k) => M_V.Γ k

private abbrev TRΛ := Fin 21 ⊕ M_U.Λ ⊕ M_V.Λ

private abbrev TRσ := M_U.σ × M_V.σ × Bool × Option Bool

private def trInitVar : TRσ M_U M_V := (M_U.initialState, M_V.initialState, false, none)

private abbrev tl0 : Fin 21 := ⟨0, by decide⟩
private abbrev tl1 : Fin 21 := ⟨1, by decide⟩
private abbrev tl2 : Fin 21 := ⟨2, by decide⟩
private abbrev tl3 : Fin 21 := ⟨3, by decide⟩
private abbrev tl4 : Fin 21 := ⟨4, by decide⟩
private abbrev tl5 : Fin 21 := ⟨5, by decide⟩
private abbrev tl6 : Fin 21 := ⟨6, by decide⟩
private abbrev tl7 : Fin 21 := ⟨7, by decide⟩
private abbrev tl8 : Fin 21 := ⟨8, by decide⟩
private abbrev tl9 : Fin 21 := ⟨9, by decide⟩
private abbrev tl10 : Fin 21 := ⟨10, by decide⟩
private abbrev tl11 : Fin 21 := ⟨11, by decide⟩
private abbrev tl12 : Fin 21 := ⟨12, by decide⟩
private abbrev tl13 : Fin 21 := ⟨13, by decide⟩
private abbrev tl14 : Fin 21 := ⟨14, by decide⟩
private abbrev tl15 : Fin 21 := ⟨15, by decide⟩
private abbrev tl16 : Fin 21 := ⟨16, by decide⟩
private abbrev tl17 : Fin 21 := ⟨17, by decide⟩
private abbrev tl18 : Fin 21 := ⟨18, by decide⟩
private abbrev tl19 : Fin 21 := ⟨19, by decide⟩
private abbrev tl20 : Fin 21 := ⟨20, by decide⟩

private def liftStmtU :
    TM2.Stmt M_U.Γ M_U.Λ M_U.σ → TM2.Stmt (TRΓ M_U M_V) (TRΛ M_U M_V) (TRσ M_U M_V)
  | .push k f s => .push (Sum.inr (Sum.inl k)) (fun v => f v.1) (liftStmtU s)
  | .peek k f s => .peek (Sum.inr (Sum.inl k)) (fun v o => (f v.1 o, v.2)) (liftStmtU s)
  | .pop k f s => .pop (Sum.inr (Sum.inl k)) (fun v o => (f v.1 o, v.2)) (liftStmtU s)
  | .load a s => .load (fun v => (a v.1, v.2)) (liftStmtU s)
  | .branch f s₁ s₂ => .branch (fun v => f v.1) (liftStmtU s₁) (liftStmtU s₂)
  | .goto f => .goto (fun v => Sum.inr (Sum.inl (f v.1)))
  | .halt => .goto (fun _ => Sum.inl tl15)

private def liftStmtV :
    TM2.Stmt M_V.Γ M_V.Λ M_V.σ → TM2.Stmt (TRΓ M_U M_V) (TRΛ M_U M_V) (TRσ M_U M_V)
  | .push k f s => .push (Sum.inr (Sum.inr k)) (fun v => f v.2.1) (liftStmtV s)
  | .peek k f s => .peek (Sum.inr (Sum.inr k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftStmtV s)
  | .pop k f s => .pop (Sum.inr (Sum.inr k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftStmtV s)
  | .load a s => .load (fun v => (v.1, a v.2.1, v.2.2)) (liftStmtV s)
  | .branch f s₁ s₂ => .branch (fun v => f v.2.1) (liftStmtV s₁) (liftStmtV s₂)
  | .goto f => .goto (fun v => Sum.inr (Sum.inr (f v.2.1)))
  | .halt => .goto (fun _ => Sum.inl tl18)

private def pushBitsTR (stk : Fin 7) :
    List Bool → TM2.Stmt (TRΓ M_U M_V) (TRΛ M_U M_V) (TRσ M_U M_V) →
      TM2.Stmt (TRΓ M_U M_V) (TRΛ M_U M_V) (TRσ M_U M_V)
  | [], s => s
  | b :: bs, s => pushBitsTR stk bs (.push (Sum.inl stk) (fun _ => b) s)

private def trProg : TRΛ M_U M_V → TM2.Stmt (TRΓ M_U M_V) (TRΛ M_U M_V) (TRσ M_U M_V)
  | Sum.inr (Sum.inl l) => liftStmtU M_U M_V (M_U.m l)
  | Sum.inr (Sum.inr l) => liftStmtV M_U M_V (M_V.m l)
  | Sum.inl ⟨0, _⟩ =>
    .pop (Sum.inl 0) (fun v o => (v.1, v.2.1, false, o))
      (.branch (fun v => v.2.2.2.getD false)
        (.pop (Sum.inl 0) (fun v _ => v)
          (.pop (Sum.inl 0) (fun v _ => v)
            (.pop (Sum.inl 0) (fun v o => (v.1, v.2.1, false, o))
              (.push (Sum.inl 1) (fun v => v.2.2.2.getD false)
                (.push (Sum.inl 2) (fun _ => true)
                  (.pop (Sum.inl 0) (fun v _ => v)
                    (.pop (Sum.inl 0) (fun _ _ => trInitVar M_U M_V)
                      (.goto (fun _ => Sum.inl tl0)))))))))
        (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl1))))
  | Sum.inl ⟨1, _⟩ =>
    .pop (Sum.inl 0) (fun v o => (v.1, v.2.1, false, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.pop (Sum.inl 0) (fun v o => (v.1, v.2.1, o.getD false, none))
          (.pop (Sum.inl 0) (fun v _ => (v.1, v.2.1, v.2.2.1, none))
            (.goto (fun _ => Sum.inl tl2))))
        (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl19))))
  | Sum.inl ⟨2, _⟩ =>
    .pop (Sum.inl 0) (fun v o => (v.1, v.2.1, v.2.2.1, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.pop (Sum.inl 0) (fun v o => (v.1, v.2.1, v.2.2.1, o))
          (.push (Sum.inl 6) (fun v => v.2.2.2.getD false)
            (.pop (Sum.inl 0) (fun v _ => (v.1, v.2.1, v.2.2.1, none))
              (.goto (fun _ => Sum.inl tl2)))))
        (.branch (fun v => v.2.2.1)
          (pushBitsTR M_U M_V 3 (encodeCoeffs (polyCoeffsRev Polynomial.X))
            (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl3))))
          (pushBitsTR M_U M_V 3 (encodeCoeffs (polyCoeffsRev q))
            (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl3))))))
  | Sum.inl ⟨3, _⟩ =>
    .peek (Sum.inl 3) (fun v o => (v.1, v.2.1, v.2.2.1, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl4)))
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl9))))
  | Sum.inl ⟨4, _⟩ =>
    .pop (Sum.inl 4) (fun v o => (v.1, v.2.1, v.2.2.1, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl5)))
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl7))))
  | Sum.inl ⟨5, _⟩ =>
    .pop (Sum.inl 2) (fun v o => (v.1, v.2.1, v.2.2.1, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.push (Sum.inl 0) (fun _ => true)
          (.push (Sum.inl 5) (fun _ => true)
            (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl5)))))
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl6))))
  | Sum.inl ⟨6, _⟩ =>
    .pop (Sum.inl 0) (fun v o => (v.1, v.2.1, v.2.2.1, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.push (Sum.inl 2) (fun _ => true)
          (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl6))))
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl4))))
  | Sum.inl ⟨7, _⟩ =>
    .pop (Sum.inl 5) (fun v o => (v.1, v.2.1, v.2.2.1, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.push (Sum.inl 4) (fun _ => true)
          (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl7))))
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl8))))
  | Sum.inl ⟨8, _⟩ =>
    .pop (Sum.inl 3) (fun v o => (v.1, v.2.1, v.2.2.1, o))
      (.branch (fun v => v.2.2.2.getD false)
        (.push (Sum.inl 4) (fun _ => true)
          (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl8))))
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl3))))
  | Sum.inl ⟨9, _⟩ =>
    .pop (Sum.inl 2) (fun v o => (v.1, v.2.1, v.2.2.1, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl9)))
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl10))))
  | Sum.inl ⟨10, _⟩ =>
    .pop (Sum.inl 6) (fun v o => (v.1, v.2.1, v.2.2.1, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.push (Sum.inl 2) (fun v => v.2.2.2.getD false)
          (.pop (Sum.inl 4) (fun v o => (v.1, v.2.1, v.2.2.1, o))
            (.branch (fun v => v.2.2.2.isSome)
              (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl10)))
              (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl19))))))
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl11))))
  | Sum.inl ⟨11, _⟩ =>
    .pop (Sum.inl 4) (fun v o => (v.1, v.2.1, v.2.2.1, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl11)))
        (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl12))))
  | Sum.inl ⟨12, _⟩ =>
    .pop (Sum.inl 2) (fun v o => (v.1, v.2.1, v.2.2.1, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.push (Sum.inl 6) (fun v => v.2.2.2.getD false)
          (.load (fun v => (v.1, v.2.1, v.2.2.1, none)) (.goto (fun _ => Sum.inl tl12))))
        (.branch (fun v => v.2.2.1)
          (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl13)))
          (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl16)))))
  | Sum.inl ⟨13, _⟩ =>
    .pop (Sum.inl 6) (fun v o => (v.1, v.2.1, false, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.push (Sum.inr (Sum.inl M_U.k₀)) (fun _ => eIn_U.symm false)
          (.push (Sum.inr (Sum.inl M_U.k₀)) (fun v => eIn_U.symm (v.2.2.2.getD false))
            (.push (Sum.inr (Sum.inl M_U.k₀)) (fun _ => eIn_U.symm true)
              (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl13))))))
        (.push (Sum.inr (Sum.inl M_U.k₀)) (fun _ => eIn_U.symm false)
          (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl14)))))
  | Sum.inl ⟨14, _⟩ =>
    .pop (Sum.inl 1) (fun v o => (v.1, v.2.1, false, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.push (Sum.inr (Sum.inl M_U.k₀)) (fun _ => eIn_U.symm false)
          (.push (Sum.inr (Sum.inl M_U.k₀)) (fun _ => eIn_U.symm true)
            (.push (Sum.inr (Sum.inl M_U.k₀)) (fun v => eIn_U.symm (v.2.2.2.getD false))
              (.push (Sum.inr (Sum.inl M_U.k₀)) (fun _ => eIn_U.symm true)
                (.push (Sum.inr (Sum.inl M_U.k₀)) (fun _ => eIn_U.symm true)
                  (.push (Sum.inr (Sum.inl M_U.k₀)) (fun _ => eIn_U.symm true)
                    (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl14)))))))))
        (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inr (Sum.inl M_U.main)))))
  | Sum.inl ⟨15, _⟩ =>
    .pop (Sum.inr (Sum.inl M_U.k₁)) (fun v o => (v.1, v.2.1, (o.map eOut_U).getD false, none))
      (.push (Sum.inl 0) (fun v => v.2.2.1)
        (.load (fun _ => trInitVar M_U M_V) .halt))
  | Sum.inl ⟨16, _⟩ =>
    .pop (Sum.inl 6) (fun v o => (v.1, v.2.1, false, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.push (Sum.inr (Sum.inr M_V.k₀)) (fun _ => eIn_V.symm false)
          (.push (Sum.inr (Sum.inr M_V.k₀)) (fun v => eIn_V.symm (v.2.2.2.getD false))
            (.push (Sum.inr (Sum.inr M_V.k₀)) (fun _ => eIn_V.symm true)
              (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl16))))))
        (.push (Sum.inr (Sum.inr M_V.k₀)) (fun _ => eIn_V.symm false)
          (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl17)))))
  | Sum.inl ⟨17, _⟩ =>
    .pop (Sum.inl 1) (fun v o => (v.1, v.2.1, false, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.push (Sum.inr (Sum.inr M_V.k₀)) (fun _ => eIn_V.symm false)
          (.push (Sum.inr (Sum.inr M_V.k₀)) (fun _ => eIn_V.symm true)
            (.push (Sum.inr (Sum.inr M_V.k₀)) (fun v => eIn_V.symm (v.2.2.2.getD false))
              (.push (Sum.inr (Sum.inr M_V.k₀)) (fun _ => eIn_V.symm true)
                (.push (Sum.inr (Sum.inr M_V.k₀)) (fun _ => eIn_V.symm true)
                  (.push (Sum.inr (Sum.inr M_V.k₀)) (fun _ => eIn_V.symm true)
                    (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl17)))))))))
        (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inr (Sum.inr M_V.main)))))
  | Sum.inl ⟨18, _⟩ =>
    .pop (Sum.inr (Sum.inr M_V.k₁)) (fun v o => (v.1, v.2.1, (o.map eOut_V).getD false, none))
      (.push (Sum.inl 0) (fun v => v.2.2.1)
        (.load (fun _ => trInitVar M_U M_V) .halt))
  | Sum.inl ⟨19, _⟩ =>
    .pop (Sum.inl 1) (fun v o => (v.1, v.2.1, false, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl19)))
        (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl20))))
  | Sum.inl ⟨_ + 20, _⟩ =>
    .pop (Sum.inl 2) (fun v o => (v.1, v.2.1, false, o))
      (.branch (fun v => v.2.2.2.isSome)
        (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl20)))
        (.pop (Sum.inl 6) (fun v o => (v.1, v.2.1, false, o))
          (.branch (fun v => v.2.2.2.isSome)
            (.load (fun _ => trInitVar M_U M_V) (.goto (fun _ => Sum.inl tl20)))
            (.push (Sum.inl 0) (fun _ => false)
              (.load (fun _ => trInitVar M_U M_V) .halt)))))

private def trTM : FinTM2 :=
  let _ := M_U.kFin
  let _ := M_U.ΛFin
  let _ := M_U.σFin
  let _ := M_V.kFin
  let _ := M_V.ΛFin
  let _ := M_V.σFin
  { K := TRK M_U M_V
    k₀ := Sum.inl 0
    k₁ := Sum.inl 0
    Γ := TRΓ M_U M_V
    Λ := TRΛ M_U M_V
    main := Sum.inl tl0
    σ := TRσ M_U M_V
    initialState := trInitVar M_U M_V
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q }

variable {M_U M_V eIn_U eOut_U eIn_V eOut_V q}

private def emptyU : ∀ k, List (M_U.Γ k) := fun _ => []
private def emptyV : ∀ k, List (M_V.Γ k) := fun _ => []

private def mkTRStk (s0 s1 s2 s3 s4 s5 s6 : List Bool)
    (sU : ∀ k, List (M_U.Γ k)) (sV : ∀ k, List (M_V.Γ k)) :
    ∀ k : TRK M_U M_V, List (TRΓ M_U M_V k)
  | Sum.inl 0 => s0
  | Sum.inl 1 => s1
  | Sum.inl 2 => s2
  | Sum.inl 3 => s3
  | Sum.inl 4 => s4
  | Sum.inl 5 => s5
  | Sum.inl 6 => s6
  | Sum.inr (Sum.inl k) => sU k
  | Sum.inr (Sum.inr k) => sV k

private def trCfg (l : Option (TRΛ M_U M_V)) (v : TRσ M_U M_V)
    (s0 s1 s2 s3 s4 s5 s6 : List Bool)
    (sU : ∀ k, List (M_U.Γ k)) (sV : ∀ k, List (M_V.Γ k)) :
    (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).Cfg :=
  ⟨l, v, mkTRStk s0 s1 s2 s3 s4 s5 s6 sU sV⟩

private lemma upd_tr0 (s0 s0' s1 s2 s3 s4 s5 s6 : List Bool)
    (sU : ∀ k, List (M_U.Γ k)) (sV : ∀ k, List (M_V.Γ k)) :
    Function.update (mkTRStk s0 s1 s2 s3 s4 s5 s6 sU sV) (Sum.inl 0) s0' =
      mkTRStk s0' s1 s2 s3 s4 s5 s6 sU sV := by
  funext k; rcases k with i | kU | kV; · fin_cases i <;> rfl
  · rfl
  · rfl

private lemma upd_tr1 (s0 s1 s1' s2 s3 s4 s5 s6 : List Bool)
    (sU : ∀ k, List (M_U.Γ k)) (sV : ∀ k, List (M_V.Γ k)) :
    Function.update (mkTRStk s0 s1 s2 s3 s4 s5 s6 sU sV) (Sum.inl 1) s1' =
      mkTRStk s0 s1' s2 s3 s4 s5 s6 sU sV := by
  funext k; rcases k with i | kU | kV; · fin_cases i <;> rfl
  · rfl
  · rfl

private lemma upd_tr2 (s0 s1 s2 s2' s3 s4 s5 s6 : List Bool)
    (sU : ∀ k, List (M_U.Γ k)) (sV : ∀ k, List (M_V.Γ k)) :
    Function.update (mkTRStk s0 s1 s2 s3 s4 s5 s6 sU sV) (Sum.inl 2) s2' =
      mkTRStk s0 s1 s2' s3 s4 s5 s6 sU sV := by
  funext k; rcases k with i | kU | kV; · fin_cases i <;> rfl
  · rfl
  · rfl

private lemma upd_tr3 (s0 s1 s2 s3 s3' s4 s5 s6 : List Bool)
    (sU : ∀ k, List (M_U.Γ k)) (sV : ∀ k, List (M_V.Γ k)) :
    Function.update (mkTRStk s0 s1 s2 s3 s4 s5 s6 sU sV) (Sum.inl 3) s3' =
      mkTRStk s0 s1 s2 s3' s4 s5 s6 sU sV := by
  funext k; rcases k with i | kU | kV; · fin_cases i <;> rfl
  · rfl
  · rfl

private lemma upd_tr4 (s0 s1 s2 s3 s4 s4' s5 s6 : List Bool)
    (sU : ∀ k, List (M_U.Γ k)) (sV : ∀ k, List (M_V.Γ k)) :
    Function.update (mkTRStk s0 s1 s2 s3 s4 s5 s6 sU sV) (Sum.inl 4) s4' =
      mkTRStk s0 s1 s2 s3 s4' s5 s6 sU sV := by
  funext k; rcases k with i | kU | kV; · fin_cases i <;> rfl
  · rfl
  · rfl

private lemma upd_tr5 (s0 s1 s2 s3 s4 s5 s5' s6 : List Bool)
    (sU : ∀ k, List (M_U.Γ k)) (sV : ∀ k, List (M_V.Γ k)) :
    Function.update (mkTRStk s0 s1 s2 s3 s4 s5 s6 sU sV) (Sum.inl 5) s5' =
      mkTRStk s0 s1 s2 s3 s4 s5' s6 sU sV := by
  funext k; rcases k with i | kU | kV; · fin_cases i <;> rfl
  · rfl
  · rfl

private lemma upd_tr6 (s0 s1 s2 s3 s4 s5 s6 s6' : List Bool)
    (sU : ∀ k, List (M_U.Γ k)) (sV : ∀ k, List (M_V.Γ k)) :
    Function.update (mkTRStk s0 s1 s2 s3 s4 s5 s6 sU sV) (Sum.inl 6) s6' =
      mkTRStk s0 s1 s2 s3 s4 s5 s6' sU sV := by
  funext k; rcases k with i | kU | kV; · fin_cases i <;> rfl
  · rfl
  · rfl

private lemma upd_trU (s0 s1 s2 s3 s4 s5 s6 : List Bool)
    (sU : ∀ k, List (M_U.Γ k)) (sV : ∀ k, List (M_V.Γ k))
    (k : M_U.K) (val : List (M_U.Γ k)) :
    Function.update (mkTRStk s0 s1 s2 s3 s4 s5 s6 sU sV) (Sum.inr (Sum.inl k)) val =
      mkTRStk s0 s1 s2 s3 s4 s5 s6 (Function.update sU k val) sV := by
  funext k'
  rcases k' with i | kU | kV
  · fin_cases i <;> rfl
  · by_cases hk : kU = k
    · subst hk; simp [Function.update, mkTRStk]
    · simp [Function.update, mkTRStk, hk]
  · rfl

private lemma upd_trV (s0 s1 s2 s3 s4 s5 s6 : List Bool)
    (sU : ∀ k, List (M_U.Γ k)) (sV : ∀ k, List (M_V.Γ k))
    (k : M_V.K) (val : List (M_V.Γ k)) :
    Function.update (mkTRStk s0 s1 s2 s3 s4 s5 s6 sU sV) (Sum.inr (Sum.inr k)) val =
      mkTRStk s0 s1 s2 s3 s4 s5 s6 sU (Function.update sV k val) := by
  funext k'
  rcases k' with i | kU | kV
  · fin_cases i <;> rfl
  · rfl
  · by_cases hk : kV = k
    · subst hk; simp [Function.update, mkTRStk]
    · simp [Function.update, mkTRStk, hk]

private lemma stepAux_pushBitsTR (stk : Fin 7) (bs : List Bool)
    (s : TM2.Stmt (TRΓ M_U M_V) (TRΛ M_U M_V) (TRσ M_U M_V))
    (v : TRσ M_U M_V) (S : ∀ k : TRK M_U M_V, List (TRΓ M_U M_V k)) :
    TM2.stepAux (pushBitsTR M_U M_V stk bs s) v S =
      TM2.stepAux s v (Function.update S (Sum.inl stk) (bs ++ S (Sum.inl stk))) := by
  induction bs generalizing s with
  | nil => simp [pushBitsTR]
  | cons b bs ih =>
    rw [pushBitsTR, ih]
    simp only [TM2.stepAux, Function.update_idem, Function.update_self, List.cons_append]

private lemma mkTRStk_halt (res : Bool) :
    ({ l := none, var := trInitVar M_U M_V,
       stk := mkTRStk [res] [] [] [] [] [] [] emptyU emptyV } :
      (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).Cfg) =
    haltList (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q) [res] := by
  dsimp [haltList, trTM]
  congr 1; funext k
  rcases k with i | kU | kV
  · fin_cases i <;> rfl
  · rfl
  · rfl

/- ### Embedded `M_U` and `M_V` Simulation -/

private def embedU (c : M_U.Cfg) : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).Cfg :=
  ⟨match c.l with
    | some l => some (Sum.inr (Sum.inl l))
    | none => some (Sum.inl tl15),
   (c.var, M_V.initialState, false, none),
   mkTRStk [] [] [] [] [] [] [] c.stk emptyV⟩

private lemma stepAux_liftStmtU (st : TM2.Stmt M_U.Γ M_U.Λ M_U.σ) (vU : M_U.σ)
    (sU : ∀ k, List (M_U.Γ k)) :
    TM2.stepAux (liftStmtU M_U M_V st) (vU, M_V.initialState, false, none)
      (mkTRStk [] [] [] [] [] [] [] sU emptyV) =
    embedU (eIn_U := eIn_U) (eOut_U := eOut_U) (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q)
      (TM2.stepAux st vU sU) := by
  induction st generalizing vU sU with
  | push k f s ih =>
    simp only [liftStmtU, TM2.stepAux, mkTRStk, upd_trU]
    exact ih _ _
  | peek k f s ih =>
    simp only [liftStmtU, TM2.stepAux, mkTRStk]
    exact ih _ _
  | pop k f s ih =>
    simp only [liftStmtU, TM2.stepAux, mkTRStk, upd_trU]
    exact ih _ _
  | load a s ih =>
    simp only [liftStmtU, TM2.stepAux]
    exact ih _ _
  | branch f s₁ s₂ ih₁ ih₂ =>
    simp only [liftStmtU, TM2.stepAux, ih₁, ih₂]
    cases f vU <;> rfl
  | goto _ => rfl
  | halt => rfl

private lemma sim_MU :
    ∀ (n : ℕ) (c c_end : M_U.Cfg),
      (flip bind M_U.step)^[n] (some c) = some c_end →
      RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (embedU c) (some (embedU c_end)) n
  | 0, c, c_end, h => by
    injection h with hce; subst hce; exact RIn.refl _ _
  | n + 1, ⟨none, vU, sU⟩, c_end, h => by
    rw [Function.iterate_succ_apply] at h
    change (flip bind M_U.step)^[n] none = some c_end at h
    rw [iterate_bind_none] at h
    cases h
  | n + 1, ⟨some l, vU, sU⟩, c_end, h => by
    rw [Function.iterate_succ_apply] at h
    change (flip bind M_U.step)^[n] (some (TM2.stepAux (M_U.m l) vU sU)) = some c_end at h
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step (embedU ⟨some l, vU, sU⟩) =
        some (embedU (TM2.stepAux (M_U.m l) vU sU)) := by
      change some (TM2.stepAux (liftStmtU M_U M_V (M_U.m l)) _ _) = _
      rw [stepAux_liftStmtU]
      rfl
    exact ((RIn.single h1).trans (sim_MU n _ c_end h)).mono (by omega)

private def embedV (c : M_V.Cfg) : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).Cfg :=
  ⟨match c.l with
    | some l => some (Sum.inr (Sum.inr l))
    | none => some (Sum.inl tl18),
   (M_U.initialState, c.var, false, none),
   mkTRStk [] [] [] [] [] [] [] emptyU c.stk⟩

private lemma stepAux_liftStmtV (st : TM2.Stmt M_V.Γ M_V.Λ M_V.σ) (vV : M_V.σ)
    (sV : ∀ k, List (M_V.Γ k)) :
    TM2.stepAux (liftStmtV M_U M_V st) (M_U.initialState, vV, false, none)
      (mkTRStk [] [] [] [] [] [] [] emptyU sV) =
    embedV (eIn_U := eIn_U) (eOut_U := eOut_U) (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q)
      (TM2.stepAux st vV sV) := by
  induction st generalizing vV sV with
  | push k f s ih =>
    simp only [liftStmtV, TM2.stepAux, mkTRStk, upd_trV]
    exact ih _ _
  | peek k f s ih =>
    simp only [liftStmtV, TM2.stepAux, mkTRStk]
    exact ih _ _
  | pop k f s ih =>
    simp only [liftStmtV, TM2.stepAux, mkTRStk, upd_trV]
    exact ih _ _
  | load a s ih =>
    simp only [liftStmtV, TM2.stepAux]
    exact ih _ _
  | branch f s₁ s₂ ih₁ ih₂ =>
    simp only [liftStmtV, TM2.stepAux, ih₁, ih₂]
    cases f vV <;> rfl
  | goto _ => rfl
  | halt => rfl

private lemma sim_MV :
    ∀ (n : ℕ) (c c_end : M_V.Cfg),
      (flip bind M_V.step)^[n] (some c) = some c_end →
      RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (embedV c) (some (embedV c_end)) n
  | 0, c, c_end, h => by
    injection h with hce; subst hce; exact RIn.refl _ _
  | n + 1, ⟨none, vV, sV⟩, c_end, h => by
    rw [Function.iterate_succ_apply] at h
    change (flip bind M_V.step)^[n] none = some c_end at h
    rw [iterate_bind_none] at h
    cases h
  | n + 1, ⟨some l, vV, sV⟩, c_end, h => by
    rw [Function.iterate_succ_apply] at h
    change (flip bind M_V.step)^[n] (some (TM2.stepAux (M_V.m l) vV sV)) = some c_end at h
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step (embedV ⟨some l, vV, sV⟩) =
        some (embedV (TM2.stepAux (M_V.m l) vV sV)) := by
      change some (TM2.stepAux (liftStmtV M_U M_V (M_V.m l)) _ _) = _
      rw [stepAux_liftStmtV]
      rfl
    exact ((RIn.single h1).trans (sim_MV n _ c_end h)).mono (by omega)

/- ### Phase Lemmas `tl0 .. tl20` -/

private lemma tr_unpackZ (zs rest accZ accN : List Bool) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl0)) (trInitVar M_U M_V)
        (delimit (bitEncode zs) ++ rest) accZ accN [] [] [] [] emptyU emptyV)
      (some (trCfg (some (Sum.inl tl1)) (trInitVar M_U M_V)
        rest (zs.reverse ++ accZ) (List.replicate zs.length true ++ accN) [] [] [] [] emptyU emptyV))
      (zs.length + 1) := by
  induction zs generalizing accZ accN with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl0)) _ _) = _
    simp only [trProg, bitEncode_list_nil, delimit, List.cons_append, List.nil_append,
      List.reverse_nil, TM2.stepAux, mkTRStk, List.head?_cons,
      List.tail_cons, Option.getD, cond_false, upd_tr0]
    rfl
  | cons b zs ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl0)) (trInitVar M_U M_V)
          (delimit (bitEncode (b :: zs)) ++ rest) accZ accN [] [] [] [] emptyU emptyV) =
        some (trCfg (some (Sum.inl tl0)) (trInitVar M_U M_V)
          (delimit (bitEncode zs) ++ rest) (b :: accZ) (true :: accN) [] [] [] [] emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl0)) _ _) = _
      rw [delimit_bitEncode_cons]
      simp only [trProg, List.cons_append, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons,
        Option.getD, cond_true, upd_tr0, upd_tr1, upd_tr2]
      rfl
    have htr := (RIn.single h1).trans (ih (b :: accZ) (true :: accN))
    rw [replicate_append_cons] at htr
    have hrev : zs.reverse ++ b :: accZ = (b :: zs).reverse ++ accZ := by
      simp [List.reverse_cons, List.append_assoc]
    rw [hrev] at htr
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma tr_abort19 (s1 s2 s6 : List Bool) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl19)) (trInitVar M_U M_V) [] s1 s2 [] [] [] s6 emptyU emptyV)
      (some (trCfg (some (Sum.inl tl20)) (trInitVar M_U M_V) [] [] s2 [] [] [] s6 emptyU emptyV))
      (s1.length + 1) := by
  induction s1 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl19)) _ _) = _
    simp only [trProg, TM2.stepAux, mkTRStk, List.head?_nil, List.tail_nil, Option.isSome,
      cond_false, upd_tr1]
    rfl
  | cons b s1 ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl19)) (trInitVar M_U M_V) [] (b :: s1) s2 [] [] [] s6 emptyU emptyV) =
        some (trCfg (some (Sum.inl tl19)) (trInitVar M_U M_V) [] s1 s2 [] [] [] s6 emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl19)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        cond_true, upd_tr1]
      rfl
    exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)

private lemma tr_abort20_s6 (s6 : List Bool) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl20)) (trInitVar M_U M_V) [] [] [] [] [] [] s6 emptyU emptyV)
      (some (haltList (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q) [false]))
      (s6.length + 1) := by
  induction s6 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl20)) _ _) = _
    simp only [trProg, TM2.stepAux, mkTRStk, List.head?_nil, List.tail_nil, Option.isSome,
      cond_false, upd_tr2, upd_tr6, upd_tr0]
    exact congr_arg some (mkTRStk_halt false)
  | cons b s6 ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl20)) (trInitVar M_U M_V) [] [] [] [] [] [] (b :: s6) emptyU emptyV) =
        some (trCfg (some (Sum.inl tl20)) (trInitVar M_U M_V) [] [] [] [] [] [] s6 emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl20)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_nil, List.tail_nil, List.head?_cons,
        List.tail_cons, Option.isSome, cond_false, cond_true, upd_tr2, upd_tr6]
      rfl
    exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)

private lemma tr_abort20 (s2 s6 : List Bool) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl20)) (trInitVar M_U M_V) [] [] s2 [] [] [] s6 emptyU emptyV)
      (some (haltList (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q) [false]))
      (s2.length + s6.length + 1) := by
  induction s2 with
  | nil =>
    simpa using tr_abort20_s6 (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
      (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) s6
  | cons b s2 ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl20)) (trInitVar M_U M_V) [] [] (b :: s2) [] [] [] s6 emptyU emptyV) =
        some (trCfg (some (Sum.inl tl20)) (trInitVar M_U M_V) [] [] s2 [] [] [] s6 emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl20)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        cond_true, upd_tr2]
      rfl
    exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)

private lemma tr_unpackPay (tag : Bool) (pay s1 s2 acc6 : List Bool) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl2)) (M_U.initialState, M_V.initialState, tag, none)
        (bitEncode pay) s1 s2 [] [] [] acc6 emptyU emptyV)
      (some (trCfg (some (Sum.inl tl3)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 s2 (encodeCoeffs (polyCoeffsRev (if tag then Polynomial.X else q)))
        [] [] (pay.reverse ++ acc6) emptyU emptyV))
      (pay.length + 1) := by
  induction pay generalizing acc6 with
  | nil =>
    cases tag <;> {
      refine RIn.single ?_
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl2)) _ _) = _
      dsimp only [trProg, bitEncode_list_nil, TM2.stepAux, mkTRStk, Option.isSome, cond]
      rw [upd_tr0, stepAux_pushBitsTR]
      simp only [mkTRStk, List.append_nil, upd_tr3, TM2.stepAux, List.reverse_nil, List.nil_append]
      rfl
    }
  | cons b pay ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl2)) (M_U.initialState, M_V.initialState, tag, none)
          (bitEncode (b :: pay)) s1 s2 [] [] [] acc6 emptyU emptyV) =
        some (trCfg (some (Sum.inl tl2)) (M_U.initialState, M_V.initialState, tag, none)
          (bitEncode pay) s1 s2 [] [] [] (b :: acc6) emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl2)) _ _) = _
      simp only [trProg, bitEncode_list_cons, TM2.stepAux, mkTRStk, List.head?_cons,
        List.tail_cons, Option.isSome, Option.getD, cond_true, upd_tr0, upd_tr6]
      rfl
    have htr := (RIn.single h1).trans (ih (b :: acc6))
    have hrev : pay.reverse ++ b :: acc6 = (b :: pay).reverse ++ acc6 := by
      simp [List.reverse_cons, List.append_assoc]
    rw [hrev] at htr
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma tr_copyN (tag : Bool) (s0 s1 cStk s4 s5 s6 : List Bool) (k : ℕ) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl5)) (M_U.initialState, M_V.initialState, tag, none)
        s0 s1 (List.replicate k true) cStk s4 s5 s6 emptyU emptyV)
      (some (trCfg (some (Sum.inl tl6)) (M_U.initialState, M_V.initialState, tag, none)
        (List.replicate k true ++ s0) s1 [] cStk s4 (List.replicate k true ++ s5) s6 emptyU emptyV))
      (k + 1) := by
  induction k generalizing s0 s5 with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl5)) _ _) = _
    simp only [trProg, List.replicate_zero, List.nil_append, TM2.stepAux, mkTRStk, List.head?_nil,
      List.tail_nil, Option.isSome, cond_false, upd_tr2]
    rfl
  | succ k ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl5)) (M_U.initialState, M_V.initialState, tag, none)
          s0 s1 (true :: List.replicate k true) cStk s4 s5 s6 emptyU emptyV) =
        some (trCfg (some (Sum.inl tl5)) (M_U.initialState, M_V.initialState, tag, none)
          (true :: s0) s1 (List.replicate k true) cStk s4 (true :: s5) s6 emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl5)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        cond_true, upd_tr2, upd_tr0, upd_tr5]
      rfl
    have htr := (RIn.single h1).trans (ih (true :: s0) (true :: s5))
    rw [replicate_append_cons, replicate_append_cons] at htr
    rw [List.replicate_succ]
    exact htr.mono (by omega)

private lemma tr_restoreN (tag : Bool) (s1 s2 cStk s4 s5 s6 : List Bool) (k : ℕ) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl6)) (M_U.initialState, M_V.initialState, tag, none)
        (List.replicate k true) s1 s2 cStk s4 s5 s6 emptyU emptyV)
      (some (trCfg (some (Sum.inl tl4)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 (List.replicate k true ++ s2) cStk s4 s5 s6 emptyU emptyV))
      (k + 1) := by
  induction k generalizing s2 with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl6)) _ _) = _
    simp only [trProg, List.replicate_zero, List.nil_append, TM2.stepAux, mkTRStk, List.head?_nil,
      List.tail_nil, Option.isSome, cond_false, upd_tr0]
    rfl
  | succ k ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl6)) (M_U.initialState, M_V.initialState, tag, none)
          (true :: List.replicate k true) s1 s2 cStk s4 s5 s6 emptyU emptyV) =
        some (trCfg (some (Sum.inl tl6)) (M_U.initialState, M_V.initialState, tag, none)
          (List.replicate k true) s1 (true :: s2) cStk s4 s5 s6 emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl6)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        cond_true, upd_tr0, upd_tr2]
      rfl
    have htr := (RIn.single h1).trans (ih (true :: s2))
    rw [replicate_append_cons] at htr
    rw [List.replicate_succ]
    exact htr.mono (by omega)

private lemma tr_mulLoop (tag : Bool) (s1 cStk s5 s6 : List Bool) (n acc : ℕ) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl4)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 (List.replicate n true) cStk (List.replicate acc true) s5 s6 emptyU emptyV)
      (some (trCfg (some (Sum.inl tl7)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 (List.replicate n true) cStk [] (List.replicate (n * acc) true ++ s5) s6 emptyU emptyV))
      (acc * (2 * n + 3) + 1) := by
  induction acc generalizing s5 with
  | zero =>
    simp only [List.replicate_zero, Nat.mul_zero, List.nil_append, Nat.zero_mul, Nat.zero_add]
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl4)) _ _) = _
    simp only [trProg, TM2.stepAux, mkTRStk, List.head?_nil, List.tail_nil, Option.isSome,
      cond_false, upd_tr4]
    rfl
  | succ acc ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl4)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 (List.replicate n true) cStk (true :: List.replicate acc true) s5 s6 emptyU emptyV) =
        some (trCfg (some (Sum.inl tl5)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 (List.replicate n true) cStk (List.replicate acc true) s5 s6 emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl4)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        cond_true, upd_tr4]
      rfl
    have hcopy := tr_copyN (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
      (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) tag [] s1 cStk (List.replicate acc true) s5 s6 n
    rw [List.append_nil] at hcopy
    have hrest := tr_restoreN (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
      (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) tag s1 [] cStk (List.replicate acc true)
      (List.replicate n true ++ s5) s6 n
    rw [List.append_nil] at hrest
    have hfull := (((RIn.single h1).trans hcopy).trans hrest).trans
      (ih (List.replicate n true ++ s5))
    rw [List.replicate_succ]
    have hrep_mul : List.replicate (n * acc) true ++ (List.replicate n true ++ s5) =
        List.replicate (n * (acc + 1)) true ++ s5 := by
      rw [← List.append_assoc, ← List.replicate_add, Nat.mul_succ, Nat.add_comm]
    rw [hrep_mul] at hfull
    refine hfull.mono ?_
    have hring : 1 + (n + 1) + (n + 1) + (acc * (2 * n + 3) + 1) =
        (acc + 1) * (2 * n + 3) + 1 := by ring
    omega

private lemma tr_move5to4 (tag : Bool) (s1 s2 cStk s4 s6 : List Bool) (k : ℕ) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl7)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 s2 cStk s4 (List.replicate k true) s6 emptyU emptyV)
      (some (trCfg (some (Sum.inl tl8)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 s2 cStk (List.replicate k true ++ s4) [] s6 emptyU emptyV))
      (k + 1) := by
  induction k generalizing s4 with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl7)) _ _) = _
    simp only [trProg, List.replicate_zero, List.nil_append, TM2.stepAux, mkTRStk, List.head?_nil,
      List.tail_nil, Option.isSome, cond_false, upd_tr5]
    rfl
  | succ k ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl7)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 s2 cStk s4 (true :: List.replicate k true) s6 emptyU emptyV) =
        some (trCfg (some (Sum.inl tl7)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 s2 cStk (true :: s4) (List.replicate k true) s6 emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl7)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        cond_true, upd_tr5, upd_tr4]
      rfl
    have htr := (RIn.single h1).trans (ih (true :: s4))
    rw [replicate_append_cons] at htr
    rw [List.replicate_succ]
    exact htr.mono (by omega)

private lemma tr_addCoeff (tag : Bool) (s1 s2 restC s4 s6 : List Bool) (c : ℕ) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl8)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 s2 (List.replicate c true ++ false :: restC) s4 [] s6 emptyU emptyV)
      (some (trCfg (some (Sum.inl tl3)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 s2 restC (List.replicate c true ++ s4) [] s6 emptyU emptyV))
      (c + 1) := by
  induction c generalizing s4 with
  | zero =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl8)) _ _) = _
    simp only [trProg, List.replicate_zero, List.nil_append, TM2.stepAux, mkTRStk, List.head?_cons,
      List.tail_cons, Option.getD, cond_false, upd_tr3]
    rfl
  | succ c ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl8)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 s2 (true :: (List.replicate c true ++ false :: restC)) s4 [] s6 emptyU emptyV) =
        some (trCfg (some (Sum.inl tl8)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 s2 (List.replicate c true ++ false :: restC) (true :: s4) [] s6 emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl8)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.getD,
        cond_true, upd_tr3, upd_tr4]
      rfl
    have htr := (RIn.single h1).trans (ih (true :: s4))
    rw [replicate_append_cons] at htr
    rw [List.replicate_succ, List.cons_append]
    exact htr.mono (by omega)

private lemma tr_hornerRun (tag : Bool) (s1 s6 : List Bool) (n : ℕ) :
    ∀ (cs : List ℕ) (accP : Polynomial ℕ),
      RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl3)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 (List.replicate n true) (encodeCoeffs cs)
          (List.replicate (accP.eval n) true) [] s6 emptyU emptyV)
        (some (trCfg (some (Sum.inl tl9)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 (List.replicate n true) []
          (List.replicate (hornerAcc cs n (accP.eval n)) true) [] s6 emptyU emptyV))
        ((hornerTotalPoly cs accP).eval n)
  | [], accP => by
    simp only [encodeCoeffs, List.map_nil, List.flatten_nil, hornerAcc, hornerTotalPoly,
      Polynomial.eval_one]
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl3)) _ _) = _
    simp only [trProg, TM2.stepAux, mkTRStk, List.head?_nil, Option.isSome, cond_false]
    rfl
  | c :: cs, accP => by
    have hc_eq : encodeCoeffs (c :: cs) =
        List.replicate c true ++ false :: encodeCoeffs cs := by
      simp [encodeCoeffs, List.append_assoc]
    have hpeek : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl3)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 (List.replicate n true) (encodeCoeffs (c :: cs))
          (List.replicate (accP.eval n) true) [] s6 emptyU emptyV) =
        some (trCfg (some (Sum.inl tl4)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 (List.replicate n true) (encodeCoeffs (c :: cs))
          (List.replicate (accP.eval n) true) [] s6 emptyU emptyV) := by
      rw [hc_eq]
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl3)) _ _) = _
      cases c <;> {
        simp only [trProg, List.replicate_zero, List.replicate_succ, List.nil_append,
          List.cons_append, TM2.stepAux, mkTRStk, List.head?_cons, Option.isSome, cond_true]
        rfl
      }
    have hmul := tr_mulLoop (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
      (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) tag s1 (encodeCoeffs (c :: cs)) [] s6 n
      (accP.eval n)
    rw [List.append_nil] at hmul
    have hmv := tr_move5to4 (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
      (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) tag s1 (List.replicate n true)
      (encodeCoeffs (c :: cs)) [] s6 (n * accP.eval n)
    rw [List.append_nil] at hmv
    have hadd := tr_addCoeff (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
      (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) tag s1 (List.replicate n true)
      (encodeCoeffs cs) (List.replicate (n * accP.eval n) true) s6 c
    rw [← hc_eq, ← List.replicate_add, Nat.add_comm c _] at hadd
    let accP' := Polynomial.X * accP + Polynomial.C c
    have heval' : accP'.eval n = n * accP.eval n + c := by simp [accP']
    rw [← heval'] at hadd
    have hih := tr_hornerRun tag s1 s6 n cs accP'
    have htot := ((((RIn.single hpeek).trans hmul).trans hmv).trans hadd).trans hih
    rw [heval'] at htot
    dsimp only [accP'] at htot
    refine htot.mono ?_
    simp only [hornerTotalPoly, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
    have hring : 1 + (accP.eval n * (2 * n + 3) + 1) + (n * accP.eval n + 1) + (c + 1) =
        accP.eval n * (3 * n + 3) + (c + 4) := by ring
    have hmono_mul : accP.eval n * (3 * n + 3) ≤ accP.eval n * (3 * n + 4) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

private lemma tr_drainN (tag : Bool) (s1 s2 s4 s6 : List Bool) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl9)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 s2 [] s4 [] s6 emptyU emptyV)
      (some (trCfg (some (Sum.inl tl10)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 [] [] s4 [] s6 emptyU emptyV))
      (s2.length + 1) := by
  induction s2 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl9)) _ _) = _
    simp only [trProg, TM2.stepAux, mkTRStk, List.head?_nil, List.tail_nil, Option.isSome,
      cond_false, upd_tr2]
    rfl
  | cons b s2 ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl9)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 (b :: s2) [] s4 [] s6 emptyU emptyV) =
        some (trCfg (some (Sum.inl tl9)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 s2 [] s4 [] s6 emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl9)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        cond_true, upd_tr2]
      rfl
    exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)

private lemma tr_checkLen_ok (tag : Bool) (s1 : List Bool) :
    ∀ (xs acc2 : List Bool) (rem : ℕ),
      xs.length ≤ rem →
      RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl10)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 acc2 [] (List.replicate rem true) [] xs emptyU emptyV)
        (some (trCfg (some (Sum.inl tl11)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 (xs.reverse ++ acc2) [] (List.replicate (rem - xs.length) true) [] [] emptyU emptyV))
        (xs.length + 1)
  | [], acc2, rem, _ => by
    simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.sub_zero]
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl10)) _ _) = _
    simp only [trProg, TM2.stepAux, mkTRStk, List.head?_nil, List.tail_nil, Option.isSome,
      cond_false, upd_tr6]
    rfl
  | b :: xs, acc2, 0, hle => by simp at hle
  | b :: xs, acc2, rem + 1, hle => by
    have hle' : xs.length ≤ rem := by simp at hle; omega
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl10)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 acc2 [] (true :: List.replicate rem true) [] (b :: xs) emptyU emptyV) =
        some (trCfg (some (Sum.inl tl10)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 (b :: acc2) [] (List.replicate rem true) [] xs emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl10)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        Option.getD, cond_true, upd_tr6, upd_tr2, upd_tr4]
      rfl
    have htr := (RIn.single h1).trans (tr_checkLen_ok tag s1 xs (b :: acc2) rem hle')
    rw [List.replicate_succ]
    have hrev : xs.reverse ++ b :: acc2 = (b :: xs).reverse ++ acc2 := by
      simp [List.reverse_cons, List.append_assoc]
    have hsub : rem - xs.length = (rem + 1) - (b :: xs).length := by simp
    rw [hrev, hsub] at htr
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma tr_checkLen_fail (tag : Bool) (s1 : List Bool) :
    ∀ (rem : ℕ) (xs acc2 : List Bool),
      rem < xs.length →
      ∃ s2' s6',
        s2'.length + s6'.length = acc2.length + xs.length ∧
        RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
          (trCfg (some (Sum.inl tl10)) (M_U.initialState, M_V.initialState, tag, none)
            [] s1 acc2 [] (List.replicate rem true) [] xs emptyU emptyV)
          (some (trCfg (some (Sum.inl tl19)) (trInitVar M_U M_V)
            [] s1 s2' [] [] [] s6' emptyU emptyV))
          (xs.length + 1)
  | _, [], _, hlt => by simp at hlt
  | 0, b :: xs, acc2, _ => by
    refine ⟨b :: acc2, xs, by simp; omega, ?_⟩
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl10)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 acc2 [] [] [] (b :: xs) emptyU emptyV) =
        some (trCfg (some (Sum.inl tl19)) (trInitVar M_U M_V)
          [] s1 (b :: acc2) [] [] [] xs emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl10)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, List.head?_nil,
        List.tail_nil, Option.isSome, Option.getD, cond_true, cond_false, upd_tr6, upd_tr2, upd_tr4]
      rfl
    exact (RIn.single h1).mono (by simp)
  | rem + 1, b :: xs, acc2, hlt => by
    have hlt' : rem < xs.length := by simp at hlt; omega
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl10)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 acc2 [] (true :: List.replicate rem true) [] (b :: xs) emptyU emptyV) =
        some (trCfg (some (Sum.inl tl10)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 (b :: acc2) [] (List.replicate rem true) [] xs emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl10)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        Option.getD, cond_true, upd_tr6, upd_tr2, upd_tr4]
      rfl
    obtain ⟨s2', s6', hlen, hrest⟩ := tr_checkLen_fail tag s1 rem xs (b :: acc2) hlt'
    rw [List.replicate_succ]
    refine ⟨s2', s6', by simp at hlen ⊢; omega, ((RIn.single h1).trans hrest).mono ?_⟩
    simp only [List.length_cons]; omega

private lemma tr_drain4 (tag : Bool) (s1 s2 s4 : List Bool) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl11)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 s2 [] s4 [] [] emptyU emptyV)
      (some (trCfg (some (Sum.inl tl12)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 s2 [] [] [] [] emptyU emptyV))
      (s4.length + 1) := by
  induction s4 with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl11)) _ _) = _
    simp only [trProg, TM2.stepAux, mkTRStk, List.head?_nil, List.tail_nil, Option.isSome,
      cond_false, upd_tr4]
    rfl
  | cons b s4 ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl11)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 s2 [] (b :: s4) [] [] emptyU emptyV) =
        some (trCfg (some (Sum.inl tl11)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 s2 [] s4 [] [] emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl11)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        cond_true, upd_tr4]
      rfl
    exact ((RIn.single h1).trans ih).mono (by simp only [List.length_cons]; omega)

private lemma tr_rev2to6 (tag : Bool) (s1 s2 acc6 : List Bool) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl12)) (M_U.initialState, M_V.initialState, tag, none)
        [] s1 s2 [] [] [] acc6 emptyU emptyV)
      (some (trCfg (some (Sum.inl (if tag then tl13 else tl16))) (trInitVar M_U M_V)
        [] s1 [] [] [] [] (s2.reverse ++ acc6) emptyU emptyV))
      (s2.length + 1) := by
  induction s2 generalizing acc6 with
  | nil =>
    cases tag <;> {
      refine RIn.single ?_
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl12)) _ _) = _
      simp only [trProg, List.reverse_nil, List.nil_append, TM2.stepAux, mkTRStk, List.head?_nil,
        List.tail_nil, Option.isSome, cond_false, cond_true, upd_tr2]
      rfl
    }
  | cons b s2 ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl12)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 (b :: s2) [] [] [] acc6 emptyU emptyV) =
        some (trCfg (some (Sum.inl tl12)) (M_U.initialState, M_V.initialState, tag, none)
          [] s1 s2 [] [] [] (b :: acc6) emptyU emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl12)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        Option.getD, cond_true, upd_tr2, upd_tr6]
      rfl
    have htr := (RIn.single h1).trans (ih (b :: acc6))
    have hrev : s2.reverse ++ b :: acc6 = (b :: s2).reverse ++ acc6 := by
      simp [List.reverse_cons, List.append_assoc]
    rw [hrev] at htr
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma tr_pushPayU (s1 payRev : List Bool) (accU : List (M_U.Γ M_U.k₀)) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl13)) (trInitVar M_U M_V)
        [] s1 [] [] [] [] payRev (Function.update emptyU M_U.k₀ accU) emptyV)
      (some (trCfg (some (Sum.inl tl14)) (trInitVar M_U M_V)
        [] s1 [] [] [] [] []
        (Function.update emptyU M_U.k₀
          (eIn_U.symm false :: ((bitEncode payRev.reverse).map eIn_U.symm ++ accU)))
        emptyV))
      (payRev.length + 1) := by
  induction payRev generalizing accU with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl13)) _ _) = _
    simp only [trProg, List.reverse_nil, bitEncode_list_nil, List.map_nil, List.nil_append,
      TM2.stepAux, mkTRStk, List.head?_nil, List.tail_nil, Option.isSome, cond_false,
      upd_tr6, upd_trU, Function.update_self, Function.update_idem]
    rfl
  | cons b pr ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl13)) (trInitVar M_U M_V)
          [] s1 [] [] [] [] (b :: pr) (Function.update emptyU M_U.k₀ accU) emptyV) =
        some (trCfg (some (Sum.inl tl13)) (trInitVar M_U M_V)
          [] s1 [] [] [] [] pr
          (Function.update emptyU M_U.k₀
            (eIn_U.symm true :: eIn_U.symm b :: eIn_U.symm false :: accU))
          emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl13)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        Option.getD, cond_true, upd_tr6, upd_trU, Function.update_self, Function.update_idem]
      rfl
    have htr := (RIn.single h1).trans
      (ih (eIn_U.symm true :: eIn_U.symm b :: eIn_U.symm false :: accU))
    have hbe : (bitEncode (b :: pr).reverse).map eIn_U.symm ++ accU =
        (bitEncode pr.reverse).map eIn_U.symm ++
          (eIn_U.symm true :: eIn_U.symm b :: eIn_U.symm false :: accU) := by
      rw [List.reverse_cons, bitEncode_list_append, List.map_append, List.append_assoc]
      rfl
    rw [← hbe] at htr
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma tr_pushZU (zRev : List Bool) (accU : List (M_U.Γ M_U.k₀)) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl14)) (trInitVar M_U M_V)
        [] zRev [] [] [] [] [] (Function.update emptyU M_U.k₀ accU) emptyV)
      (some (trCfg (some (Sum.inr (Sum.inl M_U.main))) (trInitVar M_U M_V)
        [] [] [] [] [] [] []
        (Function.update emptyU M_U.k₀
          (((bitEncode zRev.reverse).flatMap (fun b => [true, b])).map eIn_U.symm ++ accU))
        emptyV))
      (zRev.length + 1) := by
  induction zRev generalizing accU with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl14)) _ _) = _
    simp only [trProg, List.reverse_nil, bitEncode_list_nil, List.flatMap_nil, List.map_nil,
      List.nil_append, TM2.stepAux, mkTRStk, List.head?_nil, List.tail_nil, Option.isSome,
      cond_false, upd_tr1]
    rfl
  | cons b zr ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl14)) (trInitVar M_U M_V)
          [] (b :: zr) [] [] [] [] [] (Function.update emptyU M_U.k₀ accU) emptyV) =
        some (trCfg (some (Sum.inl tl14)) (trInitVar M_U M_V)
          [] zr [] [] [] [] []
          (Function.update emptyU M_U.k₀
            (eIn_U.symm true :: eIn_U.symm true :: eIn_U.symm true ::
              eIn_U.symm b :: eIn_U.symm true :: eIn_U.symm false :: accU))
          emptyV) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl14)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        Option.getD, cond_true, upd_tr1, upd_trU, Function.update_self, Function.update_idem]
      rfl
    have htr := (RIn.single h1).trans
      (ih (eIn_U.symm true :: eIn_U.symm true :: eIn_U.symm true ::
            eIn_U.symm b :: eIn_U.symm true :: eIn_U.symm false :: accU))
    have hbe : (((bitEncode (b :: zr).reverse).flatMap (fun c => [true, c])).map eIn_U.symm) ++ accU =
        (((bitEncode zr.reverse).flatMap (fun c => [true, c])).map eIn_U.symm) ++
          (eIn_U.symm true :: eIn_U.symm true :: eIn_U.symm true ::
            eIn_U.symm b :: eIn_U.symm true :: eIn_U.symm false :: accU) := by
      rw [List.reverse_cons, bitEncode_list_append, List.flatMap_append, List.map_append,
        List.append_assoc]
      rfl
    rw [← hbe] at htr
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma tr_pushPayV (s1 payRev : List Bool) (accV : List (M_V.Γ M_V.k₀)) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl16)) (trInitVar M_U M_V)
        [] s1 [] [] [] [] payRev emptyU (Function.update emptyV M_V.k₀ accV))
      (some (trCfg (some (Sum.inl tl17)) (trInitVar M_U M_V)
        [] s1 [] [] [] [] [] emptyU
        (Function.update emptyV M_V.k₀
          (eIn_V.symm false :: ((bitEncode payRev.reverse).map eIn_V.symm ++ accV)))))
      (payRev.length + 1) := by
  induction payRev generalizing accV with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl16)) _ _) = _
    simp only [trProg, List.reverse_nil, bitEncode_list_nil, List.map_nil, List.nil_append,
      TM2.stepAux, mkTRStk, List.head?_nil, List.tail_nil, Option.isSome, cond_false,
      upd_tr6, upd_trV, Function.update_self, Function.update_idem]
    rfl
  | cons b pr ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl16)) (trInitVar M_U M_V)
          [] s1 [] [] [] [] (b :: pr) emptyU (Function.update emptyV M_V.k₀ accV)) =
        some (trCfg (some (Sum.inl tl16)) (trInitVar M_U M_V)
          [] s1 [] [] [] [] pr emptyU
          (Function.update emptyV M_V.k₀
            (eIn_V.symm true :: eIn_V.symm b :: eIn_V.symm false :: accV))) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl16)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        Option.getD, cond_true, upd_tr6, upd_trV, Function.update_self, Function.update_idem]
      rfl
    have htr := (RIn.single h1).trans
      (ih (eIn_V.symm true :: eIn_V.symm b :: eIn_V.symm false :: accV))
    have hbe : (bitEncode (b :: pr).reverse).map eIn_V.symm ++ accV =
        (bitEncode pr.reverse).map eIn_V.symm ++
          (eIn_V.symm true :: eIn_V.symm b :: eIn_V.symm false :: accV) := by
      rw [List.reverse_cons, bitEncode_list_append, List.map_append, List.append_assoc]
      rfl
    rw [← hbe] at htr
    exact htr.mono (by simp only [List.length_cons]; omega)

private lemma tr_pushZV (zRev : List Bool) (accV : List (M_V.Γ M_V.k₀)) :
    RIn (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
      (trCfg (some (Sum.inl tl17)) (trInitVar M_U M_V)
        [] zRev [] [] [] [] [] emptyU (Function.update emptyV M_V.k₀ accV))
      (some (trCfg (some (Sum.inr (Sum.inr M_V.main))) (trInitVar M_U M_V)
        [] [] [] [] [] [] [] emptyU
        (Function.update emptyV M_V.k₀
          (((bitEncode zRev.reverse).flatMap (fun b => [true, b])).map eIn_V.symm ++ accV))))
      (zRev.length + 1) := by
  induction zRev generalizing accV with
  | nil =>
    refine RIn.single ?_
    change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl17)) _ _) = _
    simp only [trProg, List.reverse_nil, bitEncode_list_nil, List.flatMap_nil, List.map_nil,
      List.nil_append, TM2.stepAux, mkTRStk, List.head?_nil, List.tail_nil, Option.isSome,
      cond_false, upd_tr1]
    rfl
  | cons b zr ih =>
    have h1 : (trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q).step
        (trCfg (some (Sum.inl tl17)) (trInitVar M_U M_V)
          [] (b :: zr) [] [] [] [] [] emptyU (Function.update emptyV M_V.k₀ accV)) =
        some (trCfg (some (Sum.inl tl17)) (trInitVar M_U M_V)
          [] zr [] [] [] [] [] emptyU
          (Function.update emptyV M_V.k₀
            (eIn_V.symm true :: eIn_V.symm true :: eIn_V.symm true ::
              eIn_V.symm b :: eIn_V.symm true :: eIn_V.symm false :: accV))) := by
      change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl17)) _ _) = _
      simp only [trProg, TM2.stepAux, mkTRStk, List.head?_cons, List.tail_cons, Option.isSome,
        Option.getD, cond_true, upd_tr1, upd_trV, Function.update_self, Function.update_idem]
      rfl
    have htr := (RIn.single h1).trans
      (ih (eIn_V.symm true :: eIn_V.symm true :: eIn_V.symm true ::
            eIn_V.symm b :: eIn_V.symm true :: eIn_V.symm false :: accV))
    have hbe : (((bitEncode (b :: zr).reverse).flatMap (fun c => [true, c])).map eIn_V.symm) ++ accV =
        (((bitEncode zr.reverse).flatMap (fun c => [true, c])).map eIn_V.symm) ++
          (eIn_V.symm true :: eIn_V.symm true :: eIn_V.symm true ::
            eIn_V.symm b :: eIn_V.symm true :: eIn_V.symm false :: accV) := by
      rw [List.reverse_cons, bitEncode_list_append, List.flatMap_append, List.map_append,
        List.append_assoc]
      rfl
    rw [← hbe] at htr
    exact htr.mono (by simp only [List.length_cons]; omega)

end TRMachine

theorem isPolyTime_trRel {U V_no : List Bool × List Bool → Bool}
    (hU : IsPolyTime U) (hV : IsPolyTime V_no) (q : Polynomial ℕ) :
    IsPolyTime (trRel U V_no q) := by
  obtain ⟨DU⟩ := hU
  obtain ⟨DV⟩ := hV
  let M_U := DU.tm
  let M_V := DV.tm
  let eIn_U := DU.inputAlphabet
  let eOut_U := DU.outputAlphabet
  let eIn_V := DV.inputAlphabet
  let eOut_V := DV.outputAlphabet
  let TM := trTM M_U M_V eIn_U eOut_U eIn_V eOut_V q
  let timePoly : Polynomial ℕ :=
    Polynomial.C 10 * Polynomial.X + Polynomial.C 30 +
      hornerTotalPoly (polyCoeffsRev Polynomial.X) 0 +
      hornerTotalPoly (polyCoeffsRev q) 0 + q + DU.time + DV.time
  have hout : ∀ zw : List Bool × List Bool,
      Nonempty (TM2OutputsInTime TM
        (List.map (Equiv.refl Bool).invFun (bitEncode zw))
        (some (List.map (Equiv.refl Bool).invFun (bitEncode (trRel U V_no q zw))))
        (timePoly.eval (bitEncode zw).length)) := by
    rintro ⟨z, w⟩
    have hinit : initList TM (bitEncode (z, w)) =
        trCfg (eIn_U := eIn_U) (eOut_U := eOut_U) (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q)
          (some (Sum.inl tl0)) (trInitVar M_U M_V)
          (delimit (bitEncode z) ++ bitEncode w) [] [] [] [] [] [] emptyU emptyV := by
      dsimp [initList, TM, trTM, trCfg, bitEncode_pair]
      congr 1; funext k
      rcases k with i | kU | kV
      · fin_cases i <;> rfl
      · rfl
      · rfl
    have s_uz := tr_unpackZ (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
      (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) z (bitEncode w) [] []
    simp only [List.append_nil] at s_uz
    have hrun_all : RIn TM.step (initList TM (bitEncode (z, w)))
        (some (haltList TM [trRel U V_no q (z, w)]))
        (timePoly.eval (bitEncode (z, w)).length) := by
      rw [hinit]
      cases w with
      | nil =>
        have h1 : TM.step
            (trCfg (some (Sum.inl tl1)) (trInitVar M_U M_V)
              (bitEncode ([] : List Bool)) z.reverse (List.replicate z.length true)
              [] [] [] [] emptyU emptyV) =
            some (trCfg (some (Sum.inl tl19)) (trInitVar M_U M_V)
              [] z.reverse (List.replicate z.length true) [] [] [] [] emptyU emptyV) := by
          change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl1)) _ _) = _
          simp only [trProg, bitEncode_list_nil, TM2.stepAux, mkTRStk, List.head?_nil,
            List.tail_nil, Option.isSome, cond_false, upd_tr0]
          rfl
        have sab19 := tr_abort19 (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
          (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) z.reverse (List.replicate z.length true) []
        rw [List.length_reverse] at sab19
        have sab20 := tr_abort20 (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
          (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) (List.replicate z.length true) []
        simp only [List.length_replicate, List.length_nil] at sab20
        have hc := ((s_uz.trans (RIn.single h1)).trans sab19).trans sab20
        dsimp only [trRel]
        refine hc.mono ?_
        simp only [timePoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_C, length_bitEncode_pair, List.length_nil]
        omega
      | cons tag payload =>
        have h1 : TM.step
            (trCfg (some (Sum.inl tl1)) (trInitVar M_U M_V)
              (bitEncode (tag :: payload)) z.reverse (List.replicate z.length true)
              [] [] [] [] emptyU emptyV) =
            some (trCfg (some (Sum.inl tl2)) (M_U.initialState, M_V.initialState, tag, none)
              (bitEncode payload) z.reverse (List.replicate z.length true)
              [] [] [] [] emptyU emptyV) := by
          change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl1)) _ _) = _
          simp only [trProg, bitEncode_list_cons, TM2.stepAux, mkTRStk, List.head?_cons,
            List.tail_cons, Option.isSome, Option.getD, cond_true, upd_tr0]
          rfl
        have s_up := tr_unpackPay (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
          (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) tag payload z.reverse
          (List.replicate z.length true) []
        rw [List.append_nil] at s_up
        let B_poly : Polynomial ℕ := if tag then Polynomial.X else q
        have s_hr := tr_hornerRun (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
          (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) tag z.reverse payload.reverse z.length
          (polyCoeffsRev B_poly) 0
        simp only [Polynomial.eval_zero, List.replicate_zero, hornerAcc_polyCoeffsRev] at s_hr
        have s_dn := tr_drainN (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
          (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) tag z.reverse
          (List.replicate z.length true) (List.replicate (B_poly.eval z.length) true) payload.reverse
        rw [List.length_replicate] at s_dn
        have spre := (((s_uz.trans (RIn.single h1)).trans s_up).trans s_hr).trans s_dn
        let N_in := (bitEncode (z, tag :: payload)).length
        have hz_le : z.length ≤ N_in := by
          dsimp [N_in]; rw [length_bitEncode_pair, List.length_cons]; omega
        have hpay_le : payload.length ≤ N_in := by
          dsimp [N_in]; rw [length_bitEncode_pair, List.length_cons]; omega
        have hpair_le : (bitEncode (z, payload)).length ≤ N_in := by
          dsimp [N_in]; rw [length_bitEncode_pair, length_bitEncode_pair, List.length_cons]; omega
        have hm_hx := poly_eval_mono (hornerTotalPoly (polyCoeffsRev Polynomial.X) 0) hz_le
        have hm_hq := poly_eval_mono (hornerTotalPoly (polyCoeffsRev q) 0) hz_le
        have hm_q := poly_eval_mono q hz_le
        have hm_U := poly_eval_mono DU.time hpair_le
        have hm_V := poly_eval_mono DV.time hpair_le
        have hB_hr_le : (hornerTotalPoly (polyCoeffsRev B_poly) 0).eval z.length ≤
            (hornerTotalPoly (polyCoeffsRev Polynomial.X) 0).eval N_in +
              (hornerTotalPoly (polyCoeffsRev q) 0).eval N_in := by
          cases tag
          · change (hornerTotalPoly (polyCoeffsRev q) 0).eval z.length ≤ _; omega
          · change (hornerTotalPoly (polyCoeffsRev Polynomial.X) 0).eval z.length ≤ _; omega
        by_cases hlen_ok : payload.length ≤ B_poly.eval z.length
        · have hpr_ok : payload.reverse.length ≤ B_poly.eval z.length := by
            rwa [List.length_reverse]
          have s_chk := tr_checkLen_ok (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
            (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) tag z.reverse payload.reverse []
            (B_poly.eval z.length) hpr_ok
          rw [List.reverse_reverse, List.append_nil, List.length_reverse] at s_chk
          have s_d4 := tr_drain4 (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
            (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) tag z.reverse payload
            (List.replicate (B_poly.eval z.length - payload.length) true)
          rw [List.length_replicate] at s_d4
          have s_r26 := tr_rev2to6 (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
            (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) tag z.reverse payload []
          rw [List.append_nil] at s_r26
          have smid := ((spre.trans s_chk).trans s_d4).trans s_r26
          have hB_val_le : B_poly.eval z.length ≤ N_in + q.eval N_in := by
            cases tag
            · dsimp [B_poly]; omega
            · dsimp [B_poly]; rw [Polynomial.eval_X]; omega
          cases tag with
          | true =>
            have hlen_z : payload.length ≤ z.length := by
              simpa [B_poly] using hlen_ok
            have htr_val : trRel U V_no q (z, true :: payload) = U (z, payload) := by
              simp [trRel, hlen_z]
            rw [htr_val]
            have hemp_u : emptyU (M_U := M_U) = Function.update emptyU M_U.k₀ [] := by
              funext k; by_cases hk : k = M_U.k₀
              · subst hk; simp [emptyU]
              · simp [emptyU, hk]
            have s_pu := tr_pushPayU (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
              (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) z.reverse payload.reverse []
            rw [ ← hemp_u, List.reverse_reverse, List.append_nil, List.length_reverse] at s_pu
            have s_zu := tr_pushZU (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
              (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) z.reverse
              (eIn_U.symm false :: (bitEncode payload).map eIn_U.symm)
            rw [List.reverse_reverse, List.length_reverse] at s_zu
            have hinpU_eq : (((bitEncode z).flatMap (fun b => [true, b])).map eIn_U.symm ++
                (eIn_U.symm false :: (bitEncode payload).map eIn_U.symm)) =
                (bitEncode (z, payload)).map eIn_U.invFun := by
              rw [bitEncode_pair, delimit_eq_flatMap (bitEncode z), List.append_assoc,
                List.singleton_append, List.map_append, List.map_cons]
              rfl
            have hstk_initU : Function.update (emptyU (M_U := M_U)) M_U.k₀
                ((bitEncode (z, payload)).map eIn_U.invFun) =
                (initList M_U ((bitEncode (z, payload)).map eIn_U.invFun)).stk := by
              funext k; by_cases hk : k = M_U.k₀
              · subst hk; simp [initList]
              · simp [initList, hk, emptyU]
            rw [hinpU_eq, hstk_initU] at s_zu
            rcases DU.outputsFun (z, payload) with ⟨⟨nU, hevalU⟩, hnU_le⟩
            change nU ≤ DU.time.eval (bitEncode (z, payload)).length at hnU_le
            have hsimU := sim_MU (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
              (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) nU
              (initList M_U ((bitEncode (z, payload)).map eIn_U.invFun))
              (haltList M_U ((bitEncode (U (z, payload))).map eOut_U.invFun)) hevalU
            have hstep15 : TM.step (embedU (eIn_U := eIn_U) (eOut_U := eOut_U) (eIn_V := eIn_V)
                (eOut_V := eOut_V) (q := q)
                (haltList M_U ((bitEncode (U (z, payload))).map eOut_U.invFun))) =
                some (haltList TM [U (z, payload)]) := by
              change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl15)) _ _) = _
              have hhk1 : (haltList M_U [eOut_U.symm (U (z, payload))]).stk M_U.k₁ =
                  [eOut_U.symm (U (z, payload))] := by simp [haltList]
              have hupd_emp : Function.update
                  (haltList M_U [eOut_U.symm (U (z, payload))]).stk M_U.k₁ [] = emptyU := by
                funext k; by_cases hk : k = M_U.k₁
                · subst hk; simp [emptyU]
                · simp [haltList, hk, emptyU]
              dsimp only [embedU, bitEncode_bool, List.map, Equiv.invFun_as_coe]
              simp only [trProg, TM2.stepAux, mkTRStk, hhk1, List.head?_cons, List.tail_cons,
                Option.map_some, Equiv.apply_symm_apply, Option.getD_some, upd_trU, hupd_emp,
                upd_tr0]
              exact congr_arg some (mkTRStk_halt (U (z, payload)))
            have s_all := (((smid.trans s_pu).trans s_zu).trans hsimU).trans (RIn.single hstep15)
            refine s_all.mono ?_
            dsimp only [N_in] at hz_le hpay_le hpair_le hm_hx hm_hq hm_q hm_U hm_V hB_hr_le hB_val_le
            simp only [timePoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
              Polynomial.eval_C]
            omega
          | false =>
            have hlen_q : payload.length ≤ q.eval z.length := by
              simpa [B_poly] using hlen_ok
            have htr_val : trRel U V_no q (z, false :: payload) = V_no (z, payload) := by
              simp [trRel, hlen_q]
            rw [htr_val]
            have hemp_v : emptyV (M_V := M_V) = Function.update emptyV M_V.k₀ [] := by
              funext k; by_cases hk : k = M_V.k₀
              · subst hk; simp [emptyV]
              · simp [emptyV, hk]
            have s_pv := tr_pushPayV (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
              (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) z.reverse payload.reverse []
            rw [← hemp_v, List.reverse_reverse, List.append_nil, List.length_reverse] at s_pv
            have s_zv := tr_pushZV (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
              (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) z.reverse
              (eIn_V.symm false :: (bitEncode payload).map eIn_V.symm)
            rw [List.reverse_reverse, List.length_reverse] at s_zv
            have hinpV_eq : (((bitEncode z).flatMap (fun b => [true, b])).map eIn_V.symm ++
                (eIn_V.symm false :: (bitEncode payload).map eIn_V.symm)) =
                (bitEncode (z, payload)).map eIn_V.invFun := by
              rw [bitEncode_pair, delimit_eq_flatMap (bitEncode z), List.append_assoc,
                List.singleton_append, List.map_append, List.map_cons]
              rfl
            have hstk_initV : Function.update (emptyV (M_V := M_V)) M_V.k₀
                ((bitEncode (z, payload)).map eIn_V.invFun) =
                (initList M_V ((bitEncode (z, payload)).map eIn_V.invFun)).stk := by
              funext k; by_cases hk : k = M_V.k₀
              · subst hk; simp [initList]
              · simp [initList, hk, emptyV]
            rw [hinpV_eq, hstk_initV] at s_zv
            rcases DV.outputsFun (z, payload) with ⟨⟨nV, hevalV⟩, hnV_le⟩
            change nV ≤ DV.time.eval (bitEncode (z, payload)).length at hnV_le
            have hsimV := sim_MV (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
              (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) nV
              (initList M_V ((bitEncode (z, payload)).map eIn_V.invFun))
              (haltList M_V ((bitEncode (V_no (z, payload))).map eOut_V.invFun)) hevalV
            have hstep18 : TM.step (embedV (eIn_U := eIn_U) (eOut_U := eOut_U) (eIn_V := eIn_V)
                (eOut_V := eOut_V) (q := q)
                (haltList M_V ((bitEncode (V_no (z, payload))).map eOut_V.invFun))) =
                some (haltList TM [V_no (z, payload)]) := by
              change some (TM2.stepAux (trProg M_U M_V eIn_U eOut_U eIn_V eOut_V q (Sum.inl tl18)) _ _) = _
              have hhk1 : (haltList M_V [eOut_V.symm (V_no (z, payload))]).stk M_V.k₁ =
                  [eOut_V.symm (V_no (z, payload))] := by simp [haltList]
              have hupd_emp : Function.update
                  (haltList M_V [eOut_V.symm (V_no (z, payload))]).stk M_V.k₁ [] = emptyV := by
                funext k; by_cases hk : k = M_V.k₁
                · subst hk; simp [emptyV]
                · simp [haltList, hk, emptyV]
              dsimp only [embedV, bitEncode_bool, List.map, Equiv.invFun_as_coe]
              simp only [trProg, TM2.stepAux, mkTRStk, hhk1, List.head?_cons, List.tail_cons,
                Option.map_some, Equiv.apply_symm_apply, Option.getD_some, upd_trV, hupd_emp,
                upd_tr0]
              exact congr_arg some (mkTRStk_halt (V_no (z, payload)))
            have s_all := (((smid.trans s_pv).trans s_zv).trans hsimV).trans (RIn.single hstep18)
            refine s_all.mono ?_
            dsimp only [N_in] at hz_le hpay_le hpair_le hm_hx hm_hq hm_q hm_U hm_V hB_hr_le hB_val_le
            simp only [timePoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
              Polynomial.eval_C]
            omega
        · have hlt : B_poly.eval z.length < payload.reverse.length := by
            rw [List.length_reverse]; omega
          obtain ⟨s2', s6', hlen26, s_fail⟩ := tr_checkLen_fail (M_U := M_U) (M_V := M_V)
            (eIn_U := eIn_U) (eOut_U := eOut_U) (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q)
            tag z.reverse (B_poly.eval z.length) payload.reverse [] hlt
          rw [List.length_nil, Nat.zero_add, List.length_reverse] at hlen26
          rw [List.length_reverse] at s_fail
          have sab19 := tr_abort19 (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
            (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) z.reverse s2' s6'
          rw [List.length_reverse] at sab19
          have sab20 := tr_abort20 (M_U := M_U) (M_V := M_V) (eIn_U := eIn_U) (eOut_U := eOut_U)
            (eIn_V := eIn_V) (eOut_V := eOut_V) (q := q) s2' s6'
          have htr_false : trRel U V_no q (z, tag :: payload) = false := by
            cases tag
            · have hnq : ¬ (payload.length ≤ q.eval z.length) := by simpa [B_poly] using hlen_ok
              simp [trRel, hnq]
            · have hnz : ¬ (payload.length ≤ z.length) := by simpa [B_poly] using hlen_ok
              simp [trRel, hnz]
          rw [htr_false]
          have s_all := ((spre.trans s_fail).trans sab19).trans sab20
          refine s_all.mono ?_
          dsimp only [N_in] at hz_le hpay_le hpair_le hm_hx hm_hq hm_q hm_U hm_V hB_hr_le
          simp only [timePoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
            Polynomial.eval_C]
          omega
    obtain ⟨steps, hsteps, heval⟩ := hrun_all
    have heval' : (flip bind TM.step)^[steps]
        (some (initList TM (List.map (Equiv.refl Bool).invFun (bitEncode (z, w))))) =
        Option.map (haltList TM)
          (some (List.map (Equiv.refl Bool).invFun (bitEncode (trRel U V_no q (z, w))))) :=
      ((congrArg (fun l : List Bool => (flip bind TM.step)^[steps] (some (initList TM l)))
        (List.map_id (bitEncode (z, w)))).trans heval).trans
        (congrArg (fun l : List Bool => some (haltList TM l))
          (List.map_id [trRel U V_no q (z, w)]).symm)
    exact ⟨⟨⟨steps, heval'⟩, hsteps⟩⟩
  exact ⟨{
    tm := TM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := timePoly
    outputsFun := fun zw => Classical.choice (hout zw)
  }⟩

end

end PudlakMod3B

namespace PudlakMod4

open Computability Turing BitstringEncoding ComplexityTheory PudlakFiniteDomain
open PudlakMod1 PudlakMod2 PudlakMod3 PudlakMod3B

noncomputable section

private def L_yes (z : List Bool) : Bool :=
  @decide (∃ y : List Bool, y.length ≤ z.length ∧ U (z, y) = true) (Classical.propDecidable _)

private lemma L_yes_mem_NP : L_yes ∈ NP := by
  refine ⟨Polynomial.X, U, isPolyTime_U, fun z => ?_⟩
  simp only [L_yes, decide_eq_true_eq, Polynomial.eval_X]

private lemma length_le_mkInstanceBits (progBits : List Bool) (p_m p_t : Polynomial ℕ)
    (x : List Bool) :
    p_m.eval x.length ≤ (mkInstanceBits progBits p_m p_t x).length := by
  dsimp [mkInstanceBits]
  simp only [List.length_append, length_delimit, List.length_replicate]
  omega

theorem exists_of_NP_eq_coNP_aux (h : NP = coNP) :
    ∃ T : TFNPProblem, T.IsComplete := by
  have hco : L_yes ∈ coNP := h ▸ L_yes_mem_NP
  obtain ⟨q, V_no, hV_no, hV_spec⟩ := hco
  let T : TFNPProblem := {
    R := trRel U V_no q
    p := Polynomial.C 1 + Polynomial.X + q
    polyTime := isPolyTime_trRel isPolyTime_U hV_no q
    total := fun z => by
      by_cases hLy : L_yes z = true
      · have hLy' : ∃ y : List Bool, y.length ≤ z.length ∧ U (z, y) = true := by
          simpa [L_yes] using hLy
        obtain ⟨y, hy_len, hy_U⟩ := hLy'
        refine ⟨true :: y, ?_, ?_⟩
        · simp only [List.length_cons, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
          omega
        · simp [trRel, hy_len, hy_U]
      · have hLyf : L_yes z = false := Bool.eq_false_iff.mpr hLy
        have hcomp : L_yesᶜ z = true := by simp [compl, hLyf]
        obtain ⟨w₀, hw₀_len, hw₀_V⟩ := (hV_spec z).mp hcomp
        refine ⟨false :: w₀, ?_, ?_⟩
        · simp only [List.length_cons, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
          omega
        · simp [trRel, hw₀_len, hw₀_V]
  }
  refine ⟨T, fun S => ?_⟩
  obtain ⟨DS⟩ := S.polyTime
  obtain ⟨prog, C_init, C_step, hcomp⟩ :=
    exists_compiled_flatProg DS.tm DS.inputAlphabet DS.outputAlphabet
  let B_poly : Polynomial ℕ :=
    Polynomial.C 6 * Polynomial.X + Polynomial.C 3 * S.p + Polynomial.C 1
  let p_t : Polynomial ℕ :=
    Polynomial.C C_init * (B_poly + Polynomial.C 1) +
      Polynomial.C C_step * (DS.time.comp B_poly + Polynomial.C 1)
  have hflat_eq : ∀ x y : List Bool, y.length ≤ S.p.eval x.length →
      flatEval prog (bitEncode (x, y)) (p_t.eval x.length) = S.R (x, y) := by
    intro x y hy_len
    have hinp_le : (bitEncode (x, y)).length ≤ B_poly.eval x.length := by
      rw [PudlakMod3B.length_bitEncode_pair]
      simp only [B_poly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      omega
    have htime_le : DS.time.eval (bitEncode (x, y)).length ≤
        (DS.time.comp B_poly).eval x.length := by
      rw [Polynomial.eval_comp]
      exact PudlakMod3B.poly_eval_mono DS.time hinp_le
    have hsteps_le : C_init * ((bitEncode (x, y)).length + 1) +
        C_step * (DS.time.eval (bitEncode (x, y)).length + 1) ≤ p_t.eval x.length := by
      simp only [p_t, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      have h1 : C_init * ((bitEncode (x, y)).length + 1) ≤ C_init * (B_poly.eval x.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 : C_step * (DS.time.eval (bitEncode (x, y)).length + 1) ≤
          C_step * ((DS.time.comp B_poly).eval x.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    exact hcomp (bitEncode (x, y)) (S.R (x, y)) (DS.time.eval (bitEncode (x, y)).length)
      (DS.outputsFun (x, y)) (p_t.eval x.length) hsteps_le
  refine ⟨mkInstanceBits (encodeProg prog) S.p p_t, fun p => p.2.tail,
    isPolyTime_mkInstanceBits (encodeProg prog) S.p p_t, isPolyTime_snd_tail, fun x w _ hw_R => ?_⟩
  have hLyes_fx : L_yes (mkInstanceBits (encodeProg prog) S.p p_t x) = true := by
    obtain ⟨y₀, hy₀_len, hy₀_R⟩ := S.total x
    simp only [L_yes, decide_eq_true_eq]
    refine ⟨y₀, hy₀_len.trans (length_le_mkInstanceBits (encodeProg prog) S.p p_t x), ?_⟩
    rw [U_mkInstanceBits]
    simp [hy₀_len, hflat_eq x y₀ hy₀_len, hy₀_R]
  cases w with
  | nil =>
    simp [T, trRel] at hw_R
  | cons tag payload =>
    cases tag with
    | false =>
      simp only [T, trRel, Bool.and_eq_true, decide_eq_true_eq] at hw_R
      have hcomp_fx : L_yesᶜ (mkInstanceBits (encodeProg prog) S.p p_t x) = true :=
        (hV_spec _).mpr ⟨payload, hw_R.1, hw_R.2⟩
      have hLyes_false : L_yes (mkInstanceBits (encodeProg prog) S.p p_t x) = false := by
        cases hly : L_yes (mkInstanceBits (encodeProg prog) S.p p_t x)
        · rfl
        · simp [compl, hly] at hcomp_fx
      rw [hLyes_fx] at hLyes_false
      cases hLyes_false
    | true =>
      simp only [T, trRel, Bool.and_eq_true, decide_eq_true_eq] at hw_R
      have hU : U (mkInstanceBits (encodeProg prog) S.p p_t x, payload) = true := hw_R.2
      rw [U_mkInstanceBits] at hU
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hU
      refine ⟨hU.1, ?_⟩
      dsimp only [List.tail_cons]
      rw [← hflat_eq x payload hU.1]
      exact hU.2

end

end PudlakMod4

theorem OMA.solution :
    type_of% @PudlakFiniteDomain.tfnp_no_complete_problem.variants.exists_of_NP_eq_coNP :=
  PudlakMod4.exists_of_NP_eq_coNP_aux
