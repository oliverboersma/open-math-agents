import OMAReductions.R_Erdos78_erdos_78_variants_cohen_R1
import Mathlib.Data.Num.Lemmas

/-!
Step `Erdos78.erdos_78.variants.cohen.R1.H2`: reading the unary list length and sorting two binary
vertex indices preserves polynomial-time computability under the canonical bitstring encodings.
-/

open Turing Computability ComplexityTheory

namespace OMA.Erdos78Adapter

/- Bounded-step reachability and polynomial monotonicity. -/

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

/- Binary arithmetic on `Computability.encodeNat`. -/

def succBits : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: succBits bs

lemma succBits_encodePosNum : ∀ p : PosNum, succBits (encodePosNum p) = encodePosNum p.succ
  | .one => rfl
  | .bit0 _ => rfl
  | .bit1 p => by simp [encodePosNum, PosNum.succ, succBits, succBits_encodePosNum p]

lemma succBits_encodeNum : ∀ m : Num, succBits (encodeNum m) = encodeNum m.succ
  | 0 => rfl
  | .pos p => succBits_encodePosNum p

lemma succBits_encodeNat (n : ℕ) : succBits (encodeNat n) = encodeNat (n + 1) := by
  unfold encodeNat
  rw [Nat.cast_succ, Num.add_one, succBits_encodeNum]

lemma length_succBits_le (bs : List Bool) : (succBits bs).length ≤ bs.length + 1 := by
  induction bs with
  | nil => simp [succBits]
  | cons b bs ih =>
    cases b <;> simp [succBits]
    omega

lemma length_encodeNat_le (n : ℕ) : (encodeNat n).length ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← succBits_encodeNat]
    exact (length_succBits_le _).trans (by omega)

def valBits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * valBits bs

lemma valBits_encodePosNum : ∀ p : PosNum, valBits (encodePosNum p) = (p : ℕ)
  | .one => rfl
  | .bit0 p => by
    simp only [encodePosNum, valBits, Bool.toNat_false, zero_add, valBits_encodePosNum p,
      PosNum.cast_bit0]
    omega
  | .bit1 p => by
    simp only [encodePosNum, valBits, Bool.toNat_true, valBits_encodePosNum p, PosNum.cast_bit1]
    omega

lemma valBits_encodeNum : ∀ m : Num, valBits (encodeNum m) = (m : ℕ)
  | 0 => rfl
  | .pos p => valBits_encodePosNum p

lemma valBits_encodeNat (n : ℕ) : valBits (encodeNat n) = n := by
  rw [encodeNat, valBits_encodeNum, Num.to_of_nat]

def stepCmp (le : Bool) (a b : Bool) : Bool :=
  if a == b then le else b

def cmpBits (le : Bool) : List Bool → List Bool → Bool
  | [], [] => le
  | a :: as, [] => cmpBits (stepCmp le a false) as []
  | [], b :: bs => cmpBits (stepCmp le false b) [] bs
  | a :: as, b :: bs => cmpBits (stepCmp le a b) as bs
termination_by x y => x.length + y.length

lemma stepCmp_spec {r s M : ℕ} (hr : r < M) (hs : s < M) (a b : Bool) :
    stepCmp (decide (r ≤ s)) a b = decide (r + M * a.toNat ≤ s + M * b.toNat) := by
  cases a <;> cases b <;> simp [stepCmp] <;> omega

lemma cmpBits_spec (x y : List Bool) (r s M : ℕ) (hr : r < M) (hs : s < M) :
    cmpBits (decide (r ≤ s)) x y = decide (r + M * valBits x ≤ s + M * valBits y) := by
  cases x with
  | nil =>
    cases y with
    | nil => simp [cmpBits, valBits]
    | cons b bs =>
      rw [cmpBits, stepCmp_spec hr hs false b]
      simp only [Bool.toNat_false, mul_zero, add_zero]
      rw [cmpBits_spec [] bs r (s + M * b.toNat) (2 * M)
        (by omega) (by cases b <;> simp <;> omega)]
      simp only [valBits, mul_zero, add_zero]
      congr 1
      ring_nf
  | cons a as =>
    cases y with
    | nil =>
      rw [cmpBits, stepCmp_spec hr hs a false]
      simp only [Bool.toNat_false, mul_zero, add_zero]
      rw [cmpBits_spec as [] (r + M * a.toNat) s (2 * M)
        (by cases a <;> simp <;> omega) (by omega)]
      simp only [valBits, mul_zero, add_zero]
      congr 1
      ring_nf
    | cons b bs =>
      rw [cmpBits, stepCmp_spec hr hs a b,
        cmpBits_spec as bs (r + M * a.toNat) (s + M * b.toNat) (2 * M)
          (by cases a <;> simp <;> omega) (by cases b <;> simp <;> omega)]
      simp only [valBits]
      congr 1
      ring_nf
termination_by x.length + y.length

lemma cmpBits_encodeNat (u v : ℕ) :
    cmpBits true (encodeNat u) (encodeNat v) = decide (u ≤ v) := by
  have h := cmpBits_spec (encodeNat u) (encodeNat v) 0 0 1 (by omega) (by omega)
  simpa [valBits_encodeNat] using h

/- Encoding structure of `List Bool`. -/

lemma delimit_bitEncode_cons (b : Bool) (s rest : List Bool) :
    BitstringEncoding.delimit (BitstringEncoding.bitEncode (b :: s)) ++ rest =
      true :: true :: true :: b :: true :: false ::
        (BitstringEncoding.delimit (BitstringEncoding.bitEncode s) ++ rest) := by
  rfl

lemma delimit_bitEncode_nil (rest : List Bool) :
    BitstringEncoding.delimit (BitstringEncoding.bitEncode ([] : List Bool)) ++ rest =
      false :: rest := by
  rfl

lemma length_bitEncode_list_bool (s : List Bool) :
    (BitstringEncoding.bitEncode s).length = 3 * s.length := by
  change (((s.map BitstringEncoding.bitEncode).map BitstringEncoding.delimit).flatten).length =
    3 * s.length
  induction s with
  | nil => rfl
  | cons b s ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rw [ih]
    have hb : (BitstringEncoding.delimit (BitstringEncoding.bitEncode b)).length = 3 := rfl
    rw [hb, List.length_cons]
    omega

/- Wrapper Turing Machine `N M e`. -/

inductive Aux
  | inp | cnt | cntTmp | xLsb | xRev | yRev
  deriving DecidableEq

instance : Fintype Aux :=
  ⟨{.inp, .cnt, .cntTmp, .xLsb, .xRev, .yRev}, by intro k; cases k <;> simp⟩

inductive Ph
  | countS
  | inc
  | incRestore
  | revCnt
  | parseX
  | unrevX
  | scanXY
  | emitMaxY
  | emitMinX
  | emitMaxX
  | emitMinY
  | emitLen
  deriving DecidableEq

instance : Fintype Ph :=
  ⟨{.countS, .inc, .incRestore, .revCnt, .parseX, .unrevX, .scanXY,
    .emitMaxY, .emitMinX, .emitMaxX, .emitMinY, .emitLen},
    by intro x; cases x <;> simp⟩

abbrev Reg := Option Bool × Option Bool × Bool

def defaultReg : Reg := (none, none, false)

section Machine
variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool)

abbrev G : Aux ⊕ M.K → Type :=
  fun k => Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool) M.Γ

def liftStmt : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Reg)
  | .push k f q => .push (Sum.inr k) (fun v => f v.1) (liftStmt q)
  | .peek k f q => .peek (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)
  | .pop k f q => .pop (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftStmt q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftStmt q₁) (liftStmt q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .halt

def resetGoto (t : M.Λ ⊕ Ph) : TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Reg) :=
  .load (fun v => (v.1, defaultReg)) (.goto fun _ => t)

def popDiscard5 (q : TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Reg)) :
    TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Reg) :=
  .pop (Sum.inl .inp) (fun v _ => v) <|
  .pop (Sum.inl .inp) (fun v _ => v) <|
  .pop (Sum.inl .inp) (fun v _ => v) <|
  .pop (Sum.inl .inp) (fun v _ => v) <|
  .pop (Sum.inl .inp) (fun v _ => v) q

def emitRaw (src : Aux) (self afterFalse : Ph) : TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Reg) :=
  .pop (Sum.inl src) (fun v o => (v.1, o, none, false)) <|
    .branch (fun v => v.2.1.isSome)
      (.push (Sum.inr M.k₀) (fun v => e.symm (v.2.1.getD false)) (resetGoto M (Sum.inr self)))
      (.push (Sum.inr M.k₀) (fun _ => e.symm false) (resetGoto M (Sum.inr afterFalse)))

def emitDelimWithFalse (src : Aux) (self afterFalse : Ph) :
    TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Reg) :=
  .pop (Sum.inl src) (fun v o => (v.1, o, none, false)) <|
    .branch (fun v => v.2.1.isSome)
      (.push (Sum.inr M.k₀) (fun v => e.symm (v.2.1.getD false)) <|
        .push (Sum.inr M.k₀) (fun _ => e.symm true) (resetGoto M (Sum.inr self)))
      (.push (Sum.inr M.k₀) (fun _ => e.symm false) (resetGoto M (Sum.inr afterFalse)))

def emitDelimFinal (src : Aux) (self : Ph) : TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Reg) :=
  .pop (Sum.inl src) (fun v o => (v.1, o, none, false)) <|
    .branch (fun v => v.2.1.isSome)
      (.push (Sum.inr M.k₀) (fun v => e.symm (v.2.1.getD false)) <|
        .push (Sum.inr M.k₀) (fun _ => e.symm true) (resetGoto M (Sum.inr self)))
      (resetGoto M (Sum.inl M.main))

def prog : M.Λ ⊕ Ph → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Reg)
  | Sum.inl l => liftStmt M (M.m l)
  | Sum.inr .countS =>
    .pop (Sum.inl .inp) (fun v o => (v.1, o, none, false)) <|
      .branch (fun v => v.2.1 == some true)
        (popDiscard5 M (resetGoto M (Sum.inr .inc)))
        (resetGoto M (Sum.inr .revCnt))
  | Sum.inr .inc =>
    .pop (Sum.inl .cnt) (fun v o => (v.1, o, none, false)) <|
      .branch (fun v => v.2.1 == some true)
        (.push (Sum.inl .cntTmp) (fun _ => false) (resetGoto M (Sum.inr .inc)))
        (.push (Sum.inl .cnt) (fun _ => true) (resetGoto M (Sum.inr .incRestore)))
  | Sum.inr .incRestore =>
    .pop (Sum.inl .cntTmp) (fun v o => (v.1, o, none, false)) <|
      .branch (fun v => v.2.1.isSome)
        (.push (Sum.inl .cnt) (fun v => v.2.1.getD false) (resetGoto M (Sum.inr .incRestore)))
        (resetGoto M (Sum.inr .countS))
  | Sum.inr .revCnt =>
    .pop (Sum.inl .cnt) (fun v o => (v.1, o, none, false)) <|
      .branch (fun v => v.2.1.isSome)
        (.push (Sum.inl .cntTmp) (fun v => v.2.1.getD false) (resetGoto M (Sum.inr .revCnt)))
        (resetGoto M (Sum.inr .parseX))
  | Sum.inr .parseX =>
    .pop (Sum.inl .inp) (fun v o => (v.1, o, none, false)) <|
      .branch (fun v => v.2.1 == some true)
        (.pop (Sum.inl .inp) (fun v o => (v.1, o, none, false)) <|
          .push (Sum.inl .cnt) (fun v => v.2.1.getD false) (resetGoto M (Sum.inr .parseX)))
        (resetGoto M (Sum.inr .unrevX))
  | Sum.inr .unrevX =>
    .pop (Sum.inl .cnt) (fun v o => (v.1, o, none, false)) <|
      .branch (fun v => v.2.1.isSome)
        (.push (Sum.inl .xLsb) (fun v => v.2.1.getD false) (resetGoto M (Sum.inr .unrevX)))
        (.load (fun v => (v.1, none, none, true)) (.goto fun _ => Sum.inr .scanXY))
  | Sum.inr .scanXY =>
    .pop (Sum.inl .xLsb) (fun v o₁ => (v.1, o₁, none, v.2.2.2)) <|
    .pop (Sum.inl .inp) (fun v o₂ => (v.1, v.2.1, o₂, v.2.2.2)) <|
      .branch (fun v => v.2.1.isSome || v.2.2.1.isSome)
        (.branch (fun v => v.2.1.isSome)
          (.push (Sum.inl .xRev) (fun v => v.2.1.getD false)
            (.branch (fun v => v.2.2.1.isSome)
              (.push (Sum.inl .yRev) (fun v => v.2.2.1.getD false)
                (.load (fun v => (v.1, none, none,
                  stepCmp v.2.2.2 (v.2.1.getD false) (v.2.2.1.getD false)))
                  (.goto fun _ => Sum.inr .scanXY)))
              (.load (fun v => (v.1, none, none,
                stepCmp v.2.2.2 (v.2.1.getD false) false))
                (.goto fun _ => Sum.inr .scanXY))))
          (.branch (fun v => v.2.2.1.isSome)
            (.push (Sum.inl .yRev) (fun v => v.2.2.1.getD false)
              (.load (fun v => (v.1, none, none,
                stepCmp v.2.2.2 false (v.2.2.1.getD false)))
                (.goto fun _ => Sum.inr .scanXY)))
            (resetGoto M (Sum.inr .scanXY))))
        (.branch (fun v => v.2.2.2)
          (resetGoto M (Sum.inr .emitMaxY))
          (resetGoto M (Sum.inr .emitMaxX)))
  | Sum.inr .emitMaxY => emitRaw M e .yRev .emitMaxY .emitMinX
  | Sum.inr .emitMinX => emitDelimWithFalse M e .xRev .emitMinX .emitLen
  | Sum.inr .emitMaxX => emitRaw M e .xRev .emitMaxX .emitMinY
  | Sum.inr .emitMinY => emitDelimWithFalse M e .yRev .emitMinY .emitLen
  | Sum.inr .emitLen => emitDelimFinal M e .cntTmp .emitLen

def N : FinTM2 :=
  letI := M.kFin
  letI := M.ΛFin
  letI := M.σFin
  { K := Aux ⊕ M.K
    k₀ := Sum.inl .inp
    k₁ := Sum.inr M.k₁
    Γ := G M
    Λ := M.Λ ⊕ Ph
    main := Sum.inr .countS
    σ := M.σ × Reg
    initialState := (M.initialState, defaultReg)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog M e }

def mk (i c ct xl xr yr : List Bool) (S : ∀ k, List (M.Γ k)) :
    ∀ k : Aux ⊕ M.K, List (G M k)
  | Sum.inl .inp => i
  | Sum.inl .cnt => c
  | Sum.inl .cntTmp => ct
  | Sum.inl .xLsb => xl
  | Sum.inl .xRev => xr
  | Sum.inl .yRev => yr
  | Sum.inr k => S k

variable {M} {e}

@[simp] lemma upd_inp (i c ct xl xr yr i' : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk M i c ct xl xr yr S) (Sum.inl .inp) i' = mk M i' c ct xl xr yr S := by
  funext k; rcases k with (_ | _ | _ | _ | _ | _) | k <;> simp [Function.update, mk]

@[simp] lemma upd_cnt (i c ct xl xr yr c' : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk M i c ct xl xr yr S) (Sum.inl .cnt) c' = mk M i c' ct xl xr yr S := by
  funext k; rcases k with (_ | _ | _ | _ | _ | _) | k <;> simp [Function.update, mk]

@[simp] lemma upd_cntTmp (i c ct xl xr yr ct' : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk M i c ct xl xr yr S) (Sum.inl .cntTmp) ct' = mk M i c ct' xl xr yr S := by
  funext k; rcases k with (_ | _ | _ | _ | _ | _) | k <;> simp [Function.update, mk]

@[simp] lemma upd_xLsb (i c ct xl xr yr xl' : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk M i c ct xl xr yr S) (Sum.inl .xLsb) xl' = mk M i c ct xl' xr yr S := by
  funext k; rcases k with (_ | _ | _ | _ | _ | _) | k <;> simp [Function.update, mk]

@[simp] lemma upd_xRev (i c ct xl xr yr xr' : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk M i c ct xl xr yr S) (Sum.inl .xRev) xr' = mk M i c ct xl xr' yr S := by
  funext k; rcases k with (_ | _ | _ | _ | _ | _) | k <;> simp [Function.update, mk]

@[simp] lemma upd_yRev (i c ct xl xr yr yr' : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk M i c ct xl xr yr S) (Sum.inl .yRev) yr' = mk M i c ct xl xr yr' S := by
  funext k; rcases k with (_ | _ | _ | _ | _ | _) | k <;> simp [Function.update, mk]

@[simp] lemma upd_inr (i c ct xl xr yr : List Bool) (S : ∀ k, List (M.Γ k)) (k : M.K)
    (v : List (G M (Sum.inr k))) :
    Function.update (mk M i c ct xl xr yr S) (Sum.inr k) v =
      mk M i c ct xl xr yr (Function.update S k v) := by
  funext k'
  rcases k' with (_ | _ | _ | _ | _ | _) | k'
  · simp [Function.update, mk]
  · simp [Function.update, mk]
  · simp [Function.update, mk]
  · simp [Function.update, mk]
  · simp [Function.update, mk]
  · simp [Function.update, mk]
  · by_cases h : k' = k
    · subst h; simp [Function.update, mk]
    · simp [Function.update, mk, h]

def liftCfg (c : TM2.Cfg M.Γ M.Λ M.σ) : (N M e).Cfg :=
  ⟨c.l.map Sum.inl, (c.var, defaultReg), mk M [] [] [] [] [] [] c.stk⟩

def cfg (l : Ph) (r : Reg) (i c ct xl xr yr : List Bool) (S : ∀ k, List (M.Γ k)) : (N M e).Cfg :=
  ⟨some (Sum.inr l), (M.initialState, r), mk M i c ct xl xr yr S⟩

lemma stepAux_lift (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftStmt M q) (v, defaultReg) (mk M [] [] [] [] [] [] S) =
      liftCfg (e := e) (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simp only [liftStmt, TM2.stepAux, upd_inr]; exact ih _ _
  | peek k f q ih => simp only [liftStmt, TM2.stepAux]; exact ih _ _
  | pop k f q ih => simp only [liftStmt, TM2.stepAux, upd_inr]; exact ih _ _
  | load a q ih => simp only [liftStmt, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftStmt, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma step_lift (c : TM2.Cfg M.Γ M.Λ M.σ) :
    (N M e).step (liftCfg c) = (M.step c).map liftCfg := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · show some (TM2.stepAux (liftStmt M (M.m l)) (v, defaultReg) (mk M [] [] [] [] [] [] S)) = _
    rw [stepAux_lift]
    rfl

lemma iterate_lift (n : ℕ) (o : Option (TM2.Cfg M.Γ M.Λ M.σ)) :
    (flip bind (N M e).step)^[n] (o.map liftCfg) = ((flip bind M.step)^[n] o).map liftCfg := by
  have hs : Function.Semiconj (Option.map (liftCfg (M := M) (e := e))) (flip bind M.step)
      (flip bind (N M e).step) := by
    intro o
    rcases o with _ | c
    · rfl
    · show (M.step c).map liftCfg = (N M e).step (liftCfg c)
      rw [step_lift]
  exact ((hs.iterate_right n) o).symm

/- Phase execution lemmas. -/

lemma incRestore_run (i c ct xl xr yr : List Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .incRestore defaultReg i c ct xl xr yr S)
      (some (cfg .countS defaultReg i (ct.reverse ++ c) [] xl xr yr S)) (ct.length + 1) := by
  induction ct generalizing c with
  | nil =>
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (Sum.inr .incRestore)) _ _) = _
    simp [prog, resetGoto, TM2.stepAux, mk, cfg]
    rfl
  | cons b ct ih =>
    have h1 : RIn (N M e).step (cfg .incRestore defaultReg i c (b :: ct) xl xr yr S)
        (some (cfg .incRestore defaultReg i (b :: c) ct xl xr yr S)) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (Sum.inr .incRestore)) _ _) = _
      simp [prog, resetGoto, TM2.stepAux, mk, cfg]
      rfl
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h1.trans (ih (b :: c))

lemma inc_run (i c ct xl xr yr : List Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .inc defaultReg i c ct xl xr yr S)
      (some (cfg .countS defaultReg i (ct.reverse ++ succBits c) [] xl xr yr S))
      (2 * c.length + ct.length + 2) := by
  induction c generalizing ct with
  | nil =>
    have h1 : RIn (N M e).step (cfg .inc defaultReg i [] ct xl xr yr S)
        (some (cfg .incRestore defaultReg i [true] ct xl xr yr S)) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (Sum.inr .inc)) _ _) = _
      simp [prog, resetGoto, TM2.stepAux, mk, cfg]
      rfl
    exact (h1.trans (incRestore_run i [true] ct xl xr yr S)).mono (by simp; omega)
  | cons b c ih =>
    cases b with
    | false =>
      have h1 : RIn (N M e).step (cfg .inc defaultReg i (false :: c) ct xl xr yr S)
          (some (cfg .incRestore defaultReg i (true :: c) ct xl xr yr S)) 1 := by
        refine RIn.single ?_
        show some (TM2.stepAux (prog M e (Sum.inr .inc)) _ _) = _
        simp [prog, resetGoto, TM2.stepAux, mk, cfg]
        rfl
      exact (h1.trans (incRestore_run i (true :: c) ct xl xr yr S)).mono
        (by simp; omega)
    | true =>
      have h1 : RIn (N M e).step (cfg .inc defaultReg i (true :: c) ct xl xr yr S)
          (some (cfg .inc defaultReg i c (false :: ct) xl xr yr S)) 1 := by
        refine RIn.single ?_
        show some (TM2.stepAux (prog M e (Sum.inr .inc)) _ _) = _
        simp [prog, resetGoto, TM2.stepAux, mk, cfg]
        rfl
      have h2 := ih (false :: ct)
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at h2
      exact (h1.trans h2).mono (by simp; omega)

lemma countS_run (s rest : List Bool) (k : ℕ) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step
      (cfg .countS defaultReg
        (BitstringEncoding.delimit (BitstringEncoding.bitEncode s) ++ rest)
        (encodeNat k) [] [] [] [] S)
      (some (cfg .revCnt defaultReg rest (encodeNat (k + s.length)) [] [] [] [] S))
      (s.length * (2 * (k + s.length) + 3) + 1) := by
  induction s generalizing k with
  | nil =>
    rw [delimit_bitEncode_nil, List.length_nil, Nat.add_zero, Nat.zero_mul, Nat.zero_add]
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (Sum.inr .countS)) _ _) = _
    simp [prog, resetGoto, TM2.stepAux, mk, cfg]
    rfl
  | cons b s ih =>
    rw [delimit_bitEncode_cons]
    have h1 : RIn (N M e).step
        (cfg .countS defaultReg
          (true :: true :: true :: b :: true :: false ::
            (BitstringEncoding.delimit (BitstringEncoding.bitEncode s) ++ rest))
          (encodeNat k) [] [] [] [] S)
        (some (cfg .inc defaultReg
          (BitstringEncoding.delimit (BitstringEncoding.bitEncode s) ++ rest)
          (encodeNat k) [] [] [] [] S)) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (Sum.inr .countS)) _ _) = _
      simp [prog, popDiscard5, resetGoto, TM2.stepAux, mk, cfg]
      rfl
    have h2 := inc_run (M := M) (e := e)
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode s) ++ rest)
      (encodeNat k) [] [] [] [] S
    simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero,
      succBits_encodeNat] at h2
    have h3 := ih (k + 1)
    have hk : k + 1 + s.length = k + (b :: s).length := by simp; omega
    rw [hk] at h3
    refine ((h1.trans h2).trans h3).mono ?_
    have hlen := length_encodeNat_le k
    simp only [List.length_cons]
    nlinarith

lemma revCnt_run (i c ct : List Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .revCnt defaultReg i c ct [] [] [] S)
      (some (cfg .parseX defaultReg i [] (c.reverse ++ ct) [] [] [] S)) (c.length + 1) := by
  induction c generalizing ct with
  | nil =>
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (Sum.inr .revCnt)) _ _) = _
    simp [prog, resetGoto, TM2.stepAux, mk, cfg]
    rfl
  | cons b c ih =>
    have h1 : RIn (N M e).step (cfg .revCnt defaultReg i (b :: c) ct [] [] [] S)
        (some (cfg .revCnt defaultReg i c (b :: ct) [] [] [] S)) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (Sum.inr .revCnt)) _ _) = _
      simp [prog, resetGoto, TM2.stepAux, mk, cfg]
      rfl
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h1.trans (ih (b :: ct))

lemma parseX_run (x rest c ct : List Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .parseX defaultReg (BitstringEncoding.delimit x ++ rest) c ct [] [] [] S)
      (some (cfg .unrevX defaultReg rest (x.reverse ++ c) ct [] [] [] S)) (x.length + 1) := by
  induction x generalizing c with
  | nil =>
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (Sum.inr .parseX)) _ _) = _
    simp [BitstringEncoding.delimit, prog, resetGoto, TM2.stepAux, mk, cfg]
    rfl
  | cons b x ih =>
    have h1 : RIn (N M e).step
        (cfg .parseX defaultReg (BitstringEncoding.delimit (b :: x) ++ rest) c ct [] [] [] S)
        (some (cfg .parseX defaultReg (BitstringEncoding.delimit x ++ rest) (b :: c) ct [] [] [] S)) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (Sum.inr .parseX)) _ _) = _
      simp [BitstringEncoding.delimit, prog, resetGoto, TM2.stepAux, mk, cfg]
      rfl
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h1.trans (ih (b :: c))

lemma unrevX_run (y c ct xl : List Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .unrevX defaultReg y c ct xl [] [] S)
      (some (cfg .scanXY (none, none, true) y [] ct (c.reverse ++ xl) [] [] S)) (c.length + 1) := by
  induction c generalizing xl with
  | nil =>
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (Sum.inr .unrevX)) _ _) = _
    simp [prog, TM2.stepAux, mk, cfg]
    rfl
  | cons b c ih =>
    have h1 : RIn (N M e).step (cfg .unrevX defaultReg y (b :: c) ct xl [] [] S)
        (some (cfg .unrevX defaultReg y c ct (b :: xl) [] [] S)) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (Sum.inr .unrevX)) _ _) = _
      simp [prog, resetGoto, TM2.stepAux, mk, cfg]
      rfl
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h1.trans (ih (b :: xl))

lemma scanXY_run (le : Bool) (x y ct xr yr : List Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .scanXY (none, none, le) y [] ct x xr yr S)
      (some (cfg (if cmpBits le x y then .emitMaxY else .emitMaxX) defaultReg
        [] [] ct [] (x.reverse ++ xr) (y.reverse ++ yr) S))
      (max x.length y.length + 1) := by
  cases x with
  | nil =>
    cases y with
    | nil =>
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (Sum.inr .scanXY)) _ _) = _
      cases le <;> simp [cmpBits, prog, resetGoto, TM2.stepAux, mk, cfg] <;> rfl
    | cons b bs =>
      have h1 : RIn (N M e).step (cfg .scanXY (none, none, le) (b :: bs) [] ct [] xr yr S)
          (some (cfg .scanXY (none, none, stepCmp le false b) bs [] ct [] xr (b :: yr) S)) 1 := by
        refine RIn.single ?_
        show some (TM2.stepAux (prog M e (Sum.inr .scanXY)) _ _) = _
        simp [prog, TM2.stepAux, mk, cfg]
        rfl
      have h2 := scanXY_run (stepCmp le false b) [] bs ct xr (b :: yr) S
      simpa [cmpBits, List.reverse_cons, List.append_assoc, Nat.add_comm] using h1.trans h2
  | cons a as =>
    cases y with
    | nil =>
      have h1 : RIn (N M e).step (cfg .scanXY (none, none, le) [] [] ct (a :: as) xr yr S)
          (some (cfg .scanXY (none, none, stepCmp le a false) [] [] ct as (a :: xr) yr S)) 1 := by
        refine RIn.single ?_
        show some (TM2.stepAux (prog M e (Sum.inr .scanXY)) _ _) = _
        simp [prog, TM2.stepAux, mk, cfg]
        rfl
      have h2 := scanXY_run (stepCmp le a false) as [] ct (a :: xr) yr S
      simpa [cmpBits, List.reverse_cons, List.append_assoc, Nat.add_comm] using h1.trans h2
    | cons b bs =>
      have h1 : RIn (N M e).step (cfg .scanXY (none, none, le) (b :: bs) [] ct (a :: as) xr yr S)
          (some (cfg .scanXY (none, none, stepCmp le a b) bs [] ct as (a :: xr) (b :: yr) S)) 1 := by
        refine RIn.single ?_
        show some (TM2.stepAux (prog M e (Sum.inr .scanXY)) _ _) = _
        simp [prog, TM2.stepAux, mk, cfg]
        rfl
      have h2 := scanXY_run (stepCmp le a b) as bs ct (a :: xr) (b :: yr) S
      simpa [cmpBits, List.reverse_cons, List.append_assoc, Nat.succ_max_succ, Nat.add_comm]
        using h1.trans h2
termination_by x.length + y.length

lemma emitMaxY_run (ct xr yr : List Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .emitMaxY defaultReg [] [] ct [] xr yr S)
      (some (cfg .emitMinX defaultReg [] [] ct [] xr []
        (Function.update S M.k₀ (e.symm false :: (yr.reverse.map e.symm ++ S M.k₀)))))
      (yr.length + 1) := by
  induction yr generalizing S with
  | nil =>
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (Sum.inr .emitMaxY)) _ _) = _
    simp [prog, emitRaw, resetGoto, TM2.stepAux, mk, cfg]
    rfl
  | cons b yr ih =>
    have h1 : RIn (N M e).step (cfg .emitMaxY defaultReg [] [] ct [] xr (b :: yr) S)
        (some (cfg .emitMaxY defaultReg [] [] ct [] xr yr
          (Function.update S M.k₀ (e.symm b :: S M.k₀)))) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (Sum.inr .emitMaxY)) _ _) = _
      simp [prog, emitRaw, resetGoto, TM2.stepAux, mk, cfg]
      rfl
    have h2 := ih (Function.update S M.k₀ (e.symm b :: S M.k₀))
    simp only [Function.update_self, Function.update_idem] at h2
    simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_comm] using h1.trans h2

lemma emitMaxX_run (ct xr yr : List Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .emitMaxX defaultReg [] [] ct [] xr yr S)
      (some (cfg .emitMinY defaultReg [] [] ct [] [] yr
        (Function.update S M.k₀ (e.symm false :: (xr.reverse.map e.symm ++ S M.k₀)))))
      (xr.length + 1) := by
  induction xr generalizing S with
  | nil =>
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (Sum.inr .emitMaxX)) _ _) = _
    simp [prog, emitRaw, resetGoto, TM2.stepAux, mk, cfg]
    rfl
  | cons b xr ih =>
    have h1 : RIn (N M e).step (cfg .emitMaxX defaultReg [] [] ct [] (b :: xr) yr S)
        (some (cfg .emitMaxX defaultReg [] [] ct [] xr yr
          (Function.update S M.k₀ (e.symm b :: S M.k₀)))) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (Sum.inr .emitMaxX)) _ _) = _
      simp [prog, emitRaw, resetGoto, TM2.stepAux, mk, cfg]
      rfl
    have h2 := ih (Function.update S M.k₀ (e.symm b :: S M.k₀))
    simp only [Function.update_self, Function.update_idem] at h2
    simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_comm] using h1.trans h2

lemma emitMinX_run (ct xr acc tail : List Bool) (S : ∀ k, List (M.Γ k))
    (hS : S M.k₀ = (BitstringEncoding.delimit acc ++ tail).map e.symm) :
    RIn (N M e).step (cfg .emitMinX defaultReg [] [] ct [] xr [] S)
      (some (cfg .emitLen defaultReg [] [] ct [] [] []
        (Function.update S M.k₀
          ((BitstringEncoding.delimit [] ++
            (BitstringEncoding.delimit (xr.reverse ++ acc) ++ tail)).map e.symm))))
      (xr.length + 1) := by
  induction xr generalizing acc S with
  | nil =>
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (Sum.inr .emitMinX)) _ _) = _
    simp [prog, emitDelimWithFalse, resetGoto, TM2.stepAux, mk, cfg, hS, BitstringEncoding.delimit]
    rfl
  | cons b xr ih =>
    have h1 : RIn (N M e).step (cfg .emitMinX defaultReg [] [] ct [] (b :: xr) [] S)
        (some (cfg .emitMinX defaultReg [] [] ct [] xr []
          (Function.update S M.k₀ (e.symm true :: e.symm b :: S M.k₀)))) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (Sum.inr .emitMinX)) _ _) = _
      simp [prog, emitDelimWithFalse, resetGoto, TM2.stepAux, mk, cfg]
      rfl
    have h2 := ih (b :: acc) (Function.update S M.k₀ (e.symm true :: e.symm b :: S M.k₀))
      (by simp [hS, BitstringEncoding.delimit])
    simp only [Function.update_idem] at h2
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h1.trans h2

lemma emitMinY_run (ct yr acc tail : List Bool) (S : ∀ k, List (M.Γ k))
    (hS : S M.k₀ = (BitstringEncoding.delimit acc ++ tail).map e.symm) :
    RIn (N M e).step (cfg .emitMinY defaultReg [] [] ct [] [] yr S)
      (some (cfg .emitLen defaultReg [] [] ct [] [] []
        (Function.update S M.k₀
          ((BitstringEncoding.delimit [] ++
            (BitstringEncoding.delimit (yr.reverse ++ acc) ++ tail)).map e.symm))))
      (yr.length + 1) := by
  induction yr generalizing acc S with
  | nil =>
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (Sum.inr .emitMinY)) _ _) = _
    simp [prog, emitDelimWithFalse, resetGoto, TM2.stepAux, mk, cfg, hS, BitstringEncoding.delimit]
    rfl
  | cons b yr ih =>
    have h1 : RIn (N M e).step (cfg .emitMinY defaultReg [] [] ct [] [] (b :: yr) S)
        (some (cfg .emitMinY defaultReg [] [] ct [] [] yr
          (Function.update S M.k₀ (e.symm true :: e.symm b :: S M.k₀)))) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (Sum.inr .emitMinY)) _ _) = _
      simp [prog, emitDelimWithFalse, resetGoto, TM2.stepAux, mk, cfg]
      rfl
    have h2 := ih (b :: acc) (Function.update S M.k₀ (e.symm true :: e.symm b :: S M.k₀))
      (by simp [hS, BitstringEncoding.delimit])
    simp only [Function.update_idem] at h2
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h1.trans h2

lemma emitLen_run (ct acc tail : List Bool) (S : ∀ k, List (M.Γ k))
    (hS : S M.k₀ = (BitstringEncoding.delimit acc ++ tail).map e.symm) :
    RIn (N M e).step (cfg .emitLen defaultReg [] [] ct [] [] [] S)
      (some (liftCfg ⟨some M.main, M.initialState,
        Function.update S M.k₀
          ((BitstringEncoding.delimit (ct.reverse ++ acc) ++ tail).map e.symm)⟩))
      (ct.length + 1) := by
  induction ct generalizing acc S with
  | nil =>
    have hupd : Function.update S M.k₀ ((BitstringEncoding.delimit acc ++ tail).map e.symm) = S := by
      rw [← hS, Function.update_eq_self]
    rw [List.reverse_nil, List.nil_append, hupd]
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (Sum.inr .emitLen)) _ _) = _
    simp [prog, emitDelimFinal, resetGoto, TM2.stepAux, mk, liftCfg]
    rfl
  | cons b ct ih =>
    have h1 : RIn (N M e).step (cfg .emitLen defaultReg [] [] (b :: ct) [] [] [] S)
        (some (cfg .emitLen defaultReg [] [] ct [] [] []
          (Function.update S M.k₀ (e.symm true :: e.symm b :: S M.k₀)))) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (Sum.inr .emitLen)) _ _) = _
      simp [prog, emitDelimFinal, resetGoto, TM2.stepAux, mk, cfg]
      rfl
    have h2 := ih (b :: acc) (Function.update S M.k₀ (e.symm true :: e.symm b :: S M.k₀))
      (by simp [hS, BitstringEncoding.delimit])
    simp only [Function.update_idem] at h2
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h1.trans h2

/- Initial, handoff, and final configuration glue. -/

lemma initList_N (l : List Bool) :
    initList (N M e) l = cfg .countS defaultReg l [] [] [] [] [] (fun _ => []) := by
  simp only [initList, cfg]
  congr 1
  funext k
  rcases k with (_ | _ | _ | _ | _ | _) | k <;> rfl

lemma initList_M (s : List (M.Γ M.k₀)) :
    liftCfg (e := e) ⟨some M.main, M.initialState, Function.update (fun _ => []) M.k₀ s⟩ =
      liftCfg (e := e) (initList M s) := by
  simp only [initList]
  congr 3
  funext k
  by_cases h : k = M.k₀
  · subst h; simp
  · rw [Function.update_of_ne h, dif_neg h]

lemma haltList_lift (s : List (M.Γ M.k₁)) :
    liftCfg (e := e) (haltList M s) = haltList (N M e) s := by
  simp only [liftCfg, haltList]
  congr 1
  funext k
  rcases k with (_ | _ | _ | _ | _ | _) | k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · by_cases h : k = M.k₁
    · subst h
      simp only [mk]
      split
      · split
        · rfl
        · rename_i hne; exact absurd rfl hne
      · rename_i hne; exact absurd trivial hne
    · simp only [mk, dif_neg h]
      split
      · rename_i heq
        exact absurd (Sum.inr_injective (heq : (Sum.inr k : Aux ⊕ M.K) = Sum.inr M.k₁)) h
      · rfl

variable (M e) in
lemma run_M {s : List (M.Γ M.k₀)} {out : List (M.Γ M.k₁)} {T : ℕ}
    (h : TM2OutputsInTime M s (some out) T) :
    RIn (N M e).step (liftCfg (e := e) (initList M s)) (some (haltList (N M e) out)) T := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  refine ⟨n, hle, ?_⟩
  have := iterate_lift (M := M) (e := e) n (some (initList M s))
  change (flip bind (N M e).step)^[n] (Option.map liftCfg (some (initList M s))) = _
  rw [this]
  refine (congrArg (Option.map liftCfg) hn).trans ?_
  show some (liftCfg (haltList M out)) = _
  rw [haltList_lift]

lemma preprocess_run (s : List Bool) (u v : ℕ) :
    RIn (N M e).step
      (cfg .countS defaultReg
        (BitstringEncoding.delimit (BitstringEncoding.bitEncode s) ++
          (BitstringEncoding.delimit (encodeNat u) ++ encodeNat v))
        [] [] [] [] [] (fun _ => []))
      (some (liftCfg (e := e) (initList M
        ((BitstringEncoding.delimit (encodeNat s.length) ++
          (BitstringEncoding.delimit (encodeNat (min u v)) ++ encodeNat (max u v))).map e.symm))))
      (2 * (BitstringEncoding.delimit (BitstringEncoding.bitEncode s) ++
          (BitstringEncoding.delimit (encodeNat u) ++ encodeNat v)).length ^ 2 +
        12 * (BitstringEncoding.delimit (BitstringEncoding.bitEncode s) ++
          (BitstringEncoding.delimit (encodeNat u) ++ encodeNat v)).length + 8) := by
  set x := encodeNat u
  set y := encodeNat v
  set inp := BitstringEncoding.delimit (BitstringEncoding.bitEncode s) ++
    (BitstringEncoding.delimit x ++ y)
  set target := BitstringEncoding.delimit (encodeNat s.length) ++
    (BitstringEncoding.delimit (encodeNat (min u v)) ++ encodeNat (max u v))
  have h1 := countS_run (M := M) (e := e) s (BitstringEncoding.delimit x ++ y) 0 (fun _ => [])
  simp only [Nat.zero_add] at h1
  have h1' : RIn (N M e).step
      (cfg .countS defaultReg inp [] [] [] [] [] (fun _ => []))
      (some (cfg .revCnt defaultReg (BitstringEncoding.delimit x ++ y)
        (encodeNat s.length) [] [] [] [] (fun _ => [])))
      (s.length * (2 * s.length + 3) + 1) := h1
  have h2 := revCnt_run (M := M) (e := e) (BitstringEncoding.delimit x ++ y)
    (encodeNat s.length) [] (fun _ => [])
  simp only [List.append_nil] at h2
  have h3 := parseX_run (M := M) (e := e) x y [] (encodeNat s.length).reverse (fun _ => [])
  simp only [List.append_nil] at h3
  have h4 := unrevX_run (M := M) (e := e) y x.reverse (encodeNat s.length).reverse [] (fun _ => [])
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h4
  have h5 := scanXY_run (M := M) (e := e) true x y (encodeNat s.length).reverse [] [] (fun _ => [])
  simp only [List.append_nil] at h5
  have hcmp : cmpBits true x y = decide (u ≤ v) := cmpBits_encodeNat u v
  rw [hcmp] at h5
  have hlen_inp : inp.length = 6 * s.length + 2 * x.length + y.length + 2 := by
    simp [inp, BitstringEncoding.length_delimit, length_bitEncode_list_bool]
    omega
  have hlen_cnt : (encodeNat s.length).length ≤ s.length := length_encodeNat_le s.length
  have hmax_xy : max x.length y.length ≤ x.length + y.length := by omega
  by_cases huv : u ≤ v
  · simp only [decide_eq_true huv, ↓reduceIte] at h5
    have hmin : min u v = u := Nat.min_eq_left huv
    have hmax : max u v = v := Nat.max_eq_right huv
    have h6 := emitMaxY_run (M := M) (e := e) (encodeNat s.length).reverse x.reverse y.reverse
      (fun _ => [])
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h6
    have h7 := emitMinX_run (M := M) (e := e) (encodeNat s.length).reverse x.reverse [] y
      (Function.update (fun _ => []) M.k₀ (e.symm false :: y.map e.symm))
      (by simp [BitstringEncoding.delimit])
    simp only [Function.update_idem, List.reverse_reverse, List.append_nil,
      List.length_reverse] at h7
    have h8 := emitLen_run (M := M) (e := e) (encodeNat s.length).reverse []
      (BitstringEncoding.delimit x ++ y)
      (Function.update (fun _ => []) M.k₀
        ((BitstringEncoding.delimit [] ++ (BitstringEncoding.delimit x ++ y)).map e.symm))
      (by simp)
    simp only [Function.update_idem, List.reverse_reverse, List.append_nil,
      List.length_reverse] at h8
    rw [initList_M] at h8
    have htarget : BitstringEncoding.delimit (encodeNat s.length) ++ (BitstringEncoding.delimit x ++ y) =
        target := by
      simp [target, x, y, hmin, hmax]
    rw [htarget] at h8
    exact (((((((h1'.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).mono
      (by nlinarith)
  · have hvu : v ≤ u := by omega
    simp only [decide_eq_false huv, Bool.false_eq_true, ↓reduceIte] at h5
    have hmin : min u v = v := Nat.min_eq_right hvu
    have hmax : max u v = u := Nat.max_eq_left hvu
    have h6 := emitMaxX_run (M := M) (e := e) (encodeNat s.length).reverse x.reverse y.reverse
      (fun _ => [])
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h6
    have h7 := emitMinY_run (M := M) (e := e) (encodeNat s.length).reverse y.reverse [] x
      (Function.update (fun _ => []) M.k₀ (e.symm false :: x.map e.symm))
      (by simp [BitstringEncoding.delimit])
    simp only [Function.update_idem, List.reverse_reverse, List.append_nil,
      List.length_reverse] at h7
    have h8 := emitLen_run (M := M) (e := e) (encodeNat s.length).reverse []
      (BitstringEncoding.delimit y ++ x)
      (Function.update (fun _ => []) M.k₀
        ((BitstringEncoding.delimit [] ++ (BitstringEncoding.delimit y ++ x)).map e.symm))
      (by simp)
    simp only [Function.update_idem, List.reverse_reverse, List.append_nil,
      List.length_reverse] at h8
    rw [initList_M] at h8
    have htarget : BitstringEncoding.delimit (encodeNat s.length) ++ (BitstringEncoding.delimit y ++ x) =
        target := by
      simp [target, x, y, hmin, hmax]
    rw [htarget] at h8
    exact (((((((h1'.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).mono
      (by nlinarith)

end Machine
end OMA.Erdos78Adapter

open OMA.Erdos78Adapter Turing Computability ComplexityTheory in
theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_cohen_R1.H2 := by
  intro f hf
  obtain ⟨M⟩ := hf
  refine ⟨fun p => f (p.1.length, min p.2.1 p.2.2, max p.2.1 p.2.2), ?_, fun _ _ _ => rfl⟩
  let P : Polynomial ℕ :=
    Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 12 * Polynomial.X + Polynomial.C 8 +
      M.time.comp (Polynomial.C 8 * Polynomial.X + Polynomial.C 2)
  refine ⟨{
    tm := N M.tm M.inputAlphabet
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := M.outputAlphabet
    time := P
    outputsFun := ?_ }⟩
  rintro ⟨s, u, v⟩
  set x := encodeNat u
  set y := encodeNat v
  set inp := BitstringEncoding.delimit (BitstringEncoding.bitEncode s) ++
    (BitstringEncoding.delimit x ++ y)
  let q : ℕ × ℕ × ℕ := (s.length, min u v, max u v)
  set target := BitstringEncoding.delimit (encodeNat s.length) ++
    (BitstringEncoding.delimit (encodeNat (min u v)) ++ encodeNat (max u v))
  have henc_in : (BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode (s, u, v) = inp :=
    rfl
  have henc_q : (BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode q = target := rfl
  have hmap_in : List.map ((Equiv.refl Bool :
      (N M.tm M.inputAlphabet).Γ (N M.tm M.inputAlphabet).k₀ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode (s, u, v)) = inp := by
    rw [henc_in]; exact List.map_id _
  have hmap_q : List.map M.inputAlphabet.invFun
      ((BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode q) = target.map M.inputAlphabet.symm :=
    rfl
  have hpre : RIn (N M.tm M.inputAlphabet).step
      (initList (N M.tm M.inputAlphabet) inp)
      (some (liftCfg (e := M.inputAlphabet) (initList M.tm (target.map M.inputAlphabet.symm))))
      (2 * inp.length ^ 2 + 12 * inp.length + 8) := by
    rw [initList_N]
    exact preprocess_run (M := M.tm) (e := M.inputAlphabet) s u v
  have hM := M.outputsFun q
  rw [hmap_q] at hM
  have hrun := hpre.trans (run_M M.tm M.inputAlphabet hM)
  have hlen_inp : inp.length = 6 * s.length + 2 * x.length + y.length + 2 := by
    simp [inp, BitstringEncoding.length_delimit, length_bitEncode_list_bool]
    omega
  have hlen_cnt : (encodeNat s.length).length ≤ s.length := length_encodeNat_le s.length
  have hlen_min : (encodeNat (min u v)).length ≤ x.length + y.length := by
    by_cases h : u ≤ v
    · rw [Nat.min_eq_left h]; change x.length ≤ _; omega
    · rw [Nat.min_eq_right (by omega)]; change y.length ≤ _; omega
  have hlen_max : (encodeNat (max u v)).length ≤ x.length + y.length := by
    by_cases h : u ≤ v
    · rw [Nat.max_eq_right h]; change y.length ≤ _; omega
    · rw [Nat.max_eq_left (by omega)]; change x.length ≤ _; omega
  have hlen_target : target.length ≤ 8 * inp.length + 2 := by
    simp only [target, BitstringEncoding.length_delimit, List.length_append]
    omega
  have htime : (2 * inp.length ^ 2 + 12 * inp.length + 8) +
      M.time.eval ((BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode q).length ≤
      P.eval ((BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode (s, u, v)).length := by
    rw [henc_in, henc_q]
    simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp]
    have hm := eval_mono M.time hlen_target
    omega
  have hrun' := hrun.mono htime
  have key : ∀ l : List Bool, l = inp →
      TM2OutputsInTime (N M.tm M.inputAlphabet) l
        (some (List.map M.outputAlphabet.invFun
          ((BitstringEncoding.toEncoding (α := Bool)).encode (f q))))
        (P.eval ((BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode (s, u, v)).length) := by
    rintro l rfl
    exact Classical.choice (by
      obtain ⟨n, hn, hexec⟩ := hrun'
      exact ⟨⟨⟨n, hexec⟩, hn⟩⟩)
  exact key _ hmap_in
