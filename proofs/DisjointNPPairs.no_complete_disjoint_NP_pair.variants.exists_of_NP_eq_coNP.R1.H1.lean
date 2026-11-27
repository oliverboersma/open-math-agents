import OMAReductions.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1
import Mathlib

-- Step DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP.R1.H1: hypothesis H1 of reduction DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP.R1
-- Credit: @TheWaler (parent reduction R1)
-- Credit: @marcusbuffett (sub-reduction R1.H1.R1)
-- Credit: Marcus Buffett (leaf H1.R1.H1)
-- Credit: OrangeHeadz (leaf H1.R1.H2)
-- Credit: @LordMike (assembly)


/-! NP membership of unary CNF satisfiability splits into verification of a
given finite bit assignment and the bound on the amount of assignment needed. -/
-- Credit: @marcusbuffett

open ComplexityTheory
namespace OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1

/-- The deterministic verifier checks the syntax and tests every clause against
the supplied finite assignment. Positions past the end default to false. -/
def H1 : Prop :=
  ∃ R : (List Bool × List Bool) → Bool, IsPolyTime R ∧ ∀ x w, R (x,w) = true ↔
    ∃ F : List (List (Bool × ℕ)),
      x = F.flatMap (fun c => c.flatMap (fun t => [true,t.1] ++ List.replicate t.2 true ++ [false]) ++ [false]) ∧
      ∀ c ∈ F, ∃ t ∈ c, (w[t.2]?).getD false = t.1

/-- Every assignment can be truncated to an input-length witness without
changing the value of any literal in the formula. -/
def H2 : Prop :=
  ∀ (F : List (List (Bool × ℕ))) (a : ℕ → Bool), ∃ w : List Bool,
    w.length ≤ (F.flatMap (fun c => c.flatMap (fun t => [true,t.1] ++ List.replicate t.2 true ++ [false]) ++ [false])).length ∧
    ∀ c ∈ F, ∀ t ∈ c, (w[t.2]?).getD false = a t.2

theorem main : H1 → H2 → OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1.H1 := by
  classical
  rintro ⟨R,poly,verify⟩ restrict
  let C : DecisionProblem := fun x => decide (∃ w : List Bool, w.length ≤ x.length ∧ R (x,w) = true)
  refine ⟨C,⟨Polynomial.X,R,poly,fun x => by simp [C]⟩,?_⟩
  intro x
  simp only [C,decide_eq_true_iff]
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨F,hx,hF⟩ := (verify x w).mp hw
    exact ⟨F,fun i => (w[i]?).getD false,hx,hF⟩
  · rintro ⟨F,a,rfl,hF⟩
    obtain ⟨w,hw,matchLit⟩ := restrict F a
    refine ⟨w,hw,(verify _ w).mpr ⟨F,rfl,?_⟩⟩
    intro c hc
    obtain ⟨t,ht,ha⟩ := hF c hc
    exact ⟨t,ht,(matchLit c hc t ht).trans ha⟩

end OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1


/-! A deterministic verifier for unary CNF. The formula scanner reads the sign
and then moves one place in the assignment for each unary digit. It rewinds the
assignment when a new sign is read. The tape and bounded-run conventions adapt
the merged machines of @steveDOTdigital and @ashnewmanjones. -/

open Turing Computability ComplexityTheory
namespace UnaryVerifier

private abbrev Lit := Bool × ℕ
private abbrev Clause := List Lit
private abbrev Formula := List Clause
private def litCode (t : Lit) := [true,t.1] ++ List.replicate t.2 true ++ [false]
private def codeC (c : Clause) := c.flatMap litCode ++ [false]
private def codeF (f : Formula) := f.flatMap codeC
private def value (w : List Bool) (t : Lit) := (w[t.2]?).getD false == t.1
private def valid (w : List Bool) (f : Formula) := ∀ c ∈ f, ∃ t ∈ c, value w t = true

private inductive Mode
  | start | body (sat : Bool) | sign (sat : Bool) | unary (sat pol : Bool) | bad
  deriving DecidableEq, Fintype
private inductive Move | stay | advance | home deriving DecidableEq

private def move : Mode → Bool → Move
  | .sign _, _ => .home
  | .unary _ _, true => .advance
  | _, _ => .stay

private def tick : Mode → Bool → Bool → Mode
  | .start, true, _ => .sign false
  | .start, false, _ => .bad
  | .body sat, true, _ => .sign sat
  | .body sat, false, _ => if sat then .start else .bad
  | .sign sat, b, _ => .unary sat b
  | .unary sat pol, false, cur => .body (sat || (cur == pol))
  | .unary sat pol, true, _ => .unary sat pol
  | .bad, _, _ => .bad

private def head (ws : List Bool) := ws.head?.getD false
private def shift (w ws : List Bool) : Move → List Bool
  | .stay => ws | .advance => ws.tail | .home => w
private def scan (w : List Bool) : List Bool → Mode → List Bool → Bool
  | [],s,_ => s == .start
  | b::xs,s,ws => scan w xs (tick s b (head ws)) (shift w ws (move s b))

private def Whole (w x : List Bool) : Prop := ∃ f, x=codeF f ∧ valid w f
private def Tail (w : List Bool) (s : Bool) (x : List Bool) : Prop :=
  ∃ c f, x=codeC c ++ codeF f ∧ (s=true ∨ ∃ t ∈ c, value w t = true) ∧ valid w f
private def Index (w ws : List Bool) (s p : Bool) (x : List Bool) : Prop :=
  ∃ (i : ℕ) (rest : List Bool), x=List.replicate i true ++ false::rest ∧
    Tail w (s || ((ws[i]?).getD false == p)) rest

private theorem valid_cons (w : List Bool) (c : Clause) (f : Formula) :
    valid w (c::f) ↔ (∃ t ∈ c, value w t = true) ∧ valid w f := by simp [valid]

private theorem tail_nil (w : List Bool) (s : Bool) : ¬Tail w s [] := by
  rintro ⟨c,f,h,-⟩
  simp [codeC,List.append_assoc] at h

private theorem whole_cases (w x : List Bool) : Whole w x ↔ x=[] ∨ Tail w false x := by
  constructor
  · rintro ⟨f,h,hf⟩
    cases f with
    | nil => exact Or.inl h
    | cons c f =>
      obtain ⟨cs,fs⟩ := (valid_cons ..).mp hf
      exact Or.inr ⟨c,f,h,Or.inr cs,fs⟩
  · rintro (rfl|⟨c,f,h,cs,fs⟩)
    · exact ⟨[],rfl,by simp [valid]⟩
    · exact ⟨c::f,h,(valid_cons ..).2 ⟨cs.resolve_left (by decide),fs⟩⟩

private theorem tail_false (w xs : List Bool) (s : Bool) :
    Tail w s (false::xs) ↔ s=true ∧ Whole w xs := by
  constructor
  · rintro ⟨c,f,h,hs,hf⟩
    cases c with
    | nil => exact ⟨hs.resolve_right (by simp), f, List.cons.inj h |>.2, hf⟩
    | cons t c => simp [codeC,litCode] at h
  · rintro ⟨hs,f,rfl,hf⟩
    exact ⟨[],f,rfl,Or.inl hs,hf⟩

private theorem tail_true (w xs : List Bool) (s : Bool) :
    Tail w s (true::xs) ↔ ∃ p ys, xs=p::ys ∧ Index w w s p ys := by
  constructor
  · rintro ⟨c,f,h,hs,hf⟩
    cases c with
    | nil => simp [codeC] at h
    | cons t c =>
      obtain ⟨p,i⟩ := t
      refine ⟨p,_,(List.cons.inj h).2,i,codeC c ++ codeF f,?_,c,f,rfl,?_,hf⟩
      · simp [codeC,List.append_assoc,List.flatMap_def]
      · simpa [value,or_assoc] using hs
  · rintro ⟨p,ys,rfl,i,rest,rfl,c,f,rfl,hs,hf⟩
    refine ⟨(p,i)::c,f,?_,?_,hf⟩
    · simp [codeC,litCode,List.append_assoc]
    · simpa [value,or_assoc] using hs

private theorem index_nil (w ws : List Bool) (s p : Bool) : ¬Index w ws s p [] := by
  rintro ⟨i,r,h,_⟩
  cases i <;> simp [List.replicate_succ] at h

private theorem index_false (w ws xs : List Bool) (s p : Bool) :
    Index w ws s p (false::xs) ↔ Tail w (s || (head ws == p)) xs := by
  constructor
  · rintro ⟨i,r,h,hT⟩
    cases i with
    | zero => cases ws <;> simpa [head,(List.cons.inj h).2] using hT
    | succ i => simp [List.replicate_succ] at h
  · intro h
    exact ⟨0,xs,rfl,by cases ws <;> simpa [head] using h⟩

private theorem index_true (w ws xs : List Bool) (s p : Bool) :
    Index w ws s p (true::xs) ↔ Index w ws.tail s p xs := by
  constructor
  · rintro ⟨i,r,h,hT⟩
    cases i with
    | zero => simp at h
    | succ i =>
      refine ⟨i,r,(List.cons.inj h).2,?_⟩
      cases ws <;> simpa using hT
  · rintro ⟨i,r,h,hT⟩
    exact ⟨i+1,r,by simp [List.replicate_succ,h],by cases ws <;> simpa using hT⟩

private def Meaning (w ws x : List Bool) : Mode → Prop
  | .start => Whole w x
  | .body s => Tail w s x
  | .sign s => ∃ p ys, x=p::ys ∧ Index w w s p ys
  | .unary s p => Index w ws s p x
  | .bad => False

private theorem scan_spec (w xs : List Bool) (s : Mode) (ws : List Bool) :
    scan w xs s ws = true ↔ Meaning w ws xs s := by
  induction xs generalizing s ws with
  | nil =>
    cases s <;> simp [scan,Meaning,whole_cases,tail_nil,index_nil]
  | cons b xs ih =>
    rw [scan,ih]
    cases s <;> cases b <;>
      simp [tick,shift,move,Meaning,whole_cases,tail_true,tail_false,index_true,index_false]
    rename_i sat
    cases sat <;> simp



private inductive Tape | input | hist | form deriving DecidableEq
private instance : Fintype Tape := ⟨{.input,.hist,.form},by intro t; cases t <;> simp⟩
private inductive Label | copy | reverse | scan | rewind | clearHist | clearInput
  deriving DecidableEq
private instance : Fintype Label := ⟨{.copy,.reverse,.scan,.rewind,.clearHist,.clearInput},
  by intro t; cases t <;> simp⟩
private abbrev Reg := Mode × Option Bool × Option Bool
private def blank (s : Mode) : Reg := (s,none,none)
private def setX (v : Reg) (b : Option Bool) : Reg := (v.1,b,v.2.2)
private def setW (v : Reg) (b : Option Bool) : Reg := (v.1,v.2.1,b)
private def tapes (input hist form : List Bool) : Tape → List Bool
  | .input => input | .hist => hist | .form => form
@[simp] private lemma getI (i h f : List Bool) : tapes i h f .input = i := rfl
@[simp] private lemma getH (i h f : List Bool) : tapes i h f .hist = h := rfl
@[simp] private lemma getF (i h f : List Bool) : tapes i h f .form = f := rfl
@[simp] private lemma updI (i h f v : List Bool) :
    Function.update (tapes i h f) .input v = tapes v h f := by funext k; cases k <;> rfl
@[simp] private lemma updH (i h f v : List Bool) :
    Function.update (tapes i h f) .hist v = tapes i v f := by funext k; cases k <;> rfl
@[simp] private lemma updF (i h f v : List Bool) :
    Function.update (tapes i h f) .form v = tapes i h v := by funext k; cases k <;> rfl

private abbrev Stmt := TM2.Stmt (fun _ : Tape => Bool) Label Reg
private def jump (l : Label) : Stmt := .load (fun v => blank v.1) (.goto (fun _ => l))
private def skipBit : Stmt → Stmt := .pop .input fun v _ => v
private def stepTo (l : Label) : Stmt :=
  .load (fun v => blank (tick v.1 (v.2.1.getD false) (v.2.2.getD false))) (.goto fun _ => l)

private def updateCursor : Stmt :=
  .branch (fun v => move v.1 (v.2.1.getD false) == .home) (stepTo .rewind)
    (.branch (fun v => (move v.1 (v.2.1.getD false) == .advance) && v.2.2.isSome)
      (skipBit (skipBit (skipBit (.push .hist (fun v => v.2.2.getD false) (stepTo .scan)))))
      (stepTo .scan))

private def program : Label → Stmt
  | .copy => .pop .input setW <|
      .branch (fun v => v.2.2.getD false)
        (skipBit (skipBit (.pop .input setW (skipBit (skipBit
          (.push .hist (fun v => v.2.2.getD false) (jump .copy))))))) (jump .reverse)
  | .reverse => .pop .hist setW <| .branch (fun v => v.2.2.isSome)
      (.push .form (fun v => v.2.2.getD false) (jump .reverse)) (jump .scan)
  | .scan => .pop .form setX <| .branch (fun v => v.2.1.isSome)
      (.pop .input setW <| .branch (fun v => v.2.2.isSome)
        (.peek .input setW (.push .input (fun _ => true) updateCursor)) updateCursor)
      (jump .clearHist)
  | .rewind => .pop .hist setW <| .branch (fun v => v.2.2.isSome)
      (.push .input (fun _ => false) (.push .input (fun v => v.2.2.getD false)
        (.push .input (fun _ => true) (jump .rewind)))) (jump .scan)
  | .clearHist => .pop .hist setW <| .branch (fun v => v.2.2.isSome)
      (jump .clearHist) (jump .clearInput)
  | .clearInput => .pop .input setW <| .branch (fun v => v.2.2.isSome)
      (jump .clearInput) (.push .input (fun v => v.1 == .start)
        (.load (fun _ => blank .start) .halt))

private def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .input
  Γ _ := Bool
  Λ := Label
  main := .copy
  σ := Reg
  initialState := blank .start
  m := program

private abbrev Cfg := TM2.Cfg (fun _ : Tape => Bool) Label Reg
private def cfg (l : Option Label) (s : Mode) (i h f : List Bool) : Cfg :=
  ⟨l,blank s,tapes i h f⟩
private def Run (a b : Cfg) (bound : ℕ) : Prop :=
  ∃ k ≤ bound, (fun v : Option Cfg => v.bind (TM2.step program))^[k] (some a) = some b

private lemma next {a b c : Cfg} {m : ℕ} (step : TM2.step program a = some b) (run : Run b c m) :
    Run a c (m+1) := by
  obtain ⟨k,hk,h⟩ := run
  refine ⟨k+1,by omega,?_⟩
  rw [Function.iterate_succ_apply]
  simpa only [Option.bind_some,step] using h

private lemma once {a b : Cfg} (step : TM2.step program a = some b) : Run a b 1 :=
  next step (show Run b b 0 from ⟨0,le_rfl,rfl⟩)

private lemma chain {a b c : Cfg} {n m : ℕ} (h : Run a b n) (h' : Run b c m) :
    Run a c (n+m) := by
  obtain ⟨i,hi,e⟩ := h
  obtain ⟨j,hj,e'⟩ := h'
  exact ⟨j+i,by omega,by rw [Function.iterate_add_apply,e,e']⟩

private lemma widen {a b : Cfg} {n m : ℕ} (h : Run a b n) (le : n ≤ m) : Run a b m := by
  obtain ⟨k,hk,r⟩ := h
  exact ⟨k,hk.trans le,r⟩

private def bits : List Bool → List Bool
  | [] => []
  | b::bs => true::b::false::bits bs
private def inputX : List Bool → List Bool
  | [] => [false]
  | b::bs => true::true::true::b::true::false::inputX bs

private lemma bits_eq (x : List Bool) : BitstringEncoding.bitEncode x = bits x := by
  induction x with
  | nil => rfl
  | cons b bs ih =>
    change true::b::false::BitstringEncoding.bitEncode bs = true::b::false::bits bs
    rw [ih]

private lemma input_eq (x : List Bool) : BitstringEncoding.delimit (bits x) = inputX x := by
  induction x with
  | nil => rfl
  | cons b bs ih => simp [bits,inputX,BitstringEncoding.delimit,ih]

private lemma bits_len (x : List Bool) : (bits x).length=3*x.length := by
  induction x <;> simp_all [bits,Nat.mul_succ]
private lemma inp_len (x : List Bool) : (inputX x).length=6*x.length+1 := by
  induction x <;> simp_all [inputX,Nat.mul_succ]

private lemma copy_run (x rest acc : List Bool) :
    Run (cfg (some .copy) .start (inputX x ++ rest) acc [])
      (cfg (some .reverse) .start rest (x.reverse++acc) []) (x.length+1) := by
  induction x generalizing acc with
  | nil => apply once; simp [cfg,program,inputX,setW,jump,blank]
  | cons b bs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
      (next (a := cfg (some .copy) .start (inputX (b::bs) ++ rest) acc [])
        (by simp [cfg,program,inputX,setW,jump,blank,skipBit]) (ih (b::acc)))

private lemma rev_run (x rest acc : List Bool) :
    Run (cfg (some .reverse) .start rest x acc)
      (cfg (some .scan) .start rest [] (x.reverse++acc)) (x.length+1) := by
  induction x generalizing acc with
  | nil => apply once; simp [cfg,program,setW,jump,blank]
  | cons b bs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
      (next (a := cfg (some .reverse) .start rest (b::bs) acc)
        (by simp [cfg,program,setW,jump,blank]) (ih (b::acc)))

private lemma home_run (s : Mode) (used ws xs : List Bool) :
    Run (cfg (some .rewind) s (bits ws) used xs)
      (cfg (some .scan) s (bits (used.reverse++ws)) [] xs) (used.length+1) := by
  induction used generalizing ws with
  | nil => apply once; simp [cfg,program,setW,jump,blank]
  | cons b bs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
      (next (a := cfg (some .rewind) s (bits ws) (b::bs) xs)
        (by simp [cfg,program,setW,jump,blank,bits]) (ih (b::ws)))

private lemma clean_input (s : Mode) (i : List Bool) :
    Run (cfg (some .clearInput) s i [] [])
      (cfg none .start [s==.start] [] []) (i.length+1) := by
  induction i with
  | nil => apply once; simp [cfg,program,setW,jump,blank]
  | cons b bs ih => exact next (by simp [cfg,program,setW,jump,blank]) ih

private lemma clean_hist (s : Mode) (i used : List Bool) :
    Run (cfg (some .clearHist) s i used []) (cfg (some .clearInput) s i [] []) (used.length+1) := by
  induction used with
  | nil => apply once; simp [cfg,program,setW,jump,blank]
  | cons b bs ih => exact next (by simp [cfg,program,setW,jump,blank]) ih


private lemma read_stay (s : Mode) (b : Bool) (ws used xs : List Bool) (hm : move s b=.stay) :
    TM2.step program (cfg (some .scan) s (bits ws) used (b::xs)) =
      some (cfg (some .scan) (tick s b (head ws)) (bits ws) used xs) := by
  cases ws <;> simp [cfg,program,setX,setW,blank,bits,head,updateCursor,stepTo,hm] <;> rfl

private def entered (used ws : List Bool) : List Bool :=
  match ws with | [] => used | b::_ => b::used

private lemma read_adv (s : Mode) (b : Bool) (ws used xs : List Bool) (hm : move s b=.advance) :
    TM2.step program (cfg (some .scan) s (bits ws) used (b::xs)) =
      some (cfg (some .scan) (tick s b (head ws)) (bits ws.tail) (entered used ws) xs) := by
  cases ws <;> simp [cfg,program,setX,setW,blank,bits,head,updateCursor,stepTo,hm,skipBit,entered] <;> rfl

private lemma read_home (s : Mode) (b : Bool) (ws used xs : List Bool) (hm : move s b=.home) :
    TM2.step program (cfg (some .scan) s (bits ws) used (b::xs)) =
      some (cfg (some .rewind) (tick s b (head ws)) (bits ws) used xs) := by
  cases ws <;> simp [cfg,program,setX,setW,blank,bits,head,updateCursor,stepTo,hm]

private lemma scan_run (w xs : List Bool) (s : Mode) (ws used : List Bool)
    (ok : used.reverse++ws=w) :
    Run (cfg (some .scan) s (bits ws) used xs)
      (cfg none .start [scan w xs s ws] [] []) ((w.length+3)*xs.length+3*w.length+3) := by
  induction xs generalizing s ws used with
  | nil =>
    have l := congrArg List.length ok
    simp only [List.length_append,List.length_reverse] at l
    have after := chain (clean_hist s (bits ws) used) (clean_input s (bits ws))
    apply widen (next (b := cfg (some .clearHist) s (bits ws) used [])
      (by simp [cfg,program,setX,jump,blank]) after)
    simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,bits_len]
    omega
  | cons b xs ih =>
    have l := congrArg List.length ok
    simp only [List.length_append,List.length_reverse] at l
    rw [scan]
    simp only [List.length_cons,Nat.mul_succ]
    cases hm : move s b with
    | stay =>
      exact widen (next (read_stay s b ws used xs hm) (ih _ _ _ ok)) (by omega)
    | advance =>
      have good : (entered used ws).reverse++ws.tail=w := by
        cases ws <;> simpa [entered,List.append_assoc] using ok
      exact widen (next (read_adv s b ws used xs hm) (ih _ _ _ good)) (by omega)
    | home =>
      have home := home_run (tick s b (head ws)) used ws xs
      rw [ok] at home
      have tail := ih (tick s b (head ws)) w [] (by simp)
      exact widen (chain (next (read_home s b ws used xs hm) home) tail) (by omega)

private def verify (p : List Bool × List Bool) : Bool := scan p.2 p.1 .start p.2

private theorem poly : IsPolyTime verify := by
  refine ⟨{
    tm := machine
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := (Polynomial.X + Polynomial.C 10)^2
    outputsFun := ?_ }⟩
  rintro ⟨x,w⟩
  let word := inputX x ++ bits w
  let ans := scan w x .start w
  have encode : BitstringEncoding.bitEncode (x,w) = word := by
    change BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++ BitstringEncoding.bitEncode w = _
    rw [bits_eq,bits_eq,input_eq]
  have ci : initList machine word = cfg (some .copy) .start word [] [] := by
    unfold initList cfg
    apply congrArg (fun st => (⟨some Label.copy,blank .start,st⟩ : Cfg))
    funext k; cases k <;> rfl
  have co : haltList machine [ans] = cfg none .start [ans] [] [] := by
    unfold haltList cfg
    apply congrArg (fun st => (⟨none,blank .start,st⟩ : Cfg))
    funext k; cases k <;> rfl
  have cp := copy_run x (bits w) []
  have rev := rev_run x.reverse (bits w) []
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at cp rev
  have total := chain (chain cp rev) (scan_run w x .start w [] (by simp))
  let k := Classical.choose total
  have hk := (Classical.choose_spec total).1
  have run := (Classical.choose_spec total).2
  refine ⟨⟨k,?_⟩,?_⟩
  · change (fun o : Option Cfg => o.bind (TM2.step program))^[k]
      (some (initList machine (List.map (id : Bool → Bool) (BitstringEncoding.bitEncode (x,w))))) =
      some (haltList machine [ans])
    rw [encode]
    let iter (c : Cfg) := (fun o : Option Cfg => o.bind (TM2.step program))^[k] (some c)
    have startEq := (congrArg (fun y : List Bool => initList machine y) (List.map_id word)).trans ci
    exact (congrArg iter startEq).trans (run.trans (congrArg some co.symm))
  · change k ≤ Polynomial.eval (BitstringEncoding.bitEncode (x,w)).length ((Polynomial.X+Polynomial.C 10)^2)
    rw [encode]
    simp only [word,List.length_append,inp_len,bits_len,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_C,Polynomial.eval_X]
    apply hk.trans
    nlinarith [Nat.zero_le (x.length^2),Nat.zero_le (w.length^2),
      Nat.zero_le (x.length*w.length)]

end UnaryVerifier

open UnaryVerifier in
theorem OMA.Leaf1.solve :
    OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1.H1 := by
  refine ⟨verify,poly,?_⟩
  intro x w
  have h := scan_spec w x .start w
  change scan w x .start w = true ↔ ∃ F, x=codeF F ∧ ∀ c ∈ F, ∃ t ∈ c, (w[t.2]?).getD false=t.1
  simpa only [Meaning,Whole,valid,value,beq_iff_eq] using h



-- Step DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP.R1.H1.R1.H2: hypothesis H2 of reduction DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP.R1.H1.R1

/-!
Let `L` be the length of the encoding of `F` and take `w = [a 0, …, a (L - 1)]`. A literal `t` of
a clause of `F` contributes `t.2 + 3` symbols to the encoding, so `t.2 < L` and the entry of `w`
at position `t.2` is `a t.2`.
-/

namespace OMA

theorem len_le {α β : Type} (f : α → List β) : ∀ (l : List α) (x : α), x ∈ l →
    (f x).length ≤ (l.flatMap f).length := by
  intro l
  induction l with
  | nil =>
    intro x hx
    simp at hx
  | cons y ys ih =>
    intro x hx
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp hx with h | h
    · rw [h]
      omega
    · have := ih x h
      omega

end OMA

theorem OMA.Leaf2.solve :
    OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1.H2 := by
  unfold OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1.H2
  intro F a
  refine ⟨(List.range (F.flatMap (fun c => c.flatMap
    (fun t => [true, t.1] ++ List.replicate t.2 true ++ [false]) ++ [false])).length).map a,
    by simp, ?_⟩
  intro c hc t ht
  have h1 := OMA.len_le
    (fun t : Bool × ℕ => [true, t.1] ++ List.replicate t.2 true ++ [false]) c t ht
  have h2 := OMA.len_le (fun c : List (Bool × ℕ) => c.flatMap
    (fun t => [true, t.1] ++ List.replicate t.2 true ++ [false]) ++ [false]) F c hc
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
    at h1 h2
  have hlt : t.2 < (F.flatMap (fun c => c.flatMap
      (fun t => [true, t.1] ++ List.replicate t.2 true ++ [false]) ++ [false])).length := by
    omega
  generalize (F.flatMap (fun c => c.flatMap
      (fun t => [true, t.1] ++ List.replicate t.2 true ++ [false]) ++ [false])).length = L
    at hlt ⊢
  rw [List.getElem?_map, List.getElem?_range hlt]
  rfl

theorem OMA.solution : OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1.H1 :=
  OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1.main OMA.Leaf1.solve OMA.Leaf2.solve
