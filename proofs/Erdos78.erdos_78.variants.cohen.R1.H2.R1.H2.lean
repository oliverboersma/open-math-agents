import OMAReductions.R_Erdos78_erdos_78_variants_cohen_R1_H2_R1

/-! Order the two canonical binary labels in linear time while carrying an
untouched dimension prefix. The comparator updates its order bit whenever
a more significant pair differs. Both stacks retain the original payload bits.
The bounded-run conventions follow @marcusbuffett's unary verifier and the
merged tape-machine constructions by @steveDOTdigital and @ashnewmanjones. -/
open Turing Computability ComplexityTheory
namespace OMA.CohenSort
private inductive Tape | input | prefixTape | low | left | right deriving DecidableEq
private instance : Fintype Tape := ⟨{.input,.prefixTape,.low,.left,.right},by intro t; cases t <;> simp⟩
private inductive Label | first | second | reverse | scan | big | small | prefixOut deriving DecidableEq
private instance : Fintype Label := ⟨{.first,.second,.reverse,.scan,.big,.small,.prefixOut},by intro t; cases t <;> simp⟩
private def tapes (i p lo a b : List Bool) : Tape → List Bool
  | .input => i
  | .prefixTape => p
  | .low => lo
  | .left => a
  | .right => b
@[simp] private lemma get_input (i p lo a b : List Bool) : tapes i p lo a b .input = i := rfl
@[simp] private lemma set_input (i p lo a b w : List Bool) : Function.update (tapes i p lo a b) .input w = tapes w p lo a b := by funext t; cases t <;> rfl
@[simp] private lemma get_prefixTape (i p lo a b : List Bool) : tapes i p lo a b .prefixTape = p := rfl
@[simp] private lemma set_prefixTape (i p lo a b w : List Bool) : Function.update (tapes i p lo a b) .prefixTape w = tapes i w lo a b := by funext t; cases t <;> rfl
@[simp] private lemma get_low (i p lo a b : List Bool) : tapes i p lo a b .low = lo := rfl
@[simp] private lemma set_low (i p lo a b w : List Bool) : Function.update (tapes i p lo a b) .low w = tapes i p w a b := by funext t; cases t <;> rfl
@[simp] private lemma get_left (i p lo a b : List Bool) : tapes i p lo a b .left = a := rfl
@[simp] private lemma set_left (i p lo a b w : List Bool) : Function.update (tapes i p lo a b) .left w = tapes i p lo w b := by funext t; cases t <;> rfl
@[simp] private lemma get_right (i p lo a b : List Bool) : tapes i p lo a b .right = b := rfl
@[simp] private lemma set_right (i p lo a b w : List Bool) : Function.update (tapes i p lo a b) .right w = tapes i p lo a w := by funext t; cases t <;> rfl

private abbrev Reg := Bool × Option Bool × Option Bool
private abbrev Stmt := TM2.Stmt (fun _ : Tape => Bool) Label Reg
private def blank (s : Bool) : Reg := (s,none,none)
private def jump (l : Label) : Stmt := .load (fun r => blank r.1) (.goto fun _ => l)
private def popA (k : Tape) : Stmt → Stmt := .pop k (fun r v => (r.1,v,r.2.2))
private def popB (k : Tape) : Stmt → Stmt := .pop k (fun r v => (r.1,r.2.1,v))
private def digitA (r : Reg) := r.2.1.getD false
private def digitB (r : Reg) := r.2.2.getD false
private def putA (k : Tape) : Stmt → Stmt := .push k digitA
private def putB (k : Tape) : Stmt → Stmt := .push k digitB
private def marker (b : Bool) : Stmt → Stmt := .push .input (fun _ => b)
private def readBlock (k : Tape) (loop done_ : Label) : Stmt :=
  popA .input (.branch digitA (popA .input (putA k (jump loop))) (jump done_))
private def chooseOrder (s a b : Bool) : Bool := if a=b then s else a
private def scanNext : Stmt :=
  .load (fun r => blank (chooseOrder r.1 (digitA r) (digitB r))) (.goto fun _ => .scan)
private def saveB : Stmt := .branch (fun r => r.2.2.isSome) (putB .right scanNext) scanNext
private def emit (k : Tape) (tag : Bool) (loop : Label) (done_ : Stmt) : Stmt :=
  popA k (.branch (fun r => r.2.1.isSome)
    (putA .input (if tag then marker true (jump loop) else jump loop)) done_)
private def program : Label → Stmt
  | .first => readBlock .prefixTape .first .second
  | .second => readBlock .left .second .reverse
  | .reverse => popA .left (.branch (fun r => r.2.1.isSome) (putA .low (jump .reverse)) (jump .scan))
  | .scan => popA .low (popB .input (.branch (fun r => r.2.1.isSome)
      (putA .left saveB) (.branch (fun r => r.2.2.isSome) (putB .right scanNext) (jump .big))))
  | .big => .branch Prod.fst (emit .left false .big (marker false (jump .small)))
      (emit .right false .big (marker false (jump .small)))
  | .small => .branch Prod.fst (emit .right true .small (marker false (jump .prefixOut)))
      (emit .left true .small (marker false (jump .prefixOut)))
  | .prefixOut => emit .prefixTape true .prefixOut (.load (fun _ => blank false) .halt)

private def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .input
  Γ _ := Bool
  Λ := Label
  main := .first
  σ := Reg
  initialState := blank false
  m := program

private abbrev Cfg := TM2.Cfg (fun _ : Tape => Bool) Label Reg
private def cfg (l : Option Label) (s : Bool) (i p lo a b : List Bool) : Cfg :=
  ⟨l,blank s,tapes i p lo a b⟩

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


private def value : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat + 2*value bs

private lemma value_pos (p : PosNum) : value (encodePosNum p) = (p : ℕ) := by
  induction p <;> simp_all [encodePosNum,value] <;> omega

private lemma value_num (n : Num) : value (encodeNum n) = (n : ℕ) := by
  cases n with
  | zero => rfl
  | pos p => exact value_pos p

private lemma value_nat (n : ℕ) : value (encodeNat n) = n :=
  (value_num _).trans (Num.to_of_nat n)

private def wins (s : Bool) (a b : List Bool) :=
  decide (value b < value a ∨ (value b = value a ∧ s = true))

private lemma wins_cons (s a b : Bool) (x y : List Bool) :
    wins (chooseOrder s a b) x y = wins s (a::x) (b::y) := by
  unfold wins
  apply decide_eq_decide.mpr
  cases s <;> cases a <;> cases b <;> simp [chooseOrder,value] <;> omega

private lemma wins_padL (s : Bool) (ys : List Bool) : wins s (false::[]) ys = wins s [] ys := rfl
private lemma wins_padR (s : Bool) (xs : List Bool) : wins s xs (false::[]) = wins s xs [] := rfl

private def tags (x : List Bool) := x.flatMap (fun b => [true,b])
private lemma tags_delimit (x t : List Bool) : tags x ++ false::t = BitstringEncoding.delimit x ++ t := by
  induction x with
  | nil => rfl
  | cons b x ih => exact congrArg (fun s => true :: b :: s) ih

private lemma first_run (x i p lo a b : List Bool) (s : Bool) :
    Run (cfg (some .first) s (BitstringEncoding.delimit x ++ i) p lo a b)
      (cfg (some .second) s i (x.reverse++p) lo a b) (x.length+1) := by
  induction x generalizing p with
  | nil => apply once; simp [cfg,program,jump,popA,putA,digitA,blank,readBlock,BitstringEncoding.delimit]
  | cons d x ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
      (next (a := cfg (some .first) s (BitstringEncoding.delimit (d::x) ++ i) p lo a b) (by simp [cfg,program,jump,popA,putA,digitA,blank,readBlock,BitstringEncoding.delimit]) (ih (d::p)))

private lemma second_run (x i p lo a b : List Bool) (s : Bool) :
    Run (cfg (some .second) s (BitstringEncoding.delimit x ++ i) p lo a b)
      (cfg (some .reverse) s i p lo (x.reverse++a) b) (x.length+1) := by
  induction x generalizing a with
  | nil => apply once; simp [cfg,program,jump,popA,putA,digitA,blank,readBlock,BitstringEncoding.delimit]
  | cons d x ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
      (next (a := cfg (some .second) s (BitstringEncoding.delimit (d::x) ++ i) p lo a b) (by simp [cfg,program,jump,popA,putA,digitA,blank,readBlock,BitstringEncoding.delimit]) (ih (d::a)))

private lemma reverse_run (i p lo a b : List Bool) (s : Bool) :
    Run (cfg (some .reverse) s i p lo a b)
      (cfg (some .scan) s i p (a.reverse++lo) [] b) (a.length+1) := by
  induction a generalizing lo with
  | nil => apply once; simp [cfg,program,jump,popA,putA,digitA,blank]
  | cons d a ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
      (next (a := cfg (some .reverse) s i p lo (d::a) b) (by simp [cfg,program,jump,popA,putA,digitA,blank]) (ih (d::lo)))

private lemma bigLeft (i p lo a b : List Bool) :
    Run (cfg (some .big) true i p lo a b)
      (cfg (some .small) true (false::(a.reverse ++ i)) p lo [] b) (a.length+1) := by
  induction a generalizing i with
  | nil => apply once; simp [cfg,program,jump,popA,marker,emit,putA,digitA,blank]
  | cons d a ih =>
    simpa [tags,List.append_assoc] using
      (next (a := cfg (some .big) true i p lo (d::a) b) (by simp [cfg,program,jump,popA,marker,emit,putA,digitA,blank]) (ih (d::i)))

private lemma bigRight (i p lo a b : List Bool) :
    Run (cfg (some .big) false i p lo a b)
      (cfg (some .small) false (false::(b.reverse ++ i)) p lo a []) (b.length+1) := by
  induction b generalizing i with
  | nil => apply once; simp [cfg,program,jump,popA,marker,emit,putA,digitA,blank]
  | cons d b ih =>
    simpa [tags,List.append_assoc] using
      (next (a := cfg (some .big) false i p lo a (d::b)) (by simp [cfg,program,jump,popA,marker,emit,putA,digitA,blank]) (ih (d::i)))

private lemma smallLeft (i p lo a b : List Bool) :
    Run (cfg (some .small) false i p lo a b)
      (cfg (some .prefixOut) false (false::(tags a.reverse ++ i)) p lo [] b) (a.length+1) := by
  induction a generalizing i with
  | nil => apply once; simp [cfg,program,jump,popA,marker,emit,putA,digitA,blank,tags]
  | cons d a ih =>
    simpa [tags,List.append_assoc] using
      (next (a := cfg (some .small) false i p lo (d::a) b) (by simp [cfg,program,jump,popA,marker,emit,putA,digitA,blank]) (ih (true::d::i)))

private lemma smallRight (i p lo a b : List Bool) :
    Run (cfg (some .small) true i p lo a b)
      (cfg (some .prefixOut) true (false::(tags b.reverse ++ i)) p lo a []) (b.length+1) := by
  induction b generalizing i with
  | nil => apply once; simp [cfg,program,jump,popA,marker,emit,putA,digitA,blank,tags]
  | cons d b ih =>
    simpa [tags,List.append_assoc] using
      (next (a := cfg (some .small) true i p lo a (d::b)) (by simp [cfg,program,jump,popA,marker,emit,putA,digitA,blank]) (ih (true::d::i)))

private lemma prefix_run (i p lo a b : List Bool) (s : Bool) :
    Run (cfg (some .prefixOut) s i p lo a b)
      (cfg none false (tags p.reverse ++ i) [] lo a b) (p.length+1) := by
  induction p generalizing i with
  | nil => apply once; simp [cfg,program,jump,popA,marker,emit,putA,digitA,blank,tags]
  | cons d p ih =>
    simpa [tags,List.append_assoc] using
      (next (a := cfg (some .prefixOut) s i (d::p) lo a b) (by simp [cfg,program,jump,popA,marker,emit,putA,digitA,blank]) (ih (true::d::i)))

private lemma scan_run (xs ys p a b : List Bool) (s : Bool) :
    Run (cfg (some .scan) s ys p xs a b)
      (cfg (some .big) (wins s xs ys) [] p [] (xs.reverse++a) (ys.reverse++b))
      (xs.length+ys.length+1) := by
  induction xs generalizing ys a b s with
  | nil =>
    induction ys generalizing a b s with
    | nil =>
      cases s <;> apply once <;> simp [cfg,program,jump,popA,popB,blank,wins,value]
    | cons y ys ih =>
      have h := next (a := cfg (some .scan) s (y::ys) p [] a b)
        (by simp [cfg,program,jump,popA,popB,putA,putB,digitA,digitB,blank,scanNext,saveB])
        (ih a (y::b) (chooseOrder s false y))
      rw [wins_cons,wins_padL] at h
      simpa [List.append_assoc] using h
  | cons x xs ih =>
    cases ys with
    | nil =>
      have h := next (a := cfg (some .scan) s [] p (x::xs) a b)
        (by simp [cfg,program,jump,popA,popB,putA,putB,digitA,digitB,blank,scanNext,saveB])
        (ih [] (x::a) b (chooseOrder s x false))
      rw [wins_cons,wins_padR] at h
      simpa [List.append_assoc] using h
    | cons y ys =>
      have h := next (a := cfg (some .scan) s (y::ys) p (x::xs) a b)
        (by simp [cfg,program,jump,popA,popB,putA,putB,digitA,digitB,blank,scanNext,saveB])
        (ih ys (x::a) (y::b) (chooseOrder s x y))
      rw [wins_cons] at h
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons]
      exact widen h (by omega)

private lemma sorted_run (d x y : List Bool) :
    let swap := wins false x y
    let u := if swap then y else x
    let v := if swap then x else y
    Run (cfg (some .first) false (BitstringEncoding.delimit d ++ BitstringEncoding.delimit x ++ y) [] [] [] [])
      (cfg none false (BitstringEncoding.delimit d ++ BitstringEncoding.delimit u ++ v) [] [] [] [])
      (5*(d.length+x.length+y.length)+8) := by
  dsimp only
  have f := first_run d (BitstringEncoding.delimit x ++ y) [] [] [] [] false
  have t := second_run x y d.reverse [] [] [] false
  have r := reverse_run y d.reverse [] x.reverse [] false
  have c := scan_run x y d.reverse [] [] false
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at f t r c
  have front := chain (chain (chain f t) r) c
  by_cases h : wins false x y = true
  · simp only [h,if_true] at front ⊢
    have g := bigLeft [] d.reverse [] x.reverse y.reverse
    have k := smallRight (false::x) d.reverse [] [] y.reverse
    have o := prefix_run (false::(BitstringEncoding.delimit y++x)) d.reverse [] [] [] true
    simp only [List.reverse_reverse,List.append_nil,List.length_reverse,tags_delimit] at g k o
    have total := chain (chain (chain front g) k) o
    simpa only [List.append_assoc] using widen total (show _ ≤ 5*(d.length+x.length+y.length)+8 by omega)
  · have hn : wins false x y = false := Bool.eq_false_iff.mpr h
    simp only [hn,Bool.false_eq_true,if_false] at front ⊢
    have g := bigRight [] d.reverse [] x.reverse y.reverse
    have k := smallLeft (false::y) d.reverse [] x.reverse []
    have o := prefix_run (false::(BitstringEncoding.delimit x++y)) d.reverse [] [] [] false
    simp only [List.reverse_reverse,List.append_nil,List.length_reverse,tags_delimit] at g k o
    have total := chain (chain (chain front g) k) o
    simpa only [List.append_assoc] using widen total (show _ ≤ 5*(d.length+x.length+y.length)+8 by omega)

theorem poly : OMA.R_Erdos78_erdos_78_variants_cohen_R1_H2_R1.H2 := by
  refine ⟨{
    tm := machine
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 5 * Polynomial.X + Polynomial.C 8
    outputsFun := ?_ }⟩
  rintro ⟨d,x,y⟩
  let word := BitstringEncoding.bitEncode (d,x,y)
  let answer := BitstringEncoding.bitEncode (d,min x y,max x y)
  have ci : initList machine word = cfg (some .first) false word [] [] [] [] := by
    unfold initList cfg
    apply congrArg (fun st => (⟨some Label.first,blank false,st⟩ : Cfg))
    funext k; cases k <;> rfl
  have co : haltList machine answer = cfg none false answer [] [] [] [] := by
    unfold haltList cfg
    apply congrArg (fun st => (⟨none,blank false,st⟩ : Cfg))
    funext k; cases k <;> rfl
  have h := sorted_run (encodeNat d) (encodeNat x) (encodeNat y)
  have hw : wins false (encodeNat x) (encodeNat y) = decide (y<x) := by simp [wins,value_nat]
  dsimp only at h
  rw [hw] at h
  have hu : (if decide (y<x) then encodeNat y else encodeNat x) = encodeNat (min x y) := by
    by_cases e : y<x
    · simp [e,min_eq_right e.le]
    · simp [e,min_eq_left (le_of_not_gt e)]
  have hv : (if decide (y<x) then encodeNat x else encodeNat y) = encodeNat (max x y) := by
    by_cases e : y<x
    · simp [e,max_eq_left e.le]
    · simp [e,max_eq_right (le_of_not_gt e)]
  rw [hu,hv] at h
  have start : word = BitstringEncoding.delimit (encodeNat d) ++
      BitstringEncoding.delimit (encodeNat x) ++ encodeNat y := by
    change _ ++ (_ ++ _) = _
    rw [List.append_assoc]
    rfl
  have finish : answer = BitstringEncoding.delimit (encodeNat d) ++
      BitstringEncoding.delimit (encodeNat (min x y)) ++ encodeNat (max x y) := by
    change _ ++ (_ ++ _) = _
    rw [List.append_assoc]
    rfl
  rw [← start,← finish] at h
  let k := Classical.choose h
  have hk := (Classical.choose_spec h).1
  have run := (Classical.choose_spec h).2
  refine ⟨⟨k,?_⟩,?_⟩
  · change (fun o : Option Cfg => o.bind (TM2.step program))^[k]
       (some (initList machine (List.map (id : Bool → Bool) word))) =
         some (haltList machine (List.map (id : Bool → Bool) answer))
    let iter (c : Cfg) := (fun o : Option Cfg => o.bind (TM2.step program))^[k] (some c)
    have a := (congrArg (fun y : List Bool => initList machine y) (List.map_id word)).trans ci
    have b := (congrArg (fun y : List Bool => haltList machine y) (List.map_id answer)).trans co
    exact (congrArg iter a).trans (run.trans (congrArg some b.symm))
  · change k ≤ Polynomial.eval word.length (Polynomial.C 5 * Polynomial.X + Polynomial.C 8)
    rw [start]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C,
      List.length_append,BitstringEncoding.length_delimit]
    omega

end OMA.CohenSort

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_cohen_R1_H2_R1.H2 := OMA.CohenSort.poly
