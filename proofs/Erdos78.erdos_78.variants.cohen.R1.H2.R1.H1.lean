import OMAReductions.R_Erdos78_erdos_78_variants_cohen_R1_H2_R1

/-! Counting self-delimited unary symbols with a binary stack counter.
The input stack keeps the encoded pair of labels below the scanned prefix.
The bounded-run conventions follow the merged unary verifier of @marcusbuffett
and the tape-machine proofs of @steveDOTdigital and @ashnewmanjones. -/
open Turing Computability ComplexityTheory
namespace OMA.CohenLength

private inductive Tape | input | hist | form deriving DecidableEq
private instance : Fintype Tape := ⟨{.input,.hist,.form},by intro t; cases t <;> simp⟩
private inductive Label | read | carry | restore | reverse | write deriving DecidableEq
private instance : Fintype Label := ⟨{.read,.carry,.restore,.reverse,.write},by intro t; cases t <;> simp⟩
private abbrev Reg := Option Bool
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
private def jump (l : Label) : Stmt := .load (fun _ => none) (.goto fun _ => l)
private def skipBit : Stmt → Stmt := .pop .input fun v _ => v
private def takeB (k : Tape) : Stmt → Stmt := .pop k fun _ x => x
private def pushB (k : Tape) (b : Bool) : Stmt → Stmt := .push k fun _ => b
private def program : Label → Stmt
  | .read => takeB .input <| .branch (fun r => r.getD false)
      (skipBit (skipBit (skipBit (skipBit (skipBit (jump .carry))))))
      (pushB .input false (jump .reverse))
  | .carry => takeB .hist <| .branch (fun r => r.getD false)
      (pushB .form false (jump .carry)) (pushB .hist true (jump .restore))
  | .restore => takeB .form <| .branch Option.isSome
      (pushB .hist false (jump .restore)) (jump .read)
  | .reverse => takeB .hist <| .branch Option.isSome
      (.push .form (fun r => r.getD false) (jump .reverse)) (jump .write)
  | .write => takeB .form <| .branch Option.isSome
      (.push .input (fun r => r.getD false) (pushB .input true (jump .write)))
      (.load (fun _ => none) .halt)

private def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .input
  Γ _ := Bool
  Λ := Label
  main := .read
  σ := Reg
  initialState := none
  m := program

private abbrev Cfg := TM2.Cfg (fun _ : Tape => Bool) Label Reg
private def cfg (l : Option Label) (i h f : List Bool) : Cfg := ⟨l,none,tapes i h f⟩

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


private def bump : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: bump bs

private lemma bump_pos (p : PosNum) : bump (encodePosNum p) = encodePosNum p.succ := by
  induction p with
  | one => rfl
  | bit1 p ih => exact congrArg (List.cons false) ih
  | bit0 p ih => rfl

private lemma bump_num (p : Num) : bump (encodeNum p) = encodeNum p.succ := by
  cases p with
  | zero => rfl
  | pos p => exact bump_pos p

private lemma bump_nat (n : ℕ) : bump (encodeNat n) = encodeNat (n+1) := by
  unfold encodeNat
  rw [Nat.cast_succ,Num.add_one]
  exact bump_num _

private lemma bump_len (b : List Bool) : (bump b).length ≤ b.length + 1 := by
  induction b with
  | nil => decide
  | cons a bs ih => cases a <;> simp [bump] <;> omega

private lemma enc_len (n : ℕ) : (encodeNat n).length ≤ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [← bump_nat]; exact (bump_len _).trans (by omega)

private lemma restore_run (input acc : List Bool) (m : ℕ) :
    Run (cfg (some .restore) input acc (List.replicate m false))
      (cfg (some .read) input (List.replicate m false ++ acc) []) (m+1) := by
  induction m generalizing acc with
  | zero => apply once; simp [cfg,program,takeB,jump]
  | succ m ih =>
    have eq : List.replicate m false ++ false::acc = List.replicate (m+1) false ++ acc := by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [← eq]
    exact next (b := cfg (some .restore) input (false::acc) (List.replicate m false))
      (by simp [cfg,program,takeB,pushB,jump,List.replicate_succ]) (ih _)

private lemma carry_run (input bs : List Bool) (m : ℕ) :
    Run (cfg (some .carry) input bs (List.replicate m false))
      (cfg (some .read) input (List.replicate m false ++ bump bs) [])
      (2*bs.length + m + 2) := by
  induction bs generalizing m with
  | nil =>
    have h := next (a := cfg (some .carry) input [] (List.replicate m false))
      (by simp [cfg,program,takeB,pushB,jump]) (restore_run input [true] m)
    exact widen h (by simp <;> omega)
  | cons b bs ih =>
    cases b with
    | false =>
      have h := next (a := cfg (some .carry) input (false::bs) (List.replicate m false))
        (by simp [cfg,program,takeB,pushB,jump]) (restore_run input (true::bs) m)
      exact widen h (by simp <;> omega)
    | true =>
      have h := next (a := cfg (some .carry) input (true::bs) (List.replicate m false))
        (by simp [cfg,program,takeB,pushB,jump,List.replicate_succ]) (ih (m+1))
      rw [List.replicate_succ',List.append_assoc,List.singleton_append] at h
      exact widen h (by simp <;> omega)

private lemma read_run (x rest : List Bool) (n : ℕ) :
    Run (cfg (some .read) (inputX x ++ rest) (encodeNat n) [])
      (cfg (some .reverse) (false::rest) (encodeNat (n+x.length)) [])
      (x.length * (2*(n+x.length)+4)+1) := by
  induction x generalizing n with
  | nil =>
    simp only [List.length_nil,Nat.add_zero,Nat.zero_mul,Nat.zero_add]
    apply once
    simp [cfg,program,inputX,takeB,pushB,jump]
  | cons b bs ih =>
    have carry := carry_run (inputX bs ++ rest) (encodeNat n) 0
    simp only [List.replicate_zero,List.nil_append,Nat.add_zero,bump_nat] at carry
    have h₁ := next (a := cfg (some .read) (inputX (b::bs) ++ rest) (encodeNat n) [])
      (by simp [cfg,program,takeB,pushB,skipBit,jump,inputX]) carry
    have h := chain h₁ (ih (n+1))
    rw [show n+1+bs.length=n+(b::bs).length by simp; omega] at h
    apply widen h
    simp only [List.length_cons]
    nlinarith [enc_len n]

private lemma reverse_run (input bs acc : List Bool) :
    Run (cfg (some .reverse) input bs acc)
      (cfg (some .write) input [] (bs.reverse++acc)) (bs.length+1) := by
  induction bs generalizing acc with
  | nil => apply once; simp [cfg,program,takeB,jump]
  | cons b bs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
      (next (a := cfg (some .reverse) input (b::bs) acc)
        (by simp [cfg,program,takeB,jump]) (ih (b::acc)))

private lemma write_run (bs input : List Bool) :
    Run (cfg (some .write) input [] bs)
      (cfg none ((bs.reverse.flatMap (fun b => [true,b])) ++ input) [] []) (bs.length+1) := by
  induction bs generalizing input with
  | nil => apply once; simp [cfg,program,takeB]
  | cons b bs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc,List.cons_append,List.nil_append] using
      (next (a := cfg (some .write) input [] (b::bs))
        (by simp [cfg,program,takeB,jump,pushB]) (ih (true::b::input)))

private lemma delimit_out (bs rest : List Bool) :
    bs.flatMap (fun b => [true,b]) ++ false::rest = BitstringEncoding.delimit bs ++ rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [BitstringEncoding.delimit,ih]


theorem poly : OMA.R_Erdos78_erdos_78_variants_cohen_R1_H2_R1.H1 := by
  refine ⟨{
    tm := machine
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := (Polynomial.X + Polynomial.C 10)^2
    outputsFun := ?_ }⟩
  rintro ⟨x,w⟩
  let tail := BitstringEncoding.bitEncode w
  let word := inputX x ++ tail
  let answer := BitstringEncoding.delimit (encodeNat x.length) ++ tail
  have encode : BitstringEncoding.bitEncode (x,w) = word := by
    change BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++ tail = _
    rw [bits_eq,input_eq]
  have ci : initList machine word = cfg (some .read) word [] [] := by
    unfold initList cfg
    apply congrArg (fun st => (⟨some Label.read,none,st⟩ : Cfg))
    funext k; cases k <;> rfl
  have co : haltList machine answer = cfg none answer [] [] := by
    unfold haltList cfg
    apply congrArg (fun st => (⟨none,none,st⟩ : Cfg))
    funext k; cases k <;> rfl
  have read := read_run x tail 0
  have rev := reverse_run (false::tail) (encodeNat x.length) []
  have wr := write_run (encodeNat x.length).reverse (false::tail)
  simp only [Nat.zero_add] at read
  simp only [List.append_nil] at rev
  simp only [List.reverse_reverse,delimit_out,List.length_reverse] at wr
  have total := chain (chain read rev) wr
  let k := Classical.choose total
  have hk := (Classical.choose_spec total).1
  have run := (Classical.choose_spec total).2
  refine ⟨⟨k,?_⟩,?_⟩
  · change (fun o : Option Cfg => o.bind (TM2.step program))^[k]
       (some (initList machine (List.map (id : Bool → Bool) (BitstringEncoding.bitEncode (x,w))))) =
         some (haltList machine (List.map (id : Bool → Bool) answer))
    rw [encode]
    let iter (c : Cfg) := (fun o : Option Cfg => o.bind (TM2.step program))^[k] (some c)
    have startEq := (congrArg (fun y : List Bool => initList machine y) (List.map_id word)).trans ci
    have endEq := (congrArg (fun y : List Bool => haltList machine y) (List.map_id answer)).trans co
    exact (congrArg iter startEq).trans (run.trans (congrArg some endEq.symm))
  · change k ≤ Polynomial.eval (BitstringEncoding.bitEncode (x,w)).length ((Polynomial.X+Polynomial.C 10)^2)
    rw [encode]
    simp only [word,List.length_append,inp_len,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_C,Polynomial.eval_X]
    apply hk.trans
    nlinarith [enc_len x.length, Nat.zero_le (tail.length^2),
      Nat.zero_le (x.length*tail.length),Nat.zero_le (x.length^2)]

end OMA.CohenLength

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_cohen_R1_H2_R1.H1 := OMA.CohenLength.poly
