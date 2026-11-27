import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1

-- Step Erdos78.erdos_78.variants.strongly_explicit.R1.H3: hypothesis H3 of reduction Erdos78.erdos_78.variants.strongly_explicit.R1
-- Credit: @adammcarter
-- H3: replacing n by the next power of two, 2 ^ (bit length of n), in the first slot is poly-time.
-- A hand-built two-stack machine rewrites only the first delimited block, in linear time.

open ComplexityTheory
open Turing Computability

-- Poly-time fact H3 for a reduction of Erdos78.erdos_78.variants.strongly_explicit:
-- the map (n, r) to (2 ^ Nat.size n, r) is computable in polynomial time.
-- Mathlib has no composition lemmas for poly-time machines, so the machine is built by hand.
-- Two stacks: the main stack (input and output) and an auxiliary stack.
-- Phase one pops the first self-delimiting block and pushes the new block, reversed, on the
-- auxiliary stack; phase two pours the auxiliary stack back on the main stack. The rest of
-- the input is never touched.

namespace Erdos78Pad

-- Reachability of a configuration within a step budget, as a Prop.

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

-- The binary encoding of a natural number is its list of bits.

lemma encodePosNum_eq_bits (p : PosNum) : encodePosNum p = Nat.bits (p : ℕ) := by
  induction p with
  | one => simp [encodePosNum]
  | bit1 p ih =>
    rw [encodePosNum, ih, PosNum.cast_bit1, ← two_mul, Nat.bit1_bits]
  | bit0 p ih =>
    rw [encodePosNum, ih, PosNum.cast_bit0, ← two_mul,
      Nat.bit0_bits _ (PosNum.to_nat_pos p).ne']

lemma encodeNum_eq_bits (q : Num) : encodeNum q = Nat.bits (q : ℕ) := by
  cases q with
  | zero => simp [encodeNum]
  | pos p => simpa [encodeNum] using encodePosNum_eq_bits p

lemma encodeNat_eq_bits (n : ℕ) : encodeNat n = Nat.bits n := by
  rw [encodeNat, encodeNum_eq_bits, Num.to_of_nat]

lemma bits_two_pow (k : ℕ) : Nat.bits (2 ^ k) = List.replicate k false ++ [true] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_comm, Nat.bit0_bits _ (by positivity), ih]
    rfl

lemma encodeNat_pad (n : ℕ) :
    encodeNat (2 ^ Nat.size n) = (encodeNat n).map (fun _ => false) ++ [true] := by
  rw [encodeNat_eq_bits, encodeNat_eq_bits, bits_two_pow, ← Nat.size_eq_bits_len]
  rw [List.map_const']

-- The machine. Stack false is the main stack, stack true the auxiliary one.
-- Label false is the parse phase, label true the pour phase.

def prog : Bool → TM2.Stmt (fun _ : Bool => Bool) Bool (Option Bool)
  | false =>
    .pop false (fun _ o => o) <|
      .branch (fun v => v == some true)
        (.pop false (fun _ o => o) <|
          .push true (fun _ => true) <|
            .push true (fun _ => false) <| .goto fun _ => false)
        (.push true (fun _ => true) <|
          .push true (fun _ => true) <|
            .push true (fun _ => false) <| .goto fun _ => true)
  | true =>
    .pop true (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push false (fun v => v.getD false) <| .goto fun _ => true)
        (.load (fun _ => none) <| .halt)

def N : FinTM2 :=
  { K := Bool
    k₀ := false
    k₁ := false
    Γ := fun _ => Bool
    Λ := Bool
    main := false
    σ := Option Bool
    initialState := none
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog }

def mk (i a : List Bool) : ∀ k : Bool, List ((fun _ : Bool => Bool) k)
  | false => i
  | true => a

lemma upd_main (i a : List Bool) (i' : List Bool) :
    Function.update (mk i a) false i' = mk i' a := by
  funext k
  cases k <;> simp [Function.update, mk]

lemma upd_aux (i a : List Bool) (a' : List Bool) :
    Function.update (mk i a) true a' = mk i a' := by
  funext k
  cases k <;> simp [Function.update, mk]

def cfg (l : Option Bool) (o : Option Bool) (i a : List Bool) : N.Cfg :=
  ⟨l, o, mk i a⟩

-- One step of each phase.

lemma step_parse_true (o : Option Bool) (c : Bool) (rest a : List Bool) :
    N.step (cfg (some false) o (true :: c :: rest) a) =
      some (cfg (some false) (some c) rest (false :: true :: a)) := by
  show some (TM2.stepAux (prog false) o (mk (true :: c :: rest) a)) = _
  simp [prog, TM2.stepAux, mk, upd_main, upd_aux, cfg]
  rfl

lemma step_parse_false (o : Option Bool) (rest a : List Bool) :
    N.step (cfg (some false) o (false :: rest) a) =
      some (cfg (some true) (some false) rest (false :: true :: true :: a)) := by
  show some (TM2.stepAux (prog false) o (mk (false :: rest) a)) = _
  simp [prog, TM2.stepAux, mk, upd_main, upd_aux, cfg]
  rfl

lemma step_pour_cons (o : Option Bool) (c : Bool) (i a : List Bool) :
    N.step (cfg (some true) o i (c :: a)) = some (cfg (some true) (some c) (c :: i) a) := by
  show some (TM2.stepAux (prog true) o (mk i (c :: a))) = _
  simp [prog, TM2.stepAux, mk, upd_main, upd_aux, cfg]
  rfl

lemma step_pour_nil (o : Option Bool) (i : List Bool) :
    N.step (cfg (some true) o i []) = some (cfg none none i []) := by
  show some (TM2.stepAux (prog true) o (mk i [])) = _
  simp [prog, TM2.stepAux, mk, upd_main, upd_aux, cfg]
  rfl

-- The two phases.

lemma parse_run (s rest a : List Bool) (o : Option Bool) :
    RIn N.step (cfg (some false) o (BitstringEncoding.delimit s ++ rest) a)
      (some (cfg (some true) (some false) rest
        ((BitstringEncoding.delimit (s.map (fun _ => false) ++ [true])).reverse ++ a)))
      (s.length + 1) := by
  induction s generalizing a o with
  | nil =>
    have := RIn.single (step_parse_false o rest a)
    simpa [BitstringEncoding.delimit] using this
  | cons c s ih =>
    have h1 := RIn.single (step_parse_true o c (BitstringEncoding.delimit s ++ rest) a)
    have h2 := ih (false :: true :: a) (some c)
    have := RIn.trans h1 h2
    simpa [BitstringEncoding.delimit, List.reverse_cons, List.append_assoc, Nat.add_comm]
      using this

lemma pour_run (i a : List Bool) (o : Option Bool) :
    RIn N.step (cfg (some true) o i a) (some (cfg none none (a.reverse ++ i) []))
      (a.length + 1) := by
  induction a generalizing o i with
  | nil => exact RIn.single (step_pour_nil o i)
  | cons c a ih =>
    have := RIn.trans (RIn.single (step_pour_cons o c i a)) (ih (c :: i) (some c))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

-- Initial and final configurations.

lemma initList_N (l : List Bool) : initList N l = cfg (some false) none l [] := by
  simp only [initList, cfg]
  congr 1
  funext k
  cases k <;> rfl

lemma haltList_N (l : List Bool) : haltList N l = cfg none none l [] := by
  simp only [haltList, cfg]
  congr 1
  funext k
  cases k <;> rfl

/-- The whole run: the first block is replaced, the rest is kept. -/
lemma full_run (s t : List Bool) :
    RIn N.step (initList N (BitstringEncoding.delimit s ++ t))
      (some (haltList N (BitstringEncoding.delimit (s.map (fun _ => false) ++ [true]) ++ t)))
      (3 * s.length + 5) := by
  rw [initList_N, haltList_N]
  have h1 := parse_run s t [] none
  have h2 := pour_run t
    ((BitstringEncoding.delimit (s.map (fun _ => false) ++ [true])).reverse ++ []) (some false)
  have h := RIn.trans h1 h2
  simp only [List.append_nil, List.reverse_reverse] at h
  refine h.mono ?_
  simp [BitstringEncoding.length_delimit]
  omega

end Erdos78Pad

open Erdos78Pad in
/-- Replacing n by 2 ^ Nat.size n in the first slot of a triple is poly-time. -/
theorem erdos78_pad_polyTime :
    ComplexityTheory.IsPolyTime (fun x : ℕ × ℕ × ℕ => ((2 : ℕ) ^ Nat.size x.1, x.2)) := by
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := Polynomial.X + Polynomial.X + 5
            outputsFun := fun x => ?_ }⟩
  set s := encodeNat x.1 with hs
  set t := BitstringEncoding.bitEncode x.2 with ht
  have henc : (BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode x =
      BitstringEncoding.delimit s ++ t := rfl
  have hout : (BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode
      ((2 : ℕ) ^ Nat.size x.1, x.2) =
      BitstringEncoding.delimit (s.map (fun _ => false) ++ [true]) ++ t := by
    have : (BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode
        ((2 : ℕ) ^ Nat.size x.1, x.2) =
        BitstringEncoding.delimit (encodeNat (2 ^ Nat.size x.1)) ++ t := rfl
    rw [this, encodeNat_pad]
  have hin : List.map ((Equiv.refl Bool : N.Γ N.k₀ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode x) =
      BitstringEncoding.delimit s ++ t := by
    rw [henc]; exact List.map_id _
  have hout' : List.map ((Equiv.refl Bool : N.Γ N.k₁ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode ((2 : ℕ) ^ Nat.size x.1, x.2)) =
      BitstringEncoding.delimit (s.map (fun _ => false) ++ [true]) ++ t := by
    rw [hout]; exact List.map_id _
  have hn : ((BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode x).length =
      2 * s.length + 1 + t.length := by
    rw [henc]; simp [BitstringEncoding.length_delimit]
  have hb : 3 * s.length + 5 ≤ (Polynomial.X + Polynomial.X + 5 : Polynomial ℕ).eval
      ((BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode x).length := by
    rw [hn]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  have key : ∀ l l' : List Bool, l = BitstringEncoding.delimit s ++ t →
      l' = BitstringEncoding.delimit (s.map (fun _ => false) ++ [true]) ++ t →
      TM2OutputsInTime N l (some l')
        ((Polynomial.X + Polynomial.X + 5 : Polynomial ℕ).eval
          ((BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode x).length) := by
    rintro l l' rfl rfl
    exact Classical.choice (by
      obtain ⟨n, hle, he⟩ := (full_run s t).mono hb
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)
  exact key _ _ hin hout'

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1.H3 :=
  erdos78_pad_polyTime
