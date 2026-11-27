import OMAReductions.R_Erdos78_erdos_78_variants_cohen_R1
import Mathlib

-- Credit: @marcusbuffett

/-! Serial composition of two finite stack machines. The output stack of the first
machine becomes the input stack of the second. No intermediate tape copy is needed. -/
namespace OMA78Serial
open Turing Function
open scoped Classical

private theorem run_map {X Y : Type} (f : X → Option X) (g : Y → Option Y) (e : X → Y)
    (step : ∀ {x z}, f x = some z → g (e x) = some (e z)) (n : ℕ) {x z : X}
    (run : (fun o : Option X => o.bind f)^[n] (some x) = some z) :
    (fun o : Option Y => o.bind g)^[n] (some (e x)) = some (e z) := by
  induction n generalizing x with
  | zero => exact congrArg (Option.map e) run
  | succ n ih =>
    rw [Function.iterate_succ_apply] at run ⊢
    change (fun o : Option X => o.bind f)^[n] (f x) = some z at run
    change (fun o : Option Y => o.bind g)^[n] (g (e x)) = _
    cases h : f x with
    | none =>
      rw [h,Function.iterate_fixed (f := fun o : Option X => o.bind f) rfl] at run
      contradiction
    | some y => rw [step h]; exact ih (h ▸ run)

private lemma init_stk (M : FinTM2) (xs : List (M.Γ M.k₀)) :
    (initList M xs).stk = update (fun _ => []) M.k₀ xs := by
  funext k
  by_cases h : k=M.k₀
  · subst k; simp [initList]
  · simp [initList,h,update_of_ne h]

private lemma halt_stk (M : FinTM2) (xs : List (M.Γ M.k₁)) :
    (haltList M xs).stk = update (fun _ => []) M.k₁ xs := by
  funext k
  by_cases h : k=M.k₁
  · subst k; simp [haltList]
  · simp [haltList,h,update_of_ne h]

private theorem cfg_ext {ι Λ σ : Type} {Γ : ι → Type} {c d : TM2.Cfg Γ Λ σ}
    (h : c.l = d.l) (v : c.var = d.var) (s : c.stk = d.stk) : c = d := by
  cases c; cases d; simp_all

private theorem frame (M : FinTM2) {I Q V : Type} {A : I → Type} [DecidableEq I]
    (loc : M.K ↪ I) (sym : ∀ k, M.Γ k ≃ A (loc k))
    (into : M.σ → V) (out : V → M.σ) (retract : ∀ v, out (into v) = v)
    (tag : M.Λ → Q) (stop : Option Q) :
    ∃ (compile : M.Λ → TM2.Stmt A Q V) (cfg : M.Cfg → TM2.Cfg A Q V),
      (∀ (P : Q → TM2.Stmt A Q V), (∀ l, P (tag l) = compile l) →
        ∀ {c d : M.Cfg}, M.step c = some d → TM2.step P (cfg c) = some (cfg d)) ∧
      (∀ xs, cfg (initList M xs) = ⟨some (tag M.main), into M.initialState,
        update (fun _ => []) (loc M.k₀) (xs.map (sym M.k₀))⟩) ∧
      (∀ ys, cfg (haltList M ys) = ⟨stop, into M.initialState,
        update (fun _ => []) (loc M.k₁) (ys.map (sym M.k₁))⟩) := by
  let storeMap (s : ∀ k,List (M.Γ k)) (j : I) : List (A j) :=
    if h : ∃ k,loc k = j then h.choose_spec ▸ (s h.choose).map (sym h.choose) else []

  have storeMap_at (s : ∀ k,List (M.Γ k)) (k) : storeMap s (loc k) = (s k).map (sym k) := by
    unfold storeMap
    split
    · rename_i h
      have aux (i : M.K) (e : loc i = loc k) : (e ▸ (s i).map (sym i)) = (s k).map (sym k) := by
        obtain rfl := loc.injective e
        rfl
      exact aux h.choose h.choose_spec
    · rename_i h
      exact (h ⟨k,rfl⟩).elim

  have storeMap_update (s : ∀ k,List (M.Γ k)) (k) (xs : List (M.Γ k)) :
      storeMap (update s k xs) = update (storeMap s) (loc k) (xs.map (sym k)) := by
    funext j
    by_cases h : ∃ i,loc i = j
    · obtain ⟨i,rfl⟩ := h
      by_cases hi : i=k
      · subst i; simp [storeMap_at]
      · simp [storeMap_at,update_of_ne hi,update_of_ne (loc.injective.ne hi)]
    · simp [storeMap,h,update_of_ne (show j ≠ loc k from fun e => h ⟨k,e.symm⟩)]

  let lab (q : Option M.Λ) : Option Q := q.elim stop (fun l => some (tag l))

  let cfg (c : M.Cfg) : TM2.Cfg A Q V := ⟨lab c.l,into c.var,storeMap c.stk⟩

  let stmt : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt A Q V :=
    TM2.Stmt.rec (motive := fun _ => TM2.Stmt A Q V)
      (fun k f _ t => .push (loc k) (fun v => sym k (f (out v))) t)
      (fun k f _ t => .peek (loc k) (fun v a => into (f (out v) (a.map (sym k).symm))) t)
      (fun k f _ t => .pop (loc k) (fun v a => into (f (out v) (a.map (sym k).symm))) t)
      (fun f _ t => .load (fun v => into (f (out v))) t)
      (fun f _ _ t u => .branch (fun v => f (out v)) t u)
      (fun l => .goto (fun v => tag (l (out v))))
      (match stop with | none => .halt | some l => .goto (fun _ => l))

  have sim_aux (t : TM2.Stmt M.Γ M.Λ M.σ) (v s) :
      TM2.stepAux (stmt t) (into v) (storeMap s) = cfg (TM2.stepAux t v s) := by
    have top (k) (s : ∀ j,List (M.Γ j)) :
        ((storeMap s (loc k)).head?).map (sym k).symm = (s k).head? := by
      rw [storeMap_at]
      cases s k <;> simp
    induction t generalizing v s with
    | push k f t ih =>
      simpa only [stmt,TM2.stepAux,retract,storeMap_at,List.map_cons,storeMap_update] using
        ih v (update s k (f v :: s k))
    | peek k f t ih => simp only [stmt,TM2.stepAux,retract,top,ih]
    | pop k f t ih =>
      simp only [stmt,TM2.stepAux,retract,top]
      simpa only [storeMap_at,List.map_tail,storeMap_update] using
        ih (f v (s k).head?) (update s k (s k).tail)
    | load f t ih => simp only [stmt,TM2.stepAux,retract,ih]
    | branch f t u ht hu => cases h : f v <;> simp [stmt,TM2.stepAux,retract,h,ht,hu]
    | goto f => simp [stmt,TM2.stepAux,cfg,lab,retract]
    | halt => cases h : stop <;> simp [stmt,TM2.stepAux,cfg,lab,h]

  have sim_step (P : Q → TM2.Stmt A Q V)
      (hp : ∀ l,P (tag l) = stmt (M.m l)) {c d : M.Cfg} (h : M.step c = some d) :
      TM2.step P (cfg c) = some (cfg d) := by
    rcases c with ⟨l,v,s⟩
    cases l with
    | none => cases h
    | some l =>
      have hd : TM2.stepAux (M.m l) v s = d := Option.some.inj h
      subst d
      change some (TM2.stepAux (P (tag l)) (into v) (storeMap s)) = _
      rw [hp,sim_aux]
  have store_nil : storeMap (fun _ => []) = fun _ => [] := by
    funext j
    by_cases h : ∃ k,loc k=j
    · obtain ⟨k,rfl⟩ := h
      exact storeMap_at (fun _ => []) k
    · simp [storeMap,h]

  have store_one (k) (xs : List (M.Γ k)) :
      storeMap (update (fun _ => []) k xs) =
        update (fun _ => []) (loc k) (xs.map (sym k)) := by
    rw [storeMap_update,store_nil]
  refine ⟨fun l => stmt (M.m l),cfg,fun P hp _ _ h => sim_step P hp h,?_,?_⟩
  · intro xs
    apply cfg_ext <;> try rfl
    exact (congrArg storeMap (init_stk M xs)).trans (store_one _ _)
  · intro xs
    apply cfg_ext <;> try rfl
    exact (congrArg storeMap (halt_stk M xs)).trans (store_one _ _)

private theorem growth (M : FinTM2) : ∃ C : ℕ, ∀ {xs : List (M.Γ M.k₀)} {ys : List (M.Γ M.k₁)} {n : ℕ},
    (fun o : Option M.Cfg => o.bind M.step)^[n] (some (initList M xs)) = some (haltList M ys) →
    ys.length ≤ xs.length + n * C := by
  let weight : TM2.Stmt M.Γ M.Λ M.σ → ℕ :=
    TM2.Stmt.rec (motive := fun _ => ℕ) (fun _ _ _ n => n+1)
      (fun _ _ _ n => n) (fun _ _ _ n => n) (fun _ _ n => n)
      (fun _ _ _ m n => max m n) (fun _ => 0) 0

  have aux (t : TM2.Stmt M.Γ M.Λ M.σ) (v s) (k : M.K) :
      ((TM2.stepAux t v s).stk k).length ≤ (s k).length + weight t := by
    induction t generalizing v s with
    | push j f t ih =>
      have h := ih v (update s j (f v :: s j))
      by_cases e : k=j
      · subst k
        change _ ≤ (s j).length + (weight t + 1)
        simp only [update_self,List.length_cons] at h
        simp only [TM2.stepAux]
        omega
      · simpa [TM2.stepAux,weight,update_of_ne e,Nat.add_assoc] using
          (Nat.le_succ_of_le h)
    | peek j f t ih => exact ih _ _
    | pop j f t ih =>
      have h := ih (f v (s j).head?) (update s j (s j).tail)
      change _ ≤ (s k).length + weight t
      refine h.trans (Nat.add_le_add_right ?_ _)
      by_cases e : k=j
      · subst k; simp
      · simp [update_of_ne e]
    | load f t ih => exact ih _ _
    | branch f t u ht hu =>
      cases e : f v <;> simp only [TM2.stepAux,e,cond_true,cond_false,weight]
      · exact (hu _ _).trans (Nat.add_le_add_left (le_max_right ..) _)
      · exact (ht _ _).trans (Nat.add_le_add_left (le_max_left ..) _)
    | goto f => simp [TM2.stepAux,weight]
    | halt => simp [TM2.stepAux,weight]

  let cap : ℕ := by
    letI := M.ΛFin
    exact Finset.univ.sup (fun l => weight (M.m l))

  have step_bound {c d : M.Cfg} (k : M.K) (h : M.step c = some d) :
      (d.stk k).length ≤ (c.stk k).length + cap := by
    obtain ⟨l,v,s⟩ := c
    cases l with
    | none => cases h
    | some l =>
      have hd : TM2.stepAux (M.m l) v s = d := Option.some.inj h
      subst d
      letI := M.ΛFin
      exact (aux (M.m l) v s k).trans <| Nat.add_le_add_left (Finset.le_sup (f := fun l => weight (M.m l)) (Finset.mem_univ l)) _

  have run_bound {c d : M.Cfg} (k : M.K) (n : ℕ)
      (hr : (fun o : Option M.Cfg => o.bind M.step)^[n] (some c) = some d) :
      (d.stk k).length ≤ (c.stk k).length + n * cap := by
    induction n generalizing c with
    | zero => obtain rfl := Option.some.inj hr; simp
    | succ n ih =>
      rw [Function.iterate_succ_apply] at hr
      change (fun o : Option M.Cfg => o.bind M.step)^[n] (M.step c) = some d at hr
      cases e : M.step c with
      | none => rw [e,Function.iterate_fixed (f := fun o : Option M.Cfg => o.bind M.step) rfl] at hr; contradiction
      | some c' =>
        have h := ih (e ▸ hr)
        have h' := step_bound k e
        rw [Nat.succ_mul]
        omega

  have encoded {xs : List (M.Γ M.k₀)} {ys : List (M.Γ M.k₁)} {n : ℕ}
      (hr : (fun o : Option M.Cfg => o.bind M.step)^[n] (some (initList M xs)) = some (haltList M ys)) :
      ys.length ≤ xs.length + n * cap := by
    have h := run_bound M.k₁ n hr
    rw [halt_stk,init_stk,update_self] at h
    by_cases e : M.k₁ = M.k₀
    · have q (j : M.K) (hj : j=M.k₀) : ((update (fun _ => []) M.k₀ xs) j).length = xs.length := by subst j; simp
      rwa [q _ e] at h
    · simp [update_of_ne e] at h
      omega
  exact ⟨cap, fun h => encoded h⟩

private theorem mono_eval (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  simp only [Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

private theorem serial {α β γ U V W : Type} {ea : α → List U}
    {eb : β → List V} {ec : γ → List W} {f : α → β} {g : β → γ}
    (F : TM2ComputableInPolyTime ea eb f) (G : TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (g ∘ f)) := by
  let M := F.tm
  let N := G.tm
  let I := M.K ⊕ N.K
  let A : I → Type := Sum.elim M.Γ N.Γ
  let Q := M.Λ ⊕ N.Λ
  let V' := M.σ × N.σ
  let b := G.inputAlphabet.trans F.outputAlphabet.symm
  let loc (k : N.K) : I := if k=N.k₀ then .inl M.k₁ else .inr k
  have inj : Injective loc := by
    intro i j h
    by_cases hi : i=N.k₀ <;> by_cases hj : j=N.k₀ <;> simp_all [loc] <;> exact Sum.inr.inj h
  let retype (k : N.K) : N.Γ k ≃ A (loc k) := by
    by_cases h : k=N.k₀
    · subst k
      let e : (Sum.inl M.k₁ : I) = loc N.k₀ := by simp [loc]
      exact b.trans (Equiv.cast (congrArg A e))
    · unfold loc
      rw [if_neg h]
      exact Equiv.refl _
  let L : M.K ↪ I := ⟨Sum.inl,Sum.inl_injective⟩
  let R : N.K ↪ I := ⟨loc,inj⟩
  letI dec : DecidableEq I := inferInstanceAs (DecidableEq (M.K ⊕ N.K))
  obtain ⟨pl,cl,sl,il,hl⟩ := frame M (A := A) (Q := Q) (V := V') L
    (fun _ => Equiv.refl _) (fun v => (v,N.initialState)) Prod.fst (fun _ => rfl)
    Sum.inl (some (.inr N.main))
  obtain ⟨pr,cr,sr,ir,hr⟩ := frame N (A := A) (Q := Q) (V := V') R retype
    (fun v => (M.initialState,v)) Prod.snd (fun _ => rfl) Sum.inr none
  let prog : Q → TM2.Stmt A Q V' := Sum.elim pl pr
  let P : FinTM2 := {
    K := I, kDecidableEq := dec,
    kFin := by letI := M.kFin; letI := N.kFin; exact inferInstanceAs (Fintype (M.K ⊕ N.K))
    k₀ := Sum.inl M.k₀, k₁ := loc N.k₁, Γ := A, Λ := Q, main := Sum.inl M.main
    ΛFin := by letI := M.ΛFin; letI := N.ΛFin; exact inferInstanceAs (Fintype (M.Λ ⊕ N.Λ))
    σ := V', initialState := (M.initialState,N.initialState)
    σFin := @instFintypeProd _ _ M.σFin N.σFin
    Γk₀Fin := M.Γk₀Fin, m := prog }
  have start (xs : List (M.Γ M.k₀)) : cl (initList M xs) = initList P xs := by
    rw [il]
    apply cfg_ext <;> try rfl
    refine Eq.trans ?_ (init_stk P xs).symm
    exact congrArg (fun ys : List (M.Γ M.k₀) => update (fun i : I => ([] : List (A i))) (.inl M.k₀) ys) (List.map_id xs)
  have handoff (xs : List (N.Γ N.k₀)) : cl (haltList M (xs.map b)) = cr (initList N xs) := by
    rw [hl,ir]
    apply cfg_ext <;> try rfl
    let z : I := .inl M.k₁
    have e : z = loc N.k₀ := by simp [z,loc]
    have aux (j : I) (h : z = j) :
        update (fun i : I => ([] : List (A i))) z (xs.map b) =
        update (fun i => ([] : List (A i))) j
          (xs.map (b.trans (Equiv.cast (congrArg A h)))) := by
      cases h
      rfl
    refine (congrArg (fun ys : List (M.Γ M.k₁) => update (fun i : I => ([] : List (A i))) z ys) (List.map_id (xs.map b))).trans ?_
    refine (aux _ e).trans ?_
    congr 2
    simp [R,retype]
  have finish (xs : List (N.Γ N.k₁)) : cr (haltList N xs) = haltList P (xs.map (retype N.k₁)) := by
    rw [hr]
    apply cfg_ext <;> try rfl
    exact (halt_stk P _).symm
  obtain ⟨C,grow⟩ := growth M
  let oa := (retype N.k₁).symm.trans G.outputAlphabet
  refine ⟨{
    tm := P
    inputAlphabet := F.inputAlphabet
    outputAlphabet := oa
    time := G.time.comp (Polynomial.X + F.time * Polynomial.C C) + F.time
    outputsFun := ?_ }⟩
  intro x
  obtain ⟨⟨i, hi⟩, hiL⟩ := F.outputsFun x
  obtain ⟨⟨j, hj⟩, hjL⟩ := G.outputsFun (f x)
  let src := (ea x).map F.inputAlphabet.invFun
  let mid := (eb (f x)).map G.inputAlphabet.invFun
  let dst := (ec (g (f x))).map G.outputAlphabet.invFun
  have bits : mid.map b = (eb (f x)).map F.outputAlphabet.invFun := by
    simp [mid,b,List.map_map,Function.comp_def,Equiv.invFun_as_coe]
  have outbits : dst.map (retype N.k₁) = (ec (g (f x))).map oa.invFun := by
    simp [dst,oa,List.map_map,Function.comp_def,Equiv.invFun_as_coe]
  have hlen := grow (xs := src) (ys := (eb (f x)).map F.outputAlphabet.invFun) (n := i) hi
  simp only [src,List.length_map] at hlen
  have h₁ := run_map M.step P.step cl
    (fun h => sl prog (fun _ => rfl) h) i
    (x := initList M src) (z := haltList M ((eb (f x)).map F.outputAlphabet.invFun)) hi
  have h₂ := run_map N.step P.step cr
    (fun h => sr prog (fun _ => rfl) h) j
    (x := initList N mid) (z := haltList N dst) hj
  rw [start,← bits,handoff] at h₁
  rw [finish] at h₂
  refine ⟨⟨j+i,?_⟩,?_⟩
  · change (fun o : Option P.Cfg => o.bind P.step)^[j+i] (some (initList P src)) = _
    rw [Function.iterate_add_apply]
    exact ((congrArg ((fun o : Option P.Cfg => o.bind P.step)^[j]) h₁).trans h₂).trans
      (congrArg (fun ys : List (P.Γ P.k₁) => some (haltList P ys)) outbits)
  · simp only [Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C]
    exact Nat.add_le_add (hjL.trans (mono_eval _ (hlen.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hiL) _)))) hiL

theorem poly_comp {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    {f : α → β} {g : β → γ} (hf : ComplexityTheory.IsPolyTime f) (hg : ComplexityTheory.IsPolyTime g) :
    ComplexityTheory.IsPolyTime (g ∘ f) := by
  obtain ⟨F⟩ := hf
  obtain ⟨G⟩ := hg
  exact serial F G

end OMA78Serial

namespace OMA.R_Erdos78_erdos_78_variants_cohen_R1_H2_R1
open ComplexityTheory

/-- Convert the unary first field to its binary length, carrying the remaining fields. -/
def H1 : Prop := IsPolyTime (fun p : List Bool × ℕ × ℕ => (p.1.length, p.2))

/-- Order the two binary vertex labels and carry the graph dimension. -/
def H2 : Prop := IsPolyTime (fun p : ℕ × ℕ × ℕ => (p.1, min p.2.1 p.2.2, max p.2.1 p.2.2))

theorem main : H1 → H2 → OMA.R_Erdos78_erdos_78_variants_cohen_R1.H2 := by
  intro h₁ h₂ f hf
  exact ⟨_, OMA78Serial.poly_comp (OMA78Serial.poly_comp h₁ h₂) hf, fun _ _ _ => rfl⟩

end OMA.R_Erdos78_erdos_78_variants_cohen_R1_H2_R1
