import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1
/-! The finite machine checker and its certificates are from @hyprspacecoyote’s
merged write-one, low-state proof (94ee0af). The exceptional sweeping machine
uses @marcusbuffett’s R2.H3 proof. We adapt @henry10101001’s used-transition
restriction: both initial commands survive restriction, and the sweep excludes
the exceptional machine under either naming of the remaining states. -/
/-! Both machines repeatedly enter state A with a tape described by two counts j and k.
The left side contains j ones. From the head to the right, the second machine sees
2*k ones, a zero, and j ones. The first machine sees an additional leading zero.
When k is positive, a sweep transfers one unit from k to j. When k reaches zero,
the machines begin a new sweep. Each transition between these configurations takes
at least one machine step. -/
namespace OMA.BB4Sweeps
open Turing Turing.BusyBeaver
abbrev TM := Machine (Fin 2) (Fin 4)
abbrev Conf := Cfg (Fin 2) (Fin 4)
abbrev Side := ListBlank (Fin 2)
def special (second : Bool) : Machine (Fin 2) (Fin 4) := fun q a =>
    let entries : List ℕ := if second then [6,4,11,6,16,13,2,15] else [6,3,3,8,15,10,16,1]
    let v := entries[2*q.val+a.val]?.getD 16
    if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩, Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩
      (if v % 2 = 0 then Dir.right else Dir.left))

def run (M : TM) (a b : Conf) := ∃ n, M.multiStep a n = some b
lemma joinSteps (M : TM) {a b c : Conf} {n k : ℕ} (h : M.multiStep a n = some b)
    (g : M.multiStep b k = some c) : M.multiStep a (n+k) = some c := by
  unfold Machine.multiStep at *
  rw [Nat.add_comm, Function.iterate_add_apply, h, g]
lemma cat {M : TM} {a b c : Conf} (h : run M a b) (g : run M b c) : run M a c := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨k, hk⟩ := g
  exact ⟨_,joinSteps M hn hk⟩
lemma stay (M : TM) (a : Conf) : run M a a := ⟨0,rfl⟩
def config (q : Fin 4) (l : Side) (a : Fin 2) (r : Side) : Conf := ⟨q,⟨a,l,r⟩⟩
def rc (q : Fin 4) (l r : Side) := config q l r.head r.tail
def lc (q : Fin 4) (l r : Side) := config q l.tail l.head r
def w : ℕ → Side → Side
  | 0, t => t
  | n+1, t => (w n t).cons 1
lemma w_cons (n : ℕ) (l : Side) : w n (l.cons 1) = (w n l).cons 1 := by
  induction n <;> simp [w, *]
lemma w_add (m n : ℕ) (t : Side) : w m (w n t) = w (n+m) t := by
  induction m <;> simp [w, *]
def z : Side := ListBlank.mk []
@[simp] lemma hz : z.head = 0 := rfl
@[simp] lemma tz : z.tail = z := rfl
@[simp] lemma cz : z.cons 0 = z := by
  simpa only [hz,tz] using ListBlank.cons_head_tail z
lemma right {M : TM} {q q' : Fin 4} {a b : Fin 2} (l r : Side)
    (h : M q a = some (some q',Stmt.write b Dir.right)) :
    M.step (config q l a r) = some (rc q' (l.cons b) r) := by
  simp [Machine.step,config,h,rc,Tape.move]
lemma left {M : TM} {q q' : Fin 4} {a b : Fin 2} (l r : Side)
    (h : M q a = some (some q',Stmt.write b Dir.left)) :
    M.step (config q l a r) = some (lc q' l (r.cons b)) := by
  simp [Machine.step,config,h,lc,Tape.move]
lemma rscan {M : TM} {q : Fin 4} (h : M q 1 = some (some q,Stmt.write 1 Dir.right))
    (n : ℕ) (l r : Side) : run M (rc q l (w n r)) (rc q (w n l) r) := by
  induction n generalizing l with
  | zero => exact stay _ _
  | succ n ih =>
    apply cat _ (show run M (rc q (l.cons 1) (w n r)) _ from by
      simpa only [w_cons,w] using ih (l.cons 1))
    refine ⟨1,?_⟩
    simpa only [Machine.multiStep_one,rc,w,ListBlank.head_cons,ListBlank.tail_cons] using right l (w n r) h
lemma lscan {M : TM} {q : Fin 4} (h : M q 1 = some (some q,Stmt.write 1 Dir.left))
    (n : ℕ) (l r : Side) : run M (lc q (w n l) r) (lc q l (w n r)) := by
  induction n generalizing r with
  | zero => exact stay _ _
  | succ n ih =>
    apply cat _ (show run M (lc q (w n l) (r.cons 1)) _ from by
      simpa only [w_cons,w] using ih (r.cons 1))
    refine ⟨1,?_⟩
    simpa only [Machine.multiStep_one,lc,w,ListBlank.head_cons,ListBlank.tail_cons] using left (w n l) r h
def first (j k : ℕ) := config 0 (w j z) 0 (w (2*k) ((w j z).cons 0))
def second (j k : ℕ) := rc 0 (w j z) (w (2*k) ((w j z).cons 0))
def advances (M : TM) (a b : Conf) := ∃ n, 0 < n ∧ M.multiStep a n = some b
lemma starts {M : TM} {a b c : Conf} (h : M.step a = some b) (g : run M b c) : advances M a c := by
  obtain ⟨n,hn⟩ := g
  exact ⟨1+n,by omega,joinSteps M (n := 1) h hn⟩
lemma endless (M : TM) (f : ℕ → ℕ → Conf) (init : f 0 0 = Machine.init [])
    (adv : ∀ j k, ∃ x y, advances M (f j k) (f x y)) : ¬ M.IsHalting := by
  have reach (n : ℕ) : ∃ j k m, n ≤ m ∧ M.multiStep (Machine.init []) m = some (f j k) := by
    induction n with
    | zero => exact ⟨0,0,0,by omega,by simp [init]⟩
    | succ n ih =>
      obtain ⟨j,k,m,hm,h⟩ := ih
      obtain ⟨x,y,d,hd,g⟩ := adv j k
      exact ⟨x,y,m+d,by omega,joinSteps M h g⟩
  rintro h
  obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp h
  obtain ⟨j,k,m,hm,g⟩ := reach (n+1)
  have := Machine.multiStep_eq_none_mono hn hm
  simp_all

lemma first_restart (j : ℕ) : advances (special false) (first j 0) (first (0) (j+1)) := by
  have h0 : (special false).step (first j 0) = some (rc 1 (ListBlank.cons 1 (w j z)) (ListBlank.cons 0 (w j z))) := by
    simpa only [first, second, rc, lc, Nat.mul_succ, Nat.add_succ, w, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right (w j z) (ListBlank.cons 0 (w j z)) (show (special false) 0 0 = some (some 1, Stmt.write 1 Dir.right) from rfl)
  have h1 : run (special false) (rc 1 (ListBlank.cons 1 (w j z)) (ListBlank.cons 0 (w j z))) (lc 0 (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (w j z))) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa only [first, second, rc, lc, Nat.mul_succ, Nat.add_succ, w, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using left (ListBlank.cons 1 (w j z)) (w j z) (show (special false) 1 0 = some (some 0, Stmt.write 1 Dir.left) from rfl)
  have h2 : run (special false) (lc 0 (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (w j z))) (lc 0 (w j z) (ListBlank.cons 1 (ListBlank.cons 1 (w j z)))) := by
    simpa only [first, second, rc, lc, Nat.mul_succ, Nat.add_succ, w, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lscan (show (special false) 0 1 = some (some 0, Stmt.write 1 Dir.left) from rfl) 1 (w j z) (ListBlank.cons 1 (w j z))
  have h3 : run (special false) (lc 0 (w j z) (ListBlank.cons 1 (ListBlank.cons 1 (w j z)))) (first (0) (j+1)) := by
    simpa only [first, second, rc, lc, Nat.mul_succ, Nat.add_succ, w, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lscan (show (special false) 0 1 = some (some 0, Stmt.write 1 Dir.left) from rfl) j z (ListBlank.cons 1 (ListBlank.cons 1 (w j z)))
  exact starts h0 (cat h1 (cat h2 h3))

lemma first_sweep (j k : ℕ) : advances (special false) (first j (k+1)) (first (j+1) (k)) := by
  have h0 : (special false).step (first j (k+1)) = some (rc 1 (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))))) := by
    simpa only [first, second, rc, lc, Nat.mul_succ, Nat.add_succ, w, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right (w j z) (ListBlank.cons 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) (show (special false) 0 0 = some (some 1, Stmt.write 1 Dir.right) from rfl)
  have h1 : run (special false) (rc 1 (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))))) (rc 2 (ListBlank.cons 0 (ListBlank.cons 1 (w j z))) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa only [first, second, rc, lc, Nat.mul_succ, Nat.add_succ, w, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (show (special false) 1 1 = some (some 2, Stmt.write 0 Dir.right) from rfl)
  have h2 : run (special false) (rc 2 (ListBlank.cons 0 (ListBlank.cons 1 (w j z))) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) (rc 2 (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (w (2*k) (ListBlank.cons 0 (w j z)))) := by
    simpa only [first, second, rc, lc, Nat.mul_succ, Nat.add_succ, w, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rscan (show (special false) 2 1 = some (some 2, Stmt.write 1 Dir.right) from rfl) 1 (ListBlank.cons 0 (ListBlank.cons 1 (w j z))) (w (2*k) (ListBlank.cons 0 (w j z)))
  have h3 : run (special false) (rc 2 (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (w (2*k) (ListBlank.cons 0 (w j z)))) (rc 2 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (ListBlank.cons 0 (w j z))) := by
    simpa only [first, second, rc, lc, Nat.mul_succ, Nat.add_succ, w, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rscan (show (special false) 2 1 = some (some 2, Stmt.write 1 Dir.right) from rfl) (2*k) (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (ListBlank.cons 0 (w j z))
  have h4 : run (special false) (rc 2 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (ListBlank.cons 0 (w j z))) (lc 3 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (ListBlank.cons 1 (w j z))) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa only [first, second, rc, lc, Nat.mul_succ, Nat.add_succ, w, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using left (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (w j z) (show (special false) 2 0 = some (some 3, Stmt.write 1 Dir.left) from rfl)
  have h5 : run (special false) (lc 3 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (ListBlank.cons 1 (w j z))) (lc 0 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa only [first, second, rc, lc, Nat.mul_succ, Nat.add_succ, w, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using left (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (ListBlank.cons 1 (w j z)) (show (special false) 3 1 = some (some 0, Stmt.write 0 Dir.left) from rfl)
  have h6 : run (special false) (lc 0 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (first (j+1) (k)) := by
    simpa only [first, second, rc, lc, Nat.mul_succ, Nat.add_succ, w, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lscan (show (special false) 0 1 = some (some 0, Stmt.write 1 Dir.left) from rfl) (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))
  exact starts h0 (cat h1 (cat h2 (cat h3 (cat h4 (cat h5 h6)))))

theorem exception : ¬ (special false).IsHalting := by
  apply endless _ first
  · simp only [first, Nat.mul_zero, w, cz]
    rfl
  · intro j k
    cases k with
    | zero => exact ⟨_,_,first_restart j⟩
    | succ k => exact ⟨_,_,first_sweep j k⟩

end OMA.BB4Sweeps
namespace OMA.BB4H2

open Turing Turing.BusyBeaver

abbrev Symbol := Fin 2
abbrev State := Fin 4
abbrev Key := State × Symbol
abbrev Machine4 := Machine Symbol State

structure Move where
  state : State
  write : Symbol
  left : Bool
  deriving DecidableEq

structure Table where
  t00 : Option Move
  t01 : Option Move
  t10 : Option Move
  t11 : Option Move
  t20 : Option Move
  t21 : Option Move
  t30 : Option Move
  t31 : Option Move
  deriving DecidableEq

def Table.empty : Table := ⟨none, none, none, none, none, none, none, none⟩

def Table.get (tb : Table) (q : State) (a : Symbol) : Option Move :=
  match q.val, a.val with
  | 0, 0 => tb.t00
  | 0, _ => tb.t01
  | 1, 0 => tb.t10
  | 1, _ => tb.t11
  | 2, 0 => tb.t20
  | 2, _ => tb.t21
  | _, 0 => tb.t30
  | _, _ => tb.t31

def Table.set (tb : Table) (q : State) (a : Symbol) (m : Move) : Table :=
  match q.val, a.val with
  | 0, 0 => { tb with t00 := some m }
  | 0, _ => { tb with t01 := some m }
  | 1, 0 => { tb with t10 := some m }
  | 1, _ => { tb with t11 := some m }
  | 2, 0 => { tb with t20 := some m }
  | 2, _ => { tb with t21 := some m }
  | _, 0 => { tb with t30 := some m }
  | _, _ => { tb with t31 := some m }

def Move.flip (m : Move) : Move := { m with left := !m.left }

def Table.flip (tb : Table) : Table :=
  ⟨tb.t00.map Move.flip, tb.t01.map Move.flip,
   tb.t10.map Move.flip, tb.t11.map Move.flip,
   tb.t20.map Move.flip, tb.t21.map Move.flip,
   tb.t30.map Move.flip, tb.t31.map Move.flip⟩

theorem Table.get_set_self (tb : Table) (q : State) (a : Symbol) (m : Move) :
    (tb.set q a m).get q a = some m := by
  fin_cases q <;> fin_cases a <;> rfl

theorem Table.get_set_ne (tb : Table) {q q' : State} {a a' : Symbol} (m : Move)
    (h : (q', a') ≠ (q, a)) : (tb.set q a m).get q' a' = tb.get q' a' := by
  fin_cases q <;> fin_cases a <;> fin_cases q' <;> fin_cases a' <;>
    first | rfl | exact absurd rfl h

theorem Table.get_flip (tb : Table) (q : State) (a : Symbol) :
    tb.flip.get q a = (tb.get q a).map Move.flip := by
  fin_cases q <;> fin_cases a <;> rfl

structure Position where
  state : State
  ls : List Symbol
  head : Symbol
  rs : List Symbol
  deriving DecidableEq

def startPos : Position := ⟨0, [], 0, []⟩

def push (a : Symbol) (xs : List Symbol) : List Symbol :=
  match a.val, xs with
  | 0, [] => []
  | _, xs => a :: xs

def symHead : List Symbol → Symbol
  | [] => 0
  | x :: _ => x

theorem symHead_eq_headI (xs : List Symbol) : symHead xs = xs.headI := by
  cases xs <;> rfl

def listEq : List Symbol → List Symbol → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x.val y.val && listEq xs ys
  | _, _ => false

theorem listEq_eq_true {xs ys : List Symbol} (h : listEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => simp [listEq] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [listEq] at h
    | cons y ys =>
      simp only [listEq, Bool.and_eq_true] at h
      rw [Fin.ext (Nat.eq_of_beq_eq_true h.1), ih h.2]

def Position.move (c : Position) (m : Move) : Position :=
  if m.left then ⟨m.state, c.ls.tail, symHead c.ls, push m.write c.rs⟩
  else ⟨m.state, push m.write c.ls, symHead c.rs, c.rs.tail⟩

def Position.flip (c : Position) : Position := ⟨c.state, c.rs, c.head, c.ls⟩

theorem flip_move (c : Position) (m : Move) :
    (c.move m).flip = c.flip.move m.flip := by
  cases m with | mk q a d => cases d <;> rfl

theorem mk_push (a : Symbol) (xs : List Symbol) :
    ListBlank.mk (push a xs) = (ListBlank.mk xs).cons a := by
  fin_cases a
  · cases xs with
    | nil => exact (ListBlank.cons_head_tail (ListBlank.mk ([] : List Symbol))).symm
    | cons x xs => exact (ListBlank.cons_mk 0 (x :: xs)).symm
  · exact (ListBlank.cons_mk 1 xs).symm

def Position.view (c : Position) : Cfg Symbol State :=
  ⟨some c.state, ⟨c.head, ListBlank.mk c.ls, ListBlank.mk c.rs⟩⟩

theorem view_start : startPos.view = Machine.init [] := rfl

def Move.command (m : Move) : Option (Option State × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def Matches (M : Machine4) (tb : Table) : Prop :=
  ∀ q a m, tb.get q a = some m → M q a = m.command

theorem matches_set {M : Machine4} {tb : Table} {q : State} {a : Symbol} {m : Move}
    (hm : Matches M tb) (h : M q a = m.command) : Matches M (tb.set q a m) := by
  intro q' a' m' hh
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    rw [Table.get_set_self] at hh
    exact (Option.some.inj hh) ▸ h
  · rw [Table.get_set_ne tb m e] at hh
    exact hm q' a' m' hh

theorem step_move {M : Machine4} {tb : Table} (hm : Matches M tb) (c : Position) (m : Move)
    (h : tb.get c.state c.head = some m) :
    M.step c.view = some (c.move m).view := by
  have he := hm c.state c.head m h
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push, symHead_eq_headI]

theorem multi_succ_front (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    M.multiStep c (k + 1) = (M.step c).bind (fun c' => M.multiStep c' k) := by
  induction k with
  | zero => rw [Machine.multiStep_one]; cases M.step c <;> rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, ih]
    cases h : M.step c with
    | none => rfl
    | some d => simp [Machine.multiStep_succ]

-- ============================================================
-- Guarded repeatable-segment checker
-- ============================================================

def takePad : ℕ → List Symbol → List Symbol
  | 0, _ => []
  | k + 1, [] => 0 :: takePad k []
  | k + 1, x :: xs => x :: takePad k xs

theorem takePad_foldr_drop (k : ℕ) (xs : List Symbol) :
    (takePad k xs).foldr ListBlank.cons (ListBlank.mk (xs.drop k)) = ListBlank.mk xs := by
  induction k generalizing xs with
  | zero => simp [takePad]
  | succ k ih =>
    cases xs with
    | nil =>
      simp only [takePad, List.foldr_cons, List.drop_nil]
      have h0 := ih []
      simp only [List.drop_nil] at h0
      rw [h0]
      exact ListBlank.cons_head_tail (ListBlank.mk [])
    | cons x xs =>
      simp only [takePad, List.foldr_cons, List.drop_succ_cons]
      rw [ih xs, ListBlank.cons_mk]

def runGuardedLeft (tb : Table) : ℕ → State → Symbol → List Symbol → List Symbol →
    Option (State × Symbol × List Symbol × List Symbol)
  | 0, q, a, near, rs => some (q, a, near, rs)
  | k + 1, q, a, near, rs =>
    match tb.get q a with
    | none => none
    | some m =>
      if m.left then
        match near with
        | [] => none
        | a' :: near' => runGuardedLeft tb k m.state a' near' (push m.write rs)
      else
        runGuardedLeft tb k m.state (symHead rs) (m.write :: near) rs.tail

def checkGuardedLeft (tb : Table) (p : ℕ) (q : State) (a : Symbol)
    (near rs : List Symbol) : Bool :=
  match runGuardedLeft tb p q a near rs with
  | none => false
  | some (q', a', near', rs') =>
    Nat.beq q'.val q.val && Nat.beq a'.val a.val && listEq rs' rs &&
      listEq (near'.take near.length) near && Nat.ble near.length near'.length

theorem runGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near rs : List Symbol)
    {q' : State} {a' : Symbol} {near' rs' : List Symbol}
    (h : runGuardedLeft tb p q a near rs = some (q', a', near', rs'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ p =
      some ⟨some q', ⟨a', near'.foldr ListBlank.cons tail, ListBlank.mk rs'⟩⟩ := by
  induction p generalizing q a near rs with
  | zero =>
    simp only [runGuardedLeft, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | true =>
        simp only [hd, ↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q, ⟨a, (x :: xs).foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ =
              some ⟨some m.state, ⟨x, xs.foldr ListBlank.cons tail, ListBlank.mk (push m.write rs)⟩⟩ := by
            simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, mk_push]
          rw [hstep, Option.bind_some]
          exact ih m.state x xs (push m.write rs) h
      | false =>
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
        have hstep : M.step ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ =
            some ⟨some m.state, ⟨symHead rs, (m.write :: near).foldr ListBlank.cons tail, ListBlank.mk rs.tail⟩⟩ := by
          simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, symHead_eq_headI]
        rw [hstep, Option.bind_some]
        exact ih m.state (symHead rs) (m.write :: near) rs.tail h

theorem runGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near ls : List Symbol)
    {q' : State} {a' : Symbol} {near' ls' : List Symbol}
    (h : runGuardedLeft tb.flip p q a near ls = some (q', a', near', ls'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q', ⟨a', ListBlank.mk ls', near'.foldr ListBlank.cons tail⟩⟩ := by
  induction p generalizing q a near ls with
  | zero =>
    simp only [runGuardedLeft, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    rw [Table.get_flip] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht, Option.map_some] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | false =>
        simp only [Move.flip, hd, Bool.not_false, ↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q, ⟨a, ListBlank.mk ls, (x :: xs).foldr ListBlank.cons tail⟩⟩ =
              some ⟨some m.state, ⟨x, ListBlank.mk (push m.write ls), xs.foldr ListBlank.cons tail⟩⟩ := by
            simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, mk_push]
          rw [hstep, Option.bind_some]
          exact ih m.state x xs (push m.write ls) h
      | true =>
        simp only [Move.flip, hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        have hstep : M.step ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ =
            some ⟨some m.state, ⟨symHead ls, ListBlank.mk ls.tail, (m.write :: near).foldr ListBlank.cons tail⟩⟩ := by
          simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, symHead_eq_headI]
        rw [hstep, Option.bind_some]
        exact ih m.state (symHead ls) (m.write :: near) ls.tail h

theorem foldr_append (xs ys : List Symbol) (tail : ListBlank Symbol) :
    (xs ++ ys).foldr ListBlank.cons tail = xs.foldr ListBlank.cons (ys.foldr ListBlank.cons tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem checkGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near rs : List Symbol}
    (h : checkGuardedLeft tb p q a near rs = true) (tail : ListBlank Symbol) :
    ∃ tail', M.multiStep ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ p =
      some ⟨some q, ⟨a, near.foldr ListBlank.cons tail', ListBlank.mk rs⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb p q a near rs with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q', a', near', rs'⟩
    simp only [hr, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hrs⟩, htake⟩, _⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hrs' : rs' = rs := listEq_eq_true hrs
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hrs'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail, ?_⟩
    rw [runGuardedLeft_sound hm p q' a' near rs' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

theorem checkGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near ls : List Symbol}
    (h : checkGuardedLeft tb.flip p q a near ls = true) (tail : ListBlank Symbol) :
    ∃ tail', M.multiStep ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail'⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb.flip p q a near ls with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q', a', near', ls'⟩
    simp only [hr, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hls⟩, htake⟩, _⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hls' : ls' = ls := listEq_eq_true hls
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hls'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail, ?_⟩
    rw [runGuardedRight_sound hm p q' a' near ls' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

structure HistItem where
  step : ℕ
  pos : ℕ
  c : Position

def findRepAux (tb : Table) (cur : HistItem) (minp maxp : ℕ) : List HistItem → Bool
  | [] => false
  | hi :: rest =>
    let minp' := if Nat.ble minp hi.pos then minp else hi.pos
    let maxp' := if Nat.ble maxp hi.pos then hi.pos else maxp
    let ok :=
      if Nat.ble (hi.step + 1) cur.step && Nat.beq hi.c.state.val cur.c.state.val && Nat.beq hi.c.head.val cur.c.head.val then
        let p := cur.step - hi.step
        let leftOk :=
          if Nat.ble hi.pos cur.pos && listEq hi.c.rs cur.c.rs then
            let dL := hi.pos - minp'
            let near := takePad dL hi.c.ls
            if listEq (takePad dL cur.c.ls) near then
              checkGuardedLeft tb p hi.c.state hi.c.head near hi.c.rs
            else false
          else false
        if leftOk then true
        else if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
          let dR := maxp' - hi.pos
          let near := takePad dR hi.c.rs
          if listEq (takePad dR cur.c.rs) near then
            checkGuardedLeft tb.flip p hi.c.state hi.c.head near hi.c.ls
          else false
        else false
      else false
    if ok then true else findRepAux tb cur minp' maxp' rest

def findRep (tb : Table) (cur : HistItem) (prev : List HistItem) : Bool :=
  findRepAux tb cur 1000 0 prev

def HistValid (M : Machine4) (hist : List HistItem) : Prop :=
  ∀ h ∈ hist, h.step ≤ 107 ∧ M.multiStep (Machine.init []) h.step = some h.c.view

def NoRepeatHyp (M : Machine4) : Prop :=
  ∀ (i p : ℕ) (q : State) (a : Symbol) (side : Bool)
      (near : List Symbol) (fixed : ListBlank Symbol), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank Symbol =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg Symbol State)
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')

theorem findRepAux_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hLoop : NoRepeatHyp M) {cur : HistItem} {prev : List HistItem}
    (hcur : cur.step ≤ 107) (hvalid : HistValid M prev)
    {minp maxp : ℕ} (h : findRepAux tb cur minp maxp prev = true) : False := by
  induction prev generalizing minp maxp with
  | nil => simp [findRepAux] at h
  | cons hi rest ih =>
    unfold findRepAux at h
    dsimp only at h
    set minp' := if Nat.ble minp hi.pos then minp else hi.pos
    set maxp' := if Nat.ble maxp hi.pos then hi.pos else maxp
    by_cases hcond : (Nat.ble (hi.step + 1) cur.step && Nat.beq hi.c.state.val cur.c.state.val && Nat.beq hi.c.head.val cur.c.head.val) = true
    · simp only [hcond, ↓reduceIte] at h
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq_true_eq] at hcond
      have ⟨hstep_hi, hrun_hi⟩ := hvalid hi (List.mem_cons_self ..)
      have hp_pos : 0 < cur.step - hi.step := by omega
      have hp_le : hi.step + (cur.step - hi.step) ≤ 107 := by omega
      by_cases hleft : (if Nat.ble hi.pos cur.pos && listEq hi.c.rs cur.c.rs then
          if listEq (takePad (hi.pos - minp') cur.c.ls) (takePad (hi.pos - minp') hi.c.ls) then
            checkGuardedLeft tb (cur.step - hi.step) hi.c.state hi.c.head (takePad (hi.pos - minp') hi.c.ls) hi.c.rs
          else false else false) = true
      · split at hleft
        · split at hleft
          · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head true
              (takePad (hi.pos - minp') hi.c.ls) (ListBlank.mk hi.c.rs)
              hp_pos hp_le
              ⟨ListBlank.mk (hi.c.ls.drop (hi.pos - minp')), by
                simpa [Position.view, takePad_foldr_drop] using hrun_hi⟩
              (checkGuardedLeft_sound hm hleft)
          · contradiction
        · contradiction
      · simp only [hleft, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hright : (if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
            if listEq (takePad (maxp' - hi.pos) cur.c.rs) (takePad (maxp' - hi.pos) hi.c.rs) then
              checkGuardedLeft tb.flip (cur.step - hi.step) hi.c.state hi.c.head (takePad (maxp' - hi.pos) hi.c.rs) hi.c.ls
            else false else false) = true
        · split at hright
          · split at hright
            · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head false
                (takePad (maxp' - hi.pos) hi.c.rs) (ListBlank.mk hi.c.ls)
                hp_pos hp_le
                ⟨ListBlank.mk (hi.c.rs.drop (maxp' - hi.pos)), by
                  simpa [Position.view, takePad_foldr_drop] using hrun_hi⟩
                (checkGuardedRight_sound hm hright)
            · contradiction
          · contradiction
        · simp only [hright, Bool.false_eq_true, ↓reduceIte] at h
          exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
      exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h

-- ============================================================
-- FAR (Finite Automata Reduction) certificate verifier
-- ============================================================

inductive CanStop (tb : Table) : Position → Prop
  | missing {c} : tb.get c.state c.head = none → CanStop tb c
  | move {c m} : tb.get c.state c.head = some m → CanStop tb (c.move m) → CanStop tb c

theorem canStop_flip {tb : Table} {c : Position} (h : CanStop tb c) :
    CanStop tb.flip c.flip := by
  induction h with
  | missing h => exact .missing (by simpa [Position.flip, Table.get_flip] using h)
  | @move c m h _ ih =>
    refine .move (m := m.flip) ?_ ?_
    · change tb.flip.get c.state c.head = some m.flip
      simp [Table.get_flip, h]
    · rwa [← flip_move]

theorem cannot_stop_run {M : Machine4} {tb : Table}
    (hm : Matches M tb) (c : Position) (hc : ¬ CanStop tb c) (k : ℕ) :
    M.multiStep c.view k ≠ none := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    cases h : tb.get c.state c.head with
    | none => exact (hc (.missing h)).elim
    | some m =>
      rw [multi_succ_front, step_move hm c m h, Option.bind_some]
      exact ih _ (fun hs => hc (.move h hs))

structure TapeDFA where
  extraStates : ℕ
  code : ℕ

abbrev TapeDFA.size (D : TapeDFA) : ℕ := D.extraStates + 1

def TapeDFA.next (D : TapeDFA) (a : Symbol) (l : Fin D.size) : Fin D.size :=
  ⟨(D.code * D.size / D.size ^ (2 * l.val + a.val)) % D.size,
    Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem TapeDFA.blank (D : TapeDFA) : D.next 0 0 = 0 := by
  apply Fin.ext
  simp [TapeDFA.next]

def TapeDFA.read (D : TapeDFA) (xs : List Symbol) : Fin D.size :=
  xs.foldr D.next 0

theorem TapeDFA.read_push (D : TapeDFA) (a : Symbol) (xs : List Symbol) :
    D.read (push a xs) = D.next a (D.read xs) := by
  fin_cases a
  · cases xs with
    | nil => exact D.blank.symm
    | cons x xs => rfl
  · rfl

theorem TapeDFA.read_pop (D : TapeDFA) (xs : List Symbol) :
    D.next xs.headI (D.read xs.tail) = D.read xs := by
  cases xs
  · exact D.blank
  · rfl

structure Certificate where
  mirror : Bool
  dfa : TapeDFA
  edges : ℕ
  blankReach : ℕ

abbrev Node (cert : Certificate) := Option (State × Fin cert.dfa.size)

def nodeId (cert : Certificate) : Node cert → ℕ
  | none => 4 * cert.dfa.size
  | some (q, l) => q.val * cert.dfa.size + l.val

def Certificate.edgeRow (cert : Certificate) (p : Node cert) (a : Symbol) : ℕ :=
  match p with
  | none => 2 ^ (4 * cert.dfa.size)
  | some _ => (cert.edges / 2 ^ ((2 * nodeId cert p + a.val) * (4 * cert.dfa.size + 1))) %
      2 ^ (4 * cert.dfa.size + 1)

def Certificate.edge (cert : Certificate) (p : Node cert) (a : Symbol)
    (q : Node cert) : Bool :=
  (cert.edgeRow p a).testBit (nodeId cert q)

theorem edge_none (cert : Certificate) (a : Symbol) (q : Node cert) :
    cert.edge none a q = q.isNone := by
  unfold Certificate.edge Certificate.edgeRow
  simp only [Nat.testBit_two_pow]
  rcases q with _ | ⟨q, l⟩
  · simp [nodeId]
  · have hq : q.val ≤ 3 := Nat.le_of_lt_succ q.isLt
    have hl : l.val < cert.dfa.size := l.isLt
    have hne : 4 * cert.dfa.size ≠ q.val * cert.dfa.size + l.val := by
      have : q.val * cert.dfa.size ≤ 3 * cert.dfa.size := Nat.mul_le_mul_right _ hq
      omega
    simp [nodeId, hne]

def Certificate.onBlank (cert : Certificate) (p : Node cert) : Bool :=
  cert.blankReach.testBit (nodeId cert p)

def unpack (val : ℕ) : Certificate :=
  let extra := val / 2 % 32
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 64 / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1, ⟨extra, val / 64 % dfaBase⟩, payload / initialBase, payload % initialBase⟩

def nodes (cert : Certificate) : List (Node cert) :=
  none :: (List.finRange 4).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩ <;> simp [nodes]

def checkBlank (cert : Certificate) : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all fun p =>
      if cert.onBlank p then
        let row := cert.edgeRow p 0
        (nodes cert).all fun q => !row.testBit (nodeId cert q) || cert.onBlank q
      else true

def checkAt (tb : Table) (cert : Certificate) (q : State) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q, l)
  let pRow := cert.edgeRow p a
  match tb.get q a with
  | none => pRow.testBit (4 * cert.dfa.size)
  | some m =>
    if m.left then
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if Nat.beq (cert.dfa.next a' l').val l.val then
          let sRow := cert.edgeRow (some (m.state, l')) a'
          (nodes cert).all fun s =>
            if sRow.testBit (nodeId cert s) then
              let swRow := cert.edgeRow s m.write
              (nodes cert).all fun t => !swRow.testBit (nodeId cert t) || pRow.testBit (nodeId cert t)
            else true
        else true
    else pRow.testBit (nodeId cert (some (m.state, cert.dfa.next m.write l)))

def checkMachine (tb : Table) (cert : Certificate) : Bool :=
  (List.finRange 4).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAt tb cert q a l

inductive Reads (cert : Certificate) : Node cert → ListBlank Symbol → Prop
  | done (t) : Reads cert none t
  | step {p q t} : cert.edge p t.head q = true → Reads cert q t.tail → Reads cert p t

theorem Reads.push {cert : Certificate} {p q : Node cert} {a : Symbol} {xs : ListBlank Symbol}
    (he : cert.edge p a q = true) (h : Reads cert q xs) : Reads cert p (xs.cons a) :=
  .step (by simpa using he) (by simpa using h)

theorem Reads.pop {cert : Certificate} {p : Node cert} {xs : ListBlank Symbol} {a : Symbol}
    (h : Reads cert p (xs.cons a)) : ∃ q, cert.edge p a q = true ∧ Reads cert q xs := by
  cases h with
  | done => exact ⟨none, by simp [edge_none], .done _⟩
  | step he hr => exact ⟨_, by simpa using he, by simpa using hr⟩

theorem no_read_blank {cert : Certificate} (hb : checkBlank cert = true) :
    ¬ Reads cert (some (0, 0)) (ListBlank.mk []) := by
  simp only [checkBlank, Bool.and_eq_true_iff, Bool.not_eq_true_eq_eq_false] at hb
  obtain ⟨⟨hstart, hsink⟩, hclosure⟩ := hb
  have each {p : Node cert} {t : ListBlank Symbol} (hr : Reads cert p t) :
      t = ListBlank.mk [] → cert.onBlank p = true → False := by
    induction hr with
    | done _ => intro _ hp; exact Bool.noConfusion (hp.symm.trans hsink)
    | @step p q t he _ ih =>
      rintro rfl hp
      have ht := allNodes hclosure p
      simp only [hp, if_true] at ht
      have hn := allNodes ht q
      have he0 : (cert.edgeRow p 0).testBit (nodeId cert q) = true := he
      simp [he0] at hn
      exact ih rfl hn
  exact fun hr => each hr rfl hstart

theorem reads_of_canStop {tb : Table} {cert : Certificate} (hchk : checkMachine tb cert = true)
    {c : Position} (hs : CanStop tb c) :
    Reads cert (some (c.state, cert.dfa.read c.ls)) ((ListBlank.mk c.rs).cons c.head) := by
  induction hs with
  | @missing c hh =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt, hh] at h
    exact Reads.push (show cert.edge (some (c.state, cert.dfa.read c.ls)) c.head none = true from h) (.done _)
  | @move c m hh _ ih =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt, hh] at h
    cases hd : m.left with
    | false =>
      have hstep : cert.edge (some (c.state, cert.dfa.read c.ls)) c.head
          (some (m.state, cert.dfa.next m.write (cert.dfa.read c.ls))) = true := by
        simpa [hd, Certificate.edge] using h
      refine Reads.push hstep ?_
      simpa [Position.move, hd, TapeDFA.read_push, symHead_eq_headI, ← ListBlank.head_mk, ← ListBlank.tail_mk]
        using ih
    | true =>
      have hr : Reads cert (some (m.state, cert.dfa.read c.ls.tail))
          (((ListBlank.mk c.rs).cons m.write).cons c.ls.headI) := by
        simpa [Position.move, hd, mk_push, symHead_eq_headI] using ih
      obtain ⟨s, he, hr⟩ := Reads.pop hr
      obtain ⟨t, hf, ht⟩ := Reads.pop hr
      simp only [hd, if_true] at h
      have h' := allFin (allFin h (cert.dfa.read c.ls.tail)) c.ls.headI
      have hbeq : Nat.beq (cert.dfa.next c.ls.headI (cert.dfa.read c.ls.tail)).val (cert.dfa.read c.ls).val = true := by
        simp [TapeDFA.read_pop]
      simp only [hbeq, if_true] at h'
      have h'' := allNodes h' s
      have he' : (cert.edgeRow (some (m.state, cert.dfa.read c.ls.tail)) c.ls.headI).testBit (nodeId cert s) = true := he
      simp only [he', if_true] at h''
      have h''' := allNodes h'' t
      have hf' : (cert.edgeRow s m.write).testBit (nodeId cert t) = true := hf
      simp [hf'] at h'''
      exact Reads.push h''' ht

def checkCertificate (tb : Table) (val : ℕ) : Bool :=
  let C := unpack val
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

theorem certificate_sound {tb : Table} {val : ℕ}
    (h : checkCertificate tb val = true) : ¬ CanStop tb startPos := by
  intro hs
  unfold checkCertificate at h
  have ⟨hb, hm⟩ := Bool.and_eq_true_iff.mp h
  apply no_read_blank hb
  have blank : (ListBlank.mk ([] : List Symbol)).cons 0 = ListBlank.mk [] :=
    ListBlank.cons_head_tail (ListBlank.mk [])
  split at hm
  · simpa only [Position.flip, startPos, TapeDFA.read, List.foldr_nil, blank] using
      (reads_of_canStop hm (canStop_flip hs))
  · simpa only [startPos, TapeDFA.read, List.foldr_nil, blank] using (reads_of_canStop hm hs)

-- ============================================================
-- Symmetry: swapping states 2 and 3
-- ============================================================

def swap23 : Equiv.Perm State := Equiv.swap (2 : State) (3 : State)

theorem swap23_0 : swap23 0 = 0 := by decide
theorem swap23_1 : swap23 1 = 1 := by decide
theorem swap23_2 : swap23 2 = 3 := by decide
theorem swap23_3 : swap23 3 = 2 := by decide
theorem swap23_inv (q : State) : swap23.symm q = swap23 q := by fin_cases q <;> decide

def reindex23 (M : Machine4) : Machine4 :=
  fun q a => (M (swap23 q) a).map fun (s, b) => (s.map swap23, b)

def mapCfg23 (c : Cfg Symbol State) : Cfg Symbol State :=
  ⟨c.q.map swap23, c.tape⟩

theorem reindex23_step (M : Machine4) (c : Cfg Symbol State) :
    (reindex23 M).step (mapCfg23 c) = (M.step c).map mapCfg23 := by
  obtain ⟨q, t⟩ := c
  cases q with
  | none => rfl
  | some q =>
    simp only [Machine.step, mapCfg23, Option.map_some, reindex23]
    have hinv : swap23 (swap23 q) = q := by fin_cases q <;> decide
    rw [hinv]
    cases M q t.head with
    | none => rfl
    | some entry => rfl

theorem reindex23_multi (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    (reindex23 M).multiStep (mapCfg23 c) k = (M.multiStep c k).map mapCfg23 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
    cases M.multiStep c k with
    | none => rfl
    | some c' => exact reindex23_step M c'

theorem mapCfg23_init : mapCfg23 (Machine.init []) = Machine.init [] := by
  simp [mapCfg23, Machine.init, swap23_0]


def sp0Table : Table :=
  ⟨some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, some ⟨0, 1, true⟩, some ⟨2, 0, false⟩,
   some ⟨3, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 0, true⟩⟩

def sp1Table : Table :=
  ⟨some ⟨1, 1, false⟩, some ⟨1, 0, false⟩, some ⟨2, 1, true⟩, some ⟨1, 1, false⟩,
   none, some ⟨3, 0, true⟩, some ⟨0, 1, false⟩, some ⟨3, 1, true⟩⟩

def m0Table : Table :=
  ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨2, 1, false⟩, some ⟨3, 1, false⟩,
   some ⟨0, 1, true⟩, some ⟨1, 0, false⟩, some ⟨0, 1, false⟩, none⟩

def tblOfList (entries : List ℕ) : Machine4 := fun q a =>
  let v := entries[2*q.val+a.val]?.getD 16
  if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩,
    Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩ (if v % 2 = 0 then Dir.right else Dir.left))

theorem eq_sp0_of_matches {M : Machine4} (hm : Matches M sp0Table) (hMiss : ∃ q a, M q a = none) :
    M = tblOfList [6,3,3,8,15,10,16,1] := by
  obtain ⟨qm, am, hMmiss⟩ := hMiss
  have hqm : qm = 3 ∧ am = 0 := by
    fin_cases qm <;> fin_cases am
    · exfalso; change M 0 0 = none at hMmiss; rw [hm 0 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 0 1 = none at hMmiss; rw [hm 0 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 0 = none at hMmiss; rw [hm 1 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 1 = none at hMmiss; rw [hm 1 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 2 0 = none at hMmiss; rw [hm 2 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 2 1 = none at hMmiss; rw [hm 2 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exact ⟨rfl, rfl⟩
    · exfalso; change M 3 1 = none at hMmiss; rw [hm 3 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
  rcases hqm with ⟨rfl, rfl⟩
  funext q a
  fin_cases q <;> fin_cases a
  · exact hm 0 0 _ rfl
  · exact hm 0 1 _ rfl
  · exact hm 1 0 _ rfl
  · exact hm 1 1 _ rfl
  · exact hm 2 0 _ rfl
  · exact hm 2 1 _ rfl
  · exact hMmiss
  · exact hm 3 1 _ rfl

theorem eq_sp1_of_matches {M : Machine4} (hm : Matches M sp1Table) (hMiss : ∃ q a, M q a = none) :
    M = tblOfList [6,4,11,6,16,13,2,15] := by
  obtain ⟨qm, am, hMmiss⟩ := hMiss
  have hqm : qm = 2 ∧ am = 0 := by
    fin_cases qm <;> fin_cases am
    · exfalso; change M 0 0 = none at hMmiss; rw [hm 0 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 0 1 = none at hMmiss; rw [hm 0 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 0 = none at hMmiss; rw [hm 1 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 1 = none at hMmiss; rw [hm 1 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exact ⟨rfl, rfl⟩
    · exfalso; change M 2 1 = none at hMmiss; rw [hm 2 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 3 0 = none at hMmiss; rw [hm 3 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 3 1 = none at hMmiss; rw [hm 3 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
  rcases hqm with ⟨rfl, rfl⟩
  funext q a
  fin_cases q <;> fin_cases a
  · exact hm 0 0 _ rfl
  · exact hm 0 1 _ rfl
  · exact hm 1 0 _ rfl
  · exact hm 1 1 _ rfl
  · exact hMmiss
  · exact hm 2 1 _ rfl
  · exact hm 3 0 _ rfl
  · exact hm 3 1 _ rfl

def runPos (tb : Table) : ℕ → Position → Option Position
  | 0, c => some c
  | k + 1, c =>
    match tb.get c.state c.head with
    | none => none
    | some m => runPos tb k (c.move m)

theorem runPos_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (k : ℕ) (c : Position) {c' : Position} (h : runPos tb k c = some c') :
    M.multiStep c.view k = some c'.view := by
  induction k generalizing c with
  | zero =>
    simp only [runPos, Option.some.injEq] at h; subst h; rfl
  | succ k ih =>
    simp only [runPos] at h
    cases ht : tb.get c.state c.head with
    | none => simp [ht] at h
    | some m =>
      simp only [ht] at h
      rw [multi_succ_front, step_move hm c m ht, Option.bind_some]
      exact ih (c.move m) h

theorem run_add (M : Machine4) (x : Cfg Symbol State) (m n : ℕ) :
    M.multiStep x (m + n) = (M.multiStep x m).bind (fun y => M.multiStep y n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, Machine.multiStep_succ, ih]
    cases M.multiStep x m <;> simp

theorem m0_not_halting {M : Machine4} (hm : Matches M m0Table) (hHalts : M.IsHalting) : False := by
  have h85 : ∃ c85, runPos m0Table 85 startPos = some c85 ∧
      checkGuardedLeft m0Table.flip 29 c85.state c85.head [] c85.ls = true := by
    refine ⟨(runPos m0Table 85 startPos).getD startPos, ?_, ?_⟩ <;> decide +kernel
  obtain ⟨c85, hrun, hcyc⟩ := h85
  have hM85 : M.multiStep (Machine.init []) 85 = some c85.view := runPos_sound hm 85 startPos hrun
  let cfg (tail : ListBlank Symbol) : Cfg Symbol State :=
    ⟨some c85.state, ⟨c85.head, ListBlank.mk c85.ls, tail⟩⟩
  have hEnter : ∃ tail, M.multiStep (Machine.init []) 85 = some (cfg tail) :=
    ⟨ListBlank.mk c85.rs, hM85⟩
  have hStep : ∀ tail, ∃ tail', M.multiStep (cfg tail) 29 = some (cfg tail') := by
    intro tail
    simpa [cfg] using checkGuardedRight_sound hm hcyc tail
  have hRec (m : ℕ) : ∃ tail, M.multiStep (Machine.init []) (85 + 29 * m) = some (cfg tail) := by
    induction m with
    | zero => simpa using hEnter
    | succ m ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨t', ht'⟩ := hStep t
      refine ⟨t', ?_⟩
      rw [Nat.mul_succ, ← Nat.add_assoc, run_add M _ (85 + 29 * m) 29, ht]
      exact ht'
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hHalts
  obtain ⟨t, ht⟩ := hRec (k + 1)
  have hnone := Machine.multiStep_eq_none_mono hk (by omega : k + 1 ≤ 85 + 29 * (k + 1))
  rw [ht] at hnone
  contradiction

def GoodMachine (M : Machine4) : Prop :=
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) ∧
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) ∧
  (∃ q a, M q a = none) ∧
  NoRepeatHyp M ∧
  M.IsHalting ∧
  (M ≠ tblOfList [6,3,3,8,15,10,16,1] ∧ reindex23 M ≠ tblOfList [6,3,3,8,15,10,16,1]) ∧
  (M ≠ tblOfList [6,4,11,6,16,13,2,15] ∧ reindex23 M ≠ tblOfList [6,4,11,6,16,13,2,15])

theorem reindex23_invol (M : Machine4) : reindex23 (reindex23 M) = M := by
  funext q a
  have hinv : swap23 (swap23 q) = q := by fin_cases q <;> decide
  simp only [reindex23, hinv]
  cases M q a with
  | none => rfl
  | some p =>
    rcases p with ⟨s, b⟩
    cases s with
    | none => rfl
    | some s =>
      have hs : swap23 (swap23 s) = s := by fin_cases s <;> decide
      simp [hs]

theorem goodMachine_reindex23 {M : Machine4} (hG : GoodMachine M) :
    GoodMachine (reindex23 M) := by
  obtain ⟨⟨q0, t0, hRun⟩, hForm, ⟨qm, am, hMiss⟩, hLoop, hHalts, ⟨hsp0, hsp0'⟩, ⟨hsp1, hsp1'⟩⟩ := hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨hsp0', by rwa [reindex23_invol]⟩, ⟨hsp1', by rwa [reindex23_invol]⟩⟩
  · refine ⟨swap23 q0, t0, ?_⟩
    rw [← mapCfg23_init, reindex23_multi, hRun]; rfl
  · intro q a
    rcases hForm (swap23 q) a with h | ⟨q', z, h⟩
    · left; simp [reindex23, h]
    · right; exact ⟨swap23 q', z, by simp [reindex23, h]⟩
  · exact ⟨swap23 qm, am, by
      have : swap23 (swap23 qm) = qm := by fin_cases qm <;> decide
      simp [reindex23, this, hMiss]⟩
  · intro i p q a side near fixed hp hle cfg hEnter hCycle
    let cfgM : ListBlank Symbol → Cfg Symbol State := fun tail =>
      let free := near.foldr ListBlank.cons tail
      ⟨some (swap23 q), if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩
    have hmap : ∀ tail, mapCfg23 (cfgM tail) = cfg tail := by
      intro tail
      have : swap23 (swap23 q) = q := by fin_cases q <;> decide
      simp [mapCfg23, cfgM, cfg, this]
    apply hLoop i p (swap23 q) a side near fixed hp hle
    · obtain ⟨tail, ht⟩ := hEnter
      rw [← mapCfg23_init, reindex23_multi] at ht
      cases hMi : M.multiStep (Machine.init []) i with
      | none => simp [hMi] at ht
      | some c' =>
        simp only [hMi, Option.map_some, Option.some.injEq] at ht
        refine ⟨tail, ?_⟩
        congr 1
        obtain ⟨q', t'⟩ := c'
        simp only [mapCfg23, cfg, Cfg.mk.injEq] at ht
        rcases ht with ⟨hq', ht'⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this, ht']
    · intro tail
      obtain ⟨tail', ht'⟩ := hCycle tail
      rw [← hmap tail, reindex23_multi] at ht'
      cases hMp : M.multiStep (cfgM tail) p with
      | none => simp [hMp] at ht'
      | some c' =>
        simp only [hMp, Option.map_some, Option.some.injEq] at ht'
        refine ⟨tail', ?_⟩
        congr 1
        obtain ⟨q', t'⟩ := c'
        simp only [mapCfg23, cfg, Cfg.mk.injEq] at ht'
        rcases ht' with ⟨hq', ht''⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this, ht'']
  · obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hHalts
    refine (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k, ?_⟩
    unfold Machine.HaltsAfter
    rw [← mapCfg23_init, reindex23_multi, hk]; rfl

def UsesOnly01 (tb : Table) : Prop :=
  tb.t20 = none ∧ tb.t21 = none ∧ tb.t30 = none ∧ tb.t31 = none ∧
  (∀ q a m, tb.get q a = some m → m.state = 0 ∨ m.state = 1)

theorem matches_reindex23 {M : Machine4} {tb : Table}
    (hm : Matches M tb) (h01 : UsesOnly01 tb) : Matches (reindex23 M) tb := by
  intro q a m hget
  have hms := h01.2.2.2.2 q a m hget
  have hq : q = 0 ∨ q = 1 := by
    fin_cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
    · fin_cases a <;> simp [Table.get, h01.1, h01.2.1] at hget
    · fin_cases a <;> simp [Table.get, h01.2.2.1, h01.2.2.2.1] at hget
  have hsq : swap23 q = q := by rcases hq with rfl | rfl <;> decide
  have hsm : swap23 m.state = m.state := by rcases hms with h | h <;> rw [h] <;> decide
  simp only [reindex23, hsq, hm q a m hget, Move.command, Option.map_some, hsm]

theorem histValid_reindex23 {M : Machine4} {hist : List HistItem}
    (hv : HistValid M hist)
    (h01 : ∀ h ∈ hist, h.c.state = 0 ∨ h.c.state = 1) :
    HistValid (reindex23 M) hist := by
  intro h hh
  have ⟨hle, hrun⟩ := hv h hh
  refine ⟨hle, ?_⟩
  rw [← mapCfg23_init, reindex23_multi, hrun]
  have hs : swap23 h.c.state = h.c.state := by
    rcases h01 h hh with hs | hs <;> rw [hs] <;> decide
  simp [mapCfg23, Position.view, hs]

-- ============================================================
-- Stateful DFS Tree Verifier
-- ============================================================

def holes (tb : Table) : Finset Key :=
  Finset.univ.filter fun k => tb.get k.1 k.2 = none

theorem holes_set (tb : Table) (q : State) (a : Symbol) (m : Move) :
    holes (tb.set q a m) = (holes tb).erase (q, a) := by
  ext ⟨q', a'⟩
  simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    simp [Table.get_set_self]
  · simp [Table.get_set_ne tb m e, e]

def moves12 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩]

def moves16 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩,
   ⟨3, 0, false⟩, ⟨3, 0, true⟩, ⟨3, 1, false⟩, ⟨3, 1, true⟩]

def movesAllowed (used2 : Bool) : List Move :=
  if used2 then moves16 else moves12

theorem mem_movesAllowed (used2 : Bool) (m : Move) (h : used2 = false → m.state ≠ 3) :
    m ∈ movesAllowed used2 := by
  obtain ⟨q, a, d⟩ := m
  cases used2
  · have h3 := h rfl
    fin_cases q <;> fin_cases a <;> cases d <;> simp_all [movesAllowed, moves12]
  · fin_cases q <;> fin_cases a <;> cases d <;> simp [movesAllowed, moves16]

inductive StepResult where
  | rep
  | done
  | missing (q : State) (a : Symbol) (rem : ℕ) (cur : HistItem) (prev : List HistItem)

def stepLoop (tb : Table) : ℕ → HistItem → List HistItem → StepResult
  | 0, _, _ => .done
  | rem + 1, cur, prev =>
    match tb.get cur.c.state cur.c.head with
    | none => .missing cur.c.state cur.c.head (rem + 1) cur prev
    | some m =>
      let nc := cur.c.move m
      let nstep := cur.step + 1
      let npos := if m.left then cur.pos - 1 else cur.pos + 1
      let ncur : HistItem := ⟨nstep, npos, nc⟩
      let nprev := cur :: prev
      if (Nat.beq nstep 6 || Nat.beq nstep 12 || Nat.beq nstep 24 || Nat.beq nstep 48 || Nat.beq nstep 107) &&
          findRep tb ncur nprev then
        .rep
      else
        stepLoop tb rem ncur nprev

def checkMoves (f : Move → List ℕ → Option (List ℕ)) : List Move → List ℕ → Option (List ℕ)
  | [], certs => some certs
  | m :: ms, certs =>
    match f m certs with
    | none => none
    | some rest => checkMoves f ms rest

def checkTree : ℕ → Bool → Table → ℕ → HistItem → List HistItem → List ℕ → Option (List ℕ)
  | 0, _, _, _, _, _, _ => none
  | holesLeft + 1, used2, tb, rem, cur, prev, certs =>
    match stepLoop tb rem cur prev with
    | .rep => some certs
    | .done =>
      match certs with
      | [] => none
      | v :: rest =>
        if Nat.beq v 0 then
          if tb == sp0Table || tb == sp1Table || tb == m0Table then some rest else none
        else if checkCertificate tb v then some rest else none
    | .missing q a rem' cur' prev' =>
      if Nat.beq holesLeft 0 then some certs
      else
        checkMoves (fun m rest =>
          checkTree holesLeft (used2 || Nat.beq m.state.val 2) (tb.set q a m) rem' cur' prev' rest)
          (movesAllowed used2) certs

theorem checkMoves_each {f : Move → List ℕ → Option (List ℕ)} {ms : List Move}
    {a b : List ℕ} (h : checkMoves f ms a = some b) {m : Move} (hm : m ∈ ms) :
    ∃ x y, f m x = some y := by
  induction ms generalizing a with
  | nil => simp at hm
  | cons head tail ih =>
    unfold checkMoves at h
    cases hh : f head a with
    | none => simp [hh] at h
    | some mid =>
      simp only [hh] at h
      rcases List.mem_cons.mp hm with rfl | ht
      · exact ⟨a, mid, hh⟩
      · exact ih h ht

theorem stepLoop_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) :
    match stepLoop tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev', h.c.state = 0 ∨ h.c.state = 1) := by
  induction rem generalizing cur prev with
  | zero => simp [stepLoop]
  | succ rem ih =>
    unfold stepLoop
    cases ht : tb.get cur.c.state cur.c.head with
    | none =>
      exact ⟨ht, rfl, rfl, hsum, Nat.succ_pos _, hv, h01⟩
    | some m =>
      simp only [ht]
      have ⟨hcur_le, hcur_run⟩ := hv cur (List.mem_cons_self ..)
      let ncur : HistItem := ⟨cur.step + 1, if m.left then cur.pos - 1 else cur.pos + 1, cur.c.move m⟩
      have hncur_run : M.multiStep (Machine.init []) (cur.step + 1) = some ncur.c.view := by
        rw [Machine.multiStep_succ, hcur_run]
        exact step_move hm cur.c m ht
      have hnv : HistValid M (ncur :: cur :: prev) := by
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact ⟨by dsimp [ncur]; omega, hncur_run⟩
        · exact hv h hh'
      have hn01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ ncur :: cur :: prev, h.c.state = 0 ∨ h.c.state = 1 := by
        intro hu
        have ⟨u, hprev01⟩ := h01 hu
        refine ⟨u, fun h hh => ?_⟩
        rcases List.mem_cons.mp hh with rfl | hh'
        · have hms := u.2.2.2.2 cur.c.state cur.c.head m ht
          cases hd : m.left <;> simpa [ncur, Position.move, hd] using hms
        · exact hprev01 h hh'
      by_cases hrep : ((Nat.beq (cur.step + 1) 6 || Nat.beq (cur.step + 1) 12 || Nat.beq (cur.step + 1) 24 ||
          Nat.beq (cur.step + 1) 48 || Nat.beq (cur.step + 1) 107) && findRep tb ncur (cur :: prev)) = true
      · rw [if_pos hrep]
        simp only [Bool.and_eq_true] at hrep
        exact findRepAux_sound hm hG.2.2.2.1 (by dsimp [ncur]; omega) hv hrep.2
      · rw [if_neg hrep]
        exact ih (by dsimp [ncur]; omega) hnv hn01

theorem usesOnly01_set {tb : Table} (h01 : UsesOnly01 tb) {q : State} {a : Symbol} {m : Move}
    (hq : q = 0 ∨ q = 1) (hm : m.state = 0 ∨ m.state = 1) :
    UsesOnly01 (tb.set q a m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.2.1
  · intro q' a' m' hh
    by_cases e : (q', a') = (q, a)
    · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
      rw [Table.get_set_self] at hh
      exact (Option.some.inj hh) ▸ hm
    · rw [Table.get_set_ne tb m e] at hh
      exact h01.2.2.2.2 q' a' m' hh

theorem checkTree_sound {holesLeft : ℕ} {used2 : Bool} {tb : Table}
    {rem : ℕ} {cur : HistItem} {prev : List HistItem} {a b : List ℕ}
    (hCount : (holes tb).card ≤ holesLeft)
    (hCheck : checkTree holesLeft used2 tb rem cur prev a = some b) :
    ∀ M : Machine4, GoodMachine M → Matches M tb →
      cur.step + rem = 107 →
      HistValid M (cur :: prev) →
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
      False := by
  induction holesLeft generalizing used2 tb rem cur prev a b with
  | zero => simp [checkTree] at hCheck
  | succ holesLeft ih =>
    intro M hG hm hsum hv hu
    unfold checkTree at hCheck
    have hstep := stepLoop_sound hm hG hsum hv hu
    cases hsl : stepLoop tb rem cur prev with
    | rep => rw [hsl] at hstep; exact hstep
    | done =>
      simp only [hsl] at hCheck
      cases a with
      | nil => simp at hCheck
      | cons v rest =>
        simp only at hCheck
        by_cases hv0 : Nat.beq v 0 = true
        · simp only [hv0, ↓reduceIte] at hCheck
          split at hCheck
          · rename_i hsp
            simp only [Bool.or_eq_true, beq_iff_eq] at hsp
            rcases hsp with (rfl | rfl) | rfl
            · exact hG.2.2.2.2.2.1.1 (eq_sp0_of_matches hm hG.2.2.1)
            · exact hG.2.2.2.2.2.2.1 (eq_sp1_of_matches hm hG.2.2.1)
            · exact m0_not_halting hm hG.2.2.2.2.1
          · simp at hCheck
        · simp only [hv0, Bool.false_eq_true, ↓reduceIte] at hCheck
          split at hCheck
          · rename_i hcert
            have hns := certificate_sound hcert
            obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hG.2.2.2.2.1
            exact cannot_stop_run hm startPos hns (k + 1) hk
          · simp at hCheck
    | missing q a rem' cur' prev' =>
      simp only [hsl] at hCheck hstep
      obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
      have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
      -- M must define (q, a) as some (some q', z) since cur'.step < 107 and M runs past 107
      have hM_def : ∃ q' z, M q a = some (some q', z) := by
        rcases hG.2.1 q a with hMnone | hMsome
        · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
            rw [Machine.multiStep_succ, hcur'_run]
            simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
          have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
          obtain ⟨q0, t0, hrun107⟩ := hG.1
          rw [h107] at hrun107
          contradiction
        · exact hMsome
      obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
      split at hCheck
      · -- holesLeft == 0: (holes tb).card ≤ 1 and (q, a) ∈ holes tb, so M has no none!
        rename_i h0
        have h0' : holesLeft = 0 := Nat.eq_of_beq_eq_true h0
        have hmem : (q, a) ∈ holes tb := by simp [holes, hnone]
        have hcard1 : (holes tb).card = 1 :=
          le_antisymm (by omega) (Finset.card_pos.mpr ⟨_, hmem⟩)
        obtain ⟨qm, am, hMmiss⟩ := hG.2.2.1
        have hqm_mem : (qm, am) ∈ holes tb := by
          simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and]
          cases hget : tb.get qm am with
          | none => rfl
          | some m =>
            have := hm qm am m hget
            rw [hMmiss] at this
            simp [Move.command] at this
        have heq_key : (qm, am) = (q, a) := by
          have hsub : ({(q, a)} : Finset Key) ⊆ holes tb := Finset.singleton_subset_iff.mpr hmem
          have hEq := Finset.eq_of_subset_of_card_le hsub (by simp [hcard1])
          rw [← hEq, Finset.mem_singleton] at hqm_mem
          exact hqm_mem
        rcases Prod.mk.inj heq_key with ⟨rfl, rfl⟩
        rw [hMmiss] at hMqa
        contradiction
      · -- Branch on movesAllowed used2
        let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
        have hm_cmd : M q a = m.command := by
          cases d <;> simpa [m, Move.command] using hMqa
        have hmem_hole : (q, a) ∈ holes tb := by simp [holes, hnone]
        have hcard_next : (holes (tb.set q a m)).card ≤ holesLeft := by
          rw [holes_set, Finset.card_erase_of_mem hmem_hole]
          omega
        by_cases hswap : used2 = false ∧ q' = 3
        · rcases hswap with ⟨hu2, rfl⟩
          have ⟨h01, hprev01⟩ := hu' hu2
          let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
          have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
          obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m2
          have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
          have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
          have hM2qa : (reindex23 M) q a = m2.command := by
            cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
          have hcard2 : (holes (tb.set q a m2)).card ≤ holesLeft := by
            rw [holes_set, Finset.card_erase_of_mem hmem_hole]
            omega
          exact ih hcard2 hxy (reindex23 M) (goodMachine_reindex23 hG)
            (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
            (histValid_reindex23 hv' hprev01) (by simp [m2])
        · have hmem_m : m ∈ movesAllowed used2 :=
            mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
          obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m
          refine ih hcard_next hxy M hG (matches_set hm hm_cmd) hsum' hv' ?_
          intro hnext_u2
          simp only [Bool.or_eq_false_iff] at hnext_u2
          have ⟨h01, hprev01⟩ := hu' hnext_u2.1
          have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
          have hm01 : m.state = 0 ∨ m.state = 1 := by
            have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
            have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
            fin_cases q' <;> simp_all [m]
          exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩

def TreeValid (tb : Table) (used2 : Bool) (rem : ℕ) (cur : HistItem) (prev : List HistItem) : Prop :=
  ∀ M : Machine4, GoodMachine M → Matches M tb →
    cur.step + rem = 107 →
    HistValid M (cur :: prev) →
    (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
    False

theorem branch_one {tb : Table} {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    {q : State} {a : Symbol} {rem' : ℕ} {cur' : HistItem} {prev' : List HistItem}
    (hsl : stepLoop tb rem cur prev = .missing q a rem' cur' prev')
    (hChildren : ∀ m ∈ movesAllowed used2,
      TreeValid (tb.set q a m) (used2 || Nat.beq m.state.val 2) rem' cur' prev') :
    TreeValid tb used2 rem cur prev := by
  intro M hG hm hsum hv hu
  have hstep := stepLoop_sound hm hG hsum hv hu
  simp only [hsl] at hstep
  obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
  have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
  have hM_def : ∃ q' z, M q a = some (some q', z) := by
    rcases hG.2.1 q a with hMnone | hMsome
    · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
        rw [Machine.multiStep_succ, hcur'_run]
        simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
      have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
      obtain ⟨q0, t0, hrun107⟩ := hG.1
      rw [h107] at hrun107
      contradiction
    · exact hMsome
  obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
  let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
  have hm_cmd : M q a = m.command := by cases d <;> simpa [m, Move.command] using hMqa
  by_cases hswap : used2 = false ∧ q' = 3
  · rcases hswap with ⟨hu2, rfl⟩
    have ⟨h01, hprev01⟩ := hu' hu2
    let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
    have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
    have hM2qa : (reindex23 M) q a = m2.command := by
      cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
    exact hChildren m2 hmem_m2 (reindex23 M) (goodMachine_reindex23 hG)
      (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
      (histValid_reindex23 hv' hprev01) (by simp [m2])
  · have hmem_m : m ∈ movesAllowed used2 :=
      mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
    refine hChildren m hmem_m M hG (matches_set hm hm_cmd) hsum' hv' ?_
    intro hnext_u2
    simp only [Bool.or_eq_false_iff] at hnext_u2
    have ⟨h01, hprev01⟩ := hu' hnext_u2.1
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hm01 : m.state = 0 ∨ m.state = 1 := by
      have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
      have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
      fin_cases q' <;> simp_all [m]
    exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩



def baseTable : Table := Table.empty.set 0 0 ⟨1, 1, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 1, false⟩⟩

private theorem mk_good_ne_sp1 (M : Machine4) (h : M 1 0 ≠ some (some 2, Stmt.write 1 Dir.left))
    (h2 : M 1 0 ≠ some (some 3, Stmt.write 1 Dir.left)) :
    M ≠ tblOfList [6,4,11,6,16,13,2,15] ∧ reindex23 M ≠ tblOfList [6,4,11,6,16,13,2,15] := by
  refine ⟨fun heq => h (by rw [heq]; rfl), fun heq => h2 ?_⟩
  have h10 := congrFun (congrFun heq 1) 0
  have hrhs : tblOfList [6,4,11,6,16,13,2,15] 1 0 = some (some 2, Stmt.write 1 Dir.left) := rfl
  rw [hrhs] at h10
  simp only [reindex23, swap23_1] at h10
  cases hM : M 1 0 with
  | none => simp [hM] at h10
  | some p =>
    rcases p with ⟨s, z⟩
    cases s with
    | none => simp [hM] at h10
    | some s =>
      simp only [hM, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h10
      rcases h10 with ⟨hs, hz⟩
      have hs3 : s = 3 := by revert hs; fin_cases s <;> decide
      subst hs3; subst hz; rfl

private theorem mk_good_ne_sp0 (M : Machine4) (h : M 1 0 ≠ some (some 0, Stmt.write 1 Dir.left)) :
    M ≠ tblOfList [6,3,3,8,15,10,16,1] ∧ reindex23 M ≠ tblOfList [6,3,3,8,15,10,16,1] := by
  refine ⟨fun heq => h (by rw [heq]; rfl), fun heq => h ?_⟩
  have h10 := congrFun (congrFun heq 1) 0
  have hrhs : tblOfList [6,3,3,8,15,10,16,1] 1 0 = some (some 0, Stmt.write 1 Dir.left) := rfl
  rw [hrhs] at h10
  simp only [reindex23, swap23_1] at h10
  cases hM : M 1 0 with
  | none => simp [hM] at h10
  | some p =>
    rcases p with ⟨s, z⟩
    cases s with
    | none => simp [hM] at h10
    | some s =>
      simp only [hM, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h10
      rcases h10 with ⟨hs, hz⟩
      have hs0 : s = 0 := by revert hs; fin_cases s <;> decide
      subst hs0; subst hz; rfl

private theorem mk_base_hm_hv {M : Machine4}
    (hFirst : M 0 0 = some (some 1, Stmt.write 1 Dir.right)) :
    Matches M baseTable ∧ HistValid M [h1, h0] := by
  have hm0 : Matches M baseTable := by
    intro q a m hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact hFirst
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := by
    rw [Machine.multiStep_one]
    exact step_move hm0 startPos ⟨1, 1, false⟩ rfl
  refine ⟨hm0, ?_⟩
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl
  · exact ⟨by decide, hrun1⟩
  · exact ⟨by decide, rfl⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨0, 0, false⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, false⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, true⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, false⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1162218284650688, 1162218284650688, 1161359425540288, 1161221986717888, 1161221986717888, 1161359425540288, 
    1161359425540288, 1128650902669377, 1128650902669377, 1128650902669377, 1128650902669377, 1128650902669377, 
    1161292860035264, 1161361575121088, 1128650902669377, 1161368023863744, 1143784436142784, 1143646997320384, 
    1143646997320384, 1143784436142784, 1143784436142784, 1128184898717761, 1128665935054913, 1128184898717761, 
    1128184898717761, 1128184898717761, 1128184898717761, 1128184898717761, 1128184898717761, 1128184898717761, 
    1128184898717761, 1128665935054913, 1128184898717761, 1128184898717761, 1128184898717761, 1128184898717761, 
    1128665935054913, 1134782236919873, 1128391273353920, 1134988343120832, 1130590296609472, 2923103628717052382937775513005439984455848630850, 
    1130590296609472, 1128184898717761, 1128665935054913, 1128184898717761, 2923728051605758559929334276757643509464395952962, 1134782236919873, 
    1161187628746817, 1128185100044353, 1161363586158784, 105639286212673, 1130849991004352, 1130849991004352, 
    1130849991004352, 1130865023389888, 1130865023389888, 2923192831697908886674815267011186569844562596674, 79268187015233, 88064280037441, 
    1161157566337216, 1161221986717888, 1161221986717888, 1161359425540288, 1161359425540288, 106105088837697, 
    106105088837697, 106105088837697, 106105088837697, 106105088837697, 1161155420950720, 1161224136298688, 
    1161361575121088, 123695392443150858820591777138241287708825726074733356504626524195064473634394268577294083227923073218533723088961746289330626501757291695701286401593906351367146623914162247, 106105088837697, 176478262204609, 90575098211533486263658875835525405515358351472487469792651516296289590232579100934942599969632568283198045465077605830062341624718609275858506052794192554468313079524934, 996326080379589994933119520496743091780632193719475123663182334198861550534239569946444288701343641990105059288028069548690203341894586471298313726532562400440301548252742, 
    996326080379589994946213082928518195671226700079501682212343895443687410653028751724423254853736349715181338242544107204094981917810529656369385040256671782517122620501574, 106105088837697, 106105088837697, 1161164019274176, 1161234884202944, 1161234884202944, 
    1161368023863744, 315644150232281319585688704440047274065724013520332675535085965997850670123086943329007405005672771716, 106105088837697, 188397414118873100197553748895780383986991256386, 513258889805605223322046716863513927553819518280132834263281228172320860999911596063740260963625352875095824763134914377741866617114409547089353692289987584628235068979270, 996326080379589994946213082928518195671226700243443580738849358166764116412959026040972814590148060441793607815440897892094600917346023932979611893342875396401053266259526, 
    33283751113574826881503524441640741768576169950950972639539258418565105856761192235198831410344587396, 106105088837697, 106105088837697, 1161157566337216, 1161226285879488, 1161226285879488, 
    1161226285879488, 1161363724701888, 123695392498937389873713026031008379330873147588545895400391457557604110633460828093831015139243145793763408518099314117208101559145445604203144583998661393877280829614632518, 106105088837697, 106105088837697, 960990105657226062769635081172618079611504952060852645863230911642428452751397879683873220130559456907866490428904379317648157635879586238909394047167586864342476995411672461361448301686504701911649763469843899544976159534999512425332082780975633555593363457496956553, 
    3957316615499431320073279171356055356640806738310767369103099384446583731722692406816474953440271611483648845082893338714131617477384177224370051912442134216524142926776938055, 30946491887137527512635394397712577111473074304103548947696709224767658918871193176911689626346964846920216999509526631456566954319190070711612740200181544283574470532443718, 106105088837697, 106105088837697, 1161157566337216, 1161226285879488, 
    1161226285879488, 1161226285879488, 1161363724701888, 315644150232281319585688704314262946501856155622764999339044754014754774866838305152974215541193719940, 92779092257213226545578303205766881518739472876252974769390464281075765781395168786082674482541344247867599410983594215192131751852105624239955368227590427282549589180460614, 106105088837697, 
    106105088837697, 271725294602967471171253495722962312279370570131803326628008940989019454074612551576159206000636453783149834841471288035893460953275693217190243603702515851463238383480390, 961842399437839889284103792053779316418144121300324526075100356006171277760259907745812225731337023463209014380993258277996721322364797791244751441692418865127267592749633778063342900308201234248835943932972174217609624296591492558636969619703306718336253992246956552, 996326080379589994946213082928518195671226700158828398485643417724627314700239057465505778076212840529566937250655311516815746776064003636950500376106014795642844413603398, 33283751113574826881503524289022424008528992618783719834858524410198564458202100755346952774217908356, 106105088837697, 
    176478262204609, 106105088837697, 1161234884202944, 1161234884202944, 106107236321345, 1161221986717888, 
    1161221986717888, 106112068159553, 996326080379589994946213082928518195671226700158828416733697537429820499893377464952279651801182834835163047546087203246882595951977229169225299658196849499922083123211846, 1147976328483520, 1143646997320384, 1143646997320384, 
    1143784436142784, 1128253834531520, 1128253834531520, 1147976328483520, 1143646997320384, 1143646997320384, 
    1143784436142784, 1143784436142784, 105639084886081, 105639084886081, 105707804362817, 105639084886081, 
    105639084886081, 106120121223233, 105639084886081, 105639084886081, 105639084886081, 105639084886081, 
    105639084886081, 105639084886081, 105639084886081, 105639084886081, 106120121223233, 105639084886081, 
    105639084886081, 105639084886081, 105639084886081, 106120121223233, 176145402239169, 1147976328483520, 
    1143646997320384, 1143646997320384, 1143784436142784, 1128185119183552, 1128253834531520, 1128253834531520, 
    1128391273353920, 1136981212206016, 1139248950809536, 1134988343120832, 1130384142439104, 1130452857787072, 
    1130590296609472, 1130384142439104, 1130452857787072, 1130590296609472, 2923192852775435601243924277142057057921917850434, 1143646997320384, 
    1143646997320384, 105639084886081, 105639084886081, 105639084886081, 105639084886081, 106120121223233, 
    105639084886081, 105639084886081, 105639084886081, 105639084886081, 123695392498937389873713026031008379330873147599292021254716145819189694294113370892891617908248666722941868301592323487903906592442059199090883659927010629186415777931374150, 105639084886081, 
    105639084886081, 49893186923645615822906216981397004028374829219736362062085763478657007460236387236461919470222713540, 316745585854529, 1161230442172608, 176076613619904, 176076613619904, 
    1161359425540288, 1161361575121088, 1161368023863744, 1161363724701888, 1161363724701888, 2924441678176966633867303379489457218622389785410, 
    2930150663503272602656521107953261480259629388610, 105639286212673, 105639286212673, 51381112945374834761192540617938412326780670786, 105639286212673, 2925868931314211233750039684930286717407825302338, 
    2923059026700301817224644585331632889757373110082, 2923728051608375487825929132855121896340814123842, 2923103628360840061931396888499865490196269177666, 2923192831681916551344901494836330691074061308738, 105639286212673, 105639286212673, 
    176076613619904, 2928712635670479399483352131567433629247236739906, 565252326492225, 72671117248577, 72671117248577, 1461596415848995981871032070828548605059021151042, 
    72671117248577, 176473898094784, 176476045578432, 176488930480320, 176488930480320, 97053213352571288021877315120692359634201088834, 
    283777349781569, 33283751113574826881503524498662970085759807968101034111121810745119851012841042868601256650153881732, 583933376907551283496523466295691399312212449876432247584513562488549585930299222531723288864935749, 33283751113574826881503524289022424008528992619056471116423766856593064236336656465239706865408163972, 72671117248577, 72671117248577, 
    72671117248577, 72671117248577, 1461596415859629846402130605115119909435766479682, 72671117248577]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, false⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, true⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, false⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, true⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, false⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [581659384877760, 581659384877760, 581110165934784, 581110165934784, 1128253618194497, 1128665935054913, 
    1128665935054913, 360713906557120, 290547021648064, 290547021648064, 564067198833344, 581659384877760, 
    146252780278464, 146252780278464, 291388315145152, 563517979890368, 563517979890368, 581110165934784, 
    145703561335488, 145703561335488, 290839096202176, 1128184898717761, 1128253618194497, 1128665935054913, 
    290555619971520, 290555619971520, 290555619971520, 290839096202176]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161155213136064, 1161155213136064, 1130850393657536, 1130850393657536, 1130850393657536, 316730754998593, 
    1130850393657536, 1130850393657536, 1128665935258433, 1133048951410880, 1130849991004352, 1130849991004352, 
    1162186007519553, 1161155213136064, 1161155213136064, 1130849923895488, 1130849923895488, 1130849923895488, 
    1135265169413056, 317211791335745, 317211791335745, 1128655266975936, 1161226147074240, 1128655266975936, 
    1128655334084800, 28545062747135879611981261830047916220198430531, 531567574968091860714533399135376918339997661924541019674117510384365364133959247851279918596547944709, 531566814648499095465420701781988736595641843044821287822516628326810816182114398730380326603230026309, 531566814648499095465420701781988736595641843044821287822516628326810816182114398730380326603230026309, 1134784602837952, 
    1135263489463232, 300169428214081, 316936913428801, 2923048573263167642360227223487895748593718404931, 1128260532637888, 1128260532637888, 
    531566925528426725179185920008209103178318478741675602874657015773459190990796046109048847669484842245, 1128329252114624, 531566909688434973202219461557242787687172698874170557935882800277009552915750199992038822820593639685, 531566909688434973202219461557252614587781686025470080892501606030944956469237596925188191146167443717, 1130384389705920, 1130865426043072, 
    1130865426043072, 1130384389705920, 1130865426043072, 1130865426043072, 1130384389705920, 2923728051608344334045009583117213363704120234818, 
    1135263489463232, 2923728073386415816985071244773188239337285768002, 794795350131107216651266565750479472874606026378291508152101953328944784947054013552650451611032133, 316730754998593, 1128322339901632, 531567574968091860714533399350101250042629270675420179531867449285253672062817069944619042340714030981, 
    565716990365888, 1130865023389888, 1130865023389888, 581110166196928, 581110166196928, 1134988328444737, 
    284791230702401, 290547021385920, 290547021385920, 565716990365888, 1130383919943872, 1130383919943872, 
    1130865426043072, 1130865426043072, 567916009492672, 567916009492672, 1130383919943872, 1130383919943872, 
    1130383919943872, 1130865426043072, 1130865426043072, 567916009492672, 567916009492672, 1130383919943872, 
    1130383919943872, 1130383919943872, 563517962850496, 563517962850496, 2923103649793976862218096171306685863984187315010, 581110166196928, 
    290839096202176, 24263303375345770896986316015129411222748800835, 275742584636184205613406846034137913783194350178934808980844662576456463492384977937197697392998981, 1128391258678081, 1128665935258433, 494660804241896241172350407130366198807300135516730496499336552710643233838780815666659548674794953127261701276425510203606449996155290121596743439904417874637138464651790919, 
    1134781968687937, 531566814648499095465418945014108932579159164373903206171963734832622162826772809524370449743269241029, 291388300469057, 1134781968687937, 1134988328444737, 513258889803854699919224884912180393193610003644175699051626634350090433525623781843474305260102692833725396076192513019967347631296573566286687020510030334223086119733831, 
    291388300469057, 1464361709306320934963368874146888773213339329347, 531502440922007731439362805349204800220111663201298714905114586039107019415045319257765639161909625540, 1134781968687937, 290555619971520, 290555619971520, 
    290555619971520, 290839096202176]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [105624522197057, 1161226151530688, 316936913428801, 106105088837697, 317211321573697, 317211791335745, 
    159451353191104, 581110165934784, 572314072912832, 581110165934784, 736462602516499213080195151913596401921747358530, 581659384877760, 
    581659384877760, 581110165934784, 581110165934784, 79457985762240, 79457985762240, 290564218295232, 
    106120121223233, 106120121223233, 532021042251963798731965620738255825052933231100913922460738971489517686740326361572558854738082546564, 564720867784877012998555968431296901372581001159985163451773454085468456024885130562598110765965919108, 33218934237609691583668613689565492339516550384879083642386580358529374957665948028891745604532228357, 18160212513472, 
    354116836790464, 354116836790464, 283954251043008, 1461551814220297022957588449697953938337899284291, 146235180978368, 146235180978368, 
    360713906557120, 290547021648064, 290547021648064, 1464361729701995221157789699309467283913485390658, 1464361729701995221157789699309467283913485390658, 564067198833344, 
    159446517158592, 564067198833344, 564067198833344, 581659384877760, 146252377625280, 581659384877760, 
    291388315145152, 563517979890368, 563517979890368, 563517979890368, 581110165934784, 581110165934784, 
    290839096202176, 105639084886081, 105707804362817, 106120121223233, 535654799719835974809215259227172449821233679073785839725814537201633001844478443033808768575106990980, 3965015557583982423210411951551003875558362109770769960731021193173264684250448327117364812627585909760122287926861108762682700131797655803188129827033392869388816682412105286, 
    183045214891533273169480434135240809249369039683, 290839096202176, 290555619971520, 290555619971520, 354123285533120, 354123285533120, 
    290343012798656, 290343012798656, 369516448321984, 11440630863596311125393325258501935482577883714, 91366501655132336094549906607691565591341044546, 290555619971520, 
    564067198833344, 581659384877760, 354123285533120, 283958550204864, 354123285533120, 283958550204864, 
    847200578180032, 1461551814220317792224250751522732397916760115011, 146239480139968, 146239480139968, 360720355299776, 290555619971520, 
    360720355299776, 290555619971520]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161223999721664, 1161223999721664, 176474300747968, 176474300747968, 2928712635670479399483487531775739301778671276866, 387108089112897, 
    176474300747968, 176474300747968, 531501949882260587742187830062414698959871411178907549532385743774434787400884770463977069734789423493, 176473830985920, 176473830985920, 317211791335745, 
    2928723437625836206828661337346230193136414507587, 1161157427728576, 1161226147205312, 1161226147205312, 1161226147205312, 176476045578432, 
    176476045578432, 176476045578432, 16674316169753703049456973052159692846972879344314065496498823346327746508403284215685671574029906629, 106109453144256, 176476045578432, 194641827349582167937822535207896829731286410724276174072915146918076379398640739720950428249068677, 
    194641827349460347516036140984851240202421779949205371133701919113346631041889312156360769311577221, 188398111022467325020803783223353612469522154051, 1161234884202944, 1161234884202944, 531566909688435445270766647306599960300812085340397854899768740023933445296751185224118506156267121221, 531826329162053553315165129197468780527532868576765067630728426049125342907269368677077696553064311365, 
    106191460044992, 2928713681049811849681036917535521245733725422147, 2928713681049811849681036917535521245733725422147, 11441676211027492211214883842859275298204041795, 66502657011482485683975418660535663683493140541512266197393429665551231760379979799990423058212956741, 387374377085249, 
    387099499178305, 316936913428801, 106191460044992, 176008296796352, 176489333133504, 2928713768122220799590905130185202007702459400771, 
    176489333133504, 176008296796352, 176489333133504, 2928713681009934867830658483561302505169797268035, 176489333133504, 97064015254883712830528379875874712688498053954, 
    1161226084225216, 106107238420672, 1161226285748416, 1161226285748416, 736461225021556852340425886462068721602793577282, 531570869686402707761685416603420552789875510672134056138890254989290451153210782960536848898386220933, 
    531570869687339291746654147297259676408698011019253240184879360078160204937694825583285702377858848645, 531505989080216822504544562357606592115969372888303575522164052474287359415636455443273412827559155589, 1128309922992320, 1135113162068416, 2923728051603682931639956306296919650334832333634, 1130440228868288, 
    1130440228868288, 531570869686402707761685416603420552789875510672134056138890254989290451153210782960536848898386220933, 1130440228868288, 1135113162068416, 1161226084225216, 106107238420672, 
    2928713681017920316200195249965283578443787682627, 317218233786689, 176485040402881, 317218233786689, 317218233786689, 1161226147205312, 
    1161226147205312, 176476045578432, 531501949882260587742187830250252627534123313290520250389698900651112097731945054691486857074338734469, 531503961561272569453176849296600449553407749980215696019373356001629649039305350429159374259900167621, 1161226147205312, 1161226147205312, 
    176476045578432, 1161226285748416, 736461225021558150419592299215655364399091159874, 913583824049833597744960904047466594291126219279848021177616615091961792534202176697279498445727389573, 4217239420481885636211905528504706373481450877615487711356448544200414901534734349183358764247695492, 581395120223413659886870286864224289706534368493510732575586968646840280950643763726017139457468416132, 
    1128309922992320, 1135113162068416, 387108089112897, 316943355879745, 387108089112897, 316943355879745, 
    1130440228868288, 1130440228868288, 1161230442172608, 1161230442172608, 387108089112897, 2923059026705577860035993389379773591928667391811, 
    2923036725960379045539581087516726097270450176579, 290280733413568, 28545062744819344518725395727102842299561808706, 28545062755111126011002843102967246484179797827, 17127081213463163188300992345426861088336527939, 194641827349460347516036140984851240202468760084615670170484725776112606321775166234804832251647109, 
    290280733413568, 290280733413568, 105707806462144, 105707806462144, 105776593178816, 28545062745826614654543029232837489191295128386, 
    105639086985408, 105707873702080, 106189312561344, 88528943911104, 105707806462144, 176076613619904, 
    176076613619904, 176488930480320, 176076613619904, 176076613619904, 176488930480320, 299635189224128, 
    299635189224128, 284242026435264, 290564218295232, 730798207961675627337607787192139971889641572163, 730778694777745561334076002866873053985015599682, 565716988727488, 
    1464361729701974451891127397484692202047229989698, 1464361729701974451891127397484692202047229989698, 567916014080192, 567916014080192, 581110166196928, 581110166196928, 
    730778694809626588843191397572614116631780540995, 863134346928961, 300184393491265, 161645995504577, 300184393491265, 581659370218305, 
    581659370218305, 1143578061710145, 1154573446425409, 1143784421466945, 830569081465494324235659410972036305767317320715633077299430481097281786347336683455359527211440297861, 4152422219672461384471280166053395763395061385806633017960438100971533611579564929654828621615088516, 
    4249743129117221364078374533308045464327129430935861725777469754760466304662076933127327270353524613, 564720867784877012998555968431296901372581001159985163451773454085468475277328890482360673887077024644, 2076195269844596962911890946643072449601311215635376849574122079255351821539917221265510242929882628, 564720867784877012998555968431296901372581001159985163451773454085468475277328890482360673887077024644, 616365761107369935875276490466496853443364381645574111911633086191001298933290101796430467974059909, 581659370218305, 
    1128184898921281, 3957286424721394490114101738518282362886921201196299553201562905280450810657515740549079966798692764162922757159122101148760297488599953218604748133382347946997899749722705479, 3957286659672668496337989637600028909787294103027356811861162672253209267508687166180195617051010144819530808975358738149843456798279515958469346339026478223724564940902911559, 1136981260380993, 1134988328444737, 1136981260380993, 
    1136981260380993, 531567321528221940808921109181222713137757811364297980594643159978147318175541457877436991737884720517, 22881958582964738358842411450472348493912524611, 284791230702401, 144053809460161, 284791230702401, 
    1128184898921281, 290547021648064, 290547021648064, 18160195473600, 551485156945714612346271653900167931923794792963912399726678340277892810707364535652063001792758468, 23549675405742972881518131472947460019920626499, 
    158897683960000, 158897683960000, 18160195473600, 105707806462144, 105707806462144, 106189312561344, 
    80007754748864, 88528943911104, 176007827034304, 176076613619904, 176076613619904, 176489333133504, 
    176489333133504, 158897683960000, 158897683960000, 176076613619904, 176076613619904, 176076613619904, 
    176007827034304, 176076613619904, 176076613619904, 176489333133504, 176489333133504, 158897683960000, 
    158897683960000, 176145270247616, 176076613619904, 176076613619904, 176076613619904, 176076613619904, 
    286441049690816, 286441049690816, 286441049690816, 286441049690816, 3965015557583982423210411951551003875558362109944019509041653996947765856354101691510085722095635277211358800638834888165820845461381827266788346797746215999017726515454369351, 282043003179712, 
    290839096202176, 290839096202176, 97064015254883712830221311546324348197566157634, 299635189224128, 284242026435264, 368231320314093308013187036825078897603753612098, 
    286441049690816, 286441049690816, 282043003179712, 290839096202176, 308431282246592, 176076613619904, 
    176076613619904, 18160195473600, 18160195473600, 563517963374784, 563517963374784, 563517963374784, 
    565716988727488, 1464361729701995221157789699309470661626090820418, 494660810374815527393634228433672799510426386911147855795382443246755255418035739300749860498064824530080026711131690642690439663831144486552856469863088204487509116225629766, 567916014080192, 265751470930873414351167253733339532646648254310819408008978200344445803270900394969617927887542042756, 567916014080192, 
    563517963374784, 265864505112980430064054651196173104792529041277022130300530685823542496871090893010757219391945687172, 581110166196928, 66437760565274650815393729049215226922465765636340765606658184082304408279524570091370759689827819909, 265783407325208761503692730946094334871500034189964688377712750467639293199055656237129324008665565701, 1464361710667450402964035378057445116266693083971, 
    531501949882260587756833167802570655661729585301604032896135132833126849084466260000481359766468469125, 1136981260380993, 1136981260380993, 72852317671872, 283958550204864, 531501949882260587742189368830738681766497685397094971057175438684888048951616581383737290994751938949, 
    1128185167358785, 1128391258678081, 1128185167358785, 1154573446425409, 1152580514489153, 291388300469057, 
    265783407325208909025111734337395657818138524017505032669723278016951772654539461688596411280733293061, 129777061125114666772444043603941826967452216841934935959646736138634724465661388102913095270441349, 188398091998576775301587150664493928186961248835, 265783407325208761503692730946094334871499974606538059511953937495106877595034597140552253510212962821, 1136981260380993, 1134988328444737, 
    291388300469057, 1464361710667450402647122728000387765892517282627, 1136981260380993, 79449387438528, 290555619971520, 290555619971520, 
    79449387438528, 290555619971520, 290839096202176, 129777061125114688385544090139422961131954691772945946369347430163358179898092070109933362506670469]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 0) (a := 1) (rem' := 105) (cur' := ⟨2, 128, ⟨0, [], 1, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b1_0
  · exact tv_b1_1
  · exact tv_b1_2
  · exact tv_b1_3
  · exact tv_b1_4
  · exact tv_b1_5
  · exact tv_b1_6
  · exact tv_b1_7
  · exact tv_b1_8
  · exact tv_b1_9
  · exact tv_b1_10
  · exact tv_b1_11

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨0, 1, false⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, false⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, true⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, false⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1162218288844992, 1161368023863744, 1161359433929152, 1161368023863744, 1161368023863744, 1128184898717761, 
    1128184898717761, 1128184898717761, 1134782236919873, 1128184898717761, 1128184898717761, 2923728051605758559929334276757643509464395952962, 
    1134782236919873, 1130521495148737, 1161359433929152, 1128184898717761, 1128184898717761, 1130521495148737, 
    1161567746331072, 2923192831701854956069828851223165909485802828610, 1161368023863744, 1161361581412800, 1161359433929152, 1161363728896448, 
    1152580520776640, 1134988334732224, 28545062749796141052404049172839978084073493314, 371085815683512892761663113785397083557700064066, 1128391264965568, 1134988334732224, 
    1130590288221120, 0, 532475143136476034682091077449233593412869620005009072438221334007730491800481848812872401524132181125, 1461551814188457737164009853868230242900040062786, 531566893848442985190985249522199105822813568075341756756410668758397244700911634967345250972221338757, 1128650902669377, 
    1128653050153025, 1128653050153025, 2923728051645554914121068579668246994825835983682, 960962161246946106553613076086465357131036759660803363331028550136622751973873839949714083699625142260122285134979453199878756407568506525751747395987767421232175962233671343587496824696231790638523008917484602459398108449929247573600068349380187907831645184499554313, 182711399388994469185623956647917522934328005186, 730778694777807788003844806864852698386281861698, 
    1461685619180706335815364995428042193136366195522, 1461507212527919533022076455774187177650054828610, 1128650902669377, 1128653050153025, 1128653050153025, 1128650902669377, 
    1128653050153025, 1128650902669377, 1128653050153025, 1128653050153025, 1128665935054913, 531502947801800442927268112574106554765563024389499914220724115473771179463628086895855583082361949829, 
    532475254015451974217798680216874913809582043784759478467505259314638549496020801393414608256211907717, 1161187628746817, 1128185100044353, 1161363590353088, 105639286212673, 4217239420481885636210232910575905170131155133257385298410841763908885746709091950686474488267423876, 
    1130849995198656, 960962621259340297160237214365777891717823722704926564183036830625967204577774570381472448983296891367838364334089242133432813258495900773360678187203359897699384377212925242438340283139698190255741390354758687864485121268592656535515274456990729511404306441249877513, 1130849995198656, 2923192831697908886674815304790262547989800162114, 79268187015233, 88064280037441, 
    72671117248577, 1161234884202944, 105639084886081, 105639084886081, 1161501172175296, 105707804362817, 
    531566814649450785657874923859239530147417212175932137192867954720507871274989159351168379776087113860, 1161368023863744, 1161361581412800, 1161368023863744, 1161363728896448, 1152580520776640, 
    1143784427754432, 1134988334732224, 105639084886081, 105639084886081, 105639084886081, 1152580520776640, 
    1128391264965568, 1134988334732224, 1130590288221120, 105639084886081, 105639084886081, 30195301736472391287196081120801443646156085058, 
    315683686851694254074744945814974539430333763952391537188801836021867973491092901266803384498698174596, 265871601429285315743838129785401450789746865156878494670530786089685978537051426205107963566764179588, 1461551814188457737164048539642320094001606268738, 24263303513663245531547580060276979485565294402, 315618806244994758245201884414474607739653996945947310482339672651678242581382163279000254584289345668, 23014462463110264477498506763757886104766814018, 
    24307905004060306777830651496822276208577255234, 551485154891272322737425054725652954449109543248202756215848172856478848626210119674864478472139909, 106105088837697, 532215612793549360890572975897818411474821744694817750350284335985236788138267684338715710615235097733, 106105088837697, 106105088837697, 
    106105088837697, 106105088837697, 176478262204609, 188397414118873100197553748895780383986991256386, 106105088837697, 265751470930873414351164612517385363006526932848833352699993503936025169955921796374149913246871863428, 
    243435318459281101955884183820061200465616851474123496610325489776771565493717089432877368014337269893398361380223867357606548872831624865727935408758339651246816572386886, 968021362195185393955541101495028777103712441320427193813939515089859961385475162891900479937982250157392375683657837093797066113693603705474201267525171394414719754481222, 265750967022100742192852272687657642285675031833739272164551234581456532686019287313506943848749348356, 265750967022100712688568472009397377696347321951545877532997366477087553674118314403898112294645282308, 60383859499976435730403761470995364169612090338329641679981479879968377396599368043751888711380204380392985356984737324240556876816235350051317340344719168356700306583110, 966134841668032944412957968563988154325480438945343854099673859027366197817049018833234425556091877858065361851484401504515447359956175597260687796910455834134424558153286, 
    1461551814199091601695146771697434242921244202818, 33218933866359176793896429000030302162540211265592764255553101123654622642221373355633629364103889028, 1461551814199091601695146771697434242921244202818, 1464361710646224212118018748175097492209259320130, 33265503442351452126331306229090706639815515675445730576512081064714911858832635625702179921282416772, 1464361710646224212118018748175097492209259320130, 
    483126158568163769936501183021458442214978864003385233287427045967609357358697082995825063905635277027025539003036140677226989204883607484234060645099444991819360497514566, 7729134014253641377469069931430460801357106564174282698180304698507398390950695855234361168600494459521130675772798662716340151125115898905320411904846327609700017466456134, 1461685619180706335815403681202132044237932401474, 961431374112543373399802241676619621526755095224203917564019382330997668318913802368541227380713093534363923595529660516887058331628859746694685748028881437438963899961549286524892966014367282331035723849744925578071923792388653269399992298138906893897203720246956552, 1461685619180706335815403681202132044237932401474, 483185357100068365494086066509854758621066598132873743333501577308872303428656333094588653105998800873741776117627680836949308397851406203941537768769378434836886587616839, 
    106105088837697, 106105088837697, 106105088837697, 106105088837697, 106105088837697, 176478262204609, 
    106105088837697, 106105088837697, 106105088837697, 106105088837697, 106120121223233, 265750967022100712688568472009397377696835429382489545829193237462636181814634433563259635618368075268, 
    1461551814199091601695146771697434242921244202818, 1464361710646224212118018748175097492209259320130, 1461685619180706274968174870247120772396178543426, 176076617814208, 1161368023863744, 1161361581412800, 
    1161368023863744, 1161363728896448, 2924441675454707698499795520666156446587293848386, 2930150668947790473391536372250951286586970526530, 2929437042379178558083499521559229679564633461570, 105639286212673, 
    105639286212673, 105639286212673, 2925868923147434427647516108460384401302537458498, 2923059026700301817224644131982721152014522341186, 2923728051608375487825928679506210158597963338562, 2923192831681916551344901041487418953331210539842, 
    105639286212673, 105639286212673, 176076617814208, 2928712635670479399483352169346509607392474305346, 565252326492225, 72671117248577, 
    72671117248577, 72671117248577, 97053213352571288021877352899768337779438654274, 283777349781569, 33218933866359176793896429000030302162540211271412168552074016993561849657143123079468080075535499396, 33330384048567549770084055013415606785296572831131718200920138323459738797924972306243578106104725636, 
    736462597050775921082969575171684009976866575170, 72671117248577, 72671117248577, 72671117248577, 72671117248577]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, false⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1128653050220736, 1135263212508096, 1128653050220736, 1135263212508096, 1130383991247040, 1161224003915968, 
    1161224003915968, 1161224003915968, 176473902289088, 3969876362449279587023773784201311402369501389713847401676384797769533677602154454237057162814751608845230593972819504591941710474419655384267326079615695722629895083247268422, 3969876362218935200743158856010803934634109105350022081620174449512728949210889883916176840023130312133685581996091875929538725339482789862424418527173649517922794999480578630, 1161368023732672, 
    176476049772736, 106107236389056, 106107236389056, 176076617814208, 176076617814208, 176076617814208]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, true⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1162218219638976, 1162188362486208, 3957286427485527111805477507569384677388174872222237410024406292647907900443146743993405640663897620220073825072464373454032373082400979230717181442025676032411935522854755910, 1161161867661760, 1130856593101760, 1161234884202944, 
    1128657613640385, 291388038583232, 286989992072128, 2923036725907292758956389560910397270399058457410, 1130521495214273, 80268920754624, 
    12993372403592331447569820076407047088587792363790735895221254607475192483360961638661980320815642249303881098552780318792508246499268354499863948046455487517824257065642233648397056181274535156756564893856318414024869468271382605914745952455080433022767682281056272633665843284915037072392165276646605109014147792982468300268452679753742189378642234704382106507242033437258, 284790968816576, 291388038583232, 291388038583232, 291388038583232, 568464985691072, 
    1128253618262209, 1134850956464321, 92771453962089640475985543543959562145872491330, 1128185037263040, 1130383991247040, 1128185037263040, 
    1130383991247040, 1161361512140992, 3957286482768179819956743135435490142320236426393206203005979382968247650497248826284140458187723898373244746626373010450178397345030322089894618712352107334879571705969211974, 1128651041214656, 1128653050220736, 1135250327605696, 
    5097036280423969610201709399962407920194101339788260799209709442026457053222829840227101965451515868807853500053614401318439558085539394673225519690745432103883396511122500590658546805345835940829058537491604771177320227952665842325201410070567692340831400261178086946523621832517094839287826584650812746102909956397309303374751235380244970563756950070915615882392395383313196619, 2923059026737561721892799147367000187441815490371, 1130849995198656, 1135250327605696, 79336906559681, 106107236389057, 
    1161168314372544, 2923192831687194541275072571900340981922369917762, 97053213341856942701362782524111109305552360258, 300184131605440, 286989992072128, 581659125093312, 
    17127037689224021982697993882382837718703952706, 176007896240321, 284778083520960, 730932012943292308569259329476995080233949352770, 284790968816576, 291388038583232, 
    246514146482369, 176145335193793, 188397414114877470853535339535104718619711394626, 105707804430528, 1161361789227456, 469678024263002803969059354250323281735195029067236688987664472590475199230583221470803247223486634092478792402831130654558931494702556178397237330764484168658154560104375812904345254266868362940875142492084193595269817461386899830446297987075292721577992246988552, 
    7092060380424047868404154416372824444409726272950638568475071432799406037037550152021456712531181827839551431686547651439636744800763451056819411806580810998347610983812266567, 176076617814208, 106107236389056, 28545062745224465645369903110165791312823979843, 317213676540352, 283846069326017, 
    123695392436852379508231302202309582380611299138249354451941716835427149370432261510863739071184262518860493724989703396936371459049139197359354396089814538793296204924924486, 1978643270868171354322361283930174228601284962845105804639348381733724010968143266958989667586136805319989612453004291435201554674975673361423606726905498467825742565330614854]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1135263212508096, 176076617814208]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, true⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161221994844608, 1128253618262209, 1128253618262209, 1161221994844608, 1161226289811904, 1161226289811904, 
    1161230584779200, 1161234879746496, 1134850895647680, 1128253618262209, 1128253618262209, 1128253618262209, 
    1134850956464321, 1128253825881024, 1134850895647680, 1134850895647680, 1134850895647680, 1128253618262209, 
    1128253618262209, 1128253618262209, 1128253618262209, 1128253618262209, 1134850956464321, 1134850956464321, 
    1161359433929152, 1128322471958721, 1128322471958721, 1130521495214273, 1161368023863744, 1161359433929152, 
    33283751484824631724445051627210082194809946813980746898519477829269031640047025888964423347658088900, 371085815683512892761663113785397083559847547714, 317209381966272, 317213676933568, 317209381966272, 317211529449920, 
    317209381966272, 317213676933568, 1128653050220737, 1128653050220737, 1128653050220737, 1128657613640385, 
    1128657613640385, 1128665935122625, 2923036725907251063541399658703168873825122202434, 1128665935122625, 1130854355179713, 1128653050220737, 
    1135267568309185, 1461507224778084742175861140455673045191562957378, 1461507212527919533022076455774187177647907344962, 317209381966272, 317213676933568, 317209381966272, 
    1461507223427589098458386613583099229212397081410, 1133051230951617, 1161224142328256, 1161230584779200, 1143646988669888, 1130452849136576, 
    176145335193793, 176145335193793, 105707804430529, 317211529449920, 317217971900864, 106107236389057, 
    106120121290945, 106120121290945, 176473900191937, 317213676933568, 246842711480513, 176007898337472, 
    176076617814208, 106107236257984, 123695392436852379508388424951488597190371932243698236059193498588685328018306518443888141631917266983146116073042837963539898866351765217494789343149944693126224803616733254, 123695392436852379508388424951488597190371932452147692587773842471043694693409327193109287156765831685205099948195166082646954971816042516581432055597668750585564564778072134, 317209381966272, 317213676933568, 
    259649206680927326188185176368381884021418068928640242872405190109537197128348708061024725416569029]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, false⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1128184898717761, 316730754998593, 149705518747840, 1128253618194497, 1130452775803073, 1128253618194497, 
    1130452775803073, 1128253618194497, 1161256216301760, 28545062744814772085679259178330447438583707458, 736462602484659927286886454528217304575992959810, 563534622888640, 
    581126808933056, 581126808933056, 7183239312607841750766374482127784713146958266082543664089944534876562400055352646690460001251963619416600690578432362887667815075445556022286553899669163281364672134569259590, 188398111017150027669405916961649806552260956738, 563534622888640, 844975584193022572032254998072954565079158789954, 
    565733646144192, 563534622888640, 567932669399744, 1461507234316624839928533501733352279662529680194, 28545062788424218319647242640094975333704405826, 371085815722063085269019155095449815187409867586, 
    567519937302720, 708807600902848, 7759266745884737787867324976944749980514209378719387916340366124477009657047840760964969804889525979180308937459557012811488376509000364282775949980132271366790941127995974, 371085815683523277078352415059357357718932312898, 371085815683513541484604461078992454791341299522, 371085815683523277197194658830753864109248238402, 
    371085815683515488603354051875065435376859501378, 565733646144192, 581126808933056, 567932669399744, 1461551814199091601695378885308951740738200213314, 581126808933056, 
    567932669399744, 183045216212744210328599737795323594158871949890, 1130452710854848, 732183652444147467471916537350491047862898627138, 365376805856876505348543652512910940000300847938, 548422019342044858184672169340773557859549991490, 
    366090429703239869922403946410024917357922636610, 23549676769515329767857079556025016139802243906, 365555209776780933718674877191158893668573664066, 183045911749907399204496550401769052250298151490, 1462220839091172936848157817860184486645629801282, 366090429703239869922403946410024917357922636610, 
    183045911749907399204496550401769052250298151490, 548422019342060435134668895709357402543695622722, 1161226151530688, 105830680692801, 7759266745884737787867324976944749980517070666467077457085701427852851118392282739691609808804726878792129465282199210198567801628606815797690150546984998577259126213046854, 1161432249143744, 
    2923192831719096013134373994256807618075860964162, 176076617945280, 732183652444147467471916537350491047862898627138, 3957286427485527111805477507569384677388244432552460802929910892738581610295799659392145110719306832369226979032977702619102839107473506149601343459173291316945571091251690055, 176076617945280, 730753606269255909307343381566585698401885655618, 
    730756393883673454697433746569728038524365673026, 735038153295344946545654850720057680658388062786, 960962621259340297160237214365777891717823722704926564183036830625967204577774570381472448983296891367838364334089242133432813258495900773360678187203359897699384377212925242438340283139698405936960232166237360261630916807558747101240760436257672778097885193249877513, 365733617785390696851019944090217798610005840450, 1130849925992641, 1130852207761601, 
    1130849925992641, 145720204333760, 1128653050153025, 6707465290378267800188040996305299253104276013836041762246681885221414074130258631026200768032554559002344796950434382194368757363173302624732023885784762686877725576012656367131333017091582937952485570274490407242245783128058865051780508958952263461404729989372662270095591926834682043978127293739138341988210718215821280159899633067198863444335062403851012519530581611739683402, 1135247972639041, 183045214870244774920159312189431438296834191938, 
    368944933271410546523299430241253656209246999362, 1464361718812959479687758868483785126154015413058, 145720204333760, 731110419553561907446953153934130837375913407042, 732180859406479780409008429971713247909418996290, 732180859406479780409008429971713247909418996290, 
    182710702482653691391103801502118927892735865410, 182710702482653691391103801502118927892735865410, 2923192831719176458548337942775563387488159404866, 1464361710646224212118018748175093551557437887298, 23014456840475806813029255431838236901917070146, 163449833525952, 
    581126808933056, 581126808933056, 2923192831719176454111543883894030792306185999170, 1130849925992641, 1130854355245249, 145720204333760, 
    1135263005025089, 1135247972639041, 548065208777344551960654481272888362446866092610, 149705518747840, 149636730065088, 183045216210090936512490604121723426668925686338, 
    548422019339391574247165198911752306503888933442, 158501611770048]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161155215233216, 1161155215233216, 1161292658446528, 1161292658446528, 1130849925992640, 317209643852097, 
    317209643852097, 317209643852097, 1133048953508032, 317209643852097, 317209643852097, 1161224003915968, 
    1161224003915968, 1161224003915968, 1130849995198656, 1130849995198656, 1130849995198656, 1130849995198656, 
    1130849995198656, 1128170350842560, 316934765945153, 316934765945153, 316934765945153, 531501949882260587742187610640932542974807645288718787159258359276052401589683382162037222221468536196, 
    1130850410435264, 1130850410435264, 2923103628706398111610211875378732297219236467266, 316934765945153]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161155215233216, 1130849925992640, 1161224003915968, 1130849995198656, 1130849995198656, 1130849995198656, 
    1130849995198656, 1161155422851520, 1128665935258433, 1161224146784704, 1128170350842560, 1130850410435264, 
    1135317178782656, 316943355879745, 316730754998593, 316730754998593, 1130850410435264, 1135317178782656, 
    316943355879745, 316943355879745]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1162186007519553, 1161155215233216, 1130849925992640, 1130849925992640, 1135265169413056, 317211791335745, 
    317211791335745, 317211791335745, 1161226151399616, 1130852142682304, 2928723416496430135774501206776895241258467857218, 1130852142682304, 
    1161368023863744, 1161234884202944, 1161368023863744, 6707465088723695756462041669331607964978116025472644350312872008527489413480729830512419988308139866264102676286666761550018666423864731055799429689640502814051701247239290373143927504507708192171950852658069962247565145082869537081160711912673013399816860144408012705988244565038151531621218891125366586274413564454694792398682296176605500909924042870819947976146372816011481162, 5765546543805391563381780853924709238853624682097217448921726523468025461793079394510719890329506207983260271377111842401099837013826329162216149249734838870697934150649561153814630356535787652784276409710848724886353907245471475500900463352808269735804134831032812500655887619441585648113447440476089469258687458514422704349040470191907302233501588958812997946592902300903161196928722514493756837698394298190833531335663452693804644100294543053829839362861708450471532548120642931032330832578185839676411574097595425037773466463660037352315832732027158123062609650693436073081680264634467789622894675813500232006517081906232752004865746168015056575166892979278, 2923371247867926600616147513671789334131671905090, 
    1128655336181952, 28545062747135879611981266552432413488353126211, 3957286482768179819956743135535386095930392185957388735263790078597741482313362023276041525026819706854350726151904883571767552696887348366975288748257375469730979548300795462, 1134784602837952, 1135263489463232, 498163040083692684825852622929707446383026283959372068153189136402887009246095278371583180794839436562966802500504694062888340005545539376625240932180461818802371370638918, 
    300169428214081, 316936913428801, 2923048573263167642360227228210280245861873100611, 960962154094212046835217857624440951243359382280315518482490121323070426323277455699297028984069885226678794144529785608723642152796426120844668831185037509327352773188446086011102625968962983901773993338880499978799650584871690942765673940116450413828374537246988552, 531501997402235843673078834018290835123961472008431187880139878726963244024552043015232619089636900996, 960962154094212046835217857624440951243359382280315518482490121323070426323277455699297059175538939419593693333797690981723307594003155694007602076818512820324125820110646703180740266647387479781198414869470911330768347804102530914224977349563430270301896713246988552, 
    1130865442820800, 1135263489463232, 3957318153739228932148079060346538864749506376802247475269367249545118780987149966454479051656757805495389180426890228976503108632634552257653435241740960192102002137451413063, 1130384406483648, 2923728051608344334045009583118942745961030505282, 1135263489463232, 
    2923728073386415816985071244774917621594196038466, 3957905353407350526976139120631990221013971080350490939812062224469849275693334582203039745551161875459259158922408130754688843673099772880427130004109069471874027487982739015, 316730754998593]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161294805930176, 1161226151399616, 1161226151399616, 1130852142682304, 1130852142682304, 1130852142682304, 
    1130852142682304, 1161226294268352, 28545062745807143467047121272107683336918405954, 4217239420481885636210136631897281682805133657625230862662893845621218483648979899785746140019048580, 371085815679526491324735453298479054058709586754]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [317213938819521, 1130852142682304, 960962161246946106553613076086465357131036759660803363331028550136622752105596062168272324174643017485134504712718546396182672776165498904677657589363237544916356401199219525425291049760101678965401314875898914088716951341871252039210347014497361154258519048249554312, 531502947801800442927268112574106554765563024389158977541438140010253705632169459728148631423571714308, 51381112945376274500313517365355780285050941251, 960962154094212046835217857624440951243359382280253876264893850955702859236005891397848311548779795992396783474157869387115280259616121763049322769887715023624252920582967569292670280706590847209466829945088566270357078386980932931709931271994527378070061065246991112, 
    1128170350842560, 5765546543806702476887127026601062026605812030159620377100539157072316557996865869353718756750242612998280499196503965765527403436404618376908544929450028048242747956843974717956178919156422278267492449560675789658796752808977728998210570252406826675328309438627628770529475709694893165380783294185179595984201318444706452921526469961249775982314998367068753299928443052751405426538768353505364613350919292712222075825825184311969840584046626745930359087354271284027881815528895339764729037880184333402173811706678186116750663554698544436553836074427258868073131513038242683710875097976666206804699438802683370971841663816832619515282054027692999150245504758862, 1134980030010304, 1135254899528640, 1135254899528640, 1134980030010304, 
    1134980030010304, 1135254899528640]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1128655201964224, 1161226151399616, 188398111022468298584047141096600982326068916803, 1161155422851520, 1130865165996992, 960962621259340297160237214365777891717823722704926564183036830625967204577774570381472448983296891367838364334089242133432813258495900773360678187203359897699384377212925242438340283139698193622445720953353922562986015005398446925428865531440026700331614729249877513, 
    146239410938305, 146239410938305, 146239410938305, 11260833764567861763437557153734853033907794192826732298546929741907961230004605123328973664641727499991108580225857996139622150252236501403308628750457037143179028690838037255152830044769237909524521568103801399025370937031681933697497111081678701265353030614027495393316535528674913698511923276844179637971846830992443288139421725635580111614559986572710677937362441046181061930093172384435988629171565262483725516321192957877266021710090690687593812603047808265729947446372022652367941458013021844290597801002799217984534396022805831732875770163464252495560477726099875259210060161765252856278131778248370604273235402590734085597601242021289111057321571406, 188397414116209299771323610296853618801017631298, 316939060912577, 
    2928712984111648387311812611712244798555905077827]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161161657946304, 1130856853148352, 1130856385483456, 3957286482768179819956743135435490142318804043455087200613195225556331186938021567337730073743051180760786641548782103839078459737764019706812171476754983316938681111870922311, 183045216210090936512490604121722863718972265026]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161161657946304, 1161161657946304, 1130856853148352, 1130856853148352, 1161230446629056, 1161230589235648, 
    1986402478530383591740645431997337819791171788675796430653565237023851118354980214322308842411105945809702174575946134962554092433377358682657474990143708397479193414375305798, 316943355879745, 316943355879745, 583925464646046181219545626144286278998196297855793523923241066406662934343686816847999484091973764, 4217239420481885636210136643637152243686984520854128963665930779374045935371929240087726707370639492, 316943355879745, 
    316943355879745, 25199934811928839270715624678261517534665676610, 1098268501511232091905869633526353011828144001858, 732894483252822335151386912506948860254055600962, 1466502595785871271813270028059675190130773185346, 1130856385483456, 
    1130856385483456, 368944944160415134053722878190673754241141658434, 1464361729701964067257796246574608815254128366402, 548065208777344551960654481272887799501207638594, 548422019339391574247165198911751743558230479426]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_12 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1128322341998784, 1128322341998784, 1128322409107648, 531501949882260587742187830062401799953215849079026943354492420063986475236549166128290397425645231876, 730778694777745480204437588260200400562725851714, 1130452710723776, 
    1130865027584192, 1139248946615232, 1130383922041024, 1130383922041024, 1130521365254336, 2923103628398100126009056459261574791546791798595, 
    1130383922041024, 1130864958378176, 1130383922041024, 1130383922041024, 1130521365254336, 1130452710723776, 
    1130452710723776, 1130865442820800, 1130865442820800, 2923103628706418556357082578737498593367177597506, 1130452710723776, 1130865027584192, 
    1139248946615232, 1139248946615232, 1139248946615232, 286974751809857, 1134781968814272, 1134850757497024, 
    150635309965633, 732183652444147467471916235119037833070497600066, 732183652444147467471916235119037833070497600066, 12845327246330068286464786420232794390791197250, 12845327246329986523001071699465389776035648066, 94198707078061318990342671869547179995270484802]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_13 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1136981260380993, 1134988328444737, 284791230702401, 291388300469057, 1134781968687937, 1152580514489153, 
    2924798486096674534384251172123657001624626307907, 183045216212744210328599662237171074916295905858, 548422019342044858184672018224469082326498808386, 551485154891272322737669299355073173284666149280410440930095278427231507486311991189088993968963716, 551485154891272322737669299355073173284666149280410440930095278427231507486311991189088993968963716, 23192863565144762642011961595397522946516886339, 
    23192863482566482911253564702969020551874519875, 4184799132117481470136590384804912716631711481930189956367360877061461175575155759908857578235642564, 1427258613643295182688179585388232154623775298]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_14 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1461551814199050063162363173866953964345177937730, 1130383922041024, 1130452710723776, 1130383922041024, 1130864958378176, 1130383922041024, 
    1130452710723776, 1130865165996992, 1130452853593024, 1130865442820800, 1130383922041024, 1130452710723776, 
    1130865027584192, 1139248946615232, 1134781968814272, 1130383922041024, 1130383922041024, 730753606269255909307343079333977310287884194370, 
    730756393883673454697432839871904000086563099202, 1134781968814272, 1134781968814272, 1134850757497024, 1134850900104128, 2923192852775435601243865681795213828755325719362, 
    2923728070660200336199320718810620743812372321090, 735038153295344946545654850720063873131498017346, 183045214870244774920159312189431438296834191938, 732178071813350692782958228063152817355968484162, 732178071802716868816678901079922360873725727554, 1427253147878464493681672394497185267807425090, 
    24263303375345770896986320737513908490903496515, 25690556491338218685467278954852468211901798210, 2865656668356194139858815234164401938578281282, 4184799116527889978398784983509455867973112952273844462953411369790883352524593908054419120161308804, 94198707078082088257004973694325639574131315522, 1427258613664064290894156381638016546396705346]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_15 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1128391258678081, 1128665935258433, 155048925737921, 291388300469057, 291388300469057, 1134781968687937, 
    146252832715713, 286990253958081, 1130383922176961, 2923103628398058426798542396605370472132140674883, 155048925737921, 291388300469057, 
    1134781968687937, 1134988328444737, 1136981260380993, 155048925737921, 291388300469057, 531502440922007731439362805349204800220111663201299247622464039188945310879928234391177846635449762500, 
    146252832715713, 1130590281933761, 2923192831719134916212085688697190549796929222467, 427727809426369, 1134781968687937, 183045911749907399204496625959632778168916537922, 
    183045911749907399204496625959632778168916537922, 548422019342060435134668971267510484738372563522, 365733617785390696851019944090218361562106745410, 185542907841756436101577024607429705419141944130]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b3_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩) (prev' := [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b3_9_0
  · exact tv_b3_9_1
  · exact tv_b3_9_2
  · exact tv_b3_9_3
  · exact tv_b3_9_4
  · exact tv_b3_9_5
  · exact tv_b3_9_6
  · exact tv_b3_9_7
  · exact tv_b3_9_8
  · exact tv_b3_9_9
  · exact tv_b3_9_10
  · exact tv_b3_9_11
  · exact tv_b3_9_12
  · exact tv_b3_9_13
  · exact tv_b3_9_14
  · exact tv_b3_9_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨0, 0, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨0, 0, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105639084886081, 176007829131457]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨0, 1, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨1, 0, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161226151530688, 105639084886081, 176145268152513, 149705518747840, 149705518747840, 149705518747840]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨1, 0, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [581126808933056]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨1, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨1, 1, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105707804362817]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨2, 0, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105624522197057, 1161363728896448, 188397414116205405533708373595759726027698355010, 3957316615270872440218284450964402880176463350301640623975954510969620871668465798660522435042921180529501278331389240189367591667146742056196177173991223282418501148015120966, 1161368023863744, 188397414116292376520944112429962175140002280258, 
    188397414116292376520944112429962175140002280258, 188397414116292376520944112429962175140002280258, 1134988334732224, 12131653030211263320436298952777171890153255490, 731108328850724106237889998034922089232461771586, 11774884663177739230295050772364549372388635202, 
    183045911749922965993481358757799644274104513090, 183045216212744210328599737795323594161019433538, 357510185251877869385279852002119825634636610, 1134988334732224, 2923371238321452602275315853772966510340150932290, 91701014069372659985672593271794370763135398722, 
    183045911749907389043484632389215799589958857282, 183045214851619934961511459397732112177341412162, 183045911749907389043484632389215799589958857282]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨2, 0, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [732183652444147467471916235119036144207752434242]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨2, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161368023863744, 589699837819074158287220465640199798039190773543901636070630101367690750358739775402030175611111305348, 365376805856876505348543652512911502952401752898, 365421404795155814697691768288430286136345121602, 548422019342044858184672093782909831947374047810, 371085815683523277355960470052001911043786822466, 
    176145268152513, 33218886717633724322929770282846208316896973432055939921869632362847460197118888930266014152742991364, 183045911749907399204496474843905326338122216002, 182711399295870563903854201082160823046401716802, 366090429703239869922403946410025480310023541570, 548087505611964723880507308402094395470668395074, 
    183045911749907399204496474843905326338122216002, 548422019342060435134668820151493676631519687234]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161226151530688, 316936913428801, 1161226151530688, 1161432249143744, 1161226151530688, 1161226151530688, 
    316943355879745, 316943355879745, 472395693875842482956046913392939744696981894344502252394457110387779621481057921742590850848549781636, 4217239420481885636211459010914495579850478051834331480633611333426374285526127186683842987020271748, 1161226151530688, 371085815683515488603199167106595216787909924675, 
    4217239420481885636211685893556066751628065196321258164476361138277165062869735580239512175978496132, 176076617945280, 7090248878460238971847168764376121580924161159599739832445669322451766280998293458925408810295074962702220768570014119489516125596154773376161653185522624110307880995022404166, 176076617945280, 176076617945280, 1462934471120232750540038280689557734390872773442, 
    1461551814199029293895701467060353401876803295042, 1464361729701974451891127397486994667343838253890, 730845597523764622455270188121439019564347200066, 732183652444147467471916235119036144207752434242, 2930150668947790473391536228513381033966198375235, 2929437042379178558083499377821659426943861310275, 
    2924441675454707698499795376928586193966521697091, 1461551814199050063162363768885131861455664125762, 1464361729701995221157789699311773126922699084610, 1461685619180664797282620678389829662772352324418, 1461507212538511818455611465716899261016768058178, 1464361718812959479687758868483785689106116318018, 
    176076617945280, 176076617945280, 176076617945280, 730753606269255909307343381566585698404033139266, 1461551814199050063162363768885131861455664125762, 1464361729701995221157789699311773126922699084610, 
    1461685619180664797282620678389829662772352324418, 730756393883673454697433746569728038526513156674, 735038153295344946545654850720057680660535546434, 2923059026700301817224643988245150899393750189891, 2925868923147434427647515964722814148681765307203, 2923728051608375487825928535768639905977191187267, 
    2923192831681916551344900897749848700710438393667]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_12 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨3, 0, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [16609689126196325622104005442823024946530596308274601818506553493546011761593282162978424220278950788, 567932669399744, 567932669399744, 737889850177365887167944742268554793740593566530, 581126808933056, 581126808933056, 
    581126808933056, 730753606269255909148887056536904664937169720130, 960962621259340297160237214365777891717823722704926564183036830625967204577774570381472448983296891367838364334089242133432813258495900773360678187203359897699384377212925242438340283139698410144517391555203383019726431675329061162382854593963477062199017993249877513, 365733617785390696851019944090217798612153324098, 732180859406479739844188920434612216575387800386, 732180859406479739844188920434612216575387800386, 
    732180859406479739844188920434612216575387800386, 732180859406461566735859406337931064443884573506]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_13 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨3, 0, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [176473833083073, 176473833083073, 176473765974209, 188397414114877627735142496094846674943464182594, 183045214870244774920159312189431438298981675586, 365555209771786573848675774793044587099723929410, 
    365733616413939552675684987465974988855308195650, 366090429698245510329703412811835792366476728130, 366090429698245510329703412811835792366476728130, 366804056266857464934908870578668845786613159746, 368231309404081336115801779265452907725789861698, 513259132768038800474175964706704692261092562407525630748202311746230247119141891044612907742193048287433231501385123929710136643594373121026885464005511627082753788784198, 
    532345381924043839394587245521308376725660196668060491222886909406200259710064848276242323962337706116, 581395120223413659886870286864224289706534368493510796390685804915720311209218530050177253139760300164, 567519937302720, 538318444843818352625747870026928865776155664585269536744159261350800007087387631276628120358193742724, 731470020425680264485449940204603903107611513410, 11441676168658192657512816332381206285819843138, 
    145307472236736, 145307472236736, 145307472236736, 260536679351365601131353048012217414298923408451769360803044306647922988559202114043481681260458820]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_14 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [731110419553561907446952851702675933720767148610, 732180859406479780409008127740258344254272737858, 732180859406479780409008127740258344254272737858]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_15 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨3, 1, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [106107236321345, 106105088837697, 97053213332632949214742027125497506952405586754, 736462602484660089546163283741581259106104152898, 563534622888640, 581126808933056, 
    581126808933056, 97053213331469874718413267653976985831148098370, 176473833083073, 17127037652003366155131344662127781168166228802, 97053213333881696302229904093361571651471291202, 176473900191937, 
    145720204333760, 286044960592064, 285976171909312, 317209643852097, 538573920120789213425353466224105219252594956484929593476579784052431455608546684046917380427619672196, 317211321573697, 
    317211791335745, 123695392436852379508231302202309582380611299138883968182017294871231182967881494299882077372607881232518396150089644403984529888440624926876026417525603307667037761541452359, 538833442545653603971551570866998823909590292472244879188418925154166886589646466480771229735903838340, 537795352846196041671507583448299033723535104648666075136836646333152692322021630364820225837043564676, 33283751113574826881503524289022424008528992624147109085483142072053836773789625477334668085453615237, 11440630821309779291363373863291032965052633666, 
    91366501614006607126956147614147983362398098242, 4122285245674505847143378038682325532780561649984459292953562054229768522310403176464356902532241792097914428979329971361195017689484872911506692060846704069185264368842930758, 581126808933056, 548065208777344551960654481272888362449013576258, 183045216210090936512490604121723426671073169986, 548422019339391574247165198911752306506036417090, 
    145307472236736, 145307472236736, 145307472236736, 145307472236736]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b3_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨2, [1], 1, []⟩⟩) (prev' := [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b3_10_0
  · exact tv_b3_10_1
  · exact tv_b3_10_2
  · exact tv_b3_10_3
  · exact tv_b3_10_4
  · exact tv_b3_10_5
  · exact tv_b3_10_6
  · exact tv_b3_10_7
  · exact tv_b3_10_8
  · exact tv_b3_10_9
  · exact tv_b3_10_10
  · exact tv_b3_10_11
  · exact tv_b3_10_12
  · exact tv_b3_10_13
  · exact tv_b3_10_14
  · exact tv_b3_10_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161224003915968, 387108089112897, 176473833083072, 176473833083072, 176473902289088]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [317211791335745, 1161157431922880, 1161226151399616, 1161226151399616, 176476049772736, 176476049772736, 
    176476049772736, 106109455241408, 176476049772736, 176476049772736, 15121341268958217710875072373595407989066104045286341663380634753164010131433675931824323699828682602480388021252343388347481447343383692004792457209737244219556390287473307614333170560465107496906349978451521716638175222273004245172083208759901346070536245997512, 3957316615500260807304154415383440348927267595372264587085710692772190009006833202005339550497400995901920204607463307506685797027284630189518952922225429864765653395661041222, 
    3894729222642533753454633438695733600004827690999301372656108772787500907251409886434889887586380201191854365589197580735557456620136737334365980216858748533079684433489479, 123695392443150858820748899887423351101132307054565268552766093658242440827669435164447072354331205580417522669252454813790871653099234909909757433336287348861039697731778630, 286974751809857, 291372798320961, 286974751809857, 291372798320961, 
    286974751809857, 291372798320961, 581401195107750416007191794568255233073116302102285076771127196732521940463555942674784446413048598597, 291372798320961, 300169428214081, 300169428214081, 
    259649639805701794309992690999734302692173818757712368079334104336847107039161359853902533958144197, 260536679396684181050952589472245220540275783041502437805346388639005094477002472826235519449796805, 387374377085249, 387099499178305, 316936913428801, 188397414134813289413053047802213214345767162690]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [246844729004224, 1161226151399616, 1161226151399616, 1161226151399616, 176476049772736, 176476049772736, 
    176476049772736, 176476049772736, 176476049772736]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161294801604800, 106107236323520, 317213938819521, 1161226151399616, 176476049772736, 176476049772736, 
    106107236323520, 980451739385969150888343969809978742182270209167727407721141055242693991245226150522649341588692610866921972032698977051883825423620538371525391140331004168466776067010347357011322395957228509183560776823330244463712333920278928373783299266348637166323630624496988553, 980451739385969150888344019478428648220147385561789404268107228890713197510403322232087939361625284217174574318905441783400686254218711462944154905497953109136825973993571419298528383716670608464411585356681333281449698108986486171771275332941186491704410656496988553, 595676670629787017905321979609534791171029194473468858239729616289250502301020951173880704076082185221, 387101646662081]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161294801604800, 317218233786689, 1161226151399616, 1161226151399616, 1161226151399616, 176476049772736, 
    176476049772736, 2928712635670481346602101760142582587977992508226, 4217239420481885636211905528504706373480688209436428399965435642922752135354437041699651781677826180, 176476049772736, 176476049772736, 537795352846196041671507583448299033723535104648666075136836646333152710596802257706630088144919478404, 
    535719165589160008864095972014603836760261255336619568614554831432541605829894529516146986239258502277, 123695392436852379508597921950393950270075578820492944895569140678978550854728653870293730418107306841233384385773186286837813280235800887570153469345555756291045078018768454, 387108089112897, 316943355879745, 387108089112897, 316943355879745, 
    4217239420481885636211459010914495579850478051834331480633611333426387709593167330518164797183508612, 4217239420481885636211459010914495579850478051834331480633611333426387709593167330518164797183508612, 4217239420481885636213217603269787319958959480924795854986572478733381898422885272826539808160759940]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161226151399616, 1161226151399616, 1161226151399616, 106109455241408, 176476049772736, 176476049772736, 
    315644150232281319585688704314262946501856155625855461232454189291733778341090208390390226743559680133, 176476049772736, 176476049772736, 33283751113574826881503524289022424008528992622601518489946768323548366981567576093258237713549848709, 1161368023863744, 966141751781705548019613169737220069598330966578509521367459913286620445093495564617124603374409325802326268440779776899402024049658976481374712665448095140265385450819143, 
    1932386705032721835166147498657400595096127451292464175214118570451404764257704470282644924926731473541168758117052047956738062999286749505273990107990399167857596493527111, 387101646662081, 316939060912577, 4217239420481885636211685893556066751628065196321258164476361138277180968697069481439940090161021060, 4217239420481885636211685893556066751628065196321258164476361138277180968697069481439940090161021060, 581395120223413659886869390394306174360970745381749438953295130813180498077819102404032219069449203845, 
    33283751484824631724446673034145557602850011312660391937804027336362161820511497469990245838091415684]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161230446366912, 387108089112897, 4217239420481885636211459022654366309422256211303055778504927565358861624338774724532483390993350788, 1161299100897472, 3957286482768179819956743135535386095930392296355129030498711427557556327111262820624217108510860923131694491049815261948198693592731188554005086751172623798169230916332772934, 176480345264320, 
    2923059026705577860035993394102158089196822087491, 183045216210090936512490604121722863716824781378]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [28545062755111126011002847825351743752334493507, 3957316615500260807304154415383440348927267595027034717924758774570976823971489438878570443832231515775145962619810172600358564178996374617032710923655175259339015605204463174, 548065208777344551960654481272887799494765187650, 548422019339391574247165198911751743551788028482]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_12 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105776595275968, 28545062745826614654543029232837489191295128386, 105707804364992, 12845327246329986523001071699463173143682617922, 105776523841728, 176076617814208, 
    176076617814208, 176076617814208, 176488934674624, 51381112982594009657072199027247165031418185539, 176007829131456, 176488865468608, 
    176076617814208, 150635309965633, 176076617814208, 176076617814208, 176076617814208, 176007898337472, 
    176076617814208, 176076617814208, 176488934674624, 316814106431680, 286974751809857, 366804056277179102129321366273149421138810540866, 
    365421404800493516219999968057938807533032478530, 183045911749922965993481358757799644276251996738, 730798207961675627337607791914524469157796267843, 1461551814199029293895701467060356779589408724802, 1464361729701974451891127397486998045056443683650, 1464361729701974451891127397486998045056443683650, 
    730845597523764703584908602725823316606324871746, 730845597523764546396234174425377531015127405122, 730845597523764622455270188121440708427092365890, 732183652444147467471916235119037833070497600066, 732183652444147467471916235119037833070497600066]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_13 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [300184393491265, 581659370218305, 1143578061710145, 1154573446425409, 1145846139990977, 1143784421466945, 
    300184393491265, 300184393491265, 581659370218305, 581659370218305, 1136981260380993, 1134988328444737, 
    1136981260380993, 1136981260380993, 284791230702401, 1128184898921281, 1128185167358785, 1154573446425409, 
    1152580514489153, 1130384190614465, 427727809426369, 183045216212744210328599737795323594158871949890, 548422019342044858184672093782909831947374047810, 2854506295715390453419768753995330170384290626, 
    551485156945714612346274229963188378808147325411661199656862362124108071542390895894757363660667972, 23549675405742972881518136195331957288075322179, 185542907860407166556083409849073839022402442050, 1427258613643295182688179585381476729412915778]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_14 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105776523841728, 105776523841728, 23549676790819323897268334994930058939231983426, 25690556491338218685467278954848034964107171650, 176076617814208, 176488865468608, 
    176076617814208, 176076617814208, 176076617814208, 4217239420481885636211905634163541590107273274736337505861047344877831224551020933453754128264347780, 176076617814208, 176076617814208, 
    176076617814208, 176488934674624, 316814106431680, 183045214870244774920159312189431438296834191938, 97064015254883712830221316268708845465720853314, 97064015256046791763327176539032271825439560514, 
    316814106431680, 176076617814208, 1427253147878464493681672394494933459403805250, 1427258613664064290894156381631261121185845826, 114224765568707201138575675023949865376649598787, 23014456880280111481682556663805046034580652867, 
    730753606258642854528498193892718131531533554498, 730753606269255909307343381566587387258188370498, 1461507223427547559925642296544890076545956254530, 265751027411102706756238584108673700935104377932504382232310647715003511817823568740195403513925681284, 1461551814199050063162363768885135239168269555522, 265856395036478320592505678676601135255137476060407965144773031101668207124754874668396762032126771332, 
    1464361729701995221157789699311776504635304514370, 265872615188032345003444305520771183226437239218958493411093882538055198614076720122253921545340010628, 1461685619180664797282620678389833040484957754178, 730756393883673454697433746569734230997475627586, 735038153295344946545654850720063873131498017346, 1464361710667450402964035382779829613534847779651]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_15 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1136981260380993, 1136981260380993, 11440326015804412236795739343173366503989867074, 548087505611964723880507459517821847301462716994, 1128185167358785, 1128253953946561, 
    1128391258678081, 1128185167358785, 1154573446425409, 1159040279524289, 1152580514489153, 286990253958081, 
    1130384190614465, 291388300469057, 1136981260380993, 1134988328444737, 291388300469057, 1464361710667450402647122732722772263160671978307, 
    1130384190614465, 1130590281933761, 1136981260380993, 11774838384770655807203397239074217937768313410, 183045911749907399204496625959632778168916537922, 183045911749907399204496625959632778168916537922, 
    11774839745900123490957251092572647664841159234, 548422019342060435134668971267221128462314009154, 365733617785390696851019944090218361562106745410]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b3_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩) (prev' := [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b3_11_0
  · exact tv_b3_11_1
  · exact tv_b3_11_2
  · exact tv_b3_11_3
  · exact tv_b3_11_4
  · exact tv_b3_11_5
  · exact tv_b3_11_6
  · exact tv_b3_11_7
  · exact tv_b3_11_8
  · exact tv_b3_11_9
  · exact tv_b3_11_10
  · exact tv_b3_11_11
  · exact tv_b3_11_12
  · exact tv_b3_11_13
  · exact tv_b3_11_14
  · exact tv_b3_11_15

private theorem tv_b3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 0) (a := 1) (rem' := 105) (cur' := ⟨2, 128, ⟨0, [], 1, [1]⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b3_0
  · exact tv_b3_1
  · exact tv_b3_2
  · exact tv_b3_3
  · exact tv_b3_4
  · exact tv_b3_5
  · exact tv_b3_6
  · exact tv_b3_7
  · exact tv_b3_8
  · exact tv_b3_9
  · exact tv_b3_10
  · exact tv_b3_11

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, false⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, some ⟨0, 0, false⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, some ⟨0, 0, true⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, some ⟨0, 1, false⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, some ⟨0, 1, true⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [581126808933056, 1128322474119360, 1128253754642624, 1128322474119360, 15015491880075510186898946478850717058093775717941504182871393619228524798168863546189639835146878392895538587725045139440929684222820542526466613866241278586469217875186788591392578895271827550139313880439039660247206738217451393800977645008522128206071040499559113, 581126808933056, 
    105707806462144, 105639086985408, 105707806462144, 105707806462144, 105707806462144, 105639086985408, 
    105639086985408, 316814102237376]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, some ⟨1, 0, false⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, some ⟨1, 0, true⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, some ⟨1, 1, false⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, some ⟨1, 1, true⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, some ⟨2, 0, false⟩, none, none, none, none⟩ true 105 ⟨2, 128, ⟨1, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [581109361414848, 581109361414848, 1128184900814913, 1128184900814913, 1128184900814913, 2923036725960399411570803720320673941019284768323, 
    531501965722252339719153175654159251103778906999082824030257485097444703186735447947230234696465436485, 531501965722252339719151417920491632846355695692230589857010064919822704877929039688216898808770383685, 431146266529984, 290546217128128, 290546217128128, 159446651507392, 
    532021042251963798731965620843914660663169648485005929422598483252240207020844195607059036158924715909, 581659116704448, 16674316292597265155222679164062872373172622608473529395681906152780268677168032826024924160652992964, 1464361709306320934963098673473112513624483631938, 1134988351509440, 91522608147619868755361059175053342544677114690, 
    291388055360448, 3957286424721394476491768881696603703764949270905187351725092416484938602254341605000608921473148624328576453730065294062537993615305547357433809825212569514415307217903726151, 563517175370432, 563517175370432, 581109361414848, 82068536038336, 
    172503365325760, 290838300070848, 1128184900814913, 1128665937152065, 1136981262478145, 1128322474055873, 
    1128322474055873, 1128184900814913, 1128185035102401, 1128185169455937, 290554815451584, 290554815451584, 
    2923728051605758559929334276757643509464395952962, 290554815451584, 290838300070848]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, some ⟨2, 0, true⟩, none, none, none, none⟩ true 105 ⟨2, 128, ⟨1, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161155280179392, 1161155280179392, 316943089803585, 3957287367290623150376993181293177581232129622381614393266729986514201454050778545139661153342885552570287911092679810267054892737660227276090257754711954441325520718842001991, 3957286659672668510067584957861248333657285160243249910408799709717896157840201095734624724798287357474680439320908363175653193101711044063198721783208836002983090567448538695, 1128655334084800, 
    1128655334084800, 565715984715968, 581109629850304, 581109629850304, 290545948692672, 290545948692672, 
    1128872230260928, 565715984715968, 567915070886080, 567915070886080, 563516890157248, 563516890157248, 
    581109629850304, 290838300070848, 1143784423564097, 532021042251963798731965620843914660663169648485006639712394246743212552494271244372655613984177931140, 3957769494445566912370758382200966777530261105346134769815185518576246753930801280115989168238267472875799748387237377433073812207041673581597359762669144234862380580899610182, 129824574333740104425167142368023059422853181824057013567169384693827191327804494341828882729285124, 
    1134988330541889, 290554815451584, 290554815451584, 290554815451584, 290838300070848]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, some ⟨2, 1, false⟩, none, none, none, none⟩ true 105 ⟨2, 128, ⟨1, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161157566337216, 1161221986717888, 1161359425540288, 1161359425540288, 106105090934849, 106105090934849, 
    106105090934849, 246842713512129, 106105090934849, 1161234884202944, 1161234884202944, 1161368023863744, 
    106105090934849, 188397414118873100197553748895780383986991256386, 106105090934849, 106105090934849, 1161234884202944, 457547442557376, 
    457547442557376, 316943093993920, 736462602516499213040503699108864369391046792002, 1161368024650176, 308439076049856, 581109361414848, 
    531503961561272569452951749475123106869455569377671845041723825986827184039449626490571548602399224132, 308439076049856, 581109361414848, 581109361414848, 581109361414848, 572313276781504, 
    581109361414848, 16611463206231790331582690966734974737471449320484367448153671820150081905605332790751894830366355780, 736462602516499213080117780366001041804626006850, 581109361414848, 290563422163904, 581109361414848, 
    581109361414848, 581659116311232, 581659116704448, 581659116704448, 581659116704448, 149825933808576, 
    149825933808576, 290563422163904, 105639086983233, 105639086983233, 105639086983233, 18159407993536, 
    73671846727872, 73671846727872, 565716454490689, 565716454490689, 426748220018880, 286148170617024, 
    286148170617024, 849377301106880, 431146266529984, 290546217128128, 290546217128128, 1143646997320384, 
    1143646997320384, 1143784436142784, 1136981222691776, 1139248963392448, 1134988351509440, 3957316615499415517322473052542012611435118212817491353968827319353173983327911198720849795181688707672200805286193057908795202725746795873449748221325188210857160593307522630, 
    291388055360448, 1464361710667450402646891213100412564074823488322, 581109361414848, 581109361414848, 581109361414848, 563517175370432, 
    563517175370432, 563517175370432, 581109361414848, 581109361414848, 290838300070848, 290563422163904, 
    105776525936705, 105639086983233, 105639086983233, 106120123320385, 105776525936705, 105639086983233, 
    105776660224193, 589699837819074158287220369446635233125573938845594946456487701420350195613453933173288921160720072836, 581395120223413659886868525052209452322863570162498957649666945056664595504295243361760546173397254276, 105639086983233, 105776660224193, 589699837819074158287220465640199794940294362884597382124424433202081580026956498315423974357863669892, 
    581395120223413659886868621239904078869638619700288133456737066691086311210532893032621910617346973828, 532021042251963798731965620843914660663169648479546287519980094215868123512504299566219673797433705348, 290838300070848, 290554815451584, 290554815451584, 290554815451584, 
    290554815451584, 284378648310721, 426761117503936, 426761117503936, 290413077336256, 439955257037248, 
    129777547423926009027780781102565142315753704806743011155612044840742836114666054625206608928492932, 456741910946662225458538112658494983610761761602, 365398058617465896121540455778301290630143300418, 431159164015040, 290554815451584, 581659116442304, 
    1464361710667450402963803863157469914448999289666, 73669701341376, 73669701341376, 565716454490689, 565716454490689, 426761117503936, 
    286156768940480, 426761117503936, 426761117503936, 286156768940480, 431159164015040, 290554815451584, 
    431159164015040, 290554815451584]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, some ⟨2, 1, true⟩, none, none, none, none⟩ true 105 ⟨2, 128, ⟨1, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161155217264832, 106105090937024, 1128307779702976, 1128307779702976, 1128307779702976, 45850507075851016982751834583598193081862603587, 
    1161155217264832, 1161155217264832, 106105090937024, 532345381924043839394587230492806517394944262445253665740865389220736974648421308766548507950848426116, 106105090937024, 1161292859838656, 
    3957302463140322436542402174683200916258089672011917355559166374409163749091216060446009074714730168038905447502576930027549740135862058419009548330815682684665102126337187399, 3957287367290623150376993181293177581232129622381614393266729986514201454050791361061876678802668496104250857700685408096806718895998304230412273175908066474902569977934477895, 1128307779702976, 457547434176961, 316943089803585, 1161368023863744, 
    1161368023732672, 316943093993920, 106105090937024, 28545062747135879611981275997201408024666728259, 581101039915712, 290279660720320, 
    1128314423480512, 290279660720320, 290279660720320, 106257562472640, 88527938261184, 105639086985408, 
    532021042251963798731963863875199192775619027109560563231813219623429323576231760576498170195309680517, 283957741494593, 123665204429260709806041275404950103065106979026191378487038295388898089591471735168618940557823341924341520086562248204855010652905201657362452802922227806022642216904685638, 290563422163904, 730778694777745561334076001686425548472860021314, 565716456575168, 
    567915477733568, 581109629850304, 581109629850304, 581109629850304, 3957340444165487474036938791759970686300609644169948882690801370744384113732836207528973167188416396582237469887527930688413996308531199424283696720121610577241020721717542471, 565716186063681, 
    290546217128128, 290546217128128, 88669672181952, 158896745353408, 18159122780352, 158896745353408, 
    18159122780352, 18159122780352, 105639086985408, 105776660222144, 2928714552130814282839884467681046390902993476163, 80007553618880, 
    88527938261184, 105639086985408, 105776660222144, 583925458845267980548670224145544649568109144810015688354033560872949846404049398995099094222127236, 583925458845267980549659432351538066009591863149056888761494648040157606832698681643439038564417668, 105639086985408, 
    105639086985408, 158896745353408, 158896745353408, 532021042251963798731965620843914660663169648479545221391641475968973088515680371957261949192268535685, 4112351938858656001185412475612465082423592798455277399872199051955922579257854841082997470392138107279246824442444044451257095498342511447428996481740066222998843999335177799, 286577688318656, 
    365733616413773074022053383008713676831047304003, 366090429698079031676071808354574480342215836483, 290838300070848, 33218933866359176793898874005847856646070458194280397541626543925445923120746363771358975230639292548, 286577688318656, 299634384704192, 
    308705900893120, 18159122780352, 18159122780352, 736462597040100518018546133232067285629592933186, 563517427028160, 565716456575168, 
    567915477733568, 563517427028160, 567915477733568, 567915477733568, 581109629850304, 563517427028160, 
    581109629850304, 581109629850304, 129777054357776070719013316393620869763460942033091475333682923451212570394884526854789937924158980, 1148045031257025, 1143784423564097, 1134988330541889, 
    706865991283649, 565716186063681, 145419280585152, 286156768940480, 149817327096256, 290554815451584, 
    290554815451584, 149817327096256, 290554815451584, 290838300070848]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 0, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 105) (cur' := ⟨2, 128, ⟨1, [], 1, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b5_0
  · exact tv_b5_1
  · exact tv_b5_2
  · exact tv_b5_3
  · exact tv_b5_4
  · exact tv_b5_5
  · exact tv_b5_6
  · exact tv_b5_7
  · exact tv_b5_8
  · exact tv_b5_9
  · exact tv_b5_10
  · exact tv_b5_11

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, false⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, some ⟨0, 0, false⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1472948235471176591424237874729127838527881806403, 730798207961716516794515676274936584431529469763, 1161363527569856, 1130590086894528, 1134988133405632, 105639019872321, 
    11462626800885117026553134099572323166107780931, 365421404832395109812831077193489406176572524355, 146235050950721, 146235050950721, 16611462835465381822984620305401450593891493467408287192233954935004432888896885618752914930113237189]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, some ⟨0, 0, true⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, some ⟨0, 1, false⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161157371236800, 1161363527569856, 16674316293503634923741747532963388744344688785560145315924706325997210792525330622417514266334646596, 1130852008460353, 1161367822537152, 1130852008460353, 
    1161367822537152, 1130590086894528, 1148182272938944, 1136981000328128, 1134988133405632, 1130452576501825, 
    1128184900814913, 1128184900814913, 1130452576501825, 1134782239288129, 531566814649450785657876671288681220503688302853484596949183997223807369863175713568544367024202334340, 2923059026708588703916805899858582544889326118723, 
    539741771032678970782398941296557377351654314487988969702302053200574461337347360141614783424035569796, 1130849930186944, 2923728051613672299785098141355752112135979718466, 532345469045932185984968987902016451231170764244666187845956737630718153140346174984260407857288331396, 539742768951196325507865402138699056102340450197875606894334348058039577989282022289613866135697244292, 163312512029377, 
    536692881530235262567516252180837327163866389679883351432200315084597933295966824135967233457661427844, 1161363527569856, 1130590086894528, 1134988133405632, 105639086983233, 105707806459969, 
    105639086983233, 105707806459969, 105639086983233, 123695392750876562368132023468398535761288131695995059881514773570258941362565669331239726995993486461144399214308946888072395317658972583821980093133308545476361924002491974, 105639084888256, 1161292654121152, 
    2923103628695950885890123742910415390964130517570, 2923103628357184667195806833741807313426468312898, 2928712635670479399483337662181370028418268140354, 539742761063115823810041972267062218841710505356774292524661452181964343035427763653292491301361827972, 11451432787134444715784545940866033436233568834, 11451432787134444715784545940866033436233568834, 
    11451432787134444715784545940866033436233568834, 11440630821309764079556171128518869339693126210, 143521302729409, 3957316615499466468212719094225360144690030576193401326336176225563880792474660491750709789220521317904490689962216329088282656043812561535844291629817740635849717105854688838, 145169899061313, 145169899061313]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, some ⟨0, 1, true⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [567932669399744, 581126808933056, 298350772801096517300608471612454741261709467534140439260839331277757301653835034481767183556262931599945209433157098108552135175029577737105087546391396454181471758660827766792786632927806536552368757463101966751003969043854509753639562133560123769993568052232749854399349422931546381342909297754533517094551911120145172412897252799485882985111038553798978398897300261598613558281423440743406470270730794766826938045923913058082315387690741096850403937030862774314691883442168413083005752919018890623820, 1128322476216512, 1128253618196672, 1128253618196672, 
    1128322476216512, 1134850757497024, 1134850757497024, 105639086983233, 1161363728896448, 1161359433929152, 
    1161368023863744, 1130590288221120, 1143784427754432, 1134988334732224, 2923103628358223134034802032402387666271951926082, 2923371238321452602255508810783217184506942337858, 
    2923371238321452602275315851411783268905328325442, 105639086983233, 16674316293503634923741747639460785823469784610328595876424569023004720035184481289290667846447302596, 567932669399744, 563534622888640, 581126808933056, 
    15015491880075510186898946187753574751622599941298218299372504857243500336452399440668269081453663200600482297712880660701794570965762762298350850783579682161568180887062524419528232606052372767584382065832910872610259569897748944831565212105158404127850753249877513, 567932669399744, 581126808933056, 105776523841728, 105639084888256, 105707804364992, 
    105707804364992, 105707804364992, 105639084888256, 105639084888256, 316814106431680, 316814106431680, 
    588342247595984243146960461664806650347894111134823189058319539685329580796825222214280004563953995845, 146237265553729, 146237265553729]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, some ⟨1, 0, false⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, some ⟨1, 0, true⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, some ⟨1, 1, false⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, some ⟨1, 1, true⟩, none, none, none, none⟩ false 105 ⟨2, 128, ⟨1, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, some ⟨2, 0, false⟩, none, none, none, none⟩ true 105 ⟨2, 128, ⟨1, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161368023863744, 1161368023863744, 316943093993920, 316943093993920, 123695392443150858820591777138244336291396694676127880012348308470959859752155427914208293232690225610499772746446926315662005548768336767756207517249308267352480943498588742, 316943093993920, 
    316943093993920, 4158272566466870091383534110015526725823507602172611964368012567025801406072639159820665750206038580530867465014741796447977381971721340934566565056801883723223996687273947718, 1128184900814913, 1134782239025985, 1128184900814913, 1128185169455937, 
    1128184900814913, 1136981262478145, 1128184900814913, 1128185169455937, 2923728051605758559929334276757643509464395952962, 2923728070659203411399534915808373065462613362499, 
    1134782239025985, 1134782239222593, 1128184900814913, 531501965722252339719151417920491632846355695692230591244294884246477388646713823652892939772354809669, 290546225516992, 581109361414848, 
    1134979745059264, 1161368023863744, 1461529513368760171541708194267836154564351099715, 290546225516992, 1134988334732224, 371085815683523277355380183440942374928657699650, 
    371085815683523277355380183440942374928657699650, 286156768940480, 290554815451584, 1461529513368780940808370496092614614143211930435, 290554815451584, 290554815451584, 
    316668207698112, 581109361414848, 567915221881536, 581109361414848, 563517175370432, 563517175370432, 
    581109361414848, 290838300070848, 1128655334021313, 6707465290378267800188040996305299253104276013836041762246681885221414074130258631026200768032554559002344796950434382194368757363173302624732023885784762686877725576012656367131331413274726370420771993498299112414524766785390860658210500772935548940210586028053788305080033752835951486118802272683481773213239572829867831718710857409353544122215615169848828501089050370254379594, 290838300070848, 7775394538434561093499525410398690591347764560630389078500841590537303646919891797599561468581924085502269704258175362072150170896310239594054949361682932360750194348783686, 
    581126540759744, 1464361709285094744434226208549526824028714636098, 567932401750720, 572300383491008, 572313268392896, 572313268392896, 
    531503961561272569453176849135596512374907906918266411641170991799136224873392324828390395036501795268, 589892569535424, 581109361414848, 581109361414848, 531501997402235843673079910031682940798121700203441071936912068624241216668446776606984635697348240325, 531501997402235843673079910031682943975115346403742413839987522459626710797609751595615523369022415813, 
    286156768940480, 286156768940480, 572298760315713, 290279929155776, 431288008839616, 290279929155776, 
    290279929155776]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, some ⟨2, 0, true⟩, none, none, none, none⟩ true 105 ⟨2, 128, ⟨1, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161155284373696, 531570869686402707761686297389117202236281552858134913091384549811172057374627816650183521235263308676, 531502947801755124347349858583043377094483510225262994396655395874472150009768629543161110252455294852, 176347335373249, 1161155284373696, 316943089803585, 
    1128655336181952, 1128655336181952, 567906778747840, 290279929155776, 283957741494593, 283957741494593, 
    283957741494593, 567906778747840, 308422433051584, 581101308351168, 581101308351168, 568319632479168, 
    572304678458304, 581101308351168, 290279929155776, 290279929155776, 1128253618196672, 1128253618196672, 
    1128253618196672, 1128322476150976, 3957286427485527111966371202728695842583176829069748882624522604873639642797585612527134723025456179512919979459974805248740161801745531798802104627668514056541580189425985606, 3957286427485527111966371202728695842583202433288036591986707076145174892945506888178211881251219883913953158102930404076072583540321614269678825582198778606881172730434025542, 567915075080384, 580697312989888, 
    581109629850304, 581109629850304, 12845327246330072723244303890083026712393683522, 12845327246329986522536843004148506872158097986, 158897168978624, 290545948692672, 
    290545948692672, 783515728287328255512451532483974193411197323044829544300422946474584637817219328075508153107858907078648094166746607158332980451521924739989696388562692659200777476506201557129284097338077480242924065423177435560605298360757371552235032403516734668695021978307932891763173448921098833239599669321052951689347671870127130494669499269707449207167370187320808623269923172532312491482282903126682595236486506623121659721300648185191516470878395201018145713064306693625920437819848536664608665523680603214197772350055341803257051109127073606826996116652194351421647015385656995661167256692436284878938972541239885732618190160431661466943107600239469020143766662775247360548494300679274445040333717039663895437564662668839796291823414377243786814273021010153940607854322567705075767326073445636434867009590279094697351616009903492858662469276870568614535999194925189995637318737509594842495720044907376460877108219049235805939981033367199433232148875882007100756268291895869680199424935062741976315711877119779156562, 162201517957235070749567927644813573688538839438190958038447365373730236890657308209996660524463620, 551485156945714612346271653900167931826173311147715374806310765591114287063269126039036716986448964, 551485156945714612346274229963188378808147329852933978667342620995784254419443714394550026685955140, 159039037117120, 
    159039037117120, 18159659651264, 18159659651264, 18159659651264, 1128253618196672, 1128253618196672, 
    1128253756674240, 531501997402235135570270672223497722561811611384958941158105423784710625611681629522205595342420263044, 1128253618196672, 1130452711641280, 708378239177408, 567640750822080, 
    708378239177408, 145290293153984, 145290293153984, 567915075080384, 145290293153984, 286027781509312, 
    145290293153984, 567915075080384, 563516890157248, 563516890157248, 581109629850304, 290838300070848, 
    2924430527809705070088021247847352967567446643522, 18159659651264, 25690556491338218685157792764444006042572953410, 158484986335936, 159034742149824, 158897168978624, 
    18159659651264, 18159659651264, 1143784423564097, 6440976386579351007184360202671336928308103994947825331788237138447489561203270958798606268530068483283960916586089065055051514098052050815428517148001942512444649902645935686, 532021042251963798731965620843914660663169648485006990001798072258480856891751591232907009299714622340, 1134988330541889, 
    6707465088723695756462041669077627629859943211427288058831457131341713279935809002271610884562989633747389829393117096023698233890445552072130854998197926784976209206539914174131281757701370673824900632331174015103389411755937176149142432403836185117737735201264528208025617468163063195880558222890504582567937438517325260551162437714993373947435439086815403249944077717519860810, 290554815451584, 290554815451584, 290554815451584, 290838300070848]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, some ⟨2, 1, false⟩, none, none, none, none⟩ true 105 ⟨2, 128, ⟨1, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161501172175296, 3957286438542059413317784003974146676407103677382444878276228009663842842020448419180671720229170008869218664760850828591717856270190048795964675283656648303126025204949102150, 730842809590394686158655526373621081270883752770, 732180859406542027361224621420599094437765747522, 1161234884202944, 1161234884202944, 
    105776525936705, 284378648310721, 426761117503936, 431159164015040, 284378648310721, 284378648310721, 
    426761117503936, 426761117503936, 290413085725120, 290413085725120, 439955257037248, 286852574614464, 
    568327551325120, 308705364022208, 581109361414848, 568327551325120, 2928712635661174768018621609549156686392245355331, 97053213332550363998982246751656397975985324867, 
    1161363729682880, 1161368024650176, 1130590289007552, 1143784428540864, 1134988335518656, 154223963542464, 
    589630568141760, 290563405386688, 564789740564044329282822216364877668663197681665740062387382482033448584823211047380415285973854037060, 149825917031360, 149825917031360, 290563405386688, 
    2923103628358223134034840718176197168324631606082, 149817327096256, 290546225516992, 14272531393526804489598839872300813045335327555, 1134988334601152, 1152580520776640, 
    1134988334732224, 167418103075776, 299359498408896, 290563405386688, 2923036725867415766959856982952414837871908764482, 2923036725867415766974712263423839823384773931842, 
    286156768940480, 567648925520832, 286156768940480, 11507228420237903406507393022878046712836129603, 290554815451584, 2923371238321452602275354537185592770958008005442, 
    158617715085760, 299350908473792, 149817327096256, 290554815451584, 14272531393547573756261141697079272624196158275, 290554815451584, 
    581109361414848, 1161368023863744, 1134979745059264, 1161368023863744, 316943093993920, 581395120223413659886868621243258330693075244354193523172568440700039717745879028145361882348375994500, 
    105639086983233, 565716454490689, 565716454490689, 286156768940480, 290546225516992, 1152580520776640, 
    1134988334732224, 105639086983233, 105639086983233, 105639086983233, 365398058617465896121540455778301290630143300418, 290554815451584, 
    565716454490689, 565716454490689, 286156768940480, 286156768940480, 290554815451584, 290554815451584, 
    1161155416494272, 17127081202995492421949558116143320587065889346, 1161155416494272, 1161567746331072, 316943089803585, 51381112946040158328984524324178507297043013442, 
    105639286214848, 105639286214848, 565716198625984, 567915221881536, 581109361414848, 567915221881536, 
    581109361414848, 581109361414848, 105639286214848, 105639286214848, 4111898116432704553380310793289078220341057323329311807578554521122088531636319273615556054251478090616447074984534139350691423503422787231710639203770179976553619822805823047, 28546369429139435525172540865741398204523484994, 
    1461546326125036362266283430743942550092410591042, 990540016391104, 990540016391104, 581109361414848, 563517175370432, 581109361414848, 
    567915221881536, 581109361414848, 581109361414848, 563517175370432, 565716198625984, 567915221881536, 
    567915221881536, 581109361414848, 563517175370432, 581109361414848, 531501997402235843673077274021725842911483841059105563912360940486185311099866721471230131629398998084, 531501997402235371604539981213064686716613139777685139418416824908282140840649504834510211789908917316, 
    143078250774593, 75351194079936, 16609689126196325622104005442823024946530596308092756479680969794805454282429668835733577007069008196, 427169156174784, 567906631946944, 567932401750720, 
    308417601213376, 308439076049856, 308430486115264, 308439076049856, 581100771480256, 581126541284032, 
    994512861139904, 290825415168960, 572300383491008, 572300383491008, 572304678458304, 572304678458304, 
    853796843426752, 290846890005440, 853796843426752, 572313268392896, 572313268392896, 308417601213376, 
    581096476512960, 290825415168960, 290838300070848, 290825415168960, 308439076049856, 581109361414848, 
    581126540759744, 1591594326637577600631662151495112104592011274040546679571523390562643458348868885853286743116608244754800862787563555446073418709602702461546779793914829487660606305596292456434663791516685796583853334952631481780896608110543046864742528013730822599296958472246197512, 581126540759744, 581126540759744, 24307905004060306777830642052701800018609215298, 581096476512960, 
    3957316615512914002351352982678628398835579526029143338830412950974156805915178149175142316945233940228417876026104333459368311541899691553649536563679083429183277254243954246, 106109520189633, 581395120223413659886870286864224289706534368493510810263533378017647909020169222306710040345542148228, 188397414118873100197553748895780383986991256386, 290838300070848, 581395120223413659886870286864224289706534368493510810263533378017647908832157364603367042948329128068, 
    576560986853824, 22858351027262722343669307131398727559616140098, 22880651857531844697045458715515027779064173378, 253439871815555874621117239454928271660212839455308826183056546742377166769378304598015534697860, 256644186946156496688729624853522746573813951200676766886169682435882373512726313763355461323156664808478347833622265538206825264439944859954443274609644519337429667327558, 981230230682060788688386542528490323211909541046980464089783707748970769404484387222376691286282105981097846320140816052539708518083021868967823141535552058960089340620358, 
    265750967022100742192852272687657642285675031833739272164551234581525533443490910296289212397624374788, 265750967022100712688568472009397377696347321951545877532997366477156554431589937386680380843520308740, 981244972719966893643983810680768554208880830772934661994916520761994117437021970274956838992886448144615617146375807390235226773232213303811305226136842100538715711581766, 1464361710646224212118018748176826874466169590594, 1464361710646224212118018748176826874466169590594, 567932401750720, 
    572300383491008, 572313268392896, 572313268392896, 581109361414848, 581109361414848, 106105090934849, 
    106105090934849, 246842713512129, 106105090934849, 106105090934849, 123695392443150858820748899887420302518563639140785144955715429595791985993255266223956700006175282551821472038322863308208395415061538436301184967926704476356858404782685767, 6810605479372839467585783473225401333979937462541447257349260675587449927971423535764158519792728701107159088805247306978186522355498543653675200226754436654842061486417195785538458415258755600334815433669379162922675105829944697808959663400395229616120168828525125836005738408146556265894714395906502614898062578385958720375209060771120925039385113609586597127064517458047716298, 
    538573920120789213425353466224105219252594956484929593476579784052428991295779840368960870836588421252, 990991763179976232357937877688383069060291730835281030513297529059933662330857148441204244982193082049040221536182500694726920625960430633090215246392644087273138231345036410885100416978449108689346859124523274359188834306451654918505492782890278511162950664245956552, 2928712374323153730910491350402134749770753774146, 129777547423926009027780351760340430626847035872746758948577907045657792701667998346529605131750788, 182710353948435630504826918633470861083123135042, 565716454490689, 
    431288008839616, 290279929155776, 290279929155776, 290279929155776, 265750967022100712688568472009397377696835429382489545829193237462705182572106056546041904167243101700, 1464361710646224212118018748176826874466169590594, 
    1464361710646224212118018748176822933814348157762, 72671117250752, 72671117250752]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, some ⟨2, 1, true⟩, none, none, none, none⟩ true 105 ⟨2, 128, ⟨1, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161155215167680, 1161292654121152, 1161155215167680, 246842715607232, 106105088839872, 51381287164796407879790213877626713339441713730, 
    2928712635660011526191811574390547118266955862594, 106105088839872, 90575098225592591870992603792827811754089132058503130527994399574134866342480809935936954702341669517658751815839530719489402022144301836315878919632034303764280770869319, 2928712374323153730911071634518848610668969464386, 513258889805605223322660477602506362728379142807342111572829538568517108761879492894337288248449595738938207419159728847861235787482809815496980451347792302919785514006598, 17127081202995493056048076350934643066959565378, 
    17127081202995416362874859681595278189341446722, 17127081202995492421913291226998597249883181634, 91344201505425351711978011997137844692005700419, 91522607467013596697110297743319031584053543747, 1161155215167680, 246842715607232, 
    469678024263096156171119672210160399660265126676396637222044499669657686584602433364853415618819662724780471908836716765212200082280498242799922072695094692959758315195374817477705967588418529375875829522653286415882284759661145810116822101758562378186760245997512, 106105088839872, 194641827349460318703478816080078309951872693212588177345845133466725726393723869159601154350360581, 3957316615499469982613701026949970110889055846652342018148766089813677673825863388131558689957867346279208342848608468251438825695874940321567900634624644382510661965809102406, 106105088839872, 1161224003915968, 
    1161224003915968, 176473902289088, 176473902289088, 6707465290378267800188040996305299253104276013836041762246681885221414074130258631026200768032554559002344796950434382194368757363173302624732023885784762686877725576012656367131333031298622448873352341174745943936059567405519795487279945926380277249379775049764983936611259874977282045119500601365841656505492512044053561547441079444561172738333309196418833210817007290911365706, 12993372403592322925403936016465393955035194078475975576744614351510315893452202888672232362148013894838119454962582625187471240169158857143609451019026191574794285564368855191973515111737558830645726957130312221788500115762425359238028946150664117564359554565389098265126405078913757411684355879758809087842582290315313455910828642003475636664077261787606666011707682718794, 265751471920874772371719598024317548227487479581801104497485370229582836623176081184127743083893179460, 
    91433404145947491877322761062110047270768493379, 91522607467023981290827367398575248148560626499, 316943089803585, 123695392679231360202601441006439030437972025008540622587843979701457131447463301922659998536367265065747678922906121068565594852256795364465409021305477142422054014016597575, 1161368023863744, 1161368023732672, 
    316943093993920, 589699837819074158287220465640199798039190773543901636069275329845248187939588699459715180958783336580, 4217239466888111241578027001395728598050171987921906544441328393804143865757719611025572926594445444, 123695392443150858820748899887423351101132307054565268552766093658242440827669435164447072354331205580417522669252454862830728960807678377376862302146181224660691607607048262, 871365386199873, 106105088839872, 
    28545062747135879611981294886739397097285510979, 513259120142961964537331115444631005067305970795775521188048066372633372920396530089177829164069643830910785200053479915431659360113968019569354491067076085908686125706823, 513259131305891817247637140293279677263148458116339398038952704444964532210006801312207500633240418703309868099548393377383402049996488301771725847950930748724111457168967, 588338160878082492772227382165677983353803784500362600037365254750337997832766086496908721242089934917, 145412833943873, 145412833943873, 
    567902605415104, 563504558904000, 581096744948416, 567906900382400, 581101039915712, 290279660720320, 
    567906900382400, 563508853871296, 581101039915712, 567906900382400, 563508853871296, 581101039915712, 
    290279660720320, 290279660720320, 105639084888256, 105639084888256, 105639084888256, 105776662319296, 
    158896749547712, 286165358875584, 299359498408896, 290563405386688, 290563405386688, 565716467061440, 
    567915490316992, 567915490316992, 568052929270464, 567915490316992, 581109629850304, 581109629850304, 
    581109629850304, 565716186063681, 290546225516992, 290546225516992, 18159122780352, 159038483468480, 
    18159122780352, 18159122780352, 105639084888256, 528358424992225939167562757954469442437936578448164334376048928478043793232996566837339086448517156953870561978667012300546948482823866749776386172595819020856546197233222, 105639084888256, 105776662319296, 
    105776662319296, 105639084888256, 176007898337472, 176076617748672, 176076617814208, 176076617814208, 
    176076617814208, 176076617814208, 818982257500273568318362351585220831005899039903341184633738046881821326948984568802328418063687217086916109485535564386862359467858731592820473714999650416535253447208247408314573319129281257725233010600895513416546868259951670928799670500787823373322143282231701875927543969185960636520110357098464905579803837860026015568247116382540259966899024637234804158861551618523210, 176007898337472, 145290293153984, 158896749547712, 
    145290293153984, 176076618731712, 145290293153984, 158896749547712, 308430486115264, 290838300070848, 
    18159122780352, 18159122780352, 565716467061440, 736462602484618388753561850878668829699784872770, 265751471920874772371719598131443868463797118280526442583528552114406848939437207913377583626028794948, 91433404145947491600024192262193591450928694083, 
    91522607467023981013528798598658792328720827203, 130775466964488864730919708632539973121588191442445950791007544452023775929694120676764234240825157, 580697312989888, 563517443805888, 563517443805888, 565716467061440, 
    565716467061440, 567915490316992, 563517443805888, 567915490316992, 581109629850304, 581109629850304, 
    581109629850304, 563517443805888, 581109629850304, 129777054357776070719013316393620869763460942033091475333644163162277908943301664819855227678373380, 1143784423564097, 1139248938234817, 
    1134988330541889, 706865991283649, 565716186063681, 145419280585152, 286156768940480, 149817327096256, 
    290554815451584, 290554815451584, 149817327096256, 290554815451584, 290838300070848]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨1, 1, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 105) (cur' := ⟨2, 128, ⟨1, [], 1, [1]⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b7_0
  · exact tv_b7_1
  · exact tv_b7_2
  · exact tv_b7_3
  · exact tv_b7_4
  · exact tv_b7_5
  · exact tv_b7_6
  · exact tv_b7_7
  · exact tv_b7_8
  · exact tv_b7_9
  · exact tv_b7_10
  · exact tv_b7_11


def Residual : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
  (∃ q' : Fin 4, (q' = 0 ∨ q' = 1) ∧ ∃ z, M 1 0 = some (some q', z)) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  let tbl (entries : List ℕ) : Machine (Fin 2) (Fin 4) := fun q a =>
    let v := entries[2*q.val+a.val]?.getD 16
    if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩,
      Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩ (if v % 2 = 0 then Dir.right else Dir.left))
  M ≠ tbl [6,3,3,8,15,10,16,1] →
  M ≠ tbl [6,3,3,12,16,1,11,14] →
  ¬ M.IsHalting

theorem step_proof : Residual := by
  intro M hFirst ⟨q', hq01, ⟨w, d⟩, hM10⟩ hRun _hUsed hForm hMissing hLoop tbl hNe0 hNe0s hHalts
  have hNeSp0 : M ≠ tblOfList [6,3,3,8,15,10,16,1] := hNe0
  have hNeSp0' : reindex23 M ≠ tblOfList [6,3,3,8,15,10,16,1] := by
    intro heq; apply hNe0s
    have hinv := congrArg reindex23 heq
    rw [reindex23_invol] at hinv
    have hswap2 : swap23 2 = 3 := by decide
    rw [hinv]; funext q a; fin_cases q <;> fin_cases a <;>
      simp [reindex23, tblOfList, tbl, swap23_0, swap23_1, hswap2, swap23_3]
  have hNeSp1 := mk_good_ne_sp1 M (by rcases hq01 with rfl | rfl <;> simp [hM10])
    (by rcases hq01 with rfl | rfl <;> simp [hM10])
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts, ⟨hNeSp0, hNeSp0'⟩, hNeSp1⟩
  obtain ⟨hm0, hv⟩ := mk_base_hm_hv hFirst
  let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
  have hm_cmd : M 1 0 = m.command := by cases d <;> simpa [m, Move.command] using hM10
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  have h01_base : UsesOnly01 baseTable := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro q a m' hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact Or.inr rfl
  have hprev01 : ∀ h ∈ [h1, h0], h.c.state = 0 ∨ h.c.state = 1 := by
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl <;> simp [h0, h1, startPos, Position.move]
  rcases hq01 with rfl | rfl
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) := usesOnly01_set h01_base (Or.inr rfl) (Or.inl rfl)
    fin_cases w <;> cases d
    · exact tv_b1 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
    · exact tv_b0 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
    · exact tv_b3 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
    · exact tv_b2 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) := usesOnly01_set h01_base (Or.inr rfl) (Or.inr rfl)
    fin_cases w <;> cases d
    · exact tv_b5 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
    · exact tv_b4 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
    · exact tv_b7 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
    · exact tv_b6 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)

theorem ne_exception {M : Machine4} (hm : M.IsHalting)
    (hs : ¬ (tblOfList [6,3,3,8,15,10,16,1]).IsHalting) :
    M ≠ tblOfList [6,3,3,8,15,10,16,1] ∧ M ≠ tblOfList [6,3,3,12,16,1,11,14] := by
  refine ⟨fun e => hs (e ▸ hm),?_⟩
  intro eq
  have hswap : reindex23 M = tblOfList [6,3,3,8,15,10,16,1] := by
    rw [eq]
    funext q a
    fin_cases q <;> fin_cases a <;> rfl
  apply hs
  rw [← hswap]
  obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hm
  apply (Machine.isHalting_iff_exists_haltsAt _).mpr
  refine ⟨n,?_⟩
  change (reindex23 M).multiStep (Machine.init []) (n+1) = none
  rw [← mapCfg23_init, reindex23_multi, hn]
  rfl

theorem run_add_freeze (M : Machine (Fin 2) (Fin 4)) (x : Cfg (Fin 2) (Fin 4)) (m n : ℕ) :
    M.multiStep x (m + n) = (M.multiStep x m).bind (fun y => M.multiStep y n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, Machine.multiStep_succ, ih]
    cases M.multiStep x m <;> simp

theorem no_repeat {M : Machine (Fin 2) (Fin 4)} (halts : M.IsHalting)
    {i p : ℕ} (hp : 0 < p) {α : Type} (cfg : α → Cfg (Fin 2) (Fin 4))
    (entered : ∃ v, M.multiStep (Machine.init []) i = some (cfg v))
    (cycle : ∀ v, ∃ w, M.multiStep (cfg v) p = some (cfg w)) : False := by
  have recur (m : ℕ) : ∃ v, M.multiStep (Machine.init []) (i + p * m) = some (cfg v) := by
    induction m with
    | zero => simpa using entered
    | succ m ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨w, hw⟩ := cycle v
      refine ⟨w, ?_⟩
      rw [Nat.mul_succ, ← Nat.add_assoc, run_add_freeze M _ (i + p*m) p, hv]
      exact hw
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  obtain ⟨v, hv⟩ := recur (k + 1)
  have hle : k + 1 ≤ i + p * (k + 1) := by
    have := Nat.mul_le_mul_right (k+1) hp
    omega
  have hnone := Machine.multiStep_eq_none_mono hk hle
  rw [hv] at hnone
  contradiction

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem leftBound (residual : Residual)
    (hs : ¬ (tblOfList [6,3,3,8,15,10,16,1]).IsHalting)
    (M : Machine4) (a : Fin 2) (q₀ : Fin 4) (hq₀ : q₀.val ≤ 1)
    (first : M 0 0 = some (some 1, Stmt.write 1 Dir.right))
    (left : M 1 0 = some (some q₀, Stmt.write a Dir.left)) (halts : M.IsHalting) :
    M.HaltsAfter (Machine.init []) 107 := by
  classical
  by_contra late
  let start : Cfg (Fin 2) (Fin 4) := Machine.init []
  have alive (i : ℕ) (hi : i ≤ 108) : M.multiStep start i ≠ none :=
    fun h => late (Machine.multiStep_eq_none_mono h hi)
  let seen (q : Fin 4) (a : Fin 2) : Prop := ∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep start i = some ⟨some q, t⟩ ∧ t.head = a
  let P : Machine (Fin 2) (Fin 4) := fun q a => if seen q a then M q a else none
  have used {q a} (h : seen q a) : ∃ r z, M q a = some (some r, z) := by
    obtain ⟨i, hi, t, ht, rfl⟩ := h
    have ha := alive (i+1+1) (by omega)
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ht] at ha
    cases hc : M q t.head with
    | none => simp [Machine.step, hc] at ha
    | some entry =>
      obtain ⟨s, z⟩ := entry
      cases s with
      | none => simp [Machine.step, hc] at ha
      | some s => exact ⟨s, z, rfl⟩
  have agree (i : ℕ) (hi : i ≤ 107) : P.multiStep start i = M.multiStep start i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih (by omega)]
      cases h : M.multiStep start i with
      | none => rfl
      | some c =>
        obtain ⟨q, t⟩ := c
        cases q with
        | none => rfl
        | some q =>
          have hv : seen q t.head := ⟨i, by omega, t, h, rfl⟩
          simp [Machine.step, P, hv]
  have restrictRun (i : ℕ) : P.multiStep start i = none ∨ P.multiStep start i = M.multiStep start i := by
    induction i with
    | zero => exact Or.inr rfl
    | succ i ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ]
      rcases ih with hi | hi
      · simp [hi]
      · rw [hi]
        cases hc : M.multiStep start i with
        | none => exact Or.inl rfl
        | some c =>
          obtain ⟨q, t⟩ := c
          cases q with
          | none => exact Or.inl rfl
          | some q => by_cases h : seen q t.head <;> simp [Machine.step, P, h]
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  have haltP : P.IsHalting := by
    apply (Machine.isHalting_iff_exists_haltsAt P).mpr
    refine ⟨k, ?_⟩
    rcases restrictRun (k+1) with h | h
    · exact h
    · exact h.trans hk
  obtain ⟨non₁,non₂⟩ := ne_exception haltP hs
  apply (residual P ?_ ?_ ?_ ?_ ?_ ?_ ?_ non₁ non₂) haltP
  · have h : seen 0 0 := ⟨0, by decide, Tape.mk₁ [], rfl, rfl⟩
    simpa [P, h] using first
  · refine ⟨q₀, (by fin_cases q₀ <;> norm_num at *), Stmt.write a Dir.left, ?_⟩
    have ht : seen 1 0 := by
      refine ⟨1,by decide,((Tape.mk₁ []).write 1).move .right,?_,rfl⟩
      rw [Machine.multiStep_one]
      change (M 0 0).map _ = _
      rw [first]
      rfl
    simpa [P,ht] using left
  · obtain ⟨q,t,ht⟩ := Machine.exists_of_not_haltsAfter M (Machine.init []) 107 late
    exact ⟨q,t,(agree 107 (by decide)).trans ht⟩
  · intro q a
    have eq : (∃ i < 107, ∃ t : Tape (Fin 2), P.multiStep start i = some ⟨some q,t⟩ ∧ t.head = a) ↔ seen q a := by
      constructor <;> rintro ⟨i,hi,t,ht,ha⟩ <;> refine ⟨i,hi,t,?_,ha⟩
      · exact (agree i (by omega)).symm.trans ht
      · exact (agree i (by omega)).trans ht
    apply eq.trans
    by_cases h : seen q a
    · simpa [P,h] using used h
    · simp [P,h]
  · intro q a
    by_cases h : seen q a
    · right
      simpa [P,h] using used h
    · left
      simp [P,h]
  · by_contra! all
    apply Machine.not_isHalting_of_forall_isSome P _ haltP
    intro q a
    by_cases h : seen q a
    · simpa [P,h] using used h
    · exact (all q a (by simp [P,h])).elim
  · intro i p q a side near fixed hp _ cfg enter loop
    exact no_repeat haltP hp cfg enter loop


end OMA.BB4H2

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1.H1 := by
  intro M a q hq hfirst hleft hhalt
  exact OMA.BB4H2.leftBound OMA.BB4H2.step_proof OMA.BB4Sweeps.exception M a q hq hfirst hleft hhalt
