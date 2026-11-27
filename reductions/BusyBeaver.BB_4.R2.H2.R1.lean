import OMAReductions.R_BusyBeaver_BB_4_R2

/-!
Split `BusyBeaver.BB_4.R2.H2` (`M 0 0 = 1RB`, excluding the two RepWL machines) into four
sub-cases by the canonicalized second transition `M 1 0`:
- `H1`: `M 1 0` transitions to state `0` or `1`
- `H2`: `M 1 0` transitions to `(2, 0, R)` or `(2, 0, L)`
- `H3`: `M 1 0 = (2, 1, R)`
- `H4`: `M 1 0 = (2, 1, L)`

States `2` and `3` are symmetric when `M 0 0 = 1RB`, so any `M` with `M 1 0` targeting state `3`
is normalized via swapping states `2 ↔ 3`. The swapped copies of the two exceptional RepWL
machines are discharged directly using the sweep invariant from `BusyBeaver.BB_4.R2.H3`
(credited to @marcusbuffett).
-/
-- Credit: @hyprspacecoyote
namespace OMA.R_BusyBeaver_BB_4_R2_H2_R1

open Turing Turing.BusyBeaver

def H1 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
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

def H2 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
  (∃ d : Dir, M 1 0 = some (some 2, Stmt.write 0 d)) →
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
  ¬ M.IsHalting

def H3 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
  M 1 0 = some (some 2, Stmt.write 1 Dir.right) →
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
  ¬ M.IsHalting

def H4 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
  M 1 0 = some (some 2, Stmt.write 1 Dir.left) →
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
  M ≠ tbl [6,4,11,6,16,13,2,15] →
  ¬ M.IsHalting

theorem main : H1 → H2 → H3 → H4 → OMA.R_BusyBeaver_BB_4_R2.H2 := by
  intro h1 h2 h3 h4 M hFirst hRun hUsed hForm hMissing hLoop special hNe0 hHalts
  let swap23 : Equiv.Perm (Fin 4) := Equiv.swap (2 : Fin 4) (3 : Fin 4)
  have hswap0 : swap23 0 = 0 := by decide
  have hswap1 : swap23 1 = 1 := by decide
  have hswap2 : swap23 2 = 3 := by decide
  have hswap3 : swap23 3 = 2 := by decide
  have hswap_inv : ∀ q : Fin 4, swap23 (swap23 q) = q := by intro q; fin_cases q <;> decide
  let reindex23 (N : Machine (Fin 2) (Fin 4)) : Machine (Fin 2) (Fin 4) :=
    fun q a => (N (swap23 q) a).map fun (s, b) => (s.map swap23, b)
  let mapCfg23 (c : Cfg (Fin 2) (Fin 4)) : Cfg (Fin 2) (Fin 4) := ⟨c.q.map swap23, c.tape⟩
  have reindex23_step (N : Machine (Fin 2) (Fin 4)) (c : Cfg (Fin 2) (Fin 4)) :
      (reindex23 N).step (mapCfg23 c) = (N.step c).map mapCfg23 := by
    obtain ⟨q, t⟩ := c
    cases q with
    | none => rfl
    | some q =>
      simp only [Machine.step, mapCfg23, Option.map_some, reindex23, hswap_inv]
      cases N q t.head <;> rfl
  have reindex23_multi (N : Machine (Fin 2) (Fin 4)) (c : Cfg (Fin 2) (Fin 4)) (k : ℕ) :
      (reindex23 N).multiStep (mapCfg23 c) k = (N.multiStep c k).map mapCfg23 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
      cases N.multiStep c k with
      | none => rfl
      | some c' => exact reindex23_step N c'
  have mapCfg23_init : mapCfg23 (Machine.init []) = Machine.init [] := by
    simp [mapCfg23, Machine.init, hswap0]
  have reindex23_isHalting (N : Machine (Fin 2) (Fin 4)) (h : N.IsHalting) : (reindex23 N).IsHalting := by
    obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt N).mp h
    refine (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k, ?_⟩
    unfold Machine.HaltsAfter
    rw [← mapCfg23_init, reindex23_multi, hk]; rfl
  let tbl (entries : List ℕ) : Machine (Fin 2) (Fin 4) := fun q a =>
    let v := entries[2*q.val+a.val]?.getD 16
    if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩,
      Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩ (if v % 2 = 0 then Dir.right else Dir.left))
  -- Prove ¬ (tbl [6,3,3,8,15,10,16,1]).IsHalting and ¬ (tbl [6,4,11,6,16,13,2,15]).IsHalting
  have joinSteps (N : Machine (Fin 2) (Fin 4)) {a b c : Cfg (Fin 2) (Fin 4)} {n k : ℕ}
      (h : N.multiStep a n = some b) (g : N.multiStep b k = some c) : N.multiStep a (n+k) = some c := by
    unfold Machine.multiStep at *
    rw [Nat.add_comm, Function.iterate_add_apply, h, g]
  let run (N : Machine (Fin 2) (Fin 4)) (a b : Cfg (Fin 2) (Fin 4)) := ∃ n, N.multiStep a n = some b
  have cat {N : Machine (Fin 2) (Fin 4)} {a b c : Cfg (Fin 2) (Fin 4)} (h : run N a b) (g : run N b c) : run N a c := by
    obtain ⟨n, hn⟩ := h; obtain ⟨k, hk⟩ := g; exact ⟨_, joinSteps N hn hk⟩
  let config (q : Fin 4) (l : ListBlank (Fin 2)) (a : Fin 2) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 4) := ⟨q, ⟨a, l, r⟩⟩
  let rc (q : Fin 4) (l r : ListBlank (Fin 2)) := config q l r.head r.tail
  let lc (q : Fin 4) (l r : ListBlank (Fin 2)) := config q l.tail l.head r
  let w (n : ℕ) (t : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
    Nat.rec t (fun _ acc => acc.cons 1) n
  have w_zero (t : ListBlank (Fin 2)) : w 0 t = t := rfl
  have w_succ (n : ℕ) (t : ListBlank (Fin 2)) : w (n + 1) t = (w n t).cons 1 := rfl
  have w_cons (n : ℕ) (l : ListBlank (Fin 2)) : w n (l.cons 1) = (w n l).cons 1 := by
    induction n <;> simp [w_zero, w_succ, *]
  have w_add (m n : ℕ) (t : ListBlank (Fin 2)) : w m (w n t) = w (n+m) t := by
    induction m with | zero => rfl | succ m ih => rw [w_succ, ih, ← Nat.add_assoc, ← w_succ]
  let z : ListBlank (Fin 2) := ListBlank.mk []
  have hz : z.head = 0 := rfl
  have tz : z.tail = z := rfl
  have cz : z.cons 0 = z := by simpa only [hz, tz] using ListBlank.cons_head_tail z
  have right {N : Machine (Fin 2) (Fin 4)} {q q' : Fin 4} {a b : Fin 2} (l r : ListBlank (Fin 2))
      (h : N q a = some (some q', Stmt.write b Dir.right)) :
      N.step (config q l a r) = some (rc q' (l.cons b) r) := by
    simp [Machine.step, config, h, rc, Tape.move]
  have left {N : Machine (Fin 2) (Fin 4)} {q q' : Fin 4} {a b : Fin 2} (l r : ListBlank (Fin 2))
      (h : N q a = some (some q', Stmt.write b Dir.left)) :
      N.step (config q l a r) = some (lc q' l (r.cons b)) := by
    simp [Machine.step, config, h, lc, Tape.move]
  have rscan {N : Machine (Fin 2) (Fin 4)} {q : Fin 4} (h : N q 1 = some (some q, Stmt.write 1 Dir.right))
      (n : ℕ) (l r : ListBlank (Fin 2)) : run N (rc q l (w n r)) (rc q (w n l) r) := by
    induction n generalizing l with
    | zero => exact ⟨0, rfl⟩
    | succ n ih =>
      apply cat _ (show run N (rc q (l.cons 1) (w n r)) _ from by simpa only [w_cons, w_zero, w_succ] using ih (l.cons 1))
      refine ⟨1, ?_⟩
      simpa only [Machine.multiStep_one, rc, w_zero, w_succ, ListBlank.head_cons, ListBlank.tail_cons] using right l (w n r) h
  have lscan {N : Machine (Fin 2) (Fin 4)} {q : Fin 4} (h : N q 1 = some (some q, Stmt.write 1 Dir.left))
      (n : ℕ) (l r : ListBlank (Fin 2)) : run N (lc q (w n l) r) (lc q l (w n r)) := by
    induction n generalizing r with
    | zero => exact ⟨0, rfl⟩
    | succ n ih =>
      apply cat _ (show run N (lc q (w n l) (r.cons 1)) _ from by simpa only [w_cons, w_zero, w_succ] using ih (r.cons 1))
      refine ⟨1, ?_⟩
      simpa only [Machine.multiStep_one, lc, w_zero, w_succ, ListBlank.head_cons, ListBlank.tail_cons] using left (w n l) r h
  let advances (N : Machine (Fin 2) (Fin 4)) (a b : Cfg (Fin 2) (Fin 4)) := ∃ n, 0 < n ∧ N.multiStep a n = some b
  have starts {N : Machine (Fin 2) (Fin 4)} {a b c : Cfg (Fin 2) (Fin 4)} (h : N.step a = some b) (g : run N b c) : advances N a c := by
    obtain ⟨n, hn⟩ := g; exact ⟨1+n, by omega, joinSteps N (n := 1) h hn⟩
  have endless (N : Machine (Fin 2) (Fin 4)) (f : ℕ → ℕ → Cfg (Fin 2) (Fin 4)) (init : f 0 0 = Machine.init [])
      (adv : ∀ j k, ∃ x y, advances N (f j k) (f x y)) : ¬ N.IsHalting := by
    have reach (n : ℕ) : ∃ j k m, n ≤ m ∧ N.multiStep (Machine.init []) m = some (f j k) := by
      induction n with
      | zero => exact ⟨0, 0, 0, by omega, by simp [init]⟩
      | succ n ih =>
        obtain ⟨j, k, m, hm, h⟩ := ih
        obtain ⟨x, y, d, hd, g⟩ := adv j k
        exact ⟨x, y, m+d, by omega, joinSteps N h g⟩
    intro halts
    obtain ⟨n, hn⟩ := (Machine.isHalting_iff_exists_haltsAt N).mp halts
    obtain ⟨j, k, m, hm, h⟩ := reach (n+1)
    have none := Machine.multiStep_eq_none_mono hn hm
    rw [h] at none; contradiction
  have not_halt_sp0 : ¬ (tbl [6,3,3,8,15,10,16,1]).IsHalting := by
    let sp0 := tbl [6,3,3,8,15,10,16,1]
    let first (j k : ℕ) := config 0 (w j z) 0 (w (2*k) ((w j z).cons 0))
    apply endless sp0 first
    · simp only [first, Nat.mul_zero, w_zero, cz]; rfl
    · intro j k
      cases k with
      | zero =>
        refine ⟨1, j, ?_⟩
        have h0 : sp0.step (first j 0) = some (rc 1 (ListBlank.cons 1 (w j z)) (ListBlank.cons 0 (w j z))) := by
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right (w j z) (ListBlank.cons 0 (w j z)) (show sp0 0 0 = some (some 1, Stmt.write 1 Dir.right) from rfl)
        have h1 : run sp0 (rc 1 (ListBlank.cons 1 (w j z)) (ListBlank.cons 0 (w j z))) (lc 0 (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (w j z))) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using left (ListBlank.cons 1 (w j z)) (w j z) (show sp0 1 0 = some (some 0, Stmt.write 1 Dir.left) from rfl)
        have h2 : run sp0 (lc 0 (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (w j z))) (lc 0 z (ListBlank.cons 1 (w j (ListBlank.cons 1 (w j z))))) := by
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lscan (show sp0 0 1 = some (some 0, Stmt.write 1 Dir.left) from rfl) (j+1) z (ListBlank.cons 1 (w j z))
        have h3 : run sp0 (lc 0 z (ListBlank.cons 1 (w j (ListBlank.cons 1 (w j z))))) (rc 1 (ListBlank.cons 1 z) (ListBlank.cons 1 (w j (ListBlank.cons 1 (w j z))))) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right z (ListBlank.cons 1 (w j (ListBlank.cons 1 (w j z)))) (show sp0 0 0 = some (some 1, Stmt.write 1 Dir.right) from rfl)
        have h4 : run sp0 (rc 1 (ListBlank.cons 1 z) (ListBlank.cons 1 (w j (ListBlank.cons 1 (w j z))))) (rc 2 (ListBlank.cons 0 (ListBlank.cons 1 z)) (w j (ListBlank.cons 1 (w j z)))) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right (ListBlank.cons 1 z) (w j (ListBlank.cons 1 (w j z))) (show sp0 1 1 = some (some 2, Stmt.write 0 Dir.right) from rfl)
        have h5 : run sp0 (rc 2 (ListBlank.cons 0 (ListBlank.cons 1 z)) (w j (ListBlank.cons 1 (w j z)))) (rc 2 (w j (ListBlank.cons 0 (ListBlank.cons 1 z))) (ListBlank.cons 1 (w j z))) := by
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rscan (show sp0 2 1 = some (some 2, Stmt.write 1 Dir.right) from rfl) j (ListBlank.cons 0 (ListBlank.cons 1 z)) (ListBlank.cons 1 (w j z))
        have h6 : run sp0 (rc 2 (w j (ListBlank.cons 0 (ListBlank.cons 1 z))) (ListBlank.cons 1 (w j z))) (rc 2 (ListBlank.cons 1 (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) (w j z)) := by
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rscan (show sp0 2 1 = some (some 2, Stmt.write 1 Dir.right) from rfl) 1 (w j (ListBlank.cons 0 (ListBlank.cons 1 z))) (w j z)
        have h7 : run sp0 (rc 2 (ListBlank.cons 1 (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) (w j z)) (rc 2 (ListBlank.cons 1 (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z))))) z) := by
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rscan (show sp0 2 1 = some (some 2, Stmt.write 1 Dir.right) from rfl) j (ListBlank.cons 1 (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) z
        have h8 : run sp0 (rc 2 (ListBlank.cons 1 (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z))))) z) (lc 3 (ListBlank.cons 1 (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z))))) (ListBlank.cons 1 z)) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using left (ListBlank.cons 1 (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z))))) z (show sp0 2 0 = some (some 3, Stmt.write 1 Dir.left) from rfl)
        have h9 : run sp0 (lc 3 (ListBlank.cons 1 (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z))))) (ListBlank.cons 1 z)) (lc 0 (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) (ListBlank.cons 0 (ListBlank.cons 1 z))) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using left (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) (ListBlank.cons 1 z) (show sp0 3 1 = some (some 0, Stmt.write 0 Dir.left) from rfl)
        have h10 : run sp0 (lc 0 (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) (ListBlank.cons 0 (ListBlank.cons 1 z))) (lc 0 (w j (ListBlank.cons 0 (ListBlank.cons 1 z))) (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) := by
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lscan (show sp0 0 1 = some (some 0, Stmt.write 1 Dir.left) from rfl) j (w j (ListBlank.cons 0 (ListBlank.cons 1 z))) (ListBlank.cons 0 (ListBlank.cons 1 z))
        have h11 : run sp0 (lc 0 (w j (ListBlank.cons 0 (ListBlank.cons 1 z))) (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) (first 1 j) := by
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lscan (show sp0 0 1 = some (some 0, Stmt.write 1 Dir.left) from rfl) j (ListBlank.cons 0 (ListBlank.cons 1 z)) (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))
        exact starts h0 (cat h1 (cat h2 (cat h3 (cat h4 (cat h5 (cat h6 (cat h7 (cat h8 (cat h9 (cat h10 h11))))))))))
      | succ k =>
        refine ⟨j+1, k, ?_⟩
        have h0 : sp0.step (first j (k+1)) = some (rc 1 (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))))) := by
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right (w j z) (ListBlank.cons 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) (show sp0 0 0 = some (some 1, Stmt.write 1 Dir.right) from rfl)
        have h1 : run sp0 (rc 1 (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))))) (rc 2 (ListBlank.cons 0 (ListBlank.cons 1 (w j z))) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (show sp0 1 1 = some (some 2, Stmt.write 0 Dir.right) from rfl)
        have h2 : run sp0 (rc 2 (ListBlank.cons 0 (ListBlank.cons 1 (w j z))) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) (rc 2 (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (w (2*k) (ListBlank.cons 0 (w j z)))) := by
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rscan (show sp0 2 1 = some (some 2, Stmt.write 1 Dir.right) from rfl) 1 (ListBlank.cons 0 (ListBlank.cons 1 (w j z))) (w (2*k) (ListBlank.cons 0 (w j z)))
        have h3 : run sp0 (rc 2 (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (w (2*k) (ListBlank.cons 0 (w j z)))) (rc 2 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (ListBlank.cons 0 (w j z))) := by
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rscan (show sp0 2 1 = some (some 2, Stmt.write 1 Dir.right) from rfl) (2*k) (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (ListBlank.cons 0 (w j z))
        have h4 : run sp0 (rc 2 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (ListBlank.cons 0 (w j z))) (lc 3 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (ListBlank.cons 1 (w j z))) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using left (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (w j z) (show sp0 2 0 = some (some 3, Stmt.write 1 Dir.left) from rfl)
        have h5 : run sp0 (lc 3 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (ListBlank.cons 1 (w j z))) (lc 0 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using left (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (ListBlank.cons 1 (w j z)) (show sp0 3 1 = some (some 0, Stmt.write 0 Dir.left) from rfl)
        have h6 : run sp0 (lc 0 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (first (j+1) k) := by
          simpa only [first, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lscan (show sp0 0 1 = some (some 0, Stmt.write 1 Dir.left) from rfl) (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))
        exact starts h0 (cat h1 (cat h2 (cat h3 (cat h4 (cat h5 h6)))))
  have not_halt_sp1 : ¬ (tbl [6,4,11,6,16,13,2,15]).IsHalting := by
    let sp1 := tbl [6,4,11,6,16,13,2,15]
    let second (j k : ℕ) := rc 0 (w j z) (w (2*k) ((w j z).cons 0))
    apply endless sp1 second
    · rfl
    · intro j k
      cases k with
      | zero =>
        refine ⟨1, j, ?_⟩
        have h0 : sp1.step (second j 0) = some (rc 1 (ListBlank.cons 1 (w j z)) (w j z)) := by
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right (w j z) (w j z) (show sp1 0 0 = some (some 1, Stmt.write 1 Dir.right) from rfl)
        have h1 : run sp1 (rc 1 (ListBlank.cons 1 (w j z)) (w j z)) (rc 1 (ListBlank.cons 1 (w j (w j z))) z) := by
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rscan (show sp1 1 1 = some (some 1, Stmt.write 1 Dir.right) from rfl) j (ListBlank.cons 1 (w j z)) z
        have h2 : run sp1 (rc 1 (ListBlank.cons 1 (w j (w j z))) z) (lc 2 (ListBlank.cons 1 (w j (w j z))) (ListBlank.cons 1 z)) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using left (ListBlank.cons 1 (w j (w j z))) z (show sp1 1 0 = some (some 2, Stmt.write 1 Dir.left) from rfl)
        have h3 : run sp1 (lc 2 (ListBlank.cons 1 (w j (w j z))) (ListBlank.cons 1 z)) (lc 3 (w j (w j z)) (ListBlank.cons 0 (ListBlank.cons 1 z))) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using left (w j (w j z)) (ListBlank.cons 1 z) (show sp1 2 1 = some (some 3, Stmt.write 0 Dir.left) from rfl)
        have h4 : run sp1 (lc 3 (w j (w j z)) (ListBlank.cons 0 (ListBlank.cons 1 z))) (lc 3 (w j z) (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) := by
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lscan (show sp1 3 1 = some (some 3, Stmt.write 1 Dir.left) from rfl) j (w j z) (ListBlank.cons 0 (ListBlank.cons 1 z))
        have h5 : run sp1 (lc 3 (w j z) (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) (lc 3 z (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z))))) := by
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lscan (show sp1 3 1 = some (some 3, Stmt.write 1 Dir.left) from rfl) j z (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))
        have h6 : run sp1 (lc 3 z (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z))))) (second 1 j) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right z (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) (show sp1 3 0 = some (some 0, Stmt.write 1 Dir.right) from rfl)
        exact starts h0 (cat h1 (cat h2 (cat h3 (cat h4 (cat h5 h6)))))
      | succ k =>
        refine ⟨j+1, k, ?_⟩
        have h0 : sp1.step (second j (k+1)) = some (rc 1 (ListBlank.cons 0 (w j z)) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) := by
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right (w j z) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (show sp1 0 1 = some (some 1, Stmt.write 0 Dir.right) from rfl)
        have h1 : run sp1 (rc 1 (ListBlank.cons 0 (w j z)) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) (rc 1 (ListBlank.cons 1 (ListBlank.cons 0 (w j z))) (w (2*k) (ListBlank.cons 0 (w j z)))) := by
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rscan (show sp1 1 1 = some (some 1, Stmt.write 1 Dir.right) from rfl) 1 (ListBlank.cons 0 (w j z)) (w (2*k) (ListBlank.cons 0 (w j z)))
        have h2 : run sp1 (rc 1 (ListBlank.cons 1 (ListBlank.cons 0 (w j z))) (w (2*k) (ListBlank.cons 0 (w j z)))) (rc 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (ListBlank.cons 0 (w j z))) := by
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rscan (show sp1 1 1 = some (some 1, Stmt.write 1 Dir.right) from rfl) (2*k) (ListBlank.cons 1 (ListBlank.cons 0 (w j z))) (ListBlank.cons 0 (w j z))
        have h3 : run sp1 (rc 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (ListBlank.cons 0 (w j z))) (lc 2 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (ListBlank.cons 1 (w j z))) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using left (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (w j z) (show sp1 1 0 = some (some 2, Stmt.write 1 Dir.left) from rfl)
        have h4 : run sp1 (lc 2 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (ListBlank.cons 1 (w j z))) (lc 3 (w (2*k) (ListBlank.cons 0 (w j z))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using left (w (2*k) (ListBlank.cons 0 (w j z))) (ListBlank.cons 1 (w j z)) (show sp1 2 1 = some (some 3, Stmt.write 0 Dir.left) from rfl)
        have h5 : run sp1 (lc 3 (w (2*k) (ListBlank.cons 0 (w j z))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (lc 3 (ListBlank.cons 0 (w j z)) (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) := by
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lscan (show sp1 3 1 = some (some 3, Stmt.write 1 Dir.left) from rfl) (2*k) (ListBlank.cons 0 (w j z)) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))
        have h6 : run sp1 (lc 3 (ListBlank.cons 0 (w j z)) (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (second (j+1) k) := by
          refine ⟨1, ?_⟩; rw [Machine.multiStep_one]
          simpa only [second, rc, lc, Nat.mul_succ, Nat.add_succ, w_zero, w_succ, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right (w j z) (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (show sp1 3 0 = some (some 0, Stmt.write 1 Dir.right) from rfl)
        exact starts h0 (cat h1 (cat h2 (cat h3 (cat h4 (cat h5 h6)))))
  have hrun1 : M.multiStep (Machine.init []) 1 = some ⟨some 1, ⟨0, ListBlank.mk [1], ListBlank.mk []⟩⟩ := by
    rw [Machine.multiStep_one]
    simp [Machine.step, Machine.init, hFirst, Tape.write, Tape.move, Tape.mk₁, Tape.mk₂, Tape.mk']
  have hM10 : ∃ q' z, M 1 0 = some (some q', z) := by
    rcases hForm 1 0 with hnone | hsome
    · have h2s : M.multiStep (Machine.init []) 2 = none := by
        rw [Machine.multiStep_succ, hrun1]; simp [Machine.step, hnone]
      have h107 := Machine.multiStep_eq_none_mono h2s (by decide : 2 ≤ 107)
      obtain ⟨q0, t0, hr⟩ := hRun; rw [h107] at hr; contradiction
    · exact hsome
  obtain ⟨q', ⟨w0, d0⟩, hM10⟩ := hM10
  have hNeSp0Swap : M ≠ tbl [6,3,3,12,16,1,11,14] := by
    intro heq
    have hH := reindex23_isHalting M hHalts
    have hEq : reindex23 M = tbl [6,3,3,8,15,10,16,1] := by
      subst heq; funext q a; fin_cases q <;> fin_cases a <;>
        simp [reindex23, tbl, hswap0, hswap1, hswap2, hswap3]
    rw [hEq] at hH; exact not_halt_sp0 hH
  fin_cases q'
  · exact h1 M hFirst ⟨0, Or.inl rfl, _, hM10⟩ hRun hUsed hForm hMissing hLoop (hNe0 false) hNeSp0Swap hHalts
  · exact h1 M hFirst ⟨1, Or.inr rfl, _, hM10⟩ hRun hUsed hForm hMissing hLoop (hNe0 false) hNeSp0Swap hHalts
  · fin_cases w0
    · exact h2 M hFirst ⟨d0, hM10⟩ hRun hUsed hForm hMissing hLoop hHalts
    · cases d0 with
      | right => exact h3 M hFirst hM10 hRun hUsed hForm hMissing hLoop hHalts
      | left => exact h4 M hFirst hM10 hRun hUsed hForm hMissing hLoop (hNe0 true) hHalts
  · let M' := reindex23 M
    have hFirst' : M' 0 0 = some (some 1, Stmt.write 1 Dir.right) := by
      simp [M', reindex23, hswap0, hFirst, hswap1]
    have hM10' : M' 1 0 = some (some 2, Stmt.write w0 d0) := by
      simp [M', reindex23, hswap1, hM10, hswap3]
    have hRun' : ∃ q t, M'.multiStep (Machine.init []) 107 = some ⟨some q, t⟩ := by
      obtain ⟨q0, t0, hr⟩ := hRun
      refine ⟨swap23 q0, t0, ?_⟩; rw [← mapCfg23_init, reindex23_multi, hr]; rfl
    have hUsed' : ∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
        M'.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
        ∃ q' z, M' q a = some (some q', z) := by
      intro q a; constructor
      · rintro ⟨i, hi, t, ht, rfl⟩
        rw [← mapCfg23_init, reindex23_multi] at ht
        cases hMi : M.multiStep (Machine.init []) i with
        | none => simp [hMi] at ht
        | some c' =>
          simp only [hMi, Option.map_some, Option.some.injEq] at ht
          obtain ⟨q0, t0⟩ := c'
          cases q0 with
          | none => simp [mapCfg23] at ht
          | some q0 =>
            simp only [mapCfg23, Option.map_some, Cfg.mk.injEq, Option.some.injEq] at ht
            rcases ht with ⟨hq0, rfl⟩
            have hq0' : q0 = swap23 q := by rw [← hq0, hswap_inv]
            subst hq0'
            obtain ⟨r, z, hrz⟩ := (hUsed (swap23 q) t0.head).mp ⟨i, hi, t0, hMi, rfl⟩
            exact ⟨swap23 r, z, by simp [M', reindex23, hrz]⟩
      · rintro ⟨r, z, hrz⟩
        simp only [M', reindex23] at hrz
        cases hMqa : M (swap23 q) a with
        | none => simp [hMqa] at hrz
        | some entry =>
          rcases entry with ⟨s, z0⟩
          cases s with
          | none => simp [hMqa] at hrz
          | some s =>
            obtain ⟨i, hi, t, ht, ha⟩ := (hUsed (swap23 q) a).mpr ⟨s, z0, hMqa⟩
            refine ⟨i, hi, t, ?_, ha⟩
            rw [← mapCfg23_init, reindex23_multi, ht]; simp [mapCfg23, hswap_inv]
    have hForm' : ∀ q a, M' q a = none ∨ ∃ q' z, M' q a = some (some q', z) := by
      intro q a
      rcases hForm (swap23 q) a with h | ⟨r, z, h⟩
      · left; simp [M', reindex23, h]
      · right; exact ⟨swap23 r, z, by simp [M', reindex23, h]⟩
    have hMissing' : ∃ q a, M' q a = none := by
      obtain ⟨qm, am, hm⟩ := hMissing
      exact ⟨swap23 qm, am, by simp [M', reindex23, hswap_inv, hm]⟩
    have hLoop' : ∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
        (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
      let cfg := fun tail : ListBlank (Fin 2) =>
        let free := near.foldr ListBlank.cons tail
        (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
      (∃ tail, M'.multiStep (Machine.init []) i = some (cfg tail)) →
      ¬ ∀ tail, ∃ tail', M'.multiStep (cfg tail) p = some (cfg tail') := by
      intro i p q a side near fixed hp hle cfg hEnter hCycle
      let cfgM : ListBlank (Fin 2) → Cfg (Fin 2) (Fin 4) := fun tail =>
        let free := near.foldr ListBlank.cons tail
        ⟨some (swap23 q), if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩
      have hmap : ∀ tail, mapCfg23 (cfgM tail) = cfg tail := by
        intro tail; simp [mapCfg23, cfgM, cfg, hswap_inv]
      apply hLoop i p (swap23 q) a side near fixed hp hle
      · obtain ⟨tail, ht⟩ := hEnter
        rw [← mapCfg23_init, reindex23_multi] at ht
        cases hMi : M.multiStep (Machine.init []) i with
        | none => simp [hMi] at ht
        | some c' =>
          simp only [hMi, Option.map_some, Option.some.injEq] at ht
          refine ⟨tail, ?_⟩; congr 1
          obtain ⟨q0, t0⟩ := c'
          cases q0 with
          | none => simp [mapCfg23, cfg] at ht
          | some q0 =>
            simp only [mapCfg23, cfg, Option.map_some, Cfg.mk.injEq, Option.some.injEq] at ht
            rcases ht with ⟨hq0, ht0⟩
            have : q0 = swap23 q := by rw [← hq0, hswap_inv]
            simp [this, ht0]
      · intro tail
        obtain ⟨tail', ht'⟩ := hCycle tail
        rw [← hmap tail, reindex23_multi] at ht'
        cases hMp : M.multiStep (cfgM tail) p with
        | none => simp [hMp] at ht'
        | some c' =>
          simp only [hMp, Option.map_some, Option.some.injEq] at ht'
          refine ⟨tail', ?_⟩; congr 1
          obtain ⟨q0, t0⟩ := c'
          cases q0 with
          | none => simp [mapCfg23, cfg] at ht'
          | some q0 =>
            simp only [mapCfg23, cfg, Option.map_some, Cfg.mk.injEq, Option.some.injEq] at ht'
            rcases ht' with ⟨hq0, ht0⟩
            have : q0 = swap23 q := by rw [← hq0, hswap_inv]
            simp [this, ht0]
    have hHalts' : M'.IsHalting := reindex23_isHalting M hHalts
    fin_cases w0
    · exact h2 M' hFirst' ⟨d0, hM10'⟩ hRun' hUsed' hForm' hMissing' hLoop' hHalts'
    · cases d0 with
      | right => exact h3 M' hFirst' hM10' hRun' hUsed' hForm' hMissing' hLoop' hHalts'
      | left =>
        have hNeSp1' : M' ≠ tbl [6,4,11,6,16,13,2,15] := fun heq => not_halt_sp1 (heq ▸ hHalts')
        exact h4 M' hFirst' hM10' hRun' hUsed' hForm' hMissing' hLoop' hNeSp1' hHalts'

end OMA.R_BusyBeaver_BB_4_R2_H2_R1
