import FormalConjectures.OEIS.«251758»

-- Problem: OeisA251758.conjecture (least x with a(x) = 8 is p_12 primorial / p_4 primorial)
-- Upstream: FormalConjectures/OEIS/251758.lean
-- Credit: @ihateSAS (agent: Internal Model, model: Internal Model)
-- Method: S(x) = s(x)/x^2 is the consecutive-divisor reciprocal sum; a = 8 forces all divisors coprime
-- to 210; a branch and bound over the chain of smallest divisors, with a certified tail bound and
-- certified divisor lists from factorizations, rules out every x below 35336848261. The search runs
-- in the kernel (decide +kernel), split into 14 separately checked pieces; its soundness is proved.

namespace OMA_A251758

open OeisA251758

/-! Part A: the divisor list, consecutive sums, and the reformulation `S = s / n^2` -/

/-- The divisor list used in the definition of `a`. -/
def D (n : ℕ) : List ℕ := (List.range (n + 1)).filter (· ∣ n)

/-- Sum of products of consecutive entries. -/
def cp : List ℕ → ℕ
  | x :: y :: t => x * y + cp (y :: t)
  | _ => 0

theorem zip_cp : ∀ l : List ℕ,
    ((l.zip l.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)).sum = cp l
  | [] => rfl
  | [_] => rfl
  | x :: y :: t => by
      have ih := zip_cp (y :: t)
      simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]; rfl

theorem a_eq (n : ℕ) : a n = if cp (D n) = 0 then 0 else n ^ 2 / cp (D n) := by
  unfold a
  simp only [zip_cp]
  rfl

/-- Generic sum over consecutive pairs. -/
def pairSum (g : ℕ → ℕ → ℚ) : List ℕ → ℚ
  | x :: y :: t => g x y + pairSum g (y :: t)
  | _ => 0

@[simp] theorem pairSum_nil (g : ℕ → ℕ → ℚ) : pairSum g [] = 0 := rfl
@[simp] theorem pairSum_single (g : ℕ → ℕ → ℚ) (x : ℕ) : pairSum g [x] = 0 := rfl
@[simp] theorem pairSum_cc (g : ℕ → ℕ → ℚ) (x y : ℕ) (t : List ℕ) :
    pairSum g (x :: y :: t) = g x y + pairSum g (y :: t) := rfl

theorem cp_cast : ∀ l : List ℕ, (cp l : ℚ) = pairSum (fun a b => (a : ℚ) * b) l
  | [] => by simp [cp]
  | [_] => by simp [cp]
  | x :: y :: t => by
      have ih := cp_cast (y :: t)
      simp only [cp, Nat.cast_add, Nat.cast_mul, pairSum_cc] at ih ⊢
      rw [ih]

theorem pairSum_append (g : ℕ → ℕ → ℚ) : ∀ (l : List ℕ) (x : ℕ) (r : List ℕ),
    pairSum g (l ++ x :: r) = pairSum g (l ++ [x]) + pairSum g (x :: r)
  | [], x, r => by simp
  | [b], x, r => by simp
  | b :: c :: t, x, r => by
      have ih := pairSum_append g (c :: t) x r
      simp only [List.cons_append, pairSum_cc] at ih ⊢
      rw [ih]; ring

theorem pairSum_concat2 (g : ℕ → ℕ → ℚ) (l : List ℕ) (y x : ℕ) :
    pairSum g (l ++ [y, x]) = pairSum g (l ++ [y]) + g y x := by
  have h := pairSum_append g l y [x]
  simpa using h

theorem pairSum_reverse (g : ℕ → ℕ → ℚ) (hg : ∀ a b, g a b = g b a) :
    ∀ l : List ℕ, pairSum g l.reverse = pairSum g l
  | [] => rfl
  | [_] => rfl
  | x :: y :: t => by
      have ih := pairSum_reverse g hg (y :: t)
      have e1 : (x :: y :: t).reverse = t.reverse ++ [y, x] := by simp
      have e2 : (y :: t).reverse = t.reverse ++ [y] := by simp
      rw [e1, pairSum_concat2, ← e2, ih, pairSum_cc, hg]
      ring

theorem pairSum_map (g : ℕ → ℕ → ℚ) (f : ℕ → ℕ) :
    ∀ l : List ℕ, pairSum g (l.map f) = pairSum (fun a b => g (f a) (f b)) l
  | [] => rfl
  | [_] => rfl
  | x :: y :: t => by
      have ih := pairSum_map g f (y :: t)
      simp only [List.map_cons, pairSum_cc] at ih ⊢
      rw [ih]

theorem pairSum_congr (g h : ℕ → ℕ → ℚ) :
    ∀ l : List ℕ, (∀ a ∈ l, ∀ b ∈ l, g a b = h a b) → pairSum g l = pairSum h l
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: t, H => by
      simp only [pairSum_cc]
      rw [H x (by simp) y (by simp),
        pairSum_congr g h (y :: t) (fun a ha b hb =>
          H a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))]

theorem pairSum_mul (c : ℚ) (g : ℕ → ℕ → ℚ) :
    ∀ l : List ℕ, pairSum (fun a b => c * g a b) l = c * pairSum g l
  | [] => by simp
  | [_] => by simp
  | x :: y :: t => by
      have ih := pairSum_mul c g (y :: t)
      simp only [pairSum_cc] at ih ⊢
      rw [ih]; ring

/-- `S(l) = sum of 1/(u v)` over consecutive pairs. -/
def Tsum (l : List ℕ) : ℚ := pairSum (fun a b => 1 / ((a : ℚ) * b)) l

theorem Tsum_nonneg : ∀ l : List ℕ, 0 ≤ Tsum l
  | [] => by simp [Tsum]
  | [_] => by simp [Tsum]
  | x :: y :: t => by
      have ih := Tsum_nonneg (y :: t)
      unfold Tsum at ih ⊢
      rw [pairSum_cc]
      have : (0 : ℚ) ≤ 1 / ((x : ℚ) * y) := by positivity
      linarith

theorem mem_D {n d : ℕ} (hn : 0 < n) : d ∈ D n ↔ d ∣ n := by
  simp only [D, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hn h), h⟩

theorem D_sorted (n : ℕ) : (D n).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem D_map_div (n : ℕ) (hn : 0 < n) : (D n).map (n / ·) = (D n).reverse := by
  have hs := D_sorted n
  have h1 : ((D n).map (n / ·)).Pairwise (· > ·) := by
    rw [List.pairwise_map]
    refine hs.imp_of_mem ?_
    intro a b ha hb hab
    have ha' := (mem_D hn).1 ha
    have hb' := (mem_D hn).1 hb
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha' hn
    obtain ⟨j, hj⟩ := ha'
    obtain ⟨k, hk⟩ := hb'
    have hb0 : 0 < b := by omega
    show n / b < n / a
    have e1 : n / a = j := by rw [hj, Nat.mul_div_cancel_left _ ha0]
    have e2 : n / b = k := by rw [hk, Nat.mul_div_cancel_left _ hb0]
    rw [e1, e2]
    by_contra hc
    push Not at hc
    have : a * j < b * k := by
      calc a * j < b * j := by
            apply Nat.mul_lt_mul_of_pos_right hab
            rcases Nat.eq_zero_or_pos j with h0 | h0
            · subst h0; omega
            · exact h0
        _ ≤ b * k := Nat.mul_le_mul_left _ hc
    omega
  have h2 : (D n).reverse.Pairwise (· > ·) := List.pairwise_reverse.2 hs
  have hp : ((D n).map (n / ·)).Perm (D n).reverse := by
    rw [List.perm_ext_iff_of_nodup h1.nodup h2.nodup]
    intro e
    simp only [List.mem_map, List.mem_reverse, mem_D hn]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact Nat.div_dvd_of_dvd hd
    · intro he
      exact ⟨n / e, Nat.div_dvd_of_dvd he, Nat.div_div_self he hn.ne'⟩
  exact List.Perm.eq_of_pairwise' (r := fun a b : ℕ => a ≥ b) (h1.imp le_of_lt) (h2.imp le_of_lt) hp

theorem cp_D_eq (n : ℕ) (hn : 0 < n) : (cp (D n) : ℚ) = (n : ℚ) ^ 2 * Tsum (D n) := by
  have hsym : ∀ a b : ℕ, (fun a b : ℕ => (a : ℚ) * b) a b = (fun a b : ℕ => (a : ℚ) * b) b a :=
    fun a b => mul_comm _ _
  calc (cp (D n) : ℚ) = pairSum (fun a b => (a : ℚ) * b) (D n) := cp_cast _
    _ = pairSum (fun a b => (a : ℚ) * b) (D n).reverse := (pairSum_reverse _ hsym _).symm
    _ = pairSum (fun a b => (a : ℚ) * b) ((D n).map (n / ·)) := by rw [D_map_div n hn]
    _ = pairSum (fun a b => ((n / a : ℕ) : ℚ) * ((n / b : ℕ) : ℚ)) (D n) := pairSum_map _ _ _
    _ = pairSum (fun a b => (n : ℚ) ^ 2 * (1 / ((a : ℚ) * b))) (D n) := by
        apply pairSum_congr
        intro a ha b hb
        have ha' := (mem_D hn).1 ha
        have hb' := (mem_D hn).1 hb
        have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_dvd_of_pos ha' hn).ne'
        have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_dvd_of_pos hb' hn).ne'
        rw [Nat.cast_div ha' ha0, Nat.cast_div hb' hb0]
        field_simp
    _ = (n : ℚ) ^ 2 * Tsum (D n) := pairSum_mul _ _ _

theorem bridge {n : ℕ} (hn : 2 ≤ n) (h : a n = 8) :
    1 / 9 < Tsum (D n) ∧ Tsum (D n) ≤ 1 / 8 := by
  rw [a_eq] at h
  split_ifs at h with h0
  have hpos : 0 < cp (D n) := Nat.pos_of_ne_zero h0
  have h1 : 8 * cp (D n) ≤ n ^ 2 := by
    have := Nat.div_mul_le_self (n ^ 2) (cp (D n))
    rw [h] at this
    linarith
  have h2 : n ^ 2 < 9 * cp (D n) := by
    have := Nat.lt_div_mul_add (a := n ^ 2) hpos
    rw [h] at this
    linarith
  have hq := cp_D_eq n (by omega)
  have hn2 : (0 : ℚ) < (n : ℚ) ^ 2 := by
    have : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  have e1 : (8 : ℚ) * (cp (D n) : ℚ) ≤ (n : ℚ) ^ 2 := by exact_mod_cast h1
  have e2 : (n : ℚ) ^ 2 < 9 * (cp (D n) : ℚ) := by exact_mod_cast h2
  rw [hq] at e1 e2
  constructor <;> nlinarith

theorem D_head {n : ℕ} (hn : 2 ≤ n) : ∃ q rest, D n = 1 :: q :: rest := by
  have hs := D_sorted n
  have h1 : 1 ∈ D n := (mem_D (by omega)).2 (one_dvd n)
  have hnn : n ∈ D n := (mem_D (by omega)).2 dvd_rfl
  match hD : D n with
  | [] => rw [hD] at h1; simp at h1
  | [h] =>
      rw [hD] at h1 hnn
      simp at h1 hnn
      omega
  | h :: q :: rest =>
      refine ⟨q, rest, ?_⟩
      rw [hD] at h1 hs
      have hh : h = 1 := by
        rcases List.mem_cons.1 h1 with h1 | h1
        · exact h1.symm
        · have hlt := List.rel_of_pairwise_cons hs h1
          have h0 : h ∈ D n := by rw [hD]; simp
          have : h = 0 := by omega
          subst this
          have := (mem_D (by omega)).1 h0
          simp at this
          omega
      rw [hh]

/-- Membership in `A`: coprime to `210`. -/
def inA (d : ℕ) : Bool := !Nat.beq (d % 2) 0 && !Nat.beq (d % 3) 0 &&
  !Nat.beq (d % 5) 0 && !Nat.beq (d % 7) 0

theorem nbeq (a b : ℕ) : ((!Nat.beq a b) = true) ↔ a ≠ b := by
  cases h : Nat.beq a b
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

theorem beqT (a b : ℕ) : (Nat.beq a b = true) ↔ a = b := by simp [Nat.beq_eq]

theorem beqD (a b : ℕ) : Nat.beq a b = decide (a = b) := Bool.eq_iff_iff.2 (by simp [Nat.beq_eq])

theorem bleD (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := Bool.eq_iff_iff.2 (by simp [Nat.ble_eq])

theorem bltD (a b : ℕ) : Nat.blt a b = decide (a < b) := Bool.eq_iff_iff.2 (by simp [Nat.blt_eq])

theorem inA_spec (d : ℕ) : inA d = true ↔ d % 2 ≠ 0 ∧ d % 3 ≠ 0 ∧ d % 5 ≠ 0 ∧ d % 7 ≠ 0 := by
  simp only [inA, Bool.and_eq_true, nbeq, and_assoc]

theorem all_inA {n : ℕ} (hn : 2 ≤ n) (hT : Tsum (D n) ≤ 1 / 8) :
    ∀ d, d ∣ n → inA d = true := by
  obtain ⟨q, rest, hD⟩ := D_head hn
  have hq : q ∣ n := (mem_D (by omega)).1 (by rw [hD]; simp)
  have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hq (by omega)
  have hTq : 1 / (q : ℚ) ≤ Tsum (D n) := by
    have := Tsum_nonneg (q :: rest)
    rw [hD]
    unfold Tsum at this ⊢
    rw [pairSum_cc]
    simp only [Nat.cast_one, one_mul]
    linarith
  have hq8 : 8 ≤ q := by
    by_contra hlt
    push Not at hlt
    have : (1 : ℚ) / 8 < 1 / q := by
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
      have : (q : ℚ) < 8 := by exact_mod_cast hlt
      linarith
    linarith
  have hsort := D_sorted n
  rw [hD] at hsort
  have key : ∀ p, p ∣ n → 1 < p → 8 ≤ p := by
    intro p hp hp1
    have hm : p ∈ D n := (mem_D (by omega)).2 hp
    rw [hD] at hm
    rcases List.mem_cons.1 hm with h | h
    · omega
    · rcases List.mem_cons.1 h with h | h
      · omega
      · have := List.rel_of_pairwise_cons (List.Pairwise.of_cons hsort) h
        omega
  intro d hd
  have h2 : ¬ 2 ∣ d := fun h => by have := key 2 (h.trans hd) (by norm_num); omega
  have h3 : ¬ 3 ∣ d := fun h => by have := key 3 (h.trans hd) (by norm_num); omega
  have h5 : ¬ 5 ∣ d := fun h => by have := key 5 (h.trans hd) (by norm_num); omega
  have h7 : ¬ 7 ∣ d := fun h => by have := key 7 (h.trans hd) (by norm_num); omega
  rw [inA_spec]
  omega


def gap (b : ℕ) : ℕ :=
  if inA (b + 1) then 1 else if inA (b + 2) then 2 else if inA (b + 3) then 3 else
  if inA (b + 4) then 4 else if inA (b + 5) then 5 else if inA (b + 6) then 6 else
  if inA (b + 7) then 7 else if inA (b + 8) then 8 else if inA (b + 9) then 9 else
  if inA (b + 10) then 10 else 11

def B : ℕ := 35336848261
def SC : ℕ := 10 ^ 30
def NN : ℕ := 2000

def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

def nsum (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => nsum g n + g n

def F1 : ℕ := nsum (fun b => if 1 ≤ b ∧ inA b = true then cdiv SC (b * (b + gap b)) else 0) NN
  + cdiv SC (2 * NN)

def PL : List ℕ := [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
  89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
  191, 193, 197, 199]

/-- Strict binding: forces `n` to a numeral before continuing. -/
def force {α : Type} (n : ℕ) (k : ℕ → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

def mult (p : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, n => (0, n)
  | f + 1, n => if Nat.beq (n % p) 0 then
      (match mult p f (n / p) with | (e, m) => (e + 1, m)) else (0, n)

def factorAux : List ℕ → ℕ → List (ℕ × ℕ) × ℕ
  | [], n => ([], n)
  | p :: ps, n =>
      match mult p 40 n with
      | (e, m) => force m fun m' => match factorAux ps m' with
        | (fs, rest) => (if Nat.beq e 0 then fs else (p, e) :: fs, rest)

def gen : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | (p, e) :: r => (List.range (e + 1)).flatMap
      (fun k => (gen r).map (fun d => p ^ k * d))

def prodF : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e) :: r => p ^ e * prodF r

def memB (p : ℕ) : List ℕ → Bool
  | [] => false
  | q :: t => Nat.beq p q || memB p t

def okF : List (ℕ × ℕ) → Bool
  | [] => true
  | (p, _) :: r => memB p PL && Nat.beq (Nat.gcd p (prodF r)) 1 && okF r

def merge : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | f + 1, x :: xs, y :: ys =>
      if Nat.ble x y then x :: merge f xs (y :: ys) else y :: merge f (x :: xs) ys

def split : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | a :: t => match split t with | (x, y) => (a :: y, x)

def msort : ℕ → List ℕ → List ℕ
  | 0, l => l
  | f + 1, l => match l with
    | [] => []
    | [a] => [a]
    | a :: b :: t => match split (a :: b :: t) with
      | (x, y) => merge (t.length + 3) (msort f x) (msort f y)

def strictSorted : List ℕ → Bool
  | a :: b :: t => Nat.blt a b && strictSorted (b :: t)
  | _ => true

def cpN : List ℕ → ℕ
  | x :: y :: t => x * y + cpN (y :: t)
  | _ => 0

def finChk (L : ℕ) (S : List ℕ) : Bool :=
  strictSorted S && force (cpN S) fun s => Nat.beq s 0 || !Nat.beq (L * L / s) 8

def finalize (L : ℕ) : Bool :=
  match factorAux PL L with
  | (fs, _) => okF fs && Nat.beq (prodF fs) L && finChk L (msort 20 (gen fs))

def minAbove (u : ℕ) : List ℕ → ℕ → ℕ
  | [], m => m
  | d :: t, m => minAbove u t (if Nat.blt u d && (Nat.beq m 0 || Nat.blt d m) then d else m)

def nextDiv (L u : ℕ) : ℕ :=
  match factorAux PL L with
  | (fs, r) => if Nat.beq r 1 then minAbove u (gen fs) 0 else 0

inductive Task
  | node (u Fu L sup slo : ℕ)
  | cand (u L sup slo w v Fv : ℕ)

/-- Equality test for `node` tasks (used for the memo list). -/
def taskEq : Task → Task → Bool
  | .node a b c d e, .node a' b' c' d' e' =>
      Nat.beq a a' && Nat.beq b b' && Nat.beq c c' && Nat.beq d d' && Nat.beq e e'
  | _, _ => false

def memT (t : Task) : List Task → Bool
  | [] => false
  | s :: r => taskEq t s || memT t r

/-- The checker. Node tasks in the memo list `M` are accepted at once; they are checked
separately (see `memo_ok`), which keeps every single kernel computation small. -/
def run (M : List Task) : ℕ → Task → Bool
  | 0, _ => false
  | n + 1, .node u Fu L sup slo =>
      if memT (.node u Fu L sup slo) M then true
      else if Nat.ble B (11 * L) then finalize L
      else if Nat.beq u L && !(Nat.ble (9 * sup) SC || Nat.blt SC (8 * slo)) then false
      else force (nextDiv L u) fun w =>
      if !Nat.beq w 0 && !(Nat.beq (L % w) 0 && Nat.blt u w) then false
      else force (u + gap u) fun v =>
      if inA v then
        force (Fu - SC / (u * v)) fun Fv => run M n (.cand u L sup slo w v Fv)
      else false
  | n + 1, .cand u L sup slo w v Fv =>
      if !Nat.beq w 0 && Nat.blt w v then true
      else force (cdiv SC (u * v)) fun t =>
      if Nat.ble (9 * (sup + t + Fv)) SC then true
      else
        (force (Nat.lcm L v) fun L2 => Nat.ble B L2 ||
          force (sup + t) fun sup2 => force (slo + SC / (u * v)) fun slo2 =>
            run M n (.node v Fv L2 sup2 slo2)) &&
        (force (v + gap v) fun vn => inA vn &&
          force (Fv - SC / (v * vn)) fun Fvn => run M n (.cand u L sup slo w vn Fvn))

/- Part B: gaps, the tail bound, rounding -/

theorem inA_odd {d : ℕ} (h : inA d = true) : d % 2 = 1 := by
  rw [inA_spec] at h
  omega

theorem inA_ge {k : ℕ} (h : inA k = true) (h2 : 2 ≤ k) : 11 ≤ k := by
  by_contra hc
  push Not at hc
  interval_cases k <;> simp [inA_spec] at h

theorem gap_pos (b : ℕ) : 1 ≤ gap b := by
  unfold gap
  split_ifs <;> omega

theorem gap_spec {u u' : ℕ} (h : inA u' = true) (hlt : u < u') : u + gap u ≤ u' := by
  by_contra hc
  obtain ⟨k, hk1, hk2, rfl⟩ : ∃ k, 1 ≤ k ∧ k < gap u ∧ u' = u + k :=
    ⟨u' - u, by omega, by omega, by omega⟩
  unfold gap at hk2
  split_ifs at hk2 <;> (interval_cases k <;> simp_all)

/-- The per-element tail term `1 / (b * b⁺)`. -/
noncomputable def fT (b : ℕ) : ℚ :=
  if inA b = true then 1 / ((b : ℚ) * ((b + gap b : ℕ) : ℚ)) else 0

theorem fT_nonneg (b : ℕ) : 0 ≤ fT b := by
  unfold fT
  split_ifs
  · positivity
  · exact le_rfl

/-- The tail bound `Tq v`, an upper bound for the consecutive sum of any
increasing chain in `A` starting at `v`. -/
noncomputable def Tq (v : ℕ) : ℚ :=
  (∑ b ∈ Finset.range NN, if v ≤ b then fT b else 0) + 1 / (2 * ((max v NN : ℕ) : ℚ))

theorem maxNN_pos (v : ℕ) : (0 : ℚ) < ((max v NN : ℕ) : ℚ) := by
  have : 0 < max v NN := lt_of_lt_of_le (by unfold NN; norm_num) (le_max_right _ _)
  exact_mod_cast this

theorem Tq_nonneg (v : ℕ) : 0 ≤ Tq v := by
  unfold Tq
  have h1 : 0 ≤ ∑ b ∈ Finset.range NN, (if v ≤ b then fT b else 0) := by
    apply Finset.sum_nonneg
    intro b _
    split_ifs
    · exact fT_nonneg b
    · exact le_rfl
  have h2 : (0 : ℚ) ≤ 1 / (2 * ((max v NN : ℕ) : ℚ)) := by
    have := maxNN_pos v
    exact (one_div_pos.2 (by linarith)).le
  linarith

theorem Tq_step {u u' : ℕ} (hu : inA u = true) (hu' : inA u' = true) (hlt : u < u') :
    1 / ((u : ℚ) * u') + Tq u' ≤ Tq u := by
  have hu1 : 1 ≤ u := by have := inA_odd hu; omega
  have hgs := gap_spec hu' hlt
  have hupos : (0 : ℚ) < u := by exact_mod_cast hu1
  have hu'pos : (0 : ℚ) < u' := by exact_mod_cast (by omega : 0 < u')
  unfold Tq
  by_cases hN : u < NN
  · have hmem : u ∈ Finset.range NN := Finset.mem_range.2 hN
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
    have e1 : (if u' ≤ u then fT u else 0) = 0 := by rw [if_neg (by omega)]
    have e2 : (if u ≤ u then fT u else 0) = fT u := by rw [if_pos le_rfl]
    rw [e1, e2]
    have hsum : ∑ b ∈ (Finset.range NN).erase u, (if u' ≤ b then fT b else 0) ≤
        ∑ b ∈ (Finset.range NN).erase u, (if u ≤ b then fT b else 0) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : u' ≤ b
      · rw [if_pos hb, if_pos (by omega)]
      · rw [if_neg hb]
        split_ifs
        · exact fT_nonneg b
        · exact le_rfl
    have hfu : 1 / ((u : ℚ) * u') ≤ fT u := by
      unfold fT
      rw [if_pos hu]
      apply one_div_le_one_div_of_le
      · exact mul_pos hupos (by exact_mod_cast (by omega : 0 < u + gap u))
      · apply mul_le_mul_of_nonneg_left _ hupos.le
        exact_mod_cast hgs
    have hmax : 1 / (2 * ((max u' NN : ℕ) : ℚ)) ≤ 1 / (2 * ((max u NN : ℕ) : ℚ)) := by
      apply one_div_le_one_div_of_le
      · have := maxNN_pos u
        linarith
      · have : max u NN ≤ max u' NN := by omega
        have : ((max u NN : ℕ) : ℚ) ≤ ((max u' NN : ℕ) : ℚ) := by exact_mod_cast this
        linarith
    linarith
  · push Not at hN
    have z1 : ∑ b ∈ Finset.range NN, (if u ≤ b then fT b else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [if_neg (by have := Finset.mem_range.1 hb; omega)]
    have z2 : ∑ b ∈ Finset.range NN, (if u' ≤ b then fT b else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [if_neg (by have := Finset.mem_range.1 hb; omega)]
    rw [z1, z2, Nat.max_eq_left hN, Nat.max_eq_left (by omega)]
    have h2 : u + 2 ≤ u' := by
      have := inA_odd hu
      have := inA_odd hu'
      omega
    have h2q : (u : ℚ) + 2 ≤ u' := by exact_mod_cast h2
    rw [zero_add, zero_add, div_add_div _ _ (mul_pos hupos hu'pos).ne'
      (mul_pos two_pos hu'pos).ne',
      div_le_div_iff₀ (mul_pos (mul_pos hupos hu'pos) (mul_pos two_pos hu'pos))
        (mul_pos two_pos hupos)]
    nlinarith [mul_pos hupos hu'pos, mul_le_mul_of_nonneg_left h2q (mul_pos hupos hu'pos).le]

theorem Tq_mono {v v' : ℕ} (hv : inA v = true) (hv' : inA v' = true) (hle : v ≤ v') :
    Tq v' ≤ Tq v := by
  rcases hle.lt_or_eq with hlt | heq
  · have := Tq_step hv hv' hlt
    have hp : (0 : ℚ) ≤ 1 / ((v : ℚ) * v') := by positivity
    linarith
  · rw [heq]

theorem tail_le : ∀ (r : List ℕ) (v : ℕ), (v :: r).Pairwise (· < ·) →
    (∀ d ∈ v :: r, inA d = true) → Tsum (v :: r) ≤ Tq v
  | [], v, _, _ => by
      have := Tq_nonneg v
      simpa [Tsum] using this
  | w :: r, v, hp, hA => by
      have hvw : v < w := List.rel_of_pairwise_cons hp (by simp)
      have ih := tail_le r w (List.Pairwise.of_cons hp)
        (fun d hd => hA d (List.mem_cons_of_mem _ hd))
      have hst := Tq_step (hA v (by simp)) (hA w (by simp)) hvw
      have e : Tsum (v :: w :: r) = 1 / ((v : ℚ) * w) + Tsum (w :: r) := by
        unfold Tsum
        rw [pairSum_cc]
      rw [e]
      linarith

theorem le_cdiv (a b : ℕ) (hb : 0 < b) : (a : ℚ) / b ≤ (cdiv a b : ℚ) := by
  have hn : a ≤ cdiv a b * b := by
    unfold cdiv
    have h1 := Nat.div_add_mod (a + b - 1) b
    have h2 := Nat.mod_lt (a + b - 1) hb
    have h3 : b * ((a + b - 1) / b) = (a + b - 1) / b * b := Nat.mul_comm _ _
    generalize b * ((a + b - 1) / b) = X at h1 h3
    generalize (a + b - 1) / b * b = Y at h3 ⊢
    omega
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast hn

theorem cast_sub_ge (a b : ℕ) : (a : ℚ) - b ≤ ((a - b : ℕ) : ℚ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]
    have : (a : ℚ) ≤ b := by exact_mod_cast h
    simp only [Nat.cast_zero]
    linarith

theorem sc_term (u v : ℕ) : (SC : ℚ) * (1 / ((u : ℚ) * v)) = (SC : ℚ) / ((u * v : ℕ) : ℚ) := by
  push_cast
  ring

/-- Step for the fixed-point tail: `SC * Tq v ≤ Fu - floor(SC/(u v))`. -/
theorem F_step {u v Fu : ℕ} (hu : inA u = true) (hv : inA v = true) (hlt : u < v)
    (hF : (SC : ℚ) * Tq u ≤ Fu) : (SC : ℚ) * Tq v ≤ ((Fu - SC / (u * v) : ℕ) : ℚ) := by
  have hst := Tq_step hu hv hlt
  have hfl : ((SC / (u * v) : ℕ) : ℚ) ≤ (SC : ℚ) / ((u * v : ℕ) : ℚ) := Nat.cast_div_le
  have := cast_sub_ge Fu (SC / (u * v))
  have hSC : (0 : ℚ) ≤ SC := by positivity
  have hm : (SC : ℚ) * (1 / ((u : ℚ) * v) + Tq v) ≤ SC * Tq u :=
    mul_le_mul_of_nonneg_left hst hSC
  rw [mul_add, sc_term] at hm
  linarith

/- Part C: divisor lists from factorizations -/

theorem PL_prime : ∀ p ∈ PL, p.Prime := by
  intro p hp
  simp only [PL, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  norm_num

theorem memB_iff (p : ℕ) : ∀ l : List ℕ, memB p l = true ↔ p ∈ l
  | [] => by simp [memB]
  | q :: t => by simp [memB, beqT, memB_iff p t]

theorem dvd_of_mem_gen : ∀ (fs : List (ℕ × ℕ)) (d : ℕ), d ∈ gen fs → d ∣ prodF fs
  | [], d, h => by simp [gen] at h; simp [h, prodF]
  | (p, e) :: r, d, h => by
      simp only [gen, List.mem_flatMap, List.mem_range, List.mem_map] at h
      obtain ⟨k, hk, d', hd', rfl⟩ := h
      exact mul_dvd_mul (pow_dvd_pow p (by omega)) (dvd_of_mem_gen r d' hd')

theorem mem_gen_of_dvd : ∀ (fs : List (ℕ × ℕ)) (d : ℕ), okF fs = true → d ∣ prodF fs →
    d ∈ gen fs
  | [], d, _, h => by simp [prodF] at h; simp [gen, h]
  | (p, e) :: r, d, hok, h => by
      simp only [okF, Bool.and_eq_true, beqT, memB_iff] at hok
      obtain ⟨⟨hpL, hg⟩, hok⟩ := hok
      have hp := PL_prime p hpL
      have hco : Nat.Coprime (p ^ e) (prodF r) := Nat.Coprime.pow_left e hg
      simp only [prodF] at h
      have hd : d = Nat.gcd d (p ^ e) * Nat.gcd d (prodF r) := by
        rw [← Nat.Coprime.gcd_mul d hco, Nat.gcd_eq_left h]
      obtain ⟨k, hk, hke⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right d (p ^ e))
      have hm := mem_gen_of_dvd r (Nat.gcd d (prodF r)) hok (Nat.gcd_dvd_right _ _)
      simp only [gen, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨k, by omega, _, hm, by rw [← hke]; exact hd.symm⟩

theorem merge_perm : ∀ (f : ℕ) (xs ys : List ℕ), (merge f xs ys).Perm (xs ++ ys)
  | 0, xs, ys => by simp [merge]
  | _ + 1, [], ys => by simp [merge]
  | _ + 1, x :: xs, [] => by simp [merge]
  | f + 1, x :: xs, y :: ys => by
      simp only [merge]
      split_ifs
      · exact (merge_perm f xs (y :: ys)).cons x
      · refine ((merge_perm f (x :: xs) ys).cons y).trans ?_
        exact List.perm_middle.symm

theorem force_eq {α : Type} (n : ℕ) (k : ℕ → α) : force n k = k n := by
  cases n <;> rfl

theorem split_perm : ∀ l : List ℕ, ((split l).1 ++ (split l).2).Perm l
  | [] => by simp [split]
  | a :: t => by
      have ih := split_perm t
      rcases h : split t with ⟨x, y⟩
      simp only [h] at ih
      simp only [split, h, List.cons_append]
      exact (List.perm_append_comm.trans ih).cons a

theorem msort_perm : ∀ (f : ℕ) (l : List ℕ), (msort f l).Perm l
  | 0, l => by simp [msort]
  | _ + 1, [] => by simp [msort]
  | _ + 1, [a] => by simp [msort]
  | f + 1, a :: b :: t => by
      have hs := split_perm (a :: b :: t)
      simp only [msort]
      rcases h : split (a :: b :: t) with ⟨x, y⟩
      simp only [h] at hs ⊢
      exact (merge_perm _ _ _).trans (((msort_perm f x).append (msort_perm f y)).trans hs)

theorem strictSorted_sound : ∀ l : List ℕ, strictSorted l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: t, h => by
      simp only [strictSorted, Bool.and_eq_true, Nat.blt_eq] at h
      have ih := strictSorted_sound (b :: t) h.2
      refine List.Pairwise.cons ?_ ih
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h.1
      · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

theorem D_eq_of {L : ℕ} {S : List ℕ} (hL : 0 < L) (hS : S.Pairwise (· < ·))
    (hm : ∀ d, d ∈ S ↔ d ∣ L) : D L = S := by
  have hp : (D L).Perm S := by
    rw [List.perm_ext_iff_of_nodup (D_sorted L).nodup hS.nodup]
    intro d
    rw [mem_D hL, hm]
  exact List.Perm.eq_of_pairwise' (r := fun a b : ℕ => a ≤ b)
    ((D_sorted L).imp le_of_lt) (hS.imp le_of_lt) hp

theorem D_eq_gen {fs : List (ℕ × ℕ)} (hok : okF fs = true)
    (hs : strictSorted (msort 20 (gen fs)) = true) (hL : 0 < prodF fs) :
    D (prodF fs) = msort 20 (gen fs) := by
  apply D_eq_of hL (strictSorted_sound _ hs)
  intro d
  rw [(msort_perm 20 (gen fs)).mem_iff]
  exact ⟨dvd_of_mem_gen fs d, mem_gen_of_dvd fs d hok⟩

theorem cpN_eq : ∀ l : List ℕ, cpN l = cp l
  | [] => rfl
  | [_] => rfl
  | x :: y :: t => by simp only [cpN, cp, cpN_eq (y :: t)]

theorem finalize_sound {L : ℕ} (hL : 0 < L) (h : finalize L = true) : a L ≠ 8 := by
  unfold finalize at h
  rcases hf : factorAux PL L with ⟨fs, rest⟩
  rw [hf] at h
  simp only [finChk, force_eq, Bool.and_eq_true, beqT, Bool.or_eq_true, nbeq] at h
  obtain ⟨⟨hok, hprod⟩, hs, hfin⟩ := h
  have hD := D_eq_gen hok hs (by rw [hprod]; exact hL)
  rw [hprod] at hD
  rw [a_eq, hD, ← cpN_eq]
  rcases hfin with h0 | h8
  · rw [if_pos h0]; omega
  · split_ifs
    · omega
    · rw [pow_two]; exact h8

/- Part D: soundness of the branch and bound checker -/

/-- Invariant of a `node` task for a putative counterexample `x`. -/
def Inv (x : ℕ) : Task → Prop
  | .node u Fu L sup slo => ∃ c rest, D x = c ++ u :: rest ∧ u ∣ L ∧ L ∣ x ∧
      (SC : ℚ) * Tq u ≤ Fu ∧ (SC : ℚ) * Tsum (c ++ [u]) ≤ sup ∧
      (slo : ℚ) ≤ SC * Tsum (c ++ [u])
  | .cand u L sup slo w v Fv => ∃ c v' r, D x = c ++ u :: v' :: r ∧ u ∣ L ∧ L ∣ x ∧
      v ≤ v' ∧ inA v = true ∧ (SC : ℚ) * Tq v ≤ Fv ∧ (SC : ℚ) * Tsum (c ++ [u]) ≤ sup ∧
      (slo : ℚ) ≤ SC * Tsum (c ++ [u]) ∧ (w ≠ 0 → w ∣ L ∧ u < w)

theorem Tsum_split (c : List ℕ) (u : ℕ) (rest : List ℕ) :
    Tsum (c ++ u :: rest) = Tsum (c ++ [u]) + Tsum (u :: rest) := by
  unfold Tsum
  exact pairSum_append _ c u rest

theorem Tsum_snoc (c : List ℕ) (u v : ℕ) :
    Tsum (c ++ [u] ++ [v]) = Tsum (c ++ [u]) + 1 / ((u : ℚ) * v) := by
  unfold Tsum
  rw [List.append_assoc, List.singleton_append]
  exact pairSum_concat2 _ c u v

theorem SC_pos : (0 : ℚ) < SC := by unfold SC; norm_num

theorem taskEq_eq : ∀ t s : Task, taskEq t s = true → t = s
  | .node a b c d e, .node a' b' c' d' e', h => by
      simp only [taskEq, Bool.and_eq_true, beqT] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      subst h1 h2 h3 h4 h5
      rfl
  | .node .., .cand .., h => by simp [taskEq] at h
  | .cand .., _, h => by simp [taskEq] at h

theorem memT_mem (t : Task) : ∀ l : List Task, memT t l = true → t ∈ l
  | [], h => by simp [memT] at h
  | s :: r, h => by
      simp only [memT, Bool.or_eq_true] at h
      rcases h with h | h
      · rw [taskEq_eq t s h]
        simp
      · exact List.mem_cons_of_mem _ (memT_mem t r h)

theorem run_sound (M : List Task) {x : ℕ} (hx2 : 2 ≤ x) (hxB : x < B) (hlo : 1 / 9 < Tsum (D x))
    (hhi : Tsum (D x) ≤ 1 / 8) (hA : ∀ d, d ∣ x → inA d = true) (hax : a x = 8)
    (hM : ∀ t ∈ M, ¬ Inv x t) :
    ∀ (n : ℕ) (t : Task), run M n t = true → ¬ Inv x t := by
  have hx0 : 0 < x := by omega
  have hsort := D_sorted x
  intro n
  induction n with
  | zero => intro t h; simp [run] at h
  | succ n ih =>
    intro t h hinv
    cases t with
    | node u Fu L sup slo =>
      by_cases hm : memT (.node u Fu L sup slo) M = true
      · exact hM _ (memT_mem _ _ hm) hinv
      obtain ⟨c, rest, hD, huL, hLx, hF, hsup, hslo⟩ := hinv
      have hL0 : 0 < L := Nat.pos_of_dvd_of_pos hLx hx0
      have hux : u ∣ x := (mem_D hx0).1 (by rw [hD]; simp)
      have hAu := hA u hux
      have hs' := hsort
      rw [hD, List.pairwise_append] at hs'
      obtain ⟨_, hsr, hcu⟩ := hs'
      simp only [run, force_eq, hm, bleD, bltD, beqD, ← decide_not, ← Bool.decide_and,
        ← Bool.decide_or, decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte] at h
      split_ifs at h with h1 h2 h3 h4
      · -- the chain has reached size where x = L
        apply finalize_sound hL0 h
        obtain ⟨k, hk⟩ := hLx
        have hkx : k ∣ x := ⟨L, by rw [hk]; ring⟩
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · interval_cases k
          · omega
          · rw [← hax, hk, mul_one]
        · have := inA_ge (hA k hkx) hk2
          have h11 : 11 * L ≤ x := by
            rw [hk, Nat.mul_comm 11 L]
            exact Nat.mul_le_mul_left L this
          omega
      · -- main branch
        rcases rest with _ | ⟨v', r⟩
        · -- the chain is complete: u = x = L
          exfalso
          have hxm : x ∈ D x := (mem_D hx0).2 dvd_rfl
          rw [hD] at hxm
          have hxu : x = u := by
            rcases List.mem_append.1 hxm with hc | hc
            · have := hcu x hc u (by simp)
              have := Nat.le_of_dvd hx0 hux
              omega
            · simpa using hc
          have hLu : L = u := Nat.dvd_antisymm (hxu ▸ hLx) huL
          have hT : Tsum (D x) = Tsum (c ++ [u]) := by rw [hD]
          rw [hT] at hlo hhi
          have hc2 : 9 * sup ≤ SC ∨ SC < 8 * slo := by
            by_contra hc
            exact h2 ⟨hLu.symm, hc⟩
          rcases hc2 with hc | hc
          · have : (9 : ℚ) * sup ≤ SC := by exact_mod_cast hc
            have := SC_pos
            nlinarith
          · have : (SC : ℚ) < 8 * slo := by exact_mod_cast hc
            have := SC_pos
            nlinarith
        · have hv'x : v' ∣ x := (mem_D hx0).1 (by rw [hD]; simp)
          have huv' : u < v' := List.rel_of_pairwise_cons hsr (by simp)
          exact ih _ h ⟨c, v', r, hD, huL, hLx, gap_spec (hA v' hv'x) huv', h4,
            F_step hAu h4 (by have := gap_pos u; omega) hF, hsup, hslo, fun hw0 => by
              push Not at h3
              have := h3 hw0
              exact ⟨Nat.dvd_of_mod_eq_zero this.1, this.2⟩⟩
    | cand u L sup slo w v Fv =>
      obtain ⟨c, v', r, hD, huL, hLx, hvv', hAv, hF, hsup, hslo, hw⟩ := hinv
      have hux : u ∣ x := (mem_D hx0).1 (by rw [hD]; simp)
      have hv'x : v' ∣ x := (mem_D hx0).1 (by rw [hD]; simp)
      have hAu := hA u hux
      have hAv' := hA v' hv'x
      have hs' := hsort
      rw [hD, List.pairwise_append] at hs'
      obtain ⟨_, hsr, hcu⟩ := hs'
      have huv' : u < v' := List.rel_of_pairwise_cons hsr (by simp)
      have hu1 : 1 ≤ u := by have := inA_odd hAu; omega
      have hv1 : 1 ≤ v := by have := inA_odd hAv; omega
      have hTx : Tsum (D x) = Tsum (c ++ [u]) + 1 / ((u : ℚ) * v') + Tsum (v' :: r) := by
        rw [hD, Tsum_split]
        unfold Tsum
        rw [pairSum_cc]
        ring
      simp only [run, force_eq, bleD, bltD, beqD, ← decide_not, ← Bool.decide_and,
        ← Bool.decide_or, decide_eq_true_eq] at h
      split_ifs at h with h1 h2
      · -- an earlier divisor of L would come before v'
        obtain ⟨hwL, huw⟩ := hw h1.1
        have hwx : w ∣ x := hwL.trans hLx
        have hwm : w ∈ D x := (mem_D hx0).2 hwx
        rw [hD] at hwm
        rcases List.mem_append.1 hwm with hc | hc
        · have := hcu w hc u (by simp)
          omega
        · rcases List.mem_cons.1 hc with hc | hc
          · omega
          · rcases List.mem_cons.1 hc with hc | hc
            · omega
            · have := List.rel_of_pairwise_cons (List.Pairwise.of_cons hsr) hc
              omega
      · -- the bound cuts this branch
        have htl := tail_le r v' (List.Pairwise.of_cons hsr)
          (fun d hd => hA d ((mem_D hx0).1 (by rw [hD]; simp [hd])))
        have hmono := Tq_mono hAv hAv' hvv'
        have huvq : (0 : ℚ) < (u : ℚ) * v := by
          have : (0 : ℚ) < u := by exact_mod_cast hu1
          have : (0 : ℚ) < v := by exact_mod_cast hv1
          positivity
        have h1uv : 1 / ((u : ℚ) * v') ≤ 1 / ((u : ℚ) * v) := by
          apply one_div_le_one_div_of_le huvq
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast hvv'
        have hcd := le_cdiv SC (u * v) (Nat.mul_pos (by omega) (by omega))
        have hsc := sc_term u v
        have h9 : (9 : ℚ) * (sup + cdiv SC (u * v) + Fv) ≤ SC := by exact_mod_cast h2
        have hSC := SC_pos
        have hsum : (SC : ℚ) * Tsum (D x) ≤ sup + cdiv SC (u * v) + Fv := by
          rw [hTx, mul_add, mul_add]
          have e1 : (SC : ℚ) * (1 / ((u : ℚ) * v')) ≤ SC * (1 / ((u : ℚ) * v)) :=
            mul_le_mul_of_nonneg_left h1uv hSC.le
          have e2 : (SC : ℚ) * Tsum (v' :: r) ≤ SC * Tq v :=
            mul_le_mul_of_nonneg_left (htl.trans hmono) hSC.le
          linarith
        nlinarith
      · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
        obtain ⟨hn1, hn2, hn3⟩ := h
        rcases hvv'.lt_or_eq with hlt | heq
        · -- v is not a divisor; move to the next candidate
          exact ih _ hn3 ⟨c, v', r, hD, huL, hLx, gap_spec hAv' hlt, hn2,
            F_step hAv hn2 (by have := gap_pos v; omega) hF, hsup, hslo, hw⟩
        · -- v is the next divisor
          subst heq
          have hlx : Nat.lcm L v ∣ x := Nat.lcm_dvd hLx hv'x
          rcases hn1 with hb | hn1
          · have := Nat.le_of_dvd hx0 hlx
            omega
          · apply ih _ hn1
            refine ⟨c ++ [u], r, by rw [hD]; simp, Nat.dvd_lcm_right L v, hlx, hF, ?_, ?_⟩
            · rw [Tsum_snoc, mul_add, sc_term]
              have := le_cdiv SC (u * v) (Nat.mul_pos (by omega) (by omega))
              push_cast at this ⊢
              linarith
            · rw [Tsum_snoc, mul_add, sc_term]
              have : ((SC / (u * v) : ℕ) : ℚ) ≤ (SC : ℚ) / ((u * v : ℕ) : ℚ) := Nat.cast_div_le
              push_cast at this ⊢
              linarith

/- Part E: the root bound and the main theorem -/

theorem nsum_eq (g : ℕ → ℕ) : ∀ n, (nsum g n : ℚ) = ∑ b ∈ Finset.range n, (g b : ℚ)
  | 0 => by simp [nsum]
  | n + 1 => by rw [nsum, Finset.sum_range_succ, Nat.cast_add, nsum_eq g n]

theorem F1_bound : (SC : ℚ) * Tq 1 ≤ F1 := by
  unfold Tq F1
  rw [Nat.cast_add, nsum_eq, mul_add, Finset.mul_sum]
  have hNN : max 1 NN = NN := Nat.max_eq_right (by unfold NN; norm_num)
  have hN0 : 0 < 2 * NN := by unfold NN; norm_num
  apply add_le_add
  · apply Finset.sum_le_sum
    intro b _
    by_cases h1 : 1 ≤ b
    · by_cases h2 : inA b = true
      · rw [if_pos h1, if_pos ⟨h1, h2⟩]
        unfold fT
        rw [if_pos h2]
        have hb : 0 < b * (b + gap b) := Nat.mul_pos (by omega) (by omega)
        have := le_cdiv SC (b * (b + gap b)) hb
        push_cast at this ⊢
        rw [mul_one_div]
        exact this
      · rw [if_pos h1, if_neg (fun h => h2 h.2)]
        unfold fT
        rw [if_neg h2]
        simp
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
      simp
  · rw [hNN, mul_one_div]
    have := le_cdiv SC (2 * NN) hN0
    push_cast at this ⊢
    exact this

set_option maxRecDepth 100000 in
def G1 : List Task := [
  .node 121 2022732247818623876542169419 10505549483
    110689482533181267963573114899 110689482533181267963573114891,
  .node 169 1494203328826371246470582540 12415649389
    110689846569013557626399486675 110689846569013557626399486666,
  .node 289 921180920134970087450246650 16235849201
    110781098731681385038957327003 110781098731681385038957326989,
  .node 341 809623095560289610133444335 955049953
    110809909942753243131489101271 110809909942753243131489101254]

def G2 : List Task := [
  .node 37 6496993685591356014487845845 1139898331
    110242506355595321948058892285 110242506355595321948058892278,
  .node 41 5837797904444355355292064698 1263130583
    110151582799575045995066370748 110151582799575045995066370741,
  .node 43 5270582929969029206681741386 1324746709
    110112464525473299364127727760 110112464525473299364127727753]

def G3 : List Task := [
  .node 47 4775778377767148949383374242 1447978961
    110044215621721315880362435740 110044215621721315880362435733,
  .node 53 4374333175037321570820548068 1632827339
    109961157993570317112383919980 109961157993570317112383919973,
  .node 59 4054537844049153998067110269 1817675717
    109894993442331385890434932849 109894993442331385890434932842,
  .node 61 3776682884338123156166582345 1879291843
    109875831031316832039269379199 109875831031316832039269379192,
  .node 67 3532004636234379578970595069 2064140221
    109825207945502264402608140452 109825207945502264402608140445,
  .node 71 3321788113215670308421929944 2187372473
    109796212563016925192877290090 109796212563016925192877290083,
  .node 73 3128849660582060429973155104 2248988599
    109782906462835296925398064239 109782906462835296925398064232]

def G4 : List Task := [
  .node 79 2955449279101221172126787842 2433836977
    109747030521839261216878126185 109747030521839261216878126178,
  .node 83 2802940509846989053779982901 2557069229
    109725994829528332648830291021 109725994829528332648830291014,
  .node 89 2667567557362895375696863909 2741917607
    109697986632462658094744128470 109697986632462658094744128463,
  .node 97 2551732969154856455275226008 2988382111
    109666032263301819771869193877 109666032263301819771869193870,
  .node 101 2449660906278465723418535185 3111614363
    109651953358077490015751029626 109651953358077490015751029619,
  .node 103 2353534788812350179825340915 3173230489
    109645323970666033771365292090 109645323970666033771365292083,
  .node 107 2262798920923773825592512678 3296462741
    109632808678543471515609039919 109632808678543471515609039912,
  .node 109 2177057687964843876179840124 3358078867
    109626895490063545312201269398 109626895490063545312201269391,
  .node 113 2095869086844441180718282927 3481311119
    109615697062322800112827261509 109615697062322800112827261502,
  .node 121 2022732247818623876542169419 338888693
    109595521382591540166847643989 109595521382591540166847643982,
  .node 127 1957657737504313991724052676 3912624001
    109582057690802372604471481904 109582057690802372604471481897,
  .node 131 1897550747061325472159227287 4035856253
    109573767071430925912117712885 109573767071430925912117712878,
  .node 137 1841831128183518596358257766 4220704631
    109562238874421724489538201950 109562238874421724489538201943,
  .node 139 1789318393845441612689718146 4282320757
    109558617306536339869974854390 109558617306536339869974854383,
  .node 143 1739008991018053173790487880 30808063
    109551678078560148361161167456 109551678078560148361161167449,
  .node 37 6496993685591356014487845845 1218512009
    110085653657271423740231681218 110085653657271423740231681211]

def G5 : List Task := [
  .node 41 5837797904444355355292064698 1350243037
    110000596137123423655174161070 110000596137123423655174161063,
  .node 43 5270582929969029206681741386 1416108551
    109964001622641144548812204727 109964001622641144548812204720,
  .node 47 4775778377767148949383374242 1547839579
    109900155873969934193031770256 109900155873969934193031770249,
  .node 53 4374333175037321570820548068 1745436121
    109822456802473838571374449061 109822456802473838571374449054,
  .node 59 4054537844049153998067110269 1943032663
    109760560931959999686325396584 109760560931959999686325396577,
  .node 61 3776682884338123156166582345 2008898177
    109742634805527029954589878653 109742634805527029954589878646,
  .node 67 3532004636234379578970595069 2206494719
    109695277725248886036422913374 109695277725248886036422913367]

def G6 : List Task := [
  .node 71 3321788113215670308421929944 2338225747
    109668153012601310646674698519 109668153012601310646674698512,
  .node 73 3128849660582060429973155104 2404091261
    109655705370495916460968325949 109655705370495916460968325942,
  .node 79 2955449279101221172126787842 2601687803
    109622144006338334669127093576 109622144006338334669127093569,
  .node 83 2802940509846989053779982901 2733418831
    109602465455466820847404925196 109602465455466820847404925189,
  .node 89 2667567557362895375696863909 2931015373
    109576264238856996264550127972 109576264238856996264550127965,
  .node 97 2551732969154856455275226008 3194477429
    109546371441900082994763898836 109546371441900082994763898829,
  .node 101 2449660906278465723418535185 3326208457
    109533200853141839029363035504 109533200853141839029363035497,
  .node 103 2353534788812350179825340915 3392073971
    109526999168144025123324764906 109526999168144025123324764899,
  .node 107 2262798920923773825592512678 3523804999
    109515291314222918496972141907 109515291314222918496972141900,
  .node 109 2177057687964843876179840124 3589670513
    109509759621773955274429388839 109509759621773955274429388832,
  .node 113 2095869086844441180718282927 3721401541
    109499283673242290410498865330 109499283673242290410498865323,
  .node 121 2022732247818623876542169419 362260327
    109480409650267885944905029586 109480409650267885944905029579,
  .node 127 1957657737504313991724052676 4182460139
    109467814583755438870424103765 109467814583755438870424103758,
  .node 131 1897550747061325472159227287 4314191167
    109460058843053117771125416618 109460058843053117771125416611,
  .node 137 1841831128183518596358257766 4511787709
    109449274400689671279034906388 109449274400689671279034906381,
  .node 139 1789318393845441612689718146 4577653223
    109445886482345279215572419960 109445886482345279215572419953,
  .node 143 1739008991018053173790487880 32932757
    109439394946496583933133809604 109439394946496583933133809597]

def G7 : List Task := [
  .node 37 6496993685591356014487845845 39306839
    108986377663184770467042643652 108986377663184770467042643646]

def G8 : List Task := [
  .node 41 5837797904444355355292064698 43556227
    108871734918637466004573812148 108871734918637466004573812142,
  .node 43 5270582929969029206681741386 45680921
    108822411877378741991651175338 108822411877378741991651175332,
  .node 47 4775778377767148949383374242 49930309
    108736358911778414990381894096 108736358911778414990381894090]

def G9 : List Task := [
  .node 53 4374333175037321570820548068 56304391
    108631634076283677413365504659 108631634076283677413365504653,
  .node 59 4054537844049153998067110269 62678473
    108548209207330242394386346972 108548209207330242394386346966,
  .node 61 3776682884338123156166582345 64803167
    108524047906485804929873257587 108524047906485804929873257581,
  .node 67 3532004636234379578970595069 71177249
    108460218798284828344517782645 108460218798284828344517782639,
  .node 71 3321788113215670308421929944 75426637
    108423659402977226732248449580 108423659402977226732248449574,
  .node 73 3128849660582060429973155104 77551331
    108406882146226478047165947420 108406882146226478047165947414,
  .node 79 2955449279101221172126787842 83925413
    108361647264101041719032112482 108361647264101041719032112476,
  .node 83 2802940509846989053779982901 88174801
    108335123999882914394102233362 108335123999882914394102233356,
  .node 31 7368833267108356886327427362 41523911
    108450189097072286856601730029 108450189097072286856601730023,
  .node 37 6496993685591356014487845845 49560797
    108269808493999803917600437301 108269808493999803917600437295]

def G10 : List Task := [
  .node 41 5837797904444355355292064698 54918721
    108178884937979527964607915764 108178884937979527964607915758,
  .node 43 5270582929969029206681741386 57597683
    108139766663877781333669272776 108139766663877781333669272770,
  .node 47 4775778377767148949383374242 62955607
    108071517760125797849903980756 108071517760125797849903980750,
  .node 53 4374333175037321570820548068 70992493
    107988460131974799081925464996 107988460131974799081925464990,
  .node 59 4054537844049153998067110269 79029379
    107922295580735867859976477865 107922295580735867859976477859,
  .node 61 3776682884338123156166582345 81708341
    107903133169721314008810924215 107903133169721314008810924209,
  .node 67 3532004636234379578970595069 89745227
    107852510083906746372149685468 107852510083906746372149685462,
  .node 71 3321788113215670308421929944 95103151
    107823514701421407162418835106 107823514701421407162418835100,
  .node 31 7368833267108356886327427362 1431859
    107220752881394047877619234858 107220752881394047877619234853]

def G11 : List Task := [
  .node 37 6496993685591356014487845845 1708993
    106945435118809731812827788063 106945435118809731812827788058,
  .node 41 5837797904444355355292064698 1893749
    106806657059620889568786570980 106806657059620889568786570975,
  .node 43 5270582929969029206681741386 1986127
    106746950220202434184722326420 106746950220202434184722326415,
  .node 47 4775778377767148949383374242 2170883
    106642780840791512025291091232 106642780840791512025291091227]

def G12 : List Task := [
  .node 23 9980430694201262046650491636 55913
    104984529536959204478386064067 104984529536959204478386064063,
  .node 29 8481180319388668343502065849 70499
    104455382345848877289039560848 104455382345848877289039560844,
  .node 31 7368833267108356886327427362 75361
    104324517986757075941136662202 104324517986757075941136662198]

def G13 : List Task := [
  .node 19 12268760213652062961982299416 2717
    101950680898049319101950680900 101950680898049319101950680897,
  .node 23 9980430694201262046650491636 3289
    101246579507449072666463970814 101246579507449072666463970811,
  .node 17 15364735445850205376842980530 187
    96256684491978609625668449199 96256684491978609625668449197]

def M : List Task := G1 ++ G2 ++ G3 ++ G4 ++ G5 ++ G6 ++ G7 ++ G8 ++ G9 ++ G10 ++ G11 ++ G12 ++ G13

set_option maxRecDepth 100000 in
theorem g1 : G1.all (run [] 10000) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g2 : G2.all (run [] 10000) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g3 : G3.all (run [] 10000) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g4 : G4.all (run [] 10000) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g5 : G5.all (run [] 10000) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g6 : G6.all (run [] 10000) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g7 : G7.all (run [] 10000) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g8 : G8.all (run [] 10000) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g9 : G9.all (run [] 10000) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g10 : G10.all (run [] 10000) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g11 : G11.all (run [] 10000) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g12 : G12.all (run [] 10000) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem g13 : G13.all (run [] 10000) = true := by decide +kernel

theorem memo_ok : ∀ s ∈ M, run [] 10000 s = true := by
  have hall : M.all (run [] 10000) = true := by
    simp only [M, List.all_append, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13,
      Bool.and_self]
  exact fun s hs => List.all_eq_true.1 hall s hs

set_option maxRecDepth 100000 in
theorem run_ok : run M 10000 (.node 1 F1 1 0 0) = true := by decide +kernel

theorem lower {x : ℕ} (hx2 : 2 ≤ x) (hax : a x = 8) : B ≤ x := by
  by_contra hxB
  push Not at hxB
  obtain ⟨hlo, hhi⟩ := bridge hx2 hax
  have hA := all_inA hx2 hhi
  obtain ⟨q, rest, hD⟩ := D_head hx2
  have hM : ∀ t ∈ M, ¬ Inv x t := fun t ht =>
    run_sound [] hx2 hxB hlo hhi hA hax (by simp) 10000 t (memo_ok t ht)
  apply run_sound M hx2 hxB hlo hhi hA hax hM 10000 _ run_ok
  refine ⟨[], q :: rest, by simpa using hD, dvd_rfl, one_dvd x, F1_bound, ?_, ?_⟩
  · simp [Tsum]
  · simp [Tsum]

theorem B_fs : prodF [(11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1)] = B := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem aB : a B = 8 := by
  have hok : okF [(11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1)] = true := by
    decide +kernel
  have hs : strictSorted (msort 20 (gen [(11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1),
      (31, 1), (37, 1)])) = true := by
    decide +kernel
  have hD := D_eq_gen hok hs (by rw [B_fs]; unfold B; norm_num)
  rw [B_fs] at hD
  rw [a_eq, hD]
  decide +kernel

theorem value : Nat.kthPrimorial 12 / Nat.kthPrimorial (Nat.primeCounting' 8) = B := by
  have h8 : Nat.primeCounting' 8 = 4 := by decide
  rw [h8, Nat.kthPrimorial_four]
  simp [Nat.kthPrimorial_succ]
  unfold B
  norm_num

theorem main : IsLeast {x : ℕ | 2 ≤ x ∧ a x = 8}
    (Nat.kthPrimorial 12 / Nat.kthPrimorial (Nat.primeCounting' 8)) := by
  rw [value]
  refine ⟨⟨by unfold B; norm_num, aB⟩, ?_⟩
  rintro x ⟨hx2, hax⟩
  exact lower hx2 hax

end OMA_A251758

theorem OMA.solution : type_of% @OeisA251758.conjecture := by
  exact OMA_A251758.main
