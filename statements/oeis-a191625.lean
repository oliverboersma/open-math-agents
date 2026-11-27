import Mathlib

/-!
# Recurrence for corner-ending two-sided prudent walks

Sources: OEIS A191625 (https://oeis.org/A191625), R. J. Mathar's conjecture,
September 2017, OEIS Foundation, CC BY-SA 4.0. The walk conventions agree with
M. Bousquet-Mélou, https://arxiv.org/abs/0804.4843, section 1.3.
Formalization: @shunyaekam.
-/

namespace OMA.S_oeis_a191625

abbrev Site := ℤ × ℤ

def dir (d : Fin 4) : Site :=
  if d.val = 0 then (1,0) else if d.val = 1 then (0,1)
  else if d.val = 2 then (-1,0) else (0,-1)

def pos {n : ℕ} (w : Fin n → Fin 4) : ℕ → Site
  | 0 => (0,0)
  | i+1 => if h : i < n then pos w i + dir (w ⟨i,h⟩) else pos w i

/-- Each step avoids pointing along any ray towards a previously visited site.
Every prefix ends on the top or right of its own box; the final point is on both. -/
def valid {n : ℕ} (w : Fin n → Fin 4) : Prop :=
  (∀ (i : Fin n) (j : ℕ), j ≤ i.val → ∀ k : ℕ, 0 < k →
    pos w j ≠ pos w i.val + k • dir (w i)) ∧
  (∀ i ≤ n, (∀ j ≤ i, (pos w j).1 ≤ (pos w i).1) ∨
            (∀ j ≤ i, (pos w j).2 ≤ (pos w i).2)) ∧
  (∀ j ≤ n, (pos w j).1 ≤ (pos w n).1 ∧ (pos w j).2 ≤ (pos w n).2)

noncomputable def count (n : ℕ) : ℤ := by
  classical
  exact ((Finset.univ.filter (fun w : Fin n → Fin 4 => valid w)).card : ℤ)

theorem main : ∀ n : ℕ, 9 ≤ n →
    ((n : ℤ)+1)*count n - 4*n*count (n-1) + ((n : ℤ)-5)*count (n-2) +
    2*(4*(n : ℤ)-3)*count (n-3) + 3*(-(n : ℤ)+3)*count (n-4) +
    2*((n : ℤ)-8)*count (n-5) + (-(n : ℤ)+13)*count (n-6) +
    8*(-(n : ℤ)+7)*count (n-7) + 2*((n : ℤ)-7)*count (n-8) +
    2*((n : ℤ)-9)*count (n-9) = 0 := by
  sorry

end OMA.S_oeis_a191625
