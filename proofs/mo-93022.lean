import OMAStatements.S_mo_93022
import Mathlib

/-! A synchronizing five-state automaton. The third letter resets every state to zero.
Each short word either acts constantly or preserves a nonconstant two-colouring,
while the specified word of length six acts as a five-cycle. -/

namespace FiveStateAutomaton

open OMA.S_mo_93022

def transition (letter : Fin 3) : Fin 5 → Fin 5 :=
  if letter = 0 then ![3, 4, 2, 0, 1]
  else if letter = 1 then ![4, 2, 1, 0, 3] else fun _ => 0

lemma reset_synchronizes : ∀ p : Fin 5, run transition [2] p = 0 := by decide

def longWord : List (Fin 3) := [0, 1, 0, 1, 1, 1]

def words : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n + 1 => [] :: ((words n).map (List.cons 0) ++ (words n).map (List.cons 1) ++
    (words n).map (List.cons 2))

lemma mem_words {v : List (Fin 3)} {n : ℕ} (h : v.length ≤ n) : v ∈ words n := by
  induction n generalizing v with
  | zero =>
    have : v = [] := List.length_eq_zero_iff.mp (by omega)
    simp [this, words]
  | succ n ih =>
    cases v with
    | nil => simp [words]
    | cons b v =>
      have hv : v ∈ words n := ih (by simpa using h)
      fin_cases b <;> simp [words, hv]

lemma strongly_connected : Strong transition := by
  have paths : ∀ p q : Fin 5, ∃ v ∈ words 5, run transition v p = q := by decide
  intro p q
  obtain ⟨v, _, hv⟩ := paths p q
  exact ⟨v, hv⟩

lemma long_connects : Connecting (run transition longWord) := by
  have cycle : ∀ p q : Fin 5, p ≠ q → ∃ k : Fin 5,
      0 < k.val ∧ (run transition longWord)^[k.val] p = q := by decide
  intro p q hpq
  obtain ⟨k, hk, he⟩ := cycle p q hpq
  exact ⟨k.val, hk, Or.inl he⟩

set_option maxRecDepth 6000 in
lemma short_disconnected (v : List (Fin 3)) (hv : v.length ≤ 4) :
    ¬ Connecting (run transition v) := by
  have cuts : ∀ w ∈ words 4, (∃ c, ∀ i, run transition w i = c) ∨
      ∃ tag : Fin 5 → Bool,
        (∀ i, tag (run transition w i) = tag i) ∧ ∃ p q, tag p ≠ tag q := by decide
  rcases cuts v (mem_words hv) with ⟨c, hconst⟩ | ⟨tag, hinv, p, q, hdif⟩
  · have two : ∀ a : Fin 5, ∃ p q : Fin 5, p ≠ a ∧ q ≠ a ∧ p ≠ q := by decide
    obtain ⟨p, q, hp, hq, hpq⟩ := two c
    intro hc
    obtain ⟨k, hk, h⟩ := hc p q hpq
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    simp only [Function.iterate_succ_apply', hconst] at h
    exact h.elim (fun e => hq e.symm) (fun e => hp e.symm)
  have keep (k : ℕ) (s : Fin 5) : tag ((run transition v)^[k] s) = tag s := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hinv, ih]
  intro hc
  obtain ⟨k, _, h | h⟩ := hc p q (fun he => hdif (congrArg tag he))
  · exact hdif ((keep k p).symm.trans (congrArg tag h))
  · exact hdif ((congrArg tag h).symm.trans (keep k q))

end FiveStateAutomaton

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_93022.main) := by
  intro h
  obtain ⟨v, hv, hc⟩ := h 5 3 (by decide) FiveStateAutomaton.transition
    FiveStateAutomaton.strongly_connected ⟨_, FiveStateAutomaton.long_connects⟩
  exact FiveStateAutomaton.short_disconnected v hv hc
