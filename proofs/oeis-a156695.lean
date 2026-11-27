import OMAStatements.S_oeis_a156695
import Mathlib

/-!
A counterexample to McEachen’s divisibility conjecture. Each positive prime
remainder would come from two exponents below 48. Every such remainder has
a proper divisor in the list below. The list is checked using division in ℕ.
-/
namespace Remainders156

def witnessed (ds : List ℕ) (v : ℕ) : Bool :=
  decide (v<2) || ds.any (fun d => decide (1 < d ∧ d < v ∧ v%d=0))

lemma composite {ds : List ℕ} {v : ℕ} (ok : witnessed ds v = true) : ¬ v.Prime := by
  intro hp
  simp only [witnessed,Bool.or_eq_true,decide_eq_true_eq,List.any_eq_true] at ok
  rcases ok with h | ⟨d,_,h⟩
  · exact (not_lt_of_ge hp.two_le) h
  · obtain ⟨large,small,div⟩ := h
    have cases := (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero div)
    omega

def certified (n h : ℕ) (ds : List ℕ) : Prop :=
  n < 2^h ∧ ∀ a b : Fin h, 0 < a.val → 0 < b.val → b.val ≤ a.val →
    witnessed ds (n-2^a.val-2^b.val)=true
instance (n h : ℕ) (ds : List ℕ) : Decidable (certified n h ds) := by
  unfold certified
  infer_instance

lemma no_rep {n h : ℕ} {ds : List ℕ} (ok : certified n h ds) :
    ¬ ∃ p a b : ℕ,p.Prime ∧ 0<a ∧ 0<b ∧ n=p+2^a+2^b := by
  rintro ⟨p,a,b,hp,ha,hb,eq⟩
  have lim (e : ℕ) (le : 2^e ≤ n) : e<h := by
    by_contra! ge
    have lower := Nat.pow_le_pow_right (by decide : 0<2) ge
    exact (not_le_of_gt ok.1) (lower.trans le)
  have check (x y : ℕ) (xpos : 0<x) (ypos : 0<y) (order : y≤x) (e : n=p+2^x+2^y) : False := by
    have v := ok.2 ⟨x,lim x (by rw [e]; exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _))⟩ ⟨y,lim y (by rw [e]; exact Nat.le_add_left _ _)⟩ xpos ypos order
    simp only [e,Nat.add_right_comm p (2^x) (2^y),Nat.add_sub_cancel] at v
    exact composite v hp
  rcases le_total a b with le | le
  · exact check b a hb ha le (by omega)
  · exact check a b ha hb le eq
def factors : List ℕ := [3, 5, 7, 11, 241, 257, 13, 19, 31, 17, 47, 29, 23, 43, 53, 37, 233, 229, 173, 193, 59, 71, 103, 67, 149, 83, 223, 41, 107, 421, 61, 26161, 33359, 489449, 529327, 389, 10781, 79, 5351, 109, 683, 333997, 6263, 1013729, 81727, 13757, 1185281, 62983, 1753, 9339397, 113, 379, 197, 467, 2273911, 97, 7937, 20899, 569, 367, 1447, 251, 25579, 263, 73, 8849, 161323, 157, 1289, 89, 167, 1497317, 4901879, 92381, 1777, 283, 10333, 1499]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma actual : certified 275984581255575 48 factors := by decide +kernel

end Remainders156

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a156695.main) := by
  intro claim
  have divisible := claim 275984581255575 (by decide +kernel) (by decide +kernel)
    (Remainders156.no_rep Remainders156.actual)
  exact (by decide +kernel : ¬ 255 ∣ 275984581255575) divisible
