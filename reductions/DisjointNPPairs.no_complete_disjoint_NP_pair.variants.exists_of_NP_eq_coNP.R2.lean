import FormalConjectures.Paper.DisjointNPPairs

/-! Use bounded universal verifier acceptance as the complete language. The
instance contains a fixed program prefix, the input, a unary certificate
bound and a unary clock. A fixed interpreter can guess the certificate and
simulate the program within the clock. The correctness obligation below
only constrains inputs on which the clock covers every candidate run.
The other obligation is a deterministic transducer for constructing these
padded instances. This route does not require conversion to Boolean formulas. -/

open ComplexityTheory DisjointNPPairs BitstringEncoding Turing

namespace OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R2

def H1 : Prop :=
  ∃ U : DecisionProblem, U ∈ NP ∧
    ∀ (R : (List Bool × List Bool) → Bool)
      (M : TM2ComputableInPolyTime bitEncode bitEncode R),
      ∃ code : List Bool, ∀ (x : List Bool) (b t : ℕ),
        (∀ w : List Bool, w.length ≤ b → M.time.eval (bitEncode (x, w)).length ≤ t) →
        (U (delimit code ++ delimit x ++ List.replicate b true ++ [false] ++
          List.replicate t true) = true ↔ ∃ w : List Bool, w.length ≤ b ∧ R (x,w) = true)

def H2 : Prop :=
  ∀ (code : List Bool) (p q : Polynomial ℕ),
    IsPolyTime (fun x : List Bool => delimit code ++ delimit x ++
      List.replicate (p.eval x.length) true ++ [false] ++ List.replicate (q.eval x.length) true)

lemma wordLength (x : List Bool) : (bitEncode x).length = 3 * x.length := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    change ([true,b,false] ++ bitEncode x).length = 3 * (x.length + 1)
    simp [ih, Nat.mul_add]

lemma pairLength (x w : List Bool) :
    (bitEncode (x,w)).length = 6 * x.length + 1 + 3 * w.length := by
  change (delimit (bitEncode x) ++ bitEncode w).length = _
  rw [List.length_append, length_delimit, wordLength, wordLength]
  omega

theorem main : H1 → H2 → type_of% @DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP := by
  intro universal padding heq
  obtain ⟨U, hU, simulates⟩ := universal
  have hUc : Uᶜ ∈ NP := (show U ∈ coNP from heq ▸ hU)
  refine ⟨U, Uᶜ, ⟨hU, hUc, ?_⟩, ?_⟩
  · intro x hx
    have h := hx.2
    change (!(U x)) = true at h
    simp [hx.1] at h
  intro A B pair
  obtain ⟨p,R,⟨M⟩,spec⟩ := pair.memA
  obtain ⟨code,correct⟩ := simulates R M
  let q : Polynomial ℕ := M.time.comp (6 * Polynomial.X + 1 + 3 * p)
  have bound (x w : List Bool) (hw : w.length ≤ p.eval x.length) :
      M.time.eval (bitEncode (x,w)).length ≤ q.eval x.length := by
    simp only [q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X, pairLength]
    generalize M.time = poly
    induction poly using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
    | monomial n a =>
      simp only [Polynomial.eval_monomial]
      gcongr
  refine ⟨_, padding code p q, fun x hx =>
    (correct x _ _ (bound x)).2 ((spec x).1 hx), ?_⟩
  intro x hx
  change (!(_)) = true
  rw [Bool.not_eq_true']
  apply Bool.eq_false_iff.mpr
  intro h
  exact pair.disjoint x ⟨(spec x).2 ((correct x _ _ (bound x)).1 h), hx⟩

end OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R2
