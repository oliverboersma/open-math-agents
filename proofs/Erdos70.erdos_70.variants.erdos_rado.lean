import FormalConjectures.ErdosProblems.«70»

/-!
# Erdős Problem 70, Erdős–Rado partial result: ℝ → (ω + n, 4)³

Original proof (no reused formalization). For a red/blue colouring of the triples of `ℝ` with no
four reals all of whose triples are blue, we find a red set of type `ω + n`.

Plan:
* `ramsey2`, `ramsey3`: infinite Ramsey for pairs (finitely many colours) and triples on `ℕ`.
* `exists_strictMono_of_not_countable`, `exists_split`: an uncountable set of reals contains an
  increasing sequence and splits at a point into two uncountable parts.
* `tops`: a red `N`-set `Z` with uncountably many reals below it red with every pair of `Z`
  (top-down choice with uncountable reservoirs, then Ramsey on the induced pair colouring).
* `lemV`: from a large pool of tops, an uncountable set either *splits* (a point `h`, an `m`-subset
  of tops and uncountably many `y > h` with `(h, y, z)` red for those tops) or contains a set of
  type `ω + M` all of whose pairs are blue with many tops (induction on `M`, countable pigeonhole).
* `main`: if no red `ω + m` existed, every uncountable set below the tops would split; iterating
  the splits and a pigeonhole on the `m`-subsets yields a red `ω + m`.
* `erdos_rado_real`: translation to `RealCardinalRamsey3`.

Mathematical source: P. Erdős and R. Rado, *A partition calculus in set theory* (1956), Thm 31;
the route here is our own (brainstormed with Claude Fable; every step checked).
-/


namespace E70

open Set

abbrev InfSet := {S : Set ℕ // S.Infinite}

lemma inf_gt (S : Set ℕ) (hS : S.Infinite) : {x ∈ S | sInf S < x}.Infinite := by
  have : {x ∈ S | sInf S < x} = S \ Iic (sInf S) := by
    ext x; simp [not_le]
  rw [this]; exact hS.sdiff (finite_Iic _)

/-- The iteration underlying both Ramsey arguments. -/
lemma iter_facts (F : InfSet → InfSet) (hF : ∀ S, (F S).1 ⊆ {x ∈ S.1 | sInf S.1 < x})
    (S0 : InfSet) :
    (∀ k l, k < l → sInf (F^[l] S0).1 ∈ (F (F^[k] S0)).1) ∧
    StrictMono (fun k => sInf (F^[k] S0).1) ∧ (∀ k, (F^[k] S0).1 ⊆ S0.1) := by
  have sub : ∀ k j, (F^[k + j] S0).1 ⊆ (F^[k] S0).1 := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih =>
      intro x hx
      rw [← add_assoc, Function.iterate_succ_apply'] at hx
      exact ih (hF _ hx).1
  have mem : ∀ k, sInf (F^[k] S0).1 ∈ (F^[k] S0).1 := fun k =>
    Nat.sInf_mem (F^[k] S0).2.nonempty
  have h1 : ∀ k l, k < l → sInf (F^[l] S0).1 ∈ (F (F^[k] S0)).1 := by
    intro k l hkl
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hkl
    have := sub (k + 1) j (mem (k + 1 + j))
    rw [show k + j + 1 = k + 1 + j by omega]
    rwa [Function.iterate_succ_apply'] at this
  refine ⟨h1, ?_, fun k => by simpa using sub 0 k⟩
  refine strictMono_nat_of_lt_succ fun k => ?_
  have := h1 k (k + 1) (by omega)
  exact (hF _ this).2

/-- A map from `ℕ` to a finite type has an infinite fibre. -/
lemma inf_fiber {κ : Type*} [Finite κ] (col : ℕ → κ) : ∃ b, {k | col k = b}.Infinite := by
  by_contra h
  push Not at h
  have : (univ : Set ℕ) ⊆ ⋃ b, {k | col k = b} := fun k _ => mem_iUnion.2 ⟨col k, rfl⟩
  exact infinite_univ ((finite_iUnion fun b => (h b)).subset this)

/-- A map from an infinite set of naturals to a finite type has an infinite fibre. -/
lemma inf_fiber_on {κ : Type*} [Finite κ] (S : Set ℕ) (hS : S.Infinite) (col : ℕ → κ) :
    ∃ b, {k ∈ S | col k = b}.Infinite := by
  by_contra h
  push Not at h
  have : S ⊆ ⋃ b, {k ∈ S | col k = b} := fun k hk => mem_iUnion.2 ⟨col k, hk, rfl⟩
  exact hS ((finite_iUnion fun b => (h b)).subset this)

/-- Infinite Ramsey for pairs, finitely many colours. -/
theorem ramsey2 {κ : Type*} [Finite κ] (c : ℕ → ℕ → κ) (S : Set ℕ) (hS : S.Infinite) :
    ∃ T ⊆ S, T.Infinite ∧ ∃ b : κ, ∀ x ∈ T, ∀ y ∈ T, x < y → c x y = b := by
  classical
  have step : ∀ S : InfSet, ∃ b : κ, {x ∈ S.1 | sInf S.1 < x ∧ c (sInf S.1) x = b}.Infinite := by
    intro S
    obtain ⟨b, hb⟩ := inf_fiber_on _ (inf_gt S.1 S.2) (c (sInf S.1))
    exact ⟨b, by simpa [and_assoc] using hb⟩
  let col : InfSet → κ := fun S => (step S).choose
  let F : InfSet → InfSet := fun S => ⟨_, (step S).choose_spec⟩
  have hF : ∀ S, (F S).1 ⊆ {x ∈ S.1 | sInf S.1 < x} := fun S x hx => ⟨hx.1, hx.2.1⟩
  have hFc : ∀ S, ∀ x ∈ (F S).1, c (sInf S.1) x = col S := fun S x hx => hx.2.2
  obtain ⟨h1, hmono, hsub⟩ := iter_facts F hF ⟨S, hS⟩
  obtain ⟨b, hb⟩ := inf_fiber (fun k => col (F^[k] ⟨S, hS⟩))
  refine ⟨(fun k => sInf (F^[k] ⟨S, hS⟩).1) '' {k | col (F^[k] ⟨S, hS⟩) = b}, ?_,
    hb.image hmono.injective.injOn, b, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact hsub k (Nat.sInf_mem (F^[k] ⟨S, hS⟩).2.nonempty)
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, -, rfl⟩ hlt
    have hkl : k < l := hmono.lt_iff_lt.mp hlt
    rw [hFc _ _ (h1 k l hkl)]
    exact hk

/-- Infinite Ramsey for triples, two colours. -/
theorem ramsey3 (c : ℕ → ℕ → ℕ → Prop) (S : Set ℕ) (hS : S.Infinite) :
    ∃ T ⊆ S, T.Infinite ∧ ∃ b : Bool,
      ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T, x < y → y < z → (c x y z ↔ b = true) := by
  classical
  have step : ∀ S : InfSet, ∃ T ⊆ {x ∈ S.1 | sInf S.1 < x}, T.Infinite ∧ ∃ b : Bool,
      ∀ x ∈ T, ∀ y ∈ T, x < y → (c (sInf S.1) x y ↔ b = true) := by
    intro S
    obtain ⟨T, hT, hTi, b, hb⟩ :=
      ramsey2 (fun x y => decide (c (sInf S.1) x y)) _ (inf_gt S.1 S.2)
    exact ⟨T, hT, hTi, b, fun x hx y hy hxy => by rw [← hb x hx y hy hxy]; simp⟩
  let F : InfSet → InfSet := fun S => ⟨(step S).choose, (step S).choose_spec.2.1⟩
  let col : InfSet → Bool := fun S => (step S).choose_spec.2.2.choose
  have hF : ∀ S, (F S).1 ⊆ {x ∈ S.1 | sInf S.1 < x} := fun S => (step S).choose_spec.1
  have hFc : ∀ S, ∀ x ∈ (F S).1, ∀ y ∈ (F S).1, x < y → (c (sInf S.1) x y ↔ col S = true) :=
    fun S => (step S).choose_spec.2.2.choose_spec
  obtain ⟨h1, hmono, hsub⟩ := iter_facts F hF ⟨S, hS⟩
  obtain ⟨b, hb⟩ := inf_fiber (fun k => col (F^[k] ⟨S, hS⟩))
  refine ⟨(fun k => sInf (F^[k] ⟨S, hS⟩).1) '' {k | col (F^[k] ⟨S, hS⟩) = b}, ?_,
    hb.image hmono.injective.injOn, b, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact hsub k (Nat.sInf_mem (F^[k] ⟨S, hS⟩).2.nonempty)
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, -, rfl⟩ _ ⟨m, -, rfl⟩ hlt hlt'
    have hkl : k < l := hmono.lt_iff_lt.mp hlt
    have hlm : l < m := hmono.lt_iff_lt.mp hlt'
    have := hFc _ _ (h1 k l hkl) _ (h1 k m (hkl.trans hlm)) hlt'
    simp only [mem_ofPred_eq] at hk
    rw [← hk]; exact this

/-- Enumerate an infinite set of naturals increasingly. -/
lemma enum (T : Set ℕ) (hT : T.Infinite) : ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ n, g n ∈ T :=
  ⟨Nat.nth (· ∈ T), Nat.nth_strictMono hT, Nat.nth_mem_of_infinite hT⟩

/-- Pigeonhole: an uncountable set covered by countably many pieces has an uncountable piece. -/
lemma pigeon {ι : Type*} (S : Set ℝ) (hS : ¬ S.Countable) (I : Set ι) (hI : I.Countable)
    (P : ι → ℝ → Prop) (hP : ∀ y ∈ S, ∃ i ∈ I, P i y) :
    ∃ i ∈ I, ¬ {y ∈ S | P i y}.Countable := by
  by_contra h
  push Not at h
  apply hS
  have : S ⊆ ⋃ i ∈ I, {y ∈ S | P i y} := by
    intro y hy
    obtain ⟨i, hi, hPi⟩ := hP y hy
    exact mem_biUnion hi ⟨hy, hPi⟩
  exact (hI.biUnion h).mono this

/-- A finite colouring of an uncountable set has an uncountable fibre. -/
lemma unc_fiber {κ : Type*} [Finite κ] (S : Set ℝ) (hS : ¬ S.Countable) (φ : ℝ → κ) :
    ∃ k, ¬ {y ∈ S | φ y = k}.Countable := by
  obtain ⟨k, -, hk⟩ := pigeon S hS (univ : Set κ) (Set.countable_univ_iff.2 inferInstance)
    (fun k y => φ y = k) (fun y _ => ⟨φ y, mem_univ _, rfl⟩)
  exact ⟨k, hk⟩

end E70


namespace E70

open Set

/-- An uncountable set of reals contains a strictly increasing sequence. -/
theorem exists_strictMono_of_not_countable (U : Set ℝ) (hU : ¬ U.Countable) :
    ∃ x : ℕ → ℝ, StrictMono x ∧ ∀ n, x n ∈ U := by
  classical
  -- points of `U` that are isolated from the left by a rational
  set L : Set ℝ := {u ∈ U | ∃ q : ℚ, (q : ℝ) < u ∧ ∀ v ∈ U, ¬ ((q : ℝ) < v ∧ v < u)} with hL
  have hLc : L.Countable := by
    have : ∀ u ∈ L, ∃ q : ℚ, (q : ℝ) < u ∧ ∀ v ∈ U, ¬ ((q : ℝ) < v ∧ v < u) := fun u hu => hu.2
    choose! φ hφ using this
    refine Set.MapsTo.countable_of_injOn (f := φ) (t := Set.univ) (fun u _ => Set.mem_univ _) ?_ Set.countable_univ
    intro u hu u' hu' huu'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hφ u' hu').2 u hu.1 ⟨by rw [← huu']; exact (hφ u hu).1, h⟩
    · exact (hφ u hu).2 u' hu'.1 ⟨by rw [huu']; exact (hφ u' hu').1, h⟩
  obtain ⟨u, huU, huL⟩ : ∃ u ∈ U, u ∉ L := by
    by_contra h
    push Not at h
    exact hU (hLc.mono h)
  have key : ∀ a < u, ∃ v ∈ U, a < v ∧ v < u := by
    intro a hau
    obtain ⟨q, haq, hqu⟩ := exists_rat_btwn hau
    have : ¬ ∀ v ∈ U, ¬ ((q : ℝ) < v ∧ v < u) := fun h => huL ⟨huU, q, hqu, h⟩
    push Not at this
    obtain ⟨v, hv, hqv, hvu⟩ := this
    exact ⟨v, hv, haq.trans hqv, hvu⟩
  obtain ⟨v0, hv0, -, hv0u⟩ := key (u - 1) (by linarith)
  let T := {v : ℝ // v ∈ U ∧ v < u}
  let nxt : T → T := fun t => ⟨(key t.1 t.2.2).choose, (key t.1 t.2.2).choose_spec.1,
    (key t.1 t.2.2).choose_spec.2.2⟩
  let seq : ℕ → T := fun n => nxt^[n] ⟨v0, hv0, hv0u⟩
  refine ⟨fun n => (seq n).1, strictMono_nat_of_lt_succ fun n => ?_, fun n => (seq n).2.1⟩
  show (seq n).1 < (seq (n + 1)).1
  simp only [seq, Function.iterate_succ_apply']
  exact (key _ (nxt^[n] ⟨v0, hv0, hv0u⟩).2.2).choose_spec.2.1

/-- An uncountable set of reals can be split by a point into two uncountable parts. -/
theorem exists_split (U : Set ℝ) (hU : ¬ U.Countable) :
    ∃ p, ¬ (U ∩ Iio p).Countable ∧ ¬ (U ∩ Ioi p).Countable := by
  by_contra hcon
  push Not at hcon
  have h : ∀ p, (U ∩ Iio p).Countable ∨ (U ∩ Ioi p).Countable := by
    intro p; by_contra h'; push Not at h'; exact h'.2 (hcon p h'.1)
  set A : Set ℝ := ⋃ q : ℚ, ⋃ (_ : (U ∩ Iio (q : ℝ)).Countable), U ∩ Iio (q : ℝ)
  set B : Set ℝ := ⋃ q : ℚ, ⋃ (_ : (U ∩ Ioi (q : ℝ)).Countable), U ∩ Ioi (q : ℝ)
  have hA : A.Countable := countable_iUnion fun q => countable_iUnion fun h => h
  have hB : B.Countable := countable_iUnion fun q => countable_iUnion fun h => h
  have hC : (U \ (A ∪ B)).Subsingleton := by
    intro u hu u' hu'
    by_contra hne
    wlog hlt : u < u' generalizing u u'
    · exact this hu' hu (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
    obtain ⟨q, huq, hqu'⟩ := exists_rat_btwn hlt
    rcases h q with hq | hq
    · exact hu.2 (Or.inl (mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hq, hu.1, huq⟩⟩))
    · exact hu'.2 (Or.inr (mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hq, hu'.1, hqu'⟩⟩))
  apply hU
  have : U ⊆ (A ∪ B) ∪ (U \ (A ∪ B)) := by
    intro u hu; by_cases h : u ∈ A ∪ B
    · exact Or.inl h
    · exact Or.inr ⟨hu, h⟩
  exact ((hA.union hB).union hC.countable).mono this

end E70


namespace E70

open Ordinal

/-- An increasing sequence followed by `n` increasing points above it is an order embedding of
`ω + n` into `ℝ`. -/
theorem exists_embed (n : ℕ) (x : ℕ → ℝ) (y : Fin n → ℝ) (hx : StrictMono x) (hy : StrictMono y)
    (hxy : ∀ i j, x i < y j) :
    ∃ e : (ω + (n : Ordinal.{0})).ToType ↪o ℝ, Set.range e = Set.range x ∪ Set.range y := by
  have ht : type (Sum.Lex (· < · : ℕ → ℕ → Prop) (· < · : Fin n → Fin n → Prop)) = ω + n := by
    rw [type_sum_lex, type_nat_lt, type_fin]
  have hiso : Nonempty ((· < · : (ω + (n : Ordinal.{0})).ToType → _ → Prop) ≃r
      (Sum.Lex (· < · : ℕ → ℕ → Prop) (· < · : Fin n → Fin n → Prop))) := by
    rw [← Ordinal.type_eq, type_toType, ht]
  obtain ⟨r⟩ := hiso
  let g : ℕ ⊕ Fin n → ℝ := Sum.elim x y
  have hg : ∀ a b, Sum.Lex (· < ·) (· < ·) a b → g a < g b := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact hx (Sum.lex_inl_inl.mp hab)
    · exact hxy a b
    · exact absurd hab Sum.lex_inr_inl
    · exact hy (Sum.lex_inr_inr.mp hab)
  have hm : StrictMono (fun u => g (r u)) := fun u v huv => hg _ _ (r.map_rel_iff.mpr huv)
  refine ⟨OrderEmbedding.ofStrictMono _ hm, ?_⟩
  ext t
  simp only [Set.mem_range, Set.mem_union, OrderEmbedding.coe_ofStrictMono]
  constructor
  · rintro ⟨u, rfl⟩
    rcases h : r u with a | a
    · left; exact ⟨a, by simp [g]⟩
    · right; exact ⟨a, by simp [g]⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨r.symm (Sum.inl a), by simp [g]⟩
    · exact ⟨r.symm (Sum.inr a), by simp [g]⟩

end E70


namespace E70
open Set

lemma nonempty_of_unc {S : Set ℝ} (h : ¬ S.Countable) : S.Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun h' => h (h' ▸ countable_empty)

lemma exists_pt_below (W : Set ℝ) (hW : ¬ W.Countable) : ∃ p ∈ W, ¬ (W ∩ Iio p).Countable := by
  obtain ⟨s, hs1, hs2⟩ := exists_split W hW
  obtain ⟨p, hp⟩ := nonempty_of_unc hs2
  refine ⟨p, hp.1, fun h => hs1 (h.mono ?_)⟩
  intro u hu; exact ⟨hu.1, show u < p from lt_trans (show u < s from hu.2) hp.2⟩

lemma exists_pt_above (W : Set ℝ) (hW : ¬ W.Countable) : ∃ p ∈ W, ¬ (W ∩ Ioi p).Countable := by
  obtain ⟨s, hs1, hs2⟩ := exists_split W hW
  obtain ⟨p, hp⟩ := nonempty_of_unc hs1
  refine ⟨p, hp.1, fun h => hs2 (h.mono ?_)⟩
  intro u hu; exact ⟨hu.1, show p < u from lt_trans (show p < s from hp.2) hu.2⟩

end E70


namespace E70
open Set

variable (r : ℝ → ℝ → ℝ → Prop)

/-- No four reals all of whose (sorted) triples are blue. -/
def K4free : Prop :=
  ∀ a b c d : ℝ, a < b → b < c → c < d → r a b c ∨ r a b d ∨ r a c d ∨ r b c d

/-- Every sorted triple of `S` is red. -/
def RedSet (S : Set ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c → r a b c

/-- A red set of type `ω + n`: an increasing sequence followed by `n` points. -/
def RedOm (n : ℕ) : Prop :=
  ∃ x : ℕ → ℝ, ∃ T : Finset ℝ, StrictMono x ∧ T.card = n ∧ (∀ i, ∀ t ∈ T, x i < t) ∧
    RedSet r (range x ∪ ↑T)

/-- Points below `Z` that are red with every pair of `Z`. -/
def D (Z : Finset ℝ) : Set ℝ :=
  {u | (∀ z ∈ Z, u < z) ∧ ∀ z ∈ Z, ∀ z' ∈ Z, z < z' → r u z z'}

variable {r}

/-- Every increasing sequence has a red subsequence. -/
lemma red_subseq (hK : K4free r) (x : ℕ → ℝ) (hx : StrictMono x) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ i j k, i < j → j < k → r (x (g i)) (x (g j)) (x (g k)) := by
  obtain ⟨T, -, hT, b, hb⟩ := ramsey3 (fun i j k => r (x i) (x j) (x k)) univ infinite_univ
  obtain ⟨g, hg, hgT⟩ := enum T hT
  cases b with
  | false =>
    exfalso
    have h := hK _ _ _ _ (hx (hg (show 0 < 1 by omega))) (hx (hg (show 1 < 2 by omega)))
      (hx (hg (show 2 < 3 by omega)))
    have e : ∀ i j k : ℕ, i < j → j < k → ¬ r (x (g i)) (x (g j)) (x (g k)) := by
      intro i j k hij hjk h'
      have := (hb _ (hgT i) _ (hgT j) _ (hgT k) (hg hij) (hg hjk)).1 h'
      simp at this
    rcases h with h | h | h | h
    · exact e 0 1 2 (by omega) (by omega) h
    · exact e 0 1 3 (by omega) (by omega) h
    · exact e 0 2 3 (by omega) (by omega) h
    · exact e 1 2 3 (by omega) (by omega) h
  | true =>
    exact ⟨g, hg, fun i j k hij hjk =>
      (hb _ (hgT i) _ (hgT j) _ (hgT k) (hg hij) (hg hjk)).2 rfl⟩

/-- **Tops.** For every `N` there is a red `N`-set `Z` with uncountably many points below it red
with every pair of `Z`. Built top-down with uncountable reservoirs (end-homogeneity), then
infinite Ramsey on the induced pair colouring; blue would give a blue `K₄`. -/
theorem tops (hK : K4free r) (N : ℕ) :
    ∃ Z : Finset ℝ, Z.card = N ∧ RedSet r ↑Z ∧ ¬ (D r Z).Countable := by
  classical
  -- states: an uncountable reservoir and the finite set of points chosen so far
  let St := {W : Set ℝ // ¬ W.Countable} × Finset ℝ
  have hpt : ∀ s : St, ∃ p ∈ s.1.1, ¬ (s.1.1 ∩ Iio p).Countable := fun s =>
    exists_pt_below s.1.1 s.1.2
  let pt : St → ℝ := fun s => (hpt s).choose
  have hfib : ∀ s : St, ∃ k : (↥s.2 → Bool),
      ¬ {u ∈ s.1.1 ∩ Iio (pt s) | (fun a : ↥s.2 => decide (r u (pt s) a)) = k}.Countable :=
    fun s => unc_fiber _ (hpt s).choose_spec.2 _
  let step : St → St := fun s => (⟨_, (hfib s).choose_spec⟩, insert (pt s) s.2)
  let st : ℕ → St := fun n => step^[n] (⟨univ, Set.not_countable_univ⟩, ∅)
  let p : ℕ → ℝ := fun n => pt (st n)
  have st_succ : ∀ n, st (n + 1) = step (st n) := fun n => Function.iterate_succ_apply' _ _ _
  have W_succ : ∀ n, (st (n + 1)).1.1 ⊆ (st n).1.1 ∩ Iio (p n) := by
    intro n u hu; rw [st_succ] at hu; exact hu.1
  have W_anti : ∀ n k, (st (n + k)).1.1 ⊆ (st n).1.1 := by
    intro n k; induction k with
    | zero => simp
    | succ k ih => intro u hu; exact ih (W_succ _ (by rwa [← add_assoc] at hu)).1
  have p_mem : ∀ n, p n ∈ (st n).1.1 := fun n => (hpt (st n)).choose_spec.1
  have p_anti : StrictAnti p := strictAnti_nat_of_succ_lt fun n => (W_succ n (p_mem (n + 1))).2
  have prev_mem : ∀ i n, i < n → p i ∈ (st n).2 := by
    intro i n hin
    induction n with
    | zero => omega
    | succ n ih =>
      rw [st_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hin with h | h
      · exact Finset.mem_insert_of_mem (ih h)
      · subst h; exact Finset.mem_insert_self _ _
  -- the fibre property: below stage `j+1`, the colour with `(p j, p i)` is constant
  have fib : ∀ j, ∀ u ∈ (st (j + 1)).1.1, ∀ v ∈ (st (j + 1)).1.1, ∀ i, i < j →
      (r u (p j) (p i) ↔ r v (p j) (p i)) := by
    intro j u hu v hv i hij
    rw [st_succ] at hu hv
    have hu2 := hu.2; have hv2 := hv.2
    have hmem := prev_mem i j hij
    have e1 := congrFun hu2 ⟨p i, hmem⟩
    have e2 := congrFun hv2 ⟨p i, hmem⟩
    simp only at e1 e2
    rw [← e2] at e1
    simpa using e1
  have later : ∀ j k, j < k → p k ∈ (st (j + 1)).1.1 := by
    intro j k hjk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hjk
    have := W_anti (j + 1) d (p_mem _)
    simpa [show j + d + 1 = j + 1 + d by omega] using this
  let C : ℕ → ℕ → Prop := fun i j => r (p (j + 1)) (p j) (p i)
  have hC : ∀ i j k, i < j → j < k → (r (p k) (p j) (p i) ↔ C i j) := fun i j k hij hjk =>
    fib j _ (later j k hjk) _ (later j (j + 1) (by omega)) i hij
  obtain ⟨T, -, hT, b, hb⟩ := ramsey2 (fun i j => decide (C i j)) univ infinite_univ
  have hb' : ∀ i ∈ T, ∀ j ∈ T, i < j → (C i j ↔ b = true) := by
    intro i hi j hj hij; rw [← hb i hi j hj hij]; simp
  cases b with
  | false =>
    exfalso
    obtain ⟨g, hg, hgT⟩ := enum T hT
    have e : ∀ a b, a < b → ¬ C (g a) (g b) := fun a b hab h => by
      simpa using (hb' _ (hgT a) _ (hgT b) (hg hab)).1 h
    have h := hK _ _ _ _ (p_anti (hg (show 2 < 3 by omega))) (p_anti (hg (show 1 < 2 by omega)))
      (p_anti (hg (show 0 < 1 by omega)))
    rcases h with h | h | h | h
    · exact e 1 2 (by omega) ((hC _ _ _ (hg (by omega)) (hg (by omega))).1 h)
    · exact e 0 2 (by omega) ((hC _ _ _ (hg (by omega)) (hg (by omega))).1 h)
    · exact e 0 1 (by omega) ((hC _ _ _ (hg (by omega)) (hg (by omega))).1 h)
    · exact e 0 1 (by omega) ((hC _ _ _ (hg (by omega)) (hg (by omega))).1 h)
  | true =>
    obtain ⟨F, hFT, hFc⟩ := hT.exists_subset_card_eq N
    refine ⟨F.image p, by rw [Finset.card_image_of_injective _ p_anti.injective, hFc], ?_, ?_⟩
    · intro a ha b hb c hc hab hbc
      simp only [Finset.coe_image, mem_image, Finset.mem_coe] at ha hb hc
      obtain ⟨k, hk, rfl⟩ := ha; obtain ⟨j, hj, rfl⟩ := hb; obtain ⟨i, hi, rfl⟩ := hc
      have hij : i < j := (StrictAnti.lt_iff_gt p_anti).mp hbc
      have hjk : j < k := (StrictAnti.lt_iff_gt p_anti).mp hab
      exact (hC i j k hij hjk).2 ((hb' i (hFT hi) j (hFT hj) hij).2 rfl)
    · set K := F.sup id + 1 with hKdef
      have hle : ∀ j ∈ F, j < K := fun j hj => by
        have := Finset.le_sup (f := id) hj; simp only [id] at this; omega
      refine fun hcount => (st K).1.2 (hcount.mono ?_)
      intro u hu
      refine ⟨?_, ?_⟩
      · intro z hz
        simp only [Finset.mem_image] at hz
        obtain ⟨j, hj, rfl⟩ := hz
        have hjK := hle j hj
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hjK
        have hu' := W_anti (j + 1) d (by rw [show j + 1 + d = K by omega]; exact hu)
        exact (W_succ j hu').2
      · intro z hz z' hz' hzz'
        simp only [Finset.mem_image] at hz hz'
        obtain ⟨j, hj, rfl⟩ := hz; obtain ⟨i, hi, rfl⟩ := hz'
        have hij : i < j := (StrictAnti.lt_iff_gt p_anti).mp hzz'
        have hjK := hle j hj
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hjK
        have hu' := W_anti (j + 1) d (by rw [show j + 1 + d = K by omega]; exact hu)
        exact (fib j _ hu' _ (later j (j + 1) (by omega)) i hij).2
          ((hb' i (hFT hi) j (hFT hj) hij).2 rfl)

end E70


namespace E70
open Set

variable (r : ℝ → ℝ → ℝ → Prop)

/-- `E` splits: a point `h ∈ E`, an `m`-subset `Z'` of the tops and uncountably many `y ∈ E`
above `h` with `(h, y, z)` red for every `z ∈ Z'`. -/
def Splits (m : ℕ) (Z : Finset ℝ) (E : Set ℝ) : Prop :=
  ∃ h ∈ E, ∃ Z' ⊆ Z, Z'.card = m ∧ ¬ {y ∈ E | h < y ∧ ∀ z ∈ Z', r h y z}.Countable

/-- Every pair of `S` is blue with `z`. -/
def PB (S : Set ℝ) (z : ℝ) : Prop := ∀ a ∈ S, ∀ b ∈ S, a < b → ¬ r a b z

/-- Size of the pool of tops needed in `lemV`. -/
def NN (m : ℕ) : ℕ → ℕ → ℕ
  | 0, L => L + m - 1
  | M + 1, L => NN m M (L + (M + 1) * (m - 1))

variable {r}

/-- **Lemma V.** With a pool of at least `NN m M L` tops, an uncountable `E` either splits, or
contains a set of type `ω + M` and at least `L` tops each blue with every pair of that set. -/
theorem lemV (m : ℕ) : ∀ M L (Z : Finset ℝ), NN m M L ≤ Z.card → ∀ E : Set ℝ, ¬ E.Countable →
    Splits r m Z E ∨ ∃ x : ℕ → ℝ, ∃ T : Finset ℝ, ∃ ZH ⊆ Z, StrictMono x ∧ (∀ i, x i ∈ E) ∧
      ↑T ⊆ E ∧ T.card = M ∧ (∀ i, ∀ t ∈ T, x i < t) ∧ L ≤ ZH.card ∧
      ∀ z ∈ ZH, PB r (range x ∪ ↑T) z := by
  classical
  intro M
  induction M with
  | zero =>
    intro L Z hN E hE
    by_cases hs : Splits r m Z E
    · exact Or.inl hs
    right
    set X : ℝ → Set ℝ := fun h => {y ∈ E | h < y ∧ m ≤ (Z.filter (fun z => r h y z)).card}
      with hX
    have exc : ∀ h ∈ E, (X h).Countable := by
      intro h hh
      by_contra hc
      apply hs
      obtain ⟨Z', hZ', hZ'c⟩ := pigeon _ hc (Z.powersetCard m : Set (Finset ℝ))
        (Finset.countable_toSet _) (fun Z' y => ∀ z ∈ Z', r h y z) (by
          intro y hy
          obtain ⟨Z', hsub, hcard⟩ := Finset.exists_subset_card_eq hy.2.2
          exact ⟨Z', Finset.mem_powersetCard.2 ⟨hsub.trans (Finset.filter_subset _ _), hcard⟩,
            fun z hz => (Finset.mem_filter.1 (hsub hz)).2⟩)
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hZ'
      exact ⟨h, hh, Z', hZ'.1, hZ'.2, fun hc' => hZ'c (hc'.mono (by
        intro y hy; exact ⟨hy.1.1, hy.1.2.1, hy.2⟩))⟩
    let St := {W : Set ℝ // W ⊆ E ∧ ¬ W.Countable}
    have hpt : ∀ W : St, ∃ p ∈ W.1, ¬ (W.1 ∩ Ioi p).Countable := fun W =>
      exists_pt_above W.1 W.2.2
    let pt : St → ℝ := fun W => (hpt W).choose
    have pt_mem : ∀ W : St, pt W ∈ W.1 := fun W => (hpt W).choose_spec.1
    let nxt : St → St := fun W => ⟨(W.1 ∩ Ioi (pt W)) \ X (pt W),
      fun y hy => W.2.1 hy.1.1, fun hc => (hpt W).choose_spec.2 <| by
        refine (hc.union (exc _ (W.2.1 (pt_mem W)))).mono ?_
        intro y hy
        by_cases h : y ∈ X (pt W)
        · exact Or.inr h
        · exact Or.inl ⟨hy, h⟩⟩
    let Wn : ℕ → St := fun n => nxt^[n] ⟨E, subset_rfl, hE⟩
    let x : ℕ → ℝ := fun n => pt (Wn n)
    have W_succ : ∀ n, (Wn (n + 1)).1 ⊆ ((Wn n).1 ∩ Ioi (x n)) \ X (x n) := by
      intro n y hy
      simp only [Wn, Function.iterate_succ_apply'] at hy
      exact hy
    have W_anti : ∀ n k, (Wn (n + k)).1 ⊆ (Wn n).1 := by
      intro n k; induction k with
      | zero => simp
      | succ k ih => intro u hu; exact ih (W_succ _ (by rwa [← add_assoc] at hu)).1.1
    have later : ∀ j k, j < k → x k ∈ (Wn (j + 1)).1 := by
      intro j k hjk
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hjk
      have := W_anti (j + 1) d (pt_mem _)
      simpa [show j + d + 1 = j + 1 + d by omega] using this
    have xE : ∀ n, x n ∈ E := fun n => (Wn n).2.1 (pt_mem _)
    have pair : ∀ i j, i < j → x i < x j ∧ ¬ m ≤ (Z.filter (fun z => r (x i) (x j) z)).card := by
      intro i j hij
      have h := W_succ i (later i j hij)
      refine ⟨h.1.2, fun hm => h.2 ⟨xE j, h.1.2, hm⟩⟩
    have hx : StrictMono x := fun i j hij => (pair i j hij).1
    let B : ℕ → ℕ → Finset ℝ := fun i j => Z.filter (fun z => ¬ r (x i) (x j) z)
    have hB : ∀ i j, i < j → L ≤ (B i j).card := by
      intro i j hij
      have h1 := (pair i j hij).2
      have h2 := Finset.card_filter_add_card_filter_not (s := Z) (fun z => r (x i) (x j) z)
      simp only [NN] at hN
      simp only [B]
      omega
    let c : ℕ → ℕ → {s // s ∈ Z.powerset} := fun i j =>
      ⟨B i j, Finset.mem_powerset.2 (Finset.filter_subset _ _)⟩
    obtain ⟨T, -, hT, b, hb⟩ := ramsey2 c univ infinite_univ
    obtain ⟨g, hg, hgT⟩ := enum T hT
    have hb' : ∀ i j, i < j → B (g i) (g j) = b.1 := fun i j hij =>
      congrArg Subtype.val (hb _ (hgT i) _ (hgT j) (hg hij))
    refine ⟨x ∘ g, ∅, b.1, Finset.mem_powerset.1 b.2, hx.comp hg, fun i => xE _, by simp,
      by simp, by simp, ?_, ?_⟩
    · rw [← hb' 0 1 (by omega)]; exact hB _ _ (hg (by omega))
    · intro z hz a ha b' hb'' hab
      simp only [Finset.coe_empty, union_empty, mem_range, Function.comp] at ha hb''
      obtain ⟨i, rfl⟩ := ha; obtain ⟨j, rfl⟩ := hb''
      have hij : i < j := (hx.comp hg).lt_iff_lt.mp hab
      rw [← hb' i j hij] at hz
      exact (Finset.mem_filter.1 hz).2
  | succ M ih =>
    intro L Z hN E hE
    obtain ⟨p, hp1, hp2⟩ := exists_split E hE
    rcases ih (L + (M + 1) * (m - 1)) Z hN (E ∩ Iio p) hp1 with hs0 |
      ⟨x, T, ZH, hZH, hx, hxE, hTE, hTc, hxT, hLZ, hPB⟩
    · left
      obtain ⟨h, hh, Z', hZ', hc, hun⟩ := hs0
      exact ⟨h, hh.1, Z', hZ', hc, fun hcnt => hun (hcnt.mono (by intro y hy; exact ⟨hy.1.1, hy.2⟩))⟩
    by_cases hs : Splits r m Z E
    · exact Or.inl hs
    right
    have hA : ∀ y : ℝ, ∃ κ : (↥ZH → Bool),
        {i | (fun z : ↥ZH => decide (r (x i) y z)) = κ}.Infinite := fun y => inf_fiber _
    choose κ hκ using hA
    have hne : ∀ y, ∃ i, i ∈ {i | (fun z : ↥ZH => decide (r (x i) y z)) = κ y} :=
      fun y => (hκ y).nonempty
    choose i0 hi0 using hne
    have const : ∀ y, ∀ i ∈ {i | (fun z : ↥ZH => decide (r (x i) y z)) = κ y}, ∀ z ∈ ZH,
        (r (x i) y z ↔ r (x (i0 y)) y z) := by
      intro y i hi z hz
      have e1 := congrFun hi ⟨z, hz⟩
      have e2 := congrFun (hi0 y) ⟨z, hz⟩
      simp only at e1 e2
      rw [← e2] at e1
      simpa using e1
    let Rt : ℝ → Finset ℝ := fun y => ZH.filter (fun z => r (x (i0 y)) y z)
    let Rtt : ℝ → ℝ → Finset ℝ := fun t y => ZH.filter (fun z => r t y z)
    let good : ℝ → Prop := fun y => m ≤ (Rt y).card ∨ ∃ t ∈ T, m ≤ (Rtt t y).card
    have hgood : {y ∈ E ∩ Ioi p | good y}.Countable := by
      by_contra hc
      apply hs
      obtain ⟨⟨h, Z'⟩, hI, hun⟩ := pigeon _ hc ((range x ∪ ↑T) ×ˢ (Z.powersetCard m : Set _))
        (((countable_range x).union (Finset.countable_toSet T)).prod (Finset.countable_toSet _))
        (fun q y => ∀ z ∈ q.2, r q.1 y z) (by
          intro y ⟨hy, hgy⟩
          rcases hgy with h1 | ⟨t, ht, h2⟩
          · obtain ⟨Z', hsub, hcard⟩ := Finset.exists_subset_card_eq h1
            refine ⟨⟨x (i0 y), Z'⟩, ⟨Or.inl (mem_range_self _), ?_⟩, ?_⟩
            · exact Finset.mem_powersetCard.2
                ⟨hsub.trans ((Finset.filter_subset _ _).trans hZH), hcard⟩
            · exact fun z hz => (Finset.mem_filter.1 (hsub hz)).2
          · obtain ⟨Z', hsub, hcard⟩ := Finset.exists_subset_card_eq h2
            refine ⟨⟨t, Z'⟩, ⟨Or.inr ht, ?_⟩, ?_⟩
            · exact Finset.mem_powersetCard.2
                ⟨hsub.trans ((Finset.filter_subset _ _).trans hZH), hcard⟩
            · exact fun z hz => (Finset.mem_filter.1 (hsub hz)).2)
      simp only [mem_prod, Finset.mem_coe, Finset.mem_powersetCard] at hI
      have hhE : h ∈ E ∩ Iio p := by
        rcases hI.1 with ⟨i, rfl⟩ | ht
        · exact hxE i
        · exact hTE ht
      refine ⟨h, hhE.1, Z', hI.2.1, hI.2.2, fun hcnt => hun (hcnt.mono ?_)⟩
      intro y hy
      exact ⟨hy.1.1.1, lt_trans (show h < p from hhE.2) hy.1.1.2, hy.2⟩
    obtain ⟨y, hyE, hyg⟩ : ∃ y ∈ E ∩ Ioi p, ¬ good y := by
      by_contra h
      push Not at h
      exact hp2 (hgood.mono (by intro y hy; exact ⟨hy, h y hy⟩))
    simp only [good, not_or, not_exists, not_and, not_le] at hyg
    obtain ⟨hRt, hRtt⟩ := hyg
    let Zy : Finset ℝ := ZH.filter (fun z => ¬ r (x (i0 y)) y z ∧ ∀ t ∈ T, ¬ r t y z)
    have hcov : ZH ⊆ (Zy ∪ Rt y) ∪ T.biUnion (fun t => Rtt t y) := by
      intro z hz
      by_cases h1 : r (x (i0 y)) y z
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hz, h1⟩))
      by_cases h2 : ∃ t ∈ T, r t y z
      · obtain ⟨t, ht, h2⟩ := h2
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_filter.2 ⟨hz, h2⟩⟩)
      · push Not at h2
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hz, h1, h2⟩))
    have hcard : L ≤ Zy.card := by
      have h1 := Finset.card_le_card hcov
      have h2 := Finset.card_union_le (Zy ∪ Rt y) (T.biUnion fun t => Rtt t y)
      have h3 := Finset.card_union_le Zy (Rt y)
      have h4 := Finset.card_biUnion_le_card_mul T (fun t => Rtt t y) (m - 1)
        (fun t ht => by have := hRtt t ht; omega)
      rw [hTc] at h4
      have h5 : (M + 1) * (m - 1) = M * (m - 1) + (m - 1) := by ring
      have h6 := hRt
      omega
    obtain ⟨g, hg, hgA⟩ := enum _ (hκ y)
    have hyT : y ∉ T := fun h => lt_irrefl y (lt_trans (show y < p from (hTE h).2) (show p < y from hyE.2))
    refine ⟨x ∘ g, insert y T, Zy, (Finset.filter_subset _ _).trans hZH, hx.comp hg,
      fun i => (hxE _).1, ?_, by rw [Finset.card_insert_of_notMem hyT, hTc], ?_, hcard, ?_⟩
    · intro t ht
      rw [Finset.coe_insert] at ht
      rcases ht with rfl | ht
      · exact hyE.1
      · exact (hTE ht).1
    · intro i t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact lt_trans (hxE (g i)).2 hyE.2
      · exact hxT _ t ht
    · intro z hz a ha b hb hab
      have hzZ := Finset.mem_filter.1 hz
      rw [Finset.coe_insert] at ha hb
      have below : ∀ w ∈ range (x ∘ g) ∪ ↑T, w < p := by
        rintro w (⟨i, rfl⟩ | hw)
        · exact (hxE _).2
        · exact (hTE hw).2
      have sub : ∀ w ∈ range (x ∘ g) ∪ ↑T, w ∈ range x ∪ ↑T := by
        rintro w (⟨i, rfl⟩ | hw)
        · exact Or.inl (mem_range_self _)
        · exact Or.inr hw
      have hb' : b = y ∨ b ∈ range (x ∘ g) ∪ ↑T := by
        rcases hb with hb | hb | hb
        · exact Or.inr (Or.inl hb)
        · exact Or.inl hb
        · exact Or.inr (Or.inr hb)
      have ha' : a = y ∨ a ∈ range (x ∘ g) ∪ ↑T := by
        rcases ha with ha | ha | ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inl ha
        · exact Or.inr (Or.inr ha)
      rcases hb' with rfl | hb'
      · rcases ha' with rfl | ha'
        · exact absurd hab (lt_irrefl _)
        rcases ha' with ⟨i, rfl⟩ | ha'
        · intro hred
          exact hzZ.2.1 ((const b (g i) (hgA i) z hzZ.1).1 hred)
        · exact hzZ.2.2 a ha'
      · rcases ha' with rfl | ha'
        · exact absurd (lt_trans (show p < a from hyE.2) (lt_trans hab (below b hb'))) (lt_irrefl p)
        · exact hPB z hzZ.1 a (sub a ha') b (sub b hb') hab

end E70


namespace E70
open Set

variable {r : ℝ → ℝ → ℝ → Prop}

/-- **Main theorem (Erdős–Rado).** A colouring of the triples of `ℝ` with no blue `K₄` has a
red set of type `ω + m`. -/
theorem main (hK : K4free r) (m : ℕ) : RedOm r m := by
  classical
  by_contra hno
  obtain ⟨Z, hZc, hZred, hD⟩ := tops hK (NN m m 1)
  have split : ∀ E ⊆ D r Z, ¬ E.Countable → Splits r m Z E := by
    intro E hE hEu
    rcases lemV m m 1 Z hZc.ge E hEu with hs | ⟨x, T, ZH, hZH, hx, hxE, hTE, hTc, hxT, hLZ, hPB⟩
    · exact hs
    · exfalso; apply hno
      obtain ⟨z, hz⟩ := Finset.card_pos.1 (by omega : 0 < ZH.card)
      refine ⟨x, T, hx, hTc, hxT, ?_⟩
      intro a ha b hb c hc hab hbc
      have hcE : c ∈ E := by
        rcases hc with ⟨i, rfl⟩ | hc
        · exact hxE i
        · exact hTE hc
      have hcz : c < z := (hE hcE).1 z (hZH hz)
      rcases hK a b c z hab hbc hcz with h | h | h | h
      · exact h
      · exact absurd h (hPB z hz a ha b hb hab)
      · exact absurd h (hPB z hz a ha c hc (hab.trans hbc))
      · exact absurd h (hPB z hz b hb c hc hbc)
  let St := {E : Set ℝ // E ⊆ D r Z ∧ ¬ E.Countable}
  have hsp : ∀ E : St, ∃ h, h ∈ E.1 ∧ ∃ Z', Z' ⊆ Z ∧ Z'.card = m ∧
      ¬ {y ∈ E.1 | h < y ∧ ∀ z ∈ Z', r h y z}.Countable := fun E => by
    obtain ⟨h, hh, Z', hZ', hc, hu⟩ := split E.1 E.2.1 E.2.2
    exact ⟨h, hh, Z', hZ', hc, hu⟩
  choose hf hmem Zf hZsub hZcard hunc using hsp
  let nxt : St → St := fun E => ⟨{y ∈ E.1 | hf E < y ∧ ∀ z ∈ Zf E, r (hf E) y z},
    fun y hy => E.2.1 hy.1, hunc E⟩
  let En : ℕ → St := fun n => nxt^[n] ⟨D r Z, subset_rfl, hD⟩
  let h : ℕ → ℝ := fun n => hf (En n)
  have E_succ : ∀ n, (En (n + 1)).1 ⊆ {y ∈ (En n).1 | h n < y ∧ ∀ z ∈ Zf (En n), r (h n) y z} := by
    intro n y hy
    simp only [En, Function.iterate_succ_apply'] at hy
    exact hy
  have E_anti : ∀ n k, (En (n + k)).1 ⊆ (En n).1 := by
    intro n k; induction k with
    | zero => simp
    | succ k ih => intro u hu; exact ih (E_succ _ (by rwa [← add_assoc] at hu)).1
  have later : ∀ i j, i < j → h i < h j ∧ ∀ z ∈ Zf (En i), r (h i) (h j) z := by
    intro i j hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have := E_anti (i + 1) d (by rw [show i + 1 + d = i + d + 1 by omega]; exact hmem _)
    exact (E_succ i this).2
  have hmono : StrictMono h := fun i j hij => (later i j hij).1
  have hD' : ∀ n, h n ∈ D r Z := fun n => (En n).2.1 (hmem _)
  obtain ⟨b, hb⟩ := inf_fiber (fun n => (⟨Zf (En n), Finset.mem_powerset.2 (hZsub _)⟩ :
    {s // s ∈ Z.powerset}))
  obtain ⟨g, hg, hgI⟩ := enum _ hb
  have hZg : ∀ n, Zf (En (g n)) = b.1 := fun n => congrArg Subtype.val (hgI n)
  obtain ⟨g', hg', hred⟩ := red_subseq hK (h ∘ g) (hmono.comp hg)
  let G := g ∘ g'
  have hG : StrictMono G := hg.comp hg'
  have hZG : ∀ n, Zf (En (G n)) = b.1 := fun n => hZg (g' n)
  have hbZ : b.1 ⊆ Z := Finset.mem_powerset.1 b.2
  have above : ∀ i, ∀ t ∈ b.1, h (G i) < t := fun i t ht => (hD' (G i)).1 t (hbZ ht)
  apply hno
  refine ⟨h ∘ G, b.1, hmono.comp hG, by rw [← hZG 0]; exact hZcard _, above, ?_⟩
  intro a ha c hc d hd hac hcd
  simp only [mem_union, mem_range, Function.comp, Finset.mem_coe] at ha hc hd
  rcases hd with ⟨k, rfl⟩ | hd
  · rcases hc with ⟨j, rfl⟩ | hc
    · rcases ha with ⟨i, rfl⟩ | ha
      · exact hred i j k ((hmono.comp hG).lt_iff_lt.mp hac) ((hmono.comp hG).lt_iff_lt.mp hcd)
      · exact absurd (lt_trans (above j a ha) hac) (lt_irrefl _)
    · exact absurd (lt_trans (above k c hc) hcd) (lt_irrefl _)
  · rcases hc with ⟨j, rfl⟩ | hc
    · rcases ha with ⟨i, rfl⟩ | ha
      · have hij : G i < G j := hG ((hmono.comp hG).lt_iff_lt.mp hac)
        have := (later (G i) (G j) hij).2 d (by rw [hZG]; exact hd)
        exact this
      · exact absurd (lt_trans (above j a ha) hac) (lt_irrefl _)
    · rcases ha with ⟨i, rfl⟩ | ha
      · exact (hD' (G i)).2 c (hbZ hc) d (hbZ hd) hcd
      · exact hZred a (hbZ ha) c (hbZ hc) d (hbZ hd) hac hcd

end E70


namespace E70
open Set Cardinal

/-- A permutation-invariant ternary predicate holds on all distinct triples of `S` once it holds
on all sorted triples. -/
lemma tri_of_sorted (P : ℝ → ℝ → ℝ → Prop)
    (hP : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → (P x y z ↔ P y x z) ∧ (P x y z ↔ P x z y))
    (S : Set ℝ) (h : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c → P a b c) :
    S.Triplewise P := by
  intro x hx y hy z hz hxy hyz hxz
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hyz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hxz with h3 | h3
  · exact h x hx y hy z hz h1 h2
  · exact absurd (h1.trans h2) (not_lt.mpr h3.le)
  · exact (hP x y z hxy hyz hxz).2.mpr (h x hx z hz y hy h3 h2)
  · have := h z hz x hx y hy h3 h1
    rw [(hP x y z hxy hyz hxz).2, (hP x z y hxz hyz.symm hxy).1]
    exact this
  · exact (hP x y z hxy hyz hxz).1.mpr (h y hy x hx z hz h1 h3)
  · have := h y hy z hz x hx h2 h3
    rw [(hP x y z hxy hyz hxz).1, (hP y x z hxy.symm hxz hyz).2]
    exact this
  · exact absurd (h2.trans h1) (not_lt.mpr h3.le)
  · have := h z hz y hy x hx h2 h1
    rw [(hP x y z hxy hyz hxz).1, (hP y x z hxy.symm hxz hyz).2,
      (hP y z x hyz hxz.symm hxy.symm).1]
    exact this

/-- The bridge to the formal statement: `ℝ → (ω + n, 4)³`. -/
theorem erdos_rado_real (n : ℕ) (isRed : ℝ → ℝ → ℝ → Prop)
    (hSym : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧ (isRed x y z ↔ isRed x z y)) :
    (∃ e : (Ordinal.omega0 + (n : Ordinal.{0})).ToType ↪o ℝ, (Set.range e).Triplewise isRed) ∨
    (∃ s : Set ℝ, #s = 4 ∧ s.Triplewise (fun x y z ↦ ¬ isRed x y z)) := by
  classical
  by_cases hblue : ∃ s : Set ℝ, #s = 4 ∧ s.Triplewise (fun x y z ↦ ¬ isRed x y z)
  · exact Or.inr hblue
  left
  have hK : K4free isRed := by
    intro a b c d hab hbc hcd
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3, h4⟩ := hcon
    apply hblue
    refine ⟨↑({a, b, c, d} : Finset ℝ), ?_, ?_⟩
    · have hcard : ({a, b, c, d} : Finset ℝ).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
        · exact ne_of_lt hcd
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨ne_of_lt hbc, ne_of_lt (hbc.trans hcd)⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨ne_of_lt hab, ne_of_lt (hab.trans hbc), ne_of_lt ((hab.trans hbc).trans hcd)⟩
      have hmk := Cardinal.mk_coe_finset (s := ({a, b, c, d} : Finset ℝ))
      rw [hcard] at hmk
      exact_mod_cast hmk
    · refine tri_of_sorted _ (fun x y z hxy hyz hxz =>
        ⟨not_congr (hSym x y z hxy hyz hxz).1, not_congr (hSym x y z hxy hyz hxz).2⟩) _ ?_
      intro u hu v hv w hw huv hvw
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
        mem_singleton_iff] at hu hv hw
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
        rcases hw with rfl | rfl | rfl | rfl <;>
        first | assumption | (exfalso; linarith)
  obtain ⟨x, T, hx, hTc, hxT, hred⟩ := main hK n
  obtain ⟨e, he⟩ := exists_embed n x (fun i => T.orderEmbOfFin hTc i) hx
    (T.orderEmbOfFin hTc).strictMono (fun i j => hxT i _ (T.orderEmbOfFin_mem hTc j))
  refine ⟨e, ?_⟩
  have hr : Set.range (fun i => T.orderEmbOfFin hTc i) = ↑T := Finset.range_orderEmbOfFin _ _
  rw [he, hr]
  exact tri_of_sorted _ hSym _ hred

end E70

theorem OMA.solution : type_of% @Erdos70.erdos_70.variants.erdos_rado := by
  intro n _ isRed hSym
  exact E70.erdos_rado_real n isRed hSym
