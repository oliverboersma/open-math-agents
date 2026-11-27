import FormalConjectures.ErdosProblems.«97»

/-
Erdős Problem 97, general fixed-k variant (refutation).  Submitted by Slash Digital Lab
(GitHub: JamesSlash).
Upstream: formal-conjectures FormalConjectures/ErdosProblems/97.lean,
declaration Erdos97.erdos_97.variants.k_equidistant.

ATTRIBUTION.  This is an independent formalization of a known result, not a new discovery.
The general fixed-k conjecture was disproved by L. Kruer, J. Kohlmeyer and L. Price, 'Unit
distances in convex polygons' (September 2026, github.com/lkruer/erdos-96-97-proof;
erdosproblems.com/97): for every k there is a strictly convex polygon in which every vertex has
k other vertices at distance one.  The construction used below is theirs: seed points near -i/2
and +i/2 indexed by subsets with base-5 labels, multiplied by products of small rotations about
the origin, one rotation per edge, chosen so that the two endpoints of an edge are at distance
exactly one.  Only the mathematics of their paper was used; this file shares no code with their
Lean development.

What is organised differently here:
* the point set is an image, so no genericity (distinct products) lemma is needed: distinctness of
  the neighbours follows from the supporting-line inequality `Hh x y < 0`;
* no edge count and no vertex deletion: exponent vectors take values in {0, 1, 2}; an edge
  (A, B) carries `2 - a` tokens on the side of A and `a` on the side of B, and the states whose
  current vertex holds at least 2k - 1 tokens while every other vertex holds at least 2k - 2 form
  a closed family in which every point has at least k unit neighbours (subsets of sizes 2k and
  2k + 1 of a 4k-element set are enough);
* no explicit constants: every analytic requirement is continuous in the scale `ε` and strict at
  `ε = 0`, so a single `eventually` argument selects `ε`.

Structure: `core` (abstract construction in the complex plane), `digit` (base-5 inequality),
`exists_rot` (correcting rotation by the intermediate value theorem), `exists_config`
(the instance for a given k), `transfer` (complex plane to the Euclidean plane).
-/

open Finset

namespace EK

/-- The support functional `⟨x, y - x⟩`. -/
noncomputable def Hh (x y : ℂ) : ℝ := (starRingEnd ℂ x * (y - x)).re

lemma Hh_apply (x y : ℂ) : Hh x y = x.re * (y.re - x.re) + x.im * (y.im - x.im) := by
  simp only [Hh, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring

lemma Hh_self (x : ℂ) : Hh x x = 0 := by
  rw [Hh_apply]; ring

lemma Hh_eq_norm {x y : ℂ} (h : ‖x‖ = ‖y‖) (hne : x ≠ y) : Hh x y < 0 := by
  have h1 : 2 * Hh x y = Complex.normSq y - Complex.normSq x - Complex.normSq (y - x) := by
    rw [Hh_apply]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have h2 : Complex.normSq y = Complex.normSq x := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]
  have h3 : 0 < Complex.normSq (y - x) := Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  linarith

lemma Hh_rot {z z' u u' : ℂ} (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1) (hu : ‖u‖ = 1) :
    Hh (z * u) (z' * u') ≤ Hh z z' + ‖u - 1‖ + ‖u' - 1‖ := by
  have hcu : starRingEnd ℂ u * u = 1 := by
    rw [Complex.conj_mul', hu]; simp
  have key : starRingEnd ℂ (z * u) * (z' * u' - z * u) =
      starRingEnd ℂ z * (z' - z) + starRingEnd ℂ z * z' * (starRingEnd ℂ u * (u' - u)) := by
    simp only [map_mul]
    linear_combination (starRingEnd ℂ z * z' - starRingEnd ℂ z * z) * hcu
  have h1 : Hh (z * u) (z' * u') =
      Hh z z' + (starRingEnd ℂ z * z' * (starRingEnd ℂ u * (u' - u))).re := by
    unfold Hh; rw [key, Complex.add_re]
  have h2 : (starRingEnd ℂ z * z' * (starRingEnd ℂ u * (u' - u))).re ≤ ‖u' - u‖ := by
    have hn : ‖starRingEnd ℂ z * z' * (starRingEnd ℂ u * (u' - u))‖ = ‖z‖ * ‖z'‖ * ‖u' - u‖ := by
      rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj, hu, one_mul]
    have hle : ‖z‖ * ‖z'‖ * ‖u' - u‖ ≤ ‖u' - u‖ := by
      have h0 : 0 ≤ ‖u' - u‖ := norm_nonneg _
      have hzz : ‖z‖ * ‖z'‖ ≤ 1 := by
        have := mul_le_mul hz hz' (norm_nonneg _) zero_le_one
        simpa using this
      nlinarith
    calc _ ≤ ‖starRingEnd ℂ z * z' * (starRingEnd ℂ u * (u' - u))‖ := Complex.re_le_norm _
      _ = ‖z‖ * ‖z'‖ * ‖u' - u‖ := hn
      _ ≤ ‖u' - u‖ := hle
  have h3 : ‖u' - u‖ ≤ ‖u' - 1‖ + ‖u - 1‖ := by
    have : u' - u = (u' - 1) - (u - 1) := by ring
    rw [this]; exact norm_sub_le _ _
  linarith

lemma norm_prod_sub_one_le {E : Type} (s : Finset E) (f : E → ℂ) (hf : ∀ e ∈ s, ‖f e‖ = 1) :
    ‖∏ e ∈ s, f e - 1‖ ≤ ∑ e ∈ s, ‖f e - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    have h1 : ‖f x‖ = 1 := hf x (Finset.mem_insert_self _ _)
    have ih' := ih (fun e he => hf e (Finset.mem_insert_of_mem he))
    have h2 : f x * ∏ e ∈ s, f e - 1 = f x * (∏ e ∈ s, f e - 1) + (f x - 1) := by ring
    rw [h2]
    calc ‖f x * (∏ e ∈ s, f e - 1) + (f x - 1)‖
        ≤ ‖f x * (∏ e ∈ s, f e - 1)‖ + ‖f x - 1‖ := norm_add_le _ _
      _ = ‖∏ e ∈ s, f e - 1‖ + ‖f x - 1‖ := by rw [norm_mul, h1, one_mul]
      _ ≤ ‖f x - 1‖ + ∑ e ∈ s, ‖f e - 1‖ := by linarith

lemma norm_pow_sub_one_le (w : ℂ) (hw : ‖w‖ = 1) (k : ℕ) : ‖w ^ k - 1‖ ≤ k * ‖w - 1‖ := by
  have h := norm_prod_sub_one_le (Finset.range k) (fun _ => w) (fun _ _ => hw)
  simpa using h

section core

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- The product of rotations attached to an exponent vector. -/
noncomputable def Wp (Es : Finset E) (w : E → ℂ) (a : E → Fin 3) : ℂ := ∏ e ∈ Es, w e ^ (a e : ℕ)

omit [DecidableEq E] in
lemma norm_Wp (Es : Finset E) (w : E → ℂ) (hw : ∀ e ∈ Es, ‖w e‖ = 1) (a : E → Fin 3) :
    ‖Wp Es w a‖ = 1 := by
  unfold Wp
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro e he
  rw [norm_pow, hw e he, one_pow]

omit [DecidableEq E] in
lemma norm_Wp_sub_one (Es : Finset E) (w : E → ℂ) (hw : ∀ e ∈ Es, ‖w e‖ = 1) (a : E → Fin 3) :
    ‖Wp Es w a - 1‖ ≤ 2 * ∑ e ∈ Es, ‖w e - 1‖ := by
  unfold Wp
  have h1 := norm_prod_sub_one_le Es (fun e => w e ^ (a e : ℕ))
    (fun e he => by rw [norm_pow, hw e he, one_pow])
  have h2 : ∑ e ∈ Es, ‖w e ^ (a e : ℕ) - 1‖ ≤ ∑ e ∈ Es, 2 * ‖w e - 1‖ := by
    apply Finset.sum_le_sum
    intro e he
    have h3 := norm_pow_sub_one_le (w e) (hw e he) (a e : ℕ)
    have h4 : ((a e : ℕ) : ℝ) ≤ 2 := by
      have : (a e : ℕ) ≤ 2 := by omega
      exact_mod_cast this
    have h5 : 0 ≤ ‖w e - 1‖ := norm_nonneg _
    nlinarith
  rw [Finset.mul_sum]
  exact le_trans h1 h2

lemma Wp_update (Es : Finset E) (w : E → ℂ) (a : E → Fin 3) (e : E) (he : e ∈ Es) (c : Fin 3) :
    Wp Es w (Function.update a e c) * w e ^ (a e : ℕ) = Wp Es w a * w e ^ (c : ℕ) := by
  unfold Wp
  rw [← Finset.mul_prod_erase Es _ he, ← Finset.mul_prod_erase Es _ he]
  have h : ∏ x ∈ Es.erase e, w x ^ ((Function.update a e c x : Fin 3) : ℕ)
      = ∏ x ∈ Es.erase e, w x ^ (a x : ℕ) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [h, Function.update_self]
  ring

/-- Tokens on the side of `u`. -/
def tok (Es : Finset E) (src dst : E → V) (u : V) (a : E → Fin 3) : ℕ :=
  ∑ e ∈ Es, ((if src e = u then 2 - (a e : ℕ) else 0) + (if dst e = u then (a e : ℕ) else 0))

lemma tok_update (Es : Finset E) (src dst : E → V) (u : V) (a : E → Fin 3) (e : E) (he : e ∈ Es)
    (c : Fin 3) :
    tok Es src dst u (Function.update a e c)
        + ((if src e = u then 2 - (a e : ℕ) else 0) + (if dst e = u then (a e : ℕ) else 0))
      = tok Es src dst u a
        + ((if src e = u then 2 - (c : ℕ) else 0) + (if dst e = u then (c : ℕ) else 0)) := by
  unfold tok
  rw [← Finset.add_sum_erase Es _ he, ← Finset.add_sum_erase Es _ he]
  have h : ∑ x ∈ Es.erase e, ((if src x = u then 2 - ((Function.update a e c x : Fin 3) : ℕ) else 0)
        + (if dst x = u then ((Function.update a e c x : Fin 3) : ℕ) else 0))
      = ∑ x ∈ Es.erase e, ((if src x = u then 2 - (a x : ℕ) else 0)
        + (if dst x = u then (a x : ℕ) else 0)) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [h, Function.update_self]
  ring

/-- The point attached to a state. -/
noncomputable def pt (Es : Finset E) (b : V → ℂ) (w : E → ℂ) (s : V × (E → Fin 3)) : ℂ :=
  b s.1 * Wp Es w s.2

/-- The invariant. -/
def Good (k : ℕ) (Es : Finset E) (src dst : E → V) (s : V × (E → Fin 3)) : Prop :=
  2 * k - 1 ≤ tok Es src dst s.1 s.2 ∧
    ∀ u, u ≠ s.1 → (∃ e ∈ Es, src e = u ∨ dst e = u) → 2 * k - 2 ≤ tok Es src dst u s.2

/-- one step up -/
def up (x : Fin 3) : Fin 3 := ⟨min ((x : ℕ) + 1) 2, by omega⟩
/-- one step down -/
def dn (x : Fin 3) : Fin 3 := ⟨(x : ℕ) - 1, by omega⟩

lemma good_out (k : ℕ) (hk : 1 ≤ k) (Es : Finset E) (src dst : E → V) (b : V → ℂ) (w : E → ℂ)
    (hw : ∀ e ∈ Es, ‖w e‖ = 1)
    (hunit : ∀ e ∈ Es, ‖b (src e) - b (dst e) * w e‖ = 1)
    (hbip : ∀ e ∈ Es, ∀ e' ∈ Es, src e ≠ dst e')
    (s : V × (E → Fin 3)) (hs : Good k Es src dst s) (e : E) (he : e ∈ Es)
    (hsrc : src e = s.1) (hle : (s.2 e : ℕ) ≤ 1) :
    Good k Es src dst (dst e, Function.update s.2 e (up (s.2 e))) ∧
      ‖pt Es b w s - pt Es b w (dst e, Function.update s.2 e (up (s.2 e)))‖ = 1 := by
  obtain ⟨v, a⟩ := s
  simp only at hsrc hle
  have hc : ((up (a e) : Fin 3) : ℕ) = (a e : ℕ) + 1 := by
    simp only [up]; omega
  have hne : src e ≠ dst e := hbip e he e he
  constructor
  · constructor
    · -- the arrival vertex gains one token
      have h := tok_update Es src dst (dst e) a e he (up (a e))
      have h6 : 2 * k - 2 ≤ tok Es src dst (dst e) a :=
        hs.2 (dst e) (by rw [← hsrc]; exact fun h => hne h.symm) ⟨e, he, Or.inr rfl⟩
      rw [if_neg hne, if_pos rfl, if_neg hne, if_pos rfl, hc] at h
      show 2 * k - 1 ≤ tok Es src dst (dst e) (Function.update a e (up (a e)))
      omega
    · intro u hu hend
      have h := tok_update Es src dst u a e he (up (a e))
      have hdu : dst e ≠ u := fun h => hu h.symm
      rw [if_neg hdu, if_neg hdu, hc] at h
      show 2 * k - 2 ≤ tok Es src dst u (Function.update a e (up (a e)))
      by_cases hsu : src e = u
      · rw [if_pos hsu, if_pos hsu] at h
        have h7 : 2 * k - 1 ≤ tok Es src dst u a := by rw [← hsu, hsrc]; exact hs.1
        omega
      · rw [if_neg hsu, if_neg hsu] at h
        have h6 : 2 * k - 2 ≤ tok Es src dst u a := hs.2 u (by rw [← hsrc]; exact fun h => hsu h.symm) hend
        omega
  · have hwne : w e ≠ 0 := by
      intro h0
      have := hw e he
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hW : Wp Es w (Function.update a e (up (a e))) = Wp Es w a * w e := by
      have h := Wp_update Es w a e he (up (a e))
      rw [hc, pow_succ] at h
      have hp : w e ^ (a e : ℕ) ≠ 0 := pow_ne_zero _ hwne
      apply mul_right_cancel₀ hp
      rw [h]; ring
    have h1 : pt Es b w (v, a) - pt Es b w (dst e, Function.update a e (up (a e)))
        = Wp Es w a * (b (src e) - b (dst e) * w e) := by
      simp only [pt]
      rw [hW, hsrc]; ring
    rw [h1, norm_mul, norm_Wp Es w hw, hunit e he, mul_one]

lemma good_in (k : ℕ) (hk : 1 ≤ k) (Es : Finset E) (src dst : E → V) (b : V → ℂ) (w : E → ℂ)
    (hw : ∀ e ∈ Es, ‖w e‖ = 1)
    (hunit : ∀ e ∈ Es, ‖b (src e) - b (dst e) * w e‖ = 1)
    (hbip : ∀ e ∈ Es, ∀ e' ∈ Es, src e ≠ dst e')
    (s : V × (E → Fin 3)) (hs : Good k Es src dst s) (e : E) (he : e ∈ Es)
    (hdst : dst e = s.1) (hge : 1 ≤ (s.2 e : ℕ)) :
    Good k Es src dst (src e, Function.update s.2 e (dn (s.2 e))) ∧
      ‖pt Es b w s - pt Es b w (src e, Function.update s.2 e (dn (s.2 e)))‖ = 1 := by
  obtain ⟨v, a⟩ := s
  simp only at hdst hge
  have hc : ((dn (a e) : Fin 3) : ℕ) = (a e : ℕ) - 1 := rfl
  have hne : src e ≠ dst e := hbip e he e he
  have hlt : (a e : ℕ) < 3 := (a e).isLt
  constructor
  · constructor
    · have h := tok_update Es src dst (src e) a e he (dn (a e))
      have h6 : 2 * k - 2 ≤ tok Es src dst (src e) a :=
        hs.2 (src e) (by rw [← hdst]; exact hne) ⟨e, he, Or.inl rfl⟩
      rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl, if_neg (Ne.symm hne), hc] at h
      show 2 * k - 1 ≤ tok Es src dst (src e) (Function.update a e (dn (a e)))
      omega
    · intro u hu hend
      have h := tok_update Es src dst u a e he (dn (a e))
      have hsu : src e ≠ u := fun h => hu h.symm
      rw [if_neg hsu, if_neg hsu, hc] at h
      show 2 * k - 2 ≤ tok Es src dst u (Function.update a e (dn (a e)))
      by_cases hdu : dst e = u
      · rw [if_pos hdu, if_pos hdu] at h
        have h7 : 2 * k - 1 ≤ tok Es src dst u a := by rw [← hdu, hdst]; exact hs.1
        omega
      · rw [if_neg hdu, if_neg hdu] at h
        have h6 : 2 * k - 2 ≤ tok Es src dst u a := hs.2 u (by rw [← hdst]; exact fun h => hdu h.symm) hend
        omega
  · have hwne : w e ≠ 0 := by
      intro h0
      have := hw e he
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hW : Wp Es w (Function.update a e (dn (a e))) * w e = Wp Es w a := by
      have h := Wp_update Es w a e he (dn (a e))
      rw [hc] at h
      have hp : w e ^ ((a e : ℕ) - 1) ≠ 0 := pow_ne_zero _ hwne
      have hpow : w e ^ (a e : ℕ) = w e ^ ((a e : ℕ) - 1) * w e := by
        rw [← pow_succ]; congr 1; omega
      rw [hpow] at h
      apply mul_right_cancel₀ hp
      rw [← h]; ring
    have h1 : pt Es b w (v, a) - pt Es b w (src e, Function.update a e (dn (a e)))
        = -(Wp Es w (Function.update a e (dn (a e))) * (b (src e) - b (dst e) * w e)) := by
      simp only [pt]
      rw [← hW, hdst]; ring
    rw [h1, norm_neg, norm_mul, norm_Wp Es w hw, hunit e he, mul_one]

end core


section core2

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma Hh_neg_of_ne (Es : Finset E) (b : V → ℂ) (w : E → ℂ)
    (hw : ∀ e ∈ Es, ‖w e‖ = 1) (hb : ∀ v, ‖b v‖ ≤ 1)
    (hmargin : ∀ v v', v ≠ v' → Hh (b v) (b v') + 4 * ∑ e ∈ Es, ‖w e - 1‖ < 0)
    (s s' : V × (E → Fin 3)) (hne : s.1 ≠ s'.1) : Hh (pt Es b w s) (pt Es b w s') < 0 := by
  have h1 := Hh_rot (u' := Wp Es w s'.2) (hb s.1) (hb s'.1) (norm_Wp Es w hw s.2)
  have h2 := norm_Wp_sub_one Es w hw s.2
  have h3 := norm_Wp_sub_one Es w hw s'.2
  have h4 := hmargin s.1 s'.1 hne
  simp only [pt]
  linarith

theorem core (k : ℕ) (hk : 1 ≤ k) (Es : Finset E) (src dst : E → V) (b : V → ℂ) (w : E → ℂ) (v0 : V)
    (hw : ∀ e ∈ Es, ‖w e‖ = 1)
    (hunit : ∀ e ∈ Es, ‖b (src e) - b (dst e) * w e‖ = 1)
    (hb : ∀ v, ‖b v‖ ≤ 1)
    (hmargin : ∀ v v', v ≠ v' → Hh (b v) (b v') + 4 * ∑ e ∈ Es, ‖w e - 1‖ < 0)
    (hsimple : ∀ e ∈ Es, ∀ e' ∈ Es, src e = src e' → dst e = dst e' → e = e')
    (hbip : ∀ e ∈ Es, ∀ e' ∈ Es, src e ≠ dst e')
    (h7 : 2 * k - 1 ≤ tok Es src dst v0 (fun _ => 1))
    (h6 : ∀ u, (∃ e ∈ Es, src e = u ∨ dst e = u) → 2 * k - 2 ≤ tok Es src dst u (fun _ => 1)) :
    ∃ P : Finset ℂ, P.Nonempty ∧ (∀ x ∈ P, ∀ y ∈ P, x ≠ y → Hh x y < 0) ∧
      ∀ x ∈ P, ∃ Q : Finset ℂ, Q ⊆ P ∧ k ≤ Q.card ∧ ∀ y ∈ Q, ‖x - y‖ = 1 := by
  classical
  refine ⟨(Finset.univ.filter (fun s : V × (E → Fin 3) => Good k Es src dst s)).image (pt Es b w),
    ?_, ?_, ?_⟩
  · refine ⟨pt Es b w (v0, fun _ => 1), Finset.mem_image.mpr ⟨(v0, fun _ => 1), ?_, rfl⟩⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h7, fun u _ hu => h6 u hu⟩
  · intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hy
    by_cases hss : s.1 = s'.1
    · apply Hh_eq_norm _ hxy
      simp only [pt]
      rw [norm_mul, norm_mul, norm_Wp Es w hw, norm_Wp Es w hw, hss]
    · exact Hh_neg_of_ne Es b w hw hb hmargin s s' hss
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    have hsG : Good k Es src dst s := (Finset.mem_filter.mp hs).2
    let Av : Finset E := Es.filter
      (fun e => (src e = s.1 ∧ (s.2 e : ℕ) ≤ 1) ∨ (dst e = s.1 ∧ 1 ≤ (s.2 e : ℕ)))
    let nb : E → V × (E → Fin 3) := fun e =>
      if src e = s.1 then (dst e, Function.update s.2 e (up (s.2 e)))
      else (src e, Function.update s.2 e (dn (s.2 e)))
    have hnb : ∀ e ∈ Av, Good k Es src dst (nb e) ∧ ‖pt Es b w s - pt Es b w (nb e)‖ = 1 ∧
        (nb e).1 = (if src e = s.1 then dst e else src e) := by
      intro e he
      obtain ⟨heE, hcase⟩ := Finset.mem_filter.mp he
      by_cases h1 : src e = s.1
      · have hle : (s.2 e : ℕ) ≤ 1 := by
          rcases hcase with h | h
          · exact h.2
          · exact absurd (h1.trans h.1.symm) (hbip e heE e heE)
        have hgo := good_out k hk Es src dst b w hw hunit hbip s hsG e heE h1 hle
        simp only [nb, if_pos h1]
        exact ⟨hgo.1, hgo.2, trivial⟩
      · have hd : dst e = s.1 ∧ 1 ≤ (s.2 e : ℕ) := by
          rcases hcase with h | h
          · exact absurd h.1 h1
          · exact h
        have hgi := good_in k hk Es src dst b w hw hunit hbip s hsG e heE hd.1 hd.2
        simp only [nb, if_neg h1]
        exact ⟨hgi.1, hgi.2, trivial⟩
    have hinj : Set.InjOn (fun e => pt Es b w (nb e)) (Av : Set E) := by
      intro e he e' he' heq
      by_contra hne
      have hdiff : (nb e).1 ≠ (nb e').1 := by
        obtain ⟨heE, hcase⟩ := Finset.mem_filter.mp he
        obtain ⟨heE', hcase'⟩ := Finset.mem_filter.mp he'
        rw [(hnb e he).2.2, (hnb e' he').2.2]
        by_cases h1 : src e = s.1 <;> by_cases h1' : src e' = s.1
        · rw [if_pos h1, if_pos h1']
          intro hd
          exact hne (hsimple e heE e' heE' (h1.trans h1'.symm) hd)
        · rw [if_pos h1, if_neg h1']
          exact fun hd => hbip e' heE' e heE hd.symm
        · rw [if_neg h1, if_pos h1']
          exact fun hd => hbip e heE e' heE' hd
        · rw [if_neg h1, if_neg h1']
          have hd : dst e = s.1 := by
            rcases hcase with h | h
            · exact absurd h.1 h1
            · exact h.1
          have hd' : dst e' = s.1 := by
            rcases hcase' with h | h
            · exact absurd h.1 h1'
            · exact h.1
          intro hs'
          exact hne (hsimple e heE e' heE' hs' (hd.trans hd'.symm))
      have hneg := Hh_neg_of_ne Es b w hw hb hmargin (nb e) (nb e') hdiff
      have heq' : pt Es b w (nb e) = pt Es b w (nb e') := heq
      rw [heq', Hh_self] at hneg
      exact lt_irrefl _ hneg
    have hcard : k ≤ Av.card := by
      have hsum : tok Es src dst s.1 s.2 ≤ 2 * Av.card := by
        unfold tok
        rw [Finset.card_filter, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro e he
        have hlt : (s.2 e : ℕ) < 3 := (s.2 e).isLt
        have hne : src e ≠ dst e := hbip e he e he
        by_cases h1 : src e = s.1
        · have h2 : dst e ≠ s.1 := fun h => hne (h1.trans h.symm)
          rw [if_pos h1, if_neg h2]
          by_cases h3 : (s.2 e : ℕ) ≤ 1
          · rw [if_pos (Or.inl ⟨h1, h3⟩)]; omega
          · rw [if_neg (by
              rintro (h | h)
              · exact h3 h.2
              · exact h2 h.1)]
            omega
        · rw [if_neg h1]
          by_cases h2 : dst e = s.1
          · rw [if_pos h2]
            by_cases h3 : 1 ≤ (s.2 e : ℕ)
            · rw [if_pos (Or.inr ⟨h2, h3⟩)]; omega
            · rw [if_neg (by
                rintro (h | h)
                · exact h1 h.1
                · exact h3 h.2)]
              omega
          · rw [if_neg h2, if_neg (by
              rintro (h | h)
              · exact h1 h.1
              · exact h2 h.1)]
            omega
      have h7' := hsG.1
      omega
    refine ⟨Av.image (fun e => pt Es b w (nb e)), ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr
        ⟨nb e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hnb e he).1⟩, rfl⟩
    · rw [Finset.card_image_of_injOn hinj]; exact hcard
    · intro y hy
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
      exact (hnb e he).2.1

end core2


section digits

/-- base-5 label of a finite set of naturals -/
noncomputable def XN (A : Finset ℕ) : ℝ := ∑ j ∈ A, (5 : ℝ) ^ j
/-- base-25 label of a finite set of naturals -/
noncomputable def TN (A : Finset ℕ) : ℝ := ∑ j ∈ A, (25 : ℝ) ^ j

lemma digit_aux (A B : Finset ℕ) (h : ℕ) (hA : h ∈ A) (hB : h ∉ B)
    (h1 : ∀ j ∈ A \ B, j ≤ h) (h2 : ∀ j ∈ B \ A, j < h) :
    |TN A - TN B| < 2 * (XN A - XN B) ^ 2 := by
  have hX : XN A - XN B = ∑ j ∈ A \ B, (5 : ℝ) ^ j - ∑ j ∈ B \ A, (5 : ℝ) ^ j := by
    unfold XN; exact Finset.sum_sdiff_sub_sum_sdiff.symm
  have hT : TN A - TN B = ∑ j ∈ A \ B, (25 : ℝ) ^ j - ∑ j ∈ B \ A, (25 : ℝ) ^ j := by
    unfold TN; exact Finset.sum_sdiff_sub_sum_sdiff.symm
  have hsub1 : A \ B ⊆ Finset.range (h + 1) :=
    fun j hj => Finset.mem_range.mpr (Nat.lt_succ_of_le (h1 j hj))
  have hsub2 : B \ A ⊆ Finset.range h := fun j hj => Finset.mem_range.mpr (h2 j hj)
  have g5 : ∀ n : ℕ, ∑ j ∈ Finset.range n, (5 : ℝ) ^ j = ((5 : ℝ) ^ n - 1) / 4 := by
    intro n
    rw [geom_sum_eq (by norm_num) n]; norm_num
  have g25 : ∀ n : ℕ, ∑ j ∈ Finset.range n, (25 : ℝ) ^ j = ((25 : ℝ) ^ n - 1) / 24 := by
    intro n
    rw [geom_sum_eq (by norm_num) n]; norm_num
  have a1 : (5 : ℝ) ^ h ≤ ∑ j ∈ A \ B, (5 : ℝ) ^ j :=
    Finset.single_le_sum (f := fun j => (5 : ℝ) ^ j) (fun j _ => by positivity)
      (Finset.mem_sdiff.mpr ⟨hA, hB⟩)
  have a2 : ∑ j ∈ B \ A, (5 : ℝ) ^ j ≤ ((5 : ℝ) ^ h - 1) / 4 := by
    rw [← g5]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun j _ _ => by positivity)
  have b1 : ∑ j ∈ A \ B, (25 : ℝ) ^ j ≤ ((25 : ℝ) ^ (h + 1) - 1) / 24 := by
    rw [← g25]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun j _ _ => by positivity)
  have b2 : ∑ j ∈ B \ A, (25 : ℝ) ^ j ≤ ((25 : ℝ) ^ h - 1) / 24 := by
    rw [← g25]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun j _ _ => by positivity)
  have b1' : 0 ≤ ∑ j ∈ A \ B, (25 : ℝ) ^ j := Finset.sum_nonneg (fun j _ => by positivity)
  have b2' : 0 ≤ ∑ j ∈ B \ A, (25 : ℝ) ^ j := Finset.sum_nonneg (fun j _ => by positivity)
  have h25 : (25 : ℝ) ^ h = ((5 : ℝ) ^ h) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h25' : (25 : ℝ) ^ (h + 1) = 25 * ((5 : ℝ) ^ h) ^ 2 := by
    rw [pow_succ, h25]; ring
  have hp : (1 : ℝ) ≤ (5 : ℝ) ^ h := one_le_pow₀ (by norm_num)
  rw [h25'] at b1
  rw [h25] at b2
  rw [hX, hT]
  have hd : (3 * (5 : ℝ) ^ h + 1) / 4 ≤
      ∑ j ∈ A \ B, (5 : ℝ) ^ j - ∑ j ∈ B \ A, (5 : ℝ) ^ j := by linarith
  have hsq : ((3 * (5 : ℝ) ^ h + 1) / 4) ^ 2 ≤
      (∑ j ∈ A \ B, (5 : ℝ) ^ j - ∑ j ∈ B \ A, (5 : ℝ) ^ j) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hd 2
  rw [abs_lt]
  constructor
  · nlinarith [sq_nonneg ((5 : ℝ) ^ h)]
  · nlinarith [sq_nonneg ((5 : ℝ) ^ h)]

lemma digit (A B : Finset ℕ) (hAB : A ≠ B) : |TN A - TN B| < 2 * (XN A - XN B) ^ 2 := by
  have hne : ((A \ B) ∪ (B \ A)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hAB
    have h' := Finset.union_eq_empty.mp h
    exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h'.1)
      (Finset.sdiff_eq_empty_iff_subset.mp h'.2)
  have hmem : ((A \ B) ∪ (B \ A)).max' hne ∈ (A \ B) ∪ (B \ A) := Finset.max'_mem _ _
  have hmax : ∀ j ∈ (A \ B) ∪ (B \ A), j ≤ ((A \ B) ∪ (B \ A)).max' hne :=
    fun j hj => Finset.le_max' _ j hj
  rcases Finset.mem_union.mp hmem with h1 | h1
  · have hA := (Finset.mem_sdiff.mp h1).1
    have hB := (Finset.mem_sdiff.mp h1).2
    apply digit_aux A B _ hA hB
    · intro j hj
      exact hmax j (Finset.mem_union_left _ hj)
    · intro j hj
      have hle := hmax j (Finset.mem_union_right _ hj)
      have hjne : j ≠ ((A \ B) ∪ (B \ A)).max' hne := by
        intro hEq
        rw [hEq] at hj
        exact (Finset.mem_sdiff.mp hj).2 hA
      omega
  · have hB := (Finset.mem_sdiff.mp h1).1
    have hA := (Finset.mem_sdiff.mp h1).2
    have key := digit_aux B A _ hB hA
      (fun j hj => hmax j (Finset.mem_union_right _ hj))
      (fun j hj => by
        have hle := hmax j (Finset.mem_union_left _ hj)
        have hjne : j ≠ ((A \ B) ∪ (B \ A)).max' hne := by
          intro hEq
          rw [hEq] at hj
          exact (Finset.mem_sdiff.mp hj).2 hB
        omega)
    rw [abs_sub_comm, show (XN A - XN B) ^ 2 = (XN B - XN A) ^ 2 by ring]
    exact key

end digits

section seeds

variable {n : ℕ}

/-- first label of a subset of `Fin n` -/
noncomputable def X (A : Finset (Fin n)) : ℝ := ∑ j ∈ A, (5 : ℝ) ^ (j : ℕ)
/-- second label of a subset of `Fin n` -/
noncomputable def T (A : Finset (Fin n)) : ℝ := ∑ j ∈ A, (25 : ℝ) ^ (j : ℕ)

lemma X_eq (A : Finset (Fin n)) : X A = XN (A.map Fin.valEmbedding) := by
  unfold X XN; rw [Finset.sum_map]; rfl

lemma T_eq (A : Finset (Fin n)) : T A = TN (A.map Fin.valEmbedding) := by
  unfold T TN; rw [Finset.sum_map]; rfl

lemma digit12 (A B : Finset (Fin n)) (h : A ≠ B) : |T A - T B| < 2 * (X A - X B) ^ 2 := by
  rw [X_eq, X_eq, T_eq, T_eq]
  exact digit _ _ (fun h' => h (Finset.map_injective _ h'))

lemma X_insert (A : Finset (Fin n)) (j : Fin n) (hj : j ∉ A) :
    X (insert j A) = X A + (5 : ℝ) ^ (j : ℕ) := by
  unfold X; rw [Finset.sum_insert hj]; ring

lemma T_insert (A : Finset (Fin n)) (j : Fin n) (hj : j ∉ A) :
    T (insert j A) = T A + ((5 : ℝ) ^ (j : ℕ)) ^ 2 := by
  have h25 : (25 : ℝ) ^ (j : ℕ) = ((5 : ℝ) ^ (j : ℕ)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  unfold T; rw [Finset.sum_insert hj, h25]; ring

/-- lower seed -/
noncomputable def low (ε x t : ℝ) : ℂ := ⟨ε * x, -1 / 2 + ε ^ 2 * (x ^ 2 + t / 2)⟩
/-- upper seed -/
noncomputable def upp (ε y u : ℝ) : ℂ := ⟨-(ε * y), 1 / 2 + ε ^ 2 * (-(y ^ 2) + u / 2)⟩

/-- the seed attached to a subset -/
noncomputable def seed (s : ℕ) (ε : ℝ) (A : Finset (Fin n)) : ℂ :=
  if A.card ≤ s then low ε (X A) (T A) else upp ε (X A) (T A)

/-- the fourth-order defect of an edge -/
noncomputable def Mf (x t z : ℝ) : ℝ := (-((x + z) ^ 2) + (t + z ^ 2) / 2) - (x ^ 2 + t / 2)

lemma Hh_low_low (ε x t x' t' : ℝ) : Hh (low ε x t) (low ε x' t') =
    ε ^ 2 * (-((x' - x) ^ 2 / 2 + (t' - t) / 4)
      + ε ^ 2 * ((x ^ 2 + t / 2) * ((x' ^ 2 + t' / 2) - (x ^ 2 + t / 2)))) := by
  rw [Hh_apply]; simp only [low]; ring

lemma Hh_upp_upp (ε y u y' u' : ℝ) : Hh (upp ε y u) (upp ε y' u') =
    ε ^ 2 * (-((y' - y) ^ 2 / 2 - (u' - u) / 4)
      + ε ^ 2 * ((-(y ^ 2) + u / 2) * ((-(y' ^ 2) + u' / 2) - (-(y ^ 2) + u / 2)))) := by
  rw [Hh_apply]; simp only [upp]; ring

lemma ev_low (K x t x' t' : ℝ) (hq : 0 < (x' - x) ^ 2 / 2 + (t' - t) / 4) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), Hh (low ε x t) (low ε x' t') + ε ^ 3 * K < 0 := by
  have hc : ContinuousAt (fun ε : ℝ => -((x' - x) ^ 2 / 2 + (t' - t) / 4)
      + ε ^ 2 * ((x ^ 2 + t / 2) * ((x' ^ 2 + t' / 2) - (x ^ 2 + t / 2))) + ε * K) 0 := by
    fun_prop
  have h0 : ∀ᶠ ε in nhds (0 : ℝ), -((x' - x) ^ 2 / 2 + (t' - t) / 4)
      + ε ^ 2 * ((x ^ 2 + t / 2) * ((x' ^ 2 + t' / 2) - (x ^ 2 + t / 2))) + ε * K < 0 := by
    apply hc.eventually_lt continuousAt_const
    norm_num; linarith
  filter_upwards [nhdsWithin_le_nhds h0, self_mem_nhdsWithin] with ε hε hpos
  have hpos' : (0 : ℝ) < ε := hpos
  rw [Hh_low_low]
  have h2 : (0 : ℝ) < ε ^ 2 := by positivity
  nlinarith [mul_neg_of_pos_of_neg h2 hε]

lemma ev_upp (K y u y' u' : ℝ) (hq : 0 < (y' - y) ^ 2 / 2 - (u' - u) / 4) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), Hh (upp ε y u) (upp ε y' u') + ε ^ 3 * K < 0 := by
  have hc : ContinuousAt (fun ε : ℝ => -((y' - y) ^ 2 / 2 - (u' - u) / 4)
      + ε ^ 2 * ((-(y ^ 2) + u / 2) * ((-(y' ^ 2) + u' / 2) - (-(y ^ 2) + u / 2))) + ε * K) 0 := by
    fun_prop
  have h0 : ∀ᶠ ε in nhds (0 : ℝ), -((y' - y) ^ 2 / 2 - (u' - u) / 4)
      + ε ^ 2 * ((-(y ^ 2) + u / 2) * ((-(y' ^ 2) + u' / 2) - (-(y ^ 2) + u / 2))) + ε * K < 0 := by
    apply hc.eventually_lt continuousAt_const
    norm_num; linarith
  filter_upwards [nhdsWithin_le_nhds h0, self_mem_nhdsWithin] with ε hε hpos
  have hpos' : (0 : ℝ) < ε := hpos
  rw [Hh_upp_upp]
  have h2 : (0 : ℝ) < ε ^ 2 := by positivity
  nlinarith [mul_neg_of_pos_of_neg h2 hε]

lemma ev_low_upp (K x t y u : ℝ) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), Hh (low ε x t) (upp ε y u) + ε ^ 3 * K < 0 := by
  have hc : ContinuousAt (fun ε : ℝ => Hh (low ε x t) (upp ε y u) + ε ^ 3 * K) 0 := by
    simp only [Hh_apply, low, upp]; fun_prop
  have h0 : ∀ᶠ ε in nhds (0 : ℝ), Hh (low ε x t) (upp ε y u) + ε ^ 3 * K < 0 := by
    apply hc.eventually_lt continuousAt_const
    simp only [Hh_apply, low, upp]; norm_num
  exact nhdsWithin_le_nhds h0

lemma ev_upp_low (K x t y u : ℝ) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), Hh (upp ε y u) (low ε x t) + ε ^ 3 * K < 0 := by
  have hc : ContinuousAt (fun ε : ℝ => Hh (upp ε y u) (low ε x t) + ε ^ 3 * K) 0 := by
    simp only [Hh_apply, low, upp]; fun_prop
  have h0 : ∀ᶠ ε in nhds (0 : ℝ), Hh (upp ε y u) (low ε x t) + ε ^ 3 * K < 0 := by
    apply hc.eventually_lt continuousAt_const
    simp only [Hh_apply, low, upp]; norm_num
  exact nhdsWithin_le_nhds h0

lemma norm_le_one_of_normSq_lt (z : ℂ) (h : z.re * z.re + z.im * z.im < 1) : ‖z‖ ≤ 1 := by
  have h1 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  by_contra hcon
  have hcon' : 1 < ‖z‖ := not_le.mp hcon
  nlinarith [norm_nonneg z]

lemma ev_norm_low (x t : ℝ) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ‖low ε x t‖ ≤ 1 := by
  have hc : ContinuousAt (fun ε : ℝ => (ε * x) * (ε * x)
      + (-1 / 2 + ε ^ 2 * (x ^ 2 + t / 2)) * (-1 / 2 + ε ^ 2 * (x ^ 2 + t / 2))) 0 := by fun_prop
  have h0 : ∀ᶠ ε in nhds (0 : ℝ), (ε * x) * (ε * x)
      + (-1 / 2 + ε ^ 2 * (x ^ 2 + t / 2)) * (-1 / 2 + ε ^ 2 * (x ^ 2 + t / 2)) < 1 := by
    apply hc.eventually_lt continuousAt_const
    norm_num
  filter_upwards [nhdsWithin_le_nhds h0] with ε hε
  exact norm_le_one_of_normSq_lt _ (by simpa only [low] using hε)

lemma ev_norm_upp (y u : ℝ) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ‖upp ε y u‖ ≤ 1 := by
  have hc : ContinuousAt (fun ε : ℝ => (-(ε * y)) * (-(ε * y))
      + (1 / 2 + ε ^ 2 * (-(y ^ 2) + u / 2)) * (1 / 2 + ε ^ 2 * (-(y ^ 2) + u / 2))) 0 := by fun_prop
  have h0 : ∀ᶠ ε in nhds (0 : ℝ), (-(ε * y)) * (-(ε * y))
      + (1 / 2 + ε ^ 2 * (-(y ^ 2) + u / 2)) * (1 / 2 + ε ^ 2 * (-(y ^ 2) + u / 2)) < 1 := by
    apply hc.eventually_lt continuousAt_const
    norm_num
  filter_upwards [nhdsWithin_le_nhds h0] with ε hε
  exact norm_le_one_of_normSq_lt _ (by simpa only [upp] using hε)

/-- A small rotation putting two points at distance exactly one. -/
lemma exists_rot (a b : ℂ) (s₁ : ℝ) (hs0 : 0 ≤ s₁) (hs1 : s₁ ≤ 1)
    (hξ : a.re * b.re + a.im * b.im ≤ 0)
    (h0 : 1 ≤ Complex.normSq (a - b))
    (h1 : Complex.normSq (a - b) + 2 * s₁ * (a.re * b.im - a.im * b.re) ≤ 1) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ ‖a - b * w‖ = 1 ∧ ‖w - 1‖ ≤ 2 * s₁ := by
  have hg : Continuous (fun s : ℝ =>
      (a.re - (b.re * Real.sqrt (1 - s ^ 2) - b.im * s)) ^ 2
        + (a.im - (b.re * s + b.im * Real.sqrt (1 - s ^ 2))) ^ 2) := by fun_prop
  have hg0 : (a.re - (b.re * Real.sqrt (1 - (0 : ℝ) ^ 2) - b.im * 0)) ^ 2
        + (a.im - (b.re * 0 + b.im * Real.sqrt (1 - (0 : ℝ) ^ 2))) ^ 2
      = Complex.normSq (a - b) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    norm_num
    ring
  have hgs : (a.re - (b.re * Real.sqrt (1 - s₁ ^ 2) - b.im * s₁)) ^ 2
        + (a.im - (b.re * s₁ + b.im * Real.sqrt (1 - s₁ ^ 2))) ^ 2 ≤ 1 := by
    have hc2 : Real.sqrt (1 - s₁ ^ 2) ^ 2 = 1 - s₁ ^ 2 := Real.sq_sqrt (by nlinarith)
    have hc0 : 0 ≤ Real.sqrt (1 - s₁ ^ 2) := Real.sqrt_nonneg _
    have hc1 : Real.sqrt (1 - s₁ ^ 2) ≤ 1 := by nlinarith
    have hexp : (a.re - (b.re * Real.sqrt (1 - s₁ ^ 2) - b.im * s₁)) ^ 2
        + (a.im - (b.re * s₁ + b.im * Real.sqrt (1 - s₁ ^ 2))) ^ 2
        = Complex.normSq (a - b)
          + 2 * (a.re * b.re + a.im * b.im) * (1 - Real.sqrt (1 - s₁ ^ 2))
          + 2 * s₁ * (a.re * b.im - a.im * b.re) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      linear_combination (b.re ^ 2 + b.im ^ 2) * hc2
    rw [hexp]
    nlinarith [mul_nonneg (neg_nonneg.mpr hξ) (sub_nonneg.mpr hc1)]
  have hivt := intermediate_value_Icc' hs0 hg.continuousOn
  obtain ⟨s, ⟨hs_lo, hs_hi⟩, hgs1⟩ := hivt ⟨hgs, by rw [hg0]; exact h0⟩
  have hs_le : s ≤ 1 := le_trans hs_hi hs1
  have hc2 : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by nlinarith)
  have hc0 : 0 ≤ Real.sqrt (1 - s ^ 2) := Real.sqrt_nonneg _
  have hc1 : Real.sqrt (1 - s ^ 2) ≤ 1 := by nlinarith
  have hc3 : 1 - s ^ 2 ≤ Real.sqrt (1 - s ^ 2) := by nlinarith
  refine ⟨⟨Real.sqrt (1 - s ^ 2), s⟩, ?_, ?_, ?_⟩
  · have h2 : ‖(⟨Real.sqrt (1 - s ^ 2), s⟩ : ℂ)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  · have h2 : ‖a - b * (⟨Real.sqrt (1 - s ^ 2), s⟩ : ℂ)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
      simp only at hgs1
      nlinarith [hgs1]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  · have h2 : ‖(⟨Real.sqrt (1 - s ^ 2), s⟩ : ℂ) - 1‖ ^ 2 ≤ (2 * s₁) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

lemma ev_edge (x t z : ℝ) (hz : 1 ≤ z) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∃ w : ℂ, ‖w‖ = 1 ∧
      ‖low ε x t - upp ε (x + z) (t + z ^ 2) * w‖ = 1 ∧ ‖w - 1‖ ≤ 4 * ε ^ 3 * (Mf x t z) ^ 2 := by
  have c1 : ∀ᶠ ε in nhds (0 : ℝ), (ε * x) * (-(ε * (x + z)))
      + (-1 / 2 + ε ^ 2 * (x ^ 2 + t / 2)) * (1 / 2 + ε ^ 2 * (-((x + z) ^ 2) + (t + z ^ 2) / 2))
        < 0 := by
    have hc : ContinuousAt (fun ε : ℝ => (ε * x) * (-(ε * (x + z)))
      + (-1 / 2 + ε ^ 2 * (x ^ 2 + t / 2))
        * (1 / 2 + ε ^ 2 * (-((x + z) ^ 2) + (t + z ^ 2) / 2))) 0 := by fun_prop
    apply hc.eventually_lt continuousAt_const
    norm_num
  have c2 : ∀ᶠ ε in nhds (0 : ℝ), -z / 2
      + ε ^ 2 * (x * (-((x + z) ^ 2) + (t + z ^ 2) / 2) + (x + z) * (x ^ 2 + t / 2)) < -1 / 4 := by
    have hc : ContinuousAt (fun ε : ℝ => -z / 2
      + ε ^ 2 * (x * (-((x + z) ^ 2) + (t + z ^ 2) / 2) + (x + z) * (x ^ 2 + t / 2))) 0 := by
      fun_prop
    apply hc.eventually_lt continuousAt_const
    norm_num; linarith
  have c3 : ∀ᶠ ε in nhds (0 : ℝ), 2 * ε ^ 3 * (Mf x t z) ^ 2 < 1 := by
    have hc : ContinuousAt (fun ε : ℝ => 2 * ε ^ 3 * (Mf x t z) ^ 2) 0 := by fun_prop
    apply hc.eventually_lt continuousAt_const
    norm_num
  filter_upwards [nhdsWithin_le_nhds c1, nhdsWithin_le_nhds c2, nhdsWithin_le_nhds c3,
    self_mem_nhdsWithin] with ε h1 h2 h3 hpos
  have hpos' : (0 : ℝ) < ε := hpos
  have hM0 : 0 ≤ (Mf x t z) ^ 2 := sq_nonneg _
  have e1 : Complex.normSq (low ε x t - upp ε (x + z) (t + z ^ 2))
      = 1 + ε ^ 4 * (Mf x t z) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, low, upp, Mf]; ring
  have e2 : (low ε x t).re * (upp ε (x + z) (t + z ^ 2)).im
        - (low ε x t).im * (upp ε (x + z) (t + z ^ 2)).re
      = ε * (-z / 2
        + ε ^ 2 * (x * (-((x + z) ^ 2) + (t + z ^ 2) / 2) + (x + z) * (x ^ 2 + t / 2))) := by
    simp only [low, upp]; ring
  have h4 : (0 : ℝ) ≤ ε ^ 4 * (Mf x t z) ^ 2 := by positivity
  have key := exists_rot (low ε x t) (upp ε (x + z) (t + z ^ 2)) (2 * ε ^ 3 * (Mf x t z) ^ 2)
    (by positivity) h3.le
    (by simp only [low, upp]; linarith)
    (by rw [e1]; linarith)
    (by
      rw [e1, e2]
      have hid : 1 + ε ^ 4 * (Mf x t z) ^ 2 + 2 * (2 * ε ^ 3 * (Mf x t z) ^ 2)
          * (ε * (-z / 2 + ε ^ 2 * (x * (-((x + z) ^ 2) + (t + z ^ 2) / 2)
            + (x + z) * (x ^ 2 + t / 2))))
          = 1 + ε ^ 4 * (Mf x t z) ^ 2 * (1 + 4 * (-z / 2 + ε ^ 2
            * (x * (-((x + z) ^ 2) + (t + z ^ 2) / 2) + (x + z) * (x ^ 2 + t / 2)))) := by ring
      rw [hid]
      nlinarith [mul_nonneg h4 (by linarith : (0 : ℝ) ≤ -(1 + 4 * (-z / 2 + ε ^ 2
            * (x * (-((x + z) ^ 2) + (t + z ^ 2) / 2) + (x + z) * (x ^ 2 + t / 2)))))])
  obtain ⟨w, hw1, hw2, hw3⟩ := key
  exact ⟨w, hw1, hw2, by linarith⟩

end seeds

section final

variable {n : ℕ}

lemma tok_src (s : ℕ) (Es : Finset (Finset (Fin n) × Fin n))
    (hEs : ∀ p : Finset (Fin n) × Fin n, p ∈ Es ↔ p.1.card = s ∧ p.2 ∉ p.1)
    (A : Finset (Fin n)) (hA : A.card = s) :
    n - s ≤ tok Es (fun p => p.1) (fun p => insert p.2 p.1) A (fun _ => 1) := by
  have h1 : (Es.filter (fun e : Finset (Fin n) × Fin n => e.1 = A)).card
      ≤ tok Es (fun p => p.1) (fun p => insert p.2 p.1) A (fun _ => 1) := by
    unfold tok
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro e _
    by_cases h : e.1 = A <;> simp [h]
  have h3 : (Aᶜ).card = n - s := by
    rw [Finset.card_compl, hA, Fintype.card_fin]
  have h2 : (Aᶜ).card ≤ (Es.filter (fun e : Finset (Fin n) × Fin n => e.1 = A)).card := by
    apply Finset.card_le_card_of_injOn (fun j => (A, j))
    · intro j hj
      rw [Finset.mem_coe] at hj
      rw [Finset.mem_coe, Finset.mem_filter, hEs]
      exact ⟨⟨hA, Finset.mem_compl.mp hj⟩, rfl⟩
    · intro j _ j' _ h
      exact (Prod.mk.inj h).2
  omega

lemma tok_dst (s : ℕ) (Es : Finset (Finset (Fin n) × Fin n))
    (hEs : ∀ p : Finset (Fin n) × Fin n, p ∈ Es ↔ p.1.card = s ∧ p.2 ∉ p.1)
    (B : Finset (Fin n)) (hB : B.card = s + 1) :
    s + 1 ≤ tok Es (fun p => p.1) (fun p => insert p.2 p.1) B (fun _ => 1) := by
  have h1 : (Es.filter (fun e : Finset (Fin n) × Fin n => insert e.2 e.1 = B)).card
      ≤ tok Es (fun p => p.1) (fun p => insert p.2 p.1) B (fun _ => 1) := by
    unfold tok
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro e _
    by_cases h : insert e.2 e.1 = B <;> simp [h]
  have h2 : B.card
      ≤ (Es.filter (fun e : Finset (Fin n) × Fin n => insert e.2 e.1 = B)).card := by
    apply Finset.card_le_card_of_injOn (fun j => (B.erase j, j))
    · intro j hj
      rw [Finset.mem_coe] at hj
      rw [Finset.mem_coe, Finset.mem_filter, hEs]
      refine ⟨⟨?_, Finset.notMem_erase j B⟩, Finset.insert_erase hj⟩
      rw [Finset.card_erase_of_mem hj, hB]; omega
    · intro j _ j' _ h
      exact (Prod.mk.inj h).2
  omega

/-- The configuration in the complex plane: every point has `k` unit neighbours. -/
theorem exists_config (k : ℕ) (hk : 1 ≤ k) :
    ∃ P : Finset ℂ, P.Nonempty ∧ (∀ x ∈ P, ∀ y ∈ P, x ≠ y → Hh x y < 0) ∧
    ∀ x ∈ P, ∃ Q : Finset ℂ, Q ⊆ P ∧ k ≤ Q.card ∧ ∀ y ∈ Q, ‖x - y‖ = 1 := by
  obtain ⟨Es, hEs⟩ : ∃ Es : Finset (Finset (Fin (4 * k)) × Fin (4 * k)),
      ∀ p : Finset (Fin (4 * k)) × Fin (4 * k), p ∈ Es ↔ p.1.card = 2 * k ∧ p.2 ∉ p.1 :=
    ⟨Finset.univ.filter (fun p => p.1.card = 2 * k ∧ p.2 ∉ p.1), fun p => by simp⟩
  obtain ⟨v0, -, hv0⟩ : ∃ v0 : Finset (Fin (4 * k)), v0 ⊆ Finset.univ ∧ v0.card = 2 * k :=
    Finset.exists_subset_card_eq (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  let Mg : Finset (Fin (4 * k)) × Fin (4 * k) → ℝ :=
    fun p => Mf (X p.1) (T p.1) ((5 : ℝ) ^ (p.2 : ℕ))
  let K : ℝ := ∑ e ∈ Es, 16 * (Mg e) ^ 2
  have hE : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ e : Finset (Fin (4 * k)) × Fin (4 * k), e ∈ Es →
      ∃ w : ℂ, ‖w‖ = 1 ∧ ‖seed (2 * k) ε e.1 - seed (2 * k) ε (insert e.2 e.1) * w‖ = 1 ∧
        ‖w - 1‖ ≤ 4 * ε ^ 3 * (Mg e) ^ 2 := by
    rw [Filter.eventually_all]
    intro e
    by_cases he : e ∈ Es
    · obtain ⟨hc, hj⟩ := (hEs e).mp he
      have hz : (1 : ℝ) ≤ (5 : ℝ) ^ (e.2 : ℕ) := one_le_pow₀ (by norm_num)
      filter_upwards [ev_edge (X e.1) (T e.1) ((5 : ℝ) ^ (e.2 : ℕ)) hz] with ε hε _
      have hs1 : seed (2 * k) ε e.1 = low ε (X e.1) (T e.1) := by
        unfold seed; rw [if_pos (by omega)]
      have hs2 : seed (2 * k) ε (insert e.2 e.1)
          = upp ε (X e.1 + (5 : ℝ) ^ (e.2 : ℕ)) (T e.1 + ((5 : ℝ) ^ (e.2 : ℕ)) ^ 2) := by
        have hc6 : (insert e.2 e.1).card = 2 * k + 1 := by
          rw [Finset.card_insert_of_notMem hj, hc]
        unfold seed; rw [if_neg (by omega), X_insert _ _ hj, T_insert _ _ hj]
      rw [hs1, hs2]; exact hε
    · exact Filter.Eventually.of_forall (fun ε h => absurd h he)
  have hM : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ vv : Finset (Fin (4 * k)) × Finset (Fin (4 * k)), vv.1 ≠ vv.2 →
        Hh (seed (2 * k) ε vv.1) (seed (2 * k) ε vv.2) + ε ^ 3 * K < 0 := by
    rw [Filter.eventually_all]
    rintro ⟨v, v'⟩
    by_cases hne : v = v'
    · exact Filter.Eventually.of_forall (fun ε h => absurd hne h)
    · have hd := digit12 v v' hne
      rw [abs_lt] at hd
      have hsq : (X v' - X v) ^ 2 = (X v - X v') ^ 2 := by ring
      by_cases h1 : v.card ≤ 2 * k <;> by_cases h2 : v'.card ≤ 2 * k
      · filter_upwards [ev_low K (X v) (T v) (X v') (T v') (by linarith [hd.1, hd.2])]
          with ε hε _
        show Hh (seed (2 * k) ε v) (seed (2 * k) ε v') + ε ^ 3 * K < 0
        unfold seed; rw [if_pos h1, if_pos h2]; exact hε
      · filter_upwards [ev_low_upp K (X v) (T v) (X v') (T v')] with ε hε _
        show Hh (seed (2 * k) ε v) (seed (2 * k) ε v') + ε ^ 3 * K < 0
        unfold seed; rw [if_pos h1, if_neg h2]; exact hε
      · filter_upwards [ev_upp_low K (X v') (T v') (X v) (T v)] with ε hε _
        show Hh (seed (2 * k) ε v) (seed (2 * k) ε v') + ε ^ 3 * K < 0
        unfold seed; rw [if_neg h1, if_pos h2]; exact hε
      · filter_upwards [ev_upp K (X v) (T v) (X v') (T v') (by linarith [hd.1, hd.2])]
          with ε hε _
        show Hh (seed (2 * k) ε v) (seed (2 * k) ε v') + ε ^ 3 * K < 0
        unfold seed; rw [if_neg h1, if_neg h2]; exact hε
  have hN : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ v : Finset (Fin (4 * k)), ‖seed (2 * k) ε v‖ ≤ 1 := by
    rw [Filter.eventually_all]
    intro v
    by_cases h1 : v.card ≤ 2 * k
    · filter_upwards [ev_norm_low (X v) (T v)] with ε hε
      unfold seed; rw [if_pos h1]; exact hε
    · filter_upwards [ev_norm_upp (X v) (T v)] with ε hε
      unfold seed; rw [if_neg h1]; exact hε
  have hpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), (0 : ℝ) < ε := self_mem_nhdsWithin
  obtain ⟨ε, hE', hM', hN', hε⟩ := (hE.and (hM.and (hN.and hpos))).exists
  have hE'' : ∀ e : Finset (Fin (4 * k)) × Fin (4 * k), ∃ w : ℂ, e ∈ Es →
      (‖w‖ = 1 ∧ ‖seed (2 * k) ε e.1 - seed (2 * k) ε (insert e.2 e.1) * w‖ = 1 ∧
        ‖w - 1‖ ≤ 4 * ε ^ 3 * (Mg e) ^ 2) := by
    intro e
    by_cases he : e ∈ Es
    · obtain ⟨w, hw⟩ := hE' e he
      exact ⟨w, fun _ => hw⟩
    · exact ⟨1, fun h => absurd h he⟩
  choose w hw using hE''
  have h7 := tok_src (2 * k) Es hEs v0 hv0
  refine core k hk Es (fun p => p.1) (fun p => insert p.2 p.1) (seed (2 * k) ε) w v0
    (fun e he => (hw e he).1) (fun e he => (hw e he).2.1) hN' ?_ ?_ ?_ (by omega) ?_
  · intro v v' hne
    have h1 : Hh (seed (2 * k) ε v) (seed (2 * k) ε v') + ε ^ 3 * K < 0 := hM' (v, v') hne
    have hsum : ∑ e ∈ Es, ‖w e - 1‖ ≤ ∑ e ∈ Es, 4 * ε ^ 3 * (Mg e) ^ 2 :=
      Finset.sum_le_sum (fun e he => (hw e he).2.2)
    have hK : 4 * ∑ e ∈ Es, 4 * ε ^ 3 * (Mg e) ^ 2 = ε ^ 3 * K := by
      simp only [K, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    linarith
  · intro e he e' he' h1 h2
    obtain ⟨hc, hj⟩ := (hEs e).mp he
    obtain ⟨hc', hj'⟩ := (hEs e').mp he'
    have h1' : e.1 = e'.1 := h1
    have h2' : insert e.2 e.1 = insert e'.2 e'.1 := h2
    have hmem : e.2 ∈ insert e'.2 e'.1 := by
      rw [← h2']; exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hmem with h | h
    · exact Prod.ext h1' h
    · rw [← h1'] at h
      exact absurd h hj
  · intro e he e' he' h
    obtain ⟨hc, hj⟩ := (hEs e).mp he
    obtain ⟨hc', hj'⟩ := (hEs e').mp he'
    have h' : e.1 = insert e'.2 e'.1 := h
    have hcard := congrArg Finset.card h'
    rw [Finset.card_insert_of_notMem hj', hc, hc'] at hcard
    omega
  · rintro u ⟨e, he, h | h⟩
    · obtain ⟨hc, hj⟩ := (hEs e).mp he
      have h' : e.1 = u := h
      have h7' := tok_src (2 * k) Es hEs u (by rw [← h']; exact hc)
      omega
    · obtain ⟨hc, hj⟩ := (hEs e).mp he
      have h' : insert e.2 e.1 = u := h
      have h6' := tok_dst (2 * k) Es hEs u (by rw [← h', Finset.card_insert_of_notMem hj, hc])
      omega

/-- Transfer from the complex plane to the Euclidean plane. -/
theorem transfer (k : ℕ) (P : Finset ℂ) (hne : P.Nonempty)
    (hsupp : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → Hh x y < 0)
    (hdeg : ∀ x ∈ P, ∃ Q : Finset ℂ, Q ⊆ P ∧ k ≤ Q.card ∧ ∀ y ∈ Q, ‖x - y‖ = 1) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.Nonempty ∧
      EuclideanGeometry.ConvexIndep (A : Set (EuclideanSpace ℝ (Fin 2))) ∧
      Erdos97.HasNEquidistantProperty k A := by
  classical
  let φ : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  refine ⟨P.image φ, hne.image φ, ?_, ?_⟩
  · intro a ha hmem
    rw [Finset.coe_image] at ha hmem
    obtain ⟨x, hx, rfl⟩ := ha
    have hxP : x ∈ P := Finset.mem_coe.mp hx
    rw [← Set.image_singleton, ← Set.image_sdiff φ.injective] at hmem
    have hlin : (convexHull ℝ) (φ '' ((P : Set ℂ) \ {x}))
        = φ '' (convexHull ℝ) ((P : Set ℂ) \ {x}) :=
      (φ.toLinearEquiv.toLinearMap.image_convexHull ((P : Set ℂ) \ {x})).symm
    rw [hlin] at hmem
    obtain ⟨x', hx'mem, hx'eq⟩ := hmem
    have hxx : x' = x := φ.injective hx'eq
    rw [hxx] at hx'mem
    have hconv : Convex ℝ {z : ℂ | (starRingEnd ℂ x * z).re < (starRingEnd ℂ x * x).re} := by
      apply convex_halfSpace_lt
      refine ⟨fun a b => ?_, fun c a => ?_⟩
      · simp [mul_add]
      · simp [Complex.real_smul, mul_left_comm]
    have hsub : (P : Set ℂ) \ {x}
        ⊆ {z : ℂ | (starRingEnd ℂ x * z).re < (starRingEnd ℂ x * x).re} := by
      intro y hy
      have hyP : y ∈ P := Finset.mem_coe.mp hy.1
      have hyx : x ≠ y := fun h => hy.2 (by rw [← h]; exact Set.mem_singleton x)
      have h1 := hsupp x hxP y hyP hyx
      unfold Hh at h1
      rw [mul_sub, Complex.sub_re] at h1
      show (starRingEnd ℂ x * y).re < (starRingEnd ℂ x * x).re
      linarith
    have h2 : (starRingEnd ℂ x * x).re < (starRingEnd ℂ x * x).re :=
      convexHull_min hsub hconv hx'mem
    exact lt_irrefl _ h2
  · unfold Erdos97.HasNEquidistantProperty Erdos97.HasNEquidistantPointsOn
      Erdos97.HasNEquidistantPointsAt
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨Q, hQP, hQc, hQd⟩ := hdeg x hx
    refine ⟨1, one_pos, ?_⟩
    have hcard : (Q.image φ).card = Q.card := Finset.card_image_of_injective Q φ.injective
    rw [ge_iff_le]
    calc k ≤ Q.card := hQc
      _ = (Q.image φ).card := hcard.symm
      _ ≤ _ := Finset.card_le_card (fun q hq => by
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_image_of_mem φ (hQP hy), by
              rw [φ.dist_map, dist_eq_norm]; exact hQd y hy⟩)

end final

end EK

theorem OMA.disproof : ¬ (type_of% @Erdos97.erdos_97.variants.k_equidistant) := by
  rintro ⟨k, h⟩
  obtain ⟨P, hne, hsupp, hdeg⟩ := EK.exists_config (k + 1) (by omega)
  obtain ⟨A, hA1, hA2, hA3⟩ := EK.transfer k P hne hsupp
    (fun x hx => by
      obtain ⟨Q, h1, h2, h3⟩ := hdeg x hx
      exact ⟨Q, h1, by omega, h3⟩)
  exact h A hA1 hA2 hA3
