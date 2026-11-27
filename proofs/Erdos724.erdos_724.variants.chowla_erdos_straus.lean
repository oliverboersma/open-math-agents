import FormalConjectures.ErdosProblems.«724»
import Mathlib

/-!
# Proof of Chowla-Erdos-Straus (1960): `maxMOLS n >> n ^ (1 / 91)`

Credit: @liuweid95-hash.
Section 1 adapts MOLS constructions from merged proofs by @ivillar, @ptc-prover-bot, @green-notes.
Sections 2-4 give a self-contained elementary Brun combinatorial sieve via Chebyshev's theta bound.
-/

namespace OMAChowla724

open Finset Filter Real Erdos724
open scoped Classical

/- ### Section 1: MOLS building blocks (prime powers, MacNeish product, Wilson recursion) -/

section MOLS

private def fieldSq {F : Type*} [Field F] {n : ℕ} (e : Fin n ≃ F) (c : F) (hc : c ≠ 0) :
    LatinSquare n where
  mat := fun i j => e.symm (c * e i + e j)
  row_injective := by
    intro i a b h
    exact e.injective (add_left_cancel (e.symm.injective h))
  col_injective := by
    intro j a b h
    exact e.injective (mul_left_cancel₀ hc (add_right_cancel (e.symm.injective h)))

private lemma field_mols_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (hn : Fintype.card F = n) : n - 1 ≤ maxMOLS n := by
  let e : Fin n ≃ F := (Fintype.equivFinOfCardEq hn).symm
  let f : Fˣ → LatinSquare n := fun u => fieldSq e (u : F) u.ne_zero
  have finj : Function.Injective f := by
    intro u v h
    have h1 := congrArg (fun L : LatinSquare n => e (L.mat (e.symm 1) (e.symm 0))) h
    simp only [f, fieldSq, Equiv.apply_symm_apply, mul_one, add_zero] at h1
    exact Units.ext h1
  have hcard : (univ.image f).card = n - 1 := by
    rw [card_image_of_injective _ finj, card_univ, Fintype.card_units, hn]
  refine le_csSup ⟨Fintype.card (LatinSquare n), ?_⟩ ⟨univ.image f, hcard, ?_⟩
  · rintro k ⟨S, rfl, -⟩
    exact card_le_univ S
  · intro L hL M hM hLM
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hL hM
    obtain ⟨u, rfl⟩ := hL
    obtain ⟨v, rfl⟩ := hM
    have huv : (u : F) ≠ v := fun h => hLM (by rw [Units.ext h])
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [f, fieldSq, Prod.mk.injEq] at h
    have h1 := e.symm.injective h.1
    have h2 := e.symm.injective h.2
    have h3 : ((u : F) - v) * (e i - e i') = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) huv
    · have hii : i = i' := e.injective (sub_eq_zero.mp h4)
      subst hii
      rw [e.injective (add_left_cancel h1)]

private lemma prime_power_bound (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    p ^ k - 1 ≤ maxMOLS (p ^ k) := by
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype (GaloisField p k) := Fintype.ofFinite _
  exact field_mols_bound (F := GaloisField p k) (p ^ k)
    (by rw [Fintype.card_eq_nat_card]; exact GaloisField.card p k (by omega))

private def prodSq {a b : ℕ} (L : LatinSquare a) (M : LatinSquare b) : LatinSquare (a * b) where
  mat := fun x y => finProdFinEquiv
    (L.mat (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1,
     M.mat (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2)
  row_injective := by
    intro x y y' h
    have h' := finProdFinEquiv.injective h
    simp only [Prod.mk.injEq] at h'
    exact finProdFinEquiv.symm.injective (Prod.ext (L.row_injective _ h'.1) (M.row_injective _ h'.2))
  col_injective := by
    intro y x x' h
    have h' := finProdFinEquiv.injective h
    simp only [Prod.mk.injEq] at h'
    exact finProdFinEquiv.symm.injective (Prod.ext (L.col_injective _ h'.1) (M.col_injective _ h'.2))

private lemma prodSq_orth {a b : ℕ} {L L' : LatinSquare a} {M M' : LatinSquare b}
    (hL : IsOrthogonal L L') (hM : IsOrthogonal M M') :
    IsOrthogonal (prodSq L M) (prodSq L' M') := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [prodSq, Prod.mk.injEq] at h
  have h1 := finProdFinEquiv.injective h.1
  have h2 := finProdFinEquiv.injective h.2
  simp only [Prod.mk.injEq] at h1 h2
  have e1 := hL (a₁ := ((finProdFinEquiv.symm x).1, (finProdFinEquiv.symm y).1))
    (a₂ := ((finProdFinEquiv.symm x').1, (finProdFinEquiv.symm y').1)) (Prod.ext h1.1 h2.1)
  have e2 := hM (a₁ := ((finProdFinEquiv.symm x).2, (finProdFinEquiv.symm y).2))
    (a₂ := ((finProdFinEquiv.symm x').2, (finProdFinEquiv.symm y').2)) (Prod.ext h1.2 h2.2)
  simp only [Prod.mk.injEq] at e1 e2
  rw [finProdFinEquiv.symm.injective (Prod.ext e1.1 e2.1),
      finProdFinEquiv.symm.injective (Prod.ext e1.2 e2.2)]

private lemma prodSq_left {a b : ℕ} (hb : 0 < b) {L L' : LatinSquare a} {M M' : LatinSquare b}
    (h : prodSq L M = prodSq L' M') : L = L' := by
  have hm : ∀ u v : Fin a, L.mat u v = L'.mat u v := by
    intro u v
    have := congrArg (fun P : LatinSquare (a * b) =>
      (finProdFinEquiv.symm (P.mat (finProdFinEquiv (u, ⟨0, hb⟩))
        (finProdFinEquiv (v, ⟨0, hb⟩)))).1) h
    simp only [prodSq, Equiv.symm_apply_apply] at this
    exact this
  cases L; cases L'
  simp only [LatinSquare.mk.injEq]
  funext u v
  exact hm u v

private lemma mols_bdd (n : ℕ) : BddAbove {k : ℕ | ∃ S : Finset (LatinSquare n), #S = k ∧
    (S : Set (LatinSquare n)).Pairwise IsOrthogonal} := by
  refine ⟨Fintype.card (LatinSquare n), ?_⟩
  rintro k ⟨S, rfl, -⟩
  exact card_le_univ S

private lemma mols_attain (n : ℕ) : ∃ S : Finset (LatinSquare n), #S = maxMOLS n ∧
    (S : Set (LatinSquare n)).Pairwise IsOrthogonal :=
  Nat.sSup_mem (s := {k : ℕ | ∃ S : Finset (LatinSquare n), #S = k ∧
    (S : Set (LatinSquare n)).Pairwise IsOrthogonal}) ⟨0, ∅, by simp, by simp⟩ (mols_bdd n)

private lemma macNeish_pair (a b : ℕ) (_ha : 1 ≤ a) (hb : 1 ≤ b) :
    min (maxMOLS a) (maxMOLS b) ≤ maxMOLS (a * b) := by
  set m := min (maxMOLS a) (maxMOLS b)
  obtain ⟨Sa, hSa, hpa⟩ := mols_attain a
  obtain ⟨Sb, hSb, hpb⟩ := mols_attain b
  obtain ⟨Ta, hTa, hTac⟩ := exists_subset_card_eq (show m ≤ #Sa by rw [hSa]; exact min_le_left _ _)
  obtain ⟨Tb, hTb, hTbc⟩ := exists_subset_card_eq (show m ≤ #Sb by rw [hSb]; exact min_le_right _ _)
  have hpa' := hpa.mono (coe_subset.mpr hTa)
  have hpb' := hpb.mono (coe_subset.mpr hTb)
  let fa : Fin m → LatinSquare a := fun i => (Ta.equivFinOfCardEq hTac).symm i
  let fb : Fin m → LatinSquare b := fun i => (Tb.equivFinOfCardEq hTbc).symm i
  have fa_mem : ∀ i, fa i ∈ Ta := fun i => ((Ta.equivFinOfCardEq hTac).symm i).2
  have fb_mem : ∀ i, fb i ∈ Tb := fun i => ((Tb.equivFinOfCardEq hTbc).symm i).2
  have fa_inj : Function.Injective fa := fun _ _ h =>
    (Ta.equivFinOfCardEq hTac).symm.injective (Subtype.ext h)
  have fb_inj : Function.Injective fb := fun _ _ h =>
    (Tb.equivFinOfCardEq hTbc).symm.injective (Subtype.ext h)
  let g : Fin m → LatinSquare (a * b) := fun i => prodSq (fa i) (fb i)
  have g_inj : Function.Injective g := fun _ _ h => fa_inj (prodSq_left (by omega) h)
  refine le_csSup (mols_bdd (a * b)) ⟨univ.image g, ?_, ?_⟩
  · rw [card_image_of_injective _ g_inj, card_univ, Fintype.card_fin]
  · intro P hP Q hQ hPQ
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hP hQ
    obtain ⟨i, rfl⟩ := hP
    obtain ⟨j, rfl⟩ := hQ
    have hij : i ≠ j := fun h => hPQ (by rw [h])
    exact prodSq_orth (hpa' (fa_mem i) (fa_mem j) (fun h => hij (fa_inj h)))
      (hpb' (fb_mem i) (fb_mem j) (fun h => hij (fb_inj h)))

private lemma macNeish :
    ∀ n : ℕ, 2 ≤ n → ∀ s : ℕ,
      (∀ p ∈ n.primeFactors, s + 1 ≤ p ^ (n.factorization p)) → s ≤ maxMOLS n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn s hs
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpn : p ∣ n := Nat.minFac_dvd n
    have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
    have hk : 1 ≤ n.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpn
    let q := p ^ (n.factorization p)
    have hqn : q ∣ n := Nat.ordProj_dvd n p
    let r := n / q
    have hqr : q * r = n := Nat.mul_div_cancel' hqn
    have hq_pos : 1 ≤ q := Nat.one_le_pow _ _ hp.pos
    have hr_pos : 1 ≤ r := Nat.pos_of_ne_zero fun hr0 => by rw [hr0, mul_zero] at hqr; omega
    have hq_ge : s ≤ maxMOLS q := by
      have h1q := prime_power_bound p (n.factorization p) hp hk
      have hsq : s + 1 ≤ q := hs p hpmem
      dsimp only [q]
      omega
    by_cases hr1 : r = 1
    · rw [← hqr, hr1, mul_one]; exact hq_ge
    · have hr2 : 2 ≤ r := by omega
      have hq2 : 2 ≤ q := by
        have hp2 : 2 ≤ p := hp.two_le
        have hpow : p ≤ p ^ (n.factorization p) := by
          simpa using Nat.pow_le_pow_right hp.pos hk
        simpa [q] using hp2.trans hpow
      have hrlt : r < n := by
        calc r = 1 * r := (one_mul r).symm
          _ < q * r := Nat.mul_lt_mul_of_pos_right (by omega) hr_pos
          _ = n := hqr
      have hpnr : ¬ p ∣ r := Nat.not_dvd_ordCompl hp (by omega)
      have hsr : s ≤ maxMOLS r := by
        refine ih r hrlt hr2 s fun p' hp' => ?_
        have hp'_prime : p'.Prime := (Nat.mem_primeFactors.mp hp').1
        have hp'_dvd_r : p' ∣ r := (Nat.mem_primeFactors.mp hp').2.1
        have hp'_ne : p' ≠ p := by rintro rfl; exact hpnr hp'_dvd_r
        have hp'_dvd_n : p' ∣ n := hp'_dvd_r.trans ⟨q, by rw [← hqr, mul_comm]⟩
        have hp'_mem : p' ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp'_prime, hp'_dvd_n, by omega⟩
        have hq_not : ¬ p' ∣ q := fun hd => by
          rcases (Nat.dvd_prime hp).mp (hp'_prime.dvd_of_dvd_pow hd) with h1' | hpeq
          · exact hp'_prime.ne_one h1'
          · exact hp'_ne hpeq
        have hfac : r.factorization p' = n.factorization p' := by
          have h := congrArg (fun x => Nat.factorization x p') hqr.symm
          rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
            Nat.factorization_eq_zero_of_not_dvd hq_not, zero_add] at h
          exact h.symm
        rw [hfac]
        exact hs p' hp'_mem
      calc s ≤ min (maxMOLS q) (maxMOLS r) := le_min hq_ge hsr
        _ ≤ maxMOLS (q * r) := macNeish_pair q r hq_pos hr_pos
        _ = maxMOLS n := by rw [hqr]

private def IsOA {α : Type*} (k : ℕ) (S : Set (Fin k → α)) : Prop :=
  ∀ a b : Fin k, a ≠ b → Set.BijOn (fun r => (r a, r b)) S Set.univ

private def rowA {T U M : Type*} {d : ℕ} (β : Fin (d + 1) → T) (r : Fin d → M) :
    Fin d → (T × M) ⊕ U :=
  fun g => Sum.inl (β g.castSucc, r g)

private def rowB {T U M : Type*} {d : ℕ} (β : Fin (d + 1) → T) (k : U) (r : Fin d → Option M) :
    Fin d → (T × M) ⊕ U :=
  fun g => match r g with
    | none => Sum.inr k
    | some s => Sum.inl (β g.castSucc, s)

private def rowC {T U M : Type*} {d : ℕ} (r : Fin d → U) : Fin d → (T × M) ⊕ U :=
  fun g => Sum.inr (r g)

private def gluedOA {T U M : Type*} {d : ℕ}
    (S5 : Set (Fin (d + 1) → T)) (S3 : Set (Fin d → M)) (S4 : Set (Fin d → Option M))
    (SU : Set (Fin d → U)) (ι : U → T) : Set (Fin d → (T × M) ⊕ U) :=
  {x | ∃ β ∈ S5, (∀ k, ι k ≠ β (Fin.last d)) ∧ ∃ r ∈ S3, x = rowA β r} ∪
  {x | ∃ β ∈ S5, ∃ k, ι k = β (Fin.last d) ∧ ∃ r ∈ S4, r ≠ (fun _ => none) ∧ x = rowB β k r} ∪
  {x | ∃ r ∈ SU, x = rowC r}

private lemma rowB_eq_inl {T U M : Type*} {d : ℕ} {β : Fin (d + 1) → T} {k : U}
    {r : Fin d → Option M} {g : Fin d} {p : T × M} :
    rowB β k r g = Sum.inl p ↔ ∃ s, r g = some s ∧ p = (β g.castSucc, s) := by
  unfold rowB; cases r g <;> simp [eq_comm]

private lemma rowB_eq_inr {T U M : Type*} {d : ℕ} {β : Fin (d + 1) → T} {k : U}
    {r : Fin d → Option M} {g : Fin d} {k' : U} :
    rowB β k r g = Sum.inr k' ↔ r g = none ∧ k = k' := by
  unfold rowB; cases r g <;> simp

private lemma oa_inj {α : Type*} {k : ℕ} {S : Set (Fin k → α)} (h : IsOA k S)
    {a b : Fin k} (hab : a ≠ b) {r r' : Fin k → α} (hr : r ∈ S) (hr' : r' ∈ S)
    (h1 : r a = r' a) (h2 : r b = r' b) : r = r' :=
  (h a b hab).injOn hr hr' (Prod.ext h1 h2)

private lemma oa_ex {α : Type*} {k : ℕ} {S : Set (Fin k → α)} (h : IsOA k S)
    {a b : Fin k} (hab : a ≠ b) (x y : α) : ∃ r ∈ S, r a = x ∧ r b = y := by
  obtain ⟨r, hr, he⟩ := (h a b hab).surjOn (Set.mem_univ (x, y))
  exact ⟨r, hr, (Prod.ext_iff.mp he).1, (Prod.ext_iff.mp he).2⟩

private lemma wilson_OA {T U M : Type*} {d : ℕ}
    {S5 : Set (Fin (d + 1) → T)} {S3 : Set (Fin d → M)}
    {S4 : Set (Fin d → Option M)} {SU : Set (Fin d → U)} {ι : U → T}
    (h5 : IsOA (d + 1) S5) (h3 : IsOA d S3) (h4 : IsOA d S4) (hnone : (fun _ => none) ∈ S4)
    (hU : IsOA d SU) (hι : Function.Injective ι) : IsOA d (gluedOA S5 S3 S4 SU ι) := by
  intro a b hab
  have hab' : a.castSucc ≠ b.castSucc := fun h => hab (Fin.castSucc_injective _ h)
  have ha4 : a.castSucc ≠ Fin.last d := Fin.castSucc_ne_last a
  have hb4 : b.castSucc ≠ Fin.last d := Fin.castSucc_ne_last b
  have allnone : ∀ r ∈ S4, r a = none → r b = none → r = fun _ => none := fun r hr h1 h2 =>
    oa_inj h4 hab hr hnone h1 h2
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · rintro x hx y hy hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨hxa, hxb⟩ := hxy
    rcases hx with (⟨β, hβ, hβι, r, hr, rfl⟩ | ⟨β, hβ, k, hk, r, hr, hrn, rfl⟩) | ⟨r, hr, rfl⟩ <;>
    rcases hy with (⟨γ, hγ, hγι, s, hs, rfl⟩ | ⟨γ, hγ, k', hk', s, hs, hsn, rfl⟩) | ⟨s, hs, rfl⟩
    · simp only [rowA, Sum.inl.injEq, Prod.mk.injEq] at hxa hxb
      rw [oa_inj h5 hab' hβ hγ hxa.1 hxb.1, oa_inj h3 hab hr hs hxa.2 hxb.2]
    · exfalso
      obtain ⟨_, _, e1⟩ := rowB_eq_inl.mp hxa.symm
      obtain ⟨_, _, e2⟩ := rowB_eq_inl.mp hxb.symm
      simp only [Prod.mk.injEq] at e1 e2
      exact hβι k' ((oa_inj h5 hab' hβ hγ e1.1 e2.1) ▸ hk')
    · simp [rowA, rowC] at hxa
    · exfalso
      obtain ⟨_, _, e1⟩ := rowB_eq_inl.mp hxa
      obtain ⟨_, _, e2⟩ := rowB_eq_inl.mp hxb
      simp only [Prod.mk.injEq] at e1 e2
      exact hγι k ((oa_inj h5 hab' hβ hγ e1.1.symm e2.1.symm) ▸ hk)
    · cases hra : r a with
      | none =>
        cases hrb : r b with
        | none => exact absurd (allnone r hr hra hrb) hrn
        | some v =>
          have xa : rowB β k r a = Sum.inr k := by simp [rowB, hra]
          have xb : rowB β k r b = Sum.inl (β b.castSucc, v) := by simp [rowB, hrb]
          rw [xa] at hxa; rw [xb] at hxb
          obtain ⟨hsa, rfl⟩ := rowB_eq_inr.mp hxa.symm
          obtain ⟨w, hsb, e⟩ := rowB_eq_inl.mp hxb.symm
          simp only [Prod.mk.injEq] at e
          have hβγ : β = γ := oa_inj h5 hb4 hβ hγ e.1 (hk.symm.trans hk')
          subst hβγ
          rw [oa_inj h4 hab hr hs (hra.trans hsa.symm) (hrb.trans (by rw [hsb, e.2]))]
      | some v =>
        have xa : rowB β k r a = Sum.inl (β a.castSucc, v) := by simp [rowB, hra]
        rw [xa] at hxa
        obtain ⟨w, hsa, e⟩ := rowB_eq_inl.mp hxa.symm
        simp only [Prod.mk.injEq] at e
        cases hrb : r b with
        | none =>
          have xb : rowB β k r b = Sum.inr k := by simp [rowB, hrb]
          rw [xb] at hxb
          obtain ⟨hsb, rfl⟩ := rowB_eq_inr.mp hxb.symm
          have hβγ : β = γ := oa_inj h5 ha4 hβ hγ e.1 (hk.symm.trans hk')
          subst hβγ
          rw [oa_inj h4 hab hr hs (hra.trans (by rw [hsa, e.2])) (hrb.trans hsb.symm)]
        | some v' =>
          have xb : rowB β k r b = Sum.inl (β b.castSucc, v') := by simp [rowB, hrb]
          rw [xb] at hxb
          obtain ⟨w', hsb, e'⟩ := rowB_eq_inl.mp hxb.symm
          simp only [Prod.mk.injEq] at e'
          have hβγ : β = γ := oa_inj h5 hab' hβ hγ e.1 e'.1
          subst hβγ
          have hkk : k = k' := hι (hk.trans hk'.symm)
          subst hkk
          rw [oa_inj h4 hab hr hs (hra.trans (by rw [hsa, e.2])) (hrb.trans (by rw [hsb, e'.2]))]
    · exfalso
      exact hrn (allnone r hr (rowB_eq_inr.mp hxa).1 (rowB_eq_inr.mp hxb).1)
    · simp [rowA, rowC] at hxa
    · exfalso
      exact hsn (allnone s hs (rowB_eq_inr.mp hxa.symm).1 (rowB_eq_inr.mp hxb.symm).1)
    · simp only [rowC, Sum.inr.injEq] at hxa hxb
      rw [oa_inj hU hab hr hs hxa hxb]
  · rintro ⟨P, Q⟩ -
    rcases P with ⟨p, α⟩ | k <;> rcases Q with ⟨q, α'⟩ | k'
    · obtain ⟨β, hβ, e1, e2⟩ := oa_ex h5 hab' p q
      by_cases hι' : ∃ k, ι k = β (Fin.last d)
      · obtain ⟨k, hk⟩ := hι'
        obtain ⟨r, hr, r1, r2⟩ := oa_ex h4 hab (some α) (some α')
        refine ⟨rowB β k r, Or.inl (Or.inr ⟨β, hβ, k, hk, r, hr, fun h => by simp [h] at r1, rfl⟩), ?_⟩
        simp [rowB, r1, r2, e1, e2]
      · push Not at hι'
        obtain ⟨r, hr, r1, r2⟩ := oa_ex h3 hab α α'
        exact ⟨rowA β r, Or.inl (Or.inl ⟨β, hβ, hι', r, hr, rfl⟩), by simp [rowA, r1, r2, e1, e2]⟩
    · obtain ⟨β, hβ, e1, e2⟩ := oa_ex h5 ha4 p (ι k')
      obtain ⟨r, hr, r1, r2⟩ := oa_ex h4 hab (some α) none
      refine ⟨rowB β k' r, Or.inl (Or.inr ⟨β, hβ, k', e2.symm, r, hr, fun h => by simp [h] at r1, rfl⟩), ?_⟩
      simp [rowB, r1, r2, e1]
    · obtain ⟨β, hβ, e1, e2⟩ := oa_ex h5 hb4 q (ι k)
      obtain ⟨r, hr, r1, r2⟩ := oa_ex h4 hab none (some α')
      refine ⟨rowB β k r, Or.inl (Or.inr ⟨β, hβ, k, e2.symm, r, hr, fun h => by simp [h] at r2, rfl⟩), ?_⟩
      simp [rowB, r1, r2, e1]
    · obtain ⟨r, hr, r1, r2⟩ := oa_ex hU hab k k'
      exact ⟨rowC r, Or.inr ⟨r, hr, rfl⟩, by simp [rowC, r1, r2]⟩

private lemma oa_of_range {ι α : Type*} [Fintype ι] [Fintype α] {k : ℕ} (f : ι → Fin k → α)
    (hcard : Fintype.card ι = Fintype.card α * Fintype.card α)
    (h : ∀ a b : Fin k, a ≠ b → Function.Injective fun i => (f i a, f i b)) :
    IsOA k (Set.range f) := by
  intro a b hab
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij; rw [h a b hab hij]
  · intro xy _
    have hb : Function.Bijective fun i => (f i a, f i b) :=
      (Fintype.bijective_iff_injective_and_card _).mpr ⟨h a b hab, by rw [hcard, Fintype.card_prod]⟩
    obtain ⟨i, hi⟩ := hb.2 xy
    exact ⟨f i, ⟨i, rfl⟩, hi⟩

private lemma getFamily {s n : ℕ} (h : s ≤ maxMOLS n) :
    ∃ L : Fin s → LatinSquare n, ∀ i j, i ≠ j → IsOrthogonal (L i) (L j) := by
  obtain ⟨S, hS, hp⟩ := mols_attain n
  have hle : s ≤ S.card := by rw [hS]; exact h
  let E : Fin s ↪ S := (Fin.castLEEmb hle).trans
    (Fintype.equivFinOfCardEq (α := S) (by simp : Fintype.card S = S.card)).symm.toEmbedding
  exact ⟨fun i => E i, fun i j hij => hp (E i).2 (E j).2 (fun eq => hij (E.injective (Subtype.ext eq)))⟩

private def fullRow {s n : ℕ} (L : Fin s → LatinSquare n) (p : Fin n × Fin n) : Fin (s + 2) → Fin n :=
  Fin.cases p.1 (Fin.cases p.2 (fun v => (L v).mat p.1 p.2))

private lemma oa_input {s n : ℕ} (h : s ≤ maxMOLS n) : ∃ S, @IsOA (Fin n) (s + 2) S := by
  obtain ⟨L, hL⟩ := getFamily h
  refine ⟨Set.range (fullRow L), oa_of_range _ (by simp) ?_⟩
  intro c d hcd
  rintro ⟨i, j⟩ ⟨i', j'⟩ eq
  obtain ⟨hx, hy⟩ := Prod.mk.inj eq
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨c, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ d with rfl | ⟨d, rfl⟩
    · exact (hcd rfl).elim
    rcases Fin.eq_zero_or_eq_succ d with rfl | ⟨d, rfl⟩
    · exact Prod.ext hx hy
    change i = i' at hx; subst i'
    exact Prod.ext rfl ((L d).row_injective i hy)
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨c, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ d with rfl | ⟨d, rfl⟩
    · exact Prod.ext hy hx
    rcases Fin.eq_zero_or_eq_succ d with rfl | ⟨d, rfl⟩
    · exact (hcd rfl).elim
    change j = j' at hx; subst j'
    exact Prod.ext ((L d).col_injective j hy) rfl
  rcases Fin.eq_zero_or_eq_succ d with rfl | ⟨d, rfl⟩
  · change i = i' at hy; subst i'
    exact Prod.ext rfl ((L c).row_injective i hx)
  rcases Fin.eq_zero_or_eq_succ d with rfl | ⟨d, rfl⟩
  · change j = j' at hy; subst j'
    exact Prod.ext ((L c).col_injective j hx) rfl
  exact hL c d (fun E => hcd (E ▸ rfl)) (Prod.ext hx hy)

private lemma oa_relabel {α β : Type*} {d : ℕ} {S : Set (Fin d → α)} (hS : IsOA d S)
    (e : Fin d → α ≃ β) : IsOA d ((fun (r : Fin d → α) i => e i (r i)) '' S) := by
  intro a b hab
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩ eq
    rw [oa_inj hS hab hr hs ((e a).injective (Prod.mk.inj eq).1) ((e b).injective (Prod.mk.inj eq).2)]
  · rintro ⟨x, y⟩ -
    obtain ⟨r, hr, hx, hy⟩ := oa_ex hS hab ((e a).symm x) ((e b).symm y)
    exact ⟨_, ⟨r, hr, rfl⟩, by simp [hx, hy]⟩

private lemma oa_withNone {s m : ℕ} (h : s ≤ maxMOLS (m + 1)) :
    ∃ S, @IsOA (Option (Fin m)) (s + 2) S ∧ (fun _ => none) ∈ S := by
  obtain ⟨A, hA⟩ := oa_input h
  obtain ⟨r, hr, _, _⟩ := oa_ex hA (show (0 : Fin (s + 2)) ≠ 1 from Fin.zero_ne_one) 0 0
  let e : Fin (m + 1) ≃ Option (Fin m) := (Fintype.equivFinOfCardEq (by simp)).symm
  let E (i : Fin (s + 2)) := e.trans (Equiv.swap (e (r i)) none)
  refine ⟨_, oa_relabel hA E, r, hr, ?_⟩
  funext i; simp [E]

private lemma oa_output {s n : ℕ} (hn : 2 ≤ n) {α : Type*} (e : α ≃ Fin n)
    {S : Set (Fin (s + 2) → α)} (h : IsOA (s + 2) S) : s ≤ maxMOLS n := by
  let a : Fin (s + 2) := 0
  let b : Fin (s + 2) := (0 : Fin (s + 1)).succ
  let c (i : Fin s) := i.succ.succ
  have hab : a ≠ b := Ne.symm (Fin.succ_ne_zero _)
  have hac (i : Fin s) : a ≠ c i := Ne.symm (Fin.succ_ne_zero _)
  have hbc (i : Fin s) : b ≠ c i := fun eq => Fin.succ_ne_zero i (Fin.succ_injective _ eq).symm
  let row (p : Fin n × Fin n) := (oa_ex h hab (e.symm p.1) (e.symm p.2)).choose
  have hr (p : Fin n × Fin n) : row p ∈ S ∧ row p a = e.symm p.1 ∧ row p b = e.symm p.2 :=
    (oa_ex h hab _ _).choose_spec
  have key {u v : Fin (s + 2)} (huv : u ≠ v) {p q : Fin n × Fin n}
      (hu : row p u = row q u) (hv : row p v = row q v) : p = q := by
    have eq := oa_inj h huv (hr p).1 (hr q).1 hu hv
    exact Prod.ext (e.symm.injective ((hr p).2.1.symm.trans ((congrFun eq a).trans (hr q).2.1)))
      (e.symm.injective ((hr p).2.2.symm.trans ((congrFun eq b).trans (hr q).2.2)))
  let L (i : Fin s) : LatinSquare n := {
    mat := fun x y => e (row (x, y) (c i))
    row_injective := fun x y z eq => congrArg Prod.snd (key (hac i)
      ((hr (x, y)).2.1.trans (hr (x, z)).2.1.symm) (e.injective eq))
    col_injective := fun y x z eq => congrArg Prod.fst (key (hbc i)
      ((hr (x, y)).2.2.trans (hr (z, y)).2.2.symm) (e.injective eq)) }
  have horth {i j : Fin s} (hij : i ≠ j) : IsOrthogonal (L i) (L j) := fun p q eq =>
    key (show c i ≠ c j from fun E => hij (Fin.succ_injective _ (Fin.succ_injective _ E)))
      (e.injective (Prod.mk.inj eq).1) (e.injective (Prod.mk.inj eq).2)
  have hinj : Function.Injective L := by
    intro i j E
    by_contra hij
    have hh := horth hij; rw [E] at hh
    let z : Fin n := ⟨0, by omega⟩
    let o : Fin n := ⟨1, by omega⟩
    obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.mp ((L j).row_injective o)) ((L j).mat z z)
    have eq : (o, k) = (z, z) := hh (Prod.ext hk hk)
    have := congrArg (fun p : Fin n × Fin n => p.1.val) eq
    contradiction
  apply le_csSup (mols_bdd n)
  refine ⟨univ.image L, by rw [card_image_of_injective _ hinj]; simp, ?_⟩
  rintro _ h1 _ h2 hne
  obtain ⟨i, _, rfl⟩ := mem_image.mp h1
  obtain ⟨j, _, rfl⟩ := mem_image.mp h2
  exact horth (fun eq => hne (congrArg L eq))

private lemma wilson_recursion (m t u s : ℕ) (hm : 1 ≤ m) (hu : 1 ≤ u) (hut : u ≤ t)
    (h1 : s ≤ maxMOLS m) (h2 : s ≤ maxMOLS (m + 1)) (h3 : s + 1 ≤ maxMOLS t)
    (h4 : s ≤ maxMOLS u) : s ≤ maxMOLS (m * t + u) := by
  obtain ⟨A, hA⟩ := oa_input h3
  obtain ⟨B, hB⟩ := oa_input h1
  obtain ⟨C, hC, h0⟩ := oa_withNone h2
  obtain ⟨D, hD⟩ := oa_input h4
  have hOA := wilson_OA hA hB hC h0 hD (Fin.castLEEmb hut).injective
  let e : ((Fin t × Fin m) ⊕ Fin u) ≃ Fin (m * t + u) :=
    Fintype.equivFinOfCardEq (by simp [Nat.mul_comm])
  exact oa_output (by nlinarith) e hOA

private lemma exists_pow_two_near {z : ℝ} (hz : 3 ≤ z) :
    ∃ k : ℕ, 2 ≤ k ∧ z < ((2 ^ k : ℕ) : ℝ) ∧ ((2 ^ k : ℕ) : ℝ) ≤ 2 * z := by
  let f : ℕ := ⌊z⌋₊
  have hf3 : 3 ≤ f := Nat.le_floor (by exact_mod_cast hz)
  have hlog : 1 ≤ Nat.log 2 f := Nat.le_log_of_pow_le (by omega) (by omega)
  refine ⟨Nat.log 2 f + 1, by omega, ?_, ?_⟩
  · have hlt : f < 2 ^ (Nat.log 2 f + 1) := Nat.lt_pow_succ_log_self (by omega) f
    have hz1 : z < (f : ℝ) + 1 := Nat.lt_floor_add_one z
    have hleR : (f : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 f + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
    exact hz1.trans_le hleR
  · have hpow : 2 ^ Nat.log 2 f ≤ f := Nat.pow_log_le_self 2 (by omega)
    have hpow2 : 2 ^ (Nat.log 2 f + 1) ≤ 2 * f := by rw [pow_succ']; omega
    have hfR : (f : ℝ) ≤ z := Nat.floor_le (by linarith)
    have hpowR : ((2 ^ (Nat.log 2 f + 1) : ℕ) : ℝ) ≤ 2 * (f : ℝ) := by exact_mod_cast hpow2
    linarith

end MOLS

/- ### Section 2: Elementary prime reciprocal bound via Chebyshev's theta bound -/

section PrimeReciprocal

private lemma inv_mul_log_le_log_log_diff {n : ℕ} (hn : 4 ≤ n) :
    1 / ((n : ℝ) * Real.log (n : ℝ)) ≤
      Real.log (Real.log (n : ℝ)) - Real.log (Real.log ((n - 1 : ℕ) : ℝ)) := by
  have hnm1_ge : (3 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ n - 1)
  have hn_eq : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    have : (n - 1) + 1 = n := by omega
    exact_mod_cast this
  have hlt : ((n - 1 : ℕ) : ℝ) < (n : ℝ) := by linarith
  have hderiv : ∀ x ∈ Set.Icc ((n - 1 : ℕ) : ℝ) (n : ℝ),
      HasDerivAt (fun t => Real.log (Real.log t)) (1 / (x * Real.log x)) x := by
    intro x hx
    have hx1 : (1 : ℝ) < x := by linarith [hx.1]
    have hx0 : x ≠ 0 := by linarith
    have hlog_pos : 0 < Real.log x := Real.log_pos hx1
    have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have h2 : HasDerivAt (fun t => Real.log (Real.log t)) (x⁻¹ / Real.log x) x :=
      h1.log hlog_pos.ne'
    convert h2 using 1
    field_simp
  have hcont : ContinuousOn (fun t => Real.log (Real.log t)) (Set.Icc ((n - 1 : ℕ) : ℝ) (n : ℝ)) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => Real.log (Real.log t))
    (fun t => 1 / (t * Real.log t)) hlt hcont (fun x hx => hderiv x (Set.Ioo_subset_Icc_self hx))
  have hsub1 : (n : ℝ) - ((n - 1 : ℕ) : ℝ) = 1 := by linarith
  rw [hsub1, div_one] at hslope
  rw [← hslope]
  have hc_pos : 0 < c := by linarith [hc.1]
  have hclog_pos : 0 < Real.log c := Real.log_pos (by linarith [hc.1])
  have hn_pos : 0 < (n : ℝ) := by linarith
  have hlog_le : Real.log c ≤ Real.log (n : ℝ) := Real.log_le_log hc_pos hc.2.le
  have hmul : c * Real.log c ≤ (n : ℝ) * Real.log (n : ℝ) := by
    exact mul_le_mul hc.2.le hlog_le hclog_pos.le hn_pos.le
  exact one_div_le_one_div_of_le (mul_pos hc_pos hclog_pos) hmul

private lemma sum_inv_mul_log_Ioc_le {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, (1 : ℝ) / ((n : ℝ) * Real.log (n : ℝ)) ≤
      Real.log (Real.log (b : ℝ)) - Real.log (Real.log (a : ℝ)) := by
  induction b with
  | zero => omega
  | succ m ih =>
    by_cases h : a = m + 1
    · subst h; simp
    · have ham : a ≤ m := by omega
      have hIoc : Finset.Ioc a (m + 1) = insert (m + 1) (Finset.Ioc a m) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      have hnot : m + 1 ∉ Finset.Ioc a m := by simp
      rw [hIoc, Finset.sum_insert hnot]
      have hstep := inv_mul_log_le_log_log_diff (n := m + 1) (by omega)
      have hm_eq : ((m + 1 - 1 : ℕ) : ℝ) = (m : ℝ) := by simp
      rw [hm_eq] at hstep
      have hih := ih ham
      linarith

private lemma theta_succ_sub (n : ℕ) (hn : 1 ≤ n) :
    Chebyshev.theta ((n : ℕ) : ℝ) - Chebyshev.theta (((n - 1 : ℕ) : ℕ) : ℝ) =
      if n.Prime then Real.log (n : ℝ) else 0 := by
  rw [Chebyshev.theta, Chebyshev.theta]
  simp only [Nat.floor_natCast]
  have hIoc : Finset.Ioc 0 n = insert n (Finset.Ioc 0 (n - 1)) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
  have hnot : n ∉ Finset.Ioc 0 (n - 1) := by simp
  rw [Finset.sum_filter, Finset.sum_filter, hIoc, Finset.sum_insert hnot]
  ring

private lemma abel_sum_Ioc (F f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, (F n - F (n - 1)) * f n =
      if a = b then 0 else
        F b * f b - F a * f (a + 1) + ∑ n ∈ Finset.Ioc a (b - 1), F n * (f n - f (n + 1)) := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0; simp
  | succ m ih =>
    by_cases h : a = m + 1
    · subst h; simp
    · have ham : a ≤ m := by omega
      have hIoc : Finset.Ioc a (m + 1) = insert (m + 1) (Finset.Ioc a m) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      have hnot : m + 1 ∉ Finset.Ioc a m := by simp
      rw [hIoc, Finset.sum_insert hnot, ih ham, if_neg h]
      by_cases ham_eq : a = m
      · subst ham_eq; simp; ring
      · rw [if_neg ham_eq]
        have hIoc2 : Finset.Ioc a m = insert m (Finset.Ioc a (m - 1)) := by
          ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
        have hnot2 : m ∉ Finset.Ioc a (m - 1) := by simp only [Finset.mem_Ioc]; omega
        simp only [Nat.add_sub_cancel]
        rw [hIoc2, Finset.sum_insert hnot2]
        ring

private lemma abel_back_Ioc (f : ℕ → ℝ) {a b : ℕ} (hab : a < b) :
    (b : ℝ) * f b + ∑ n ∈ Finset.Ioc a (b - 1), (n : ℝ) * (f n - f (n + 1)) =
      ((a + 1 : ℕ) : ℝ) * f (a + 1) + ∑ n ∈ Finset.Ioc (a + 1) b, f n := by
  induction b with
  | zero => omega
  | succ m ih =>
    by_cases h : a = m
    · subst h; simp
    · have ham : a < m := by omega
      have hIoc1 : Finset.Ioc a m = insert m (Finset.Ioc a (m - 1)) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      have hnot1 : m ∉ Finset.Ioc a (m - 1) := by simp only [Finset.mem_Ioc]; omega
      have hIoc2 : Finset.Ioc (a + 1) (m + 1) = insert (m + 1) (Finset.Ioc (a + 1) m) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      have hnot2 : m + 1 ∉ Finset.Ioc (a + 1) m := by simp only [Finset.mem_Ioc]; omega
      simp only [Nat.add_sub_cancel]
      rw [hIoc1, Finset.sum_insert hnot1, hIoc2, Finset.sum_insert hnot2]
      have hih := ih ham
      push_cast at hih ⊢
      linarith

private lemma sum_prime_inv_Ioc_le {a b : ℕ} (ha : 4 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      Real.log 4 * (1 / Real.log (a : ℝ) + Real.log (Real.log (b : ℝ) / Real.log (a : ℝ))) := by
  have ha_pos : (0 : ℝ) < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < a))
  have hb_pos : (0 : ℝ) < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  have hlog4_pos : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  by_cases heq : a = b
  · subst heq
    simp only [Finset.Ioc_self, Finset.filter_empty, Finset.sum_empty, div_self ha_pos.ne',
      Real.log_one, add_zero]
    positivity
  have hab_lt : a < b := by omega
  let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) * Real.log (n : ℝ))
  have hsum_eq :
      ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) =
      ∑ n ∈ Finset.Ioc a b,
        (Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n - 1 : ℕ) : ℝ)) * f n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := by simp only [Finset.mem_Ioc] at hn; omega
    have hn2 : 2 ≤ n := by simp only [Finset.mem_Ioc] at hn; omega
    rw [theta_succ_sub n hn1]
    split_ifs with hp
    · have hlogn : Real.log (n : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      dsimp only [f]
      field_simp
    · simp
  rw [hsum_eq, abel_sum_Ioc (fun n => Chebyshev.theta (n : ℝ)) f hab, if_neg heq]
  have hf_anti : ∀ n, 2 ≤ n → f (n + 1) ≤ f n := by
    intro n hn
    dsimp only [f]
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hle1 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
    have hle2 : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_le_log hn_pos hle1
    exact one_div_le_one_div_of_le (mul_pos hn_pos hlog_pos)
      (mul_le_mul hle1 hle2 hlog_pos.le (by positivity))
  have hf_nonneg : ∀ n, 2 ≤ n → 0 ≤ f n := by
    intro n hn
    dsimp only [f]
    have : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    positivity
  have h1 : Chebyshev.theta (b : ℝ) * f b - Chebyshev.theta (a : ℝ) * f (a + 1) +
      ∑ n ∈ Finset.Ioc a (b - 1), Chebyshev.theta (n : ℝ) * (f n - f (n + 1)) ≤
      Real.log 4 * ((b : ℝ) * f b +
        ∑ n ∈ Finset.Ioc a (b - 1), (n : ℝ) * (f n - f (n + 1))) := by
    have hta : 0 ≤ Chebyshev.theta (a : ℝ) * f (a + 1) :=
      mul_nonneg (Chebyshev.theta_nonneg _) (hf_nonneg (a + 1) (by omega))
    have htb : Chebyshev.theta (b : ℝ) * f b ≤ (Real.log 4 * (b : ℝ)) * f b :=
      mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by positivity))
        (hf_nonneg b (by omega))
    have htsum : ∑ n ∈ Finset.Ioc a (b - 1), Chebyshev.theta (n : ℝ) * (f n - f (n + 1)) ≤
        ∑ n ∈ Finset.Ioc a (b - 1), (Real.log 4 * (n : ℝ)) * (f n - f (n + 1)) := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn2 : 2 ≤ n := by simp only [Finset.mem_Ioc] at hn; omega
      exact mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by positivity))
        (sub_nonneg.mpr (hf_anti n hn2))
    rw [mul_add, Finset.mul_sum]
    have htsum' : ∑ n ∈ Finset.Ioc a (b - 1), Real.log 4 * ((n : ℝ) * (f n - f (n + 1))) =
        ∑ n ∈ Finset.Ioc a (b - 1), (Real.log 4 * (n : ℝ)) * (f n - f (n + 1)) := by
      refine Finset.sum_congr rfl fun n _ => by ring
    rw [htsum']
    linarith
  refine h1.trans ?_
  rw [abel_back_Ioc f hab_lt]
  refine mul_le_mul_of_nonneg_left ?_ hlog4_pos
  have ha1_term : ((a + 1 : ℕ) : ℝ) * f (a + 1) = 1 / Real.log ((a + 1 : ℕ) : ℝ) := by
    dsimp only [f]
    have h0 : ((a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have ha1_le : 1 / Real.log ((a + 1 : ℕ) : ℝ) ≤ 1 / Real.log (a : ℝ) :=
    one_div_le_one_div_of_le ha_pos (Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ a))
  have hsum_le : ∑ n ∈ Finset.Ioc (a + 1) b, f n ≤
      Real.log (Real.log (b : ℝ)) - Real.log (Real.log ((a + 1 : ℕ) : ℝ)) :=
    sum_inv_mul_log_Ioc_le (by omega) (by omega)
  have hlog_mono : Real.log (Real.log (a : ℝ)) ≤ Real.log (Real.log ((a + 1 : ℕ) : ℝ)) :=
    Real.log_le_log ha_pos (Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ a))
  rw [Real.log_div hb_pos.ne' ha_pos.ne']
  linarith

private lemma sum_two_div_prime_bucket_le_two {A B : ℕ} (hA : 100 ≤ A) (hAB : A ≤ B)
    (hB : B ≤ 2 * A + 1) :
    ∑ p ∈ (Finset.Ioc (2 ^ A) (2 ^ B)).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ≤ 2 := by
  have h2A4 : 4 ≤ 2 ^ A := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ A := Nat.pow_le_pow_right (by omega) (by omega)
  have h2AB : 2 ^ A ≤ 2 ^ B := Nat.pow_le_pow_right (by omega) hAB
  have hsum := sum_prime_inv_Ioc_le h2A4 h2AB
  have hscale :
      ∑ p ∈ (Finset.Ioc (2 ^ A) (2 ^ B)).filter Nat.Prime, (2 : ℝ) / (p : ℝ) =
      2 * ∑ p ∈ (Finset.Ioc (2 ^ A) (2 ^ B)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
  rw [hscale]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt : Real.log 2 < 0.694 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hlogA : Real.log ((2 ^ A : ℕ) : ℝ) = (A : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlogB : Real.log ((2 ^ B : ℕ) : ℝ) = (B : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hA_pos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (by omega : 0 < A)
  have hdiv_eq : Real.log ((2 ^ B : ℕ) : ℝ) / Real.log ((2 ^ A : ℕ) : ℝ) = (B : ℝ) / (A : ℝ) := by
    rw [hlogA, hlogB]; field_simp [hlog2_pos.ne']
  have hBA_le : (B : ℝ) / (A : ℝ) ≤ 201 / 100 := by
    rw [div_le_div_iff₀ hA_pos (by norm_num : (0 : ℝ) < 100)]
    have : B * 100 ≤ 201 * A := by omega
    exact_mod_cast this
  have hlog_BA : Real.log ((B : ℝ) / (A : ℝ)) ≤ Real.log 2 + 1 / 200 := by
    have h1 : Real.log ((B : ℝ) / (A : ℝ)) ≤ Real.log (201 / 100) :=
      Real.log_le_log (div_pos (by exact_mod_cast (by omega : 0 < B)) hA_pos) hBA_le
    have h2 : Real.log (201 / 100 : ℝ) = Real.log 2 + Real.log (201 / 200 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h3 : Real.log (201 / 200 : ℝ) ≤ 201 / 200 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hinv_le : 1 / Real.log ((2 ^ A : ℕ) : ℝ) ≤ 1 / (100 * Real.log 2) := by
    rw [hlogA]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hA) hlog2_pos.le)
  calc 2 * ∑ p ∈ (Finset.Ioc (2 ^ A) (2 ^ B)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ 2 * (Real.log 4 * (1 / Real.log ((2 ^ A : ℕ) : ℝ) +
          Real.log (Real.log ((2 ^ B : ℕ) : ℝ) / Real.log ((2 ^ A : ℕ) : ℝ)))) := by
        gcongr
    _ = 4 * Real.log 2 * (1 / Real.log ((2 ^ A : ℕ) : ℝ) + Real.log ((B : ℝ) / (A : ℝ))) := by
        rw [hlog4_eq, hdiv_eq]; ring
    _ ≤ 4 * Real.log 2 * (1 / (100 * Real.log 2) + (Real.log 2 + 1 / 200)) := by
        gcongr
    _ = 4 / 100 + 4 * (Real.log 2) ^ 2 + 4 * Real.log 2 / 200 := by
        field_simp [hlog2_pos.ne']; ring
    _ ≤ 2 := by nlinarith

end PrimeReciprocal

/- ### Section 3: Pure combinatorial Bonferroni and multi-bucket telescoping sieve -/

section CombinatorialSieve

private lemma alt_sum_choose (m M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * (m.choose j : ℝ) =
      if m = 0 then 1 else (-1 : ℝ) ^ M * ((m - 1).choose M : ℝ) := by
  induction M with
  | zero =>
    by_cases hm : m = 0 <;> simp [hm]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hm : m = 0
    · subst hm; simp
    · simp only [if_neg hm]
      have hpas : m.choose (k + 1) = (m - 1).choose k + (m - 1).choose (k + 1) := by
        cases m with
        | zero => exact absurd rfl hm
        | succ m' => exact Nat.choose_succ_succ m' k
      rw [hpas]
      push_cast
      ring

private lemma bonferroni_sum_eq {α : Type*} [DecidableEq α] (B : Finset α)
    (P : α → Prop) [DecidablePred P] (M : ℕ) :
    ∑ S ∈ B.powerset.filter (fun S => S.card ≤ M),
        (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, P p then (1 : ℝ) else 0) =
      ∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * ((B.filter P).card.choose j : ℝ) := by
  set F := B.filter P
  have h1 :
      ∑ S ∈ B.powerset.filter (fun S => S.card ≤ M),
        (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, P p then (1 : ℝ) else 0) =
      ∑ S ∈ F.powerset.filter (fun S => S.card ≤ M), (-1 : ℝ) ^ S.card := by
    have hite : ∀ S ∈ B.powerset.filter (fun S => S.card ≤ M),
        (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, P p then (1 : ℝ) else 0) =
        if ∀ p ∈ S, P p then (-1 : ℝ) ^ S.card else 0 := fun S _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, F]
    constructor
    · rintro ⟨⟨hSB, hcard⟩, hP⟩
      exact ⟨fun p hp => Finset.mem_filter.mpr ⟨hSB hp, hP p hp⟩, hcard⟩
    · rintro ⟨hSF, hcard⟩
      exact ⟨⟨fun p hp => (Finset.mem_filter.mp (hSF hp)).1, hcard⟩,
        fun p hp => (Finset.mem_filter.mp (hSF hp)).2⟩
  rw [h1]
  have hpart :
      ∑ S ∈ F.powerset.filter (fun S => S.card ≤ M), (-1 : ℝ) ^ S.card =
      ∑ j ∈ Finset.range (M + 1),
        ∑ S ∈ F.powersetCard j, (-1 : ℝ) ^ S.card := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard]
      constructor
      · rintro ⟨hSF, hcard⟩; exact ⟨S.card, by omega, hSF, rfl⟩
      · rintro ⟨j, hj, hSF, hcard⟩; exact ⟨hSF, by omega⟩
    · intro i _ j _ hij
      show Disjoint (F.powersetCard i) (F.powersetCard j)
      rw [Finset.disjoint_left]
      intro S hi hj
      exact hij ((Finset.mem_powersetCard.mp hi).2.symm.trans (Finset.mem_powersetCard.mp hj).2)
  rw [hpart]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconst : ∑ S ∈ F.powersetCard j, (-1 : ℝ) ^ S.card =
      ∑ _S ∈ F.powersetCard j, (-1 : ℝ) ^ j :=
    Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2]
  rw [hconst, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]

private lemma bonferroni_upper {α : Type*} [DecidableEq α] (B : Finset α)
    (P : α → Prop) [DecidablePred P] (r : ℕ) :
    (if ∀ p ∈ B, ¬ P p then (1 : ℝ) else 0) ≤
      ∑ S ∈ B.powerset.filter (fun S => S.card ≤ 2 * r),
        (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, P p then (1 : ℝ) else 0) := by
  rw [bonferroni_sum_eq, alt_sum_choose]
  by_cases h0 : (B.filter P).card = 0
  · rw [if_pos h0]
    have hall : ∀ p ∈ B, ¬ P p := by
      intro p hp hPp
      have hmem : p ∈ B.filter P := Finset.mem_filter.mpr ⟨hp, hPp⟩
      exact Finset.card_pos.mpr ⟨p, hmem⟩ |>.ne' h0
    rw [if_pos hall]
  · rw [if_neg h0]
    have hex : ¬ (∀ p ∈ B, ¬ P p) := by
      intro hall
      apply h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact hall
    rw [if_neg hex]
    have hpow : (-1 : ℝ) ^ (2 * r) = 1 := by rw [pow_mul]; norm_num
    rw [hpow, one_mul]
    positivity

private lemma bonferroni_lower {α : Type*} [DecidableEq α] (B : Finset α)
    (P : α → Prop) [DecidablePred P] {r : ℕ} (hr : 1 ≤ r) :
    ∑ S ∈ B.powerset.filter (fun S => S.card ≤ 2 * r - 1),
        (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, P p then (1 : ℝ) else 0) ≤
      (if ∀ p ∈ B, ¬ P p then (1 : ℝ) else 0) := by
  rw [bonferroni_sum_eq, alt_sum_choose]
  by_cases h0 : (B.filter P).card = 0
  · rw [if_pos h0]
    have hall : ∀ p ∈ B, ¬ P p := by
      intro p hp hPp
      exact (Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hPp⟩⟩).ne' h0
    rw [if_pos hall]
  · rw [if_neg h0]
    have hex : ¬ (∀ p ∈ B, ¬ P p) := by
      intro hall
      apply h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact hall
    rw [if_neg hex]
    have hodd : (-1 : ℝ) ^ (2 * r - 1) = -1 := by
      have : 2 * r - 1 = 2 * (r - 1) + 1 := by omega
      rw [this, pow_succ, pow_mul]; norm_num
    rw [hodd]
    have : (0 : ℝ) ≤ (((B.filter P).card - 1).choose (2 * r - 1) : ℝ) := by positivity
    linarith

private lemma bonferroni_diff {α : Type*} [DecidableEq α] (B : Finset α)
    (P : α → Prop) [DecidablePred P] {r : ℕ} (hr : 1 ≤ r) :
    (∑ S ∈ B.powerset.filter (fun S => S.card ≤ 2 * r),
        (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, P p then (1 : ℝ) else 0)) -
      (∑ S ∈ B.powerset.filter (fun S => S.card ≤ 2 * r - 1),
        (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, P p then (1 : ℝ) else 0)) =
      ∑ S ∈ B.powersetCard (2 * r), (if ∀ p ∈ S, P p then (1 : ℝ) else 0) := by
  have hsub : B.powerset.filter (fun S => S.card ≤ 2 * r) =
      B.powerset.filter (fun S => S.card ≤ 2 * r - 1) ∪ B.powersetCard (2 * r) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hSB, hc⟩
      by_cases h : S.card = 2 * r
      · exact Or.inr ⟨hSB, h⟩
      · exact Or.inl ⟨hSB, by omega⟩
    · rintro (⟨hSB, hc⟩ | ⟨hSB, hc⟩)
      · exact ⟨hSB, by omega⟩
      · exact ⟨hSB, by omega⟩
  have hdisj : Disjoint (B.powerset.filter (fun S => S.card ≤ 2 * r - 1)) (B.powersetCard (2 * r)) := by
    rw [Finset.disjoint_left]
    intro S h1 h2
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at h1 h2
    omega
  rw [hsub, Finset.sum_union hdisj, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hc : S.card = 2 * r := (Finset.mem_powersetCard.mp hS).2
  rw [hc, pow_mul]
  norm_num

private lemma prod_one_sub_weight_sum {α : Type*} [DecidableEq α] (B S : Finset α)
    (hSB : S ⊆ B) (ν : α → ℝ) :
    ∑ A ∈ B.powerset.filter (fun A => S ⊆ A),
        ((∏ p ∈ A, ν p) * (∏ p ∈ B \ A, (1 - ν p))) =
      ∏ p ∈ S, ν p := by
  have hbij :
      ∑ A ∈ B.powerset.filter (fun A => S ⊆ A),
        ((∏ p ∈ A, ν p) * (∏ p ∈ B \ A, (1 - ν p))) =
      ∑ T ∈ (B \ S).powerset,
        ((∏ p ∈ S ∪ T, ν p) * (∏ p ∈ (B \ S) \ T, (1 - ν p))) := by
    refine Finset.sum_nbij' (fun A => A \ S) (fun T => S ∪ T) ?_ ?_ ?_ ?_ ?_
    · intro A hA
      simp only [Finset.mem_filter, Finset.mem_powerset] at hA ⊢
      exact Finset.sdiff_subset_sdiff hA.1 subset_rfl
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
      exact ⟨Finset.union_subset hSB (hT.trans Finset.sdiff_subset), Finset.subset_union_left⟩
    · intro A hA
      simp only [Finset.mem_filter] at hA
      exact Finset.union_sdiff_of_subset hA.2
    · intro T hT
      simp only [Finset.mem_powerset] at hT
      have hdisj : Disjoint S T := Disjoint.mono_right hT disjoint_sdiff_self_right
      exact Finset.union_sdiff_cancel_left hdisj
    · intro A hA
      simp only [Finset.mem_filter, Finset.mem_powerset] at hA
      have h1 : S ∪ (A \ S) = A := Finset.union_sdiff_of_subset hA.2
      have h2 : (B \ S) \ (A \ S) = B \ A := by
        ext x; simp only [Finset.mem_sdiff]; tauto
      rw [h1, h2]
  rw [hbij]
  have hfac : ∀ T ∈ (B \ S).powerset,
      (∏ p ∈ S ∪ T, ν p) * (∏ p ∈ (B \ S) \ T, (1 - ν p)) =
      (∏ p ∈ S, ν p) * ((∏ p ∈ T, ν p) * (∏ p ∈ (B \ S) \ T, (1 - ν p))) := by
    intro T hT
    have hdisj : Disjoint S T :=
      Disjoint.mono_right (Finset.mem_powerset.mp hT) disjoint_sdiff_self_right
    rw [Finset.prod_union hdisj]; ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  have htot : ∑ T ∈ (B \ S).powerset,
      ((∏ p ∈ T, ν p) * (∏ p ∈ (B \ S) \ T, (1 - ν p))) = ∏ p ∈ B \ S, (ν p + (1 - ν p)) := by
    rw [Finset.prod_add]
  rw [htot]
  have hone : ∏ p ∈ B \ S, (ν p + (1 - ν p)) = 1 := by
    refine Finset.prod_eq_one fun p _ => by ring
  rw [hone, mul_one]

private lemma expect_upper_ge_prod {α : Type*} [DecidableEq α] (B : Finset α)
    (ν : α → ℝ) (hν : ∀ p ∈ B, 0 ≤ ν p ∧ ν p ≤ 1) (r : ℕ) :
    ∏ p ∈ B, (1 - ν p) ≤
      ∑ S ∈ B.powerset.filter (fun S => S.card ≤ 2 * r),
        (-1 : ℝ) ^ S.card * (∏ p ∈ S, ν p) := by
  let w : Finset α → ℝ := fun A => (∏ p ∈ A, ν p) * (∏ p ∈ B \ A, (1 - ν p))
  have hw_nonneg : ∀ A ∈ B.powerset, 0 ≤ w A := by
    intro A hA
    have hAB := Finset.mem_powerset.mp hA
    refine mul_nonneg (Finset.prod_nonneg fun p hp => (hν p (hAB hp)).1)
      (Finset.prod_nonneg fun p hp => ?_)
    have hpB := (Finset.mem_sdiff.mp hp).1
    linarith [(hν p hpB).2]
  have hlhs : ∏ p ∈ B, (1 - ν p) =
      ∑ A ∈ B.powerset, w A * (if ∀ p ∈ B, p ∉ A then (1 : ℝ) else 0) := by
    have hempty : ∀ A ∈ B.powerset, (∀ p ∈ B, p ∉ A) ↔ A = ∅ := by
      intro A hA
      have hAB := Finset.mem_powerset.mp hA
      constructor
      · intro h; ext p; simp only [Finset.notMem_empty, iff_false]
        intro hpA; exact h p (hAB hpA) hpA
      · rintro rfl p _ hp; exact Finset.notMem_empty p hp
    have hcongr : ∑ A ∈ B.powerset, w A * (if ∀ p ∈ B, p ∉ A then (1 : ℝ) else 0) =
        ∑ A ∈ B.powerset, (if A = ∅ then w A else 0) := by
      refine Finset.sum_congr rfl fun A hA => ?_
      by_cases h : A = ∅
      · rw [if_pos ((hempty A hA).mpr h), if_pos h, mul_one]
      · rw [if_neg (fun h' => h ((hempty A hA).mp h')), if_neg h, mul_zero]
    rw [hcongr, Finset.sum_ite_eq' B.powerset ∅, if_pos (Finset.empty_mem_powerset B)]
    simp [w]
  have hrhs : ∑ S ∈ B.powerset.filter (fun S => S.card ≤ 2 * r),
      (-1 : ℝ) ^ S.card * (∏ p ∈ S, ν p) =
      ∑ A ∈ B.powerset, w A *
        (∑ S ∈ B.powerset.filter (fun S => S.card ≤ 2 * r),
          (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, p ∈ A then (1 : ℝ) else 0)) := by
    calc ∑ S ∈ B.powerset.filter (fun S => S.card ≤ 2 * r), (-1 : ℝ) ^ S.card * (∏ p ∈ S, ν p)
        = ∑ S ∈ B.powerset.filter (fun S => S.card ≤ 2 * r),
            (-1 : ℝ) ^ S.card * (∑ A ∈ B.powerset.filter (fun A => S ⊆ A), w A) := by
          refine Finset.sum_congr rfl fun S hS => ?_
          rw [prod_one_sub_weight_sum B S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) ν]
      _ = ∑ S ∈ B.powerset.filter (fun S => S.card ≤ 2 * r),
            ∑ A ∈ B.powerset, w A * ((-1 : ℝ) ^ S.card * (if ∀ p ∈ S, p ∈ A then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun A _ => ?_
          change (-1 : ℝ) ^ S.card * (if S ⊆ A then w A else 0) = _
          by_cases hSA : S ⊆ A
          · have hall : ∀ p ∈ S, p ∈ A := fun p hp => hSA hp
            rw [if_pos hSA, if_pos hall]; ring
          · have hnot : ¬ ∀ p ∈ S, p ∈ A := fun h => hSA (fun p hp => h p hp)
            rw [if_neg hSA, if_neg hnot]; ring
      _ = ∑ A ∈ B.powerset, w A *
            ∑ S ∈ B.powerset.filter (fun S => S.card ≤ 2 * r),
              (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, p ∈ A then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun A _ => (Finset.mul_sum _ _ _).symm
  rw [hlhs, hrhs]
  refine Finset.sum_le_sum fun A hA => ?_
  exact mul_le_mul_of_nonneg_left (bonferroni_upper B (fun p => p ∈ A) r) (hw_nonneg A hA)

private lemma sum_powersetCard_prod_le {α : Type*} [DecidableEq α] (B : Finset α)
    (ν : α → ℝ) (hν : ∀ p ∈ B, 0 ≤ ν p) (m : ℕ) :
    ∑ S ∈ B.powersetCard m, (∏ p ∈ S, ν p) ≤ (∑ p ∈ B, ν p) ^ m / (m.factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hmul : ((k + 1 : ℕ) : ℝ) * ∑ S ∈ B.powersetCard (k + 1), (∏ p ∈ S, ν p) =
        ∑ p ∈ B, ν p * ∑ T ∈ (B.erase p).powersetCard k, (∏ q ∈ T, ν q) := by
      calc ((k + 1 : ℕ) : ℝ) * ∑ S ∈ B.powersetCard (k + 1), (∏ p ∈ S, ν p)
          = ∑ S ∈ B.powersetCard (k + 1), ∑ p ∈ S, ν p * (∏ q ∈ S.erase p, ν q) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun S hS => ?_
            have hcard : S.card = k + 1 := (Finset.mem_powersetCard.mp hS).2
            have hinner : ∀ p ∈ S, ν p * (∏ q ∈ S.erase p, ν q) = ∏ q ∈ S, ν q := fun p hp =>
              Finset.mul_prod_erase S ν hp
            rw [Finset.sum_congr rfl hinner, Finset.sum_const, hcard, nsmul_eq_mul]
        _ = ∑ S ∈ B.powersetCard (k + 1), ∑ p ∈ B,
              if p ∈ S then ν p * (∏ q ∈ S.erase p, ν q) else 0 := by
            refine Finset.sum_congr rfl fun S hS => ?_
            rw [← Finset.sum_filter]
            congr 1; ext p; simp only [Finset.mem_filter]
            exact ⟨fun hp => ⟨(Finset.mem_powersetCard.mp hS).1 hp, hp⟩, fun hp => hp.2⟩
        _ = ∑ p ∈ B, ∑ S ∈ (B.powersetCard (k + 1)).filter (fun S => p ∈ S),
              ν p * (∏ q ∈ S.erase p, ν q) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => (Finset.sum_filter _ _).symm
        _ = ∑ p ∈ B, ν p * ∑ T ∈ (B.erase p).powersetCard k, (∏ q ∈ T, ν q) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            rw [← Finset.mul_sum]
            congr 1
            refine Finset.sum_nbij' (fun S => S.erase p) (fun T => insert p T) ?_ ?_ ?_ ?_ ?_
            · intro S hS
              simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
              refine ⟨Finset.erase_subset_erase p hS.1.1, ?_⟩
              rw [Finset.card_erase_of_mem hS.2, hS.1.2]; omega
            · intro T hT
              simp only [Finset.mem_filter, Finset.mem_powersetCard] at hT ⊢
              have hnot : p ∉ T := fun h => (Finset.mem_erase.mp (hT.1 h)).1 rfl
              refine ⟨⟨Finset.insert_subset hp (hT.1.trans (Finset.erase_subset p B)), ?_⟩,
                Finset.mem_insert_self p T⟩
              rw [Finset.card_insert_of_notMem hnot, hT.2]
            · intro S hS
              exact Finset.insert_erase (Finset.mem_filter.mp hS).2
            · intro T hT
              have hnot : p ∉ T := fun h =>
                (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hT).1 h)).1 rfl
              exact Finset.erase_insert hnot
            · intro _ _; rfl
    have hstep : ((k + 1 : ℕ) : ℝ) * ∑ S ∈ B.powersetCard (k + 1), (∏ p ∈ S, ν p) ≤
        (∑ p ∈ B, ν p) * ∑ T ∈ B.powersetCard k, (∏ q ∈ T, ν q) := by
      rw [hmul, Finset.sum_mul]
      refine Finset.sum_le_sum fun p hp => ?_
      refine mul_le_mul_of_nonneg_left ?_ (hν p hp)
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · exact Finset.powersetCard_mono (Finset.erase_subset p B)
      · intro T hT _
        exact Finset.prod_nonneg fun q hq => hν q ((Finset.mem_powersetCard.mp hT).1 hq)
    have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hfac : ((k + 1).factorial : ℝ) = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hsum_nonneg : 0 ≤ ∑ p ∈ B, ν p := Finset.sum_nonneg hν
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((k + 1).factorial : ℝ)), hfac]
    have hgoal : (((k + 1 : ℕ) : ℝ) * ∑ S ∈ B.powersetCard (k + 1), (∏ p ∈ S, ν p)) *
        (k.factorial : ℝ) ≤ (∑ p ∈ B, ν p) ^ (k + 1) := by
      calc (((k + 1 : ℕ) : ℝ) * ∑ S ∈ B.powersetCard (k + 1), (∏ p ∈ S, ν p)) * (k.factorial : ℝ)
          ≤ ((∑ p ∈ B, ν p) * ∑ T ∈ B.powersetCard k, (∏ q ∈ T, ν q)) * (k.factorial : ℝ) :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
        _ ≤ ((∑ p ∈ B, ν p) * ((∑ p ∈ B, ν p) ^ k / (k.factorial : ℝ))) * (k.factorial : ℝ) := by
            gcongr
        _ = (∑ p ∈ B, ν p) ^ (k + 1) := by
            have hf0 : (k.factorial : ℝ) ≠ 0 := by positivity
            field_simp; ring
    linarith [hgoal]

private lemma prod_ge_telescoping {ι : Type*} [DecidableEq ι] (s : Finset ι) (a L U : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hL : ∀ i ∈ s, L i ≤ a i) (hU : ∀ i ∈ s, a i ≤ U i) :
    (∏ i ∈ s, U i) - ∑ i ∈ s, (U i - L i) * (∏ j ∈ s.erase i, U j) ≤ ∏ i ∈ s, a i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    have hU_nonneg : ∀ i ∈ insert x s, 0 ≤ U i := fun i hi => (ha i hi).trans (hU i hi)
    have ha_s : ∀ i ∈ s, 0 ≤ a i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hL_s : ∀ i ∈ s, L i ≤ a i := fun i hi => hL i (Finset.mem_insert_of_mem hi)
    have hU_s : ∀ i ∈ s, a i ≤ U i := fun i hi => hU i (Finset.mem_insert_of_mem hi)
    have hax : 0 ≤ a x := ha x (Finset.mem_insert_self x s)
    have hLx : L x ≤ a x := hL x (Finset.mem_insert_self x s)
    have hUx : a x ≤ U x := hU x (Finset.mem_insert_self x s)
    have hprod_a_le : ∏ i ∈ s, a i ≤ ∏ i ∈ s, U i :=
      Finset.prod_le_prod ha_s hU_s
    have hsum_ins : ∑ i ∈ insert x s, (U i - L i) * (∏ j ∈ (insert x s).erase i, U j) =
        (U x - L x) * (∏ j ∈ s, U j) +
        U x * ∑ i ∈ s, (U i - L i) * (∏ j ∈ s.erase i, U j) := by
      rw [Finset.sum_insert hx, Finset.erase_insert hx, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hix : i ≠ x := fun h => hx (h ▸ hi)
      rw [Finset.erase_insert_of_ne hix.symm, Finset.prod_insert (fun h => hx (Finset.mem_of_mem_erase h))]
      ring
    rw [Finset.prod_insert hx, Finset.prod_insert hx, hsum_ins]
    have hih := ih ha_s hL_s hU_s
    have h1 : (U x - a x) * (∏ i ∈ s, a i) ≤ (U x - L x) * (∏ i ∈ s, U i) :=
      mul_le_mul (by linarith) hprod_a_le (Finset.prod_nonneg ha_s) (by linarith)
    have h2 : U x * ((∏ i ∈ s, U i) - ∑ i ∈ s, (U i - L i) * (∏ j ∈ s.erase i, U j)) ≤
        U x * (∏ i ∈ s, a i) :=
      mul_le_mul_of_nonneg_left hih (hU_nonneg x (Finset.mem_insert_self x s))
    linarith

private lemma one_sub_ge_exp_neg_two {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp (-2 * t) ≤ 1 - t := by
  have h1 : Real.exp (2 * t) * (1 - t) ≥ 1 := by
    have h2 : 1 + 2 * t ≤ Real.exp (2 * t) := by
      linarith [Real.add_one_le_exp (2 * t)]
    have h3 : (1 + 2 * t) * (1 - t) ≤ Real.exp (2 * t) * (1 - t) :=
      mul_le_mul_of_nonneg_right h2 (by linarith)
    nlinarith
  have hpos : 0 < Real.exp (2 * t) := Real.exp_pos _
  rw [show -2 * t = -(2 * t) by ring, Real.exp_neg]
  rw [inv_le_iff_one_le_mul₀ hpos]
  linarith

end CombinatorialSieve

/- ### Section 4: CRT counting and the 2-dimensional interval sieve for L ≥ C * z^29 -/

section Sieve29

private lemma crt_avoid_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (bad : ℕ → Finset ℕ) (hbad : ∀ p ∈ P, (bad p).card < p) :
    ∃ x0 < ∏ p ∈ P, p, ∀ p ∈ P, x0 % p ∉ bad p := by
  induction P using Finset.induction_on with
  | empty => exact ⟨0, by simp, fun _ hp => absurd hp (Finset.notMem_empty _)⟩
  | @insert p s hp ih =>
    have hpp : p.Prime := hP p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hbad_s : ∀ q ∈ s, (bad q).card < q := fun q hq => hbad q (Finset.mem_insert_of_mem hq)
    obtain ⟨xs, hxs_lt, hxs_good⟩ := ih hs hbad_s
    have hpick : ∃ r < p, r ∉ bad p := by
      have hlt : 0 < ((Finset.range p) \ bad p).card := by
        have h1 : (Finset.range p).card ≤ ((Finset.range p) \ bad p).card + (bad p).card :=
          Finset.card_le_card_sdiff_add_card
        rw [Finset.card_range] at h1
        have := hbad p (Finset.mem_insert_self p s)
        omega
      obtain ⟨r, hr⟩ := Finset.card_pos.mp hlt
      rw [Finset.mem_sdiff, Finset.mem_range] at hr
      exact ⟨r, hr.1, hr.2⟩
    obtain ⟨rp, hrp_lt, hrp_good⟩ := hpick
    set M := ∏ q ∈ s, q
    have hM_pos : 0 < M := Finset.prod_pos fun q hq => (hs q hq).pos
    have hcop : Nat.Coprime p M := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hpp (hs q hq)).mpr (fun h => hp (h ▸ hq))
    let res := Nat.chineseRemainder hcop rp xs
    refine ⟨res.val, ?_, ?_⟩
    · rw [Finset.prod_insert hp]
      exact Nat.chineseRemainder_lt_mul hcop rp xs hpp.ne_zero hM_pos.ne'
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hqs
      · have hmod : res.val % q = rp := by
          have := res.property.1
          rw [Nat.ModEq, Nat.mod_eq_of_lt hrp_lt] at this; exact this
        rw [hmod]; exact hrp_good
      · have hmodM : res.val % M = xs := by
          have := res.property.2
          rw [Nat.ModEq, Nat.mod_eq_of_lt hxs_lt] at this; exact this
        have hqM : q ∣ M := Finset.dvd_prod_of_mem (fun x => x) hqs
        rw [← Nat.mod_mod_of_dvd res.val hqM, hmodM]
        exact hxs_good q hqs

private lemma count_mod_Ico_approx (Y0 L D r : ℕ) (hD : 0 < D) (hr : r < D) :
    |(((Finset.Ico Y0 (Y0 + L)).filter (fun y => y % D = r)).card : ℝ) - (L : ℝ) / (D : ℝ)| ≤ 1 := by
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  -- Split L = q * D + rem
  set q := L / D
  set rem := L % D
  have hL : L = q * D + rem := by rw [mul_comm]; exact (Nat.div_add_mod L D).symm
  have hrem : rem < D := Nat.mod_lt L hD
  -- Partition Ico Y0 (Y0 + L) into q full blocks of length D plus a tail of length rem
  have hblock : ∀ A : ℕ, ((Finset.Ico A (A + D)).filter (fun y => y % D = r)).card = 1 := by
    intro A
    let y0 := A + (r + D - A % D) % D
    have hmem : y0 ∈ (Finset.Ico A (A + D)).filter (fun y => y % D = r) := by
      simp only [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · have := Nat.mod_lt (r + D - A % D) hD; omega
      · have hA : A % D < D := Nat.mod_lt A hD
        have hA_eq : A = D * (A / D) + A % D := (Nat.div_add_mod A D).symm
        have hsum : A + (r + D - A % D) = D * (A / D + 1) + r := by
          rw [mul_add, mul_one]; omega
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hsum, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    rw [Finset.card_eq_one]
    refine ⟨y0, Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun y hy => ?_⟩⟩
    simp only [Finset.mem_filter, Finset.mem_Ico] at hy hmem
    have hdiv : D ∣ (if y0 ≤ y then y - y0 else y0 - y) := by
      split_ifs with hle
      · rw [Nat.dvd_iff_mod_eq_zero]
        have := (Nat.modEq_iff_dvd' hle).mp (show y0 ≡ y [MOD D] from by rw [Nat.ModEq, hmem.2, hy.2])
        exact Nat.mod_eq_zero_of_dvd this
      · rw [Nat.dvd_iff_mod_eq_zero]
        have := (Nat.modEq_iff_dvd' (by omega : y ≤ y0)).mp
          (show y ≡ y0 [MOD D] from by rw [Nat.ModEq, hy.2, hmem.2])
        exact Nat.mod_eq_zero_of_dvd this
    split_ifs at hdiv with hle
    · by_cases heq : y = y0
      · exact heq
      · have hpos : 0 < y - y0 := by omega
        have := Nat.le_of_dvd hpos hdiv
        omega
    · have hpos : 0 < y0 - y := by omega
      have := Nat.le_of_dvd hpos hdiv
      omega
  have hfull : ∀ m A : ℕ, ((Finset.Ico A (A + m * D)).filter (fun y => y % D = r)).card = m := by
    intro m
    induction m with
    | zero => intro A; simp
    | succ k ih =>
      intro A
      have hsplit : Finset.Ico A (A + (k + 1) * D) =
          Finset.Ico A (A + k * D) ∪ Finset.Ico (A + k * D) (A + k * D + D) := by
        ext y; simp only [Finset.mem_Ico, Finset.mem_union]
        have : (k + 1) * D = k * D + D := by ring
        omega
      have hdisj : Disjoint (Finset.Ico A (A + k * D)) (Finset.Ico (A + k * D) (A + k * D + D)) := by
        rw [Finset.disjoint_left]; intro y h1 h2
        simp only [Finset.mem_Ico] at h1 h2; omega
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
        ih A, hblock (A + k * D)]
  have hsplit_all : Finset.Ico Y0 (Y0 + L) =
      Finset.Ico Y0 (Y0 + q * D) ∪ Finset.Ico (Y0 + q * D) (Y0 + q * D + rem) := by
    ext y; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  have hdisj_all : Disjoint (Finset.Ico Y0 (Y0 + q * D))
      (Finset.Ico (Y0 + q * D) (Y0 + q * D + rem)) := by
    rw [Finset.disjoint_left]; intro y h1 h2
    simp only [Finset.mem_Ico] at h1 h2; omega
  have htail : ((Finset.Ico (Y0 + q * D) (Y0 + q * D + rem)).filter (fun y => y % D = r)).card ≤ 1 := by
    calc ((Finset.Ico (Y0 + q * D) (Y0 + q * D + rem)).filter (fun y => y % D = r)).card
        ≤ ((Finset.Ico (Y0 + q * D) (Y0 + q * D + D)).filter (fun y => y % D = r)).card := by
          refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
          intro y hy; simp only [Finset.mem_Ico] at hy ⊢; omega
      _ = 1 := hblock (Y0 + q * D)
  rw [hsplit_all, Finset.filter_union,
    Finset.card_union_of_disjoint (hdisj_all.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
    hfull q Y0]
  have hLD : (L : ℝ) / (D : ℝ) = (q : ℝ) + (rem : ℝ) / (D : ℝ) := by
    have hLR : (L : ℝ) = (q : ℝ) * (D : ℝ) + (rem : ℝ) := by exact_mod_cast hL
    rw [hLR]; field_simp
  have hrem0 : (0 : ℝ) ≤ (rem : ℝ) / (D : ℝ) := by positivity
  have hrem1 : (rem : ℝ) / (D : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hrem.le
  have ht0 : (0 : ℝ) ≤ (((Finset.Ico (Y0 + q * D) (Y0 + q * D + rem)).filter (fun y => y % D = r)).card : ℝ) :=
    Nat.cast_nonneg _
  have ht1 : (((Finset.Ico (Y0 + q * D) (Y0 + q * D + rem)).filter (fun y => y % D = r)).card : ℝ) ≤ 1 := by
    exact_mod_cast htail
  rw [Nat.cast_add, hLD, abs_le]
  constructor <;> linarith

private lemma crt_bad_residues_card (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (bad : ℕ → Finset ℕ) (hbad : ∀ p ∈ S, bad p ⊆ Finset.range p) :
    ((Finset.range (∏ p ∈ S, p)).filter (fun r => ∀ p ∈ S, r % p ∈ bad p)).card =
      ∏ p ∈ S, (bad p).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hps : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hbad_p : bad p ⊆ Finset.range p := hbad p (Finset.mem_insert_self p s)
    have hbad_s : ∀ q ∈ s, bad q ⊆ Finset.range q := fun q hq => hbad q (Finset.mem_insert_of_mem hq)
    set M := ∏ q ∈ s, q
    have hM_pos : 0 < M := Finset.prod_pos fun q hq => (hs q hq).pos
    have hcop : Nat.Coprime p M := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact (Nat.coprime_primes hps (hs q hq)).mpr (fun h => hp (h ▸ hq))
    rw [Finset.prod_insert hp, Finset.prod_insert hp]
    set A := (Finset.range (p * M)).filter (fun r => ∀ q ∈ insert p s, r % q ∈ bad q)
    set B := (bad p) ×ˢ ((Finset.range M).filter (fun r => ∀ q ∈ s, r % q ∈ bad q))
    have hcard_eq : A.card = B.card := by
      refine Finset.card_bij (fun r _ => (r % p, r % M)) ?_ ?_ ?_
      · intro r hr
        simp only [A, B, Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hr ⊢
        refine ⟨hr.2 p (Finset.mem_insert_self p s), Nat.mod_lt r hM_pos, fun q hq => ?_⟩
        have hqM : q ∣ M := Finset.dvd_prod_of_mem id hq
        rw [Nat.mod_mod_of_dvd r hqM]
        exact hr.2 q (Finset.mem_insert_of_mem hq)
      · intro r1 hr1 r2 hr2 heq
        simp only [A, Finset.mem_filter, Finset.mem_range] at hr1 hr2
        simp only [Prod.mk.injEq] at heq
        have hm1 : r1 ≡ r2 [MOD p] := heq.1
        have hm2 : r1 ≡ r2 [MOD M] := heq.2
        have hmul : r1 ≡ r2 [MOD p * M] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hm1, hm2⟩
        rw [Nat.ModEq, Nat.mod_eq_of_lt hr1.1, Nat.mod_eq_of_lt hr2.1] at hmul
        exact hmul
      · rintro ⟨a, b⟩ hab
        simp only [B, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hab
        have ha_lt : a < p := Finset.mem_range.mp (hbad_p hab.1)
        let r := Nat.chineseRemainder hcop a b
        have hr_lt : r.val < p * M := Nat.chineseRemainder_lt_mul hcop a b hps.ne_zero hM_pos.ne'
        have hrmp : r.val % p = a := by
          have := r.property.1
          rw [Nat.ModEq, Nat.mod_eq_of_lt ha_lt] at this; exact this
        have hrmM : r.val % M = b := by
          have := r.property.2
          rw [Nat.ModEq, Nat.mod_eq_of_lt hab.2.1] at this; exact this
        refine ⟨r.val, ?_, Prod.ext hrmp hrmM⟩
        simp only [A, Finset.mem_filter, Finset.mem_range]
        refine ⟨hr_lt, fun q hq => ?_⟩
        rcases Finset.mem_insert.mp hq with rfl | hqs
        · rw [hrmp]; exact hab.1
        · have hqM : q ∣ M := Finset.dvd_prod_of_mem id hqs
          rw [← Nat.mod_mod_of_dvd r.val hqM, hrmM]
          exact hab.2.2 q hqs
    rw [hcard_eq, Finset.card_product, ih hs hbad_s]

private lemma crt_count_bad_subset (Y0 L' : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (bad : ℕ → Finset ℕ) (hbad : ∀ p ∈ S, bad p ⊆ Finset.range p) :
    |(((Finset.Ico Y0 (Y0 + L')).filter (fun y => ∀ p ∈ S, y % p ∈ bad p)).card : ℝ) -
        (L' : ℝ) * ∏ p ∈ S, ((bad p).card : ℝ) / (p : ℝ)| ≤
      ∏ p ∈ S, ((bad p).card : ℝ) := by
  set D := ∏ p ∈ S, p
  have hD_pos : 0 < D := Finset.prod_pos fun p hp => (hS p hp).pos
  set R := (Finset.range D).filter (fun r => ∀ p ∈ S, r % p ∈ bad p)
  have hR_card : R.card = ∏ p ∈ S, (bad p).card := crt_bad_residues_card S hS bad hbad
  have hpart :
      ((Finset.Ico Y0 (Y0 + L')).filter (fun y => ∀ p ∈ S, y % p ∈ bad p)).card =
      ∑ r ∈ R, ((Finset.Ico Y0 (Y0 + L')).filter (fun y => y % D = r)).card := by
    have hbi : (Finset.Ico Y0 (Y0 + L')).filter (fun y => ∀ p ∈ S, y % p ∈ bad p) =
        R.biUnion (fun r => (Finset.Ico Y0 (Y0 + L')).filter (fun y => y % D = r)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_biUnion, R, Finset.mem_range]
      constructor
      · rintro ⟨hy, hall⟩
        refine ⟨y % D, ⟨Nat.mod_lt y hD_pos, fun p hp => ?_⟩, hy, rfl⟩
        have hpD : p ∣ D := Finset.dvd_prod_of_mem (fun x => x) hp
        rw [Nat.mod_mod_of_dvd y hpD]
        exact hall p hp
      · rintro ⟨r, ⟨_, hrall⟩, hy, hyr⟩
        refine ⟨hy, fun p hp => ?_⟩
        have hpD : p ∣ D := Finset.dvd_prod_of_mem (fun x => x) hp
        rw [← Nat.mod_mod_of_dvd y hpD, hyr]
        exact hrall p hp
    rw [hbi, Finset.card_biUnion]
    intro r1 _ r2 _ hne
    show Disjoint ((Finset.Ico Y0 (Y0 + L')).filter (fun y => y % D = r1))
      ((Finset.Ico Y0 (Y0 + L')).filter (fun y => y % D = r2))
    rw [Finset.disjoint_left]
    intro y h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hmain : (L' : ℝ) * ∏ p ∈ S, ((bad p).card : ℝ) / (p : ℝ) =
      ∑ _r ∈ R, (L' : ℝ) / (D : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, hR_card, Finset.prod_div_distrib]
    have h1 : ((∏ p ∈ S, (bad p).card : ℕ) : ℝ) = ∏ p ∈ S, ((bad p).card : ℝ) := by push_cast; rfl
    have h2 : (D : ℝ) = ∏ p ∈ S, (p : ℝ) := by dsimp only [D]; push_cast; rfl
    rw [h1, h2]; ring
  rw [hpart, Nat.cast_sum, hmain, ← Finset.sum_sub_distrib]
  calc |∑ r ∈ R, ((((Finset.Ico Y0 (Y0 + L')).filter (fun y => y % D = r)).card : ℝ) -
          (L' : ℝ) / (D : ℝ))|
      ≤ ∑ r ∈ R, |(((Finset.Ico Y0 (Y0 + L')).filter (fun y => y % D = r)).card : ℝ) -
          (L' : ℝ) / (D : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ R, (1 : ℝ) := Finset.sum_le_sum fun r hr =>
        count_mod_Ico_approx Y0 L' D r hD_pos (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
    _ = (R.card : ℝ) := by simp
    _ = ∏ p ∈ S, ((bad p).card : ℝ) := by rw [hR_card]; push_cast; rfl

private lemma bad_residues_linear (p : ℕ) (hp : p.Prime) (x0 Q0 : ℕ) (a b : ℤ)
    (hQ : ¬ p ∣ Q0) (ha : ¬ ((p : ℤ) ∣ a)) :
    ∃ B : Finset ℕ, B ⊆ Finset.range p ∧ 1 ≤ B.card ∧ B.card ≤ 2 ∧
      ∀ y : ℕ, (y % p ∈ B ↔
        ((p : ℤ) ∣ ((x0 + Q0 * y : ℕ) : ℤ) ∨ (p : ℤ) ∣ a * ((x0 + Q0 * y : ℕ) : ℤ) + b)) := by
  have : Fact p.Prime := ⟨hp⟩
  let B := (Finset.range p).filter (fun r =>
    ((p : ℤ) ∣ ((x0 + Q0 * r : ℕ) : ℤ) ∨ (p : ℤ) ∣ a * ((x0 + Q0 * r : ℕ) : ℤ) + b))
  have hQ0 : (Q0 : ZMod p) ≠ 0 := by
    intro h; exact hQ ((ZMod.natCast_eq_zero_iff Q0 p).mp h)
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h; exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  let r1 : ZMod p := -(x0 : ZMod p) * (Q0 : ZMod p)⁻¹
  let r2 : ZMod p := -((a : ZMod p) * (x0 : ZMod p) + (b : ZMod p)) * ((a : ZMod p) * (Q0 : ZMod p))⁻¹
  have hiff : ∀ y : ℕ,
      (((p : ℤ) ∣ ((x0 + Q0 * y : ℕ) : ℤ) ∨ (p : ℤ) ∣ a * ((x0 + Q0 * y : ℕ) : ℤ) + b) ↔
        ((y : ZMod p) = r1 ∨ (y : ZMod p) = r2)) := by
    intro y
    constructor
    · rintro (h1 | h2)
      · left
        have hz : ((x0 + Q0 * y : ℕ) : ZMod p) = 0 := by
          have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((x0 + Q0 * y : ℕ) : ℤ) p).mpr h1
          simpa using this
        push_cast at hz
        have hmul : (Q0 : ZMod p) * (y : ZMod p) = -(x0 : ZMod p) := eq_neg_of_add_eq_zero_right hz
        calc (y : ZMod p) = (Q0 : ZMod p) * (y : ZMod p) * (Q0 : ZMod p)⁻¹ := by
              rw [mul_comm (Q0 : ZMod p), mul_assoc, mul_inv_cancel₀ hQ0, mul_one]
          _ = r1 := by rw [hmul]
      · right
        have hz : ((a * ((x0 + Q0 * y : ℕ) : ℤ) + b : ℤ) : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h2
        push_cast at hz
        have haQ0 : (a : ZMod p) * (Q0 : ZMod p) ≠ 0 := mul_ne_zero ha0 hQ0
        have hmul : ((a : ZMod p) * (Q0 : ZMod p)) * (y : ZMod p) =
            -((a : ZMod p) * (x0 : ZMod p) + (b : ZMod p)) := by
          apply eq_neg_of_add_eq_zero_right
          linear_combination hz
        calc (y : ZMod p) = ((a : ZMod p) * (Q0 : ZMod p)) * (y : ZMod p) *
              ((a : ZMod p) * (Q0 : ZMod p))⁻¹ := by
              rw [mul_comm ((a : ZMod p) * (Q0 : ZMod p)), mul_assoc, mul_inv_cancel₀ haQ0, mul_one]
          _ = r2 := by rw [hmul]
    · rintro (h1 | h2)
      · left
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [h1]
        dsimp only [r1]
        have : (Q0 : ZMod p) * (-(x0 : ZMod p) * (Q0 : ZMod p)⁻¹) = -(x0 : ZMod p) := by
          rw [mul_comm (Q0 : ZMod p), mul_assoc, inv_mul_cancel₀ hQ0, mul_one]
        rw [this, add_neg_cancel]
      · right
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_add, Nat.cast_mul, h2, r2]
        have haQ0 : (a : ZMod p) * (Q0 : ZMod p) ≠ 0 := mul_ne_zero ha0 hQ0
        have : (a : ZMod p) * ((Q0 : ZMod p) * (-((a : ZMod p) * (x0 : ZMod p) + (b : ZMod p)) *
            ((a : ZMod p) * (Q0 : ZMod p))⁻¹)) = -((a : ZMod p) * (x0 : ZMod p) + (b : ZMod p)) := by
          calc (a : ZMod p) * ((Q0 : ZMod p) * (-((a : ZMod p) * (x0 : ZMod p) + (b : ZMod p)) *
                ((a : ZMod p) * (Q0 : ZMod p))⁻¹))
              = (-((a : ZMod p) * (x0 : ZMod p) + (b : ZMod p))) *
                (((a : ZMod p) * (Q0 : ZMod p)) * ((a : ZMod p) * (Q0 : ZMod p))⁻¹) := by ring
            _ = -((a : ZMod p) * (x0 : ZMod p) + (b : ZMod p)) := by
                rw [mul_inv_cancel₀ haQ0, mul_one]
        linear_combination this
  have hBeq : B = {r1.val, r2.val} := by
    ext r
    simp only [B, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    rw [hiff r]
    constructor
    · rintro ⟨hr, h1 | h2⟩
      · left; have := congrArg ZMod.val h1; rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hr] at this
      · right; have := congrArg ZMod.val h2; rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hr] at this
    · rintro (rfl | rfl)
      · exact ⟨r1.val_lt, Or.inl (ZMod.natCast_zmod_val r1)⟩
      · exact ⟨r2.val_lt, Or.inr (ZMod.natCast_zmod_val r2)⟩
  refine ⟨B, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · rw [hBeq]
    exact Finset.card_pos.mpr ⟨r1.val, Finset.mem_insert_self _ _⟩
  · rw [hBeq]
    exact Finset.card_le_two
  · intro y
    have hy_mod : ((y % p : ℕ) : ZMod p) = (y : ZMod p) := by simp
    simp only [B, Finset.mem_filter, Finset.mem_range]
    rw [hiff (y % p), hiff y, hy_mod]
    exact and_iff_right (Nat.mod_lt y hp.pos)

private lemma sum_weighted_powerset_le (B : Finset ℕ) (m M : ℕ) (hM : 2 ≤ M)
    (hB : B.card ≤ 2 ^ (M - 1)) :
    ∑ S ∈ B.powerset.filter (fun S => S.card ≤ m), (2 : ℝ) ^ S.card ≤
      2 * ((2 : ℝ) ^ M) ^ m := by
  have h1 :
      ∑ S ∈ B.powerset.filter (fun S => S.card ≤ m), (2 : ℝ) ^ S.card =
      ∑ j ∈ Finset.range (m + 1), (B.card.choose j : ℝ) * (2 : ℝ) ^ j := by
    have hpart :
        ∑ S ∈ B.powerset.filter (fun S => S.card ≤ m), (2 : ℝ) ^ S.card =
        ∑ j ∈ Finset.range (m + 1), ∑ S ∈ B.powersetCard j, (2 : ℝ) ^ S.card := by
      rw [← Finset.sum_biUnion]
      · congr 1; ext S
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
          Finset.mem_range, Finset.mem_powersetCard]
        constructor
        · rintro ⟨hSB, hc⟩; exact ⟨S.card, by omega, hSB, rfl⟩
        · rintro ⟨j, hj, hSB, hc⟩; exact ⟨hSB, by omega⟩
      · intro i _ j _ hij
        show Disjoint (B.powersetCard i) (B.powersetCard j)
        rw [Finset.disjoint_left]; intro S hi hj
        exact hij ((Finset.mem_powersetCard.mp hi).2.symm.trans (Finset.mem_powersetCard.mp hj).2)
    rw [hpart]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc : ∑ S ∈ B.powersetCard j, (2 : ℝ) ^ S.card = ∑ _S ∈ B.powersetCard j, (2 : ℝ) ^ j :=
      Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2]
    rw [hc, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  rw [h1]
  have h2B : (2 : ℝ) * (B.card : ℝ) ≤ (2 : ℝ) ^ M := by
    have hpow : 2 * 2 ^ (M - 1) = 2 ^ M := by
      cases M with
      | zero => omega
      | succ k => simp [pow_succ']
    have hnat : 2 * B.card ≤ 2 ^ M := by omega
    exact_mod_cast hnat
  have hterm : ∀ j, (B.card.choose j : ℝ) * (2 : ℝ) ^ j ≤ ((2 : ℝ) ^ M) ^ j := by
    intro j
    have hch : (B.card.choose j : ℝ) ≤ (B.card : ℝ) ^ j := by
      have h1 : (B.card.choose j : ℝ) ≤ (B.card : ℝ) ^ j / (j.factorial : ℝ) :=
        Nat.choose_le_pow_div j B.card
      have h2 : (1 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
      exact h1.trans (div_le_self (by positivity) h2)
    calc (B.card.choose j : ℝ) * (2 : ℝ) ^ j
        ≤ (B.card : ℝ) ^ j * (2 : ℝ) ^ j := by gcongr
      _ = ((2 : ℝ) * (B.card : ℝ)) ^ j := by rw [← mul_pow, mul_comm]
      _ ≤ ((2 : ℝ) ^ M) ^ j := by gcongr
  have hgeom : ∑ j ∈ Finset.range (m + 1), ((2 : ℝ) ^ M) ^ j ≤ 2 * ((2 : ℝ) ^ M) ^ m := by
    set R : ℝ := (2 : ℝ) ^ M
    have hR2 : 2 ≤ R := by
      dsimp only [R]
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) (by omega)
    have hgs := geom_sum_mul R (m + 1)
    have hR1 : 1 ≤ R - 1 := by linarith
    have hle : (∑ j ∈ Finset.range (m + 1), R ^ j) * 1 ≤
        (∑ j ∈ Finset.range (m + 1), R ^ j) * (R - 1) :=
      mul_le_mul_of_nonneg_left hR1 (Finset.sum_nonneg fun _ _ => by positivity)
    rw [mul_one, hgs] at hle
    have hRm : R ^ (m + 1) ≤ R * R ^ m := by rw [pow_succ']
    -- Actually R - 1 ≥ R / 2 since R ≥ 2
    have hhalf : R / 2 ≤ R - 1 := by linarith
    have hle2 : (∑ j ∈ Finset.range (m + 1), R ^ j) * (R / 2) ≤ R ^ (m + 1) - 1 := by
      calc (∑ j ∈ Finset.range (m + 1), R ^ j) * (R / 2)
          ≤ (∑ j ∈ Finset.range (m + 1), R ^ j) * (R - 1) :=
            mul_le_mul_of_nonneg_left hhalf (Finset.sum_nonneg fun _ _ => by positivity)
        _ = R ^ (m + 1) - 1 := hgs
    have hRpos : 0 < R := by linarith
    have : (∑ j ∈ Finset.range (m + 1), R ^ j) * R ≤ 2 * R ^ (m + 1) := by linarith
    rw [pow_succ] at this
    exact le_of_mul_le_mul_right (by linarith) hRpos
  exact (Finset.sum_le_sum fun j _ => hterm j).trans hgeom

private lemma sum_linear_geom_le (K : ℕ) :
    ∑ k ∈ Finset.range K, (2 * (5 + k) : ℝ) / (2 : ℝ) ^ k ≤ 24 := by
  have h1 : ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1), (k : ℝ) / (2 : ℝ) ^ k =
      2 - ((N : ℝ) + 2) / (2 : ℝ) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      field_simp
      ring
  have h2 : ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (2 : ℝ) ^ k =
      2 - 1 / (2 : ℝ) ^ N := by
    intro N
    induction N with
    | zero => simp; norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      field_simp
      ring
  cases K with
  | zero => simp
  | succ N =>
    have hsplit : ∑ k ∈ Finset.range (N + 1), (2 * (5 + k) : ℝ) / (2 : ℝ) ^ k =
        10 * (∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (2 : ℝ) ^ k) +
        2 * (∑ k ∈ Finset.range (N + 1), (k : ℝ) / (2 : ℝ) ^ k) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit, h1 N, h2 N]
    have ha : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ N := by positivity
    have hb : (0 : ℝ) ≤ ((N : ℝ) + 2) / (2 : ℝ) ^ N := by positivity
    linarith

private lemma tail_ratio_sum_le_half (K : ℕ) :
    ∑ k ∈ Finset.range K, Real.exp 4 * ((2 : ℝ) ^ (2 * (5 + k)) / ((2 * (5 + k)).factorial : ℝ)) ≤
      1 / 2 := by
  have hterm : ∀ k : ℕ,
      (2 : ℝ) ^ (2 * (5 + k)) / ((2 * (5 + k)).factorial : ℝ) ≤
      (1 / 2 : ℝ) ^ k * ((2 : ℝ) ^ 10 / ((10 : ℕ).factorial : ℝ)) := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
      have hpow : (2 : ℝ) ^ (2 * (5 + (j + 1))) = 4 * (2 : ℝ) ^ (2 * (5 + j)) := by
        have : 2 * (5 + (j + 1)) = 2 * (5 + j) + 2 := by omega
        rw [this, pow_add]; norm_num; ring
      have hfac : ((2 * (5 + (j + 1))).factorial : ℝ) =
          ((2 * (5 + j) + 2 : ℕ) : ℝ) * ((2 * (5 + j) + 1 : ℕ) : ℝ) *
            ((2 * (5 + j)).factorial : ℝ) := by
        have : 2 * (5 + (j + 1)) = (2 * (5 + j) + 1) + 1 := by omega
        rw [this, Nat.factorial_succ, Nat.factorial_succ]
        push_cast; ring
      have hden : (8 : ℝ) ≤ ((2 * (5 + j) + 2 : ℕ) : ℝ) * ((2 * (5 + j) + 1 : ℕ) : ℝ) := by
        have : 8 ≤ (2 * (5 + j) + 2) * (2 * (5 + j) + 1) := by nlinarith
        exact_mod_cast this
      rw [hpow, hfac]
      have hratio : 4 / (((2 * (5 + j) + 2 : ℕ) : ℝ) * ((2 * (5 + j) + 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      calc 4 * (2 : ℝ) ^ (2 * (5 + j)) /
            ((((2 * (5 + j) + 2 : ℕ) : ℝ) * ((2 * (5 + j) + 1 : ℕ) : ℝ)) *
              ((2 * (5 + j)).factorial : ℝ))
          = (4 / (((2 * (5 + j) + 2 : ℕ) : ℝ) * ((2 * (5 + j) + 1 : ℕ) : ℝ))) *
            ((2 : ℝ) ^ (2 * (5 + j)) / ((2 * (5 + j)).factorial : ℝ)) := by ring
        _ ≤ (1 / 2) * ((1 / 2 : ℝ) ^ j * ((2 : ℝ) ^ 10 / ((10 : ℕ).factorial : ℝ))) := by
            gcongr
        _ = (1 / 2 : ℝ) ^ (j + 1) * ((2 : ℝ) ^ 10 / ((10 : ℕ).factorial : ℝ)) := by
            rw [pow_succ']; ring
  have hexp4 : Real.exp 4 ≤ 81 := by
    have h1 : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
    calc Real.exp 4 = (Real.exp 1) ^ (4 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3 ^ (4 : ℕ) := by gcongr
      _ = 81 := by norm_num
  have hgeom : ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k ≤ 2 := by
    have h2 : ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ k = 2 - (1 / 2 : ℝ) ^ N := by
      intro N
      induction N with
      | zero => simp; norm_num
      | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
    cases K with
    | zero => simp
    | succ N =>
      rw [h2 N]
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N := by positivity
      linarith
  calc ∑ k ∈ Finset.range K, Real.exp 4 * ((2 : ℝ) ^ (2 * (5 + k)) / ((2 * (5 + k)).factorial : ℝ))
      ≤ ∑ k ∈ Finset.range K, 81 * ((1 / 2 : ℝ) ^ k * ((2 : ℝ) ^ 10 / ((10 : ℕ).factorial : ℝ))) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul hexp4 (hterm k) (by positivity) (by norm_num)
    _ = 81 * ((2 : ℝ) ^ 10 / ((10 : ℕ).factorial : ℝ)) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 81 * ((2 : ℝ) ^ 10 / ((10 : ℕ).factorial : ℝ)) * 2 := by gcongr
    _ ≤ 1 / 2 := by norm_num [Nat.factorial]

private lemma prod_one_sub_two_div_ge (N : ℕ) (hN : 3 ≤ N) :
    (2 : ℝ) / ((N : ℝ) ^ 2) ≤ ∏ m ∈ Finset.Icc 3 N, (1 - (2 : ℝ) / (m : ℝ)) := by
  have htel : ∀ n : ℕ, 3 ≤ n →
      ∏ m ∈ Finset.Icc 3 n, (1 - (2 : ℝ) / (m : ℝ)) = 2 / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
    intro n hn
    induction n with
    | zero => omega
    | succ k ih =>
      by_cases hk : k = 2
      · subst hk; simp; norm_num
      · have hk3 : 3 ≤ k := by omega
        have hIcc : Finset.Icc 3 (k + 1) = insert (k + 1) (Finset.Icc 3 k) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot : k + 1 ∉ Finset.Icc 3 k := by simp
        rw [hIcc, Finset.prod_insert hnot, ih hk3]
        have hk0 : (k : ℝ) ≠ 0 := by positivity
        have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hkm1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (by omega : k - 1 ≠ 0)
        have hsub : ((k + 1 - 1 : ℕ) : ℝ) = (k : ℝ) := by simp
        have hsub2 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; norm_num
        rw [hsub, hsub2]
        have hkm1' : (k : ℝ) - 1 ≠ 0 := by linarith [show (3 : ℝ) ≤ k by exact_mod_cast hk3]
        push_cast
        field_simp [hk0, hk1, hkm1']
        ring
  rw [htel N hN]
  have h1 : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
  have hpos : 0 < (N : ℝ) * ((N - 1 : ℕ) : ℝ) := by
    have : 0 < N - 1 := by omega
    positivity
  rw [div_le_div_iff₀ (by positivity) hpos]
  nlinarith

private lemma odd_primes_card_le (M : ℕ) (hM : 1 ≤ M) :
    ((Finset.Ioc 2 (2 ^ M)).filter Nat.Prime).card ≤ 2 ^ (M - 1) := by
  have hsub : (Finset.Ioc 2 (2 ^ M)).filter Nat.Prime ⊆
      (Finset.range (2 ^ (M - 1))).image (fun k => 2 * k + 1) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hodd : p % 2 = 1 := by
      rcases hp.2.eq_two_or_odd with rfl | ho
      · omega
      · exact ho
    rw [Finset.mem_image]
    refine ⟨p / 2, Finset.mem_range.mpr ?_, by omega⟩
    have hpow : 2 * 2 ^ (M - 1) = 2 ^ M := by
      cases M with
      | zero => omega
      | succ k => simp [pow_succ']
    omega
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

private lemma sieve_29_aux (Mbase : ℕ) (hMbase : 200 ≤ Mbase) :
    ∃ C : ℝ, 3 ≤ C ∧ ∀ (z : ℝ) (X L : ℕ) (a b : ℤ),
      C ≤ z → C * z ^ (29 : ℕ) ≤ (L : ℝ) →
      (∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z → ¬ ((p : ℤ) ∣ a)) →
      ∃ x ∈ Finset.Ico X (X + L),
        ¬ 2 ∣ x ∧
        ∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z →
          ¬ ((p : ℤ) ∣ (x : ℤ)) ∧ ¬ ((p : ℤ) ∣ a * (x : ℤ) + b) := by
  have h4_le_base : 4 ≤ 2 ^ Mbase := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Mbase := Nat.pow_le_pow_right (by omega) (by omega)
  have hbase_le_succ : 2 ^ Mbase ≤ 2 ^ (Mbase + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  -- Pre-sieve all primes ≤ 2^Mbase into one congruence class mod Q0
  let P0 : Finset ℕ := (Finset.range (2 ^ Mbase + 1)).filter Nat.Prime
  let Q0 : ℕ := ∏ p ∈ P0, p
  have hP0_prime : ∀ p ∈ P0, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hQ0_pos : 0 < Q0 := Finset.prod_pos fun p hp => (hP0_prime p hp).pos
  have hQ0_posR : (0 : ℝ) < (Q0 : ℝ) := by exact_mod_cast hQ0_pos
  have h2_mem_P0 : 2 ∈ P0 := by
    simp only [P0, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two⟩
  -- Choose C large enough: C = max (2^(Mbase+1)) (2^30 * Q0)
  let C : ℝ := max ((2 ^ (Mbase + 1) : ℕ) : ℝ) ((2 ^ 30 : ℝ) * (Q0 : ℝ))
  have hC_ge_base1 : ((2 ^ (Mbase + 1) : ℕ) : ℝ) ≤ C := le_max_left _ _
  have hC_ge_Q0 : (2 ^ 30 : ℝ) * (Q0 : ℝ) ≤ C := le_max_right _ _
  have hC3 : 3 ≤ C := by
    have : (3 : ℝ) ≤ ((2 ^ (Mbase + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ 2 ^ (Mbase + 1))
    linarith
  refine ⟨C, hC3, ?_⟩
  intro z X L a b hzC hLC ha_nodvd
  have hz_pos : 0 < z := by linarith
  have hzbase1 : ((2 ^ (Mbase + 1) : ℕ) : ℝ) ≤ z := hC_ge_base1.trans hzC
  have hz_floor_ge : 2 ^ (Mbase + 1) ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hzbase1)
  -- Step 1: Pick x0 < Q0 avoiding 2 | x0 and p | x0, p | (a*x0 + b) for all 3 ≤ p ≤ 2^Mbase
  let bad0 : ℕ → Finset ℕ := fun p =>
    if p = 2 then {0}
    else (Finset.range p).filter (fun r : ℕ => (p : ℤ) ∣ (r : ℤ) ∨ (p : ℤ) ∣ a * (r : ℤ) + b)
  have hbad0_lt : ∀ p ∈ P0, (bad0 p).card < p := by
    intro p hp
    have hpp := hP0_prime p hp
    dsimp only [bad0]
    split_ifs with hp2
    · subst hp2; simp
    · have hp3 : 3 ≤ p := by have := hpp.two_le; omega
      have hpz : (p : ℝ) ≤ z := by
        have hple : p ≤ 2 ^ Mbase := by
          have := (Finset.mem_filter.mp hp).1
          rw [Finset.mem_range] at this; omega
        have h1 : (p : ℝ) ≤ ((2 ^ (Mbase + 1) : ℕ) : ℝ) := by exact_mod_cast hple.trans hbase_le_succ
        linarith
      obtain ⟨B, _, _, hB2, hBiff⟩ := bad_residues_linear p hpp 0 1 a b
        (fun h => hpp.ne_one (Nat.dvd_one.mp h)) (ha_nodvd p hpp hp3 hpz)
      have hsub : (Finset.range p).filter (fun r : ℕ => (p : ℤ) ∣ (r : ℤ) ∨ (p : ℤ) ∣ a * (r : ℤ) + b) ⊆ B := by
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        have hmod : r % p = r := Nat.mod_eq_of_lt hr.1
        rw [← hmod, hBiff r]
        simpa using hr.2
      have hcard : ((Finset.range p).filter (fun r : ℕ => (p : ℤ) ∣ (r : ℤ) ∨ (p : ℤ) ∣ a * (r : ℤ) + b)).card ≤ 2 :=
        (Finset.card_le_card hsub).trans hB2
      omega
  obtain ⟨x0, hx0_lt, hx0_good⟩ := crt_avoid_primes P0 hP0_prime bad0 hbad0_lt
  -- Step 2: Arithmetic progression y ∈ [Y0, Y0 + L') maps to x0 + Q0 * y ∈ [X, X + L)
  let Y0 : ℕ := if X ≤ x0 then 0 else (X - x0 + Q0 - 1) / Q0
  let L' : ℕ := L / Q0 - 1
  have hL_ge_4Q0 : 4 * Q0 ≤ L := by
    have hz1 : (1 : ℝ) ≤ z ^ (29 : ℕ) := one_le_pow₀ (by linarith)
    have h4 : (4 : ℝ) * (Q0 : ℝ) ≤ C * z ^ (29 : ℕ) := by
      have h4C : (4 : ℝ) * (Q0 : ℝ) ≤ C := by
        have : (4 : ℝ) * (Q0 : ℝ) ≤ (2 ^ 30 : ℝ) * (Q0 : ℝ) :=
          mul_le_mul_of_nonneg_right (by norm_num) hQ0_posR.le
        linarith
      nlinarith
    exact_mod_cast h4.trans hLC
  have hL'_ge : (L : ℝ) / (2 * (Q0 : ℝ)) ≤ (L' : ℝ) := by
    have hdiv : L < L / Q0 * Q0 + Q0 := Nat.lt_div_mul_add hQ0_pos
    have hq_ge4 : 4 ≤ L / Q0 := (Nat.le_div_iff_mul_le hQ0_pos).mpr (by linarith)
    have h2 : L ≤ 2 * Q0 * (L / Q0 - 1) := by
      have : L / Q0 + 1 ≤ 2 * (L / Q0 - 1) := by omega
      nlinarith
    have h2R : (L : ℝ) ≤ (2 * (Q0 : ℝ)) * (L' : ℝ) := by
      have : L ≤ 2 * Q0 * L' := h2
      exact_mod_cast (by linarith : L ≤ 2 * Q0 * L')
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hmap_Ico : ∀ y ∈ Finset.Ico Y0 (Y0 + L'), x0 + Q0 * y ∈ Finset.Ico X (X + L) := by
    intro y hy
    simp only [Finset.mem_Ico] at hy ⊢
    have hlow : X ≤ x0 + Q0 * Y0 := by
      dsimp only [Y0]
      split_ifs with hle
      · omega
      · have h2 : X - x0 ≤ Q0 * ((X - x0 + Q0 - 1) / Q0) := by
          have := Nat.div_add_mod (X - x0 + Q0 - 1) Q0
          have := Nat.mod_lt (X - x0 + Q0 - 1) hQ0_pos
          omega
        omega
    have hhi_base : x0 + Q0 * Y0 < X + Q0 := by
      dsimp only [Y0]
      split_ifs with hle
      · omega
      · have h1 : Q0 * ((X - x0 + Q0 - 1) / Q0) ≤ X - x0 + Q0 - 1 :=
          Nat.mul_div_le (X - x0 + Q0 - 1) Q0
        omega
    have h1 : x0 + Q0 * y ≥ X := by nlinarith
    have h2 : Q0 * L' + Q0 ≤ L := by
      have hq : Q0 * (L / Q0) ≤ L := Nat.mul_div_le L Q0
      have hq1 : 1 ≤ L / Q0 := (Nat.le_div_iff_mul_le hQ0_pos).mpr (by omega : 1 * Q0 ≤ L)
      have : Q0 * L' + Q0 = Q0 * (L / Q0) := by
        dsimp only [L']; rw [← mul_add_one, Nat.sub_add_cancel hq1]
      omega
    have h3 : x0 + Q0 * y < X + L := by
      have hL'1 : 1 ≤ L' := by
        have := (Nat.le_div_iff_mul_le hQ0_pos).mpr (by omega : 2 * Q0 ≤ L)
        dsimp only [L']; omega
      have hy_le : y ≤ Y0 + (L' - 1) := by omega
      have : x0 + Q0 * y ≤ x0 + Q0 * Y0 + Q0 * (L' - 1) := by nlinarith
      have : Q0 * (L' - 1) + Q0 = Q0 * L' := by rw [← mul_add_one, Nat.sub_add_cancel hL'1]
      omega
    exact ⟨h1, h3⟩
  -- Step 3: Define geometric-exponent prime buckets B_k for 0 ≤ k < K
  let M0 : ℕ := Nat.log 2 ⌊z⌋₊ + 1
  have hM0_ge : Mbase + 2 ≤ M0 := by
    have : Mbase + 1 ≤ Nat.log 2 ⌊z⌋₊ := Nat.le_log_of_pow_le (by omega) hz_floor_ge
    omega
  have h2M0_gt : ⌊z⌋₊ < 2 ^ M0 := Nat.lt_pow_succ_log_self (by omega) ⌊z⌋₊
  have h2M0_le : ((2 ^ M0 : ℕ) : ℝ) ≤ 2 * z := by
    have h1 : 2 ^ Nat.log 2 ⌊z⌋₊ ≤ ⌊z⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have h2 : 2 ^ M0 ≤ 2 * ⌊z⌋₊ := by dsimp only [M0]; rw [pow_succ']; omega
    have h3 : ((2 ^ M0 : ℕ) : ℝ) ≤ 2 * (⌊z⌋₊ : ℝ) := by exact_mod_cast h2
    linarith [Nat.floor_le hz_pos.le]
  have hM0_le_z : (M0 : ℝ) ≤ z := by
    have hnat : M0 ≤ 2 ^ (M0 - 1) := by
      have : ∀ n : ℕ, 1 ≤ n → n + 1 ≤ 2 ^ n := by
        intro n; induction n with
        | zero => omega
        | succ m ih =>
          intro _; cases m with
          | zero => norm_num
          | succ m' => have := ih (by omega); rw [pow_succ']; omega
      have h := this (M0 - 1) (by omega)
      omega
    have hle : 2 ^ (M0 - 1) ≤ ⌊z⌋₊ := Nat.pow_log_le_self 2 (by omega)
    exact (by exact_mod_cast hnat.trans hle : (M0 : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le hz_pos.le)
  -- Let K be the smallest k with M0 / 2^k ≤ Mbase
  have hexK : ∃ k : ℕ, M0 / 2 ^ k ≤ Mbase := ⟨M0, by
    have h1 : M0 < 2 ^ M0 := Nat.lt_two_pow_self
    rw [Nat.div_eq_of_lt h1]; omega⟩
  let K : ℕ := Nat.find hexK
  have hMK_le : M0 / 2 ^ K ≤ Mbase := Nat.find_spec hexK
  have hK_pos : 1 ≤ K := by
    by_contra h0
    have hK0 : K = 0 := by omega
    rw [hK0, pow_zero, Nat.div_one] at hMK_le
    omega
  have hM_gt : ∀ k < K, Mbase < M0 / 2 ^ k := fun k hk => by
    have := Nat.find_min hexK hk; omega
  have h2K_le : (2 : ℝ) ^ K ≤ 2 * z := by
    have hKm1 : Mbase < M0 / 2 ^ (K - 1) := hM_gt (K - 1) (by omega)
    have hdiv_pos : 1 ≤ M0 / 2 ^ (K - 1) := by omega
    have hpow_le : 2 ^ (K - 1) ≤ M0 := by
      have h1 := (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega : 0 < 2))).mp hdiv_pos
      simpa using h1
    have hpowK : 2 ^ K ≤ 2 * M0 := by
      obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
      have hKeq : 2 ^ K = 2 * 2 ^ (K - 1) := by
        rw [hk', Nat.succ_sub_one, pow_succ']
      rw [hKeq]; exact Nat.mul_le_mul_left 2 hpow_le
    have h1 : ((2 ^ K : ℕ) : ℝ) ≤ 2 * (M0 : ℝ) := by exact_mod_cast hpowK
    have h2 : ((2 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ K := by push_cast; rfl
    linarith
  have hK_le : (K : ℝ) + 1 ≤ 2 * z := by
    have hnat : K + 1 ≤ 2 ^ K := by
      have : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
        intro n; induction n with
        | zero => norm_num
        | succ m ih => rw [pow_succ']; omega
      exact this K
    have h1 : (K : ℝ) + 1 ≤ (2 : ℝ) ^ K := by exact_mod_cast hnat
    linarith
  -- Bucket B k: primes p with max(2^Mbase, 2^(M_{k+1})) < p ≤ min(⌊z⌋₊, 2^(M_k))
  let Mk : ℕ → ℕ := fun k => M0 / 2 ^ k
  let Bk : Fin K → Finset ℕ := fun k =>
    (Finset.Ioc (max (2 ^ Mbase) (2 ^ Mk (k.val + 1))) (min ⌊z⌋₊ (2 ^ Mk k.val))).filter Nat.Prime
  have hBk_prime : ∀ k : Fin K, ∀ p ∈ Bk k, p.Prime := fun k p hp =>
    (Finset.mem_filter.mp hp).2
  have hBk_gt_base : ∀ k : Fin K, ∀ p ∈ Bk k, 2 ^ Mbase < p := fun k p hp => by
    have h := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    exact lt_of_le_of_lt (le_max_left _ _) h
  have hBk_le_z : ∀ k : Fin K, ∀ p ∈ Bk k, (p : ℝ) ≤ z := fun k p hp => by
    have h := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
    have hpfl : p ≤ ⌊z⌋₊ := h.trans (min_le_left _ _)
    exact (by exact_mod_cast hpfl : (p : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le hz_pos.le)
  have hBk_disj : ∀ i j : Fin K, i ≠ j → Disjoint (Bk i) (Bk j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro p hpi hpj
    have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpi).1
    have hj := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpj).1
    have hmono : ∀ a b : ℕ, a ≤ b → Mk b ≤ Mk a := fun a b hab =>
      Nat.div_le_div_left (Nat.pow_le_pow_right (by omega) hab) (Nat.pow_pos (by omega))
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · have h1 : 2 ^ Mk j.val ≤ 2 ^ Mk (i.val + 1) :=
        Nat.pow_le_pow_right (by omega) (hmono (i.val + 1) j.val hlt)
      have h2 : p ≤ 2 ^ Mk j.val := hj.2.trans (min_le_right _ _)
      have h3 : 2 ^ Mk (i.val + 1) < p := lt_of_le_of_lt (le_max_right _ _) hi.1
      omega
    · have h1 : 2 ^ Mk i.val ≤ 2 ^ Mk (j.val + 1) :=
        Nat.pow_le_pow_right (by omega) (hmono (j.val + 1) i.val hgt)
      have h2 : p ≤ 2 ^ Mk i.val := hi.2.trans (min_le_right _ _)
      have h3 : 2 ^ Mk (j.val + 1) < p := lt_of_le_of_lt (le_max_right _ _) hj.1
      omega
  -- Every prime p with 2^Mbase < p ≤ ⌊z⌋₊ lies in some Bk k
  have hcover : ∀ p : ℕ, p.Prime → 2 ^ Mbase < p → p ≤ ⌊z⌋₊ → ∃ k : Fin K, p ∈ Bk k := by
    intro p hp hgt hle
    have hlt0 : p ≤ 2 ^ Mk 0 := by
      have : Mk 0 = M0 := by simp [Mk]
      rw [this]; omega
    have hgtK : 2 ^ Mk K < p := by
      have : 2 ^ Mk K ≤ 2 ^ Mbase := Nat.pow_le_pow_right (by omega) hMK_le
      omega
    have hex : ∃ k : ℕ, 2 ^ Mk k < p := ⟨K, hgtK⟩
    let j := Nat.find hex
    have hj_gt : 2 ^ Mk j < p := Nat.find_spec hex
    have hj_pos : 1 ≤ j := by
      by_contra h0
      have hj0 : j = 0 := by omega
      rw [hj0] at hj_gt; omega
    have hj_leK : j ≤ K := Nat.find_min' hex hgtK
    have hjm1_le : p ≤ 2 ^ Mk (j - 1) := by
      have := Nat.find_min hex (show j - 1 < j by omega); omega
    refine ⟨⟨j - 1, by omega⟩, ?_⟩
    simp only [Bk, Finset.mem_filter, Finset.mem_Ioc]
    have hj_eq : j - 1 + 1 = j := by omega
    rw [hj_eq]
    exact ⟨⟨max_lt hgt hj_gt, le_min hle hjm1_le⟩, hp⟩
  -- Step 4: Bad residue sets and densities for primes p > 2^Mbase, p ≤ ⌊z⌋₊
  have hbad_ex : ∀ p : ℕ, (h : p.Prime ∧ 2 ^ Mbase < p ∧ p ≤ ⌊z⌋₊) →
      ∃ B : Finset ℕ, B ⊆ Finset.range p ∧ 1 ≤ B.card ∧ B.card ≤ 2 ∧
        ∀ y : ℕ, (y % p ∈ B ↔
          ((p : ℤ) ∣ ((x0 + Q0 * y : ℕ) : ℤ) ∨ (p : ℤ) ∣ a * ((x0 + Q0 * y : ℕ) : ℤ) + b)) := by
    intro p ⟨hpp, hgt, hle⟩
    have hp3 : 3 ≤ p := by omega
    have hpz : (p : ℝ) ≤ z := (by exact_mod_cast hle : (p : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le hz_pos.le)
    have hnotQ0 : ¬ p ∣ Q0 := by
      intro hdvd
      obtain ⟨q, hqP0, hpq⟩ := hpp.prime.exists_mem_finset_dvd hdvd
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hpp (hP0_prime q hqP0)).mp hpq
      subst heq
      have := Finset.mem_range.mp (Finset.mem_filter.mp hqP0).1; omega
    exact bad_residues_linear p hpp x0 Q0 a b hnotQ0 (ha_nodvd p hpp hp3 hpz)
  let bad : ℕ → Finset ℕ := fun p =>
    if h : p.Prime ∧ 2 ^ Mbase < p ∧ p ≤ ⌊z⌋₊ then (hbad_ex p h).choose else ∅
  have hbad_sub : ∀ k : Fin K, ∀ p ∈ Bk k, bad p ⊆ Finset.range p := by
    intro k p hp
    have hcond : p.Prime ∧ 2 ^ Mbase < p ∧ p ≤ ⌊z⌋₊ :=
      ⟨hBk_prime k p hp, hBk_gt_base k p hp, (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2.trans (min_le_left _ _)⟩
    simp only [bad, dif_pos hcond]
    exact (hbad_ex p hcond).choose_spec.1
  have hbad_card_le2 : ∀ k : Fin K, ∀ p ∈ Bk k, (bad p).card ≤ 2 := by
    intro k p hp
    have hcond : p.Prime ∧ 2 ^ Mbase < p ∧ p ≤ ⌊z⌋₊ :=
      ⟨hBk_prime k p hp, hBk_gt_base k p hp, (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2.trans (min_le_left _ _)⟩
    simp only [bad, dif_pos hcond]
    exact (hbad_ex p hcond).choose_spec.2.2.1
  have hbad_iff : ∀ k : Fin K, ∀ p ∈ Bk k, ∀ y : ℕ,
      (y % p ∈ bad p ↔
        ((p : ℤ) ∣ ((x0 + Q0 * y : ℕ) : ℤ) ∨ (p : ℤ) ∣ a * ((x0 + Q0 * y : ℕ) : ℤ) + b)) := by
    intro k p hp y
    have hcond : p.Prime ∧ 2 ^ Mbase < p ∧ p ≤ ⌊z⌋₊ :=
      ⟨hBk_prime k p hp, hBk_gt_base k p hp, (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2.trans (min_le_left _ _)⟩
    simp only [bad, dif_pos hcond]
    exact (hbad_ex p hcond).choose_spec.2.2.2 y
  let ν : ℕ → ℝ := fun p => ((bad p).card : ℝ) / (p : ℝ)
  let rk : Fin K → ℕ := fun k => 5 + k.val
  -- Step 5: Per-bucket density bounds
  have hν_bounds : ∀ k : Fin K, ∀ p ∈ Bk k, 0 ≤ ν p ∧ ν p ≤ 1 / 2 := by
    intro k p hp
    have hgt := hBk_gt_base k p hp
    have hc2 := hbad_card_le2 k p hp
    have hp4 : 4 ≤ p := by omega
    refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
    dsimp only [ν]
    rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < p)) (by norm_num)]
    have : (bad p).card * 2 ≤ 1 * p := by omega
    exact_mod_cast this
  have hSk_le2 : ∀ k : Fin K, ∑ p ∈ Bk k, ν p ≤ 2 := by
    intro k
    have hMk_gt : Mbase < Mk k.val := hM_gt k.val k.isLt
    have hMk1_eq : Mk (k.val + 1) = Mk k.val / 2 := by
      dsimp only [Mk]; rw [pow_succ, Nat.div_div_eq_div_mul]
    have hA100 : 100 ≤ Mk (k.val + 1) := by omega
    have hAB : Mk (k.val + 1) ≤ Mk k.val := by omega
    have hB : Mk k.val ≤ 2 * Mk (k.val + 1) + 1 := by omega
    calc ∑ p ∈ Bk k, ν p
        ≤ ∑ p ∈ Bk k, (2 : ℝ) / (p : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          dsimp only [ν]
          exact div_le_div_of_nonneg_right (by exact_mod_cast hbad_card_le2 k p hp) (Nat.cast_nonneg _)
      _ ≤ ∑ p ∈ (Finset.Ioc (2 ^ Mk (k.val + 1)) (2 ^ Mk k.val)).filter Nat.Prime,
            (2 : ℝ) / (p : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
          intro p hp
          simp only [Bk, Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
          exact ⟨⟨lt_of_le_of_lt (le_max_right _ _) hp.1.1, hp.1.2.trans (min_le_right _ _)⟩, hp.2⟩
      _ ≤ 2 := sum_two_div_prime_bucket_le_two hA100 hAB hB
  -- Step 6: Set up multi-bucket sieve over I' = Ico Y0 (Y0 + L')
  let I' : Finset ℕ := Finset.Ico Y0 (Y0 + L')
  let Pev : ℕ → ℕ → Prop := fun y p => y % p ∈ bad p
  let ak : ℕ → Fin K → ℝ := fun y k => if ∀ p ∈ Bk k, ¬ Pev y p then 1 else 0
  let Uk : ℕ → Fin K → ℝ := fun y k =>
    ∑ S ∈ (Bk k).powerset.filter (fun S => S.card ≤ 2 * rk k),
      (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, Pev y p then 1 else 0)
  let Lk : ℕ → Fin K → ℝ := fun y k =>
    ∑ S ∈ (Bk k).powerset.filter (fun S => S.card ≤ 2 * rk k - 1),
      (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, Pev y p then 1 else 0)
  let EU : Fin K → ℝ := fun k =>
    ∑ S ∈ (Bk k).powerset.filter (fun S => S.card ≤ 2 * rk k),
      (-1 : ℝ) ^ S.card * (∏ p ∈ S, ν p)
  let ED : Fin K → ℝ := fun k =>
    ∑ S ∈ (Bk k).powersetCard (2 * rk k), (∏ p ∈ S, ν p)
  -- Expected values vs W_k
  have hEU_ge_W : ∀ k : Fin K, ∏ p ∈ Bk k, (1 - ν p) ≤ EU k := fun k =>
    expect_upper_ge_prod (Bk k) ν (fun p hp => ⟨(hν_bounds k p hp).1, by linarith [(hν_bounds k p hp).2]⟩) (rk k)
  have hW_ge_exp : ∀ k : Fin K, Real.exp (-4) ≤ ∏ p ∈ Bk k, (1 - ν p) := by
    intro k
    calc Real.exp (-4) = Real.exp (-2 * 2) := by norm_num
      _ ≤ Real.exp (-2 * ∑ p ∈ Bk k, ν p) := by
          apply Real.exp_le_exp.mpr; linarith [hSk_le2 k]
      _ = ∏ p ∈ Bk k, Real.exp (-2 * ν p) := by
          rw [Finset.mul_sum, Real.exp_sum]
      _ ≤ ∏ p ∈ Bk k, (1 - ν p) := by
          refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun p hp => ?_
          exact one_sub_ge_exp_neg_two (hν_bounds k p hp).1 (hν_bounds k p hp).2
  have hEU_pos : ∀ k : Fin K, 0 < EU k := fun k =>
    lt_of_lt_of_le (Real.exp_pos (-4)) ((hW_ge_exp k).trans (hEU_ge_W k))
  have hED_le : ∀ k : Fin K, ED k ≤ (2 : ℝ) ^ (2 * rk k) / ((2 * rk k).factorial : ℝ) := by
    intro k
    calc ED k ≤ (∑ p ∈ Bk k, ν p) ^ (2 * rk k) / ((2 * rk k).factorial : ℝ) :=
          sum_powersetCard_prod_le (Bk k) ν (fun p hp => (hν_bounds k p hp).1) (2 * rk k)
      _ ≤ (2 : ℝ) ^ (2 * rk k) / ((2 * rk k).factorial : ℝ) :=
          div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (Finset.sum_nonneg fun p hp => (hν_bounds k p hp).1) (hSk_le2 k) _)
            (Nat.cast_nonneg _)
  -- Step 7: Main term lower bound
  have hratio_sum : ∑ i : Fin K, ED i / EU i ≤ 1 / 2 := by
    calc ∑ i : Fin K, ED i / EU i
        ≤ ∑ i : Fin K, ((2 : ℝ) ^ (2 * rk i) / ((2 * rk i).factorial : ℝ)) / Real.exp (-4) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := hED_le i
          have h2 : Real.exp (-4) ≤ EU i := (hW_ge_exp i).trans (hEU_ge_W i)
          exact div_le_div₀ (div_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _))
            h1 (Real.exp_pos (-4)) h2
      _ = ∑ k ∈ Finset.range K, Real.exp 4 * ((2 : ℝ) ^ (2 * (5 + k)) / ((2 * (5 + k)).factorial : ℝ)) := by
          rw [Fin.sum_univ_eq_sum_range (fun k => ((2 : ℝ) ^ (2 * (5 + k)) / ((2 * (5 + k)).factorial : ℝ)) / Real.exp (-4))]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Real.exp_neg, div_inv_eq_mul, mul_comm]
      _ ≤ 1 / 2 := tail_ratio_sum_le_half K
  have hprod_EU_ge : (2 : ℝ) / (z ^ 2) ≤ ∏ k : Fin K, EU k := by
    have hdisj_all : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint Bk :=
      fun i _ j _ hij => hBk_disj i j hij
    have hunion_sub : (Finset.univ.biUnion Bk) ⊆ Finset.Icc 3 ⌊z⌋₊ := by
      intro p hp
      obtain ⟨k, _, hpk⟩ := Finset.mem_biUnion.mp hp
      have hgt := hBk_gt_base k p hpk
      have hle := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpk).1).2.trans (min_le_left _ _)
      exact Finset.mem_Icc.mpr ⟨by omega, hle⟩
    have hfloor3 : 3 ≤ ⌊z⌋₊ := by omega
    calc (2 : ℝ) / (z ^ 2)
        ≤ (2 : ℝ) / ((⌊z⌋₊ : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num)
            (pow_pos (by exact_mod_cast (by omega : 0 < ⌊z⌋₊)) 2)
            (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hz_pos.le) 2)
      _ ≤ ∏ m ∈ Finset.Icc 3 ⌊z⌋₊, (1 - (2 : ℝ) / (m : ℝ)) :=
          prod_one_sub_two_div_ge ⌊z⌋₊ hfloor3
      _ ≤ ∏ p ∈ Finset.univ.biUnion Bk, (1 - (2 : ℝ) / (p : ℝ)) := by
          have hle1 : ∀ m ∈ Finset.Icc 3 ⌊z⌋₊, 1 - (2 : ℝ) / (m : ℝ) ≤ 1 := fun m _ => by
            have : (0 : ℝ) ≤ 2 / (m : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
            linarith
          have hge0 : ∀ m ∈ Finset.Icc 3 ⌊z⌋₊, 0 ≤ 1 - (2 : ℝ) / (m : ℝ) := fun m hm => by
            have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
            have : (2 : ℝ) / (m : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
            linarith
          have h1 : ∏ m ∈ Finset.Icc 3 ⌊z⌋₊, (1 - (2 : ℝ) / (m : ℝ)) =
              (∏ m ∈ (Finset.Icc 3 ⌊z⌋₊) \ (Finset.univ.biUnion Bk), (1 - (2 : ℝ) / (m : ℝ))) *
              (∏ m ∈ Finset.univ.biUnion Bk, (1 - (2 : ℝ) / (m : ℝ))) :=
            (Finset.prod_sdiff hunion_sub).symm
          rw [h1]
          have hrest : ∏ m ∈ (Finset.Icc 3 ⌊z⌋₊) \ (Finset.univ.biUnion Bk), (1 - (2 : ℝ) / (m : ℝ)) ≤ 1 :=
            Finset.prod_le_one (fun m hm => hge0 m (Finset.mem_sdiff.mp hm).1)
              (fun m hm => hle1 m (Finset.mem_sdiff.mp hm).1)
          have hmain0 : 0 ≤ ∏ m ∈ Finset.univ.biUnion Bk, (1 - (2 : ℝ) / (m : ℝ)) :=
            Finset.prod_nonneg fun m hm => hge0 m (hunion_sub hm)
          nlinarith only [hrest, hmain0]
      _ = ∏ k : Fin K, ∏ p ∈ Bk k, (1 - (2 : ℝ) / (p : ℝ)) :=
          Finset.prod_biUnion hdisj_all
      _ ≤ ∏ k : Fin K, ∏ p ∈ Bk k, (1 - ν p) := by
          refine Finset.prod_le_prod (fun k _ => Finset.prod_nonneg fun p hp => ?_) fun k _ => ?_
          · have hgt := hBk_gt_base k p hp
            have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
            have : (2 : ℝ) / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
            linarith
          · refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
            · have hgt := hBk_gt_base k p hp
              have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
              have : (2 : ℝ) / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
              linarith
            · have hc2 : ((bad p).card : ℝ) ≤ 2 := by exact_mod_cast hbad_card_le2 k p hp
              have : ν p ≤ 2 / (p : ℝ) := div_le_div_of_nonneg_right hc2 (Nat.cast_nonneg _)
              linarith
      _ ≤ ∏ k : Fin K, EU k := by
          refine Finset.prod_le_prod (fun k _ => (Real.exp_pos (-4)).le.trans (hW_ge_exp k))
            (fun k _ => hEU_ge_W k)
  have hmain_comb :
      (L' : ℝ) * ((∏ k : Fin K, EU k) - ∑ i : Fin K, ED i * (∏ k ∈ Finset.univ.erase i, EU k)) ≥
      (L' : ℝ) / (z ^ 2) := by
    have hfactor : (∏ k : Fin K, EU k) - ∑ i : Fin K, ED i * (∏ k ∈ Finset.univ.erase i, EU k) =
        (∏ k : Fin K, EU k) * (1 - ∑ i : Fin K, ED i / EU i) := by
      rw [mul_sub, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hpeq : ∏ k : Fin K, EU k = EU i * ∏ k ∈ Finset.univ.erase i, EU k :=
        (Finset.mul_prod_erase Finset.univ EU (Finset.mem_univ i)).symm
      have hi0 : EU i ≠ 0 := (hEU_pos i).ne'
      rw [hpeq]; field_simp
    rw [hfactor]
    have h1 : 1 / 2 ≤ 1 - ∑ i : Fin K, ED i / EU i := by linarith [hratio_sum]
    have h2 : (1 : ℝ) / (z ^ 2) ≤ (∏ k : Fin K, EU k) * (1 - ∑ i : Fin K, ED i / EU i) := by
      calc (1 : ℝ) / (z ^ 2) = ((2 : ℝ) / (z ^ 2)) * (1 / 2) := by ring
        _ ≤ (∏ k : Fin K, EU k) * (1 - ∑ i : Fin K, ED i / EU i) :=
          mul_le_mul hprod_EU_ge h1 (by norm_num) (Finset.prod_nonneg fun k _ => (hEU_pos k).le)
    calc (L' : ℝ) / (z ^ 2) = (L' : ℝ) * ((1 : ℝ) / (z ^ 2)) := by ring
      _ ≤ (L' : ℝ) * ((∏ k : Fin K, EU k) * (1 - ∑ i : Fin K, ED i / EU i)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
  -- Step 8: Expand products over tuples of subsets and bound CRT errors
  let FamU : Fin K → Finset (Finset ℕ) := fun k => (Bk k).powerset.filter (fun S => S.card ≤ 2 * rk k)
  let FamD : Fin K → Finset (Finset ℕ) := fun k => (Bk k).powersetCard (2 * rk k)
  have hFamD_sub : ∀ k : Fin K, FamD k ⊆ FamU k := by
    intro k S hS
    simp only [FamD, FamU, Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact ⟨hS.1, hS.2.le⟩
  have htuple_err : ∀ (F : Fin K → Finset (Finset ℕ)),
      (∀ k, F k ⊆ FamU k) →
      |((∑ y ∈ I', ∏ k : Fin K, ∑ S ∈ F k, (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, Pev y p then 1 else 0)) -
        (L' : ℝ) * ∏ k : Fin K, ∑ S ∈ F k, (-1 : ℝ) ^ S.card * (∏ p ∈ S, ν p))| ≤
      ∏ k : Fin K, ∑ S ∈ FamU k, (2 : ℝ) ^ S.card := by
    intro F hF
    let Dom := Fintype.piFinset F
    have hexp_y : ∀ y ∈ I',
        (∏ k : Fin K, ∑ S ∈ F k, (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, Pev y p then 1 else 0)) =
        ∑ f ∈ Dom, (∏ k : Fin K, (-1 : ℝ) ^ (f k).card) *
          (if ∀ p ∈ Finset.univ.biUnion f, Pev y p then (1 : ℝ) else 0) := by
      intro y _
      rw [Finset.prod_univ_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.prod_mul_distrib]
      congr 1
      by_cases hall : ∀ k : Fin K, ∀ p ∈ f k, Pev y p
      · have h1 : ∀ p ∈ Finset.univ.biUnion f, Pev y p := by
          intro p hp; obtain ⟨k, _, hpk⟩ := Finset.mem_biUnion.mp hp; exact hall k p hpk
        rw [if_pos h1]
        exact Finset.prod_eq_one fun k _ => if_pos (hall k)
      · have h1 : ¬ ∀ p ∈ Finset.univ.biUnion f, Pev y p := by
          intro h; apply hall; intro k p hpk; exact h p (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hpk⟩)
        rw [if_neg h1]
        push Not at hall
        obtain ⟨k0, p0, hp0, hnp0⟩ := hall
        refine Finset.prod_eq_zero (Finset.mem_univ k0) ?_
        exact if_neg (fun h => hnp0 (h p0 hp0))
    have hexp_main :
        (∏ k : Fin K, ∑ S ∈ F k, (-1 : ℝ) ^ S.card * (∏ p ∈ S, ν p)) =
        ∑ f ∈ Dom, (∏ k : Fin K, (-1 : ℝ) ^ (f k).card) * (∏ p ∈ Finset.univ.biUnion f, ν p) := by
      rw [Finset.prod_univ_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      rw [Finset.prod_mul_distrib]
      congr 1
      have hdisj_f : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint f := by
        intro i _ j _ hij
        have hfi : f i ⊆ Bk i := Finset.mem_powerset.mp (Finset.mem_filter.mp (hF i ((Fintype.mem_piFinset.mp hf) i))).1
        have hfj : f j ⊆ Bk j := Finset.mem_powerset.mp (Finset.mem_filter.mp (hF j ((Fintype.mem_piFinset.mp hf) j))).1
        exact (hBk_disj i j hij).mono hfi hfj
      exact (Finset.prod_biUnion hdisj_f).symm
    rw [Finset.sum_congr rfl hexp_y, Finset.sum_comm, hexp_main, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc |∑ f ∈ Dom, ((∑ y ∈ I', (∏ k : Fin K, (-1 : ℝ) ^ (f k).card) *
            (if ∀ p ∈ Finset.univ.biUnion f, Pev y p then (1 : ℝ) else 0)) -
            (L' : ℝ) * ((∏ k : Fin K, (-1 : ℝ) ^ (f k).card) * (∏ p ∈ Finset.univ.biUnion f, ν p)))|
        ≤ ∑ f ∈ Dom, |(∑ y ∈ I', (∏ k : Fin K, (-1 : ℝ) ^ (f k).card) *
            (if ∀ p ∈ Finset.univ.biUnion f, Pev y p then (1 : ℝ) else 0)) -
            (L' : ℝ) * ((∏ k : Fin K, (-1 : ℝ) ^ (f k).card) * (∏ p ∈ Finset.univ.biUnion f, ν p))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ f ∈ Dom, ∏ k : Fin K, (2 : ℝ) ^ (f k).card := by
          refine Finset.sum_le_sum fun f hf => ?_
          have hsign : |∏ k : Fin K, (-1 : ℝ) ^ (f k).card| = 1 := by
            rw [Finset.abs_prod]; refine Finset.prod_eq_one fun k _ => by simp
          have hsum_card : (∑ i ∈ I', if ∀ p ∈ Finset.univ.biUnion f, Pev i p then (1 : ℝ) else 0) =
              (((Finset.Ico Y0 (Y0 + L')).filter (fun y => ∀ p ∈ Finset.univ.biUnion f, y % p ∈ bad p)).card : ℝ) := by
            rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases h : ∀ p ∈ Finset.univ.biUnion f, Pev i p
            · have h' : ∀ p ∈ Finset.univ.biUnion f, i % p ∈ bad p := h
              rw [if_pos h, if_pos h']; simp
            · have h' : ¬ ∀ p ∈ Finset.univ.biUnion f, i % p ∈ bad p := h
              rw [if_neg h, if_neg h']
          rw [← Finset.mul_sum, hsum_card, ← mul_assoc, mul_comm (L' : ℝ), mul_assoc, ← mul_sub,
            abs_mul, hsign, one_mul]
          let S := Finset.univ.biUnion f
          have hS_prime : ∀ p ∈ S, p.Prime := by
            intro p hp; obtain ⟨k, _, hpk⟩ := Finset.mem_biUnion.mp hp
            have hfk : f k ⊆ Bk k := Finset.mem_powerset.mp (Finset.mem_filter.mp (hF k ((Fintype.mem_piFinset.mp hf) k))).1
            exact hBk_prime k p (hfk hpk)
          have hS_sub : ∀ p ∈ S, bad p ⊆ Finset.range p := by
            intro p hp; obtain ⟨k, _, hpk⟩ := Finset.mem_biUnion.mp hp
            have hfk : f k ⊆ Bk k := Finset.mem_powerset.mp (Finset.mem_filter.mp (hF k ((Fintype.mem_piFinset.mp hf) k))).1
            exact hbad_sub k p (hfk hpk)
          have hcrt := crt_count_bad_subset Y0 L' S hS_prime bad hS_sub
          refine hcrt.trans ?_
          have hdisj_f : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint f := by
            intro i _ j _ hij
            have hfi : f i ⊆ Bk i := Finset.mem_powerset.mp (Finset.mem_filter.mp (hF i ((Fintype.mem_piFinset.mp hf) i))).1
            have hfj : f j ⊆ Bk j := Finset.mem_powerset.mp (Finset.mem_filter.mp (hF j ((Fintype.mem_piFinset.mp hf) j))).1
            exact (hBk_disj i j hij).mono hfi hfj
          calc ∏ p ∈ S, ((bad p).card : ℝ)
              ≤ ∏ p ∈ S, (2 : ℝ) := by
                refine Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun p hp => ?_
                obtain ⟨k, _, hpk⟩ := Finset.mem_biUnion.mp hp
                have hfk : f k ⊆ Bk k := Finset.mem_powerset.mp (Finset.mem_filter.mp (hF k ((Fintype.mem_piFinset.mp hf) k))).1
                exact_mod_cast hbad_card_le2 k p (hfk hpk)
            _ = ∏ k : Fin K, ∏ _p ∈ f k, (2 : ℝ) := Finset.prod_biUnion hdisj_f
            _ = ∏ k : Fin K, (2 : ℝ) ^ (f k).card := by
                refine Finset.prod_congr rfl fun k _ => by simp
      _ = ∏ k : Fin K, ∑ S ∈ F k, (2 : ℝ) ^ S.card := (Finset.prod_univ_sum F (fun _ S => (2 : ℝ) ^ S.card)).symm
      _ ≤ ∏ k : Fin K, ∑ S ∈ FamU k, (2 : ℝ) ^ S.card := by
          refine Finset.prod_le_prod (fun k _ => Finset.sum_nonneg fun _ _ => pow_nonneg (by norm_num) _)
            fun k _ => Finset.sum_le_sum_of_subset_of_nonneg (hF k) (fun _ _ _ => pow_nonneg (by norm_num) _)
  -- Step 9: Bound the total CRT error term by 2^25 * z^25
  have hprod_err_bound : ∏ k : Fin K, ∑ S ∈ FamU k, (2 : ℝ) ^ S.card ≤ 2 ^ 25 * z ^ 25 := by
    have hper : ∀ k : Fin K, ∑ S ∈ FamU k, (2 : ℝ) ^ S.card ≤ 2 * ((2 : ℝ) ^ Mk k.val) ^ (2 * rk k) := by
      intro k
      have hMk2 : 2 ≤ Mk k.val := by
        have hgt : Mbase < Mk k.val := hM_gt k.val k.isLt
        omega
      have hBk_card : (Bk k).card ≤ 2 ^ (Mk k.val - 1) := by
        have hsub : Bk k ⊆ (Finset.Ioc 2 (2 ^ Mk k.val)).filter Nat.Prime := by
          intro p hp
          simp only [Bk, Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
          have hgt := lt_of_le_of_lt (le_max_left _ _) hp.1.1
          exact ⟨⟨by omega, hp.1.2.trans (min_le_right _ _)⟩, hp.2⟩
        exact (Finset.card_le_card hsub).trans (odd_primes_card_le (Mk k.val) (by omega))
      exact sum_weighted_powerset_le (Bk k) (2 * rk k) (Mk k.val) hMk2 hBk_card
    calc ∏ k : Fin K, ∑ S ∈ FamU k, (2 : ℝ) ^ S.card
        ≤ ∏ k : Fin K, (2 * ((2 : ℝ) ^ Mk k.val) ^ (2 * rk k)) := by
          refine Finset.prod_le_prod (fun k _ => Finset.sum_nonneg fun _ _ => by positivity)
            (fun k _ => hper k)
      _ = (2 : ℝ) ^ K * (2 : ℝ) ^ (∑ k : Fin K, Mk k.val * (2 * rk k)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          congr 1
          simp_rw [← pow_mul]
          rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ (2 * z) * (2 : ℝ) ^ (24 * M0) := by
          refine mul_le_mul h2K_le ?_ (by positivity) (by positivity)
          have hexp : ∑ k : Fin K, Mk k.val * (2 * rk k) ≤ 24 * M0 := by
            have hR : ((∑ k : Fin K, Mk k.val * (2 * rk k) : ℕ) : ℝ) ≤ (24 * M0 : ℝ) := by
              rw [Nat.cast_sum, Fin.sum_univ_eq_sum_range (fun k => ((Mk k * (2 * (5 + k)) : ℕ) : ℝ))]
              calc ∑ k ∈ Finset.range K, ((Mk k * (2 * (5 + k)) : ℕ) : ℝ)
                  ≤ ∑ k ∈ Finset.range K, ((M0 : ℝ) / (2 : ℝ) ^ k) * (2 * (5 + k) : ℝ) := by
                    refine Finset.sum_le_sum fun k _ => ?_
                    push_cast
                    have hdiv : (Mk k : ℝ) ≤ (M0 : ℝ) / (2 : ℝ) ^ k := by
                      rw [le_div_iff₀ (by positivity)]
                      have : Mk k * 2 ^ k ≤ M0 := Nat.div_mul_le_self M0 (2 ^ k)
                      exact_mod_cast this
                    gcongr
                _ = (M0 : ℝ) * ∑ k ∈ Finset.range K, (2 * (5 + k) : ℝ) / (2 : ℝ) ^ k := by
                    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
                _ ≤ (M0 : ℝ) * 24 := by gcongr; exact sum_linear_geom_le K
                _ = 24 * (M0 : ℝ) := by ring
            exact_mod_cast hR
          exact pow_le_pow_right₀ (by norm_num) hexp
      _ ≤ (2 * z) * (2 * z) ^ (24 : ℕ) := by
          have h2M : (2 : ℝ) ^ (24 * M0) = ((2 ^ M0 : ℕ) : ℝ) ^ (24 : ℕ) := by
            rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm]
          rw [h2M]
          gcongr
      _ = 2 ^ 25 * z ^ 25 := by ring
  -- Step 10: Combine telescoping inequality, main term, and error bound to get ∑ y ∈ I', ∏ k, ak y k > 0
  have hsum_pos : (0 : ℝ) < ∑ y ∈ I', ∏ k : Fin K, ak y k := by
    have hpt : ∀ y ∈ I',
        (∏ k : Fin K, Uk y k) - ∑ i : Fin K, (Uk y i - Lk y i) * (∏ k ∈ Finset.univ.erase i, Uk y k) ≤
        ∏ k : Fin K, ak y k := by
      intro y _
      refine prod_ge_telescoping Finset.univ (ak y) (Lk y) (Uk y) ?_ ?_ ?_
      · intro k _; dsimp only [ak]; split_ifs <;> norm_num
      · intro k _; exact bonferroni_lower (Bk k) (Pev y) (by dsimp only [rk]; omega)
      · intro k _; exact bonferroni_upper (Bk k) (Pev y) (rk k)
    have hsum_ge :
        (∑ y ∈ I', ∏ k : Fin K, Uk y k) -
        ∑ i : Fin K, ∑ y ∈ I', (Uk y i - Lk y i) * (∏ k ∈ Finset.univ.erase i, Uk y k) ≤
        ∑ y ∈ I', ∏ k : Fin K, ak y k := by
      have h1 := Finset.sum_le_sum hpt
      rw [Finset.sum_sub_distrib, Finset.sum_comm] at h1
      exact h1
    -- Error on first term
    have herr0 :
        |(∑ y ∈ I', ∏ k : Fin K, Uk y k) - (L' : ℝ) * ∏ k : Fin K, EU k| ≤
        2 ^ 25 * z ^ 25 :=
      (htuple_err FamU (fun _ => subset_rfl)).trans hprod_err_bound
    -- Error on each subtracted term i
    have herri : ∀ i : Fin K,
        |(∑ y ∈ I', (Uk y i - Lk y i) * (∏ k ∈ Finset.univ.erase i, Uk y k)) -
          (L' : ℝ) * (ED i * ∏ k ∈ Finset.univ.erase i, EU k)| ≤
        2 ^ 25 * z ^ 25 := by
      intro i
      let Fi : Fin K → Finset (Finset ℕ) := fun k => if k = i then FamD k else FamU k
      have hFi_sub : ∀ k, Fi k ⊆ FamU k := fun k => by
        dsimp only [Fi]; split_ifs; exact hFamD_sub k; exact subset_rfl
      have hrew_y : ∀ y ∈ I',
          (Uk y i - Lk y i) * (∏ k ∈ Finset.univ.erase i, Uk y k) =
          ∏ k : Fin K, ∑ S ∈ Fi k, (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, Pev y p then 1 else 0) := by
        intro y _
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
        congr 1
        · rw [bonferroni_diff (Bk i) (Pev y) (by dsimp only [rk]; omega)]
          simp only [Fi, if_pos rfl, FamD]
          refine Finset.sum_congr rfl fun S hS => ?_
          have hc := (Finset.mem_powersetCard.mp hS).2
          rw [hc, pow_mul]; norm_num
        · refine Finset.prod_congr rfl fun k hk => ?_
          have hki : k ≠ i := (Finset.mem_erase.mp hk).1
          simp only [Fi, if_neg hki, Uk, FamU]
      have hrew_E :
          ED i * (∏ k ∈ Finset.univ.erase i, EU k) =
          ∏ k : Fin K, ∑ S ∈ Fi k, (-1 : ℝ) ^ S.card * (∏ p ∈ S, ν p) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
        congr 1
        · simp only [Fi, if_pos rfl, ED, FamD]
          refine Finset.sum_congr rfl fun S hS => ?_
          have hc := (Finset.mem_powersetCard.mp hS).2
          rw [hc, pow_mul]; norm_num
        · refine Finset.prod_congr rfl fun k hk => ?_
          have hki : k ≠ i := (Finset.mem_erase.mp hk).1
          simp only [Fi, if_neg hki, EU, FamU]
      rw [Finset.sum_congr rfl hrew_y, hrew_E]
      exact (htuple_err Fi hFi_sub).trans hprod_err_bound
    have htotal_err :
        (∑ y ∈ I', ∏ k : Fin K, Uk y k) -
          ∑ i : Fin K, ∑ y ∈ I', (Uk y i - Lk y i) * (∏ k ∈ Finset.univ.erase i, Uk y k) ≥
        (L' : ℝ) * ((∏ k : Fin K, EU k) - ∑ i : Fin K, ED i * (∏ k ∈ Finset.univ.erase i, EU k)) -
          ((K : ℝ) + 1) * (2 ^ 25 * z ^ 25) := by
      have h0 := (abs_le.mp herr0).1
      have hi_sum : ∑ i : Fin K, ∑ y ∈ I', (Uk y i - Lk y i) * (∏ k ∈ Finset.univ.erase i, Uk y k) ≤
          (L' : ℝ) * ∑ i : Fin K, ED i * (∏ k ∈ Finset.univ.erase i, EU k) +
          (K : ℝ) * (2 ^ 25 * z ^ 25) := by
        have hstep : ∀ i : Fin K,
            ∑ y ∈ I', (Uk y i - Lk y i) * (∏ k ∈ Finset.univ.erase i, Uk y k) ≤
            (L' : ℝ) * (ED i * ∏ k ∈ Finset.univ.erase i, EU k) + 2 ^ 25 * z ^ 25 := fun i => by
          linarith [(abs_le.mp (herri i)).2]
        calc ∑ i : Fin K, ∑ y ∈ I', (Uk y i - Lk y i) * (∏ k ∈ Finset.univ.erase i, Uk y k)
            ≤ ∑ i : Fin K, ((L' : ℝ) * (ED i * ∏ k ∈ Finset.univ.erase i, EU k) + 2 ^ 25 * z ^ 25) :=
              Finset.sum_le_sum fun i _ => hstep i
          _ = (L' : ℝ) * ∑ i : Fin K, ED i * (∏ k ∈ Finset.univ.erase i, EU k) +
              (K : ℝ) * (2 ^ 25 * z ^ 25) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul]
      linarith only [h0, hi_sum]
    have hL'_main : (L' : ℝ) / (z ^ 2) ≥ 2 ^ 29 * z ^ 27 := by
      have h1 : C * z ^ (29 : ℕ) / (2 * (Q0 : ℝ)) ≤ (L' : ℝ) :=
        (div_le_div_of_nonneg_right hLC (by linarith only [hQ0_posR])).trans hL'_ge
      have h2 : (2 ^ 29 : ℝ) * z ^ (29 : ℕ) ≤ C * z ^ (29 : ℕ) / (2 * (Q0 : ℝ)) := by
        rw [le_div_iff₀ (by linarith only [hQ0_posR])]
        calc (2 ^ 29 : ℝ) * z ^ (29 : ℕ) * (2 * (Q0 : ℝ))
            = ((2 ^ 30 : ℝ) * (Q0 : ℝ)) * z ^ (29 : ℕ) := by ring
          _ ≤ C * z ^ (29 : ℕ) := mul_le_mul_of_nonneg_right hC_ge_Q0 (pow_nonneg hz_pos.le _)
      have h3 : (2 ^ 29 : ℝ) * z ^ (29 : ℕ) / (z ^ 2) = 2 ^ 29 * z ^ 27 := by
        field_simp [hz_pos.ne']
      calc 2 ^ 29 * z ^ 27 = (2 ^ 29 : ℝ) * z ^ (29 : ℕ) / (z ^ 2) := h3.symm
        _ ≤ (L' : ℝ) / (z ^ 2) := div_le_div_of_nonneg_right (h2.trans h1) (sq_nonneg z)
    have herr_final : ((K : ℝ) + 1) * (2 ^ 25 * z ^ 25) ≤ 2 ^ 26 * z ^ 26 := by
      calc ((K : ℝ) + 1) * (2 ^ 25 * z ^ 25)
          ≤ (2 * z) * (2 ^ 25 * z ^ 25) :=
            mul_le_mul_of_nonneg_right hK_le (mul_nonneg (by norm_num) (pow_nonneg hz_pos.le _))
        _ = 2 ^ 26 * z ^ 26 := by ring
    have hz_ge1 : (1 : ℝ) ≤ z := by linarith only [hC3, hzC]
    have hz26_pos : (0 : ℝ) < z ^ 26 := pow_pos hz_pos 26
    have hstrict : 2 ^ 26 * z ^ 26 < 2 ^ 29 * z ^ 27 := by
      have hzpow : z ^ 26 ≤ z ^ 27 := pow_le_pow_right₀ hz_ge1 (by omega)
      linarith only [hz26_pos, hzpow]
    linarith only [hsum_ge, htotal_err, hmain_comb, hL'_main, herr_final, hstrict]
  -- Step 11: Extract a surviving y ∈ I' and return x = x0 + Q0 * y
  have hex_y : ∃ y ∈ I', (0 : ℝ) < ∏ k : Fin K, ak y k := by
    by_contra hall
    push Not at hall
    have hle : ∑ y ∈ I', ∏ k : Fin K, ak y k ≤ 0 := Finset.sum_nonpos hall
    linarith only [hsum_pos, hle]
  obtain ⟨y, hyI', hy_pos⟩ := hex_y
  refine ⟨x0 + Q0 * y, hmap_Ico y hyI', ?_, ?_⟩
  · -- ¬ 2 ∣ x0 + Q0 * y
    have h2Q0 : 2 ∣ Q0 := Finset.dvd_prod_of_mem (fun x => x) h2_mem_P0
    have h2x0 : x0 % 2 ≠ 0 := by
      have h := hx0_good 2 h2_mem_P0
      simp only [bad0, if_pos rfl, Finset.mem_singleton] at h
      exact h
    intro hdvd
    have h1 : 2 ∣ x0 := (Nat.dvd_add_left (dvd_mul_of_dvd_left h2Q0 y)).mp hdvd
    exact h2x0 (Nat.mod_eq_zero_of_dvd h1)
  · intro p hp hp3 hpz
    by_cases hsmall : p ≤ 2 ^ Mbase
    · have hpP0 : p ∈ P0 := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
      have hpQ0 : p ∣ Q0 := Finset.dvd_prod_of_mem (fun x => x) hpP0
      have hnot := hx0_good p hpP0
      simp only [bad0, if_neg (by omega : p ≠ 2), Finset.mem_filter, Finset.mem_range,
        not_and, not_or] at hnot
      have hnot' := hnot (Nat.mod_lt x0 hp.pos)
      have hmod1 : (x0 : ℤ) ≡ ((x0 % p : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
        rw [Int.ModEq, Int.natCast_mod, Int.emod_emod]
      have hmod2 : ((x0 + Q0 * y : ℕ) : ℤ) ≡ (x0 : ℤ) [ZMOD (p : ℤ)] := by
        rw [Int.ModEq]; push_cast
        have : (p : ℤ) ∣ (Q0 : ℤ) * (y : ℤ) := dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hpQ0) _
        rw [Int.add_emod, Int.emod_eq_zero_of_dvd this, add_zero, Int.emod_emod]
      have hmod3 : ((x0 + Q0 * y : ℕ) : ℤ) ≡ ((x0 % p : ℕ) : ℤ) [ZMOD (p : ℤ)] := hmod2.trans hmod1
      constructor
      · intro hdvd
        apply hnot'.1
        exact (Int.ModEq.dvd_iff hmod3).mp hdvd
      · intro hdvd
        apply hnot'.2
        have hm4 : a * ((x0 + Q0 * y : ℕ) : ℤ) + b ≡ a * ((x0 % p : ℕ) : ℤ) + b [ZMOD (p : ℤ)] :=
          (Int.ModEq.mul_left a hmod3).add_right b
        exact (Int.ModEq.dvd_iff hm4).mp hdvd
    · have hgtbase : 2 ^ Mbase < p := by omega
      have hple : p ≤ ⌊z⌋₊ := Nat.le_floor hpz
      obtain ⟨k, hpk⟩ := hcover p hp hgtbase hple
      have hak_ne0 : ak y k ≠ 0 := by
        intro h0
        have := Finset.prod_eq_zero (Finset.mem_univ k) h0
        linarith
      have hnotP : ¬ Pev y p := by
        dsimp only [ak] at hak_ne0
        split_ifs at hak_ne0 with hall
        · exact hall p hpk
        · exact absurd rfl hak_ne0
      have hiff := hbad_iff k p hpk y
      have hno := mt hiff.mpr hnotP
      push Not at hno
      exact hno

private lemma sieve_29 :
    ∃ C : ℝ, 3 ≤ C ∧ ∀ (z : ℝ) (X L : ℕ) (a b : ℤ),
      C ≤ z → C * z ^ (29 : ℕ) ≤ (L : ℝ) →
      (∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z → ¬ ((p : ℤ) ∣ a)) →
      ∃ x ∈ Finset.Ico X (X + L),
        ¬ 2 ∣ x ∧
        ∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z →
          ¬ ((p : ℤ) ∣ (x : ℤ)) ∧ ¬ ((p : ℤ) ∣ a * (x : ℤ) + b) :=
  sieve_29_aux 200 le_rfl

end Sieve29

/- ### Section 5: Deduction of Chowla-Erdos-Straus (1960): maxMOLS n >> n^(1/91) -/

theorem chowla_erdos_straus_proof :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((1 : ℝ) / 91) ≤ (maxMOLS n : ℝ) := by
  obtain ⟨C, hC3, hsieve⟩ := sieve_29
  let c : ℝ := 1 / (40 * C ^ (3 : ℕ))
  have hc_pos : 0 < c := by positivity
  refine ⟨c / 2, by positivity, ?_⟩
  have hpow_atTop : Tendsto (fun n : ℕ => c * (n : ℝ) ^ ((1 : ℝ) / 91)) atTop atTop :=
    Tendsto.const_mul_atTop hc_pos
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 91)).comp tendsto_natCast_atTop_atTop)
  have h_ev1 : ∀ᶠ n : ℕ in atTop, C ≤ c * (n : ℝ) ^ ((1 : ℝ) / 91) :=
    hpow_atTop.eventually (eventually_ge_atTop C)
  have h_ev2 : ∀ᶠ n : ℕ in atTop, (6 : ℝ) ≤ c * (n : ℝ) ^ ((1 : ℝ) / 91) :=
    hpow_atTop.eventually (eventually_ge_atTop 6)
  have h_ev3 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  filter_upwards [h_ev1, h_ev2, h_ev3] with n hzC hz6 hn2
  set z : ℝ := c * (n : ℝ) ^ ((1 : ℝ) / 91)
  have hz3 : 3 ≤ z := by linarith
  obtain ⟨k, hk2, hzA, hA2z⟩ := exists_pow_two_near hz3
  let A : ℕ := 2 ^ k
  have hA_ge : 4 ≤ A := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk2
    simpa [A] using this
  have hA_odd : ∀ p : ℕ, p.Prime → 3 ≤ p → ¬ ((p : ℤ) ∣ (A : ℤ)) := by
    intro p hp hp3 hdiv
    have hdivN : p ∣ 2 ^ k := Int.natCast_dvd_natCast.mp hdiv
    have hdvd2 := hp.dvd_of_dvd_pow hdivN
    have := (Nat.dvd_prime Nat.prime_two).mp hdvd2
    omega
  let Lq : ℕ := ⌈C * z ^ (29 : ℕ)⌉₊
  have hLq : C * z ^ (29 : ℕ) ≤ (Lq : ℝ) := Nat.le_ceil _
  let bq : ℤ := if Even n then -1 else 1
  obtain ⟨q, hq_mem, hq_odd, hq_sieve⟩ :=
    hsieve z 1 Lq (A : ℤ) bq hzC hLq (fun p hp hp3 _ => hA_odd p hp hp3)
  have hq_ge : 1 ≤ q := (Finset.mem_Ico.mp hq_mem).1
  have hq_lt : q < 1 + Lq := (Finset.mem_Ico.mp hq_mem).2
  have hLq_lt : (Lq : ℝ) < C * z ^ (29 : ℕ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hq_leR : (q : ℝ) ≤ 2 * C * z ^ (29 : ℕ) := by
    have hqR : (q : ℝ) < 1 + (Lq : ℝ) := by exact_mod_cast hq_lt
    have hz29 : (1 : ℝ) ≤ z ^ (29 : ℕ) := one_le_pow₀ (by linarith)
    have hCz29 : (2 : ℝ) ≤ C * z ^ (29 : ℕ) := by nlinarith
    linarith
  let m : ℕ := if Even n then A * q - 1 else A * q
  have hAq4 : 4 ≤ A * q := Nat.mul_le_mul hA_ge hq_ge
  have hm_ge3 : 3 ≤ m := by dsimp only [m]; split_ifs <;> omega
  have hm_leR : (m : ℝ) ≤ 4 * C * z ^ (30 : ℕ) := by
    have hAqR : ((A * q : ℕ) : ℝ) ≤ 4 * C * z ^ (30 : ℕ) := by
      calc ((A * q : ℕ) : ℝ) = (A : ℝ) * (q : ℝ) := by push_cast; ring
        _ ≤ (2 * z) * (2 * C * z ^ (29 : ℕ)) := by gcongr
        _ = 4 * C * z ^ (30 : ℕ) := by ring
    dsimp only [m]
    split_ifs with he
    · have hsub : ((A * q - 1 : ℕ) : ℝ) ≤ ((A * q : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le (A * q) 1
      linarith
    · exact hAqR
  have hAq_pos : 1 ≤ A * q := by nlinarith
  have hm_nodvd : ∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z → ¬ p ∣ m := by
    intro p hp hp3 hpz hpm
    have hps := hq_sieve p hp hp3 hpz
    dsimp only [m] at hpm
    split_ifs at hpm with he
    · have hpmZ : (p : ℤ) ∣ (A : ℤ) * (q : ℤ) + bq := by
        have hcast : ((A * q - 1 : ℕ) : ℤ) = (A : ℤ) * (q : ℤ) + bq := by simp [bq, he]; omega
        rw [← hcast]; exact Int.natCast_dvd_natCast.mpr hpm
      exact hps.2 hpmZ
    · rcases hp.dvd_mul.mp hpm with hpA | hpq
      · exact hA_odd p hp hp3 (Int.natCast_dvd_natCast.mpr hpA)
      · exact hps.1 (Int.natCast_dvd_natCast.mpr hpq)
  have hm_fac : ∀ p ∈ m.primeFactors, z < ((p ^ (m.factorization p) : ℕ) : ℝ) := by
    intro p hp_mem
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hpm := (Nat.mem_primeFactors.mp hp_mem).2.1
    by_cases hp2 : p = 2
    · subst hp2
      by_cases he : Even n
      · have h2A : 2 ∣ A := dvd_pow_self 2 (by omega)
        have h2Aq : 2 ∣ A * q := dvd_mul_of_dvd_left h2A q
        have hodd_m : ¬ 2 ∣ m := by dsimp only [m]; rw [if_pos he]; omega
        exact False.elim (hodd_m hpm)
      · have hm_eq : m = A * q := by simp [m, he]
        have hpow_dvd : 2 ^ k ∣ m := by rw [hm_eq]; exact dvd_mul_right A q
        have hk_le : k ≤ m.factorization 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp hpow_dvd
        have h2le : A ≤ 2 ^ m.factorization 2 := Nat.pow_le_pow_right (by omega) hk_le
        exact hzA.trans_le (by exact_mod_cast h2le)
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hzp : z < (p : ℝ) := by
        by_contra hle; push Not at hle; exact hm_nodvd p hp hp3 hle hpm
      have hk1 : 1 ≤ m.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpm
      exact hzp.trans_le (by exact_mod_cast Nat.le_self_pow (by omega) p)
  have hm1_fac : ∀ p ∈ (m + 1).primeFactors, z < ((p ^ ((m + 1).factorization p) : ℕ) : ℝ) := by
    intro p hp_mem
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hpm1 := (Nat.mem_primeFactors.mp hp_mem).2.1
    by_cases hp2 : p = 2
    · subst hp2
      by_cases he : Even n
      · have hm1_eq : m + 1 = A * q := by dsimp only [m]; rw [if_pos he]; omega
        have hpow_dvd : 2 ^ k ∣ m + 1 := by rw [hm1_eq]; exact dvd_mul_right A q
        have hk_le : k ≤ (m + 1).factorization 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp hpow_dvd
        have h2le : A ≤ 2 ^ (m + 1).factorization 2 := Nat.pow_le_pow_right (by omega) hk_le
        exact hzA.trans_le (by exact_mod_cast h2le)
      · have h2A : 2 ∣ A := dvd_pow_self 2 (by omega)
        have h2Aq : 2 ∣ A * q := dvd_mul_of_dvd_left h2A q
        have hodd_m1 : ¬ 2 ∣ m + 1 := by dsimp only [m]; rw [if_neg he]; omega
        exact False.elim (hodd_m1 hpm1)
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hzp : z < (p : ℝ) := by
        by_contra hle; push Not at hle
        have hps := hq_sieve p hp hp3 hle
        dsimp only [m] at hpm1
        split_ifs at hpm1 with he
        · have hsub1 : A * q - 1 + 1 = A * q := Nat.sub_add_cancel hAq_pos
          have hpAq : p ∣ A * q := by rwa [hsub1] at hpm1
          rcases hp.dvd_mul.mp hpAq with hpA | hpq
          · exact hA_odd p hp hp3 (Int.natCast_dvd_natCast.mpr hpA)
          · exact hps.1 (Int.natCast_dvd_natCast.mpr hpq)
        · have hpmZ : (p : ℤ) ∣ (A : ℤ) * (q : ℤ) + bq := by
            have hcast : ((A * q + 1 : ℕ) : ℤ) = (A : ℤ) * (q : ℤ) + bq := by simp [bq, he]
            rw [← hcast]; exact Int.natCast_dvd_natCast.mpr hpm1
          exact hps.2 hpmZ
      have hk1 : 1 ≤ (m + 1).factorization p :=
        Nat.Prime.factorization_pos_of_dvd hp (by omega) hpm1
      exact hzp.trans_le (by exact_mod_cast Nat.le_self_pow (by omega) p)
  let Xt : ℕ := ⌈(n : ℝ) / ((m : ℝ) + 1)⌉₊
  let Yt : ℕ := (n - 2) / m + 1
  have hnz91 : (n : ℝ) = z ^ (91 : ℕ) / c ^ (91 : ℕ) := by
    have hz_pow : z ^ (91 : ℕ) = c ^ (91 : ℕ) * (n : ℝ) := by
      dsimp only [z]
      rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 91)) 91,
        ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hz_pow]; field_simp [hc_pos.ne']
  have hmm1_le : (m : ℝ) * ((m : ℝ) + 1) ≤ 20 * C ^ (2 : ℕ) * z ^ (60 : ℕ) := by
    have hm1_le : (m : ℝ) + 1 ≤ 5 * C * z ^ (30 : ℕ) := by
      have : (1 : ℝ) ≤ z ^ (30 : ℕ) := one_le_pow₀ (by linarith)
      nlinarith
    calc (m : ℝ) * ((m : ℝ) + 1) ≤ (4 * C * z ^ (30 : ℕ)) * (5 * C * z ^ (30 : ℕ)) := by gcongr
      _ = 20 * C ^ (2 : ℕ) * z ^ (60 : ℕ) := by ring
  have hc91_le : 20 * C ^ (2 : ℕ) * c ^ (91 : ℕ) ≤ 1 / (2 * C) := by
    have h40 : (1 : ℝ) ≤ 40 * C ^ (3 : ℕ) := by nlinarith
    have hc_le1 : c ≤ 1 := by
      dsimp only [c]; rw [div_le_one (by positivity)]; exact h40
    have hc91_le1 : c ^ (91 : ℕ) ≤ c ^ (1 : ℕ) := pow_le_pow_of_le_one hc_pos.le hc_le1 (by omega)
    rw [pow_one] at hc91_le1
    calc 20 * C ^ (2 : ℕ) * c ^ (91 : ℕ) ≤ 20 * C ^ (2 : ℕ) * c := by gcongr
      _ = 1 / (2 * C) := by dsimp only [c]; field_simp; ring
  have hdiff_ge : C * z ^ (29 : ℕ) ≤ (Yt : ℝ) - (Xt : ℝ) := by
    have hYt_gt : ((n : ℝ) - 2) / (m : ℝ) < (Yt : ℝ) := by
      have hm_pos : 0 < m := by omega
      have hdiv : n - 2 < m * ((n - 2) / m + 1) := by
        have := Nat.lt_div_mul_add hm_pos (a := n - 2); linarith
      have hdivR : ((n - 2 : ℕ) : ℝ) < (m : ℝ) * (((n - 2) / m + 1 : ℕ) : ℝ) := by exact_mod_cast hdiv
      have hn2R : (n : ℝ) - 2 = ((n - 2 : ℕ) : ℝ) := by rw [Nat.cast_sub hn2]; norm_num
      rw [hn2R]
      exact (div_lt_iff₀' (by positivity)).mpr (by simpa [Yt] using hdivR)
    have hXt_lt : (Xt : ℝ) < (n : ℝ) / ((m : ℝ) + 1) + 1 := Nat.ceil_lt_add_one (by positivity)
    have hn_gap : 2 * C * z ^ (29 : ℕ) ≤ (n : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) := by
      rw [hnz91, div_div]
      have hden_pos : 0 < c ^ (91 : ℕ) * ((m : ℝ) * ((m : ℝ) + 1)) := by positivity
      rw [le_div_iff₀ hden_pos]
      have hz89_le : z ^ (89 : ℕ) ≤ z ^ (91 : ℕ) := pow_le_pow_right₀ (by linarith) (by omega)
      calc 2 * C * z ^ (29 : ℕ) * (c ^ (91 : ℕ) * ((m : ℝ) * ((m : ℝ) + 1)))
          ≤ 2 * C * z ^ (29 : ℕ) * (c ^ (91 : ℕ) * (20 * C ^ (2 : ℕ) * z ^ (60 : ℕ))) := by gcongr
        _ = 2 * C * (20 * C ^ (2 : ℕ) * c ^ (91 : ℕ)) * z ^ (89 : ℕ) := by ring
        _ ≤ 2 * C * (1 / (2 * C)) * z ^ (91 : ℕ) := by gcongr
        _ = z ^ (91 : ℕ) := by field_simp
    have hsub_id : (n : ℝ) / (m : ℝ) - (n : ℝ) / ((m : ℝ) + 1) =
        (n : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) := by
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      have hm10 : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp; ring
    have h2m : 2 / (m : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
      linarith
    have hCz29_ge3 : 3 ≤ C * z ^ (29 : ℕ) := by
      have : 1 ≤ z ^ (29 : ℕ) := one_le_pow₀ (by linarith)
      nlinarith
    have hpart : ((n : ℝ) - 2) / (m : ℝ) - ((n : ℝ) / ((m : ℝ) + 1) + 1) =
        ((n : ℝ) / (m : ℝ) - (n : ℝ) / ((m : ℝ) + 1)) - 2 / (m : ℝ) - 1 := by ring
    linarith
  have hXY_le : Xt ≤ Yt := by
    have hpos : (0 : ℝ) ≤ (Yt : ℝ) - (Xt : ℝ) := by
      have : 0 ≤ C * z ^ (29 : ℕ) := by positivity
      linarith
    exact_mod_cast (sub_nonneg.mp hpos)
  let Lt : ℕ := Yt - Xt
  have hLt_eq : Xt + Lt = Yt := Nat.add_sub_cancel' hXY_le
  have hLtR : C * z ^ (29 : ℕ) ≤ (Lt : ℝ) := by
    have : (Lt : ℝ) = (Yt : ℝ) - (Xt : ℝ) := by dsimp only [Lt]; rw [Nat.cast_sub hXY_le]
    linarith
  obtain ⟨t, ht_mem, ht_odd, ht_sieve⟩ :=
    hsieve z Xt Lt (-(m : ℤ)) (n : ℤ) hzC hLtR fun p hp hp3 hpz hdiv =>
      hm_nodvd p hp hp3 hpz (Int.natCast_dvd_natCast.mp (dvd_neg.mp hdiv))
  have ht_ge : Xt ≤ t := (Finset.mem_Ico.mp ht_mem).1
  have ht_lt : t < Yt := by rw [← hLt_eq]; exact (Finset.mem_Ico.mp ht_mem).2
  have hut : n - m * t ≤ t := by
    have h1' : (n : ℝ) / ((m : ℝ) + 1) ≤ (Xt : ℝ) := Nat.le_ceil _
    have h2' : (Xt : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge
    have h3' : (n : ℝ) ≤ (t : ℝ) * ((m : ℝ) + 1) := (div_le_iff₀ (by positivity)).mp (h1'.trans h2')
    have h3N : n ≤ (m + 1) * t := by exact_mod_cast (by linarith : (n : ℝ) ≤ ((m : ℝ) + 1) * (t : ℝ))
    have : n ≤ m * t + t := by linarith
    omega
  have hmt_le : m * t ≤ n - 2 := by
    have htle : t ≤ (n - 2) / m := by omega
    calc m * t ≤ m * ((n - 2) / m) := Nat.mul_le_mul_left m htle
      _ ≤ n - 2 := Nat.mul_div_le (n - 2) m
  let u : ℕ := n - m * t
  have hu2 : 2 ≤ u := by omega
  have ht2 : 2 ≤ t := by omega
  have hn_eq : n = m * t + u := by omega
  have ht_fac : ∀ p ∈ t.primeFactors, z < ((p ^ (t.factorization p) : ℕ) : ℝ) := by
    intro p hp_mem
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hpt := (Nat.mem_primeFactors.mp hp_mem).2.1
    by_cases hp2 : p = 2
    · subst hp2; exact False.elim (ht_odd hpt)
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hzp : z < (p : ℝ) := by
        by_contra hle; push Not at hle
        exact (ht_sieve p hp hp3 hle).1 (Int.natCast_dvd_natCast.mpr hpt)
      have hk1 : 1 ≤ t.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpt
      exact hzp.trans_le (by exact_mod_cast Nat.le_self_pow (by omega) p)
  have hu_odd : ¬ 2 ∣ u := by
    by_cases he : Even n
    · have hm_odd : ¬ 2 ∣ m := by
        have h2Aq : 2 ∣ A * q := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) q
        dsimp only [m]; rw [if_pos he]; omega
      obtain ⟨r, hr⟩ := he
      intro h2u
      have h2mt : 2 ∣ m * t := by omega
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2mt with h2m | h2t
      · exact hm_odd h2m
      · exact ht_odd h2t
    · have hm_even : 2 ∣ m := by
        dsimp only [m]; rw [if_neg he]
        exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) q
      intro h2u
      exact he (even_iff_two_dvd.mpr (by rw [hn_eq]; exact dvd_add (dvd_mul_of_dvd_left hm_even t) h2u))
  have hu_fac : ∀ p ∈ u.primeFactors, z < ((p ^ (u.factorization p) : ℕ) : ℝ) := by
    intro p hp_mem
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hpu := (Nat.mem_primeFactors.mp hp_mem).2.1
    by_cases hp2 : p = 2
    · subst hp2; exact False.elim (hu_odd hpu)
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hzp : z < (p : ℝ) := by
        by_contra hle; push Not at hle
        have hpuZ : (p : ℤ) ∣ -(m : ℤ) * (t : ℤ) + (n : ℤ) := by
          have hcast : (u : ℤ) = -(m : ℤ) * (t : ℤ) + (n : ℤ) := by
            dsimp only [u]; zify [show m * t ≤ n by omega]; ring
          rw [← hcast]; exact Int.natCast_dvd_natCast.mpr hpu
        exact (ht_sieve p hp hp3 hle).2 hpuZ
      have hk1 : 1 ≤ u.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpu
      exact hzp.trans_le (by exact_mod_cast Nat.le_self_pow (by omega) p)
  let s : ℕ := ⌊z⌋₊ - 2
  have hs_le_z : (s : ℝ) + 2 ≤ z := by
    have hfl6 : 6 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz6)
    have hs2 : s + 2 = ⌊z⌋₊ := by omega
    have hs2R : (s : ℝ) + 2 = (⌊z⌋₊ : ℝ) := by exact_mod_cast hs2
    rw [hs2R]; exact Nat.floor_le (by linarith)
  have hsm : s ≤ maxMOLS m := by
    refine macNeish m (by omega) s fun p hp => ?_
    have hltR : (s : ℝ) + 1 < ((p ^ m.factorization p : ℕ) : ℝ) := by linarith [hm_fac p hp]
    have hltN : s + 1 < p ^ m.factorization p := by exact_mod_cast hltR
    omega
  have hsm1 : s ≤ maxMOLS (m + 1) := by
    refine macNeish (m + 1) (by omega) s fun p hp => ?_
    have hltR : (s : ℝ) + 1 < ((p ^ (m + 1).factorization p : ℕ) : ℝ) := by linarith [hm1_fac p hp]
    have hltN : s + 1 < p ^ (m + 1).factorization p := by exact_mod_cast hltR
    omega
  have hst : s + 1 ≤ maxMOLS t := by
    refine macNeish t ht2 (s + 1) fun p hp => ?_
    have hltR : (s : ℝ) + 2 < ((p ^ t.factorization p : ℕ) : ℝ) := by linarith [ht_fac p hp]
    have hltN : s + 2 < p ^ t.factorization p := by exact_mod_cast hltR
    omega
  have hsu : s ≤ maxMOLS u := by
    refine macNeish u hu2 s fun p hp => ?_
    have hltR : (s : ℝ) + 1 < ((p ^ u.factorization p : ℕ) : ℝ) := by linarith [hu_fac p hp]
    have hltN : s + 1 < p ^ u.factorization p := by exact_mod_cast hltR
    omega
  have hs_n : s ≤ maxMOLS n := by
    rw [hn_eq]
    exact wilson_recursion m t u s (by omega) (by omega) hut hsm hsm1 hst hsu
  have hs_lower : c / 2 * (n : ℝ) ^ ((1 : ℝ) / 91) ≤ (s : ℝ) := by
    have hfl6 : 6 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz6)
    have hs2 : s + 2 = ⌊z⌋₊ := by omega
    have hs2R : (s : ℝ) + 2 = (⌊z⌋₊ : ℝ) := by exact_mod_cast hs2
    have hfl_gt : z - 1 < (⌊z⌋₊ : ℝ) := Nat.sub_one_lt_floor z
    have h2' : c / 2 * (n : ℝ) ^ ((1 : ℝ) / 91) = z / 2 := by dsimp only [z]; ring
    linarith
  exact hs_lower.trans (by exact_mod_cast hs_n)

end OMAChowla724

theorem OMA.solution : type_of% @Erdos724.erdos_724.variants.chowla_erdos_straus :=
  OMAChowla724.chowla_erdos_straus_proof
