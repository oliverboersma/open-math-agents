import FormalConjectures.Wikipedia.RudinsConjecture

-- Credit: @senamakel

namespace OMA.RudinWitness
open RudinsConjecture

lemma Q_filter (N q a : ℕ) : Q N q a = ((Finset.range N).filter (fun n => IsSquare (q*n+a))).card := by
  classical
  change Set.ncard _ = _
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp

lemma Q_bound (N q a : ℕ) : Q N q a ≤ N := by
  rw [Q_filter]
  exact (Finset.card_filter_le ..).trans_eq (Finset.card_range N)

lemma no_adjacent (a : ℕ) (ha : 144 ≤ a) : ¬ (IsSquare a ∧ IsSquare (a+24)) := by
  rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  have hx12 : 12 ≤ x := by nlinarith
  have hxy : x < y := by nlinarith
  have hstep : x+1 ≤ y := by omega
  nlinarith [sq_nonneg ((y:ℤ)-(x:ℤ)-1)]

lemma Q_24_bound (a : ℕ) : Q 6 24 a ≤ 4 := by
  classical
  rw [Q_filter]
  by_cases ha : a < 144
  · interval_cases a <;> decide +kernel
  · have ha : 144 ≤ a := by omega
    have h01 := no_adjacent a ha
    have h23 := no_adjacent (a+48) (by omega)
    obtain ⟨i, hi, hni⟩ : ∃ i : ℕ, i < 2 ∧ ¬ IsSquare (24*i+a) := by
      by_cases h0 : IsSquare a
      · refine ⟨1, by omega, ?_⟩
        intro h1
        apply h01 ⟨h0, ?_⟩
        simpa [Nat.add_comm] using h1
      · exact ⟨0, by omega, by simpa using h0⟩
    obtain ⟨j, hj, hnj⟩ : ∃ j : ℕ, (2 ≤ j ∧ j < 4) ∧ ¬ IsSquare (24*j+a) := by
      by_cases h2 : IsSquare (a+48)
      · refine ⟨3, by omega, ?_⟩
        intro h3
        apply h23 ⟨h2, ?_⟩
        rwa [show a + 48 + 24 = 24*3+a by omega]
      · exact ⟨2, by omega, by simpa [Nat.add_comm] using h2⟩
    have hsubset : (Finset.range 6).filter (fun n => IsSquare (24*n+a)) ⊆
        ((Finset.range 6).erase i).erase j := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      simp only [Finset.mem_erase, Finset.mem_range]
      exact ⟨fun hn' => hnj (hn' ▸ hn.2), fun hn' => hni (hn' ▸ hn.2), hn.1⟩
    apply (Finset.card_le_card hsubset).trans
    have himem : i ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
    have hjmem : j ∈ (Finset.range 6).erase i := by simp; omega
    rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem himem]
    decide

end OMA.RudinWitness

open RudinsConjecture OMA.RudinWitness

theorem OMA.disproof : ¬ (type_of% @RudinsConjecture.rudins_conjecture_unique) :=by
  intro hu
  have h120 : IsNontrivial 120 49 := by unfold IsNontrivial; decide +kernel
  have hcount : Q 6 120 49 = 4 := by rw [Q_filter]; decide +kernel
  let S : Set ℕ := {m : ℕ | ∃ q a : ℕ, IsNontrivial q a ∧ Q 6 q a = m}
  have hb : BddAbove S := by
    refine ⟨6, ?_⟩
    rintro m ⟨q,a,_,rfl⟩
    exact Q_bound 6 q a
  have hne : S.Nonempty := ⟨4, 120, 49, h120, hcount⟩
  obtain ⟨q,a,hqa,hmax⟩ := Nat.sSup_mem hne hb
  have hmax' : Q 6 q a = Qmax 6 := hmax
  have hq : q = 24 := hu 6 (by decide) q a hqa hmax'
  have hupper : Qmax 6 ≤ 4 := by
    rw [← hmax',hq]
    exact Q_24_bound a
  have hlower : 4 ≤ Qmax 6 := le_csSup hb (show 4 ∈ S from ⟨120,49,h120,hcount⟩)
  have h120max : Q 6 120 49 = Qmax 6 := by omega
  have hbad := hu 6 (by decide) 120 49 h120 h120max
  omega
