import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R2
import Mathlib.Tactic

/-! A two-point deletion and bipartiteness reduction for the Johnson formulation. -/

open Finset

namespace OMA.R_Erdos835_erdos_835_variants_johnson_R2_H1_R1

/-- Color the blocks avoiding two fixed points. The graph on missing-color incidences
has edges between the two incidences of a star, and between adjacent stars with the
same missing color. Require that graph to be bipartite. -/
def H1 : Prop :=
  ∃ (p : ℕ), Nat.Prime p ∧ 17 ≤ p ∧
    ∃ (x y : Fin (2 * p - 3)), x ≠ y ∧
      ∃ d : Finset (Fin (2 * p - 3)) → Fin p,
        (∀ S : Finset (Fin (2 * p - 3)), S.card = p - 3 → x ∉ S → y ∉ S →
          ∀ a ∉ S, ∀ b ∉ S, a ≠ x → a ≠ y → b ≠ x → b ≠ y → a ≠ b →
            d (insert a S) ≠ d (insert b S)) ∧
        let missing (S : Finset (Fin (2 * p - 3))) (c : Fin p) :=
          ∀ a ∉ S, a ≠ x → a ≠ y → d (insert a S) ≠ c
        ∃ side : Finset (Fin (2 * p - 3)) → Fin p → Bool,
          (∀ S : Finset (Fin (2 * p - 3)), S.card = p - 3 → x ∉ S → y ∉ S →
            ∀ c e, missing S c → missing S e → c ≠ e → side S c ≠ side S e) ∧
          (∀ U : Finset (Fin (2 * p - 3)), U.card = p - 4 → x ∉ U → y ∉ U →
            ∀ a ∉ U, ∀ b ∉ U, a ≠ x → a ≠ y → b ≠ x → b ≠ y → a ≠ b →
              ∀ c, missing (insert a U) c → missing (insert b U) c →
                side (insert a U) c ≠ side (insert b U) c)

/-- In a proper symmetric edge coloring of an odd complete graph with as many colors
as vertices, the color omitted at a vertex is different at every vertex. -/
def H2 : Prop :=
  ∀ (p : ℕ), Odd p → ∀ (Q : Finset (Fin (2 * p - 3))), Q.card = p →
    ∀ (e : Fin (2 * p - 3) → Fin (2 * p - 3) → Fin p),
      (∀ a ∈ Q, ∀ b ∈ Q, e a b = e b a) →
      (∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, b ≠ a → c ≠ a → b ≠ c → e a b ≠ e a c) →
      ∀ f : Fin (2 * p - 3) → Fin p,
        (∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → e a b ≠ f a) → Set.InjOn f Q

lemma choose_false_of_card_two {p : ℕ} (L : Finset (Fin p)) (side : Fin p → Bool)
    (hL : L.card = 2) (hside : Set.InjOn side L) : ∃ a ∈ L, side a = false := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hL
  by_cases ha : side a = false
  · exact ⟨a, by simp, ha⟩
  · refine ⟨b, by simp, ?_⟩
    have h : side a ≠ side b := fun e => hab (hside (by simp) (by simp) e)
    cases hsa : side a <;> cases hsb : side b <;> simp_all

lemma choose_color {p : ℕ} (hp : 17 ≤ p) (x y : Fin (2 * p - 3)) (hxy : x ≠ y)
    (d : Finset (Fin (2 * p - 3)) → Fin p)
    (hd : ∀ S : Finset (Fin (2 * p - 3)), S.card = p - 3 → x ∉ S → y ∉ S →
        ∀ a ∉ S, ∀ b ∉ S, a ≠ x → a ≠ y → b ≠ x → b ≠ y → a ≠ b →
          d (insert a S) ≠ d (insert b S))
    (side : Finset (Fin (2 * p - 3)) → Fin p → Bool)
    (hs : ∀ S : Finset (Fin (2 * p - 3)), S.card = p - 3 → x ∉ S → y ∉ S →
        ∀ c e, (∀ a ∉ S, a ≠ x → a ≠ y → d (insert a S) ≠ c) →
          (∀ a ∉ S, a ≠ x → a ≠ y → d (insert a S) ≠ e) → c ≠ e → side S c ≠ side S e)
    (S : Finset (Fin (2 * p - 3))) (hS : S.card = p - 3) (hx : x ∉ S) (hy : y ∉ S) :
    ∃ c, side S c = false ∧ (∀ a ∉ S, a ≠ x → a ≠ y → d (insert a S) ≠ c) := by
  classical
  let Q : Finset (Fin (2 * p - 3)) := (insert x (insert y S))ᶜ
  let L : Finset (Fin p) := (Q.image (fun a => d (insert a S)))ᶜ
  have hQ : ∀ a, a ∈ Q ↔ a ∉ S ∧ a ≠ x ∧ a ≠ y := by
    intro a
    simp only [Q, mem_compl, mem_insert, not_or]
    tauto
  have hL : ∀ c, c ∈ L ↔ ∀ a ∉ S, a ≠ x → a ≠ y → d (insert a S) ≠ c := by
    intro c
    simp only [L, mem_compl, mem_image, not_exists, not_and, hQ]
    exact ⟨fun h a ha hax hay => h a ⟨ha, hax, hay⟩,
      fun h a ha => h a ha.1 ha.2.1 ha.2.2⟩
  have hQc : Q.card = p - 2 := by
    have hxyS : x ∉ insert y S := by simp [hxy, hx]
    dsimp only [Q]
    rw [card_compl, Fintype.card_fin, card_insert_of_notMem hxyS,
      card_insert_of_notMem hy, hS]
    omega
  have hinj : Set.InjOn (fun a => d (insert a S)) Q := by
    intro a ha b hb he
    obtain ⟨haS, hax, hay⟩ := (hQ a).mp ha
    obtain ⟨hbS, hbx, hby⟩ := (hQ b).mp hb
    by_contra hn
    exact hd S hS hx hy a haS b hbS hax hay hbx hby hn he
  have hLc : L.card = 2 := by
    simp only [L, card_compl, Fintype.card_fin, card_image_of_injOn hinj, hQc]
    omega
  have hinjSide : Set.InjOn (side S) L := by
    intro c hc e he hsce
    by_contra hn
    exact hs S hS hx hy c e ((hL c).mp hc) ((hL e).mp he) hn hsce
  obtain ⟨c, hc, ht⟩ := choose_false_of_card_two L (side S) hLc hinjSide
  exact ⟨c, ht, (hL c).mp hc⟩

lemma restore_last {p : ℕ} (hp : 17 ≤ p) (ho : Odd p) (edge : H2)
    (y : Fin (2 * p - 3)) (d : Finset (Fin (2 * p - 3)) → Fin p)
    (hd : ∀ S : Finset (Fin (2 * p - 3)), S.card = p - 3 → y ∉ S →
        ∀ a ∉ S, ∀ b ∉ S, a ≠ y → b ≠ y → a ≠ b → d (insert a S) ≠ d (insert b S)) :
    ∃ c : Finset (Fin (2 * p - 3)) → Fin p,
      ∀ S : Finset (Fin (2 * p - 3)), S.card = p - 3 →
        ∀ i : Fin p, ∃ a ∉ S, c (insert a S) = i := by
  classical
  have makeMissing (S : Finset (Fin (2 * p - 3))) (hS : S.card = p - 3) (hyS : y ∉ S) :
      ∃ f : Fin p, ∀ a ∉ S, a ≠ y → d (insert a S) ≠ f := by
    let Q : Finset (Fin (2 * p - 3)) := (insert y S)ᶜ
    let im := Q.image (fun z => d (insert z S))
    have hQ : Q.card = p - 1 := by
      simp only [Q, card_compl, Fintype.card_fin, card_insert_of_notMem hyS, hS]
      omega
    have hIm : im.card ≤ p - 1 := by
      simpa only [hQ] using (card_image_le (s := Q) (f := fun z => d (insert z S)))
    have hf : (imᶜ : Finset (Fin p)).Nonempty := by
      apply card_pos.mp
      rw [card_compl, Fintype.card_fin]
      omega
    obtain ⟨f, hf⟩ := hf
    refine ⟨f, fun a ha hay h => ?_⟩
    exact (mem_compl.mp hf) (mem_image.mpr ⟨a, by simp [Q, ha, hay], h⟩)
  let m (S : Finset (Fin (2 * p - 3))) : Fin p :=
    if h : S.card = p - 3 ∧ y ∉ S then (makeMissing S h.1 h.2).choose else ⟨0, by omega⟩
  have hm (S : Finset (Fin (2 * p - 3))) (hS : S.card = p - 3) (hyS : y ∉ S) :
      ∀ a ∉ S, a ≠ y → d (insert a S) ≠ m S := by
    simpa only [m, dif_pos (And.intro hS hyS)] using (makeMissing S hS hyS).choose_spec
  let c (B : Finset (Fin (2 * p - 3))) := if y ∈ B then m (B.erase y) else d B
  refine ⟨c, fun S hS i => ?_⟩
  let Q : Finset (Fin (2 * p - 3)) := Sᶜ
  have hQ : Q.card = p := by
    simp only [Q, card_compl, Fintype.card_fin, hS]
    omega
  have hinj : Set.InjOn (fun a => c (insert a S)) Q := by
    intro a ha b hb he
    have haS : a ∉ S := mem_compl.mp ha
    have hbS : b ∉ S := mem_compl.mp hb
    by_contra hab
    by_cases hyS : y ∈ S
    · let U := S.erase y
      let W : Finset (Fin (2 * p - 3)) := (insert y U)ᶜ
      have hW : W = Q := by simp [W, U, Q, hyS]
      have haW : a ∈ W := hW ▸ ha
      have hbW : b ∈ W := hW ▸ hb
      have hU : U.card = p - 4 := by
        simp only [U, card_erase_of_mem hyS, hS]
        omega
      have hWmem (v : Fin (2 * p - 3)) : v ∈ W ↔ v ∉ U ∧ v ≠ y := by
        simp only [W, mem_compl, mem_insert, not_or]
        tauto
      have hInsert (v : Fin (2 * p - 3)) (hv : v ∈ W) : (insert v U).card = p - 3 := by
        rw [card_insert_of_notMem ((hWmem v).mp hv).1, hU]
        omega
      have hyInsert (v : Fin (2 * p - 3)) (hv : v ∈ W) : y ∉ insert v U := by
        simp [U, Ne.symm ((hWmem v).mp hv).2]
      let entry (v w : Fin (2 * p - 3)) := d (insert w (insert v U))
      let omitted (v : Fin (2 * p - 3)) := m (insert v U)
      have hentrySym : ∀ v ∈ W, ∀ w ∈ W, entry v w = entry w v := by
        intro v _ w _
        simp only [entry, insert_comm]
      have hentryProper : ∀ v ∈ W, ∀ w ∈ W, ∀ z ∈ W,
          w ≠ v → z ≠ v → w ≠ z → entry v w ≠ entry v z := by
        intro v hv w hw z hz hwv hzv hwz
        obtain ⟨hwU, hwy⟩ := (hWmem w).mp hw
        obtain ⟨hzU, hzy⟩ := (hWmem z).mp hz
        exact hd (insert v U) (hInsert v hv) (hyInsert v hv) w (by simp [hwv, hwU])
          z (by simp [hzv, hzU]) hwy hzy hwz
      have homit : ∀ v ∈ W, ∀ w ∈ W, v ≠ w → entry v w ≠ omitted v := by
        intro v hv w hw hvw
        obtain ⟨hwU, hwy⟩ := (hWmem w).mp hw
        exact hm (insert v U) (hInsert v hv) (hyInsert v hv) w (by simp [Ne.symm hvw, hwU]) hwy
      have hWc : W.card = p := by rw [hW, hQ]
      have hinjO := edge p ho W hWc entry hentrySym hentryProper omitted homit
      have hca (v : Fin (2 * p - 3)) (hv : v ∈ W) : c (insert v S) = omitted v := by
        simp [c, omitted, U, hyS, erase_insert_of_ne ((hWmem v).mp hv).2]
      exact hab (hinjO haW hbW ((hca a haW).symm.trans (he.trans (hca b hbW))))
    · by_cases hay : a = y
      · subst a
        simp only [c, mem_insert_self, if_true, erase_insert hyS] at he
        have hyb : y ∉ insert b S := by simp [hab, hyS]
        rw [if_neg hyb] at he
        exact hm S hS hyS b hbS (Ne.symm hab) he.symm
      · by_cases hby : b = y
        · subst b
          have hya : y ∉ insert a S := by simp [Ne.symm hay, hyS]
          exact hm S hS hyS a haS hay (by
            simpa only [c, mem_insert_self, if_true, erase_insert hyS, if_neg hya] using he)
        · have hya : y ∉ insert a S := by simp [Ne.symm hay, hyS]
          have hyb : y ∉ insert b S := by simp [Ne.symm hby, hyS]
          exact hd S hS hyS a haS b hbS hay hby hab (by simpa only [c, if_neg hya, if_neg hyb] using he)
  have hImage : Q.image (fun a => c (insert a S)) = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    rw [card_image_of_injOn hinj, hQ, card_univ, Fintype.card_fin]
  have hi : i ∈ Q.image (fun a => c (insert a S)) := hImage.symm ▸ mem_univ i
  obtain ⟨a, ha, he⟩ := mem_image.mp hi
  exact ⟨a, mem_compl.mp ha, he⟩

set_option maxHeartbeats 500000 in
theorem main : H1 → H2 → OMA.R_Erdos835_erdos_835_variants_johnson_R2.H1 := by
  classical
  rintro ⟨p, hp, hp17, x, y, hxy, d, hd, side, hside, hcross⟩ edge
  let pick (S : Finset (Fin (2 * p - 3))) : Fin p :=
    if h : S.card = p - 3 ∧ x ∉ S ∧ y ∉ S then
      (choose_color hp17 x y hxy d hd side hside S h.1 h.2.1 h.2.2).choose
    else ⟨0, by omega⟩
  have hpick (S : Finset (Fin (2 * p - 3))) (hS : S.card = p - 3) (hx : x ∉ S) (hy : y ∉ S) :
      side S (pick S) = false ∧ ∀ a ∉ S, a ≠ x → a ≠ y → d (insert a S) ≠ pick S := by
    simpa only [pick, dif_pos (And.intro hS (And.intro hx hy))] using
      (choose_color hp17 x y hxy d hd side hside S hS hx hy).choose_spec
  let e (B : Finset (Fin (2 * p - 3))) := if x ∈ B then pick (B.erase x) else d B
  have hOdd : Odd p := hp.odd_of_ne_two (by omega)
  refine ⟨p, hp, hp17, restore_last hp17 hOdd edge y e ?_⟩
  intro S hS hy a ha b hb hay hby hab
  by_cases hx : x ∈ S
  · let U := S.erase x
    have hU : U.card = p - 4 := by simp only [U, card_erase_of_mem hx, hS]; omega
    have hxU : x ∉ U := notMem_erase _ _
    have hyU : y ∉ U := fun h => hy (mem_of_mem_erase h)
    have haU : a ∉ U := fun h => ha (mem_of_mem_erase h)
    have hbU : b ∉ U := fun h => hb (mem_of_mem_erase h)
    have hax : a ≠ x := fun h => ha (h.symm ▸ hx)
    have hbx : b ≠ x := fun h => hb (h.symm ▸ hx)
    have hcard (z : Fin (2 * p - 3)) (hz : z ∉ U) : (insert z U).card = p - 3 := by
      rw [card_insert_of_notMem hz, hU]
      omega
    have hpa := hpick (insert a U) (hcard a haU) (by simp [hax.symm, hxU]) (by simp [hay.symm, hyU])
    have hpb := hpick (insert b U) (hcard b hbU) (by simp [hbx.symm, hxU]) (by simp [hby.symm, hyU])
    have hn : pick (insert a U) ≠ pick (insert b U) := by
      intro heq
      have h := hcross U hU hxU hyU a haU b hbU hax hay hbx hby hab (pick (insert a U))
        hpa.2 (heq ▸ hpb.2)
      exact h (hpa.1.trans (heq ▸ hpb.1.symm))
    simpa only [e, mem_insert_of_mem hx, if_true, erase_insert_of_ne hax, erase_insert_of_ne hbx, U] using hn
  · by_cases hax : a = x
    · subst a
      have hxb : x ∉ insert b S := by simp [hab, hx]
      simpa only [e, mem_insert_self, if_true, erase_insert hx, if_neg hxb, ne_comm] using
        (hpick S hS hx hy).2 b hb hab.symm hby
    · by_cases hbx : b = x
      · subst b
        have hxa : x ∉ insert a S := by simp [Ne.symm hax, hx]
        simpa only [e, mem_insert_self, if_true, erase_insert hx, if_neg hxa] using
          (hpick S hS hx hy).2 a ha hax hay
      · have hxa : x ∉ insert a S := by simp [Ne.symm hax, hx]
        have hxb : x ∉ insert b S := by simp [Ne.symm hbx, hx]
        simpa only [e, if_neg hxa, if_neg hxb] using hd S hS hx hy a ha b hb hax hay hbx hby hab

end OMA.R_Erdos835_erdos_835_variants_johnson_R2_H1_R1
