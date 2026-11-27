import OMAStatements.S_mo_312603
import Mathlib

open Set MeasureTheory Filter
open scoped ENNReal
namespace ThreeSites
open OMA.S_mo_312603

abbrev M := Bool × Bool × Bool

def num (p : M) := p.1.toNat + 2 * p.2.1.toNat + 4 * p.2.2.toNat

def win (p q : M) : M :=
  let a := num p
  let b := num q
  if a = 4 ∨ a = 5 then
    if b = 2 ∨ b = 6 then (false,true,true) else (true,false,true)
  else if a = 2 ∨ a = 6 then
    if b = 4 ∨ b = 5 ∨ b = 6 ∨ (a = 6 ∧ b = 2) then (false,true,true)
    else (true,true,false)
  else if b = 4 ∨ b = 5 then (true,false,true) else (true,true,false)

def count (p : M) := p.1.toNat + p.2.1.toNat + p.2.2.toNat
def both (p q : M) : M := (p.1 && q.1, p.2.1 && q.2.1, p.2.2 && q.2.2)
def score (p q : M) := count (both p q)

lemma finite_rules : ∀ a b x : M,
    count (win a b) = 2 ∧ count a ≤ score a (win a b) + score a (win a b) ∧
    count b ≤ score b (win a b) + score b (win a b) ∧
    score a (win x b) ≤ score a (win a b) ∧ score b (win a x) ≤ score b (win a b) := by
  decide

inductive Step {α : Type} : (ℝ → α) → Prop
  | const (v : α) : Step (fun _ => v)
  | cut (k : ℝ) {f g : ℝ → α} : Step f → Step g →
      Step (fun x => if x ≤ k then f x else g x)

lemma Step.map {α β : Type} (u : α → β) {f : ℝ → α} (hf : Step f) :
    Step (fun x => u (f x)) := by
  induction hf with
  | const v => exact .const _
  | cut k hf hg il ir =>
    convert Step.cut k il ir using 1
    funext x
    by_cases hx : x ≤ k <;> simp [hx]

lemma Step.map₂ {α β γ : Type} (u : α → β → γ) {f : ℝ → α} {g : ℝ → β}
    (hf : Step f) (hg : Step g) : Step (fun x => u (f x) (g x)) := by
  induction hf with
  | const v => exact hg.map (u v)
  | cut k hf hr il ir =>
    convert Step.cut k il ir using 1
    funext x
    by_cases hx : x ≤ k <;> simp [hx]

lemma Step.shift {α : Type} {f : ℝ → α} (hf : Step f) (d : ℝ) :
    Step (fun x => f (x+d)) := by
  induction hf with
  | const v => exact .const _
  | cut k hf hg il ir =>
    convert Step.cut (k-d) il ir using 1
    funext x
    simp only [le_sub_iff_add_le]

lemma Step.meas {α : Type} [MeasurableSpace α] {f : ℝ → α} (hf : Step f) : Measurable f := by
  induction hf with
  | const v => exact measurable_const
  | cut k hf hg il ir => exact Measurable.ite measurableSet_Iic il ir

def supp (f : ℝ → Bool) : Set ℝ := {x | f x = true}

lemma input {s : Set ℝ} (hs : Piece s) :
    ∃ f : ℝ → Bool, Step f ∧ supp f =ᵐ[volume] s := by
  induction hs with
  | @interval a b ha hab hb =>
    refine ⟨fun x => if x ≤ a then false else if x ≤ b then true else false,
      .cut a (.const _) (.cut b (.const _) (.const _)), ?_⟩
    have h : supp (fun x => if x ≤ a then false else if x ≤ b then true else false) = Ioc a b := by
      ext x
      simp [supp, mem_Ioc, not_le]
    rw [h]
    exact Ioc_ae_eq_Icc
  | union hs ht is it =>
    obtain ⟨f,hf,ef⟩ := is
    obtain ⟨g,hg,eg⟩ := it
    refine ⟨_,hf.map₂ (· || ·) hg, ?_⟩
    simpa [supp, Set.union_def] using ef.union eg

lemma bounds {s : Set ℝ} (hs : Piece s) : s ⊆ Icc 0 1 := by
  induction hs with
  | interval ha hab hb => exact Icc_subset_Icc ha hb
  | union hs ht il ir => exact union_subset il ir

lemma positive {s : Set ℝ} (hs : Piece s) : 0 < volume s := by
  induction hs with
  | interval ha hab hb => simpa [Real.volume_Icc] using ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  | union hs ht il ir => exact il.trans_le (measure_mono subset_union_left)

def Realized (s : Set ℝ) := ∃ t : Set ℝ, (t = ∅ ∨ Piece t) ∧ s =ᵐ[volume] t

lemma realized_union {s t : Set ℝ} (hs : Realized s) (ht : Realized t) : Realized (s ∪ t) := by
  obtain ⟨u,hu,eu⟩ := hs
  obtain ⟨v,hv,ev⟩ := ht
  refine ⟨u ∪ v, ?_, eu.union ev⟩
  rcases hu with rfl | hu
  · simpa using hv
  rcases hv with rfl | hv
  · simpa using Or.inr hu
  exact Or.inr (.union hu hv)

lemma realize {f : ℝ → Bool} (hf : Step f) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) : Realized (Ioc a b ∩ supp f) := by
  induction hf generalizing a b with
  | const v =>
    cases v
    · refine ⟨∅, Or.inl rfl, ?_⟩
      simp [supp]
    · refine ⟨Icc a b, Or.inr (.interval ha hab hb), ?_⟩
      simpa [supp] using (Ioc_ae_eq_Icc (a := a) (b := b) (μ := volume))
  | @cut k f g hf hg il ir =>
    by_cases hka : k ≤ a
    · convert ir ha hab hb using 1
      ext x
      simp only [mem_inter_iff, mem_Ioc, supp, mem_ofPred_eq]
      by_cases hx : a < x ∧ x ≤ b
      · simp [hx, not_le.mpr (lt_of_le_of_lt hka hx.1)]
      · simp [hx]
    by_cases hbk : b ≤ k
    · convert il ha hab hb using 1
      ext x
      simp only [mem_inter_iff, mem_Ioc, supp, mem_ofPred_eq]
      by_cases hx : a < x ∧ x ≤ b
      · simp [hx, hx.2.trans hbk]
      · simp [hx]
    have hak : a < k := lt_of_not_ge hka
    have hkb : k < b := lt_of_not_ge hbk
    convert realized_union (il ha hak (hkb.le.trans hb)) (ir (ha.trans hak.le) hkb hb) using 1
    ext x
    simp only [mem_union, mem_inter_iff, mem_Ioc, supp, mem_ofPred_eq]
    split <;> grind

noncomputable def model (A : Report) := (input A.2).choose
lemma model_step (A : Report) : Step (model A) := (input A.2).choose_spec.1
lemma model_ae (A : Report) : supp (model A) =ᵐ[volume] A.1 := (input A.2).choose_spec.2

noncomputable abbrev h : ℝ := 1/3
noncomputable def mask (f : ℝ → Bool) (x : ℝ) : M := (f x, f (x+h), f (x+2*h))
lemma mask_step {f : ℝ → Bool} (hf : Step f) : Step (mask f) :=
  hf.map₂ Prod.mk ((hf.shift h).map₂ Prod.mk (hf.shift (2*h)))

noncomputable def tile (v : ℝ → M) (y : ℝ) : Bool :=
  if y ≤ h then (v y).1 else if y ≤ 2*h then (v (y-h)).2.1 else (v (y-2*h)).2.2

lemma tile_step {v : ℝ → M} (hv : Step v) : Step (tile v) := by
  exact .cut h (hv.map Prod.fst) (.cut (2*h)
    (by simpa [sub_eq_add_neg] using (hv.shift (-h)).map (fun p : M => p.2.1))
    (by simpa [sub_eq_add_neg] using (hv.shift (-(2*h))).map (fun p : M => p.2.2)))

lemma tile_mask (v : ℝ → M) {x : ℝ} (hx : x ∈ Ioc 0 h) : mask (tile v) x = v x := by
  obtain ⟨hx0,hx1⟩ := hx
  have h1 : ¬ x+h ≤ h := by linarith
  have h2 : x+h ≤ 2*h := by linarith
  have h3 : ¬ x+2*h ≤ h := by dsimp [h] at *; linarith
  have h4 : ¬ x+2*h ≤ 2*h := by linarith
  simp only [mask, tile, if_pos hx1, if_neg h1, if_pos h2, if_neg h3, if_neg h4,
    add_sub_cancel_right, Prod.mk.eta]

noncomputable def output (f g : ℝ → Bool) := tile (fun x => win (mask f x) (mask g x))
lemma output_step {f g : ℝ → Bool} (hf : Step f) (hg : Step g) : Step (output f g) :=
  tile_step ((mask_step hf).map₂ win (mask_step hg))

def domain := Ioc (0 : ℝ) 1
noncomputable def mass (f : ℝ → Bool) := volume (domain ∩ supp f)
noncomputable def weight (b : Bool) : ℝ≥0∞ := b.toNat

lemma supp_meas {f : ℝ → Bool} (hf : Step f) : MeasurableSet (supp f) :=
  hf.meas (measurableSet_singleton true)

lemma mass_integral {f : ℝ → Bool} (hf : Step f) :
    mass f = ∫⁻ y in domain, weight (f y) := by
  have eqf : (fun y => weight (f y)) = (supp f).indicator (1 : ℝ → ℝ≥0∞) := by
    funext y
    cases hfy : f y <;> simp [indicator, supp, hfy, weight]
  rw [eqf, lintegral_indicator_one (supp_meas hf), Measure.restrict_apply (supp_meas hf)]
  simp [mass, inter_comm]

lemma shift_integral (u : ℝ → ℝ≥0∞) (d : ℝ) :
    (∫⁻ x in Ioc 0 h, u (x+d)) = ∫⁻ y in Ioc d (h+d), u y := by
  have hp := (measurePreserving_add_right (volume : Measure ℝ) d).restrict_preimage_emb
    (measurableEmbedding_addRight d) (Ioc d (h+d))
  have he : (fun x : ℝ => x+d) ⁻¹' Ioc d (h+d) = Ioc 0 h := by
    ext x
    simp
  rw [he] at hp
  exact hp.lintegral_comp_emb (measurableEmbedding_addRight d) u

lemma add_split (u : ℝ → ℝ≥0∞) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫⁻ y in Ioc a c, u y) = (∫⁻ y in Ioc a b, u y) + ∫⁻ y in Ioc b c, u y := by
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc, lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]

lemma fiber {f : ℝ → Bool} (hf : Step f) :
    mass f = ∫⁻ x in Ioc 0 h, (count (mask f x) : ℝ≥0∞) := by
  let u := fun y => weight (f y)
  have hL : Measurable u := (hf.map weight).meas
  have hM : Measurable (fun x => u (x+h)) := ((hf.shift h).map weight).meas
  have hcount (x : ℝ) : (count (mask f x) : ℝ≥0∞) = u x + u (x+h) + u (x+2*h) := by
    simp [u,weight,count,mask]
  simp_rw [hcount]
  have hu12 : Measurable (fun x => u x + u (x+h)) := hL.add hM
  rw [lintegral_add_left hu12 (fun x => u (x+2*h)), lintegral_add_left hL (fun x => u (x+h)),
    shift_integral u h, shift_integral u (2*h), mass_integral hf]
  change (∫⁻ y in Ioc 0 1, u y) = _
  have he : h+h = 2*h := by ring
  have he' : h+2*h = 1 := by norm_num [h]
  rw [he,he',add_split u (a := 0) (b := 2*h) (c := 1) (by norm_num [h]) (by norm_num [h]),
    add_split u (a := 0) (b := h) (c := 2*h) (by norm_num [h]) (by norm_num [h])]

lemma mass_le {f g : ℝ → Bool} (hf : Step f) (hg : Step g)
    (H : ∀ x ∈ Ioc 0 h, count (mask f x) ≤ count (mask g x)) : mass f ≤ mass g := by
  rw [fiber hf, fiber hg]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioc (a := 0) (b := h))]
    with x hx
  exact_mod_cast H x hx

lemma mass_le_twice {f g : ℝ → Bool} (hf : Step f) (hg : Step g)
    (H : ∀ x ∈ Ioc 0 h, count (mask f x) ≤ count (mask g x) + count (mask g x)) :
    mass f ≤ mass g + mass g := by
  rw [fiber hf, fiber hg, ← lintegral_add_left ((mask_step hg).map
    (fun p => (count p : ℝ≥0∞))).meas]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioc (a := 0) (b := h))]
    with x hx
  exact_mod_cast H x hx

lemma fixed_mass {f g : ℝ → Bool} (hf : Step f) (hg : Step g) :
    mass (output f g) = ENNReal.ofReal (2/3) := by
  rw [fiber (output_step hf hg)]
  calc
    _ = ∫⁻ _x in Ioc (0:ℝ) h, (2 : ℝ≥0∞) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioc (a := 0) (b := h))]
        with x hx
      rw [output, tile_mask _ hx, (finite_rules (mask f x) (mask g x) (mask f x)).1]
      norm_num
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
      have he : (2:ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
      rw [he, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring

def meet (f g : ℝ → Bool) := fun x => f x && g x
lemma meet_step {f g : ℝ → Bool} (hf : Step f) (hg : Step g) : Step (meet f g) :=
  hf.map₂ (· && ·) hg

lemma meet_mask (f g : ℝ → Bool) (x : ℝ) : mask (meet f g) x = both (mask f x) (mask g x) := rfl

lemma utility_mask (f g k : ℝ → Bool) {x : ℝ} (hx : x ∈ Ioc 0 h) :
    count (mask (meet f (output g k)) x) = score (mask f x) (win (mask g x) (mask k x)) := by
  rw [meet_mask,output,tile_mask _ hx]
  rfl

lemma input_mass (A : Report) : mass (model A) = volume A.1 := by
  have he : (domain ∩ supp (model A) : Set ℝ) =ᵐ[volume] (Icc 0 1 ∩ A.1 : Set ℝ) :=
    Ioc_ae_eq_Icc.inter (model_ae A)
  rw [inter_eq_right.mpr (bounds A.2)] at he
  exact measure_congr he

lemma winner_exists (A B : Report) :
    ∃ S : Report, (domain ∩ supp (output (model A) (model B)) : Set ℝ) =ᵐ[volume] S.1 := by
  obtain ⟨s,hs,he⟩ := realize (output_step (model_step A) (model_step B))
    (a := 0) (b := 1) (by norm_num) (by norm_num) (by norm_num)
  rcases hs with rfl | hs
  · have hh := measure_congr he
    change mass (output (model A) (model B)) = volume (∅ : Set ℝ) at hh
    rw [fixed_mass (model_step A) (model_step B), measure_empty] at hh
    norm_num at hh
  exact ⟨⟨s,hs⟩,he⟩

noncomputable def F (A B : Report) : Report := (winner_exists A B).choose
lemma winner_ae (A B : Report) :
    (domain ∩ supp (output (model A) (model B)) : Set ℝ) =ᵐ[volume] (F A B).1 :=
  (winner_exists A B).choose_spec

lemma utility (A B C : Report) :
    volume (A.1 ∩ (F B C).1) = mass (meet (model A) (output (model B) (model C))) := by
  have H := measure_congr ((model_ae A).inter (winner_ae B C))
  rw [← H]
  unfold mass
  congr 1
  ext x
  simp [supp,meet,and_left_comm]

end ThreeSites

open ThreeSites OMA.S_mo_312603

theorem OMA.solution : type_of% @OMA.S_mo_312603.main := by
  refine ⟨F, fun A B => ⟨?_, ?_, ?_, fun X => ⟨?_, ?_⟩⟩⟩
  · intro hw
    have he := measure_congr (winner_ae A B)
    change mass (output (model A) (model B)) = _ at he
    rw [fixed_mass (model_step A) (model_step B), hw, Real.volume_Icc] at he
    norm_num at he
  · rw [utility]
    apply lt_of_not_ge
    intro hn
    have hz := le_zero_iff.mp hn
    have H := mass_le_twice (model_step A) (meet_step (model_step A)
      (output_step (model_step A) (model_step B))) (fun x hx => by
        rw [utility_mask _ _ _ hx]
        exact (finite_rules _ _ (mask (model A) x)).2.1)
    rw [input_mass, hz, add_zero] at H
    exact (positive A.2).not_ge H
  · rw [utility]
    apply lt_of_not_ge
    intro hn
    have hz := le_zero_iff.mp hn
    have H := mass_le_twice (model_step B) (meet_step (model_step B)
      (output_step (model_step A) (model_step B))) (fun x hx => by
        rw [utility_mask _ _ _ hx]
        exact (finite_rules _ _ (mask (model A) x)).2.2.1)
    rw [input_mass, hz, add_zero] at H
    exact (positive B.2).not_ge H
  · rw [utility,utility]
    apply mass_le (meet_step (model_step A) (output_step (model_step X) (model_step B)))
      (meet_step (model_step A) (output_step (model_step A) (model_step B)))
    intro x hx
    rw [utility_mask _ _ _ hx,utility_mask _ _ _ hx]
    exact (finite_rules _ _ _).2.2.2.1
  · rw [utility,utility]
    apply mass_le (meet_step (model_step B) (output_step (model_step A) (model_step X)))
      (meet_step (model_step B) (output_step (model_step A) (model_step B)))
    intro x hx
    rw [utility_mask _ _ _ hx,utility_mask _ _ _ hx]
    exact (finite_rules _ _ _).2.2.2.2

