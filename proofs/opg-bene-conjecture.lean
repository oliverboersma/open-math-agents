import OMAStatements.S_opg_bene_conjecture
import Mathlib

namespace BenesDisproof

open OMA.S_opg_bene_conjecture

private abbrev V := Bool × Fin 5
private abbrev E := V × Fin 5

private def src (e : E) : V := e.1

private def turn (b : Bool) (i : Fin 5) : Bool :=
  if i = 0 then !b else b

private theorem turn_turn (b : Bool) (i : Fin 5) : turn (turn b i) i = b := by
  by_cases h : i = 0 <;> simp [turn, h]

private def tgt (e : E) : V := (turn e.1.1 e.1.2, e.2)

private def φ : Equiv.Perm E where
  toFun e := ((turn e.1.1 e.2, e.2), e.1.2)
  invFun e := ((turn e.1.1 e.1.2, e.2), e.1.2)
  left_inv := by
    rintro ⟨⟨b, i⟩, j⟩
    change ((turn (turn b j) j, i), j) = ((b, i), j)
    rw [turn_turn]
  right_inv := by
    rintro ⟨⟨b, i⟩, j⟩
    change ((turn (turn b i) i, i), j) = ((b, i), j)
    rw [turn_turn]

private theorem tgt_phi (e : E) : tgt (φ e) = src e := by
  rcases e with ⟨⟨b, i⟩, j⟩
  change (turn (turn b j) j, i) = (b, i)
  rw [turn_turn]

private theorem src_phi_symm (e : E) : src (φ.symm e) = tgt e := rfl

private def block (v : V) : Finset E :=
  Finset.univ.filter (fun e => v = src e)

private theorem mem_block {e : E} {v : V} : e ∈ block v ↔ src e = v := by
  simp only [block, Finset.mem_filter, Finset.mem_univ, true_and]
  exact eq_comm

private def u : Finpartition (Finset.univ : Finset E) :=
  letI : DecidableRel (Setoid.ker src).r :=
    fun a b => inferInstanceAs (Decidable (src a = src b))
  Finpartition.ofSetoid (Setoid.ker src)

private theorem part_is_block {P : Finset E} (hP : P ∈ u.parts) :
    ∃ v : V, P = block v := by
  change P ∈ Finset.univ.image (fun e : E => block (src e)) at hP
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hP
  exact ⟨src e, rfl⟩

private theorem uniform : IsUniform u := by
  refine ⟨5, ?_⟩
  intro P hP
  obtain ⟨v, rfl⟩ := part_is_block hP
  let emb : Fin 5 ↪ E := ⟨fun j => (v, j), fun _ _ h => congrArg Prod.snd h⟩
  have hb : block v = Finset.univ.map emb := by
    ext e
    constructor
    · intro he
      exact Finset.mem_map.mpr
        ⟨e.2, Finset.mem_univ _, Prod.ext (mem_block.mp he).symm rfl⟩
    · intro he
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp he
      exact mem_block.mpr rfl
  simp [hb]

private theorem incoming {e : E} {v : V} (he : e ∈ (block v).image φ) :
    tgt e = v := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  exact (tgt_phi a).trans (mem_block.mp ha)

private theorem trivial_inf : InfImageTrivial u φ := by
  intro P hP Q hQ
  obtain ⟨v, rfl⟩ := part_is_block hP
  obtain ⟨w, rfl⟩ := part_is_block hQ
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨he₁, he₂⟩ := Finset.mem_inter.mp he
  obtain ⟨hf₁, hf₂⟩ := Finset.mem_inter.mp hf
  exact Prod.ext ((mem_block.mp he₁).trans (mem_block.mp hf₁).symm)
    (congrArg (fun v : V => v.2) ((incoming he₂).trans (incoming hf₂).symm))

private theorem swap_mem {x y : E} (h : src x = src y) :
    Equiv.swap x y ∈ blockStabilizer u := by
  intro P hP e he
  obtain ⟨v, rfl⟩ := part_is_block hP
  apply mem_block.mpr
  have he' := mem_block.mp he
  rw [Equiv.swap_apply_def]
  split
  · rename_i h₁
    exact h.symm.trans (h₁ ▸ he')
  · split
    · rename_i h₂
      exact h.trans (h₂ ▸ he')
    · exact he'

private theorem one_step (x y : E) (h : src x = tgt y) :
    ∃ g ∈ coset u φ, g x = y := by
  refine ⟨φ * Equiv.swap x (φ.symm y), ⟨_, swap_mem (h.trans (src_phi_symm y).symm), rfl⟩, ?_⟩
  simp [Equiv.Perm.mul_apply]

private theorem two_edges (v w : V) :
    ∃ e f : E, src e = v ∧ tgt e = src f ∧ tgt f = w := by
  rcases v with ⟨b, i⟩
  rcases w with ⟨c, j⟩
  let k : Fin 5 := if turn b i = c then 1 else 0
  refine ⟨((b, i), k), ((turn b i, k), j), rfl, rfl, Prod.ext ?_ rfl⟩
  change turn (turn b i) (if turn b i = c then 1 else 0) = c
  generalize turn b i = d
  cases d <;> cases c <;> decide

private theorem transitive : IsTransitive (setPow (coset u φ) 3) := by
  intro x y
  obtain ⟨e, f, he, hef, hf⟩ := two_edges (tgt y) (src x)
  obtain ⟨a, ha, ha'⟩ := one_step x f hf.symm
  obtain ⟨b, hb, hb'⟩ := one_step f e hef.symm
  obtain ⟨c, hc, hc'⟩ := one_step e y he
  refine ⟨c * (b * a), ⟨c, hc, b * a, ⟨b, hb, a, ha, rfl⟩, rfl⟩, ?_⟩
  simp only [Equiv.Perm.mul_apply, ha', hb', hc']

private theorem step_target {g : Equiv.Perm E} (hg : g ∈ coset u φ) (e : E) :
    tgt (g e) = src e := by
  obtain ⟨σ, hσ, rfl⟩ := hg
  have hm : e ∈ block (src e) := mem_block.mpr rfl
  have hp : block (src e) ∈ u.parts :=
    Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  exact (tgt_phi (σ e)).trans (mem_block.mp (hσ _ hp e hm))

private theorem crossing {g : Equiv.Perm E} (hg : g ∈ coset u φ) {e : E}
    (h₀ : (src e).1 = false) (h₁ : (src (g e)).1 ≠ false) :
    src (g e) = (true, 0) := by
  have hb : (src (g e)).1 = true := by simpa using h₁
  have ht : (tgt (g e)).1 = false := (congrArg Prod.fst (step_target hg e)).trans h₀
  change turn (src (g e)).1 (src (g e)).2 = false at ht
  apply Prod.ext hb
  by_contra hn
  simp [turn, hn, hb] at ht

private def flip : Equiv.Perm E where
  toFun e := ((!e.1.1, e.1.2), e.2)
  invFun e := ((!e.1.1, e.1.2), e.2)
  left_inv := by rintro ⟨⟨b, i⟩, j⟩; cases b <;> rfl
  right_inv := by rintro ⟨⟨b, i⟩, j⟩; cases b <;> rfl

private def start (p : Fin 5 × Fin 5) : E := ((false, p.1), p.2)

-- The target of the fifth edge fixes the source reached after four steps.
private theorem missing : φ * flip ∉ setPow (coset u φ) 5 := by
  intro h
  obtain ⟨a₅, h₅, _, ⟨a₄, h₄, _, ⟨a₃, h₃, _, ⟨a₂, h₂, a₁, h₁, rfl⟩, rfl⟩,
    rfl⟩, hprod⟩ := h
  let route : Fin 4 → Equiv.Perm E :=
    ![a₁, a₂ * a₁, a₃ * (a₂ * a₁), a₄ * (a₃ * (a₂ * a₁))]
  have hend (p : Fin 5 × Fin 5) : (src (route 3 (start p))).1 = true := by
    have ht := step_target h₅ (route 3 (start p))
    change tgt ((a₅ * (a₄ * (a₃ * (a₂ * a₁)))) (start p)) = _ at ht
    rw [← hprod] at ht
    exact congrArg Prod.fst (ht.symm.trans (tgt_phi (flip (start p))))
  have hit (p : Fin 5 × Fin 5) : ∃ t : Fin 4, src (route t (start p)) = (true, 0) := by
    by_cases h0 : (src (route 0 (start p))).1 = false
    · by_cases h1 : (src (route 1 (start p))).1 = false
      · by_cases h2 : (src (route 2 (start p))).1 = false
        · exact ⟨3, crossing h₄ h2 (fun hfalse => Bool.noConfusion ((hend p).symm.trans hfalse))⟩
        · exact ⟨2, crossing h₃ h1 h2⟩
      · exact ⟨1, crossing h₂ h0 h1⟩
    · exact ⟨0, crossing h₁ rfl h0⟩
  choose time htime using hit
  let code (p : Fin 5 × Fin 5) : Fin 4 × Fin 5 :=
    (time p, (route (time p) (start p)).2)
  have hinj : Function.Injective code := by
    intro p q hpq
    have ht : time p = time q := congrArg Prod.fst hpq
    have he : route (time p) (start p) = route (time p) (start q) := by
      apply Prod.ext
      · change src (route (time p) (start p)) = src (route (time p) (start q))
        rw [htime p, ht, htime q]
      · have hs : (route (time p) (start p)).2 = (route (time q) (start q)).2 :=
          congrArg (fun c : Fin 4 × Fin 5 => c.2) hpq
        simpa only [ht] using hs
    have hs := (route (time p)).injective he
    exact Prod.ext (congrArg (fun e : E => e.1.2) hs) (congrArg (fun e : E => e.2) hs)
  have hc := Fintype.card_le_of_injective code hinj
  norm_num [Fintype.card_prod] at hc

theorem counterexample : ∃ (u' : Finpartition (Finset.univ : Finset E)) (p : Equiv.Perm E),
    IsUniform u' ∧ InfImageTrivial u' p ∧ IsTransitive (setPow (coset u' p) 3) ∧
      setPow (coset u' p) 5 ≠ Set.univ := by
  refine ⟨u, φ, uniform, trivial_inf, transitive, ?_⟩
  intro h
  exact missing (h ▸ Set.mem_univ (φ * flip))

end BenesDisproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_bene_conjecture.main) := by
  intro h
  obtain ⟨u, p, hu, hp, ht, hn⟩ := BenesDisproof.counterexample
  exact hn (h _ u p 3 hu hp (by decide) ht)