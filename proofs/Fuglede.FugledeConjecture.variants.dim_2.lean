import FormalConjectures.Wikipedia.Fuglede

-- Problem: Fuglede's conjecture — dim 2
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/Fuglede.lean:59 (declaration Fuglede.FugledeConjecture.variants.dim_2)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Refutation, following T. Zhang, Both directions of Fuglede's conjecture fail in dimension two,
-- arXiv:2607.15632. We formalize the direction: there is a bounded spectral set in the plane that
-- does not tile by translations. The set is A[60] + (0,1]^2, a union of 216000 unit squares, where
-- A is the 60-point set of Z_12 x Z_12 x Z_5 (= Z_60 x Z_12) of the paper.
--   Part 1: A does not tile the finite group (no common tiling complement argument).
--   Part 2-3: explicit orthogonal spectrum of A and of its lift to Z^2.
--   Part 4: the lift does not tile Z^2 (counting argument of Matolcsi).
--   Part 5: the planar set does not tile R^2.
--   Part 6-9: the planar set is spectral (orthogonality; completeness via the Fourier basis of the
--   2-torus and an orthogonal-matrix argument).

-- ===== Part 1 =====
section

namespace FG

abbrev H := ZMod 12 × ZMod 12
abbrev K := H × ZMod 5

def V0 : Finset H := Finset.univ.filter (fun h => h.1 = 0)
def V1 : Finset H := Finset.univ.filter (fun h => h.1 = h.2)
def V2 : Finset H :=
  Finset.univ.filter (fun h => ∃ m : ZMod 12, h = (4 * m, 2 * m) ∨ h = (4 * m + 1, 2 * m + 2))

def VL (t : ZMod 5) : Finset H := if t = 3 then V2 else if t = 4 then V1 else V0

def At : Set K := {a | a.1 ∈ VL a.2}

/-- `A ⊕ B = G` (direct tiling). -/
def Tiles {G : Type*} [AddCommGroup G] (A B : Set G) : Prop :=
  ∀ g, ∃! p : G × G, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = g

lemma tiles_uniq {G : Type*} [AddCommGroup G] {A B : Set G} (hT : Tiles A B)
    {a a' b b' : G} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (h : a + b = a' + b') : a = a' ∧ b = b' := by
  have := (hT (a + b)).unique (y₁ := (a, b)) (y₂ := (a', b')) ⟨ha, hb, rfl⟩ ⟨ha', hb', h.symm⟩
  simpa [Prod.ext_iff] using this

lemma mem_At {a : K} : a ∈ At ↔ a.1 ∈ VL a.2 := Iff.rfl

lemma VL4 : VL 4 = V1 := by unfold VL; rw [if_neg (by decide), if_pos rfl]
lemma VL3 : VL 3 = V2 := by unfold VL; rw [if_pos rfl]
lemma VL_V0 {t : ZMod 5} (h3 : t ≠ 3) (h4 : t ≠ 4) : VL t = V0 := by
  unfold VL; rw [if_neg h3, if_neg h4]

lemma diff_At (h : H) (d : ZMod 5) (hd : d ≠ 0) :
    ∃ a ∈ At, ∃ a' ∈ At, a = a' + (h, d) := by
  obtain ⟨x, y⟩ := h
  have m1 : ∀ x : ZMod 12, ((-x, -x), (4 : ZMod 5)) ∈ At := fun x => by
    rw [mem_At, VL4]; simp [V1]
  have m0 : ∀ (u : ZMod 12) (t : ZMod 5), t ≠ 3 → t ≠ 4 → ((0, u), t) ∈ At := fun u t h3 h4 => by
    rw [mem_At, VL_V0 h3 h4]; simp [V0]
  fin_cases d
  · exact absurd rfl hd
  · exact ⟨((0, y - x), 0), m0 (y - x) 0 (by decide) (by decide), ((-x, -x), 4), m1 x,
      by ext <;> simp <;> first | rfl | decide | ring1⟩
  · exact ⟨((0, y - x), 1), m0 (y - x) 1 (by decide) (by decide), ((-x, -x), 4), m1 x,
      by ext <;> simp <;> first | rfl | decide | ring1⟩
  · exact ⟨((0, y - x), 2), m0 (y - x) 2 (by decide) (by decide), ((-x, -x), 4), m1 x,
      by ext <;> simp <;> first | rfl | decide | ring1⟩
  · refine ⟨((x, x), 4), ?_, ((0, x - y), 0), m0 (x - y) 0 (by decide) (by decide),
      by ext <;> simp <;> first | rfl | decide | ring1⟩
    have := m1 (-x); rwa [neg_neg] at this

lemma same_layer {B : Set K} (hT : Tiles At B) {b b' : K} (hb : b ∈ B) (hb' : b' ∈ B) :
    b.2 = b'.2 := by
  by_contra hne
  obtain ⟨a, ha, a', ha', hdiff⟩ := diff_At (b'.1 - b.1) (b'.2 - b.2) (sub_ne_zero.mpr (Ne.symm hne))
  have key : a + b = a' + b' := by
    rw [hdiff]; ext <;> simp <;> abel
  have := (tiles_uniq hT ha ha' hb hb' key).2
  exact hne (by rw [this])

lemma mem_V2 {h : H} : h ∈ V2 ↔ ∃ m : ZMod 12, h = (4 * m, 2 * m) ∨ h = (4 * m + 1, 2 * m + 2) := by
  simp [V2]

def c4 : ZMod 12 →+* ZMod 4 := ZMod.castHom (by norm_num) (ZMod 4)
def c6 : ZMod 12 →+* ZMod 6 := ZMod.castHom (by norm_num) (ZMod 6)
def phi (h : H) : ZMod 4 × ZMod 6 := (c4 h.1, c6 (h.1 + h.2))

lemma phi_sub (h h' : H) : phi (h - h') = phi h - phi h' := by
  ext
  · simp [phi]
  · simp only [phi, Prod.snd_sub, Prod.fst_sub, ← map_sub]; congr 1; ring

set_option maxRecDepth 20000 in
lemma ker_phi : ∀ h : H, phi h = 0 → ∃ m : ZMod 12, h = (4 * m, 2 * m) := by decide

lemma phi_V2 : ∀ m : ZMod 12, phi (4 * m, 2 * m) = 0 ∧ phi (4 * m + 1, 2 * m + 2) = (1, 3) := by
  decide

lemma phi_surj : ∀ w : ZMod 4 × ZMod 6, ∃ h : H, phi h = w := by decide

lemma phi_c : phi (1, 2) = (1, 3) := by decide

lemma ne_4m1 : ∀ m : ZMod 12, 4 * m + 1 ≠ 0 := by decide

lemma par6 : ∀ a b : ZMod 12, (c6 (a + b)).val % 2 = 0 ↔ (a - b).val % 2 = 0 := by decide

lemma fiber3 : ∀ r : ZMod 4, (Finset.univ.filter (fun x : ZMod 12 => c4 x = r)).card = 3 := by decide

lemma even6 : (Finset.univ.filter (fun z : ZMod 12 => z.val % 2 = 0)).card = 6 := by decide

lemma comb' : ∀ S1 : Finset (ZMod 6), S1.card = 3 →
    (S1.filter (fun s => s.val % 2 = 0)).card =
      ((Finset.univ.filter (fun s => s + 3 ∉ S1)).filter (fun s => s.val % 2 = 0)).card := by
  decide

lemma comb (S1 S2 : Finset (ZMod 6)) (h3 : S1.card = 3) (hx : ∀ s, s ∈ S1 ↔ ¬ (s - 3 ∈ S2)) :
    (S1.filter (fun s => s.val % 2 = 0)).card = (S2.filter (fun s => s.val % 2 = 0)).card := by
  have : S2 = Finset.univ.filter (fun s => s + 3 ∉ S1) := by
    ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hx (s + 3)]; simp
  rw [this]; exact comb' S1 h3

theorem no_common (C : Set H) (h0 : Tiles (V0 : Set H) C) (h1 : Tiles (V1 : Set H) C)
    (h2 : Tiles (V2 : Set H) C) : False := by
  have ex : ∀ x : ZMod 12, ∃ y, (x, y) ∈ C := by
    intro x
    obtain ⟨⟨v, c⟩, ⟨hv, hc, hvc⟩, -⟩ := h0 (x, 0)
    have hv1 : v.1 = 0 := by simpa [V0] using hv
    refine ⟨c.2, ?_⟩
    have : c.1 = x := by
      have := congrArg Prod.fst hvc; simp only [Prod.fst_add, hv1, zero_add] at this; exact this
    rw [← this]; exact hc
  choose g hg using ex
  have uniq : ∀ c ∈ C, c = (c.1, g c.1) := by
    intro c hc
    have := tiles_uniq h0 (a := (0, c.2 - g c.1)) (a' := 0) (b := (c.1, g c.1)) (b' := c)
      (by simp [V0]) (by simp [V0]) (hg _) hc (by ext <;> simp)
    exact this.2.symm
  have inj : Function.Injective (fun x => x - g x) := by
    intro x x' hxx
    simp only at hxx
    have := tiles_uniq h1 (a := (x - x', x - x')) (a' := 0) (b := (x', g x')) (b' := (x, g x))
      (by simp [V1]) (by simp [V1]) (hg _) (hg _)
      (by ext <;> simp <;> linear_combination hxx)
    exact (congrArg Prod.fst this.2).symm
  have count6 : (Finset.univ.filter (fun x => (x - g x).val % 2 = 0)).card = 6 := by
    rw [← even6]
    apply Finset.card_nbij (fun x => x - g x)
    · intro a ha; simpa using ha
    · intro a _ b _ hab; exact inj hab
    · intro z hz
      obtain ⟨x, hx⟩ := (Finite.injective_iff_bijective.mp inj).2 z
      refine ⟨x, ?_, hx⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
      simp only at hx; rw [hx]; exact hz
  have mem0 : (0 : H) ∈ (V2 : Set H) := by
    rw [Finset.mem_coe, mem_V2]; exact ⟨0, Or.inl (by ext <;> simp)⟩
  have injC : ∀ x x', phi (x, g x) = phi (x', g x') → x = x' := by
    intro x x' he
    obtain ⟨m, hm⟩ := ker_phi ((x, g x) - (x', g x')) (by rw [phi_sub, he, sub_self])
    have := tiles_uniq h2 (a := (x, g x) - (x', g x')) (a' := 0) (b := (x', g x')) (b' := (x, g x))
      (by rw [hm, Finset.mem_coe, mem_V2]; exact ⟨m, Or.inl rfl⟩) mem0 (hg _) (hg _) (by abel)
    exact (congrArg Prod.fst this.2).symm
  have notboth : ∀ x x' (w : ZMod 4 × ZMod 6), phi (x, g x) = w → phi (x', g x') = w - (1, 3) →
      False := by
    intro x x' w hx hx'
    obtain ⟨m, hm⟩ := ker_phi ((x, g x) - (x', g x') - (1, 2))
      (by rw [phi_sub, phi_sub, hx, hx', phi_c]; abel)
    have hd : (x, g x) - (x', g x') = (4 * m + 1, 2 * m + 2) := by
      rw [sub_eq_iff_eq_add] at hm; rw [hm]; ext <;> simp <;> ring
    have := tiles_uniq h2 (a := (x, g x) - (x', g x')) (a' := 0) (b := (x', g x')) (b' := (x, g x))
      (by rw [hd, Finset.mem_coe, mem_V2]; exact ⟨m, Or.inr rfl⟩) mem0 (hg _) (hg _) (by abel)
    have h1 := congrArg Prod.fst (hd.symm.trans this.1)
    exact ne_4m1 m h1
  have atleast : ∀ w : ZMod 4 × ZMod 6, (∃ x, phi (x, g x) = w) ∨ (∃ x, phi (x, g x) = w - (1, 3)) := by
    intro w
    obtain ⟨h, hh⟩ := phi_surj w
    obtain ⟨⟨v, c⟩, ⟨hv, hc, hvc⟩, -⟩ := h2 h
    simp only at hv hc hvc
    rw [Finset.mem_coe, mem_V2] at hv
    obtain ⟨m, hm | hm⟩ := hv
    · left; refine ⟨c.1, ?_⟩
      rw [← uniq c hc]
      have : c = h - v := by rw [← hvc]; abel
      rw [this, phi_sub, hh, hm, (phi_V2 m).1, sub_zero]
    · right; refine ⟨c.1, ?_⟩
      rw [← uniq c hc]
      have : c = h - v := by rw [← hvc]; abel
      rw [this, phi_sub, hh, hm, (phi_V2 m).2]
  -- the fibre sets
  let fib : ZMod 4 → Finset (ZMod 12) := fun r => Finset.univ.filter (fun x => c4 x = r)
  let q : ZMod 12 → ZMod 6 := fun x => (phi (x, g x)).2
  let S : ZMod 4 → Finset (ZMod 6) := fun r => (fib r).image q
  have hq : ∀ x, phi (x, g x) = (c4 x, q x) := fun x => rfl
  have qinj : ∀ r, Set.InjOn q (fib r) := by
    intro r x hx x' hx' he
    simp only [fib, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hx'
    apply injC; rw [hq, hq, hx, hx']; exact Prod.ext rfl he
  have Scard : ∀ r, (S r).card = 3 := fun r => by
    rw [Finset.card_image_of_injOn (qinj r)]; exact fiber3 r
  have Sx : ∀ r s, s ∈ S r ↔ ¬ (s - 3 ∈ S (r - 1)) := by
    intro r s
    simp only [S, fib, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩ ⟨x', hx', he⟩
      apply notboth x x' (r, q x) (by rw [hq, hx])
      rw [hq, hx', he]; rfl
    · intro hn
      rcases atleast (r, s) with ⟨x, hx⟩ | ⟨x, hx⟩
      · rw [hq] at hx; exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
      · exfalso; apply hn; rw [hq] at hx
        exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  let e : ZMod 4 → ℕ := fun r => ((S r).filter (fun s => s.val % 2 = 0)).card
  have he : ∀ r, e r = e (r - 1) := fun r => comb _ _ (Scard r) (Sx r)
  have e_eq : ∀ r, e r = ((fib r).filter (fun x => (q x).val % 2 = 0)).card := by
    intro r
    simp only [e, S, Finset.filter_image]
    rw [Finset.card_image_of_injOn]
    intro x hx x' hx' h
    exact qinj r (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hx')).1) h
  have total : ∑ r : ZMod 4, e r = 6 := by
    simp_rw [e_eq]
    refine Eq.trans ?_ count6
    rw [Finset.card_eq_sum_card_fiberwise (f := c4) (t := Finset.univ) (by simp)]
    apply Finset.sum_congr rfl
    intro r _
    congr 1; ext x
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
    have : (q x).val % 2 = 0 ↔ (x - g x).val % 2 = 0 := par6 x (g x)
    rw [this]; tauto
  have e1 := he 1; have e2 := he 2; have e3 := he 3
  have h10 : (1 : ZMod 4) - 1 = 0 := by decide
  have h21 : (2 : ZMod 4) - 1 = 1 := by decide
  have h32 : (3 : ZMod 4) - 1 = 2 := by decide
  rw [h10] at e1; rw [h21] at e2; rw [h32] at e3
  have : ∑ r : ZMod 4, e r = e 0 + e 1 + e 2 + e 3 := by
    rw [show (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]; ring
  omega

theorem At_not_tile (B : Set K) (hT : Tiles At B) : False := by
  obtain ⟨⟨a0, b0⟩, ⟨-, hb0, -⟩, -⟩ := hT 0
  simp only at hb0
  let C : Set H := {h | (h, b0.2) ∈ B}
  have layer : ∀ t : ZMod 5, Tiles (VL t : Set H) C := by
    intro t h
    obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, huniq⟩ := hT (h, t + b0.2)
    simp only at ha hb hab
    have hb2 : b.2 = b0.2 := same_layer hT hb hb0
    have ha2 : a.2 = t := by
      have := congrArg Prod.snd hab; simp only [Prod.snd_add] at this; rw [hb2] at this
      exact add_right_cancel this
    refine ⟨(a.1, b.1), ⟨?_, ?_, ?_⟩, ?_⟩
    · show a.1 ∈ VL t; rw [← ha2]; exact ha
    · show (b.1, b0.2) ∈ B; rw [← hb2]; exact hb
    · have := congrArg Prod.fst hab; simpa using this
    · rintro ⟨v, c⟩ ⟨hv, hc, hvc⟩
      simp only at hv hc hvc
      have := huniq ((v, t), (c, b0.2)) ⟨hv, hc, Prod.ext hvc rfl⟩
      have e1 := congrArg (fun p : K × K => p.1.1) this
      have e2 := congrArg (fun p : K × K => p.2.1) this
      simp only at e1 e2
      rw [e1, e2]
  have l0 := layer 0; rw [VL_V0 (by decide) (by decide)] at l0
  have l4 := layer 4; rw [VL4] at l4
  have l3 := layer 3; rw [VL3] at l3
  exact no_common C l0 l4 l3

end FG

end

-- ===== Part 2 =====
section

open Real

namespace FG

noncomputable def ee (θ : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * θ)

lemma ee_add (a b : ℝ) : ee (a + b) = ee a * ee b := by
  simp only [ee, ← Complex.exp_add]; congr 1; push_cast; ring

lemma ee_int (n : ℤ) : ee n = 1 := by
  simp only [ee]; rw [Complex.exp_eq_one_iff]; exact ⟨n, by push_cast; ring⟩

lemma ee_zero : ee 0 = 1 := by simpa using ee_int 0

lemma ee_add_int (a : ℝ) (n : ℤ) : ee (a + n) = ee a := by rw [ee_add, ee_int, mul_one]

lemma ee_half : ee (1 / 2) = -1 := by
  simp only [ee]
  have : 2 * (π : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ) = π * Complex.I := by push_cast; ring
  rw [this, Complex.exp_pi_mul_I]

lemma ee_eq_one {θ : ℝ} (h : ee θ = 1) : ∃ n : ℤ, θ = n := by
  simp only [ee] at h; rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have h2 : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (2 * π * Complex.I) * (θ : ℂ) = (2 * π * Complex.I) * (n : ℂ) := by rw [hn]; ring
  have := mul_left_cancel₀ h2 this
  exact_mod_cast this

lemma ee_nat_mul (m : ℕ) (θ : ℝ) : ee (m * θ) = ee θ ^ m := by
  induction m with
  | zero => simp [ee_zero]
  | succ m ih => rw [pow_succ, ← ih, ← ee_add]; congr 1; push_cast; ring

lemma geom0 (N : ℕ) (θ : ℝ) (h1 : ∀ n : ℤ, θ ≠ n) (hN : ∃ n : ℤ, (N : ℝ) * θ = n) :
    ∑ m ∈ Finset.range N, ee (m * θ) = 0 := by
  have hne : ee θ ≠ 1 := fun h => by obtain ⟨n, hn⟩ := ee_eq_one h; exact h1 n hn
  simp_rw [ee_nat_mul]
  rw [geom_sum_eq hne, ← ee_nat_mul]
  obtain ⟨n, hn⟩ := hN
  rw [hn, ee_int]; simp

lemma not_int_of_not_dvd {a : ℤ} {n : ℕ} (hn : 0 < n) (h : ¬ (n : ℤ) ∣ a) :
    ∀ m : ℤ, (a : ℝ) / n ≠ m := by
  intro m hm; apply h; refine ⟨m, ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by positivity
  field_simp at hm
  exact_mod_cast (by linarith : (a : ℝ) = n * m)

/-- geometric sum of `ee (m a / n)` over a full period. -/
lemma geom_dvd (n : ℕ) (hn : 0 < n) (a : ℤ) (h : ¬ (n : ℤ) ∣ a) :
    ∑ m ∈ Finset.range n, ee (m * ((a : ℝ) / n)) = 0 :=
  geom0 n _ (not_int_of_not_dvd hn h) ⟨a, by field_simp⟩

lemma ee_mod (a : ℤ) (N n : ℕ) (hn : 0 < n) :
    ee (a * ((N % n : ℕ) : ℝ) / n) = ee (a * N / n) := by
  have hN : (N : ℝ) = (N % n : ℕ) + n * (N / n : ℕ) := by exact_mod_cast (Nat.mod_add_div N n).symm
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [hN, mul_add, add_div, show (a : ℝ) * (n * (N / n : ℕ)) / n = ((a * ((N / n : ℕ) : ℤ) : ℤ) : ℝ) by
    rw [Int.cast_mul, Int.cast_natCast]; field_simp, ee_add_int]

lemma sum_zmod12 (F : ℕ → ℂ) : ∑ k : ZMod 12, F k.val = ∑ m ∈ Finset.range 12, F m :=
  Fin.sum_univ_eq_sum_range F 12

lemma sum_zmod5 (F : ℕ → ℂ) : ∑ k : ZMod 5, F k.val = ∑ m ∈ Finset.range 5, F m :=
  Fin.sum_univ_eq_sum_range F 5

noncomputable def cH (du dv : ℤ) (h : H) : ℂ := ee ((du * h.1.val + dv * h.2.val) / 12)

lemma V0_eq : V0 = Finset.univ.image (fun k : ZMod 12 => ((0 : ZMod 12), k)) := by decide
lemma V1_eq : V1 = Finset.univ.image (fun k : ZMod 12 => (k, k)) := by decide

def v2f (p : ℕ × ℕ) : H := (((4 * p.1 + p.2 : ℕ) : ZMod 12), ((2 * p.1 + 2 * p.2 : ℕ) : ZMod 12))

lemma V2_eq : V2 = (Finset.range 6 ×ˢ Finset.range 2).image v2f := by decide

lemma v2f_inj : Set.InjOn v2f ↑(Finset.range 6 ×ˢ Finset.range 2) := by
  intro p hp p' hp' h
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hp hp'
  obtain ⟨a, b⟩ := p; obtain ⟨a', b'⟩ := p'
  simp only at hp hp'
  obtain ⟨ha, hb⟩ := hp; obtain ⟨ha', hb'⟩ := hp'
  interval_cases a <;> interval_cases b <;> interval_cases a' <;> interval_cases b' <;>
    first | rfl | (exfalso; revert h; decide)

lemma sV0 (du dv : ℤ) : ∑ h ∈ V0, cH du dv h = ∑ m ∈ Finset.range 12, ee (m * ((dv : ℝ) / 12)) := by
  rw [V0_eq, Finset.sum_image (by intro a _ b _ h; simpa using h)]
  simp only [cH]
  rw [← sum_zmod12 (fun m => ee (m * ((dv : ℝ) / 12)))]
  congr 1; ext k; congr 1; simp; ring

lemma sV1 (du dv : ℤ) :
    ∑ h ∈ V1, cH du dv h = ∑ m ∈ Finset.range 12, ee (m * (((du + dv : ℤ) : ℝ) / 12)) := by
  rw [V1_eq, Finset.sum_image (by intro a _ b _ h; simpa using h)]
  simp only [cH]
  rw [← sum_zmod12 (fun m => ee (m * (((du + dv : ℤ) : ℝ) / 12)))]
  congr 1; ext k; congr 1; push_cast; ring

lemma sV2 (du dv : ℤ) :
    ∑ h ∈ V2, cH du dv h = (∑ m ∈ Finset.range 6, ee (m * (((4 * du + 2 * dv : ℤ) : ℝ) / 12))) *
      (1 + ee (((du + 2 * dv : ℤ) : ℝ) / 12)) := by
  rw [V2_eq, Finset.sum_image v2f_inj, Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_add, mul_one]
  simp only [cH, v2f, ZMod.val_natCast]
  have e1 : ∀ (N : ℕ) (a : ℤ), (a : ℝ) * ((N % 12 : ℕ) : ℝ) = (a : ℝ) * N - 12 * (a * (N / 12 : ℕ) : ℤ) := by
    intro N a
    have := Nat.mod_add_div N 12
    have h' : ((N % 12 : ℕ) : ℝ) = N - 12 * (N / 12 : ℕ) := by
      rw [eq_sub_iff_add_eq]; exact_mod_cast this
    rw [h']; simp only [Int.cast_mul, Int.cast_natCast]; ring
  rw [e1, e1, e1, e1]
  congr 1
  · rw [show ((du : ℝ) * (4 * m + 0 : ℕ) - 12 * ((du * ((4 * m + 0 : ℕ) / 12 : ℕ) : ℤ) : ℝ) +
        ((dv : ℝ) * (2 * m + 2 * 0 : ℕ) - 12 * ((dv * ((2 * m + 2 * 0 : ℕ) / 12 : ℕ) : ℤ) : ℝ))) / 12
        = m * (((4 * du + 2 * dv : ℤ) : ℝ) / 12) +
          ((-(du * ((4 * m + 0 : ℕ) / 12 : ℕ) + dv * ((2 * m + 2 * 0 : ℕ) / 12 : ℕ)) : ℤ) : ℝ) by
        simp only [Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_neg, Int.cast_ofNat, Nat.cast_add,
          Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]; ring, ee_add_int]
  · rw [← ee_add]
    rw [show ((du : ℝ) * (4 * m + 1 : ℕ) - 12 * ((du * ((4 * m + 1 : ℕ) / 12 : ℕ) : ℤ) : ℝ) +
        ((dv : ℝ) * (2 * m + 2 * 1 : ℕ) - 12 * ((dv * ((2 * m + 2 * 1 : ℕ) / 12 : ℕ) : ℤ) : ℝ))) / 12
        = (m * (((4 * du + 2 * dv : ℤ) : ℝ) / 12) + ((du + 2 * dv : ℤ) : ℝ) / 12) +
          ((-(du * ((4 * m + 1 : ℕ) / 12 : ℕ) + dv * ((2 * m + 2 * 1 : ℕ) / 12 : ℕ)) : ℤ) : ℝ) by
        simp only [Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_neg, Int.cast_ofNat, Nat.cast_add,
          Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]; ring, ee_add_int]

def fE (y : ZMod 12) : ZMod 12 := (![0, 5, 0, 7, 9, 2, 10, 4, 7, 8, 10, 10] : Fin 12 → ZMod 12) y

lemma E1 : ∀ y y' : ZMod 12, y ≠ y' → fE y + y ≠ fE y' + y' := by decide
lemma E2 : ∀ y y' : ZMod 12, y ≠ y' →
    4 * (fE y - fE y') + 2 * (y - y') ≠ 0 ∨ (fE y - fE y') + 2 * (y - y') = 6 := by decide

lemma zcast12 (x : ZMod 12) : (((x.val : ℤ)) : ZMod 12) = x := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]
lemma zcast5 (x : ZMod 5) : (((x.val : ℤ)) : ZMod 5) = x := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

lemma dvd12 (z : ℤ) : ((12 : ℕ) : ℤ) ∣ z ↔ (z : ZMod 12) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd z 12).symm
lemma dvd5 (z : ℤ) : ((5 : ℕ) : ℤ) ∣ z ↔ (z : ZMod 5) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).symm

noncomputable def chi (du dv dr : ℤ) (κ : K) : ℂ :=
  ee ((du * κ.1.1.val + dv * κ.1.2.val) / 12 + dr * κ.2.val / 5)

lemma chi_split (du dv dr : ℤ) (h : H) (t : ZMod 5) :
    chi du dv dr (h, t) = cH du dv h * ee (dr * t.val / 5) := ee_add _ _

lemma VL_cases (t : ZMod 5) : VL t = V0 ∨ VL t = V1 ∨ VL t = V2 := by
  unfold VL; split_ifs <;> simp

lemma card_VL (t : ZMod 5) : (VL t).card = 12 := by
  rcases VL_cases t with h | h | h <;> rw [h] <;> decide

lemma sum_At (F : K → ℂ) :
    ∑ κ : K, (if κ.1 ∈ VL κ.2 then F κ else 0) = ∑ t : ZMod 5, ∑ h ∈ VL t, F (h, t) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  show ∑ x, (if x ∈ VL t then F (x, t) else 0) = _
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma inner0 (y y' : ZMod 12) (hy : y ≠ y') (t : ZMod 5) :
    ∑ h ∈ VL t, cH (((fE y).val : ℤ) - (fE y').val) ((y.val : ℤ) - y'.val) h = 0 := by
  set du : ℤ := ((fE y).val : ℤ) - (fE y').val with hdu
  set dv : ℤ := (y.val : ℤ) - y'.val with hdv
  have cu : (du : ZMod 12) = fE y - fE y' := by rw [hdu, Int.cast_sub, zcast12, zcast12]
  have cv : (dv : ZMod 12) = y - y' := by rw [hdv, Int.cast_sub, zcast12, zcast12]
  rcases VL_cases t with h | h | h <;> rw [h]
  · rw [sV0]
    have := geom_dvd 12 (by norm_num) dv (by
      rw [dvd12, cv]
      exact sub_ne_zero.mpr hy)
    simpa using this
  · rw [sV1]
    have := geom_dvd 12 (by norm_num) (du + dv) (by
      rw [dvd12, Int.cast_add, cu, cv]
      intro h0; apply E1 y y' hy; linear_combination h0)
    simpa using this
  · rw [sV2]
    rcases E2 y y' hy with h2 | h2
    · have hb : ¬ ((12 : ℕ) : ℤ) ∣ (4 * du + 2 * dv) := by
        rw [dvd12]
        push_cast; rw [cu, cv]; exact h2
      have := geom0 6 (((4 * du + 2 * dv : ℤ) : ℝ) / 12)
        (by have := not_int_of_not_dvd (by norm_num) hb; simpa using this)
        ⟨2 * du + dv, by push_cast; ring⟩
      rw [this, zero_mul]
    · have hb : ((12 : ℕ) : ℤ) ∣ (du + 2 * dv - 6) := by
        rw [dvd12]
        push_cast; rw [cu, cv, h2]; ring
      obtain ⟨q, hq⟩ := hb
      have : (((du + 2 * dv : ℤ) : ℝ) / 12) = 1 / 2 + (q : ℤ) := by
        have : ((du + 2 * dv : ℤ) : ℝ) = 12 * q + 6 := by
          have := congrArg (fun z : ℤ => (z : ℝ)) hq; push_cast at this ⊢; linarith
        rw [this]; ring
      rw [this, ee_add_int, ee_half]; ring

theorem At_orth (y y' : ZMod 12) (r r' : ZMod 5) (hne : (y, r) ≠ (y', r')) :
    ∑ κ : K, (if κ.1 ∈ VL κ.2 then
      chi (((fE y).val : ℤ) - (fE y').val) ((y.val : ℤ) - y'.val) ((r.val : ℤ) - r'.val) κ
      else 0) = 0 := by
  rw [sum_At]
  simp_rw [chi_split, ← Finset.sum_mul]
  by_cases hy : y = y'
  · subst hy
    have hr : r ≠ r' := fun h => hne (by rw [h])
    simp only [sub_self, cH, Int.cast_zero, zero_mul, add_zero, zero_div, ee_zero,
      Finset.sum_const, card_VL, nsmul_eq_mul, Nat.cast_ofNat]
    rw [← Finset.mul_sum]
    have h5 := geom_dvd 5 (by norm_num) ((r.val : ℤ) - r'.val) (by
      rw [dvd5, Int.cast_sub,
        zcast5, zcast5]
      exact sub_ne_zero.mpr hr)
    have : ∑ t : ZMod 5, ee ((((r.val : ℤ) - r'.val : ℤ) : ℝ) * t.val / 5) =
        ∑ m ∈ Finset.range 5, ee (m * ((((r.val : ℤ) - r'.val : ℤ) : ℝ) / ((5 : ℕ) : ℝ))) := by
      rw [← sum_zmod5]; congr 1; ext t; congr 1; push_cast; ring
    rw [this, h5, mul_zero]
  · simp only [inner0 y y' hy, zero_mul, Finset.sum_const_zero]

end FG

end

-- ===== Part 3 =====
section

open Real Finset

namespace FG

abbrev kk : ℕ := 60

def πN (p : ℕ × ℕ) : K := (((p.1 : ZMod 12), (p.2 : ZMod 12)), (p.1 : ZMod 5))

def condK (κ : K) : Prop := κ.1 ∈ VL κ.2

instance : DecidablePred condK := fun κ => inferInstanceAs (Decidable (κ.1 ∈ VL κ.2))

def SN : Finset (ℕ × ℕ) := (range (60 * kk) ×ˢ range (12 * kk)).filter (fun p => condK (πN p))

lemma sum_range_blocks {M : Type*} [AddCommMonoid M] (a k : ℕ) (f : ℕ → M) :
    ∑ X ∈ range (a * k), f X = ∑ j ∈ range k, ∑ x ∈ range a, f (a * j + x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma πN_shift (X0 Y0 j1 j2 : ℕ) : πN (60 * j1 + X0, 12 * j2 + Y0) = πN (X0, Y0) := by
  have h1 : ((60 : ℕ) : ZMod 12) = 0 := by decide
  have h2 : ((12 : ℕ) : ZMod 12) = 0 := by decide
  have h3 : ((60 : ℕ) : ZMod 5) = 0 := by decide
  simp only [πN, Nat.cast_add, Nat.cast_mul, h1, h2, h3, zero_mul, zero_add]

lemma sum_SN {M : Type*} [AddCommMonoid M] (F : ℕ × ℕ → M) :
    ∑ p ∈ SN, F p = ∑ j1 ∈ range kk, ∑ j2 ∈ range kk, ∑ X0 ∈ range 60, ∑ Y0 ∈ range 12,
      (if condK (πN (X0, Y0)) then F (60 * j1 + X0, 12 * j2 + Y0) else 0) := by
  rw [SN, Finset.sum_filter, Finset.sum_product, sum_range_blocks]
  simp_rw [sum_range_blocks 12 kk, πN_shift]
  apply Finset.sum_congr rfl; intro j1 _
  rw [Finset.sum_comm]

set_option maxRecDepth 200000 in
lemma crt_wit : ∀ κ : K, πN ((25 * κ.1.1.val + 36 * κ.2.val) % 60, κ.1.2.val) = κ := by decide

lemma crt_lt (κ : K) : (25 * κ.1.1.val + 36 * κ.2.val) % 60 < 60 ∧ κ.1.2.val < 12 :=
  ⟨Nat.mod_lt _ (by norm_num), ZMod.val_lt _⟩

set_option maxRecDepth 100000 in
lemma πN_injOn : Set.InjOn πN ↑(range 60 ×ˢ range 12) := by
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' he
  simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at hab hab'
  simp only [πN, Prod.mk.injEq, ZMod.natCast_eq_natCast_iff'] at he
  obtain ⟨⟨h1, h2⟩, h3⟩ := he
  simp only [Prod.mk.injEq]; omega

lemma sum_P_K {M : Type*} [AddCommMonoid M] (G : K → M) :
    ∑ X0 ∈ range 60, ∑ Y0 ∈ range 12, G (πN (X0, Y0)) = ∑ κ : K, G κ := by
  rw [← Finset.sum_product' (f := fun a b => G (πN (a, b)))]
  apply Finset.sum_nbij πN
  · simp
  · exact πN_injOn
  · intro κ _
    refine ⟨((25 * κ.1.1.val + 36 * κ.2.val) % 60, κ.1.2.val), ?_, crt_wit κ⟩
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]; exact crt_lt κ
  · intro p _; rfl

lemma sum_At' {M : Type*} [AddCommMonoid M] (F : K → M) :
    ∑ κ : K, (if condK κ then F κ else 0) = ∑ t : ZMod 5, ∑ h ∈ VL t, F (h, t) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  show ∑ x, (if x ∈ VL t then F (x, t) else 0) = _
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma card_SN : SN.card = 60 * kk * kk := by
  rw [Finset.card_eq_sum_ones, sum_SN]
  have : ∑ X0 ∈ range 60, ∑ Y0 ∈ range 12, (if condK (πN (X0, Y0)) then 1 else 0) = 60 := by
    rw [sum_P_K (fun κ => if condK κ then 1 else 0), sum_At']
    simp [card_VL]
  simp only [this, Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

abbrev I := ZMod 12 × ZMod 5 × Fin kk × Fin kk

noncomputable def γ1 (i : I) : ℝ :=
  ((fE i.1).val : ℝ) / 12 + (i.2.1.val : ℝ) / 5 + ((i.2.2.1 : ℕ) : ℝ) / (60 * (kk : ℝ))
noncomputable def γ2 (i : I) : ℝ := (i.1.val : ℝ) / 12 + ((i.2.2.2 : ℕ) : ℝ) / (12 * (kk : ℝ))

lemma chi_eq (du dv dr : ℤ) (X0 Y0 : ℕ) :
    chi du dv dr (πN (X0, Y0)) = ee (((du : ℝ) / 12 + dr / 5) * X0 + dv / 12 * Y0) := by
  simp only [chi, πN, ZMod.val_natCast]
  have hx12 : (X0 : ℝ) = (X0 % 12 : ℕ) + 12 * (X0 / 12 : ℕ) := by exact_mod_cast (Nat.mod_add_div X0 12).symm
  have hy12 : (Y0 : ℝ) = (Y0 % 12 : ℕ) + 12 * (Y0 / 12 : ℕ) := by exact_mod_cast (Nat.mod_add_div Y0 12).symm
  have hx5 : (X0 : ℝ) = (X0 % 5 : ℕ) + 5 * (X0 / 5 : ℕ) := by exact_mod_cast (Nat.mod_add_div X0 5).symm
  rw [show (((du : ℝ) / 12 + dr / 5) * X0 + dv / 12 * Y0 : ℝ) =
      (du * ((X0 % 12 : ℕ) : ℝ) + dv * ((Y0 % 12 : ℕ) : ℝ)) / 12 + dr * ((X0 % 5 : ℕ) : ℝ) / 5 +
      ((du * ((X0 / 12 : ℕ) : ℤ) + dv * ((Y0 / 12 : ℕ) : ℤ) + dr * ((X0 / 5 : ℕ) : ℤ) : ℤ) : ℝ) by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    linear_combination ((du : ℝ) / 12) * hx12 + ((dr : ℝ) / 5) * hx5 + ((dv : ℝ) / 12) * hy12,
    ee_add_int]

lemma geom_fin (s s' : Fin kk) (h : s ≠ s') :
    ∑ j ∈ range kk, ee (j * ((((s : ℕ) : ℤ) - ((s' : ℕ) : ℤ) : ℤ) / (kk : ℝ))) = 0 := by
  apply geom_dvd kk (by norm_num)
  rintro ⟨c, hc⟩
  have h1 := s.isLt; have h2 := s'.isLt
  have : (s : ℕ) ≠ (s' : ℕ) := fun e => h (Fin.ext e)
  simp only [kk] at *
  omega

theorem S_orth (i i' : I) (hne : i ≠ i') :
    ∑ p ∈ SN, ee ((γ1 i - γ1 i') * p.1 + (γ2 i - γ2 i') * p.2) = 0 := by
  obtain ⟨y, r, s1, s2⟩ := i; obtain ⟨y', r', s1', s2'⟩ := i'
  set du : ℤ := ((fE y).val : ℤ) - (fE y').val with hdu
  set dv : ℤ := (y.val : ℤ) - y'.val with hdv
  set dr : ℤ := (r.val : ℤ) - r'.val with hdr
  set d1 : ℤ := ((s1 : ℕ) : ℤ) - ((s1' : ℕ) : ℤ) with hd1
  set d2 : ℤ := ((s2 : ℕ) : ℤ) - ((s2' : ℕ) : ℤ) with hd2
  have hk : (kk : ℝ) ≠ 0 := by norm_num
  have key : ∀ j1 j2 X0 Y0 : ℕ,
      ee ((γ1 (y, r, s1, s2) - γ1 (y', r', s1', s2')) * ((60 * j1 + X0 : ℕ) : ℝ) +
        (γ2 (y, r, s1, s2) - γ2 (y', r', s1', s2')) * ((12 * j2 + Y0 : ℕ) : ℝ)) =
      ee (((du : ℝ) / 12 + dr / 5 + d1 / (60 * kk)) * X0 + ((dv : ℝ) / 12 + d2 / (12 * kk)) * Y0) *
        ee (j1 * ((d1 : ℝ) / kk)) * ee (j2 * ((d2 : ℝ) / kk)) := by
    intro j1 j2 X0 Y0
    rw [← ee_add, ← ee_add]
    rw [show (γ1 (y, r, s1, s2) - γ1 (y', r', s1', s2')) * ((60 * j1 + X0 : ℕ) : ℝ) +
        (γ2 (y, r, s1, s2) - γ2 (y', r', s1', s2')) * ((12 * j2 + Y0 : ℕ) : ℝ) =
        (((du : ℝ) / 12 + dr / 5 + d1 / (60 * kk)) * X0 + ((dv : ℝ) / 12 + d2 / (12 * kk)) * Y0 +
          j1 * ((d1 : ℝ) / kk) + j2 * ((d2 : ℝ) / kk)) +
          (((j1 : ℤ) * (5 * du + 12 * dr) + (j2 : ℤ) * dv : ℤ) : ℝ) by
      simp only [γ1, γ2, hdu, hdv, hdr, hd1, hd2]
      push_cast
      field_simp
      ring, ee_add_int]
  rw [sum_SN]
  simp only [key]
  simp_rw [← ite_zero_mul, ← Finset.sum_mul]
  rw [← Finset.sum_mul_sum, ← Finset.mul_sum]
  by_cases h1 : s1 = s1'
  · by_cases h2 : s2 = s2'
    · subst h1 h2
      have hyr : (y, r) ≠ (y', r') := fun e => hne (by rw [Prod.mk.injEq] at e; rw [e.1, e.2])
      have hQ : ∑ X0 ∈ range 60, ∑ Y0 ∈ range 12, (if condK (πN (X0, Y0)) then
          ee (((du : ℝ) / 12 + dr / 5 + d1 / (60 * kk)) * X0 + ((dv : ℝ) / 12 + d2 / (12 * kk)) * Y0)
          else 0) = 0 := by
        have e0 : ∀ X0 Y0 : ℕ, ee (((du : ℝ) / 12 + dr / 5 + d1 / (60 * kk)) * X0 +
            ((dv : ℝ) / 12 + d2 / (12 * kk)) * Y0) = chi du dv dr (πN (X0, Y0)) := by
          intro X0 Y0; rw [chi_eq]; congr 1; simp [hd1, hd2]
        simp_rw [e0]
        rw [sum_P_K (fun κ => if condK κ then chi du dv dr κ else 0)]
        exact At_orth y y' r r' hyr
      rw [hQ]; ring
    · rw [geom_fin s2 s2' h2]; ring
  · rw [geom_fin s1 s1' h1]; ring

end FG

end

-- ===== Part 4 =====
section

open Finset

namespace FG

def πZ (z : ℤ × ℤ) : K := (((z.1 : ZMod 12), (z.2 : ZMod 12)), (z.1 : ZMod 5))

lemma πZ_add (a b : ℤ × ℤ) : πZ (a + b) = πZ a + πZ b := by
  simp only [πZ, Prod.fst_add, Prod.snd_add, Int.cast_add, Prod.mk_add_mk]

lemma πZ_sub (a b : ℤ × ℤ) : πZ (a - b) = πZ a - πZ b := by
  simp only [πZ, Prod.fst_sub, Prod.snd_sub, Int.cast_sub, Prod.mk_sub_mk]

lemma πZ_cast (a b : ℕ) : πZ ((a : ℤ), (b : ℤ)) = πN (a, b) := by
  simp only [πZ, πN, Int.cast_natCast]

def cZ (p : ℕ × ℕ) : ℤ × ℤ := ((p.1 : ℤ), (p.2 : ℤ))

lemma cZ_inj : Function.Injective cZ := fun p q h => by
  simp only [cZ, Prod.mk.injEq, Nat.cast_inj] at h; exact Prod.ext h.1 h.2

noncomputable def SZ : Finset (ℤ × ℤ) :=
  Classical.choose (⟨SN.image cZ, rfl⟩ : ∃ S : Finset (ℤ × ℤ), S = SN.image cZ)

lemma SZ_eq : SZ = SN.image cZ :=
  Classical.choose_spec (⟨SN.image cZ, rfl⟩ : ∃ S : Finset (ℤ × ℤ), S = SN.image cZ)

lemma card_SZ : SZ.card = 216000 := by
  rw [SZ_eq, card_image_of_injective _ cZ_inj, card_SN]; norm_num [kk]

lemma mem_SZ {z : ℤ × ℤ} :
    z ∈ SZ ↔ (0 ≤ z.1 ∧ z.1 < 3600 ∧ 0 ≤ z.2 ∧ z.2 < 720) ∧ condK (πZ z) := by
  rw [SZ_eq]; simp only [mem_image, SN, mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨p, ⟨⟨h1, h2⟩, hc⟩, rfl⟩
    simp only [cZ]
    rw [πZ_cast]
    simp only [kk] at h1 h2
    refine ⟨⟨by positivity, by omega, by positivity, by omega⟩, hc⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, hc⟩
    refine ⟨(z.1.toNat, z.2.toNat), ⟨⟨by simp only [kk]; omega, by simp only [kk]; omega⟩, ?_⟩, ?_⟩
    · have : z = ((z.1.toNat : ℤ), (z.2.toNat : ℤ)) := by
        ext <;> simp <;> omega
      rw [this, πZ_cast] at hc; exact hc
    · simp only [cZ]; ext <;> simp <;> omega

lemma surjP (κ : K) : ∃ p : ℤ × ℤ, (0 ≤ p.1 ∧ p.1 < 60 ∧ 0 ≤ p.2 ∧ p.2 < 12) ∧ πZ p = κ := by
  refine ⟨((((25 * κ.1.1.val + 36 * κ.2.val) % 60 : ℕ) : ℤ), ((κ.1.2.val : ℕ) : ℤ)), ?_, ?_⟩
  · have := crt_lt κ; simp only; omega
  · rw [πZ_cast]; exact crt_wit κ

def NN : ℤ := 1000000

lemma card_box (a b c d : ℤ) (h1 : a ≤ b) (h2 : c ≤ d) :
    (Ico a b ×ˢ Ico c d).card = (b - a).toNat * (d - c).toNat := by
  rw [card_product, Int.card_Ico, Int.card_Ico]

def Outer : Finset (ℤ × ℤ) := Ico (-59) 3600 ×ˢ Ico (-11) 720
def Inner : Finset (ℤ × ℤ) := Icc 0 3540 ×ˢ Icc 0 708
def Ring : Finset (ℤ × ℤ) := Outer \ Inner

set_option maxRecDepth 100000 in
lemma card_Ring : Ring.card = 164160 := by
  rw [Ring, card_sdiff_of_subset]
  · rw [Outer, Inner, card_product, card_product, Int.card_Ico, Int.card_Ico, Int.card_Icc,
      Int.card_Icc]; decide
  · intro z hz
    simp only [Inner, Outer, mem_product, mem_Icc, mem_Ico] at hz ⊢; omega

set_option maxRecDepth 100000 in
open Classical in
theorem SZ_not_tile (B : Set (ℤ × ℤ)) (hT : Tiles (SZ : Set (ℤ × ℤ)) B) : False := by
  have uq : ∀ {s s' σ σ' : ℤ × ℤ}, s ∈ SZ → s' ∈ SZ → σ ∈ B → σ' ∈ B → s + σ = s' + σ' →
      s = s' ∧ σ = σ' := fun hs hs' hσ hσ' h =>
    tiles_uniq hT (Finset.mem_coe.mpr hs) (Finset.mem_coe.mpr hs') hσ hσ' h
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = 1000000 := ⟨_, rfl⟩
  obtain ⟨CN, hCN⟩ : ∃ CN : Finset (ℤ × ℤ), CN = Ico 0 N ×ˢ Ico 0 N := ⟨_, rfl⟩
  obtain ⟨SigN, hSigN⟩ : ∃ SigN : Finset (ℤ × ℤ),
      SigN = ((CN ×ˢ SZ).image (fun q => q.1 - q.2)).filter (· ∈ B) := ⟨_, rfl⟩
  have memSig : ∀ σ, σ ∈ SigN ↔ σ ∈ B ∧ ∃ c ∈ CN, ∃ s ∈ SZ, c - s = σ := by
    intro σ; rw [hSigN]; simp only [mem_filter, mem_image, mem_product]
    constructor
    · rintro ⟨⟨⟨c, s⟩, ⟨hc, hs⟩, h⟩, hb⟩; exact ⟨hb, c, hc, s, hs, h⟩
    · rintro ⟨hb, c, hc, s, hs, h⟩; exact ⟨⟨(c, s), ⟨hc, hs⟩, h⟩, hb⟩
  obtain ⟨tr, htr⟩ : ∃ tr : (ℤ × ℤ) → Finset (ℤ × ℤ) → Finset (ℤ × ℤ),
      tr = fun σ F => F.map (addLeftEmbedding σ) := ⟨_, rfl⟩
  have mem_tr : ∀ σ F z, z ∈ tr σ F ↔ ∃ s ∈ F, σ + s = z := by
    intro σ F z; rw [htr]; simp only [mem_map, addLeftEmbedding_apply]
  have card_tr : ∀ σ F, (tr σ F).card = F.card := by intro σ F; rw [htr, card_map]
  obtain ⟨Bx, hBx⟩ : ∃ Bx : Finset (ℤ × ℤ), Bx = Ico (-3600) (N + 3600) ×ˢ Ico (-720) (N + 720) :=
    ⟨_, rfl⟩
  have hBxc : (Bx.card : ℤ) = (N + 7200) * (N + 1440) := by
    rw [hBx, card_product, Int.card_Ico, Int.card_Ico]; push_cast
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]; ring
  have hcount : SigN.card * 216000 ≤ Bx.card := by
    have hdisj : (SigN : Set (ℤ × ℤ)).PairwiseDisjoint (fun σ => tr σ SZ) := by
      intro σ hσ σ' hσ' hne
      rw [Function.onFun, Finset.disjoint_left]
      intro z hz hz'
      rw [mem_tr] at hz hz'
      obtain ⟨s, hs, hz⟩ := hz; obtain ⟨s', hs', he⟩ := hz'
      have h1 := ((memSig σ).mp hσ).1; have h2 := ((memSig σ').mp hσ').1
      have := uq hs hs' h1 h2 (by rw [add_comm s, add_comm s', hz, he])
      exact hne this.2
    have hsub : SigN.biUnion (fun σ => tr σ SZ) ⊆ Bx := by
      intro z hz
      rw [mem_biUnion] at hz
      obtain ⟨σ, hσ, hz⟩ := hz
      rw [mem_tr] at hz
      obtain ⟨s, hs, hz⟩ := hz
      obtain ⟨-, c, hc, s0, hs0, hσe⟩ := (memSig σ).mp hσ
      rw [mem_SZ] at hs hs0
      rw [hCN, mem_product, mem_Ico, mem_Ico] at hc
      rw [hBx, mem_product, mem_Ico, mem_Ico, ← hz, ← hσe]
      simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub]
      omega
    have := card_le_card hsub
    rw [card_biUnion hdisj] at this
    simp only [card_tr, card_SZ, sum_const, smul_eq_mul] at this
    exact this
  obtain ⟨Bad, hBad⟩ : ∃ Bad : Finset (ℤ × ℤ), Bad = SigN.biUnion (fun σ => tr σ Ring) := ⟨_, rfl⟩
  have hbad : Bad.card ≤ SigN.card * 164160 := by
    rw [hBad]; refine (card_biUnion_le).trans ?_
    simp only [card_tr, card_Ring, sum_const, smul_eq_mul, le_refl]
  obtain ⟨DN, hDN0⟩ : ∃ DN : Finset (ℤ × ℤ), DN = Ico 0 (N - 60) ×ˢ Ico 0 (N - 12) := ⟨_, rfl⟩
  have hDN : (DN.card : ℤ) = (N - 60) * (N - 12) := by
    rw [hDN0, card_product, Int.card_Ico, Int.card_Ico]; push_cast
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]; ring
  have hlt : Bad.card < DN.card := by
    have h1 : (SigN.card : ℤ) * 216000 ≤ (N + 7200) * (N + 1440) := by
      rw [← hBxc]; exact_mod_cast hcount
    have h2 : (Bad.card : ℤ) ≤ SigN.card * 164160 := by exact_mod_cast hbad
    have : (Bad.card : ℤ) < DN.card := by
      rw [hDN]; subst hN; norm_num at h1 ⊢; omega
    exact_mod_cast this
  obtain ⟨x, hxD, hxB⟩ := exists_mem_notMem_of_card_lt_card hlt
  have good : ∀ σ ∈ SigN, x - σ ∉ Ring := by
    intro σ hσ hR; apply hxB
    rw [hBad, mem_biUnion]
    exact ⟨σ, hσ, (mem_tr σ Ring x).mpr ⟨x - σ, hR, by abel⟩⟩
  rw [hDN0, mem_product, mem_Ico, mem_Ico] at hxD
  -- Claim A
  have claimA : ∀ σ ∈ B, ∀ p : ℤ × ℤ, (0 ≤ p.1 ∧ p.1 < 60 ∧ 0 ≤ p.2 ∧ p.2 < 12) →
      x + p - σ ∈ SZ → ∀ p' : ℤ × ℤ, (0 ≤ p'.1 ∧ p'.1 < 60 ∧ 0 ≤ p'.2 ∧ p'.2 < 12) →
      (0 ≤ (x + p' - σ).1 ∧ (x + p' - σ).1 < 3600 ∧ 0 ≤ (x + p' - σ).2 ∧ (x + p' - σ).2 < 720) := by
    intro σ hσ p hp hs p' hp'
    have hσN : σ ∈ SigN := (memSig σ).mpr ⟨hσ, x + p, by
      rw [hCN, mem_product, mem_Ico, mem_Ico]; simp only [Prod.fst_add, Prod.snd_add]; omega,
      x + p - σ, hs, by abel⟩
    have hg := good σ hσN
    rw [mem_SZ] at hs
    have hout : x - σ ∈ Outer := by
      simp only [Outer, mem_product, mem_Ico]
      simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub] at hs ⊢; omega
    have hin : x - σ ∈ Inner := by
      by_contra hn; exact hg (mem_sdiff.mpr ⟨hout, hn⟩)
    simp only [Inner, mem_product, mem_Icc] at hin
    simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub] at hin ⊢; omega
  let B' : Set K := {κ | ∃ σ ∈ B, ∃ p : ℤ × ℤ, (0 ≤ p.1 ∧ p.1 < 60 ∧ 0 ≤ p.2 ∧ p.2 < 12) ∧
    x + p - σ ∈ SZ ∧ κ = πZ σ}
  apply At_not_tile B'
  intro κ
  obtain ⟨p, hp, hpκ⟩ := surjP (κ - πZ x)
  have hw : πZ (x + p) = κ := by rw [πZ_add, hpκ]; abel
  obtain ⟨⟨s, σ⟩, ⟨hs, hσ, hsσ⟩, -⟩ := hT (x + p)
  simp only at hs hσ hsσ
  refine ⟨(πZ s, πZ σ), ⟨?_, ⟨σ, hσ, p, hp, by rw [← hsσ]; simpa using hs, rfl⟩, ?_⟩, ?_⟩
  · exact ((mem_SZ.mp hs).2 : condK (πZ s))
  · simp only; rw [← πZ_add, hsσ, hw]
  · rintro ⟨a, b⟩ ⟨ha, ⟨σ', hσ', p', hp', hs', rfl⟩, hab⟩
    simp only at ha hab
    have hbox := claimA σ' hσ' p' hp' hs' p hp
    have hmem : x + p - σ' ∈ SZ := by
      rw [mem_SZ]; refine ⟨hbox, ?_⟩
      show condK (πZ (x + p - σ'))
      rw [πZ_sub, hw, ← hab, add_sub_cancel_right]; exact ha
    have := uq hmem hs hσ' hσ (by rw [hsσ]; abel)
    have e1 : a = πZ s := by
      rw [← this.1, πZ_sub, hw, ← hab]; abel
    rw [e1, this.2]

end FG

end

-- ===== Part 5 =====
section

open MeasureTheory Set

namespace FG

noncomputable def zc (z : ℤ × ℤ) : Fin 2 → ℝ := ![(z.1 : ℝ), (z.2 : ℝ)]

def inS (z : ℤ × ℤ) : Prop := (0 ≤ z.1 ∧ z.1 < 3600 ∧ 0 ≤ z.2 ∧ z.2 < 720) ∧ condK (πZ z)

lemma inS_iff (z : ℤ × ℤ) : inS z ↔ z ∈ (SZ : Set (ℤ × ℤ)) := by
  rw [Finset.mem_coe, mem_SZ]; rfl

def Om : Set (Fin 2 → ℝ) := {x | ∃ z : ℤ × ℤ, inS z ∧ ∀ i, x i - zc z i ∈ Ioc (0 : ℝ) 1}

lemma ioc_floor (m : ℤ) (r : ℝ) : (m : ℝ) + r ∈ Ioc (0 : ℝ) 1 ↔ ⌊1 - r⌋ = m := by
  rw [Int.floor_eq_iff, mem_Ioc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem Om_not_tile : ¬ tilesByTranslation Om := by
  rintro ⟨T, hTc, hcov, hdisj⟩
  set N1 := univ \ ⋃ t ∈ T, translateSet Om t with hN1
  set P2 : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) := {p | p.1 ∈ T ∧ p.2 ∈ T ∧ p.1 ≠ p.2} with hP2
  set N2 := ⋃ p ∈ P2, translateSet Om p.1 ∩ translateSet Om p.2 with hN2d
  have hN2 : volume N2 = 0 := by
    rw [hN2d, measure_biUnion_null_iff ((hTc.prod hTc).mono (fun p hp => Set.mem_prod.mpr ⟨hp.1, hp.2.1⟩))]
    rintro p ⟨h1, h2, h3⟩; exact hdisj h1 h2 h3
  set Nall := ⋃ m : ℤ × ℤ, (fun x => x + zc m) ⁻¹' (N1 ∪ N2) with hNall
  have hNall0 : volume Nall = 0 := by
    apply measure_iUnion_null; intro m
    have := measure_preimage_add_right (volume : Measure (Fin 2 → ℝ)) (zc m) (N1 ∪ N2)
    rw [this]; exact measure_union_null hcov hN2
  obtain ⟨x, hx⟩ := (measure_eq_zero_iff_ae_notMem.mp hNall0).exists
  have hxn : ∀ n : ℤ × ℤ, x + zc n ∉ N1 ∧ x + zc n ∉ N2 := by
    intro n
    have : x ∉ (fun x => x + zc n) ⁻¹' (N1 ∪ N2) := fun h => hx (mem_iUnion.mpr ⟨n, h⟩)
    simp only [mem_preimage, mem_union, not_or] at this; exact this
  obtain ⟨b, hb⟩ : ∃ b : (Fin 2 → ℝ) → ℤ × ℤ, b = fun t => (⌊1 - (x 0 - t 0)⌋, ⌊1 - (x 1 - t 1)⌋) :=
    ⟨_, rfl⟩
  have memT : ∀ (n : ℤ × ℤ) t, x + zc n ∈ translateSet Om t ↔ inS (n - b t) := by
    intro n t
    simp only [translateSet, Om, mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, hzi⟩
      have h0 := hzi 0; have h1 := hzi 1
      simp only [Pi.sub_apply, Pi.add_apply, zc, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      have e0 : ⌊1 - (x 0 - t 0)⌋ = n.1 - z.1 := by
        rw [← ioc_floor]; push_cast; convert h0 using 1; ring
      have e1 : ⌊1 - (x 1 - t 1)⌋ = n.2 - z.2 := by
        rw [← ioc_floor]; push_cast; convert h1 using 1; ring
      have : n - b t = z := by
        simp only [hb, e0, e1]; ext <;> simp
      rw [this]; exact hz
    · intro h
      refine ⟨n - b t, h, ?_⟩
      intro i
      fin_cases i
      · simp only [Pi.sub_apply, Pi.add_apply, zc, hb, Fin.zero_eta, Matrix.cons_val_zero,
          Prod.fst_sub]
        have := (ioc_floor (⌊1 - (x 0 - t 0)⌋) (x 0 - t 0)).mpr rfl
        push_cast; convert this using 1; ring
      · simp only [Pi.sub_apply, Pi.add_apply, zc, hb, Fin.mk_one, Matrix.cons_val_one,
          Prod.snd_sub]
        have := (ioc_floor (⌊1 - (x 1 - t 1)⌋) (x 1 - t 1)).mpr rfl
        push_cast; convert this using 1; ring
  apply SZ_not_tile (b '' T)
  intro n
  have hcov' := (hxn n).1
  simp only [hN1, mem_diff, mem_univ, true_and, not_not, mem_iUnion] at hcov'
  obtain ⟨t, ht, hxt⟩ := hcov'
  have hS0 : inS (n - b t) := (memT n t).mp hxt
  have hS1 : n - b t ∈ (SZ : Set (ℤ × ℤ)) := by rw [← inS_iff]; exact hS0
  refine ⟨(n - b t, b t), ⟨?_, ⟨t, ht, rfl⟩, by simp⟩, ?_⟩
  · dsimp only; exact hS1
  rintro ⟨s, b'⟩ ⟨hs, ⟨t', ht', rfl⟩, he⟩
  simp only at hs he
  have hxt' : x + zc n ∈ translateSet Om t' := by
    rw [memT, ← he, add_sub_cancel_right, inS_iff]; exact hs
  have htt : t' = t := by
    rcases eq_or_ne t' t with h | hne
    · exact h
    exfalso
    have hmem : ((t', t) : (Fin 2 → ℝ) × (Fin 2 → ℝ)) ∈ P2 := ⟨ht', ht, hne⟩
    have hin : x + zc n ∈ N2 := by
      rw [hN2d]; exact mem_biUnion hmem ⟨hxt', hxt⟩
    exact (hxn n).2 hin
  rw [htt] at he ⊢
  simp only [Prod.mk.injEq, and_true]
  rw [← he]; abel

end FG

end

-- ===== Part 6 =====
section

open MeasureTheory Set Real

namespace FG

def Qz (c : Fin 2 → ℝ) : Set (Fin 2 → ℝ) := {x | ∀ i, x i - c i ∈ Ioc (0 : ℝ) 1}

def Q : Set (Fin 2 → ℝ) := {y | ∀ i, y i ∈ Ioc (0 : ℝ) 1}

lemma Qz_pi (c : Fin 2 → ℝ) : Qz c = Set.pi univ (fun i => Ioc (c i) (c i + 1)) := by
  ext x; simp only [Qz, mem_setOf_eq, mem_pi, mem_univ, true_implies, mem_Ioc]
  apply forall_congr'; intro i; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma Q_pi : Q = Set.pi univ (fun _ => Ioc (0 : ℝ) 1) := by
  ext x; simp [Q]

lemma meas_Qz (c : Fin 2 → ℝ) : MeasurableSet (Qz c) := by
  rw [Qz_pi]; exact MeasurableSet.univ_pi (fun i => measurableSet_Ioc)

lemma meas_Q : MeasurableSet Q := by
  rw [Q_pi]; exact MeasurableSet.univ_pi (fun i => measurableSet_Ioc)

lemma vol_Qz (c : Fin 2 → ℝ) : volume (Qz c) = 1 := by
  rw [Qz_pi, Real.volume_pi_Ioc]; simp

lemma preim_Qz (c : Fin 2 → ℝ) : (fun y => y + c) ⁻¹' (Qz c) = Q := by
  ext y; simp [Qz, Q]

lemma trans_int (c : Fin 2 → ℝ) (f : (Fin 2 → ℝ) → ℂ) :
    ∫ x in Qz c, f x = ∫ y in Q, f (y + c) := by
  have := (measurePreserving_add_right (volume : Measure (Fin 2 → ℝ)) c).setIntegral_preimage_emb
    (MeasurableEquiv.addRight c).measurableEmbedding f (Qz c)
  rw [preim_Qz] at this; exact this.symm

lemma trans_intOn (c : Fin 2 → ℝ) (f : (Fin 2 → ℝ) → ℂ) :
    IntegrableOn (fun y => f (y + c)) Q ↔ IntegrableOn f (Qz c) := by
  have := (measurePreserving_add_right (volume : Measure (Fin 2 → ℝ)) c).integrableOn_comp_preimage
    (MeasurableEquiv.addRight c).measurableEmbedding (f := f) (s := Qz c)
  rw [preim_Qz] at this; exact this

lemma zc_apply0 (z : ℤ × ℤ) : zc z 0 = z.1 := rfl
lemma zc_apply1 (z : ℤ × ℤ) : zc z 1 = z.2 := rfl

lemma Qz_disj {z z' : ℤ × ℤ} (h : z ≠ z') : Disjoint (Qz (zc z)) (Qz (zc z')) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  apply h
  have key : ∀ (m m' : ℤ) (r : ℝ), r - m ∈ Ioc (0 : ℝ) 1 → r - m' ∈ Ioc (0 : ℝ) 1 → m = m' := by
    intro m m' r h1 h2
    have e1 := (ioc_floor (-m) r).mp (by push_cast; convert h1 using 1; ring)
    have e2 := (ioc_floor (-m') r).mp (by push_cast; convert h2 using 1; ring)
    omega
  have a0 := key z.1 z'.1 (x 0) (hx 0) (hx' 0)
  have a1 := key z.2 z'.2 (x 1) (hx 1) (hx' 1)
  exact Prod.ext a0 a1

lemma Om_eq : Om = ⋃ z ∈ SZ, Qz (zc z) := by
  ext x
  simp only [Om, mem_setOf_eq, mem_iUnion]
  constructor
  · rintro ⟨z, hz, hx⟩
    rw [inS_iff, Finset.mem_coe] at hz
    exact ⟨z, hz, hx⟩
  · rintro ⟨z, hz, hx⟩
    refine ⟨z, ?_, hx⟩
    rw [inS_iff, Finset.mem_coe]; exact hz

lemma meas_Om : MeasurableSet Om := by
  rw [Om_eq]; exact Finset.measurableSet_biUnion _ (fun z _ => meas_Qz _)

lemma Om_bdd : Bornology.IsBounded Om := by
  apply (Metric.isBounded_Icc (0 : Fin 2 → ℝ) (fun _ => 3601)).subset
  intro x hx
  rcases hx with ⟨z, hz, hx⟩
  obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := hz
  have b0 := hx 0; have b1 := hx 1
  rw [zc_apply0] at b0; rw [zc_apply1] at b1
  have c1 : (0 : ℝ) ≤ z.1 := by exact_mod_cast h1
  have c2 : (z.1 : ℝ) ≤ 3599 := by exact_mod_cast (by omega : z.1 ≤ 3599)
  have c3 : (0 : ℝ) ≤ z.2 := by exact_mod_cast h3
  have c4 : (z.2 : ℝ) ≤ 719 := by exact_mod_cast (by omega : z.2 ≤ 719)
  simp only [mem_Ioc] at b0 b1
  constructor <;> intro i <;> fin_cases i <;> simp <;> linarith [b0.1, b0.2, b1.1, b1.2]

lemma SZ_nonempty : SZ.Nonempty := by
  rw [← Finset.card_pos, card_SZ]; norm_num

lemma Om_pos : 0 < volume Om := by
  obtain ⟨z, hz⟩ := SZ_nonempty
  have : Qz (zc z) ⊆ Om := by
    rw [Om_eq]; exact Set.subset_biUnion_of_mem (u := fun z => Qz (zc z)) (Finset.mem_coe.mpr hz)
  calc (0 : ENNReal) < 1 := by norm_num
    _ = volume (Qz (zc z)) := (vol_Qz _).symm
    _ ≤ volume Om := measure_mono this

lemma Om_fin : volume Om ≠ ⊤ := Om_bdd.measure_lt_top.ne

/-- integral over `Om` as a sum of integrals over the unit square. -/
lemma int_Om (f : (Fin 2 → ℝ) → ℂ) (hf : IntegrableOn f Om) :
    ∫ x in Om, f x = ∑ z ∈ SZ, ∫ y in Q, f (y + zc z) := by
  rw [Om_eq, integral_biUnion_finset SZ (fun z _ => meas_Qz _)
    (fun z _ z' _ h => Qz_disj h)]
  · apply Finset.sum_congr rfl; intro z _; exact trans_int _ _
  · intro z hz
    apply hf.mono_set
    rw [Om_eq]; exact Set.subset_biUnion_of_mem (u := fun z => Qz (zc z)) (Finset.mem_coe.mpr hz)

lemma ee_norm (θ : ℝ) : ‖ee θ‖ = 1 := by
  rw [ee, show 2 * (π : ℂ) * Complex.I * (θ : ℂ) = ((2 * π * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ee_conj (θ : ℝ) : (starRingEnd ℂ) (ee θ) = ee (-θ) := by
  rw [ee, ee, ← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, map_ofNat]

lemma ee_cont : Continuous ee := by unfold ee; fun_prop

lemma ec_eq (ξ x : Fin 2 → ℝ) : exponentialCharacter ξ x = ee (ξ 0 * x 0 + ξ 1 * x 1) := by
  simp only [exponentialCharacter, ee, Fin.sum_univ_two]

lemma int_Ioc_ee (m : ℤ) (hm : m ≠ 0) : ∫ t in Ioc (0 : ℝ) 1, ee (m * t) = 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hc : (2 * π * Complex.I * m : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hm]
  have := integral_exp_mul_complex (a := 0) (b := 1) hc
  simp only [ee]
  have e : ∀ t : ℝ, Complex.exp (2 * π * Complex.I * ((m * t : ℝ) : ℂ)) =
      Complex.exp (2 * π * Complex.I * m * t) := by intro t; push_cast; ring_nf
  simp_rw [e, this]
  have h1 : Complex.exp (2 * π * Complex.I * m * ((1 : ℝ) : ℂ)) = 1 := by
    have := ee_int m; simp only [ee] at this; rw [← this]; push_cast; ring_nf
  rw [h1]; simp

lemma int_Q_ee (m0 m1 : ℤ) (hm : m0 ≠ 0 ∨ m1 ≠ 0) :
    ∫ y in Q, ee (m0 * y 0 + m1 * y 1) = 0 := by
  rw [Q_pi, volume_pi, Measure.restrict_pi_pi]
  have : ∀ y : Fin 2 → ℝ, ee (m0 * y 0 + m1 * y 1) = ∏ i : Fin 2, ee (![(m0 : ℝ), m1] i * y i) := by
    intro y; rw [Fin.prod_univ_two, ← ee_add]; simp
  simp_rw [this]
  rw [integral_fintype_prod_eq_prod (fun i t => ee (![(m0 : ℝ), m1] i * t)), Fin.prod_univ_two]
  rcases hm with h | h
  · simp only [Matrix.cons_val_zero]; rw [int_Ioc_ee m0 h, zero_mul]
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
    rw [int_Ioc_ee m1 h, mul_zero]

end FG

end

-- ===== Part 7 =====
section

open MeasureTheory Set Real

namespace FG

noncomputable def γv (i : I) : Fin 2 → ℝ := ![γ1 i, γ2 i]

def Lam : Set (Fin 2 → ℝ) := {ξ | ∃ i : I, ∃ n : Fin 2 → ℤ, ξ = γv i + fun j => (n j : ℝ)}

instance finOm : IsFiniteMeasure (volume.restrict Om) := isFiniteMeasure_restrict.mpr Om_fin

lemma intOn_ee (a b : ℝ) : IntegrableOn (fun x : Fin 2 → ℝ => ee (a * x 0 + b * x 1)) Om := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact (ee_cont.comp (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => (ee_norm _).le)

lemma sum_SZ_SN (F : ℤ × ℤ → ℂ) : ∑ z ∈ SZ, F z = ∑ p ∈ SN, F (cZ p) := by
  rw [SZ_eq, Finset.sum_image (fun p _ q _ h => cZ_inj h)]

theorem orth_int {ξ1 ξ2 : Fin 2 → ℝ} (h1 : ξ1 ∈ Lam) (h2 : ξ2 ∈ Lam) (hne : ξ1 ≠ ξ2) :
    ∫ x in Om, (starRingEnd ℂ) (exponentialCharacter ξ1 x) * exponentialCharacter ξ2 x = 0 := by
  obtain ⟨i1, n1, rfl⟩ := h1
  obtain ⟨i2, n2, rfl⟩ := h2
  set d0 : ℝ := (γv i2 + fun j => (n2 j : ℝ)) 0 - (γv i1 + fun j => (n1 j : ℝ)) 0 with hd0
  set d1 : ℝ := (γv i2 + fun j => (n2 j : ℝ)) 1 - (γv i1 + fun j => (n1 j : ℝ)) 1 with hd1
  have hpt : ∀ x : Fin 2 → ℝ, (starRingEnd ℂ) (exponentialCharacter (γv i1 + fun j => (n1 j : ℝ)) x) *
      exponentialCharacter (γv i2 + fun j => (n2 j : ℝ)) x = ee (d0 * x 0 + d1 * x 1) := by
    intro x
    rw [ec_eq, ec_eq, ee_conj, ← ee_add]; congr 1; rw [hd0, hd1]; ring
  simp_rw [hpt]
  rw [int_Om _ (intOn_ee d0 d1)]
  have hsplit : ∀ z : ℤ × ℤ, ∫ y in Q, ee (d0 * (y + zc z) 0 + d1 * (y + zc z) 1) =
      ee (d0 * z.1 + d1 * z.2) * ∫ y in Q, ee (d0 * y 0 + d1 * y 1) := by
    intro z
    rw [← integral_const_mul]; congr 1; ext y
    rw [← ee_add]; congr 1; simp only [Pi.add_apply, zc_apply0, zc_apply1]; ring
  simp_rw [hsplit, ← Finset.sum_mul]
  by_cases hi : i1 = i2
  · subst hi
    have hn : n1 ≠ n2 := by
      intro e; apply hne; rw [e]
    have e0 : d0 = ((n2 0 - n1 0 : ℤ) : ℝ) := by rw [hd0]; simp
    have e1 : d1 = ((n2 1 - n1 1 : ℤ) : ℝ) := by rw [hd1]; simp
    rw [e0, e1, int_Q_ee, mul_zero]
    by_contra hc; rw [not_or, not_not, not_not] at hc
    apply hn; ext j; fin_cases j <;> simp <;> omega
  · have : ∑ z ∈ SZ, ee (d0 * z.1 + d1 * z.2) = 0 := by
      rw [sum_SZ_SN]
      have key : ∀ p : ℕ × ℕ, ee (d0 * ((cZ p).1 : ℝ) + d1 * ((cZ p).2 : ℝ)) =
          ee ((γ1 i2 - γ1 i1) * p.1 + (γ2 i2 - γ2 i1) * p.2) := by
        intro p
        have : d0 * ((cZ p).1 : ℝ) + d1 * ((cZ p).2 : ℝ) =
            ((γ1 i2 - γ1 i1) * p.1 + (γ2 i2 - γ2 i1) * p.2) +
              (((n2 0 - n1 0) * (p.1 : ℤ) + (n2 1 - n1 1) * (p.2 : ℤ) : ℤ) : ℝ) := by
          rw [hd0, hd1]; simp [cZ, γv]; ring
        rw [this, ee_add_int]
      simp_rw [key]
      exact S_orth i2 i1 (Ne.symm hi)
    rw [this, zero_mul]

lemma inner_L2 {f g : (Fin 2 → ℝ) → ℂ} (hf : MemLp f 2 (volume.restrict Om))
    (hg : MemLp g 2 (volume.restrict Om)) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x in Om, (starRingEnd ℂ) (f x) * g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

lemma card_I : Fintype.card I = 216000 := by simp [I, kk]

/-- an orthogonal square matrix is injective. -/
lemma LA (M : I → (ℤ × ℤ) → ℂ)
    (hM : ∀ i i', ∑ z ∈ SZ, M i z * (starRingEnd ℂ) (M i' z) = if i = i' then (216000 : ℂ) else 0)
    (v : ℤ × ℤ → ℂ) (hv : ∀ i, ∑ z ∈ SZ, M i z * v z = 0) : ∀ z ∈ SZ, v z = 0 := by
  classical
  have hc : Fintype.card I = Fintype.card SZ := by rw [card_I, Fintype.card_coe, card_SZ]
  let A : Matrix I SZ ℂ := Matrix.of (fun i a => M i a)
  let B : Matrix SZ I ℂ := Matrix.of (fun a i => (216000 : ℂ)⁻¹ * (starRingEnd ℂ) (M i a))
  have hAB : A * B = 1 := by
    ext i i'
    simp only [A, B, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply]
    have := hM i i'
    rw [← Finset.sum_coe_sort SZ] at this
    simp_rw [mul_left_comm _ ((216000 : ℂ)⁻¹), ← Finset.mul_sum, this]
    split_ifs <;> simp
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_card_eq I SZ ℂ (A := A) (B := B) hc).mp hAB
  intro z hz
  have hAv : A.mulVec (fun a : SZ => v a) = 0 := by
    ext i
    simp only [A, Matrix.mulVec, dotProduct, Pi.zero_apply, Matrix.of_apply]
    rw [Finset.sum_coe_sort SZ (fun z => M i z * v z)]; exact hv i
  have : (fun a : SZ => v a) = 0 := by
    rw [← Matrix.one_mulVec (fun a : SZ => v a), ← hBA, ← Matrix.mulVec_mulVec, hAv,
      Matrix.mulVec_zero]
  exact congrFun this ⟨z, hz⟩

end FG

end

-- ===== Part 8 =====
section

open MeasureTheory Set Real

namespace FG

section torus

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def S0 : Set (Fin 2 → ℝ) := {x | ∀ i, x i ∈ Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i + 1)}

lemma S0_eq : S0 = Q := by ext x; simp [S0, Q]

lemma meas_S0 : MeasurableSet S0 := by rw [S0_eq]; exact meas_Q

noncomputable def lift (w : UnitAddTorus (Fin 2)) : Fin 2 → ℝ :=
  ((UnitAddTorus.measurableEquivPiIoc (0 : Fin 2 → ℝ)) w).1

lemma lift_mp : MeasurePreserving lift volume (volume.restrict Q) := by
  have h1 := UnitAddTorus.measurePreserving_equivPiIoc (d := Fin 2) (0 : Fin 2 → ℝ)
  have h2 : MeasurePreserving (Subtype.val : S0 → (Fin 2 → ℝ))
      (Measure.comap Subtype.val volume) (volume.restrict S0) :=
    ⟨measurable_subtype_coe, map_comap_subtype_coe meas_S0 _⟩
  rw [← S0_eq]; exact h2.comp h1

lemma mF_eval (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    UnitAddTorus.mFourier n (fun i => (x i : UnitAddCircle)) =
      ee ((n 0 : ℝ) * x 0 + (n 1 : ℝ) * x 1) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two, fourier_coe_apply]
  rw [ee, ← Complex.exp_add]; congr 1; push_cast; ring

lemma lift_coe {x : Fin 2 → ℝ} (hx : x ∈ Q) : lift (fun i => (x i : UnitAddCircle)) = x := by
  ext i
  simp only [lift, UnitAddTorus.coe_measurableEquivPiIoc_apply]
  exact AddCircle.equivIoc_coe_of_mem (by simpa using hx i)

theorem fourier_unique (h : (Fin 2 → ℝ) → ℂ) (hs : StronglyMeasurable h)
    (hL : MemLp h 2 (volume.restrict Q))
    (hc : ∀ n : Fin 2 → ℤ, ∫ y in Q, ee (-((n 0 : ℝ) * y 0 + (n 1 : ℝ) * y 1)) * h y = 0) :
    h =ᵐ[volume.restrict Q] 0 := by
  have hG : MemLp (h ∘ lift) 2 volume := hL.comp_measurePreserving lift_mp
  have hcoef : ∀ n, UnitAddTorus.mFourierCoeff (h ∘ lift) n = 0 := by
    intro n
    rw [UnitAddTorus.mFourierCoeff_eq_integral _ n 0]
    change ∫ x in S0, _ = _
    rw [S0_eq, ← hc n]
    apply setIntegral_congr_fun meas_Q
    intro x hx
    simp only [Function.comp_apply, lift_coe hx, mF_eval, smul_eq_mul]
    congr 1; congr 1; simp only [Pi.neg_apply]; push_cast; ring
  have hP := UnitAddTorus.hasSum_sq_mFourierCoeff (hG.toLp (h ∘ lift))
  have hco : ∀ i, UnitAddTorus.mFourierCoeff (⇑(hG.toLp (h ∘ lift))) i = 0 := by
    intro i; rw [← hcoef i]
    unfold UnitAddTorus.mFourierCoeff
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with w hw
    rw [hw]
  simp only [hco, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hP
  have hint0 := hP.unique hasSum_zero
  have hint : ∫ t, ‖(h ∘ lift) t‖ ^ 2 = 0 := by
    rw [← hint0]; apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with w hw
    rw [hw]
  have hae := (integral_eq_zero_iff_of_nonneg (fun t => by positivity)
    ((memLp_two_iff_integrable_sq_norm hG.1).mp hG)).mp hint
  have hG0 : ∀ᵐ w ∂(volume : Measure (UnitAddTorus (Fin 2))), h (lift w) = 0 := by
    filter_upwards [hae] with w hw
    simpa using hw
  have hm : MeasurableSet {x | h x = 0} := hs.measurable (measurableSet_singleton 0)
  rw [← lift_mp.map_eq]
  show ∀ᵐ x ∂(Measure.map lift volume), h x = 0
  rw [ae_map_iff lift_mp.aemeasurable hm]
  exact hG0

end torus

end FG

end

-- ===== Part 9 =====
section

open MeasureTheory Set Real

namespace FG

lemma mp_Qz (c : Fin 2 → ℝ) :
    MeasurePreserving (fun y => y + c) (volume.restrict Q) (volume.restrict (Qz c)) := by
  have := (measurePreserving_add_right (volume : Measure (Fin 2 → ℝ)) c).restrict_preimage_emb
    (MeasurableEquiv.addRight c).measurableEmbedding (Qz c)
  rwa [preim_Qz] at this

lemma Qz_sub {z : ℤ × ℤ} (hz : z ∈ SZ) : Qz (zc z) ⊆ Om := by
  rw [Om_eq]; exact Set.subset_biUnion_of_mem (u := fun z => Qz (zc z)) (Finset.mem_coe.mpr hz)

lemma ee_ne (θ : ℝ) : ee θ ≠ 0 := by
  intro h; have := ee_norm θ; rw [h, norm_zero] at this; exact zero_ne_one this

lemma term_eq (i : I) (n : Fin 2 → ℤ) (z : ℤ × ℤ) (y : Fin 2 → ℝ) :
    ee (-((n 0 : ℝ) * y 0 + (n 1 : ℝ) * y 1)) *
      ee (-(γ1 i * y 0 + γ2 i * y 1 + (γ1 i * z.1 + γ2 i * z.2))) =
    (starRingEnd ℂ) (exponentialCharacter (γv i + fun j => (n j : ℝ)) (y + zc z)) := by
  rw [ec_eq, ee_conj, ← ee_add]
  rw [show -((γv i + fun j => (n j : ℝ)) 0 * (y + zc z) 0 + (γv i + fun j => (n j : ℝ)) 1 * (y + zc z) 1) =
      (-((n 0 : ℝ) * y 0 + (n 1 : ℝ) * y 1) + -(γ1 i * y 0 + γ2 i * y 1 + (γ1 i * z.1 + γ2 i * z.2))) +
        ((-(n 0 * z.1 + n 1 * z.2) : ℤ) : ℝ) by
    simp only [γv, Pi.add_apply, zc_apply0, zc_apply1, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    push_cast; ring, ee_add_int]

lemma hM_orth (i i' : I) :
    ∑ z ∈ SZ, ee (-(γ1 i * z.1 + γ2 i * z.2)) * (starRingEnd ℂ) (ee (-(γ1 i' * z.1 + γ2 i' * z.2))) =
      if i = i' then (216000 : ℂ) else 0 := by
  have e : ∀ z : ℤ × ℤ, ee (-(γ1 i * z.1 + γ2 i * z.2)) * (starRingEnd ℂ) (ee (-(γ1 i' * z.1 + γ2 i' * z.2)))
      = ee ((γ1 i' - γ1 i) * z.1 + (γ2 i' - γ2 i) * z.2) := by
    intro z; rw [ee_conj, ← ee_add]; congr 1; ring
  simp_rw [e]
  split_ifs with h
  · subst h; simp [card_SZ, ee_zero]
  · rw [sum_SZ_SN]
    have : ∀ p : ℕ × ℕ, ee ((γ1 i' - γ1 i) * ((cZ p).1 : ℝ) + (γ2 i' - γ2 i) * ((cZ p).2 : ℝ)) =
        ee ((γ1 i' - γ1 i) * p.1 + (γ2 i' - γ2 i) * p.2) := by
      intro p; simp [cZ]
    simp_rw [this]
    exact S_orth i' i (Ne.symm h)

theorem Om_spectral : isSpectral Om := by
  refine ⟨Lam, meas_Om.nullMeasurableSet, Om_pos, Om_fin, ?_, ?_⟩
  · intro ξ1 h1 ξ2 h2 hne
    rw [inner_L2]; exact orth_int h1 h2 hne
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro g hg
  have hort : ∀ ξ ∈ Lam, ∫ x in Om, (starRingEnd ℂ) (exponentialCharacter ξ x) * g x = 0 := by
    intro ξ hξ
    have hmem := Submodule.subset_span (R := ℂ) (Set.mem_range_self
      (f := fun ξ : Lam => (exponentialCharacter_memLp Om_fin ξ.1).toLp (exponentialCharacter ξ.1))
      ⟨ξ, hξ⟩)
    have := Submodule.inner_right_of_mem_orthogonal hmem hg
    rw [L2.inner_def] at this
    rw [← this]
    apply integral_congr_ae
    filter_upwards [(exponentialCharacter_memLp Om_fin ξ).coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply, mul_comm]
  have hgL : MemLp (⇑g) 2 (volume.restrict Om) := Lp.memLp g
  set gm := hgL.1.mk with hgm_def
  have hgm : StronglyMeasurable gm := hgL.1.stronglyMeasurable_mk
  have hgae : (⇑g) =ᵐ[volume.restrict Om] gm := hgL.1.ae_eq_mk
  have hgmL : MemLp gm 2 (volume.restrict Om) := hgL.ae_eq hgae
  have hort' : ∀ ξ ∈ Lam, ∫ x in Om, (starRingEnd ℂ) (exponentialCharacter ξ x) * gm x = 0 := by
    intro ξ hξ; rw [← hort ξ hξ]
    apply integral_congr_ae
    filter_upwards [hgae] with x hx; rw [hx]
  have hk : ∀ z ∈ SZ, MemLp (fun y => gm (y + zc z)) 2 (volume.restrict Q) := by
    intro z hz
    have h1 : MemLp gm 2 (volume.restrict (Qz (zc z))) :=
      hgmL.mono_measure (Measure.restrict_mono (Qz_sub hz) le_rfl)
    exact h1.comp_measurePreserving (mp_Qz (zc z))
  have hgmI : Integrable gm (volume.restrict Om) := hgmL.integrable one_le_two
  -- the functions to which Fourier uniqueness is applied
  let T : I → (ℤ × ℤ) → (Fin 2 → ℝ) → ℂ := fun i z y =>
    ee (-(γ1 i * y 0 + γ2 i * y 1 + (γ1 i * z.1 + γ2 i * z.2))) * gm (y + zc z)
  have hTm : ∀ i z, StronglyMeasurable (T i z) := by
    intro i z
    exact ((ee_cont.comp (by fun_prop)).stronglyMeasurable).mul
      (hgm.comp_measurable (measurable_add_const _))
  have hTL : ∀ i, ∀ z ∈ SZ, MemLp (T i z) 2 (volume.restrict Q) := by
    intro i z hz
    refine (hk z hz).of_le (hTm i z).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro y; simp only [T, norm_mul, ee_norm, one_mul, le_refl]
  have hH : ∀ i, (fun y => ∑ z ∈ SZ, T i z y) =ᵐ[volume.restrict Q] 0 := by
    intro i
    apply fourier_unique
    · exact Finset.stronglyMeasurable_fun_sum _ (fun z _ => hTm i z)
    · exact memLp_finsetSum _ (hTL i)
    · intro n
      have hξ : (γv i + fun j => (n j : ℝ)) ∈ Lam := ⟨i, n, rfl⟩
      have hI : IntegrableOn (fun x => (starRingEnd ℂ) (exponentialCharacter
          (γv i + fun j => (n j : ℝ)) x) * gm x) Om :=
        hgmI.bdd_mul (c := 1)
          ((Complex.continuous_conj.comp (continuous_exponentialCharacter _)).aestronglyMeasurable)
          (Filter.Eventually.of_forall (fun x => by
            rw [RCLike.norm_conj, norm_exponentialCharacter]))
      rw [← hort' _ hξ, int_Om _ hI]
      rw [← integral_finsetSum]
      · apply integral_congr_ae
        filter_upwards with y
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro z _
        simp only [T]; rw [← mul_assoc, term_eq]
      · intro z hz
        exact (trans_intOn (zc z) _).mpr (hI.mono_set (Qz_sub hz))
  have hz0 : ∀ᵐ y ∂(volume.restrict Q), ∀ z ∈ SZ, gm (y + zc z) = 0 := by
    have hall : ∀ᵐ y ∂(volume.restrict Q), ∀ i, ∑ z ∈ SZ, T i z y = 0 := by
      rw [ae_all_iff]; intro i; filter_upwards [hH i] with y hy; exact hy
    filter_upwards [hall] with y hy
    apply LA (fun i z => ee (-(γ1 i * z.1 + γ2 i * z.2))) hM_orth (fun z => gm (y + zc z))
    intro i
    have := hy i
    simp only [T] at this
    have e : ∀ z : ℤ × ℤ, ee (-(γ1 i * y 0 + γ2 i * y 1 + (γ1 i * z.1 + γ2 i * z.2))) * gm (y + zc z)
        = ee (-(γ1 i * y 0 + γ2 i * y 1)) * (ee (-(γ1 i * z.1 + γ2 i * z.2)) * gm (y + zc z)) := by
      intro z; rw [← mul_assoc, ← ee_add]; congr 2; ring
    simp_rw [e, ← Finset.mul_sum] at this
    exact (mul_eq_zero.mp this).resolve_left (ee_ne _)
  have hgm0 : gm =ᵐ[volume.restrict Om] 0 := by
    rw [Om_eq]
    show ∀ᵐ x ∂(volume.restrict (⋃ z ∈ SZ, Qz (zc z))), gm x = 0
    rw [ae_restrict_biUnion_finset_iff]
    intro z hz
    have hms : MeasurableSet {x | gm x = 0} := hgm.measurable (measurableSet_singleton 0)
    rw [← (mp_Qz (zc z)).map_eq, ae_map_iff (mp_Qz _).aemeasurable hms]
    filter_upwards [hz0] with y hy; exact hy z hz
  rw [Lp.eq_zero_iff_ae_eq_zero]
  exact hgae.trans hgm0

end FG

theorem OMA.disproof : ¬ (type_of% @Fuglede.FugledeConjecture.variants.dim_2) := by
  intro h
  exact FG.Om_not_tile ((h FG.Om FG.Om_bdd FG.meas_Om FG.Om_pos).mp FG.Om_spectral)

end
