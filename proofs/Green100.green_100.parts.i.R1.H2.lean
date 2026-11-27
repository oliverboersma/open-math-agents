import OMAReductions.R_Green100_green_100_parts_i_R1
import Mathlib

/-!
# Gromov-Weiss surjunctivity for linear cellular automata over finite fields

Step `Green100.green_100.parts.i.R1.H2`: if `G` is a sofic group and `K` is a finite field, then
every injective linear cellular automaton `x ↦ (g ↦ ∑ u, b_u * x (g * u))` on `G → K` is
surjective.

Proof:
1. Compactness of `G → K` (with discrete `K`) turns injectivity into local injectivity on a finite
   memory window `M`, and turns non-surjectivity into a finite window `E` with a nonzero linear
   annihilator `λ` on the image of `τ` restricted to `E`.
2. Tensor-power amplification of `IsSofic G` boosts the `1/4` Hamming separation to `1 - δ`.
3. On a finite sofic model `Fin N`, the finite linear map `τ_N` satisfies:
   - `dim (ker τ_N) ≤ C₁ * δ * N` (via local injectivity on `M`), hence `dim (range τ_N) ≥ (1 - C₁ * δ) * N`;
   - `dim (range τ_N) ≤ N - |A|` for a maximal packing `A` of disjoint `E`-translates, with
     `|A| ≥ (1 - C₂ * δ) * N / |E|²`.
   Choosing `δ` small enough yields a contradiction.
-/

namespace Green100Surjunctivity

open Green100 Finset

section AmplifiedSofic

private lemma card_filter_pi_eq {k n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    (Finset.univ.filter fun f : Fin k → Fin n => ∀ j : Fin k, P (f j)).card =
      (Finset.univ.filter P).card ^ k := by
  classical
  have h1 : (Finset.univ.filter fun f : Fin k → Fin n => ∀ j : Fin k, P (f j)) =
      Fintype.piFinset (fun _ : Fin k => Finset.univ.filter P) := by
    ext f
    simp [Fintype.mem_piFinset]
  rw [h1, Fintype.card_piFinset]
  simp

private lemma card_filter_pi_exists_le {k n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    (Finset.univ.filter fun f : Fin k → Fin n => ∃ j : Fin k, P (f j)).card ≤
      k * (Finset.univ.filter P).card * n ^ (k - 1) := by
  classical
  cases k with
  | zero =>
    simp
  | succ m =>
    have hsub : (Finset.univ.filter fun f : Fin (m + 1) → Fin n => ∃ j, P (f j)) ⊆
        Finset.univ.biUnion fun j : Fin (m + 1) =>
          Finset.univ.filter fun f : Fin (m + 1) → Fin n => P (f j) := by
      intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hf ⊢
      exact hf
    have hcard_j : ∀ j : Fin (m + 1),
        (Finset.univ.filter fun f : Fin (m + 1) → Fin n => P (f j)).card =
          (Finset.univ.filter P).card * n ^ m := by
      intro j
      have h1 : (Finset.univ.filter fun f : Fin (m + 1) → Fin n => P (f j)) =
          Fintype.piFinset (fun i : Fin (m + 1) => if i = j then Finset.univ.filter P else Finset.univ) := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
        constructor
        · intro h i
          split_ifs with hij
          · subst hij; simpa using h
          · exact Finset.mem_univ _
        · intro h
          have hj := h j
          simpa using hj
      rw [h1, Fintype.card_piFinset]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
      have hrest : ∏ i ∈ Finset.univ.erase j,
          (if i = j then Finset.univ.filter P else Finset.univ).card = n ^ m := by
        calc ∏ i ∈ Finset.univ.erase j,
              (if i = j then Finset.univ.filter P else Finset.univ).card
            = ∏ _i ∈ Finset.univ.erase j, n := by
              refine Finset.prod_congr rfl fun i hi => ?_
              have hne : i ≠ j := (Finset.mem_erase.mp hi).1
              simp [hne]
          _ = n ^ m := by simp [Finset.card_erase_of_mem]
      simp [hrest]
    calc (Finset.univ.filter fun f : Fin (m + 1) → Fin n => ∃ j, P (f j)).card
        ≤ ∑ j : Fin (m + 1), (Finset.univ.filter fun f : Fin (m + 1) → Fin n => P (f j)).card :=
          (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ = ∑ _j : Fin (m + 1), (Finset.univ.filter P).card * n ^ m := by
          refine Finset.sum_congr rfl fun j _ => hcard_j j
      _ = (m + 1) * (Finset.univ.filter P).card * n ^ m := by
          simp [mul_assoc]

private lemma isSofic_amplified {G : Type} [Group G] [Nontrivial G] (hsofic : IsSofic G)
    (F : Finset G) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (N : ℕ) (θ : G → Equiv.Perm (Fin N)),
      0 < N ∧
      (∀ g ∈ F, ∀ h ∈ F, g * h ∈ F → hammingDistNorm (θ g * θ h) (θ (g * h)) < δ) ∧
      (1 ∈ F → hammingDistNorm (θ 1) 1 < δ) ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → (1 - δ : ℝ) < hammingDistNorm (θ x) (θ y)) := by
  classical
  obtain ⟨g₀, g₁, hg01⟩ := exists_pair_ne G
  let F' : Finset G := insert g₀ (insert g₁ F)
  obtain ⟨k0, hk0⟩ := exists_pow_lt_of_lt_one hδ (show (3 / 4 : ℝ) < 1 by norm_num)
  let k : ℕ := k0 + 1
  have hk_pow : (3 / 4 : ℝ) ^ k < δ := by
    calc (3 / 4 : ℝ) ^ k = (3 / 4 : ℝ) ^ k0 * (3 / 4 : ℝ) := by simp [k, pow_succ]
      _ ≤ (3 / 4 : ℝ) ^ k0 * 1 := by gcongr; norm_num
      _ = (3 / 4 : ℝ) ^ k0 := mul_one _
      _ < δ := hk0
  have hε : 0 < δ / (k : ℝ) := div_pos hδ (by positivity)
  obtain ⟨n₀, θ₀, hmul₀, hone₀, hsep₀⟩ := hsofic F' (δ / (k : ℝ)) hε
  have hn₀_pos : 0 < n₀ := by
    by_contra h0
    have hn0 : n₀ = 0 := by omega
    have h0r : (n₀ : ℝ) = 0 := by exact_mod_cast hn0
    have hsep := hsep₀ g₀ (by simp [F']) g₁ (by simp [F']) hg01
    rw [hammingDistNorm, h0r] at hsep
    norm_num at hsep
  let N : ℕ := n₀ ^ k
  have hN_pos : 0 < N := pow_pos hn₀_pos k
  let e : (Fin k → Fin n₀) ≃ Fin N := Fintype.equivFinOfCardEq (by simp [N])
  let θ : G → Equiv.Perm (Fin N) := fun g =>
    e.symm.trans ((Equiv.piCongrRight fun _ => θ₀ g).trans e)
  have hθ_apply : ∀ (g : G) (f : Fin k → Fin n₀),
      θ g (e f) = e (fun j => θ₀ g (f j)) := fun g f => by
    simp only [θ, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  have hdist_le : ∀ (σ τ : Equiv.Perm (Fin n₀)),
      let σ' : Equiv.Perm (Fin N) := e.symm.trans ((Equiv.piCongrRight fun _ => σ).trans e)
      let τ' : Equiv.Perm (Fin N) := e.symm.trans ((Equiv.piCongrRight fun _ => τ).trans e)
      hammingDistNorm σ' τ' ≤ (k : ℝ) * hammingDistNorm σ τ := by
    intro σ τ σ' τ'
    have hcard : hammingDist (⇑σ') (⇑τ') ≤ k * hammingDist (⇑σ) (⇑τ) * n₀ ^ (k - 1) := by
      have heq : hammingDist (⇑σ') (⇑τ') =
          (Finset.univ.filter fun f : Fin k → Fin n₀ => ∃ j : Fin k, σ (f j) ≠ τ (f j)).card := by
        rw [hammingDist]
        refine Finset.card_bij (fun i _ => e.symm i) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          by_contra hall
          push_neg at hall
          apply hi
          have : (Equiv.piCongrRight fun _ => σ) (e.symm i) =
              (Equiv.piCongrRight fun _ => τ) (e.symm i) := funext hall
          exact congrArg e this
        · intro i₁ _ i₂ _ h; exact e.symm.injective h
        · intro f hf
          refine ⟨e f, ?_, e.symm_apply_apply f⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
          obtain ⟨j, hj⟩ := hf
          intro heq'
          have h1 := e.injective heq'
          exact hj (by simpa using congrFun h1 j)
      rw [heq]
      simpa [hammingDist] using card_filter_pi_exists_le (k := k) (n := n₀) (fun i => σ i ≠ τ i)
    rw [hammingDistNorm, hammingDistNorm]
    have hcast : (hammingDist (⇑σ') (⇑τ') : ℝ) ≤ (k : ℝ) * (hammingDist (⇑σ) (⇑τ) : ℝ) * (n₀ : ℝ) ^ (k - 1) := by
      exact_mod_cast hcard
    have hN_eq : (N : ℝ) = (n₀ : ℝ) * (n₀ : ℝ) ^ (k - 1) := by
      simp only [N, k, Nat.add_sub_cancel, pow_succ, Nat.cast_mul, Nat.cast_pow]
      ring
    have hn0_r : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀_pos
    have hN_r : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
    rw [div_le_iff₀ hN_r]
    calc (hammingDist (⇑σ') (⇑τ') : ℝ)
        ≤ (k : ℝ) * (hammingDist (⇑σ) (⇑τ) : ℝ) * (n₀ : ℝ) ^ (k - 1) := hcast
      _ = (k : ℝ) * ((hammingDist (⇑σ) (⇑τ) : ℝ) / (n₀ : ℝ)) * (N : ℝ) := by
          rw [hN_eq]; field_simp [hn0_r.ne']
  refine ⟨N, θ, hN_pos, ?_, ?_, ?_⟩
  · intro g hg h hh hgh
    have hcomp : θ g * θ h = e.symm.trans ((Equiv.piCongrRight fun _ => θ₀ g * θ₀ h).trans e) := by
      refine Equiv.ext fun i => ?_
      obtain ⟨f, rfl⟩ := e.surjective i
      simp only [Equiv.Perm.mul_apply, θ, Equiv.trans_apply, Equiv.symm_apply_apply,
        Equiv.piCongrRight_apply]
      rfl
    rw [hcomp]
    have h1 := hdist_le (θ₀ g * θ₀ h) (θ₀ (g * h))
    have h2 := hmul₀ g (by simp [F', hg]) h (by simp [F', hh]) (by simp [F', hgh])
    have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
    calc hammingDistNorm _ (θ (g * h))
        ≤ (k : ℝ) * hammingDistNorm (θ₀ g * θ₀ h) (θ₀ (g * h)) := h1
      _ < (k : ℝ) * (δ / (k : ℝ)) := mul_lt_mul_of_pos_left h2 hk_pos
      _ = δ := mul_div_cancel₀ δ hk_pos.ne'
  · intro h1F
    have hone_eq : (1 : Equiv.Perm (Fin N)) = e.symm.trans ((Equiv.piCongrRight fun _ => (1 : Equiv.Perm (Fin n₀))).trans e) := by
      refine Equiv.ext fun i => ?_
      obtain ⟨f, rfl⟩ := e.surjective i
      simp only [Equiv.Perm.coe_one, id_eq, Equiv.trans_apply, Equiv.symm_apply_apply,
        Equiv.piCongrRight_apply]
      rfl
    rw [hone_eq]
    have h1 := hdist_le (θ₀ 1) 1
    have h2 := hone₀ (by simp [F', h1F])
    have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
    calc hammingDistNorm (θ 1) _
        ≤ (k : ℝ) * hammingDistNorm (θ₀ 1) 1 := h1
      _ < (k : ℝ) * (δ / (k : ℝ)) := mul_lt_mul_of_pos_left h2 hk_pos
      _ = δ := mul_div_cancel₀ δ hk_pos.ne'
  · intro x hx y hy hxy
    have hsep := hsep₀ x (by simp [F', hx]) y (by simp [F', hy]) hxy
    have hagree : (Finset.univ.filter fun i : Fin N => θ x i = θ y i).card =
        (n₀ - hammingDist (⇑(θ₀ x)) (⇑(θ₀ y))) ^ k := by
      have hbij : (Finset.univ.filter fun i : Fin N => θ x i = θ y i).card =
          (Finset.univ.filter fun f : Fin k → Fin n₀ => ∀ j : Fin k, θ₀ x (f j) = θ₀ y (f j)).card := by
        refine Finset.card_bij (fun i _ => e.symm i) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          have := e.injective hi
          intro j
          simpa using congrFun this j
        · intro i₁ _ i₂ _ h; exact e.symm.injective h
        · intro f hf
          refine ⟨e f, ?_, e.symm_apply_apply f⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
          rw [hθ_apply, hθ_apply]
          exact congrArg e (funext hf)
      rw [hbij, card_filter_pi_eq (P := fun i => θ₀ x i = θ₀ y i)]
      congr 1
      have hcompl := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n₀)))
        (p := fun i => θ₀ x i = θ₀ y i)
      simp only [Finset.card_univ, Fintype.card_fin] at hcompl
      have hne_eq : (Finset.univ.filter fun i : Fin n₀ => ¬ θ₀ x i = θ₀ y i).card =
          hammingDist (⇑(θ₀ x)) (⇑(θ₀ y)) := rfl
      omega
    have hcomplN := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (p := fun i => θ x i = θ y i)
    simp only [Finset.card_univ, Fintype.card_fin] at hcomplN
    have hdistN : hammingDist (⇑(θ x)) (⇑(θ y)) = N - (n₀ - hammingDist (⇑(θ₀ x)) (⇑(θ₀ y))) ^ k := by
      have hne_eq : (Finset.univ.filter fun i : Fin N => ¬ θ x i = θ y i).card =
          hammingDist (⇑(θ x)) (⇑(θ y)) := rfl
      omega
    have hle_n0 : hammingDist (⇑(θ₀ x)) (⇑(θ₀ y)) ≤ n₀ := by
      calc hammingDist (⇑(θ₀ x)) (⇑(θ₀ y)) ≤ (Finset.univ : Finset (Fin n₀)).card := Finset.card_filter_le _ _
        _ = n₀ := by simp
    have hfrac : ((n₀ - hammingDist (⇑(θ₀ x)) (⇑(θ₀ y)) : ℕ) : ℝ) / (n₀ : ℝ) ≤ 3 / 4 := by
      rw [Nat.cast_sub hle_n0, sub_div, div_self (by exact_mod_cast hn₀_pos.ne')]
      have : (1 / 4 : ℝ) ≤ (hammingDist (⇑(θ₀ x)) (⇑(θ₀ y)) : ℝ) / (n₀ : ℝ) := hsep
      linarith
    have hpow_le : (((n₀ - hammingDist (⇑(θ₀ x)) (⇑(θ₀ y)) : ℕ) : ℝ) ^ k) / (N : ℝ) ≤ (3 / 4 : ℝ) ^ k := by
      rw [show (N : ℝ) = (n₀ : ℝ) ^ k by simp [N], ← div_pow]
      exact pow_le_pow_left₀ (by positivity) hfrac k
    have hle_N : (n₀ - hammingDist (⇑(θ₀ x)) (⇑(θ₀ y))) ^ k ≤ N := by
      exact Nat.pow_le_pow_left (Nat.sub_le _ _) k
    rw [hammingDistNorm, hdistN, Nat.cast_sub hle_N, sub_div,
      div_self (by exact_mod_cast hN_pos.ne'), Nat.cast_pow]
    linarith

end AmplifiedSofic

section MainProof

private def tau {K : Type} [Field K] {G : Type} [Group G] (b : MonoidAlgebra K G) :
    (G → K) →ₗ[K] (G → K) where
  toFun x g := b.coeff.sum fun u c => c * x (g * u)
  map_add' x y := by
    ext g
    simp only [Pi.add_apply, Finsupp.sum, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring

private lemma local_injective {K : Type} [Field K] [Fintype K] {G : Type} [Group G]
    (b : MonoidAlgebra K G) (hinj : Function.Injective (tau b)) :
    ∃ M : Finset G, 1 ∈ M ∧ ∀ x : G → K, (∀ g ∈ M, tau b x g = 0) → x 1 = 0 := by
  classical
  letI : TopologicalSpace K := ⊥
  haveI : DiscreteTopology K := ⟨rfl⟩
  haveI : CompactSpace K := Finite.compactSpace
  haveI : T2Space K := inferInstance
  have hcont_eval : ∀ g : G, Continuous (fun x : G → K => x g) := fun g => continuous_apply g
  have hcont_tau : ∀ g : G, Continuous (fun x : G → K => tau b x g) := by
    intro g
    change Continuous (fun x : G → K => ∑ u ∈ b.coeff.support, b.coeff u * x (g * u))
    exact continuous_finset_sum _ fun u _ => continuous_const.mul (continuous_apply (g * u))
  by_contra hno
  push_neg at hno
  let C : Finset G → Set (G → K) := fun M =>
    {x | x 1 ≠ 0 ∧ ∀ g ∈ M, tau b x g = 0}
  have hC_ne : ∀ M : Finset G, (C M).Nonempty := by
    intro M
    obtain ⟨x, hx1, hx2⟩ := hno (insert 1 M) (by simp)
    exact ⟨x, hx2, fun g hg => hx1 g (by simp [hg])⟩
  have hC_closed : ∀ M : Finset G, IsClosed (C M) := by
    intro M
    have h1 : IsClosed {x : G → K | x 1 ≠ 0} :=
      (isClosed_discrete ({0}ᶜ : Set K)).preimage (hcont_eval 1)
    have h2 : IsClosed {x : G → K | ∀ g ∈ M, tau b x g = 0} := by
      have : {x : G → K | ∀ g ∈ M, tau b x g = 0} = ⋂ g ∈ M, {x | tau b x g = 0} := by
        ext x; simp
      rw [this]
      exact isClosed_biInter fun g _ => isClosed_eq (hcont_tau g) continuous_const
    exact h1.inter h2
  have hdir : Directed (· ⊇ ·) C := by
    intro M₁ M₂
    refine ⟨M₁ ∪ M₂, ?_, ?_⟩
    · intro x hx; exact ⟨hx.1, fun g hg => hx.2 g (Finset.mem_union_left _ hg)⟩
    · intro x hx; exact ⟨hx.1, fun g hg => hx.2 g (Finset.mem_union_right _ hg)⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    C hdir hC_ne (fun M => (hC_closed M).isCompact) hC_closed
  have hx1 : x 1 ≠ 0 := (Set.mem_iInter.mp hx ∅).1
  have hx_ker : tau b x = 0 := by
    ext g
    exact (Set.mem_iInter.mp hx {g}).2 g (by simp)
  have hx0 : x = 0 := hinj (by rw [hx_ker, map_zero])
  exact hx1 (by simp [hx0])

private lemma exists_non_surj_window {K : Type} [Field K] [Fintype K] {G : Type} [Group G]
    (b : MonoidAlgebra K G) (hnot_surj : ¬ Function.Surjective (tau b)) :
    ∃ (E : Finset G), E.Nonempty ∧
      ∃ (c : E → K), (∃ g₀ : E, c g₀ ≠ 0) ∧
        ∀ x : G → K, ∑ g : E, c g * tau b x g.1 = 0 := by
  classical
  letI : TopologicalSpace K := ⊥
  haveI : DiscreteTopology K := ⟨rfl⟩
  haveI : CompactSpace K := Finite.compactSpace
  haveI : T2Space K := inferInstance
  have hcont : Continuous (tau b) := by
    refine continuous_pi fun g => ?_
    change Continuous (fun x : G → K => ∑ u ∈ b.coeff.support, b.coeff u * x (g * u))
    exact continuous_finset_sum _ fun u _ => continuous_const.mul (continuous_apply (g * u))
  have hclosed : IsClosed (Set.range (tau b)) := by
    simpa [Set.image_univ] using (isCompact_univ.image hcont).isClosed
  have hex_y : ∃ y : G → K, y ∉ Set.range (tau b) := by
    by_contra h; push_neg at h; exact hnot_surj h
  obtain ⟨y, hy⟩ := hex_y
  have hopen : IsOpen (Set.range (tau b))ᶜ := hclosed.isOpen_compl
  rw [isOpen_pi_iff] at hopen
  obtain ⟨E, U, hU, hsub⟩ := hopen y hy
  have hnot_surj_E : ¬ Function.Surjective (fun x : G → K => fun g : E => tau b x g.1) := by
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj (fun g => y g.1)
    have hxU : tau b x ∈ Set.pi (E : Set G) U := by
      intro g hg
      have hEq : tau b x g = y g := congrFun hx ⟨g, hg⟩
      rw [hEq]
      exact (hU g hg).2
    exact hsub hxU ⟨x, rfl⟩
  have hE_ne : E.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hnot_surj_E
    intro f
    refine ⟨0, funext fun ⟨g, hg⟩ => ?_⟩
    simp [h] at hg
  let Φ : (G → K) →ₗ[K] (E → K) :=
    { toFun := fun x g => tau b x g.1
      map_add' := fun x₁ x₂ => by ext g; simp [map_add]
      map_smul' := fun a x => by ext g; simp [map_smul] }
  have hrange_ne : LinearMap.range Φ ≠ ⊤ := by
    intro h
    exact hnot_surj_E (LinearMap.range_eq_top.mp h)
  have hlt : Module.finrank K (LinearMap.range Φ) < Module.finrank K (E → K) :=
    Submodule.finrank_lt hrange_ne
  let Q := (E → K) ⧸ LinearMap.range Φ
  have hQ_pos : 0 < Module.finrank K Q := by
    have h : Module.finrank K Q + Module.finrank K (LinearMap.range Φ) =
        Module.finrank K (E → K) := Submodule.finrank_quotient_add_finrank (LinearMap.range Φ)
    omega
  let bQ := Module.finBasis K Q
  let ψ : Q →ₗ[K] K :=
    { toFun := fun q => bQ.repr q ⟨0, hQ_pos⟩
      map_add' := fun q₁ q₂ => by simp
      map_smul' := fun a q => by simp }
  let lam : (E → K) →ₗ[K] K := ψ.comp (LinearMap.range Φ).mkQ
  have hlam_ne : lam ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := Submodule.mkQ_surjective (LinearMap.range Φ) (bQ ⟨0, hQ_pos⟩)
    have h1 : lam v = 0 := by rw [h0]; rfl
    have h2 : lam v = 1 := by
      simp [lam, ψ, hv]
    exact one_ne_zero (h2.symm.trans h1)
  let c : E → K := fun g => lam (Pi.single g 1)
  have hc_ne : ∃ g₀ : E, c g₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hlam_ne
    refine LinearMap.ext fun v => ?_
    have hv : v = ∑ g : E, v g • Pi.single g (1 : K) := by
      ext g'
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [map_smul, show lam (Pi.single g 1) = c g from rfl, hall g, smul_zero]
  refine ⟨E, hE_ne, c, hc_ne, fun x => ?_⟩
  have hPhi : Φ x = ∑ g : E, (tau b x g.1) • Pi.single g (1 : K) := by
    ext g'
    simp [Φ, Finset.sum_apply, Pi.single_apply]
  have hmk : (LinearMap.range Φ).mkQ (Φ x) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
  have h0 : lam (Φ x) = 0 := by
    simp [lam, hmk]
  rw [hPhi, map_sum] at h0
  simpa [c, map_smul, smul_eq_mul, mul_comm] using h0

private lemma exists_maximal_packing {N : ℕ} {V : Finset (Fin N)} (B : Fin N → Finset (Fin N))
    (hB_ne : ∀ i ∈ V, (B i).Nonempty) :
    ∃ A : Finset (Fin N), A ⊆ V ∧
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ → Disjoint (B a₁) (B a₂)) ∧
      (∀ i ∈ V, ∃ a ∈ A, ¬ Disjoint (B i) (B a)) := by
  classical
  let P : Finset (Finset (Fin N)) :=
    V.powerset.filter fun A => ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ → Disjoint (B a₁) (B a₂)
  have hP_ne : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨A, hAP, hAmax⟩ := Finset.exists_max_image P Finset.card hP_ne
  simp only [P, Finset.mem_filter, Finset.mem_powerset] at hAP
  refine ⟨A, hAP.1, hAP.2, ?_⟩
  intro i hi
  by_contra hdisj
  push_neg at hdisj
  have hiA : i ∉ A := by
    intro hiA
    have hd := hdisj i hiA
    rw [disjoint_self, Finset.bot_eq_empty] at hd
    exact (hB_ne i hi).ne_empty hd
  have hmem : insert i A ∈ P := by
    simp only [P, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset_iff.mpr ⟨hi, hAP.1⟩, ?_⟩
    intro a₁ ha₁ a₂ ha₂ hne
    rcases Finset.mem_insert.mp ha₁ with rfl | ha₁' <;>
      rcases Finset.mem_insert.mp ha₂ with rfl | ha₂'
    · exact absurd rfl hne
    · exact hdisj a₂ ha₂'
    · exact (hdisj a₁ ha₁').symm
    · exact hAP.2 a₁ ha₁' a₂ ha₂' hne
  have hle := hAmax (insert i A) hmem
  rw [Finset.card_insert_of_notMem hiA] at hle
  omega

private lemma card_inv_ne_eq_hammingDist {N : ℕ} (σ τ : Equiv.Perm (Fin N)) :
    (Finset.univ.filter fun i : Fin N => σ⁻¹ i ≠ τ⁻¹ i).card = hammingDist (⇑σ) (⇑τ) := by
  classical
  rw [hammingDist]
  refine Finset.card_bij (fun i _ => τ⁻¹ i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro h
    apply hi
    have := congrArg (⇑(σ⁻¹)) h
    simpa using this.symm
  · intro i₁ _ i₂ _ h
    exact (τ⁻¹ : Equiv.Perm (Fin N)).injective h
  · intro j hj
    refine ⟨τ j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    intro h
    apply hj
    have := congrArg σ h
    simpa using this.symm

private lemma card_inv_eq_eq_sub_hammingDist {N : ℕ} (σ τ : Equiv.Perm (Fin N)) :
    (Finset.univ.filter fun i : Fin N => σ⁻¹ i = τ⁻¹ i).card = N - hammingDist (⇑σ) (⇑τ) := by
  classical
  have hcompl := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (p := fun i => σ⁻¹ i = τ⁻¹ i)
  simp only [Finset.card_univ, Fintype.card_fin] at hcompl
  have hne := card_inv_ne_eq_hammingDist σ τ
  change (Finset.univ.filter fun i : Fin N => σ⁻¹ i = τ⁻¹ i).card +
    (Finset.univ.filter fun i : Fin N => σ⁻¹ i ≠ τ⁻¹ i).card = N at hcompl
  omega

private lemma card_inv_mul_ne_eq_hammingDist {N : ℕ} (σ₁ σ₂ σ₁₂ : Equiv.Perm (Fin N)) :
    (Finset.univ.filter fun i : Fin N => σ₁₂⁻¹ i ≠ σ₂⁻¹ (σ₁⁻¹ i)).card =
      hammingDist (⇑(σ₁ * σ₂)) (⇑σ₁₂) := by
  classical
  have hset : (Finset.univ.filter fun i : Fin N => σ₁₂⁻¹ i ≠ σ₂⁻¹ (σ₁⁻¹ i)) =
      (Finset.univ.filter fun i : Fin N => σ₁₂⁻¹ i ≠ (σ₁ * σ₂)⁻¹ i) := by
    ext i
    simp [mul_inv_rev, Equiv.Perm.mul_apply]
  rw [hset, card_inv_ne_eq_hammingDist, hammingDist_comm]

theorem surjunctive_of_isSofic : OMA.R_Green100_green_100_parts_i_R1.H2 := by
  intro K _ _ G _ hsofic b hinj
  classical
  by_cases hsub : Subsingleton G
  · haveI : Finite G := inferInstance
    haveI : Finite (G → K) := inferInstance
    exact Finite.surjective_of_injective hinj
  · haveI : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
    by_contra hnot_surj
    obtain ⟨M, h1M, hM⟩ := local_injective b hinj
    obtain ⟨E, hE_ne, c, ⟨g₀, hg₀⟩, hc_vanish⟩ := exists_non_surj_window b hnot_surj
    let S : Finset G := b.coeff.support
    let F : Finset G :=
      M ∪ E ∪ S ∪ (M.biUnion fun g => S.image fun u => g * u) ∪
        (E.biUnion fun g => S.image fun u => g * u)
    have h1F : 1 ∈ F := by simp [F, h1M]
    have hMF : ∀ g ∈ M, g ∈ F := fun g hg => by simp [F, hg]
    have hEF : ∀ g ∈ E, g ∈ F := fun g hg => by simp [F, hg]
    have hSF : ∀ u ∈ S, u ∈ F := fun u hu => by simp [F, hu]
    have hMSF : ∀ g ∈ M, ∀ u ∈ S, g * u ∈ F := fun g hg u hu => by
      simp only [F, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
      left; right; exact ⟨g, hg, u, hu, rfl⟩
    have hESF : ∀ g ∈ E, ∀ u ∈ S, g * u ∈ F := fun g hg u hu => by
      simp only [F, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
      right; exact ⟨g, hg, u, hu, rfl⟩
    let C₁ : ℕ := 1 + M.card * S.card
    let C₂ : ℕ := E.card * E.card + E.card * S.card
    have hE_pos : 0 < E.card := hE_ne.card_pos
    let denom : ℝ := (C₁ : ℝ) * (E.card : ℝ) ^ 2 + (C₂ : ℝ) + 1
    have hdenom_pos : 0 < denom := by positivity
    let δ : ℝ := 1 / (2 * denom)
    have hδ_pos : 0 < δ := by positivity
    obtain ⟨N, θ, hN_pos, hmul, hone, hsep⟩ := isSofic_amplified hsofic F δ hδ_pos
    have hN_r : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
    -- Finite linear cellular automaton τ_N on Fin N → K
    let τN : (Fin N → K) →ₗ[K] (Fin N → K) :=
      { toFun := fun z i => ∑ u ∈ S, b.coeff u * z ((θ u)⁻¹ i)
        map_add' := fun z₁ z₂ => by ext i; simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun a z => by
          ext i
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => by ring }
    -- Good set V₁ for local injectivity
    let V₁ : Finset (Fin N) := Finset.univ.filter fun i =>
      (θ 1)⁻¹ i = i ∧ ∀ g ∈ M, ∀ u ∈ S, (θ (g * u))⁻¹ i = (θ u)⁻¹ ((θ g)⁻¹ i)
    -- Bound on bad vertices for V₁
    have hbad₁ : (Finset.univ \ V₁).card < (C₁ : ℝ) * δ * (N : ℝ) := by
      let B0 : Finset (Fin N) := Finset.univ.filter fun i => (θ 1)⁻¹ i ≠ (1 : Equiv.Perm (Fin N))⁻¹ i
      let B1 : Finset (Fin N) :=
        M.biUnion fun g => S.biUnion fun u =>
          Finset.univ.filter fun i => (θ (g * u))⁻¹ i ≠ (θ u)⁻¹ ((θ g)⁻¹ i)
      have hsub_bad : Finset.univ \ V₁ ⊆ B0 ∪ B1 := by
        intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, V₁, Finset.mem_filter,
          not_and, not_forall] at hi
        by_cases h1i : (θ 1)⁻¹ i = i
        · obtain ⟨g, hg, u, hu, hne⟩ := hi h1i
          refine Finset.mem_union_right _ ?_
          simp only [B1, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨g, hg, u, hu, hne⟩
        · refine Finset.mem_union_left _ ?_
          simp only [B0, Finset.mem_filter, Finset.mem_univ, true_and, inv_one, Equiv.Perm.coe_one, id_eq]
          exact h1i
      have hB0 : (B0.card : ℝ) < δ * (N : ℝ) := by
        have h1 := hone h1F
        rw [hammingDistNorm, div_lt_iff₀ hN_r] at h1
        have heq : B0.card = hammingDist (⇑(θ 1)) (⇑(1 : Equiv.Perm (Fin N))) :=
          card_inv_ne_eq_hammingDist (θ 1) 1
        rw [heq]; exact h1
      have hB1 : (B1.card : ℝ) ≤ (M.card * S.card : ℕ) * (δ * (N : ℝ)) := by
        have hle1 : B1.card ≤ ∑ g ∈ M, ∑ u ∈ S,
            (Finset.univ.filter fun i : Fin N => (θ (g * u))⁻¹ i ≠ (θ u)⁻¹ ((θ g)⁻¹ i)).card :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum fun g _ => Finset.card_biUnion_le)
        have hle1_r : (B1.card : ℝ) ≤ ∑ g ∈ M, ∑ u ∈ S,
            ((Finset.univ.filter fun i : Fin N => (θ (g * u))⁻¹ i ≠ (θ u)⁻¹ ((θ g)⁻¹ i)).card : ℝ) := by
          exact_mod_cast hle1
        have hterm : ∀ g ∈ M, ∀ u ∈ S,
            ((Finset.univ.filter fun i : Fin N => (θ (g * u))⁻¹ i ≠ (θ u)⁻¹ ((θ g)⁻¹ i)).card : ℝ) ≤ δ * (N : ℝ) := by
          intro g hg u hu
          have h1 := hmul g (hMF g hg) u (hSF u hu) (hMSF g hg u hu)
          rw [hammingDistNorm, div_lt_iff₀ hN_r] at h1
          rw [card_inv_mul_ne_eq_hammingDist]
          exact h1.le
        calc (B1.card : ℝ)
            ≤ ∑ g ∈ M, ∑ u ∈ S, (δ * (N : ℝ)) :=
              hle1_r.trans (Finset.sum_le_sum fun g hg => Finset.sum_le_sum fun u hu => hterm g hg u hu)
          _ = (M.card * S.card : ℕ) * (δ * (N : ℝ)) := by
              simp [mul_assoc]
      have hcard_le : ((Finset.univ \ V₁).card : ℝ) ≤ (B0.card : ℝ) + (B1.card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub_bad).trans (Finset.card_union_le B0 B1)
      have hC1 : ((C₁ : ℝ) * δ * (N : ℝ)) = δ * (N : ℝ) + (M.card * S.card : ℕ) * (δ * (N : ℝ)) := by
        simp only [C₁, Nat.cast_add, Nat.cast_one, Nat.cast_mul]; ring
      linarith
    -- Every z ∈ ker τN vanishes on V₁, so dim(ker τN) ≤ (univ \ V₁).card
    have hker_dim : Module.finrank K (LinearMap.ker τN) ≤ (Finset.univ \ V₁).card := by
      let res : (Fin N → K) →ₗ[K] ((Finset.univ \ V₁ : Finset (Fin N)) → K) :=
        { toFun := fun z i => z i.1
          map_add' := fun _ _ => by ext i; rfl
          map_smul' := fun _ _ => by ext i; rfl }
      have hinj_ker : Function.Injective (res.domRestrict (LinearMap.ker τN)) := by
        intro ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩ heq
        apply Subtype.ext
        have hdiff : z₁ - z₂ ∈ LinearMap.ker τN := (LinearMap.ker τN).sub_mem hz₁ hz₂
        suffices h0 : z₁ - z₂ = 0 from sub_eq_zero.mp h0
        ext i
        by_cases hi : i ∈ V₁
        · simp only [V₁, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          let x : G → K := fun g => (z₁ - z₂) ((θ g)⁻¹ i)
          have hxM : ∀ g ∈ M, tau b x g = 0 := by
            intro g hg
            change ∑ u ∈ S, b.coeff u * x (g * u) = 0
            have heq_sum : ∑ u ∈ S, b.coeff u * x (g * u) = τN (z₁ - z₂) ((θ g)⁻¹ i) := by
              refine Finset.sum_congr rfl fun u hu => ?_
              simp only [x, hi.2 g hg u hu]
            rw [heq_sum]
            exact congrFun (LinearMap.mem_ker.mp hdiff) ((θ g)⁻¹ i)
          have hx1 : (z₁ - z₂) ((θ 1)⁻¹ i) = 0 := hM x hxM
          rw [hi.1] at hx1
          exact hx1
        · have hi_sdiff : i ∈ Finset.univ \ V₁ := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
          have := congrFun heq ⟨i, hi_sdiff⟩
          exact sub_eq_zero.mpr this
      have h1 := LinearMap.finrank_le_finrank_of_injective hinj_ker
      simpa only [Module.finrank_pi, Fintype.card_coe] using h1
    -- Good set V₂ for non-surjectivity on E
    let V₂ : Finset (Fin N) := Finset.univ.filter fun i =>
      (∀ g₁ ∈ E, ∀ g₂ ∈ E, g₁ ≠ g₂ → (θ g₁)⁻¹ i ≠ (θ g₂)⁻¹ i) ∧
      (∀ g ∈ E, ∀ u ∈ S, (θ (g * u))⁻¹ i = (θ u)⁻¹ ((θ g)⁻¹ i))
    have hbad₂ : ((Finset.univ \ V₂).card : ℝ) ≤ (C₂ : ℝ) * δ * (N : ℝ) := by
      let B2 : Finset (Fin N) :=
        E.biUnion fun g₁ => E.biUnion fun g₂ =>
          if g₁ ≠ g₂ then Finset.univ.filter fun i => (θ g₁)⁻¹ i = (θ g₂)⁻¹ i else ∅
      let B3 : Finset (Fin N) :=
        E.biUnion fun g => S.biUnion fun u =>
          Finset.univ.filter fun i => (θ (g * u))⁻¹ i ≠ (θ u)⁻¹ ((θ g)⁻¹ i)
      have hsub_bad : Finset.univ \ V₂ ⊆ B2 ∪ B3 := by
        intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, V₂, Finset.mem_filter] at hi
        by_cases h1 : ∀ g₁ ∈ E, ∀ g₂ ∈ E, g₁ ≠ g₂ → (θ g₁)⁻¹ i ≠ (θ g₂)⁻¹ i
        · have h2 : ¬ ∀ g ∈ E, ∀ u ∈ S, (θ (g * u))⁻¹ i = (θ u)⁻¹ ((θ g)⁻¹ i) := fun h2 => hi ⟨h1, h2⟩
          push_neg at h2
          obtain ⟨g, hg, u, hu, hne⟩ := h2
          refine Finset.mem_union_right _ ?_
          simp only [B3, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨g, hg, u, hu, hne⟩
        · push_neg at h1
          obtain ⟨g₁, hg₁, g₂, hg₂, hne, heq⟩ := h1
          refine Finset.mem_union_left _ ?_
          simp only [B2, Finset.mem_biUnion]
          refine ⟨g₁, hg₁, g₂, hg₂, ?_⟩
          rw [if_pos hne]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact heq
      have hB2 : (B2.card : ℝ) ≤ (E.card * E.card : ℕ) * (δ * (N : ℝ)) := by
        have hle : B2.card ≤ ∑ g₁ ∈ E, ∑ g₂ ∈ E,
            (if g₁ ≠ g₂ then Finset.univ.filter fun i : Fin N => (θ g₁)⁻¹ i = (θ g₂)⁻¹ i else ∅).card :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
        have hle_r : (B2.card : ℝ) ≤ ∑ g₁ ∈ E, ∑ g₂ ∈ E,
            ((if g₁ ≠ g₂ then Finset.univ.filter fun i : Fin N => (θ g₁)⁻¹ i = (θ g₂)⁻¹ i else ∅).card : ℝ) := by
          exact_mod_cast hle
        have hterm : ∀ g₁ ∈ E, ∀ g₂ ∈ E,
            ((if g₁ ≠ g₂ then Finset.univ.filter fun i : Fin N => (θ g₁)⁻¹ i = (θ g₂)⁻¹ i else ∅).card : ℝ) ≤ δ * (N : ℝ) := by
          intro g₁ hg₁ g₂ hg₂
          split_ifs with hne
          · have h1 := hsep g₁ (hEF g₁ hg₁) g₂ (hEF g₂ hg₂) hne
            rw [hammingDistNorm, lt_div_iff₀ hN_r] at h1
            have hleN : hammingDist (⇑(θ g₁)) (⇑(θ g₂)) ≤ N := by
              calc hammingDist (⇑(θ g₁)) (⇑(θ g₂)) ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_filter_le _ _
                _ = N := by simp
            rw [card_inv_eq_eq_sub_hammingDist, Nat.cast_sub hleN]
            linarith
          · simp; positivity
        calc (B2.card : ℝ)
            ≤ ∑ g₁ ∈ E, ∑ g₂ ∈ E, (δ * (N : ℝ)) :=
              hle_r.trans (Finset.sum_le_sum fun g₁ hg₁ => Finset.sum_le_sum fun g₂ hg₂ => hterm g₁ hg₁ g₂ hg₂)
          _ = (E.card * E.card : ℕ) * (δ * (N : ℝ)) := by simp [mul_assoc]
      have hB3 : (B3.card : ℝ) ≤ (E.card * S.card : ℕ) * (δ * (N : ℝ)) := by
        have hle : B3.card ≤ ∑ g ∈ E, ∑ u ∈ S,
            (Finset.univ.filter fun i : Fin N => (θ (g * u))⁻¹ i ≠ (θ u)⁻¹ ((θ g)⁻¹ i)).card :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
        have hle_r : (B3.card : ℝ) ≤ ∑ g ∈ E, ∑ u ∈ S,
            ((Finset.univ.filter fun i : Fin N => (θ (g * u))⁻¹ i ≠ (θ u)⁻¹ ((θ g)⁻¹ i)).card : ℝ) := by
          exact_mod_cast hle
        have hterm : ∀ g ∈ E, ∀ u ∈ S,
            ((Finset.univ.filter fun i : Fin N => (θ (g * u))⁻¹ i ≠ (θ u)⁻¹ ((θ g)⁻¹ i)).card : ℝ) ≤ δ * (N : ℝ) := by
          intro g hg u hu
          have h1 := hmul g (hEF g hg) u (hSF u hu) (hESF g hg u hu)
          rw [hammingDistNorm, div_lt_iff₀ hN_r] at h1
          rw [card_inv_mul_ne_eq_hammingDist]
          exact h1.le
        calc (B3.card : ℝ)
            ≤ ∑ g ∈ E, ∑ u ∈ S, (δ * (N : ℝ)) :=
              hle_r.trans (Finset.sum_le_sum fun g hg => Finset.sum_le_sum fun u hu => hterm g hg u hu)
          _ = (E.card * S.card : ℕ) * (δ * (N : ℝ)) := by simp [mul_assoc]
      have hcard_le : ((Finset.univ \ V₂).card : ℝ) ≤ (B2.card : ℝ) + (B3.card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub_bad).trans (Finset.card_union_le B2 B3)
      have hC2 : ((C₂ : ℝ) * δ * (N : ℝ)) =
          (E.card * E.card : ℕ) * (δ * (N : ℝ)) + (E.card * S.card : ℕ) * (δ * (N : ℝ)) := by
        simp only [C₂, Nat.cast_add, Nat.cast_mul]; ring
      linarith
    -- Maximal packing A ⊆ V₂ of disjoint E-translates B i = E.image (fun g => (θ g)⁻¹ i)
    let B : Fin N → Finset (Fin N) := fun i => E.image fun g => (θ g)⁻¹ i
    have hB_ne : ∀ i ∈ V₂, (B i).Nonempty := fun i _ => hE_ne.image _
    obtain ⟨A, hAV₂, hAdisj, hAmax⟩ := exists_maximal_packing B hB_ne
    -- Size bound: V₂.card ≤ E.card^2 * A.card
    have hpack_card : V₂.card ≤ E.card * E.card * A.card := by
      let U : Finset (Fin N) := A.biUnion B
      have hU_card : U.card ≤ A.card * E.card := by
        calc U.card ≤ ∑ a ∈ A, (B a).card := Finset.card_biUnion_le
          _ ≤ ∑ _a ∈ A, E.card := Finset.sum_le_sum fun a _ => Finset.card_image_le
          _ = A.card * E.card := by simp
      have hV₂_sub : V₂ ⊆ U.biUnion fun j => E.image fun g => θ g j := by
        intro i hi
        obtain ⟨a, haA, hnotdisj⟩ := hAmax i hi
        rw [Finset.not_disjoint_iff] at hnotdisj
        obtain ⟨j, hjBi, hjBa⟩ := hnotdisj
        simp only [B, Finset.mem_image] at hjBi
        obtain ⟨g, hgE, rfl⟩ := hjBi
        simp only [Finset.mem_biUnion, Finset.mem_image]
        refine ⟨(θ g)⁻¹ i, Finset.mem_biUnion.mpr ⟨a, haA, hjBa⟩, g, hgE, by simp⟩
      calc V₂.card ≤ (U.biUnion fun j => E.image fun g => θ g j).card := Finset.card_le_card hV₂_sub
        _ ≤ ∑ j ∈ U, (E.image fun g => θ g j).card := Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ U, E.card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ = U.card * E.card := by simp
        _ ≤ (A.card * E.card) * E.card := Nat.mul_le_mul_right E.card hU_card
        _ = E.card * E.card * A.card := by ring
    -- Surjective annihilator Ψ : (Fin N → K) →ₗ[K] (A → K) vanishing on range τN
    let Ψ : (Fin N → K) →ₗ[K] (A → K) :=
      { toFun := fun w a => ∑ g : E, c g * w ((θ g.1)⁻¹ a.1)
        map_add' := fun w₁ w₂ => by ext a; simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun r w => by
          ext a
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => by ring }
    have hrange_le_ker : LinearMap.range τN ≤ LinearMap.ker Ψ := by
      rintro _ ⟨z, rfl⟩
      rw [LinearMap.mem_ker]
      ext ⟨a, haA⟩
      have haV₂ := hAV₂ haA
      simp only [V₂, Finset.mem_filter, Finset.mem_univ, true_and] at haV₂
      let x : G → K := fun g => z ((θ g)⁻¹ a)
      have heq : ∀ g : E, τN z ((θ g.1)⁻¹ a) = tau b x g.1 := by
        intro g
        change ∑ u ∈ S, b.coeff u * z ((θ u)⁻¹ ((θ g.1)⁻¹ a)) =
          ∑ u ∈ S, b.coeff u * z ((θ (g.1 * u))⁻¹ a)
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [haV₂.2 g.1 g.2 u hu]
      simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      simp_rw [heq]
      exact hc_vanish x
    have hΨ_surj : Function.Surjective Ψ := by
      intro v
      let w : Fin N → K := fun j =>
        if h : ∃ a : A, j = (θ g₀.1)⁻¹ a.1 then v (Classical.choose h) / c g₀ else 0
      refine ⟨w, ?_⟩
      ext a
      simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk]
      have haV₂ := hAV₂ a.2
      simp only [V₂, Finset.mem_filter, Finset.mem_univ, true_and] at haV₂
      rw [Finset.sum_eq_single g₀]
      · have hex : ∃ a' : A, (θ g₀.1)⁻¹ a.1 = (θ g₀.1)⁻¹ a'.1 := ⟨a, rfl⟩
        have hch : Classical.choose hex = a := by
          apply Subtype.ext
          exact (θ g₀.1)⁻¹.injective (Classical.choose_spec hex).symm
        simp only [w, hex, ↓reduceDIte, hch]
        exact mul_div_cancel₀ (v a) hg₀
      · intro g _ hgg₀
        have hno : ¬ ∃ a' : A, (θ g.1)⁻¹ a.1 = (θ g₀.1)⁻¹ a'.1 := by
          rintro ⟨a', ha'⟩
          by_cases haa' : a.1 = a'.1
          · rw [← haa'] at ha'
            exact haV₂.1 g.1 g.2 g₀.1 g₀.2 (fun h => hgg₀ (Subtype.ext h)) ha'
          · have hdisj := hAdisj a.1 a.2 a'.1 a'.2 haa'
            have hmem1 : (θ g.1)⁻¹ a.1 ∈ B a.1 := Finset.mem_image.mpr ⟨g.1, g.2, rfl⟩
            have hmem2 : (θ g.1)⁻¹ a.1 ∈ B a'.1 := by
              rw [ha']
              exact Finset.mem_image.mpr ⟨g₀.1, g₀.2, rfl⟩
            exact Finset.disjoint_left.mp hdisj hmem1 hmem2
        simp only [w, dif_neg hno, mul_zero]
      · intro h; exact absurd (Finset.mem_univ g₀) h
    -- Combine rank-nullity bounds to get a contradiction
    have hkerΨ : Module.finrank K (LinearMap.ker Ψ) + A.card = N := by
      have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
      rw [LinearMap.range_eq_top.mpr hΨ_surj, finrank_top] at hrn
      simp only [Module.finrank_pi, Fintype.card_coe, Fintype.card_fin] at hrn
      omega
    have hrnτ : Module.finrank K (LinearMap.range τN) + Module.finrank K (LinearMap.ker τN) = N := by
      have hrn := LinearMap.finrank_range_add_finrank_ker τN
      simp only [Module.finrank_pi, Fintype.card_fin] at hrn
      exact hrn
    have hrange_le : Module.finrank K (LinearMap.range τN) ≤ Module.finrank K (LinearMap.ker Ψ) :=
      Submodule.finrank_mono hrange_le_ker
    have hA_le_bad₁ : A.card ≤ (Finset.univ \ V₁).card := by omega
    have hV₂_eq : (V₂.card : ℝ) + ((Finset.univ \ V₂).card : ℝ) = (N : ℝ) := by
      have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ V₂)
      simp only [Finset.card_univ, Fintype.card_fin] at h
      exact_mod_cast (by omega : V₂.card + (Finset.univ \ V₂).card = N)
    have hpack_r : (V₂.card : ℝ) ≤ (E.card : ℝ) ^ 2 * (A.card : ℝ) := by
      have : (V₂.card : ℝ) ≤ (E.card : ℝ) * (E.card : ℝ) * (A.card : ℝ) := by exact_mod_cast hpack_card
      linarith [sq (E.card : ℝ)]
    have hA_lt : (A.card : ℝ) < (C₁ : ℝ) * δ * (N : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast hA_le_bad₁) hbad₁
    have hE2_pos : (0 : ℝ) < (E.card : ℝ) ^ 2 := by positivity
    have h1 : (N : ℝ) - (C₂ : ℝ) * δ * (N : ℝ) ≤ (V₂.card : ℝ) := by linarith
    have h2 : (V₂.card : ℝ) < (E.card : ℝ) ^ 2 * ((C₁ : ℝ) * δ * (N : ℝ)) :=
      lt_of_le_of_lt hpack_r (mul_lt_mul_of_pos_left hA_lt hE2_pos)
    have h3 : (N : ℝ) < ((C₁ : ℝ) * (E.card : ℝ) ^ 2 + (C₂ : ℝ)) * δ * (N : ℝ) := by linarith
    have h4 : (1 : ℝ) < ((C₁ : ℝ) * (E.card : ℝ) ^ 2 + (C₂ : ℝ)) * δ := by
      nlinarith
    have h5 : ((C₁ : ℝ) * (E.card : ℝ) ^ 2 + (C₂ : ℝ)) * δ < 1 := by
      have hlt_denom : (C₁ : ℝ) * (E.card : ℝ) ^ 2 + (C₂ : ℝ) < denom := by
        dsimp [denom]; linarith
      have hmul_le : ((C₁ : ℝ) * (E.card : ℝ) ^ 2 + (C₂ : ℝ)) * δ < denom * δ :=
        mul_lt_mul_of_pos_right hlt_denom hδ_pos
      have hdd : denom * δ = 1 / 2 := by
        dsimp [δ]; field_simp [hdenom_pos.ne']
      linarith
    linarith

end MainProof

end Green100Surjunctivity

theorem OMA.solution : OMA.R_Green100_green_100_parts_i_R1.H2 :=
  Green100Surjunctivity.surjunctive_of_isSofic

