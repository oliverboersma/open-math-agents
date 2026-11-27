import OMAReductions.R_Green100_green_100_parts_i_R1_H2_R1
import Mathlib

/-! Amplify finite sofic approximations using the coordinatewise action. -/
open Green100 Finset
open scoped Classical
namespace SoficAmplification

private lemma badUnionBound {α β : Type*} [DecidableEq β] (S : Finset α) (bad : α → Finset β) (B : ℝ)
    (h : ∀ a ∈ S, ((bad a).card : ℝ) ≤ B) :
    ((S.biUnion bad).card : ℝ) ≤ (S.card : ℝ)*B := by
  classical
  calc
    _ ≤ ∑ a ∈ S, ((bad a).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _a ∈ S, B := sum_le_sum h
    _ = _ := by simp

private lemma equalTuples {n m : ℕ} (p q : Fin n → Fin n) :
    ((univ : Finset (Fin m → Fin n)).filter (fun a => ∀ j, p (a j) = q (a j))).card =
      ((univ : Finset (Fin n)).filter (fun i => p i = q i)).card ^ m := by
  classical
  rw [← Fintype.card_piFinset_const]
  congr 1
  ext a
  simp [Fintype.mem_piFinset]

private lemma badCoordinate {n m : ℕ} (D : Finset (Fin n)) (j : Fin m) :
    ((univ : Finset (Fin m → Fin n)).filter (fun a => a j ∈ D)).card = D.card * n^(m-1) := by
  classical
  let S : Fin m → Finset (Fin n) := Function.update (fun _ => univ) j D
  have he : univ.filter (fun a : Fin m → Fin n => a j ∈ D) = Fintype.piFinset S := by
    ext a
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro ha i
      by_cases hi : i = j
      · simpa [S, hi] using ha
      · simp [S, Function.update_of_ne hi]
    · intro ha
      simpa [S] using ha j
  rw [he, Fintype.card_piFinset]
  have hu : (fun i => (S i).card) = Function.update (fun _ => n) j D.card := by
    ext i
    by_cases hi : i = j
    · simp [hi, S]
    · simp [S, Function.update_of_ne hi]
  rw [hu, prod_update_of_mem (mem_univ j)]
  have hcard : ((univ : Finset (Fin m)) \ {j}).card = m-1 := by
    rw [card_sdiff_of_subset (subset_univ _)]
    simp
  simp [hcard]

private lemma tupleDiff {n m : ℕ} (p q : Fin n → Fin n) :
    (((univ : Finset (Fin m → Fin n)).filter (fun a => ¬ ∀ j, p (a j) = q (a j))).card : ℝ) ≤
      (m : ℝ) * (hammingDist p q : ℝ) * (n : ℝ)^(m-1) := by
  classical
  let D := (univ : Finset (Fin n)).filter (fun i => p i ≠ q i)
  let B (j : Fin m) := (univ : Finset (Fin m → Fin n)).filter (fun a => a j ∈ D)
  have hb : (univ : Finset (Fin m → Fin n)).filter (fun a => ¬ ∀ j, p (a j) = q (a j)) =
      (univ : Finset (Fin m)).biUnion B := by
    ext a
    simp [B, D, not_forall]
  rw [hb]
  simpa [B, badCoordinate, D, hammingDist, mul_assoc] using
    badUnionBound (univ : Finset (Fin m)) B ((D.card : ℝ)*(n : ℝ)^(m-1))
      (fun j _ => by simp [B, badCoordinate])

theorem model (G : Type) [Group G] (sofic : IsSofic G) (F : Finset G) (k : ℕ) :
    ∃ (n : ℕ) (θ : G → Equiv.Perm (Fin n)) (U : Finset (Fin n)),
      k*(n-U.card) < n ∧ ∀ i ∈ U, θ 1 i = i ∧ Set.InjOn (fun g => θ g i) F ∧
        ∀ g ∈ F, ∀ h ∈ F, θ (g*h) i = θ g (θ h i) := by
  classical
  let pairs := F ×ˢ F
  let C : ℝ := 1 + 2*(pairs.card : ℝ)
  let δ : ℝ := (2*(k+1)*C)⁻¹
  have hp : 0 < C := by dsimp [C]; positivity
  have hd : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨r,hr₀⟩ := exists_pow_lt_of_lt_one hd (show (3/4:ℝ) < 1 by norm_num)
  let m := r+1
  have hm : 0 < m := Nat.succ_pos r
  have hr : (3/4:ℝ)^m < δ := by
    change (3/4:ℝ)^(r+1) < δ
    rw [pow_succ]
    have hz : 0 ≤ (3/4:ℝ)^r := by positivity
    linarith
  let ε := δ / (m+1)
  have he : 0 < ε := by dsimp [ε]; positivity
  let E := insert 1 (F ∪ pairs.image (fun x => x.1*x.2))
  have oneE : 1 ∈ E := mem_insert_self _ _
  have sub : F ⊆ E := fun _ hx => mem_insert_of_mem (mem_union_left _ hx)
  have prodE {g h : G} (hx : (g,h) ∈ pairs) : g*h ∈ E :=
    mem_insert_of_mem (mem_union_right _ (mem_image_of_mem (fun x => x.1*x.2) hx))
  obtain ⟨n,θ,mulE,idE,sepE⟩ := sofic E ε he
  by_cases hz : n = 0
  · subst n
    have only : ∀ x ∈ F, ∀ y ∈ F, x = y := by
      intro x hx y hy
      by_contra hxy
      have := sepE x (sub hx) y (sub hy) hxy
      norm_num [hammingDistNorm] at this
    refine ⟨1,fun _ => 1,univ,by simp,?_⟩
    intro i _
    refine ⟨rfl,fun x hx y hy _ => only x hx y hy,?_⟩
    intros
    rfl
  let T := Fin m → Fin n
  let N := n^m
  let M (g : G) : Equiv.Perm T := Equiv.piCongrRight (fun _ => θ g)
  have cards : Fintype.card T = N := by simp [T,N]
  let e : T ≃ Fin N := Fintype.equivFinOfCardEq cards
  have hn : (0:ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hz)
  have hN : (0:ℝ) < N := by exact_mod_cast (pow_pos (Nat.pos_of_ne_zero hz) m)
  have formula : (n:ℝ) * (n:ℝ)^(m-1) = (N:ℝ) := by
    have ex : m-1+1 = m := by omega
    rw [← pow_succ',ex]
    simp [N]
  have diffBound (p q : Equiv.Perm (Fin n)) (hh : hammingDistNorm p q < ε) :
      (((univ : Finset T).filter (fun a => ¬ ∀ j, p (a j) = q (a j))).card : ℝ) ≤ δ*N := by
    have hq : (hammingDist (⇑p) (⇑q) : ℝ) ≤ ε*n := ((div_lt_iff₀ hn).mp hh).le
    refine (tupleDiff _ _).trans ?_
    calc
      _ ≤ (m:ℝ) * (ε*n) * (n:ℝ)^(m-1) := by gcongr
      _ = ((m:ℝ)*ε)*N := by rw [mul_assoc, mul_assoc, formula, ← mul_assoc]
      _ ≤ δ*N := by
        gcongr
        dsimp [ε]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (show (0:ℝ) < m+1 by positivity)).mpr
        linarith
  have sepBound (p q : Equiv.Perm (Fin n)) (hh : (1/4:ℝ) ≤ hammingDistNorm p q) :
      (((univ : Finset T).filter (fun a => ∀ j, p (a j) = q (a j))).card : ℝ) ≤ δ*N := by
    have hq : (1/4:ℝ)*n ≤ (hammingDist (⇑p) (⇑q) : ℝ) := (le_div_iff₀ hn).mp hh
    have hcard := (Finset.card_filter_add_card_filter_not (s := univ) (fun i : Fin n => p i = q i))
    have hcomp : (((univ : Finset (Fin n)).filter (fun i => p i = q i)).card : ℝ) +
        (hammingDist (⇑p) (⇑q) : ℝ) = n := by exact_mod_cast (by simpa [hammingDist] using hcard)
    rw [equalTuples]
    push_cast
    calc
      _ ≤ ((3/4:ℝ)*n)^m := by gcongr <;> linarith
      _ = (3/4:ℝ)^m * (N:ℝ) := by simp [mul_pow,N]
      _ ≤ δ*N := by gcongr
  let A := (univ : Finset T).filter (fun a => ¬∀ j, θ 1 (a j) = a j)
  let B (x : G × G) := (univ : Finset T).filter
    (fun a => ¬∀ j, θ x.1 (θ x.2 (a j)) = θ (x.1*x.2) (a j))
  let D (x : G × G) := if x.1 = x.2 then ∅ else
    (univ : Finset T).filter (fun a => ∀ j, θ x.1 (a j) = θ x.2 (a j))
  let bad := (A ∪ pairs.biUnion B) ∪ pairs.biUnion D
  have hA : (A.card:ℝ) ≤ δ*N := diffBound (θ 1) 1 (idE oneE)
  have hB : ∀ x ∈ pairs, ((B x).card:ℝ) ≤ δ*N := by
    rintro ⟨g,h⟩ hx
    obtain ⟨hg,hh⟩ : g ∈ F ∧ h ∈ F := by simpa [pairs] using hx
    exact diffBound (θ g * θ h) (θ (g*h)) (mulE g (sub hg) h (sub hh) (prodE hx))
  have hD : ∀ x ∈ pairs, ((D x).card:ℝ) ≤ δ*N := by
    rintro ⟨g,h⟩ hx
    obtain ⟨hg,hh⟩ : g ∈ F ∧ h ∈ F := by simpa [pairs] using hx
    by_cases eq : g = h
    · simp [D, eq]; positivity
    · simpa [D, eq] using sepBound (θ g) (θ h) (sepE g (sub hg) h (sub hh) eq)
  have addBound (S V : Finset T) : ((S ∪ V).card:ℝ) ≤ S.card + V.card := by
    exact_mod_cast (card_union_le S V)
  have hbad : (bad.card:ℝ) ≤ C*(δ*N) := by
    have hh := addBound (A ∪ pairs.biUnion B) (pairs.biUnion D)
    have h1 := addBound A (pairs.biUnion B)
    have h2 := badUnionBound pairs B _ hB
    have h3 := badUnionBound pairs D _ hD
    dsimp [bad]
    dsimp [C]
    linarith
  let good := univ \ bad
  have hg : N - good.card = bad.card := by
    have hsub : bad ⊆ (univ : Finset T) := subset_univ _
    have hl := card_sdiff_of_subset hsub
    rw [card_univ, cards] at hl
    have hle : bad.card ≤ N := by simpa only [cards,card_univ] using card_mono hsub
    change N - (univ \ bad).card = bad.card
    omega
  refine ⟨N,fun g => ((e.symm.trans (M g)).trans e),good.map e.toEmbedding,?_,?_⟩
  · rw [card_map,hg]
    have hcancel : C*δ = (2*((k:ℝ)+1))⁻¹ := by
      dsimp [δ]
      field_simp
    have hreal : (k:ℝ)*(bad.card:ℝ) < N := calc
      _ ≤ (k:ℝ)*(C*(δ*N)) := by gcongr
      _ = ((k:ℝ)*(2*((k:ℝ)+1))⁻¹)*N := by rw [← mul_assoc C, hcancel, mul_assoc]
      _ < N := by
        have hk : (k:ℝ)*(2*((k:ℝ)+1))⁻¹ < 1 := by
          rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
          linarith [Nat.cast_nonneg (α := ℝ) k]
        simpa using (mul_lt_mul_of_pos_right hk hN)
    exact_mod_cast hreal
  · intro i hi
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hi
    have ha' : a ∉ bad := (mem_sdiff.mp ha).2
    have haA : a ∉ A := fun x => ha' (mem_union_left _ (mem_union_left _ x))
    have haB (x : G × G) (hx : x ∈ pairs) : a ∉ B x := fun hb =>
      ha' (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨x,hx,hb⟩)))
    have haD (x : G × G) (hx : x ∈ pairs) : a ∉ D x := fun hb =>
      ha' (mem_union_right _ (mem_biUnion.mpr ⟨x,hx,hb⟩))
    have apply_eq (g : G) (b : T) : (e.symm.trans (M g) |>.trans e) (e b) = e (M g b) := by simp
    change (e.symm.trans (M 1) |>.trans e) (e a) = e a ∧ _ ∧ _
    refine ⟨?_,?_,?_⟩
    · rw [apply_eq]
      apply congrArg e
      funext j
      exact (by simpa [A] using haA : ∀ j, θ 1 (a j) = a j) j
    · intro g hg h hh eq
      change ((e.symm.trans (M g)).trans e) (e a) = ((e.symm.trans (M h)).trans e) (e a) at eq
      have eq' : ∀ j, θ g (a j) = θ h (a j) := by
        rw [apply_eq, apply_eq] at eq
        exact congrFun (e.injective eq)
      by_contra ne
      exact haD (g,h) (mem_product.mpr ⟨hg,hh⟩) (by simp [D, ne, eq'])
    · intro g hg h hh
      change ((e.symm.trans (M (g*h))).trans e) (e a) =
        ((e.symm.trans (M g)).trans e) (((e.symm.trans (M h)).trans e) (e a))
      rw [apply_eq, apply_eq, apply_eq]
      apply congrArg e
      funext j
      exact ((by simpa [B] using haB (g,h) (mem_product.mpr ⟨hg,hh⟩) :
        ∀ j, θ g (θ h (a j)) = θ (g*h) (a j)) j).symm

end SoficAmplification

theorem OMA.solution : OMA.R_Green100_green_100_parts_i_R1_H2_R1.H1 := SoficAmplification.model