import OMAReductions.R_Erdos147_erdos_147_variants_janzer_conjecture_R1

/-!
# Erdős 147, even-degree step in Janzer conjecture

Adaptation credit: Hanan Beer (@hananzlt). This reuses the complete even-degree proof
by @iLc0, merged in PR3734, including the attributed cubic-cycle argument from PR3513.
The reduction defining this exact step is by @NicholasWierenga (PR3718).
Source: https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3734
This is an auxiliary specialization of existing results, not a proof of the full conjecture.

Pour tout `r ≥ 4` pair et tout `ε > 0`, il existe un graphe biparti `r`-régulier `H` avec
`ex(n, H) = O(n^(2 - 2/r + ε))` (Janzer, arXiv 2006.01062, théorème 1.12, réfutation d'une
conjecture d'Erdős et Simonovits). Ici `H = C_{2k}[t]`, avec `t = r/2` et `k` grand.

Preuve : graphe auxiliaire sur les `t`-parties (définition 5.1 de l'article), où deux parties
sont voisines si elles forment un `K_{t,t}` ; le lemme 5.2 (peu de voisins rencontrent un
ensemble donné) ; un sous-graphe « proportionnel » obtenu par effeuillage, qui remplace les
lemmes 5.3 et 5.4 ; enfin le lemme du cycle homomorphe sans conflit, sous la forme pondérée
par la marche aléatoire (`E147H3`, repris de la variante cubique, PR #3513).
-/

-- Credit: @iLc0

open SimpleGraph Finset Filter Asymptotics Matrix
open scoped Classical

namespace E147H3

/-- Matrice de la marche aléatoire simple : `walkM G u v = 1 / d(u)` si `u ~ v`, `0` sinon. -/
noncomputable def walkM {W : Type} [Fintype W] (G : SimpleGraph W) : Matrix W W ℝ :=
  fun u v => if G.Adj u v then ((G.degree u : ℝ))⁻¹ else 0

/-- Poids d'un uplet cyclique `x : Fin L → W` : produit des `M (x i) (x (i+1 mod L))`. -/
noncomputable def cycW {W : Type} [Fintype W] (M : Matrix W W ℝ) {L : ℕ} (x : Fin L → W) : ℝ :=
  ∏ i : Fin L, M (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩)

-- Lemme 9 : découpe des uplets cycliques, borne de Cauchy–Schwarz pondérée.

private def ext9 {W : Type} {n : ℕ} (x : Fin n → W) (z : W) (i : ℕ) : W :=
  if h : i < n then x ⟨i,h⟩ else z

private noncomputable def path9 {W : Type} [Fintype W] (M : Matrix W W ℝ)
    {n : ℕ} (x : Fin n → W) (z : W) : ℝ :=
  ∏ i : Fin n, M (ext9 x z i) (ext9 x z (i.val+1))

private def drop9 {W : Type} (n : ℕ) {s : ℕ} (x : Fin (s+n) → W) : Fin s → W :=
  fun i => x ⟨n+i.val, by omega⟩

private theorem cons9_val {W : Type} {n : ℕ} (a : W) (x : Fin n → W) (i : Fin (n+1))
    (j : Fin n) (h : i.val = j.val+1) : Fin.cons (α := fun _ => W) a x i = x j := by
  rw [show i = j.succ from Fin.ext h, Fin.cons_succ]

private theorem ext9_zero_cons {W : Type} {n : ℕ} (a z : W) (x : Fin n → W) :
    ext9 (Fin.cons a x) z 0 = a := by simp [ext9]

private theorem ext9_succ_cons {W : Type} {n : ℕ} (a z : W) (x : Fin n → W) (i : ℕ) :
    ext9 (Fin.cons a x) z (i+1) = ext9 x z i := by
  by_cases h : i < n
  · simp only [ext9, dif_pos (Nat.succ_lt_succ h), dif_pos h]
    exact cons9_val a x _ _ rfl
  · simp [ext9, h]

private theorem path9_cons {W : Type} [Fintype W] (M : Matrix W W ℝ)
    {n : ℕ} (a z : W) (x : Fin n → W) :
    path9 M (Fin.cons a x) z = M a (ext9 x z 0) * path9 M x z := by
  simp [path9, Fin.prod_univ_succ, ext9_zero_cons, ext9_succ_cons]

private theorem drop9_cons {W : Type} (s n : ℕ) (a : W) (x : Fin (s+n) → W) :
    drop9 (n+1) (Fin.cons a x) = drop9 n x := by
  funext i
  unfold drop9
  exact cons9_val a x _ _ (by dsimp; omega)

private theorem sumCons9 {W : Type} [Fintype W] {n : ℕ} (H : (Fin (n+1) → W) → ℝ) :
    ∑ x, H x = ∑ a, ∑ x, H (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => W)).sum_comp H, Fintype.sum_prod_type]
  rfl

private theorem cut9 {W : Type} [Fintype W] (M : Matrix W W ℝ) (s n : ℕ) (z : W)
    (H : W → (Fin s → W) → ℝ) :
    ∑ x : Fin (s+n) → W, path9 M x z * H (ext9 x z 0) (drop9 n x) =
    ∑ b, ∑ y : Fin s → W, path9 M y z * ((M^n) b (ext9 y z 0) * H b y) := by
  classical
  induction n generalizing H with
  | zero =>
    rw [sum_comm]
    have hd (x : Fin s → W) : drop9 0 x = x := by funext i; simp [drop9]
    simp [Matrix.one_apply, hd, mul_ite, ite_mul]
  | succ n ih =>
    refine (sumCons9 (n := s+n) (fun x => path9 M x z * H (ext9 x z 0) (drop9 (n+1) x))).trans ?_
    simp only [path9_cons, ext9_zero_cons, drop9_cons]
    apply sum_congr rfl
    intro b _
    calc
      _ = ∑ x : Fin (s+n) → W, path9 M x z *
          ((fun e y => M b e * H b y) (ext9 x z 0) (drop9 n x)) := by
        apply sum_congr rfl; intros; ring
      _ = _ := ih (fun e y => M b e * H b y)
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro y _
        rw [pow_succ', Matrix.mul_apply]
        simp only [sum_mul, mul_sum]
        apply sum_congr rfl
        intros
        ring

private theorem cyc9 {W : Type} [Fintype W] (M : Matrix W W ℝ) {n : ℕ}
    (x : Fin (n+1) → W) : cycW M x = path9 M x (x 0) := by
  apply prod_congr rfl
  intro i _
  simp only [ext9, dif_pos i.isLt]
  by_cases hi : i.val+1 < n+1
  · simp [hi, Nat.mod_eq_of_lt hi]
  · have he : i.val+1 = n+1 := by omega
    simp [he]

private theorem split9 {W : Type} [Fintype W] (M : Matrix W W ℝ)
    (L j l n m s : ℕ) (hL : L = 0+s+m+n+1) (hj : j = n+1)
    (hl : l = j+m) (hs : 0<s) (F : W → W → W → W → ℝ) :
    ∑ x : Fin L → W, cycW M x *
      F (x ⟨0,by omega⟩) (x ⟨1,by omega⟩) (x ⟨j,by omega⟩) (x ⟨l,by omega⟩) =
    ∑ a, ∑ b, ∑ e, ∑ c, M a b * (M^n) b e * (M^m) e c * (M^s) c a * F a b e c := by
  subst L l j
  rw [sumCons9]
  apply sum_congr rfl
  intro a _
  let H := fun (b : W) (y : Fin (0+s+m) → W) =>
    M a b * F a b (ext9 y a 0) (ext9 (drop9 m y) a 0)
  calc
    _ = ∑ x : Fin (0+s+m+n) → W, path9 M x a * H (ext9 x a 0) (drop9 n x) := by
      apply sum_congr rfl
      intro x _
      rw [cyc9]
      simp only [Fin.cons_zero, path9_cons, H]
      have hpos : 0 < 0+s+m+n := by omega
      have hpos' : 0 < 0+s+m := by omega
      simp only [ext9, dif_pos hpos, dif_pos hpos', dif_pos (by omega : 0 < 0+s), drop9]
      simp only [Nat.add_zero]
      rw [cons9_val a x ⟨1,by omega⟩ ⟨0,hpos⟩ rfl,
        cons9_val a x ⟨n+1,by omega⟩ ⟨n,by omega⟩ rfl,
        cons9_val a x ⟨n+1+m,by omega⟩ ⟨n+m,by omega⟩ (by dsimp; omega)]
      rw [show (⟨0, by omega⟩ : Fin (0+s+m+n+1)) = 0 from rfl, Fin.cons_zero]
      ring
    _ = _ := cut9 M _ _ a H
    _ = _ := by
      apply sum_congr rfl
      intro b _
      change (∑ y : Fin (0+s+m) → W, path9 M y a *
        ((fun e t => (M^n) b e * (M a b * F a b e (ext9 t a 0)))
          (ext9 y a 0) (drop9 m y))) = _
      rw [cut9 M (0+s) m a (fun e t => (M^n) b e * (M a b * F a b e (ext9 t a 0)))]
      apply sum_congr rfl
      intro e _
      change (∑ t : Fin (0+s) → W, path9 M t a *
        ((fun c (_ : Fin 0 → W) => (M^m) e c * ((M^n) b e * (M a b * F a b e c)))
          (ext9 t a 0) (drop9 s t))) = _
      rw [cut9 M 0 s a (fun c _ => (M^m) e c * ((M^n) b e * (M a b * F a b e c)))]
      apply sum_congr rfl
      intro c _
      simp [path9, ext9]
      ring

/-- Découpe d'un uplet cyclique de longueur `2k` aux positions `0, 1, j, k+1`. -/
theorem cyc_split {W : Type} [Fintype W] (M : Matrix W W ℝ) (k j : ℕ) (hk : 2 ≤ k)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (F : W → W → W → W → ℝ) :
    ∑ x : Fin (2 * k) → W, cycW M x *
        F (x ⟨0, by omega⟩) (x ⟨1, by omega⟩) (x ⟨j, by omega⟩) (x ⟨k + 1, by omega⟩) =
      ∑ a, ∑ b, ∑ e, ∑ c, M a b * (M ^ (j - 1)) b e * (M ^ (k + 1 - j)) e c *
        (M ^ (k - 1)) c a * F a b e c := by
  exact split9 M (2*k) j (k+1) (j-1) (k+1-j) (k-1)
    (by omega) (by omega) (by omega) (by omega) F

private theorem trip9 {W : Type} [Fintype W] (M : Matrix W W ℝ) (k : ℕ) (hk : 2 ≤ k)
    (F : W → W → W → ℝ) :
    ∑ x : Fin (2*k) → W, cycW M x * F (x ⟨0,by omega⟩) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) =
    ∑ a, ∑ b, ∑ c, M a b * (M^k) b c * (M^(k-1)) c a * F a b c := by
  classical
  rw [cyc_split M k 1 hk (by omega) (by omega) (fun a b _ c => F a b c)]
  simp [Matrix.one_apply, mul_ite, ite_mul, sum_ite_irrel]

private theorem nn9 {W : Type} [Fintype W] (G : SimpleGraph W) (a b : W) :
    0 ≤ walkM G a b := by unfold walkM; split <;> positivity

private theorem row9 {W : Type} [Fintype W] (G : SimpleGraph W) (a : W) :
    ∑ b, walkM G a b ≤ 1 := by
  classical
  simp only [walkM, ← sum_filter, sum_const, nsmul_eq_mul, ← G.neighborFinset_eq_filter,
    G.card_neighborFinset_eq_degree]
  by_cases h : (G.degree a : ℝ) = 0 <;> simp [h]

private theorem iso9 {W : Type} [Fintype W] (G : SimpleGraph W) (m : ℕ) (hm : 0 < m)
    (a b : W) (ha : G.degree a = 0) : (walkM G ^ m) a b = 0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [pow_succ', Matrix.mul_apply]
  simp [walkM, ha]

private theorem trace9 {W : Type} [Fintype W] (M : Matrix W W ℝ) (p q : ℕ) :
    trace (M ^ (p+q)) = ∑ a, ∑ b, (M^p) a b * (M^q) b a := by
  simp only [pow_add, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private theorem ratio9 {U V : ℝ} (hU : 0 ≤ U) (_hV : 0 ≤ V) : V * (U / V) ≤ U := by
  by_cases h : V = 0
  · simp [h, hU]
  · exact le_of_eq (by field_simp)

private theorem upperFirst9 {W : Type} [Fintype W] (G : SimpleGraph W) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2*k) → W, cycW (walkM G) x *
      (((walkM G)^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) /
       ((walkM G)^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩)) ≤
    trace (walkM G ^ (2*(k-1))) := by
  classical
  let M := walkM G
  let P := fun n : ℕ => M^n
  have hn := Matrix.pow_apply_nonneg (nn9 G)
  rw [trip9 (walkM G) k hk (fun a b c => (P (k-1)) a c / (P k) b c),
    two_mul, trace9]
  apply sum_le_sum
  intro a _
  rw [sum_comm]
  apply sum_le_sum
  intro c _
  calc
    _ ≤ ∑ b, M a b * ((P (k-1)) a c * (P (k-1)) c a) := by
      apply sum_le_sum
      intro b _
      have hh := mul_le_mul_of_nonneg_left (ratio9 (hn (k-1) a c) (hn k b c))
        (mul_nonneg (nn9 G a b) (hn (k-1) c a))
      dsimp [M, P] at *
      linarith only [hh]
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_of_le_one_left (mul_nonneg (hn _ _ _) (hn _ _ _)) (row9 G a)

private theorem mass9 {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (α : ℝ)
    (hrel : ∀ u v, (#((G.neighborFinset v).filter (r u)) : ℝ) ≤ α * G.degree v)
    (n : ℕ) (hn : 0 < n)
    (hrev : ∀ a c, (G.degree a : ℝ) * (walkM G^n) a c = G.degree c * (walkM G^n) c a)
    (b e c : W) :
    ∑ a, (if r a e then walkM G a b * (walkM G^n) c a / (walkM G^n) a c else 0) ≤
      α * G.degree b / G.degree c := by
  classical
  calc
    _ ≤ ∑ a, (if G.Adj b a ∧ r e a then (1 : ℝ) else 0) / G.degree c := by
      apply sum_le_sum
      intro a _
      by_cases h : r a e
      · rw [if_pos h]
        by_cases hab : G.Adj a b
        · rw [if_pos ⟨hab.symm, hr _ _ h⟩]
          simp only [walkM, if_pos hab]
          by_cases hc : G.degree c = 0
          · simp [hc, iso9 G n hn c a hc]
          by_cases hp : (walkM G^n) a c = 0
          · rw [hp]
            simp
          have ha : (G.degree a : ℝ) ≠ 0 := by exact_mod_cast hab.degree_pos_left.ne'
          have hc' : (G.degree c : ℝ) ≠ 0 := by exact_mod_cast hc
          change (G.degree a : ℝ)⁻¹ * (walkM G^n) c a / (walkM G^n) a c ≤ _
          apply le_of_eq
          field_simp [ha,hc',hp]
          linarith only [hrev a c]
        · have hba : ¬ G.Adj b a := fun h => hab h.symm
          simp [walkM, hab, hba]
      · simp only [if_neg h]
        positivity
    _ = (#((G.neighborFinset b).filter (r e)) : ℝ) / G.degree c := by
      rw [← sum_div, sum_boole]
      have hs : univ.filter (fun a => G.Adj b a ∧ r e a) = (G.neighborFinset b).filter (r e) := by
        ext a
        simp
      rw [hs]
    _ ≤ _ := div_le_div_of_nonneg_right (hrel e b) (by positivity)

private theorem upperOne9 {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (α : ℝ) (hα : 0 ≤ α)
    (hrel : ∀ u v, (#((G.neighborFinset v).filter (r u)) : ℝ) ≤ α * G.degree v)
    (hrev : ∀ (m : ℕ) (u v : W),
      (G.degree u : ℝ) * (walkM G ^ m) u v = G.degree v * (walkM G ^ m) v u)
    (k j : ℕ) (hk : 2 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∑ x : Fin (2*k) → W, cycW (walkM G) x *
      (if r (x ⟨0,by omega⟩) (x ⟨j,by omega⟩) then
       ((walkM G)^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) /
       ((walkM G)^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) else 0) ≤
    α * trace (walkM G ^ (2*k)) := by
  classical
  let M := walkM G
  let P := fun n : ℕ => M^n
  let D := fun a : W => (G.degree a : ℝ)
  have hn := Matrix.pow_apply_nonneg (nn9 G)
  rw [cyc_split (walkM G) k j hk hj hjk
    (fun a b e c => if r a e then (P k) b c / (P (k-1)) a c else 0),
    two_mul, trace9, mul_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro b _
  rw [mul_sum]
  let f := fun a e c : W => M a b * (P (j-1)) b e * (P (k+1-j)) e c *
    (P (k-1)) c a * (if r a e then (P k) b c / (P (k-1)) a c else 0)
  change (∑ a, ∑ e, ∑ c, f a e c) ≤ _
  have perm : (∑ a, ∑ e, ∑ c, f a e c) = ∑ c, ∑ e, ∑ a, f a e c := by
    calc
      _ = ∑ a, ∑ c, ∑ e, f a e c := sum_congr rfl (fun _ _ => sum_comm)
      _ = _ := sum_comm
        |>.trans (sum_congr rfl (fun _ _ => sum_comm))
  rw [perm]
  apply sum_le_sum
  intro c _
  have hc : D b * (P k) b c / D c ≤ (P k) c b := by
    by_cases hd : D c = 0
    · simpa [hd] using hn k c b
    · apply le_of_eq
      apply (div_eq_iff hd).mpr
      simpa [D, P, M, mul_comm] using hrev k b c
  calc
    _ ≤ ∑ e, (α * D b / D c) * ((P (j-1)) b e * (P (k+1-j)) e c * (P k) b c) := by
      apply sum_le_sum
      intro e _
      have hh := mass9 G r hr α hrel (k-1) (by omega) (hrev _) b e c
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hh
        (mul_nonneg (mul_nonneg (hn _ _ _) (hn _ _ _)) (hn _ _ _)))
      rw [sum_mul]
      apply sum_congr rfl
      intro a _
      dsimp [f, P, M]
      by_cases hr' : r a e <;> simp [hr']
      ring
    _ = α * (P k) b c * (D b * (P k) b c / D c) := by
      rw [← mul_sum, ← sum_mul]
      have hp : (∑ e, (P (j-1)) b e * (P (k+1-j)) e c) = (P k) b c := by
        change ((M^(j-1)) * (M^(k+1-j))) b c = _
        rw [← pow_add, show j-1 + (k+1-j) = k by omega]
      rw [hp]
      ring
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hc (mul_nonneg hα (hn _ _ _))

private theorem cw9_nonneg {W : Type} [Fintype W] (G : SimpleGraph W) {N : ℕ}
    (x : Fin N → W) : 0 ≤ cycW (walkM G) x :=
  prod_nonneg (fun _ _ => nn9 G _ _)

private theorem support9 {W : Type} [Fintype W] (G : SimpleGraph W)
    (hrev : ∀ (m : ℕ) (u v : W),
      (G.degree u : ℝ) * (walkM G ^ m) u v = G.degree v * (walkM G ^ m) v u)
    (k : ℕ) (hk : 2 ≤ k) (x : Fin (2*k) → W) (hx : cycW (walkM G) x ≠ 0) :
    (walkM G^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) ≠ 0 ∧
    (walkM G^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) ≠ 0 := by
  classical
  let M := walkM G
  let P := fun n : ℕ => M^n
  let bad := fun a b c : W => if (P (k-1)) a c = 0 ∨ (P k) b c = 0 then (1:ℝ) else 0
  let term := fun y : Fin (2*k) → W => cycW M y * bad (y ⟨0,by omega⟩) (y ⟨1,by omega⟩)
    (y ⟨k+1,by omega⟩)
  have hzero : ∑ y, term y = 0 := by
    dsimp only [term]
    rw [trip9 M k hk bad]
    apply sum_eq_zero
    intro a _
    apply sum_eq_zero
    intro b _
    apply sum_eq_zero
    intro c _
    by_cases ha : (P (k-1)) a c = 0
    · have hc : (P (k-1)) c a = 0 := by
        by_cases hd : G.degree c = 0
        · exact iso9 G _ (by omega) c a hd
        · have hh := hrev (k-1) a c
          change _ * (P (k-1)) a c = _ * (P (k-1)) c a at hh
          rw [ha, mul_zero] at hh
          exact (mul_eq_zero.mp hh.symm).resolve_left (by exact_mod_cast hd)
      change _ * (P (k-1)) c a * _ = 0
      simp [hc]
    · by_cases hb : (P k) b c = 0
      · change _ * (P k) b c * _ * _ = 0
        simp [hb]
      · simp [bad, ha, hb]
  have hn (y) (_ : y ∈ univ) : 0 ≤ term y := by
    dsimp only [term,bad]
    exact mul_nonneg (cw9_nonneg G y) (by split <;> norm_num)
  have hh := (sum_eq_zero_iff_of_nonneg hn).mp hzero x (mem_univ x)
  dsimp only [term,bad] at hh
  by_contra! h
  have h' : (P (k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) = 0 ∨
      (P k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) = 0 := by tauto
  rw [if_pos h', mul_one] at hh
  exact hx hh

/-- Poids des uplets cycliques en conflit depuis la position 0 (lemme clé de Janzer [Ja20],
version pondérée par la marche aléatoire). -/
theorem conflict0_le {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (α : ℝ) (hα : 0 ≤ α)
    (hrel : ∀ u v, (#((G.neighborFinset v).filter (r u)) : ℝ) ≤ α * G.degree v)
    (hrev : ∀ (m : ℕ) (u v : W),
      (G.degree u : ℝ) * (walkM G ^ m) u v = G.degree v * (walkM G ^ m) v u)
    (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W,
        (if ∃ j : Fin (2 * k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (x ⟨0, by omega⟩) (x j)
          then cycW (walkM G) x else 0) ≤
      Real.sqrt (k * α * trace (walkM G ^ (2 * (k - 1))) * trace (walkM G ^ (2 * k))) := by
  classical
  let X := Fin (2*k) → W
  let M := walkM G
  let P := fun n : ℕ => M^n
  let a := fun x : X => x ⟨0,by omega⟩
  let b := fun x : X => x ⟨1,by omega⟩
  let c := fun x : X => x ⟨k+1,by omega⟩
  let hit := fun x : X =>
    ∃ j : Fin (2*k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (a x) (x j)
  let T := fun x : X => if hit x then cycW M x else 0
  let A := fun x : X => (P (k-1)) (a x) (c x)
  let B := fun x : X => (P k) (b x) (c x)
  have hn := Matrix.pow_apply_nonneg (nn9 G)
  have hA (x : X) : 0 ≤ A x := hn _ _ _
  have hB (x : X) : 0 ≤ B x := hn _ _ _
  have hT (x : X) : 0 ≤ T x := by
    dsimp only [T]
    split
    · exact cw9_nonneg G x
    · rfl
  have hf (x : X) : 0 ≤ T x * (A x / B x) := mul_nonneg (hT x) (div_nonneg (hA x) (hB x))
  have hg (x : X) : 0 ≤ T x * (B x / A x) := mul_nonneg (hT x) (div_nonneg (hB x) (hA x))
  have cs := sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset X)
    (fun x _ => hf x) (fun x _ => hg x) (r := T) (by
      intro x _
      by_cases h : cycW M x = 0
      · simp [T,h]
      · obtain ⟨h₁,h₂⟩ := support9 G hrev k hk x h
        have h₁' : A x ≠ 0 := h₁
        have h₂' : B x ≠ 0 := h₂
        apply le_of_eq
        field_simp [h₁',h₂'])
  have hfirst : ∑ x, T x * (A x / B x) ≤ trace (P (2*(k-1))) := by
    apply le_trans _ (upperFirst9 G k hk)
    apply sum_le_sum
    intro x _
    change T x * (A x / B x) ≤ cycW M x * (A x / B x)
    apply mul_le_mul_of_nonneg_right _ (div_nonneg (hA x) (hB x))
    dsimp only [T]
    split
    · rfl
    · exact cw9_nonneg G x
  let idx := fun p : Fin k => (⟨p.val+1,by omega⟩ : Fin (2*k))
  let term := fun (x : X) (p : Fin k) =>
    cycW M x * (if r (a x) (x (idx p)) then B x / A x else 0)
  have hterm (x p) : 0 ≤ term x p := by
    apply mul_nonneg (cw9_nonneg G x)
    split
    · exact div_nonneg (hB x) (hA x)
    · rfl
  have hsecond : ∑ x, T x * (B x / A x) ≤ (k:ℝ) * (α * trace (P (2*k))) := by
    calc
      _ ≤ ∑ x, ∑ p, term x p := by
        apply sum_le_sum
        intro x _
        by_cases h : hit x
        · obtain ⟨j,hj,hjk,hrj⟩ := h
          let p : Fin k := ⟨j.val-1,by omega⟩
          have he : idx p = j := by apply Fin.ext; dsimp [idx,p]; omega
          calc
            _ = term x p := by
              have h' : hit x := ⟨j,hj,hjk,hrj⟩
              simp only [T,term,if_pos h',he,if_pos hrj]
            _ ≤ _ := single_le_sum (fun q _ => hterm x q) (mem_univ p)
        · simpa [T,h] using sum_nonneg (fun p (_ : p ∈ univ) => hterm x p)
      _ = ∑ p, ∑ x, term x p := sum_comm
      _ ≤ ∑ _p : Fin k, α * trace (P (2*k)) := by
        apply sum_le_sum
        intro p _
        exact upperOne9 G r hr α hα hrel hrev k (p.val+1) hk (by omega) (by omega)
      _ = _ := by simp [nsmul_eq_mul]
  apply Real.le_sqrt_of_sq_le
  change (∑ x, T x)^2 ≤ _
  calc
    _ ≤ _ := cs
    _ ≤ _ := mul_le_mul hfirst hsecond (sum_nonneg (fun x _ => hg x))
      (le_trans (sum_nonneg (fun x _ => hf x)) hfirst)
    _ = _ := by dsimp [P,M]; ring

-- Lemme 10 : réversibilité, traces paires, rotations.

theorem walkM_nonneg {W : Type} [Fintype W] (G : SimpleGraph W) (u v : W) :
    0 ≤ walkM G u v := by
  unfold walkM
  split <;> positivity

theorem walkM_pow_nonneg {W : Type} [Fintype W] (G : SimpleGraph W) (m : ℕ) (u v : W) :
    0 ≤ (walkM G ^ m) u v := by
  induction m generalizing u v with
  | zero => simp only [pow_zero, Matrix.one_apply]; split <;> norm_num
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact sum_nonneg fun _ _ ↦ mul_nonneg (ih ..) (walkM_nonneg ..)

private theorem walkM_balance {W : Type} [Fintype W] (G : SimpleGraph W) (w : W → ℝ)
    (hw : ∀ u, 0 < G.degree u → w u = G.degree u) (m : ℕ) (u v : W) :
    w u * (walkM G ^ m) u v = w v * (walkM G ^ m) v u := by
  have base (a b : W) : w a * walkM G a b = w b * walkM G b a := by
    by_cases h : G.Adj a b
    · simp [walkM, h, h.symm, hw a h.degree_pos_left, hw b h.degree_pos_right,
          h.degree_pos_left.ne', h.degree_pos_right.ne']
    · have h' : ¬G.Adj b a := fun e ↦ h e.symm
      simp [walkM, h, h']
  induction m generalizing u v with
  | zero =>
    by_cases h : u = v <;> simp [h, Ne.symm]
  | succ m ih =>
    conv_lhs => rw [pow_succ', Matrix.mul_apply, Finset.mul_sum]
    conv_rhs => rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
    apply sum_congr rfl
    intro z _
    linear_combination (walkM G ^ m) z v * base u z + walkM G z u * ih z v

/-- Réversibilité de la marche aléatoire : `d(u) Pᵐ(u,v) = d(v) Pᵐ(v,u)`. -/
theorem walkM_pow_rev {W : Type} [Fintype W] (G : SimpleGraph W) (m : ℕ) (u v : W) :
    (G.degree u : ℝ) * (walkM G ^ m) u v = G.degree v * (walkM G ^ m) v u := by
  exact walkM_balance G _ (fun _ _ ↦ rfl) m u v

private theorem trace_split_walkM {W : Type} [Fintype W] (G : SimpleGraph W) (a b : ℕ) :
    trace (walkM G ^ (a + b)) = ∑ p : W × W, (walkM G ^ a) p.1 p.2 * (walkM G ^ b) p.2 p.1 := by
  simp [pow_add, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]

/-- Log-convexité des traces paires. -/
theorem trace_walkM_logconvex {W : Type} [Fintype W] (G : SimpleGraph W) (j : ℕ) (hj : 1 ≤ j) :
    trace (walkM G ^ (2 * j)) ^ 2 ≤
      trace (walkM G ^ (2 * (j - 1))) * trace (walkM G ^ (2 * (j + 1))) := by
  let w (u : W) : ℝ := if G.degree u = 0 then 1 else G.degree u
  have hw (u : W) (hu : 0 < G.degree u) : w u = G.degree u := by simp [w, hu.ne']
  have hw' (u : W) : w u ≠ 0 := by unfold w; split <;> simp_all
  let a := j - 1
  let b := j + 1
  rw [show 2 * j = a + b by dsimp [a, b]; omega, trace_split_walkM,
      show 2 * (j - 1) = a + a by dsimp [a]; omega, trace_split_walkM,
      show 2 * (j + 1) = b + b by dsimp [b]; omega, trace_split_walkM]
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · exact fun _ _ ↦ mul_nonneg (walkM_pow_nonneg ..) (walkM_pow_nonneg ..)
  · exact fun _ _ ↦ mul_nonneg (walkM_pow_nonneg ..) (walkM_pow_nonneg ..)
  · rintro ⟨u, v⟩ _
    dsimp only
    have he : (walkM G ^ a) u v * (walkM G ^ b) v u =
        (walkM G ^ a) v u * (walkM G ^ b) u v := by
      apply mul_left_cancel₀ (hw' u)
      linear_combination (walkM G ^ b) v u * walkM_balance G w hw a u v -
          (walkM G ^ a) v u * walkM_balance G w hw b u v
    apply le_of_eq
    linear_combination (walkM G ^ a) u v * (walkM G ^ b) v u * he

private theorem walkM_row {W : Type} [Fintype W] (G : SimpleGraph W) (m : ℕ)
    (u : W) (hu : 0 < G.degree u) : ∑ v, (walkM G ^ m) u v = 1 := by
  have row (z : W) (hz : 0 < G.degree z) : ∑ v, walkM G z v = 1 := by
    simp only [walkM, ← Finset.sum_filter, ← G.neighborFinset_eq_filter,
      sum_const, card_neighborFinset_eq_degree, nsmul_eq_mul]
    simp [hz.ne']
  induction m generalizing u with
  | zero => simp [Matrix.one_apply]
  | succ m ih =>
    simp only [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [← row u hu]
    apply sum_congr rfl
    intro z _
    by_cases h : G.Adj u z
    · rw [ih z h.degree_pos_right, mul_one]
    · simp [walkM, h]

theorem one_le_trace_walkM {W : Type} [Fintype W] (G : SimpleGraph W)
    (hG : G.edgeFinset.Nonempty) (k : ℕ) : 1 ≤ trace (walkM G ^ (2 * k)) := by
  let d (u : W) : ℝ := G.degree u
  let P := walkM G ^ k
  have hsum : ∑ p : W × W, d p.1 * P p.1 p.2 = ∑ u, d u := by
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro u _
    change (∑ v, d u * P u v) = d u
    rw [← Finset.mul_sum]
    by_cases hu : 0 < G.degree u
    · rw [show ∑ v, P u v = 1 from walkM_row G k u hu, mul_one]
    · simp [d, Nat.eq_zero_of_not_pos hu]
  have hsq : ∑ p : W × W, d p.1 * d p.2 = (∑ u, d u) ^ 2 := by
    rw [Fintype.sum_prod_type, sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have hpos : 0 < ∑ u, d u := by
    have h : 0 < ∑ u, G.degree u := by
      rw [G.sum_degrees_eq_twice_card_edges]; exact Nat.mul_pos (by decide) (card_pos.mpr hG)
    dsimp [d]
    exact_mod_cast h
  have hc : (∑ p : W × W, d p.1 * P p.1 p.2) ^ 2 ≤
      (∑ p : W × W, P p.1 p.2 * P p.2 p.1) * ∑ p : W × W, d p.1 * d p.2 := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · exact fun _ _ ↦ mul_nonneg (walkM_pow_nonneg ..) (walkM_pow_nonneg ..)
    · intro i _; dsimp [d]; positivity
    · rintro ⟨u, v⟩ _
      apply le_of_eq
      dsimp [d, P]
      linear_combination (G.degree u : ℝ) * (walkM G ^ k) u v * walkM_pow_rev G k u v
  rw [hsum, hsq, ← trace_split_walkM G k k] at hc
  rw [two_mul]
  exact le_of_mul_le_mul_right (by simpa only [one_mul] using hc :
    1 * (∑ u, d u) ^ 2 ≤ _ * _) (sq_pos_of_pos hpos)

theorem trace_walkM_interp {W : Type} [Fintype W] (G : SimpleGraph W)
    (hG : G.edgeFinset.Nonempty) (k : ℕ) (hk : 1 ≤ k) :
    trace (walkM G ^ (2 * (k - 1))) ≤
      (Fintype.card W : ℝ) ^ (1 / (k : ℝ)) * trace (walkM G ^ (2 * k)) ^ (1 - 1 / (k : ℝ)) := by
  let T (n : ℕ) := trace (walkM G ^ (2 * n))
  have pos (n : ℕ) : 0 < T n := lt_of_lt_of_le zero_lt_one (one_le_trace_walkM G hG n)
  let a (n : ℕ) := Real.log (T n)
  have step (n : ℕ) : a (n + 1) - a n ≤ a (n + 2) - a (n + 1) := by
    have h : T (n + 1) ^ 2 ≤ T n * T (n + 2) := by
      simpa [T] using trace_walkM_logconvex G (n + 1) (by omega)
    have h' := Real.log_le_log (sq_pos_of_pos (pos _)) h
    rw [Real.log_pow, Real.log_mul (pos _).ne' (pos _).ne'] at h'
    dsimp [a]; norm_num at h'; linarith
  have bound (n : ℕ) : a n - a 0 ≤ (n : ℝ) * (a (n + 1) - a n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      linarith [mul_le_mul_of_nonneg_left (step n) (Nat.cast_nonneg (α := ℝ) n), step n]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hc : T 0 = Fintype.card W := by simp [T]
  rw [← hc]
  change T (n + 1 - 1) ≤ T 0 ^ (1 / ((n + 1 : ℕ) : ℝ)) * T (n + 1) ^ (1 - 1 / ((n + 1 : ℕ) : ℝ))
  rw [Nat.add_sub_cancel]
  apply (Real.log_le_log_iff (pos _) (mul_pos (Real.rpow_pos_of_pos (pos _) _) (Real.rpow_pos_of_pos (pos _) _))).mp
  rw [Real.log_mul (Real.rpow_pos_of_pos (pos _) _).ne' (Real.rpow_pos_of_pos (pos _) _).ne',
    Real.log_rpow (pos _), Real.log_rpow (pos _)]
  change a n ≤ 1 / ((n + 1 : ℕ) : ℝ) * a 0 + (1 - 1 / ((n + 1 : ℕ) : ℝ)) * a (n + 1)
  push_cast
  field_simp
  linarith [bound n]

/-- Union sur les rotations : un conflit entre deux positions quelconques se ramène, par
rotation, à un conflit entre la position 0 et une position de `[1, k]`. -/
theorem bad_le_rot {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (r : W → W → Prop) (hr : ∀ u w, r u w → r w u) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W,
        (if ∃ i j : Fin (2 * k), i ≠ j ∧ r (x i) (x j) then cycW M x else 0) ≤
      2 * k * ∑ x : Fin (2 * k) → W,
        (if ∃ j : Fin (2 * k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (x ⟨0, by omega⟩) (x j)
          then cycW M x else 0) := by
  classical
  let : NeZero (2 * k) := ⟨by omega⟩
  let I := Fin (2 * k)
  let rot (s : I) (x : I → W) := fun i : I ↦ x (i + s)
  let good (x : I → W) := ∃ j : I, 1 ≤ j.val ∧ j.val ≤ k ∧ r (x 0) (x j)
  let B (x : I → W) : ℝ := if good x then cycW M x else 0
  have cycpos (x : I → W) : 0 ≤ cycW M x := prod_nonneg fun _ _ ↦ hM ..
  have bpos (x : I → W) : 0 ≤ B x := by dsimp [B]; split <;> simp_all only [le_refl]
  let δ : I := ⟨1, by omega⟩
  have cyc (s : I) (x : I → W) : cycW M (rot s x) = cycW M x := by
    change (∏ i : I, M (x (i + s)) (x ((i + δ) + s))) = ∏ i : I, M (x i) (x (i + δ))
    simp_rw [add_right_comm _ δ s]
    exact Equiv.prod_comp (Equiv.addRight s) (fun i : I ↦ M (x i) (x (i + δ)))
  have reindex (s : I) : ∑ x : I → W, B (rot s x) = ∑ x : I → W, B x := by
    exact Equiv.sum_comp ((Equiv.addRight s).symm.arrowCongr (Equiv.refl W)) B
  have ordered (x : I → W) (i j : I) (hlt : i.val < j.val) (hij : r (x i) (x j)) :
      ∃ s : I, good (rot s x) := by
    by_cases h : j.val - i.val ≤ k
    · let t : I := ⟨j.val - i.val, by have := j.isLt; omega⟩
      have ht : t + i = j := by
        apply Fin.ext
        rw [Fin.val_add_eq_ite]; dsimp [t]; split <;> have := j.isLt <;> omega
      exact ⟨i, t, by dsimp [t]; omega, h, by simpa [rot, ht] using hij⟩
    · let t : I := ⟨2 * k - j.val + i.val, by have := j.isLt; omega⟩
      have ht : t + j = i := by
        apply Fin.ext
        rw [Fin.val_add_eq_ite]; dsimp [t]; split <;> have := j.isLt <;> omega
      exact ⟨j, t, by dsimp [t]; have := j.isLt; omega, by dsimp [t]; omega,
        by simpa [rot, ht] using hr _ _ hij⟩
  change _ ≤ 2 * (k : ℝ) * ∑ x : I → W, B x
  calc
    _ ≤ ∑ x : I → W, ∑ s : I, B (rot s x) := by
      apply sum_le_sum
      intro x _
      split
      · rename_i hx
        obtain ⟨i, j, hne, hij⟩ := hx
        have hval : i.val ≠ j.val := fun h ↦ hne (Fin.ext h)
        obtain ⟨s, hs⟩ : ∃ s : I, good (rot s x) :=
          (lt_or_gt_of_ne hval).elim (fun h ↦ ordered x i j h hij) (fun h ↦ ordered x j i h (hr _ _ hij))
        calc
          cycW M x = B (rot s x) := by simp [B, hs, cyc]
          _ ≤ _ := single_le_sum (fun z _ ↦ bpos (rot z x)) (mem_univ s)
      · exact sum_nonneg fun _ _ ↦ bpos _
    _ = _ := by rw [sum_comm]; simp [reindex, I]

end E147H3

namespace E147JE

/-- Lemme 2.5 de Janzer (arXiv 2109.06110), sous forme asymptotique : l'hypothèse `H3` de la
réduction R1 de la variante cubique, prouvée ci-dessous (`h3_holds`). -/
def H3 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ θ : ℝ, 0 < θ → ∀ᶠ N : ℕ in atTop,
    ∀ (W : Type) [Fintype W], Fintype.card W = N →
    ∀ (G : SimpleGraph W) (r : W → W → Prop), (∀ u w, r u w → r w u) →
    G.edgeFinset.Nonempty →
    (∀ u v, (#((G.neighborFinset v).filter (r u)) : ℝ) ≤
        (N : ℝ) ^ (-(1 / (k : ℝ) + θ)) * G.degree v) →
    ∃ x : Fin (2 * k) → W,
      (∀ i, G.Adj (x i) (x ⟨(i.val + 1) % (2 * k), Nat.mod_lt _ i.pos⟩)) ∧
      ∀ i j, i ≠ j → ¬ r (x i) (x j)

open E147H3 in
private theorem total_cycW_eq_trace {W : Type} [Fintype W] (M : Matrix W W ℝ)
    (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W, cycW M x = trace (M ^ (2 * k)) := by
  classical
  calc
    _ = trace (M * (M ^ (1 - 1 : ℕ) * (M ^ (k + 1 - 1) * M ^ (k - 1)))) := by
      simpa only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum,
        mul_one, mul_assoc] using cyc_split M k 1 hk le_rfl (by omega) (fun _ _ _ _ => 1)
    _ = _ := by
      simp only [← pow_add, ← pow_succ']
      congr 2
      omega

private theorem strict_conflict_bound {n k θ p t : ℝ} (hn : 0 < n) (hk : 0 < k)
    (ht : 1 ≤ t) (hp : p ≤ n ^ (1 / k) * t ^ (1 - 1 / k))
    (hbig : 4 * k ^ 3 < n ^ θ) :
    2 * k * Real.sqrt (k * n ^ (-(1 / k + θ)) * p * t) < t := by
  have ht' : 0 < t := zero_lt_one.trans_le ht
  have h2k : 0 < 2 * k := by positivity
  have hp' : p ≤ n ^ (1 / k) * t := hp.trans (mul_le_mul_of_nonneg_left
    (calc
      t ^ (1 - 1 / k) ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht (by
        have : 0 ≤ 1 / k := by positivity
        linarith)
      _ = t := Real.rpow_one _) (Real.rpow_nonneg hn.le _))
  have hexp : n ^ (-(1 / k + θ)) * n ^ (1 / k) = (n ^ θ)⁻¹ := by
    rw [← Real.rpow_add hn, show -(1 / k + θ) + 1 / k = -θ by ring, Real.rpow_neg hn.le]
  have hfac : 4 * k ^ 3 * (n ^ θ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one (Real.rpow_pos_of_pos hn _)]
    exact hbig
  rw [mul_comm (2 * k), ← lt_div_iff₀ h2k, Real.sqrt_lt' (div_pos ht' h2k), div_pow,
    lt_div_iff₀ (sq_pos_of_pos h2k)]
  calc
    _ ≤ k * n ^ (-(1 / k + θ)) * (n ^ (1 / k) * t) * t * (2 * k) ^ 2 := by
      gcongr
    _ = (4 * k ^ 3 * (n ^ (-(1 / k + θ)) * n ^ (1 / k))) * t ^ 2 := by ring
    _ < t ^ 2 := by
      rw [hexp]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hfac (sq_pos_of_pos ht')

open E147H3 in
theorem h3_holds : H3 := by
  classical
  intro k hk θ hθ
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, hlim.eventually_gt_atTop (4 * (k : ℝ) ^ 3)]
    with N hN hbig
  intro W _ hW G r hr hG hrel
  let M := walkM G
  let bad (x : Fin (2 * k) → W) := ∃ i j, i ≠ j ∧ r (x i) (x j)
  have ht := one_le_trace_walkM G hG k
  have hp := trace_walkM_interp G hG k (by omega)
  rw [hW] at hp
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hc := conflict0_le G r hr _ (Real.rpow_nonneg hN'.le _) hrel (walkM_pow_rev G) k hk
  have hbad : (∑ x : Fin (2 * k) → W, if bad x then cycW M x else 0) <
      trace (M ^ (2 * k)) :=
    (bad_le_rot M (walkM_nonneg G) r hr k hk).trans_lt
      ((mul_le_mul_of_nonneg_left hc (by positivity)).trans_lt
        (strict_conflict_bound hN' hk' ht hp hbig))
  obtain ⟨x, hx, hb⟩ : ∃ x : Fin (2 * k) → W, cycW M x ≠ 0 ∧ ¬ bad x := by
    by_contra h
    apply (not_le_of_gt hbad)
    rw [← total_cycW_eq_trace M k hk]
    apply Finset.sum_le_sum
    intro x _
    split_ifs with hb
    · exact le_rfl
    · by_cases hw : cycW M x = 0
      · rw [hw]
      · exact (h ⟨x, hw, hb⟩).elim
  refine ⟨x, ?_, fun i j hij hr' => hb ⟨i, j, hij, hr'⟩⟩
  intro i
  by_contra hadj
  apply hx
  unfold cycW
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [M, walkM, hadj])

/- ## Le graphe `C_{2k}[t]` et le passage à `Fin q` -/

/-- Le graphe `C_{2k}[t]` : `(i, a) ~ (j, b)` ssi `i` et `j` sont voisins sur le cycle `C_{2k}`. -/
def blowup (k t : ℕ) : SimpleGraph (Fin (2 * k) × Fin t) :=
  SimpleGraph.fromRel fun p q => (p.1.val + 1) % (2 * k) = q.1.val

private theorem blowup_step {n u v : ℕ} (hu : u < n) :
    (u + 1) % n = v ↔ u + 1 = v ∧ v < n ∨ u + 1 = n ∧ v = 0 := by
  by_cases h : u + 1 < n
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have he : u + 1 = n := by omega
    rw [he, Nat.mod_self]
    omega

/-- `C_{2k}[t]` est `2t`-régulier dès que `k ≥ 2`. -/
theorem blowup_regular (k t : ℕ) (hk : 2 ≤ k) : (blowup k t).IsRegularOfDegree (2 * t) := by
  intro ⟨i, a⟩
  have hi := i.isLt
  let p : Fin (2 * k) := ⟨(i.val + 1) % (2 * k), Nat.mod_lt _ i.pos⟩
  let q : Fin (2 * k) := ⟨if i.val = 0 then 2 * k - 1 else i.val - 1, by split <;> omega⟩
  have hp : i.val + 1 = p.val ∧ p.val < 2 * k ∨ i.val + 1 = 2 * k ∧ p.val = 0 :=
    (blowup_step hi).mp rfl
  have hq (j : Fin (2 * k)) : (j.val + 1) % (2 * k) = i.val ↔ j.val = q.val := by
    rw [blowup_step j.isLt]
    have hj := j.isLt
    dsimp only [q]
    split <;> omega
  have hip : i.val ≠ p.val := by omega
  have hiq : i.val ≠ q.val := by dsimp only [q]; split <;> omega
  have hpq : p ≠ q := by rw [Ne, Fin.ext_iff]; dsimp only [q]; split <;> omega
  have N : (blowup k t).neighborFinset (i, a) = ({p, q} : Finset _) ×ˢ univ := by
    ext ⟨j, b⟩
    have hp' : (i.val + 1) % (2 * k) = j.val ↔ j.val = p.val := eq_comm
    rw [SimpleGraph.mem_neighborFinset]
    simp only [blowup, SimpleGraph.fromRel_adj, ne_eq, Prod.mk.injEq, Fin.ext_iff,
      mem_product, mem_insert, mem_singleton, mem_univ, and_true, hp', hq]
    grind only
  rw [← SimpleGraph.card_neighborFinset_eq_degree, N]
  simp [hpq]

/-- `C_{2k}[t]` est biparti : couleur `i mod 2`. -/
theorem blowup_bipartite (k t : ℕ) : (blowup k t).IsBipartite := by
  let f (a : Fin (2 * k) × Fin t) : Fin 2 := ⟨a.1.val % 2, Nat.mod_lt _ (by decide)⟩
  refine ⟨Coloring.mk f ?_⟩
  intro a b h he
  have ec : a.1.val % 2 = b.1.val % 2 := congrArg Fin.val he
  rcases h.2 with hab | hba
  · have hs := (blowup_step a.1.isLt).mp hab
    omega
  · have hs := (blowup_step b.1.isLt).mp hba
    omega

/-- Si, à partir d'un rang, tout graphe à `n` sommets et au moins `n^a` arêtes contient `H`,
alors `ex(n, H) = O(n^b)` pour tout `b ≥ a`. -/
theorem bigO_of_eventually_contains {W : Type*} (H : SimpleGraph W) (a b : ℝ) (hab : a ≤ b)
    (h : ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), (n : ℝ) ^ a ≤ #G.edgeFinset → H ⊑ G) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpos : (0 : ℝ) ≤ (n : ℝ) ^ a := Real.rpow_nonneg (by positivity) a
  have hex : (extremalNumber n H : ℝ) ≤ (n : ℝ) ^ a := by
    have key := (extremalNumber_le_iff_of_nonneg (V := Fin n) H hpos).2
    rw [Fintype.card_fin] at key
    apply key
    intro G inst hfree
    have hinst : inst = (fun _ _ => Classical.propDecidable _) := Subsingleton.elim _ _
    subst hinst
    by_contra hlt
    exact hfree (hn G (le_of_lt (not_le.mp hlt)))
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) b),
    one_mul]
  exact hex.trans (Real.rpow_le_rpow_of_exponent_le hn1' hab)

/-- Transport de `C_{2k}[t]` sur `Fin (2k·t)` et passage à `O(n^b)`. -/
theorem transfer_blowup (k t : ℕ) (hk : 2 ≤ k) (ht : 1 ≤ t) (a b : ℝ) (hab : a ≤ b)
    (h : ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), (n : ℝ) ^ a ≤ #G.edgeFinset →
      blowup k t ⊑ G) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsBipartite ∧ H.IsRegularOfDegree (2 * t) ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  let e := finProdFinEquiv (m := 2 * k) (n := t)
  have hk0 : 0 < k := by omega
  have ht0 : 0 < t := by omega
  refine ⟨2 * k * t, (blowup k t).map e.toEmbedding, by positivity, ?_, ?_, ?_⟩
  · exact Colorable.of_hom (SimpleGraph.Iso.map e _).symm.toHom (blowup_bipartite k t)
  · intro v
    have hd := (SimpleGraph.Iso.map e (blowup k t)).degree_eq (e.symm v)
    have hv : (SimpleGraph.Iso.map e (blowup k t)) (e.symm v) = v := by simp [SimpleGraph.Iso.map]
    rw [hv] at hd
    convert hd.trans (blowup_regular k t hk (e.symm v)) using 2
    rfl
  · have hcongr : ∀ n, extremalNumber n ((blowup k t).map e.toEmbedding) =
        extremalNumber n (blowup k t) := fun _ => extremalNumber_congr_right
          (SimpleGraph.Iso.map e (blowup k t)).symm
    simp_rw [hcongr]
    exact bigO_of_eventually_contains (blowup k t) a b hab h

/- ## Effeuillage : un sous-graphe où chaque sommet garde une part de son degré -/

/-- Si `2 ∑ f < ∑ deg` sur `S`, on retire un à un les sommets `y` de degré `< f y` : il reste
un ensemble non vide `T` où chaque `y` a au moins `f y` voisins dans `T`. -/
theorem exists_core {α : Type*} (A : α → α → Prop) (hA : ∀ a b, A a b → A b a) (f : α → ℝ)
    (S : Finset α) (h : 2 * ∑ y ∈ S, f y < ∑ y ∈ S, (#(S.filter (A y)) : ℝ)) :
    ∃ T ⊆ S, T.Nonempty ∧ ∀ y ∈ T, f y ≤ #(T.filter (A y)) := by
  classical
  revert h
  refine S.strongInductionOn ?_
  intro S ih h
  by_cases hall : ∀ y ∈ S, f y ≤ #(S.filter (A y))
  · refine ⟨S, Subset.rfl, nonempty_iff_ne_empty.mpr ?_, hall⟩
    rintro rfl
    simp at h
  push Not at hall
  obtain ⟨v, hv, hbad⟩ := hall
  let R := S.erase v
  have hdeg (y : α) : (#(S.filter (A y)) : ℝ) =
      #(R.filter (A y)) + (if A y v then 1 else 0) := by
    dsimp [R]
    rw [filter_erase]
    by_cases hy : A y v
    · rw [if_pos hy]
      exact_mod_cast (card_erase_add_one (mem_filter.mpr ⟨hv, hy⟩)).symm
    · simp [hy]
  have hcnt : #(R.filter (fun y => A y v)) ≤ #(S.filter (A v)) := by
    apply card_le_card
    intro y hy
    obtain ⟨hyR, hyv⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨mem_of_mem_erase hyR, hA _ _ hyv⟩
  have hsplit : (∑ y ∈ R, (#(S.filter (A y)) : ℝ)) =
      (∑ y ∈ R, (#(R.filter (A y)) : ℝ)) + #(R.filter (fun y => A y v)) := by
    simp_rw [hdeg]
    rw [sum_add_distrib, sum_boole]
  have hf := S.add_sum_erase f hv
  have hd := S.add_sum_erase (fun y => (#(S.filter (A y)) : ℝ)) hv
  change f v + ∑ y ∈ R, f y = _ at hf
  change (#(S.filter (A v)) : ℝ) + ∑ y ∈ R, (#(S.filter (A y)) : ℝ) = _ at hd
  have hcnt' : (#(R.filter (fun y => A y v)) : ℝ) ≤ #(S.filter (A v)) := by
    exact_mod_cast hcnt
  obtain ⟨T, hT, hne, hmin⟩ := ih R (erase_ssubset hv) (by linarith)
  exact ⟨T, hT.trans (erase_subset _ _), hne, hmin⟩

/- ## Graphe auxiliaire des `t`-parties (Janzer, définition 5.1, lemme 5.2) -/

/-- Parmi les `t`-parties de `C`, celles qui contiennent `v` sont une proportion `≤ t / #C`. -/
theorem card_filter_mem_powersetCard_mul {α : Type*} (C : Finset α) (t : ℕ) (v : α) :
    #((powersetCard t C).filter (fun z => v ∈ z)) * #C ≤ t * (#C).choose t := by
  classical
  by_cases hv : v ∈ C
  · cases t with
    | zero => simp
    | succ k =>
      have h := card_filter_powersetCard_subset ({v} : Finset α) C (k + 1)
        (singleton_subset_iff.mpr hv) (by simp)
      simp only [singleton_subset_iff, card_singleton, Nat.add_sub_cancel] at h
      rw [h, ← card_erase_add_one hv]
      simp only [Nat.add_sub_cancel]
      simpa only [mul_comm] using (Nat.add_one_mul_choose_eq (#(C.erase v)) k).le
  · have he : (powersetCard t C).filter (fun z => v ∈ z) = ∅ := by
      exact filter_eq_empty_iff.mpr fun _ hz hvz => hv ((mem_powersetCard.mp hz).1 hvz)
    simp [he]

private theorem aux_family_eq {V : Type*} [Fintype V] (G : SimpleGraph V) (t : ℕ) (y : Finset V) :
    (powersetCard t (univ : Finset V)).filter (fun z => ∀ a ∈ y, ∀ b ∈ z, G.Adj a b) =
      powersetCard t (univ.filter fun v => ∀ a ∈ y, G.Adj a v) := by
  ext z
  simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨fun b hb => mem_filter.mpr ⟨mem_univ _, fun a ha => h a ha b hb⟩, hz⟩
  · rintro ⟨h, hz⟩
    exact ⟨hz, fun a ha b hb => (mem_filter.mp (h hb)).2 a ha⟩

/-- Les voisins de `y` dans le graphe auxiliaire sont les `t`-parties du voisinage commun. -/
theorem card_aux_nbrs {V : Type*} [Fintype V] (G : SimpleGraph V) (t : ℕ) (y : Finset V) :
    #((powersetCard t (univ : Finset V)).filter (fun z => ∀ a ∈ y, ∀ b ∈ z, G.Adj a b)) =
      (#(univ.filter fun v => ∀ a ∈ y, G.Adj a v)).choose t := by
  rw [aux_family_eq, card_powersetCard]

/-- Lemme 5.2 : les voisins de `y` qui rencontrent `u` (`#u = t`) sont une proportion
`≤ t² / #N(y)` des voisins de `y`, où `N(y)` est le voisinage commun de `y`. -/
theorem card_meet_le {V : Type*} [Fintype V] (G : SimpleGraph V) (t : ℕ) (y u : Finset V)
    (hu : #u = t) :
    (#(((powersetCard t (univ : Finset V)).filter (fun z => ∀ a ∈ y, ∀ b ∈ z, G.Adj a b)).filter
        (fun z => ¬ Disjoint u z)) : ℝ) * #(univ.filter fun v => ∀ a ∈ y, G.Adj a v) ≤
      t * t * ((#(univ.filter fun v => ∀ a ∈ y, G.Adj a v)).choose t : ℝ) := by
  classical
  rw [aux_family_eq]
  let C := univ.filter fun v => ∀ a ∈ y, G.Adj a v
  let F := powersetCard t C
  let H (a : V) := F.filter fun z => a ∈ z
  have hsub : F.filter (fun z => ¬ Disjoint u z) ⊆ u.biUnion H := by
    intro z hz
    obtain ⟨hz, hmeet⟩ := mem_filter.mp hz
    obtain ⟨a, hau, haz⟩ := not_disjoint_iff.mp hmeet
    exact mem_biUnion.mpr ⟨a, hau, mem_filter.mpr ⟨hz, haz⟩⟩
  have h : #(F.filter (fun z => ¬ Disjoint u z)) * #C ≤ t * t * (#C).choose t := calc
    _ ≤ (∑ a ∈ u, #(H a)) * #C :=
      Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ a ∈ u, #(H a) * #C := sum_mul _ _ _
    _ ≤ ∑ _a ∈ u, t * (#C).choose t :=
      sum_le_sum fun a _ => card_filter_mem_powersetCard_mul C t a
    _ = _ := by simp [hu, mul_assoc]
  exact_mod_cast h

/- ## Comptage des `K_{t,t}` (Kővári–Sós–Turán / Erdős–Simonovits, sous forme convexe) -/

/-- Double comptage : `∑_y #N(y) = ∑_v C(d(v), t)` sur les `t`-parties `y`. -/
theorem sum_card_cn {V : Type*} [Fintype V] (G : SimpleGraph V) (t : ℕ) :
    ∑ y ∈ powersetCard t (univ : Finset V), #(univ.filter fun v => ∀ a ∈ y, G.Adj a v) =
      ∑ v, (G.degree v).choose t := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [← Finset.card_filter]
  have he : ((powersetCard t (univ : Finset V)).filter fun y => ∀ a ∈ y, G.Adj a v) =
      powersetCard t (G.neighborFinset v) := by
    ext y
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
    have h : (∀ a ∈ y, G.Adj a v) ↔ y ⊆ G.neighborFinset v := by
      constructor
      · intro H a ha
        exact (G.mem_neighborFinset _ _).mpr (H a ha).symm
      · intro H a ha
        exact ((G.mem_neighborFinset _ _).mp (H ha)).symm
    rw [h, and_comm]
  rw [he, card_powersetCard, G.card_neighborFinset_eq_degree]

/-- Jensen pour les coefficients binomiaux : `#s (μ + 1 - t)^t ≤ t! ∑ C(m_i, t)`, où `μ` est la
moyenne des `m_i`, dès que `μ ≥ t - 1`. -/
theorem jensen_choose {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (m : ι → ℕ) (t : ℕ)
    (ht : 1 ≤ t) (hμ : (t : ℝ) - 1 ≤ (∑ i ∈ s, (m i : ℝ)) / #s) :
    (#s : ℝ) * ((∑ i ∈ s, (m i : ℝ)) / #s + 1 - t) ^ t ≤
      (t.factorial : ℝ) * ∑ i ∈ s, ((m i).choose t : ℝ) := by
  let a (i : ι) : ℝ := (m i + 1 - t : ℕ)
  have hc : 0 < (#s : ℝ) := by exact_mod_cast hs.card_pos
  have ha (i : ι) : 0 ≤ a i := by dsimp [a]; positivity
  have hb (i : ι) : (m i : ℝ) + 1 - t ≤ a i := by
    rw [sub_le_iff_le_add]
    dsimp [a]
    exact_mod_cast (show m i + 1 ≤ m i + 1 - t + t by omega)
  have hav : (∑ i ∈ s, (m i : ℝ)) / #s + 1 - t ≤ (∑ i ∈ s, a i) / #s := by
    apply (le_div_iff₀ hc).mpr
    calc
      _ = ∑ i ∈ s, ((m i : ℝ) + 1 - t) := by
        simp only [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
        field_simp
      _ ≤ _ := sum_le_sum fun i _ => hb i
  have hp (i : ι) : a i ^ t ≤ (t.factorial : ℝ) * ((m i).choose t : ℝ) := by
    dsimp [a]
    exact_mod_cast ((Nat.pow_sub_le_descFactorial (m i) t).trans_eq
      (Nat.descFactorial_eq_factorial_mul_choose (m i) t))
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
  calc
    _ ≤ (#s : ℝ) * ((∑ i ∈ s, a i) / #s) ^ (p + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hav _) hc.le
    _ = (∑ i ∈ s, a i) ^ (p + 1) / (#s : ℝ) ^ p := by
      rw [div_pow, pow_succ (#s : ℝ)]
      field_simp
    _ ≤ ∑ i ∈ s, a i ^ (p + 1) := pow_sum_div_card_le_sum_pow (fun i _ => ha i) p
    _ ≤ _ := by rw [mul_sum]; exact sum_le_sum fun i _ => hp i

private theorem aux_shift_pow (t : ℕ) (ht : 1 ≤ t) (F C X U : ℝ)
    (hF : 0 ≤ F) (hC : 0 ≤ C) (hX : 1 ≤ X)
    (hU : X * (2 + t + 4 * F * (C ^ t + 1)) ≤ U) :
    4 * F * ((C * X) ^ t + 1) < (U + 1 - t) ^ t := by
  let A := 1 + 4 * F * (C ^ t + 1)
  have hA : 1 ≤ A := by dsimp [A]; linarith only [show 0 ≤ 4 * F * (C ^ t + 1) by positivity]
  have hshift : A * X ≤ U + 1 - t := by
    dsimp [A]
    nlinarith only [hU, hX, mul_nonneg (sub_nonneg.mpr hX) (Nat.cast_nonneg t : 0 ≤ (t : ℝ))]
  have hX' : 1 ≤ X ^ t := one_le_pow₀ hX
  calc
    _ ≤ 4 * F * (C ^ t + 1) * X ^ t := by
      rw [mul_pow]
      nlinarith only [mul_nonneg hF (sub_nonneg.mpr hX')]
    _ < A * X ^ t := by dsimp [A]; nlinarith only [hX']
    _ ≤ A ^ t * X ^ t := by
      apply mul_le_mul_of_nonneg_right _ (by linarith only [hX'])
      simpa using pow_le_pow_right₀ hA ht
    _ = (A * X) ^ t := (mul_pow ..).symm
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hshift t

/-- Beaucoup d'arêtes donnent beaucoup de `K_{t,t}` : la somme des degrés auxiliaires dépasse
`4 #P (L^t + 1)`, où `L = 4 t² n^(t(1/k + θ))` est le seuil de voisinage commun. -/
theorem many_aux_edges (t : ℕ) (ht : 1 ≤ t) (k : ℕ) (hk : 2 ≤ k) (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ (2 - 1 / (t : ℝ) + 1 / (k : ℝ) + 2 * θ) ≤ #G.edgeFinset →
      4 * (#(powersetCard t (univ : Finset (Fin n))) : ℝ) *
          ((4 * (t : ℝ) ^ 2 * (n : ℝ) ^ ((t : ℝ) * (1 / k + θ))) ^ t + 1) <
        ∑ y ∈ powersetCard t (univ : Finset (Fin n)),
          ((#(univ.filter fun v => ∀ a ∈ y, G.Adj a v)).choose t : ℝ) := by
  classical
  let a := 1 - 1 / (t : ℝ) + 1 / (k : ℝ) + 2 * θ
  let b := (t : ℝ) * (1 / (k : ℝ) + θ)
  let c := (t : ℝ) * θ
  let C := 4 * (t : ℝ) ^ 2
  let F := (t.factorial : ℝ)
  have ht1 : 1 ≤ (t : ℝ) := by exact_mod_cast ht
  have ht0 : 0 < (t : ℝ) := by linarith
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hF : 0 < F := by dsimp [F]; exact_mod_cast t.factorial_pos
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : 0 < a := by
    have hdiv : 1 / (t : ℝ) ≤ 1 := (div_le_iff₀ ht0).mpr (by linarith)
    dsimp [a]
    linarith only [hdiv, hθ, one_div_pos.mpr hk0]
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 < c := mul_pos ht0 hθ
  have ev (z : ℝ) (hz : 0 < z) (L : ℝ) : ∀ᶠ n : ℕ in atTop, L ≤ (n : ℝ) ^ z :=
    (tendsto_atTop.1 ((tendsto_rpow_atTop hz).comp tendsto_natCast_atTop_atTop)) L
  filter_upwards [eventually_ge_atTop t, ev a ha t, ev c hc (2 + t + 4 * F * (C ^ t + 1))]
    with n hnt hna hnc
  intro G he
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (ht.trans hnt)
  have hn : 0 < (n : ℝ) := by linarith
  let P := powersetCard t (univ : Finset (Fin n))
  let m (y : Finset (Fin n)) := #(univ.filter fun v => ∀ a ∈ y, G.Adj a v)
  let D := (∑ i, (G.degree i : ℝ)) / n
  let U := (∑ y ∈ P, (m y : ℝ)) / #P
  let X := (n : ℝ) ^ b
  let Y := (n : ℝ) ^ c
  have hX : 1 ≤ X := Real.one_le_rpow hn1 hb
  have hXY : 0 ≤ X * Y := by dsimp [X, Y]; positivity
  have hP : P.Nonempty := powersetCard_nonempty.mpr (by simpa using hnt)
  have hp : 0 < (#P : ℝ) := by exact_mod_cast hP.card_pos
  have hcount : (∑ y ∈ P, (m y : ℝ)) = ∑ i, ((G.degree i).choose t : ℝ) := by
    dsimp only [P, m]
    norm_cast
    convert! sum_card_cn G t using 1
    refine sum_congr rfl fun y _ => congrArg Finset.card ?_
    ext v
    simp only [mem_filter]
  have hdeg : (∑ i, (G.degree i : ℝ)) = 2 * (#G.edgeFinset : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hne : (n : ℝ) * (n : ℝ) ^ a ≤ (#G.edgeFinset : ℝ) := by
    calc
      _ = (n : ℝ) ^ (1 + a) := by rw [Real.rpow_add hn 1 a, Real.rpow_one]
      _ = (n : ℝ) ^ (2 - 1 / (t : ℝ) + 1 / (k : ℝ) + 2 * θ) := by
        congr 1
        dsimp [a]
        ring
      _ ≤ _ := he
  have hD : 2 * (n : ℝ) ^ a ≤ D := by
    apply (le_div_iff₀ hn).mpr
    rw [hdeg]
    linarith only [hne]
  have hDs : (n : ℝ) ^ a ≤ D + 1 - t := by linarith only [hD, hna]
  have hdμ : (t : ℝ) - 1 ≤ D := by linarith only [hDs, Real.rpow_pos_of_pos hn a]
  have Jd := jensen_choose (univ : Finset (Fin n)) ⟨⟨0, by omega⟩, mem_univ _⟩ (fun v => G.degree v) t ht
    (by simpa [D] using hdμ)
  change _ ≤ F * _ at Jd
  simp only [card_univ, Fintype.card_fin] at Jd
  have hbound : F * (#P : ℝ) ≤ (n : ℝ) ^ t := by
    dsimp [F, P]
    rw [card_powersetCard, card_univ, Fintype.card_fin]
    exact_mod_cast ((Nat.descFactorial_eq_factorial_mul_choose n t).symm.le.trans
      (Nat.descFactorial_le_pow n t))
  have hid : (n : ℝ) ^ t * (X * Y) = (n : ℝ) * ((n : ℝ) ^ a) ^ t := by
    calc
      _ = (n : ℝ) ^ ((t : ℝ) + (b + c)) := by
        rw [Real.rpow_add hn (t : ℝ) (b + c), Real.rpow_add hn b c, Real.rpow_natCast]
      _ = (n : ℝ) ^ (1 + a * t) := by
        congr 1
        dsimp [a, b, c]
        field_simp
        ring
      _ = _ := by rw [Real.rpow_add hn 1 (a * t), Real.rpow_one, Real.rpow_mul_natCast hn.le]
  have hlower : X * Y ≤ U := by
    apply (le_div_iff₀ hp).mpr
    apply le_of_mul_le_mul_left (a := F) _ hF
    calc
      _ = (F * (#P : ℝ)) * (X * Y) := by ring
      _ ≤ (n : ℝ) ^ t * (X * Y) := mul_le_mul_of_nonneg_right hbound hXY
      _ = _ := hid
      _ ≤ (n : ℝ) * (D + 1 - t) ^ t := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.rpow_nonneg hn.le a) hDs t) hn.le
      _ ≤ _ := by rw [hcount]; exact Jd
  have hlarge : X * (2 + t + 4 * F * (C ^ t + 1)) ≤ U :=
    (mul_le_mul_of_nonneg_left hnc (by linarith only [hX] : 0 ≤ X)).trans hlower
  have hUμ : (t : ℝ) - 1 ≤ U := by
    have hK : 0 ≤ 2 + (t : ℝ) + 4 * F * (C ^ t + 1) := by positivity
    have hz := mul_le_mul_of_nonneg_right hX hK
    nlinarith only [hz, hlarge, show 0 ≤ 4 * F * (C ^ t + 1) by positivity]
  have Jm := jensen_choose P hP m t ht hUμ
  have hstrict := aux_shift_pow t ht F C X U hF.le hC hX hlarge
  apply lt_of_mul_lt_mul_left (a := F) _ hF.le
  calc
    _ = (#P : ℝ) * (4 * F * ((C * X) ^ t + 1)) := by dsimp [P, C, X, b]; ring
    _ < (#P : ℝ) * (U + 1 - t) ^ t := mul_lt_mul_of_pos_left hstrict hp
    _ ≤ _ := Jm

/- ## Du cycle de `t`-parties disjointes à la copie de `C_{2k}[t]` -/

/-- Un `2k`-cycle homomorphe de `t`-parties deux à deux disjointes, chaque paire consécutive
formant un `K_{t,t}`, donne une copie de `C_{2k}[t]`. -/
theorem lift_walk {V : Type*} [LinearOrder V] (G : SimpleGraph V) (k t : ℕ)
    (x : Fin (2 * k) → Finset V) (hcard : ∀ i, #(x i) = t)
    (hadj : ∀ i, ∀ u ∈ x i, ∀ w ∈ x ⟨(i.val + 1) % (2 * k), Nat.mod_lt _ i.pos⟩, G.Adj u w)
    (hdisj : ∀ i j, i ≠ j → Disjoint (x i) (x j)) : blowup k t ⊑ G := by
  let φ (v : Fin (2 * k) × Fin t) : V := (x v.1).orderEmbOfFin (hcard v.1) v.2
  have hmem (i : Fin (2 * k)) (a : Fin t) : φ (i, a) ∈ x i :=
    (x i).orderEmbOfFin_mem (hcard i) a
  have hinj : Function.Injective φ := by
    rintro ⟨i, a⟩ ⟨j, b⟩ he
    have hij : i = j := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj i j hne) (hmem i a) (he ▸ hmem j b)
    subst j
    have hab : a = b := ((x i).orderEmbOfFin (hcard i)).injective he
    rw [hab]
  refine ⟨⟨⟨φ, ?_⟩, hinj⟩⟩
  rintro ⟨i, a⟩ ⟨j, b⟩ hab
  have step (r s : Fin (2 * k)) (u v : Fin t) (hs : (r.val + 1) % (2 * k) = s.val) :
      G.Adj (φ (r, u)) (φ (s, v)) := by
    have e : (⟨(r.val + 1) % (2 * k), Nat.mod_lt _ r.pos⟩ : Fin (2 * k)) = s := Fin.ext hs
    exact hadj r _ (hmem r u) _ (by rw [e]; exact hmem s v)
  rcases hab.2 with h | h
  · exact step i j a b h
  · exact (step j i b a h).symm

private theorem core_choose_lower (c t : ℕ) (ht : 1 ≤ t) (hc : t ≤ c) :
    c - t + 1 ≤ c.choose t := calc
  _ = (c - t + 1).choose (c - t) := (Nat.choose_succ_self_right _).symm
  _ ≤ c.choose (c - t) := Nat.choose_le_choose _ (by omega)
  _ = _ := Nat.choose_symm hc

private theorem core_ratio {b x d c q t : ℝ} (hb : 0 ≤ b) (hx : b ≤ x) (hc : 0 ≤ c) (ht : 0 < t)
    (hL : 4 * t ^ 2 * q ≤ c) (hM : x * c ≤ t * t * d)
    {deg : ℝ} (hd : d ≤ 4 * deg) : b * q ≤ deg := by
  apply le_of_mul_le_mul_left _ (show 0 < 4 * t ^ 2 by positivity)
  calc
    4 * t ^ 2 * (b * q) = b * (4 * t ^ 2 * q) := by ring
    _ ≤ b * c := mul_le_mul_of_nonneg_left hL hb
    _ ≤ x * c := mul_le_mul_of_nonneg_right hx hc
    _ ≤ t * t * d := hM
    _ ≤ t * t * (4 * deg) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

private theorem core_edge_instances {V : Type} {F : SimpleGraph V} {i j : Fintype F.edgeSet}
    (h : (@SimpleGraph.edgeFinset V F i).Nonempty) : (@SimpleGraph.edgeFinset V F j).Nonempty :=
  Subsingleton.elim i j ▸ h

private theorem core_bound_instances {V : Type} {F : SimpleGraph V} {v : V} {P : V → Prop}
    {a : ℝ} {i j : Fintype (F.neighborSet v)} {d e : DecidablePred P}
    (h : (#(@Finset.filter _ P d (@SimpleGraph.neighborFinset V F v i)) : ℝ) ≤
      a * (@SimpleGraph.degree V F v i)) :
    (#(@Finset.filter _ P e (@SimpleGraph.neighborFinset V F v j)) : ℝ) ≤
      a * (@SimpleGraph.degree V F v j) := by
  cases Subsingleton.elim i j
  cases Subsingleton.elim d e
  exact h

set_option maxHeartbeats 800000 in

/-- `H3` appliqué au graphe auxiliaire restreint au cœur `T`, avec la relation « se rencontrer ». -/
theorem walk_of_core (h3 : H3) (t : ℕ) (ht : 1 ≤ t) (k : ℕ) (hk : 2 ≤ k) (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : SimpleGraph (Fin n)) (T : Finset (Finset (Fin n))),
      T ⊆ powersetCard t univ → T.Nonempty →
      (∀ y ∈ T, 4 * (t : ℝ) ^ 2 * (n : ℝ) ^ ((t : ℝ) * (1 / k + θ)) ≤
          #(univ.filter fun v => ∀ a ∈ y, G.Adj a v) ∧
        ((#(univ.filter fun v => ∀ a ∈ y, G.Adj a v)).choose t : ℝ) ≤
          4 * #(T.filter fun z => ∀ a ∈ y, ∀ b ∈ z, G.Adj a b)) →
      ∃ x : Fin (2 * k) → Finset (Fin n), (∀ i, x i ∈ T) ∧
        (∀ i, ∀ u ∈ x i, ∀ w ∈ x ⟨(i.val + 1) % (2 * k), Nat.mod_lt _ i.pos⟩, G.Adj u w) ∧
        ∀ i j, i ≠ j → Disjoint (x i) (x j) := by
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (h3 k hk θ hθ)
  let s := 1 / (k : ℝ) + θ
  have hs : 0 < s := by dsimp [s]; positivity
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ ((t : ℝ) * s)) atTop atTop :=
    (tendsto_rpow_atTop (mul_pos ht' hs)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop (↑(4 * N₀ + t) : ℝ)] with n hn
  intro G T hTP hT hcore
  let A (y z : Finset (Fin n)) := ∀ a ∈ y, ∀ b ∈ z, G.Adj a b
  let C (y : Finset (Fin n)) := #(univ.filter fun v => ∀ a ∈ y, G.Adj a v)
  let q := (n : ℝ) ^ ((t : ℝ) * s)
  have hC (y) (hy : y ∈ T) : 4 * (t : ℝ) ^ 2 * q ≤ C y := (hcore y hy).1
  have hD (y) (hy : y ∈ T) : ((C y).choose t : ℝ) ≤ 4 * #(T.filter (A y)) :=
    (hcore y hy).2
  have hsize (y : ↥T) : #y.1 = t := (mem_powersetCard.mp (hTP y.2)).2
  let F : SimpleGraph ↥T := {
    Adj := fun y z => A y.1 z.1
    symm := ⟨fun _ _ h a ha b hb => (h b hb a ha).symm⟩
    loopless := ⟨fun y h => by
      obtain ⟨a, ha⟩ := card_pos.mp (show 0 < #y.1 by rw [hsize]; omega)
      exact G.loopless.irrefl a (h a ha a ha)⟩ }
  let r (u w : ↥T) := ¬ Disjoint u.1 w.1
  have hr (u w : ↥T) : r u w → r w u := fun h h' => h h'.symm
  have hdeg (v : ↥T) : F.degree v = #(T.filter (A v.1)) := by
    have he : (F.neighborFinset v).image Subtype.val = T.filter (A v.1) := by
      ext z
      constructor
      · intro hz
        obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
        exact mem_filter.mpr ⟨w.2, (F.mem_neighborFinset v w).mp hw⟩
      · intro hz
        obtain ⟨hzt, hA⟩ := mem_filter.mp hz
        exact mem_image.mpr ⟨⟨z, hzt⟩, (F.mem_neighborFinset _ _).mpr hA, rfl⟩
    rw [← he, card_image_of_injective _ Subtype.val_injective, card_neighborFinset_eq_degree]
  obtain ⟨y, hy⟩ := hT
  have hCy : 4 * N₀ + t ≤ C y := by
    have hcoef : 1 ≤ 4 * (t : ℝ) ^ 2 := by
      have ht₁ : (1 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith [sq_nonneg ((t : ℝ) - 1)]
    have hq : 0 ≤ q := Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact_mod_cast hn.trans ((le_mul_of_one_le_left hq hcoef).trans (hC y hy))
  have hlower := core_choose_lower (C y) t ht (by omega)
  have hdy : (C y).choose t ≤ 4 * #(T.filter (A y)) := by exact_mod_cast hD y hy
  have hle := card_filter_le T (A y)
  have hlarge : N₀ ≤ #T := by omega
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < #(T.filter (A y)) by omega)
  obtain ⟨hzT, hyz⟩ := mem_filter.mp hz
  have hedge : F.edgeFinset.Nonempty :=
    ⟨s((⟨y, hy⟩ : ↥T), ⟨z, hzT⟩), SimpleGraph.mem_edgeFinset.mpr hyz⟩
  have hTpos : 0 < (#T : ℝ) := by exact_mod_cast card_pos.mpr (show T.Nonempty from ⟨y, hy⟩)
  have hpow : (#T : ℝ) ^ s ≤ q := by
    have hcard : #T ≤ n ^ t := calc
      #T ≤ _ := card_le_card hTP
      _ = n.choose t := by simp
      _ ≤ _ := Nat.choose_le_pow _ _
    change (#T : ℝ) ^ s ≤ (n : ℝ) ^ ((t : ℝ) * s)
    rw [Real.rpow_natCast_mul (Nat.cast_nonneg _)]
    exact Real.rpow_le_rpow hTpos.le (by exact_mod_cast hcard) hs.le
  have hprop (u v : ↥T) : (#((F.neighborFinset v).filter (r u)) : ℝ) ≤
      (#T : ℝ) ^ (-s) * F.degree v := by
    let P := powersetCard t (univ : Finset (Fin n))
    let B := (F.neighborFinset v).filter (r u)
    let X := (P.filter (A v.1)).filter (fun z => ¬ Disjoint u.1 z)
    have hBX : #B ≤ #X := by
      apply card_le_card_of_injOn Subtype.val _ Subtype.val_injective.injOn
      intro w hw
      obtain ⟨hnbr, hmeet⟩ := mem_filter.mp hw
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hTP w.2, (F.mem_neighborFinset _ _).mp hnbr⟩, hmeet⟩
    have hmeet : (#X : ℝ) * C v.1 ≤ t * (t : ℝ) * ((C v.1).choose t : ℝ) := by
      dsimp only [X, P, A, C]
      convert card_meet_le G t v.1 u.1 (hsize u)
    rw [Real.rpow_neg hTpos.le, inv_mul_eq_div, le_div_iff₀ (Real.rpow_pos_of_pos hTpos s)]
    change (#B : ℝ) * (#T : ℝ) ^ s ≤ F.degree v
    apply (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)).trans
    rw [hdeg]
    exact core_ratio (Nat.cast_nonneg _) (by exact_mod_cast hBX) (Nat.cast_nonneg _) ht' (hC _ v.2)
      hmeet (hD _ v.2)
  obtain ⟨x, hx, hd⟩ := hN₀ _ hlarge ↥T (Fintype.card_coe T) F r hr
    (core_edge_instances hedge) (fun u v => core_bound_instances (hprop u v))
  exact ⟨fun i => (x i).1, fun i => (x i).2, hx, fun i j hij => not_not.mp (hd i j hij)⟩

/-- Théorème principal : tout graphe à `n` sommets et au moins `n^(2 - 1/t + 1/k + 2θ)` arêtes
contient `C_{2k}[t]`, pour `n` grand. -/
theorem contains_blowup (t : ℕ) (ht : 1 ≤ t) (k : ℕ) (hk : 2 ≤ k) (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ (2 - 1 / (t : ℝ) + 1 / (k : ℝ) + 2 * θ) ≤ #G.edgeFinset → blowup k t ⊑ G := by
  filter_upwards [many_aux_edges t ht k hk θ hθ, walk_of_core h3_holds t ht k hk θ hθ]
    with n hmany hwalk
  intro G hG
  have hm := hmany G hG
  have hw := hwalk G
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 4 * (t : ℝ) ^ 2 * (n : ℝ) ^ ((t : ℝ) * (1 / k + θ)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Finset (Fin n) → ℕ,
      ∀ y, c y = #(univ.filter fun v => ∀ a ∈ y, G.Adj a v) := ⟨_, fun _ => rfl⟩
  rw [← hL] at hm hw
  simp only [← hc] at hm hw
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hA : ∀ a b : Finset (Fin n), (∀ x ∈ a, ∀ y ∈ b, G.Adj x y) →
      ∀ x ∈ b, ∀ y ∈ a, G.Adj x y := fun a b h x hx y hy => (h y hy x hx).symm
  have hdeg : ∀ y, (#((powersetCard t univ).filter (fun z => ∀ a ∈ y, ∀ b ∈ z, G.Adj a b)) : ℝ) =
      ((c y).choose t : ℝ) := by
    intro y
    rw [hc]
    norm_cast
    convert card_aux_nbrs G t y
  let f : Finset (Fin n) → ℝ := fun y =>
    if L ≤ c y then ((c y).choose t : ℝ) / 4 else ((c y).choose t : ℝ) + 1
  have hfle : ∀ y, f y ≤ ((c y).choose t : ℝ) / 4 + (L ^ t + 1) := by
    intro y
    simp only [f]
    split_ifs with h
    · have : (0 : ℝ) ≤ L ^ t + 1 := by positivity
      linarith
    · push Not at h
      have h1 : ((c y).choose t : ℝ) ≤ (c y : ℝ) ^ t := by exact_mod_cast Nat.choose_le_pow (c y) t
      have h2 : (c y : ℝ) ^ t ≤ L ^ t := pow_le_pow_left₀ (Nat.cast_nonneg _) h.le t
      have h3 : (0 : ℝ) ≤ ((c y).choose t : ℝ) / 4 := by positivity
      linarith
  have key : 2 * ∑ y ∈ powersetCard t univ, f y <
      ∑ y ∈ powersetCard t univ, ((c y).choose t : ℝ) := by
    have h1 : ∑ y ∈ powersetCard t (univ : Finset (Fin n)), f y ≤
        ∑ y ∈ powersetCard t (univ : Finset (Fin n)), (((c y).choose t : ℝ) / 4 + (L ^ t + 1)) :=
      sum_le_sum fun y _ => hfle y
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_div] at h1
    linarith
  obtain ⟨T, hTP, hTne, hTf⟩ := exists_core (fun y z => ∀ a ∈ y, ∀ b ∈ z, G.Adj a b) hA f
    (powersetCard t univ) (by
      convert key using 3 with y hy
      have h := hdeg y
      norm_cast at h
      convert h)
  have hcore : ∀ y ∈ T, L ≤ c y ∧
      ((c y).choose t : ℝ) ≤ 4 * #(T.filter fun z => ∀ a ∈ y, ∀ b ∈ z, G.Adj a b) := by
    intro y hy
    have hfy := hTf y hy
    have hTPy : (#(T.filter fun z => ∀ a ∈ y, ∀ b ∈ z, G.Adj a b) : ℝ) ≤
        #((powersetCard t univ).filter (fun z => ∀ a ∈ y, ∀ b ∈ z, G.Adj a b)) := by
      exact_mod_cast card_le_card (filter_subset_filter _ hTP)
    rw [hdeg y] at hTPy
    have hfy' : f y ≤ #(T.filter fun z => ∀ a ∈ y, ∀ b ∈ z, G.Adj a b) := by
      convert hfy
    by_cases h : L ≤ c y
    · refine ⟨h, ?_⟩
      simp only [f, if_pos h] at hfy'
      linarith
    · simp only [f, if_neg h] at hfy'
      linarith
  obtain ⟨x, hxT, hxadj, hxdisj⟩ := hw T hTP hTne hcore
  exact lift_walk G k t x (fun i => (mem_powersetCard.1 (hTP (hxT i))).2) hxadj hxdisj

end E147JE

open E147JE in
theorem OMA.solution : OMA.R_Erdos147_erdos_147_variants_janzer_conjecture_R1.H1 := by
  intro r hr heven ε hε
  obtain ⟨t, rfl⟩ : ∃ t, r = 2 * t := ⟨r / 2, by obtain ⟨m, hm⟩ := heven; omega⟩
  have ht : 1 ≤ t := by omega
  have hθ : 0 < ε / 4 := by positivity
  set k : ℕ := ⌈2 / ε⌉₊ + 2 with hkdef
  have hk2 : 2 ≤ k := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk' : 1 / (k : ℝ) ≤ ε / 2 := by
    have h1 : 2 / ε ≤ (k : ℝ) := by
      have := Nat.le_ceil (2 / ε)
      have h2 : ((⌈2 / ε⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show ⌈2 / ε⌉₊ ≤ k by omega)
      linarith
    rw [div_le_iff₀ hkpos]
    rw [div_le_iff₀ hε] at h1
    linarith
  have hab : 2 - 1 / (t : ℝ) + 1 / (k : ℝ) + 2 * (ε / 4) ≤ 2 - 2 / ((2 * t : ℕ) : ℝ) + ε := by
    have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have h2t : 2 / ((2 * t : ℕ) : ℝ) = 1 / (t : ℝ) := by
      push_cast
      field_simp
    rw [h2t]
    linarith
  exact transfer_blowup k t hk2 ht _ _ hab (contains_blowup t ht k hk2 (ε / 4) hθ)
