import OMAReductions.R_Erdos147_erdos_147_variants_janzer_conjecture_R1

/-!
# Cubic step of the Janzer conjecture reduction

Specialization by Hanan Beer (@hananzlt). The assembled cubic proof is by
@drobison00 (PR4566, commit b79e8777ae6ba1d25bed90cf094a88eac6c63b5f).
Its reduction and three component proofs are by @iLc0 (PR3177, PR3513,
PR3725 and PR3868). The embedded Sidorenko arguments retain their provenance
from @JamesSlash (PR641), adapted from @TheWaler (PR478).
The target reduction is by @NicholasWierenga (PR3718).
Source: https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4566
This proves the existing cubic step only; the general Janzer conjecture
remains unresolved. All mathematical arguments below are reused.

Assembled proof of erdos-147-cubic from upstream reduction R1 and
verified step proofs R1.H1, R1.H2, and R1.H3.
-/

section R1Sec

/-
# Erdős 147, variante cubique : réduction R1

Traduction de Janzer, *Disproof of a conjecture of Erdős and Simonovits on the Turán number of
graphs with minimum degree 3* (arXiv 2109.06110), théorème 1.1 : pour tout `ε > 0`, il existe un
graphe biparti 3-régulier `H` avec `ex(n, H) = O(n^(4/3+ε))`. Le graphe est `H_(k,ℓ)` (définition
1.2), et le théorème 1.3 se prouve en trois étapes : régularisation, ensemble bon de `8k`-cycles,
ensemble agréable, copie de `H_(k,ℓ)`.

Tout est prouvé ici sauf trois lemmes de l'article, pris pour hypothèses :

- `H1` : lemme 2.14 (peu de 4-cycles : un ensemble bon de `8k`-cycles existe) ;
- `H2` : lemme 2.15 (beaucoup de 4-cycles : idem) ;
- `H3` : lemme 2.5 (cycle homomorphe sans conflit), sous forme asymptotique.

Prouvés dans ce fichier : `H_(k,ℓ)` biparti et 3-régulier, la régularisation (variante du
lemme 2.9, sans le lemme d'Erdős–Simonovits), le nettoyage des 4-cycles (lemme 2.10), le passage
d'un ensemble bon à un ensemble agréable (lemme 2.12), l'étape 3 (lemme 2.13) depuis `H3`,
l'étape 1 depuis `H1` et `H2`, le théorème 1.3 et le passage à `O(n^(4/3+ε))`.

Les 4-cycles sont comptés étiquetés `(a, b, c, d)` : chaque copie de `C₄` en donne 8, d'où les
facteurs 8 de `H1` et `H2` devant les bornes de l'article.
-/

-- Credit: @iLc0

open SimpleGraph Finset Filter Asymptotics
open scoped Classical

namespace OMA.R_Erdos147_erdos_147_variants_cubic_R1

/-- Lemme 2.14 de Janzer (peu de 4-cycles). L'hypothèse `ε < 1/6`, absente de l'article, affaiblit
l'énoncé. `c4` est l'ensemble des 4-cycles étiquetés, `nxt` la position suivante modulo `8k` ; la
conclusion est la définition 2.11 (ensemble `n^(-ε/2)`-bon non vide de `8k`-cycles). -/
def H1 : Prop :=
  ∀ ε K : ℝ, 0 < ε → ε < 1 / 6 → 0 < K → ∀ k : ℕ, 1 / ε ≤ k → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        let c4 : Finset (Fin n × Fin n × Fin n × Fin n) := univ.filter fun t =>
          G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
            t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2
        let nxt : Fin (8 * k) → Fin (8 * k) := fun i => ⟨(i.val + 1) % (8 * k), Nat.mod_lt _ i.pos⟩
        (n : ℝ) ^ (4 / 3 + ε) / 6 ≤ #G.edgeFinset →
        (∀ v, (G.degree v : ℝ) ≤ K * (n : ℝ) ^ (1 / 3 + ε)) →
        (∀ e ∈ G.edgeFinset, (#(c4.filter fun t => e = s(t.1, t.2.1) ∨ e = s(t.2.1, t.2.2.1) ∨
            e = s(t.2.2.1, t.2.2.2) ∨ e = s(t.2.2.2, t.1)) : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 3 + 2 * ε)) →
        ∃ C : Finset (Fin (8 * k) → Fin n), C.Nonempty ∧ ∃ s : ℝ, 0 < s ∧
          (∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))) ∧
          (∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s) ∧
          ∀ i : Fin (8 * k), ∃ P : Finset (Fin (8 * k) → Fin n),
            (#P : ℝ) ≤ (n : ℝ) ^ (-(ε / 2)) * #C / (16 * k * s) ∧
            ∀ x ∈ C, ∃ y ∈ P, ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j

/-- Lemme 2.15 de Janzer (beaucoup de 4-cycles) : `#c4 = 8 q` où `q` compte les copies de `C₄`. -/
def H2 : Prop :=
  ∀ ε K : ℝ, 0 < ε → ε < 1 / 6 → 0 < K → ∀ k : ℕ, 1 / ε ≤ k → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        let c4 : Finset (Fin n × Fin n × Fin n × Fin n) := univ.filter fun t =>
          G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
            t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2
        let nxt : Fin (8 * k) → Fin (8 * k) := fun i => ⟨(i.val + 1) % (8 * k), Nat.mod_lt _ i.pos⟩
        (∀ v, (G.degree v : ℝ) ≤ K * (n : ℝ) ^ (1 / 3 + ε)) →
        8 * (n : ℝ) ^ (5 / 3 + 3 * ε) / (96 * Real.log n) ≤ #c4 →
        (∀ e ∈ G.edgeFinset, (#(c4.filter fun t => e = s(t.1, t.2.1) ∨ e = s(t.2.1, t.2.2.1) ∨
            e = s(t.2.2.1, t.2.2.2) ∨ e = s(t.2.2.2, t.1)) : ℝ) ≤
            96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * #c4) →
        ∃ C : Finset (Fin (8 * k) → Fin n), C.Nonempty ∧ ∃ s : ℝ, 0 < s ∧
          (∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))) ∧
          (∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s) ∧
          ∀ i : Fin (8 * k), ∃ P : Finset (Fin (8 * k) → Fin n),
            (#P : ℝ) ≤ (n : ℝ) ^ (-(ε / 2)) * #C / (16 * k * s) ∧
            ∀ x ∈ C, ∃ y ∈ P, ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j

/-- Lemme 2.5 de Janzer (arXiv 2109.06110), sous forme asymptotique. -/
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

end OMA.R_Erdos147_erdos_147_variants_cubic_R1

namespace E147Step3

open OMA.R_Erdos147_erdos_147_variants_cubic_R1

/- Les positions directes et réfléchies placent chacune des deux colonnes dans un cycle. -/
private theorem s5_row_pos :
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    ∀ {k} (b) (j : Fin (4*k)), row (pos b j) = j := by
  intro phase pos row k b j
  apply Fin.ext
  have := j.isLt
  simp only [row, pos]
  split_ifs <;> omega

private theorem s5_side_pos :
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    ∀ {k} (b) (j : Fin (4*k)), side (pos b j) = b := by
  intro phase pos row side
  have row_pos : ∀ {k} (b) (j : Fin (4*k)), row (pos b j) = j := @s5_row_pos
  intro k b j
  simp only [side, row_pos]
  have := j.isLt
  cases b <;> cases e : phase j <;> simp [pos, e] <;> omega

private theorem s5_pos_side :
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    ∀ {k} (p : Fin (8*k)), pos (side p) (row p) = p := by
  intro phase pos row side k p
  apply Fin.ext
  have := p.isLt
  by_cases h : p.val < 4*k <;> cases e : phase (row p) <;>
    simp [pos, side, h, row] <;> omega

private theorem s5_pack_pos :
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    ∀ {V : Type} {k} (w : Bool → Fin (4*k) → V) (b j), pack w (pos b j) = w b j := by
  intro phase pos row side pack
  have row_pos : ∀ {k} (b) (j : Fin (4*k)), row (pos b j) = j := @s5_row_pos
  have side_pos : ∀ {k} (b) (j : Fin (4*k)), side (pos b j) = b := @s5_side_pos
  intro V k w b j
  simp [pack, side_pos, row_pos]

private theorem s5_nxt_val {L} (p : Fin L) :
    (p.val+1) % L = if p.val+1 < L then p.val+1 else 0 := by
  have hp := p.isLt
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [show p.val+1 = L by omega, Nat.mod_self]

private theorem s5_near_val :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let near {L} (p q : Fin L) : Prop := nxt p = q ∨ nxt q = p
    ∀ {L} (p q : Fin L), near p q ↔ (if p.val + 1 < L then p.val+1 else 0) = q.val ∨
      (if q.val + 1 < L then q.val+1 else 0) = p.val := by
  intro nxt near L p q
  simp only [near, Fin.ext_iff, nxt, s5_nxt_val]

private theorem s5_near_inner :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let near {L} (p q : Fin L) : Prop := nxt p = q ∨ nxt q = p
    ∀ {k} (b : Bool) (i j : Fin (4*k)) (_ : i.val+1=j.val)
    (_ : i.val % 2 = 0), near (pos b i) (pos b j) := by
  intro nxt phase pos near
  have near_val : ∀ {L} (p q : Fin L), near p q ↔ (if p.val + 1 < L then p.val+1 else 0) = q.val ∨
      (if q.val + 1 < L then q.val+1 else 0) = p.val := @s5_near_val
  intro k b i j h he
  have hi := i.isLt
  have hj := j.isLt
  cases b <;> by_cases ei : i.val / 2 % 2 = 1 <;> by_cases ej : j.val / 2 % 2 = 1 <;>
    simp [near_val, pos, phase, ei, ej] <;> split_ifs <;> omega

private theorem s5_near_cross :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let near {L} (p q : Fin L) : Prop := nxt p = q ∨ nxt q = p
    ∀ {k} (b : Bool) (i j : Fin (4*k)) (_ : i.val+1=j.val)
    (_ : i.val % 2 ≠ 0), near (pos b i) (pos (!b) j) := by
  intro nxt phase pos near
  have near_val : ∀ {L} (p q : Fin L), near p q ↔ (if p.val + 1 < L then p.val+1 else 0) = q.val ∨
      (if q.val + 1 < L then q.val+1 else 0) = p.val := @s5_near_val
  intro k b i j h he
  have hi := i.isLt
  have hj := j.isLt
  cases b <;> by_cases ei : i.val / 2 % 2 = 1 <;> by_cases ej : j.val / 2 % 2 = 1 <;>
    simp [near_val, pos, phase, ei, ej] <;> split_ifs <;> omega

private theorem s5_near_end :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let near {L} (p q : Fin L) : Prop := nxt p = q ∨ nxt q = p
    ∀ {k} (i : Fin (4*k)) (_ : i.val = 0 ∨ i.val+1=4*k), near (pos false i) (pos true i) := by
  intro nxt phase pos near
  have near_val : ∀ {L} (p q : Fin L), near p q ↔ (if p.val + 1 < L then p.val+1 else 0) = q.val ∨
      (if q.val + 1 < L then q.val+1 else 0) = p.val := @s5_near_val
  intro k i he
  have hi := i.isLt
  by_cases ei : i.val / 2 % 2 = 1 <;> simp [near_val, pos, phase, ei] <;> split_ifs <;> omega

/- Chaque coordonnée appartient à deux positions consécutives de sa propre colonne. -/
private theorem s5_nice_positions :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let _near {L} (p q : Fin L) : Prop := nxt p = q ∨ nxt q = p
    ∀ {k} (b : Bool) (j : Fin (4*k)), ∃ i : Fin (8*k),
    (pos b j = nxt i ∨ pos b j = nxt (nxt i)) ∧ side (nxt i) = b ∧ side (nxt (nxt i)) = b := by
  intro nxt phase pos row side near
  have side_pos : ∀ {k} (b) (j : Fin (4*k)), side (pos b j) = b := @s5_side_pos
  have near_inner : ∀ {k} (b : Bool) (i j : Fin (4*k)) (_ : i.val+1=j.val)
    (_ : i.val % 2 = 0), near (pos b i) (pos b j) := @s5_near_inner
  intro k b j
  have hp : ∀ p : Fin (8*k), ∃ i, nxt i = p := by
    intro p
    refine ⟨⟨if p.val = 0 then 8*k-1 else p.val-1, by have := p.isLt; split_ifs <;> omega⟩, ?_⟩
    apply Fin.ext
    have he (t : Fin (8*k)) : (nxt t).val = if t.val+1 < 8*k then t.val+1 else 0 := s5_nxt_val t
    rw [he]
    have := p.isLt
    simp only
    split_ifs <;> omega
  have hj := j.isLt
  let a : Fin (4*k) := ⟨2*(j.val/2), by omega⟩
  let d : Fin (4*k) := ⟨2*(j.val/2)+1, by omega⟩
  have hjad : j = a ∨ j = d := by
    simp only [Fin.ext_iff, a, d]
    omega
  have had := near_inner b a d (by rfl) (by simp [a])
  obtain ⟨p,q,he,hs,ht,hj'⟩ : ∃ p q, nxt p = q ∧ side p = b ∧ side q = b ∧
      (pos b j = p ∨ pos b j = q) := by
    rcases had with e | e
    · refine ⟨pos b a, pos b d, e, side_pos .., side_pos .., ?_⟩
      exact hjad.imp (congrArg (pos b)) (congrArg (pos b))
    · refine ⟨pos b d, pos b a, e, side_pos .., side_pos .., ?_⟩
      exact hjad.symm.imp (congrArg (pos b)) (congrArg (pos b))
  obtain ⟨i,hi⟩ := hp p
  exact ⟨i, by simpa only [hi,he] using hj', by simpa only [hi] using hs,
    by simpa only [hi,he] using ht⟩

private theorem s5_pack_inj :
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let _pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    ∀ {k n} (b) (y : Fin (4*k) → Fin n), Function.Injective (fun z => pack (mix b y z)) := by
  intro phase pos row side pack mix
  have pack_pos : ∀ {V : Type} {k} (w : Bool → Fin (4*k) → V) (b j), pack w (pos b j) = w b j := @s5_pack_pos
  intro k n b y z w h
  funext j
  simpa [pack_pos, mix] using congrFun h (pos b j)

private theorem s5_sum_fibers_bound {U K : Type*} [Fintype K] [DecidableEq K] (A : Finset U)
    (key : U → K) (P : U → Prop) [DecidablePred P] (β : ℝ)
    (h : ∀ q, (#((A.filter P).filter fun z => key z = q) : ℝ) ≤
      β * #(A.filter fun z => key z = q)) :
    (#(A.filter P) : ℝ) ≤ β * #A := by
  have h₁ := Finset.card_eq_sum_card_fiberwise (f := key) (s := A.filter P) (t := univ)
    (fun _ _ => mem_univ _)
  have h₂ := Finset.card_eq_sum_card_fiberwise (f := key) (s := A) (t := univ)
    (fun _ _ => mem_univ _)
  rw [h₁, h₂, Nat.cast_sum, Nat.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun q _ => h q

/- On fixe la colonne opposée et on somme la condition agréable sur les fibres de la restriction. -/
private theorem s5_slice_bound :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let _pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let slice {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) (b) (y : Fin (4*k) → Fin n) :=
      univ.filter fun z => pack (mix b y z) ∈ C
    ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : IsNice G k β C) (_hβ : 0 ≤ β)
    (b) (y : Fin (4*k) → Fin n) (j : Fin (4*k)) (u : Fin n), (#((slice C b y).filter fun z => z j = u) : ℝ) ≤ β * #(slice C b y) := by
  intro nxt AgreeOff IsCyc IsNice phase pos row side pack mix slice
  have pos_side : ∀ {k} (p : Fin (8*k)), pos (side p) (row p) = p := @s5_pos_side
  have pack_pos : ∀ {V : Type} {k} (w : Bool → Fin (4*k) → V) (b j), pack w (pos b j) = w b j := @s5_pack_pos
  have nice_positions : ∀ {k} (b : Bool) (j : Fin (4*k)), ∃ i : Fin (8*k),
    (pos b j = nxt i ∨ pos b j = nxt (nxt i)) ∧ side (nxt i) = b ∧ side (nxt (nxt i)) = b := @s5_nice_positions
  have pack_inj : ∀ {k n} (b) (y : Fin (4*k) → Fin n), Function.Injective (fun z => pack (mix b y z)) := @s5_pack_inj
  intro k n G β C hC hβ b y j u
  classical
  obtain ⟨i,hj,h1,h2⟩ := nice_positions b j
  let F := fun z => pack (mix b y z)
  let readB := fun (x : Fin (8*k) → Fin n) j => x (pos b j)
  have readF (z) : readB (F z) = z := by
    funext t
    simp [readB,F,pack_pos,mix]
  let key := fun z (p : {p : Fin (8*k) // p ≠ nxt i ∧ p ≠ nxt (nxt i)}) => F z p
  apply s5_sum_fibers_bound _ key
  intro q
  by_cases hq : ∃ z ∈ slice C b y, key z = q
  · obtain ⟨z₀,hz₀,rfl⟩ := hq
    have hoff (z) : key z = key z₀ ↔ AgreeOff i (F z) (F z₀) := by
      constructor
      · exact fun e p e₁ e₂ => congrFun e ⟨p,e₁,e₂⟩
      · exact fun e => funext fun p => e p p.2.1 p.2.2
    have inv (x) (hx : AgreeOff i x (F z₀)) : F (readB x) = x := by
      funext p
      by_cases hs : side p = b
      · simp only [F,pack,mix,hs,if_pos,readB]
        rw [← hs, pos_side]
      · have hn₁ : p ≠ nxt i := fun e => hs (e ▸ h1)
        have hn₂ : p ≠ nxt (nxt i) := fun e => hs (e ▸ h2)
        rw [hx p hn₁ hn₂]
        simp [F,pack,mix,hs]
    have ha := hC.2 i (F z₀) u
    apply le_trans _ (le_trans ha (mul_le_mul_of_nonneg_left _ hβ))
    · exact_mod_cast Finset.card_le_card_of_injOn F (by
        intro z hz
        obtain ⟨⟨hzC,hzu⟩,hzq⟩ := (show (z ∈ slice C b y ∧ z j = u) ∧ key z = key z₀ by
          simpa only [Finset.mem_coe,Finset.mem_filter] using hz)
        simp only [Finset.mem_coe, Finset.mem_filter]
        refine ⟨(mem_filter.mp hzC).2, (hoff z).mp hzq, ?_⟩
        have he : F z (pos b j) = u := by simpa [F,pack_pos,mix] using hzu
        rcases hj with e | e
        · exact Or.inl (e ▸ he)
        · exact Or.inr (e ▸ he)) (pack_inj b y).injOn
    · exact_mod_cast Finset.card_le_card_of_injOn readB (by
        intro x hx
        obtain ⟨hm,ho⟩ := mem_filter.mp hx
        have he := inv x ho
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, by change F (readB x) ∈ C; rwa [he]⟩,
          (hoff _).mpr (he.symm ▸ ho)⟩) (by
        intro x hx x' hx' e
        exact (inv _ (mem_filter.mp hx).2).symm.trans
          ((congrArg F e).trans (inv _ (mem_filter.mp hx').2)))
  · have hem : ((slice C b y).filter (fun z => z j = u)).filter (fun z => key z = q) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hq ⟨z,(mem_filter.mp (mem_filter.mp hz).1).1,(mem_filter.mp hz).2⟩
    rw [hem]
    simp only [card_empty, Nat.cast_zero]
    exact mul_nonneg hβ (Nat.cast_nonneg _)

private theorem s5_mix_flip :
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    ∀ {k n} (y z : Fin (4*k) → Fin n), mix true z y = mix false y z := by
  intro mix k n y z
  funext b; cases b <;> rfl

private theorem s5_aux_adj :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let _pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let slice {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) (b) (y : Fin (4*k) → Fin n) :=
      univ.filter fun z => pack (mix b y z) ∈ C
    let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
        SimpleGraph (Fin (4*k) → Fin n) :=
      SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
    ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (y z), (auxG C).Adj y z ↔ z ∈ slice C true y ∨ z ∈ slice C false y := by
  intro nxt AgreeOff IsCyc IsNice phase pos row side pack mix slice auxG
  have side_pos : ∀ {k} (b) (j : Fin (4*k)), side (pos b j) = b := @s5_side_pos
  have pack_pos : ∀ {V : Type} {k} (w : Bool → Fin (4*k) → V) (b j), pack w (pos b j) = w b j := @s5_pack_pos
  have mix_flip : ∀ {k n} (y z : Fin (4*k) → Fin n), mix true z y = mix false y z := @s5_mix_flip
  intro k n G β C hk hC y z
  simp only [auxG,SimpleGraph.fromRel_adj,mix_flip y z,slice,mem_filter,mem_univ,true_and]
  refine ⟨And.right, fun hz => ⟨?_,hz⟩⟩
  rintro rfl
  have hn (b : Bool) (hm : pack (mix b y y) ∈ C) : False := by
    let j : Fin (4*k) := ⟨0,by omega⟩
    have e := (hC.1 _ hm).1 (a₁ := pos true j) (a₂ := pos false j)
      (by simp [pack_pos,mix])
    have ee := congrArg side e
    simp [side_pos] at ee
  exact hz.elim (hn _) (hn _)

private theorem s5_aux_nonempty :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let _pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let _slice {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) (b) (y : Fin (4*k) → Fin n) :=
      univ.filter fun z => pack (mix b y z) ∈ C
    let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
        SimpleGraph (Fin (4*k) → Fin n) :=
      SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
    ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (_ : C.Nonempty), (auxG C).edgeFinset.Nonempty := by
  intro nxt AgreeOff IsCyc IsNice phase pos row side pack mix slice auxG
  have pos_side : ∀ {k} (p : Fin (8*k)), pos (side p) (row p) = p := @s5_pos_side
  have pack_pos : ∀ {V : Type} {k} (w : Bool → Fin (4*k) → V) (b j), pack w (pos b j) = w b j := @s5_pack_pos
  have aux_adj : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (y z), (auxG C).Adj y z ↔ z ∈ slice C true y ∨ z ∈ slice C false y := @s5_aux_adj
  intro k n G β C hk hC hne
  obtain ⟨x,hx⟩ := hne
  let y := fun j => x (pos false j)
  let z := fun j => x (pos true j)
  have he : pack (mix true y z) = x := by
    funext p
    rw [← pos_side p]
    simp only [pack_pos]
    cases e : side p <;> simp [mix,y,z]
  have ha : (auxG C).Adj y z := (aux_adj hk hC ..).mpr <| Or.inl <|
    mem_filter.mpr ⟨mem_univ _,he ▸ hx⟩
  exact ⟨s(y,z),mem_edgeFinset.mpr ha⟩

private theorem s5_aux_bound :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let _slice {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) (b) (y : Fin (4*k) → Fin n) :=
      univ.filter fun z => pack (mix b y z) ∈ C
    let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
        SimpleGraph (Fin (4*k) → Fin n) :=
      SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
    ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (_hβ : 0 ≤ β)
    (y) (j : Fin (4*k)) (u : Fin n), (#(((auxG C).neighborFinset y).filter fun z => z j = u) : ℝ) ≤ 2*β*(auxG C).degree y := by
  intro nxt AgreeOff IsCyc IsNice phase row side pack mix slice auxG
  have slice_bound : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : IsNice G k β C) (hβ : 0 ≤ β)
    (b) (y : Fin (4*k) → Fin n) (j : Fin (4*k)) (u : Fin n), (#((slice C b y).filter fun z => z j = u) : ℝ) ≤ β * #(slice C b y) := @s5_slice_bound
  have aux_adj : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (y z), (auxG C).Adj y z ↔ z ∈ slice C true y ∨ z ∈ slice C false y := @s5_aux_adj
  intro k n G β C hk hC hβ y j u
  classical
  have he : (auxG C).neighborFinset y = slice C true y ∪ slice C false y := by
    ext z
    simp only [mem_neighborFinset, mem_union, aux_adj hk hC]
  have hb (b) : (#(slice C b y) : ℝ) ≤ (auxG C).degree y := by
    rw [← card_neighborFinset_eq_degree,he]
    exact_mod_cast Finset.card_le_card (by cases b <;> simp : slice C b y ⊆ _)
  rw [he,filter_union]
  have hn := Finset.card_union_le ((slice C true y).filter fun z => z j = u)
    ((slice C false y).filter fun z => z j = u)
  have h₁ := (slice_bound hC hβ true y j u).trans (mul_le_mul_of_nonneg_left (hb true) hβ)
  have h₂ := (slice_bound hC hβ false y j u).trans (mul_le_mul_of_nonneg_left (hb false) hβ)
  exact (Nat.cast_le.mpr hn).trans (by push_cast; linarith)

/- Une collision est détectée par au moins une des (4k)² paires de coordonnées. -/
private theorem s5_collision_bound :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
        SimpleGraph (Fin (4*k) → Fin n) :=
      SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
    let collide {k n : ℕ} (y z : Fin (4*k) → Fin n) : Prop := ∃ a b, y a = z b
    ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (hβ : 0 ≤ β)
    (x v), (#(((auxG C).neighborFinset v).filter (collide x)) : ℝ) ≤
      32*(k : ℝ)^2*β*(auxG C).degree v := by
  intro nxt AgreeOff IsCyc IsNice phase row side pack mix auxG collide
  have aux_bound : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (hβ : 0 ≤ β)
    (y) (j : Fin (4*k)) (u : Fin n), (#(((auxG C).neighborFinset y).filter fun z => z j = u) : ℝ) ≤ 2*β*(auxG C).degree y := @s5_aux_bound
  intro k n G β C hk hC hβ x v
  classical
  let S := (auxG C).neighborFinset v
  let T := fun (p : Fin (4*k) × Fin (4*k)) => S.filter fun z => z p.2 = x p.1
  have hs : S.filter (collide x) ⊆ univ.biUnion T := by
    intro z hz
    obtain ⟨hz,a,b,he⟩ := mem_filter.mp hz
    exact mem_biUnion.mpr ⟨(a,b),mem_univ _,mem_filter.mpr ⟨hz,he.symm⟩⟩
  have hc := (card_le_card hs).trans (Finset.card_biUnion_le ..)
  calc
    _ ≤ ((∑ p, #(T p) : ℕ) : ℝ) := by exact_mod_cast hc
    _ = ∑ p, (#(T p) : ℝ) := by push_cast; rfl
    _ ≤ ∑ _p : Fin (4*k) × Fin (4*k), (2*β*(auxG C).degree v) :=
      sum_le_sum fun p _ => aux_bound hk hC hβ v p.2 (x p.1)
    _ = _ := by simp; ring

private theorem s5_aux_edges :
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let _pos {k : ℕ} (b : Bool) (j : Fin (4*k)) : Fin (8*k) :=
      ⟨if phase j = b then j.val else 8*k-1-j.val, by split <;> have := j.isLt <;> omega⟩
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let _near {L} (p q : Fin L) : Prop := nxt p = q ∨ nxt q = p
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let _slice {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) (b) (y : Fin (4*k) → Fin n) :=
      univ.filter fun z => pack (mix b y z) ∈ C
    let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
        SimpleGraph (Fin (4*k) → Fin n) :=
      SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
    ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) {y z}
    (_ : (auxG C).Adj y z), Function.Injective y ∧
    (∀ i j, i.val+1=j.val → i.val%2=0 → G.Adj (y i) (y j)) ∧
    (∀ i j, i.val+1=j.val → i.val%2≠0 → G.Adj (y i) (z j)) ∧
    (∀ i, i.val=0 ∨ i.val+1=4*k → G.Adj (y i) (z i)) := by
  intro nxt AgreeOff IsCyc IsNice phase pos row side pack near mix slice auxG
  have row_pos : ∀ {k} (b) (j : Fin (4*k)), row (pos b j) = j := @s5_row_pos
  have pack_pos : ∀ {V : Type} {k} (w : Bool → Fin (4*k) → V) (b j), pack w (pos b j) = w b j := @s5_pack_pos
  have near_inner : ∀ {k} (b : Bool) (i j : Fin (4*k)) (_ : i.val+1=j.val)
    (_ : i.val % 2 = 0), near (pos b i) (pos b j) := @s5_near_inner
  have near_cross : ∀ {k} (b : Bool) (i j : Fin (4*k)) (_ : i.val+1=j.val)
    (_ : i.val % 2 ≠ 0), near (pos b i) (pos (!b) j) := @s5_near_cross
  have near_end : ∀ {k} (i : Fin (4*k)) (_ : i.val = 0 ∨ i.val+1=4*k), near (pos false i) (pos true i) := @s5_near_end
  have aux_adj : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (y z), (auxG C).Adj y z ↔ z ∈ slice C true y ∨ z ∈ slice C false y := @s5_aux_adj
  intro k n G β C hk hC y z h
  obtain ⟨b,hm⟩ : ∃ b, pack (mix b y z) ∈ C := by
    rcases (aux_adj hk hC ..).mp h with h | h
    · exact ⟨true,(mem_filter.mp h).2⟩
    · exact ⟨false,(mem_filter.mp h).2⟩
  let w := mix b y z
  have hw : IsCyc G (pack w) := hC.1 _ hm
  have hy : w (!b) = y := by cases b <;> rfl
  have hz : w b = z := by simp [w,mix]
  have edge {t s : Bool} {i j} (he : near (pos t i) (pos s j)) :
      G.Adj (w t i) (w s j) := by
    rcases he with e | e
    · simpa only [e,pack_pos] using hw.2 (pos t i)
    · simpa only [e,pack_pos] using (hw.2 (pos s j)).symm
  refine ⟨?_,?_,?_,?_⟩
  · intro i j e
    have en := hw.1 (a₁ := pos (!b) i) (a₂ := pos (!b) j) (by simpa only [pack_pos,hy] using e)
    simpa only [row_pos] using congrArg row en
  · intro i j e h
    simpa only [hy] using edge (near_inner (!b) i j e h)
  · intro i j e h
    simpa only [Bool.not_not,hy,hz] using edge (near_cross (!b) i j e h)
  · intro i hi
    have e := edge (near_end i hi)
    cases b <;> first | exact e | exact e.symm

/- La copie lit la ligne dans la coordonnée et la colonne dans le cycle auxiliaire. -/
private theorem s5_lift_cycle :
    let hRel (k ℓ : ℕ) (a b : Fin (4 * k) × Fin (2 * ℓ)) : Prop :=
      (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)
    let Hkl (k ℓ : ℕ) : SimpleGraph (Fin (4 * k) × Fin (2 * ℓ)) := SimpleGraph.fromRel (hRel k ℓ)
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
    let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
      ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
    let side {k : ℕ} (p : Fin (8*k)) : Bool :=
      if p.val < 4*k then phase (row p) else !(phase (row p))
    let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
      w (side p) (row p)
    let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
      if t = b then z else y
    let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
        SimpleGraph (Fin (4*k) → Fin n) :=
      SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
    let collide {k n : ℕ} (y z : Fin (4*k) → Fin n) : Prop := ∃ a b, y a = z b
    ∀ {k ℓ n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C)
    (X : Fin (2*ℓ) → Fin (4*k) → Fin n)
    (_ : ∀ c, (auxG C).Adj (X c) (X (nxt c)))
    (_hd : ∀ i j, i ≠ j → ¬ collide (X i) (X j)), Hkl k ℓ ⊑ G := by
  intro hRel Hkl nxt AgreeOff IsCyc IsNice phase row side pack mix auxG collide
  have aux_edges : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) {y z}
    (_ : (auxG C).Adj y z), Function.Injective y ∧
    (∀ i j, i.val+1=j.val → i.val%2=0 → G.Adj (y i) (y j)) ∧
    (∀ i j, i.val+1=j.val → i.val%2≠0 → G.Adj (y i) (z j)) ∧
    (∀ i, i.val=0 ∨ i.val+1=4*k → G.Adj (y i) (z i)) := @s5_aux_edges
  intro k ℓ n G β C hk hC X hX hd
  let f := fun (a : Fin (4*k) × Fin (2*ℓ)) => X a.2 a.1
  have em {a b} (e : hRel k ℓ a b) : G.Adj (f a) (f b) := by
    rcases a with ⟨i,c⟩
    rcases b with ⟨j,d⟩
    change G.Adj (X c i) (X d j)
    rcases e with ⟨hi,hj⟩ | ⟨rfl,hi,hj⟩
    · by_cases hpar : i.val % 2 = 0
      · simp only [hpar,if_true] at hj
        subst d
        exact (aux_edges hk hC (hX c)).2.1 i j hi hpar
      · simp only [hpar,if_false] at hj
        rcases hj with hj | hj
        · have he : nxt c = d := Fin.ext hj
          exact he ▸ (aux_edges hk hC (hX c)).2.2.1 i j hi hpar
        · have he : nxt d = c := Fin.ext hj
          exact he ▸ (aux_edges hk hC (hX d).symm).2.2.1 i j hi hpar
    · have he : nxt c = d := Fin.ext hj
      exact he ▸ (aux_edges hk hC (hX c)).2.2.2 _ hi
  refine ⟨⟨⟨f,fun h => ?_⟩,?_⟩⟩
  · rcases h.2 with h | h
    · exact em h
    · exact (em h).symm
  · rintro ⟨i,c⟩ ⟨j,d⟩ e
    change X c i = X d j at e
    by_cases hcd : c = d
    · subst d
      exact Prod.ext ((aux_edges hk hC (hX c)).1 e) rfl
    · exact (hd c d hcd ⟨i,j,e⟩).elim

/- Les dénombrements ne dépendent pas des instances utilisées pour énumérer les ensembles finis. -/
private theorem s5_edge_instances {V : Type} {A : SimpleGraph V} {i j : Fintype A.edgeSet}
    (h : (@SimpleGraph.edgeFinset V A i).Nonempty) : (@SimpleGraph.edgeFinset V A j).Nonempty :=
  Subsingleton.elim i j ▸ h

private theorem s5_bound_instances {V : Type} {A : SimpleGraph V} {v : V} {P : V → Prop}
    {t : ℝ} {i j : Fintype (A.neighborSet v)} {d e : DecidablePred P}
    (h : (#(@Finset.filter _ P d (@SimpleGraph.neighborFinset V A v i)) : ℝ) ≤
      t * (@SimpleGraph.degree V A v i)) :
    (#(@Finset.filter _ P e (@SimpleGraph.neighborFinset V A v j)) : ℝ) ≤
      t * (@SimpleGraph.degree V A v j) := by
  cases Subsingleton.elim i j
  cases Subsingleton.elim d e
  exact h

private theorem s5_finish :
    let hRel (k ℓ : ℕ) (a b : Fin (4 * k) × Fin (2 * ℓ)) : Prop :=
      (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)
    let Hkl (k ℓ : ℕ) : SimpleGraph (Fin (4 * k) × Fin (2 * ℓ)) := SimpleGraph.fromRel (hRel k ℓ)
    let nxt {L : ℕ} (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    let AgreeOff {V : Type} {L : ℕ} (i : Fin L) (x y : Fin L → V) : Prop :=
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    let IsCyc {V : Type} (G : SimpleGraph V) {L : ℕ} (x : Fin L → V) : Prop :=
      Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))
    let IsNice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (β : ℝ)
        (C : Finset (Fin (8 * k) → Fin n)) : Prop :=
      (∀ x ∈ C, IsCyc G x) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            β * #(C.filter fun x => AgreeOff i x y)
    let Step3 : Prop :=
      ∀ δ : ℝ, 0 < δ → ∀ k ℓ : ℕ, 1 ≤ k → 2 ≤ ℓ → 8 * k / δ ≤ ℓ → ∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Fin n), ∀ C : Finset (Fin (8 * k) → Fin n), C.Nonempty →
          IsNice G k ((n : ℝ) ^ (-δ)) C → Hkl k ℓ ⊑ G
    ∀ (auxG : {k n : ℕ} → Finset (Fin (8*k) → Fin n) → SimpleGraph (Fin (4*k) → Fin n))
    (collide : {k n : ℕ} → (Fin (4*k) → Fin n) → (Fin (4*k) → Fin n) → Prop)
    (_ : ∀ {k n} (x y : Fin (4*k) → Fin n), collide x y → collide y x)
    (_ : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (_ : C.Nonempty), (auxG C).edgeFinset.Nonempty)
    (_ : ∀ {k n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C) (_hβ : 0 ≤ β)
    (x v), (#(((auxG C).neighborFinset v).filter (collide x)) : ℝ) ≤
      32*(k : ℝ)^2*β*(auxG C).degree v)
    (_ : ∀ {k ℓ n} {G : SimpleGraph (Fin n)} {β : ℝ}
    {C : Finset (Fin (8*k) → Fin n)} (_ : 1 ≤ k) (_ : IsNice G k β C)
    (X : Fin (2*ℓ) → Fin (4*k) → Fin n)
    (_ : ∀ c, (auxG C).Adj (X c) (X (nxt c)))
    (_hd : ∀ i j, i ≠ j → ¬ collide (X i) (X j)), Hkl k ℓ ⊑ G)
    (_ : H3), Step3 := by
  intro hRel Hkl nxt AgreeOff IsCyc IsNice Step3 auxG collide sym aux_nonempty collision_bound lift_cycle h
  classical
  intro δ hδ k ℓ hk hℓ hsize
  have hkr : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hlr : 0 < (ℓ : ℝ) := by exact_mod_cast (show 0 < ℓ by omega)
  let θ := δ / (16*k)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hN := (tendsto_pow_atTop (α := ℕ) (n := 4*k) (by omega)).eventually (h ℓ hℓ θ hθ)
  have hlarge := ((tendsto_rpow_atTop (show 0 < δ/4 by positivity)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (32*(k : ℝ)^2))
  filter_upwards [hN,hlarge,eventually_ge_atTop (1 : ℕ)] with n hn hbig hn₁
  intro G C hne hC
  have hnr : 1 ≤ (n : ℝ) := by exact_mod_cast hn₁
  have hnp : 0 < (n : ℝ) := by linarith
  change 32*(k : ℝ)^2 ≤ (n : ℝ)^(δ/4) at hbig
  have hratio : (4*(k : ℝ))*(1/(ℓ : ℝ)) ≤ δ/2 := by
    rw [← mul_div_assoc, mul_one, div_le_iff₀ hlr]
    have he := (div_le_iff₀ hδ).mp hsize
    nlinarith
  have hcancel : (4*(k : ℝ))*θ = δ/4 := by
    dsimp [θ]
    field_simp
    ring
  have hbound : 32*(k : ℝ)^2*(n : ℝ)^(-δ) ≤
      ((n^(4*k) : ℕ) : ℝ)^(-(1/(ℓ : ℝ)+θ)) := by
    calc
      _ ≤ (n : ℝ)^(δ/4)*(n : ℝ)^(-δ) := by gcongr
      _ = (n : ℝ)^(δ/4 + -δ) := (Real.rpow_add hnp ..).symm
      _ ≤ (n : ℝ)^((4*(k : ℝ))*(-(1/(ℓ : ℝ)+θ))) := by
        apply Real.rpow_le_rpow_of_exponent_le hnr
        rw [mul_neg,mul_add,hcancel]
        linarith
      _ = _ := by
        rw [Nat.cast_pow,← Real.rpow_natCast,← Real.rpow_mul hnp.le]
        norm_cast
  obtain ⟨X,hX,hd⟩ := hn (Fin (4*k) → Fin n) (by simp) (auxG C) collide
    sym (aux_nonempty hk hC hne)
    (fun x v => (collision_bound hk hC (Real.rpow_nonneg hnp.le _) x v).trans
      (mul_le_mul_of_nonneg_right hbound (by positivity)))
  exact lift_cycle hk hC X hX hd

theorem step3_of_H3 (h : H3) :
    ∀ δ : ℝ, 0 < δ → ∀ k ℓ : ℕ, 1 ≤ k → 2 ≤ ℓ → 8 * k / δ ≤ ℓ → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), ∀ C : Finset (Fin (8 * k) → Fin n), C.Nonempty →
      let nxt : Fin (8 * k) → Fin (8 * k) := fun i => ⟨(i.val + 1) % (8 * k), Nat.mod_lt _ i.pos⟩
      ((∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))) ∧
        ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → Fin n) (u : Fin n),
          (#(C.filter fun x => (∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j) ∧
              (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
            (n : ℝ) ^ (-δ) * #(C.filter fun x => ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j)) →
      SimpleGraph.fromRel (fun a b : Fin (4 * k) × Fin (2 * ℓ) =>
        (a.1.val + 1 = b.1.val ∧
            (if a.1.val % 2 = 0 then a.2 = b.2
             else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
          (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val))
        ⊑ G := by
  let phase {k : ℕ} (j : Fin (4*k)) : Bool := decide (j.val / 2 % 2 = 1)
  let row {k : ℕ} (p : Fin (8*k)) : Fin (4*k) :=
    ⟨if p.val < 4*k then p.val else 8*k-1-p.val, by split <;> have := p.isLt <;> omega⟩
  let side {k : ℕ} (p : Fin (8*k)) : Bool :=
    if p.val < 4*k then phase (row p) else !(phase (row p))
  let pack {V : Type} {k} (w : Bool → Fin (4*k) → V) (p : Fin (8*k)) : V :=
    w (side p) (row p)
  let mix {k n : ℕ} (b : Bool) (y z : Fin (4*k) → Fin n) (t : Bool) :=
    if t = b then z else y
  let auxG {k n : ℕ} (C : Finset (Fin (8*k) → Fin n)) :
      SimpleGraph (Fin (4*k) → Fin n) :=
    SimpleGraph.fromRel fun y z => pack (mix true y z) ∈ C
  let collide {k n : ℕ} (y z : Fin (4*k) → Fin n) : Prop := ∃ a b, y a = z b
  apply s5_finish @auxG @collide _ _ _ @s5_lift_cycle h
  · exact fun _ _ ⟨a,b,e⟩ => ⟨b,a,e.symm⟩
  · intro k n G β C hk hC he
    exact s5_edge_instances (s5_aux_nonempty hk hC he)
  · intro k n G β C hk hC hβ x v
    exact s5_bound_instances (s5_collision_bound hk hC hβ x v)

end E147Step3

namespace E147

open OMA.R_Erdos147_erdos_147_variants_cubic_R1

private theorem hkl_step {n u v : ℕ} (hu : u < n) :
    (u + 1) % n = v ↔ u + 1 = v ∧ v < n ∨ u + 1 = n ∧ v = 0 := by
  by_cases h : u + 1 < n
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have he : u + 1 = n := by omega
    rw [he, Nat.mod_self]
    omega

private theorem hkl_step_color {k ℓ : ℕ} {a b : Fin (4 * k) × Fin (2 * ℓ)}
    (h : (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)) :
    (a.2.val + (a.1.val + 1) / 2) % 2 ≠ (b.2.val + (b.1.val + 1) / 2) % 2 := by
  simp only [Fin.ext_iff, hkl_step a.2.isLt, hkl_step b.2.isLt] at h
  rcases h with ⟨_, h⟩ | ⟨_, _, h⟩
  · split at h <;> omega
  · omega

set_option maxHeartbeats 1000000 in
/-- `H_{k,ℓ}` est 3-régulier. -/
theorem hkl_regular (k ℓ : ℕ) (hk : 1 ≤ k) (hl : 2 ≤ ℓ) :
    let hRel := fun a b : Fin (4 * k) × Fin (2 * ℓ) =>
      (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)
    (SimpleGraph.fromRel hRel).IsRegularOfDegree 3 := by
  intro hRel ⟨r, c⟩
  have hr := r.isLt
  have hc := c.isLt
  let m : Fin (4 * k) := ⟨if r.val % 2 = 0 then r.val + 1 else r.val - 1, by
    split <;> omega⟩
  let x : Fin (4 * k) := ⟨if r.val % 2 = 0 then r.val - 1 else min (r.val + 1) (4 * k - 1), by
    simp only [Nat.min_def]
    split_ifs <;> omega⟩
  let p : Fin (2 * ℓ) := ⟨(c.val + 1) % (2 * ℓ), Nat.mod_lt _ (by omega)⟩
  let q : Fin (2 * ℓ) := ⟨if c.val = 0 then 2 * ℓ - 1 else c.val - 1, by split <;> omega⟩
  have hp : c.val + 1 = p.val ∧ p.val < 2 * ℓ ∨ c.val + 1 = 2 * ℓ ∧ p.val = 0 :=
    (hkl_step hc).mp rfl
  have hq (d : Fin (2 * ℓ)) : (d.val + 1) % (2 * ℓ) = c.val ↔ d.val = q.val := by
    rw [hkl_step d.isLt]
    have hd := d.isLt
    dsimp only [q]
    split <;> omega
  have hpq : p.val ≠ q.val := by dsimp only [q]; split <;> omega
  have hcp : c.val ≠ p.val := by omega
  have hcq : c.val ≠ q.val := by dsimp only [q]; split <;> omega
  have N : (SimpleGraph.fromRel hRel).neighborFinset (r, c) = {(m, c), (x, p), (x, q)} := by
    ext ⟨s, d⟩
    have hs := s.isLt
    have hm : s.val = m.val ↔
        r.val + 1 = s.val ∧ r.val % 2 = 0 ∨ s.val + 1 = r.val ∧ s.val % 2 = 0 := by
      dsimp only [m]
      split <;> omega
    have hx : s.val = x.val ↔
        r.val + 1 = s.val ∧ r.val % 2 ≠ 0 ∨ s.val + 1 = r.val ∧ s.val % 2 ≠ 0 ∨
        r.val = s.val ∧ (r.val = 0 ∨ r.val + 1 = 4 * k) := by
      dsimp only [x]
      simp only [Nat.min_def]
      split_ifs <;> omega
    have hp' : (c.val + 1) % (2 * ℓ) = d.val ↔ d.val = p.val := eq_comm
    rw [SimpleGraph.mem_neighborFinset]
    simp only [SimpleGraph.fromRel_adj, hRel, mem_insert,
      mem_singleton, ne_eq, Prod.mk.injEq, Fin.ext_iff, hp', hq, hm, hx, ite_prop_iff_or]
    grind only
  rw [← SimpleGraph.card_neighborFinset_eq_degree, N]
  simp [Fin.ext_iff, hcp, hcq, hpq]

/-- `H_{k,ℓ}` est biparti. -/
theorem hkl_bipartite (k ℓ : ℕ) :
    let hRel := fun a b : Fin (4 * k) × Fin (2 * ℓ) =>
      (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)
    (SimpleGraph.fromRel hRel).IsBipartite := by
  intro hRel
  let f (a : Fin (4 * k) × Fin (2 * ℓ)) : Fin 2 :=
    ⟨(a.2.val + (a.1.val + 1) / 2) % 2, Nat.mod_lt _ (by decide)⟩
  refine ⟨Coloring.mk f ?_⟩
  intro a b h he
  have e := congrArg Fin.val he
  rcases h.2 with hab | hba
  · exact hkl_step_color hab e
  · exact hkl_step_color hba e.symm

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

/-- Lemme 2.10 : un sous-graphe couvrant avec la moitié des arêtes, où aucune arête n'est dans
une trop grande part des 4-cycles. -/
theorem clean_c4 {m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.edgeFinset.Nonempty) :
    let cyc4 := fun F : SimpleGraph (Fin m) => univ.filter fun t : Fin m × Fin m × Fin m × Fin m =>
      F.Adj t.1 t.2.1 ∧ F.Adj t.2.1 t.2.2.1 ∧ F.Adj t.2.2.1 t.2.2.2 ∧ F.Adj t.2.2.2 t.1 ∧
        t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2
    let UsesEdge := fun (t : Fin m × Fin m × Fin m × Fin m) (e : Sym2 (Fin m)) =>
      e = s(t.1, t.2.1) ∨ e = s(t.2.1, t.2.2.1) ∨ e = s(t.2.2.1, t.2.2.2) ∨ e = s(t.2.2.2, t.1)
    ∃ F : SimpleGraph (Fin m), F ≤ G ∧ (#G.edgeFinset : ℝ) / 2 ≤ #F.edgeFinset ∧
      ∀ e ∈ F.edgeFinset, (#((cyc4 F).filter fun t => UsesEdge t e) : ℝ) ≤
        16 * Real.log m / #F.edgeFinset * #(cyc4 F) := by
  intro cyc4 UsesEdge
  classical
  have clean_c4_delete (F : SimpleGraph (Fin m)) (e : Sym2 (Fin m)) :
      cyc4 (F.deleteEdges ({e} : Finset _)) = (cyc4 F).filter fun t => ¬ UsesEdge t e := by
    ext t
    simp only [cyc4, mem_filter, mem_univ, true_and, deleteEdges_adj, Finset.mem_coe,
      Finset.mem_singleton, UsesEdge]
    grind only
  let E : ℝ := #G.edgeFinset
  let L : ℝ := Real.log m
  let θ : ℝ := 16 * L / E
  have hEn : 0 < #G.edgeFinset := Finset.card_pos.mpr hG
  have hE : 0 < E := by dsimp only [E]; exact_mod_cast hEn
  have hm : 2 ≤ m := by
    have h := G.card_edgeFinset_le_card_choose_two
    rw [Fintype.card_fin] at h
    by_contra! hlt
    rw [Nat.choose_eq_zero_of_lt hlt] at h
    omega
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := by linarith
  have hL : 1 / 2 ≤ L := by
    have h₂ := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have h₃ := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hmR
    change 1 / 2 ≤ Real.log m
    linarith
  have hθ : 0 < θ := div_pos (by linarith) hE
  have hθE : θ * E = 16 * L := div_mul_cancel₀ _ hE.ne'
  let P : ℕ → Prop := fun n => ∃ F : SimpleGraph (Fin m), #F.edgeFinset = n ∧ F ≤ G ∧
    E / 2 ≤ #F.edgeFinset ∧ (#(cyc4 F) : ℝ) ≤ Real.exp (4 * L - θ * (E - #F.edgeFinset))
  have hP : ∃ n, P n := by
    refine ⟨_, G, rfl, le_rfl, ?_, ?_⟩
    · change E / 2 ≤ E
      linarith
    · change (#(cyc4 G) : ℝ) ≤ Real.exp (4 * L - θ * (E - E))
      rw [sub_self, mul_zero, sub_zero, show (4 : ℝ) = (4 : ℕ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hmpos]
      have h : #(cyc4 G) ≤ m ^ 4 := by
        simpa [Fintype.card_prod, pow_succ, mul_assoc] using (cyc4 G).card_le_univ
      exact_mod_cast h
  obtain ⟨F, hFn, hFG, hhalf, hpot⟩ := Nat.find_spec hP
  refine ⟨F, hFG, hhalf, ?_⟩
  intro e he
  have hFpos : 0 < (#F.edgeFinset : ℝ) := by linarith
  have hFE : (#F.edgeFinset : ℝ) ≤ E := by
    dsimp only [E]
    exact_mod_cast card_le_card (edgeFinset_mono hFG)
  have hcoef : θ ≤ 16 * Real.log m / #F.edgeFinset := by
    exact div_le_div_of_nonneg_left (by change 0 ≤ 16 * L; linarith) hFpos hFE
  apply le_trans _ (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _))
  by_contra! hbad
  obtain ⟨D, hDel⟩ : ∃ D : SimpleGraph (Fin m), D = F.deleteEdges ({e} : Finset _) := ⟨_, rfl⟩
  have hedges : #D.edgeFinset + 1 = #F.edgeFinset := by
    subst D
    rw [edgeFinset_deleteEdges, sdiff_singleton_eq_erase]
    exact card_erase_add_one he
  have hcycles : #((cyc4 F).filter fun t => UsesEdge t e) + #(cyc4 D) = #(cyc4 F) := by
    subst D
    rw [clean_c4_delete]
    exact card_filter_add_card_filter_not _
  have hedgesR : (#D.edgeFinset : ℝ) + 1 = #F.edgeFinset := by exact_mod_cast hedges
  have hcyclesR : (#((cyc4 F).filter fun t => UsesEdge t e) : ℝ) + #(cyc4 D) = #(cyc4 F) := by
    exact_mod_cast hcycles
  have hq : 0 < #(cyc4 F) := by
    by_contra! hn
    have hz : #(cyc4 F) = 0 := by omega
    have hu : #((cyc4 F).filter fun t => UsesEdge t e) = 0 := by omega
    simp [hz, hu] at hbad
  have hqR : (1 : ℝ) ≤ #(cyc4 F) := by exact_mod_cast hq
  have hθlt : θ < 1 := by
    by_contra! hn
    have := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg #(cyc4 F) : (0 : ℝ) ≤ _)
    linarith [Nat.cast_nonneg #(cyc4 D) (α := ℝ)]
  have hE4 : 4 ≤ E := by nlinarith [mul_lt_mul_of_pos_right hθlt hE]
  have hx := Real.one_le_exp_iff.mp (hqR.trans hpot)
  have hfrac : 0 ≤ θ * (4 * #F.edgeFinset - 3 * E) := by linarith only [hθE, hx]
  have hroom := nonneg_of_mul_nonneg_right hfrac hθ
  have hD : P #D.edgeFinset := by
    refine ⟨D, rfl, hDel ▸ (deleteEdges_le _).trans hFG, by linarith only [hroom, hE4, hedgesR], ?_⟩
    calc
      (#(cyc4 D) : ℝ) ≤ (1 - θ) * #(cyc4 F) := by linarith
      _ ≤ Real.exp (-θ) * #(cyc4 F) :=
        mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg _) (Nat.cast_nonneg _)
      _ ≤ Real.exp (-θ) * Real.exp (4 * L - θ * (E - #F.edgeFinset)) :=
        mul_le_mul_of_nonneg_left hpot (Real.exp_pos _).le
      _ = Real.exp (4 * L - θ * (E - #D.edgeFinset)) := by
        rw [← Real.exp_add, ← hedgesR]
        congr 1
        ring
  have hmin := Nat.find_min' hP hD
  omega

private theorem prune_good_classes {V : Type*} {L : ℕ} (nx : Fin L → Fin L) (T : ℝ)
    (hT : 0 ≤ T) (Q : Finset (Σ _ : Fin L, Fin L → V)) (D : Finset (Fin L → V))
    (hD : D.Nonempty) (hmass : T * #Q ≤ #D) :
    let AgreeOff := fun (i : Fin L) (x y : Fin L → V) => ∀ j, j ≠ nx i → j ≠ nx (nx i) → x j = y j
    (∀ x ∈ D, ∀ i, ∃ z, (⟨i, z⟩ ∈ Q) ∧ AgreeOff i x z) →
    ∃ E ⊆ D, E.Nonempty ∧ ∀ (i : Fin L) (y : Fin L → V),
      (E.filter fun x => AgreeOff i x y).Nonempty → T ≤ #(E.filter fun x => AgreeOff i x y) := by
  intro AgreeOff hcover
  classical
  induction Q using Finset.strongInductionOn generalizing D with
  | _ Q ih =>
    by_cases hdone : ∀ (i : Fin L) (y : Fin L → V),
      (D.filter fun x => AgreeOff i x y).Nonempty → T ≤ #(D.filter fun x => AgreeOff i x y)
    · exact ⟨D, Subset.rfl, hD, hdone⟩
    push Not at hdone
    obtain ⟨i, y, ⟨w, hw⟩, hlight⟩ := hdone
    obtain ⟨hwD, hwy⟩ := mem_filter.mp hw
    obtain ⟨z, hz, hwz⟩ := hcover w hwD i
    let q : Σ _ : Fin L, Fin L → V := ⟨i, z⟩
    let D₁ := D.filter fun x => ¬ AgreeOff i x y
    have hsplit : (#(D.filter fun x => AgreeOff i x y) : ℝ) + #D₁ = #D := by
      exact_mod_cast D.card_filter_add_card_filter_not (fun x => AgreeOff i x y)
    have hq : (#(Q.erase q) : ℝ) + 1 = #Q := by
      exact_mod_cast Finset.card_erase_add_one (show q ∈ Q from hz)
    rw [← hq] at hmass
    have hstrict : T * #(Q.erase q) < #D₁ := by nlinarith only [hsplit, hlight, hmass]
    have hpos : (0 : ℝ) < #D₁ := lt_of_le_of_lt (mul_nonneg hT (Nat.cast_nonneg _)) hstrict
    have hn : D₁.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpos)
    have hsub : D₁ ⊆ D := Finset.filter_subset _ _
    obtain ⟨E, hE, hnE, hlarge⟩ := ih (Q.erase q) (Finset.erase_ssubset hz) D₁ hn hstrict.le (by
      intro x hx j
      obtain ⟨v, hv, hxv⟩ := hcover x (hsub hx) j
      refine ⟨v, mem_erase.mpr ⟨?_, hv⟩, hxv⟩
      intro he
      change (⟨j, v⟩ : Σ _ : Fin L, Fin L → V) = ⟨i, z⟩ at he
      cases he
      apply (mem_filter.mp hx).2
      intro l h₁ h₂
      exact (hxv l h₁ h₂).trans ((hwz l h₁ h₂).symm.trans (hwy l h₁ h₂)))
    exact ⟨E, hE.trans hsub, hnE, hlarge⟩

/-- Fixer l'une des deux coordonnées libres ne laisse que l'autre variable. -/
private theorem card_fixed_good {V : Type*} {L : ℕ} (nx : Fin L → Fin L)
    (C D : Finset (Fin L → V)) (hDC : D ⊆ C) (s : ℝ) (hs : 0 ≤ s)
    (hline : ∀ y ∈ C, ∀ b, (#(C.filter fun x => ∀ j, j ≠ b → x j = y j) : ℝ) ≤ s)
    (i a b : Fin L) (y : Fin L → V) (u : V)
    (hab : ∀ j, j ≠ a → j ≠ b → j ≠ nx i ∧ j ≠ nx (nx i)) :
    let AgreeOff := fun (i : Fin L) (x y : Fin L → V) => ∀ j, j ≠ nx i → j ≠ nx (nx i) → x j = y j
    (#(D.filter fun x => AgreeOff i x y ∧ x a = u) : ℝ) ≤ s := by
  intro AgreeOff
  classical
  let F := D.filter fun x => AgreeOff i x y ∧ x a = u
  change (#F : ℝ) ≤ s
  by_cases hn : F.Nonempty
  · obtain ⟨w, hw⟩ := hn
    obtain ⟨hwD, hwy, hwa⟩ := mem_filter.mp hw
    have hsub : F ⊆ C.filter (fun x => ∀ j, j ≠ b → x j = w j) := by
      intro x hx
      obtain ⟨hxD, hxy, hxa⟩ := mem_filter.mp hx
      refine mem_filter.mpr ⟨hDC hxD, ?_⟩
      intro j hj
      by_cases hja : j = a
      · subst j; exact hxa.trans hwa.symm
      · obtain ⟨h₁, h₂⟩ := hab j hja hj
        exact (hxy j h₁ h₂).trans (hwy j h₁ h₂).symm
    exact (Nat.cast_le.mpr (card_le_card hsub)).trans (hline w (hDC hwD) b)
  · simpa [Finset.not_nonempty_iff_eq_empty.mp hn] using hs

/-- Lemme 2.12 de l'article (étape 2) : un ensemble bon non vide contient un ensemble agréable
non vide. -/
theorem good_imp_nice {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k)
    (β : ℝ) (hβ : 0 < β) (C : Finset (Fin (8 * k) → V)) (hC : C.Nonempty)
    (nxt : Fin (8 * k) → Fin (8 * k)) :
    let AgreeOff := fun (i : Fin (8 * k)) (x y : Fin (8 * k) → V) =>
      ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j
    (∃ s : ℝ, 0 < s ∧ (∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))) ∧
      (∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s) ∧
      ∀ i : Fin (8 * k), ∃ P : Finset (Fin (8 * k) → V),
        (#P : ℝ) ≤ β * #C / (16 * k * s) ∧ ∀ x ∈ C, ∃ y ∈ P, AgreeOff i x y) →
    ∃ D ⊆ C, D.Nonempty ∧ (∀ x ∈ D, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))) ∧
      ∀ (i : Fin (8 * k)) (y : Fin (8 * k) → V) (u : V),
        (#(D.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)) : ℝ) ≤
          β * #(D.filter fun x => AgreeOff i x y) := by
  intro AgreeOff h
  classical
  obtain ⟨s, hs, hcyc, hline, hrepr⟩ := h
  choose P hP hcov using hrepr
  let T := 2 * s / β
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let Q : Finset (Σ _ : Fin (8 * k), Fin (8 * k) → V) := univ.sigma P
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcard : (#Q : ℝ) ≤ (8 * (k : ℝ)) * (β * #C / (16 * k * s)) := by
    change (#(univ.sigma P) : ℝ) ≤ _
    rw [Finset.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _i : Fin (8 * k), β * #C / (16 * k * s) := Finset.sum_le_sum (fun i _ => hP i)
      _ = _ := by simp
  have hmass : T * #Q ≤ #C := calc
    _ ≤ T * ((8 * (k : ℝ)) * (β * #C / (16 * k * s))) := mul_le_mul_of_nonneg_left hcard hT
    _ = _ := by dsimp [T]; field_simp [hβ.ne', hs.ne', hk'.ne']; ring
  obtain ⟨D, hDC, hnD, hlarge⟩ := prune_good_classes nxt T hT Q C hC hmass (by
    intro x hx i
    obtain ⟨y, hy, hxy⟩ := hcov i x hx
    exact ⟨y, Finset.mem_sigma.mpr ⟨mem_univ _, hy⟩, hxy⟩)
  refine ⟨D, hDC, hnD, fun x hx => hcyc x (hDC hx), ?_⟩
  intro i y u
  let F := D.filter fun x => AgreeOff i x y ∧ (x (nxt i) = u ∨ x (nxt (nxt i)) = u)
  change (#F : ℝ) ≤ _
  by_cases hn : F.Nonempty
  · obtain ⟨w, hw⟩ := hn
    obtain ⟨hwD, hwy, _⟩ := mem_filter.mp hw
    have hthick := hlarge i y ⟨w, mem_filter.mpr ⟨hwD, hwy⟩⟩
    let A := D.filter fun x => AgreeOff i x y ∧ x (nxt i) = u
    let B := D.filter fun x => AgreeOff i x y ∧ x (nxt (nxt i)) = u
    have hA : (#A : ℝ) ≤ s := card_fixed_good nxt C D hDC s hs.le hline i _ _ y u
      (fun _ ha hb => ⟨ha, hb⟩)
    have hB : (#B : ℝ) ≤ s := card_fixed_good nxt C D hDC s hs.le hline i _ _ y u
      (fun _ ha hb => ⟨hb, ha⟩)
    have hsub : F ⊆ A ∪ B := by
      intro x hx
      obtain ⟨hxD, hxy, hx₁ | hx₂⟩ := mem_filter.mp hx
      · exact mem_union_left _ (mem_filter.mpr ⟨hxD, hxy, hx₁⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hxD, hxy, hx₂⟩)
    have hc : (#F : ℝ) ≤ #A + #B := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le A B)
    have hmul := (div_le_iff₀ hβ).mp hthick
    rw [mul_comm β]
    linarith only [hc, hA, hB, hmul]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp only [card_empty, Nat.cast_zero]
    positivity

private theorem degre_ajout_borne {m t : ℕ} (S : SimpleGraph (Fin m)) {u v : Fin m}
    (hs : ∀ x, S.degree x ≤ t) (hu : S.degree u < t) (hv : S.degree v < t) :
    ∀ x, (S ⊔ edge u v).degree x ≤ t := by
  classical
  intro x
  by_cases hx : x = u ∨ x = v
  · have hlt : S.degree x < t := hx.elim (fun e => e ▸ hu) (fun e => e ▸ hv)
    have hsub : (S ⊔ edge u v).neighborFinset x ⊆
        insert (if x = u then v else u) (S.neighborFinset x) := by
      intro y hy
      simp only [mem_neighborFinset, sup_adj, edge_adj] at hy
      simp only [mem_insert, mem_neighborFinset]
      split_ifs <;> grind
    exact (card_le_card hsub).trans ((card_insert_le _ _).trans hlt)
  · have hsub : (S ⊔ edge u v).neighborFinset x ⊆ S.neighborFinset x := by
      intro y hy
      simp only [mem_neighborFinset, sup_adj, edge_adj] at *
      tauto
    exact (card_le_card hsub).trans (hs x)

private theorem glouton_saturation {m : ℕ} (H : SimpleGraph (Fin m)) (t : ℕ) :
    ∃ S ≤ H, (∀ v, S.degree v ≤ t) ∧
      ∀ u v, H.Adj u v → ¬ S.Adj u v → t ≤ S.degree u ∨ t ≤ S.degree v := by
  classical
  let F := univ.filter (fun S : SimpleGraph (Fin m) => S ≤ H ∧ ∀ v, S.degree v ≤ t)
  have hF : F.Nonempty := by
    refine ⟨⊥, mem_filter.mpr ⟨mem_univ _, bot_le, ?_⟩⟩
    intro v
    simp [degree]
  obtain ⟨S, hS, hmax⟩ := F.exists_max_image (fun S => #S.edgeFinset) hF
  obtain ⟨hSH, hdeg⟩ := (mem_filter.mp hS).2
  refine ⟨S, hSH, hdeg, ?_⟩
  have hsat {u v} (hadj : H.Adj u v) (hmiss : ¬ S.Adj u v) : t ≤ S.degree u ∨ t ≤ S.degree v := by
    by_contra! hsmall
    have hnew : S ⊔ edge u v ∈ F := by
      refine mem_filter.mpr ⟨mem_univ _, sup_le hSH ((edge_le_iff H).mpr (.inr hadj)), ?_⟩
      intro x
      convert! degre_ajout_borne S hdeg hsmall.1 hsmall.2 x using 1
      exact congrArg (fun I => @SimpleGraph.degree _ (S ⊔ edge u v) x I) (Subsingleton.elim _ _)
    have hbad := hmax _ hnew
    have hmono {B C : SimpleGraph (Fin m)} (hlt : B < C) : #B.edgeFinset < #C.edgeFinset :=
      card_lt_card (edgeFinset_strict_mono hlt)
    exact (not_lt_of_ge hbad) (hmono (S.lt_sup_edge _ _ hadj.ne hmiss))
  exact fun _ _ => hsat

/-- Les arêtes manquées rencontrent toutes le petit ensemble saturé. On le réunit à
chaque classe modulo `p` et l'on retient la classe qui contient le plus d'arêtes. -/
private theorem concentrer {n p : ℕ} (hp : 0 < p) (hpn : p ≤ n)
    (G S : SimpleGraph (Fin n)) (hSG : S ≤ G) (A : Finset (Fin n))
    (hA : #A * p ≤ n) (hpetit : 2 * #S.edgeFinset ≤ #G.edgeFinset)
    (hcouv : ∀ u v, G.Adj u v → ¬ S.Adj u v → u ∈ A ∨ v ∈ A) :
    ∃ k, ∃ H : SimpleGraph (Fin k), H ⊑ G ∧ k * p ≤ 3 * n ∧
      #G.edgeFinset ≤ 2 * p * #H.edgeFinset := by
  classical
  let c (v : Fin n) := v.val % p
  let C (j : ℕ) := univ.filter fun v : Fin n => c v = j
  let U (j : ℕ) := A ∪ C j
  let E (j : ℕ) := G.edgeFinset.filter fun e => e.toFinset ⊆ U j
  have hc (v : Fin n) : v ∈ C (c v) := mem_filter.mpr ⟨mem_univ _, rfl⟩
  have hcover : G.edgeFinset \ S.edgeFinset ⊆ (range p).biUnion E := by
    intro e
    induction e using Sym2.inductionOn with | hf u v =>
      intro he
      obtain ⟨h₁, h₂⟩ := mem_sdiff.mp he
      rcases hcouv u v (mem_edgeFinset.mp h₁) (fun h => h₂ (mem_edgeFinset.mpr h)) with hu | hv
      · refine mem_biUnion.mpr ⟨c v, mem_range.mpr (Nat.mod_lt _ hp),
            mem_filter.mpr ⟨h₁, ?_⟩⟩
        rw [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff]
        exact ⟨mem_union_left _ hu, mem_union_right _ (hc v)⟩
      · refine mem_biUnion.mpr ⟨c u, mem_range.mpr (Nat.mod_lt _ hp),
            mem_filter.mpr ⟨h₁, ?_⟩⟩
        rw [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff]
        exact ⟨mem_union_right _ (hc u), mem_union_left _ hv⟩
  obtain ⟨j, hj, hbest⟩ := (range p).exists_max_image (fun j => #(E j))
    ⟨0, mem_range.mpr hp⟩
  have hcount : #(G.edgeFinset \ S.edgeFinset) ≤ p * #(E j) := calc
    _ ≤ #((range p).biUnion E) := card_le_card hcover
    _ ≤ ∑ i ∈ range p, #(E i) := card_biUnion_le
    _ ≤ ∑ _i ∈ range p, #(E j) := sum_le_sum hbest
    _ = _ := by simp
  have hf : #(C j) ≤ n / p + 1 := by
    rw [← card_range (n / p + 1)]
    apply card_le_card_of_injOn (fun v : Fin n => v.val / p)
    · intro v _
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right v.isLt.le))
    · intro v hv w hw heq
      have hv' := (mem_filter.mp hv).2
      have hw' := (mem_filter.mp hw).2
      change v.val % p = j at hv'
      change w.val % p = j at hw'
      change v.val / p = w.val / p at heq
      exact Fin.ext (calc
        _ = v.val % p + p * (v.val / p) := (Nat.mod_add_div ..).symm
        _ = w.val % p + p * (w.val / p) := by rw [hv', hw', heq]
        _ = _ := Nat.mod_add_div ..)
  let H := G.induce (U j : Set (Fin n))
  have hcard : Fintype.card (U j : Set (Fin n)) = #(U j) := Fintype.card_coe _
  refine ⟨#(U j), H.overFin hcard, ?_, ?_, ?_⟩
  · exact (show H.overFin hcard ⊑ H from ⟨(H.overFinIso hcard).symm.toCopy⟩).trans
      ⟨Copy.induce G _⟩
  · calc
      #(U j) * p ≤ (#A + #(C j)) * p := Nat.mul_le_mul_right _ (card_union_le ..)
      _ ≤ (#A + (n / p + 1)) * p := by gcongr
      _ ≤ 3 * n := by nlinarith only [hA, Nat.div_mul_le_self n p, hpn]
  · have hpart := card_sdiff_add_card_eq_card (edgeFinset_mono hSG)
    have hEq : #(E j) = #(H.overFin hcard).edgeFinset :=
      (G.card_filter_edgeFinset_toFinset_subset (U j)).trans (H.overFinIso hcard).card_edgeFinset_eq
    rw [← hEq]
    linarith only [hpart, hpetit, hcount]

private theorem aretes_le_carre {n : ℕ} (G : SimpleGraph (Fin n)) :
    #G.edgeFinset ≤ n * n := by
  classical
  have h : 2 * #G.edgeFinset ≤ n * n := calc
    _ = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
    _ ≤ ∑ _v : Fin n, n := sum_le_sum fun v _ => by simpa using (G.degree_lt_card_verts v).le
    _ = _ := by simp
  omega

/-- Le quotient du nombre d'arêtes par `n^(1+δ)` ne décroît pas lors d'une
concentration. La constante `D`, fixée une fois pour toutes, minore ce quotient. -/
private theorem regulariser {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D) {q : ℕ}
    (hq : 2 ≤ q) (hgain : 8 ≤ (q : ℝ) ^ δ) (n : ℕ) (hn : 0 < n)
    (hdom : (n : ℝ) ^ δ ≤ D) (G : SimpleGraph (Fin n))
    (hE : D * (n : ℝ) ^ (1 + δ) ≤ #G.edgeFinset) :
    ∃ m, ∃ S : SimpleGraph (Fin m), D ≤ m ∧ S ⊑ G ∧
      (m : ℝ) ^ (1 + (δ + δ)) / 3 ≤ #S.edgeFinset ∧
      ∀ v, (S.degree v : ℝ) ≤ ((4*q : ℕ) + 1 : ℝ) * (m : ℝ) ^ (δ + δ) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    let p := 4*q
    have hp : 0 < p := by dsimp [p]; omega
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    let X := (n : ℝ) ^ (δ + δ)
    have hX : 1 ≤ X := Real.one_le_rpow hn1 (by linarith)
    have hX' : 0 < X := by linarith
    have hid : (n : ℝ) ^ (1 + (δ + δ)) = n * X := by
      rw [Real.rpow_add hn', Real.rpow_one]
    have hprod : (n : ℝ) ^ δ * (n : ℝ) ^ (1 + δ) = n * X := by
      rw [← Real.rpow_add hn', ← hid]
      congr 1
      ring
    have hden : (n : ℝ) * X ≤ #G.edgeFinset := by
      rw [← hprod]
      exact (mul_le_mul_of_nonneg_right hdom (by positivity)).trans hE
    have hsize : D ≤ n := by
      have hpow : (n : ℝ) ≤ (n : ℝ) ^ (1 + δ) := by
        rw [Real.rpow_add hn', Real.rpow_one]
        exact le_mul_of_one_le_right hn'.le (Real.one_le_rpow hn1 hδ.le)
      have htop : (#G.edgeFinset : ℝ) ≤ n * n := by exact_mod_cast aretes_le_carre G
      exact le_of_mul_le_mul_right ((mul_le_mul_of_nonneg_left hpow hD.le).trans (hE.trans htop)) hn'
    by_cases hpn : p ≤ n
    · let t := ⌈(p : ℝ) * X⌉₊
      have ht : (p : ℝ) * X ≤ t := Nat.le_ceil _
      obtain ⟨S, hSG, hdeg, hsat⟩ := glouton_saturation G t
      by_cases hdense : (n : ℝ) * X / 3 ≤ #S.edgeFinset
      · refine ⟨n, S, hsize, IsContained.of_le hSG, hid ▸ hdense, ?_⟩
        intro v
        have hd : (S.degree v : ℝ) ≤ t := by exact_mod_cast hdeg v
        have ht' : (t : ℝ) < (p : ℝ) * X + 1 := Nat.ceil_lt_add_one (by positivity)
        change (S.degree v : ℝ) ≤ ((p : ℝ) + 1) * X
        linarith only [hd, ht', hX]
      · let A := univ.filter fun v => t ≤ S.degree v
        have hsum : #A * t ≤ 2 * #S.edgeFinset := by
          rw [← S.sum_degrees_eq_twice_card_edges]
          calc
            _ = ∑ _v ∈ A, t := by simp
            _ ≤ ∑ v ∈ A, S.degree v := sum_le_sum fun v hv => (mem_filter.mp hv).2
            _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
        have hcount : #A * p ≤ n := by
          have hl : (#A : ℝ) * ((p : ℝ) * X) ≤ #A * (t : ℝ) :=
            mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
          have hs : (#A : ℝ) * t ≤ 2 * #S.edgeFinset := by exact_mod_cast hsum
          have : ((#A : ℝ) * p) * X ≤ n * X := by
            linarith only [hl, hs, not_le.mp hdense, Nat.cast_nonneg (α := ℝ) S.edgeFinset.card]
          exact_mod_cast le_of_mul_le_mul_right this hX'
        have hsmall : 2 * #S.edgeFinset ≤ #G.edgeFinset := by
          have : 2 * (#S.edgeFinset : ℝ) ≤ #G.edgeFinset := by
            linarith only [not_le.mp hdense, hden, Nat.cast_nonneg (α := ℝ) S.edgeFinset.card]
          exact_mod_cast this
        obtain ⟨k, H, hHG, hk, he⟩ := concentrer hp hpn G S hSG A hcount hsmall (by
          intro u v huv hnot
          simpa [A] using hsat u v huv hnot)
        have hkq : k * q ≤ n := by dsimp [p] at hk; nlinarith only [hk]
        have hkn : k < n := by nlinarith only [hkq, Nat.mul_le_mul_left k hq, hn]
        have hkpos : 0 < k := by
          by_contra! h
          have hkz : k = 0 := by omega
          have he0 : #H.edgeFinset = 0 := Nat.eq_zero_of_le_zero ((aretes_le_carre H).trans (by simp [hkz]))
          have hg0 : #G.edgeFinset = 0 := by simpa [he0] using he
          rw [hg0, Nat.cast_zero] at hE
          exact (not_lt_of_ge hE) (mul_pos hD (Real.rpow_pos_of_pos hn' _))
        have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
        have hg : (2 : ℝ) * p ≤ (q : ℝ) ^ (1 + δ) := by
          rw [Real.rpow_add hqpos, Real.rpow_one]
          dsimp [p]
          push_cast
          nlinarith only [mul_le_mul_of_nonneg_left hgain hqpos.le]
        have hstep : (k : ℝ) ^ (1 + δ) * (2 * (p : ℝ)) ≤ (n : ℝ) ^ (1 + δ) := calc
          _ ≤ (k : ℝ) ^ (1 + δ) * (q : ℝ) ^ (1 + δ) :=
            mul_le_mul_of_nonneg_left hg (by positivity)
          _ = ((k : ℝ) * q) ^ (1 + δ) := (Real.mul_rpow (by positivity) hqpos.le).symm
          _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkq) (by linarith)
        have hE' : D * (k : ℝ) ^ (1 + δ) ≤ #H.edgeFinset := by
          have he' : (#G.edgeFinset : ℝ) ≤ 2 * p * (#H.edgeFinset : ℝ) := by exact_mod_cast he
          refine le_of_mul_le_mul_right (a := 2 * (p : ℝ)) ?_ (by positivity)
          linarith only [mul_le_mul_of_nonneg_left hstep hD.le, hE, he']
        obtain ⟨m, F, hm, hFH, hf, hd⟩ := ih k hkn hkpos
          ((Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkn.le) hδ.le).trans hdom) H hE'
        exact ⟨m, F, hm, hFH.trans hHG, hf, hd⟩
    · refine ⟨n, G, hsize, IsContained.of_le le_rfl, ?_, ?_⟩
      · rw [hid]
        linarith only [hden, Nat.cast_nonneg (α := ℝ) G.edgeFinset.card]
      · intro v
        have hd : G.degree v ≤ p := (by simpa using (G.degree_lt_card_verts v).le : G.degree v ≤ n).trans (by omega)
        change (G.degree v : ℝ) ≤ ((p : ℝ) + 1) * X
        exact (by exact_mod_cast hd : (G.degree v : ℝ) ≤ p).trans
          ((by linarith : (p : ℝ) ≤ p + 1).trans (le_mul_of_one_le_right (by positivity) hX))

/-- Lemme 2.9 affaibli (exposant `γ > 0` existentiel), prouvé directement : tout graphe à `n`
sommets et au moins `n^{1+α}` arêtes contient un sous-graphe à `m ≥ n^γ` sommets, au moins
`m^{1+α}/3` arêtes et de degré maximal au plus `K m^α`. -/
theorem regularizationW :
    ∀ α : ℝ, 0 < α → α < 1 → ∃ K : ℝ, 0 < K ∧ ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), (n : ℝ) ^ (1 + α) ≤ #G.edgeFinset →
      ∃ m : ℕ, ∃ G' : SimpleGraph (Fin m), (n : ℝ) ^ γ ≤ m ∧ G' ⊑ G ∧
        (m : ℝ) ^ (1 + α) / 3 ≤ #G'.edgeFinset ∧ ∀ v, (G'.degree v : ℝ) ≤ K * (m : ℝ) ^ α := by
  classical
  intro α hα _
  let δ := α / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hα' : α = δ + δ := by dsimp [δ]; ring
  obtain ⟨r, hr⟩ := exists_nat_ge ((8 : ℝ) ^ δ⁻¹)
  let q := r + 2
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hgain : 8 ≤ (q : ℝ) ^ δ := by
    calc
      _ = ((8 : ℝ) ^ δ⁻¹) ^ δ := (Real.rpow_inv_rpow (by norm_num) hδ.ne').symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (hr.trans (by exact_mod_cast (by dsimp [q]; omega : r ≤ q))) hδ.le
  refine ⟨((4*q : ℕ) + 1 : ℝ), by positivity, δ, hδ, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro G hG
  rw [hα'] at hG ⊢
  apply regulariser hδ (Real.rpow_pos_of_pos (by exact_mod_cast hn) δ) hq hgain n hn le_rfl G
  rw [← Real.rpow_add (by exact_mod_cast hn : (0 : ℝ) < n)]
  convert hG using 2
  ring

/-- L'étape 1 découle des lemmes 2.14 et 2.15, selon que le nombre de 4-cycles est petit ou
grand. -/
theorem step1_of_few_many (h14 : H1) (h15 : H2) :
    ∀ ε K : ℝ, 0 < ε → ε < 1 / 6 → 0 < K → ∀ k : ℕ, 1 / ε ≤ k → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        let c4 : Finset (Fin n × Fin n × Fin n × Fin n) := univ.filter fun t =>
          G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
            t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2
        let nxt : Fin (8 * k) → Fin (8 * k) := fun i => ⟨(i.val + 1) % (8 * k), Nat.mod_lt _ i.pos⟩
        (n : ℝ) ^ (4 / 3 + ε) / 6 ≤ #G.edgeFinset →
        (∀ v, (G.degree v : ℝ) ≤ K * (n : ℝ) ^ (1 / 3 + ε)) →
        (∀ e ∈ G.edgeFinset, (#(c4.filter fun t => e = s(t.1, t.2.1) ∨ e = s(t.2.1, t.2.2.1) ∨
            e = s(t.2.2.1, t.2.2.2) ∨ e = s(t.2.2.2, t.1)) : ℝ) ≤
            96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * #c4) →
        ∃ C : Finset (Fin (8 * k) → Fin n), C.Nonempty ∧ ∃ s : ℝ, 0 < s ∧
          (∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (nxt i))) ∧
          (∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s) ∧
          ∀ i : Fin (8 * k), ∃ P : Finset (Fin (8 * k) → Fin n),
            (#P : ℝ) ≤ (n : ℝ) ^ (-(ε / 2)) * #C / (16 * k * s) ∧
            ∀ x ∈ C, ∃ y ∈ P, ∀ j, j ≠ nxt i → j ≠ nxt (nxt i) → x j = y j := by
  intro ε K hε hε6 hK k hk
  filter_upwards [h14 ε K hε hε6 hK k hk, h15 ε K hε hε6 hK k hk, eventually_ge_atTop 2]
    with n h14n h15n hn2
  intro G c4 nxt hE hdeg hu
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hP : (0 : ℝ) < (n : ℝ) ^ (4 / 3 + ε) := Real.rpow_pos_of_pos (by linarith) _
  by_cases hq : 8 * (n : ℝ) ^ (5 / 3 + 3 * ε) / (96 * Real.log n) ≤ #c4
  · exact h15n G hdeg hq hu
  · push Not at hq
    apply h14n G hE hdeg
    intro e he
    refine (hu e he).trans ?_
    have hsplit : (n : ℝ) ^ (5 / 3 + 3 * ε) =
        (n : ℝ) ^ (4 / 3 + ε) * (n : ℝ) ^ (1 / 3 + 2 * ε) := by
      rw [← Real.rpow_add (by linarith)]
      congr 1
      ring
    calc 96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * #c4
        ≤ 96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) *
            (8 * (n : ℝ) ^ (5 / 3 + 3 * ε) / (96 * Real.log n)) := by
          apply mul_le_mul_of_nonneg_left hq.le
          positivity
      _ = 8 * (n : ℝ) ^ (1 / 3 + 2 * ε) := by
          rw [hsplit]
          field_simp

/- La cardinalité d'un filtre ne dépend pas de l'instance de décision du prédicat. -/
private theorem filtre_borne {V : Type*} {P : V → Prop} {d e : DecidablePred P}
    {S : Finset V} {t : ℝ} (h : (#(@Finset.filter _ P d S) : ℝ) ≤ t) :
    (#(@Finset.filter _ P e S) : ℝ) ≤ t := Subsingleton.elim d e ▸ h

private theorem filtres_proportion {V : Type*} {P Q : V → Prop} {d e : DecidablePred P}
    {f g : DecidablePred Q} {S : Finset V} {β : ℝ}
    (h : (#(@Finset.filter _ P d S) : ℝ) ≤ β * #(@Finset.filter _ Q f S)) :
    (#(@Finset.filter _ P e S) : ℝ) ≤ β * #(@Finset.filter _ Q g S) := by
  cases Subsingleton.elim d e
  cases Subsingleton.elim f g
  exact h

/-- Théorème 1.3 : pour `0 < ε < 1/6`, `k ≥ 1/ε`, `ℓ ≥ 16k/ε`, tout graphe à `n` sommets
(`n` grand) et au moins `n^{4/3+ε}` arêtes contient `H_{k,ℓ}`. -/
theorem thm13 (h1 : H1) (h2 : H2) (h3 : H3) (ε : ℝ) (hε : 0 < ε)
    (hε6 : ε < 1 / 6) (k ℓ : ℕ) (hk : 1 / ε ≤ k) (hl : 16 * k / ε ≤ ℓ) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ (4 / 3 + ε) ≤ #G.edgeFinset →
      SimpleGraph.fromRel (fun a b : Fin (4 * k) × Fin (2 * ℓ) =>
        (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)) ⊑ G := by
  -- paramètres
  set α : ℝ := 1 / 3 + ε with hαdef
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := by linarith
  have hk1r : (1 : ℝ) ≤ k := by
    have : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
    linarith
  have hk1 : 1 ≤ k := by exact_mod_cast hk1r
  have hl2 : 2 ≤ ℓ := by
    have h16 : (2 : ℝ) ≤ 16 * k / ε := by rw [le_div_iff₀ hε]; nlinarith
    exact_mod_cast h16.trans hl
  obtain ⟨K, hK, γ, hγ, hRegN⟩ := regularizationW α hα0 hα1
  have hS1' := step1_of_few_many h1 h2 ε K hε hε6 hK k hk
  have hS3' := E147Step3.step3_of_H3 h3 (ε / 2) (by positivity) k ℓ hk1 hl2 (by
    have : 8 * (k : ℝ) / (ε / 2) = 16 * k / ε := by field_simp; ring
    rw [this]; exact hl)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hS1'.and (hS3'.and (eventually_ge_atTop 1)))
  have hγev : ∀ᶠ n : ℕ in atTop, (M : ℝ) ≤ (n : ℝ) ^ γ :=
    ((tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (M : ℝ)
  filter_upwards [hRegN, hγev] with n hn hnM
  intro G hG
  have hexp : (1 + α : ℝ) = 4 / 3 + ε := by rw [hαdef]; ring
  obtain ⟨m, G', hm, hG'G, hG'e, hG'deg⟩ := hn G (by rw [hexp]; exact hG)
  have hmM : M ≤ m := by exact_mod_cast hnM.trans hm
  obtain ⟨hS1m, hS3m, hm1⟩ := hM m hmM
  have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm0r : (0 : ℝ) < m := by linarith
  have hpow0 : (0 : ℝ) < (m : ℝ) ^ (4 / 3 + ε) := Real.rpow_pos_of_pos hm0r _
  have hG'e' : (m : ℝ) ^ (4 / 3 + ε) / 3 ≤ #G'.edgeFinset := by rw [← hexp]; exact hG'e
  have hne : G'.edgeFinset.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < #G'.edgeFinset := lt_of_lt_of_le (by positivity) hG'e'
    exact_mod_cast this
  obtain ⟨F, hFG', hFe, hFc4⟩ := clean_c4 G' hne
  have hFe' : (m : ℝ) ^ (4 / 3 + ε) / 6 ≤ #F.edgeFinset := by linarith
  have hFpos : (0 : ℝ) < #F.edgeFinset := lt_of_lt_of_le (by positivity) hFe'
  have hdeg : ∀ v, (F.degree v : ℝ) ≤ K * (m : ℝ) ^ (1 / 3 + ε) := by
    intro v
    have h1 : F.degree v ≤ G'.degree v := by
      apply Finset.card_le_card
      intro w hw
      simp only [mem_neighborFinset] at hw ⊢
      exact hFG' hw
    calc (F.degree v : ℝ) ≤ G'.degree v := by exact_mod_cast h1
      _ ≤ K * (m : ℝ) ^ α := hG'deg v
  obtain ⟨C, hCne, hCgood⟩ := hS1m F hFe' hdeg (by
    intro e he
    refine (hFc4 e he).trans ?_
    have hlog : 0 ≤ Real.log m := Real.log_nonneg hm1r
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [div_le_div_iff₀ hFpos hpow0]
    nlinarith)
  obtain ⟨D, -, hDne, hDnice⟩ :=
    good_imp_nice F k hk1 ((m : ℝ) ^ (-(ε / 2))) (Real.rpow_pos_of_pos hm0r _) C hCne
      (fun i => ⟨(i.val + 1) % (8 * k), Nat.mod_lt _ i.pos⟩) (by
        obtain ⟨s, hs, hcyc, hfix, hrepr⟩ := hCgood
        exact ⟨s, hs, hcyc, fun y hy i => filtre_borne (hfix y hy i), hrepr⟩)
  have hcopy := hS3m F D hDne ⟨hDnice.1, fun i y u => filtres_proportion (hDnice.2 i y u)⟩
  exact (hcopy.trans (IsContained.of_le hFG')).trans hG'G

/-- Passage de `Fin (4k) × Fin (2ℓ)` à `Fin q`. -/
theorem transfer (h1 : H1) (h2 : H2) (h3 : H3) (ε : ℝ) (hε : 0 < ε) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsBipartite ∧ H.IsRegularOfDegree 3 ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (4 / 3 + ε : ℝ) := by
  set ε₀ : ℝ := min ε (1 / 12) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min hε (by norm_num)
  have hε₀12 : ε₀ ≤ 1 / 12 := min_le_right _ _
  have hε₀6 : ε₀ < 1 / 6 := lt_of_le_of_lt hε₀12 (by norm_num)
  have hε₀le : ε₀ ≤ ε := min_le_left _ _
  set k : ℕ := ⌈1 / ε₀⌉₊ with hkdef
  set ℓ : ℕ := ⌈16 * k / ε₀⌉₊ with hldef
  have hk : 1 / ε₀ ≤ k := Nat.le_ceil _
  have hl : 16 * k / ε₀ ≤ ℓ := Nat.le_ceil _
  let e := finProdFinEquiv (m := 4 * k) (n := 2 * ℓ)
  have hk1 : (1 : ℝ) ≤ k := by
    have : (1 : ℝ) ≤ 1 / ε₀ := by rw [le_div_iff₀ hε₀pos]; linarith
    linarith
  have hl0 : 0 < ℓ := by
    have : (0 : ℝ) < 16 * k / ε₀ := by positivity
    exact_mod_cast this.trans_le hl
  have hk0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  let Hk : SimpleGraph (Fin (4 * k) × Fin (2 * ℓ)) := SimpleGraph.fromRel fun a b =>
        (a.1.val + 1 = b.1.val ∧
          (if a.1.val % 2 = 0 then a.2 = b.2
           else (a.2.val + 1) % (2 * ℓ) = b.2.val ∨ (b.2.val + 1) % (2 * ℓ) = a.2.val)) ∨
        (a.1 = b.1 ∧ (a.1.val = 0 ∨ a.1.val + 1 = 4 * k) ∧ (a.2.val + 1) % (2 * ℓ) = b.2.val)
  refine ⟨4 * k * (2 * ℓ), Hk.map e.toEmbedding, by positivity, ?_, ?_, ?_⟩
  · exact Colorable.of_hom (SimpleGraph.Iso.map e Hk).symm.toHom (hkl_bipartite k ℓ)
  · intro v
    have hd1 := (SimpleGraph.Iso.map e Hk).degree_eq (e.symm v)
    have hd2 := hkl_regular k ℓ (by exact_mod_cast hk1) (by
      have : (2 : ℝ) ≤ ℓ := by
        have h16 : (2 : ℝ) ≤ 16 * k / ε₀ := by
          rw [le_div_iff₀ hε₀pos]; nlinarith
        linarith
      exact_mod_cast this) (e.symm v)
    have hd3 : (SimpleGraph.Iso.map e Hk) (e.symm v) = v := by
      simp [SimpleGraph.Iso.map]
    rw [hd3] at hd1
    convert hd1.trans hd2 using 2
    rfl
  · have hcongr : ∀ n, extremalNumber n (Hk.map e.toEmbedding) =
        extremalNumber n Hk := fun n =>
      extremalNumber_congr_right (SimpleGraph.Iso.map e Hk).symm
    simp_rw [hcongr]
    exact bigO_of_eventually_contains Hk (4 / 3 + ε₀) (4 / 3 + ε) (by linarith)
      (thm13 h1 h2 h3 ε₀ hε₀pos hε₀6 k ℓ hk hl)

end E147
end R1Sec

section H1Sec
open SimpleGraph Finset Filter Asymptotics Matrix
open scoped Classical

namespace E147H1

/-- Poids d'un uplet cyclique `x : Fin L → W` : produit des `M (x i) (x (i+1 mod L))`. -/
noncomputable def cycW {W : Type} [Fintype W] (M : Matrix W W ℝ) {L : ℕ} (x : Fin L → W) : ℝ :=
  ∏ i : Fin L, M (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩)

/-- Matrice d'adjacence réelle de `G`. -/
noncomputable def adjR {W : Type} [Fintype W] (G : SimpleGraph W) : Matrix W W ℝ :=
  fun u v => if G.Adj u v then 1 else 0

/- ## Déjà prouvés pour `H3` (lemmes 9, 10, 11) -/

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

/-- Masse totale des uplets cycliques de longueur `2k`. -/
theorem total_cycW_eq_trace {W : Type} [Fintype W] (M : Matrix W W ℝ)
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

/- ## Lemme 12 : cycles homomorphes en conflit, version adjacence -/

private theorem trip12 {W : Type} [Fintype W] (M : Matrix W W ℝ) (k : ℕ) (hk : 2 ≤ k)
    (F : W → W → W → ℝ) :
    ∑ x : Fin (2*k) → W, cycW M x * F (x ⟨0,by omega⟩) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) =
    ∑ a, ∑ b, ∑ c, M a b * (M^k) b c * (M^(k-1)) c a * F a b c := by
  classical
  rw [cyc_split M k 1 hk (by omega) (by omega) (fun a b _ c => F a b c)]
  simp [Matrix.one_apply, mul_ite, ite_mul, sum_ite_irrel]

private theorem nn12 {W : Type} [Fintype W] (G : SimpleGraph W) (a b : W) :
    0 ≤ adjR G a b := by unfold adjR; split <;> positivity

private theorem symm12 {W : Type} [Fintype W] (G : SimpleGraph W) (n : ℕ) (u v : W) :
    (adjR G ^ n) u v = (adjR G ^ n) v u := by
  have h : (adjR G).IsSymm := by
    ext a b
    change (if G.Adj b a then (1:ℝ) else 0) = _
    simp only [adjR, G.adj_comm b a]
  exact (h.pow n).apply v u

private theorem row12 {W : Type} [Fintype W] (G : SimpleGraph W) (a : W) :
    ∑ b, adjR G a b = (G.degree a : ℝ) := by
  simp only [adjR, sum_boole, ← G.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]

private theorem trace12 {W : Type} [Fintype W] (M : Matrix W W ℝ) (p q : ℕ) :
    trace (M ^ (p+q)) = ∑ a, ∑ b, (M^p) a b * (M^q) b a := by
  simp only [pow_add, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private theorem ratio12 {U V : ℝ} (hU : 0 ≤ U) (_hV : 0 ≤ V) : V * (U / V) ≤ U := by
  by_cases h : V = 0
  · simp [h, hU]
  · exact le_of_eq (by field_simp)

private theorem upperFirst12 {W : Type} [Fintype W] (G : SimpleGraph W)
    (Δ : ℝ) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2*k) → W, cycW (adjR G) x *
      (((adjR G)^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) /
       ((adjR G)^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩)) ≤
    Δ * trace (adjR G ^ (2*(k-1))) := by
  classical
  let M := adjR G
  let P := fun n : ℕ => M^n
  have hn := Matrix.pow_apply_nonneg (nn12 G)
  rw [trip12 (adjR G) k hk (fun a b c => (P (k-1)) a c / (P k) b c),
    two_mul, trace12, mul_sum]
  apply sum_le_sum
  intro a _
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro c _
  calc
    _ ≤ ∑ b, M a b * ((P (k-1)) a c * (P (k-1)) c a) := by
      apply sum_le_sum
      intro b _
      have hh := mul_le_mul_of_nonneg_left (ratio12 (hn (k-1) a c) (hn k b c))
        (mul_nonneg (nn12 G a b) (hn (k-1) c a))
      dsimp [M, P] at *
      linarith only [hh]
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right ((row12 G a).le.trans (hdeg a))
        (mul_nonneg (hn _ _ _) (hn _ _ _))

private theorem mass12 {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (n : ℕ) (b e c : W) :
    ∑ a, (if r a e then adjR G a b * (adjR G^n) c a / (adjR G^n) a c else 0) ≤
      (#((G.neighborFinset b).filter (r e)) : ℝ) := by
  classical
  calc
    _ ≤ ∑ a, if G.Adj b a ∧ r e a then (1:ℝ) else 0 := by
      apply sum_le_sum
      intro a _
      rw [symm12 G n c a]
      by_cases h : r a e
      · by_cases hab : G.Adj a b
        · rw [if_pos h, if_pos ⟨hab.symm, hr a e h⟩]
          simp only [adjR, if_pos hab, one_mul]
          exact div_self_le_one _
        · have hba : ¬ G.Adj b a := fun h' => hab h'.symm
          simp [h,adjR,hab,hba]
      · simp only [if_neg h]
        split <;> norm_num
    _ = _ := by
      rw [sum_boole]
      have he : univ.filter (fun a => G.Adj b a ∧ r e a) = (G.neighborFinset b).filter (r e) := by
        ext a
        simp
      rw [he]

private theorem upperOne12 {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (s : ℝ)
    (k j : ℕ) (hk : 2 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k)
    (hrel : ∀ b e, (adjR G ^ (j-1)) b e ≠ 0 →
      (#((G.neighborFinset b).filter (r e)) : ℝ) ≤ s) :
    ∑ x : Fin (2*k) → W, cycW (adjR G) x *
      (if r (x ⟨0,by omega⟩) (x ⟨j,by omega⟩) then
       ((adjR G)^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) /
       ((adjR G)^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) else 0) ≤
    s * trace (adjR G ^ (2*k)) := by
  classical
  let M := adjR G
  let P := fun n : ℕ => M^n
  have hn := Matrix.pow_apply_nonneg (nn12 G)
  rw [cyc_split (adjR G) k j hk hj hjk
    (fun a b e c => if r a e then (P k) b c / (P (k-1)) a c else 0),
    two_mul, trace12, mul_sum]
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
  calc
    _ ≤ ∑ e, s * ((P (j-1)) b e * (P (k+1-j)) e c * (P k) b c) := by
      apply sum_le_sum
      intro e _
      by_cases hz : (P (j-1)) b e = 0
      · simp [f, hz]
      have hh := (mass12 G r hr (k-1) b e c).trans (hrel b e hz)
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hh
        (mul_nonneg (mul_nonneg (hn _ _ _) (hn _ _ _)) (hn _ _ _)))
      rw [sum_mul]
      apply sum_congr rfl
      intro a _
      dsimp [f, P, M]
      by_cases hr' : r a e <;> simp [hr']
      ring
    _ = s * ((P k) b c * (P k) b c) := by
      rw [← mul_sum, ← sum_mul]
      have hp : (∑ e, (P (j-1)) b e * (P (k+1-j)) e c) = (P k) b c := by
        change ((M^(j-1)) * (M^(k+1-j))) b c = _
        rw [← pow_add, show j-1 + (k+1-j) = k by omega]
      rw [hp]
    _ = _ := by
      exact congrArg (fun z => s * ((P k) b c * z)) (symm12 G k b c)

private theorem cwNonneg12 {W : Type} [Fintype W] (G : SimpleGraph W) {N : ℕ}
    (x : Fin N → W) : 0 ≤ cycW (adjR G) x :=
  prod_nonneg (fun _ _ => nn12 G _ _)

private theorem support12 {W : Type} [Fintype W] (G : SimpleGraph W)
    (k : ℕ) (hk : 2 ≤ k) (x : Fin (2*k) → W) (hx : cycW (adjR G) x ≠ 0) :
    (adjR G^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) ≠ 0 ∧
    (adjR G^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) ≠ 0 := by
  classical
  let M := adjR G
  let P := fun n : ℕ => M^n
  let bad := fun a b c : W => if (P (k-1)) a c = 0 ∨ (P k) b c = 0 then (1:ℝ) else 0
  let term := fun y : Fin (2*k) → W => cycW M y * bad (y ⟨0,by omega⟩) (y ⟨1,by omega⟩)
    (y ⟨k+1,by omega⟩)
  have hzero : ∑ y, term y = 0 := by
    dsimp only [term]
    rw [trip12 M k hk bad]
    apply sum_eq_zero
    intro a _
    apply sum_eq_zero
    intro b _
    apply sum_eq_zero
    intro c _
    by_cases ha : (P (k-1)) a c = 0
    · have hc : (P (k-1)) c a = 0 := (symm12 G (k-1) c a).trans ha
      change _ * (P (k-1)) c a * _ = 0
      simp [hc]
    · by_cases hb : (P k) b c = 0
      · change _ * (P k) b c * _ * _ = 0
        simp [hb]
      · simp [bad, ha, hb]
  have hn (y) (_ : y ∈ univ) : 0 ≤ term y := by
    dsimp only [term,bad]
    exact mul_nonneg (cwNonneg12 G y) (by split <;> norm_num)
  have hh := (sum_eq_zero_iff_of_nonneg hn).mp hzero x (mem_univ x)
  dsimp only [term,bad] at hh
  by_contra! h
  have h' : (P (k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) = 0 ∨
      (P k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) = 0 := by tauto
  rw [if_pos h', mul_one] at hh
  exact hx hh

private theorem cs12 {W : Type} [Fintype W] (G : SimpleGraph W)
    (Δ : ℝ) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (k : ℕ) (hk : 2 ≤ k)
    (hit : (Fin (2*k) → W) → Prop) (C : ℝ)
    (hsecond : ∑ x : Fin (2*k) → W, (if hit x then cycW (adjR G) x else 0) *
      ((adjR G^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) /
       (adjR G^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩)) ≤ C) :
    (∑ x, if hit x then cycW (adjR G) x else 0) ≤
      Real.sqrt ((Δ * trace (adjR G ^ (2*(k-1)))) * C) := by
  classical
  let X := Fin (2*k) → W
  let M := adjR G
  let P := fun n : ℕ => M^n
  let a := fun x : X => x ⟨0,by omega⟩
  let b := fun x : X => x ⟨1,by omega⟩
  let c := fun x : X => x ⟨k+1,by omega⟩
  let T := fun x : X => if hit x then cycW M x else 0
  let A := fun x : X => (P (k-1)) (a x) (c x)
  let B := fun x : X => (P k) (b x) (c x)
  have hn := Matrix.pow_apply_nonneg (nn12 G)
  have hA (x : X) : 0 ≤ A x := hn _ _ _
  have hB (x : X) : 0 ≤ B x := hn _ _ _
  have hT (x : X) : 0 ≤ T x := by
    dsimp only [T]
    split
    · exact cwNonneg12 G x
    · rfl
  have hf (x : X) : 0 ≤ T x * (A x / B x) := mul_nonneg (hT x) (div_nonneg (hA x) (hB x))
  have hg (x : X) : 0 ≤ T x * (B x / A x) := mul_nonneg (hT x) (div_nonneg (hB x) (hA x))
  have cs := sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset X)
    (fun x _ => hf x) (fun x _ => hg x) (r := T) (by
      intro x _
      by_cases h : cycW M x = 0
      · simp [T,h]
      · obtain ⟨h₁,h₂⟩ := support12 G k hk x h
        have h₁' : A x ≠ 0 := h₁
        have h₂' : B x ≠ 0 := h₂
        apply le_of_eq
        field_simp [h₁',h₂'])
  have hfirst : ∑ x, T x * (A x / B x) ≤ Δ * trace (P (2*(k-1))) := by
    apply le_trans _ (upperFirst12 G Δ hdeg k hk)
    apply sum_le_sum
    intro x _
    change T x * (A x / B x) ≤ cycW M x * (A x / B x)
    apply mul_le_mul_of_nonneg_right _ (div_nonneg (hA x) (hB x))
    dsimp only [T]
    split
    · rfl
    · exact cwNonneg12 G x
  apply Real.le_sqrt_of_sq_le
  change (∑ x, T x)^2 ≤ _
  exact cs.trans (mul_le_mul hfirst hsecond (sum_nonneg (fun x _ => hg x))
    (le_trans (sum_nonneg (fun x _ => hf x)) hfirst))

/-- Cycles homomorphes en conflit depuis la position 0 (lemme 2.1 de [Ja20], forme trace). -/
theorem conflictA_le {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (s Δ : ℝ) (hs : 0 ≤ s) (hΔ : 0 ≤ Δ)
    (hrel : ∀ u v, (#((G.neighborFinset v).filter (r u)) : ℝ) ≤ s)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W,
        (if ∃ j : Fin (2 * k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (x ⟨0, by omega⟩) (x j)
          then cycW (adjR G) x else 0) ≤
      Real.sqrt (k * s * Δ * trace (adjR G ^ (2 * (k - 1))) * trace (adjR G ^ (2 * k))) := by
  classical
  have _hsΔ := mul_nonneg hs hΔ
  let X := Fin (2*k) → W
  let M := adjR G
  let P := fun n : ℕ => M^n
  let a := fun x : X => x ⟨0,by omega⟩
  let b := fun x : X => x ⟨1,by omega⟩
  let c := fun x : X => x ⟨k+1,by omega⟩
  let hit := fun x : X =>
    ∃ j : Fin (2*k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (a x) (x j)
  let T := fun x : X => @ite ℝ (hit x) (Classical.propDecidable _) (cycW M x) 0
  let A := fun x : X => (P (k-1)) (a x) (c x)
  let B := fun x : X => (P k) (b x) (c x)
  have hn := Matrix.pow_apply_nonneg (nn12 G)
  have hA (x : X) : 0 ≤ A x := hn _ _ _
  have hB (x : X) : 0 ≤ B x := hn _ _ _
  let idx := fun p : Fin k => (⟨p.val+1,by omega⟩ : Fin (2*k))
  let term := fun (x : X) (p : Fin k) =>
    cycW M x * (if r (a x) (x (idx p)) then B x / A x else 0)
  have hterm (x p) : 0 ≤ term x p := by
    apply mul_nonneg (cwNonneg12 G x)
    split
    · exact div_nonneg (hB x) (hA x)
    · rfl
  have hsecond : ∑ x, T x * (B x / A x) ≤ (k:ℝ) * (s * trace (P (2*k))) := by
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
      _ ≤ ∑ _p : Fin k, s * trace (P (2*k)) := by
        apply sum_le_sum
        intro p _
        exact upperOne12 G r hr s k (p.val+1) hk (by omega) (by omega) (fun b e _ => hrel e b)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ = ∑ x : X, T x := by
      apply sum_congr rfl
      intro x _
      by_cases h : hit x <;> simp only [T, hit, a] at h ⊢ <;> simp [h, M]
    _ ≤ _ := cs12 G Δ hdeg k hk hit ((k:ℝ) * (s * trace (adjR G ^ (2*k)))) hsecond
    _ = _ := congrArg Real.sqrt (by ring)

/-- Cycles homomorphes dont les positions 0 et 2 sont en relation ; la relation n'est bornée
qu'entre les deux bouts d'une arête. -/
theorem conflict2_le {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (s Δ : ℝ) (hs : 0 ≤ s) (hΔ : 0 ≤ Δ)
    (hrel : ∀ b e, G.Adj b e → (#((G.neighborFinset b).filter (r e)) : ℝ) ≤ s)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W,
        (if r (x ⟨0, by omega⟩) (x ⟨2, by omega⟩) then cycW (adjR G) x else 0) ≤
      Real.sqrt (s * Δ * trace (adjR G ^ (2 * (k - 1))) * trace (adjR G ^ (2 * k))) := by
  classical
  have _hsΔ := mul_nonneg hs hΔ
  let hit := fun x : Fin (2*k) → W => r (x ⟨0,by omega⟩) (x ⟨2,by omega⟩)
  have hlocal (b e : W) (h : (adjR G ^ (2-1)) b e ≠ 0) :
      (#((G.neighborFinset b).filter (r e)) : ℝ) ≤ s := by
    apply hrel b e
    by_contra hn
    exact h (by simp [adjR,hn])
  have hsecond := upperOne12 G r hr s k 2 hk (by omega) hk hlocal
  refine (cs12 G Δ hdeg k hk hit (s * trace (adjR G ^ (2*k))) ?_).trans_eq
    (congrArg Real.sqrt (by ring))
  simpa only [hit, ite_mul, mul_ite, zero_mul, mul_zero] using hsecond

/- ## Lemme 13 : traces de la matrice d'adjacence, Sidorenko, rotations -/

theorem adjR_nonneg {W : Type} [Fintype W] (G : SimpleGraph W) (u v : W) :
    0 ≤ adjR G u v := by
  unfold adjR
  split <;> positivity

theorem cycW_adjR {W : Type} [Fintype W] (G : SimpleGraph W) {L : ℕ} (x : Fin L → W) :
    cycW (adjR G) x =
      if ∀ i : Fin L, G.Adj (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩) then 1 else 0 := by
  classical
  split_ifs with h
  · exact Finset.prod_eq_one (fun i _ => if_pos (h i))
  · obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (mem_univ i) (if_neg hi)

private theorem powNonneg13 {W : Type} [Fintype W] (G : SimpleGraph W) (m : ℕ) (a b : W) :
    0 ≤ (adjR G ^ m) a b := Matrix.pow_apply_nonneg (adjR_nonneg G) m a b

private theorem symm13 {W : Type} [Fintype W] (G : SimpleGraph W) : (adjR G).IsSymm := by
  ext a b
  change (if G.Adj b a then (1:ℝ) else 0) = _
  simp only [adjR, G.adj_comm b a]

theorem one_le_trace_adjR {W : Type} [Fintype W] (G : SimpleGraph W)
    (hG : G.edgeFinset.Nonempty) (k : ℕ) : 1 ≤ trace (adjR G ^ (2 * k)) := by
  classical
  obtain ⟨u,v,huv⟩ := ne_bot_iff_exists_adj.mp (edgeFinset_nonempty.mp hG)
  have h₂ : 1 ≤ (adjR G ^ 2) u u := by
    rw [sq, Matrix.mul_apply]
    calc
      1 = adjR G u v * adjR G v u := by simp [adjR,huv,huv.symm]
      _ ≤ _ := single_le_sum (fun z _ => mul_nonneg (adjR_nonneg G u z) (adjR_nonneg G z u))
        (mem_univ v)
  have hdiag : 1 ≤ (adjR G ^ (2 * k)) u u := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, pow_add, Matrix.mul_apply]
      calc
        1 ≤ (adjR G ^ (2 * k)) u u * (adjR G ^ 2) u u := one_le_mul_of_one_le_of_one_le ih h₂
        _ ≤ _ := single_le_sum (fun z _ => mul_nonneg (powNonneg13 G _ u z) (powNonneg13 G 2 z u))
          (mem_univ u)
  exact hdiag.trans (single_le_sum (fun z _ => powNonneg13 G (2*k) z z) (mem_univ u))

private theorem traceSplit13 {W : Type} [Fintype W] (G : SimpleGraph W) (a b : ℕ) :
    trace (adjR G ^ (a + b)) = ∑ p : W × W, (adjR G ^ a) p.1 p.2 * (adjR G ^ b) p.2 p.1 := by
  simp [pow_add, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]

/-- Log-convexité des traces paires. -/
private theorem logConvex13 {W : Type} [Fintype W] (G : SimpleGraph W) (j : ℕ) (hj : 1 ≤ j) :
    trace (adjR G ^ (2 * j)) ^ 2 ≤
      trace (adjR G ^ (2 * (j - 1))) * trace (adjR G ^ (2 * (j + 1))) := by
  let a := j - 1
  let b := j + 1
  rw [show 2 * j = a + b by dsimp [a, b]; omega, traceSplit13,
      show 2 * (j - 1) = a + a by dsimp [a]; omega, traceSplit13,
      show 2 * (j + 1) = b + b by dsimp [b]; omega, traceSplit13]
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · exact fun _ _ ↦ mul_nonneg (powNonneg13 ..) (powNonneg13 ..)
  · exact fun _ _ ↦ mul_nonneg (powNonneg13 ..) (powNonneg13 ..)
  · rintro ⟨u, v⟩ _
    dsimp only
    rw [((symm13 G).pow a).apply u v, ((symm13 G).pow b).apply u v]
    exact le_of_eq (by ring)

/-- Log-convexité des traces paires, avec `T_0 = |W|`. -/
theorem trace_adjR_interp {W : Type} [Fintype W] (G : SimpleGraph W)
    (hG : G.edgeFinset.Nonempty) (k : ℕ) (hk : 1 ≤ k) :
    trace (adjR G ^ (2 * (k - 1))) ≤
      (Fintype.card W : ℝ) ^ (1 / (k : ℝ)) * trace (adjR G ^ (2 * k)) ^ (1 - 1 / (k : ℝ)) := by
  let T (n : ℕ) := trace (adjR G ^ (2 * n))
  have pos (n : ℕ) : 0 < T n := lt_of_lt_of_le zero_lt_one (one_le_trace_adjR G hG n)
  let a (n : ℕ) := Real.log (T n)
  have step (n : ℕ) : a (n + 1) - a n ≤ a (n + 2) - a (n + 1) := by
    have h : T (n + 1) ^ 2 ≤ T n * T (n + 2) := by
      simpa [T] using logConvex13 G (n + 1) (by omega)
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

-- Recopié de la preuve fusionnée de Sidorenko pour les cycles pairs (PR #641, adaptée de la PR #478).
private theorem symmetricTrace13 {N k : ℕ} (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    ((1 / (N : ℝ)) * ∑ a : Fin N, ∑ b : Fin N, A a b) ^ (2 * k) ≤
      (A ^ (2 * k)).trace := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  let U := hA.eigenvectorUnitary
  let ev : Fin N → ℝ := hA.eigenvalues
  have hspec : A = (U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal ev *
      star (U : Matrix (Fin N) (Fin N) ℝ) := by
    have h := hA.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, U, ev] using h
  have hpow : A ^ (2 * k) =
      Unitary.conjStarAlgAut ℝ _ U (Matrix.diagonal (fun i => ev i ^ (2 * k))) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_pow, Matrix.diagonal_pow]
    rfl
  have htr : (A ^ (2 * k)).trace = ∑ i : Fin N, ev i ^ (2 * k) := by
    rw [hpow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
    have hUU : star (U : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
      Unitary.coe_star_mul_self U
    rw [hUU, one_mul, Matrix.trace_diagonal]
  let v : Fin N → ℝ := fun _ => 1 / Real.sqrt (N : ℝ)
  have hvv : v ⬝ᵥ v = 1 := by
    simp only [dotProduct, v]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hNpos)
    have hsq_ne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hNpos)
    field_simp [hsq_ne, ne_of_gt hNpos]
    linarith
  let w : Fin N → ℝ := (star (U : Matrix (Fin N) (Fin N) ℝ)).mulVec v
  have hstar_tr : star (U : Matrix (Fin N) (Fin N) ℝ) =
      Matrix.transpose (U : Matrix (Fin N) (Fin N) ℝ) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hww : ∑ i : Fin N, w i ^ 2 = 1 := by
    have hdot : w ⬝ᵥ w = 1 := by
      dsimp only [w]
      rw [Matrix.dotProduct_mulVec, hstar_tr, Matrix.vecMul_transpose,
        ← hstar_tr, Matrix.mulVec_mulVec]
      have hUU : (U : Matrix (Fin N) (Fin N) ℝ) * star (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
        Unitary.coe_mul_star_self U
      rw [hUU, Matrix.one_mulVec, hvv]
    simpa [dotProduct, sq] using hdot
  have hquad_lhs : v ⬝ᵥ (A.mulVec v) = (1 / (N : ℝ)) * ∑ a : Fin N, ∑ b : Fin N, A a b := by
    simp only [dotProduct, Matrix.mulVec, v, Finset.mul_sum]
    have hsq_ne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hNpos)
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp [hsq_ne, ne_of_gt hNpos]
    rw [Real.sq_sqrt (le_of_lt hNpos)]
    ring
  have hquad_rhs : v ⬝ᵥ (A.mulVec v) = ∑ i : Fin N, w i ^ 2 * ev i := by
    rw [hspec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    have hvU : Matrix.vecMul v (U : Matrix (Fin N) (Fin N) ℝ) = w := by
      dsimp only [w]
      rw [hstar_tr, Matrix.mulVec_transpose]
    rw [hvU]
    change w ⬝ᵥ ((Matrix.diagonal ev).mulVec w) = _
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 * k)) :=
    (even_two_mul k).convexOn_pow
  have hjensen := hconv.map_sum_le (t := Finset.univ) (w := fun i => w i ^ 2) (p := ev)
    (fun i _ => sq_nonneg (w i)) hww (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hjensen
  have hle_tr : ∑ i : Fin N, w i ^ 2 * ev i ^ (2 * k) ≤ ∑ i : Fin N, ev i ^ (2 * k) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hw_le : w i ^ 2 ≤ 1 := by
      rw [← hww]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
    have hev_nn : 0 ≤ ev i ^ (2 * k) := (even_two_mul k).pow_nonneg (ev i)
    nlinarith
  rw [← hquad_lhs, hquad_rhs, htr]
  exact le_trans hjensen hle_tr

/-- Sidorenko pour les cycles pairs, forme trace (lemme 2.6 de l'article). -/
theorem sidorenko_adjR {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) (k : ℕ) :
    (2 * (#G.edgeFinset : ℝ) / n) ^ (2 * k) ≤ trace (adjR G ^ (2 * k)) := by
  have hA : (adjR G).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact symm13 G
  have hs := symmetricTrace13 (k := k) hn (adjR G) hA
  have hrow (u : Fin n) : ∑ v, adjR G u v = (G.degree u : ℝ) := by
    simp only [adjR, sum_boole, ← G.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]
  simp_rw [hrow] at hs
  have hsum : (∑ a, (G.degree a : ℝ)) = 2 * (#G.edgeFinset : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hs
  simpa only [div_eq_inv_mul, mul_one] using hs

/-- Union sur les rotations pour un conflit entre les positions `i` et `i + 2`. -/
theorem bad2_le_rot {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (r : W → W → Prop) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W,
        (if ∃ i : Fin (2 * k), r (x i) (x ⟨(i.val + 2) % (2 * k), Nat.mod_lt _ i.pos⟩)
          then cycW M x else 0) ≤
      2 * k * ∑ x : Fin (2 * k) → W,
        (if r (x ⟨0, by omega⟩) (x ⟨2, by omega⟩) then cycW M x else 0) := by
  classical
  let : NeZero (2 * k) := ⟨by omega⟩
  let I := Fin (2 * k)
  let rot (s : I) (x : I → W) := fun i : I ↦ x (i + s)
  let q : I := ⟨2,by omega⟩
  let good (x : I → W) := r (x 0) (x q)
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
  change _ ≤ 2 * (k : ℝ) * ∑ x : I → W, B x
  calc
    _ ≤ ∑ x : I → W, ∑ s : I, B (rot s x) := by
      apply sum_le_sum
      intro x _
      split
      · rename_i hx
        obtain ⟨s,hr⟩ := hx
        have hs : good (rot s x) := by
          change r (x (0+s)) (x (q+s))
          rw [zero_add, add_comm q s]
          exact hr
        calc
          cycW M x = B (rot s x) := by simp [B, hs, cyc]
          _ ≤ _ := single_le_sum (fun z _ ↦ bpos (rot z x)) (mem_univ s)
      · exact sum_nonneg fun _ _ ↦ bpos _
    _ = _ := by rw [sum_comm]; simp [reindex, I]

/- ## Lemme 15 : codegrés, conditions 2 et 3 de la définition 2.11 -/

open scoped Fin.NatCast in
private theorem shift15 {L : ℕ} [NeZero L] (i : Fin L) (a : ℕ) :
    (⟨(i.val + a) % L, Nat.mod_lt _ i.pos⟩ : Fin L) = i + (a : Fin L) := by
  apply Fin.ext
  simp [Fin.val_add]

private theorem paths15 {n : ℕ} (G : SimpleGraph (Fin n)) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (m : ℕ) :
    (#(univ.filter fun z : Fin (m + 1) → Fin n => ∀ j : Fin m,
        G.Adj (z j.castSucc) (z j.succ)) : ℝ) ≤ n * Δ ^ m := by
  classical
  let P (l : ℕ) := univ.filter fun z : Fin (l + 1) → Fin n =>
    ∀ j : Fin l, G.Adj (z j.castSucc) (z j.succ)
  change (#(P m) : ℝ) ≤ _
  induction m with
  | zero => simp [P]
  | succ m ih =>
    let U := (P m).sigma fun z => G.neighborFinset (z 0)
    have hcard : #(P (m+1)) ≤ #U := by
      apply card_le_card_of_injOn (fun z : Fin (m + 2) → Fin n =>
        (⟨Fin.tail z, z 0⟩ : Σ _ : Fin (m + 1) → Fin n, Fin n))
      · intro z hz
        have hz' := (mem_filter.mp hz).2
        apply mem_sigma.mpr
        refine ⟨mem_filter.mpr ⟨mem_univ _, fun j => hz' j.succ⟩, ?_⟩
        exact (G.mem_neighborFinset _ _).mpr (hz' 0).symm
      · intro z _ w _ h
        have ht := congrArg Sigma.fst h
        have hh := congrArg (fun q : Σ _ : Fin (m + 1) → Fin n, Fin n => q.2) h
        change Fin.tail z = Fin.tail w at ht
        change z 0 = w 0 at hh
        rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail w, ht, hh]
    calc
      (#(P (m+1)) : ℝ) ≤ #U := by exact_mod_cast hcard
      _ = ∑ z ∈ P m, (G.degree (z 0) : ℝ) := by simp [U]
      _ ≤ ∑ _z ∈ P m, Δ := Finset.sum_le_sum (fun z _ => hdeg (z 0))
      _ = (#(P m) : ℝ) * Δ := by simp
      _ ≤ n * Δ ^ m * Δ := mul_le_mul_of_nonneg_right ih hΔ
      _ = n * Δ ^ (m + 1) := by rw [pow_succ, mul_assoc]

/-- Chaque `a ∈ N(b)`, `a ≠ e`, de codegré `> t` avec `e` donne au moins `t - 1` 4-cycles
étiquetés `(e, b, a, y)` qui passent par l'arête `s(e, b)`. -/
theorem codeg_bound {n : ℕ} (G : SimpleGraph (Fin n)) (t B : ℝ) (b e : Fin n) (hbe : G.Adj b e)
    (hB : (#(((univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter fun q =>
          G.Adj q.1 q.2.1 ∧ G.Adj q.2.1 q.2.2.1 ∧ G.Adj q.2.2.1 q.2.2.2 ∧ G.Adj q.2.2.2 q.1 ∧
            q.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2).filter fun q =>
          s(e, b) = s(q.1, q.2.1) ∨ s(e, b) = s(q.2.1, q.2.2.1) ∨
            s(e, b) = s(q.2.2.1, q.2.2.2) ∨ s(e, b) = s(q.2.2.2, q.1)) : ℝ) ≤ B) :
    (#((G.neighborFinset b).filter fun a =>
        e ≠ a ∧ t < (#(G.neighborFinset e ∩ G.neighborFinset a) : ℝ)) : ℝ) * (t - 1) ≤ B := by
  classical
  let S := (G.neighborFinset b).filter fun a =>
    e ≠ a ∧ t < (#(G.neighborFinset e ∩ G.neighborFinset a) : ℝ)
  let U (a : Fin n) := (G.neighborFinset e ∩ G.neighborFinset a).erase b
  have hu (a) (ha : a ∈ S) : t - 1 ≤ (#(U a) : ℝ) := by
    obtain ⟨hba, _, hgt⟩ := mem_filter.mp ha
    have hb : b ∈ G.neighborFinset e ∩ G.neighborFinset a :=
      mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hbe.symm,
        (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hba).symm⟩
    dsimp only [U]
    rw [Finset.cast_card_erase_of_mem hb]
    linarith
  apply le_trans _ hB
  calc
    _ = ∑ _a ∈ S, (t - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ S, (#(U a) : ℝ) := Finset.sum_le_sum hu
    _ = (#(S.sigma U) : ℝ) := by simp
    _ ≤ _ := by
      exact_mod_cast (Finset.card_le_card_of_injOn
        (fun q : Σ _ : Fin n, Fin n => (e, b, q.1, q.2)) (s := S.sigma U) (by
          rintro ⟨a, y⟩ h
          obtain ⟨ha, hy⟩ := mem_sigma.mp h
          obtain ⟨hba, hea, _⟩ := mem_filter.mp ha
          obtain ⟨hyb, hya⟩ := mem_erase.mp hy
          obtain ⟨hey, hay⟩ := mem_inter.mp hya
          apply mem_filter.mpr
          exact ⟨mem_filter.mpr ⟨mem_univ _, hbe.symm, (G.mem_neighborFinset _ _).mp hba,
            (G.mem_neighborFinset _ _).mp hay, ((G.mem_neighborFinset _ _).mp hey).symm, hea, hyb.symm⟩, Or.inl rfl⟩) (by
          rintro ⟨a, y⟩ _ ⟨a', y'⟩ _ h
          change (e, b, a, y) = (e, b, a', y') at h
          obtain ⟨rfl, rfl⟩ : a = a' ∧ y = y' := by simpa using h
          rfl))

open scoped Fin.NatCast Fin.CommRing in
/-- Condition 2 : à une position près, un cycle homomorphe est déterminé par un voisin commun
de ses deux voisins. -/
theorem fix1_card {n : ℕ} (G : SimpleGraph (Fin n)) (L : ℕ) (hL : 3 ≤ L) (s : ℝ)
    (C : Finset (Fin L → Fin n))
    (hC : ∀ x ∈ C, (∀ i : Fin L, G.Adj (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩)) ∧
      ∀ i : Fin L, (#(G.neighborFinset (x i) ∩
        G.neighborFinset (x ⟨(i.val + 2) % L, Nat.mod_lt _ i.pos⟩)) : ℝ) ≤ s) :
    ∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s := by
  classical
  let : NeZero L := ⟨by omega⟩
  intro y hy i
  let p := i - 1
  have hp1 : p + 1 = i := sub_add_cancel _ _
  have hp2 : p + 2 = i + 1 := by dsimp [p]; ring
  have hone : (1 : Fin L) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < L)] at hv
  have hn : i + 1 ≠ i := fun h => hone (add_left_cancel (show i + 1 = i + 0 by rwa [add_zero]))
  have hp : p ≠ i := fun h => hn ((congrArg (· + 1) h.symm).trans hp1)
  have hbound := (hC y hy).2 p
  rw [shift15, Nat.cast_ofNat, hp2] at hbound
  apply le_trans _ hbound
  exact_mod_cast (card_le_card_of_injOn (fun x : Fin L → Fin n => x i) (by
    intro x hx
    obtain ⟨hxc, hxy⟩ := mem_filter.mp hx
    have h1 := (hC x hxc).1 p
    have h2 := (hC x hxc).1 i
    rw [shift15, Nat.cast_one, hp1, hxy p hp] at h1
    rw [shift15, Nat.cast_one, hxy _ hn] at h2
    exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1, (G.mem_neighborFinset _ _).mpr h2.symm⟩) (by
    intro x hx z hz he
    funext j
    by_cases hj : j = i
    · exact hj ▸ he
    · exact ((mem_filter.mp hx).2 j hj).trans ((mem_filter.mp hz).2 j hj).symm))

open scoped Fin.NatCast Fin.CommRing in
/-- Condition 3 : oublier deux positions consécutives d'un cycle homomorphe laisse un chemin à
`L - 3` arêtes, d'où au plus `|W| Δ^(L-3)` images. -/
theorem forget2_card {n : ℕ} (G : SimpleGraph (Fin n)) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (L : ℕ) (hL : 3 ≤ L) (C : Finset (Fin L → Fin n))
    (hC : ∀ x ∈ C, ∀ i : Fin L, G.Adj (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩))
    (i : Fin L) :
    let nx : Fin L → Fin L := fun i => ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    ∃ P : Finset (Fin L → Fin n), (#P : ℝ) ≤ n * Δ ^ (L - 3) ∧
      ∀ x ∈ C, ∃ y ∈ P, ∀ j, j ≠ nx i → j ≠ nx (nx i) → x j = y j := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 3 := ⟨L - 3, by omega⟩
  intro nx
  have hnx (j) : nx j = j + 1 := by simpa only [Nat.cast_one] using shift15 j 1
  let P := univ.filter fun z : Fin (m + 1) → Fin n => ∀ j : Fin m, G.Adj (z j.castSucc) (z j.succ)
  let expand (z : Fin (m + 1) → Fin n) (j : Fin (m + 3)) : Fin n :=
    if h : (i - j).val < m + 1 then z ⟨(i - j).val, h⟩ else z 0
  refine ⟨P.image expand, ?_, ?_⟩
  · calc
      (#(P.image expand) : ℝ) ≤ #P := by exact_mod_cast (card_image_le : #(P.image expand) ≤ #P)
      _ ≤ n * Δ ^ m := paths15 G Δ hΔ hdeg m
      _ = _ := by simp
  · intro x hx
    let z (t : Fin (m + 1)) := x (i - (t.val : Fin (m + 3)))
    have hz : z ∈ P := by
      apply mem_filter.mpr
      refine ⟨mem_univ _, fun j => ?_⟩
      have ha := (hC x hx (i - ((j.val : Fin (m + 3)) + 1))).symm
      rw [shift15, Nat.cast_one] at ha
      have hshift : i - ((j.val : Fin (m + 3)) + 1) + 1 = i - (j.val : Fin (m + 3)) := by abel
      simpa only [z, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, hshift] using ha
    refine ⟨expand z, mem_image_of_mem _ hz, fun j hj₁ hj₂ => ?_⟩
    have hwrap : (m : Fin (m + 3)) + 3 = 0 := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using Fin.natCast_self (m + 3)
    have hback : (((i - j).val : ℕ) : Fin (m + 3)) = i - j := by simp
    have hsmall : (i - j).val < m + 1 := by
      by_contra! hn
      have hlt := (i - j).isLt
      have he : (i - j).val = m + 1 ∨ (i - j).val = m + 2 := by omega
      rcases he with he | he
      · apply hj₂
        rw [hnx, hnx]
        rw [he, Nat.cast_add, Nat.cast_one] at hback
        linear_combination hback - hwrap
      · apply hj₁
        rw [hnx]
        rw [he, Nat.cast_add, Nat.cast_ofNat] at hback
        linear_combination hback - hwrap
    simp only [expand, dif_pos hsmall, z, hback]
    simp

/- ## Lemme 16 : asymptotique -/

private theorem growth16 (C a b : ℝ) (h : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ)^a ≤ (n : ℝ)^b := by
  have ht := ((tendsto_rpow_atTop (sub_pos.mpr h)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop C
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht] with n hn hc
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc
    _ ≤ (n : ℝ)^(b-a) * (n : ℝ)^a := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← Real.rpow_add hn', sub_add_cancel]

private theorem sqrt16 {q d N T S P : ℝ} (hT : 0 < T) (hP : 0 ≤ P)
    (hS : S ≤ N^d * T^(1-d)) (hcoef : 64*q^2*P*N^d ≤ T^d) :
    2*q * Real.sqrt (P*S*T) ≤ T/4 := by
  by_cases h : P*S*T ≤ 0
  · rw [Real.sqrt_eq_zero_of_nonpos h, mul_zero]; positivity
  have hbound : 64*q^2*P*S ≤ T := calc
    _ ≤ 64*q^2*P*(N^d*T^(1-d)) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (64*q^2*P*N^d)*T^(1-d) := by ring
    _ ≤ T^d*T^(1-d) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = T := by rw [← Real.rpow_add hT, show d+(1-d) = 1 by ring, Real.rpow_one]
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, Real.sq_sqrt (le_of_not_ge h)]
  nlinarith only [mul_le_mul_of_nonneg_right hbound hT.le]

private theorem last16 {ε K N a T : ℝ} {k L : ℕ} (hN : 0 < N) (hk : 0 < k)
    (hmin : (N^a / 3)^L ≤ T)
    (hbig : (32*(k:ℝ)*3^L*K^(L-3)) * N^(1+a*(↑(L-3) : ℝ)+2*ε+ε/2) ≤ N^(a*(L:ℝ))) :
    N * (K*N^a)^(L-3) ≤ N^(-(ε/2)) * (T/2) / (16*k*N^(2*ε)) := by
  have hthree : (0:ℝ) < 3^L := by positivity
  rw [div_pow] at hmin
  rw [Real.rpow_mul hN.le a (L : ℝ), Real.rpow_natCast] at hbig
  have h := hbig.trans ((div_le_iff₀ hthree).mp hmin)
  have hprod : N*(K*N^a)^(L-3)*(16*k*N^(2*ε))*(2*N^(ε/2)) ≤ T := by
    apply (le_of_mul_le_mul_right _ hthree)
    calc
      _ = (32*(k:ℝ)*3^L*K^(L-3)) * N^(1+a*(↑(L-3) : ℝ)+2*ε+ε/2) := by
        rw [mul_pow, Real.rpow_add hN, Real.rpow_add hN, Real.rpow_add hN, Real.rpow_one,
          Real.rpow_mul hN.le a (↑(L-3) : ℝ), Real.rpow_natCast]
        ring
      _ ≤ _ := h
  apply (le_div_iff₀ (by positivity)).mpr
  rw [Real.rpow_neg hN.le, ← div_eq_inv_mul]
  apply (le_div_iff₀ (by positivity)).mpr
  linarith only [hprod]

/-- Les inégalités numériques de la preuve, pour `n` grand (`K4 = 4k`, `L = 8k`). -/
theorem h1_asymp (ε K : ℝ) (hε : 0 < ε) (hε6 : ε < 1 / 6) (hK : 0 < K) (k : ℕ)
    (hk : 1 / ε ≤ k) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 2 ≤ (n : ℝ) ^ (2 * ε) ∧
      ∀ E T T' : ℝ, (n : ℝ) ^ (4 / 3 + ε) / 6 ≤ E → (2 * E / n) ^ (2 * (4 * k)) ≤ T →
        T' ≤ (n : ℝ) ^ (1 / ((4 * k : ℕ) : ℝ)) * T ^ (1 - 1 / ((4 * k : ℕ) : ℝ)) →
        0 < T ∧
        2 * ((4 * k : ℕ) : ℝ) *
            Real.sqrt (((4 * k : ℕ) : ℝ) * 1 * (K * (n : ℝ) ^ (1 / 3 + ε)) * T' * T) ≤ T / 4 ∧
        2 * ((4 * k : ℕ) : ℝ) *
            Real.sqrt (8 * (n : ℝ) ^ (1 / 3 + 2 * ε) / ((n : ℝ) ^ (2 * ε) - 1) *
              (K * (n : ℝ) ^ (1 / 3 + ε)) * T' * T) ≤ T / 4 ∧
        (n : ℝ) * (K * (n : ℝ) ^ (1 / 3 + ε)) ^ (2 * (4 * k) - 3) ≤
          (n : ℝ) ^ (-(ε / 2)) * (T / 2) / (16 * k * (n : ℝ) ^ (2 * ε)) := by
  let q : ℝ := ((4*k : ℕ) : ℝ)
  let L := 2*(4*k)
  let d : ℝ := 1/q
  let a : ℝ := 1/3+ε
  have hkpos : 0 < k := by
    have hh : (6:ℝ) < k := lt_of_lt_of_le ((lt_div_iff₀ hε).mpr (by linarith only [hε6])) hk
    exact_mod_cast (lt_trans (by norm_num : (0:ℝ) < 6) hh)
  have hq : 0 < q := by dsimp [q]; positivity
  have hd : 0 < d := one_div_pos.mpr hq
  have hdε : d ≤ ε/4 := by
    apply (div_le_iff₀ hq).mpr
    have hh := (div_le_iff₀ hε).mp hk
    dsimp [q]; push_cast; linarith
  have hp : (L : ℝ)*d = 2 := by
    dsimp [L,d,q]; push_cast; field_simp
  have he₁ : a+d < 2*a := by dsimp [a]; linarith
  have he₂ : 1/3+a+d < 2*a := by dsimp [a]; linarith
  have he₃ : 1+a*(↑(L-3) : ℝ)+2*ε+ε/2 < a*(L:ℝ) := by
    rw [Nat.cast_sub (by dsimp [L]; omega : 3 ≤ L)]
    dsimp [a]; linarith
  have ht := ((tendsto_rpow_atTop (show 0 < 2*ε by positivity)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht, growth16 (576*q^3*K) _ _ he₁,
    growth16 (9216*q^2*K) _ _ he₂, growth16 (32*(k:ℝ)*3^L*K^(L-3)) _ _ he₃]
    with n hn h2 h₁ h₂ h₃
  let N : ℝ := n
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (by omega : 0 < n)
  refine ⟨hn,h2,?_⟩
  intro E T T' hE hT hT'
  have hbase : N^a/3 ≤ 2*E/N := by
    apply (le_div_iff₀ hN).mpr
    change N^(4/3+ε)/6 ≤ E at hE
    rw [show 4/3+ε = a+1 by dsimp [a]; ring, Real.rpow_add hN, Real.rpow_one] at hE
    linarith
  have hmin : (N^a/3)^L ≤ T := (pow_le_pow_left₀ (by positivity) hbase L).trans hT
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hmin
  have hroot : N^(2*a)/9 ≤ T^d := calc
    _ = (N^a/3)^2 := by rw [mul_comm (2:ℝ), Real.rpow_mul hN.le, Real.rpow_two]; ring
    _ = ((N^a/3)^L)^d := by
      rw [← Real.rpow_natCast _ L, ← Real.rpow_mul (by positivity), hp, Real.rpow_two]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hmin hd.le
  have hfirst : 64*q^2*(q*1*(K*N^a))*N^d ≤ T^d := by
    apply le_trans _ hroot
    change 576*q^3*K*N^(a+d) ≤ N^(2*a) at h₁
    rw [Real.rpow_add hN] at h₁
    linarith only [h₁]
  have hs : 8*N^(1/3+2*ε)/(N^(2*ε)-1) ≤ 16*N^(1/3:ℝ) := by
    change 2 ≤ N^(2*ε) at h2
    apply (div_le_iff₀ (by linarith)).mpr
    rw [Real.rpow_add hN]
    nlinarith only [mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hN.le (1/3))]
  have hsecond : 64*q^2*((8*N^(1/3+2*ε)/(N^(2*ε)-1))*(K*N^a))*N^d ≤ T^d := by
    apply le_trans _ hroot
    calc
      _ ≤ 64*q^2*((16*N^(1/3:ℝ))*(K*N^a))*N^d := by gcongr
      _ ≤ _ := by
        change 9216*q^2*K*N^(1/3+a+d) ≤ N^(2*a) at h₂
        rw [Real.rpow_add hN, Real.rpow_add hN] at h₂
        linarith only [h₂]
  have hden : 0 ≤ N^(2*ε)-1 := by change 2 ≤ N^(2*ε) at h2; linarith
  exact ⟨hTpos, sqrt16 hTpos (by positivity) hT' hfirst,
    sqrt16 hTpos (by positivity) hT' hsecond, last16 hN hkpos hmin h₃⟩

end E147H1

private theorem diff14 {L : ℕ} (hL : 3 ≤ L) (i : Fin L) :
    i ≠ ⟨(i.val + 2) % L, Nat.mod_lt _ i.pos⟩ := by
  intro he
  have h := congrArg Fin.val he
  change i.val = (i.val + 2) % L at h
  by_cases hb : i.val + 2 < L
  · rw [Nat.mod_eq_of_lt hb] at h
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : L ≤ i.val + 2), Nat.mod_eq_of_lt (by omega)] at h
    omega

open E147H1 in
set_option maxHeartbeats 2000000 in
lemma h1_solution : OMA.R_Erdos147_erdos_147_variants_cubic_R1.H1 := by
  classical
  intro ε K hε hε6 hK k hk
  have hkpos : 0 < k := by
    by_contra! hz
    have hzero : k = 0 := by omega
    rw [hzero, Nat.cast_zero] at hk
    exact (not_lt_of_ge hk) (by positivity)
  let m := 4 * k
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hL : 3 ≤ 2 * m := by omega
  filter_upwards [h1_asymp ε K hε hε6 hK k hk] with n hn
  obtain ⟨hn1, hn2, hnum⟩ := hn
  intro G c4 nxt₀ hE hdeg hc4
  let next (L : ℕ) (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
  let result (L : ℕ) : Prop := ∃ C : Finset (Fin L → Fin n), C.Nonempty ∧ ∃ s : ℝ, 0 < s ∧
    (∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (next L i))) ∧
    (∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s) ∧
    ∀ i : Fin L, ∃ P : Finset (Fin L → Fin n),
      (#P : ℝ) ≤ (n : ℝ) ^ (-(ε / 2)) * #C / (16 * k * s) ∧
      ∀ x ∈ C, ∃ y ∈ P, ∀ j, j ≠ next L i → j ≠ next L (next L i) → x j = y j
  change result (8 * k)
  rw [show 8 * k = 2 * m by dsimp [m]; ring]
  let nxt := next (2 * m)
  let A := adjR G
  let T := trace (A ^ (2 * m))
  let T' := trace (A ^ (2 * (m - 1)))
  let Δ := K * (n : ℝ) ^ (1 / 3 + ε)
  let s := (n : ℝ) ^ (2 * ε)
  let B := 8 * (n : ℝ) ^ (1 / 3 + 2 * ε)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < s := by dsimp [s]; positivity
  have hsm : 0 < s - 1 := by change 2 ≤ s at hn2; linarith
  have hΔ : 0 ≤ Δ := by dsimp [Δ]; positivity
  have hG : G.edgeFinset.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (show 0 < (#G.edgeFinset : ℝ) from lt_of_lt_of_le (by positivity) hE)
  have hT := sidorenko_adjR hn1 G m
  have hT' := trace_adjR_interp G hG m (by omega)
  rw [Fintype.card_fin] at hT'
  obtain ⟨hpos, hrep, hcodeg, hlast⟩ := hnum (#G.edgeFinset) T T' hE hT (by
    dsimp only [T, T', A, m]
    dsimp only [m] at hT'
    convert hT' using 0
    congr!)
  let r : Fin n → Fin n → Prop := fun u w =>
    u ≠ w ∧ s < (#(G.neighborFinset u ∩ G.neighborFinset w) : ℝ)
  have hr : ∀ u w, r u w → r w u := by
    intro u w h
    exact ⟨h.1.symm, by simpa only [Finset.inter_comm] using h.2⟩
  have hrel : ∀ b e, G.Adj b e → (#((G.neighborFinset b).filter (r e)) : ℝ) ≤ B / (s - 1) := by
    intro b e he
    apply (le_div_iff₀ hsm).2
    exact codeg_bound G s B b e he (hc4 s(e, b) (by simpa using he.symm))
  let bad₁ (x : Fin (2 * m) → Fin n) := ∃ i j, i ≠ j ∧ x i = x j
  let two (i : Fin (2 * m)) : Fin (2 * m) := ⟨(i.val + 2) % (2 * m), Nat.mod_lt _ i.pos⟩
  let bad₂ (x : Fin (2 * m) → Fin n) := ∃ i, r (x i) (x (two i))
  have hrel₁ (u v : Fin n) : (#((G.neighborFinset v).filter (Eq u)) : ℝ) ≤ 1 := by
    have hsub : (G.neighborFinset v).filter (Eq u) ⊆ {u} := by
      intro w hw
      exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hw).2.symm
    exact_mod_cast (show #((G.neighborFinset v).filter (Eq u)) ≤ 1 by
      simpa only [Finset.card_singleton] using Finset.card_le_card hsub)
  have hS₁ : (∑ x, if bad₁ x then cycW A x else 0) ≤ T / 4 := by
    have hrot := bad_le_rot A (adjR_nonneg G) Eq (fun _ _ h => h.symm) m hm
    have hanch := conflictA_le G Eq (fun _ _ h => h.symm) 1 Δ (by norm_num) hΔ (by
      intro u v
      convert hrel₁ u v using 0
      congr!) hdeg m hm
    have hb := hrot.trans (mul_le_mul_of_nonneg_left hanch (by positivity))
    apply le_trans _ hrep
    dsimp only [bad₁, T, T', Δ, A, m] at hb ⊢
    convert hb using 0
    congr!
  have hS₂ : (∑ x, if bad₂ x then cycW A x else 0) ≤ T / 4 := by
    have hrot := bad2_le_rot A (adjR_nonneg G) r m hm
    have hanch := conflict2_le G r hr (B / (s - 1)) Δ (by dsimp [B]; positivity) hΔ (by
      intro b e he
      convert hrel b e he using 0
      congr!) hdeg m hm
    have hb := hrot.trans (mul_le_mul_of_nonneg_left hanch (by positivity))
    apply le_trans _ hcodeg
    dsimp only [bad₂, two, T, T', B, s, Δ, A, m] at hb ⊢
    convert hb using 0
    congr!
  let cycle (x : Fin (2 * m) → Fin n) := ∀ i, G.Adj (x i) (x (nxt i))
  let small (x : Fin (2 * m) → Fin n) := ∀ i,
    (#(G.neighborFinset (x i) ∩ G.neighborFinset (x (two i))) : ℝ) ≤ s
  let C := univ.filter fun x : Fin (2 * m) → Fin n => Function.Injective x ∧ cycle x ∧ small x
  have hC (x) (hx : x ∈ C) : Function.Injective x ∧ cycle x ∧ small x := (mem_filter.mp hx).2
  have hpoint (x : Fin (2 * m) → Fin n) : cycW A x - (if bad₁ x then cycW A x else 0) -
      (if bad₂ x then cycW A x else 0) ≤ if x ∈ C then (1 : ℝ) else 0 := by
    have hw : cycW A x = if cycle x then 1 else 0 := cycW_adjR G x
    by_cases hcyc : cycle x
    · rw [if_pos hcyc] at hw
      rw [hw]
      by_cases h₁ : bad₁ x
      · split_ifs <;> norm_num
      by_cases h₂ : bad₂ x
      · split_ifs <;> norm_num
      have hinj : Function.Injective x := fun i j hij =>
        by_contra fun hne => h₁ ⟨i, j, hne, hij⟩
      have hx : x ∈ C := by
        apply mem_filter.mpr
        refine ⟨mem_univ _, hinj, hcyc, fun i => le_of_not_gt fun hgt => h₂ ⟨i, ?_, hgt⟩⟩
        exact fun h => diff14 hL i (hinj h)
      simp [h₁, h₂, hx]
    · rw [if_neg hcyc] at hw
      rw [hw]
      split_ifs <;> norm_num
  have hsum := Finset.sum_le_sum (s := univ) (fun x _ => hpoint x)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, total_cycW_eq_trace A m hm] at hsum
  have hcard : T - (∑ x, if bad₁ x then cycW A x else 0) -
      (∑ x, if bad₂ x then cycW A x else 0) ≤ (#C : ℝ) := by
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter] at hsum
    dsimp only [T]
    convert hsum using 0
    congr!
  have hhalf : T / 2 ≤ (#C : ℝ) := by linarith only [hcard, hS₁, hS₂]
  have hCpos : 0 < (#C : ℝ) := lt_of_lt_of_le (by linarith only [hpos]) hhalf
  refine ⟨C, Finset.card_pos.mp (by exact_mod_cast hCpos), s, hs,
    fun x hx => ⟨(hC x hx).1, (hC x hx).2.1⟩,
    fix1_card G (2 * m) hL s C (fun x hx => (hC x hx).2), fun i => ?_⟩
  obtain ⟨P, hP, hP'⟩ := forget2_card G Δ hΔ hdeg (2 * m) hL C (fun x hx => (hC x hx).2.1) i
  refine ⟨P, hP.trans (hlast.trans ?_), hP'⟩
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhalf (by positivity)) (by positivity)
end H1Sec

section H2Sec
open SimpleGraph Finset Filter Asymptotics Matrix
open scoped Classical

namespace E147H2

/-- Poids d'un uplet cyclique `x : Fin L → W` : produit des `M (x i) (x (i+1 mod L))`. -/
noncomputable def cycW {W : Type} [Fintype W] (M : Matrix W W ℝ) {L : ℕ} (x : Fin L → W) : ℝ :=
  ∏ i : Fin L, M (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩)

/-- Multiplicités d'un ensemble de triplets : `hmat D a b = #{y | (a, y, b) ∈ D}`. -/
noncomputable def hmat {W : Type} [Fintype W] (D : Finset (W × W × W)) : Matrix W W ℝ :=
  fun a b => (#(D.filter fun t => t.1 = a ∧ t.2.2 = b) : ℝ)

/-- Les triplets de `D` qui commencent par `a`. -/
noncomputable def rowSet {W : Type} (D : Finset (W × W × W)) (a : W) : Finset (W × W × W) :=
  D.filter fun t => t.1 = a

/-- Les milieux `y` des triplets `(a, y, z)` de `D`. -/
noncomputable def extSet {W : Type} (D : Finset (W × W × W)) (a : W) : Finset W :=
  (rowSet D a).image fun t => t.2.1

/-- Les `2m`-cycles injectifs `x₀ y₀ x₁ y₁ ⋯ x_(m-1) y_(m-1)` (positions `2i` et `2i+1`) dont
chaque triplet `(x_i, y_i, x_(i+1))` est dans `D`. -/
noncomputable def cycSet {W : Type} [Fintype W] (D : Finset (W × W × W)) (m : ℕ) :
    Finset (Fin (2 * m) → W) :=
  univ.filter fun w => Function.Injective w ∧ ∀ i : Fin m,
    (w ⟨2 * i.val, by have := i.isLt; omega⟩, w ⟨2 * i.val + 1, by have := i.isLt; omega⟩,
      w ⟨(2 * i.val + 2) % (2 * m), Nat.mod_lt _ (by have := i.isLt; omega)⟩) ∈ D

/- ## Déjà prouvés pour `H1` (repris de `h1-complet.lean`) -/

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

/-- Masse totale des uplets cycliques de longueur `2k`. -/
theorem total_cycW_eq_trace {W : Type} [Fintype W] (M : Matrix W W ℝ)
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

/- ## Lemme 17 : traces d'une matrice pondérée symétrique -/

/- ## Auxiliaires (modèle : `h1-complet.lean`, lemmes 12 et 13) -/

private theorem symm17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hsym : ∀ u v, M u v = M v u)
    (n : ℕ) (u v : W) : (M ^ n) u v = (M ^ n) v u := by
  have h : M.IsSymm := by
    ext a b
    exact hsym b a
  exact (h.pow n).apply v u

private theorem trip17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (k : ℕ) (hk : 2 ≤ k)
    (F : W → W → W → ℝ) :
    ∑ x : Fin (2*k) → W, cycW M x * F (x ⟨0,by omega⟩) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) =
    ∑ a, ∑ b, ∑ c, M a b * (M^k) b c * (M^(k-1)) c a * F a b c := by
  classical
  rw [cyc_split M k 1 hk (by omega) (by omega) (fun a b _ c => F a b c)]
  simp [Matrix.one_apply, mul_ite, ite_mul, sum_ite_irrel]

private theorem trace17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (p q : ℕ) :
    trace (M ^ (p+q)) = ∑ a, ∑ b, (M^p) a b * (M^q) b a := by
  simp only [pow_add, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private theorem ratio17 {U V : ℝ} (hU : 0 ≤ U) (_hV : 0 ≤ V) : V * (U / V) ≤ U := by
  by_cases h : V = 0
  · simp [h, hU]
  · exact le_of_eq (by field_simp)

private theorem upperFirst17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (R : ℝ) (hrow : ∀ a, ∑ b, M a b ≤ R) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2*k) → W, cycW M x *
      ((M^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) /
       (M^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩)) ≤
    R * trace (M ^ (2*(k-1))) := by
  classical
  let P := fun n : ℕ => M^n
  have hn := Matrix.pow_apply_nonneg hM
  rw [trip17 M k hk (fun a b c => (P (k-1)) a c / (P k) b c),
    two_mul, trace17, mul_sum]
  apply sum_le_sum
  intro a _
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro c _
  calc
    _ ≤ ∑ b, M a b * ((P (k-1)) a c * (P (k-1)) c a) := by
      apply sum_le_sum
      intro b _
      have hh := mul_le_mul_of_nonneg_left (ratio17 (hn (k-1) a c) (hn k b c))
        (mul_nonneg (hM a b) (hn (k-1) c a))
      dsimp [P] at *
      linarith only [hh]
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (hrow a) (mul_nonneg (hn _ _ _) (hn _ _ _))

private theorem mass17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u) (r : W → W → Prop) (hr : ∀ u w, r u w → r w u) (s : ℝ)
    (hmass : ∀ b e, ∑ a, (if r e a then M b a else 0) ≤ s) (n : ℕ) (b e c : W) :
    ∑ a, (if r a e then M a b * (M^n) c a / (M^n) a c else 0) ≤ s := by
  classical
  calc
    _ ≤ ∑ a, (if r e a then M b a else 0) := by
      apply sum_le_sum
      intro a _
      rw [symm17 M hsym n c a]
      by_cases h : r a e
      · rw [if_pos h, if_pos (hr a e h), hsym a b, mul_div_assoc]
        exact mul_le_of_le_one_right (hM b a) (div_self_le_one _)
      · rw [if_neg h]
        split
        · exact hM b a
        · exact le_rfl
    _ ≤ s := hmass b e

private theorem upperOne17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u) (r : W → W → Prop) (hr : ∀ u w, r u w → r w u) (s : ℝ)
    (hmass : ∀ b e, ∑ a, (if r e a then M b a else 0) ≤ s)
    (k j : ℕ) (hk : 2 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∑ x : Fin (2*k) → W, cycW M x *
      (if r (x ⟨0,by omega⟩) (x ⟨j,by omega⟩) then
       (M^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) /
       (M^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) else 0) ≤
    s * trace (M ^ (2*k)) := by
  classical
  let P := fun n : ℕ => M^n
  have hn := Matrix.pow_apply_nonneg hM
  rw [cyc_split M k j hk hj hjk
    (fun a b e c => if r a e then (P k) b c / (P (k-1)) a c else 0),
    two_mul, trace17, mul_sum]
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
  calc
    _ ≤ ∑ e, s * ((P (j-1)) b e * (P (k+1-j)) e c * (P k) b c) := by
      apply sum_le_sum
      intro e _
      have hh := mass17 M hM hsym r hr s hmass (k-1) b e c
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hh
        (mul_nonneg (mul_nonneg (hn _ _ _) (hn _ _ _)) (hn _ _ _)))
      rw [sum_mul]
      apply sum_congr rfl
      intro a _
      dsimp [f, P]
      by_cases hr' : r a e
      · simp only [hr', if_true]
        ring
      · simp [hr']
    _ = s * ((P k) b c * (P k) b c) := by
      rw [← mul_sum, ← sum_mul]
      have hp : (∑ e, (P (j-1)) b e * (P (k+1-j)) e c) = (P k) b c := by
        change ((M^(j-1)) * (M^(k+1-j))) b c = _
        rw [← pow_add, show j-1 + (k+1-j) = k by omega]
      rw [hp]
    _ = _ := by
      exact congrArg (fun z => s * ((P k) b c * z)) (symm17 M hsym k b c)

private theorem cwNonneg17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    {N : ℕ} (x : Fin N → W) : 0 ≤ cycW M x :=
  prod_nonneg (fun _ _ => hM _ _)

private theorem support17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u)
    (k : ℕ) (hk : 2 ≤ k) (x : Fin (2*k) → W) (hx : cycW M x ≠ 0) :
    (M^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) ≠ 0 ∧
    (M^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) ≠ 0 := by
  classical
  let P := fun n : ℕ => M^n
  let bad := fun a b c : W => if (P (k-1)) a c = 0 ∨ (P k) b c = 0 then (1:ℝ) else 0
  let term := fun y : Fin (2*k) → W => cycW M y * bad (y ⟨0,by omega⟩) (y ⟨1,by omega⟩)
    (y ⟨k+1,by omega⟩)
  have hzero : ∑ y, term y = 0 := by
    dsimp only [term]
    rw [trip17 M k hk bad]
    apply sum_eq_zero
    intro a _
    apply sum_eq_zero
    intro b _
    apply sum_eq_zero
    intro c _
    by_cases ha : (P (k-1)) a c = 0
    · have hc : (P (k-1)) c a = 0 := (symm17 M hsym (k-1) c a).trans ha
      change _ * (P (k-1)) c a * _ = 0
      simp [hc]
    · by_cases hb : (P k) b c = 0
      · change _ * (P k) b c * _ * _ = 0
        simp [hb]
      · simp [bad, ha, hb]
  have hn (y) (_ : y ∈ univ) : 0 ≤ term y := by
    dsimp only [term,bad]
    exact mul_nonneg (cwNonneg17 M hM y) (by split <;> norm_num)
  have hh := (sum_eq_zero_iff_of_nonneg hn).mp hzero x (mem_univ x)
  dsimp only [term,bad] at hh
  by_contra! h
  have h' : (P (k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) = 0 ∨
      (P k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) = 0 := by tauto
  rw [if_pos h', mul_one] at hh
  exact hx hh

private theorem cs17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u)
    (R : ℝ) (hrow : ∀ a, ∑ b, M a b ≤ R) (k : ℕ) (hk : 2 ≤ k)
    (hit : (Fin (2*k) → W) → Prop) (C : ℝ)
    (hsecond : ∑ x : Fin (2*k) → W, (if hit x then cycW M x else 0) *
      ((M^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) /
       (M^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩)) ≤ C) :
    (∑ x, if hit x then cycW M x else 0) ≤
      Real.sqrt ((R * trace (M ^ (2*(k-1)))) * C) := by
  classical
  let X := Fin (2*k) → W
  let P := fun n : ℕ => M^n
  let a := fun x : X => x ⟨0,by omega⟩
  let b := fun x : X => x ⟨1,by omega⟩
  let c := fun x : X => x ⟨k+1,by omega⟩
  let T := fun x : X => if hit x then cycW M x else 0
  let A := fun x : X => (P (k-1)) (a x) (c x)
  let B := fun x : X => (P k) (b x) (c x)
  have hn := Matrix.pow_apply_nonneg hM
  have hA (x : X) : 0 ≤ A x := hn _ _ _
  have hB (x : X) : 0 ≤ B x := hn _ _ _
  have hT (x : X) : 0 ≤ T x := by
    dsimp only [T]
    split
    · exact cwNonneg17 M hM x
    · rfl
  have hf (x : X) : 0 ≤ T x * (A x / B x) := mul_nonneg (hT x) (div_nonneg (hA x) (hB x))
  have hg (x : X) : 0 ≤ T x * (B x / A x) := mul_nonneg (hT x) (div_nonneg (hB x) (hA x))
  have cs := sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset X)
    (fun x _ => hf x) (fun x _ => hg x) (r := T) (by
      intro x _
      by_cases h : cycW M x = 0
      · simp [T,h]
      · obtain ⟨h₁,h₂⟩ := support17 M hM hsym k hk x h
        have h₁' : A x ≠ 0 := h₁
        have h₂' : B x ≠ 0 := h₂
        apply le_of_eq
        field_simp [h₁',h₂'])
  have hfirst : ∑ x, T x * (A x / B x) ≤ R * trace (P (2*(k-1))) := by
    apply le_trans _ (upperFirst17 M hM R hrow k hk)
    apply sum_le_sum
    intro x _
    change T x * (A x / B x) ≤ cycW M x * (A x / B x)
    apply mul_le_mul_of_nonneg_right _ (div_nonneg (hA x) (hB x))
    dsimp only [T]
    split
    · rfl
    · exact cwNonneg17 M hM x
  apply Real.le_sqrt_of_sq_le
  change (∑ x, T x)^2 ≤ _
  exact cs.trans (mul_le_mul hfirst hsecond (sum_nonneg (fun x _ => hg x))
    (le_trans (sum_nonneg (fun x _ => hf x)) hfirst))

private theorem traceSplit17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (a b : ℕ) :
    trace (M ^ (a + b)) = ∑ p : W × W, (M ^ a) p.1 p.2 * (M ^ b) p.2 p.1 := by
  simp [pow_add, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]

/-- Log-convexité des traces paires. -/
private theorem logConvex17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u) (j : ℕ) (hj : 1 ≤ j) :
    trace (M ^ (2 * j)) ^ 2 ≤ trace (M ^ (2 * (j - 1))) * trace (M ^ (2 * (j + 1))) := by
  have hn := Matrix.pow_apply_nonneg hM
  let a := j - 1
  let b := j + 1
  rw [show 2 * j = a + b by dsimp [a, b]; omega, traceSplit17,
      show 2 * (j - 1) = a + a by dsimp [a]; omega, traceSplit17,
      show 2 * (j + 1) = b + b by dsimp [b]; omega, traceSplit17]
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · exact fun _ _ ↦ mul_nonneg (hn ..) (hn ..)
  · exact fun _ _ ↦ mul_nonneg (hn ..) (hn ..)
  · rintro ⟨u, v⟩ _
    dsimp only
    rw [symm17 M hsym a v u, symm17 M hsym b v u]
    exact le_of_eq (by ring)

-- Recopié de la preuve fusionnée de Sidorenko pour les cycles pairs (PR #641), vecteur test
-- unitaire quelconque.
private theorem symTrace17 {N k : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (v : Fin N → ℝ) (hvv : v ⬝ᵥ v = 1) :
    (v ⬝ᵥ (A.mulVec v)) ^ (2 * k) ≤ (A ^ (2 * k)).trace := by
  let U := hA.eigenvectorUnitary
  let ev : Fin N → ℝ := hA.eigenvalues
  have hspec : A = (U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal ev *
      star (U : Matrix (Fin N) (Fin N) ℝ) := by
    have h := hA.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, U, ev] using h
  have hpow : A ^ (2 * k) =
      Unitary.conjStarAlgAut ℝ _ U (Matrix.diagonal (fun i => ev i ^ (2 * k))) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_pow, Matrix.diagonal_pow]
    rfl
  have htr : (A ^ (2 * k)).trace = ∑ i : Fin N, ev i ^ (2 * k) := by
    rw [hpow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
    have hUU : star (U : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
      Unitary.coe_star_mul_self U
    rw [hUU, one_mul, Matrix.trace_diagonal]
  let w : Fin N → ℝ := (star (U : Matrix (Fin N) (Fin N) ℝ)).mulVec v
  have hstar_tr : star (U : Matrix (Fin N) (Fin N) ℝ) =
      Matrix.transpose (U : Matrix (Fin N) (Fin N) ℝ) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hww : ∑ i : Fin N, w i ^ 2 = 1 := by
    have hdot : w ⬝ᵥ w = 1 := by
      dsimp only [w]
      rw [Matrix.dotProduct_mulVec, hstar_tr, Matrix.vecMul_transpose,
        ← hstar_tr, Matrix.mulVec_mulVec]
      have hUU : (U : Matrix (Fin N) (Fin N) ℝ) * star (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
        Unitary.coe_mul_star_self U
      rw [hUU, Matrix.one_mulVec, hvv]
    simpa [dotProduct, sq] using hdot
  have hquad_rhs : v ⬝ᵥ (A.mulVec v) = ∑ i : Fin N, w i ^ 2 * ev i := by
    rw [hspec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    have hvU : Matrix.vecMul v (U : Matrix (Fin N) (Fin N) ℝ) = w := by
      dsimp only [w]
      rw [hstar_tr, Matrix.mulVec_transpose]
    rw [hvU]
    change w ⬝ᵥ ((Matrix.diagonal ev).mulVec w) = _
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 * k)) :=
    (even_two_mul k).convexOn_pow
  have hjensen := hconv.map_sum_le (t := Finset.univ) (w := fun i => w i ^ 2) (p := ev)
    (fun i _ => sq_nonneg (w i)) hww (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hjensen
  have hle_tr : ∑ i : Fin N, w i ^ 2 * ev i ^ (2 * k) ≤ ∑ i : Fin N, ev i ^ (2 * k) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hw_le : w i ^ 2 ≤ 1 := by
      rw [← hww]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
    have hev_nn : 0 ≤ ev i ^ (2 * k) := (even_two_mul k).pow_nonneg (ev i)
    nlinarith
  rw [hquad_rhs, htr]
  exact le_trans hjensen hle_tr

/- ## À prouver -/

/-- Cycles homomorphes pondérés en conflit depuis la position 0 : version matrice de
`conflictA_le`. `R` borne les sommes de lignes, `s` la masse `∑_a [r e a] M b a`. -/
theorem conflictM_le {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u) (r : W → W → Prop) (hr : ∀ u w, r u w → r w u)
    (s R : ℝ) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hmass : ∀ b e, ∑ a, (if r e a then M b a else 0) ≤ s)
    (hrow : ∀ a, ∑ b, M a b ≤ R) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W,
        (if ∃ j : Fin (2 * k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (x ⟨0, by omega⟩) (x j)
          then cycW M x else 0) ≤
      Real.sqrt (k * s * R * trace (M ^ (2 * (k - 1))) * trace (M ^ (2 * k))) := by
  classical
  have _hsR := mul_nonneg hs hR
  let X := Fin (2*k) → W
  let P := fun n : ℕ => M^n
  let a := fun x : X => x ⟨0,by omega⟩
  let b := fun x : X => x ⟨1,by omega⟩
  let c := fun x : X => x ⟨k+1,by omega⟩
  let hit := fun x : X =>
    ∃ j : Fin (2*k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (a x) (x j)
  let T := fun x : X => @ite ℝ (hit x) (Classical.propDecidable _) (cycW M x) 0
  let A := fun x : X => (P (k-1)) (a x) (c x)
  let B := fun x : X => (P k) (b x) (c x)
  have hn := Matrix.pow_apply_nonneg hM
  have hA (x : X) : 0 ≤ A x := hn _ _ _
  have hB (x : X) : 0 ≤ B x := hn _ _ _
  let idx := fun p : Fin k => (⟨p.val+1,by omega⟩ : Fin (2*k))
  let term := fun (x : X) (p : Fin k) =>
    cycW M x * (if r (a x) (x (idx p)) then B x / A x else 0)
  have hterm (x p) : 0 ≤ term x p := by
    apply mul_nonneg (cwNonneg17 M hM x)
    split
    · exact div_nonneg (hB x) (hA x)
    · rfl
  have hsecond : ∑ x, T x * (B x / A x) ≤ (k:ℝ) * (s * trace (P (2*k))) := by
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
      _ ≤ ∑ _p : Fin k, s * trace (P (2*k)) := by
        apply sum_le_sum
        intro p _
        exact upperOne17 M hM hsym r hr s hmass k (p.val+1) hk (by omega) (by omega)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ = ∑ x : X, T x := by
      apply sum_congr rfl
      intro x _
      by_cases h : hit x <;> simp only [T, hit, a] at h ⊢ <;> simp [h]
    _ ≤ _ := cs17 M hM hsym R hrow k hk hit ((k:ℝ) * (s * trace (M ^ (2*k)))) hsecond
    _ = _ := congrArg Real.sqrt (by ring)

/-- Sidorenko pour les cycles pairs, matrice symétrique portée par `S × S` : vecteur test
`1_S / √|S|` au lieu de `1 / √N`. -/
theorem sidorenko_supp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ u v, M u v = M v u)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hsupp : ∀ u v, M u v ≠ 0 → u ∈ S ∧ v ∈ S)
    (m : ℕ) :
    ((∑ a, ∑ b, M a b) / (#S : ℝ)) ^ (2 * m) ≤ trace (M ^ (2 * m)) := by
  have hSpos : (0:ℝ) < #S := by exact_mod_cast hS.card_pos
  have hA : M.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext a b
    exact hsym b a
  have hsq : Real.sqrt (#S : ℝ) ^ 2 = #S := Real.sq_sqrt hSpos.le
  have hsq_ne : Real.sqrt (#S : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hSpos).ne'
  let v : Fin n → ℝ := fun a => if a ∈ S then 1 / Real.sqrt (#S : ℝ) else 0
  have hvv : v ⬝ᵥ v = 1 := by
    have hterm (a : Fin n) : v a * v a = if a ∈ S then 1 / (#S : ℝ) else 0 := by
      by_cases ha : a ∈ S
      · simp only [v, if_pos ha]
        field_simp
        rw [hsq]
      · simp [v, ha]
    simp only [dotProduct, hterm, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    field_simp
  have hquad : v ⬝ᵥ (M.mulVec v) = (∑ a, ∑ b, M a b) / (#S : ℝ) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : M a b = 0
    · simp [h]
    · obtain ⟨ha, hb⟩ := hsupp a b h
      simp only [v, if_pos ha, if_pos hb]
      field_simp
      rw [hsq]
  have h := symTrace17 (k := m) M hA v hvv
  rwa [hquad] at h

/-- Les traces paires d'une matrice symétrique positive non nulle sont strictement positives. -/
theorem trace_pos_M {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u) (hpos : ∃ u v, 0 < M u v) (k : ℕ) :
    0 < trace (M ^ (2 * k)) := by
  obtain ⟨u, v, huv⟩ := hpos
  have hn := Matrix.pow_apply_nonneg hM
  have h₂ : 0 < (M ^ 2) u u := by
    rw [sq, Matrix.mul_apply]
    calc
      0 < M u v * M v u := by rw [← hsym u v]; exact mul_pos huv huv
      _ ≤ _ := single_le_sum (fun z _ => mul_nonneg (hM u z) (hM z u)) (mem_univ v)
  have hdiag : 0 < (M ^ (2 * k)) u u := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, pow_add, Matrix.mul_apply]
      calc
        0 < (M ^ (2 * k)) u u * (M ^ 2) u u := mul_pos ih h₂
        _ ≤ _ := single_le_sum (fun z _ => mul_nonneg (hn _ u z) (hn 2 z u)) (mem_univ u)
  exact hdiag.trans_le (single_le_sum (fun z _ => hn (2 * k) z z) (mem_univ u))

/-- Log-convexité des traces paires, avec `T_0 = |W|` : version matrice de
`trace_adjR_interp`. -/
theorem trace_interp_M {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u) (hpos : ∃ u v, 0 < M u v) (k : ℕ) (hk : 1 ≤ k) :
    trace (M ^ (2 * (k - 1))) ≤
      (Fintype.card W : ℝ) ^ (1 / (k : ℝ)) * trace (M ^ (2 * k)) ^ (1 - 1 / (k : ℝ)) := by
  let T (n : ℕ) := trace (M ^ (2 * n))
  have pos (n : ℕ) : 0 < T n := trace_pos_M M hM hsym hpos n
  let a (n : ℕ) := Real.log (T n)
  have step (n : ℕ) : a (n + 1) - a n ≤ a (n + 2) - a (n + 1) := by
    have h : T (n + 1) ^ 2 ≤ T n * T (n + 2) := by
      simpa [T] using logConvex17 M hM hsym (n + 1) (by omega)
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
  apply (Real.log_le_log_iff (pos _) (mul_pos (Real.rpow_pos_of_pos (pos _) _)
    (Real.rpow_pos_of_pos (pos _) _))).mp
  rw [Real.log_mul (Real.rpow_pos_of_pos (pos _) _).ne' (Real.rpow_pos_of_pos (pos _) _).ne',
    Real.log_rpow (pos _), Real.log_rpow (pos _)]
  change a n ≤ 1 / ((n + 1 : ℕ) : ℝ) * a 0 + (1 - 1 / ((n + 1 : ℕ) : ℝ)) * a (n + 1)
  push_cast
  field_simp
  linarith [bound n]

/- ## Lemme 18 : auxiliaires -/

/-- Tiroirs : une fibre porte au moins la part moyenne. -/
theorem pigeon18 {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Nonempty) :
    ∃ y ∈ t, #s ≤ #t * #(s.filter fun a => f a = y) := by
  obtain ⟨y, hy, hmax⟩ := t.exists_max_image (fun y => #(s.filter fun a => f a = y)) ht
  refine ⟨y, hy, ?_⟩
  rw [card_eq_sum_card_fiberwise (by intro a ha; exact hf a ha)]
  calc _ ≤ ∑ _b ∈ t, #(s.filter fun a => f a = y) := sum_le_sum hmax
    _ = _ := by rw [sum_const, smul_eq_mul]

/-- Un ensemble de triplets stable par `(x, y, z) ↦ (z, y, x)` a des multiplicités symétriques. -/
theorem swapCard18 {α : Type*} [DecidableEq α] (D : Finset (α × α × α))
    (hD : ∀ p ∈ D, (p.2.2, p.2.1, p.1) ∈ D) (a b : α) :
    #(D.filter fun q => q.1 = a ∧ q.2.2 = b) ≤ #(D.filter fun q => q.1 = b ∧ q.2.2 = a) := by
  apply card_le_card_of_injOn (fun q => (q.2.2, q.2.1, q.1))
  · intro q hq
    obtain ⟨hqD, h1, h2⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨hD q hqD, h2, h1⟩
  · rintro ⟨x, y, z⟩ _ ⟨x', y', z'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl

/- ## Lemme 18 : choix de `v`, `s`, `s'` et de l'ensemble de triplets `D` (étapes A et B) -/

/-- Lemme 2.17 de l'article sans symétrisation, puis une classe dyadique des multiplicités
`h(x,z) = hmat D x z`. `Δ` borne les degrés, `U` le nombre de 4-cycles étiquetés par arête. -/
theorem stepAB {n : ℕ} (G : SimpleGraph (Fin n)) (Δ U : ℝ)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ)
    (hU : ∀ e ∈ G.edgeFinset,
      (#(((univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter fun t =>
          G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
            t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2).filter fun t =>
          e = s(t.1, t.2.1) ∨ e = s(t.2.1, t.2.2.1) ∨ e = s(t.2.2.1, t.2.2.2) ∨
            e = s(t.2.2.2, t.1)) : ℝ) ≤ U)
    (hQ : 0 < #((univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter fun t =>
          G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
            t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2)) :
    ∃ (v : Fin n) (s s' : ℝ) (D : Finset (Fin n × Fin n × Fin n)),
      0 < s ∧ s ≤ 2 * Δ ∧ 0 < s' ∧
      (#((univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter fun t =>
          G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
            t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2) : ℝ) ≤
        2 * n * ((Nat.log 2 n : ℝ) + 1) ^ 2 * #D ∧
      (∀ t ∈ D, G.Adj v t.1 ∧ G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧
        (#(G.neighborFinset v ∩ G.neighborFinset t.2.1) : ℝ) ≤ s ∧
        (#(G.neighborFinset t.1 ∩ G.neighborFinset t.2.2) : ℝ) ≤ s) ∧
      (∀ t ∈ D, (t.2.2, t.2.1, t.1) ∈ D) ∧
      (∀ t ∈ D, s' ≤ hmat D t.1 t.2.2) ∧
      (#D : ℝ) ≤ 2 * s' * Δ ^ 2 ∧
      (∀ a b, hmat D a b ≤ s) ∧
      (∀ a, (#(rowSet D a) : ℝ) ≤ U) ∧
      (∀ a, (#(extSet D a) : ℝ) * s ≤ 4 * U) := by
  classical
  set c4 : Finset (Fin n × Fin n × Fin n × Fin n) :=
    (univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter fun t =>
      G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
        t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 with hc4
  have mem4 : ∀ t, t ∈ c4 ↔ (G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧
      G.Adj t.2.2.2 t.1 ∧ t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2) := fun t => by
    rw [hc4, mem_filter]; exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  obtain ⟨d, hd⟩ : ∃ d : Fin n → Fin n → ℕ,
      ∀ a b, d a b = #(G.neighborFinset a ∩ G.neighborFinset b) := ⟨_, fun _ _ => rfl⟩
  have dsymm : ∀ a b, d a b = d b a := fun a b => by rw [hd, hd, inter_comm]
  have ddeg : ∀ a b, d a b ≤ G.degree a := fun a b => by
    rw [hd, ← card_neighborFinset_eq_degree]; exact card_le_card inter_subset_left
  have dn : ∀ a b, d a b ≤ n := fun a b => by
    rw [hd]; exact (card_le_univ _).trans (by rw [Fintype.card_fin])
  obtain ⟨t0, ht0⟩ := card_pos.mp hQ
  have hU0 : 0 ≤ U :=
    le_trans (Nat.cast_nonneg _) (hU _ (G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr ((mem4 t0).mp ht0).1)))
  -- Étape 1 : la rotation `(a,b,c,d) ↦ (b,c,d,a)`.
  obtain ⟨c4', hc4', h1⟩ : ∃ c4' : Finset (Fin n × Fin n × Fin n × Fin n),
      (∀ t, t ∈ c4' ↔ t ∈ c4 ∧ d t.2.1 t.2.2.2 ≤ d t.1 t.2.2.1) ∧ #c4 ≤ 2 * #c4' := by
    refine ⟨c4.filter fun t => d t.2.1 t.2.2.2 ≤ d t.1 t.2.2.1, fun t => mem_filter, ?_⟩
    have hsplit := card_filter_add_card_filter_not (s := c4)
      (fun t => d t.2.1 t.2.2.2 ≤ d t.1 t.2.2.1)
    have hrot : #(c4.filter fun t => ¬ d t.2.1 t.2.2.2 ≤ d t.1 t.2.2.1) ≤
        #(c4.filter fun t => d t.2.1 t.2.2.2 ≤ d t.1 t.2.2.1) := by
      apply card_le_card_of_injOn (fun t => (t.2.1, t.2.2.1, t.2.2.2, t.1))
      · intro t ht
        obtain ⟨htc, hlt⟩ := mem_filter.mp ht
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (mem4 t).mp htc
        refine mem_filter.mpr ⟨(mem4 _).mpr ⟨h2, h3, h4, h1, h6, fun h => h5 h.symm⟩, ?_⟩
        show d t.2.2.1 t.1 ≤ d t.2.1 t.2.2.2
        rw [dsymm t.2.2.1 t.1]
        omega
      · rintro ⟨a, b, c, e⟩ _ ⟨a', b', c', e'⟩ _ h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        rfl
    omega
  -- Étape 2 : tiroirs sur `v = t.1`.
  have hn0 : (univ : Finset (Fin n)).Nonempty := ⟨t0.1, mem_univ _⟩
  obtain ⟨v, -, hv⟩ : ∃ v ∈ (univ : Finset (Fin n)),
      #c4' ≤ #(univ : Finset (Fin n)) * #(c4'.filter fun t => t.1 = v) :=
    pigeon18 c4' univ (fun t => t.1) (fun _ _ => mem_univ _) hn0
  rw [card_univ, Fintype.card_fin] at hv
  -- Étape 3 : tiroirs sur `j = Nat.log 2 (d v y)`.
  obtain ⟨j, -, hj⟩ : ∃ j ∈ range (Nat.log 2 n + 1),
      #(c4'.filter fun t => t.1 = v) ≤ #(range (Nat.log 2 n + 1)) *
        #((c4'.filter fun t => t.1 = v).filter fun t => Nat.log 2 (d v t.2.2.1) = j) := by
    refine pigeon18 (c4'.filter fun t => t.1 = v) (range (Nat.log 2 n + 1))
      (fun t => Nat.log 2 (d v t.2.2.1))
      (fun t _ => ?_) nonempty_range_add_one
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (dn _ _)))
  rw [card_range] at hj
  obtain ⟨D₀, hD₀, hAD⟩ : ∃ D₀ : Finset (Fin n × Fin n × Fin n),
      (∀ p, p ∈ D₀ ↔ (G.Adj v p.1 ∧ G.Adj p.1 p.2.1 ∧ G.Adj p.2.1 p.2.2 ∧ G.Adj p.2.2 v ∧
        v ≠ p.2.1 ∧ p.1 ≠ p.2.2) ∧ d p.1 p.2.2 ≤ d v p.2.1 ∧ Nat.log 2 (d v p.2.1) = j) ∧
      #((c4'.filter fun t => t.1 = v).filter fun t => Nat.log 2 (d v t.2.2.1) = j) ≤ #D₀ := by
    refine ⟨univ.filter fun p => (G.Adj v p.1 ∧ G.Adj p.1 p.2.1 ∧ G.Adj p.2.1 p.2.2 ∧
        G.Adj p.2.2 v ∧ v ≠ p.2.1 ∧ p.1 ≠ p.2.2) ∧ d p.1 p.2.2 ≤ d v p.2.1 ∧
        Nat.log 2 (d v p.2.1) = j,
      fun p => by rw [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩, ?_⟩
    apply card_le_card_of_injOn (fun t => t.2)
    · intro t ht
      obtain ⟨htA, hlog⟩ := mem_filter.mp ht
      obtain ⟨htc', ht1⟩ := mem_filter.mp htA
      obtain ⟨htc, hle⟩ := (hc4' t).mp htc'
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (mem4 t).mp htc
      rw [ht1] at h1 h4 h5 hle
      exact mem_filter.mpr ⟨mem_univ _, ⟨h1, h2, h3, h4, h5, h6⟩, hle, hlog⟩
    · intro t ht t' ht' h
      have e1 := (mem_filter.mp (mem_filter.mp ht).1).2
      have e2 := (mem_filter.mp (mem_filter.mp ht').1).2
      exact Prod.ext (e1.trans e2.symm) h
  -- Étape 4 : tiroirs sur `j' = Nat.log 2 (h(x,z))`.
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : Fin n → Fin n → ℕ,
      ∀ a b, h₀ a b = #(D₀.filter fun q => q.1 = a ∧ q.2.2 = b) := ⟨_, fun _ _ => rfl⟩
  have h0n : ∀ a b, h₀ a b ≤ n := by
    intro a b
    rw [hh₀]
    calc _ ≤ #(univ : Finset (Fin n)) := by
          apply card_le_card_of_injOn (fun q => q.2.1) (by intro q _; exact mem_univ _)
          intro q hq q' hq' h
          obtain ⟨-, hq1, hq2⟩ := mem_filter.mp hq
          obtain ⟨-, hq1', hq2'⟩ := mem_filter.mp hq'
          exact Prod.ext (hq1.trans hq1'.symm) (Prod.ext h (hq2.trans hq2'.symm))
      _ = n := by rw [card_univ, Fintype.card_fin]
  obtain ⟨j', -, hj'⟩ : ∃ j' ∈ range (Nat.log 2 n + 1), #D₀ ≤ #(range (Nat.log 2 n + 1)) *
      #(D₀.filter fun p => Nat.log 2 (h₀ p.1 p.2.2) = j') := by
    refine pigeon18 D₀ _ (fun p => Nat.log 2 (h₀ p.1 p.2.2)) (fun p _ => ?_) nonempty_range_add_one
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (h0n _ _)))
  rw [card_range] at hj'
  obtain ⟨D, hD, hDc⟩ : ∃ D : Finset (Fin n × Fin n × Fin n),
      (∀ p, p ∈ D ↔ p ∈ D₀ ∧ Nat.log 2 (h₀ p.1 p.2.2) = j') ∧
      #D₀ ≤ (Nat.log 2 n + 1) * #D := ⟨_, fun p => mem_filter, hj'⟩
  -- La borne de comptage.
  have hbig : #c4 ≤ 2 * n * (Nat.log 2 n + 1) ^ 2 * #D := by
    calc #c4 ≤ 2 * #c4' := h1
      _ ≤ 2 * (n * #(c4'.filter fun t => t.1 = v)) := Nat.mul_le_mul_left _ hv
      _ ≤ 2 * (n * ((Nat.log 2 n + 1) *
            #((c4'.filter fun t => t.1 = v).filter fun t => Nat.log 2 (d v t.2.2.1) = j))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hj)
      _ ≤ 2 * (n * ((Nat.log 2 n + 1) * #D₀)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hAD))
      _ ≤ 2 * (n * ((Nat.log 2 n + 1) * ((Nat.log 2 n + 1) * #D))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hDc))
      _ = 2 * n * (Nat.log 2 n + 1) ^ 2 * #D := by ring
  have hDpos : 0 < #D := by
    rcases Nat.eq_zero_or_pos #D with h | h
    · rw [h, mul_zero] at hbig; omega
    · exact h
  obtain ⟨t₀, ht₀⟩ := card_pos.mp hDpos
  -- Faits sur `D₀`, `h₀` et `D`.
  have hDsub : ∀ p ∈ D, p ∈ D₀ := fun p hp => ((hD p).mp hp).1
  have hD0f : ∀ p ∈ D₀, 2 ≤ d v p.2.1 ∧ 2 ^ j ≤ d v p.2.1 ∧ d v p.2.1 < 2 ^ (j + 1) ∧
      d p.1 p.2.2 < 2 ^ (j + 1) := by
    intro p hp
    obtain ⟨⟨h1, h2, h3, h4, -, h6⟩, hle, hlog⟩ := (hD₀ p).mp hp
    have h2le : 2 ≤ d v p.2.1 := by
      rw [hd, ← card_pair h6]
      apply card_le_card
      intro x hx
      rw [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1,
          (G.mem_neighborFinset _ _).mpr h2.symm⟩
      · exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h4.symm,
          (G.mem_neighborFinset _ _).mpr h3⟩
    have hlo := Nat.pow_log_le_self 2 (show d v p.2.1 ≠ 0 by omega)
    have hhi := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (d v p.2.1)
    rw [hlog] at hlo hhi
    exact ⟨h2le, hlo, hhi, lt_of_le_of_lt hle hhi⟩
  have hD0sym : ∀ p ∈ D₀, (p.2.2, p.2.1, p.1) ∈ D₀ := by
    intro p hp
    obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hle, hlog⟩ := (hD₀ p).mp hp
    exact (hD₀ _).mpr ⟨⟨h4.symm, h3.symm, h2.symm, h1.symm, h5, fun h => h6 h.symm⟩,
      (dsymm p.2.2 p.1).trans_le hle, hlog⟩
  have h0sym : ∀ a b, h₀ a b = h₀ b a := fun a b => by
    rw [hh₀, hh₀]
    exact le_antisymm (swapCard18 D₀ hD0sym a b) (swapCard18 D₀ hD0sym b a)
  have hfibD : ∀ p ∈ D, h₀ p.1 p.2.2 ≤ #(D.filter fun q => q.1 = p.1 ∧ q.2.2 = p.2.2) := by
    intro p hp
    rw [hh₀]
    apply card_le_card
    intro q hq
    obtain ⟨hqD, hq1, hq2⟩ := mem_filter.mp hq
    refine mem_filter.mpr ⟨(hD q).mpr ⟨hqD, ?_⟩, hq1, hq2⟩
    rw [hq1, hq2]; exact ((hD p).mp hp).2
  have hfibD' : ∀ a b, #(D.filter fun q => q.1 = a ∧ q.2.2 = b) ≤ h₀ a b := by
    intro a b
    rw [hh₀]
    apply card_le_card
    intro q hq
    obtain ⟨hqD, hq1, hq2⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨hDsub q hqD, hq1, hq2⟩
  have hDcls : ∀ p ∈ D, 2 ^ j' ≤ h₀ p.1 p.2.2 ∧ h₀ p.1 p.2.2 < 2 ^ (j' + 1) := by
    intro p hp
    obtain ⟨hp0, hlog⟩ := (hD p).mp hp
    have hne : h₀ p.1 p.2.2 ≠ 0 := by
      rw [hh₀]; exact (card_pos.mpr ⟨p, mem_filter.mpr ⟨hp0, rfl, rfl⟩⟩).ne'
    have hlo := Nat.pow_log_le_self 2 hne
    have hhi := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (h₀ p.1 p.2.2)
    rw [hlog] at hlo hhi
    exact ⟨hlo, hhi⟩
  have hmatE : ∀ a b, hmat D a b = (#(D.filter fun q => q.1 = a ∧ q.2.2 = b) : ℝ) := by
    intro a b
    simp only [hmat]
    congr 2
    ext q
    simp only [mem_filter]
  have memR : ∀ a q, q ∈ rowSet D a ↔ q ∈ D ∧ q.1 = a := by
    intro a q
    simp only [rowSet, mem_filter]
  have memE : ∀ a y, y ∈ extSet D a ↔ ∃ q ∈ D, q.1 = a ∧ q.2.1 = y := by
    intro a y
    simp only [extSet, rowSet, mem_image, mem_filter, and_assoc]
  refine ⟨v, 2 ^ (j + 1), 2 ^ j', D, by positivity, ?_, by positivity, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- `s ≤ 2Δ`
    obtain ⟨-, hlo, -, -⟩ := hD0f t₀ (hDsub t₀ ht₀)
    have e1 : (2 : ℝ) ^ j ≤ d v t₀.2.1 := by exact_mod_cast hlo
    have e2 : (d v t₀.2.1 : ℝ) ≤ G.degree v := by exact_mod_cast ddeg _ _
    rw [pow_succ]
    linarith [hdeg v]
  · -- la borne de comptage
    exact_mod_cast hbig
  · -- adjacences et codegrés
    intro t ht
    obtain ⟨⟨h1, h2, h3, -, -, -⟩, -, -⟩ := (hD₀ t).mp (hDsub t ht)
    obtain ⟨-, -, hhi, hhi'⟩ := hD0f t (hDsub t ht)
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · rw [← hd]; exact_mod_cast hhi.le
    · rw [← hd]; exact_mod_cast hhi'.le
  · -- symétrie
    intro t ht
    obtain ⟨ht0, hlog⟩ := (hD t).mp ht
    refine (hD _).mpr ⟨hD0sym t ht0, ?_⟩
    show Nat.log 2 (h₀ t.2.2 t.1) = j'
    rw [h0sym]; exact hlog
  · -- `s' ≤ hmat D t.1 t.2.2`
    intro t ht
    rw [hmatE]
    exact_mod_cast (hDcls t ht).1.trans (hfibD t ht)
  · -- `#D ≤ 2 s' Δ²`
    have hmaps : ∀ q ∈ D, (q.1, q.2.2) ∈ G.neighborFinset v ×ˢ G.neighborFinset v := by
      intro q hq
      obtain ⟨⟨h1, -, -, h4, -, -⟩, -, -⟩ := (hD₀ q).mp (hDsub q hq)
      exact mem_product.mpr ⟨(G.mem_neighborFinset _ _).mpr h1,
        (G.mem_neighborFinset _ _).mpr h4.symm⟩
    have hcard : #D ≤ #(G.neighborFinset v ×ˢ G.neighborFinset v) * 2 ^ (j' + 1) := by
      rw [card_eq_sum_card_fiberwise (f := fun q => (q.1, q.2.2))
        (by intro q hq; exact hmaps q hq)]
      refine (sum_le_card_nsmul _ _ _ ?_).trans (by rw [smul_eq_mul])
      rintro ⟨a, b⟩ -
      rcases (D.filter fun q => (q.1, q.2.2) = (a, b)).eq_empty_or_nonempty with he | ⟨p, hp⟩
      · rw [he, card_empty]; exact Nat.zero_le _
      · obtain ⟨hpD, hpab⟩ := mem_filter.mp hp
        simp only [Prod.mk.injEq] at hpab
        obtain ⟨rfl, rfl⟩ := hpab
        refine le_trans ?_ (hDcls p hpD).2.le
        refine le_trans ?_ (hfibD' p.1 p.2.2)
        apply card_le_card
        intro q hq
        obtain ⟨hqD, hq'⟩ := mem_filter.mp hq
        simp only [Prod.mk.injEq] at hq'
        exact mem_filter.mpr ⟨hqD, hq'⟩
    rw [card_product, card_neighborFinset_eq_degree] at hcard
    have hc : (#D : ℝ) ≤ (G.degree v : ℝ) * G.degree v * 2 ^ (j' + 1) := by
      exact_mod_cast hcard
    have hd0 : (0 : ℝ) ≤ G.degree v := Nat.cast_nonneg _
    have hdv := hdeg v
    have hsq : (G.degree v : ℝ) * G.degree v ≤ Δ ^ 2 := by nlinarith
    calc (#D : ℝ) ≤ (G.degree v : ℝ) * G.degree v * 2 ^ (j' + 1) := hc
      _ ≤ Δ ^ 2 * 2 ^ (j' + 1) := mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = 2 * 2 ^ j' * Δ ^ 2 := by ring
  · -- `hmat D a b ≤ s`
    intro a b
    rw [hmatE]
    rcases (D.filter fun q => q.1 = a ∧ q.2.2 = b).eq_empty_or_nonempty with he | ⟨p, hp⟩
    · rw [he, card_empty, Nat.cast_zero]; positivity
    · obtain ⟨hpD, rfl, rfl⟩ := mem_filter.mp hp
      have hcd : #(D.filter fun q => q.1 = p.1 ∧ q.2.2 = p.2.2) ≤ d p.1 p.2.2 := by
        rw [hd]
        apply card_le_card_of_injOn (fun q => q.2.1)
        · intro q hq
          obtain ⟨hqD, hq1, hq2⟩ := mem_filter.mp hq
          obtain ⟨⟨-, h2, h3, -, -, -⟩, -, -⟩ := (hD₀ q).mp (hDsub q hqD)
          rw [← hq1, ← hq2]
          exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h2,
            (G.mem_neighborFinset _ _).mpr h3.symm⟩
        · intro q hq q' hq' h
          obtain ⟨-, hq1, hq2⟩ := mem_filter.mp hq
          obtain ⟨-, hq1', hq2'⟩ := mem_filter.mp hq'
          exact Prod.ext (hq1.trans hq1'.symm) (Prod.ext h (hq2.trans hq2'.symm))
      exact_mod_cast hcd.trans (hD0f p (hDsub p hpD)).2.2.2.le
  · -- `#(rowSet D a) ≤ U`
    intro a
    rcases (rowSet D a).eq_empty_or_nonempty with he | ⟨p, hp⟩
    · rw [he, card_empty, Nat.cast_zero]; exact hU0
    · obtain ⟨hpD, rfl⟩ := (memR a p).mp hp
      obtain ⟨⟨hva, -, -, -, -, -⟩, -, -⟩ := (hD₀ p).mp (hDsub p hpD)
      refine le_trans (Nat.cast_le.mpr (card_le_card_of_injOn
        (fun q => (v, q.1, q.2.1, q.2.2)) ?_ ?_)) (hU _ (G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hva)))
      · intro q hq
        obtain ⟨hqD, hq1⟩ := (memR _ q).mp hq
        obtain ⟨hc, -, -⟩ := (hD₀ q).mp (hDsub q hqD)
        refine mem_filter.mpr ⟨(mem4 _).mpr hc, Or.inl ?_⟩
        show s(v, p.1) = s(v, q.1)
        rw [hq1]
      · intro q _ q' _ h
        have e1 : q.1 = q'.1 := congrArg (fun t => t.2.1) h
        have e2 : q.2.1 = q'.2.1 := congrArg (fun t => t.2.2.1) h
        have e3 : q.2.2 = q'.2.2 := congrArg (fun t => t.2.2.2) h
        exact Prod.ext e1 (Prod.ext e2 e3)
  · -- `#(extSet D a) * s ≤ 4U`
    intro a
    rcases (extSet D a).eq_empty_or_nonempty with he | ⟨y₀, hy₀⟩
    · rw [he, card_empty, Nat.cast_zero, zero_mul]; linarith
    · obtain ⟨p, hpD, rfl, -⟩ := (memE a y₀).mp hy₀
      obtain ⟨⟨hva, -, -, -, -, -⟩, -, -⟩ := (hD₀ p).mp (hDsub p hpD)
      have hW : ∀ y ∈ extSet D p.1, (2 : ℝ) ^ (j + 1) / 4 ≤
          #((G.neighborFinset v ∩ G.neighborFinset y).erase p.1) := by
        intro y hy
        obtain ⟨q, hqD, hq1, rfl⟩ := (memE _ y).mp hy
        obtain ⟨⟨h1, h2, -, -, -, -⟩, -, -⟩ := (hD₀ q).mp (hDsub q hqD)
        obtain ⟨h2le, hlo, -, -⟩ := hD0f q (hDsub q hqD)
        have hmem : p.1 ∈ G.neighborFinset v ∩ G.neighborFinset q.2.1 := by
          rw [← hq1]
          exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1,
            (G.mem_neighborFinset _ _).mpr h2.symm⟩
        rw [cast_card_erase_of_mem hmem, ← hd]
        have e1 : (2 : ℝ) ^ j ≤ d v q.2.1 := by exact_mod_cast hlo
        have e2 : (2 : ℝ) ≤ d v q.2.1 := by exact_mod_cast h2le
        rw [pow_succ]
        linarith
      have hS : (#((extSet D p.1).sigma fun y =>
          (G.neighborFinset v ∩ G.neighborFinset y).erase p.1) : ℝ) ≤ U := by
        refine le_trans (Nat.cast_le.mpr (card_le_card_of_injOn
          (fun r : (Σ _ : Fin n, Fin n) => (v, p.1, r.1, r.2)) ?_ ?_))
          (hU _ (G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hva)))
        · rintro ⟨y, w⟩ hr
          obtain ⟨hy, hw⟩ := mem_sigma.mp hr
          obtain ⟨hwa, hw'⟩ := mem_erase.mp hw
          obtain ⟨hvw, hyw⟩ := mem_inter.mp hw'
          obtain ⟨q, hqD, hq1, rfl⟩ := (memE _ y).mp hy
          obtain ⟨⟨-, h2, -, -, h5, -⟩, -, -⟩ := (hD₀ q).mp (hDsub q hqD)
          refine mem_filter.mpr ⟨(mem4 _).mpr ⟨hva, ?_, (G.mem_neighborFinset _ _).mp hyw,
            ((G.mem_neighborFinset _ _).mp hvw).symm, h5, fun h => hwa h.symm⟩, Or.inl rfl⟩
          show G.Adj p.1 q.2.1
          rw [← hq1]; exact h2
        · rintro ⟨y, w⟩ _ ⟨y', w'⟩ _ h
          have e1 : y = y' := congrArg (fun t => t.2.2.1) h
          have e2 : w = w' := congrArg (fun t => t.2.2.2) h
          subst e1; subst e2; rfl
      have hsum : (#(extSet D p.1) : ℝ) * ((2 : ℝ) ^ (j + 1) / 4) ≤ U := by
        calc (#(extSet D p.1) : ℝ) * ((2 : ℝ) ^ (j + 1) / 4)
            = ∑ _y ∈ extSet D p.1, (2 : ℝ) ^ (j + 1) / 4 := by
              rw [sum_const, nsmul_eq_mul]
          _ ≤ ∑ y ∈ extSet D p.1,
              (#((G.neighborFinset v ∩ G.neighborFinset y).erase p.1) : ℝ) := sum_le_sum hW
          _ = (#((extSet D p.1).sigma fun y =>
              (G.neighborFinset v ∩ G.neighborFinset y).erase p.1) : ℝ) := by
              rw [card_sigma, Nat.cast_sum]
          _ ≤ U := hS
      calc (#(extSet D p.1) : ℝ) * 2 ^ (j + 1)
          = 4 * ((#(extSet D p.1) : ℝ) * ((2 : ℝ) ^ (j + 1) / 4)) := by ring
        _ ≤ 4 * U := by linarith

/- ## Lemme 19 : la matrice `hmat D` et le comptage des cycles (étape C) -/

theorem hmat_nonneg {W : Type} [Fintype W] (D : Finset (W × W × W)) (a b : W) :
    0 ≤ hmat D a b := by
  unfold hmat
  positivity

theorem hmat_symm {W : Type} [Fintype W] (D : Finset (W × W × W))
    (hsymm : ∀ t ∈ D, (t.2.2, t.2.1, t.1) ∈ D) (a b : W) :
    hmat D a b = hmat D b a := by
  unfold hmat
  congr 1
  apply Finset.card_nbij' (fun t => (t.2.2, t.2.1, t.1)) (fun t => (t.2.2, t.2.1, t.1))
  · intro t ht
    simp only [mem_coe, mem_filter] at ht ⊢
    exact ⟨hsymm t ht.1, ht.2.2, ht.2.1⟩
  · intro t ht
    simp only [mem_coe, mem_filter] at ht ⊢
    exact ⟨hsymm t ht.1, ht.2.2, ht.2.1⟩
  · intro t _
    rfl
  · intro t _
    rfl

private theorem hmat_row19 {W : Type} [Fintype W] (D : Finset (W × W × W)) (a : W) :
    ∑ b, hmat D a b = #(rowSet D a) := by
  unfold hmat rowSet
  rw [← Nat.cast_sum, card_eq_sum_card_fiberwise (f := fun t => t.2.2) (t := univ)
    (fun _ _ => mem_univ _)]
  push_cast
  refine sum_congr rfl fun b _ => ?_
  rw [filter_filter]

theorem hmat_sum {W : Type} [Fintype W] (D : Finset (W × W × W)) :
    ∑ a, ∑ b, hmat D a b = #D := by
  rw [sum_congr rfl fun a _ => hmat_row19 D a, ← Nat.cast_sum,
    card_eq_sum_card_fiberwise (s := D) (f := fun t => t.1) (t := univ) (fun _ _ => mem_univ _)]
  rfl

theorem hmat_row {W : Type} [Fintype W] (D : Finset (W × W × W)) (a : W) :
    ∑ b, hmat D a b = #(rowSet D a) :=
  hmat_row19 D a

theorem hmat_supp {W : Type} [Fintype W] (D : Finset (W × W × W)) (S : Finset W)
    (hfirst : ∀ t ∈ D, t.1 ∈ S) (hsymm : ∀ t ∈ D, (t.2.2, t.2.1, t.1) ∈ D) (a b : W)
    (hab : hmat D a b ≠ 0) : a ∈ S ∧ b ∈ S := by
  unfold hmat at hab
  have hne : (D.filter fun t => t.1 = a ∧ t.2.2 = b).Nonempty := by
    rw [← card_pos]
    exact Nat.pos_of_ne_zero (by exact_mod_cast hab)
  obtain ⟨t, ht⟩ := hne
  rw [mem_filter] at ht
  obtain ⟨htD, rfl, rfl⟩ := ht
  exact ⟨hfirst t htD, hfirst _ (hsymm t htD)⟩

/-- `hmat D a b` compte les milieux `y` des triplets `(a, y, b)` de `D`. -/
private theorem hmat_eq_card19 {W : Type} [Fintype W] (D : Finset (W × W × W)) (a b : W) :
    hmat D a b = (#(univ.filter fun y => (a, y, b) ∈ D) : ℝ) := by
  unfold hmat
  congr 1
  apply Finset.card_nbij' (fun t => t.2.1) (fun y => (a, y, b))
  · intro t ht
    simp only [mem_coe, mem_filter, mem_univ, true_and] at ht ⊢
    obtain ⟨h, h1, h2⟩ := ht
    rw [← h1, ← h2]
    exact h
  · intro y hy
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hy
    simp [hy]
  · intro t ht
    simp only [mem_coe, mem_filter] at ht
    obtain ⟨_, h1, h2⟩ := ht
    rw [← h1, ← h2]
  · intro y _
    rfl

/-- Cardinal d'un ensemble de paires, fibre par fibre selon la première coordonnée. -/
private theorem card_prod19 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (S : Finset (α × β)) :
    #S = ∑ a, #(univ.filter fun b => (a, b) ∈ S) := by
  calc #S = #(univ.filter fun p => p ∈ S) := by
        congr 1
        ext p
        simp
    _ = ∑ a, ∑ b, (if (a, b) ∈ S then 1 else 0) := by
        rw [card_filter, Fintype.sum_prod_type]
    _ = ∑ a, #(univ.filter fun b => (a, b) ∈ S) := by
        simp only [card_filter]

/-- À `x` fixé, les `y` admissibles forment un `piFinset` de cardinal `cycW (hmat D) x`. -/
private theorem fiber_card19 {W : Type} [Fintype W] (D : Finset (W × W × W)) {m : ℕ}
    (x : Fin m → W) :
    (#(univ.filter fun y : Fin m → W =>
        ∀ l : Fin m, (x l, y l, x ⟨(l.val + 1) % m, Nat.mod_lt _ l.pos⟩) ∈ D) : ℝ) =
      cycW (hmat D) x := by
  have h : (univ.filter fun y : Fin m → W =>
        ∀ l : Fin m, (x l, y l, x ⟨(l.val + 1) % m, Nat.mod_lt _ l.pos⟩) ∈ D) =
      Fintype.piFinset fun l : Fin m =>
        univ.filter fun c => (x l, c, x ⟨(l.val + 1) % m, Nat.mod_lt _ l.pos⟩) ∈ D := by
    ext y
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset, Nat.cast_prod]
  unfold cycW
  refine prod_congr rfl fun l _ => ?_
  rw [hmat_eq_card19]

/-- À `x` fixé, un ensemble de `y` admissibles où `y j` est déterminé par les autres
coordonnées a un cardinal au plus `cycW (hmat D) x / s'`. -/
private theorem fiber_bound19 {W : Type} [Fintype W] (D : Finset (W × W × W)) {m : ℕ}
    (s' : ℝ) (hs' : 0 < s') (hlow : ∀ t ∈ D, s' ≤ hmat D t.1 t.2.2)
    (x : Fin m → W) (j : Fin m) (A : Finset (Fin m → W))
    (hA : ∀ y ∈ A, ∀ l : Fin m, (x l, y l, x ⟨(l.val + 1) % m, Nat.mod_lt _ l.pos⟩) ∈ D)
    (hinj : ∀ y ∈ A, ∀ y' ∈ A, (∀ l, l ≠ j → y l = y' l) → y = y') :
    s' * (#A : ℝ) ≤ cycW (hmat D) x := by
  set Yf : Fin m → Finset W := fun l =>
    univ.filter fun c => (x l, c, x ⟨(l.val + 1) % m, Nat.mod_lt _ l.pos⟩) ∈ D with hYf
  have hcyc : cycW (hmat D) x = ∏ l, (#(Yf l) : ℝ) := by
    unfold cycW
    refine prod_congr rfl fun l _ => ?_
    rw [hmat_eq_card19]
  rcases A.eq_empty_or_nonempty with hE | ⟨y0, hy0⟩
  · rw [hE, card_empty, Nat.cast_zero, mul_zero, hcyc]
    exact prod_nonneg fun l _ => Nat.cast_nonneg _
  · have hMj : s' ≤ (#(Yf j) : ℝ) := by
      have := hlow _ (hA y0 hy0 j)
      rw [hmat_eq_card19] at this
      exact this
    have hcard : #A ≤ ∏ l ∈ univ.erase j, #(Yf l) := by
      calc #A ≤ #(Fintype.piFinset (Function.update Yf j {x j})) := by
            apply card_le_card_of_injOn (fun y => Function.update y j (x j))
            · intro y hy
              simp only [mem_coe, Fintype.mem_piFinset]
              intro l
              by_cases hl : l = j
              · subst hl
                simp
              · rw [Function.update_of_ne hl, Function.update_of_ne hl]
                simp only [hYf, mem_filter, mem_univ, true_and]
                exact hA y hy l
            · intro y hy y' hy' hyy
              apply hinj y hy y' hy'
              intro l hl
              have := congrFun hyy l
              simp only [Function.update_of_ne hl] at this
              exact this
        _ = ∏ l ∈ univ.erase j, #(Yf l) := by
            rw [Fintype.card_piFinset, ← mul_prod_erase univ _ (mem_univ j),
              Function.update_self, card_singleton, one_mul]
            refine prod_congr rfl fun l hl => ?_
            rw [Function.update_of_ne (ne_of_mem_erase hl)]
    have hP : 0 ≤ ∏ l ∈ univ.erase j, (#(Yf l) : ℝ) :=
      prod_nonneg fun l _ => Nat.cast_nonneg _
    calc s' * (#A : ℝ) ≤ s' * ∏ l ∈ univ.erase j, (#(Yf l) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hs'.le
          exact_mod_cast hcard
      _ ≤ (#(Yf j) : ℝ) * ∏ l ∈ univ.erase j, (#(Yf l) : ℝ) :=
          mul_le_mul_of_nonneg_right hMj hP
      _ = cycW (hmat D) x := by
          rw [hcyc, mul_prod_erase univ (fun l => (#(Yf l) : ℝ)) (mem_univ j)]

/-- Forme générale de `cycSet_card`, pour des cycles de longueur `2m` quelconque. -/
private theorem cycSet_card19 {W : Type} [Fintype W] (D : Finset (W × W × W)) (m : ℕ)
    (s' : ℝ) (hs' : 0 < s') (hlow : ∀ t ∈ D, s' ≤ hmat D t.1 t.2.2) :
    ∑ x : Fin m → W, cycW (hmat D) x -
        ∑ x : Fin m → W,
          (if ∃ i j : Fin m, i ≠ j ∧ x i = x j then cycW (hmat D) x else 0) -
        2 * (m : ℝ) ^ 2 * (∑ x : Fin m → W, cycW (hmat D) x) / s' ≤
      (#(cycSet D m) : ℝ) := by
  set T := ∑ x : Fin m → W, cycW (hmat D) x with hT
  -- L'entrelacement `x₀ y₀ x₁ y₁ ⋯`.
  let ι : (Fin m → W) × (Fin m → W) → Fin (2 * m) → W := fun p q =>
    if q.val % 2 = 0 then p.1 ⟨q.val / 2, by have := q.isLt; omega⟩
    else p.2 ⟨q.val / 2, by have := q.isLt; omega⟩
  have hιe : ∀ p (q : Fin (2 * m)) (i : Fin m), q.val = 2 * i.val → ι p q = p.1 i := by
    intro p q i hq
    simp only [ι]
    rw [if_pos (by omega)]
    exact congrArg p.1 (Fin.ext (by show q.val / 2 = i.val; omega))
  have hιo : ∀ p (q : Fin (2 * m)) (i : Fin m), q.val = 2 * i.val + 1 → ι p q = p.2 i := by
    intro p q i hq
    simp only [ι]
    rw [if_neg (by omega)]
    exact congrArg p.2 (Fin.ext (by show q.val / 2 = i.val; omega))
  have hmod : ∀ i : Fin m, (2 * i.val + 2) % (2 * m) = 2 * ((i.val + 1) % m) := by
    intro i
    rw [show 2 * i.val + 2 = 2 * (i.val + 1) by ring, Nat.mul_mod_mul_left]
  -- Les paires admissibles et leurs sous-ensembles.
  set V := univ.filter fun p : (Fin m → W) × (Fin m → W) =>
    ∀ l : Fin m, (p.1 l, p.2 l, p.1 ⟨(l.val + 1) % m, Nat.mod_lt _ l.pos⟩) ∈ D with hV
  set G := V.filter fun p => Function.Injective (ι p) with hG
  set BT := V.filter fun p => ∃ i j : Fin m, i ≠ j ∧ p.1 i = p.1 j with hBT
  set BY := (univ : Finset (Fin m × Fin m)).biUnion
    (fun ij => V.filter fun p => ij.1 ≠ ij.2 ∧ p.2 ij.1 = p.2 ij.2) with hBY
  set BX := (univ : Finset (Fin m × Fin m)).biUnion
    (fun ij => V.filter fun p => p.1 ij.1 = p.2 ij.2) with hBX
  -- `#V = T`.
  have hVc : (#V : ℝ) = T := by
    rw [card_prod19 V, Nat.cast_sum, hT]
    refine sum_congr rfl fun x _ => ?_
    rw [← fiber_card19 D x]
    congr 2
    ext y
    simp [hV]
  -- `#BT` : le terme des `x` répétés.
  have hBTc : (#BT : ℝ) = ∑ x : Fin m → W,
      (if ∃ i j : Fin m, i ≠ j ∧ x i = x j then cycW (hmat D) x else 0) := by
    rw [card_prod19 BT, Nat.cast_sum]
    refine sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [← fiber_card19 D x]
      congr 2
      ext y
      simp [hBT, hV, h]
    · rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
      intro y _ hy
      simp only [hBT, mem_filter] at hy
      exact h hy.2
  -- Chaque paire de positions (YY) ou (TY) coûte au plus `T / s'`.
  have hYc : ∀ ij : Fin m × Fin m,
      (#(V.filter fun p => ij.1 ≠ ij.2 ∧ p.2 ij.1 = p.2 ij.2) : ℝ) ≤ T / s' := by
    intro ij
    rw [le_div_iff₀ hs', mul_comm, card_prod19, Nat.cast_sum, mul_sum, hT]
    refine sum_le_sum fun x _ => ?_
    apply fiber_bound19 D s' hs' hlow x ij.2
    · intro y hy
      simp only [hV, mem_filter, mem_univ, true_and] at hy
      exact hy.1
    · intro y hy y' hy' hyy
      simp only [hV, mem_filter, mem_univ, true_and] at hy hy'
      funext l
      by_cases hl : l = ij.2
      · rw [hl, ← hy.2.2, ← hy'.2.2]
        exact hyy ij.1 hy.2.1
      · exact hyy l hl
  have hXc : ∀ ij : Fin m × Fin m,
      (#(V.filter fun p => p.1 ij.1 = p.2 ij.2) : ℝ) ≤ T / s' := by
    intro ij
    rw [le_div_iff₀ hs', mul_comm, card_prod19, Nat.cast_sum, mul_sum, hT]
    refine sum_le_sum fun x _ => ?_
    apply fiber_bound19 D s' hs' hlow x ij.2
    · intro y hy
      simp only [hV, mem_filter, mem_univ, true_and] at hy
      exact hy.1
    · intro y hy y' hy' hyy
      simp only [hV, mem_filter, mem_univ, true_and] at hy hy'
      funext l
      by_cases hl : l = ij.2
      · rw [hl, ← hy.2, ← hy'.2]
      · exact hyy l hl
  have hpairs : ((Fintype.card (Fin m × Fin m) : ℕ) : ℝ) = (m : ℝ) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hBYc : (#BY : ℝ) ≤ (m : ℝ) ^ 2 * (T / s') := by
    calc (#BY : ℝ) ≤ ∑ ij : Fin m × Fin m,
          (#(V.filter fun p => ij.1 ≠ ij.2 ∧ p.2 ij.1 = p.2 ij.2) : ℝ) := by
          rw [hBY]
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _ij : Fin m × Fin m, T / s' := sum_le_sum fun ij _ => hYc ij
      _ = (m : ℝ) ^ 2 * (T / s') := by
          rw [sum_const, card_univ, nsmul_eq_mul, hpairs]
  have hBXc : (#BX : ℝ) ≤ (m : ℝ) ^ 2 * (T / s') := by
    calc (#BX : ℝ) ≤ ∑ ij : Fin m × Fin m,
          (#(V.filter fun p => p.1 ij.1 = p.2 ij.2) : ℝ) := by
          rw [hBX]
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _ij : Fin m × Fin m, T / s' := sum_le_sum fun ij _ => hXc ij
      _ = (m : ℝ) ^ 2 * (T / s') := by
          rw [sum_const, card_univ, nsmul_eq_mul, hpairs]
  -- Les paires injectives donnent des cycles de `cycSet D m`.
  have hGc : #G ≤ #(cycSet D m) := by
    apply card_le_card_of_injOn ι
    · intro p hp
      simp only [hG, hV, mem_coe, mem_filter, mem_univ, true_and] at hp
      simp only [cycSet, mem_coe, mem_filter, mem_univ, true_and]
      refine ⟨hp.2, fun i => ?_⟩
      have e1 := hιe p ⟨2 * i.val, by have := i.isLt; omega⟩ i rfl
      have e2 := hιo p ⟨2 * i.val + 1, by have := i.isLt; omega⟩ i rfl
      have e3 := hιe p ⟨(2 * i.val + 2) % (2 * m), Nat.mod_lt _ (by have := i.isLt; omega)⟩
        ⟨(i.val + 1) % m, Nat.mod_lt _ i.pos⟩ (hmod i)
      rw [e1, e2, e3]
      exact hp.1 i
    · intro p _ p' _ hpp
      have h1 : ∀ i : Fin m, p.1 i = p'.1 i := fun i => by
        have := congrFun hpp ⟨2 * i.val, by have := i.isLt; omega⟩
        rwa [hιe p _ i rfl, hιe p' _ i rfl] at this
      have h2 : ∀ i : Fin m, p.2 i = p'.2 i := fun i => by
        have := congrFun hpp ⟨2 * i.val + 1, by have := i.isLt; omega⟩
        rwa [hιo p _ i rfl, hιo p' _ i rfl] at this
      exact Prod.ext (funext h1) (funext h2)
  -- Toute paire admissible est injective ou mauvaise.
  have hcover : V ⊆ G ∪ (BT ∪ (BY ∪ BX)) := by
    intro p hp
    by_cases hinj : Function.Injective (ι p)
    · exact mem_union_left _ (by rw [hG, mem_filter]; exact ⟨hp, hinj⟩)
    · apply mem_union_right
      obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hinj
      simp only [ι] at hab
      have ha2 : a.val / 2 < m := by have := a.isLt; omega
      have hb2 : b.val / 2 < m := by have := b.isLt; omega
      split_ifs at hab with ha hb hb
      · refine mem_union_left _ ?_
        rw [hBT, mem_filter]
        refine ⟨hp, ⟨a.val / 2, ha2⟩, ⟨b.val / 2, hb2⟩, ?_, hab⟩
        intro h
        rw [Fin.mk.injEq] at h
        exact hne (Fin.ext (by omega))
      · refine mem_union_right _ (mem_union_right _ ?_)
        rw [hBX, mem_biUnion]
        exact ⟨(⟨a.val / 2, ha2⟩, ⟨b.val / 2, hb2⟩), mem_univ _, mem_filter.mpr ⟨hp, hab⟩⟩
      · refine mem_union_right _ (mem_union_right _ ?_)
        rw [hBX, mem_biUnion]
        exact ⟨(⟨b.val / 2, hb2⟩, ⟨a.val / 2, ha2⟩), mem_univ _, mem_filter.mpr ⟨hp, hab.symm⟩⟩
      · refine mem_union_right _ (mem_union_left _ ?_)
        rw [hBY, mem_biUnion]
        refine ⟨(⟨a.val / 2, ha2⟩, ⟨b.val / 2, hb2⟩), mem_univ _, mem_filter.mpr ⟨hp, ?_, hab⟩⟩
        intro h
        rw [Fin.mk.injEq] at h
        exact hne (Fin.ext (by omega))
  have hcard : #V ≤ #G + (#BT + (#BY + #BX)) := by
    calc #V ≤ #(G ∪ (BT ∪ (BY ∪ BX))) := card_le_card hcover
      _ ≤ #G + #(BT ∪ (BY ∪ BX)) := card_union_le _ _
      _ ≤ #G + (#BT + #(BY ∪ BX)) := by gcongr; exact card_union_le _ _
      _ ≤ #G + (#BT + (#BY + #BX)) := by gcongr; exact card_union_le _ _
  have hcardR : (#V : ℝ) ≤ #G + (#BT + (#BY + #BX)) := by exact_mod_cast hcard
  have hGR : (#G : ℝ) ≤ #(cycSet D m) := by exact_mod_cast hGc
  have hsplit : 2 * (m : ℝ) ^ 2 * T / s' = (m : ℝ) ^ 2 * (T / s') + (m : ℝ) ^ 2 * (T / s') := by
    ring
  rw [hsplit, ← hBTc]
  linarith

/-- Comptage : les `4k`-cycles `x₀ y₀ ⋯` de triplets dans `D` ont pour masse
`trace (hmat D ^ (2k))` ; on retire ceux où deux `x` coïncident (somme pondérée), puis ceux où un
`y` coïncide avec un autre sommet (au plus `2 (2k)²` paires de positions, chacune de masse
`≤ trace / s'` car les multiplicités non nulles valent au moins `s'`). -/
theorem cycSet_card {W : Type} [Fintype W] (D : Finset (W × W × W)) (k : ℕ) (hk : 2 ≤ k)
    (s' : ℝ) (hs' : 0 < s') (hlow : ∀ t ∈ D, s' ≤ hmat D t.1 t.2.2) :
    trace (hmat D ^ (2 * k)) -
        ∑ x : Fin (2 * k) → W,
          (if ∃ i j : Fin (2 * k), i ≠ j ∧ x i = x j then cycW (hmat D) x else 0) -
        2 * (2 * (k : ℝ)) ^ 2 * trace (hmat D ^ (2 * k)) / s' ≤
      (#(cycSet D (2 * k)) : ℝ) := by
  have h := cycSet_card19 D (2 * k) s' hs' hlow
  rw [total_cycW_eq_trace (hmat D) k hk] at h
  push_cast at h
  exact h

/- ## Lemme 20 : les trois conditions de la définition 2.11 (étape D) -/

/-- Les triplets d'un élément de `cycSet`. -/
private theorem trip20 {W : Type} [Fintype W] {D : Finset (W × W × W)} {m : ℕ}
    {w : Fin (2 * m) → W} (hw : w ∈ cycSet D m) (l : ℕ) (hl : l < m) :
    (w ⟨2 * l, by omega⟩, w ⟨2 * l + 1, by omega⟩,
      w ⟨(2 * l + 2) % (2 * m), Nat.mod_lt _ (by omega)⟩) ∈ D := by
  simp only [cycSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  exact hw.2 ⟨l, hl⟩

private theorem inj20 {W : Type} [Fintype W] {D : Finset (W × W × W)} {m : ℕ}
    {w : Fin (2 * m) → W} (hw : w ∈ cycSet D m) : Function.Injective w := by
  simp only [cycSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  exact hw.1

private theorem val20 {W : Type} {L : ℕ} (w : Fin L → W) (a b : Fin L) (h : a.val = b.val) :
    w a = w b := congrArg w (Fin.ext h)

/-- Condition 1 : sommets distincts, arêtes consécutives. -/
theorem cycSet_adj {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n × Fin n × Fin n))
    (m : ℕ) (hD : ∀ t ∈ D, G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2) :
    ∀ w ∈ cycSet D m, Function.Injective w ∧
      ∀ p : Fin (2 * m), G.Adj (w p) (w ⟨(p.val + 1) % (2 * m), Nat.mod_lt _ p.pos⟩) := by
  intro w hw
  refine ⟨inj20 hw, fun p => ?_⟩
  have hp := p.isLt
  obtain ⟨l, hl | hl⟩ : ∃ l, p.val = 2 * l ∨ p.val = 2 * l + 1 := ⟨p.val / 2, by omega⟩
  · have h := (hD _ (trip20 hw l (by omega))).1
    rwa [val20 w p ⟨2 * l, by omega⟩ hl,
      val20 w ⟨(p.val + 1) % (2 * m), Nat.mod_lt _ p.pos⟩ ⟨2 * l + 1, by omega⟩
        (by simp only; rw [hl, Nat.mod_eq_of_lt (by omega)])]
  · have h := (hD _ (trip20 hw l (by omega))).2
    rwa [val20 w p ⟨2 * l + 1, by omega⟩ hl,
      val20 w ⟨(p.val + 1) % (2 * m), Nat.mod_lt _ p.pos⟩
        ⟨(2 * l + 2) % (2 * m), Nat.mod_lt _ (by omega)⟩ (by simp only; rw [hl])]

/-- Condition 2 : à une position près, un cycle est déterminé par un voisin commun de `v` et
d'un `y` (position paire), ou de deux `x` (position impaire). -/
theorem cycSet_fix {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (D : Finset (Fin n × Fin n × Fin n)) (m : ℕ) (s : ℝ)
    (hD : ∀ t ∈ D, G.Adj v t.1 ∧ G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧
      (#(G.neighborFinset v ∩ G.neighborFinset t.2.1) : ℝ) ≤ s ∧
      (#(G.neighborFinset t.1 ∩ G.neighborFinset t.2.2) : ℝ) ≤ s) :
    ∀ y ∈ cycSet D m, ∀ i,
      (#((cycSet D m).filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s := by
  intro y hy i
  have hi := i.isLt
  have hinj : Set.InjOn (fun x : Fin (2 * m) → Fin n => x i)
      ((cycSet D m).filter fun x => ∀ j, j ≠ i → x j = y j) := by
    intro x hx z hz he
    funext j
    by_cases hj : j = i
    · subst hj
      exact he
    · exact ((Finset.mem_filter.mp hx).2 j hj).trans ((Finset.mem_filter.mp hz).2 j hj).symm
  have hne (a : Fin (2 * m)) (h : a.val ≠ i.val) : a ≠ i := fun e => h (congrArg Fin.val e)
  obtain ⟨l, hl | hl⟩ : ∃ l, i.val = 2 * l ∨ i.val = 2 * l + 1 := ⟨i.val / 2, by omega⟩
  · have hA := (hD _ (trip20 hy l (by omega))).2.2.2.1
    refine le_trans ?_ hA
    exact_mod_cast Finset.card_le_card_of_injOn (fun x : Fin (2 * m) → Fin n => x i) (by
      intro x hx
      obtain ⟨hxc, hxy⟩ := Finset.mem_filter.mp hx
      have ht := hD _ (trip20 hxc l (by omega))
      have e1 := val20 x i ⟨2 * l, by omega⟩ hl
      have e2 := hxy ⟨2 * l + 1, by omega⟩ (hne _ (by simp only; omega))
      simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe,
        SimpleGraph.mem_neighborFinset]
      rw [e1]
      exact ⟨ht.1, e2 ▸ ht.2.1.symm⟩) hinj
  · have hB := (hD _ (trip20 hy l (by omega))).2.2.2.2
    refine le_trans ?_ hB
    exact_mod_cast Finset.card_le_card_of_injOn (fun x : Fin (2 * m) → Fin n => x i) (by
      intro x hx
      obtain ⟨hxc, hxy⟩ := Finset.mem_filter.mp hx
      have ht := hD _ (trip20 hxc l (by omega))
      have e1 := val20 x i ⟨2 * l + 1, by omega⟩ hl
      have e2 := hxy ⟨2 * l, by omega⟩ (hne _ (by simp only; omega))
      have e3 := hxy ⟨(2 * l + 2) % (2 * m), Nat.mod_lt _ (by omega)⟩ (hne _ (by
        simp only
        rcases Nat.lt_or_ge (2 * l + 2) (2 * m) with h | h
        · rw [Nat.mod_eq_of_lt h]; omega
        · rw [show 2 * l + 2 = 2 * m by omega, Nat.mod_self]; omega))
      simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe,
        SimpleGraph.mem_neighborFinset]
      rw [e1]
      exact ⟨e2 ▸ ht.2.1, e3 ▸ ht.2.2.1.symm⟩) hinj

/-- Fibres : `#A ≤ #(A.image π) * K` si chaque fibre a au plus `K` éléments. -/
private theorem fib20 {β γ : Type} [DecidableEq γ] (A : Finset β) (π : β → γ) (K : ℝ)
    (h : ∀ u0 ∈ A.image π, (#(A.filter fun u => π u = u0) : ℝ) ≤ K) :
    (#A : ℝ) ≤ #(A.image π) * K := by
  rw [Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem π hx)]
  push_cast
  calc ∑ b ∈ A.image π, (#(A.filter fun u => π u = b) : ℝ) ≤ ∑ _b ∈ A.image π, K :=
        Finset.sum_le_sum h
    _ = #(A.image π) * K := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Allonger une fenêtre de lecture de `N` à `M` positions multiplie le nombre de lectures par
au plus `K`, si chaque fibre s'injecte par `φ` dans un ensemble `T u0` de taille `≤ K`. -/
private theorem step20 {α W γ : Type} (C : Finset α) (f : α → ℕ → W) (N M : ℕ) (hNM : N ≤ M)
    (T : (Fin N → W) → Finset γ) (φ : (Fin M → W) → γ) (K : ℝ)
    (hT : ∀ u0, (#(T u0) : ℝ) ≤ K)
    (hmaps : ∀ w ∈ C, φ (fun t => f w t.val) ∈ T (fun t => f w t.val))
    (hinj : ∀ w ∈ C, ∀ w' ∈ C, (∀ t < N, f w t = f w' t) →
      φ (fun t => f w t.val) = φ (fun t => f w' t.val) → ∀ t < M, f w t = f w' t) :
    (#(C.image fun w (t : Fin M) => f w t.val) : ℝ) ≤
      #(C.image fun w (t : Fin N) => f w t.val) * K := by
  have hAB : (C.image fun w (t : Fin M) => f w t.val).image
      (fun u (t : Fin N) => u ⟨t.val, lt_of_lt_of_le t.isLt hNM⟩) =
      C.image fun w (t : Fin N) => f w t.val := by
    rw [Finset.image_image]
    rfl
  rw [← hAB]
  apply fib20 (C.image fun w (t : Fin M) => f w t.val)
    (fun u (t : Fin N) => u ⟨t.val, lt_of_lt_of_le t.isLt hNM⟩) K
  intro u0 _
  refine le_trans (Nat.cast_le.mpr ?_) (hT u0)
  apply Finset.card_le_card_of_injOn φ
  · intro u hu
    obtain ⟨hu, hπ⟩ := Finset.mem_filter.mp hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    rw [← hπ]
    exact hmaps w hw
  · intro u hu u' hu' he
    obtain ⟨hu, hπ⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu', hπ'⟩ := Finset.mem_filter.mp hu'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hu'
    funext t
    exact hinj w hw w' hw' (fun s hs => congrFun (hπ.trans hπ'.symm) ⟨s, hs⟩) he t.val t.isLt

/-- Lectures des `2q+1` premières positions : un départ dans `S`, puis `q` triplets de `D`. -/
private theorem readQ20 {α W : Type} (C : Finset α) (f : α → ℕ → W) (D : Finset (W × W × W))
    (S : Finset W) (Δ R : ℝ) (hS : (#S : ℝ) ≤ Δ) (hR : 0 ≤ R)
    (hrow : ∀ a, (#(rowSet D a) : ℝ) ≤ R) (r : ℕ)
    (h0 : ∀ w ∈ C, f w 0 ∈ S)
    (htr : ∀ w ∈ C, ∀ t < r, (f w (2 * t), f w (2 * t + 1), f w (2 * t + 2)) ∈ D) :
    ∀ q ≤ r, (#(C.image fun w (t : Fin (2 * q + 1)) => f w t.val) : ℝ) ≤ Δ * R ^ q := by
  intro q
  induction q with
  | zero =>
    intro _
    have hc : #(C.image fun w (t : Fin (2 * 0 + 1)) => f w t.val) ≤ #S := by
      apply Finset.card_le_card_of_injOn (fun u => u ⟨0, by omega⟩)
      · intro u hu
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
        exact h0 w hw
      · intro u hu u' hu' he
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hu'
        funext t
        have ht : t = ⟨0, by omega⟩ := Fin.ext (by have := t.isLt; omega)
        subst ht
        exact he
    calc (#(C.image fun w (t : Fin (2 * 0 + 1)) => f w t.val) : ℝ) ≤ #S := by exact_mod_cast hc
      _ ≤ Δ * R ^ 0 := by rw [pow_zero, mul_one]; exact hS
  | succ q ih =>
    intro hq
    calc (#(C.image fun w (t : Fin (2 * (q + 1) + 1)) => f w t.val) : ℝ)
        ≤ #(C.image fun w (t : Fin (2 * q + 1)) => f w t.val) * R :=
          step20 C f (2 * q + 1) (2 * (q + 1) + 1) (by omega)
            (fun u0 => rowSet D (u0 ⟨2 * q, by omega⟩))
            (fun u => (u ⟨2 * q, by omega⟩, u ⟨2 * q + 1, by omega⟩, u ⟨2 * q + 2, by omega⟩))
            R (fun _ => hrow _)
            (fun w hw => by
              show (f w (2 * q), f w (2 * q + 1), f w (2 * q + 2)) ∈ rowSet D (f w (2 * q))
              exact Finset.mem_filter.mpr ⟨htr w hw q (by omega), rfl⟩)
            (fun w _ w' _ hlt he t ht => by
              rcases (show t < 2 * q + 1 ∨ t = 2 * q + 1 ∨ t = 2 * q + 2 by omega) with h | h | h
              · exact hlt t h
              · subst h
                exact congrArg (fun p => p.2.1) he
              · subst h
                exact congrArg (fun p => p.2.2) he)
      _ ≤ Δ * R ^ q * R := mul_le_mul_of_nonneg_right (ih (by omega)) hR
      _ = Δ * R ^ (q + 1) := by rw [pow_succ, mul_assoc]

/-- Lectures des `2r+2` premières positions : `readQ20`, puis un `y` final dans `extSet`. -/
private theorem read20 {α W : Type} (C : Finset α) (f : α → ℕ → W) (D : Finset (W × W × W))
    (S : Finset W) (Δ R E : ℝ) (hS : (#S : ℝ) ≤ Δ) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hrow : ∀ a, (#(rowSet D a) : ℝ) ≤ R) (hext : ∀ a, (#(extSet D a) : ℝ) ≤ E) (r : ℕ)
    (h0 : ∀ w ∈ C, f w 0 ∈ S)
    (htr : ∀ w ∈ C, ∀ t < r, (f w (2 * t), f w (2 * t + 1), f w (2 * t + 2)) ∈ D)
    (hlast : ∀ w ∈ C, f w (2 * r + 1) ∈ extSet D (f w (2 * r))) :
    (#(C.image fun w (t : Fin (2 * r + 2)) => f w t.val) : ℝ) ≤ Δ * R ^ r * E := by
  calc (#(C.image fun w (t : Fin (2 * r + 2)) => f w t.val) : ℝ)
      ≤ #(C.image fun w (t : Fin (2 * r + 1)) => f w t.val) * E :=
        step20 C f (2 * r + 1) (2 * r + 2) (by omega)
          (fun u0 => extSet D (u0 ⟨2 * r, by omega⟩)) (fun u => u ⟨2 * r + 1, by omega⟩)
          E (fun _ => hext _)
          (fun w hw => by
            show f w (2 * r + 1) ∈ extSet D (f w (2 * r))
            exact hlast w hw)
          (fun w _ w' _ hlt he t ht => by
            rcases (show t < 2 * r + 1 ∨ t = 2 * r + 1 by omega) with h | h
            · exact hlt t h
            · subst h
              exact he)
    _ ≤ Δ * R ^ r * E :=
        mul_le_mul_of_nonneg_right (readQ20 C f D S Δ R hS hR hrow r h0 htr r le_rfl) hE

/-- Oubli de deux positions : si les positions gardées se lisent, dans l'ordre `a 0, a 1, …`,
comme un départ dans `S`, `r` triplets de `D` et un `y` final dans `extSet`, alors `Δ R^r E`
fonctions suffisent à décrire `C` hors de `p1` et `p2`. -/
private theorem forget20 {W : Type} {L : ℕ} (C : Finset (Fin L → W)) (D : Finset (W × W × W))
    (S : Finset W) (Δ R E : ℝ) (hS : (#S : ℝ) ≤ Δ) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hrow : ∀ a, (#(rowSet D a) : ℝ) ≤ R) (hext : ∀ a, (#(extSet D a) : ℝ) ≤ E)
    (r : ℕ) (a : ℕ → Fin L) (p1 p2 : Fin L)
    (h0 : ∀ w ∈ C, w (a 0) ∈ S)
    (htr : ∀ w ∈ C, ∀ t < r, (w (a (2 * t)), w (a (2 * t + 1)), w (a (2 * t + 2))) ∈ D)
    (hlast : ∀ w ∈ C, w (a (2 * r + 1)) ∈ extSet D (w (a (2 * r))))
    (hcov : ∀ j, j ≠ p1 → j ≠ p2 → ∃ t < 2 * r + 2, a t = j) :
    ∃ P : Finset (Fin L → W), (#P : ℝ) ≤ Δ * R ^ r * E ∧
      ∀ w ∈ C, ∃ y ∈ P, ∀ j, j ≠ p1 → j ≠ p2 → w j = y j := by
  have hB := read20 C (fun w t => w (a t)) D S Δ R E hS hR hE hrow hext r h0 htr hlast
  refine ⟨(C.image fun w (t : Fin (2 * r + 2)) => w (a t.val)).image
      (fun u j => if h : ∃ t : Fin (2 * r + 2), a t.val = j then u h.choose
        else u ⟨0, by omega⟩), ?_, ?_⟩
  · exact le_trans (by exact_mod_cast Finset.card_image_le) hB
  · intro w hw
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hw), fun j hj1 hj2 => ?_⟩
    obtain ⟨t, ht, hat⟩ := hcov j hj1 hj2
    have hex : ∃ t : Fin (2 * r + 2), a t.val = j := ⟨⟨t, ht⟩, hat⟩
    dsimp only
    rw [dif_pos hex, hex.choose_spec]

/-- `x % n` pour `x < 2n`. -/
private theorem mod20 (x n : ℕ) (h : x < 2 * n) :
    (x < n ∧ x % n = x) ∨ (n ≤ x ∧ x % n = x - n) := by
  rcases Nat.lt_or_ge x n with hx | hx
  · exact Or.inl ⟨hx, Nat.mod_eq_of_lt hx⟩
  · refine Or.inr ⟨hx, ?_⟩
    rw [Nat.mod_eq_sub_mod hx, Nat.mod_eq_of_lt (by omega)]

/-- Le triplet de `cycSet` qui commence en position `2q` (modulo `2m`), pour tout `q`. -/
private theorem tripX20 {W : Type} [Fintype W] {D : Finset (W × W × W)} {m : ℕ}
    {w : Fin (2 * m) → W} (hw : w ∈ cycSet D m) (h2m : 0 < 2 * m) (x0 x1 x2 q : ℕ)
    (h0 : x0 = 2 * q) (h1 : x1 = 2 * q + 1) (h2 : x2 = 2 * q + 2) :
    (w ⟨x0 % (2 * m), Nat.mod_lt _ h2m⟩, w ⟨x1 % (2 * m), Nat.mod_lt _ h2m⟩,
      w ⟨x2 % (2 * m), Nat.mod_lt _ h2m⟩) ∈ D := by
  subst h0 h1 h2
  have hm : 0 < m := by omega
  have hqm := Nat.mod_lt q hm
  have h := trip20 hw (q % m) hqm
  have e0 : (2 * q) % (2 * m) = 2 * (q % m) := Nat.mul_mod_mul_left 2 q m
  have e0' : (2 * q) % (2 * m) = (2 * (q % m)) % (2 * m) := by
    rw [e0, Nat.mod_eq_of_lt (show 2 * (q % m) < 2 * m by omega)]
  have e1 : (2 * q + 1) % (2 * m) = 2 * (q % m) + 1 := by
    have e : (2 * q + 1) % (2 * m) = (2 * (q % m) + 1) % (2 * m) :=
      Nat.ModEq.add_right 1 (n := 2 * m) e0'
    rw [e, Nat.mod_eq_of_lt (show 2 * (q % m) + 1 < 2 * m by omega)]
  have e2 : (2 * q + 2) % (2 * m) = (2 * (q % m) + 2) % (2 * m) :=
    Nat.ModEq.add_right 2 (n := 2 * m) e0'
  have k0 : (⟨(2 * q) % (2 * m), Nat.mod_lt _ h2m⟩ : Fin (2 * m)) =
      ⟨2 * (q % m), by omega⟩ := Fin.ext e0
  have k1 : (⟨(2 * q + 1) % (2 * m), Nat.mod_lt _ h2m⟩ : Fin (2 * m)) =
      ⟨2 * (q % m) + 1, by omega⟩ := Fin.ext e1
  have k2 : (⟨(2 * q + 2) % (2 * m), Nat.mod_lt _ h2m⟩ : Fin (2 * m)) =
      ⟨(2 * (q % m) + 2) % (2 * m), Nat.mod_lt _ h2m⟩ := Fin.ext e2
  rw [k0, k1, k2]
  exact h

/-- Le même triplet, retourné par la symétrie de `D`. -/
private theorem tripR20 {W : Type} [Fintype W] {D : Finset (W × W × W)} {m : ℕ}
    {w : Fin (2 * m) → W} (hw : w ∈ cycSet D m) (h2m : 0 < 2 * m)
    (hsymm : ∀ t ∈ D, (t.2.2, t.2.1, t.1) ∈ D) (x0 x1 x2 q : ℕ)
    (h0 : x0 = 2 * q + 2) (h1 : x1 = 2 * q + 1) (h2 : x2 = 2 * q) :
    (w ⟨x0 % (2 * m), Nat.mod_lt _ h2m⟩, w ⟨x1 % (2 * m), Nat.mod_lt _ h2m⟩,
      w ⟨x2 % (2 * m), Nat.mod_lt _ h2m⟩) ∈ D :=
  hsymm _ (tripX20 hw h2m x2 x1 x0 q h2 h1 h0)

private theorem first20 {W : Type} [Fintype W] {D : Finset (W × W × W)} {m : ℕ}
    {w : Fin (2 * m) → W} (hw : w ∈ cycSet D m) (h2m : 0 < 2 * m) {S : Finset W}
    (hfirst : ∀ t ∈ D, t.1 ∈ S) (x q : ℕ) (h : x = 2 * q) :
    w ⟨x % (2 * m), Nat.mod_lt _ h2m⟩ ∈ S :=
  hfirst _ (tripX20 hw h2m x (2 * q + 1) (2 * q + 2) q h rfl rfl)

private theorem ext20 {W : Type} {D : Finset (W × W × W)} {a b c : W} (h : (a, b, c) ∈ D) :
    b ∈ extSet D a :=
  Finset.mem_image.mpr ⟨(a, b, c), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

/-- Condition 3 : oublier deux positions consécutives laisse un chemin `x y x ⋯ x y` (lu dans un
sens ou dans l'autre, `D` étant symétrique) : `x` initial dans `S`, `m - 2` triplets complets
(au plus `R` choix chacun), un `y` final dans `extSet` du dernier `x`. -/
theorem cycSet_forget {W : Type} [Fintype W] (D : Finset (W × W × W)) (m : ℕ) (hm : 2 ≤ m)
    (S : Finset W) (Δ R E : ℝ) (hS : (#S : ℝ) ≤ Δ) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hsymm : ∀ t ∈ D, (t.2.2, t.2.1, t.1) ∈ D) (hfirst : ∀ t ∈ D, t.1 ∈ S)
    (hrow : ∀ a, (#(rowSet D a) : ℝ) ≤ R) (hext : ∀ a, (#(extSet D a) : ℝ) ≤ E)
    (i : Fin (2 * m)) :
    let nx : Fin (2 * m) → Fin (2 * m) := fun i => ⟨(i.val + 1) % (2 * m), Nat.mod_lt _ i.pos⟩
    ∃ P : Finset (Fin (2 * m) → W), (#P : ℝ) ≤ Δ * R ^ (m - 2) * E ∧
      ∀ w ∈ cycSet D m, ∃ y ∈ P, ∀ j, j ≠ nx i → j ≠ nx (nx i) → w j = y j := by
  intro nx
  have h2m : 0 < 2 * m := by omega
  have hi := i.isLt
  have hne : ∀ j : Fin (2 * m), j ≠ nx i → j ≠ nx (nx i) →
      j.val ≠ (i.val + 1) % (2 * m) ∧ j.val ≠ ((i.val + 1) % (2 * m) + 1) % (2 * m) :=
    fun j h1 h2 => ⟨fun e => h1 (Fin.ext e), fun e => h2 (Fin.ext e)⟩
  have hm1 := mod20 (i.val + 1) (2 * m) (by omega)
  have hm2 := mod20 ((i.val + 1) % (2 * m) + 1) (2 * m)
    (by have := Nat.mod_lt (i.val + 1) h2m; omega)
  obtain ⟨l, hl | hl⟩ : ∃ l, i.val = 2 * l ∨ i.val = 2 * l + 1 := ⟨i.val / 2, by omega⟩
  · -- `i` pair : lecture à l'envers depuis `i`
    refine forget20 (cycSet D m) D S Δ R E hS hR hE hrow hext (m - 2)
      (fun t => ⟨(i.val + 2 * m - t) % (2 * m), Nat.mod_lt _ h2m⟩) (nx i) (nx (nx i))
      ?_ ?_ ?_ ?_
    · intro w hw
      exact first20 hw h2m hfirst (i.val + 2 * m - 0) (l + m) (by omega)
    · intro w hw t ht
      exact tripR20 hw h2m hsymm (i.val + 2 * m - 2 * t) (i.val + 2 * m - (2 * t + 1))
        (i.val + 2 * m - (2 * t + 2)) (l + m - t - 1) (by omega) (by omega) (by omega)
    · intro w hw
      exact ext20 (tripR20 hw h2m hsymm (i.val + 2 * m - 2 * (m - 2))
        (i.val + 2 * m - (2 * (m - 2) + 1)) (2 * l + 2) (l + 1) (by omega) (by omega)
        (by omega))
    · intro j hj1 hj2
      obtain ⟨hj1', hj2'⟩ := hne j hj1 hj2
      have hj := j.isLt
      by_cases hji : j.val ≤ i.val
      · refine ⟨i.val - j.val, by omega, Fin.ext ?_⟩
        show (i.val + 2 * m - (i.val - j.val)) % (2 * m) = j.val
        have := mod20 (i.val + 2 * m - (i.val - j.val)) (2 * m) (by omega)
        omega
      · refine ⟨i.val + 2 * m - j.val, by omega, Fin.ext ?_⟩
        show (i.val + 2 * m - (i.val + 2 * m - j.val)) % (2 * m) = j.val
        have := mod20 (i.val + 2 * m - (i.val + 2 * m - j.val)) (2 * m) (by omega)
        omega
  · -- `i` impair : lecture directe depuis `i + 3`
    refine forget20 (cycSet D m) D S Δ R E hS hR hE hrow hext (m - 2)
      (fun t => ⟨(i.val + 3 + t) % (2 * m), Nat.mod_lt _ h2m⟩) (nx i) (nx (nx i))
      ?_ ?_ ?_ ?_
    · intro w hw
      exact first20 hw h2m hfirst (i.val + 3 + 0) (l + 2) (by omega)
    · intro w hw t ht
      exact tripX20 hw h2m (i.val + 3 + 2 * t) (i.val + 3 + (2 * t + 1))
        (i.val + 3 + (2 * t + 2)) (l + 2 + t) (by omega) (by omega) (by omega)
    · intro w hw
      exact ext20 (tripX20 hw h2m (i.val + 3 + 2 * (m - 2)) (i.val + 3 + (2 * (m - 2) + 1))
        (2 * (l + m) + 2) (l + m) (by omega) (by omega) rfl)
    · intro j hj1 hj2
      obtain ⟨hj1', hj2'⟩ := hne j hj1 hj2
      have hj := j.isLt
      by_cases hji : i.val + 3 ≤ j.val
      · refine ⟨j.val - (i.val + 3), by omega, Fin.ext ?_⟩
        show (i.val + 3 + (j.val - (i.val + 3))) % (2 * m) = j.val
        have := mod20 (i.val + 3 + (j.val - (i.val + 3))) (2 * m) (by omega)
        omega
      · refine ⟨j.val + 2 * m - (i.val + 3), by omega, Fin.ext ?_⟩
        show (i.val + 3 + (j.val + 2 * m - (i.val + 3))) % (2 * m) = j.val
        have := mod20 (i.val + 3 + (j.val + 2 * m - (i.val + 3))) (2 * m) (by omega)
        omega

/- ## Lemme 21 : asymptotique (étape E) -/

private theorem growth21 (C a b : ℝ) (h : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ)^a ≤ (n : ℝ)^b := by
  have ht := ((tendsto_rpow_atTop (sub_pos.mpr h)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop C
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht] with n hn hc
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc
    _ ≤ (n : ℝ)^(b-a) * (n : ℝ)^a := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← Real.rpow_add hn', sub_add_cancel]

private theorem sqrt21 {q d N T S P : ℝ} (hT : 0 < T) (hP : 0 ≤ P)
    (hS : S ≤ N^d * T^(1-d)) (hcoef : 64*q^2*P*N^d ≤ T^d) :
    2*q * Real.sqrt (P*S*T) ≤ T/4 := by
  by_cases h : P*S*T ≤ 0
  · rw [Real.sqrt_eq_zero_of_nonpos h, mul_zero]; positivity
  have hbound : 64*q^2*P*S ≤ T := calc
    _ ≤ 64*q^2*P*(N^d*T^(1-d)) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (64*q^2*P*N^d)*T^(1-d) := by ring
    _ ≤ T^d*T^(1-d) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = T := by rw [← Real.rpow_add hT, show d+(1-d) = 1 by ring, Real.rpow_one]
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, Real.sq_sqrt (le_of_not_ge h)]
  nlinarith only [mul_le_mul_of_nonneg_right hbound hT.le]

/-- Une puissance du facteur polylogarithmique `log n · (⌊log₂ n⌋ + 1)²` est négligeable devant
`n ^ b`. -/
private theorem logpow21 (b C : ℝ) (m : ℕ) (hb : 0 < b) (hC : 0 ≤ C) (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop,
      C * (Real.log n * ((Nat.log 2 n : ℝ) + 1) ^ 2) ^ m ≤ (n : ℝ) ^ b := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  set δ : ℝ := b / (12 * m) with hδ
  have hδ0 : 0 < δ := by positivity
  filter_upwards [eventually_ge_atTop 3, growth21 (1/δ) δ (2*δ) (by linarith),
    growth21 (3/δ) δ (2*δ) (by linarith), growth21 C (b/2) b (by linarith)]
    with n hn h1 h2 h3
  have hN3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0:ℝ) < n := by linarith
  have hlog : Real.log n ≤ (n:ℝ)^δ / δ := Real.log_le_rpow_div hN0.le hδ0
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9
    linarith
  have hnl : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
    have hpow : ((2:ℕ):ℝ)^(Nat.log 2 n) ≤ (n:ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have h4 := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at h4
    have h5 := Real.log_two_gt_d9
    push_cast at h4
    nlinarith
  have hL : Real.log n ≤ (n:ℝ)^(2*δ) := by
    calc _ ≤ (n:ℝ)^δ/δ := hlog
      _ = 1/δ * (n:ℝ)^δ := by ring
      _ ≤ _ := h1
  have hJ : (Nat.log 2 n : ℝ) + 1 ≤ (n:ℝ)^(2*δ) := by
    calc _ ≤ 3 * Real.log n := by linarith
      _ ≤ 3 * ((n:ℝ)^δ/δ) := by linarith
      _ = 3/δ * (n:ℝ)^δ := by ring
      _ ≤ _ := h2
  have hJ0 : (0:ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by positivity
  have hG0 : 0 ≤ Real.log n * ((Nat.log 2 n : ℝ) + 1) ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hG : Real.log n * ((Nat.log 2 n : ℝ) + 1) ^ 2 ≤ (n:ℝ)^(b/2/m) := by
    calc _ ≤ (n:ℝ)^(2*δ) * ((n:ℝ)^(2*δ))^2 := by gcongr
      _ = (n:ℝ)^(b/2/m) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
        congr 1
        rw [hδ]; push_cast; field_simp; ring
  have hGm : (Real.log n * ((Nat.log 2 n : ℝ) + 1) ^ 2)^m ≤ (n:ℝ)^(b/2) := by
    calc _ ≤ ((n:ℝ)^(b/2/m))^m := pow_le_pow_left₀ hG0 hG m
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        congr 1
        field_simp
  calc _ ≤ C * (n:ℝ)^(b/2) := mul_le_mul_of_nonneg_left hGm hC
    _ ≤ _ := h3

set_option maxHeartbeats 1000000 in
/-- Les inégalités numériques de la preuve, pour `n` grand. `Q = #c4`, `Dc = #D`, `T` et `T'`
les traces `2·(2k)` et `2·(2k-1)` de `hmat D`, `Δ = K n^(1/3+ε)`,
`U = 96 log n / n^(4/3+ε) · Q`. -/
theorem h2_asymp (ε K : ℝ) (hε : 0 < ε) (hε6 : ε < 1 / 6) (hK : 0 < K) (k : ℕ)
    (hk : 1 / ε ≤ k) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      ∀ Q Dc s s' T T' : ℝ,
        8 * (n : ℝ) ^ (5 / 3 + 3 * ε) / (96 * Real.log n) ≤ Q →
        Q ≤ 2 * n * ((Nat.log 2 n : ℝ) + 1) ^ 2 * Dc →
        0 < s → s ≤ 2 * (K * (n : ℝ) ^ (1 / 3 + ε)) →
        Dc ≤ 2 * s' * (K * (n : ℝ) ^ (1 / 3 + ε)) ^ 2 →
        (Dc / (K * (n : ℝ) ^ (1 / 3 + ε))) ^ (2 * (2 * k)) ≤ T →
        T' ≤ (n : ℝ) ^ (1 / ((2 * k : ℕ) : ℝ)) * T ^ (1 - 1 / ((2 * k : ℕ) : ℝ)) →
        0 < T ∧
        2 * ((2 * k : ℕ) : ℝ) * Real.sqrt (((2 * k : ℕ) : ℝ) * s *
            (96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * Q) * T' * T) ≤ T / 4 ∧
        2 * (2 * ((2 * k : ℕ) : ℝ)) ^ 2 * T / s' ≤ T / 4 ∧
        K * (n : ℝ) ^ (1 / 3 + ε) *
            (96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * Q) ^ (2 * (2 * k) - 2) *
            (4 * (96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * Q) / s) ≤
          (n : ℝ) ^ (-(ε / 2)) * (T / 2) / (16 * k * s) := by
  have hk6 : (6:ℝ) < k := lt_of_lt_of_le ((lt_div_iff₀ hε).mpr (by linarith)) hk
  have hk1 : 1 ≤ k * ε := (div_le_iff₀ hε).mp hk
  have hk0 : (0:ℝ) < k := by linarith
  have hk7 : 6 < k := by exact_mod_cast hk6
  set q : ℝ := ((2 * k : ℕ) : ℝ) with hq
  have hqv : q = 2 * (k:ℝ) := by rw [hq]; push_cast; ring
  have hq0 : 0 < q := by rw [hqv]; linarith
  have hdq : 1 / q ≤ ε / 2 := by
    rw [div_le_iff₀ hq0, hqv]; nlinarith
  have hLd : ((2 * (2 * k) : ℕ) : ℝ) * (1 / q) = 2 := by
    rw [hqv]; push_cast; field_simp
  obtain ⟨p, hp⟩ : ∃ p, 2 * (2 * k) - 2 = p := ⟨_, rfl⟩
  have hp2 : 2 * (2 * k) = p + 2 := by omega
  filter_upwards [eventually_ge_atTop 3,
    logpow21 (ε/2) (589824*q^3*K^3) 2 (by positivity) (by positivity) (by norm_num),
    logpow21 (ε/2) (1536*q^2*K^2) 1 (by positivity) (by positivity) (by norm_num),
    logpow21 (ε/2) (3072*k*K^2*(192*K)^(p+1)) (p+2) (by positivity) (by positivity) (by omega)]
    with n hn g2 g3 g4
  refine ⟨by omega, ?_⟩
  intro Q Dc s s' T T' hQ hQD hs0 hs hDs' hT hT'
  have hN3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0:ℝ) < n := by linarith
  have hL0 : 0 < Real.log n := Real.log_pos (by linarith)
  have e43 : (n:ℝ) ^ (4/3+ε) = n * (n:ℝ) ^ (1/3+ε) := by
    rw [show (4/3:ℝ)+ε = 1 + (1/3+ε) by ring, Real.rpow_add hN0 1, Real.rpow_one]
  have e53 : (n:ℝ) ^ (5/3+3*ε) = n * ((n:ℝ) ^ (1/3+ε))^2 * ((n:ℝ) ^ (ε/2))^2 := by
    rw [show (5/3:ℝ)+3*ε = 1 + (1/3+ε) + (1/3+ε) + (ε/2+ε/2) by ring,
      Real.rpow_add hN0 (1 + (1/3+ε) + (1/3+ε)), Real.rpow_add hN0 (1 + (1/3+ε)),
      Real.rpow_add hN0 1, Real.rpow_add hN0 (ε/2), Real.rpow_one]
    ring
  have eneg : (n:ℝ) ^ (-(ε/2)) = ((n:ℝ) ^ (ε/2))⁻¹ := Real.rpow_neg hN0.le _
  have e1q : (n:ℝ) ^ (1/q) ≤ (n:ℝ) ^ (ε/2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hdq
  rw [e53] at hQ
  rw [e43, eneg, hp]
  set N : ℝ := (n:ℝ) with hNdef
  set L := Real.log N with hLdef
  set J : ℝ := (Nat.log 2 n : ℝ) + 1 with hJdef
  have hJ1 : 1 ≤ J := by
    rw [hJdef]; have := (Nat.log 2 n).cast_nonneg (α := ℝ); linarith
  set G := L * J^2 with hGdef
  have hG0 : 0 < G := by positivity
  set A := N ^ (1/3+ε) with hAdef
  have hA0 : 0 < A := by positivity
  set h := N ^ (ε/2) with hhdef
  have hh1 : 1 ≤ h := Real.one_le_rpow (by linarith) (by positivity)
  have hh0 : 0 < h := by linarith
  set U := 96 * L / (N * A) * Q with hUdef
  -- Q > 0, Dc > 0
  have hQ' : 8*(N*A^2*h^2) ≤ 96*L*Q := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 96*L)).mp hQ
    linarith
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have hU0 : 0 ≤ U := by rw [hUdef]; positivity
  have hDc0 : 0 < Dc := by
    by_contra hc
    have := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0:ℝ) ≤ 2*N*J^2) (not_lt.mp hc)
    linarith
  obtain ⟨x, hx0, rfl⟩ : ∃ x, 0 < x ∧ Dc = K*A*x :=
    ⟨Dc/(K*A), by positivity, by field_simp⟩
  rw [mul_div_cancel_left₀ x (by positivity : K*A ≠ 0)] at hT
  have hTpos : 0 < T := lt_of_lt_of_le (pow_pos hx0 _) hT
  -- (i)
  have hi : A*h^2 ≤ 24*K*G*x := by
    have h1 : 8*(N*A^2*h^2) ≤ 96*L*(2*N*J^2*(K*A*x)) :=
      hQ'.trans (mul_le_mul_of_nonneg_left hQD (by positivity))
    have h2 : (A*h^2) * (8*N*A) ≤ (24*K*G*x) * (8*N*A) := by
      calc (A*h^2)*(8*N*A) = 8*(N*A^2*h^2) := by ring
      _ ≤ 96*L*(2*N*J^2*(K*A*x)) := h1
      _ = (24*K*G*x)*(8*N*A) := by rw [hGdef]; ring
    exact le_of_mul_le_mul_right h2 (by positivity)
  -- (ii)
  have hii : U ≤ 192*K*G*x := by
    rw [hUdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc 96*L*Q ≤ 96*L*(2*N*J^2*(K*A*x)) := mul_le_mul_of_nonneg_left hQD (by positivity)
    _ = _ := by rw [hGdef]; ring
  -- (iii)
  have hroot : x^2 ≤ T^(1/q) := calc
    x^2 = (x^(2*(2*k)))^(1/q) := by
      rw [← Real.rpow_natCast x (2*(2*k)), ← Real.rpow_mul hx0.le, hLd, Real.rpow_two]
    _ ≤ T^(1/q) := Real.rpow_le_rpow (by positivity) hT (by positivity)
  -- 2e conclusion
  have hkey2 : 24576*q^3*K^2*A*G*h ≤ x := by
    have h1 : (24576*q^3*K^2*A*G*h) * (24*K*G) ≤ x * (24*K*G) := by
      calc (24576*q^3*K^2*A*G*h) * (24*K*G) = (589824*q^3*K^3*G^2) * (A*h) := by ring
      _ ≤ h * (A*h) := mul_le_mul_of_nonneg_right g2 (by positivity)
      _ = A*h^2 := by ring
      _ ≤ 24*K*G*x := hi
      _ = x*(24*K*G) := by ring
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hcoef : 64*q^2*(q*s*U)*N^(1/q) ≤ T^(1/q) := calc
    64*q^2*(q*s*U)*N^(1/q) ≤ 64*q^2*(q*(2*(K*A))*(192*K*G*x))*h := by gcongr
    _ = (24576*q^3*K^2*A*G*h)*x := by ring
    _ ≤ x * x := mul_le_mul_of_nonneg_right hkey2 hx0.le
    _ = x^2 := by ring
    _ ≤ T^(1/q) := hroot
  -- 3e conclusion
  have hx2 : x ≤ 2*s'*K*A := by
    have h1 : (K*A)*x ≤ (K*A)*(2*s'*K*A) := by
      calc (K*A)*x ≤ 2*s'*(K*A)^2 := hDs'
      _ = _ := by ring
    exact le_of_mul_le_mul_left h1 (by positivity)
  have hs'0 : 0 < s' := by
    by_contra hc
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) (by positivity : (0:ℝ) ≤ K*A)
    linarith [lt_of_lt_of_le hx0 hx2]
  have h32 : 32*q^2 ≤ s' := by
    have h1 : (32*q^2) * (48*K^2*G*A) ≤ s' * (48*K^2*G*A) := by
      calc (32*q^2) * (48*K^2*G*A) = (1536*q^2*K^2*G^1) * A := by ring
      _ ≤ h * A := mul_le_mul_of_nonneg_right g3 hA0.le
      _ ≤ h^2 * A := by gcongr; nlinarith
      _ = A*h^2 := by ring
      _ ≤ 24*K*G*x := hi
      _ ≤ 24*K*G*(2*s'*K*A) := by gcongr
      _ = s' * (48*K^2*G*A) := by ring
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hthird : 2 * (2 * q) ^ 2 * T / s' ≤ T / 4 := by
    rw [div_le_iff₀ hs'0]
    nlinarith [mul_le_mul_of_nonneg_left h32 hTpos.le]
  -- 4e conclusion
  have hkey4 : 128*k*K*A*h*(192*K*G)^(p+1) ≤ x := by
    have h1 : (128*k*K*A*h*(192*K*G)^(p+1)) * (24*K*G) ≤ x * (24*K*G) := by
      calc (128*k*K*A*h*(192*K*G)^(p+1)) * (24*K*G)
          = (3072*k*K^2*(192*K)^(p+1)*G^(p+2)) * (A*h) := by ring_nf
      _ ≤ h * (A*h) := mul_le_mul_of_nonneg_right g4 (by positivity)
      _ = A*h^2 := by ring
      _ ≤ 24*K*G*x := hi
      _ = x*(24*K*G) := by ring
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hmain : 128*k*K*A*h*U^(p+1) ≤ T := calc
    128*k*K*A*h*U^(p+1) ≤ 128*k*K*A*h*(192*K*G*x)^(p+1) := by gcongr
    _ = (128*k*K*A*h*(192*K*G)^(p+1)) * x^(p+1) := by ring_nf
    _ ≤ x * x^(p+1) := mul_le_mul_of_nonneg_right hkey4 (by positivity)
    _ = x^(p+2) := by ring
    _ ≤ T := by rw [← hp2]; exact hT
  have hlhs : K*A*U^p*(4*U/s) = 128*k*K*A*h*U^(p+1) / (32*k*s*h) := by
    field_simp
    ring
  have hrhs : h⁻¹*(T/2)/(16*k*s) = T/(32*k*s*h) := by
    field_simp
    ring
  refine ⟨hTpos, sqrt21 hTpos (by positivity) hT' hcoef, hthird, ?_⟩
  rw [hlhs, hrhs]
  exact div_le_div_of_nonneg_right hmain (by positivity)

end E147H2

open E147H2 in
set_option maxHeartbeats 2000000 in
lemma h2_solution : OMA.R_Erdos147_erdos_147_variants_cubic_R1.H2 := by
  classical
  intro ε K hε hε6 hK k hk
  have hkpos : 0 < k := by
    by_contra! hz
    have hzero : k = 0 := by omega
    rw [hzero, Nat.cast_zero] at hk
    exact (not_lt_of_ge hk) (by positivity)
  have hk2 : 2 ≤ 2 * k := by omega
  filter_upwards [h2_asymp ε K hε hε6 hK k hk] with n hn
  obtain ⟨hn2, hnum⟩ := hn
  intro G c4 nxt₀ hdeg hQ hU
  let next (L : ℕ) (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
  let result (L : ℕ) : Prop := ∃ C : Finset (Fin L → Fin n), C.Nonempty ∧ ∃ s : ℝ, 0 < s ∧
    (∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (next L i))) ∧
    (∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s) ∧
    ∀ i : Fin L, ∃ P : Finset (Fin L → Fin n),
      (#P : ℝ) ≤ (n : ℝ) ^ (-(ε / 2)) * #C / (16 * k * s) ∧
      ∀ x ∈ C, ∃ y ∈ P, ∀ j, j ≠ next L i → j ≠ next L (next L i) → x j = y j
  change result (8 * k)
  rw [show 8 * k = 2 * (2 * (2 * k)) by ring]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hQpos : 0 < (#c4 : ℝ) := lt_of_lt_of_le
    (div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hnpos _)) (mul_pos (by norm_num) hlog)) hQ
  have hU0 : 0 ≤ 96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * (#c4 : ℝ) :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hlog.le) (Real.rpow_nonneg hnpos.le _))
      hQpos.le
  have hQnat : 0 < #c4 := Nat.cast_pos.mp hQpos
  obtain ⟨v, s, s', D, hs, hs2, hs', hQD, hD, hsymm, hlow, hDc, hhs, hrowU, hext⟩ :=
    stepAB G (K * (n : ℝ) ^ (1 / 3 + ε)) (96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * #c4)
      hdeg hU hQnat
  have hQD' : (#c4 : ℝ) ≤ 2 * n * ((Nat.log 2 n : ℝ) + 1) ^ 2 * #D := hQD
  have hDpos : 0 < #D := by
    rcases Nat.eq_zero_or_pos (#D) with h0 | h0
    · rw [h0, Nat.cast_zero, mul_zero] at hQD'
      linarith
    · exact h0
  obtain ⟨t₀, ht₀⟩ := Finset.card_pos.mp hDpos
  have hpos : ∃ u w, 0 < hmat D u w := ⟨t₀.1, t₀.2.2, lt_of_lt_of_le hs' (hlow t₀ ht₀)⟩
  have hfirst : ∀ t ∈ D, t.1 ∈ G.neighborFinset v :=
    fun t ht => (G.mem_neighborFinset v t.1).2 (hD t ht).1
  have hSne : (G.neighborFinset v).Nonempty := ⟨t₀.1, hfirst t₀ ht₀⟩
  have hScard : (#(G.neighborFinset v) : ℝ) ≤ K * (n : ℝ) ^ (1 / 3 + ε) := by
    rw [G.card_neighborFinset_eq_degree]
    exact hdeg v
  have hSpos : 0 < (#(G.neighborFinset v) : ℝ) := by exact_mod_cast hSne.card_pos
  have hsid := sidorenko_supp (hmat D) (hmat_symm D hsymm) (G.neighborFinset v) hSne
    (hmat_supp D _ hfirst hsymm) (2 * k)
  rw [hmat_sum] at hsid
  have hT : ((#D : ℝ) / (K * (n : ℝ) ^ (1 / 3 + ε))) ^ (2 * (2 * k)) ≤
      trace (hmat D ^ (2 * (2 * k))) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) ?_ _) hsid
    exact div_le_div_of_nonneg_left (by positivity) hSpos hScard
  have hint := trace_interp_M (hmat D) (hmat_nonneg D) (hmat_symm D hsymm) hpos (2 * k)
    (by omega)
  rw [Fintype.card_fin] at hint
  obtain ⟨hTpos, hTT, hYY, hlast⟩ := hnum (#c4) (#D) s s' _ _ hQ hQD' hs hs2 hDc
    (by convert hT using 0; congr!) hint
  have hrot := bad_le_rot (hmat D) (hmat_nonneg D) Eq (fun _ _ h => h.symm) (2 * k) hk2
  have hrow : ∀ a, ∑ b, hmat D a b ≤ 96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * #c4 :=
    fun a => (hmat_row D a).trans_le (hrowU a)
  have hanch := conflictM_le (hmat D) (hmat_nonneg D) (hmat_symm D hsymm) Eq
    (fun _ _ h => h.symm) s _ hs.le hU0 (fun b e => by
      refine le_of_eq_of_le ?_ (hhs b e)
      refine (Finset.sum_eq_single e ?_ ?_).trans ?_
      · intro a _ hae
        exact if_neg (Ne.symm hae)
      · intro h
        exact absurd (mem_univ e) h
      · exact if_pos rfl) hrow (2 * k) hk2
  have hbad := (hrot.trans (mul_le_mul_of_nonneg_left hanch (by positivity))).trans hTT
  have hcard := cycSet_card D (2 * k) hk2 s' hs' hlow
  have hCpos : 0 < (#(cycSet D (2 * (2 * k))) : ℝ) := by linarith
  have hD' : ∀ t ∈ D, G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 :=
    fun t ht => ⟨(hD t ht).2.1, (hD t ht).2.2.1⟩
  have hadj := cycSet_adj G D (2 * (2 * k)) hD'
  refine ⟨cycSet D (2 * (2 * k)), Finset.card_pos.mp (by exact_mod_cast hCpos), s, hs,
    fun x hx => hadj x hx, cycSet_fix G v D _ s hD, fun i => ?_⟩
  have hext' : ∀ a, (#(extSet D a) : ℝ) ≤
      4 * (96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * #c4) / s :=
    fun a => (le_div_iff₀ hs).2 (hext a)
  obtain ⟨P, hP, hP'⟩ := cycSet_forget D (2 * (2 * k)) (by omega) (G.neighborFinset v)
    (K * (n : ℝ) ^ (1 / 3 + ε)) _ _ hScard hU0 (by positivity) hsymm hfirst hrowU hext' i
  refine ⟨P, hP.trans (hlast.trans ?_), hP'⟩
  gcongr
  linarith
end H2Sec

section H3Sec
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
lemma h3_solution : OMA.R_Erdos147_erdos_147_variants_cubic_R1.H3 := by
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
end H3Sec

open OMA.R_Erdos147_erdos_147_variants_cubic_R1 in
theorem OMA.solution : OMA.R_Erdos147_erdos_147_variants_janzer_conjecture_R1.H2 := by
  intro ε hε
  exact E147.transfer h1_solution h2_solution h3_solution ε hε
