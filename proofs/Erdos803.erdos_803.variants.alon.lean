import FormalConjectures.ErdosProblems.«803»
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Alon's construction by finite counting on dyadic blocks. -/

open Finset Real SimpleGraph
open scoped BigOperators Classical

open Finset
open scoped BigOperators Classical

namespace AlonRandom803

noncomputable section

variable {Ω : Type*} [Fintype Ω]

def mass (E : Finset Ω) : ℝ := (E.card : ℝ) / Fintype.card Ω

theorem mass_nonneg (E : Finset Ω) : 0 ≤ mass E := by unfold mass; positivity

theorem mass_mono {E F : Finset Ω} (h : E ⊆ F) : mass E ≤ mass F := by
  unfold mass
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card h) (by positivity)

theorem mass_union_le [DecidableEq Ω] {ι : Type*} (s : Finset ι) (E : ι → Finset Ω) :
    mass (s.biUnion E) ≤ ∑ i ∈ s, mass (E i) := by
  unfold mass
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_biUnion_le) (by positivity)

theorem exists_not_mem_of_mass_sum_lt_one [Nonempty Ω] [DecidableEq Ω] {ι : Type*}
    (s : Finset ι) (E : ι → Finset Ω) (h : ∑ i ∈ s, mass (E i) < 1) :
    ∃ x : Ω, ∀ i ∈ s, x ∉ E i := by
  by_contra! hf
  have he : s.biUnion E = (univ : Finset Ω) := eq_univ_of_forall fun x => mem_biUnion.mpr (hf x)
  have h1 : mass (univ : Finset Ω) = 1 := by
    simp [mass, Nat.ne_of_gt (Fintype.card_pos (α := Ω))]
  have hb := mass_union_le s E
  rw [he,h1] at hb
  exact (not_lt_of_ge hb) h

theorem fixed_mass {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]
    [∀ i, Nonempty (β i)] (s : Finset ι) (f : (i : ι) → β i)
    {p : ℝ} (hs : ∀ i ∈ s, (1 : ℝ) / Fintype.card (β i) ≤ p) :
    mass (univ.filter fun g : (i : ι) → β i => ∀ i ∈ s, g i = f i) ≤ p ^ s.card := by
  let t : (i : ι) → Finset (β i) := fun i => if i ∈ s then {f i} else univ
  have he : (univ.filter fun g : (i : ι) → β i => ∀ i ∈ s, g i = f i) =
      Fintype.piFinset t := by
    ext g
    simp only [mem_filter,mem_univ,true_and,Fintype.mem_piFinset]
    constructor
    · intro hg i
      by_cases hi : i ∈ s
      · simpa [t,hi] using hg i hi
      · simp [t,hi]
    · intro hg i hi
      simpa [t,hi] using hg i
  rw [he,mass,Fintype.card_piFinset,Fintype.card_pi]
  push_cast
  rw [← Finset.prod_div_distrib]
  rw [← Finset.prod_subset (subset_univ s) (f := fun i =>
    (t i).card / (Fintype.card (β i) : ℝ)) (by
      intro i _ hi
      simp [t,hi, Nat.ne_of_gt (Fintype.card_pos (α := β i))])]
  calc
    _ ≤ ∏ i ∈ s, p := Finset.prod_le_prod (fun _ _ => by positivity) (fun i hi => by
      simpa [t,hi] using hs i hi)
    _ = _ := by simp

section Bipartite

variable {A I : Type*} [Fintype A] [Fintype I] (B : I → Type*) [∀ i, Fintype (B i)]

abbrev Choice := (j : A × I) → B j.2

def realizes (g : Choice (A := A) B) (e : A × Sigma B) : Prop :=
  g (e.1,e.2.1) = e.2.2

def edges (g : Choice (A := A) B) (P : Finset A) (Q : Finset (Sigma B)) : Finset (A × Sigma B) :=
  (P ×ˢ Q).filter (realizes B g)

theorem chosen_edges_mass [∀ i, Nonempty (B i)] (F : Finset (A × Sigma B)) {p : ℝ}
    (hp : 0 ≤ p) (hF : ∀ e ∈ F, (1 : ℝ) / Fintype.card (B e.2.1) ≤ p) :
    mass (univ.filter fun g : Choice B => ∀ e ∈ F, realizes B g e) ≤ p ^ F.card := by
  let E := univ.filter fun g : Choice (A := A) B => ∀ e ∈ F, realizes B g e
  change mass E ≤ _
  by_cases he : E.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp he,mass,pow_nonneg hp]
  obtain ⟨f,hf⟩ := he
  have hf' : ∀ e ∈ F, realizes B f e := (mem_filter.mp hf).2
  let key : A × Sigma B → A × I := fun e => (e.1,e.2.1)
  have hkey : Set.InjOn key (F : Set (A × Sigma B)) := by
    rintro ⟨a,i,x⟩ hu ⟨b,j,y⟩ hv hij
    change (a,i) = (b,j) at hij
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hij
    have h := (hf' (a,⟨i,x⟩) hu).symm.trans (hf' (a,⟨i,y⟩) hv)
    simpa only [Prod.mk.injEq,Sigma.mk.injEq,true_and,heq_eq_eq] using h
  have hi : ∀ j ∈ F.image key, (1 : ℝ) / Fintype.card (B j.2) ≤ p := by
    intro j hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    exact hF e he
  have hsub : E ⊆ (univ.filter fun g : Choice B => ∀ j ∈ F.image key, g j = f j) := by
    intro g hg
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    intro j hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    exact ((mem_filter.mp hg).2 e he).trans (hf' e he).symm
  exact (mass_mono hsub).trans (by simpa only [Finset.card_image_of_injOn hkey] using fixed_mass (F.image key) f hi)

theorem rectangle_mass [∀ i, Nonempty (B i)] (P : Finset A) (Q : Finset (Sigma B))
    (k : ℕ) {p : ℝ} (hp : 0 ≤ p) (hQ : ∀ b ∈ Q, (1 : ℝ) / Fintype.card (B b.1) ≤ p) :
    mass (univ.filter fun g : Choice B => k ≤ (edges B g P Q).card) ≤
      ((P.card * Q.card).choose k : ℝ) * p ^ k := by
  let C := (P ×ˢ Q).powersetCard k
  let E (F : Finset (A × Sigma B)) := univ.filter fun g : Choice B => ∀ e ∈ F, realizes B g e
  have hs : (univ.filter fun g : Choice B => k ≤ (edges B g P Q).card) ⊆ C.biUnion E := by
    intro g hg
    obtain ⟨F,hF,he⟩ := Finset.exists_subset_card_eq ((mem_filter.mp hg).2)
    have he' : F ⊆ P ×ˢ Q := hF.trans (Finset.filter_subset _ _)
    exact mem_biUnion.mpr ⟨F,mem_powersetCard.mpr ⟨he',he⟩,
      mem_filter.mpr ⟨mem_univ _,fun e he => (mem_filter.mp (hF he)).2⟩⟩
  calc
    _ ≤ mass (C.biUnion E) := mass_mono hs
    _ ≤ ∑ F ∈ C, mass (E F) := mass_union_le C E
    _ ≤ ∑ _F ∈ C, p^k := Finset.sum_le_sum fun F hF => by
      obtain ⟨hFPQ,hk⟩ := mem_powersetCard.mp hF
      rw [← hk]
      exact chosen_edges_mass B F hp (fun e he => hQ _ (mem_product.mp (hFPQ he)).2)
    _ = _ := by simp [C,Finset.card_powersetCard,Finset.card_product]

end Bipartite

end

end AlonRandom803

namespace AlonRandom803

def cutoff (K : ℕ) : ℕ := 2 ^ (K / 8)

def threshold (K : ℕ) : ℕ := 32 + 8 * Nat.sqrt K

private theorem two_pow_le {a b : ℕ} (h : a ≤ b) : (2 : ℝ)^a ≤ 2^b :=
  pow_le_pow_right₀ (by norm_num) h

theorem small_count {K m a b : ℕ} (hK : 32 ≤ K) (hm : m ≤ cutoff K)
    (ha : a ≤ m) (hb : b ≤ m) :
    ((a*b).choose (32*m) : ℝ) * (1 / (2:ℝ)^(K/2))^(32*m) ≤ 1 / (2:ℝ)^(6*(K+1)*m) := by
  let k := 32*m
  have hab : a*b ≤ 2^(2*(K/8)) := by
    calc
      a*b ≤ m*m := Nat.mul_le_mul ha hb
      _ ≤ cutoff K * cutoff K := Nat.mul_le_mul hm hm
      _ = _ := by simp [cutoff,two_mul,pow_add]
  have hE : 2 * (K/8) * k + 6*(K+1)*m ≤ (K/2)*k := by
    have h : 2*(K/8)*32 + 6*(K+1) ≤ (K/2)*32 := by omega
    have he := Nat.mul_le_mul_right m h
    simpa [k,Nat.add_mul,Nat.mul_assoc] using he
  have hcap : ((a*b).choose k : ℝ) ≤ ((2 : ℝ)^(2*(K/8)))^k := by
    have hn := (Nat.choose_le_pow (a*b) k).trans (Nat.pow_le_pow_left hab k)
    exact_mod_cast hn
  change _ * (1/(2:ℝ)^(K/2))^k ≤ _
  calc
    _ ≤ ((2:ℝ)^(2*(K/8)))^k * (1/(2:ℝ)^(K/2))^k := by gcongr
    _ = (2:ℝ)^(2*(K/8)*k) / (2:ℝ)^(K/2*k) := by
      simp only [div_pow,one_pow,← pow_mul,mul_one_div]
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      rw [← pow_add,one_mul]
      exact two_pow_le hE

theorem threshold_sq (K : ℕ) : 6*(K+1)+2 ≤ threshold K ^ 2 := by
  have hroot := Nat.lt_succ_sqrt' K
  change K < (Nat.sqrt K + 1)^2 at hroot
  have h₁ : 8*(Nat.sqrt K + 1) ≤ threshold K := by unfold threshold; omega
  have h₂ := Nat.pow_le_pow_left h₁ 2
  rw [mul_pow] at h₂
  norm_num at h₂
  omega

theorem large_count {K m a b : ℕ} (hm : 0 < m) (ha : a ≤ m) (hb : b ≤ m) :
    ((a*b).choose (threshold K*m) : ℝ) * (1 / ((m:ℝ) * (2:ℝ)^threshold K))^(threshold K*m)
      ≤ 1 / (2:ℝ)^(6*(K+1)*m) := by
  let r := threshold K
  let k := r*m
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hab : ((a*b : ℕ):ℝ) ≤ (m:ℝ) * m := by
    exact_mod_cast Nat.mul_le_mul ha hb
  have hs : ((a*b).choose k : ℝ) ≤ ((m:ℝ)*m)^k / k.factorial :=
    (Nat.choose_le_pow_div (α := ℝ) k (a*b)).trans (by gcongr)
  have he : Real.exp (m:ℝ) ≤ (2:ℝ)^(2*m) := by
    rw [pow_mul,show (m:ℝ) = (m:ℝ)*1 from by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_one_lt_three.le.trans (by norm_num)) _
  have hh : 2*m + 6*(K+1)*m ≤ r*k := by
    have h := Nat.mul_le_mul_right m (threshold_sq K)
    simpa [r,k,Nat.add_mul,Nat.mul_assoc,pow_two,Nat.add_comm] using h
  change _ * (1/((m:ℝ)*(2:ℝ)^r))^k ≤ _
  calc
    _ ≤ ((m:ℝ)*m)^k / k.factorial * (1/((m:ℝ)*(2:ℝ)^r))^k := by gcongr
    _ = ((m:ℝ)^k / k.factorial) / (2:ℝ)^(r*k) := by
      rw [div_pow,one_pow,mul_pow,mul_pow,← pow_mul]
      have hm' : (m:ℝ)^k ≠ 0 := ne_of_gt (pow_pos hmR _)
      field_simp
    _ ≤ Real.exp (m:ℝ) / (2:ℝ)^(r*k) :=
      div_le_div_of_nonneg_right (Real.pow_div_factorial_le_exp (m:ℝ) hmR.le k) (by positivity)
    _ ≤ (2:ℝ)^(2*m) / (2:ℝ)^(r*k) := div_le_div_of_nonneg_right he (by positivity)
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      rw [← pow_add,one_mul]
      exact two_pow_le hh

theorem sum_bound (N : ℕ) :
    ∑ m ∈ Icc 1 N, (1/4:ℝ)^m < 1 := by
  calc
    _ ≤ ∑' m : ℕ, (1/4:ℝ)^m * (1/4) := by
      have he : Icc 1 N = Ico 1 (N+1) := by ext i; simp
      rw [he,Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      simpa only [pow_add,pow_one,mul_comm] using
        (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
          (by norm_num : (1/4:ℝ)<1)).mul_right (1/4) |>.sum_le_tsum (range N) (by intro i hi; positivity)
    _ < _ := by
      rw [tsum_mul_right,tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)]
      norm_num

end AlonRandom803

namespace AlonRandom803

noncomputable section

private def boundedSets (X : Type*) [Fintype X] (m : ℕ) : Finset (Finset X) :=
  (range (m+1)).biUnion fun k => (univ : Finset X).powersetCard k

private theorem mem_boundedSets {X : Type*} [Fintype X] {P : Finset X} {m : ℕ} :
    P ∈ boundedSets X m ↔ P.card ≤ m := by
  simp [boundedSets,Finset.mem_biUnion,Finset.mem_powersetCard]

private theorem card_boundedSets {X : Type*} [Fintype X] {N : ℕ}
    (hN : 2 ≤ N) (hX : Fintype.card X ≤ N) (m : ℕ) :
    (boundedSets X m).card ≤ N^(2*m) := by
  have hpow : m+1 ≤ 2^m := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ]; omega
  have hmN : m+1 ≤ N^m := hpow.trans (Nat.pow_le_pow_left hN _)
  unfold boundedSets
  calc
    _ ≤ ∑ k ∈ range (m+1), ((univ : Finset X).powersetCard k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ range (m+1), N^m := Finset.sum_le_sum fun k hk => by
      rw [Finset.card_powersetCard,Finset.card_univ]
      exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left hX _).trans
        (Nat.pow_le_pow_right (by omega) (by simpa using hk)))
    _ = (m+1)*N^m := by simp
    _ ≤ N^(2*m) := by
      rw [two_mul,pow_add]
      exact Nat.mul_le_mul_right _ hmN

section Bipartite

variable {A I : Type*} [Fintype A] [Fintype I] (B : I → Type*)
    [∀ i, Fintype (B i)] [∀ i, Nonempty (B i)]

def largePart (K m : ℕ) (Q : Finset (Sigma B)) : Finset (Sigma B) :=
  Q.filter fun b => m * 2^threshold K ≤ Fintype.card (B b.1)

private def trim (K m : ℕ) (Q : Finset (Sigma B)) : Finset (Sigma B) :=
  if m ≤ cutoff K then Q else largePart B K m Q

private def edgeLimit (K m : ℕ) : ℕ :=
  if m ≤ cutoff K then 32*m else threshold K*m

private def bad (K m : ℕ) : Finset (Choice (A := A) B) :=
  (boundedSets A m ×ˢ boundedSets (Sigma B) m).biUnion fun pq =>
    univ.filter fun g => edgeLimit K m ≤ (edges B g pq.1 (trim B K m pq.2)).card

private theorem rectangle_bad_mass {K m : ℕ} (hK : 32 ≤ K) (hm : 0 < m)
    (hmin : ∀ i, 2^(K/2) ≤ Fintype.card (B i))
    {P : Finset A} {Q : Finset (Sigma B)} (hP : P.card ≤ m) (hQ : Q.card ≤ m) :
    mass (univ.filter fun g : Choice B => edgeLimit K m ≤ (edges B g P (trim B K m Q)).card) ≤
      1 / (2:ℝ)^(6*(K+1)*m) := by
  by_cases hs : m ≤ cutoff K
  · rw [trim,if_pos hs,edgeLimit,if_pos hs]
    refine (rectangle_mass B P Q (32*m) (p := 1/(2:ℝ)^(K/2)) (by positivity) ?_).trans
      (small_count hK hs hP hQ)
    intro b _
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hmin b.1
  · rw [trim,if_neg hs,edgeLimit,if_neg hs]
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    refine (rectangle_mass B P (largePart B K m Q) (threshold K*m)
      (p := 1/((m:ℝ)*(2:ℝ)^threshold K)) (by positivity) ?_).trans
      (large_count hm hP ((Finset.card_filter_le _ _).trans hQ))
    intro b hb
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (mem_filter.mp hb).2

private theorem bad_mass {K m : ℕ} (hK : 32 ≤ K) (hm : 0 < m)
    (hA : Fintype.card A ≤ 2^(K+1)) (hB : Fintype.card (Sigma B) ≤ 2^(K+1))
    (hmin : ∀ i, 2^(K/2) ≤ Fintype.card (B i)) :
    mass (bad (A := A) B K m) ≤ (1/4:ℝ)^m := by
  let Z := boundedSets A m ×ˢ boundedSets (Sigma B) m
  let E (pq : Finset A × Finset (Sigma B)) : Finset (Choice (A := A) B) :=
    univ.filter fun g => edgeLimit K m ≤ (edges B g pq.1 (trim B K m pq.2)).card
  have h₂ : 2 ≤ 2^(K+1) := by rw [pow_succ]; have := Nat.one_le_pow K 2 (by decide); omega
  have hZ : Z.card ≤ 2^(4*(K+1)*m) := by
    rw [Finset.card_product]
    calc
      _ ≤ ((2:ℕ)^(K+1))^(2*m) * ((2:ℕ)^(K+1))^(2*m) :=
        Nat.mul_le_mul (card_boundedSets h₂ hA m) (card_boundedSets h₂ hB m)
      _ = _ := by rw [← pow_add,← pow_mul]; congr 1; ring
  have hZR : (Z.card:ℝ) ≤ (2:ℝ)^(4*(K+1)*m) := by exact_mod_cast hZ
  change mass (Z.biUnion E) ≤ _
  calc
    _ ≤ ∑ pq ∈ Z, mass (E pq) := mass_union_le Z E
    _ ≤ ∑ _pq ∈ Z, 1/(2:ℝ)^(6*(K+1)*m) := Finset.sum_le_sum fun pq hpq => by
      obtain ⟨hP,hQ⟩ := Finset.mem_product.mp hpq
      exact rectangle_bad_mass B hK hm hmin (mem_boundedSets.mp hP) (mem_boundedSets.mp hQ)
    _ = (Z.card:ℝ)*(1/(2:ℝ)^(6*(K+1)*m)) := by simp
    _ ≤ (2:ℝ)^(4*(K+1)*m)/(2:ℝ)^(6*(K+1)*m) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hZR (by positivity)
    _ ≤ _ := by
      rw [div_pow,one_pow,show (4:ℝ)^m = (2:ℝ)^(2*m) from by rw [pow_mul]; norm_num]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      rw [← pow_add,one_mul]
      apply two_pow_le
      have h : 4*(K+1)*m + 2*m ≤ 4*(K+1)*m + 2*(K+1)*m := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
      calc
        _ ≤ _ := h
        _ = _ := by ring

theorem exists_good {K : ℕ} (n : ℕ) (hK : 32 ≤ K)
    (hA : Fintype.card A ≤ 2^(K+1)) (hB : Fintype.card (Sigma B) ≤ 2^(K+1))
    (hmin : ∀ i, 2^(K/2) ≤ Fintype.card (B i)) :
    ∃ g : Choice (A := A) B, ∀ m ∈ Icc 1 n, ∀ (P : Finset A) (Q : Finset (Sigma B)),
      P.card ≤ m → Q.card ≤ m →
      (m ≤ cutoff K → (edges B g P Q).card ≤ 32*m) ∧
      (cutoff K < m → (edges B g P (largePart B K m Q)).card ≤ threshold K*m) := by
  have hmass : ∑ m ∈ Icc 1 n, mass (bad (A := A) B K m) < 1 := by
    refine (Finset.sum_le_sum (fun m hm => bad_mass B hK (by have := (mem_Icc.mp hm).1; omega)
      hA hB hmin)).trans_lt (sum_bound n)
  obtain ⟨g,hg⟩ := exists_not_mem_of_mass_sum_lt_one (Icc 1 n) (bad (A := A) B K) hmass
  refine ⟨g,fun m hm P Q hP hQ => ?_⟩
  have hg' : (edges B g P (trim B K m Q)).card < edgeLimit K m := by
    by_contra! hn
    exact hg m hm (mem_biUnion.mpr ⟨(P,Q),Finset.mem_product.mpr
      ⟨mem_boundedSets.mpr hP,mem_boundedSets.mpr hQ⟩, mem_filter.mpr ⟨mem_univ _,hn⟩⟩)
  exact ⟨fun h => by simpa only [trim,edgeLimit,if_pos h] using hg'.le,
    fun h => by simpa only [trim,edgeLimit,if_neg h.not_ge] using hg'.le⟩

end Bipartite

end

end AlonRandom803

namespace AlonBlocks803

abbrev L (n : ℕ) := Fin (n/2)

abbrev I (K : ℕ) := Fin 8 × ↥(Ico (K/2) (K-4))

abbrev B (K : ℕ) (i : I K) := Fin (2^i.2.val)

theorem card_block (K : ℕ) (i : I K) : Fintype.card (B K i) = 2^i.2.val :=
  Fintype.card_fin _

theorem min_block (K : ℕ) (i : I K) : 2^(K/2) ≤ Fintype.card (B K i) := by
  rw [card_block]
  exact Nat.pow_le_pow_right (by decide) (mem_Ico.mp i.2.property).1

theorem sum_block_labels (K : ℕ) (f : ℕ → ℕ) :
    ∑ i : I K, f i.2.val = 8 * ∑ k ∈ Ico (K/2) (K-4), f k := by
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_attach]

theorem card_blocks (K : ℕ) : Fintype.card (I K) = 8 * (K-4-K/2) := by
  simp [Nat.card_Ico]

private theorem two_geom (k : ℕ) : (∑ i ∈ range k, (2:ℕ)^i) + 1 = 2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,pow_succ]
    omega

theorem card_right (K n : ℕ) (hK : 4 ≤ K) (hN : 2^K ≤ n) :
    Fintype.card (Sigma (B K)) ≤ n/2 := by
  simp only [Fintype.card_sigma,card_block,sum_block_labels]
  have hs : Ico (K/2) (K-4) ⊆ range (K-4) := fun _ hi =>
    mem_range.mpr (mem_Ico.mp hi).2
  have hq := Finset.sum_le_sum_of_subset_of_nonneg hs
    (f := fun i => (2:ℕ)^i) (fun _ _ _ => Nat.zero_le _)
  have hpow := two_geom (K-4)
  have he : 2 * (8 * 2^(K-4)) = 2^K := by
    rw [← mul_assoc,show 2*8 = (2:ℕ)^4 by decide,← pow_add]
    congr 1
    omega
  have hle : (∑ i ∈ Ico (K/2) (K-4), (2:ℕ)^i) ≤ 2^(K-4) := by omega
  have ht := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 8 hle)
  rw [he] at ht
  omega

noncomputable def embedding (K n : ℕ) (hK : 4 ≤ K) (hN : 2^K ≤ n) :
    (L n ⊕ Sigma (B K)) ↪ Fin n :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (by
    rw [Fintype.card_sum,Fintype.card_fin]
    have := card_right K n hK hN
    omega))

theorem enough_edges (K n : ℕ) (hK : 32 ≤ K) (hN : 2^K ≤ n) (hn : n ≤ 2^(K+1)) :
    (n : ℝ)*Real.log n ≤ (Fintype.card (L n) : ℝ) * Fintype.card (I K) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hN
  have hn3 : 3 ≤ n := by
    have := (Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ K by omega)).trans hN
    norm_num at this
    omega
  have hl : (n:ℝ) ≤ 3 * (Fintype.card (L n) : ℝ) := by
    rw [Fintype.card_fin]
    exact_mod_cast (show n ≤ 3*(n/2) by omega)
  have hb : (3:ℝ)*K ≤ Fintype.card (I K) := by
    rw [card_blocks]
    exact_mod_cast (show 3*K ≤ 8*(K-4-K/2) by omega)
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  have hlog : Real.log n ≤ K := calc
    _ ≤ Real.log ((2:ℝ)^(K+1)) := Real.log_le_log hnr (by exact_mod_cast hn)
    _ = (K+1:ℕ)*Real.log 2 := Real.log_pow _ _
    _ ≤ _ := by
      have h₂ : Real.log 2 ≤ 3/4 := Real.log_two_lt_d9.le.trans (by norm_num)
      have hK' : (32:ℝ) ≤ K := by exact_mod_cast hK
      push_cast
      have hx := mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ (K:ℝ)+1)
      linarith
  calc
    _ ≤ (n:ℝ)*K := mul_le_mul_of_nonneg_left hlog hnr.le
    _ ≤ (3*(Fintype.card (L n) : ℝ))*K := mul_le_mul_of_nonneg_right hl (by positivity)
    _ = (Fintype.card (L n) : ℝ)*(3*K) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

end AlonBlocks803

open scoped BigOperators
open Finset

namespace AlonBalanceProof

variable {A B I V : Type*}

/-- Balance bounds each degree by a fixed multiple of the average degree. -/
theorem degree_le_scaled_average [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {D : ℝ} (hD : 0 ≤ D) (hbal : G.IsBalanced D) (v : V) :
    (Fintype.card V : ℝ) * G.degree v ≤ D * (2 * G.edgeFinset.card) := by
  have hsum : Fintype.card V * G.minDegree ≤ 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    simpa using (Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => G.minDegree_le_degree x)
  have havg : (Fintype.card V : ℝ) * G.minDegree ≤ 2 * G.edgeFinset.card := by
    exact_mod_cast hsum
  have hdegree : (G.degree v : ℝ) ≤ G.maxDegree := by
    exact_mod_cast G.degree_le_maxDegree v
  calc
    (Fintype.card V : ℝ) * G.degree v ≤ (Fintype.card V : ℝ) * (D * G.minDegree) :=
      mul_le_mul_of_nonneg_left (hdegree.trans hbal) (by positivity)
    _ = D * ((Fintype.card V : ℝ) * G.minDegree) := by ring
    _ ≤ D * (2 * G.edgeFinset.card) := mul_le_mul_of_nonneg_left havg hD

/-- The edges into a set of right vertices are bounded by its cardinality times the degree bound. -/
theorem right_fiber_bound [DecidableEq B] (F : Finset (A × B)) (T : Finset B) (d : ℝ)
    (hdeg : ∀ b ∈ T, ((F.filter fun e => e.2 = b).card : ℝ) ≤ d) :
    ((F.filter fun e => e.2 ∈ T).card : ℝ) ≤ T.card * d := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter F T Prod.snd, Nat.cast_sum]
  simpa using Finset.sum_le_sum hdeg

/-- A block contributes at most one edge for each selected left vertex. -/
theorem middle_block_bound [DecidableEq A] [DecidableEq I] (F : Finset (A × B))
    (L : Finset A) (M : Finset I) (block : B → I)
    (hleft : ∀ e ∈ F, e.1 ∈ L)
    (hblock : ∀ e ∈ F, ∀ f ∈ F, e.1 = f.1 → block e.2 = block f.2 → e = f) :
    (F.filter fun e => block e.2 ∈ M).card ≤ L.card * M.card := by
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun e => (e.1, block e.2))
  · intro e he
    have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
    exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hleft e he'.1, he'.2⟩)
  · intro e he f hf h
    exact hblock e (Finset.mem_filter.mp (Finset.mem_coe.mp he)).1
      f (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).1
      (congrArg (fun x : A × I => x.1) h) (congrArg (fun x : A × I => x.2) h)

/-- Tiny blocks contribute at most half the edges when their total size is at most m / (4D). -/
theorem tiny_block_bound [DecidableEq B] (F : Finset (A × B)) (T : Finset B)
    {m D : ℝ} (hm : 0 < m) (hsize : 4 * D * T.card ≤ m)
    (hdeg : ∀ b ∈ T, ((F.filter fun e => e.2 = b).card : ℝ) * m ≤ D * (2 * F.card)) :
    ((F.filter fun e => e.2 ∈ T).card : ℝ) ≤ F.card / 2 := by
  have hcard := right_fiber_bound F T (D * (2 * F.card) / m)
    (fun b hb => (le_div_iff₀ hm).2 (hdeg b hb))
  apply (le_div_iff₀ (show (0 : ℝ) < 2 by norm_num)).2
  apply (le_of_mul_le_mul_right (a := m) ?_ hm)
  rw [← mul_div_assoc] at hcard
  have hscaled := (le_div_iff₀ hm).1 hcard
  have hbudget := mul_le_mul_of_nonneg_right hsize (show (0 : ℝ) ≤ F.card by positivity)
  nlinarith only [hscaled, hbudget]

/-- Combining the three block ranges absorbs the tiny-block contribution. -/
theorem split_edge_bound [DecidableEq A] [DecidableEq B] [DecidableEq I]
    (F : Finset (A × B)) (L : Finset A) (T U : Finset B) (M : Finset I) (block : B → I)
    {m D r : ℝ} (hm : 0 < m) (hleftSize : (L.card : ℝ) ≤ m)
    (hleft : ∀ e ∈ F, e.1 ∈ L)
    (hblock : ∀ e ∈ F, ∀ f ∈ F, e.1 = f.1 → block e.2 = block f.2 → e = f)
    (hcover : ∀ e ∈ F, e.2 ∈ T ∨ block e.2 ∈ M ∨ e.2 ∈ U)
    (htinySize : 4 * D * T.card ≤ m)
    (hdeg : ∀ b ∈ T, ((F.filter fun e => e.2 = b).card : ℝ) * m ≤ D * (2 * F.card))
    (hlarge : ((F.filter fun e => e.2 ∈ U).card : ℝ) ≤ r * m) :
    (F.card : ℝ) ≤ 2 * m * ((M.card : ℝ) + r) := by
  let FT := F.filter fun e => e.2 ∈ T
  let FM := F.filter fun e => block e.2 ∈ M
  let FU := F.filter fun e => e.2 ∈ U
  have hunion : F ⊆ FT ∪ (FM ∪ FU) := by
    intro e he
    simpa [FT, FM, FU, Finset.mem_union, Finset.mem_filter, he] using hcover e he
  have hcards : F.card ≤ FT.card + (FM.card + FU.card) :=
    (Finset.card_le_card hunion).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  have htotal : (F.card : ℝ) ≤ (FT.card : ℝ) + ((FM.card : ℝ) + FU.card) := by
    exact_mod_cast hcards
  have htiny : (FT.card : ℝ) ≤ F.card / 2 :=
    tiny_block_bound F T hm htinySize hdeg
  have hmids : (FM.card : ℝ) ≤ (L.card : ℝ) * M.card := by
    exact_mod_cast middle_block_bound F L M block hleft hblock
  have hmid : (FM.card : ℝ) ≤ m * M.card :=
    hmids.trans (mul_le_mul_of_nonneg_right hleftSize (by positivity))
  change (FU.card : ℝ) ≤ r * m at hlarge
  nlinarith only [htotal, htiny, hmid, hlarge]

end AlonBalanceProof

open Finset SimpleGraph
open scoped Classical

namespace AlonBalanceProof

noncomputable section

variable {A I V : Type*} (B : I → Type*) (g : (j : A × I) → B j.2)

/-- Each left vertex chooses one right vertex in each block. -/
def choiceGraph : SimpleGraph (A ⊕ Sigma B) where
  Adj
    | .inl a, .inr b => g (a, b.1) = b.2
    | .inr b, .inl a => g (a, b.1) = b.2
    | _, _ => False
  symm.symm x y h := by cases x <;> cases y <;> exact h
  loopless.irrefl x := by cases x <;> exact not_false

section Subgraphs

variable [Fintype A] [Fintype (Sigma B)] [Fintype V]
  (f : (A ⊕ Sigma B) ↪ V) (H : ((choiceGraph B g).map f).Subgraph)

def orientedEdges : Finset (A × Sigma B) :=
  univ.filter fun e => H.Adj (f (.inl e.1)) (f (.inr e.2))

omit [Fintype V] in
theorem mem_orientedEdges (e : A × Sigma B) :
    e ∈ orientedEdges B g f H ↔ H.Adj (f (.inl e.1)) (f (.inr e.2)) := by
  simp [orientedEdges]

omit [Fintype V] in
theorem realizes_of_mem_orientedEdges {e : A × Sigma B}
    (he : e ∈ orientedEdges B g f H) : g (e.1, e.2.1) = e.2.2 :=
  map_adj_apply.mp ((mem_orientedEdges B g f H e).mp he).adj_sub

theorem orientedEdges_card :
    (orientedEdges B g f H).card = H.edgeSet.ncard := by
  let toEdge (e : ↥(orientedEdges B g f H)) : H.edgeSet :=
    ⟨s(f (.inl e.val.1), f (.inr e.val.2)), (mem_orientedEdges B g f H e.val).mp e.property⟩
  have hi : Function.Injective toEdge := by
    intro e e' h
    have h' := Sym2.eq_iff.mp (congrArg Subtype.val h)
    apply Subtype.ext
    rcases h' with ⟨ha, hb⟩ | ⟨ha, _⟩
    · exact Prod.ext (Sum.inl.inj (f.injective ha)) (Sum.inr.inj (f.injective hb))
    · cases f.injective ha
  have hs : Function.Surjective toEdge := by
    rintro ⟨e,he⟩
    induction e using Sym2.ind with
    | h u v =>
      have huv : H.Adj u v := Subgraph.mem_edgeSet.mp he
      obtain ⟨x, y, hxy, rfl, rfl⟩ := (SimpleGraph.map_adj f _ u v).mp huv.adj_sub
      cases x with
      | inl a =>
        cases y with
        | inl a' => exact False.elim hxy
        | inr b =>
          exact ⟨⟨(a,b), (mem_orientedEdges B g f H _).2 huv⟩, rfl⟩
      | inr b =>
        cases y with
        | inl a =>
          exact ⟨⟨(a,b), (mem_orientedEdges B g f H _).2 huv.symm⟩,
            Subtype.ext (Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩))⟩
        | inr b' => exact False.elim hxy
  simpa only [Fintype.card_coe, Set.fintypeCard_eq_ncard] using
    Fintype.card_congr (Equiv.ofBijective toEdge ⟨hi, hs⟩)

def leftVertices : Finset A := univ.filter fun a => f (.inl a) ∈ H.verts

def rightVertices : Finset (Sigma B) := univ.filter fun b => f (.inr b) ∈ H.verts

omit [Fintype V] in
theorem left_mem_of_mem_orientedEdges {e : A × Sigma B}
    (he : e ∈ orientedEdges B g f H) : e.1 ∈ leftVertices B g f H := by
  simpa [leftVertices] using ((mem_orientedEdges B g f H e).mp he).fst_mem

omit [Fintype V] in
theorem right_mem_of_mem_orientedEdges {e : A × Sigma B}
    (he : e ∈ orientedEdges B g f H) : e.2 ∈ rightVertices B g f H := by
  simpa [rightVertices] using ((mem_orientedEdges B g f H e).mp he).snd_mem

omit [Fintype (Sigma B)] in
theorem leftVertices_card_le : (leftVertices B g f H).card ≤ H.verts.ncard := by
  rw [Set.ncard_eq_toFinset_card]
  exact card_le_card_of_injOn (fun a => f (.inl a))
    (by intro a ha; simpa [leftVertices] using ha)
    (fun a _ a' _ h => Sum.inl.inj (f.injective h))

omit [Fintype A] in
theorem rightVertices_card_le : (rightVertices B g f H).card ≤ H.verts.ncard := by
  rw [Set.ncard_eq_toFinset_card]
  exact card_le_card_of_injOn (fun b => f (.inr b))
    (by intro b hb; simpa [rightVertices] using hb)
    (fun b _ b' _ h => Sum.inr.inj (f.injective h))

omit [Fintype V] in
theorem orientedEdges_subrectangle {b : A × Sigma B}
    (he : b ∈ orientedEdges B g f H) :
    b ∈ (leftVertices B g f H ×ˢ rightVertices B g f H).filter
      (fun e => g (e.1, e.2.1) = e.2.2) :=
  mem_filter.mpr ⟨mem_product.mpr ⟨left_mem_of_mem_orientedEdges B g f H he,
    right_mem_of_mem_orientedEdges B g f H he⟩, realizes_of_mem_orientedEdges B g f H he⟩

omit [Fintype V] in
theorem orientedEdges_block_injective {e e' : A × Sigma B}
    (he : e ∈ orientedEdges B g f H) (he' : e' ∈ orientedEdges B g f H)
    (ha : e.1 = e'.1) (hb : e.2.1 = e'.2.1) : e = e' := by
  rcases e with ⟨a,i,b⟩
  rcases e' with ⟨a',i',b'⟩
  dsimp at ha hb
  subst a' i'
  have h₁ : g (a,i) = b := realizes_of_mem_orientedEdges B g f H (e := (a,⟨i,b⟩)) he
  have h₂ : g (a,i) = b' := realizes_of_mem_orientedEdges B g f H (e := (a,⟨i,b'⟩)) he'
  have hbb := h₁.symm.trans h₂
  rw [hbb]

theorem orientedEdges_fiber_le_degree [DecidableEq (Sigma B)] {b : Sigma B} (hb : f (.inr b) ∈ H.verts) :
    ((orientedEdges B g f H).filter fun e => e.2 = b).card ≤
      H.coe.degree ⟨f (.inr b), hb⟩ := by
  let T := (orientedEdges B g f H).filter fun e => e.2 = b
  let v : H.verts := ⟨f (.inr b),hb⟩
  let toNeighbor (e : T) : H.coe.neighborSet v := by
    have he := mem_filter.mp e.property
    have h := (mem_orientedEdges B g f H e.val).mp he.1
    refine ⟨⟨f (.inl e.val.1), h.fst_mem⟩, ?_⟩
    change H.Adj (f (.inr b)) (f (.inl e.val.1))
    rw [← he.2]
    exact h.symm
  have hi : Function.Injective toNeighbor := by
    intro e e' h
    have hh := congrArg (fun p : H.coe.neighborSet v => p.val.val) h
    change f (.inl e.val.1) = f (.inl e'.val.1) at hh
    have ha : e.val.1 = e'.val.1 := Sum.inl.inj (f.injective hh)
    have hb' : e.val.2 = e'.val.2 :=
      (mem_filter.mp e.property).2.trans (mem_filter.mp e'.property).2.symm
    exact Subtype.ext (Prod.ext ha hb')
  simpa only [T, Fintype.card_coe, SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective toNeighbor hi

end Subgraphs

theorem coe_edgeFinset_card {G : SimpleGraph V} [Fintype V] (H : G.Subgraph) :
    H.coe.edgeFinset.card = H.edgeSet.ncard := by
  rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard, ← H.image_coe_edgeSet_coe]
  exact ((Sym2.map.injective (f := (Subtype.val : H.verts → V))
    Subtype.val_injective).injOn.ncard_image).symm

theorem choiceGraph_map_ncard [Fintype A] [Fintype I] [Fintype (Sigma B)] [Fintype V]
    (f : (A ⊕ Sigma B) ↪ V) :
    ((choiceGraph B g).map f).edgeSet.ncard = Fintype.card A * Fintype.card I := by
  let H : ((choiceGraph B g).map f).Subgraph := ⊤
  rw [← Subgraph.edgeSet_top, ← orientedEdges_card B g f H]
  let append (j : A × I) : A × Sigma B := (j.1, ⟨j.2, g j⟩)
  have h : (univ : Finset (A × I)).image append = orientedEdges B g f H := by
    ext e
    constructor
    · intro he
      obtain ⟨j, _, rfl⟩ := mem_image.mp he
      exact (mem_orientedEdges B g f H _).mpr (Subgraph.top_adj.mpr (map_adj_apply.mpr rfl))
    · intro he
      refine mem_image.mpr ⟨(e.1,e.2.1), mem_univ _, ?_⟩
      have hs := realizes_of_mem_orientedEdges B g f H he
      rcases e with ⟨a,i,b⟩
      change g (a,i) = b at hs
      change (a, (⟨i, g (a,i)⟩ : Sigma B)) = (a,⟨i,b⟩)
      rw [hs]
  rw [← h, card_image_of_injective]
  · simp
  · intro i j h
    exact congrArg (fun e : A × Sigma B => (e.1,e.2.1)) h

end

end AlonBalanceProof

open Finset Real
open scoped BigOperators Classical

namespace AlonBalanceProof

abbrev DyadicIndex (J : Finset ℕ) := Fin 8 × ↥J
abbrev DyadicBlock (J : Finset ℕ) (i : DyadicIndex J) := Fin (2 ^ i.2.val)

def tiny (J : Finset ℕ) (q : ℕ) : Finset (Sigma (DyadicBlock J)) :=
  univ.filter fun b => b.1.2.val < q

def middle (J : Finset ℕ) (q p : ℕ) : Finset (DyadicIndex J) :=
  univ.filter fun i => q ≤ i.2.val ∧ i.2.val < p

def large (J : Finset ℕ) (p : ℕ) : Finset (Sigma (DyadicBlock J)) :=
  univ.filter fun b => p ≤ b.1.2.val

private theorem two_geom_le (q : ℕ) : (∑ i ∈ range q, (2 : ℕ)^i) ≤ 2^q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_range_succ, pow_succ]
    omega

theorem tiny_card (J : Finset ℕ) (q : ℕ) : (tiny J q).card ≤ 8 * 2^q := by
  let toBlock (e : ↥(tiny J q)) : Fin 8 × (Σ k : Fin q, Fin (2 ^ k.val)) :=
    let hk : e.val.1.2.val < q := (mem_filter.mp e.property).2
    (e.val.1.1, ⟨⟨e.val.1.2.val, hk⟩, e.val.2⟩)
  have hi : Function.Injective toBlock := by
    rintro ⟨⟨⟨a,k⟩,x⟩,hx⟩ ⟨⟨⟨a',k'⟩,x'⟩,hx'⟩ h
    have ha : a = a' := congrArg (fun z : Fin 8 × (Σ k : Fin q, Fin (2 ^ k.val)) => z.1) h
    have hk : k = k' := Subtype.ext (congrArg
      (fun z : Fin 8 × (Σ k : Fin q, Fin (2 ^ k.val)) => z.2.1.val) h)
    subst a' k'
    have hxx : x = x' := by
      simpa only [toBlock, Prod.mk.injEq, Sigma.mk.injEq, true_and, heq_eq_eq] using h
    subst x'
    rfl
  have h := Fintype.card_le_of_injective toBlock hi
  simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma,
    Fin.sum_univ_eq_sum_range] at h
  exact h.trans (Nat.mul_le_mul_left _ (two_geom_le q))

theorem middle_card (J : Finset ℕ) (q p : ℕ) :
    (middle J q p).card ≤ 8 * (p - q) := by
  let toIndex (i : ↥(middle J q p)) : Fin 8 × ↥(Ico q p) :=
    (i.val.1, ⟨i.val.2.val, mem_Ico.mpr (mem_filter.mp i.property).2⟩)
  have hi : Function.Injective toIndex := by
    intro i j h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z : Fin 8 × ↥(Ico q p) => z.1) h)
      (Subtype.ext (congrArg (fun z : Fin 8 × ↥(Ico q p) => z.2.val) h))
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, Nat.card_Ico] using
    Fintype.card_le_of_injective toIndex hi

theorem tiny_budget (J : Finset ℕ) (m t : ℕ) (hm : m ≠ 0) (D : ℝ) (hD : 0 ≤ D)
    (hDpow : 32 * D ≤ (2 : ℝ)^t) :
    4 * D * (tiny J (Nat.log 2 m - t)).card ≤ (m : ℝ) := by
  let l := Nat.log 2 m
  change 4 * D * (tiny J (l-t)).card ≤ (m : ℝ)
  by_cases h : t ≤ l
  · have hcard : ((tiny J (l-t)).card : ℝ) ≤ 8* (2:ℝ)^(l-t) := by
      exact_mod_cast tiny_card J (l-t)
    have hp : (2 : ℝ)^l ≤ (m : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hm
    calc
      _ ≤ 4 * D * (8 * (2:ℝ)^(l-t)) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = (32 * D) * (2:ℝ)^(l-t) := by ring
      _ ≤ (2:ℝ)^t * (2:ℝ)^(l-t) := mul_le_mul_of_nonneg_right hDpow (by positivity)
      _ = (2 : ℝ)^l := by rw [← pow_add, Nat.add_sub_of_le h]
      _ ≤ _ := hp
  · have ht : tiny J (l-t) = ∅ := by simp [tiny, Nat.sub_eq_zero_of_le (Nat.le_of_not_ge h)]
    simp [ht]

theorem covered_by_ranges (J : Finset ℕ) (q p : ℕ) (b : Sigma (DyadicBlock J)) :
    b ∈ tiny J q ∨ b.1 ∈ middle J q p ∨ b ∈ large J p := by
  simp only [tiny, middle, large, mem_filter, mem_univ, true_and]
  omega

theorem large_enough (J : Finset ℕ) (m r : ℕ) (b : Sigma (DyadicBlock J))
    (hb : b ∈ large J (Nat.log 2 m + r + 1)) :
    m * 2^r ≤ Fintype.card (DyadicBlock J b.1) := by
  have hb' := (mem_filter.mp hb).2
  have hm := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) m
  have hshift : (Nat.log 2 m).succ + r ≤ b.1.2.val := by
    change Nat.log 2 m + r + 1 ≤ b.1.2.val at hb'
    omega
  rw [Fintype.card_fin]
  calc
    _ ≤ 2^(Nat.log 2 m).succ * 2^r := Nat.mul_le_mul_right _ hm.le
    _ = 2^((Nat.log 2 m).succ+r) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hshift

end AlonBalanceProof

open Finset Real
open scoped BigOperators Classical

namespace AlonBalanceProof

theorem threshold_le_log (K m t : ℕ) (hK : 32 ≤ K) (hKt : 32 * (t+1)^2 ≤ K)
    (hm : 2^(K/8) < m) :
    (32 + 8 * (Nat.sqrt K : ℝ) ≤ 80 * √(log (m : ℝ))) ∧
    ((t : ℝ) + 1 ≤ √(log (m : ℝ))) := by
  have h2 : (1/2 : ℝ) ≤ log 2 := (by norm_num : (1/2 : ℝ) ≤ 0.6931471803).trans log_two_gt_d9.le
  have hpow : (2 : ℝ)^(K/8) ≤ (m : ℝ) := by exact_mod_cast hm.le
  have hlog := log_le_log (by positivity) hpow
  rw [log_pow] at hlog
  have hceil : (K : ℝ) ≤ 16 * ((K/8 : ℕ) : ℝ) := by
    exact_mod_cast (show K ≤ 16 * (K/8) by omega)
  have hlog2 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ ((K/8 : ℕ) : ℝ) by positivity)
  have hKlog : (K : ℝ) ≤ 32 * log (m : ℝ) := by linarith only [hceil,hlog,hlog2]
  have hKreal : (32 : ℝ) ≤ K := by exact_mod_cast hK
  have hlogpos : 1 ≤ log (m : ℝ) := by linarith
  have hroot : 1 ≤ √(log (m : ℝ)) := Real.one_le_sqrt.mpr hlogpos
  have hnatroot : (Nat.sqrt K : ℝ)^2 ≤ (K : ℝ) := by
    exact_mod_cast Nat.sqrt_le' K
  have hh : (Nat.sqrt K : ℝ) ≤ 6 * √(log (m : ℝ)) := by
    have hpowroot : (6 * √(log (m : ℝ)))^2 = 36 * log (m : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      norm_num
    apply le_of_sq_le_sq _ (by positivity : 0 ≤ 6 * √(log (m : ℝ)))
    linarith only [hnatroot,hpowroot,hKlog,hlogpos]
  refine ⟨by linarith only [hh, hroot], Real.le_sqrt_of_sq_le ?_⟩
  have hKt' : (32 : ℝ) * ((t : ℝ)+1)^2 ≤ (K : ℝ) := by exact_mod_cast hKt
  linarith only [hKt',hKlog]

theorem small_sqrt_log (m : ℕ) (hm : 2 ≤ m) : (1/2 : ℝ) ≤ √(log (m : ℝ)) := by
  apply Real.le_sqrt_of_sq_le
  have h : log 2 ≤ log (m : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hm)
  linarith only [log_two_gt_d9, h]

end AlonBalanceProof

open Filter AlonBalanceProof AlonRandom803 AlonBlocks803 in
/-- Alon's dyadic random bipartite construction gives the balanced-subgraph bound. -/
theorem OMA.solution : type_of% @Erdos803.erdos_803.variants.alon := by
  classical
  refine ⟨2000, fun D hD => ?_⟩
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (32 * D) (by norm_num : (1:ℝ) < 2)
  let K₀ := max 32 (32 * (t+1)^2)
  refine eventually_atTop.mpr ⟨2^K₀, fun n hn => ?_⟩
  let K := Nat.log 2 n
  have hK₀ : K₀ ≤ K := Nat.le_log_of_pow_le (by decide) hn
  have hK : 32 ≤ K := (le_max_left _ _).trans hK₀
  have hKt : 32 * (t+1)^2 ≤ K := (le_max_right _ _).trans hK₀
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hN : 2^K ≤ n := Nat.pow_log_le_self 2 hnpos.ne'
  have hnUpper : n ≤ 2^(K+1) := (Nat.lt_pow_succ_log_self (by decide) n).le
  have hK4 : 4 ≤ K := by omega
  let _ : ∀ i : I K, Nonempty (B K i) := fun i => ⟨⟨0, by positivity⟩⟩
  have hA : Fintype.card (L n) ≤ 2^(K+1) := by
    simp only [L, Fintype.card_fin]
    omega
  have hB : Fintype.card (Sigma (B K)) ≤ 2^(K+1) :=
    (card_right K n hK4 hN).trans (by omega)
  obtain ⟨g, hg⟩ := exists_good (A := L n) (B K) n hK hA hB (min_block K)
  let f := embedding K n hK4 hN
  refine ⟨(choiceGraph (B K) g).map f, ?_, ?_⟩
  · rw [choiceGraph_map_ncard, Nat.cast_mul]
    exact enough_edges K n hK hN hnUpper
  intro H hbal
  let m := H.verts.ncard
  have hmN : m ≤ n := by
    simpa only [m, Nat.card_eq_fintype_card, Fintype.card_fin] using
      Set.ncard_le_card H.verts
  have hlogD : 0 ≤ log D := (Real.log_pos hD).le
  change (H.edgeSet.ncard : ℝ) ≤ 2000 * ((m : ℝ) * √(log (m : ℝ)) + log D)
  by_cases hm2 : m < 2
  · have hcard := H.coe.card_edgeFinset_le_card_choose_two
    rw [coe_edgeFinset_card, Set.fintypeCard_eq_ncard, Nat.choose_eq_zero_of_lt hm2] at hcard
    rw [Nat.le_zero.mp hcard, Nat.cast_zero]
    positivity
  have hm : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  let F := orientedEdges (B K) g f H
  let P := leftVertices (B K) g f H
  let Q := rightVertices (B K) g f H
  have hEc : F.card = H.edgeSet.ncard := orientedEdges_card (B K) g f H
  have hP : P.card ≤ m := leftVertices_card_le (B K) g f H
  have hQ : Q.card ≤ m := rightVertices_card_le (B K) g f H
  have hgood := hg m (mem_Icc.mpr ⟨hm,hmN⟩) P Q hP hQ
  have hsub {e : L n × Sigma (B K)} (he : e ∈ F) :
      e ∈ edges (B K) g P Q :=
    orientedEdges_subrectangle (B K) g f H he
  rw [← hEc]
  by_cases hsmall : m ≤ cutoff K
  · have hbound : (F.card : ℝ) ≤ 32 * (m : ℝ) := by
      exact_mod_cast (card_le_card (fun _ he => hsub he)).trans (hgood.1 hsmall)
    have hsqrt := small_sqrt_log m (by omega)
    have hp := mul_le_mul_of_nonneg_left hsqrt hmR.le
    linarith only [hbound, hp, hlogD]
  let r := threshold K
  let J := Ico (K/2) (K-4)
  let q := Nat.log 2 m - t
  let p := Nat.log 2 m + r + 1
  let T := tiny J q
  let M := middle J q p
  let U := large J p
  have hlargeN : (F.filter fun e => e.2 ∈ U).card ≤ r * m := by
    refine (card_le_card ?_).trans (hgood.2 (Nat.lt_of_not_ge hsmall))
    intro e he
    obtain ⟨heF,heU⟩ := mem_filter.mp he
    have he' := mem_filter.mp (hsub heF)
    have hmem := mem_product.mp he'.1
    refine mem_filter.mpr ⟨mem_product.mpr ⟨hmem.1, mem_filter.mpr ⟨hmem.2, ?_⟩⟩, he'.2⟩
    exact large_enough J m r e.2 heU
  have hlarge : ((F.filter fun e => e.2 ∈ U).card : ℝ) ≤ (r : ℝ) * m := by
    exact_mod_cast hlargeN
  have hdeg (b : Sigma (B K)) (_ : b ∈ T) :
      ((F.filter fun e => e.2 = b).card : ℝ) * m ≤ D * (2 * F.card) := by
    by_cases hb : f (.inr b) ∈ H.verts
    · let v : H.verts := ⟨f (.inr b), hb⟩
      have hfiberN : (F.filter fun e => e.2 = b).card ≤ (H.coe.neighborSet v).ncard := by
        simpa only [F, v, ← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using
          orientedEdges_fiber_le_degree (B K) g f H hb
      have hfiber : ((F.filter fun e => e.2 = b).card : ℝ) ≤ (H.coe.neighborSet v).ncard :=
        Nat.cast_le.mpr hfiberN
      have havg := degree_le_scaled_average H.coe (by linarith : 0 ≤ D) hbal v
      rw [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard,
        coe_edgeFinset_card, ← hEc, ← show m = H.verts.ncard from rfl] at havg
      rw [mul_comm _ (m : ℝ)]
      exact (mul_le_mul_of_nonneg_left hfiber hmR.le).trans havg
    · have hzero : (F.filter fun e => e.2 = b) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro e he
        obtain ⟨heF, rfl⟩ := mem_filter.mp he
        exact hb ((mem_orientedEdges (B K) g f H e).mp heF).snd_mem
      rw [hzero]
      simp only [card_empty, Nat.cast_zero, zero_mul]
      positivity
  have hT := tiny_budget J m t hm.ne' D (by linarith) ht.le
  have hP' : (P.card : ℝ) ≤ m := by exact_mod_cast hP
  have hsplit : (F.card : ℝ) ≤ 2 * m * ((M.card : ℝ) + r) :=
    split_edge_bound F P T U M (fun b => b.1) hmR hP'
      (fun _ he => left_mem_of_mem_orientedEdges (B K) g f H he)
      (fun _ he _ he' => orientedEdges_block_injective (B K) g f H he he')
      (fun e _ => covered_by_ranges J q p e.2) hT hdeg hlarge
  have hM : M.card ≤ 8 * (t+r+1) :=
    (middle_card J q p).trans (Nat.mul_le_mul_left _ (by dsimp [p,q]; omega))
  have hMreal : (M.card : ℝ) ≤ 8 * ((t : ℝ) + r + 1) := by exact_mod_cast hM
  obtain ⟨hr, htlog⟩ := threshold_le_log K m t hK hKt (Nat.lt_of_not_ge hsmall)
  have hrt : (r : ℝ) ≤ 80 * √(log (m : ℝ)) := by
    simpa only [r, threshold, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hr
  have hMlog : (M.card : ℝ) + r ≤ 728 * √(log (m : ℝ)) := by
    linarith only [hMreal, hrt, htlog]
  have he := mul_le_mul_of_nonneg_left hMlog (show 0 ≤ 2 * (m : ℝ) by positivity)
  have hz : 0 ≤ (m : ℝ) * √(log (m : ℝ)) := by positivity
  linarith only [hsplit, he, hz, hlogD]