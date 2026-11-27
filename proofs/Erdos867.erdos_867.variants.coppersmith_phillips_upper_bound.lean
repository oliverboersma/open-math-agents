import FormalConjectures.ErdosProblems.«867»

/-!
# Consecutive-sum-free sets: a strict improvement on the dyadic bound

Coppersmith and Phillips, *On a question of Erdős on subsequence sums*,
SIAM Journal on Discrete Mathematics 9 (1996), 173–177,
doi:10.1137/S0895480193244139, distinguish holes coming from consecutive
pairs from other missing values and count them in alternating dyadic layers.

Here an independent finite obstruction gives a saving of N/480 up to a
constant in seven pairs of layers, sufficient for the specified error.
The six local windows have centers t, 3t, 4t, 12t, 16t, and 48t.
Every consecutive run of a prescribed membership pattern forbids its sum.
Two sums of adjacent pairs differ by at least two, and attaining that
minimum determines three consecutive selected integers at half the scale.
The finite checks below combine exactly these rules. The Boolean
refutation is checked by reverse unit propagation in the kernel.
-/

/-! Counting members and unforced holes in adjacent dyadic layers. -/

open Finset
namespace OMA.CP867

def AdjPair (A : Finset ℕ) (a b : ℕ) : Prop :=
  a ∈ A ∧ b ∈ A ∧ a < b ∧ ∀ z ∈ A, a < z → z < b → False

def Forced (A : Finset ℕ) (z : ℕ) : Prop :=
  ∃ a b, AdjPair A a b ∧ a + b = z

def Hole (A : Finset ℕ) (z : ℕ) : Prop :=
  z ∉ A ∧ ¬ Forced A z

theorem forced_out {A : Finset ℕ} (hA : Erdos867.ConsecutiveSumFree A)
    {n : ℕ} (hn : Forced A n) : n ∉ A := by
  obtain ⟨a,b,⟨ha,hb,hab,he⟩,rfl⟩ := hn
  have heq : Icc a b ∩ A = {a,b} := by
    ext z
    simp only [mem_inter, mem_Icc, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨haz,hzb⟩,hz⟩
      by_contra! hn
      exact he z hz (by omega) (by omega)
    · rintro (rfl|rfl) <;> simp [ha,hb,hab.le]
  have h := hA a b
  simpa [heq,hab.ne] using h

theorem pair_separate {A : Finset ℕ} {a b c d : ℕ}
    (h : AdjPair A a b) (g : AdjPair A c d) (hlt : a+b < c+d) :
    b ≤ c := by
  obtain ⟨ha,hb,hab,he⟩ := h
  obtain ⟨hc,hd,hcd,hf⟩ := g
  by_contra! hn
  by_cases hca : a < c
  · exact he c hc hca hn
  by_cases hbd : c < b ∧ b < d
  · exact hf b hb hbd.1 hbd.2
  omega

theorem not_adjacent_forced {A : Finset ℕ} {n : ℕ}
    (h : Forced A n) : ¬ Forced A (n+1) := by
  obtain ⟨a,b,p,rfl⟩ := h
  rintro ⟨c,d,q,e⟩
  have := pair_separate p q (by omega)
  have := p.2.2.1
  have := q.2.2.1
  omega

theorem two_apart {A : Finset ℕ} {n : ℕ}
    (h : Forced A n) (g : Forced A (n+2)) :
    ∃ a, n=2*a+1 ∧ a∈A ∧ a+1∈A ∧ a+2∈A := by
  obtain ⟨a,b,p,rfl⟩ := h
  obtain ⟨c,d,q,e⟩ := g
  have := pair_separate p q (by omega)
  have := p.2.2.1
  have := q.2.2.1
  have hb : b=a+1 := by omega
  have hd : d=a+2 := by omega
  exact ⟨a,by omega,p.1,hb ▸ p.2.1,hd ▸ q.2.1⟩

noncomputable def holes (A : Finset ℕ) (lo hi : ℕ) : Finset ℕ := by
  classical exact (Ioc lo hi).filter (Hole A)

def mass (A : Finset ℕ) (n : ℕ) : ℕ := (A.filter (· ≤ n)).card

theorem pair_layer (A : Finset ℕ) (hA : Erdos867.ConsecutiveSumFree A) (n : ℕ) :
    mass A n + (holes A (n/2) n).card ≤ mass A (n/4) + (n-n/2) + 1 := by
  classical
  let S := (Ioc (n/4) (n/2)) ∩ A
  let T := (Ioc (n/2) n) ∩ A
  let U := holes A (n/2) n
  let F := (Ioc (n/2) n).filter (Forced A)
  have hadd (l m : ℕ) (hlm : l ≤ m) :
      mass A m = mass A l + ((Ioc l m) ∩ A).card := by
    have e : A.filter (· ≤ m) = A.filter (· ≤ l) ∪ (Ioc l m ∩ A) := by
      ext z
      simp only [mem_filter, mem_union, mem_inter, mem_Ioc]
      by_cases ha : z ∈ A <;> simp [ha]; omega
    unfold mass
    rw [e, card_union_of_disjoint]
    exact disjoint_left.mpr (fun z hz hz' =>
      (mem_Ioc.mp (mem_inter.mp hz').1).1.not_ge (mem_filter.mp hz).2)
  have hpart : T.card + U.card + F.card ≤ n-n/2 := by
    have ht : Disjoint T U := disjoint_left.mpr (fun z hz hu =>
      (mem_filter.mp hu).2.1 (mem_inter.mp hz).2)
    have hf : Disjoint (T∪U) F := by
      refine disjoint_left.mpr ?_
      intro z hz h
      rcases mem_union.mp hz with hz|hz
      · exact forced_out hA (mem_filter.mp h).2 (mem_inter.mp hz).2
      · exact (mem_filter.mp hz).2.2 (mem_filter.mp h).2
    rw [← card_union_of_disjoint ht, ← card_union_of_disjoint hf, ← Nat.card_Ioc]
    apply card_le_card
    intro z hz
    rcases mem_union.mp hz with h|h
    · rcases mem_union.mp h with h|h
      · exact (mem_inter.mp h).1
      · exact (mem_filter.mp h).1
    · exact (mem_filter.mp h).1
  have hF : S.card ≤ F.card + 1 := by
    cases hs : S.card with
    | zero => omega
    | succ k =>
      let q := S.orderEmbOfFin hs
      let f (i : Fin k) := q i.castSucc + q i.succ
      have qmem (i : Fin (k+1)) : q i ∈ S := S.orderEmbOfFin_mem hs i
      have qbd (i : Fin (k+1)) := mem_Ioc.mp (mem_inter.mp (qmem i)).1
      have mono : StrictMono f := fun i j hij =>
        Nat.add_lt_add (q.strictMono (Fin.castSucc_lt_castSucc_iff.mpr hij))
          (q.strictMono (Fin.succ_lt_succ_iff.mpr hij))
      have hf (i : Fin k) : f i ∈ F := by
        have hlt := q.strictMono (Fin.castSucc_lt_succ (i := i))
        have h₁ := qbd i.castSucc
        have h₂ := qbd i.succ
        refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨by dsimp [f]; omega, by dsimp [f]; omega⟩,
          q i.castSucc,q i.succ,⟨(mem_inter.mp (qmem _)).2,
            (mem_inter.mp (qmem _)).2,hlt,?_⟩,rfl⟩
        intro z hz h₃ h₄
        have hzS : z ∈ S := mem_inter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, hz⟩
        have hzr : z ∈ Set.range q := by rw [S.range_orderEmbOfFin hs]; exact hzS
        obtain ⟨j,rfl⟩ := hzr
        have hj₁ := q.lt_iff_lt.mp h₃
        have hj₂ := q.lt_iff_lt.mp h₄
        change i.val < j.val at hj₁
        change j.val < i.val+1 at hj₂
        omega
      have hc : (univ.image f).card ≤ F.card := card_le_card (by
        intro z hz
        obtain ⟨i,_,rfl⟩ := mem_image.mp hz
        exact hf i)
      rw [card_image_of_injective _ mono.injective, card_univ, Fintype.card_fin] at hc
      omega
  have h₁ := hadd (n/2) n (by omega)
  have h₂ := hadd (n/4) (n/2) (by omega)
  change mass A n = mass A (n/2) + T.card at h₁
  change mass A (n/2) = mass A (n/4) + S.card at h₂
  change mass A n + U.card ≤ _
  omega

noncomputable def window (A : Finset ℕ) (i t : ℕ) : Finset ℕ := by
  classical exact (Icc (i*t-(i+1)) (i*t+(i+1))).filter (Hole A)

private theorem card_of_width {S : Finset ℕ} {k : ℕ}
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≤ y+k) : S.card ≤ k+1 := by
  by_cases hn : S.Nonempty
  · calc S.card ≤ (Icc (S.min' hn) (S.min' hn+k)).card := card_le_card (by
          intro x hx
          exact mem_Icc.mpr ⟨S.min'_le x hx, h x hx _ (S.min'_mem _)⟩)
         _ = k+1 := by rw [Nat.card_Icc]; omega
  · simp [not_nonempty_iff_eq_empty.mp hn]

private theorem double_count (A T B : Finset ℕ) (i k : ℕ)
    (cover : ∀ t ∈ T, window A i t ⊆ B)
    (width : ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ window A i x, z ∈ window A i y → x ≤ y+k) :
    (∑ t ∈ T, (window A i t).card) ≤ B.card*(k+1) := by
  classical
  have hs (t : ℕ) (ht : t ∈ T) :
      (window A i t).card = ∑ z ∈ B, if z ∈ window A i t then 1 else 0 := by
    rw [sum_boole]
    congr 1
    ext z
    simp only [mem_filter]
    exact ⟨fun hz => ⟨cover t ht hz,hz⟩, And.right⟩
  calc
    _ = ∑ t ∈ T, ∑ z ∈ B, if z ∈ window A i t then 1 else 0 := sum_congr rfl hs
    _ = ∑ z ∈ B, ∑ t ∈ T, if z ∈ window A i t then 1 else 0 := sum_comm
    _ ≤ ∑ _z ∈ B, (k+1) := by
      refine sum_le_sum (fun z _ => ?_)
      rw [sum_boole]
      apply card_of_width
      intro x hx y hy
      obtain ⟨hx,hz⟩ := mem_filter.mp hx
      obtain ⟨hy,hyz⟩ := mem_filter.mp hy
      exact width x hx y hy z hz hyz
    _ = B.card*(k+1) := by simp

private theorem holes_split (A : Finset ℕ) {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    (holes A a b).card + (holes A b c).card = (holes A a c).card := by
  classical
  have hj : holes A a b ∪ holes A b c = holes A a c := by
    ext z
    simp only [holes, mem_union, mem_filter, mem_Ioc]
    by_cases h : Hole A z <;> simp [h]; omega
  rw [← hj, card_union_of_disjoint]
  apply disjoint_left.mpr
  intro z hz hz'
  have h := (mem_Ioc.mp (mem_filter.mp hz).1).2
  exact (mem_Ioc.mp (mem_filter.mp hz').1).1.not_ge h

def localCondition (A : Finset ℕ) : Prop :=
  ∀ t ≥ 3, 8 ≤ 3*(window A 1 t).card +
    5*((window A 3 t).card + (window A 4 t).card + (window A 12 t).card +
      (window A 16 t).card + (window A 48 t).card)

theorem period (A : Finset ℕ) (hA : Erdos867.ConsecutiveSumFree A)
    (h : localCondition A) (q : ℕ) (hq : 1 ≤ q) :
    15 * mass A (16384*q) ≤ 163333*q+168 := by
  classical
  let T := Icc (192*q+3) (256*q-3)
  have hcnt : T.card = 64*q-5 := by simp [T, Nat.card_Icc]; omega
  have hw (t i z : ℕ) (hz : z ∈ window A i t) :=
    mem_Icc.mp (mem_filter.mp hz).1
  have mk (i lo hi k : ℕ)
      (geo : ∀ t ∈ T, ∀ z, i*t-(i+1) ≤ z → z ≤ i*t+(i+1) → lo < z ∧ z ≤ hi)
      (width : ∀ x y z : ℕ, i*x-(i+1) ≤ z → z ≤ i*y+(i+1) → x ≤ y+k) :
      (∑ t ∈ T, (window A i t).card) ≤ (holes A lo hi).card*(k+1) := by
    apply double_count
    · intro t ht z hz
      exact mem_filter.mpr ⟨mem_Ioc.mpr (geo t ht _ (hw _ _ _ hz).1 (hw _ _ _ hz).2),
        (mem_filter.mp hz).2⟩
    · exact fun x _ y _ z hx hy => width x y z (hw _ _ _ hx).1 (hw _ _ _ hy).2
  have w₁ := mk 1 (128*q) (256*q) 4 (by
    intro t ht z h₁ h₂; have := mem_Icc.mp ht; omega) (by omega)
  have w₃ := mk 3 (512*q) (768*q) 2 (by
    intro t ht z h₁ h₂; have := mem_Icc.mp ht; omega) (by omega)
  have w₄ := mk 4 (768*q) (1024*q) 2 (by
    intro t ht z h₁ h₂; have := mem_Icc.mp ht; omega) (by omega)
  have w₁₂ := mk 12 (2048*q) (3072*q) 2 (by
    intro t ht z h₁ h₂; have := mem_Icc.mp ht; omega) (by omega)
  have w₁₆ := mk 16 (3072*q) (4096*q) 2 (by
    intro t ht z h₁ h₂; have := mem_Icc.mp ht; omega) (by omega)
  have w₄₈ := mk 48 (8192*q) (16384*q) 2 (by
    intro t ht z h₁ h₂; have := mem_Icc.mp ht; omega) (by omega)
  have hl := sum_le_sum (s := T) (fun t ht => h t (by have := mem_Icc.mp ht; omega))
  simp only [mul_add, sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, hcnt] at hl
  have s₁ := holes_split A (a := 512*q) (b := 768*q) (c := 1024*q) (by omega) (by omega)
  have s₂ := holes_split A (a := 2048*q) (b := 3072*q) (c := 4096*q) (by omega) (by omega)
  have layers (d : ℕ) := pair_layer A hA (4*d*q)
  have a₀ := layers 4096
  have a₁ := layers 1024
  have a₂ := layers 256
  have a₃ := layers 64
  have a₄ := layers 16
  have a₅ := layers 4
  have a₆ := layers 1
  have base : mass A q ≤ q+1 := by
    calc mass A q ≤ (Icc 0 q).card := card_le_card (by
           intro x hx; exact mem_Icc.mpr ⟨Nat.zero_le _, (mem_filter.mp hx).2⟩)
         _ = q+1 := by simp [Nat.card_Icc]
  norm_num [Nat.mul_div_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] at a₀ a₁ a₂ a₃ a₄ a₅ a₆
  simp only [Nat.mul_comm] at w₁ w₃ w₄ w₁₂ w₁₆ w₄₈ s₁ s₂ ⊢
  omega

theorem finish (H : ∀ A : Finset ℕ, Erdos867.ConsecutiveSumFree A → localCondition A) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ A ⊆ Icc 1 N, Erdos867.ConsecutiveSumFree A →
      (A.card : ℝ) ≤ (2/3-1/512)*(N : ℝ) + Real.log (N : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (200000000 : ℕ)] with N hn
  intro A hsub hA
  let q := N/16384+1
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hN : N ≤ 16384*q := by dsimp [q]; omega
  have hc : mass A (16384*q) = A.card := by
    unfold mass
    rw [filter_eq_self.mpr (fun x hx => (mem_Icc.mp (hsub hx)).2.trans hN)]
  have b := period A hA (H A hA) q hq
  rw [hc] at b
  have b' : A.card * 1536 ≤ 1021*N := by dsimp [q] at b; omega
  have br : (A.card : ℝ)*1536 ≤ 1021*N := by exact_mod_cast b'
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  linarith

end OMA.CP867

/-! The local finite constraints: interval sums, the minimum spacing of consecutive
pair sums, and the weighted count of unforced holes. -/

open Finset
namespace OMA.CP867

def literal (v : ℕ → Bool) (z : ℤ) : Bool :=
  if 0 < z then v z.natAbs else !(v z.natAbs)

def key (hole : Bool) (i s : ℕ) : ℕ :=
  (if hole then 16384 else 0) + 256*i+s+1

def pos (hole : Bool) (i s : ℕ) : ℤ := key hole i s

noncomputable def assignment (A : Finset ℕ) (b x : ℕ) : Bool := by
  classical
  let n := (x-1)%16384/256*b + (x-1)%256
  exact if x ≤ 16384 then decide (n∈A) else decide (Hole A n)

private theorem atKey (A : Finset ℕ) (b i s : ℕ) (hi : i<64) (hs : s<256) (k : Bool) :
    assignment A b (key k i s) =
      (if k then @decide (Hole A (i*b+s)) (Classical.propDecidable _) else decide (i*b+s∈A)) := by
  cases k <;> unfold assignment key <;> dsimp
  · have e : (256*i+s)%16384/256 = i := by omega
    simp [e, Nat.mod_eq_of_lt hs, show 256*i+s+1 ≤ 16384 by omega]
  · have e : (16384+256*i+s)%16384/256 = i := by omega
    have f : (16384+256*i+s)%256 = s := by omega
    simp [e,f,show ¬16384+256*i+s+1 ≤ 16384 by omega]

private theorem pos_pos (k : Bool) (i s : ℕ) : 0 < pos k i s := by
  dsimp [pos,key]; positivity

private theorem valPos (A : Finset ℕ) (b i s : ℕ) (hi : i<64) (hs : s<256) (k : Bool) :
    literal (assignment A b) (pos k i s) = true ↔ (if k then Hole A (i*b+s) else i*b+s∈A) := by
  rw [literal,if_pos (pos_pos ..)]
  change assignment A b (key k i s) = true ↔ _
  rw [atKey _ _ _ _ hi hs]
  cases k <;> simp

private theorem valNeg (A : Finset ℕ) (b i s : ℕ) (hi : i<64) (hs : s<256) (k : Bool) :
    literal (assignment A b) (-pos k i s) = true ↔ ¬(if k then Hole A (i*b+s) else i*b+s∈A) := by
  have e : literal (assignment A b) (-pos k i s) = !(literal (assignment A b) (pos k i s)) := by
    simp [literal,pos_pos,Int.natAbs_neg,(pos_pos k i s).le]
  rw [e,← valPos A b i s hi hs k]
  cases literal (assignment A b) (pos k i s) <;> simp

def offsets (a n mask : ℕ) : Finset ℕ :=
  (Ico a (a+n)).filter (fun x => mask.testBit (x-a))

def budgetCount (xs : List (ℕ × ℕ)) (i : ℕ) : Finset ℕ :=
  ((xs.filter (fun p => p.1 = i)).map Prod.snd).toFinset

def cost (f : ℕ → ℕ) : ℕ := 3*f 1+5*(f 3+f 4+f 12+f 16+f 48)

inductive Rule where
  | run (i a n mask : ℕ)
  | adj (i a : ℕ)
  | even (i a : ℕ)
  | lift (i a k : ℕ)
  | budget (xs : List (ℕ × ℕ))

def Rule.raw : Rule → List ℤ
  | .run i a n mask =>
    ((List.range' a n).map (fun s =>
      if mask.testBit (s-a) then -pos false i s else pos false i s)) ++
      [-pos false ((offsets a n mask).card*i) (∑ s ∈ offsets a n mask, s)]
  | .adj i a => [pos false i a, pos false i (a+1),pos true i a,pos true i (a+1)]
  | .even i a => [pos false i a, pos false i (a+2),pos true i a,pos true i (a+2)]
  | .lift i a k =>
    [pos false (2*i) (2*a+1),pos false (2*i) (2*a+3),
     pos true (2*i) (2*a+1),pos true (2*i) (2*a+3),pos false i (a+k)]
  | .budget xs => xs.map (fun p => -pos true p.1 p.2)

def Rule.clause (r : Rule) : List ℤ := (r.raw).insertionSort (· ≤ ·)

def Rule.valid (par : ℕ) : Rule → Bool
  | .run i a n mask =>
    let S := offsets a n mask
    decide (i<64 ∧ a+n≤256 ∧ 2≤S.card ∧ S.card*i<64 ∧ (∑ s ∈ S,s)<256)
  | .adj i a => decide (i<64 ∧ a+1<256)
  | .even i a => decide (i<64 ∧ a+2<256 ∧ (i*par+a)%2=0)
  | .lift i a k => decide (2*i<64 ∧ 2*a+3<256 ∧ k≤2)
  | .budget xs => xs.all (fun p => decide (p.1<64 ∧ p.2<256 ∧ p.1≤p.2+1 ∧ p.2≤3*p.1+1)) &&
      decide (8 ≤ cost (fun i => (budgetCount xs i).card))

private theorem budget_le {A : Finset ℕ} {b : ℕ} (xs : List (ℕ × ℕ))
    (hwin : ∀ p ∈ xs, p.1≤p.2+1 ∧ p.2≤3*p.1+1)
    (hm : ∀ p ∈ xs, Hole A (p.1*b+p.2)) (i : ℕ) :
    (budgetCount xs i).card ≤ (window A i (b+2)).card := by
  classical
  let S := budgetCount xs i
  let f (s : ℕ) := i*b+s
  have inj : Function.Injective f := by intro x y h; dsimp [f] at h; omega
  rw [← card_image_of_injective S inj]
  apply card_le_card
  intro x hx
  obtain ⟨s,hs,rfl⟩ := mem_image.mp hx
  have hss : (i,s) ∈ xs := by
    simp only [S, budgetCount, List.mem_toFinset, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hs
    obtain ⟨⟨u,v⟩,⟨hz,hui⟩,hvs⟩ := hs
    change u=i at hui
    change v=s at hvs
    simpa only [hui,hvs] using hz
  obtain ⟨h₁,h₂⟩ := hwin (i,s) hss
  change i ≤ s+1 at h₁
  change s≤3*i+1 at h₂
  refine mem_filter.mpr ⟨mem_Icc.mpr ?_,hm _ hss⟩
  dsimp [f]
  rw [Nat.mul_add]
  omega

private theorem run_forbid {A : Finset ℕ} (H : Erdos867.ConsecutiveSumFree A)
    (b i a n mask : ℕ) (hs : 2 ≤ (offsets a n mask).card)
    (bits : ∀ s, a ≤ s → s<a+n → (i*b+s∈A ↔ s∈offsets a n mask)) :
    (offsets a n mask).card*i*b + (∑ s ∈ offsets a n mask,s) ∉ A := by
  let S := offsets a n mask
  let f (s : ℕ) := i*b+s
  have inj : Function.Injective f := by intro x y h; dsimp [f] at h; omega
  have hn : 0<n := by
    by_contra! hn
    have : n=0 := by omega
    simp [this,offsets] at hs
  have eqn : Icc (i*b+a) (i*b+a+n-1) ∩ A = S.image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨hm,hn'⟩,hx⟩ := (mem_Icc.and Iff.rfl).mp (mem_inter.mp hx)
      have e : i*b+(x-i*b)=x := by omega
      refine mem_image.mpr ⟨x-i*b,(bits _ (by omega) (by omega)).mp (e.symm ▸ hx),e⟩
    · intro hx
      obtain ⟨s,hs,rfl⟩ := mem_image.mp hx
      have hh := mem_Ico.mp (mem_filter.mp hs).1
      exact mem_inter.mpr ⟨mem_Icc.mpr ⟨by dsimp [f]; omega,by dsimp [f]; omega⟩,
        (bits _ hh.1 hh.2).mpr hs⟩
  have hc := H (i*b+a) (i*b+a+n-1)
  rw [eqn,card_image_of_injective _ inj, sum_image (fun _ _ _ _ h => inj h)] at hc
  have he : ∑ s ∈ S, f s = S.card*i*b+∑ s ∈ S,s := by
    change (∑ s ∈ S, (i*b+s)) = _
    rw [sum_add_distrib, sum_const, smul_eq_mul, Nat.mul_assoc]
  rw [he] at hc
  exact hc hs

theorem rule_sound {A : Finset ℕ} (H : Erdos867.ConsecutiveSumFree A) (b par : ℕ)
    (hp : b%2=par) (hbudget : cost (fun i => (window A i (b+2)).card) < 8)
    (r : Rule) (hr : r.valid par = true) :
    r.clause.any (literal (assignment A b)) = true := by
  classical
  by_contra bad
  have hx (z : ℤ) (hz : z ∈ r.raw) : ¬ literal (assignment A b) z = true :=
    fun h => bad (List.any_eq_true.mpr ⟨z,(List.mem_insertionSort _).mpr hz,h⟩)
  have hpos (k : Bool) (i s : ℕ) (hi : i<64) (hs : s<256) (h : pos k i s ∈ r.raw) :
      ¬(if k then Hole A (i*b+s) else i*b+s ∈ A) :=
    fun hv => hx _ h ((valPos A b i s hi hs k).mpr hv)
  have hneg (k : Bool) (i s : ℕ) (hi : i<64) (hs : s<256) (h : -pos k i s ∈ r.raw) :
      (if k then Hole A (i*b+s) else i*b+s ∈ A) := by
    by_contra hv
    exact hx _ h ((valNeg A b i s hi hs k).mpr hv)
  have forced (i s : ℕ) (hi : i<64) (hs : s<256)
      (h₁ : pos false i s ∈ r.raw) (h₂ : pos true i s ∈ r.raw) : Forced A (i*b+s) := by
    by_contra hf
    exact hpos true i s hi hs h₂ ⟨hpos false i s hi hs h₁,hf⟩
  cases r with
  | run i a n mask =>
    obtain ⟨hi,hbound,hcard,hout,hout'⟩ := of_decide_eq_true hr
    have hb (s : ℕ) (h₁ : a ≤ s) (h₂ : s<a+n) :
        i*b+s ∈ A ↔ s ∈ offsets a n mask := by
      have hl : s ∈ List.range' a n := List.mem_range'_1.mpr ⟨h₁,h₂⟩
      have hm : (if mask.testBit (s-a) then -pos false i s else pos false i s) ∈
          (Rule.run i a n mask).raw := List.mem_append_left _ (List.mem_map_of_mem hl)
      cases hv : mask.testBit (s-a) with
      | true =>
        simp only [hv,if_true] at hm
        have hs : i*b+s ∈ A := hneg false i s hi (by omega) hm
        simp [offsets,hs,hv,h₁,h₂]
      | false =>
        simp only [hv,Bool.false_eq_true,if_false] at hm
        have hs : i*b+s ∉ A := hpos false i s hi (by omega) hm
        simp [offsets,hs,hv]
    have hs := hneg false _ _ hout hout' (by simp [Rule.raw])
    exact run_forbid H b i a n mask hcard hb hs
  | adj i a =>
    obtain ⟨hi,hs⟩ := of_decide_eq_true hr
    have h₁ := forced i a hi (by omega) (by simp [Rule.raw]) (by simp [Rule.raw])
    have h₂ := forced i (a+1) hi hs (by simp [Rule.raw]) (by simp [Rule.raw])
    exact not_adjacent_forced h₁ (by simpa only [Nat.add_assoc] using h₂)
  | even i a =>
    obtain ⟨hi,hs,he⟩ := of_decide_eq_true hr
    have h₁ := forced i a hi (by omega) (by simp [Rule.raw]) (by simp [Rule.raw])
    have h₂ := forced i (a+2) hi hs (by simp [Rule.raw]) (by simp [Rule.raw])
    obtain ⟨u,hu,_⟩ := two_apart h₁ (by simpa only [Nat.add_assoc] using h₂)
    have hmod : (i*b+a)%2=(i*par+a)%2 := by simp only [Nat.add_mod,Nat.mul_mod,← hp,Nat.mod_mod]
    omega
  | lift i a k =>
    obtain ⟨hi,hs,hk⟩ := of_decide_eq_true hr
    have h₁ := forced (2*i) (2*a+1) hi (by omega) (by simp [Rule.raw]) (by simp [Rule.raw])
    have h₂ := forced (2*i) (2*a+3) hi hs (by simp [Rule.raw]) (by simp [Rule.raw])
    obtain ⟨u,hu,hv₀,hv₁,hv₂⟩ := two_apart h₁ (by simpa only [Nat.add_assoc] using h₂)
    have hno : i*b+(a+k) ∉ A := hpos false i (a+k) (by omega) (by omega) (by simp [Rule.raw])
    have heq : u=i*b+a := by rw [Nat.mul_assoc] at hu; omega
    subst u
    interval_cases k <;> simp_all [Nat.add_assoc]
  | budget xs =>
    obtain ⟨hw,hc⟩ := Bool.and_eq_true_iff.mp hr
    have hw' := List.all_eq_true.mp hw
    have info (p : ℕ × ℕ) (hp : p∈xs) := of_decide_eq_true (hw' p hp)
    have hm (p : ℕ × ℕ) (h : p∈xs) : Hole A (p.1*b+p.2) :=
      hneg true p.1 p.2 (info _ h).1 (info _ h).2.1 (List.mem_map_of_mem h)
    have bound := budget_le xs (fun p hp => (info p hp).2.2) hm
    have bound' : cost (fun i => (budgetCount xs i).card) ≤
        cost (fun i => (window A i (b+2)).card) := by unfold cost; gcongr <;> apply bound
    exact (Nat.not_lt.mpr ((of_decide_eq_true hc).trans bound')) hbudget

end OMA.CP867

/-! A sound bit-set checker for reverse unit propagation. Each clause is stored
as one integer with two bits per atom (positive and negative). The initial
masks are verified once against the signed clauses, and learned masks are
verified by unit propagation using strictly earlier clauses. -/

namespace OMA.SharedCert867

def lit (v:ℕ→Bool) (l:ℤ) := if 0<l then v l.natAbs else !(v l.natAbs)
def clauseSat (v:ℕ→Bool) (c:List ℤ) := c.any (lit v)

/-- Fixed-width little-endian packing for compact, independently checkable
input data. The fuel bounds parsing; correctness depends only on the decoded
clauses and the subsequent mathematical refutation. -/
def digits (base:ℕ) : ℕ → ℕ → List ℕ
  | 0,_ => []
  | budget+1,n => if n=0 then [] else n%base :: digits base budget (n/base)

abbrev Table := Array (List (List ℤ))

def initAt (B:Table) (i:ℕ) : List ℤ := ((B[i/32]?).getD [])[i%32]?.getD [1,-1]

def block (f:ℕ→Bool) (start:ℕ) (len:ℕ) := (List.range' start len).all f

theorem block_union {f:ℕ→Bool} {s n m:ℕ} (a:block f s n) (b:block f (s+n) m) :
    block f s (n+m) := by
  unfold block at *
  rw [←List.range'_append_1,List.all_append,a,b]
  rfl

theorem init_sound (B:Table) (v:ℕ→Bool) (s:∀ c∈B.toList.flatten,clauseSat v c=true)
    (i:ℕ) : clauseSat v (initAt B i)=true := by
  have taut : clauseSat v [1,-1]=true := by simp [clauseSat,lit]
  unfold initAt
  cases h:B[i/32]? with
  | none => simpa using taut
  | some row =>
    cases g:row[i%32]? with
    | none => simpa [g] using taut
    | some c =>
      simp only [Option.getD_some,g]
      exact s c (List.mem_flatten.mpr ⟨row,Array.mem_toList_iff.mpr (Array.mem_of_getElem? h),
        List.mem_of_getElem? g⟩)


abbrev Masks := ℕ → ℕ
abbrev ProofTable := ℕ → ℕ × ℕ

/-- Extract one variable-length binary word from a block, using packed 16-bit
start and end offsets. No algebraic assumptions on either integer are needed. -/
def packedAt (data offsets i : ℕ) : ℕ :=
  let a := (offsets >>> (16*i)) % 65536
  let b := (offsets >>> (16*(i+1))) % 65536
  (data >>> a) % (1 <<< (b-a))

def squeeze (guess back:ℕ→ℕ) (n:ℕ) :=
  let g:=guess n
  if g<256 ∧ back g=n then g else 256+n
def expand (back:ℕ→ℕ) (n:ℕ) := if n<256 then back n else n-256

private theorem inverse (guess back:ℕ→ℕ) (n:ℕ) : expand back (squeeze guess back n)=n := by
  unfold squeeze
  dsimp only
  split
  · rename_i h
    simp [expand,h.1,h.2]
  · simp [expand]

def key (guess back:ℕ→ℕ) (z:ℤ) := 2*squeeze guess back z.natAbs + (if 0<z then 0 else 1)
def literalValue (back:ℕ→ℕ) (v:ℕ→Bool) (j:ℕ) :=
  if j%2=0 then v (expand back (j/2)) else !(v (expand back (j/2)))
def opposite (j:ℕ) := if j%2=0 then j+1 else j-1
def bit (i:ℕ) := 1 <<< i

def word (guess back:ℕ→ℕ) : List ℤ → ℕ
  | [] => 0
  | l::ls => bit (key guess back l) ||| word guess back ls
def bitSat (back:ℕ→ℕ) (v:ℕ→Bool) (c:ℕ) :=
  ∃j,c.testBit j=true ∧ literalValue back v j=true

private theorem key_value (guess back:ℕ→ℕ) (v:ℕ→Bool) (z:ℤ) :
    literalValue back v (key guess back z)=lit v z := by
  have eq : (2*squeeze guess back z.natAbs+1)/2=squeeze guess back z.natAbs := by omega
  by_cases h:0<z <;> simp [literalValue,key,lit,h,Nat.add_mod,eq,inverse]
private theorem opposite_value (back:ℕ→ℕ) (v:ℕ→Bool) (j:ℕ) :
    literalValue back v (opposite j) = !(literalValue back v j) := by
  unfold literalValue opposite
  split
  · rename_i h
    rw [if_neg (by omega),show (j+1)/2=j/2 by omega]
  · rename_i h
    rw [if_pos (by omega),show (j-1)/2=j/2 by omega,Bool.not_not]

private theorem test_bit (i j:ℕ) : (bit i).testBit j = decide (i=j) := by
  simp [bit,Nat.shiftLeft_eq,Nat.testBit_two_pow]

private theorem member_bit (guess back:ℕ→ℕ) {l:ℤ} {s:List ℤ} (h:l∈s) : (word guess back s).testBit (key guess back l)=true := by
  induction s with
  | nil => simp at h
  | cons a s ih =>
    rw [word,Nat.testBit_or,test_bit]
    rcases List.mem_cons.mp h with rfl|ht
    · simp
    · simp [ih ht]

theorem word_sat (guess back:ℕ→ℕ) {v:ℕ→Bool} {c:List ℤ} (h:clauseSat v c=true) : bitSat back v (word guess back c) := by
  obtain ⟨l,hl,vh⟩ := List.any_eq_true.mp h
  exact ⟨key guess back l,member_bit guess back hl,(key_value ..).trans vh⟩

def propFast (seen:ℕ) : List (ℕ×ℕ) → Bool
  | [] => false
  | (c,pivot)::cs =>
    let r:=c ^^^ (c &&& seen)
    if r=0 then true else bit pivot == r && propFast (seen ||| bit (opposite pivot)) cs

private theorem fast_sound (back:ℕ→ℕ) (v:ℕ→Bool) (cs:List (ℕ×ℕ)) (sat:∀c∈cs,bitSat back v c.1)
    (seen:ℕ) (no:¬bitSat back v seen) (ok:propFast seen cs=true) : False := by
  induction cs generalizing seen with
  | nil => simp [propFast] at ok
  | cons h cs ih =>
    obtain ⟨c,pivot⟩ := h
    obtain ⟨j,cj,tj⟩ := sat (c,pivot) (by simp)
    have js : seen.testBit j=false := by
      cases h:seen.testBit j
      · rfl
      · exact (no ⟨j,h,tj⟩).elim
    let r:=c ^^^ (c &&& seen)
    have jr : r.testBit j=true := by simp [r,cj,js]
    have nz : r≠0 := by intro e;simp [e] at jr
    change (if r=0 then true else bit pivot == r && propFast (seen ||| bit (opposite pivot)) cs)=true at ok
    rw [if_neg nz,Bool.and_eq_true_iff] at ok
    have rr : bit pivot=r := eq_of_beq ok.1
    have idx : pivot=j := of_decide_eq_true ((test_bit ..).symm.trans ((congrArg (fun n:ℕ => n.testBit j) rr).trans jr))
    apply ih (fun z hz => sat z (by simp [hz])) _ _ ok.2
    rintro ⟨b,test,value⟩
    rw [Nat.testBit_or,Bool.or_eq_true_iff,test_bit,decide_eq_true_eq] at test
    rcases test with h|rfl
    · exact no ⟨b,h,value⟩
    · rw [idx,opposite_value,tj] at value
      contradiction

/-- The low nine bits encode the trailing-zero count of the mask. -/
def decode (a:ℕ) := (a/512) <<< (a%512)
def baseMask (S:Masks) (i:ℕ) := decode (S i)

def baseOk (guess back:ℕ→ℕ) (B:Table) (S:Masks) (i:ℕ) :=
  word guess back (initAt B i) == baseMask S i

def getMask (S:Masks) (n:ℕ) (R:ProofTable) (j:ℕ) :=
  if j<n then baseMask S j else decode (R (j-n)).1

def okFast (S:Masks) (n:ℕ) (R:ProofTable) (i:ℕ) : Bool :=
  let r:=R i
  let ids:=digits 2097152 256 r.2
  ids.all (fun j => j%4096-1<n+i) && propFast (decode r.1)
    (ids.map (fun j => (getMask S n R (j%4096-1),j/4096)))

theorem finalFast (guess back:ℕ→ℕ) (B:Table) (S:Masks) (n:ℕ) (R:ProofTable) (last:ℕ)
    (initial:block (baseOk guess back B S) 0 n)
    (ok:block (okFast S n R) 0 (last+1)) (empty:(R last).1=0)
    (v:ℕ→Bool) (sat:∀c∈B.toList.flatten,clauseSat v c=true) : False := by
  have base (j:ℕ) (hj:j<n) : bitSat back v (baseMask S j) := by
    have okj := List.all_eq_true.mp initial j (List.mem_range'_1.mpr (by omega))
    have e : word guess back (initAt B j) = baseMask S j := eq_of_beq okj
    exact e ▸ word_sat guess back (init_sound B v sat j)
  have all (i:ℕ) (hi:i ≤ last) : bitSat back v (decode (R i).1) := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      have valid := List.all_eq_true.mp ok i (List.mem_range'_1.mpr (by omega))
      obtain ⟨bounds,prop⟩ := Bool.and_eq_true_iff.mp valid
      by_contra no
      apply fast_sound back v _ _ _ no prop
      intro c hc
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
      have small : j%4096-1<n+i := of_decide_eq_true (List.all_eq_true.mp bounds j hj)
      dsimp only
      unfold getMask
      split
      · rename_i h;exact base _ h
      · exact ih _ (by omega) (by omega)
  obtain ⟨j,bad,_⟩ := all last (by rfl)
  simp [empty,decode] at bad

end OMA.SharedCert867

/-! The shared finite clause system, in its original order. -/
namespace OMA.SharedCert867

def guess (n:ℕ) := if n<12361 then (if n<4119 then (if n<1552 then (if n<1029 then (n-515) else (if n<1547 then (n-1023) else (n-1531))) else (if n<2060 then (n-1533) else (if n<3088 then (n-2040) else (n-3056)))) else (if n<6190 then (if n<4140 then (n-4069) else (if n<6187 then (n-4070) else (n-6116))) else (if n<6196 then (if n<6193 then (n-6118) else (n-6119)) else (if n<12358 then (n-6120) else (n-12275))))) else (if n<20503 then (if n<12407 then (if n<12366 then (n-12276) else (if n<12371 then (n-12279) else (n-12282))) else (if n<17413 then (n-12283) else (if n<19472 then (n-17286) else (n-19335)))) else (if n<28745 then (if n<20524 then (n-20348) else (if n<28742 then (n-20349) else (n-28566))) else (if n<28755 then (if n<28750 then (n-28567) else (n-28570)) else (if n<28791 then (n-28573) else (n-28574)))))
def back (n:ℕ) := if n<85 then (if n<50 then (if n<19 then (if n<6 then (n+515) else (if n<16 then (n+1023) else (n+1531))) else (if n<20 then (n+1533) else (if n<32 then (n+2040) else (n+3056)))) else (if n<72 then (if n<70 then (n+4069) else (if n<71 then (n+4070) else (n+6116))) else (if n<76 then (if n<74 then (n+6118) else (n+6119)) else (if n<83 then (n+6120) else (n+12275))))) else (if n<155 then (if n<124 then (if n<87 then (n+12276) else (if n<89 then (n+12279) else (n+12282))) else (if n<127 then (n+12283) else (if n<137 then (n+17286) else (n+19335)))) else (if n<178 then (if n<175 then (n+20348) else (if n<176 then (n+20349) else (n+28566))) else (if n<182 then (if n<180 then (n+28567) else (n+28570)) else (if n<217 then (n+28573) else (n+28574)))))

def b2_0 : List (List ℤ) :=
  [[-1549,-518,-517,-516],[-1552,-519,-518,-517],[-3100,-520,-519,-518,-517,-516,-515],[-2062,-1033,-1030,1031,1032],[-2063,-1033,-1031,1032],[-2065,-1035,-1031,1032,1033,1034],[-2064,-1033,-1032],[-2065,-1034,-1032,1033],[-2066,-1035,-1032,1033,1034],[-2066,-1034,-1033],[-2067,-1035,-1033,1034],[-2068,-1036,-1033,1034,1035],[-2068,-1035,-1034],[-2069,-1036,-1034,1035],[-2071,-1037,-1035,1036],[-3089,-1032,-1030,-1029,1031],[-3090,-1033,-1030,-1029,1031,1032],[-3091,-1033,-1031,-1029,1030,1032],[-3095,-1035,-1033,-1029,1030,1031,1032,1034],[-3092,-1033,-1031,-1030,1032],[-3093,-1033,-1032,-1030,1031],[-3094,-1035,-1031,-1030,1032,1033,1034],[-3096,-1035,-1033,-1030,1031,1032,1034],[-3094,-1033,-1032,-1031],[-3095,-1034,-1032,-1031,1033],[-3096,-1034,-1033,-1031,1032],[-3097,-1035,-1033,-1031,1032,1034],[-3098,-1035,-1034,-1031,1032,1033],[-3098,-1036,-1033,-1031,1032,1034,1035],[-3099,-1036,-1034,-1031,1032,1033,1035],[-3100,-1036,-1035,-1031,1032,1033,1034],[-3099,-1037,-1033,-1031,1032,1034,1035,1036]]
def b2_1 : List (List ℤ) :=
  [[-3101,-1037,-1035,-1031,1032,1033,1034,1036],[-3097,-1034,-1033,-1032],[-3098,-1035,-1033,-1032,1034],[-3099,-1035,-1034,-1032,1033],[-3099,-1036,-1033,-1032,1034,1035],[-3100,-1036,-1034,-1032,1033,1035],[-3101,-1036,-1035,-1032,1033,1034],[-3100,-1037,-1033,-1032,1034,1035,1036],[-3101,-1037,-1034,-1032,1033,1035,1036],[-3102,-1037,-1035,-1032,1033,1034,1036],[-3100,-1035,-1034,-1033],[-3101,-1036,-1034,-1033,1035],[-3102,-1036,-1035,-1033,1034],[-3103,-1037,-1035,-1033,1034,1036],[-3103,-1036,-1035,-1034],[-3104,-1037,-1035,-1034,1036],[-3105,-1037,-1036,-1034,1035],[-4121,-1033,-1032,-1030,-1029,1031],[-4124,-1035,-1033,-1030,-1029,1031,1032,1034],[-4125,-1035,-1033,-1031,-1029,1030,1032,1034],[-4128,-1036,-1035,-1031,-1029,1030,1032,1033,1034],[-4126,-1035,-1033,-1031,-1030,1032,1034],[-4129,-1036,-1035,-1031,-1030,1032,1033,1034],[-4129,-1036,-1034,-1032,-1030,1031,1033,1035],[-4131,-1037,-1035,-1032,-1030,1031,1033,1034,1036],[-4127,-1034,-1033,-1032,-1031],[-4128,-1035,-1033,-1032,-1031,1034],[-4129,-1035,-1034,-1032,-1031,1033],[-4130,-1035,-1034,-1033,-1031,1032],[-4130,-1036,-1034,-1032,-1031,1033,1035],[-4131,-1036,-1034,-1033,-1031,1032,1035],[-4132,-1036,-1035,-1033,-1031,1032,1034]]
def b2_2 : List (List ℤ) :=
  [[-4133,-1036,-1035,-1034,-1031,1032,1033],[-4130,-1037,-1033,-1032,-1031,1034,1035,1036],[-4132,-1037,-1035,-1032,-1031,1033,1034,1036],[-4132,-1037,-1034,-1033,-1031,1032,1035,1036],[-4133,-1037,-1035,-1033,-1031,1032,1034,1036],[-4134,-1037,-1036,-1033,-1031,1032,1034,1035],[-4134,-1037,-1035,-1034,-1031,1032,1033,1036],[-4133,-1036,-1035,-1033,-1032,1034],[-4134,-1037,-1035,-1033,-1032,1034,1036],[-4135,-1037,-1035,-1034,-1032,1033,1036],[-4136,-1037,-1036,-1034,-1032,1033,1035],[-4135,-1036,-1035,-1034,-1033],[-4136,-1037,-1035,-1034,-1033,1036],[-4137,-1037,-1036,-1034,-1033,1035],[-4140,-1038,-1037,-1035,-1033,1034,1036],[-3094,-1548,-1547],[-12373,-2066,-2065,-2064,-2062,-2061,-2060,2063],[-12385,-2068,-2067,-2066,-2064,-2063,-2062,2065],[-12397,-2070,-2069,-2068,-2066,-2065,-2064,2067],[-6187,-3095,-3093,3094],[-6190,-3096,-3095],[-6191,-3097,-3095,3096],[-6193,-3098,-3096,3097],[-6194,-3098,-3097],[-6197,-3101,-3097,3098,3099,3100],[-6196,-3099,-3098],[-6198,-3100,-3099],[-6199,-3101,-3099,3100],[-6201,-3103,-3099,3100,3101,3102],[-6200,-3101,-3100],[-6202,-3102,-3101],[-12358,-3092,-3091,-3090,-3088,3089]]
def b2_3 : List (List ℤ) :=
  [[-12361,-3093,-3092,-3090,-3089,3091],[-12366,-3094,-3093,-3092,-3090,3091],[-12372,-3096,-3095,-3093,-3091,3092,3094],[-12373,-3097,-3095,-3093,-3091,3092,3094,3096],[-12375,-3098,-3096,-3093,-3091,3092,3094,3095,3097],[-12371,-3095,-3094,-3093,-3092],[-12373,-3096,-3095,-3093,-3092,3094],[-12374,-3097,-3095,-3093,-3092,3094,3096],[-12375,-3097,-3095,-3094,-3092,3093,3096],[-12375,-3096,-3095,-3094,-3093],[-12377,-3097,-3096,-3094,-3093,3095],[-12378,-3097,-3096,-3095,-3093,3094],[-12379,-3098,-3096,-3095,-3093,3094,3097],[-12381,-3099,-3097,-3095,-3093,3094,3096,3098],[-12382,-3100,-3097,-3095,-3093,3094,3096,3098,3099],[-12385,-3101,-3099,-3095,-3093,3094,3096,3097,3098,3100],[-12380,-3098,-3096,-3095,-3094,3097],[-12381,-3099,-3096,-3095,-3094,3097,3098],[-12382,-3099,-3097,-3095,-3094,3096,3098],[-12383,-3099,-3097,-3096,-3094,3095,3098],[-12384,-3099,-3098,-3096,-3094,3095,3097],[-12385,-3100,-3098,-3096,-3094,3095,3097,3099],[-12385,-3099,-3098,-3096,-3095,3097],[-12386,-3099,-3098,-3097,-3095,3096],[-12387,-3100,-3098,-3097,-3095,3096,3099],[-12388,-3100,-3099,-3097,-3095,3096,3098],[-12389,-3100,-3099,-3098,-3095,3096,3097],[-12387,-3101,-3098,-3096,-3095,3097,3099,3100],[-12389,-3101,-3099,-3097,-3095,3096,3098,3100],[-12391,-3102,-3100,-3097,-3095,3096,3098,3099,3101],[-12392,-3102,-3101,-3097,-3095,3096,3098,3099,3100],[-12391,-3103,-3099,-3097,-3095,3096,3098,3100,3101,3102]]
def b2_4 : List (List ℤ) :=
  [[-12393,-3103,-3101,-3097,-3095,3096,3098,3099,3100,3102],[-12387,-3099,-3098,-3097,-3096],[-12388,-3100,-3098,-3097,-3096,3099],[-12389,-3100,-3099,-3097,-3096,3098],[-12390,-3100,-3099,-3098,-3096,3097],[-12390,-3101,-3099,-3097,-3096,3098,3100],[-12393,-3101,-3100,-3099,-3096,3097,3098],[-12395,-3102,-3101,-3099,-3096,3097,3098,3100],[-12396,-3103,-3101,-3099,-3096,3097,3098,3100,3102],[-12391,-3100,-3099,-3098,-3097],[-12392,-3101,-3099,-3098,-3097,3100],[-12393,-3101,-3100,-3098,-3097,3099],[-12394,-3101,-3100,-3099,-3097,3098],[-12393,-3102,-3099,-3098,-3097,3100,3101],[-12395,-3102,-3101,-3098,-3097,3099,3100],[-12395,-3102,-3100,-3099,-3097,3098,3101],[-12396,-3102,-3101,-3099,-3097,3098,3100],[-12394,-3103,-3099,-3098,-3097,3100,3101,3102],[-12396,-3103,-3101,-3098,-3097,3099,3100,3102],[-12397,-3103,-3101,-3099,-3097,3098,3100,3102],[-12398,-3103,-3102,-3099,-3097,3098,3100,3101],[-12399,-3104,-3102,-3099,-3097,3098,3100,3101,3103],[-12395,-3101,-3100,-3099,-3098],[-12396,-3102,-3100,-3099,-3098,3101],[-12397,-3102,-3101,-3099,-3098,3100],[-12398,-3102,-3101,-3100,-3098,3099],[-12398,-3103,-3101,-3099,-3098,3100,3102],[-12399,-3103,-3101,-3100,-3098,3099,3102],[-12401,-3103,-3102,-3101,-3098,3099,3100],[-12402,-3105,-3103,-3099,-3098,3100,3101,3102,3104],[-12399,-3102,-3101,-3100,-3099],[-12400,-3103,-3101,-3100,-3099,3102]]
def b2_5 : List (List ℤ) :=
  [[-12401,-3103,-3102,-3100,-3099,3101],[-12402,-3103,-3102,-3101,-3099,3100],[-12403,-3104,-3102,-3101,-3099,3100,3103],[-12405,-3104,-3103,-3102,-3099,3100,3101],[-12405,-3105,-3103,-3101,-3099,3100,3102,3104],[-12404,-3104,-3102,-3101,-3100,3103],[-12409,-3105,-3104,-3102,-3101,3103],[-12359,-4122,-4120,-4119,4121],[-12362,-4123,-4121,-4120,4122],[-12367,-4124,-4123,-4122],[-12372,-4126,-4125,-4123,4124],[-12374,-4127,-4125,-4124,4126],[-12375,-4127,-4126,-4124,4125],[-12376,-4127,-4126,-4125],[-12377,-4128,-4126,-4125,4127],[-12378,-4128,-4127,-4125,4126],[-12379,-4128,-4127,-4126],[-12380,-4129,-4127,-4126,4128],[-12381,-4129,-4128,-4126,4127],[-12382,-4129,-4128,-4127],[-12383,-4130,-4128,-4127,4129],[-12384,-4130,-4129,-4127,4128],[-12386,-4131,-4129,-4128,4130],[-12387,-4131,-4130,-4128,4129],[-12388,-4131,-4130,-4129],[-12389,-4132,-4130,-4129,4131],[-12390,-4132,-4131,-4129,4130],[-12391,-4133,-4131,-4129,4130,4132],[-12391,-4132,-4131,-4130],[-12392,-4133,-4131,-4130,4132],[-12393,-4133,-4132,-4130,4131],[-12394,-4133,-4132,-4131]]
def b2_6 : List (List ℤ) :=
  [[-12395,-4134,-4132,-4131,4133],[-12396,-4134,-4133,-4131,4132],[-12397,-4134,-4133,-4132],[-12398,-4135,-4133,-4132,4134],[-12399,-4135,-4134,-4132,4133],[-12400,-4135,-4134,-4133],[-12401,-4136,-4134,-4133,4135],[-12402,-4136,-4135,-4133,4134],[-12403,-4136,-4135,-4134],[-12404,-4137,-4135,-4134,4136],[-12407,-4138,-4136,-4135,4137],[-12408,-4138,-4137,-4135,4136],[1029,1030,17413,17414],[1029,1031,17413,17415],[1030,1031,17414,17415],[515,1030,1032,17414,17416],[1031,1032,17415,17416],[1031,1033,17415,17417],[1032,1033,17416,17417],[516,1032,1034,17416,17418],[517,1032,1034,17416,17418],[518,1032,1034,17416,17418],[1033,1034,17417,17418],[1033,1035,17417,17419],[1034,1035,17418,17419],[517,1034,1036,17418,17420],[518,1034,1036,17418,17420],[519,1034,1036,17418,17420],[1035,1036,17419,17420],[1035,1037,17419,17421],[1036,1037,17420,17421],[520,1036,1038,17420,17422]]
def b2_7 : List (List ℤ) :=
  [[3088,3089,19472,19473],[3089,3090,19473,19474],[3089,3091,19473,19475],[3090,3091,19474,19475],[1547,3090,3092,19474,19476],[3091,3092,19475,19476],[3091,3093,19475,19477],[3092,3093,19476,19477],[3093,3094,19477,19478],[3093,3095,19477,19479],[3094,3095,19478,19479],[3095,3096,19479,19480],[3095,3097,19479,19481],[3096,3097,19480,19481],[1548,3096,3098,19480,19482],[1549,3096,3098,19480,19482],[3097,3098,19481,19482],[3097,3099,19481,19483],[3098,3099,19482,19483],[1549,3098,3100,19482,19484],[3099,3100,19483,19484],[3099,3101,19483,19485],[3100,3101,19484,19485],[1552,3100,3102,19484,19486],[3101,3102,19485,19486],[3101,3103,19485,19487],[3102,3103,19486,19487],[3103,3104,19487,19488],[3103,3105,19487,19489],[3104,3105,19488,19489],[4119,4121,20503,20505],[4120,4121,20504,20505]]
def b2_8 : List (List ℤ) :=
  [[2060,4120,4122,20504,20506],[2061,4120,4122,20504,20506],[2062,4120,4122,20504,20506],[4121,4122,20505,20506],[4123,4124,20507,20508],[4123,4125,20507,20509],[4124,4125,20508,20509],[2062,4124,4126,20508,20510],[2063,4124,4126,20508,20510],[2064,4124,4126,20508,20510],[4125,4126,20509,20510],[4125,4127,20509,20511],[4126,4127,20510,20511],[2064,4126,4128,20510,20512],[4127,4128,20511,20512],[4127,4129,20511,20513],[4128,4129,20512,20513],[2064,4128,4130,20512,20514],[2065,4128,4130,20512,20514],[2066,4128,4130,20512,20514],[4129,4130,20513,20514],[4129,4131,20513,20515],[4130,4131,20514,20515],[2065,4130,4132,20514,20516],[2066,4130,4132,20514,20516],[4131,4132,20515,20516],[4131,4133,20515,20517],[4132,4133,20516,20517],[2066,4132,4134,20516,20518],[2067,4132,4134,20516,20518],[2068,4132,4134,20516,20518],[4133,4134,20517,20518]]
def b2_9 : List (List ℤ) :=
  [[4133,4135,20517,20519],[4134,4135,20518,20519],[2068,4134,4136,20518,20520],[2069,4134,4136,20518,20520],[4135,4136,20519,20520],[4135,4137,20519,20521],[4136,4137,20520,20521],[2068,4136,4138,20520,20522],[2069,4136,4138,20520,20522],[2070,4136,4138,20520,20522],[4137,4138,20521,20522],[2071,4138,4140,20522,20524],[12358,12359,28742,28743],[12361,12362,28745,28746],[12366,12367,28750,28751],[12371,12372,28755,28756],[12372,12373,28756,28757],[6187,12372,12374,28756,28758],[12373,12374,28757,28758],[12373,12375,28757,28759],[12374,12375,28758,28759],[12375,12376,28759,28760],[12377,12378,28761,28762],[12377,12379,28761,28763],[12378,12379,28762,28763],[6190,12378,12380,28762,28764],[12379,12380,28763,28764],[12380,12381,28764,28765],[6191,12380,12382,28764,28766],[12381,12382,28765,28766],[12381,12383,28765,28767],[12383,12385,28767,28769]]
def b2_10 : List (List ℤ) :=
  [[12384,12385,28768,28769],[6193,12384,12386,28768,28770],[12385,12386,28769,28770],[12386,12387,28770,28771],[6194,12386,12388,28770,28772],[12387,12388,28771,28772],[12387,12389,28771,28773],[12388,12389,28772,28773],[12389,12390,28773,28774],[12389,12391,28773,28775],[12390,12391,28774,28775],[6196,12390,12392,28774,28776],[6197,12390,12392,28774,28776],[12391,12392,28775,28776],[12391,12393,28775,28777],[12392,12393,28776,28777],[12393,12394,28777,28778],[12393,12395,28777,28779],[12394,12395,28778,28779],[6198,12394,12396,28778,28780],[12395,12396,28779,28780],[12395,12397,28779,28781],[12396,12397,28780,28781],[6199,12396,12398,28780,28782],[12397,12398,28781,28782],[12398,12399,28782,28783],[12399,12400,28783,28784],[12399,12401,28783,28785],[6200,12400,12402,28784,28786],[6201,12400,12402,28784,28786],[12401,12402,28785,28786],[12401,12403,28785,28787]]
def b2_11 : List (List ℤ) :=
  [[6202,12402,12404,28786,28788],[12403,12404,28787,28788],[12404,12405,28788,28789],[12405,12407,28789,28791],[12408,12409,28792,28793],[-17415,-17413],[-17416,-17413],[-17417,-17413],[-17419,-17413],[-17420,-17413],[-17421,-17413],[-19481,-17413],[-19482,-17413],[-19483,-17413],[-19484,-17413],[-19485,-17413],[-19486,-17413],[-19487,-17413],[-19488,-17413],[-19489,-17413],[-20515,-17413],[-20516,-17413],[-20517,-17413],[-20518,-17413],[-20519,-17413],[-20520,-17413],[-20521,-17413],[-20522,-17413],[-28769,-17413],[-28774,-17413],[-28775,-17413],[-28779,-17413]]
def b2_12 : List (List ℤ) :=
  [[-28780,-17413],[-28781,-17413],[-28782,-17413],[-28783,-17413],[-28785,-17413],[-28786,-17413],[-28787,-17413],[-28788,-17413],[-28792,-17413],[-28793,-17413],[-17415,-17414],[-17416,-17414],[-17417,-17414],[-17419,-17414],[-17420,-17414],[-17421,-17414],[-19479,-17414],[-19481,-17414],[-19482,-17414],[-19483,-17414],[-19484,-17414],[-19485,-17414],[-19486,-17414],[-19487,-17414],[-19488,-17414],[-19489,-17414],[-20512,-17414],[-20513,-17414],[-20514,-17414],[-20515,-17414],[-20516,-17414],[-20517,-17414]]
def b2_13 : List (List ℤ) :=
  [[-20518,-17414],[-20519,-17414],[-20520,-17414],[-20521,-17414],[-20522,-17414],[-28769,-17414],[-28770,-17414],[-28774,-17414],[-28775,-17414],[-28779,-17414],[-28780,-17414],[-28781,-17414],[-28782,-17414],[-28783,-17414],[-28785,-17414],[-28786,-17414],[-28787,-17414],[-28788,-17414],[-28792,-17414],[-28793,-17414],[-17416,-17415],[-17417,-17415],[-17418,-17415],[-17419,-17415],[-17420,-17415],[-17421,-17415],[-19477,-17415],[-19478,-17415],[-19479,-17415],[-19480,-17415],[-19481,-17415],[-19482,-17415]]
def b2_14 : List (List ℤ) :=
  [[-19483,-17415],[-19484,-17415],[-19485,-17415],[-19486,-17415],[-19487,-17415],[-19488,-17415],[-19489,-17415],[-20509,-17415],[-20510,-17415],[-20511,-17415],[-20512,-17415],[-20513,-17415],[-20514,-17415],[-20515,-17415],[-20516,-17415],[-20517,-17415],[-20518,-17415],[-20519,-17415],[-20520,-17415],[-20521,-17415],[-28761,-17415],[-28762,-17415],[-28763,-17415],[-28770,-17415],[-28771,-17415],[-28772,-17415],[-28773,-17415],[-28774,-17415],[-28775,-17415],[-28776,-17415],[-28777,-17415],[-28778,-17415]]
def b2_15 : List (List ℤ) :=
  [[-28779,-17415],[-28780,-17415],[-28781,-17415],[-28782,-17415],[-28783,-17415],[-28785,-17415],[-28786,-17415],[-28787,-17415],[-28788,-17415],[-28789,-17415],[-17417,-17416],[-17418,-17416],[-17419,-17416],[-17420,-17416],[-17421,-17416],[-19474,-17416],[-19475,-17416],[-19476,-17416],[-19477,-17416],[-19478,-17416],[-19479,-17416],[-19480,-17416],[-19481,-17416],[-19482,-17416],[-19483,-17416],[-19484,-17416],[-19485,-17416],[-19486,-17416],[-19487,-17416],[-19488,-17416],[-19489,-17416],[-20507,-17416]]
def b2_16 : List (List ℤ) :=
  [[-20508,-17416],[-20509,-17416],[-20510,-17416],[-20511,-17416],[-20512,-17416],[-20513,-17416],[-20514,-17416],[-20515,-17416],[-20516,-17416],[-20517,-17416],[-20518,-17416],[-20519,-17416],[-20520,-17416],[-20521,-17416],[-28755,-17416],[-28756,-17416],[-28757,-17416],[-28758,-17416],[-28759,-17416],[-28760,-17416],[-28765,-17416],[-28766,-17416],[-28769,-17416],[-28770,-17416],[-28771,-17416],[-28772,-17416],[-28773,-17416],[-28774,-17416],[-28775,-17416],[-28776,-17416],[-28777,-17416],[-28778,-17416]]
def b2_17 : List (List ℤ) :=
  [[-28779,-17416],[-28780,-17416],[-28781,-17416],[-28782,-17416],[-28783,-17416],[-28784,-17416],[-28785,-17416],[-28786,-17416],[-28787,-17416],[-28788,-17416],[-28789,-17416],[-17418,-17417],[-17419,-17417],[-17420,-17417],[-17421,-17417],[-19475,-17417],[-19476,-17417],[-19477,-17417],[-19478,-17417],[-19479,-17417],[-19480,-17417],[-19481,-17417],[-19482,-17417],[-19483,-17417],[-19484,-17417],[-19485,-17417],[-19486,-17417],[-19487,-17417],[-19489,-17417],[-20508,-17417],[-20509,-17417],[-20510,-17417]]
def b2_18 : List (List ℤ) :=
  [[-20511,-17417],[-20512,-17417],[-20513,-17417],[-20514,-17417],[-20515,-17417],[-20516,-17417],[-20517,-17417],[-20518,-17417],[-20519,-17417],[-20520,-17417],[-20521,-17417],[-28756,-17417],[-28757,-17417],[-28758,-17417],[-28761,-17417],[-28762,-17417],[-28763,-17417],[-28765,-17417],[-28767,-17417],[-28768,-17417],[-28769,-17417],[-28770,-17417],[-28771,-17417],[-28772,-17417],[-28773,-17417],[-28774,-17417],[-28775,-17417],[-28776,-17417],[-28777,-17417],[-28778,-17417],[-28779,-17417],[-28780,-17417]]
def b2_19 : List (List ℤ) :=
  [[-28781,-17417],[-28782,-17417],[-28783,-17417],[-28784,-17417],[-28785,-17417],[-28786,-17417],[-28788,-17417],[-17419,-17418],[-17420,-17418],[-17421,-17418],[-19479,-17418],[-19480,-17418],[-19481,-17418],[-19482,-17418],[-19483,-17418],[-19484,-17418],[-19485,-17418],[-19486,-17418],[-19487,-17418],[-20512,-17418],[-20513,-17418],[-20514,-17418],[-20515,-17418],[-20516,-17418],[-20517,-17418],[-20518,-17418],[-20519,-17418],[-20520,-17418],[-28769,-17418],[-28770,-17418],[-28771,-17418],[-28772,-17418]]
def b2_20 : List (List ℤ) :=
  [[-28773,-17418],[-28774,-17418],[-28775,-17418],[-28776,-17418],[-28777,-17418],[-28778,-17418],[-28779,-17418],[-28780,-17418],[-28781,-17418],[-28782,-17418],[-28783,-17418],[-28784,-17418],[-28785,-17418],[-28786,-17418],[-17420,-17419],[-17421,-17419],[-19472,-17419],[-19473,-17419],[-19474,-17419],[-19475,-17419],[-19476,-17419],[-19477,-17419],[-19478,-17419],[-19479,-17419],[-19480,-17419],[-19481,-17419],[-19482,-17419],[-19483,-17419],[-19484,-17419],[-19485,-17419],[-19486,-17419],[-20503,-17419]]
def b2_21 : List (List ℤ) :=
  [[-20504,-17419],[-20505,-17419],[-20506,-17419],[-20509,-17419],[-20510,-17419],[-20511,-17419],[-20512,-17419],[-20513,-17419],[-20514,-17419],[-20515,-17419],[-20516,-17419],[-20517,-17419],[-20518,-17419],[-28742,-17419],[-28743,-17419],[-28761,-17419],[-28762,-17419],[-28763,-17419],[-28765,-17419],[-28767,-17419],[-28769,-17419],[-28770,-17419],[-28771,-17419],[-28772,-17419],[-28773,-17419],[-28774,-17419],[-28775,-17419],[-28776,-17419],[-28777,-17419],[-28778,-17419],[-28779,-17419],[-28780,-17419]]
def b2_22 : List (List ℤ) :=
  [[-17421,-17420],[-19472,-17420],[-19473,-17420],[-19474,-17420],[-19475,-17420],[-19476,-17420],[-19477,-17420],[-19478,-17420],[-19479,-17420],[-19480,-17420],[-19481,-17420],[-19482,-17420],[-19483,-17420],[-19484,-17420],[-19485,-17420],[-19486,-17420],[-19487,-17420],[-20503,-17420],[-20504,-17420],[-20505,-17420],[-20506,-17420],[-20507,-17420],[-20508,-17420],[-20509,-17420],[-20510,-17420],[-20511,-17420],[-20512,-17420],[-20513,-17420],[-20514,-17420],[-20515,-17420],[-20516,-17420],[-20517,-17420]]
def b2_23 : List (List ℤ) :=
  [[-20518,-17420],[-28742,-17420],[-28743,-17420],[-28745,-17420],[-28746,-17420],[-28750,-17420],[-28751,-17420],[-28756,-17420],[-28757,-17420],[-28758,-17420],[-28759,-17420],[-28761,-17420],[-28762,-17420],[-28763,-17420],[-28764,-17420],[-28765,-17420],[-28768,-17420],[-28769,-17420],[-28771,-17420],[-28772,-17420],[-28773,-17420],[-28774,-17420],[-28775,-17420],[-28776,-17420],[-28777,-17420],[-28778,-17420],[-28779,-17420],[-28780,-17420],[-28781,-17420],[-28782,-17420],[-19472,-17421],[-19473,-17421]]
def b2_24 : List (List ℤ) :=
  [[-19474,-17421],[-19475,-17421],[-19476,-17421],[-19477,-17421],[-19478,-17421],[-19479,-17421],[-19480,-17421],[-19481,-17421],[-19482,-17421],[-19483,-17421],[-19484,-17421],[-19485,-17421],[-20503,-17421],[-20504,-17421],[-20505,-17421],[-20506,-17421],[-20507,-17421],[-20508,-17421],[-20509,-17421],[-20510,-17421],[-20511,-17421],[-20512,-17421],[-20513,-17421],[-20514,-17421],[-20515,-17421],[-20516,-17421],[-28742,-17421],[-28743,-17421],[-28745,-17421],[-28746,-17421],[-28750,-17421],[-28751,-17421]]
def b2_25 : List (List ℤ) :=
  [[-28756,-17421],[-28757,-17421],[-28758,-17421],[-28759,-17421],[-28761,-17421],[-28762,-17421],[-28763,-17421],[-28764,-17421],[-28765,-17421],[-28768,-17421],[-28769,-17421],[-28773,-17421],[-28774,-17421],[-28775,-17421],[-28776,-17421],[-28777,-17421],[-28779,-17421],[-19479,-17422],[-20512,-17422],[-20513,-17422],[-20514,-17422],[-28763,-17422],[-28764,-17422],[-28768,-17422],[-28770,-17422],[-19481,-19472],[-19482,-19472],[-19483,-19472],[-19484,-19472],[-19485,-19472],[-19486,-19472],[-19487,-19472]]
def b2_26 : List (List ℤ) :=
  [[-19488,-19472],[-20515,-19472],[-20516,-19472],[-20517,-19472],[-20518,-19472],[-20519,-19472],[-20520,-19472],[-20521,-19472],[-28779,-19472],[-28780,-19472],[-28781,-19472],[-28782,-19472],[-28783,-19472],[-28785,-19472],[-28786,-19472],[-28787,-19472],[-28788,-19472],[-19481,-19473],[-19482,-19473],[-19483,-19473],[-19484,-19473],[-19485,-19473],[-19486,-19473],[-19487,-19473],[-19488,-19473],[-19489,-19473],[-20515,-19473],[-20516,-19473],[-20517,-19473],[-20518,-19473],[-20519,-19473],[-20520,-19473]]
def b2_27 : List (List ℤ) :=
  [[-20521,-19473],[-20522,-19473],[-28779,-19473],[-28780,-19473],[-28781,-19473],[-28782,-19473],[-28783,-19473],[-28785,-19473],[-28786,-19473],[-28787,-19473],[-28788,-19473],[-28792,-19473],[-28793,-19473],[-19481,-19474],[-19482,-19474],[-19483,-19474],[-19484,-19474],[-19485,-19474],[-19486,-19474],[-19487,-19474],[-19488,-19474],[-19489,-19474],[-20515,-19474],[-20516,-19474],[-20517,-19474],[-20518,-19474],[-20519,-19474],[-20520,-19474],[-20521,-19474],[-20522,-19474],[-28779,-19474],[-28780,-19474]]
def b2_28 : List (List ℤ) :=
  [[-28781,-19474],[-28782,-19474],[-28783,-19474],[-28785,-19474],[-28786,-19474],[-28787,-19474],[-28788,-19474],[-28792,-19474],[-28793,-19474],[-19479,-19475],[-19481,-19475],[-19482,-19475],[-19483,-19475],[-19484,-19475],[-19485,-19475],[-19486,-19475],[-19487,-19475],[-19488,-19475],[-19489,-19475],[-20512,-19475],[-20513,-19475],[-20514,-19475],[-20515,-19475],[-20516,-19475],[-20517,-19475],[-20518,-19475],[-20519,-19475],[-20520,-19475],[-20521,-19475],[-20522,-19475],[-28769,-19475],[-28770,-19475]]
def b2_29 : List (List ℤ) :=
  [[-28774,-19475],[-28775,-19475],[-28779,-19475],[-28780,-19475],[-28781,-19475],[-28782,-19475],[-28783,-19475],[-28785,-19475],[-28786,-19475],[-28787,-19475],[-28788,-19475],[-28792,-19475],[-28793,-19475],[-19479,-19476],[-19481,-19476],[-19482,-19476],[-19483,-19476],[-19484,-19476],[-19485,-19476],[-19486,-19476],[-19487,-19476],[-19488,-19476],[-19489,-19476],[-20512,-19476],[-20513,-19476],[-20514,-19476],[-20515,-19476],[-20516,-19476],[-20517,-19476],[-20518,-19476],[-20519,-19476],[-20520,-19476]]
def b2_30 : List (List ℤ) :=
  [[-20521,-19476],[-20522,-19476],[-28769,-19476],[-28770,-19476],[-28774,-19476],[-28775,-19476],[-28779,-19476],[-28780,-19476],[-28781,-19476],[-28782,-19476],[-28783,-19476],[-28785,-19476],[-28786,-19476],[-28787,-19476],[-28788,-19476],[-28792,-19476],[-28793,-19476],[-19479,-19477],[-19481,-19477],[-19482,-19477],[-19483,-19477],[-19484,-19477],[-19485,-19477],[-19486,-19477],[-19487,-19477],[-19488,-19477],[-19489,-19477],[-20512,-19477],[-20513,-19477],[-20514,-19477],[-20515,-19477],[-20516,-19477]]
def b2_31 : List (List ℤ) :=
  [[-20517,-19477],[-20518,-19477],[-20519,-19477],[-20520,-19477],[-20521,-19477],[-20522,-19477],[-28769,-19477],[-28770,-19477],[-28774,-19477],[-28775,-19477],[-28776,-19477],[-28777,-19477],[-28779,-19477],[-28780,-19477],[-28781,-19477],[-28782,-19477],[-28783,-19477],[-28785,-19477],[-28786,-19477],[-28787,-19477],[-28788,-19477],[-28792,-19477],[-28793,-19477],[-19481,-19478],[-19482,-19478],[-19483,-19478],[-19484,-19478],[-19485,-19478],[-19486,-19478],[-19487,-19478],[-19488,-19478],[-20514,-19478]]
def b2_32 : List (List ℤ) :=
  [[-20515,-19478],[-20516,-19478],[-20517,-19478],[-20518,-19478],[-20519,-19478],[-20520,-19478],[-20521,-19478],[-28776,-19478],[-28777,-19478],[-28779,-19478],[-28780,-19478],[-28781,-19478],[-28782,-19478],[-28783,-19478],[-28785,-19478],[-28786,-19478],[-28787,-19478],[-28788,-19478],[-19480,-19479],[-19481,-19479],[-19482,-19479],[-19483,-19479],[-19484,-19479],[-19485,-19479],[-19486,-19479],[-19487,-19479],[-19488,-19479],[-19489,-19479],[-20508,-19479],[-20509,-19479],[-20510,-19479],[-20511,-19479]]
def b2_33 : List (List ℤ) :=
  [[-20512,-19479],[-20513,-19479],[-20514,-19479],[-20515,-19479],[-20516,-19479],[-20517,-19479],[-20518,-19479],[-20519,-19479],[-20520,-19479],[-20521,-19479],[-20522,-19479],[-20524,-19479],[-28758,-19479],[-28759,-19479],[-28768,-19479],[-28770,-19479],[-28774,-19479],[-28775,-19479],[-28776,-19479],[-28777,-19479],[-28779,-19479],[-28780,-19479],[-28781,-19479],[-28782,-19479],[-28783,-19479],[-28785,-19479],[-28786,-19479],[-28787,-19479],[-28788,-19479],[-28789,-19479],[-28792,-19479],[-28793,-19479]]
def b2_34 : List (List ℤ) :=
  [[-19481,-19480],[-19482,-19480],[-19483,-19480],[-19484,-19480],[-19485,-19480],[-19486,-19480],[-19487,-19480],[-19488,-19480],[-19489,-19480],[-20512,-19480],[-20513,-19480],[-20514,-19480],[-20515,-19480],[-20516,-19480],[-20517,-19480],[-20518,-19480],[-20519,-19480],[-20520,-19480],[-20521,-19480],[-28771,-19480],[-28772,-19480],[-28773,-19480],[-28774,-19480],[-28776,-19480],[-28777,-19480],[-28779,-19480],[-28780,-19480],[-28781,-19480],[-28782,-19480],[-28785,-19480],[-28786,-19480],[-28787,-19480]]
def b2_35 : List (List ℤ) :=
  [[-28788,-19480],[-28789,-19480],[-19482,-19481],[-19483,-19481],[-19484,-19481],[-19485,-19481],[-19486,-19481],[-19487,-19481],[-19488,-19481],[-19489,-19481],[-20503,-19481],[-20504,-19481],[-20505,-19481],[-20506,-19481],[-20511,-19481],[-20512,-19481],[-20513,-19481],[-20514,-19481],[-20515,-19481],[-20516,-19481],[-20517,-19481],[-20518,-19481],[-20519,-19481],[-20520,-19481],[-20521,-19481],[-20522,-19481],[-28742,-19481],[-28743,-19481],[-28767,-19481],[-28768,-19481],[-28769,-19481],[-28770,-19481]]
def b2_36 : List (List ℤ) :=
  [[-28773,-19481],[-28774,-19481],[-28775,-19481],[-28776,-19481],[-28777,-19481],[-28778,-19481],[-28779,-19481],[-28780,-19481],[-28781,-19481],[-28782,-19481],[-28783,-19481],[-28784,-19481],[-28785,-19481],[-28786,-19481],[-28787,-19481],[-28788,-19481],[-28789,-19481],[-28792,-19481],[-28793,-19481],[-19483,-19482],[-19484,-19482],[-19485,-19482],[-19486,-19482],[-19487,-19482],[-19488,-19482],[-19489,-19482],[-20503,-19482],[-20504,-19482],[-20505,-19482],[-20506,-19482],[-20508,-19482],[-20509,-19482]]
def b2_37 : List (List ℤ) :=
  [[-20510,-19482],[-20511,-19482],[-20512,-19482],[-20513,-19482],[-20514,-19482],[-20515,-19482],[-20516,-19482],[-20517,-19482],[-20518,-19482],[-20519,-19482],[-20520,-19482],[-20521,-19482],[-28742,-19482],[-28743,-19482],[-28756,-19482],[-28757,-19482],[-28758,-19482],[-28759,-19482],[-28761,-19482],[-28762,-19482],[-28763,-19482],[-28764,-19482],[-28765,-19482],[-28766,-19482],[-28767,-19482],[-28777,-19482],[-28778,-19482],[-28779,-19482],[-28780,-19482],[-28782,-19482],[-28783,-19482],[-28785,-19482]]
def b2_38 : List (List ℤ) :=
  [[-28786,-19482],[-28787,-19482],[-28788,-19482],[-28789,-19482],[-19484,-19483],[-19485,-19483],[-19486,-19483],[-19487,-19483],[-19488,-19483],[-20503,-19483],[-20504,-19483],[-20505,-19483],[-20506,-19483],[-20507,-19483],[-20508,-19483],[-20509,-19483],[-20510,-19483],[-20511,-19483],[-20512,-19483],[-20513,-19483],[-20514,-19483],[-20515,-19483],[-20516,-19483],[-20517,-19483],[-20518,-19483],[-20519,-19483],[-20520,-19483],[-28742,-19483],[-28743,-19483],[-28745,-19483],[-28746,-19483],[-28750,-19483]]
def b2_39 : List (List ℤ) :=
  [[-28751,-19483],[-28756,-19483],[-28757,-19483],[-28758,-19483],[-28759,-19483],[-28761,-19483],[-28762,-19483],[-28763,-19483],[-28764,-19483],[-28766,-19483],[-28771,-19483],[-28772,-19483],[-28773,-19483],[-28774,-19483],[-28775,-19483],[-28776,-19483],[-28777,-19483],[-28778,-19483],[-28779,-19483],[-28780,-19483],[-28781,-19483],[-28782,-19483],[-28783,-19483],[-28784,-19483],[-28785,-19483],[-19485,-19484],[-19486,-19484],[-19487,-19484],[-19488,-19484],[-19489,-19484],[-20503,-19484],[-20504,-19484]]
def b2_40 : List (List ℤ) :=
  [[-20505,-19484],[-20506,-19484],[-20509,-19484],[-20510,-19484],[-20511,-19484],[-20512,-19484],[-20513,-19484],[-20514,-19484],[-20515,-19484],[-20516,-19484],[-20517,-19484],[-20518,-19484],[-20519,-19484],[-20520,-19484],[-20521,-19484],[-20522,-19484],[-28742,-19484],[-28743,-19484],[-28761,-19484],[-28762,-19484],[-28763,-19484],[-28777,-19484],[-28778,-19484],[-28779,-19484],[-28780,-19484],[-28781,-19484],[-28782,-19484],[-28783,-19484],[-28785,-19484],[-28789,-19484],[-28791,-19484],[-19486,-19485]]
def b2_41 : List (List ℤ) :=
  [[-19487,-19485],[-19488,-19485],[-19489,-19485],[-20503,-19485],[-20504,-19485],[-20505,-19485],[-20506,-19485],[-20507,-19485],[-20508,-19485],[-20509,-19485],[-20510,-19485],[-20511,-19485],[-20512,-19485],[-20513,-19485],[-20514,-19485],[-20515,-19485],[-20516,-19485],[-20517,-19485],[-20518,-19485],[-20519,-19485],[-20520,-19485],[-20521,-19485],[-20522,-19485],[-28742,-19485],[-28743,-19485],[-28745,-19485],[-28746,-19485],[-28750,-19485],[-28751,-19485],[-28756,-19485],[-28757,-19485],[-28758,-19485]]
def b2_42 : List (List ℤ) :=
  [[-28759,-19485],[-28761,-19485],[-28762,-19485],[-28763,-19485],[-28764,-19485],[-28765,-19485],[-28768,-19485],[-28769,-19485],[-28771,-19485],[-28772,-19485],[-28773,-19485],[-28774,-19485],[-28775,-19485],[-28777,-19485],[-28778,-19485],[-28779,-19485],[-28781,-19485],[-28782,-19485],[-28783,-19485],[-28784,-19485],[-28785,-19485],[-28786,-19485],[-28789,-19485],[-28791,-19485],[-20503,-19486],[-20504,-19486],[-20505,-19486],[-20506,-19486],[-20507,-19486],[-20508,-19486],[-20509,-19486],[-20510,-19486]]
def b2_43 : List (List ℤ) :=
  [[-20511,-19486],[-20512,-19486],[-20513,-19486],[-20514,-19486],[-20515,-19486],[-20516,-19486],[-28742,-19486],[-28743,-19486],[-28745,-19486],[-28746,-19486],[-28750,-19486],[-28751,-19486],[-28756,-19486],[-28757,-19486],[-28758,-19486],[-28759,-19486],[-28761,-19486],[-28762,-19486],[-28763,-19486],[-28764,-19486],[-28765,-19486],[-28768,-19486],[-28769,-19486],[-28772,-19486],[-28773,-19486],[-28774,-19486],[-28775,-19486],[-28776,-19486],[-20503,-19487],[-20504,-19487],[-20505,-19487],[-20506,-19487]]
def b2_44 : List (List ℤ) :=
  [[-20507,-19487],[-20508,-19487],[-20509,-19487],[-20510,-19487],[-20511,-19487],[-20512,-19487],[-20513,-19487],[-20514,-19487],[-20515,-19487],[-20516,-19487],[-28742,-19487],[-28743,-19487],[-28745,-19487],[-28746,-19487],[-28750,-19487],[-28751,-19487],[-28756,-19487],[-28757,-19487],[-28758,-19487],[-28759,-19487],[-28761,-19487],[-28762,-19487],[-28763,-19487],[-28764,-19487],[-28765,-19487],[-28768,-19487],[-28769,-19487],[-28773,-19487],[-28774,-19487],[-28775,-19487],[-28776,-19487],[-28777,-19487]]
def b2_45 : List (List ℤ) :=
  [[-28779,-19487],[-20503,-19488],[-20504,-19488],[-20505,-19488],[-20506,-19488],[-20507,-19488],[-20508,-19488],[-20509,-19488],[-20510,-19488],[-20511,-19488],[-20512,-19488],[-20513,-19488],[-20514,-19488],[-20515,-19488],[-20516,-19488],[-28742,-19488],[-28743,-19488],[-28745,-19488],[-28746,-19488],[-28750,-19488],[-28751,-19488],[-28756,-19488],[-28757,-19488],[-28758,-19488],[-28759,-19488],[-28761,-19488],[-28763,-19488],[-28764,-19488],[-28768,-19488],[-28773,-19488],[-28774,-19488],[-28776,-19488]]
def b2_46 : List (List ℤ) :=
  [[-20504,-19489],[-20505,-19489],[-20506,-19489],[-20507,-19489],[-20508,-19489],[-20509,-19489],[-20510,-19489],[-20511,-19489],[-20512,-19489],[-20513,-19489],[-20514,-19489],[-20515,-19489],[-20516,-19489],[-28745,-19489],[-28746,-19489],[-28750,-19489],[-28751,-19489],[-28756,-19489],[-28757,-19489],[-28758,-19489],[-28759,-19489],[-28763,-19489],[-28764,-19489],[-28768,-19489],[-28773,-19489],[-28774,-19489],[-28780,-19489],[-28781,-19489],[-28782,-19489],[-28783,-19489],[-20515,-20503],[-20516,-20503]]
def b2_47 : List (List ℤ) :=
  [[-20517,-20503],[-20518,-20503],[-20519,-20503],[-20520,-20503],[-20521,-20503],[-28779,-20503],[-28780,-20503],[-28781,-20503],[-28782,-20503],[-28783,-20503],[-28785,-20503],[-28786,-20503],[-28787,-20503],[-28788,-20503],[-20515,-20504],[-20516,-20504],[-20517,-20504],[-20518,-20504],[-20519,-20504],[-20520,-20504],[-20521,-20504],[-20522,-20504],[-28779,-20504],[-28780,-20504],[-28781,-20504],[-28782,-20504],[-28783,-20504],[-28785,-20504],[-28786,-20504],[-28787,-20504],[-28788,-20504],[-28792,-20504]]
def b2_48 : List (List ℤ) :=
  [[-28793,-20504],[-20515,-20505],[-20516,-20505],[-20517,-20505],[-20518,-20505],[-20519,-20505],[-20520,-20505],[-20521,-20505],[-20522,-20505],[-28779,-20505],[-28780,-20505],[-28781,-20505],[-28782,-20505],[-28783,-20505],[-28785,-20505],[-28786,-20505],[-28787,-20505],[-28788,-20505],[-28792,-20505],[-28793,-20505],[-20515,-20506],[-20516,-20506],[-20517,-20506],[-20518,-20506],[-20519,-20506],[-20520,-20506],[-20521,-20506],[-20522,-20506],[-28779,-20506],[-28780,-20506],[-28781,-20506],[-28782,-20506]]
def b2_49 : List (List ℤ) :=
  [[-28783,-20506],[-28785,-20506],[-28786,-20506],[-28787,-20506],[-28788,-20506],[-28792,-20506],[-28793,-20506],[-20515,-20507],[-20516,-20507],[-20517,-20507],[-20518,-20507],[-20519,-20507],[-20520,-20507],[-20521,-20507],[-20522,-20507],[-28779,-20507],[-28780,-20507],[-28781,-20507],[-28782,-20507],[-28787,-20507],[-28788,-20507],[-28792,-20507],[-28793,-20507],[-20512,-20508],[-20513,-20508],[-20514,-20508],[-20515,-20508],[-20516,-20508],[-20517,-20508],[-20518,-20508],[-20519,-20508],[-20520,-20508]]
def b2_50 : List (List ℤ) :=
  [[-20521,-20508],[-20522,-20508],[-28769,-20508],[-28770,-20508],[-28774,-20508],[-28775,-20508],[-28779,-20508],[-28780,-20508],[-28781,-20508],[-28782,-20508],[-28787,-20508],[-28788,-20508],[-28792,-20508],[-28793,-20508],[-20512,-20509],[-20513,-20509],[-20514,-20509],[-20515,-20509],[-20516,-20509],[-20517,-20509],[-20518,-20509],[-20519,-20509],[-20520,-20509],[-20521,-20509],[-20522,-20509],[-28769,-20509],[-28770,-20509],[-28774,-20509],[-28775,-20509],[-28776,-20509],[-28777,-20509],[-28779,-20509]]
def b2_51 : List (List ℤ) :=
  [[-28780,-20509],[-28781,-20509],[-28782,-20509],[-28785,-20509],[-28786,-20509],[-28787,-20509],[-28788,-20509],[-28792,-20509],[-28793,-20509],[-20512,-20510],[-20513,-20510],[-20514,-20510],[-20515,-20510],[-20516,-20510],[-20517,-20510],[-20518,-20510],[-20519,-20510],[-20520,-20510],[-20521,-20510],[-20522,-20510],[-28769,-20510],[-28770,-20510],[-28774,-20510],[-28775,-20510],[-28776,-20510],[-28777,-20510],[-28779,-20510],[-28780,-20510],[-28781,-20510],[-28782,-20510],[-28783,-20510],[-28785,-20510]]
def b2_52 : List (List ℤ) :=
  [[-28786,-20510],[-28787,-20510],[-28788,-20510],[-28792,-20510],[-28793,-20510],[-20512,-20511],[-20513,-20511],[-20514,-20511],[-20515,-20511],[-20516,-20511],[-20517,-20511],[-20518,-20511],[-20519,-20511],[-20520,-20511],[-20521,-20511],[-20522,-20511],[-28769,-20511],[-28770,-20511],[-28774,-20511],[-28775,-20511],[-28776,-20511],[-28777,-20511],[-28779,-20511],[-28780,-20511],[-28781,-20511],[-28782,-20511],[-28783,-20511],[-28785,-20511],[-28786,-20511],[-28787,-20511],[-28788,-20511],[-28792,-20511]]
def b2_53 : List (List ℤ) :=
  [[-28793,-20511],[-20514,-20512],[-20515,-20512],[-20516,-20512],[-20517,-20512],[-20518,-20512],[-20519,-20512],[-20520,-20512],[-20521,-20512],[-20522,-20512],[-20524,-20512],[-28756,-20512],[-28758,-20512],[-28759,-20512],[-28776,-20512],[-28777,-20512],[-28779,-20512],[-28780,-20512],[-28781,-20512],[-28782,-20512],[-28783,-20512],[-28785,-20512],[-28786,-20512],[-28787,-20512],[-28788,-20512],[-28792,-20512],[-28793,-20512],[-20514,-20513],[-20515,-20513],[-20516,-20513],[-20517,-20513],[-20518,-20513]]
def b2_54 : List (List ℤ) :=
  [[-20519,-20513],[-20520,-20513],[-20521,-20513],[-20524,-20513],[-28756,-20513],[-28758,-20513],[-28759,-20513],[-28776,-20513],[-28777,-20513],[-28779,-20513],[-28780,-20513],[-28781,-20513],[-28782,-20513],[-28783,-20513],[-28785,-20513],[-28786,-20513],[-28787,-20513],[-28788,-20513],[-28789,-20513],[-20515,-20514],[-20516,-20514],[-20517,-20514],[-20518,-20514],[-20519,-20514],[-20520,-20514],[-20521,-20514],[-20522,-20514],[-20524,-20514],[-28756,-20514],[-28758,-20514],[-28759,-20514],[-28761,-20514]]
def b2_55 : List (List ℤ) :=
  [[-28762,-20514],[-28763,-20514],[-28779,-20514],[-28780,-20514],[-28781,-20514],[-28782,-20514],[-28785,-20514],[-28786,-20514],[-28787,-20514],[-28788,-20514],[-28789,-20514],[-28792,-20514],[-28793,-20514],[-20517,-20515],[-20518,-20515],[-20519,-20515],[-20520,-20515],[-20521,-20515],[-28742,-20515],[-28743,-20515],[-28745,-20515],[-28746,-20515],[-28750,-20515],[-28751,-20515],[-28756,-20515],[-28757,-20515],[-28758,-20515],[-28759,-20515],[-28761,-20515],[-28762,-20515],[-28763,-20515],[-28764,-20515]]
def b2_56 : List (List ℤ) :=
  [[-28765,-20515],[-28768,-20515],[-28769,-20515],[-28785,-20515],[-28786,-20515],[-28787,-20515],[-28788,-20515],[-28789,-20515],[-20517,-20516],[-20518,-20516],[-20519,-20516],[-20520,-20516],[-20521,-20516],[-28742,-20516],[-28743,-20516],[-28745,-20516],[-28746,-20516],[-28750,-20516],[-28751,-20516],[-28756,-20516],[-28757,-20516],[-28758,-20516],[-28759,-20516],[-28762,-20516],[-28763,-20516],[-28764,-20516],[-28765,-20516],[-28768,-20516],[-28769,-20516],[-28771,-20516],[-28772,-20516],[-28785,-20516]]
def b2_57 : List (List ℤ) :=
  [[-28786,-20516],[-28787,-20516],[-28788,-20516],[-28789,-20516],[-28742,-20517],[-28743,-20517],[-28745,-20517],[-28746,-20517],[-28750,-20517],[-28751,-20517],[-28756,-20517],[-28757,-20517],[-28758,-20517],[-28759,-20517],[-28761,-20517],[-28762,-20517],[-28763,-20517],[-28764,-20517],[-28765,-20517],[-28768,-20517],[-28769,-20517],[-28772,-20517],[-28773,-20517],[-28774,-20517],[-28775,-20517],[-28776,-20517],[-28742,-20518],[-28743,-20518],[-28745,-20518],[-28746,-20518],[-28750,-20518],[-28751,-20518]]
def b2_58 : List (List ℤ) :=
  [[-28756,-20518],[-28757,-20518],[-28758,-20518],[-28759,-20518],[-28761,-20518],[-28762,-20518],[-28763,-20518],[-28764,-20518],[-28765,-20518],[-28768,-20518],[-28769,-20518],[-28773,-20518],[-28774,-20518],[-28776,-20518],[-28742,-20519],[-28743,-20519],[-28745,-20519],[-28746,-20519],[-28750,-20519],[-28751,-20519],[-28756,-20519],[-28757,-20519],[-28758,-20519],[-28759,-20519],[-28761,-20519],[-28762,-20519],[-28763,-20519],[-28764,-20519],[-28765,-20519],[-28773,-20519],[-28774,-20519],[-28775,-20519]]
def b2_59 : List (List ℤ) :=
  [[-28776,-20519],[-28777,-20519],[-28779,-20519],[-28742,-20520],[-28743,-20520],[-28745,-20520],[-28746,-20520],[-28750,-20520],[-28751,-20520],[-28756,-20520],[-28757,-20520],[-28758,-20520],[-28759,-20520],[-28761,-20520],[-28763,-20520],[-28764,-20520],[-28772,-20520],[-28773,-20520],[-28774,-20520],[-28775,-20520],[-28776,-20520],[-28742,-20521],[-28743,-20521],[-28745,-20521],[-28746,-20521],[-28750,-20521],[-28751,-20521],[-28756,-20521],[-28757,-20521],[-28758,-20521],[-28759,-20521],[-28761,-20521]]
def b2_60 : List (List ℤ) :=
  [[-28763,-20521],[-28764,-20521],[-28773,-20521],[-28774,-20521],[-28775,-20521],[-28776,-20521],[-28777,-20521],[-28779,-20521],[-28745,-20522],[-28746,-20522],[-28750,-20522],[-28751,-20522],[-28756,-20522],[-28757,-20522],[-28758,-20522],[-28759,-20522],[-28763,-20522],[-28764,-20522],[-28774,-20522],[-28775,-20522],[-28763,-20524],[-28764,-20524],[-28768,-20524],[-28770,-20524],[-28779,-28742],[-28780,-28742],[-28781,-28742],[-28782,-28742],[-28783,-28742],[-28785,-28742],[-28786,-28742],[-28787,-28742]]
def b2_61 : List (List ℤ) :=
  [[-28788,-28742],[-28779,-28743],[-28780,-28743],[-28781,-28743],[-28782,-28743],[-28783,-28743],[-28785,-28743],[-28786,-28743],[-28787,-28743],[-28788,-28743],[-28779,-28745],[-28780,-28745],[-28781,-28745],[-28782,-28745],[-28787,-28745],[-28788,-28745],[-28792,-28745],[-28793,-28745],[-28779,-28746],[-28780,-28746],[-28781,-28746],[-28782,-28746],[-28787,-28746],[-28788,-28746],[-28792,-28746],[-28793,-28746],[-28779,-28750],[-28780,-28750],[-28781,-28750],[-28782,-28750],[-28787,-28750],[-28788,-28750]]
def b2_62 : List (List ℤ) :=
  [[-28792,-28750],[-28793,-28750],[-28779,-28751],[-28780,-28751],[-28781,-28751],[-28782,-28751],[-28787,-28751],[-28788,-28751],[-28792,-28751],[-28793,-28751],[-28769,-28756],[-28770,-28756],[-28774,-28756],[-28775,-28756],[-28779,-28756],[-28780,-28756],[-28781,-28756],[-28782,-28756],[-28787,-28756],[-28788,-28756],[-28792,-28756],[-28793,-28756],[-28769,-28757],[-28774,-28757],[-28775,-28757],[-28779,-28757],[-28780,-28757],[-28781,-28757],[-28782,-28757],[-28787,-28757],[-28788,-28757],[-28792,-28757]]
def b2_63 : List (List ℤ) :=
  [[-28793,-28757],[-28769,-28758],[-28770,-28758],[-28774,-28758],[-28775,-28758],[-28779,-28758],[-28780,-28758],[-28781,-28758],[-28782,-28758],[-28787,-28758],[-28788,-28758],[-28792,-28758],[-28793,-28758],[-28769,-28759],[-28770,-28759],[-28774,-28759],[-28775,-28759],[-28779,-28759],[-28780,-28759],[-28781,-28759],[-28782,-28759],[-28787,-28759],[-28788,-28759],[-28792,-28759],[-28793,-28759],[-28776,-28761],[-28777,-28761],[-28785,-28761],[-28786,-28761],[-28787,-28761],[-28788,-28761],[-28776,-28762]]
def b2_64 : List (List ℤ) :=
  [[-28777,-28762],[-28780,-28762],[-28781,-28762],[-28782,-28762],[-28783,-28762],[-28776,-28763],[-28777,-28763],[-28779,-28763],[-28780,-28763],[-28781,-28763],[-28782,-28763],[-28785,-28763],[-28786,-28763],[-28787,-28763],[-28788,-28763],[-28792,-28763],[-28793,-28763],[-28779,-28764],[-28780,-28764],[-28781,-28764],[-28782,-28764],[-28783,-28764],[-28787,-28764],[-28788,-28764],[-28792,-28764],[-28793,-28764],[-28779,-28765],[-28780,-28765],[-28781,-28765],[-28782,-28765],[-28783,-28765],[-28779,-28768]]
def b2_65 : List (List ℤ) :=
  [[-28780,-28768],[-28781,-28768],[-28782,-28768],[-28788,-28768],[-28774,-28769],[-28775,-28769],[-28779,-28769],[-28780,-28769],[-28781,-28769],[-28782,-28769],[-28785,-28773],[-28786,-28773],[-28788,-28773],[-28789,-28773],[-28779,-28774],[-28785,-28774],[-28786,-28774],[-28787,-28774],[-28788,-28774],[-28789,-28774],[-28792,-28774],[-28793,-28774],[-28778,-28775],[-28779,-28775],[-28785,-28775],[-28786,-28775],[-28787,-28775],[-28792,-28775],[-28793,-28775],[-28785,-28776],[-28786,-28776],[-28787,-28776]]
def b2_66 : List (List ℤ) :=
  [[-28788,-28776],[-28785,-28777],[-28786,-28777],[-28784,-28778],[-28784,-28779],[-28785,-28779],[-28786,-28779],[-28787,-28779],[-28787,-28780],[-28789,-28780],[-28787,-28781],[-28789,-28781],[-28789,-28782],[-28789,-28783]]
private def maskTable₂p0 (i:ℕ) : ℕ := packedAt 0x200000000000268360000000098660000000261780000000a17800000025856000000098560000000a15800000096138000000984e000000284e000000958460000009846000002583e0000000000000000000aaa0180000002a0580000002a03 0x30202c2029202640238020a01de01b40188015e0136010a00e200ba0058002c0000 (i%16)
private def maskTable₂p1 (i:ℕ) : ℕ := packedAt 0x200000000000000959846000000000000000a5611800000000000000996118000000000000025984600000000000000296118000000000000026611800000000000002984600000000000002684600000000000002a11800000000000009960f800000000000095a0f80000000000002983e0000000000002683e0000000000000995836000000000000998360000000000025a0d 0x4a20452040003b00362031402c8027e023601f001a4015c011600d2008600420000 (i%16)
private def maskTable₂p2 (i:ℕ) : ℕ := packedAt 0x800000000000000009a1780000000000000000a85e0000000000000000998560000000000000000a61580000000000000009a158000000000000000a85600000000000000026584e0000000000000009661380000000000000095a138000000000000000a584e0000000000000009984e0000000000000025a138000000000000002984e000000000000002684e000000000000002a13800000000000000265611 0x50804b40462040e03bc036c031e02ca0278022801d60186013800ea009e00540000 (i%16)
private def maskTable₂p3 (i:ℕ) : ℕ := packedAt 0x20000000000000000000000002998460000000000000000000000009a61180000000000000000000000099a118000000000000000000000002a611800000000000000000000000a6846000000000000000000000009a84600000000000000000000000aa1180000000000000000000000099660f8000000000000000000000026660f80000000000000000000000295a0f800000000000000000000026683e0000000000000000000000295983600000000000000000000026660d800000000000000000000265a0d800000000000000000000a683600000000000000000a617 0x6fe06860610059c052804b6044603d8036002ec0278020a0196012800bc00560000 (i%16)
private def maskTable₂p4 (i:ℕ) : ℕ := packedAt 0x80000000002886000000000000000000000000000a6615800000000000000000000000000a6856000000000000000000000000009a85600000000000000000000000000aa158000000000000000000000000029984e000000000000000000000000026984e000000000000000000000000099a13800000000000000000000000029a138000000000000000000000000269611800000000000000000000000029661180000000000000000000000009998460000000000000000000000009698460000000000000000000000009968460000000000000000000000095a8460000000000000000000000000a9611 0x768073206b0063205b6053c04be044203c8035002d4025801de016600ee007a0000 (i%16)
private def maskTable₂p5 (i:ℕ) : ℕ := packedAt 0x200000000000000000000000a990600000000000000000296e00000000000000000a59800000000000000009595e0000000000000000265780000000000000000a5780000000000000002956000000000000000256538000000000000000294e00000000000000026518000000000000000993e000000000000000293e000000000000000264b8000000000000000000000000000000000000000002a6a3180000000000000000000000000000000000002a6a2d800000000000000000000000000000002a6a29 0x63605c60572052004ca0478042803da0388033a02ec029e02520204014400980000 (i%16)
private def maskTable₂p6 (i:ℕ) : ℕ := packedAt 0x20000000000000000000000000000265664b800000000000000000000000000096664b800000000000000000000000000099992e0000000000000000000000000009a64b8000000000000000000000000002a64b800000000000000000000000000a692e00000000000000000000000000aa4b800000000000000000000000009a64980000000000000000000000002669260000000000000000000000000a69260000000000000000000000002a9260000000000000000000000000996647800000000000000000000000099991e00000000000000000000000029991e000000000000000000000000a99160000000000000000000000029a43 0x7ce074006b8063205b0053004b2043803bc034202ca025601d8015e00e600720000 (i%16)
private def maskTable₂p7 (i:ℕ) : ℕ := packedAt 0x8000000000000000000000000000000959993e0000000000000000000000000000000295993e000000000000000000000000000000099664f800000000000000000000000000000099993e00000000000000000000000000000259a4f80000000000000000000000000000002a593e00000000000000000000000000000029993e0000000000000000000000000000009a64f8000000000000000000000000000002a64f800000000000000000000000000000a693e0000000000000000000000000000099993600000000000000000000000000000a664d800000000000000000000000000009a64d800000000000000000000000000026693600000000000000000000000000025a93600000000000000000000000000026a4d 0x8d4083e07a60710067e05f0055e04ce044003b4032a029e0214018c010600820000 (i%16)
private def maskTable₂p8 (i:ℕ) : ℕ := packedAt 0x80000000000000000000000000000000026994e000000000000000000000000000000000a5a538000000000000000000000000000000025a94e000000000000000000000000000000000a994e0000000000000000000000000000000029a538000000000000000000000000000000026a53800000000000000000000000000000002a94e000000000000000000000000000000000999651800000000000000000000000000000000299651800000000000000000000000000000000a9651800000000000000000000000000000026694600000000000000000000000000000002a651800000000000000000000000000000029a5180000000000000000000000000000009a9460000000000000000000000000000002a9460000000000000000000000000000000265664f 0x95808be0824078e06f6066005cc053a049c0400036802d6024401b40126009a0000 (i%16)
private def maskTable₂p9 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000000000000009a95e00000000000000000000000000000000000aa57800000000000000000000000000000000002656956000000000000000000000000000000000002a59560000000000000000000000000000000000269956000000000000000000000000000000000099a5580000000000000000000000000000000000a99560000000000000000000000000000000000a695600000000000000000000000000000000026a558000000000000000000000000000000000aa558000000000000000000000000000000000265994e0000000000000000000000000000000000a5994e000000000000000000000000000000000266653800000000000000000000000000000000265a5380000000000000000000000000000000256a538000000000000000000000000000000000a6653 0x9e2094208a407fe075a06ba061c057e04e2044803b0030e026e01d00134009c0000 (i%16)
private def maskTable₂p10 (i:ℕ) : ℕ := packedAt 0x800000000000000000299c600000000000000000269c6000000000000000002a7180000000000000000299be0000000000000000269be0000000000000000a66d80000000000000002a6b80000000000000009a678000000000000002699600000000000000000000000000000000000000a696e00000000000000000000000000000000000026a59800000000000000000000000000000000000099995e0000000000000000000000000000000000000a965780000000000000000000000000000000000026995e000000000000000000000000000000000000a995e0000000000000000000000000000000000029a57 0x784072a06d2067c062605d20580053004e0049203e60340029601ec014600a20000 (i%16)
private def maskTable₂p11 (i:ℕ) : ℕ := packedAt 0x800000000000000000000000a9f600000000000000000000000a67b800000000000000000000009a7b80000000000000000000000a9ee0000000000000000000000999e60000000000000000000000a67980000000000000000000009a798000000000000000000000a9e6000000000000000000000a6778000000000000000000009a7780000000000000000000299d60000000000000000000269d600000000000000000002a758000000000000000000299ce000000000000000000269ce0000000000000000002a73 0x65405e60578050c04a2043603cc036402fe0298023401d20172011400b6005a0000 (i%16)
private def maskTable₂p12 (i:ℕ) : ℕ := packedAt 0x88000000000000000000000000000000000000000000000000000000000022000802800000000000000000000000000000000000000000000000000000000000a0e880000000000000000000000000000000000000000000000000000000000220ca00000000000000000000000000000000000000000000000000000000000283200000000000000000000000000029a160000000000000000000000000009a858000000000000000000000000009a83800000000000000000000000000aa0e00000000000000000000000000a681800000000000000000000000009a8180000000000000000000000000aa060000000000000000000000000a67f80000000000000000000000009a7f8000000000000000000000000a9fe000000000000000000000000a67d8000000000000000000000009a7d 0x9a4089607980698059a051a049c042003a6032c02b4023e01c8015400e200700000 (i%16)
private def maskTable₂p13 (i:ℕ) : ℕ := packedAt 0x22000000000000000000000000000000000000000000000000000000000008800082a800000000000000000000000000000000000000000000000000000000000a1a8800000000000000000000000000000000000000000000000000000000002218a000000000000000000000000000000000000000000000000000000000002862200000000000000000000000000000000000000000000000000000000000880020888000000000000000000000000000000000000000000000000000000000022000206880000000000000000000000000000000000000000000000000000000000220000812800000000000000000000000000000000000000000000000000000000000a168800000000000000000000000000000000000000000000000000000000002214a000000000000000000000000000000000000000000000000000000000002852200000000000000000000000000000000000000000000000000000000000880081a200000000000000000000000000000000000000000000000000000000000880020488000000000000000000000000000000000000000000000000000000000022000202a00000000000000000000000000000000000000000000000000000000000284a2000000000000000000000000000000000000000000000000000000000008842800000000000000000000000000000000000000000000000000000000000a10 0x105e0f4e0e500d500c520b440a340922082407240626051a040c02fc01fe00fe0000 (i%16)
private def maskTable₂p14 (i:ℕ) : ℕ := packedAt 0x88000000000000000000000000000000000000000000000000002200000000002248800000000000000000000000000000000000000000000000000220000000000088a8000000000000000000000000000000000000000000000000000a508800000000000000000000000000000000000000000000000000224ea000000000000000000000000000000000000000000000000000293a8000000000000000000000000000000000000000000000000000a4c8800000000000000000000000000000000000000000000000000224aa000000000000000000000000000000000000000000000000000292a8000000000000000000000000000000000000000000000000000a4888000000000000000000000000000000000000000000000000002246a000000000000000000000000000000000000000000000000000291a200000000000000000000000000000000000000000000000000088000000008828000000000000000000000000000000000000000000000000000a4488000000000000000000000000000000000000000000000000002242a000000000000000000000000000000000000000000000000000290a8000000000000000000000000000000000000000000000000000a40 0xe6c0d600c520b740a9409b608d807f8071a063c055c047e037a029c01bc00de0000 (i%16)
private def maskTable₂p15 (i:ℕ) : ℕ := packedAt 0xa000000000000000000000000000000000000000000000000000299a200000000000000000000000000000000000000000000000000089928000000000000000000000000000000000000000000000000000a608800000000000000000000000000000000000000000000000000225ea000000000000000000000000000000000000000000000000000297a8000000000000000000000000000000000000000000000000000a5c8800000000000000000000000000000000000000000000000000225aa000000000000000000000000000000000000000000000000000296a20000000000000000000000000000000000000000000000000008800000000000226a00000000000000000000000000000000000000000000000000029622000000000000000000000000000000000000000000000000000895a8000000000000000000000000000000000000000000000000000a5688000000000000000000000000000000000000000000000000002200000000000224a00000000000000000000000000000000000000000000000000029522000000000000000000000000000000000000000000000000000894a8000000000000000000000000000000000000000000000000000a52 0xe500d720c920bb40ad409f609180838075a0648056a048a03ac029c01be00de0000 (i%16)
private def maskTable₂p16 (i:ℕ) : ℕ := packedAt 0x2200000000000000000000000000000000000000000000000000089d28000000000000000000000000000000000000000000000000000a7488000000000000000000000000000000000000000000000000002200000000000000008c28000000000000000000000000000000000000000000000000000a7288000000000000000000000000000000000000000000000000002270a00000000000000000000000000000000000000000000000000029c22000000000000000000000000000000000000000000000000000880000000000000023088000000000000000000000000000000000000000000000000002200000000000000022e88000000000000000000000000000000000000000000000000002200000000000000008b28000000000000000000000000000000000000000000000000000a6e8800000000000000000000000000000000000000000000000000226ca00000000000000000000000000000000000000000000000000029b28000000000000000000000000000000000000000000000000000a68880000000000000000000000000000000000000000000000000022000000000000008b2200000000000000000000000000000000000000000000000000088000000000000008aa20000000000000000000000000000000000000000000000000008800000000000000228 0xfaa0eca0dec0cca0bec0b0c0a2e091007f006ce05f0051004320354023a011e0000 (i%16)
private def maskTable₂p17 (i:ℕ) : ℕ := packedAt 0x28000000000000000000000000000000000000000000000000000a80880000000000000000000000000000000000000000000000000022000000000000000008e2200000000000000000000000000000000000000000000000000088000000000000000008da20000000000000000000000000000000000000000000000000008800000000000000000234a00000000000000000000000000000000000000000000000000029fa200000000000000000000000000000000000000000000000000089f28000000000000000000000000000000000000000000000000000a7c880000000000000000000000000000000000000000000000000022000000000000000008d2200000000000000000000000000000000000000000000000000088000000000000000008ca8000000000000000000000000000000000000000000000000000a7a88000000000000000000000000000000000000000000000000002278a00000000000000000000000000000000000000000000000000029e22000000000000000000000000000000000000000000000000000880000000000000002348800000000000000000000000000000000000000000000000000220000000000000000232880000000000000000000000000000000000000000000000000022000000000000000008c28000000000000000000000000000000000000000000000000000a76 0x10260f480e220cfa0bd00af20a120934080e06e606080528044a0328020400de0000 (i%16)
private def maskTable₂p18 (i:ℕ) : ℕ := packedAt 0xa0000000000000000000000000000000000000000000002aca8000000000000000000000000000000000000000000000aaea0000000000000000000000000000000000000000000002aaa8000000000000000000000000000000000000000000000aa6a000000000000000000000000000000000000000000000000000280000000000000000008fa8000000000000000000000000000000000000000000000000000a888800000000000000000000000000000000000000000000000000220000000000000000008f22000000000000000000000000000000000000000000000000000880000000000000000008ea200000000000000000000000000000000000000000000000000088000000000000000000238a0000000000000000000000000000000000000000000000000002a1a20000000000000000000000000000000000000000000000000008a128000000000000000000000000000000000000000000000000000a848800000000000000000000000000000000000000000000000000220000000000000000023a8800000000000000000000000000000000000000000000000000220000000000000000008e28000000000000000000000000000000000000000000000000000a8288000000000000000000000000000000000000000000000000002280 0xf500e8a0dc40cfe0c380b0e0a30090607da06ac05ce04ee041002e801be00e00000 (i%16)
private def maskTable₂p19 (i:ℕ) : ℕ := packedAt 0x220000000000000000000000000000000000000000000008b2a20000000000000000000000000000000000000000000008b1a8000000000000000000000000000000000000000000000ac6880000000000000000000000000000000000000000000022000000000000a4a8000000000000000000000000000000000000000000000ac4a0000000000000000000000000000000000000000000002b0a20000000000000000000000000000000000000000000008800000000000a428000000000000000000000000000000000000000000000ac0880000000000000000000000000000000000000000000022bea0000000000000000000000000000000000000000000002afa8000000000000000000000000000000000000000000000abaa0000000000000000000000000000000000000000000002ae220000000000000000000000000000000000000000000008ada8000000000000000000000000000000000000000000000ab6880000000000000000000000000000000000000000000022000000000a3a8000000000000000000000000000000000000000000000ab4 0xcf60c2e0b660aa009a608e0081a0722065c059404ce04080342027a01b400c60000 (i%16)
private def maskTable₂p20 (i:ℕ) : ℕ := packedAt 0x28000000000000000000000000000000000000000000000adc880000000000000000000000000000000000000000000022daa0000000000000000000000000000000000000000000002b6a2000000000000000000000000000000000000000000000880000000000000029a880000000000000000000000000000000000000000000022000000000000000298a0000000000000000000000000000000000000000000002b6220000000000000000000000000000000000000000000008b5a8000000000000000000000000000000000000000000000ad6a0000000000000000000000000000000000000000000002b5220000000000000000000000000000000000000000000008b4a8000000000000000000000000000000000000000000000ad288000000000000000000000000000000000000000000002200000000000000a5a8000000000000000000000000000000000000000000000ad0a0000000000000000000000000000000000000000000002b3a2000000000000000000000000000000000000000000000880000000000000a528000000000000000000000000000000000000000000000acc 0xd5e0c980bd00b0a0a0408fc0836076e06a805e2051a04540352028c01c600c60000 (i%16)
private def maskTable₂p21 (i:ℕ) : ℕ := packedAt 0x880000000000000000000000000000000000000000000022eea0000000000000000000000000000000000000000000002bba200000000000000000000000000000000000000000000088000000000000000002a28800000000000000000000000000000000000000000000220000000000000000002a0880000000000000000000000000000000000000000000022eaa0000000000000000000000000000000000000000000002baa8000000000000000000000000000000000000000000000ae8a0000000000000000000000000000000000000000000002b9a200000000000000000000000000000000000000000000088000000000000000029ea0000000000000000000000000000000000000000000002b9220000000000000000000000000000000000000000000008b8a8000000000000000000000000000000000000000000000ae2880000000000000000000000000000000000000000000022000000000000000029ca0000000000000000000000000000000000000000000002b8220000000000000000000000000000000000000000000008b7a8000000000000000000000000000000000000000000000ade 0xd900cc80c020af009dc0914084e078806c205b404ee042603600254018e00c60000 (i%16)
private def maskTable₂p22 (i:ℕ) : ℕ := packedAt 0x800000000002ff80000000000bfe0000000000bfe0000000002ff8000000002ff8000bfe000bfe002ff80bfe0bfe2ffa0000000000000000000000000000000000000000000002bea8000000000000000000000000000000000000000000000af6a0000000000000000000000000000000000000000000002bd28000000000000000000000000000000000000000000000af28800000000000000000000000000000000000000000000220000000000000000002a4 0x5a80570053a050604d404a4048a0472045c044a043a042c036602a001da01140000 (i%16)
private def maskTable₂p23 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000000000000000000bfe0000000000000000000000000000000000000bfe0000000000000000000000000000000000002ff80000000000000000000000000000000002ff800000000000000000000002ff80000000000000000000000bfe0000000000000000000000bfe0000000000000000000002ff8000000000000000000002ff800000000000000000000bfe00000000000000000000bfe00000000000000000002ff80000000000002ff8000000000000bfe000000000000bfe000000000002ff 0x67605ce052e049003fc0394032e02ca0268020801aa014e00f400b40076003a0000 (i%16)
private def maskTable₂p24 (i:ℕ) : ℕ := packedAt 0x2000c06003018030183018c06c060000000000000000000000000000000000000000000002ff8000000000000000000000000000000000000000000002ff80000000000000000000000000000000000000000000bfe0000000000000000000000000000000000000000000bfe0000000000000000000000000000000000000000002ff8000000000000000000000000000000000000000002ff800000000000000000000000000000000000000002ff80000000000000000000000000000000000000000bfe0000000000000000000000000000000000000000bfe0000000000000000000000000000000000000002ff 0x77e07660750073c072c071e07120650059004d6041e036802b40204015600aa0000 (i%16)
private def maskTable₂p25 (i:ℕ) : ℕ := packedAt 0x200000000000000000000c06000000000000000000030180000000000000000003018000000000000000000c06000000000000000000c06000000000000000003018000000000000c06000000000000c06000000000003018000000000030180000000000c060000000000c06000000000301800000000301800000000c060000000301 0x41a03be0364030c02b60262021001d20196015c012400ee00ba00880058002a0000 (i%16)
private def maskTable₂p26 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000000000000000000000c060000000000000000000000000000000000000000030180000000000000000000000000000000000000000c060000000000000000000000000000000000000000c06000000000000000000000000000000000000000301800000000000000000000000000000000000000301800000000000000000000000000000000000000c0600000000000000000000000000000000000030180000000000000000000000000000000000030180000000000000000000000000000000003018000000000000000000000000000000000c06000000000000000000000030180000000000000000000003018000000000000000000000c06000000000000000000000c0600000000000000000000301 0x902084e079c06ee0642059804f0044a03ac0310027c01ea0184012000be005e0000 (i%16)
private def maskTable₂p27 (i:ℕ) : ℕ := packedAt 0x800000000c0e00000000c0e000000030380000003038000000c0e000000c0e003038030380c0e0c0e303b03800000000000000000000000000000000000000000000301800000000000000000000000000000000000000000000c060000000000000000000000000000000000000000000c06000000000000000000000000000000000000000000301 0x448041a03ee03c4039c03760352033c03280316030602f802ec022c016e00b60000 (i%16)
private def maskTable₂p28 (i:ℕ) : ℕ := packedAt 0x80000000000000000000c0e0000000000000000000c0e000000000000000000303800000000000000000303800000000000000000c0e00000000000000000c0e000000000000000030380000000000000003038000000000000000c0e000000000000c0e000000000003038000000000030380000000000c0e0000000000c0e000000000303800000000303 0x45c040203aa0354030002ae025e021001c4017a013e010400cc0096006200300000 (i%16)
private def maskTable₂p29 (i:ℕ) : ℕ := packedAt 0x80000000000000000000000000000000000000c0e0000000000000000000000000000000000000c0e000000000000000000000000000000000000303800000000000000000000000000000000000303800000000000000000000000000000000000c0e00000000000000000000000000000000000c0e000000000000000000000000000000000030380000000000000000000000000000000003038000000000000000000000000000000000c0e000000000000000000000000000000c0e00000000000000000000000000000303800000000000000000000000000003038000000000000000000000c0e000000000000000000000c0e0000000000000000000030380000000000000000000303 0x86c07ca072a068c05f0055604be042803940302027e01fc017c011a00ba005c0000 (i%16)
private def maskTable₂p30 (i:ℕ) : ℕ := packedAt 0x80003058030580c160c16305b0580000000000000000000000000000000000000000003038000000000000000000000000000000000000000000c0e000000000000000000000000000000000000000000c0e000000000000000000000000000000000000000003038000000000000000000000000000000000000000030380000000000000000000000000000000000000003038000000000000000000000000000000000000000c0e000000000000000000000000000000000000000c0e0000000000000000000000000000000000000030380000000000000000000000000000000000000303 0x738071c070806f606e606d806cc0614055e04aa03f80348029c01f2014a00a40000 (i%16)
private def maskTable₂p31 (i:ℕ) : ℕ := packedAt 0x80000000000000305800000000000c1600000000000c16000000000030580000000003058000000000c16000000000c16000000003058000000030580000000c160000000c16000000305800000305800000c1600000c160000305 0x2d80294025a022201ec01b801860156012800fc00d200aa00840060003e001e0000 (i%16)
private def maskTable₂p32 (i:ℕ) : ℕ := packedAt 0x8000000000000000000000000030580000000000000000000000000c16000000000000000000000c16000000000000000000003058000000000000000000030580000000000000000000c160000000000000000000c16000000000000000000305800000000000000000305800000000000000000c1600000000000000000c16000000000000000030580000000000000003058000000000000000c16000000000000000c1600000000000000305 0x57004fc048a042a03cc0370031602be0268021401c20172012400d8008e00460000 (i%16)
private def maskTable₂p33 (i:ℕ) : ℕ := packedAt 0x80000000000000000000000000000000000003058000000000000000000000000000000000000c16000000000000000000000000000000000000c16000000000000000000000000000000000003058000000000000000000000000000000000030580000000000000000000000000000000000c160000000000000000000000000000000000c16000000000000000000000000000000000305800000000000000000000000000000000305800000000000000000000000000000000c160000000000000000000000000000000c1600000000000000000000000000000030580000000000000000000000000003058000000000000000000000000000c16000000000000000000000000000c1600000000000000000000000000305 0x8d80838079a06fe066405cc053604a20410038002f2026a01e4016800ee00760000 (i%16)
private def maskTable₂p34 (i:ℕ) : ℕ := packedAt 0x800030780c1e0c1e307b078000000000000000000000000000000000000000000c16000000000000000000000000000000000000000000c16000000000000000000000000000000000000000003058000000000000000000000000000000000000000030580000000000000000000000000000000000000000c160000000000000000000000000000000000000000c16000000000000000000000000000000000000000305800000000000000000000000000000000000000305800000000000000000000000000000000000000c1600000000000000000000000000000000000000c160000000000000000000000000000000000000305 0x7bc07a0078e077e0770076406ae05fa0548049803ea033e029401ec014600a20000 (i%16)
private def maskTable₂p35 (i:ℕ) : ℕ := packedAt 0x2000000000000000c1e00000000000000307800000000000003078000000000030780000000003078000000000c1e000000000c1e000000003078000000030780000000c1e0000000c1e000000307800000307800000c1e00000c1e0000307 0x2f602ae0268022401ec01b801860156012800fc00d200aa00840060003e001e0000 (i%16)
private def maskTable₂p36 (i:ℕ) : ℕ := packedAt 0x200000000000000000000000000003078000000000000000000000000000307800000000000000000000000000c1e00000000000000000000000000c1e0000000000000000000000000307800000000000000000000c1e00000000000000000000c1e000000000000000000030780000000000000000003078000000000000000000c1e000000000000000000c1e000000000000000003078000000000000000030780000000000000000c1e0000000000000000c1e000000000000000307 0x5f2057404f80482040e039c033e02e20288023001da0186013400e40096004a0000 (i%16)
private def maskTable₂p37 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000000000000000030780000000000000000000000000000000000003078000000000000000000000000000000000000c1e000000000000000000000000000000000000c1e000000000000000000000000000000000003078000000000000000000000000000000000030780000000000000000000000000000000000c1e0000000000000000000000000000000000c1e000000000000000000000000000000000307800000000000000000000000000000000307800000000000000000000000000000000c1e00000000000000000000000000000000c1e0000000000000000000000000000000307800000000000000000000000000000030780000000000000000000000000000030780000000000000000000000000000307 0x92a088807e8074a06ae0614057c04e6045203c0033002a20216018c010400800000 (i%16)
private def maskTable₂p38 (i:ℕ) : ℕ := packedAt 0x8000000030980000000c260000000c26000000309800000309800000c260c26309b09800000000000000000000000000000000000000000c1e000000000000000000000000000000000000000030780000000000000000000000000000000000000003078000000000000000000000000000000000000000c1e000000000000000000000000000000000000000c1e0000000000000000000000000000000000000030780000000000000000000000000000000000000307 0x5bc05900566053e051804f404d204c204b404a803f60348029c01f2014a00a40000 (i%16)
private def maskTable₂p39 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000000000000c26000000000000000000000000000000003098000000000000000000000000000000030980000000000000000000000000000000c26000000000000000000030980000000000000000003098000000000000000000c26000000000000000000c26000000000000000003098000000000000000030980000000000000000c260000000000000000c260000000000000003098000000000c26000000000c2600000000309 0x5a60516048803fc0372031802c0026a021601c40174012600da0090005e002e0000 (i%16)
private def maskTable₂p40 (i:ℕ) : ℕ := packedAt 0x8c2ec2e0000000000000000000000000000000000000000c26000000000000000000000000000000000000000309800000000000000000000000000000000000000309800000000000000000000000000000000000000c2600000000000000000000000000000000000000c26000000000000000000000000000000000000030980000000000000000000000000000000000003098000000000000000000000000000000000000c26000000000000000000000000000000000000c26000000000000000000000000000000000003098000000000000000000000000000000000030980000000000000000000000000000000000c260000000000000000000000000000000000c26000000000000000000000000000000000309 0x8cc08be08b20806075c06b4060e056a04c80428038a02ee025401bc012600920000 (i%16)
private def maskTable₂p41 (i:ℕ) : ℕ := packedAt 0x2000000000030b800000000c2e00000000c2e000000030b800000030b8000000c2e000000c2e0000030b8000030b80000c2e0000c2e00030b80030b800c2e00c2e030b 0x21601e001b20186015c0134010e00ea00c800a8008a006e0054003c002600120000 (i%16)
private def maskTable₂p42 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000000c2e00000000000000000000030b80000000000000000000030b80000000000000000030b800000000000000000c2e00000000000000000c2e000000000000000030b800000000000000030b8000000000000000c2e000000000000000c2e0000000000000030b8000000000000030b80000000000000c2e000000000000c2e0000000000030b8000000000030b 0x4d6045e03fc039c034802f602a60258020c01c2017a013400f000ae007200380000 (i%16)
private def maskTable₂p43 (i:ℕ) : ℕ := packedAt 0x200000000000000000000000000000000000030b80000000000000000000000000000000000030b800000000000000000000000000000000000c2e00000000000000000000000000000000000c2e000000000000000000000000000000000030b800000000000000000000000000000000030b8000000000000000000000000000000000c2e000000000000000000000000000000000c2e0000000000000000000000000000000030b8000000000000000000000000000000030b80000000000000000000000000000000c2e0000000000000000000000000000000c2e000000000000000000000000000000c2e00000000000000000000000000000c2e0000000000000000000000000000c2e00000000000000000000000000030b 0x8de084007a4070a067205dc054804b604260398030c028201fa017600f6007a0000 (i%16)
private def maskTable₂p44 (i:ℕ) : ℕ := packedAt 0x200000000c36000000030d800000030d8000000c36000000c360000030d8000030d80000c360000c3600030d80030d800c3600c36030d830db0d 0x1ce01a201780150012a010600e400c400a6008a007000580042002e001c000c0000 (i%16)
private def maskTable₂p45 (i:ℕ) : ℕ := packedAt 0x8000000000000000030d80000000000000000c360000000000000000c3600000000000000030d80000000000000030d800000000000000c3600000000000000c36000000000000030d800000000000030d8000000000000c36000000000000c360000000000030d8000000000030d80000000000c360000000000c360000000030d 0x40c03bc036e032202d80290024a020601c401840146010a00d000980062002e0000 (i%16)
private def maskTable₂p46 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000000030d800000000000000000000000000030d8000000000000000000000000000c36000000000000000000000000000c360000000000000000000000000030d80000000000000000000000000c360000000000000000000000000c3600000000000000000000000030d80000000000000000000000030d8000000000000000000000030d80000000000000000000000c360000000000000000000000c3600000000000000000000030d80000000000000000000030d800000000000000000000c360000000000000000030d 0x6c2064405c8054e04d6046003ee037e031002a4023c01d60172011000b000520000 (i%16)
private def maskTable₂p47 (i:ℕ) : ℕ := packedAt 0x830f8c3e0000000000000000000000000000000000000c3600000000000000000000000000000000000030d80000000000000000000000000000000000030d800000000000000000000000000000000000c3600000000000000000000000000000000000c36000000000000000000000000000000000030d800000000000000000000000000000000030d8000000000000000000000000000000000c36000000000000000000000000000000000c360000000000000000000000000000000030d8000000000000000000000000000000030d80000000000000000000000000000000c3600000000000000000000000000000030d80000000000000000000000000000030d 0x82408140806076606c8062c059204fa046403d0033e02ae02200194010a00840000 (i%16)
private def maskTable₂p48 (i:ℕ) : ℕ := packedAt 0x8000000000030f80000000000c3e0000000000c3e00000000030f800000030f8000000c3e000000c3e0000030f8000030f80000c3e0000c3e00030f80030f800c3e00c3e030f 0x23001f801c2018e015c0134010e00ea00c800a8008a006e0054003c002600120000 (i%16)
private def maskTable₂p49 (i:ℕ) : ℕ := packedAt 0x80000000000000000000000c3e0000000000000000000000c3e00000000000000000000030f80000000000000000000030f800000000000000000000c3e00000000000000000000c3e0000000000000000c3e00000000000000030f80000000000000030f800000000000000c3e00000000000000c3e000000000000030f800000000000030f8000000000000c3e000000000000c3e0000000000030f 0x4e4047e041a03b8035802fa029e0252020801c0017a013600f400b40076003a0000 (i%16)
private def maskTable₂p50 (i:ℕ) : ℕ := packedAt 0x20000000000000000000000000000000000c3e00000000000000000000000000000000030f80000000000000000000000000000000030f800000000000000000000000000000000c3e00000000000000000000000000000000c3e000000000000000000000000000000c3e0000000000000000000000000000030f800000000000000000000000000030f8000000000000000000000000000c3e000000000000000000000000000c3e0000000000000000000000000030f8000000000000000000000000030f800000000000000000000000030f8000000000000000000000000c3e000000000000000000000000c3e0000000000000000000000030f 0x7e2074e06bc062c059e0512048e040c03900316029e022801b4014400d6006a0000 (i%16)
private def maskTable₂p51 (i:ℕ) : ℕ := packedAt 0x20000000c4e000000313800000313800000c4e00000c4e0000313800031380000000000000000000000000000031180000000000000000000000000000311800000000000000000000000000311800000000000000000000000000c46000000000000003118000000000000031180000000000000c460003118000000000000000000000000000000000030f 0x45e0436041003ec03ca03aa038c037002ec026c01f4017e013800f400b200980000 (i%16)
private def maskTable₂p52 (i:ℕ) : ℕ := packedAt 0x8000000000000000000000000000000000000031380000000000000000000000000000000000000c4e0000000000000000000000000000000000000c4e000000000000000000000000000000000000c4e000000000000000000000000000000000003138000000000000000000000000000000000031380000000000000000000000000000000000c4e0000000000000000000000000000000000c4e000000000000000003138000000000000000031380000000000000000c4e0000000000000000c4e000000000000000313800000000000000313800000000000000c4e0000000313 0x71c067805d60536049a0400036802d2023e01ec019c014e010200b80070002a0000 (i%16)
private def maskTable₂p53 (i:ℕ) : ℕ := packedAt 0x2000000000000000031580000000000000003158000000000000000c56000000000000000c56000000000000003158000000000000031580000000c560000000c56000000315800000315800000c5600000c56000031580003158000c5600000000000000000000000000000000000000313 0x38e034002f402aa0262021c01d801ae01860160013c011a00fa00dc00c000a60000 (i%16)
private def maskTable₂p54 (i:ℕ) : ℕ := packedAt 0x80003178000c5e000c5e0000000000000000000000000000000000000000c560000000000000000000000000000000000000003158000000000000000000000000000000000000031580000000000000000000000000000000000000c560000000000000000000000000000000000000c56000000000000000000000000000000000000315800000000000000000000000000000000000c5600000000000000000000000000000000000c56000000000000000000000000000000000031580000000000000000000000000000000003158000000000000000000000000000000000c560000000000000000031580000000000000000315 0x7b8079c0782076a06be0614057004ce042e039002f6025e01c8013400a200500000 (i%16)
private def maskTable₂p55 (i:ℕ) : ℕ := packedAt 0x8000000000000000000000000000000000c5e000000000000000000000000000000000c5e00000000000000000c5e000000000000000031780000000000000003178000000000000000c5e000000000000000c5e000000000000003178000000000000031780000000000000c5e0000000c5e000000317800000317800000c5e00000c5e0000317 0x43c03aa031a02ca027c023001e6019e0158011400d200aa00840060003e001e0000 (i%16)
private def maskTable₂p56 (i:ℕ) : ℕ := packedAt 0x8000031980000c660000c66000319800319800c6603198000000000000000000000000000000000000000c5e000000000000000000000000000000000000000c5e000000000000000000000000000000000000031780000000000000000000000000000000000003178000000000000000000000000000000000000c5e000000000000000000000000000000000000c5e00000000000000000000000000000000000c5e00000000000000000000000000000000003178000000000000000000000000000000000317 0x6440624060605ea05d005b805a2059004e6043e039c02fc025e01c2012a00940000 (i%16)
private def maskTable₂p57 (i:ℕ) : ℕ := packedAt 0x20000000000000000000000000000c6600000000000000000000000000031980000000000000000c660000000000000000c66000000000000000319800000000000000319800000000000000c6600000000000000c66000000000000031980000000000003198000000000000c66000000000000c66000000000003198000000c66000000c6600000319 0x44e03d20358030a02be0274022c01e601a20160012000e200a6006c004600220000 (i%16)
private def maskTable₂p58 (i:ℕ) : ℕ := packedAt 0x800c6e00c6e0c6e000000000000000000000000000000000000000c660000000000000000000000000000000000000031980000000000000000000000000000000000003198000000000000000000000000000000000000c66000000000000000000000000000000000000c660000000000000000000000000000000000031980000000000000000000000000000000000c660000000000000000000000000000000000c66000000000000000000000000000000000319800000000000000000000000000000000319800000000000000000000000000000000c66000000000000000000000000000000319800000000000000000000000000000319 0x7e007ca07b607a606fe065805b8051a047e03e4034e02ba02280198010a00840000 (i%16)
private def maskTable₂p59 (i:ℕ) : ℕ := packedAt 0x2000000000000000c6e0000000000000031b8000000000000031b80000000000000c6e0000000000000c6e00000000000031b80000000000031b800000000000c6e00000000000c6e000000c6e0000031b8000031b80000c6e0000c6e00031b80031b 0x31202ca0284024001fe01be01800144010a00d200ae008c006c004e003200180000 (i%16)
private def maskTable₂p60 (i:ℕ) : ℕ := packedAt 0x200000000000000000000000000000000000000c6e00000000000000000000000000000000000031b80000000000000000000000000000000000031b800000000000000000000000000000000000c6e00000000000000000000000000000000000c6e0000000000000000000000000000000000c6e00000000000000000000000000000000031b80000000000000000000000000000000031b800000000000000000000000000000000c6e00000000000000000000000000000000c6e000000000000000000000000000000c6e0000000000000000000000000000031b8000000000000000000000000000c6e000000000000000000000000000c6e0000000000000000c6e00000000000000031b 0x86e07ca072c069005f6055e04ca043803a8031a028e020a0188010e0096004a0000 (i%16)
private def maskTable₂p61 (i:ℕ) : ℕ := packedAt 0x8000000000000c76000000000000c760000000000031d8000000000031d80000000000c760000031d8000031d80000c760000c7600031d80031d800c7600c76031d8c760000000000000000000000000000000000000031b 0x2c002820246020c01d4019e017c015c013e0122010800f000da00c600b400a60000 (i%16)
private def maskTable₂p62 (i:ℕ) : ℕ := packedAt 0x80000000000000000000000000000000031d800000000000000000000000000000000c7600000000000000000000000000000000c76000000000000000000000000000000031d8000000000000000000000000000000c76000000000000000000000000000000c760000000000000000000000000000031d8000000000000000000000000000031d80000000000000000000000000031d800000000000000000000000000c7600000000000000031d80000000000000031d800000000000000c7600000000000000c76000000000000031d800000000000031d 0x6cc063c05ae052204980412038e030c028c0214019e0154010c00c6008200400000 (i%16)
private def maskTable₂p63 (i:ℕ) : ℕ := packedAt 0x8000000000031f80000c7e0000c7e00031f80031f800c7e00c7e031f831f8000000000000000000000000000000000000031d80000000000000000000000000000000000000c76000000000000000000000000000000000000c760000000000000000000000000000000000031d8000000000000000000000000000000000031d80000000000000000000000000000000000c7600000000000000000000000000000000031d 0x52c04f404d604ba04a004880472045e044c043c039802f6025a01c0012800920000 (i%16)
private def maskTable₂p64 (i:ℕ) : ℕ := packedAt 0x80000000000000000000000000000000000c7e0000000000000000000000000000000000c7e000000000000000000000000000000000c7e0000000000000000000000000000000031f8000000000000000000000000000000031f80000000000000000000000000000000c7e0000000000000000000000000000000c7e000000000000000000000000000000c7e0000000000000000000000000000031f800000000000000c7e00000000000000c7e000000000000031f800000000000031f8000000000000c7e000000000000c7e0000000000031f 0x6ac0616058204f2046403d8034e02c6024201c0017a013600f400b40076003a0000 (i%16)
private def maskTable₂p65 (i:ℕ) : ℕ := packedAt 0x800000000321800000000c8600000000c86000000032180000c860000c86000321800321800c8600c86032183218c86c860000000000000000000000000000000000031f8000000000000000000000000000000000031f 0x2b80288025a022e020401e601ca01b001980182016e015c014c013e013200980000 (i%16)
private def maskTable₂p66 (i:ℕ) : ℕ := packedAt 0x200000000000000000000000000c860000000000000000000000000c860000000000000000000032180000000000000000000321800000000000000321800000000000000c8600000000000000c86000000000000032180000000000003218000000000000c86000000000000c86000000000003218000000000032180000000000c860000000000c86000000000321 0x47a04060396033802dc0294024e020a01c80188014a010e00d4009c006600320000 (i%16)
private def maskTable₂p67 (i:ℕ) : ℕ := packedAt 0x20000000000000000000000000000000000000c86000000000000000000000000000000000000321800000000000000000000000000000000000c8600000000000000000000000000000000000c86000000000000000000000000000000000032180000000000000000000000000000000003218000000000000000000000000000000000c86000000000000000000000000000000003218000000000000000000000000000000032180000000000000000000000000000000c860000000000000000000000000000000c86000000000000000000000000000000321800000000000000000000000000000c8600000000000000000000000000000c8600000000000000000000000000003218000000000000000000000000000321 0x8da083a079c0702066a05d4054004ae04200394030a028201fc017a00fa007c0000 (i%16)
private def maskTable₂p68 (i:ℕ) : ℕ := packedAt 0x2000000000000c8e000000000003238000000000032380000000000c8e0000000000c8e00000000032380000000032380003238000c8e000c8e003238032380c8e0c8e323b23 0x22e01f201b80180014a011600e400b40098007e00660050003c002a001a000c0000 (i%16)
private def maskTable₂p69 (i:ℕ) : ℕ := packedAt 0x80000000000000000000000000000000003238000000000000000000000000000000000c8e000000000000000000000000000000000c8e000000000000000000000000000000032380000000000000000000000000000003238000000000000000000000000000000c8e000000000000000000000000000000c8e00000000000000000000000000000c8e00000000000000000000000000003238000000000000000000000000000c8e000000000000000000000000000c8e000000000000000000000000003238000000000000000000000000032380000000000000c8e0000000000000c8e000000000000323 0x76c06d8064605b6052c04a4041e039a031a029c022201aa013400c0007e003e0000 (i%16)
private def maskTable₂p70 (i:ℕ) : ℕ := packedAt 0x800000000c9600000000c96000003258000032580000c960000c96000325800325800c9600c96032583258c96c9600000000000000000000000000000000000c8e0000000000000000000000000000000000323 0x29c026e02420220020001e201c601ac0194017e016a01580148013a012e00960000 (i%16)
private def maskTable₂p71 (i:ℕ) : ℕ := packedAt 0x80000000000000000000000003258000000000000000000000000c96000000000000000000000000c9600000000000000000000000325800000000000000325800000000000000c96000000000000032580000000000003258000000000000c96000000000000c96000000000003258000000000032580000000000c960000000000c96000000000325800000000325 0x47c040c039e033202c80280023a01f801b8017a013e010400cc0096006200300000 (i%16)
private def maskTable₂p72 (i:ℕ) : ℕ := packedAt 0x80000000000000000000000000000000003258000000000000000000000000000000000c96000000000000000000000000000000000c96000000000000000000000000000000003258000000000000000000000000000000032580000000000000000000000000000000c960000000000000000000000000000000c96000000000000000000000000000000325800000000000000000000000000000325800000000000000000000000000000c9600000000000000000000000000000c96000000000000000000000000000032580000000000000000000000000003258000000000000000000000000000c96000000000000000000000000000c9600000000000000000000000000325 0x85007bc072a069a060c058004f6046e03e8036402e2026201e4016800ee00760000 (i%16)
private def maskTable₂p73 (i:ℕ) : ℕ := packedAt 0x8000000c9e000000c9e00000c9e000032780003278000c9e000c9e003278032780c9e0c9e327b27800000000000000000000000000000000000325800000000000000000000000000000000000c960000000000000000000000000000000000325 0x30802e202be029e02800264024a0232021c020801f601e601d801cc013000960000 (i%16)
private def maskTable₂p74 (i:ℕ) : ℕ := packedAt 0x800000000000000000327800000000000000000c9e00000000000000327800000000000003278000000000000c9e000000000000c9e000000000003278000000000032780000000000c9e0000000000c9e000000000327800000000327800000000c9e00000000c9e00000003278000000327 0x394034002ee02a80264022601ea01b001780142010e00dc00ac007e005200280000 (i%16)
private def maskTable₂p75 (i:ℕ) : ℕ := packedAt 0x200000000000000000000000000000000c9e0000000000000000000000000000000c9e000000000000000000000000000000327800000000000000000000000000000c9e00000000000000000000000000000c9e000000000000000000000000000032780000000000000000000000000003278000000000000000000000032780000000000000000000000c9e0000000000000000000000c9e000000000000000000000327800000000000000000000327800000000000000000000c9e00000000000000000000c9e0000000000000000000c9e000000000000000000327 0x6f2066605de055804d6045603d8035c02f4028e022a01c80168010a00ae00560000 (i%16)
private def maskTable₂p76 (i:ℕ) : ℕ := packedAt 0x2000000ca6000003298000032980000ca60000ca60003298003298032980ca60ca6329b2980000000000000000000000000000000003278000000000000000000000000000000000c9e000000000000000000000000000000000c9e00000000000000000000000000000000327 0x36603420320030002e202c602ac02940280026e025e0250024401b0011e008e0000 (i%16)
private def maskTable₂p77 (i:ℕ) : ℕ := packedAt 0x2000000000000000329800000000000000329800000000000000ca600000000000000ca60000000000000329800000000000ca600000000000ca6000000000032980000000003298000000000ca6000000000ca6000000003298000000032980000000ca60000000ca6000000329 0x36e032402dc02960252021001d6019e01680134010200d200a40078004e00260000 (i%16)
private def maskTable₂p78 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000000ca6000000000000000000000000003298000000000000000000000000032980000000000000000000000000ca60000000000000000000000000ca60000000000000000000000003298000000000000000000000329800000000000000000000329800000000000000000000ca600000000000000000000ca600000000000000000003298000000000000000000ca6000000000000000000ca600000000000000000329800000000000000003298000000000000000329 0x62205aa053404c0044e03de0370030c02ac024e01f20198014200ee009c004c0000 (i%16)
private def maskTable₂p79 (i:ℕ) : ℕ := packedAt 0x80032b800cae00cae032b832b8caecae000000000000000000000000000000032980000000000000000000000000000003298000000000000000000000000000000ca6000000000000000000000000000000ca6000000000000000000000000000003298000000000000000000000000000032980000000000000000000000000000ca60000000000000000000000000000ca6000000000000000000000000000329 0x51004f804e204ce04bc04ac049e04920408038002fa027601f4017400f6007a0000 (i%16)
private def maskTable₂p80 (i:ℕ) : ℕ := packedAt 0x80000000000032b800000000000cae00000000000cae000000000032b800000000032b8000000000cae000000000cae0000000032b8000000032b80000000cae0000000cae00000032b80000032b800000cae0000cae00032b 0x2c8028c0252021a01e401b0017e014e012000f400ca00a2007c00580036001a0000 (i%16)
private def maskTable₂p81 (i:ℕ) : ℕ := packedAt 0xb2d8000000000000000000000000000000000cae000000000000000000000000000000000cae0000000000000000000000000000000cae000000000000000000000000000000cae0000000000000000000000000000032b8000000000000000000000000000032b80000000000000000000000000000cae0000000000000000000000000000cae00000000000000000000000000032b80000000000000000000000000032b8000000000000000000032b80000000000000000000cae0000000000000000000cae000000000000032b800000000000032b 0x6b806ac061a058a0502047e03fc037c02fe028202080190013400da008200400000 (i%16)
private def maskTable₂p82 (i:ℕ) : ℕ := packedAt 0x8000000032d80000000cb60000000cb600000032d80000032d800000cb600000cb6000032d800032d8000cb6000cb60032d8032d80cb60cb632d 0x1d001a4017a0152012c010800e600c600a8008c0072005a00440030001e000e0000 (i%16)
private def maskTable₂p83 (i:ℕ) : ℕ := packedAt 0x8000000000000000032d80000000000000000cb60000000000000000cb6000000000000000cb60000000000000032d8000000000000032d80000000000000cb60000000000000cb600000000000032d800000000000cb600000000000cb6000000000032d800000000032d8000000000cb6000000000cb60000000032d 0x3e80398034a02fe02b60270022c01ea01aa016c013200fa00c40090005e002e0000 (i%16)
private def maskTable₂p84 (i:ℕ) : ℕ := packedAt 0x8000000000000000000000000000cb6000000000000000000000000000cb60000000000000000000000000032d80000000000000000000000000cb60000000000000000000000000cb600000000000000000000000032d80000000000000000000000032d800000000000000000000000cb6000000000000000000000032d800000000000000000000032d800000000000000000000cb600000000000000000000cb6000000000000000000032d800000000000000000032d8000000000000000000cb60000000000000000032d 0x66c05f2057a05040492042203b4034802de0278021401b6015a010000a800520000 (i%16)
private def maskTable₂p85 (i:ℕ) : ℕ := packedAt 0x8000032f80000cbe0000cbe00032f80032f800cbe00cbe032f80000000000000000000000000000000032d800000000000000000000000000000000cb60000000000000000000000000000000cb600000000000000000000000000000032d80000000000000000000000000000032d800000000000000000000000000000cb600000000000000000000000000000cb6000000000000000000000000000032d 0x4f804d804ba049e0484046c04560442043003a00312028a0204018000fe007e0000 (i%16)
private def maskTable₂p86 (i:ℕ) : ℕ := packedAt 0x8000000000000000032f80000000000000000cbe0000000000000000cbe00000000000000032f800000000000000cbe00000000000000cbe000000000000032f800000000000032f8000000000000cbe000000000000cbe00000000cbe000000032f800000032f8000000cbe000000cbe0000032f 0x3a40354030602ba0270022a01e601a40164012600ea00be0094006c004600220000 (i%16)
private def maskTable₂p87 (i:ℕ) : ℕ := packedAt 0x800cc600cc60331833180000000000000000000000000cbe0000000000000000000000000cbe00000000000000000000000032f80000000000000000000000032f800000000000000000000000cbe0000000000000000000000cbe00000000000000000000032f8000000000000000000032f80000000000000000000cbe0000000000000000000cbe00000000000000000032f80000000000000000032f 0x4f004da04c604b404a4043203c2035402e8027e021a01b8015c010200aa00540000 (i%16)
private def maskTable₂p88 (i:ℕ) : ℕ := packedAt 0x8000000000000033180000000000000cc60000000000000cc6000000000000331800000000000331800000000000cc6000000033180000003318000000cc6000000cc6000003318000033180000cc60000cc6000331800331 0x2c40280023e01fe01c00184014a012000f800d200ae008c006c004e003200180000 (i%16)
private def maskTable₂p89 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000033180000000000000000000000003318000000000000000000000000cc6000000000000000000000000cc6000000000000000000000003318000000000000000000000cc6000000000000000000000cc6000000000000000000033180000000000000000003318000000000000000000cc6000000000000000000cc60000000000000000033180000000000000000cc60000000000000000cc6000000000000000331800000000000000331 0x5c2055004e004720406039c033a02da0280022801d2017e012c00de009200480000 (i%16)
private def maskTable₂p90 (i:ℕ) : ℕ := packedAt 0x8000000000033380000003338000000cce000000cce000003338000033380000cce0000cce000333800333800cce00cce033383338cce00000000000000000000000000331 0x22801f001c801a2017e015c013c011e010200e800d000ba00a60094008400760000 (i%16)
private def maskTable₂p91 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000333800000000000000000000000cce00000000000000000000000cce000000000000000000003338000000000000000000cce000000000000000000cce00000000000000000cce0000000000000000cce000000000000000333800000000000000333800000000000000cce000000000000033380000000000003338000000000000cce000000000000cce00000000000333 0x4f20484041a03b2035402fe02aa025a020e01c4017c013600f400b40076003a0000 (i%16)
private def maskTable₂p92 (i:ℕ) : ℕ := packedAt 0x2000000000000335800000000000335800000000000cd6000000335800000335800000cd600000cd6000033580003358000cd6000cd6003358033580cd60cd6335 0x20601c8018c0152012c010800e600c600a8008c0072005a00440030001e000e0000 (i%16)
private def maskTable₂p93 (i:ℕ) : ℕ := packedAt 0x2000000cde000003378000000000000000000000000000cd6000000000000000000000000000cd600000000000000000000000000335800000000000000000000000003358000000000000000000000033580000000000000000000000cd600000000000000000000cd6000000000000000000cd6000000000000000003358000000000000000cd6000000000000000cd600000000000000335800000000000003358000000000000335 0x54e052a0508048e041603a0032c02c4025e020201ae015c011200ca008400400000 (i%16)
private def maskTable₂p94 (i:ℕ) : ℕ := packedAt 0x800000ce600000ce6000000000000000000000000000003378000000000000000000000000000033780000000000000000000000000000cde0000000000000000000000000000cde000000000000000000000000000cde000000000000000000000000003378000000000000000000000000033780000000000000000000000000cde0000000000000000000000000cde000000003378000000033780000000cde0000000cde000000337 0x554053205120490041003920316029e022801b4014200d200a40078004e00260000 (i%16)
private def maskTable₂p95 (i:ℕ) : ℕ := packedAt 0x20000000000000000000000000000003398000000000000000000000000000033980000000000000000000000000000ce60000000000000000000000000000ce6000000000000000000000000000339800000000000000000000000000ce600000000000000000000000000ce6000000000000000000000000033980000000000000000000000003398000000000000000000000000ce6000000003398000000033980000000ce60000000ce6000000339800000339 0x5aa052404a4042603aa033002ba024601d4016400f600c8009c0072004a00240000 (i%16)
private def maskTable₂p96 (i:ℕ) : ℕ := packedAt 0x200000000000000000000000000033b80000000000000000000000000033b8000000000000000000000000033b80000000000000000000000000cee0000000000000000000000000cee00000000000000000000000033b80000000000000000000000033b8000000033b80000000cee0000000cee00000033b80000033b800000cee00000cee000033b8000000000000000000000000000000339 0x4d2045803e0036c02fa028a021c01b00184015a0132010c00e800c600a600880000 (i%16)
private def maskTable₂p97 (i:ℕ) : ℕ := packedAt 0x800000000000000000000000033d8000000000000000000000000cf6000000000000000000000000cf60000000000000000000000033d80000000cf60000000cf600000033d80000033d800000cf600000cf6000033d800033d8000000000000000000000000000000cee000000000000000000000000000000cee000000000000000000000000000033b800000000000000000000000000033b 0x4d0046003f20386031c02f202ca02a40280025e023e02200204017e00fa007c0000 (i%16)
private def maskTable₂p98 (i:ℕ) : ℕ := packedAt 0x8000000000000000000000033f800000033f8000000cfe000000cfe0000033f8000033f80000cfe0000cfe00033f80000000000000000000000000000033d800000000000000000000000000000cf60000000000000000000000000000cf600000000000000000000000000033d80000000000000000000000000033d800000000000000000000000000cf6000000000000000000000000033d 0x4cc0464043c041603f203d003b003920376035c02d8025601da016000e800720000 (i%16)
private def maskTable₂p99 (i:ℕ) : ℕ := packedAt 0x2000003418000034180000d060000d06000341800341800d0600d060341800000000000000000000000000000cfe00000000000000000000000000000cfe00000000000000000000000000033f80000000000000000000000000033f8000000000000000000000000cfe000000000000000000000000cfe0000000000000000000000033f 0x422040003e003c203a6038c0374035e034a033802b6023601bc014400d6006a0000 (i%16)
private def maskTable₂p100 (i:ℕ) : ℕ := packedAt 0x80d0e0d0e00000000000000000000000000000d060000000000000000000000000000341800000000000000000000000000341800000000000000000000000000d06000000000000000000000000d06000000000000000000000003418000000000000000000000034180000000000000000000000d060000000000000000000034180000000000000000000341800000000000000000341800000000000000000d06000000341800000341 0x55c054a053a04ba043c03c4034e02e20278021001aa014c00f0009c004a00240000 (i%16)
private def maskTable₂p101 (i:ℕ) : ℕ := packedAt 0x20000000000000000000000d0e000000000000000000000d0e000000000000000000003438000000000000000000034380000000000000000000d0e0000000000000000034380000000000000000343800000343800000d0e00000d0e000034380003438000d0e000d0e0034380343 0x376031202b2025401f8019e014c00fc00d800b600960078005c0042002a00140000 (i%16)
private def maskTable₂p102 (i:ℕ) : ℕ := packedAt 0x2000345800345800d1600d16034583458d1600000000000000000000000000003438000000000000000000000000000343800000000000000000000000000d0e00000000000000000000000000d0e00000000000000000000000003438000000000000000000000000343800000000000000000000000d0e00000000000000000000000d0e0000000000000000000000343 0x48a047004580442042e041c040c03fe03800304028e021a01a8013800ce00660000 (i%16)
private def maskTable₂p103 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000345800000000000000000000000d1600000000000000000000000d16000000000000000000000034580000000000000000000003458000000000000000000000d16000000000000000000003458000000000000000000034580000000000000000000d160000000000000000000d1600000000000000000d160000000000000000345800000d1600000d1600003458000345 0x4f20484041a03b2034c02e80286022801cc0172011a00ca007c005a003a001c0000 (i%16)
private def maskTable₂p104 (i:ℕ) : ℕ := packedAt 0x200000d1e000034780003478000d1e000d1e003478034780d1e0d1e347b4780000000000000000000000000003458000000000000000000000000000d1600000000000000000000000000d1600000000000000000000000003458000000000000000000000000345 0x33e031e030002e402ca02b2029c0288027602660258024c01d0015600e200700000 (i%16)
private def maskTable₂p105 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000000d1e000000000000000000000000034780000000000000000000000003478000000000000000000000000d1e000000000000000000000000d1e00000000000000000000000d1e000000000000000000000034780000000000000000000003478000000000000000000000d1e000000000000000000000d1e00000000000000000000d1e000000000000000000034780000000000000000003478000000000000000000d1e00000000000000003478000000000000000347 0x62605ae053c04cc045e03f2038a032402c0025e01fe01a2014800f0009a004c0000 (i%16)
private def maskTable₂p106 (i:ℕ) : ℕ := packedAt 0x80000000000000000000d260000000000000000000d26000000000034980000000003498000000003498000034980000d260000d26000349800349800d2600d26034983498d26000000000000000000000000000347 0x2ac025201fa01c40190016001400122010600ec00d400be00aa00980088007a0000 (i%16)
private def maskTable₂p107 (i:ℕ) : ℕ := packedAt 0x8034b80d2e0d2e34bb4b800000000000000000000000000349800000000000000000000000000d260000000000000000000000000d26000000000000000000000000349800000000000000000000000349800000000000000000000000d26000000000000000000000034980000000000000000000003498000000000000000000000d26000000000000000000000d2600000000000000000000349 0x4dc04c804b604a60498048c0414039e032e02c0025401ea0184012000be005e0000 (i%16)
private def maskTable₂p108 (i:ℕ) : ℕ := packedAt 0x20000000000000000000000034b8000000000000000000000034b800000000000000000000034b8000000000000000000000d2e000000000000000000000d2e0000000000000000000034b8000000000000000000034b800000000000000000034b8000000000000000000d2e0000000000d2e00000000034b800000000d2e000034b8000d2e000d2e0034b 0x45a03f00388032402c20262020401a8015000fa00c6009400660048002e00160000 (i%16)
private def maskTable₂p109 (i:ℕ) : ℕ := packedAt 0x2000000000034d8000000000d36000000000d3600000000d360000d3600034d80034d800d3600d36034d834d8d36d360000000000000000000000000d2e00000000000000000000000034b80000000000000000000000034b 0x2c2028c025a022a01fe01e201c801b0019a0186017401640156014a00da006c0000 (i%16)
private def maskTable₂p110 (i:ℕ) : ℕ := packedAt 0x2034f834f8d3e00000000000000000000000000d36000000000000000000000000034d8000000000000000000000000d36000000000000000000000000d360000000000000000000000034d8000000000000000000000034d80000000000000000000000d36000000000000000000000d360000000000000000000034d8000000000000000000034d80000000000000000000d360000000000034d8000000000034d 0x50e04fc04ec04de046a03f8038a031e02b4024c01e60186012800cc007200380000 (i%16)
private def maskTable₂p111 (i:ℕ) : ℕ := packedAt 0x800000000000d3e00000000000d3e000000000034f800000000034f80000000034f800000000d3e00000000d3e000000034f8000000d3e000000d3e0000034f8000034f80000d3e0000d3e0034f8034f 0x2800246020e01d801a401740146011a00f000ca00a6008400640046002a00140000 (i%16)
private def maskTable₂p112 (i:ℕ) : ℕ := packedAt 0x2000035180003518000d4600d46035183518d46d46000000000000000000000000d3e0000000000000000000000034f8000000000000000000000034f80000000000000000000000d3e0000000000000000000000d3e00000000000000d3e000000000000034f80000000000034f 0x36e03500334031a030602f402e402d602ca025e01f4018c012600c2007e003c0000 (i%16)
private def maskTable₂p113 (i:ℕ) : ℕ := packedAt 0x8000000000000000000000d46000000000000000d460000000000000035180000000000000d460000000000000d46000000000003518000000000035180000000000d460000000000d46000000003518000000035180000000d460000000d46000000d460000035180000351 0x36002fe02b60270022e01ee01b4017c0146011200e400b8008e0066004200200000 (i%16)
private def maskTable₂p114 (i:ℕ) : ℕ := packedAt 0x8000000000d4e000000000d4e00000000d4e000000035380000003538000000d4e000003538000035380000d4e0000d4e000353800353800000000000000000000000d4600000000000000000000000d4600000000000000000000003518000000000000000000000351 0x350031e02ee02c202980270024a0228020801ea01ce01b4019c013200ca00640000 (i%16)
private def maskTable₂p115 (i:ℕ) : ℕ := packedAt 0x8000035580000d560000d56000355800355800d56000000000000000035380000000000000003538000000000000000d4e000000000000000d4e0000000000000035380000000000003538000000000000d4e00000000000d4e00000000003538000000000353 0x334031402f602da02c002a80292024401f801ae0166012000e000a2006a00340000 (i%16)
private def maskTable₂p116 (i:ℕ) : ℕ := packedAt 0x800d5e00d5e0000000000000000d56000000000000000d56000000000000003558000000000000d56000000000000d56000000000035580000000003558000000000d56000000000d560000000035580000000d560000000d56000000355800000355 0x31402fe02ea029e0256021001d201960160012c00fa00ca009c0072004a00240000 (i%16)
private def maskTable₂p117 (i:ℕ) : ℕ := packedAt 0x2000000000000000d5e000000000000003578000000000000035780000000003578000000000d5e000000000d5e000000003578000000035780000003578000000d5e000000d5e0000035780000d5e0000d5e000357800357 0x2c2027a023401f001bc018a015a012c010000d800b2008e006c004e003200180000 (i%16)
private def maskTable₂p118 (i:ℕ) : ℕ := packedAt 0x800000000359800000000d6600000003598000000d66000000d66000003598000035980003598000d66000d66003598035980d6600000000000000000d5e0000000000000000d5e000000000000000357 0x2840254022601fc01d601b2019001700154013a0122010c00f800e60096004a0000 (i%16)
private def maskTable₂p119 (i:ℕ) : ℕ := packedAt 0x20000000d6e000000d6e0000035b8000035b80000d6e00035b80035b800d6e00d6e035b835b800000000000000359800000000000000d6600000000000000d6600000000000003598000000000000359 0x27e02560232021001f001d201b801a0018a017601640154010c00c6008200400000 (i%16)
private def maskTable₂p120 (i:ℕ) : ℕ := packedAt 0x20000035d8000035d80000d760000d76000d760035d8035d80d760000000000000000d6e000000000000000d6e0000000000000035b8000000000000035b80000000000000d6e0000000000000d6e0000000035b8000000035b 0x2ca02a80288026a024e02360220020c01fa01ae0166012000dc009a005a002c0000 (i%16)
private def maskTable₂p121 (i:ℕ) : ℕ := packedAt 0x8000000000000000000d86000000000000000000d860000000000000000036180000000000000000d860000000000000000d86000000000000000361800000000000000361800000000000000d86000000000035f8000000000d7e000000035f800000035f80000000000000d760000000000000d7600000000d76000000035d 0x40003aa0356030402b6026a022001d80192015c012a010000d800960056002a0000 (i%16)
private def maskTable₂p122 (i:ℕ) : ℕ := packedAt 0x2000000000000000000d9600000000000000000365800000000000000365800000000000000d9600000000000000d9600000000000003658000000000000000000d8e000000000000000000d8e000000000000000003638000000000000000036380000000000000003638000000000000000d8e000000000000000d8e00000000000000363800000000000003638000000000000000000361 0x4c60472042003d80392034e030c02b60262021001c00174012a00e2009c00580000 (i%16)
private def maskTable₂p123 (i:ℕ) : ℕ := packedAt 0x8000000000000000036980000000000000000da600000000000000da6000000000000036980000000000003698000000000000da600000000000000000003678000000000000000000367800000000000000000d9e00000000000000000d9e000000000000003678000000000000036780000000000000d9e0000000000000d9e00000000000000000000d960000000000000000000365 0x4b80468041a03d603940354031602bc0264021201c2017c013800f600b6005a0000 (i%16)
private def maskTable₂p124 (i:ℕ) : ℕ := packedAt 0x800000000000dbe00000000000dbe000000000dbe0000000036f8000000dbe000000dbe00000000000000000036b80000000000000000036b80000000000000000dae0000000000000000dae000000000000036b800000000000036b8000000000000dae000000000000dae0000000000000000000da6000000000000000000369 0x40803ce039603660338031202ee0298024401f601aa0168012800ea00ae00560000 (i%16)
private def maskTable₂p125 (i:ℕ) : ℕ := packedAt 0x20000000000000000371800000000000000371800000000000000dc6000000000000dc6000000000003718000000000037180000000000dc60000000037180000000371800000dc60000000000000000036f8000000000000000036f8000000000000000dbe000000000000000dbe00000000000036f80000000000036f 0x3ea039c0354030e02d202980260022a01fc01d001ae015c010c00c2007a003c0000 (i%16)
private def maskTable₂p126 (i:ℕ) : ℕ := packedAt 0x20000000dd600000dd6000037580000000000000000dce0000000000000000dce0000000000000037380000000000000373800000000000dce00000000000dce000000000037380000000003738000000037380000000dce000003738000037380000000000000000371 0x34e0326030602e8029a024e020801c4018a0152011c00e800bc0092007000500000 (i%16)
private def maskTable₂p127 (i:ℕ) : ℕ := packedAt 0x200000037b80000000000003798000000000000de6000000000000de60000000000037980000000de60000000de60000000000000000dd60000000000000003758000000000000037580000000000000dd600000000000dd6000000000037580000000003758000000000dd60000000375 0x3860360032002e202a6026c0242021a01ce0184014000fe00c60090005c002a0000 (i%16)
private def maskTable₂p128 (i:ℕ) : ℕ := packedAt 0x80000000000000df6000000000000df60000000000037d8000000000037d80000000000df6000000000df60000000037d8000000037d80000000df600000037d80000037d800000000037b8000000000dee000000000dee0000000037b800000037b 0x31002ce02920258022001ea01ba018c01600136011000ec00b80086005600280000 (i%16)
private def maskTable₂p129 (i:ℕ) : ℕ := packedAt 0x200000e1e000000003818000000038180000000e060000000e0600000038180000000000000dfe0000000000000dfe0000000000037f8000000000037f80000000037f800000000dfe00000000dfe000000037f800000037f8000000000000037d 0x30602e602b8028c0262023a021401d201920158012000f000c20096006c00440000 (i%16)
private def maskTable₂p130 (i:ℕ) : ℕ := packedAt 0x800003938039380000000e460000000e46000000e4600000391800000389800000e2600000e260000389800e2600e260000000003878000000e1e000000e1e00000387 0x21801f801e401ba0192016e014c0128010600e600c800b2009e006c004600220000 (i%16)
private def maskTable₂p131 (i:ℕ) : ℕ := packedAt 0x8000039780000e5e0000e5e00000000e560000000395800000e5600000e56000039580e560e56000000003938000000039380000003938000000e4e000000e4e00000393 0x220020001e201c6019a0170014e012e011000fe00ee00c00094006c004600220000 (i%16)
private def maskTable₂p132 (i:ℕ) : ℕ := packedAt 0x800e96000e8e0003a1800e860000e7e000e7e00039d80039d800e7600e760039b80003998000e6600000397 0x15c0146012e011400fe00e200ca00b000980082006e0058003c00220000 (i%16)
def maskTable₂ (i:ℕ) : ℕ := if i<1056 then (if i<528 then (if i<256 then (if i<128 then (if i<64 then (if i<32 then (if i<16 then (maskTable₂p0 i) else (maskTable₂p1 i)) else (if i<48 then (maskTable₂p2 i) else (maskTable₂p3 i))) else (if i<96 then (if i<80 then (maskTable₂p4 i) else (maskTable₂p5 i)) else (if i<112 then (maskTable₂p6 i) else (maskTable₂p7 i)))) else (if i<192 then (if i<160 then (if i<144 then (maskTable₂p8 i) else (maskTable₂p9 i)) else (if i<176 then (maskTable₂p10 i) else (maskTable₂p11 i))) else (if i<224 then (if i<208 then (maskTable₂p12 i) else (maskTable₂p13 i)) else (if i<240 then (maskTable₂p14 i) else (maskTable₂p15 i))))) else (if i<384 then (if i<320 then (if i<288 then (if i<272 then (maskTable₂p16 i) else (maskTable₂p17 i)) else (if i<304 then (maskTable₂p18 i) else (maskTable₂p19 i))) else (if i<352 then (if i<336 then (maskTable₂p20 i) else (maskTable₂p21 i)) else (if i<368 then (maskTable₂p22 i) else (maskTable₂p23 i)))) else (if i<448 then (if i<416 then (if i<400 then (maskTable₂p24 i) else (maskTable₂p25 i)) else (if i<432 then (maskTable₂p26 i) else (maskTable₂p27 i))) else (if i<480 then (if i<464 then (maskTable₂p28 i) else (maskTable₂p29 i)) else (if i<496 then (maskTable₂p30 i) else (if i<512 then (maskTable₂p31 i) else (maskTable₂p32 i))))))) else (if i<784 then (if i<656 then (if i<592 then (if i<560 then (if i<544 then (maskTable₂p33 i) else (maskTable₂p34 i)) else (if i<576 then (maskTable₂p35 i) else (maskTable₂p36 i))) else (if i<624 then (if i<608 then (maskTable₂p37 i) else (maskTable₂p38 i)) else (if i<640 then (maskTable₂p39 i) else (maskTable₂p40 i)))) else (if i<720 then (if i<688 then (if i<672 then (maskTable₂p41 i) else (maskTable₂p42 i)) else (if i<704 then (maskTable₂p43 i) else (maskTable₂p44 i))) else (if i<752 then (if i<736 then (maskTable₂p45 i) else (maskTable₂p46 i)) else (if i<768 then (maskTable₂p47 i) else (maskTable₂p48 i))))) else (if i<912 then (if i<848 then (if i<816 then (if i<800 then (maskTable₂p49 i) else (maskTable₂p50 i)) else (if i<832 then (maskTable₂p51 i) else (maskTable₂p52 i))) else (if i<880 then (if i<864 then (maskTable₂p53 i) else (maskTable₂p54 i)) else (if i<896 then (maskTable₂p55 i) else (maskTable₂p56 i)))) else (if i<976 then (if i<944 then (if i<928 then (maskTable₂p57 i) else (maskTable₂p58 i)) else (if i<960 then (maskTable₂p59 i) else (maskTable₂p60 i))) else (if i<1008 then (if i<992 then (maskTable₂p61 i) else (maskTable₂p62 i)) else (if i<1024 then (maskTable₂p63 i) else (if i<1040 then (maskTable₂p64 i) else (maskTable₂p65 i)))))))) else (if i<1584 then (if i<1312 then (if i<1184 then (if i<1120 then (if i<1088 then (if i<1072 then (maskTable₂p66 i) else (maskTable₂p67 i)) else (if i<1104 then (maskTable₂p68 i) else (maskTable₂p69 i))) else (if i<1152 then (if i<1136 then (maskTable₂p70 i) else (maskTable₂p71 i)) else (if i<1168 then (maskTable₂p72 i) else (maskTable₂p73 i)))) else (if i<1248 then (if i<1216 then (if i<1200 then (maskTable₂p74 i) else (maskTable₂p75 i)) else (if i<1232 then (maskTable₂p76 i) else (maskTable₂p77 i))) else (if i<1280 then (if i<1264 then (maskTable₂p78 i) else (maskTable₂p79 i)) else (if i<1296 then (maskTable₂p80 i) else (maskTable₂p81 i))))) else (if i<1440 then (if i<1376 then (if i<1344 then (if i<1328 then (maskTable₂p82 i) else (maskTable₂p83 i)) else (if i<1360 then (maskTable₂p84 i) else (maskTable₂p85 i))) else (if i<1408 then (if i<1392 then (maskTable₂p86 i) else (maskTable₂p87 i)) else (if i<1424 then (maskTable₂p88 i) else (maskTable₂p89 i)))) else (if i<1504 then (if i<1472 then (if i<1456 then (maskTable₂p90 i) else (maskTable₂p91 i)) else (if i<1488 then (maskTable₂p92 i) else (maskTable₂p93 i))) else (if i<1536 then (if i<1520 then (maskTable₂p94 i) else (maskTable₂p95 i)) else (if i<1552 then (maskTable₂p96 i) else (if i<1568 then (maskTable₂p97 i) else (maskTable₂p98 i))))))) else (if i<1856 then (if i<1712 then (if i<1648 then (if i<1616 then (if i<1600 then (maskTable₂p99 i) else (maskTable₂p100 i)) else (if i<1632 then (maskTable₂p101 i) else (maskTable₂p102 i))) else (if i<1680 then (if i<1664 then (maskTable₂p103 i) else (maskTable₂p104 i)) else (if i<1696 then (maskTable₂p105 i) else (maskTable₂p106 i)))) else (if i<1776 then (if i<1744 then (if i<1728 then (maskTable₂p107 i) else (maskTable₂p108 i)) else (if i<1760 then (maskTable₂p109 i) else (maskTable₂p110 i))) else (if i<1808 then (if i<1792 then (maskTable₂p111 i) else (maskTable₂p112 i)) else (if i<1824 then (maskTable₂p113 i) else (if i<1840 then (maskTable₂p114 i) else (maskTable₂p115 i)))))) else (if i<1984 then (if i<1920 then (if i<1888 then (if i<1872 then (maskTable₂p116 i) else (maskTable₂p117 i)) else (if i<1904 then (maskTable₂p118 i) else (maskTable₂p119 i))) else (if i<1952 then (if i<1936 then (maskTable₂p120 i) else (maskTable₂p121 i)) else (if i<1968 then (maskTable₂p122 i) else (maskTable₂p123 i)))) else (if i<2048 then (if i<2016 then (if i<2000 then (maskTable₂p124 i) else (maskTable₂p125 i)) else (if i<2032 then (maskTable₂p126 i) else (maskTable₂p127 i))) else (if i<2080 then (if i<2064 then (maskTable₂p128 i) else (maskTable₂p129 i)) else (if i<2096 then (maskTable₂p130 i) else (if i<2112 then (maskTable₂p131 i) else (maskTable₂p132 i))))))))
def base₂ : List (List ℤ) := [b2_0,b2_1,b2_2,b2_3,b2_4,b2_5,b2_6,b2_7,b2_8,b2_9,b2_10,b2_11,b2_12,b2_13,b2_14,b2_15,b2_16,b2_17,b2_18,b2_19,b2_20,b2_21,b2_22,b2_23,b2_24,b2_25,b2_26,b2_27,b2_28,b2_29,b2_30,b2_31,b2_32,b2_33,b2_34,b2_35,b2_36,b2_37,b2_38,b2_39,b2_40,b2_41,b2_42,b2_43,b2_44,b2_45,b2_46,b2_47,b2_48,b2_49,b2_50,b2_51,b2_52,b2_53,b2_54,b2_55,b2_56,b2_57,b2_58,b2_59,b2_60,b2_61,b2_62,b2_63,b2_64,b2_65,b2_66].flatten
def baseTable₂ : Table := #[b2_0,b2_1,b2_2,b2_3,b2_4,b2_5,b2_6,b2_7,b2_8,b2_9,b2_10,b2_11,b2_12,b2_13,b2_14,b2_15,b2_16,b2_17,b2_18,b2_19,b2_20,b2_21,b2_22,b2_23,b2_24,b2_25,b2_26,b2_27,b2_28,b2_29,b2_30,b2_31,b2_32,b2_33,b2_34,b2_35,b2_36,b2_37,b2_38,b2_39,b2_40,b2_41,b2_42,b2_43,b2_44,b2_45,b2_46,b2_47,b2_48,b2_49,b2_50,b2_51,b2_52,b2_53,b2_54,b2_55,b2_56,b2_57,b2_58,b2_59,b2_60,b2_61,b2_62,b2_63,b2_64,b2_65,b2_66]
private def compatible := baseOk guess back baseTable₂ maskTable₂

private theorem valid2_0 : block compatible 0 32 := by decide +kernel
private theorem valid2_1 : block compatible 32 32 := by decide +kernel
private theorem valid2_2 : block compatible 64 32 := by decide +kernel
private theorem valid2_3 : block compatible 96 32 := by decide +kernel
private theorem valid2_4 : block compatible 128 32 := by decide +kernel
private theorem valid2_5 : block compatible 160 32 := by decide +kernel
private theorem valid2_6 : block compatible 192 32 := by decide +kernel
private theorem valid2_7 : block compatible 224 32 := by decide +kernel
private theorem valid2_8 : block compatible 256 32 := by decide +kernel
private theorem valid2_9 : block compatible 288 32 := by decide +kernel
private theorem valid2_10 : block compatible 320 32 := by decide +kernel
private theorem valid2_11 : block compatible 352 32 := by decide +kernel
private theorem valid2_12 : block compatible 384 32 := by decide +kernel
private theorem valid2_13 : block compatible 416 32 := by decide +kernel
private theorem valid2_14 : block compatible 448 32 := by decide +kernel
private theorem valid2_15 : block compatible 480 32 := by decide +kernel
private theorem valid2_16 : block compatible 512 32 := by decide +kernel
private theorem valid2_17 : block compatible 544 32 := by decide +kernel
private theorem valid2_18 : block compatible 576 32 := by decide +kernel
private theorem valid2_19 : block compatible 608 32 := by decide +kernel
private theorem valid2_20 : block compatible 640 32 := by decide +kernel
private theorem valid2_21 : block compatible 672 32 := by decide +kernel
private theorem valid2_22 : block compatible 704 32 := by decide +kernel
private theorem valid2_23 : block compatible 736 32 := by decide +kernel
private theorem valid2_24 : block compatible 768 32 := by decide +kernel
private theorem valid2_25 : block compatible 800 32 := by decide +kernel
private theorem valid2_26 : block compatible 832 32 := by decide +kernel
private theorem valid2_27 : block compatible 864 32 := by decide +kernel
private theorem valid2_28 : block compatible 896 32 := by decide +kernel
private theorem valid2_29 : block compatible 928 32 := by decide +kernel
private theorem valid2_30 : block compatible 960 32 := by decide +kernel
private theorem valid2_31 : block compatible 992 32 := by decide +kernel
private theorem valid2_32 : block compatible 1024 32 := by decide +kernel
private theorem valid2_33 : block compatible 1056 32 := by decide +kernel
private theorem valid2_34 : block compatible 1088 32 := by decide +kernel
private theorem valid2_35 : block compatible 1120 32 := by decide +kernel
private theorem valid2_36 : block compatible 1152 32 := by decide +kernel
private theorem valid2_37 : block compatible 1184 32 := by decide +kernel
private theorem valid2_38 : block compatible 1216 32 := by decide +kernel
private theorem valid2_39 : block compatible 1248 32 := by decide +kernel
private theorem valid2_40 : block compatible 1280 32 := by decide +kernel
private theorem valid2_41 : block compatible 1312 32 := by decide +kernel
private theorem valid2_42 : block compatible 1344 32 := by decide +kernel
private theorem valid2_43 : block compatible 1376 32 := by decide +kernel
private theorem valid2_44 : block compatible 1408 32 := by decide +kernel
private theorem valid2_45 : block compatible 1440 32 := by decide +kernel
private theorem valid2_46 : block compatible 1472 32 := by decide +kernel
private theorem valid2_47 : block compatible 1504 32 := by decide +kernel
private theorem valid2_48 : block compatible 1536 32 := by decide +kernel
private theorem valid2_49 : block compatible 1568 32 := by decide +kernel
private theorem valid2_50 : block compatible 1600 32 := by decide +kernel
private theorem valid2_51 : block compatible 1632 32 := by decide +kernel
private theorem valid2_52 : block compatible 1664 32 := by decide +kernel
private theorem valid2_53 : block compatible 1696 32 := by decide +kernel
private theorem valid2_54 : block compatible 1728 32 := by decide +kernel
private theorem valid2_55 : block compatible 1760 32 := by decide +kernel
private theorem valid2_56 : block compatible 1792 32 := by decide +kernel
private theorem valid2_57 : block compatible 1824 32 := by decide +kernel
private theorem valid2_58 : block compatible 1856 32 := by decide +kernel
private theorem valid2_59 : block compatible 1888 32 := by decide +kernel
private theorem valid2_60 : block compatible 1920 32 := by decide +kernel
private theorem valid2_61 : block compatible 1952 32 := by decide +kernel
private theorem valid2_62 : block compatible 1984 32 := by decide +kernel
private theorem valid2_63 : block compatible 2016 32 := by decide +kernel
private theorem valid2_64 : block compatible 2048 32 := by decide +kernel
private theorem valid2_65 : block compatible 2080 32 := by decide +kernel
private theorem valid2_66 : block compatible 2112 14 := by decide +kernel
set_option maxRecDepth 20000 in
theorem base_valid : block compatible 0 2126 :=
  (@block_union compatible 0 1056 1070 (@block_union compatible 0 512 544 (@block_union compatible 0 256 256 (@block_union compatible 0 128 128 (@block_union compatible 0 64 64 (@block_union compatible 0 32 32 valid2_0 valid2_1) (@block_union compatible 64 32 32 valid2_2 valid2_3)) (@block_union compatible 128 64 64 (@block_union compatible 128 32 32 valid2_4 valid2_5) (@block_union compatible 192 32 32 valid2_6 valid2_7))) (@block_union compatible 256 128 128 (@block_union compatible 256 64 64 (@block_union compatible 256 32 32 valid2_8 valid2_9) (@block_union compatible 320 32 32 valid2_10 valid2_11)) (@block_union compatible 384 64 64 (@block_union compatible 384 32 32 valid2_12 valid2_13) (@block_union compatible 448 32 32 valid2_14 valid2_15)))) (@block_union compatible 512 256 288 (@block_union compatible 512 128 128 (@block_union compatible 512 64 64 (@block_union compatible 512 32 32 valid2_16 valid2_17) (@block_union compatible 576 32 32 valid2_18 valid2_19)) (@block_union compatible 640 64 64 (@block_union compatible 640 32 32 valid2_20 valid2_21) (@block_union compatible 704 32 32 valid2_22 valid2_23))) (@block_union compatible 768 128 160 (@block_union compatible 768 64 64 (@block_union compatible 768 32 32 valid2_24 valid2_25) (@block_union compatible 832 32 32 valid2_26 valid2_27)) (@block_union compatible 896 64 96 (@block_union compatible 896 32 32 valid2_28 valid2_29) (@block_union compatible 960 32 64 valid2_30 (@block_union compatible 992 32 32 valid2_31 valid2_32)))))) (@block_union compatible 1056 544 526 (@block_union compatible 1056 256 288 (@block_union compatible 1056 128 128 (@block_union compatible 1056 64 64 (@block_union compatible 1056 32 32 valid2_33 valid2_34) (@block_union compatible 1120 32 32 valid2_35 valid2_36)) (@block_union compatible 1184 64 64 (@block_union compatible 1184 32 32 valid2_37 valid2_38) (@block_union compatible 1248 32 32 valid2_39 valid2_40))) (@block_union compatible 1312 128 160 (@block_union compatible 1312 64 64 (@block_union compatible 1312 32 32 valid2_41 valid2_42) (@block_union compatible 1376 32 32 valid2_43 valid2_44)) (@block_union compatible 1440 64 96 (@block_union compatible 1440 32 32 valid2_45 valid2_46) (@block_union compatible 1504 32 64 valid2_47 (@block_union compatible 1536 32 32 valid2_48 valid2_49))))) (@block_union compatible 1600 256 270 (@block_union compatible 1600 128 128 (@block_union compatible 1600 64 64 (@block_union compatible 1600 32 32 valid2_50 valid2_51) (@block_union compatible 1664 32 32 valid2_52 valid2_53)) (@block_union compatible 1728 64 64 (@block_union compatible 1728 32 32 valid2_54 valid2_55) (@block_union compatible 1792 32 32 valid2_56 valid2_57))) (@block_union compatible 1856 128 142 (@block_union compatible 1856 64 64 (@block_union compatible 1856 32 32 valid2_58 valid2_59) (@block_union compatible 1920 32 32 valid2_60 valid2_61)) (@block_union compatible 1984 64 78 (@block_union compatible 1984 32 32 valid2_62 valid2_63) (@block_union compatible 2048 32 46 valid2_64 (@block_union compatible 2080 32 14 valid2_65 valid2_66)))))))

end OMA.SharedCert867

/-! Checking the geometric rule instance behind each clause. -/

namespace OMA.CP867
open OMA.SharedCert867

private def budgetRule (c : List ℤ) : Rule :=
  .budget (c.map (fun z => let n := z.natAbs-16385; (n/256,n%256)))


private theorem rules_ok {A : Finset ℕ} {b : ℕ} (H : Erdos867.ConsecutiveSumFree A)
    (h : cost (fun i => (window A i (b+2)).card) < 8) (rs : List Rule) (C : List (List ℤ))
    (good : ((rs.all (Rule.valid 0) && rs.all (Rule.valid 1)) && (rs.map Rule.clause == C)) = true) :
    ∀ c ∈ C, c.any (literal (assignment A b)) = true := by
  obtain ⟨h01,e⟩ := Bool.and_eq_true_iff.mp good
  obtain ⟨h0,h1⟩ := Bool.and_eq_true_iff.mp h01
  intro c hc
  rw [← LawfulBEq.eq_of_beq e] at hc
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hc
  by_cases p : b%2=0
  · exact rule_sound H b 0 p h r (List.all_eq_true.mp h0 r hr)
  · exact rule_sound H b 1 (by omega) h r (List.all_eq_true.mp h1 r hr)
private def r2_0 : List Rule :=
  [.run 2 3 3 7,
   .run 2 4 3 7,
   .run 2 2 6 63,
   .run 4 5 4 9,
   .run 4 6 3 5,
   .run 4 6 5 17,
   .run 4 7 2 3,
   .run 4 7 3 5,
   .run 4 7 4 9,
   .run 4 8 2 3,
   .run 4 8 3 5,
   .run 4 8 4 9,
   .run 4 9 2 3,
   .run 4 9 3 5,
   .run 4 10 3 5,
   .run 4 4 4 11,
   .run 4 4 5 19,
   .run 4 4 5 21,
   .run 4 4 7 81,
   .run 4 5 4 11,
   .run 4 5 4 13,
   .run 4 5 6 35,
   .run 4 5 6 41,
   .run 4 6 3 7,
   .run 4 6 4 11,
   .run 4 6 4 13,
   .run 4 6 5 21,
   .run 4 6 5 25,
   .run 4 6 6 37,
   .run 4 6 6 41,
   .run 4 6 6 49,
   .run 4 6 7 69]
private theorem v2_0 : ((r2_0.all (Rule.valid 0) && r2_0.all (Rule.valid 1)) && (r2_0.map Rule.clause == b2_0)) = true := by decide +kernel
private def r2_1 : List Rule :=
  [.run 4 6 7 81,
   .run 4 7 3 7,
   .run 4 7 4 11,
   .run 4 7 4 13,
   .run 4 7 5 19,
   .run 4 7 5 21,
   .run 4 7 5 25,
   .run 4 7 6 35,
   .run 4 7 6 37,
   .run 4 7 6 41,
   .run 4 8 3 7,
   .run 4 8 4 11,
   .run 4 8 4 13,
   .run 4 8 5 21,
   .run 4 9 3 7,
   .run 4 9 4 11,
   .run 4 9 4 13,
   .run 4 4 5 27,
   .run 4 4 7 83,
   .run 4 4 7 85,
   .run 4 4 8 197,
   .run 4 5 6 43,
   .run 4 5 7 99,
   .run 4 5 7 85,
   .run 4 5 8 165,
   .run 4 6 4 15,
   .run 4 6 5 23,
   .run 4 6 5 27,
   .run 4 6 5 29,
   .run 4 6 6 43,
   .run 4 6 6 45,
   .run 4 6 6 53]
private theorem v2_1 : ((r2_1.all (Rule.valid 0) && r2_1.all (Rule.valid 1)) && (r2_1.map Rule.clause == b2_1)) = true := by decide +kernel
private def r2_2 : List Rule :=
  [.run 4 6 6 57,
   .run 4 6 7 71,
   .run 4 6 7 83,
   .run 4 6 7 77,
   .run 4 6 7 85,
   .run 4 6 7 101,
   .run 4 6 7 89,
   .run 4 7 5 27,
   .run 4 7 6 43,
   .run 4 7 6 45,
   .run 4 7 6 53,
   .run 4 8 4 15,
   .run 4 8 5 23,
   .run 4 8 5 27,
   .run 4 8 6 53,
   .run 6 10 2 3,
   .run 8 11 7 119,
   .run 8 13 7 119,
   .run 8 15 7 119,
   .run 12 20 3 5,
   .run 12 22 2 3,
   .run 12 22 3 5,
   .run 12 23 3 5,
   .run 12 24 2 3,
   .run 12 24 5 17,
   .run 12 25 2 3,
   .run 12 26 2 3,
   .run 12 26 3 5,
   .run 12 26 5 17,
   .run 12 27 2 3,
   .run 12 28 2 3,
   .run 12 15 5 29]
private theorem v2_2 : ((r2_2.all (Rule.valid 0) && r2_2.all (Rule.valid 1)) && (r2_2.map Rule.clause == b2_2)) = true := by decide +kernel
private def r2_3 : List Rule :=
  [.run 12 16 5 27,
   .run 12 17 5 29,
   .run 12 18 6 53,
   .run 12 18 7 85,
   .run 12 18 8 165,
   .run 12 19 4 15,
   .run 12 19 5 27,
   .run 12 19 6 43,
   .run 12 19 6 45,
   .run 12 20 4 15,
   .run 12 20 5 27,
   .run 12 20 5 29,
   .run 12 20 6 45,
   .run 12 20 7 85,
   .run 12 20 8 149,
   .run 12 20 9 325,
   .run 12 21 5 23,
   .run 12 21 6 39,
   .run 12 21 6 43,
   .run 12 21 6 45,
   .run 12 21 6 53,
   .run 12 21 7 85,
   .run 12 22 5 27,
   .run 12 22 5 29,
   .run 12 22 6 45,
   .run 12 22 6 53,
   .run 12 22 6 57,
   .run 12 22 7 75,
   .run 12 22 7 85,
   .run 12 22 8 165,
   .run 12 22 8 197,
   .run 12 22 9 277]
private theorem v2_3 : ((r2_3.all (Rule.valid 0) && r2_3.all (Rule.valid 1)) && (r2_3.map Rule.clause == b2_3)) = true := by decide +kernel
private def r2_4 : List Rule :=
  [.run 12 22 9 325,
   .run 12 23 4 15,
   .run 12 23 5 23,
   .run 12 23 5 27,
   .run 12 23 5 29,
   .run 12 23 6 43,
   .run 12 23 6 57,
   .run 12 23 7 105,
   .run 12 23 8 169,
   .run 12 24 4 15,
   .run 12 24 5 23,
   .run 12 24 5 27,
   .run 12 24 5 29,
   .run 12 24 6 39,
   .run 12 24 6 51,
   .run 12 24 6 45,
   .run 12 24 6 53,
   .run 12 24 7 71,
   .run 12 24 7 83,
   .run 12 24 7 85,
   .run 12 24 7 101,
   .run 12 24 8 165,
   .run 12 25 4 15,
   .run 12 25 5 23,
   .run 12 25 5 27,
   .run 12 25 5 29,
   .run 12 25 6 43,
   .run 12 25 6 45,
   .run 12 25 6 57,
   .run 12 25 8 163,
   .run 12 26 4 15,
   .run 12 26 5 23]
private theorem v2_4 : ((r2_4.all (Rule.valid 0) && r2_4.all (Rule.valid 1)) && (r2_4.map Rule.clause == b2_4)) = true := by decide +kernel
private def r2_5 : List Rule :=
  [.run 12 26 5 27,
   .run 12 26 5 29,
   .run 12 26 6 45,
   .run 12 26 6 57,
   .run 12 26 7 85,
   .run 12 27 5 23,
   .run 12 28 5 27,
   .run 16 22 4 11,
   .run 16 23 4 11,
   .run 16 25 3 7,
   .run 16 26 4 13,
   .run 16 27 4 11,
   .run 16 27 4 13,
   .run 16 28 3 7,
   .run 16 28 4 11,
   .run 16 28 4 13,
   .run 16 29 3 7,
   .run 16 29 4 11,
   .run 16 29 4 13,
   .run 16 30 3 7,
   .run 16 30 4 11,
   .run 16 30 4 13,
   .run 16 31 4 11,
   .run 16 31 4 13,
   .run 16 32 3 7,
   .run 16 32 4 11,
   .run 16 32 4 13,
   .run 16 32 5 21,
   .run 16 33 3 7,
   .run 16 33 4 11,
   .run 16 33 4 13,
   .run 16 34 3 7]
private theorem v2_5 : ((r2_5.all (Rule.valid 0) && r2_5.all (Rule.valid 1)) && (r2_5.map Rule.clause == b2_5)) = true := by decide +kernel
private def r2_6 : List Rule :=
  [.run 16 34 4 11,
   .run 16 34 4 13,
   .run 16 35 3 7,
   .run 16 35 4 11,
   .run 16 35 4 13,
   .run 16 36 3 7,
   .run 16 36 4 11,
   .run 16 36 4 13,
   .run 16 37 3 7,
   .run 16 37 4 11,
   .run 16 38 4 11,
   .run 16 38 4 13,
   .adj 4 4,
   .even 4 4,
   .adj 4 5,
   .lift 2 2 0,
   .adj 4 6,
   .even 4 6,
   .adj 4 7,
   .lift 2 3 0,
   .lift 2 3 1,
   .lift 2 3 2,
   .adj 4 8,
   .even 4 8,
   .adj 4 9,
   .lift 2 4 0,
   .lift 2 4 1,
   .lift 2 4 2,
   .adj 4 10,
   .even 4 10,
   .adj 4 11,
   .lift 2 5 2]
private theorem v2_6 : ((r2_6.all (Rule.valid 0) && r2_6.all (Rule.valid 1)) && (r2_6.map Rule.clause == b2_6)) = true := by decide +kernel
private def r2_7 : List Rule :=
  [.adj 12 15,
   .adj 12 16,
   .even 12 16,
   .adj 12 17,
   .lift 6 8 2,
   .adj 12 18,
   .even 12 18,
   .adj 12 19,
   .adj 12 20,
   .even 12 20,
   .adj 12 21,
   .adj 12 22,
   .even 12 22,
   .adj 12 23,
   .lift 6 11 0,
   .lift 6 11 1,
   .adj 12 24,
   .even 12 24,
   .adj 12 25,
   .lift 6 12 0,
   .adj 12 26,
   .even 12 26,
   .adj 12 27,
   .lift 6 13 2,
   .adj 12 28,
   .even 12 28,
   .adj 12 29,
   .adj 12 30,
   .even 12 30,
   .adj 12 31,
   .even 16 22,
   .adj 16 23]
private theorem v2_7 : ((r2_7.all (Rule.valid 0) && r2_7.all (Rule.valid 1)) && (r2_7.map Rule.clause == b2_7)) = true := by decide +kernel
private def r2_8 : List Rule :=
  [.lift 8 11 0,
   .lift 8 11 1,
   .lift 8 11 2,
   .adj 16 24,
   .adj 16 26,
   .even 16 26,
   .adj 16 27,
   .lift 8 13 0,
   .lift 8 13 1,
   .lift 8 13 2,
   .adj 16 28,
   .even 16 28,
   .adj 16 29,
   .lift 8 14 1,
   .adj 16 30,
   .even 16 30,
   .adj 16 31,
   .lift 8 15 0,
   .lift 8 15 1,
   .lift 8 15 2,
   .adj 16 32,
   .even 16 32,
   .adj 16 33,
   .lift 8 16 0,
   .lift 8 16 1,
   .adj 16 34,
   .even 16 34,
   .adj 16 35,
   .lift 8 17 0,
   .lift 8 17 1,
   .lift 8 17 2,
   .adj 16 36]
private theorem v2_8 : ((r2_8.all (Rule.valid 0) && r2_8.all (Rule.valid 1)) && (r2_8.map Rule.clause == b2_8)) = true := by decide +kernel
private def r2_9 : List Rule :=
  [.even 16 36,
   .adj 16 37,
   .lift 8 18 1,
   .lift 8 18 2,
   .adj 16 38,
   .even 16 38,
   .adj 16 39,
   .lift 8 19 0,
   .lift 8 19 1,
   .lift 8 19 2,
   .adj 16 40,
   .lift 8 20 2,
   .adj 48 69,
   .adj 48 72,
   .adj 48 77,
   .adj 48 82,
   .adj 48 83,
   .lift 24 41 1,
   .adj 48 84,
   .even 48 84,
   .adj 48 85,
   .adj 48 86,
   .adj 48 88,
   .even 48 88,
   .adj 48 89,
   .lift 24 44 1,
   .adj 48 90,
   .adj 48 91,
   .lift 24 45 1,
   .adj 48 92,
   .even 48 92,
   .even 48 94]
private theorem v2_9 : ((r2_9.all (Rule.valid 0) && r2_9.all (Rule.valid 1)) && (r2_9.map Rule.clause == b2_9)) = true := by decide +kernel
private def r2_10 : List Rule :=
  [.adj 48 95,
   .lift 24 47 1,
   .adj 48 96,
   .adj 48 97,
   .lift 24 48 1,
   .adj 48 98,
   .even 48 98,
   .adj 48 99,
   .adj 48 100,
   .even 48 100,
   .adj 48 101,
   .lift 24 50 1,
   .lift 24 50 2,
   .adj 48 102,
   .even 48 102,
   .adj 48 103,
   .adj 48 104,
   .even 48 104,
   .adj 48 105,
   .lift 24 52 1,
   .adj 48 106,
   .even 48 106,
   .adj 48 107,
   .lift 24 53 1,
   .adj 48 108,
   .adj 48 109,
   .adj 48 110,
   .even 48 110,
   .lift 24 55 0,
   .lift 24 55 1,
   .adj 48 112,
   .even 48 112]
private theorem v2_10 : ((r2_10.all (Rule.valid 0) && r2_10.all (Rule.valid 1)) && (r2_10.map Rule.clause == b2_10)) = true := by decide +kernel
private def r2_11 : List Rule :=
  [.lift 24 56 1,
   .adj 48 114,
   .adj 48 115,
   .even 48 116,
   .adj 48 119] ++ (b2_11.drop 5).map budgetRule
private theorem v2_11 : ((r2_11.all (Rule.valid 0) && r2_11.all (Rule.valid 1)) && (r2_11.map Rule.clause == b2_11)) = true := by decide +kernel
private def r2_12 : List Rule :=
  b2_12.map budgetRule
private theorem v2_12 : ((r2_12.all (Rule.valid 0) && r2_12.all (Rule.valid 1)) && (r2_12.map Rule.clause == b2_12)) = true := by decide +kernel
private def r2_13 : List Rule :=
  b2_13.map budgetRule
private theorem v2_13 : ((r2_13.all (Rule.valid 0) && r2_13.all (Rule.valid 1)) && (r2_13.map Rule.clause == b2_13)) = true := by decide +kernel
private def r2_14 : List Rule :=
  b2_14.map budgetRule
private theorem v2_14 : ((r2_14.all (Rule.valid 0) && r2_14.all (Rule.valid 1)) && (r2_14.map Rule.clause == b2_14)) = true := by decide +kernel
private def r2_15 : List Rule :=
  b2_15.map budgetRule
private theorem v2_15 : ((r2_15.all (Rule.valid 0) && r2_15.all (Rule.valid 1)) && (r2_15.map Rule.clause == b2_15)) = true := by decide +kernel
private def r2_16 : List Rule :=
  b2_16.map budgetRule
private theorem v2_16 : ((r2_16.all (Rule.valid 0) && r2_16.all (Rule.valid 1)) && (r2_16.map Rule.clause == b2_16)) = true := by decide +kernel
private def r2_17 : List Rule :=
  b2_17.map budgetRule
private theorem v2_17 : ((r2_17.all (Rule.valid 0) && r2_17.all (Rule.valid 1)) && (r2_17.map Rule.clause == b2_17)) = true := by decide +kernel
private def r2_18 : List Rule :=
  b2_18.map budgetRule
private theorem v2_18 : ((r2_18.all (Rule.valid 0) && r2_18.all (Rule.valid 1)) && (r2_18.map Rule.clause == b2_18)) = true := by decide +kernel
private def r2_19 : List Rule :=
  b2_19.map budgetRule
private theorem v2_19 : ((r2_19.all (Rule.valid 0) && r2_19.all (Rule.valid 1)) && (r2_19.map Rule.clause == b2_19)) = true := by decide +kernel
private def r2_20 : List Rule :=
  b2_20.map budgetRule
private theorem v2_20 : ((r2_20.all (Rule.valid 0) && r2_20.all (Rule.valid 1)) && (r2_20.map Rule.clause == b2_20)) = true := by decide +kernel
private def r2_21 : List Rule :=
  b2_21.map budgetRule
private theorem v2_21 : ((r2_21.all (Rule.valid 0) && r2_21.all (Rule.valid 1)) && (r2_21.map Rule.clause == b2_21)) = true := by decide +kernel
private def r2_22 : List Rule :=
  b2_22.map budgetRule
private theorem v2_22 : ((r2_22.all (Rule.valid 0) && r2_22.all (Rule.valid 1)) && (r2_22.map Rule.clause == b2_22)) = true := by decide +kernel
private def r2_23 : List Rule :=
  b2_23.map budgetRule
private theorem v2_23 : ((r2_23.all (Rule.valid 0) && r2_23.all (Rule.valid 1)) && (r2_23.map Rule.clause == b2_23)) = true := by decide +kernel
private def r2_24 : List Rule :=
  b2_24.map budgetRule
private theorem v2_24 : ((r2_24.all (Rule.valid 0) && r2_24.all (Rule.valid 1)) && (r2_24.map Rule.clause == b2_24)) = true := by decide +kernel
private def r2_25 : List Rule :=
  b2_25.map budgetRule
private theorem v2_25 : ((r2_25.all (Rule.valid 0) && r2_25.all (Rule.valid 1)) && (r2_25.map Rule.clause == b2_25)) = true := by decide +kernel
private def r2_26 : List Rule :=
  b2_26.map budgetRule
private theorem v2_26 : ((r2_26.all (Rule.valid 0) && r2_26.all (Rule.valid 1)) && (r2_26.map Rule.clause == b2_26)) = true := by decide +kernel
private def r2_27 : List Rule :=
  b2_27.map budgetRule
private theorem v2_27 : ((r2_27.all (Rule.valid 0) && r2_27.all (Rule.valid 1)) && (r2_27.map Rule.clause == b2_27)) = true := by decide +kernel
private def r2_28 : List Rule :=
  b2_28.map budgetRule
private theorem v2_28 : ((r2_28.all (Rule.valid 0) && r2_28.all (Rule.valid 1)) && (r2_28.map Rule.clause == b2_28)) = true := by decide +kernel
private def r2_29 : List Rule :=
  b2_29.map budgetRule
private theorem v2_29 : ((r2_29.all (Rule.valid 0) && r2_29.all (Rule.valid 1)) && (r2_29.map Rule.clause == b2_29)) = true := by decide +kernel
private def r2_30 : List Rule :=
  b2_30.map budgetRule
private theorem v2_30 : ((r2_30.all (Rule.valid 0) && r2_30.all (Rule.valid 1)) && (r2_30.map Rule.clause == b2_30)) = true := by decide +kernel
private def r2_31 : List Rule :=
  b2_31.map budgetRule
private theorem v2_31 : ((r2_31.all (Rule.valid 0) && r2_31.all (Rule.valid 1)) && (r2_31.map Rule.clause == b2_31)) = true := by decide +kernel
private def r2_32 : List Rule :=
  b2_32.map budgetRule
private theorem v2_32 : ((r2_32.all (Rule.valid 0) && r2_32.all (Rule.valid 1)) && (r2_32.map Rule.clause == b2_32)) = true := by decide +kernel
private def r2_33 : List Rule :=
  b2_33.map budgetRule
private theorem v2_33 : ((r2_33.all (Rule.valid 0) && r2_33.all (Rule.valid 1)) && (r2_33.map Rule.clause == b2_33)) = true := by decide +kernel
private def r2_34 : List Rule :=
  b2_34.map budgetRule
private theorem v2_34 : ((r2_34.all (Rule.valid 0) && r2_34.all (Rule.valid 1)) && (r2_34.map Rule.clause == b2_34)) = true := by decide +kernel
private def r2_35 : List Rule :=
  b2_35.map budgetRule
private theorem v2_35 : ((r2_35.all (Rule.valid 0) && r2_35.all (Rule.valid 1)) && (r2_35.map Rule.clause == b2_35)) = true := by decide +kernel
private def r2_36 : List Rule :=
  b2_36.map budgetRule
private theorem v2_36 : ((r2_36.all (Rule.valid 0) && r2_36.all (Rule.valid 1)) && (r2_36.map Rule.clause == b2_36)) = true := by decide +kernel
private def r2_37 : List Rule :=
  b2_37.map budgetRule
private theorem v2_37 : ((r2_37.all (Rule.valid 0) && r2_37.all (Rule.valid 1)) && (r2_37.map Rule.clause == b2_37)) = true := by decide +kernel
private def r2_38 : List Rule :=
  b2_38.map budgetRule
private theorem v2_38 : ((r2_38.all (Rule.valid 0) && r2_38.all (Rule.valid 1)) && (r2_38.map Rule.clause == b2_38)) = true := by decide +kernel
private def r2_39 : List Rule :=
  b2_39.map budgetRule
private theorem v2_39 : ((r2_39.all (Rule.valid 0) && r2_39.all (Rule.valid 1)) && (r2_39.map Rule.clause == b2_39)) = true := by decide +kernel
private def r2_40 : List Rule :=
  b2_40.map budgetRule
private theorem v2_40 : ((r2_40.all (Rule.valid 0) && r2_40.all (Rule.valid 1)) && (r2_40.map Rule.clause == b2_40)) = true := by decide +kernel
private def r2_41 : List Rule :=
  b2_41.map budgetRule
private theorem v2_41 : ((r2_41.all (Rule.valid 0) && r2_41.all (Rule.valid 1)) && (r2_41.map Rule.clause == b2_41)) = true := by decide +kernel
private def r2_42 : List Rule :=
  b2_42.map budgetRule
private theorem v2_42 : ((r2_42.all (Rule.valid 0) && r2_42.all (Rule.valid 1)) && (r2_42.map Rule.clause == b2_42)) = true := by decide +kernel
private def r2_43 : List Rule :=
  b2_43.map budgetRule
private theorem v2_43 : ((r2_43.all (Rule.valid 0) && r2_43.all (Rule.valid 1)) && (r2_43.map Rule.clause == b2_43)) = true := by decide +kernel
private def r2_44 : List Rule :=
  b2_44.map budgetRule
private theorem v2_44 : ((r2_44.all (Rule.valid 0) && r2_44.all (Rule.valid 1)) && (r2_44.map Rule.clause == b2_44)) = true := by decide +kernel
private def r2_45 : List Rule :=
  b2_45.map budgetRule
private theorem v2_45 : ((r2_45.all (Rule.valid 0) && r2_45.all (Rule.valid 1)) && (r2_45.map Rule.clause == b2_45)) = true := by decide +kernel
private def r2_46 : List Rule :=
  b2_46.map budgetRule
private theorem v2_46 : ((r2_46.all (Rule.valid 0) && r2_46.all (Rule.valid 1)) && (r2_46.map Rule.clause == b2_46)) = true := by decide +kernel
private def r2_47 : List Rule :=
  b2_47.map budgetRule
private theorem v2_47 : ((r2_47.all (Rule.valid 0) && r2_47.all (Rule.valid 1)) && (r2_47.map Rule.clause == b2_47)) = true := by decide +kernel
private def r2_48 : List Rule :=
  b2_48.map budgetRule
private theorem v2_48 : ((r2_48.all (Rule.valid 0) && r2_48.all (Rule.valid 1)) && (r2_48.map Rule.clause == b2_48)) = true := by decide +kernel
private def r2_49 : List Rule :=
  b2_49.map budgetRule
private theorem v2_49 : ((r2_49.all (Rule.valid 0) && r2_49.all (Rule.valid 1)) && (r2_49.map Rule.clause == b2_49)) = true := by decide +kernel
private def r2_50 : List Rule :=
  b2_50.map budgetRule
private theorem v2_50 : ((r2_50.all (Rule.valid 0) && r2_50.all (Rule.valid 1)) && (r2_50.map Rule.clause == b2_50)) = true := by decide +kernel
private def r2_51 : List Rule :=
  b2_51.map budgetRule
private theorem v2_51 : ((r2_51.all (Rule.valid 0) && r2_51.all (Rule.valid 1)) && (r2_51.map Rule.clause == b2_51)) = true := by decide +kernel
private def r2_52 : List Rule :=
  b2_52.map budgetRule
private theorem v2_52 : ((r2_52.all (Rule.valid 0) && r2_52.all (Rule.valid 1)) && (r2_52.map Rule.clause == b2_52)) = true := by decide +kernel
private def r2_53 : List Rule :=
  b2_53.map budgetRule
private theorem v2_53 : ((r2_53.all (Rule.valid 0) && r2_53.all (Rule.valid 1)) && (r2_53.map Rule.clause == b2_53)) = true := by decide +kernel
private def r2_54 : List Rule :=
  b2_54.map budgetRule
private theorem v2_54 : ((r2_54.all (Rule.valid 0) && r2_54.all (Rule.valid 1)) && (r2_54.map Rule.clause == b2_54)) = true := by decide +kernel
private def r2_55 : List Rule :=
  b2_55.map budgetRule
private theorem v2_55 : ((r2_55.all (Rule.valid 0) && r2_55.all (Rule.valid 1)) && (r2_55.map Rule.clause == b2_55)) = true := by decide +kernel
private def r2_56 : List Rule :=
  b2_56.map budgetRule
private theorem v2_56 : ((r2_56.all (Rule.valid 0) && r2_56.all (Rule.valid 1)) && (r2_56.map Rule.clause == b2_56)) = true := by decide +kernel
private def r2_57 : List Rule :=
  b2_57.map budgetRule
private theorem v2_57 : ((r2_57.all (Rule.valid 0) && r2_57.all (Rule.valid 1)) && (r2_57.map Rule.clause == b2_57)) = true := by decide +kernel
private def r2_58 : List Rule :=
  b2_58.map budgetRule
private theorem v2_58 : ((r2_58.all (Rule.valid 0) && r2_58.all (Rule.valid 1)) && (r2_58.map Rule.clause == b2_58)) = true := by decide +kernel
private def r2_59 : List Rule :=
  b2_59.map budgetRule
private theorem v2_59 : ((r2_59.all (Rule.valid 0) && r2_59.all (Rule.valid 1)) && (r2_59.map Rule.clause == b2_59)) = true := by decide +kernel
private def r2_60 : List Rule :=
  b2_60.map budgetRule
private theorem v2_60 : ((r2_60.all (Rule.valid 0) && r2_60.all (Rule.valid 1)) && (r2_60.map Rule.clause == b2_60)) = true := by decide +kernel
private def r2_61 : List Rule :=
  b2_61.map budgetRule
private theorem v2_61 : ((r2_61.all (Rule.valid 0) && r2_61.all (Rule.valid 1)) && (r2_61.map Rule.clause == b2_61)) = true := by decide +kernel
private def r2_62 : List Rule :=
  b2_62.map budgetRule
private theorem v2_62 : ((r2_62.all (Rule.valid 0) && r2_62.all (Rule.valid 1)) && (r2_62.map Rule.clause == b2_62)) = true := by decide +kernel
private def r2_63 : List Rule :=
  b2_63.map budgetRule
private theorem v2_63 : ((r2_63.all (Rule.valid 0) && r2_63.all (Rule.valid 1)) && (r2_63.map Rule.clause == b2_63)) = true := by decide +kernel
private def r2_64 : List Rule :=
  b2_64.map budgetRule
private theorem v2_64 : ((r2_64.all (Rule.valid 0) && r2_64.all (Rule.valid 1)) && (r2_64.map Rule.clause == b2_64)) = true := by decide +kernel
private def r2_65 : List Rule :=
  b2_65.map budgetRule
private theorem v2_65 : ((r2_65.all (Rule.valid 0) && r2_65.all (Rule.valid 1)) && (r2_65.map Rule.clause == b2_65)) = true := by decide +kernel
private def r2_66 : List Rule :=
  b2_66.map budgetRule
private theorem v2_66 : ((r2_66.all (Rule.valid 0) && r2_66.all (Rule.valid 1)) && (r2_66.map Rule.clause == b2_66)) = true := by decide +kernel
theorem model₂ {A : Finset ℕ} {b : ℕ} (H : Erdos867.ConsecutiveSumFree A)
    (h : cost (fun i => (window A i (b+2)).card) < 8) :
    ∀ c ∈ base₂, c.any (literal (assignment A b)) = true := by
  intro c hc
  obtain ⟨C,hC,hc'⟩ := List.mem_flatten.mp hc
  have each : ∀ X ∈ [b2_0,b2_1,b2_2,b2_3,b2_4,b2_5,b2_6,b2_7,b2_8,b2_9,b2_10,b2_11,b2_12,b2_13,b2_14,b2_15,b2_16,b2_17,b2_18,b2_19,b2_20,b2_21,b2_22,b2_23,b2_24,b2_25,b2_26,b2_27,b2_28,b2_29,b2_30,b2_31,b2_32,b2_33,b2_34,b2_35,b2_36,b2_37,b2_38,b2_39,b2_40,b2_41,b2_42,b2_43,b2_44,b2_45,b2_46,b2_47,b2_48,b2_49,b2_50,b2_51,b2_52,b2_53,b2_54,b2_55,b2_56,b2_57,b2_58,b2_59,b2_60,b2_61,b2_62,b2_63,b2_64,b2_65,b2_66],
      ∀ d ∈ X, d.any (literal (assignment A b)) = true := by
    simp only [List.forall_mem_cons,List.not_mem_nil, false_implies, forall_const, and_true]
    exact ⟨rules_ok H h _ _ v2_0,
      rules_ok H h _ _ v2_1,
      rules_ok H h _ _ v2_2,
      rules_ok H h _ _ v2_3,
      rules_ok H h _ _ v2_4,
      rules_ok H h _ _ v2_5,
      rules_ok H h _ _ v2_6,
      rules_ok H h _ _ v2_7,
      rules_ok H h _ _ v2_8,
      rules_ok H h _ _ v2_9,
      rules_ok H h _ _ v2_10,
      rules_ok H h _ _ v2_11,
      rules_ok H h _ _ v2_12,
      rules_ok H h _ _ v2_13,
      rules_ok H h _ _ v2_14,
      rules_ok H h _ _ v2_15,
      rules_ok H h _ _ v2_16,
      rules_ok H h _ _ v2_17,
      rules_ok H h _ _ v2_18,
      rules_ok H h _ _ v2_19,
      rules_ok H h _ _ v2_20,
      rules_ok H h _ _ v2_21,
      rules_ok H h _ _ v2_22,
      rules_ok H h _ _ v2_23,
      rules_ok H h _ _ v2_24,
      rules_ok H h _ _ v2_25,
      rules_ok H h _ _ v2_26,
      rules_ok H h _ _ v2_27,
      rules_ok H h _ _ v2_28,
      rules_ok H h _ _ v2_29,
      rules_ok H h _ _ v2_30,
      rules_ok H h _ _ v2_31,
      rules_ok H h _ _ v2_32,
      rules_ok H h _ _ v2_33,
      rules_ok H h _ _ v2_34,
      rules_ok H h _ _ v2_35,
      rules_ok H h _ _ v2_36,
      rules_ok H h _ _ v2_37,
      rules_ok H h _ _ v2_38,
      rules_ok H h _ _ v2_39,
      rules_ok H h _ _ v2_40,
      rules_ok H h _ _ v2_41,
      rules_ok H h _ _ v2_42,
      rules_ok H h _ _ v2_43,
      rules_ok H h _ _ v2_44,
      rules_ok H h _ _ v2_45,
      rules_ok H h _ _ v2_46,
      rules_ok H h _ _ v2_47,
      rules_ok H h _ _ v2_48,
      rules_ok H h _ _ v2_49,
      rules_ok H h _ _ v2_50,
      rules_ok H h _ _ v2_51,
      rules_ok H h _ _ v2_52,
      rules_ok H h _ _ v2_53,
      rules_ok H h _ _ v2_54,
      rules_ok H h _ _ v2_55,
      rules_ok H h _ _ v2_56,
      rules_ok H h _ _ v2_57,
      rules_ok H h _ _ v2_58,
      rules_ok H h _ _ v2_59,
      rules_ok H h _ _ v2_60,
      rules_ok H h _ _ v2_61,
      rules_ok H h _ _ v2_62,
      rules_ok H h _ _ v2_63,
      rules_ok H h _ _ v2_64,
      rules_ok H h _ _ v2_65,
      rules_ok H h _ _ v2_66⟩
  exact each C hC c hc'
end OMA.CP867

/-! Kernel-verified local refutation using bit-set unit propagation. -/
namespace OMA.SharedCert867

private def learn₂p0 (i:ℕ) : ℕ := packedAt 0x100000000000000000000010000000000000000000000000000000000000000084a0000000000000000000002000000000000000080000000000000000000000010940000000000000000000004000000000000000800000000000000000000000021280000000000000000000000000000000000000000000000000000000000000842500000000000000000000000000000000000004000000000000000000000001084a000000000000080000000000000000000000180000000000000000469000000000000000000000100000000000000000000000000000000540000008883a000000000000000000000200000000000000028000000000000000000000011094000000000000000000000400000000000000050000000000000000000000022106c00000000000000000000000000000000000005000000000000000000000002241f00000000000001000000000000000000000004000000000000000000000001084a0000000000000200000000000000000000000800000000000000000000000a1094000000000000000000400000000000000000000000000020932000000000000000000000000020000000000000000000000000000000000002421000000000000000000000000000000000000004000000000000000000000009423000000000000000000000000010000000000000000000000000000000000005210 0x10250f1e0e170d100c090b020a1d0912080b06ff05f504ee03e7031a021101090000 (i%16)
private def learn₂p1 (i:ℕ) : ℕ := packedAt 0x200000001000000000000020000000000000000000000008000000000000000000000000004949b000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000005307c0000000002000000000000000000000000000000000000000000000000000000000014c1f0000000000000000000000000000000000000000000000000000000040000000000005341b000000000800000000000000000000000000000000000040000000000000000000000000004a4d8000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000a60fa000000000000000000000000a27d880000000000000000000000000000000000000000000020000000000000000000000000000000000001532bc000000000000000000000000000000000000000000000000000000001542b00002000000000000000000000000000000000000000000000000000000000000150ac00008000000000000000000000000000000000000000000000000000000000000d42b00000000000000000000015bc00000000000000000000000000000000000000000000000000000000000000508c00000000000000000000000000000000000000000000000000000000000001508c00000000000000000000000000000000000000000000000000000000000002427000000000000000000000000000000000000000000000000000000000000005210 0x117e10450e9f0d790c510b180978090407a306ad05970481041f0317020f01090000 (i%16)
private def learn₂p2 (i:ℕ) : ℕ := packedAt 0x100000000004000000000000000000000000000000000000000000000000000000000001509c0000200000000000000000000000000000000000000000000000000000008a00000000000002a84600000000000100000000000000000000000000000000000000800000000000000000000a421000000000000000000000000000000000040000000000000002688000000000800000000000000000000000a00000000020000000000000001a138000000000000000000000000000000000000000000020000000000000005a138000000000001000000000000000000000000000000012b5400000000000000000000000001400000000000000000100000000000000000000000000000009a53800000000000000001000000000000020000002000001000000000000000000000000000000000000000400000000000000150ac000000000000000008000000000000100000010000000000000000000000000000000002000000000002000000000000000a856000000000000000004008000000000080000008000000000000000000000000000000001100000000001000000000000000542b000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000014c1f4000000000000000000000000000000002000000000000000000000000001a85600000000400000000000000000000000000000000000008000000000000000000000000000949b000000000000000000002100000000000000000000000040000000000000000000000000024a4d8000000000001000000000000000000000100000000000000000000000040000000000000000000000000024a4d 0x13cd12a3116210350f600e600d600ca30b5c09bf0822068504e103de02a5016c0000 (i%16)
private def learn₂p3 (i:ℕ) : ℕ := packedAt 0x2000000008820000000000000000000000800000000000000000011a40000000100400000000000000000000014000000000000000000234800000000000000000000000000000000000000000000000000000000000aa42100000000000000000000000000000000000000000000000000000000000354842000020000000000000000000000000000000000000000000000000000006a90840000000000000000000000000000000000002aa0002000000000000000000000000000000000000000000000000000000000014842000000002000000000000000000000000a4fd000000008000000000000000002000000540c000008004200000000000000000000000000000000000000000180a000000000000000a158000004008400000000000000000000000000000000000000000301400000000000000142b000000201080000000000000000000000000000000000000000060280000000000000028560000001021000000000000000000000000000000000000000000c0500000000000000050ac200000000000000000000000000000000000000000800000000000000000185e10800000000000000000000000000000000000000000202800000000000000285610800000000000000000000000000000000000000000202800000000000000a8562000000000000000000000000a27f 0xfba0edb0dfc0cf90bf60af3094a08b5082306fc05d504ae03870286017e00760000 (i%16)
private def learn₂p4 (i:ℕ) : ℕ := packedAt 0x100000000000000002000000000000000000000000000000000000000000000000000000080000000000000000000000000269084000000000000000000000000000000000000000000000000000000000000052108000000000000000000000000000000000000000000000000000000000000a421500000000000000000140000000000000000000000000040000000000000000000000267d84000000000000000000000000000000000100000000000000000000000000d09c50000000000000000011000000054540000140000000000000000000000000000000002200000000000000000000000009a13a000000000000000000000000000000000100000000000000000000000000cd09c2000000000000000000000000000000000400000000000000000000000000684e000000000000000000000000000000000280000000004ad10000000000000000140000000000000000000000000000000004400000000000000000000000006158000000004000000000000000000000001200000000000000000000000001a138000000004400000000000000029f8000000000200000000000000000000000000000000012b4000000000001000000000000000000000127ca0000000000000000000000000000000000400000001000000000000000004d09c0000000000000000000000000000000000000000000000000000000000015210 0x10490eab0da40ca10b7c0a7708e007db06d6061904d003d0035c029f020801030000 (i%16)
private def learn₂p5 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000000000000400000000000000000000000000000000000001000000000000000000000000004d21080000000000000000000000000000000000000000400000000000000000000000000000040000000000000000000000000134842000000000000000000000000000000000000000000000000000000000000004000000001000000200000000000000000004d2108000000000000000400014a90000000000000000000000000000000000008000000000000000400014a900008000000000000000000000000000000080000000000000006678000000000000000000000000000000000000000000000000000000014a9000000000000000000000000000000000000000000400000000000000026880000000000000000000200000000000000000000000000000000000000000100000000044000008000400000000000000134842000000000000000000008000040000000000000000000080000000000000000000000001100000000010000000000000004d21080000000000000000000200000400000000000000000002000000000000000000000000044000000000400000000000000134842000000000000000000008000001000000000000000000080000000000000000000000001100000000010000000000000004d210800000000000000000000000000000000000000000020000000000000001344000000000000000000000000000000000000000080000000000000000000000000000002000000000000000000000000009a42100000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000014842000000000000000000000000000000000000000000000000000000000000002800000001000000000000000000000000004d210 0x1536139811fa105c0ffd0f0d0e300d410c4c0aae0910077205d404db033d019e0000 (i%16)
private def learn₂p6 (i:ℕ) : ℕ := packedAt 0x4000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000001a4210000000000000000000000000000000000000000200000000000000000000000000000002000000000000000000000000006908400000000000000000000000000004400000000008000004000000000000000000000000000000000102653800000000000000000000000000000000000000010000008000000000000000000000000000000000144ca7000000800000000000000000000000000000000014cca7500000000000000000000000000200000000000000000000000a1214000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000001a4210000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000006908400000000000000000000000000000000000000000000000000000000000014842000000000000000000000000009a4210000000000000000000000000000000000004000000000000000000000000013484200000000000000000000000000000000000008000000000000000000000000026908400000000000000000000000000000000000040000000000000000000000000134842000000000000000000000000000000000002000000000000000000000000009a42100000000000000000000000000000001000000000000000000000000004d210aa800080000000000000000000000000000001000000000000000000000000004d210 0x129710f90f5b0e000ca50bed0b0f097107d306ce06510542042f031e021101140000 (i%16)
private def learn₂p7 (i:ℕ) : ℕ := packedAt 0x8000000000000000000080000000000000000000000000000000000000000000000000003000000002008028000236800000000000000000000000000000000000000000000000000000001491000000000000000000000000000000000000000000000000000000000292288000000000000000000000000002a00000000000000002000000000000000000000000000000000081329d0052440000000000000000000000000000000000000000000000002952000000000000000000000000000000000000000000000000000000000000000000149100000000000000000000000000000000000000000000000000000000000000000000000000000000000000a48a20000000000000000000000000000000000000000000008000000000000000000000000000000000144ca74052440000000000000000000000000000000000000000000000000a5280000000000000000000000000000000000000000000000000000000052440000000000000000000000000000000000000000000000000000000000000000000000000000000000002922000000000000000000020000000000000000000010000000000000000000000000000000c0000000080200000008da800400000000000000000002000000000000000000000000000000000000000000000000000000000014c1f40080000000000000000000100000000000000000000000000000000000000000000000000000000000a60f 0x10e40f6c0e7d0d8a0c2f0c170b460a2d08c8076d075706840593043202ba015d0000 (i%16)
private def learn₂p8 (i:ℕ) : ℕ := packedAt 0x348420000000000000000000000000000000000000000000000000000000000348420000000000000001000014a5000000000000000000000000000000000000800000000000000040000529400002000000000000000000000000000000200000000000000012658000000000000000000000000000000000000000000000000000000014a500000000000000000000000000000000000000000100000000000000009a20000000000000000000000000000000000000000000000000000000000000080000000000000004d100000000000000000000000000000000000000000000000000000000000004000000000000000268800000000000000000000000000000000080000000000000004d100000000000000000000000000000000040000000000000002688000000000000000000080000000000000010000000000000000000000000000000000003000000002008000000236aa000000000000000000000000004000000000000000000000010242800000000000000000008000000000000010000000000000000000000000000000000000300000000200800000023680000000000000000000800000000000000400000000000000000000000000000000000030000000020080000002368000000000000000000080000000000000004000000000000000000000000000000000003000000002008000000236 0x100a0ffa0efe0e9d0dab0ccc0bdd0aea09a50864079106c00548046802f001780000 (i%16)
private def learn₂p9 (i:ℕ) : ℕ := packedAt 0x100000000000000000000000000000000000000000000000000000000000000000000014c1f50000000000000020000000000000000000000000000000000021257800000000000000000000000000000000000000000000000000000000000000000000029084000000000000000000000000000000000000000000000000000000000000000000001484200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a4210000000000000000000000000000000000000000000000000000000000000000000000000000000521080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a4210000000000000000054080000000000000000000000000000000000000000000400000000000000a15aa80000000000000000002a20000000aaa0000002a00000000000000000000000000000000040000000000400000000000000050ad54000000000000000000151000000055500000014000000000000000000000000000000000200000000002000000000000000a856880000000000000000000a000000002a00000000a000000000000000000000000000000000500000000011000000000000000542b0000000000000000000000000000000000000000000a5280000000000000000000000000000000000000000000000000000000000000000000000000000000a42150000000000000000050000000000000000000000000000000000400000000000000000000000002a15800000000000000000000000000000000000000000000000000000000000000014a500000000000000000000000000000000000000000000000000000000000000000a52 0x149913711290116710420e9d0d500bad0a6408bf071a057504bc036d022001110000 (i%16)
private def learn₂p10 (i:ℕ) : ℕ := packedAt 0x2000400000000000000000000400000000000000000000000010000000000000000004000000a4fd54080000000000000000151000000015500000015000000000000000000000000000000000200000000002000000000000000285680000000000000000000000000400000000000000000000000149faa80000000000000000002a240000002aa0000002a00000000000000000000000000000000040000000000400000000000000050ac0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014842a8000000000000000000000000000000000040000000000000002688800000000000000000028000000000aa0000002a00000000000000000000000000000000140000000002400000000000000050ad4000000054000008000000000000000000000000008000000000088000000000000000a15a000000000000000000000000000000000000000000040000000000000000d0ad0000000000000000000154000000015400000054000000000000000000000000000000000400000000008000000000000000a15800000000000000000000000000000000000000000000000000000000000000000000000000000000a4214000000000000000000054000000005500000015000000000000000000000000000000000180000000002000000000000000285600000000000000000000000000000000000000000000000000000000000000000000000000000000a42100000000000000000000000000000000000000000000000000000000000000000000148420000000000000000000000000000000000000000000000000000000000000000000000290840000000000000000000000000000000000000000000000000000000000000000000005210 0x150613c91226114a0fa70dfe0d200b7f0a58095707b8066504c60375025201270000 (i%16)
private def learn₂p11 (i:ℕ) : ℕ := packedAt 0x10000000000000000000002000000000800000000000000000000080000000000000000000085000000020d4a75000000000000000000000000000000008000000000000000000000000000685620000020000000000000280aa000002800000002a000000000000000000000000000000001400000000044c400000000000005308d50000000000000000000544000000055400000054000000000000000000000000000000000800000000008000000000000000a15aa0000000000000000000a880000000aa8000000a800000000000000000000000000000000120000000001000000000000000142b540000000000000000001510000000955000000150000000000000000000000000000000002000000000020000000000000002856a80000000000000000002a200000012aa0000002a00000000000000000000000000000000050000000000400000000000000050ad50000000000000000000544000000055400000054000000000000000000000000000000000800000000009400000000000000a15800000000000000000000000000000000000000000000000000000000000000000000000000000000000000529552000000000000000000544000000055400000054000000000000000000000000000000000800000000008000000000000000a158000000000000000554000400000000000000000000008000000000000000000000040000000000000983ea88000000000000000002a200000002aa0000002a00000000000000000000000000000000050000000000500000000000000050ac40000000000000000001500000000155000000150000000000000000000000000000000006800000000020000000000000002856000000000000000000000000000000000000554000400000000000000000000008000000000000000000000040000000000000983ea88000000000000000002a200000002aa0000002a00000000800000000000000000200000150000000000400000000000000050ad51400000000000000000544000000055400000054000000010000000000000000004000002a00000000008000000000000000a15 0x18d1176d166a14c31320117d0fda0e370c940b2b09880832068f04ee034601a30000 (i%16)
private def learn₂p12 (i:ℕ) : ℕ := packedAt 0x20000000000000001000000000002000000000000000020000000c000000000000000023480000000000000000000000100000000000000000000000000010000000000000000100000006000000000000000011a400000200000000000000000000040000000000000000400000018000000000000000046900020000000000000000000000000002000000000000000020000000c0000000000000000234800000000000000000000000100000000000000000000000000010000000000000000100000006000000000000000011a4000000000000000000000002000000000000001000000000000000000000000000000000000000000000200000000000000028560000000000000000000008040000000280000008000000000000000000000000000000000000000000001000000000000000142b00000000000000000000040080000001400000040000000000000000000000000000000000000000000008000000000000000a1580000000000000000000000000000000000000000000000000004000000000000000040000000000000000000000000000000a90940000000000000000000000000000000000000000000000000000000000000029620000000000000000000000000000000000000000000000000000000000000052c4000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000014423000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000005212800000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000002a84600000000000000000000040000000010001000000000000000000000000000000000000009800000002418000000000000002a4250000000004000000000000000000000000000000000000000002600000000916653 0x16b61594141312f111c0103b0e9a0cf90b5809b308aa07a305fd045802b2010d0000 (i%16)
private def learn₂p13 (i:ℕ) : ℕ := packedAt 0x214000000000000000000000000000000000000000000180000000481284000000050000000000000000000000000000000000000000000100000000200000000000000069846000000000000000400000000000000000000000000000000000080000000000000000000000034c2300000011400000010000000000000000000000000000000000004000000008000000000000001a61180000000000000008000000000000000000000000000000000012000000000000000000000000d308c00000085000000100000000000000000000000000000000000018000000024000000000000002856800000000000000000001000000000000000000000000000000033327d000000000000000000000000000000000008000000000000000000000000698460000000000000000000008020000000280000008000000000002000000000000000020000000c00000001000000000000000142b00080000000000000000000000000008000000000000000080000003000000000000000008d20000000000000004000000000002000000000000000020000000c0000000000000000234aa0000000000000000000aa80000000aa8000000a800000000000000000000000000000000000000000001000000000000000142b0080000000000000000000000000008000000000000000080000003000000000000000008d20400000000000000000000000000040000000000000000400000018000000000000000046900000008000000000000000000010000000000000000100000006000000000000000011a4000000000000000000000020000000000000000000000000002000000000000000020000000c0000000000000000234 0x13b612cb118610410efc0db70c760b8f0a8a08e907ba069804f503ca02a1017f0000 (i%16)
private def learn₂p14 (i:ℕ) : ℕ := packedAt 0x800000000000000000000000000000000000000000000014a1000000000000000000000000000000000000000000000000000000029422000000000000000000020000000002a8000000a8000000000000000000000000000000000000000000010a0000000000000142b50000000000000000000540000000015408000054000000000000000000000000000000000000000000008000000000000000a15800000000000000000000000000000000000000000000000000000000000000000528400000000000000000000000000000000000000000000000000000000000000002942000000000000000000000000000000000000000000000000000000000000000000000000000000000000014a10100000000000000000000000000000004d129c0000000000000020000000002280000008000000000000000000000000000000000002000000009000000000000000142b00000000000008000000000000000000000000000000010000000000000000000000000000000a04a10000000000000008000000000000000000000000000000000000000000001000000000000000142b0000000000000000200000008a0000002a000000000000000000000000000000008048000000024c0000000000000050ac000000000000000200000008a0000002a00000000000000000000000000000000804c000000024c0000000000000050ac000000000000000020000000002a8000000a800000000000000000000000000000002040000000009000000000000000142b0000000000000000200000000000000000000000000000000002600000000a04a10000000000000000000000000000000000080000000000000000000000005a611 0x13d4130d122210810ee00dcb0cba0b550abb093107e906a90523039f020d01050000 (i%16)
private def learn₂p15 (i:ℕ) : ℕ := packedAt 0x1414000000000000000000000000000000000000000000000000000000000000000000002a8000000296253a0000000000000000000000000000000000000000000000000000000000000000000400000000002000000000000000a17800000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000002429000000000000000000000000000000000080000000000000000000008000000000000000000000000004cc932000000000000000000000000000000000400000000000000000000040000000000000000000000000026649900000000000000000000000000000000010000000028850000000000000042d000000000000000000000000000000000000000000000000028850000000000000242d400000000000000000000000000020000000000000000000000a4f55000000050000000000000000000000000000000000000000000040000000000000002615a00000000000000a14800000000000000000000000000000000000000000000000000000000000000000014291000000000000000000010000000001540000005400000000000000000000000000000000000000000000850000000000000085e0000010000000000000000000000000000000000000000000020000000000000002429000000000000000000000000000000000000000000000000000000000000000002942000000000000000000000000000000000000000000000014a10000000000000000000000000000000000000000000000a50 0x120110a80f200d950c320ad109d508bd07e106bc0674055903ba02a1018e00c50000 (i%16)
private def learn₂p16 (i:ℕ) : ℕ := packedAt 0x111540000000000000000000000000500000000500000000000000000000000000000000028a0000000086800000000000002a1588280000000000000000000000000000000000000000000000000000000000000000000014d000000044b4a7000000000000000000000000000000000000000000000000000000000000000000000000000000044c000000000000042f00000081000000000000000000000800000000000000000000006000000018980000011a4000000000000000000000000800000000000000000000000000000000000000000010000000000113000000000000010bc000000000000000000000000000000000000000000808000000000000000000000000000000010b129d00010000000000000000100400000014000000100000040000002000000000000000000002a900000020626000000000000028568000000000000000000008020000000200000008000002000800100000000000000000000000800000113130000000000000142b00000000000000000000000020000000000000000000000000000000000000000000c0000000000400000000000000142f1000000000000000000000000000000000000000000000000000000000000000000000000000000440000000000000042f1000000000000000000000000000000000000000000000000000000000000000000100000000000440000000000000042f00000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000c21280000000000000000200000000000000000000000000000000000000000000000000000000000002000000000000000217800000000000000008000000000000000000000000000000000000000000000000000000000000020000000000000002178000000000000000008000000000000000000000000000000000000000000000000000000000000200000000000000021784000000000000000550000000000000000000000000000100000000000000000000000000000002200000000000000a17 0x180116641505137d125b10d30f870de60c450abd093507ad06200498031001880000 (i%16)
private def learn₂p17 (i:ℕ) : ℕ := packedAt 0x400000000000000000000000000000000000000000000000008490000000000000090a400000000000000000000000000000000000000000000000008498000000000000090a4100000000000000000000000000000000000000000000000002126000000000000024290000000000000000000000000000000000000000000000000000004000000000000048520000000000000000000000000000208000000000000000000000000000000000000000000000000109300000000000001214800000002000000000000000000000000000000000000000000020000000000000004a12a0800000000000000000000000000820000004000000000000000000000000000000000000000000424a74000000000000000000000000000a000000000000000000000000a7da80000000000000002aa0000000000000000000000000020400000000000000000000004f700000004400000000000000000000000000000000000000000004000000000000000942504000000000000000000000000000000000000000000000000084980000000000000984e00000000000000000000000000208000001000000000000000000000000000000000000000000109300000008caa0000000000000000a280000000000000000000000000080000000000000000000000053dd50000000000000000000000000000020000000000000000000004000000000000000004650000000000000000000000000000200000000000000000000000000000000000000000000000000048000000000000042f0014000000000000000144000000014100000054140000000000000000000000000000000000000000084800000000000000a15 0x1397127f116710490f2a0d980c780b250a44091d07fd06de0572044b0325019d0000 (i%16)
private def learn₂p18 (i:ℕ) : ℕ := packedAt 0x400000000200000000000000000000000000000000000000000022200000000000000a5094000000004000000000000000000000000a02a000000000000000000000000000000000000000000000200000000000000000000000000000000144ca700000010000000000000000000000000000000000000000000024000000000000024294000000000000000000000000000000000000000000800000000000000001a178aa800000000000000002aa0000000000000000200000000000000000000000000000000000000000011110000000000000052c23000000100000000000000000000000000000000000000000002040000000000000261380000000000000000000000000000000000000000000000000902000000000000012148000000004000000000000000000000000000000000000000000240000000000000004852a80000000000000000a8280004000000000000000000000000000000000001010000000000000001284aa80000000000000000a00000040000000000000000000000000000000000010000000000000000052c2300000000040000000000000000000000000000000000000000004808000000000000090a400000000000000000000000000000000000000000008080000000000000984e000000000000000000000000000000000000000000000000002480000000000000485200400000000000000000000000000000000000000000000000000010000000000000090a408000000000000000000000000000000000000000000000000000200000000000001214 0x1233110f107e0f290e110d100b6d0a54093c081a06ca05790457035a0242011f0000 (i%16)
private def learn₂p19 (i:ℕ) : ℕ := packedAt 0x100000000000000000000000000000000000000000000000000000000000000295a0000000000000000000000000000000000000000000000000000000000000014ad00000000000000000000000000000000000000000000000000000000000000a56a0a000000000000000a0a00000000000000000000000000000000520000000424c000000000000050ac00000000000000000000000000000000000000000000000000000295a0000000000000000000000000000000000000000000000000000052b4000000000000000000000000000000000000000000000000000000000000000a56a800000002800000002828000000000200000000000000000000014000000010930000000000000142b5000000005080000004000000000000400000000000000000000028000000021260000000000000a8560000000000000000000000000000000000000000000000000000000000000000000000000000000000014ad00000000000000000001440000000140000000141400000000010000000000000000000008a0000000084980000000000000a15800000000000000000002200000000a1000000080000000000008000000000000000000004500000000424c000000000000150ad0800000000000000000004000000000000000000002a8000000025264f800000000000000002004000000000000000000000000000000a5264f80000000000000000000000000000000000000000000000000012000000000000012148000000004000000000000000000000000000000000000000000444000000000000004a12 0x1269116210590f540e0b0d260c430b3809ed08a2074505a8040b0320023c01240000 (i%16)
private def learn₂p20 (i:ℕ) : ℕ := packedAt 0x80000000000000000000000000000000000000000000000000092000000000000010bc1000000000000000000000000000000000000000000000000011200000000000000285600000000000000000000000000000000000000000044ad000000000000000000000000000000000000000000895a00000000000000000000000000000000000000000000000004248000000000000042f0000000000000000000000000000000000000000000a5680000000000000000000000000000000000000000000000000000000000000508400000000000000000000000000000000000000000000000000000000000000a10800000000000000000000000000000000000000000000000010920000000000000104230000040000000000000000000000000000000000000000000212400000000000002084600000a0000000000000000000000000000000000000000000424800000000000004108c0000000000000000000000000000000000000000000000000000000000000a56800000000000000000000000000000000000000000000000000000000000052b500000000000000014040000000000000000000000000000000004000000084980000000000000a1580000000000000000000000000000000000000000000000000000000000014ad40000000000000014040000000000000000000000000000000024000000084980000000000000a15 0x10540f3f0e220d690cb20b9d0ae409df08d807bd06a2058704840383024001410000 (i%16)
private def learn₂p21 (i:ℕ) : ℕ := packedAt 0x2a00000000000000000000000a000000000000000000004200000000000000000000000000000044c9f5000000000000000050000000000000000000000000000400000000000000000000029ee008000000000000000000000000000000000000000000000000101200000000000005042300000000000000000000000000000000000000000000000000002b5a0000000000000000000000000000000000000000000000000000056b440000000000000000000510000000150000000150000000000000000000000000000000006000000000220000000000000002856020000000000000000000a882000002a800000002800000000000000000000000000000000100800000011500000000000000542b400000000000000000000000000000000000000000000000000088980000000000002a211a000000040000000000000000000000000000000000020000000444c000000000000150ad00000005000000000000000000000000000000000000000000022260000000000000a884600000001400000040000000000000000000000000000000000000000000008000000000000000a15800000001400000054000000000000000000000000000000000000000000008000000000000000a158000000005000000150000000000000000000000000000000000000000000020000000000000002856a000000028000000280000000000000000000000000000000000000000001113000000000000054423000000000000000000000000228000000a800000000000000000000000000000000000000000001000000000000000142b0000000140000000000000000000100000000000000000000000400000008a800000000000002a15 0x13de1295117610510f720e8f0cee0b490a24090307de069c0558041202c901410000 (i%16)
private def learn₂p22 (i:ℕ) : ℕ := packedAt 0x1000400000000000000000000000000000042ccc9f400000000000000000044000000050000000010000000000008000000000000000000000980000000049980000000000002a1580000000000000000000000000000000000000000000000001012000000000000010bc0100000000000000000000000000000000000000000000000002024000000000000021780000000000000000000000000000000000000000000000000000400000000000000152842000000000000000000000000000000020000000000000000000000000000000000000000000000000000100000000000000054a1080000000000000000000008000000000a0000002a10000000000000000000000000000000000000000000400000000000000050ac00000000000000000000000000000000000000000000000000000000000000000000028420000000000000000000000000000000000000000000000000000000000000000000000000000000050840000000000000000000000000000000500000000000000000000000000000000000000000200000000002000000000000000a942100000000000000000000000000000001400000050200000000000000000000000000000000800000000008000000000000002a1580000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005084010000000000000000000000000000000000000000000000000202400000000000002084600800002000000000000000000000000000000000000000000010120000000000000104231000000000000000000000000000500000000000000000400200000000000000000000000000000022664fa000000000000000000000000000010000000000000000000005278 0x14b514111278116310440f1e0d780bd70ab2096307bd061c047f035a023500dc0000 (i%16)
private def learn₂p23 (i:ℕ) : ℕ := packedAt 0xa000000000000200000a000000000000000000000000000000000000000000000c8000000000000042f4400000000000400001400000000000000000000000000000000000000000000190000000000000085ea80000000000000000002aa00000002aa0000002a00000000000000000000000000000000000000000000400000000000000050ac00000000050000001508000000000000000000000000000000000000000000200000000000000028560000000000000000000000000000000000000000000000000000000000000000000508510000000000010000050000000000000000000000000000000000000000000006400000000000002084700000002800000000000000000000000000000000000000000009300000000000000142b000000000000000000000000000000000000000000000000000059800000000000000a15a80000000000000000000000000000000000000000100000000000000000030bd000000000000000000001500000000000000000054000000000000000000000000000000000000000002a58000000000000000a15aa000000000000000000000010000000000000000000000000000a2200400000000000000000000000000000000000000000000000000090000000000000085e0000082000000000000000000000000000000a12a53800000000000000000000000010000000000000000000000000000000000000000000000000000244c000000000000150ac00000000000000000008000000000000000000000014fb500000000000000000144000000050000000010000000000008000000000000000000000880000000049980000000000002a15 0x1360121510ca0f270dde0cc30b720a510930082f068805aa048a03dc025301990000 (i%16)
private def learn₂p24 (i:ℕ) : ℕ := packedAt 0x20000000000001000000000000000000000013d54000000000000000554000000140000005000000000000000000000000000000000000000000000a800000000000000684ea2a80000000000000aaa0000002a8a000000000000000000000000000000000000000000000000009200000002308000030000000000000000000000000000000000000000000001200000000000000484a00000000000000000000000000000000000000000000000000048000000000000042f0000000000000000000000000100000000400000000000000000000000000000000000000000004a900000000000000a15800000000000000000000000008000000020000000000000000000000000000000000000000000254800000000000005108c4000000000000000154000000000000000500000000000000000000000000000000000000000000aa00000000000000288460000000000000000000000000280000000800000000000000000000000000000000000000000009520000000000000144230000000000000000000000000100000002000000000000000000000000000000000000000000004a800000000000000a1580000000000000000000000000000000000000000000000000032000000000000010bc40000000000000000000000000000800000000000000000000088000000000000000000000021a61180000200000000000000000000000000000000000000000000032000000000000010bc0000000000002000008000000000000000000000000000000000000000000000c8000000000000042f000000018000000000000000000000000000000000000000000049900000000000000a15c0000000000000000000000000000000000440000000140800000000000005212 0x146613cb123e10cc0fb20e9d0d140b8709f6086906e005cb0484036f022501040000 (i%16)
private def learn₂p25 (i:ℕ) : ℕ := packedAt 0xa0000000100000000002280000000a80000000800000000000000000000000000000000000000000000440000000000000334270000008000000000000000000000000000000000000000000002480000009992640008000000000000000000000000000000000000000000000000001240000004cc9320000000000000000000000400000000000000000000000000000000000000000000000000092000000266499000000000000000000000008000000000000000000000000000000000000000000000000001240000004cc9328010000088000000080000000000000000000000000000000000000000000044000000000000033427000000000005000000011000100010000000000000000050000000000000000000000000008980000000000006684e000004000000000000000000000000000000000000000000000480000001332000000230800003000000000000000000000000000000000000000000000120000000000000042b400000000000000000000000000000000000000000000a0000000000000005a13c0000000000000000000000000000000000000000000444c0000000000000342700000004000000000054154000014000400140000000000000000100000000000000000800000000026600000000000009a1380000000008000000000000000000000001405100000000000000000154000000054000000140000000000000000000000000000000000000000000026000000000000019a13c00000000000000000000000000000000000000000004c4c0000000000000342740000000000000000000000000000000000020000000020000000000000005a13 0x134811ad10a70f920e310cce0b850a0e08ec07d506d005cd043803a3020801050000 (i%16)
private def learn₂p26 (i:ℕ) : ℕ := packedAt 0x1000000000000000000000000000000000000000000000000000000200000000c080000008c20000000000000000000000000000000000000000000010800000000000000000000001400000000000000000000000004d09c0000000000000200000000000000000000000000000000000000000200000004c0c0000008c2000000000000100000000000000000000000000000000000000000100000002606000000461000000000008000000000001000000000000000000000000000000000000000001000000026060000004610000000000000000000000000000000000000000000000000440000000000000014270000000000000000000000000000000000000000000020000000000000005a13800000000000008400000000000000000000000000000000009800000000000000284e000000000000021000000000000000000000000000000000026000000000000008a138000000000000000000000000000000000000000000000202000000000000000000000000000000004d4ca700000000200000000000400000000000000000000000004000000000000000000000000098000000098994e00000000100000000000800000000000000000000000008000000000000000000000000130000000131329c000000000000008000000000000000000000000000000000000920000002664995010000001000000010000000000000000000000000000000000002080000008980000000000006684e80000000000000000008a01000002a00000002000000000000000000000000000000000000000000001100000000000000cd09d000000000000000000114000000054002000040000000000000000000000000000000000000000000022000000000000019a13 0x144d1322118f105e0f310dd90cc50bc40aae0998083d06e2058704810336019b0000 (i%16)
private def learn₂p27 (i:ℕ) : ℕ := packedAt 0x100000000000000000000a000000000000000020000000000000000000000000400000000011000000000000004509c20000000000000000000000044000000000440000000000000114275000000000000000000000000008400000000000000000000000040000000000000000000000002684e0000000010002800000000200000000000000000000000000000000000000000200000004c0c0000008c200040000000000000000000000000000000000000000040000000981800000118420000000000000000000000050000000000000000000000000134270800000000000000000000005100000000011000000000000004509c000400000000484000000000000000000000001804000001098180000010000026158000a0000000090800000000000000000000000300800000213030000002000004c2b0000000080001000000000000000000000000000000000000000601000000226040000004610000000000001400000800100000000000000000000000000000000000000000100000002606000000461000000000000140000200010000000000000000000000000000000000000000010000000260600000046100000000000000000000000000000000000000000000004840000000000000000000000000000000098994e000000000000050000000048400000000000000000000000000000000109800000000000002615800000000000005000000004840000000000000000000000000000000010980000000000000261580000000000000000000000000050000000048400000000000000000000000000000000109800000000000002615 0x12f1117b109d0f520dfe0cf70c190b3b0a28091507e90695054103e602ac01700000 (i%16)
private def learn₂p28 (i:ℕ) : ℕ := packedAt 0x8000000000004000000000000000000000000000000000000001200000000011000000000000004509c400000000000000000000000000000000000000000000900000000000000000000000000098992e00000000000000000000001000000000000000000000000000000000000002408000002622020000000000008a13a800000000a00080000000000000000000000000000000000000000400000001100000000000000c509c0000000054000000005000400000000000000000000000000000000000000002000000008800000000000006284e001000000800000000000000000000000000000000000000000000000000004400000000000003142710020000014000000000000000000000000000000000000000000000000000022000000000000018a13800000000a000a00000a000800000000000000000000000000000000000000404000000011000000000000004509c0000000050005000005000400010000000000000000000000000000000000202000000008800000000000002284e2000000000800a8000000002000000000000000000000000000000000000000010000000044400000000000031427000000000800000000000010000000000000000000000000000000000000000010000000260600000046150000000014001000000000000000000000000000000000000000004000000022000000000000018a1380400000020002000000000000000000000000000000000000000000000000044000000000000031427100000000040040000000001000000000000000000000000000000000000000008a00000022200000000000018a138800000000000000000000000000000000000000000000200000000000000000000000000015325c0000000010009000000000000000000000000000000000000000000000000022000000000000018a13 0x158c14431306119410470ed60d8d0c400acf095e07e90695054803fd0288014b0000 (i%16)
private def learn₂p29 (i:ℕ) : ℕ := packedAt 0x40000000000000000000000008b8a0001000000000000000000000000000000000000000001000000026060000004610000000000000000000000000000000000000000000000000000001000000022000000000000019a138000000000000200001000080000000000000000000000000000000000000000080000001303000000230a800000000a00080000000000000000000000000000000000000000000000001100000000000000c509d000000000000800000000000000000000000000000000000000000000000008800000000000006684e00000000000000000000000000040000000000000000000000008020000000440000000000000134270000000000000080000000000000000000000000000000000000000200000004c080000008c20000000000000000000000000004000000000000000000000004802000000044000000000000013427400000000000000000000009a138000000000000000000000000800000000000000000000000000000000000000000000000002684e00000000000000000000000000280000000000000000000001342700000000000000000000000042000000000000000000000000000000000000000000000000013427000000000000000000000000000000000000000000000000000000000000000000000000029d20000000000000000000000000000000000000000000000000000000000000000000000000053a5100000000000000000000000000000000000000000000040000000000000000000000000026264b 0x11db116a10610f180dc40c770b2e09e508b6076d070005c204e903a90276013f0000 (i%16)
private def learn₂p30 (i:ℕ) : ℕ := packedAt 0x152940000000000000000000000000000000000000000000000000000294a000000004000000000000013427500000000000000015000000014000000010000000000000000000000000000000000008000000094980000000000006684e00000000000000000000000000000000000000000000000000000000000052a40000000000000000000000000000000000000000000000000a548000000000000000000000000000000000000000000000000052a400000000000000000000000000000000000000000000000000000000000a54a0000000000000000000400000000000000000000000000000000cacc9f00000001004000000000000000000000000000000000000000006800000058192e000000044000000000000013427000000000000000000000000000000000000000000800000011000000000000004d09c00000000000000000000000000000000000000000400000008808000000000002684e0000000000000000000000045c500000000000000000000000000000000000011000000000000000000000000001a00000026264b800000000100000000000040000000000000000000000000000000000000000000000000001a00000026264b 0xe1d0e0f0d2e0cc10b320a330960088b079006a5059e0531041b0306029901600000 (i%16)
private def learn₂p31 (i:ℕ) : ℕ := packedAt 0x20004000000001000000000000000000000000000000000000000000900000000612640000000000000000000000008000000002000000000000000000000000000000000000000001200000000824ca80000000000000000002a200200002aa0080002a00000000000000000000000000000000040048000000420800000000000050ac00000000000000000000002284ea90840000000000000000000002000000000000000000000000000000000000000000000000000000000014842000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000002908400000000000000000000000000000000000000000000000000000000000800000000000000050ac0000000000000000000000000000000000000000000a74800000000000000000000004d09d000000000000000001540000001400000000000000000000000000000000000000000000000000009060000000000000a684ea0000000000000000002a80000000a000000008000000000000000000000000000000000000000000054000000000000001342700000000000000000000000000000000000000000000800000000000000000000004d09d0000000000000000001540000000500000000400000000000000000000000000000000000000000002a0000000000000019a1380000000000000000000000000000000000000000008000000010400000000000002684e00000000000000000000000000000000000000000000000000041000000000000029a13 0x1222110f0fa80e070d9a0d870c320a8b094f08940827069204f503d7023c011e0000 (i%16)
private def learn₂p32 (i:ℕ) : ℕ := packedAt 0x2000000000000000000000000000000000000000000000000000000000000000000142d00000000000000000000000000000000000000000000000000000000000000000000a168a13aa138000010002000000000000000000000000000000000000000001200000000824c8000040002000000000000000000000000000000000000000001200000000824c8000000002000040000000000000000000000000000000000001200000000824c8000004002000000000000000000000000000000000000000001200000000824ca800000008000000000000000000000000000000000000000000004000000000000001542700000020040000000000000000000000000000000000000000024000000010499000000000400002000000000000000000000000000000000000240000000104990000000005500000005000000000000000000000000000000000000000000002000000000000000aa13800010000000004000000000000000000000000000000000000000002400000001049944000000015400000014000000000000000000000000000000000000000000008000000000000002a84e000010000000004000000000000000000000000000000000000000002400000001849900000000000000000000000008000000002000000000000000000000000000000000000000001200000000c24c 0xfca0eb10d940d840d740c700b6c0a680964083d0739063504e803d1028201690000 (i%16)
private def learn₂p33 (i:ℕ) : ℕ := packedAt 0x280000000020000000000000000000000000000000000000000012000000100200000000000005423400000000100000000000000000000000000000000000000000090000000a0100000000000002a118000000000000000000000000000000000000000000000000002293200010000000000000000000000000000000000000000000000000002400000009a49910010000100004000000000000000000000000000000000000000002400000020040000000000000a8460000000000000000000000000000000000000000000000000000000000000a13d09c000000000000000684e000000000000000000000001a13800000008000000000000000684e000000022000000000000001a138000000000000000000000000000000000000080000000000000000000000000000000000002400000002100000011840000000000000000000000000000000000001000000000000000000000000000000000000048000000042000000230900000000000000000000000684e400000010000000000000001a138000000000000000000000000000000000000000000010000000000000001a13 0xd3e0bfd0abc09de08c9077a0678066b061e05b0054204d4035701dc016e01000000 (i%16)
private def learn₂p34 (i:ℕ) : ℕ := packedAt 0x400000000000000000000000000000000000000000000000000000080000000000000142b0000000000000000000000000000000142000005400000000000000000000000000000000000000000000850000000000000085e00000000000000050ac800000000000000a158000000000000000000000000000000000000000000000000004000000000000000a1580000000000000000000000000000000000000000000000000001000000000000000285684ea138000000000000000000000000000000000000000000000000000000000000000000014274842800000022528000000000000000284e000000000000000000000000000000000000000000000000008000000000000000284e0000000000000000000000000000000000000000000000000000000000008000000000000000284e0000000000000000a42100000000010000000000000000000000000000000000000000009000000080100000000000002a11 0xb3b0a19087a082f07e406cc05ae05a2059404750466043803ea02d2019201410000 (i%16)
private def learn₂p35 (i:ℕ) : ℕ := packedAt 0x440000000000000000000000000000000200000000000000000011000000000000a9174000000000000000000000000000000000000000000000000000000000000042b00000000000000000000000000000000000000000000000000000000000001020e800000000000000000000000000000000000002000000000000000000000008560000000000000000000000000000000000000100000000000000000000000215a15800000000000000000000000000000000000000000000000000000000000050ac000000000000000000000000000000000000000000000080000000000000285600000002000000000000000000000000000000000000000000000040000000000000142b000000000000000000000000000000000000000000000000000000000000142b0000000000000028560000000000000000000000000000000000000000000000400000000000000a15800000000000000000000000000000000000000000000000000000400000000000000a1580000002800000000000000000000000000000000000000000000080000000000000142b40000000000000000000540000000011408000014000000000000000000000000000000000000000000000000000000000000a158000000280000000000000000000000000000000000000000000008000000000000014210 0xfa30e8b0d890c800b7e0a7c0a70096f086e074d064d0606050403e402c501240000 (i%16)
private def learn₂p36 (i:ℕ) : ℕ := packedAt 0x4000000040000010000000000000000000044000000001000000100000000a000000000000088846000000000000000000000000000000000000000000000000000000000000040000000000000000000000008884682802a80a0000000000000aa2aa88000aa0000000200000000000000100000000000000000004100200000451000000000000011108d05001500000000000000015450000001540000000400000000000000000000000000000000008a000000008a00000002a0000022211800000000010000000100000040000000000000000000000000000000000000400000002800000000000022211800000000000000000000000000000000000000000000000000000000000100000000000000000000000022211aa028000000000000000a80000002800000008000000000000000000000000000000000105000000011440000000000000444235405000000000000000150000000500000001000000000200000000000000000000000020a00000002288000000000000088846a8000000000000000002a0000000a00000002000000000400000000000000000000000041000000004d0000000000000011108c00000000000000000000000000000000000000000000000000000000004022000000050000000010000011108c40000000000000000015000000050000000100000000008000000000000000000000002080000000268000000000000008884600000000004000000000000000000000004500000000000000000000000011108d00000001400000004000000000a00000000000000000000000082000000009a00000000000000222118000000000000000000000000000000000000000000000000000000000082000000002a00000002a00000222118000000000000000000000000400000000000000000000000000000000040000000000000000000000000222118000000000000000000000000000000000a00000000000000000000000082000000002000000002a0000022211 0x173315f6148a12db112c0fc40e5c0cc10b26098b0823068a0583043802d001680000 (i%16)
private def learn₂p37 (i:ℕ) : ℕ := packedAt 0x8aa8a800000000000000a2aa000000a2a00000200800000000000000000000000000000005000000000401000000000000011108c55400000000000000005150000000514000001000000000000000000000000000000000028000000002080000000000000088846a8000000000000000002a0000000a0000000200000000000000000000000000000000005000000000450000000000000011108c000000000000000000000000000000000044000000001000000100000000a000000000000088846000000000000000000000000000000000022000000000800200080000000500000000000004442300000000000000000000000000000000001100000000040002004000008028000000000000222118a0280a0000100000000aaa2000008000000080000000000000000000000000000000001040080000114500000000000004442300000000000000000000000000000000008000000000000000000000000044423000000000000000000000000000000000000000000000000000000000022000000000a3a000000000000008000000000000000000022000000000800000080000000500000000000004442300000000000000000000000000000000000800000000000000000000000018884620000000000000000040000000000000000000000000000000040b000000000008928280aa88a0280000000000aa2aa88000aa2a00000200000000000000000000000000000000004400200000401400000000008011108d05005501405000000000015455510001545000000400000000200000000000000000000000008200400002822800000000000022211a0a00aa0280a00000000002a8aaa20002a8000000080000000000000000000000000000000001040080000114500000000000004442350000000000000000440000000000000000000000000000000004000000000000000000000000022211 0x1600145f12be11230fe60ea90d6c0bd10acd09ae0871076a065a04ab02fc014d0000 (i%16)
private def learn₂p38 (i:ℕ) : ℕ := packedAt 0x4000000000000000000000000000000000000000000000480000000500000000000004442300000000000000000000000000000000000000000000001200000001400000000000011108d000000000000000000000000000000000008000000000000000000000889074000008000000000000000000000000000000000000000000000900000000a00000000000008884600000000000000000000000000001000000000000000000000000028124400000200000000000000000000000000000000000000000000000000002000000000000000110ac00000000000000000000000000000000000000000000002200000000000000022e8000000000000000000000000000000000000000000000088000100500000000000004442341401540501400000000005555540000550500000100400000000000000000000000000000000000100000208a00000000000008884682802a80a0280000000000aaaaa80000aa2a00000200800000000000000000000000000000000000200000411400000000000011108d05005501405000000000015555500001545000000400000000000000000000000000000000002000400000822800000000000022211a0a00aa0280a00000000002aaaaa00002a8a8000008020000000010000000000000000000000020008000010450000000000000444230000020000000000000000000000000000000000000000000000000000401400000000000011108c4000000001000000100000000a00000000000008884682802a80a0280000000000aa2aa80000aa0000000200000000000000000000000000000000004500000000451400000000000011108c40000000100000000080000000000000000000000000000000081600000000000000215 0x145f1339120f11130fd60ee70dab0ca00b7909ca081b066c04bd037f02ce011f0000 (i%16)
private def learn₂p39 (i:ℕ) : ℕ := packedAt 0x5100000000015400000000540000050000000000000000000000000000000000100000000a00000000000008884680000000800000000000000000000000000000000000000000001002000000000000044423000000000000000000000000000000000000000000000000000152840000000000000000000000000000000000000000000000000000000000000000000000000000000000a50800000000000000000000000000a0000000200000000000000000000000000000000000000000000410800000000000011108c00000000000000000000000000500400001000000000000000000000000000000000000000000002084000000000000088846000000000000000000000000000000000000000000000000000000000000000528400000000000000000000000000000000000000000000000000000000000000000000000000000000000294200000000000000000000000000000000000000000000000000000000000000014a100000000000000000001400000005000000010000000000000000000000000000000000040000000020840000000000000888460000000000000000000000000000000000000000000000000000052840000000000000000000000000000010000000000000004000000000000000000000000010000000028250000000000000242d1000000000000000000000000000000000000000000000000028050000000000000242d000002000000000000000000000000000000000000000000000008000000000000000000000442b00000200000000000000000000000000000000000000000000000000002000000000000000110ac0000000000000000000000000000000000000000000002400000402800000000000022211 0x143712ca11a110c30f6c0dd70c420b3709da08cd0732064f04b9039d026101270000 (i%16)
private def learn₂p40 (i:ℕ) : ℕ := packedAt 0x8000000000000000000000000000000000000015850000000000200000000000000000000000000000000000000000000000000008000000000000000000000000004c40082a82800a8000000000000000aa28880000aa0000000200000000000000000000000000000000004522000000450000000000000011108d05001500000000000000015455500001540000000400000000000000200000000000000000008a400000008a0000000000000022211800000000000000000000000000100000000000000000000000000000000000000000000000000000400000000000011108d050055000000000000000154551000015400000004000000000000000000000000000000000082002000008a0400000000000022211a0a00aa0000000000000002a8aa200002a8004000080000000000000000000000000000000001040040000114080000000000004442300000000000000000000000000000000000000000000000000000000000000000000000000000000224e800000000000000000014000000000000000000000000000000000000000000000000000200000002800000000000022211800000000000000005000000000000000000000000000000000000000000000000000080000000a000000000000088846000000000000000000a288840000a0000000200000000000000000000000000000000004100000000451400000000000011108c0000000000000000000000000000000000000000000000000000000000000000000044230000000000000000005150000000500400001000000000000000000000000000000000020000000002188000000000000088846a80000000000000000028a00000002800000008000000000000000000000000000000000100000000014c00000000000000444234000000000000000000450000000140000000400000000000000000000000000000000009000000000a600000000000000222118800880000000000000000000000000000000400000000000000220022000000000000022e 0x179416ed156613b71208107b0ecc0d1d0bcc0a4008be07230601046602c501280000 (i%16)
private def learn₂p41 (i:ℕ) : ℕ := packedAt 0x200800000000000000000000000000100000000000000000000000000000000000000001200000000400000000000011108c01000000000000000000000000000800000000000000000000000000000000000000002400000000800000000000022211802000028000000000000000000000a00000000000000000000000200000000000000004000000001000000000000044507c8800000010000000000000444234000000000000000000000000000000000000000000000100000000000000000000000000888000000000022283e000000000000000000000000000000020000000000000888460000000000000000000000000000000000000000000000000000200000000000004442300000000000000000000000000000005000000000000044483a2000000000000000000229ce0000000000000000000000000000000000000000000000000000080000000000002221180000000000020000000000000000000000000000000000000000000008884600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110004010000804000040000000000000000000000000000000000000000400000000000a02800000000000262211a0a00aa0000000000000002a8aa200002a80200000800000000000000000000000000000000010400000001040800000000000044423414015405000000000000055155400005500000001000000000000000000000000000000000020800000002282000000000000088846000000000010000014000000000000000000000000000000000000000000000400008000000222800000000000262211 0x137a11ef10640ed70e690cfa0c320b150a4a09ea08cc07d2063504e0033101820000 (i%16)
private def learn₂p42 (i:ℕ) : ℕ := packedAt 0x505001500000000000000015455500001540000000400000000000000000000000000000000000002100000820800000000000022211a0a00aa0000000000000002a8aaa00002a8000000080000000000000000000000000000000000000420000104100000000000004442341400540000000000000005515540000550000000100000000000000000000000000000000000001840000208200000000000008884682802a8000000000000000aa2aa80000aa0000000200000000000000000000000000000000000103000000410400000000000011108c000000000000000000000882000000000000000000000000000020000000000000000000013480000013400000000000001120e800005501000000000000000055100000140000000400000000000000000000000000000000008000000000820800000000000022211a0a00aa0200000000000002a8aaa00002a800000008000000000000000000000000000000000000000000010410000000000000444234140054000000000000000551454000055000000010000000000000000800000000000000000228180000022800000000000000888468a82000000000000200000000000000000000000000000000002000000000010400000000000011108c000020000000000000000000000000000000000000000000000000000400400000000000011108d050055014000000000000154555000015400000004000000000000000000000000000000000080000000008a0800000000000022211800000000000022283e0000000000000000000000000000000000000000000000000000000000000800000000000022211a000000000000000000000000000000000000000000000000000000000000400000000000011141f000000000000000000000000000000000000000000000000000008000000000000000000000442b004000040000000000000000000000000000000000000000000000000000000000000008800000002000000000000088a0f 0x172f158013d1122210730ed40d240b7509c6087b073f05900546040802c9018d0000 (i%16)
private def learn₂p43 (i:ℕ) : ℕ := packedAt 0x200000000000000000001504000000000000000000000000000000000000000000000000000000000020800000000000022211800000000000000000000541000000000000000000000000000000000000000000000000000000000008200000000000008884615040000000000000000000000000000000000000000000000000000000000208000000000000222118150400000000000000000000000000000000000000000000000000000000002080000000000002221188000000000000000882aa800000a0000000200000000000000000000000000000000000000000000410400000000000011108c00000000000000000000a82000000000000000000000000000000000000000000000000000000000010400000000000011108d400000000000000045155400000500000001000000000000000000000000000000000000000000002082000000000000088846a000000000000000100aaa000002800000008000000000000000000000000000000000000000000010410000000000000444235000000000000000000555000009400000004000000000000000000000000000000000000000000008208000000000000222118001500000000000000000055500000140000000400000000000000000000000000000000000000000000820800000000000022211a8000000000000000002aa800010a0000000200000000000000000000000000000000000000000000410400000000000011108c00002a000000000000000000aaa00000280000000800000000000000000000000000000000000000000001041000000000000044423000002a000000000000000000aaa0000028000000080000000000000000000000000000000000000000000104100000000000004442341400540000000000000005515540000550000000100000000000000000000000000000000000000000000208200000000000008884682800a8000000000000000aa2aa80000aa0000000200000000000000000000000000000000000000100000410400000000000011108c000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000011120e 0x195e17c8162e14e4139811ff10670ece0d350b9c09f4085b06ad04fd034e019f0000 (i%16)
private def learn₂p44 (i:ℕ) : ℕ := packedAt 0x800002008000000000000000000000001000000000000000000008001480000000000442b000008000000000000000000000000004000000000000000000000005246800000000000004000000040000000000000000000000000000000000000000000040000000000000002215800000000000010000000100000000000000000000000000000000000000000000100000000000000008856000000000000000000000000000000000000000000000000000000020000000000000888460000000000000000000000000000000000000000000000000000400400000000000011108c000000000000000000000000000000000000000000000000000000000010800000000000022211800000000000100000000000000000000000000000000000000000000000100000000000004442340000000400000000000000000000000000000000000000000000820800000000000022211800000000000000000000000000000000500000001000000000000000000000000000000000000000000002082000000000000088846000000000000000000000000000000000500000001000000000000000000000000000000000000000000002082000000000000088846000000140000000400000000000000000000000000000000000000000000820800000000000022211800000500000001000000000000000000000000000000000000000000002082000000000000088846a000002800000008000000000000000000000000000000000000000000010410000000000000444235400000500000001000000000000000000000000000000000000000000002082000000000000088846005500000140000000400000000000000000000000000000000000000000000820800000000000022211 0x147c13591268110c0fb20e8a0d630c280aed09c408160666052003de029901520000 (i%16)
private def learn₂p45 (i:ℕ) : ℕ := packedAt 0x10000000000000000000000000000000050000000011529c000000000800000000000000008000014ff0000000001400000000000000000000014fb400000000000000002000000000000000000000000000000000019a55aa000000000000000000000000010000000000000000000000000200000000000000000236800000000000000000000000000008000000000100000002000000000000000000000000000000000114ab0000000000000001000000000040100000008000000000000000000000000000000000000000008694e000000000000000000000000000000000000000000000000000000000000000000005084442300000000000000044423000000000000000000000000000000000000000000000000000000000000000000222118000000000000000000000000000000000000000000000000000000000000000000002221180000000000000000000000000000000000000000000000000000800000000000000044423000000000000000000000000000000000000000000000000000000000000044423400000004000000000000000000000000000000000000000000004000000000000000222118004000000040000000000000000000000000000000000000000000040000000000000002215 0xed50e1b0d8d0cfd0c180af00999084e072f071d06cd05b004880361025901300000 (i%16)
private def learn₂p46 (i:ℕ) : ℕ := packedAt 0x100000000000000000000000000000000000000000000000000000000000141d81c0000000000000000000000000000000000000000004af000000000000000000000000000000000000000000025480000000000000000000000000000000000000000008000000000000000084e000000000000000000000000000000000a7b8000000000000000000000000000000000000000000000000000000200004250000000000000000000000000000000000000000000225080000000000000000000000000000000028000000002558000000000000000000000000000000002800000000a558000000000000000000000000000000002800000000a94e00000000000000000000000000000000000000000020200000000000000213800000000000000000000000000000000000000000004000000000000000508400000000000000000000000000000000140000000054000000000000000284200000000000000000000000000000000000000000000200000000000000150740000000000000000000000000000000014000000005424e 0xc950b990b8f0ad90a2009260894079906dc0624056c04b203b802bb01be00bf0000 (i%16)
private def learn₂p47 (i:ℕ) : ℕ := packedAt 0x800000000000000000a0000000000000000000000000020000000000000000000000014800000013424e8040000000000000000000000000000000000000000000000000001000000000849d000000000000000000080000000000000000000000000000000000000000000000000002000000001093a000000000000000000040000000000000000000000000000000000000000000000000001000000000849d0000000000000000000000000000000000000000000000000000640000000000000085f0000000000000000212800000000000000000000000000000000000000000004ad0000000000000000000000000000000000000000000100000000000000021094000000000000000000000000000000000000000000000000000000000000284b00000000000000022128000000000000000000000000000000000000000000030000000000000002108c0000000000000000000000000000000000000000000180000000000000018847000000000000000028420000000000000000000000000000000000000000000000000000000000088320000000000000000000000000000000000000000000000000000000000008842000000000000000000000000000000000000000000000000000000000000a10 0xec40d740c650b1209bd08a208540799069b059a054c044b034a02fa01fe00fe0000 (i%16)
private def learn₂p48 (i:ℕ) : ℕ := packedAt 0x8a2a000000000000000002a00000000a800000002000000000000000000000000000000000050000000014c0000000000000050bc0000000000000000000000000000000000000000000000000005000000000849d0000000000000000000000000000000000000000000800000002600000000000000285e0000000040000000000000000000000000000000000000000002000000009800000000000000a17880a000000000000000002a00000000a800000000000000000000000000000000000000000050000000094c00000023880000000000000000a800000000000000000000000000430000000000000000000000014f74000000010000000000000000000000000000000000000000000900000002600000000000000085e8000000000000000000000000008000000000000000000000001200000004d0000000000000010bc1400000001000000000000000a20000000000000000000000009200000026a492e010000000000000000000000000510000000000000000000000014f745000000004000000000000002880400000000000000000000024800000002924ba8000000000000a0000000000000000000000000000000020000000000000000053ad000000000000000000000000000020000000000000000000000069ee00000000000000000000000000000015a500000000008000000000000000000000000001440000000000000000000000053dc20000000000000000000000000000000000000000000000000000800000000424e 0x11a810070f010de60ca80b280a0108c20783067a05990490037f029e0215010b0000 (i%16)
private def learn₂p49 (i:ℕ) : ℕ := packedAt 0xa400000000080000000000000094290000000000000000ca84a00000000088000000000000009429000000000000001242754000000000000000000000000000800000000000000000000001000000000000000000469000000000000000000000000000000000000000000084000000020000000a148a800000000000000a2a000000000000000000000000050000000000000000000000014000000001100000000000000028520000000000000000000000000000000000000000000100000000000000124275000000000000000000000000000000000000000000000400000000000000000000000000000000880000000000000014290000000000000000000000000000000000000000000200000000000000006484e00000000000000000000000000000000000000000041000000000000001242795700000000000000042f0000000000000000000000000000000000000000000000000000600000000000000085e0000000000000000000000000000000000000000000000000000c0000000000000050bc0000000000000000000000000000000000000000000000000009800000000000000a17 0xd6c0cf50ca20c2d0be10ab909bc082e073105a504a203a5039a03510236011b0000 (i%16)
private def learn₂p50 (i:ℕ) : ℕ := packedAt 0x2a00000000000000000000000000010000000000000000000000427aaa00000000000000022a000000000000000000000000000800000000000000008000004ff1000000000000000000000000000220000000000000000000000227ba000000000000000000000000266247aa0000000000000000000000000028000000000000000002000000000000000000000000000000000104ab0000000000000012852a802200000000000000000000004000010000000000000000000080088000000000000008caa000000000000000000002800000000000000000000000800000000000000000000000014c971000000000000000000000000000080000000000000000000000440000000000002a465000000000000000000000000000000000050800000004000000000000000a1480000000000000000000400000000000000000000000000000120000000000000028520000000000800000000000000942900000000000000000000000295095400000000100000000000000128520000000000000000000000295107400000000000001000000000000000000004276 0xcf60c180af50a140998084107f606ca0599047d0380026a01f50183010e009b0000 (i%16)
private def learn₂p51 (i:ℕ) : ℕ := packedAt 0x20000000000000004212a613880000004028000000000000000000000000000000000000000080000000042000000000000042f000000000000000000000000000000000000000000025695600000000000000000000000000000000000000000004ab000000000000000000000000000000000000000000020000000000000010c5000000000000000000000000000080000000000000000000000927b8200000000000000000000000000000000000000000004000000000000002188000000000000000000000000000000000000000000004000000000000002109c00000000000000000000000000000000000000000000000000000000000221480000000000000010b40000000000000000000000000000000000000000000080000000000000010b40000000000000000000000000000000000000000000000000000000000285a00000000000000242d40000000000000000000000000000a000000000000000000000a7b 0xb460af80ae809ad08f408ea0831073b065c0560045f03600317021b012200d90000 (i%16)
private def learn₂p52 (i:ℕ) : ℕ := packedAt 0x200000008020080000000000000000000009fe000000000080400000000000000000000000000000000000000011a4000000000100800000000000000000000013dc4290bc85208460000000000000000000000000000000000000000000000000000000000042f5000000000015540000000000000000000000000000008040000000000000000400000000000000000465000000000000000000000000000000000000000000200000000000000012178425000000000000000000000000000000000000000000000000000000000001084a90a40000000000000000000000000000000000000000000000000000000000285e0000000000000000000000000000000000000000040000000000000000142f00000000000000000000000000000000010000000000000000000000000a17 0x98e08fa081b07830775076b075e074e06550501040803f902fa02eb01f200f90000 (i%16)
private def learn₂p53 (i:ℕ) : ℕ := packedAt 0x200000000000000000000000000000000000800000000a20000000000000008560000000000000000000000006a00000002808000000000000010c4000000000000000000000000d40000000511000000000000002188000000000000000000000000000000000000000000000000000000000000000000000000000000431000000000000000000000000000000000000000000000000000000400000000510000000000000021880000000000000000000000000000000000000000000000000000000000000000000000000800000000a200000000000000431000000000000000000000000000000000000000000000000000000000000000000000000040000000051000000000000002188000000000000000000000000220000000280000000000000002198000000000000000000000000220000000280000000000000002215aa80000000000000000000000005400000000000000000000000044000000000000000008db9de7e0000000200000000000000000184e20000000000000000000000000144000000000000000000000004400000000000000000234800000000000000000000000000000000000000000000000000000000000309c0000000000000000000000000000000000000000000810000000234 0xed60dd60cff0c280ae109980801066c059404b8038e0384037a030601dc00df0000 (i%16)
private def learn₂p54 (i:ℕ) : ℕ := packedAt 0x1000000000000000000000000000000000000000000000000000000000022158000000000000000000000000880000000a220000000000000086600000002a000000000000000210a44000000000000000000000000280000000000000000000000002215800000000000000000000000000000000010000000150000000000000001085200000000000000000000000034000000000000000000000000110ac00000000000000000000000011000000014b7000000000000000000000000000000000000000000000000000000000000000000021890000000000000000000000002200000000888000000000000010c40000000000000000000000000000000000000000000080000000000000008620000000000000000000000000400000001510000000000000021890000000000000000000000002a00000000888000000000000010c40000000000000000008000000004000000000000000010000001a7f8800000000000000000000000100000000144000000000000008628000000000000000000000000880000000a0253800000000000000000000000000000000088000000000000000000000000218 0xd7d0c840bae0b3b0a5c095e088307ed06d405fb04fe0428034f0270019a00fc0000 (i%16)
private def learn₂p55 (i:ℕ) : ℕ := packedAt 0x100000001000000000000000010cc00000004008000000000000043300000001404000000000000010cc000000050100000000000000442b1000000012ed00000000000000010c62000000022598800000008000000000000000086620000000200800000000000002198000000000000000442b1000000014b700000000000000000000000011000000014b7100000001400000000000000010cc0000000000000221580000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000866000000020400000000000000219 0x71906ab063d05cf055d052f04e304b0043e03cc037d034d02b902470200006e0000 (i%16)
private def learn₂p56 (i:ℕ) : ℕ := packedAt 0x100000000000000004333ec00000000000000000000000043300000000400000000000000010cc00000000000002198800000002020000000000000086600000000000000000000000000000000000000000000000000000000000010a400000000000000000000000000000000088000000022200000000000000866200000000000000000000000000000000000000000000000000000004000084a0000000000000000000000000000000008800000002a200000000000000866000000000000000000000000000000004000000000000000000000004c3210800000000000000000000000000000000000000000500000000000000010a12800000000000002215880000000000000000000a0000000000000000000000001200000000000000000000000132123c00000004bb000000000000000000000000000000000004000000000000000000000000218 0xa710a250a1b09ad093f08fc088a078b06920592049a03a002a4025c012700fd0000 (i%16)
private def learn₂p57 (i:ℕ) : ℕ := packedAt 0x25896e000000000000000000000000000000000000000000025b8425694b0d84f27d5614c1725ca61980000000000000219 0x18a0180017600bc00b200a8009e0094008a00800076006c00620058004e00440000 (i%16)
private def learn₂p58 (i:ℕ) : ℕ := packedAt 0x2e3b7e5c9fa809eb2de672fd3f4dd4f51c230b 0x960096008c00820078006e0064005a00500046003c00320028001e0014000a0000 (i%16)
def learn₂ (i:ℕ) : ℕ := if i<464 then (if i<224 then (if i<112 then (if i<48 then (if i<16 then (learn₂p0 i) else (if i<32 then (learn₂p1 i) else (learn₂p2 i))) else (if i<80 then (if i<64 then (learn₂p3 i) else (learn₂p4 i)) else (if i<96 then (learn₂p5 i) else (learn₂p6 i)))) else (if i<160 then (if i<128 then (learn₂p7 i) else (if i<144 then (learn₂p8 i) else (learn₂p9 i))) else (if i<192 then (if i<176 then (learn₂p10 i) else (learn₂p11 i)) else (if i<208 then (learn₂p12 i) else (learn₂p13 i))))) else (if i<336 then (if i<272 then (if i<240 then (learn₂p14 i) else (if i<256 then (learn₂p15 i) else (learn₂p16 i))) else (if i<304 then (if i<288 then (learn₂p17 i) else (learn₂p18 i)) else (if i<320 then (learn₂p19 i) else (learn₂p20 i)))) else (if i<400 then (if i<368 then (if i<352 then (learn₂p21 i) else (learn₂p22 i)) else (if i<384 then (learn₂p23 i) else (learn₂p24 i))) else (if i<432 then (if i<416 then (learn₂p25 i) else (learn₂p26 i)) else (if i<448 then (learn₂p27 i) else (learn₂p28 i)))))) else (if i<704 then (if i<576 then (if i<512 then (if i<480 then (learn₂p29 i) else (if i<496 then (learn₂p30 i) else (learn₂p31 i))) else (if i<544 then (if i<528 then (learn₂p32 i) else (learn₂p33 i)) else (if i<560 then (learn₂p34 i) else (learn₂p35 i)))) else (if i<640 then (if i<608 then (if i<592 then (learn₂p36 i) else (learn₂p37 i)) else (if i<624 then (learn₂p38 i) else (learn₂p39 i))) else (if i<672 then (if i<656 then (learn₂p40 i) else (learn₂p41 i)) else (if i<688 then (learn₂p42 i) else (learn₂p43 i))))) else (if i<816 then (if i<752 then (if i<720 then (learn₂p44 i) else (if i<736 then (learn₂p45 i) else (learn₂p46 i))) else (if i<784 then (if i<768 then (learn₂p47 i) else (learn₂p48 i)) else (if i<800 then (learn₂p49 i) else (learn₂p50 i)))) else (if i<880 then (if i<848 then (if i<832 then (learn₂p51 i) else (learn₂p52 i)) else (if i<864 then (learn₂p53 i) else (learn₂p54 i))) else (if i<912 then (if i<896 then (learn₂p55 i) else (learn₂p56 i)) else (if i<928 then (learn₂p57 i) else (learn₂p58 i))))))
private def hints₂p0 (i:ℕ) : ℕ := packedAt 0xcd0681a03c0d8e02187210d3ac2e8603642f0b6100d10a069d14c51fe2d7031ba8493542ca4286627051ef808c841c8be8e62b325a831a3c1509a0d4ba1355c8561c042cdc2124a0e8230731cc0d8920280e858190898c0448682287b0b63bc2bd34c628a62919302ba992504c4a3a609433138d981dccc8e9262d6f32117802b305059e0ee540f1939849583ca52614500ee919839383b64260d253082980d84034606374180d90bc2dc249aa16520140d3828f7c1c8bf0e6558932b3c42e42b9d8444e82214b317a498b51cc542f0b7ba1b03f0c81e9f0458f422a7985aa698c52cc5e9e6330b2908696085034e0e45e100d1828f7c0c6eaa4e30906f85f9703e5002372f578a9b9b638521aa0f45508a2b07b1603dcfc2345b02c3e81f8683743207a7a8596c0a4b68529af0a99332dc8996664cc32a65d4f319a898d42ca433a6630d2c195985cb4c32526143500a27076484c18a41dc5101a0a069c1c8bc201a3051ef818dd48cc1e4a611767e1193e08bd34c629e6335131aa22c103140808a8408ce15268104358552c04bd5e0c4ac12e26033aac184901cc4a0e72207210838cd820c6e107238091c40d01819b15300b298ececc3e7a621193027f8b5c5cc06826253f3118e98250cc4e366076931fb59904e4c3a023216731e178029383b64260c500ee2980d84034606374180d98493542ca40281a7051ef83917c8cc1e4a6119a0d85607c2abfc5ae02321c5882764c06761858920398941ce7210b238091c40d2fa64f453148c981474c12866271b303bf9941383b64260c540f1939849403b8a6036100d1818dd060366124d50b2900a069c147be0e45f233079298403e15769341a984272ba135608582e42b0e02166e109250741cc0d8920297d327a298a5d4c92f664d413128e98250cc4e3660773323178029383b64260c540f1939849403b8a6036100d1818dd060366124d50b2900a069c147be0e45f23307929845d1f8468f422e7d03f0d06e86614e9a6314f319a898d42ca421a582140d3839178403460a3df031baa6264169b2176dd08b2a03e9f045cfc2325a0f72b07a9ec0f4b20579332da698c53cc66a26352b30b9698665ccbe526143500a27076484c18a41dc5101a0a069c1c8bc201a3051ef818dd48cc1e4a611b4a01dc540f193984c8cc1e4a6104a0e98e9821383ae3e60b2130684f0a06940c6ea0e45f3a60836244154a00dcc613c628591383ac941d278111390871583cca41e24d0183b81d8c401caa046140d70c06cd14c523e60b21306c0994decc9a9662f0926a85948474c124e6130722fa498b4a4c2a4a6117f328c0440e2200709203a08c1ce430102580a8303381c19f153008c9813fc5ae2e603031ba8e98246cc0e02321132ff 0x1f201d891927189d175a13b513440ef90e9d0bf608fb07b8053904600415016c0000 (i%16)
private def hints₂p1 (i:ℕ) : ℕ := packedAt 0xe2500ee6209dc8d14efef052d5485429c180c81fe6610035082110388801c2690322180811839c901d00c0ce9cafec54da632753173859eb11c4cd3ec6f511b3cdb0bcfc74fcdfe30d375ec9db0812c0561ac901d11d3d6060673fc5be367644b015a8330801a8410c81fea812d538301103888c1c6400e13481910c0422667b635128b9b8d854462a6ab1938e9ba7fced4067aa0539500e2500ee2a078b104ee468a3274aabfbae4951de5aa90a8538301903fcd42086610022071100384d2064430100606711839c901d0ff1849eb10c64e9e2669b3b60e9cafdd8de9a2a6cf6179d8d9e5cdd7aa3a7e3173832580ae11fc30ec2f10a25282fd81de18ef30a32e07d9803f10c24a801214109117c0bd0a09933199aa8d0eb46c65e32f31198ab8d16a46bea6341591a32b07aca4650b41ef2b1952c815cb465ac0ef0c7798519703ecc01f88612540090a08488be05e8504c0d4321683dcac1eb3341baaa13d4d09aae8512d41897a0cd650a7528753141a95a0beb50f25282c5902bb0bc42894a0be5c0a57b0b1bd43290424684125440939883f8bc1f88704d3081807037c7201bab43bd8a1f4c506ab6855af43daca14c34b266a83957428aaa13ccd06cac1eb294162d07bcad05cb20572d41885f0a069046188250bd0722f818dd42ce2160730b16009bb084e17e0d6761113a0881283a8a41da500ec260759e40f09e032180d80ac30df4c9e8a6291f305909835ecc9a9662f0b2908e98250cc4e4660f0722fa498b5e4c964a611473150b43057af84e0ec21e7010c39086b0e148ea0744d018298115f4c9e8a62943313a498b5e4c968e62a16860879dc0eceb0a01085f0a06b860366124d50b29083917d24c5a8e62b50a812d350821903fccc200a7851348190303381c19f3b30f9e9883fc5ae063756131b9c9874046426e61b6331c 0x151014b5128a120010540fba0d8f0d720d3f0b3e09280694061f038b0248016d0000 (i%16)
private def hints₂p2 (i:ℕ) : ℕ := packedAt 0xc0a612d22071100384901d0460e754c3d90c0409602a6987c0606703833c230fb15359899a0d8d6c6c2b611d3da7f8b9c6ceda2e6eb011998c9c940c6de924e8540f1939371403ba464d84e0ed298114849ae4a4db5ebe1383b0879c0430e421ac306d250749d40e89a03053022beaddc7cffe3a7b5475aabcadd5156a686b5190303381c19f011997f8b9d4198400d4208640ff9bad14e568e76b493d5a5ac27c171ca1225908d74862210488b81f65a0fa4182497c0b8381be520f10d82415408c310f3a328a939374c49ce1e4d50d269cf94455c9ee5e4e52d271aa93d4949b650d06ec349a6164d10ee580f52a0799483ca4e4dd2326c94937e3ca02564e18d27fc8940c849ae4a4dbe49c1d8510836a0a434851f291024e8412541091a1e1d47201b59764aab9dd5dd3eb6eed224282620e1d0350e55573b8697155dd3ec0f30a3778639803f0b81f6801212f817a14130b41ee1a87297ab3eb5e825aa713158b99ad8434b8aa6e4a5902b96aa42a14e0c0640ff330801a8410881c4400e13481910c0401819c460e7240743fc6162669d6179e8a9b44e57f276c1f637a79eb114dd7ae327511b3cc8e9f945ce109602bbe1d04de2500ee2a078b104ee468a5274ab92a3c5fddc38b104eca01dd7f4e991a21f1280773104ee468c37f818 0xf040c5d0b050aab0a1007fa07b506ad0652058d05060398016d015000b6005b0000 (i%16)
private def hints₂p3 (i:ℕ) : ℕ := packedAt 0x609f046cfc2388188da893c54c9e69e4ef7c7a1193e08d1fc30ea24f14d276a793bcb552150a70603207f998400d4208440e2200709a40c886020480e82307383033a266a11b3ce9eb1258dea62e70d375ed8e9fa464eaa72bfd3b6118a9b53fc61f582c04b01579851d861d41c19e600fc2e07dbbc31d002428612541091406198be05e8504c0d4459683dcb20570f85f818dbcc49cea64f35927c9593855c9ef5251b2f27296938d549ea670fc560f2298114a49be4a4db1c3fc3fa0621dd42b4e61597484d97619deb115af88989c40c6e21a3310b178848ac419783f104246841253081821e1c8381bf0f85fd194540c6dea24f131273a993cd649f21a4d35727bd5947684a26aa4f5a528b99c3f1503c64e4dc3900d4f82e1583c8a60452926f929369683dcb20572d271959384b54e0c0a90a8240741903fccc2006a10423071910388801c24b0153481910c0401c19e0c0ce8e9f2c046927ac37395f59baf2d8ddde76c10ff17bad093a2432ac30ed031b7959386a4a350824b5727b41091a1e1c87201b5527aac93e45620e2f109198858dc4344e204bc1f8610300e06fc349a6624e73387e2a078c9c9ba1f0be560f2298114a49be4a4db2d5485429c180c81fe6610035082110388801c2480e8230739a40c8860204b0150606703833e3a7eb375ee7f8c44f589602365395ffb1bd54ed84ac2f43847c11aa893c53c9de347d8683f861b90561cc2b3a328aa893c67ca229e4efa1289c23e08d200470ff0fee4158750ad398565d21365d8677a86522049d0824a9f05c2d07ba0848d0f0e41b02f2c8158e403431104620fed79e7d6cf066a76fa328aa893c54c9e6b24f90d2699593867ca22ae4f7ab28ea793be84a265a4e35527ad2945e11f0469002387f87f720ac3a8569cc2b2e909b2ec33bd43291024e841254f82e1683dd04246878720d8179640ac7201a188823107f56ce766a727af3abd19455449e2a64f35927c86934cac9c33e5115727bd594753c9df425132d271aa93d694a2f08f82348011c3fc3fb90561d42b4e61597484d97619dea1948812742092a7c170b41ee8212343c3906c0bcb20563900d0c4411883fa6a6edaf387ad9bee8ca2aa24f153279ac93e4349a6564e19f288ab93deaca3a9e4efa128996938d549eb4a517847c11a4008e1fe1fdc82b0ea15a730acba426cbb0cef50ca44093a104953e0b85a0f741091a1e1c83605e5902b1c806862208c41fd3535aad9b0ebcdaf4651551278a993cd649f21a4d32b270cf94455c9ef5651d4f277d0944cb49c6aa4f5a528bc4341ba1c0de86934c2c9a32100240830c9780afbc8581de1425c0f92c07ba104990c24e5b02c44827068374381bc19880d69a856cd22a64f35927c86934cac9c2164d15727bd59476a4a365e4e52d271aa93d611f0469002387f87f720ac3a8569cc2b2e909b2ec33bd43291024e8412541091a1e1c93e0b85a0f70d8179640ac7201ba328aa893c54c9e6b24f90d2699593867ca22ae4f7ab28ea793be84a265a4e35527ad2945ebcd46b66918a810c3 0x22a3221d21971ce1192714c512d9129211cc0ebb0baa08990588052e02ef001d0000 (i%16)
private def hints₂p4 (i:ℕ) : ℕ := packedAt 0x503b056cb0129a7844730ab66a265d618ae30c12b0799483c4bc1f65a0f93f08e210484f82374f6f394a6e49d2b73af332f567a8b8755dd3e5aa713158b92a3de85e6ea6e4a550232e816a04120351310d89d87c2fcb552150a7060240741903fccc2006a10423071910388801c24b0153481910c0401c19e0c0ce818dcc6cb1a765a9172c49c969c0463e2a587192c58e963d84b8a6e5a5632e39e96ac4cb09fe2d52035130188792b44937a26cf82348011c3fc4d20a25c2f11f97284cc942d2c9d69e4ef4d27686934d4c9e72a5075127887c2fde1e0454f617cdc1506d0a7e0b88548f9122818966fc4935a1e0af0f21989993937674a1f3650d3127394937d4c9e61a4d34f277d0944cbc9cb3250b2d27192936a0a25e34b0128e0153730ab38c304f82365e0fb2d07ca04120ba05a1a8982b0799483c4aa04724381bf225909f2e07d9683e8a41e25f8902a8118621e4ad12cea15a7244a3a4310fd12a801204209168ca2aa24f12726e98939d4c9e61a4d30b268ab93dcbc9ca5a4e35527a92936e94a2f01c02a27c8916fc4935a1e33650d99285c0d06e86402c6c23c3811fba3c08b1e845dad0f07d0c02bc3d38224d3c2b0e90c4d19455349db3e5114f277a593aa1048aae4f680120a993cd549eae1683dcb20b6568926f0a8a705533650d2b270cf944664a165a4e318580f52d07b1503cca41e52726e94937cac9c25a4e32526dba3c08b1e845e9a4ed4f277a593aef8740b8360919086124400902104890711cf015f730abb88555b8298ef0a17284c364214b81f25e0fa2c07b8ec038b60581a0dd0cc46264168a01dc560f22a07894c0886a0152726e91936674a1e624e72926fa993cd649f21a4d32b270c994142c9a33e5115727bd59476a4a37425132f272cb9424b49c6aa4f52526d 0x149311eb0f810deb0d8f0bce0ab50a99085a07d4077c05fa0521045c03eb03b90000 (i%16)
private def hints₂p5 (i:ℕ) : ℕ := packedAt 0x14058094760adb9855b4f088e30c1cd44cbac31508242560f33e08d9783ecb41f27e11c29078d5cf8e527ab533e1ce9f6c9cf529e7bf313d9979ec544f83427df2d3d7929e995408cba05a810480d44c4362761f0bf4058094760adb9855b4f088e30c1cd44cbac314ac1e6520f12f07d9683e4f82367e11c42090cc45ca522dd2516c978b8d3c5d74230551176ab8bce746024e2db2d170a98bb95408cba05a810480d44c4362761f0bf5066100350821903fe72be13d6169db01cdd782a02387f8a62b455d4e29caa046810480d44c4362761f0bfe7294cc93a4ecea2aaa0c81fe6a1049ba4dcf527a4c1e7298a9330804e62a2a0c81fe6a1049ba654f5337ce529972749ca8330801a8410c81ff395f19eb0bcdd78676c094058094760adb9855b4f088e30c1cd44c9f046ca41e25e0fb2d07ce757de62afd294cb92a364b54969ebdf2749cd0afccbd56a70200670a8350824f6294c81ff3b8a49bc51bac31508242550232e816a04120351310d89d87c2fd5e28a50b2140e6156760adb8c3074f0887c11bcd44c9783ecb41f2520f198ac053d8565aa4f294cdd0b0fc951bb3ac3b2f55c93a4f15408cba05a810480d44c4362761f0bf28590a0730ab3b056dc6183a78443e08d9783ecb41f39a89929078cc55ff42c192d526a7b014a53325eab79d60a93a4ec951b4aa0465d02d4082406a2621b13b0f85f942c850398559d82b6e30c1d3c221f046ca41e25e0fb2d07ce6a2664a8d7294ca98abee857a29ebbf2749b97aaccb54933abcc550232e816a04120351310d89d87c2fd4198400d4208640ff9db034dd78e7ac33395f3a02c04a3b056dcc2ada784475862b8c30735132841213e08d9783ecb41f27e11c290789583cea6341a11acab8d14c46625e32f5119f928c96746aa5a32d27193948ca53c678aa0465d02d4082406a2621b13b0f85fcf07c34c046ba80b0128ec15b730ab69e111d618ae30c1cd44c9483c5082427c11b2b0799f8470bc1f65a0f998ac649d2ba9ede953726abba84951f2529bb9d7a2a8b87cb54e65ead1a17a4b1096d86278aa0465d02d4082406a2621b13b0f85f 0x1835158d12e5118d11461096103a10080f6d0c860a71085c064705ac030402d20000 (i%16)
private def hints₂p6 (i:ℕ) : ℕ := packedAt 0x241531a040c5ed546850716a180d985c5b42627311d11785f89087c2fa1048aae34531198968cb1483c64a324560f3938c995408e523287e895aa8d0a0e2d4301b30989c85c5b436276a233ff65d8bb2d07d4bc65e7dd42b4588bad18d6d61ca1229f05cd18d6e7c6af0110388801c35872848a7c170b213e5c0fb2d07d3a8568bf120e90c4400901483c4ac1e6841223f08f4c56324e95d53726abba867de8e4a8f9294ddaab9e545c3e5aa732f568d1bd2c3e17e1b13a550231b805a0e2d4301b30b8b684c4e561ca1229f05c2c84fba8568b81f65a0fa7486217e240ac1e6520f1420911fa25500241294dc93a56cbd59ea2e1d5774f96a9c4c562e4a8f7a379caab9dd4dc973ef350f85f86c4e95408d0716a180d985c5b4262725aa7060548541203a0d4208640ff3308011838c881c4400e12580a9a40c8860200e0cf06067464a527a547632af8a9494dca82c255d3b2a2808c744ca4606370ff1698b949c74a5a725431b295a02c04a3b056dcc2ada784471860e6a265d618a7c11b2f07d9683e4ac1e6520f1420909f84729e7772d3b3979da54cef652763253afce9e3d5cefea2779313b5939d8684f263515f158b48cc59c5e2ca27163a58a081c58204120ba05a1a8982a811c3e17e1b13b40ec15b2c04a69e111cc2ad9a89975862b8c304fc238520f13e08d9583cd082425e0fb2d07cd44d724a6a531358ce9b1d3cd6e526a9a1365a99aed5cd7e5e6af27353969ab15408cba05a810480d44c4362761f0bfa58a081c58503b056cb0129a7844730ab66a265d618ae30c12b0799483c4fc2385e0fb2d07ca10484f82372938dd09d2c9ce324a7172d38fa89cc4c4e473a7472f390ab9cdd3ce5ea6732550232e816a04120351310d89d87c2fe96282071614058094760adb9855b4f088e30c1cd44cbac314bc1f65a0f92b0799483c5082427c11b3f08e49cdbe5e6e729370a99bce74dfe4a6dda1381ab9bdd3cdde626e92d372a89bc15408cba05a810480d44c4362761f0bfa58a081c58503b056cb0129a7844730ab66a265d618ae30c1290789783ecb41f2560f3420909f8470f82372d33e9299d4c4d024e6779d3499799fca4cf2ae68d53344a89a1e84d2e9e684550232e816a04120351310d89d87c2fe96282071611c3fc4cd4c7425a387511cf988e2e6c78252383251bfa78e7674787423c72f1c4938e0204120351310d89d87c2ff412c0563b15c4906023071a9a27d53158440e2200709a40c8860200c0ce7fc5683833e03143a58a0 0x1c7e1be21a2119da1993193619051647139e11340df90b270855058302b101430000 (i%16)
private def hints₂p7 (i:ℕ) : ℕ := packedAt 0x1d11b3bc8e9f0540478fe188e88cb96c66cc6330ad19484122abc6468e31ca518b2f8c3cfc617446cece3a7afd11d3d98d9dac631703ecb41f5e7293d5939ea4703a237193e7293b1939d874474f8e3677fd11b3ca8e9f8561ca1229f05c2c84fba856bc64e7a9253d38e07446e313c64a75f273b0e88d9da474f63a2367911d3eeac3942453e0b85909f750ad3a4310b81f65a0fa3f08f210488ac1e6520f1d18c1cc45ca522dd2516c978b8d445daae2f32716dcf8c0cb45c25aa98a753c5c9a40c886020460e72407403033a3a7c31b3bd8b9bcc54d7626688ff1778c9cc92c056a15025a66100350821903fd4f17269032218081203a08c1ce0c0ce8d9df4e57ca2a6bd133458c9cd4f58622e6f5375e28e9f13fc5e276c0a4b015 0x8e507b707850753071d06c1068f065d062b05ce05720540050e04dc031a01d60000 (i%16)
private def hints₂p8 (i:ℕ) : ℕ := packedAt 0x8cb2fc483a4311002407e11e29078a10488ac1e7531d0d28f2cb470ea239fa31e4988e2ca47064a37f9f1e2ab8e94bc7124e381551d18146ea0e2d46e016550230c06cc3e17e131390d89d85c5b54198400d4208640ff9da934e54967aa4f375249646594a371d21887e11ea8c6c68e35f3f1ad318d597c6a210488ad157578a254096a9e34a2b1a7198d18bc6844e33c9119c6903221808030339ff1825f8904009054e302ab17e4b01507067c062fac7171618b7d2c5043e17e1b13a550231b805a0e2d4301b30b8b684c4e78c9d2764a8db3a8dba8330801a8412729393d49e93078c96368c81ff378d9a8330801a8412728d93d46ef192a35c9d26ea0d4208661003207fce57c27ac2d3b6039baf0541a8410cc200640ff9eb104ed8366ebd3395faa8330801a8410c81ff3b60b9cafc4f587a6ebcf5066100350821903fe72afd3b57f9eac04dd5f6a0cc200640ff350824ed56e6eab33d55c9caad7995e318a41e2e90c4d19b31f8479082445c0fb2d07d67cd92626b15135c929a94a4d52ae6bf2f357939a9cb4d5b8c8f17318ce90c42b0799483c4b41f47e11e2e07da1048a5271b2738cd19d3494e2f3e7492d38fa89cc4c4e465e7215739b8c6748621583cca41e2841222e07d9683e8fc23da3382cf9c049cdbe5e6e729370929b755cdee626e92d372a89bc623a232ca41e2560f3420911f847a5a67d2533a989a049ccee5e67f2933cab9a3544d0f3e695a334c 0x10a00e330a3b09f4094408e808b6081b078006e5064a05af0442042502b401430000 (i%16)
private def hints₂p9 (i:ℕ) : ℕ := packedAt 0x542a04b4cc200640ff3508229e348d2064430102446692c0566ea49153568b9b958d4e67aa4f395258c9c7d854e22667d3b526060673fc5c2071cf558e22981105a37a1716d0d89d87c2fd09703e4b01ef2d54c6a29e348901d0690322180812c0541819c0e0cf8d9da45cdcec2aceff1718999fc0465e3a7b1635688a9abc64e42071cf558e22981105a37a1716d0d89d87c2fe783e1b20232b038e7aac7114c0882d1bd0b8b686c4ec3e17f3c1f0db011b081c73d56388a6044168de85c5b4362761f0bf9e0f8c0808d058dc9ac2e4b038e7aac7114c0882d1bd0b8b686c4ec3e17f3c1f0e7011af81c73d56388a6044168de85c5b4362761f0bf5f788643bc2850c2485c0f92f07d1603dc7601c5b02c0d06ea0048108244198e141c731583ca6a38f531d0ad8ea6b47a25a387591d3998e34c471656385291c1d78f4c946ff523cdab1e7ab8e94bc713623d56079864bbc2850824c861272e07c9783e8b01ee8904e2d816070378341ba198e5a32e07d9803f0be05ef21600d4393bc31d0c24a8012142c721683dcb20574a5d8677b0b19883f8bc1f8f50ca3081822049c381be878720d8261640afc64a32527193cf07c5fd8dcf2023436173b818e8cc0d4392104890c2463900df193a554951dfc64e95725478 0xeb30c5f0c2d0a170952088d079e06d90445034002510162013000bf006400320000 (i%16)
private def hints₂p10 (i:ℕ) : ℕ := packedAt 0x23f1c82b151724cfc254734d5773630991a3e8614734d573362e111131b3cf8b9c3c54dae327571335181c73d56388a6044168de85c5b4362761f0bf50640ff330801a84124e870c9448273c8580381bc1a0dd77c768640acbc1f4580f7a33007e1703ecbe05e1a8722c8158623dac0d06ec79a004825aa90a8538301203a0cc200640ff350821003848c1c6440e22580a9a40c8860200e0cf06067464e7202347637657f8bd4dd79272be93b6078a9b045cdf23a7c913347b0bb24f586a36781038e7aac7114c0882d1bd0b8b686c4ec3e17ebef10c877c76a18490bc1f43b00e2d816068374331c28412296a9c180901d0a98a22007091838c881c44b0153481910c0401c19e0c0ce8e9f1d8dd42c2e9f011a28d9dfc5cdedfe2f31535f899a3464e6e071cf558e22981105a37a1716d0d89d87c2fd42a04b4cc200640ff3508229e348901d0690322180812c0541819c0e0cf8c9c6cdd32ac29b8ff16e8e9eac5cdc2729971b3b1b1a6ec4ccf22a6a93b4cc9ea66c04652071cf558e22981105a37a1716d0d89d87c2fcb5531aaa78d2240741a40c8860204b0150606703833dfe2e56358c8a9ac44cd02c2b17011988e9ecc64e462e6e91b3b581c73d56388a6044168de85c5b4362761f0bf9f0119607c7740e39eab1c4530220b46f42e2da1b13b0f85f 0xf320ee70eb10e930e5d0d550d0e0c480bc20ba70b86089e07d8058302db00c50000 (i%16)
private def hints₂p11 (i:ℕ) : ℕ := packedAt 0x2a2df08e708601703ed002432f520cdaa7e6553aa6a652c0fa2d845b70531320b597840c9c194e0e06f0683763926abb3b182ec80a4b642ecfc2327c1173c08ab5c1f4f607a5902b0c47b0d4028a2035496b83e9383b1b21767e1193e08b9e0454a20347b03d080689640ac26044188f62948396a3e0ab206849024048552db4e9add79383482915c8d18aa2e492143ec8c1740c7ab611cd35909d2c82d3e3ec6a015496b83e9383b1b2176781152880d1ec0f4201a2130222948395426cbb0ce5e0fc7a8651840c11024e1c0df43c3906c130b2056e815a0c47b3ac314b51f07e11c3e08da104869f1f7a5905818f56460ba4287d5172491a314148af4709b93834a6b75d2db4f611cd35909a4b5c1f49c1d8d90bb3c08a944068f607a100d10981114a41caa1365d8672f07e3d4328c2060881270e06fa1e1c8360985902b740ad0623d9d618a5a8f83f08e1f046d0824281908818e3d45736468932141cc8aece8d77696b954d5cbc9aed4147fe9f1f7a5905a4b5c1f49c1d8d90bb3f08c9f045cf022a5101a3d81e840344b2056130220c47b14a41cb51f055903424810d402a9f1f7a5905828ffe4d76a9ab974b5cac8aecc8507246893515cd818e3f8c9d26a4a8d5348e6d8c8378c9d3124a9231cdb184e9aaef45c90c040901d0460e706067474f95fe2f7365d8672f07e3d4328c2060881277448007037d0f0e49f05c0d8261640ac311ec5a8f8424814e0e06f06837432056580f72dc7bbc85811024cef0c743092c5c90c040901d0460e706067474fd1fe30f1cdb184d9aaeee8a3fe3f1c82b1515cdcfaedcd239b631fc7f87f730acba856a9f1f7a18fd 0x12e611b7118610690dd50a84074804f304970465042f03a5027701b3012900de0000 (i%16)
private def hints₂p12 (i:ℕ) : ℕ := packedAt 0xbb6c0a61f8464f822f932bacb95e544aae9e55576d814c3e08b9f8467270634f705a8b90e5e0feecfc2327c1176c0a65456bf2eb814f5aec9adfddb60530fc2327c117c9bc265de1aa2e1b4f6f2bb3e08b9f8465b029997841a7b83d45c8f2706722f2b507abb60cb54ba399051eb335add8b75eadba2b2db35b6daaab6bcc562216553a96e79aae5cbd592a6dad0d2ddd7b7547320a3d762da70d2dc99ad66adb42b2d85536bf98ac3d55b0216551355caadb61cbd58f5eda5a96cfbb3f08c9f045cf022a7b03d6c0a60403469add3031e8c9c19545c8b2f0814f70682914d2db446a015ef2d53495a86fbcb54ce56a190f3bc889d40ea8ed3d496b8094891403ba468c12548fd0403460a453031e89c2fc2bd860da7010c390869283a4ea0744d0188fa08d15a0af2ffd1d3f4a3b4f50d99afb01c4e0ed90a1e1403ba468c0540f193a6149523eaee5091738619703ed002432f579a9b9be40525ae0fa5a90f2ac873642ecfc2327c1173c08a9483b89c1d87b03d2880d0403446a0154b6d182914d3dc1b3f09323460a8b9164e0ca063d14d6e992a47e8612eb8eb096778639703ed002432f520d2aa9d4d4cb52aab2c0fa 0xd980cfd0c620bc70b2c0a910a4608ff07b80675064306110560051c035a00c60000 (i%16)
private def hints₂p13 (i:ℕ) : ℕ := packedAt 0x549c6120df0bf2e07ca0046e5eaf153736c70a43541e8aa114580f7cead0e656809c1d92141a2907748d11e4a8d0da14a6b85d1e045a96b0e7e11aa8ac553d62722b399559eb134e117984959f64aa1b259f868110f822e1c0de3f08cd3cb7a1651f512df1a80543e16e48eaede1536eed5b82ea5c135ee0f556ef99ad74bd596b2de3ad706adb7942caaa9c22e7d92a87c2dc64fe089512ab0e06fc2a49c3607e3500a87c2def8741103607e1902b2c4941383b0a2034100d16b0a484c089b2176520f13f08c9f045e1a5a32749892a344147f60638b9359dc8ace54562a4688f2141aa7ac48d402be9683dff0d06eddb60530fc2327c117c9acee5d67ea2b154f58998491d664961b24955922a9c90cbe4835323f0b91ed5c8ecce472b7237af91a1a8055db60530fc2327c117c9bb9e5ddd6a2e194f6f1bb3e08bb60530fc2334f2dec997b544b7f2e5f11ea8390bbb3f08c9f045db02999774ea8b8553dbbf26e9b767e1193e08bb60532a2e134f6eec9b9c65dceaecfc232d814c3e08bd4559b2eaf99357aa7ab2dd9f045db02987e119cbc1f53dc132706151720 0xceb0ac00a61099e085707bb05a6058a056f03c30328028d026c01d10136009b0000 (i%16)
private def hints₂p14 (i:ℕ) : ℕ := packedAt 0x1dd232ca92965f74951a24688f24753475d7a485551da668d3240ee91c9deae4e2af2735b93a923d7a30d4d13e6689155450ee91a29c951e7ba468a325477ee92a4748d17e40aa1151ba7b77a04322a91ea838f843093a10499e02be8990d77c76c34bdf5b07753739d4c1cc2caeeaeec12f57bd5c1d56de1432056580f72f07d451501e8a41dcda14a6a0a41383b2468a525478cabba645dca42853233ad6d1ab38c241ce187a184bcec989703e5051e7ac9234008dcbd5e6b6f075574ca9b9bebe0b6b2ee55775ed5c166a60ae66b7c580f784bd00ab6b23e1ce186820c84209321849de02bf57762adbc3eae10f5308598152cec98b8c241be17eef8ed2e07ca0046eb2ee32f578a9b9b1603dcbc1f51f0820c84209321849de02bfad848adbc455dd8f5708fa984677c769783ebd154229a8290da14a6b85d1383b0a41dc781169094c644ae71e5712529aca95dc8ca669655110381bf0f85b 0xad50aa30a7109a80948091608e408b2089506d305f905d804400251015e00310000 (i%16)
private def hints₂p15 (i:ℕ) : ℕ := packedAt 0x952a8473a0565bc2a2e70c37086047b9683e9e42c05f02f7786386a1c9002428612598acf4bd5ee5aa9b0b2bbd4c1cd4dce75b077335bf41470d55d36b2ee81494cabbb0434bde1e65d2060360241a70521d8392dc2caef73184f0941d38181fbfc0b47d03b73184f0941d37f815c0c0f47d036f4f528eda14a6c0a4b5c1ecb0132540f012800808351cc2ac1389871860a08480f82367e11c87ca001836c081b41b02d0a4a2c364fa9e8e7051f793a31e852269a8e591481caa41d451d2968e355476c9a4167521ea68ea4e0ec90a0a48d10649290180d985c9fdc1d8444f21727a947690a3b50521b0292d707b2c04cb98559c6182821203e08d9f84710208a100d1098119503c49c1db4b44ba8a2754d13f1a8a94d44cd0a2e49d10aaa8a1051f6c7a2ad3d1364282793457cea2d64515a92895031be9107707037c3605a1494586c9f43e502ecf022b707037c3605a5c0f92f07d6bc1c8d6124d9220ee92ca26bc1c8da124db2060360241a707236828fbc903ba472841593c90301b0120d3828fb41c8d7ba468a525478ee9298448cc1fba4a53523299 0xcc80c570a7d0a0e099e092e05f3028e0271021701bb018900f00096006400320000 (i%16)
private def hints₂p16 (i:ℕ) : ℕ := packedAt 0x932e847b9055dc42a6e70c370860202574bc1f8610300e06f86c130b20573a5c093770ae390555d618ae30c1a637422d320b4549282d48a65dd3b26e9b2b50caa470a0e56a672b6d694fc8caab642ecf822e7e1193c08a9ec0f4b20574b9340c4a9d3e54aa32a34d9500806884c0886a0141494c8290ec3ccbaaeec12d54dacbba40c7761a5ef238dd08b4c82d1524a0b41ef2b4fdad69547346a36e909b95493174265ba1169905a734ab9501f4b52b2eb0c571860a06560bc1f8610307a86522049c381be878720d82621255a62b3d9b837adbc2eae0ea5eaf75776096aa6d65dd35b0770d2f72c8159e0454fc2323500a3e08b9ec0f4201a30521d818eeb5a53f232ab4d950a8ca8d2e4d21e65d4f9520c4a984c088292991c540956f0a93a056b32a2da551cd1a8dca83dcb81f32f57b96aa6e760e253b32a2da351bd0a8d4a83dcb81f25b95773861d65d2137a351bd0a8d17619e5524daf91a6e845a64168a80fa3500a3c08ad2e4d23dcb41f4f21602f817bbc31c350e48012143092cc567a1e65d2f57babbb04b553616577a9839acbba54dce75b0770d2f70a4a647b9683e9e42c05f02f7786386a1c9002428612542caa20a386aae99335be98acf43ccba5eaf75776096aa6c2caef5307359774a9b9ceb60ee1a5ee189530981105253254aa11ce815a6f0a93ac315c61828194e2e07c9783e8b71c99b837cec1c1640acfc2323500aa8ca89f045cf607a100d18290ec0c7769b2a14f952d8c174d5765051c2189530981168546b46a37a551ccca8b4aa48e66b7d3159e8697bd4dce65eaf7597748595deae0eb530735b785d7c16c3ccbaaae992d54dabbb06b60ec2929990830c9780afbc8581de142580a43007f3d8592669fbb151e9aa7f6cd47df21968011b9549b2284ad0c24e841262e07c9783e8c60627d92744c8696e3d8341ba1c0de98acf56de161e65dab83a97abdd5dd825aa9b0b2bbd4c1cd75e52b2ee953739d6c1dc34bdc29298100d18290ec0c7769f2a5216828f5d7b83d55bbe66b5d2b50998acf56de161e65dab83a97abdd5dd825aa9b0b2bbd4c1cd65dd2a6e73ad83b8697b85253242d051eb335afaab854ad42b5ee473159eadbc2c3ccbb570752f57babbb04b553616577a9839acbba54dce75b0770d2f70a4a648c4ad4221e65d5776096aa6eb60ec292992a5508e740ad378549d618ae30c140ca71703e4bc1f45b8e4424a6e6545b4aa39a351bd0a8d4aa48d051c3b18349aaed4cd6feaae9baf833c90a4b642ecfc2327c1173c08acc567b3706f5b785879976ae0ea5eaf75776096aa6c2caef530739d838acbba54dce75b0770d2f71a8051640acf607a100d18290ec0c774260441494c 0x1e901da11d301a5d19e815c514d61437133211970f7e0b7107cd06320497040d0000 (i%16)
private def hints₂p17 (i:ℕ) : ℕ := packedAt 0x2588f822c7a1153c81e37c230301b0120d32c07a9503cc201a50b298a7a1254d09a9a8474b422828fad450960e4692b417cba19c9d0560637b29416cca1a4803b09f2db9596096c94cb5cbf06969ce4b504e5932120d30806941c8e206383051f9968cd92f41a5a4272c995960f6c2a596081a71368011c3fcb39f045cf72cce0151710a935a1ddbe118540f32c07ac9c8de964878d2579091a644966564734f245aa9246649769a48951246a9923e3c9632e4b98282120408605d1f8468f022c7d962e1503cc201a5271f8818da860362081a7747e11a3c08b1f6588f52c2d01446b43bb7c231a60f2580f52a079e6477f1a3b3971dea98e864476e9a39b511cfa58e64ac70a9e39d491cbc58ec49c7031e3b5211bd8106941e58c6601011019cacb05d1f8468f022c7d9623d4b0b40511a60f2d68776f8461503ccb01eb27237a5921e3495e424698b256c892ccac8e6924854f245cc92ed34912a248d53247c792c65c97226d002387f0bd6d0a7db9f045cf022a76113c840348241a61595f2d07b15e5709c1d90d2f7818eed4dce6b2ee9294efcec1c6a60e6165772d54dabbb04bd5ee1e65d0725bcdc1bc850ca0a43b3159e8f2e07db8854cbe05ee10c00d4392004850c24a8595e3f08c9503ccf822e828e199a7ed4542b4aa394d50893a4ae7d4669ea135550cd0a8d4a83d4f607a5902b080688623d8260443500a 0xffa0dcc0dab0d620cf40c940c610a5d0a2b09e4096106e304ce0483043c02540000 (i%16)
private def hints₂p18 (i:ℕ) : ℕ := packedAt 0xc43f08fa104890608e1c0df0d820a025f5c52f8e88cb2e07d97e5e4aa0383900dab924d4c91f4a4c7512469891e4348bb3e4c15924aaa92468c98b564cd2f23bce92fc3c8bf424c39b25ed39320403460a3d7031b6c1410901f046cfc23953247a89235549229e48b225908d720aab8054e44b211ae4155700a9b8c305042407c11b3f08e204104352f4600fc2e07d97e5e4aa038180d80806955482e9e411a3224988fed64836a6415a7226cf9116ac8a2a2413a5225ab90666c882163db0d1ee998ff6748865e3f9a1223818dac1034e1f0b6139782d4bb95a5c700e06fd75420bced0a02c04a176319cc2b2e90c43f08fa1048900240830470e06fbc65d03605f0f85b1c80695407298900764283609f2e41902490301b0120d38594c4147d6401d84f97383cbb4b65c260d06e864090252eaf015f77c769603dcbc1f50b22d87917cac8e65e477ab266aa92440c6dab2495a9265828f5c348ba6247953247ab924ee86c078332e8100d1c8420912004810c246830470e06f86c0bc7201b90841224009021848d0608ef015f0e06fbbe3b43605e3900d2f07d060360201a55520b988fed64836a6415ab228ab9064ac7ea163db0d1ee978fe6a489e0636b040d387c2d84e5cb71020d28506c04406432049ec5b96e94cb7cb65c324e0ec0806904834e42831031c3828fdc1c8ebb09f2d721416 0xfa80d000c650c1e08ce08b3075a06fc064e048f044803ad016e011100ca00320000 (i%16)
private def hints₂p19 (i:ℕ) : ℕ := packedAt 0x1eb2b50b94a6c7acad432529b3eb2b50a94a6bcc3b6651eaf3112f98998cc51640ac311edeb294c895a7e7aca531e569f7eb294da95a86cc220a386b2a1d2a0f594cc343e16c26045a99852c8158623da38507307594db87c2d84c08b5330a5902bf594a7ccad47657f3aa319b5179507aca660e1f0b6130222c8158623dbf970205b829a5e0fc4d82c9865e9bc2a45595e0d82638c305082428198299a64e853d73e9e9a54f7c9a776753cf369e5994f1cba7843e16c260445902b932a0409783ecbb302e41576f0a8b8854dce186e10c0cca78e6d3cb3a9e79f4f4d0a7ad35360b2dd07f2a847e5d3c3269dde0a80fad01446b0a3b4c2e0ec2227c1163d08a9e40e0b204c0e0cf0d06e844064320481297f2707652c90e1645b8d2579091a62c95b224b349242a7922c0c6da9a4890118d8691741a5ecb52ee5697196cb86e86c078332fc100d1869174147ae0636d0b22d 0xa910a5f0a2d09fb0971093f090d08db08120788075606a204b8039f032d009b0000 (i%16)
private def hints₂p20 (i:ℕ) : ℕ := packedAt 0xfcda14a2ac3bb5c2e8fc2347a1173c08b1f649c320565c0f92c07b9383b21a59b0b29c97a63d353571e9d92d4c6a7a6b52d3531a9d7914ed95a62d4535e4282d2899d08068c16672073365b99acacb004c08829301747e11a3d08b9e0458fb24e1902b6b43b9603d4a81e74f530c6aa4cad3ea428318f54aa6a97c9d25aa2a630b29e86967e4552e96a5d2c0f608068c16670260450399bf6968fdca47e7da5a387291c1f5958e14a4706041a3059992c8158623da173310d99708ccb04c08829301eb291f9958fd68c0c6e20a3dba3031b9828f74961ee59832056df08c6b43b9603d4a81e7292cd9396663cbd29e5bd4b2dca9970664be65659d212c9c6979e44bd6a25bf972f8a696ec326572b2c0130220a4c045cfb2547b9660c815b7c231ad0ee580f52a079c84a6252539532accc95ee44ae71e571972bca6954d44aae965512b29d9394dd3caab1a56f0a994cacb004c08829301eb2b1c2948e0c0a6469f3274d992270761ec0f6430ca5902b0c47b43e16c2604414980f594a6b4ad427d6529ab2b50898f3e08bd2e640b2056188f6f595a83ca5353d6563f529986824c5b6651eaf3112f98998cc5556636a731c7e119a8cc61640ac311ec3500a 0xdfc0b550940090e08dc07ed07bb078907570553033d022401f201c00160012e0000 (i%16)
private def hints₂p21 (i:ℕ) : ℕ := packedAt 0x1e8b125055078680a235051ae0ec222790b96a0a434851e440c01f85f02f0d4396b26a50c24a858e4d5cd5ebe6a9ae0fa559a86cca39f8464f822e828e199a7eec547ab6a1f354fe98a7e54542a1a59d5350b97a7dd3542352a3b4f5098594ed55432aea1b5950e954d39383b0f607b218652c8158d402a972685699e87c2d84c0882930149c9c18e460b2939182dc9c19d81e71eeef0c740090a18496c0f38f777863a004850c24a858e4d6c8b6be46b5723add08b4c82d0d4028b205678115a5c9a43e16c26045250d61492accfb6651cf822e7e119a796f64cbdb225eb512df864d2c2e69a9b3483500aa5c9a43e16cb20567b03d09811494358524ab33ed99473f08c9f045f22573932baa8955d3caa86a0154b9342c815d366921f0b6130229a1a7cd1d4668a9b3490f85b0981148c6b5ba6aedb1247576f0a9b776adc1752e09af707aab77ccd6ba5eacb596f198ac4eb5c1ab6de5247335afa9b84d55c2b5ae452f566acb864c562aaee17af723d5b90d6dc3752e41220600fc2f81786a1c90c24a8590cd6491a0a3d65eaf35b783aaba654dcdf5f05b59772abbaf6ae0b353057335bec80a4e4e681af251319292accfb6651cfc2323500a2c815c86194f022b4b93487c2d9f045cf607a130228f541c85d6de12b2ee75775fd6c196ae0c65eaf5a9830a9b9c4cd6feaae9baf833a664dd7f2eec356926d6c8b37422d320b45902b3c08ad2e4d21f0b613022 0x107d10220fc60c5d0c2a0bf70b9a0a4108bb077406ff06c905c104b901f800f00000 (i%16)
private def hints₂p22 (i:ℕ) : ℕ := packedAt 0x1005d095802e84a9783f0c32f4e815a0d8263ac315082430f85b098111640ae92d707d6cca39f045cab3507e1193d81e9640ad051c24e0ec080688623da9ea615753490a0c40c70e5ea41051fbada9b5354be66a4551531aaa99cd548e1653d9354c86967d4d4cab2a6bb1557d4aaacc548722a972c9bb1a80552e4d0ad33d0f85b098110526026e8311ed0b99886ccb8466c826044149802b4cf68c0c7a20a453ac9b98e1ac8e9d5c74a041a3059b841cdac3e16e1b32f0b998aacdb4ae6de48eb641d311fdac906d4c82b56451af22aab9064cc7fa5e3f9a9227d1818e14147eb460a417031d190ba98e856c752b23a7331c6988e2ebc7a7523cdab1e7ab8e94bc712041a3059b487c2dc3665e173311cb5b20ed8915cc47f6b241b5320ad59146bc8aaae419331fe978fe6a489e6a3ffa305224818f2561d21365e0fb4f82e174264b2114da14e730ab9526c1ba17ce58fc6b4d6a08475002387c11a3f8220703789c1d87a92cd197f554b871e5e94f2de85947cc4b46925b7532e09596766cbea425938d2f397968644bd6a25bfa12fdcb97c67cbf29a5bb0c9b10d8160666b32b2c03500aa5c9a15a67a1f0b6130220a4c0515a20f0970582a4d83542e4f135ed29ae6b4d6b963f09c1d87a1194108ea00470f82359f2c09094c54cab322573492a7c795c534aa6a25578b2b6cd95f4aca769e5558d2b7aa9569fe4be151ec3500aa5c9a15a67a1f0b6130220d8160666b029301544e82db84234b12517076111 0x111510f8101e0ce20c430bfc0b1e0a400a0e09dc0895078d075b03770065001d0000 (i%16)
private def hints₂p23 (i:ℕ) : ℕ := packedAt 0x2e8fc234781166b0a41ea4b4fb24ed507a080689383b2063a121426c8b9bc1482b1ee6d529cda7cd1d4668a9b3492b9c8a5c9a43e16c260441902b2c4e3cb670cb73785699e0a4c047320a3d65e389311c59a8e3d6c7535a3d1331c6d78f4ea479b563cfb11ea81068c1672eab36c119c987c2d84c08a573912d9c32dcde15a67829301216828f59b8d6914e8c147d60637b2473341baaa13cbd0675e87ba943aada156ad0ef5a879200ec2783d35052323266d70bac7c991f8468f022d3192e3d4969f649e972688990d0c81596271e9b349519a2a7cd1cae720b73792d9c32b4cf43e16c2604414980bf6f0a920046cfc2347a117718481f649cb81f2109b7cca8b675462a2a155350b97a7dd354229ea12130220c81596271e428587f408619f8465051c27b03d0c4e31883f8c338aea15a730acba4254bc1f45c0f9084dbccd3f762a3d5b50f9aa7f4c53f2a2a150d2cea9a85e9547366a3f2f4fba6a8468d46e1653b5d510aca8768546aab2292a0f7abc8a8d402a1f0b613022c4341ba1c0de97a0d81786243511388f81647b85255e4572d14256861274209352170200b20f4559c2700a8b50521b4294f61646f85fb5c2e8c01fc5e0fd7c865a0046cfc2347a1173c08b18c0c51425686127420931f649c341ba1c0de44c868667049c1d8100d1a7a9855d4d2428318f54a818e1c147eeb6a6d4d52f99a915454c6baa6fb35589aa91e6d53e1653d9954e86967d4d4cab2a6bb155798a90e4552f2b2c14b9342b4cf43e16c26044149802dcde52170248b21155e7884f3b431900182620fe42092b8854cc32f4878727084906c0bd460ba5e0fb2e84737a700a937eda14b6cca39f045cfc232828e13d81e9640ac6a0154b93487c2dcc5486b2a6b9d550a9a99434b3f4aaa79354ccdaa7cd548f56aad55533a8a98ccd48b4eaa9a1551d1aa95354be5ea4157534a7a980403460638613022828fdcb3b80545c42a59d550a9a9966553b36a9f5553392a1e43d0a0981a97a3007e17e6f9d02b2e70c3404dec3e16c260445902b 0x175215131339131812f712c510040e820b700b400ab60a6f05cf059d018f00f00000 (i%16)
private def hints₂p24 (i:ℕ) : ℕ := packedAt 0x5e200470fe1767c1173c08ad3caaa96551512aba6954d4cab1b4295952bb6c0a4e44ae726575788011c3f85db68539b0298dd08b2d07b9f045cf022a590283d82107037c3604a9905a0c81184237adcec2247c1173c08a9ee599a0288d68776f84634c1e4b41ec580f52a0799383b2388189b3fcb39f045cf72cce0151710a935a1ddbe1185a0f62c07a95c080381be1b01d2a07806406c4a002109980306b010354041a8179daaa956e34ade9e5552729b9594ecb4a7a965519b2be828f6c3ca42a25574d2a9ca95de5caf2124d18f2b8c895ce64af6a65592929c9094c674afef9002387c11a3fce7b70538f525adb08a0c8159603dc21331532accb95e534aa6a25572b29da795542a7661b3aa549d496ce196e6f0ad33c130220a4c065658248ea63a15b1d4d68f456474e6638d311c5d78f4ea479b563cf571d2978e24083460b3972b9b7aacdb0467621f0b61302286ceae0a06538f822e7e119414709ec0f43138c620fe710a9186715be11c599d72f07d1703e6669fb99516d8a8f675462b6a1f354fe98a7e54542aa6a17b351f97a7de6d45e9aa114f509d1a8dd75442aaa195750daca8768546a553ac3500a87c2d84c08a1b3ab7e8011b3f08d1e845dbc29e7d9276d8450640ac26045577284c39c30f430979f8492e07ca0046f59246828f597abcd6de0eaae9953737d7c16d65dcaaeebdab82cd4c15ccd6fb20294d70ba3f08d1e045a6325c7d9273d496b6c22832056580f7a7cd1d4668a9b3494b93487c2d84c08a1b3ab7c8011c3e08d1fe74dac294dc14e3d496870379b61141902b2c07b84265e9e5bd0b28fa99704acb3b225eb512dfcb97c534b76972690f85b09811612004710423a7c11a3fce9b58521c82aad507a718481ea4b4381bc4e0ec2e07c84265eaa5c38f2f4a796f42ca3f3a5f7532e095967484b265e5a1912f5a896fe7cbf29a5bb0c9d20c81596271c6a0154b9342b4cf43e16c26044149802dcde4b670ee8f022c7d03f0d0225d1f8468f022c7a92d3ec93840345ad26b031d382906e3ddc6b139d579d1a7cd1d4668a9b3492b9c885ce852e4d21f0b6130220c81596271e5b3865b9bc2b4cf052602e9ac2918f9323f08d1e045a6325cd507a3d4969f649c9c1d8100d190a1441483322ebd031d2a5c9a22643432056589c7a6cd254668a9f3472b9c885ce816e6f25b3865699e87c2d84c08829301848011c4108e9f0468ff39ee4155718481ea4b4b81f210998ce95fe7cb02a65594d2a9a8955cbca7e5653b4f2aaaa9568d4028260441902b2c4e3fe7c9300d4978640ae9e55410998 0x1d4f1c211ade19da164a144a12af0f890ed90bf10a1b070a06c304ae0245006f0000 (i%16)
private def hints₂p25 (i:ℕ) : ℕ := packedAt 0x2786aae939f81c87c3015408e78c706e628591283a4e821f1f3fdbfaba6055d63a7b1475619e31c1b98a1644a0e93a087c74f8e3e80b4768dbfbae605d76c8e821ec494aa3b4d474fc2c8e821ec494ba3b4dc74fc67865eac1a367ed2b3fd559c33ecf95767187c3015408e786aae919f81397aba55dd72fc279a594bd1ca543e1809a030108de2a811cf18e0dcc50b2250749c8438e821f81599bfacc47cffa3a7b345584a3ac2c4c2084803605a819e30c4f29703e4b01ee5b9e463837156774ad3b84a0e92680c0423786200e129db2707667cb02425312929ca9956604acf3257b912b9a4953c7ca5f1e571932bacb95e654aee9a553512aba2952c3ca431656d2f29fa59544b4a7a5653b2729ba395353caab1a56f552ad8e94b05e76a80e06f86c09680e06f86c094333c6809e2710a9b84234b13c1552ada395366cafa5e53f452a5a4953e04acf3e5819d2bf63837156776a6559932bacb95e654aee9a553512ab8794852caa25a53d2b29da79551283a63e52f1d2962680c04237a78662b315775cbf09e69652f47294c50b2390871e0444e821e1b0483b81d8c401c9a030108dec1410901f046cfc239552ada7955544aaea6559196e90c42f817210488fc23c801200e06fa0e2606e017224286255dd71d118c5c0f8bf09e69652f47294270026285920e260101b8040da0306d9c8438e821e1b0483b81d86277d002367e11a3c08b1f66b4f53bcd7928aa956e34ade8e54d2f29fa2952c249a31e571492a7c895ce04acf3e5803100763837156776a6559932bacb95e654aee9a553512ab8794852caa25a53d2b29da79551283a63e52f1d2962680c04237a107037c3604a108de 0x133612d61210114a10ee10920fde0eeb0dfb0a3e0a0e073e060c057104bd00460000 (i%16)
private def hints₂p26 (i:ℕ) : ℕ := packedAt 0x13f4560f325074c9d29e3a7c11f40294a6bdfdc6a3f1c82ab4f2dea896fe7cbf2191307f0c30d82443e18274c106c4882ab142c8a13d84e0eb3a0879c8438f022321428bdbad525a9e8ed1b7f75ca2b38d2db0674c106c4882a9401b98c278c50b2270759c8438f02227410f90a135edcc2fee654566fa5b5fd25a9702e674768b9d3041b1220aa5006e6309e3142c8e821e4e0eb390871e044692d494768a90a12d159ba96d7d7b718c0b8dca398558b33eae30c1758629f046d08242821203f08e1783ed020905d02d0d4f096a518ab3ba189f8ab9f1e4cfa6a67c39d3edca9f553cf7e627b32f3d8a69ef544f821a58fa33f0d09f7cb4f5f4a7e39f3eeaa9f14acf5a967bb973eb8594b43e1802e0450f3080d98798406c8667da1652e17022c5754faa10485042407e11c2c04a1783ed020905d02d2d4a306a7be1f0c017022a8a01434b225a7f9a340dd2a0754d00eae80b313feaaa024bcff6a79b844cec22e9856dda140e108d844d30ade6854dda140e108d2c04a398559c61827c11ba7b80e860773b037089a615bcd0a9bb4281c211a58094730ab38c304f82374f700d0c0a67604a78c706e628591283a4e821f7f2efc0978474b1e3e591472da9e8638373142c8941d27410f8e9f751e7c23f3df819eecf4f0c3e182633ce31007d2cf568e7aeaf3d92f9ed3b81d95408c9a030108de9e1aab4667da621f0c0550239e1aaa0267d02e1f0c055023 0x10690fca0f160dd20c640b0b07e507c40764058e051c04290336027000c000600000 (i%16)
private def hints₂p27 (i:ℕ) : ℕ := packedAt 0x11205e8cb98acc68e0574b02d0d2efcfc09c3e180aa0461702290a1682102187539fbabcfe1283a63f3ef1d9f93b81d95408c9a030108de0b8110c401e8250423c8011c1b805ce9820d891055280373184f18a1644e0eb390871d043cf022321427bfba4605d2696d81496a6a04a3a965ed50e8aa577de727f6191310f8600d8244235a6b4a13e4580f73e08d9c8438f02225b97c270759e844b1e5e94f2dea596e524b6f3a5f7452d99596766cbea425938d2f3c897acb4b3f3e5f94d2dd8644c06c0b4b940e810c375c3fc3e182a73f64a0e98fcfbc767e4ee076550232680c0423782e04431007942c8469783edc02a65a0f998968e74bef365f52f2d096967c3281a74c106c4882a9427a98a1647210e3a0879e04449c1d7496b5a5b675fe05a42873a4a022f07dcc6814b41f32da0497d01d168068f4017b9ffa9cfdc3164211ac294d814b284f3b6c2f4f02227a112270759f046e92b0d4b587c9aced3562322b392141aa7ac4e5567a74c106c4882a9401b98c278c50b2270759c8438e821e7811190a0c60551a92a5b4b52ebfaa2ce9820d891055284f6b142c89c1d67210e3a0879e0446feae921419a4ab152d58e7d4b01293ea580942f07d96a51a5eac1a567f98ac24b54ae50b33ea5e0fb2d4a3695a6e5eac32d52c98ac2ca1667d4bc1f65a94698acb6960165eae52d543 0xf890ec00da60d5b0c2c0be10b830848076e0597042a02fb01f601d50136009b0000 (i%16)
private def hints₂p28 (i:ℕ) : ℕ := packedAt 0xab39e835c61827c11ba7a126750d74286e7e11ca8cff1dc0ecaa0464d0180846f05c0886200fb8a34210c5006e6c0a5b184f1b617ac50b2270759e8448e421c7410f90a1ae4e0bf2b07147697a4b58d159ef382ac599f573d06b8c304f8237819f4bfcf9d3dbfb4b00b4d6e1d0c01bac31508243579fc3f08e54e7eea33fc7703b2a811934060211bc1702218803cf0cc565b4b00ba380486976e7e00af54350f860a8cff1dc0ecaa0464d0180846f05c0886200f42b492dbbf977c322610424081a1787c305168668f4304e0eb90d07934060211bc170229e98696ccc5612a33fc7703b2a811934060211bc1702218803cf868da6b4ad370d2da98ac2d467f8ee076550232680c0423782e04431007a15a496ddfcbbe1942c4e0eb90d0786c1209a030108de0b811465e95ad662b0da36b4cfb59522856ff41ce90c4420911f8478bf1208389887c300dc02ea33fc7703b2a8118c401c9c1d721a0f0d824134060211bc17022a11390871d043c6200e7703b0846f05c08a82e8ed19456709e1d2b5acc561a1a5b7a36b4cfb59520446974250f860a8cff1dc0ecaa0464d0180846f05c0886200f3c3a56ce8696e4c561f3ed97a36cd87c305467faa73f7579fc96d051283a63b3f27703b2a811934060211bc1702218803cf8c367c8a3420c50b2a8cff54e7ee5b4144a0e98ecfc9dc0ecaa0464d0180846f05c0886200f3a608362441567873e86d0d2c9d1a1c4c506b4a8730f860a8cff54e7eeaf3f92da0a25074c767e4ee076550232680c0423782e04431007 0x11ac107d10610d3b0c090aec0a2309300867067805ee05b8047102eb01b901860000 (i%16)
private def hints₂p29 (i:ℕ) : ℕ := packedAt 0xab685acf3ad6345745560bdab9515ded5ca5d45545a1996d0555e7f0941d31fa29a8cff55689e3b3f24d0180846f15408c6200f5868d40742679a1b9ef979fecc4ffaae80ba540ed1a06cb4ff21a5912041d1355689e3b3f24d0180846f15408c6200fd24ba148fa025edd1ac98943e4e0eb250749e0444e421d81701bfb805edbfa3e8034b6bda4b51d159b69c2367d0c190d0f1d28963b3f27e11ca8cff134060211bc5502318803e09f046d042407e11c4082406a784ac1e6520f1a8b52695ad662b0d254708696dd4da964e947576a7d1b5a53da8e529a72f562cfb59555a9a5aa5b4810fa3d1238a88e1f0c055023c13e08da08480fc238810480d4f09583cca41e35168a94a69555a324e945a369ad2b4dc951be9ed135768d97ab0cb54b2a6d170d2dacfb4c4c56161f0c05502390801200d4f0a0e834fd418560f329078d45a2a529a55568c93a5168da6b4ad372546fabb46cbd5865aa595368b8696d67da6262b0b4610fa4d1139855a1f0c055023d0d10676886408104841d0686a784ac1e6520f13f506545a934ad6b3158692a38434b6ea6d4b274a3abb53e8dad2529a72f562cfb59555a9a5aa5b0f8602a811c3e8ed2f496b187d25ace8ed3343ac613c 0xe240df10dbb0c890c690c480ba90b0d0ac608db069c049c025e0087005400210000 (i%16)
private def hints₂p30 (i:ℕ) : ℕ := packedAt 0x231c903ca4c1e729a3df192a3249d252588f8236dfa36408241740b4354765906f6409ea4c158a3420c50b22d4a31e8448f02224e0eb86966cbd31e629914d4d5caa77cb531b069d57b4e7a7a6b52d352a69b17f4e9cca78e5d3c24282d554d99451a9c843a934744a0e98ed1cc7e8e28b46e57a34a8cff0c401e1f0c0550232680c042378e944b7e7d0bd6f0a8368539ba0fe5c0fb2f817200480fc23c1c0df41c4c43e1806e01655023f393a51ca534fce527ab273d4f3939fcca4febce529a3274a1fb2f840cf5920de9305628d083142c8f0222580f527075dfd2db069714b4a495a4aded2d24282b260f3a3225074c7e8ce3b3f24d0180846f559cf41ae3a28410901f8471020901aa29d0a0667502aa6807519feaad13c767e49a030108de2a8118c401f65528447382ac79a1cd0c01dea8c0e421d45a31a4d171783ee6340a5a0f997d169383adcf41b21a1e71d14208480fc238810482e81686a8b25b415539fb3a512d467faab44f1d9f92680c042378aa04631007ab6859f73acf764c4a1f3c088e0606e96d957f812ce0ab6868be9345d64781116250fd2db32ff0298181d 0xd1e0cd40ca208e507cc079a07680736070406e705b8054303ea0154012100710000 (i%16)
private def hints₂p31 (i:ℕ) : ℕ := packedAt 0x4e1860dabf0af270769503c4e421a7010c25074c7d0124a8ed79745a2b385f5d1e86cab274a98e9f14e17e15ec306d390869403b8e02184e0ed2a0789283a68ad01797fc8fa07c8d17a86cc97d80c93a604952363a7e53861836afc2bce421a4a0e92a0789383ace0219456838e9fac95242fb01f1f412bcbffd0d99e4e987ae90b284a1c85a0a3d4ac1eb315868696dc2ca9eb6d53a96b6a9b52d65aa356d6f576a794a69cbd58a56a0d556a699ad5cb54b75ed734810fd6c899d40ea1f0c410a4aa3d239640aca604416a458d2240742984b4860204b01554c7c8303381c19e6987c8a9acc4cd067ab4b635b1b0ad84ed6923a7b4ff1738d9db45cdd602333395a39bad1464e4a652175ba49d6d241583d6071ce828e1d7c7d5663d2af1e5298f198c784b63be5f1d92b8ebd5c7554e3a7531d1558e285c5b4362761f0be530222c815cb54f208a98f92580a9a40c81c19e0c0ceb0bbb4046922a6c33d61b9cafacdd7963273b637778d9e0c5cdf6266913b6087f8bdcb5531f2a79012580a9a40c81c19e0c0ce899a846cf3a7ac49637a98b9c3585e826ebdb193aa9caff4ed8462a6d5011b17f8c3fa95e7321e62b5968e94a69555a335ad3daf69f95a82ccd6ab56d3b5768d97ab0d6da3e5aa595368bd4b4e434b6a62b0b0b2a687d251c28e8df807c0bf700a9b78549c61105c0fb2f817200480fc23c1c0df41c4c06e910a00e059a43670a0b342d8f02225a9463d0891283a49c1d71f3f8d3a4654d1d73a90f2d466aaa3b67d222928e14b47197a33cc51a34a9175147486965d351cb469159b486c4a3fe652170e8fd1d3d390a0a53d1ce481e327a422b51f55e380a747874a252680c15408c6e0170f8600846f0c401f05c42aa7c11b410901f8471ca1125e0fb408241740b4ad47c55023c5750ada10485042407e11c768501783ed020905d02d0d520cb39f046cfc238810480d520b80545c42a4df0872c52016a518f4224500eea7a53434b32a695131498a8a53d352965a92d494a391a214bd25f3a979994bacda5de8d2faaa953a54bf92a318c401e1f0c1578e02b51f14e8f0aa0473eea15a2e07dba4310be05c84122400901f8478381be8389887c300dc02f00f817ee01536f0a938c220b81f65f02e400901f8478381be838980dd1f8dc02cad47c55023aaa54e6d2ef329759d4bca8a53d4d2a0a01dd2546391a2116a51a629312f49796a4b43e1821a59982e21553e08da08480fc238e50892f07da04120ba05a56a3e2a811d552a73a9799f4bda8a53d4d2a29e94c500ee92a31c8d108b528d3149897a4bcb525a1f0c10d2cc 0x1d871c431ad519671724136711cf10370ea00e6d09e209080843056d047e02150000 (i%16)
private def hints₂p32 (i:ℕ) : ℕ := packedAt 0x6cc249b616535b30b29c84937f6108de0bd2d9da92e70bf0af618369283a4e421a7010c280771383ae4a8c91d3d5a2a68d0d342f29cd23443bea7447cfea501ea54a3e2bd2b4be96a634b30da5896d2bcae956430ca7503a2680c43e18a8f48e10a4a2c81594c088ed497385f857b0c1b4e421a7010c270769503c4941d2500eea2ab050d57e3e7fb7957192a33c74f624e92f23446beab9ce1860dabf0af2a0789383ac941d27210d380861424f6fab2f2749892a3447cffaf2b2b1d3d9a2ac250d60e70c306d5f8579c8434a81e24a0e9270759c0430a127d272ccbc976514b664a5971d2c7be97747cb22865b1385f857b0c1b4a81e2500ee380861383ac941d27210d92a3348d116f2a854352a93a4b5f55123e7f91d3d7a2a95ce17e15ec306d250749c04309c1da7210d2a470474f8ef2eb31f405a1b2b4951de8ace37d75b284a1d5a94f5b227a9a4dacd2942e952574ab2186587c311d40e89a03010a4aa3d239640aca604476a4b9c2fc2bd860da7210d280771c04309c1da540f125074d1541246889795138f9fdc9d256faa2b4350392a32c74f5a70c306d5f8579383b4a81e27210d380861283a4a127f7d2b2bc95847ca5e4a535452a5a195249ca6e3a52d385f857b0c1b4a81e27010c250749c84349c1d72547593a5450d952f2e5f1d3e1a2b37df5cc63e80650943a9528eb644f5349b59a5290c32c3e188ea0744d0180852551e91cb2056530223b525ce1860dabf0af270769283a4e02187210d284a095237e3e80d254788e9f250d95ef2edd45672bebb7c3e9503c49c1d72546993a4cc7cffe92b5732a4cadd286ae93d051c355a4e284a1eb644f5349b2186587c311d40e89a03010a4aa3d239640aca604476a4b9c30c1b57e15e4a0e9390869503c49c1d67010c8e9f2c9d2b28ace7254798fa03de5e02faf03436589c30c1b57e15e4e0ed2a0789c0430941d27210d8fa0849d306f2ffb2548ea1b32c74fcefb01b45681 0x164b161915e715a212f9118b10320ed90d6b0aec097e082505bb0477028801440000 (i%16)
private def hints₂p33 (i:ℕ) : ℕ := packedAt 0xf192a3ac9d2a2a51ea838f84209355e380ab4db5ba50d5d27d569391321a5b8f6284a1cbe96a1b4b12da5795d2acc6966b34a5a9a4d0cd2e42e9a61f0c5ad9132981105a9a270bf0af618369c0430941d27210da1b2a5e5cbe3a7c34566fbeb98c7d00ea54d53387dabd3593a9b0a128731a59acd29436962174d3ad91387c314be96a574ab2da57d4d2694c0882d4d1fc4783ae481db3861836afc2bc941d27010c39086c74f8ef2eb31f405a1b2b5159c6faeb7498828f5aad276ae93eb74a05094398d2cd6694a1b4b10ba69d6c89c3e18a5f4b52ba5596d2bea6934a604416a68a543b0879d40e89a030108b69094c524a9e8e54c530220b5344ef9e844a1a51f492a7a6954c2a7e0ad4ce77a6687c300c401c334b92ccd68776f8461e8448b41ec580f52a079c84a62a6559992bdc895cd24a9f1e571972bcca95dd34aa646533512aba59544b4a7a5653b2729ba7955634ade141b2520f284d2f8c401e534bb25a5e0cd2e1de99adcf822e781153dcb3340515ad0eedf08c4b82c35420cb41ec580f52a07994277242531532accc95ee44ae69254f8f2b8cb95e654aee9a55323299a8955e2cada965512d29e9594ec9ca6e9e5558d2b78506c9483ca134be57a6518803ca69764b4bc19a5cee540f12849f94e9919c286d10b73e08b9e0454f73be4e0eb9094c434a3f1256b1f297a6954e2cada965512729ba795542a7e21f0c04d0180846f496978334b9cc4706324833ad04c96c266b90ac370855c5d5ae6eaf6f755a0b1fd584890a188e8158d1d31a0c30dcc2afa1a62380859f82f0e6162da14b6109ca02789b210cc106c714be394244a13cc559dd188039d29863652b552adbd958e6cafa86549452a5a8955c8ca672a577972bcc995d54cab33e5819d2bfbe959464a511e0a84a0e98e94b1383ae3e52e4d0180846f484a60f022b4b2a83e08b9ee77e9a5534f2aa4f82e1683de5a53c5c0f8138010203700c1b6040da84c3c86c0965e53f2b29d2ccf2c34a3e153f019a5c87c307311c18c920ceb41325b099ae42b0dc215737e9a0b255c5f76defa51b2958c94a23c150941d31d29627075c7ca5e425307010ba1952514a97988e0c6490675a0992d84cd721586e10aa0b24dc5f72defa3737e88d94ac64a511e0a84a0e98e94b1383ae3e52f2129838085d0ca928a54bb18026e509e65f85794a9509c1d67210d380861283a6425310d28fbc95847ca5e46533452a5a19525ecac68e54d1d296854fc15a980334b84d0180846f4dd7e15ec106c270759c8434e02184a0e9284f3484a621a51f792b08f94bc8ca668a54b432a4bd958d1ca9a3a52d0a0d984d2f9483c89a030108de94d2ec96978334b91367c11a4008e37e248ff13597284cc942d2c9d69e4ef4d276a993ce54a0ea24f10f860 0x1f841d5a1b051ad119e1187017a716c91432110c0f0d089f06de051d0333011d0000 (i%16)
private def hints₂p34 (i:ℕ) : ℕ := packedAt 0x34500ee08068c9519a4688b031c3828fd84e9e250e5e8cfa948d98c9ed665063d8320565a0f62c07acb519a165350d2cb95a32c903c8a74f729a79acb01ea188f695cdbc2e6621b32e1101a2d4ce942768274f129a7991d3d47b0640acb41ec580f596a22c34b2a165332b44494d3cccf1483b8a2034100d192a3240c7060a3f32344309d3c53b85a9a270c306d5f8579283a4e421a7010c2807713a9b24a8c9474d28e9ead15346869a1794e691a21df53a23e7f5214169453b1da9d0ea0744d0180853a9528f8af4e653022f62dc7b4b519a1a597240f20cd2e14c0882d4d10ba692bd39fb16e3da531e32d8ef86c4e8669702d4d10ba692bd39c3e8e9a5494d39407949691a48eb2d1d5568cd7b4fcad41666b55ab69dabb46cbd586b6d1f2d52ca9b45ea5a721a5b531585a30879de9be434e549a71d6c899d40e89a0310f8620853814c0882d4d10ba6992399a0dd5509ea684d5742896a0c4bd0661a59359429d7a1eea50eab68553141a95a0bead0ee174d30f862d6c898429c0a604416a6892398ac3434b6eb6d53a96b6a9b52d65aa356d6f576a797ab14ad41aaad4d335ab96a96ebdae6174d30f862d6c898429c0a604416a68932163e2b7493ada484147ac0e39d1321a5b8f6acc7a55e3ca631e12d8ef97c764ae3af571d5538e9d4c7455638a1b13b0f85f0cd2e14c0882d4d10ba69923acb47555a335ed3f2b50599ad56ada76aed1b2f561adb47cb54b2a6d17a969c8696d4c56168d4ddad91387c3114c0882d4d10ba69 0x115e10c610660f880e9b0de70d330d120afc0a370987092a06fc054c039c01b00000 (i%16)
private def hints₂p35 (i:ℕ) : ℕ := packedAt 0x1445820628101150814c96a0c68f054268351283a08c1cc49014075462e84d5721586e109380859cea2ce95144e0ed2849f14c06c5e00a180d9084cbc2ca3e825af1b2c6a296cdccbaaea5d7212c992965c249a63258b1d2c7b797450cb60274f017a89d01819aff16a808c784265c274f0180d98594785ea26124d27010b39d45d0cb628a5b3445820628101150810c844c6022434114338549ec2d8d020878111358551dc2c56025ec213b578313141c4980ceb6134560972ec2b5560c26e10736083120398941ce440e4210719c40d08e0240c0cd0781b50cb62ce5cb4d2dd7f8b54f4b56e25d37d2eeb4973474b1e3258b152c3808c7dacb9eea5d7392d38b9624ecb52fe5df492db8d9634fcb5a825af4b2dcb29720bc01598282cf07727076c84b24ac1e5292cd2849f1503c64a597272cc2980d8603661651f09269084cb84e9e02f513872f1c49791d2a2b341a0680f036390869c0432865b0ff16aa396d40463e8a5b21099709d3c0603661651e17a8984934e8a13b41099791965432a20a550813a7893baca2955d147528bd2d445ada29ead17f5a8c12b44498a23cbd11a453b451a8787c2d84e9e0ad4f852a8485d42e8c0c70e0a3f72ca860880d04e9e248ea63a15b1d4ac8e9ccc71a6238baf1e9d48f36ac79eae3a52f1c481068c1672e1f0b656a7c85d42eb644aab36d2b9b70880d04e9e34509e6084cc434a3e4653213a782954268213305093f85540c36a0e5750413a78d04265ca127c13a78d1403b82136f2344492a3284e9e3ba4b4fb23a80acca0cc64f6b727557939d5c9c6b644ca203410a7f87c2d84e9e0ad4f92da7e93bd4a2f4bd11a1f0b613a782b53e68c1672e071cf559b687c2d84e9e0ad4f92da7e 0x13c1137b10a80f91094e080b0788061705a603f6037302f002ac023e0110009b0000 (i%16)
private def hints₂p36 (i:ℕ) : ℕ := packedAt 0x114381be1b040400901fa255075387ca9d680a1b3c1dcb528c540f12b079535b7a6aba9a37e9d7bf5e55f9712fc5937e4cfbf3d75e3e96d8d0f323abbabed5fb24e96351716cebf354dcb666b718b7e396aa04a53936efdb31593d6bf5685fa2b2ed94f6fba4b56d6ddfa5eadf55743b90995bea6a1b51a5301b09d3c05ea26287037c360808011b3f08d04e9e02f5130da8da7b7dd4dcb6a2e2d0f323a962c842b9855db0296e58fc6d85e200470ff53634114180871dc2dc652c2781153dd4c14c06c274f017a89a63a1291c0940f04a9161988812743864be8595e42c4fd0a77a853210484c41fa600fc2e07d962a490208a5f02e730ab390554381bee3a930d82004e9e21b51a3700b0bd44d4a8c0438ee16e781153dd4c1f2a6505520d01436783b9503c4b528c560f2a6b6ed3dbe64e95f937cd87990cb54fa5eadb897cba5b62d4dcaf3af9f496acc5be64c564746fa5294e2d0be8d45c533efa1957ce86d4694c06c274f017a89df0e82286c101002367e11a09d3c05ea261b51b51714a9b95c3cc869edf352859097720abb88559cf52f1c3f85ea061a1b4296e41556c842b8c25cb152c5301b09d3c05ea266cbc1f6e81582e84cb96a513e0b9365e0fb2e84cba0561cc2aee5a944f82e166a4464226341143e08be7df42a2e29a17d1d1be9525ab33af9f5372ba7b7cd35b74b528d0f3210bd44cbd5b61b51b3159196a9f47e200470ff526e215673d49450e06fa003043608013a780bd44c36a36e0e06f86c100fc2385e0fb40c34174264274f017a8986d46d47b98559c82aae3097cfbe8685f473af9e5a9468799085ea265eadb0da8d98ac8cb54fb7c3a08a1b040400901fa254274f017a8986d46d45c52a6e570f321aaba0d31d0948e04a0782548b0cc44093a1c325f42caf21627e853bd4298c41fa600fc2e07d97c0b8381be1b0403f08e210485030d013a781b805ebdf52b2ed551714dabead75e36aeeab335b69aae954dcaeb6ef9ad7d3dbbeb16a51a1e64217a8997ab6c36a3662b232d53e 0x171d1326123810dc0eb30bc80ad90a79099e092d070306a3061e055b043e034f0000 (i%16)
private def hints₂p37 (i:ℕ) : ℕ := packedAt 0x2060d60206a808352124da24aa392078956ab5bd1367c11a3f82006aa90a603613a780bd44e3a184950a18cec15b770ae69d231d6138580f59207915eab0a603613a782f07d9740b43554817a89a962c84b9f0469c42aae615772c7e1fc1003554813a780bd44d549f0468b41f27f0402e81686aa9101555512ab879484bca7e5a53d4f2aa8555284e9e02f513305c0f92c07b96eaa5c82aa7c11b71cf153caaa5653b2d29e9794fd4cab33e5819d2bf2a078c9ca6cac1e52929c2980d84e9e02f5132529a85552d4e6ddf5b5afa75b77c9aae94cd6daaeeab31591aebc6ed5f5742fa35976ad7bea5b84cae7551a3aa6a795552caa25e53f0f290a8955d34aa72a577932baa4953d4cab33e5819d2bf680a1b3c1dcac1e52929c2a078c9ca6e4a5345301b09d3c05ea271256b8b2b641553c2aa96a826aba9af7ebaebc7d5dd5f6afd9335b8dbbf6cc564f5afd5a17e8acbb656ddfa006aa90fc23c8012009d3c0dc02c2f513552ad87948544aaea655932b9bf4dbdf4b1d0c24a850c6760adbb8571d61385e0fb2e81686aa90b01ea57aa02a551b7a26cf82348011c3fd5120aa7c4a0025a9460306b010354041a92946484936e9d232a68ebb74938798467521f269052d466d7a485551db3e91149470d6a47d2d1c65e8cf5947898a3469522f6a92533469a8a3a65520e6a8d55b479c5a405351cb2e909a348ad4a46e251ff3290b57477d0a44cad196ba8f527463828fbd3d1ce4953d0da8d2980d84e9e02f51314381be13a780bd44c36a361cb01e856a3e872c07a15a8f8ab542e815a6f0a93ac315c61827c11b420909703ed0208a5f02e0e06f86c1021b51a5301b09d3c05ea2668b01ea57aa0a1b46a719e0ee5301b09d3c05ea26287037c36080801203f44a84e9e02f5130da8d 0x1462133b11f8112f0ffd0e270abe09b608dd08aa034d02f202c0013e010c009a0000 (i%16)
private def hints₂p38 (i:ℕ) : ℕ := packedAt 0x15774552b992d418d1e0a84d06a25074118398920280eabc5d09aae42b0e02166e1097f8b95d5652023311d3d98c9c8dbd646e6b27455848d9dad0d60e82b042f00509d3c680c0cd09d3c05ea2740606683c05091574b90ac370849c042e82a534352a808cb3fc5c02f5122f00509d3c4c96a0c68f054268351183989519b1938fb7a9f46cecd7426b73540baaa0ca343cc565aa59315850bd44c36a361345560a0aaf609f046cfc238e215240d5720aa7dbf55fa548b8594d65d2135291b9948595a32c903c4ab56d59640d0b24e8d92b12c878b644cfb2452d8e666b4f5d64294a67d558fa0a4035163cabb1fd3d8ef3ac8fb564da9b1ec3cc4ab6c833158293a4fd358ea6ab8bb764ecab2364d91692c71af64cd6b25d004268b5642f0052980d84e9e02f5131b3ed50206ab0ac1e482a9f92a32c2ca765556a5301b09d3c05ea268b565216481e5981522bd5838ea4dbf566821203e08d9f8471035685301b09d3c05ea26ab74a917a948d9207915ea80f82348211e3f82006aa90a603613a781b80585ea268b56512551018358081aa020d4d2a45e6521613125240f22bd58208480f82367e11c2980d84e9e02f51345ab29a2c07a9703ecaf5605f02e740ad152abc381beeb0c56f0a906c10108242e30c13e08d9f84710355c82a9fd4b4052d9af5ed0795678d1b3f4cd6a6529a34966ac4b3ae959ff32cf5274a1a9b37d6d9cf42cfb2b5049aae3d559c2a2cdd97679cfb3e42ca976ed0b93677a7b36c1480e62b098b676d6b416759ef6ad0959672abb38d759d21e6294d66c86d4694c06c274f017a899a2c07a95eac0a955e5c0fb2f8173a0568381beeb0c56f0a906c10108242e30c13e08d9f84710355c82a9f2d4a34bd58352d014b66bd7b41e559e266b53294d1a4b356259d74acff9967a93a50d4d9beb6ce7a167d95a824d571eaace15166ecbb3ce7d9f21654bb7685c9b3bd3d9b60a40731584c5b3b6b5a0b3acf7b5684acb3955d9c65aa575d6748798a5359b289557a3aa686d4694c06c274f017a89a9b1a08a0c0448ee16e329613c08ab4050cf7530cf0772980d84e9e02f5130306b010354041a90926d12551c903c4274f017a89 0x18cd18ac16ab1666154f145f13ea13b70f950ea50d9e0c810b300690019c00a90000 (i%16)
private def hints₂p39 (i:ℕ) : ℕ := packedAt 0x992d418d1e0a84d06a2507411839892028ba1350755e2e42b0e821a6e109380858bc014274f10306b010354041a8240f084936c8d1064e8c7051f792566156b2b3b5965301b09d3c05ea26214883ba4c1e3dd2548791a2d54fa0eab6aa8ed9f488d2a45ea5237429132b465a7a39c92b26af2730b93facca0ca6b110158b51ac8a9d6368eb1ca603613a780bd44d5620aa7f428b955450cfa2dd3d136441dc560f285c9fca6b110158b51ac8a9d6368eb1ca603613a780bd44f748d13a4a8e9dd2345d92a45774951d64689f53e830c5aaa3b3aab0e495845c0fb2f81707037c36080841213f08e436a36af2730b93f94d6214c06c274f017a89ee92a3248d10fd4b213457949740ad4249b74a9172b465925614a41583cae0e06f9783ec360805d9483f08e146ad9035584e0ed2b0791503c50553e5301b0806896aae61e62b95694a6b44565a3aa2d15294d2a4b43555a32063950520493a516b5a7b46d3521420d7b4fe4da4e6ab91335aac4b48c951be9ed13b76a1abb46e75a5e5eac3b56a0a5b43d6da3ea6d17a1699cfb4c42ca9b16d255d69009d3c05ea261b51b28d3158496a95c3cc502f5130da8dac5c0999c042cdc212b7863b89915ccc8e8662741312a298a43a51a5b57d31abd0bd44c36a345e00a13a78 0xec00d910c6a0c350c030a5308f708c50893086106f006be0623060201cd01580000 (i%16)
private def hints₂p40 (i:ℕ) : ℕ := packedAt 0x13bbebcadfde5a78783811825911338afbcb85ea261b51a3f00fa9b1a08a0c04486422753634114180891dc2dc652c278115f52cd6815eac0a955ede15271d499f8470f823681aae2856696a5190553f53475dba49c3cc233a90f9348296a336bd242aa8ed9f488a4a386b523e968e32f467aca3c4c51a34a917b549299a34d451d2165353546aada3ce2d2029a8e597484d1a456a5237128ff99485aba3be85226568cb5d47a93a31c147de9e8e70da8d94d6994c06c274f017a89a9b1a08a0c0448ee16e329613c08ab40508f7530cd075c9a4152d1c7169018747e265364903b6435b195ad74a82b942b34a603613a780bd449f847103559d4980cacc1425d09ab46a71721587410d370849283a08c1cc730362480a038340020060a0e00f8278203700c1ac040d50106a2304b28a83f0926ba5a114147d6ea85d47420a0a0edcd0b63a7a5011918d9d7444cca327155f42cc9a18e2d0c30e85e2f0054a82b942b347e01e8b0cc7d0b2bf429cc41fa8812743864bc8589ea14c600fc2e07d97c0b8381bf0da8d0d820162a51c82aae3a933f08e2104850355995ad72980d84e9e02f513db2548390a196c0eabc395675bdf36e6fc9757f08e9f4bfc5fa3274347693808d446cf1682c8a13a780bd44ec0eabc395675cdf8a82c876f7cbbabf751da460234d1d3e77f8bec64e7e3678613a780bd44c70ff56081aaca5b286dd9a666b51ad666aeb2ced59a26ab8d4f652c5b2debd99f26cb99565dceb3062596b3ecc3a1662adb2c549a0410cd51c6b0aa1a08a0c044864226b012f3b858abc189850e04c067560972d84d1560c2bb0ad2407312839c881c8420e3370839b0418e8218470123dd4c1c6af01819a7c11b0781b206ab0e559c56ad2270769528f4a603650acd2d4a320aa7c314bb25464b5a70c64e3616539674dfaba6d43cc2a8e9a52f4c77f8b7474f568a9a3314c8b2a6f5353562e6e1954ef9ca65e853d6367632d4c6cfa7a4fd33a9e9ad414cfa1a6864d3ba2a6a99d4f3b7a715cd392769993d4cda9a6c52534eb29b7754e5d1a7b5f53a2e29c7514d790a0b55536602329694e00bd44c36a345e00a13a78ba3f08d1f42e5ac28ed41466983e166b44f559e670a9340821ac2a8f0222b012f3b858abc189850e04c067560972d84d1560c2bb0ad2407312839c881c8420e3370839b0418e82184701238d5e0303341e06c72ace27076dad3863271b674dfa3a693fc5ba3a7ab454d1b2a6f535357529f3173709ca65c6cec71e9d9a54f79fa6752d3528299f434d08a9aa6353aede9c5734e49da664f5336929a7914edd3a7c5d5396fa9d1714e390a0b404652d29c1280f21780294c06c274f017a89c743092a14319d82b6ee15c7584e1783ecba05a1aaa44056805ea27ecbe05c5d09a0e06fba056836080eb0c53f08e210484274f017a8986d46d470d04506022432113 0x207520421fa81f5d1ee81a9c18ad1351131f11f310c70f2f08040214013a004b0000 (i%16)
private def hints₂p41 (i:ℕ) : ℕ := packedAt 0xab62a07896aafeb2739a13a5db9d6c9ce320a3e3b53acd19d3534e5b3e749ad3aaad9ced44e626a7275539aa59cad24e533a7475d39ed79d5c3cc0b167412f390ca9d155ce6e667254f397a99ccca6b4ca603613a780bd44cc6af4a15d125ae5ab62d4a31523132a78d4f3bbd69e74bced2a677baf3cfd19e5554efb3a78f493b8a59dcedcf469a775573bfa89de56cf061e6079f3c8ae9e14147cb6a7a1353b7c59e24cceda4e761593c0d09e4c36a36535a65301b09d3c05ea266357b2dabe28574496b96ad8b557f493dcad9f2d74f9b6e7efaf3f5a99f0e74fb64e7a9953ead69fa53cf7e0a3e7353dbac9f243cc129a7bd513e0999ed684fbf6a7ed8b3e8aa9f152cf774718f9f8c297c61d5e322381d0548c525d7511839a535a65301b2480a4c6af4e606c13a780bd44942ba24b5cb57e5bab797d5c0bc014274f050ae892d72d58a3c1516a0c64d06a5d09a942ba24b5ca490143981b04e9e02f51359d6f4af8c9c650d2828a943474a28e9ea5cd2c6ea964ff16da0a4f9cc0da4c1e31b8c4075739541de035c8560f22980d84e9e02f51329ad328574496b96518b759b2d44597a234883ba1f2813193d86d4694c06c274f017a89b53d08a9d8444f35ccc813e6509fb104f18e0e44c0675b09a120398941cebb0ad238091b841ce82180c0cd38d5e1cab3ade95f1938cc0a5bdfd2db06971714b0c2a5cd0d2828a943474a2a6a52c74f52e6963494a3a5a525d52c9fe2db4149f93078c6e310aa0ee560f292d7294c06c274f017a8994d69c06b92d0ec1655b595483ee50acd270769583c8b528c548e3878c84c46625e32f21191928c94b465a1b51b29ad32980d84e9e02f513a1011a88290e558a3c1516a0c64d06a5d09aae42b0e821a6eab7380859283a08c1cc730362480a038340020060a0e00f8278203700c1ac040d50106a2304b2e6d8d09275bab63c6cee6bed890119c8c9cac1481a8ed0f113348e9ee84e9e02f5130da8d1f807d16acb000680283801e06c1f04f0406e018358081aa020d439085a304b28a83f0926b828fac04646226654341eafa164803b4e35b23f00f458663e8595fa14e620fd44093a1c325e42c4f50a63007e1703ecbe05c1c0df86d4686c100b1528e415571d499f84710824281aac2b07914c06c274f017a8994d69d58a3c1516a0c64d06a5d09aae42b0e821a6eab7380859283a08c1cc730362480a038340020060a0e00f8278203700c1ac040d50106a2304b20a431757ef8493f444ce6e6fc71b3c4808d3c74fa2327415f798a3b4962aac3135bf43ad4a2d590fc03d16198fa1657e8539883f51024e870c9790b13d4298c01f85c0fb2f81707037e1b51a1b04009d3c05ea24b1528e415571d49a10484ed5b87ba98285669f8471035593bbf99bdf4cda201c01f04f4609657eb798a0e24c0672407312839c8e0240b0035b09a030334001a0bb0ad6185883c0d8e82186e107395670203700c1ac040d50106a1c6b56e6fc541643b7be5c1485eeafdd47691808d3474f9dfe2fb717d78493ec64e7e367870da8d2980d84e9e02f5123f00f 0x22ec1fec1cc2195918cf17f1160215241156113911180fc10f8f0c7a08c703a50000 (i%16)
private def hints₂p42 (i:ℕ) : ℕ := packedAt 0xce480e65b09a1283a48e024bb0ad26838830334dc20ec413b7f8c1d0592aff02b193a68d9e55c5f760235b7d80bbabfac74fc23e81ba2afd618589dabf0e42165301b09d3c05ea24a15d125ae5a2d7903ebce875eb3bbf99bdf4cda201c01f04f4609622c3311024e870c9afd6f3e8595e42c4c50717e853bd4298980ce0b0033107e9803f0b81f6b61342407312839cb152c5f02e1f807aec2b48e024e61560406e07037c0c1ac040d50106a1b841c1819a000d071d4986c1023678d757f18e9f55c5f660235309283a0b233fc5fe327450521d3f08e210484f823794af840d56436a34ac1e45301b09d3c05ea26535a650ae892d7283ebcd055ecc30b13b57e1c842e875eb45af28d9f6bed03559a3afa3c0889583c8a603613a780bd44ca6b4ca15d125ae567d7483ebcd055ec7210ba1d7ad16bca4e890cc43864bc8589155baf50a605801962a5b0c282e615666d7bb8ea4d9f5d284121c4c130003401f5e7011a90106a0103540c1ad0521d0406e424a0f295f0fa1657e8539883f4c01f85c0fb2f81707037e1b51a1b0403f08e206ab0ac1e525ae52980dca6b4d055ed43af509d3c05ea26a4cd59e68104358552c04bd5825caf062558309301b4881c8420e32407312839d6c268470123d85b2ec2b41819acc14137083b084ecd820cff1838b9c15adf1b0f0474164abfc0ac64e9a36795657ae9eb104ed836e2fbb15366808d6df602e72bf5677b6babfac74fc27ec67697bec4c150bc014274f0c50b2a9335679a0410ee1626b0aa6109dac04bd5825cc5071578312ac184980ce440e421071920398941ceb6134238091b04197615a6e1073a086030334e357872ace3dd4c5bdf5a3275aff18ab2bd9474fdeeaff33d6278b9c4dadf2a7ec6f7f81a8d9e8da5f0a2a6db717e1bec08dcdfb68ed4339601b3bdd50593a76c29011b4c9c1b0bc014a15d145af207d79d0ebd4f823681aac2b079496b94a603613a780bd44ca6b4e777f337be99b4403803e09e8c12cafd6f30c2c4ed5eec507126033b30504901cc4a0e7c3d6ead84d08e0240b0035d8569b841ce82180c0cd395670203700c1ac040d50106a002b8ce35ad89825b7be6dcdf92eafe11d3e97f8bf5c5f623274347693808d4424a0a0a4391b3c5a0b22a2c333255e8fa1652857433eba68b5e40faf31f807a2049d0e192f21627a853162a59cc2ace3a933e08da10485fa14e620fd3007e1703ecbe05c1c0df86d4686c100fc23881aac2b079496b94a603729ad34157b50ebd4274f017a89adc3d85b1e0446b3cce1527b0b63c0889a0410ee1626b0aa6109dac04bd5825cc5071578312ac184980ce440e421071920398941ceb6134238092ec2b4dc20e7410c660a09b04181819a71abc395675c5d0b0ee957f748c4ba5cfd8aecee7d4768c8d9df595cf672be54163eb5ba0454d7a327353d618beba3c5cdea0234375744b4b9fdcdd0e3a7c4ff1789db02dbea42a953f0baa71780294c06c274f017a8928574496b959f5d345af207d79d7a1503c50553f4b650dbb34ccd6a35accd51653aeb2cd4d9536acd1274a09aae353d94b5eccf9365ccab2ee759829aca30b2a4abb2b43cc4e92c9f31583aab2ad6595f46cc79f661d0b3156d960ac1e525ae52980d84e9e02f51329ad38da06ab0fb5c156c540f12d4a352d9436ecd32f55f99ad46b599aa2ca75d659a9b2a6d59a24e941355c6a7b2962d96f5eccf9365ccab2ee759829aca35765687989d2593e0a40555655acb2be2596b46cc79f661d0b3156d9625b57d31abda15789d04368f5e07303686d46ca6b4ca603613a780bd44942ba24b5cb45af2ab22d5604bd580a15d125ae5ab62a07896a51a9adbfaf7f79aaeaccd6e716fdf5976dcabf8eddfe6aeeb1b57f8a5b63e7dfcea2e2f5372eaebc841484e92d5d274b2d1bfacbd5c29edf9ad7f6aaba243cc9342fe99d7f2adbbfdd2bbe5b57d31abd3a086e4eb5b135aa7010b86d46ca6b4ca603650ae892d72d1ebc0e606c13a780bd44d60cc5616ad8a81e25aabfa6b6f4d575346fd3af7ebcabf2e7df9ebaf1f4b6c687991d5dd5f6afd9274b1a8b8b675f9aa6e5b335b8c5bf1eddfb75afd5a17e8acbb653dbee92d5b5b77e97ab7d55d0e0a42572aec8cd7746ebb5721586eaeb98d5eca6b4ca603650ae892d729cc0d8274f017a89 0x308c2de5284826da234a1f7c1a5e140413ce0e970bac0b7907bc075c039f037e0000 (i%16)
private def hints₂p43 (i:ℕ) : ℕ := packedAt 0x2a4cd59e681043d85b1e0444d6154770b158097b084ed5e0c4c50715609713019d560c2b61342207210838c901cc4a0e75d85691c048d820c7410c37083b305041819a71abc3956762609e72bef717da8b9bfd9decedef9f1d3ed8d9e3d95eaf0f041737e68a9b1dadf0ed2f77011aa9fb1850591dfe3017d808a3b4bc64e8e76c153d61dbabf95fe0485e00a5301b09d3c05ea24a15d125ae567d74d16bc81f5e75266acf340821ec2d8f02226b0aa3b858ac04bd84276af06262838ab04b8980ceab0615b09a110390841c6480e625073aec2b48e0246c1063a0861b841d982820c0cd38d5e1cab3a3274b3b60ca0b24dadf1713053697bdb2bd6c046b2ff029677b58b9c0dc5f71fe30515365b7be8cfd8cafb015737e88e9f7e1e08a72bf33d61fa3b4cdd5fd2367922f0052980d84e9e02f51250ae892d72b3eba68b5e40faf3a9335679a0410f616c78111358551dc2c56025ec213b578313141c55825c4c06755830ad84d0881c8420e32407312839d7615a47012360831d0430dc20e0c0cd38d5e1cab39982831535cbeb8cd1da2a72be169712bab8bcf585a76c0773716b8b8ac6cef2cae21193989fb14dadc4dfe2ed8771ca0b1e474f820233f6f714c4b8ed9dc462e6f17f71a1780294c06c274f017a8928574496b959f5d345af207d79d499ab3cd02087b0b63c0889ac2a8ee162b012f6109dabc1898a0e2ac12e26033aac1856c268440e421071920398941cebb0ad238091b0418e82186e107660a0830334e357872ace808d059dca2dee571d3e18d9dedfdcca2e6f389735beb98d95c9e72be33d617b9b96dd5cbad6e551535d9db024fd8ab0ee694163da3b45da5ca5fe2ef7172c8c9cc8bc014a603613a780bd44942ba24b5cacfae9a2d7903ebcea60f559e7c11b33854a06ab0d0209a3afa358551e04456025e770b15783130a1a95825c4c06755830ad84d0881c8420e32407312839d7615a47012360831d0430dc20e0c0cd38d5e1cab3a3a7c73b606b8bab64dd7ee6eaf75758b2ba8c0468a3677f3d6199fb165bdd562e6f76b7547f8bcd058ff2aec11535fa3b46ce57ceceea569753bebadc64e6ead61082af6178029583c8a603613a780bd44ca6b4ca15d125ae567d74d16bc81f5e79fb09a1d7ad499ab3cd02087b0b63c0889ac2a8ee162b012f6109dabc1898a0e2ac12e26033aac1856c268440e421071920398941cebb0ad238091b0418e82186e107660a0830334e357872ace8b9c05cdf9e023573f631b2bd64ed82ed6f8941648bfc09c64e92eafe787821bec04c6cf2272bf1677b4c4c144f587ad2f79153647f8c0dbdf423a7dd47698b8bed8bc014a603613a780bd44942ba24b5cacfae9a2d7903ebcea60f82367aacf40d5619c2a7475f4681043c0889ac2a8ee162b012f6109dabc1898a0e2ac12e26033aac1856c268440e421071920398941cebb0ad238091b0418e82186e107060669c6af0e559d1b3cebec0759dededefa77f8179eb126560ee2e70d4769ec9c19474fd2e2fbd193aa9caff4ed8462a6d5011b1b2bd7dcdfaaeafed697bfb5be3bfc61e82c973f634d6580d6ec1e6760dafb059ad826d6c0f6f6042f0052b07914c06c274f017a8994d69942ba24b5cacfae9a2d7903ebcd055ed43af5a983d5679f046cce15281aac3408268ebe8d615478111580979dc2c55e0c4c286e5609713019d560c2b61342207210838c901cc4a0e75d85691c048d820c7410c37083830334e357872acec9bc2474f96deef93f62e808d25a5dea2a6c33d61b9cafadaddee3273b67779b2bbc46cf06faf037177d8b9bed059068ed1f95785b9bbf4ed821fe2f77577f178029583c8a603613a780bd44ca6b4ca15d125ae567d74d16bc81f5e682af6a1d7ad071304ccd0b6ca54c1f046cf559e81aac33854e8ebe8d020878111358551dc2c56025ec213b578313141c55825c4c06755830ad84d0881c8420e32407312839d7615a47012360831d0430dc20e0c0cd38d5e1cab3a2a6b3755b99ead2dc56ded6b6b675b3b7adb50569ee6b71475aabfade5956ca7eb4d3b5a48e9ed5a56d1fe2e7875bd8d9db45cdd6fab77935bf808ccce568e327242f0052b07914c06c274f017a8994d69942ba24b5cacfae9a2d7903ebcd055ed43af5a0e260999a16d94a983e08d9eab3d03558670a9d1d7d1a0410f02226b0aa3b858ac04bd850deaf0625609713019d560c2b61342207210838c901cc4a0e75d85691c048d820c7410c37083830334e357872acebabfbd9dee2e6fd71d3f5bec07dc5f7e3679f4769f8b9c3bfc6227ac4b011b2b4be0595ec2d6f91395ff8a9b5c64eae76c253f635b7bea61e09282c9993833178029583c8a603613a780bd44ca6b4ca15d125ae567d74d16bc81f5e682af6a1d7ad071304ccd0b6ca54c1eab3cce152681043c0889ac2a8ee162b012f6109dabc1898a0e2ac12e26033aac1856c268440e421071920398941cebb0ad238091b0418e82186e1073e08d830334e357872ace40d565a5742e6ba9755d57f8ba4e570676b85675cfbfaebc54d6a7ab876f5d28b9bb51d722cab9d715d38c9c9dad7463a7b77d5d6808cd61d7623676fa35dda0ae2cfd71326bb42f0052b07914c06c274f017a8994d69942ba24b5cacfae9a2d7903ebcd055ed43af5a983e08d9eab3d03558670a9d1d7d1a0410f02226b0aa3b858ac04bd84276af06262838ab04b8980ceab0615b09a110390841c6480e625073aec2b48e0246c1063a0861b841c1819a71abc395676560f2e2fc13f6368c9d65adf26cef733b613babfc595ec6e6fd993835b4be0c5ce2272c016f7d58d9e85059368ed417d810bfc0cc046ce3a7ed3d6268a9b63fc6245e00a560f22980d84e9e02f51329ad328574496b959f5d345af207d79a0abda875eb5f4781113b858b084ed8a0e24c0675b09a120398941cebb0ad238091d0430dc20e0c0cd38d5e1cab3b455f36f7d68c9d6bfc62a3a7ef9583dbabfcdfe06a367a3717e1bec08dcdfb68ed434164e808da14c06c274f017a8928574496b959f5d345af207d79a0abda875eb5f195694d1b4d518430eb5fc71b00a1d7ad5e4046a5fe2ff94af8d1d7f83ebceaf1fe307011ad 0x4576406d3b64365b31522bc726be20a01b3f15780fdb0a140489013500ab00360000 (i%16)
private def hints₂p44 (i:ℕ) : ℕ := packedAt 0x3090838c881c9153588b9ba4c251a5b63a17a8986d46e12207210838e2e6e51535694698ac74b54ec2f5130da8d94698ac6cb54e82f5130da8da9335679a0410f616c78111358551dc2c56025ec213b578313141c55825c4c06755830ad84d0881c8420e32407312839d7615a47012360831d0430dc20ecc141060669c6af0e559c540f1b3ab550d57ecaad36f56db4ab5e255de3676917373c3abb4fd576feae8ff171b8ab740465e3a7b1274978a9abd1d58692ac53b55bb5ab65d55c296ac74d564b9ab7d0557a327217d5739eaae4e55685e00a5301b09d3c05ea24a15d125ae567d74d16bc81f5e75266acf340821ec2d8f02226b0aa3b858ac04bd84276af06262838ab04b8980ceab0615b09a110390841c6480e625073aec2b48e0246c1063a0861b841c1819a71abc3956733050672afd3b57fa4ac33fc5ca2a6b13f581beacbdd565312b376758ebfacc4f56030eb354b587808cc5356223a7b319391b7ac8d95636d6b2173593b8ac945cdd23676b41582b4ac7d1d6166162c54b1887d8bd0ebd45e00a5301b09d3c05ea24a15d125ae567d74d16bc81f5e76a7a1153b0889e6b999027cca13f6209e31c1c8980ceb61342407312839d7615a470123a0861b841c1819a71abc395675bd2be32719814b7bfa5b60d2e2e2961854b9a3a515352963a7a9734b1a4a51d2d292ea964ff16da0a4fc983c6031c71b8c42b07914c06c274f017a8994d69942ba24b5cb45af207d79d69d0430dc20eba13438d5e1cab396f0c747315b89915bcc86e6647011908d981c74c1282625753247f8b5c64c08a15d125ae5a2d7903ebcea4cd59e68104358551dc2c56025ec213b578313141c55825c4c06755830ad84d0881c8420e32407312839d7615a47012360831d0430dc20e7ba98060669c6af0e559d3b609b5bc6454d8a7ac397d791c9bc9c5cdfacaf1395794b8bc73fc5f2cef153f62fbfbc95a5e2e72bed5cae2458663e85976b62bb7b1444093a1c325e42c4fd0a77a8531883f4c01f85c0fb2c54b17c0b9cc2ac1c0df71d4986c101082427e11c3e08da06ab50553fa16ccd2b674ad41eded8b335acacb615cdb1aead8f4f6bda0b1cc6cee6a6d7f516be808ce464e56aad810b2a8a3b43cd572ab6d87af6d2cfb65d5db063a7bba36cdd6b68ea5b3f3ad954ab11a6d89d26c4a1b51a2f0052b07914c06c274f017a8994d69942ba24b5cb45af207d79d0ebd6a4cd59e68104358551dc2c56025ec213b578313141c55825c4c06755830ad84d0881c8420e32407312839d7615a47012360831d0430dc20e7ba98060669c6af0e559d9583cb8bf04fd8dad6f93677b99db09d95ec72706b697c18b9c44e5802fb0217f8199eb13454db1fe3122f0052b07914c06c274f017a8928574496b968b5e40faf3a1d7ac74f768ed0f19395808ce46cee682c73756c7b9b635bdb14f823681aadd2b676a5b3f42d9929ad34154fd55b02165512b507a8b5f67db2f3ad95596c2abb60e8db369ed7b536bfa5588d36c4e936255f39583dceb6568db373ed974f6bdd0b6620aa7eaad81536bfa8b5f42caa2956234db13a4d896622049d14258870c946827be8595e42c41e0e07e853bd429816006620fd3007e1703ecb152c5f02e1f807b98558101b81c0df71d4986c101082427e11c3e08da06ab0001a082a9f0306b010354041a90119d82903ccd6b75add3b56eca8b6ad65b66b6db54f6d4aab6be7db92124ed576d885954d7db7342dcb355cbceb71eddbb6a6dad11335aeb6de8db9b5edd50da8d2b079496b94a603613a780bd44ca6b4c1f5e798881274509621c3251a09efa165790b1078381fa14ef50a6058019883f4c01f85c0fb2c54b17c0b87e01ee61560406e07037dc75261b040420909f8470f8236000d040d56018358081aa020d44154fd45a9202337a16b388999eb5ae2bed570520585953d6daa6a6d4b596a8abb53e8dad29ed479d6b1cfb596d5aea6ab9309274aab536ddaee66b575d6aad7b5cc36a34ac1e525ae52980d84e9e02f51329ad307d79d499ab3cd02087b0b63c0889ac2a8ee162b012f6109dabc1898a0e2ac12e26033aac1856c268440e421071920398941cebb0ad238091b0418e82186e107060669c6af0e559ccc141b5b7c46ceeededf387702bfb804f58563a7bf3f6287f8bac54d6e76c05696f78b9bbd95bd682c77395efa3b44df5bfeeadf9736fbc4b81dc5beaceded19397808cf53ac405e00a5301b09d3c05ea24a15d125ae567d74d16bc81f5e743af5a983e08d9eab3d03558670a9d1d7d1a0410f02226b0aa3b858ac04bd84276af06262838ab04b8980ceab0615b09a110390841c6480e625073aec2b48e0246c1063a0861b841c1819a71abc395674ed826d6f19153629eb0e5f5e460234b1d3e6b9bc7e4de4e2e6fd65789cabca50590ae2f1d757908d9e15bde35fe2f91939eb3bc54fd8befef256978b9cafb51da42b961559b0f178029583c8a603613a780bd44ca6b4ca15d125ae567d74d16bc81f5e79fb094157b546c32a7617a1b0dced8750ebd6a60f559e7c11b33854a06ab0d0209a3afa358551e04456025e770b15783130a1c55825c4c06755830ad84d0881c8420e32407312839d7615a47012360831d0430dc20e0c0cd38d5e1cab3a32739011a3c9bb9d05901fe2f53f62da3b475d5db6e2ed7957749cafa4ed81e2a6c11737cb3bb3c74f92d6ed369768b7bb5595d9ae6ed93d61abebb7c6cf005e00a560f22980d84e9e02f51329ad328574496b959f5d345af207d79e7ec25055ed51b0ca9d85e86c373b61d43af5 0x3e963de73d8c3d2c3ccc374531a92ddb2c1a23361c891b571639111b0be805ca0000 (i%16)
private def hints₂p45 (i:ℕ) : ℕ := packedAt 0x2fcf422e7d0c0700a9b7853dc612edb08a2c045b72cb73a3c34f1cecd8f05347372a3bb991df4c82d5f9e845cfb658d814c6f0a836853a9e39d4d1cdca8eee4c7732e3bd991df9473d85ed2c7329a39b365e0fb8fc4108f2004726cbc1f6e81582e84ca7c170b212ee6157710aae7c78b423c79d1e1988e2de200470ff2ce7c1173c08a9ee599b429ee2152700a8b5a1ddbe118580f5918df63c76b3a3c34f1ce948e0e6c78296399511cfa68e6e4476ea63a1971dec68ece6477f460637f051f7ad12c07a95ec94a955ede15271d499f8470f823681aae4154f9403b34e91953475cea43d551db3e9114b471aca3c4c51a34a917514748594d5351cb2e909a348ad4a46c8d1073290b57477d0a44cad1964282927463828fbd3d1ce4964995ad727d8c96ac8a5f6470fb212980dca6b4c274f017a89adb680a11eea619a0eb5d47ac3a3f62d202b68f33546a99a34ed524b5a91f49470d7a4864d20b6e9264ca6c4a82b952abdbc2a4e3a933f08e1f046d0355da948da5a38e56b5e535a7a548bd0a44e5d2133e91131468aca3c55d1de9a8e5a348aa7a39a0aa7eaa8ed53475a8a3a42ca6a1f6439d487cca42cad1964e8c7051f7280764850509f6325ab2297d91c8d106496485301b09d3c05ea26367dae140d5620aa7ca81e33341b8594c53d092aa84f53426a6a11d5d0a2a284b9f436cea1acd50736e8815d42ba4a10d650a75e87b5b42ad0a1be8d0e262835ad43c93a0aed50fe401da560f294d6994c06c274f017a8987d9093ec64b56452fb23ed27d8d49519e428325301b09d3c05ea26a4cfc2387c11b4157b3885550354953b0bcfd84b942603605a540f12c07b9383b4b81f2560f6a4ac349d2624a8d12b4fca5ac3d356233ab435158a90a0d50d60e9eb132d521985904a6b4ca603613a780bd44c3ec86c5c9c1db25308a1989c84c18a603613a780bd44c10d215266acf3d85b1e0444d6154770b158097b084ed5e0c4c50715609713019d5763cb613424073110390941cebb0ad238091b0418dc20e7410c060669c6af19828272ace07d79b3eba4a01dc4e0ed2a078c6cecf0ea8f6f53e92a335a54f2e2a7f234459fa9448506282a531938fc4aa45354be72a4b4352a9ea93c9d25afaa8973540baaa0dad4f62e6e5011968e9ebbfc5c292a5b4b52ebfaa2cb251a7763f67b1cb2d8dc36a345e00a5301b09d3c05ea268f57345ac094698abfcb54982f5130da8d 0x1b861a431954190918ec18b617c715b2158011d80d0a09f8097206c6062700600000 (i%16)
private def hints₂p46 (i:ℕ) : ℕ := packedAt 0x19f03b3db282d07b1483c8af67854b3bca8eecb470e56385291c1928dfc846f6aa3a3165908a6e0a636852db328e7bb393e08da06cb8fd65452b3272594846c986e0165a9460c06c85ea24281a613b3a4c82d5547460a36b091b7978e243c6ea163714f1ce838db4c4717463c94b1cca88e7cb470e9a39b951ddc98ee54c7421a373971de2a59ddfa0046cf422e7db2c3f595378545c82a8d81496d0a50dc02dc211ad70844e82d96a518301b2580f40bd44896ce0281a613b3a2859b9483c4ac1e7551d1828dac246de4e3812f1c4878dd67c78a163714f1ce838db4946fe523839b1e0958e14c4716a239f2d1c3a68e6e54777223b7931dca98e84346e7323bf20603602c1ae15a78848dbc2c6e20e36d20603602c1ae15a780959c0903d0b210850b37290789583ccab66cd69ad848dbe3c76a4e381491cb858dc41c6da4a37f291c1958e152c733223b78d1d9818358081aa020d40bd4485034e0a36b091b7838db40c1ac040d50106a04eccc481e04e0ec0bced4846f64637d051b5848db9583ce52382520f1928dfc9c70230b41ec580f52907915ecd64a37f291c1958e14b470dbd2c54b1cccc8efd34736a239f531d0cb8ef654777643364c17a890859905034c276664e0ed29d9a4846f60a36b091b7858dc41c6da4a37fb21901b0bd44842cc4281a613b3327597c146d61236f0b1b8838db4b905835c2b4f1091b7838db5c1d660500ee27076c846f64637d251bf0c06c85ea24281a7071b6828dac246de1637172d41453c4d7b441e1a535c510170759813acbd2e0b18b1d8958e14b470c301b217a890a069c1c6da0a36b091b7858dc35a6b6963998f1daa48e5e34767223b79a0d0137f8b340462c301b217a890a069c1c6da0a36b091b7858dc581c042ce6162741103b0889e42e58026ec21386a0a32fc1ada61044c0eb250751403b24237b231bec78ed4746ee3e3797b1d6a48e5d0c72296399451c9bc8ead1c72afa3af8d1d9 0x164516281535120f0e410dbd0bd40b2b09da08820769068f062f05190319023f0000 (i%16)
private def hints₂p47 (i:ℕ) : ℕ := packedAt 0xa335420da735e500eca4b524850964689d8d71ec7b8fd4258b3369797b4ca9da6d81c042ce6162c01376109c2fc1ac941d4500ec3b0889303ace822121426bdb9850d952f2e5f1d3e191a27d159befae63496a58fa01d1da2ec0e0216730b16009bb084e17e0d64c0eb280761d8444e82204a0ea8fa045ee002468b17d806a4b57d0d97af2ff54567990a19d1da563a7d7607010b39858b004dd84270bf06b260759403b0e82204a0ea3b088c7d0268acf523459a3b4b50d97efb00f1d3eca4b585e5feef700321434b53a0881e8454ec222ca1403c81e33c1d8301b0500ec2c07a9329b2928e14b4718594d51d1bf0a8fb4d472c4a3fc8d106568cb214149207913c0642168107b480ad3c04ad26d1c2d68b07b48f229cb41683da4a46d29238cd92f67497e5a4759525b9191afe6512d3040d30ad44e9c147b20e459ba1b01d0cd9305034e164d1051ec86934c1c8b21168810b42f229cb41683da524719b25ece92fcb48eb2a4b7232358306bc965102b687807e89b3e08ba02788f72cce2152700a8b7c231ad0ee5a0f62c07ae74afe42531532accc95ee44ae71e571972bcca95dd34aa646533512abcd95f52caa25a53d2b29da7955634adca41e50a0d992d2f066c9a535a71368011c3fcb39f045cf72cce2152700a8b7c231ad0ee520f22d4ce1626672e43d4d207c690cd3c823224375320ac790d4a47e6a2413231f6cd91052c81b3243f9d221ca90ec96c9e43395559b68259fe740ecf74a0767ba303b3d 0x111c10170e560c950ad408aa087407af076707350670058102d90057003a001d0000 (i%16)
private def hints₂p48 (i:ℕ) : ℕ := packedAt 0x9c2e84d3a8571d02b2ef0c773861a18495042448504a0e06f86c0bcbd6b50f862085a00569e20f69012b491c806da9afc1ace8220500ec3b0889283a8981d74768890a11df5b8a46899496a2bdb70d0d9463a7bd1f400a2b365e5b829822b6a6bf06b3a0881403b0ec2224a0ea26075d1da22428477d6e291a26525a8af6dc3436518e9ef47d0028acd9796e0a65ac52ed6c9e03252b4a3c81e042d002b4f012b4983da44e174269d42b8e815977863b9c30d0c24a821224282507037c3605e5eb5a3f08d20046cfb6b2dc150710a937c230b41eda16ccd2b67434b7266b59ab6d0acb61665b269ed7b536bf98ac3e5db22a2d7d556c097ab1ebdb4aaed83a36cd96a976a5b3f3ad950f862085a00569e20f69012b49295a50e4037210c2468412241861bc0585cc2b2f50a67484d29417cc01f85c0fb837ca0a7e68545b617ae19673f5a941b50519a735e50970c6aa4c8d1171ea954952d9607b16c231bd6ae7c116a7da793c0642168107b480ad3c04ad24a56956a47f967a8a275551424533c51b563a0881283a9c42a4e0151a3b4a5159e23a7d54365dcec1c66e0de4286594b4e6e0a8666d2f2f69953b4d3e08b53ed3c9e03210b4083da40569e0256936a8d5083a4daa9f045a9f69f53b4db523fcb3d45a92aad4dac981d6beb538fa025e5d16fae8f549673f5a9546d45a735e76111bdda81f045a9f69f53b4d859c42c0e6162c01376109c4710217d46c6b8f63dc7e38810be3fcb3d55d1aa2e31607010b39858b004dd84270bf06b260759283a8ec2227411028076485092f6dfd436528fa00c74f7ef2dfb496a3a3b44c8d1368acdb7d6ff 0x12bc114f0fc90d9b09e209080893071104b9044403f902cc026f0251021e01c10000 (i%16)
private def hints₂p49 (i:ℕ) : ℕ := packedAt 0x77670a09383b4a128acd0b63a08794c22cee06adc15006066b7c2fc1e06e7a1173c08b15ad8e4b2899725c808c6d1c9069a4899925dc392a53c915fe2d1492429091a6249569648610b3f828f586adb4b41ee59b6c9591ccb48ea0c1af09b4609db5c21c0df8691743c8bc2167f051eb8306bc26d1ada1012fae0154710aab94260b81f25b0210e06f86c07d3a0b656b63a9923e4c96b2a4b70d22ecf930534913324bb55248a7922cb48ea5e4779d25fc892cc3c8be964879b25e0859fc147ae0c1af09b4609db5dfa0046cf422e7d0390759f04410cfd6d4de1526e5b338c25cb01f0270022edb287037c081b4060db0406e06c09cb56d39d25f9591ccbc8ee9e48b9925da69224046361a45d9525ba89234248b3264b553247cb92e41ad9c6a0130f8600ad3c15ad8ef9002387a1193e08d5f1e8464f82347fb68404beb88555c02a8e50986e5b327416cb81f2580f72b5b1e5c972a648f9325aa892365496f3e4c14d244cc92ed549229e48b2d23a9791dcac8e73a4bf91259a5921e6c97a514a210a5308a6c0a4b6853dae174df0bf3d08b9e0458fb2ce56b639452884294c229b0292da14f6bc48b7c2fcf422e7d9673f08ea004810711cdcb66710aab9855dc02a8e50984e82d9703e4b01ee5bb64aa93d644a065a4e397284cc942cbc9cb425134f277cf9445349db265052b270a993ce54a0f3650d9d287a893c42035cad6c6350090ad3c4a2944214a6114d814c6d0a7264168ad6c7507037c2b4f10f8608877484da7c170b212ee215572c44208475002385e0fb3f8219740a8381be1b0272b5b1c3e1806a01210b40a893c674a1e624e75327986934e7ca225e4e55527a8406b8569e37c3a0867e1190d8138d4024f72cc5a0f60c06c37e249ad0f12d271cb942664a16964eb4f277a693b42c9a21a4d35327994937e54a0ea24f108b440bdb143e1882168015a78095a4c1ed22d4cec222741103c81e2fc1aca41da180d8250751303aca12df254648594e51d34a3a7ab454d1bda73d2d352869a1794e6a4a69c8d10efa9d11f3fa90a0b4a2d849e03210b400ad3c04ad260f691be1d0290d8131683d8b01eb0d28f9694f4aca76141b019b6087c31042d002b4f107b48095a4eb5f5a99d0440a01d84c0eb3b0889283aaf6a2945504a3a82c8d112f2a271f3fbbea8ad0d40e92a0d214178e9eb4a83d69732059b5f3c81e13c0642168107b480ad3c04ad24a5695828212040daf388549be1187c1173f08c1683db42d99a56ce8696e4cd6b356da1596c2ccb64d3daf6a6d7f31587a8b5f535af2aad812f563d7b6955db0746d9b2d52ed4b67e75b2a956ba7bb5c1980413c064a56947903c085a00569e02569307b48 0x1e831b731ada1843153214eb128211a40e3b0db10d6c0b3e08ea067d054f03110000 (i%16)
private def hints₂p50 (i:ℕ) : ℕ := packedAt 0x4a39f045e51cf822e7bb7c6c0a6378541b429d7e8011b3e85ee8240324d9783edd02b05d0994f82e16425dc42aae61572b5b1d95974265d02b0e615772dbc1bc2b1716ee7010b39858b084e5820d8509ae295ba3385019616ad39af3a0881283a49c1d6790372680b03adc0ed6ea1ab6d4f82e1683dcb36ccd69ad6eda91e8460f82347fb7319803042cfe8a4814b243c692be24957424c37124dbd9284848d3164ad4123ec892ccac8e65e47749242d19314b48ea9e48b7d251aa92446c8c63e46785253a692251c906de499051ebcf93065496e8647f3123ca89235cc93b264b553247c792c4648c23a4659725c8306bc26d18ad6c613b6bb761c08f8d0475071f836b2a4008e7311c18c920ceb41325b099a3c15290b8424582103010af04e0ec680a29442092e0b052b74690a3338505aa172cdb6f3c08895ad8f1e4b123235c392a52490b164ad21234c492ae3495e96487dc9c1da509452b5b1c96512db9002367db713d5b906adb4b41ee59b6ca9923d3c9165a4752b2398306bc26d18276d76e00f0373b0899e04569a48949242a59218cc0182167f051eb8306bc26d1ad4e822079037075b81dadbd98282ca1406783b9383b4a128a5308b6e0a736c2f4ad6c725944cb92e65496e8e48385253c392a4848d3124ab4b2430859fc147ac356da5a0f72cdb64ac8e65a475060d784da304edaf506066c04635fe2d010b3f828f5c1835e1368d6c781113a087d1c906924854b243 0x10bb109a10250ff30fd70f2708f4087f080e07c8061d05c204a503b2010a00710000 (i%16)
private def hints₂p51 (i:ℕ) : ℕ := packedAt 0xb4783da45a9afc1ace822076111260759283a8a12df474d2bda73d2d352869a1794e691a21df53a24282d280f393dc61e40f09e03210b40a4d1d4768e63f47107b48a2d1b94a8f8ae04855b8ab535f8359d0440a13a876111260759283aaf2967434a0a3a5148d10a969497d4b5bda5a485054ab715e7291f9938fc156e2a40900e060360216810b1ed838f5c12e242b51216b832b5b1f02167e130240c5c415ad8c2b51216b83bf3ecb39fae1d013c4e21556e0a7380551ca130db08a4e82d9703e4b01ee5b0290e06fb7a5983607c7a961680a235851da6104520ed284bc0cc0209e032120d3085a0674aff3e5812129886947d4cab20e45b992bdc895cd24a9e4a535972bca6954c8ca66a25570f290c595b4bca7f3657d4b2a89694f4aca769e5558d2b7aa956c2ae1b2b29815a892b5b185ae0ef8f8235e0859f84ee14341bb0d22e8306c15ad8c2b51216b838fc4008e1fe1fdd42b4e615974d9597619dea1948812742092a084910e09659026ab924d4c91f4a4c751246ad925d6492aaa4914f245d59336bc99c381bce4b7a2d4bb4b48e8ad6c79f260ce92fcbc8ef424c3a32621d807068374bc1fa639c68691743c8be624793523d8306c056a242d707b10b2688391659f844074274f01a0dd0a06c42c9a21a4d30722c845c1416e0433701be1d0200d80e842cfc274f0140d786947c1c8b61e5210a0d92b5b1c16e0433701b3091ec858f6dfa0046cfb6fe7ab7e6c0a5b78549b6114e30972c045b72df4fd654e4b7a690a2350515a20f097058290771383b0a202e5a9460759f62c8632e43d4d207c690cd3c8229240b311fd968fdd4c82b1e4350f1ef808c667c88aa2413231f6a590366487f3a4432f1fcc990e68488f2a43b25b2790ce55566db4736704b3f1b805846c9a1b51a14b7909db5a64168ad6c735e790b9 0x14e814c71284113d10f610330fb00b3a0b1d0a7006dd06ab05cd04c9049700210000 (i%16)
private def hints₂p52 (i:ℕ) : ℕ := packedAt 0x18a8412141090204300f912353279ab93dd549ea51cfc2327c1173ddce360526a24f193282a693b53c9de964eb912818d1f66b4ff6f951278a493a63ca02a64f38d27fa793bd2c9d5b429595283c8940c5b060d78506cc26e102f73573215a89bd3d08a9f0458f20700eb3e08dcc1fa3f1012fae4157710ab39c250bb0cef50ca6d0a5a2049d0824a821246c84321c12cbc1fa590261d8071426f0a41e21c0de31ce3068374b52ec56b489291b6bc99e4e46f4b24385916e849861e45f9d25fd59334b48ea9e48b55248ac9255349120231b9f2608691765496e624795b24ba892348c8d7264b5572499a91ec1ae5c2572819b922adc54fd8f72ccb0745f8359303ac941d47b03e2780c8cc020257291d232a191fd1c9069a489852538f919df494692485812529091a5ec942f249f4b243a29200683761a45c19b92859169426f0b52ec15a899691d15ad20a41e3272379291b48c8d60d72e55b8a8d1fedf0fb35ada14a6f0a935c211c61205c0f92c07b96ee543607c7ab966309fb2c1d17e0d6560f3280761303ac941d4520edbe959674afe425312929ca9956604acf3257b792b0c895cd24a9e3e52f852b4c795c494a6b2a5774d2a99194cd44aae8a54b432a49794fd2caa25a53d7b2b19594ec9ca6e8e54d4f2aac695bc74a589e0330a0d8085a0066e486601012b940ad44956e2acce421a75b533b0899e045690e06fc3e1882168012b9486947c283603372415a89f6c28362081a707b930cdc9056a265fca41e25a9769291b49c8de5a47415a892b5c7156e2a5fca41e25a9769291b49c8de5a47506b912b5c704ee34ab71582821203e08da04104352f4e297c3007e1683e8b81f65fb903f5c79483c6aa4174f208988fecb47eea64159f222cd9104347ba663fd9d221978fe49c7e24a3ef040d3085a043e16cad71c13b8d0ad44956e2abeef0a12e07c9603dde32e85b97987c2d95ae3821681a1223d4913cbc7f21a3dd2b1faab906694896a2413ab228cf91169c89aa64155920d968fde8c892aa416520f1938fc4947de081a613b8d0ad44956e2b7c3a08e1b0414108fa004707201b0f85b085a04347baa24135320aaa905c1034c2771a15a89 0x18dd18421764165f160115e0112b0e04094e08f2084407d2071e065503c2012e0000 (i%16)
private def hints₂p53 (i:ℕ) : ℕ := packedAt 0x26b4f53bcd7084284f3644ae69254f8f2b89194cd2caa31a56f0da8d2adc56cc2ca6e1312d260f32bdd64a69742f73455b8ac4420913a231aaf755a5ba9d1dd4160246ab75655b8acfdd1ecc249ea1655a17b9a9ad3d4ef35c210a13cd8f2b8c695bc28366468a30927ba4b53e45d7a96d830da8d0a5cd956e282f73535a7a9de6b84214279b225738f2b89194ce34ade141b30928ba4b5ad2db3a1b51a14b9b2adc505ee6a6b4f53bcd7084284f3644ae71e5718d2b78506cc8d17692d694b6cd84945436a342973655b8a0bdcd7a094004b203e060d60206a8083502167f272379591cc147ae0c1ae1ab6d84da304ee882b74c17b9a2adc55e1e0454ff6fc7b9ad6c0a4b68529af360e5ba52707614405c1d67ce88c62907895ae2e9a40f8d219a7904524817224372d1fba990563c86a0231951209d2912c8c7daae4199b220a590364c8724e3f19521d92d93c8672a5736f559b6d1cd9c12cfc6e01611b2609d3c156e2b3f74617b9ac4420911faca9070d167e11b2609d3c060364281af0b2bf8392fc148861250e17b9ab3f08d9304e9e0301b2140d785960424a220a445072600bdcd62a10485042407e11c40dd0ba8571de142e6156700a9b90554bc1f4e30902c07b96c09c356ca350090c5cdd5c926a648fa5263a89234c48f21a45d9f260d4932d549225a4752b239ce92fe84987364bc56b4829078c9c8de0d741259442adc505ee6a3a838683f860551c211a9d05b2c04a39855dcb1108211d4008e1783ecfe0865db650e06f86c09cb573e560f329078d549ea5e4e5a1289cf9444349a6a64f32926f98939e6ca1a4e4dd51278085a042035e4b2890f8601a804862e6cab71417b9a8ea0e3f1002387fb9e6b5ceba8571de142e01536f0a9390554bc1f4e30902e07c9603dea24f19d287cd9434c49cea64f32b270cf9446a4a369e4ef2f272cc942cb49c6aa4f5a528b2b079c9c9ba524de55b8a 0x15da14e7144c1387134011f910b20f6b0e130a840a3d097408ab059a056702940000 (i%16)
private def hints₂p54 (i:ℕ) : ℕ := packedAt 0x59f846c98274f112b51209418615566da0967e7fbbb85dd7046c9a1b51a13a780a5de3ac27cb0122e7bb80bdcd156e2ad1a1177413ba2c743092a14319d82b6ee15cac906e9c89b4a44b5720cd4913c12cfd0577211b2609d3c59f84407e0a3d61ab6d8306b84ee882f7358884122740acd5c83342447559b6d1cd9c12cfc2364c13a78bb672dd81583cca41e327bb792d2f4a69743374e17b9a2adc56cc249ba1653617b9ade0e82343c9a90575e1a0dd8406cc2eed4b37687fbb386d46842cfc274f014b9b82dc085ee6a060d60206a808350481e9092689594ec9ca6e0b70213a780a5cd85ee68ab715762e108d2adc57a0940065653b2729b0306b010354041a90a0d984dd927c170b3762830c370860416e04274f014b9baadd5956e282f7358884122740ac55c9ef465159fba3a1a101b39a15485dd727416c2973617b9acfdd1dd7160244ac1e72729b855d79feeb5070d129a5d0a5cd866e9cab71417b9a9e2a112b080d986d46852e6eab75617b9a 0xb970b610a1a09e408cb0841077c06b3066c053e0441040b02890218017b00880000 (i%16)
private def hints₂p55 (i:ℕ) : ℕ := packedAt 0x2b8ef0a1758629603dd042405e0fa3f08e210486564732d23aaa9246a49966247951246d2931d4c91eae493060d784da304ee882b78a5bbcc295e695aefd0379417b9ad78391bc26d1a4c1e213ba292ca2056f042f73455b8a97d710aac1835dca12309b462cdde04ee882b79681bca2b5dfe76e933f74617b9a2adc5609f8471c52f882120a990554482736441559b6825df046c98274f081bca2b5dfe76e933f74655b8a868720aab9855b42513080d9415e438c2421775c58bc92b0799483c64f76e14b9b92d2f4a69743378e5bbc42adc505ee6b3f7479dba4f796938cac9c2101b30bbb50bdcd54dc21819b2863f5d7c20365c61210bbae2dde2052e6ca41e325a5e2b079c9eede534ba19bc7cedd205ee68ab715e253bc69391bc1835e1368c13ba292ca2056f14b778855b8a0bdcd460f735a7f0c06b84238054dc612056bbfc792c54491a9a48949242c892ce3495e964879b25e2c07bcac8e65a474330060859f9403c04a002020d40206a81835a0a3d7232359391bc1835e1368c13ba20ade296ef10ab7159dba40bdcd4a34c47f65a3f70f1ef978fe412efa1b51a17b9ad985ddac24a24b3769a015772de19583cca41e327bb792d2f4a697433784e7bb82adc567ee8c2f73575e7fbad4182307037a1e4d41a0dd8406cc2eeb8b01230da8d29078c96978ac1e727bb794d2e842cfc274f014b9b82dc0866f082f73455b8a88284a2966ef02b78253bbd720abb8855b4378056bbf73ddc156e282f7359fba3cedd278c9c7e24b64f04bbe08d9304e9e0ab715ae15bbe83930c24a260a44617b9ad309dd1056efa0b71707b48 0x128a10740fc40ea70d640bb40b4309d508fb061305740431026c015300cd005c0000 (i%16)
private def hints₂p56 (i:ℕ) : ℕ := packedAt 0x84c1f0040da0306d820370bb6ca1b027095eb0903d0b211b0d22e828f5cbc8ee56473272372b5a4380545be17e8011ba99239e845e9a4887e11aa7922d4491b364bd9925d8306bc26f602b7a452bda0bdcd156e28fb7bb5d76850284178b0128e6159788643a43110c246841223f5d7a004810608c5a0f92f07d87037872019a728c96938cbc9cb42513ab28eab93dd649f2a64f30f26a98939e8ca282167e1a0dd8406c9583cca41e30da8d09d3c42ef3e4f76f55bab0a5cdc16e064b4bd29a5d0cdee176f40ab71417b9af92ddedcbc8ee5a475060d784dec056f48a57b45dbd00bdcd5013ac315cc2ac7e11c41090210485c72fa81bd9d0de055c926a648fa5263a8923554920ad6905e0fb9791dcc48f20c1af09bd80ade914af68bb7a055b8acedd205ee6a378306bc983c6137b1259440ade0956e282f73569057bd78306bc26f602b7a417b9aba0095a341c8b20206d01836c101b81b027095eb0903d04c1f059bd59391bcac8e65e477051eb8691741835cbb7a015bd20bdcd156e2a060d60206a8083502f7351d418611fc10c217a81c0df0d8138d4024257a6e415470846a7416c2b7a551246869174046360a3d75524887917e6c9782f7359fba32adc559f03c0e42f735f0d5b6842cfc2f735667610f3c0881d42b97826cbb069258331203958c27c2105064839932f4564260b61315a855918390d820a72108380838883bc9c1d8450113781994405c5a0080cb410759f15ae2f0242b191f18f8fa5dc8529240b472047f8b3c747ce023196f210b6907dd484e824031b1f2918fb60c85a864054b2069f90051480e2e3e171211938fc5cc84a4339504bbe08d9304e9e0ab71417b9a992e6ded1e0a84a0e98c821200e06f54c9e61e4d41a0dd8406cc2ef3c2167f0da8d09d3c556eac2973705b810cde7206f282f73576a59bae0a5cd9483c64b4bc560f393ddbca6974ab71417b9a 0x15ac12f50f500e8b0c720bd50b600b2a09ae095907970761071d0268022000c90000 (i%16)
private def hints₂p57 (i:ℕ) : ℕ := packedAt 0x5e4866f80b77db285e8cb2ec63398564b211ae90c4700a8a10489be17e830463f08d20046cf422e1c0ded2945cb49c73250b2f272d0944d3c9deae4f74d276a993cc3c9aa624e79b286a893c68ca28341bb080d985df615afa8ab71452be9cfdd1d56f94fb7ba14be4085f5866f802f73413be786df4545be17ee108d3f08d20046cf422e58bb5a9956664af69a553512abcd95f53caa8fb7ba56bea2adc514afa4337c167f05be309df3f9956e2a537c327be6f12adc5496f8a4f7cd51a14be4a780a5f25db866f82eac337c173619be0b810bdcd066f829782f73419be0a5d0bdcd066f82f7ca57b526e580f72e07c96ef79c42a4da14a6f85fb5c2e8fc2348011b3d08b9e0458ad6914b243c892ccac8e65e4772d23aa7922e649769a4899525ba892354c91e0c1af09bd80ade905ee68fb7bb9dba4 0x9b70981060704990463041c03d503b4039303720351033002fa02c4028e026d0000 (i%16)
private def hints₂p58 (i:ℕ) : ℕ := packedAt 0x54b3b74999bf671dfeb7eff240ab71458bee295f495afa8b77da5cbfbbf3f5fd1eafe0fb7ba80bf9f92ddf6cbefd65b7ef1a3edeed46fc69f7e91ba9df91f6f769f7e9173edeed36fce9f7e938c22fc285845f84e508bf09de117e13b422fc279845f84f108bf0d90cdf005ee6a177df527184837c2fcb81f27e11a4008d9e845ea6559992bda6954d44aae5e53f2d29ea7955676e90b77da56bea295f4962fb8ab7147dbdd 0x52b04ce044803ec03a5035d031502cd02ae028f027002510232021301f401ad0000 (i%16)
def hints₂ (i:ℕ) : ℕ := if i<464 then (if i<224 then (if i<112 then (if i<48 then (if i<16 then (hints₂p0 i) else (if i<32 then (hints₂p1 i) else (hints₂p2 i))) else (if i<80 then (if i<64 then (hints₂p3 i) else (hints₂p4 i)) else (if i<96 then (hints₂p5 i) else (hints₂p6 i)))) else (if i<160 then (if i<128 then (hints₂p7 i) else (if i<144 then (hints₂p8 i) else (hints₂p9 i))) else (if i<192 then (if i<176 then (hints₂p10 i) else (hints₂p11 i)) else (if i<208 then (hints₂p12 i) else (hints₂p13 i))))) else (if i<336 then (if i<272 then (if i<240 then (hints₂p14 i) else (if i<256 then (hints₂p15 i) else (hints₂p16 i))) else (if i<304 then (if i<288 then (hints₂p17 i) else (hints₂p18 i)) else (if i<320 then (hints₂p19 i) else (hints₂p20 i)))) else (if i<400 then (if i<368 then (if i<352 then (hints₂p21 i) else (hints₂p22 i)) else (if i<384 then (hints₂p23 i) else (hints₂p24 i))) else (if i<432 then (if i<416 then (hints₂p25 i) else (hints₂p26 i)) else (if i<448 then (hints₂p27 i) else (hints₂p28 i)))))) else (if i<704 then (if i<576 then (if i<512 then (if i<480 then (hints₂p29 i) else (if i<496 then (hints₂p30 i) else (hints₂p31 i))) else (if i<544 then (if i<528 then (hints₂p32 i) else (hints₂p33 i)) else (if i<560 then (hints₂p34 i) else (hints₂p35 i)))) else (if i<640 then (if i<608 then (if i<592 then (hints₂p36 i) else (hints₂p37 i)) else (if i<624 then (hints₂p38 i) else (hints₂p39 i))) else (if i<672 then (if i<656 then (hints₂p40 i) else (hints₂p41 i)) else (if i<688 then (hints₂p42 i) else (hints₂p43 i))))) else (if i<816 then (if i<752 then (if i<720 then (hints₂p44 i) else (if i<736 then (hints₂p45 i) else (hints₂p46 i))) else (if i<784 then (if i<768 then (hints₂p47 i) else (hints₂p48 i)) else (if i<800 then (hints₂p49 i) else (hints₂p50 i)))) else (if i<880 then (if i<848 then (if i<832 then (hints₂p51 i) else (hints₂p52 i)) else (if i<864 then (hints₂p53 i) else (hints₂p54 i))) else (if i<912 then (if i<896 then (hints₂p55 i) else (hints₂p56 i)) else (if i<928 then (hints₂p57 i) else (hints₂p58 i))))))
private def rows₂ (i:ℕ) : ℕ×ℕ := (learn₂ i,hints₂ i)
private def good₂ := okFast maskTable₂ 2126 rows₂

private theorem step2_0 : block good₂ 0 8 := by decide +kernel
private theorem step2_1 : block good₂ 8 8 := by decide +kernel
private theorem step2_2 : block good₂ 16 8 := by decide +kernel
private theorem step2_3 : block good₂ 24 8 := by decide +kernel
private theorem step2_4 : block good₂ 32 8 := by decide +kernel
private theorem step2_5 : block good₂ 40 8 := by decide +kernel
private theorem step2_6 : block good₂ 48 8 := by decide +kernel
private theorem step2_7 : block good₂ 56 8 := by decide +kernel
private theorem step2_8 : block good₂ 64 8 := by decide +kernel
private theorem step2_9 : block good₂ 72 8 := by decide +kernel
private theorem step2_10 : block good₂ 80 8 := by decide +kernel
private theorem step2_11 : block good₂ 88 8 := by decide +kernel
private theorem step2_12 : block good₂ 96 8 := by decide +kernel
private theorem step2_13 : block good₂ 104 8 := by decide +kernel
private theorem step2_14 : block good₂ 112 8 := by decide +kernel
private theorem step2_15 : block good₂ 120 8 := by decide +kernel
private theorem step2_16 : block good₂ 128 8 := by decide +kernel
private theorem step2_17 : block good₂ 136 8 := by decide +kernel
private theorem step2_18 : block good₂ 144 8 := by decide +kernel
private theorem step2_19 : block good₂ 152 8 := by decide +kernel
private theorem step2_20 : block good₂ 160 8 := by decide +kernel
private theorem step2_21 : block good₂ 168 8 := by decide +kernel
private theorem step2_22 : block good₂ 176 8 := by decide +kernel
private theorem step2_23 : block good₂ 184 8 := by decide +kernel
private theorem step2_24 : block good₂ 192 8 := by decide +kernel
private theorem step2_25 : block good₂ 200 8 := by decide +kernel
private theorem step2_26 : block good₂ 208 8 := by decide +kernel
private theorem step2_27 : block good₂ 216 8 := by decide +kernel
private theorem step2_28 : block good₂ 224 8 := by decide +kernel
private theorem step2_29 : block good₂ 232 8 := by decide +kernel
private theorem step2_30 : block good₂ 240 8 := by decide +kernel
private theorem step2_31 : block good₂ 248 8 := by decide +kernel
private theorem step2_32 : block good₂ 256 8 := by decide +kernel
private theorem step2_33 : block good₂ 264 8 := by decide +kernel
private theorem step2_34 : block good₂ 272 8 := by decide +kernel
private theorem step2_35 : block good₂ 280 8 := by decide +kernel
private theorem step2_36 : block good₂ 288 8 := by decide +kernel
private theorem step2_37 : block good₂ 296 8 := by decide +kernel
private theorem step2_38 : block good₂ 304 8 := by decide +kernel
private theorem step2_39 : block good₂ 312 8 := by decide +kernel
private theorem step2_40 : block good₂ 320 8 := by decide +kernel
private theorem step2_41 : block good₂ 328 8 := by decide +kernel
private theorem step2_42 : block good₂ 336 8 := by decide +kernel
private theorem step2_43 : block good₂ 344 8 := by decide +kernel
private theorem step2_44 : block good₂ 352 8 := by decide +kernel
private theorem step2_45 : block good₂ 360 8 := by decide +kernel
private theorem step2_46 : block good₂ 368 8 := by decide +kernel
private theorem step2_47 : block good₂ 376 8 := by decide +kernel
private theorem step2_48 : block good₂ 384 8 := by decide +kernel
private theorem step2_49 : block good₂ 392 8 := by decide +kernel
private theorem step2_50 : block good₂ 400 8 := by decide +kernel
private theorem step2_51 : block good₂ 408 8 := by decide +kernel
private theorem step2_52 : block good₂ 416 8 := by decide +kernel
private theorem step2_53 : block good₂ 424 8 := by decide +kernel
private theorem step2_54 : block good₂ 432 8 := by decide +kernel
private theorem step2_55 : block good₂ 440 8 := by decide +kernel
private theorem step2_56 : block good₂ 448 8 := by decide +kernel
private theorem step2_57 : block good₂ 456 8 := by decide +kernel
private theorem step2_58 : block good₂ 464 8 := by decide +kernel
private theorem step2_59 : block good₂ 472 8 := by decide +kernel
private theorem step2_60 : block good₂ 480 8 := by decide +kernel
private theorem step2_61 : block good₂ 488 8 := by decide +kernel
private theorem step2_62 : block good₂ 496 8 := by decide +kernel
private theorem step2_63 : block good₂ 504 8 := by decide +kernel
private theorem step2_64 : block good₂ 512 8 := by decide +kernel
private theorem step2_65 : block good₂ 520 8 := by decide +kernel
private theorem step2_66 : block good₂ 528 8 := by decide +kernel
private theorem step2_67 : block good₂ 536 8 := by decide +kernel
private theorem step2_68 : block good₂ 544 8 := by decide +kernel
private theorem step2_69 : block good₂ 552 8 := by decide +kernel
private theorem step2_70 : block good₂ 560 8 := by decide +kernel
private theorem step2_71 : block good₂ 568 8 := by decide +kernel
private theorem step2_72 : block good₂ 576 8 := by decide +kernel
private theorem step2_73 : block good₂ 584 8 := by decide +kernel
private theorem step2_74 : block good₂ 592 8 := by decide +kernel
private theorem step2_75 : block good₂ 600 8 := by decide +kernel
private theorem step2_76 : block good₂ 608 8 := by decide +kernel
private theorem step2_77 : block good₂ 616 8 := by decide +kernel
private theorem step2_78 : block good₂ 624 8 := by decide +kernel
private theorem step2_79 : block good₂ 632 8 := by decide +kernel
private theorem step2_80 : block good₂ 640 8 := by decide +kernel
private theorem step2_81 : block good₂ 648 8 := by decide +kernel
private theorem step2_82 : block good₂ 656 8 := by decide +kernel
private theorem step2_83 : block good₂ 664 8 := by decide +kernel
private theorem step2_84 : block good₂ 672 8 := by decide +kernel
private theorem step2_85 : block good₂ 680 8 := by decide +kernel
private theorem step2_86 : block good₂ 688 8 := by decide +kernel
private theorem step2_87 : block good₂ 696 8 := by decide +kernel
private theorem step2_88 : block good₂ 704 8 := by decide +kernel
private theorem step2_89 : block good₂ 712 8 := by decide +kernel
private theorem step2_90 : block good₂ 720 8 := by decide +kernel
private theorem step2_91 : block good₂ 728 8 := by decide +kernel
private theorem step2_92 : block good₂ 736 8 := by decide +kernel
private theorem step2_93 : block good₂ 744 8 := by decide +kernel
private theorem step2_94 : block good₂ 752 8 := by decide +kernel
private theorem step2_95 : block good₂ 760 8 := by decide +kernel
private theorem step2_96 : block good₂ 768 8 := by decide +kernel
private theorem step2_97 : block good₂ 776 8 := by decide +kernel
private theorem step2_98 : block good₂ 784 8 := by decide +kernel
private theorem step2_99 : block good₂ 792 8 := by decide +kernel
private theorem step2_100 : block good₂ 800 8 := by decide +kernel
private theorem step2_101 : block good₂ 808 8 := by decide +kernel
private theorem step2_102 : block good₂ 816 8 := by decide +kernel
private theorem step2_103 : block good₂ 824 8 := by decide +kernel
private theorem step2_104 : block good₂ 832 8 := by decide +kernel
private theorem step2_105 : block good₂ 840 8 := by decide +kernel
private theorem step2_106 : block good₂ 848 8 := by decide +kernel
private theorem step2_107 : block good₂ 856 8 := by decide +kernel
private theorem step2_108 : block good₂ 864 8 := by decide +kernel
private theorem step2_109 : block good₂ 872 8 := by decide +kernel
private theorem step2_110 : block good₂ 880 8 := by decide +kernel
private theorem step2_111 : block good₂ 888 8 := by decide +kernel
private theorem step2_112 : block good₂ 896 8 := by decide +kernel
private theorem step2_113 : block good₂ 904 8 := by decide +kernel
private theorem step2_114 : block good₂ 912 8 := by decide +kernel
private theorem step2_115 : block good₂ 920 8 := by decide +kernel
private theorem step2_116 : block good₂ 928 8 := by decide +kernel
private theorem step2_117 : block good₂ 936 8 := by decide +kernel
set_option maxRecDepth 20000 in
theorem refute₂ (v:ℕ→Bool) (h:∀c∈base₂,clauseSat v c=true) : False := by
  apply finalFast guess back baseTable₂ maskTable₂ 2126 rows₂ 943 base_valid _ (by decide) v h
  exact (@block_union good₂ 0 472 472 (@block_union good₂ 0 232 240 (@block_union good₂ 0 112 120 (@block_union good₂ 0 56 56 (@block_union good₂ 0 24 32 (@block_union good₂ 0 8 16 step2_0 (@block_union good₂ 8 8 8 step2_1 step2_2)) (@block_union good₂ 24 16 16 (@block_union good₂ 24 8 8 step2_3 step2_4) (@block_union good₂ 40 8 8 step2_5 step2_6))) (@block_union good₂ 56 24 32 (@block_union good₂ 56 8 16 step2_7 (@block_union good₂ 64 8 8 step2_8 step2_9)) (@block_union good₂ 80 16 16 (@block_union good₂ 80 8 8 step2_10 step2_11) (@block_union good₂ 96 8 8 step2_12 step2_13)))) (@block_union good₂ 112 56 64 (@block_union good₂ 112 24 32 (@block_union good₂ 112 8 16 step2_14 (@block_union good₂ 120 8 8 step2_15 step2_16)) (@block_union good₂ 136 16 16 (@block_union good₂ 136 8 8 step2_17 step2_18) (@block_union good₂ 152 8 8 step2_19 step2_20))) (@block_union good₂ 168 32 32 (@block_union good₂ 168 16 16 (@block_union good₂ 168 8 8 step2_21 step2_22) (@block_union good₂ 184 8 8 step2_23 step2_24)) (@block_union good₂ 200 16 16 (@block_union good₂ 200 8 8 step2_25 step2_26) (@block_union good₂ 216 8 8 step2_27 step2_28))))) (@block_union good₂ 232 120 120 (@block_union good₂ 232 56 64 (@block_union good₂ 232 24 32 (@block_union good₂ 232 8 16 step2_29 (@block_union good₂ 240 8 8 step2_30 step2_31)) (@block_union good₂ 256 16 16 (@block_union good₂ 256 8 8 step2_32 step2_33) (@block_union good₂ 272 8 8 step2_34 step2_35))) (@block_union good₂ 288 32 32 (@block_union good₂ 288 16 16 (@block_union good₂ 288 8 8 step2_36 step2_37) (@block_union good₂ 304 8 8 step2_38 step2_39)) (@block_union good₂ 320 16 16 (@block_union good₂ 320 8 8 step2_40 step2_41) (@block_union good₂ 336 8 8 step2_42 step2_43)))) (@block_union good₂ 352 56 64 (@block_union good₂ 352 24 32 (@block_union good₂ 352 8 16 step2_44 (@block_union good₂ 360 8 8 step2_45 step2_46)) (@block_union good₂ 376 16 16 (@block_union good₂ 376 8 8 step2_47 step2_48) (@block_union good₂ 392 8 8 step2_49 step2_50))) (@block_union good₂ 408 32 32 (@block_union good₂ 408 16 16 (@block_union good₂ 408 8 8 step2_51 step2_52) (@block_union good₂ 424 8 8 step2_53 step2_54)) (@block_union good₂ 440 16 16 (@block_union good₂ 440 8 8 step2_55 step2_56) (@block_union good₂ 456 8 8 step2_57 step2_58)))))) (@block_union good₂ 472 232 240 (@block_union good₂ 472 112 120 (@block_union good₂ 472 56 56 (@block_union good₂ 472 24 32 (@block_union good₂ 472 8 16 step2_59 (@block_union good₂ 480 8 8 step2_60 step2_61)) (@block_union good₂ 496 16 16 (@block_union good₂ 496 8 8 step2_62 step2_63) (@block_union good₂ 512 8 8 step2_64 step2_65))) (@block_union good₂ 528 24 32 (@block_union good₂ 528 8 16 step2_66 (@block_union good₂ 536 8 8 step2_67 step2_68)) (@block_union good₂ 552 16 16 (@block_union good₂ 552 8 8 step2_69 step2_70) (@block_union good₂ 568 8 8 step2_71 step2_72)))) (@block_union good₂ 584 56 64 (@block_union good₂ 584 24 32 (@block_union good₂ 584 8 16 step2_73 (@block_union good₂ 592 8 8 step2_74 step2_75)) (@block_union good₂ 608 16 16 (@block_union good₂ 608 8 8 step2_76 step2_77) (@block_union good₂ 624 8 8 step2_78 step2_79))) (@block_union good₂ 640 32 32 (@block_union good₂ 640 16 16 (@block_union good₂ 640 8 8 step2_80 step2_81) (@block_union good₂ 656 8 8 step2_82 step2_83)) (@block_union good₂ 672 16 16 (@block_union good₂ 672 8 8 step2_84 step2_85) (@block_union good₂ 688 8 8 step2_86 step2_87))))) (@block_union good₂ 704 120 120 (@block_union good₂ 704 56 64 (@block_union good₂ 704 24 32 (@block_union good₂ 704 8 16 step2_88 (@block_union good₂ 712 8 8 step2_89 step2_90)) (@block_union good₂ 728 16 16 (@block_union good₂ 728 8 8 step2_91 step2_92) (@block_union good₂ 744 8 8 step2_93 step2_94))) (@block_union good₂ 760 32 32 (@block_union good₂ 760 16 16 (@block_union good₂ 760 8 8 step2_95 step2_96) (@block_union good₂ 776 8 8 step2_97 step2_98)) (@block_union good₂ 792 16 16 (@block_union good₂ 792 8 8 step2_99 step2_100) (@block_union good₂ 808 8 8 step2_101 step2_102)))) (@block_union good₂ 824 56 64 (@block_union good₂ 824 24 32 (@block_union good₂ 824 8 16 step2_103 (@block_union good₂ 832 8 8 step2_104 step2_105)) (@block_union good₂ 848 16 16 (@block_union good₂ 848 8 8 step2_106 step2_107) (@block_union good₂ 864 8 8 step2_108 step2_109))) (@block_union good₂ 880 32 32 (@block_union good₂ 880 16 16 (@block_union good₂ 880 8 8 step2_110 step2_111) (@block_union good₂ 896 8 8 step2_112 step2_113)) (@block_union good₂ 912 16 16 (@block_union good₂ 912 8 8 step2_114 step2_115) (@block_union good₂ 928 8 8 step2_116 step2_117)))))))

end OMA.SharedCert867

theorem OMA.solution : type_of% @Erdos867.erdos_867.variants.coppersmith_phillips_upper_bound := by
  apply OMA.CP867.finish
  intro A hA t ht
  by_contra! hsmall
  let b := t-2
  have ht' : b+2=t := by dsimp [b]; omega
  have h : OMA.CP867.cost (fun i => (OMA.CP867.window A i (b+2)).card) < 8 := by
    simpa only [ht', OMA.CP867.cost] using hsmall
  exact OMA.SharedCert867.refute₂ _ (OMA.CP867.model₂ hA h)
