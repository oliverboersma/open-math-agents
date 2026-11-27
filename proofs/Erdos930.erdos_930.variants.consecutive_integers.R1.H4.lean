import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1

/-! Multiplicative Sidon product bound for lengths at least 30000.
The bounded-range proof adapts Marcus Buffett’s H4.R1 reduction and its H1,
H3 and H2.R1.H2 proofs, following Erdős and Selfridge (1975), Section 2.1.
Here the gcd sieve uses the primes through 499 and certifies all widths below
250000. The large-range cover, prime estimate and shifted-factorial argument
are adapted from Ian Qvist’s consecutive_strong proof. We apply the cover to
the image of the given index set and use the standard four-power primorial bound. -/

namespace Erdos930Sidon

namespace ShortRange930
open Finset

def Covers : Prop := ∀ x : ℕ,
  (∃ U V : Finset ℕ, (∀ s : ℕ, 0 < s → s ≤ x → ∃ u ∈ U, ∃ v ∈ V, s=u*v) ∧
    1260*(U.card+V.card.choose 2) ≤ 353*x+383040) ∧
  (∃ U V : Finset ℕ, (∀ s : ℕ, 0 < s → s ≤ x → ∃ u ∈ U, ∃ v ∈ V, s=u*v) ∧
    41580*(U.card+V.card.choose 2) ≤ 9547*x+62037360)

theorem coverBound {S U V : Finset ℕ} (pos : ∀ s ∈ S, 0<s) (uniq : (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ w ∈ S, x*y=z*w → x=z ∨ x=w))
    (cover : ∀ s ∈ S, ∃ u ∈ U, ∃ v ∈ V, s=u*v) :
    S.card ≤ U.card + V.card.choose 2 := by
  classical
  let F (u : ℕ) := V.filter (fun v => u*v ∈ S)
  let P (u : ℕ) := (F u).powersetCard 2
  have disj : (U : Set ℕ).PairwiseDisjoint P := by
    intro u hu t ht hut
    apply Finset.disjoint_left.mpr
    intro pair hp hq
    have m := mem_powersetCard.mp hp
    have n := mem_powersetCard.mp hq
    obtain ⟨v,w,hvw,rfl⟩ := card_eq_two.mp m.2
    have h0 := (mem_filter.mp (m.1 (mem_insert_self ..))).2
    have h1 := (mem_filter.mp (m.1 (mem_insert_of_mem (mem_singleton_self _)))).2
    have h2 := (mem_filter.mp (n.1 (mem_insert_self ..))).2
    have h3 := (mem_filter.mp (n.1 (mem_insert_of_mem (mem_singleton_self _)))).2
    have hpos := pos _ h0
    rcases uniq _ h0 _ h3 _ h1 _ h2 (by ring) with he|he
    · exact hvw (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_mul_pos_right hpos) he)
    · exact hut (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_mul_pos_left hpos) he)
  have subset : U.biUnion P ⊆ V.powersetCard 2 := by
    intro s hs
    obtain ⟨u,_,hu⟩ := mem_biUnion.mp hs
    have h := mem_powersetCard.mp hu
    exact mem_powersetCard.mpr ⟨h.1.trans (filter_subset ..), h.2⟩
  have pairs := card_le_card subset
  rw [card_biUnion disj,card_powersetCard] at pairs
  have localBound (u : ℕ) : (F u).card ≤ 1 + (P u).card := by
    rw [show (P u).card = (F u).card.choose 2 from card_powersetCard ..]
    generalize (F u).card = m
    cases m with
    | zero => omega
    | succ m => rw [Nat.choose_succ_succ, Nat.choose_one_right]; omega
  have mapped : S ⊆ U.biUnion (fun u => (F u).image (u*·)) := by
    intro s hs
    obtain ⟨u,hu,v,hv,rfl⟩ := cover s hs
    exact mem_biUnion.mpr ⟨u,hu,mem_image.mpr ⟨v, mem_filter.mpr ⟨hv,hs⟩,rfl⟩⟩
  calc S.card ≤ _ := card_le_card mapped
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ u ∈ U, (1+(P u).card) := sum_le_sum (fun u _ => card_image_le.trans (localBound u))
    _ ≤ _ := by rw [sum_add_distrib]; simpa using Nat.add_le_add_left pairs U.card

theorem sortedProd (covers : Covers) {k : ℕ} (a : Fin k → ℕ) (apos : ∀ i, 0 < a i)
    (sid : ∀ i j u v, i ≤ j → u ≤ v → a i*a j = a u*a v → i=u ∧ j=v)
    (T : Finset (Fin k)) :
    let L (i : ℕ) := max i (max ((1260*(i-304)+352)/353) ((41580*(i-1492)+9546)/9547))
   
    (∏ i ∈ range T.card, L (i+1)) ≤ ∏ i ∈ T, a i := by
  classical
  let L (i : ℕ) := max i (max ((1260*(i-304)+352)/353) ((41580*(i-1492)+9546)/9547))
  change (∏ i ∈ range T.card, L (i+1)) ≤ _
  have inj : Function.Injective a := by
    intro i j he
    exact (sid i i j j le_rfl le_rfl (by rw [he])).1
  have pair (i j u v : Fin k) (he : a i*a j = a u*a v) : i=u ∨ i=v := by
    rcases le_total i j with hi|hi <;> rcases le_total u v with hj|hj
    · exact Or.inl (sid _ _ _ _ hi hj he).1
    · exact Or.inr (sid _ _ _ _ hi hj (he.trans (mul_comm ..))).1
    · exact Or.inr (sid _ _ _ _ hi hj ((mul_comm ..).trans he)).2
    · exact Or.inl (sid _ _ _ _ hi hj ((mul_comm ..).trans (he.trans (mul_comm ..)))).2
  let B := T.image a
  have hB : B.card = T.card := card_image_of_injective _ inj
  let b := B.orderEmbOfFin hB
  have bmem (i : Fin T.card) : b i ∈ B := B.orderEmbOfFin_mem _ _
  have lower (i : Fin T.card) : L (i.val+1) ≤ b i := by
    let S := (Iic i).image b
    have hS : S.card = i.val+1 := (card_image_of_injective _ b.injective).trans (Fin.card_Iic _)
    have sinB {s : ℕ} (hs : s ∈ S) : s ∈ B := by
      obtain ⟨t,_,rfl⟩ := mem_image.mp hs
      exact bmem t
    have pos (s : ℕ) (hs : s ∈ S) : 0 < s := by
      obtain ⟨t,_,rfl⟩ := mem_image.mp (sinB hs)
      exact apos t
    have small (s : ℕ) (hs : s ∈ S) : s ≤ b i := by
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hs
      exact b.monotone (mem_Iic.mp ht)
    have uniq : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ w ∈ S, x*y=z*w → x=z ∨ x=w := by
      intro x hx y hy z hz w hw
      obtain ⟨s,_,rfl⟩ := mem_image.mp (sinB hx)
      obtain ⟨t,_,rfl⟩ := mem_image.mp (sinB hy)
      obtain ⟨m,_,rfl⟩ := mem_image.mp (sinB hz)
      obtain ⟨n,_,rfl⟩ := mem_image.mp (sinB hw)
      intro h
      exact (pair s t m n h).imp (congrArg a) (congrArg a)
    have hsmall : S ⊆ Icc 1 (b i) := fun s hs => mem_Icc.mpr ⟨pos s hs,small s hs⟩
    have hc := card_le_card hsmall
    simp only [Nat.card_Icc] at hc
    obtain ⟨⟨U₁,V₁,hc₁,hn₁⟩,⟨U₂,V₂,hc₂,hn₂⟩⟩ := covers (b i)
    have ha := coverBound pos uniq (fun s hs => hc₁ s (pos s hs) (small s hs))
    have hb := coverBound pos uniq (fun s hs => hc₂ s (pos s hs) (small s hs))
    have h1 : 1260*S.card ≤ 353*b i+383040 := by omega
    have h2 : 41580*S.card ≤ 9547*b i+62037360 := by omega
    rw [hS] at h1 h2 hc
    dsimp only [L]
    omega
  rw [← Fin.prod_univ_eq_prod_range]
  calc _ ≤ ∏ i, b i := Finset.prod_le_prod' (fun i _ => lower i)
    _ = ∏ s ∈ B, s := by
      conv_rhs => rw [← B.image_orderEmbOfFin_univ hB]
      rw [Finset.prod_image b.injective.injOn]
    _ = _ := by dsimp only [B]; rw [Finset.prod_image inj.injOn]

end ShortRange930

namespace Coeff930

def tally (P : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n+1 => tally P n + (P (n+1)).toNat

def scan (P : ℕ → Bool) (d c err : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, t, a => decide (d*a ≤ c*t+err)
  | n+1, t, a => decide (d*a ≤ c*t+err) && scan P d c err n (t+1) (a+(P (t+1)).toNat)

theorem scanSound (P : ℕ → Bool) (d c e n t : ℕ)
    (h : scan P d c e n t (tally P t)) {r : ℕ} (hlo : t ≤ r) (hhi : r ≤ t+n) :
    d*tally P r ≤ c*r+e := by
  induction n generalizing t with
  | zero =>
    have hr : r=t := by omega
    simpa [scan,hr] using h
  | succ n ih =>
    have hh := Bool.and_eq_true_iff.mp h
    rcases eq_or_lt_of_le hlo with hr|hr
    · simpa [hr] using hh.1
    · exact ih (t+1) hh.2 (by omega) (by omega)

theorem wheelBound (P : ℕ → Bool) (m d c e : ℕ) (hm : 0 < m)
    (hper : ∀ n, P (n+m)=P n)
    (hblock : d*tally P m ≤ c*m)
    (hscan : scan P d c e m 0 0) (n : ℕ) :
    d*tally P n ≤ c*n+e := by
  have shift (r : ℕ) : tally P (r+m) = tally P r + tally P m := by
    induction r with
    | zero => simp [tally]
    | succ r ih =>
      rw [show r+1+m=(r+m)+1 by omega, tally, ih,
        show r+m+1=(r+1)+m by omega, hper, tally]
      omega
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ m
    · exact scanSound P d c e m 0 hscan (Nat.zero_le _) (by omega)
    · have prev := ih (n-m) (by omega)
      have he : (n-m)+m=n := by omega
      have hs := shift (n-m)
      rw [he] at hs
      rw [hs,Nat.mul_add]
      calc _ ≤ c*(n-m)+e+c*m := Nat.add_le_add prev hblock
        _ = _ := by have := congrArg (c*·) he; simp only [Nat.mul_add] at this; omega

open Finset

def wheelPart (P : ℕ → Bool) (b : ℕ) : Finset ℕ := ((range b).filter (fun t => P (t+1))).image (·+1)

theorem wheelPart_card (P : ℕ → Bool) (b : ℕ) : (wheelPart P b).card = tally P b := by
  rw [wheelPart, card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)]
  induction b with
  | zero => simp [tally]
  | succ n ih =>
    rw [range_add_one, filter_insert]
    cases h : P (n+1) <;> simp [h,tally,ih]

theorem mem_wheelPart {P : ℕ → Bool} {n b : ℕ} (hn : 0<n) (hb : n≤b) (h : P n) :
    n ∈ wheelPart P b := by
  refine mem_image.mpr ⟨n-1,mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩,by omega⟩
  simpa [show n-1+1=n by omega] using h

end Coeff930

namespace Coeff930
def prLeast2 (n : ℕ) : Bool := decide (n%2 = 0)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
theorem prLeast2Bound (n : ℕ) : 2*(wheelPart prLeast2 n).card ≤ 1*n+0 := by
  rw [wheelPart_card]
  apply wheelBound prLeast2 2 2 1 0 (by decide)
  · intro n
    simp [prLeast2]
  · decide +kernel
  · decide +kernel

def prLeast3 (n : ℕ) : Bool := decide (n%2 ≠ 0 ∧ n%3 = 0)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
theorem prLeast3Bound (n : ℕ) : 6*(wheelPart prLeast3 n).card ≤ 1*n+3 := by
  rw [wheelPart_card]
  apply wheelBound prLeast3 6 6 1 3 (by decide)
  · intro n
    simp [prLeast3, Nat.add_mod]
  · decide +kernel
  · decide +kernel

def prLeast5 (n : ℕ) : Bool := decide (n%2 ≠ 0 ∧ n%3 ≠ 0 ∧ n%5 = 0)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
theorem prLeast5Bound (n : ℕ) : 30*(wheelPart prLeast5 n).card ≤ 2*n+20 := by
  rw [wheelPart_card]
  apply wheelBound prLeast5 30 30 2 20 (by decide)
  · intro n
    simp [prLeast5, Nat.add_mod]
  · decide +kernel
  · decide +kernel

def prLeast7 (n : ℕ) : Bool := decide (n%2 ≠ 0 ∧ n%3 ≠ 0 ∧ n%5 ≠ 0 ∧ n%7 = 0)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
theorem prLeast7Bound (n : ℕ) : 210*(wheelPart prLeast7 n).card ≤ 8*n+196 := by
  rw [wheelPart_card]
  apply wheelBound prLeast7 210 210 8 196 (by decide)
  · intro n
    simp [prLeast7, Nat.add_mod]
  · decide +kernel
  · decide +kernel

def prFree210 (n : ℕ) : Bool := decide (n%2 ≠ 0 ∧ n%3 ≠ 0 ∧ n%5 ≠ 0 ∧ n%7 ≠ 0)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
theorem prFree210Bound (n : ℕ) : 210*(wheelPart prFree210 n).card ≤ 48*n+318 := by
  rw [wheelPart_card]
  apply wheelBound prFree210 210 210 48 318 (by decide)
  · intro n
    simp [prFree210, Nat.add_mod]
  · decide +kernel
  · decide +kernel

def prLeast11 (n : ℕ) : Bool := decide (n%2 ≠ 0 ∧ n%3 ≠ 0 ∧ n%5 ≠ 0 ∧ n%7 ≠ 0 ∧ n%11 = 0)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
theorem prLeast11Bound (n : ℕ) : 2310*(wheelPart prLeast11 n).card ≤ 48*n+3498 := by
  rw [wheelPart_card]
  apply wheelBound prLeast11 2310 2310 48 3498 (by decide)
  · intro n
    simp [prLeast11, Nat.add_mod]
  · decide +kernel
  · decide +kernel

def prFree2310 (n : ℕ) : Bool := decide (n%2 ≠ 0 ∧ n%3 ≠ 0 ∧ n%5 ≠ 0 ∧ n%7 ≠ 0 ∧ n%11 ≠ 0)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
theorem prFree2310Bound (n : ℕ) : 2310*(wheelPart prFree2310 n).card ≤ 480*n+5820 := by
  rw [wheelPart_card]
  apply wheelBound prFree2310 2310 2310 480 5820 (by decide)
  · intro n
    simp [prFree2310, Nat.add_mod]
  · decide +kernel
  · decide +kernel

end Coeff930

namespace Coeff930
open Finset

theorem maxFactor {V : Finset ℕ} (h1 : 1 ∈ V) {s : ℕ} (hs : 0<s) :
    ∃ u v : ℕ, 0<u ∧ 0<v ∧ v ∈ V ∧ s=u*v ∧
      ∀ p : ℕ, 1<p → p ∣ u → p*v ∉ V := by
  classical
  let D := V.filter (· ∣ s)
  have hD : D.Nonempty := ⟨1,mem_filter.mpr ⟨h1,one_dvd _⟩⟩
  let v := D.max' hD
  have hv := mem_filter.mp (D.max'_mem hD)
  obtain ⟨u,hu⟩ := hv.2
  have hval : s=u*v := hu.trans (Nat.mul_comm _ _)
  have hpos : 0 < u*v := hval ▸ hs
  have uv := Nat.pos_of_mul_pos_right hpos
  have vv := Nat.pos_of_mul_pos_left hpos
  refine ⟨u,v,uv,vv,hv.1,hval,?_⟩
  intro p hp hd hmem
  have hdv : p*v ∣ s := hval ▸ mul_dvd_mul hd (dvd_refl v)
  have hl := D.le_max' (p*v) (mem_filter.mpr ⟨hmem,hdv⟩)
  change p*v ≤ v at hl
  have := Nat.mul_lt_mul_of_pos_right hp vv
  omega

end Coeff930

namespace Coeff930
open Finset
private def VA : Finset ℕ := ([1,2,3,4,5,6,7,8,9,10,12,14,15,16,18,20,21,24,25,27,28,30,32,35,36] : List ℕ).toFinset

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
private lemma closeA2 : ∀ v ∈ VA, v < 20 → 2*v ∈ VA := by
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
private lemma closeA3 : ∀ v ∈ VA, v < 14 → 3*v ∈ VA := by
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
private lemma closeA5 : ∀ v ∈ VA, v < 8 → 5*v ∈ VA := by
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
private lemma closeA7 : ∀ v ∈ VA, v < 6 → 7*v ∈ VA := by
  decide +kernel

private def UA (x : ℕ) := wheelPart prLeast2 (x/20) ∪ wheelPart prLeast3 (x/14) ∪ wheelPart prLeast5 (x/8) ∪ wheelPart prLeast7 (x/6) ∪ wheelPart prFree210 (x/1)

theorem coverA (x s : ℕ) (hs : 0 < s) (hx : s ≤ x) : ∃ u ∈ UA x, ∃ v ∈ VA, s=u*v := by
  obtain ⟨u,v,hu,hv,hV,he,hmax⟩ := maxFactor (V := VA) (by decide) hs
  refine ⟨u, ?_, v,hV,he⟩
  have hup : u*v ≤ x := he ▸ hx
  by_cases h2 : u%2=0
  · have hd := Nat.dvd_of_mod_eq_zero h2
    have hh : 20 ≤ v := by
      by_contra! hlt
      exact hmax 2 (by decide) hd (closeA2 v hV hlt)
    have hle : u ≤ x/20 := (Nat.le_div_iff_mul_le (by decide)).mpr ((Nat.mul_le_mul_left u hh).trans hup)
    have hmem : u ∈ wheelPart prLeast2 (x/20) := mem_wheelPart hu hle (by simp [prLeast2,h2])
    simp only [UA,Finset.mem_union]
    tauto
  by_cases h3 : u%3=0
  · have hd := Nat.dvd_of_mod_eq_zero h3
    have hh : 14 ≤ v := by
      by_contra! hlt
      exact hmax 3 (by decide) hd (closeA3 v hV hlt)
    have hle : u ≤ x/14 := (Nat.le_div_iff_mul_le (by decide)).mpr ((Nat.mul_le_mul_left u hh).trans hup)
    have hmem : u ∈ wheelPart prLeast3 (x/14) := mem_wheelPart hu hle (by simp [prLeast3,h2,h3])
    simp only [UA,Finset.mem_union]
    tauto
  by_cases h5 : u%5=0
  · have hd := Nat.dvd_of_mod_eq_zero h5
    have hh : 8 ≤ v := by
      by_contra! hlt
      exact hmax 5 (by decide) hd (closeA5 v hV hlt)
    have hle : u ≤ x/8 := (Nat.le_div_iff_mul_le (by decide)).mpr ((Nat.mul_le_mul_left u hh).trans hup)
    have hmem : u ∈ wheelPart prLeast5 (x/8) := mem_wheelPart hu hle (by simp [prLeast5,h2,h3,h5])
    simp only [UA,Finset.mem_union]
    tauto
  by_cases h7 : u%7=0
  · have hd := Nat.dvd_of_mod_eq_zero h7
    have hh : 6 ≤ v := by
      by_contra! hlt
      exact hmax 7 (by decide) hd (closeA7 v hV hlt)
    have hle : u ≤ x/6 := (Nat.le_div_iff_mul_le (by decide)).mpr ((Nat.mul_le_mul_left u hh).trans hup)
    have hmem : u ∈ wheelPart prLeast7 (x/6) := mem_wheelPart hu hle (by simp [prLeast7,h2,h3,h5,h7])
    simp only [UA,Finset.mem_union]
    tauto
  have hle : u ≤ x/1 := by simpa using (Nat.le_mul_of_pos_right u hv).trans hup
  have hmem : u ∈ wheelPart prFree210 (x/1) := mem_wheelPart hu hle (by simp [prFree210,h2,h3,h5,h7])
  simp only [UA,Finset.mem_union]
  tauto

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
theorem sizeA (x : ℕ) : 1260 * (UA x).card ≤ 353*x+5040 := by
  have h0 := prLeast2Bound (x/20)
  have h1 := prLeast3Bound (x/14)
  have h2 := prLeast5Bound (x/8)
  have h3 := prLeast7Bound (x/6)
  have h4 := prFree210Bound (x/1)
  have total : (UA x).card ≤ (wheelPart prLeast2 (x/20)).card + (wheelPart prLeast3 (x/14)).card + (wheelPart prLeast5 (x/8)).card + (wheelPart prLeast7 (x/6)).card + (wheelPart prFree210 (x/1)).card := by
    dsimp only [UA]
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    exact Finset.card_union_le _ _
  omega

end Coeff930

namespace Coeff930
open Finset
private def VB : Finset ℕ := ([1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,18,20,21,22,24,25,27,28,30,32,33,35,36,40,42,44,45,48,49,50,54,55,56,60,63,64,66,70,72,75,77,80,81,84,88,90,96,98,99,100] : List ℕ).toFinset

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
private lemma closeB2 : ∀ v ∈ VB, v < 54 → 2*v ∈ VB := by
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
private lemma closeB3 : ∀ v ∈ VB, v < 35 → 3*v ∈ VB := by
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
private lemma closeB5 : ∀ v ∈ VB, v < 21 → 5*v ∈ VB := by
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
private lemma closeB7 : ∀ v ∈ VB, v < 15 → 7*v ∈ VB := by
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
private lemma closeB11 : ∀ v ∈ VB, v < 10 → 11*v ∈ VB := by
  decide +kernel

private def UB (x : ℕ) := wheelPart prLeast2 (x/54) ∪ wheelPart prLeast3 (x/35) ∪ wheelPart prLeast5 (x/21) ∪ wheelPart prLeast7 (x/15) ∪ wheelPart prLeast11 (x/10) ∪ wheelPart prFree2310 (x/1)

theorem coverB (x s : ℕ) (hs : 0 < s) (hx : s ≤ x) : ∃ u ∈ UB x, ∃ v ∈ VB, s=u*v := by
  obtain ⟨u,v,hu,hv,hV,he,hmax⟩ := maxFactor (V := VB) (by decide) hs
  refine ⟨u, ?_, v,hV,he⟩
  have hup : u*v ≤ x := he ▸ hx
  by_cases h2 : u%2=0
  · have hd := Nat.dvd_of_mod_eq_zero h2
    have hh : 54 ≤ v := by
      by_contra! hlt
      exact hmax 2 (by decide) hd (closeB2 v hV hlt)
    have hle : u ≤ x/54 := (Nat.le_div_iff_mul_le (by decide)).mpr ((Nat.mul_le_mul_left u hh).trans hup)
    have hmem : u ∈ wheelPart prLeast2 (x/54) := mem_wheelPart hu hle (by simp [prLeast2,h2])
    simp only [UB,Finset.mem_union]
    tauto
  by_cases h3 : u%3=0
  · have hd := Nat.dvd_of_mod_eq_zero h3
    have hh : 35 ≤ v := by
      by_contra! hlt
      exact hmax 3 (by decide) hd (closeB3 v hV hlt)
    have hle : u ≤ x/35 := (Nat.le_div_iff_mul_le (by decide)).mpr ((Nat.mul_le_mul_left u hh).trans hup)
    have hmem : u ∈ wheelPart prLeast3 (x/35) := mem_wheelPart hu hle (by simp [prLeast3,h2,h3])
    simp only [UB,Finset.mem_union]
    tauto
  by_cases h5 : u%5=0
  · have hd := Nat.dvd_of_mod_eq_zero h5
    have hh : 21 ≤ v := by
      by_contra! hlt
      exact hmax 5 (by decide) hd (closeB5 v hV hlt)
    have hle : u ≤ x/21 := (Nat.le_div_iff_mul_le (by decide)).mpr ((Nat.mul_le_mul_left u hh).trans hup)
    have hmem : u ∈ wheelPart prLeast5 (x/21) := mem_wheelPart hu hle (by simp [prLeast5,h2,h3,h5])
    simp only [UB,Finset.mem_union]
    tauto
  by_cases h7 : u%7=0
  · have hd := Nat.dvd_of_mod_eq_zero h7
    have hh : 15 ≤ v := by
      by_contra! hlt
      exact hmax 7 (by decide) hd (closeB7 v hV hlt)
    have hle : u ≤ x/15 := (Nat.le_div_iff_mul_le (by decide)).mpr ((Nat.mul_le_mul_left u hh).trans hup)
    have hmem : u ∈ wheelPart prLeast7 (x/15) := mem_wheelPart hu hle (by simp [prLeast7,h2,h3,h5,h7])
    simp only [UB,Finset.mem_union]
    tauto
  by_cases h11 : u%11=0
  · have hd := Nat.dvd_of_mod_eq_zero h11
    have hh : 10 ≤ v := by
      by_contra! hlt
      exact hmax 11 (by decide) hd (closeB11 v hV hlt)
    have hle : u ≤ x/10 := (Nat.le_div_iff_mul_le (by decide)).mpr ((Nat.mul_le_mul_left u hh).trans hup)
    have hmem : u ∈ wheelPart prLeast11 (x/10) := mem_wheelPart hu hle (by simp [prLeast11,h2,h3,h5,h7,h11])
    simp only [UB,Finset.mem_union]
    tauto
  have hle : u ≤ x/1 := by simpa using (Nat.le_mul_of_pos_right u hv).trans hup
  have hmem : u ∈ wheelPart prFree2310 (x/1) := mem_wheelPart hu hle (by simp [prFree2310,h2,h3,h5,h7,h11])
  simp only [UB,Finset.mem_union]
  tauto

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
theorem sizeB (x : ℕ) : 41580 * (UB x).card ≤ 9547*x+291060 := by
  have h0 := prLeast2Bound (x/54)
  have h1 := prLeast3Bound (x/35)
  have h2 := prLeast5Bound (x/21)
  have h3 := prLeast7Bound (x/15)
  have h4 := prLeast11Bound (x/10)
  have h5 := prFree2310Bound (x/1)
  have total : (UB x).card ≤ (wheelPart prLeast2 (x/54)).card + (wheelPart prLeast3 (x/35)).card + (wheelPart prLeast5 (x/21)).card + (wheelPart prLeast7 (x/15)).card + (wheelPart prLeast11 (x/10)).card + (wheelPart prFree2310 (x/1)).card := by
    dsimp only [UB]
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    exact Finset.card_union_le _ _
  omega

end Coeff930

open Coeff930

theorem coefficientCovers : ShortRange930.Covers := by
  intro x
  constructor
  · refine ⟨UA x,VA,coverA x,?_⟩
    have hc : VA.card.choose 2 = 300 := by decide +kernel
    rw [hc]
    have := sizeA x
    omega
  · refine ⟨UB x,VB,coverB x,?_⟩
    have hc : VB.card.choose 2 = 1485 := by decide +kernel
    rw [hc]
    have := sizeB x
    omega

open Finset

namespace OMA930

def Lf (i : ℕ) : ℕ :=
  max i (max ((1260*(i-304)+352)/353) ((41580*(i-1492)+9546)/9547))

/-- The product of `k` consecutive values of `g` starting at `i`. -/
def blk (g : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, i => g i * blk g k (i + 1)

/-- The product of `j` consecutive blocks of 150 values of `g` starting at `i`. -/
def out (g : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | j + 1, i => blk g 150 i * out g j (i + 150)

lemma blk_eq (g : ℕ → ℕ) : ∀ k i, blk g k i = ∏ t ∈ range k, g (i + t) := by
  intro k
  induction k with
  | zero =>
    intro i
    simp [blk]
  | succ k ih =>
    intro i
    rw [blk, ih, Finset.prod_range_succ', Nat.add_zero, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    congr 1
    omega

lemma out_eq (g : ℕ → ℕ) : ∀ j i, out g j i = ∏ t ∈ range (150 * j), g (i + t) := by
  intro j
  induction j with
  | zero =>
    intro i
    simp [out]
  | succ j ih =>
    intro i
    rw [out, ih, blk_eq, show 150 * (j + 1) = 150 + 150 * j by ring, Finset.prod_range_add]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Nat.add_assoc]

lemma base : Nat.ble (out (fun i => 18 * (i + 1)) 178 0)
    (out (fun i => 5 * Lf (i + 1)) 178 0) = true := by decide +kernel

lemma Q : ∀ m, 26700 ≤ m →
    ∏ t ∈ range m, 18 * (t + 1) ≤ ∏ t ∈ range m, 5 * Lf (t + 1) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have h := Nat.le_of_ble_eq_true base
    rw [out_eq, out_eq] at h
    have h150 : 150 * 178 = 26700 := by norm_num
    rw [h150] at h
    simp only [zero_add] at h
    exact h
  | succ m hm ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    refine Nat.mul_le_mul ih ?_
    have h1 : (41580*(m+1-1492)+9546)/9547 ≤ Lf (m+1) :=
      le_max_of_le_right (le_max_right _ _)
    omega

lemma exp_bound : Real.exp (51/40) < 18/5 := by
  have h1 : Real.exp (51/40) ^ 40 = Real.exp 1 ^ 51 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    norm_num
  have h2 : Real.exp 1 ^ 51 < (2.7182818286 : ℝ) ^ 51 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h3 : (2.7182818286 : ℝ) ^ 51 ≤ (18/5) ^ 40 := by norm_num
  refine lt_of_pow_lt_pow_left₀ 40 (by norm_num) ?_
  rw [h1]
  exact h2.trans_le h3

theorem main : ∀ m : ℕ, 26700 ≤ m →
    (51:ℝ)/40*m ≤ Real.log ((∏ i ∈ range m, Lf (i+1) : ℕ) : ℝ) -
      Real.log (m.factorial : ℝ) := by
  intro m hm
  have hq := Q m hm
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_range, Finset.prod_range_add_one_eq_factorial] at hq
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = ∏ i ∈ range m, Lf (i+1) := ⟨_, rfl⟩
  rw [← hP] at hq ⊢
  have hqR : (18:ℝ)^m * (m.factorial : ℝ) ≤ 5^m * (P : ℝ) := by exact_mod_cast hq
  have hf : (0:ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hl : (0:ℝ) < 18^m * (m.factorial : ℝ) := by positivity
  have hPpos : (0:ℝ) < P := by
    by_contra h
    have h0 : (P:ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [h0, mul_zero] at hqR
    linarith
  have hlog := Real.log_le_log hl hqR
  rw [Real.log_mul (by positivity) hf.ne', Real.log_mul (by positivity) hPpos.ne',
    Real.log_pow, Real.log_pow] at hlog
  have h185 : (51:ℝ)/40 ≤ Real.log 18 - Real.log 5 := by
    rw [← Real.log_div (by norm_num) (by norm_num), Real.le_log_iff_exp_le (by norm_num)]
    exact exp_bound.le
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have h4 := mul_le_mul_of_nonneg_left h185 hm0
  linarith

end OMA930

namespace ShortRange930

theorem bounded (k : ℕ) (a : Fin k → ℕ) (hk : 30000 ≤ k) (apos : ∀ i, 0 < a i)
    (sid : ∀ i j u v, i ≤ j → u ≤ v → a i*a j = a u*a v → i=u ∧ j=v)
    (T : Finset (Fin k)) (hT : k - k.primesBelow.card ≤ T.card)
    (px' : (k.primesBelow.card : ℝ) * (Real.log k-6/5) ≤ k) :
    (k-1).factorial < ∏ i ∈ T, a i := by
  classical
  let L (i : ℕ) := max i (max ((1260*(i-304)+352)/353) ((41580*(i-1492)+9546)/9547))
  let r := k.primesBelow.card
  let m := k-r
  have hl : r ≤ k := by
    change (k.primesBelow).card ≤ k
    simpa using card_le_card (show k.primesBelow ⊆ range k from
      fun p hp => mem_range.mpr (Nat.lt_of_mem_primesBelow hp))
  have hmk : m+r=k := Nat.sub_add_cancel hl
  have hmkr : (m:ℝ)+(r:ℝ)=(k:ℝ) := by exact_mod_cast hmk
  have px : (r:ℝ)*(Real.log k-6/5) ≤ k := px'
  have hklarge : (30000:ℝ) ≤ k := by exact_mod_cast hk
  have logk : (103/10:ℝ) ≤ Real.log k := by
    have p : (2:ℝ)^1041 ≤ (k:ℝ)^70 := (show (2:ℝ)^1041 ≤ 30000^70 by exact_mod_cast (by decide +kernel : (2:ℕ)^1041 ≤ 30000^70)).trans
      (pow_le_pow_left₀ (by norm_num) hklarge _)
    have h := Real.log_le_log (show 0 < (2:ℝ)^1041 by positivity) p
    rw [Real.log_pow,Real.log_pow] at h
    norm_num1 at h
    linarith [Real.log_two_gt_d9]
  have frac : 100*(r:ℝ) ≤ 11*k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr logk) (Nat.cast_nonneg (α:=ℝ) r)]
  have hm : 26700 ≤ m := by
    have hn : 26700 ≤ (m:ℝ) := by linarith
    exact_mod_cast hn
  have kr : (r:ℝ)*Real.log k < (51:ℝ)/40*m := by linarith
  let Z := ∏ i ∈ range m, L (i+1)
  have gz : (51:ℝ)/40*m ≤ Real.log (Z:ℝ) - Real.log (m.factorial:ℝ) := OMA930.main m hm
  have hpow : m.factorial * k^r < Z := by
    by_contra! hn
    have posZ : 0 < Z := Finset.prod_pos (fun i _ => lt_of_lt_of_le (Nat.succ_pos i) (le_max_left ..))
    have hlog := Real.log_le_log (show 0 < (Z:ℝ) by exact_mod_cast posZ)
      (show (Z:ℝ) ≤ (m.factorial:ℕ) * (k:ℝ)^r by exact_mod_cast hn)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
    linarith
  have hfac : k.factorial ≤ m.factorial*k^r := by
    rw [← Nat.factorial_mul_descFactorial hl]
    exact Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow k r)
  obtain ⟨D,hsub,hc⟩ := Finset.exists_subset_card_eq hT
  have hs := sortedProd coefficientCovers a apos sid D
  change D.card=m at hc
  rw [hc] at hs
  exact ((Nat.factorial_le (show k-1 ≤ k by omega)).trans hfac).trans_lt
    ((hpow.trans_le hs).trans_le (Finset.prod_le_prod_of_subset_of_one_le' hsub (fun i _ _ => apos i)))

end ShortRange930

namespace OMA930b

def Q : ℕ := 124846525121166472890127769845656706959834701767553316679575342375728606681436245953703527478773456698735316531921607496638484885416740029028542605893861455745313937474271661656548230159065196413238268640890

def isP (n : ℕ) : Bool := if n < 500 then decide n.Prime else Nat.beq (Nat.gcd n Q) 1

def blkCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => (isP n).toNat + blkCount k (n + 1)

set_option maxRecDepth 10000 in
private theorem Q_eq : Q = primorial 499 := by decide +kernel

lemma prime_isP {n : ℕ} (hp : n.Prime) : isP n = true := by
  unfold isP
  split_ifs with h
  · simpa using hp
  · have hnd : ¬ n ∣ Q := by
      rw [Q_eq, hp.dvd_primorial_iff]
      omega
    have hcop : Nat.gcd n Q = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    rw [hcop]
    rfl

lemma count_add_le : ∀ len b,
    Nat.count Nat.Prime (b + len) ≤ Nat.count Nat.Prime b + blkCount len b := by
  intro len
  induction len with
  | zero =>
    intro b
    simp [blkCount]
  | succ len ih =>
    intro b
    have h1 := ih (b + 1)
    have h2 : b + (len + 1) = b + 1 + len := by omega
    rw [h2, blkCount]
    have h3 : Nat.count Nat.Prime (b + 1) ≤ Nat.count Nat.Prime b + (isP b).toNat := by
      rw [Nat.count_succ]
      by_cases hp : Nat.Prime b
      · rw [if_pos hp, prime_isP hp]
        exact le_of_eq rfl
      · rw [if_neg hp]
        omega
    omega

def Cnt (b c : ℕ) : Prop := Nat.count Nat.Prime b ≤ c

lemma cstep (b len c d : ℕ) (h : Cnt b c) (hd : blkCount len b = d) :
    Cnt (b + len) (c + d) := by
  have h1 := count_add_le len b
  unfold Cnt at *
  omega

lemma log_30000 : Real.log 30000 ≤ 10.32 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 10.32 = Real.exp 1 ^ 10 * Real.exp 0.32 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  rw [h1]
  have h2 : (2.7182818283:ℝ) ^ 10 ≤ Real.exp 1 ^ 10 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 10
  have h3 : (1.3712:ℝ) ≤ Real.exp 0.32 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 0.32)
    exact le_trans (by norm_num) h
  have h4 : (22026:ℝ) ≤ (2.7182818283:ℝ) ^ 10 := by norm_num
  calc (30000:ℝ) ≤ 22026 * 1.3712 := by norm_num
    _ ≤ Real.exp 1 ^ 10 * Real.exp 0.32 :=
        mul_le_mul (h4.trans h2) h3 (by norm_num) (by positivity)

lemma log_grid (a' j : ℕ) (hpos : 0 < a') (hgrid : a' * 1000 ^ j ≤ 30000 * 1004 ^ j) :
    Real.log a' ≤ 10.32 + 0.004 * j := by
  have hR : (a':ℝ) * 1000 ^ j ≤ 30000 * 1004 ^ j := by exact_mod_cast hgrid
  have ha : (0:ℝ) < a' := by exact_mod_cast hpos
  have h := Real.log_le_log (by positivity) hR
  rw [Real.log_mul ha.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_pow, Real.log_pow] at h
  have h1 : Real.log 1004 - Real.log 1000 ≤ 0.004 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 1004 / 1000)).trans (by norm_num)
  have h2 := log_30000
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have h3 := mul_le_mul_of_nonneg_left h1 hj
  linarith

lemma interval (a a' P j : ℕ) (ha : 30000 ≤ a) (hc : Cnt a' P)
    (hgrid : a' * 1000 ^ j ≤ 30000 * 1004 ^ j) (hnum : P * (9120 + 4 * j) ≤ 1000 * a)
    (k : ℕ) (hak : a ≤ k) (hka : k < a') :
    (k.primesBelow.card : ℝ) * (Real.log k - 6/5) ≤ k := by
  have hk3 : (30000:ℝ) ≤ k := by exact_mod_cast (by omega : 30000 ≤ k)
  have hkpos : (0:ℝ) < k := by linarith
  have hcard : (k.primesBelow.card : ℝ) ≤ P := by
    have h1 : k.primesBelow.card ≤ P := by
      rw [Nat.primesBelow_card_eq_primeCounting']
      show Nat.count Nat.Prime k ≤ P
      exact le_trans (Nat.count_monotone _ hka.le) hc
    exact_mod_cast h1
  have hlogk : Real.log k ≤ 10.32 + 0.004 * j :=
    (Real.log_le_log hkpos (by exact_mod_cast hka.le)).trans (log_grid a' j (by omega) hgrid)
  have hlog0 : (6/5 : ℝ) ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le hkpos]
    have h2 : Real.exp (6/5) ≤ Real.exp (1 + 1) := Real.exp_le_exp.2 (by norm_num)
    rw [Real.exp_add] at h2
    have h3 := Real.exp_one_lt_d9
    have h4 := Real.exp_pos 1
    have h5 := mul_lt_mul'' h3 h3 h4.le h4.le
    linarith
  have hnumR : (P:ℝ) * (9120 + 4 * j) ≤ 1000 * a := by exact_mod_cast hnum
  have hakR : (a:ℝ) ≤ k := by exact_mod_cast hak
  have hP0 : (0:ℝ) ≤ P := Nat.cast_nonneg P
  calc (k.primesBelow.card : ℝ) * (Real.log k - 6/5)
      ≤ P * (Real.log k - 6/5) := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ ≤ P * (10.32 + 0.004 * j - 6/5) := mul_le_mul_of_nonneg_left (by linarith) hP0
    _ = (P * (9120 + 4 * j)) / 1000 := by ring
    _ ≤ (1000 * a) / 1000 := div_le_div_of_nonneg_right hnumR (by norm_num)
    _ = a := by ring
    _ ≤ k := hakR

def Good (b : ℕ) : Prop :=
  ∀ k : ℕ, 30000 ≤ k → k < b → (k.primesBelow.card : ℝ) * (Real.log k - 6/5) ≤ k

lemma extend (a a' P j : ℕ) (hg : Good a) (ha : 30000 ≤ a) (hc : Cnt a' P)
    (hgrid : a' * 1000 ^ j ≤ 30000 * 1004 ^ j) (hnum : P * (9120 + 4 * j) ≤ 1000 * a) :
    Good a' := by
  intro k hk hlt
  by_cases h : k < a
  · exact hg k hk h
  · exact interval a a' P j ha hc hgrid hnum k (not_lt.1 h) hlt

private theorem step (a len c d j : ℕ) (h : Good a ∧ Cnt a c)
    (ha : 30000 ≤ a) (hd : blkCount len a = d)
    (hg : (a+len)*1000^j ≤ 30000*1004^j) (hn : (c+d)*(9120+4*j) ≤ 1000*a) :
    Good (a+len) ∧ Cnt (a+len) (c+d) := by
  have hc := cstep a len c d h.2 hd
  exact ⟨extend a (a+len) (c+d) j h.1 ha hc hg hn, hc⟩

private lemma p0 : Cnt 0 0 := by simp [Cnt]
private lemma p500 : Cnt 500 95 := cstep 0 500 0 95 p0 (by decide +kernel)
private lemma p1000 : Cnt 1000 168 := cstep 500 500 95 73 p500 (by decide +kernel)
private lemma p1500 : Cnt 1500 239 := cstep 1000 500 168 71 p1000 (by decide +kernel)
private lemma p2000 : Cnt 2000 303 := cstep 1500 500 239 64 p1500 (by decide +kernel)
private lemma p2500 : Cnt 2500 367 := cstep 2000 500 303 64 p2000 (by decide +kernel)
private lemma p3000 : Cnt 3000 430 := cstep 2500 500 367 63 p2500 (by decide +kernel)
private lemma p3500 : Cnt 3500 489 := cstep 3000 500 430 59 p3000 (by decide +kernel)
private lemma p4000 : Cnt 4000 550 := cstep 3500 500 489 61 p3500 (by decide +kernel)
private lemma p4500 : Cnt 4500 610 := cstep 4000 500 550 60 p4000 (by decide +kernel)
private lemma p5000 : Cnt 5000 669 := cstep 4500 500 610 59 p4500 (by decide +kernel)
private lemma p5500 : Cnt 5500 725 := cstep 5000 500 669 56 p5000 (by decide +kernel)
private lemma p6000 : Cnt 6000 783 := cstep 5500 500 725 58 p5500 (by decide +kernel)
private lemma p6500 : Cnt 6500 842 := cstep 6000 500 783 59 p6000 (by decide +kernel)
private lemma p7000 : Cnt 7000 900 := cstep 6500 500 842 58 p6500 (by decide +kernel)
private lemma p7500 : Cnt 7500 950 := cstep 7000 500 900 50 p7000 (by decide +kernel)
private lemma p8000 : Cnt 8000 1007 := cstep 7500 500 950 57 p7500 (by decide +kernel)
private lemma p8500 : Cnt 8500 1059 := cstep 8000 500 1007 52 p8000 (by decide +kernel)
private lemma p9000 : Cnt 9000 1117 := cstep 8500 500 1059 58 p8500 (by decide +kernel)
private lemma p9500 : Cnt 9500 1177 := cstep 9000 500 1117 60 p9000 (by decide +kernel)
private lemma p10000 : Cnt 10000 1229 := cstep 9500 500 1177 52 p9500 (by decide +kernel)
private lemma p10500 : Cnt 10500 1284 := cstep 10000 500 1229 55 p10000 (by decide +kernel)
private lemma p11000 : Cnt 11000 1335 := cstep 10500 500 1284 51 p10500 (by decide +kernel)
private lemma p11500 : Cnt 11500 1387 := cstep 11000 500 1335 52 p11000 (by decide +kernel)
private lemma p12000 : Cnt 12000 1438 := cstep 11500 500 1387 51 p11500 (by decide +kernel)
private lemma p12500 : Cnt 12500 1492 := cstep 12000 500 1438 54 p12000 (by decide +kernel)
private lemma p13000 : Cnt 13000 1547 := cstep 12500 500 1492 55 p12500 (by decide +kernel)
private lemma p13500 : Cnt 13500 1600 := cstep 13000 500 1547 53 p13000 (by decide +kernel)
private lemma p14000 : Cnt 14000 1652 := cstep 13500 500 1600 52 p13500 (by decide +kernel)
private lemma p14500 : Cnt 14500 1698 := cstep 14000 500 1652 46 p14000 (by decide +kernel)
private lemma p15000 : Cnt 15000 1754 := cstep 14500 500 1698 56 p14500 (by decide +kernel)
private lemma p15500 : Cnt 15500 1810 := cstep 15000 500 1754 56 p15000 (by decide +kernel)
private lemma p16000 : Cnt 16000 1862 := cstep 15500 500 1810 52 p15500 (by decide +kernel)
private lemma p16500 : Cnt 16500 1912 := cstep 16000 500 1862 50 p16000 (by decide +kernel)
private lemma p17000 : Cnt 17000 1960 := cstep 16500 500 1912 48 p16500 (by decide +kernel)
private lemma p17500 : Cnt 17500 2014 := cstep 17000 500 1960 54 p17000 (by decide +kernel)
private lemma p18000 : Cnt 18000 2064 := cstep 17500 500 2014 50 p17500 (by decide +kernel)
private lemma p18500 : Cnt 18500 2118 := cstep 18000 500 2064 54 p18000 (by decide +kernel)
private lemma p19000 : Cnt 19000 2158 := cstep 18500 500 2118 40 p18500 (by decide +kernel)
private lemma p19500 : Cnt 19500 2212 := cstep 19000 500 2158 54 p19000 (by decide +kernel)
private lemma p20000 : Cnt 20000 2262 := cstep 19500 500 2212 50 p19500 (by decide +kernel)
private lemma p20500 : Cnt 20500 2313 := cstep 20000 500 2262 51 p20000 (by decide +kernel)
private lemma p21000 : Cnt 21000 2360 := cstep 20500 500 2313 47 p20500 (by decide +kernel)
private lemma p21500 : Cnt 21500 2412 := cstep 21000 500 2360 52 p21000 (by decide +kernel)
private lemma p22000 : Cnt 22000 2464 := cstep 21500 500 2412 52 p21500 (by decide +kernel)
private lemma p22500 : Cnt 22500 2515 := cstep 22000 500 2464 51 p22000 (by decide +kernel)
private lemma p23000 : Cnt 23000 2564 := cstep 22500 500 2515 49 p22500 (by decide +kernel)
private lemma p23500 : Cnt 23500 2613 := cstep 23000 500 2564 49 p23000 (by decide +kernel)
private lemma p24000 : Cnt 24000 2668 := cstep 23500 500 2613 55 p23500 (by decide +kernel)
private lemma p24500 : Cnt 24500 2718 := cstep 24000 500 2668 50 p24000 (by decide +kernel)
private lemma p25000 : Cnt 25000 2762 := cstep 24500 500 2718 44 p24500 (by decide +kernel)
private lemma p25500 : Cnt 25500 2810 := cstep 25000 500 2762 48 p25000 (by decide +kernel)
private lemma p26000 : Cnt 26000 2860 := cstep 25500 500 2810 50 p25500 (by decide +kernel)
private lemma p26500 : Cnt 26500 2910 := cstep 26000 500 2860 50 p26000 (by decide +kernel)
private lemma p27000 : Cnt 27000 2961 := cstep 26500 500 2910 51 p26500 (by decide +kernel)
private lemma p27500 : Cnt 27500 3004 := cstep 27000 500 2961 43 p27000 (by decide +kernel)
private lemma p28000 : Cnt 28000 3055 := cstep 27500 500 3004 51 p27500 (by decide +kernel)
private lemma p28500 : Cnt 28500 3100 := cstep 28000 500 3055 45 p28000 (by decide +kernel)
private lemma p29000 : Cnt 29000 3153 := cstep 28500 500 3100 53 p28500 (by decide +kernel)
private lemma p29500 : Cnt 29500 3203 := cstep 29000 500 3153 50 p29000 (by decide +kernel)
private lemma p30000 : Cnt 30000 3245 := cstep 29500 500 3203 42 p29500 (by decide +kernel)

private lemma g30000 : Good 30000 ∧ Cnt 30000 3245 := ⟨fun _ h1 h2 => by omega, p30000⟩

private lemma g30391 : Good 30391 ∧ Cnt 30391 3283 :=
  step 30000 391 3245 38 4 g30000 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g30829 : Good 30829 ∧ Cnt 30829 3322 :=
  step 30391 438 3283 39 7 g30391 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g31231 : Good 31231 ∧ Cnt 31231 3364 :=
  step 30829 402 3322 42 11 g30829 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g31649 : Good 31649 ∧ Cnt 31649 3403 :=
  step 31231 418 3364 39 14 g31231 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g32099 : Good 32099 ∧ Cnt 32099 3444 :=
  step 31649 450 3403 41 17 g31649 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g32503 : Good 32503 ∧ Cnt 32503 3487 :=
  step 32099 404 3444 43 21 g32099 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g32911 : Good 32911 ∧ Cnt 32911 3526 :=
  step 32503 408 3487 39 24 g32503 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g33317 : Good 33317 ∧ Cnt 33317 3566 :=
  step 32911 406 3526 40 27 g32911 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g33679 : Good 33679 ∧ Cnt 33679 3607 :=
  step 33317 362 3566 41 29 g33317 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g34039 : Good 34039 ∧ Cnt 34039 3641 :=
  step 33679 360 3607 34 32 g33679 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g34403 : Good 34403 ∧ Cnt 34403 3675 :=
  step 34039 364 3641 34 35 g34039 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g34759 : Good 34759 ∧ Cnt 34759 3712 :=
  step 34403 356 3675 37 37 g34403 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g35129 : Good 35129 ∧ Cnt 35129 3745 :=
  step 34759 370 3712 33 40 g34759 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g35521 : Good 35521 ∧ Cnt 35521 3780 :=
  step 35129 392 3745 35 43 g35129 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g35951 : Good 35951 ∧ Cnt 35951 3817 :=
  step 35521 430 3780 37 46 g35521 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g36383 : Good 36383 ∧ Cnt 36383 3859 :=
  step 35951 432 3817 42 49 g35951 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g36787 : Good 36787 ∧ Cnt 36787 3900 :=
  step 36383 404 3859 41 52 g36383 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g37199 : Good 37199 ∧ Cnt 37199 3940 :=
  step 36787 412 3900 40 54 g36787 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g37573 : Good 37573 ∧ Cnt 37573 3979 :=
  step 37199 374 3940 39 57 g37199 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g37991 : Good 37991 ∧ Cnt 37991 4014 :=
  step 37573 418 3979 35 60 g37573 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g38447 : Good 38447 ∧ Cnt 38447 4053 :=
  step 37991 456 4014 39 63 g37991 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g38903 : Good 38903 ∧ Cnt 38903 4097 :=
  step 38447 456 4053 44 66 g38447 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g39356 : Good 39356 ∧ Cnt 39356 4142 :=
  step 38903 453 4097 45 68 g38903 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g39829 : Good 39829 ∧ Cnt 39829 4185 :=
  step 39356 473 4142 43 71 g39356 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g40283 : Good 40283 ∧ Cnt 40283 4229 :=
  step 39829 454 4185 44 74 g39829 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g40801 : Good 40801 ∧ Cnt 40801 4270 :=
  step 40283 518 4229 41 78 g40283 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g41281 : Good 41281 ∧ Cnt 41281 4322 :=
  step 40801 480 4270 52 80 g40801 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g41771 : Good 41771 ∧ Cnt 41771 4367 :=
  step 41281 490 4322 45 83 g41281 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g42221 : Good 42221 ∧ Cnt 42221 4413 :=
  step 41771 450 4367 46 86 g41771 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g42641 : Good 42641 ∧ Cnt 42641 4455 :=
  step 42221 420 4413 42 89 g42221 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g43019 : Good 43019 ∧ Cnt 43019 4496 :=
  step 42641 378 4455 41 91 g42641 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g43486 : Good 43486 ∧ Cnt 43486 4532 :=
  step 43019 467 4496 36 93 g43019 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g43973 : Good 43973 ∧ Cnt 43973 4575 :=
  step 43486 487 4532 43 96 g43486 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g44453 : Good 44453 ∧ Cnt 44453 4620 :=
  step 43973 480 4575 45 99 g43973 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g44909 : Good 44909 ∧ Cnt 44909 4665 :=
  step 44453 456 4620 45 102 g44453 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g45403 : Good 45403 ∧ Cnt 45403 4709 :=
  step 44909 494 4665 44 104 g44909 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g45949 : Good 45949 ∧ Cnt 45949 4755 :=
  step 45403 546 4709 46 107 g45403 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g46507 : Good 46507 ∧ Cnt 46507 4806 :=
  step 45949 558 4755 51 110 g45949 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g47101 : Good 47101 ∧ Cnt 47101 4858 :=
  step 46507 594 4806 52 113 g46507 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g47668 : Good 47668 ∧ Cnt 47668 4914 :=
  step 47101 567 4858 56 116 g47101 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g48247 : Good 48247 ∧ Cnt 48247 4965 :=
  step 47668 579 4914 51 120 g47668 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g48823 : Good 48823 ∧ Cnt 48823 5021 :=
  step 48247 576 4965 56 122 g48247 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g49409 : Good 49409 ∧ Cnt 49409 5075 :=
  step 48823 586 5021 54 125 g48823 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g49957 : Good 49957 ∧ Cnt 49957 5129 :=
  step 49409 548 5075 54 128 g49409 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g50513 : Good 50513 ∧ Cnt 50513 5180 :=
  step 49957 556 5129 51 131 g49957 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g51133 : Good 51133 ∧ Cnt 51133 5231 :=
  step 50513 620 5180 51 134 g50513 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g51679 : Good 51679 ∧ Cnt 51679 5288 :=
  step 51133 546 5231 57 137 g51133 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g52249 : Good 52249 ∧ Cnt 52249 5340 :=
  step 51679 570 5288 52 139 g51679 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g52861 : Good 52861 ∧ Cnt 52861 5393 :=
  step 52249 612 5340 53 142 g52249 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g53441 : Good 53441 ∧ Cnt 53441 5449 :=
  step 52861 580 5393 56 145 g52861 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g54013 : Good 54013 ∧ Cnt 54013 5502 :=
  step 53441 572 5449 53 148 g53441 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g54598 : Good 54598 ∧ Cnt 54598 5556 :=
  step 54013 585 5502 54 150 g54013 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g55219 : Good 55219 ∧ Cnt 55219 5610 :=
  step 54598 621 5556 54 153 g54598 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g55829 : Good 55829 ∧ Cnt 55829 5666 :=
  step 55219 610 5610 56 156 g55219 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g56453 : Good 56453 ∧ Cnt 56453 5722 :=
  step 55829 624 5666 56 159 g55829 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g56999 : Good 56999 ∧ Cnt 56999 5781 :=
  step 56453 546 5722 59 161 g56453 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g57557 : Good 57557 ∧ Cnt 57557 5830 :=
  step 56999 558 5781 49 164 g56999 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g58099 : Good 58099 ∧ Cnt 58099 5882 :=
  step 57557 542 5830 52 166 g57557 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g58657 : Good 58657 ∧ Cnt 58657 5933 :=
  step 58099 558 5882 51 168 g58099 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g59167 : Good 59167 ∧ Cnt 59167 5982 :=
  step 58657 510 5933 49 171 g58657 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g59663 : Good 59663 ∧ Cnt 59663 6030 :=
  step 59167 496 5982 48 173 g59167 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g60169 : Good 60169 ∧ Cnt 60169 6075 :=
  step 59663 506 6030 45 175 g59663 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g60737 : Good 60737 ∧ Cnt 60737 6122 :=
  step 60169 568 6075 47 177 g60169 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g61357 : Good 61357 ∧ Cnt 61357 6172 :=
  step 60737 620 6122 50 180 g60737 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g61987 : Good 61987 ∧ Cnt 61987 6230 :=
  step 61357 630 6172 58 182 g61357 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g62627 : Good 62627 ∧ Cnt 62627 6286 :=
  step 61987 640 6230 56 185 g61987 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g63317 : Good 63317 ∧ Cnt 63317 6343 :=
  step 62627 690 6286 57 188 g62627 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g63913 : Good 63913 ∧ Cnt 63913 6408 :=
  step 63317 596 6343 65 190 g63317 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g64613 : Good 64613 ∧ Cnt 64613 6461 :=
  step 63913 700 6408 53 193 g63913 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g65342 : Good 65342 ∧ Cnt 65342 6526 :=
  step 64613 729 6461 65 195 g64613 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g66037 : Good 66037 ∧ Cnt 66037 6592 :=
  step 65342 695 6526 66 198 g65342 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g66763 : Good 66763 ∧ Cnt 66763 6654 :=
  step 66037 726 6592 62 201 g66037 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g67462 : Good 67462 ∧ Cnt 67462 6720 :=
  step 66763 699 6654 66 203 g66763 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g68147 : Good 68147 ∧ Cnt 68147 6784 :=
  step 67462 685 6720 64 206 g67462 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g68891 : Good 68891 ∧ Cnt 68891 6844 :=
  step 68147 744 6784 60 209 g68147 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g69641 : Good 69641 ∧ Cnt 69641 6906 :=
  step 68891 750 6844 62 211 g68891 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g70391 : Good 70391 ∧ Cnt 70391 6975 :=
  step 69641 750 6906 69 214 g69641 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g71141 : Good 71141 ∧ Cnt 71141 7042 :=
  step 70391 750 6975 67 217 g70391 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g71891 : Good 71891 ∧ Cnt 71891 7116 :=
  step 71141 750 7042 74 219 g71141 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g72641 : Good 72641 ∧ Cnt 72641 7181 :=
  step 71891 750 7116 65 222 g71891 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g73391 : Good 73391 ∧ Cnt 73391 7249 :=
  step 72641 750 7181 68 225 g72641 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g74141 : Good 74141 ∧ Cnt 74141 7312 :=
  step 73391 750 7249 63 227 g73391 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g74887 : Good 74887 ∧ Cnt 74887 7384 :=
  step 74141 746 7312 72 230 g74141 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g75637 : Good 75637 ∧ Cnt 75637 7451 :=
  step 74887 750 7384 67 232 g74887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g76387 : Good 76387 ∧ Cnt 76387 7515 :=
  step 75637 750 7451 64 235 g75637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g77137 : Good 77137 ∧ Cnt 77137 7577 :=
  step 76387 750 7515 62 237 g76387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g77887 : Good 77887 ∧ Cnt 77887 7653 :=
  step 77137 750 7577 76 239 g77137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g78637 : Good 78637 ∧ Cnt 78637 7715 :=
  step 77887 750 7653 62 242 g77887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g79387 : Good 79387 ∧ Cnt 79387 7779 :=
  step 78637 750 7715 64 244 g78637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g80137 : Good 80137 ∧ Cnt 80137 7844 :=
  step 79387 750 7779 65 247 g79387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g80887 : Good 80887 ∧ Cnt 80887 7915 :=
  step 80137 750 7844 71 249 g80137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g81637 : Good 81637 ∧ Cnt 81637 7983 :=
  step 80887 750 7915 68 251 g80887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g82387 : Good 82387 ∧ Cnt 82387 8054 :=
  step 81637 750 7983 71 254 g81637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g83137 : Good 83137 ∧ Cnt 83137 8118 :=
  step 82387 750 8054 64 256 g82387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g83887 : Good 83887 ∧ Cnt 83887 8181 :=
  step 83137 750 8118 63 258 g83137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g84637 : Good 84637 ∧ Cnt 84637 8247 :=
  step 83887 750 8181 66 260 g83887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g85387 : Good 85387 ∧ Cnt 85387 8312 :=
  step 84637 750 8247 65 263 g84637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g86137 : Good 86137 ∧ Cnt 86137 8373 :=
  step 85387 750 8312 61 265 g85387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g86887 : Good 86887 ∧ Cnt 86887 8441 :=
  step 86137 750 8373 68 267 g86137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g87637 : Good 87637 ∧ Cnt 87637 8509 :=
  step 86887 750 8441 68 269 g86887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g88387 : Good 88387 ∧ Cnt 88387 8568 :=
  step 87637 750 8509 59 271 g87637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g89137 : Good 89137 ∧ Cnt 89137 8635 :=
  step 88387 750 8568 67 273 g88387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g89887 : Good 89887 ∧ Cnt 89887 8701 :=
  step 89137 750 8635 66 275 g89137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g90637 : Good 90637 ∧ Cnt 90637 8772 :=
  step 89887 750 8701 71 277 g89887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g91387 : Good 91387 ∧ Cnt 91387 8836 :=
  step 90637 750 8772 64 280 g90637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g92137 : Good 92137 ∧ Cnt 92137 8897 :=
  step 91387 750 8836 61 282 g91387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g92887 : Good 92887 ∧ Cnt 92887 8974 :=
  step 92137 750 8897 77 284 g92137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g93637 : Good 93637 ∧ Cnt 93637 9041 :=
  step 92887 750 8974 67 286 g92887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g94387 : Good 94387 ∧ Cnt 94387 9102 :=
  step 93637 750 9041 61 288 g93637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g95137 : Good 95137 ∧ Cnt 95137 9171 :=
  step 94387 750 9102 69 290 g94387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g95887 : Good 95887 ∧ Cnt 95887 9241 :=
  step 95137 750 9171 70 292 g95137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g96637 : Good 96637 ∧ Cnt 96637 9303 :=
  step 95887 750 9241 62 294 g95887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g97387 : Good 97387 ∧ Cnt 97387 9366 :=
  step 96637 750 9303 63 295 g96637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g98137 : Good 98137 ∧ Cnt 98137 9428 :=
  step 97387 750 9366 62 297 g97387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g98887 : Good 98887 ∧ Cnt 98887 9490 :=
  step 98137 750 9428 62 299 g98137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g99637 : Good 99637 ∧ Cnt 99637 9559 :=
  step 98887 750 9490 69 301 g98887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g100387 : Good 100387 ∧ Cnt 100387 9622 :=
  step 99637 750 9559 63 303 g99637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g101137 : Good 101137 ∧ Cnt 101137 9685 :=
  step 100387 750 9622 63 305 g100387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g101887 : Good 101887 ∧ Cnt 101887 9756 :=
  step 101137 750 9685 71 307 g101137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g102637 : Good 102637 ∧ Cnt 102637 9826 :=
  step 101887 750 9756 70 309 g101887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g103387 : Good 103387 ∧ Cnt 103387 9879 :=
  step 102637 750 9826 53 310 g102637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g104137 : Good 104137 ∧ Cnt 104137 9946 :=
  step 103387 750 9879 67 312 g103387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g104887 : Good 104887 ∧ Cnt 104887 10014 :=
  step 104137 750 9946 68 314 g104137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g105637 : Good 105637 ∧ Cnt 105637 10077 :=
  step 104887 750 10014 63 316 g104887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g106387 : Good 106387 ∧ Cnt 106387 10141 :=
  step 105637 750 10077 64 318 g105637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g107137 : Good 107137 ∧ Cnt 107137 10210 :=
  step 106387 750 10141 69 319 g106387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g107887 : Good 107887 ∧ Cnt 107887 10265 :=
  step 107137 750 10210 55 321 g107137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g108637 : Good 108637 ∧ Cnt 108637 10329 :=
  step 107887 750 10265 64 323 g107887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g109387 : Good 109387 ∧ Cnt 109387 10398 :=
  step 108637 750 10329 69 325 g108637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g110137 : Good 110137 ∧ Cnt 110137 10463 :=
  step 109387 750 10398 65 326 g109387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g110887 : Good 110887 ∧ Cnt 110887 10523 :=
  step 110137 750 10463 60 328 g110137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g111637 : Good 111637 ∧ Cnt 111637 10586 :=
  step 110887 750 10523 63 330 g110887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g112387 : Good 112387 ∧ Cnt 112387 10657 :=
  step 111637 750 10586 71 331 g111637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g113137 : Good 113137 ∧ Cnt 113137 10718 :=
  step 112387 750 10657 61 333 g112387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g113887 : Good 113887 ∧ Cnt 113887 10777 :=
  step 113137 750 10718 59 335 g113137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g114637 : Good 114637 ∧ Cnt 114637 10839 :=
  step 113887 750 10777 62 336 g113887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g115387 : Good 115387 ∧ Cnt 115387 10906 :=
  step 114637 750 10839 67 338 g114637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g116137 : Good 116137 ∧ Cnt 116137 10974 :=
  step 115387 750 10906 68 340 g115387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g116887 : Good 116887 ∧ Cnt 116887 11033 :=
  step 116137 750 10974 59 341 g116137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g117637 : Good 117637 ∧ Cnt 117637 11097 :=
  step 116887 750 11033 64 343 g116887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g118387 : Good 118387 ∧ Cnt 118387 11163 :=
  step 117637 750 11097 66 344 g117637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g119137 : Good 119137 ∧ Cnt 119137 11228 :=
  step 118387 750 11163 65 346 g118387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g119887 : Good 119887 ∧ Cnt 119887 11291 :=
  step 119137 750 11228 63 348 g119137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g120637 : Good 120637 ∧ Cnt 120637 11351 :=
  step 119887 750 11291 60 349 g119887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g121387 : Good 121387 ∧ Cnt 121387 11425 :=
  step 120637 750 11351 74 351 g120637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g122137 : Good 122137 ∧ Cnt 122137 11489 :=
  step 121387 750 11425 64 352 g121387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g122887 : Good 122887 ∧ Cnt 122887 11554 :=
  step 122137 750 11489 65 354 g122137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g123637 : Good 123637 ∧ Cnt 123637 11618 :=
  step 122887 750 11554 64 355 g122887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g124387 : Good 124387 ∧ Cnt 124387 11684 :=
  step 123637 750 11618 66 357 g123637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g125137 : Good 125137 ∧ Cnt 125137 11746 :=
  step 124387 750 11684 62 358 g124387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g125887 : Good 125887 ∧ Cnt 125887 11808 :=
  step 125137 750 11746 62 360 g125137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g126637 : Good 126637 ∧ Cnt 126637 11874 :=
  step 125887 750 11808 66 361 g125887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g127387 : Good 127387 ∧ Cnt 127387 11932 :=
  step 126637 750 11874 58 363 g126637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g128137 : Good 128137 ∧ Cnt 128137 11995 :=
  step 127387 750 11932 63 364 g127387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g128887 : Good 128887 ∧ Cnt 128887 12064 :=
  step 128137 750 11995 69 366 g128137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g129637 : Good 129637 ∧ Cnt 129637 12134 :=
  step 128887 750 12064 70 367 g128887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g130387 : Good 130387 ∧ Cnt 130387 12194 :=
  step 129637 750 12134 60 369 g129637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g131137 : Good 131137 ∧ Cnt 131137 12255 :=
  step 130387 750 12194 61 370 g130387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g131887 : Good 131887 ∧ Cnt 131887 12316 :=
  step 131137 750 12255 61 371 g131137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g132637 : Good 132637 ∧ Cnt 132637 12380 :=
  step 131887 750 12316 64 373 g131887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g133387 : Good 133387 ∧ Cnt 133387 12448 :=
  step 132637 750 12380 68 374 g132637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g134137 : Good 134137 ∧ Cnt 134137 12507 :=
  step 133387 750 12448 59 376 g133387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g134887 : Good 134887 ∧ Cnt 134887 12567 :=
  step 134137 750 12507 60 377 g134137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g135637 : Good 135637 ∧ Cnt 135637 12636 :=
  step 134887 750 12567 69 378 g134887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g136387 : Good 136387 ∧ Cnt 136387 12700 :=
  step 135637 750 12636 64 380 g135637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g137137 : Good 137137 ∧ Cnt 137137 12768 :=
  step 136387 750 12700 68 381 g136387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g137887 : Good 137887 ∧ Cnt 137887 12831 :=
  step 137137 750 12768 63 383 g137137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g138637 : Good 138637 ∧ Cnt 138637 12898 :=
  step 137887 750 12831 67 384 g137887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g139387 : Good 139387 ∧ Cnt 139387 12955 :=
  step 138637 750 12898 57 385 g138637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g140137 : Good 140137 ∧ Cnt 140137 13017 :=
  step 139387 750 12955 62 387 g139387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g140887 : Good 140887 ∧ Cnt 140887 13088 :=
  step 140137 750 13017 71 388 g140137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g141637 : Good 141637 ∧ Cnt 141637 13149 :=
  step 140887 750 13088 61 389 g140887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g142387 : Good 142387 ∧ Cnt 142387 13215 :=
  step 141637 750 13149 66 391 g141637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g143137 : Good 143137 ∧ Cnt 143137 13272 :=
  step 142387 750 13215 57 392 g142387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g143887 : Good 143887 ∧ Cnt 143887 13336 :=
  step 143137 750 13272 64 393 g143137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g144637 : Good 144637 ∧ Cnt 144637 13393 :=
  step 143887 750 13336 57 395 g143887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g145387 : Good 145387 ∧ Cnt 145387 13450 :=
  step 144637 750 13393 57 396 g144637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g146137 : Good 146137 ∧ Cnt 146137 13520 :=
  step 145387 750 13450 70 397 g145387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g146887 : Good 146887 ∧ Cnt 146887 13580 :=
  step 146137 750 13520 60 398 g146137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g147637 : Good 147637 ∧ Cnt 147637 13646 :=
  step 146887 750 13580 66 400 g146887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g148387 : Good 148387 ∧ Cnt 148387 13703 :=
  step 147637 750 13646 57 401 g147637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g149137 : Good 149137 ∧ Cnt 149137 13772 :=
  step 148387 750 13703 69 402 g148387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g149887 : Good 149887 ∧ Cnt 149887 13838 :=
  step 149137 750 13772 66 403 g149137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g150637 : Good 150637 ∧ Cnt 150637 13904 :=
  step 149887 750 13838 66 405 g149887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g151387 : Good 151387 ∧ Cnt 151387 13966 :=
  step 150637 750 13904 62 406 g150637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g152137 : Good 152137 ∧ Cnt 152137 14036 :=
  step 151387 750 13966 70 407 g151387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g152887 : Good 152887 ∧ Cnt 152887 14100 :=
  step 152137 750 14036 64 408 g152137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g153637 : Good 153637 ∧ Cnt 153637 14162 :=
  step 152887 750 14100 62 410 g152887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g154387 : Good 154387 ∧ Cnt 154387 14223 :=
  step 153637 750 14162 61 411 g153637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g155137 : Good 155137 ∧ Cnt 155137 14282 :=
  step 154387 750 14223 59 412 g154387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g155887 : Good 155887 ∧ Cnt 155887 14353 :=
  step 155137 750 14282 71 413 g155137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g156637 : Good 156637 ∧ Cnt 156637 14404 :=
  step 155887 750 14353 51 415 g155887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g157387 : Good 157387 ∧ Cnt 157387 14473 :=
  step 156637 750 14404 69 416 g156637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g158137 : Good 158137 ∧ Cnt 158137 14530 :=
  step 157387 750 14473 57 417 g157387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g158887 : Good 158887 ∧ Cnt 158887 14591 :=
  step 158137 750 14530 61 418 g158137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g159637 : Good 159637 ∧ Cnt 159637 14652 :=
  step 158887 750 14591 61 419 g158887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g160387 : Good 160387 ∧ Cnt 160387 14714 :=
  step 159637 750 14652 62 420 g159637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g161137 : Good 161137 ∧ Cnt 161137 14779 :=
  step 160387 750 14714 65 422 g160387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g161887 : Good 161887 ∧ Cnt 161887 14842 :=
  step 161137 750 14779 63 423 g161137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g162637 : Good 162637 ∧ Cnt 162637 14898 :=
  step 161887 750 14842 56 424 g161887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g163387 : Good 163387 ∧ Cnt 163387 14963 :=
  step 162637 750 14898 65 425 g162637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g164137 : Good 164137 ∧ Cnt 164137 15026 :=
  step 163387 750 14963 63 426 g163387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g164887 : Good 164887 ∧ Cnt 164887 15087 :=
  step 164137 750 15026 61 427 g164137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g165637 : Good 165637 ∧ Cnt 165637 15146 :=
  step 164887 750 15087 59 429 g164887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g166387 : Good 166387 ∧ Cnt 166387 15202 :=
  step 165637 750 15146 56 430 g165637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g167137 : Good 167137 ∧ Cnt 167137 15271 :=
  step 166387 750 15202 69 431 g166387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g167887 : Good 167887 ∧ Cnt 167887 15329 :=
  step 167137 750 15271 58 432 g167137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g168637 : Good 168637 ∧ Cnt 168637 15385 :=
  step 167887 750 15329 56 433 g167887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g169387 : Good 169387 ∧ Cnt 169387 15445 :=
  step 168637 750 15385 60 434 g168637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g170137 : Good 170137 ∧ Cnt 170137 15508 :=
  step 169387 750 15445 63 435 g169387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g170887 : Good 170887 ∧ Cnt 170887 15577 :=
  step 170137 750 15508 69 436 g170137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g171637 : Good 171637 ∧ Cnt 171637 15633 :=
  step 170887 750 15577 56 437 g170887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g172387 : Good 172387 ∧ Cnt 172387 15700 :=
  step 171637 750 15633 67 439 g171637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g173137 : Good 173137 ∧ Cnt 173137 15762 :=
  step 172387 750 15700 62 440 g172387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g173887 : Good 173887 ∧ Cnt 173887 15823 :=
  step 173137 750 15762 61 441 g173137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g174637 : Good 174637 ∧ Cnt 174637 15886 :=
  step 173887 750 15823 63 442 g173887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g175387 : Good 175387 ∧ Cnt 175387 15939 :=
  step 174637 750 15886 53 443 g174637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g176137 : Good 176137 ∧ Cnt 176137 16004 :=
  step 175387 750 15939 65 444 g175387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g176887 : Good 176887 ∧ Cnt 176887 16075 :=
  step 176137 750 16004 71 445 g176137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g177637 : Good 177637 ∧ Cnt 177637 16131 :=
  step 176887 750 16075 56 446 g176887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g178387 : Good 178387 ∧ Cnt 178387 16190 :=
  step 177637 750 16131 59 447 g177637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g179137 : Good 179137 ∧ Cnt 179137 16260 :=
  step 178387 750 16190 70 448 g178387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g179887 : Good 179887 ∧ Cnt 179887 16327 :=
  step 179137 750 16260 67 449 g179137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g180637 : Good 180637 ∧ Cnt 180637 16394 :=
  step 179887 750 16327 67 450 g179887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g181387 : Good 181387 ∧ Cnt 181387 16441 :=
  step 180637 750 16394 47 451 g180637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g182137 : Good 182137 ∧ Cnt 182137 16508 :=
  step 181387 750 16441 67 452 g181387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g182887 : Good 182887 ∧ Cnt 182887 16571 :=
  step 182137 750 16508 63 453 g182137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g183637 : Good 183637 ∧ Cnt 183637 16636 :=
  step 182887 750 16571 65 454 g182887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g184387 : Good 184387 ∧ Cnt 184387 16695 :=
  step 183637 750 16636 59 455 g183637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g185137 : Good 185137 ∧ Cnt 185137 16757 :=
  step 184387 750 16695 62 456 g184387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g185887 : Good 185887 ∧ Cnt 185887 16824 :=
  step 185137 750 16757 67 457 g185137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g186637 : Good 186637 ∧ Cnt 186637 16887 :=
  step 185887 750 16824 63 458 g185887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g187387 : Good 187387 ∧ Cnt 187387 16953 :=
  step 186637 750 16887 66 459 g186637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g188137 : Good 188137 ∧ Cnt 188137 17007 :=
  step 187387 750 16953 54 460 g187387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g188887 : Good 188887 ∧ Cnt 188887 17072 :=
  step 188137 750 17007 65 461 g188137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g189637 : Good 189637 ∧ Cnt 189637 17137 :=
  step 188887 750 17072 65 462 g188887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g190387 : Good 190387 ∧ Cnt 190387 17196 :=
  step 189637 750 17137 59 463 g189637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g191137 : Good 191137 ∧ Cnt 191137 17256 :=
  step 190387 750 17196 60 464 g190387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g191887 : Good 191887 ∧ Cnt 191887 17318 :=
  step 191137 750 17256 62 465 g191137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g192637 : Good 192637 ∧ Cnt 192637 17384 :=
  step 191887 750 17318 66 466 g191887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g193387 : Good 193387 ∧ Cnt 193387 17445 :=
  step 192637 750 17384 61 467 g192637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g194137 : Good 194137 ∧ Cnt 194137 17511 :=
  step 193387 750 17445 66 468 g193387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g194887 : Good 194887 ∧ Cnt 194887 17564 :=
  step 194137 750 17511 53 469 g194137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g195637 : Good 195637 ∧ Cnt 195637 17625 :=
  step 194887 750 17564 61 470 g194887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g196387 : Good 196387 ∧ Cnt 196387 17687 :=
  step 195637 750 17625 62 471 g195637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g197137 : Good 197137 ∧ Cnt 197137 17746 :=
  step 196387 750 17687 59 472 g196387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g197887 : Good 197887 ∧ Cnt 197887 17808 :=
  step 197137 750 17746 62 473 g197137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g198637 : Good 198637 ∧ Cnt 198637 17874 :=
  step 197887 750 17808 66 474 g197887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g199387 : Good 199387 ∧ Cnt 199387 17932 :=
  step 198637 750 17874 58 475 g198637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g200137 : Good 200137 ∧ Cnt 200137 17995 :=
  step 199387 750 17932 63 476 g199387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g200887 : Good 200887 ∧ Cnt 200887 18051 :=
  step 200137 750 17995 56 477 g200137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g201637 : Good 201637 ∧ Cnt 201637 18111 :=
  step 200887 750 18051 60 478 g200887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g202387 : Good 202387 ∧ Cnt 202387 18177 :=
  step 201637 750 18111 66 479 g201637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g203137 : Good 203137 ∧ Cnt 203137 18233 :=
  step 202387 750 18177 56 480 g202387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g203887 : Good 203887 ∧ Cnt 203887 18293 :=
  step 203137 750 18233 60 481 g203137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g204637 : Good 204637 ∧ Cnt 204637 18355 :=
  step 203887 750 18293 62 481 g203887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g205387 : Good 205387 ∧ Cnt 205387 18411 :=
  step 204637 750 18355 56 482 g204637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g206137 : Good 206137 ∧ Cnt 206137 18476 :=
  step 205387 750 18411 65 483 g205387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g206887 : Good 206887 ∧ Cnt 206887 18536 :=
  step 206137 750 18476 60 484 g206137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g207637 : Good 207637 ∧ Cnt 207637 18605 :=
  step 206887 750 18536 69 485 g206887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g208387 : Good 208387 ∧ Cnt 208387 18667 :=
  step 207637 750 18605 62 486 g207637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g209137 : Good 209137 ∧ Cnt 209137 18726 :=
  step 208387 750 18667 59 487 g208387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g209887 : Good 209887 ∧ Cnt 209887 18796 :=
  step 209137 750 18726 70 488 g209137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g210637 : Good 210637 ∧ Cnt 210637 18863 :=
  step 209887 750 18796 67 489 g209887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g211387 : Good 211387 ∧ Cnt 211387 18926 :=
  step 210637 750 18863 63 490 g210637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g212137 : Good 212137 ∧ Cnt 212137 18985 :=
  step 211387 750 18926 59 490 g211387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g212887 : Good 212887 ∧ Cnt 212887 19037 :=
  step 212137 750 18985 52 491 g212137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g213637 : Good 213637 ∧ Cnt 213637 19099 :=
  step 212887 750 19037 62 492 g212887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g214387 : Good 214387 ∧ Cnt 214387 19159 :=
  step 213637 750 19099 60 493 g213637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g215137 : Good 215137 ∧ Cnt 215137 19218 :=
  step 214387 750 19159 59 494 g214387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g215887 : Good 215887 ∧ Cnt 215887 19277 :=
  step 215137 750 19218 59 495 g215137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g216637 : Good 216637 ∧ Cnt 216637 19331 :=
  step 215887 750 19277 54 496 g215887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g217387 : Good 217387 ∧ Cnt 217387 19397 :=
  step 216637 750 19331 66 497 g216637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g218137 : Good 218137 ∧ Cnt 218137 19455 :=
  step 217387 750 19397 58 497 g217387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g218887 : Good 218887 ∧ Cnt 218887 19517 :=
  step 218137 750 19455 62 498 g218137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g219637 : Good 219637 ∧ Cnt 219637 19579 :=
  step 218887 750 19517 62 499 g218887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g220387 : Good 220387 ∧ Cnt 220387 19645 :=
  step 219637 750 19579 66 500 g219637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g221137 : Good 221137 ∧ Cnt 221137 19706 :=
  step 220387 750 19645 61 501 g220387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g221887 : Good 221887 ∧ Cnt 221887 19767 :=
  step 221137 750 19706 61 502 g221137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g222637 : Good 222637 ∧ Cnt 222637 19827 :=
  step 221887 750 19767 60 503 g221887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g223387 : Good 223387 ∧ Cnt 223387 19894 :=
  step 222637 750 19827 67 503 g222637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g224137 : Good 224137 ∧ Cnt 224137 19949 :=
  step 223387 750 19894 55 504 g223387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g224887 : Good 224887 ∧ Cnt 224887 20009 :=
  step 224137 750 19949 60 505 g224137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g225637 : Good 225637 ∧ Cnt 225637 20075 :=
  step 224887 750 20009 66 506 g224887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g226387 : Good 226387 ∧ Cnt 226387 20133 :=
  step 225637 750 20075 58 507 g225637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g227137 : Good 227137 ∧ Cnt 227137 20189 :=
  step 226387 750 20133 56 508 g226387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g227887 : Good 227887 ∧ Cnt 227887 20254 :=
  step 227137 750 20189 65 508 g227137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g228637 : Good 228637 ∧ Cnt 228637 20316 :=
  step 227887 750 20254 62 509 g227887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g229387 : Good 229387 ∧ Cnt 229387 20379 :=
  step 228637 750 20316 63 510 g228637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g230137 : Good 230137 ∧ Cnt 230137 20449 :=
  step 229387 750 20379 70 511 g229387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g230887 : Good 230887 ∧ Cnt 230887 20512 :=
  step 230137 750 20449 63 512 g230137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g231637 : Good 231637 ∧ Cnt 231637 20574 :=
  step 230887 750 20512 62 513 g230887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g232387 : Good 232387 ∧ Cnt 232387 20626 :=
  step 231637 750 20574 52 513 g231637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g233137 : Good 233137 ∧ Cnt 233137 20681 :=
  step 232387 750 20626 55 514 g232387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g233887 : Good 233887 ∧ Cnt 233887 20737 :=
  step 233137 750 20681 56 515 g233137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g234637 : Good 234637 ∧ Cnt 234637 20800 :=
  step 233887 750 20737 63 516 g233887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g235387 : Good 235387 ∧ Cnt 235387 20861 :=
  step 234637 750 20800 61 517 g234637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g236137 : Good 236137 ∧ Cnt 236137 20916 :=
  step 235387 750 20861 55 517 g235387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g236887 : Good 236887 ∧ Cnt 236887 20973 :=
  step 236137 750 20916 57 518 g236137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g237637 : Good 237637 ∧ Cnt 237637 21027 :=
  step 236887 750 20973 54 519 g236887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g238387 : Good 238387 ∧ Cnt 238387 21093 :=
  step 237637 750 21027 66 520 g237637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g239137 : Good 239137 ∧ Cnt 239137 21150 :=
  step 238387 750 21093 57 520 g238387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g239887 : Good 239887 ∧ Cnt 239887 21213 :=
  step 239137 750 21150 63 521 g239137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g240637 : Good 240637 ∧ Cnt 240637 21272 :=
  step 239887 750 21213 59 522 g239887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g241387 : Good 241387 ∧ Cnt 241387 21334 :=
  step 240637 750 21272 62 523 g240637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g242137 : Good 242137 ∧ Cnt 242137 21401 :=
  step 241387 750 21334 67 524 g241387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g242887 : Good 242887 ∧ Cnt 242887 21461 :=
  step 242137 750 21401 60 524 g242137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g243637 : Good 243637 ∧ Cnt 243637 21519 :=
  step 242887 750 21461 58 525 g242887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g244387 : Good 244387 ∧ Cnt 244387 21579 :=
  step 243637 750 21519 60 526 g243637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g245137 : Good 245137 ∧ Cnt 245137 21643 :=
  step 244387 750 21579 64 527 g244387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g245887 : Good 245887 ∧ Cnt 245887 21703 :=
  step 245137 750 21643 60 527 g245137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g246637 : Good 246637 ∧ Cnt 246637 21762 :=
  step 245887 750 21703 59 528 g245887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g247387 : Good 247387 ∧ Cnt 247387 21823 :=
  step 246637 750 21762 61 529 g246637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g248137 : Good 248137 ∧ Cnt 248137 21888 :=
  step 247387 750 21823 65 530 g247387 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g248887 : Good 248887 ∧ Cnt 248887 21956 :=
  step 248137 750 21888 68 531 g248137 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g249637 : Good 249637 ∧ Cnt 249637 22015 :=
  step 248887 750 21956 59 531 g248887 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private lemma g250000 : Good 250000 ∧ Cnt 250000 22044 :=
  step 249637 363 22015 29 532 g249637 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem finite_bound : Good 250000 := g250000.1

end OMA930b

open Finset
namespace CubicSmoothCover

def smooth (P B : ℕ) : Finset ℕ :=
  (Icc 1 B).filter (fun v => ∀ p ∈ v.primeFactors, p ≤ P)

def coprimeUpTo (M x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (M.Coprime ·)

private theorem coprime_primorial {P u : ℕ} :
    (primorial P).Coprime u ↔ ∀ q, q.Prime → q ∣ u → P < q := by
  constructor
  · intro h q hq hqu
    by_contra! hqP
    exact hq.ne_one (Nat.dvd_one.mp (h.gcd_eq_one ▸ Nat.dvd_gcd
      (hq.dvd_primorial_iff.mpr hqP) hqu))
  · intro h
    by_contra hn
    have hg : (primorial P).gcd u ≠ 1 := hn
    let q := ((primorial P).gcd u).minFac
    have hq := Nat.minFac_prime hg
    have hd : q ∣ (primorial P).gcd u := Nat.minFac_dvd _
    exact (not_lt_of_ge (hq.dvd_primorial_iff.mp (hd.trans (Nat.gcd_dvd_left _ _))))
      (h q hq (hd.trans (Nat.gcd_dvd_right _ _)))

private theorem greedy {P B : ℕ} (u v : ℕ) (hu : 0 < u) (hv : v ∈ smooth P B)
    (horder : ∀ q, q.Prime → q ∣ u → ∀ p ∈ v.primeFactors, p ≤ q) :
    ∃ a b : ℕ, 0 < a ∧ b ∈ smooth P B ∧ a * b = u * v ∧
      ((primorial P).Coprime a ∨
        ∃ p, p.Prime ∧ p ≤ P ∧ p ∣ a ∧ B < p * b ∧
          (∀ q, q.Prime → q ∣ a → p ≤ q) ∧ ∀ q ∈ b.primeFactors, q ≤ p) := by
  by_cases hcop : (primorial P).Coprime u
  · exact ⟨u, v, hu, hv, rfl, Or.inl hcop⟩
  have hun : u ≠ 1 := by
    intro he; exact hcop (he ▸ Nat.coprime_one_right _)
  let p := u.minFac
  have hp : p.Prime := Nat.minFac_prime hun
  have hpdvd : p ∣ u := Nat.minFac_dvd u
  have hpmin (q : ℕ) (hq : q.Prime) (hqu : q ∣ u) : p ≤ q :=
    Nat.minFac_le_of_dvd hq.two_le hqu
  have hpP : p ≤ P := by
    by_contra! hlt
    exact hcop (coprime_primorial.mpr
      (fun q hq hd => hlt.trans_le (hpmin q hq hd)))
  by_cases hnext : p * v ≤ B
  · have hvpos : 0 < v := by
      have := (mem_Icc.mp (mem_filter.mp hv).1).1
      omega
    have hdivide : u / p * p = u := Nat.div_mul_cancel hpdvd
    have hu' : 0 < u / p := by
      by_contra! hz
      rw [Nat.eq_zero_of_le_zero hz, zero_mul] at hdivide
      omega
    have hv' : p * v ∈ smooth P B := by
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.mul_pos hp.pos hvpos), hnext⟩, ?_⟩
      intro q hq
      rcases (Nat.mem_primeFactors.mp hq).1.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hq)
        with hd | hd
      · have he := (Nat.dvd_prime hp).mp hd
        rcases he with he | he
        · exact ((Nat.prime_of_mem_primeFactors hq).ne_one he).elim
        · simpa [he] using hpP
      · exact (mem_filter.mp hv).2 q ((Nat.prime_of_mem_primeFactors hq).mem_primeFactors
          hd hvpos.ne')
    have horder' (q : ℕ) (hq : q.Prime) (hqu : q ∣ u / p)
        (w : ℕ) (hw : w ∈ (p * v).primeFactors) : w ≤ q := by
      have hqu' : q ∣ u := hqu.trans (show u / p ∣ u by exact ⟨p, hdivide.symm⟩)
      rcases (Nat.prime_of_mem_primeFactors hw).dvd_mul.mp (Nat.dvd_of_mem_primeFactors hw)
        with hd | hd
      · rcases (Nat.dvd_prime hp).mp hd with he | he
        · exact ((Nat.prime_of_mem_primeFactors hw).ne_one he).elim
        · simpa [he] using hpmin q hq hqu'
      · exact horder q hq hqu' w ((Nat.prime_of_mem_primeFactors hw).mem_primeFactors
          hd hvpos.ne')
    obtain ⟨a, b, ha, hb, hab, ht⟩ := greedy (u / p) (p * v) hu' hv' horder'
    exact ⟨a, b, ha, hb, hab.trans (by rw [← mul_assoc, hdivide]), ht⟩
  · exact ⟨u, v, hu, hv, rfl, Or.inr
      ⟨p, hp, hpP, hpdvd, lt_of_not_ge hnext, hpmin, horder p hp hpdvd⟩⟩
termination_by u
decreasing_by exact Nat.div_lt_self hu hp.one_lt

def multiples (x p d : ℕ) : Finset ℕ :=
  (coprimeUpTo (primorial (p - 1)) (x / (p * d))).image (p * ·)

def remaining (P : ℕ) (d : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  coprimeUpTo (primorial P) x ∪ (Nat.primesLE P).biUnion (fun p => multiples x p (d p))

theorem remaining_pos {P : ℕ} {d : ℕ → ℕ} {x a : ℕ} (ha : a ∈ remaining P d x) :
    0 < a := by
  rcases mem_union.mp ha with hr | hr
  · have := (mem_Icc.mp (mem_filter.mp hr).1).1
    omega
  · obtain ⟨p, hp, hap⟩ := mem_biUnion.mp hr
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hap
    have hp' : p.Prime := Nat.prime_of_mem_primesLE hp
    have hw' := (mem_Icc.mp (mem_filter.mp hw).1).1
    exact Nat.mul_pos hp'.pos (by omega)

theorem smooth_pos {P B v : ℕ} (hv : v ∈ smooth P B) : 0 < v := by
  have := (mem_Icc.mp (mem_filter.mp hv).1).1
  omega

theorem factor {P B a x : ℕ} {d : ℕ → ℕ} (hB : 1 ≤ B) (ha : 0 < a) (hax : a ≤ x)
    (hd : ∀ p b, p.Prime → p ≤ P → b ∈ smooth P B → B < p * b →
      (∀ q ∈ b.primeFactors, q ≤ p) → d p ≤ b)
    (hdpos : ∀ p ∈ Nat.primesLE P, 0 < d p) :
    ∃ u ∈ remaining P d x, ∃ v ∈ smooth P B, u * v = a := by
  have h1 : 1 ∈ smooth P B := by simp [smooth, hB]
  obtain ⟨u, v, hu, hv, huv, hdone⟩ :=
    greedy a 1 ha h1 (by simp)
  rw [mul_one] at huv
  have hux : u ≤ x :=
    (Nat.le_mul_of_pos_right _ (smooth_pos hv)).trans (huv ▸ hax)
  refine ⟨u, ?_, v, hv, huv⟩
  rcases hdone with hcop | ⟨p, hp, hple, hpu, hbig, hmin, hsmall⟩
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hux⟩, hcop⟩)
  · have hpmem : p ∈ Nat.primesLE P := Nat.mem_primesLE.mpr ⟨hple, hp⟩
    have hdiv : u / p * p = u := Nat.div_mul_cancel hpu
    have hmul : u / p * (p * d p) ≤ x := by
      rw [← mul_assoc, hdiv]
      exact (Nat.mul_le_mul_left u (hd p v hp hple hv hbig hsmall)).trans (huv ▸ hax)
    have hun : 1 ≤ u / p := by
      by_contra! hz
      have he : u / p = 0 := Nat.lt_one_iff.mp hz
      rw [he, zero_mul] at hdiv
      omega
    refine mem_union_right _ (mem_biUnion.mpr ⟨p, hpmem, mem_image.mpr
      ⟨u / p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hun, ?_⟩, ?_⟩, ?_⟩⟩)
    · exact (Nat.le_div_iff_mul_le (Nat.mul_pos hp.pos (hdpos p hpmem))).mpr hmul
    · exact coprime_primorial.mpr (fun q hq hqdiv => by
        have := hmin q hq (hqdiv.trans (show u / p ∣ u by exact ⟨p, hdiv.symm⟩))
        exact lt_of_lt_of_le (Nat.sub_lt (hp.pos) (by decide)) this)
    · rwa [mul_comm]

end CubicSmoothCover

namespace CubicSmoothCover

private theorem coprimeUpTo_period (M x : ℕ) :
    (coprimeUpTo M (x + M)).card = (coprimeUpTo M x).card + M.totient := by
  let A := Icc 1 x
  let B := Ico (x + 1) (x + 1 + M)
  have hsplit : Icc 1 (x + M) = A ∪ B := by
    ext i
    simp only [A, B, mem_union, mem_Icc, mem_Ico]
    omega
  have hdis : Disjoint A B := by
    refine disjoint_left.mpr fun i hi hj => ?_
    have hi' := (mem_Icc.mp hi).2
    have hj' := (mem_Ico.mp hj).1
    omega
  unfold coprimeUpTo
  rw [hsplit, filter_union, card_union_of_disjoint (hdis.mono
    (filter_subset _ _) (filter_subset _ _))]
  exact congrArg _ (Nat.filter_coprime_Ico_eq_totient M (x + 1))

private def prefixCount (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => prefixCount M n + if M.Coprime (n + 1) then 1 else 0

private theorem card_coprimeUpTo (M x : ℕ) :
    (coprimeUpTo M x).card = prefixCount M x := by
  induction x with
  | zero => simp [coprimeUpTo, prefixCount]
  | succ x ih =>
    have hsplit : Icc 1 (x + 1) = insert (x + 1) (Icc 1 x) := by
      ext i
      simp only [mem_Icc, mem_insert]
      omega
    rw [coprimeUpTo, hsplit, filter_insert, prefixCount, ← ih]
    split
    · rw [card_insert_of_notMem]
      · rfl
      · simp [mem_filter, mem_Icc]
    · simp only [coprimeUpTo, add_zero]

private def scan (M φ D : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, t, c => decide (M * c ≤ φ * t + D)
  | n + 1, t, c => decide (M * c ≤ φ * t + D) &&
      scan M φ D n (t + 1) (c + if M.Coprime (t + 1) then 1 else 0)

private theorem scan_sound {M φ D n t : ℕ} (h : scan M φ D n t (prefixCount M t) = true)
    (r : ℕ) (ht : t ≤ r) (hr : r ≤ t + n) :
    M * prefixCount M r ≤ φ * r + D := by
  induction n generalizing t with
  | zero =>
    have he : r = t := by omega
    simpa [scan, he] using h
  | succ n ih =>
    simp only [scan, Bool.and_eq_true, decide_eq_true_eq, ← prefixCount.eq_2] at h
    by_cases he : r = t
    · simpa [he] using h.1
    · exact ih h.2 (by omega) (by omega)

private theorem card_le_of_scan {M D : ℕ} (hM : 0 < M)
    (h : scan M M.totient D (M - 1) 0 0 = true) (x : ℕ) :
    M * (coprimeUpTo M x).card ≤ M.totient * x + D := by
  have hmod : x % M ≤ M - 1 := by have := Nat.mod_lt x hM; omega
  have hpre : M * (coprimeUpTo M (x % M)).card ≤ M.totient * (x % M) + D := by
    rw [card_coprimeUpTo]
    exact scan_sound (t := 0) (n := M - 1) h _ (Nat.zero_le _) (by omega)
  suffices ∀ q : ℕ, M * (coprimeUpTo M (x % M + q * M)).card ≤
      M.totient * (x % M + q * M) + D by
    have H := this (x / M)
    rwa [mul_comm (x / M), Nat.mod_add_div] at H
  intro q
  induction q with
  | zero => simpa using hpre
  | succ q ih =>
    rw [Nat.succ_mul, ← add_assoc, coprimeUpTo_period, mul_add, mul_add, mul_comm M M.totient]
    omega

private theorem coprime_card_1 (x : ℕ) : (coprimeUpTo 1 x).card ≤ x := by
  simpa using card_le_of_scan (M := 1) (D := 0) (by decide) (by decide) x

private theorem coprime_card_2 (x : ℕ) : 2 * (coprimeUpTo 2 x).card ≤ x + 1 := by
  have hφ : Nat.totient 2 = 1 := by decide
  simpa [hφ] using card_le_of_scan (M := 2) (D := 1) (by decide) (by decide) x

private theorem coprime_card_6 (x : ℕ) : 6 * (coprimeUpTo 6 x).card ≤ 2*x + 4 := by
  have hφ : Nat.totient 6 = 2 := by decide
  simpa [hφ] using card_le_of_scan (M := 6) (D := 4) (by decide) (by decide) x

private theorem coprime_card_30 (x : ℕ) : 30 * (coprimeUpTo 30 x).card ≤ 8*x + 28 := by
  have hφ : Nat.totient 30 = 8 := by decide
  simpa [hφ] using card_le_of_scan (M := 30) (D := 28) (by decide) (by decide) x

set_option maxRecDepth 10000 in
private theorem coprime_card_210 (x : ℕ) : 210 * (coprimeUpTo 210 x).card ≤ 48*x + 318 := by
  have hφ : Nat.totient 210 = 48 := by decide
  simpa [hφ] using card_le_of_scan (M := 210) (D := 318) (by decide) (by rw [hφ]; decide) x

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
private theorem coprime_card_2310 (x : ℕ) :
    2310 * (coprimeUpTo 2310 x).card ≤ 480*x + 5820 := by
  have hφ : Nat.totient 2310 = 480 := by decide
  simpa [hφ] using card_le_of_scan (M := 2310) (D := 5820) (by decide) (by rw [hφ]; decide) x

end CubicSmoothCover

namespace CubicSmoothCover

def cutoff100 : ℕ → ℕ
  | 2 => 64
  | 3 => 36
  | 5 => 21
  | 7 => 15
  | 11 => 10
  | _ => 1

private theorem primes_11 : Nat.primesLE 11 = {2, 3, 5, 7, 11} := by decide

private def trialSmooth (P B : ℕ) : Finset ℕ :=
  (Icc 1 B).filter (fun v => ∀ p ∈ Nat.primesLE B, p ∣ v → p ≤ P)

private theorem trialSmooth_eq (P B : ℕ) : trialSmooth P B = smooth P B := by
  ext v
  simp only [trialSmooth, smooth, mem_filter]
  refine and_congr_right fun hv => ⟨?_, ?_⟩
  · intro h q hq
    exact h q (Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hq).trans
      (mem_Icc.mp hv).2, Nat.prime_of_mem_primeFactors hq⟩) (Nat.dvd_of_mem_primeFactors hq)
  · intro h q hq hdiv
    exact h q ((Nat.prime_of_mem_primesLE hq).mem_primeFactors hdiv
      (by have := (mem_Icc.mp hv).1; omega))


set_option maxRecDepth 12000 in
private theorem cutoff_100_valid {p b : ℕ} (hp : p.Prime) (hple : p ≤ 11)
    (hb : b ∈ smooth 11 100) (hbig : 100 < p * b) (hsm : ∀ q ∈ b.primeFactors, q ≤ p) :
    cutoff100 p ≤ b := by
  have hp' : p ∈ Nat.primesLE 11 := Nat.mem_primesLE.mpr ⟨hple, hp⟩
  rw [primes_11] at hp'
  simp only [mem_insert, mem_singleton] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl
  · have hcheck : ∀ t : Fin 13, 51 + t.val ∉ trialSmooth 2 100 := by decide
    by_contra! hs
    change b < 64 at hs
    have hb' : 51 ≤ b := by omega
    let t : Fin 13 := ⟨b - 51, by omega⟩
    have hmem : b ∈ smooth 2 100 := mem_filter.mpr ⟨(mem_filter.mp hb).1, hsm⟩
    rw [← trialSmooth_eq] at hmem
    exact hcheck t (by simpa [t, Nat.add_sub_of_le hb'] using hmem)
  · have hcheck : ∀ t : Fin 2, 34 + t.val ∉ trialSmooth 3 100 := by decide
    by_contra! hs
    change b < 36 at hs
    have hb' : 34 ≤ b := by omega
    let t : Fin 2 := ⟨b - 34, by omega⟩
    have hmem : b ∈ smooth 3 100 := mem_filter.mpr ⟨(mem_filter.mp hb).1, hsm⟩
    rw [← trialSmooth_eq] at hmem
    exact hcheck t (by simpa [t, Nat.add_sub_of_le hb'] using hmem)
  · change 21 ≤ b
    omega
  · change 15 ≤ b
    omega
  · change 10 ≤ b
    omega

theorem factor100 {a x : ℕ} (ha : 0 < a) (hax : a ≤ x) :
    ∃ u ∈ remaining 11 cutoff100 x, ∃ v ∈ smooth 11 100, u * v = a := by
  apply factor (by decide) ha hax
  · intro p b hp hple hb hbig hsm
    exact cutoff_100_valid hp hple hb hbig hsm
  · intro p hp
    rw [primes_11] at hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem multiples_card (x p d : ℕ) (hp : 0 < p) :
    (multiples x p d).card = (coprimeUpTo (primorial (p - 1)) (x / (p * d))).card := by
  apply card_image_of_injective
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left hp hab

private theorem aggregate_100 (x : ℕ) :
    (remaining 11 cutoff100 x).card ≤ (coprimeUpTo 2310 x).card +
      ((coprimeUpTo 1 (x / 128)).card + (coprimeUpTo 2 (x / 108)).card +
      (coprimeUpTo 6 (x / 105)).card + (coprimeUpTo 30 (x / 105)).card +
      (coprimeUpTo 210 (x / 110)).card) := by
  have hprim : primorial 11 = 2310 := by decide
  have h₂ : primorial (2 - 1) = 1 := by decide
  have h₃ : primorial (3 - 1) = 2 := by decide
  have h₅ : primorial (5 - 1) = 6 := by decide
  have h₇ : primorial (7 - 1) = 30 := by decide
  have h₁₁ : primorial (11 - 1) = 210 := by decide
  have hm (p : ℕ) (hp : 0 < p) := multiples_card x p (cutoff100 p) hp
  have h := (card_union_le (s := coprimeUpTo (primorial 11) x)
    ((Nat.primesLE 11).biUnion (fun p => multiples x p (cutoff100 p)))).trans
    (Nat.add_le_add_left (card_biUnion_le) _)
  rw [primes_11] at h
  have hf : ((remaining 11 cutoff100 x).card) ≤
      (coprimeUpTo (primorial 11) x).card +
        ∑ p ∈ ({2, 3, 5, 7, 11} : Finset ℕ), (multiples x p (cutoff100 p)).card := by
    simpa only [remaining, primes_11] using h
  rw [hprim] at hf
  simp only [sum_insert (by decide : 2 ∉ ({3, 5, 7, 11} : Finset ℕ)),
    sum_insert (by decide : 3 ∉ ({5, 7, 11} : Finset ℕ)),
    sum_insert (by decide : 5 ∉ ({7, 11} : Finset ℕ)),
    sum_insert (by decide : 7 ∉ ({11} : Finset ℕ)), sum_singleton] at hf
  rw [hm 2 (by decide), hm 3 (by decide), hm 5 (by decide),
    hm 7 (by decide), hm 11 (by decide), h₂, h₃, h₅, h₇, h₁₁] at hf
  simp only [cutoff100] at hf
  norm_num1 at hf
  omega

theorem remaining_100_card (x : ℕ) :
    10000 * (remaining 11 cutoff100 x).card ≤ 2281 * x + 62000 := by
  have H := aggregate_100 x
  have h₁ := coprime_card_1 (x / 128)
  have h₂ := coprime_card_2 (x / 108)
  have h₆ := coprime_card_6 (x / 105)
  have h₃₀ := coprime_card_30 (x / 105)
  have h₂₁₀ := coprime_card_210 (x / 110)
  have h₂₃₁₀ := coprime_card_2310 x
  have hdiv₁ : 128 * (x / 128) ≤ x := by simpa [mul_comm] using Nat.div_mul_le_self x 128
  have hdiv₂ : 108 * (x / 108) ≤ x := by simpa [mul_comm] using Nat.div_mul_le_self x 108
  have hdiv₃ : 105 * (x / 105) ≤ x := by simpa [mul_comm] using Nat.div_mul_le_self x 105
  have hdiv₄ : 110 * (x / 110) ≤ x := by simpa [mul_comm] using Nat.div_mul_le_self x 110
  omega

end CubicSmoothCover

namespace CubicSmoothCover

def ratios (V : Finset ℕ) : Finset ℚ :=
  ((V ×ˢ V).filter (fun w => w.2 < w.1)).image (fun w => (w.1 : ℚ) / w.2)

/-- Bound the surplus over one factorization per first factor by distinct ratios in the
second factors, when products of two elements determine the unordered pair. -/
theorem pair_count_ratios (A U V : Finset ℕ)
    (hU : ∀ u ∈ U, 0 < u) (hV : ∀ v ∈ V, 0 < v)
    (hfactor : ∀ a ∈ A, ∃ u ∈ U, ∃ v ∈ V, u * v = a)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a * b = c * d → (a ::ₘ b ::ₘ (0 : Multiset ℕ)) = c ::ₘ d ::ₘ 0) :
    A.card ≤ U.card + (ratios V).card := by
  classical
  have hchoose (a : A) : ∃ u : ℕ, u ∈ U ∧ ∃ v ∈ V, u * v = a.val := hfactor a.val a.prop
  let first (a : A) : ℕ := (hchoose a).choose
  have hfirst (a : A) := (hchoose a).choose_spec
  let N (u : ℕ) := V.filter (fun v => ∃ h : u * v ∈ A, first ⟨u * v, h⟩ = u)
  have hmem {u v : ℕ} (hv : v ∈ N u) : u * v ∈ A := (mem_filter.mp hv).2.choose
  have hlabel {u v : ℕ} (hv : v ∈ N u) : first ⟨u * v, hmem hv⟩ = u :=
    (mem_filter.mp hv).2.choose_spec
  let base (u : ℕ) := if h : (N u).Nonempty then (N u).min' h else 0
  have hbase {u : ℕ} (h : (N u).Nonempty) : base u ∈ N u := by
    simpa [base, h] using (N u).min'_mem h
  have hb_le {u v : ℕ} (hv : v ∈ N u) : base u ≤ v := by
    have h : (N u).Nonempty := ⟨v, hv⟩
    simpa [base, h] using (N u).min'_le v hv
  let E := U.sigma (fun u => (N u).erase (base u))
  let quotient (p : Sigma (fun _ : ℕ => ℕ)) : ℚ := (p.2 : ℚ) / base p.1
  have hf (p : Sigma (fun _ : ℕ => ℕ)) (hp : p ∈ E) :
      p.1 ∈ U ∧ p.2 ∈ N p.1 ∧ base p.1 ∈ N p.1 ∧ base p.1 < p.2 := by
    have h := mem_sigma.mp hp
    have h' := mem_erase.mp h.2
    exact ⟨h.1, h'.2, hbase ⟨_, h'.2⟩, lt_of_le_of_ne (hb_le h'.2) (Ne.symm h'.1)⟩
  have hquot : Set.MapsTo quotient E (ratios V) := by
    intro p hp
    obtain ⟨_, hv, hb, hlt⟩ := hf p hp
    exact mem_image.mpr ⟨(p.2, base p.1), mem_filter.mpr
      ⟨mem_product.mpr ⟨(mem_filter.mp hv).1, (mem_filter.mp hb).1⟩, hlt⟩, rfl⟩
  have hinj : Set.InjOn quotient E := by
    rintro ⟨u, v⟩ hu ⟨w, z⟩ hw hq
    obtain ⟨hu, hv, hb, hlt⟩ := hf ⟨u,v⟩ hu
    obtain ⟨hw, hz, hc, hlt'⟩ := hf ⟨w,z⟩ hw
    change (v : ℚ) / (base u : ℚ) = (z : ℚ) / (base w : ℚ) at hq
    have hu0 : (base u : ℚ) ≠ 0 := by exact_mod_cast (hV _ (mem_filter.mp hb).1).ne'
    have hw0 : (base w : ℚ) ≠ 0 := by exact_mod_cast (hV _ (mem_filter.mp hc).1).ne'
    have hr : v * base w = z * base u := by exact_mod_cast (div_eq_div_iff hu0 hw0).mp hq
    have hprod : (u * v) * (w * base w) = (w * z) * (u * base u) := by
      rw [show u * v * (w * base w) = (u * w) * (v * base w) by ring, hr]
      ring
    have he := hpair _ (hmem hv) _ (hmem hc)
      _ (hmem hz) _ (hmem hb) hprod
    have hm : u * v ∈ w * z ::ₘ u * base u ::ₘ (0 : Multiset ℕ) :=
      he ▸ Multiset.mem_cons_self _ _
    have hval : u * v = w * z := by
      rcases (by simpa using hm : u * v = w * z ∨ u * v = u * base u) with h | h
      · exact h
      · exact (ne_of_gt (Nat.mul_lt_mul_of_pos_left hlt (hU u hu)) h).elim
    have hl : (⟨u * v, hmem hv⟩ : A) = ⟨w * z, hmem hz⟩ := Subtype.ext hval
    have huw : u = w := (hlabel hv).symm.trans ((congrArg first hl).trans (hlabel hz))
    subst w
    have heq : v = z := Nat.eq_of_mul_eq_mul_left (hU u hu) hval
    subst z
    rfl
  have heCard : E.card ≤ (ratios V).card := card_le_card_of_injOn quotient hquot hinj
  have hsum : (∑ u ∈ U, (N u).card) ≤ U.card + E.card := by
    rw [card_sigma]
    calc
      (∑ u ∈ U, (N u).card) ≤ ∑ u ∈ U, (1 + ((N u).erase (base u)).card) := by
        refine sum_le_sum fun u _ => ?_
        by_cases h : (N u).Nonempty
        · rw [card_erase_of_mem (hbase h)]
          have := card_pos.mpr h
          omega
        · simp [not_nonempty_iff_eq_empty.mp h]
      _ = _ := by rw [sum_add_distrib]; simp
  let f (p : Sigma (fun _ : ℕ => ℕ)) := p.1 * p.2
  have hsubset : A ⊆ (U.sigma N).image f := by
    intro a ha
    obtain ⟨hu, v, hv, hmul⟩ := hfirst ⟨a, ha⟩
    let u := first ⟨a, ha⟩
    have ha' : u * v ∈ A := hmul ▸ ha
    have hs : (⟨u * v, ha'⟩ : A) = ⟨a, ha⟩ := Subtype.ext hmul
    exact mem_image.mpr ⟨⟨u, v⟩, mem_sigma.mpr ⟨hu,
      mem_filter.mpr ⟨hv, ⟨ha', congrArg first hs⟩⟩⟩, hmul⟩
  exact ((card_le_card hsubset).trans card_image_le).trans
    (by rw [card_sigma]; exact hsum.trans (Nat.add_le_add_left heCard _))

end CubicSmoothCover

namespace CubicSmoothCover

private def reducedPairs (V : Finset ℕ) : Finset (ℕ × ℕ) :=
  (V ×ˢ V).filter (fun w => w.2 < w.1 ∧ w.1.Coprime w.2)

private theorem smooth_of_dvd {P B a b : ℕ} (hb : b ∈ smooth P B)
    (ha : 0 < a) (hdiv : a ∣ b) : a ∈ smooth P B := by
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨ha, (Nat.le_of_dvd (smooth_pos hb) hdiv).trans
    (mem_Icc.mp (mem_filter.mp hb).1).2⟩, ?_⟩
  intro p hp
  exact (mem_filter.mp hb).2 _ ((Nat.prime_of_mem_primeFactors hp).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hp).trans hdiv) (smooth_pos hb).ne')

private theorem ratios_le_reduced (P B : ℕ) :
    (ratios (smooth P B)).card ≤ (reducedPairs (smooth P B)).card := by
  refine (card_le_card (t := (reducedPairs (smooth P B)).image
    (fun z => (z.1 : ℚ) / z.2)) ?_).trans card_image_le
  intro q hq
  obtain ⟨⟨v, w⟩, h, rfl⟩ := mem_image.mp hq
  obtain ⟨hmem, hlt⟩ := mem_filter.mp h
  obtain ⟨hv, hw⟩ := mem_product.mp hmem
  let g := v.gcd w
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (smooth_pos hv)
  have hvg : (v / g) * g = v := Nat.div_mul_cancel (Nat.gcd_dvd_left v w)
  have hwg : (w / g) * g = w := Nat.div_mul_cancel (Nat.gcd_dvd_right v w)
  have ha : 0 < v / g := by
    by_contra! h0
    rw [Nat.eq_zero_of_le_zero h0, zero_mul] at hvg
    exact (smooth_pos hv).ne' hvg.symm
  have hb : 0 < w / g := by
    by_contra! h0
    rw [Nat.eq_zero_of_le_zero h0, zero_mul] at hwg
    exact (smooth_pos hw).ne' hwg.symm
  refine mem_image.mpr ⟨(v / g,w / g), mem_filter.mpr ⟨mem_product.mpr
    ⟨smooth_of_dvd hv ha ⟨g,hvg.symm⟩, smooth_of_dvd hw hb ⟨g,hwg.symm⟩⟩, ?_⟩, ?_⟩
  · refine ⟨?_, Nat.coprime_div_gcd_div_gcd hg⟩
    exact Nat.lt_of_mul_lt_mul_right (show (w/g)*g < (v/g)*g by rwa [hvg,hwg])
  · apply (div_eq_div_iff (by exact_mod_cast hb.ne') (by exact_mod_cast (smooth_pos hw).ne')).mpr
    exact_mod_cast (show (v/g)*w = v*(w/g) from calc
      (v/g)*w = (v/g)*((w/g)*g) := by rw [hwg]
      _ = ((v/g)*g)*(w/g) := by ac_rfl
      _ = _ := by rw [hvg])

set_option maxRecDepth 40000 in
set_option maxHeartbeats 5000000 in
theorem ratios_100_card : (ratios (smooth 11 100)).card ≤ 513 := by
  apply (ratios_le_reduced 11 100).trans
  rw [← trialSmooth_eq]
  decide

end CubicSmoothCover

open Finset

namespace CubicPrimeCount

private theorem factorial_factorization_of_lt_sq {n p : ℕ} (hp : p.Prime)
    (hn : n < p ^ 2) : n.factorial.factorization p = n / p := by
  have hlog : Nat.log p n < 2 := Nat.log_lt_of_lt_pow' (by decide) hn
  rw [Nat.factorization_factorial hp hlog, show Ico 1 2 = {1} by decide, sum_singleton, pow_one]

private def multinomial42 (m : ℕ) : ℕ :=
  (42*m).choose (21*m) * (21*m).choose (14*m) * (7*m).choose (6*m)

private theorem multinomial42_pos (m : ℕ) : 0 < multinomial42 m :=
  mul_pos (mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
    (Nat.choose_pos (by omega))

private theorem prime_dvd_multinomial42 {m p : ℕ} (hm : 40 ≤ m)
    (hp : p.Prime) (hmp : m < p) (hpm : p ≤ 42*m) : p ∣ multinomial42 m := by
  have h1 : (42*m).choose (21*m) * (21*m).factorial * (21*m).factorial =
      (42*m).factorial := by
    simpa only [show 42*m-21*m = 21*m by omega] using
      (Nat.choose_mul_factorial_mul_factorial (n := 42*m) (k := 21*m) (by omega))
  have h2 : (21*m).choose (14*m) * (14*m).factorial * (7*m).factorial =
      (21*m).factorial := by
    simpa only [show 21*m-14*m = 7*m by omega] using
      (Nat.choose_mul_factorial_mul_factorial (n := 21*m) (k := 14*m) (by omega))
  have h3 : (7*m).choose (6*m) * (6*m).factorial * m.factorial = (7*m).factorial := by
    simpa only [show 7*m-6*m = m by omega] using
      (Nat.choose_mul_factorial_mul_factorial (n := 7*m) (k := 6*m) (by omega))
  have hM : multinomial42 m * (21*m).factorial * (14*m).factorial * (6*m).factorial *
      m.factorial = (42*m).factorial := calc
    _ = (42*m).choose (21*m) * (21*m).factorial *
        ((21*m).choose (14*m) * (14*m).factorial *
          ((7*m).choose (6*m) * (6*m).factorial * m.factorial)) := by
      unfold multinomial42
      ac_rfl
    _ = _ := by rw [h3, h2, h1]
  have hp2 : 42*m < p^2 := by
    have h := Nat.pow_le_pow_left (show m+1 ≤ p by omega) 2
    have h' : 40 * m ≤ m * m := Nat.mul_le_mul_right m hm
    nlinarith only [h, h']
  have hfac := congrArg (fun n : ℕ => n.factorization p) hM
  have hM0 := (multinomial42_pos m).ne'
  rw [Nat.factorization_mul (by positivity : multinomial42 m * (21*m).factorial *
      (14*m).factorial * (6*m).factorial ≠ 0) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (by positivity : multinomial42 m * (21*m).factorial *
      (14*m).factorial ≠ 0) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (mul_ne_zero hM0 (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    Nat.factorization_mul hM0 (Nat.factorial_ne_zero _)] at hfac
  simp only [Finsupp.add_apply] at hfac
  rw [factorial_factorization_of_lt_sq hp hp2,
    factorial_factorization_of_lt_sq hp (show 21*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show 14*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show 6*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show m < p^2 by omega), Nat.div_eq_of_lt hmp] at hfac
  have hd (j a : ℕ) (hj : (42*m)/j = a) : (42*m)/p/j = a/p := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm p j, ← Nat.div_div_eq_div_mul, hj]
  rw [← hd 2 (21*m) (by omega), ← hd 3 (14*m) (by omega), ← hd 7 (6*m) (by omega)] at hfac
  have hLo : 1 ≤ (42*m)/p := (Nat.one_le_div_iff hp.pos).mpr hpm
  have hHi : (42*m)/p < 42 := (Nat.div_lt_iff_lt_mul hp.pos).mpr
    (Nat.mul_lt_mul_of_pos_left hmp (by decide))
  have hstrict : ∀ q : Fin 42, 0 < q.val → q.val/2 + q.val/3 + q.val/7 < q.val := by decide
  have hf : 0 < (multinomial42 m).factorization p := by
    have hi := hstrict ⟨(42*m)/p, hHi⟩ (by exact hLo)
    dsimp at hi
    omega
  exact Nat.dvd_of_mem_primeFactors (by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hf.ne' : p ∈ (multinomial42 m).primeFactors)

private theorem weighted_binomial (m a b : ℕ) (hb : b ≤ a) :
    (a*m).choose (b*m) * (b^b * (a-b)^(a-b))^m ≤ (a^a)^m := by
  have hm : b*m ≤ a*m := Nat.mul_le_mul_right m hb
  have hs := single_le_sum (s := range (a*m+1))
    (f := fun j => b^j * (a-b)^(a*m-j) * (a*m).choose j)
    (fun _ _ => Nat.zero_le _) (a := b*m) (mem_range.mpr (by omega))
  have hexpand : a^(a*m) = ∑ j ∈ range (a*m+1), b^j * (a-b)^(a*m-j) * (a*m).choose j := by
    simpa only [Nat.add_sub_of_le hb, Nat.cast_id] using (add_pow b (a-b) (a*m))
  rw [← hexpand] at hs
  rw [← Nat.sub_mul, pow_mul b b, pow_mul (a-b) (a-b), ← mul_pow, pow_mul a a] at hs
  simpa only [Nat.mul_comm] using hs

private theorem multinomial42_bound (m : ℕ) :
    multinomial42 m * ((21^42 * 14^14 * 7^7 * 6^6 : ℕ)^m) ≤
      ((42^42 * 21^21 * 7^7 : ℕ)^m) := by
  have h1 := weighted_binomial m 42 21 (by decide)
  have h2 := weighted_binomial m 21 14 (by decide)
  have h3 := weighted_binomial m 7 6 (by decide)
  simp only [show 42-21=21 by decide, show 21-14=7 by decide,
    show 7-6=1 by decide, one_pow, mul_one] at h1 h2 h3
  have h := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  rw [show (21^42 : ℕ) = 21^21 * 21^21 by rw [← pow_add]] 
  simp only [mul_pow] at h
  simp only [mul_pow, multinomial42]
  exact h.trans_eq' (by ring)

private theorem primorial_div (m : ℕ) (hm : 40 ≤ m) :
    primorial (42*m) ∣ primorial m * multinomial42 m := by
  rw [show 42*m = m+(41*m) by omega, primorial_add]
  apply Nat.mul_dvd_mul_left
  refine prod_primes_dvd _ (fun _ h => (mem_filter.mp h).2.prime) ?_
  intro p hp
  obtain ⟨hpI,hpP⟩ := mem_filter.mp hp
  obtain ⟨h₁,h₂⟩ := mem_Ico.mp hpI
  exact prime_dvd_multinomial42 hm hpP (by omega) (by omega)

set_option maxRecDepth 10000 in
private theorem primorial42
    (m : ℕ) (hm : 40 ≤ m) :
    primorial (42*m) * 100^(42*m) ≤ 305^(42*m) := by
  let den : ℕ := 21^42 * 14^14 * 7^7 * 6^6
  let num : ℕ := 42^42 * 21^21 * 7^7
  have hden : 0 < den := by dsimp [den]; positivity
  have h := Nat.le_of_dvd (mul_pos (primorial_pos _) (multinomial42_pos _))
    (primorial_div m hm)
  have hn : multinomial42 m * den^m ≤ num^m := multinomial42_bound m
  have hconst : 4*num*100^42 ≤ den*305^42 := by norm_num [num, den]
  apply Nat.le_of_mul_le_mul_left _ (pow_pos hden m)
  calc
    den^m * (primorial (42*m) * 100^(42*m)) ≤
        den^m * ((primorial m * multinomial42 m) * 100^(42*m)) := by gcongr
    _ = primorial m * (multinomial42 m * den^m) * (100^42)^m := by
      rw [pow_mul 100 42]
      ring
    _ ≤ (4^m * num^m) * (100^42)^m :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (primorial_le_four_pow _) hn)
    _ = (4*num*100^42)^m := by simp only [mul_pow]
    _ ≤ (den*305^42)^m := Nat.pow_le_pow_left hconst _
    _ = den^m * 305^(42*m) := by rw [mul_pow, pow_mul 305 42]

theorem theta_le
    {x : ℝ} (hx : 1680 ≤ x) :
    Chebyshev.theta x ≤ (9/8 : ℝ) * (x + 41) := by
  let n := ⌊x⌋₊
  let m := (n+41)/42
  have hn : 1680 ≤ n := by
    dsimp [n]
    apply (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr
    exact_mod_cast hx
  have hm : 40 ≤ m := by dsimp [m]; omega
  have hround : n ≤ 42*m := by dsimp [m]; omega
  have hround' : 42*m ≤ n+41 := by dsimp [m]; omega
  have hprim := primorial42 m hm
  have hcast : (primorial (42*m) : ℝ) * (100:ℝ)^(42*m) ≤ (305:ℝ)^(42*m) := by
    exact_mod_cast hprim
  have hr : (primorial (42*m) : ℝ) ≤ (305/100:ℝ)^(42*m) := by
    rw [div_pow]
    exact (le_div_iff₀ (by positivity)).mpr hcast
  have hlog : Real.log (305/100:ℝ) ≤ 9/8 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    exact (by norm_num [Finset.sum_range_succ, Nat.factorial] : (305/100:ℝ) ≤
      ∑ i ∈ range 6, (9/8:ℝ)^i / (i.factorial : ℝ)).trans
      (Real.sum_le_exp_of_nonneg (by norm_num) 6)
  have hprimpos : 0 < (primorial (42*m) : ℝ) := by exact_mod_cast primorial_pos (42*m)
  have hpos : 0 < (primorial n : ℝ) := by exact_mod_cast primorial_pos n
  have hnle : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  rw [Chebyshev.theta_eq_log_primorial]
  change Real.log (primorial n : ℝ) ≤ _
  calc
    _ ≤ Real.log (primorial (42*m) : ℝ) :=
      Real.log_le_log hpos (by exact_mod_cast primorial_mono hround)
    _ ≤ Real.log ((305/100 : ℝ)^(42*m)) := Real.log_le_log hprimpos hr
    _ = (42*m : ℕ) * Real.log (305/100:ℝ) := Real.log_pow _ _
    _ ≤ (42*m : ℕ) * (9/8 : ℝ) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ (9/8 : ℝ) * (x + 41) := by
      have h := (show (42*m : ℕ) ≤ n+41 from hround')
      have h' : ((42*m : ℕ) : ℝ) ≤ n+41 := by exact_mod_cast h
      linarith

end CubicPrimeCount

namespace CubicPrimeCount

open MeasureTheory

private theorem log2000_ge : (7:ℝ) ≤ Real.log 2000 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp 7 = Real.exp 1 ^ 7 := by
    convert Real.exp_nat_mul 1 7 using 2; norm_num
  rw [h]
  exact (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_d9.le.trans
    (by norm_num : (2.7182818286:ℝ) ≤ 11/4)) 7).trans (by norm_num)

theorem log250000_ge : (12:ℝ) ≤ Real.log 250000 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp 12 = Real.exp 1 ^ 12 := by
    convert Real.exp_nat_mul 1 12 using 2; norm_num
  rw [h]
  exact (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_d9.le.trans
    (by norm_num : (2.7182818286:ℝ) ≤ 11/4)) 12).trans (by norm_num)

private theorem log250000_le : Real.log 250000 ≤ (13:ℝ) := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : Real.exp 13 = Real.exp 1 ^ 13 := by
    convert Real.exp_nat_mul 1 13 using 2; norm_num
  rw [h]
  exact (by norm_num : (250000:ℝ) ≤ (8/3)^13).trans
    (pow_le_pow_left₀ (by norm_num) ((by norm_num : (8/3:ℝ) ≤ 2.7182818283).trans
      Real.exp_one_gt_d9.le) 13)

theorem log_div_le {x : ℝ} (hx : 250000 ≤ x) : Real.log x / x ≤ 13 / 250000 := by
  have h : 250000 ∈ Set.Ici (Real.exp 1) := by
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  exact (Real.log_div_self_antitoneOn h (h.trans hx) hx).trans
    (div_le_div_of_nonneg_right log250000_le (by norm_num))

private theorem integral_tail {x : ℝ} (hx : 2000 ≤ x) :
    (∫ t in (2000:ℝ)..x, 1 / Real.log t ^ 2) ≤ (7/5) * x / Real.log x ^ 2 := by
  let g (t : ℝ) := (7/5) * t / Real.log t ^ 2
  let d (t : ℝ) := (7/5) * ((Real.log t - 2) / Real.log t ^ 3)
  have hlog {t : ℝ} (ht : 2000 ≤ t) : 7 ≤ Real.log t :=
    log2000_ge.trans (Real.log_le_log (by norm_num) ht)
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc 2000 x) : HasDerivAt g (d t) t := by
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl : 0 < Real.log t := lt_of_lt_of_le (by norm_num) (hlog ht.1)
    have h := ((hasDerivAt_id t).const_mul (7/5:ℝ)).div
      ((Real.hasDerivAt_log ht0.ne').pow 2) (pow_ne_zero 2 hl.ne')
    convert h using 1
    all_goals first | rfl | (dsimp [d, g]; field_simp [ht0.ne', hl.ne'])
  have hdc : ContinuousOn d (Set.uIcc 2000 x) := by
    dsimp [d]
    refine continuousOn_const.mul ((Real.continuousOn_log.mono ?_).sub continuousOn_const
      |>.div ((Real.continuousOn_log.mono ?_).pow _) ?_)
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact fun h => by have he := Set.mem_singleton_iff.mp h; linarith [ht.1]
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact fun h => by have he := Set.mem_singleton_iff.mp h; linarith [ht.1]
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (by norm_num) (hlog ht.1)))
  have hInt : IntervalIntegrable d volume 2000 x := hdc.intervalIntegrable
  calc
    _ ≤ ∫ t in (2000:ℝ)..x, d t := by
      refine intervalIntegral.integral_mono_on hx
        (Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith))
        hInt (fun t ht => ?_)
      have hl := hlog ht.1
      have hl0 : 0 < Real.log t := by linarith
      dsimp [d]
      rw [show Real.log t ^ 3 = Real.log t ^ 2 * Real.log t by ring, ← mul_div_assoc,
        le_div_iff₀ (mul_pos (pow_pos hl0 _) hl0)]
      field_simp [hl0.ne']
      linarith
    _ = g x - g 2000 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
    _ ≤ _ := sub_le_self _ (by dsimp [g]; positivity)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1500000 in
private theorem prime_count_2000 : Nat.primeCounting 2000 ≤ 377 := by
  let R := (range 2001).filter ((510510:ℕ).Coprime ·)
  have hR : R.card ≤ 359 := by decide
  have hP : primorial 17 = 510510 := by decide
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hsub : (range 2001).filter Nat.Prime ⊆ range 18 ∪ R := by
    intro p hp
    obtain ⟨hpr, hprime⟩ := mem_filter.mp hp
    by_cases h : p < 18
    · exact mem_union_left _ (mem_range.mpr h)
    · have hcop : (primorial 17).Coprime p := by
        rw [Nat.coprime_comm, hprime.coprime_iff_not_dvd, hprime.dvd_primorial_iff]
        omega
      exact mem_union_right _ (mem_filter.mpr ⟨hpr, hP ▸ hcop⟩)
  exact (card_le_card hsub).trans ((card_union_le (range 18) R).trans (by simp only [card_range]; omega))

set_option maxHeartbeats 750000 in
theorem prime_count
    {k : ℕ} (hk : 250000 ≤ k) :
    (Nat.primeCounting k : ℝ) * Real.log (k : ℝ) ≤ (128/100:ℝ) * k := by
  let x : ℝ := k
  have hx : 250000 ≤ x := by dsimp [x]; exact_mod_cast hk
  have hx0 : 0 < x := by linarith
  have hx2 : (2000:ℝ) ≤ x := by linarith
  have hlog : 12 ≤ Real.log x := log250000_ge.trans (Real.log_le_log (by norm_num) hx)
  have hl0 : 0 < Real.log x := by linarith
  let f (t : ℝ) := Chebyshev.theta t / (t * Real.log t ^ 2)
  have hi (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable f volume a b := by
    refine intervalIntegrable_iff.mpr ?_
    rw [Set.uIoc_of_le hab, ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq b).mono_set (Set.Icc_subset_Icc_left ha)
  have hs := Chebyshev.primeCounting_eq_theta_div_log_add_integral (x := x) (by linarith)
  have hs' := Chebyshev.primeCounting_eq_theta_div_log_add_integral (x := (2000:ℝ)) (by norm_num)
  have hn : ⌊x⌋₊ = k := Nat.floor_natCast k
  have hn' : ⌊(2000:ℝ)⌋₊ = 2000 := Nat.floor_natCast 2000
  rw [hn, ← intervalIntegral.integral_add_adjacent_intervals
    (hi _ _ (by norm_num) (by norm_num : (2:ℝ) ≤ 2000)) (hi _ _ (by norm_num) hx2)] at hs
  rw [hn'] at hs'
  change (Nat.primeCounting k : ℝ) = _ + ((∫ t in 2..2000, f t) + ∫ t in 2000..x, f t) at hs
  change (Nat.primeCounting 2000 : ℝ) = _ + ∫ t in 2..2000, f t at hs'
  have hfirst : (∫ t in (2:ℝ)..2000, f t) ≤ 377 := by
    have hθ : 0 ≤ Chebyshev.theta 2000 / Real.log 2000 :=
      div_nonneg (Chebyshev.theta_nonneg _) (by linarith [log2000_ge])
    have hc : (Nat.primeCounting 2000 : ℝ) ≤ 377 := by exact_mod_cast prime_count_2000
    linarith
  have hsecond : (∫ t in (2000:ℝ)..x, f t) ≤ (23/20)*(7/5)*x/Real.log x^2 := by
    have hbound (t : ℝ) (ht : t ∈ Set.Icc 2000 x) :
        f t ≤ (23/20:ℝ) * (1 / Real.log t ^ 2) := by
      have ht0 : 0 < t := by linarith [ht.1]
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      have h := theta_le (show 1680 ≤ t by linarith [ht.1])
      dsimp [f]
      rw [div_le_iff₀ (mul_pos ht0 (pow_pos hlogt 2))]
      field_simp [hlogt.ne']
      linarith [ht.1]
    calc
      _ ≤ ∫ t in (2000:ℝ)..x, (23/20:ℝ)*(1 / Real.log t ^ 2) :=
        intervalIntegral.integral_mono_on hx2 (hi _ _ (by norm_num) hx2)
          ((Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)).const_mul _)
          hbound
      _ = (23/20:ℝ) * (∫ t in (2000:ℝ)..x, 1 / Real.log t ^ 2) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (integral_tail hx2) (show 0 ≤ (23/20:ℝ) by norm_num)
        simpa only [mul_div_assoc, mul_assoc] using h
  have hθ : Chebyshev.theta x ≤ (1126/1000:ℝ)*x := by
    have h := theta_le (show 1680 ≤ x by linarith)
    linarith
  have hp : (Nat.primeCounting k : ℝ) ≤ 377 + (1126/1000)*x/Real.log x +
      (23/20)*(7/5)*x/Real.log x^2 := by
    linarith [div_le_div_of_nonneg_right hθ hl0.le]
  have hd := mul_le_mul_of_nonneg_right hp hl0.le
  have hr : Real.log x ≤ (13/250000)*x := (div_le_iff₀ hx0).mp (log_div_le hx)
  have ht : x / Real.log x ≤ x / 12 := div_le_div_of_nonneg_left hx0.le (by norm_num) hlog
  have he : (377 + (1126/1000)*x/Real.log x + (23/20)*(7/5)*x/Real.log x^2) *
      Real.log x = 377 * Real.log x + (1126/1000)*x + (23/20)*(7/5)*(x/Real.log x) := by
    field_simp [hl0.ne']
  rw [he] at hd
  change (Nat.primeCounting k : ℝ) * Real.log x ≤ (128/100:ℝ) * x
  linarith

end CubicPrimeCount

namespace ErdosSelfridge

private theorem scaled_prod_ge_of_card_below_shift (A : Finset ℕ) (D a b : ℕ) 
    (hA : ∀ j ∈ A, 0 < j)
    (hcount : ∀ x, a * (A.filter (· ≤ x)).card ≤ b * x + a*D) :
    a ^ (A.card - D) * (A.card - D).factorial ≤ b ^ (A.card - D) * A.prod id := by
  classical
  let e := A.orderEmbOfFin rfl
  have ranked (i : Fin A.card) : a * (i.val + 1) ≤ b * e i + a*D := by
    let f : Fin (i.val + 1) ↪ ℕ :=
      ⟨fun j => e ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩,
        fun j z h => Fin.ext (congrArg (fun z : Fin A.card => z.val) (e.injective h))⟩
    have hsub : Finset.univ.map f ⊆ A.filter (· ≤ e i) := by
      intro a ha
      obtain ⟨j, _, rfl⟩ := mem_map.mp ha
      apply mem_filter.mpr
      exact ⟨A.orderEmbOfFin_mem rfl _, e.monotone (by
        change j.val ≤ i.val
        omega)⟩
    have h := card_le_card hsub
    simp only [card_map, card_univ, Fintype.card_fin] at h
    exact (Nat.mul_le_mul_left _ h).trans (hcount _)
  let m := A.card - D
  let g : Fin m ↪ ℕ :=
    ⟨fun j => e ⟨D + j.val, by have := j.isLt; dsimp [m] at this; omega⟩,
      fun j z h => Fin.ext (by
        have h' := congrArg Fin.val (e.injective h)
        change D + j.val = D + z.val at h'
        omega)⟩
  have hmono (i : Fin m) : a * (i.val + 1) ≤ b * g i := by
    have h := ranked ⟨D + i.val, by have := i.isLt; dsimp [m] at this; omega⟩
    change a * (D + i.val + 1) ≤ b * g i + a*D at h
    rw [show a * (D + i.val + 1) = a * D + a * (i.val + 1) by ring] at h
    omega
  have hA' : Finset.univ.map g ⊆ A := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := mem_map.mp ha
    exact A.orderEmbOfFin_mem rfl _
  have hmul : (∏ i : Fin m, a * (i.val + 1)) = a ^ m * m.factorial := by
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    congr 1
    rw [Fin.prod_univ_eq_prod_range (fun i => i + 1), prod_range_add_one_eq_factorial]
  change a ^ m * m.factorial ≤ b ^ m * A.prod id
  rw [← hmul]
  calc
    (∏ i : Fin m, a * (i.val + 1)) ≤ ∏ i : Fin m, b * g i :=
      prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hmono i)
    _ = b ^ m * (Finset.univ.map g).prod id := by
      rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_map]
      rfl
    _ ≤ _ := Nat.mul_le_mul_left _ (prod_le_prod_of_subset_of_one_le' hA' (fun _ hj _ => hA _ hj))
private theorem log_ratio_lower : (147/100:ℝ) ≤ Real.log (10000/2281) := by
  have h := Real.le_log_one_add_of_nonneg (x := (219/2281 : ℝ)) (by norm_num)
  rw [show (10000/2281:ℝ) = 2^2*(1 + 219/2281) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num at h ⊢
  linarith [Real.log_two_gt_d9]

private theorem explicit_factorial_ratio {k : ℕ} (hk : 250000 ≤ k) :
    let m := k - (Nat.primeCounting k + 520)
    2281^m * k.factorial < 10000^m * m.factorial := by
  let b := Nat.primeCounting k + 520
  let m := k - b
  change 2281^m * k.factorial < 10000^m * m.factorial
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkR : (250000 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog := CubicPrimeCount.log250000_ge.trans (Real.log_le_log (by norm_num) hkR)
  have hp := CubicPrimeCount.prime_count hk
  have hp' : (Nat.primeCounting k : ℝ) ≤ (128/1200:ℝ)*k := by
    have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (Nat.primeCounting k))
    linarith
  have hd : (520:ℝ) ≤ (520/250000:ℝ)*k := by linarith
  have hb : (b : ℝ) ≤ (128/1200 + 520/250000:ℝ)*k := by
    simp only [b, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hb_le : b ≤ k := by
    have hbR : (b : ℝ) ≤ k := by linarith
    exact_mod_cast hbR
  have hmR : (m : ℝ) = (k : ℝ) - b := Nat.cast_sub hb_le
  have hlogUpper := (div_le_iff₀ hk0).mp (CubicPrimeCount.log_div_le hkR)
  have hleft : (b : ℝ)*Real.log k ≤
      (128/100 + 520*13/250000:ℝ) * k := by
    simp only [b, Nat.cast_add, Nat.cast_ofNat, add_mul]
    linarith
  have hright : (147/100:ℝ)*((1-(128/1200+520/250000))*k) ≤
      (m:ℝ)*Real.log (10000/2281) := by
    have hmLower : ((1-(128/1200+520/250000):ℝ)*k) ≤ (m:ℝ) := by linarith
    refine (mul_le_mul_of_nonneg_left hmLower (by norm_num)).trans ?_
    rw [mul_comm (147/100:ℝ) (m:ℝ)]
    exact mul_le_mul_of_nonneg_left log_ratio_lower (Nat.cast_nonneg m)
  have hlogcmp : (b : ℝ) * Real.log k < (m : ℝ) * Real.log (10000/2281) := by
    linarith
  have hR : (k : ℝ)^b < (10000/2281:ℝ)^m := by
    apply (Real.log_lt_log_iff (pow_pos hk0 _) (pow_pos (by norm_num) _)).1
    simpa only [Real.log_pow] using hlogcmp
  rw [div_pow, lt_div_iff₀ (by positivity)] at hR
  have hpower : k^b * 2281^m < 10000^m := by exact_mod_cast hR
  have hfac : k.factorial ≤ m.factorial * k^b := by
    have h := Nat.ascFactorial_le_pow_add m b
    have he : m+b = k := Nat.sub_add_cancel hb_le
    rw [he] at h
    have he' := Nat.factorial_mul_ascFactorial m b
    rw [he] at he'
    exact he'.symm.le.trans (Nat.mul_le_mul_left _ h)
  calc
    _ ≤ 2281^m * (m.factorial*k^b) := Nat.mul_le_mul_left _ hfac
    _ = m.factorial * (k^b * 2281^m) := by ring
    _ < m.factorial * 10000^m := Nat.mul_lt_mul_of_pos_left hpower (Nat.factorial_pos _)
    _ = _ := mul_comm _ _

theorem large (k : ℕ) (a : Fin k → ℕ)
    (apos : ∀ i, 0 < a i)
    (sid : ∀ i j u v, i ≤ j → u ≤ v → a i*a j = a u*a v → i=u ∧ j=v)
    (T : Finset (Fin k)) (hT : k - k.primesBelow.card ≤ T.card) (hk : 250000 ≤ k) :
    (k-1).factorial < ∏ i ∈ T, a i := by
  classical
  have inj : Function.Injective a := fun i j he =>
    (sid i i j j le_rfl le_rfl (by rw [he])).1
  let A := T.image a
  have hA {v : ℕ} (hv : v ∈ A) : 0 < v := by
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    exact apos i
  have pairs (i j u v : Fin k) (he : a i * a j = a u * a v) :
      (a i ::ₘ a j ::ₘ (0 : Multiset ℕ)) = a u ::ₘ a v ::ₘ 0 := by
    rcases le_total i j with h|h <;> rcases le_total u v with g|g
    · obtain ⟨rfl,rfl⟩ := sid _ _ _ _ h g he
      rfl
    · obtain ⟨rfl,rfl⟩ := sid _ _ _ _ h g (he.trans (mul_comm ..))
      exact Multiset.cons_swap .. 
    · obtain ⟨rfl,rfl⟩ := sid _ _ _ _ h g ((mul_comm ..).trans he)
      exact Multiset.cons_swap ..
    · obtain ⟨rfl,rfl⟩ := sid _ _ _ _ h g ((mul_comm ..).trans (he.trans (mul_comm ..)))
      rfl
  have hcount (x : ℕ) : 10000 * (A.filter (· ≤ x)).card ≤ 2281*x + 10000*520 := by
    let U := CubicSmoothCover.remaining 11 CubicSmoothCover.cutoff100 x
    let V := CubicSmoothCover.smooth 11 100
    have hc := CubicSmoothCover.pair_count_ratios (A.filter (· ≤ x)) U V
      (fun _ => CubicSmoothCover.remaining_pos) (fun _ => CubicSmoothCover.smooth_pos)
      (fun _ ht => CubicSmoothCover.factor100 (hA (mem_filter.mp ht).1) (mem_filter.mp ht).2)
      (by
        intro b hb c hc d hd e he
        obtain ⟨i, _, rfl⟩ := mem_image.mp (mem_filter.mp hb).1
        obtain ⟨j, _, rfl⟩ := mem_image.mp (mem_filter.mp hc).1
        obtain ⟨u, _, rfl⟩ := mem_image.mp (mem_filter.mp hd).1
        obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_filter.mp he).1
        exact pairs i j u v)
    have hU : 10000 * U.card ≤ 2281*x + 62000 := CubicSmoothCover.remaining_100_card x
    have hV : (CubicSmoothCover.ratios V).card ≤ 513 := CubicSmoothCover.ratios_100_card
    omega
  have hlow := scaled_prod_ge_of_card_below_shift A 520 10000 2281 (fun _ => hA) hcount
  simp only [A, card_image_of_injective _ inj, prod_image inj.injOn, id_eq] at hlow
  have hcount' : k.primesBelow.card ≤ Nat.primeCounting k := by
    rw [Nat.primesBelow_card_eq_primeCounting']
    exact Nat.monotone_primeCounting' (Nat.le_succ _)
  let m := k - (Nat.primeCounting k + 520)
  let s := T.card - 520
  have hm : m ≤ s := by dsimp [m, s]; omega
  have hfac := explicit_factorial_ratio hk
  change 2281^m * k.factorial < 10000^m * m.factorial at hfac
  have hfac' : 2281^s * k.factorial < 10000^s * s.factorial := calc
    _ = 2281^(s-m) * (2281^m * k.factorial) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
    _ < 2281^(s-m) * (10000^m * m.factorial) :=
      Nat.mul_lt_mul_of_pos_left hfac (by positivity)
    _ ≤ 10000^(s-m) * (10000^m * s.factorial) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _) (Nat.mul_le_mul_left _ (Nat.factorial_le hm))
    _ = _ := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
  exact (Nat.factorial_le (Nat.sub_le k 1)).trans_lt
    (Nat.lt_of_mul_lt_mul_left (hfac'.trans_le hlow))

end ErdosSelfridge

end Erdos930Sidon

-- Credit: @MrSeizy
theorem OMA.solution : OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1.H4 := by
  intro k a hk apos sid T hT
  by_cases h : k < 250000
  · exact Erdos930Sidon.ShortRange930.bounded k a hk apos sid T hT
      (Erdos930Sidon.OMA930b.finite_bound k hk h)
  · exact Erdos930Sidon.ErdosSelfridge.large k a apos sid T hT (by omega)
