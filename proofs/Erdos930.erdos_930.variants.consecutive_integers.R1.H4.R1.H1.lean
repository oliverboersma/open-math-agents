import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1

/-! Erdős and Selfridge (1975), Section 2.1. For each integer take its largest divisor from the indicated finite smooth set. A prime dividing the complementary factor forces a lower bound on this divisor. The remaining cardinality estimates follow from explicit periodic counts. -/

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
    simp [prLeast2, Nat.add_mod]
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

theorem OMA.solution : OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1.H1 := by
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
