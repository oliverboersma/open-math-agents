import OMAStatements.S_oeis_a004044
import Mathlib

namespace OMA.R_oeis_a004044_R1

open OMA.S_oeis_a004044

/-- When no pair of centers is adjacent, all excess coverage is outside the code. -/
def H1 : Prop := ∀ m : ℕ, 0 < m → let n := (3^m+1)/2
    ∀ C : Finset (Fin n → Fin 3), IsCoveringCode n C →
    let e := fun x => (C.filter (fun c => hammingDist x c ≤ 1)).card - 1
    (∑ x ∈ C, e x) = 0 → 2*C.card ≤ ∑ x ∈ Cᶜ, e x

/-- When the centers themselves account for some but less than two excess
    covers per center, the other words must make up the shortfall. -/
def H2 : Prop := ∀ m : ℕ, 0 < m → let n := (3^m+1)/2
    ∀ C : Finset (Fin n → Fin 3), IsCoveringCode n C →
    let e := fun x => (C.filter (fun c => hammingDist x c ≤ 1)).card - 1
    let inside := ∑ x ∈ C, e x
    0 < inside → inside < 2*C.card → 2*C.card - inside ≤ ∑ x ∈ Cᶜ, e x

lemma length_bound (m : ℕ) : m ≤ (3^m+1)/2 := by
  have aux : ∀ k : ℕ, 2*k+1 ≤ 3^k := by
    intro k
    induction k with
    | zero => decide
    | succ k ih => rw [pow_succ]; omega
  have := aux m
  omega

lemma hamming_upper (m : ℕ) :
    let n := (3^m+1)/2
    ∃ C : Finset (Fin n → Fin 3), C.card ≤ 3^(n-m) ∧ IsCoveringCode n C := by
  classical
  let n := (3^m+1)/2
  let V := Fin m → ZMod 3
  let P := Projectivization (ZMod 3) V
  let _ : Fintype P := Fintype.ofFinite P
  have vc : Fintype.card V = 3^m := by simp [V,ZMod.card]
  have pc : 3^m = Fintype.card P * 2 + 1 := by
    simpa only [Nat.card_eq_fintype_card,vc,ZMod.card,Nat.reduceSub] using
      Projectivization.card' (ZMod 3) V
  let e : Fin n ≃ Option P := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin,Fintype.card_option]
    dsimp [n]
    omega)
  let col (i : Fin n) : V := (e i).elim 0 Projectivization.rep
  let syn (x : Fin n → ZMod 3) : V := ∑ i, x i • col i
  have rep (v : V) (hv : v ≠ 0) : ∃ i : Fin n, ∃ a : ZMod 3, a • col i = v := by
    let L : P := Projectivization.mk (ZMod 3) v hv
    obtain ⟨u,hu⟩ := Projectivization.exists_smul_eq_mk_rep (ZMod 3) v hv
    refine ⟨e.symm (some L), ↑u⁻¹, ?_⟩
    simp only [col, Equiv.apply_symm_apply, Option.elim_some]
    change u • v = L.rep at hu
    rw [← hu]
    exact inv_smul_smul u v
  have hmn : m ≤ n := length_bound m
  have count : Fintype.card (Fin n → ZMod 3) ≤ Fintype.card V * 3^(n-m) := by
    simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card,vc,←pow_add]
    rw [Nat.add_sub_of_le hmn]
  obtain ⟨b,hb⟩ := Fintype.exists_card_fiber_le_of_card_le_mul syn count
  let C := Finset.univ.filter (fun x => syn x = b)
  refine ⟨C,hb,?_⟩
  change ∀ x : Fin n → ZMod 3, ∃ y ∈ C, hammingDist x y ≤ 1
  intro x
  by_cases hx : syn x = b
  · exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,by simp⟩
  · obtain ⟨i,a,hi⟩ := rep (syn x-b) (sub_ne_zero.mpr hx)
    let delta : Fin n → ZMod 3 := Pi.single i a
    let y : Fin n → ZMod 3 := x-delta
    have hdel : syn delta = a • col i := by
      dsimp only [syn,delta]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    have hsyn : syn y = b := by
      change (∑ j, (x j - delta j) • col j) = b
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib]
      change syn x-syn delta=b
      rw [hdel, hi]
      abel
    refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsyn⟩, ?_⟩
    change (Finset.univ.filter (fun j => x j ≠ y j)).card ≤ 1
    calc
      _ ≤ ({i} : Finset (Fin n)).card := Finset.card_le_card (by
        intro j hj
        by_contra hn
        have hji : j ≠ i := by simpa using hn
        have he := (Finset.mem_filter.mp hj).2
        exact he (by simp [y,delta,Pi.single_eq_of_ne hji]))
      _ = 1 := Finset.card_singleton _


lemma ball_bound {n : ℕ} (c : Fin n → Fin 3) :
    (Finset.univ.filter (fun x => hammingDist x c ≤ 1)).card ≤ 1+2*n := by
  classical
  let sides (i : Fin n) := (Finset.univ.erase (c i)).image (Function.update c i)
  let near := Finset.univ.biUnion sides
  have incl : Finset.univ.filter (fun x => hammingDist x c ≤ 1) ⊆ insert c near := by
    intro x hx
    by_cases he : x=c
    · simp [he]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp he
    have hdist := (Finset.mem_filter.mp hx).2
    have hone := Finset.card_le_one.mp hdist
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨x i,by simp [hi],?_⟩⟩
    funext j
    by_cases hji : j=i
    · simp [hji]
    · rw [Function.update_of_ne hji]
      by_contra hd
      exact hji (hone j (by simp [Ne.symm hd]) i (by simp [hi]))
  have hlocal (i : Fin n) : (sides i).card ≤ 2 := by
    have h := Finset.card_image_le (f := Function.update c i) (s := Finset.univ.erase (c i))
    simpa [sides] using h
  have hnear : near.card ≤ 2*n := calc
    _ ≤ ∑ i : Fin n, (sides i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin n, (2 : ℕ) := Finset.sum_le_sum (fun i _ => hlocal i)
    _ = 2*n := by simp [mul_comm]
  have := (Finset.card_le_card incl).trans (Finset.card_insert_le c near)
  omega

lemma enough_excess {m n : ℕ} (hlen : 2*n=3^m+1) (hmn : m ≤ n)
    (C : Finset (Fin n → Fin 3)) (hc : IsCoveringCode n C)
    (hex : 2*C.card ≤ ∑ x : Fin n → Fin 3,
      ((C.filter (fun c => hammingDist x c ≤ 1)).card - 1)) : 3^(n-m) ≤ C.card := by
  classical
  let f (x : Fin n → Fin 3) := (C.filter (fun c => hammingDist x c ≤ 1)).card
  have hpos (x : Fin n → Fin 3) : 0 < f x := by
    obtain ⟨c,hc,hd⟩ := hc x
    exact Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨hc,hd⟩⟩
  have totals : (∑ x, f x) = (∑ x, (f x-1)) + 3^n := by
    calc
      _ = ∑ x, ((f x-1)+1) := Finset.sum_congr rfl (fun x _ => by have := hpos x; omega)
      _ = _ := by simp [Finset.sum_add_distrib]
  have bound : (∑ x, f x) ≤ C.card*(1+2*n) := calc
    _ = ∑ c ∈ C, (Finset.univ.filter (fun x => hammingDist x c ≤ 1)).card := by
      simp only [f, Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _c ∈ C, (1+2*n) := Finset.sum_le_sum (fun c _ => ball_bound c)
    _ = _ := by simp
  change 2*C.card ≤ ∑ x, (f x-1) at hex
  have bt : 3^n ≤ C.card*3^m := by
    rw [hlen] at bound
    nlinarith
  have hmul : 3^(n-m)*3^m ≤ C.card*3^m := by
    simpa only [← pow_add, Nat.sub_add_cancel hmn] using bt
  exact Nat.le_of_mul_le_mul_right hmul (by positivity)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a004044.main := by
  intro independent sparse m hm
  classical
  let n := (3^m+1)/2
  have hlen : 2*n=3^m+1 := by
    have hodd : Odd (3^m : ℕ) := Odd.pow (by decide : Odd (3:ℕ))
    obtain ⟨k,hk⟩ := hodd
    dsimp [n]
    omega
  have hmn : m ≤ n := length_bound m
  obtain ⟨B,hs,hb⟩ := hamming_upper m
  apply le_antisymm
  · exact (Nat.sInf_le (s := {j : ℕ | ∃ C : Finset (Fin n → Fin 3),
      C.card=j ∧ IsCoveringCode n C}) ⟨B,rfl,hb⟩).trans hs
  · apply le_csInf
    · exact ⟨B.card,B,rfl,hb⟩
    rintro _ ⟨C,rfl,hc⟩
    let e (x : Fin n → Fin 3) := (C.filter (fun c => hammingDist x c ≤ 1)).card-1
    let inside := ∑ x ∈ C, e x
    let outside := ∑ x ∈ Cᶜ, e x
    have split : inside + outside = ∑ x, e x := Finset.sum_add_sum_compl C e
    apply enough_excess hlen hmn C hc
    change 2*C.card ≤ ∑ x, e x
    rw [← split]
    by_cases hz : inside = 0
    · have h : 2*C.card ≤ outside := independent m hm C hc hz
      omega
    by_cases hd : inside < 2*C.card
    · have h : 2*C.card-inside ≤ outside := sparse m hm C hc (Nat.pos_of_ne_zero hz) hd
      omega
    · omega

end OMA.R_oeis_a004044_R1

