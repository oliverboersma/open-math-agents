import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1

/-! Mortenson, A Kronecker-type identity and the representations of a number
as a sum of three squares, (1.11) and (1.12). A reduced form of discriminant
minus s supplies three odd positive numbers b, 2a-b, 2c-b, congruent modulo
four. The two possible residues give the positive and negative cones of the
triangular-number identity. Credit: @marcusbuffett. -/

namespace OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H2_R1
open Finset
open scoped Classical

private lemma sqtri (x : ℕ) : (2*x+1)^2 = 8*(∑ j ∈ range x,(j+1))+1 := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [sum_range_succ]
    nlinarith only [ih]

private lemma residues {s a b c : ℕ} (hs : s%8=3) (h : 4*a*c=s+b^2) :
    a%2=1 ∧ c%2=1 ∧ (b%4=1 ∨ b%4=3) := by
  have btab : b^2%8=0 ∨ b^2%8=1 ∨ b^2%8=4 := by
    rw [Nat.pow_mod]
    have h8 := Nat.mod_lt b (by decide : 0 < 8)
    interval_cases b%8 <;> decide
  have b2 : b^2%8=1 := by
    have hh : 4*(a*c)=s+b^2 := by simpa [Nat.mul_assoc] using h
    omega
  have odd : b%4=1 ∨ b%4=3 := by
    rw [Nat.pow_mod] at b2
    have h8 := Nat.mod_lt b (by decide : 0 < 8)
    interval_cases hmod : b%8 <;> norm_num [hmod] at b2 <;> omega
  have pc : (a*c)%2=1 := by
    have hh : 4*(a*c)=s+b^2 := by simpa [Nat.mul_assoc] using h
    omega
  rw [Nat.mul_mod] at pc
  have h2a := Nat.mod_lt a (by decide : 0 < 2)
  have h2c := Nat.mod_lt c (by decide : 0 < 2)
  interval_cases a%2 <;> interval_cases c%2 <;> simp_all

private lemma into_cones (m : ℕ) {a b c : ℕ} (ba : b ≤ a) (ac : a ≤ c)
    (form : 4*a*c=8*m+3+b^2) :
    let x := b/4
    let y := (2*a-b)/4
    let z := (2*c-b)/4
    let o := if b%4=1 then 1 else 3
    a=2*(x+y)+o ∧ b=4*x+o ∧ c=2*(x+z)+o ∧
      (if b%4=1 then 2*(x*y+x*z+y*z)+x+y+z
       else 2*(x*y+x*z+y*z)+3*(x+y+z)+3)=m := by
  obtain ⟨oa,oc,ob⟩ := residues (by omega : (8*m+3)%8=3) form
  dsimp only
  split_ifs with h
  · have h1 : a=2*(b/4+(2*a-b)/4)+1 := by omega
    have h2 : b=4*(b/4)+1 := by omega
    have h3 : c=2*(b/4+(2*c-b)/4)+1 := by omega
    refine ⟨h1,h2,h3,?_⟩
    nlinarith only [show 4*(2*(b/4+(2*a-b)/4)+1)*(2*(b/4+(2*c-b)/4)+1) =
      8*m+3+(4*(b/4)+1)^2 by rwa [←h1,←h2,←h3]]
  · have h1 : a=2*(b/4+(2*a-b)/4)+3 := by omega
    have h2 : b=4*(b/4)+3 := by omega
    have h3 : c=2*(b/4+(2*c-b)/4)+3 := by omega
    refine ⟨h1,h2,h3,?_⟩
    nlinarith only [show 4*(2*(b/4+(2*a-b)/4)+3)*(2*(b/4+(2*c-b)/4)+3) =
      8*m+3+(4*(b/4)+3)^2 by rwa [←h1,←h2,←h3]]

-- The cube of the Gauss triangular-number product, coefficient by coefficient.
def H1 : Prop := ∀ m : ℕ,
  let E := ∏ i ∈ Icc 1 m, ((1+Polynomial.X^i)*(1-Polynomial.X^(2*i)) : Polynomial ℤ)
  let U := (range (m+1)) ×ˢ ((range (m+1)) ×ˢ (range (m+1)))
  let T := fun x : ℕ => ∑ j ∈ range x,(j+1)
  (E^3).coeff m = ((U.filter (fun v => T v.1+T v.2.1+T v.2.2=m)).card:ℤ)

-- Mortenson (1.12): the coefficient on the product side counts two cones.
def H2 : Prop := ∀ m : ℕ,
  let E := ∏ i ∈ Icc 1 m, ((1+Polynomial.X^i)*(1-Polynomial.X^(2*i)) : Polynomial ℤ)
  let U := (range (m+1)) ×ˢ ((range (m+1)) ×ˢ (range (m+1)))
  let A := fun v : ℕ×ℕ×ℕ => 2*(v.1*v.2.1+v.1*v.2.2+v.2.1*v.2.2)+v.1+v.2.1+v.2.2
  let B := fun v : ℕ×ℕ×ℕ => 2*(v.1*v.2.1+v.1*v.2.2+v.2.1*v.2.2)+3*(v.1+v.2.1+v.2.2)+3
  (E^3).coeff m =
    ((U.filter (fun v => A v=m)).card:ℤ) + ((U.filter (fun v => B v=m)).card:ℤ)

theorem main : H1 → H2 → OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1.H2 := by
  intro gauss mort
  intro s hs _ hmod
  let m := s/8
  have seq : s=8*m+3 := by dsimp [m]; omega
  let U := (range (m+1)) ×ˢ ((range (m+1)) ×ˢ (range (m+1)))
  let T := fun x : ℕ => ∑ j ∈ range x,(j+1)
  let A := fun v : ℕ×ℕ×ℕ => 2*(v.1*v.2.1+v.1*v.2.2+v.2.1*v.2.2)+v.1+v.2.1+v.2.2
  let B := fun v : ℕ×ℕ×ℕ => 2*(v.1*v.2.1+v.1*v.2.2+v.2.1*v.2.2)+3*(v.1+v.2.1+v.2.2)+3
  let L := U.filter (fun v => A v=m)
  let J := U.filter (fun v => B v=m)
  let D := U.filter (fun v => T v.1+T v.2.1+T v.2.2=m)
  let V := (range (s+1)) ×ˢ ((range (s+1)) ×ˢ (range (s+1)))
  let G := V.filter (fun v => 0< v.1 ∧ v.2.1≤ v.1 ∧ v.1≤ v.2.2 ∧ 4*v.1*v.2.2=s+v.2.1^2)
  let R := V.filter (fun v => v.1^2+v.2.1^2+v.2.2^2=s)
  change G.card ≤ R.card
  have counts : L.card+J.card=D.card := by
    have hi := (mort m).symm.trans (gauss m)
    exact_mod_cast hi
  let param (v:ℕ×ℕ×ℕ) := (v.2.1/4,(2*v.1-v.2.1)/4,(2*v.2.2-v.2.1)/4)
  let f (v:ℕ×ℕ×ℕ) : (ℕ×ℕ×ℕ) ⊕ (ℕ×ℕ×ℕ) :=
    if v.2.1%4=1 then Sum.inl (param v) else Sum.inr (param v)
  let back (o : ℕ) (w:ℕ×ℕ×ℕ) := (2*(w.1+w.2.1)+o,4*w.1+o,2*(w.1+w.2.2)+o)
  have data (v : ℕ×ℕ×ℕ) (hv : v∈G) :
      v=back (if v.2.1%4=1 then 1 else 3) (param v) ∧
      (if v.2.1%4=1 then A (param v) else B (param v))=m := by
    obtain ⟨hab,hbc,he⟩ := (mem_filter.mp hv).2.2
    rw [seq] at he
    obtain ⟨e1,e2,e3,e4⟩ := into_cones m hab hbc he
    exact ⟨Prod.ext e1 (Prod.ext e2 e3),e4⟩
  have cover : G.card ≤ (L.disjSum J).card := by
    apply card_le_card_of_injOn f
    · intro v hv
      obtain ⟨_,count⟩ := data v hv
      rcases hh : param v with ⟨x,y,z⟩
      rw [hh] at count
      change (if v.2.1%4=1 then Sum.inl (param v) else Sum.inr (param v)) ∈ _
      split_ifs with hc
      · rw [if_pos hc] at count
        change 2*(x*y+x*z+y*z)+x+y+z=m at count
        change Sum.inl (param v) ∈ L.disjSum J
        rw [hh,inl_mem_disjSum]
        exact mem_filter.mpr ⟨by simp only [U,mem_product,mem_range]; omega,count⟩
      · rw [if_neg hc] at count
        change 2*(x*y+x*z+y*z)+3*(x+y+z)+3=m at count
        change Sum.inr (param v) ∈ L.disjSum J
        rw [hh,inr_mem_disjSum]
        exact mem_filter.mpr ⟨by simp only [U,mem_product,mem_range]; omega,count⟩
    · intro v hv w hw he
      have hh := congrArg (Sum.elim (back 1) (back 3)) he
      have ev := (data v hv).1
      have ew := (data w hw).1
      by_cases a : v.2.1%4=1 <;> by_cases b : w.2.1%4=1 <;>
        simp only [f,a,b,if_true,if_false,Sum.elim_inl,Sum.elim_inr] at hh ev ew <;>
        exact ev.trans (hh.trans ew.symm)
  rw [card_disjSum,counts] at cover
  refine cover.trans (card_le_card_of_injOn (fun v:ℕ×ℕ×ℕ => (2*v.1+1,2*v.2.1+1,2*v.2.2+1)) ?_ ?_)
  · rintro ⟨a,b,c⟩ hv
    obtain ⟨hv,ht⟩ := mem_filter.mp hv
    simp only [U,mem_product,mem_range] at hv
    refine mem_filter.mpr ⟨by simp only [V,mem_product,mem_range]; omega,?_⟩
    change (2*a+1)^2+(2*b+1)^2+(2*c+1)^2=s
    change (∑j∈range a,(j+1))+(∑j∈range b,(j+1))+(∑j∈range c,(j+1))=m at ht
    rw [sqtri,sqtri,sqtri]
    omega
  · rintro ⟨a,b,c⟩ ha ⟨d,e,f⟩ hb hh
    simpa using hh

end OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H2_R1
