import OMAReductions.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1

/-! Bui, Pratt and Zaharescu, section 3. The centered factorial equation
gives a common rational approximation to two algebraic functions. Three
independent integer Padé forms with sufficiently small values preclude that
approximation, since their scalar products with the integer vector would all
have absolute value less than one. Credit: @marcusbuffett. -/

namespace OMA.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1_H1_R1

open Finset Filter Real
open scoped Classical

private lemma incompatible {Y D w z : ℝ} (hY : 0 < Y) (hD : 0 < D)
    {x : ℕ} (hx : 0 < x) (hxy : (x:ℝ) ≤ 2*Y) {p q : ℤ}
    (hp : |(x:ℝ)*w-p| ≤ 1/D) (hq : |(x:ℝ)*z-q| ≤ 1/D)
    (A : Matrix (Fin 3) (Fin 3) ℤ) (hn : A.det ≠ 0)
    (hs : ∀ i j, |(A i j:ℝ)| ≤ D/8)
    (he : ∀ i, |(A i 0:ℝ)+(A i 1:ℝ)*w+(A i 2:ℝ)*z| ≤ 1/(8*Y)) : False := by
  let v : Fin 3 → ℤ := ![(x:ℤ),p,q]
  have hz : A.mulVec v = 0 := by
    funext i
    let a : ℝ := A i 0
    let b : ℝ := A i 1
    let c : ℝ := A i 2
    have bound1 : |(x:ℝ)*(a+b*w+c*z)| ≤ 1/4 := by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      have hh := mul_le_mul hxy (he i) (abs_nonneg _) (by positivity)
      calc _ ≤ (2*Y)*(1/(8*Y)) := hh
           _ = _ := by field_simp <;> ring
    have bound2 (e f : ℝ) (hh : |e| ≤ D/8) (hf : |f| ≤ 1/D) : |e*f| ≤ 1/8 := by
      rw [abs_mul]
      calc _ ≤ (D/8)*(1/D) := mul_le_mul hh hf (abs_nonneg _) (by positivity)
           _ = _ := by field_simp
    have hsmall : |a*x+b*p+c*q| < 1 := by
      have eq : a*x+b*p+c*q=(x:ℝ)*(a+b*w+c*z) - b*((x:ℝ)*w-p) - c*((x:ℝ)*z-q) := by ring
      rw [eq]
      have t1 := abs_sub ((x:ℝ)*(a+b*w+c*z)) (b*((x:ℝ)*w-p))
      have t2 := abs_sub ((x:ℝ)*(a+b*w+c*z)-b*((x:ℝ)*w-p)) (c*((x:ℝ)*z-q))
      linarith [bound2 b _ (hs i 1) hp,bound2 c _ (hs i 2) hq]
    change A.mulVec v i = 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    change A i 0*(x:ℤ)+A i 1*p+A i 2*q=0
    have hi : |A i 0*(x:ℤ)+A i 1*p+A i 2*q| < 1 := by
      dsimp [a,b,c] at hsmall
      exact_mod_cast hsmall
    rw [abs_lt] at hi
    omega
  have hv := Matrix.eq_zero_of_mulVec_eq_zero hn hz
  have h0 := congrFun hv 0
  change (x:ℤ) = 0 at h0
  omega

-- The approximation by shifted factorial solutions, Lemma 3.3.
def H1 : Prop := ∀ T : Finset ℕ, 2 ≤ T.card → ∀ η : ℝ, 0 < η →
  let r := T.card
  let Y := fun n : ℕ => (r:ℝ)*(n.factorial:ℝ)^(1/(r:ℝ))
  let w := fun b n : ℕ => ∏ j ∈ Ico 1 b, (1-(j:ℝ)/n)^(-(1:ℝ)/r)
  let sol := fun n y : ℕ => (r:ℤ)^r*(n.factorial:ℤ) = ∏ i∈T, ((y:ℤ)+(r:ℤ)*i-(∑ j∈T,(j:ℤ)))
  ∀ᶠ N : ℕ in atTop, ∀ n ∈ Ico N (2*N), ∀ x : ℕ, sol n x →
    0 < x ∧ (x:ℝ) ≤ 2*Y n ∧ ∀ b : ℕ, 0 < b → b ≤ n →
      b ≤ ⌊(N:ℝ)^(1/34:ℝ)⌋₊ → r ∣ b → (∃ z : ℕ, sol (n-b) z) →
      ∃ p : ℤ, |(x:ℝ)*w b n-p| ≤ 1/(Y n)^(1-η)

-- The simultaneous Padé certificate after clearing the denominators in
-- Proposition 3.4. This estimate involves only the degree and the shifts.
def H2 : Prop := ∀ r : ℕ, 2 ≤ r → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
  let Y := fun n : ℕ => (r:ℝ)*(n.factorial:ℝ)^(1/(r:ℝ))
  let w := fun b n : ℕ => ∏ j ∈ Ico 1 b, (1-(j:ℝ)/n)^(-(1:ℝ)/r)
  ∀ᶠ N : ℕ in atTop, let M := ⌊(N:ℝ)^(1/34:ℝ)⌋₊
    ∀ u v : ℕ, 0 < u → u < v → v ≤ M → r ∣ u → r ∣ v →
    let cert := fun n : ℕ => ∃ A : Matrix (Fin 3) (Fin 3) ℤ, A.det ≠ 0 ∧
      (∀ i j, |(A i j:ℝ)| ≤ (Y n)^(1-η)/8) ∧
      ∀ i, |(A i 0:ℝ)+(A i 1:ℝ)*w u n+(A i 2:ℝ)*w v n| ≤ 1/(8*Y n)
    (((Ico N (2*N)).filter (fun n => ¬cert n)).card:ℝ) ≤ C*N/(M:ℝ)^3

theorem main : H1 → H2 → OMA.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1.H1 := by
  intro approx pade T hr
  let r := T.card
  let Y := fun n : ℕ => (r:ℝ)*(n.factorial:ℝ)^(1/(r:ℝ))
  let w := fun b n : ℕ => ∏ j ∈ Ico 1 b, (1-(j:ℝ)/n)^(-(1:ℝ)/r)
  let sol := fun n y : ℕ => (r:ℤ)^r*(n.factorial:ℤ) = ∏ i∈T, ((y:ℤ)+(r:ℤ)*i-(∑ j∈T,(j:ℤ)))
  obtain ⟨η,hη,C,hC,hp⟩ := pade r hr
  have ha := approx T hr η hη
  obtain ⟨B,hB⟩ := eventually_atTop.mp (ha.and hp)
  let K := max C (((B+1:ℕ):ℝ)^3)
  refine ⟨K,lt_of_lt_of_le hC (le_max_left ..),?_⟩
  intro N hN
  intro M u v hu huv hv du dv
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hM : 1 ≤ M := Nat.one_le_floor_iff _ |>.mpr (Real.one_le_rpow hN1 (by norm_num))
  have hMp : 0 < (M:ℝ) := by exact_mod_cast (show 0 < M by omega)
  let G := (Ico N (2*N)).filter (fun n => v≤n ∧ (∃ x,sol n x) ∧
    (∃ x,sol (n-u) x) ∧ (∃ x,sol (n-v) x))
  change (G.card:ℝ) ≤ K*N/(M:ℝ)^3
  by_cases large : B ≤ N
  · obtain ⟨a,b⟩ := hB N large
    let cert := fun n : ℕ => ∃ A : Matrix (Fin 3) (Fin 3) ℤ, A.det ≠ 0 ∧
      (∀ i j, |(A i j:ℝ)| ≤ (Y n)^(1-η)/8) ∧
      ∀ i, |(A i 0:ℝ)+(A i 1:ℝ)*w u n+(A i 2:ℝ)*w v n| ≤ 1/(8*Y n)
    let F := (Ico N (2*N)).filter (fun n => ¬cert n)
    have hsub : G ⊆ F := by
      intro n hn
      obtain ⟨hin,hnv,⟨x,hx⟩,hu0,hv0⟩ := mem_filter.mp hn
      refine mem_filter.mpr ⟨hin,?_⟩
      rintro ⟨A,hd,hs,he⟩
      obtain ⟨hx0,hxy,hb⟩ := a n hin x hx
      obtain ⟨p,hp⟩ := hb u hu (by omega) (by omega) du hu0
      obtain ⟨q,hq⟩ := hb v (by omega) hnv hv dv hv0
      have hY : 0 < Y n := by
        have rr : 0 < (r:ℝ) := by exact_mod_cast (show 0 < r by change 2 ≤ r at hr; omega)
        dsimp [Y]
        positivity
      exact incompatible hY (Real.rpow_pos_of_pos hY _) hx0 hxy hp hq A hd hs he
    have hF : (F.card:ℝ) ≤ C*N/(M:ℝ)^3 := b u v hu huv hv du dv
    calc (G.card:ℝ) ≤ F.card := by exact_mod_cast card_le_card hsub
         _ ≤ C*N/(M:ℝ)^3 := hF
         _ ≤ K*N/(M:ℝ)^3 := by gcongr; exact le_max_left ..
  · have hmN : M ≤ N := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le hN1 (by norm_num))
    have hG : G.card ≤ N := by
      calc G.card ≤ (Ico N (2*N)).card := card_le_card (filter_subset ..)
           _ = N := by rw [Nat.card_Ico]; omega
    have hmB : (M:ℝ) ≤ (B+1:ℕ) := by exact_mod_cast (show M ≤ B+1 by omega)
    have hk : (M:ℝ)^3 ≤ K := (pow_le_pow_left₀ (Nat.cast_nonneg _) hmB 3).trans (le_max_right ..)
    rw [le_div_iff₀ (pow_pos hMp _)]
    calc (G.card:ℝ)*(M:ℝ)^3 ≤ (N:ℝ)*K := by
              exact mul_le_mul (by exact_mod_cast hG) hk (by positivity) (Nat.cast_nonneg _)
         _ = K*N := mul_comm ..

end OMA.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1_H1_R1
