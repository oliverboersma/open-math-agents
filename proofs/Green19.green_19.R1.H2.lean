import OMAReductions.R_Green19_green_19_R1
import Mathlib

-- Credit: @marcusbuffett
/-! A random coloring of the three vertex classes realizes the triangle template. A fourth-moment bounded-differences estimate controls all nonzero directions simultaneously. -/
open Finset Filter
open scoped Classical BigOperators
namespace GreenSample
variable {V : Type*} [Fintype V] [Nonempty V]
private lemma eprod {U W : Type*} [Fintype U] [Fintype W] (f : U × W → ℝ) :
    (𝔼 a, f a) = 𝔼 u, 𝔼 w, f (u,w) := by
  simpa using expect_product (univ : Finset U) (univ : Finset W) f

private lemma echead {n : ℕ} (f : (Fin (n+1) → V) → ℝ) :
    (𝔼 a, f a) = 𝔼 t : Fin n → V, 𝔼 v : V, f (Fin.cons v t) := by
  let e : ((Fin n → V) × V) ≃ (Fin (n+1) → V) :=
    { toFun := fun p ↦ Fin.cons p.2 p.1
      invFun := fun a ↦ (fun i ↦ a i.succ, a 0)
      left_inv := fun p ↦ by simp
      right_inv := fun a ↦ by ext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp }
  rw [← Fintype.expect_equiv e (fun p ↦ f (e p)) f (fun _ ↦ rfl), eprod]
  rfl

private lemma abs_mean {U : Type*} [Fintype U] [Nonempty U] {f g : U → ℝ} {L : ℝ}
    (h : ∀ u, |f u - g u| ≤ L) : |(𝔼 u, f u) - 𝔼 u, g u| ≤ L := by
  rw [← expect_sub_distrib]
  exact (abs_expect_le _ _).trans (expect_le univ_nonempty fun u _ ↦ h u)

private lemma conditional {U : Type*} [Fintype U] [Nonempty U] (a L : ℝ) (b : U → ℝ)
    (hb : ∀ u, |b u| ≤ L) (hz : (𝔼 u, b u) = 0) :
    (𝔼 u, (a+b u)^2) ≤ a^2 + L^2 ∧
    (𝔼 u, (a+b u)^4) ≤ a^4 + 8*L^2*a^2 + 3*L^4 := by
  have bs (u) : (b u)^2 ≤ L^2 := by
    have h := abs_le.mp (hb u)
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (show 0 ≤ L + b u by linarith [h.1])]
  have bq (u) : (b u)^4 ≤ L^4 := by nlinarith [sq_le_sq' (show -(L^2) ≤ (b u)^2 by nlinarith [sq_nonneg (b u), sq_nonneg L]) (bs u)]
  constructor
  · calc
      _ ≤ 𝔼 u, (a^2 + L^2 + (2*a)*b u) := expect_le_expect fun u _ ↦ by nlinarith [bs u]
      _ = _ := by rw [expect_add_distrib, ← mul_expect]; simp [hz]
  · calc
      _ ≤ 𝔼 u, (a^4 + 8*L^2*a^2 + 3*L^4 + (4*a^3)*b u) := expect_le_expect fun u _ ↦ by
        nlinarith [sq_nonneg (a*b u - (b u)^2), bq u, mul_le_mul_of_nonneg_right (bs u) (sq_nonneg a)]
      _ = _ := by rw [expect_add_distrib, ← mul_expect]; simp [hz]

lemma boundedMoments {n : ℕ} (f : (Fin n → V) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (osc : ∀ (i : Fin n) x y, (∀ j, j ≠ i → x j = y j) → |f x-f y| ≤ L) :
    (𝔼 x, (f x - 𝔼 z, f z)^2) ≤ n * L^2 ∧
    (𝔼 x, (f x - 𝔼 z, f z)^4) ≤ 4*(n:ℝ)^2 * L^4 := by
  classical
  induction n with
  | zero =>
    have eq : ∀ x : Fin 0 → V, f x = f (fun i ↦ i.elim0) := fun x ↦ congrArg f (Subsingleton.elim _ _)
    simp [eq]
  | succ n ih =>
    let g := fun t : Fin n → V ↦ 𝔼 v : V, f (Fin.cons v t)
    let m := 𝔼 t, g t
    have hmean : (𝔼 z, f z) = m := echead f
    have gosc (i : Fin n) (x y : Fin n → V) (h : ∀ j, j ≠ i → x j = y j) : |g x-g y| ≤ L := by
      apply abs_mean
      intro v
      apply osc i.succ
      intro j
      refine Fin.cases (by simp) (fun k hk ↦ ?_) j
      simpa using h k (fun he ↦ hk (congrArg Fin.succ he))
    obtain ⟨ig2,ig4⟩ := ih g gosc
    have cb (t : Fin n → V) (v : V) : |f (Fin.cons v t)-g t| ≤ L := by
      have h (w : V) : |f (Fin.cons v t)-f (Fin.cons w t)| ≤ L := by
        apply osc 0
        intro j
        refine Fin.cases (by simp) (fun k _ ↦ by simp) j
      simpa only [g, Fintype.expect_const] using abs_mean h
    have bound (t : Fin n → V) :=
      conditional (g t-m) L (fun v ↦ f (Fin.cons v t)-g t) (cb t) (by simp [expect_sub_distrib,g])
    have c2 (t : Fin n → V) : (𝔼 v, (f (Fin.cons v t)-m)^2) ≤ (g t-m)^2 + L^2 := by
      simpa only [sub_add_sub_cancel'] using (bound t).1
    have c4 (t : Fin n → V) : (𝔼 v, (f (Fin.cons v t)-m)^4) ≤ (g t-m)^4 + 8*L^2*(g t-m)^2 + 3*L^4 := by
      simpa only [sub_add_sub_cancel'] using (bound t).2
    change (𝔼 x, (g x-m)^2) ≤ _ at ig2
    change (𝔼 x, (g x-m)^4) ≤ _ at ig4
    rw [hmean, echead, echead (fun x ↦ (f x-m)^4)]
    constructor
    · calc
        _ ≤ 𝔼 t, ((g t-m)^2 + L^2) := expect_le_expect fun t _ ↦ c2 t
        _ ≤ _ := by rw [expect_add_distrib, Fintype.expect_const]; push_cast; linarith
    · calc
        _ ≤ 𝔼 t, ((g t-m)^4 + 8*L^2*(g t-m)^2 + 3*L^4) := expect_le_expect fun t _ ↦ c4 t
        _ ≤ _ := by
          simp only [expect_add_distrib, ← mul_expect, Fintype.expect_const, Nat.cast_succ]
          nlinarith [mul_le_mul_of_nonneg_left ig2 (show 0 ≤ 8*L^2 by positivity), sq_nonneg (L^2)]
lemma momentsAny {I : Type*} [Fintype I] [DecidableEq I] (f : (I → V) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (osc : ∀ (i : I) x y, (∀ j, j ≠ i → x j = y j) → |f x-f y| ≤ L) :
    (𝔼 x, (f x - 𝔼 z, f z)^4) ≤ 4*(Fintype.card I : ℝ)^2 * L^4 := by
  let e := Fintype.equivFin I
  let E := e.arrowCongr (Equiv.refl V)
  let g := fun u ↦ f (E.symm u)
  have he (u : Fin (Fintype.card I) → V) (i : I) : E.symm u i = u (e i) := rfl
  have hosc (i : Fin (Fintype.card I)) (x y : Fin (Fintype.card I) → V)
      (h : ∀ j, j ≠ i → x j = y j) : |g x-g y| ≤ L := by
    apply osc (e.symm i)
    intro j hj
    exact h (e j) (fun eq ↦ hj (e.apply_eq_iff_eq_symm_apply.mp eq))
  have hg := (boundedMoments g L hL hosc).2
  have avg : (𝔼 x, f x) = 𝔼 u, g u := Fintype.expect_equiv E _ _ (fun x ↦ by simp [g])
  rw [avg, Fintype.expect_equiv E _ (fun u ↦ (g u - 𝔼 z, g z)^4) (fun x ↦ by simp [g])]
  exact hg

lemma simultaneous {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] (F : K → (I → V) → ℝ)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 < T)
    (osc : ∀ k (i : I) x y, (∀ j, j ≠ i → x j = y j) → |F k x-F k y| ≤ L)
    (big : (Fintype.card K : ℝ)*(4*(Fintype.card I : ℝ)^2 * L^4) < T^4) :
    ∃ x, ∀ k, |F k x - 𝔼 z, F k z| < T := by
  classical
  have av : (𝔼 x, ∑ k, (F k x - 𝔼 z, F k z)^4) ≤
      (Fintype.card K : ℝ)*(4*(Fintype.card I : ℝ)^2*L^4) := by
    rw [expect_sum_comm]
    simpa using sum_le_sum (s := (univ : Finset K)) (fun k _ ↦ momentsAny (F k) L hL (osc k))
  obtain ⟨x,_,hx⟩ := exists_le_of_expect_le univ_nonempty av
  refine ⟨x, fun k ↦ ?_⟩
  have b := single_le_sum (s := (univ : Finset K)) (f := fun k ↦ (F k x - 𝔼 z, F k z)^4)
      (fun i _ ↦ by positivity) (mem_univ k)
  by_contra! h
  have := pow_le_pow_left₀ hT.le h 4
  rw [← abs_pow, abs_of_nonneg (by positivity)] at this
  linarith

lemma marginal {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (u : J ↪ I) (H : (J → V) → ℝ) :
    (𝔼 x : I → V, H (fun j ↦ x (u j))) = 𝔼 z, H z := by
  classical
  let s := Set.range u
  let e := Equiv.ofInjective u u.injective
  let e₁ := Equiv.piEquivPiSubtypeProd (fun i ↦ i ∈ s) (fun _ ↦ V)
  let e₂ := e.symm.arrowCongr (Equiv.refl V)
  let E := e₁.trans (e₂.prodCongr (Equiv.refl _))
  have he (x : I → V) : (E x).1 = fun j ↦ x (u j) := rfl
  rw [Fintype.expect_equiv E _ (fun pair ↦ H pair.1) (fun x ↦ by rw [he]), eprod]
  simp [Fintype.expect_const]

noncomputable def countSample {U I J : Type*} [Fintype U]
    (coord : U → J → I) (H : (J → V) → Prop) (f : I → V) : ℝ :=
  ∑ p : U, if H (fun j ↦ f (coord p j)) then 1 else 0

lemma meanSample {U I J : Type*} [Fintype U] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (coord : U → J → I) (hi : ∀ p, Function.Injective (coord p)) (H : (J → V) → Prop) :
    (𝔼 f, countSample coord H f) =
    (Fintype.card U : ℝ) * (((univ : Finset (J → V)).filter H).card / (Fintype.card V : ℝ)^(Fintype.card J)) := by
  classical
  unfold countSample
  rw [expect_sum_comm]
  have hh (p : U) := marginal (V := V) (⟨_,hi p⟩ : J ↪ I) (fun z ↦ if H z then (1:ℝ) else 0)
  simp only [Function.Embedding.coeFn_mk] at hh
  simp_rw [hh]
  rw [Fintype.expect_eq_sum_div_card]
  simp [Fintype.card_fun, Nat.cast_pow, Finset.sum_boole]

lemma oscSample {U I J : Type*} [Fintype U] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (coord : U → J → I) (H : (J → V) → Prop) (M : ℕ)
    (hM : ∀ j i, ((univ : Finset U).filter (fun p ↦ coord p j = i)).card ≤ M)
    (i : I) (x y : I → V) (hxy : ∀ j, j ≠ i → x j = y j) :
    |countSample coord H x-countSample coord H y| ≤ (Fintype.card J : ℝ)*M := by
  classical
  unfold countSample
  rw [← sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ p : U, ∑ j : J, if coord p j = i then (1:ℝ) else 0 := by
      apply sum_le_sum
      intro p _
      by_cases hb : ∃ j, coord p j = i
      · obtain ⟨j,hj⟩ := hb
        have h := single_le_sum (s := (univ : Finset J))
          (f := fun j ↦ if coord p j = i then (1:ℝ) else 0) (fun k _ ↦ by split <;> norm_num) (mem_univ j)
        rw [if_pos hj] at h
        split_ifs <;> norm_num at * <;> assumption
      · have same : (fun j ↦ x (coord p j)) = (fun j ↦ y (coord p j)) :=
          funext fun j ↦ hxy _ (fun he ↦ hb ⟨_,he⟩)
        rw [same, sub_self, abs_zero]
        exact sum_nonneg (fun j _ ↦ by split <;> norm_num)
    _ = ∑ j : J, (((univ : Finset U).filter (fun p ↦ coord p j = i)).card : ℝ) := by rw [sum_comm]; simp [Finset.sum_boole]
    _ ≤ ∑ _ : J, (M : ℝ) := sum_le_sum fun j _ ↦ by exact_mod_cast hM j i
    _ = _ := by simp

end GreenSample

open Finset Filter
open scoped Classical BigOperators
namespace GreenSample
variable {V : Type*} [Fintype V] [DecidableEq V]
def triangle (G : SimpleGraph V) (a b c : V) := G.Adj a b ∧ G.Adj a c ∧ G.Adj b c
def densityEvent (G : SimpleGraph V) (u : Fin 3 → V) := triangle G (u 0) (u 1) (u 2)
def cornerEvent (G : SimpleGraph V) (u : Fin 6 → V) :=
  triangle G (u 0) (u 1) (u 2) ∧ triangle G (u 3) (u 1) (u 5) ∧ triangle G (u 0) (u 4) (u 5)

lemma uniqueThird {G : SimpleGraph V} (hl : G.LocallyLinear) {a b c d : V}
    (hc : triangle G a b c) (hd : triangle G a b d) : c = d := by
  obtain ⟨hab,hac,hbc⟩ := hc
  obtain ⟨_,had,hbd⟩ := hd
  have eq : ({a,b,c} : Finset V) = {a,b,d} := by
    apply hl.1.eq (by simp [SimpleGraph.is3Clique_triple_iff, *]) (by simp [SimpleGraph.is3Clique_triple_iff, *])
    exact Set.Nontrivial.not_subsingleton ⟨a, by simp, b, by simp, hab.ne⟩
  have h : c ∈ ({a,b,d} : Finset V) := eq ▸ (by simp)
  simpa [hac.ne', hbc.ne'] using h

lemma congrCorner {G : SimpleGraph V} (hl : G.LocallyLinear) {u : Fin 6 → V} (h : cornerEvent G u) :
    u 2 = u 5 ∧ u 3 = u 0 ∧ u 4 = u 1 := by
  obtain ⟨ha,hb,hc⟩ := h
  have t : triangle G (u 0) (u 1) (u 5) := ⟨ha.1,hc.2.1,hb.2.2⟩
  refine ⟨uniqueThird hl ha t, ?_, ?_⟩
  · exact uniqueThird (a := u 1) (b := u 5) hl ⟨hb.2.2,hb.1.symm,hb.2.1.symm⟩ ⟨t.2.2,t.1.symm,t.2.1.symm⟩
  · exact uniqueThird (a := u 0) (b := u 5) hl ⟨hc.2.1,hc.1,hc.2.2.symm⟩ ⟨t.2.1,t.1,t.2.2.symm⟩

lemma cornerCard (G : SimpleGraph V) (hl : G.LocallyLinear) :
    ((univ : Finset (Fin 6 → V)).filter (cornerEvent G)).card ≤ (Fintype.card V)^2 := by
  let S := (univ : Finset (Fin 6 → V)).filter (cornerEvent G)
  let F (u : S) : V × V := (u.val 0, u.val 1)
  have inj : Function.Injective F := by
    intro u v e
    have hu := (mem_filter.mp u.property).2
    have hv := (mem_filter.mp v.property).2
    have eq0 : u.val 0 = v.val 0 := congrArg Prod.fst e
    have eq1 : u.val 1 = v.val 1 := congrArg Prod.snd e
    have eq2 : u.val 2 = v.val 2 := uniqueThird hl hu.1 (by rw [eq0,eq1]; exact hv.1)
    obtain ⟨ua,ub,uc⟩ := congrCorner hl hu
    obtain ⟨va,vb,vc⟩ := congrCorner hl hv
    apply Subtype.ext
    funext i
    fin_cases i <;> simp_all
  simpa only [Fintype.card_coe,S,Fintype.card_prod,pow_two] using Fintype.card_le_of_injective F inj

lemma densityCard (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * (G.cliqueFinset 3).card ≤ ((univ : Finset (Fin 3 → V)).filter (densityEvent G)).card := by
  let C := ↥(G.cliqueFinset 3)
  have rep (s : C) : ∃ a b c, triangle G a b c ∧ s.val = {a,b,c} := by
    obtain ⟨a,b,c,hab,hac,hbc,e⟩ := SimpleGraph.is3Clique_iff.mp (SimpleGraph.mem_cliqueFinset_iff.mp s.property)
    exact ⟨a,b,c,⟨hab,hac,hbc⟩,e⟩
  choose a b c tr he using rep
  let P := (univ : Finset (Fin 3 → V)).filter (densityEvent G)
  let f (p : Bool × C) : Fin 3 → V := if p.1 then ![b p.2,a p.2,c p.2] else ![a p.2,b p.2,c p.2]
  have hf (p : Bool × C) : f p ∈ P := by
    obtain ⟨flag,s⟩ := p
    obtain ⟨hab,hac,hbc⟩ := tr s
    cases flag <;> simp [P,f,densityEvent,triangle,hab,hac,hbc,hab.symm]
  let F (p : Bool × C) : P := ⟨f p,hf p⟩
  have recover (p : Bool × C) : ({f p 0,f p 1,f p 2} : Finset V) = p.2.val := by
    obtain ⟨flag,s⟩ := p
    cases flag <;> simp [f,he s,Finset.insert_comm]
  have inj : Function.Injective F := by
    rintro ⟨b₁,s⟩ ⟨b₂,t⟩ eq
    have ev : f (b₁,s) = f (b₂,t) := congrArg Subtype.val eq
    have eqs : s = t := Subtype.ext ((recover (b₁,s)).symm.trans ((congrArg (fun v : Fin 3 → V ↦ ({v 0,v 1,v 2} : Finset V)) ev).trans (recover (b₂,t))))
    subst t
    have first := congrFun ev 0
    have ne := (tr s).1.ne
    cases b₁ <;> cases b₂ <;> simp_all [f]
  simpa only [C,P,Fintype.card_prod,Fintype.card_bool,Fintype.card_coe] using Fintype.card_le_of_injective F inj
end GreenSample

open Finset Filter
open scoped Classical BigOperators
namespace GreenSample
variable {W : Type*} [AddCommGroup W] [Fintype W] [DecidableEq W]
def coord3 (p : W × W) : Fin 3 → Fin 3 × W := ![(0,p.1), (1,p.2), (2,p.1+p.2)]
def coord6 (d : W) (p : W × W) : Fin 6 → Fin 3 × W :=
  ![(0,p.1), (1,p.2), (2,p.1+p.2), (0,p.1+d), (1,p.2+d), (2,p.1+p.2+d)]

lemma coord3inj (p : W × W) : Function.Injective (coord3 p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coord3]
lemma coord6inj {d : W} (hd : d ≠ 0) (p : W × W) : Function.Injective (coord6 d p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coord6]

private lemma lineBound (k : Fin 3) (t : W) (i : Fin 3 × W) :
    ((univ : Finset (W × W)).filter (fun p ↦
      (k, (![p.1,p.2,p.1+p.2] k)+t) = i)).card ≤ Fintype.card W := by
  classical
  let S := (univ : Finset (W × W)).filter (fun p ↦ (k, (![p.1,p.2,p.1+p.2] k)+t) = i)
  let key (x : S) := if k = 0 then x.val.2 else x.val.1
  have inj : Function.Injective key := by
    rintro ⟨⟨x,y⟩,hx⟩ ⟨⟨x',y'⟩,hy⟩ eq
    have ev := congrArg Prod.snd (((mem_filter.mp hx).2).trans (mem_filter.mp hy).2.symm)
    fin_cases k <;> simp_all [key]
  simpa only [S,Fintype.card_coe] using Fintype.card_le_of_injective key inj

lemma bound3 (j : Fin 3) (i : Fin 3 × W) :
    ((univ : Finset (W × W)).filter (fun p ↦ coord3 p j = i)).card ≤ Fintype.card W := by
  fin_cases j
  · convert! lineBound 0 (0:W) i using 1
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [coord3]
  · convert! lineBound 1 (0:W) i using 1
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [coord3]
  · convert! lineBound 2 (0:W) i using 1
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [coord3]

lemma bound6 (d : W) (j : Fin 6) (i : Fin 3 × W) :
    ((univ : Finset (W × W)).filter (fun p ↦ coord6 d p j = i)).card ≤ Fintype.card W := by
  fin_cases j
  · convert! lineBound 0 (0:W) i using 1
    all_goals congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp [coord6]
  · convert! lineBound 1 (0:W) i using 1
    all_goals congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp [coord6]
  · convert! lineBound 2 (0:W) i using 1
    all_goals congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp [coord6]
  · convert! lineBound 0 d i using 1
    all_goals congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp [coord6]
  · convert! lineBound 1 d i using 1
    all_goals congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp [coord6]
  · convert! lineBound 2 d i using 1
    all_goals congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp [coord6]
end GreenSample

namespace GreenSample
open Filter Finset
open scoped Classical BigOperators
variable {W V : Type*} [AddCommGroup W] [Fintype W] [Fintype V]

noncomputable def vertexSet (G : SimpleGraph V) (x : Fin 3 × W → V) : Finset (W × W) :=
  univ.filter (fun p ↦ densityEvent G (fun j ↦ x (coord3 p j)))

lemma sample3eq (G : SimpleGraph V) (x : Fin 3 × W → V) :
    countSample coord3 (densityEvent G) x = ((vertexSet G x).card : ℝ) := by
  simp [countSample,vertexSet,sum_boole]

lemma sample6eq (G : SimpleGraph V) (x : Fin 3 × W → V) (d : W) :
    countSample (coord6 d) (cornerEvent G) x = ((Green19.S d (vertexSet G x)).card : ℝ) := by
  classical
  simp only [countSample,sum_boole]
  apply congrArg (fun s : Finset (W × W) ↦ (s.card : ℝ))
  have mv (p : W × W) : p ∈ vertexSet G x ↔ densityEvent G (fun j ↦ x (coord3 p j)) := by
    unfold vertexSet
    exact (@Finset.mem_filter _ _ _ _ _).trans (and_iff_right (mem_univ p))
  ext p
  unfold Green19.S
  rw [Finset.mem_filter,Finset.mem_filter]
  simp only [mem_univ,true_and,Green19.IsCorner,mv,cornerEvent,densityEvent]
  simp [coord3,coord6,add_assoc,add_comm,add_left_comm]

end GreenSample

open GreenSample Filter Finset
open scoped Classical BigOperators
theorem OMA.solution : OMA.R_Green19_green_19_R1.H2 := by
  classical
  intro q hq G _ hl
  haveI : NeZero q := ⟨by omega⟩
  have qp : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  apply Filter.Eventually.frequently
  filter_upwards [eventually_gt_atTop (46656*q^16)] with n hn
  let W := 𝔽₂ n
  let N : ℝ := Fintype.card W
  have np : 0 < N := by dsimp [N]; positivity
  let t : ℝ := (G.cliqueFinset 3).card
  by_cases ht : (G.cliqueFinset 3).card = 0
  · refine ⟨∅, ?_, fun d _ ↦ ?_⟩
    · simp [ht]
    · simp [Green19.S,Green19.IsCorner]; positivity
  have tp : 1 ≤ t := by dsimp [t]; exact_mod_cast (show 1 ≤ (G.cliqueFinset 3).card by omega)
  have cardW : Fintype.card W = 2^n := by simp [W,𝔽₂,𝔽,Fintype.card_fun]
  have alln (m : ℕ) : m < 2^m := by induction m with | zero => simp | succ m ih => rw [pow_succ]; omega
  have hn2 := alln n
  have large : 46656 * (q : ℝ)^16 < N := by
    dsimp only [N]
    exact_mod_cast (show 46656*q^16 < Fintype.card W by rw [cardW]; omega)
  let F (d : W) (f : Fin 3 × W → Fin q) :=
    if d = 0 then countSample coord3 (densityEvent G) f else countSample (coord6 d) (cornerEvent G) f
  let T := N^2 / (q:ℝ)^4
  have Tpos : 0 < T := by dsimp [T]; positivity
  have os (d : W) (i : Fin 3 × W) (f g : Fin 3 × W → Fin q) (h : ∀ j, j ≠ i → f j = g j) :
      |F d f - F d g| ≤ 6*N := by
    by_cases hd : d = 0
    · simpa [F,hd] using (oscSample coord3 (densityEvent G) (Fintype.card W) (bound3 (W := W)) i f g h).trans
        (show (Fintype.card (Fin 3):ℝ)*Fintype.card W ≤ 6*N by simp only [Fintype.card_fin,Nat.cast_ofNat]; change 3*N ≤ 6*N; linarith)
    · simpa [F,hd,N] using oscSample (coord6 d) (cornerEvent G) (Fintype.card W) (bound6 d) i f g h
  have big : (Fintype.card W : ℝ)*(4*(Fintype.card (Fin 3 × W):ℝ)^2*(6*N)^4) < T^4 := by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    change N*(4*(3*N)^2*(6*N)^4) < (N^2/(q:ℝ)^4)^4
    rw [div_pow, lt_div_iff₀ (by positivity)]
    nlinarith only [mul_lt_mul_of_pos_right large (show 0 < N^7 by positivity)]
  obtain ⟨f,good⟩ := simultaneous (V := Fin q) F (L := 6*N) (T := T) (by positivity) Tpos os big
  have h3 := meanSample (V := Fin q) (@coord3 W _ ) coord3inj (densityEvent G)
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at h3
  have dg := good 0
  simp only [F,if_true] at dg
  rw [h3] at dg
  have lo := (abs_lt.mp dg).1
  have ca : 2*t ≤ (((univ : Finset (Fin 3 → Fin q)).filter (densityEvent G)).card : ℝ) := by dsimp [t]; exact_mod_cast densityCard G
  have lomean : N*N * (2*t/(q:ℝ)^3) ≤ N*N * ((((univ : Finset (Fin 3 → Fin q)).filter (densityEvent G)).card : ℝ)/(q:ℝ)^3) := by gcongr
  have margin : T ≤ (t/(q:ℝ)^3)*N^2 := by
    change N^2 / (q:ℝ)^4 ≤ _
    field_simp
    have qr : 1 ≤ (q:ℝ) := by exact_mod_cast hq.le
    exact one_le_mul_of_one_le_of_one_le qr tp
  refine ⟨vertexSet G f, ?_, ?_⟩
  · change t / (q:ℝ)^3 * N^2 ≤ _
    rw [← sample3eq]
    change -T < countSample coord3 (densityEvent G) f - N*N*(_/(q:ℝ)^3) at lo
    have hh : t/(q:ℝ)^3*N^2 + T ≤ N*N*(2*t/(q:ℝ)^3) := calc
      _ ≤ t/(q:ℝ)^3*N^2 + t/(q:ℝ)^3*N^2 := add_le_add_right margin _
      _ = _ := by ring
    linarith only [lo,hh.trans lomean]
  · intro d hd
    have h6 := meanSample (V := Fin q) (coord6 d) (coord6inj hd) (cornerEvent G)
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at h6
    have ug := good d
    simp only [F,if_neg hd] at ug
    rw [h6] at ug
    have hi := (abs_lt.mp ug).2
    have ca6 : (((univ : Finset (Fin 6 → Fin q)).filter (cornerEvent G)).card : ℝ) ≤ (q:ℝ)^2 := by
      simpa only [Fintype.card_fin] using (show (((univ : Finset (Fin 6 → Fin q)).filter (cornerEvent G)).card : ℝ) ≤ (Fintype.card (Fin q) : ℝ)^2 by exact_mod_cast cornerCard G hl)
    have up : N*N * ((((univ : Finset (Fin 6 → Fin q)).filter (cornerEvent G)).card : ℝ)/(q:ℝ)^6) ≤ T := calc
      _ ≤ N*N * ((q:ℝ)^2/(q:ℝ)^6) := by gcongr
      _ = _ := by dsimp [T]; field_simp <;> ring
    rw [← sample6eq]
    change countSample (coord6 d) (cornerEvent G) f ≤ (2/(q:ℝ)^4)*N^2
    change countSample (coord6 d) (cornerEvent G) f - N*N*(_/(q:ℝ)^6) < T at hi
    calc
      _ ≤ T+T := by linarith only [up,hi]
      _ = _ := by dsimp [T]; ring

