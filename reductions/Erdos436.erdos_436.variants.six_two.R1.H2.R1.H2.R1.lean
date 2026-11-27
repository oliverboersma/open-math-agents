import OMAReductions.R_Erdos436_erdos_436_variants_six_two_R1_H2_R1
import Mathlib

/-! Quadratic reciprocity puts the prescribed signs in a rational arithmetic
progression. Cubic character prescription in that progression supplies the
independent cubic part. Their common kernel is the sixth powers. -/
namespace OMA.R_Erdos436_erdos_436_variants_six_two_R1_H2_R1_H2_R1

def H1 : Prop :=
  let w (q : ℕ) : ℕ := if q ∈ ([3,43,61] : List ℕ) then 0 else
    if q ∈ ([71,101,331,733,1423,4877,5413,6043] : List ℕ) then 4 else 5
  ∃ m a C : ℕ, 0 < m ∧ a.Coprime m ∧ 3 ∣ m ∧ a % 3 = 1 ∧
    ∀ p > C, p.Prime → p ≡ a [MOD m] → ∀ q : ℕ, q.Prime → q ≤ 202124 →
      (q : ZMod p)^((p-1)/2) = (-1 : ZMod p)^(w q)

def H2 : Prop :=
  let w (q : ℕ) : ℕ := if q ∈ ([3,43,61] : List ℕ) then 0 else
    if q ∈ ([71,101,331,733,1423,4877,5413,6043] : List ℕ) then 4 else 5
  ∀ m a : ℕ, 0 < m → a.Coprime m → 3 ∣ m → a % 3 = 1 →
    ∀ B : ℕ, ∃ p > B, p.Prime ∧ p ≡ a [MOD m] ∧ 3 ∣ p-1 ∧
      ∃ u : ZMod p, IsPrimitiveRoot u 3 ∧ ∀ q : ℕ, q.Prime → q ≤ 202124 →
        (q : ZMod p)^((p-1)/3) = u^(w q)


lemma criterion (p k : ℕ) (hp : p.Prime) (hk : k ∣ p-1) (hk0 : 0<k)
    (a : ZMod p) (ha : a ≠ 0) : (∃ x : ZMod p, x^k=a) ↔ a^((p-1)/k)=1 := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨x,rfl⟩
    have hx : x ≠ 0 := by rintro rfl; simp [hk0.ne'] at ha
    rw [← pow_mul,Nat.mul_div_cancel' hk]
    exact ZMod.pow_card_sub_one_eq_one hx
  · intro hz
    let b : (ZMod p)ˣ := Units.mk0 a ha
    obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    obtain ⟨e,he⟩ := (mem_powers_iff_mem_zpowers.mpr (hg b) : b ∈ Submonoid.powers g)
    change g^e = b at he
    have hcard : orderOf g = p-1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg,Nat.card_eq_fintype_card,ZMod.card_units]
    have heq : g^(e*((p-1)/k))=1 := by
      rw [pow_mul,he]
      apply Units.ext
      exact hz
    have hd := orderOf_dvd_of_pow_eq_one heq
    rw [hcard] at hd
    let m := (p-1)/k
    have hprod : k*m=p-1 := Nat.mul_div_cancel' hk
    have hm : 0 < m := Nat.div_pos (Nat.le_of_dvd (by have := hp.one_lt; omega) hk) hk0
    have hd' : k*m ∣ e*m := hprod ▸ hd
    obtain ⟨j,hj⟩ := Nat.dvd_of_mul_dvd_mul_right hm hd'
    refine ⟨(g : ZMod p)^j,?_⟩
    rw [← pow_mul,Nat.mul_comm,← hj]
    exact congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) he


lemma eval_list {p : ℕ} (w : ℕ → ℕ) (u : ZMod p) (e : ℕ) (l : List ℕ)
    (h : ∀ q ∈ l, (q : ZMod p)^e = u^(w q)) :
    (l.prod : ZMod p)^e = u^(l.map w).sum := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.prod_cons,Nat.cast_mul,mul_pow,List.map_cons,List.sum_cons,pow_add]
    rw [h q (by simp),ih (fun x hx => h x (by simp [hx]))]

theorem main : H1 → H2 → OMA.R_Erdos436_erdos_436_variants_six_two_R1_H2_R1.H2 := by
  intro quadratic cubic B
  let w (q : ℕ) : ℕ := if q ∈ ([3,43,61] : List ℕ) then 0 else
    if q ∈ ([71,101,331,733,1423,4877,5413,6043] : List ℕ) then 4 else 5
  obtain ⟨m,a,C,hm,hcop,hm3,ha,hq⟩ := quadratic
  obtain ⟨p,hB,hp,hm0,h3,u,hu,hc⟩ := cubic m a hm hcop hm3 ha (max (max B C) 202124)
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have h2 : 2 ∣ p-1 := by obtain ⟨j,hj⟩ := hp.odd_of_ne_two hp2; omega
  have h6 : 6 ∣ p-1 := by omega
  refine ⟨p,by omega,hp,fun n hn hN => ?_⟩
  have hnz : (n : ZMod p) ≠ 0 := by
    intro he
    have := Nat.le_of_dvd hn ((ZMod.natCast_eq_zero_iff _ _).mp he)
    omega
  let l := n.primeFactorsList
  have heval (e : ℕ) (z : ZMod p)
      (h : ∀ q : ℕ, q.Prime → q ≤ 202124 → (q : ZMod p)^e = z^(w q)) :
      (n : ZMod p)^e=z^(l.map w).sum := by
    rw [← Nat.prod_primeFactorsList (n := n) (by omega : n ≠ 0)] at ⊢
    change ((n.primeFactorsList.prod : ℕ) : ZMod p)^e = z^(l.map w).sum
    apply eval_list
    intro q hmem
    exact h q (Nat.prime_of_mem_primeFactorsList hmem)
      ((Nat.le_of_mem_primeFactors (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hmem)).trans hN)
  have eq2 := heval _ _ (hq p (by omega) hp hm0)
  have eq3 := heval _ _ hc
  let x := (n : ZMod p)^((p-1)/6)
  have ex2 : x^2 = u^(l.map w).sum := by
    rw [show x^2 = (n : ZMod p)^((p-1)/3) by dsimp [x]; rw [← pow_mul]; congr 1 <;> omega]
    exact eq3
  have ex3 : x^3 = (-1 : ZMod p)^(l.map w).sum := by
    rw [show x^3 = (n : ZMod p)^((p-1)/2) by dsimp [x]; rw [← pow_mul]; congr 1 <;> omega]
    exact eq2
  have hx : x=1 ↔ 6 ∣ (l.map w).sum := by
    have neg := IsPrimitiveRoot.neg_one (R := ZMod p) p hp2
    constructor
    · intro h
      rw [h,one_pow,eq_comm,hu.pow_eq_one_iff_dvd] at ex2
      rw [h,one_pow,eq_comm,neg.pow_eq_one_iff_dvd] at ex3
      omega
    · intro h
      rw [(hu.pow_eq_one_iff_dvd _).mpr (by omega)] at ex2
      rw [(neg.pow_eq_one_iff_dvd _).mpr (by omega)] at ex3
      rwa [pow_succ,ex2,one_mul] at ex3
  rw [Erdos436.IsPowerResidue,and_iff_right hnz,criterion p 6 hp h6 (by decide) _ hnz,hx,
    ← ZMod.natCast_eq_zero_iff]
  let f (q : ℕ) : ZMod 6 := if q ∈ ([3,43,61] : List ℕ) then 0 else
    if q ∈ ([71,101,331,733,1423,4877,5413,6043] : List ℕ) then 4 else 5
  suffices eqsum : ∀ t : List ℕ, ((t.map w).sum : ZMod 6) = (t.map f).sum by
    rw [eqsum]
  intro t
  induction t with
  | nil => rfl
  | cons q l ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    rw [ih]
    congr 1
    unfold w f
    split_ifs <;> norm_num

end OMA.R_Erdos436_erdos_436_variants_six_two_R1_H2_R1_H2_R1
