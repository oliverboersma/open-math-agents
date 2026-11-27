import OMAReductions.R_Erdos824_erdos_824_variants_pollack_pomerance_R1
import Mathlib

/-!
Use only integer powers of two. If l=floor(log₂ x) and t=floor(log₂ l / 41),
take y=2^(10t), and fit 3d primes below x with d=floor((l-1)/(390t)).
There are at least 2^(129t) primes in the input and at most 2^(130t).
The gap between 40t and 41t absorbs the cost of encoding the smooth values.
-/

open Filter
namespace OMA.PollackScale

private lemma choose_blocks (n k b : ℕ) (h : (b+1)*k ≤ n) : b^k ≤ n.choose k := by
  apply Nat.le_of_mul_le_mul_left (c := k.factorial) _ (Nat.factorial_pos _)
  calc
    k.factorial*b^k ≤ k^k*b^k := Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
    _ = (k*b)^k := (mul_pow _ _ _).symm
    _ ≤ (n+1-k)^k := Nat.pow_le_pow_left (by rw [add_mul,one_mul,mul_comm b k] at h; omega) _
    _ ≤ n.descFactorial k := Nat.pow_sub_le_descFactorial _ _
    _ = _ := Nat.descFactorial_eq_factorial_mul_choose _ _

private lemma plenty {t : ℕ} (h : 100 ≤ t) : 1000000*(t+1) ≤ 2^t := by
  induction t, h using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    rw [pow_succ]
    omega

private lemma numeric (K x l t d : ℕ) (ht : 100 ≤ t) (hK : K ≤ t)
    (hx : 2^l ≤ x) (hx' : x < 2^(l+1))
    (hl : 2^(41*t) ≤ l) (hl' : l < 2^(41*(t+1)))
    (hd : (390*t)*d ≤ l-1) (hd' : l-1 < (390*t)*(d+1)) :
    (2^(10*t))^4 ≤ l ∧ ((2^(10*t))^13)^(3*d) < x ∧
    ∀ n : ℕ, n ≤ (2^(10*t))^13 → (2^(10*t))^129 ≤ n^10 → ∃ M : ℕ,
      ((Nat.log 2 (x^2)+2)^((2^(10*t))^4+1))*M ≤ n.choose (3*d) ∧
      2*2^(3*d)*(n+1)^(2*d) < M ∧ 2*(2*K*x+1)*(n+1)^d < M^2 := by
  have mono {a b : ℕ} (h : a ≤ b) : 2^a ≤ 2^b := Nat.pow_le_pow_right (by decide) h
  have strict {a b : ℕ} (h : a < b) : 2^a < 2^b := Nat.pow_lt_pow_right (by decide) h
  have ll : 0<l := (Nat.two_pow_pos _).trans_le hl
  have hn40 : (2^(10*t))^4 = 2^(40*t) := by rw [←pow_mul]; congr 1 <;> ring
  have hn130 : (2^(10*t))^13 = 2^(130*t) := by rw [←pow_mul]; congr 1 <;> ring
  have hsmall := mono (show 40*t ≤ 41*t by omega)
  have ht41 : 2^(41*t) = 2^(40*t)*2^t := by rw [←pow_add,show 40*t+t=41*t by omega]
  have huge := Nat.mul_le_mul_left (2^(40*t)) (plenty ht)
  rw [←ht41] at huge
  have hbpos : 0 < 2^(40*t) := by positivity
  have htlow : 100*(2^(40*t)+1) ≤ d := by
    by_contra! bad
    have h := Nat.mul_le_mul_left (390*t) (show d+1 ≤ 100*(2^(40*t)+1) by omega)
    have aux := Nat.mul_le_mul_left t (show 1 ≤ 2^(40*t) by omega)
    nlinarith only [hd',h,hl,huge,Nat.sub_add_cancel ll,aux,hbpos]
  have ht2 : t < 2^(40*t) := by
    apply (Nat.lt_pow_self (by decide : 1<2)).trans_le
    exact mono (by omega)
  have hdpos : 0<d := by omega
  have hkl : 3*d ≤ l := by
    have hm := Nat.mul_le_mul_right d (show 3 ≤ 390*t by omega)
    omega
  have hupper : l < 2^(41*t+41) := by simpa only [Nat.mul_add,Nat.mul_one] using hl'
  have hlog : Nat.log 2 (x^2) ≤ 2*(l+1) := by
    have b := Nat.pow_le_pow_left hx'.le 2
    have h := Nat.log_mono_right (b := 2) b
    rw [←pow_mul,Nat.log_pow (by decide)] at h
    omega
  have hbase : Nat.log 2 (x^2)+2 ≤ 2^(42*t) := by
    have hm := mono (show 41*t+41+2 ≤ 42*t by omega)
    rw [pow_add] at hm
    norm_num only [Nat.reducePow] at hm
    omega
  refine ⟨hn40 ▸ hsmall.trans hl, ?_, ?_⟩
  · rw [hn130,←pow_mul]
    exact (strict (by nlinarith only [hd,Nat.sub_add_cancel ll])).trans_le hx
  intro n hnu hnl
  rw [hn130] at hnu
  have hnlo : 2^(129*t) ≤ n := by
    apply (Nat.pow_le_pow_iff_left (by decide : 10 ≠ 0)).mp
    convert hnl using 1 <;> rw [←pow_mul,←pow_mul] <;> congr 1 <;> ring
  let M := 2^((260*t+6)*d+2)
  refine ⟨M,?_,?_,?_⟩
  · have hbk : (2^(87*t)+1)*(3*d) ≤ n := by
      have h1 : 2^(87*t)+1 ≤ 2^(87*t+1) := by rw [pow_succ]; have := Nat.two_pow_pos (87*t); omega
      calc _ ≤ 2^(87*t+1)*2^(41*t+41) := Nat.mul_le_mul h1 (hkl.trans hupper.le)
           _ = 2^(87*t+1+(41*t+41)) := (pow_add ..).symm
           _ ≤ _ := (mono (by omega)).trans hnlo
    have choose := choose_blocks n (3*d) (2^(87*t)) hbk
    rw [←pow_mul] at choose
    rw [hn40]
    calc
      (Nat.log 2 (x^2)+2)^(2^(40*t)+1)*M ≤ (2^(42*t))^(2^(40*t)+1)*M :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbase _)
      _ = 2^((42*t)*(2^(40*t)+1)+((260*t+6)*d+2)) := by dsimp [M]; rw [←pow_mul,←pow_add]
      _ ≤ _ := (mono (by
        have h1 := Nat.mul_le_mul_left t htlow
        have h2 := Nat.mul_le_mul_right d ht
        nlinarith only [h1,h2,hdpos,htlow])).trans choose
  · have hn : n+1 ≤ 2^(130*t+1) := by rw [pow_succ]; have := Nat.two_pow_pos (130*t); omega
    calc 2*2^(3*d)*(n+1)^(2*d) ≤ 2*2^(3*d)*(2^(130*t+1))^(2*d) :=
           Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _)
         _ = 2^(3*d+1+(130*t+1)*(2*d)) := by rw [←pow_mul, pow_add (2:ℕ) (3*d+1),pow_succ (2:ℕ) (3*d)]; ring
         _ < M := strict (by nlinarith)
  · have hn : n+1 ≤ 2^(130*t+1) := by rw [pow_succ]; have := Nat.two_pow_pos (130*t); omega
    have kbound : K ≤ 2^t := hK.trans (Nat.lt_pow_self (by decide)).le
    have hh : 2*K*x+1 ≤ 2^(t+l+3) := by
      have hh := Nat.mul_le_mul kbound hx'.le
      rw [←pow_add] at hh
      have eq : 2^(t+l+3) = 2^(t+(l+1))*4 := by rw [show t+l+3 = t+(l+1)+2 by omega,pow_add]; norm_num
      rw [eq]
      have hpos := Nat.two_pow_pos (t+(l+1))
      nlinarith only [hh,hpos]
    calc 2*(2*K*x+1)*(n+1)^d ≤ 2*2^(t+l+3)*(2^(130*t+1))^d :=
           Nat.mul_le_mul (Nat.mul_le_mul_left _ hh) (Nat.pow_le_pow_left hn _)
         _ = 2^(t+l+3+1+(130*t+1)*d) := by rw [←pow_mul,pow_add (2:ℕ) (t+l+3+1),pow_succ (2:ℕ) (t+l+3)]; ring
         _ < 2^(((260*t+6)*d+2)*2) := strict (by
           have hlback := Nat.sub_add_cancel ll
           nlinarith only [hd',hlback,ht2,htlow])
         _ = _ := by rw [pow_mul]

end OMA.PollackScale

theorem OMA.solution : OMA.R_Erdos824_erdos_824_variants_pollack_pomerance_R1.H2 := by
  intro K Y
  let T := max 100 (max K Y)
  filter_upwards [Filter.eventually_ge_atTop ((2:ℕ)^(2^(41*T)))] with x hx
  let l := Nat.log 2 x
  let t := Nat.log 2 l / 41
  let d := (l-1)/(390*t)
  have hx0 : x ≠ 0 := (lt_of_lt_of_le (by positivity) hx).ne'
  have hlT : 2^(41*T) ≤ l := (Nat.le_log_iff_pow_le (by decide) hx0).mpr hx
  have hl0 : l ≠ 0 := (lt_of_lt_of_le (by positivity) hlT).ne'
  have hlt : 41*T ≤ Nat.log 2 l := (Nat.le_log_iff_pow_le (by decide) hl0).mpr hlT
  have htT : T ≤ t := by dsimp only [t]; omega
  have ht : 100 ≤ t := (le_max_left ..).trans htT
  have hK : K ≤ t := (le_max_left K Y).trans ((le_max_right ..).trans htT)
  have hY : Y ≤ t := (le_max_right K Y).trans ((le_max_right ..).trans htT)
  have htlo : 41*t ≤ Nat.log 2 l := by dsimp only [t]; omega
  have hthi : Nat.log 2 l+1 ≤ 41*(t+1) := by dsimp only [t]; omega
  have hd : (390*t)*d ≤ l-1 := by
    simpa [d,mul_comm] using Nat.div_mul_le_self (l-1) (390*t)
  have hd' : l-1 < (390*t)*(d+1) := by
    rw [Nat.mul_comm (390*t)]
    apply (Nat.div_lt_iff_lt_mul (show 0 < 390*t by omega)).mp
    exact Nat.lt_succ_self d
  have h := OMA.PollackScale.numeric K x l t d ht hK (Nat.pow_log_le_self 2 hx0)
    (Nat.lt_pow_succ_log_self (by decide) x)
    ((Nat.le_log_iff_pow_le (by decide) hl0).mp htlo)
    ((Nat.lt_pow_succ_log_self (by decide : 1 < 2) l).trans_le
      (Nat.pow_le_pow_right (by decide) hthi)) hd hd'
  exact ⟨2^(10*t),d,hY.trans ((Nat.lt_pow_self (by decide : 1 < 2)).le.trans
    (Nat.pow_le_pow_right (by decide) (by omega))),h⟩
