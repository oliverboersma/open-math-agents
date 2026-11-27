import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1

-- Reduction Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1 of step Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1
-- Credit: @marcusbuffett

namespace OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1

open Filter Finset Real

private lemma square_mod {t : ℕ} (ht : t%2=1) : t^2 % 8 = 1 := by
  have h := Nat.mod_lt t (by decide : 0 < 8)
  have e := Nat.pow_mod t 2 8
  interval_cases h' : t%8 <;> simp_all <;> omega

private lemma split_mod {t s : ℕ} (h : (t^2*s)%8=3) : t%2=1 ∧ s%8=3 := by
  have ht : t%2=1 := by
    by_contra hn
    have e : t%2=0 := by omega
    have h' : (t^2*s)%2=0 := by simp [pow_two, Nat.mul_mod, e]
    omega
  refine ⟨ht, ?_⟩
  rwa [Nat.mul_mod, square_mod ht, one_mul, Nat.mod_mod] at h

private lemma square_growth (R : ℕ → ℕ)
    (hb : ∀ p n : ℕ, p.Prime → p%2=1 → n%8=3 → ¬p^2 ∣ n → p*R n ≤ R (p^2*n))
    (hr : ∀ p n : ℕ, p.Prime → p%2=1 → n%8=3 →
      (p+1)*R (p^2*n) ≤ R (p^4*n)+p*R n)
    {s : ℕ} (hs : s%8=3) : ∀ t : ℕ, t%2=1 → t*R s ≤ R (t^2*s) := by
  have step (p : ℕ) (hp : p.Prime) (ho : p%2=1) : ∀ n : ℕ, n%8=3 → p*R n ≤ R (p^2*n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hd : p^2 ∣ n
      · obtain ⟨m, rfl⟩ := hd
        have hm := (split_mod hn).2
        have hmpos : 0 < m := by omega
        have hpp := hp.two_le
        have hlt : m < p^2*m := by nlinarith [Nat.mul_self_le_mul_self hpp, Nat.mul_le_mul_right m (Nat.mul_self_le_mul_self hpp)]
        have hprev := ih m hlt hm
        have hrec := hr p m hp ho hm
        rw [show p^2*(p^2*m)=p^4*m by ring]
        nlinarith only [hprev, hrec]
      · exact hb p n hp ho hn hd
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    by_cases ht1 : t=1
    · simp [ht1]
    have htp : 0<t := by omega
    let p := t.minFac
    have hp : p.Prime := Nat.minFac_prime ht1
    obtain ⟨u, he⟩ := Nat.minFac_dvd t
    change t=p*u at he
    have hpu := Nat.mul_mod p u 2
    have ho : p%2=1 := by
      by_contra h
      have hz : p%2=0 := by omega
      rw [he, hpu] at ht
      simp [hz] at ht
    have hu : u%2=1 := by
      by_contra h
      have hz : u%2=0 := by omega
      rw [he, hpu] at ht
      simp [hz] at ht
    have hut : u<t := by have := hp.two_le; obtain rfl | hupos := Nat.eq_zero_or_pos u <;> nlinarith
    have hmod : (u^2*s)%8=3 := by rw [Nat.mul_mod, square_mod hu, one_mul, Nat.mod_mod, hs]
    calc
      t*R s = p*(u*R s) := by rw [he, Nat.mul_assoc]
      _ ≤ p*R (u^2*s) := Nat.mul_le_mul_left p (ih u hut hu)
      _ ≤ R (p^2*(u^2*s)) := step p hp ho _ hmod
      _ = R (t^2*s) := by rw [he]; congr 1; ring

def H1 : Prop :=
  let B := fun s : ℕ => (((range (s+1)) ×ˢ ((range (s+1)) ×ˢ (range (s+1)))).filter (fun v : ℕ × ℕ × ℕ => 0 < v.1 ∧ v.2.1 ≤ v.1 ∧ v.1 ≤ v.2.2 ∧ 4*v.1*v.2.2 = s+v.2.1^2)).card
  ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, 0 < s → Squarefree s → s % 8 = 3 →
    C * (s : ℝ) ^ (3/8 : ℝ) ≤ B s

def H2 : Prop :=
  let B := fun s : ℕ => (((range (s+1)) ×ˢ ((range (s+1)) ×ˢ (range (s+1)))).filter (fun v : ℕ × ℕ × ℕ => 0 < v.1 ∧ v.2.1 ≤ v.1 ∧ v.1 ≤ v.2.2 ∧ 4*v.1*v.2.2 = s+v.2.1^2)).card
  let R := fun n : ℕ => (((range (n+1)) ×ˢ ((range (n+1)) ×ˢ (range (n+1)))).filter (fun v : ℕ × ℕ × ℕ => v.1^2 + v.2.1^2 + v.2.2^2 = n)).card
  ∀ s : ℕ, 0 < s → Squarefree s → s % 8 = 3 → B s ≤ R s

def H3 : Prop :=
  let R := fun n : ℕ => (((range (n+1)) ×ˢ ((range (n+1)) ×ˢ (range (n+1)))).filter (fun v : ℕ × ℕ × ℕ => v.1^2 + v.2.1^2 + v.2.2^2 = n)).card
  ∀ p n : ℕ, p.Prime → p % 2 = 1 → n % 8 = 3 → ¬ p^2 ∣ n →
    p * R n ≤ R (p^2*n)

def H4 : Prop :=
  let R := fun n : ℕ => (((range (n+1)) ×ˢ ((range (n+1)) ×ˢ (range (n+1)))).filter (fun v : ℕ × ℕ × ℕ => v.1^2 + v.2.1^2 + v.2.2^2 = n)).card
  ∀ p n : ℕ, p.Prime → p % 2 = 1 → n % 8 = 3 →
    (p+1)*R (p^2*n) ≤ R (p^4*n)+p*R n

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1.H1 := by
  intro h1 h2 h3 h4
  let R := fun n : ℕ => (((range (n+1)) ×ˢ ((range (n+1)) ×ˢ (range (n+1)))).filter (fun v : ℕ × ℕ × ℕ => v.1^2 + v.2.1^2 + v.2.2^2 = n)).card
  let B := fun s : ℕ => (((range (s+1)) ×ˢ ((range (s+1)) ×ˢ (range (s+1)))).filter (fun v : ℕ × ℕ × ℕ => 0 < v.1 ∧ v.2.1 ≤ v.1 ∧ v.1 ≤ v.2.2 ∧ 4*v.1*v.2.2 = s+v.2.1^2)).card
  obtain ⟨C, hC, hB⟩ := h1
  change ∀ s : ℕ, 0<s → Squarefree s → s%8=3 → C*(s:ℝ)^(3/8:ℝ) ≤ B s at hB
  change ∀ s : ℕ, 0<s → Squarefree s → s%8=3 → B s ≤ R s at h2
  have hlim : Tendsto (fun m : ℕ => (((8*m+3 : ℕ) : ℝ)) ^ (3/40:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun m : ℕ => show m ≤ 8*m+3 by omega) tendsto_id))
  filter_upwards [hlim.eventually_gt_atTop (1/C)] with m hm
  let N := 8*m+3
  change (N:ℝ)^(3/10:ℝ) < (R N:ℝ)
  have hn : 0<N := by dsimp [N]; omega
  have hn8 : N%8=3 := by dsimp [N]; omega
  obtain ⟨s,t,hs,ht,he,hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hmod := split_mod (he ▸ hn8 : (t^2*s)%8=3)
  have hR : t*R s ≤ R N := he ▸ square_growth R h3 h4 hmod.2 t hmod.1
  have hsR := (hB s hs hsq hmod.2).trans (Nat.cast_le.mpr (h2 s hs hsq hmod.2))
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hsplit : (N:ℝ)^(3/8:ℝ) ≤ (t:ℝ)*(s:ℝ)^(3/8:ℝ) := by
    rw [← he, Nat.cast_mul, Nat.cast_pow, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast (t:ℝ) 2, ← Real.rpow_mul (by positivity)]
    gcongr
    simpa only [Nat.cast_ofNat, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le ht' (show (2:ℝ)*(3/8) ≤ 1 by norm_num)
  have hn' : 0<(N:ℝ) := by exact_mod_cast hn
  change 1/C < (N:ℝ)^(3/40:ℝ) at hm
  have hc := (div_lt_iff₀ hC).mp hm
  calc
    (N:ℝ)^(3/10:ℝ) = (N:ℝ)^(3/10:ℝ)*1 := by ring
    _ < (N:ℝ)^(3/10:ℝ)*((N:ℝ)^(3/40:ℝ)*C) := mul_lt_mul_of_pos_left hc (Real.rpow_pos_of_pos hn' _)
    _ = C*(N:ℝ)^(3/8:ℝ) := by rw [← mul_assoc, ← Real.rpow_add hn']; norm_num; ring
    _ ≤ C*((t:ℝ)*(s:ℝ)^(3/8:ℝ)) := mul_le_mul_of_nonneg_left hsplit hC.le
    _ = (t:ℝ)*(C*(s:ℝ)^(3/8:ℝ)) := by ring
    _ ≤ (t:ℝ)*(R s:ℝ) := mul_le_mul_of_nonneg_left hsR (by positivity)
    _ ≤ (R N:ℝ) := by exact_mod_cast hR

end OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1
