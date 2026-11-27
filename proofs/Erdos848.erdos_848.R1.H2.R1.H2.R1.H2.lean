import OMAReductions.R_Erdos848_erdos_848_R1_H2_R1_H2_R1
import Mathlib

/-! For a fixed crossed residue class modulo 25 the square factor 5²
never occurs. We sum the other prime square densities and use the primorial
bound to control the one-point rounding errors. The two elementary ZMod
lemmas are adapted from MacchaCat/erdos848 at
99b8d9bf40fdd090a2a117328c5707ca21ec748e, Apache-2.0. -/
namespace OMA.E848CrossSieve
open Finset
lemma exists_prime_sq_dvd {n : ℕ} (h : ¬ Squarefree n) : ∃ p, p.Prime ∧ p * p ∣ n := by
  rw [Nat.squarefree_iff_prime_squarefree] at h
  push Not at h
  obtain ⟨p, hp, hd⟩ := h
  exact ⟨p, hp, hd⟩

/-- If a prime divides `b`, its square cannot divide `ab + 1`. -/
lemma not_sq_dvd_of_dvd {p a b : ℕ} (hp : p.Prime) (hpb : p ∣ b) : ¬ p * p ∣ a * b + 1 := by
  intro h
  have h1 : p ∣ a * b + 1 := dvd_trans (Dvd.intro p rfl) h
  have h2 : p ∣ a * b := dvd_mul_of_dvd_right hpb a
  have : p ∣ 1 := (Nat.dvd_add_right h2).mp h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- (F5) For a prime `p ∤ b` there is a residue `c < p²` with
`p² ∣ ab+1 ↔ a ≡ c (mod p²)`. -/
lemma prime_sq_dvd_mul_add_one_iff {p b : ℕ} (hp : p.Prime) (hpb : ¬ p ∣ b) :
    ∃ c < p * p, ∀ a, p * p ∣ a * b + 1 ↔ a % (p * p) = c := by
  have hpp : 0 < p * p := Nat.mul_pos hp.pos hp.pos
  have hcop : Nat.Coprime b (p * p) :=
    Nat.Coprime.mul_right ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb)))
      ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb)))
  -- let u be the inverse of b mod p²; c = (p² - 1) * u mod p²  (i.e. -b⁻¹)
  set u := ((ZMod.unitOfCoprime b hcop)⁻¹ : (ZMod (p * p))ˣ)
  set c := ((-(u : ZMod (p * p))).val) with hc
  have : NeZero (p * p) := ⟨hpp.ne'⟩
  refine ⟨c, ZMod.val_lt _, fun a => ?_⟩
  have hb : ((b : ZMod (p * p)) * (u : ZMod (p * p))) = 1 := by
    have := Units.mul_inv (ZMod.unitOfCoprime b hcop)
    simp [u, ZMod.coe_unitOfCoprime] at this ⊢
  rw [← ZMod.natCast_eq_zero_iff]   -- p² ∣ ab+1 ↔ (ab+1 : ZMod p²) = 0
  constructor
  · intro h
    have h' : ((a : ZMod (p * p)) * b + 1) = 0 := by exact_mod_cast h
    have : (a : ZMod (p * p)) = -(u : ZMod (p * p)) := by
      have := congrArg (· * (u : ZMod (p * p))) h'
      simp only [add_mul, zero_mul, one_mul, mul_assoc, hb, mul_one] at this
      exact eq_neg_of_add_eq_zero_left this
    rw [hc, ← this, ZMod.val_natCast]
  · intro h
    have : (a : ZMod (p * p)) = -(u : ZMod (p * p)) := by
      rw [← ZMod.natCast_mod a (p * p), h, hc, ZMod.natCast_zmod_val]
    push_cast
    rw [this, neg_mul, mul_comm (u : ZMod (p * p)) (b : ZMod (p * p)), hb, neg_add_cancel]

lemma primes_sparse (N : ℕ) (hN : 2^2300≤N) : 1000*(Nat.primesLE N).card ≤ N := by
  let S := (Nat.primesLE N).filter (fun p => p<2^2048)
  let L := (Nat.primesLE N).filter (fun p => ¬p<2^2048)
  have small : S.card ≤ 2^2048 := by
    rw [←card_range (2^2048)]
    exact card_le_card (fun p hp => mem_range.mpr (mem_filter.mp hp).2)
  have bound : (2^2048 : ℕ)^L.card ≤ 4^N := calc
    _ = ∏ _ ∈ L, (2^2048 : ℕ) := by simp
    _ ≤ ∏ p ∈ L, p := prod_le_prod' (fun p hp => Nat.le_of_not_gt (mem_filter.mp hp).2)
    _ ≤ ∏ p ∈ Nat.primesLE N,p := by
      exact prod_le_prod_of_subset_of_one_le' (filter_subset _ _)
        (fun p hp _ => (Nat.prime_of_mem_primesLE hp).one_lt.le)
    _ = primorial N := (primorial_eq_prod_primesLE N).symm
    _ ≤ 4^N := primorial_le_four_pow _
  have exp : 2048*L.card ≤ 2*N := by
    apply (pow_le_pow_iff_right₀ (by decide : 1<(2:ℕ))).mp
    simpa only [pow_mul, show (2:ℕ)^2=4 by decide] using bound
  have count : S.card+L.card=(Nat.primesLE N).card := card_filter_add_card_filter_not _
  have hhuge : 64000*2^2048≤N := le_trans (by decide +kernel) hN
  omega

def weight (n : ℕ) : ℚ :=
  if n<16 then if n∈([2,3,7,11,13] : List ℕ) then 1/(n:ℚ)^2 else 0
  else 1/((n:ℚ)-1)-1/(n:ℚ)

lemma weight_pos (n : ℕ) : 0≤weight n := by
  unfold weight; split
  · split <;> positivity
  · next h =>
      have hn : (16:ℚ)≤n := by exact_mod_cast (Nat.le_of_not_gt h)
      exact sub_nonneg.mpr (one_div_le_one_div_of_le (by linarith) (by linarith))

lemma weight_prime (p : ℕ) (hp : p.Prime) (ne : p≠5) : 1/(p:ℚ)^2 ≤ weight p := by
  by_cases h : p<16
  · have all : ∀ q : Fin 16, q.val.Prime → q.val≠5 → q.val∈([2,3,7,11,13] : List ℕ) := by decide +kernel
    simp [weight,h,all ⟨_,h⟩ hp ne]
  · have hp' : (16:ℚ)≤p := by exact_mod_cast (Nat.le_of_not_gt h)
    rw [weight,if_neg h]
    have pos : 0<(p:ℚ) := by linarith
    have pos' : 0<(p:ℚ)-1 := by linarith
    field_simp
    nlinarith [sq_nonneg (p:ℚ)]

lemma weights (N : ℕ) (hN : 16≤N) : ∑ n ∈ range N, weight n ≤ 47/100 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hN
  have eqn (k : ℕ) : ∑ n ∈ range (16+k),weight n =
      (∑ n ∈ range 16,weight n)+1/15-1/(15+(k:ℚ)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 16+(k+1)=16+k+1 by omega,sum_range_succ,ih,weight,if_neg (by omega)]
      push_cast; ring_nf
  rw [eqn]
  have b : (∑ n ∈ range 16,weight n)+1/15≤47/100 := by decide +kernel
  linarith [show 0≤1/(15+(k:ℚ)) by positivity]

lemma residue (N b r p : ℕ) (hp : p.Prime) (no5 : p≠5) :
    (((Icc 1 N).filter (fun a => a%25=r ∧ p*p∣a*b+1)).card : ℚ) ≤
      (N:ℚ)/25*(1/(p:ℚ)^2)+1 := by
  by_cases d : p∣b
  · have empty : ((Icc 1 N).filter (fun a => a%25=r ∧ p*p∣a*b+1))=∅ := by
      apply eq_empty_iff_forall_notMem.mpr; intro a ha
      exact not_sq_dvd_of_dvd hp d (mem_filter.mp ha).2.2
    rw [empty]; simp; positivity
  obtain ⟨c,_,hc⟩ := prime_sq_dvd_mul_add_one_iff hp d
  let M := 25*(p*p)
  have cop : Nat.Coprime 25 (p*p) := by
    have opp := (Nat.coprime_primes (by decide : Nat.Prime 5) hp).mpr no5.symm
    simpa only [show 25=5*5 by decide] using
      (opp.mul_left opp).mul_right (opp.mul_left opp)
  have C : ((Icc 1 N).filter (fun a => a%25=r ∧ p*p∣a*b+1)).card ≤ N/M+1 := by
    rw [←card_range (N/M+1)]
    apply card_le_card_of_injOn (fun a => a/M)
    · intro a ha
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp ha).1).2))
    · intro a ha z hz e
      obtain ⟨_,ra,da⟩ := mem_filter.mp ha
      obtain ⟨_,rz,dz⟩ := mem_filter.mp hz
      have mm : a % M=z % M := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp
        ⟨ra.trans rz.symm,((hc a).mp da).trans ((hc z).mp dz).symm⟩
      change a/M=z/M at e
      rw [←Nat.div_add_mod a M,←Nat.div_add_mod z M,e,mm]
  have Mpos : 0<(M:ℚ) := by exact_mod_cast (Nat.mul_pos (show 0<25 by decide) (Nat.mul_pos hp.pos hp.pos))
  have dv : (↑(N/M):ℚ)≤(N:ℚ)/M := by
    apply (le_div_iff₀ Mpos).mpr; exact_mod_cast Nat.div_mul_le_self N M
  calc
    _ ≤ (↑(N/M):ℚ)+1 := by exact_mod_cast C
    _ ≤ (N:ℚ)/M+1 := by linarith
    _ = _ := by dsimp [M]; push_cast; ring_nf

lemma one_class (N b r : ℕ) (hN : 2^2300≤N) (hb : b≤N)
    (cross : ∀ a : ℕ, a%25=r → ¬25∣a*b+1) :
    (((Icc 1 N).filter (fun a => a%25=r ∧ ¬Squarefree (a*b+1))).card : ℚ) ≤
      (N:ℚ)/25*(47/100)+(N:ℚ)/1000 := by
  classical
  let S := (Nat.primesLE N).erase 5
  let C (p : ℕ) := (Icc 1 N).filter (fun a => a%25=r ∧ p*p∣a*b+1)
  have cover : (Icc 1 N).filter (fun a => a%25=r ∧ ¬Squarefree (a*b+1)) ⊆ S.biUnion C := by
    intro a ha
    obtain ⟨ha,hr,hb'⟩ := mem_filter.mp ha
    obtain ⟨p,hp,hd⟩ := exists_prime_sq_dvd hb'
    have ne : p≠5 := by rintro rfl; exact cross a hr hd
    have small : p≤N := by
      have bound := Nat.le_of_dvd (Nat.succ_pos _) hd
      have lo := Nat.mul_le_mul (mem_Icc.mp ha).2 hb
      by_contra! hh
      have prod := Nat.mul_le_mul (show N+1≤p by omega) (show N+1≤p by omega)
      have nz : 1≤N := (show 1≤2^2300 by decide +kernel).trans hN
      change p*p ≤ a*b+1 at bound
      have gap : N*N+1 < (N+1)*(N+1) := by
        simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
        omega
      omega
    exact mem_biUnion.mpr ⟨p,mem_erase.mpr ⟨ne,Nat.mem_primesLE.mpr ⟨small,hp⟩⟩,mem_filter.mpr ⟨ha,hr,hd⟩⟩
  have val (p : ℕ) (hp : p∈S) : ((C p).card:ℚ) ≤ (N:ℚ)/25*weight p+1 := by
    obtain ⟨ne,mem⟩ := mem_erase.mp hp
    have prime := Nat.prime_of_mem_primesLE mem
    exact (residue N b r p prime ne).trans (by gcongr; exact weight_prime p prime ne)
  have big : 16≤N+1 := by have := le_trans (show 16≤2^2300 by decide +kernel) hN; omega
  have ss : ∑ p ∈ S,weight p ≤ 47/100 := le_trans
    (sum_le_sum_of_subset_of_nonneg (s:=S) (t:=range (N+1))
      (fun p hp => mem_range.mpr (Nat.lt_succ_of_le (Nat.mem_primesLE.mp (mem_erase.mp hp).2).1))
      (fun p _ _ => weight_pos p)) (weights (N+1) big)
  have pc : (S.card:ℚ)≤(N:ℚ)/1000 := by
    have h := le_trans (Nat.mul_le_mul_left 1000 (card_le_card (erase_subset 5 (Nat.primesLE N)))) (primes_sparse N hN)
    have h' : 1000*(S.card:ℚ)≤(N:ℚ) := by exact_mod_cast h
    linarith
  calc
    _ ≤ (∑ p ∈ S, ((C p).card:ℚ)) := by exact_mod_cast (card_le_card cover).trans card_biUnion_le
    _ ≤ ∑ p ∈ S, ((N:ℚ)/25*weight p+1) := sum_le_sum val
    _ = (N:ℚ)/25*(∑ p ∈ S, weight p)+S.card := by simp [sum_add_distrib,mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left ss (by positivity)) pc

end OMA.E848CrossSieve

open OMA.E848CrossSieve Finset in
theorem OMA.solution : OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1.H2 := by
  intro N hN
  dsimp only
  intro b b' hb h7 hb' h18
  have h1 := one_class N b 18 hN (mem_Icc.mp hb.1).2 (fun a ha => by
    rw [Nat.dvd_iff_mod_eq_zero,Nat.add_mod,Nat.mul_mod,ha,h7]; decide)
  have h2 := one_class N b' 7 hN (mem_Icc.mp hb'.1).2 (fun a ha => by
    rw [Nat.dvd_iff_mod_eq_zero,Nat.add_mod,Nat.mul_mod,ha,h18]; decide)
  let c := ((Icc 1 N).filter (fun a => a%25=7)).card
  have lb : N/25 ≤ c := by
    rw [←card_range (N/25)]
    apply card_le_card_of_injOn (fun i => 25*i+7)
    · intro i hi
      have h := mem_range.mp hi
      apply mem_filter.mpr
      change 25*i+7 ∈ Icc 1 N ∧ (25*i+7)%25=7
      exact ⟨mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
    · intro i _ j _ h; change 25*i+7=25*j+7 at h; omega
  have hfloor : N ≤ 25*c+24 := by omega
  have hf : (N:ℚ) ≤ 25*(c:ℚ)+24 := by exact_mod_cast hfloor
  have hbig : (100000:ℚ)≤N := by exact_mod_cast (le_trans (show 100000≤2^2300 by decide +kernel) hN)
  exact_mod_cast (show (((Icc 1 N).filter (fun a => a%25=18 ∧ ¬Squarefree (a*b+1))).card:ℚ)+
    (((Icc 1 N).filter (fun a => a%25=7 ∧ ¬Squarefree (a*b'+1))).card:ℚ) ≤ (c:ℚ) by linarith)
