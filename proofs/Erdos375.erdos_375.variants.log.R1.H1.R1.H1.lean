import OMAReductions.R_Erdos375_erdos_375_variants_log_R1_H1_R1

/-! For each prime, assign a row where its valuation is largest. The powers
at every other row divide its distance to that row. Distinct prime powers
are coprime, so their full product divides the factorial. -/
open Finset

private lemma product_dist {k : ℕ} (j:Fin k) (S:Finset (Fin k)) :
    (∏ i∈S, (if i.val<j.val then j.val-i.val else if j.val < i.val then i.val-j.val else 1)) ∣ k.factorial := by
  classical
  let L := S.filter (fun i => i.val<j.val)
  let R := S.filter (fun i => j.val < i.val)
  have injL : Set.InjOn (fun i:Fin k => j.val-i.val) ↑L := by
    intro i hi i' hi' e
    have h := (mem_filter.mp hi).2
    have h' := (mem_filter.mp hi').2
    apply Fin.ext
    dsimp at e
    omega
  have injR : Set.InjOn (fun i:Fin k => i.val-j.val) ↑R := by
    intro i hi i' hi' e
    have h := (mem_filter.mp hi).2
    have h' := (mem_filter.mp hi').2
    apply Fin.ext
    dsimp at e
    omega
  have lsub : L.image (fun i => j.val-i.val) ⊆ Icc 1 j.val := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    have := (mem_filter.mp hi).2
    exact mem_Icc.mpr ⟨by omega,Nat.sub_le ..⟩
  have rsub : R.image (fun i => i.val-j.val) ⊆ Icc 1 (k-j.val) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    have := (mem_filter.mp hi).2
    have := i.isLt
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have left := prod_dvd_prod_of_subset _ _ id lsub
  have right := prod_dvd_prod_of_subset _ _ id rsub
  have prodI (n:ℕ) : ∏ i∈Icc 1 n,id i=n.factorial := by
    have e : Icc 1 n=Ico 1 (n+1) := by ext i; simp
    rw [e]; exact prod_Ico_id_eq_factorial n
  rw [prod_image injL,prodI] at left
  rw [prod_image injR,prodI] at right
  have eq : (∏ i∈S, (if i.val<j.val then j.val-i.val else if j.val < i.val then i.val-j.val else 1)) =
       (∏ i∈L, (j.val-i.val))*(∏ i∈R,(i.val-j.val)) := by
    dsimp only [L,R]
    rw [prod_filter,prod_filter,←prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    by_cases h:i.val<j.val <;> simp [h,show i.val<j.val → ¬j.val < i.val from fun a => a.asymm]
  rw [eq]
  exact (Nat.mul_dvd_mul left right).trans (Nat.factorial_mul_factorial_dvd_factorial j.isLt.le)

private lemma off_max {n k p:ℕ} (_hp:p.Prime) (J:Finset (Fin k)) (j:Fin k)
    (maxi:∀ i∈J, (n+i.val+1).factorization p ≤ (n+j.val+1).factorization p) :
    (∏ i∈J, p^(if i=j then 0 else (n+i.val+1).factorization p)) ∣ k.factorial := by
  apply dvd_trans _ (product_dist j J)
  apply prod_dvd_prod_of_dvd
  intro i hi
  by_cases eq:i=j
  · simp [eq]
  rw [if_neg eq]
  have dl := Nat.ordProj_dvd (n+i.val+1) p
  have dr : p^(n+i.val+1).factorization p ∣ n+j.val+1 :=
    (pow_dvd_pow _ (maxi i hi)).trans (Nat.ordProj_dvd _ _)
  by_cases lt:i.val<j.val
  · rw [if_pos lt]
    have h := Nat.dvd_sub dr dl
    rwa [show n+j.val+1-(n+i.val+1)=j.val-i.val by omega] at h
  · have gt : j.val < i.val := by have ne : i.val≠j.val := fun h => eq (Fin.ext h); omega
    rw [if_neg lt,if_pos gt]
    have h := Nat.dvd_sub dl dr
    rwa [show n+i.val+1-(n+j.val+1)=i.val-j.val by omega] at h

theorem OMA.solution : OMA.R_Erdos375_erdos_375_variants_log_R1_H1_R1.H1 := by
  classical
  intro n k J P deficit small
  have jne : J.Nonempty := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) deficit)
  let w (i:Fin k) := n+i.val+1
  have wp (i:Fin k) : 0<w i := Nat.succ_pos _
  let e (i:Fin k) (p:ℕ) := (w i).factorization p
  have ex (p:ℕ) := J.exists_max_image (fun i => e i p) jne
  choose f fj mx using ex
  let F (i:Fin k) := P.filter (fun p => f p=i)
  let Z := J.filter (fun i => (F i).card=0)
  let B := J.filter (fun i => (F i).card=1)
  have pprime (p:ℕ) (hp:p∈P) : p.Prime := by
    obtain ⟨i,_,h⟩ := mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors h
  have psum : ∑ i∈J,(F i).card = P.card := (card_eq_sum_card_fiberwise (f:=f) (s:=P) (t:=J) (fun p _ => fj p)).symm
  have count : J.card ≤ 2*Z.card+B.card := by
    have point (i:Fin k) : 2≤(F i).card+2*(if (F i).card=0 then 1 else 0)+(if (F i).card=1 then 1 else 0) := by split_ifs <;> omega
    have h := sum_le_sum (s:=J) (fun i _ => point i)
    rw [sum_add_distrib,sum_add_distrib,←mul_sum,psum] at h
    simp only [sum_const,nsmul_eq_mul] at h
    have z : ∑ i∈J,(if (F i).card=0 then 1 else 0) = Z.card := (card_filter ..).symm
    have b : ∑ i∈J,(if (F i).card=1 then 1 else 0) = B.card := (card_filter ..).symm
    rw [z,b] at h
    change J.card*2 ≤ P.card+2*Z.card+B.card at h
    omega
  let v (i:Fin k) (p:ℕ) := if i=f p then 0 else e i p
  let u (i:Fin k) := ∏ p∈P,p^(v i p)
  have u0 (i:Fin k) : 0<u i := prod_pos fun p hp => pow_pos (pprime p hp).pos _
  have all : ∏ i∈J,u i ∣ k.factorial := by
    change (∏ i∈J,∏ p∈P,p^(v i p)) ∣ _
    rw [prod_comm]
    apply prod_dvd_of_isRelPrime
    · intro p hp q hq pq
      apply Nat.coprime_iff_isRelPrime.mp
      apply Nat.Coprime.prod_left
      intro i _
      apply Nat.Coprime.prod_right
      intro j _
      exact (((pprime p hp).coprime_iff_not_dvd.mpr (fun h => pq (((Nat.dvd_prime (pprime q hq)).mp h).resolve_left (pprime p hp).ne_one))).pow_left _).pow_right _
    · intro p hp
      exact off_max (pprime p hp) J (f p) (mx p)
  have bound (T:Finset (Fin k)) (hT:T⊆J) : ∏ i∈T,u i ≤ k.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos k) ((prod_dvd_prod_of_subset _ _ u hT).trans all)
  let remn (i:Fin k) := ∏ p∈P,p^(if i=f p then e i p else 0)
  have split (i:Fin k) (hi:i∈J) : w i = u i*remn i := by
    have sub : (w i).primeFactors⊆P := fun p hp => mem_biUnion.mpr ⟨i,hi,hp⟩
    have prod : ∏ p∈P, p^(e i p) = w i := by
      apply Eq.trans _ (Nat.prod_primeFactors_pow_factorization (wp i).ne').symm
      change ∏ p∈P, p^(e i p) = ∏ p∈(w i).primeFactors,p^(e i p)
      symm
      apply prod_subset sub
      intro p _ hp
      have z : (w i).factorization p=0 := by
        simpa only [←Finsupp.notMem_support_iff,Nat.support_factorization] using hp
      simp [e,z]
    rw [←prod]
    dsimp only [u,remn]
    rw [←prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    by_cases eq:i=f p <;> simp [v,eq]
  have zero (i:Fin k) (hi:i∈Z) : n+1≤u i := by
    obtain ⟨ij,empty⟩ := mem_filter.mp hi
    have no (p:ℕ) (hp:p∈P) : i≠f p := by
      intro eq
      have h : p∈F i := mem_filter.mpr ⟨hp,eq.symm⟩
      rw [card_eq_zero.mp empty] at h
      exact notMem_empty _ h
    have r : remn i=1 := prod_eq_one (fun p hp => by simp [no p hp])
    have e := split i ij
    rw [r,mul_one] at e
    dsimp [w] at e
    omega
  have get (i:Fin k) (hi:i∈B) : ∃ q:ℕ,F i={q} := card_eq_one.mp (mem_filter.mp hi).2
  let p (i:Fin k) := if h:i∈B then (get i h).choose else 0
  have singleton (i:Fin k) (hi:i∈B) : F i={p i} := by simpa [p,hi] using (get i hi).choose_spec
  have member (i:Fin k) (hi:i∈B) : p i∈P ∧ f (p i)=i := by
    have h : p i∈F i := by rw [singleton i hi]; simp
    exact mem_filter.mp h
  refine ⟨Z.card,B,p,fun i => e i (p i),u,filter_subset ..,count,?_,bound B (filter_subset ..),?_,?_⟩
  · calc (n+1)^Z.card = ∏ i∈Z,(n+1) := (prod_const _).symm
         _ ≤ ∏ i∈Z,u i := prod_le_prod' (fun i hi => zero i hi)
         _ ≤ _ := bound Z (filter_subset ..)
  · intro i hi j hj eq
    exact (member i hi).2.symm.trans ((congrArg f eq).trans (member j hj).2)
  · intro i hi
    refine ⟨pprime _ (member i hi).1,small _ (member i hi).1,u0 i,?_⟩
    have r : remn i=(p i)^(e i (p i)) := by
      dsimp [remn]
      rw [prod_eq_single_of_mem (p i) (member i hi).1 (fun q hq ne => ?_),if_pos (member i hi).2.symm]
      have no : i≠f q := by
        intro eq
        have h : q∈F i := mem_filter.mpr ⟨hq,eq.symm⟩
        rw [singleton i hi] at h
        exact ne (mem_singleton.mp h)
      simp [no]
    exact (split i (mem_filter.mp hi).1).trans (congrArg (u i * ·) r)
