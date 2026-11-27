import OMAStatements.S_oeis_a292728
import Mathlib.Tactic

-- Problem: A292728: a(n) is the number of terminal states that can be achieved via the following algorithm: start with n piles each containing one sto
-- Upstream: formal-conjectures statements/oeis-a292728.lean:0 (declaration OMA.S_oeis_a292728.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA_A292728

open OMA.S_oeis_a292728

private def phi (s : Multiset ℕ) : ℕ := (s.map (fun x => x * x)).sum

private lemma position_card_le {n : ℕ} {s : Multiset ℕ} (hs : position n s) : s.card ≤ n := by
  have h1 : s.card = (s.map (fun _ => (1 : ℕ))).sum := by simp
  have h2 : (s.map (fun _ => (1 : ℕ))).sum ≤ s.sum := by
    have hle : ∀ x ∈ s, 1 ≤ x := fun x hx => hs.2 x hx
    clear h1 hs
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      have ha : 1 ≤ a := hle a (Multiset.mem_cons_self a t)
      have ht : (t.map (fun _ => (1 : ℕ))).sum ≤ t.sum :=
        ih (fun x hx => hle x (Multiset.mem_cons_of_mem hx))
      omega
  have hsum := hs.1
  omega

private lemma position_le_of_mem {n : ℕ} {s : Multiset ℕ} (hs : position n s) {x : ℕ}
    (hx : x ∈ s) : x ≤ n := by
  rw [← hs.1]
  exact Multiset.le_sum_of_mem hx

private lemma finite_position (n : ℕ) : {s : Multiset ℕ | position n s}.Finite := by
  let f : Multiset ℕ → (Fin (n + 1) → Fin (n + 1)) :=
    fun s i => ⟨min (s.count i.1) n, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hinj : Set.InjOn f {s : Multiset ℕ | position n s} := by
    intro s hs t ht hst
    ext x
    by_cases hxn : x ≤ n
    · have hsc : s.count x ≤ n := (Multiset.count_le_card x s).trans (position_card_le hs)
      have htc : t.count x ≤ n := (Multiset.count_le_card x t).trans (position_card_le ht)
      have hfx := congrArg (fun g => (g ⟨x, Nat.lt_succ_of_le hxn⟩).1) hst
      simp only [f, min_eq_left hsc, min_eq_left htc] at hfx
      exact hfx
    · have hxs : x ∉ s := fun hx => hxn (position_le_of_mem hs hx)
      have hxt : x ∉ t := fun hx => hxn (position_le_of_mem ht hx)
      rw [Multiset.count_eq_zero_of_notMem hxs, Multiset.count_eq_zero_of_notMem hxt]
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

private lemma move_halve (x : ℕ) (hx : 0 < x) (rest : Multiset ℕ) :
    move (x ::ₘ x ::ₘ rest) ((2 * x) ::ₘ rest) := by
  refine ⟨x, x, rest, hx, le_refl x, rfl, ?_⟩
  simp [two_mul]

private lemma move_avg {a b : ℕ} (ha : 0 < a) (hab : a < b) (heven : (a + b) % 2 = 0)
    (rest : Multiset ℕ) :
    move (((a + b) / 2) ::ₘ ((a + b) / 2) ::ₘ rest) (a ::ₘ b ::ₘ rest) := by
  refine ⟨(a + b) / 2, (a + b) / 2 - a, rest, by omega, by omega, rfl, ?_⟩
  have hne : (a + b) / 2 - a ≠ (a + b) / 2 := by omega
  rw [if_neg hne]
  have h1 : (a + b) / 2 - ((a + b) / 2 - a) = a := by omega
  have h2 : (a + b) / 2 + ((a + b) / 2 - a) = b := by omega
  rw [h1, h2]

private lemma phi_halve {x : ℕ} (hx : 0 < x) (rest : Multiset ℕ) :
    phi (x ::ₘ x ::ₘ rest) < phi ((2 * x) ::ₘ rest) := by
  simp only [phi, Multiset.map_cons, Multiset.sum_cons]
  nlinarith

private lemma phi_avg {a b : ℕ} (hab : a < b) (heven : (a + b) % 2 = 0) (rest : Multiset ℕ) :
    phi (((a + b) / 2) ::ₘ ((a + b) / 2) ::ₘ rest) < phi (a ::ₘ b ::ₘ rest) := by
  simp only [phi, Multiset.map_cons, Multiset.sum_cons]
  have h2m : 2 * ((a + b) / 2) = a + b := by omega
  nlinarith

private lemma move_dvd_of_odd {d : ℕ} (hd : Odd d) {s t : Multiset ℕ} (hm : move s t)
    (ht : ∀ x ∈ t, d ∣ x) : ∀ x ∈ s, d ∣ x := by
  rcases hm with ⟨x, y, rest, hy, hyx, rfl, rfl⟩
  have hcop : Nat.Coprime d 2 := by
    rcases hd with ⟨k, rfl⟩
    rw [Nat.coprime_comm]
    exact Nat.coprime_two_left.mpr (by exact ⟨k, rfl⟩)
  have hdx : d ∣ x := by
    by_cases h : y = x
    · rw [if_pos h] at ht
      have h2x : d ∣ 2 * x := by
        have := ht (x + y) (Multiset.mem_cons_self _ _)
        rwa [h, ← two_mul] at this
      exact hcop.dvd_of_dvd_mul_left h2x
    · rw [if_neg h] at ht
      have h1 : d ∣ x - y := ht (x - y) (Multiset.mem_cons_self _ _)
      have h2 : d ∣ x + y := ht (x + y) (Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _))
      have h2x : d ∣ 2 * x := by
        have hsum : (x - y) + (x + y) = 2 * x := by omega
        rw [← hsum]
        exact dvd_add h1 h2
      exact hcop.dvd_of_dvd_mul_left h2x
  have hrest : ∀ z ∈ rest, d ∣ z := by
    intro z hz
    by_cases h : y = x
    · rw [if_pos h] at ht
      exact ht z (Multiset.mem_cons_of_mem hz)
    · rw [if_neg h] at ht
      exact ht z (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hz))
  intro z hz
  rcases Multiset.mem_cons.mp hz with rfl | hz
  · exact hdx
  · rcases Multiset.mem_cons.mp hz with rfl | hz
    · exact hdx
    · exact hrest z hz

private lemma reflTransGen_dvd_of_odd {d : ℕ} (hd : Odd d) {u v : Multiset ℕ}
    (h : Relation.ReflTransGen move u v) (hv : ∀ x ∈ v, d ∣ x) : ∀ x ∈ u, d ∣ x := by
  induction h with
  | refl => exact hv
  | tail _ hm ih => exact ih (move_dvd_of_odd hd hm hv)

private lemma reachable_dvd_eq_one {n d : ℕ} (hn : 0 < n) (hd : Odd d) {s : Multiset ℕ}
    (hr : reachable n s) (hs : ∀ x ∈ s, d ∣ x) : d = 1 := by
  have hrep := reflTransGen_dvd_of_odd hd hr hs
  have h1 : d ∣ 1 := hrep 1 (Multiset.mem_replicate.mpr ⟨by omega, rfl⟩)
  exact Nat.eq_one_of_dvd_one h1

private lemma not_reachable_pair_odd {a b d : ℕ} (ha : Odd a) (hb : Odd b) (hd : Odd d)
    (hd1 : 1 < d) (hdab : d ∣ a + b) : ¬ reachable (a + b) ({a, b} : Multiset ℕ) := by
  intro hr
  generalize hs : ({a, b} : Multiset ℕ) = s at hr
  cases hr with
  | refl =>
    have hcard := congrArg Multiset.card hs
    simp only [Multiset.card_replicate, Multiset.insert_eq_cons, Multiset.card_cons,
      Multiset.card_singleton] at hcard
    have hd3 : 3 ≤ d := by
      rcases hd with ⟨k, rfl⟩
      omega
    have hle : d ≤ a + b := Nat.le_of_dvd (by omega) hdab
    omega
  | tail hprev hm =>
    rw [← hs] at hm
    rcases hm with ⟨x, y, rest, hy, hyx, rfl, hpair⟩
    by_cases h : y = x
    · rw [if_pos h] at hpair
      have hmem : x + y ∈ ({a, b} : Multiset ℕ) := by
        rw [hpair]
        exact Multiset.mem_cons_self _ _
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
      rcases ha with ⟨ka, rfl⟩
      rcases hb with ⟨kb, rfl⟩
      omega
    · rw [if_neg h] at hpair
      have hcard := congrArg Multiset.card hpair
      simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton] at hcard
      have hrest0 : rest = 0 := Multiset.card_eq_zero.mp (by omega)
      have hsum := congrArg Multiset.sum hpair
      simp only [hrest0, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton,
        Multiset.sum_zero, add_zero] at hsum
      have h2x : a + b = 2 * x := by omega
      have hcop : Nat.Coprime d 2 := by
        rcases hd with ⟨k, rfl⟩
        rw [Nat.coprime_comm]
        exact Nat.coprime_two_left.mpr ⟨k, rfl⟩
      have hdx : d ∣ x := hcop.dvd_of_dvd_mul_left (h2x ▸ hdab)
      have hall : ∀ z ∈ x ::ₘ x ::ₘ rest, d ∣ z := by
        intro z hz
        rw [hrest0] at hz
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hz
        rcases hz with rfl | rfl <;> exact hdx
      have hn : 0 < a + b := by
        rcases ha with ⟨ka, rfl⟩
        omega
      have hd_eq := reachable_dvd_eq_one hn hd hprev hall
      omega

private lemma eq_replicate_one_of_forall_eq_one {n : ℕ} {s : Multiset ℕ}
    (hsum : s.sum = n) (hall : ∀ x ∈ s, x = 1) : s = Multiset.replicate n 1 := by
  have hcard : s.card = n := by
    have h1 : s.sum = s.card * 1 := by
      have hrep := Multiset.eq_replicate.mpr ⟨rfl, hall⟩
      conv_lhs => rw [hrep]
      simp
    omega
  exact Multiset.eq_replicate.mpr ⟨hcard, hall⟩

private lemma exists_pow_two_or_odd_prime_dvd (n : ℕ) (hn : 0 < n) :
    (∃ k : ℕ, n = 2 ^ k) ∨ (∃ p : ℕ, Nat.Prime p ∧ Odd p ∧ p ∣ n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · left; exact ⟨0, by simp [h1]⟩
    · by_cases h2 : 2 ∣ n
      · rcases h2 with ⟨m, rfl⟩
        have hm0 : 0 < m := by omega
        have hmlt : m < 2 * m := by omega
        rcases ih m hmlt hm0 with ⟨k, rfl⟩ | ⟨p, hp, hpo, hpd⟩
        · left; exact ⟨k + 1, by ring⟩
        · right; exact ⟨p, hp, hpo, dvd_mul_of_dvd_right hpd 2⟩
      · right
        refine ⟨n.minFac, Nat.minFac_prime h1, ?_, Nat.minFac_dvd n⟩
        have hne2 : n.minFac ≠ 2 := by
          intro heq
          apply h2
          rw [← heq]
          exact Nat.minFac_dvd n
        rcases (Nat.minFac_prime h1).eq_two_or_odd with h | h
        · exact absurd h hne2
        · exact Nat.odd_iff.mpr h

private lemma reachable_of_pow_two (k : ℕ) :
    ∀ s : Multiset ℕ, position (2 ^ k) s → reachable (2 ^ k) s := by
  suffices h : ∀ N s, phi s = N → position (2 ^ k) s → reachable (2 ^ k) s by
    intro s hs; exact h (phi s) s rfl hs
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro s hphi hs
    by_cases hall1 : ∀ x ∈ s, x = 1
    · rw [eq_replicate_one_of_forall_eq_one hs.1 hall1]
      exact Relation.ReflTransGen.refl
    · by_cases heven : ∃ x ∈ s, x % 2 = 0
      · rcases heven with ⟨x, hxmem, hxev⟩
        rcases Multiset.exists_cons_of_mem hxmem with ⟨rest, rfl⟩
        have hxpos : 0 < x := hs.2 x (Multiset.mem_cons_self _ _)
        set u := x / 2
        have hxu : x = 2 * u := by omega
        have hupos : 0 < u := by omega
        let t := u ::ₘ u ::ₘ rest
        have htpos : position (2 ^ k) t := by
          refine ⟨?_, ?_⟩
          · have hsum := hs.1
            simp only [t, Multiset.sum_cons] at hsum ⊢
            omega
          · intro z hz
            simp only [t, Multiset.mem_cons] at hz
            rcases hz with rfl | rfl | hz
            · exact hupos
            · exact hupos
            · exact hs.2 z (Multiset.mem_cons_of_mem hz)
        have hphi_lt : phi t < N := by
          rw [← hphi, hxu]
          exact phi_halve hupos rest
        have hmove : move t (x ::ₘ rest) := by
          rw [hxu]
          exact move_halve u hupos rest
        exact Relation.ReflTransGen.tail (ih (phi t) hphi_lt t rfl htpos) hmove
      · push Not at hall1 heven
        rcases hall1 with ⟨a, hamem, hane1⟩
        have hodd_all : ∀ x ∈ s, x % 2 = 1 := fun x hx => by
          have := heven x hx; omega
        have hex_ne : ∃ b ∈ s, b ≠ a := by
          by_contra hall_a
          push Not at hall_a
          have hsrep : s = Multiset.replicate s.card a := Multiset.eq_replicate.mpr ⟨rfl, hall_a⟩
          have hdvd : a ∣ 2 ^ k := by
            refine ⟨s.card, ?_⟩
            have hsum := hs.1
            rw [hsrep, Multiset.sum_replicate, smul_eq_mul] at hsum
            linarith
          have haodd : Odd a := Nat.odd_iff.mpr (hodd_all a hamem)
          have hcop : Nat.Coprime a (2 ^ k) :=
            (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr haodd)).pow_right k
          exact hane1 (Nat.eq_one_of_dvd_one (hcop.dvd_of_dvd_mul_left (by simpa using hdvd)))
        rcases hex_ne with ⟨b, hbmem, hbne⟩
        rcases Multiset.exists_cons_of_mem hamem with ⟨r1, rfl⟩
        have hb_r1 : b ∈ r1 := by
          rcases Multiset.mem_cons.mp hbmem with rfl | h
          · exact absurd rfl hbne
          · exact h
        rcases Multiset.exists_cons_of_mem hb_r1 with ⟨rest, rfl⟩
        have ha_pos : 0 < a := hs.2 a (Multiset.mem_cons_self _ _)
        have hb_pos : 0 < b := hs.2 b (Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _))
        have ha_odd : a % 2 = 1 := hodd_all a (Multiset.mem_cons_self _ _)
        have hb_odd : b % 2 = 1 := hodd_all b (Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _))
        have hab_ev : (a + b) % 2 = 0 := by omega
        set m := (a + b) / 2
        have hmpos : 0 < m := by omega
        let t := m ::ₘ m ::ₘ rest
        have htpos : position (2 ^ k) t := by
          refine ⟨?_, ?_⟩
          · have hsum := hs.1
            simp only [t, Multiset.sum_cons] at hsum ⊢
            omega
          · intro z hz
            simp only [t, Multiset.mem_cons] at hz
            rcases hz with rfl | rfl | hz
            · exact hmpos
            · exact hmpos
            · exact hs.2 z (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hz))
        rcases lt_or_gt_of_ne hbne with hba | hab
        · have hphi_lt : phi t < N := by
            rw [← hphi, Multiset.cons_swap]
            have hmeq : m = (b + a) / 2 := by omega
            simpa only [t, hmeq] using phi_avg hba (by omega) rest
          have hmove : move t (a ::ₘ b ::ₘ rest) := by
            rw [Multiset.cons_swap]
            have hmeq : m = (b + a) / 2 := by omega
            simpa only [t, hmeq] using move_avg hb_pos hba (by omega) rest
          exact Relation.ReflTransGen.tail (ih (phi t) hphi_lt t rfl htpos) hmove
        · have hphi_lt : phi t < N := by
            rw [← hphi]
            exact phi_avg hab hab_ev rest
          have hmove : move t (a ::ₘ b ::ₘ rest) := move_avg ha_pos hab hab_ev rest
          exact Relation.ReflTransGen.tail (ih (phi t) hphi_lt t rfl htpos) hmove

private lemma reachable_of_pow_two_mul_prime (k p : ℕ) (hp : Nat.Prime p) (_hp_odd : Odd p) :
    ∀ s : Multiset ℕ, position (2 ^ k * p) s →
      (¬ ∀ x ∈ s, p ∣ x) →
      (¬ ∃ a b, Odd a ∧ Odd b ∧ s = ({a, b} : Multiset ℕ)) →
      reachable (2 ^ k * p) s := by
  suffices h : ∀ N s, phi s = N → position (2 ^ k * p) s →
      (¬ ∀ x ∈ s, p ∣ x) →
      (¬ ∃ a b, Odd a ∧ Odd b ∧ s = ({a, b} : Multiset ℕ)) →
      reachable (2 ^ k * p) s by
    intro s hs h1 h2; exact h (phi s) s rfl hs h1 h2
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro s hphi hs hndvd hnot2
    by_cases hall1 : ∀ x ∈ s, x = 1
    · rw [eq_replicate_one_of_forall_eq_one hs.1 hall1]
      exact Relation.ReflTransGen.refl
    · by_cases heven : ∃ x ∈ s, x % 2 = 0
      · rcases heven with ⟨x, hxmem, hxev⟩
        rcases Multiset.exists_cons_of_mem hxmem with ⟨rest, rfl⟩
        have hxpos : 0 < x := hs.2 x (Multiset.mem_cons_self _ _)
        set u := x / 2
        have hxu : x = 2 * u := by omega
        have hupos : 0 < u := by omega
        let t := u ::ₘ u ::ₘ rest
        have htpos : position (2 ^ k * p) t := by
          refine ⟨?_, ?_⟩
          · have hsum := hs.1
            simp only [t, Multiset.sum_cons] at hsum ⊢
            omega
          · intro z hz
            simp only [t, Multiset.mem_cons] at hz
            rcases hz with rfl | rfl | hz
            · exact hupos
            · exact hupos
            · exact hs.2 z (Multiset.mem_cons_of_mem hz)
        have ht_ndvd : ¬ ∀ z ∈ t, p ∣ z := by
          intro htdvd
          apply hndvd
          intro z hz
          rcases Multiset.mem_cons.mp hz with rfl | hz
          · rw [hxu]
            exact dvd_mul_of_dvd_right (htdvd u (Multiset.mem_cons_self _ _)) 2
          · exact htdvd z (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hz))
        have ht_not2 : ¬ ∃ a b, Odd a ∧ Odd b ∧ t = ({a, b} : Multiset ℕ) := by
          rintro ⟨a, b, _, _, hteq⟩
          have hcard := congrArg Multiset.card hteq
          simp only [t, Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton] at hcard
          have hrest0 : rest = 0 := Multiset.card_eq_zero.mp (by omega)
          apply hndvd
          intro z hz
          rw [hrest0] at hz
          simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hz
          subst hz
          have hsum := hs.1
          rw [hrest0, Multiset.sum_cons, Multiset.sum_zero, add_zero] at hsum
          rw [hsum]
          exact dvd_mul_left p (2 ^ k)
        have hphi_lt : phi t < N := by
          rw [← hphi, hxu]
          exact phi_halve hupos rest
        have hmove : move t (x ::ₘ rest) := by
          rw [hxu]
          exact move_halve u hupos rest
        exact Relation.ReflTransGen.tail (ih (phi t) hphi_lt t rfl htpos ht_ndvd ht_not2) hmove
      · push Not at heven
        have hodd_all : ∀ x ∈ s, x % 2 = 1 := fun x hx => by
          have := heven x hx; omega
        have hcard_ge3 : 3 ≤ s.card := by
          by_contra hlt
          have hle2 : s.card ≤ 2 := by omega
          interval_cases hc : s.card
          · have hs0 : s = 0 := Multiset.card_eq_zero.mp hc
            have hsum := hs.1
            rw [hs0, Multiset.sum_zero] at hsum
            have hpos : 0 < 2 ^ k * p := Nat.mul_pos (by positivity) hp.pos
            omega
          · rcases Multiset.card_eq_one.mp hc with ⟨x, rfl⟩
            have hsum := hs.1
            simp only [Multiset.sum_singleton] at hsum
            apply hndvd
            intro z hz
            rw [Multiset.mem_singleton.mp hz, hsum]
            exact dvd_mul_left p (2 ^ k)
          · rcases Multiset.card_eq_two.mp hc with ⟨a, b, rfl⟩
            apply hnot2
            refine ⟨a, b, Nat.odd_iff.mpr (hodd_all a (by simp)),
              Nat.odd_iff.mpr (hodd_all b (by simp)), rfl⟩
        have hex_a : ∃ a ∈ s, ¬ p ∣ a := by
          by_contra hall
          push Not at hall
          exact hndvd hall
        rcases hex_a with ⟨a, hamem, ha_ndvd⟩
        rcases Multiset.exists_cons_of_mem hamem with ⟨r1, rfl⟩
        have hex_b : ∃ b ∈ r1, ¬ p ∣ b := by
          by_contra hall_r1
          push Not at hall_r1
          have hr1_dvd : p ∣ r1.sum := Multiset.dvd_sum hall_r1
          have hsum_dvd : p ∣ a + r1.sum := by
            have := hs.1
            rw [Multiset.sum_cons] at this
            rw [this]
            exact dvd_mul_left p (2 ^ k)
          exact ha_ndvd ((Nat.dvd_add_left hr1_dvd).mp hsum_dvd)
        rcases hex_b with ⟨b, hbmem, hb_ndvd⟩
        rcases Multiset.exists_cons_of_mem hbmem with ⟨r2, rfl⟩
        have hstep_data : ∃ u v rest', a ::ₘ b ::ₘ r2 = u ::ₘ v ::ₘ rest' ∧ u ≠ v ∧
            ∃ w ∈ rest', ¬ p ∣ w := by
          by_cases hc : ∃ c ∈ r2, ¬ p ∣ c
          · rcases hc with ⟨c, hcmem, hc_ndvd⟩
            by_cases hab : a = b
            · subst hab
              have hex_z : ∃ z ∈ r2, z ≠ a := by
                by_contra hall_z
                push Not at hall_z
                have hall_s : ∀ z ∈ a ::ₘ a ::ₘ r2, z = a := by
                  intro z hz
                  rcases Multiset.mem_cons.mp hz with rfl | hz
                  · rfl
                  · rcases Multiset.mem_cons.mp hz with rfl | hz
                    · rfl
                    · exact hall_z z hz
                have ha_ne1 : a ≠ 1 := by
                  intro ha1
                  apply hall1
                  intro z hz
                  rw [hall_s z hz, ha1]
                have hsrep : a ::ₘ a ::ₘ r2 = Multiset.replicate (a ::ₘ a ::ₘ r2).card a :=
                  Multiset.eq_replicate.mpr ⟨rfl, hall_s⟩
                have hdvd : a ∣ 2 ^ k * p := by
                  refine ⟨(a ::ₘ a ::ₘ r2).card, ?_⟩
                  have hsum := hs.1
                  rw [hsrep, Multiset.sum_replicate, smul_eq_mul] at hsum
                  linarith
                have haodd : Odd a := Nat.odd_iff.mpr (hodd_all a (Multiset.mem_cons_self _ _))
                have hcop : Nat.Coprime a (2 ^ k) :=
                  (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr haodd)).pow_right k
                have hap : a ∣ p := hcop.dvd_of_dvd_mul_left hdvd
                rcases hp.eq_one_or_self_of_dvd a hap with h1 | h2
                · exact ha_ne1 h1
                · exact ha_ndvd (h2 ▸ dvd_refl p)
              rcases hex_z with ⟨z, hzmem, hzne⟩
              rcases Multiset.exists_cons_of_mem hzmem with ⟨r3, rfl⟩
              refine ⟨a, z, a ::ₘ r3, ?_, hzne.symm, a, Multiset.mem_cons_self _ _, ha_ndvd⟩
              rw [Multiset.cons_swap a z r3]
            · exact ⟨a, b, r2, rfl, hab, c, hcmem, hc_ndvd⟩
          · push Not at hc
            have hr2_ne : r2 ≠ 0 := by
              intro h0
              rw [h0] at hcard_ge3
              simp at hcard_ge3
            rcases Multiset.exists_mem_of_ne_zero hr2_ne with ⟨c, hcmem⟩
            rcases Multiset.exists_cons_of_mem hcmem with ⟨r3, rfl⟩
            have hc_dvd : p ∣ c := hc c (Multiset.mem_cons_self _ _)
            have hac : a ≠ c := fun h => ha_ndvd (h ▸ hc_dvd)
            refine ⟨a, c, b ::ₘ r3, ?_, hac, b, Multiset.mem_cons_self _ _, hb_ndvd⟩
            rw [Multiset.cons_swap b c r3]
        rcases hstep_data with ⟨u, v, rest', hseq, huv_ne, w, hwmem, hw_ndvd⟩
        have hu_mem : u ∈ a ::ₘ b ::ₘ r2 := by rw [hseq]; exact Multiset.mem_cons_self _ _
        have hv_mem : v ∈ a ::ₘ b ::ₘ r2 := by
          rw [hseq]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
        have hu_pos : 0 < u := hs.2 u hu_mem
        have hv_pos : 0 < v := hs.2 v hv_mem
        have hu_odd : u % 2 = 1 := hodd_all u hu_mem
        have hv_odd : v % 2 = 1 := hodd_all v hv_mem
        set m := (u + v) / 2
        have hmpos : 0 < m := by omega
        let t := m ::ₘ m ::ₘ rest'
        have htpos : position (2 ^ k * p) t := by
          refine ⟨?_, ?_⟩
          · have hsum := hs.1
            rw [hseq] at hsum
            simp only [t, Multiset.sum_cons] at hsum ⊢
            omega
          · intro z hz
            simp only [t, Multiset.mem_cons] at hz
            rcases hz with rfl | rfl | hz
            · exact hmpos
            · exact hmpos
            · apply hs.2 z
              rw [hseq]
              exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hz)
        have ht_ndvd : ¬ ∀ z ∈ t, p ∣ z := by
          intro htdvd
          exact hw_ndvd (htdvd w (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hwmem)))
        have ht_not2 : ¬ ∃ x y, Odd x ∧ Odd y ∧ t = ({x, y} : Multiset ℕ) := by
          rintro ⟨x, y, _, _, hteq⟩
          have hcard1 := congrArg Multiset.card hteq
          have hcard2 := congrArg Multiset.card hseq
          simp only [t, Multiset.insert_eq_cons, Multiset.card_cons,
            Multiset.card_singleton] at hcard1 hcard2 hcard_ge3
          omega
        rcases lt_or_gt_of_ne huv_ne with huv | hvu
        · have hphi_lt : phi t < N := by
            rw [← hphi, hseq]
            exact phi_avg huv (by omega) rest'
          have hmove : move t (a ::ₘ b ::ₘ r2) := by
            rw [hseq]
            exact move_avg hu_pos huv (by omega) rest'
          exact Relation.ReflTransGen.tail (ih (phi t) hphi_lt t rfl htpos ht_ndvd ht_not2) hmove
        · have hphi_lt : phi t < N := by
            rw [← hphi, hseq, Multiset.cons_swap]
            have hmeq : m = (v + u) / 2 := by omega
            simpa only [t, hmeq] using phi_avg hvu (by omega) rest'
          have hmove : move t (a ::ₘ b ::ₘ r2) := by
            rw [hseq, Multiset.cons_swap]
            have hmeq : m = (v + u) / 2 := by omega
            simpa only [t, hmeq] using move_avg hv_pos hvu (by omega) rest'
          exact Relation.ReflTransGen.tail (ih (phi t) hphi_lt t rfl htpos ht_ndvd ht_not2) hmove

private lemma diff_eq_ncard_unreach (n : ℕ) :
    distinctPartitions n - a n =
      Set.ncard {s : Multiset ℕ | position n s ∧ s.Nodup ∧ ¬ reachable n s} := by
  let D := {s : Multiset ℕ | position n s ∧ s.Nodup}
  let R := {s : Multiset ℕ | position n s ∧ s.Nodup ∧ reachable n s}
  let U := {s : Multiset ℕ | position n s ∧ s.Nodup ∧ ¬ reachable n s}
  have hDfin : D.Finite := (finite_position n).subset (fun s hs => hs.1)
  have hsub : R ⊆ D := fun s hs => ⟨hs.1, hs.2.1⟩
  have hRfin : R.Finite := hDfin.subset hsub
  have hUfin : U.Finite := (finite_position n).subset (fun s hs => hs.1)
  have hunion : R ∪ U = D := by
    ext s
    simp only [Set.mem_union, Set.mem_ofPred_eq, D, R, U]
    tauto
  have hdisj : Disjoint R U := by
    rw [Set.disjoint_left]
    intro s hsR hsU
    exact hsU.2.2 hsR.2.2
  have hadd : R.ncard + U.ncard = D.ncard := by
    rw [← Set.ncard_union_eq hdisj hRfin hUfin, hunion]
  change D.ncard - R.ncard = U.ncard
  omega

private lemma a_le_distinctPartitions (n : ℕ) : a n ≤ distinctPartitions n := by
  have hDfin : {s : Multiset ℕ | position n s ∧ s.Nodup}.Finite :=
    (finite_position n).subset (fun s hs => hs.1)
  exact Set.ncard_le_ncard (fun s hs => ⟨hs.1, hs.2.1⟩) hDfin

private lemma singleton_mem_unreach {n p : ℕ} (hn : 0 < n) (hp : Nat.Prime p) (hp_odd : Odd p)
    (hpd : p ∣ n) :
    ({n} : Multiset ℕ) ∈ {s : Multiset ℕ | position n s ∧ s.Nodup ∧ ¬ reachable n s} := by
  refine ⟨⟨by simp, fun x hx => by rw [Multiset.mem_singleton.mp hx]; exact hn⟩,
    Multiset.nodup_singleton n, ?_⟩
  intro hr
  have hall : ∀ x ∈ ({n} : Multiset ℕ), p ∣ x := fun x hx => by
    rw [Multiset.mem_singleton.mp hx]; exact hpd
  exact hp.ne_one (reachable_dvd_eq_one hn hp_odd hr hall)

private lemma main_proof : ∀ n : ℕ, 0 < n →
    (a n = distinctPartitions n ↔ ∃ k : ℕ, n = 2 ^ k) ∧
    (distinctPartitions n - a n = 1 ↔ Nat.Prime n ∧ Odd n) := by
  intro n hn
  let U := {s : Multiset ℕ | position n s ∧ s.Nodup ∧ ¬ reachable n s}
  have hUfin : U.Finite := (finite_position n).subset (fun s hs => hs.1)
  have hdiff : distinctPartitions n - a n = U.ncard := diff_eq_ncard_unreach n
  have hle : a n ≤ distinctPartitions n := a_le_distinctPartitions n
  constructor
  · constructor
    · intro heq
      have hU0 : U.ncard = 0 := by omega
      have hUemp : U = ∅ := (Set.ncard_eq_zero hUfin).mp hU0
      rcases exists_pow_two_or_odd_prime_dvd n hn with hpow | ⟨p, hp, hpo, hpd⟩
      · exact hpow
      · exfalso
        have hmem : ({n} : Multiset ℕ) ∈ U := singleton_mem_unreach hn hp hpo hpd
        rw [hUemp] at hmem
        exact hmem
    · rintro ⟨k, rfl⟩
      have hUemp : U = ∅ := by
        ext s
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not, U]
        intro hs _
        exact reachable_of_pow_two k s hs
      have hU0 : U.ncard = 0 := by rw [hUemp, Set.ncard_empty]
      omega
  · rw [hdiff]
    constructor
    · intro hU1
      rcases exists_pow_two_or_odd_prime_dvd n hn with ⟨k, rfl⟩ | ⟨p, hp, hpo, hpd⟩
      · exfalso
        have hUemp : U = ∅ := by
          ext s
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not, U]
          intro hs _
          exact reachable_of_pow_two k s hs
        rw [hUemp, Set.ncard_empty] at hU1
        omega
      · rcases hpd with ⟨m, rfl⟩
        have hmpos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with rfl | h
          · simp at hn
          · exact h
        by_cases hm1 : m = 1
        · subst hm1; simpa using And.intro hp hpo
        · exfalso
          have hs1 : ({p * m} : Multiset ℕ) ∈ U :=
            singleton_mem_unreach hn hp hpo (dvd_mul_right p m)
          have hp3 : 3 ≤ p := by
            have := hp.two_le
            rcases hpo with ⟨k, rfl⟩
            omega
          have hex_s2 : ∃ s2 ∈ U, s2 ≠ ({p * m} : Multiset ℕ) := by
            by_cases hm2 : m = 2
            · subst hm2
              refine ⟨{2 * p - 1, 1}, ?_, ?_⟩
              · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
                · simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
                  omega
                · intro x hx
                  simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                    Multiset.mem_singleton] at hx
                  rcases hx with rfl | rfl <;> omega
                · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons,
                    Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
                  omega
                · have hsum_eq : (2 * p - 1) + 1 = p * 2 := by omega
                  rw [← hsum_eq]
                  exact not_reachable_pair_odd
                    (by exact ⟨p - 1, by omega⟩)
                    ⟨0, rfl⟩ hpo hp.one_lt (by rw [hsum_eq]; exact dvd_mul_right p 2)
              · intro heq
                have hcard := congrArg Multiset.card heq
                simp only [Multiset.insert_eq_cons, Multiset.card_cons,
                  Multiset.card_singleton] at hcard
                omega
            · have hm3 : 3 ≤ m := by omega
              refine ⟨{p * (m - 1), p}, ?_, ?_⟩
              · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
                · simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
                  have : p * (m - 1) + p = p * m := by
                    calc p * (m - 1) + p = p * (m - 1) + p * 1 := by ring
                    _ = p * (m - 1 + 1) := by rw [← mul_add]
                    _ = p * m := by rw [Nat.sub_add_cancel (by omega)]
                  exact this
                · intro x hx
                  simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                    Multiset.mem_singleton] at hx
                  rcases hx with rfl | rfl
                  · exact Nat.mul_pos hp.pos (by omega)
                  · exact hp.pos
                · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons,
                    Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
                  have : p < p * (m - 1) := lt_mul_of_one_lt_right hp.pos (by omega)
                  omega
                · intro hr
                  have hall : ∀ x ∈ ({p * (m - 1), p} : Multiset ℕ), p ∣ x := by
                    intro x hx
                    simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                      Multiset.mem_singleton] at hx
                    rcases hx with rfl | rfl
                    · exact dvd_mul_right p (m - 1)
                    · exact dvd_refl _
                  exact hp.ne_one (reachable_dvd_eq_one hn hpo hr hall)
              · intro heq
                have hcard := congrArg Multiset.card heq
                simp only [Multiset.insert_eq_cons, Multiset.card_cons,
                  Multiset.card_singleton] at hcard
                omega
          rcases hex_s2 with ⟨s2, hs2, hne⟩
          have hpair_sub : ({({p * m} : Multiset ℕ), s2} : Set (Multiset ℕ)) ⊆ U := by
            intro x hx
            rcases hx with rfl | rfl
            · exact hs1
            · exact hs2
          have h2le : 2 ≤ U.ncard := by
            have hpair_card : ({({p * m} : Multiset ℕ), s2} : Set (Multiset ℕ)).ncard = 2 := by
              rw [Set.ncard_pair hne.symm]
            rw [← hpair_card]
            exact Set.ncard_le_ncard hpair_sub hUfin
          omega
    · rintro ⟨hp, hpo⟩
      have hUeq : U = {({n} : Multiset ℕ)} := by
        ext s
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, U]
        constructor
        · rintro ⟨hs, _, hnr⟩
          have hnot2 : ¬ ∃ a b, Odd a ∧ Odd b ∧ s = ({a, b} : Multiset ℕ) := by
            rintro ⟨a, b, ha, hb, rfl⟩
            have hsum := hs.1
            simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum
            rcases ha with ⟨ka, rfl⟩
            rcases hb with ⟨kb, rfl⟩
            rcases hpo with ⟨kn, hkn⟩
            omega
          have hdvd_all : ∀ x ∈ s, n ∣ x := by
            by_contra hndvd
            apply hnr
            have h1 : 2 ^ 0 * n = n := by ring
            rw [← h1] at hs ⊢
            exact reachable_of_pow_two_mul_prime 0 n hp hpo s hs hndvd hnot2
          have hs_ne : s ≠ 0 := by
            intro h0
            have := hs.1
            rw [h0, Multiset.sum_zero] at this
            omega
          rcases Multiset.exists_mem_of_ne_zero hs_ne with ⟨x, hxmem⟩
          rcases Multiset.exists_cons_of_mem hxmem with ⟨rest, rfl⟩
          have hxn : n ≤ x := Nat.le_of_dvd (hs.2 x (Multiset.mem_cons_self _ _))
            (hdvd_all x (Multiset.mem_cons_self _ _))
          have hsum := hs.1
          rw [Multiset.sum_cons] at hsum
          have hrest_sum : rest.sum = 0 := by omega
          have hrest0 : rest = 0 := by
            by_contra hne0
            rcases Multiset.exists_mem_of_ne_zero hne0 with ⟨y, hymem⟩
            have hypos : 0 < y := hs.2 y (Multiset.mem_cons_of_mem hymem)
            have hyle : y ≤ rest.sum := Multiset.le_sum_of_mem hymem
            omega
          subst hrest0
          have hx_eq : x = n := by omega
          subst hx_eq
          rfl
        · rintro rfl
          exact singleton_mem_unreach hn hp hpo (dvd_refl n)
      rw [hUeq, Set.ncard_singleton]

end OMA_A292728

theorem OMA.solution : type_of% @OMA.S_oeis_a292728.main := OMA_A292728.main_proof
