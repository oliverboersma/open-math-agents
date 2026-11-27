import OMAStatements.S_oeis_a292727
import Mathlib.Tactic

-- Problem: A292727: a(n) is the number of states that cannot be achieved when starting from n piles each containing one stone, where stones can be tra
-- Upstream: formal-conjectures statements/oeis-a292727.lean:0 (declaration OMA.S_oeis_a292727.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA_A292727

open OMA.S_oeis_a292727

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
    exact Nat.coprime_two_left.mpr ⟨k, rfl⟩
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

private lemma reachable_of_pow_two_mul_prime (k p : ℕ) (hp : Nat.Prime p) :
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

private lemma singleton_mem_unreach {n p : ℕ} (hn : 0 < n) (hp : Nat.Prime p) (hp_odd : Odd p)
    (hpd : p ∣ n) :
    ({n} : Multiset ℕ) ∈ {s : Multiset ℕ | position n s ∧ ¬ reachable n s} := by
  refine ⟨⟨by simp, fun x hx => by rw [Multiset.mem_singleton.mp hx]; exact hn⟩, ?_⟩
  intro hr
  have hall : ∀ x ∈ ({n} : Multiset ℕ), p ∣ x := fun x hx => by
    rw [Multiset.mem_singleton.mp hx]; exact hpd
  exact hp.ne_one (reachable_dvd_eq_one hn hp_odd hr hall)

private def partsAux : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, 0, _ => [[]]
  | 0, _ + 1, _ => []
  | _ + 1, 0, _ => [[]]
  | _ + 1, _ + 1, 0 => []
  | fuel + 1, rem + 1, maxPart + 1 =>
    if maxPart + 1 ≤ rem + 1 then
      (partsAux fuel (rem - maxPart) (maxPart + 1)).map (fun l => (maxPart + 1) :: l) ++
        partsAux fuel (rem + 1) maxPart
    else
      partsAux fuel (rem + 1) maxPart

private lemma mem_partsAux : ∀ (fuel rem maxPart : ℕ) (l : List ℕ),
    rem + maxPart ≤ fuel → l.sum = rem →
    (∀ x ∈ l, 0 < x ∧ x ≤ maxPart) → l.Pairwise (· ≥ ·) →
    l ∈ partsAux fuel rem maxPart := by
  intro fuel
  induction fuel with
  | zero =>
    intro rem maxPart l hle hsum hbd _
    have hr0 : rem = 0 := by omega
    subst hr0
    cases l with
    | nil => simp [partsAux]
    | cons x xs =>
      have hx := (hbd x (by simp)).1
      simp at hsum
      omega
  | succ fuel ih =>
    intro rem maxPart l hle hsum hbd hpw
    cases rem with
    | zero =>
      cases l with
      | nil => simp [partsAux]
      | cons x xs =>
        have hx := (hbd x (by simp)).1
        simp at hsum
        omega
    | succ r =>
      cases maxPart with
      | zero =>
        cases l with
        | nil => simp at hsum
        | cons x xs =>
          have := hbd x (by simp)
          omega
      | succ mp =>
        cases l with
        | nil => simp at hsum
        | cons x xs =>
          have hxbd := hbd x (by simp)
          have hsum_eq : x + xs.sum = r + 1 := by simpa using hsum
          by_cases hxtop : x = mp + 1
          · subst hxtop
            have hle_m : mp + 1 ≤ r + 1 := by omega
            simp only [partsAux, if_pos hle_m, List.mem_append, List.mem_map]
            left
            refine ⟨xs, ?_, rfl⟩
            refine ih (r - mp) (mp + 1) xs (by omega) (by omega) ?_ (List.Pairwise.of_cons hpw)
            intro y hy
            exact ⟨(hbd y (by simp [hy])).1, (List.pairwise_cons.mp hpw).1 y hy⟩
          · have hbd' : ∀ y ∈ x :: xs, 0 < y ∧ y ≤ mp := by
              intro y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · omega
              · have hyx := (List.pairwise_cons.mp hpw).1 y hy
                exact ⟨(hbd y (by simp [hy])).1, by omega⟩
            have hrec := ih (r + 1) mp (x :: xs) (by omega) hsum hbd' hpw
            simp only [partsAux]
            split_ifs
            · exact List.mem_append_right _ hrec
            · exact hrec

private lemma ncard_position_eq_of_partsAux (c : ℕ)
    (hvalid : ∀ l ∈ partsAux (2 * c) c c, l.sum = c ∧ (∀ x ∈ l, 0 < x) ∧ l.Pairwise (· ≥ ·))
    (hnodup : (partsAux (2 * c) c c).Nodup) :
    Set.ncard {t : Multiset ℕ | position c t} = (partsAux (2 * c) c c).length := by
  let S : Set (List ℕ) := {l | l ∈ partsAux (2 * c) c c}
  have hinj : Set.InjOn (fun l : List ℕ => (l : Multiset ℕ)) S := by
    intro l1 hl1 l2 hl2 heq
    have hperm : l1.Perm l2 := Multiset.coe_eq_coe.mp heq
    have hpw1 := (hvalid l1 hl1).2.2
    have hpw2 := (hvalid l2 hl2).2.2
    exact List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h2 h1) hpw1 hpw2 hperm
  have himg : (fun l : List ℕ => (l : Multiset ℕ)) '' S = {t : Multiset ℕ | position c t} := by
    ext t
    simp only [Set.mem_image, Set.mem_ofPred_eq, S]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hv := hvalid l hl
      exact ⟨by simpa using hv.1, fun x hx => hv.2.1 x (Multiset.mem_coe.mp hx)⟩
    · intro ht
      let l := t.sort (· ≥ ·)
      refine ⟨l, ?_, Multiset.sort_eq t (· ≥ ·)⟩
      have hlcoe : (l : Multiset ℕ) = t := Multiset.sort_eq t (· ≥ ·)
      refine mem_partsAux (2 * c) c c l (by omega) ?_ ?_ (Multiset.pairwise_sort t (· ≥ ·))
      · have hsum := ht.1
        rw [← hlcoe] at hsum
        simpa using hsum
      · intro x hx
        have hxt : x ∈ t := by rw [← hlcoe]; exact Multiset.mem_coe.mpr hx
        exact ⟨ht.2 x hxt, position_le_of_mem ht hxt⟩
  rw [← himg, Set.InjOn.ncard_image hinj]
  have hSeq : S = ↑(partsAux (2 * c) c c).toFinset := by
    ext l
    simp [S]
  rw [hSeq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup]

private lemma ncard_position_four : Set.ncard {t : Multiset ℕ | position 4 t} = 5 := by
  have hvalid : ∀ l ∈ partsAux 8 4 4, l.sum = 4 ∧ (∀ x ∈ l, 0 < x) ∧ l.Pairwise (· ≥ ·) := by
    decide
  have hnodup : (partsAux 8 4 4).Nodup := by decide
  rw [ncard_position_eq_of_partsAux 4 hvalid hnodup]
  rfl

private lemma ncard_position_eight : Set.ncard {t : Multiset ℕ | position 8 t} = 22 := by
  have hvalid : ∀ l ∈ partsAux 16 8 8, l.sum = 8 ∧ (∀ x ∈ l, 0 < x) ∧ l.Pairwise (· ≥ ·) := by
    decide
  have hnodup : (partsAux 16 8 8).Nodup := by decide
  rw [ncard_position_eq_of_partsAux 8 hvalid hnodup]
  rfl

private lemma ncard_mul_prime (c p : ℕ) (hp : 0 < p) :
    Set.ncard {s : Multiset ℕ | position (c * p) s ∧ ∀ x ∈ s, p ∣ x} =
      Set.ncard {t : Multiset ℕ | position c t} := by
  let g : Multiset ℕ → Multiset ℕ := fun t => t.map (· * p)
  have hginj : Function.Injective g := by
    intro t1 t2 heq
    ext x
    have hmul_inj : Function.Injective (· * p) := mul_left_injective₀ hp.ne'
    have hc1 := Multiset.count_map_eq_count' (· * p) t1 hmul_inj x
    have hc2 := Multiset.count_map_eq_count' (· * p) t2 hmul_inj x
    rw [← hc1, ← hc2]
    exact congrArg (fun m => m.count (x * p)) heq
  have himg : g '' {t : Multiset ℕ | position c t} =
      {s : Multiset ℕ | position (c * p) s ∧ ∀ x ∈ s, p ∣ x} := by
    ext s
    simp only [Set.mem_image, Set.mem_ofPred_eq, g]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [Multiset.sum_map_mul_right, ht.1]
      · intro y hy
        rcases Multiset.mem_map.mp hy with ⟨x, hx, rfl⟩
        exact Nat.mul_pos (ht.2 x hx) hp
      · intro y hy
        rcases Multiset.mem_map.mp hy with ⟨x, _, rfl⟩
        exact dvd_mul_left p x
    · rintro ⟨hs, hdvd⟩
      refine ⟨s.map (· / p), ⟨?_, ?_⟩, ?_⟩
      · have hmul : (s.map (· / p)).sum * p = c * p := by
          rw [← Multiset.sum_map_mul_right]
          have hmap : s.map (fun i => i / p * p) = s := by
            conv_rhs => rw [← Multiset.map_id' s]
            exact Multiset.map_congr rfl (fun x hx => Nat.div_mul_cancel (hdvd x hx))
          rw [hmap, hs.1]
        exact Nat.eq_of_mul_eq_mul_right hp hmul
      · intro y hy
        rcases Multiset.mem_map.mp hy with ⟨x, hx, rfl⟩
        have hxpos : 0 < x := hs.2 x hx
        have hpx : p ≤ x := Nat.le_of_dvd hxpos (hdvd x hx)
        exact Nat.div_pos hpx hp
      · rw [Multiset.map_map]
        conv_rhs => rw [← Multiset.map_id' s]
        exact Multiset.map_congr rfl (fun x hx => Nat.div_mul_cancel (hdvd x hx))
  rw [← himg, Set.ncard_image_of_injective _ hginj]

private lemma a_four_mul_m_prime (k m p : ℕ) (hk : 2 ^ k = 4 * m) (hm : 0 < m)
    (hp : Nat.Prime p) (hp_odd : Odd p) :
    a (4 * m * p) =
      Set.ncard {t : Multiset ℕ | position (4 * m) t} +
      (((Finset.range (m * p)).image (fun i => 2 * i + 1)).filter (fun x => ¬ p ∣ x)).card := by
  let A := {s : Multiset ℕ | position (4 * m * p) s ∧ ∀ x ∈ s, p ∣ x}
  let B := {s : Multiset ℕ | position (4 * m * p) s ∧ (¬ ∀ x ∈ s, p ∣ x) ∧
    ∃ u v, Odd u ∧ Odd v ∧ s = ({u, v} : Multiset ℕ)}
  have hAfin : A.Finite := (finite_position (4 * m * p)).subset (fun s hs => hs.1)
  have hBfin : B.Finite := (finite_position (4 * m * p)).subset (fun s hs => hs.1)
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro s hsA hsB
    exact hsB.2.1 hsA.2
  have hunion : {s : Multiset ℕ | position (4 * m * p) s ∧ ¬ reachable (4 * m * p) s} = A ∪ B := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_union, A, B]
    constructor
    · rintro ⟨hs, hnr⟩
      by_cases hdvd : ∀ x ∈ s, p ∣ x
      · left; exact ⟨hs, hdvd⟩
      · right
        refine ⟨hs, hdvd, ?_⟩
        by_contra hnot2
        apply hnr
        rw [← hk] at hs ⊢
        exact reachable_of_pow_two_mul_prime k p hp s hs hdvd hnot2
    · rintro (⟨hs, hdvd⟩ | ⟨hs, _, u, v, hu, hv, rfl⟩)
      · refine ⟨hs, ?_⟩
        intro hr
        have hpos : 0 < 4 * m * p := Nat.mul_pos (Nat.mul_pos (by norm_num) hm) hp.pos
        exact hp.ne_one (reachable_dvd_eq_one hpos hp_odd hr hdvd)
      · refine ⟨hs, ?_⟩
        have hsum : u + v = 4 * m * p := by
          have := hs.1
          simpa only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] using this
        rw [← hsum]
        exact not_reachable_pair_odd hu hv hp_odd hp.one_lt (hsum ▸ dvd_mul_left p (4 * m))
  have hAcard : A.ncard = Set.ncard {t : Multiset ℕ | position (4 * m) t} :=
    ncard_mul_prime (4 * m) p hp.pos
  set M := m * p
  have h4M : 4 * m * p = 4 * M := by ring
  let S : Finset ℕ := ((Finset.range M).image (fun i => 2 * i + 1)).filter (fun x => ¬ p ∣ x)
  let h : ℕ → Multiset ℕ := fun x => ({x, 4 * M - x} : Multiset ℕ)
  have hS_lt : ∀ x ∈ S, x < 2 * M := by
    intro x hx
    simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hx
    rcases hx.1 with ⟨i, hi, rfl⟩
    omega
  have hS_odd : ∀ x ∈ S, Odd x := by
    intro x hx
    simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hx
    rcases hx.1 with ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  have hS_ndvd : ∀ x ∈ S, ¬ p ∣ x := fun x hx => (Finset.mem_filter.mp hx).2
  have hinj : Set.InjOn h (S : Set ℕ) := by
    intro x hx y hy heq
    have hxlt := hS_lt x hx
    have hylt := hS_lt y hy
    have hmem : x ∈ h y := by
      rw [← heq]
      simp [h]
    simp only [h, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
    rcases hmem with rfl | hxy
    · rfl
    · omega
  have himg : h '' (S : Set ℕ) = B := by
    ext s
    simp only [Set.mem_image, Finset.mem_coe, Set.mem_ofPred_eq, B]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxlt := hS_lt x hx
      have hxodd := hS_odd x hx
      have hxndvd := hS_ndvd x hx
      have hxpos : 0 < x := by rcases hxodd with ⟨i, rfl⟩; omega
      have hyodd : Odd (4 * M - x) := by
        rcases hxodd with ⟨i, rfl⟩
        exact ⟨2 * M - i - 1, by omega⟩
      refine ⟨⟨?_, ?_⟩, ?_, x, 4 * M - x, hxodd, hyodd, rfl⟩
      · simp only [h, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
        omega
      · intro z hz
        simp only [h, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> omega
      · intro hall
        exact hxndvd (hall x (by simp [h]))
    · rintro ⟨hs, hndvd, u, v, hu, hv, rfl⟩
      have hsum : u + v = 4 * M := by
        have := hs.1
        simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at this
        omega
      have huv_ne : u ≠ v := by
        intro heq
        subst heq
        rcases hu with ⟨i, rfl⟩
        omega
      have hmin_mem : ∀ a b, Odd a → Odd b → a < b → a + b = 4 * M →
          (¬ ∀ z ∈ ({a, b} : Multiset ℕ), p ∣ z) →
          ∃ x ∈ S, h x = ({a, b} : Multiset ℕ) := by
        intro a b ha _ hab hsum' hndvd'
        have ha_ndvd : ¬ p ∣ a := by
          intro hpa
          apply hndvd'
          intro z hz
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
          rcases hz with rfl | hzb
          · exact hpa
          · rw [hzb]
            have hpb : p ∣ a + b := by rw [hsum', ← h4M]; exact dvd_mul_left p (4 * m)
            exact (Nat.dvd_add_right hpa).mp hpb
        refine ⟨a, ?_, ?_⟩
        · simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
          refine ⟨⟨a / 2, ?_, ?_⟩, ha_ndvd⟩
          · rcases ha with ⟨i, rfl⟩; omega
          · rcases ha with ⟨i, rfl⟩; omega
        · simp only [h]
          have hb_eq : 4 * M - a = b := by omega
          rw [hb_eq]
      rcases lt_or_gt_of_ne huv_ne with huv | hvu
      · exact hmin_mem u v hu hv huv hsum hndvd
      · have hcomm : ({u, v} : Multiset ℕ) = ({v, u} : Multiset ℕ) := Multiset.pair_comm u v
        rw [hcomm] at hndvd ⊢
        exact hmin_mem v u hv hu hvu (by omega) hndvd
  have hBcard : B.ncard = S.card := by
    rw [← himg, Set.InjOn.ncard_image hinj, Set.ncard_coe_finset]
  change Set.ncard {s : Multiset ℕ | position (4 * m * p) s ∧ ¬ reachable (4 * m * p) s} = _
  rw [hunion, Set.ncard_union_eq hdisj hAfin hBfin, hAcard, hBcard]

private lemma card_odd_not_dvd_p (p : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p) :
    (((Finset.range (1 * p)).image (fun i => 2 * i + 1)).filter (fun x => ¬ p ∣ x)).card =
      p - 1 := by
  let T := (Finset.range (1 * p)).image (fun i => 2 * i + 1)
  have hTcard : T.card = p := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range, one_mul]
  have hp_mem : p ∈ T := by
    simp only [T, Finset.mem_image, Finset.mem_range, one_mul]
    rcases hp_odd with ⟨k, rfl⟩
    exact ⟨k, by omega, by omega⟩
  have hfilt : T.filter (fun x => ¬ p ∣ x) = T.erase p := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hndvd⟩
      exact ⟨fun h => hndvd (h ▸ dvd_refl p), hx⟩
    · rintro ⟨hne, hx⟩
      refine ⟨hx, ?_⟩
      intro hpd
      simp only [T, Finset.mem_image, Finset.mem_range, one_mul] at hx
      rcases hx with ⟨i, hi, rfl⟩
      rcases hpd with ⟨q, hq⟩
      have hq1 : q = 1 := by nlinarith
      subst hq1
      exact hne (by omega)
  rw [hfilt, Finset.card_erase_of_mem hp_mem, hTcard]

private lemma card_odd_not_dvd_2p (p : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p) :
    (((Finset.range (2 * p)).image (fun i => 2 * i + 1)).filter (fun x => ¬ p ∣ x)).card =
      2 * p - 2 := by
  let T := (Finset.range (2 * p)).image (fun i => 2 * i + 1)
  have hTcard : T.card = 2 * p := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range]
  have hp_mem : p ∈ T := by
    simp only [T, Finset.mem_image, Finset.mem_range]
    rcases hp_odd with ⟨k, rfl⟩
    exact ⟨k, by omega, by omega⟩
  have h3p_mem : 3 * p ∈ T := by
    simp only [T, Finset.mem_image, Finset.mem_range]
    rcases hp_odd with ⟨k, rfl⟩
    exact ⟨3 * k + 1, by omega, by omega⟩
  have hp_ne_3p : p ≠ 3 * p := by
    have := hp.pos
    omega
  have hfilt : T.filter (fun x => ¬ p ∣ x) = (T.erase p).erase (3 * p) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hndvd⟩
      exact ⟨fun h => hndvd (h ▸ dvd_mul_left p 3), fun h => hndvd (h ▸ dvd_refl p), hx⟩
    · rintro ⟨hne3, hne1, hx⟩
      refine ⟨hx, ?_⟩
      intro hpd
      simp only [T, Finset.mem_image, Finset.mem_range] at hx
      rcases hx with ⟨i, hi, rfl⟩
      rcases hpd with ⟨q, hq⟩
      have hq_lt : q < 4 := by nlinarith
      have hq_pos : 0 < q := by nlinarith
      interval_cases q
      · exact hne1 (by omega)
      · omega
      · exact hne3 (by omega)
  have h3p_mem' : 3 * p ∈ T.erase p := Finset.mem_erase.mpr ⟨hp_ne_3p.symm, h3p_mem⟩
  rw [hfilt, Finset.card_erase_of_mem h3p_mem', Finset.card_erase_of_mem hp_mem, hTcard]
  omega

private lemma main_proof :
    (∀ n : ℕ, 0 < n →
      (a n = 0 ↔ ∃ k : ℕ, n = 2 ^ k) ∧
      (a n = 1 ↔ Nat.Prime n ∧ Odd n)) ∧
    (∀ p : ℕ, Nat.Prime p → Odd p → a (4 * p) = p + 4 ∧ a (8 * p) = 2 * p + 20) := by
  constructor
  · intro n hn
    let U := {s : Multiset ℕ | position n s ∧ ¬ reachable n s}
    have hUfin : U.Finite := (finite_position n).subset (fun s hs => hs.1)
    constructor
    · constructor
      · intro ha0
        have hUemp : U = ∅ := (Set.ncard_eq_zero hUfin).mp ha0
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
          exact reachable_of_pow_two k s
        change U.ncard = 0
        rw [hUemp, Set.ncard_empty]
    · constructor
      · intro ha1
        rcases exists_pow_two_or_odd_prime_dvd n hn with ⟨k, rfl⟩ | ⟨p, hp, hpo, hpd⟩
        · exfalso
          have hUemp : U = ∅ := by
            ext s
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not, U]
            exact reachable_of_pow_two k s
          change U.ncard = 1 at ha1
          rw [hUemp, Set.ncard_empty] at ha1
          omega
        · rcases hpd with ⟨m, rfl⟩
          have hmpos : 0 < m := by
            rcases Nat.eq_zero_or_pos m with rfl | h
            · simp at hn
            · exact h
          by_cases hm1 : m = 1
          · subst hm1; simpa using And.intro hp hpo
          · exfalso
            have hm2 : 2 ≤ m := by omega
            have hs1 : ({p * m} : Multiset ℕ) ∈ U :=
              singleton_mem_unreach hn hp hpo (dvd_mul_right p m)
            let s2 : Multiset ℕ := {p * (m - 1), p}
            have hs2 : s2 ∈ U := by
              refine ⟨⟨?_, ?_⟩, ?_⟩
              · simp only [s2, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
                calc p * (m - 1) + p = p * (m - 1) + p * 1 := by ring
                _ = p * (m - 1 + 1) := by rw [← mul_add]
                _ = p * m := by rw [Nat.sub_add_cancel (by omega)]
              · intro x hx
                simp only [s2, Multiset.insert_eq_cons, Multiset.mem_cons,
                  Multiset.mem_singleton] at hx
                rcases hx with rfl | rfl
                · exact Nat.mul_pos hp.pos (by omega)
                · exact hp.pos
              · intro hr
                have hall : ∀ x ∈ s2, p ∣ x := by
                  intro x hx
                  simp only [s2, Multiset.insert_eq_cons, Multiset.mem_cons,
                    Multiset.mem_singleton] at hx
                  rcases hx with rfl | rfl
                  · exact dvd_mul_right p (m - 1)
                  · exact dvd_refl _
                exact hp.ne_one (reachable_dvd_eq_one hn hpo hr hall)
            have hne : ({p * m} : Multiset ℕ) ≠ s2 := by
              intro heq
              have hcard := congrArg Multiset.card heq
              simp only [s2, Multiset.insert_eq_cons, Multiset.card_cons,
                Multiset.card_singleton] at hcard
              omega
            have hpair_sub : ({({p * m} : Multiset ℕ), s2} : Set (Multiset ℕ)) ⊆ U := by
              intro x hx
              rcases hx with rfl | rfl
              · exact hs1
              · exact hs2
            have h2le : 2 ≤ U.ncard := by
              rw [← Set.ncard_pair hne]
              exact Set.ncard_le_ncard hpair_sub hUfin
            change U.ncard = 1 at ha1
            omega
      · rintro ⟨hp, hpo⟩
        have hUeq : U = {({n} : Multiset ℕ)} := by
          ext s
          simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, U]
          constructor
          · rintro ⟨hs, hnr⟩
            have hnot2 : ¬ ∃ u v, Odd u ∧ Odd v ∧ s = ({u, v} : Multiset ℕ) := by
              rintro ⟨u, v, hu, hv, rfl⟩
              have hsum := hs.1
              simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum
              rcases hu with ⟨ku, rfl⟩
              rcases hv with ⟨kv, rfl⟩
              rcases hpo with ⟨kn, hkn⟩
              omega
            have hdvd_all : ∀ x ∈ s, n ∣ x := by
              by_contra hndvd
              apply hnr
              have h1 : 2 ^ 0 * n = n := by ring
              rw [← h1] at hs ⊢
              exact reachable_of_pow_two_mul_prime 0 n hp s hs hndvd hnot2
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
        change U.ncard = 1
        rw [hUeq, Set.ncard_singleton]
  · intro p hp hpo
    have hp_pos : 1 ≤ p := hp.pos
    constructor
    · have h4 := a_four_mul_m_prime 2 1 p (by norm_num) (by norm_num) hp hpo
      rw [show (4 * 1 : ℕ) = 4 by norm_num] at h4
      rw [h4, ncard_position_four, card_odd_not_dvd_p p hp hpo]
      omega
    · have h8 := a_four_mul_m_prime 3 2 p (by norm_num) (by norm_num) hp hpo
      rw [show (4 * 2 : ℕ) = 8 by norm_num] at h8
      rw [h8, ncard_position_eight, card_odd_not_dvd_2p p hp hpo]
      omega

end OMA_A292727

theorem OMA.solution : type_of% @OMA.S_oeis_a292727.main := OMA_A292727.main_proof
