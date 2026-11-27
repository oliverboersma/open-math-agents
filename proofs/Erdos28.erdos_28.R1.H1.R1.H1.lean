import OMAReductions.R_Erdos28_erdos_28_R1_H1_R1

/-!
# Six ordered representations are forced by the endpoint 70

Every subset of the natural numbers covering 0 through 70 by sums of two
members has an integer in that interval with at least six ordered representations.
The included witness covers the interval through 69 with a maximum of five.
Grekos, Haddad, Helou and Pihko published the endpoint in J. Number Theory 102
(2003), section 6.4. TheWaler independently enumerated it on the worksheet.
This file contributes a kernel-checked finite proof and a witness at 69.
Credit for the Lean formalization and independent search: @anmolspace.

At each position the search considers including or excluding that position.
An uncovered sum at the current position cannot be repaired by larger terms.
The inclusion test extracts six distinct first coordinates and checks their
reflected partners. Each surviving choice is explored through the endpoint.
-/


namespace OMA.Erdos28Five

private def pick (v : Nat) : Nat := ((0x14293caa19f60aca4480811b172b07150b15341248462414c9a3a00b5b0f0059e0633180273b097937e89c0d089488b12cc03500ecc0038b9f370640400005cdbd041c01a0200000 : Nat) >>> (7*((v ^^^ (v-1))%83)))%128

private def gather : Nat → Nat → Bool
  | 0, _ => true
  | k+1, v =>
    let p := pick v
    v.testBit p && gather k (v ^^^ (1 <<< p))

private theorem singleBit (i j : Nat) : (1 <<< i : Nat).testBit j = decide (i=j) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

private theorem gather_sound {k v : Nat} (h : gather k v = true) :
    ∃ l : List Nat, l.length=k ∧ l.Nodup ∧ ∀ i ∈ l, v.testBit i=true := by
  induction k generalizing v with
  | zero => exact ⟨[],rfl,List.nodup_nil,by simp⟩
  | succ k ih =>
    let p := pick v
    obtain ⟨hp,hr⟩ := Bool.and_eq_true_iff.mp h
    change v.testBit p = true at hp
    obtain ⟨l,hl,hd,hs⟩ := ih hr
    have ne (i : Nat) (hi : i ∈ l) : p ≠ i := by
      rintro rfl
      have hz := hs _ hi
      simp [Nat.testBit_xor, singleBit, hp, p] at hz
    refine ⟨p::l, by simp [hl], List.nodup_cons.mpr ⟨fun z => ne _ z rfl, hd⟩, ?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl|hi
    · exact hp
    · have hz := hs _ hi
      rw [Nat.testBit_xor, singleBit] at hz
      simpa only [show decide (pick v=i)=false from decide_eq_false (ne i hi), Bool.xor_false] using hz

private structure State where
  pos : Nat
  rev : Nat
  one : Nat
  two : Nat
  deriving DecidableEq

private def add (s : State) (x : Nat) : State :=
  let t := s.pos <<< x
  ⟨s.pos ||| (1 <<< x), s.rev ||| (1 <<< (70-x)),
   s.one ||| t, s.two ||| (s.one &&& t)⟩

private def pairs (s : State) (n : Nat) := s.pos &&& (s.rev >>> (70-n))

private def crowded (s : State) (n : Nat) : Bool :=
  decide (n ≤ 70) && gather 6 (pairs s n)

private def includeStops (s : State) (x : Nat) : Bool :=
  let bad := ((s.pos <<< x) &&& s.two) &&& (2^71-1)
  bad != 0 && crowded (add s x) (pick bad)

/-- Six distinct first coordinates of ordered representations of one sum. -/
def Six (A : Nat → Prop) : Prop :=
  ∃ n ≤ 70, ∃ l : List Nat, l.length = 6 ∧ l.Nodup ∧
    ∀ a ∈ l, ∃ b, A a ∧ A b ∧ a+b=n

private structure Fits (A : Nat → Prop) (x : Nat) (s : State) : Prop where
  complete : ∀ a < x, A a → s.pos.testBit a = true ∧ s.rev.testBit (70-a) = true
  forward : ∀ a, s.pos.testBit a = true → A a
  backward : ∀ i, s.rev.testBit i = true → ∃ b ≤ 70, A b ∧ i = 70-b

private theorem skipFits {A x s} (h : Fits A x s) (hn : ¬A x) : Fits A (x+1) s := by
  refine ⟨?_,h.forward,h.backward⟩
  intro a ha hA
  exact h.complete a (by by_cases z : a=x; exact False.elim (hn (z ▸ hA)); omega) hA

private theorem addFits {A x s} (h : Fits A x s) (hx : x ≤ 70) (ha : A x) :
    Fits A (x+1) (add s x) := by
  refine ⟨?_,?_,?_⟩
  · intro a hv hA
    by_cases hz : a=x
    · subst a
      simp [add,Nat.testBit_or,singleBit]
    · obtain ⟨hp,hr⟩ := h.complete a (by omega) hA
      simp [add,Nat.testBit_or,hp,hr]
  · intro a hb
    simp only [add,Nat.testBit_or,Bool.or_eq_true_iff,singleBit,decide_eq_true_eq] at hb
    rcases hb with hi|rfl
    · exact h.forward _ hi
    · exact ha
  · intro i hb
    simp only [add,Nat.testBit_or,Bool.or_eq_true_iff,singleBit,decide_eq_true_eq] at hb
    rcases hb with hi|rfl
    · exact h.backward _ hi
    · exact ⟨x,hx,ha,rfl⟩

private theorem pairSound {A x s n a} (h : Fits A x s) (hn : n ≤ 70)
    (ha : (pairs s n).testBit a = true) : ∃ b, A a ∧ A b ∧ a+b=n := by
  simp only [pairs,Nat.testBit_and,Nat.testBit_shiftRight,Bool.and_eq_true_iff] at ha
  obtain ⟨b,hb,hA,he⟩ := h.backward _ ha.2
  exact ⟨b,h.forward _ ha.1,hA,by omega⟩

private theorem crowdedSound {A x s n} (h : Fits A x s) (hc : crowded s n = true) : Six A := by
  obtain ⟨hn, hg⟩ := Bool.and_eq_true_iff.mp hc
  have hn' : n ≤ 70 := of_decide_eq_true hn
  obtain ⟨l,hl,hd,hs⟩ := gather_sound hg
  exact ⟨n,hn',l,hl,hd,fun a ha => pairSound h hn' (hs a ha)⟩

private def Covers (A : Nat → Prop) := ∀ n ≤ 70, ∃ a b, A a ∧ A b ∧ a+b=n

private theorem cannotSkip {A x s} (h : Fits A x s) (hx : x ≤ 70) (cov : Covers A)
    (hn : ¬A x) (hz : pairs s x = 0) : False := by
  obtain ⟨a,b,ha,hb,hs⟩ := cov x hx
  have h₁ : a < x := by by_cases e : a=x; exact False.elim (hn (e ▸ ha)); omega
  have h₂ : b < x := by by_cases e : b=x; exact False.elim (hn (e ▸ hb)); omega
  have hp := (h.complete a h₁ ha).1
  have hr := (h.complete b h₂ hb).2
  have he : (70-x)+a=70-b := by omega
  have : (pairs s x).testBit a = true := by simp [pairs,Nat.testBit_shiftRight,he,hp,hr]
  simp [hz] at this

private def check : Nat → Nat → State → Bool
  | 0, _, _ => false
  | k+1, x, s =>
    (includeStops s x || check k (x+1) (add s x)) &&
    (pairs s x == 0 || check k (x+1) s)

private theorem check_sound {A : Nat → Prop} (cov : Covers A) (k x : Nat) (s : State)
    (bound : k+x ≤ 71) (h : Fits A x s) (hc : check k x s = true) : Six A := by
  induction k generalizing x s with
  | zero => contradiction
  | succ k ih =>
    have hx : x ≤ 70 := by omega
    have hh := Bool.and_eq_true_iff.mp hc
    by_cases ha : A x
    · rcases Bool.or_eq_true_iff.mp hh.1 with hp|hr
      · exact crowdedSound (addFits h hx ha) (Bool.and_eq_true_iff.mp hp).2
      · exact ih (x+1) _ (by omega) (addFits h hx ha) hr
    · rcases Bool.or_eq_true_iff.mp hh.2 with hp|hr
      · exact False.elim (cannotSkip h hx cov ha (beq_iff_eq.mp hp))
      · exact ih (x+1) _ (by omega) (skipFits h ha) hr

private def zero : State := ⟨0,0,0,0⟩

private theorem step {k x : Nat} {s : State}
    (hl : includeStops s x = true ∨ check k (x+1) (add s x) = true)
    (hr : pairs s x = 0 ∨ check k (x+1) s = true) : check (k+1) x s = true := by
  apply Bool.and_eq_true_iff.mpr
  exact ⟨Bool.or_eq_true_iff.mpr hl, Bool.or_eq_true_iff.mpr (hr.imp (fun h => beq_iff_eq.mpr h) id)⟩

private theorem part0 : check 62 9 (⟨0x15f,0x7d4000000000000000,0x5ffe,0x7f8⟩ : State) = true := by decide +kernel

private theorem part1 : check 62 9 (⟨0x5f,0x7d0000000000000000,0x7fe,0xf8⟩ : State) = true := by decide +kernel

private theorem part2 : check 63 8 (⟨0x5f,0x7d0000000000000000,0x7fe,0xf8⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x5f,0x7d0000000000000000,0x7fe,0xf8⟩ : State)) (Or.inr part0) (Or.inr part1)

private theorem part3 : check 64 7 (⟨0x5f,0x7d0000000000000000,0x7fe,0xf8⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x5f,0x7d0000000000000000,0x7fe,0xf8⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part2)

private theorem part4 : check 62 9 (⟨0x19f,0x7cc000000000000000,0x9ffe,0xfb8⟩ : State) = true := by decide +kernel

private theorem part5 : check 62 9 (⟨0x9f,0x7c8000000000000000,0xffe,0xb8⟩ : State) = true := by decide +kernel

private theorem part6 : check 63 8 (⟨0x9f,0x7c8000000000000000,0xffe,0xb8⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x9f,0x7c8000000000000000,0xffe,0xb8⟩ : State)) (Or.inr part4) (Or.inr part5)

private theorem part7 : check 62 9 (⟨0x11f,0x7c4000000000000000,0x1ffe,0x38⟩ : State) = true := by decide +kernel

private theorem part8 : check 62 9 (⟨0x1f,0x7c0000000000000000,0xfe,0x38⟩ : State) = true := by decide +kernel

private theorem part9 : check 63 8 (⟨0x1f,0x7c0000000000000000,0xfe,0x38⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x1f,0x7c0000000000000000,0xfe,0x38⟩ : State)) (Or.inr part7) (Or.inr part8)

private theorem part10 : check 64 7 (⟨0x1f,0x7c0000000000000000,0xfe,0x38⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x1f,0x7c0000000000000000,0xfe,0x38⟩ : State)) (Or.inr part6) (Or.inr part9)

private theorem part11 : check 65 6 (⟨0x1f,0x7c0000000000000000,0xfe,0x38⟩ : State) = true := step (k:=64) (x:=6) (s:=(⟨0x1f,0x7c0000000000000000,0xfe,0x38⟩ : State)) (Or.inr part3) (Or.inr part10)

private theorem part12 : check 66 5 (⟨0x1f,0x7c0000000000000000,0xfe,0x38⟩ : State) = true := step (k:=65) (x:=5) (s:=(⟨0x1f,0x7c0000000000000000,0xfe,0x38⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part11)

private theorem part13 : check 62 9 (⟨0x6f,0x7b0000000000000000,0xbfe,0x1e8⟩ : State) = true := by decide +kernel

private theorem part14 : check 63 8 (⟨0x6f,0x7b0000000000000000,0xbfe,0x1e8⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x6f,0x7b0000000000000000,0xbfe,0x1e8⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part13)

private theorem part15 : check 64 7 (⟨0x6f,0x7b0000000000000000,0xbfe,0x1e8⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x6f,0x7b0000000000000000,0xbfe,0x1e8⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part14)

private theorem part16 : check 62 9 (⟨0xaf,0x7a8000000000000000,0x17fe,0x1a8⟩ : State) = true := by decide +kernel

private theorem part17 : check 63 8 (⟨0xaf,0x7a8000000000000000,0x17fe,0x1a8⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0xaf,0x7a8000000000000000,0x17fe,0x1a8⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part16)

private theorem part18 : check 62 9 (⟨0x12f,0x7a4000000000000000,0x2ffe,0x128⟩ : State) = true := by decide +kernel

private theorem part19 : check 62 9 (⟨0x2f,0x7a0000000000000000,0x1fe,0x28⟩ : State) = true := by decide +kernel

private theorem part20 : check 63 8 (⟨0x2f,0x7a0000000000000000,0x1fe,0x28⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x2f,0x7a0000000000000000,0x1fe,0x28⟩ : State)) (Or.inr part18) (Or.inr part19)

private theorem part21 : check 64 7 (⟨0x2f,0x7a0000000000000000,0x1fe,0x28⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x2f,0x7a0000000000000000,0x1fe,0x28⟩ : State)) (Or.inr part17) (Or.inr part20)

private theorem part22 : check 65 6 (⟨0x2f,0x7a0000000000000000,0x1fe,0x28⟩ : State) = true := step (k:=64) (x:=6) (s:=(⟨0x2f,0x7a0000000000000000,0x1fe,0x28⟩ : State)) (Or.inr part15) (Or.inr part21)

private theorem part23 : check 62 9 (⟨0xcf,0x798000000000000000,0x27fe,0x388⟩ : State) = true := by decide +kernel

private theorem part24 : check 63 8 (⟨0xcf,0x798000000000000000,0x27fe,0x388⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0xcf,0x798000000000000000,0x27fe,0x388⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part23)

private theorem part25 : check 62 9 (⟨0x14f,0x794000000000000000,0x4ffe,0x308⟩ : State) = true := by decide +kernel

private theorem part26 : check 62 9 (⟨0x4f,0x790000000000000000,0x3fe,0x8⟩ : State) = true := by decide +kernel

private theorem part27 : check 63 8 (⟨0x4f,0x790000000000000000,0x3fe,0x8⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x4f,0x790000000000000000,0x3fe,0x8⟩ : State)) (Or.inr part25) (Or.inr part26)

private theorem part28 : check 64 7 (⟨0x4f,0x790000000000000000,0x3fe,0x8⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x4f,0x790000000000000000,0x3fe,0x8⟩ : State)) (Or.inr part24) (Or.inr part27)

private theorem part29 : check 62 9 (⟨0x18f,0x78c000000000000000,0x8fbe,0x708⟩ : State) = true := by decide +kernel

private theorem part30 : check 62 9 (⟨0x8f,0x788000000000000000,0x7be,0x8⟩ : State) = true := by decide +kernel

private theorem part31 : check 63 8 (⟨0x8f,0x788000000000000000,0x7be,0x8⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x8f,0x788000000000000000,0x7be,0x8⟩ : State)) (Or.inr part29) (Or.inr part30)

private theorem part32 : check 64 7 (⟨0xf,0x780000000000000000,0x3e,0x8⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0xf,0x780000000000000000,0x3e,0x8⟩ : State)) (Or.inr part31) (Or.inl (by decide +kernel))

private theorem part33 : check 65 6 (⟨0xf,0x780000000000000000,0x3e,0x8⟩ : State) = true := step (k:=64) (x:=6) (s:=(⟨0xf,0x780000000000000000,0x3e,0x8⟩ : State)) (Or.inr part28) (Or.inr part32)

private theorem part34 : check 66 5 (⟨0xf,0x780000000000000000,0x3e,0x8⟩ : State) = true := step (k:=65) (x:=5) (s:=(⟨0xf,0x780000000000000000,0x3e,0x8⟩ : State)) (Or.inr part22) (Or.inr part33)

private theorem part35 : check 67 4 (⟨0xf,0x780000000000000000,0x3e,0x8⟩ : State) = true := step (k:=66) (x:=4) (s:=(⟨0xf,0x780000000000000000,0x3e,0x8⟩ : State)) (Or.inr part12) (Or.inr part34)

private theorem part36 : check 62 9 (⟨0xb7,0x768000000000000000,0x1bfe,0x2e0⟩ : State) = true := by decide +kernel

private theorem part37 : check 63 8 (⟨0xb7,0x768000000000000000,0x1bfe,0x2e0⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0xb7,0x768000000000000000,0x1bfe,0x2e0⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part36)

private theorem part38 : check 62 9 (⟨0x137,0x764000000000000000,0x37fe,0x260⟩ : State) = true := by decide +kernel

private theorem part39 : check 62 9 (⟨0x37,0x760000000000000000,0x2fe,0x60⟩ : State) = true := by decide +kernel

private theorem part40 : check 63 8 (⟨0x37,0x760000000000000000,0x2fe,0x60⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x37,0x760000000000000000,0x2fe,0x60⟩ : State)) (Or.inr part38) (Or.inr part39)

private theorem part41 : check 64 7 (⟨0x37,0x760000000000000000,0x2fe,0x60⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x37,0x760000000000000000,0x2fe,0x60⟩ : State)) (Or.inr part37) (Or.inr part40)

private theorem part42 : check 65 6 (⟨0x37,0x760000000000000000,0x2fe,0x60⟩ : State) = true := step (k:=64) (x:=6) (s:=(⟨0x37,0x760000000000000000,0x2fe,0x60⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part41)

private theorem part43 : check 62 9 (⟨0xd7,0x758000000000000000,0x2ffe,0x1c0⟩ : State) = true := by decide +kernel

private theorem part44 : check 63 8 (⟨0xd7,0x758000000000000000,0x2ffe,0x1c0⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0xd7,0x758000000000000000,0x2ffe,0x1c0⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part43)

private theorem part45 : check 62 9 (⟨0x157,0x754000000000000000,0x57fe,0x540⟩ : State) = true := by decide +kernel

private theorem part46 : check 62 9 (⟨0x57,0x750000000000000000,0x5fe,0x40⟩ : State) = true := by decide +kernel

private theorem part47 : check 63 8 (⟨0x57,0x750000000000000000,0x5fe,0x40⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x57,0x750000000000000000,0x5fe,0x40⟩ : State)) (Or.inr part45) (Or.inr part46)

private theorem part48 : check 64 7 (⟨0x57,0x750000000000000000,0x5fe,0x40⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x57,0x750000000000000000,0x5fe,0x40⟩ : State)) (Or.inr part44) (Or.inr part47)

private theorem part49 : check 62 9 (⟨0x197,0x74c000000000000000,0x9ffe,0x300⟩ : State) = true := by decide +kernel

private theorem part50 : check 62 9 (⟨0x97,0x748000000000000000,0xbfe,0x0⟩ : State) = true := by decide +kernel

private theorem part51 : check 63 8 (⟨0x97,0x748000000000000000,0xbfe,0x0⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x97,0x748000000000000000,0xbfe,0x0⟩ : State)) (Or.inr part49) (Or.inr part50)

private theorem part52 : check 64 7 (⟨0x17,0x740000000000000000,0x7e,0x0⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x17,0x740000000000000000,0x7e,0x0⟩ : State)) (Or.inr part51) (Or.inl (by decide +kernel))

private theorem part53 : check 65 6 (⟨0x17,0x740000000000000000,0x7e,0x0⟩ : State) = true := step (k:=64) (x:=6) (s:=(⟨0x17,0x740000000000000000,0x7e,0x0⟩ : State)) (Or.inr part48) (Or.inr part52)

private theorem part54 : check 66 5 (⟨0x17,0x740000000000000000,0x7e,0x0⟩ : State) = true := step (k:=65) (x:=5) (s:=(⟨0x17,0x740000000000000000,0x7e,0x0⟩ : State)) (Or.inr part42) (Or.inr part53)

private theorem part55 : check 62 9 (⟨0x167,0x734000000000000000,0x6fee,0x1c0⟩ : State) = true := by decide +kernel

private theorem part56 : check 62 9 (⟨0x67,0x730000000000000000,0x9ee,0xc0⟩ : State) = true := by decide +kernel

private theorem part57 : check 63 8 (⟨0x67,0x730000000000000000,0x9ee,0xc0⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x67,0x730000000000000000,0x9ee,0xc0⟩ : State)) (Or.inr part55) (Or.inr part56)

private theorem part58 : check 64 7 (⟨0x67,0x730000000000000000,0x9ee,0xc0⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x67,0x730000000000000000,0x9ee,0xc0⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part57)

private theorem part59 : check 62 9 (⟨0x1a7,0x72c000000000000000,0xb7ee,0x380⟩ : State) = true := by decide +kernel

private theorem part60 : check 62 9 (⟨0xa7,0x728000000000000000,0x13ee,0x80⟩ : State) = true := by decide +kernel

private theorem part61 : check 63 8 (⟨0xa7,0x728000000000000000,0x13ee,0x80⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0xa7,0x728000000000000000,0x13ee,0x80⟩ : State)) (Or.inr part59) (Or.inr part60)

private theorem part62 : check 62 9 (⟨0x127,0x724000000000000000,0x27ee,0x0⟩ : State) = true := by decide +kernel

private theorem part63 : check 63 8 (⟨0x27,0x720000000000000000,0xee,0x0⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x27,0x720000000000000000,0xee,0x0⟩ : State)) (Or.inr part62) (Or.inl (by decide +kernel))

private theorem part64 : check 64 7 (⟨0x27,0x720000000000000000,0xee,0x0⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x27,0x720000000000000000,0xee,0x0⟩ : State)) (Or.inr part61) (Or.inr part63)

private theorem part65 : check 65 6 (⟨0x27,0x720000000000000000,0xee,0x0⟩ : State) = true := step (k:=64) (x:=6) (s:=(⟨0x27,0x720000000000000000,0xee,0x0⟩ : State)) (Or.inr part58) (Or.inr part64)

private theorem part66 : check 66 5 (⟨0x7,0x700000000000000000,0xe,0x0⟩ : State) = true := step (k:=65) (x:=5) (s:=(⟨0x7,0x700000000000000000,0xe,0x0⟩ : State)) (Or.inr part65) (Or.inl (by decide +kernel))

private theorem part67 : check 67 4 (⟨0x7,0x700000000000000000,0xe,0x0⟩ : State) = true := step (k:=66) (x:=4) (s:=(⟨0x7,0x700000000000000000,0xe,0x0⟩ : State)) (Or.inr part54) (Or.inr part66)

private theorem part68 : check 68 3 (⟨0x7,0x700000000000000000,0xe,0x0⟩ : State) = true := step (k:=67) (x:=3) (s:=(⟨0x7,0x700000000000000000,0xe,0x0⟩ : State)) (Or.inr part35) (Or.inr part67)

private theorem part69 : check 62 9 (⟨0x7b,0x6f0000000000000000,0xffa,0x2f0⟩ : State) = true := by decide +kernel

private theorem part70 : check 63 8 (⟨0x7b,0x6f0000000000000000,0xffa,0x2f0⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x7b,0x6f0000000000000000,0xffa,0x2f0⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part69)

private theorem part71 : check 64 7 (⟨0x7b,0x6f0000000000000000,0xffa,0x2f0⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x7b,0x6f0000000000000000,0xffa,0x2f0⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part70)

private theorem part72 : check 62 9 (⟨0xbb,0x6e8000000000000000,0x1ffa,0x1b0⟩ : State) = true := by decide +kernel

private theorem part73 : check 63 8 (⟨0xbb,0x6e8000000000000000,0x1ffa,0x1b0⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0xbb,0x6e8000000000000000,0x1ffa,0x1b0⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part72)

private theorem part74 : check 62 9 (⟨0x13b,0x6e4000000000000000,0x3bfa,0x330⟩ : State) = true := by decide +kernel

private theorem part75 : check 62 9 (⟨0x3b,0x6e0000000000000000,0x3fa,0x30⟩ : State) = true := by decide +kernel

private theorem part76 : check 63 8 (⟨0x3b,0x6e0000000000000000,0x3fa,0x30⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x3b,0x6e0000000000000000,0x3fa,0x30⟩ : State)) (Or.inr part74) (Or.inr part75)

private theorem part77 : check 64 7 (⟨0x3b,0x6e0000000000000000,0x3fa,0x30⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x3b,0x6e0000000000000000,0x3fa,0x30⟩ : State)) (Or.inr part73) (Or.inr part76)

private theorem part78 : check 65 6 (⟨0x3b,0x6e0000000000000000,0x3fa,0x30⟩ : State) = true := step (k:=64) (x:=6) (s:=(⟨0x3b,0x6e0000000000000000,0x3fa,0x30⟩ : State)) (Or.inr part71) (Or.inr part77)

private theorem part79 : check 62 9 (⟨0x15b,0x6d4000000000000000,0x5ffa,0x290⟩ : State) = true := by decide +kernel

private theorem part80 : check 62 9 (⟨0x5b,0x6d0000000000000000,0x6fa,0x90⟩ : State) = true := by decide +kernel

private theorem part81 : check 63 8 (⟨0x5b,0x6d0000000000000000,0x6fa,0x90⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x5b,0x6d0000000000000000,0x6fa,0x90⟩ : State)) (Or.inr part79) (Or.inr part80)

private theorem part82 : check 64 7 (⟨0x5b,0x6d0000000000000000,0x6fa,0x90⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x5b,0x6d0000000000000000,0x6fa,0x90⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part81)

private theorem part83 : check 62 9 (⟨0x19b,0x6cc000000000000000,0x9fba,0x990⟩ : State) = true := by decide +kernel

private theorem part84 : check 62 9 (⟨0x9b,0x6c8000000000000000,0xdba,0x90⟩ : State) = true := by decide +kernel

private theorem part85 : check 63 8 (⟨0x9b,0x6c8000000000000000,0xdba,0x90⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x9b,0x6c8000000000000000,0xdba,0x90⟩ : State)) (Or.inr part83) (Or.inr part84)

private theorem part86 : check 62 9 (⟨0x11b,0x6c4000000000000000,0x1bba,0x10⟩ : State) = true := by decide +kernel

private theorem part87 : check 62 9 (⟨0x1b,0x6c0000000000000000,0xba,0x10⟩ : State) = true := by decide +kernel

private theorem part88 : check 63 8 (⟨0x1b,0x6c0000000000000000,0xba,0x10⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x1b,0x6c0000000000000000,0xba,0x10⟩ : State)) (Or.inr part86) (Or.inr part87)

private theorem part89 : check 64 7 (⟨0x1b,0x6c0000000000000000,0xba,0x10⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x1b,0x6c0000000000000000,0xba,0x10⟩ : State)) (Or.inr part85) (Or.inr part88)

private theorem part90 : check 65 6 (⟨0x1b,0x6c0000000000000000,0xba,0x10⟩ : State) = true := step (k:=64) (x:=6) (s:=(⟨0x1b,0x6c0000000000000000,0xba,0x10⟩ : State)) (Or.inr part82) (Or.inr part89)

private theorem part91 : check 66 5 (⟨0x1b,0x6c0000000000000000,0xba,0x10⟩ : State) = true := step (k:=65) (x:=5) (s:=(⟨0x1b,0x6c0000000000000000,0xba,0x10⟩ : State)) (Or.inr part78) (Or.inr part90)

private theorem part92 : check 62 9 (⟨0xeb,0x6b8000000000000000,0x3ffa,0x1c0⟩ : State) = true := by decide +kernel

private theorem part93 : check 63 8 (⟨0xeb,0x6b8000000000000000,0x3ffa,0x1c0⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0xeb,0x6b8000000000000000,0x3ffa,0x1c0⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part92)

private theorem part94 : check 62 9 (⟨0x16b,0x6b4000000000000000,0x6bfa,0xb40⟩ : State) = true := by decide +kernel

private theorem part95 : check 62 9 (⟨0x6b,0x6b0000000000000000,0xbfa,0x40⟩ : State) = true := by decide +kernel

private theorem part96 : check 63 8 (⟨0x6b,0x6b0000000000000000,0xbfa,0x40⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0x6b,0x6b0000000000000000,0xbfa,0x40⟩ : State)) (Or.inr part94) (Or.inr part95)

private theorem part97 : check 64 7 (⟨0x6b,0x6b0000000000000000,0xbfa,0x40⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x6b,0x6b0000000000000000,0xbfa,0x40⟩ : State)) (Or.inr part93) (Or.inr part96)

private theorem part98 : check 62 9 (⟨0xab,0x6a8000000000000000,0x15fa,0x100⟩ : State) = true := by decide +kernel

private theorem part99 : check 63 8 (⟨0xab,0x6a8000000000000000,0x15fa,0x100⟩ : State) = true := step (k:=62) (x:=8) (s:=(⟨0xab,0x6a8000000000000000,0x15fa,0x100⟩ : State)) (Or.inl (by decide +kernel)) (Or.inr part98)

private theorem part100 : check 64 7 (⟨0x2b,0x6a0000000000000000,0x17a,0x0⟩ : State) = true := step (k:=63) (x:=7) (s:=(⟨0x2b,0x6a0000000000000000,0x17a,0x0⟩ : State)) (Or.inr part99) (Or.inl (by decide +kernel))

private theorem part101 : check 65 6 (⟨0x2b,0x6a0000000000000000,0x17a,0x0⟩ : State) = true := step (k:=64) (x:=6) (s:=(⟨0x2b,0x6a0000000000000000,0x17a,0x0⟩ : State)) (Or.inr part97) (Or.inr part100)

private theorem part102 : check 66 5 (⟨0xb,0x680000000000000000,0x1a,0x0⟩ : State) = true := step (k:=65) (x:=5) (s:=(⟨0xb,0x680000000000000000,0x1a,0x0⟩ : State)) (Or.inr part101) (Or.inl (by decide +kernel))

private theorem part103 : check 67 4 (⟨0xb,0x680000000000000000,0x1a,0x0⟩ : State) = true := step (k:=66) (x:=4) (s:=(⟨0xb,0x680000000000000000,0x1a,0x0⟩ : State)) (Or.inr part91) (Or.inr part102)

private theorem part104 : check 68 3 (⟨0x3,0x600000000000000000,0x2,0x0⟩ : State) = true := step (k:=67) (x:=3) (s:=(⟨0x3,0x600000000000000000,0x2,0x0⟩ : State)) (Or.inr part103) (Or.inl (by decide +kernel))

private theorem part105 : check 69 2 (⟨0x3,0x600000000000000000,0x2,0x0⟩ : State) = true := step (k:=68) (x:=2) (s:=(⟨0x3,0x600000000000000000,0x2,0x0⟩ : State)) (Or.inr part68) (Or.inr part104)

private theorem part106 : check 70 1 (⟨0x1,0x400000000000000000,0x0,0x0⟩ : State) = true := step (k:=69) (x:=1) (s:=(⟨0x1,0x400000000000000000,0x0,0x0⟩ : State)) (Or.inr part105) (Or.inl (by decide +kernel))

private theorem part107 : check 71 0 (⟨0x0,0x0,0x0,0x0⟩ : State) = true := step (k:=70) (x:=0) (s:=(⟨0x0,0x0,0x0,0x0⟩ : State)) (Or.inr part106) (Or.inl (by decide +kernel))

private theorem checked : check 71 0 zero = true := part107

theorem six_of_cover (A : Nat → Prop) (h : ∀ n ≤ 70, ∃ a b, A a ∧ A b ∧ a+b=n) : Six A := by
  apply check_sound h 71 0 zero (by decide) _ checked
  exact ⟨by simp,by simp [zero],by simp [zero]⟩

end OMA.Erdos28Five

namespace OMA.Erdos28Five

theorem five_lt_count (S : Finset Nat)
    (cov : ∀ n ≤ 70, ∃ a ∈ S, ∃ b ∈ S, a+b=n) :
    ∃ n ≤ 70, 5 < ((Finset.HasAntidiagonal.antidiagonal n).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card := by
  obtain ⟨n,hn,l,hl,hd,hw⟩ := six_of_cover (fun a => a ∈ S) (by
    intro n hn
    obtain ⟨a,ha,b,hb,he⟩ := cov n hn
    exact ⟨a,b,ha,hb,he⟩)
  let f : Nat → Nat × Nat := fun a => (a,n-a)
  have fi : Function.Injective f := fun _ _ h => congrArg Prod.fst h
  have card := Finset.card_image_of_injective l.toFinset fi
  rw [List.toFinset_card_of_nodup hd, hl] at card
  have sub : l.toFinset.image f ⊆ (Finset.HasAntidiagonal.antidiagonal n).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, h₁, h₂, he⟩ := hw a (List.mem_toFinset.mp ha)
    have hb : n-a=b := by omega
    exact Finset.mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by change a+(n-a)=n; omega),
      h₁, by change n-a ∈ S; simpa only [hb] using h₂⟩
  have hb := Finset.card_le_card sub
  exact ⟨n,hn,by omega⟩

end OMA.Erdos28Five

namespace OMA.Erdos28Endpoint

/-- A cover of 0 through 69 with at most five ordered representations per sum. -/
def lastCover : Finset ℕ :=
  {0, 1, 3, 4, 5, 6, 10, 15, 17, 23, 31, 39, 47, 55, 63}

def countAt (n : ℕ) : ℕ :=
  ((Finset.HasAntidiagonal.antidiagonal n).filter (fun p => p.1 ∈ lastCover ∧ p.2 ∈ lastCover)).card

set_option maxRecDepth 8000 in
set_option maxHeartbeats 9000000 in
theorem last_counts : ∀ n : Fin 70, 0 < countAt n ∧ countAt n ≤ 5 := by
  decide

theorem last_subset : lastCover ⊆ Finset.Iic 69 := by decide

theorem last_covers (n : ℕ) (hn : n ≤ 69) :
    ∃ a ∈ lastCover, ∃ b ∈ lastCover, a+b=n := by
  have h := (last_counts ⟨n, by omega⟩).1
  change 0 < ((Finset.HasAntidiagonal.antidiagonal n).filter
    (fun p => p.1 ∈ lastCover ∧ p.2 ∈ lastCover)).card at h
  obtain ⟨p,hp⟩ := Finset.card_pos.mp h
  obtain ⟨hs, ha, hb⟩ := Finset.mem_filter.mp hp
  exact ⟨p.1, ha, p.2, hb, Finset.HasAntidiagonal.mem_antidiagonal.mp hs⟩

end OMA.Erdos28Endpoint


theorem OMA.solution : OMA.R_Erdos28_erdos_28_R1_H1_R1.H1 := by
  classical
  intro S _ cov
  obtain ⟨n,hn,hs⟩ := OMA.Erdos28Five.five_lt_count S cov
  exact ⟨n,hn,by simpa only [AdditiveCombinatorics.sumRep_def, Finset.mem_coe] using hs⟩
