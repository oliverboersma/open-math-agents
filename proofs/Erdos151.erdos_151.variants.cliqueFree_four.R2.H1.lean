import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R2
import Mathlib

/-! Erdős 151 for four-clique-free graphs with independence threshold at most nine.
Proof and finite certificates by @princek0. A triangle-free colored link on at
most seven vertices always extends over its center. A minimal triangle-Ramsey
subgraph therefore has minimum positive degree eight. At order at least 26,
a weighted incidence count extends one such core neighborhood to nine vertices
unless a larger ambient neighborhood already supplies the bound. At smaller
orders an explicit 25-vertex triangle-free circulant gives threshold at most eight. -/


namespace Erdos151Research.ThresholdNine
open SimpleGraph

/-- The extremal size in the definition of H is attained. -/
theorem independent_at_threshold (n : ℕ) (F : SimpleGraph (Fin n)) (tf : F.CliqueFree 3) :
    ∃ T, F.IsNIndepSet (Erdos151.H n) T := by
  let sizes : Set ℕ := {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ T, G.IsNIndepSet k T}
  have zero : 0 ∈ sizes := fun G _ => ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩
  have limited : sizes ⊆ Set.Iic n := by
    intro k hk
    obtain ⟨T,hT⟩ := hk F tf
    simpa [hT.card_eq] using Finset.card_le_univ T
  have member : Erdos151.H n ∈ sizes := (show sizes.Nonempty from ⟨0,zero⟩).csSup_mem ((Set.finite_Iic n).subset limited)
  exact member F tf

/-- An independent set in the hitting graph avoids every prohibited clique. -/
theorem bound_of_hitting (n : ℕ) (G F : SimpleGraph (Fin n)) (tf : F.CliqueFree 3)
    (hit : ∀ Q, G.IsBigMaximalClique Q → ∃ x ∈ Q, ∃ y ∈ Q, F.Adj x y) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  obtain ⟨T,chosen⟩ := independent_at_threshold n F tf
  have cover : G.IsCliqueTransversal Tᶜ := by
    intro Q maximal
    obtain ⟨x,hx,y,hy,edge⟩ := hit Q maximal
    by_cases xT : x ∈ T
    · exact ⟨y,hy,Finset.mem_compl.mpr (fun yT => chosen.isIndepSet xT yT edge.ne edge)⟩
    · exact ⟨x,hx,Finset.mem_compl.mpr xT⟩
  exact csInf_le' ⟨Tᶜ,cover,by rw [Finset.card_compl,Fintype.card_fin,chosen.card_eq]⟩

end Erdos151Research.ThresholdNine


/-! A kernel-checked certificate for seven-vertex triangle-free edge-coloured links. -/
namespace Erdos151Local.Link7

def pairs : Array (Fin 7 × Fin 7) := #[(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (1,2), (1,3), (1,4), (1,5), (1,6), (2,3), (2,4), (2,5), (2,6), (3,4), (3,5), (3,6), (4,5), (4,6), (5,6)]
def triples : Array (Fin 7 × Fin 7 × Fin 7) := #[(0,1,2), (0,1,3), (0,1,4), (0,1,5), (0,1,6), (0,2,3), (0,2,4), (0,2,5), (0,2,6), (0,3,4), (0,3,5), (0,3,6), (0,4,5), (0,4,6), (0,5,6), (1,2,3), (1,2,4), (1,2,5), (1,2,6), (1,3,4), (1,3,5), (1,3,6), (1,4,5), (1,4,6), (1,5,6), (2,3,4), (2,3,5), (2,3,6), (2,4,5), (2,4,6), (2,5,6), (3,4,5), (3,4,6), (3,5,6), (4,5,6)]
def triMasks : Array Nat := #[67, 133, 265, 529, 1057, 2054, 4106, 8210, 16418, 32780, 65556, 131108, 262168, 524328, 1048624, 2240, 4416, 8768, 17472, 33152, 66176, 132224, 262912, 525568, 1050112, 38912, 75776, 149504, 274432, 544768, 1073152, 360448, 688128, 1245184, 1835008]
def redMasks : Array Nat := #[0, 0, 0, 1, 0, 2, 64, 67, 0, 4, 128, 133, 2048, 2054, 2240, 2247, 0, 8, 256, 265, 4096, 4106, 4416, 4427, 32768, 32780, 33152, 33165, 38912, 38926, 39360, 39375, 0, 16, 512, 529, 8192, 8210, 8768, 8787, 65536, 65556, 66176, 66197, 75776, 75798, 76480, 76503, 262144, 262168, 262912, 262937, 274432, 274458, 275264, 275291, 360448, 360476, 361344, 361373, 374784, 374814, 375744, 375775, 0, 32, 1024, 1057, 16384, 16418, 17472, 17507, 131072, 131108, 132224, 132261, 149504, 149542, 150720, 150759, 524288, 524328, 525568, 525609, 544768, 544810, 546112, 546155, 688128, 688172, 689536, 689581, 710656, 710702, 712128, 712175, 1048576, 1048624, 1050112, 1050161, 1073152, 1073202, 1074752, 1074803, 1245184, 1245236, 1246848, 1246901, 1271808, 1271862, 1273536, 1273591, 1835008, 1835064, 1836800, 1836857, 1863680, 1863738, 1865536, 1865595, 2064384, 2064444, 2066304, 2066365, 2095104, 2095166, 2097088, 2097151]

inductive Certificate where
  | triangle (index : Nat)
  | witness (vertices : Nat)
  | edge (index : Nat) (yes no : Certificate)
  | color (index : Nat) (yes no : Certificate)

def subsetB (s t : Nat) : Bool := s &&& t == s

def check (tree : Certificate) (edges nonedges reds blues : Nat) : Bool :=
  match tree with
  | .triangle j => decide (j < 35) && subsetB triMasks[j]! edges
  | .witness c => decide (c < 128) && subsetB redMasks[c]! (nonedges ||| blues) &&
      subsetB redMasks[127 ^^^ c]! (nonedges ||| reds)
  | .edge i yes no => check yes (edges ||| 2^i) nonedges reds blues &&
      check no edges (nonedges ||| 2^i) reds blues
  | .color i yes no => check yes edges nonedges (reds ||| 2^i) blues &&
      check no edges nonedges reds (blues ||| 2^i)

def Holds (s : Nat) (f : Nat → Bool) (b : Bool) : Prop :=
  ∀ i, s.testBit i = true → f i = b

private theorem subset_sound {s t : Nat} (h : subsetB s t = true) {i : Nat}
    (hi : s.testBit i = true) : t.testBit i = true := by
  have e : s &&& t = s := by simpa [subsetB] using h
  have := congrArg (fun n : Nat => n.testBit i) e
  simpa [hi] using this

private theorem hold_or {s : Nat} {f : Nat → Bool} {b : Bool} (h : Holds s f b)
    (i : Nat) (hi : f i = b) : Holds (s ||| 2^i) f b := by
  intro j hj
  rw [Nat.testBit_or, Bool.or_eq_true] at hj
  obtain hj | hj := hj
  · exact h j hj
  · have hij : i = j := by simpa [Nat.testBit_two_pow] using hj
    simpa [← hij] using hi

def Good (g red : Nat → Bool) (c : Nat) : Prop :=
  (∀ i, redMasks[c]!.testBit i = true → g i = true → red i = false) ∧
  (∀ i, redMasks[127 ^^^ c]!.testBit i = true → g i = true → red i = true)

def TriangleFree (g : Nat → Bool) : Prop :=
  ∀ j : Fin 35, ¬ Holds triMasks[j.val]! g true

private theorem check_sound (tree : Certificate) (g red : Nat → Bool)
    (ht : TriangleFree g) (edges nonedges reds blues : Nat)
    (hp : Holds edges g true) (ha : Holds nonedges g false)
    (hr : Holds reds red true) (hb : Holds blues red false)
    (h : check tree edges nonedges reds blues = true) :
    ∃ c : Fin 128, Good g red c.val := by
  induction tree generalizing edges nonedges reds blues with
  | triangle j =>
    obtain ⟨hj, hsub⟩ := Bool.and_eq_true_iff.mp h
    apply False.elim (ht ⟨j, of_decide_eq_true hj⟩ ?_)
    intro i hi
    exact hp i (subset_sound hsub hi)
  | witness c =>
    obtain ⟨h1, hn⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hc, hpairs⟩ := Bool.and_eq_true_iff.mp h1
    refine ⟨⟨c, of_decide_eq_true hc⟩, ?_, ?_⟩
    · intro i hm hg
      have hi := subset_sound hpairs hm
      rw [Nat.testBit_or, Bool.or_eq_true] at hi
      exact hi.elim (fun h0 => by simp [ha i h0] at hg) (hb i)
    · intro i hm hg
      have hi := subset_sound hn hm
      rw [Nat.testBit_or, Bool.or_eq_true] at hi
      exact hi.elim (fun h0 => by simp [ha i h0] at hg) (hr i)
  | edge i yes no y n =>
    obtain ⟨hy,hn⟩ := Bool.and_eq_true_iff.mp h
    cases e : g i with
    | false => exact n _ _ _ _ hp (hold_or ha i e) hr hb hn
    | true => exact y _ _ _ _ (hold_or hp i e) ha hr hb hy
  | color i yes no y n =>
    obtain ⟨hy,hn⟩ := Bool.and_eq_true_iff.mp h
    cases e : red i with
    | false => exact n _ _ _ _ hp ha hr (hold_or hb i e) hn
    | true => exact y _ _ _ _ hp ha (hold_or hr i e) hb hy

private def n2 : Certificate := (.triangle 5)
private def n3 : Certificate := (.triangle 2)
private def n4 : Certificate := (.triangle 6)
private def n5 : Certificate := (.triangle 9)
private def n6 : Certificate := (.triangle 3)
private def n7 : Certificate := (.triangle 7)
private def n8 : Certificate := (.triangle 10)
private def n9 : Certificate := (.triangle 12)
private def n10 : Certificate := (.triangle 4)
private def n11 : Certificate := (.triangle 8)
private def n12 : Certificate := (.triangle 11)
private def n13 : Certificate := (.witness 62)
private def n18 : Certificate := (.edge 10 n10 (.edge 14 n11 (.edge 17 n12 (.color 5 n13 (.witness 65)))))
private def n24 : Certificate := (.witness 78)
private def n28 : Certificate := (.color 18 n24 (.color 19 (.witness 33) (.witness 94)))
private def n29 : Certificate := (.witness 49)
private def n30 : Certificate := (.color 18 (.color 19 (.witness 33) (.witness 94)) n29)
private def n35 : Certificate := (.triangle 24)
private def n36 : Certificate := (.triangle 30)
private def n37 : Certificate := (.witness 30)
private def n38 : Certificate := (.witness 97)
private def n39 : Certificate := (.color 20 (.witness 30) (.witness 97))
private def n43 : Certificate := (.edge 14 n36 (.color 17 (.color 19 (.witness 33) n39) (.color 19 n39 (.witness 94))))
private def n44 : Certificate := (.triangle 33)
private def n47 : Certificate := (.color 18 (.witness 65) n39)
private def n48 : Certificate := (.color 18 n39 n13)
private def n50 : Certificate := (.edge 16 (.edge 17 n44 (.color 14 (.color 19 (.witness 33) n39) (.color 19 n39 (.witness 94)))) (.color 9 n47 n48))
private def n56 : Certificate := (.edge 16 (.edge 17 n44 (.color 10 (.color 19 (.witness 33) n39) (.color 19 n39 (.witness 94)))) (.color 13 n47 n48))
private def n65 : Certificate := (.edge 12 n4 (.edge 15 n5 (.edge 4 (.edge 9 n6 (.edge 13 n7 (.edge 16 n8 (.edge 18 n9 (.edge 5 n18 n13))))) (.edge 5 (.edge 10 n10 (.edge 14 n11 (.edge 17 n12 (.color 3 n28 n30)))) (.edge 20 (.edge 9 (.edge 10 n35 (.edge 13 n43 n50)) (.edge 13 (.edge 14 n36 n56) (.color 16 n47 n48))) n37)))))
private def n70 : Certificate := (.color 18 n24 (.color 20 (.witness 17) (.witness 110)))
private def n71 : Certificate := (.color 18 (.color 20 (.witness 17) (.witness 110)) n29)
private def n76 : Certificate := (.triangle 23)
private def n77 : Certificate := (.triangle 29)
private def n78 : Certificate := (.witness 46)
private def n79 : Certificate := (.witness 81)
private def n80 : Certificate := (.color 19 (.witness 46) (.witness 81))
private def n82 : Certificate := (.edge 14 n77 (.color 17 n80 n80))
private def n83 : Certificate := (.triangle 32)
private def n86 : Certificate := (.color 18 (.witness 65) n80)
private def n87 : Certificate := (.color 18 n80 n13)
private def n89 : Certificate := (.edge 15 (.edge 17 n83 (.color 14 n80 n80)) (.color 8 n86 n87))
private def n95 : Certificate := (.edge 15 (.edge 17 n83 (.color 10 n80 n80)) (.color 12 n86 n87))
private def n104 : Certificate := (.edge 9 n6 (.edge 13 n7 (.edge 16 n8 (.edge 5 (.edge 10 n10 (.edge 14 n11 (.edge 17 n12 (.color 4 n70 n71)))) (.edge 19 (.edge 8 (.edge 10 n76 (.edge 12 n82 n89)) (.edge 12 (.edge 14 n77 n95) (.color 15 n86 n87))) n78)))))
private def n105 : Certificate := (.triangle 22)
private def n106 : Certificate := (.triangle 28)
private def n107 : Certificate := (.color 18 (.witness 78) (.witness 49))
private def n109 : Certificate := (.edge 13 n106 (.color 16 n107 n107))
private def n110 : Certificate := (.triangle 31)
private def n114 : Certificate := (.edge 15 (.edge 16 n110 (.color 13 n107 n107)) (.color 8 n107 n107))
private def n120 : Certificate := (.edge 15 (.edge 16 n110 (.color 9 n107 n107)) (.color 12 n107 n107))
private def n129 : Certificate := (.triangle 34)
private def n138 : Certificate := (.color 2 (.witness 102) (.witness 25))
private def n145 : Certificate := (.edge 13 n106 (.edge 14 n77 (.edge 15 (.edge 16 n110 (.color 2 (.color 15 (.witness 102) (.color 17 (.witness 17) (.witness 110))) (.color 15 (.color 17 (.witness 17) (.witness 110)) (.witness 25)))) (.color 0 (.color 1 (.witness 24) n138) (.color 1 n138 (.witness 103))))))
private def n148 : Certificate := (.color 1 (.witness 106) (.witness 21))
private def n152 : Certificate := (.witness 28)
private def n153 : Certificate := (.witness 99)
private def n154 : Certificate := (.color 0 (.witness 28) (.witness 99))
private def n155 : Certificate := (.edge 15 (.edge 16 n110 (.edge 17 n83 (.color 0 n148 n148))) n154)
private def n161 : Certificate := (.color 0 (.witness 108) (.witness 19))
private def n163 : Certificate := (.edge 16 n110 (.edge 17 n83 n161))
private def n164 : Certificate := (.witness 26)
private def n165 : Certificate := (.witness 101)
private def n166 : Certificate := (.color 1 (.witness 26) (.witness 101))
private def n168 : Certificate := (.edge 15 n163 (.color 0 n166 n166))
private def n171 : Certificate := (.color 15 (.witness 97) (.witness 30))
private def n175 : Certificate := (.witness 86)
private def n178 : Certificate := (.witness 41)
private def n182 : Certificate := (.witness 40)
private def n183 : Certificate := (.color 2 (.witness 86) (.witness 41))
private def n185 : Certificate := (.witness 87)
private def n190 : Certificate := (.edge 12 n106 (.edge 14 n36 (.edge 16 (.edge 15 n110 (.color 2 (.color 16 n175 (.color 17 (.witness 33) (.witness 94))) (.color 16 (.color 17 (.witness 33) (.witness 94)) n178))) (.color 0 (.color 1 n182 n183) (.color 1 n183 n185)))))
private def n193 : Certificate := (.color 1 (.witness 90) (.witness 37))
private def n199 : Certificate := (.color 0 (.witness 44) (.witness 83))
private def n200 : Certificate := (.edge 16 (.edge 15 n110 (.edge 17 n44 (.color 0 n193 n193))) n199)
private def n205 : Certificate := (.color 18 (.witness 14) (.witness 113))
private def n211 : Certificate := (.witness 92)
private def n212 : Certificate := (.witness 35)
private def n215 : Certificate := (.edge 14 n36 (.edge 17 n44 (.color 0 n211 n212)))
private def n216 : Certificate := (.color 8 (.witness 97) (.witness 30))
private def n217 : Certificate := (.color 0 n216 n216)
private def n218 : Certificate := (.edge 20 n215 n217)
private def n220 : Certificate := (.color 13 n79 n78)
private def n224 : Certificate := (.color 16 (.witness 81) (.witness 46))
private def n229 : Certificate := (.color 2 (.color 16 (.witness 65) n13) (.color 16 (.witness 65) n13))
private def n232 : Certificate := (.witness 54)
private def n233 : Certificate := (.witness 73)
private def n234 : Certificate := (.color 2 (.witness 54) (.witness 73))
private def n241 : Certificate := (.edge 12 n77 (.edge 13 n36 (.edge 17 (.edge 15 n83 n229) (.color 0 (.color 1 (.witness 72) n234) (.color 1 n234 (.witness 55))))))
private def n242 : Certificate := (.witness 58)
private def n243 : Certificate := (.witness 69)
private def n244 : Certificate := (.color 1 (.witness 58) (.witness 69))
private def n250 : Certificate := (.color 0 (.witness 76) (.witness 51))
private def n251 : Certificate := (.edge 17 (.edge 15 n83 (.edge 16 n44 (.color 0 n244 n244))) n250)
private def n254 : Certificate := (.color 19 (.witness 14) (.witness 113))
private def n255 : Certificate := (.color 15 n38 n254)
private def n256 : Certificate := (.color 15 n254 n37)
private def n260 : Certificate := (.witness 60)
private def n261 : Certificate := (.witness 67)
private def n264 : Certificate := (.edge 13 n36 (.edge 16 n44 (.color 0 n260 n261)))
private def n265 : Certificate := (.edge 20 n264 n217)
private def n267 : Certificate := (.witness 74)
private def n269 : Certificate := (.color 13 n267 (.color 14 n29 n24))
private def n270 : Certificate := (.witness 53)
private def n271 : Certificate := (.color 13 (.color 14 n29 n24) n270)
private def n275 : Certificate := (.color 17 (.witness 49) (.witness 78))
private def n278 : Certificate := (.color 20 (.witness 14) (.witness 113))
private def n285 : Certificate := (.color 13 (.color 16 (.witness 81) n278) (.color 16 n278 (.witness 46)))
private def n290 : Certificate := (.edge 5 (.edge 10 n10 (.edge 14 n11 (.edge 17 n12 (.edge 18 (.edge 8 (.edge 9 n105 (.edge 12 n109 n114)) (.edge 12 (.edge 13 n106 n120) (.color 15 n107 n107))) (.witness 49))))) (.edge 18 (.edge 19 (.edge 20 n129 (.edge 8 (.edge 9 n105 (.edge 10 n76 (.edge 12 n145 n155))) (.edge 12 (.edge 13 n106 (.edge 14 n77 n168)) n171))) (.edge 9 (.edge 8 n105 (.edge 20 (.edge 10 n35 (.edge 13 n190 n200)) (.color 12 (.color 15 n38 n205) (.color 15 n205 n37)))) (.edge 13 (.edge 12 n106 (.edge 16 (.edge 15 n110 n218) (.color 1 n220 n220))) n224))) (.edge 19 (.edge 10 (.edge 8 n76 (.edge 20 (.edge 9 n35 (.edge 14 n241 n251)) (.color 12 n255 n256))) (.edge 14 (.edge 12 n77 (.edge 17 (.edge 15 n83 n265) (.color 1 n269 n271))) n275)) (.edge 20 (.edge 9 (.edge 10 n35 (.color 14 (.color 17 n29 n278) (.color 17 n278 n24))) n285) (.witness 14)))))
private def n295 : Certificate := (.triangle 13)
private def n299 : Certificate := (.color 16 n175 (.color 20 (.witness 9) (.witness 118)))
private def n300 : Certificate := (.color 16 (.color 20 (.witness 9) (.witness 118)) n178)
private def n305 : Certificate := (.triangle 21)
private def n306 : Certificate := (.triangle 27)
private def n307 : Certificate := (.color 17 (.witness 54) (.witness 73))
private def n308 : Certificate := (.edge 14 n306 n307)
private def n311 : Certificate := (.color 16 (.witness 65) n307)
private def n312 : Certificate := (.color 16 n307 n13)
private def n314 : Certificate := (.edge 15 (.edge 19 n83 (.color 14 n307 n307)) (.color 7 n311 n312))
private def n320 : Certificate := (.edge 15 (.edge 19 n83 (.color 10 n307 n307)) (.color 11 n311 n312))
private def n329 : Certificate := (.edge 9 n6 (.edge 13 n7 (.edge 18 n9 (.edge 5 (.edge 10 n10 (.edge 14 n11 (.edge 19 n295 (.color 4 n299 n300)))) (.edge 17 (.edge 7 (.edge 10 n305 (.edge 11 n308 n314)) (.edge 11 (.edge 14 n306 n320) (.color 15 n311 n312))) n232)))))
private def n330 : Certificate := (.triangle 20)
private def n331 : Certificate := (.triangle 26)
private def n332 : Certificate := (.color 16 (.witness 86) (.witness 41))
private def n333 : Certificate := (.edge 13 n331 n332)
private def n337 : Certificate := (.edge 15 (.edge 18 n110 (.color 13 n332 n332)) (.color 7 n332 n332))
private def n343 : Certificate := (.edge 15 (.edge 18 n110 (.color 9 n332 n332)) (.color 11 n332 n332))
private def n356 : Certificate := (.edge 18 n110 (.color 3 (.color 15 (.witness 102) (.color 19 (.witness 9) (.witness 118))) (.color 15 (.color 19 (.witness 9) (.witness 118)) (.witness 25))))
private def n357 : Certificate := (.color 3 (.witness 102) (.witness 25))
private def n363 : Certificate := (.edge 13 n331 (.edge 14 n306 (.edge 15 n356 (.color 0 (.color 1 (.witness 24) n357) (.color 1 n357 (.witness 103))))))
private def n364 : Certificate := (.witness 114)
private def n365 : Certificate := (.witness 13)
private def n366 : Certificate := (.color 1 (.witness 114) (.witness 13))
private def n370 : Certificate := (.edge 15 (.edge 18 n110 (.edge 19 n83 (.color 0 n366 n366))) n154)
private def n379 : Certificate := (.edge 15 (.edge 18 n110 (.edge 19 n83 (.color 0 (.witness 116) (.witness 11)))) (.color 0 n166 n166))
private def n386 : Certificate := (.witness 48)
private def n387 : Certificate := (.color 3 (.witness 78) (.witness 49))
private def n389 : Certificate := (.witness 79)
private def n394 : Certificate := (.edge 11 n331 (.edge 14 n36 (.edge 18 (.edge 15 n110 (.color 3 n28 n30)) (.color 0 (.color 1 n386 n387) (.color 1 n387 n389)))))
private def n399 : Certificate := (.color 0 (.witness 52) (.witness 75))
private def n400 : Certificate := (.edge 18 (.edge 15 n110 (.edge 19 n129 (.color 0 n193 n193))) n399)
private def n405 : Certificate := (.color 16 (.witness 22) (.witness 105))
private def n413 : Certificate := (.color 7 (.witness 97) (.witness 30))
private def n414 : Certificate := (.color 0 n413 n413)
private def n415 : Certificate := (.edge 20 (.edge 14 n36 (.edge 19 n129 (.color 0 n211 n212))) n414)
private def n417 : Certificate := (.color 13 (.witness 73) (.witness 54))
private def n418 : Certificate := (.color 1 n417 n417)
private def n421 : Certificate := (.color 18 (.witness 73) (.witness 54))
private def n426 : Certificate := (.color 18 (.witness 65) (.witness 62))
private def n429 : Certificate := (.witness 80)
private def n430 : Certificate := (.color 3 (.witness 46) (.witness 81))
private def n432 : Certificate := (.witness 47)
private def n437 : Certificate := (.edge 11 n306 (.edge 13 n36 (.edge 19 (.edge 15 n83 (.color 3 n426 n426)) (.color 0 (.color 1 n429 n430) (.color 1 n430 n432)))))
private def n440 : Certificate := (.witness 84)
private def n441 : Certificate := (.witness 43)
private def n442 : Certificate := (.color 0 (.witness 84) (.witness 43))
private def n443 : Certificate := (.edge 19 (.edge 15 n83 (.edge 18 n129 (.color 0 n244 n244))) n442)
private def n447 : Certificate := (.color 15 n38 (.color 17 (.witness 22) (.witness 105)))
private def n448 : Certificate := (.color 15 (.color 17 (.witness 22) (.witness 105)) n37)
private def n452 : Certificate := (.edge 18 n129 (.color 0 n260 n261))
private def n454 : Certificate := (.edge 20 (.edge 13 n36 n452) n414)
private def n456 : Certificate := (.witness 82)
private def n457 : Certificate := (.color 14 (.witness 41) (.witness 86))
private def n459 : Certificate := (.witness 45)
private def n461 : Certificate := (.color 1 (.color 13 n456 n457) (.color 13 n457 n459))
private def n464 : Certificate := (.color 19 (.witness 41) (.witness 86))
private def n468 : Certificate := (.color 20 (.witness 22) (.witness 105))
private def n480 : Certificate := (.edge 5 (.edge 10 n10 (.edge 14 n11 (.edge 19 n295 (.edge 16 (.edge 7 (.edge 9 n330 (.edge 11 n333 n337)) (.edge 11 (.edge 13 n331 n343) (.color 15 n332 n332))) (.witness 41))))) (.edge 16 (.edge 17 (.edge 20 n44 (.edge 7 (.edge 9 n330 (.edge 10 n305 (.edge 11 n363 n370))) (.edge 11 (.edge 13 n331 (.edge 14 n306 n379)) n171))) (.edge 9 (.edge 7 n330 (.edge 20 (.edge 10 n35 (.edge 13 n394 n400)) (.color 11 (.color 15 n38 n405) (.color 15 n405 n37)))) (.edge 13 (.edge 11 n331 (.edge 18 (.edge 15 n110 n415) n418)) (.color 16 n421 n421)))) (.edge 17 (.edge 10 (.edge 7 n305 (.edge 20 (.edge 9 n35 (.edge 14 n437 n443)) (.color 11 n447 n448))) (.edge 14 (.edge 11 n306 (.edge 19 (.edge 15 n83 n454) n461)) (.color 17 n464 n464))) (.edge 20 (.edge 9 (.edge 10 n35 (.color 14 (.color 19 n178 n468) (.color 19 n468 n175))) (.color 13 (.color 18 n233 n468) (.color 18 n468 n232))) (.witness 22)))))
private def n484 : Certificate := (.triangle 14)
private def n485 : Certificate := (.triangle 19)
private def n486 : Certificate := (.triangle 25)
private def n487 : Certificate := (.color 15 (.witness 102) (.witness 25))
private def n488 : Certificate := (.edge 12 n486 n487)
private def n492 : Certificate := (.edge 16 (.edge 18 n110 (.color 12 n487 n487)) (.color 7 n487 n487))
private def n498 : Certificate := (.edge 16 (.edge 18 n110 (.color 8 n487 n487)) (.color 11 n487 n487))
private def n507 : Certificate := (.color 4 (.witness 86) (.witness 41))
private def n513 : Certificate := (.edge 12 n486 (.edge 14 n306 (.edge 16 (.edge 18 n110 (.color 4 n299 n300)) (.color 0 (.color 1 n182 n507) (.color 1 n507 n185)))))
private def n516 : Certificate := (.edge 16 (.edge 18 n110 (.edge 20 n44 (.color 0 n366 n366))) n199)
private def n524 : Certificate := (.color 1 (.witness 42) (.witness 85))
private def n526 : Certificate := (.edge 16 (.edge 18 n110 (.edge 20 n44 (.color 0 (.witness 116) (.witness 11)))) (.color 0 n524 n524))
private def n534 : Certificate := (.color 4 (.witness 78) (.witness 49))
private def n540 : Certificate := (.edge 11 n486 (.edge 14 n77 (.edge 18 (.edge 16 n110 (.color 4 n70 n71)) (.color 0 (.color 1 n386 n534) (.color 1 n534 n389)))))
private def n543 : Certificate := (.edge 18 (.edge 16 n110 (.edge 20 n129 (.color 0 n148 n148))) n399)
private def n548 : Certificate := (.color 15 (.witness 38) (.witness 89))
private def n554 : Certificate := (.color 7 (.witness 81) (.witness 46))
private def n555 : Certificate := (.color 0 n554 n554)
private def n556 : Certificate := (.edge 19 (.edge 14 n77 (.edge 20 n129 n161)) n555)
private def n558 : Certificate := (.color 12 (.witness 73) (.witness 54))
private def n567 : Certificate := (.witness 96)
private def n568 : Certificate := (.color 4 (.witness 30) (.witness 97))
private def n570 : Certificate := (.witness 31)
private def n575 : Certificate := (.edge 11 n306 (.edge 12 n77 (.edge 20 (.edge 16 n44 n426) (.color 0 (.color 1 n567 n568) (.color 1 n568 n570)))))
private def n577 : Certificate := (.witness 100)
private def n578 : Certificate := (.witness 27)
private def n579 : Certificate := (.color 0 (.witness 100) (.witness 27))
private def n580 : Certificate := (.edge 20 (.edge 16 n44 (.edge 18 n129 (.color 0 n244 n244))) n579)
private def n583 : Certificate := (.color 17 (.witness 38) (.witness 89))
private def n584 : Certificate := (.color 16 n79 n583)
private def n585 : Certificate := (.color 16 n583 n78)
private def n586 : Certificate := (.color 11 (.color 16 (.witness 81) n583) (.color 16 n583 (.witness 46)))
private def n589 : Certificate := (.edge 16 n44 n452)
private def n590 : Certificate := (.witness 98)
private def n591 : Certificate := (.witness 29)
private def n592 : Certificate := (.color 1 (.witness 98) (.witness 29))
private def n594 : Certificate := (.edge 20 n589 (.color 0 n592 n592))
private def n599 : Certificate := (.color 20 (.witness 25) (.witness 102))
private def n605 : Certificate := (.color 19 (.witness 38) (.witness 89))
private def n615 : Certificate := (.edge 5 (.edge 10 n10 (.edge 14 n11 (.edge 20 n484 (.edge 15 (.edge 7 (.edge 8 n485 (.edge 11 n488 n492)) (.edge 11 (.edge 12 n486 n498) n487)) (.witness 25))))) (.edge 15 (.edge 17 (.edge 19 n83 (.edge 7 (.edge 8 n485 (.edge 10 n305 (.edge 11 n513 n516))) (.edge 11 (.edge 12 n486 (.edge 14 n306 n526)) (.color 15 n224 n224)))) (.edge 8 (.edge 7 n485 (.edge 19 (.edge 10 n76 (.edge 12 n540 n543)) (.color 11 n548 n548))) (.edge 12 (.edge 11 n486 (.edge 18 (.edge 16 n110 n556) (.color 1 n558 n558))) (.color 15 n421 n421)))) (.edge 17 (.edge 10 (.edge 7 n305 (.edge 19 (.edge 8 n76 (.edge 14 n575 n580)) n586)) (.edge 14 (.edge 11 n306 (.edge 19 (.edge 12 n77 n594) (.color 7 n584 n585))) (.color 17 (.color 19 (.witness 38) n599) (.color 19 n599 (.witness 89))))) (.edge 19 (.edge 8 (.edge 10 n76 (.color 14 n605 n605)) (.color 12 (.color 18 n233 n605) (.color 18 n605 n232))) (.witness 38)))))
private def n619 : Certificate := (.color 5 (.witness 54) (.witness 73))
private def n625 : Certificate := (.edge 12 n486 (.edge 13 n331 (.edge 17 (.edge 19 n83 n332) (.color 0 (.color 1 (.witness 72) n619) (.color 1 n619 (.witness 55))))))
private def n627 : Certificate := (.edge 17 (.edge 19 n83 (.edge 20 n44 (.color 0 n366 n366))) n250)
private def n632 : Certificate := (.color 1 (.witness 74) (.witness 53))
private def n634 : Certificate := (.edge 17 (.edge 19 n83 (.edge 20 n44 (.color 0 (.witness 116) (.witness 11)))) (.color 0 n632 n632))
private def n637 : Certificate := (.witness 70)
private def n639 : Certificate := (.witness 57)
private def n646 : Certificate := (.color 5 (.witness 46) (.witness 81))
private def n652 : Certificate := (.edge 11 n486 (.edge 13 n106 (.edge 19 (.edge 17 n83 n107) (.color 0 (.color 1 n429 n646) (.color 1 n646 n432)))))
private def n654 : Certificate := (.edge 19 (.edge 17 n83 (.edge 20 n129 (.color 0 n148 n148))) n442)
private def n657 : Certificate := (.color 15 (.witness 70) (.witness 57))
private def n662 : Certificate := (.color 1 (.witness 82) (.witness 45))
private def n664 : Certificate := (.edge 19 (.edge 17 n83 (.edge 20 n129 n161)) (.color 0 n662 n662))
private def n669 : Certificate := (.color 18 n637 n464)
private def n670 : Certificate := (.color 18 n464 n639)
private def n676 : Certificate := (.color 5 (.witness 30) (.witness 97))
private def n682 : Certificate := (.edge 11 n331 (.edge 12 n106 (.edge 20 (.edge 17 n44 n107) (.color 0 (.color 1 n567 n676) (.color 1 n676 n570)))))
private def n684 : Certificate := (.edge 20 (.edge 17 n44 (.edge 19 n129 (.color 0 n193 n193))) n579)
private def n687 : Certificate := (.color 16 (.witness 70) (.witness 57))
private def n691 : Certificate := (.edge 17 n44 (.edge 19 n129 (.color 0 n211 n212)))
private def n692 : Certificate := (.edge 20 n691 (.color 0 n592 n592))
private def n697 : Certificate := (.color 18 n637 n599)
private def n698 : Certificate := (.color 18 n599 n639)
private def n702 : Certificate := (.color 18 (.witness 70) (.witness 57))
private def n705 : Certificate := (.color 12 n702 n702)
private def n710 : Certificate := (.edge 14 n11 (.edge 15 (.edge 16 (.edge 18 n110 (.edge 7 (.edge 8 n485 (.edge 9 n330 (.edge 11 n625 n627))) (.edge 11 (.edge 12 n486 (.edge 13 n331 n634)) (.color 15 (.color 16 n637 n275) (.color 16 n275 n639))))) (.edge 8 (.edge 7 n485 (.edge 18 (.edge 9 n105 (.edge 12 n652 n654)) (.color 11 n657 n657))) (.edge 12 (.edge 11 n486 (.edge 18 (.edge 13 n106 n664) (.color 7 n657 n657))) (.color 15 (.color 18 n637 n464) (.color 18 n464 n639))))) (.edge 16 (.edge 9 (.edge 7 n330 (.edge 18 (.edge 8 n105 (.edge 13 n682 n684)) (.color 11 n687 n687))) (.edge 13 (.edge 11 n331 (.edge 18 (.edge 12 n106 n692) (.color 7 n687 n687))) (.color 16 (.color 18 n637 n599) (.color 18 n599 n639)))) (.edge 18 (.edge 8 (.edge 9 n105 (.color 13 n702 n702)) n705) n639))))
private def n722 : Certificate := (.edge 10 n305 (.edge 11 (.edge 12 n486 (.edge 13 n331 (.color 1 (.color 11 n364 (.color 14 (.witness 9) (.witness 118))) (.color 11 (.color 14 (.witness 9) (.witness 118)) n365)))) (.color 0 (.witness 12) (.witness 115))))
private def n725 : Certificate := (.color 11 (.witness 113) (.witness 14))
private def n727 : Certificate := (.edge 13 n331 (.color 1 n725 n725))
private def n734 : Certificate := (.color 7 (.witness 113) (.witness 14))
private def n739 : Certificate := (.edge 12 (.edge 19 n77 (.edge 13 (.edge 20 n36 (.color 0 n734 n734)) (.color 1 n558 n558))) n418)
private def n745 : Certificate := (.color 8 (.witness 73) (.witness 54))
private def n749 : Certificate := (.color 9 (.witness 73) (.witness 54))
private def n751 : Certificate := (.edge 8 (.edge 19 n76 (.edge 9 (.edge 20 n35 (.color 1 n725 n725)) (.color 0 n745 n745))) (.color 0 n749 n749))
private def n762 : Certificate := (.edge 14 (.edge 12 n77 (.edge 20 (.edge 9 n35 n418) n171)) (.color 0 (.color 9 (.witness 76) (.color 10 n29 n24)) (.color 9 (.color 10 n29 n24) (.witness 51))))
private def n764 : Certificate := (.color 14 n29 n278)
private def n765 : Certificate := (.color 14 n278 n24)
private def n775 : Certificate := (.edge 11 n486 (.edge 18 (.edge 9 n105 (.color 13 n107 n107)) n29))
private def n777 : Certificate := (.color 8 (.witness 105) (.witness 22))
private def n778 : Certificate := (.color 0 n777 n777)
private def n779 : Certificate := (.edge 20 n129 n778)
private def n781 : Certificate := (.color 11 (.witness 49) (.witness 78))
private def n782 : Certificate := (.color 1 n781 n781)
private def n784 : Certificate := (.edge 13 (.edge 14 (.edge 20 n36 n778) n782) n399)
private def n789 : Certificate := (.color 12 (.witness 105) (.witness 22))
private def n791 : Certificate := (.edge 20 n129 (.color 1 n789 n789))
private def n793 : Certificate := (.color 7 (.witness 49) (.witness 78))
private def n794 : Certificate := (.color 0 n793 n793)
private def n796 : Certificate := (.edge 9 (.edge 10 (.edge 20 n35 (.color 1 n789 n789)) n794) n250)
private def n800 : Certificate := (.color 13 n233 n468)
private def n801 : Certificate := (.color 13 n468 n232)
private def n813 : Certificate := (.edge 13 (.edge 18 n106 (.edge 20 (.edge 9 n35 (.edge 14 n36 n250)) n734)) (.edge 9 (.edge 20 n35 (.color 1 n789 n789)) n555))
private def n815 : Certificate := (.color 14 n178 n468)
private def n816 : Certificate := (.color 14 n468 n175)
private def n821 : Certificate := (.color 12 (.witness 41) (.witness 86))
private def n824 : Certificate := (.edge 18 n106 (.edge 14 (.edge 20 n36 (.color 0 n734 n734)) (.color 1 n821 n821)))
private def n836 : Certificate := (.color 11 (.witness 81) (.witness 46))
private def n839 : Certificate := (.edge 13 n36 (.edge 9 (.edge 10 n35 (.edge 8 (.edge 18 n105 n399) (.color 1 (.color 11 n456 n457) (.color 11 n457 n459)))) (.color 1 n836 n836)))
private def n842 : Certificate := (.color 8 (.witness 41) (.witness 86))
private def n845 : Certificate := (.edge 18 n105 (.edge 10 (.edge 20 n35 (.color 1 n725 n725)) (.color 0 n842 n842)))
private def n849 : Certificate := (.color 0 (.color 9 n440 (.color 10 n178 n175)) (.color 9 (.color 10 n178 n175) n441))
private def n856 : Certificate := (.edge 12 n106 (.edge 20 (.edge 10 n35 n461) n171))
private def n857 : Certificate := (.color 9 (.witness 81) (.witness 46))
private def n858 : Certificate := (.color 0 n857 n857)
private def n869 : Certificate := (.edge 16 (.edge 18 n110 (.edge 17 (.edge 19 n83 (.edge 20 n44 (.edge 7 (.edge 8 n485 (.edge 9 n330 n722)) (.edge 11 (.edge 12 n486 n727) (.witness 14))))) (.edge 7 (.edge 8 n485 (.edge 9 n330 (.edge 11 (.edge 12 n486 n417) (.edge 14 n739 n250)))) (.edge 11 (.edge 12 n486 (.edge 13 n331 (.edge 10 n751 n399))) (.edge 10 (.edge 19 (.edge 8 n76 n762) (.color 10 n764 n765)) (.color 14 n29 n24)))))) (.edge 19 (.edge 17 n83 (.edge 8 (.edge 10 n76 (.edge 7 n485 (.edge 12 (.edge 14 n77 n775) (.edge 18 n779 n784)))) (.edge 12 (.edge 14 n77 (.edge 11 n486 (.edge 18 n791 n796))) (.edge 20 (.edge 18 n129 (.color 9 n800 n801)) (.witness 22))))) (.edge 7 (.edge 8 n485 (.edge 10 (.edge 17 n305 (.edge 12 (.edge 11 n486 n813) (.color 10 n815 n816))) (.edge 11 (.edge 12 n486 n457) (.edge 13 (.edge 12 n824 n461) n199)))) (.edge 11 (.edge 12 n486 (.edge 14 (.edge 17 n306 (.edge 20 n839 n777)) (.edge 9 (.edge 8 n845 n849) n442))) (.edge 9 (.edge 18 (.edge 8 n105 (.edge 13 n856 n858)) (.color 9 (.color 13 n79 n278) (.color 13 n278 n78))) n220)))))
private def n872 : Certificate := (.edge 11 n331 (.edge 18 (.edge 8 n105 (.color 12 n107 n107)) n29))
private def n875 : Certificate := (.color 9 (.witness 89) (.witness 38))
private def n880 : Certificate := (.edge 19 n129 (.color 0 (.color 8 (.witness 36) n875) (.color 8 n875 (.witness 91))))
private def n883 : Certificate := (.edge 12 (.edge 14 (.edge 19 n77 (.color 0 (.color 8 (.witness 36) n875) (.color 8 n875 (.witness 91)))) n782) n399)
private def n888 : Certificate := (.edge 14 n36 n821)
private def n897 : Certificate := (.edge 11 (.edge 14 (.edge 17 n306 (.color 0 (.color 7 (.witness 36) n875) (.color 7 n875 (.witness 91)))) (.color 1 (.color 11 n456 n821) (.color 11 n821 n459))) n199)
private def n901 : Certificate := (.color 14 (.witness 57) (.witness 70))
private def n902 : Certificate := (.edge 17 n306 n901)
private def n903 : Certificate := (.witness 66)
private def n905 : Certificate := (.witness 61)
private def n907 : Certificate := (.color 1 (.color 12 n903 n901) (.color 12 n901 n905))
private def n915 : Certificate := (.color 13 (.witness 89) (.witness 38))
private def n920 : Certificate := (.edge 19 n129 (.color 1 (.color 12 (.witness 34) n915) (.color 12 n915 (.witness 93))))
private def n923 : Certificate := (.edge 8 (.edge 10 (.edge 19 n76 (.color 1 (.color 12 (.witness 34) n915) (.color 12 n915 (.witness 93)))) n794) n250)
private def n935 : Certificate := (.edge 7 (.edge 10 (.edge 17 n305 (.color 1 (.color 11 (.witness 34) n915) (.color 11 n915 (.witness 93)))) (.color 0 (.color 7 n440 n842) (.color 7 n842 n441))) n442)
private def n938 : Certificate := (.color 10 (.witness 57) (.witness 70))
private def n939 : Certificate := (.edge 17 n305 n938)
private def n944 : Certificate := (.color 0 (.color 8 (.witness 68) n938) (.color 8 n938 (.witness 59)))
private def n956 : Certificate := (.edge 7 n305 (.edge 8 n76 (.edge 14 (.edge 11 n306 (.color 1 (.color 12 (.witness 65) n13) (.color 12 (.witness 65) n13))) (.color 0 (.witness 68) (.witness 59)))))
private def n958 : Certificate := (.edge 14 (.edge 11 n306 n907) n639)
private def n979 : Certificate := (.color 8 (.color 12 (.witness 105) (.color 19 (.witness 6) (.witness 121))) (.color 12 (.color 19 (.witness 6) (.witness 121)) (.witness 22)))
private def n987 : Certificate := (.edge 11 n306 (.edge 12 (.edge 19 n77 (.edge 13 (.edge 18 n106 (.color 0 n734 n734)) n199)) n414))
private def n999 : Certificate := (.color 10 (.witness 25) (.witness 102))
private def n1004 : Certificate := (.edge 14 n77 (.edge 13 (.edge 18 n106 (.edge 11 (.edge 16 n331 (.color 0 (.color 7 (.witness 68) n938) (.color 7 n938 (.witness 59)))) n250)) (.color 0 (.color 7 n577 n999) (.color 7 n999 n578))))
private def n1007 : Certificate := (.color 7 (.color 11 n38 n405) (.color 11 n405 n37))
private def n1012 : Certificate := (.edge 18 n106 n901)
private def n1019 : Certificate := (.color 13 (.witness 25) (.witness 102))
private def n1022 : Certificate := (.color 1 (.color 11 (.witness 98) n1019) (.color 11 n1019 (.witness 29)))
private def n1023 : Certificate := (.edge 14 (.edge 17 n306 (.color 0 (.color 7 (.witness 20) n777) (.color 7 n777 (.witness 107)))) n1022)
private def n1026 : Certificate := (.color 14 (.witness 25) (.witness 102))
private def n1032 : Certificate := (.edge 14 (.edge 19 n77 (.color 0 n734 n734)) (.color 1 (.color 12 n590 n1019) (.color 12 n1019 n591)))
private def n1034 : Certificate := (.color 12 n590 n1026)
private def n1035 : Certificate := (.color 12 n1026 n591)
private def n1045 : Certificate := (.edge 14 n77 (.color 0 (.color 8 n577 n999) (.color 8 n999 n578)))
private def n1052 : Certificate := (.edge 11 (.edge 13 (.edge 16 n331 (.edge 14 (.edge 17 n306 n778) n442)) n586) n217)
private def n1061 : Certificate := (.edge 13 (.edge 16 n331 (.edge 14 (.edge 17 n306 (.color 0 (.witness 20) (.witness 107))) n1022)) (.color 1 (.color 11 n590 n1026) (.color 11 n1026 n591)))
private def n1069 : Certificate := (.edge 11 (.edge 17 n306 (.edge 13 (.edge 16 n331 n778) n399)) n217)
private def n1076 : Certificate := (.color 9 (.witness 68) n938)
private def n1077 : Certificate := (.color 9 n938 (.witness 59))
private def n1079 : Certificate := (.edge 14 (.edge 17 n306 n789) (.color 0 n1076 n1077))
private def n1081 : Certificate := (.color 11 (.witness 97) (.witness 30))
private def n1085 : Certificate := (.edge 19 n77 (.color 0 n875 n875))
private def n1086 : Certificate := (.color 1 n1081 n1081)
private def n1091 : Certificate := (.color 12 (.witness 97) (.witness 30))
private def n1095 : Certificate := (.edge 20 (.edge 9 (.edge 10 n35 (.edge 16 (.edge 17 n44 (.edge 7 n330 (.edge 13 (.edge 14 n36 n872) (.edge 18 n880 n883)))) (.edge 18 (.edge 19 n129 (.edge 8 n105 (.edge 13 n888 n897))) (.edge 14 (.edge 13 n36 (.edge 11 n902 n907)) (.witness 57))))) (.edge 13 (.edge 14 n36 (.edge 16 (.edge 17 n44 (.edge 11 n331 (.edge 18 n920 n923))) (.edge 18 (.edge 19 n129 (.edge 12 n106 n935)) (.edge 10 (.edge 7 n939 n944) (.witness 57))))) (.edge 17 (.edge 16 n44 (.edge 19 (.edge 18 n129 (.edge 10 n956 n958)) (.color 7 (.color 11 n79 n583) (.color 11 n583 n78)))) (.edge 19 (.edge 18 n129 (.color 8 (.color 12 n233 n605) (.color 12 n605 n232))) (.witness 38))))) (.edge 7 (.edge 9 (.edge 16 n330 (.edge 8 (.edge 18 n105 (.edge 10 (.edge 17 n305 n979) n901)) (.edge 17 (.edge 10 n305 (.edge 14 n987 n705)) n789))) (.edge 10 (.edge 17 n305 (.edge 19 (.edge 8 n76 (.edge 12 n1004 n1007)) n915)) (.edge 11 (.edge 13 (.edge 16 n331 (.edge 12 n1012 n1023)) n1026) (.edge 12 (.edge 13 (.edge 18 n106 n1032) (.color 1 n1034 n1035)) n154)))) (.edge 8 (.edge 18 (.edge 9 n105 (.edge 12 (.edge 13 n106 (.edge 19 n1045 n586)) (.edge 10 (.edge 19 n76 n1052) (.edge 11 n1061 n154)))) (.edge 19 (.edge 10 n76 (.edge 14 (.edge 12 n77 n1069) (.color 11 n687 n687))) n725)) (.edge 11 (.edge 13 (.edge 16 n331 (.edge 12 (.edge 18 n106 n1079) n1081)) (.edge 14 (.edge 17 n306 (.edge 12 n1085 n1086)) n579)) n1091))))
private def n1102 : Certificate := (.triangle 15)
private def n1103 : Certificate := (.triangle 16)
private def n1107 : Certificate := (.edge 6 (.edge 11 n1102 (.edge 12 n1103 (.color 6 (.witness 121) (.witness 6)))) (.witness 6))
private def n1112 : Certificate := (.color 13 n903 n905)
private def n1118 : Certificate := (.color 13 n903 n901)
private def n1119 : Certificate := (.color 13 n901 n905)
private def n1121 : Certificate := (.edge 12 (.edge 19 n77 (.color 5 n901 n901)) (.color 11 n1118 n1119))
private def n1130 : Certificate := (.edge 16 n330 (.edge 18 n105 (.edge 4 n6 (.edge 10 (.edge 17 n305 (.edge 19 n76 (.edge 20 n35 (.edge 5 n10 n1107)))) (.edge 6 (.edge 11 n1102 (.edge 12 (.triangle 16) (.color 6 n1112 n1112))) (.edge 14 (.edge 11 (.edge 17 n306 n1121) (.color 12 n1118 n1119)) (.witness 57)))))))
private def n1132 : Certificate := (.color 13 (.witness 89) (.color 14 (.witness 34) (.witness 93)))
private def n1133 : Certificate := (.color 13 (.color 14 (.witness 34) (.witness 93)) (.witness 38))
private def n1140 : Certificate := (.edge 12 (.edge 18 n106 (.color 4 n915 n915)) (.color 11 n915 n915))
private def n1149 : Certificate := (.color 20 (.witness 29) (.witness 98))
private def n1153 : Certificate := (.edge 14 n36 (.color 17 (.color 19 (.witness 34) n1149) (.color 19 n1149 (.witness 93))))
private def n1156 : Certificate := (.color 18 n903 n1149)
private def n1157 : Certificate := (.color 18 n1149 n905)
private def n1159 : Certificate := (.edge 16 (.edge 17 n44 (.color 14 (.color 19 (.witness 34) n1149) (.color 19 n1149 (.witness 93)))) (.color 4 n1156 n1157))
private def n1165 : Certificate := (.edge 16 (.edge 17 n44 (.color 5 (.color 19 (.witness 34) n1149) (.color 19 n1149 (.witness 93)))) (.color 13 n1156 n1157))
private def n1176 : Certificate := (.color 8 (.witness 77) (.witness 50))
private def n1177 : Certificate := (.color 7 n386 n1176)
private def n1178 : Certificate := (.color 7 n1176 n389)
private def n1182 : Certificate := (.edge 18 (.edge 12 n106 (.color 5 (.color 19 (.witness 34) n1149) (.color 19 n1149 (.witness 93)))) (.edge 4 (.edge 5 n484 (.color 0 n1177 n1178)) n794))
private def n1185 : Certificate := (.color 7 (.witness 85) (.witness 42))
private def n1189 : Certificate := (.edge 19 n129 (.edge 4 (.edge 5 n484 (.color 0 n1185 n1185)) (.color 0 (.color 7 n440 n842) (.color 7 n842 n441))))
private def n1191 : Certificate := (.color 4 (.witness 70) (.witness 57))
private def n1192 : Certificate := (.color 0 n1191 n1191)
private def n1198 : Certificate := (.color 8 (.witness 45) (.witness 82))
private def n1203 : Certificate := (.edge 19 (.edge 12 n77 (.color 4 n1156 n1157)) (.edge 4 (.edge 5 n484 n555) (.color 0 (.color 7 n429 n1198) (.color 7 n1198 n432))))
private def n1208 : Certificate := (.edge 5 n484 (.color 8 (.color 12 n233 n605) (.color 12 n605 n232)))
private def n1213 : Certificate := (.color 7 (.witness 53) (.witness 74))
private def n1215 : Certificate := (.edge 12 (.edge 14 n77 (.color 7 (.color 11 n29 n687) (.color 11 n687 n24))) (.color 0 n1213 n1213))
private def n1218 : Certificate := (.witness 88)
private def n1219 : Certificate := (.color 5 (.witness 38) (.witness 89))
private def n1221 : Certificate := (.witness 39)
private def n1223 : Certificate := (.color 0 (.color 4 (.witness 88) (.color 5 (.witness 38) (.witness 89))) (.color 4 (.color 5 (.witness 38) (.witness 89)) (.witness 39)))
private def n1232 : Certificate := (.edge 14 (.edge 17 n306 (.edge 19 n77 (.color 0 (.witness 120) (.witness 7)))) n1192)
private def n1234 : Certificate := (.color 11 (.witness 98) (.witness 29))
private def n1239 : Certificate := (.color 12 (.witness 98) (.witness 29))
private def n1243 : Certificate := (.edge 10 (.edge 17 n305 (.edge 19 n76 (.edge 5 n10 (.edge 6 (.edge 11 n1102 (.edge 12 n1103 (.color 6 n1132 n1133))) (.edge 13 (.edge 11 (.edge 16 n331 n1140) (.color 12 n915 n915)) (.witness 38)))))) (.edge 6 (.edge 11 n1102 (.edge 12 n1103 (.edge 20 (.edge 4 (.edge 5 n484 (.edge 13 n1153 n1159)) (.edge 13 (.edge 14 n36 n1165) (.color 16 n1156 n1157))) n591))) (.edge 20 (.edge 13 (.edge 14 n36 (.edge 16 (.edge 11 n331 (.edge 17 n44 n1182)) (.edge 18 (.edge 12 n106 n1189) n1192))) (.edge 17 (.edge 16 n44 (.edge 14 (.edge 11 n306 n1203) (.color 4 n697 n698))) (.edge 19 (.edge 18 n129 (.edge 4 n1208 n1215)) n1223))) (.edge 11 (.edge 13 (.edge 16 n331 (.edge 12 (.edge 18 n106 n1232) n1234)) (.color 11 n1034 n1035)) n1239))))
private def n1247 : Certificate := (.triangle 17)
private def n1251 : Certificate := (.color 12 (.witness 105) (.color 14 (.witness 18) (.witness 109)))
private def n1252 : Certificate := (.color 12 (.color 14 (.witness 18) (.witness 109)) (.witness 22))
private def n1259 : Certificate := (.edge 13 (.edge 18 n106 (.color 3 n789 n789)) (.color 11 n789 n789))
private def n1267 : Certificate := (.color 19 (.witness 45) (.witness 82))
private def n1269 : Certificate := (.edge 14 n77 (.color 17 n1267 n1267))
private def n1272 : Certificate := (.color 18 n903 n1267)
private def n1273 : Certificate := (.color 18 n1267 n905)
private def n1275 : Certificate := (.edge 15 (.edge 17 n83 (.color 14 n1267 n1267)) (.color 3 n1272 n1273))
private def n1281 : Certificate := (.edge 15 (.edge 17 n83 (.color 5 n1267 n1267)) (.color 12 n1272 n1273))
private def n1290 : Certificate := (.color 9 (.witness 77) (.witness 50))
private def n1296 : Certificate := (.edge 18 (.edge 13 n106 (.color 5 n1267 n1267)) (.edge 3 (.edge 5 n295 (.color 0 (.color 7 n386 n1290) (.color 7 n1290 n389))) n794))
private def n1299 : Certificate := (.color 7 (.witness 101) (.witness 26))
private def n1302 : Certificate := (.color 9 (.witness 25) (.witness 102))
private def n1307 : Certificate := (.edge 20 n129 (.edge 3 (.edge 5 n295 (.color 0 n1299 n1299)) (.color 0 (.color 7 n577 n1302) (.color 7 n1302 n578))))
private def n1309 : Certificate := (.color 3 (.witness 70) (.witness 57))
private def n1310 : Certificate := (.color 0 n1309 n1309)
private def n1316 : Certificate := (.color 9 (.witness 29) (.witness 98))
private def n1321 : Certificate := (.edge 20 (.edge 13 n36 (.color 3 n1272 n1273)) (.edge 3 (.edge 5 n295 n414) (.color 0 (.color 7 n567 n1316) (.color 7 n1316 n570))))
private def n1326 : Certificate := (.edge 5 n295 (.color 9 n800 n801))
private def n1331 : Certificate := (.edge 13 (.edge 14 n36 (.color 7 (.color 11 n29 n657) (.color 11 n657 n24))) (.color 0 n1213 n1213))
private def n1334 : Certificate := (.witness 104)
private def n1335 : Certificate := (.color 5 (.witness 22) (.witness 105))
private def n1337 : Certificate := (.witness 23)
private def n1339 : Certificate := (.color 0 (.color 3 n1334 n1335) (.color 3 n1335 n1337))
private def n1345 : Certificate := (.edge 14 (.edge 17 n306 (.edge 20 n36 (.color 0 (.witness 120) (.witness 7)))) n1310)
private def n1347 : Certificate := (.color 11 (.witness 82) (.witness 45))
private def n1352 : Certificate := (.color 13 (.witness 82) (.witness 45))
private def n1357 : Certificate := (.edge 10 (.edge 17 n305 (.edge 20 n35 (.edge 5 n10 (.edge 6 (.edge 11 n1102 (.edge 13 n1247 (.color 6 n1251 n1252))) (.edge 12 (.edge 11 (.edge 15 n486 n1259) n789) (.witness 22)))))) (.edge 6 (.edge 11 n1102 (.edge 13 n1247 (.edge 19 (.edge 3 (.edge 5 n295 (.edge 12 n1269 n1275)) (.edge 12 (.edge 14 n77 n1281) (.color 15 n1272 n1273))) n459))) (.edge 19 (.edge 12 (.edge 14 n77 (.edge 15 (.edge 11 n486 (.edge 17 n83 n1296)) (.edge 18 (.edge 13 n106 n1307) n1310))) (.edge 17 (.edge 15 n83 (.edge 14 (.edge 11 n306 n1321) (.color 3 n669 n670))) (.edge 20 (.edge 18 n129 (.edge 3 n1326 n1331)) n1339))) (.edge 11 (.edge 12 (.edge 15 n486 (.edge 13 (.edge 18 n106 n1345) n1347)) (.color 11 (.color 13 n456 n457) (.color 13 n457 n459))) (.color 12 n1352 n1352)))))
private def n1360 : Certificate := (.triangle 18)
private def n1361 : Certificate := (.color 18 (.witness 77) (.witness 50))
private def n1363 : Certificate := (.edge 13 n106 (.color 16 n1361 n1361))
private def n1367 : Certificate := (.edge 15 (.edge 16 n110 (.color 13 n1361 n1361)) (.color 3 n1361 n1361))
private def n1373 : Certificate := (.edge 15 (.edge 16 n110 (.color 4 n1361 n1361)) (.color 12 n1361 n1361))
private def n1382 : Certificate := (.color 10 (.witness 45) (.witness 82))
private def n1388 : Certificate := (.edge 19 (.edge 14 n77 (.color 4 n1361 n1361)) (.edge 3 (.edge 4 n9 (.color 0 (.color 7 n429 n1382) (.color 7 n1382 n432))) n555))
private def n1393 : Certificate := (.edge 20 n129 (.edge 3 (.edge 4 n9 (.color 0 n1299 n1299)) (.color 0 (.color 7 n577 n999) (.color 7 n999 n578))))
private def n1395 : Certificate := (.color 3 (.witness 38) (.witness 89))
private def n1402 : Certificate := (.color 10 (.witness 29) (.witness 98))
private def n1407 : Certificate := (.edge 20 (.edge 14 n36 (.color 3 n1361 n1361)) (.edge 3 (.edge 4 n9 n414) (.color 0 (.color 7 n567 n1402) (.color 7 n1402 n570))))
private def n1412 : Certificate := (.edge 4 n9 (.color 13 (.color 18 n233 n468) (.color 18 n468 n232)))
private def n1416 : Certificate := (.color 7 (.color 11 (.witness 81) n548) (.color 11 n548 (.witness 46)))
private def n1417 : Certificate := (.edge 13 (.edge 14 n36 (.color 0 n1185 n1185)) n1416)
private def n1420 : Certificate := (.color 4 (.witness 22) (.witness 105))
private def n1430 : Certificate := (.edge 14 (.edge 19 n77 (.edge 20 n36 (.color 0 (.witness 120) (.witness 7)))) (.color 0 (.color 7 n243 n242) (.color 7 n243 n242)))
private def n1437 : Certificate := (.color 14 (.witness 50) (.witness 77))
private def n1438 : Certificate := (.color 13 n233 n1437)
private def n1439 : Certificate := (.color 13 n1437 n232)
private def n1444 : Certificate := (.edge 5 n10 (.edge 6 (.edge 11 n1102 (.edge 14 n1360 (.edge 18 (.edge 3 (.edge 4 n9 (.edge 12 n1363 n1367)) (.edge 12 (.edge 13 n106 n1373) (.color 15 n1361 n1361))) (.witness 50)))) (.edge 18 (.edge 12 (.edge 13 n106 (.edge 15 (.edge 11 n486 (.edge 16 n110 n1388)) (.edge 19 (.edge 14 n77 n1393) (.color 0 n1395 n1395)))) (.edge 16 (.edge 15 n110 (.edge 13 (.edge 11 n331 n1407) (.color 3 n421 n421))) (.edge 20 (.edge 19 n129 (.edge 3 n1412 n1417)) (.color 0 (.color 3 n1334 n1420) (.color 3 n1420 n1337))))) (.edge 11 (.edge 12 (.edge 15 n486 (.edge 13 (.edge 16 n331 n1430) (.color 11 n558 n558))) (.color 11 n417 n417)) (.color 12 n1438 n1439)))))
private def n1446 : Certificate := (.color 11 (.witness 114) (.witness 13))
private def n1448 : Certificate := (.edge 20 n36 (.color 7 n1446 n1446))
private def n1453 : Certificate := (.edge 3 (.edge 19 n295 (.edge 4 (.edge 20 n484 n1446) n1310)) n1192)
private def n1454 : Certificate := (.witness 56)
private def n1455 : Certificate := (.witness 71)
private def n1456 : Certificate := (.color 0 (.witness 56) (.witness 71))
private def n1463 : Certificate := (.edge 3 (.edge 18 n9 (.edge 5 (.edge 20 n484 n1446) (.color 0 n1395 n1395))) n1223)
private def n1464 : Certificate := (.color 0 (.witness 88) (.witness 39))
private def n1469 : Certificate := (.color 11 (.witness 50) (.witness 77))
private def n1472 : Certificate := (.edge 18 (.edge 3 n9 (.color 17 (.color 19 (.witness 38) n599) (.color 19 n599 (.witness 89)))) (.edge 16 (.edge 17 n44 n1469) n1456))
private def n1476 : Certificate := (.edge 18 n129 (.edge 3 (.edge 5 n295 (.edge 16 (.edge 17 n44 n1469) n1456)) n687))
private def n1478 : Certificate := (.edge 16 (.edge 17 n44 n1464) n1347)
private def n1481 : Certificate := (.edge 18 n9 n357)
private def n1482 : Certificate := (.color 0 n357 n357)
private def n1494 : Certificate := (.edge 4 n9 (.edge 19 (.edge 5 n295 (.color 3 n421 n421)) n1464))
private def n1496 : Certificate := (.edge 20 (.edge 19 n129 n1223) n1234)
private def n1499 : Certificate := (.edge 19 n295 n619)
private def n1500 : Certificate := (.color 4 (.witness 72) n619)
private def n1501 : Certificate := (.color 4 n619 (.witness 55))
private def n1502 : Certificate := (.color 0 n1500 n1501)
private def n1509 : Certificate := (.edge 5 n484 (.color 4 n421 n421))
private def n1514 : Certificate := (.edge 19 (.edge 18 n129 (.color 0 (.color 3 (.witness 72) n619) (.color 3 n619 (.witness 55)))) n1347)
private def n1519 : Certificate := (.edge 18 n9 (.edge 5 (.edge 19 n295 n1446) (.color 0 (.color 3 n1334 n1420) (.color 3 n1420 n1337))))
private def n1521 : Certificate := (.color 0 (.witness 104) (.witness 23))
private def n1525 : Certificate := (.edge 4 n9 (.color 17 n464 n464))
private def n1527 : Certificate := (.edge 15 (.edge 17 n83 n1469) n1456)
private def n1531 : Certificate := (.edge 4 (.edge 5 n484 n1527) n657)
private def n1533 : Certificate := (.edge 17 n83 n1521)
private def n1545 : Certificate := (.edge 6 n1102 (.edge 12 (.edge 15 (.triangle 25) (.edge 13 (.edge 18 n106 (.edge 16 (.triangle 26) (.edge 14 (.edge 19 n77 n1448) (.edge 5 n1453 n1456)))) (.edge 14 (.edge 19 n77 (.edge 17 n306 (.edge 4 n1463 n1464))) (.edge 20 (.edge 4 (.edge 5 n484 n1472) (.edge 19 n1476 n1478)) (.edge 3 (.edge 4 n1481 n1482) (.witness 25)))))) (.edge 16 (.edge 13 (.triangle 26) (.edge 17 (.edge 20 (.triangle 33) (.edge 14 n306 (.edge 15 n356 n357))) (.edge 18 (.edge 15 (.triangle 31) (.edge 3 n1494 n1496)) (.edge 5 (.edge 3 n1499 n1502) (.witness 54))))) (.edge 14 (.edge 17 n306 (.edge 20 (.edge 13 (.triangle 30) (.edge 4 n1509 n1514)) (.edge 3 (.edge 4 n1519 n1339) n1521))) (.edge 19 (.edge 3 (.edge 5 n295 (.edge 18 n1525 n1527)) (.edge 20 (.edge 18 n129 n1531) (.edge 15 n1533 n1234))) (.edge 4 (.edge 3 (.edge 18 n9 n507) (.color 0 n507 n507)) (.witness 41)))))))
private def n1555 : Certificate := (.edge 14 n77 (.edge 15 (.edge 16 n110 (.color 7 (.color 15 n165 (.color 17 (.witness 18) (.witness 109))) (.color 15 (.color 17 (.witness 18) (.witness 109)) n164))) (.color 0 (.color 6 (.witness 24) n1299) (.color 6 n1299 (.witness 103)))))
private def n1557 : Certificate := (.color 6 (.witness 105) (.witness 22))
private def n1558 : Certificate := (.color 0 n1557 n1557)
private def n1560 : Certificate := (.edge 16 n110 (.edge 17 n83 n1558))
private def n1565 : Certificate := (.color 6 (.witness 25) (.witness 102))
private def n1566 : Certificate := (.color 0 n1565 n1565)
private def n1570 : Certificate := (.color 15 (.witness 98) (.witness 29))
private def n1583 : Certificate := (.edge 14 n36 (.edge 16 (.edge 15 n110 (.color 7 (.color 16 (.witness 85) (.color 17 (.witness 34) (.witness 93))) (.color 16 (.color 17 (.witness 34) (.witness 93)) (.witness 42)))) (.color 0 (.color 6 n182 n1185) (.color 6 n1185 n185))))
private def n1585 : Certificate := (.color 6 (.witness 89) (.witness 38))
private def n1588 : Certificate := (.edge 15 n110 (.edge 17 n44 (.color 0 n1585 n1585)))
private def n1598 : Certificate := (.color 3 (.witness 98) (.witness 29))
private def n1599 : Certificate := (.color 0 n1598 n1598)
private def n1602 : Certificate := (.color 6 n1352 n1352)
private def n1605 : Certificate := (.color 16 (.witness 82) (.witness 45))
private def n1616 : Certificate := (.edge 13 n36 (.edge 17 (.edge 15 n83 (.color 7 (.color 16 n903 n905) (.color 16 n903 n905))) (.color 0 (.color 6 (.witness 72) n1213) (.color 6 n1213 (.witness 55)))))
private def n1618 : Certificate := (.color 6 (.witness 57) (.witness 70))
private def n1619 : Certificate := (.color 0 n1618 n1618)
private def n1621 : Certificate := (.edge 15 n83 (.edge 16 n44 n1619))
private def n1636 : Certificate := (.color 17 (.witness 50) (.witness 77))
private def n1639 : Certificate := (.color 20 (.witness 13) (.witness 114))
private def n1650 : Certificate := (.edge 18 (.edge 19 (.edge 20 n129 (.edge 3 (.edge 4 n9 (.edge 5 n295 (.edge 12 (.edge 13 n106 n1555) (.edge 15 n1560 n154)))) (.edge 12 (.edge 13 n106 (.edge 14 n77 (.edge 15 n163 n1566))) n1570))) (.edge 4 (.edge 3 n9 (.edge 20 (.edge 5 n484 (.edge 13 (.edge 12 n106 n1583) (.edge 16 n1588 n199))) (.color 12 (.color 15 (.witness 98) (.color 18 n365 n364)) (.color 15 (.color 18 n365 n364) (.witness 29))))) (.edge 13 (.edge 12 n106 (.edge 16 (.edge 15 n110 (.edge 20 n215 n1599)) n1602)) n1605))) (.edge 19 (.edge 5 (.edge 3 n295 (.edge 20 (.edge 4 n484 (.edge 14 (.edge 12 n77 n1616) (.edge 17 n1621 n250))) (.color 12 (.color 15 (.witness 98) (.color 19 n365 n364)) (.color 15 (.color 19 n365 n364) (.witness 29))))) (.edge 14 (.edge 12 n77 (.edge 17 (.edge 15 n83 (.edge 20 n264 n1599)) (.color 6 (.color 13 n233 n1437) (.color 13 n1437 n232)))) n1636)) (.edge 20 (.edge 4 (.edge 5 n484 (.color 14 (.color 17 (.witness 50) n1639) (.color 17 n1639 (.witness 77)))) (.color 13 (.color 16 n456 n1639) (.color 16 n1639 n459))) n365)))
private def n1659 : Certificate := (.color 11 n364 (.color 17 (.witness 5) (.witness 122)))
private def n1660 : Certificate := (.color 11 (.color 17 (.witness 5) (.witness 122)) n365)
private def n1665 : Certificate := (.edge 16 n331 n1446)
private def n1666 : Certificate := (.color 6 n1446 n1446)
private def n1674 : Certificate := (.color 14 (.witness 58) (.witness 69))
private def n1675 : Certificate := (.edge 17 n306 n1674)
private def n1677 : Certificate := (.color 13 (.witness 65) n1674)
private def n1678 : Certificate := (.color 13 n1674 n13)
private def n1680 : Certificate := (.edge 12 (.edge 19 n77 n1674) (.color 6 n1677 n1678))
private def n1686 : Certificate := (.edge 12 (.edge 19 n77 (.color 10 n1674 n1674)) (.color 11 n1677 n1678))
private def n1695 : Certificate := (.color 4 (.witness 90) (.witness 37))
private def n1701 : Certificate := (.edge 13 (.edge 16 n331 (.color 10 n1674 n1674)) (.edge 6 (.edge 10 n1360 (.color 0 (.color 3 (.witness 36) n1695) (.color 3 n1695 (.witness 91)))) (.color 0 n1395 n1395)))
private def n1704 : Certificate := (.color 3 (.witness 106) (.witness 21))
private def n1708 : Certificate := (.edge 20 n36 (.edge 6 (.edge 10 n1360 (.color 0 n1704 n1704)) (.color 0 (.color 3 n1334 n1420) (.color 3 n1420 n1337))))
private def n1710 : Certificate := (.color 6 (.witness 73) (.witness 54))
private def n1711 : Certificate := (.color 0 n1710 n1710)
private def n1724 : Certificate := (.edge 20 (.edge 13 n36 (.edge 16 n44 (.color 0 (.color 6 (.witness 65) n13) (.color 6 (.witness 65) n13)))) (.edge 6 (.edge 10 n1360 n1599) (.color 0 (.color 3 n567 n568) (.color 3 n568 n570))))
private def n1729 : Certificate := (.edge 10 n1360 (.color 4 (.color 16 n456 n1639) (.color 16 n1639 n459)))
private def n1732 : Certificate := (.edge 16 (.edge 17 n44 n558) (.color 0 n430 n430))
private def n1735 : Certificate := (.witness 112)
private def n1736 : Certificate := (.color 10 n365 n364)
private def n1738 : Certificate := (.witness 15)
private def n1740 : Certificate := (.color 0 (.color 6 n1735 n1736) (.color 6 n1736 n1738))
private def n1744 : Certificate := (.edge 17 (.edge 19 n83 (.edge 20 n44 (.color 0 (.witness 116) (.witness 11)))) n1711)
private def n1746 : Certificate := (.color 15 (.witness 69) (.witness 58))
private def n1750 : Certificate := (.color 16 (.witness 69) (.witness 58))
private def n1759 : Certificate := (.edge 5 (.edge 19 n295 (.edge 20 n484 (.edge 10 n10 (.edge 2 (.edge 15 n5 (.edge 16 n8 (.color 2 n1659 n1660))) (.edge 11 (.edge 12 (.edge 15 n486 n1446) (.edge 13 n1665 n1666)) n365))))) (.edge 2 (.edge 15 n5 (.edge 16 n8 (.edge 14 (.edge 6 (.edge 10 n1360 (.edge 11 n1675 n1680)) (.edge 11 (.edge 17 n306 n1686) (.color 12 n1677 n1678))) (.witness 58)))) (.edge 14 (.edge 11 (.edge 17 n306 (.edge 12 (.edge 15 n486 (.edge 19 n77 n1701)) (.edge 13 (.edge 16 n331 n1708) n1711))) (.edge 19 (.edge 12 n77 (.edge 17 (.edge 15 n83 n1724) (.color 6 n1438 n1439))) (.edge 20 (.edge 13 n36 (.edge 6 n1729 n1732)) (.color 0 (.color 6 n1735 n1736) (.color 6 n1736 n1738))))) (.edge 11 (.edge 15 (.edge 12 n486 (.edge 16 (.edge 13 n331 n1744) (.color 11 n1746 n1746))) (.color 11 n1750 n1750)) (.color 15 (.color 16 (.witness 69) n1636) (.color 16 n1636 (.witness 58)))))))
private def n1762 : Certificate := (.color 13 (.witness 90) (.witness 37))
private def n1763 : Certificate := (.edge 16 n331 n1762)
private def n1766 : Certificate := (.edge 12 (.edge 18 n106 n1762) (.color 6 n1762 n1762))
private def n1772 : Certificate := (.edge 12 (.edge 18 n106 (.color 9 n1762 n1762)) (.color 11 n1762 n1762))
private def n1781 : Certificate := (.color 5 (.witness 58) (.witness 69))
private def n1787 : Certificate := (.edge 14 (.edge 17 n306 (.color 9 n1762 n1762)) (.edge 6 (.edge 9 n1247 (.color 0 (.color 3 (.witness 68) n1781) (.color 3 n1781 (.witness 59)))) n1310))
private def n1792 : Certificate := (.edge 20 n36 (.edge 6 (.edge 9 n1247 (.color 0 n1704 n1704)) n1339))
private def n1794 : Certificate := (.color 6 (.witness 41) (.witness 86))
private def n1808 : Certificate := (.edge 20 (.edge 14 n36 (.edge 17 n44 (.color 0 (.color 6 (.witness 33) (.witness 94)) (.color 6 (.witness 33) (.witness 94))))) (.edge 6 (.edge 9 n1247 n1599) (.color 0 (.color 3 n567 n676) (.color 3 n676 n570))))
private def n1812 : Certificate := (.edge 9 n1247 (.color 13 (.color 16 n456 n1639) (.color 16 n1639 n459)))
private def n1815 : Certificate := (.edge 16 (.edge 17 n44 (.color 0 n387 n387)) n821)
private def n1818 : Certificate := (.color 9 (.witness 13) (.witness 114))
private def n1826 : Certificate := (.color 3 (.witness 74) (.witness 53))
private def n1828 : Certificate := (.edge 17 (.edge 14 n306 (.edge 20 n44 (.color 0 (.witness 116) (.witness 11)))) (.color 0 n1826 n1826))
private def n1830 : Certificate := (.color 6 n1347 n1347)
private def n1833 : Certificate := (.color 17 (.witness 37) (.witness 90))
private def n1842 : Certificate := (.edge 10 n10 (.edge 2 (.edge 15 n5 (.edge 17 n12 (.edge 13 (.edge 6 (.edge 9 n1247 (.edge 11 n1763 n1766)) (.edge 11 (.edge 16 n331 n1772) (.color 12 n1762 n1762))) (.witness 37)))) (.edge 13 (.edge 11 (.edge 16 n331 (.edge 12 (.edge 15 n486 (.edge 18 n106 n1787)) (.edge 14 (.edge 17 n306 n1792) (.color 0 n1794 n1794)))) (.edge 18 (.edge 12 n106 (.edge 16 (.edge 15 n110 n1808) n1602)) (.edge 20 (.edge 14 n36 (.edge 6 n1812 n1815)) (.color 0 (.color 6 n1735 n1818) (.color 6 n1818 n1738))))) (.edge 11 (.edge 15 (.edge 12 n486 (.edge 16 (.edge 18 n110 n1828) n1830)) (.color 11 (.color 16 n456 n1833) (.color 16 n1833 n459))) (.color 15 n1605 n1605)))))
private def n1844 : Certificate := (.color 15 (.witness 101) (.witness 26))
private def n1846 : Certificate := (.edge 20 n44 (.color 3 n1844 n1844))
private def n1852 : Certificate := (.edge 6 (.edge 14 n1360 (.edge 9 (.edge 20 n35 (.color 11 n1844 n1844)) n1711)) (.color 0 n749 n749))
private def n1859 : Certificate := (.edge 6 (.edge 13 n1247 (.edge 10 (.edge 20 n35 (.color 11 n1844 n1844)) (.color 0 n1794 n1794))) n849)
private def n1866 : Certificate := (.edge 13 (.edge 6 n1247 (.color 14 (.color 19 n178 n468) (.color 19 n468 n175))) (.edge 18 (.edge 19 n129 n1830) n399))
private def n1870 : Certificate := (.edge 13 n36 (.edge 6 (.edge 10 n1360 (.edge 18 (.edge 19 n129 n1830) n399)) n421))
private def n1872 : Certificate := (.color 6 n1469 n1469)
private def n1873 : Certificate := (.edge 18 (.edge 19 n129 n442) n1872)
private def n1876 : Certificate := (.edge 13 n1247 n1557)
private def n1883 : Certificate := (.edge 13 n106 (.color 6 n1251 n1252))
private def n1889 : Certificate := (.edge 9 n1247 (.edge 14 (.edge 10 n1360 n1602) n442))
private def n1891 : Certificate := (.edge 20 (.edge 14 n36 n849) n171)
private def n1894 : Certificate := (.edge 14 n1360 n1382)
private def n1897 : Certificate := (.color 0 (.color 9 n429 n1382) (.color 9 n1382 n432))
private def n1904 : Certificate := (.edge 10 n35 (.color 9 n1352 n1352))
private def n1909 : Certificate := (.edge 14 (.edge 13 n36 (.color 0 (.color 6 n429 n1382) (.color 6 n1382 n432))) n1746)
private def n1914 : Certificate := (.edge 13 n1247 (.edge 10 (.edge 14 n1360 n1844) (.color 0 (.color 6 n1735 n1818) (.color 6 n1818 n1738))))
private def n1916 : Certificate := (.color 0 (.witness 112) (.witness 15))
private def n1920 : Certificate := (.edge 9 n1247 n1437)
private def n1921 : Certificate := (.color 15 (.witness 37) (.witness 90))
private def n1923 : Certificate := (.edge 12 (.edge 19 n77 n1921) n399)
private def n1927 : Certificate := (.edge 9 (.edge 10 n35 n1923) n558)
private def n1929 : Certificate := (.edge 19 n77 n1916)
private def n1941 : Certificate := (.edge 2 n5 (.edge 11 (.edge 12 n486 (.edge 16 (.edge 13 n331 (.edge 18 n110 (.edge 17 (.edge 14 n306 n1846) (.edge 10 n1852 n399)))) (.edge 17 (.edge 14 n306 (.edge 19 n83 (.edge 9 n1859 n442))) (.edge 20 (.edge 9 (.edge 10 n35 n1866) (.edge 14 n1870 n1873)) (.edge 6 (.edge 9 n1876 n1558) (.witness 22)))))) (.edge 18 (.edge 16 n110 (.edge 19 (.edge 20 n129 (.edge 17 n83 (.edge 12 n1883 n1557))) (.edge 13 (.edge 12 n106 (.edge 6 n1889 n1891)) (.edge 10 (.edge 6 n1894 n1897) n459)))) (.edge 17 (.edge 19 n83 (.edge 20 (.edge 16 n44 (.edge 9 n1904 n1909)) (.edge 6 (.edge 9 n1914 n1740) n1916))) (.edge 14 (.edge 6 (.edge 10 n1360 (.edge 13 n1920 n1923)) (.edge 20 (.edge 13 n36 n1927) (.edge 12 n1929 n171))) (.edge 9 (.edge 6 (.edge 13 n1247 n1290) (.color 0 n1290 n1290)) (.witness 50)))))))
private def n1951 : Certificate := (.edge 17 n306 (.edge 12 (.edge 18 n106 (.color 3 (.color 12 (.witness 106) (.color 19 (.witness 5) (.witness 122))) (.color 12 (.color 19 (.witness 5) (.witness 122)) (.witness 21)))) (.color 0 (.color 2 (.witness 20) n1704) (.color 2 n1704 (.witness 107)))))
private def n1953 : Certificate := (.color 2 (.witness 114) (.witness 13))
private def n1954 : Certificate := (.color 0 n1953 n1953)
private def n1956 : Certificate := (.edge 18 n106 (.edge 19 n77 n1954))
private def n1961 : Certificate := (.edge 18 n106 (.edge 19 n77 (.color 0 (.witness 120) (.witness 7))))
private def n1962 : Certificate := (.color 2 (.witness 22) (.witness 105))
private def n1963 : Certificate := (.color 0 n1962 n1962)
private def n1975 : Certificate := (.edge 17 n44 (.edge 18 (.edge 12 n106 (.color 3 n28 n30)) (.color 0 (.color 2 n386 n387) (.color 2 n387 n389))))
private def n1977 : Certificate := (.color 0 n183 n183)
private def n1979 : Certificate := (.edge 12 n106 (.edge 19 n129 n1977))
private def n1983 : Certificate := (.color 13 (.witness 26) (.witness 101))
private def n1989 : Certificate := (.color 6 (.witness 97) (.witness 30))
private def n1990 : Certificate := (.color 0 n1989 n1989)
private def n1996 : Certificate := (.color 18 (.witness 69) (.witness 58))
private def n2006 : Certificate := (.edge 16 n44 (.edge 19 (.edge 12 n77 (.color 3 n426 n426)) (.color 0 (.color 2 n429 n430) (.color 2 n430 n432))))
private def n2009 : Certificate := (.edge 18 n129 (.color 0 n234 n234))
private def n2010 : Certificate := (.edge 12 n77 n2009)
private def n2014 : Certificate := (.color 14 (.witness 26) (.witness 101))
private def n2015 : Certificate := (.color 12 n38 n2014)
private def n2016 : Certificate := (.color 12 n2014 n37)
private def n2025 : Certificate := (.color 19 (.witness 37) (.witness 90))
private def n2029 : Certificate := (.color 20 (.witness 26) (.witness 101))
private def n2034 : Certificate := (.color 18 n243 n2029)
private def n2035 : Certificate := (.color 18 n2029 n242)
private def n2036 : Certificate := (.color 16 n2034 n2035)
private def n2040 : Certificate := (.edge 13 (.edge 14 (.edge 20 n36 (.edge 6 (.edge 9 n1247 (.edge 10 n1360 (.edge 11 (.edge 16 n331 n1951) (.edge 12 n1956 n154)))) (.edge 11 (.edge 16 n331 (.edge 17 n306 (.edge 12 n1961 n1963))) n1091))) (.edge 9 (.edge 6 n1247 (.edge 20 (.edge 10 n35 (.edge 16 (.edge 11 n331 n1975) (.edge 18 n1979 n1456))) (.color 11 (.color 12 n38 n1983) (.color 12 n1983 n37)))) (.edge 16 (.edge 11 n331 (.edge 18 (.edge 12 n106 (.edge 20 n691 n1990)) (.color 2 n1750 n1750))) (.color 13 n1996 n1996)))) (.edge 14 (.edge 10 (.edge 6 n1360 (.edge 20 (.edge 9 n35 (.edge 17 (.edge 11 n306 n2006) (.edge 19 n2010 n1464))) (.color 11 n2015 n2016))) (.edge 17 (.edge 11 n306 (.edge 19 (.edge 12 n77 (.edge 20 n589 n1990)) (.color 2 (.color 16 n456 n1833) (.color 16 n1833 n459)))) (.color 14 n2025 n2025))) (.edge 20 (.edge 9 (.edge 10 n35 (.color 17 (.color 19 (.witness 37) n2029) (.color 19 n2029 (.witness 90)))) n2036) n164)))
private def n2048 : Certificate := (.color 15 n165 (.color 19 (.witness 10) (.witness 117)))
private def n2049 : Certificate := (.color 15 (.color 19 (.witness 10) (.witness 117)) n164)
private def n2055 : Certificate := (.edge 18 n110 (.color 12 n1844 n1844))
private def n2056 : Certificate := (.color 2 n1844 n1844)
private def n2065 : Certificate := (.edge 13 (.edge 16 n331 (.color 2 n725 n725)) n725)
private def n2071 : Certificate := (.color 9 (.witness 69) (.witness 58))
private def n2074 : Certificate := (.edge 18 n106 (.edge 14 (.edge 17 n306 (.edge 19 n77 (.color 0 (.witness 120) (.witness 7)))) (.color 0 n2071 n2071)))
private def n2079 : Certificate := (.color 10 (.witness 53) (.witness 74))
private def n2080 : Certificate := (.color 9 (.witness 72) n2079)
private def n2081 : Certificate := (.color 9 n2079 (.witness 55))
private def n2084 : Certificate := (.edge 18 n110 (.edge 17 (.edge 14 n306 n1844) (.color 0 n2080 n2081)))
private def n2087 : Certificate := (.color 9 (.witness 85) (.witness 42))
private def n2090 : Certificate := (.edge 15 (.edge 19 n83 (.color 0 n2087 n2087)) n1081)
private def n2097 : Certificate := (.edge 16 n110 (.edge 19 (.edge 14 n77 n2056) n858))
private def n2105 : Certificate := (.edge 5 n10 (.edge 6 (.edge 13 (.triangle 17) (.edge 14 (.triangle 18) (.edge 8 (.edge 12 (.triangle 16) (.edge 18 n105 (.color 8 n2048 n2049))) (.edge 15 (.edge 11 (.edge 12 n486 n1844) (.edge 16 n2055 n2056)) (.witness 26))))) (.edge 8 (.edge 18 n105 (.edge 19 (.triangle 23) (.edge 11 (.edge 12 (.edge 15 n486 n2065) n725) (.witness 14)))) (.edge 11 (.edge 12 (.edge 15 n486 (.edge 13 (.edge 16 n331 n2074) (.color 11 n2015 n2016))) (.edge 16 (.edge 13 n331 (.edge 15 n2084 n1081)) (.edge 17 (.edge 14 n306 n2090) n1521))) (.edge 12 (.edge 18 (.edge 13 n106 (.edge 15 n2097 n1091)) (.color 12 (.color 15 n38 n254) (.color 15 n254 n37))) n171)))))
private def n2108 : Certificate := (.edge 17 n44 (.edge 14 n36 n107))
private def n2111 : Certificate := (.color 0 (.color 2 n567 n676) (.color 2 n676 n570))
private def n2120 : Certificate := (.color 2 n171 n171)
private def n2122 : Certificate := (.edge 5 n12 (.edge 11 (.edge 14 n306 (.edge 15 (.edge 19 n83 (.color 0 n182 n185)) n1081)) n2120))
private def n2127 : Certificate := (.edge 11 (.edge 14 n306 (.color 15 n669 n670)) (.edge 15 (.edge 19 n83 n1352) (.color 0 n567 n570)))
private def n2134 : Certificate := (.edge 15 n486 (.edge 19 n77 (.color 0 (.witness 120) (.witness 7))))
private def n2135 : Certificate := (.color 9 (.witness 21) (.witness 106))
private def n2138 : Certificate := (.color 0 (.color 8 n1334 n2135) (.color 8 n2135 n1337))
private def n2147 : Certificate := (.edge 19 n83 (.edge 2 (.edge 5 n12 (.color 0 (.color 8 n182 n2087) (.color 8 n2087 n185))) (.color 0 n842 n842)))
private def n2150 : Certificate := (.color 2 (.witness 70) (.witness 57))
private def n2160 : Certificate := (.edge 15 n83 (.edge 2 (.edge 5 n12 n217) (.color 0 (.color 8 n567 n1316) (.color 8 n1316 n570))))
private def n2161 : Certificate := (.color 13 (.witness 74) (.witness 53))
private def n2164 : Certificate := (.color 5 (.witness 14) (.witness 113))
private def n2176 : Certificate := (.edge 6 n1247 (.edge 18 (.edge 12 n106 (.edge 8 n105 (.edge 16 (.edge 11 n331 (.edge 15 n110 (.edge 20 n2108 n2111))) (.edge 20 (.edge 14 n36 (.edge 19 n129 n1977)) (.edge 17 (.edge 2 n2122 n2127) n1521))))) (.edge 11 (.edge 16 n331 (.edge 14 (.edge 17 n306 (.edge 20 n36 (.edge 12 n2134 n2138))) (.edge 15 (.edge 12 n486 (.edge 17 n2147 n781)) (.color 0 n2150 n2150)))) (.edge 14 (.edge 20 n36 (.edge 19 (.edge 12 n77 (.edge 17 n2160 n2161)) (.color 0 (.color 2 n1735 n2164) (.color 2 n2164 n1738)))) (.edge 17 (.edge 2 (.edge 5 n12 n275) (.color 15 (.color 16 n637 n275) (.color 16 n275 n639))) (.witness 49))))))
private def n2178 : Certificate := (.edge 11 n486 (.edge 14 n77 n161))
private def n2181 : Certificate := (.color 0 (.color 6 n1334 n2135) (.color 6 n2135 n1337))
private def n2190 : Certificate := (.edge 14 n306 (.edge 2 (.edge 5 n12 (.color 0 (.color 6 n182 n2087) (.color 6 n2087 n185))) (.color 0 n1794 n1794)))
private def n2193 : Certificate := (.color 2 (.color 11 n456 n1921) (.color 11 n1921 n459))
private def n2196 : Certificate := (.color 2 (.witness 82) (.witness 45))
private def n2206 : Certificate := (.edge 11 n306 (.edge 2 (.edge 5 n12 n1990) (.color 0 (.color 6 n567 n1316) (.color 6 n1316 n570))))
private def n2207 : Certificate := (.color 18 (.witness 74) (.witness 53))
private def n2210 : Certificate := (.color 5 (.witness 26) (.witness 101))
private def n2223 : Certificate := (.color 17 (.witness 53) (.witness 74))
private def n2227 : Certificate := (.color 8 (.witness 101) (.witness 26))
private def n2228 : Certificate := (.edge 20 n44 n2227)
private def n2237 : Certificate := (.edge 6 (.edge 8 (.edge 12 n1103 (.color 2 (.color 11 n903 n2223) (.color 11 n2223 n905))) (.color 0 (.color 6 n1454 n2071) (.color 6 n2071 n1455))) n1456)
private def n2248 : Certificate := (.edge 6 (.edge 8 (.edge 12 n1103 (.color 11 (.color 16 n903 n2223) (.color 16 n2223 n905))) n579) (.color 0 (.color 8 n577 n1302) (.color 8 n1302 n578)))
private def n2260 : Certificate := (.edge 5 n12 (.edge 6 (.edge 8 n1103 (.color 9 (.color 16 n243 n2029) (.color 16 n2029 n242))) (.color 2 (.color 16 n637 n275) (.color 16 n275 n639))))
private def n2264 : Certificate := (.edge 6 (.edge 8 n1103 (.edge 16 (.edge 20 n44 n579) n1619)) n687)
private def n2270 : Certificate := (.color 6 (.witness 113) (.witness 14))
private def n2276 : Certificate := (.edge 8 (.edge 12 n1103 (.color 2 (.color 15 n903 n2223) (.color 15 n2223 n905))) n199)
private def n2279 : Certificate := (.color 0 (.color 8 (.witness 44) n857) (.color 8 n857 (.witness 83)))
private def n2285 : Certificate := (.edge 8 (.edge 12 n1103 (.color 15 (.color 16 n903 n2223) (.color 16 n2223 n905))) (.color 0 (.color 6 n1735 n1818) (.color 6 n1818 n1738)))
private def n2292 : Certificate := (.color 12 (.witness 74) (.witness 53))
private def n2298 : Certificate := (.edge 18 (.edge 8 n105 (.edge 15 (.edge 16 n110 (.edge 19 (.edge 17 n83 (.edge 20 n129 (.edge 12 n2178 n2181))) (.edge 11 (.edge 12 n486 (.edge 17 n2190 n2193)) (.color 0 n2196 n2196)))) (.edge 19 (.edge 20 n129 (.edge 14 (.edge 12 n77 (.edge 17 n2206 n2207)) (.color 0 (.color 2 n577 n2210) (.color 2 n2210 n578)))) (.edge 17 (.edge 2 (.edge 5 n12 (.color 14 n1833 n1833)) (.color 11 (.color 16 n456 n1833) (.color 16 n1833 n459))) (.witness 37))))) (.edge 17 (.edge 11 (.edge 14 n306 (.edge 15 (.edge 12 n486 (.edge 19 n83 (.color 5 n2223 n2223))) (.edge 2 (.edge 5 n12 (.edge 16 n2228 n2237)) (.edge 16 (.edge 20 n44 n2248) n1618)))) (.edge 19 (.edge 15 n83 (.edge 12 (.edge 14 n77 (.edge 2 n2260 n2264)) (.color 2 (.color 16 n903 n2223) (.color 16 n2223 n905)))) (.edge 2 (.edge 5 n12 (.edge 16 (.edge 20 n44 n2270) (.edge 6 n2276 n2279))) (.edge 16 (.edge 20 n44 (.edge 6 n2285 n1916)) n1198)))) (.edge 12 (.edge 6 (.edge 8 n1103 n2292) (.color 11 n2292 n2292)) (.witness 53))))
private def n2305 : Certificate := (.edge 12 n77 (.edge 15 n83 (.color 8 (.color 18 n903 n905) (.color 18 n903 n905))))
private def n2308 : Certificate := (.color 0 (.color 6 n429 n1198) (.color 6 n1198 n432))
private def n2319 : Certificate := (.color 6 (.color 12 n178 n1352) (.color 12 n1352 n175))
private def n2321 : Certificate := (.edge 8 n1103 (.edge 11 (.edge 15 n486 (.edge 13 (.edge 18 n106 (.color 0 (.witness 68) (.witness 59))) n1830)) n2319))
private def n2329 : Certificate := (.edge 11 (.edge 15 n486 (.color 8 (.color 12 n178 n702) (.color 12 n702 n175))) (.edge 13 (.edge 18 n106 n657) (.color 0 n429 n432)))
private def n2337 : Certificate := (.edge 13 n331 (.edge 18 n110 (.color 0 (.witness 116) (.witness 11))))
private def n2338 : Certificate := (.color 5 (.witness 42) (.witness 85))
private def n2341 : Certificate := (.color 0 (.color 4 n440 n2338) (.color 4 n2338 n441))
private def n2345 : Certificate := (.color 4 (.witness 68) n1781)
private def n2346 : Certificate := (.color 4 n1781 (.witness 59))
private def n2350 : Certificate := (.edge 18 n106 (.edge 6 (.edge 8 n1103 (.color 0 n2345 n2346)) n1192))
private def n2351 : Certificate := (.color 6 n1234 n1234)
private def n2357 : Certificate := (.color 4 (.witness 82) (.witness 45))
private def n2360 : Certificate := (.color 4 n429 n646)
private def n2361 : Certificate := (.color 4 n646 n432)
private def n2364 : Certificate := (.edge 13 n106 (.edge 6 (.edge 8 n1103 (.color 0 n2357 n2357)) (.color 0 n2360 n2361)))
private def n2367 : Certificate := (.color 8 n365 n364)
private def n2379 : Certificate := (.edge 2 n12 (.edge 20 (.edge 16 n44 (.edge 4 n484 (.edge 14 (.edge 11 n306 (.edge 13 n36 (.edge 19 n2305 n2308))) (.edge 19 (.edge 15 n83 (.edge 18 n129 n1619)) (.edge 12 (.edge 6 n2321 n2329) n442))))) (.edge 11 (.edge 14 n306 (.edge 15 (.edge 12 n486 (.edge 19 n83 (.edge 16 n2337 n2341))) (.edge 13 (.edge 16 n331 (.edge 12 n2350 n2351)) n1566))) (.edge 15 (.edge 19 n83 (.edge 18 (.edge 16 n110 (.edge 12 n2364 n1570)) (.color 0 (.color 6 n1735 n2367) (.color 6 n2367 n1738)))) (.edge 12 (.edge 6 (.edge 8 n1103 n1239) n1239) n591)))))
private def n2381 : Certificate := (.edge 11 n331 (.edge 15 n110 (.color 0 n211 n212)))
private def n2384 : Certificate := (.color 0 (.color 2 n440 n2338) (.color 2 n2338 n441))
private def n2393 : Certificate := (.edge 15 n486 (.edge 6 (.edge 8 n1103 (.color 0 (.color 2 (.witness 68) n1781) (.color 2 n1781 (.witness 59)))) (.color 0 n2150 n2150)))
private def n2396 : Certificate := (.color 6 (.color 11 n29 n2161) (.color 11 n2161 n24))
private def n2409 : Certificate := (.edge 11 n486 (.edge 6 (.edge 8 n1103 (.color 0 n2196 n2196)) (.color 0 (.color 2 n429 n646) (.color 2 n646 n432))))
private def n2412 : Certificate := (.color 8 (.color 15 (.witness 37) n2207) (.color 15 n2207 (.witness 90)))
private def n2415 : Certificate := (.color 8 (.witness 37) (.witness 90))
private def n2424 : Certificate := (.color 12 (.witness 106) (.witness 21))
private def n2428 : Certificate := (.edge 19 n77 n1695)
private def n2434 : Certificate := (.edge 2 (.edge 4 (.edge 16 n8 (.color 6 (.color 11 (.witness 17) n2424) (.color 11 n2424 (.witness 110)))) (.color 0 (.color 2 n577 n2210) (.color 2 n2210 n578))) n579)
private def n2440 : Certificate := (.edge 2 (.edge 4 (.edge 16 n8 (.color 11 n2424 n2424)) n1464) n1223)
private def n2454 : Certificate := (.edge 4 n8 (.edge 6 (.edge 8 n1103 (.color 12 (.color 18 n267 n2025) (.color 18 n2025 n270))) (.edge 14 (.edge 19 n77 n1464) (.color 0 n138 n138))))
private def n2455 : Certificate := (.color 6 n1239 n1239)
private def n2463 : Certificate := (.edge 4 (.edge 16 n8 (.color 6 n2424 n2424)) n250)
private def n2465 : Certificate := (.color 4 (.witness 76) (.color 5 (.witness 50) (.witness 77)))
private def n2466 : Certificate := (.color 4 (.color 5 (.witness 50) (.witness 77)) (.witness 51))
private def n2467 : Certificate := (.color 0 n2465 n2466)
private def n2472 : Certificate := (.edge 4 (.edge 16 n8 n2424) (.color 0 (.color 2 n1735 n2164) (.color 2 n2164 n1738)))
private def n2479 : Certificate := (.color 16 (.witness 21) (.witness 106))
private def n2488 : Certificate := (.edge 20 (.edge 4 n484 (.edge 13 (.edge 14 n36 (.edge 18 (.edge 12 n106 (.edge 19 n129 (.edge 16 n2381 n2384))) (.edge 11 (.edge 16 n331 (.edge 12 n2393 n2396)) (.color 0 (.color 6 n29 n24) (.color 6 n29 n24))))) (.edge 18 (.edge 19 n129 (.edge 15 (.edge 16 n110 (.edge 12 n2409 n2412)) (.color 0 (.color 6 n1218 n2415) (.color 6 n2415 n1221)))) (.edge 12 (.edge 6 (.edge 8 n1103 n2292) (.color 11 n2292 n2292)) (.witness 53))))) (.edge 12 (.edge 11 (.edge 15 n486 (.edge 13 (.edge 16 n331 (.edge 18 n106 (.color 8 n2424 n2424))) (.edge 6 (.edge 8 n1103 (.edge 14 n2428 n2434)) (.edge 14 (.edge 19 n77 n2440) n138)))) (.edge 18 (.edge 13 n106 (.edge 16 (.edge 15 n110 (.edge 2 n2454 n2455)) (.color 6 n2424 n2424))) (.edge 6 (.edge 8 n1103 (.edge 14 (.edge 19 n77 n1953) (.edge 2 n2463 n2467))) (.edge 14 (.edge 19 n77 (.edge 2 n2472 n1916)) n534)))) (.edge 16 (.edge 2 (.edge 4 n8 (.color 13 n2479 n2479)) (.color 11 (.color 15 n590 n2479) (.color 15 n2479 n591))) (.witness 21))))
private def n2496 : Certificate := (.edge 6 (.edge 8 n1103 (.color 0 (.color 6 (.witness 120) (.color 10 (.witness 5) (.witness 122))) (.color 6 (.color 10 (.witness 5) (.witness 122)) (.witness 7)))) (.color 0 (.witness 120) (.witness 7)))
private def n2502 : Certificate := (.color 0 (.color 2 (.witness 36) n1695) (.color 2 n1695 (.witness 91)))
private def n2505 : Certificate := (.color 2 (.witness 38) (.witness 89))
private def n2518 : Certificate := (.edge 4 n8 (.edge 15 (.edge 18 n110 (.edge 17 (.edge 20 n44 (.color 0 (.witness 12) (.witness 115))) (.color 6 n2292 n2292))) (.color 2 (.color 16 n456 n1833) (.color 16 n1833 n459))))
private def n2523 : Certificate := (.edge 15 (.edge 18 n110 (.color 4 (.color 16 n456 n1639) (.color 16 n1639 n459))) (.edge 17 (.edge 20 n44 n2455) (.color 0 (.witness 36) (.witness 91))))
private def n2529 : Certificate := (.color 4 (.witness 14) (.witness 113))
private def n2541 : Certificate := (.edge 19 n77 (.edge 11 (.edge 15 n486 (.edge 17 n306 (.edge 13 (.edge 16 n331 (.edge 18 n106 (.edge 20 n36 n2496))) (.edge 6 (.edge 8 n1103 (.edge 10 n1360 n2502)) (.color 0 n2505 n2505))))) (.edge 6 (.edge 8 n1103 (.edge 10 n1360 (.edge 13 (.edge 18 n106 (.edge 20 n36 n1954)) (.edge 16 (.edge 2 n2518 n2523) n199)))) (.edge 13 (.edge 18 n106 (.edge 20 n36 (.color 0 (.color 2 n1735 n2529) (.color 2 n2529 n1738)))) (.edge 16 (.edge 2 (.edge 4 n8 n224) (.color 15 n224 n224)) n78)))))
private def n2547 : Certificate := (.edge 8 (.edge 6 n1103 (.color 0 (.color 8 (.witness 108) (.color 10 (.witness 17) (.witness 110))) (.color 8 (.color 10 (.witness 17) (.witness 110)) (.witness 19)))) n161)
private def n2550 : Certificate := (.color 6 (.witness 81) (.witness 46))
private def n2554 : Certificate := (.color 2 n386 n534)
private def n2555 : Certificate := (.color 2 n534 n389)
private def n2556 : Certificate := (.color 0 n2554 n2555)
private def n2559 : Certificate := (.edge 4 n8 n285)
private def n2562 : Certificate := (.edge 17 (.edge 20 n44 n1916) (.color 0 n1176 n1176))
private def n2564 : Certificate := (.color 12 (.witness 42) (.witness 85))
private def n2570 : Certificate := (.edge 2 (.edge 4 n8 (.color 0 n2270 n2270)) n1740)
private def n2575 : Certificate := (.color 2 (.witness 50) (.witness 77))
private def n2583 : Certificate := (.edge 4 n8 (.edge 10 (.edge 19 n76 n285) (.color 2 (.color 16 n637 n275) (.color 16 n275 n639))))
private def n2588 : Certificate := (.edge 10 (.edge 19 n76 n2562) (.edge 17 (.edge 20 n44 n1239) (.color 0 n386 n389)))
private def n2591 : Certificate := (.color 8 (.witness 69) (.witness 58))
private def n2598 : Certificate := (.edge 16 (.edge 17 n44 (.edge 2 (.edge 4 n8 n781) (.color 8 (.color 12 n233 n605) (.color 12 n605 n232)))) n1456)
private def n2604 : Certificate := (.edge 17 (.edge 20 n44 (.color 0 n2227 n2227)) n1464)
private def n2615 : Certificate := (.edge 19 n129 (.color 0 n1585 n1585))
private def n2619 : Certificate := (.color 4 (.witness 26) (.witness 101))
private def n2628 : Certificate := (.edge 15 (.edge 11 n486 (.edge 18 (.edge 16 (.triangle 31) (.edge 13 n106 (.edge 19 (.edge 17 (.triangle 32) (.edge 20 n129 n2547)) n2550))) (.edge 8 (.edge 6 (.triangle 16) (.edge 19 (.edge 17 (.triangle 32) (.edge 10 n76 n2556)) (.edge 16 (.edge 2 n2559 n2562) n2564))) (.edge 17 (.edge 19 (.triangle 32) (.edge 16 (.edge 20 n44 n2570) (.color 6 n2564 n2564))) (.color 0 n2575 n2575))))) (.edge 8 (.edge 6 (.triangle 16) (.edge 13 (.edge 18 n106 (.edge 16 (.edge 11 n331 (.edge 2 n2583 n2588)) (.color 0 n2591 n2591))) (.edge 19 (.edge 10 n76 (.edge 20 (.edge 18 n129 n2598) (.color 0 n138 n138))) (.edge 16 (.edge 2 (.edge 4 n8 n2604) n586) n836)))) (.edge 13 (.edge 18 n106 (.edge 16 (.edge 11 n331 (.color 2 n1750 n1750)) (.witness 58))) (.edge 16 (.edge 20 (.edge 17 n44 (.edge 2 (.edge 4 n8 n2036) (.edge 18 n2615 n1872))) (.color 0 (.color 2 (.witness 100) n2619) (.color 2 n2619 (.witness 27)))) (.color 12 n1996 n1996)))))
private def n2630 : Certificate := (.color 16 (.witness 85) (.witness 42))
private def n2636 : Certificate := (.edge 10 (.edge 19 n76 (.color 11 n2630 n2630)) n1566)
private def n2645 : Certificate := (.edge 10 (.edge 14 n1360 (.color 15 n2630 n2630)) (.color 0 (.color 6 n1735 n2367) (.color 6 n2367 n1738)))
private def n2653 : Certificate := (.edge 14 n1360 (.edge 8 (.edge 19 n76 (.color 2 n2630 n2630)) n1990))
private def n2658 : Certificate := (.color 8 n567 n1402)
private def n2659 : Certificate := (.color 8 n1402 n570)
private def n2670 : Certificate := (.edge 4 n8 (.edge 8 (.edge 19 n76 (.color 8 (.color 15 n38 n205) (.color 15 n205 n37))) n2120))
private def n2676 : Certificate := (.edge 8 (.edge 19 n76 (.edge 15 (.edge 18 n110 n1916) (.color 0 n2658 n2659))) (.edge 15 (.edge 18 n110 n417) (.color 0 n567 n570)))
private def n2689 : Certificate := (.edge 2 (.edge 4 n8 (.edge 8 (.edge 10 n76 n154) n1990)) (.color 8 (.color 18 (.witness 77) (.color 19 (.witness 34) (.witness 93))) (.color 18 (.color 19 (.witness 34) (.witness 93)) (.witness 50))))
private def n2691 : Certificate := (.color 2 (.witness 34) (.witness 93))
private def n2699 : Certificate := (.edge 10 (.edge 19 n76 (.color 2 (.color 15 (.witness 34) n2630) (.color 15 n2630 (.witness 93)))) (.color 0 (.color 6 n29 n24) (.color 6 n29 n24)))
private def n2708 : Certificate := (.color 6 (.color 11 (.witness 97) n2014) (.color 11 n2014 (.witness 30)))
private def n2712 : Certificate := (.edge 2 (.edge 4 n8 n2708) (.edge 6 (.edge 14 n1360 n579) n421))
private def n2714 : Certificate := (.color 11 n590 n2479)
private def n2715 : Certificate := (.color 11 n2479 n591)
private def n2723 : Certificate := (.edge 10 (.edge 14 n1360 (.color 2 (.color 11 (.witness 34) n2630) (.color 11 n2630 (.witness 93)))) (.color 0 (.color 6 n1218 n2415) (.color 6 n2415 n1221)))
private def n2730 : Certificate := (.color 8 (.witness 72) n2079)
private def n2731 : Certificate := (.color 8 n2079 (.witness 55))
private def n2737 : Certificate := (.edge 19 n76 (.color 11 (.color 15 (.witness 34) n2630) (.color 15 n2630 (.witness 93))))
private def n2745 : Certificate := (.edge 17 (.edge 20 n44 (.edge 11 (.edge 14 n306 (.edge 13 n331 (.edge 15 (.edge 19 n83 (.color 4 n2630 n2630)) (.edge 2 (.edge 4 n8 n2227) (.edge 8 n2636 n579))))) (.edge 15 (.edge 19 n83 (.edge 18 n110 (.edge 2 (.edge 4 n8 n2270) (.edge 6 n2645 n1916)))) (.edge 2 (.edge 4 n8 (.edge 10 (.edge 6 n2653 n217) n154)) (.edge 10 (.edge 6 (.edge 14 n1360 n1402) (.color 0 n2658 n2659)) (.witness 29)))))) (.edge 13 (.edge 11 n331 (.edge 14 (.edge 20 n36 (.edge 10 (.edge 6 n1360 (.edge 2 n2670 n2676)) (.color 2 (.color 15 n590 n2479) (.color 15 n2479 n591)))) (.edge 18 (.edge 15 n110 (.edge 19 (.edge 20 n129 n2689) (.color 0 n2691 n2691))) (.edge 2 (.edge 4 n8 (.edge 8 n2699 n250)) n1176)))) (.edge 18 (.edge 15 n110 (.edge 19 (.edge 20 n129 (.edge 10 (.edge 8 n76 n2712) (.color 2 n2714 n2715))) (.edge 2 (.edge 4 n8 (.edge 6 n2723 n1464)) n1585))) (.edge 2 (.edge 4 n8 (.edge 10 (.edge 6 (.edge 14 n1360 n2079) (.color 0 n2730 n2731)) (.witness 53))) (.edge 10 (.edge 6 (.edge 14 n1360 (.edge 8 n2737 n1711)) (.color 0 n745 n745)) n399)))))
private def n2750 : Certificate := (.edge 20 (.edge 13 n36 n426) (.color 0 (.color 2 n567 n568) (.color 2 n568 n570)))
private def n2757 : Certificate := (.color 14 (.witness 42) (.witness 85))
private def n2758 : Certificate := (.color 13 n79 n2757)
private def n2759 : Certificate := (.color 13 n2757 n78)
private def n2763 : Certificate := (.color 2 (.witness 98) (.witness 29))
private def n2770 : Certificate := (.color 20 (.witness 21) (.witness 106))
private def n2776 : Certificate := (.color 19 (.witness 42) (.witness 85))
private def n2784 : Certificate := (.edge 14 (.edge 10 (.edge 6 n1360 (.edge 19 (.edge 8 n76 (.edge 17 (.edge 11 n306 (.edge 15 n83 n2750)) (.edge 20 (.edge 13 n36 n2009) n1521))) (.color 11 (.color 13 n79 n2757) (.color 13 n2757 n78)))) (.edge 17 (.edge 11 n306 (.edge 19 (.edge 15 n83 (.edge 20 (.edge 13 n36 n452) (.color 0 n2763 n2763))) (.color 6 (.color 13 n79 n2757) (.color 13 n2757 n78)))) (.color 14 (.color 19 (.witness 42) n2770) (.color 19 n2770 (.witness 85))))) (.edge 19 (.edge 8 (.edge 10 n76 (.color 17 n2776 n2776)) (.color 15 (.color 18 (.witness 69) n2776) (.color 18 n2776 (.witness 58)))) (.witness 42)))
private def n2794 : Certificate := (.edge 6 (.edge 7 n1102 (.edge 8 n1103 (.color 6 (.witness 121) (.witness 6)))) (.witness 6))
private def n2799 : Certificate := (.color 6 (.witness 120) (.witness 7))
private def n2806 : Certificate := (.edge 17 n306 (.edge 19 n77 (.edge 20 n36 (.edge 1 (.edge 2 n2 (.edge 3 n4 (.edge 4 n7 (.edge 5 n11 n2794)))) (.edge 6 (.edge 7 n1102 (.edge 8 n1103 n2799)) (.witness 7))))))
private def n2807 : Certificate := (.color 9 (.witness 68) (.witness 59))
private def n2814 : Certificate := (.edge 8 (.edge 19 n76 (.color 5 n938 n938)) (.color 7 n1076 n1077))
private def n2825 : Certificate := (.edge 3 (.edge 19 n295 n1781) (.color 2 n2345 n2346))
private def n2834 : Certificate := (.color 13 (.witness 27) (.witness 100))
private def n2840 : Certificate := (.edge 3 n295 (.edge 8 n76 (.edge 20 (.edge 4 n484 n2807) (.color 11 (.color 12 n567 n2834) (.color 12 n2834 n570)))))
private def n2841 : Certificate := (.color 12 (.witness 43) (.witness 84))
private def n2845 : Certificate := (.color 11 (.witness 112) (.witness 15))
private def n2846 : Certificate := (.edge 20 (.edge 4 n484 (.edge 9 n35 (.color 11 n2841 n2841))) n2845)
private def n2849 : Certificate := (.color 5 (.witness 56) (.witness 71))
private def n2850 : Certificate := (.color 4 n637 n2849)
private def n2851 : Certificate := (.color 4 n2849 n639)
private def n2852 : Certificate := (.color 3 n2850 n2851)
private def n2855 : Certificate := (.color 11 (.witness 51) (.witness 76))
private def n2858 : Certificate := (.color 12 (.witness 104) (.witness 23))
private def n2860 : Certificate := (.edge 20 (.edge 4 n484 (.edge 9 n35 n2855)) (.color 11 n2858 n2858))
private def n2862 : Certificate := (.color 2 n2850 n2851)
private def n2865 : Certificate := (.color 20 (.witness 7) (.witness 120))
private def n2871 : Certificate := (.color 10 (.witness 56) (.witness 71))
private def n2880 : Certificate := (.edge 1 (.edge 2 n2 (.edge 3 n4 (.edge 4 n7 (.edge 6 (.edge 7 n1102 (.edge 8 n1103 (.color 6 n2807 n2807))) (.edge 10 (.edge 7 (.edge 17 n305 n2814) (.color 8 n1076 n1077)) n639))))) (.edge 6 (.edge 7 n1102 (.edge 8 n1103 (.edge 9 n1247 (.edge 5 (.edge 2 (.edge 17 n12 n2825) (.color 3 n2345 n2346)) n242)))) (.edge 5 (.edge 17 (.edge 2 n12 (.edge 10 (.edge 7 n305 (.edge 19 n2840 n2846)) (.color 3 (.color 4 n637 n2849) (.color 4 n2849 n639)))) (.edge 19 (.edge 3 n295 (.edge 10 (.edge 8 n76 n2860) (.color 2 n2850 n2851))) (.color 5 (.color 10 n1454 n2865) (.color 10 n2865 n1455)))) (.edge 10 (.edge 7 (.edge 17 n305 n2871) (.color 8 (.color 9 n243 n2871) (.color 9 n2871 n242))) n1454))))
private def n2885 : Certificate := (.color 9 (.witness 89) (.color 10 (.witness 36) (.witness 91)))
private def n2886 : Certificate := (.color 9 (.color 10 (.witness 36) (.witness 91)) (.witness 38))
private def n2887 : Certificate := (.color 6 n2885 n2886)
private def n2893 : Certificate := (.edge 8 (.edge 18 n105 (.color 4 n875 n875)) (.color 7 n875 n875))
private def n2904 : Certificate := (.edge 3 (.edge 18 n9 n1695) (.color 2 n1695 n1695))
private def n2913 : Certificate := (.color 14 (.witness 27) (.witness 100))
private def n2919 : Certificate := (.edge 3 n9 (.edge 8 n105 (.edge 20 (.edge 5 n484 n875) (.color 11 (.color 12 n567 n2913) (.color 12 n2913 n570)))))
private def n2920 : Certificate := (.color 12 (.witness 75) (.witness 52))
private def n2924 : Certificate := (.edge 20 (.edge 5 n484 (.edge 10 n35 (.color 11 n2920 n2920))) n2845)
private def n2927 : Certificate := (.color 4 (.witness 88) (.witness 39))
private def n2928 : Certificate := (.color 3 n2927 n2927)
private def n2931 : Certificate := (.color 11 (.witness 83) (.witness 44))
private def n2934 : Certificate := (.edge 20 (.edge 5 n484 (.edge 10 n35 n2931)) (.color 11 n2858 n2858))
private def n2944 : Certificate := (.color 9 (.witness 88) (.witness 39))
private def n2946 : Certificate := (.color 8 n2944 n2944)
private def n2951 : Certificate := (.edge 1 (.edge 2 n2 (.edge 3 n4 (.edge 5 n11 (.edge 6 (.edge 7 n1102 (.edge 8 n1103 (.color 6 n2885 n2886))) (.edge 9 (.edge 7 (.edge 16 n330 n2893) (.color 8 n875 n875)) (.witness 38)))))) (.edge 6 (.edge 7 n1102 (.edge 8 n1103 (.edge 10 n1360 (.edge 4 (.edge 2 (.edge 16 n8 n2904) (.color 3 n1695 n1695)) (.witness 37))))) (.edge 4 (.edge 16 (.edge 2 n8 (.edge 9 (.edge 7 n330 (.edge 18 n2919 n2924)) n2928)) (.edge 18 (.edge 3 n9 (.edge 9 (.edge 8 n105 n2934) (.color 2 n2927 n2927))) (.color 4 (.color 9 n1218 n2865) (.color 9 n2865 n1221)))) (.edge 9 (.edge 7 (.edge 16 n330 n2944) n2946) n1221))))
private def n2954 : Certificate := (.color 20 (.witness 27) (.witness 100))
private def n2958 : Certificate := (.edge 10 n35 (.color 17 (.color 19 (.witness 36) n2954) (.color 19 n2954 (.witness 91))))
private def n2961 : Certificate := (.color 18 (.witness 68) n2954)
private def n2962 : Certificate := (.color 18 n2954 (.witness 59))
private def n2964 : Certificate := (.edge 16 (.edge 17 n44 (.color 10 (.color 19 (.witness 36) n2954) (.color 19 n2954 (.witness 91)))) (.color 4 n2961 n2962))
private def n2970 : Certificate := (.edge 16 (.edge 17 n44 (.color 5 (.color 19 (.witness 36) n2954) (.color 19 n2954 (.witness 91)))) (.color 9 n2961 n2962))
private def n2984 : Certificate := (.edge 18 (.edge 8 n105 (.color 5 (.color 19 (.witness 36) n2954) (.color 19 n2954 (.witness 91)))) (.edge 4 (.edge 5 n484 (.color 1 (.color 11 n386 n2920) (.color 11 n2920 n389))) n782))
private def n2990 : Certificate := (.edge 19 n129 (.edge 4 (.edge 5 n484 (.color 1 n2931 n2931)) (.color 1 (.color 11 n456 n821) (.color 11 n821 n459))))
private def n2992 : Certificate := (.color 1 n1191 n1191)
private def n3002 : Certificate := (.edge 19 (.edge 8 n76 (.color 4 n2961 n2962)) (.edge 4 (.edge 5 n484 (.color 1 n836 n836)) (.color 1 (.color 11 n429 n2841) (.color 11 n2841 n432))))
private def n3008 : Certificate := (.edge 8 (.edge 10 n76 (.color 7 (.color 11 n29 n687) (.color 11 n687 n24))) (.color 1 n2855 n2855))
private def n3015 : Certificate := (.color 1 (.witness 120) (.witness 7))
private def n3018 : Certificate := (.edge 10 (.edge 17 n305 (.edge 19 n76 n3015)) n2992)
private def n3020 : Certificate := (.color 7 (.witness 100) (.witness 27))
private def n3023 : Certificate := (.color 7 (.color 8 (.witness 100) n999) (.color 8 n999 (.witness 27)))
private def n3025 : Certificate := (.color 8 (.witness 100) (.witness 27))
private def n3029 : Certificate := (.edge 3 n4 (.edge 6 (.edge 7 n1102 (.edge 8 n1103 (.edge 20 (.edge 4 (.edge 5 n484 (.edge 9 n2958 n2964)) (.edge 9 (.edge 10 n35 n2970) (.color 16 n2961 n2962))) n578))) (.edge 20 (.edge 9 (.edge 10 n35 (.edge 16 (.edge 7 n330 (.edge 17 n44 n2984)) (.edge 18 (.edge 8 n105 n2990) n2992))) (.edge 17 (.edge 16 n44 (.edge 10 (.edge 7 n305 n3002) (.color 4 n697 n698))) (.edge 19 (.edge 18 n129 (.edge 4 n1208 n3008)) (.color 1 (.color 4 n1218 n1219) (.color 4 n1219 n1221))))) (.edge 7 (.edge 9 (.edge 16 n330 (.edge 8 (.edge 18 n105 n3018) n3020)) n3023) n3025))))
private def n3035 : Certificate := (.edge 18 (.edge 3 n9 (.color 10 (.color 19 (.witness 36) n2954) (.color 19 n2954 (.witness 91)))) (.edge 9 (.edge 10 n35 (.color 6 (.color 11 n386 n2920) (.color 11 n2920 n389))) n1872))
private def n3044 : Certificate := (.edge 19 n129 (.edge 9 (.edge 10 n35 (.color 6 n2931 n2931)) (.color 6 (.color 11 n79 n2564) (.color 11 n2564 n78))))
private def n3054 : Certificate := (.edge 19 (.edge 3 n295 (.color 9 n2961 n2962)) (.edge 9 (.edge 10 n35 n1830) (.color 6 (.color 11 n429 n2841) (.color 11 n2841 n432))))
private def n3059 : Certificate := (.edge 5 n295 (.color 9 (.color 16 n243 n2029) (.color 16 n2029 n242)))
private def n3065 : Certificate := (.edge 9 (.edge 10 n35 (.color 6 (.color 11 n29 n2292) (.color 11 n2292 n24))) (.color 6 n2855 n2855))
private def n3071 : Certificate := (.color 6 (.color 9 (.witness 88) (.color 10 (.witness 37) (.witness 90))) (.color 9 (.color 10 (.witness 37) (.witness 90)) (.witness 39)))
private def n3079 : Certificate := (.color 2 (.color 3 n577 n2619) (.color 3 n2619 n578))
private def n3080 : Certificate := (.edge 5 (.edge 17 n12 (.edge 19 n295 n2799)) n3079)
private def n3082 : Certificate := (.color 2 (.witness 100) (.witness 27))
private def n3089 : Certificate := (.color 3 (.witness 100) (.witness 27))
private def n3093 : Certificate := (.edge 7 n1102 (.edge 8 (.triangle 16) (.edge 20 (.edge 4 (.edge 5 n484 (.edge 16 (.edge 2 n8 (.edge 17 n44 n3035)) (.edge 18 (.edge 3 n9 n3044) (.color 6 n2071 n2071)))) (.edge 17 (.edge 16 n44 (.edge 5 (.edge 2 n12 n3054) (.color 9 n2034 n2035))) (.edge 19 (.edge 18 n129 (.edge 3 n3059 n3065)) n3071))) (.edge 2 (.edge 4 (.edge 16 n8 (.edge 3 (.edge 18 n9 n3080) n3082)) (.color 2 (.color 3 (.witness 100) n2210) (.color 3 n2210 (.witness 27)))) n3089))))
private def n3102 : Certificate := (.edge 7 n330 (.edge 18 (.edge 3 n9 (.edge 8 n105 (.color 12 (.color 18 (.witness 75) (.color 19 (.witness 36) (.witness 91))) (.color 18 (.color 19 (.witness 36) (.witness 91)) (.witness 52))))) (.color 11 n386 n389)))
private def n3104 : Certificate := (.edge 19 n129 n1395)
private def n3106 : Certificate := (.color 16 (.witness 71) (.witness 56))
private def n3111 : Certificate := (.edge 8 (.edge 10 (.edge 19 n76 n1395) (.color 7 (.color 11 n386 n3106) (.color 11 n3106 n389))) n1469)
private def n3116 : Certificate := (.color 18 (.witness 71) (.witness 56))
private def n3120 : Certificate := (.edge 10 n35 (.color 8 (.color 12 n182 n3116) (.color 12 n3116 n185)))
private def n3123 : Certificate := (.edge 7 (.edge 10 (.edge 17 n305 n2505) (.color 8 (.color 12 n182 n3116) (.color 12 n3116 n185))) n836)
private def n3127 : Certificate := (.color 8 n243 n2871)
private def n3128 : Certificate := (.color 8 n2871 n242)
private def n3129 : Certificate := (.color 7 n3127 n3128)
private def n3135 : Certificate := (.edge 19 n129 n2415)
private def n3139 : Certificate := (.edge 3 (.edge 5 (.edge 19 n295 n2415) (.color 2 (.color 11 n386 n3106) (.color 11 n3106 n389))) n781)
private def n3147 : Certificate := (.edge 2 (.edge 5 (.edge 17 n12 (.color 7 (.witness 37) (.witness 90))) (.color 3 (.color 12 n182 n3116) (.color 12 n3116 n185))) n1347)
private def n3158 : Certificate := (.edge 2 n12 (.edge 3 n295 (.color 7 (.color 8 (.witness 68) n938) (.color 8 n938 (.witness 59)))))
private def n3161 : Certificate := (.color 17 (.witness 39) (.witness 88))
private def n3162 : Certificate := (.color 10 n3161 n3161)
private def n3164 : Certificate := (.color 11 n429 n3161)
private def n3165 : Certificate := (.color 11 n3161 n432)
private def n3170 : Certificate := (.color 19 (.witness 39) (.witness 88))
private def n3171 : Certificate := (.color 10 n3170 n3170)
private def n3173 : Certificate := (.color 12 (.witness 72) n3170)
private def n3174 : Certificate := (.color 12 n3170 (.witness 55))
private def n3182 : Certificate := (.color 19 (.witness 7) (.witness 120))
private def n3185 : Certificate := (.color 5 (.color 10 n1454 n3182) (.color 10 n3182 n1455))
private def n3193 : Certificate := (.edge 7 n305 (.edge 8 (.edge 19 n76 (.edge 9 (.edge 18 n105 (.color 8 (.color 9 n243 n2871) (.color 9 n2871 n242))) n836)) n3082))
private def n3196 : Certificate := (.color 4 (.color 9 (.witness 24) n3116) (.color 9 n3116 (.witness 103)))
private def n3201 : Certificate := (.color 8 (.color 12 n1334 n3182) (.color 12 n3182 n1337))
private def n3202 : Certificate := (.edge 18 n105 n3201)
private def n3204 : Certificate := (.edge 10 (.edge 19 n76 (.color 2 n2927 n2927)) n138)
private def n3206 : Certificate := (.color 11 (.witness 19) (.witness 108))
private def n3215 : Certificate := (.edge 10 n76 (.edge 9 (.edge 18 n105 (.edge 7 (.edge 16 n330 n2150) n781)) n138))
private def n3217 : Certificate := (.color 18 (.witness 72) n3170)
private def n3218 : Certificate := (.color 18 n3170 (.witness 55))
private def n3221 : Certificate := (.edge 7 (.edge 9 (.edge 16 n330 n3206) (.color 12 n3217 n3218)) n3082)
private def n3226 : Certificate := (.edge 18 n105 n2871)
private def n3229 : Certificate := (.color 10 (.witness 24) (.witness 103))
private def n3237 : Certificate := (.edge 10 n76 n357)
private def n3240 : Certificate := (.color 5 (.color 10 (.witness 24) n3161) (.color 10 n3161 (.witness 103)))
private def n3248 : Certificate := (.edge 7 (.edge 9 (.edge 16 n330 (.edge 10 (.edge 17 n305 (.color 7 n2944 n2944)) n1347)) n3240) n3089)
private def n3257 : Certificate := (.edge 7 (.edge 17 n305 (.edge 9 (.edge 16 n330 (.color 7 (.color 9 n243 n2871) (.color 9 n2871 n242))) n1469)) n3089)
private def n3259 : Certificate := (.color 9 (.witness 24) n3106)
private def n3260 : Certificate := (.color 9 n3106 (.witness 103))
private def n3267 : Certificate := (.color 7 (.color 11 n1735 (.color 17 (.witness 7) (.witness 120))) (.color 11 (.color 17 (.witness 7) (.witness 120)) n1738))
private def n3269 : Certificate := (.edge 17 n305 n2928)
private def n3276 : Certificate := (.edge 10 (.edge 17 n305 n3201) n1191)
private def n3284 : Certificate := (.edge 20 (.edge 4 (.edge 5 n484 (.edge 16 (.edge 17 n44 (.edge 2 n8 (.edge 9 (.edge 10 n35 n3102) (.edge 18 n3104 n3111)))) (.edge 18 (.edge 19 n129 (.edge 3 n9 (.edge 9 n3120 n3123))) (.edge 10 (.edge 9 n35 (.color 7 n3127 n3128)) n1454)))) (.edge 9 (.edge 10 n35 (.edge 16 (.edge 17 n44 (.edge 7 n330 (.edge 18 n3135 n3139))) (.edge 18 (.edge 19 n129 (.edge 8 n105 n3147)) (.color 2 (.color 3 n637 n2849) (.color 3 n2849 n639))))) (.edge 17 (.edge 16 n44 (.edge 19 (.edge 18 n129 (.edge 5 n3158 n3129)) (.edge 2 (.edge 5 n12 n3162) (.color 7 n3164 n3165)))) (.edge 19 (.edge 18 n129 (.edge 3 (.edge 5 n295 n3171) (.color 8 n3173 n3174))) (.witness 39))))) (.edge 2 (.edge 4 (.edge 16 n8 (.edge 3 (.edge 18 n9 (.edge 5 (.edge 17 n12 n3185) n2871)) (.edge 17 (.edge 5 n12 (.edge 10 n3193 n3196)) (.edge 8 (.edge 9 n3202 n3204) n3206)))) (.edge 5 (.edge 17 n12 (.edge 19 (.edge 3 n295 (.edge 8 n3215 n3221)) n2944)) (.edge 7 (.edge 9 (.edge 16 n330 (.edge 8 n3226 n1299)) (.color 7 (.color 8 n165 n3229) (.color 8 n3229 n164))) n2227))) (.edge 3 (.edge 18 (.edge 4 n9 (.edge 8 (.edge 9 n105 (.edge 19 n3237 n3240)) (.edge 5 (.edge 19 n295 n3248) n1299))) (.edge 19 (.edge 5 n295 (.edge 10 (.edge 8 n76 n3257) (.color 4 n3259 n3260))) (.edge 7 (.edge 9 (.edge 16 n330 n3267) (.edge 10 n3269 n357)) n2845))) (.edge 7 (.edge 9 (.edge 16 n330 (.edge 8 (.edge 18 n105 n3276) n3020)) n3023) n3025))))
private def n3293 : Certificate := (.edge 15 (.edge 3 n5 (.edge 8 n485 (.color 15 (.witness 103) (.witness 24)))) (.witness 24))
private def n3297 : Certificate := (.color 2 (.witness 116) (.witness 11))
private def n3301 : Certificate := (.edge 18 n105 (.color 3 n2227 n2227))
private def n3302 : Certificate := (.color 6 n2227 n2227)
private def n3310 : Certificate := (.color 7 (.witness 116) (.witness 11))
private def n3313 : Certificate := (.color 1 n357 n357)
private def n3322 : Certificate := (.color 11 (.witness 99) (.witness 28))
private def n3328 : Certificate := (.color 16 (.witness 84) (.witness 43))
private def n3330 : Certificate := (.edge 19 (.edge 5 n295 (.edge 10 n76 (.color 1 (.color 6 (.witness 24) n3322) (.color 6 n3322 (.witness 103))))) (.color 11 n3328 n3328))
private def n3332 : Certificate := (.color 1 n3089 n3089)
private def n3335 : Certificate := (.color 19 (.witness 11) (.witness 116))
private def n3343 : Certificate := (.edge 2 (.edge 4 n8 (.edge 5 n12 (.edge 1 n2 (.edge 7 (.edge 9 n330 (.edge 10 n305 (.edge 6 n1102 n3293))) (.edge 15 (.edge 18 n110 (.edge 19 n83 n3297)) (.edge 8 (.edge 9 n3301 n3302) n164)))))) (.edge 7 (.edge 9 n330 (.edge 10 n305 (.edge 6 n1102 (.edge 15 (.edge 18 n110 (.edge 19 n83 n3310)) (.edge 3 (.edge 4 n1481 n3313) (.witness 25)))))) (.edge 15 (.edge 18 n110 (.edge 19 n83 (.witness 11))) (.edge 3 (.edge 18 (.edge 4 n9 (.edge 8 (.edge 9 n105 n3330) n3332)) (.color 3 (.color 8 n577 n3335) (.color 8 n3335 n578))) n3025))))
private def n3346 : Certificate := (.color 18 (.witness 72) (.witness 55))
private def n3353 : Certificate := (.edge 8 (.edge 10 n76 (.color 14 n3170 n3170)) (.color 3 n3217 n3218))
private def n3364 : Certificate := (.edge 8 (.edge 19 n76 (.color 5 n2079 n2079)) (.color 6 n2080 n2081))
private def n3379 : Certificate := (.edge 18 n129 (.edge 3 (.edge 5 n295 (.edge 6 (.edge 14 n1360 (.color 2 (.color 11 (.witness 50) n1750) (.color 11 n1750 (.witness 77)))) n234)) (.color 6 (.witness 72) (.witness 55))))
private def n3381 : Certificate := (.edge 5 n295 n2708)
private def n3383 : Certificate := (.color 16 (.witness 23) (.witness 104))
private def n3387 : Certificate := (.edge 6 (.edge 14 n1360 n3082) (.color 2 (.color 11 n567 n3383) (.color 11 n3383 n570)))
private def n3393 : Certificate := (.edge 14 n1360 (.edge 8 (.edge 18 n105 n3297) (.color 2 (.color 3 n577 n2210) (.color 3 n2210 n578))))
private def n3396 : Certificate := (.color 6 (.witness 88) (.witness 39))
private def n3402 : Certificate := (.edge 5 n295 (.edge 8 (.edge 9 n105 (.color 6 n3322 n3322)) n2708))
private def n3403 : Certificate := (.color 8 n2207 n2207)
private def n3406 : Certificate := (.color 6 n2415 n2415)
private def n3408 : Certificate := (.color 2 n1826 n1826)
private def n3413 : Certificate := (.edge 1 n2 (.edge 7 (.edge 9 n330 (.edge 6 n1102 (.edge 15 (.edge 3 n5 (.edge 8 n485 (.color 15 n3346 n3346))) (.edge 19 (.edge 3 (.edge 5 n295 n3353) (.color 8 n3217 n3218)) n1221)))) (.edge 15 (.edge 18 n110 (.edge 3 n5 (.edge 10 (.edge 6 (.edge 14 n1360 n3364) (.color 8 n2080 n2081)) (.witness 53)))) (.edge 10 (.edge 19 (.edge 8 n76 (.edge 20 (.edge 9 n35 n3379) (.edge 3 n3381 n3387))) (.edge 9 (.edge 20 n35 (.edge 6 n3393 n2946)) n3396)) (.edge 18 (.edge 19 (.edge 20 n129 (.edge 3 n3402 n3403)) n3406) n3408)))))
private def n3416 : Certificate := (.edge 3 n1499 (.color 1 n1500 n1501))
private def n3427 : Certificate := (.color 7 (.color 8 (.witness 72) (.witness 55)) (.color 8 (.witness 72) (.witness 55)))
private def n3429 : Certificate := (.edge 18 n129 (.edge 1 (.edge 14 n11 (.edge 8 (.edge 10 n76 (.color 7 (.color 11 n29 n687) (.color 11 n687 n24))) (.color 1 (.witness 72) (.witness 55)))) n3427))
private def n3431 : Certificate := (.edge 14 n11 n3023)
private def n3434 : Certificate := (.edge 8 (.edge 10 n76 n1234) (.color 7 (.color 11 n567 n3383) (.color 11 n3383 n570)))
private def n3440 : Certificate := (.edge 14 n11 (.edge 3 (.edge 18 n9 n3310) (.color 1 (.color 4 n1218 n1219) (.color 4 n1219 n1221))))
private def n3443 : Certificate := (.color 1 (.witness 88) (.witness 39))
private def n3449 : Certificate := (.edge 4 n9 (.edge 8 (.edge 10 n76 (.color 1 n3322 n3322)) n1007))
private def n3450 : Certificate := (.color 8 (.color 18 n233 n605) (.color 18 n605 n232))
private def n3453 : Certificate := (.color 1 n1395 n1395)
private def n3460 : Certificate := (.edge 9 n330 (.edge 6 n1102 (.edge 15 (.edge 18 n110 (.edge 8 n485 (.edge 5 (.edge 1 (.edge 14 n11 n3416) (.color 3 n1500 n1501)) n232))) (.edge 5 (.edge 19 (.edge 3 n295 (.edge 20 (.edge 4 n484 n3429) (.edge 1 n3431 n3434))) (.edge 4 (.edge 20 n484 (.edge 1 n3440 n2928)) n3443)) (.edge 18 (.edge 19 (.edge 20 n129 (.edge 3 n3449 n3450)) n3453) (.color 7 n745 n745))))))
private def n3461 : Certificate := (.color 18 (.witness 75) (.witness 52))
private def n3465 : Certificate := (.edge 10 n76 (.color 9 (.color 16 (.witness 20) n3461) (.color 16 n3461 (.witness 107))))
private def n3469 : Certificate := (.edge 6 (.edge 10 (.edge 14 n1360 n166) (.color 3 n3461 n3461)) n1086)
private def n3476 : Certificate := (.edge 1 (.edge 5 (.edge 14 n11 n1565) (.color 8 n3461 n3461)) n2351)
private def n3480 : Certificate := (.edge 5 n11 (.color 10 n2913 n2913))
private def n3483 : Certificate := (.color 6 (.color 11 n567 n2913) (.color 11 n2913 n570))
private def n3496 : Certificate := (.edge 1 n11 (.edge 6 (.edge 10 n1360 (.edge 8 (.edge 9 n105 n2351) n1695)) (.edge 8 (.edge 9 n105 n2927) (.color 11 n567 n570))))
private def n3506 : Certificate := (.edge 14 (.edge 6 n1360 (.edge 1 (.edge 5 n11 n1086) n2944)) n3332)
private def n3514 : Certificate := (.edge 6 (.edge 10 n1360 (.color 3 (.color 8 (.witness 36) n3461) (.color 8 n3461 (.witness 91)))) n3443)
private def n3517 : Certificate := (.color 11 (.witness 35) (.witness 92))
private def n3532 : Certificate := (.edge 8 n76 (.edge 20 (.edge 4 n484 (.color 9 (.witness 72) (.witness 55))) (.color 11 (.color 15 n567 n3383) (.color 15 n3383 n570))))
private def n3534 : Certificate := (.color 15 (.witness 39) (.witness 88))
private def n3537 : Certificate := (.edge 4 n484 (.edge 9 n35 (.color 11 n3534 n3534)))
private def n3541 : Certificate := (.color 5 (.witness 52) (.witness 75))
private def n3544 : Certificate := (.color 3 (.color 4 n267 n3541) (.color 4 n3541 n270))
private def n3551 : Certificate := (.edge 4 n484 (.edge 9 n35 (.color 1 (.color 6 (.witness 72) n2855) (.color 6 n2855 (.witness 55)))))
private def n3552 : Certificate := (.color 15 (.witness 100) (.witness 27))
private def n3553 : Certificate := (.color 11 n3552 n3552)
private def n3559 : Certificate := (.color 20 (.witness 11) (.witness 116))
private def n3569 : Certificate := (.color 8 (.color 9 n233 (.color 10 (.witness 52) (.witness 75))) (.color 9 (.color 10 (.witness 52) (.witness 75)) n232))
private def n3573 : Certificate := (.edge 18 (.edge 15 n110 (.edge 19 (.edge 20 n129 (.edge 3 (.edge 5 n295 (.edge 4 n9 (.edge 8 n3465 n3469))) (.edge 8 (.edge 10 n76 (.edge 9 n105 n3476)) (.edge 14 (.edge 1 n3480 n3483) n578)))) (.edge 4 (.edge 3 n9 (.edge 5 (.edge 20 n484 (.edge 14 n3496 n3025)) (.edge 9 (.edge 8 n105 n2887) n1585))) (.edge 9 (.edge 8 n105 (.edge 10 (.edge 20 n35 n3506) n193)) (.edge 14 (.edge 1 (.edge 5 n11 n3514) n3396) (.color 1 (.color 6 n1218 n3517) (.color 6 n3517 n1221))))))) (.edge 5 (.edge 14 (.edge 1 n11 (.edge 10 (.edge 6 n1360 (.edge 19 (.edge 3 n295 n3532) (.edge 20 n3537 n2845))) n3544)) (.edge 19 (.edge 3 n295 (.edge 10 (.edge 8 n76 (.edge 20 n3551 n3553)) (.color 1 (.color 4 n267 n3541) (.color 4 n3541 n270)))) (.color 5 (.color 10 (.witness 52) n3559) (.color 10 n3559 (.witness 75))))) (.edge 10 (.edge 6 (.edge 14 n1360 (.color 10 (.witness 52) (.witness 75))) n3569) (.witness 52))))
private def n3579 : Certificate := (.color 18 (.witness 75) (.color 20 (.witness 20) (.witness 107)))
private def n3580 : Certificate := (.color 18 (.color 20 (.witness 20) (.witness 107)) (.witness 52))
private def n3584 : Certificate := (.color 9 n3461 n3461)
private def n3587 : Certificate := (.edge 9 n105 (.color 4 n3461 n3461))
private def n3588 : Certificate := (.color 15 n3461 n3461)
private def n3598 : Certificate := (.edge 9 (.edge 18 n105 (.color 3 n777 n777)) (.color 7 n777 n777))
private def n3609 : Certificate := (.edge 20 n129 (.edge 3 (.edge 4 n9 (.color 7 (.witness 20) (.witness 107))) (.edge 7 (.edge 15 n485 (.color 1 (.color 11 n590 n1026) (.color 11 n1026 n591))) n148)))
private def n3612 : Certificate := (.color 14 (.witness 43) (.witness 84))
private def n3617 : Certificate := (.edge 4 n9 (.edge 7 (.edge 15 n485 n3443) (.color 1 (.color 11 n429 n3612) (.color 11 n3612 n432))))
private def n3621 : Certificate := (.edge 20 n35 n3015)
private def n3623 : Certificate := (.edge 15 n485 (.edge 9 n3621 n3453))
private def n3626 : Certificate := (.color 7 (.witness 52) (.witness 75))
private def n3630 : Certificate := (.edge 4 n9 (.color 9 (.color 18 n233 n468) (.color 18 n468 n232)))
private def n3632 : Certificate := (.edge 9 (.edge 10 n35 (.color 1 n2931 n2931)) n1416)
private def n3635 : Certificate := (.color 1 (.color 3 n1334 n1420) (.color 3 n1420 n1337))
private def n3642 : Certificate := (.edge 2 n2 (.edge 6 (.edge 10 n1360 (.edge 7 n1102 (.edge 13 (.edge 4 n7 (.edge 9 (.triangle 17) (.color 13 n3579 n3580))) (.edge 18 (.edge 3 (.edge 4 n9 n3584) (.edge 8 n3587 n3588)) (.witness 52))))) (.edge 13 (.edge 20 (.triangle 30) (.edge 4 n7 (.edge 8 (.edge 7 (.edge 15 n485 n3598) n777) (.witness 22)))) (.edge 8 (.edge 18 (.edge 9 n105 (.edge 19 (.edge 10 n76 n3609) (.edge 3 n3617 n1416))) (.edge 10 (.edge 19 n76 (.edge 7 n3623 n3569)) n3626)) (.edge 18 (.edge 20 (.edge 19 n129 (.edge 3 n3630 n3632)) (.color 1 (.color 3 n1334 n1420) (.color 3 n1420 n1337))) (.color 7 n749 n749))))))
private def n3646 : Certificate := (.edge 4 (.edge 18 n9 n1704) (.color 2 n1704 n1704))
private def n3661 : Certificate := (.edge 20 n129 (.edge 2 (.edge 15 n5 (.edge 8 (.edge 9 n105 (.color 2 (.witness 20) (.witness 107))) n2708)) (.color 6 (.color 8 (.witness 105) (.color 9 (.witness 20) (.witness 107))) (.color 8 (.color 9 (.witness 20) (.witness 107)) (.witness 22)))))
private def n3663 : Certificate := (.edge 15 n5 n3406)
private def n3666 : Certificate := (.edge 8 (.edge 9 n105 (.color 6 (.color 11 n429 n3612) (.color 11 n3612 n432))) n1830)
private def n3672 : Certificate := (.edge 15 n5 (.edge 4 (.edge 20 n484 n2799) n3408))
private def n3675 : Certificate := (.color 2 (.witness 52) (.witness 75))
private def n3683 : Certificate := (.edge 5 n484 (.edge 8 (.edge 9 n105 (.color 6 (.color 11 n79 n2757) (.color 11 n2757 n78))) (.color 6 n2931 n2931)))
private def n3686 : Certificate := (.color 6 (.color 8 n1334 n2135) (.color 8 n2135 n1337))
private def n3694 : Certificate := (.edge 10 n1360 (.edge 7 n1102 (.edge 13 (.edge 20 n36 (.edge 9 n1247 (.edge 3 (.edge 2 (.edge 15 n5 n3646) n1704) (.witness 21)))) (.edge 3 (.edge 18 (.edge 4 n9 (.edge 19 (.edge 5 n295 n3661) (.edge 2 n3663 n3666))) (.edge 5 (.edge 19 n295 (.edge 2 n3672 n3544)) n3675)) (.edge 18 (.edge 20 (.edge 19 n129 (.edge 4 n3683 n2412)) (.color 6 (.color 8 n1334 n2135) (.color 8 n2135 n1337))) (.color 2 (.color 4 (.witness 74) (.witness 53)) (.color 4 (.witness 74) (.witness 53))))))))
private def n3695 : Certificate := (.color 20 (.witness 23) (.witness 104))
private def n3699 : Certificate := (.edge 8 n105 (.color 10 (.color 14 n182 n3695) (.color 14 n3695 n185)))
private def n3701 : Certificate := (.color 18 (.witness 72) n3695)
private def n3702 : Certificate := (.color 18 n3695 (.witness 55))
private def n3705 : Certificate := (.edge 7 (.edge 8 (.edge 15 n485 n2505) (.color 4 n3701 n3702)) n836)
private def n3712 : Certificate := (.edge 2 (.edge 3 (.edge 15 n5 (.color 7 (.witness 37) (.witness 90))) (.color 9 n3701 n3702)) n1347)
private def n3716 : Certificate := (.edge 3 n5 (.color 8 n3534 n3534))
private def n3719 : Certificate := (.color 7 (.color 11 n429 n3534) (.color 11 n3534 n432))
private def n3733 : Certificate := (.edge 2 n5 (.edge 7 (.edge 8 n485 (.edge 9 (.edge 10 n35 n1347) (.color 3 (.witness 72) (.witness 55)))) (.edge 9 (.edge 10 n35 n1826) (.color 11 n429 n432))))
private def n3746 : Certificate := (.edge 15 (.edge 7 n485 (.edge 2 (.edge 3 n5 n836) n745)) (.color 2 (.color 3 (.witness 38) n2927) (.color 3 n2927 (.witness 89))))
private def n3754 : Certificate := (.edge 7 (.edge 8 n485 (.color 4 (.color 9 (.witness 72) n3695) (.color 9 n3695 (.witness 55)))) n3675)
private def n3764 : Certificate := (.color 13 n429 n3612)
private def n3765 : Certificate := (.color 13 n3612 n432)
private def n3768 : Certificate := (.edge 9 n105 (.edge 19 (.edge 5 n295 n777) (.color 11 n3764 n3765)))
private def n3770 : Certificate := (.color 13 (.witness 75) (.witness 52))
private def n3773 : Certificate := (.edge 5 n295 (.edge 10 n76 (.color 11 n3770 n3770)))
private def n3777 : Certificate := (.color 3 (.witness 104) (.witness 23))
private def n3781 : Certificate := (.edge 5 n295 (.edge 10 n76 n3322))
private def n3782 : Certificate := (.color 13 (.witness 88) (.witness 39))
private def n3783 : Certificate := (.color 11 n3782 n3782)
private def n3786 : Certificate := (.color 2 n3777 n3777)
private def n3794 : Certificate := (.color 8 (.witness 104) (.witness 23))
private def n3799 : Certificate := (.edge 20 (.edge 13 n36 (.edge 18 (.edge 19 n129 (.edge 4 (.edge 3 n9 (.edge 5 n484 (.edge 9 n3699 n3705))) (.edge 9 (.edge 8 n105 (.edge 10 n35 n3712)) (.edge 15 (.edge 2 n3716 n3719) (.witness 39))))) (.edge 5 (.edge 4 n484 (.edge 3 (.edge 19 n295 (.edge 15 n3733 n2944)) (.edge 10 (.edge 9 n35 n3427) n1213))) (.edge 10 (.edge 9 n35 (.edge 8 (.edge 19 n76 n3746) n234)) (.edge 15 (.edge 2 (.edge 3 n5 n3754) n3626) (.color 11 n261 n260)))))) (.edge 3 (.edge 15 (.edge 2 n5 (.edge 8 (.edge 7 n485 (.edge 18 (.edge 4 n9 n3768) (.edge 19 n3773 n2845))) n3777)) (.edge 18 (.edge 4 n9 (.edge 8 (.edge 9 n105 (.edge 19 n3781 n3783)) n3786)) (.color 3 (.color 8 n1334 n3182) (.color 8 n3182 n1337)))) (.edge 8 (.edge 7 (.edge 15 n485 n3794) n3794) n1337)))
private def n3808 : Certificate := (.edge 13 n1247 (.edge 8 (.edge 18 n105 (.edge 10 (.edge 20 n35 n3297) n3408)) n3071))
private def n3809 : Certificate := (.color 2 n440 n441)
private def n3814 : Certificate := (.color 9 (.color 13 n1218 n2865) (.color 13 n2865 n1221))
private def n3815 : Certificate := (.edge 18 n105 n3814)
private def n3817 : Certificate := (.edge 10 (.edge 20 n35 n3786) n183)
private def n3824 : Certificate := (.edge 13 n1247 (.color 9 n2034 n2035))
private def n3827 : Certificate := (.edge 10 n35 (.color 3 n3116 n3116))
private def n3830 : Certificate := (.edge 7 (.edge 10 (.edge 17 n305 n1962) (.color 3 n3116 n3116)) n1081)
private def n3837 : Certificate := (.edge 17 n305 (.edge 19 (.edge 8 n76 (.edge 20 n129 n1962)) n3517))
private def n3838 : Certificate := (.color 13 n3116 n3116)
private def n3845 : Certificate := (.edge 8 (.edge 10 n76 (.color 6 n3322 n3322)) (.color 6 (.color 11 n38 n1983) (.color 11 n1983 n37)))
private def n3853 : Certificate := (.edge 20 n35 (.edge 8 (.edge 19 n76 n3297) n3079))
private def n3854 : Certificate := (.color 6 (.witness 56) (.witness 71))
private def n3863 : Certificate := (.edge 15 n5 (.edge 5 (.edge 19 n295 (.edge 17 n12 (.edge 4 (.edge 18 n9 (.edge 20 n484 n2799)) (.edge 6 (.edge 7 n1102 (.edge 9 n3808 n3809)) (.edge 9 (.edge 8 n3815 n3817) n3517))))) (.edge 18 (.edge 4 n9 (.edge 9 (.edge 8 n105 (.edge 6 (.edge 7 n1102 n3824) (.edge 20 n3827 n3830))) (.edge 7 (.edge 6 n1102 (.edge 10 n3837 n3838)) (.edge 19 (.edge 20 n129 n3845) n3809)))) (.edge 6 (.edge 7 n1102 (.edge 9 (.edge 13 n1247 (.edge 10 n3853 n3854)) (.color 6 n2591 n2591))) (.edge 10 (.edge 7 (.edge 17 n305 n2871) (.color 8 (.color 9 n243 n2871) (.color 9 n2871 n242))) n1454)))))
private def n3865 : Certificate := (.color 18 n1455 (.color 19 n182 n185))
private def n3866 : Certificate := (.color 18 (.color 19 n182 n185) n1454)
private def n3873 : Certificate := (.edge 20 n35 n3794)
private def n3878 : Certificate := (.edge 20 (.edge 18 n129 n2862) (.color 7 (.witness 21) (.witness 106)))
private def n3880 : Certificate := (.color 7 n3794 n3794)
private def n3882 : Certificate := (.edge 5 (.edge 20 n484 n3880) n1185)
private def n3887 : Certificate := (.color 19 n182 n3695)
private def n3888 : Certificate := (.color 19 n3695 n185)
private def n3891 : Certificate := (.color 5 n3887 n3888)
private def n3903 : Certificate := (.edge 8 n105 (.edge 19 n129 (.edge 6 (.edge 13 n1247 n2193) n183)))
private def n3907 : Certificate := (.edge 8 (.edge 10 n76 n2396) (.color 6 n2855 n2855))
private def n3913 : Certificate := (.edge 13 n1247 (.edge 10 (.edge 19 n76 n3297) (.color 2 (.color 4 n267 n270) (.color 4 n267 n270))))
private def n3916 : Certificate := (.color 10 (.witness 21) (.witness 106))
private def n3919 : Certificate := (.color 6 (.color 8 n1334 n3916) (.color 8 n3916 n1337))
private def n3921 : Certificate := (.color 6 (.witness 104) (.witness 23))
private def n3925 : Certificate := (.color 4 n2087 n2087)
private def n3931 : Certificate := (.edge 15 (.edge 17 (.edge 19 n83 (.color 6 (.color 8 n182 n2087) (.color 8 n2087 n185))) n3675) n3854)
private def n3933 : Certificate := (.color 15 (.witness 71) (.witness 56))
private def n3941 : Certificate := (.edge 6 (.edge 13 n1247 (.edge 15 (.edge 17 n83 n3675) n3854)) n3933)
private def n3948 : Certificate := (.edge 17 (.edge 19 n83 (.color 6 n2087 n2087)) n3921)
private def n3951 : Certificate := (.color 17 (.witness 23) (.witness 104))
private def n3958 : Certificate := (.edge 7 (.edge 6 n1102 (.edge 17 (.edge 10 n305 (.edge 5 n12 (.edge 15 (.edge 8 n485 (.color 15 n3865 n3866)) (.color 8 n3116 n3116)))) (.edge 8 (.edge 15 n485 (.edge 9 (.edge 18 n105 (.edge 10 n3873 n2862)) (.edge 19 (.edge 10 n76 n3878) (.edge 4 n3882 n3517)))) (.edge 20 (.edge 4 (.edge 5 n484 (.color 10 n3887 n3888)) (.edge 9 (.edge 10 n35 n3891) (.color 13 n3701 n3702))) n1337)))) (.edge 5 (.edge 17 n12 (.edge 20 (.edge 4 n484 (.edge 9 (.edge 10 n35 (.edge 18 n3903 n2396)) (.edge 19 (.edge 18 n129 n3907) n3809))) (.edge 8 (.edge 9 (.edge 18 n105 (.edge 6 n3913 n3794)) (.color 6 (.color 8 n1334 n3916) (.color 8 n3916 n1337))) n3921))) (.edge 9 (.edge 8 (.edge 18 n105 (.edge 10 (.edge 19 n76 (.edge 20 n35 n3925)) (.edge 6 (.edge 13 n1247 n3931) (.color 8 n3933 n3933)))) (.edge 20 (.edge 10 n35 (.edge 19 (.edge 18 n129 n3941) (.color 6 n182 n185))) (.edge 6 (.edge 13 n1247 (.edge 15 n3948 n3082)) (.color 10 n3951 n3951)))) (.edge 19 (.edge 8 (.edge 10 n76 (.color 17 n2776 n2776)) (.color 15 (.color 18 n243 n2776) (.color 18 n2776 n242))) (.witness 42)))))
private def n3966 : Certificate := (.edge 13 n7 (.edge 3 (.edge 18 n9 (.edge 5 (.edge 20 n484 n3310) n3453)) (.color 1 (.color 4 n1218 n1219) (.color 4 n1219 n1221))))
private def n3967 : Certificate := (.color 4 (.color 13 n1218 n2865) (.color 13 n2865 n1221))
private def n3969 : Certificate := (.edge 3 (.edge 18 n9 n3967) n3882)
private def n3971 : Certificate := (.color 7 (.witness 84) (.witness 43))
private def n3979 : Certificate := (.edge 5 n484 (.edge 19 n129 (.edge 1 (.edge 13 n7 (.color 7 (.color 11 n79 n583) (.color 11 n583 n78))) n1185)))
private def n3983 : Certificate := (.edge 3 (.edge 5 n295 (.color 1 n3322 n3322)) n1022)
private def n3990 : Certificate := (.edge 13 n7 (.edge 3 (.edge 19 n295 n3310) n2992))
private def n3993 : Certificate := (.color 1 (.witness 56) (.witness 71))
private def n4003 : Certificate := (.edge 3 n9 (.edge 19 n129 (.edge 1 (.edge 13 n7 n1416) n1185)))
private def n4006 : Certificate := (.color 1 (.color 11 (.witness 50) n417) (.color 11 n417 (.witness 77)))
private def n4010 : Certificate := (.edge 3 (.edge 5 n295 n4006) (.color 1 n2855 n2855))
private def n4016 : Certificate := (.edge 13 n7 (.edge 5 (.edge 19 n295 n3310) n3635))
private def n4021 : Certificate := (.color 1 (.witness 104) (.witness 23))
private def n4032 : Certificate := (.edge 15 (.edge 17 (.edge 19 n83 (.color 1 (.color 3 n182 n507) (.color 3 n507 n185))) n3626) n3993)
private def n4041 : Certificate := (.edge 1 (.edge 13 n7 (.edge 15 (.edge 17 n83 n3626) n3993)) n3933)
private def n4048 : Certificate := (.edge 17 (.edge 19 n83 (.color 1 n507 n507)) n4021)
private def n4060 : Certificate := (.edge 8 (.edge 15 n485 (.edge 10 (.edge 19 n76 (.edge 17 n305 (.edge 9 (.edge 18 n105 n3621) (.edge 4 (.edge 1 n3966 n3969) n3971)))) (.edge 18 (.edge 9 n105 (.edge 4 (.edge 3 n9 (.edge 20 n3979 n1022)) (.edge 19 (.edge 20 n129 n3983) n3971))) (.edge 4 (.edge 5 (.edge 20 n484 (.edge 1 n3990 n2852)) n3993) (.color 1 n1309 n1309))))) (.edge 10 (.edge 17 n305 (.edge 20 (.edge 9 n35 (.edge 4 (.edge 5 n484 (.edge 18 n4003 n4006)) (.edge 19 (.edge 18 n129 n4010) n3971))) (.edge 3 (.edge 4 (.edge 18 n9 (.edge 1 n4016 n3777)) (.color 1 (.color 3 n1334 n1335) (.color 3 n1335 n1337))) n4021))) (.edge 4 (.edge 3 (.edge 18 n9 (.edge 5 (.edge 19 n295 (.edge 20 n484 n507)) (.edge 1 (.edge 13 n7 n4032) (.color 3 n3933 n3933)))) (.edge 20 (.edge 5 n484 (.edge 19 (.edge 18 n129 n4041) (.color 1 n182 n185))) (.edge 1 (.edge 13 n7 (.edge 15 n4048 n3020)) (.color 5 n3951 n3951)))) (.edge 19 (.edge 3 (.edge 5 n295 (.color 17 n464 n464)) (.color 15 n669 n670)) (.witness 41)))))
private def n4062 : Certificate := (.color 19 (.witness 43) (.witness 84))
private def n4063 : Certificate := (.color 17 (.witness 20) n4062)
private def n4064 : Certificate := (.color 17 n4062 (.witness 107))
private def n4072 : Certificate := (.edge 9 (.edge 13 n1247 n166) (.color 3 (.color 18 (.witness 68) n4062) (.color 18 n4062 (.witness 59))))
private def n4081 : Certificate := (.edge 4 (.edge 13 n7 n1565) (.color 8 (.color 18 (.witness 68) n4062) (.color 18 n4062 (.witness 59))))
private def n4089 : Certificate := (.edge 4 n7 (.edge 6 (.edge 9 n1247 (.color 15 (.color 18 (.witness 68) n4062) (.color 18 n4062 (.witness 59)))) n4021))
private def n4091 : Certificate := (.color 6 n1334 n3206)
private def n4092 : Certificate := (.color 6 n3206 n1337)
private def n4096 : Certificate := (.color 9 n2834 n2834)
private def n4097 : Certificate := (.edge 4 n7 n4096)
private def n4098 : Certificate := (.color 11 n567 n2834)
private def n4099 : Certificate := (.color 11 n2834 n570)
private def n4116 : Certificate := (.edge 9 n1247 (.edge 8 (.edge 10 n76 (.color 11 (.color 15 n590 (.color 17 (.witness 21) (.witness 106))) (.color 15 (.color 17 (.witness 21) (.witness 106)) n591))) (.edge 15 (.edge 17 n83 n3921) (.color 4 (.witness 68) (.witness 59)))))
private def n4123 : Certificate := (.edge 8 (.edge 10 n76 (.edge 15 (.edge 17 n83 n3794) n1191)) (.color 11 (.color 15 n567 n3951) (.color 15 n3951 n570)))
private def n4128 : Certificate := (.color 8 (.color 15 n577 n3335) (.color 15 n3335 n578))
private def n4134 : Certificate := (.edge 6 (.edge 13 n1247 n3553) (.edge 15 (.edge 17 n83 n4021) n2807))
private def n4136 : Certificate := (.color 15 (.witness 68) (.witness 59))
private def n4144 : Certificate := (.edge 9 (.edge 13 n1247 n632) (.color 8 (.color 15 (.witness 68) n4062) (.color 15 n4062 (.witness 59))))
private def n4154 : Certificate := (.edge 1 (.edge 4 n7 (.color 11 n447 n448)) (.edge 15 (.edge 17 n83 n3777) n2071))
private def n4156 : Certificate := (.color 3 (.color 15 n577 n3335) (.color 15 n3335 n578))
private def n4161 : Certificate := (.edge 4 (.edge 13 n7 n1710) (.color 3 (.color 15 (.witness 68) n4062) (.color 15 n4062 (.witness 59))))
private def n4167 : Certificate := (.color 9 n3770 n3770)
private def n4169 : Certificate := (.color 11 n386 n3770)
private def n4170 : Certificate := (.color 11 n3770 n389)
private def n4178 : Certificate := (.edge 9 n1247 (.color 3 (.color 8 (.witness 68) n4062) (.color 8 n4062 (.witness 59))))
private def n4189 : Certificate := (.edge 18 (.edge 20 n129 (.edge 3 (.edge 4 n9 (.edge 5 n295 (.edge 8 (.edge 9 n105 (.color 10 n4063 n4064)) (.edge 15 (.edge 17 n83 n1557) (.edge 6 n4072 n1086))))) (.edge 8 (.edge 9 n105 (.edge 10 n76 (.edge 15 (.edge 17 n83 n148) (.edge 1 n4081 n2351)))) (.edge 15 (.edge 17 n83 (.edge 13 (.edge 1 n4089 n3921) (.color 1 n4091 n4092))) (.edge 13 (.edge 1 (.edge 4 n7 n4096) (.color 6 n4098 n4099)) (.witness 27)))))) (.edge 5 (.edge 3 n295 (.edge 4 (.edge 20 n484 (.edge 13 (.edge 1 n7 (.edge 6 n4116 n4123)) (.color 8 (.color 15 n577 n3335) (.color 15 n3335 n578)))) (.edge 10 (.edge 8 n76 (.edge 9 (.edge 20 n35 n4134) (.color 11 n4136 n4136))) (.edge 15 (.edge 17 n83 (.edge 6 n4144 n782)) n1618)))) (.edge 10 (.edge 8 n76 (.edge 9 (.edge 20 n35 (.edge 13 (.edge 6 n1247 n4154) n4156)) (.edge 15 (.edge 17 n83 (.edge 1 n4161 n1872)) n244))) (.edge 15 (.edge 17 n83 (.edge 13 (.edge 1 (.edge 4 n7 n4167) (.color 6 n4169 n4170)) (.witness 52))) (.edge 13 (.edge 1 (.edge 4 n7 (.edge 6 n4178 n3993)) n3854) (.color 1 (.color 6 (.witness 56) (.color 11 n261 n260)) (.color 6 (.color 11 n261 n260) (.witness 71))))))))
private def n4191 : Certificate := (.edge 20 (.edge 5 n484 n2087) (.color 11 (.color 15 n567 n3951) (.color 15 n3951 n570)))
private def n4195 : Certificate := (.edge 10 n35 (.color 11 n3933 n3933))
private def n4200 : Certificate := (.color 4 (.witness 84) (.witness 43))
private def n4207 : Certificate := (.edge 10 n35 (.color 1 (.color 6 n182 n2931) (.color 6 n2931 n185)))
private def n4219 : Certificate := (.color 9 (.witness 84) (.witness 43))
private def n4224 : Certificate := (.edge 4 (.edge 13 (.edge 1 n7 (.edge 9 (.edge 6 n1247 (.edge 18 (.edge 3 n9 (.edge 8 n105 n4191)) (.edge 20 (.edge 5 n484 n4195) n2845))) (.color 3 n4200 n4200))) (.edge 18 (.edge 3 n9 (.edge 9 (.edge 8 n105 (.edge 20 (.edge 5 n484 n4207) (.color 11 n3552 n3552))) (.color 1 n4200 n4200))) (.color 4 (.color 9 (.witness 84) n3559) (.color 9 n3559 (.witness 43))))) (.edge 9 (.edge 6 (.edge 13 n1247 n4219) (.color 8 n4219 n4219)) (.witness 43)))
private def n4233 : Certificate := (.edge 15 (.edge 2 n5 (.edge 7 n485 (.color 15 (.witness 103) (.witness 24)))) (.witness 24))
private def n4237 : Certificate := (.color 2 (.witness 18) (.witness 109))
private def n4241 : Certificate := (.edge 16 n330 (.color 2 n1299 n1299))
private def n4242 : Certificate := (.color 6 n1299 n1299)
private def n4250 : Certificate := (.color 6 (.color 7 (.witness 20) (.witness 107)) (.color 7 (.witness 20) (.witness 107)))
private def n4254 : Certificate := (.edge 13 n1247 (.color 1 n1557 n1557))
private def n4263 : Certificate := (.color 3 (.witness 108) (.witness 19))
private def n4273 : Certificate := (.edge 10 (.edge 14 n1360 (.edge 17 n305 (.color 1 (.color 2 (.witness 18) n4263) (.color 2 n4263 (.witness 109))))) (.color 6 (.color 7 n38 (.color 9 n152 n153)) (.color 7 (.color 9 n152 n153) n37)))
private def n4277 : Certificate := (.color 10 n152 n153)
private def n4285 : Certificate := (.edge 12 (.edge 13 n106 (.edge 14 n77 (.edge 1 n4 (.edge 8 (.edge 9 n105 (.edge 10 n76 (.edge 6 n1103 n4233))) (.edge 15 (.edge 16 n110 (.edge 17 n83 n4237)) (.edge 7 (.edge 9 n4241 n4242) (.witness 26))))))) (.edge 15 (.edge 16 n110 (.edge 17 n83 (.edge 2 n5 (.edge 8 (.edge 9 n105 (.edge 10 n76 n4250)) (.edge 6 (.edge 9 n4254 n1557) (.witness 22)))))) (.edge 8 (.edge 9 n105 (.edge 10 n76 (.witness 28))) (.edge 6 (.edge 9 (.edge 13 n1247 (.edge 7 (.edge 16 n330 n4273) n1989)) (.color 6 (.color 7 n38 (.color 10 n152 n153)) (.color 7 (.color 10 n152 n153) n37))) n413))))
private def n4288 : Certificate := (.color 7 (.witness 17) (.witness 110))
private def n4291 : Certificate := (.edge 16 n8 n138)
private def n4292 : Certificate := (.color 1 n138 n138)
private def n4299 : Certificate := (.edge 13 n7 n148)
private def n4305 : Certificate := (.color 8 (.witness 108) (.witness 19))
private def n4311 : Certificate := (.color 4 (.witness 28) (.witness 99))
private def n4315 : Certificate := (.edge 5 (.edge 14 n11 (.edge 17 n12 (.color 6 (.color 7 (.witness 17) n4305) (.color 7 n4305 (.witness 110))))) (.color 1 (.color 2 n590 n4311) (.color 2 n4311 n591)))
private def n4319 : Certificate := (.color 5 (.witness 28) (.witness 99))
private def n4327 : Certificate := (.edge 10 n76 (.edge 12 (.edge 13 n106 (.edge 14 n77 (.edge 6 n1103 (.edge 15 (.edge 16 n110 (.edge 17 n83 n4288)) (.edge 2 (.edge 4 n4291 n4292) (.witness 25)))))) (.edge 15 (.edge 16 n110 (.edge 17 n83 (.edge 7 n485 (.edge 1 (.edge 4 n4299 n148) (.witness 21))))) (.edge 1 (.edge 4 (.edge 13 n7 (.edge 2 (.edge 16 n8 n4315) n592)) (.color 1 (.color 2 n590 n4319) (.color 2 n4319 n591))) n2763))))
private def n4331 : Certificate := (.color 12 (.witness 99) (.witness 28))
private def n4341 : Certificate := (.edge 17 (.edge 5 n12 (.edge 10 n305 (.color 1 (.color 6 (.witness 24) n4331) (.color 6 n4331 (.witness 103))))) (.color 2 (.color 7 n577 (.color 16 (.witness 19) (.witness 108))) (.color 7 (.color 16 (.witness 19) (.witness 108)) n578)))
private def n4346 : Certificate := (.color 17 (.witness 19) (.witness 108))
private def n4349 : Certificate := (.color 2 (.color 7 n577 n4346) (.color 7 n4346 n578))
private def n4354 : Certificate := (.edge 13 n106 (.edge 14 n77 (.edge 15 (.edge 16 n110 (.edge 17 n83 (.witness 19))) (.edge 2 (.edge 16 (.edge 4 n8 (.edge 7 (.edge 9 n330 n4341) (.color 1 n3082 n3082))) (.color 2 (.color 7 n577 n4346) (.color 7 n4346 n578))) n3020))))
private def n4355 : Certificate := (.color 15 (.witness 99) (.witness 28))
private def n4365 : Certificate := (.edge 14 (.edge 5 n11 (.edge 10 n1360 (.color 2 (.color 7 (.witness 20) n4355) (.color 7 n4355 (.witness 107))))) (.color 1 (.color 6 n1334 (.color 13 (.witness 19) (.witness 108))) (.color 6 (.color 13 (.witness 19) (.witness 108)) n1337)))
private def n4369 : Certificate := (.color 14 (.witness 19) (.witness 108))
private def n4382 : Certificate := (.edge 6 (.edge 14 n1360 n4349) (.edge 7 (.edge 17 n305 n4021) (.color 1 (.color 2 n567 n568) (.color 2 n568 n570))))
private def n4383 : Certificate := (.color 18 n261 n260)
private def n4392 : Certificate := (.edge 6 n1360 (.edge 7 (.edge 17 n305 (.edge 9 (.edge 16 n330 n4021) n421)) (.color 1 n567 n570)))
private def n4398 : Certificate := (.edge 7 (.edge 9 (.edge 16 n330 n4383) n592) (.color 1 (.color 6 n567 n2913) (.color 6 n2913 n570)))
private def n4404 : Certificate := (.color 6 n3020 n3020)
private def n4409 : Certificate := (.edge 10 n305 (.edge 9 (.edge 16 n330 (.edge 6 (.edge 13 n1247 n4404) n702)) n592))
private def n4412 : Certificate := (.color 1 (.color 6 n567 n2834) (.color 6 n2834 n570))
private def n4415 : Certificate := (.edge 13 n1247 (.color 2 (.color 7 n577 (.color 16 (.witness 19) (.witness 108))) (.color 7 (.color 16 (.witness 19) (.witness 108)) n578)))
private def n4417 : Certificate := (.edge 7 (.edge 16 n330 n4021) (.color 1 (.color 2 n567 n676) (.color 2 n676 n570)))
private def n4419 : Certificate := (.color 18 (.witness 76) (.witness 51))
private def n4424 : Certificate := (.edge 16 n330 (.edge 10 (.edge 14 n1360 n4349) (.color 6 (.color 7 n38 (.color 9 n152 n153)) (.color 7 (.color 9 n152 n153) n37))))
private def n4431 : Certificate := (.edge 10 n305 n2763)
private def n4437 : Certificate := (.edge 6 (.edge 10 (.edge 14 n1360 n4419) n2763) (.color 2 (.color 7 n567 n3383) (.color 7 n3383 n570)))
private def n4444 : Certificate := (.edge 6 (.edge 9 (.edge 13 n1247 (.edge 10 (.edge 14 n1360 n3082) n2207)) (.edge 10 (.edge 14 n1360 n4419) n2763)) (.color 2 n567 n570))
private def n4452 : Certificate := (.edge 6 (.edge 14 n1360 (.edge 9 (.edge 13 n1247 n3082) n1996)) (.color 2 n567 n570))
private def n4455 : Certificate := (.edge 9 (.edge 13 n1247 n4383) n2763)
private def n4458 : Certificate := (.color 2 (.color 7 n567 n3951) (.color 7 n3951 n570))
private def n4466 : Certificate := (.edge 10 (.edge 14 n1360 n3020) (.color 6 (.color 7 n567 n1316) (.color 7 n1316 n570)))
private def n4477 : Certificate := (.edge 15 (.edge 16 n110 (.edge 17 n83 (.edge 1 (.edge 13 (.edge 4 n7 (.edge 6 (.edge 9 n1247 n4365) n4021)) (.color 1 (.color 6 n1334 n4369) (.color 6 n4369 n1337))) n3921))) (.edge 1 (.edge 4 (.edge 13 n7 (.edge 2 (.edge 16 n8 (.edge 5 (.edge 14 n11 n4349) (.edge 10 n4382 n4383))) (.edge 14 (.edge 5 n11 (.edge 10 n4392 n4398)) n3020))) (.edge 5 (.edge 14 n11 (.edge 17 (.edge 2 n12 (.edge 7 n4409 n4412)) (.edge 9 (.edge 6 n4415 n4417) n4419))) (.edge 6 (.edge 9 (.edge 13 n1247 (.edge 7 n4424 n1989)) (.color 6 (.color 7 n38 n4277) (.color 7 n4277 n37))) n413))) (.edge 2 (.edge 16 (.edge 4 n8 (.edge 7 (.edge 9 n330 (.edge 17 n4431 n4437)) (.edge 5 (.edge 17 n12 n4444) n1989))) (.edge 17 (.edge 5 n12 (.edge 10 (.edge 7 n305 n4452) (.edge 6 n4455 n4458))) n3921)) (.edge 6 (.edge 9 (.edge 13 n1247 (.edge 7 (.edge 16 n330 n4466) (.color 6 n567 n570))) (.color 6 (.color 7 n567 n1402) (.color 7 n1402 n570))) (.color 7 n567 n570)))))
private def n4483 : Certificate := (.color 20 (.witness 31) (.witness 96))
private def n4490 : Certificate := (.edge 20 (.edge 5 n484 (.edge 10 n35 (.color 14 (.color 17 (.witness 32) n4483) (.color 17 n4483 (.witness 95))))) n570)
private def n4494 : Certificate := (.color 13 (.witness 83) (.witness 44))
private def n4500 : Certificate := (.edge 5 n12 (.color 10 (.color 14 n182 n3951) (.color 14 n3951 n185)))
private def n4501 : Certificate := (.color 7 (.color 15 n567 n3951) (.color 15 n3951 n570))
private def n4508 : Certificate := (.color 4 (.witness 92) (.witness 35))
private def n4512 : Certificate := (.edge 14 n1360 (.color 5 n1402 n1402))
private def n4513 : Certificate := (.color 7 n2658 n2659)
private def n4520 : Certificate := (.edge 15 n485 (.color 2 n1185 n1185))
private def n4521 : Certificate := (.color 6 n1185 n1185)
private def n4529 : Certificate := (.edge 14 n1360 (.edge 8 (.edge 15 n485 (.color 2 n4508 n4508)) n3921))
private def n4535 : Certificate := (.edge 5 (.edge 17 n12 n3921) (.color 6 n4494 n4494))
private def n4536 : Certificate := (.color 7 n1570 n1570)
private def n4542 : Certificate := (.edge 14 n1360 n4200)
private def n4544 : Certificate := (.color 18 (.witness 15) (.witness 112))
private def n4545 : Certificate := (.color 15 n567 n4544)
private def n4546 : Certificate := (.color 15 n4544 n570)
private def n4554 : Certificate := (.edge 12 n106 (.edge 9 (.edge 6 n1247 (.edge 8 n105 (.edge 16 (.edge 2 n8 (.edge 7 n330 (.edge 15 n110 n4490))) (.edge 20 (.edge 5 n484 (.edge 10 n35 n4494)) (.edge 17 (.edge 2 n4500 n4501) n1337))))) (.edge 16 (.edge 2 n8 (.edge 15 n110 (.edge 20 (.edge 14 n36 (.edge 17 n44 n4508)) (.edge 10 (.edge 6 n4512 n4513) n591)))) (.edge 20 (.edge 5 n484 (.edge 14 n36 (.edge 7 (.edge 8 n4520 n4521) (.witness 42)))) (.edge 7 (.edge 10 (.edge 17 n305 (.edge 6 n4529 n3880)) (.edge 8 (.edge 15 n485 n2763) (.edge 2 n4535 n4536))) (.edge 2 (.edge 5 (.edge 17 n12 n3919) (.color 6 n2758 n2759)) (.edge 6 (.edge 10 n4542 n1570) (.color 8 n4545 n4546))))))))
private def n4556 : Certificate := (.color 16 (.witness 83) (.witness 44))
private def n4559 : Certificate := (.color 6 (.color 12 n567 n2913) (.color 12 n2913 n570))
private def n4566 : Certificate := (.edge 12 n1103 (.color 1 n1585 n1585))
private def n4574 : Certificate := (.edge 17 n305 (.edge 8 (.edge 12 n1103 (.color 1 n4508 n4508)) n4404))
private def n4575 : Certificate := (.color 6 n3025 n3025)
private def n4580 : Certificate := (.edge 5 (.edge 14 n11 n1565) (.color 7 n4556 n4556))
private def n4585 : Certificate := (.edge 17 n305 n2927)
private def n4587 : Certificate := (.color 12 n567 n4544)
private def n4588 : Certificate := (.color 12 n4544 n570)
private def n4596 : Certificate := (.edge 2 n8 (.edge 15 n110 (.edge 9 (.edge 7 n330 (.edge 8 n105 (.edge 20 (.edge 5 n484 (.edge 10 n35 n4556)) (.edge 14 (.edge 1 n3480 n4559) n578)))) (.edge 20 (.edge 5 n484 (.edge 17 n44 (.edge 6 (.edge 8 n4566 n1585) (.witness 38)))) (.edge 6 (.edge 10 (.edge 14 n1360 (.edge 7 n4574 n4575)) (.edge 8 (.edge 12 n1103 n592) (.edge 1 n4580 n2455))) (.edge 1 (.edge 5 n3431 (.color 7 n584 n585)) (.edge 7 (.edge 10 n4585 n1239) (.color 8 n4587 n4588))))))))
private def n4600 : Certificate := (.edge 1 n11 (.edge 2 (.edge 17 n12 (.color 6 (.color 7 (.witness 21) (.witness 106)) (.color 7 (.witness 21) (.witness 106)))) n4536))
private def n4605 : Certificate := (.edge 15 n485 (.edge 17 (.edge 2 n12 (.edge 10 n305 n592)) n4305))
private def n4608 : Certificate := (.edge 2 (.edge 17 n12 (.color 6 n4305 n4305)) (.color 1 n4200 n4200))
private def n4613 : Certificate := (.edge 2 n12 (.edge 10 n305 (.color 1 n1034 n1035)))
private def n4616 : Certificate := (.edge 1 (.edge 14 n11 (.color 7 n4305 n4305)) (.color 2 n2927 n2927))
private def n4627 : Certificate := (.edge 2 n12 (.edge 7 n305 (.color 12 n4545 n4546)))
private def n4630 : Certificate := (.color 5 (.witness 44) (.witness 83))
private def n4646 : Certificate := (.edge 14 n1360 (.edge 17 n305 (.color 1 (.color 2 (.witness 34) n4508) (.color 2 n4508 (.witness 93)))))
private def n4647 : Certificate := (.color 8 (.witness 44) (.witness 83))
private def n4650 : Certificate := (.color 6 (.color 7 n79 n4647) (.color 7 n4647 n78))
private def n4657 : Certificate := (.color 10 (.witness 44) (.witness 83))
private def n4661 : Certificate := (.color 7 (.color 9 n79 n4657) (.color 9 n4657 n78))
private def n4665 : Certificate := (.edge 5 (.edge 20 n484 (.edge 8 (.edge 9 n105 (.edge 6 (.edge 12 (.triangle 16) (.edge 14 (.edge 10 n1360 n4600) (.edge 7 n4605 n4608))) (.edge 7 (.edge 15 n485 (.edge 17 n4613 n4616)) (.edge 1 (.edge 14 n11 n646) (.color 2 n2360 n2361))))) (.edge 14 (.edge 1 n11 (.edge 10 (.edge 6 n1360 (.edge 17 n4627 n2858)) (.color 2 (.color 4 n456 n4630) (.color 4 n4630 n459)))) (.color 5 (.color 10 (.witness 44) n4346) (.color 10 n4346 (.witness 83)))))) (.edge 8 (.edge 9 n105 (.edge 6 (.edge 12 (.triangle 16) (.edge 7 (.edge 15 n485 (.edge 10 n4646 n4650)) n2550)) n554)) (.edge 10 (.edge 6 (.edge 14 n1360 n4657) (.color 7 (.color 9 (.witness 81) n4657) (.color 9 n4657 (.witness 46)))) (.witness 44))))
private def n4669 : Certificate := (.color 9 (.witness 92) (.witness 35))
private def n4672 : Certificate := (.edge 14 n11 n676)
private def n4673 : Certificate := (.color 2 (.color 3 n567 n676) (.color 3 n676 n570))
private def n4679 : Certificate := (.edge 15 n5 n183)
private def n4680 : Certificate := (.color 1 n183 n183)
private def n4688 : Certificate := (.edge 14 n11 (.edge 3 (.edge 15 n5 (.color 7 n4669 n4669)) n4021))
private def n4693 : Certificate := (.edge 10 (.edge 17 n305 n4021) (.color 1 n4494 n4494))
private def n4697 : Certificate := (.color 7 (.color 9 n440 (.color 10 n178 n175)) (.color 9 (.color 10 n178 n175) n441))
private def n4701 : Certificate := (.edge 17 n305 n3777)
private def n4710 : Certificate := (.edge 6 n1247 (.edge 12 n106 (.edge 16 (.edge 7 n330 (.edge 15 (.triangle 31) (.edge 20 (.edge 14 n36 (.edge 17 n44 n4669)) (.edge 5 (.edge 1 n4672 n4673) n37)))) (.edge 20 (.edge 10 n35 (.edge 14 n36 (.edge 2 (.edge 3 n4679 n4680) (.witness 41)))) (.edge 2 (.edge 5 (.edge 17 n12 (.edge 1 n4688 n3786)) (.edge 3 (.edge 15 n5 n413) (.edge 7 n4693 n2120))) (.edge 1 (.edge 5 (.edge 14 n11 n4697) (.color 7 n447 n448)) (.edge 7 (.edge 10 n4701 n1352) (.color 3 n4545 n4546))))))))
private def n4711 : Certificate := (.edge 12 n4 n193)
private def n4719 : Certificate := (.edge 17 n12 (.edge 3 (.edge 12 n4 (.color 6 n4669 n4669)) (.color 1 n3082 n3082)))
private def n4724 : Certificate := (.edge 10 (.edge 14 n1360 n166) (.color 2 n4556 n4556))
private def n4725 : Certificate := (.color 1 n1091 n1091)
private def n4732 : Certificate := (.edge 14 n1360 n3089)
private def n4742 : Certificate := (.edge 12 n4 (.edge 2 (.edge 15 n5 n413) (.color 7 n447 n448)))
private def n4749 : Certificate := (.edge 2 (.edge 5 n12 (.edge 3 (.edge 15 n5 n1091) n857)) (.color 9 n429 n432))
private def n4752 : Certificate := (.edge 3 (.edge 15 n5 (.color 7 n2944 n2944)) n2858)
private def n4753 : Certificate := (.color 7 (.color 9 n429 n1382) (.color 9 n1382 n432))
private def n4760 : Certificate := (.edge 3 (.edge 15 n5 n166) (.color 6 (.color 9 n79 n4657) (.color 9 n4657 n78)))
private def n4764 : Certificate := (.edge 3 (.edge 12 n4 (.color 6 n4219 n4219)) n3552)
private def n4765 : Certificate := (.color 6 (.color 9 n429 n1382) (.color 9 n1382 n432))
private def n4769 : Certificate := (.edge 12 n4 n4263)
private def n4770 : Certificate := (.color 2 n4263 n4263)
private def n4780 : Certificate := (.edge 14 n11 (.edge 17 n12 (.color 6 (.color 7 (.witness 33) n4669) (.color 7 n4669 (.witness 94)))))
private def n4781 : Certificate := (.color 3 (.witness 44) (.witness 83))
private def n4784 : Certificate := (.color 1 (.color 2 n456 n4781) (.color 2 n4781 n459))
private def n4795 : Certificate := (.edge 16 (.edge 7 n330 (.edge 15 n110 (.edge 20 (.edge 10 n35 (.edge 17 n44 (.edge 1 (.edge 3 n4711 n193) (.witness 37)))) (.edge 1 (.edge 5 (.edge 14 n11 (.edge 2 n4719 n3332)) (.edge 3 (.edge 12 n4 n1989) (.edge 6 n4724 n4725))) (.edge 2 (.edge 5 (.edge 17 n12 n3071) (.color 6 n2015 n2016)) (.edge 6 (.edge 10 n4732 n1605) (.color 3 n4587 n4588))))))) (.edge 10 (.edge 20 n35 (.edge 14 (.edge 6 n1360 (.edge 1 (.edge 5 n11 (.edge 3 n4742 n4661)) (.edge 17 (.edge 7 n305 n4749) (.edge 2 n4752 n4753)))) (.edge 17 (.edge 7 n305 (.edge 2 (.edge 5 n12 n4760) (.edge 1 n4764 n4765))) (.edge 3 (.edge 1 n4769 n4770) (.witness 19))))) (.edge 1 (.edge 3 (.edge 12 n4 (.edge 2 (.edge 15 n5 (.edge 5 n4780 n4784)) n662)) (.color 1 (.color 2 n456 n4630) (.color 2 n4630 n459))) n2196)))
private def n4812 : Certificate := (.edge 6 n1360 (.edge 17 (.edge 2 n12 (.color 7 n429 n432)) (.color 2 (.color 7 n429 n3534) (.color 7 n3534 n432))))
private def n4819 : Certificate := (.edge 7 (.edge 10 n305 n662) (.color 1 (.color 6 n429 n2841) (.color 6 n2841 n432)))
private def n4821 : Certificate := (.color 15 n212 n4419)
private def n4822 : Certificate := (.color 15 n4419 n211)
private def n4837 : Certificate := (.edge 8 n1103 (.edge 7 (.edge 10 n305 (.edge 16 (.edge 20 n44 n1565) n662)) (.color 16 n2961 n2962)))
private def n4842 : Certificate := (.edge 7 (.edge 10 n305 (.color 16 n697 n698)) (.edge 16 (.edge 20 n44 n3025) (.color 1 n429 n432)))
private def n4845 : Certificate := (.color 12 (.witness 35) (.witness 92))
private def n4854 : Certificate := (.edge 17 (.edge 7 n305 (.edge 16 (.edge 20 n44 n166) n2550)) (.color 1 (.color 6 n1218 n4845) (.color 6 n4845 n1221)))
private def n4860 : Certificate := (.edge 16 (.edge 20 n44 (.color 1 n4331 n4331)) n554)
private def n4872 : Certificate := (.edge 2 (.edge 5 n12 n2036) (.edge 16 (.edge 20 n44 n3089) (.color 6 n429 n432)))
private def n4877 : Certificate := (.edge 20 n44 (.color 6 n4331 n4331))
private def n4878 : Certificate := (.edge 16 n4877 n2196)
private def n4885 : Certificate := (.color 14 n3161 n3161)
private def n4887 : Certificate := (.color 16 n429 n3161)
private def n4888 : Certificate := (.color 16 n3161 n432)
private def n4897 : Certificate := (.edge 15 (.edge 16 n110 (.edge 3 (.edge 1 n4 (.edge 2 n5 (.edge 8 (.edge 6 n1103 (.color 7 n429 n432)) (.color 6 (.color 7 n429 n1382) (.color 7 n1382 n432))))) (.edge 8 (.edge 6 n1103 (.edge 7 n485 (.color 1 (.color 2 n429 n646) (.color 2 n646 n432)))) (.edge 5 (.edge 14 (.edge 1 n11 (.edge 10 n4812 n2196)) (.edge 17 (.edge 2 n12 n4819) (.color 12 n4821 n4822))) (.color 6 (.color 7 n79 n4657) (.color 7 n4657 n78)))))) (.edge 1 (.edge 3 n4 (.edge 5 (.edge 14 n11 (.edge 17 (.edge 2 n12 (.edge 6 n4837 n4842)) (.color 1 (.color 6 n1218 n4845) (.color 6 n4845 n1221)))) (.edge 6 (.edge 8 n1103 (.edge 10 (.edge 14 n1360 n4854) n4556)) (.edge 17 (.edge 7 (.edge 10 n305 n4860) (.color 2 n224 n224)) n3443)))) (.edge 6 (.edge 8 n1103 (.edge 10 (.edge 14 n1360 (.edge 17 (.edge 7 n305 n4872) n3396)) (.edge 17 (.edge 2 (.edge 5 n12 n4878) (.color 7 n1605 n1605)) n3396))) (.edge 17 (.edge 2 (.edge 5 n12 (.edge 7 (.edge 10 n305 n4885) (.color 2 n4887 n4888))) (.color 7 n4887 n4888)) n1221))))
private def n4906 : Certificate := (.edge 10 n1360 (.edge 7 (.edge 8 n485 (.edge 13 (.edge 20 n36 n3921) n2196)) (.color 13 (.color 18 n267 n2770) (.color 18 n2770 n270))))
private def n4911 : Certificate := (.edge 7 (.edge 8 n485 (.color 13 n3701 n3702)) (.edge 13 (.edge 20 n36 n3794) (.color 2 n429 n432)))
private def n4914 : Certificate := (.color 15 n212 n211)
private def n4923 : Certificate := (.edge 14 (.edge 6 n1360 (.edge 13 (.edge 20 n36 n4021) n554)) (.color 2 (.color 7 n440 n4914) (.color 7 n4914 n441)))
private def n4929 : Certificate := (.edge 13 (.edge 20 n36 (.color 2 n4355 n4355)) n2550)
private def n4939 : Certificate := (.edge 1 (.edge 5 n11 (.color 13 (.color 18 n233 n468) (.color 18 n468 n232))) (.edge 13 (.edge 20 n36 n3777) (.color 7 n429 n432)))
private def n4941 : Certificate := (.color 6 n3971 n3971)
private def n4946 : Certificate := (.edge 13 (.edge 20 n36 (.color 7 n4355 n4355)) n662)
private def n4961 : Certificate := (.edge 16 n110 (.edge 2 (.edge 3 n5 (.edge 5 (.edge 17 n12 (.edge 14 (.edge 1 n11 (.edge 6 n4906 n4911)) (.color 2 (.color 7 n440 n4914) (.color 7 n4914 n441)))) (.edge 7 (.edge 8 n485 (.edge 10 (.edge 17 n305 n4923) n4494)) (.edge 14 (.edge 6 (.edge 10 n1360 n4929) (.color 1 n220 n220)) n524)))) (.edge 7 (.edge 8 n485 (.edge 10 (.edge 17 n305 (.edge 14 (.edge 6 n1360 n4939) n4941)) (.edge 14 (.edge 1 (.edge 5 n11 n4946) n1602) n1794))) (.edge 14 (.edge 1 (.edge 5 n11 (.edge 6 (.edge 10 n1360 n3612) (.color 1 n3764 n3765))) (.color 6 n3764 n3765)) n441))))
private def n4967 : Certificate := (.edge 20 (.edge 13 n36 (.color 16 n429 n432)) (.color 3 (.color 8 n567 n4544) (.color 8 n4544 n570)))
private def n4971 : Certificate := (.edge 16 n44 (.color 6 (.color 7 n429 n1198) (.color 7 n1198 n432)))
private def n4983 : Certificate := (.edge 16 n44 (.color 1 (.color 2 n429 n430) (.color 2 n430 n432)))
private def n4987 : Certificate := (.color 1 (.color 13 n1218 (.color 14 n212 n211)) (.color 13 (.color 14 n212 n211) n1221))
private def n4996 : Certificate := (.color 17 (.witness 35) (.witness 92))
private def n5004 : Certificate := (.edge 14 (.edge 5 (.edge 1 n11 (.edge 17 (.edge 2 n12 (.edge 10 (.edge 6 n1360 (.edge 7 n305 n4967)) (.edge 20 (.edge 13 n36 n4971) n1598))) (.color 6 (.color 13 n1218 (.color 14 n212 n211)) (.color 13 (.color 14 n212 n211) n1221)))) (.edge 10 (.edge 6 n1360 (.edge 17 (.edge 7 n305 (.edge 20 (.edge 13 n36 n4983) n216)) n4987)) (.color 14 (.color 17 n212 (.color 20 n152 n153)) (.color 17 (.color 20 n152 n153) n211)))) (.edge 17 (.edge 2 (.edge 5 n12 (.color 10 n4996 n4996)) (.color 7 (.color 16 n440 n4996) (.color 16 n4996 n441))) n212))
private def n5017 : Certificate := (.edge 20 (.edge 4 n484 (.edge 9 n35 (.color 13 (.color 16 (.witness 64) n4483) (.color 16 n4483 (.witness 63))))) n570)
private def n5021 : Certificate := (.color 13 (.witness 72) (.witness 55))
private def n5027 : Certificate := (.edge 4 n8 (.color 9 (.color 13 (.witness 72) n3383) (.color 13 n3383 (.witness 55))))
private def n5028 : Certificate := (.color 7 (.color 15 n567 n3383) (.color 15 n3383 n570))
private def n5035 : Certificate := (.color 4 n903 n905)
private def n5039 : Certificate := (.edge 13 n1247 (.color 4 n1316 n1316))
private def n5040 : Certificate := (.color 7 (.color 8 n567 n1316) (.color 8 n1316 n570))
private def n5047 : Certificate := (.edge 15 n485 (.color 2 n1213 n1213))
private def n5048 : Certificate := (.color 6 n1213 n1213)
private def n5053 : Certificate := (.color 5 (.witness 60) (.witness 67))
private def n5059 : Certificate := (.edge 13 n1247 (.edge 8 (.edge 15 n485 (.color 2 (.color 4 n903 n5053) (.color 4 n5053 n905))) n3921))
private def n5063 : Certificate := (.color 14 (.witness 51) (.witness 76))
private def n5064 : Certificate := (.color 13 (.witness 72) n5063)
private def n5065 : Certificate := (.color 13 n5063 (.witness 55))
private def n5067 : Certificate := (.edge 4 (.edge 16 n8 n3921) (.color 6 n5064 n5065))
private def n5074 : Certificate := (.edge 13 n1247 (.color 4 n267 n270))
private def n5076 : Certificate := (.color 19 (.witness 15) (.witness 112))
private def n5077 : Certificate := (.color 15 n567 n5076)
private def n5078 : Certificate := (.color 15 n5076 n570)
private def n5086 : Certificate := (.edge 12 n77 (.edge 10 (.edge 6 n1360 (.edge 8 n76 (.edge 17 (.edge 2 n12 (.edge 7 n305 (.edge 15 n83 n5017))) (.edge 20 (.edge 4 n484 (.edge 9 n35 n5021)) (.edge 16 (.edge 2 n5027 n5028) n1337))))) (.edge 17 (.edge 2 n12 (.edge 15 n83 (.edge 20 (.edge 13 n36 (.edge 16 n44 n5035)) (.edge 9 (.edge 6 n5039 n5040) n591)))) (.edge 20 (.edge 4 n484 (.edge 13 n36 (.edge 7 (.edge 8 n5047 n5048) (.witness 53)))) (.edge 7 (.edge 9 (.edge 16 n330 (.edge 6 n5059 n3880)) (.edge 8 (.edge 15 n485 n2763) (.edge 2 n5067 n4536))) (.edge 2 (.edge 4 (.edge 16 n8 n3686) (.color 6 n2161 n2161)) (.edge 6 (.edge 9 n5074 n1570) (.color 8 n5077 n5078))))))))
private def n5088 : Certificate := (.color 15 (.color 16 n429 n432) (.color 16 n429 n432))
private def n5094 : Certificate := (.edge 3 n5 (.color 8 (.color 12 (.witness 72) n3534) (.color 12 n3534 (.witness 55))))
private def n5095 : Certificate := (.color 7 n3534 n3534)
private def n5102 : Certificate := (.edge 12 n1103 (.color 3 n1198 n1198))
private def n5103 : Certificate := (.color 7 n1198 n1198)
private def n5113 : Certificate := (.edge 12 n1103 (.edge 9 (.edge 16 n330 (.color 2 (.color 3 n903 n5053) (.color 3 n5053 n905))) n3396))
private def n5116 : Certificate := (.color 7 (.color 8 (.witness 37) n2944) (.color 8 n2944 (.witness 90)))
private def n5124 : Certificate := (.edge 3 (.edge 15 n5 n3396) (.color 6 (.color 12 (.witness 72) n5063) (.color 12 n5063 (.witness 55))))
private def n5127 : Certificate := (.color 7 (.color 15 (.witness 37) n1605) (.color 15 n1605 (.witness 90)))
private def n5132 : Certificate := (.edge 12 n1103 n1826)
private def n5134 : Certificate := (.color 20 (.witness 15) (.witness 112))
private def n5135 : Certificate := (.color 16 n429 n5134)
private def n5136 : Certificate := (.color 16 n5134 n432)
private def n5144 : Certificate := (.edge 4 n484 (.edge 13 (.triangle 30) (.edge 10 (.edge 6 (.triangle 18) (.edge 9 n35 (.edge 17 (.edge 2 n12 (.edge 7 n305 n5088)) (.edge 15 (.edge 2 n5094 n5095) (.witness 39))))) (.edge 17 (.edge 2 n12 (.edge 16 n44 (.edge 8 (.edge 6 n5102 n5103) (.witness 45)))) (.edge 7 (.edge 8 (.edge 15 (.triangle 19) (.edge 6 n5113 n5116)) (.edge 9 (.edge 16 n330 n2196) (.edge 2 n5124 n5127))) (.edge 2 (.edge 3 (.edge 15 n5 n3406) (.color 6 n2292 n2292)) (.edge 6 (.edge 8 n5132 n1921) (.color 9 n5135 n5136))))))))
private def n5145 : Certificate := (.edge 3 n5 (.edge 4 (.edge 16 n8 n3686) (.color 6 n2161 n2161)))
private def n5150 : Certificate := (.edge 13 n1247 (.edge 16 (.edge 4 n8 (.edge 7 n330 n3408)) n2799))
private def n5155 : Certificate := (.edge 4 (.edge 16 n8 n2799) (.color 2 (.color 3 n590 n4319) (.color 3 n4319 n591)))
private def n5161 : Certificate := (.edge 4 n8 (.edge 7 n330 (.color 2 n1921 n1921)))
private def n5163 : Certificate := (.edge 3 (.edge 15 n5 n2799) (.color 2 (.color 4 n456 n4630) (.color 4 n4630 n459)))
private def n5173 : Certificate := (.edge 4 n8 (.edge 9 n330 (.color 12 n5064 n5065)))
private def n5176 : Certificate := (.color 2 (.witness 112) (.witness 15))
private def n5188 : Certificate := (.edge 13 n1247 (.edge 16 n330 (.color 3 (.color 4 n903 n5053) (.color 4 n5053 n905))))
private def n5191 : Certificate := (.color 6 (.witness 112) (.witness 15))
private def n5199 : Certificate := (.color 7 (.witness 112) (.witness 15))
private def n5204 : Certificate := (.edge 2 (.edge 17 n12 (.edge 6 (.edge 10 n1360 (.edge 8 (.edge 12 (.triangle 16) (.edge 15 (.edge 7 n485 n5145) (.edge 9 n5150 n5155))) (.edge 9 (.edge 13 (.triangle 17) (.edge 16 n5161 n5163)) (.edge 3 (.edge 15 n5 n1953) n1953)))) (.edge 15 (.edge 3 n5 (.edge 7 (.edge 8 n485 (.edge 16 n5173 n2858)) n5176)) (.color 2 (.color 7 (.witness 112) (.color 16 (.witness 7) (.witness 120))) (.color 7 (.color 16 (.witness 7) (.witness 120)) (.witness 15)))))) (.edge 6 (.edge 10 n1360 (.edge 8 (.edge 12 (.triangle 16) (.edge 7 (.edge 15 n485 (.edge 9 n5188 n1598)) n5191)) (.color 6 (.color 7 (.witness 112) n1818) (.color 7 n1818 (.witness 15))))) (.edge 7 (.edge 8 (.edge 15 n485 n5199) n5199) (.witness 15))))
private def n5208 : Certificate := (.color 16 (.witness 68) (.witness 59))
private def n5211 : Certificate := (.color 6 (.color 12 n567 n2834) (.color 12 n2834 n570))
private def n5218 : Certificate := (.edge 12 n1103 (.color 1 n1618 n1618))
private def n5226 : Certificate := (.edge 16 n330 (.edge 8 (.edge 12 n1103 (.color 1 (.color 4 n903 n5053) (.color 4 n5053 n905))) n4404))
private def n5229 : Certificate := (.color 17 (.witness 51) (.witness 76))
private def n5233 : Certificate := (.edge 4 (.edge 13 n7 n1565) (.color 7 (.color 16 (.witness 68) n5229) (.color 16 n5229 (.witness 59))))
private def n5237 : Certificate := (.color 7 (.color 8 n577 n1302) (.color 8 n1302 n578))
private def n5240 : Certificate := (.edge 16 n330 n1191)
private def n5242 : Certificate := (.color 12 n567 n5076)
private def n5243 : Certificate := (.color 12 n5076 n570)
private def n5251 : Certificate := (.edge 3 n295 (.edge 15 n83 (.edge 10 (.edge 7 n305 (.edge 8 n76 (.edge 20 (.edge 4 n484 (.edge 9 n35 n5208)) (.edge 13 (.edge 1 n4097 n5211) n578)))) (.edge 20 (.edge 4 n484 (.edge 16 n44 (.edge 6 (.edge 8 n5218 n1618) n639))) (.edge 6 (.edge 9 (.edge 13 n1247 (.edge 7 n5226 n4575)) (.edge 8 (.edge 12 n1103 n592) (.edge 1 n5233 n2455))) (.edge 1 (.edge 4 (.edge 13 n7 n5237) (.color 7 n687 n687)) (.edge 7 (.edge 9 n5240 n1239) (.color 8 n5242 n5243))))))))
private def n5253 : Certificate := (.edge 3 n4 (.color 8 n2841 n2841))
private def n5254 : Certificate := (.color 6 n2841 n2841)
private def n5262 : Certificate := (.edge 15 n485 (.edge 9 (.edge 13 n1247 (.color 1 (.color 3 n903 n5053) (.color 3 n5053 n905))) n4941))
private def n5265 : Certificate := (.color 6 (.color 8 n178 n4219) (.color 8 n4219 n175))
private def n5273 : Certificate := (.edge 3 (.edge 12 n4 n1794) (.color 7 (.color 15 (.witness 68) n5229) (.color 15 n5229 (.witness 59))))
private def n5277 : Certificate := (.color 7 n842 n842)
private def n5280 : Certificate := (.edge 15 n485 n1309)
private def n5282 : Certificate := (.color 13 n429 n5134)
private def n5283 : Certificate := (.color 13 n5134 n432)
private def n5291 : Certificate := (.edge 13 n1247 n3310)
private def n5296 : Certificate := (.edge 1 (.edge 4 (.edge 13 n7 (.color 6 n3310 n3310)) (.color 1 (.color 3 n590 n4319) (.color 3 n4319 n591))) n1598)
private def n5303 : Certificate := (.edge 1 (.edge 3 (.edge 12 n4 (.edge 4 (.edge 13 n7 n3310) (.color 1 n1309 n1309))) n2992) n2852)
private def n5307 : Certificate := (.edge 3 (.edge 12 n4 (.edge 4 (.edge 13 n7 n3310) (.color 1 (.color 3 n590 n4319) (.color 3 n4319 n591)))) (.color 1 (.color 12 n590 n1019) (.color 12 n1019 n591)))
private def n5313 : Certificate := (.edge 1 (.edge 4 n7 (.color 1 n821 n821)) n5199)
private def n5317 : Certificate := (.edge 3 (.edge 12 n4 (.color 6 n3310 n3310)) (.color 1 (.color 4 n456 n4630) (.color 4 n4630 n459)))
private def n5318 : Certificate := (.color 3 n2357 n2357)
private def n5330 : Certificate := (.edge 4 n7 (.edge 9 n1247 (.color 15 (.color 16 (.witness 68) n5229) (.color 16 n5229 (.witness 59)))))
private def n5334 : Certificate := (.color 1 (.color 6 n1735 (.color 12 (.witness 11) (.witness 116))) (.color 6 (.color 12 (.witness 11) (.witness 116)) n1738))
private def n5337 : Certificate := (.color 1 (.witness 112) (.witness 15))
private def n5347 : Certificate := (.edge 20 (.edge 4 n484 (.edge 16 n44 (.edge 10 (.edge 7 n305 (.edge 9 n35 (.edge 12 (.edge 1 n5253 n5254) (.witness 43)))) (.edge 6 (.edge 8 (.edge 12 n1103 (.edge 7 n5262 n5265)) (.edge 9 (.edge 13 n1247 n662) (.edge 1 n5273 n2319))) (.edge 1 (.edge 3 (.edge 12 n4 n5277) (.color 7 n657 n657)) (.edge 7 (.edge 8 n5280 n821) (.color 9 n5282 n5283))))))) (.edge 7 (.edge 10 n305 (.edge 8 (.edge 15 n485 (.edge 6 (.edge 12 n1103 (.edge 9 n5291 n5296)) (.edge 9 (.edge 16 n330 n5303) (.edge 1 n5307 n5199)))) (.edge 9 (.edge 16 n330 (.edge 13 (.edge 6 n1247 n5313) (.edge 1 n5317 n5318))) (.edge 1 (.edge 3 (.edge 12 n4 n366) n366) n365)))) (.edge 1 (.edge 12 (.edge 3 n4 (.edge 6 (.edge 8 n1103 (.edge 13 n5330 n5334)) n5337)) (.color 1 (.color 6 n1735 (.color 13 (.witness 11) (.witness 116))) (.color 6 (.color 13 (.witness 11) (.witness 116)) n1738))) n5191)))
private def n5353 : Certificate := (.color 7 (.witness 116) (.color 16 (.witness 3) (.witness 124)))
private def n5354 : Certificate := (.color 7 (.color 16 (.witness 3) (.witness 124)) (.witness 11))
private def n5363 : Certificate := (.edge 15 n485 (.edge 9 n5291 (.color 3 n4508 n4508)))
private def n5367 : Certificate := (.edge 7 (.edge 16 n330 n4263) n5191)
private def n5380 : Certificate := (.edge 15 n5 (.edge 7 (.edge 16 n330 (.edge 10 (.edge 20 n35 n4770) n2196)) n3071))
private def n5385 : Certificate := (.edge 7 (.edge 16 n330 (.color 5 n1382 n1382)) (.edge 10 (.edge 20 n35 n5191) n1921))
private def n5388 : Certificate := (.color 3 (.witness 76) (.witness 51))
private def n5395 : Certificate := (.edge 9 (.edge 16 n330 (.edge 10 (.edge 20 n35 n5199) n821)) n5388)
private def n5397 : Certificate := (.color 10 n386 n5134)
private def n5398 : Certificate := (.color 10 n5134 n389)
private def n5403 : Certificate := (.edge 20 n35 n5176)
private def n5404 : Certificate := (.color 2 n387 n387)
private def n5415 : Certificate := (.edge 6 (.edge 13 n1247 (.edge 10 (.edge 20 n35 (.color 1 n4263 n4263)) n662)) n4697)
private def n5422 : Certificate := (.color 9 (.color 16 n440 n3559) (.color 16 n3559 n441))
private def n5424 : Certificate := (.edge 20 n35 n5337)
private def n5425 : Certificate := (.color 1 n387 n387)
private def n5439 : Certificate := (.edge 4 (.edge 20 n484 (.edge 1 (.edge 12 n4 (.edge 13 n7 (.edge 2 (.edge 15 n5 (.color 2 n5353 n5354)) n3310))) (.edge 2 (.edge 15 n5 (.edge 16 n8 n2799)) (.edge 6 (.edge 8 (.edge 12 n1103 (.edge 7 n5363 n5191)) (.edge 9 (.edge 13 n1247 n5367) (.color 3 n2465 n2466))) n5199)))) (.edge 12 (.edge 1 n4 (.edge 6 (.edge 8 n1103 (.edge 9 (.edge 13 n1247 (.edge 2 n5380 n5385)) (.color 2 n5388 n5388))) (.edge 15 (.edge 2 n5 (.edge 7 (.edge 8 n485 n5395) (.color 5 n5397 n5398))) (.edge 9 (.edge 7 (.edge 16 n330 n3814) (.edge 10 n5403 n5404)) n4845)))) (.edge 15 (.edge 2 n5 (.edge 7 (.edge 8 n485 (.edge 9 (.edge 16 n330 n5415) (.color 1 n5388 n5388))) (.edge 9 (.edge 6 (.edge 13 n1247 n5422) (.edge 10 n5424 n5425)) (.color 15 n212 n211)))) (.edge 9 (.edge 6 (.edge 13 n1247 n4669) (.edge 7 (.edge 16 n330 n4669) (.color 8 n4669 n4669))) n212))))
private def n5445 : Certificate := (.edge 16 n8 (.edge 7 (.edge 15 n485 (.edge 10 (.edge 19 n76 (.color 2 n4508 n4508)) n2763)) n3919))
private def n5449 : Certificate := (.edge 7 (.edge 15 n485 (.color 5 n1402 n1402)) (.edge 10 (.edge 19 n76 n5191) n1570))
private def n5452 : Certificate := (.color 4 (.witness 76) (.witness 51))
private def n5459 : Certificate := (.edge 8 (.edge 15 n485 (.edge 10 (.edge 19 n76 n5199) n1239)) n5452)
private def n5461 : Certificate := (.color 10 n386 n5076)
private def n5462 : Certificate := (.color 10 n5076 n389)
private def n5467 : Certificate := (.edge 19 n76 n5176)
private def n5468 : Certificate := (.color 2 n534 n534)
private def n5478 : Certificate := (.edge 6 (.edge 12 n1103 (.edge 10 (.edge 19 n76 (.color 1 n4508 n4508)) n592)) n3023)
private def n5484 : Certificate := (.edge 19 n76 n5337)
private def n5485 : Certificate := (.color 1 n534 n534)
private def n5498 : Certificate := (.edge 20 n484 (.edge 13 (.edge 1 n7 (.edge 6 (.edge 9 n1247 (.edge 8 (.edge 12 n1103 (.edge 2 n5445 n5449)) (.color 2 n5452 n5452))) (.edge 16 (.edge 2 n8 (.edge 7 (.edge 9 n330 n5459) (.color 5 n5461 n5462))) (.edge 8 (.edge 7 (.edge 15 n485 n3201) (.edge 10 n5467 n5468)) n2858)))) (.edge 16 (.edge 2 n8 (.edge 7 (.edge 9 n330 (.edge 8 (.edge 15 n485 n5478) (.color 1 n5452 n5452))) (.edge 8 (.edge 6 (.edge 12 n1103 n4128) (.edge 10 n5484 n5485)) n3552))) (.edge 8 (.edge 6 (.edge 12 n1103 n4305) (.edge 7 (.edge 15 n485 n4305) n4305)) (.witness 19)))))
private def n5503 : Certificate := (.edge 10 (.edge 19 n76 n4669) (.color 1 (.color 2 n903 n5053) (.color 2 n5053 n905)))
private def n5506 : Certificate := (.color 1 n3297 n3297)
private def n5507 : Certificate := (.edge 20 n35 n5506)
private def n5512 : Certificate := (.color 8 (.witness 76) (.witness 51))
private def n5525 : Certificate := (.color 9 (.witness 76) (.witness 51))
private def n5530 : Certificate := (.edge 8 (.edge 6 (.edge 12 n1103 (.edge 9 (.edge 13 n1247 (.edge 7 (.edge 15 n485 (.edge 16 n330 n5503)) (.edge 10 (.edge 19 n76 n5507) n632))) n5512)) (.edge 7 (.edge 15 n485 (.edge 9 (.edge 16 n330 (.edge 10 (.edge 19 n76 n3621) (.color 1 n2150 n2150))) (.color 7 n5512 n5512))) (.color 8 (.color 9 (.witness 76) (.color 10 n29 n24)) (.color 9 (.color 10 n29 n24) (.witness 51))))) (.edge 9 (.edge 6 (.edge 13 n1247 n5525) (.color 7 n5525 n5525)) (.witness 51)))
private def n5538 : Certificate := (.color 4 (.color 9 n211 (.color 20 (.witness 3) (.witness 124))) (.color 9 (.color 20 (.witness 3) (.witness 124)) n212))
private def n5541 : Certificate := (.edge 13 n7 n4508)
private def n5544 : Certificate := (.color 2 (.color 3 (.witness 34) n4508) (.color 3 n4508 (.witness 93)))
private def n5550 : Certificate := (.edge 15 n5 n3297)
private def n5555 : Certificate := (.color 10 (.witness 60) (.witness 67))
private def n5561 : Certificate := (.edge 13 n7 (.edge 3 (.edge 15 n5 (.color 6 (.color 8 (.witness 65) n5555) (.color 8 n5555 n13))) n524))
private def n5562 : Certificate := (.color 3 (.witness 42) (.witness 85))
private def n5563 : Certificate := (.color 2 n5562 n5562)
private def n5566 : Certificate := (.color 2 (.color 16 n440 n4996) (.color 16 n4996 n441))
private def n5569 : Certificate := (.edge 17 (.edge 20 n44 n2270) (.color 6 n5512 n5512))
private def n5573 : Certificate := (.color 4 (.color 16 n440 n3559) (.color 16 n3559 n441))
private def n5577 : Certificate := (.edge 20 n44 n5191)
private def n5578 : Certificate := (.color 6 n1176 n1176)
private def n5586 : Certificate := (.edge 12 n1103 (.edge 19 n76 (.edge 7 (.edge 15 n485 (.edge 17 n305 (.edge 9 (.edge 13 n1247 (.edge 16 n330 n5538)) (.edge 4 (.edge 1 n5541 n5544) n212)))) (.edge 9 (.edge 13 n1247 (.edge 20 n35 (.edge 2 (.edge 3 n5550 n5506) (.witness 11)))) (.edge 2 (.edge 4 (.edge 16 n8 (.edge 1 n5561 n5563)) (.edge 3 (.edge 15 n5 n5566) (.edge 16 n5569 n524))) (.edge 1 (.edge 4 (.edge 13 n7 n5573) (.color 15 n3328 n3328)) (.edge 16 (.edge 17 n5577 n5578) n5562)))))))
private def n5594 : Certificate := (.edge 12 n4 (.edge 4 (.edge 16 n8 (.color 6 (.color 9 (.witness 65) n5555) (.color 9 n5555 n13))) n166))
private def n5599 : Certificate := (.color 2 (.color 15 n577 n4346) (.color 15 n4346 n578))
private def n5603 : Certificate := (.edge 17 (.edge 19 n83 n2270) (.color 6 n5525 n5525))
private def n5609 : Certificate := (.edge 19 n83 n5191)
private def n5610 : Certificate := (.color 6 n1290 n1290)
private def n5619 : Certificate := (.edge 4 n8 (.color 10 n5229 n5229))
private def n5623 : Certificate := (.edge 1 (.edge 4 (.edge 13 n7 n2550) (.color 2 (.color 15 (.witness 68) n5229) (.color 15 n5229 (.witness 59)))) (.color 6 n2564 n2564))
private def n5630 : Certificate := (.edge 1 (.edge 3 (.edge 12 n4 (.color 1 (.color 6 n1735 (.color 13 (.witness 11) (.witness 116))) (.color 6 (.color 13 (.witness 11) (.witness 116)) n1738))) (.edge 4 (.edge 13 n7 n5334) n2270)) n5191)
private def n5637 : Certificate := (.edge 3 (.edge 12 n4 (.color 1 (.color 3 (.witness 42) n4200) (.color 3 n4200 (.witness 85)))) (.edge 4 (.edge 13 n7 n2550) n4136))
private def n5643 : Certificate := (.edge 1 (.edge 13 n7 n3332) n1750)
private def n5646 : Certificate := (.edge 3 (.edge 12 n4 n1989) (.color 2 (.color 16 (.witness 68) n5229) (.color 16 n5229 (.witness 59))))
private def n5647 : Certificate := (.color 6 (.color 12 n38 n1983) (.color 12 n1983 n37))
private def n5661 : Certificate := (.edge 13 n7 (.edge 16 n8 (.color 6 (.color 7 (.witness 65) n5555) (.color 7 n5555 n13))))
private def n5664 : Certificate := (.color 1 (.color 2 (.witness 50) n5388) (.color 2 n5388 (.witness 77)))
private def n5667 : Certificate := (.color 1 (.witness 50) (.witness 77))
private def n5670 : Certificate := (.color 2 (.witness 50) n5452)
private def n5671 : Certificate := (.color 2 n5452 (.witness 77))
private def n5676 : Certificate := (.edge 9 (.edge 13 (.triangle 17) (.edge 20 n35 (.edge 7 (.edge 16 n330 (.edge 17 n305 (.edge 3 (.edge 1 n4769 n4770) (.witness 19)))) (.edge 2 (.edge 3 (.edge 15 n5 (.edge 1 n5594 n3079)) (.edge 4 (.edge 16 n8 n5599) (.edge 15 n5603 n166))) (.edge 1 (.edge 3 (.edge 12 n4 n4156) n3552) (.edge 15 (.edge 17 n5609 n5610) n3089)))))) (.edge 17 (.edge 7 n305 (.edge 15 (.edge 19 (.triangle 32) (.edge 2 (.edge 3 n5 (.edge 16 n5619 n5623)) (.edge 16 (.edge 20 n44 n5630) (.edge 1 n5637 n1746)))) (.edge 16 (.edge 20 n44 (.edge 4 (.edge 2 n8 n5643) (.edge 1 n5646 n5647))) (.edge 1 (.edge 3 (.edge 12 n4 n244) n244) (.witness 58))))) (.edge 1 (.edge 3 (.edge 12 n4 (.edge 2 (.edge 15 n5 (.edge 4 n5661 n5664)) n5667)) (.color 1 (.color 2 (.witness 50) n5452) (.color 2 n5452 (.witness 77)))) n2575)))
private def n5679 : Certificate := (.edge 12 n4 n3015)
private def n5688 : Certificate := (.edge 16 n8 (.edge 3 (.edge 12 n4 (.color 7 (.color 8 (.witness 65) n5555) (.color 8 n5555 n13))) (.color 1 n2505 n2505)))
private def n5693 : Certificate := (.edge 14 (.edge 20 n36 n734) (.color 7 n5512 n5512))
private def n5700 : Certificate := (.edge 20 n36 n5199)
private def n5701 : Certificate := (.color 7 n1176 n1176)
private def n5713 : Certificate := (.edge 15 n5 (.edge 4 (.edge 13 n7 (.color 7 (.color 9 (.witness 65) n5555) (.color 9 n5555 n13))) (.color 1 n1962 n1962)))
private def n5718 : Certificate := (.color 1 (.color 12 n1334 n4369) (.color 12 n4369 n1337))
private def n5721 : Certificate := (.edge 14 (.edge 19 n77 n734) (.color 7 n5525 n5525))
private def n5725 : Certificate := (.color 3 (.color 12 n1334 n3182) (.color 12 n3182 n1337))
private def n5728 : Certificate := (.edge 19 n77 n5199)
private def n5729 : Certificate := (.color 7 n1290 n1290)
private def n5736 : Certificate := (.edge 13 n7 n234)
private def n5740 : Certificate := (.edge 13 (.edge 14 (.edge 20 n36 n413) n5664) (.color 1 n234 n234))
private def n5747 : Certificate := (.edge 12 (.edge 14 (.edge 19 n77 n554) (.color 1 n5670 n5671)) (.color 1 n234 n234))
private def n5751 : Certificate := (.color 10 n5063 n5063)
private def n5762 : Certificate := (.edge 14 (.edge 12 (.edge 19 n77 n3967) (.edge 13 (.edge 20 n36 n3786) n234)) n2575)
private def n5766 : Certificate := (.edge 12 (.edge 19 n77 (.color 12 n3782 n3782)) (.edge 13 (.edge 20 n36 n413) n234))
private def n5776 : Certificate := (.edge 12 (.edge 19 n77 (.edge 13 (.edge 20 n36 n2858) n554)) (.color 4 (.color 13 (.witness 72) n3695) (.color 13 n3695 (.witness 55))))
private def n5784 : Certificate := (.edge 8 (.edge 15 n485 (.edge 19 n76 (.edge 9 (.edge 16 n330 (.edge 20 n35 (.edge 1 (.edge 3 n5679 n3015) (.witness 7)))) (.edge 1 (.edge 4 (.edge 13 n7 (.edge 2 n5688 n3453)) (.edge 3 (.edge 12 n4 n4987) (.edge 13 n5693 n3443))) (.edge 2 (.edge 4 (.edge 16 n8 n3967) (.color 12 n3782 n3782)) (.edge 13 (.edge 14 n5700 n5701) n1395)))))) (.edge 9 (.edge 16 n330 (.edge 20 n35 (.edge 1 (.edge 3 (.edge 12 n4 (.edge 2 n5713 n3635)) (.edge 4 (.edge 13 n7 n5718) (.edge 12 n5721 n4021))) (.edge 2 (.edge 3 (.edge 15 n5 n5725) n2858) (.edge 12 (.edge 14 n5728 n5729) n3777))))) (.edge 1 (.edge 3 (.edge 12 n4 (.edge 2 (.edge 15 n5 (.edge 4 n5736 n5740)) n418)) (.edge 4 (.edge 13 n7 (.edge 2 (.edge 16 n8 n5747) (.color 1 n558 n558))) (.edge 14 (.edge 12 (.edge 19 n77 n5751) (.color 1 n5064 n5065)) (.witness 51)))) (.edge 2 (.edge 3 (.edge 15 n5 (.edge 4 (.edge 16 n8 n5762) (.edge 14 n5766 n2575))) (.edge 4 (.edge 16 n8 (.edge 14 n5776 n2575)) (.color 12 n5064 n5065))) (.color 12 (.color 13 n233 n1437) (.color 13 n1437 n232))))))
private def n5793 : Certificate := (.edge 2 (.edge 15 n5 (.edge 4 n5736 n5664)) n5667)
private def n5800 : Certificate := (.edge 2 (.edge 16 n8 n5599) n3552)
private def n5806 : Certificate := (.edge 3 n5 (.edge 4 (.edge 16 n8 n2858) n5525))
private def n5809 : Certificate := (.edge 16 n8 n2071)
private def n5816 : Certificate := (.edge 16 n8 n4021)
private def n5819 : Certificate := (.edge 13 n7 n749)
private def n5832 : Certificate := (.edge 8 n76 (.edge 20 (.edge 9 n35 (.edge 14 (.edge 12 n77 (.edge 13 n36 (.edge 17 (.edge 15 n83 n229) n234))) (.edge 17 (.edge 15 n83 (.edge 16 n44 n244)) (.edge 1 (.edge 3 (.edge 12 n4 n5793) (.color 1 n5670 n5671)) n2575)))) (.edge 12 (.edge 14 n77 (.edge 1 (.edge 3 n4 (.edge 4 (.edge 13 n7 n5800) (.color 12 n255 n256))) (.edge 15 (.edge 17 n83 (.edge 2 n5806 n1290)) (.edge 2 (.edge 4 n5809 n1091) (.color 3 n5242 n5243))))) (.edge 15 (.edge 17 n83 (.edge 2 (.edge 3 n5 (.edge 4 n5816 n2120)) (.edge 1 (.edge 4 n5819 n171) (.color 3 n5077 n5078)))) (.edge 4 (.edge 1 (.edge 13 n7 n568) (.color 2 (.color 3 n567 n568) (.color 3 n568 n570))) n37)))))
private def n5833 : Certificate := (.edge 2 (.edge 15 n5 n5566) (.color 15 n3328 n3328))
private def n5839 : Certificate := (.edge 4 n8 (.edge 3 (.edge 15 n5 n4845) n5512))
private def n5842 : Certificate := (.edge 15 n5 n2591)
private def n5849 : Certificate := (.edge 15 n5 n3443)
private def n5852 : Certificate := (.color 2 (.color 15 (.witness 38) n224) (.color 15 n224 (.witness 89)))
private def n5855 : Certificate := (.edge 12 n4 n745)
private def n5869 : Certificate := (.edge 16 n8 (.color 8 (.color 9 (.witness 65) n5555) (.color 9 n5555 n13)))
private def n5872 : Certificate := (.color 2 n1735 (.color 3 (.witness 14) (.witness 113)))
private def n5873 : Certificate := (.color 2 (.color 3 (.witness 14) (.witness 113)) n1738)
private def n5882 : Certificate := (.edge 20 (.edge 9 n35 (.edge 13 (.edge 14 n36 (.edge 1 (.edge 4 n7 (.edge 3 (.edge 12 n4 n5833) n285)) (.edge 16 (.edge 17 n44 (.edge 2 n5839 n1176)) (.edge 2 (.edge 3 n5842 n2564) (.color 4 n5282 n5283))))) (.edge 16 (.edge 17 n44 (.edge 2 (.edge 4 n8 (.edge 3 n5849 n5852)) (.edge 1 (.edge 3 n5855 n548) (.color 4 n5135 n5136)))) (.edge 3 (.edge 1 (.edge 12 n4 n430) (.color 2 n430 n430)) n78)))) (.edge 1 (.edge 3 (.edge 12 n4 (.edge 2 (.edge 15 n5 (.edge 4 (.edge 13 n7 n5869) (.color 1 n5872 n5873))) n5337)) (.color 1 (.color 2 n1735 (.color 4 (.witness 14) (.witness 113))) (.color 2 (.color 4 (.witness 14) (.witness 113)) n1738))) n5176))
private def n5887 : Certificate := (.color 16 (.witness 83) (.color 20 (.witness 12) (.witness 115)))
private def n5888 : Certificate := (.color 16 (.color 20 (.witness 12) (.witness 115)) (.witness 44))
private def n5895 : Certificate := (.edge 9 n330 n5229)
private def n5900 : Certificate := (.edge 17 (.edge 19 n83 (.color 1 (.color 12 n182 n4494) (.color 12 n4494 n185))) n793)
private def n5903 : Certificate := (.edge 17 (.edge 20 n44 (.color 1 n4331 n4331)) n793)
private def n5918 : Certificate := (.edge 4 n8 (.edge 14 (.edge 19 n77 (.edge 17 (.edge 20 n44 n734) n3443)) (.edge 17 (.edge 20 n44 (.color 1 (.witness 24) (.witness 103))) n793)))
private def n5923 : Certificate := (.edge 14 (.edge 19 n77 (.color 7 n584 n585)) (.color 4 (.color 16 n637 n599) (.color 16 n599 n639)))
private def n5926 : Certificate := (.color 12 (.witness 67) (.witness 60))
private def n5933 : Certificate := (.edge 16 (.edge 20 n44 (.edge 2 (.edge 4 n8 (.color 2 (.color 16 n637 n275) (.color 16 n275 n639))) n3025)) n3993)
private def n5938 : Certificate := (.color 9 (.color 16 n79 n278) (.color 16 n278 n78))
private def n5940 : Certificate := (.edge 20 n44 n5337)
private def n5941 : Certificate := (.color 1 n2920 n2920)
private def n5951 : Certificate := (.edge 2 (.edge 4 n8 (.edge 7 (.edge 9 n330 (.color 1 (.color 6 (.witness 24) n4331) (.color 6 n4331 (.witness 103)))) n166)) n4404)
private def n5953 : Certificate := (.color 6 n1454 n5926)
private def n5954 : Certificate := (.color 6 n5926 n1455)
private def n5960 : Certificate := (.color 6 (.color 7 n29 n5525) (.color 7 n5525 n24))
private def n5962 : Certificate := (.edge 9 n330 n5667)
private def n5965 : Certificate := (.color 1 (.color 6 n386 n2920) (.color 6 n2920 n389))
private def n5968 : Certificate := (.color 19 (.witness 44) (.witness 83))
private def n5985 : Certificate := (.edge 13 (.edge 4 n7 (.edge 6 (.edge 8 n1103 (.edge 9 n1247 (.edge 14 (.edge 19 n77 (.color 13 n5887 n5888)) n5229))) (.edge 14 (.edge 19 n77 (.edge 20 n36 n734)) (.edge 7 (.edge 15 (.edge 8 n485 (.edge 16 n5895 n5900)) (.edge 16 (.edge 9 n330 n5903) n3993)) n275)))) (.edge 8 (.edge 6 n1103 (.edge 7 (.edge 15 n485 (.edge 16 (.edge 9 n330 (.edge 2 n5918 n5923)) (.color 1 n5926 n5926))) (.edge 19 (.edge 14 n77 (.edge 17 (.edge 15 n83 n5933) (.color 1 n2554 n2555))) (.edge 16 (.edge 2 (.edge 4 n8 n5938) (.edge 17 n5940 n5941)) n4647)))) (.edge 19 (.edge 14 n77 (.edge 17 (.edge 15 n83 (.edge 16 (.edge 20 n44 n5951) (.color 1 n5953 n5954))) (.edge 16 (.edge 2 (.edge 4 n8 n5960) (.edge 7 n5962 n5965)) (.color 12 (.color 15 n261 n5968) (.color 15 n5968 n260))))) (.edge 16 (.edge 2 (.edge 4 n8 (.color 9 n4556 n4556)) (.edge 7 (.edge 9 n330 (.color 4 n4556 n4556)) (.color 15 n4556 n4556))) (.witness 44)))))
private def n5989 : Certificate := (.edge 3 n5 (.edge 17 (.edge 19 n83 (.color 9 n4556 n4556)) (.color 6 n2292 n2292)))
private def n5991 : Certificate := (.edge 14 (.edge 19 n77 (.color 2 (.color 16 n456 n1833) (.color 16 n1833 n459))) (.color 9 (.color 16 n243 n2029) (.color 16 n2029 n242)))
private def n5996 : Certificate := (.edge 19 (.edge 14 n77 (.edge 15 n83 n3089)) n5191)
private def n6004 : Certificate := (.edge 2 (.edge 3 n5 (.color 12 (.color 15 n261 n5968) (.color 15 n5968 n260))) (.color 6 (.color 7 n386 n1290) (.color 7 n1290 n389)))
private def n6016 : Certificate := (.edge 2 (.edge 4 n8 n5124) (.color 6 (.color 12 n233 n1437) (.color 12 n1437 n232)))
private def n6024 : Certificate := (.edge 19 n83 (.color 6 (.color 12 n182 n4494) (.color 12 n4494 n185)))
private def n6035 : Certificate := (.edge 8 n1103 (.edge 9 (.edge 13 n1247 (.edge 16 (.edge 7 n330 (.edge 2 (.edge 4 n8 (.edge 15 n5989 n5991)) (.edge 17 (.edge 20 n44 n5996) (.color 6 n2920 n2920)))) (.edge 19 (.edge 14 n77 (.edge 15 (.edge 17 n83 n6004) n3854)) (.color 2 n4781 n4781)))) (.edge 14 (.edge 19 n77 (.edge 20 (.edge 13 n36 (.edge 16 (.edge 17 n44 n6016) (.color 2 n4781 n4781))) n1953)) (.edge 2 (.edge 15 (.edge 3 n5 (.edge 16 (.edge 4 n8 n5229) (.edge 17 n6024 n2575))) (.edge 16 (.edge 4 n8 (.edge 17 n4877 n2575)) n3854)) n1636))))
private def n6040 : Certificate := (.edge 7 (.edge 9 n330 (.edge 15 n5094 n1221)) (.edge 3 (.edge 15 n5 n2415) n2292))
private def n6044 : Certificate := (.edge 9 n330 (.edge 8 (.edge 15 n485 n1395) n558))
private def n6048 : Certificate := (.color 7 n4647 n4647)
private def n6050 : Certificate := (.edge 8 n485 n4781)
private def n6053 : Certificate := (.color 4 (.color 9 n429 n5134) (.color 9 n5134 n432))
private def n6061 : Certificate := (.edge 16 (.edge 4 n8 n734) (.color 12 n4494 n4494))
private def n6065 : Certificate := (.edge 9 n330 n4331)
private def n6068 : Certificate := (.color 14 n1454 n1455)
private def n6105 : Certificate := (.edge 14 (.edge 19 n77 (.edge 20 (.edge 13 n36 (.edge 16 (.edge 17 n44 (.edge 2 (.edge 4 n8 n6040) (.edge 7 n6044 n2920))) (.edge 15 (.edge 2 (.edge 3 n5 n6048) (.edge 7 n6050 n6053)) n5926))) (.edge 2 (.edge 15 (.edge 3 n5 (.edge 7 (.edge 8 n485 n6061) n5176)) (.edge 16 (.edge 4 n8 (.edge 7 n6065 n5176)) (.color 12 (.color 13 n261 n6068) (.color 13 n6068 n260)))) n5199))) (.edge 15 (.edge 2 (.edge 3 n5 (.edge 16 (.edge 4 n8 (.edge 7 (.edge 8 n485 n5895) n275)) (.edge 7 (.edge 8 n485 (.color 12 n3933 n3933)) (.color 2 n3933 n3933)))) (.edge 7 (.edge 8 n485 (.edge 16 (.edge 9 n330 n1636) (.color 7 n3933 n3933))) (.color 15 (.color 16 n1455 (.color 17 n386 n389)) (.color 16 (.color 17 n386 n389) n1454)))) (.edge 16 (.edge 2 (.edge 4 n8 (.edge 7 (.edge 9 n330 (.color 13 n3106 n3106)) (.color 2 n3106 n3106))) (.color 7 n3106 n3106)) n1454)))
private def n6109 : Certificate := (.color 17 n386 n5076)
private def n6110 : Certificate := (.color 17 n5076 n389)
private def n6111 : Certificate := (.color 14 n6109 n6110)
private def n6118 : Certificate := (.color 3 (.color 15 n590 (.color 19 n365 n364)) (.color 15 (.color 19 n365 n364) n591))
private def n6120 : Certificate := (.color 6 n3770 n3770)
private def n6132 : Certificate := (.edge 3 n5 (.edge 7 (.edge 8 n485 (.edge 17 (.edge 19 n83 n1953) n3921)) (.color 2 (.color 15 n590 (.color 17 (.witness 21) (.witness 106))) (.color 15 (.color 17 (.witness 21) (.witness 106)) n591))))
private def n6134 : Certificate := (.edge 7 (.edge 8 n485 n6118) (.edge 17 n5609 n1704))
private def n6136 : Certificate := (.color 3 n590 n4311)
private def n6137 : Certificate := (.color 3 n4311 n591)
private def n6147 : Certificate := (.edge 7 (.edge 8 n485 (.edge 17 (.edge 19 n83 (.color 6 n182 n185)) n2575)) (.color 8 (.color 15 n243 n2776) (.color 15 n2776 n242)))
private def n6152 : Certificate := (.edge 8 n485 (.color 7 (.color 15 n243 n1636) (.color 15 n1636 n242)))
private def n6155 : Certificate := (.edge 17 (.edge 19 n83 n5562) (.color 6 n386 n389))
private def n6165 : Certificate := (.edge 7 (.edge 8 n485 (.color 14 n3951 n3951)) (.edge 17 (.edge 19 n83 n5176) n3794))
private def n6169 : Certificate := (.edge 8 n485 (.edge 17 (.edge 19 n83 n5199) n3777))
private def n6172 : Certificate := (.color 13 (.witness 67) (.witness 60))
private def n6181 : Certificate := (.edge 1 n7 (.edge 16 (.edge 2 n8 (.edge 9 (.edge 7 n330 (.edge 6 (.triangle 17) (.edge 20 (.edge 17 n44 n3770) (.color 14 n6109 n6110)))) (.edge 20 (.edge 17 n44 (.edge 14 (.triangle 30) (.color 6 n1177 n1178))) (.edge 15 (.edge 7 (.edge 8 n485 n6118) (.edge 17 n5609 n6120)) n1598)))) (.edge 6 (.edge 9 (.triangle 17) (.edge 14 (.edge 20 (.triangle 30) (.edge 15 (.edge 2 n6132 n6134) (.color 2 n6136 n6137))) (.edge 15 (.edge 2 (.edge 3 n5 n6147) (.edge 7 n6152 n6155)) n3854))) (.edge 14 (.edge 20 (.triangle 30) (.edge 15 (.edge 2 (.edge 3 n5 n6165) (.edge 7 n6169 n6111)) n6172)) (.edge 15 (.edge 2 (.edge 3 n5 (.color 8 n3933 n3933)) (.color 7 n3933 n3933)) (.witness 56))))))
private def n6187 : Certificate := (.edge 14 (.edge 20 n36 (.edge 17 (.edge 19 n83 n734) n4021)) (.edge 17 (.edge 19 n83 (.color 1 n182 n185)) n793))
private def n6189 : Certificate := (.edge 20 n36 (.color 7 n447 n448))
private def n6192 : Certificate := (.color 3 (.color 15 n637 n464) (.color 15 n464 n639))
private def n6204 : Certificate := (.edge 19 n83 (.edge 2 (.edge 3 n5 (.color 2 (.color 15 n637 n275) (.color 15 n275 n639))) n842))
private def n6225 : Certificate := (.edge 3 n5 (.edge 7 (.edge 8 n485 (.color 1 (.color 6 n182 n4494) (.color 6 n4494 n185))) n524))
private def n6233 : Certificate := (.color 7 n29 n5512)
private def n6234 : Certificate := (.color 7 n5512 n24)
private def n6238 : Certificate := (.color 6 n386 n3770)
private def n6239 : Certificate := (.color 6 n3770 n389)
private def n6258 : Certificate := (.edge 9 (.edge 6 n1247 (.edge 7 (.edge 16 n330 (.edge 15 (.edge 8 n485 (.edge 2 (.edge 3 n5 n6187) (.edge 14 n6189 n6192))) (.color 1 n6172 n6172))) (.edge 20 (.edge 14 n36 (.edge 17 (.edge 16 n44 (.edge 15 n6204 n3993)) (.color 1 (.color 2 n386 n387) (.color 2 n387 n389)))) (.edge 15 (.edge 2 (.edge 3 n5 (.color 8 n255 n256)) (.edge 17 (.edge 19 n83 n5337) (.color 1 n3770 n3770))) n216)))) (.edge 20 (.edge 14 n36 (.edge 17 (.edge 16 n44 (.edge 15 (.edge 19 n83 (.edge 2 n6225 n4941)) (.color 1 (.color 6 n1454 n6172) (.color 6 n6172 n1455)))) (.edge 15 (.edge 2 (.edge 3 n5 (.color 6 n6233 n6234)) (.edge 7 (.edge 8 n485 n5667) (.color 1 n6238 n6239))) (.color 3 (.color 8 (.witness 76) (.color 19 n212 n211)) (.color 8 (.color 19 n212 n211) (.witness 51)))))) (.edge 15 (.edge 2 (.edge 3 n5 (.color 8 n4355 n4355)) (.edge 7 (.edge 8 n485 (.color 3 n4355 n4355)) n4355)) (.witness 28))))
private def n6260 : Certificate := (.edge 19 n83 n4556)
private def n6263 : Certificate := (.color 1 (.color 6 (.witness 72) n5063) (.color 6 n5063 (.witness 55)))
private def n6271 : Certificate := (.color 15 (.witness 67) (.witness 60))
private def n6287 : Certificate := (.edge 2 (.edge 3 n5 (.edge 16 (.edge 4 n8 (.edge 7 (.edge 8 n485 (.edge 9 n330 (.edge 17 n6260 n6263))) (.edge 17 (.edge 19 n83 (.edge 20 n44 n2270)) n632))) (.color 8 n6271 n6271))) (.edge 7 (.edge 8 n485 (.edge 16 (.edge 9 n330 (.edge 17 (.edge 19 n83 (.edge 20 n44 n366)) n1710)) (.color 7 n6271 n6271))) (.color 15 (.color 16 n261 (.color 17 (.witness 52) (.witness 75))) (.color 16 (.color 17 (.witness 52) (.witness 75)) n260))))
private def n6288 : Certificate := (.color 16 (.witness 67) (.witness 60))
private def n6293 : Certificate := (.edge 16 (.edge 2 (.edge 4 n8 (.color 9 n6288 n6288)) (.color 7 n6288 n6288)) n260)
private def n6301 : Certificate := (.edge 0 (.edge 1 (.edge 6 (.triangle 0) (.edge 2 (.edge 7 (.triangle 1) (.edge 11 (.triangle 5) (.edge 3 (.edge 8 n3 n65) (.edge 4 n104 n290)))) (.edge 3 (.edge 8 n3 (.edge 12 (.triangle 6) (.edge 4 n329 n480))) (.edge 4 (.edge 9 (.triangle 3) (.edge 13 n7 n615)) (.edge 5 (.edge 10 n10 n710) (.edge 15 n869 n1095)))))) (.edge 7 (.edge 2 (.triangle 1) (.edge 8 (.edge 15 (.triangle 19) (.edge 3 n3 (.edge 9 n1130 n1243))) (.edge 9 (.edge 16 (.triangle 20) (.edge 4 n6 n1357)) (.edge 10 (.edge 17 n305 n1444) (.edge 11 n1545 n1650))))) (.edge 3 (.edge 8 n3 (.edge 4 (.edge 18 (.triangle 12) (.edge 9 n6 n1759)) (.edge 5 (.edge 19 n295 n1842) (.edge 15 n1941 n2040)))) (.edge 9 (.edge 4 n6 (.edge 10 (.edge 20 n35 n2105) (.edge 13 n2176 n2298))) (.edge 5 (.edge 10 n10 (.edge 17 n2379 n2488)) (.edge 12 (.edge 14 n2541 n2628) (.edge 16 n2745 n2784))))))) (.edge 11 (.edge 12 (.edge 15 (.triangle 25) (.edge 13 (.edge 16 (.triangle 26) (.edge 18 (.triangle 28) (.edge 14 n2806 n2880))) (.edge 14 (.edge 17 (.triangle 27) (.edge 19 n77 n2951)) (.edge 1 (.edge 2 n2 n3029) (.edge 6 n3093 n3284))))) (.edge 16 (.edge 13 (.triangle 26) (.edge 17 (.edge 20 (.triangle 33) (.edge 14 n306 n3343)) (.edge 2 (.edge 4 n8 n3413) (.edge 7 n3460 n3573)))) (.edge 14 (.edge 17 n306 (.edge 1 (.edge 5 n11 n3642) (.edge 6 n3694 n3799))) (.edge 2 (.edge 1 n2 (.edge 3 n3863 n3958)) (.edge 7 (.edge 6 n1102 n4060) (.edge 19 n4189 n4224)))))) (.edge 18 (.edge 19 (.edge 20 (.triangle 34) (.edge 3 (.edge 4 (.triangle 12) (.edge 5 n295 n4285)) (.edge 8 (.edge 9 n105 n4327) (.edge 12 n4354 n4477)))) (.edge 4 (.edge 3 (.triangle 12) (.edge 13 (.edge 1 n7 n4554) (.edge 16 n4596 n4665))) (.edge 9 (.edge 8 n105 (.edge 13 n4710 n4795)) (.edge 12 (.edge 13 n106 n4897) (.edge 15 n4961 n5004))))) (.edge 5 (.edge 14 (.edge 1 n11 (.edge 19 (.edge 3 n295 n5086) (.edge 20 n5144 n5204))) (.edge 17 (.edge 2 (.triangle 11) (.edge 19 n5251 n5347)) (.edge 3 (.edge 19 n295 n5439) (.edge 4 n5498 n5530)))) (.edge 10 (.edge 6 (.edge 14 (.triangle 18) (.edge 8 n5586 n5676)) (.edge 7 (.edge 17 n305 n5784) (.edge 19 n5832 n5882))) (.edge 12 (.edge 1 (.edge 3 n4 n5985) (.edge 6 n6035 n6105)) (.edge 13 (.edge 4 n6181 n6258) (.edge 15 n6287 n6293))))))))
def masterCertificate := n6301

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem master_pass : check masterCertificate 0 0 0 0 = true := by decide +kernel

theorem finite_extension (g red : Nat → Bool) (ht : TriangleFree g) :
    ∃ c : Fin 128, Good g red c.val := by
  apply check_sound masterCertificate g red ht 0 0 0 0 <;>
    first | exact master_pass | intro i hi; simp at hi

/-- Lexicographic rank of a pair of distinct vertices in increasing order. -/
private def rank (a b : Fin 7) : Nat :=
  a.val * (13 - a.val) / 2 + (b.val - a.val - 1)

private def coded (f : Fin 7 → Fin 7 → Bool) (i : Nat) : Bool :=
  let p := pairs[i]!
  f p.1 p.2

private theorem pair_spec : ∀ a b : Fin 7, a < b → pairs[rank a b]! = (a,b) := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem red_spec : ∀ c : Fin 128, ∀ a b : Fin 7, a < b →
    redMasks[c.val]!.testBit (rank a b) = (c.val.testBit a.val && c.val.testBit b.val) := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem blue_spec : ∀ c : Fin 128, ∀ a b : Fin 7, a < b →
    redMasks[127 ^^^ c.val]!.testBit (rank a b) = (!c.val.testBit a.val && !c.val.testBit b.val) := by
  decide +kernel

private theorem tri_spec : ∀ j : Fin 35,
    let p := triples[j.val]!
    let a := p.1; let b := p.2.1; let c := p.2.2
    a < b ∧ b < c ∧ a < c ∧ triMasks[j.val]!.testBit (rank a b) = true ∧
      triMasks[j.val]!.testBit (rank a c) = true ∧ triMasks[j.val]!.testBit (rank b c) = true := by
  decide +kernel

private theorem coded_pair (f : Fin 7 → Fin 7 → Bool) {a b} (hab : a < b) :
    coded f (rank a b) = f a b := by simp [coded, pair_spec a b hab]

/-- On every triangle-free graph on seven labeled vertices, every Boolean edge coloring
admits vertex colors that never coincide with their common edge color at both ends. -/
theorem link_extension (g red : Fin 7 → Fin 7 → Bool)
    (ht : ∀ a b c : Fin 7, a < b → b < c → g a b = true → g a c = true →
      g b c = true → False) :
    ∃ col : Fin 7 → Bool, ∀ a b : Fin 7, a < b → g a b = true →
      ¬ (red a b = col a ∧ red a b = col b) := by
  have htf : TriangleFree (coded g) := by
    intro j hj
    obtain ⟨hab, hbc, hac, t₁, t₂, t₃⟩ := tri_spec j
    exact ht _ _ _ hab hbc ((coded_pair g hab).symm.trans (hj _ t₁))
      ((coded_pair g hac).symm.trans (hj _ t₂)) ((coded_pair g hbc).symm.trans (hj _ t₃))
  obtain ⟨c, hred, hblue⟩ := finite_extension (coded g) (coded red) htf
  refine ⟨fun v => c.val.testBit v.val, ?_⟩
  intro a b hab hedge hbad
  obtain ⟨ha,hb⟩ := hbad
  change red a b = c.val.testBit a.val at ha
  change red a b = c.val.testBit b.val at hb
  have hg := (coded_pair g hab).trans hedge
  cases h : red a b with
  | true =>
    have hbits : redMasks[c.val]!.testBit (rank a b) = true := by
      rw [red_spec c a b hab, ← ha, ← hb, h]
      rfl
    have impossible := (coded_pair red hab).symm.trans (hred _ hbits hg)
    simp [h] at impossible
  | false =>
    have hbits : redMasks[127 ^^^ c.val]!.testBit (rank a b) = true := by
      rw [blue_spec c a b hab, ← ha, ← hb, h]
      rfl
    have impossible := (coded_pair red hab).symm.trans (hblue _ hbits hg)
    simp [h] at impossible


end Erdos151Local.Link7

/-! For an edge-minimal triangle Ramsey graph use its edges as points and its triangles
as rows. A signed vector in the kernel of the incidence matrix would extend a valid
coloring of a graph with one edge deleted. -/

namespace Erdos151Research.CoreDensity

open Finset
open scoped BigOperators

def Bichromatic {E : Type*} (c : E → Bool) (s : Finset E) : Prop :=
  (∃ i ∈ s, c i = true) ∧ ∃ j ∈ s, c j = false

private theorem has_both_signs {E : Type*} (s : Finset E) (z : E → ℚ)
    (total : ∑ i ∈ s, z i = 0) (nonzero : ∃ i ∈ s, z i ≠ 0) :
    (∃ i ∈ s, 0 < z i) ∧ ∃ j ∈ s, z j < 0 := by
  obtain ⟨i, hi, hne⟩ := nonzero
  constructor
  · by_contra! neg
    have sum_neg : ∑ j ∈ s, -z j = 0 := by simp [total]
    have zero := (sum_eq_zero_iff_of_nonneg (fun j hj => neg_nonneg.mpr (neg j hj))).mp sum_neg i hi
    exact hne (neg_eq_zero.mp zero)
  · by_contra! pos
    exact hne ((sum_eq_zero_iff_of_nonneg pos).mp total i hi)

theorem density {E T : Type*} [Fintype E] [Fintype T] (row : T → Finset E)
    (ramsey : ¬ ∃ c : E → Bool, ∀ t, Bichromatic c (row t))
    (minimal : ∀ e : E, ∃ c : E → Bool, ∀ t, e ∉ row t → Bichromatic c (row t)) :
    Fintype.card E ≤ Fintype.card T := by
  classical
  let A : (E → ℚ) →ₗ[ℚ] (T → ℚ) :=
    { toFun := fun f t => ∑ i ∈ row t, f i
      map_add' := by intros; ext; simp [Finset.sum_add_distrib]
      map_smul' := by intros; ext; simp [Finset.mul_sum] }
  have trivial : ∀ z, A z = 0 → z = 0 := by
    intro z hz
    by_contra hne
    obtain ⟨e, he⟩ : ∃ e, z e ≠ 0 := by
      by_contra! all
      exact hne (funext all)
    obtain ⟨c, hc⟩ := minimal e
    let newColor (i : E) : Bool := if z i = 0 then c i else decide (0 < z i)
    apply ramsey
    refine ⟨newColor, fun t => ?_⟩
    by_cases zero : ∀ i ∈ row t, z i = 0
    · obtain ⟨⟨i, hi, hci⟩, j, hj, hcj⟩ := hc t (fun h => he (zero e h))
      exact ⟨⟨i, hi, by simp [newColor, zero i hi, hci]⟩,
             ⟨j, hj, by simp [newColor, zero j hj, hcj]⟩⟩
    · push Not at zero
      have total : ∑ i ∈ row t, z i = 0 := congrFun hz t
      obtain ⟨⟨i, hi, hpos⟩, j, hj, hneg⟩ := has_both_signs (row t) z total zero
      exact ⟨⟨i, hi, by simp [newColor, hpos.ne', hpos]⟩,
             ⟨j, hj, by simp [newColor, hneg.ne, hneg.not_gt]⟩⟩
  have inj : Function.Injective A := by
    intro x y hxy
    exact sub_eq_zero.mp (trivial (x-y) (by simp [map_sub, hxy]))
  simpa only [Module.finrank_pi] using LinearMap.finrank_le_finrank_of_injective inj

open SimpleGraph

variable {V : Type*} [DecidableEq V]

def pairs (s : Finset V) : Finset (Sym2 V) := s.sym2.filter (fun e => ¬e.IsDiag)

theorem mk_mem_pairs {a b : V} {s : Finset V} :
    s(a,b) ∈ pairs s ↔ a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  simp [pairs, and_assoc]

theorem pairs_are_edges (C : SimpleGraph V) {s : Finset V} (hs : C.IsClique s)
    {e : Sym2 V} (he : e ∈ pairs s) : e ∈ C.edgeSet := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    obtain ⟨ha, hb, hab⟩ := mk_mem_pairs.mp he
    exact hs ha hb hab

def GoodColoring (C : SimpleGraph V) (c : Sym2 V → Bool) : Prop :=
  ∀ t : Finset V, C.IsNClique 3 t → Bichromatic c (pairs t)

def Arrow (C : SimpleGraph V) : Prop := ¬ ∃ c, GoodColoring C c

theorem exists_minimal_core [Finite V] (G : SimpleGraph V) (hG : Arrow G) :
    ∃ C ≤ G, Minimal Arrow C := exists_minimal_le_of_wellFoundedLT Arrow G hG

theorem colorable_below {C D : SimpleGraph V} (hmin : Minimal Arrow C) (hlt : D < C) :
    ∃ c, GoodColoring D c := by
  by_contra notColorable
  exact hlt.not_ge (hmin.2 (show Arrow D from notColorable) hlt.le)

theorem colorable_delete {C : SimpleGraph V} (hmin : Minimal Arrow C)
    {e : Sym2 V} (he : e ∈ C.edgeSet) : ∃ c, GoodColoring (C.deleteEdges {e}) c := by
  apply colorable_below hmin
  refine lt_of_le_of_ne (C.deleteEdges_le _) ?_
  intro eqn
  have absent : e ∉ (C.deleteEdges {e}).edgeSet := by simp [SimpleGraph.edgeSet_deleteEdges]
  rw [eqn] at absent
  exact absent he

theorem triangle_survives_delete {C : SimpleGraph V} {t : Finset V} (htri : C.IsNClique 3 t)
    {e : Sym2 V} (missing : e ∉ pairs t) : (C.deleteEdges {e}).IsNClique 3 t := by
  refine ⟨?_, htri.card_eq⟩
  intro a ha b hb hab
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨htri.isClique ha hb hab, ?_⟩
  intro eqn
  change s(a,b) = e at eqn
  exact missing (eqn ▸ mk_mem_pairs.mpr ⟨ha,hb,hab⟩)

theorem edge_in_triangle {C : SimpleGraph V} (hmin : Minimal Arrow C)
    {e : Sym2 V} (he : e ∈ C.edgeSet) : ∃ t, C.IsNClique 3 t ∧ e ∈ pairs t := by
  obtain ⟨c, hc⟩ := colorable_delete hmin he
  by_contra! missing
  apply hmin.1
  exact ⟨c, fun t ht => hc t (triangle_survives_delete ht (missing t ht))⟩

theorem colorable_delete_vertex {C : SimpleGraph V} (hmin : Minimal Arrow C)
    {v u : V} (hu : C.Adj v u) : ∃ c, GoodColoring (C.deleteIncidenceSet v) c := by
  apply colorable_below hmin
  refine lt_of_le_of_ne (C.deleteIncidenceSet_le _) ?_
  intro eqn
  have impossible : (C.deleteIncidenceSet v).Adj v u := by rwa [eqn]
  exact (SimpleGraph.deleteIncidenceSet_adj.mp impossible).2.1 rfl

theorem minimal_core_density [Fintype V] (C : SimpleGraph V) (hmin : Minimal Arrow C) :
    Nat.card C.edgeSet ≤ Nat.card (C.cliqueSet 3) := by
  classical
  let E := C.edgeSet
  let T := C.cliqueSet 3
  let : Fintype E := Fintype.ofFinite E
  let : Fintype T := Fintype.ofFinite T
  let row (t : T) : Finset E := (pairs t.val).subtype (· ∈ C.edgeSet)
  have hArrow : ¬ ∃ c : E → Bool, ∀ t, Bichromatic c (row t) := by
    rintro ⟨c, hc⟩
    apply hmin.1
    refine ⟨fun e => if h : e ∈ C.edgeSet then c ⟨e,h⟩ else false, ?_⟩
    intro t ht
    obtain ⟨⟨e, he, ce⟩, f, hf, cf⟩ := hc ⟨t,ht⟩
    exact ⟨⟨e.val, Finset.mem_subtype.mp he, by simpa [e.property] using ce⟩,
           ⟨f.val, Finset.mem_subtype.mp hf, by simpa [f.property] using cf⟩⟩
  have minimal (e : E) : ∃ c : E → Bool, ∀ t, e ∉ row t → Bichromatic c (row t) := by
    obtain ⟨c, hc⟩ := colorable_delete hmin e.property
    refine ⟨fun x => c x.val, ?_⟩
    intro t missing
    have htri : C.IsNClique 3 t.val := t.property
    have survives := triangle_survives_delete htri (fun h => missing (Finset.mem_subtype.mpr h))
    obtain ⟨⟨a, ha, ca⟩, b, hb, cb⟩ := hc t.val survives
    exact ⟨⟨⟨a,pairs_are_edges C htri.isClique ha⟩, Finset.mem_subtype.mpr ha, ca⟩,
           ⟨⟨b,pairs_are_edges C htri.isClique hb⟩, Finset.mem_subtype.mpr hb, cb⟩⟩
  have result := density row hArrow minimal
  simpa only [Nat.card_eq_fintype_card] using result

end Erdos151Research.CoreDensity

namespace Erdos151Research.CoreDensity

open SimpleGraph

variable {V : Type*} [DecidableEq V] {C : SimpleGraph V}

theorem exists_edge_of_arrow (hC : Arrow C) : ∃ u v, C.Adj u v := by
  by_contra! noedges
  apply hC
  refine ⟨fun _ => false, fun t ht => ?_⟩
  obtain ⟨a, b, c, ab, _⟩ := is3Clique_iff.mp ht
  exact (noedges a b ab).elim

theorem core_edge_has_common_neighbor (hmin : Minimal Arrow C) {a b : V} (hab : C.Adj a b) :
    ∃ z, C.Adj z a ∧ C.Adj z b := by
  obtain ⟨t, htri, hp⟩ := edge_in_triangle hmin (e := s(a,b)) hab
  obtain ⟨ha,hb,ne⟩ := mk_mem_pairs.mp hp
  have outside : ¬ t ⊆ {a,b} := by
    intro sub
    have bound := Finset.card_le_card sub
    rw [htri.card_eq, Finset.card_pair ne] at bound
    omega
  obtain ⟨z, hz, hzpair⟩ := Finset.not_subset.mp outside
  have za : z ≠ a := fun eqn => hzpair (eqn ▸ Finset.mem_insert_self _ _)
  have zb : z ≠ b := by intro eqn; apply hzpair; simp [eqn]
  exact ⟨z, htri.isClique hz ha za, htri.isClique hz hb zb⟩

end Erdos151Research.CoreDensity

namespace Erdos151Research.CoreDensity

open SimpleGraph

/-- An arbitrary edge coloring of a triangle-free graph of order at most seven extends
over a cone vertex without creating a monochromatic triangle through that vertex. -/
theorem small_link_extension {V : Type*} [Fintype V] (L : SimpleGraph V) (free : L.CliqueFree 3)
    (size : Fintype.card V ≤ 7) (c : Sym2 V → Bool) :
    ∃ col : V → Bool, ∀ x y, L.Adj x y → ¬ (c s(x,y) = col x ∧ c s(x,y) = col y) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h => exact ⟨fun _ => false, fun x => isEmptyElim x⟩
  | inr h =>
    let e := (Fintype.equivFin V).toEmbedding.trans (Fin.castLEEmb size)
    let back := Function.invFun e
    have left (x : V) : back (e x) = x := Function.leftInverse_invFun e.injective x
    let graph := L.map e
    let red (i j : Fin 7) := c s(back i,back j)
    have hg : graph.CliqueFree 3 := cliqueFree_map_iff.mpr free
    obtain ⟨col,hcol⟩ := Erdos151Local.Link7.link_extension
      (fun i j => decide (graph.Adj i j)) red (by
        intro i j k _ _ h₁ h₂ h₃
        exact hg _ (is3Clique_triple_iff.mpr ⟨of_decide_eq_true h₁, of_decide_eq_true h₂,
          of_decide_eq_true h₃⟩))
    refine ⟨fun x => col (e x), ?_⟩
    intro x y adj
    have mapped : graph.Adj (e x) (e y) := map_adj_apply.mpr adj
    rcases lt_or_gt_of_ne (e.injective.ne adj.ne) with hxy | hyx
    · simpa [red, left] using hcol (e x) (e y) hxy (decide_eq_true mapped)
    · simpa [red, left, Sym2.eq_swap (a := y) (b := x), and_comm] using
        hcol (e y) (e x) hyx (decide_eq_true mapped.symm)


private theorem neighborhood_triangle_free {V : Type*} (C : SimpleGraph V)
    (h4 : C.CliqueFree 4) (v : V) : (C.induce (C.neighborSet v)).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨x,y,z,xy,xz,yz,-⟩ := is3Clique_iff.mp ht
  have base : C.IsNClique 3 {x.val,y.val,z.val} := is3Clique_triple_iff.mpr ⟨xy,xz,yz⟩
  apply h4 _ (base.insert (a := v) ?_)
  intro u hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  obtain rfl | rfl | rfl := hu
  · exact x.property
  · exact y.property
  · exact z.property

private def starColor {V : Type*} [DecidableEq V] (v : V) (atV : V → Bool)
    (base : Sym2 V → Bool) : Sym2 V → Bool :=
  Sym2.lift ⟨fun x y => if x = v then atV y else if y = v then atV x else base s(x,y), by
    intro x y
    by_cases hx : x = v <;> by_cases hy : y = v <;> simp [hx, hy, Sym2.eq_swap]⟩

private theorem bichromatic_of_ne {E : Type*} (c : E → Bool) {t : Finset E} {e f : E}
    (he : e ∈ t) (hf : f ∈ t) (diff : c e ≠ c f) : Bichromatic c t := by
  cases ce : c e <;> cases cf : c f
  · exact False.elim (diff (ce.trans cf.symm))
  · exact ⟨⟨f,hf,cf⟩,e,he,ce⟩
  · exact ⟨⟨e,he,ce⟩,f,hf,cf⟩
  · exact False.elim (diff (ce.trans cf.symm))

/-- Every non-isolated vertex of an edge-minimal triangle-Ramsey graph with no
four-clique has degree at least eight. Isolated vertices may be retained in the
common ambient vertex type. -/
theorem minimal_core_degree {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) [DecidableRel C.Adj] (h4 : C.CliqueFree 4)
    (hmin : Minimal Arrow C) {v u : V} (nonisolated : C.Adj v u) : 8 ≤ C.degree v := by
  classical
  by_contra! small
  obtain ⟨c,hc⟩ := colorable_delete_vertex hmin nonisolated
  let L := C.induce (C.neighborSet v)
  obtain ⟨col,valid⟩ := small_link_extension L (neighborhood_triangle_free C h4 v)
    (by rw [C.card_neighborSet_eq_degree]; omega)
    (fun p => c (p.map Subtype.val))
  let atV (x : V) := if h : C.Adj v x then col ⟨x,h⟩ else false
  let next := starColor v atV c
  apply hmin.1
  refine ⟨next, fun t ht => ?_⟩
  by_cases mem : v ∈ t
  · have card : (t.erase v).card = 2 := by rw [Finset.card_erase_of_mem mem, ht.card_eq]
    obtain ⟨x,y,xy,eq⟩ := Finset.card_eq_two.mp card
    have hx : x ∈ t.erase v := by rw [eq]; simp
    have hy : y ∈ t.erase v := by rw [eq]; simp
    obtain ⟨xv,xt⟩ := Finset.mem_erase.mp hx
    obtain ⟨yv,yt⟩ := Finset.mem_erase.mp hy
    have vx := ht.isClique mem xt xv.symm
    have vy := ht.isClique mem yt yv.symm
    have exy := ht.isClique xt yt xy
    have hdiff := valid ⟨x,vx⟩ ⟨y,vy⟩ exy
    have at_xy : next s(x,y) = c s(x,y) := by simp [next, starColor, xv, yv]
    have at_vx : next s(v,x) = col ⟨x,vx⟩ := by simp [next, starColor, atV, vx]
    have at_vy : next s(v,y) = col ⟨y,vy⟩ := by simp [next, starColor, atV, vy]
    change ¬ (c s(x,y) = col ⟨x,vx⟩ ∧ c s(x,y) = col ⟨y,vy⟩) at hdiff
    rw [← at_xy, ← at_vx, ← at_vy] at hdiff
    have mxy := mk_mem_pairs.mpr (And.intro xt (And.intro yt xy))
    rcases not_and_or.mp hdiff with h | h
    · exact bichromatic_of_ne next mxy (mk_mem_pairs.mpr ⟨mem,xt,xv.symm⟩) h
    · exact bichromatic_of_ne next mxy (mk_mem_pairs.mpr ⟨mem,yt,yv.symm⟩) h
  · have survives : (C.deleteIncidenceSet v).IsNClique 3 t := by
      refine ⟨?_,ht.card_eq⟩
      intro x hx y hy hxy
      exact deleteIncidenceSet_adj.mpr ⟨ht.isClique hx hy hxy,
        (fun eq => mem (eq ▸ hx)), (fun eq => mem (eq ▸ hy))⟩
    have agrees (e : Sym2 V) (he : e ∈ pairs t) : next e = c e := by
      induction e using Sym2.inductionOn with
      | _ x y =>
        obtain ⟨hx,hy,-⟩ := mk_mem_pairs.mp he
        have xv : x ≠ v := fun eq => mem (eq ▸ hx)
        have yv : y ≠ v := fun eq => mem (eq ▸ hy)
        simp [next, starColor, xv, yv]
    obtain ⟨⟨e,he,ce⟩,f,hf,cf⟩ := hc t survives
    exact ⟨⟨e,he,(agrees e he).trans ce⟩,f,hf,(agrees f hf).trans cf⟩

end Erdos151Research.CoreDensity

/-! From a bichromatic triangle edge coloring to the original transversal inequality. -/

namespace Erdos151Research.CoreDensity

open SimpleGraph

/-- In a good coloring keep every red edge and every edge that lies in no triangle. -/
theorem bound_of_good_coloring (n : ℕ) (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → Bool)
    (hc : GoodColoring G c) : G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  classical
  let selected (e : Sym2 (Fin n)) : Prop :=
    e ∈ G.edgeSet ∧ (c e = true ∨ ∀ t, G.IsNClique 3 t → e ∉ pairs t)
  let F := fromEdgeSet {e | selected e}
  have hFG : F ≤ G := by
    intro a b hab
    exact hab.1.1
  have free : F.CliqueFree 3 := by
    intro t ht
    have hgt := ht.mono hFG
    obtain ⟨e, he, blue⟩ := (hc t hgt).2
    have edgeF := pairs_are_edges F ht.isClique he
    have inSelected : selected e := by
      rw [SimpleGraph.edgeSet_fromEdgeSet] at edgeF
      exact edgeF.1
    rcases inSelected.2 with red | lone
    · simp [red] at blue
    · exact lone t hgt he
  apply Erdos151Research.ThresholdNine.bound_of_hitting n G F free
  intro s hs
  by_cases large : 3 ≤ s.card
  · obtain ⟨t, hts, hcard⟩ := Finset.exists_subset_card_eq large
    have ht : G.IsNClique 3 t := ⟨hs.1.1.subset hts, hcard⟩
    obtain ⟨e, he, red⟩ := (hc t ht).1
    induction e using Sym2.inductionOn with
    | _ a b =>
      obtain ⟨ha,hb,hab⟩ := mk_mem_pairs.mp he
      exact ⟨a, hts ha, b, hts hb, (SimpleGraph.fromEdgeSet_adj _).mpr
        ⟨⟨ht.isClique ha hb hab, Or.inl red⟩, hab⟩⟩
  · have hcard : s.card = 2 := by have := hs.2; omega
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hcard
    have gab := hs.1.1 (by simp : a ∈ ({a,b} : Finset _)) (by simp : b ∈ ({a,b} : Finset _)) hab
    refine ⟨a, by simp, b, by simp, (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨gab, Or.inr ?_⟩, hab⟩⟩
    intro t ht he
    obtain ⟨ha,hb,_⟩ := mk_mem_pairs.mp he
    have incl : ({a,b} : Finset _) ⊆ t :=
      Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
    have back := hs.1.2 ht.isClique incl
    have card := Finset.card_le_card back
    rw [ht.card_eq, Finset.card_pair hab] at card
    omega

end Erdos151Research.CoreDensity

/-! # Extending a set containing no nontrivial maximal clique -/

namespace Erdos151.NeighborhoodExtension

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- An outsider can be added if its neighbors in the original set are independent
and each edge from it to the set belongs to some triangle. -/
def SafeToAdd (U : Finset V) (x : V) : Prop :=
  G.IsIndepSet {y | y ∈ U ∧ G.Adj x y} ∧
    ∀ y ∈ U, G.Adj x y → ∃ z, G.Adj z x ∧ G.Adj z y

omit [Fintype V] in
private theorem cannot_extend {C : Finset V} (hC : G.IsBigMaximalClique C) (z : V)
    (hz : ∀ a ∈ C, G.Adj z a) : False := by
  have hins : G.IsClique ((insert z C : Finset V) : Set V) := by
    rw [Finset.coe_insert, SimpleGraph.isClique_insert]
    exact ⟨hC.1.1, fun a ha _ => hz a ha⟩
  have hzC : z ∈ C := hC.1.2 hins (Finset.subset_insert z C) (Finset.mem_insert_self z C)
  exact G.irrefl (hz z hzC)

/-- Safe outsiders can be added simultaneously if they form an independent set.
This direction holds for graphs of arbitrary clique number. -/
theorem safe_independent_union {U T : Finset V}
    (hU : G.IsCliqueTransversal Uᶜ) (hT : G.IsIndepSet (T : Set V))
    (hsafe : ∀ x ∈ T, SafeToAdd (G := G) U x) : G.IsCliqueTransversal (U ∪ T)ᶜ := by
  classical
  intro C hC
  by_contra! hmiss
  have hsub (a) (ha : a ∈ C) : a ∈ U ∨ a ∈ T := by
    exact Finset.mem_union.mp (Finset.notMem_compl.mp (hmiss a ha))
  obtain ⟨x, hxC, hxoutside⟩ := hU C hC
  have hxT : x ∈ T := (hsub x hxC).resolve_left (Finset.mem_compl.mp hxoutside)
  have hother (a) (ha : a ∈ C) (hxa : x ≠ a) : a ∈ U ∧ G.Adj x a := by
    have hxa' := hC.1.1 hxC ha hxa
    exact ⟨(hsub a ha).resolve_right (fun haT => hT hxT haT hxa hxa'), hxa'⟩
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hC.2
  have hex : ∃ y ∈ C, x ≠ y := by
    by_cases hxa : x = a
    · exact ⟨b, hb, by simpa [hxa] using hab⟩
    · exact ⟨a, ha, hxa⟩
  obtain ⟨y, hyC, hxy⟩ := hex
  obtain ⟨hyU, hxy'⟩ := hother y hyC hxy
  obtain ⟨z, hzx, hzy⟩ := (hsafe x hxT).2 y hyU hxy'
  apply cannot_extend hC z
  intro w hw
  by_cases hxw : x = w
  · simpa [← hxw] using hzx
  by_cases hyw : y = w
  · simpa [← hyw] using hzy
  exact False.elim ((hsafe x hxT).1 ⟨hyU, hxy'⟩ (hother w hw hxw) hyw (hC.1.1 hyC hw hyw))

/-- An open neighborhood cannot contain a maximal clique, since its center would extend it. -/
theorem neighborhood_compl_transversal (v : V) [DecidableRel G.Adj] :
    G.IsCliqueTransversal (G.neighborFinset v)ᶜ := by
  classical
  intro C hC
  by_contra! hmiss
  apply cannot_extend hC v
  intro a ha
  exact (G.mem_neighborFinset v a).mp (Finset.notMem_compl.mp (hmiss a ha))



end Erdos151.NeighborhoodExtension

/-! # A dense link in a graph with at least as many triangles as edges -/

namespace Erdos151.DenseLink

open SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Common neighbors of an edge biject with triangles containing that edge. -/
theorem common_neighbors_count {v u : V} (hvu : G.Adj v u) :
    ((G.neighborFinset v).filter (G.Adj u)).card =
      ((G.cliqueFinset 3).filter fun t => v ∈ t ∧ u ∈ t).card := by
  classical
  refine Finset.card_bij (fun x _ => {v, u, x}) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨mem_cliqueFinset_iff.mpr ?_, by simp⟩
    exact is3Clique_triple_iff.mpr ⟨hvu, (G.mem_neighborFinset v x).mp hx₁, hx₂⟩
  · intro a ha b _ heq
    obtain ⟨hva, hua⟩ := Finset.mem_filter.mp ha
    have h₁ := ((G.mem_neighborFinset v a).mp hva).ne.symm
    have h₂ := hua.ne.symm
    have hab : a ∈ ({v, u, b} : Finset V) := heq ▸ (by simp)
    simpa [h₁, h₂] using hab
  · intro t ht
    obtain ⟨ht, hvt, hut⟩ := Finset.mem_filter.mp ht
    have htc := mem_cliqueFinset_iff.mp ht
    have hsub : ({v,u} : Finset V) ⊆ t :=
      Finset.insert_subset_iff.mpr ⟨hvt, Finset.singleton_subset_iff.mpr hut⟩
    have hsize : (t \ {v,u}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, htc.2]
      simp [hvu.ne]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hsize
    have hxt : x ∈ t \ {v,u} := by rw [hx]; simp
    obtain ⟨hxt, hxn⟩ := Finset.mem_sdiff.mp hxt
    have hxv : v ≠ x := by rintro rfl; exact hxn (by simp)
    have hxu : u ≠ x := by rintro rfl; exact hxn (by simp)
    refine ⟨x, Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v x).mpr
      (htc.1 hvt hxt hxv), htc.1 hut hxt hxu⟩, ?_⟩
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset_iff.mpr
        ⟨hvt, Finset.insert_subset_iff.mpr ⟨hut, Finset.singleton_subset_iff.mpr hxt⟩⟩
    · rw [htc.2]
      simp [hvu.ne, hxv, hxu]

/-- For fixed center `v`, each triangle through the center has two other corners. -/
theorem link_count (v : V) :
    (∑ u ∈ G.neighborFinset v, ((G.neighborFinset v).filter (G.Adj u)).card) =
      2 * ((G.cliqueFinset 3).filter fun t => v ∈ t).card := by
  classical
  let Ts := (G.cliqueFinset 3).filter fun t => v ∈ t
  calc
    _ = ∑ u ∈ G.neighborFinset v, (Ts.filter fun t => u ∈ t).card := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [common_neighbors_count G ((G.mem_neighborFinset v u).mp hu)]
      simp [Ts, Finset.filter_filter]
    _ = ∑ t ∈ Ts, ((G.neighborFinset v).filter fun u => u ∈ t).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    _ = ∑ _t ∈ Ts, 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      obtain ⟨ht, hvt⟩ := Finset.mem_filter.mp ht
      have htc := mem_cliqueFinset_iff.mp ht
      have eqf : (G.neighborFinset v).filter (fun u => u ∈ t) = t.erase v := by
        ext x
        simp only [Finset.mem_filter, mem_neighborFinset, Finset.mem_erase]
        exact ⟨fun h => ⟨h.1.ne.symm, h.2⟩, fun h => ⟨htc.1 hvt h.2 h.1.symm, h.2⟩⟩
      rw [eqf, Finset.card_erase_of_mem hvt, htc.2]
    _ = _ := by simp [Ts, Nat.mul_comm]


/-- Across all centers, the two orientations of every triangle are counted at each of
its three vertices. -/
theorem sum_link_count :
    (∑ v, ∑ u ∈ G.neighborFinset v, ((G.neighborFinset v).filter (G.Adj u)).card) =
      6 * (G.cliqueFinset 3).card := by
  classical
  simp_rw [link_count]
  have htranspose : (∑ v : V, ((G.cliqueFinset 3).filter fun t => v ∈ t).card) =
      ∑ t ∈ G.cliqueFinset 3, (Finset.univ.filter fun v => v ∈ t).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [← Finset.mul_sum, htranspose]
  have hc : (∑ t ∈ G.cliqueFinset 3, (Finset.univ.filter fun v => v ∈ t).card)
      = ∑ _t ∈ G.cliqueFinset 3, 3 := by
    apply Finset.sum_congr rfl
    intro t ht
    have eqf : Finset.univ.filter (fun v => v ∈ t) = t := by ext; simp
    rw [eqf, (mem_cliqueFinset_iff.mp ht).2]
  rw [hc]
  simp [Nat.mul_comm]
  omega

/-- Some positive-degree vertex has at least three internal adjacency incidences per
neighbor, even when the core is represented as a spanning subgraph with isolated vertices. -/
theorem exists_dense_link (hE : ∃ x y, G.Adj x y)
    (hD : Nat.card G.edgeSet ≤ Nat.card (G.cliqueSet 3)) :
    ∃ v, 0 < G.degree v ∧ 3 * G.degree v ≤
      ∑ u ∈ G.neighborFinset v, ((G.neighborFinset v).filter (G.Adj u)).card := by
  classical
  have hcount : G.edgeFinset.card ≤ (G.cliqueFinset 3).card := by
    rw [← G.coe_edgeFinset, ← G.coe_cliqueFinset 3] at hD
    simpa only [Nat.card_coe_set_eq, Set.ncard_coe_finset] using hD
  by_contra! hn
  have weak (v : V) : (∑ u ∈ G.neighborFinset v, ((G.neighborFinset v).filter (G.Adj u)).card)
      ≤ 3 * G.degree v := by
    by_cases h : 0 < G.degree v
    · exact (hn v h).le
    · have he : G.neighborFinset v = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos h)
      simp [he]
  obtain ⟨x, y, hxy⟩ := hE
  have hx : 0 < G.degree x := Finset.card_pos.mpr ⟨y, (G.mem_neighborFinset x y).mpr hxy⟩
  have hlt := Finset.sum_lt_sum (fun v (_ : v ∈ Finset.univ) => weak v)
    ⟨x, Finset.mem_univ x, hn x hx⟩
  rw [sum_link_count, ← Finset.mul_sum, G.sum_degrees_eq_twice_card_edges] at hlt
  omega


end Erdos151.DenseLink

/-! # Counting the vertices blocked from extending a neighborhood -/

namespace Erdos151.NeighborhoodIncidence

open SimpleGraph
open scoped Classical

variable {V : Type*} (G : SimpleGraph V)

/-- An edge contained in no triangle. -/
def Lone (x y : V) : Prop := G.Adj x y ∧ ¬ ∃ z, G.Adj z x ∧ G.Adj z y

theorem lone_symm {x y : V} : Lone G x y ↔ Lone G y x := by
  constructor <;> rintro ⟨h, hn⟩ <;> refine ⟨h.symm, ?_⟩ <;>
    rintro ⟨z, h₁, h₂⟩ <;> exact hn ⟨z, h₂, h₁⟩

/-- For an unsafe outsider, count crossing edges once and lone crossing edges twice.
Every unsafe outsider contributes at least two. The hypothesis unfolds `SafeToAdd`
from `NeighborhoodExtension` and makes this counting lemma independently usable. -/
theorem unsafe_weight (S : Finset V) (x : V)
    (hx : ¬ (G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
      ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a)) :
    2 ≤ (S.filter (G.Adj x)).card + (S.filter (Lone G x)).card := by
  by_cases h : ∃ a ∈ S, Lone G x a
  · obtain ⟨a, ha, hl⟩ := h
    have h₁ : 0 < (S.filter (G.Adj x)).card :=
      Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hl.1⟩⟩
    have h₂ : 0 < (S.filter (Lone G x)).card :=
      Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hl⟩⟩
    omega
  · by_contra! hlt
    apply hx
    constructor
    · intro a ha b hb hab _
      have hc : (S.filter (G.Adj x)).card ≤ 1 := by omega
      exact hab (Finset.card_le_one_iff.mp hc (Finset.mem_filter.mpr ha) (Finset.mem_filter.mpr hb))
    · intro a ha hadj
      by_contra hnone
      exact h ⟨a, ha, hadj, hnone⟩

private theorem transpose_card {A B : Type*} (X : Finset A) (S : Finset B) (r : A → B → Prop) :
    (∑ x ∈ X, (S.filter (r x)).card) = ∑ u ∈ S, (X.filter fun x => r x u).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- The incidence inequality used by the order-41 argument. `X` is the full set of
outsiders and `B` any subset rejected by the individual safety test. Both sums on the
right are over the original neighborhood and can be bounded by vertex degrees. -/
theorem bad_incidence_bound (S X B : Finset V) (hBX : B ⊆ X)
    (hbad : ∀ x ∈ B, ¬ (G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
      ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a)) :
    2 * B.card ≤ (∑ u ∈ S, (X.filter (G.Adj u)).card) +
      ∑ u ∈ S, (X.filter (Lone G u)).card := by
  calc
    2 * B.card = ∑ _x ∈ B, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ B, ((S.filter (G.Adj x)).card + (S.filter (Lone G x)).card) :=
      Finset.sum_le_sum fun x hx => unsafe_weight G S x (hbad x hx)
    _ ≤ ∑ x ∈ X, ((S.filter (G.Adj x)).card + (S.filter (Lone G x)).card) :=
      Finset.sum_le_sum_of_subset_of_nonneg hBX (fun _ _ _ => Nat.zero_le _)
    _ = _ := by
      rw [Finset.sum_add_distrib, transpose_card X S G.Adj, transpose_card X S (Lone G)]
      congr 1
      · apply Finset.sum_congr rfl
        intro u _
        congr 1
        exact Finset.filter_congr fun x _ => G.adj_comm x u
      · apply Finset.sum_congr rfl
        intro u _
        congr 1
        exact Finset.filter_congr fun _ _ => lone_symm G

/-- For each neighbor `u` of the selected center `v`, its edges into the outsider set
and its core edges in the link have distinct endpoints, and the center costs one more.
A lone outsider edge cannot belong to a core in which every edge lies in a triangle. -/
theorem local_capacity [Fintype V] (C : SimpleGraph V) (hCG : C ≤ G)
    (htri : ∀ {a b}, C.Adj a b → ∃ z, C.Adj z a ∧ C.Adj z b)
    (v u : V) (S X : Finset V) (huv : G.Adj u v) (hvS : v ∉ S) (hvX : v ∉ X)
    (hSX : Disjoint S X) :
    (X.filter (G.Adj u)).card + (S.filter (C.Adj u)).card + 1 ≤ G.degree u ∧
    (X.filter (Lone G u)).card + C.degree u ≤ G.degree u := by
  classical
  let A := X.filter (G.Adj u)
  let B := S.filter (C.Adj u)
  have dAB : Disjoint A B := hSX.symm.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hvAB : v ∉ A ∪ B := by
    intro hv
    rcases Finset.mem_union.mp hv with ha | hb
    · exact hvX (Finset.mem_filter.mp ha).1
    · exact hvS (Finset.mem_filter.mp hb).1
  have hsub : insert v (A ∪ B) ⊆ G.neighborFinset u := by
    intro a ha
    apply (G.mem_neighborFinset u a).mpr
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact huv
    · rcases Finset.mem_union.mp ha with ha | hb
      · exact (Finset.mem_filter.mp ha).2
      · exact hCG (Finset.mem_filter.mp hb).2
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hvAB, Finset.card_union_of_disjoint dAB] at hcount
  refine ⟨hcount, ?_⟩
  let L := X.filter (Lone G u)
  have dLC : Disjoint L (C.neighborFinset u) := by
    apply Finset.disjoint_left.mpr
    intro a ha hca
    obtain ⟨z, hzu, hza⟩ := htri ((C.mem_neighborFinset u a).mp hca)
    exact (Finset.mem_filter.mp ha).2.2 ⟨z, hCG hzu, hCG hza⟩
  have hLC : L ∪ C.neighborFinset u ⊆ G.neighborFinset u := by
    intro a ha
    apply (G.mem_neighborFinset u a).mpr
    rcases Finset.mem_union.mp ha with hl | hc
    · exact (Finset.mem_filter.mp hl).2.1
    · exact hCG ((C.mem_neighborFinset u a).mp hc)
  have hlcount := Finset.card_le_card hLC
  rw [Finset.card_union_of_disjoint dLC] at hlcount
  exact hlcount

/-- Internal adjacency incidences are twice the number of edges induced on a set. -/
theorem internal_count [Fintype V] (S : Finset V) :
    (∑ u ∈ S, (S.filter (G.Adj u)).card) = 2 * (G.induce (S : Set V)).edgeFinset.card := by
  classical
  have hl (u : S) :
      (G.induce (S : Set V)).degree u = (S.filter (G.Adj (u : V))).card := by
    change ((G.induce (S : Set V)).neighborFinset u).card = _
    apply Finset.card_bij (fun (x : S) _ => (x : V))
    · intro x hx
      exact Finset.mem_filter.mpr ⟨x.property, ((G.induce (S : Set V)).mem_neighborFinset u x).mp hx⟩
    · intros; apply Subtype.ext; assumption
    · intro x hx
      obtain ⟨hxS, hux⟩ := Finset.mem_filter.mp hx
      exact ⟨⟨x, hxS⟩, (SimpleGraph.mem_neighborFinset _ _ _).mpr hux, rfl⟩
  have h := (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges
  simp_rw [hl] at h
  rw [← Finset.sum_attach S (fun u => (S.filter (G.Adj u)).card)]
  simpa using h

/-- A dense eight- or nine-vertex link in a core of minimum degree eight has enough
individually safe outsiders at order at least 37, if the ambient degrees are at most nine. -/
theorem many_good_outsiders [Fintype V] (C : SimpleGraph V) (hCG : C ≤ G)
    (htri : ∀ {a b}, C.Adj a b → ∃ z, C.Adj z a ∧ C.Adj z b)
    (v : V) (S X B : Finset V) (hS : ∀ u ∈ S, G.Adj u v)
    (hvS : v ∉ S) (hvX : v ∉ X) (hSX : Disjoint S X) (hBX : B ⊆ X)
    (hbad : ∀ x ∈ B, ¬ (G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
      ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a))
    (hdeg : ∀ u ∈ S, 8 ≤ C.degree u ∧ G.degree u ≤ 9)
    (hdensity : 3 * S.card ≤ ∑ u ∈ S, (S.filter (C.Adj u)).card)
    (horder : 37 ≤ X.card + S.card + 1) (hsize : S.card = 8 ∨ S.card = 9) :
    (S.card = 8 ∧ 4 ≤ (X \ B).card) ∨ (S.card = 9 ∧ 1 ≤ (X \ B).card) := by
  classical
  have hcap (u : V) (hu : u ∈ S) :=
    local_capacity G C hCG htri v u S X (hS u hu) hvS hvX hSX
  have hcross : (∑ u ∈ S, (X.filter (G.Adj u)).card) +
      (∑ u ∈ S, (S.filter (C.Adj u)).card) ≤ 8 * S.card := by
    calc
      _ = ∑ u ∈ S, ((X.filter (G.Adj u)).card + (S.filter (C.Adj u)).card) :=
        Finset.sum_add_distrib.symm
      _ ≤ ∑ _u ∈ S, 8 := Finset.sum_le_sum fun u hu => by
        have := (hcap u hu).1
        have := (hdeg u hu).2
        omega
      _ = _ := by simp [Nat.mul_comm]
  have hlone : (∑ u ∈ S, (X.filter (Lone G u)).card) ≤ S.card := by
    calc
      _ ≤ ∑ _u ∈ S, 1 := Finset.sum_le_sum fun u hu => by
        have := (hcap u hu).2
        obtain ⟨_, _⟩ := hdeg u hu
        omega
      _ = _ := by simp
  have hbadcount := bad_incidence_bound G S X B hBX hbad
  have heven := internal_count C S
  rw [Finset.card_sdiff_of_subset hBX]
  rcases hsize with h | h
  · exact Or.inl ⟨h, by omega⟩
  · exact Or.inr ⟨h, by omega⟩


end Erdos151.NeighborhoodIncidence

/-! # A degree-sensitive lower bound for safe outsiders of a Ramsey core link

For a suitable positive-degree vertex with core degree `d`, write `g` for the number of
safe outsiders and `D` for the maximum ambient degree. The bound is
`2g ≥ 2n − 2 − 2(D−1)d + d² + m`, where `m` counts crossing edges from the link
to safe outsiders. The main theorem uses addition in ℕ to avoid subtraction.
-/

namespace Erdos151.WeightedNeighborhood

open SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] (C : SimpleGraph V)

/-- Each neighbor's degree is counted once per edge arriving there. -/
theorem sum_neighbor_degrees :
    (∑ v, ∑ u ∈ C.neighborFinset v, C.degree u) = ∑ v, C.degree v * C.degree v := by
  classical
  have hN (v : V) : C.neighborFinset v = Finset.univ.filter (C.Adj v) := by ext; simp
  calc
    _ = ∑ u, ∑ v : V, if C.Adj v u then C.degree u else 0 := by
      simp_rw [hN, Finset.sum_filter]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      calc
        _ = ∑ v : V, if C.Adj u v then C.degree u else 0 := by
          apply Finset.sum_congr rfl
          intro v _
          rw [C.adj_comm v u]
        _ = ∑ _v ∈ C.neighborFinset u, C.degree u := by rw [hN, Finset.sum_filter]
        _ = _ := by simp

/-- Averaging the triangle incidence and neighbor-degree identities jointly gives a
center where the sum of the two link statistics pays for `3d+d²`. -/
theorem exists_weighted_link (hE : ∃ x y, C.Adj x y)
    (hD : Nat.card C.edgeSet ≤ Nat.card (C.cliqueSet 3)) :
    ∃ v, 0 < C.degree v ∧ 3 * C.degree v + C.degree v * C.degree v ≤
      (∑ u ∈ C.neighborFinset v, ((C.neighborFinset v).filter (C.Adj u)).card) +
        ∑ u ∈ C.neighborFinset v, C.degree u := by
  classical
  have hcount : C.edgeFinset.card ≤ (C.cliqueFinset 3).card := by
    rw [← C.coe_edgeFinset, ← C.coe_cliqueFinset 3] at hD
    simpa only [Nat.card_coe_set_eq, Set.ncard_coe_finset] using hD
  by_contra! hn
  have weak (v : V) :
      (∑ u ∈ C.neighborFinset v, ((C.neighborFinset v).filter (C.Adj u)).card) +
        (∑ u ∈ C.neighborFinset v, C.degree u) ≤ 3 * C.degree v + C.degree v * C.degree v := by
    by_cases hv : 0 < C.degree v
    · exact (hn v hv).le
    · have he : C.neighborFinset v = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hv)
      simp [he]
  obtain ⟨x, y, hxy⟩ := hE
  have hx : 0 < C.degree x := Finset.card_pos.mpr ⟨y, (C.mem_neighborFinset x y).mpr hxy⟩
  have hlt := Finset.sum_lt_sum (fun v (_ : v ∈ Finset.univ) => weak v)
    ⟨x, Finset.mem_univ x, hn x hx⟩
  simp only [Finset.sum_add_distrib, DenseLink.sum_link_count, sum_neighbor_degrees,
    ← Finset.mul_sum, C.sum_degrees_eq_twice_card_edges] at hlt
  omega

variable (G : SimpleGraph V)

/-- A graph with maximum degree `D` and a nonempty core with at least as many triangles
as edges contains a core link whose safe outsiders satisfy the degree-sensitive bound.
Here every core edge lies in a triangle. The proof charges each triangle obstruction
two crossing edges and each lone-edge obstruction an extra unit of non-core degree. -/
theorem safe_outsider_bound_on_core (D : ℕ) (hmax : ∀ u, 0 < C.degree u → G.degree u ≤ D) (hCG : C ≤ G)
    (hedge : ∃ x y, C.Adj x y) (hdensity : Nat.card C.edgeSet ≤ Nat.card (C.cliqueSet 3))
    (htri : ∀ {a b}, C.Adj a b → ∃ z, C.Adj z a ∧ C.Adj z b) :
    ∃ (v : V) (A : Finset V), 0 < C.degree v ∧ A ⊆ (insert v (C.neighborFinset v))ᶜ ∧
      (∀ x ∈ A, G.IsIndepSet {a | a ∈ C.neighborFinset v ∧ G.Adj x a} ∧
        ∀ a ∈ C.neighborFinset v, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a) ∧
      2 * Fintype.card V + C.degree v * C.degree v + 2 * C.degree v +
        (∑ u ∈ C.neighborFinset v, (A.filter (G.Adj u)).card) ≤
        2 * A.card + 2 * (D * C.degree v) + 2 := by
  classical
  obtain ⟨v, hv, hvdense⟩ := exists_weighted_link C hedge hdensity
  let S := C.neighborFinset v
  let X := (insert v S)ᶜ
  let safe (x : V) := G.IsIndepSet {a | a ∈ S ∧ G.Adj x a} ∧
    ∀ a ∈ S, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a
  let B := X.filter fun x => ¬ safe x
  let A := X \ B
  have hvS : v ∉ S := C.notMem_neighborFinset_self v
  have hvX : v ∉ X := by simp [X]
  have hSX : Disjoint S X := by
    apply Finset.disjoint_left.mpr
    exact fun u hu hx => (Finset.mem_compl.mp hx) (Finset.mem_insert_of_mem hu)
  have hBX : B ⊆ X := Finset.filter_subset _ _
  have hbad := NeighborhoodIncidence.bad_incidence_bound G S B B (fun _ h => h)
    (fun _ hx => (Finset.mem_filter.mp hx).2)
  have hpart : (∑ u ∈ S, (B.filter (G.Adj u)).card) + (∑ u ∈ S, (A.filter (G.Adj u)).card) =
      ∑ u ∈ S, (X.filter (G.Adj u)).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    have hdis : Disjoint (B.filter (G.Adj u)) (A.filter (G.Adj u)) :=
      Finset.disjoint_sdiff.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have heq : B ∪ A = X := Finset.union_sdiff_of_subset hBX
    rw [← Finset.card_union_of_disjoint hdis, ← Finset.filter_union, heq]
  have hmono : (∑ u ∈ S, (B.filter (NeighborhoodIncidence.Lone G u)).card) ≤
      ∑ u ∈ S, (X.filter (NeighborhoodIncidence.Lone G u)).card :=
    Finset.sum_le_sum fun u _ => Finset.card_le_card (Finset.filter_subset_filter _ hBX)
  have hcap (u : V) (hu : u ∈ S) :=
    NeighborhoodIncidence.local_capacity G C hCG htri v u S X
      (hCG ((C.mem_neighborFinset v u).mp hu).symm) hvS hvX hSX
  have degree (u : V) (hu : u ∈ S) := hmax u
    ((C.degree_pos_iff_exists_adj u).mpr ⟨v,((C.mem_neighborFinset v u).mp hu).symm⟩)
  have hcross : (∑ u ∈ S, (X.filter (G.Adj u)).card) +
      (∑ u ∈ S, (S.filter (C.Adj u)).card) + S.card ≤ D * S.card := by
    have hs := Finset.sum_le_sum (s := S) (fun u hu => (hcap u hu).1.trans (degree u hu))
    simpa [Finset.sum_add_distrib, Nat.mul_comm] using hs
  have hlone : (∑ u ∈ S, (X.filter (NeighborhoodIncidence.Lone G u)).card) +
      (∑ u ∈ S, C.degree u) ≤ D * S.card := by
    have hs := Finset.sum_le_sum (s := S) (fun u hu => (hcap u hu).2.trans (degree u hu))
    simpa [Finset.sum_add_distrib, Nat.mul_comm] using hs
  refine ⟨v, A, hv, Finset.sdiff_subset, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxX, hxB⟩ := Finset.mem_sdiff.mp hx
    by_contra h
    exact hxB (Finset.mem_filter.mpr ⟨hxX, h⟩)
  · have hA : A.card = X.card - B.card := Finset.card_sdiff_of_subset hBX
    have hcardB := Finset.card_le_card hBX
    have hX : X.card + (S.card + 1) = Fintype.card V := by
      change (insert v S)ᶜ.card + (S.card + 1) = _
      rw [← Finset.card_insert_of_notMem hvS, Finset.card_compl_add_card]
    change 3 * S.card + S.card * S.card ≤
      (∑ u ∈ S, (S.filter (C.Adj u)).card) + ∑ u ∈ S, C.degree u at hvdense
    change 2 * Fintype.card V + S.card * S.card + 2 * S.card +
      (∑ u ∈ S, (A.filter (G.Adj u)).card) ≤
      2 * A.card + 2 * (D * S.card) + 2
    omega

theorem safe_outsider_bound (D : ℕ) (hmax : ∀ u, G.degree u ≤ D) (hCG : C ≤ G)
    (hedge : ∃ x y, C.Adj x y) (hdensity : Nat.card C.edgeSet ≤ Nat.card (C.cliqueSet 3))
    (htri : ∀ {a b}, C.Adj a b → ∃ z, C.Adj z a ∧ C.Adj z b) :
    ∃ (v : V) (A : Finset V), 0 < C.degree v ∧ A ⊆ (insert v (C.neighborFinset v))ᶜ ∧
      (∀ x ∈ A, G.IsIndepSet {a | a ∈ C.neighborFinset v ∧ G.Adj x a} ∧
        ∀ a ∈ C.neighborFinset v, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a) ∧
      2 * Fintype.card V + C.degree v * C.degree v + 2 * C.degree v +
        (∑ u ∈ C.neighborFinset v, (A.filter (G.Adj u)).card) ≤
        2 * A.card + 2 * (D * C.degree v) + 2 :=
  safe_outsider_bound_on_core C G D (fun u _ => hmax u) hCG hedge hdensity htri


/-- Specializing to maximum degree eight, the selected core link has exactly eight
vertices. There are at least `n−25` safe outsiders, so one can be appended at order 26. -/
theorem exists_nine_of_degree_eight (horder : 26 ≤ Fintype.card V)
    (hmax : ∀ u, G.degree u ≤ 8) (hCG : C ≤ G)
    (hedge : ∃ x y, C.Adj x y) (hdensity : Nat.card C.edgeSet ≤ Nat.card (C.cliqueSet 3))
    (hmin : ∀ u, 0 < C.degree u → 8 ≤ C.degree u)
    (htri : ∀ {a b}, C.Adj a b → ∃ z, C.Adj z a ∧ C.Adj z b) :
    ∃ (v : V) (T : Finset V), Disjoint (C.neighborFinset v) T ∧
      G.IsIndepSet (T : Set V) ∧
      (∀ x ∈ T, G.IsIndepSet {a | a ∈ C.neighborFinset v ∧ G.Adj x a} ∧
        ∀ a ∈ C.neighborFinset v, G.Adj x a → ∃ z, G.Adj z x ∧ G.Adj z a) ∧
      9 ≤ (C.neighborFinset v).card + T.card := by
  classical
  obtain ⟨v, A, hv, hout, hsafe, hcount⟩ :=
    safe_outsider_bound C G 8 hmax hCG hedge hdensity htri
  have hdeg := le_antisymm ((SimpleGraph.degree_le_of_le (v := v) hCG).trans (hmax v)) (hmin v hv)
  rw [hdeg] at hcount
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  have hsub : ({x} : Finset V) ⊆ A := Finset.singleton_subset_iff.mpr hx
  refine ⟨v, {x}, ?_, ?_, fun z hz => hsafe z (hsub hz), ?_⟩
  · apply Finset.disjoint_left.mpr
    intro z hz hzx
    exact (Finset.mem_compl.mp (hout (hsub hzx))) (Finset.mem_insert_of_mem hz)
  · rw [← SimpleGraph.isClique_compl, Finset.coe_singleton]
    exact SimpleGraph.isClique_singleton x
  · rw [C.card_neighborFinset_eq_degree, hdeg, Finset.card_singleton]


end Erdos151.WeightedNeighborhood

/-! From a weighted core neighborhood to a nine-vertex free set. -/

namespace Erdos151Research

open SimpleGraph CoreDensity Erdos151.NeighborhoodExtension

open scoped Classical

theorem bound_of_large_degree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (large : Erdos151.H n ≤ G.degree v) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  calc
    G.cliqueTransversalNumber ≤ ((G.neighborFinset v)ᶜ).card :=
      csInf_le' ⟨_,neighborhood_compl_transversal v,rfl⟩
    _ ≤ n - Erdos151.H n := by
      rw [Finset.card_compl, Fintype.card_fin]
      exact Nat.sub_le_sub_left large n

theorem bound_at_most_eight {n : ℕ} (hk : Erdos151.H n ≤ 8)
    (G : SimpleGraph (Fin n)) (hK : G.CliqueFree 4) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  classical
  by_cases arrow : Arrow G
  · obtain ⟨C,hCG,hmin⟩ := exists_minimal_core G arrow
    obtain ⟨v,w,adj⟩ := exists_edge_of_arrow hmin.1
    have d := minimal_core_degree C (CliqueFree.anti hCG hK) hmin adj
    exact bound_of_large_degree G v (hk.trans (d.trans (C.degree_le_of_le hCG)))
  · obtain ⟨c,hc⟩ : ∃ c, GoodColoring G c := Classical.not_not.mp arrow
    exact bound_of_good_coloring n G c hc

theorem bound_of_core_extension {n : ℕ} (G C : SimpleGraph (Fin n)) (hCG : C ≤ G)
    (v : Fin n) (T : Finset (Fin n)) (disj : Disjoint (C.neighborFinset v) T)
    (ind : G.IsIndepSet (T : Set (Fin n)))
    (safe : ∀ x ∈ T, SafeToAdd (G := G) (C.neighborFinset v) x)
    (size : Erdos151.H n ≤ (C.neighborFinset v).card + T.card) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  have hcore : G.IsCliqueTransversal (C.neighborFinset v)ᶜ := by
    intro Q hQ
    obtain ⟨a,ha,hout⟩ := neighborhood_compl_transversal (G := G) v Q hQ
    refine ⟨a,ha,Finset.mem_compl.mpr (fun hin => (Finset.mem_compl.mp hout) ?_)⟩
    exact (G.mem_neighborFinset v a).mpr (hCG ((C.mem_neighborFinset v a).mp hin))
  have transv := safe_independent_union hcore ind safe
  calc
    G.cliqueTransversalNumber ≤ ((C.neighborFinset v ∪ T)ᶜ).card := csInf_le' ⟨_,transv,rfl⟩
    _ ≤ n - Erdos151.H n := by
      rw [Finset.card_compl, Fintype.card_fin, Finset.card_union_of_disjoint disj]
      exact Nat.sub_le_sub_left size n

/-- Reduce a numerical threshold to its sparse minimal Ramsey-core case. -/
theorem bound_of_core_case {n k : ℕ} (hk : Erdos151.H n ≤ k)
    (G : SimpleGraph (Fin n)) (hK : G.CliqueFree 4)
    (core_case : (∀ v, G.degree v < k) → ∀ C : SimpleGraph (Fin n), C ≤ G →
      (∃ x y, C.Adj x y) → Nat.card C.edgeSet ≤ Nat.card (C.cliqueSet 3) →
      (∀ u, 0 < C.degree u → 8 ≤ C.degree u) →
      (∀ {a b}, C.Adj a b → ∃ z, C.Adj z a ∧ C.Adj z b) →
      ∃ (v : Fin n) (T : Finset (Fin n)), Disjoint (C.neighborFinset v) T ∧
        G.IsIndepSet (T : Set _) ∧ (∀ x ∈ T, SafeToAdd (G := G) (C.neighborFinset v) x) ∧
        k ≤ (C.neighborFinset v).card + T.card) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  classical
  by_cases small : ∀ v, G.degree v < k
  · by_cases arrow : Arrow G
    · obtain ⟨C, hCG, hmin⟩ := exists_minimal_core G arrow
      have degree (u : Fin n) (hu : 0 < C.degree u) : 8 ≤ C.degree u := by
        obtain ⟨a, hca⟩ := (C.degree_pos_iff_exists_adj u).mp hu
        exact minimal_core_degree C (CliqueFree.anti hCG hK) hmin hca
      obtain ⟨v,T,disj,ind,safe,size⟩ := core_case small C hCG (exists_edge_of_arrow hmin.1)
        (minimal_core_density C hmin) degree (core_edge_has_common_neighbor hmin)
      exact bound_of_core_extension G C hCG v T disj ind safe (hk.trans size)
    · obtain ⟨c,hc⟩ : ∃ c, GoodColoring G c := Classical.not_not.mp arrow
      exact bound_of_good_coloring n G c hc
  · push Not at small
    obtain ⟨v,hv⟩ := small
    exact bound_of_large_degree G v (hk.trans hv)

theorem bound_at_most_nine {n : ℕ} (hn : 26 ≤ n) (hk : Erdos151.H n ≤ 9)
    (G : SimpleGraph (Fin n)) (hK : G.CliqueFree 4) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  apply bound_of_core_case hk G hK
  intro small C hCG hedge hdensity hmin htri
  exact Erdos151.WeightedNeighborhood.exists_nine_of_degree_eight C G (by simpa using hn)
    (fun u => Nat.le_of_lt_succ (small u)) hCG hedge hdensity hmin htri


end Erdos151Research

/-! An independent-set certificate shared by Ramsey witnesses of different orders. -/

namespace Erdos151Research.RamseyCertificate

/-- Branch on whether an independent set contains the first candidate. -/
def bounded {V : Type*} (adj : V → V → Bool) : ℕ → ℕ → List V → Bool
  | 0, cap, xs => decide (xs.length ≤ cap)
  | fuel + 1, cap, xs =>
    if xs.length ≤ cap then true else
      match cap, xs with
      | k + 1, a :: tail =>
        bounded adj fuel (k + 1) tail && bounded adj fuel k (tail.filter fun b => !adj a b)
      | _, _ => false

theorem bounded_sound {V : Type*} [DecidableEq V] (adj : V → V → Bool)
    (fuel cap : ℕ) (xs : List V) (s : Finset V) (checked : bounded adj fuel cap xs = true)
    (mem : ∀ x ∈ s, x ∈ xs) (ind : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → adj x y = false) :
    s.card ≤ cap := by
  have size_bound {t : Finset V} {ys : List V} (incl : ∀ x ∈ t, x ∈ ys) : t.card ≤ ys.length := by
    refine (Finset.card_le_card (show t ⊆ ys.toFinset from ?_)).trans ys.toFinset_card_le
    exact fun x hx => List.mem_toFinset.mpr (incl x hx)
  induction fuel generalizing cap xs s with
  | zero => exact (size_bound mem).trans (by simpa [bounded] using checked)
  | succ fuel ih =>
    by_cases short : xs.length ≤ cap
    · exact (size_bound mem).trans short
    cases xs with
    | nil => simp at short
    | cons a tail =>
      cases cap with
      | zero => simp [bounded] at checked
      | succ k =>
        have both : bounded adj fuel (k+1) tail = true ∧
            bounded adj fuel k (tail.filter fun b => !adj a b) = true := by
          have long : ¬ tail.length ≤ k := by simpa using short
          simpa [bounded, long] using checked
        by_cases ha : a ∈ s
        · have hsmall : (s.erase a).card ≤ k := by
            apply ih k _ (s.erase a) both.2
            · intro x hx
              obtain ⟨hxa, hs⟩ := Finset.mem_erase.mp hx
              apply List.mem_filter.mpr
              exact ⟨(List.mem_cons.mp (mem x hs)).resolve_left hxa, by simp [ind a ha x hs hxa.symm]⟩
            · intro x hx y hy hxy
              exact ind x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
          have := Finset.card_erase_add_one ha
          omega
        · apply ih (k+1) tail s both.1 _ ind
          intro x hx
          exact (List.mem_cons.mp (mem x hx)).resolve_left (fun he => ha (he ▸ hx))

end Erdos151Research.RamseyCertificate

/-! The finite threshold from a 25-vertex circulant and restriction. -/

namespace Erdos151Research.SmallThresholds

open SimpleGraph RamseyCertificate

theorem upper_of_cyclic {m cap : ℕ} [NeZero m] (p : Fin m → Bool)
    (flip : ∀ x, p (-x) = p x) (zero : p 0 = false)
    (tri : ∀ x y, p x = true → p y = true → p (x-y) = false)
    (checked : bounded (fun a b => p (a-b)) m cap (List.finRange m) = true)
    {n : ℕ} (hn : n ≤ m) : Erdos151.H n ≤ cap := by
  let e := Fin.castLEEmb hn
  let L : SimpleGraph (Fin n) :=
    { Adj := fun a b => p (e a - e b) = true
      symm := ⟨by intro a b h; rwa [← neg_sub (e a) (e b), flip]⟩
      loopless := ⟨by intro a; simp [zero]⟩ }
  have free : L.CliqueFree 3 := by
    intro t ht
    obtain ⟨a,b,c,ab,ac,bc,-⟩ := is3Clique_iff.mp ht
    have contradiction := tri (e a-e c) (e a-e b) ac ab
    have cancel : (e a-e c)-(e a-e b) = e b-e c := by abel
    rw [cancel] at contradiction
    exact Bool.noConfusion (contradiction.symm.trans bc)
  obtain ⟨s,hs⟩ := Erdos151Research.ThresholdNine.independent_at_threshold n L free
  have bound : (s.map e).card ≤ cap := by
    apply bounded_sound _ m cap (List.finRange m) _ checked
    · intro x _; exact List.mem_finRange x
    · intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hy
      exact Bool.eq_false_iff.mpr (hs.isIndepSet ha hb (fun he => hxy (congrArg e he)))
  simpa only [Finset.card_map, hs.card_eq] using bound

private def p25 (x : Fin 25) := [1,3,8,17,22,24].contains x.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem at_most_eight {n : ℕ} (hn : n ≤ 25) : Erdos151.H n ≤ 8 := by
  exact upper_of_cyclic p25 (by decide) (by decide) (by decide) (by decide +kernel) hn


end Erdos151Research.SmallThresholds

theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2.H1 := by
  intro n threshold G four
  by_cases small : n ≤ 25
  · exact Erdos151Research.bound_at_most_eight (Erdos151Research.SmallThresholds.at_most_eight small) G four
  · exact Erdos151Research.bound_at_most_nine (by omega) threshold G four
