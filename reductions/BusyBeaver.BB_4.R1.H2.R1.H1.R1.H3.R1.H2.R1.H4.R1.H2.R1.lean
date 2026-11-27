import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1

/-!
Split the 53 base-17 residual tables of write-0 H4 into four batches so each
batch can be proved nonhalting independently (FAR / bounded simulation).

Parent classification: @marcusbuffett `…H4.R1`.
-/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1_H2_R1

open Turing Turing.BusyBeaver

def H1 : Prop :=
  let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=
    let k := z / 17 ^ (2 * r.val + s.val) % 17
    if k = 16 then none
    else some (some (Fin.ofNat 4 (k / 4)),
      .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))
  ∀ z ∈ ([192926630, 394870650, 515740378, 1336417724, 1408830431, 1627390098,
       1689441169, 2446657396, 2452336858, 2460855813, 2460855983, 2930234279,
       3133858477] : List ℕ), ¬ Machine.IsHalting (entry z)

def H2 : Prop :=
  let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=
    let k := z / 17 ^ (2 * r.val + s.val) % 17
    if k = 16 then none
    else some (some (Fin.ofNat 4 (k / 4)),
      .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))
  ∀ z ∈ ([3267241361, 3267325035, 3267408318, 3267408386, 3268076724, 3268179812,
       3268243766, 3325136085, 3330584823, 3330638645, 3475567181, 3475567351,
       3672067699] : List ℕ), ¬ Machine.IsHalting (entry z)

def H3 : Prop :=
  let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=
    let k := z / 17 ^ (2 * r.val + s.val) % 17
    if k = 16 then none
    else some (some (Fin.ofNat 4 (k / 4)),
      .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))
  ∀ z ∈ ([3673413691, 3673413861, 4079576433, 4093775003, 4100731862, 4498257380,
       4684022874, 4953712200, 4972106404, 4972170205, 5435078199, 5439716071,
       5439804454] : List ℕ), ¬ Machine.IsHalting (entry z)

def H4 : Prop :=
  let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=
    let k := z / 17 ^ (2 * r.val + s.val) % 17
    if k = 16 then none
    else some (some (Fin.ofNat 4 (k / 4)),
      .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))
  ∀ z ∈ ([5440806757, 5453953928, 5537278425, 5792616725, 6328050068, 6695802976,
       6734875946, 6734876082, 6734876116, 6745900956, 6746235074, 6775658997,
       6778655859, 6852444036] : List ℕ), ¬ Machine.IsHalting (entry z)

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1.H2 := by
  intro h1 h2 h3 h4 z hz
  let L1 : List ℕ := [192926630, 394870650, 515740378, 1336417724, 1408830431, 1627390098,
    1689441169, 2446657396, 2452336858, 2460855813, 2460855983, 2930234279, 3133858477]
  let L2 : List ℕ := [3267241361, 3267325035, 3267408318, 3267408386, 3268076724, 3268179812,
    3268243766, 3325136085, 3330584823, 3330638645, 3475567181, 3475567351, 3672067699]
  let L3 : List ℕ := [3673413691, 3673413861, 4079576433, 4093775003, 4100731862, 4498257380,
    4684022874, 4953712200, 4972106404, 4972170205, 5435078199, 5439716071, 5439804454]
  let L4 : List ℕ := [5440806757, 5453953928, 5537278425, 5792616725, 6328050068, 6695802976,
    6734875946, 6734876082, 6734876116, 6745900956, 6746235074, 6775658997, 6778655859,
    6852444036]
  have hEq :
      ([192926630, 394870650, 515740378, 1336417724, 1408830431, 1627390098,
         1689441169, 2446657396, 2452336858, 2460855813, 2460855983, 2930234279,
         3133858477, 3267241361, 3267325035, 3267408318, 3267408386, 3268076724,
         3268179812, 3268243766, 3325136085, 3330584823, 3330638645, 3475567181,
         3475567351, 3672067699, 3673413691, 3673413861, 4079576433, 4093775003,
         4100731862, 4498257380, 4684022874, 4953712200, 4972106404, 4972170205,
         5435078199, 5439716071, 5439804454, 5440806757, 5453953928, 5537278425,
         5792616725, 6328050068, 6695802976, 6734875946, 6734876082, 6734876116,
         6745900956, 6746235074, 6775658997, 6778655859, 6852444036] : List ℕ) =
        L1 ++ L2 ++ L3 ++ L4 := rfl
  have hz' : z ∈ L1 ++ L2 ++ L3 ++ L4 := by
    rwa [← hEq]
  -- Association: `((L1 ++ L2) ++ L3) ++ L4`.
  rcases (List.mem_append.mp hz') with h123 | h4mem
  · rcases (List.mem_append.mp h123) with h12 | h3mem
    · rcases (List.mem_append.mp h12) with h1mem | h2mem
      · exact h1 z h1mem
      · exact h2 z h2mem
    · exact h3 z h3mem
  · exact h4 z h4mem

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1_H2_R1
