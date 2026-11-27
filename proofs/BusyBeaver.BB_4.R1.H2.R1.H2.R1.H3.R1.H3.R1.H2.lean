import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1
import Mathlib

/-! Finite invariants for four machines with growing runs of ones. Each half-tape
reader tracks zero/one runs, recording parity and distinguishing short runs.
The masks list the reachable combinations of control, current bit and reader
states. The closure of each marked set is checked in the kernel. -/
-- Credit: @marcusbuffett
namespace OMA.BB4FourReaders
open Turing Turing.BusyBeaver

private def digit (z : ℕ) (q : Fin 4) (a : Fin 2) := z / 17^(2*q.val+a.val) % 17
private def table (z : ℕ) : Machine (Fin 2) (Fin 4) := fun q a =>
  let k := digit z q a
  if k=16 then none else some (some (Fin.ofNat 4 (k/4)),
    .write (Fin.ofNat 2 (k/2)) (if k%2=0 then .left else .right))

private def marked {n : ℕ} (mask : ℕ) (q : Fin 4) (a : Fin 2) (l r : Fin n) :=
  mask.testBit (((2*q.val+a.val)*n+l.val)*n+r.val)

private def checked {n : ℕ} (z : ℕ) (D : Fin 2 → Fin n → Fin n) (mask : ℕ)
    (q : Fin 4) (a s t : Fin 2) (l r : Fin n) : Bool :=
  if marked mask q a (D s l) (D t r) then
    let k := digit z q a
    let p := Fin.ofNat 4 (k/4)
    let w := Fin.ofNat 2 (k/2)
    k != 16 && (if k%2=0 then marked mask p s l (D w (D t r))
      else marked mask p t (D w (D s l)) r)
  else true

private theorem sound {n : ℕ} [NeZero n] (z : ℕ) (D : Fin 2 → Fin n → Fin n) (mask : ℕ)
    (blank : D 0 0=0) (start : marked (n := n) mask 0 0 0 0=true)
    (ok : ∀ q a s t l r, checked z D mask q a s t l r=true) : ¬ (table z).IsHalting := by
  apply OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1.certified (table z) (0 : Fin n) (0 : Fin n) D D (marked mask) blank blank start
  intro q a s t l r h
  have good := ok q a s t l r
  simp only [checked,h,if_true,Bool.and_eq_true,bne_iff_ne] at good
  let k := digit z q a
  refine ⟨Fin.ofNat 4 (k/4),Fin.ofNat 2 (k/2),(if k%2=0 then .left else .right),?_,?_⟩
  · exact if_neg good.1
  · by_cases e : digit z q a % 2 = 0
    · simpa only [k,if_pos e] using good.2
    · simpa only [k,if_neg e] using good.2

private def scan14 (a : Fin 2) (i : Fin 14) : Fin 14 :=
  Fin.ofNat 14 (((1873377558468118847585242158739984 : ℕ) >>> (4*(2*i.val+a.val))) % 16)

private theorem safe1790187557 : ¬ (table 1790187557).IsHalting := by
  apply sound 1790187557 scan14 1292992344039040663581825669380677428862516886076166368833062707913438795804819422060351654864622813901383744907134647117738760652368450202713980118045573810919358692175211670804142197145353165750674788218436005967610690003448849943881684134525952212810992846511105228513988365228258415229291740831318746226464988253230023536669142228487209163204593887332180449409254645172508715645118390423070954058890241569836413053470397248574324663829565903410982551553 (by decide +kernel) (by decide +kernel)
  decide +kernel

private def scan4 (a : Fin 2) (i : Fin 4) : Fin 4 :=
  Fin.ofNat 4 (((304230928 : ℕ) >>> (4*(2*i.val+a.val))) % 16)

private theorem safe6207529726 : ¬ (table 6207529726).IsHalting := by
  apply sound 6207529726 scan4 191574986160306418620838945167226568705 (by decide +kernel) (by decide +kernel)
  decide +kernel

private theorem safe6221728296 : ¬ (table 6221728296).IsHalting := by
  apply sound 6221728296 scan14 4246557200659462318499547521705344654462686545268162046028628710771374046862370178705737582632845490955744853538906821520164651179481792970576458483351660477418934405225967798961041848900712841960810774447501913366043856220125550030855710559448493911569286349218245315433835523793533134669034143392865866910969057843489322278277322403076126740524551216673915634713353226284865379241767237441130393955633298961358328219786143093401125292523651073 (by decide +kernel) (by decide +kernel)
  decide +kernel

private theorem safe6810924734 : ¬ (table 6810924734).IsHalting := by
  apply sound 6810924734 scan4 1277556613962400699678013259785 (by decide +kernel) (by decide +kernel)
  decide +kernel

theorem all_four : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1.H2 := by
  intro z hz
  change z ∈ ([1790187557,6207529726,6221728296,6810924734] : List ℕ) at hz
  change ¬ (table z).IsHalting
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact safe1790187557
  · exact safe6207529726
  · exact safe6221728296
  · exact safe6810924734

end OMA.BB4FourReaders

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1.H2 := OMA.BB4FourReaders.all_four
