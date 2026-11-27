import OMAReductions.R_Erdos556_erdos_556_variants_luczak_asymptotic_R1
import Mathlib

/- Reversible helper-name map SHA256: 8e3790ad740a0f33a119eab17b8f094d25040e3fc364694c0cb476eeb5245ad1.
The full alias-to-original JSON map accompanies this submission. -/
/-!
# Upper bound for sufficiently large odd cycles
Credit: Hanan Beer (@hananzlt), verification, compatibility, exact statement
bridge and integration. The mathematical formalization is reused from
plby/lean-proofs, pinned commit8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
All original author and license notices are retained in their source modules.
In particular, the Bondy-Chvatal development credits Shuhao Song and its
original Mathlib pull-request source; Menger credits the Lean-Proofs Authors.
The mathematical result is due to Kohayakawa, Simonovits and Skokan.
This submits only the odd-cycle upper-bound input H2 of the Łuczak reduction.
The same checked infrastructure also supplies the sharp odd-cycle result.
No claim to a new mathematical discovery is made.
-/
section dX
namespace Erdos556
open SimpleGraph
open scoped SimpleGraph
structure q4 (V:Type*) where
  colour:V → V → Fin 3
  symm: ∀ u v,colour u v=colour v u
def q4.graph {V:Type*} (c:q4 V) (i:Fin 3) :
    SimpleGraph V where
  Adj u v:=u ≠ v ∧ c.colour u v=i
  symm:= ⟨by
    intro u v h
    exact ⟨h.1.symm,(c.symm v u).trans h.2⟩⟩
  loopless:= ⟨by simp⟩
@[simp] theorem q4.e4 {V:Type*} (c:q4 V)
    (i:Fin 3) (u v :V) :
    (c.graph i).Adj u v ↔ u ≠ v ∧ c.colour u v=i:=Iff.rfl
def q4.comap {V W :Type*} (c:q4 V) (f:W → V) :
    q4 W where
  colour u v:=c.colour (f u) (f v)
  symm u v:=c.symm (f u) (f v)
theorem q4.tY {V W :Type*} (c:q4 V)
    (f:W ↪ V) (i:Fin 3) :
    (c.comap f).graph i = (c.graph i).comap f :=by
  ext u v
  simp only [e4,comap,SimpleGraph.comap_adj]
  exact and_congr_left fun _ => f.injective.ne_iff.symm
def rr (n m :ℕ) : Prop:=
  ∀ c :q4 (Fin m),∃ i:Fin 3,cycleGraph n ⊑ c.graph i
noncomputable def sS (n:ℕ) : ℕ:=
  sInf {m:ℕ | rr n m}
theorem rr.mono {n a b:ℕ} (h:rr n a) (hab:a ≤ b) :
    rr n b:=by
  intro c
  let f :Fin a ↪ Fin b :=Fin.castLEEmb hab
  obtain ⟨i,hi⟩ :=h (c.comap f)
  refine ⟨i,?_⟩
  rw [c.tY f i] at hi
  exact hi.trans (SimpleGraph.Embedding.comap f (c.graph i)).isContained
theorem rr.of_equiv {n m :ℕ} {V:Type*}
    (h:rr n m) (e:Fin m ≃ V) (c:q4 V) :
    ∃ i :Fin 3,cycleGraph n ⊑ c.graph i :=by
  obtain ⟨i,hi⟩ :=h (c.comap e.toEmbedding)
  refine ⟨i,?_⟩
  rw [c.tY e.toEmbedding i] at hi
  exact hi.trans (SimpleGraph.Embedding.comap e.toEmbedding (c.graph i)).isContained
end Erdos556
end dX
section e0
/-
# Qualitative finite Ramsey existence
The elementary two-colour induction is adapted from the existing proved
development in `Util/Ramsey.lean). Its dependencies are kept here so that
the #556 development is self-contained apart from Mathlib.
-/
namespace Erdos556.TwoColour
open Finset
open scoped SimpleGraph
theorem wN {V W :Type*} {G:SimpleGraph V}
    {H:SimpleGraph W} {n:ℕ} (f:H ↪g G) :
    G.IndepSetFree n → H.IndepSetFree n :=by
  intro h
  rw [← SimpleGraph.cliqueFree_compl] at h ⊢
  exact h.comap
    (((SimpleGraph.Embedding.complEquiv (G:=H) (H:=G)).toFun f).isContained)
def us (k l m:ℕ) : Prop:=
  ∀ G :SimpleGraph (Fin m),¬ (G.CliqueFree k ∧ G.IndepSetFree l)
theorem xi {k l m:ℕ} {V:Type*} [Fintype V]
    (hcard:Fintype.card V =m) (h:us k l m)
    (G:SimpleGraph V) : ¬ (G.CliqueFree k ∧ G.IndepSetFree l) :=by
  classical
  intro hbad
  let e :Fin m ≃ V :=Fintype.equivOfCardEq (by simpa using hcard.symm)
  let f :Fin m ↪ V :=e.toEmbedding
  exact h (G.comap f) ⟨hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained,
    wN (SimpleGraph.Embedding.comap f G) hbad.2⟩
theorem zy {k l a b :ℕ} (hab:a ≤ b)
    (h:us k l a) : us k l b :=by
  intro G hbad
  let f :Fin a ↪ Fin b :=Fin.castLEEmb hab
  exact h (G.comap f) ⟨hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained,
    wN (SimpleGraph.Embedding.comap f G) hbad.2⟩
theorem xI (k l :ℕ) : ∃ n,us k l n :=by
  revert l
  induction k with
  | zero=>
      intro l
      refine ⟨0,?_⟩
      intro G hbad
      simpa using hbad.1
  | succ k ih=>
      intro l
      induction l with
      | zero=>
          refine ⟨0,?_⟩
          intro G hbad
          exact hbad.2 ∅ (by simp [SimpleGraph.isNIndepSet_iff])
      | succ l ihl=>
          rcases ih (l+1) with ⟨m,hm⟩
          rcases ihl with ⟨n,hn⟩
          refine ⟨m+n+1,?_⟩
          intro G hbad
          classical
          let v :Fin (m+n+1) :=0
          by_cases hdeg:m ≤ G.degree v
          · let H :SimpleGraph (G.neighborSet v) :=G.induce (G.neighborSet v)
            have hprop:us k (l+1) (G.degree v) :=zy hdeg hm
            have hcf:H.CliqueFree k :=by
              intro t ht
              let t':Finset (Fin (m+n+1)) :=
                Finset.map ⟨Subtype.val,Subtype.val_injective⟩ t
              have htInd:
                  (((⊤ : SimpleGraph.Subgraph G).induce (G.neighborSet v)).coe).IsNClique k t:=by
                rw [← SimpleGraph.induce_eq_coe_induce_top]
                exact ht
              have ht':G.IsNClique k t':=by
                simpa [H,t'] using
                  (SimpleGraph.IsNClique.of_induce
                    (S:= (⊤ : SimpleGraph.Subgraph G)) (F:=G.neighborSet v) (cc:=htInd))
              have hvt: ∀ b ∈ t',G.Adj v b:=by
                intro b hb
                rcases Finset.mem_map.mp hb with ⟨x,hx,rfl⟩
                exact x.property
              exact hbad.1 _ (ht'.insert hvt)
            have hif:H.IndepSetFree (l+1) :=by
              exact wN
                (SimpleGraph.Embedding.induce (G:=G) (s:=G.neighborSet v)) hbad.2
            exact xi (G.card_neighborSet_eq_degree v) hprop H ⟨hcf,hif⟩
          · let H :SimpleGraph (Gᶜ.neighborSet v) :=G.induce (Gᶜ.neighborSet v)
            have hcompdeg:n ≤ Gᶜ.degree v :=by
              rw [G.degree_compl (v:=v),Fintype.card_fin]
              omega
            have hprop:us (k+1) l (Gᶜ.degree v) :=
              zy hcompdeg hn
            have hcf:H.CliqueFree (k+1) :=by
              exact hbad.1.comap
                (SimpleGraph.Embedding.induce (G:=G) (s:=Gᶜ.neighborSet v)).isContained
            have hif:H.IndepSetFree l :=by
              intro t ht
              let t':Finset (Fin (m+n+1)) :=
                Finset.map ⟨Subtype.val,Subtype.val_injective⟩ t
              have htInd:
                  (((⊤ : SimpleGraph.Subgraph G).induce
                    (Gᶜ.neighborSet v)).coe).IsNIndepSet l t:=by
                rw [← SimpleGraph.induce_eq_coe_induce_top]
                exact ht
              have ht':G.IsNIndepSet l t':=by
                simpa [H,t'] using
                  (SimpleGraph.isNIndepSet_induce
                    (G:=G) (F:=Gᶜ.neighborSet v) (s:=t) (n:=l)).1 htInd
              have ht'compl:Gᶜ.IsNClique l t':=by
                simpa using ht'
              have hvt: ∀ b ∈ t',Gᶜ.Adj v b:=by
                intro b hb
                rcases Finset.mem_map.mp hb with ⟨x,hx,rfl⟩
                exact x.property
              have ht'':G.IsNIndepSet (l+1) (insert v t') :=by
                simpa using ht'compl.insert hvt
              exact hbad.2 _ ht''
            exact xi (Gᶜ.card_neighborSet_eq_degree v) hprop H ⟨hcf,hif⟩
end Erdos556.TwoColour
namespace Erdos556
open SimpleGraph
open scoped SimpleGraph
theorem ug {V:Type*} {G:SimpleGraph V} {n:ℕ}
    (h: ¬ G.CliqueFree n) : cycleGraph n ⊑ G :=by
  have htop:cycleGraph n ⊑ completeGraph (Fin n) :=IsContained.of_le le_top
  exact htop.trans ((G.not_cliqueFree_iff_top_isContained n).mp h)
theorem q4.tR {V W :Type*} (c:q4 V)
    (f:W ↪ V) {n:ℕ} {i:Fin 3}
    (h:cycleGraph n ⊑ (c.comap f).graph i) : cycleGraph n ⊑ c.graph i :=by
  rw [c.tY f i] at h
  exact h.trans (SimpleGraph.Embedding.comap f (c.graph i)).isContained
theorem a2 (n:ℕ) : ∃ m,rr n m:=by
  classical
  obtain ⟨m,hm⟩ :=TwoColour.xI n n
  obtain ⟨N,hN⟩ :=TwoColour.xI n m
  refine ⟨N,?_⟩
  intro c
  by_cases hred: (c.graph 0).CliqueFree n
  · have hnind: ¬ (c.graph 0).IndepSetFree m :=fun hi=> hN _ ⟨hred,hi⟩
    have hncompl: ¬ (c.graph 0)ᶜ.CliqueFree m :=by
      simpa only [cliqueFree_compl] using hnind
    let e := (c.graph 0)ᶜ.topEmbeddingOfNotCliqueFree hncompl
    let f :Fin m ↪ Fin N := ⟨e,e.injective⟩
    let d :=c.comap f
    have hzero {u v :Fin m} (huv:u ≠ v) : d.colour u v ≠ 0:=by
      intro hc
      have he:=e.map_rel_iff.mpr huv
      exact he.2 ⟨f.injective.ne huv,hc⟩
    have hcomp: (d.graph 1)ᶜ ≤ d.graph 2 :=by
      intro u v h
      have huv:u ≠ v:=h.1
      have h0:=hzero huv
      have h1:d.colour u v ≠ 1:=fun h1=> h.2 ⟨huv,h1⟩
      refine ⟨huv,?_⟩
      have hc:= (d.colour u v).isLt
      apply Fin.ext
      have h0v: (d.colour u v).val ≠ 0:=by
        intro hval
        exact h0 (Fin.ext hval)
      have h1v: (d.colour u v).val ≠ 1:=by
        intro hval
        exact h1 (Fin.ext hval)
      omega
    by_cases hblue: (d.graph 1).CliqueFree n
    · have hni: ¬ (d.graph 1).IndepSetFree n :=fun hi=> hm _ ⟨hblue,hi⟩
      have hnc: ¬ (d.graph 1)ᶜ.CliqueFree n :=by
        simpa only [cliqueFree_compl] using hni
      have hcycle:cycleGraph n ⊑ d.graph 2 :=
        (ug hnc).mono_right hcomp
      exact ⟨2,c.tR f hcycle⟩
    · exact ⟨1,c.tR f (ug hblue)⟩
  · exact ⟨0,ug hred⟩
end Erdos556
end e0
section dW
namespace Erdos556
open SimpleGraph
open scoped SimpleGraph
abbrev uD (n:ℕ) :=Bool × Bool × Fin (n-1)
def sv (n:ℕ) : q4 (uD n) where
  colour x y:=if x.1 ≠ y.1 then 0 else if x.2.1 ≠ y.2.1 then 1 else 2
  symm x y:=by simp only [ne_comm]
theorem a6 {n:ℕ} {x y :uD n}
    (h: ((sv n).graph 0).Adj x y) : x.1 ≠ y.1:=by
  have hc:=h.2
  change (if x.1 ≠ y.1 then (0:Fin 3) else
    if x.2.1 ≠ y.2.1 then 1 else 2) = 0 at hc
  split_ifs at hc <;> simp_all
theorem ao {n:ℕ} {x y :uD n}
    (h: ((sv n).graph 1).Adj x y) : x.2.1 ≠ y.2.1:=by
  have hc:=h.2
  change (if x.1 ≠ y.1 then (0:Fin 3) else
    if x.2.1 ≠ y.2.1 then 1 else 2) = 1 at hc
  split_ifs at hc <;> simp_all
theorem aw {n:ℕ} {x y :uD n}
    (h: ((sv n).graph 2).Adj x y) :
    (x.1,x.2.1) = (y.1,y.2.1) :=by
  have hc:=h.2
  change (if x.1 ≠ y.1 then (0:Fin 3) else
    if x.2.1 ≠ y.2.1 then 1 else 2) = 2 at hc
  split_ifs at hc <;> simp_all
theorem wb {V:Type*} {G:SimpleGraph V}
    (b:G.Coloring Bool) {n:ℕ} (hn:2 < n) (ho:Odd n) :
    ¬ cycleGraph n ⊑ G :=by
  intro h
  obtain ⟨v,p,_,hp⟩ := (cycleGraph_isContained_iff hn).mp h
  have he:Even p.length:= (b.even_length_iff_congr p).mpr Iff.rfl
  rw [hp] at he
  exact (Nat.not_even_iff_odd.mpr ho) he
theorem aN {V W :Type*} {G:SimpleGraph V}
    (label:V → W) (hlabel: ∀ {u v},G.Adj u v → label u =label v)
    {u v :V} (p:G.Walk u v) : label u =label v :=by
  induction p with
  | nil=> rfl
  | cons h p ih=> exact (hlabel h).trans ih
theorem t3 (n:ℕ) (hn:2 < n) (ho:Odd n)
    (i:Fin 3) : ¬ cycleGraph n ⊑ (sv n).graph i :=by
  fin_cases i
  · let b : ((sv n).graph 0).Coloring Bool:=
      { toFun:=fun x => x.1
        map_rel':=by
          intro x y h
          exact a6 h }
    exact wb b hn ho
  · let b : ((sv n).graph 1).Coloring Bool:=
      { toFun:=fun x => x.2.1
        map_rel':=by
          intro x y h
          exact ao h }
    exact wb b hn ho
  · rintro ⟨f⟩
    have hlabel (u v :Fin n) :
        ((f u).1,(f u).2.1) = ((f v).1,(f v).2.1) :=by
      obtain ⟨p⟩ :=cycleGraph_preconnected u v
      exact aN (fun x :uD n => (x.1,x.2.1))
        (fun h => aw h) (p.map f.toHom)
    have hinj:Function.Injective (fun u :Fin n => (f u).2.2) :=by
      intro u v huv
      apply f.injective
      have h :=hlabel u v
      apply Prod.ext
      · exact congrArg (fun z :Bool × Bool=> z.1) h
      · exact Prod.ext (congrArg (fun z :Bool × Bool=> z.2) h) huv
    have hc:=Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at hc
    omega
theorem aJ (n:ℕ) :
    Fintype.card (uD n) = 4*n-4:=by
  simp only [uD,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  omega
theorem wc (n:ℕ) (hn:2 < n) (ho:Odd n) :
    ¬ rr n (4*n-4) :=by
  intro h
  let e :Fin (4*n-4) ≃ uD n :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_fin,aJ])
  obtain ⟨i,hi⟩ :=h.of_equiv e (sv n)
  exact t3 n hn ho i hi
end Erdos556
end dW
section dT
namespace Erdos556
theorem az (n:ℕ) : rr n (sS n) :=by
  exact csInf_mem (a2 n)
theorem xk {n m :ℕ} (h:rr n m) :
    sS n ≤ m :=by
  exact csInf_le (OrderBot.bddBelow _) h
theorem wB (n:ℕ) (hn:2 < n) (ho:Odd n) :
    4*n-3 ≤ sS n :=by
  by_contra h
  have hsmall:sS n ≤ 4 *n-4:=by omega
  exact wc n hn ho
    ((az n).mono hsmall)
end Erdos556
end dT
section dR
namespace Erdos556
open Finset
abbrev wz:=Fin 3 → Bool
abbrev q1:=Fin 3 → Option Bool
def q0 (p:q1) : Finset wz:=
  univ.filter (fun v => ∀ i,p i=none ∨ p i =some (v i))
def q3 (p:q1) : ℕ:=
  (univ.filter (fun i => p i=none)).card
def cubeFace (i:Fin 3) (b:Bool) : q1:=
  fun j => if j =i then some b else none
def qF:q1:=fun _ => none
theorem sM (p:q1) : q3 p ≤ 3 :=by
  have h :=card_le_univ (univ.filter (fun i :Fin 3 => p i=none))
  simpa only [q3,Fintype.card_fin] using h
theorem qU: ∀ p:q1,
    (q0 p).card=2^q3 p :=by
  decide
theorem r4: ∀ (i:Fin 3) (b:Bool),q3 (cubeFace i b) = 2:=by
  decide
theorem zx:q3 qF=3:=by decide
theorem sz: ∀ p:q1,
    q3 p =3 ↔ p=qF:=by
  decide
theorem u1: ∀ p:q1,
    q3 p =2 ↔ ∃ (i:Fin 3) (b:Bool),p=cubeFace i b:=by
  decide
end Erdos556
end dR
section e2
namespace Erdos556
theorem ru: ∀ p q:q1,
    q3 p =1 → q3 q =1 → p ≠ q →
    ((q0 p) ∩ (q0 q)).card ≠ 1 →
    Disjoint (q0 p) (q0 q) :=by
  decide
theorem ui: ∀ (i j :Fin 3) (b c :Bool),
    Disjoint (q0 (cubeFace i b)) (q0 (cubeFace j c)) ↔
      i=j ∧ b ≠ c:=by
  decide
end Erdos556
end e2
section dQ
namespace Erdos556
open Finset
structure q6 (w:q1 → ℝ) : Prop where
  nonneg: ∀ p,0 ≤ w p
  sum_four: ∑ p,w p=4
  vertex_zero: ∀ p,q3 p =0 → w p=0
  edge_le_one: ∀ p,q3 p =1 → w p ≤ 1
  compatible: ∀ p q,0 < w p → 0 < w q →
    (q0 p ∩ q0 q).card ≠ 1
def qb (p q :q1) : ℝ:=
  if Disjoint (q0 p) (q0 q) then 0 else 1
def qd (w:q1 → ℝ) : ℝ:=
  (∑ p,∑ q,qb p q*w p*w q) - ∑ p,(q3 p :ℝ) * w p
def qm (w:q1 → ℝ) (p:q1) : ℝ:=
  2* (∑ q,qb p q*w q) - q3 p
theorem sm (p q :q1) : qb p q=qb q p:=by
  simp only [qb,disjoint_comm]
theorem vU (p:q1) : qb p p=1:=by
  have hcard:0 < (q0 p).card:=by rw [qU];positivity
  have hne: ¬ Disjoint (q0 p) (q0 p) :=by
    simpa only [disjoint_self,Finset.bot_eq_empty,← card_eq_zero] using Nat.ne_of_gt hcard
  simp only [qb,if_neg hne]
theorem vh (E:Finset q1) (S:Finset wz)
    (hdim: ∀ p ∈ E,q3 p =1)
    (hdisj: (E:Set q1).Pairwise (fun p q=> Disjoint (q0 p)
      (q0 q)))
    (hsub: ∀ p ∈ E,q0 p ⊆ S) : 2*E.card ≤ S.card:=by
  have hsum: (∑ p ∈ E,(q0 p).card) = 2*E.card:=by
    calc
      (∑ p ∈ E,(q0 p).card) = ∑ _p ∈ E,2:=by
        apply sum_congr rfl
        intro p hp
        rw [qU,hdim p hp]
        norm_num
      _=2*E.card:=by simp [Nat.mul_comm]
  rw [← hsum,← card_biUnion hdisj]
  apply card_le_card
  intro v hv
  obtain ⟨p,hp,hvp⟩ :=mem_biUnion.mp hv
  exact hsub p hp hvp
open scoped Classical in
noncomputable def ql (w:q1 → ℝ) : Finset q1:=
  univ.filter (fun p => q3 p =1 ∧ 0 < w p)
theorem q6.s0 {w:q1 → ℝ} (hw:q6 w) :
    (ql w :Set q1).Pairwise
      (fun p q=> Disjoint (q0 p) (q0 q)) :=by
  intro p hp q hq hpq
  obtain ⟨_,hpdim,hpw⟩ :=mem_filter.mp hp
  obtain ⟨_,hqdim,hqw⟩ :=mem_filter.mp hq
  exact ru p q hpdim hqdim hpq (hw.compatible p q hpw hqw)
theorem q6.vl {w:q1 → ℝ} (hw:q6 w) :
    (ql w).card ≤ 4:=by
  have h :=vh (ql w) univ
    (fun p hp=> (mem_filter.mp hp).2.1) hw.s0 (fun _ _=> subset_univ _)
  have hcard: (univ:Finset wz).card=8:=by decide
  rw [hcard] at h
  omega
end Erdos556
end dQ
section dO
namespace Erdos556
open Finset
theorem vn {V P R:Type*} [Fintype V] [Fintype P] [DecidableEq P]
    [Semiring R] (label:V → P) (f:P → R) :
    (∑ v,f (label v)) = ∑ p,((univ.filter (fun v => label v =p)).card:R) * f p :=by
  classical
  have h :=sum_fiberwise' (univ:Finset V) label f
  simpa only [sum_const,nsmul_eq_mul] using h.symm
theorem aE {V P :Type*} [Fintype V] [Fintype P] [DecidableEq P]
    (label:V → P) : (∑ p,(univ.filter (fun v => label v =p)).card) = Fintype.card V :=by
  simpa using (vn label (fun _ => (1:ℕ))).symm
theorem yG {V P R:Type*} [Fintype V] [Fintype P] [DecidableEq P]
    [Semiring R] (label:V → P) (f:P → P → R) :
    (∑ u,∑ v,f (label u) (label v)) =
      ∑ p,∑ q,((univ.filter (fun v => label v =p)).card:R) *
        ((univ.filter (fun v => label v =q)).card:R) * f p q:=by
  classical
  calc
    _= ∑ u,∑ q,((univ.filter (fun v => label v =q)).card:R) * f (label u) q :=by
      apply sum_congr rfl
      intro u _
      exact vn label (f (label u))
    _= ∑ p,((univ.filter (fun v => label v =p)).card:R) *
        (∑ q,((univ.filter (fun v => label v =q)).card:R) * f p q) :=
      vn label (fun p => ∑ q,((univ.filter (fun v => label v =q)).card:R) * f
        p q)
    _=_:=by simp only [mul_sum,mul_assoc]
end Erdos556
end dO
section dV
namespace Erdos556
open SimpleGraph Finset
theorem q7 {V:Type*} (G:SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeFinset.card=Nat.card G.edgeSet:=
  G.card_edgeSet.symm.trans Nat.card_eq_fintype_card.symm
theorem tf {V W :Type*} [Fintype V]
    [DecidableEq W] (G:SimpleGraph V) [DecidableRel G.Adj]
    (f:V ↪ W) (A:Finset W) :
    ((G.map f).induce (A:Set W)).edgeFinset.card=
      (G.induce ((univ.filter (fun v => f v ∈ A) : Finset V) : Set V)).edgeFinset.card:=by
  classical
  let B :=univ.filter (fun v :V=> f v ∈ A)
  let g : (B:Set V) ↪ (A:Set W) :=
    { toFun:=fun v => ⟨f v.val,(mem_filter.mp v.property).2⟩
      inj':=fun u v h => Subtype.ext (f.injective (congrArg Subtype.val h))}
  have e : (G.map f).induce (A:Set W) ≃g (G.induce (B:Set V)).map g :=
    { toEquiv:=Equiv.refl _
      map_rel_iff':=by
        intro u v
        constructor
        · rintro ⟨hne,a,b,hab,ha,hb⟩
          change (G.map f).Adj u.val v.val
          refine ⟨fun h => hne (Subtype.ext h),a.val,b.val,hab,?_,?_⟩
          · exact congrArg Subtype.val ha
          · exact congrArg Subtype.val hb
        · intro huv
          change (G.map f).Adj u.val v.val at huv
          obtain ⟨hne,a,b,hab,ha,hb⟩ :=huv
          have haB:a ∈ B:=mem_filter.mpr ⟨mem_univ _,ha ▸ u.property⟩
          have hbB:b ∈ B:=mem_filter.mpr ⟨mem_univ _,hb ▸ v.property⟩
          refine ⟨fun h => hne (congrArg Subtype.val h),⟨a,haB⟩,⟨b,hbB⟩,hab,?_,?_⟩
          · exact Subtype.ext ha
          · exact Subtype.ext hb}
  exact e.card_edgeFinset_eq.trans (card_edgeFinset_map g (G.induce (B:Set V)))
theorem t1 {V W :Type*} [Fintype V]
    [DecidableEq W] (f:V ↪ W) (A:Finset W) :
    (univ.filter (fun v => f v ∈ A)).card ≤ A.card:=by
  classical
  let B :=univ.filter (fun v :V=> f v ∈ A)
  let g : (B:Set V) ↪ (A:Set W) :=
    { toFun:=fun v => ⟨f v.val,(mem_filter.mp v.property).2⟩
      inj':=fun u v h => Subtype.ext (f.injective (congrArg Subtype.val h))}
  have h :=Fintype.card_le_of_injective g g.injective
  have hcardB:Fintype.card (B:Set V) = B.card:=by
    calc
      Fintype.card (B:Set V) = (B:Set V).ncard:=Nat.card_eq_fintype_card.symm
      _=B.card:=Set.ncard_coe_finset B
  have hcardA:Fintype.card (A:Set W) = A.card:=by
    calc
      Fintype.card (A:Set W) = (A:Set W).ncard:=Nat.card_eq_fintype_card.symm
      _=A.card:=Set.ncard_coe_finset A
  rw [hcardB,hcardA] at h
  exact h
theorem x2 {V W :Type*} [Fintype V]
    [DecidableEq W] (G:SimpleGraph V) [DecidableRel G.Adj]
    (f:V ↪ W) (D:ℝ) (hD:0 ≤ D)
    (h: ∀ S:Finset V,((G.induce (S:Set V)).edgeFinset.card:ℝ) ≤ D*S.card) :
    ∀ A :Finset W,(((G.map f).induce (A:Set W)).edgeFinset.card:ℝ) ≤ D*A.card:=by
  classical
  intro A
  rw [tf G f A]
  apply (h _).trans
  apply mul_le_mul_of_nonneg_left _ hD
  exact_mod_cast t1 f A
theorem ac {V W :Type*}
    (G:SimpleGraph V) (f:V ↪ W) (S:Finset V)
    (h: ∀ a b,G.Adj a b → a ∈ S ∧ b ∈ S) :
    ∀ a b,(G.map f).Adj a b → a ∈ S.map f ∧ b ∈ S.map f :=by
  classical
  rintro a b ⟨_,u,v,huv,rfl,rfl⟩
  exact ⟨mem_map.mpr ⟨u,(h u v huv).1,rfl⟩,mem_map.mpr ⟨v,(h u v huv).2,rfl⟩⟩
theorem tW {V W :Type*}
    (G:SimpleGraph V) (f:V ↪ W) (S:Finset V)
    (h: ∀ a b,G.Adj a b → a ∉ S ∧ b ∉ S) :
    ∀ a b,(G.map f).Adj a b → a ∉ S.map f ∧ b ∉ S.map f :=by
  classical
  rintro a b ⟨_,u,v,huv,rfl,rfl⟩
  have hoff (x:V) (hx:x ∉ S) : f x ∉ S.map f :=by
    intro hxmem
    obtain ⟨y,hy,hyx⟩ :=mem_map.mp hxmem
    exact hx ((f.injective hyx) ▸ hy)
  exact ⟨hoff u (h u v huv).1,hoff v (h u v huv).2⟩
end Erdos556
end dV
section cG
namespace Erdos556
open SimpleGraph Finset
def qJ {V:Type*} (label:V → q1) : SimpleGraph V where
  Adj u v:=Disjoint (q0 (label u)) (q0 (label v))
  symm:= ⟨fun _ _ h => h.symm⟩
  loopless:= ⟨by
    intro v h
    have he:q0 (label v) = ∅ :=by
      simpa only [disjoint_self,Finset.bot_eq_empty] using h
    have hp:0 < (q0 (label v)).card:=by rw [qU];positivity
    rw [he,card_empty] at hp
    omega⟩
def qO (w:q1 → ℝ) : ℝ:=
  ∑ p,∑ q,if Disjoint (q0 p) (q0 q) then w p*w q else 0
theorem sb {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] :
    2* (Nat.card G.edgeSet:ℝ) = ∑ u,∑ v,if G.Adj u v then (1:ℝ) else 0 :=by
  classical
  have hdegree (u:V) : G.degree u = ∑ v,if G.Adj u v then (1:ℕ) else 0 :=by
    rw [sum_boole,← card_neighborFinset_eq_degree]
    congr 1
    ext v
    simp
  have h :=G.sum_degrees_eq_twice_card_edges
  simp only [hdegree,q7] at h
  exact_mod_cast h.symm
theorem sY {V:Type*} [Fintype V]
    (label:V → q1) :
    2* (Nat.card (qJ label).edgeSet:ℝ) =
      qO (fun p => ((univ.filter (fun v => label v =p)).card:ℝ)) :=by
  classical
  rw [sb]
  have hadj: (∑ u,∑ v,if (qJ label).Adj u v then (1:ℝ) else 0) =
      ∑ u,∑ v,if Disjoint (q0 (label u)) (q0 (label v)) then (1:ℝ)
        else 0 :=by
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    by_cases h :Disjoint (q0 (label u)) (q0 (label v)) <;>
      simp [qJ,h]
  rw [hadj]
  rw [yG label (fun p q=>
    if Disjoint (q0 p) (q0 q) then (1:ℝ) else 0)]
  unfold qO
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  split_ifs <;> simp
theorem zv (w:q1 → ℝ) :
    qd w = (∑ p,w p) ^ 2-qO w -
      ∑ p,(q3 p :ℝ) * w p :=by
  have h : (∑ p,∑ q,qb p q*w p*w q) + qO w = (∑ p,w p) ^ 2:=by
    calc
      _= ∑ p,∑ q,(qb p q*w p*w q+
          if Disjoint (q0 p) (q0 q) then w p*w q else 0) :=by
        simp only [qO,sum_add_distrib]
      _= ∑ p,∑ q,w p*w q:=by
        apply sum_congr rfl
        intro p _
        apply sum_congr rfl
        intro q _
        unfold qb
        split_ifs <;> simp
      _=_:=by
        simp only [pow_two,sum_mul,mul_sum]
        exact sum_comm
  unfold qd
  linarith
end Erdos556
end cG
section cH
namespace Erdos556
open SimpleGraph
theorem rq {V:Type*} {G:SimpleGraph V}
    {u v :V} (p:G.Walk u v) (hp:p.IsPath) (S:Set V) (hv:v ∈ S) :
    ∃ w ∈ S,∃ q:G.Walk u w,q.IsPath ∧ q.length ≤ p.length ∧
      q.support ⊆ p.support ∧ ∀ x ∈ q.support,x ∈ S → x=w:=by
  classical
  let P (m:ℕ) : Prop:= ∃ w ∈ S,∃ q:G.Walk u w,
    q.IsPath ∧ q.support ⊆ p.support ∧ q.length=m
  have hex: ∃ m,P m:= ⟨p.length,v,hv,p,hp,List.Subset.refl _,rfl⟩
  obtain ⟨w,hw,q,hq,hsub,hlen⟩ :=Nat.find_spec hex
  have hmin {z:V} (hz:z ∈ S) (r:G.Walk u z) (hr:r.IsPath)
      (hrs:r.support ⊆ p.support) : q.length ≤ r.length:=by
    rw [hlen]
    exact Nat.find_min' hex ⟨z,hz,r,hr,hrs,rfl⟩
  refine ⟨w,hw,q,hq,hmin hv p hp (List.Subset.refl _),hsub,?_⟩
  intro x hx hxS
  by_contra hxw
  have hlt:=q.length_takeUntil_lt_length hx hxw
  have hle:=hmin hxS (q.takeUntil x hx) (hq.takeUntil hx)
    (fun _ hz=> hsub (q.support_takeUntil_subset_support hx hz))
  omega
theorem qr {V:Type*} {G:SimpleGraph V}
    {u v w:V} (p:G.Walk u v) (q:G.Walk v w)
    (hp:p.IsPath) (hq:q.IsPath)
    (hinter: ∀ x ∈ p.support,x ∈ q.support → x=v) :
    (p.append q).IsPath:=by
  induction p with
  | nil=> simpa using hq
  | @cons u z v huz p ih=>
      have hp':=hp.of_cons
      have hu:u ∉ p.support:= (Walk.cons_isPath_iff huz p).mp hp |>.2
      have huv:u ≠ v:=fun h => hu (h ▸ p.end_mem_support)
      have huq:u ∉ q.support:=fun h => huv (hinter u (by simp) h)
      have hi: ∀ x ∈ p.support,x ∈ q.support → x=v:=
        fun x hx hxq=> hinter x (by simp [hx]) hxq
      exact (ih q hp' hq hi).cons (by
        intro hx
        rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
        · exact hu hx
        · exact huq hx)
end Erdos556
end cH
section dD
namespace Erdos556
open SimpleGraph
theorem qz {V:Type*} {G:SimpleGraph V} {u v x:V}
    (p:G.Walk u v) (i:ℕ) (hi:i ≤ p.length) :
    x ∈ (p.take i).support ↔ ∃ j,j ≤ i ∧ p.getVert j =x:=by
  constructor
  · intro hx
    obtain ⟨j,hjx,hj⟩ :=Walk.mem_support_iff_exists_getVert.mp hx
    have hj':j ≤ i:=by simpa only [Walk.take_length,min_eq_left hi] using hj
    refine ⟨j,hj',?_⟩
    simpa only [Walk.take_getVert,inf_eq_right.mpr hj'] using hjx
  · rintro ⟨j,hj,hjx⟩
    apply Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨j,?_,?_⟩
    · simpa only [Walk.take_getVert,inf_eq_right.mpr hj] using hjx
    · simpa only [Walk.take_length,min_eq_left hi] using hj
theorem rd {V:Type*} {G:SimpleGraph V} {u v x:V}
    (p:G.Walk u v) (i:ℕ) (hi:i ≤ p.length) :
    x ∈ (p.drop i).support ↔ ∃ j,i ≤ j ∧ j ≤ p.length ∧ p.getVert j =x:=by
  constructor
  · intro hx
    obtain ⟨j,hjx,hj⟩ :=Walk.mem_support_iff_exists_getVert.mp hx
    rw [Walk.drop_length] at hj
    refine ⟨i+j,by omega,by omega,?_⟩
    simpa only [Walk.drop_getVert] using hjx
  · rintro ⟨j,hij,hj,hjx⟩
    apply Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨j-i,?_,?_⟩
    · simpa only [Walk.drop_getVert,Nat.add_sub_of_le hij] using hjx
    · rw [Walk.drop_length]
      omega
theorem vJ {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (i j :ℕ) (hij:i < j) (hj:j ≤ p.length) :
    (p.take i).support.Disjoint (p.drop j).support:=by
  rw [List.disjoint_left]
  intro x hx hy
  obtain ⟨a,ha,hax⟩ := (qz p i (by omega)).mp hx
  obtain ⟨b,hjb,hb,hbx⟩ := (rd p j hj).mp hy
  have hab:a=b:=hp.getVert_injOn (by change a ≤ p.length;omega) hb (hax.trans hbx.symm)
  omega
def sX {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (i j :ℕ) (hij:i ≤ j) : G.Walk (p.getVert i) (p.getVert j) :=
  ((p.drop i).take (j-i)).copy rfl (by
    rw [Walk.drop_getVert,Nat.add_sub_of_le hij])
theorem y2 {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (i j :ℕ) (hij:i ≤ j) (hj:j ≤ p.length) :
    (sX p i j hij).length=j-i:=by
  simp only [sX,Walk.length_copy,Walk.take_length,Walk.drop_length]
  exact min_eq_left (by omega)
theorem aj {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (i j :ℕ) (hij:i ≤ j) :
    (sX p i j hij).IsPath:=by
  simpa only [sX,Walk.isPath_copy] using ((hp.drop i).take (j-i))
theorem vo {V:Type*} {G:SimpleGraph V} {u v x:V}
    (p:G.Walk u v) (i j :ℕ) (hij:i ≤ j) (hj:j ≤ p.length) :
    x ∈ (sX p i j hij).support ↔
      ∃ a,i ≤ a ∧ a ≤ j ∧ p.getVert a =x:=by
  rw [sX,Walk.support_copy]
  have hlen:j-i ≤ (p.drop i).length:=by rw [Walk.drop_length];omega
  rw [qz (p.drop i) (j-i) hlen]
  constructor
  · rintro ⟨a,ha,hax⟩
    refine ⟨i+a,by omega,by omega,?_⟩
    simpa only [Walk.drop_getVert] using hax
  · rintro ⟨a,hia,haj,hax⟩
    refine ⟨a-i,by omega,?_⟩
    simpa only [Walk.drop_getVert,Nat.add_sub_of_le hia] using hax
end Erdos556
end dD
section dL
namespace Erdos556
open SimpleGraph
def rF {V:Type*} {G:SimpleGraph V} {v:V}
    (c:G.Walk v v) (i j :ℕ) : G.Walk (c.getVert j) (c.getVert i) :=
  (c.drop j).append (c.take i)
theorem uF {V:Type*} {G:SimpleGraph V} {v:V}
    (c:G.Walk v v) (i j :ℕ) (hi:i ≤ c.length) :
    (rF c i j).length=c.length-j+i:=by
  simp only [rF,Walk.length_append,Walk.drop_length,
    Walk.take_length,min_eq_left hi]
theorem x5 {V:Type*} {G:SimpleGraph V} {v:V}
    (c:G.Walk v v) (hc:c.IsCycle) (i j :ℕ) (hij:i < j) (hj:j ≤ c.length) :
    (rF c i j).IsPath:=by
  apply qr (c.drop j) (c.take i)
    (hc.isPath_drop (by omega)) (hc.isPath_take (by omega))
  intro x hxd hxt
  obtain ⟨a,hja,ha,hax⟩ := (rd c j hj).mp hxd
  obtain ⟨b,hb,hbx⟩ := (qz c i (by omega)).mp hxt
  by_cases he:a=c.length
  · rw [he,Walk.getVert_length] at hax
    exact hax.symm
  · have hab:=hc.getVert_injOn' (by change a ≤ c.length-1;omega)
      (by change b ≤ c.length-1;omega) (hax.trans hbx.symm)
    omega
theorem xU {V:Type*} {G:SimpleGraph V} {v x :V}
    (c:G.Walk v v) (i j :ℕ) (hi:i ≤ c.length) (hj:j ≤ c.length)
    (hx:x ∈ (rF c i j).support) : x ∈ c.support:=by
  rcases (Walk.mem_support_append_iff (c.drop j) (c.take i)).mp hx with hxd | hxt
  · obtain ⟨a,_,_,hax⟩ := (rd c j hj).mp hxd
    exact hax ▸ c.getVert_mem_support a
  · obtain ⟨a,_,hax⟩ := (qz c i hi).mp hxt
    exact hax ▸ c.getVert_mem_support a
theorem rA {V:Type*} {G:SimpleGraph V} {v:V}
    (c:G.Walk v v) (hc:c.IsCycle) (i j a:ℕ)
    (hia:i ≤ a) (haj:a ≤ j) (hj:j < c.length)
    (ha:c.getVert a ∈ (rF c i j).support) : a=i ∨ a=j:=by
  rcases (Walk.mem_support_append_iff (c.drop j) (c.take i)).mp ha with had | hat
  · obtain ⟨b,hjb,hb,hba⟩ := (rd c j hj.le).mp had
    by_cases hbe:b=c.length
    · rw [hbe,Walk.getVert_length] at hba
      have h := (hc.getVert_endpoint_iff (by omega)).mp hba.symm
      left
      omega
    · have hba':=hc.getVert_injOn' (by change b ≤ c.length-1;omega)
        (by change a ≤ c.length-1;omega) hba
      right
      omega
  · obtain ⟨b,hbi,hba⟩ := (qz c i (by omega)).mp hat
    have hba':=hc.getVert_injOn' (by change b ≤ c.length-1;omega)
      (by change a ≤ c.length-1;omega) hba
    left
    omega
end Erdos556
end dL
section ds
namespace Erdos556
open Finset
theorem wj {I V :Type*} [DecidableEq V]
    (A:Finset I) (S:I → Finset V) (m:ℕ)
    (hinter: ∀ i ∈ A,∀ j ∈ A,i ≠ j → (S i ∩ S j).card ≤ m) :
    (∑ i ∈ A,(S i).card) ≤ (A.biUnion S).card+A.card^2*m:=by
  classical
  induction A using Finset.induction_on with
  | empty=> simp
  | @insert i A hi ih=>
      have hpair: ∀ a ∈ A,∀ b ∈ A,a ≠ b → (S a ∩ S b).card ≤ m:=by
        intro a ha b hb hab
        exact hinter a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab
      have hrec:=ih hpair
      have hcross: (S i ∩ A.biUnion S).card ≤ A.card*m:=by
        have hsub:S i ∩ A.biUnion S ⊆ A.biUnion (fun j => S i ∩ S j) :=by
          intro x hx
          obtain ⟨hxi,hxA⟩ :=mem_inter.mp hx
          obtain ⟨j,hj,hxj⟩ :=mem_biUnion.mp hxA
          exact mem_biUnion.mpr ⟨j,hj,mem_inter.mpr ⟨hxi,hxj⟩⟩
        calc
          (S i ∩ A.biUnion S).card ≤ (A.biUnion (fun j => S i ∩ S j)).card:=card_le_card hsub
          _ ≤ ∑ j ∈ A,(S i ∩ S j).card:=card_biUnion_le
          _ ≤ ∑ _j ∈ A,m:=by
            apply sum_le_sum
            intro j hj
            exact hinter i (mem_insert_self _ _) j (mem_insert_of_mem hj)
              (fun h => hi (h.symm ▸ hj))
          _=A.card*m:=by simp
      have hunion:=card_union_add_card_inter (S i) (A.biUnion S)
      rw [sum_insert hi,biUnion_insert,card_insert_of_notMem hi]
      calc
        (S i).card+ ∑ j ∈ A,(S j).card ≤
            (S i).card+ (A.biUnion S).card+A.card^2*m:=by omega
        _= (S i ∪ A.biUnion S).card+ (S i ∩ A.biUnion S).card+A.card^2*m:=by omega
        _ ≤ (S i ∪ A.biUnion S).card+A.card*m+A.card^2*m:=by omega
        _ ≤ (S i ∪ A.biUnion S).card+ (A.card+1) ^ 2*m:=by
          nlinarith [Nat.zero_le (A.card*m)]
theorem yl {I V :Type*} [Fintype I] [Fintype V]
    [DecidableEq V] (S:I → Finset V) (d m :ℕ)
    (hsize: ∀ i,d ≤ (S i).card)
    (hcount:Fintype.card V + (Fintype.card I) ^ 2*m < Fintype.card I *d) :
    ∃ i j:I,i ≠ j ∧ m < (S i ∩ S j).card:=by
  classical
  by_contra! h
  have hsum:Fintype.card I *d ≤ ∑ i,(S i).card:=by
    calc
      Fintype.card I *d= ∑ _i:I,d:=by simp
      _ ≤ ∑ i,(S i).card:=sum_le_sum fun i _=> hsize i
  have hbound:=wj univ S m
    (fun i _ j _ hij=> h i j hij)
  rw [card_univ] at hbound
  have hcard:=card_le_univ (univ.biUnion S)
  omega
theorem vN {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (D d :ℕ)
    (hN:0 < Fintype.card V) (hscale:Fintype.card V ≤ D *d)
    (hdegree: ∀ v,d ≤ G.degree v) (S:Finset V) (hS:2*S.card ≤ d)
    (a:Fin (4*D) → V) :
    ∃ i j:Fin (4*D),i ≠ j ∧
      Fintype.card V / (2* (4*D) ^ 2) <
        ((G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S).card:=by
  classical
  let W (i:Fin (4*D)) :=G.neighborFinset (a i) \ S
  have hsize (i:Fin (4*D)) : d-S.card ≤ (W i).card:=by
    have hi:=hdegree (a i)
    have hint: (S ∩ G.neighborFinset (a i)).card ≤ S.card:=card_le_card inter_subset_left
    dsimp [W]
    rw [card_sdiff]
    rw [G.card_neighborFinset_eq_degree]
    omega
  have hcount:Fintype.card V + (4*D) ^ 2*
      (Fintype.card V / (2* (4*D) ^ 2)) < 4*D* (d-S.card) :=by
    have hd:d ≤ 2* (d-S.card) :=by omega
    have hmul:=Nat.mul_le_mul_left (2*D) hd
    have hdiv:=Nat.div_mul_le_self (Fintype.card V) (2* (4*D) ^ 2)
    nlinarith
  obtain ⟨i,j,hij,hc⟩ :=yl W (d-S.card)
    (Fintype.card V / (2* (4*D) ^ 2)) hsize (by simpa only [Fintype.card_fin] using hcount)
  refine ⟨i,j,hij,?_⟩
  have heq:W i ∩ W j= (G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S:=by
    ext v
    simp only [W,mem_inter,mem_sdiff]
    tauto
  rwa [heq] at hc
end Erdos556
end ds
section ci
namespace Erdos556
open Finset
theorem wC {V:Type*} [Fintype V]
    (D L d:ℕ) (hL:0 < L) (hN:0 < Fintype.card V)
    (hscale:Fintype.card V ≤ D *d)
    (S:Fin (2*D*L) → Finset V) (hsize: ∀ i,d ≤ (S i).card) :
    ∃ (X:Finset (Fin (2*D*L))) (W:Finset V),
      L ≤ X.card ∧ Fintype.card V ≤ 2 *D*2^ (2*D*L) * W.card ∧
      ∀ i ∈ X,∀ v ∈ W,v ∈ S i:=by
  classical
  let I :=Fin (2*D*L)
  let pattern (v:V) : Finset I :=univ.filter (fun i => v ∈ S i)
  let A :=univ.filter (fun v => L ≤ (pattern v).card)
  have hinc: (∑ i :I,(S i).card) = ∑ v :V,(pattern v).card:=by
    have hs (i:I) : (S i).card= ∑ v:V,if v ∈ S i then 1 else 0 :=by simp
    have hp (v:V) : (pattern v).card= ∑ i:I,if v ∈ S i then 1 else 0 :=by
      simp [pattern]
    simp_rw [hs,hp]
    exact sum_comm
  have hlower: (2*D*L) * d ≤ ∑ v :V,(pattern v).card:=by
    rw [← hinc]
    calc
      (2*D*L) * d= ∑ _i:I,d:=by simp [I]
      _ ≤ ∑ i :I,(S i).card:=sum_le_sum fun i _=> hsize i
  have hpoint (v:V) : (pattern v).card ≤ L+if v ∈ A then 2 *D*L else 0 :=by
    by_cases hv:v ∈ A
    · rw [if_pos hv]
      have h :=card_le_univ (pattern v)
      simp only [I,Fintype.card_fin] at h
      omega
    · rw [if_neg hv]
      have h : ¬ L ≤ (pattern v).card:=by simpa only [A,mem_filter,mem_univ,true_and] using hv
      omega
  have hupper: (∑ v :V,(pattern v).card) ≤ L*Fintype.card V + (2*D*L) * A.card:=by
    calc
      (∑ v :V,(pattern v).card) ≤ ∑ v :V,(L+if v ∈ A then 2 *D*L else 0) :=
        sum_le_sum fun v _=> hpoint v
      _=L*Fintype.card V + (2*D*L) * A.card:=by
        simp [sum_add_distrib,Nat.mul_comm]
  have hA:Fintype.card V ≤ 2 *D*A.card:=by
    have hscaled:=Nat.mul_le_mul_left (2*L) hscale
    have h :L*Fintype.card V ≤ L * (2*D*A.card) :=by
      nlinarith only [hlower,hupper,hscaled]
    exact (mul_le_mul_iff_right₀ hL).mp h
  let fiber (X:Finset I) :=A.filter (fun v => pattern v =X)
  obtain ⟨X,_,hmax⟩ :=exists_max_image (univ:Finset (Finset I))
    (fun X => (fiber X).card) univ_nonempty
  have hfib:A.card= ∑ X:Finset I,(fiber X).card:=
    card_eq_sum_card_fiberwise (fun v _=> mem_univ (pattern v))
  have hbound:A.card ≤ 2^ (2*D*L) * (fiber X).card:=by
    rw [hfib]
    calc
      (∑ Y :Finset I,(fiber Y).card) ≤ ∑ _Y:Finset I,(fiber X).card:=
        sum_le_sum fun Y _=> hmax Y (mem_univ Y)
      _=2^ (2*D*L) * (fiber X).card:=by simp [I]
  have hlarge:Fintype.card V ≤ 2 *D*2^ (2*D*L) * (fiber X).card:=by
    calc
      Fintype.card V ≤ 2 *D*A.card:=hA
      _ ≤ 2*D* (2^ (2*D*L) * (fiber X).card) :=Nat.mul_le_mul_left _ hbound
      _=2*D*2^ (2*D*L) * (fiber X).card:=by ring
  have hnon: (fiber X).Nonempty:=by
    apply card_pos.mp
    by_contra h
    have hz: (fiber X).card=0:=by omega
    rw [hz,mul_zero] at hlarge
    omega
  obtain ⟨v,hv⟩ :=hnon
  have hvA:= (mem_filter.mp hv).1
  have hvX:= (mem_filter.mp hv).2
  have hX:L ≤ X.card:=by
    rw [← hvX]
    exact (mem_filter.mp hvA).2
  refine ⟨X,fiber X,hX,hlarge,?_⟩
  intro i hi v hv
  have hpat:= (mem_filter.mp hv).2
  have hi':i ∈ pattern v :=by rw [hpat];exact hi
  exact (mem_filter.mp hi').2
end Erdos556
end ci
section d4
namespace Erdos556
open SimpleGraph Finset
def xW {V:Type*} [DecidableEq V] {G:SimpleGraph V} {z:V}
    (c:G.Walk z z) (W:Finset V) : Finset ℕ :=
  (range c.length).filter (fun i => c.getVert i ∈ W)
theorem ae {V:Type*} [DecidableEq V] {G:SimpleGraph V} {z:V}
    (c:G.Walk z z) (hc:c.IsCycle) (W:Finset V) (hW: ∀ x ∈ W,x ∈ c.support) :
    (xW c W).image c.getVert=W:=by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,hix⟩ :=mem_image.mp hx
    exact hix ▸ (mem_filter.mp hi).2
  · intro hx
    obtain ⟨i,hix,hi⟩ :=Walk.mem_support_iff_exists_getVert.mp (hW x hx)
    by_cases hie:i=c.length
    · have hzx:z=x:=by simpa only [hie,Walk.getVert_length] using hix
      apply mem_image.mpr
      refine ⟨0,mem_filter.mpr ⟨mem_range.mpr (by have h :=hc.three_le_length;omega),?_⟩,?_⟩
      · simpa only [Walk.getVert_zero,hzx] using hx
      · simpa only [Walk.getVert_zero] using hzx
    · exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr (by omega),hix ▸ hx⟩,hix⟩
theorem ax {V:Type*} [DecidableEq V] {G:SimpleGraph V} {z:V}
    (c:G.Walk z z) (hc:c.IsCycle) (W:Finset V) (hW: ∀ x ∈ W,x ∈ c.support) :
    (xW c W).card=W.card:=by
  have hinj:Set.InjOn c.getVert (xW c W:Set ℕ) :=by
    intro i hi j hj hij
    have hi':=mem_range.mp (mem_filter.mp hi).1
    have hj':=mem_range.mp (mem_filter.mp hj).1
    exact hc.getVert_injOn' (by change i ≤ c.length-1;omega)
      (by change j ≤ c.length-1;omega) hij
  have hcard:=card_image_of_injOn hinj
  rw [ae c hc W hW] at hcard
  exact hcard.symm
theorem vC {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {z:V} (c:G.Walk z z) (hc:c.IsCycle)
    (D L d:ℕ) (hL:0 < L) (hscale:Fintype.card V ≤ D *d)
    (hdegree: ∀ v,d ≤ G.degree v) (hlen:4*D*L ≤ c.length) :
    ∃ (A:Finset ℕ) (W:Finset V),A.card=L ∧
      (∀ i ∈ A,i < 4*D*L ∧ Even i) ∧
      (A.image c.getVert).card=L ∧
      Fintype.card V ≤ 2 *D*2^ (2*D*L) * W.card ∧
      ∀ i ∈ A,∀ w ∈ W,G.Adj (c.getVert i) w :=by
  classical
  obtain ⟨I,W,hI,hW,hcommon⟩ :=wC D L d hL
    (Fintype.card_pos_iff.mpr ⟨z⟩) hscale
    (fun i => G.neighborFinset (c.getVert (2*i.val)))
    (fun i => by simpa only [G.card_neighborFinset_eq_degree] using hdegree (c.getVert (2*i.val)))
  obtain ⟨J,hJI,hJ⟩ :=exists_subset_card_eq hI
  let f :Fin (2*D*L) ↪ ℕ:=
    ⟨fun i => 2 *i.val,by
      intro i j h
      change 2 *i.val=2*j.val at h
      exact Fin.ext (by omega)⟩
  let A :=J.map f
  have hA:A.card=L:=by simpa only [A,card_map] using hJ
  have hpos (i:ℕ) (hi:i ∈ A) : i < 4*D*L ∧ Even i :=by
    obtain ⟨a,ha,rfl⟩ :=mem_map.mp hi
    have hat:=a.isLt
    change 2 *a.val < 4*D*L ∧ Even (2*a.val)
    have hb:=Nat.mul_lt_mul_of_pos_left hat (by decide:0 < 2)
    have he:2* (2*D*L) = 4*D*L:=by ring
    rw [he] at hb
    exact ⟨hb,⟨a.val,by omega⟩⟩
  have hinj:Set.InjOn c.getVert (A:Set ℕ) :=by
    intro i hi j hj hij
    have hi':= (hpos i hi).1
    have hj':= (hpos j hj).1
    exact hc.getVert_injOn' (by change i ≤ c.length-1;omega)
      (by change j ≤ c.length-1;omega) hij
  refine ⟨A,W,hA,hpos,(card_image_of_injOn hinj).trans hA,hW,?_⟩
  intro i hi w hw
  obtain ⟨a,ha,rfl⟩ :=mem_map.mp hi
  exact (G.mem_neighborFinset _ _).mp (hcommon a (hJI ha) w hw)
end Erdos556
end d4
section d9
namespace Erdos556
open SimpleGraph Finset
theorem xB {V:Type*} [DecidableEq V] {G:SimpleGraph V} {z:V}
    (c:G.Walk z z) (W:Finset V) (N K Q M :ℕ) (hM:M ≤ c.length)
    (hsize:N ≤ K*W.card) (hN:2*K* (Q+M+1) ≤ N)
    (hoff: (W \ c.support.toFinset).card < Q) :
    ∃ U :Finset V,U ⊆ W ∧ (∀ x ∈ U,x ∈ c.support) ∧
      (∀ i,i ≤ M → c.getVert i ∉ U) ∧ N ≤ 2*K*U.card:=by
  let P := (c.take M).support.toFinset
  let E :=W \ c.support.toFinset
  let U := (W ∩ c.support.toFinset) \ P
  have hP:P.card ≤ M+1:=by
    have h :=List.toFinset_card_le (c.take M).support
    simpa only [Walk.length_support,Walk.take_length,min_eq_left hM] using h
  have hcover:W ⊆ U ∪ E ∪ P:=by
    intro x hxW
    by_cases hxP:x ∈ P
    · exact mem_union_right _ hxP
    by_cases hxC:x ∈ c.support.toFinset
    · exact mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨mem_inter.mpr ⟨hxW,hxC⟩,hxP⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨hxW,hxC⟩))
  have hcount:W.card ≤ U.card+Q+M+1:=by
    have h₁:=card_le_card hcover
    have h₂:=card_union_le (U ∪ E) P
    have h₃:=card_union_le U E
    change E.card < Q at hoff
    omega
  refine ⟨U,(sdiff_subset).trans inter_subset_left,?_,?_,?_⟩
  · intro x hx
    exact List.mem_toFinset.mp (mem_inter.mp (mem_sdiff.mp hx).1).2
  · intro i hi hmem
    have hp:c.getVert i ∈ P :=List.mem_toFinset.mpr
      ((qz c M hM).mpr ⟨i,hi,rfl⟩)
    exact (mem_sdiff.mp hmem).2 hp
  · have hmul:=Nat.mul_le_mul_left K hcount
    nlinarith only [hsize,hN,hmul]
end Erdos556
end d9
section cU
namespace Erdos556
open SimpleGraph Finset
theorem xa (S:Finset ℕ) (N Q :ℕ) (hQ:0 < Q)
    (hS: ∀ i ∈ S,i < N) (hc:2* (N/Q+1) < S.card) :
    ∃ i ∈ S,∃ j ∈ S,i < j ∧ j < i+Q ∧ i%2=j%2:=by
  let f (i:ℕ) := (i/Q,i%2)
  let T :=range (N/Q+1) ×ˢ range 2
  have hT:T.card < S.card:=by simpa only [T,card_product,card_range,Nat.mul_comm] using hc
  have hf: ∀ i ∈ S,f i ∈ T:=by
    intro i hi
    apply mem_product.mpr
    refine ⟨mem_range.mpr ?_,mem_range.mpr (Nat.mod_lt _ (by decide))⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (hS i hi).le)
  obtain ⟨i,hi,j,hj,hij,heq⟩ :=exists_ne_map_eq_of_card_lt_of_maps_to hT hf
  have hdiv:i/Q=j/Q:=congrArg Prod.fst heq
  have hpar:i%2=j%2:=congrArg Prod.snd heq
  have hclose:j < i+Q ∧ i < j+Q:=by
    have hiq:=Nat.div_add_mod i Q
    have hjq:=Nat.div_add_mod j Q
    have him:=Nat.mod_lt i hQ
    have hjm:=Nat.mod_lt j hQ
    rw [hdiv] at hiq
    omega
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ⟨i,hi,j,hj,hij,hclose.1,hpar⟩
  · exact ⟨j,hj,i,hi,hji,hclose.2,hpar.symm⟩
theorem th (N K :ℕ) (hK:0 < K) (hN:4*K ≤ N) :
    2* (N/ (4*K) + 1) ≤ N/K:=by
  have hq:1 ≤ N/ (4*K) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hmul:=Nat.div_mul_le_self N (4*K)
  have hdiv:4* (N/ (4*K)) ≤ N/K:=by
    apply (Nat.le_div_iff_mul_le hK).mpr
    nlinarith only [hmul]
  omega
theorem vE {V:Type*}
    {G:SimpleGraph V} {u v :V} (p:G.Walk u v)
    (W:Finset V) (hW: ∀ x ∈ W,x ∈ p.support)
    (N K :ℕ) (hK:0 < K) (hN:4*K ≤ N) (hpN:p.length < N)
    (hcard:N/K < W.card) :
    ∃ i j:ℕ,i < j ∧ j ≤ p.length ∧ j < i+4*K ∧
      i%2=j%2 ∧ p.getVert i ∈ W ∧ p.getVert j ∈ W :=by
  classical
  let S :=W.image (fun x => p.support.idxOf x)
  have hidx (x:V) (hx:x ∈ W) : p.support.idxOf x ≤ p.length:=by
    have h :=List.idxOf_lt_length_of_mem (hW x hx)
    rw [Walk.length_support] at h
    omega
  have hinj:Set.InjOn (fun x => p.support.idxOf x) (W:Set V) :=by
    intro x hx y hy hxy
    have h :=congrArg p.getVert hxy
    simpa only [p.getVert_support_idxOf (hW x hx),p.getVert_support_idxOf (hW y hy)] using h
  have hScard:S.card=W.card:=card_image_of_injOn hinj
  have hS (i:ℕ) (hi:i ∈ S) : i < N:=by
    obtain ⟨x,hx,rfl⟩ :=mem_image.mp hi
    exact (hidx x hx).trans_lt hpN
  have hc:2* (N/ (4*K) + 1) < S.card:=by
    rw [hScard]
    exact (th N K hK hN).trans_lt hcard
  obtain ⟨i,hi,j,hj,hij,hclose,hpar⟩ :=
    xa S N (4*K) (by omega) hS hc
  obtain ⟨x,hx,hxi⟩ :=mem_image.mp hi
  obtain ⟨y,hy,hyj⟩ :=mem_image.mp hj
  have hix:p.getVert i =x:=by rw [← hxi];exact p.getVert_support_idxOf (hW x hx)
  have hjy:p.getVert j =y:=by rw [← hyj];exact p.getVert_support_idxOf (hW y hy)
  refine ⟨i,j,hij,?_,hclose,hpar,hix ▸ hx,hjy ▸ hy⟩
  rw [← hyj]
  exact hidx y hy
end Erdos556
end cU
section dF
namespace Erdos556
open Finset
theorem yJ (S:Finset ℕ) (N Q L:ℕ) (hQ:0 < Q)
    (hS: ∀ i ∈ S,i < N)
    (hc:2* (N/Q+1) * (L-1) < S.card) :
    ∃ T :Finset ℕ,T ⊆ S ∧ T.card=L ∧
      ∀ i ∈ T,∀ j ∈ T,i%2=j%2 ∧ j < i+Q:=by
  let f (i:ℕ) := (i/Q,i%2)
  let B :=range (N/Q+1) ×ˢ range 2
  have hf: ∀ i ∈ S,f i ∈ B:=by
    intro i hi
    apply mem_product.mpr
    refine ⟨mem_range.mpr ?_,mem_range.mpr (Nat.mod_lt _ (by decide))⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (hS i hi).le)
  have hBc:B.card* (L-1) < S.card:=by
    simpa only [B,card_product,card_range,Nat.mul_comm (N/Q+1) 2] using hc
  obtain ⟨b,_,hb⟩ :=exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hBc
  obtain ⟨T,hT,hTc⟩ :=exists_subset_card_eq (show L ≤ (S.filter (fun i => f i=b)).card by
    omega)
  refine ⟨T,hT.trans (filter_subset _ _),hTc,?_⟩
  intro i hi j hj
  have hi':= (mem_filter.mp (hT hi)).2
  have hj':= (mem_filter.mp (hT hj)).2
  have heq:=hi'.trans hj'.symm
  have hdiv:i/Q=j/Q:=congrArg Prod.fst heq
  have hpar:i%2=j%2:=congrArg Prod.snd heq
  refine ⟨hpar,?_⟩
  have hiq:=Nat.div_add_mod i Q
  have hjq:=Nat.div_add_mod j Q
  have him:=Nat.mod_lt i hQ
  have hjm:=Nat.mod_lt j hQ
  rw [hdiv] at hiq
  omega
theorem yL (N K L:ℕ) (hK:0 < K) (hL:0 < L)
    (hN:8*K*L ≤ N) :
    2* (N/ (8*K*L) + 1) * (L-1) < N/ (2*K) :=by
  have hQ:0 < 8*K*L:=by positivity
  have hq:1 ≤ N/ (8*K*L) := (Nat.le_div_iff_mul_le hQ).mpr (by omega)
  have hmul:=Nat.div_mul_le_self N (8*K*L)
  have hdiv:4*L* (N/ (8*K*L)) ≤ N/ (2*K) :=by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    nlinarith only [hmul]
  have hsub:L-1+1=L:=by omega
  have hprod:0 ≤ (N/ (8*K*L) - 1) * (L-1) :=Nat.zero_le _
  have hqsub:N/ (8*K*L) - 1+1=N/ (8*K*L) :=by omega
  nlinarith
end Erdos556
end dF
section dI
namespace Erdos556
open SimpleGraph Finset
theorem ys {V:Type*} {G:SimpleGraph V} {z:V}
    (c:G.Walk z z) (hc:c.IsCycle) (W:Finset V) (hW: ∀ x ∈ W,x ∈ c.support)
    (M N K L :ℕ) (hK:0 < K) (hL:0 < L) (hN:8*K*L ≤ N)
    (hcN:c.length ≤ N) (hsize:N ≤ 2*K*W.card)
    (hoff: ∀ i,i ≤ M → c.getVert i ∉ W) :
    ∃ B :Finset ℕ,B.card=L ∧
      (∀ i ∈ B,M < i ∧ i < c.length ∧ c.getVert i ∈ W) ∧
      ∀ i ∈ B,∀ j ∈ B,i%2=j%2 ∧ j < i+8*K*L:=by
  classical
  let S :=xW c W
  have hScard:S.card=W.card:=ax c hc W hW
  have hS (i:ℕ) (hi:i ∈ S) : i < N:=
    (mem_range.mp (mem_filter.mp hi).1).trans_le hcN
  have hdiv:N/ (2*K) ≤ W.card:=by
    have h :=Nat.div_le_div_right hsize (c:=2*K)
    simpa only [Nat.mul_div_cancel_left W.card (by omega:0 < 2*K)] using h
  have hcount:2* (N/ (8*K*L) + 1) * (L-1) < S.card:=by
    rw [hScard]
    exact (yL N K L hK hL hN).trans_le hdiv
  obtain ⟨B,hBS,hB,hpar⟩ :=yJ S N (8*K*L) L
    (by positivity) hS hcount
  refine ⟨B,hB,?_,hpar⟩
  intro i hi
  obtain ⟨hiN,hiW⟩ :=mem_filter.mp (hBS hi)
  exact ⟨by by_contra h;exact hoff i (by omega) hiW,mem_range.mp hiN,hiW⟩
end Erdos556
end dI
section cO
namespace Erdos556
open SimpleGraph Finset
theorem vx {V:Type*} [DecidableEq V]
    {G:SimpleGraph V} {w:V} (c:G.Walk w w) (hc:c.IsCycle)
    (A:Finset ℕ) (hA:2 ≤ A.card) (M:ℕ) (hM:M < c.length)
    (hAM: ∀ i ∈ A,i ≤ M) (hpar: ∀ i ∈ A,∀ j ∈ A,i%2=j%2)
    (Y:Finset V) (hY: ∀ y ∈ Y,y ∉ c.support) :
    ∃ u ∈ A.image c.getVert,∃ v ∈ A.image c.getVert,u ≠ v ∧
      ∃ p :G.Walk u v,p.IsPath ∧ c.length ≤ p.length+M ∧
        p.length%2=c.length%2 ∧
        ∀ z ∈ p.support,z ∈ A.image c.getVert ∪ Y → z=u ∨ z=v:=by
  classical
  have hAnon:A.Nonempty:=card_pos.mp (by omega)
  let i :=A.min' hAnon
  let j :=A.max' hAnon
  have hiA:i ∈ A:=A.min'_mem hAnon
  have hjA:j ∈ A:=A.max'_mem hAnon
  have hij:i < j:=A.min'_lt_max'_of_card (by omega)
  have hiM:=hAM i hiA
  have hjM:=hAM j hjA
  have huv:c.getVert j ≠ c.getVert i :=by
    intro heq
    have h :=hc.getVert_injOn' (by change j ≤ c.length-1;omega)
      (by change i ≤ c.length-1;omega) heq
    omega
  refine ⟨c.getVert j,mem_image.mpr ⟨j,hjA,rfl⟩,
    c.getVert i,mem_image.mpr ⟨i,hiA,rfl⟩,huv,
    rF c i j,x5 c hc i j hij (by omega),?_,?_,?_⟩
  · rw [uF c i j (by omega)]
    omega
  · rw [uF c i j (by omega)]
    have h :=hpar i hiA j hjA
    omega
  · intro z hz hzR
    rcases mem_union.mp hzR with hzA | hzY
    · obtain ⟨a,haA,haz⟩ :=mem_image.mp hzA
      have hia:i ≤ a:=A.min'_le a haA
      have haj:a ≤ j:=A.le_max' a haA
      have haz':c.getVert a ∈ (rF c i j).support:=haz ▸ hz
      rcases rA c hc i j a hia haj (by omega) haz'
        with hai | haj
      · right
        rw [← haz,hai]
      · left
        rw [← haz,haj]
    · exact (hY z hzY (xU c i j (by omega) (by omega) hz)).elim
end Erdos556
end cO
section dJ
namespace Erdos556
open SimpleGraph
theorem vb {V:Type*} {G:SimpleGraph V} {z:V}
    (c:G.Walk z z) (hc:c.IsCycle) (u v w y w':ℕ)
    (huv:u < v) (hvw:v < w) (hwy:w < y) (hyw:y < w') (hw':w' < c.length)
    (huy:G.Adj (c.getVert u) (c.getVert y))
    (hvy:G.Adj (c.getVert v) (c.getVert y)) :
    ∃ p :G.Walk (c.getVert w') (c.getVert w),p.IsPath ∧
      p.length+v+w'=c.length+u+w+2 ∧
      (∀ a,u < a → a < v → c.getVert a ∉ p.support) ∧
      (∀ a,w < a → a < w' → a ≠ y → c.getVert a ∉ p.support) :=by
  let q :=rF c u w'
  let r :=sX c v w (by omega)
  have hq:q.IsPath:=x5 c hc u w' (by omega) hw'.le
  have hr:r.IsPath:=by
    simp only [r,sX,Walk.isPath_copy]
    exact (hc.isPath_drop (by omega:0 < v)).take (w-v)
  have hqavoid (a:ℕ) (hua:u < a) (haw:a < w') : c.getVert a ∉ q.support:=by
    intro ha
    have h :=rA c hc u w' a hua.le haw.le hw' ha
    omega
  have hrmem (a:V) (ha:a ∈ r.support) :
      ∃ k,v ≤ k ∧ k ≤ w ∧ c.getVert k =a:=
    (vo c v w (by omega) (by omega)).mp ha
  have hyq:c.getVert y ∉ q.support:=hqavoid y (by omega) hyw
  have hyr:c.getVert y ∉ r.support:=by
    intro hy
    obtain ⟨k,hvk,hkw,hky⟩ :=hrmem _ hy
    have h :=hc.getVert_injOn' (by change k ≤ c.length-1;omega)
      (by change y ≤ c.length-1;omega) hky
    omega
  have hqr:q.support.Disjoint r.support:=by
    rw [List.disjoint_left]
    intro a haq har
    obtain ⟨k,hvk,hkw,hka⟩ :=hrmem a har
    exact hqavoid k (by omega) (by omega) (hka ▸ haq)
  let p := (q.concat huy).append (Walk.cons hvy.symm r)
  have hp:p.IsPath:=by
    apply qr (q.concat huy) (Walk.cons hvy.symm r)
      (hq.concat hyq huy) ((Walk.cons_isPath_iff _ _).mpr ⟨hr,hyr⟩)
    intro a ha hb
    simp only [Walk.support_concat,List.mem_append,List.mem_singleton] at ha
    simp only [Walk.support_cons,List.mem_cons] at hb
    rcases ha with haq | hay
    · rcases hb with hay | har
      · exact hay
      · exact (hqr haq har).elim
    · exact hay
  have havoid (a:ℕ) (hua:u < a) (haw:a < w')
      (havw: ¬ (v ≤ a ∧ a ≤ w)) (hay:a ≠ y) : c.getVert a ∉ p.support:=by
    intro ha
    rcases (Walk.mem_support_append_iff (q.concat huy) (Walk.cons hvy.symm r)).mp ha with ha | ha
    · simp only [Walk.support_concat,List.mem_append,List.mem_singleton] at ha
      rcases ha with haq | hay'
      · exact hqavoid a hua haw haq
      · exact hay (hc.getVert_injOn' (by change a ≤ c.length-1;omega)
          (by change y ≤ c.length-1;omega) hay')
    · simp only [Walk.support_cons,List.mem_cons] at ha
      rcases ha with hay' | har
      · exact hay (hc.getVert_injOn' (by change a ≤ c.length-1;omega)
          (by change y ≤ c.length-1;omega) hay')
      · obtain ⟨k,hvk,hkw,hka⟩ :=hrmem _ har
        have hka':=hc.getVert_injOn' (by change k ≤ c.length-1;omega)
          (by change a ≤ c.length-1;omega) hka
        exact havw (by omega)
  refine ⟨p,hp,?_,?_,?_⟩
  · simp only [p,q,r,Walk.length_append,Walk.length_concat,Walk.length_cons,
      uF c u w' (by omega),y2 c v w (by omega) (by omega)]
    omega
  · intro a hua hav
    exact havoid a hua (by omega) (by omega) (by omega)
  · intro a hwa haw hay
    exact havoid a (by omega) haw (by omega) hay
end Erdos556
end dJ
section cX
namespace Erdos556
open SimpleGraph Finset
theorem vg {V:Type*} [DecidableEq V]
    {G:SimpleGraph V} {z:V} (c:G.Walk z z) (hc:c.IsCycle)
    (A B :Finset ℕ) (Q M H:ℕ) (hQ:0 < Q)
    (hA:A.card=Q+2) (hB:B.card=Q+3) (hM:M < c.length)
    (hAM: ∀ a ∈ A,a ≤ M) (hBM: ∀ b ∈ B,M < b ∧ b < c.length)
    (hparA: ∀ a ∈ A,∀ b ∈ A,a%2=b%2)
    (hparB: ∀ a ∈ B,∀ b ∈ B,a%2=b%2)
    (hdiam: ∀ a ∈ B,∀ b ∈ B,b < a+H)
    (hcomplete: ∀ a ∈ A,∀ b ∈ B,G.Adj (c.getVert a) (c.getVert b)) :
    ∃ X Y:Finset V,X.card=Q+2 ∧ Y.card=Q ∧ Disjoint X Y ∧
      (∀ x ∈ X,∀ y ∈ Y,G.Adj x y) ∧
      ∃ u ∈ X,∃ v ∈ X,u ≠ v ∧ ∃ p:G.Walk u v,p.IsPath ∧
        c.length ≤ p.length+M+H ∧ p.length%2=c.length%2 ∧
        ∀ w ∈ p.support,w ∈ X ∪ Y → w=u ∨ w=v:=by
  classical
  have hAn:A.Nonempty:=card_pos.mp (by omega)
  have hBn:B.Nonempty:=card_pos.mp (by omega)
  let a :=A.min' hAn
  let b :=A.max' hAn
  let w :=B.min' hBn
  let w':=B.max' hBn
  have ha:a ∈ A:=A.min'_mem hAn
  have hb:b ∈ A:=A.max'_mem hAn
  have hw:w ∈ B:=B.min'_mem hBn
  have hw':w' ∈ B:=B.max'_mem hBn
  have hab:a < b:=A.min'_lt_max'_of_card (by omega)
  have hww:w < w':=B.min'_lt_max'_of_card (by omega)
  have hmiddle: (B \ {w,w'}).Nonempty:=by
    apply card_pos.mp
    have hpair: ({w,w'} : Finset ℕ).card ≤ 2:= (card_insert_le _ _).trans (by simp)
    have hint:=card_le_card (show ({w,w'} : Finset ℕ) ∩ B ⊆ {w,w'} from inter_subset_left)
    rw [card_sdiff]
    omega
  obtain ⟨y,hy⟩ :=hmiddle
  have hyB:= (mem_sdiff.mp hy).1
  have hyw:y ≠ w:=fun h => (mem_sdiff.mp hy).2 (by simp [h])
  have hyw':y ≠ w':=fun h => (mem_sdiff.mp hy).2 (by simp [h])
  have hwy:w < y:=lt_of_le_of_ne (B.min'_le y hyB) hyw.symm
  have hywlt:y < w':=lt_of_le_of_ne (B.le_max' y hyB) hyw'
  have hbM:=hAM b hb
  have haM:=hAM a ha
  have hwM:= (hBM w hw).1
  have hwlen:= (hBM w' hw').2
  have hallA (i:ℕ) (hi:i ∈ A) : i < c.length:= (hAM i hi).trans_lt hM
  have hinjA:Set.InjOn c.getVert (A:Set ℕ) :=by
    intro i hi j hj hij
    exact hc.getVert_injOn' (by change i ≤ c.length-1;have h :=hallA i hi;omega)
      (by change j ≤ c.length-1;have h :=hallA j hj;omega) hij
  have hinjB:Set.InjOn c.getVert (B:Set ℕ) :=by
    intro i hi j hj hij
    exact hc.getVert_injOn' (by change i ≤ c.length-1;have h := (hBM i hi).2;omega)
      (by change j ≤ c.length-1;have h := (hBM j hj).2;omega) hij
  have habv:c.getVert a ≠ c.getVert b :=fun h => (ne_of_lt hab) (hinjA ha hb h)
  have hwyv:c.getVert w ≠ c.getVert y :=fun h => hyw (hinjB hw hyB h).symm
  have hw'yv:c.getVert w' ≠ c.getVert y :=fun h => hyw' (hinjB hw' hyB h).symm
  let X := (B.image c.getVert).erase (c.getVert y)
  let Y := ((A.image c.getVert).erase (c.getVert a)).erase (c.getVert b)
  have hX:X.card=Q+2:=by
    dsimp [X]
    rw [card_erase_of_mem (mem_image.mpr ⟨y,hyB,rfl⟩),card_image_of_injOn hinjB,hB]
    omega
  have hY:Y.card=Q:=by
    dsimp [Y]
    rw [card_erase_of_mem (mem_erase.mpr ⟨habv.symm,mem_image.mpr ⟨b,hb,rfl⟩⟩),
      card_erase_of_mem (mem_image.mpr ⟨a,ha,rfl⟩),card_image_of_injOn hinjA,hA]
    omega
  have hXYcomplete (x:V) (hx:x ∈ X) (v:V) (hv:v ∈ Y) : G.Adj x v:=by
    obtain ⟨i,hi,rfl⟩ :=mem_image.mp (mem_of_mem_erase hx)
    obtain ⟨j,hj,rfl⟩ :=mem_image.mp (mem_of_mem_erase (mem_of_mem_erase hv))
    exact (hcomplete j hj i hi).symm
  have hXY:Disjoint X Y:=by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (hXYcomplete x hx x hy).ne rfl
  obtain ⟨p,hp,hlen,havoidA,havoidB⟩ :=vb c hc a b w y w'
    hab (by omega) hwy hywlt hwlen (hcomplete a ha y hyB) (hcomplete b hb y hyB)
  refine ⟨X,Y,hX,hY,hXY,hXYcomplete,c.getVert w',
    mem_erase.mpr ⟨hw'yv,mem_image.mpr ⟨w',hw',rfl⟩⟩,
    c.getVert w,mem_erase.mpr ⟨hwyv,mem_image.mpr ⟨w,hw,rfl⟩⟩,
    (fun h => (ne_of_lt hww) (hinjB hw' hw h).symm),p,hp,?_,?_,?_⟩
  · have hd:=hdiam w hw w' hw'
    omega
  · have h₁:=hparA a ha b hb
    have h₂:=hparB w hw w' hw'
    omega
  · intro v hv hvXY
    rcases mem_union.mp hvXY with hvX | hvY
    · have hvy:= (mem_erase.mp hvX).1
      obtain ⟨i,hi,hiv⟩ :=mem_image.mp (mem_of_mem_erase hvX)
      by_cases hiw:i=w
      · right
        rw [← hiv,hiw]
      by_cases hiw':i=w'
      · left
        rw [← hiv,hiw']
      have hwil:w ≤ i:=B.min'_le i hi
      have hiwl:i ≤ w':=B.le_max' i hi
      have hiy:i ≠ y:=fun h => hvy (by rw [← hiv,h])
      exact (havoidB i (by omega) (by omega) hiy (hiv ▸ hv)).elim
    · have hvb:= (mem_erase.mp hvY).1
      have hva:= (mem_erase.mp (mem_of_mem_erase hvY)).1
      obtain ⟨i,hi,hiv⟩ :=mem_image.mp (mem_of_mem_erase (mem_of_mem_erase hvY))
      have hai:a ≤ i:=A.min'_le i hi
      have hib:i ≤ b:=A.le_max' i hi
      have hia:i ≠ a:=fun h => hva (by rw [← hiv,h])
      have hib':i ≠ b:=fun h => hvb (by rw [← hiv,h])
      exact (havoidA i (by omega) (by omega) (hiv ▸ hv)).elim
end Erdos556
end cX
section dr
namespace Erdos556
open SimpleGraph Finset
def rR (D Q :ℕ) :=4*D* (Q+2)
def rl (D Q :ℕ) :=2*D*2^ (2*D* (Q+2))
def sd (D Q :ℕ) :=8*rl D Q* (Q+3)
theorem tl {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {z:V} (c:G.Walk z z) (hc:c.IsCycle)
    (D d Q:ℕ) (hD:0 < D) (hQ:0 < Q)
    (hscale:Fintype.card V ≤ D *d) (hdegree: ∀ v,d ≤ G.degree v)
    (hlen:rR D Q < c.length)
    (hNloss:2*rl D Q* (Q+rR D Q+1) ≤
      Fintype.card V)
    (hNblock:sd D Q ≤ Fintype.card V) :
    ∃ X Y:Finset V,X.card=Q+2 ∧ Y.card=Q ∧ Disjoint X Y ∧
      (∀ x ∈ X,∀ y ∈ Y,G.Adj x y) ∧
      ∃ u ∈ X,∃ v ∈ X,u ≠ v ∧ ∃ p:G.Walk u v,p.IsPath ∧
        c.length ≤ p.length+rR D Q+sd D Q ∧
        p.length%2=c.length%2 ∧
        ∀ w ∈ p.support,w ∈ X ∪ Y → w=u ∨ w=v:=by
  classical
  let M :=rR D Q
  let K :=rl D Q
  let H :=sd D Q
  obtain ⟨A,W,hA,hAP,hAX,hWsize,hcomplete⟩ :=vC
    G c hc D (Q+2) d (by omega) hscale hdegree hlen.le
  have hAM (i:ℕ) (hi:i ∈ A) : i ≤ M:= (hAP i hi).1.le
  have hparA (i:ℕ) (hi:i ∈ A) (j:ℕ) (hj:j ∈ A) : i%2=j%2:=by
    have hiE:=Nat.even_iff.mp (hAP i hi).2
    have hjE:=Nat.even_iff.mp (hAP j hj).2
    omega
  let E :=W \ c.support.toFinset
  by_cases hext:Q ≤ E.card
  · obtain ⟨Y,hYE,hY⟩ :=exists_subset_card_eq hext
    have hYW:Y ⊆ W:=hYE.trans sdiff_subset
    have hYoff (y:V) (hy:y ∈ Y) : y ∉ c.support:=by
      intro hyc
      exact (mem_sdiff.mp (hYE hy)).2 (List.mem_toFinset.mpr hyc)
    let X :=A.image c.getVert
    have hcomp (x:V) (hx:x ∈ X) (y:V) (hy:y ∈ Y) : G.Adj x y:=by
      obtain ⟨i,hi,rfl⟩ :=mem_image.mp hx
      exact hcomplete i hi y (hYW hy)
    have hXY:Disjoint X Y:=by
      rw [Finset.disjoint_left]
      intro x hx hy
      exact (hcomp x hx x hy).ne rfl
    obtain ⟨u,hu,v,hv,huv,p,hp,hpL,hpPar,hpOff⟩ :=
      vx c hc A (by omega) M hlen hAM hparA Y hYoff
    exact ⟨X,Y,hAX,hY,hXY,hcomp,u,hu,v,hv,huv,p,hp,
      by omega,hpPar,hpOff⟩
  · have hK:0 < K:=by dsimp [K,rl];positivity
    obtain ⟨U,hUW,hUC,hUoff,hUsize⟩ :=xB c W
      (Fintype.card V) K Q M hlen.le hWsize hNloss (Nat.lt_of_not_ge hext)
    have hcN:c.length ≤ Fintype.card V :=by
      have h :=hc.isPath_tail.length_lt
      rw [Walk.length_tail] at h
      have hlen3:=hc.three_le_length
      omega
    obtain ⟨B,hB,hBM,hblock⟩ :=ys c hc U hUC M
      (Fintype.card V) K (Q+3) hK (by omega) hNblock hcN hUsize hUoff
    have hcomp (i:ℕ) (hi:i ∈ A) (j:ℕ) (hj:j ∈ B) :
        G.Adj (c.getVert i) (c.getVert j) :=hcomplete i hi _ (hUW (hBM j hj).2.2)
    exact vg c hc A B Q M H hQ hA hB hlen hAM
      (fun j hj=> ⟨(hBM j hj).1,(hBM j hj).2.1⟩) hparA
      (fun i hi j hj=> (hblock i hi j hj).1) (fun i hi j hj=> (hblock i hi j hj).2) hcomp
end Erdos556
end dr
section cd
namespace Erdos556
open SimpleGraph
theorem zg {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (i j :ℕ) (hij:i < j) (hj:j ≤ p.length)
    (x:V) (hx:x ∉ p.support) (hix:G.Adj (p.getVert i) x)
    (hjx:G.Adj (p.getVert j) x) :
    ∃ q :G.Walk u v,q.IsPath ∧ q.length+j=p.length+i+2 ∧
      ∀ z ∈ q.support,z ∈ p.support ∨ z=x:=by
  have hi:i ≤ p.length:=hij.le.trans hj
  have hpre (z:V) (hz:z ∈ (p.take i).support) : z ∈ p.support:=by
    obtain ⟨a,_,hax⟩ := (qz p i hi).mp hz
    exact hax ▸ p.getVert_mem_support a
  have hpost (z:V) (hz:z ∈ (p.drop j).support) : z ∈ p.support:=by
    obtain ⟨a,_,_,hax⟩ := (rd p j hj).mp hz
    exact hax ▸ p.getVert_mem_support a
  let a :G.Walk u x:= (p.take i).concat hix
  let b :G.Walk x v:=Walk.cons hjx.symm (p.drop j)
  have ha:a.IsPath:= (hp.take i).concat (fun h => hx (hpre x h)) hix
  have hb:b.IsPath:= (Walk.cons_isPath_iff _ _).mpr
    ⟨hp.drop j,fun h => hx (hpost x h)⟩
  have hab: (a.append b).IsPath:=by
    apply qr a b ha hb
    intro z hza hzb
    simp only [a,Walk.support_concat,List.mem_append,List.mem_singleton] at hza
    simp only [b,Walk.support_cons,List.mem_cons] at hzb
    rcases hza with hza | hzx
    · rcases hzb with hzx | hzb
      · exact hzx
      · exact ((vJ p hp i j hij hj) hza hzb).elim
    · exact hzx
  refine ⟨a.append b,hab,?_,?_⟩
  · simp only [a,b,Walk.length_append,Walk.length_concat,Walk.length_cons,
      Walk.take_length,min_eq_left hi,Walk.drop_length]
    omega
  · intro z hz
    rcases (Walk.mem_support_append_iff a b).mp hz with hz | hz
    · simp only [a,Walk.support_concat,List.mem_append,List.mem_singleton] at hz
      exact hz.elim (fun h => Or.inl (hpre z h)) Or.inr
    · simp only [b,Walk.support_cons,List.mem_cons] at hz
      exact hz.elim Or.inr (fun h => Or.inl (hpost z h))
theorem v7 {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (i j :ℕ) (hij:i+4 ≤ j)
    (hj:j ≤ p.length) (hpar:i%2=j%2)
    (x:V) (hx:x ∉ p.support) (hix:G.Adj (p.getVert i) x)
    (hjx:G.Adj (p.getVert j) x) :
    ∃ q :G.Walk u v,q.IsPath ∧ q.length < p.length ∧
      p.length ≤ q.length+ (j-i) ∧ q.length%2=p.length%2 ∧
      ∀ z ∈ q.support,z ∈ p.support ∨ z=x:=by
  obtain ⟨q,hq,hlen,hs⟩ :=zg p hp i j (by omega) hj x hx hix hjx
  exact ⟨q,hq,by omega,by omega,by omega,hs⟩
theorem zm {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (i i' j j':ℕ)
    (hii:i < i') (hij:i' ≤ j) (hjj:j < j') (hj':j' ≤ p.length)
    (hchord₁:G.Adj (p.getVert i) (p.getVert j))
    (hchord₂:G.Adj (p.getVert i') (p.getVert j')) :
    ∃ q :G.Walk u v,q.IsPath ∧ q.length+i'+j'=p.length+i+j+2 ∧
      ∀ z ∈ q.support,z ∈ p.support:=by
  have hi:i ≤ p.length:=by omega
  have hi':i' ≤ p.length:=by omega
  have hj:j ≤ p.length:=by omega
  let a := (p.take i).concat hchord₁
  let b := (sX p i' j hij).reverse
  let c :=Walk.cons hchord₂ (p.drop j')
  have hbmem (z:V) (hz:z ∈ b.support) :
      ∃ k,i' ≤ k ∧ k ≤ j ∧ p.getVert k =z:=by
    apply (vo p i' j hij hj).mp
    simpa only [b,Walk.support_reverse,List.mem_reverse] using hz
  have ha:a.IsPath:=by
    apply (hp.take i).concat
    intro hz
    obtain ⟨k,hk,hkj⟩ := (qz p i hi).mp hz
    have hkj':=hp.getVert_injOn (by change k ≤ p.length;omega) hj hkj
    omega
  have hb:b.IsPath:= (aj p hp i' j hij).reverse
  have hab: (a.append b).IsPath:=by
    apply qr a b ha hb
    intro z hza hzb
    simp only [a,Walk.support_concat,List.mem_append,List.mem_singleton] at hza
    rcases hza with hza | hzj
    · obtain ⟨k,hk,hkz⟩ := (qz p i hi).mp hza
      obtain ⟨l,hil,hlj,hlz⟩ :=hbmem z hzb
      have hkl:=hp.getVert_injOn (by change k ≤ p.length;omega)
        (by change l ≤ p.length;omega) (hkz.trans hlz.symm)
      omega
    · exact hzj
  have hc:c.IsPath:=by
    apply (Walk.cons_isPath_iff _ _).mpr
    refine ⟨hp.drop j',?_⟩
    intro hz
    obtain ⟨k,hjk,hk,hki⟩ := (rd p j' hj').mp hz
    have hki':=hp.getVert_injOn hk hi' hki
    omega
  have habpre (z:V) (hz:z ∈ (a.append b).support) : z ∈ (p.take j).support:=by
    apply (qz p j hj).mpr
    rcases (Walk.mem_support_append_iff a b).mp hz with hza | hzb
    · simp only [a,Walk.support_concat,List.mem_append,List.mem_singleton] at hza
      rcases hza with hza | hzj
      · obtain ⟨k,hk,hkz⟩ := (qz p i hi).mp hza
        exact ⟨k,by omega,hkz⟩
      · exact ⟨j,le_rfl,hzj.symm⟩
    · obtain ⟨k,_,hk,hkz⟩ :=hbmem z hzb
      exact ⟨k,hk,hkz⟩
  have hpath: ((a.append b).append c).IsPath:=by
    apply qr (a.append b) c hab hc
    intro z hzab hzc
    simp only [c,Walk.support_cons,List.mem_cons] at hzc
    rcases hzc with hzi | hzc
    · exact hzi
    · exact ((vJ p hp j j' hjj hj') (habpre z hzab) hzc).elim
  refine ⟨(a.append b).append c,hpath,?_,?_⟩
  · simp only [a,b,c,Walk.length_append,Walk.length_concat,Walk.take_length,
      min_eq_left hi,Walk.length_reverse,y2 p i' j hij hj,
      Walk.length_cons,Walk.drop_length]
    omega
  · intro z hz
    rcases (Walk.mem_support_append_iff (a.append b) c).mp hz with hzab | hzc
    · obtain ⟨k,_,hkz⟩ := (qz p j hj).mp (habpre z hzab)
      exact hkz ▸ p.getVert_mem_support k
    · simp only [c,Walk.support_cons,List.mem_cons] at hzc
      rcases hzc with hzi | hzc
      · exact hzi ▸ p.getVert_mem_support i'
      · obtain ⟨k,_,_,hkz⟩ := (rd p j' hj').mp hzc
        exact hkz ▸ p.getVert_mem_support k
theorem vf {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (i i' j j':ℕ)
    (hii:i+4 ≤ i') (hij:i' ≤ j) (hjj:j+2 ≤ j') (hj':j' ≤ p.length)
    (hpar₁:i%2=i'%2) (hpar₂:j%2=j'%2)
    (hchord₁:G.Adj (p.getVert i) (p.getVert j))
    (hchord₂:G.Adj (p.getVert i') (p.getVert j')) :
    ∃ q :G.Walk u v,q.IsPath ∧ q.length < p.length ∧
      p.length ≤ q.length+ (i'-i) + (j'-j) ∧
      q.length%2=p.length%2 ∧ ∀ z ∈ q.support,z ∈ p.support:=by
  obtain ⟨q,hq,hlen,hs⟩ :=zm p hp i i' j j'
    (by omega) hij (by omega) hj' hchord₁ hchord₂
  exact ⟨q,hq,by omega,by omega,by omega,hs⟩
end Erdos556
end cd
section cM
namespace Erdos556
open SimpleGraph Finset
theorem u8 {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (D d :ℕ) (hD:0 < D)
    (hscale:Fintype.card V ≤ D *d) (hdegree: ∀ v,d ≤ G.degree v)
    (hN:8* (4*D) ^ 2 ≤ Fintype.card V)
    (R:Finset V) (hR:2* (R.card+16*D+1) ≤ d)
    {u v :V} (p:G.Walk u v) (hp:p.IsPath) (hlen:16*D ≤ p.length) :
    ∃ q :G.Walk u v,q.IsPath ∧ q.length < p.length ∧
      p.length ≤ q.length+ (16*D+8* (4*D) ^ 2) ∧
      q.length%2=p.length%2 ∧
      ∀ z ∈ q.support,z ∈ p.support ∨ z ∉ R:=by
  classical
  let S :=R ∪ (p.take (16*D)).support.toFinset
  have hprefix: (p.take (16*D)).support.toFinset.card ≤ 16*D+1:=by
    have h :=List.toFinset_card_le (p.take (16*D)).support
    simpa only [Walk.length_support,Walk.take_length,min_eq_left hlen] using h
  have hS:2*S.card ≤ d:=by
    have h :=card_union_le R (p.take (16*D)).support.toFinset
    change S.card ≤ R.card+ (p.take (16*D)).support.toFinset.card at h
    omega
  let a (i:Fin (4*D)) :=p.getVert (4*i.val)
  have hpositive:0 < Fintype.card V :=by nlinarith
  obtain ⟨i₀,j₀,hne,hc⟩ :=vN G D d hpositive
    hscale hdegree S hS a
  have hordered: ∃ i j:Fin (4*D),i.val < j.val ∧
      Fintype.card V / (2* (4*D) ^ 2) <
        ((G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S).card:=by
    have hne':i₀.val ≠ j₀.val:=fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with hij | hji
    · exact ⟨i₀,j₀,hij,hc⟩
    · refine ⟨j₀,i₀,hji,?_⟩
      rwa [inter_comm]
  obtain ⟨i,j,hij,hcommon⟩ :=hordered
  let W := (G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S
  have hmem (x:V) (hx:x ∈ W) :
      G.Adj (p.getVert (4*i.val)) x ∧ G.Adj (p.getVert (4*j.val)) x ∧ x ∉ S :=by
    obtain ⟨hxij,hxS⟩ :=mem_sdiff.mp hx
    obtain ⟨hxi,hxj⟩ :=mem_inter.mp hxij
    exact ⟨(G.mem_neighborFinset _ _).mp hxi,(G.mem_neighborFinset _ _).mp hxj,hxS⟩
  have h4j:4*j.val ≤ p.length:=by have h :=j.isLt;omega
  have h4i:4*i.val+4 ≤ 4*j.val:=by omega
  have hpar: (4*i.val) % 2= (4*j.val) % 2:=by omega
  by_cases hex: ∃ x ∈ W,x ∉ p.support
  · obtain ⟨x,hxW,hx⟩ :=hex
    obtain ⟨hix,hjx,hxS⟩ :=hmem x hxW
    have hxR:x ∉ R:=fun h => hxS (mem_union_left _ h)
    obtain ⟨q,hq,hlt,hbound,hparq,hsupport⟩ :=
      v7 p hp (4*i.val) (4*j.val)
        h4i h4j hpar x hx hix hjx
    refine ⟨q,hq,hlt,?_,hparq,?_⟩
    · have hjlt:=j.isLt
      omega
    · intro z hz
      rcases hsupport z hz with hzp | hzx
      · exact Or.inl hzp
      · exact Or.inr (hzx ▸ hxR)
  · have hW: ∀ x ∈ W,x ∈ p.support:=by
      intro x hx
      by_contra h
      exact hex ⟨x,hx,h⟩
    have hK:0 < 2* (4*D) ^ 2:=by positivity
    have hN':4* (2* (4*D) ^ 2) ≤ Fintype.card V :=by nlinarith only [hN]
    obtain ⟨s,t,hst,ht,hclose,hparst,hsW,htW⟩ :=
      vE p W hW (Fintype.card V)
        (2* (4*D) ^ 2) hK hN' hp.length_lt hcommon
    have hs:16*D < s:=by
      by_contra h
      have hs':s ≤ 16*D:=by omega
      have hsP:p.getVert s ∈ (p.take (16*D)).support:=
        (qz p (16*D) hlen).mpr ⟨s,hs',rfl⟩
      exact (hmem _ hsW).2.2 (mem_union_right R (List.mem_toFinset.mpr hsP))
    have hst2:s+2 ≤ t:=by omega
    have hjs:4*j.val ≤ s:=by have hjlt:=j.isLt;omega
    obtain ⟨q,hq,hlt,hbound,hparq,hsupport⟩ :=
      vf p hp (4*i.val) (4*j.val) s t
        h4i hjs hst2 ht hpar hparst (hmem _ hsW).1 (hmem _ htW).2.1
    refine ⟨q,hq,hlt,?_,hparq,fun z hz=> Or.inl (hsupport z hz)⟩
    have hjlt:=j.isLt
    omega
end Erdos556
end cM
section cD
namespace Erdos556
open SimpleGraph
theorem zu {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (D d :ℕ) (hD:0 < D)
    (hscale:Fintype.card V ≤ D *d) (hdegree: ∀ v,d ≤ G.degree v)
    (hN:8* (4*D) ^ 2 ≤ Fintype.card V)
    (R:Finset V) (hR:2* (R.card+16*D+1) ≤ d)
    (t:ℕ) (ht:16*D ≤ t) {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (hlen:t ≤ p.length)
    (hoff: ∀ z ∈ p.support,z ∈ R → z=u ∨ z=v) :
    ∃ q :G.Walk u v,q.IsPath ∧ q.length ≤ t ∧
      t < q.length+ (16*D+8* (4*D) ^ 2) ∧
      q.length%2=p.length%2 ∧
      ∀ z ∈ q.support,z ∈ R → z=u ∨ z=v:=by
  classical
  have aux: ∀ M:ℕ,∀ p:G.Walk u v,p.length=M → p.IsPath → t ≤ p.length →
      (∀ z ∈ p.support,z ∈ R → z=u ∨ z=v) →
      ∃ q :G.Walk u v,q.IsPath ∧ q.length ≤ t ∧
        t < q.length+ (16*D+8* (4*D) ^ 2) ∧
        q.length%2=p.length%2 ∧
        ∀ z ∈ q.support,z ∈ R → z=u ∨ z=v:=by
    intro M
    induction M using Nat.strong_induction_on with
    | h M ih=>
        intro p hpM hp htP hoff
        by_cases hstop:p.length ≤ t
        · exact ⟨p,hp,hstop,by omega,rfl,hoff⟩
        obtain ⟨q,hq,hlt,hbound,hpar,hsupp⟩ :=
          u8 G D d hD hscale hdegree hN R hR
            p hp (by omega)
        have hoffq: ∀ z ∈ q.support,z ∈ R → z=u ∨ z=v:=by
          intro z hz hzR
          rcases hsupp z hz with hzp | hzoff
          · exact hoff z hzp hzR
          · exact (hzoff hzR).elim
        by_cases htq:t ≤ q.length
        · obtain ⟨w,hw,hwt,hwin,hwpar,hwoff⟩ :=
            ih q.length (by omega) q rfl hq htq hoffq
          exact ⟨w,hw,hwt,hwin,hwpar.trans hpar,hwoff⟩
        · exact ⟨q,hq,by omega,by omega,hpar,hoffq⟩
  exact aux p.length p rfl hp hlen hoff
end Erdos556
end cD
section dv
namespace Erdos556
open SimpleGraph
theorem yP {V:Type*} {G:SimpleGraph V}
    {u v :V} (p:G.Walk u v) (hp:p.length=G.dist u v)
    {i j :ℕ} (hij:i ≤ j) (hj:j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j-i:=by
  have hsub:= ((p.take j).isSubwalk_drop i).trans (p.isSubwalk_take j)
  have h :=length_eq_dist_of_subwalk hp hsub
  simpa only [Walk.drop_length,Walk.take_length,Walk.take_getVert,
    inf_eq_left.mpr hj,inf_eq_right.mpr hij] using h.symm
theorem sx {V:Type*} {G:SimpleGraph V}
    {u v :V} (p:G.Walk u v) (hp:p.length=G.dist u v)
    {i j :ℕ} (hij:i+3 ≤ j) (hj:j ≤ p.length) (z:V) :
    ¬ (G.Adj (p.getVert i) z ∧ G.Adj (p.getVert j) z) :=by
  rintro ⟨hi,hjz⟩
  have hdist:=G.dist_le (Walk.cons hi (Walk.cons hjz.symm Walk.nil))
  rw [yP p hp (by omega) hj] at hdist
  simp only [Walk.length_cons,Walk.length_nil] at hdist
  omega
theorem sU {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {u v :V} (p:G.Walk u v)
    (hp:p.length=G.dist u v) (d:ℕ) (hdeg: ∀ w,d ≤ G.degree w) :
    (p.length/3+1) * d ≤ Fintype.card V :=by
  classical
  let I :=Fin (p.length/3+1)
  let W (i:I) :=G.neighborSet (p.getVert (3*i.val))
  let f : (Σ i :I,W i) → V:=fun x => x.2.val
  have hindex (i:I) : 3*i.val ≤ p.length:=by
    have hi:=i.isLt
    omega
  have hinj:Function.Injective f :=by
    rintro ⟨i,x⟩ ⟨j,y⟩ hxy
    have hij:i=j:=by
      by_contra hne
      have hval:i.val ≠ j.val:=fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hval with hij | hji
      · apply sx p hp
          (i:=3*i.val) (j:=3*j.val) (by omega) (hindex j) x.val
        refine ⟨x.property,?_⟩
        have heq:x.val=y.val:=hxy
        rw [heq]
        exact y.property
      · apply sx p hp
          (i:=3*j.val) (j:=3*i.val) (by omega) (hindex i) y.val
        refine ⟨y.property,?_⟩
        have heq:x.val=y.val:=hxy
        rw [← heq]
        exact x.property
    subst j
    have heq:x=y:=Subtype.ext hxy
    subst y
    rfl
  have hc:=Fintype.card_le_of_injective f hinj
  have hsum: (p.length/3+1) * d ≤ Fintype.card (Σ i :I,W i) :=by
    rw [Fintype.card_sigma]
    calc
      (p.length/3+1) * d= ∑ _i:I,d:=by simp [I]
      _ ≤ ∑ i :I,Fintype.card (W i) :=by
        apply Finset.sum_le_sum
        intro i _
        simpa only [W,card_neighborSet_eq_degree] using hdeg (p.getVert (3*i.val))
  exact hsum.trans hc
theorem xD {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (hconn:G.Connected)
    (d:ℕ) (hd:0 < d) (hdeg: ∀ w,d ≤ G.degree w) (u v :V) :
    ∃ p :G.Walk u v,p.IsPath ∧ d*p.length < 3*Fintype.card V :=by
  classical
  obtain ⟨p,hp,hdist⟩ :=hconn.exists_path_of_dist u v
  refine ⟨p,hp,?_⟩
  have hc:=sU G p hdist d hdeg
  have hlen:p.length < 3* (p.length/3+1) :=by omega
  nlinarith
end Erdos556
end dv
section d1
namespace Erdos556
open SimpleGraph Finset
def q8 {V:Type*} (G:SimpleGraph V) (b:ℕ) : Prop:=
  ∀ S :Finset V,S.card ≤ b → (G.induce (S:Set V)ᶜ).Preconnected
theorem q8.mono {V:Type*} {G:SimpleGraph V} {a b :ℕ}
    (h:q8 G b) (hab:a ≤ b) : q8 G a:=
  fun S hS=> h S (hS.trans hab)
theorem qW {V:Type*} [Fintype V]
    [DecidableEq V] (G:SimpleGraph V) [DecidableRel G.Adj]
    (S:Finset V) (v: ↥((S:Set V)ᶜ)) :
    G.degree v.val ≤ (G.induce (S:Set V)ᶜ).degree v +S.card:=by
  classical
  have hdeg: (G.induce (S:Set V)ᶜ).degree v =
      (G.neighborFinset v.val \ S).card:=by
    have h :=congrArg Finset.card (G.map_neighborFinset_induce v)
    simpa [← sdiff_eq_inter_compl] using h
  rw [hdeg,← G.card_neighborFinset_eq_degree v.val]
  have h :=card_sdiff_add_card_inter (G.neighborFinset v.val) S
  have hle:=card_le_card (inter_subset_right (s₁:=G.neighborFinset v.val) (s₂:=S))
  omega
theorem sB {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d :ℕ)
    (hconn:q8 G b) (hd:0 < d)
    (hdeg: ∀ w,d+b ≤ G.degree w) (S:Finset V) (hS:S.card ≤ b)
    (u v :V) (hu:u ∉ S) (hv:v ∉ S) :
    ∃ p :G.Walk u v,p.IsPath ∧ d*p.length < 3*Fintype.card V ∧
      ∀ x ∈ p.support,x ∉ S:=by
  classical
  let U := (S:Set V)ᶜ
  let u':U:= ⟨u,hu⟩
  let v':U:= ⟨v,hv⟩
  let:Nonempty U := ⟨u'⟩
  have hc: (G.induce U).Connected:= ⟨hconn S hS⟩
  have hmin (w:U) : d ≤ (G.induce U).degree w :=by
    have h :=qW G S w
    have hg:=hdeg w.val
    change G.degree w.val ≤ (G.induce U).degree w +S.card at h
    omega
  obtain ⟨p,hp,hlen⟩ :=xD
    (G.induce U) hc d hd hmin u' v'
  let f :G.induce U ↪g G :=SimpleGraph.Embedding.induce U
  refine ⟨p.map f.toHom,hp.map f.injective,?_,?_⟩
  · change d * (p.map f.toHom).length < 3*Fintype.card V
    simp only [Walk.length_map]
    exact hlen.trans_le (Nat.mul_le_mul_left 3 (Fintype.card_le_of_injective
      (fun x :U=> x.val) Subtype.val_injective))
  · intro x hx
    change x ∈ (p.map f.toHom).support at hx
    rw [Walk.support_map,List.mem_map] at hx
    obtain ⟨y,_,hy⟩ :=hx
    subst x
    exact y.property
end Erdos556
end d1
section d8
namespace Erdos556
open SimpleGraph
theorem uX {V:Type*} {G:SimpleGraph V}
    {v:V} (p:G.Walk v v) (hp:Odd p.length) :
    ∃ (w:V) (q:G.Walk w w),q.IsCycle ∧ Odd q.length ∧ q.length ≤ p.length:=by
  classical
  let P (m:ℕ) : Prop:= ∃ (w:V) (q:G.Walk w w),Odd q.length ∧ q.length=m
  have hex: ∃ m,P m:= ⟨p.length,v,p,hp,rfl⟩
  obtain ⟨w,q,hodd,hlen⟩ :=Nat.find_spec hex
  have hmin {z:V} (r:G.Walk z z) (hr:Odd r.length) : q.length ≤ r.length:=by
    rw [hlen]
    exact Nat.find_min' hex ⟨z,r,hr,rfl⟩
  have hnotnil: ¬ q.Nil:=by
    rw [Walk.not_nil_iff_lt_length]
    have hmod:=Nat.odd_iff.mp hodd
    omega
  have htail:q.tail.IsPath:=by
    apply Walk.isPath_iff_isSubwalk_imp_nil.mpr
    intro z r hr
    by_contra hrnil
    have hrpos:0 < r.length:=Walk.not_nil_iff_lt_length.mp hrnil
    have hrle:=Walk.length_le_of_isSubwalk hr
    rw [Walk.length_tail] at hrle
    by_cases hrodd:Odd r.length
    · have:=hmin r hrodd
      omega
    · obtain ⟨a,b,hab⟩ :=hr
      have htotal:q.length=a.length+r.length+b.length+1:=by
        have h :=congrArg Walk.length hab
        simp only [Walk.length_tail,Walk.length_append] at h
        have hpos:=Walk.not_nil_iff_lt_length.mp hnotnil
        omega
      let s :=Walk.cons (q.adj_snd hnotnil) (a.append b)
      have hslen:s.length=a.length+b.length+1:=by
        simp only [s,Walk.length_cons,Walk.length_append]
      have hsodd:Odd s.length:=by
        have hqmod:=Nat.odd_iff.mp hodd
        have hrmod:=Nat.even_iff.mp (Nat.not_odd_iff_even.mp hrodd)
        apply Nat.odd_iff.mpr
        omega
      have:=hmin s hsodd
      omega
  have hthree:3 ≤ q.length:=by
    have hne:q.length ≠ 1:=fun h => (Walk.adj_of_length_eq_one h).ne rfl
    have hmod:=Nat.odd_iff.mp hodd
    omega
  exact ⟨w,q,Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨htail,hthree⟩,
    hodd,hmin p hp⟩
theorem xJ {V:Type*} (G:SimpleGraph V) :
    G.Colorable 2 ↔ ∀ (v:V) (p:G.Walk v v),p.IsCycle → ¬ Odd p.length:=by
  rw [two_colorable_iff_forall_loop_even]
  constructor
  · intro h v p _ ho
    exact (Nat.not_even_iff_odd.mpr ho) (h v p)
  · intro h v p
    apply Nat.not_odd_iff_even.mp
    intro ho
    obtain ⟨w,q,hq,hodd,_⟩ :=uX p ho
    exact h w q hq hodd
theorem tr {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (hconn:G.Connected)
    (hnonbip: ¬ G.Colorable 2) (d:ℕ) (hd:0 < d)
    (hdeg: ∀ v,d ≤ G.degree v) :
    ∃ (w:V) (q:G.Walk w w),q.IsCycle ∧ Odd q.length ∧
      d*q.length < 6*Fintype.card V +d:=by
  classical
  let root:V:=Classical.choice hconn.nonempty
  let f (v:V) : Fin 2 := ⟨G.dist root v %2,Nat.mod_lt _ (by decide)⟩
  have hex: ∃ a b,G.Adj a b ∧ f a =f b:=by
    by_contra h
    push Not at h
    apply hnonbip
    exact ⟨{ toFun:=f,map_rel':=fun {a b} hab=> h a b hab}⟩
  obtain ⟨a,b,hab,hpar⟩ :=hex
  obtain ⟨pa,_,hpa⟩ :=hconn.exists_path_of_dist root a
  obtain ⟨pb,_,hpb⟩ :=hconn.exists_path_of_dist root b
  have hshort {x y :V} (r:G.Walk x y) (hr:r.length=G.dist x y) :
      d*r.length < 3*Fintype.card V :=by
    have hc:=sU G r hr d hdeg
    have hlen:r.length < 3* (r.length/3+1) :=by omega
    nlinarith
  have ha:=hshort pa hpa
  have hb:=hshort pb hpb
  let p := (pa.concat hab).append pb.reverse
  have hlen:p.length=pa.length+1+pb.length:=by
    simp only [p,Walk.length_append,Walk.length_concat,Walk.length_reverse]
  have hodd:Odd p.length:=by
    have heq:=congrArg Fin.val hpar
    change G.dist root a %2=G.dist root b %2 at heq
    rw [← hpa,← hpb] at heq
    apply Nat.odd_iff.mpr
    omega
  have hbound:d*p.length < 6*Fintype.card V +d:=by nlinarith
  obtain ⟨w,q,hq,hqodd,hqle⟩ :=uX p hodd
  exact ⟨w,q,hq,hqodd,(Nat.mul_le_mul_left d hqle).trans_lt hbound⟩
end Erdos556
end d8
section cP
namespace Erdos556
open SimpleGraph
def qT {V:Type*} (G:SimpleGraph V) (b:ℕ) : Prop:=
  ∀ S :Finset V,S.card ≤ b → ¬ (G.induce (S:Set V)ᶜ).Colorable 2
theorem z3 {V:Type*} (G:SimpleGraph V)
    (h: ¬ G.Colorable 2) : Nonempty V :=by
  by_contra hn
  have:IsEmpty V :=not_nonempty_iff.mp hn
  apply h
  refine ⟨{ toFun:=fun x => isEmptyElim x,map_rel':= ?_}⟩
  intro x
  exact isEmptyElim x
theorem xA {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d :ℕ)
    (hconn:q8 G b) (hnonbip:qT G b)
    (hd:0 < d) (hdeg: ∀ w,d+b ≤ G.degree w)
    (S:Finset V) (hS:S.card ≤ b) :
    ∃ (w:V) (c:G.Walk w w),c.IsCycle ∧ Odd c.length ∧
      d*c.length < 6*Fintype.card V +d ∧ ∀ x ∈ c.support,x ∉ S:=by
  classical
  let U := (S:Set V)ᶜ
  have hnb: ¬ (G.induce U).Colorable 2 :=hnonbip S hS
  have:Nonempty U :=z3 _ hnb
  have hc: (G.induce U).Connected:= ⟨hconn S hS⟩
  have hmin (v:U) : d ≤ (G.induce U).degree v :=by
    have h :=qW G S v
    have hg:=hdeg v.val
    change G.degree v.val ≤ (G.induce U).degree v +S.card at h
    omega
  obtain ⟨w,c,hcyc,hodd,hlen⟩ :=tr (G.induce U) hc hnb d hd hmin
  let f :G.induce U ↪g G :=SimpleGraph.Embedding.induce U
  refine ⟨f w,c.map f.toHom,hcyc.map f.injective,?_,?_,?_⟩
  · simpa only [Walk.length_map] using hodd
  · simp only [Walk.length_map]
    have hcard:=Fintype.card_le_of_injective (fun x :U=> x.val) Subtype.val_injective
    omega
  · intro x hx
    rw [Walk.support_map,List.mem_map] at hx
    obtain ⟨y,_,hy⟩ :=hx
    subst x
    exact y.property
end Erdos556
end cP
section cT
namespace Erdos556
open SimpleGraph Finset
theorem wX {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d D:ℕ)
    (hconn:q8 G b) (hd:0 < d)
    (hdeg: ∀ w,d+b ≤ G.degree w) (hN:Fintype.card V ≤ D *d)
    (S:Finset V) (hbudget:S.card+3*D+1 ≤ b)
    (C:Set V) (hC:C.Nontrivial) (hCS: ∀ z ∈ C,z ∉ S)
    (u v :V) (hu:u ∉ S) (hv:v ∉ S) (huv:u ≠ v) :
    ∃ x ∈ C,∃ y ∈ C,∃ (p:G.Walk u x) (q:G.Walk v y),
      p.IsPath ∧ q.IsPath ∧ p.length < 3*D ∧ q.length < 3*D ∧ x ≠ y ∧
      (∀ z ∈ p.support,z ∈ C → z=x) ∧
      (∀ z ∈ q.support,z ∈ C → z=y) ∧
      (∀ z ∈ p.support,z ∉ q.support) ∧
      (∀ z ∈ p.support,z ∉ S) ∧ (∀ z ∈ q.support,z ∉ S) :=by
  classical
  obtain ⟨w,hwC,hwv⟩ :=hC.exists_ne v
  have hfirst: (insert v S).card ≤ b:= (card_insert_le v S).trans (by omega)
  obtain ⟨p',hp',hplen,hpavoid⟩ :=sB G b d hconn hd hdeg
    (insert v S) hfirst u w (by simpa using And.intro huv hu)
    (by simpa using And.intro hwv (hCS w hwC))
  obtain ⟨x,hxC,p,hp,hpp',hpsub,hpC⟩ :=rq p' hp' C hwC
  have hpbound:p.length < 3*D:=by nlinarith
  have hpav (z:V) (hz:z ∈ p.support) : z ∉ insert v S:=
    hpavoid z (hpsub hz)
  have hpcard:p.support.toFinset.card ≤ 3*D:=by
    have hcard:=List.toFinset_card_le p.support
    rw [p.length_support] at hcard
    omega
  let T :=S ∪ p.support.toFinset
  have hT:T.card ≤ b:= (card_union_le S p.support.toFinset).trans (by omega)
  obtain ⟨z,hzC,hzx⟩ :=hC.exists_ne x
  have hzT:z ∉ T:=by
    simp only [T,mem_union,List.mem_toFinset,not_or]
    exact ⟨hCS z hzC,fun h => hzx (hpC z h hzC)⟩
  have hvT:v ∉ T:=by
    simp only [T,mem_union,List.mem_toFinset,not_or]
    exact ⟨hv,fun h => hpav v h (mem_insert_self v S)⟩
  obtain ⟨q',hq',hqlen,hqavoid⟩ :=sB G b d hconn hd hdeg
    T hT v z hvT hzT
  obtain ⟨y,hyC,q,hq,hqq',hqsub,hqC⟩ :=rq q' hq' C hzC
  have hqbound:q.length < 3*D:=by nlinarith
  have hqav (z:V) (hz:z ∈ q.support) : z ∉ T:=hqavoid z (hqsub hz)
  have hpq (z:V) (hzp:z ∈ p.support) (hzq:z ∈ q.support) : False:=
    hqav z hzq (mem_union_right S (List.mem_toFinset.mpr hzp))
  have hxy:x ≠ y:=by
    intro h
    exact hpq x p.end_mem_support (h ▸ q.end_mem_support)
  refine ⟨x,hxC,y,hyC,p,q,hp,hq,hpbound,hqbound,hxy,hpC,hqC,hpq,?_,?_⟩
  · intro z hz hzS
    exact hpav z hz (mem_insert_of_mem hzS)
  · intro z hz hzS
    exact hqav z hz (mem_union_left _ hzS)
end Erdos556
end cT
section da
namespace Erdos556
open SimpleGraph
theorem zH {V:Type*} {G:SimpleGraph V}
    {w:V} (c:G.Walk w w) (hc:c.IsCycle) (hodd:Odd c.length)
    (u v :V) (hu:u ∈ c.support) (hv:v ∈ c.support) (huv:u ≠ v) :
    ∃ p q:G.Walk u v,p.IsPath ∧ q.IsPath ∧
      p.length+q.length=c.length ∧ p.length%2 ≠ q.length%2 ∧
      p.support ⊆ c.support ∧ q.support ⊆ c.support:=by
  classical
  let r :=c.rotate u hu
  have hr:r.IsCycle:=hc.rotate hu
  have hvr:v ∈ r.support:= (c.mem_support_rotate_iff u hu).mpr hv
  let p :=r.takeUntil v hvr
  let s :=r.dropUntil v hvr
  have hp:p.IsPath:=hr.isPath_takeUntil hvr
  have hs:s.IsPath:=by
    have hcycle: (p.append s).IsCycle:=by
      simpa only [p,s,Walk.take_spec] using hr
    exact hcycle.isPath_of_append_right (Walk.not_nil_of_ne huv)
  have hlen:p.length+s.reverse.length=c.length:=by
    have h :=congrArg Walk.length (r.take_spec hvr)
    simpa only [Walk.length_append,r,Walk.length_rotate,Walk.length_reverse] using h
  refine ⟨p,s.reverse,hp,hs.reverse,hlen,?_,?_,?_⟩
  · have ho:=Nat.odd_iff.mp hodd
    omega
  · intro x hx
    exact (c.mem_support_rotate_iff u hu).mp (r.support_takeUntil_subset_support hvr hx)
  · intro x hx
    rw [Walk.support_reverse,List.mem_reverse] at hx
    exact (c.mem_support_rotate_iff u hu).mp (r.support_dropUntil_subset_support hvr hx)
theorem rE {V:Type*} {G:SimpleGraph V}
    {w u v x y:V} (c:G.Walk w w) (hc:c.IsCycle) (hodd:Odd c.length)
    (p:G.Walk u x) (q:G.Walk v y) (hp:p.IsPath) (hq:q.IsPath)
    (hx:x ∈ c.support) (hy:y ∈ c.support) (hxy:x ≠ y)
    (hpC: ∀ z ∈ p.support,z ∈ c.support → z=x)
    (hqC: ∀ z ∈ q.support,z ∈ c.support → z=y)
    (hpq: ∀ z ∈ p.support,z ∉ q.support) :
    ∃ p₀ p₁:G.Walk u v,p₀.IsPath ∧ p₁.IsPath ∧
      p₀.length%2 ≠ p₁.length%2 ∧
      p₀.length ≤ p.length+q.length+c.length ∧
      p₁.length ≤ p.length+q.length+c.length ∧
      (∀ z ∈ p₀.support,z ∈ p.support ∨ z ∈ q.support ∨ z ∈ c.support) ∧
      (∀ z ∈ p₁.support,z ∈ p.support ∨ z ∈ q.support ∨ z ∈ c.support) :=by
  obtain ⟨a,b,ha,hb,hlen,hpar,haC,hbC⟩ :=
    zH c hc hodd x y hx hy hxy
  have hpath (r:G.Walk x y) (hr:r.IsPath) (hrC:r.support ⊆ c.support) :
      ((p.append r).append q.reverse).IsPath:=by
    have hpr:=qr p r hp hr
      (fun z hz hzr=> hpC z hz (hrC hzr))
    apply qr (p.append r) q.reverse hpr hq.reverse
    intro z hz hzq
    rw [Walk.support_reverse,List.mem_reverse] at hzq
    rcases (Walk.mem_support_append_iff _ _).mp hz with hzp | hzr
    · exact (hpq z hzp hzq).elim
    · exact hqC z hzq (hrC hzr)
  have hsupport (r:G.Walk x y) (hrC:r.support ⊆ c.support) (z:V)
      (hz:z ∈ ((p.append r).append q.reverse).support) :
      z ∈ p.support ∨ z ∈ q.support ∨ z ∈ c.support:=by
    rcases (Walk.mem_support_append_iff _ _).mp hz with hzpr | hzq
    · rcases (Walk.mem_support_append_iff _ _).mp hzpr with hzp | hzr
      · exact Or.inl hzp
      · exact Or.inr (Or.inr (hrC hzr))
    · exact Or.inr (Or.inl (by simpa only [Walk.support_reverse,List.mem_reverse] using hzq))
  refine ⟨(p.append a).append q.reverse,(p.append b).append q.reverse,
    hpath a ha haC,hpath b hb hbC,?_,?_,?_,hsupport a haC,hsupport b hbC⟩
  · simp only [Walk.length_append,Walk.length_reverse]
    omega
  · simp only [Walk.length_append,Walk.length_reverse]
    omega
  · simp only [Walk.length_append,Walk.length_reverse]
    omega
end Erdos556
end da
section dz
namespace Erdos556
open SimpleGraph Finset
def qZ {V:Type*} (G:SimpleGraph V) (L:ℕ) (u v :V)
    (S:Finset V) : Prop:=
  ∀ r :Fin 2,∃ p:G.Walk u v,p.IsPath ∧ p.length ≤ L ∧ p.length%2=r.val ∧
    ∀ x ∈ p.support,x ≠ u → x ≠ v → x ∈ S
theorem qZ.mono {V:Type*} {G:SimpleGraph V} {L:ℕ} {u v :V}
    {S T :Finset V} (h:qZ G L u v S) (hST:S ⊆ T) :
    qZ G L u v T :=by
  intro r
  obtain ⟨p,hp,hlen,hpar,hs⟩ :=h r
  exact ⟨p,hp,hlen,hpar,fun x hx hxu hxv=> hST (hs x hx hxu hxv)⟩
theorem vz {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d D:ℕ)
    (hconn:q8 G (b+3*D+3))
    (hnonbip:qT G (b+3*D+3))
    (hd:0 < d) (hdeg: ∀ w,d+ (b+3*D+3) ≤ G.degree w)
    (hN:Fintype.card V ≤ D *d) (u v :V) (huv:u ≠ v)
    (S:Finset V) (hS:S.card ≤ b) :
    ∃ T :Finset V,qZ G (12*D+3) u v T ∧
      T.card ≤ 12*D+3 ∧ Disjoint S T:=by
  classical
  let S₀:= (S.erase u).erase v
  have hS₀:S₀.card ≤ b:=
    (card_le_card ((erase_subset v (S.erase u)).trans (erase_subset u S))).trans hS
  let F :=insert u (insert v S₀)
  have hF:F.card ≤ b+3*D+3:=by
    have h1:=card_insert_le u (insert v S₀)
    have h2:=card_insert_le v S₀
    dsimp [F]
    omega
  obtain ⟨w,c,hc,hodd,hclen,hcav⟩ :=xA G
    (b+3*D+3) d hconn hnonbip hd hdeg F hF
  have hcshort:c.length ≤ 6*D:=by nlinarith
  let C :Set V := {z | z ∈ c.support}
  have hC:C.Nontrivial:=by
    refine ⟨w,c.start_mem_support,c.snd,?_,(c.adj_snd hc.not_nil).ne⟩
    exact List.mem_of_mem_tail (Walk.snd_mem_tail_support hc.not_nil)
  have hCS (z:V) (hz:z ∈ C) : z ∉ S₀:=by
    intro hzS
    exact hcav z hz (mem_insert_of_mem (mem_insert_of_mem hzS))
  obtain ⟨x,hxC,y,hyC,p,q,hp,hq,hplen,hqlen,hxy,hpC,hqC,hpq,hpav,hqav⟩ :=
    wX G (b+3*D+3) d D hconn hd hdeg hN
      S₀ (by omega) C hC hCS u v (by simp [S₀]) (by simp [S₀]) huv
  obtain ⟨p₀,p₁,hp₀,hp₁,hpar,hlen₀,hlen₁,hs₀,hs₁⟩ :=
    rE c hc hodd p q hp hq hxC hyC hxy hpC hqC hpq
  let U := (p.support.toFinset ∪ q.support.toFinset) ∪ c.support.toFinset
  let T := (U.erase u).erase v
  have hmem {z:V} (hz:z ∈ p.support ∨ z ∈ q.support ∨ z ∈ c.support)
      (hzu:z ≠ u) (hzv:z ≠ v) : z ∈ T:=by
    simp only [T,U,mem_erase,mem_union,List.mem_toFinset]
    exact ⟨hzv,hzu,by tauto⟩
  have hTsize:T.card ≤ 12*D+3:=by
    have hTle:T.card ≤ U.card:=
      card_le_card ((erase_subset v (U.erase u)).trans (erase_subset u U))
    have hUle:U.card ≤ p.support.toFinset.card+q.support.toFinset.card+
        c.support.toFinset.card:=
      (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    have hpcard:=List.toFinset_card_le p.support
    have hqcard:=List.toFinset_card_le q.support
    have hccard:=List.toFinset_card_le c.support
    rw [p.length_support] at hpcard
    rw [q.length_support] at hqcard
    rw [c.length_support] at hccard
    omega
  have hST:Disjoint S T:=by
    rw [Finset.disjoint_left]
    intro z hzS hzT
    simp only [T,U,mem_erase,mem_union,List.mem_toFinset] at hzT
    have hzS₀:z ∈ S₀:=by
      simp only [S₀,mem_erase]
      exact ⟨hzT.1,hzT.2.1,hzS⟩
    rcases hzT.2.2 with (hzp | hzq) | hzc
    · exact hpav z hzp hzS₀
    · exact hqav z hzq hzS₀
    · exact hCS z hzc hzS₀
  refine ⟨T,?_,hTsize,hST⟩
  intro r
  by_cases h :p₀.length%2=r.val
  · exact ⟨p₀,hp₀,by omega,h,fun z hz hzu hzv=> hmem (hs₀ z hz) hzu hzv⟩
  · have hr:p₁.length%2=r.val:=by have:=r.isLt;omega
    exact ⟨p₁,hp₁,by omega,hr,fun z hz hzu hzv=> hmem (hs₁ z hz) hzu hzv⟩
end Erdos556
end dz
section cw
/-
Copyright 2026 The Lean-Proofs Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Elementary finite Bernoulli sampling
This self-contained finite-sum development is adapted from the proved
Bernoulli counting lemmas in `Erdos76/Kahn.lean` and
`Erdos76/FiniteBernoulliLocality.lean`. No local lemma or hypergraph theorem
is imported or assumed.
-/
namespace Erdos556.Bernoulli
open Finset
open scoped BigOperators
noncomputable section
open scoped Classical
def qv {Ω:Type*} [Fintype Ω] (mass:Ω → ℝ) (event:Ω → Prop) : ℝ:=
  ∑ x,if event x then mass x else 0
variable {E:Type*} [DecidableEq E]
def q9 (U:Finset E) (p:E → ℝ) (S:Finset E) : ℝ:=
  (∏ e ∈ S,p e) * ∏ e ∈ U \ S,(1-p e)
lemma yC (U:Finset E) (p:E → ℝ) :
    ∑ S ∈ U.powerset,q9 U p S =1:=by
  simp only [q9]
  rw [← prod_add]
  simp
lemma tO {U S :Finset E} {p:E → ℝ}
    (hS:S ⊆ U) (hp₀: ∀ e ∈ U,0 ≤ p e) (hp₁: ∀ e ∈ U,p e ≤ 1) :
    0 ≤ q9 U p S :=by
  apply mul_nonneg
  · exact prod_nonneg fun e he ↦ hp₀ e (hS he)
  · exact prod_nonneg fun e he ↦ sub_nonneg.mpr (hp₁ e (mem_sdiff.mp he).1)
lemma tS {U T :Finset E} {p:E → ℝ} {e:E}
    (_heU:e ∈ U) (hT:T ⊆ U.erase e) :
    q9 U p (insert e T) = p e *q9 (U.erase e) p T:=by
  have heT:e ∉ T:=by
    intro he
    exact (mem_erase.mp (hT he)).1 rfl
  have hdiff:U \ insert e T=U.erase e \ T :=by
    ext x
    simp only [mem_sdiff,mem_insert,mem_erase]
    tauto
  simp only [q9,prod_insert heT,hdiff]
  ring
lemma zn {U:Finset E} {p:E → ℝ} {e:E} (heU:e ∈ U) :
    ∑ S ∈ U.powerset with e ∈ S,q9 U p S =p e:=by
  have hsets:U.powerset.filter (fun S ↦ e ∈ S) =
      (U.erase e).powerset.image (insert e) :=by
    ext S
    simp only [mem_filter,mem_powerset,mem_image]
    constructor
    · rintro ⟨hSU,heS⟩
      refine ⟨S.erase e,?_,?_⟩
      · intro x hx
        obtain ⟨hxe,hxS⟩ :=mem_erase.mp hx
        exact mem_erase.mpr ⟨hxe,hSU hxS⟩
      · simpa using insert_erase heS
    · rintro ⟨T,hT,rfl⟩
      exact ⟨insert_subset heU (hT.trans (erase_subset _ _)),mem_insert_self _ _⟩
  rw [hsets,sum_image]
  · calc
      ∑ T ∈ (U.erase e).powerset,q9 U p (insert e T) =
          ∑ T ∈ (U.erase e).powerset,p e*q9 (U.erase e) p T:=by
        apply sum_congr rfl
        intro T hT
        exact tS heU (mem_powerset.mp hT)
      _=p e* ∑ T ∈ (U.erase e).powerset,q9 (U.erase e) p T:=by
        rw [mul_sum]
      _=p e:=by rw [yC,mul_one]
  · intro A hA B hB hAB
    have heA:e ∉ A:=by
      intro heA
      exact (mem_erase.mp ((mem_powerset.mp hA) heA)).1 rfl
    have heB:e ∉ B:=by
      intro heB
      exact (mem_erase.mp ((mem_powerset.mp hB) heB)).1 rfl
    simpa [heA,heB] using congrArg (fun S :Finset E ↦ S.erase e) hAB
lemma yc (U:Finset E) (p:E → ℝ) :
    ∑ S ∈ U.powerset,q9 U p S * (S.card:ℝ) = ∑ e ∈ U,p e:=by
  calc
    ∑ S ∈ U.powerset,q9 U p S * (S.card:ℝ) =
        ∑ S ∈ U.powerset,∑ e ∈ U,if e ∈ S then q9 U p S else 0 :=by
      apply sum_congr rfl
      intro S hS
      rw [← sum_filter]
      have hfilter:U.filter (fun e ↦ e ∈ S) = S:=by
        ext e
        simp only [mem_filter]
        constructor
        · exact fun h ↦ h.2
        · intro heS
          exact ⟨(mem_powerset.mp hS) heS,heS⟩
      rw [hfilter]
      simp [mul_comm]
    _= ∑ e ∈ U,∑ S ∈ U.powerset,
          if e ∈ S then q9 U p S else 0 :=by rw [sum_comm]
    _= ∑ e ∈ U,p e:=by
      apply sum_congr rfl
      intro e heU
      rw [← sum_filter,zn heU]
variable [Fintype E]
def AgreesOn (R S T:Finset E) : Prop:=S ∩ R=T ∩ R
def qP (R:Finset E) (event:Finset E → Prop) : Prop:=
  ∀ S T,AgreesOn R S T → (event S ↔ event T)
omit [Fintype E] in
lemma xY {R R' S T:Finset E} (hRR':R ⊆ R')
    (h:AgreesOn R' S T) : AgreesOn R S T :=by
  unfold AgreesOn at h ⊢
  ext e
  have hmem:e ∈ S ∩ R' ↔ e ∈ T ∩ R':=by rw [h]
  simp only [mem_inter] at hmem ⊢
  constructor
  · rintro ⟨heS,heR⟩
    exact ⟨(hmem.mp ⟨heS,hRR' heR⟩).1,heR⟩
  · rintro ⟨heT,heR⟩
    exact ⟨(hmem.mpr ⟨heT,hRR' heR⟩).1,heR⟩
omit [Fintype E] in
lemma a9 (R:Finset E) : qP R (fun _ ↦ True) :=by
  intro S T hST
  simp
omit [Fintype E] in
lemma av {R T :Finset E} {A B :Finset E → Prop}
    (hA:qP R A) (hB:qP T B) :
    qP (R ∪ T) (fun S ↦ A S ∧ B S) :=by
  intro S V hSV
  have hR:AgreesOn R S V :=xY subset_union_left hSV
  have hT:AgreesOn T S V :=xY subset_union_right hSV
  exact and_congr (hA S V hR) (hB S V hT)
abbrev Subsets (U:Finset E) := {S:Finset E //S ⊆ U}
def y1 (U:Finset E) :
    Subsets U ≃ ↥U.powerset:=
  Equiv.subtypeEquivRight (by intro S;simp)
def t4:Subsets (Finset.univ:Finset E) ≃ Finset E where
  toFun S :=S.1
  invFun S := ⟨S,subset_univ S⟩
  left_inv _S:=Subtype.ext rfl
  right_inv _S:=rfl
def tT {U V :Finset E} (hUV:Disjoint U V) :
    Subsets (U ∪ V) ≃ Subsets U × Subsets V where
  toFun S :=
    (⟨S.1 ∩ U,inter_subset_right⟩,⟨S.1 ∩ V,inter_subset_right⟩)
  invFun P := ⟨P.1.1 ∪ P.2.1,union_subset_union P.1.2 P.2.2⟩
  left_inv S :=by
    apply Subtype.ext
    ext e
    simp only [mem_union,mem_inter]
    constructor
    · intro h
      rcases h with h | h
      · exact h.1
      · exact h.1
    · intro heS
      have hsplit:e ∈ U ∨ e ∈ V:=by
        simpa only [mem_union] using S.2 heS
      rcases hsplit with heU | heV
      · exact Or.inl ⟨heS,heU⟩
      · exact Or.inr ⟨heS,heV⟩
  right_inv P :=by
    rcases P with ⟨A,B⟩
    apply Prod.ext
    · apply Subtype.ext
      ext e
      simp only [mem_inter,mem_union]
      constructor
      · rintro ⟨heA | heB,heU⟩
        · exact heA
        · exact False.elim ((Finset.disjoint_left.mp hUV) heU (B.2 heB))
      · intro heA
        exact ⟨Or.inl heA,A.2 heA⟩
    · apply Subtype.ext
      ext e
      simp only [mem_inter,mem_union]
      constructor
      · rintro ⟨heA | heB,heV⟩
        · exact False.elim ((Finset.disjoint_left.mp hUV) (A.2 heA) heV)
        · exact heB
      · intro heB
        exact ⟨Or.inr heB,B.2 heB⟩
def qo (U:Finset E) (p:E → ℝ) (event:Finset E → Prop) : ℝ:=
  ∑ S :Subsets U,if event S.1 then q9 U p S.1 else 0
lemma zp (U:Finset E) (p:E → ℝ) :
    ∑ S :Subsets U,q9 U p S.1=1:=by
  calc
    (∑ S :Subsets U,q9 U p S.1) =
        ∑ S : ↥U.powerset,q9 U p S.1:=by
      apply Fintype.sum_equiv (y1 U)
      intro S
      rfl
    _= ∑ S ∈ U.powerset,q9 U p S :=by
      simpa using
        (Finset.sum_attach U.powerset
          (fun S :Finset E ↦ q9 U p S))
    _=1:=yC U p
lemma wh (U:Finset E) (p:E → ℝ) :
    qo U p (fun _ ↦ True) = 1:=by
  unfold qo
  simpa using zp U p
lemma s1 (p:E → ℝ)
    (event:Finset E → Prop) :
    qv
        (fun S :Finset E ↦ q9 Finset.univ p S) event=
      qo Finset.univ p event:=by
  unfold qv qo
  symm
  apply Fintype.sum_equiv t4
  intro S
  by_cases h :event S.1 <;> simp [h,t4]
omit [Fintype E] in
lemma xy {U V A B :Finset E} {p:E → ℝ}
    (hUV:Disjoint U V) (hA:A ⊆ U) (hB:B ⊆ V) :
    q9 (U ∪ V) p (A ∪ B) =
      q9 U p A *q9 V p B :=by
  have hAB:Disjoint A B:=hUV.mono hA hB
  have hdiff: (U ∪ V) \ (A ∪ B) = (U \ A) ∪ (V \ B) :=by
    ext e
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨heU | heV,hnot⟩
      · exact Or.inl ⟨heU,fun heA ↦ hnot (Or.inl heA)⟩
      · exact Or.inr ⟨heV,fun heB ↦ hnot (Or.inr heB)⟩
    · rintro (⟨heU,heA⟩ | ⟨heV,heB⟩)
      · refine ⟨Or.inl heU,?_⟩
        rintro (hAe | hBe)
        · exact heA hAe
        · exact (Finset.disjoint_left.mp hUV) heU (hB hBe)
      · refine ⟨Or.inr heV,?_⟩
        rintro (hAe | hBe)
        · exact (Finset.disjoint_left.mp hUV) (hA hAe) heV
        · exact heB hBe
  have hdiffDisj:Disjoint (U \ A) (V \ B) :=
    hUV.mono sdiff_subset sdiff_subset
  simp only [q9,prod_union hAB,hdiff,prod_union hdiffDisj]
  ring
lemma sk {U V :Finset E} {p:E → ℝ}
    {A B :Finset E → Prop} (hUV:Disjoint U V)
    (hA:qP U A) (hB:qP V B) :
    qo (U ∪ V) p (fun S ↦ A S ∧ B S) =
      qo U p A *qo V p B :=by
  let split:Subsets (U ∪ V) ≃ Subsets U × Subsets V :=
    tT hUV
  let summand:Subsets (U ∪ V) → ℝ:=fun S ↦
    if A S.1 ∧ B S.1 then q9 (U ∪ V) p S.1 else 0
  calc
    qo (U ∪ V) p (fun S ↦ A S ∧ B S) =
        ∑ S :Subsets (U ∪ V),summand S :=by
      unfold qo
      apply sum_congr rfl
      intro S _
      by_cases h :A S.1 ∧ B S.1 <;> simp [summand,h]
    _= ∑ P:Subsets U × Subsets V,summand (split.symm P) :=by
      apply Fintype.sum_equiv split
      intro S
      simp only [Equiv.symm_apply_apply]
    _= ∑ X:Subsets U,∑ Y:Subsets V,summand (split.symm (X,Y)) :=by
      rw [Fintype.sum_prod_type]
    _= ∑ X:Subsets U,∑ Y:Subsets V,
        (if A X.1 then q9 U p X.1 else 0) *
          (if B Y.1 then q9 V p Y.1 else 0) :=by
      apply sum_congr rfl
      intro X _
      apply sum_congr rfl
      intro Y _
      have hsplit: (split.symm (X,Y)).1=X.1 ∪ Y.1:=rfl
      have hAgreeA:AgreesOn U (X.1 ∪ Y.1) X.1:=by
        unfold AgreesOn
        ext e
        simp only [mem_inter,mem_union]
        constructor
        · rintro ⟨heX | heY,heU⟩
          · exact ⟨heX,X.2 heX⟩
          · exact False.elim ((Finset.disjoint_left.mp hUV) heU (Y.2 heY))
        · rintro ⟨heX,heU⟩
          exact ⟨Or.inl heX,heU⟩
      have hAgreeB:AgreesOn V (X.1 ∪ Y.1) Y.1:=by
        unfold AgreesOn
        ext e
        simp only [mem_inter,mem_union]
        constructor
        · rintro ⟨heX | heY,heV⟩
          · exact False.elim ((Finset.disjoint_left.mp hUV) (X.2 heX) heV)
          · exact ⟨heY,Y.2 heY⟩
        · rintro ⟨heY,heV⟩
          exact ⟨Or.inr heY,heV⟩
      have hAE:A (X.1 ∪ Y.1) ↔ A X.1:=hA _ _ hAgreeA
      have hBE:B (X.1 ∪ Y.1) ↔ B Y.1:=hB _ _ hAgreeB
      rw [show summand (split.symm (X,Y)) =
          if A (X.1 ∪ Y.1) ∧ B (X.1 ∪ Y.1) then
            q9 (U ∪ V) p (X.1 ∪ Y.1) else 0 by
              change (if A (split.symm (X,Y)).1 ∧ B (split.symm (X,Y)).1 then
                q9 (U ∪ V) p (split.symm (X,Y)).1 else 0) = _
              rw [hsplit]]
      rw [xy hUV X.2 Y.2]
      by_cases hAX:A X.1 <;> by_cases hBY:B Y.1 <;>
        simp_all
    _= (∑ X :Subsets U,if A X.1 then q9 U p X.1 else 0) *
        ∑ Y :Subsets V,if B Y.1 then q9 V p Y.1 else 0 :=by
      rw [sum_mul]
      apply sum_congr rfl
      intro X _
      rw [mul_sum]
    _=qo U p A *qo V p B :=by
      rfl
lemma r9 {R:Finset E} {p:E → ℝ}
    {event:Finset E → Prop} (hlocal:qP R event) :
    qv
        (fun S :Finset E ↦ q9 Finset.univ p S) event=
      qo R p event:=by
  calc
    qv
        (fun S :Finset E ↦ q9 Finset.univ p S) event=
        qo Finset.univ p event:=
      s1 p event
    _=qo R p event:=by
      have hfactor:=sk
        (p:=p) (U:=R) (V:=Finset.univ \ R)
        (A:=event) (B:=fun _ ↦ True) Finset.disjoint_sdiff hlocal
        (a9 (Finset.univ \ R))
      have hcover:R ∪ (Finset.univ \ R) = (Finset.univ:Finset E) :=
        union_sdiff_of_subset (subset_univ R)
      rw [hcover] at hfactor
      simpa [wh] using hfactor
theorem yz {R T :Finset E} {p:E → ℝ}
    {A B :Finset E → Prop} (hRT:Disjoint R T)
    (hA:qP R A) (hB:qP T B) :
    qv
        (fun S :Finset E ↦ q9 Finset.univ p S)
        (fun S ↦ A S ∧ B S) =
      qv
          (fun S :Finset E ↦ q9 Finset.univ p S) A *
        qv
          (fun S :Finset E ↦ q9 Finset.univ p S) B :=by
  calc
    qv
        (fun S :Finset E ↦ q9 Finset.univ p S)
        (fun S ↦ A S ∧ B S) =
        qo (R ∪ T) p (fun S ↦ A S ∧ B S) :=
      r9 (av hA hB)
    _=qo R p A *qo T p B :=
      sk hRT hA hB
    _=qv
          (fun S :Finset E ↦ q9 Finset.univ p S) A *
        qv
          (fun S :Finset E ↦ q9 Finset.univ p S) B :=by
      rw [r9 hA,
        r9 hB]
end
end Erdos556.Bernoulli
end cw
section du
namespace Erdos556.Bernoulli
open Finset
open scoped BigOperators
noncomputable section
open scoped Classical
theorem dN {Ω:Type*} [Fintype Ω] (mass:Ω → ℝ)
    (hsum: ∑ x,mass x =1) (A:Ω → Prop) :
    qv mass (fun x => ¬ A x) = 1-qv mass A :=by
  have hsplit:qv mass A +qv mass (fun x => ¬ A x) = 1:=by
    unfold qv
    rw [← sum_add_distrib,← hsum]
    apply sum_congr rfl
    intro x _
    by_cases ha:A x <;> simp [ha]
  linarith
theorem bu {Ω:Type*} [Fintype Ω] (mass:Ω → ℝ)
    (hmass: ∀ x,0 ≤ mass x) (A B :Ω → Prop) :
    qv mass (fun x => A x ∨ B x) ≤ qv mass A +qv mass B :=by
  unfold qv
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases ha:A x <;> by_cases hb:B x <;> simp [ha,hb,hmass x]
theorem a5 {Ω I :Type*} [Fintype Ω] [Fintype I]
    (mass:Ω → ℝ) (hmass: ∀ x,0 ≤ mass x) (A:I → Ω → Prop) :
    qv mass (fun x => ∃ i,A i x) ≤ ∑ i,qv mass (A i) :=by
  unfold qv
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  by_cases h : ∃ i,A i x
  · obtain ⟨i,hi⟩ :=h
    rw [if_pos ⟨i,hi⟩]
    have hle:=single_le_sum (s:= (univ:Finset I))
      (f:=fun j => if A j x then mass x else 0)
      (fun j _=> by split_ifs <;> simp_all) (mem_univ i)
    simpa only [if_pos hi] using hle
  · rw [if_neg h]
    apply sum_nonneg
    intro i _
    split_ifs <;> simp_all
theorem aI {Ω:Type*} [Fintype Ω]
    (mass X :Ω → ℝ) (hmass: ∀ x,0 ≤ mass x) (hX: ∀ x,0 ≤ X x) (t:ℝ) :
    t*qv mass (fun x => t < X x) ≤ ∑ x,mass x *X x:=by
  unfold qv
  rw [mul_sum]
  apply sum_le_sum
  intro x _
  by_cases hx:t < X x
  · rw [if_pos hx,mul_comm t]
    exact mul_le_mul_of_nonneg_left hx.le (hmass x)
  · rw [if_neg hx,mul_zero]
    exact mul_nonneg (hmass x) (hX x)
theorem wl {Ω:Type*} [Fintype Ω]
    (mass:Ω → ℝ) (hsum: ∑ x,mass x =1) (A:Ω → Prop)
    (hA:qv mass A < 1) : ∃ x,¬ A x:=by
  by_contra h
  push Not at h
  have heq:qv mass A =1:=by simp [qv,h,hsum]
  linarith
variable {E:Type*} [Fintype E] [DecidableEq E]
theorem uM (p:E → ℝ) :
    ∑ S :Finset E,q9 univ p S=1:=by
  have h :=s1 p (fun _ => True)
  simpa only [qv,if_true,wh] using h
omit [Fintype E] in
theorem zV (L:Finset E) : qP L (fun X => L ⊆ X) :=by
  intro X Y hXY
  unfold AgreesOn at hXY
  constructor
  · intro hLX x hxL
    have hx:x ∈ X ∩ L:=mem_inter.mpr ⟨hLX hxL,hxL⟩
    rw [hXY] at hx
    exact (mem_inter.mp hx).1
  · intro hLY x hxL
    have hx:x ∈ Y ∩ L:=mem_inter.mpr ⟨hLY hxL,hxL⟩
    rw [← hXY] at hx
    exact (mem_inter.mp hx).1
omit [Fintype E] in
theorem am {L:Finset E} {A:Finset E → Prop}
    (hA:qP L A) : qP L (fun X => ¬ A X) :=by
  intro X Y hXY
  exact not_congr (hA X Y hXY)
theorem au (p:E → ℝ) (L:Finset E) :
    qv (q9 univ p) (fun X => L ⊆ X) = ∏ e ∈ L,p e:=by
  rw [r9 (zV L)]
  unfold qo
  rw [sum_eq_single (⟨L,subset_rfl⟩ : Subsets L)]
  · simp [q9]
  · intro X _ hX
    have hn: ¬ L ⊆ X.val:=by
      intro h
      exact hX (Subtype.ext (Subset.antisymm X.property h))
    simp [hn]
  · simp
omit [Fintype E] in
theorem yf {I:Type*}
    (R:I → Finset E) (A:I → Finset E → Prop)
    (hA: ∀ i,qP (R i) (A i)) (J:Finset I) :
    qP (J.biUnion R) (fun S => ∀ i ∈ J,A i S) :=by
  classical
  intro S T hST
  constructor
  · intro h i hi
    have hsub:R i ⊆ J.biUnion R :=subset_biUnion_of_mem R hi
    exact (hA i S T (xY hsub hST)).mp (h i hi)
  · intro h i hi
    have hsub:R i ⊆ J.biUnion R :=subset_biUnion_of_mem R hi
    exact (hA i S T (xY hsub hST)).mpr (h i hi)
theorem yT {I:Type*}
    (p:E → ℝ) (R:I → Finset E) (A:I → Finset E → Prop)
    (hA: ∀ i,qP (R i) (A i)) (J:Finset I)
    (hdisj: (J:Set I).Pairwise fun i j=> Disjoint (R i) (R j)) :
    qv (q9 univ p) (fun S => ∀ i ∈ J,A i S) =
      ∏ i ∈ J,qv (q9 univ p) (A i) :=by
  classical
  revert hdisj
  induction J using Finset.induction_on with
  | empty=>
      intro _
      simp [qv,uM]
  | @insert i J hi ih=>
      intro hdisj
      have hD:Disjoint (R i) (J.biUnion R) :=by
        rw [disjoint_biUnion_right]
        intro j hj
        exact hdisj (mem_insert_self i J) (mem_insert_of_mem hj)
          (by intro h;subst j;exact hi hj)
      have hDJ: (J:Set I).Pairwise fun i j=> Disjoint (R i) (R j) :=
        hdisj.mono (subset_insert i J)
      simp only [forall_mem_insert,prod_insert hi]
      rw [yz hD (hA i)
        (yf R A hA J),ih hDJ]
theorem tH {I:Type*}
    (q:ℝ) (R:I → Finset E) (J:Finset I)
    (hdisj: (J:Set I).Pairwise fun i j=> Disjoint (R i) (R j)) :
    qv (q9 univ (fun _ :E=> q))
      (fun S => ∀ i ∈ J,¬ R i ⊆ S) = ∏ i ∈ J,(1-q^ (R i).card) :=by
  classical
  rw [yT (fun _ => q) R (fun i S=> ¬ R i ⊆ S)
    (fun i => am (zV (R i))) J hdisj]
  apply prod_congr rfl
  intro i _
  rw [dN _ (uM _) (fun S => R i ⊆ S),
    au]
  simp
theorem yQ {I:Type*}
    (q:ℝ) (hq0:0 ≤ q) (hq1:q ≤ 1) (R:I → Finset E) (J:Finset I)
    (hdisj: (J:Set I).Pairwise fun i j=> Disjoint (R i) (R j)) (L:ℕ)
    (hsize: ∀ i ∈ J,(R i).card ≤ L) :
    qv (q9 univ (fun _ :E=> q))
      (fun S => ∀ i ∈ J,¬ R i ⊆ S) ≤ (1-q^L) ^ J.card:=by
  classical
  rw [tH q R J hdisj]
  calc
    ∏ i ∈ J,(1-q^ (R i).card) ≤ ∏ _i ∈ J,(1-q^L) :=by
      apply prod_le_prod
      · intro i _
        exact sub_nonneg.mpr (pow_le_one₀ hq0 hq1)
      · intro i hi
        exact sub_le_sub_left (pow_le_pow_of_le_one hq0 hq1 (hsize i hi)) 1
    _= (1-q^L) ^ J.card:=by simp
omit [DecidableEq E] in
theorem wY {I:Type*} [Fintype I]
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) (L m :ℕ)
    (R:I → Fin m → Finset E)
    (hdisj: ∀ i,(Set.univ:Set (Fin m)).Pairwise
      fun j k=> Disjoint (R i j) (R i k))
    (hsize: ∀ i j,(R i j).card ≤ L)
    (hfail: (Fintype.card I :ℝ) * (1-q^L) ^ m < 1/2)
    (hE:0 < Fintype.card E) :
    ∃ S :Finset E,(S.card:ℝ) ≤ 2*q*Fintype.card E ∧
      ∀ i,∃ j,R i j ⊆ S:=by
  classical
  let mass:Finset E → ℝ :=q9 univ (fun _ => q)
  have hmass (S:Finset E) : 0 ≤ mass S :=
    tO (subset_univ S) (fun _ _=> hq0.le) (fun _ _=> hq1)
  have hsum: ∑ S,mass S =1:=uM _
  have hmean: ∑ S:Finset E,mass S * (S.card:ℝ) =
      q*Fintype.card E :=by
    simpa [mass,mul_comm] using
      yc (univ:Finset E) (fun _ => q)
  let t :ℝ:=2*q*Fintype.card E
  have ht:0 < t:=by
    dsimp [t]
    exact mul_pos (mul_pos (by norm_num) hq0) (by exact_mod_cast hE)
  have hlarge:qv mass (fun S => t < (S.card:ℝ)) ≤ 1/2:=by
    apply (mul_le_mul_iff_right₀ ht).mp
    calc
      t*qv mass (fun S => t < (S.card:ℝ)) ≤
          ∑ S :Finset E,mass S * (S.card:ℝ) :=
        aI mass (fun S => S.card) hmass (fun S => by positivity) t
      _=t* (1/2) :=by rw [hmean];dsimp [t];ring
  let bad:I → Finset E → Prop:=fun i S=> ∀ j,¬ R i j ⊆ S
  have hbad (i:I) : qv mass (bad i) ≤ (1-q^L) ^ m:=by
    simpa only [mass,bad,mem_univ,forall_true_left,card_univ,Fintype.card_fin]
      using yQ q hq0.le hq1 (R i) univ
        (by simpa only [coe_univ] using hdisj i) L (fun j _=> hsize i j)
  have hsome:qv mass (fun S => ∃ i,bad i S) < 1/2:=by
    calc
      qv mass (fun S => ∃ i,bad i S) ≤ ∑ i,qv mass (bad i) :=
        a5 mass hmass bad
      _ ≤ ∑ _i:I,(1-q^L) ^ m:=sum_le_sum (fun i _=> hbad i)
      _= (Fintype.card I :ℝ) * (1-q^L) ^ m:=by simp
      _ < 1/2:=hfail
  have hall:qv mass (fun S => t < (S.card:ℝ) ∨ ∃ i,bad i S) < 1:=by
    have h :=bu mass hmass
      (fun S => t < (S.card:ℝ)) (fun S => ∃ i,bad i S)
    linarith
  obtain ⟨S,hS⟩ :=wl mass hsum _ hall
  refine ⟨S,le_of_not_gt (fun h => hS (Or.inl h)),?_⟩
  intro i
  by_contra hi
  push Not at hi
  exact hS (Or.inr ⟨i,hi⟩)
end
end Erdos556.Bernoulli
end du
section cl
namespace Erdos556
open Finset
theorem tt {E:Type*}
    (P:Finset E → Prop) (L b m:ℕ) (hbound:m*L ≤ b)
    (havoid: ∀ S:Finset E,S.card ≤ b →
      ∃ T :Finset E,P T ∧ T.card ≤ L ∧ Disjoint S T) :
    ∃ R :Fin m → Finset E,(∀ i,P (R i) ∧ (R i).card ≤ L) ∧
      Pairwise (fun i j=> Disjoint (R i) (R j)) :=by
  classical
  induction m with
  | zero=>
      refine ⟨Fin.elim0,?_,?_⟩
      · intro i;exact Fin.elim0 i
      · intro i;exact Fin.elim0 i
  | succ m ih=>
      obtain ⟨R,hR,hD⟩ :=ih (by nlinarith)
      let S := (univ:Finset (Fin m)).biUnion R
      have hS:S.card ≤ b:=by
        calc
          S.card ≤ ∑ i :Fin m,(R i).card:=card_biUnion_le
          _ ≤ ∑ _i:Fin m,L:=sum_le_sum (fun i _=> (hR i).2)
          _=m*L:=by simp
          _ ≤ b:=by nlinarith
      obtain ⟨T,hT,hsize,hST⟩ :=havoid S hS
      have hTR (i:Fin m) : Disjoint T (R i) :=
        hST.symm.mono_right (subset_biUnion_of_mem R (mem_univ i))
      refine ⟨Fin.cons T R,?_,?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ⟨hT,hsize⟩
        · exact hR j
      · intro i j hij
        revert hij
        refine Fin.cases ?_ (fun i => ?_) i <;>
          refine Fin.cases ?_ (fun j => ?_) j
        · intro h;exact (h rfl).elim
        · intro _;exact hTR j
        · intro _;exact (hTR i).symm
        · intro h
          exact hD (fun he=> h (congrArg Fin.succ he))
theorem xq {E I :Type*}
    [Fintype I] (R:I → Finset E) (T:Finset E)
    (hD:Pairwise (fun i j=> Disjoint (R i) (R j)))
    (hmeet: ∀ i,¬ Disjoint T (R i)) : Fintype.card I ≤ T.card:=by
  classical
  have hx: ∀ i,∃ x,x ∈ T ∧ x ∈ R i:=by
    intro i
    simpa only [Finset.disjoint_left,not_forall,not_not,exists_prop] using hmeet i
  choose x hxT hxR using hx
  let f :I → T:=fun i => ⟨x i,hxT i⟩
  have hinj:Function.Injective f :=by
    intro i j hij
    by_contra hne
    have heq:x i=x j:=congrArg Subtype.val hij
    exact Finset.disjoint_left.mp (hD hne) (hxR i) (heq ▸ hxR j)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
theorem y7 {E I :Type*}
    [Fintype I] (R:I → Finset E) (T:Finset E)
    (hD:Pairwise (fun i j=> Disjoint (R i) (R j)))
    (hcard:T.card < Fintype.card I) : ∃ i,Disjoint T (R i) :=by
  classical
  by_contra h
  push Not at h
  exact (Nat.not_le_of_gt hcard) (xq R T hD h)
end Erdos556
end cl
section dn
namespace Erdos556
open Finset
theorem uA {E I :Type*} [Fintype E]
    [Fintype I] (P:I → Finset E → Prop) (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1)
    (L b m a :ℕ) (hbound: ((a+1) * m) * L ≤ b)
    (havoid: ∀ i S,S.card ≤ b →
      ∃ T :Finset E,P i T ∧ T.card ≤ L ∧ Disjoint S T)
    (hfail: (Fintype.card I :ℝ) * (a+1) * (1-q^L) ^ m < 1/2)
    (hE:0 < Fintype.card E) :
    ∃ S :Finset E,(S.card:ℝ) ≤ 2*q*Fintype.card E ∧
      ∀ i T,T.card ≤ a → ∃ U :Finset E,
        U ⊆ S ∧ P i U ∧ U.card ≤ L ∧ Disjoint T U:=by
  classical
  have hpacks (i:I) :=tt (P i) L b ((a+1) * m)
    hbound (havoid i)
  choose R hR hD using hpacks
  let Q (i:I × Fin (a+1)) (j:Fin m) : Finset E :=
    R i.1 (finProdFinEquiv (i.2,j))
  have hQD (i:I × Fin (a+1)) :
      (Set.univ:Set (Fin m)).Pairwise fun j k=> Disjoint (Q i j) (Q i k) :=by
    intro j _ k _ hjk
    apply hD i.1
    intro heq
    exact hjk (congrArg Prod.snd (finProdFinEquiv.injective heq))
  have hQS (i:I × Fin (a+1)) (j:Fin m) : (Q i j).card ≤ L:=
    (hR i.1 (finProdFinEquiv (i.2,j))).2
  have hfailure: (Fintype.card (I × Fin (a+1)) : ℝ) *
      (1-q^L) ^ m < 1/2:=by
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,
      Nat.cast_one] using hfail
  obtain ⟨S,hS,hhit⟩ :=Bernoulli.wY
    q hq0 hq1 L m Q hQD hQS hfailure hE
  refine ⟨S,hS,?_⟩
  intro i T hT
  have hg (g:Fin (a+1)) : ∃ j,Q (i,g) j ⊆ S :=hhit (i,g)
  choose j hj using hg
  let F (g:Fin (a+1)) : Finset E :=Q (i,g) (j g)
  have hFD:Pairwise (fun g h=> Disjoint (F g) (F h)) :=by
    intro g h hgh
    apply hD i
    intro heq
    exact hgh (congrArg Prod.fst (finProdFinEquiv.injective heq))
  obtain ⟨g,hgT⟩ :=y7 F T hFD
    (by simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hT)
  exact ⟨F g,hj g,(hR i (finProdFinEquiv (g,j g))).1,hQS (i,g) (j g),hgT⟩
end Erdos556
end dn
section cr
namespace Erdos556
open SimpleGraph Finset
def qY {V:Type*} (G:SimpleGraph V) (L:ℕ) (u v :V)
    (S:Finset V) : Prop:=
  ∃ p :G.Walk u v,p.IsPath ∧ p.length ≤ L ∧
    ∀ x ∈ p.support,x ≠ u → x ≠ v → x ∈ S
theorem qY.mono {V:Type*} {G:SimpleGraph V} {L:ℕ} {u v :V}
    {S T :Finset V} (h:qY G L u v S) (hST:S ⊆ T) :
    qY G L u v T :=by
  obtain ⟨p,hp,hlen,hs⟩ :=h
  exact ⟨p,hp,hlen,fun x hx hxu hxv=> hST (hs x hx hxu hxv)⟩
theorem x6 {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d L:ℕ)
    (hconn:q8 G b) (hd:0 < d)
    (hdeg: ∀ w,d+b ≤ G.degree w) (hdiam:3*Fintype.card V ≤ d *L)
    (u v :V) (S:Finset V) (hS:S.card ≤ b) :
    ∃ T :Finset V,qY G L u v T ∧ T.card ≤ L ∧ Disjoint S T:=by
  classical
  let S':= (S.erase u).erase v
  have hS':S'.card ≤ b:=
    (Finset.card_le_card ((erase_subset v (S.erase u)).trans (erase_subset u S))).trans hS
  obtain ⟨p,hp,hlen,hav⟩ :=sB G b d hconn hd hdeg S' hS'
    u v (by simp [S']) (by simp [S'])
  have hlen':p.length+1 ≤ L:=by nlinarith
  let T := (p.support.toFinset.erase u).erase v
  refine ⟨T,⟨p,hp,by omega,?_⟩,?_,?_⟩
  · intro x hx hxu hxv
    simp only [T,mem_erase,List.mem_toFinset]
    exact ⟨hxv,hxu,hx⟩
  · calc
      T.card ≤ p.support.toFinset.card:=
        Finset.card_le_card ((erase_subset v _).trans (erase_subset u _))
      _ ≤ p.support.length:=List.toFinset_card_le p.support
      _=p.length+1:=p.length_support
      _ ≤ L:=hlen'
  · rw [Finset.disjoint_left]
    intro x hxS hxT
    simp only [T,mem_erase,List.mem_toFinset] at hxT
    apply hav x hxT.2.2
    simp only [S',mem_erase]
    exact ⟨hxT.1,hxT.2.1,hxS⟩
theorem zM {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d L m a:ℕ)
    (hconn:q8 G b) (hd:0 < d)
    (hdeg: ∀ w,d+b ≤ G.degree w) (hdiam:3*Fintype.card V ≤ d *L)
    (hbound: ((a+1) * m) * L ≤ b)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1)
    (hfail: (Fintype.card V :ℝ) ^ 2* (a+1) * (1-q^L) ^ m < 1/2)
    (hV:0 < Fintype.card V) :
    ∃ R :Finset V,(R.card:ℝ) ≤ 2*q*Fintype.card V ∧
      ∀ u v S,S.card ≤ a → qY G L u v (R \ S) :=by
  classical
  let P : (V × V) → Finset V → Prop:=fun uv=> qY G L uv.1 uv.2
  have hav (uv:V × V) (S:Finset V) (hS:S.card ≤ b) :
      ∃ T :Finset V,P uv T ∧ T.card ≤ L ∧ Disjoint S T:=
    x6 G b d L hconn hd hdeg hdiam uv.1 uv.2 S hS
  have hf: (Fintype.card (V × V) : ℝ) * (a+1) *
      (1-q^L) ^ m < 1/2:=by
    simpa only [Fintype.card_prod,Nat.cast_mul,pow_two] using hfail
  obtain ⟨R,hR,hhit⟩ :=uA P q hq0 hq1 L b m a
    hbound hav hf hV
  refine ⟨R,hR,?_⟩
  intro u v S hS
  obtain ⟨T,hTR,hP,_,hST⟩ :=hhit (u,v) S hS
  apply hP.mono
  intro x hx
  exact mem_sdiff.mpr ⟨hTR hx,fun hxS=> Finset.disjoint_left.mp hST hxS hx⟩
end Erdos556
end cr
section dE
namespace Erdos556
open SimpleGraph
theorem s9 {V:Type*} {G:SimpleGraph V}
    {u v :V} (p:G.Walk u v) (hp:p.IsPath) : u ∉ p.support.tail:=by
  have h :=hp.support_nodup
  rw [← p.cons_tail_support,List.nodup_cons] at h
  exact h.1
theorem qy {V:Type*} {G:SimpleGraph V}
    {u v :V} (p q :G.Walk u v) (hp:p.IsPath) (hq:q.IsPath) (hlen:1 < p.length)
    (hinter: ∀ x ∈ p.support,x ∈ q.support → x=u ∨ x=v) :
    (p.append q.reverse).IsCycle:=by
  apply hp.isCycle_append hq.reverse _ (Or.inl hlen)
  rw [List.disjoint_left]
  intro x hxp hxq
  have hxp':x ∈ p.support:=List.mem_of_mem_tail hxp
  have hxq':x ∈ q.support:=by
    simpa only [Walk.support_reverse,List.mem_reverse] using List.mem_of_mem_tail hxq
  rcases hinter x hxp' hxq' with hxu | hxv
  · exact s9 p hp (hxu ▸ hxp)
  · exact s9 q.reverse hq.reverse (hxv ▸ hxq)
theorem sZ {V:Type*} {G:SimpleGraph V}
    {u v :V} (p:G.Walk u v) (hp:p.IsPath) (hlen:1 < p.length)
    (L:ℕ) (R:Finset V) (hav: ∀ x ∈ p.support,x ∉ R)
    (hconn:qZ G L u v R) :
    ∃ c :G.Walk u u,c.IsCycle ∧ Odd c.length ∧
      p.length ≤ c.length ∧ c.length ≤ p.length+L:=by
  let r :Fin 2 := ⟨(p.length+1) % 2,Nat.mod_lt _ (by decide)⟩
  obtain ⟨q,hq,hqL,hqpar,hqR⟩ :=hconn r
  have hc: (p.append q.reverse).IsCycle:=by
    apply qy p q hp hq hlen
    intro x hxp hxq
    by_cases hxu:x=u
    · exact Or.inl hxu
    by_cases hxv:x=v
    · exact Or.inr hxv
    exact (hav x hxp (hqR x hxq hxu hxv)).elim
  refine ⟨p.append q.reverse,hc,?_,?_,?_⟩
  · apply Nat.odd_iff.mpr
    simp only [Walk.length_append,Walk.length_reverse]
    change q.length%2= (p.length+1) % 2 at hqpar
    omega
  · simp only [Walk.length_append,Walk.length_reverse]
    omega
  · simp only [Walk.length_append,Walk.length_reverse]
    omega
end Erdos556
end dE
section cg
namespace Erdos556
open SimpleGraph Finset
theorem rf {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (L:ℕ) (hL:0 < L) (X Y :Finset V)
    (hXY:Disjoint X Y) (hcomplete: ∀ x ∈ X,∀ y ∈ Y,G.Adj x y)
    (hX:L+1 ≤ X.card) (hY:L ≤ Y.card)
    (u v :V) (hu:u ∈ X) (hv:v ∈ X) (huv:u ≠ v) :
    ∃ p :G.Walk u v,p.IsPath ∧ p.length=2*L ∧
      ∀ z ∈ p.support,z ∈ X ∪ Y:=by
  induction L generalizing X Y u v with
  | zero=> omega
  | succ L ih=>
      classical
      obtain ⟨y,hy⟩ :=card_pos.mp (show 0 < Y.card by omega)
      have huy:u ≠ y:=fun h => Finset.disjoint_left.mp hXY hu (h.symm ▸ hy)
      have hvy:v ≠ y:=fun h => Finset.disjoint_left.mp hXY hv (h.symm ▸ hy)
      by_cases hzero:L=0
      · subst L
        let p :G.Walk u v:=Walk.cons (hcomplete u hu y hy)
          (Walk.cons (hcomplete v hv y hy).symm Walk.nil)
        refine ⟨p,?_,rfl,?_⟩
        · apply (Walk.cons_isPath_iff _ _).mpr
          refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨?_,?_⟩,?_⟩
          · exact Walk.IsPath.nil
          · simpa using hvy.symm
          · simpa only [Walk.support_cons,Walk.support_nil,List.mem_cons,
              List.not_mem_nil,or_false,not_or] using And.intro huy huv
        · intro z hz
          simp only [p,Walk.support_cons,Walk.support_nil,List.mem_cons,
            List.not_mem_nil,or_false] at hz
          rcases hz with rfl | rfl | rfl
          · exact mem_union_left _ hu
          · exact mem_union_right _ hy
          · exact mem_union_left _ hv
      · have hwex: (X \ {u,v}).Nonempty:=by
          apply card_pos.mp
          have hle: ({u,v} : Finset V).card ≤ 2:=by
            exact (card_insert_le _ _).trans (by simp)
          have hc:=card_le_card (show X ∩ {u,v} ⊆ ({u,v} : Finset V) from inter_subset_right)
          rw [card_sdiff,inter_comm]
          omega
        obtain ⟨w,hw⟩ :=hwex
        have hwX:w ∈ X:= (mem_sdiff.mp hw).1
        have hwu:w ≠ u:=fun h => (mem_sdiff.mp hw).2 (by simp [h])
        have hwv:w ≠ v:=by
          have hn:= (mem_sdiff.mp hw).2
          exact fun h => hn (by simp [h])
        have hX':L+1 ≤ (X.erase u).card:=by rw [card_erase_of_mem hu];omega
        have hY':L ≤ (Y.erase y).card:=by rw [card_erase_of_mem hy];omega
        have hXY':Disjoint (X.erase u) (Y.erase y) :=
          hXY.mono (erase_subset _ _) (erase_subset _ _)
        have hcomplete': ∀ x ∈ X.erase u,∀ z ∈ Y.erase y,G.Adj x z:=
          fun x hx z hz=> hcomplete x (mem_of_mem_erase hx) z (mem_of_mem_erase hz)
        obtain ⟨q,hq,hqlen,hqS⟩ :=ih (by omega) (X.erase u) (Y.erase y) hXY'
          hcomplete' hX' hY' w v (mem_erase.mpr ⟨hwu,hwX⟩)
          (mem_erase.mpr ⟨huv.symm,hv⟩) hwv
        have huq:u ∉ q.support:=by
          intro h
          rcases mem_union.mp (hqS u h) with hx | hz
          · exact (mem_erase.mp hx).1 rfl
          · exact Finset.disjoint_left.mp hXY hu (mem_of_mem_erase hz)
        have hyq:y ∉ q.support:=by
          intro h
          rcases mem_union.mp (hqS y h) with hx | hz
          · exact Finset.disjoint_left.mp hXY (mem_of_mem_erase hx) hy
          · exact (mem_erase.mp hz).1 rfl
        let p :G.Walk u v:=Walk.cons (hcomplete u hu y hy)
          (Walk.cons (hcomplete w hwX y hy).symm q)
        refine ⟨p,?_,?_,?_⟩
        · apply (Walk.cons_isPath_iff _ _).mpr
          refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hq,hyq⟩,?_⟩
          simpa only [Walk.support_cons,List.mem_cons,not_or] using And.intro huy huq
        · simp only [p,Walk.length_cons,hqlen]
          omega
        · intro z hz
          simp only [p,Walk.support_cons,List.mem_cons] at hz
          rcases hz with rfl | rfl | hz
          · exact mem_union_left _ hu
          · exact mem_union_right _ hy
          · exact (union_subset_union (erase_subset _ _) (erase_subset _ _)) (hqS z hz)
theorem wq {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (L:ℕ) (hL:0 < L) (X Y :Finset V)
    (hXY:Disjoint X Y) (hcomplete: ∀ x ∈ X,∀ y ∈ Y,G.Adj x y)
    (hX:L+1 ≤ X.card) (hY:L ≤ Y.card)
    (u v :V) (hu:u ∈ X) (hv:v ∈ X) (huv:u ≠ v)
    (p:G.Walk u v) (hp:p.IsPath) (hlen:1 < p.length)
    (hoff: ∀ z ∈ p.support,z ∈ X ∪ Y → z=u ∨ z=v) :
    ∃ c :G.Walk u u,c.IsCycle ∧ c.length=p.length+2*L:=by
  obtain ⟨q,hq,hqL,hqS⟩ :=rf G L hL X Y
    hXY hcomplete hX hY u v hu hv huv
  refine ⟨p.append q.reverse,?_,?_⟩
  · exact qy p q hp hq hlen
      (fun z hzp hzq=> hoff z hzp (hqS z hzq))
  · simp only [Walk.length_append,Walk.length_reverse,hqL]
end Erdos556
end cg
section cj
namespace Erdos556
open SimpleGraph Finset
theorem u9 {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (D d :ℕ) (hD:0 < D)
    (hscale:Fintype.card V ≤ D *d) (hdegree: ∀ v,d ≤ G.degree v)
    (hN:8* (4*D) ^ 2 ≤ Fintype.card V)
    (X Y :Finset V) (hXY:Disjoint X Y)
    (hcomplete: ∀ x ∈ X,∀ y ∈ Y,G.Adj x y)
    (hX:16*D+8* (4*D) ^ 2+1 ≤ X.card)
    (hY:16*D+8* (4*D) ^ 2 ≤ Y.card)
    (hR:2* ((X ∪ Y).card+16*D+1) ≤ d)
    (u v :V) (hu:u ∈ X) (hv:v ∈ X) (huv:u ≠ v)
    (p:G.Walk u v) (hp:p.IsPath)
    (hoff: ∀ z ∈ p.support,z ∈ X ∪ Y → z=u ∨ z=v)
    (n:ℕ) (hn:32*D+8* (4*D) ^ 2+4 ≤ n)
    (hnp:n ≤ p.length+2) (hpar:n%2=p.length%2) :
    ∃ c :G.Walk u u,c.IsCycle ∧ c.length=n:=by
  obtain ⟨q,hq,hqt,hwin,hqpar,hqoff⟩ :=zu G D d hD
    hscale hdegree hN (X ∪ Y) hR (n-2) (by omega) p hp (by omega) hoff
  let L := (n-q.length) / 2
  have hqparn:q.length%2=n%2:=hqpar.trans hpar.symm
  have hqgt:1 < q.length:=by omega
  have hL:0 < L:=by dsimp [L];omega
  have hLe:L ≤ 16*D+8* (4*D) ^ 2:=by dsimp [L];omega
  have hlen:q.length+2*L=n:=by dsimp [L];omega
  obtain ⟨c,hc,hclen⟩ :=wq G L hL X Y hXY hcomplete
    (by omega) (by omega) u v hu hv huv q hq hqgt hqoff
  exact ⟨c,hc,hclen.trans hlen⟩
end Erdos556
end cj
section dy
namespace Erdos556
open SimpleGraph Finset
theorem zG (D:ℕ) (hD:0 < D) :
    ∃ N₀ K :ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (d:ℕ),
      N₀ ≤ Fintype.card V → Fintype.card V ≤ D *d → (∀ v,d ≤ G.degree v) →
      ∀ (z:V) (c:G.Walk z z),c.IsCycle →
      ∀ n :ℕ,K ≤ n → n+K ≤ c.length → n%2=c.length%2 →
      ∃ (w:V) (q:G.Walk w w),q.IsCycle ∧ q.length=n:=by
  let Q :=16*D+8* (4*D) ^ 2
  let M :=rR D Q
  let H :=sd D Q
  let L :=rl D Q
  let C :=2* (2*Q+16*D+3)
  let K :=M+H+ (32*D+8* (4*D) ^ 2+4) + 1
  let N₀:=D*C+8* (4*D) ^ 2+2*L* (Q+M+1) + H
  have hQ:0 < Q:=by dsimp [Q];omega
  refine ⟨N₀,K,?_⟩
  intro V _ _ G _ d hN hscale hdegree z c hc n hn hnc hpar
  have hNshort:8* (4*D) ^ 2 ≤ Fintype.card V :=by dsimp [N₀] at hN;omega
  have hNloss:2*L* (Q+M+1) ≤ Fintype.card V :=by dsimp [N₀] at hN;omega
  have hNblock:H ≤ Fintype.card V :=by dsimp [N₀] at hN;omega
  have hDC:D*C ≤ D*d:=by
    have h :D*C ≤ Fintype.card V :=by dsimp [N₀] at hN;omega
    exact h.trans hscale
  have hC:C ≤ d:= (mul_le_mul_iff_right₀ hD).mp hDC
  have hlen:M < c.length:=by dsimp [K] at hn hnc;omega
  obtain ⟨X,Y,hX,hY,hXY,hcomplete,u,hu,v,hv,huv,p,hp,hpL,hpPar,hpOff⟩ :=
    tl G c hc D d Q hD hQ hscale hdegree hlen hNloss hNblock
  have hR:2* ((X ∪ Y).card+16*D+1) ≤ d:=by
    rw [card_union_of_disjoint hXY,hX,hY]
    dsimp [C] at hC
    omega
  have htarget:32*D+8* (4*D) ^ 2+4 ≤ n:=by dsimp [K] at hn;omega
  have hpath:n ≤ p.length+2:=by
    change c.length ≤ p.length+M+H at hpL
    dsimp [K] at hnc
    omega
  have hX':16*D+8* (4*D) ^ 2+1 ≤ X.card:=by
    change X.card=16*D+8* (4*D) ^ 2+2 at hX
    omega
  have hY':16*D+8* (4*D) ^ 2 ≤ Y.card:=hY.ge
  obtain ⟨q,hq,hqlen⟩ :=u9 G D d hD
    hscale hdegree hNshort X Y hXY hcomplete hX' hY' hR u v hu hv huv p hp hpOff
    n htarget hpath (hpar.trans hpPar.symm)
  exact ⟨u,q,hq,hqlen⟩
theorem uR (D:ℕ) (hD:0 < D) :
    ∃ N₀ K :ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (d n :ℕ),
      N₀ ≤ Fintype.card V → Fintype.card V ≤ D *d → (∀ v,d ≤ G.degree v) →
      3 ≤ n → Odd n → K ≤ n → ¬ cycleGraph n ⊑ G →
      ∀ (z:V) (c:G.Walk z z),c.IsCycle → Odd c.length → c.length < n+K:=by
  obtain ⟨N₀,K,hspec⟩ :=zG D hD
  refine ⟨N₀,K,?_⟩
  intro V _ _ G _ d n hN hscale hdegree hn hodd hnK hno z c hc hcodd
  by_contra hlong
  have hpar:n%2=c.length%2:= (Nat.odd_iff.mp hodd).trans (Nat.odd_iff.mp hcodd).symm
  obtain ⟨w,q,hq,hqlen⟩ :=hspec G d hN hscale hdegree z c hc n hnK (by omega) hpar
  apply hno
  exact (cycleGraph_isContained_iff (by omega)).mpr ⟨w,q,hq,hqlen⟩
end Erdos556
end dy
section cY
namespace Erdos556
open SimpleGraph
def dj {V:Type*} [DecidableEq V] (G:SimpleGraph V)
    (S:Finset V) (v:S) :
    (G.induce (S:Set V)).induce ({v}ᶜ:Set S) ≃g
      G.induce (S.erase v.val:Set V) where
  toEquiv:=
    { toFun:=fun x => ⟨x.val.val,Finset.mem_erase.mpr ⟨by
        intro h
        exact x.property (Subtype.ext h),x.val.property⟩⟩
      invFun:=fun x => ⟨⟨x.val,(Finset.mem_erase.mp x.property).2⟩,by
        intro h
        exact (Finset.mem_erase.mp x.property).1 (congrArg Subtype.val h)⟩
      left_inv:=fun _ => rfl
      right_inv:=fun _ => rfl}
  map_rel_iff':=by intro x y;rfl
theorem rN {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (v:S) :
    (G.induce (S.erase v.val:Set V)).edgeFinset.card+
      (G.induce (S:Set V)).degree v = (G.induce (S:Set V)).edgeFinset.card:=by
  rw [← (dj G S v).card_edgeFinset_eq]
  rw [card_edgeFinset_induce_compl_singleton,card_edgeFinset_deleteIncidenceSet]
  exact Nat.sub_add_cancel ((G.induce (S:Set V)).degree_le_card_edgeFinset v)
theorem a4 {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (d:ℝ) :
    ∃ S :Finset V,
      (G.edgeFinset.card:ℝ) - d*Fintype.card V ≤
        ((G.induce (S:Set V)).edgeFinset.card:ℝ) - d*S.card ∧
      ∀ v :S,d < (G.induce (S:Set V)).degree v :=by
  classical
  let excess (S:Finset V) : ℝ:=
    ((G.induce (S:Set V)).edgeFinset.card:ℝ) - d*S.card
  let baseline:ℝ:= (G.edgeFinset.card:ℝ) - d*Fintype.card V
  let good:Finset (Finset V) :=Finset.univ.filter fun S => baseline ≤ excess S
  have huniv: (Finset.univ:Finset V) ∈ good:=by
    have he: (G.induce ((Finset.univ:Finset V) : Set V)).edgeFinset.card=
        G.edgeFinset.card:=by
      rw [← G.card_filter_edgeFinset_toFinset_subset Finset.univ]
      simp
    simp [good,excess,baseline,he]
  obtain ⟨S,hS,hminimal⟩ :=good.exists_min_image Finset.card ⟨_,huniv⟩
  have hgood:baseline ≤ excess S := (Finset.mem_filter.mp hS).2
  refine ⟨S,hgood,?_⟩
  intro v
  by_contra hdegree
  have hdegree': ((G.induce (S:Set V)).degree v :ℝ) ≤ d:=by
    exact le_of_not_gt hdegree
  let T :=S.erase v.val
  have hcard:T.card+1=S.card:=Finset.card_erase_add_one v.property
  have hedge:=rN G S v
  have hedgeR: ((G.induce (T:Set V)).edgeFinset.card:ℝ) +
      (G.induce (S:Set V)).degree v = (G.induce (S:Set V)).edgeFinset.card:=by
    exact_mod_cast hedge
  have hcardR: (T.card:ℝ) + 1=S.card:=by exact_mod_cast hcard
  have hT:T ∈ good:=by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    dsimp [excess] at hgood ⊢
    nlinarith
  have hle:=hminimal T hT
  omega
end Erdos556
end cY
section dq
namespace Erdos556
open SimpleGraph Finset
noncomputable def sy {V:Type*} [DecidableEq V] (G:SimpleGraph V)
    (S:Finset V) (T:Finset S) :
    (G.induce (S:Set V)).induce (T:Set S) ≃g
      G.induce (T.map (Function.Embedding.subtype (fun v => v ∈ S)) : Set V) :=by
  let f : ↥(T:Set S) → ↥(T.map (Function.Embedding.subtype (fun v => v ∈ S)) : Set V) :=
    fun x => ⟨x.val.val,mem_map.mpr ⟨x.val,x.property,rfl⟩⟩
  have hinj:Function.Injective f :=by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    change (f x).val= (f y).val
    exact congrArg Subtype.val h
  have hsurj:Function.Surjective f :=by
    intro y
    obtain ⟨x,hx,hxy⟩ :=mem_map.mp y.property
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  exact { toEquiv:=Equiv.ofBijective f ⟨hinj,hsurj⟩,map_rel_iff':=Iff.rfl}
theorem u7 {V:Type*} [Finite V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k η :ℝ) (hη:0 ≤ η)
    (A:Finset V)
    (he:k*A.card+η* (A.card:ℝ) ^ 2 < ((G.induce (A:Set V)).edgeFinset.card:ℝ)) :
    ∃ S :Finset V,S.Nonempty ∧
      k*S.card+η* (S.card:ℝ) ^ 2 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
      (∀ v :S,k < (G.induce (S:Set V)).degree v) ∧
      ∀ T :Finset V,T.card < S.card →
        ((G.induce (T:Set V)).edgeFinset.card:ℝ) ≤ k*T.card+η* (T.card:ℝ) ^ 2:=by
  classical
  let:=Fintype.ofFinite V
  let good:Finset (Finset V) :=univ.filter fun S =>
    k*S.card+η* (S.card:ℝ) ^ 2 < ((G.induce (S:Set V)).edgeFinset.card:ℝ)
  have hA:A ∈ good:=mem_filter.mpr ⟨mem_univ _,he⟩
  obtain ⟨S,hS,hminimal⟩ :=good.exists_min_image Finset.card ⟨_,hA⟩
  have hgood:= (mem_filter.mp hS).2
  have hsmall (T:Finset V) (hT:T.card < S.card) :
      ((G.induce (T:Set V)).edgeFinset.card:ℝ) ≤ k*T.card+η* (T.card:ℝ) ^ 2:=by
    by_contra hn
    have hTgood:T ∈ good:=mem_filter.mpr ⟨mem_univ _,lt_of_not_ge hn⟩
    exact (Nat.not_le_of_gt hT) (hminimal T hTgood)
  have hdegree (v:S) : k < (G.induce (S:Set V)).degree v :=by
    by_contra hdeg
    have hdeg':=le_of_not_gt hdeg
    let T :=S.erase v.val
    have hcard:T.card+1=S.card:=card_erase_add_one v.property
    have hcardR: (T.card:ℝ) + 1=S.card:=by exact_mod_cast hcard
    have hedge:=rN G S v
    have hedgeR: ((G.induce (T:Set V)).edgeFinset.card:ℝ) +
        (G.induce (S:Set V)).degree v = (G.induce (S:Set V)).edgeFinset.card:=by
      exact_mod_cast hedge
    have hT:=hsmall T (by omega)
    have hnonneg:=mul_nonneg hη (by positivity: (0:ℝ) ≤ 2* (T.card:ℝ) + 1)
    rw [← hcardR] at hgood
    nlinarith
  have hnonempty:S.Nonempty:=by
    by_contra h
    have hzero:S.card=0:=card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h)
    have hScard:Fintype.card (S:Set V) = S.card:=by
      calc
        Fintype.card (S:Set V) = (S:Set V).ncard:=Nat.card_eq_fintype_card.symm
        _=S.card:=Set.ncard_coe_finset S
    have hb:= (G.induce (S:Set V)).card_edgeFinset_le_card_choose_two
    rw [hScard,hzero] at hb
    norm_num only [Nat.choose_zero_succ] at hb
    have hezero: (G.induce (S:Set V)).edgeFinset.card=0:=Nat.eq_zero_of_le_zero hb
    simp [hzero,hezero] at hgood
  exact ⟨S,hnonempty,hgood,hdegree,hsmall⟩
theorem s5
    {V:Type*} [Finite V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k η :ℝ) (hη:0 ≤ η) (A:Finset V)
    (he:k*A.card+η* (A.card:ℝ) ^ 2 < ((G.induce (A:Set V)).edgeFinset.card:ℝ)) :
    ∃ S :Finset V,S.Nonempty ∧
      k*S.card+η* (S.card:ℝ) ^ 2 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
      (∀ v :S,k < (G.induce (S:Set V)).degree v) ∧
      ∀ T :Finset S,T.card < S.card →
        (((G.induce (S:Set V)).induce (T:Set S)).edgeFinset.card:ℝ) ≤
          k*T.card+η* (T.card:ℝ) ^ 2:=by
  classical
  let:=Fintype.ofFinite V
  obtain ⟨S,hS,hdense,hdeg,hsmall⟩ :=
    u7 G k η hη A he
  refine ⟨S,hS,hdense,hdeg,?_⟩
  intro T hT
  have h :=hsmall (T.map (Function.Embedding.subtype (fun v => v ∈ S)))
    (by simpa only [card_map] using hT)
  rw [← (sy G S T).card_edgeFinset_eq,card_map] at h
  exact h
theorem yr (a b t N k β η e :ℝ)
    (ha0:0 ≤ a) (hb0:0 ≤ b) (ht0:0 ≤ t) (hk0:0 ≤ k) (hη:0 ≤ η)
    (hN:N=a+b+t) (ht:t ≤ β) (hβ:β ≤ k)
    (ha:k-β ≤ a) (hb:k-β ≤ b)
    (hbudget:β*N ≤ 2*η* (k-β) ^ 2)
    (he:e ≤ k* (a+b) + η* (a^2+b^2) + t*N) :
    e ≤ k*N+η*N^2:=by
  have hr0:0 ≤ k-β:=sub_nonneg.mpr hβ
  have hab: (k-β) ^ 2 ≤ a*b:=by
    simpa only [pow_two] using mul_le_mul ha hb hr0 ha0
  have hprod:=mul_le_mul_of_nonneg_left hab (by positivity:0 ≤ 2*η)
  have hN0:0 ≤ N:=by linarith
  have htN:=mul_le_mul_of_nonneg_right ht hN0
  have hkt:=mul_nonneg hk0 ht0
  have hquad:=mul_nonneg hη (mul_nonneg ht0 (by linarith:0 ≤ 2*N-t))
  have hid:k*N+η*N^2-
      (k* (a+b) + η* (a^2+b^2) + t*N) =
      k*t+η*t* (2*N-t) + 2*η* (a*b) - t*N:=by
    rw [hN]
    ring
  nlinarith
end Erdos556
end dq
section cR
namespace Erdos556
open SimpleGraph Finset
theorem rk {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (S:Finset V) (h: ¬ (G.induce (S:Set V)ᶜ).Preconnected) :
    ∃ A B:Finset V,A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      Disjoint A S ∧ Disjoint B S ∧ A ∪ B ∪ S=univ ∧
      ∀ a ∈ A,∀ b ∈ B,¬ G.Adj a b:=by
  classical
  let U := (S:Set V)ᶜ
  let H :=G.induce U
  obtain ⟨u,v,huv⟩ : ∃ u v:U,¬ H.Reachable u v:=by
    simpa only [SimpleGraph.Preconnected,not_forall] using h
  let A := ({x:V | ∃ hx:x ∉ S,H.Reachable u ⟨x,hx⟩} : Set V).toFinset
  let B := (S ∪ A)ᶜ
  have hA (x:V) : x ∈ A ↔ ∃ hx:x ∉ S,H.Reachable u ⟨x,hx⟩ :=by
    simp only [A,Set.mem_toFinset,Set.mem_ofPred_eq]
  have hAS:Disjoint A S:=by
    rw [Finset.disjoint_left]
    intro x hx
    exact ((hA x).mp hx).choose
  have hAB:Disjoint A B:=by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (mem_compl.mp hxB) (mem_union_right S hxA)
  have hBS:Disjoint B S:=by
    rw [Finset.disjoint_left]
    intro x hxB hxS
    exact (mem_compl.mp hxB) (mem_union_left A hxS)
  have hAnon:A.Nonempty:= ⟨u.val,(hA _).mpr ⟨u.property,.rfl⟩⟩
  have hBnon:B.Nonempty:=by
    refine ⟨v.val,?_⟩
    simp only [B,mem_compl,mem_union,not_or]
    refine ⟨v.property,?_⟩
    intro hvA
    obtain ⟨_,hreach⟩ := (hA _).mp hvA
    exact huv hreach
  have hcover:A ∪ B ∪ S=univ:=by
    calc
      A ∪ B ∪ S= (S ∪ A) ∪ (S ∪ A)ᶜ:=by dsimp [B];ac_rfl
      _=univ:=Finset.union_compl (S ∪ A)
  refine ⟨A,B,hAnon,hBnon,hAB,hAS,hBS,hcover,?_⟩
  intro a ha b hb hab
  obtain ⟨haS,hreach⟩ := (hA a).mp ha
  have hbS:b ∉ S:=fun h => (mem_compl.mp hb) (mem_union_left A h)
  have hadj:H.Adj ⟨a,haS⟩ ⟨b,hbS⟩ :=hab
  have hbA:b ∈ A:= (hA b).mpr ⟨hbS,hreach.trans hadj.reachable⟩
  exact (mem_compl.mp hb) (mem_union_right S hbA)
theorem qR {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A B S:Finset V)
    (hcover:A ∪ B ∪ S=univ) (hcross: ∀ a ∈ A,∀ b ∈ B,¬ G.Adj a b)
    (a:V) (ha:a ∈ A) : G.degree a ≤ A.card+S.card:=by
  have hsub:G.neighborFinset a ⊆ A ∪ S :=by
    intro x hx
    have hall:x ∈ A ∪ B ∪ S:=by rw [hcover];exact mem_univ _
    rcases mem_union.mp hall with hAB | hS
    · rcases mem_union.mp hAB with hA | hB
      · exact mem_union_left _ hA
      · exact (hcross a ha x hB ((G.mem_neighborFinset a x).mp hx)).elim
    · exact mem_union_right _ hS
  rw [← G.card_neighborFinset_eq_degree a]
  exact (card_le_card hsub).trans (card_union_le A S)
theorem vp {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A B S:Finset V)
    (hcover:A ∪ B ∪ S=univ) (hcross: ∀ a ∈ A,∀ b ∈ B,¬ G.Adj a b) :
    G.edgeFinset.card ≤ (G.induce (A:Set V)).edgeFinset.card+
      (G.induce (B:Set V)).edgeFinset.card+S.card*Fintype.card V :=by
  classical
  let X :=G.edgeFinset.filter (fun e => e.toFinset ⊆ A)
  let Y :=G.edgeFinset.filter (fun e => e.toFinset ⊆ B)
  let Z :=S.biUnion (fun v => G.incidenceFinset v)
  have hpart (v:V) (hv:v ∉ S) : v ∈ A ∨ v ∈ B:=by
    have hall:v ∈ A ∪ B ∪ S:=by rw [hcover];exact mem_univ v
    exact mem_union.mp ((mem_union.mp hall).resolve_right hv)
  have hZmem (e:Sym2 V) (he:e ∈ G.edgeFinset) (v:V) (hv:v ∈ S) (hve:v ∈ e) :
      e ∈ Z:=by
    apply mem_biUnion.mpr
    refine ⟨v,hv,?_⟩
    rw [G.incidenceFinset_eq_filter]
    exact mem_filter.mpr ⟨he,hve⟩
  have hedgecover:G.edgeFinset ⊆ X ∪ Y ∪ Z:=by
    intro e he
    rcases e with ⟨⟨u,v⟩⟩
    by_cases huS:u ∈ S
    · exact mem_union_right _ (hZmem _ he u huS (by simp))
    by_cases hvS:v ∈ S
    · exact mem_union_right _ (hZmem _ he v hvS (by simp))
    have huv:G.Adj u v:=by simpa using he
    rcases hpart u huS with huA | huB <;> rcases hpart v hvS with hvA | hvB
    · apply mem_union_left
      apply mem_union_left
      exact mem_filter.mpr ⟨he,by simpa only [Sym2.toFinset_mk_eq,
        insert_subset_iff,singleton_subset_iff] using And.intro huA hvA⟩
    · exact (hcross u huA v hvB huv).elim
    · exact (hcross v hvA u huB huv.symm).elim
    · apply mem_union_left
      apply mem_union_right
      exact mem_filter.mpr ⟨he,by simpa only [Sym2.toFinset_mk_eq,
        insert_subset_iff,singleton_subset_iff] using And.intro huB hvB⟩
  have hX:X.card= (G.induce (A:Set V)).edgeFinset.card:=
    G.card_filter_edgeFinset_toFinset_subset A
  have hY:Y.card= (G.induce (B:Set V)).edgeFinset.card:=
    G.card_filter_edgeFinset_toFinset_subset B
  have hZ:Z.card ≤ S.card*Fintype.card V :=by
    calc
      Z.card ≤ ∑ v ∈ S,(G.incidenceFinset v).card:=card_biUnion_le
      _ ≤ ∑ _v ∈ S,Fintype.card V :=by
        apply sum_le_sum
        intro v _
        rw [G.card_incidenceFinset_eq_degree]
        exact (G.degree_lt_card_verts v).le
      _=S.card*Fintype.card V :=by simp
  have h1:=card_le_card hedgecover
  have h2:=card_union_le (X ∪ Y) Z
  have h3:=card_union_le X Y
  omega
end Erdos556
end cR
section cz
namespace Erdos556
open SimpleGraph Finset
theorem sl
    {V:Type*} [Fintype V] (G:SimpleGraph V) [DecidableRel G.Adj]
    (b:ℕ) (k η :ℝ) (hk:0 ≤ k) (hη:0 ≤ η) (hbk: (b:ℝ) ≤ k)
    (hbudget: (b:ℝ) * Fintype.card V ≤ 2 *η* (k-b) ^ 2)
    (he:k*Fintype.card V +η* (Fintype.card V :ℝ) ^ 2 < (G.edgeFinset.card:ℝ))
    (hdeg: ∀ v,k < (G.degree v :ℝ))
    (hsmall: ∀ T:Finset V,T.card < Fintype.card V →
      ((G.induce (T:Set V)).edgeFinset.card:ℝ) ≤ k*T.card+η* (T.card:ℝ) ^ 2) :
    q8 G b:=by
  classical
  intro S hS
  by_contra hconn
  obtain ⟨A,B,hA,hB,hAB,hAS,hBS,hcover,hcross⟩ :=
    rk G S hconn
  have hASBS:Disjoint (A ∪ B) S :=Finset.disjoint_union_left.mpr ⟨hAS,hBS⟩
  have hcards:A.card+B.card+S.card=Fintype.card V :=by
    have h :=congrArg Finset.card hcover
    simpa only [card_union_of_disjoint hASBS,card_union_of_disjoint hAB,card_univ] using h
  have hApos:=hA.card_pos
  have hBpos:=hB.card_pos
  have heA:=hsmall A (by omega)
  have heB:=hsmall B (by omega)
  have hSR: (S.card:ℝ) ≤ b:=by exact_mod_cast hS
  obtain ⟨a,haA⟩ :=hA
  obtain ⟨c,hcB⟩ :=hB
  have hda:=qR G A B S hcover hcross a haA
  have hdc:=qR G B A S
    (by rw [union_comm B A];exact hcover)
    (fun x hx y hy hxy=> hcross y hy x hx hxy.symm) c hcB
  have hdaR: (G.degree a :ℝ) ≤ (A.card:ℝ) + S.card:=by exact_mod_cast hda
  have hdcR: (G.degree c :ℝ) ≤ (B.card:ℝ) + S.card:=by exact_mod_cast hdc
  have ha:k- (b:ℝ) ≤ A.card:=by have:=hdeg a;linarith
  have hb:k- (b:ℝ) ≤ B.card:=by have:=hdeg c;linarith
  have hedge:=vp G A B S hcover hcross
  have hedgeR: (G.edgeFinset.card:ℝ) ≤
      ((G.induce (A:Set V)).edgeFinset.card:ℝ) +
      ((G.induce (B:Set V)).edgeFinset.card:ℝ) + (S.card:ℝ) * Fintype.card V :=by
    exact_mod_cast hedge
  have hbound:=yr (A.card:ℝ) (B.card:ℝ) (S.card:ℝ)
    (Fintype.card V :ℝ) k (b:ℝ) η (G.edgeFinset.card:ℝ)
    (by positivity) (by positivity) (by positivity) hk hη
    (by exact_mod_cast hcards.symm) hSR hbk ha hb hbudget (by linarith)
  exact (not_le_of_gt he) hbound
theorem sR
    {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b:ℕ) (k η :ℝ)
    (hk:0 ≤ k) (hη:0 ≤ η) (hbk: (b:ℝ) ≤ k)
    (hbudget: (b:ℝ) * Fintype.card V ≤ 2 *η* (k-b) ^ 2)
    (A:Finset V)
    (he:k*A.card+η* (A.card:ℝ) ^ 2 < ((G.induce (A:Set V)).edgeFinset.card:ℝ)) :
    ∃ S :Finset V,S.Nonempty ∧
      k*S.card+η* (S.card:ℝ) ^ 2 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
      (∀ v :S,k < (G.induce (S:Set V)).degree v) ∧
      q8 (G.induce (S:Set V)) b :=by
  classical
  obtain ⟨S,hS,hdense,hdeg,hsmall⟩ :=
    s5 G k η hη A he
  have hcard:Fintype.card (S:Set V) = S.card:=by
    calc
      Fintype.card (S:Set V) = (S:Set V).ncard:=Nat.card_eq_fintype_card.symm
      _=S.card:=Set.ncard_coe_finset S
  have hcardle: (Fintype.card (S:Set V) : ℝ) ≤ Fintype.card V :=by
    exact_mod_cast Fintype.card_le_of_injective (fun x : (S:Set V) => x.val) Subtype.val_injective
  have hbudget': (b:ℝ) * Fintype.card (S:Set V) ≤ 2*η* (k-b) ^ 2:=
    (mul_le_mul_of_nonneg_left hcardle (Nat.cast_nonneg b)).trans hbudget
  refine ⟨S,hS,hdense,hdeg,?_⟩
  apply sl (G.induce (S:Set V))
    b k η hk hη hbk hbudget'
  · simpa only [hcard] using hdense
  · exact hdeg
  · intro T hT
    exact hsmall T (by simpa only [hcard] using hT)
end Erdos556
end cz
section dk
namespace Erdos556
open SimpleGraph Finset
theorem rc {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) :
    G.edgeFinset.card ≤ (G.induce (S:Set V)ᶜ).edgeFinset.card+
      S.card*Fintype.card V :=by
  classical
  let A :=G.edgeFinset.filter (fun e => e.toFinset ⊆ Sᶜ)
  let B :=S.biUnion (fun v => G.incidenceFinset v)
  have hcover:G.edgeFinset ⊆ A ∪ B:=by
    intro e he
    by_cases h :e.toFinset ⊆ Sᶜ
    · exact mem_union_left _ (mem_filter.mpr ⟨he,h⟩)
    · obtain ⟨x,hxe,hx⟩ :=not_subset.mp h
      have hxS:x ∈ S:=by simpa only [mem_compl,not_not] using hx
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨x,hxS,?_⟩
      rw [G.incidenceFinset_eq_filter]
      exact mem_filter.mpr ⟨he,by simpa using hxe⟩
  have hA:A.card= (G.induce (S:Set V)ᶜ).edgeFinset.card:=by
    have h :=congrArg Finset.card (G.map_edgeFinset_induce (s:= (S:Set V)ᶜ))
    simp only [card_map] at h
    have heq:G.edgeFinset ∩ ((S:Set V)ᶜ).toFinset.sym2=A:=by
      simp [A,G.filter_edgeFinset_toFinset_subset]
    rw [heq] at h
    exact h.symm
  have hB:B.card ≤ S.card*Fintype.card V :=by
    calc
      B.card ≤ ∑ v ∈ S,(G.incidenceFinset v).card:=card_biUnion_le
      _ ≤ ∑ _v ∈ S,Fintype.card V :=by
        apply sum_le_sum
        intro v _
        rw [G.card_incidenceFinset_eq_degree]
        exact (G.degree_lt_card_verts v).le
      _=S.card*Fintype.card V :=by simp
  exact (card_le_card hcover).trans ((card_union_le A B).trans (by omega))
end Erdos556
end dk
section dK
/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song, Yury Kudryashov
-/
namespace Erdos556.Function
open Filter _root_.Function
variable {α:Type*} [PartialOrder α] [hα:WellFoundedGT α] {f:α → α}
lemma Monotone.eventuallyConst_atTop {ι:Type*}
    [SemilatticeSup ι] [Nonempty ι] {g:ι → α} (hg:Monotone g) :
    EventuallyConst g atTop:=by
  rw [Filter.eventuallyConst_atTop]
  obtain ⟨x,hx⟩ : ∃ x,g x=_:=hα.wf.min_mem _ (Set.range_nonempty _)
  refine ⟨x,fun z hz ↦ ?_⟩
  have hxz:g x ≤ g z:=hg hz
  have hnlt: ¬g x < g z:=by
    simpa [hx] using hα.wf.not_lt_min (Set.range g) (Set.mem_range_self z)
  exact (eq_of_le_of_not_lt hxz hnlt).symm
lemma rH (hf:id ≤ f) (x:α) :
    EventuallyConst (fun n ↦ f^[n] x) atTop:=
  Monotone.eventuallyConst_atTop (fun _ _ h ↦ monotone_iterate_of_id_le hf h x)
noncomputable def ai {f:ℕ → α} (hf:EventuallyConst f atTop) :=
  (eventuallyConst_atTop.mp hf).choose
noncomputable def rT (hf:id ≤ f) (x:α) : ℕ:=
  ai (rH hf x)
lemma wK (hf:id ≤ f) (x:α) :
    ∀ m ≥ rT hf x,
      f^[m] x =f^[rT hf x] x :=
  (eventuallyConst_atTop.mp (rH hf x)).choose_spec
noncomputable def v3 (hf:id ≤ f) (x:α) :=
  f^[rT hf x] x
lemma t0 (hf:id ≤ f) (x:α) :
    IsFixedPt f (v3 hf x) :=by
  unfold IsFixedPt
  simp only [v3,← iterate_succ_apply']
  apply wK
  simp
lemma tJ (hf:id ≤ f) (x:α) : x ≤ v3 hf x :=by
  simp only [v3]
  conv_lhs=> rw [← iterate_zero_apply f x]
  apply f.monotone_iterate_of_id_le hf
  simp
end Erdos556.Function
end dK
section d0
/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
/-
# Bondy--Chvátal theorem
This is the proved Mathlib development by Shuhao Song from commit
`c83689ab8f` of the `meow-sister/BondyChvatal_PR` branch, vendored here
because the theorem is not part of the Mathlib v4.33.0 module set.
-/
namespace SimpleGraph
open Walk Function Erdos556.Function
open scoped List
variable {V:Type*} [Fintype V] [DecidableEq V] (G:SimpleGraph V)
def rO:=by
  classical
  exact { (u,v) : V × V | G.degree u +G.degree v ≥ (Fintype.card V) ∧ u ≠ v ∧ ¬G.Adj u v}
noncomputable def qg:SimpleGraph V :=by
  classical
  exact if h : (rO G).Nonempty then
    G ⊔ edge h.some.1 h.some.2
  else
    G
omit [DecidableEq V] in
lemma s6:G ≤ qg G :=by
  classical
  unfold qg
  split_ifs with h
  repeat simp
noncomputable def qE:=Erdos556.Function.v3 s6 G
omit [DecidableEq V] in
lemma sa: (qg G \ G).edgeSet.Subsingleton:=by
  classical
  unfold qg
  split_ifs with h
  · simp only [sup_sdiff_left_self,edgeSet_sdiff]
    apply Set.Subsingleton.anti (t:= (edge h.some.1 h.some.2).edgeSet)
    · have:h.some.1 ≠ h.some.2:=h.some_mem.2.1
      simp [edgeSet_edge_of_ne this]
    · apply Set.sdiff_subset
  · simp
omit [DecidableEq V] in
lemma xx {u v :V} (huv: ¬G.Adj u v)
    (huv':G.qg.Adj u v) :
    G.qg.deleteEdges {s(u,v)} = G:=by
  classical
  rw [← edgeSet_inj]
  ext e
  simp only [edgeSet_deleteEdges,Set.mem_sdiff,Set.mem_singleton_iff]
  apply Iff.intro
  · rintro ⟨he₁,he₂⟩
    by_contra he₃
    have mem₁:e ∈ (qg G \ G).edgeSet:=by simpa using ⟨he₁,he₃⟩
    have mem₂:s(u,v) ∈ (qg G \ G).edgeSet:=by simpa using ⟨huv',huv⟩
    exact he₂ <| (sa G) mem₁ mem₂
  · intro he
    apply And.intro (edgeSet_mono (s6 G) he)
    intro he'
    simp only [he',mem_edgeSet] at he
    exact huv he
omit [DecidableEq V] in
lemma uY:
    qg G =G ↔ rO G = ∅ :=by
  classical
  unfold qg
  split_ifs with h
  · have: (G ⊔ edge h.some.1 h.some.2=G) ↔ False:=by
      rw [sup_eq_left,iff_false]
      intro hle
      have hedge: (edge h.some.1 h.some.2).Adj h.some.1 h.some.2:=
        (edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,h.some_mem.2.1⟩
      exact h.some_mem.2.2 (hle hedge)
    simp only [this,false_iff]
    simpa [← Set.not_nonempty_iff_eq_empty] using h
  · simpa [← Set.not_nonempty_iff_eq_empty] using h
omit [DecidableEq V] in
open Classical in
lemma zF:qg G =G ↔
    ∀ {u} {v},u ≠ v → G.degree u +G.degree v ≥ (Fintype.card V) → G.Adj u v:=by
  classical
  rw [uY]
  constructor
  · intro hempty u v huv hdeg
    by_contra hadj
    have hmem: (u,v) ∈ rO G := ⟨hdeg,huv,hadj⟩
    rw [hempty] at hmem
    exact hmem
  · intro h
    ext ⟨u,v⟩
    constructor
    · intro huv
      exact (huv.2.2 (h huv.2.1 huv.1)).elim
    · intro hfalse
      exact hfalse.elim
omit [DecidableEq V] in
open Classical in
lemma zr {u v :V} (huv: ¬G.Adj u v)
    (huv':G.qg.Adj u v) :
    G.degree u +G.degree v ≥ (Fintype.card V) :=by
  classical
  have ne: (rO G).Nonempty:=by
    by_contra h
    simp only [Set.nonempty_iff_ne_empty,← uY,Decidable.not_not] at h
    rw [h] at huv'
    exact huv huv'
  let w :=ne.some
  have prop₁:G.degree w.1+G.degree w.2 ≥ (Fintype.card V) :=ne.some_mem.1
  have mem₁:s(u,v) ∈ (qg G \ G).edgeSet:=by simpa using ⟨huv',huv⟩
  have mem₂:s(w.1,w.2) ∈ (qg G \ G).edgeSet:=by
    have prop₂:w.1 ≠ w.2:=ne.some_mem.2.1
    have prop₃: ¬G.Adj w.1 w.2:=ne.some_mem.2.2
    have G_eq:G.qg=G ⊔ edge w.1 w.2:=by simp [qg,ne,w]
    simpa [-Prod.mk.eta,G_eq,edge_adj] using And.intro prop₂ prop₃
  have edge_eq:= (sa G mem₁ mem₂).symm
  simp only [Prod.mk.eta,Sym2.eq,Sym2.rel_iff'] at edge_eq
  rcases edge_eq with h | h
  · rw [h] at prop₁
    simpa using prop₁
  · rw [h] at prop₁
    rw [add_comm]
    simpa using prop₁
omit [DecidableEq V] in
lemma rs:G ≤ qE G :=by
  classical
  rw [qE]
  apply Erdos556.Function.tJ
omit [DecidableEq V] in
open Classical in
lemma rK: ∀ {u} {v},u ≠ v →
    G.qE.degree u +G.qE.degree v ≥ (Fintype.card V) →
      G.qE.Adj u v:=by
  classical
  have:qg (qE G) = qE G :=
    t0 s6 G
  rwa [zF] at this
variable {G}
namespace Walk
variable {a:V} {p:G.Walk a a}
omit [Fintype V] in
protected theorem IsHamiltonianCycle.aC [Finite V] (hp:p.IsHamiltonianCycle)
    {H:SimpleGraph V} (h: ∀ e ∈ p.edges,e ∈ H.edgeSet) :
    (p.transfer H h).IsHamiltonianCycle:=by
  classical
  let:=Fintype.ofFinite V
  rw [isHamiltonianCycle_iff_isCycle_and_length_eq]
  exact ⟨hp.isCycle.transfer h,by simpa using hp.length_eq⟩
omit [DecidableEq V] [Fintype V] in
private lemma IsCycle.rB (hp:p.IsCycle)
    {d e :G.Dart} (hd:d ∈ p.darts) (he:e ∈ p.darts)
    (hfst:d.fst=e.fst) : d=e:=by
  classical
  obtain ⟨i,hi,rfl⟩ :=List.getElem_of_mem hd
  obtain ⟨j,hj,rfl⟩ :=List.getElem_of_mem he
  have hget:p.getVert i =p.getVert j :=by
    simpa [p.darts_getElem_eq_getVert i hi,p.darts_getElem_eq_getVert j hj] using hfst
  have hi':i ≤ p.length-1:=by
    have hi_len:i < p.length:=by simpa using hi
    omega
  have hj':j ≤ p.length-1:=by
    have hj_len:j < p.length:=by simpa using hj
    omega
  have hij:=hp.getVert_injOn' hi' hj' hget
  subst j
  rfl
omit [DecidableEq V] [Fintype V] in
private lemma IsCycle.zU (hp:p.IsCycle)
    {d e :G.Dart} (hd:d ∈ p.darts) (he:e ∈ p.darts)
    (hsnd:d.snd=e.snd) : d=e:=by
  classical
  obtain ⟨i,hi,rfl⟩ :=List.getElem_of_mem hd
  obtain ⟨j,hj,rfl⟩ :=List.getElem_of_mem he
  have hget:p.getVert (i+1) = p.getVert (j+1) :=by
    simpa [p.darts_getElem_eq_getVert i hi,p.darts_getElem_eq_getVert j hj] using hsnd
  have hi':i < p.length:=by simpa using hi
  have hj':j < p.length:=by simpa using hj
  have hij:=hp.getVert_injOn
    (show 1 ≤ i +1 ∧ i+1 ≤ p.length by omega)
    (show 1 ≤ j +1 ∧ j+1 ≤ p.length by omega) hget
  have:i=j:=Nat.add_right_cancel hij
  subst j
  rfl
omit [DecidableEq V] [Fintype V] in
private lemma uj {u v :V}
    {r:G.Walk u v} (hnodup:r.support.dropLast.Nodup)
    {d e :G.Dart} (hd:d ∈ r.darts) (he:e ∈ r.darts)
    (hfst:d.fst=e.fst) : d=e:=by
  classical
  obtain ⟨i,hi,rfl⟩ :=List.getElem_of_mem hd
  obtain ⟨j,hj,rfl⟩ :=List.getElem_of_mem he
  have hi':i < r.support.dropLast.length:=by simpa using hi
  have hj':j < r.support.dropLast.length:=by simpa using hj
  have hget:r.support.dropLast[i]'hi'=r.support.dropLast[j]'hj':=by
    simpa [r.fst_darts_getElem hi,r.fst_darts_getElem hj] using hfst
  have hij:= (List.Nodup.getElem_inj_iff hnodup).mp hget
  subst j
  rfl
private theorem rV
    (hp:p.length=Fintype.card V) (hV:3 ≤ Fintype.card V)
    (hsupport:p.support.tail.toFinset=Finset.univ) :
    p.IsHamiltonianCycle:=by
  classical
  rw [isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_,hp⟩
  rw [isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_,by omega⟩
  apply IsPath.mk'
  rw [support_tail_of_not_nil p (by rw [not_nil_iff_lt_length,hp];omega)]
  have hcard:p.support.tail.toFinset.card=p.support.tail.length:=by
    rw [hsupport]
    simp [hp]
  have hmulti: ((p.support.tail:Multiset V).toFinset.card=
      (p.support.tail:Multiset V).card) :=by simpa using hcard
  simpa using Multiset.toFinset_card_eq_card_iff_nodup.mp hmulti
namespace IsHamiltonianCycle
omit [Fintype V]
variable (b:V)
private lemma yk (hp:p.IsHamiltonianCycle) : b ∈ p.support.tail:=by
  classical
  rw [← support_tail_of_not_nil p hp.not_nil]
  exact hp.isHamiltonian_tail.mem_support b
private lemma zj (hp:p.IsHamiltonianCycle) :
    b ∈ p.support.dropLast:=by
  classical
  have hb:b ∈ p.tail.support:=by
    simpa [support_tail_of_not_nil p hp.not_nil] using hp.yk b
  have hb':b ∈ p.dropLast.support:=
    (List.Perm.mem_iff (support_tail_perm_support_dropLast p)).mp hb
  simpa [support_dropLast hp.not_nil] using hb'
noncomputable def zf (hp:p.IsHamiltonianCycle) : G.Dart:=
  Exists.choose <| show ∃ d ∈ p.darts,d.fst=b by
    simpa [← Walk.map_fst_darts] using hp.zj b
noncomputable def qk (hp:p.IsHamiltonianCycle) : V:=
  (hp.zf b).snd
lemma qH (hp:p.IsHamiltonianCycle) :
    ∃ d ∈ p.darts,d.fst=b ∧ d.snd=hp.qk b :=by
  classical
  unfold qk zf
  generalize_proofs hd
  have hspec:=hd.choose_spec
  set d :=hd.choose
  exact ⟨d,hspec.1,hspec.2,rfl⟩
lemma xe (hp:p.IsHamiltonianCycle) : Function.Injective hp.qk:=by
  classical
  intro v₁ v₂ hnext
  obtain ⟨d₁,hd₁,hd₁fst,hd₁snd⟩ :=hp.qH v₁
  obtain ⟨d₂,hd₂,hd₂fst,hd₂snd⟩ :=hp.qH v₂
  have heq:d₁=d₂:=hp.isCycle.zU hd₁ hd₂ <| by
    rw [hd₁snd,hd₂snd]
    exact hnext
  rw [← hd₁fst,← hd₂fst,heq]
lemma uE (hp:p.IsHamiltonianCycle)
    {i:ℕ} (hi:i < p.length) (hi':p.getVert i =b) :
    p.getVert (i+1) = hp.qk b :=by
  classical
  have hiD:i < p.darts.length:=by simpa using hi
  have hdi:p.darts[i] ∈ p.darts:=List.getElem_mem hiD
  obtain ⟨d,hd,hdfst,hdsnd⟩ :=hp.qH b
  have hfst:p.darts[i].fst=d.fst:=by
    rw [p.darts_getElem_eq_getVert i hiD,hdfst]
    exact hi'
  have heq:=hp.isCycle.rB hdi hd hfst
  have hsnd:=congrArg (fun z :G.Dart ↦ z.snd) heq
  rw [p.darts_getElem_eq_getVert i hiD,hdsnd] at hsnd
  exact hsnd
lemma tX (hp:p.IsHamiltonianCycle) (hb:b ∈ p.support) (c:V) :
    ((hp.rotate hb).qk c) = hp.qk c :=by
  classical
  obtain ⟨d₁,hd₁,hd₁fst,hd₁snd⟩ := (hp.rotate hb).qH c
  obtain ⟨d₂,hd₂,hd₂fst,hd₂snd⟩ :=hp.qH c
  have hd₁':d₁ ∈ p.darts:=by
    simpa using (List.IsRotated.mem_iff (rotate_darts p b hb)).mp hd₁
  have heq:d₁=d₂:=hp.isCycle.rB hd₁' hd₂ <| by
    rw [hd₁fst,hd₂fst]
  rw [← hd₁snd,← hd₂snd,heq]
variable {b}
theorem t7 (hp:p.IsHamiltonianCycle) : hp.qk b ≠ b :=by
  classical
  obtain ⟨d,-,hdfst,hdsnd⟩ :=hp.qH b
  intro h
  exact d.adj.ne (hdfst.trans (hdsnd.trans h).symm)
theorem tL (hp:p.IsHamiltonianCycle) :
    hp.qk (hp.qk b) ≠ b:=by
  classical
  have hb:b ∈ p.support:=hp.mem_support b
  let q :=p.rotate b hb
  have hq:q.IsHamiltonianCycle:=hp.rotate hb
  have hlen:3 ≤ q.length:=hq.isCycle.three_le_length
  have hq0:q.getVert 0 =b:=by simp [q]
  have hq1:q.getVert 1 =hq.qk b :=
    hq.uE b (i:=0) (by omega) hq0
  have hq2:q.getVert 2 =hq.qk (hq.qk b) :=
    hq.uE (hq.qk b) (i:=1) (by omega) hq1
  have hrot: ∀ c,hq.qk c =hp.qk c :=by
    intro c
    change (hp.rotate hb).qk c =hp.qk c
    exact IsHamiltonianCycle.tX b hp hb c
  simp only [hrot] at hq1 hq2
  intro h
  have h02:q.getVert 0 =q.getVert 2 :=by rw [hq0,hq2,h]
  have:=hq.isCycle.getVert_injOn'
    (show 0 ≤ q.length-1 by omega)
    (show 2 ≤ q.length-1 by omega) h02
  omega
end IsHamiltonianCycle
end Walk
private theorem zi
    {u u' v v':V} {p:G.Walk u u'}
    (hV: (Fintype.card V) ≥ 3) (hp:p.support ~ Finset.univ.toList)
    (ne:v ≠ u') (vu':G.Adj v u') (v'u:G.Adj v' u)
    (d:G.Dart) (hd:d ∈ p.darts) (hd₁:d.fst=v) (hd₂:d.snd=v') :
    IsHamiltonian G :=by
  classical
  have hv:v ∈ p.support:=by simp [List.Perm.mem_iff hp]
  have not_nil: ¬(p.dropUntil v hv).Nil:=not_nil_of_ne ne
  have snd_eq_v': (p.dropUntil v hv).getVert 1 =v':=by
    have hsupport:p.support.Nodup:=by
      rw [List.Perm.nodup_iff hp]
      apply Finset.nodup_toList
    have hdrop:p.support.dropLast.Nodup:=p.support.dropLast_prefix.nodup hsupport
    have hfirst: (p.dropUntil v hv).firstDart not_nil ∈ p.darts:=
      p.darts_dropUntil_subset_darts hv
        ((p.dropUntil v hv).firstDart_mem_darts not_nil)
    have heq: (p.dropUntil v hv).firstDart not_nil=d:=
      uj hdrop hfirst hd (by simp [hd₁])
    have hsnd:=congrArg (fun z :G.Dart ↦ z.snd) heq
    simpa [hd₂] using hsnd
  let q := (p.takeUntil _ hv)
    |>.append vu'.toWalk
    |>.append (p.dropUntil v hv |>.tail |>.reverse.copy rfl snd_eq_v')
    |>.append v'u.toWalk
  suffices q.IsHamiltonianCycle from fun _ ↦ ⟨u,q,this⟩
  apply rV
  · have hsum: (p.takeUntil v hv).length+ (p.dropUntil v hv).length=p.length:=by
      have hwalk:=congrArg Walk.length (p.take_spec hv)
      simpa only [Walk.length_append] using hwalk
    have:=calc
      p.length+1=p.support.length:=by simp
      _=Finset.univ.toList.length:=by apply List.Perm.length_eq hp
      _= (Fintype.card V) :=by simp
    have:=Walk.length_tail_add_one not_nil
    simp [q,add_assoc]
    omega
  · assumption
  · simp only [tail_support_append,support_cons,support_nil,List.tail_cons,support_copy,
      support_reverse,List.append_assoc,
      List.cons_append,List.toFinset_append,List.toFinset_cons,
      List.toFinset_nil,insert_empty_eq,Finset.union_insert,Finset.eq_univ_iff_forall,
      Finset.mem_insert,Finset.mem_union,List.mem_toFinset,Finset.mem_singleton,
      Finset.notMem_empty,false_or,q]
    intro w
    by_contra hw
    simp only [not_or] at hw
    rcases hw with ⟨hw₁,hw₂,hw₃,hw₄⟩
    have mem_tail:w ∈ p.support.tail:=by
      have mem:w ∈ p.support:=by simp [List.Perm.mem_iff hp]
      rw [← Walk.cons_tail_support] at mem
      simp only [List.mem_cons] at mem
      exact mem.resolve_left hw₄
    have not_mem_drop:w ∉ (p.dropUntil v hv).support.tail:=by
      have tail_not_nil: (p.dropUntil v hv).support.tail ≠ [] :=by
        have hpos:0 < (p.dropUntil v hv).length:=
          not_nil_iff_lt_length.mp not_nil
        apply List.ne_nil_of_length_pos
        rw [List.length_tail,length_support]
        omega
      have: (p.dropUntil v hv).support.tail.getLast tail_not_nil=u':=by
        rw [List.getLast_tail,getLast_support]
      have hw_dropLast:
          w ∉ (p.dropUntil v hv).support.tail.dropLast:=by
        simpa only [List.tail_reverse,List.mem_reverse,
          support_tail_of_not_nil _ not_nil] using hw₃
      intro hwmem
      rw [← List.dropLast_append_getLast tail_not_nil,this,
        List.mem_append,List.mem_singleton] at hwmem
      exact hwmem.elim hw_dropLast hw₁
    have append:p.support.tail=
        (p.takeUntil v hv).support.tail++ (p.dropUntil v hv).support.tail:=by
      rw [← tail_support_append,take_spec]
    simp only [append,List.mem_append] at mem_tail
    rcases mem_tail with h | h
    · exact hw₂ h
    · exact not_mem_drop h
open Classical in
private theorem xN
    {u v :V} {q:G.qg.Walk u u} (hq:q.IsHamiltonianCycle)
    (hV: (Fintype.card V) ≥ 3) (huv:G.degree u +G.degree v ≥ (Fintype.card V))
    (hv:v=hq.qk u) (not_adj: ¬G.Adj u v) :
    ∃ w w' d,G.Adj w v ∧ G.Adj w' u ∧ d ∈ q.darts ∧ d.fst=w' ∧ d.snd=w:=by
  classical
  let X := (hq.qk ·) '' {w | G.Adj u w} \ {u}
  let Y := {w | G.Adj v w} \ {hq.qk v}
  have cardX:G.degree u -1 ≤ X.toFinset.card:=calc
    _= (G.neighborFinset u).card-1:=by simp
    _= (Finset.univ.filter (G.Adj u)).card-1:=by rw [neighborFinset_eq_filter]
    _ ≤ ((Finset.univ.filter (G.Adj u)).image (hq.qk ·)).card-
        ({u} : Finset _).card:=by
      simp [Finset.card_image_of_injective _ hq.xe]
    _ ≤ (((Finset.univ.filter (G.Adj u)).image (hq.qk ·)) \ {u}).card:=by
      apply Finset.le_card_sdiff
    _=_:=by simp [X]
  have cardY:G.degree v -1 ≤ Y.toFinset.card:=calc
    _= (G.neighborFinset v).card-1:=by simp
    _ ≤ (Finset.univ.filter (G.Adj v)).card- ({hq.qk v} : Finset _).card:=by
      simp [neighborFinset_eq_filter]
    _ ≤ (Finset.univ.filter (G.Adj v) \ {hq.qk v}).card:=by
      apply Finset.le_card_sdiff
    _=_:=by simp [Y]
  have card_union: (X ∪ Y).toFinset.card ≤ (Fintype.card V) - 3:=calc
    _ ≤ ({v,hq.qk v,u}ᶜ:Finset _).card:=by
      apply Finset.card_le_card
      rw [Finset.subset_compl_comm]
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_singleton,Set.toFinset_union,
        Set.toFinset_sdiff,Set.toFinset_image,Set.toFinset_ofPred,Set.toFinset_singleton,
        Finset.compl_union,Finset.mem_inter,Finset.mem_compl,Finset.mem_sdiff,
        Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,not_and,
        Decidable.not_not,forall_exists_index,and_imp,X,Y] at hw ⊢
      apply And.intro
      · intro w' adj qk
        rcases hw with hw | hw | hw
        · rw [hw,hv] at qk
          rw [hq.xe qk] at adj
          simp at adj
        · rw [hw] at qk
          rw [hq.xe qk] at adj
          exact False.elim (not_adj adj)
        · exact hw
      · intro adj
        rcases hw with hw | hw | hw
        · rw [hw] at adj
          simp at adj
        · exact hw
        · rw [hw] at adj
          exact False.elim (not_adj adj.symm)
    _=_:=by
      suffices ({v,hq.qk v,u} : Finset _).card=3 by rw [Finset.card_compl,this]
      rw [Finset.card_insert_of_notMem,Finset.card_insert_of_notMem]
      · simp
      · simpa [hv] using hq.tL
      · simpa [hv] using And.intro hq.t7.symm hq.t7
  have non_empty: (X ∩ Y).toFinset.card ≠ 0:=fun h ↦ by
    suffices (Fintype.card V) - 2 ≤ (Fintype.card V) - 3 by omega
    calc
      _ ≤ (G.degree u +G.degree v) - 2:=Nat.sub_le_sub_right huv _
      _ ≤ (G.degree u -1) + (G.degree v -1) :=by omega
      _ ≤ X.toFinset.card+Y.toFinset.card:=add_le_add cardX cardY
      _= (X ∪ Y).toFinset.card+ (X ∩ Y).toFinset.card:=by
        simpa [-Set.toFinset_card] using (Finset.card_union_add_card_inter _ _).symm
      _ ≤ (Fintype.card V) - 3+0:=add_le_add card_union (le_of_eq h)
      _= (Fintype.card V) - 3:=by simp
  obtain ⟨w,hw⟩ :=Finset.card_ne_zero.mp non_empty
  simp only [Set.toFinset_inter,Set.toFinset_sdiff,Set.toFinset_image,
    Set.toFinset_ofPred,Set.toFinset_singleton,Finset.mem_inter,Finset.mem_sdiff,
    Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,
    X,Y] at hw
  rcases hw with ⟨⟨⟨w',hw'₁,hw'₂⟩,-⟩,hw₂,-⟩
  obtain ⟨d,hd₁,hd₂⟩ :=hq.qH w'
  rw [hw'₂] at hd₂
  exact ⟨w,w',d,hw₂.symm,hw'₁.symm,hd₁,hd₂⟩
theorem yp (hG:IsHamiltonian (qg G)) :
    IsHamiltonian G :=by
  classical
  by_cases trivial:Fintype.card V =1
  · exact absurd trivial
  · by_contra nonHamiltonian
    obtain ⟨a,p,hp⟩ :=hG trivial
    obtain ⟨d,hd,hd'⟩ : ∃ d ∈ p.darts,¬G.Adj d.fst d.snd:=by
      by_contra h
      simp only [not_exists,not_and,Decidable.not_not] at h
      have edgeSubset (e) (he:e ∈ p.edges) : e ∈ G.edgeSet:=by
        simp only [edges,List.mem_map] at he
        obtain ⟨d,hd,hd'⟩ :=he
        rw [← hd']
        exact h _ hd
      let q :=p.transfer G edgeSubset
      suffices q.IsHamiltonianCycle from nonHamiltonian (fun _ ↦ ⟨a,q,this⟩)
      exact hp.aC edgeSubset
    set u :=d.fst
    set v :=d.snd
    have hu:u ∈ p.support:=Walk.dart_fst_mem_support_of_mem_darts _ hd
    let q :=p.rotate u hu
    have hq:q.IsHamiltonianCycle:=hp.rotate hu
    have hd_q:d ∈ q.darts:=by
      simpa [q] using List.IsRotated.mem_iff (rotate_darts p u hu) |>.mpr hd
    have q_not_nil: ¬q.Nil:=by
      erw [nil_rotate]
      exact hp.1.not_nil
    have next_u_eq_v:q.getVert 1 =v:=by
      have heq:q.firstDart q_not_nil=d:=
        hq.isCycle.rB (q.firstDart_mem_darts q_not_nil) hd_q (by simp [u])
      have hsnd:=congrArg (fun z :G.qg.Dart ↦ z.snd) heq
      simpa [v] using hsnd
    have uv_not_edge:s(u,v) ∉ q.tail.edges:=by
      have:q=cons (q.adj_snd q_not_nil) q.tail:=by
        exact (q.cons_tail_eq q_not_nil).symm
      have:q.edges=s(u,v) ::q.tail.edges:=by
        simp only [this,edges_cons]
        simp [next_u_eq_v]
      intro h
      have nodup:=hq.1.edges_nodup
      rw [this] at nodup
      exact List.not_nodup_cons_of_mem h nodup
    have G_closure_del:G.qg.deleteEdges {s(u,v)} = G:=by
      exact xx _ hd' d.adj
    let q':=q.tail
      |>.toDeleteEdge s(u,v) uv_not_edge
      |>.transfer G (by
        simp (config:= {singlePass:=true}) only [← G_closure_del]
        exact edges_subset_edgeSet _)
      |>.copy next_u_eq_v rfl
    have perm_q':q'.support ~ Finset.univ.toList:=by
      rw [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at hq
      simp only [transfer_transfer,support_copy,support_transfer,
        List.perm_iff_count,q']
      intro a
      rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)]
      simpa [support_tail_of_not_nil _ q_not_nil] using hq.2 _
    have hV: (Fintype.card V) ≥ 3:=hq.length_eq ▸ hq.isCycle.three_le_length
    have deg_sum:=zr G hd' d.adj
    have next_u:v=hq.qk u :=by
      obtain ⟨d',hd'₁,hd'₂,hd'₃⟩ :=hq.qH u
      have heq:d=d':=
        hq.isCycle.rB hd_q hd'₁ (by simpa [u] using hd'₂.symm)
      change d.snd=hq.qk u
      rw [← hd'₃]
      exact congrArg (fun z :G.qg.Dart ↦ z.snd) heq
    obtain ⟨w,w',d',hw,hw',d'_mem,hd'₁,hd'₂⟩ :=
      xN hq hV deg_sum next_u hd'
    have q'_support:q'.support=q.support.tail:=by
      simp [q',support_tail_of_not_nil _ q_not_nil]
    obtain ⟨i,i_lt,hi⟩ :=List.getElem_of_mem d'_mem
    simp only [length_darts] at i_lt
    have hi_darts:i < q.darts.length:=by simpa using i_lt
    rw [← hi,q.darts_getElem_eq_getVert i hi_darts] at hd'₂
    rw [← hi,q.darts_getElem_eq_getVert i hi_darts] at hd'₁
    change q.getVert i =w' at hd'₁
    change q.getVert (i+1) = w at hd'₂
    have i_nz:i ≠ 0:=by
      rintro rfl
      have huw':u=w':=by simpa using hd'₁
      exact G.loopless.irrefl _ (huw' ▸ hw'.symm)
    have i_min_1:i-1 < q'.darts.length:=by
      have q'_length:q'.length=q.length-1:=by
        simp [transfer_transfer,length_copy,length_transfer,q']
      simp [q'_length]
      omega
    have hd''₁: (q'.darts[i-1]).fst=w':=by
      rw [q'.darts_getElem_eq_getVert (i-1) i_min_1]
      change q'.getVert (i-1) = w'
      rw [show q'.getVert (i-1) = q.tail.getVert (i-1) by
        simp only [Walk.getVert_eq_getD_support,support_copy,support_transfer,q']]
      rw [q.getVert_tail,show i -1+1=i by omega,hd'₁]
    have hd''₂: (q'.darts[i-1]).snd=w:=by
      rw [q'.darts_getElem_eq_getVert (i-1) i_min_1]
      change q'.getVert (i-1+1) = w
      rw [show q'.getVert (i-1+1) = q.tail.getVert (i-1+1) by
        simp only [Walk.getVert_eq_getD_support,support_copy,support_transfer,q']]
      rw [q.getVert_tail,show i -1+1+1=i+1 by omega,hd'₂]
    have w'_ne_u:w' ≠ u:=fun eq ↦ by simp [eq] at hw'
    have Hamiltonian:=
      zi hV perm_q' w'_ne_u hw' hw q'.darts[i-1]
      (List.getElem_mem i_min_1) hd''₁ hd''₂
    exact nonHamiltonian Hamiltonian
private theorem yt {n} (hG: ¬IsHamiltonian G) :
    ¬IsHamiltonian (qg^[n] G) :=by
  classical
  induction n with
  | zero=> simpa
  | succ m ih=>
    rw [add_comm]
    contrapose ih
    simp only [iterate_add_apply,iterate_one] at ih ⊢
    exact yp ih
theorem sI:IsHamiltonian (qE G) ↔ IsHamiltonian G :=by
  classical
  apply Iff.intro <;> intro hG
  · unfold qE Erdos556.Function.v3 at hG
    contrapose hG
    exact yt hG
  · exact IsHamiltonian.mono (rs _) hG
private theorem wg (hV:3 ≤ Fintype.card V) :
    (⊤ : SimpleGraph V).IsHamiltonian:=by
  classical
  obtain ⟨r,hr⟩ : ∃ r,Fintype.card V =r+3:=
    ⟨Fintype.card V -3,by omega⟩
  let e :Fin (r+3) ≃ V:=by
    simpa [hr] using (Fintype.equivFin V).symm
  let f :cycleGraph (r+3) →g (⊤ : SimpleGraph V) :=
    ⟨fun x ↦ e x,fun {a b} hab ↦ by
      simp only [top_adj,ne_eq]
      exact e.injective.ne hab.ne⟩
  let p := (cycleGraph.cycle r).map f
  intro _
  refine ⟨f 0,p,?_⟩
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_,?_⟩
  · exact cycleGraph.isCycle_cycle.map e.injective
  · simp [p,hr]
theorem x3 [DecidableRel G.Adj] (hV: (Fintype.card V) ≥ 3)
    (hG: ∀ u,2*G.degree u ≥ (Fintype.card V)) : G.IsHamiltonian:=by
  classical
  suffices G.qE= (⊤ : SimpleGraph V) from
    sI.mp (this ▸ wg hV)
  rw [eq_top_iff]
  intro u v ne
  simp only [top_adj,ne_eq] at ne
  apply rK G ne
  calc
    (Fintype.card V) ≤ G.degree u +G.degree v :=by
      have:=hG u
      have:=hG v
      omega
    _ ≤ G.qE.degree u +G.qE.degree v :=
      add_le_add (G.degree_le_of_le (v:=u) (rs G))
        (G.degree_le_of_le (v:=v) (rs G))
end SimpleGraph
end d0
section cB
namespace Erdos556
open SimpleGraph
def ed {k n :ℕ} (h:k ≤ n) :
    (pathGraph k).Copy (pathGraph n) where
  toHom:=
    { toFun:=Fin.castLE h
      map_rel':=by
        intro a b hab
        simpa only [pathGraph_adj,Fin.val_castLE] using hab}
  injective':=fun _ _ he=> Fin.ext (congrArg (Fin.val (n:=n)) he)
theorem wH {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {u v :V} (p:G.Walk u v) (hp:p.IsHamiltonian)
    (hcard:3 ≤ Fintype.card V) (hdeg:Fintype.card V ≤ G.degree u +G.degree v) :
    G.IsHamiltonian:=by
  classical
  have hlen:=hp.length_eq
  have hlen₂:2 ≤ p.length:=by omega
  have hne:u ≠ v:=by
    intro h
    have heq:p.getVert 0 =p.getVert p.length:=by simpa using h
    have hi:0=p.length:=hp.isPath.getVert_injOn (by simp) (by simp) heq
    omega
  have hcl:=G.rs
  have hcladj:G.qE.Adj u v:=G.rK hne
    (hdeg.trans (Nat.add_le_add (G.degree_le_of_le (v:=u) hcl)
      (G.degree_le_of_le (v:=v) hcl)))
  have hsub: ∀ e ∈ p.edges,e ∈ G.qE.edgeSet:=
    fun _ he ↦ edgeSet_mono hcl (p.edges_subset_edgeSet he)
  let p':=p.transfer G.qE hsub
  have hp':p'.IsHamiltonian:=by
    apply (hp.isPath.transfer hsub).isHamiltonian_of_mem
    intro x
    rw [Walk.support_transfer]
    exact hp.mem_support x
  let q :=Walk.cons hcladj.symm p'
  have hq:q.IsCycle:=by
    apply (Walk.cons_isCycle_iff p' hcladj.symm).mpr
    refine ⟨hp'.isPath,?_⟩
    intro he
    have h :=hp'.isPath.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    have hp'len:p'.length=p.length:=Walk.length_transfer p hsub
    omega
  have hqham:q.IsHamiltonianCycle:=by
    apply Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
    refine ⟨hq,?_⟩
    dsimp only [q,p']
    rw [Walk.length_cons,Walk.length_transfer]
    omega
  exact (SimpleGraph.sI (G:=G)).mp (fun _ ↦ ⟨v,q,hqham⟩)
theorem s7 {V:Type*} [Fintype V]
    [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {u v :V} (p:G.Walk u v) (hp:p.IsPath)
    (hlen:2 ≤ p.length)
    (hdeg:p.length+1 ≤
      (G.induce {x | x ∈ p.support}).degree ⟨u,p.start_mem_support⟩ +
      (G.induce {x | x ∈ p.support}).degree ⟨v,p.end_mem_support⟩) :
    cycleGraph (p.length+1) ⊑ G.induce {x | x ∈ p.support} :=by
  classical
  let S :Set V := {x | x ∈ p.support}
  let p':=p.induce S (fun _ hx ↦ hx)
  have hp':p'.IsPath:=by
    apply (Walk.isPath_map_iff_of_injective (f:= (Embedding.induce (G:=G) S).toHom)
      (p:=p') (Embedding.induce (G:=G) S).injective).mp
    rw [Walk.map_induce]
    exact hp
  have hham:p'.IsHamiltonian:=by
    apply hp'.isHamiltonian_of_mem
    intro x
    rw [Walk.support_induce]
    simpa only [List.mem_attachWith] using (show x.val ∈ p.support from x.property)
  have hcard:Fintype.card S =p.length+1:=by
    have hS:S= (p.support.toFinset:Set V) :=by ext x;simp [S]
    calc
      Fintype.card S =S.ncard:=Nat.card_eq_fintype_card.symm
      _=p.support.toFinset.card:=by rw [hS,Set.ncard_coe_finset]
      _=p.length+1:=by
        rw [List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support]
  have hG:=wH (G.induce S) p' hham
    (by rw [hcard];omega) (by rw [hcard];exact hdeg)
  obtain ⟨z,q,hq⟩ :=hG (by rw [hcard];omega)
  have hc:cycleGraph (p.length+1) ⊑ G.induce S :=
    (cycleGraph_isContained_iff (by omega)).mpr
      ⟨z,q,hq.isCycle,hq.length_eq.trans hcard⟩
  exact hc
theorem uz {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {u v :V} (p:G.Walk u v) (hp:p.IsPath)
    (hlen:2 ≤ p.length)
    (hdeg:p.length+1 ≤
      (G.induce {x | x ∈ p.support}).degree ⟨u,p.start_mem_support⟩ +
      (G.induce {x | x ∈ p.support}).degree ⟨v,p.end_mem_support⟩) :
    cycleGraph (p.length+1) ⊑ G:=
  (s7 G p hp hlen hdeg).trans
    (Embedding.induce {x | x ∈ p.support}).isContained
theorem vK {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (hconn:G.Connected) {v:V} (q:G.Walk v v) (hq:q.IsCycle)
    (hmax: ∀ {a b :V} (p:G.Walk a b),p.IsPath → p.length < q.length) :
    G.IsHamiltonian:=by
  classical
  have hall: ∀ x,x ∈ q.support:=by
    intro x
    by_contra hx
    obtain ⟨p⟩ :=hconn.preconnected v x
    obtain ⟨d,_,hd,hdout⟩ :=p.exists_boundary_dart {z | z ∈ q.support}
      q.start_mem_support hx
    let r :=q.rotate d.fst hd
    have hr:r.IsCycle:=hq.rotate hd
    have houts:d.snd ∉ r.tail.support:=by
      intro hmem
      have hmem':d.snd ∈ r.support:=by
        rw [← Walk.cons_support_tail hr.not_nil]
        exact List.mem_cons_of_mem _ hmem
      exact hdout ((q.mem_support_rotate_iff d.fst hd).mp hmem')
    have hp':=hr.isPath_tail.concat houts d.adj
    have hlt:=hmax _ hp'
    have heq: (r.tail.concat d.adj).length=q.length:=by
      rw [Walk.length_concat,Walk.length_tail,Walk.length_rotate]
      exact Nat.sub_add_cancel (by have:=hq.three_le_length;omega)
    rw [heq] at hlt
    exact hlt.false
  refine fun _ ↦ ⟨v,q,⟨hq,?_⟩⟩
  apply hq.isPath_tail.isHamiltonian_of_mem
  intro x
  have hx:=hall x
  rw [← Walk.cons_tail_support q] at hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact q.tail.end_mem_support
  · rwa [Walk.support_tail_of_not_nil q hq.not_nil]
lemma sD {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Set V) [DecidablePred (· ∈ S)]
    (v:V) (hv:v ∈ S) (hwithin: ∀ w,G.Adj v w → w ∈ S) :
    (G.induce S).degree ⟨v,hv⟩ = G.degree v :=by
  classical
  let e : (G.induce S).neighborSet ⟨v,hv⟩ ≃ G.neighborSet v :=
    { toFun:=fun w ↦ ⟨w.val.val,w.property⟩
      invFun:=fun w ↦ ⟨⟨w.val,hwithin w.val w.property⟩,w.property⟩
      left_inv:=fun _ ↦ rfl
      right_inv:=fun _ ↦ rfl}
  rw [← card_neighborSet_eq_degree,← card_neighborSet_eq_degree]
  exact Fintype.card_congr e
theorem sV {V:Type*}
    [Fintype V] [DecidableEq V] (G:SimpleGraph V) [DecidableRel G.Adj]
    (hconn:G.Connected) {u v :V} (p:G.Walk u v) (hp:p.IsPath)
    (hmax: ∀ {a b :V} (q:G.Walk a b),q.IsPath → q.length ≤ p.length)
    (hlen:2 ≤ p.length) (hdeg:p.length+1 ≤ G.degree u +G.degree v) :
    G.IsHamiltonian:=by
  classical
  have hstart: ∀ w,G.Adj u w → w ∈ p.support:=by
    intro w hw
    by_contra hnot
    have hq: (Walk.cons hw.symm p).IsPath:= (Walk.cons_isPath_iff _ _).mpr ⟨hp,hnot⟩
    have h :=hmax _ hq
    simp only [Walk.length_cons] at h
    omega
  have hend: ∀ w,G.Adj v w → w ∈ p.support:=by
    intro w hw
    by_contra hnot
    have h :=hmax _ (hp.concat hnot hw)
    simp only [Walk.length_concat] at h
    omega
  have hcopy:=uz G p hp hlen (by
    rw [sD G {x | x ∈ p.support} u p.start_mem_support hstart,
      sD G {x | x ∈ p.support} v p.end_mem_support hend]
    exact hdeg)
  obtain ⟨x,q,hq,hqlen⟩ := (cycleGraph_isContained_iff (by omega)).mp hcopy
  apply vK G hconn q hq
  intro a b r hr
  rw [hqlen]
  exact Nat.lt_succ_of_le (hmax r hr)
end Erdos556
end cB
section dh
namespace Erdos556
open SimpleGraph
theorem z8 {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (u:V) (hu:2 ≤ G.degree u) :
    ∃ (a b :V) (p:G.Walk a b),p.IsPath ∧ p.length=2:=by
  classical
  have hnb:1 < (G.neighborFinset u).card:=by
    rw [card_neighborFinset_eq_degree]
    omega
  obtain ⟨a,ha,b,hb,hab⟩ :=Finset.one_lt_card.mp hnb
  have hua:G.Adj u a:= (G.mem_neighborFinset u a).mp ha
  have hub:G.Adj u b:= (G.mem_neighborFinset u b).mp hb
  let p :=Walk.cons hua.symm (Walk.cons hub Walk.nil)
  refine ⟨a,b,p,?_,rfl⟩
  simp [p,Walk.cons_isPath_iff,hua.ne.symm,hub.ne,hab]
theorem ur {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (hconn:G.Connected)
    (d:ℕ) (hd:2 ≤ d) (hdeg: ∀ v,d ≤ G.degree v) :
    ∃ (u v :V) (p:G.Walk u v),p.IsPath ∧
      min (2*d+1) (Fintype.card V) ≤ p.length+1:=by
  classical
  have:Nonempty V :=hconn.nonempty
  obtain ⟨u,v,p,hp,hmax⟩ :=Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨u,v,p,hp,?_⟩
  by_contra hlong
  have hshort:p.length+1 < min (2*d+1) (Fintype.card V) :=by omega
  obtain ⟨a,b,q,hq,hqlen⟩ :=z8 G u (hd.trans (hdeg u))
  have hlen:2 ≤ p.length:=by
    have h :=hmax a b q hq
    omega
  have hham:=sV G hconn p hp
    (fun {_ _} q hq=> hmax _ _ q hq) hlen (by
      have hu:=hdeg u
      have hv:=hdeg v
      omega)
  obtain ⟨z,q,hq⟩ :=hham (by omega)
  have h :=hmax _ _ q.tail hq.isCycle.isPath_tail
  rw [Walk.length_tail,hq.length_eq] at h
  omega
theorem wk {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj]
    (hmax: ∀ {u v} (p:G.Walk u v),p.IsPath → p.length ≤ 1) (v:V) :
    G.degree v ≤ 1 :=by
  classical
  by_contra h
  obtain ⟨a,b,p,hp,hlen⟩ :=z8 G v (by omega)
  have:=hmax p hp
  omega
theorem vW {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj]
    (hmax: ∀ {u v} (p:G.Walk u v),p.IsPath → p.length ≤ 0) (v:V) :
    G.degree v =0:=by
  classical
  by_contra h
  have hn: (G.neighborFinset v).Nonempty:=by
    rw [← Finset.card_pos,card_neighborFinset_eq_degree]
    omega
  obtain ⟨w,hw⟩ :=hn
  have hadj:G.Adj v w:= (G.mem_neighborFinset v w).mp hw
  have hp: (Walk.cons hadj Walk.nil).IsPath:=by
    simp [Walk.cons_isPath_iff,hadj.ne]
  have:=hmax _ hp
  simp only [Walk.length_cons,Walk.length_nil] at this
  omega
theorem tc {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (C:G.ConnectedComponent)
    [Fintype C] [DecidableRel C.toSimpleGraph.Adj] (v:C) :
    C.toSimpleGraph.degree v =G.degree v.val:=by
  classical
  let e :C.toSimpleGraph.neighborSet v ≃ G.neighborSet v.val:=
    { toFun:=fun w => ⟨w.val.val,w.property⟩
      invFun:=fun w => ⟨⟨w.val,C.mem_supp_of_adj_mem_supp v.property w.property⟩,
        w.property⟩
      left_inv:=fun _ => rfl
      right_inv:=fun _ => rfl}
  rw [← card_neighborSet_eq_degree,← card_neighborSet_eq_degree]
  exact Fintype.card_congr e
theorem wP {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ) (hk:2 ≤ k)
    (hmin: ∀ v,k < 2*G.degree v)
    (hmax: ∀ {u v} (p:G.Walk u v),p.IsPath → p.length ≤ k) (v:V) :
    G.degree v ≤ k :=by
  classical
  let C :=G.connectedComponentMk v
  have hd: ∀ w:C,k/2+1 ≤ C.toSimpleGraph.degree w :=by
    intro w
    rw [tc]
    have h :=hmin w.val
    omega
  obtain ⟨a,b,p,hp,hlen⟩ :=ur C.toSimpleGraph
    C.connected_toSimpleGraph (k/2+1) (by omega) hd
  have hp': (p.map C.toSimpleGraph_hom).IsPath:=
    hp.map (by intro x y h;exact Subtype.ext h)
  have hbound:=hmax _ hp'
  rw [Walk.length_map] at hbound
  have hcard:Fintype.card C ≤ k +1:=by omega
  let v':C:= ⟨v,ConnectedComponent.connectedComponentMk_mem⟩
  have hdeg:=C.toSimpleGraph.degree_lt_card_verts v'
  rw [tc] at hdeg
  exact Nat.le_of_lt_succ (hdeg.trans_le hcard)
theorem vi {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ)
    (hdeg: ∀ v,G.degree v ≤ k) :
    2*G.edgeFinset.card ≤ k*Fintype.card V :=by
  classical
  calc
    2*G.edgeFinset.card= ∑ v,G.degree v :=G.sum_degrees_eq_twice_card_edges.symm
    _ ≤ ∑ _v:V,k:=Finset.sum_le_sum fun v _=> hdeg v
    _=k*Fintype.card V :=by simp [Nat.mul_comm]
universe u
private theorem a3 (N:ℕ) :
    ∀ (V:Type u) [Fintype V]
      (G:SimpleGraph V) [DecidableRel G.Adj],Fintype.card V =N →
      ∀ k :ℕ,
      (∀ {a b :V} (p:G.Walk a b),p.IsPath → p.length ≤ k) →
      2*G.edgeFinset.card ≤ k*Fintype.card V :=by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih=>
      intro V _ G _ hcard k hmax
      classical
      by_cases hsmall:k ≤ 1
      · apply vi G k
        intro v
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsmall with rfl | rfl
        · exact (vW G hmax v).le
        · exact wk G hmax v
      · have hk:2 ≤ k:=by omega
        by_cases hlow: ∃ v,2*G.degree v ≤ k
        · obtain ⟨v,hv⟩ :=hlow
          let S :Set V := {v}ᶜ
          let H :=G.induce S
          have hS:Fintype.card S =Fintype.card V -1:=by
            simpa [S] using Set.card_ne_eq v
          have hpos:0 < Fintype.card V :=Fintype.card_pos_iff.mpr ⟨v⟩
          have hlt:Fintype.card S < N :=by omega
          have hmaxH: ∀ {a b :S} (p:H.Walk a b),p.IsPath → p.length ≤ k:=by
            intro a b p hp
            let f := (Embedding.induce (G:=G) S).toHom
            have hp': (p.map f).IsPath:=hp.map (by
              intro x y h
              exact Subtype.ext h)
            simpa only [Walk.length_map] using hmax (p.map f) hp'
          have hrec:=ih (Fintype.card S) hlt S H rfl k hmaxH
          have hedge:H.edgeFinset.card+G.degree v =G.edgeFinset.card:=by
            dsimp [H,S]
            rw [card_edgeFinset_induce_compl_singleton,
              card_edgeFinset_deleteIncidenceSet]
            exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)
          have hcardadd:Fintype.card S +1=Fintype.card V :=by omega
          nlinarith
        · apply vi G k
          apply wP G k hk
          · intro v
            by_contra h
            exact hlow ⟨v,by omega⟩
          · exact hmax
theorem ty {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ)
    (hmax: ∀ {a b :V} (p:G.Walk a b),p.IsPath → p.length ≤ k) :
    2*G.edgeFinset.card ≤ k*Fintype.card V :=
  a3 (Fintype.card V) V G rfl k hmax
theorem z6 {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ)
    (he:k*Fintype.card V < 2 *G.edgeFinset.card) :
    ∃ (a b :V) (p:G.Walk a b),p.IsPath ∧ k < p.length:=by
  classical
  by_contra h
  push Not at h
  have hb:=ty G k (fun p hp=> h _ _ p hp)
  omega
end Erdos556
end dh
section db
namespace Erdos556
open Filter
open scoped Topology
theorem y6 {r:ℝ} (hr0:0 ≤ r) (hr1:r < 1) :
    Tendsto (fun n :ℕ=> ((n:ℝ) + 1) ^ 2*r^n) atTop (𝓝 0) :=by
  have h2:=tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0 hr1
  have h1:=tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have h0:=tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  convert (h2.add (h1.const_mul 2)).add h0 using 1
  · ext n
    ring
  · norm_num
theorem ti (K:ℕ) (hK:0 < K) (C:ℝ) (hC:0 ≤ C)
    {r:ℝ} (hr0:0 ≤ r) (hr1:r < 1) :
    Tendsto (fun n :ℕ=> (n:ℝ) ^ 2*C*r^ (n/K)) atTop (𝓝 0) :=by
  have hdiv:Tendsto (fun n :ℕ=> n /K) atTop atTop:=
    Nat.tendsto_div_const_atTop hK.ne'
  have hmajor:Tendsto
      (fun n :ℕ=> ((K:ℝ) ^ 2*C) * (((n/K:ℕ) : ℝ) + 1) ^ 2*r^ (n/K))
      atTop (𝓝 0) :=by
    convert ((y6 hr0 hr1).comp hdiv).const_mul
      ((K:ℝ) ^ 2*C) using 1
    · ext n
      simp only [Function.comp_apply]
      ring
    · simp
  apply squeeze_zero (fun n => by positivity) (fun n => ?_) hmajor
  have hn:n ≤ K* (n/K+1) :=by
    have hmod:=Nat.mod_lt n hK
    have hdecomp:=Nat.mod_add_div n K
    nlinarith
  have hnR: (n:ℝ) ≤ (K:ℝ) * (((n/K:ℕ) : ℝ) + 1) :=by
    exact_mod_cast hn
  have hsq: (n:ℝ) ^ 2 ≤ ((K:ℝ) * (((n/K:ℕ) : ℝ) + 1)) ^ 2:=by
    gcongr
  calc
    (n:ℝ) ^ 2*C*r^ (n/K) ≤
        ((K:ℝ) * (((n/K:ℕ) : ℝ) + 1)) ^ 2*C*r^ (n/K) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hC) (pow_nonneg hr0 _)
    _= ((K:ℝ) ^ 2*C) * (((n/K:ℕ) : ℝ) + 1) ^ 2*r^ (n/K) :=by ring
theorem uW (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1)
    (L K a:ℕ) (hK:0 < K) :
    ∀ᶠ n :ℕ in atTop,
      (n:ℝ) ^ 2* (a+1) * (1-q^L) ^ (n/K) < 1/2:=by
  have hr0:0 ≤ 1-q^L:=sub_nonneg.mpr (pow_le_one₀ hq0.le hq1)
  have hr1:1-q^L < 1:=by have:=pow_pos hq0 L;linarith
  have h :=ti K hK ((a:ℝ) + 1) (by positivity) hr0 hr1
  exact h.eventually (gt_mem_nhds (by norm_num: (0:ℝ) < 1/2))
end Erdos556
end db
section dg
namespace Erdos556
open SimpleGraph Finset Filter
theorem td {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d D m a:ℕ)
    (hconn:q8 G (b+3*D+3))
    (hnonbip:qT G (b+3*D+3))
    (hd:0 < d) (hdeg: ∀ w,d+ (b+3*D+3) ≤ G.degree w)
    (hN:Fintype.card V ≤ D *d)
    (hbound: ((a+1) * m) * (12*D+3) ≤ b)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1)
    (hfail: (Fintype.card V :ℝ) ^ 2* (a+1) *
      (1-q^ (12*D+3)) ^ m < 1/2)
    (hV:0 < Fintype.card V) :
    ∃ R :Finset V,(R.card:ℝ) ≤ 2*q*Fintype.card V ∧
      ∀ u v,u ≠ v → ∀ S,S.card ≤ a →
        qZ G (12*D+3) u v (R \ S) :=by
  classical
  let I := {uv:V × V//uv.1 ≠ uv.2}
  let P :I → Finset V → Prop:=fun uv=> qZ G (12*D+3) uv.val.1 uv.val.2
  have hav (uv:I) (S:Finset V) (hS:S.card ≤ b) :
      ∃ T :Finset V,P uv T ∧ T.card ≤ 12*D+3 ∧ Disjoint S T:=
    vz G b d D hconn hnonbip hd hdeg hN
      uv.val.1 uv.val.2 uv.property S hS
  have hI: (Fintype.card I :ℝ) ≤ (Fintype.card V :ℝ) ^ 2:=by
    have h :=Fintype.card_le_of_injective (fun uv:I=> uv.val) Subtype.val_injective
    rw [Fintype.card_prod] at h
    rw [pow_two]
    exact_mod_cast h
  have hr:0 ≤ 1-q^ (12*D+3) :=sub_nonneg.mpr (pow_le_one₀ hq0.le hq1)
  have hf: (Fintype.card I :ℝ) * (a+1) * (1-q^ (12*D+3)) ^ m < 1/2:=by
    apply lt_of_le_of_lt _ hfail
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hI (by positivity)) (pow_nonneg hr _)
  obtain ⟨R,hR,hhit⟩ :=uA P q hq0 hq1 (12*D+3) b m a
    hbound hav hf hV
  refine ⟨R,hR,?_⟩
  intro u v huv S hS
  obtain ⟨T,hTR,hP,_,hST⟩ :=hhit ⟨(u,v),huv⟩ S hS
  apply hP.mono
  intro x hx
  exact mem_sdiff.mpr ⟨hTR hx,fun hxS=> Finset.disjoint_left.mp hST hxS hx⟩
theorem xw (D B a:ℕ) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (b d :ℕ),
      N₀ ≤ Fintype.card V → q8 G (b+3*D+3) →
      qT G (b+3*D+3) →
      (∀ w,d+ (b+3*D+3) ≤ G.degree w) → Fintype.card V ≤ D *d →
      Fintype.card V ≤ B *b →
      ∃ R :Finset V,(R.card:ℝ) ≤ 2*q*Fintype.card V ∧
        ∀ u v,u ≠ v → ∀ S,S.card ≤ a →
          qZ G (12*D+3) u v (R \ S) :=by
  let L :=12*D+3
  let K :=B* ((a+1) * L)
  have hL:0 < L:=by dsimp [L];omega
  have hK:0 < K:=Nat.mul_pos hB (Nat.mul_pos (by omega) hL)
  obtain ⟨N₁,hN₁⟩ :=eventually_atTop.mp (uW q hq0 hq1 L K a hK)
  refine ⟨max N₁ 1,?_⟩
  intro V _ _ G _ b d hN hc hnb hg hd hb
  have hV:0 < Fintype.card V :=by omega
  have hdpos:0 < d:=by nlinarith
  let m :=Fintype.card V /K
  have hbudget: ((a+1) * m) * L ≤ b:=by
    have hmul:B* (((a+1) * m) * L) ≤ B*b:=by
      calc
        B* (((a+1) * m) * L) = m*K:=by dsimp [K];ring
        _ ≤ Fintype.card V :=Nat.div_mul_le_self _ _
        _ ≤ B*b:=hb
    nlinarith
  exact td G b d D m a hc hnb hdpos hg hd hbudget q hq0 hq1
    (hN₁ _ (by omega)) hV
end Erdos556
end dg
section cq
namespace Erdos556
open SimpleGraph
theorem wL {V:Type*} {G:SimpleGraph V}
    (R:Finset V) (L k :ℕ) (hk:1 ≤ k)
    (hres: ∀ u v,u ≠ v → qZ G L u v R)
    (hodd: ∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k)
    {u v :V} (p:G.Walk u v) (hp:p.IsPath) (hav: ∀ x ∈ p.support,x ∉ R) :
    p.length ≤ 2*k:=by
  by_contra hlen
  have huv:u ≠ v:=by
    intro h
    have hz:= ((hp.nil_iff_eq).mpr h).length_eq_zero
    omega
  obtain ⟨c,hc,ho,hge,_⟩ :=sZ
    p hp (by omega) L R hav (hres u v huv)
  have hle:=hodd u c hc ho
  omega
theorem xO {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (R:Finset V) (L k :ℕ) (hk:1 ≤ k)
    (hres: ∀ u v,u ≠ v → qZ G L u v R)
    (hodd: ∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) :
    G.edgeFinset.card ≤ (k+R.card) * Fintype.card V :=by
  classical
  let U := (R:Set V)ᶜ
  let H :=G.induce U
  let f :H ↪g G :=SimpleGraph.Embedding.induce U
  have hpaths {u v :U} (p:H.Walk u v) (hp:p.IsPath) : p.length ≤ 2*k:=by
    have h :=wL R L k hk hres hodd
      (p.map f.toHom) (hp.map f.injective) (by
        intro x hx
        rw [Walk.support_map,List.mem_map] at hx
        obtain ⟨y,_,hy⟩ :=hx
        subst x
        exact y.property)
    simpa only [Walk.length_map] using h
  have hbound:=ty H (2*k) hpaths
  have hcard:=Fintype.card_le_of_injective (fun x :U=> x.val) Subtype.val_injective
  have hretained:H.edgeFinset.card ≤ k*Fintype.card V :=by
    have hmul:=Nat.mul_le_mul_left k hcard
    nlinarith
  have hdeleted:=rc G R
  change G.edgeFinset.card ≤ H.edgeFinset.card+R.card*Fintype.card V at hdeleted
  nlinarith
theorem ua (D B :ℕ) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (b d k:ℕ),
      N₀ ≤ Fintype.card V → q8 G (b+3*D+3) →
      qT G (b+3*D+3) →
      (∀ w,d+ (b+3*D+3) ≤ G.degree w) → Fintype.card V ≤ D *d →
      Fintype.card V ≤ B *b → 1 ≤ k →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      (G.edgeFinset.card:ℝ) ≤ (k:ℝ) * Fintype.card V +
        2*q* (Fintype.card V :ℝ) ^ 2:=by
  obtain ⟨N₀,hN₀⟩ :=xw D B 0 hB q hq0 hq1
  refine ⟨N₀,?_⟩
  intro V _ _ G _ b d k hN hc hnb hg hd hb hk ho
  obtain ⟨R,hR,hres⟩ :=hN₀ G b d hN hc hnb hg hd hb
  have hres' (u v :V) (huv:u ≠ v) : qZ G (12*D+3) u v R :=by
    simpa only [Finset.sdiff_empty] using hres u v huv ∅ (by simp)
  have he:=xO G R (12*D+3) k hk hres' ho
  have heR: (G.edgeFinset.card:ℝ) ≤ ((k:ℝ) + R.card) * Fintype.card V :=by
    exact_mod_cast he
  have hm:=mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg (Fintype.card V) :
    (0:ℝ) ≤ Fintype.card V)
  nlinarith
end Erdos556
end cq
section cN
namespace Erdos556
open SimpleGraph
universe u
variable {V:Type u} [Fintype V] [DecidableEq V]
variable {G:SimpleGraph V}
def qh (G:SimpleGraph V) : Prop:=
  3 ≤ Fintype.card V ∧ G.Connected ∧
    ∀ v :V,(G.induce ({v}ᶜ:Set V)).Connected
namespace qh
omit [DecidableEq V] in
theorem xV (hG:qh G) : 3 ≤ Fintype.card V :=hG.1
omit [DecidableEq V] in
theorem connected (hG:qh G) : G.Connected:=hG.2.1
omit [DecidableEq V] in
theorem t9 (hG:qh G) (v:V) :
    (G.induce ({v}ᶜ:Set V)).Connected:=
  hG.2.2 v
omit [DecidableEq V] in
theorem nontrivial (hG:qh G) : Nontrivial V :=by
  classical
  exact Fintype.one_lt_card_iff_nontrivial.mp (by
    have h :=hG.xV
    omega)
omit [DecidableEq V] in
theorem exists_ne (hG:qh G) (v:V) : ∃ w :V,w ≠ v:=by
  classical
  let:=hG.nontrivial
  exact _root_.exists_ne v
omit [DecidableEq V] in
theorem dU (hG:qh G) (v:V) :
    ∃ x y:V,x ≠ v ∧ y ≠ v ∧ x ≠ y:=by
  classical
  have hcard:2 ≤ Fintype.card ({v}ᶜ:Set V) :=by
    rw [Fintype.card_compl_set,Set.card_singleton]
    have h :=hG.xV
    omega
  let:Nontrivial ({v}ᶜ:Set V) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,y,hxy⟩ :=exists_pair_ne ({v}ᶜ:Set V)
  have hx: (x:V) ≠ v:=by
    simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using x.2
  have hy: (y:V) ≠ v:=by
    simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using y.2
  exact ⟨x,y,hx,hy,fun h ↦ hxy (Subtype.ext h)⟩
omit [DecidableEq V] in
theorem sT (hG:qh G) (z:V) {x y :V}
    (hx:x ≠ z) (hy:y ≠ z) :
    ∃ p :G.Walk x y,p.IsPath ∧ z ∉ p.support:=by
  classical
  let x': ({z}ᶜ:Set V) := ⟨x,hx⟩
  let y': ({z}ᶜ:Set V) := ⟨y,hy⟩
  obtain ⟨p,hp⟩ := (hG.t9 z).exists_isPath x' y'
  let e :G.induce ({z}ᶜ:Set V) ↪g G :=
    SimpleGraph.Embedding.induce ({z}ᶜ:Set V)
  let q :=p.map e.toHom
  have hqpath:q.IsPath:=hp.map e.injective
  have hqavoid:z ∉ q.support:=by
    intro hz
    have hsupport:q.support=p.support.map e :=by
      exact SimpleGraph.Walk.support_map e.toHom p
    rw [hsupport,List.mem_map] at hz
    obtain ⟨w,hw,hwz⟩ :=hz
    have hwne: (w:V) ≠ z:=by
      simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using w.2
    exact hwne hwz
  have hex:e x'=x:=by rfl
  have hey:e y'=y:=by rfl
  let q':G.Walk x y:=q.copy hex hey
  have hq'path:q'.IsPath:=
    (SimpleGraph.Walk.isPath_copy q hex hey).2 hqpath
  have hq'avoid:z ∉ q'.support:=by
    simpa only [q',SimpleGraph.Walk.support_copy] using hqavoid
  exact ⟨q',hq'path,hq'avoid⟩
end qh
structure te (G:SimpleGraph V) (A B :Set V) where
  a₁:V
  a₂:V
  b₁:V
  b₂:V
  p:G.Walk a₁ b₁
  q:G.Walk a₂ b₂
  p_isPath:p.IsPath
  q_isPath:q.IsPath
  a₁_mem:a₁ ∈ A
  a₂_mem:a₂ ∈ A
  b₁_mem:b₁ ∈ B
  b₂_mem:b₂ ∈ B
  disjoint_support:p.support.Disjoint q.support
  p_interior: ∀ x ∈ p.support.tail.dropLast,x ∉ A ∪ B
  q_interior: ∀ x ∈ q.support.tail.dropLast,x ∉ A ∪ B
namespace te
variable {A B :Set V}
end te
end Erdos556
namespace Erdos556
open SimpleGraph
theorem qh.iso {V W :Type*} [Fintype V] [Fintype W]
    {G:SimpleGraph V} {H:SimpleGraph W}
    (hG:qh G) (e:G ≃g H) : qh H :=by
  classical
  refine ⟨?_,hG.connected.map e.toHom e.surjective,?_⟩
  · rw [← Fintype.card_congr e.toEquiv]
    exact hG.xV
  · intro w
    have hbij:Set.BijOn e ({e.symm w}ᶜ:Set V) ({w}ᶜ:Set W) :=by
      refine ⟨?_,e.injective.injOn,?_⟩
      · intro x hx
        change e x ≠ w
        intro heq
        apply hx
        exact e.injective (heq.trans (e.apply_symm_apply w).symm)
      · intro y hy
        refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
        intro h
        exact hy (e.symm.injective h)
    let f :=e.induce hbij
    exact (hG.t9 (e.symm w)).map f.toHom f.surjective
end Erdos556
end cN
section dx
/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
namespace Erdos556
open SimpleGraph
universe u
variable {V:Type u} [Fintype V] [DecidableEq V]
variable {G:SimpleGraph V}
variable {A B S:Set V}
namespace te
end te
def ec (G:SimpleGraph V) (A B S:Set V) : Prop:=
  ∀ ⦃a b :V⦄,a ∈ A → b ∈ B →
    ∀ p :G.Walk a b,∃ x,x ∈ S ∧ x ∈ p.support
namespace qh
end qh
structure x7 (G:SimpleGraph V) (A B :Set V) where
  a₁:V
  a₂:V
  b₁:V
  b₂:V
  p:G.Walk a₁ b₁
  q:G.Walk a₂ b₂
  p_isPath:p.IsPath
  q_isPath:q.IsPath
  a₁_mem:a₁ ∈ A
  a₂_mem:a₂ ∈ A
  b₁_mem:b₁ ∈ B
  b₂_mem:b₂ ∈ B
  disjoint_support:p.support.Disjoint q.support
namespace x7
structure ee {a b :V} (p:G.Walk a b) (A B :Set V) where
  left:V
  right:V
  walk:G.Walk left right
  isPath:walk.IsPath
  left_mem:left ∈ A
  right_mem:right ∈ B
  support_subset:walk.support ⊆ p.support
  interior: ∀ x ∈ walk.support.tail.dropLast,x ∉ A ∪ B
end x7
namespace qh
end qh
end Erdos556
end dx
section cI
/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
The definitions `IsArm`, `ArmsDisj`, and the indexed-arc proof below are
adapted from `ListColoring.RubinCases` at commit
80a728c86f28222a58b11a777f9d22419fd2fb69 of
https://github.com/rkirov/list-color-function, released under Apache 2.0.
-/
namespace Erdos556
open SimpleGraph
variable {V:Type*} {G:SimpleGraph V}
theorem yg {v:V} {c:G.Walk v v} (hc:c.IsCycle)
    {a b :V} (ha:a ∈ c.support) (hb:b ∈ c.support) (hab:a ≠ b) :
    ∃ (p q :G.Walk a b),p.IsPath ∧ q.IsPath ∧
      1 ≤ p.length ∧ 1 ≤ q.length ∧ p.length+q.length=c.length ∧
      (∀ x ∈ p.support,x ∈ q.support → x=a ∨ x=b) ∧
      (∀ x,x ∈ c.support ↔ x ∈ p.support ∨ x ∈ q.support) ∧
      (∀ e,e ∈ p.edges → e ∈ c.edges) ∧
      (∀ e,e ∈ q.edges → e ∈ c.edges) :=by
  classical
  let c':G.Walk a a:=c.rotate a ha
  have hc':c'.IsCycle:= (SimpleGraph.Walk.isCycle_rotate ha).mpr hc
  have hb':b ∈ c'.support:=
    (SimpleGraph.Walk.mem_support_rotate_iff c a ha).mpr hb
  let p :G.Walk a b:=c'.takeUntil b hb'
  let r :G.Walk b a:=c'.dropUntil b hb'
  let q :G.Walk a b:=r.reverse
  have hdecomp:p.append r =c':=by
    exact c'.take_spec hb'
  have hpPath:p.IsPath:=hc'.isPath_takeUntil hb'
  have happCycle: (p.append r).IsCycle:=by
    rw [hdecomp]
    exact hc'
  have hrPath:r.IsPath:=by
    exact happCycle.isPath_of_append_right (SimpleGraph.Walk.not_nil_of_ne hab)
  have hqPath:q.IsPath:=hrPath.reverse
  have hpPos:1 ≤ p.length:=by
    have:0 < p.length:=SimpleGraph.Walk.not_nil_iff_lt_length.mp
      (SimpleGraph.Walk.not_nil_of_ne hab)
    omega
  have hqPos:1 ≤ q.length:=by
    have:0 < r.length:=SimpleGraph.Walk.not_nil_iff_lt_length.mp
      (SimpleGraph.Walk.not_nil_of_ne hab.symm)
    have:1 ≤ r.length:=by omega
    simpa [q] using this
  have hlen:p.length+q.length=c.length:=by
    have:=congrArg SimpleGraph.Walk.length hdecomp
    simpa [q,c',SimpleGraph.Walk.length_rotate] using this
  have htailNodup: (p.support.tail++r.support.tail).Nodup:=by
    rw [← SimpleGraph.Walk.tail_support_append]
    rw [hdecomp]
    exact hc'.support_nodup
  have hmeet: ∀ x ∈ p.support,x ∈ q.support → x=a ∨ x=b:=by
    intro x hxp hxq
    by_contra h
    push Not at h
    have hxpt:x ∈ p.support.tail:=
      (SimpleGraph.Walk.mem_support_iff p).mp hxp |>.resolve_left h.1
    have hxr:x ∈ r.support:=by
      simpa [q,SimpleGraph.Walk.support_reverse] using hxq
    have hxrt:x ∈ r.support.tail:=
      (SimpleGraph.Walk.mem_support_iff r).mp hxr |>.resolve_left h.2
    exact (List.disjoint_of_nodup_append htailNodup hxpt hxrt)
  have hsupp: ∀ x,x ∈ c.support ↔ x ∈ p.support ∨ x ∈ q.support:=by
    intro x
    rw [← SimpleGraph.Walk.mem_support_rotate_iff c a ha]
    change x ∈ c'.support ↔ x ∈ p.support ∨ x ∈ q.support
    rw [← hdecomp,SimpleGraph.Walk.mem_support_append_iff]
    simp only [q,SimpleGraph.Walk.support_reverse,List.mem_reverse]
  have hedg: ∀ e:Sym2 V,e ∈ c'.edges ↔ e ∈ c.edges:=fun _ ↦
    (SimpleGraph.Walk.rotate_edges c a ha).mem_iff
  have hpEdges: ∀ e,e ∈ p.edges → e ∈ c.edges:=by
    intro e he
    apply (hedg e).mp
    exact SimpleGraph.Walk.edges_takeUntil_subset_edges c' hb' he
  have hqEdges: ∀ e,e ∈ q.edges → e ∈ c.edges:=by
    intro e he
    apply (hedg e).mp
    apply SimpleGraph.Walk.edges_dropUntil_subset_edges c' hb'
    simpa [q,SimpleGraph.Walk.edges_reverse] using he
  exact ⟨p,q,hpPath,hqPath,hpPos,hqPos,hlen,hmeet,hsupp,hpEdges,hqEdges⟩
end Erdos556
end cI
section cL
/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
namespace Erdos556
open SimpleGraph
universe u
variable {V:Type u} [Fintype V] [DecidableEq V]
variable {G:SimpleGraph V}
def rg (G:SimpleGraph V) (x y :V) : Prop:=
  ∃ (z:V) (c:G.Walk z z),c.IsCycle ∧ x ∈ c.support ∧ y ∈ c.support
abbrev sg (V:Type u) :=Sum V Bool
def qA (G:SimpleGraph V) (A B :Set V) :
    SimpleGraph (sg V) where
  Adj s t:=
    match s,t with
    | Sum.inl x,Sum.inl y => G.Adj x y
    | Sum.inl x,Sum.inr false=> x ∈ A
    | Sum.inr false,Sum.inl x => x ∈ A
    | Sum.inl x,Sum.inr true=> x ∈ B
    | Sum.inr true,Sum.inl x => x ∈ B
    | Sum.inr _,Sum.inr _ => False
  symm:= ⟨by
    intro s t h
    cases s with
    | inl x =>
        cases t with
        | inl y => exact h.symm
        | inr i => cases i <;> exact h
    | inr i =>
        cases t with
        | inl x => cases i <;> exact h
        | inr k =>
            cases i <;> cases k <;> exact False.elim h⟩
  loopless:= ⟨by
    intro s h
    cases s with
    | inl x => exact h.ne rfl
    | inr i => cases i <;> exact False.elim h⟩
omit [DecidableEq V] [Fintype V] in
@[simp] theorem e3 {A B :Set V} {x y :V} :
    (qA G A B).Adj (Sum.inl x) (Sum.inl y) ↔ G.Adj x y:=
  Iff.rfl
omit [DecidableEq V] [Fintype V] in
@[simp] theorem dY {A B :Set V} {x:V} :
    (qA G A B).Adj (Sum.inl x) (Sum.inr false) ↔ x ∈ A:=
  Iff.rfl
omit [DecidableEq V] [Fintype V] in
@[simp] theorem u2 {A B :Set V} {x:V} :
    (qA G A B).Adj (Sum.inr false) (Sum.inl x) ↔ x ∈ A:=
  Iff.rfl
omit [DecidableEq V] [Fintype V] in
@[simp] theorem dM {A B :Set V} {x:V} :
    (qA G A B).Adj (Sum.inl x) (Sum.inr true) ↔ x ∈ B:=
  Iff.rfl
omit [DecidableEq V] [Fintype V] in
@[simp] theorem sJ {A B :Set V} {x:V} :
    (qA G A B).Adj (Sum.inr true) (Sum.inl x) ↔ x ∈ B:=
  Iff.rfl
def qn (G:SimpleGraph V) (A B :Set V) :
    G ↪g qA G A B where
  toFun:=Sum.inl
  inj':=Sum.inl_injective
  map_rel_iff':=Iff.rfl
namespace qh
omit [DecidableEq V] in
theorem vX (hG:qh G) {x y :V}
    (hxy:G.Adj x y) :
    ∃ c :G.Walk x x,c.IsCycle ∧ y ∈ c.support:=by
  classical
  obtain ⟨r,s,hry,hsy,hrs⟩ :=hG.dU y
  let t :V:=if r =x then s else r
  have hty:t ≠ y:=by
    dsimp [t]
    split <;> assumption
  have htx:t ≠ x:=by
    dsimp [t]
    split_ifs with hrx
    · exact fun hsx ↦ hrs (hrx.trans hsx.symm)
    · exact hrx
  obtain ⟨p,hp,hpy⟩ :=hG.sT y hxy.ne hty
  have hp_nonNil: ¬ p.Nil:=by
    exact Walk.not_nil_of_ne htx.symm
  let w :V:=p.snd
  have hxw:G.Adj x w:=p.adj_snd hp_nonNil
  have hwy:w ≠ y:=by
    intro h
    exact hpy (h ▸ List.mem_of_mem_tail (p.snd_mem_tail_support hp_nonNil))
  obtain ⟨q₀,hq₀,hq₀x⟩ :=
    hG.sT x hxy.ne.symm hxw.ne.symm
  let q :G.Walk y x:=q₀.concat hxw.symm
  have hq:q.IsPath:=hq₀.concat hq₀x hxw.symm
  have hedge:s(x,y) ∉ q.edges:=by
    intro he
    have he':s(y,x) ∈ q.edges:=by simpa [Sym2.eq_swap] using he
    have hlen:q.length=1:=hq.length_eq_one_of_mem_edges he'
    have hq₀len:q₀.length=0:=by
      have:q.length=q₀.length+1:=by simp [q]
      omega
    exact hwy (q₀.eq_of_length_eq_zero hq₀len).symm
  let c :G.Walk x x:=Walk.cons hxy q
  have hc:c.IsCycle:= (Walk.cons_isCycle_iff q hxy).2 ⟨hq,hedge⟩
  refine ⟨c,hc,?_⟩
  simp [c]
omit [DecidableEq V] [Fintype V] in
private theorem yM
    {z:V} {c:G.Walk z z} (hc:c.IsCycle)
    {x w t:V} (hx:x ∈ c.support) (hw:w ∈ c.support)
    (ht:t ∈ c.support) (hxw:x ≠ w) :
    ∃ r :G.Walk x w,
      r.IsPath ∧ t ∈ r.support ∧ (∀ v ∈ r.support,v ∈ c.support) :=by
  classical
  let c':G.Walk x x:=c.rotate x hx
  have hc':c'.IsCycle:=hc.rotate hx
  have hw':w ∈ c'.support:=by
    simpa [c'] using (c.mem_support_rotate_iff x hx).2 hw
  have ht':t ∈ c'.support:=by
    simpa [c'] using (c.mem_support_rotate_iff x hx).2 ht
  let r₁:G.Walk x w:=c'.takeUntil w hw'
  let d :G.Walk w x:=c'.dropUntil w hw'
  let r₂:G.Walk x w:=d.reverse
  have hr₁:r₁.IsPath:=hc'.isPath_takeUntil hw'
  have hr₂:r₂.IsPath:=by
    apply Walk.isPath_reverse_iff d |>.mpr
    have hcycleappend: (r₁.append d).IsCycle:=by
      simpa [r₁,d] using hc'
    exact Walk.IsCycle.isPath_of_append_right (Walk.not_nil_of_ne hxw) hcycleappend
  have hr₁_sub: ∀ v ∈ r₁.support,v ∈ c.support:=by
    intro v hv
    have hv':v ∈ c'.support:=c'.support_takeUntil_subset_support hw' hv
    exact (c.mem_support_rotate_iff x hx).1 (by simpa [c'] using hv')
  have hr₂_sub: ∀ v ∈ r₂.support,v ∈ c.support:=by
    intro v hv
    have hvd:v ∈ d.support:=by simpa [r₂] using hv
    have hv':v ∈ c'.support:=c'.support_dropUntil_subset_support hw' hvd
    exact (c.mem_support_rotate_iff x hx).1 (by simpa [c'] using hv')
  by_cases htr₁:t ∈ r₁.support
  · exact ⟨r₁,hr₁,htr₁,hr₁_sub⟩
  · refine ⟨r₂,hr₂,?_,hr₂_sub⟩
    have htappend:t ∈ (r₁.append d).support:=by
      simpa [r₁,d,Walk.take_spec c' hw'] using ht'
    rw [Walk.mem_support_append_iff] at htappend
    have htd:t ∈ d.support:=htappend.resolve_left htr₁
    simpa [r₂] using htd
omit [DecidableEq V] [Fintype V] in
private theorem vT
    {root x y:V} (hxy:G.Adj x y) (hcycle:rg G root x)
    (p:G.Walk y root) (hp:p.IsPath) (hpx:x ∉ p.support) :
    rg G root y :=by
  classical
  rcases hcycle with ⟨z,c,hc,hroot,hx⟩
  by_cases hyc:y ∈ c.support
  · exact ⟨z,c,hc,hroot,hyc⟩
  let Cset:Finset V :=c.support.toFinset
  have hmeet: {v ∈ Cset | v ∈ p.support}.Nonempty:=by
    refine ⟨root,?_⟩
    simp [Cset,hroot]
  obtain ⟨w,hwC,hwp,hfirst⟩ :=
    p.exists_mem_support_forall_mem_support_imp_eq Cset hmeet
  have hwc:w ∈ c.support:=by simpa [Cset] using hwC
  have hxw:x ≠ w:=by
    intro h
    exact hpx (h ▸ hwp)
  let q :G.Walk y w:=p.takeUntil w hwp
  have hq:q.IsPath:=hp.takeUntil hwp
  obtain ⟨r,hr,hrootr,hrsub⟩ :=
    yM hc hx hwc hroot hxw
  let body:G.Walk x y:=r.append q.reverse
  have hdisj:r.support.Disjoint q.reverse.support.tail:=by
    rw [List.disjoint_left]
    intro v hvr hvqtail
    have hvc:v ∈ c.support:=hrsub v hvr
    have hvq:v ∈ q.support:=by
      have:v ∈ q.reverse.support:=List.mem_of_mem_tail hvqtail
      simpa using this
    have hvw:v=w:=hfirst v (by simpa [Cset] using hvc) hvq
    subst v
    have hne:=hq.reverse.support_nodup.rel_head_tail hvqtail
    exact hne (by simp)
  have hbody:body.IsPath:=by
    simp only [Walk.isPath_def,body,Walk.support_append]
    exact List.Nodup.append hr.support_nodup hq.reverse.support_nodup.tail hdisj
  have hedge:s(y,x) ∉ body.edges:=by
    intro he
    simp only [body,Walk.edges_append,List.mem_append] at he
    rcases he with her | heq
    · have hyv:y ∈ r.support:=r.fst_mem_support_of_mem_edges her
      exact hyc (hrsub y hyv)
    · have hex:s(x,y) ∈ q.edges:=by
        simpa [Walk.edges_reverse,Sym2.eq_swap] using heq
      have hxp:x ∈ p.support:=by
        exact p.support_takeUntil_subset_support hwp
          (q.fst_mem_support_of_mem_edges hex)
      exact hpx hxp
  let d :G.Walk y y:=Walk.cons hxy.symm body
  have hd:d.IsCycle:= (Walk.cons_isCycle_iff body hxy.symm).2 ⟨hbody,hedge⟩
  refine ⟨y,d,hd,?_,?_⟩
  · have:root ∈ body.support:=by
      simp only [body,Walk.mem_support_append_iff]
      exact Or.inl hrootr
    simp only [d,Walk.support_cons,List.mem_cons]
    exact Or.inr this
  · simp [d]
omit [DecidableEq V] in
private theorem tV
    (hG:qh G) {root x y:V} (hrx:root ≠ x)
    (hxy:G.Adj x y) (hcycle:rg G root x) :
    rg G root y :=by
  classical
  obtain ⟨p,hp,hpx⟩ :=hG.sT x hxy.ne.symm hrx
  exact vT hxy hcycle p hp hpx
omit [DecidableEq V] in
private theorem ye
    (hG:qh G) {root x :V} :
    ∀ (l:List V),List.IsChain G.Adj (x::l) →
      root ∉ x::l → rg G root x →
      ∀ y ∈ x ::l,rg G root y :=by
  classical
  intro l
  induction l generalizing x with
  | nil=>
      intro _ _ hcycle y hy
      simp only [List.mem_singleton] at hy
      simpa [hy] using hcycle
  | cons v l ih=>
      intro hchain hroot hcycle y hy
      have hc:=List.isChain_cons_cons.mp hchain
      have hrel:G.Adj x v:=hc.1
      have htailchain:List.IsChain G.Adj (v::l) :=hc.2
      have hrootx:root ≠ x:=by
        intro h
        exact hroot (by simp [h])
      have hroottail:root ∉ v::l:=by
        intro h
        exact hroot (List.mem_cons_of_mem x h)
      have hnext:rg G root v :=
        tV hG hrootx hrel hcycle
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hcycle
      · exact ih htailchain hroottail hnext y (by simpa only [List.mem_cons] using hy)
omit [DecidableEq V] in
private theorem yI
    (hG:qh G) {root x y:V}
    (p:G.Walk x y) (_hp:p.IsPath) (hroot:root ∉ p.support)
    (hcycle:rg G root x) :
    rg G root y :=by
  classical
  exact ye hG p.support.tail
    (by rw [p.cons_tail_support];exact p.isChain_adj_support)
    (by rw [p.cons_tail_support];exact hroot) hcycle y
    (by rw [p.cons_tail_support];exact p.end_mem_support)
omit [DecidableEq V] in
theorem ar (hG:qh G) (x:V) :
    rg G x x :=by
  classical
  obtain ⟨t,htx⟩ :=hG.exists_ne x
  obtain ⟨p,hp⟩ :=hG.connected.exists_isPath x t
  have hp_nonNil: ¬ p.Nil:=Walk.not_nil_of_ne htx.symm
  have hxsnd:G.Adj x p.snd:=p.adj_snd hp_nonNil
  obtain ⟨c,hc,-⟩ :=hG.vX hxsnd
  exact ⟨x,c,hc,c.start_mem_support,c.start_mem_support⟩
omit [DecidableEq V] in
theorem dS (hG:qh G) (x y :V) :
    rg G x y :=by
  classical
  by_cases hxy:x=y
  · subst y
    exact hG.ar x
  obtain ⟨p,hp⟩ :=hG.connected.exists_isPath x y
  cases p with
  | nil=> exact (hxy rfl).elim
  | @cons x v y h p =>
      have hp':p.IsPath:=hp.of_cons
      have hxnot:x ∉ p.support:= (Walk.cons_isPath_iff h p).1 hp |>.2
      obtain ⟨c,hc,hv⟩ :=hG.vX h
      have hbase:rg G x v :=
        ⟨x,c,hc,c.start_mem_support,hv⟩
      exact yI hG p hp' hxnot hbase
private theorem tB
    {W:Type*} {H:SimpleGraph W} (r:W)
    (h: ∀ w:W,Nonempty (H.Walk w r)) : H.Connected:=by
  refine { preconnected:= ?_,nonempty:= ⟨r⟩}
  intro u v
  obtain ⟨p⟩ :=h u
  obtain ⟨q⟩ :=h v
  exact ⟨p.append q.reverse⟩
private theorem r0
    {W:Type*} {H:SimpleGraph W} (z r :W) (hr:r ≠ z)
    (h: ∀ w:W,w ≠ z →
      ∃ p :H.Walk w r,z ∉ p.support) :
    (H.induce ({z}ᶜ:Set W)).Connected:=by
  classical
  let r': ({z}ᶜ:Set W) := ⟨r,by simpa using hr⟩
  refine { preconnected:= ?_,nonempty:= ⟨r'⟩}
  intro u v
  have hu': (u:W) ∉ ({z} : Set W) :=u.2
  have hv': (v:W) ∉ ({z} : Set W) :=v.2
  have hu: (u:W) ≠ z:=fun huz ↦ hu' (by simpa using huz)
  have hv: (v:W) ≠ z:=fun hvz ↦ hv' (by simpa using hvz)
  obtain ⟨p,hp⟩ :=h u hu
  obtain ⟨q,hq⟩ :=h v hv
  let w :H.Walk u v:=p.append q.reverse
  have hw: ∀ x ∈ w.support,x ∈ ({z}ᶜ:Set W) :=by
    intro x hx
    rw [Walk.mem_support_append_iff] at hx
    simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
    rcases hx with hxp | hxq
    · exact fun hzx ↦ hp (hzx ▸ hxp)
    · have hxq':x ∈ q.support:=by simpa using hxq
      exact fun hzx ↦ hq (hzx ▸ hxq')
  let wi:=w.induce ({z}ᶜ:Set W) hw
  exact ⟨wi.copy (Subtype.ext rfl) (Subtype.ext rfl)⟩
omit [DecidableEq V] [Fintype V] in
private theorem wu (hG:G.Connected) (A B :Set V) (x y :V) :
    ∃ p : (qA G A B).Walk (Sum.inl x) (Sum.inl y),
      ∀ z ∈ p.support,z ∈ Set.range (Sum.inl:V → sg V) :=by
  classical
  obtain ⟨p⟩ :=hG x y
  let r :=p.map (qn G A B).toHom
  have hr: ∀ z ∈ r.support,
      z ∈ Set.range (Sum.inl:V → sg V) :=by
    intro z hz
    simp only [r,Walk.support_map,List.mem_map] at hz
    obtain ⟨w,-,rfl⟩ :=hz
    exact Set.mem_range_self w
  let hx: (qn G A B) x =Sum.inl x :=rfl
  let hy: (qn G A B) y =Sum.inl y :=rfl
  let r':=r.copy hx hy
  have hsupp:r'.support=r.support:=Walk.support_copy r hx hy
  refine ⟨r',?_⟩
  intro z hz
  exact hr z (hsupp ▸ hz)
omit [DecidableEq V] in
private theorem wr (hG:qh G)
    (A B :Set V) (z:V) {x y :V} (hx:x ≠ z) (hy:y ≠ z) :
    ∃ p : (qA G A B).Walk (Sum.inl x) (Sum.inl y),
      Sum.inl z ∉ p.support:=by
  classical
  obtain ⟨p,-,hpz⟩ :=hG.sT z hx hy
  refine ⟨p.map (qn G A B).toHom,?_⟩
  intro hz
  change (qn G A B) z ∈
    (p.map (qn G A B).toHom).support at hz
  rw [Walk.support_map,List.mem_map] at hz
  obtain ⟨w,hw,hwz⟩ :=hz
  exact hpz ((Sum.inl_injective hwz) ▸ hw)
omit [DecidableEq V] [Fintype V] in
private theorem tF (hG:G.Connected)
    {A B :Set V} (hA:A.Nonempty) (hB:B.Nonempty) :
    (qA G A B).Connected:=by
  classical
  obtain ⟨a,ha⟩ :=hA
  obtain ⟨b,hb⟩ :=hB
  apply tB (H:=qA G A B) (Sum.inl a)
  intro w
  cases w with
  | inl x =>
      obtain ⟨p,-⟩ :=wu hG A B x a
      exact ⟨p⟩
  | inr i =>
      cases i with
      | false=>
          exact ⟨Walk.cons (u2.mpr ha) Walk.nil⟩
      | true=>
          obtain ⟨p,-⟩ :=wu hG A B b a
          exact ⟨Walk.cons (sJ.mpr hb) p⟩
omit [DecidableEq V] in
private theorem xh (hG:qh G)
    {A B :Set V} (hA:2 ≤ A.ncard) (hB:2 ≤ B.ncard) (z:V) :
    ((qA G A B).induce
      ({Sum.inl z}ᶜ:Set (sg V))).Connected:=by
  classical
  obtain ⟨a,ha,haz⟩ :=A.exists_ne_of_one_lt_ncard (by omega) z
  obtain ⟨b,hb,hbz⟩ :=B.exists_ne_of_one_lt_ncard (by omega) z
  apply r0
    (H:=qA G A B) (Sum.inl z) (Sum.inl a) (by simpa)
  intro w hw
  cases w with
  | inl x =>
      have hxz:x ≠ z:=by
        intro hxz
        exact hw (by simp [hxz])
      exact wr hG A B z hxz haz
  | inr i =>
      cases i with
      | false=>
          refine ⟨Walk.cons (u2.mpr ha) Walk.nil,?_⟩
          simp [haz.symm]
      | true=>
          obtain ⟨p,hp⟩ :=wr hG A B z hbz haz
          refine ⟨Walk.cons (sJ.mpr hb) p,?_⟩
          simpa using hp
omit [DecidableEq V] [Fintype V] in
private theorem wV (hG:G.Connected)
    {A B :Set V} (hB:B.Nonempty) :
    ((qA G A B).induce
      ({Sum.inr false}ᶜ:Set (sg V))).Connected:=by
  classical
  obtain ⟨b,hb⟩ :=hB
  apply r0
    (H:=qA G A B) (Sum.inr false) (Sum.inl b) (by simp)
  intro w hw
  cases w with
  | inl x =>
      obtain ⟨p,hpold⟩ :=wu hG A B x b
      refine ⟨p,?_⟩
      intro h
      obtain ⟨y,hy⟩ :=hpold _ h
      cases hy
  | inr i =>
      cases i with
      | false=> exact (hw rfl).elim
      | true=>
          refine ⟨Walk.cons (sJ.mpr hb) Walk.nil,?_⟩
          simp
omit [DecidableEq V] [Fintype V] in
private theorem wI (hG:G.Connected)
    {A B :Set V} (hA:A.Nonempty) :
    ((qA G A B).induce
      ({Sum.inr true}ᶜ:Set (sg V))).Connected:=by
  classical
  obtain ⟨a,ha⟩ :=hA
  apply r0
    (H:=qA G A B) (Sum.inr true) (Sum.inl a) (by simp)
  intro w hw
  cases w with
  | inl x =>
      obtain ⟨p,hpold⟩ :=wu hG A B x a
      refine ⟨p,?_⟩
      intro h
      obtain ⟨y,hy⟩ :=hpold _ h
      cases hy
  | inr i =>
      cases i with
      | false=>
          refine ⟨Walk.cons (u2.mpr ha) Walk.nil,?_⟩
          simp
      | true=> exact (hw rfl).elim
omit [DecidableEq V] in
theorem yK (hG:qh G) {A B :Set V}
    (hA:2 ≤ A.ncard) (hB:2 ≤ B.ncard) :
    qh (qA G A B) :=by
  classical
  have hAne:A.Nonempty:= (Set.ncard_pos (Set.toFinite A)).mp (by omega)
  have hBne:B.Nonempty:= (Set.ncard_pos (Set.toFinite B)).mp (by omega)
  refine ⟨?_,tF hG.connected hAne hBne,?_⟩
  · have hcard:=hG.xV
    simp [sg]
    omega
  · intro z
    cases z with
    | inl x => exact xh hG hA hB x
    | inr i =>
        cases i with
        | false=> exact wV hG.connected hBne
        | true=> exact wI hG.connected hAne
private structure w5 (G:SimpleGraph V) (A B :Set V)
    (p: (qA G A B).Walk (Sum.inr false) (Sum.inr true)) where
  a:V
  b:V
  walk: (qA G A B).Walk (Sum.inl a) (Sum.inl b)
  isPath:walk.IsPath
  a_mem:a ∈ A
  b_mem:b ∈ B
  support_subset_tail:walk.support ⊆ p.support.tail
  old_support: ∀ x ∈ walk.support,
    x ∈ Set.range (Sum.inl:V → sg V)
omit [DecidableEq V] [Fintype V] in
private theorem ya {A B :Set V}
    (p: (qA G A B).Walk (Sum.inr false) (Sum.inr true))
    (hp:p.IsPath) : Nonempty (w5 G A B p) :=by
  classical
  have hp_nonNil: ¬p.Nil:=Walk.not_nil_of_ne (by simp)
  have htailPath:p.tail.IsPath:=hp.tail
  have htail_nonNil: ¬p.tail.Nil:=by
    intro hnil
    have hsnd:p.snd=Sum.inr true:=htailPath.nil_iff_eq.mp hnil
    have hadj:=p.adj_snd hp_nonNil
    rw [hsnd] at hadj
    simp [qA] at hadj
  have hpen:p.tail.penultimate=p.penultimate:=by
    have h :=Walk.penultimate_cons_of_not_nil
      (p.adj_snd hp_nonNil) p.tail htail_nonNil
    rw [p.cons_tail_eq hp_nonNil] at h
    exact h.symm
  have hleft:=p.adj_snd hp_nonNil
  have hright:=p.adj_penultimate hp_nonNil
  cases hs:p.snd with
  | inr i =>
    rw [hs] at hleft
    cases i <;> simp [qA] at hleft
  | inl a =>
    rw [hs] at hleft
    cases ht:p.penultimate with
    | inr i =>
      rw [ht] at hright
      cases i <;> simp [qA] at hright
    | inl b =>
      rw [ht] at hright
      have ha:a ∈ A:=by simpa using hleft
      have hb:b ∈ B:=by simpa using hright
      let m₀:=p.tail.dropLast
      have hm₀:m₀.IsPath:=hp.tail.dropLast
      have hmend:p.tail.penultimate=Sum.inl b :=hpen.trans ht
      let m : (qA G A B).Walk (Sum.inl a) (Sum.inl b) :=
        m₀.copy hs hmend
      have hmsub:m.support ⊆ p.support.tail:=by
        intro x hx
        have hx₀:x ∈ m₀.support:=by simpa [m] using hx
        have hxdrop:x ∈ p.tail.support.dropLast:=by
          simpa [m₀,Walk.support_dropLast htail_nonNil] using hx₀
        have hxtail:x ∈ p.tail.support:=List.mem_of_mem_dropLast hxdrop
        simpa [p.support_tail_of_not_nil hp_nonNil] using hxtail
      have halpha:Sum.inr false ∉ p.support.tail:=by
        have hn:=hp.support_nodup
        rw [← p.cons_tail_support] at hn
        exact (List.nodup_cons.mp hn).1
      have hbeta:Sum.inr true ∉ m.support:=by
        intro hx
        have hx₀:Sum.inr true ∈ m₀.support:=by simpa [m] using hx
        have hn:=hp.tail.support_nodup
        rw [← p.tail.support_dropLast_concat htail_nonNil] at hn
        exact hn.disjoint hx₀ (by simp)
      refine ⟨{
        a:=a
        b:=b
        walk:=m
        isPath:=by simpa [m] using hm₀
        a_mem:=ha
        b_mem:=hb
        support_subset_tail:=hmsub
        old_support:= ?_}⟩
      intro x hx
      cases x with
      | inl v => exact ⟨v,rfl⟩
      | inr i =>
          cases i with
          | false=> exact (halpha (hmsub hx)).elim
          | true=> exact (hbeta hx).elim
omit [DecidableEq V] [Fintype V] in
private theorem ad {A B :Set V} {a b :V}
    (p: (qA G A B).Walk (Sum.inl a) (Sum.inl b))
    (hold: ∀ x ∈ p.support,
      x ∈ Set.range (Sum.inl:V → sg V)) :
    ∃ q :G.Walk a b,q.map (qn G A B).toHom=p:=by
  classical
  let e :=qn G A B
  have hold': ∀ x ∈ p.support,x ∈ Set.range e :=by
    intro x hx
    obtain ⟨v,hv⟩ :=hold x hx
    refine ⟨v,?_⟩
    change Sum.inl v =x
    exact hv
  let p':=p.induce (Set.range e) hold'
  let q₀:=p'.map e.isoInduceRange.symm.toHom
  have hqa:e.isoInduceRange.symm
      ⟨Sum.inl a,Set.mem_range_self a⟩ = a:=by
    exact e.isoInduceRange.symm_apply_apply a
  have hqb:e.isoInduceRange.symm
      ⟨Sum.inl b,Set.mem_range_self b⟩ = b:=by
    exact e.isoInduceRange.symm_apply_apply b
  let q :G.Walk a b:=q₀.copy hqa hqb
  refine ⟨q,?_⟩
  apply Walk.ext_support
  calc
    (q.map (qn G A B).toHom).support=
        (q₀.map e.toHom).support:=by
      simp [q,e]
    _=p.support:=by
      simp only [q₀,Walk.support_map,List.map_map]
      change List.map (fun x :Set.range e => e (e.isoInduceRange.symm x))
          p'.support=p.support
      have hfun: (fun x :Set.range e => e (e.isoInduceRange.symm x)) =
          (fun x :Set.range e => (x:sg V)) :=by
        funext x
        exact congrArg Subtype.val (e.isoInduceRange.apply_symm_apply x)
      rw [hfun]
      change ((p.induce (Set.range e) hold').support.map Subtype.val) = p.support
      rw [Walk.support_induce]
      exact List.attachWith_map_subtype_val hold'
omit [DecidableEq V] [Fintype V] in
private theorem w5.tw {A B :Set V}
    {p: (qA G A B).Walk (Sum.inr false) (Sum.inr true)}
    (S:w5 G A B p) :
    ∃ q :G.Walk S.a S.b,
      q.IsPath ∧ q.map (qn G A B).toHom=S.walk:=by
  classical
  obtain ⟨q,hq⟩ :=ad S.walk S.old_support
  refine ⟨q,?_,hq⟩
  have hmapped: (q.map (qn G A B).toHom).IsPath:=by
    rw [Walk.isPath_def,hq]
    exact S.isPath.support_nodup
  exact (Walk.isPath_map_iff_of_injective
    (f:= (qn G A B).toHom)
    (qn G A B).injective).mp hmapped
omit [DecidableEq V] in
theorem yF (hG:qh G) {A B :Set V}
    (hA:2 ≤ A.ncard) (hB:2 ≤ B.ncard) :
    Nonempty (x7 G A B) :=by
  classical
  let H :=qA G A B
  have hH:qh H :=hG.yK hA hB
  obtain ⟨z,c,hc,hleft,hright⟩ :=
    hH.dS (Sum.inr false) (Sum.inr true)
  obtain ⟨p,q,hp,hq,-,-,-,hmeet,-,-,-⟩ :=
    yg hc hleft hright (by simp)
  obtain ⟨P⟩ :=ya p hp
  obtain ⟨Q⟩ :=ya q hq
  obtain ⟨pG,hpG,hpmap⟩ :=P.tw
  obtain ⟨qG,hqG,hqmap⟩ :=Q.tw
  have hdisj:pG.support.Disjoint qG.support:=by
    rw [List.disjoint_left]
    intro x hxp hxq
    have hxp':Sum.inl x ∈ P.walk.support:=by
      have hxpmap: (qn G A B) x ∈
          (pG.map (qn G A B).toHom).support:=by
        rw [Walk.support_map]
        exact List.mem_map.mpr ⟨x,hxp,rfl⟩
      rw [hpmap] at hxpmap
      exact hxpmap
    have hxq':Sum.inl x ∈ Q.walk.support:=by
      have hxqmap: (qn G A B) x ∈
          (qG.map (qn G A B).toHom).support:=by
        rw [Walk.support_map]
        exact List.mem_map.mpr ⟨x,hxq,rfl⟩
      rw [hqmap] at hxqmap
      exact hxqmap
    have hxpArc:Sum.inl x ∈ p.support:=
      List.mem_of_mem_tail (P.support_subset_tail hxp')
    have hxqArc:Sum.inl x ∈ q.support:=
      List.mem_of_mem_tail (Q.support_subset_tail hxq')
    rcases hmeet (Sum.inl x) hxpArc hxqArc with h | h <;> simp at h
  exact ⟨{
    a₁:=P.a
    a₂:=Q.a
    b₁:=P.b
    b₂:=Q.b
    p:=pG
    q:=qG
    p_isPath:=hpG
    q_isPath:=hqG
    a₁_mem:=P.a_mem
    a₂_mem:=Q.a_mem
    b₁_mem:=P.b_mem
    b₂_mem:=Q.b_mem
    disjoint_support:=hdisj}⟩
end qh
end Erdos556
end cL
section ch
namespace Erdos556
open SimpleGraph
private theorem y4 (A B C:Prop) :
    ((A ↔ B) ↔ (B ↔ C)) ↔ (A ↔ C) :=by
  tauto
theorem xt {V:Type*} {G:SimpleGraph V}
    (S:Set V) (colour:S → Bool) {u v :S}
    (p:G.Walk u.val v.val) (hp:p.IsPath)
    (hwrong: ¬ (Even p.length ↔ (colour u ↔ colour v))) :
    ∃ a b:S,a.val ≠ b.val ∧ ∃ q :G.Walk a.val b.val,q.IsPath ∧
      ¬ (Even q.length ↔ (colour a ↔ colour b)) ∧ q.length ≤ p.length ∧
      ∀ z ∈ q.support,z ≠ a.val → z ≠ b.val → z ∉ S:=by
  classical
  let P (m:ℕ) : Prop:= ∃ a b :S,∃ q:G.Walk a.val b.val,
    q.IsPath ∧ ¬ (Even q.length ↔ (colour a ↔ colour b)) ∧ q.length=m
  have hex: ∃ m,P m:= ⟨p.length,u,v,p,hp,hwrong,rfl⟩
  obtain ⟨a,b,q,hq,hqw,hlen⟩ :=Nat.find_spec hex
  have hmin {x y :S} (r:G.Walk x.val y.val) (hr:r.IsPath)
      (hw: ¬ (Even r.length ↔ (colour x ↔ colour y))) : q.length ≤ r.length:=by
    rw [hlen]
    exact Nat.find_min' hex ⟨x,y,r,hr,hw,rfl⟩
  have hcons {x y :S} (r:G.Walk x.val y.val) (hr:r.IsPath)
      (hlt:r.length < q.length) : Even r.length ↔ (colour x ↔ colour y) :=by
    by_contra hw
    exact (Nat.not_le_of_gt hlt) (hmin (x:=x) (y:=y) r hr hw)
  have hab:a.val ≠ b.val:=by
    intro h
    have heq:a=b:=Subtype.ext h
    subst b
    have hz:= (Walk.isPath_iff_nil.mp hq).length_eq_zero
    exact hqw (by simp [hz])
  refine ⟨a,b,hab,q,hq,hqw,hmin (x:=u) (y:=v) p hp hwrong,?_⟩
  intro z hz hza hzb hzS
  let x :S:= ⟨z,hzS⟩
  let r :G.Walk a.val x.val:=q.takeUntil z hz
  let s :G.Walk x.val b.val:=q.dropUntil z hz
  have hr:=hcons (x:=a) (y:=x) r (hq.takeUntil hz) (q.length_takeUntil_lt_length hz hzb)
  have hs:=hcons (x:=x) (y:=b) s (hq.dropUntil hz) (q.length_dropUntil_lt_length hz hza)
  have hsum:q.length=r.length+s.length:=by
    have h :=congrArg Walk.length (q.take_spec hz)
    simpa only [Walk.length_append] using h.symm
  apply hqw
  rw [hsum,Nat.even_add,hr,hs]
  exact y4 _ _ _
theorem xC {V:Type*} {G:SimpleGraph V}
    (S:Set V) (colour: (G.induce S).Coloring Bool) {u v :S}
    (p: (G.induce S).Walk u v) (hp:p.IsPath) (hlen:1 < p.length)
    (q:G.Walk u.val v.val) (hq:q.IsPath)
    (hqS: ∀ z ∈ q.support,z ≠ u.val → z ≠ v.val → z ∉ S)
    (hwrong: ¬ (Even q.length ↔ (colour u ↔ colour v))) :
    ∃ c :G.Walk u.val u.val,c.IsCycle ∧ Odd c.length ∧ p.length ≤ c.length:=by
  let f :G.induce S ↪g G :=
    { toFun:=Subtype.val,inj':=Subtype.val_injective,map_rel_iff':=Iff.rfl}
  have hpS (z:V) (hz:z ∈ (p.map f.toHom).support) : z ∈ S:=by
    rw [Walk.support_map,List.mem_map] at hz
    obtain ⟨x,_,hx⟩ :=hz
    subst z
    exact x.property
  have hcycle: ((p.map f.toHom).append q.reverse).IsCycle:=by
    apply qy (p.map f.toHom) q
      (hp.map f.injective) hq (by simpa only [Walk.length_map] using hlen)
    intro z hzp hzq
    by_cases hzu:z=u.val
    · exact Or.inl hzu
    by_cases hzv:z=v.val
    · exact Or.inr hzv
    exact (hqS z hzq hzu hzv (hpS z hzp)).elim
  have hpar:p.length%2 ≠ q.length%2:=by
    intro h
    apply hwrong
    have heq:Even q.length ↔ Even p.length:=by
      simp only [Nat.even_iff]
      omega
    exact heq.trans (colour.even_length_iff_congr p)
  refine ⟨(p.map f.toHom).append q.reverse,hcycle,?_,?_⟩
  · apply Nat.odd_iff.mpr
    change ((p.map f.toHom).append q.reverse).length%2=1
    simp only [Walk.length_append,Walk.length_map,Walk.length_reverse]
    omega
  · change p.length ≤ ((p.map f.toHom).append q.reverse).length
    simp only [Walk.length_append,Walk.length_map,Walk.length_reverse]
    omega
end Erdos556
end ch
section de
namespace Erdos556
open SimpleGraph
theorem ve {V:Type*} [Fintype V]
    {G:SimpleGraph V} (hG:qh G) (hnonbip: ¬ G.Colorable 2)
    (S:Set V) (hS:2 ≤ S.ncard) (colour:S → Bool) :
    ∃ a b:S,∃ p:G.Walk a.val b.val,p.IsPath ∧
      ¬ (Even p.length ↔ (colour a ↔ colour b)) :=by
  classical
  obtain ⟨w,c,hc,ho⟩ : ∃ (w:V) (c:G.Walk w w),c.IsCycle ∧ Odd c.length:=by
    by_contra h
    apply hnonbip
    apply (xJ G).mpr
    intro w c hc ho
    exact h ⟨w,c,hc,ho⟩
  let C :Set V := {z | z ∈ c.support}
  have hC:C.Nontrivial:=by
    refine ⟨w,c.start_mem_support,c.snd,?_,(c.adj_snd hc.not_nil).ne⟩
    exact List.mem_of_mem_tail (Walk.snd_mem_tail_support hc.not_nil)
  have hCcard:2 ≤ C.ncard:=Set.one_lt_ncard_iff_nontrivial.mpr hC
  obtain ⟨P⟩ :=hG.yF hS hCcard
  obtain ⟨x,hxC,p,hp,_,hpsub,hpC⟩ :=
    rq P.p P.p_isPath C P.b₁_mem
  obtain ⟨y,hyC,q,hq,_,hqsub,hqC⟩ :=
    rq P.q P.q_isPath C P.b₂_mem
  have hpq (z:V) (hzp:z ∈ p.support) (hzq:z ∈ q.support) : False:=
    P.disjoint_support (hpsub hzp) (hqsub hzq)
  have hxy:x ≠ y:=by
    intro h
    exact hpq x p.end_mem_support (h ▸ q.end_mem_support)
  obtain ⟨r,s,hr,hs,hpar,_,_,_,_⟩ :=
    rE c hc ho p q hp hq hxC hyC hxy hpC hqC hpq
  let a :S:= ⟨P.a₁,P.a₁_mem⟩
  let b :S:= ⟨P.a₂,P.a₂_mem⟩
  by_cases h :Even r.length ↔ (colour a ↔ colour b)
  · refine ⟨a,b,s,hs,?_⟩
    intro h'
    have he:=h.trans h'.symm
    simp only [Nat.even_iff] at he
    apply hpar
    omega
  · exact ⟨a,b,r,hr,h⟩
theorem vu {V:Type*} [Fintype V]
    {G:SimpleGraph V} (hG:qh G) (hnonbip: ¬ G.Colorable 2)
    (S:Set V) (hS:2 ≤ S.ncard) (colour:S → Bool) :
    ∃ a b:S,a.val ≠ b.val ∧ ∃ p :G.Walk a.val b.val,p.IsPath ∧
      ¬ (Even p.length ↔ (colour a ↔ colour b)) ∧
      ∀ z ∈ p.support,z ≠ a.val → z ≠ b.val → z ∉ S:=by
  classical
  obtain ⟨u,v,p,hp,hw⟩ :=ve hG hnonbip S hS colour
  obtain ⟨a,b,hab,q,hq,hqw,_,hav⟩ :=
    xt S colour (u:=u) (v:=v) p hp hw
  exact ⟨a,b,hab,q,hq,hqw,hav⟩
end Erdos556
end de
section cQ
namespace Erdos556
open SimpleGraph Finset
theorem ub {V:Type*} [DecidableEq V]
    {G:SimpleGraph V} (L:ℕ) (R:Finset V)
    (hres: ∀ x y S,S.card ≤ L+1 → qY G L x y (R \ S))
    (u v :V) (huv:u ≠ v) {a b :V} (p:G.Walk a b) (hp:p.IsPath)
    (hlen:0 < p.length) (hav: ∀ x ∈ p.support,x ∉ R ∧ x ≠ u ∧ x ≠ v) :
    ∃ q :G.Walk u v,q.IsPath ∧ p.length ≤ q.length ∧ q.length ≤ p.length+2*L:=by
  classical
  have hab:a ≠ b:=by
    intro h
    have hz:= ((hp.nil_iff_eq).mpr h).length_eq_zero
    omega
  have hau:a ≠ u:= (hav a p.start_mem_support).2.1
  have hav':a ≠ v:= (hav a p.start_mem_support).2.2
  have hbu:b ≠ u:= (hav b p.end_mem_support).2.1
  obtain ⟨r,hr,hrlen,hrR⟩ :=hres u a {v} (by simp)
  have hrv:v ∉ r.support:=by
    intro hv
    have h :=hrR v hv huv.symm hav'.symm
    exact (mem_sdiff.mp h).2 (mem_singleton_self v)
  have hrP (z:V) (hzr:z ∈ r.support) (hzp:z ∈ p.support) : z=a:=by
    by_contra hza
    have hzu:= (hav z hzp).2.1
    exact (hav z hzp).1 (mem_sdiff.mp (hrR z hzr hzu hza)).1
  have hrb:b ∉ r.support:=by
    intro h
    exact hab (hrP b h p.end_mem_support).symm
  have hcard:r.support.toFinset.card ≤ L+1:=by
    have h :=List.toFinset_card_le r.support
    rw [r.length_support] at h
    omega
  obtain ⟨s,hs,hslen,hsR⟩ :=hres v b r.support.toFinset hcard
  have hrs (z:V) (hzr:z ∈ r.support) (hzs:z ∈ s.support) : False:=by
    have hzv:z ≠ v:=fun h => hrv (h ▸ hzr)
    have hzb:z ≠ b:=fun h => hrb (h ▸ hzr)
    exact (mem_sdiff.mp (hsR z hzs hzv hzb)).2 (List.mem_toFinset.mpr hzr)
  have hsP (z:V) (hzp:z ∈ p.support) (hzs:z ∈ s.support) : z=b:=by
    by_contra hzb
    have hzv:= (hav z hzp).2.2
    exact (hav z hzp).1 (mem_sdiff.mp (hsR z hzs hzv hzb)).1
  have hrp: (r.append p).IsPath:=qr r p hr hp hrP
  have hq: ((r.append p).append s.reverse).IsPath:=by
    apply qr (r.append p) s.reverse hrp hs.reverse
    intro z hz hzsr
    have hzs:z ∈ s.support:=by
      simpa only [Walk.support_reverse,List.mem_reverse] using hzsr
    rcases (Walk.mem_support_append_iff _ _).mp hz with hzr | hzp
    · exact (hrs z hzr hzs).elim
    · exact hsP z hzp hzs
  refine ⟨(r.append p).append s.reverse,hq,?_,?_⟩ <;>
    simp only [Walk.length_append,Walk.length_reverse] <;> omega
end Erdos556
end cQ
section cK
namespace Erdos556
open SimpleGraph Filter
theorem sh (D B a:ℕ) (hD:0 < D) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (b d :ℕ),
      N₀ ≤ Fintype.card V → q8 G b →
      (∀ w,d+b ≤ G.degree w) → Fintype.card V ≤ D *d →
      Fintype.card V ≤ B *b →
      ∃ R :Finset V,(R.card:ℝ) ≤ 2*q*Fintype.card V ∧
        ∀ u v S,S.card ≤ a → qY G (3*D) u v (R \ S) :=by
  let L :=3*D
  let K :=B* ((a+1) * L)
  have hL:0 < L:=by dsimp [L];omega
  have hK:0 < K:=Nat.mul_pos hB (Nat.mul_pos (by omega) hL)
  obtain ⟨N₁,hN₁⟩ :=eventually_atTop.mp (uW q hq0 hq1 L K a hK)
  refine ⟨max N₁ 1,?_⟩
  intro V _ _ G _ b d hN hc hg hd hb
  have hV:0 < Fintype.card V :=by omega
  have hdpos:0 < d:=by nlinarith
  let m :=Fintype.card V /K
  have hbudget: ((a+1) * m) * L ≤ b:=by
    have hmul:B* (((a+1) * m) * L) ≤ B*b:=by
      calc
        B* (((a+1) * m) * L) = m*K:=by dsimp [K];ring
        _ ≤ Fintype.card V :=Nat.div_mul_le_self _ _
        _ ≤ B*b:=hb
    nlinarith
  have hdiam:3*Fintype.card V ≤ d *L:=by dsimp [L];nlinarith
  exact zM G b d L m a hc hdpos hg hdiam hbudget q hq0 hq1
    (hN₁ _ (by omega)) hV
end Erdos556
end cK
section cS
namespace Erdos556
open SimpleGraph Finset
theorem vA {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (L k :ℕ) (R:Finset V)
    (hres: ∀ x y S,S.card ≤ L+1 → qY G L x y (R \ S))
    (he: (k+R.card+2) * Fintype.card V < G.edgeFinset.card)
    (u v :V) (huv:u ≠ v) :
    ∃ p :G.Walk u v,p.IsPath ∧ 2*k < p.length:=by
  classical
  let S :=insert u (insert v R)
  let U := (S:Set V)ᶜ
  let H :=G.induce U
  have hS:S.card ≤ R.card+2:=by
    have h1:=card_insert_le u (insert v R)
    have h2:=card_insert_le v R
    dsimp [S]
    omega
  have hdeleted:=rc G S
  change G.edgeFinset.card ≤ H.edgeFinset.card+S.card*Fintype.card V at hdeleted
  have hmul:=Nat.mul_le_mul_right (Fintype.card V) hS
  have hH:k*Fintype.card V < H.edgeFinset.card:=by nlinarith
  have hcard:=Fintype.card_le_of_injective (fun x :U=> x.val) Subtype.val_injective
  have hH': (2*k) * Fintype.card U < 2 *H.edgeFinset.card:=by
    have hmul':=Nat.mul_le_mul_left k hcard
    nlinarith
  obtain ⟨a,b,p,hp,hlen⟩ :=z6 H (2*k) hH'
  let f :H ↪g G :=SimpleGraph.Embedding.induce U
  have hav (x:V) (hx:x ∈ (p.map f.toHom).support) : x ∉ R ∧ x ≠ u ∧ x ≠ v:=by
    rw [Walk.support_map,List.mem_map] at hx
    obtain ⟨y,_,hy⟩ :=hx
    subst x
    have h :=y.property
    change y.val ∉ insert u (insert v R) at h
    simp only [mem_insert,not_or] at h
    exact ⟨h.2.2,h.1,h.2.1⟩
  have hpos:0 < (p.map f.toHom).length:=by
    simpa only [Walk.length_map] using (Nat.lt_of_le_of_lt (Nat.zero_le _) hlen)
  obtain ⟨q,hq,hge,_⟩ :=ub L R hres u v huv
    (p.map f.toHom) (hp.map f.injective) hpos hav
  simp only [Walk.length_map] at hge
  exact ⟨q,hq,hlen.trans_le hge⟩
theorem w1 (D B :ℕ) (hD:0 < D) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (b d k:ℕ),
      N₀ ≤ Fintype.card V → q8 G b →
      (∀ w,d+b ≤ G.degree w) → Fintype.card V ≤ D *d → Fintype.card V ≤ B *b →
      (k:ℝ) * Fintype.card V +2*q* (Fintype.card V :ℝ) ^ 2+
        2*Fintype.card V < (G.edgeFinset.card:ℝ) →
      ∀ u v,u ≠ v → ∃ p:G.Walk u v,p.IsPath ∧ 2*k < p.length:=by
  obtain ⟨N₀,hN₀⟩ :=sh D B (3*D+1) hD hB q hq0 hq1
  refine ⟨N₀,?_⟩
  intro V _ _ G _ b d k hN hc hg hd hb he u v huv
  obtain ⟨R,hR,hres⟩ :=hN₀ G b d hN hc hg hd hb
  have hmul:=mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg (Fintype.card V) :
    (0:ℝ) ≤ Fintype.card V)
  have heR: ((k:ℝ) + R.card+2) * Fintype.card V < (G.edgeFinset.card:ℝ) :=by
    nlinarith
  have heN: (k+R.card+2) * Fintype.card V < G.edgeFinset.card:=by exact_mod_cast heR
  exact vA G (3*D) k R hres heN u v huv
end Erdos556
end cS
section cJ
namespace Erdos556
open SimpleGraph
theorem xl {V:Type*} [Fintype V]
    {G:SimpleGraph V} (hG:qh G) (hnonbip: ¬ G.Colorable 2)
    (S:Set V) (hS:2 ≤ S.ncard) (colour: (G.induce S).Coloring Bool)
    (k:ℕ) (hk:1 ≤ k)
    (hlong: ∀ u v:S,u ≠ v → ∃ p: (G.induce S).Walk u v,
      p.IsPath ∧ 2*k < p.length) :
    ∃ (w:V) (c:G.Walk w w),c.IsCycle ∧ Odd c.length ∧ 2*k < c.length:=by
  classical
  obtain ⟨u,v,huv,q,hq,hwrong,hqS⟩ :=
    vu hG hnonbip S hS colour
  obtain ⟨p,hp,hlen⟩ :=hlong u v (fun h => huv (congrArg Subtype.val h))
  obtain ⟨c,hc,ho,hge⟩ :=xC S colour p hp (by omega)
    q hq hqS hwrong
  exact ⟨u.val,c,hc,ho,hlen.trans_le hge⟩
theorem ux (D B :ℕ) (hD:0 < D) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (b d k:ℕ),
      qh G → ¬ G.Colorable 2 → 2 ≤ S.card →
      N₀ ≤ Fintype.card (S:Set V) → q8 (G.induce (S:Set V)) b →
      (∀ w : (S:Set V),d+b ≤ (G.induce (S:Set V)).degree w) →
      Fintype.card (S:Set V) ≤ D*d → Fintype.card (S:Set V) ≤ B*b → 1 ≤ k →
      (G.induce (S:Set V)).Colorable 2 →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      ((G.induce (S:Set V)).edgeFinset.card:ℝ) ≤
        (k:ℝ) * Fintype.card (S:Set V) + 2*q* (Fintype.card (S:Set V) : ℝ) ^ 2+
          2*Fintype.card (S:Set V) :=by
  obtain ⟨N₀,hN₀⟩ :=w1 D B hD hB q hq0 hq1
  refine ⟨N₀,?_⟩
  intro V _ _ G _ S b d k hG hnb hS hN hc hg hd hb hk hcol ho
  by_contra he
  have hdensity:=lt_of_not_ge he
  have hlong:=hN₀ (G.induce (S:Set V)) b d k hN hc hg hd hb hdensity
  obtain ⟨colour⟩ :=hcol
  let col: (G.induce (S:Set V)).Coloring Bool:=
    SimpleGraph.recolorOfEquiv _ finTwoEquiv colour
  have hScard:2 ≤ (S:Set V).ncard:=by simpa only [Set.ncard_coe_finset] using hS
  obtain ⟨w,c,hcyc,hodd,hlen⟩ :=xl
    hG hnb (S:Set V) hScard col k hk hlong
  exact (Nat.not_le_of_gt hlen) (ho w c hcyc hodd)
end Erdos556
end cJ
section d3
namespace Erdos556
open SimpleGraph Finset
noncomputable def bB {V:Type*} [DecidableEq V] (G:SimpleGraph V)
    (S:Finset V) (T:Finset ↥((S:Set V)ᶜ)) :
    (G.induce (S:Set V)ᶜ).induce (T:Set ↥((S:Set V)ᶜ))ᶜ ≃g
      G.induce (↑(S ∪ T.map (Function.Embedding.subtype (fun v => v ∈ (S:Set V)ᶜ)) :
        Finset V) : Set V)ᶜ:=by
  let U := (S:Set V)ᶜ
  let F :=S ∪ T.map (Function.Embedding.subtype (fun v => v ∈ U))
  let f : ↥((T:Set U)ᶜ) → ↥((F:Set V)ᶜ) :=fun x => ⟨x.val.val,by
    intro hx
    rcases mem_union.mp hx with hxS | hxT
    · exact x.val.property hxS
    · obtain ⟨y,hyT,hyx⟩ :=mem_map.mp hxT
      have heq:y=x.val:=Subtype.ext hyx
      exact x.property (heq ▸ hyT)⟩
  have hinj:Function.Injective f :=by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    change (f x).val= (f y).val
    exact congrArg Subtype.val h
  have hsurj:Function.Surjective f :=by
    intro y
    have hyS:y.val ∉ S:=fun h => y.property (mem_union_left _ h)
    let x :U:= ⟨y.val,hyS⟩
    have hxT:x ∉ T:=by
      intro h
      exact y.property (mem_union_right S (mem_map.mpr ⟨x,h,rfl⟩))
    exact ⟨⟨x,hxT⟩,rfl⟩
  exact { toEquiv:=Equiv.ofBijective f ⟨hinj,hsurj⟩,map_rel_iff':=Iff.rfl}
theorem q8.e6 {V:Type*}
    {G:SimpleGraph V} {b s :ℕ} (hG:q8 G (b+s))
    (S:Finset V) (hS:S.card ≤ s) :
    q8 (G.induce (S:Set V)ᶜ) b :=by
  classical
  intro T hT
  let F :=S ∪ T.map (Function.Embedding.subtype (fun v => v ∈ (S:Set V)ᶜ))
  have hF:F.card ≤ b+s:=by
    have h :=card_union_le S (T.map (Function.Embedding.subtype (fun v => v ∈ (S:Set V)ᶜ)))
    rw [card_map] at h
    dsimp [F]
    omega
  exact (bB G S T).preconnected_iff.mpr (hG F hF)
end Erdos556
end d3
section cf
namespace Erdos556
open SimpleGraph Finset
noncomputable def cZ {V W :Type*} [DecidableEq V] [DecidableEq W]
    {G:SimpleGraph V} {H:SimpleGraph W} (e:G ≃g H) (S:Finset V) :
    G.induce (S:Set V)ᶜ ≃g H.induce (S.map e.toEquiv.toEmbedding:Set W)ᶜ where
  toEquiv:=
    { toFun:=fun x => ⟨e x.val,by
        intro hx
        obtain ⟨y,hy,hyx⟩ :=mem_map.mp hx
        exact x.property (e.injective hyx ▸ hy)⟩
      invFun:=fun y => ⟨e.symm y.val,by
        intro hy
        exact y.property (mem_map.mpr ⟨e.symm y.val,hy,e.apply_symm_apply y.val⟩)⟩
      left_inv:=fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv:=fun y => Subtype.ext (e.apply_symm_apply y.val)}
  map_rel_iff':=by intro x y;exact e.map_adj_iff
theorem q8.iso {V W :Type*}
    {G:SimpleGraph V} {H:SimpleGraph W} {b:ℕ}
    (hG:q8 G b) (e:G ≃g H) : q8 H b:=by
  classical
  intro S hS
  have h :=hG (S.map e.symm.toEquiv.toEmbedding) (by simpa only [card_map] using hS)
  exact (cZ e.symm S).preconnected_iff.mpr h
end Erdos556
end cf
section df
namespace Erdos556
open SimpleGraph Finset
def x8 {V:Type*} (G:SimpleGraph V) (S T :Set V) (h:S=T) :
    G.induce S ≃g G.induce T :=by
  subst T
  exact SimpleGraph.Iso.refl
def xX {V:Type*} [DecidableEq V] (S:Finset V) (T:Finset S) : Finset V :=
  Tᶜ.map (Function.Embedding.subtype (fun v => v ∈ S))
theorem ak {V:Type*} [DecidableEq V] (S:Finset V) (T:Finset S) :
    (xX S T).card=S.card-T.card:=by
  simp only [xX,card_map,card_compl,Fintype.card_coe]
noncomputable def tk {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (S:Finset V) (T:Finset S) :
    (G.induce (S:Set V)).induce (T:Set S)ᶜ ≃g
      G.induce (xX S T:Set V) :=
  (x8 (G.induce (S:Set V)) (T:Set S)ᶜ
    (↑(Tᶜ:Finset S) : Set S) (Finset.coe_compl T).symm).trans
      (sy G S Tᶜ)
end Erdos556
end df
section cs
namespace Erdos556
open SimpleGraph Finset
theorem wW (D B :ℕ) (hD:0 < D) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (b d k:ℕ),
      qh G → ¬ G.Colorable 2 → N₀+ (b+3*D+3) + 2 ≤ S.card →
      q8 (G.induce (S:Set V)) (2* (b+3*D+3)) →
      (∀ w :S,d+2* (b+3*D+3) ≤ (G.induce (S:Set V)).degree w) →
      S.card ≤ D*d → S.card ≤ B*b → 1 ≤ k →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      ((G.induce (S:Set V)).edgeFinset.card:ℝ) ≤
        (k:ℝ) * S.card+2*q* (S.card:ℝ) ^ 2+ (b+3*D+5:ℕ) * (S.card:ℝ) :=by
  obtain ⟨N₁,hN₁⟩ :=ua D B hB q hq0 hq1
  obtain ⟨N₂,hN₂⟩ :=ux D B hD hB q hq0 hq1
  refine ⟨max N₁ N₂,?_⟩
  intro V _ _ G _ S b d k hG hnb hN hc hg hd hb hk ho
  classical
  let J :=G.induce (S:Set V)
  let t :=b+3*D+3
  have hScard:Fintype.card (S:Set V) = S.card:=by
    calc
      Fintype.card (S:Set V) = (S:Set V).ncard:=Nat.card_eq_fintype_card.symm
      _=S.card:=Set.ncard_coe_finset S
  have hoJ (w: (S:Set V)) (c:J.Walk w w) (hcyc:c.IsCycle) (hodd:Odd c.length) :
      c.length ≤ 2*k:=by
    let f :J ↪g G :=SimpleGraph.Embedding.induce (S:Set V)
    have h :=ho (f w) (c.map f.toHom) (hcyc.map f.injective)
      (by simpa only [Walk.length_map] using hodd)
    simpa only [Walk.length_map] using h
  by_cases hrobust:qT J t
  · have hg' (w: (S:Set V)) : d+ (b+3*D+3) ≤ J.degree w :=by
      have h :=hg w
      change d +2* (b+3*D+3) ≤ J.degree w at h
      omega
    have hcore:=hN₁ J b d k (by rw [hScard];omega) (hc.mono (by omega))
      hrobust hg' (by simpa only [hScard] using hd) (by simpa only [hScard] using hb) hk hoJ
    rw [hScard] at hcore
    have hnonneg: (0:ℝ) ≤ (b+3*D+5:ℕ) * (S.card:ℝ) :=by positivity
    exact hcore.trans (le_add_of_nonneg_right hnonneg)
  · obtain ⟨T,hT,hcol⟩ : ∃ T :Finset (S:Set V),T.card ≤ t ∧
        (J.induce (T:Set (S:Set V))ᶜ).Colorable 2 :=by
      simpa only [qT,not_forall,not_not,exists_prop] using hrobust
    let K :=xX S T
    let H :=J.induce (T:Set (S:Set V))ᶜ
    let e :H ≃g G.induce (K:Set V) :=tk G S T
    have hK:K.card=S.card-T.card:=ak S T
    have hKle:K.card ≤ S.card:=by omega
    have hKcard:Fintype.card (K:Set V) = K.card:=by
      calc
        Fintype.card (K:Set V) = (K:Set V).ncard:=Nat.card_eq_fintype_card.symm
        _=K.card:=Set.ncard_coe_finset K
    have hHC:q8 H b:=
      (hc.mono (show b +t ≤ 2* (b+3*D+3) by dsimp [t];omega)).e6 T hT
    have hHD (w: ↥((T:Set (S:Set V))ᶜ)) : d+b ≤ H.degree w :=by
      have h :=qW J T w
      have hdeg:=hg w.val
      change d +2* (b+3*D+3) ≤ J.degree w.val at hdeg
      change J.degree w.val ≤ H.degree w +T.card at h
      dsimp [t] at hT
      omega
    have hKD (v: (K:Set V)) : d+b ≤ (G.induce (K:Set V)).degree v :=by
      calc
        d+b ≤ H.degree (e.symm v) :=hHD _
        _= (G.induce (K:Set V)).degree v :=by rw [← e.degree_eq,e.apply_symm_apply]
    have hcolK: (G.induce (K:Set V)).Colorable 2 :=hcol.of_hom e.symm.toHom
    have hcore:=hN₂ G K b d k hG hnb (by dsimp [t] at hT;omega)
      (by rw [hKcard];dsimp [t] at hT;omega) (hHC.iso e) hKD
      (by rw [hKcard];omega) (by rw [hKcard];omega) hk hcolK ho
    rw [hKcard] at hcore
    have hKL: (K.card:ℝ) ≤ S.card:=by exact_mod_cast hKle
    have hmain: (k:ℝ) * K.card+2*q* (K.card:ℝ) ^ 2+2*K.card ≤
        (k:ℝ) * S.card+2*q* (S.card:ℝ) ^ 2+2*S.card:=by
      gcongr
    have hdel:=rc J T
    change J.edgeFinset.card ≤ H.edgeFinset.card+T.card*Fintype.card (S:Set V) at hdel
    rw [e.card_edgeFinset_eq,hScard] at hdel
    have hdelR: (J.edgeFinset.card:ℝ) ≤ ((G.induce (K:Set V)).edgeFinset.card:ℝ) +
        (T.card:ℝ) * S.card:=by exact_mod_cast hdel
    have hTR: (T.card:ℝ) ≤ (b+3*D+3:ℕ) :=by exact_mod_cast hT
    have hmul:=mul_le_mul_of_nonneg_right hTR (Nat.cast_nonneg S.card: (0:ℝ) ≤ S.card)
    push_cast at hmul ⊢
    nlinarith
end Erdos556
end cs
section cW
namespace Erdos556
open SimpleGraph Finset
theorem uV (D B :ℕ) (hD:0 < D) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (b d k:ℕ) (r η :ℝ),
      qh G → ¬ G.Colorable 2 → 1 ≤ k → 0 ≤ r → 0 ≤ η →
      ((2* (b+3*D+3) : ℕ) : ℝ) ≤ r →
      ((2* (b+3*D+3) : ℕ) : ℝ) * Fintype.card V ≤
        2*η* (r- (2* (b+3*D+3) : ℕ)) ^ 2 →
      ((d+2* (b+3*D+3) : ℕ) : ℝ) ≤ r →
      Fintype.card V ≤ D *d → Fintype.card V ≤ B *b →
      ((N₀+ (b+3*D+3) + 2:ℕ) : ℝ) ≤ r →
      (k:ℝ) + 2*q*Fintype.card V + (b+3*D+5:ℕ) ≤ r →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      ∀ A :Finset V,((G.induce (A:Set V)).edgeFinset.card:ℝ) ≤
        r*A.card+η* (A.card:ℝ) ^ 2:=by
  obtain ⟨N₀,hN₀⟩ :=wW D B hD hB q hq0 hq1
  refine ⟨N₀,?_⟩
  intro V _ _ G _ b d k r η hG hnb hk hr hη ht hbudget hdeg hDcard hBcard horder hmargin ho A
  by_contra hA
  obtain ⟨S,hS,hdense,hmin,hc⟩ :=sR
    G (2* (b+3*D+3)) r η hr hη ht hbudget A (lt_of_not_ge hA)
  have hScard:Fintype.card (S:Set V) = S.card:=by
    calc
      Fintype.card (S:Set V) = (S:Set V).ncard:=Nat.card_eq_fintype_card.symm
      _=S.card:=Set.ncard_coe_finset S
  have hSle:S.card ≤ Fintype.card V :=card_le_univ S
  obtain ⟨v,hv⟩ :=hS
  have hminv:=hmin ⟨v,hv⟩
  have hvdeg:= (G.induce (S:Set V)).degree_lt_card_verts ⟨v,hv⟩
  rw [hScard] at hvdeg
  have hvdegR: ((G.induce (S:Set V)).degree ⟨v,hv⟩ : ℝ) < S.card:=by exact_mod_cast hvdeg
  have hSorder:N₀+ (b+3*D+3) + 2 ≤ S.card:=by
    have h : ((N₀+ (b+3*D+3) + 2:ℕ) : ℝ) ≤ S.card:=by linarith
    exact_mod_cast h
  have hdegrees (w:S) : d+2* (b+3*D+3) ≤ (G.induce (S:Set V)).degree w :=by
    have h :=hdeg.trans (hmin w).le
    exact_mod_cast h
  have hbound:=hN₀ G S b d k hG hnb hSorder hc hdegrees
    (hSle.trans hDcard) (hSle.trans hBcard) hk ho
  have hSleR: (S.card:ℝ) ≤ Fintype.card V :=by exact_mod_cast hSle
  have hsq:=mul_le_mul_of_nonneg_right hSleR (Nat.cast_nonneg S.card: (0:ℝ) ≤ S.card)
  have hqmul:=mul_le_mul_of_nonneg_left hsq (by positivity: (0:ℝ) ≤ 2*q)
  have hrmul:=mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg S.card: (0:ℝ) ≤ S.card)
  have hηmul:=mul_nonneg hη (sq_nonneg (S.card:ℝ))
  nlinarith
end Erdos556
end cW
section cn
namespace Erdos556
private theorem zJ (ε B t N x:ℝ)
    (hε:0 ≤ ε) (ht:0 ≤ t) (hN:0 ≤ N)
    (hB:4096 ≤ ε*B) (htB:B*t ≤ 2*N) (hx:N ≤ 32*x) :
    2*t*N ≤ ε*x^2:=by
  have h1:=mul_le_mul_of_nonneg_right hB (by positivity:0 ≤ 2*t*N)
  have h2:=mul_le_mul_of_nonneg_right htB (by positivity:0 ≤ 2*ε*N)
  have hsq:N^2 ≤ (32*x) ^ 2:=by gcongr
  have h3:=mul_le_mul_of_nonneg_left hsq hε
  nlinarith
private theorem tG (N B :ℕ) (hB:0 < B) (hN:B ≤ N) :
    N ≤ 2*B* (N/B) :=by
  have hb:1 ≤ N/B:=Nat.div_pos hN hB
  have hmod:=Nat.mod_lt N hB
  have hsum:=Nat.mod_add_div N B
  have hmul:=Nat.mul_le_mul_left B hb
  nlinarith
theorem ay (ε:ℝ) (hε:0 < ε) (B N₀ N k:ℕ)
    (hB:128 ≤ B) (hεB:4096 ≤ ε*B)
    (hN:195*B ≤ N) (hN₀:64* (N₀+2) ≤ N) (hk:N ≤ 16*k) :
    ∃ b d:ℕ,
      N ≤ 64*d ∧ N ≤ (2*B) * b ∧
      ((2* (b+195) : ℕ) : ℝ) ≤ (k:ℝ) + ε*N/2 ∧
      ((2* (b+195) : ℕ) : ℝ) * N ≤
        ε* ((k:ℝ) + ε*N/2- (2* (b+195) : ℕ)) ^ 2 ∧
      ((d+2* (b+195) : ℕ) : ℝ) ≤ (k:ℝ) + ε*N/2 ∧
      ((N₀+ (b+195) + 2:ℕ) : ℝ) ≤ (k:ℝ) + ε*N/2 ∧
      (k:ℝ) + ε/8*N+ (b+197:ℕ) ≤ (k:ℝ) + ε*N/2:=by
  let b :=N/B
  let d :=N/32
  let t :=b+195
  let r :ℝ:= (k:ℝ) + ε*N/2
  have hBpos:0 < B:=by omega
  have hBN:B ≤ N:=by nlinarith
  have hdb:N ≤ (2*B) * b:=tG N B hBpos hBN
  have hdd:N ≤ 64*d:=by dsimp [d];omega
  have hBb:b*B ≤ N:=Nat.div_mul_le_self _ _
  have hBt:B*t ≤ 2*N:=by dsimp [t];nlinarith
  have hBtR: (B:ℝ) * t ≤ 2*N:=by exact_mod_cast hBt
  have hB128: (128:ℝ) ≤ B:=by exact_mod_cast hB
  have h64t: (64:ℝ) * t ≤ N:=by
    have h :=mul_le_mul_of_nonneg_right hB128 (Nat.cast_nonneg t : (0:ℝ) ≤ t)
    nlinarith
  have hdN: (32:ℝ) * d ≤ N:=by
    have h :d*32 ≤ N:=Nat.div_mul_le_self _ _
    exact_mod_cast (by nlinarith:32*d ≤ N)
  have hkR: (N:ℝ) ≤ 16*k:=by exact_mod_cast hk
  have hrk: (k:ℝ) ≤ r:=by dsimp [r];exact le_add_of_nonneg_right (by positivity)
  have hdegree: (d:ℝ) + 2*t ≤ r:=by nlinarith
  have htR: (2:ℝ) * t ≤ r:=by have:= (Nat.cast_nonneg d : (0:ℝ) ≤ d);linarith
  have hx: (N:ℝ) ≤ 32* (r-2*t) :=by nlinarith
  have hbudget:=zJ ε B t N (r-2*t) hε.le
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hεB hBtR hx
  have hN₀R: (64:ℝ) * ((N₀:ℝ) + 2) ≤ N:=by exact_mod_cast hN₀
  have horder: (N₀:ℝ) + t+2 ≤ r:=by nlinarith
  have hBNR: (B:ℝ) ≤ N:=by exact_mod_cast hBN
  have hεN: (4096:ℝ) ≤ ε*N:=
    hεB.trans (mul_le_mul_of_nonneg_left hBNR hε.le)
  have h8t: (8:ℝ) * t ≤ ε*N:=by
    have h1:=mul_le_mul_of_nonneg_right (show (16:ℝ) ≤ ε*B by linarith)
      (Nat.cast_nonneg t : (0:ℝ) ≤ t)
    have h2:=mul_le_mul_of_nonneg_left hBtR hε.le
    nlinarith
  have hmargin: (k:ℝ) + ε/8*N+ ((t:ℝ) + 2) ≤ r:=by
    dsimp [r]
    nlinarith
  refine ⟨b,d,hdd,hdb,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.cast_mul,Nat.cast_ofNat,r,t] using htR
  · simpa only [Nat.cast_mul,Nat.cast_ofNat,r,t] using hbudget
  · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,r,t] using hdegree
  · simpa only [Nat.cast_add,Nat.cast_ofNat,r,t] using horder
  · have heq:b+197=t+2:=by dsimp [t]
    simpa only [heq,Nat.cast_add,Nat.cast_ofNat,r] using hmargin
end Erdos556
end cn
section ce
namespace Erdos556
open SimpleGraph Finset
theorem v2 (ε:ℝ) (hε:0 < ε) (hε1:ε ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ),
      N₀ ≤ Fintype.card V → Fintype.card V ≤ 16*k → qh G → ¬ G.Colorable 2 →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      ∀ A :Finset V,((G.induce (A:Set V)).edgeFinset.card:ℝ) ≤
        ((k:ℝ) + ε*Fintype.card V) * A.card:=by
  obtain ⟨B,hB⟩ :=exists_nat_gt ((4096:ℝ) / ε+128)
  have hdiv0: (0:ℝ) ≤ 4096/ε:=by positivity
  have hB128R: (128:ℝ) ≤ B:=by linarith
  have hB128:128 ≤ B:=by exact_mod_cast hB128R
  have hεB: (4096:ℝ) ≤ ε*B:=by
    have h : (4096:ℝ) / ε < B:=by linarith
    have h':= (div_lt_iff₀ hε).mp h
    nlinarith
  have hBpos:0 < 2*B:=by omega
  have hqpos:0 < ε/16:=by positivity
  have hqle:ε/16 ≤ 1:=by linarith
  obtain ⟨N₁,hN₁⟩ :=uV 64 (2*B)
    (by decide) hBpos (ε/16) hqpos hqle
  refine ⟨max (195*B) (64* (N₁+2)),?_⟩
  intro V _ _ G _ k hN hk hG hnb ho
  let N :=Fintype.card V
  have hLarge:195*B ≤ N:=by dsimp [N];omega
  have hThreshold:64* (N₁+2) ≤ N:=by dsimp [N];omega
  have hkpos:1 ≤ k:=by dsimp [N] at hLarge;nlinarith
  obtain ⟨b,d,hDd,hBb,ht,hbudget,hdegree,horder,hmargin⟩ :=
    ay ε hε B N₁ N k hB128 hεB hLarge hThreshold hk
  have hηeq:2* (ε/2) = ε:=by ring
  have hqeq:2* (ε/16) = ε/8:=by ring
  have hquad:=hN₁ G b d k ((k:ℝ) + ε*N/2) (ε/2) hG hnb hkpos
    (by positivity) (by positivity)
    (by simpa [Nat.add_assoc] using ht)
    (by simpa [Nat.add_assoc,hηeq] using hbudget)
    (by simpa [Nat.add_assoc] using hdegree)
    hDd hBb (by simpa [Nat.add_assoc] using horder)
    (by simpa [Nat.add_assoc,hqeq] using hmargin) ho
  intro A
  have hA:=hquad A
  have hcard: (A.card:ℝ) ≤ N:=by exact_mod_cast card_le_univ A
  have hsq:=mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg A.card: (0:ℝ) ≤ A.card)
  have hεsq:=mul_le_mul_of_nonneg_left hsq (by positivity: (0:ℝ) ≤ ε/2)
  change ((G.induce (A:Set V)).edgeFinset.card:ℝ) ≤ ((k:ℝ) + ε*N) * A.card
  nlinarith
theorem xz (ε:ℝ) (hε:0 < ε) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ),
      N₀ ≤ Fintype.card V → Fintype.card V ≤ 16*k → qh G → ¬ G.Colorable 2 →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      ∀ A :Finset V,((G.induce (A:Set V)).edgeFinset.card:ℝ) ≤
        ((k:ℝ) + ε*Fintype.card V) * A.card:=by
  have hδ:0 < min ε 1:=lt_min hε (by norm_num)
  obtain ⟨N₀,hN₀⟩ :=v2 (min ε 1) hδ (min_le_right _ _)
  refine ⟨N₀,?_⟩
  intro V _ _ G _ k hN hk hG hnb ho A
  apply (hN₀ G k hN hk hG hnb ho A).trans
  gcongr
  exact min_le_left ε 1
end Erdos556
end ce
section cp
namespace Erdos556
open SimpleGraph Finset
def rp {V:Type*} (G:SimpleGraph V) (P:Finset (Finset V)) : SimpleGraph V where
  Adj u v:=G.Adj u v ∧ ∃ A ∈ P,u ∈ A ∧ v ∈ A
  symm:= ⟨by
    rintro u v ⟨huv,A,hA,hu,hv⟩
    exact ⟨huv.symm,A,hA,hv,hu⟩⟩
  loopless:= ⟨by intro u h;exact h.1.ne rfl⟩
theorem ah {V:Type*} (G:SimpleGraph V) (P:Finset (Finset V)) :
    rp G P ≤ G:=fun _ _ h => h.1
theorem xE {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (P:Finset (Finset V))
    [DecidableRel (rp G P).Adj]
    (hP: (P:Set (Finset V)).Pairwise Disjoint) :
    (rp G P).edgeFinset.card= ∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card:=by
  classical
  let E (A:Finset V) :=G.edgeFinset.filter (fun e => e.toFinset ⊆ A)
  have hedges: (rp G P).edgeFinset=P.biUnion E :=by
    ext e
    rcases e with ⟨⟨u,v⟩⟩
    change s(u,v) ∈ (rp G P).edgeFinset ↔ s(u,v) ∈ P.biUnion E
    rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    change (G.Adj u v ∧ ∃ A ∈ P,u ∈ A ∧ v ∈ A) ↔ s(u,v) ∈ P.biUnion E
    simp only [mem_edgeFinset,mem_edgeSet,mem_biUnion,E,mem_filter,
      Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff]
    constructor
    · rintro ⟨huv,A,hA,hu,hv⟩
      exact ⟨A,hA,huv,hu,hv⟩
    · rintro ⟨A,hA,huv,hu,hv⟩
      exact ⟨huv,A,hA,hu,hv⟩
  have hdisj: (P:Set (Finset V)).Pairwise fun A B=> Disjoint (E A) (E B) :=by
    intro A hA B hB hAB
    rw [Finset.disjoint_left]
    intro e heA heB
    have ha:= (mem_filter.mp heA).2
    have hb:= (mem_filter.mp heB).2
    obtain ⟨v,hv⟩ :=Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty e)
    exact Finset.disjoint_left.mp (hP hA hB hAB) (ha hv) (hb hv)
  rw [hedges,card_biUnion hdisj]
  apply sum_congr rfl
  intro A _
  exact G.card_filter_edgeFinset_toFinset_subset A
theorem a1 {V:Type*}
    (G:SimpleGraph V) (P:Finset (Finset V)) (n:ℕ) [NeZero n]
    (hP: (P:Set (Finset V)).Pairwise Disjoint)
    (hcolour: ∀ A ∈ P,(G.induce (A:Set V)).Colorable n) :
    (rp G P).Colorable n :=by
  classical
  let C (A:P) : (G.induce (A.val:Set V)).Coloring (Fin n) :=
    Classical.choice (hcolour A.val A.property)
  let Q (v:V) : Prop:= ∃ A:P,v ∈ A.val
  let f (v:V) : Fin n :=if h :Q v then
    C (Classical.choose h) ⟨v,Classical.choose_spec h⟩ else 0
  have hf (A:P) (v:V) (hv:v ∈ A.val) : f v =C A ⟨v,hv⟩ :=by
    have hvQ:Q v:= ⟨A,hv⟩
    dsimp [f]
    rw [dif_pos hvQ]
    have heq:Classical.choose hvQ=A:=by
      apply Subtype.ext
      by_contra hne
      exact Finset.disjoint_left.mp
        (hP (Classical.choose hvQ).property A.property hne) (Classical.choose_spec hvQ) hv
    subst heq
    rfl
  refine ⟨{ toFun:=f,map_rel':= ?_}⟩
  intro u v huv
  obtain ⟨hG,A,hA,hu,hv⟩ :=huv
  rw [hf ⟨A,hA⟩ u hu,hf ⟨A,hA⟩ v hv]
  exact (C ⟨A,hA⟩).valid hG
end Erdos556
end cp
section cy
namespace Erdos556
open SimpleGraph Finset
def qp {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) (P:Finset (Finset V)) : Prop:=
  (P:Set (Finset V)).Pairwise Disjoint ∧
    ∀ A ∈ P,r < A.card ∧ qh (G.induce (A:Set V))
theorem qp.nonempty {V:Type*} [DecidableEq V]
    {G:SimpleGraph V} {r:ℕ} {P:Finset (Finset V)}
    (hP:qp G r P) {A:Finset V} (hA:A ∈ P) : A.Nonempty:=
  card_pos.mp ((Nat.zero_le r).trans_lt (hP.2 A hA).1)
def s4 {V:Type*} [DecidableEq V] (S:Finset V) (P:Finset (Finset S)) :
    Finset (Finset V) :=
  P.map (Finset.mapEmbedding (Function.Embedding.subtype (fun v => v ∈ S))).toEmbedding
theorem vH {V:Type*} [DecidableEq V] (S:Finset V) (P:Finset (Finset S))
    (A:Finset V) : A ∈ s4 S P ↔
      ∃ T ∈ P,T.map (Function.Embedding.subtype (fun v => v ∈ S)) = A:=by
  exact Finset.mem_map
theorem rP {V:Type*} [DecidableEq V]
    {S:Finset V} {P:Finset (Finset S)} {A:Finset V} (hA:A ∈ s4 S P) : A ⊆ S:=by
  obtain ⟨T,_,rfl⟩ := (vH S P A).mp hA
  intro x hx
  obtain ⟨y,_,hyx⟩ :=mem_map.mp hx
  exact hyx ▸ y.property
theorem qp.lift {V:Type*} [DecidableEq V]
    {G:SimpleGraph V} {r:ℕ} {S:Finset V} {P:Finset (Finset S)}
    (hP:qp (G.induce (S:Set V)) r P) :
    qp G r (s4 S P) :=by
  constructor
  · intro A hA B hB hAB
    obtain ⟨T,hT,rfl⟩ := (vH S P A).mp hA
    obtain ⟨U,hU,rfl⟩ := (vH S P B).mp hB
    apply (Finset.disjoint_map _).mpr
    exact hP.1 hT hU (fun h => hAB (congrArg (Finset.map _) h))
  · intro A hA
    obtain ⟨T,hT,rfl⟩ := (vH S P A).mp hA
    refine ⟨by simpa only [card_map] using (hP.2 T hT).1,?_⟩
    exact (hP.2 T hT).2.iso (sy G S T)
theorem vF {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (P:Finset (Finset S)) :
    (∑ A ∈ s4 S P,(G.induce (A:Set V)).edgeFinset.card) =
      ∑ T ∈ P,((G.induce (S:Set V)).induce (T:Set S)).edgeFinset.card:=by
  rw [s4,sum_map]
  apply sum_congr rfl
  intro T _
  exact (sy G S T).card_edgeFinset_eq.symm
theorem ab {V:Type*} [DecidableEq V]
    {S T :Finset V} (hST:Disjoint S T) (P:Finset (Finset S)) (Q:Finset (Finset T))
    (hP: ∀ A ∈ P,A.Nonempty) : Disjoint (s4 S P) (s4 T Q) :=by
  rw [Finset.disjoint_left]
  intro A hAP hAQ
  have hAS:=rP hAP
  have hAT:=rP hAQ
  obtain ⟨U,hU,rfl⟩ := (vH S P A).mp hAP
  obtain ⟨x,hx⟩ :=hP U hU
  have hxmap:x.val ∈ U.map (Function.Embedding.subtype (fun v => v ∈ S)) :=
    mem_map.mpr ⟨x,hx,rfl⟩
  exact Finset.disjoint_left.mp hST (hAS hxmap) (hAT hxmap)
theorem qp.union {V:Type*} [DecidableEq V]
    {G:SimpleGraph V} {r:ℕ} {P Q :Finset (Finset V)}
    (hP:qp G r P) (hQ:qp G r Q)
    (hcross: ∀ A ∈ P,∀ B ∈ Q,Disjoint A B) :
    qp G r (P ∪ Q) :=by
  constructor
  · intro A hA B hB hAB
    rcases mem_union.mp hA with hAP | hAQ <;> rcases mem_union.mp hB with hBP | hBQ
    · exact hP.1 hAP hBP hAB
    · exact hcross A hAP B hBQ
    · exact (hcross B hBP A hAQ).symm
    · exact hQ.1 hAQ hBQ hAB
  · intro A hA
    exact (mem_union.mp hA).elim (hP.2 A) (hQ.2 A)
end Erdos556
end cy
section dw
namespace Erdos556
open SimpleGraph Finset
theorem uU {V:Type*} [Fintype V]
    [DecidableEq V] (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) :
    G.edgeFinset.card ≤ (G.induce (S:Set V)ᶜ).edgeFinset.card+
      ∑ v ∈ S,G.degree v :=by
  classical
  let A :=G.edgeFinset.filter (fun e => e.toFinset ⊆ Sᶜ)
  let B :=S.biUnion (fun v => G.incidenceFinset v)
  have hcover:G.edgeFinset ⊆ A ∪ B:=by
    intro e he
    by_cases h :e.toFinset ⊆ Sᶜ
    · exact mem_union_left _ (mem_filter.mpr ⟨he,h⟩)
    · obtain ⟨x,hxe,hx⟩ :=not_subset.mp h
      have hxS:x ∈ S:=by simpa only [mem_compl,not_not] using hx
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨x,hxS,?_⟩
      rw [G.incidenceFinset_eq_filter]
      exact mem_filter.mpr ⟨he,by simpa using hxe⟩
  have hA:A.card= (G.induce (S:Set V)ᶜ).edgeFinset.card:=by
    have h :=congrArg Finset.card (G.map_edgeFinset_induce (s:= (S:Set V)ᶜ))
    simp only [card_map] at h
    have heq:G.edgeFinset ∩ ((S:Set V)ᶜ).toFinset.sym2=A:=by
      simp [A,G.filter_edgeFinset_toFinset_subset]
    rw [heq] at h
    exact h.symm
  have hB:B.card ≤ ∑ v ∈ S,G.degree v :=by
    simpa only [G.card_incidenceFinset_eq_degree] using
      (card_biUnion_le:B.card ≤ ∑ v ∈ S,(G.incidenceFinset v).card)
  exact (card_le_card hcover).trans ((card_union_le A B).trans (by omega))
theorem rU
    {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (d:ℕ)
    (hd: ∀ v ∈ S,G.degree v ≤ d) :
    G.edgeFinset.card ≤ (G.induce (S:Set V)ᶜ).edgeFinset.card+S.card*d:=by
  have hsum: (∑ v ∈ S,G.degree v) ≤ S.card*d:=by
    calc
      (∑ v ∈ S,G.degree v) ≤ ∑ _v ∈ S,d:=sum_le_sum hd
      _=S.card*d:=by simp
  exact (uU G S).trans (by omega)
theorem ze (r a b s N:ℕ)
    (ha:r < a) (hb:r < b) (hs:s ≤ 1) (hN:a+b+s=N) :
    (r+1) ^ 2*a+a^2+ ((r+1) ^ 2*b+b^2) +
      (r+1) * (s*N) ≤ (r+1) ^ 2*N+N^2:=by
  have hra:r+1 ≤ a:=ha
  have hrb:r+1 ≤ b:=hb
  have h1:=Nat.mul_le_mul_right b hra
  have h2:=Nat.mul_le_mul_right a hrb
  interval_cases s <;> nlinarith
end Erdos556
end dw
section cF
namespace Erdos556
open SimpleGraph Finset
theorem uw {V:Type*} [Fintype V]
    [DecidableEq V] (G:SimpleGraph V) (hcard:3 ≤ Fintype.card V)
    (hG: ¬ qh G) :
    ∃ A B S :Finset V,A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      Disjoint A S ∧ Disjoint B S ∧ A ∪ B ∪ S=univ ∧ S.card ≤ 1 ∧
      ∀ a ∈ A,∀ b ∈ B,¬ G.Adj a b:=by
  classical
  have hex: ∃ S:Finset V,S.card ≤ 1 ∧ ¬ (G.induce (S:Set V)ᶜ).Preconnected:=by
    by_cases hc:G.Connected
    · have hv: ∃ v:V,¬ (G.induce ({v}ᶜ:Set V)).Connected:=by
        by_contra! h
        exact hG ⟨hcard,hc,h⟩
      obtain ⟨v,hv⟩ :=hv
      refine ⟨{v},by simp,?_⟩
      rw [Finset.coe_singleton]
      intro hp
      have hn:0 < Fintype.card ({v}ᶜ:Set V) :=by
        rw [Fintype.card_compl_set,Set.card_singleton]
        omega
      let:Nonempty ({v}ᶜ:Set V) :=Fintype.card_pos_iff.mp hn
      exact hv ⟨hp⟩
    · refine ⟨∅,by simp,?_⟩
      rw [Finset.coe_empty,Set.compl_empty]
      intro hp
      let:Nonempty V :=Fintype.card_pos_iff.mp (by omega)
      exact hc ⟨(G.induceUnivIso.preconnected_iff).mp hp⟩
  obtain ⟨S,hS,hdisc⟩ :=hex
  obtain ⟨A,B,hA,hB,hAB,hAS,hBS,hcover,hcross⟩ :=
    rk G S hdisc
  exact ⟨A,B,S,hA,hB,hAB,hAS,hBS,hcover,hS,hcross⟩
theorem tp {V:Type*} [Fintype V] [DecidableEq V]
    (A B S:Finset V) (hAB:Disjoint A B) (hAS:Disjoint A S)
    (hBS:Disjoint B S) (hcover:A ∪ B ∪ S=univ) :
    A.card+B.card+S.card=Fintype.card V :=by
  have h :=congrArg Finset.card hcover
  rwa [card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAS,hBS⟩),
    card_union_of_disjoint hAB,card_univ] at h
end Erdos556
end cF
section d2
namespace Erdos556
open SimpleGraph Finset
private theorem yu (r N e:ℕ) (hN:N ≤ r)
    (he:2*e ≤ N*N) : (r+1) * e ≤ (r+1) ^ 2*N+N^2:=by
  have h1:=Nat.mul_le_mul_right N hN
  have h2:e ≤ (r+1) * N:=by nlinarith
  have h3:=Nat.mul_le_mul_left (r+1) h2
  nlinarith
private theorem tZ (r a b N e f s:ℕ) (hN:a+b=N)
    (he:e ≤ f+a* (r+1))
    (hf: (r+1) * f ≤ (r+1) * s+ (r+1) ^ 2*b+b^2) :
    (r+1) * e ≤ (r+1) * s+ (r+1) ^ 2*N+N^2:=by
  have h :=Nat.mul_le_mul_left (r+1) he
  nlinarith
universe u
private theorem xP (N:ℕ) :
    ∀ (V:Type u) [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj],Fintype.card V =N →
      ∀ r :ℕ,2 ≤ r → ∃ P:Finset (Finset V),
        qp G r P ∧
        (r+1) * G.edgeFinset.card ≤
          (r+1) * (∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card) +
            (r+1) ^ 2*Fintype.card V + (Fintype.card V) ^ 2:=by
  induction N using Nat.strong_induction_on with
  | h N ih=>
      intro V _ _ G _ hcard r hr
      classical
      by_cases hsmall:Fintype.card V ≤ r
      · refine ⟨∅,⟨by simp,by simp⟩,?_⟩
        simp only [sum_empty,mul_zero,zero_add]
        apply yu r (Fintype.card V) G.edgeFinset.card hsmall
        calc
          2*G.edgeFinset.card= ∑ v,G.degree v :=G.sum_degrees_eq_twice_card_edges.symm
          _ ≤ ∑ _v:V,Fintype.card V :=sum_le_sum fun v _=> (G.degree_lt_card_verts v).le
          _=Fintype.card V *Fintype.card V :=by simp
      by_cases htwo:qh G
      · let e :G.induce (↑(univ:Finset V) : Set V) ≃g G :=
          (x8 G _ _ Finset.coe_univ).trans G.induceUnivIso
        have hc:qh (G.induce (↑(univ:Finset V) : Set V)) :=
          htwo.iso e.symm
        have he: (G.induce (↑(univ:Finset V) : Set V)).edgeFinset.card=G.edgeFinset.card:=by
          exact e.card_edgeFinset_eq
        refine ⟨{univ},⟨by simp,?_⟩,?_⟩
        · intro A hA
          have hA':A=univ:=mem_singleton.mp hA
          subst A
          exact ⟨by simpa only [card_univ] using Nat.lt_of_not_ge hsmall,hc⟩
        · simp only [sum_singleton,he]
          omega
      have hsmallside: ∀ A:Finset V,A.Nonempty → A.card < Fintype.card V →
          (∀ v ∈ A,G.degree v ≤ r +1) → ∃ P :Finset (Finset V),
          qp G r P ∧
          (r+1) * G.edgeFinset.card ≤
            (r+1) * (∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card) +
              (r+1) ^ 2*Fintype.card V + (Fintype.card V) ^ 2:=by
        intro A hA hAlt hdeg
        let T :=Aᶜ
        have hTcard:Fintype.card (T:Set V) = T.card:=Fintype.card_coe T
        have hsum:A.card+T.card=Fintype.card V :=by
          dsimp [T]
          rw [card_compl]
          exact Nat.add_sub_of_le (card_le_univ A)
        have hTlt:Fintype.card (T:Set V) < N:=by
          have hpos:=card_pos.mpr hA
          omega
        obtain ⟨P,hP,heP⟩ :=ih (Fintype.card (T:Set V)) hTlt
          (T:Set V) (G.induce (T:Set V)) rfl r hr
        refine ⟨s4 T P,hP.lift,?_⟩
        rw [vF]
        rw [hTcard] at heP
        have he:=rU G A (r+1) hdeg
        have he':G.edgeFinset.card ≤ (G.induce (T:Set V)).edgeFinset.card+
            A.card* (r+1) :=by
          have heq:= (x8 G (A:Set V)ᶜ (T:Set V)
            (Finset.coe_compl A).symm).card_edgeFinset_eq
          rw [heq] at he
          exact he
        exact tZ r A.card T.card (Fintype.card V) _ _ _ hsum he' heP
      obtain ⟨A,B,S,hA,hB,hAB,hAS,hBS,hcover,hS,hcross⟩ :=
        uw G (by omega) htwo
      have hsum:=tp A B S hAB hAS hBS hcover
      have hApos:=card_pos.mpr hA
      have hBpos:=card_pos.mpr hB
      by_cases hAsmall:A.card ≤ r
      · apply hsmallside A hA (by omega)
        intro v hv
        have hd:=qR G A B S hcover hcross v hv
        omega
      by_cases hBsmall:B.card ≤ r
      · apply hsmallside B hB (by omega)
        intro v hv
        have hcover':B ∪ A ∪ S=univ:=by rw [union_comm B A];exact hcover
        have hcross': ∀ b ∈ B,∀ a ∈ A,¬ G.Adj b a:=
          fun b hb a ha hadj=> hcross a ha b hb hadj.symm
        have hd:=qR G B A S hcover' hcross' v hv
        omega
      have hAc:Fintype.card (A:Set V) = A.card:=Fintype.card_coe A
      have hBc:Fintype.card (B:Set V) = B.card:=Fintype.card_coe B
      obtain ⟨P,hP,heP⟩ :=ih (Fintype.card (A:Set V)) (by omega)
        (A:Set V) (G.induce (A:Set V)) rfl r hr
      obtain ⟨Q,hQ,heQ⟩ :=ih (Fintype.card (B:Set V)) (by omega)
        (B:Set V) (G.induce (B:Set V)) rfl r hr
      have hPQ:Disjoint (s4 A P) (s4 B Q) :=
        ab hAB P Q (fun _ h=> hP.nonempty h)
      refine ⟨s4 A P ∪ s4 B Q,hP.lift.union hQ.lift ?_,?_⟩
      · intro X hX Y hY
        exact hAB.mono (rP hX) (rP hY)
      · rw [sum_union hPQ,vF,vF]
        rw [hAc] at heP
        rw [hBc] at heQ
        have hedge:=vp G A B S hcover hcross
        have hedge':=Nat.mul_le_mul_left (r+1) hedge
        have hpot:=ze r A.card B.card S.card (Fintype.card V)
          (by omega) (by omega) hS hsum
        nlinarith only [heP,heQ,hedge',hpot]
theorem zY {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (r:ℕ) (hr:2 ≤ r) :
    ∃ P :Finset (Finset V),qp G r P ∧
      (r+1) * G.edgeFinset.card ≤
        (r+1) * (∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card) +
          (r+1) ^ 2*Fintype.card V + (Fintype.card V) ^ 2:=
  xP (Fintype.card V) V G rfl r hr
end Erdos556
end d2
section cu
namespace Erdos556
open SimpleGraph Finset
private theorem yH (r N e s :ℕ) (ε:ℝ)
    (_hε:0 < ε) (hr:2 ≤ ε* (r+1))
    (hN:2* (r+1) ≤ ε*N)
    (he: (r+1) * e ≤ (r+1) * s+ (r+1) ^ 2*N+N^2) :
    (e:ℝ) ≤ s+ε* (N:ℝ) ^ 2:=by
  have heR: ((r:ℝ) + 1) * e ≤ ((r:ℝ) + 1) * s+
      ((r:ℝ) + 1) ^ 2*N+ (N:ℝ) ^ 2:=by exact_mod_cast he
  have h1:=mul_le_mul_of_nonneg_right hN
    (by positivity: (0:ℝ) ≤ ((r:ℝ) + 1) * N)
  have h2:=mul_le_mul_of_nonneg_right hr
    (by positivity: (0:ℝ) ≤ (N:ℝ) ^ 2)
  have hbound: ((r:ℝ) + 1) * e ≤ ((r:ℝ) + 1) * (s+ε* (N:ℝ) ^ 2) :=by
    nlinarith only [heR,h1,h2]
  exact (mul_le_mul_iff_right₀ (by positivity: (0:ℝ) < (r:ℝ) + 1)).mp hbound
theorem wF (ε:ℝ) (hε:0 < ε) (R:ℕ) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj],N₀ ≤ Fintype.card V →
      ∃ P :Finset (Finset V),qp G R P ∧
        (G.edgeFinset.card:ℝ) ≤
          (∑ A ∈ P,((G.induce (A:Set V)).edgeFinset.card:ℝ)) +
            ε* (Fintype.card V :ℝ) ^ 2:=by
  obtain ⟨r,hr⟩ :=exists_nat_gt ((R:ℝ) + 2+2/ε)
  have hdiv: (0:ℝ) ≤ 2/ε:=by positivity
  have hrR:R ≤ r:=by exact_mod_cast (show (R:ℝ) ≤ r by linarith)
  have hr2:2 ≤ r:=by exact_mod_cast (show (2:ℝ) ≤ r by linarith)
  have hrε: (2:ℝ) ≤ ε* (r+1) :=by
    have hx:2/ε < (r:ℝ) + 1:=by linarith [Nat.cast_nonneg R (α:=ℝ)]
    have hx':= (div_lt_iff₀ hε).mp hx
    nlinarith
  obtain ⟨N₀,hN₀⟩ :=exists_nat_gt (2* ((r:ℝ) + 1) / ε)
  refine ⟨N₀,?_⟩
  intro V _ _ G _ hN
  obtain ⟨P,hP,heP⟩ :=zY G r hr2
  have hNreal: (N₀:ℝ) ≤ Fintype.card V :=by exact_mod_cast hN
  have hNε:2* ((r:ℝ) + 1) ≤ ε*Fintype.card V :=by
    have hx:= (div_lt_iff₀ hε).mp (hN₀.trans_le hNreal)
    nlinarith
  refine ⟨P,⟨hP.1,fun A hA=> ⟨hrR.trans_lt (hP.2 A hA).1,(hP.2 A hA).2⟩⟩,?_⟩
  have h :=yH r (Fintype.card V) G.edgeFinset.card
    (∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card) ε hε hrε hNε heP
  simpa only [Nat.cast_sum] using h
end Erdos556
end cu
section ck
namespace Erdos556
open SimpleGraph Finset
theorem zo {V:Type*}
    (G:SimpleGraph V) [DecidableRel G.Adj] (A:Finset V) (d:ℝ)
    (h: ∀ T:Finset A,(((G.induce (A:Set V)).induce (T:Set A)).edgeFinset.card:ℝ) ≤
      d*T.card) :
    ∀ S :Finset V,S ⊆ A → ((G.induce (S:Set V)).edgeFinset.card:ℝ) ≤ d*S.card:=by
  classical
  intro S hS
  let T :Finset A :=S.subtype (fun v => v ∈ A)
  have hmap:T.map (Function.Embedding.subtype (fun v => v ∈ A)) = S:=
    subtype_map_of_mem (fun v hv=> hS hv)
  have hcard:T.card=S.card:=by
    have hc:=congrArg Finset.card hmap
    simpa only [card_map] using hc
  let e : (G.induce (A:Set V)).induce (T:Set A) ≃g G.induce (S:Set V) :=
    (sy G A T).trans (x8 G _ _ (congrArg (fun U :Finset V =>
      (U:Set V)) hmap))
  have hT:=h T
  rw [e.card_edgeFinset_eq,hcard] at hT
  exact hT
theorem xs {V:Type*} [Finite V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (P:Finset (Finset V))
    [DecidableRel (rp G P).Adj] (S:Finset V) :
    ((rp G P).induce (S:Set V)).edgeFinset.card ≤
      ∑ A ∈ P,(G.induce (↑(A ∩ S) : Set V)).edgeFinset.card:=by
  classical
  let:=Fintype.ofFinite V
  let E (A:Finset V) :=G.edgeFinset.filter (fun e => e.toFinset ⊆ A ∩ S)
  let F := (rp G P).edgeFinset.filter (fun e => e.toFinset ⊆ S)
  have hcover:F ⊆ P.biUnion E :=by
    intro e he
    obtain ⟨he,hS⟩ :=mem_filter.mp he
    rcases e with ⟨⟨u,v⟩⟩
    rw [mem_edgeFinset,mem_edgeSet] at he
    obtain ⟨huv,A,hA,hu,hv⟩ :=he
    apply mem_biUnion.mpr
    refine ⟨A,hA,mem_filter.mpr ⟨?_,?_⟩⟩
    · simpa using huv
    · have huS:u ∈ S:=hS (by simp)
      have hvS:v ∈ S:=hS (by simp)
      simpa only [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff,mem_inter]
        using And.intro (And.intro hu huS) (And.intro hv hvS)
  calc
    ((rp G P).induce (S:Set V)).edgeFinset.card=F.card:=
      ((rp G P).card_filter_edgeFinset_toFinset_subset S).symm
    _ ≤ (P.biUnion E).card:=card_le_card hcover
    _ ≤ ∑ A ∈ P,(E A).card:=card_biUnion_le
    _= ∑ A ∈ P,(G.induce (↑(A ∩ S) : Set V)).edgeFinset.card:=by
      apply sum_congr rfl
      intro A _
      exact G.card_filter_edgeFinset_toFinset_subset (A ∩ S)
theorem z0 {V:Type*} [DecidableEq V]
    (P:Finset (Finset V)) (hP: (P:Set (Finset V)).Pairwise Disjoint) (S:Finset V) :
    (∑ A ∈ P,(A ∩ S).card) ≤ S.card:=by
  have hdisj: (P:Set (Finset V)).Pairwise fun A B=> Disjoint (A ∩ S) (B ∩ S) :=by
    intro A hA B hB hAB
    exact (hP hA hB hAB).mono (inter_subset_left) (inter_subset_left)
  rw [← card_biUnion hdisj]
  apply card_le_card
  intro v hv
  obtain ⟨A,_,hvA⟩ :=mem_biUnion.mp hv
  exact (mem_inter.mp hvA).2
theorem z5 {V:Type*} [Finite V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (P:Finset (Finset V))
    [DecidableRel (rp G P).Adj]
    (hP: (P:Set (Finset V)).Pairwise Disjoint) (d:ℝ) (hd:0 ≤ d)
    (h: ∀ A ∈ P,∀ S:Finset V,S ⊆ A →
      ((G.induce (S:Set V)).edgeFinset.card:ℝ) ≤ d*S.card) :
    ∀ S :Finset V,(((rp G P).induce (S:Set V)).edgeFinset.card:ℝ) ≤ d*S.card:=by
  classical
  let:=Fintype.ofFinite V
  intro S
  have hcard: (∑ A ∈ P,((A ∩ S).card:ℝ)) ≤ S.card:=by
    exact_mod_cast z0 P hP S
  calc
    (((rp G P).induce (S:Set V)).edgeFinset.card:ℝ) ≤
        ∑ A ∈ P,((G.induce (↑(A ∩ S) : Set V)).edgeFinset.card:ℝ) :=by
      exact_mod_cast xs G P S
    _ ≤ ∑ A ∈ P,d* (A ∩ S).card:=by
      apply sum_le_sum
      intro A hA
      exact h A hA (A ∩ S) inter_subset_left
    _=d* ∑ A ∈ P,((A ∩ S).card:ℝ) := (mul_sum _ _ _).symm
    _ ≤ d*S.card:=mul_le_mul_of_nonneg_left hcard hd
end Erdos556
end ck
section dB
namespace Erdos556
open SimpleGraph Finset
open scoped Classical in
theorem xK (ε:ℝ) (hε:0 < ε) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ),
      N₀ ≤ Fintype.card V → Fintype.card V ≤ 16*k →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      ∃ (B F :SimpleGraph V) (S:Finset V),
        B ≤ G ∧ F ≤ G ∧ B.Colorable 2 ∧
        (∀ u v,B.Adj u v → u ∉ S ∧ v ∉ S) ∧
        (∀ u v,F.Adj u v → u ∈ S ∧ v ∈ S) ∧
        (G.edgeFinset.card:ℝ) ≤ B.edgeFinset.card+F.edgeFinset.card+
          ε* (Fintype.card V :ℝ) ^ 2 ∧
        (∀ A :Finset V,((F.induce (A:Set V)).edgeFinset.card:ℝ) ≤
          ((k:ℝ) + ε*Fintype.card V) * A.card) :=by
  obtain ⟨R,hR⟩ :=xz ε hε
  obtain ⟨N₀,hN₀⟩ :=wF ε hε R
  refine ⟨N₀,?_⟩
  intro V _ _ G _ k hN hk ho
  classical
  obtain ⟨P,hP,heP⟩ :=hN₀ G hN
  let Q :Finset (Finset V) :=P.filter (fun A => (G.induce (A:Set V)).Colorable 2)
  let T :Finset (Finset V) :=P.filter (fun A => ¬ (G.induce (A:Set V)).Colorable 2)
  let S :Finset V :=T.biUnion id
  let B :=rp G Q
  let F :=rp G T
  have hQsub:Q ⊆ P:=filter_subset _ _
  have hTsub:T ⊆ P:=filter_subset _ _
  have hQ: (Q:Set (Finset V)).Pairwise Disjoint:=hP.1.mono hQsub
  have hT: (T:Set (Finset V)).Pairwise Disjoint:=hP.1.mono hTsub
  have hB:B.Colorable 2 :=a1 G Q 2 hQ
    (fun A hA=> (mem_filter.mp hA).2)
  have hQT:Disjoint Q T:=by
    rw [Finset.disjoint_left]
    intro A hAQ hAT
    exact (mem_filter.mp hAT).2 (mem_filter.mp hAQ).2
  have hQTunion:Q ∪ T=P:=filter_union_filter_not_eq _ _
  have heq:B.edgeFinset.card+F.edgeFinset.card=
      ∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card:=by
    rw [xE G Q hQ,xE G T hT,
      ← sum_union hQT,hQTunion]
  refine ⟨B,F,S,ah G Q,ah G T,hB,?_,?_,?_,?_⟩
  · intro u v huv
    obtain ⟨_,A,hA,hu,hv⟩ :=huv
    have hoff (x:V) (hx:x ∈ A) : x ∉ S:=by
      intro hxS
      obtain ⟨C,hC,hxC⟩ :=mem_biUnion.mp hxS
      have hAC:A ≠ C:=by
        intro he
        subst C
        exact Finset.disjoint_left.mp hQT hA hC
      exact Finset.disjoint_left.mp (hP.1 (hQsub hA) (hTsub hC) hAC) hx hxC
    exact ⟨hoff u hu,hoff v hv⟩
  · intro u v huv
    obtain ⟨_,A,hA,hu,hv⟩ :=huv
    exact ⟨mem_biUnion.mpr ⟨A,hA,hu⟩,mem_biUnion.mpr ⟨A,hA,hv⟩⟩
  · have heqR: (B.edgeFinset.card:ℝ) + F.edgeFinset.card=
        ∑ A ∈ P,((G.induce (A:Set V)).edgeFinset.card:ℝ) :=by exact_mod_cast heq
    rw [heqR]
    exact heP
  · apply z5 G T hT
      ((k:ℝ) + ε*Fintype.card V) (by positivity)
    intro A hA
    have hAR:R < A.card:= (hP.2 A (hTsub hA)).1
    have hAc:Fintype.card (A:Set V) = A.card:=Fintype.card_coe A
    have hAk:Fintype.card (A:Set V) ≤ 16*k:=by
      rw [hAc]
      exact (card_le_univ A).trans hk
    have hoA (w: (A:Set V)) (c: (G.induce (A:Set V)).Walk w w)
        (hc:c.IsCycle) (hcodd:Odd c.length) : c.length ≤ 2*k:=by
      let f :G.induce (A:Set V) ↪g G :=SimpleGraph.Embedding.induce (A:Set V)
      have h :=ho (f w) (c.map f.toHom) (hc.map f.injective)
        (by simpa only [Walk.length_map] using hcodd)
      simpa only [Walk.length_map] using h
    have hd:=hR (G.induce (A:Set V)) k (by omega) hAk
      (hP.2 A (hTsub hA)).2 (mem_filter.mp hA).2 hoA
    apply zo G A
    intro U
    apply (hd U).trans
    gcongr
    rw [hAc]
    exact_mod_cast card_le_univ A
end Erdos556
end dB
section d6
namespace Erdos556
open SimpleGraph Finset
open scoped Classical in
theorem vd (ε:ℝ) (hε:0 < ε) :
    ∃ n₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (n:ℕ),
      n₀ ≤ n → Odd n → n ≤ Fintype.card V → Fintype.card V ≤ 4 *n →
      (¬ cycleGraph n ⊑ G) →
      ∃ (B F :SimpleGraph V) (T:Finset V),
        B ≤ G ∧ F ≤ G ∧ B.Colorable 2 ∧
        (∀ u v,B.Adj u v → u ∉ T ∧ v ∉ T) ∧
        (∀ u v,F.Adj u v → u ∈ T ∧ v ∈ T) ∧
        (G.edgeFinset.card:ℝ) ≤ B.edgeFinset.card+F.edgeFinset.card+
          ε* (Fintype.card V :ℝ) ^ 2 ∧
        (∀ A :Finset V,((F.induce (A:Set V)).edgeFinset.card:ℝ) ≤
          ((n:ℝ) / 2+ε*Fintype.card V) * A.card) :=by
  obtain ⟨D,hDreal⟩ :=exists_nat_gt (2/ε)
  have hD:0 < D:=by
    have hp:0 < 2/ε:=by positivity
    have hpD:0 < (D:ℝ) :=hp.trans hDreal
    exact_mod_cast hpD
  have hDε:2 ≤ ε* (D:ℝ) :=by
    have h := (div_lt_iff₀ hε).mp hDreal
    nlinarith
  obtain ⟨N₁,K,hspec⟩ :=uR D hD
  obtain ⟨N₂,hdecomp⟩ :=xK (ε/2) (by positivity)
  obtain ⟨M,hM⟩ :=exists_nat_ge ((K:ℝ) / ε)
  have hKM: (K:ℝ) ≤ ε*M:=by
    have h := (div_le_iff₀ hε).mp hM
    nlinarith
  let R :=max N₁ N₂
  refine ⟨max (D* (R+1)) (max K (max M 3)),?_⟩
  intro V _ _ G _ n hn hodd hnN hNn hno
  classical
  let N :=Fintype.card V
  let q :=N/D
  have hn3:3 ≤ n:=by omega
  have hnK:K ≤ n:=by omega
  have hKN: (K:ℝ) ≤ ε*N:=by
    have hMN:M ≤ N:=by omega
    exact hKM.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hMN) hε.le)
  have hqN: (D:ℝ) * q ≤ N:=by exact_mod_cast (Nat.mul_div_le N D)
  have hqsmall:2* (q:ℝ) ≤ ε*N:=by
    have h₁:=mul_le_mul_of_nonneg_right hDε (show 0 ≤ (q:ℝ) by positivity)
    have h₂:=mul_le_mul_of_nonneg_left hqN hε.le
    nlinarith only [h₁,h₂]
  have hpruneLoss: (q:ℝ) * N ≤ ε/2* (N:ℝ) ^ 2:=by
    have h :=mul_le_mul_of_nonneg_right hqsmall (show 0 ≤ (N:ℝ) by positivity)
    nlinarith only [h]
  obtain ⟨S,hprune,hdegree⟩ :=a4 G (q:ℝ)
  have hcardS:Fintype.card (S:Set V) = S.card:=by
    calc
      Fintype.card (S:Set V) = (S:Set V).ncard:=Nat.card_eq_fintype_card.symm
      _=S.card:=Set.ncard_coe_finset S
  have hSN:S.card ≤ N:=card_le_univ S
  have hcoreLoss: (G.edgeFinset.card:ℝ) ≤ (G.induce (S:Set V)).edgeFinset.card+
      ε/2* (N:ℝ) ^ 2:=by
    have hnonneg:0 ≤ (q:ℝ) * S.card:=by positivity
    change (G.edgeFinset.card:ℝ) - (q:ℝ) * N ≤
      ((G.induce (S:Set V)).edgeFinset.card:ℝ) - (q:ℝ) * S.card at hprune
    linarith
  by_cases hSempty:S= ∅
  · have hezero: (G.induce (S:Set V)).edgeFinset.card=0:=by
      have h := (G.induce (S:Set V)).card_edgeFinset_le_card_choose_two
      have hSc:S.card=0:=by rw [hSempty,card_empty]
      rw [hcardS,hSc] at h
      exact Nat.eq_zero_of_le_zero (by simpa only [Nat.choose_zero_succ] using h)
    rw [hezero,Nat.cast_zero,zero_add] at hcoreLoss
    refine ⟨⊥,⊥,∅,bot_le,bot_le,?_,?_,?_,?_,?_⟩
    · exact ⟨{ toFun:=fun _ => (0:Fin 2),map_rel':=fun h => h.elim}⟩
    · intro u v h
      exact h.elim
    · intro u v h
      exact h.elim
    · have hbot:Nat.card (⊥ : SimpleGraph V).edgeSet=0:=by
        rw [edgeSet_bot]
        simp
      have hnonneg:0 ≤ ε* (N:ℝ) ^ 2:=by positivity
      have hres: (G.edgeFinset.card:ℝ) ≤ ε* (N:ℝ) ^ 2:=by linarith
      simpa only [q7,hbot,Nat.cast_zero,zero_add] using hres
    · intro A
      have he:Nat.card (((⊥ : SimpleGraph V).induce (A:Set V)).edgeSet) = 0:=by
        change Nat.card (⊥ : SimpleGraph (A:Set V)).edgeSet=0
        rw [edgeSet_bot]
        simp
      simpa only [q7,he,Nat.cast_zero] using
        (show (0:ℝ) ≤ ((n:ℝ) / 2+ε*Fintype.card V) * A.card by positivity)
  · have hqR:R+1 ≤ q:=by
      apply (Nat.le_div_iff_mul_le hD).mpr
      have hnR:D* (R+1) ≤ n:=by omega
      exact (by simpa only [Nat.mul_comm] using hnR.trans hnN)
    obtain ⟨s,hs⟩ :=nonempty_iff_ne_empty.mpr hSempty
    have hdegNat (v: (S:Set V)) : q+1 ≤ (G.induce (S:Set V)).degree v :=by
      have h :q < (G.induce (S:Set V)).degree v :=by exact_mod_cast hdegree v
      omega
    have hSlarge:R ≤ Fintype.card (S:Set V) :=by
      have h₁:=hdegNat ⟨s,hs⟩
      have h₂:= (G.induce (S:Set V)).degree_lt_card_verts ⟨s,hs⟩
      omega
    have hscale:Fintype.card (S:Set V) ≤ D* (q+1) :=by
      rw [hcardS]
      exact hSN.trans (Nat.lt_mul_div_succ N hD).le
    have hnoS: ¬ cycleGraph n ⊑ G.induce (S:Set V) :=fun h =>
      hno (h.trans (Embedding.induce (S:Set V)).isContained)
    have hcut:=hspec (G.induce (S:Set V)) (q+1) n
      (by dsimp only [R] at hSlarge;omega) hscale hdegNat hn3 hodd hnK hnoS
    let k := (n+K) / 2
    have hkN:Fintype.card (S:Set V) ≤ 16*k:=by
      rw [hcardS]
      have h :4*n ≤ 16*k:=by dsimp only [k];omega
      exact hSN.trans (hNn.trans h)
    have hoddBound (v: (S:Set V)) (w: (G.induce (S:Set V)).Walk v v)
        (hw:w.IsCycle) (ho:Odd w.length) : w.length ≤ 2*k:=by
      have h :=hcut v w hw ho
      dsimp only [k]
      omega
    obtain ⟨B,F,T,hBG,hFG,hBcol,hBoff,hFon,hE,hFden⟩ :=
      hdecomp (G.induce (S:Set V)) k (by dsimp only [R] at hSlarge;omega) hkN hoddBound
    let f : (S:Set V) ↪ V:=Function.Embedding.subtype _
    have hBmap:B.map f ≤ G := (map_le_iff_le_comap f B G).mpr hBG
    have hFmap:F.map f ≤ G := (map_le_iff_le_comap f F G).mpr hFG
    refine ⟨B.map f,F.map f,T.map f,hBmap,hFmap,hBcol.map f,
      tW B f T hBoff,ac F f T hFon,?_,?_⟩
    · have hBcard:=card_edgeFinset_map f B
      have hFcard:=card_edgeFinset_map f F
      simp only [q7] at hBcard hFcard ⊢
      rw [hBcard,hFcard]
      have hSNreal: (S.card:ℝ) ≤ N:=by exact_mod_cast hSN
      have hsq: (S.card:ℝ) ^ 2 ≤ (N:ℝ) ^ 2:=by nlinarith
      have herror:=mul_le_mul_of_nonneg_left hsq (show 0 ≤ ε /2 by positivity)
      rw [hcardS] at hE
      simp only [q7] at hE hcoreLoss
      change (Nat.card G.edgeSet:ℝ) ≤ (Nat.card B.edgeSet:ℝ) + Nat.card F.edgeSet+ε* (N:
        ℝ) ^ 2
      linarith
    · have hkReal:2* (k:ℝ) ≤ (n:ℝ) + K:=by
        exact_mod_cast (show 2 *k ≤ n+K from Nat.mul_div_le (n+K) 2)
      have hSNreal: (Fintype.card (S:Set V) : ℝ) ≤ N:=by rw [hcardS];exact_mod_cast hSN
      have hmul:=mul_le_mul_of_nonneg_left hSNreal hε.le
      have hcoef: (k:ℝ) + ε/2*Fintype.card (S:Set V) ≤ (n:ℝ) / 2+ε*N:=by
        nlinarith only [hkReal,hKN,hmul]
      have hden:=x2 F f
        ((k:ℝ) + ε/2*Fintype.card (S:Set V)) (by positivity) hFden
      intro A
      have hres:= (hden A).trans (mul_le_mul_of_nonneg_right hcoef (by positivity))
      simpa only [q7] using hres
end Erdos556
end d6
section cA
namespace Erdos556
open SimpleGraph
instance q4.graphDecidableAdj {V:Type*} [DecidableEq V]
    (c:q4 V) (i:Fin 3) : DecidableRel (c.graph i).Adj:=
  fun u v=> inferInstanceAs (Decidable (u ≠ v ∧ c.colour u v=i))
theorem sN (i:Fin 3) : i=0 ∨ i=1 ∨ i=2:=by omega
theorem q4.r7 {V:Type*}
    (c:q4 V) (S:Finset V) (i j k:Fin 3)
    (hall: ∀ a:Fin 3,a=i ∨ a=j ∨ a=k)
    (hi: ∀ u ∈ S,∀ v ∈ S,¬ (c.graph i).Adj u v)
    (hj: ∀ u ∈ S,∀ v ∈ S,¬ (c.graph j).Adj u v) : (c.graph k).IsClique (S:Set V) :=by
  intro u hu v hv huv
  rcases hall (c.colour u v) with h | h | h
  · exact (hi u hu v hv ⟨huv,h⟩).elim
  · exact (hj u hu v hv ⟨huv,h⟩).elim
  · exact ⟨huv,h⟩
end Erdos556
end cA
section dc
namespace Erdos556
open Finset
def qc (i:Fin 4) : wz:=
  ![![false,false,false],![false,true,true],![true,false,true],![true,true,false]] i
def qu (i:Fin 4) (a:Fin 3) : q1:=
  fun j => if j =a then none else some (qc i j)
def vI (i:Fin 4) (a:Fin 3) : wz:=
  fun j => if j =a then !(qc i j) else qc i j
theorem yh: ∀ (i:Fin 4) (a:Fin 3),
    q3 (qu i a) = 1:=by decide
theorem r5: ∀ (i:Fin 4) (a:Fin 3),
    qc i ∈ q0 (qu i a) :=by decide
theorem un: ∀ (i:Fin 4) (a:Fin 3),
    vI i a ∈ q0 (qu i a) :=by decide
theorem tq: ∀ p:q1,q3 p =1 →
    ∃ (i:Fin 4) (a:Fin 3),p=qu i a:=by decide
def qV (p q :q1) (i:Fin 3) : Prop:=
  (p i =some false ∧ q i =some true) ∨ (p i =some true ∧ q i =some false)
instance (p q :q1) (i:Fin 3) : Decidable (qV p q i) :=
  inferInstanceAs (Decidable ((p i =some false ∧ q i =some true) ∨
    (p i =some true ∧ q i =some false)))
def q5 (p q :q1) (i:Fin 3) : Prop:=
  qV p q i ∧ ∀ j,j ≠ i → ¬ qV p q j
instance (p q :q1) (i:Fin 3) : Decidable (q5 p q i) :=
  inferInstanceAs (Decidable (qV p q i ∧ ∀ j,j ≠ i → ¬ qV p q j))
def uf (p:Fin 4 → q1) (k:Fin 3 → Fin 3) : Prop:=
  q5 (p 0) (p 2) (k 0) ∧ q5 (p 1) (p 3) (k 0) ∧
  q5 (p 0) (p 1) (k 1) ∧ q5 (p 2) (p 3) (k 1)
def uq (p:Fin 4 → q1) (k:Fin 3 → Fin 3) : Prop:=
  q5 (p 0) (p 2) (k 0) ∧ q5 (p 0) (p 3) (k 0) ∧
  q5 (p 1) (p 2) (k 0) ∧ q5 (p 1) (p 3) (k 0) ∧
  q5 (p 0) (p 1) (k 1) ∧ q5 (p 2) (p 3) (k 2)
instance (p:Fin 4 → q1) (k:Fin 3 → Fin 3) : Decidable (uf p k) :=
  inferInstanceAs (Decidable (q5 (p 0) (p 2) (k 0) ∧
    q5 (p 1) (p 3) (k 0) ∧ q5 (p 0) (p 1) (k 1) ∧
    q5 (p 2) (p 3) (k 1)))
instance (p:Fin 4 → q1) (k:Fin 3 → Fin 3) : Decidable (uq p k) :=
  inferInstanceAs (Decidable (q5 (p 0) (p 2) (k 0) ∧
    q5 (p 0) (p 3) (k 0) ∧ q5 (p 1) (p 2) (k 0) ∧
    q5 (p 1) (p 3) (k 0) ∧ q5 (p 0) (p 1) (k 1) ∧
    q5 (p 2) (p 3) (k 2)))
end Erdos556
end dc
section cx
namespace Erdos556
open SimpleGraph Finset
structure q2 {V:Type*} (c:q4 V) (E D :ℝ) where
  bipartite:Fin 3 → SimpleGraph V
  sparse:Fin 3 → SimpleGraph V
  stars:Fin 3 → Finset V
  bicolouring: ∀ i,(bipartite i).Coloring Bool
  bipartite_le: ∀ i,bipartite i ≤ c.graph i
  sparse_le: ∀ i,sparse i ≤ c.graph i
  bipartite_off: ∀ i u v,(bipartite i).Adj u v → u ∉ stars i ∧ v ∉ stars i
  sparse_on: ∀ i u v,(sparse i).Adj u v → u ∈ stars i ∧ v ∈ stars i
  edge_loss: ∀ i,(Nat.card (c.graph i).edgeSet:ℝ) ≤
    Nat.card (bipartite i).edgeSet+Nat.card (sparse i).edgeSet+E
  hereditary_density: ∀ i (A:Finset V),(Nat.card ((sparse i).induce (A:Set V)).edgeSet:ℝ) ≤
    D*A.card
theorem wZ (ε:ℝ) (hε:0 < ε) :
    ∃ n₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (c:q4 V) (n:ℕ),
      n₀ ≤ n → Odd n → n ≤ Fintype.card V → Fintype.card V ≤ 4 *n →
      (∀ i,¬ cycleGraph n ⊑ c.graph i) →
      Nonempty (q2 c (ε* (Fintype.card V :ℝ) ^ 2)
        ((n:ℝ) / 2+ε*Fintype.card V)) :=by
  obtain ⟨n₀,hn₀⟩ :=vd ε hε
  refine ⟨n₀,?_⟩
  intro V _ _ c n hn hodd hnN hNn hno
  classical
  choose B F T hBG hFG hcol hBoff hFon he hden using
    fun i => hn₀ (c.graph i) n hn hodd hnN hNn (hno i)
  refine ⟨{
    bipartite:=B
    sparse:=F
    stars:=T
    bicolouring:=fun i => (B i).recolorOfEquiv finTwoEquiv (Classical.choice (hcol i))
    bipartite_le:=hBG
    sparse_le:=hFG
    bipartite_off:=hBoff
    sparse_on:=hFon
    edge_loss:= ?_
    hereditary_density:= ?_}⟩
  · intro i
    simpa only [q7] using he i
  · intro i A
    simpa only [q7] using hden i A
def q2.profile {V:Type*} [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (v:V) : q1:=
  fun i => if v ∈ h.stars i then none else some (h.bicolouring i v)
def q2.qa {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (p:q1) :
      Finset V :=
  univ.filter (fun v => h.profile v =p)
def q2.retained {V:Type*}
    {c:q4 V} {E D :ℝ} (h:q2 c E D) : SimpleGraph V :=
  ⨆ i,h.bipartite i ⊔ h.sparse i
def q2.missing {V:Type*}
    {c:q4 V} {E D :ℝ} (h:q2 c E D) : SimpleGraph V :=
  h.retainedᶜ
theorem q2.ry {V:Type*} [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D)
    (i:Fin 3) (u v :V) (huv: (h.bipartite i).Adj u v) :
    qV (h.profile u) (h.profile v) i :=by
  have hu:= (h.bipartite_off i u v huv).1
  have hv:= (h.bipartite_off i u v huv).2
  have hbits:= (h.bicolouring i).valid huv
  simp only [qV,profile,if_neg hu,if_neg hv,Option.some.injEq]
  cases huval:h.bicolouring i u <;> cases hvval:h.bicolouring i v <;> simp_all
theorem q2.z1 {V:Type*} [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D)
    (i:Fin 3) (u v :V) (huv: (h.sparse i).Adj u v) :
    h.profile u i=none ∧ h.profile v i=none:=by
  have hu:= (h.sparse_on i u v huv).1
  have hv:= (h.sparse_on i u v huv).2
  simp only [profile,if_pos hu,if_pos hv,and_self]
end Erdos556
end cx
section dA
namespace Erdos556
open SimpleGraph Finset
theorem q2.r3 {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (p:q1) (v:
      V) :
    v ∈ h.qa p ↔ h.profile v =p:=by
  simp only [qa,mem_filter,mem_univ,true_and]
theorem q2.tK {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D)
    (p q :q1) (hpq:p ≠ q) : Disjoint (h.qa p) (h.qa q) :=by
  apply Finset.disjoint_left.mpr
  intro v hvp hvq
  exact hpq ((h.r3 p v).mp hvp |>.symm.trans ((h.r3 q v).mp
    hvq))
theorem q2.xF {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) :
    (∑ p,(h.qa p).card) = Fintype.card V :=aE h.profile
theorem q2.aK {V:Type*} [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (v:V) (i:Fin 3) :
    h.profile v i=none ↔ v ∈ h.stars i :=by
  by_cases hv:v ∈ h.stars i <;> simp [profile,hv]
theorem q2.tQ {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) :
    (∑ i,(h.stars i).card) = ∑ p,q3 p * (h.qa p).card:=by
  classical
  have hstar (i:Fin 3) : (h.stars i).card= ∑ v,if h.profile v i=none then 1 else 0 :=by
    rw [sum_boole]
    congr 1
    ext v
    simp only [mem_filter,mem_univ,true_and,h.aK]
  calc
    _= ∑ i,∑ v,if h.profile v i=none then 1 else 0 :=sum_congr rfl (fun i _=> hstar i)
    _= ∑ v,∑ i,if h.profile v i=none then 1 else 0 :=sum_comm
    _= ∑ v,q3 (h.profile v) :=by
      apply sum_congr rfl
      intro v _
      rw [q3,sum_boole]
      simp only [Nat.cast_id]
    _= ∑ p,(h.qa p).card*q3 p :=vn h.profile
      q3
    _=_:=sum_congr rfl (fun _ _=> Nat.mul_comm _ _)
end Erdos556
end dA
section dG
namespace Erdos556
open SimpleGraph Finset
theorem vZ {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card+Gᶜ.edgeFinset.card= (Fintype.card V).choose 2 :=by
  classical
  have hdisj:Disjoint G.edgeFinset Gᶜ.edgeFinset:=by
    rw [Finset.disjoint_left]
    intro e he hec
    rcases e with ⟨⟨u,v⟩⟩
    have hG:G.Adj u v:=by simpa using he
    have hc:Gᶜ.Adj u v:=by simpa using hec
    have hc':u ≠ v ∧ ¬ G.Adj u v:=by simpa only [compl_adj] using hc
    exact hc'.2 hG
  have hunion:G.edgeFinset ∪ Gᶜ.edgeFinset= (⊤ : SimpleGraph V).edgeFinset:=by
    ext e
    rcases e with ⟨⟨u,v⟩⟩
    simp only [mem_union,mem_edgeFinset,mem_edgeSet,top_adj,compl_adj]
    constructor
    · rintro (h | h)
      · exact h.ne
      · exact h.1
    · intro hne
      by_cases h :G.Adj u v
      · exact Or.inl h
      · exact Or.inr ⟨hne,h⟩
  calc
    G.edgeFinset.card+Gᶜ.edgeFinset.card= (G.edgeFinset ∪ Gᶜ.edgeFinset).card:=
      (card_union_of_disjoint hdisj).symm
    _= (Fintype.card V).choose 2 :=by rw [hunion,card_edgeFinset_top_eq_card_choose_two]
theorem rn {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] :
    2* ((G.edgeFinset.card:ℝ) + Gᶜ.edgeFinset.card) =
      (Fintype.card V :ℝ) * ((Fintype.card V :ℝ) - 1) :=by
  have h : (G.edgeFinset.card:ℝ) + Gᶜ.edgeFinset.card= ((Fintype.card V).choose 2 :ℝ) :=by
    exact_mod_cast vZ G
  rw [h,Nat.cast_choose_two]
  ring
theorem uh {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] :
    2* (G.edgeFinset.card:ℝ) ≤ (Fintype.card V :ℝ) * ((Fintype.card V :ℝ) - 1) :=by
  classical
  have h : (G.edgeFinset.card:ℝ) ≤ ((Fintype.card V).choose 2 :ℝ) :=by
    exact_mod_cast G.card_edgeFinset_le_card_choose_two
  rw [Nat.cast_choose_two] at h
  linarith
theorem z9 {V:Type*} (G:SimpleGraph V) (S:Set V) :
    (G.induce S)ᶜ=Gᶜ.induce S :=by
  ext x y
  simp only [compl_adj,induce_adj,ne_eq,Subtype.coe_inj]
end Erdos556
end dG
section dp
namespace Erdos556
open SimpleGraph Finset
open scoped Classical in
theorem c8 {V I :Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (G:I → SimpleGraph V) : (⨆ i,G i).edgeFinset=univ.biUnion (fun i => (G i).edgeFinset) :=by
  ext e
  simp only [mem_edgeFinset,edgeSet_iSup,Set.mem_iUnion,mem_biUnion,mem_univ,true_and]
theorem wD {V I :Type*} [Finite V] [Fintype I]
    (G:I → SimpleGraph V) (hdis: ∀ i j,i ≠ j → Disjoint (G i) (G j)) :
    Nat.card (⨆ i,G i).edgeSet= ∑ i,Nat.card (G i).edgeSet:=by
  classical
  let:=Fintype.ofFinite V
  have hd: ((univ:Finset I) : Set I).Pairwise (fun i j=> Disjoint (G i).edgeFinset (G
    j).edgeFinset) :=by
    intro i _ j _ hij
    exact SimpleGraph.disjoint_edgeFinset.mpr (hdis i j hij)
  have h : (⨆ i,G i).edgeFinset.card= ∑ i,(G i).edgeFinset.card:=by
    rw [c8,card_biUnion hd]
  simpa only [q7] using h
theorem yD {V:Type*} [Finite V]
    (G H :SimpleGraph V) (hdis:Disjoint G H) :
    Nat.card (G ⊔ H).edgeSet=Nat.card G.edgeSet+Nat.card H.edgeSet:=by
  classical
  let:=Fintype.ofFinite V
  have h : (G ⊔ H).edgeFinset.card=G.edgeFinset.card+H.edgeFinset.card:=by
    rw [edgeFinset_sup,card_union_of_disjoint (SimpleGraph.disjoint_edgeFinset.mpr hdis)]
  simpa only [q7] using h
theorem v1 {V:Type*} [Finite V]
    (G:SimpleGraph V) : Nat.card G.edgeSet+Nat.card Gᶜ.edgeSet=Nat.card (⊤ : SimpleGraph
      V).edgeSet:=by
  classical
  let:=Fintype.ofFinite V
  have h :=vZ G
  have ht:=card_edgeFinset_top_eq_card_choose_two (V:=V)
  simp only [q7] at h ht
  exact h.trans ht.symm
theorem q4.zs {V:Type*} (c:q4 V)
    (i j :Fin 3) (hij:i ≠ j) : Disjoint (c.graph i) (c.graph j) :=by
  apply SimpleGraph.disjoint_left.mpr
  intro u v hi hj
  exact hij (hi.2.symm.trans hj.2)
theorem q4.aF {V:Type*} (c:q4 V) :
    (⨆ i,c.graph i) = ⊤ :=by
  ext u v
  rw [iSup_adj,top_adj]
  constructor
  · rintro ⟨i,hi⟩
    exact hi.1
  · intro huv
    exact ⟨c.colour u v,huv,rfl⟩
theorem q4.bz {V:Type*} [Finite V]
    (c:q4 V) :
    (∑ i,Nat.card (c.graph i).edgeSet) = Nat.card (⊤ : SimpleGraph V).edgeSet:=by
  classical
  let:=Fintype.ofFinite V
  have h :=wD c.graph c.zs
  rw [c.aF] at h
  exact h.symm
end Erdos556
end dp
section di
namespace Erdos556
open SimpleGraph Finset
theorem q2.co {V:Type*}
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (i:Fin 3) :
    Disjoint (h.bipartite i) (h.sparse i) :=by
  apply SimpleGraph.disjoint_left.mpr
  intro u v hB hF
  exact (h.bipartite_off i u v hB).1 (h.sparse_on i u v hF).1
theorem q2.zD {V:Type*} [Finite V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) :
    Nat.card h.retained.edgeSet=
      ∑ i,(Nat.card (h.bipartite i).edgeSet+Nat.card (h.sparse i).edgeSet) :=by
  classical
  let:=Fintype.ofFinite V
  have hdis (i j :Fin 3) (hij:i ≠ j) :
      Disjoint (h.bipartite i ⊔ h.sparse i) (h.bipartite j ⊔ h.sparse j) :=
    (c.zs i j hij).mono (sup_le (h.bipartite_le i) (h.sparse_le i))
      (sup_le (h.bipartite_le j) (h.sparse_le j))
  dsimp only [retained]
  rw [wD _ hdis]
  apply sum_congr rfl
  intro i _
  exact yD _ _ (h.co i)
theorem q2.v9 {V:Type*} [Finite V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) :
    (Nat.card h.missing.edgeSet:ℝ) ≤ 3*E:=by
  classical
  let:=Fintype.ofFinite V
  have hcol: (∑ i,(Nat.card (c.graph i).edgeSet:ℝ)) = Nat.card (⊤ : SimpleGraph V).edgeSet:=by
    exact_mod_cast c.bz
  have hret: (Nat.card h.retained.edgeSet:ℝ) =
      ∑ i,((Nat.card (h.bipartite i).edgeSet:ℝ) + Nat.card (h.sparse i).edgeSet) :=by
    exact_mod_cast h.zD
  have hcomp: (Nat.card h.retained.edgeSet:ℝ) + Nat.card h.missing.edgeSet=
      Nat.card (⊤ : SimpleGraph V).edgeSet:=by
    exact_mod_cast v1 h.retained
  have hsum: (∑ i,(Nat.card (c.graph i).edgeSet:ℝ)) ≤
      (∑ i,((Nat.card (h.bipartite i).edgeSet:ℝ) + Nat.card (h.sparse i).edgeSet)) + 3*E:=by
    calc
      _ ≤ ∑ i,((Nat.card (h.bipartite i).edgeSet:ℝ) + Nat.card (h.sparse i).edgeSet+E) :=
        sum_le_sum (fun i _=> h.edge_loss i)
      _=_:=by rw [sum_add_distrib];simp
  linarith
theorem q2.tU {V:Type*} [Finite V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (i:Fin 3) :
    (Nat.card (h.sparse i).edgeSet:ℝ) ≤ D* (h.stars i).card:=by
  classical
  let:=Fintype.ofFinite V
  have hsupp: (h.sparse i).support ⊆ (h.stars i :Set V) :=by
    intro u hu
    obtain ⟨v,huv⟩ :=hu
    exact (h.sparse_on i u v huv).1
  have hcount:= (h.sparse i).card_edgeFinset_induce_of_support_subset hsupp
  simp only [q7] at hcount
  have hd:=h.hereditary_density i (h.stars i)
  rw [hcount] at hd
  exact hd
end Erdos556
end di
section dt
namespace Erdos556
theorem re: ∀ (p q :q1) (i:Fin 3),
    qV p q i → Disjoint (q0 p) (q0 q) :=by decide
theorem uc: ∀ (p q :q1) (i:Fin 3),
    (q0 p ∩ q0 q).card=1 → ¬ (p i =none ∧ q i =none) :=by decide
theorem xm: ∀ p:q1,q3 p =1 →
    ∃ i,p i=none ∧ ∀ j,p j=none → j=i:=by decide
end Erdos556
end dt
section cC
namespace Erdos556
open SimpleGraph Finset
theorem xj {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (B:Finset V) (u:V)
    (h: ∀ v ∈ B,u ≠ v → G.Adj u v) : B.card ≤ G.degree u +1:=by
  classical
  have hsub:B.erase u ⊆ G.neighborFinset u :=by
    intro v hv
    exact (G.mem_neighborFinset u v).mpr (h v (mem_of_mem_erase hv) (mem_erase.mp hv).1.symm)
  have hc:=card_le_card hsub
  rw [card_neighborFinset_eq_degree] at hc
  by_cases hu:u ∈ B
  · rw [card_erase_of_mem hu] at hc
    omega
  · rw [erase_eq_of_notMem hu] at hc
    omega
theorem xb {V:Type*} [Fintype V]
    (G:SimpleGraph V) (A B :Finset V)
    (h: ∀ u ∈ A,∀ v ∈ B,u ≠ v → G.Adj u v) :
    A.card*B.card ≤ 2*Nat.card G.edgeSet+Fintype.card V :=by
  classical
  calc
    A.card*B.card= ∑ _u ∈ A,B.card:=by simp
    _ ≤ ∑ u ∈ A,(G.degree u +1) :=
      sum_le_sum (fun u hu=> xj G B u (h u hu))
    _= (∑ u ∈ A,G.degree u) + A.card:=by rw [sum_add_distrib];simp
    _ ≤ (∑ u,G.degree u) + Fintype.card V :=
      Nat.add_le_add (sum_le_sum_of_subset (subset_univ _)) (card_le_univ A)
    _=_:=by rw [G.sum_degrees_eq_twice_card_edges,q7]
theorem zW {V:Type*} [Finite V]
    (G H :SimpleGraph V) (h:G ≤ H) : Nat.card G.edgeSet ≤ Nat.card H.edgeSet:=by
  classical
  let:=Fintype.ofFinite V
  have hc:=card_le_card (edgeFinset_mono h)
  simpa only [q7] using hc
theorem t2 {V:Type*} [Finite V]
    (G:SimpleGraph V) (S:Finset V) : Nat.card (G.induce (S:Set V)).edgeSet ≤ Nat.card
      G.edgeSet:=by
  classical
  let:=Fintype.ofFinite V
  let f := (Embedding.induce (G:=G) (S:Set V)).toCopy.mapEdgeSet
  have h :=Fintype.card_le_of_injective f f.injective
  simpa only [← Nat.card_eq_fintype_card] using h
end Erdos556
end cC
section cV
namespace Erdos556
open SimpleGraph Finset
theorem yx {V:Type*} [Fintype V] :
    2* (Nat.card (⊤ : SimpleGraph V).edgeSet:ℝ) + Fintype.card V =
      (Fintype.card V :ℝ) ^ 2:=by
  classical
  rw [sb]
  have hd: (∑ u :V,∑ v:V,if u =v then (1:ℝ) else 0) = Fintype.card V :=by
    simp
  rw [← hd]
  calc
    _= ∑ u:V,∑ v:V,
        ((if (⊤ : SimpleGraph V).Adj u v then (1:ℝ) else 0) +
          if u =v then 1 else 0) :=by simp only [sum_add_distrib]
    _= ∑ _u:V,∑ _v:V,(1:ℝ) :=by
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      by_cases huv:u=v <;> simp [top_adj,huv]
    _=_:=by simp [pow_two]
def q2.bipartiteUnion {V:Type*}
    {c:q4 V} {E D :ℝ} (h:q2 c E D) :
    SimpleGraph V := ⨆ i,h.bipartite i
theorem q2.vm {V:Type*} [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) :
    h.bipartiteUnion ≤ qJ h.profile:=by
  intro u v huv
  obtain ⟨i,hi⟩ :=iSup_adj.mp huv
  exact re _ _ _ (h.ry i u v hi)
theorem q2.yj {V:Type*}
    [Finite V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) :
    Nat.card h.bipartiteUnion.edgeSet= ∑ i,Nat.card (h.bipartite i).edgeSet:=by
  classical
  let:=Fintype.ofFinite V
  apply wD
  intro i j hij
  exact (c.zs i j hij).mono (h.bipartite_le i) (h.bipartite_le j)
theorem q2.yE {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) :
    (Fintype.card V :ℝ) ^ 2 ≤ Fintype.card V +
      2*Nat.card h.bipartiteUnion.edgeSet+
      2*D* (∑ p,(q3 p :ℝ) * (h.qa p).card) + 6*E:=by
  have hret: (Nat.card h.retained.edgeSet:ℝ) =
      (Nat.card h.bipartiteUnion.edgeSet:ℝ) + ∑ i,(Nat.card (h.sparse i).edgeSet:ℝ) :=by
    have hh:=h.zD
    rw [sum_add_distrib,← h.yj] at hh
    exact_mod_cast hh
  have hf: (∑ i,(Nat.card (h.sparse i).edgeSet:ℝ)) ≤
      D* (∑ p,(q3 p :ℝ) * (h.qa p).card) :=by
    calc
      _ ≤ ∑ i,D* (h.stars i).card:=sum_le_sum (fun i _=> h.tU i)
      _=D* (∑ i,((h.stars i).card:ℝ)) := (mul_sum _ _ _).symm
      _=_:=by
        congr 1
        exact_mod_cast h.tQ
  have hcomp: (Nat.card h.retained.edgeSet:ℝ) + Nat.card h.missing.edgeSet=
      Nat.card (⊤ : SimpleGraph V).edgeSet:=by
    exact_mod_cast v1 h.retained
  have hm:=h.v9
  have ht:=yx (V:=V)
  linarith
theorem q2.yS {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (n:ℝ) :
    (Fintype.card V :ℝ) ^ 2-
        qO (fun p => ((h.qa p).card:ℝ)) -
        n* (∑ p,(q3 p :ℝ) * (h.qa p).card) ≤
      Fintype.card V + (2*D-n) *
        (∑ p,(q3 p :ℝ) * (h.qa p).card) + 6*E:=by
  have hpot:=sY h.profile
  have hle: (Nat.card h.bipartiteUnion.edgeSet:ℝ) ≤
      Nat.card (qJ h.profile).edgeSet:=by
    exact_mod_cast zW _ _ h.vm
  have hb:=h.yE
  change 2 * (Nat.card (qJ h.profile).edgeSet:ℝ) =
    qO (fun p => ((h.qa p).card:ℝ)) at hpot
  nlinarith
theorem q2.wR {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) :
    (∑ p,(q3 p :ℝ) * (h.qa p).card) ≤ 3*Fintype.card V :=by
  have hs: (∑ i,(h.stars i).card) ≤ 3*Fintype.card V :=by
    calc
      _ ≤ ∑ _i:Fin 3,Fintype.card V :=sum_le_sum (fun i _=> card_le_univ _)
      _=_:=by simp
  rw [h.tQ] at hs
  exact_mod_cast hs
end Erdos556
end cV
section cv
namespace Erdos556
open SimpleGraph Finset
theorem q2.uZ {V:Type*}
    [DecidableEq V] {c:q4 V} {E D :ℝ} (h:q2 c E D)
    (u v :V) (huv:u ≠ v)
    (hinter: (q0 (h.profile u) ∩ q0 (h.profile v)).card=1) :
    h.missing.Adj u v:=by
  rw [missing,compl_adj]
  refine ⟨huv,?_⟩
  intro hret
  obtain ⟨i,hi⟩ :=iSup_adj.mp hret
  rcases hi with hB | hF
  · have hdis:=re _ _ i (h.ry i u v hB)
    have he:q0 (h.profile u) ∩ q0 (h.profile v) = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdis
    rw [he,card_empty] at hinter
    omega
  · exact uc _ _ i hinter
      (h.z1 i u v hF)
theorem q2.su {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (p q :q1)
    (hpq: (q0 p ∩ q0 q).card=1) :
    ((h.qa p).card:ℝ) * (h.qa q).card ≤ 6*E+Fintype.card V :=by
  classical
  have hpair: ∀ u ∈ h.qa p,∀ v ∈ h.qa q,u ≠ v → h.missing.Adj u v:=by
    intro u hu v hv huv
    apply h.uZ u v huv
    rw [(h.r3 p u).mp hu,(h.r3 q v).mp hv]
    exact hpq
  have hc:=xb h.missing (h.qa p) (h.qa q) hpair
  have hcR: ((h.qa p).card:ℝ) * (h.qa q).card ≤
      2* (Nat.card h.missing.edgeSet:ℝ) + Fintype.card V :=by exact_mod_cast hc
  have hm:=h.v9
  linarith
theorem q2.zQ {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (p:q1) (hp:q3 p =0) :
    ((h.qa p).card:ℝ) ^ 2 ≤ 6*E+Fintype.card V :=by
  have hpq: (q0 p ∩ q0 p).card=1:=by
    rw [inter_self,qU,hp]
    rfl
  simpa only [pow_two] using h.su p p hpq
theorem q2.w4 {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (p:q1) (i:Fin 3)
    (hfree: ∀ j,p j=none → j=i)
    (u v :V) (hu:u ∈ h.qa p) (hv:v ∈ h.qa p)
    (hwrong: (c.graph i)ᶜ.Adj u v) : h.missing.Adj u v:=by
  rw [missing,compl_adj]
  refine ⟨hwrong.1,?_⟩
  intro hret
  obtain ⟨j,hj⟩ :=iSup_adj.mp hret
  have hup:= (h.r3 p u).mp hu
  have hvp:= (h.r3 p v).mp hv
  rcases hj with hB | hF
  · have hopp:=h.ry j u v hB
    rw [hup,hvp] at hopp
    rcases hopp with ⟨h0,h1⟩ | ⟨h1,h0⟩ <;>
      have he: (some false:Option Bool) = some true:=h0.symm.trans h1 <;> cases he
  · have hpf:= (h.z1 j u v hF).1
    rw [hup] at hpf
    have hji:=hfree j hpf
    subst j
    exact hwrong.2 (h.sparse_le i hF)
end Erdos556
end cv
section cm
namespace Erdos556
open SimpleGraph Finset
theorem wo {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj]
    (A:Finset V) (v:V) (hv:v ∈ A)
    (hadj: ∀ u ∈ A,u ≠ v → G.Adj v u) : A.card ≤ G.degree v +1:=by
  classical
  have hsub:A.erase v ⊆ G.neighborFinset v :=by
    intro u hu
    rw [mem_erase] at hu
    exact (G.mem_neighborFinset v u).mpr (hadj u hu.2 hu.1)
  have h :=card_le_card hsub
  rw [card_erase_of_mem hv,G.card_neighborFinset_eq_degree] at h
  have hp:=card_pos.mpr ⟨v,hv⟩
  omega
theorem zO {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A:Finset V) (d:ℕ)
    (hN:3 ≤ Fintype.card V)
    (hsize:Fintype.card V +2*d ≤ 2*A.card)
    (hcore: ∀ v ∈ A,A.card ≤ G.degree v +d)
    (hout: ∀ v ∉ A,Fintype.card V -A.card+1 ≤ G.degree v) :
    G.IsHamiltonian:=by
  classical
  let H :=G.qE
  have hle:G ≤ H:=G.rs
  have hcard:A.card ≤ Fintype.card V :=card_le_univ A
  have hcoreH (u v :V) (hu:u ∈ A) (hv:v ∈ A) (huv:u ≠ v) :
      H.Adj u v:=by
    apply G.rK huv
    change Fintype.card V ≤ H.degree u +H.degree v
    have hu':= (hcore u hu).trans (Nat.add_le_add_right (G.degree_le_of_le hle) d)
    have hv':= (hcore v hv).trans (Nat.add_le_add_right (G.degree_le_of_le hle) d)
    omega
  have hdegA (u:V) (hu:u ∈ A) : A.card ≤ H.degree u +1:=by
    apply wo H A u hu
    intro v hv hvu
    exact hcoreH u v hu hv hvu.symm
  have hcross (u v :V) (hu:u ∈ A) (hv:v ∉ A) : H.Adj u v:=by
    have huv:u ≠ v:=fun h => hv (h ▸ hu)
    apply G.rK huv
    change Fintype.card V ≤ H.degree u +H.degree v
    have hu':=hdegA u hu
    have hv':= (hout v hv).trans (G.degree_le_of_le hle)
    omega
  have hdegOut (u:V) (hu:u ∉ A) : A.card ≤ H.degree u :=by
    have hsub:A ⊆ H.neighborFinset u :=by
      intro v hv
      exact (H.mem_neighborFinset u v).mpr (hcross v u hv hu).symm
    exact card_le_card hsub
  have htop:H= ⊤ :=by
    apply top_unique
    intro u v huv
    have hne:u ≠ v:=by simpa only [top_adj] using huv
    by_cases hu:u ∈ A
    · by_cases hv:v ∈ A
      · exact hcoreH u v hu hv hne
      · exact hcross u v hu hv
    · by_cases hv:v ∈ A
      · exact (hcross v u hv hu).symm
      · apply G.rK hne
        change Fintype.card V ≤ H.degree u +H.degree v
        have hu':=hdegOut u hu
        have hv':=hdegOut v hv
        omega
  apply G.sI.mp
  change H.IsHamiltonian
  rw [htop]
  apply SimpleGraph.x3 hN
  intro v
  rw [((⊤ : SimpleGraph V).degree_eq_card_sub_one v).mpr (by simp [IsUniversal])]
  omega
theorem wS {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (v: (S:Set V)) :
    (G.induce (S:Set V)).degree v = (G.neighborFinset v.val ∩ S).card:=by
  classical
  have h :=congrArg Finset.card (G.map_neighborFinset_induce v)
  simpa only [card_map,card_neighborFinset_eq_degree,Finset.toFinset_coe,
    ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h
theorem wE {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A W :Finset V) (d:ℕ)
    (hdis:Disjoint A W) (hN:3 ≤ A.card+W.card)
    (hsize:W.card+2*d ≤ A.card)
    (hcore: ∀ v ∈ A,A.card ≤ (G.neighborFinset v ∩ A).card+d)
    (hout: ∀ v ∈ W,W.card+1 ≤ (G.neighborFinset v ∩ A).card) :
    (G.induce ((A ∪ W:Finset V) : Set V)).IsHamiltonian:=by
  classical
  let S :=A ∪ W
  let H :=G.induce (S:Set V)
  let A':Finset (S:Set V) :=univ.filter (fun v => v.val ∈ A)
  have hcard:Fintype.card (S:Set V) = A.card+W.card:=by
    calc
      Fintype.card (S:Set V) = (S:Set V).ncard:=Nat.card_eq_fintype_card.symm
      _=S.card:=Set.ncard_coe_finset S
      _=A.card+W.card:=card_union_of_disjoint hdis
  have himage:A'.image Subtype.val=A:=by
    ext v
    simp only [A',mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hv
      exact ⟨⟨v,mem_union_left W hv⟩,hv,rfl⟩
  have hAcard:A'.card=A.card:=by
    rw [← himage,card_image_of_injective _ Subtype.val_injective]
  have hdeg (v: (S:Set V)) : (G.neighborFinset v.val ∩ A).card ≤ H.degree v :=by
    rw [wS]
    apply card_le_card
    exact inter_subset_inter_left (subset_union_left:A ⊆ S)
  apply zO H A' d
  · simpa only [hcard] using hN
  · rw [hcard,hAcard]
    omega
  · intro v hv
    have hvA:v.val ∈ A:= (mem_filter.mp hv).2
    rw [hAcard]
    exact (hcore v.val hvA).trans (Nat.add_le_add_right (hdeg v) d)
  · intro v hv
    have hvA:v.val ∉ A:=by simpa only [A',mem_filter,mem_univ,true_and] using hv
    have hvW:v.val ∈ W:= (mem_union.mp v.property).resolve_left hvA
    rw [hcard,hAcard,Nat.add_sub_cancel_left]
    exact (hout v.val hvW).trans (hdeg v)
theorem sr {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A W :Finset V) (d:ℕ)
    (hdis:Disjoint A W) (hN:3 ≤ A.card+W.card)
    (hsize:W.card+2*d ≤ A.card)
    (hcore: ∀ v ∈ A,A.card ≤ (G.neighborFinset v ∩ A).card+d)
    (hout: ∀ v ∈ W,W.card+1 ≤ (G.neighborFinset v ∩ A).card) :
    ∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=A.card+W.card:=by
  classical
  let S :=A ∪ W
  have hcard:Fintype.card (S:Set V) = A.card+W.card:=by
    calc
      Fintype.card (S:Set V) = (S:Set V).ncard:=Nat.card_eq_fintype_card.symm
      _=S.card:=Set.ncard_coe_finset S
      _=A.card+W.card:=card_union_of_disjoint hdis
  have hHam: (G.induce (S:Set V)).IsHamiltonian:=
    wE G A W d hdis hN hsize hcore hout
  let:Nontrivial (S:Set V) :=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v⟩ := (inferInstance:Nonempty (S:Set V))
  obtain ⟨c,hc⟩ :=hHam.exists_isHamiltonianCycle v
  refine ⟨(Embedding.induce (S:Set V)).toHom v,
    c.map (Embedding.induce (S:Set V)).toHom,
    hc.isCycle.map Subtype.val_injective,?_⟩
  rw [Walk.length_map,hc.length_eq,hcard]
end Erdos556
end cm
section dm
namespace Erdos556
open SimpleGraph Finset
theorem a7 {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) :
    ∑ v ∈ S,(G.neighborFinset v ∩ S).card=
      2* (G.induce (S:Set V)).edgeFinset.card:=by
  classical
  rw [← (G.induce (S:Set V)).sum_degrees_eq_twice_card_edges]
  simp_rw [wS]
  exact (Finset.sum_coe_sort S (fun v => (G.neighborFinset v ∩ S).card)).symm
theorem vk {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (r:ℕ) :
    ∃ A :Finset V,A ⊆ S ∧
      r* (S.card-A.card) ≤ 2* (G.induce (S:Set V)).edgeFinset.card ∧
      ∀ v ∈ A,(G.neighborFinset v ∩ S).card ≤ r:=by
  classical
  let A :=S.filter (fun v => (G.neighborFinset v ∩ S).card ≤ r)
  have hAS:A ⊆ S:=filter_subset _ _
  refine ⟨A,hAS,?_,fun v hv=> (mem_filter.mp hv).2⟩
  have hbad (v:V) (hv:v ∈ S \ A) : r ≤ (G.neighborFinset v ∩ S).card:=by
    have hvS:= (mem_sdiff.mp hv).1
    have hvA:= (mem_sdiff.mp hv).2
    have hn: ¬ (G.neighborFinset v ∩ S).card ≤ r:=by
      intro h
      exact hvA (mem_filter.mpr ⟨hvS,h⟩)
    omega
  calc
    r* (S.card-A.card) = ∑ _v ∈ S \ A,r:=by
      rw [sum_const,smul_eq_mul,card_sdiff,inter_eq_left.mpr hAS,Nat.mul_comm]
    _ ≤ ∑ v ∈ S \ A,(G.neighborFinset v ∩ S).card:=sum_le_sum hbad
    _ ≤ ∑ v ∈ S,(G.neighborFinset v ∩ S).card:=
      sum_le_sum_of_subset sdiff_subset
    _=2* (G.induce (S:Set V)).edgeFinset.card:=a7 G S
theorem r1 {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (v:V) (hv:v ∈ S) :
    (G.neighborFinset v ∩ S).card+ (Gᶜ.neighborFinset v ∩ S).card+1=S.card:=by
  classical
  have hdis:Disjoint (G.neighborFinset v ∩ S) (Gᶜ.neighborFinset v ∩ S) :=by
    apply Finset.disjoint_left.mpr
    intro u hu huc
    have h := (G.mem_neighborFinset v u).mp (mem_inter.mp hu).1
    have hc:= (Gᶜ.mem_neighborFinset v u).mp (mem_inter.mp huc).1
    exact (show ¬ G.Adj v u from hc.2) h
  have hunion: (G.neighborFinset v ∩ S) ∪ (Gᶜ.neighborFinset v ∩ S) = S.erase v :=by
    ext u
    simp only [mem_union,mem_inter,mem_neighborFinset,compl_adj,mem_erase]
    constructor
    · rintro (⟨h,hu⟩ | ⟨⟨h,_⟩,hu⟩)
      · exact ⟨h.ne.symm,hu⟩
      · exact ⟨h.symm,hu⟩
    · rintro ⟨huv,hu⟩
      by_cases h :G.Adj v u
      · exact Or.inl ⟨h,hu⟩
      · exact Or.inr ⟨⟨huv.symm,h⟩,hu⟩
  have h :=congrArg Finset.card hunion
  rw [card_union_of_disjoint hdis,card_erase_of_mem hv] at h
  have hp:=card_pos.mpr ⟨v,hv⟩
  omega
theorem sL {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A S :Finset V) (r:ℕ)
    (hAS:A ⊆ S) (hclean: ∀ v ∈ A,(Gᶜ.neighborFinset v ∩ S).card ≤ r) :
    ∀ v ∈ A,A.card ≤ (G.neighborFinset v ∩ A).card+ (r+1) :=by
  intro v hv
  have h :=r1 G A v hv
  have hle: (Gᶜ.neighborFinset v ∩ A).card ≤ r:=
    (card_le_card (inter_subset_inter_left hAS)).trans (hclean v hv)
  omega
end Erdos556
end dm
section dH
namespace Erdos556
open SimpleGraph Finset
theorem uN {V:Type*} [Finite V]
    (G:SimpleGraph V) (S:Finset V) (n:ℕ) (hn:8 ≤ n)
    (hno: ¬ cycleGraph n ⊑ G) :
    n*S.card ≤ n*n+16*Nat.card (Gᶜ.induce (S:Set V)).edgeSet:=by
  classical
  let:=Fintype.ofFinite V
  let q :=n/4
  obtain ⟨A,hAS,hbad,hclean⟩ :=vk Gᶜ S q
  have hAn:A.card < n:=by
    by_contra hlarge
    obtain ⟨C,hCA,hCc⟩ :=exists_subset_card_eq (show n ≤ A.card by omega)
    have hCS:C ⊆ S:=hCA.trans hAS
    have hCcore: ∀ v ∈ C,C.card ≤ (G.neighborFinset v ∩ C).card+ (q+1) :=
      sL G C S q hCS (fun v hv=> hclean v (hCA hv))
    obtain ⟨v,c,hc,hlen⟩ :=sr G C ∅ (q+1)
      (by simp) (by simp only [card_empty,add_zero,hCc];omega)
      (by simp only [card_empty,zero_add,hCc];dsimp only [q];omega) hCcore
      (by intro v hv;simp at hv)
    apply hno
    apply (cycleGraph_isContained_iff (by omega:2 < n)).mpr
    exact ⟨v,c,hc,by simpa only [card_empty,add_zero,hCc] using hlen⟩
  have hq:n ≤ 8*q:=by dsimp only [q];omega
  have hloss:=Nat.mul_le_mul_right (S.card-A.card) hq
  rw [q7] at hbad
  have hNl:n* (S.card-A.card) ≤ 16*Nat.card (Gᶜ.induce (S:Set V)).edgeSet:=by
    nlinarith only [hloss,hbad]
  have hAc:=card_le_card hAS
  have hsum:=Nat.sub_add_cancel hAc
  have hAn':=Nat.mul_le_mul_left n hAn.le
  nlinarith only [hNl,hsum,hAn']
end Erdos556
end dH
section dC
namespace Erdos556
open SimpleGraph Finset
theorem q2.t5 {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D)
    (n:ℕ) (hn:8 ≤ n) (hno: ∀ i,¬ cycleGraph n ⊑ c.graph i)
    (p:q1) (hp:q3 p =1) :
    (n:ℝ) * (h.qa p).card ≤ (n:ℝ) ^ 2+48*E:=by
  classical
  obtain ⟨i,hi,huniq⟩ :=xm p hp
  let S :=h.qa p
  have hsub: (c.graph i)ᶜ.induce (S:Set V) ≤ h.missing.induce (S:Set V) :=by
    intro u v huv
    exact h.w4 p i huniq u.val v.val u.property v.property huv
  have hwrong:Nat.card ((c.graph i)ᶜ.induce (S:Set V)).edgeSet ≤ Nat.card h.missing.edgeSet:=
    (zW _ _ hsub).trans (t2 h.missing S)
  have hbound:=uN (c.graph i) S n hn (hno i)
  have hboundR: (n:ℝ) * S.card ≤ (n:ℝ) ^ 2+
      16* (Nat.card ((c.graph i)ᶜ.induce (S:Set V)).edgeSet:ℝ) :=by
    rw [pow_two]
    exact_mod_cast hbound
  have hwrongR: (Nat.card ((c.graph i)ᶜ.induce (S:Set V)).edgeSet:ℝ) ≤
      Nat.card h.missing.edgeSet:=by exact_mod_cast hwrong
  have hmissing:=h.v9
  change (n:ℝ) * S.card ≤ (n:ℝ) ^ 2+48*E
  linarith
end Erdos556
end dC
section d7
namespace Erdos556
open Finset
def qQ (x y :q1 → ℝ) : ℝ:=
  ∑ p,∑ q,qb p q*x p*y q
def u0 (x:q1 → ℝ) : ℝ:=
  ∑ p,(q3 p :ℝ) * x p
theorem yO (w:q1 → ℝ) :
    qd w =qQ w w-u0 w :=rfl
theorem tD (x y z:q1 → ℝ) :
    qQ (x+y) z =qQ x z+qQ y z:=by
  simp only [qQ,Pi.add_apply,mul_add,add_mul,sum_add_distrib]
theorem x4 (x y z:q1 → ℝ) :
    qQ x (y+z) = qQ x y+qQ x z:=by
  simp only [qQ,Pi.add_apply,mul_add,sum_add_distrib]
theorem aD (x y :q1 → ℝ) : qQ x y=qQ y x:=by
  rw [qQ,sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  rw [sm q p]
  ring
theorem u3 (x:q1 → ℝ) (p:q1) (t:ℝ) :
    qQ (Pi.single p t) x =t* ∑ q,qb p q*x q:=by
  classical
  simp [qQ,Pi.single_apply,mul_ite,mul_sum,mul_comm,mul_left_comm]
theorem ym (x:q1 → ℝ) (p:q1) (t:ℝ) :
    qQ x (Pi.single p t) = t* ∑ q,qb p q*x q:=by
  rw [aD,u3]
theorem yb (p:q1) (s t :ℝ) :
    qQ (Pi.single p s) (Pi.single p t) = s*t:=by
  classical
  rw [u3]
  simp [Pi.single_apply,mul_ite,vU]
theorem dd (x y :q1 → ℝ) : u0 (x+y) = u0 x +u0
    y:=by
  simp only [u0,Pi.add_apply,mul_add,sum_add_distrib]
theorem aA (p:q1) (t:ℝ) :
    u0 (Pi.single p t) = q3 p *t:=by
  classical
  simp [u0,Pi.single_apply,mul_ite]
theorem rI (w:q1 → ℝ) (p:q1) (t:ℝ) :
    qd (w+Pi.single p t) = qd w +t*qm w p+t^2:=by
  simp only [yO]
  rw [tD,x4,x4,
    ym,u3,yb,
    dd,aA]
  dsimp [qm]
  ring
theorem uk (w:q1 → ℝ) (p q :q1) (t:ℝ) :
    qm (w+Pi.single p t) q =qm w q+2*t*qb q p:=by
  classical
  simp only [qm,Pi.add_apply,mul_add,sum_add_distrib]
  have hsum: (∑ r,qb q r* (Pi.single p t:q1 → ℝ) r) = qb q p*t
    :=by
    simp [Pi.single_apply,mul_ite]
  rw [hsum]
  ring
end Erdos556
end d7
section dl
namespace Erdos556
def up (w:q1 → ℝ) (p q :q1) (t:ℝ) : q1 → ℝ:=
  (w+Pi.single p t) + Pi.single q (-t)
def qx (w:q1 → ℝ) (p q :q1) : q1 → ℝ:=
  up w p q (w q)
theorem xT (w:q1 → ℝ) (p q :q1) (t:ℝ)
    (hpq:qb p q=1) :
    qd (up w p q t) = qd w +t* (qm w p-qm w q) :=by
  rw [up,rI,rI,uk,
    sm q p,hpq]
  ring
theorem zl (w:q1 → ℝ) (p q :q1) (t:ℝ)
    (hpq:qb p q=1) :
    qm (up w p q t) p -qm (up w p q t) q =
      qm w p-qm w q:=by
  simp only [up,uk,vU,
    sm q p,hpq]
  ring
theorem uG (w:q1 → ℝ) (p q :q1) (hpq:p ≠ q) :
    qx w p q q=0:=by
  classical
  simp [qx,up,Ne.symm hpq]
theorem uH (w:q1 → ℝ) (p q :q1) (hpq:p ≠ q) :
    qx w p q p=w p+w q:=by
  classical
  simp [qx,up,hpq]
theorem rL (w:q1 → ℝ) (p q r:q1)
    (hrp:r ≠ p) (hrq:r ≠ q) : qx w p q r=w r:=by
  classical
  simp [qx,up,hrp,hrq]
theorem si (w:q1 → ℝ) (p q :q1)
    (hp:0 ≤ w p) (hq:0 ≤ w q) (hpq:qb p q=1) :
    qd (qx w p q) ≤ qd w ∨
      qd (qx w q p) ≤ qd w :=by
  by_cases hgrad:qm w p ≤ qm w q
  · left
    rw [qx,xT w p q (w q) hpq]
    have h :=mul_nonpos_of_nonneg_of_nonpos hq (sub_nonpos.mpr hgrad)
    linarith
  · right
    have hqp:qb q p=1:= (sm q p).trans hpq
    rw [qx,xT w q p (w p) hqp]
    have h :=mul_nonpos_of_nonneg_of_nonpos hp (by linarith:qm w q-qm w
      p ≤ 0)
    linarith
end Erdos556
end dl
section cE
namespace Erdos556
open Finset
theorem e1 (w:q1 → ℝ) (p q :q1) (t:ℝ) :
    (∑ r,up w p q t r) = ∑ r,w r:=by
  classical
  simp [up,Pi.add_apply,sum_add_distrib]
theorem v0 {w:q1 → ℝ} {p q r:q1}
    (hpq:p ≠ q) (hp:0 < w p) (hr:0 < qx w p q r) : 0 < w r :=by
  by_cases hrp:r=p
  · exact hrp ▸ hp
  by_cases hrq:r=q
  · rw [hrq,uG w p q hpq] at hr
    exact hr.false.elim
  · rwa [rL w p q r hrp hrq] at hr
theorem q6.transfer {w:q1 → ℝ} (hw:q6 w)
    (p q :q1) (hpq:p ≠ q) (hp:0 < w p)
    (hpdim:2 ≤ q3 p) (hqdim:2 ≤ q3 q) :
    q6 (qx w p q) :=by
  constructor
  · intro r
    by_cases hrp:r=p
    · rw [hrp,uH w p q hpq]
      exact add_nonneg (hw.nonneg p) (hw.nonneg q)
    by_cases hrq:r=q
    · rw [hrq,uG w p q hpq]
    · rw [rL w p q r hrp hrq]
      exact hw.nonneg r
  · rw [qx,e1]
    exact hw.sum_four
  · intro r hr
    have hrp:r ≠ p:=by intro h;subst r;omega
    have hrq:r ≠ q:=by intro h;subst r;omega
    rw [rL w p q r hrp hrq]
    exact hw.vertex_zero r hr
  · intro r hr
    have hrp:r ≠ p:=by intro h;subst r;omega
    have hrq:r ≠ q:=by intro h;subst r;omega
    rw [rL w p q r hrp hrq]
    exact hw.edge_le_one r hr
  · intro r s hr hs
    exact hw.compatible r s (v0 hpq hp hr)
      (v0 hpq hp hs)
open scoped Classical in
noncomputable def qe (w:q1 → ℝ) : Finset q1:=
  univ.filter (fun p => 2 ≤ q3 p ∧ 0 < w p)
theorem za {w:q1 → ℝ} (hw:q6 w)
    (p q :q1) (hpq:p ≠ q) (hp:0 < w p)
    (hpdim:2 ≤ q3 p) :
    qe (qx w p q) = (qe w).erase q :=by
  classical
  ext r
  simp only [qe,mem_filter,mem_univ,true_and,mem_erase]
  by_cases hrp:r=p
  · subst r
    rw [uH w p q hpq]
    have hpos:0 < w p+w q:=add_pos_of_pos_of_nonneg hp (hw.nonneg q)
    exact ⟨fun _ => ⟨hpq,hpdim,hp⟩,fun _ => ⟨hpdim,hpos⟩⟩
  by_cases hrq:r=q
  · subst r
    rw [uG w p q hpq]
    simp
  · rw [rL w p q r hrp hrq]
    exact ⟨fun h => ⟨hrq,h⟩,fun h => h.2⟩
theorem rh {w:q1 → ℝ} (hw:q6 w)
    (p q :q1) (hpq:p ≠ q) (hp:0 < w p) (hq:0 < w q)
    (hpdim:2 ≤ q3 p) (hqdim:2 ≤ q3 q) :
    (qe (qx w p q)).card < (qe w).card:=by
  classical
  rw [za hw p q hpq hp hpdim]
  exact card_erase_lt_of_mem (mem_filter.mpr ⟨mem_univ q,hqdim,hq⟩)
end Erdos556
end cE
section bq
namespace Erdos556
open Finset
theorem yW (w:q1 → ℝ) (hw:q6 w) :
    ∃ v :q1 → ℝ,q6 v ∧
      (qe v :Set q1).Pairwise
        (fun p q=> Disjoint (q0 p) (q0 q)) ∧
      qd v ≤ qd w :=by
  classical
  have aux: ∀ M:ℕ,∀ w:q1 → ℝ,q6 w →
      (qe w).card=M →
      ∃ v :q1 → ℝ,q6 v ∧
        (qe v :Set q1).Pairwise
          (fun p q=> Disjoint (q0 p) (q0 q)) ∧
        qd v ≤ qd w :=by
    intro M
    induction M using Nat.strong_induction_on with
    | h M ih=>
        intro w hw hM
        by_cases hdisj: (qe w :Set q1).Pairwise
            (fun p q=> Disjoint (q0 p) (q0 q))
        · exact ⟨w,hw,hdisj,le_rfl⟩
        simp only [Set.Pairwise] at hdisj
        push Not at hdisj
        obtain ⟨p,hpH,q,hqH,hpq,hnot⟩ :=hdisj
        have hpdim:= (mem_filter.mp hpH).2.1
        have hqdim:= (mem_filter.mp hqH).2.1
        have hp:= (mem_filter.mp hpH).2.2
        have hq:= (mem_filter.mp hqH).2.2
        have hover:qb p q=1:=by simp only [qb,if_neg hnot]
        have step (x:q1 → ℝ) (hx:q6 x)
            (hxc: (qe x).card < (qe w).card)
            (hxe:qd x ≤ qd w) :
            ∃ v :q1 → ℝ,q6 v ∧
              (qe v :Set q1).Pairwise
                (fun p q=> Disjoint (q0 p) (q0 q)) ∧
              qd v ≤ qd w :=by
          obtain ⟨v,hv,hvd,hve⟩ :=ih (qe x).card (by omega) x hx rfl
          exact ⟨v,hv,hvd,hve.trans hxe⟩
        rcases si w p q (hw.nonneg p) (hw.nonneg q) hover with
          hE | hE
        · exact step (qx w p q) (hw.transfer p q hpq hp hpdim hqdim)
            (rh hw p q hpq hp hq hpdim hqdim) hE
        · exact step (qx w q p) (hw.transfer q p hpq.symm hq hqdim hpdim)
            (rh hw q p hpq.symm hq hp hqdim hpdim) hE
  exact aux (qe w).card w hw rfl
end Erdos556
end bq
section bS
namespace Erdos556
open Finset
theorem ws (x:q1 → ℝ)
    (hzero: ∀ p q,p ≠ q → qb p q*x p*x q=0) :
    qQ x x= ∑ p,x p^2:=by
  unfold qQ
  apply sum_congr rfl
  intro p _
  rw [sum_eq_single p]
  · rw [vU]
    ring
  · intro q _ hqp
    exact hzero p q hqp.symm
  · intro hp
    exact (hp (mem_univ p)).elim
theorem vB (x:q1 → ℝ) (S:Finset q1)
    (hsupport: ∀ p,p ∉ S → x p=0)
    (hdim: ∀ p ∈ S,q3 p =1)
    (hdisj: (S:Set q1).Pairwise (fun p q=> Disjoint (q0 p)
      (q0 q))) :
    qd x = (∑ p ∈ S,x p^2) - ∑ p ∈ S,x p:=by
  classical
  have hzero (p q :q1) (hpq:p ≠ q) : qb p q*x p*x q=0:=by
    by_cases hp:p ∈ S
    · by_cases hq:q ∈ S
      · simp only [qb,if_pos (hdisj hp hq hpq),zero_mul]
      · rw [hsupport q hq,mul_zero]
    · rw [hsupport p hp,mul_zero,zero_mul]
  have hsq: (∑ p,x p^2) = ∑ p ∈ S,x p^2:=by
    symm
    apply sum_subset (subset_univ S)
    intro p _ hp
    rw [hsupport p hp]
    norm_num
  have hlin:u0 x = ∑ p ∈ S,x p:=by
    calc
      u0 x = ∑ p ∈ S,(q3 p :ℝ) * x p :=by
        symm
        apply sum_subset (subset_univ S)
        intro p _ hp
        rw [hsupport p hp,mul_zero]
      _= ∑ p ∈ S,x p:=by
        apply sum_congr rfl
        intro p hp
        rw [hdim p hp]
        norm_num
  rw [yO,ws x hzero,hsq,hlin]
theorem tE (p:q1) : qb qF p =1:=by
  have hfull:q0 qF=univ:=by decide
  have hnon: (q0 p).Nonempty:=by
    apply card_pos.mp
    rw [qU]
    positivity
  have hnot: ¬ Disjoint (q0 qF) (q0 p) :=by
    intro hd
    obtain ⟨v,hv⟩ :=hnon
    exact Finset.disjoint_left.mp hd (by rw [hfull];exact mem_univ v) hv
  simp only [qb,if_neg hnot]
theorem xg (x:q1 → ℝ) :
    qm x qF=2* (∑ p,x p) - 3:=by
  simp only [qm,tE,one_mul,zx,Nat.cast_ofNat]
end Erdos556
end bS
section b4
namespace Erdos556
open Finset
theorem wT {I:Type*} (S:Finset I) (f:I → ℝ)
    (m:ℕ) (hcard:S.card ≤ m) :
    (∑ i ∈ S,f i) ^ 2 ≤ (m:ℝ) * ∑ i ∈ S,f i^2:=by
  have h :=sum_mul_sq_le_sq_mul_sq S f (fun _ => (1:ℝ))
  have h': (∑ i ∈ S,f i) ^ 2 ≤ (S.card:ℝ) * ∑ i ∈ S,f i^2:=by
    simpa only [mul_one,one_pow,sum_const,nsmul_eq_mul,mul_one,mul_comm] using h
  apply h'.trans
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
  exact sum_nonneg fun i _=> sq_nonneg (f i)
theorem zC {I:Type*} (S:Finset I) (f:I → ℝ)
    (hf: ∀ i ∈ S,f i ≤ 1) : (∑ i ∈ S,f i) ≤ S.card:=by
  calc
    (∑ i ∈ S,f i) ≤ ∑ _i ∈ S,(1:ℝ) :=sum_le_sum hf
    _=S.card:=by simp
theorem uB {I:Type*} (S:Finset I) (f:I → ℝ)
    (m:ℕ) (hcard:S.card ≤ m) (hf: ∀ i ∈ S,f i ≤ 1)
    (hsum: ∑ i ∈ S,f i= (m:ℝ)) : S.card=m ∧ ∀ i ∈ S,f i=1:=by
  have hcR: (m:ℝ) ≤ S.card:=by rw [← hsum];exact zC S f hf
  have hc:S.card=m:=by exact_mod_cast le_antisymm (by exact_mod_cast hcard) hcR
  refine ⟨hc,?_⟩
  intro i hi
  by_contra hne
  have hlt: (∑ j ∈ S,f j) < ∑ _j ∈ S,(1:ℝ) :=
    sum_lt_sum hf ⟨i,hi,lt_of_le_of_ne (hf i hi) hne⟩
  simp only [hsum,sum_const,nsmul_eq_mul,mul_one,hc,lt_self_iff_false] at hlt
theorem q6.aB {w:q1 → ℝ} (hw:q6 w) :
    (∑ p ∈ ql w,w p) ^ 2 ≤ 4* ∑ p ∈ ql w,w p^2:=by
  exact wT (ql w) w 4 hw.vl
end Erdos556
end b4
section aY
namespace Erdos556
theorem a8 (z E S:ℝ) (hz:0 ≤ z) (hE:0 ≤ E)
    (htotal:E+z=4) (hS:E^2 ≤ 4*S) :
    z ≤ z^2+2*z*E+S-E-3*z:=by
  have hzE:0 ≤ z*E:=mul_nonneg hz hE
  nlinarith
theorem xZ (y₀ y₁ E₀ E₁ S₀ S₁:ℝ)
    (hE₀:0 ≤ E₀) (hE₀':E₀ ≤ 2) (hE₁:0 ≤ E₁) (hE₁':E₁ ≤ 2)
    (hS₀:E₀^2 ≤ 2*S₀) (hS₁:E₁^2 ≤ 2*S₁)
    (htotal:y₀+E₀+y₁+E₁=4) :
    0 ≤ y₀^2+2*y₀*E₀+S₀-2*y₀-E₀+
      (y₁^2+2*y₁*E₁+S₁-2*y₁-E₁) :=by
  have hprod₀:=mul_nonneg hE₀ (sub_nonneg.mpr hE₀')
  have hprod₁:=mul_nonneg hE₁ (sub_nonneg.mpr hE₁')
  have hs₀:=sq_nonneg (y₀+E₀-2)
  have hs₁:=sq_nonneg (y₁+E₁-2)
  nlinarith
theorem y5 (y₀ y₁ E₀ E₁ S₀ S₁:ℝ)
    (hE₀:0 ≤ E₀) (hE₀':E₀ ≤ 2) (hE₁:0 ≤ E₁) (hE₁':E₁ ≤ 2)
    (hS₀:E₀^2 ≤ 2*S₀) (hS₁:E₁^2 ≤ 2*S₁)
    (htotal:y₀+E₀+y₁+E₁=4)
    (hzero:y₀^2+2*y₀*E₀+S₀-2*y₀-E₀+
      (y₁^2+2*y₁*E₁+S₁-2*y₁-E₁) = 0) :
    y₀+E₀=2 ∧ y₁+E₁=2 ∧ (E₀=0 ∨ E₀=2) ∧ (E₁=0 ∨ E₁=2) :=by
  have hprod₀:=mul_nonneg hE₀ (sub_nonneg.mpr hE₀')
  have hprod₁:=mul_nonneg hE₁ (sub_nonneg.mpr hE₁')
  have hs₀:=sq_nonneg (y₀+E₀-2)
  have hs₁:=sq_nonneg (y₁+E₁-2)
  have hL₀:y₀+E₀=2:=by nlinarith
  have hL₁:y₁+E₁=2:=by nlinarith
  have hE₀zero:E₀* (2-E₀) = 0:=by nlinarith
  have hE₁zero:E₁* (2-E₁) = 0:=by nlinarith
  refine ⟨hL₀,hL₁,?_,?_⟩
  · rcases mul_eq_zero.mp hE₀zero with h | h
    · exact Or.inl h
    · right;linarith
  · rcases mul_eq_zero.mp hE₁zero with h | h
    · exact Or.inl h
    · right;linarith
end Erdos556
end aY
section be
namespace Erdos556
open Finset
theorem q6.u6 {w:q1 → ℝ}
    (hw:q6 w)
    (hhigh: ∀ p,2 ≤ q3 p → p ≠ qF → w p =0) :
    w qF ≤ qd w :=by
  classical
  let E :=ql w
  let x (p:q1) : ℝ:=if p =qF then 0 else w p
  have hx (p:q1) (hp:p ∈ E) : x p =w p:=by
    have hd:= (mem_filter.mp hp).2.1
    have hne:p ≠ qF:=by intro h;subst p;rw [zx] at hd;omega
    exact if_neg hne
  have hzero (p:q1) (hp:p ∉ E) : x p =0:=by
    by_cases hpc:p=qF
    · exact if_pos hpc
    rw [show x p=w p from if_neg hpc]
    by_cases hd0:q3 p =0
    · exact hw.vertex_zero p hd0
    by_cases hd1:q3 p =1
    · have hnot: ¬ 0 < w p:=fun h => hp (mem_filter.mpr ⟨mem_univ p,hd1,h⟩)
      exact le_antisymm (le_of_not_gt hnot) (hw.nonneg p)
    · exact hhigh p (by omega) hpc
  have hdecomp:w=x+Pi.single qF (w qF) :=by
    funext p
    by_cases hpc:p=qF
    · subst p
      simp [x]
    · simp [x,hpc]
  have hsum: (∑ p,x p) = ∑ p ∈ E,w p:=by
    calc
      (∑ p,x p) = ∑ p ∈ E,x p:=by
        symm
        exact sum_subset (subset_univ E) (fun p _ hp=> hzero p hp)
      _= ∑ p ∈ E,w p:=sum_congr rfl hx
  have henergy:qd x = (∑ p ∈ E,w p^2) - ∑ p ∈ E,w p:=by
    rw [vB x E hzero (fun p hp=> (mem_filter.mp hp).2.1)
      hw.s0]
    congr 1
    · exact sum_congr rfl (fun p hp=> congrArg (fun a :ℝ=> a ^2) (hx p hp))
    · exact sum_congr rfl hx
  have htotal: (∑ p ∈ E,w p) + w qF=4:=by
    calc
      (∑ p ∈ E,w p) + w qF= (∑ p,x p) + w qF:=by rw [hsum]
      _= ∑ p,((x+Pi.single qF (w qF)) : q1 → ℝ) p :=by
        simp [Pi.add_apply,sum_add_distrib]
      _= ∑ p,w p:=congrArg (fun f :q1 → ℝ=> ∑ p,f p) hdecomp.symm
      _=4:=hw.sum_four
  have hfull:qd w = (∑ p ∈ E,w p^2) - (∑ p ∈ E,w p) +
      w qF* (2* (∑ p ∈ E,w p) - 3) + (w qF) ^ 2:=by
    calc
      qd w =qd (x+Pi.single qF (w qF)) :=congrArg qd
        hdecomp
      _=_:=by rw [rI,henergy,xg,hsum]
  have hbound:=a8 (w qF) (∑ p ∈ E,w p) (∑ p ∈ E,w p^2)
    (hw.nonneg qF) (sum_nonneg fun p _=> hw.nonneg p) htotal hw.aB
  rw [hfull]
  nlinarith only [hbound]
end Erdos556
end be
section aZ
namespace Erdos556
open Finset
theorem z4: ∀ (i:Fin 3) (b:Bool),cubeFace i b ≠ cubeFace i (!b) :=by
  decide
theorem se: ∀ (i:Fin 3) (b:Bool) (p:q1),
    q3 p =1 →
    (q0 p ∩ q0 (cubeFace i b)).card ≠ 1 →
    q0 p ⊆ q0 (cubeFace i b) ∨
      q0 p ⊆ q0 (cubeFace i (!b)) :=by
  decide
theorem ta: ∀ (i:Fin 3) (b:Bool) (p:q1),
    q3 p =1 →
    ¬ (q0 p ⊆ q0 (cubeFace i b) ∧
      q0 p ⊆ q0 (cubeFace i (!b))) :=by
  decide
theorem tC {p q :q1} (hsub:q0 q ⊆ q0 p) :
    qb p q=1:=by
  have hnon: (q0 q).Nonempty:=by
    apply card_pos.mp
    rw [qU]
    positivity
  have hnot: ¬ Disjoint (q0 p) (q0 q) :=by
    intro h
    obtain ⟨v,hv⟩ :=hnon
    exact Finset.disjoint_left.mp h (hsub hv) hv
  simp only [qb,if_neg hnot]
theorem zZ (i:Fin 3) (b:Bool) :
    qb (cubeFace i b) (cubeFace i (!b)) = 0:=by
  have hb:b ≠ !b:=by cases b <;> decide
  have hdisj:= (ui i i b (!b)).mpr ⟨rfl,hb⟩
  simp only [qb,if_pos hdisj]
theorem we (i:Fin 3) (b:Bool) (p:q1)
    (hsub:q0 p ⊆ q0 (cubeFace i (!b))) :
    qb (cubeFace i b) p =0:=by
  have hb:b ≠ !b:=by cases b <;> decide
  have hdisj:= ((ui i i b (!b)).mpr ⟨rfl,hb⟩).mono_right hsub
  simp only [qb,if_pos hdisj]
end Erdos556
end aZ
section aQ
namespace Erdos556
open Finset
noncomputable def qf (w:q1 → ℝ) (i:Fin 3) (b:Bool) :
    Finset q1:=
  (ql w).filter (fun p => q0 p ⊆ q0 (cubeFace i b))
theorem ut (w:q1 → ℝ) (i:Fin 3) (b:Bool) :
    qf w i b ⊆ ql w :=filter_subset _ _
theorem q6.uL {w:q1 → ℝ} (hw:q6 w)
    (i:Fin 3) (b:Bool) : (qf w i b).card ≤ 2:=by
  have h :=vh (qf w i b) (q0 (cubeFace i b))
    (fun p hp=> (mem_filter.mp (mem_filter.mp hp).1).2.1)
    (hw.s0.mono (ut w i b))
    (fun p hp=> (mem_filter.mp hp).2)
  rw [qU,r4] at h
  norm_num at h
  omega
theorem w0 (w:q1 → ℝ) (i:Fin 3) (b:Bool) :
    Disjoint (qf w i b) (qf w i (!b)) :=by
  rw [Finset.disjoint_left]
  intro p hp hq
  have hd:= (mem_filter.mp (mem_filter.mp hp).1).2.1
  exact ta i b p hd ⟨(mem_filter.mp hp).2,(mem_filter.mp hq).2⟩
theorem xc {w:q1 → ℝ} (hw:q6 w)
    (i:Fin 3) (b:Bool) (hb:0 < w (cubeFace i b)) :
    qf w i b ∪ qf w i (!b) = ql w :=by
  apply Subset.antisymm
  · exact union_subset (ut w i b) (ut w i (!b))
  · intro p hp
    have hd:= (mem_filter.mp hp).2.1
    have hwpos:= (mem_filter.mp hp).2.2
    rcases se i b p hd (hw.compatible p (cubeFace i b) hwpos hb) with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hp,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,h⟩)
theorem q6.ud {w:q1 → ℝ} (hw:q6 w)
    (i:Fin 3) (b:Bool) : (∑ p ∈ qf w i b,w p) ≤ 2:=by
  apply (zC (qf w i b) w ?_).trans
  · exact_mod_cast hw.uL i b
  · intro p hp
    exact hw.edge_le_one p (mem_filter.mp (mem_filter.mp hp).1).2.1
theorem q6.sf {w:q1 → ℝ} (hw:q6 w)
    (i:Fin 3) (b:Bool) :
    (∑ p ∈ qf w i b,w p) ^ 2 ≤ 2* ∑ p ∈ qf w i b,w p^2:=
  wT (qf w i b) w 2 (hw.uL i b)
theorem sG (w x :q1 → ℝ) (i:Fin 3) (b:Bool)
    (hx: ∀ p ∈ ql w,x p=w p)
    (hzero: ∀ p,p ∉ ql w → x p=0)
    (hpart: ∀ p ∈ ql w,
      q0 p ⊆ q0 (cubeFace i b) ∨
        q0 p ⊆ q0 (cubeFace i (!b))) :
    qm x (cubeFace i b) = 2* (∑ p ∈ qf w i b,w p) - 2:=by
  classical
  have hsum: (∑ p,qb (cubeFace i b) p *x p) = ∑ p ∈ qf w i b,w p:=by
    calc
      (∑ p,qb (cubeFace i b) p *x p) =
          ∑ p ∈ ql w,qb (cubeFace i b) p *x p:=by
        symm
        apply sum_subset (subset_univ _)
        intro p _ hp
        rw [hzero p hp,mul_zero]
      _= ∑ p ∈ qf w i b,w p:=by
        rw [qf,sum_filter]
        apply sum_congr rfl
        intro p hp
        rw [hx p hp]
        by_cases hsub:q0 p ⊆ q0 (cubeFace i b)
        · rw [if_pos hsub,tC hsub,one_mul]
        · rw [if_neg hsub,
            we i b p ((hpart p hp).resolve_left hsub),zero_mul]
  simp only [qm,hsum,r4,Nat.cast_ofNat]
end Erdos556
end aQ
section bo
namespace Erdos556
open Finset
theorem q6.sQ {w:q1 → ℝ}
    (hw:q6 w) (i:Fin 3) (b:Bool) (hface:0 < w (cubeFace i b))
    (hhigh: ∀ r,2 ≤ q3 r → r ≠ cubeFace i b → r ≠ cubeFace i (!b) → w r =0) :
    0 ≤ qd w ∧ (qd w =0 →
      w (cubeFace i b) + (∑ r ∈ qf w i b,w r) = 2 ∧
      w (cubeFace i (!b)) + (∑ r ∈ qf w i (!b),w r) = 2 ∧
      ((∑ r ∈ qf w i b,w r) = 0 ∨ (∑ r ∈ qf w i b,w r) = 2) ∧
      ((∑ r ∈ qf w i (!b),w r) = 0 ∨
        (∑ r ∈ qf w i (!b),w r) = 2)) :=by
  classical
  let p :=cubeFace i b
  let q :=cubeFace i (!b)
  have hpq:p ≠ q:=z4 i b
  let E :=ql w
  let x (r:q1) : ℝ:=if r =p ∨ r=q then 0 else w r
  have hx (r:q1) (hr:r ∈ E) : x r =w r:=by
    have hd:= (mem_filter.mp hr).2.1
    have hrp:r ≠ p:=by
      intro h
      subst r
      change q3 (cubeFace i b) = 1 at hd
      rw [r4] at hd
      omega
    have hrq:r ≠ q:=by
      intro h
      subst r
      change q3 (cubeFace i (!b)) = 1 at hd
      rw [r4] at hd
      omega
    exact if_neg (not_or.mpr ⟨hrp,hrq⟩)
  have hzero (r:q1) (hr:r ∉ E) : x r =0:=by
    by_cases hfaces:r=p ∨ r=q
    · exact if_pos hfaces
    rw [show x r=w r from if_neg hfaces]
    by_cases hd0:q3 r =0
    · exact hw.vertex_zero r hd0
    by_cases hd1:q3 r =1
    · have hn: ¬ 0 < w r:=fun h => hr (mem_filter.mpr ⟨mem_univ r,hd1,h⟩)
      exact le_antisymm (le_of_not_gt hn) (hw.nonneg r)
    · exact hhigh r (by omega) (not_or.mp hfaces).1 (not_or.mp hfaces).2
  have hdecomp:w= (x+Pi.single p (w p)) + Pi.single q (w q) :=by
    funext r
    by_cases hrp:r=p
    · subst r
      simp [x,hpq]
    by_cases hrq:r=q
    · subst r
      simp [x,Ne.symm hpq]
    · simp [x,hrp,hrq]
  have hsum: (∑ r,x r) = ∑ r ∈ E,w r:=by
    calc
      (∑ r,x r) = ∑ r ∈ E,x r:=by
        symm
        exact sum_subset (subset_univ E) (fun r _ hr=> hzero r hr)
      _= ∑ r ∈ E,w r:=sum_congr rfl hx
  have henergy:qd x = (∑ r ∈ E,w r^2) - ∑ r ∈ E,w r:=by
    rw [vB x E hzero (fun r hr=> (mem_filter.mp hr).2.1)
      hw.s0]
    congr 1
    · exact sum_congr rfl (fun r hr=> congrArg (fun a :ℝ=> a ^2) (hx r hr))
    · exact sum_congr rfl hx
  let E₀:= ∑ r ∈ qf w i b,w r
  let E₁:= ∑ r ∈ qf w i (!b),w r
  let S₀:= ∑ r ∈ qf w i b,w r^2
  let S₁:= ∑ r ∈ qf w i (!b),w r^2
  have hsplit: (∑ r ∈ E,w r) = E₀+E₁:=by
    dsimp only [E]
    rw [← xc hw i b hface,sum_union (w0 w i b)]
  have hsplitSq: (∑ r ∈ E,w r^2) = S₀+S₁:=by
    dsimp only [E]
    rw [← xc hw i b hface,sum_union (w0 w i b)]
  have hpart (r:q1) (hr:r ∈ E) :
      q0 r ⊆ q0 p ∨ q0 r ⊆ q0 q :=
    se i b r (mem_filter.mp hr).2.1
      (hw.compatible r p (mem_filter.mp hr).2.2 hface)
  have hgrad₀:qm x p=2*E₀-2:=
    sG w x i b hx hzero hpart
  have hgrad₁:qm x q=2*E₁-2:=by
    apply sG w x i (!b) hx hzero
    intro r hr
    simpa only [Bool.not_not] using (hpart r hr).symm
  have htotal:w p+E₀+w q+E₁=4:=by
    have ht: (∑ r,x r) + w p +w q=4:=by
      calc
        (∑ r,x r) + w p +w q=
            ∑ r,(((x+Pi.single p (w p)) + Pi.single q (w q)) : q1 → ℝ) r :=by
          simp [Pi.add_apply,sum_add_distrib]
        _= ∑ r,w r:=congrArg (fun f :q1 → ℝ=> ∑ r,f r) hdecomp.symm
        _=4:=hw.sum_four
    rw [hsum,hsplit] at ht
    linarith
  have hover:qb q p=0:= (sm q p).trans (zZ i b)
  have hfull:qd w =
      (w p) ^ 2+2*w p*E₀+S₀-2*w p-E₀+
        ((w q) ^ 2+2*w q*E₁+S₁-2*w q-E₁) :=by
    calc
      qd w =qd ((x+Pi.single p (w p)) + Pi.single q (w q)) :=
        congrArg qd hdecomp
      _=_:=by
        rw [rI,rI,uk,
          hgrad₀,hgrad₁,hover,henergy,hsplit,hsplitSq]
        ring
  constructor
  · rw [hfull]
    exact xZ (w p) (w q) E₀ E₁ S₀ S₁
      (sum_nonneg fun r _=> hw.nonneg r) (hw.ud i b)
      (sum_nonneg fun r _=> hw.nonneg r) (hw.ud i (!b))
      (hw.sf i b) (hw.sf i (!b)) htotal
  · intro hzero
    rw [hfull] at hzero
    exact y5 (w p) (w q) E₀ E₁ S₀ S₁
      (sum_nonneg fun r _=> hw.nonneg r) (hw.ud i b)
      (sum_nonneg fun r _=> hw.nonneg r) (hw.ud i (!b))
      (hw.sf i b) (hw.sf i (!b)) htotal hzero
theorem q6.zc {w:q1 → ℝ}
    (hw:q6 w) (i:Fin 3) (b:Bool) (hface:0 < w (cubeFace i b))
    (hhigh: ∀ r,2 ≤ q3 r → r ≠ cubeFace i b → r ≠ cubeFace i (!b) → w r =0) :
    0 ≤ qd w :=
  (hw.sQ i b hface hhigh).1
end Erdos556
end bo
section aX
namespace Erdos556
open Finset
theorem u5: ∀ (i:Fin 3) (b:Bool) (p:q1),
    2 ≤ q3 p → Disjoint (q0 (cubeFace i b)) (q0 p) →
      p=cubeFace i (!b) :=by
  decide
theorem uy (w:q1 → ℝ) (hw:q6 w)
    (hdisj: (qe w :Set q1).Pairwise
      (fun p q=> Disjoint (q0 p) (q0 q))) :
    0 ≤ qd w :=by
  classical
  by_cases hface: ∃ p:q1,q3 p =2 ∧ 0 < w p
  · obtain ⟨p,hpdim,hp⟩ :=hface
    obtain ⟨i,b,rfl⟩ := (u1 p).mp hpdim
    apply hw.zc i b hp
    intro r hr hrp hrq
    by_contra hrzero
    have hrpos:0 < w r:=lt_of_le_of_ne (hw.nonneg r) (Ne.symm hrzero)
    have hpH:cubeFace i b ∈ qe w :=
      mem_filter.mpr ⟨mem_univ _,by rw [r4],hp⟩
    have hrH:r ∈ qe w :=mem_filter.mpr ⟨mem_univ _,hr,hrpos⟩
    exact hrq (u5 i b r hr (hdisj hpH hrH hrp.symm))
  · have hhigh: ∀ p,2 ≤ q3 p → p ≠ qF → w p =0:=by
      intro p hpdim hpne
      have hdim3:q3 p ≠ 3 :=fun h => hpne ((sz p).mp h)
      have hmax:=sM p
      have hdim2:q3 p =2:=by omega
      have hnot: ¬ 0 < w p:=fun h => hface ⟨p,hdim2,h⟩
      exact le_antisymm (le_of_not_gt hnot) (hw.nonneg p)
    exact (hw.nonneg qF).trans (hw.u6 hhigh)
theorem zS (w:q1 → ℝ) (hw:q6 w) : 0 ≤ qd w :=by
  obtain ⟨v,hv,hdisj,henergy⟩ :=yW w hw
  exact (uy v hv hdisj).trans henergy
end Erdos556
end aX
section aV
namespace Erdos556
open Finset
structure qs (w:q1 → ℝ) : Prop where
  normalized: ∀ p,0 < w p →
    (q3 p =1 ∧ w p=1) ∨ (q3 p =2 ∧ w p=2)
  disjoint: ∀ p q,p ≠ q → 0 < w p → 0 < w q →
    Disjoint (q0 p) (q0 q)
open scoped Classical in
noncomputable def qj (w:q1 → ℝ) : Finset q1:=
  univ.filter (fun p => 0 < w p)
theorem q6.eq_zero_of_not_pos {w:q1 → ℝ} (hw:q6 w)
    (p:q1) (hp: ¬ 0 < w p) : w p =0:=
  le_antisymm (le_of_not_gt hp) (hw.nonneg p)
theorem q6.tA {w:q1 → ℝ} (hw:q6 w) :
    (∑ p ∈ qj w,w p) = 4:=by
  classical
  calc
    (∑ p ∈ qj w,w p) = ∑ p,w p:=by
      apply sum_subset (subset_univ _)
      intro p _ hp
      apply hw.eq_zero_of_not_pos
      intro h
      exact hp (mem_filter.mpr ⟨mem_univ p,h⟩)
    _=4:=hw.sum_four
theorem qs.zh {w:q1 → ℝ} (ht:qs w)
    (p:q1) (hp:0 < w p) : ((q0 p).card:ℝ) = 2*w p:=by
  rcases ht.normalized p hp with ⟨hd,hw⟩ | ⟨hd,hw⟩ <;>
    rw [qU,hd,hw] <;> norm_num
theorem qs.cover {w:q1 → ℝ} (ht:qs w) (hw:q6 w) :
    (qj w).biUnion q0=univ:=by
  classical
  have hdisj: (qj w :Set q1).Pairwise
      (fun p q=> Disjoint (q0 p) (q0 q)) :=by
    intro p hp q hq hpq
    exact ht.disjoint p q hpq (mem_filter.mp hp).2 (mem_filter.mp hq).2
  have hsumR: (∑ p ∈ qj w,((q0 p).card:ℝ)) = 8:=by
    calc
      (∑ p ∈ qj w,((q0 p).card:ℝ)) =
          ∑ p ∈ qj w,2*w p:=
        sum_congr rfl (fun p hp=> ht.zh p (mem_filter.mp hp).2)
      _=2* ∑ p ∈ qj w,w p:= (mul_sum _ _ _).symm
      _=8:=by rw [hw.tA];norm_num
  have hsum: (∑ p ∈ qj w,(q0 p).card) = 8:=by
    exact_mod_cast hsumR
  have hcard: ((qj w).biUnion q0).card=8:=by
    rw [card_biUnion hdisj,hsum]
  have huniv: (univ:Finset wz).card=8:=by decide
  exact eq_of_subset_of_card_le (subset_univ _) (by omega)
theorem qs.ts {w:q1 → ℝ}
    (ht:qs w) (hw:q6 w) (S:Finset wz) :
    (∑ p ∈ qj w,(q0 p ∩ S).card) = S.card:=by
  classical
  have hdisj: (qj w :Set q1).Pairwise
      (fun p q=> Disjoint (q0 p ∩ S) (q0 q ∩ S)) :=by
    intro p hp q hq hpq
    exact (ht.disjoint p q hpq (mem_filter.mp hp).2 (mem_filter.mp hq).2).mono
      inter_subset_left inter_subset_left
  have hcover: (qj w).biUnion (fun p => q0 p ∩ S) = S:=by
    ext v
    constructor
    · intro hv
      obtain ⟨p,hp,hvp⟩ :=mem_biUnion.mp hv
      exact (mem_inter.mp hvp).2
    · intro hv
      have hall:v ∈ (qj w).biUnion q0:=by
        rw [ht.cover hw]
        exact mem_univ v
      obtain ⟨p,hp,hvp⟩ :=mem_biUnion.mp hall
      exact mem_biUnion.mpr ⟨p,hp,mem_inter.mpr ⟨hvp,hv⟩⟩
  rw [← card_biUnion hdisj,hcover]
end Erdos556
end aV
section c7
namespace Erdos556
open Finset
theorem q6.a0 {w:q1 → ℝ} (hw:q6 w)
    (hedges: ∀ p,q3 p ≠ 1 → w p=0) : qs w :=by
  classical
  have hposdim (p:q1) (hp:0 < w p) : q3 p =1:=by
    by_contra h
    rw [hedges p h] at hp
    exact hp.false
  have hsum: (∑ p ∈ ql w,w p) = 4:=by
    calc
      (∑ p ∈ ql w,w p) = ∑ p,w p:=by
        apply sum_subset (subset_univ _)
        intro p _ hp
        apply hw.eq_zero_of_not_pos
        intro hpos
        exact hp (mem_filter.mpr ⟨mem_univ p,hposdim p hpos,hpos⟩)
      _=4:=hw.sum_four
  obtain ⟨_,hones⟩ :=uB (ql w) w 4
    hw.vl
    (fun p hp=> hw.edge_le_one p (mem_filter.mp hp).2.1) hsum
  constructor
  · intro p hp
    exact Or.inl ⟨hposdim p hp,hones p (mem_filter.mpr ⟨mem_univ p,hposdim p hp,hp⟩)⟩
  · intro p q hpq hp hq
    exact ru p q (hposdim p hp) (hposdim q hq) hpq
      (hw.compatible p q hp hq)
theorem q6.wy {w:q1 → ℝ}
    (hw:q6 w)
    (hhigh: ∀ p,2 ≤ q3 p → p ≠ qF → w p =0)
    (hzero:qd w =0) : qs w :=by
  have hcube:w qF=0:=by
    have h :=hw.u6 hhigh
    rw [hzero] at h
    exact le_antisymm h (hw.nonneg qF)
  apply hw.a0
  intro p hp
  by_cases hp0:q3 p =0
  · exact hw.vertex_zero p hp0
  by_cases hpc:p=qF
  · exact hpc ▸ hcube
  · exact hhigh p (by omega) hpc
end Erdos556
end c7
section b8
namespace Erdos556
open Finset
theorem q6.wO {w:q1 → ℝ}
    (hw:q6 w) (i:Fin 3) (b:Bool) (hface:0 < w (cubeFace i b))
    (hhigh: ∀ r,2 ≤ q3 r → r ≠ cubeFace i b → r ≠ cubeFace i (!b) → w r =0)
    (hzero:qd w =0) : qs w :=by
  classical
  let p :=cubeFace i b
  let q :=cubeFace i (!b)
  have hpq:p ≠ q:=z4 i b
  obtain ⟨hL₀,hL₁,hE₀,hE₁⟩ := (hw.sQ i b hface hhigh).2 hzero
  have hE₀zero: (∑ r ∈ qf w i b,w r) = 0:=by
    rcases hE₀ with h | h
    · exact h
    · rw [h] at hL₀
      linarith
  have hwp:w p=2:=by
    rw [hE₀zero] at hL₀
    simpa only [add_zero] using hL₀
  have hwq:w q=0 ∨ w q=2:=by
    rcases hE₁ with h | h
    · right;rw [h] at hL₁;simpa only [add_zero] using hL₁
    · left;rw [h] at hL₁;change w q+2=2 at hL₁;linarith
  have hedge (r:q1) (hrdim:q3 r =1) (hr:0 < w r) :
      w r =1 ∧ q0 r ⊆ q0 q ∧ w q=0:=by
    have hrE:r ∈ ql w :=mem_filter.mpr ⟨mem_univ r,hrdim,hr⟩
    have hnot: ¬ q0 r ⊆ q0 p :=by
      intro hsub
      have hrF:r ∈ qf w i b :=mem_filter.mpr ⟨hrE,hsub⟩
      have hle:=single_le_sum (fun s _=> hw.nonneg s) hrF
      rw [hE₀zero] at hle
      linarith
    have hsub:q0 r ⊆ q0 q :=
      (se i b r hrdim (hw.compatible r p hr hface)).resolve_left hnot
    have hrF:r ∈ qf w i (!b) :=mem_filter.mpr ⟨hrE,hsub⟩
    have hmass: (∑ s ∈ qf w i (!b),w s) = 2:=by
      rcases hE₁ with h | h
      · have hle:=single_le_sum (fun s _=> hw.nonneg s) hrF
        rw [h] at hle
        linarith
      · exact h
    obtain ⟨_,hones⟩ :=uB (qf w i (!b)) w 2
      (hw.uL i (!b))
      (fun s hs=> hw.edge_le_one s (mem_filter.mp (mem_filter.mp hs).1).2.1) hmass
    have hqzero:w q=0:=by rw [hmass] at hL₁;change w q+2=2 at hL₁;linarith
    exact ⟨hones r hrF,hsub,hqzero⟩
  have hcases (r:q1) (hr:0 < w r) :
      r=p ∨ r=q ∨
        (q3 r =1 ∧ w r=1 ∧ q0 r ⊆ q0 q ∧ w q=0) :=by
    by_cases hrp:r=p
    · exact Or.inl hrp
    by_cases hrq:r=q
    · exact Or.inr (Or.inl hrq)
    have hrdim:q3 r =1:=by
      by_contra hd
      by_cases hd0:q3 r =0
      · rw [hw.vertex_zero r hd0] at hr
        exact hr.false
      · rw [hhigh r (by omega) hrp hrq] at hr
        exact hr.false
    exact Or.inr (Or.inr ⟨hrdim,hedge r hrdim hr⟩)
  have hdisj:Disjoint (q0 p) (q0 q) :=
    (ui i i b (!b)).mpr ⟨rfl,by cases b <;> decide⟩
  constructor
  · intro r hr
    rcases hcases r hr with rfl | rfl | ⟨hd,hw,_,_⟩
    · exact Or.inr ⟨r4 i b,hwp⟩
    · have hq2:w q=2:=hwq.resolve_left (ne_of_gt hr)
      exact Or.inr ⟨r4 i (!b),hq2⟩
    · exact Or.inl ⟨hd,hw⟩
  · intro r s hrs hr hs
    rcases hcases r hr with rfl | rfl | ⟨hrd,hrw,hrsub,hq0⟩
    · rcases hcases s hs with rfl | rfl | ⟨hsd,hsw,hssub,_⟩
      · exact (hrs rfl).elim
      · exact hdisj
      · exact hdisj.mono_right hssub
    · rcases hcases s hs with rfl | rfl | ⟨_,_,_,hq0⟩
      · exact hdisj.symm
      · exact (hrs rfl).elim
      · rw [hq0] at hr;exact hr.false.elim
    · rcases hcases s hs with rfl | rfl | ⟨hsd,_,_,_⟩
      · exact (hdisj.mono_right hrsub).symm
      · rw [hq0] at hs;exact hs.false.elim
      · exact ru r s hrd hsd hrs (hw.compatible r s hr hs)
end Erdos556
end b8
section bT
namespace Erdos556
open Finset
theorem w9: ∀ p q:q1,
    q3 p =2 → q3 q =2 → p ≠ q →
    ¬ Disjoint (q0 p) (q0 q) →
      (q0 p ∩ q0 q).card=2:=by
  decide
theorem qs.tN {w:q1 → ℝ}
    (ht:qs w) (hw:q6 w) (p:q1) (hp:0 < w p) :
    qm w p=2*w p-q3 p :=by
  classical
  unfold qm
  rw [sum_eq_single p]
  · rw [vU,one_mul]
  · intro q _ hqp
    by_cases hq:0 < w q
    · simp only [qb,if_pos (ht.disjoint p q hqp.symm hp hq),zero_mul]
    · rw [hw.eq_zero_of_not_pos q hq,mul_zero]
  · intro h
    exact (h (mem_univ p)).elim
theorem qs.zK {w:q1 → ℝ}
    (ht:qs w) (hw:q6 w) (p q :q1) (hp:0 < w p)
    (hpdim:q3 p =2) (hqdim:q3 q =2) (hpq:p ≠ q)
    (hinter: ¬ Disjoint (q0 p) (q0 q)) : 4 ≤ qm w q:=by
  classical
  have hwp:w p=2:=by
    rcases ht.normalized p hp with ⟨hd,_⟩ | ⟨_,h⟩
    · omega
    · exact h
  have hintcard:=w9 p q hpdim hqdim hpq hinter
  have hover:qb q p=1:=by
    have hnot: ¬ Disjoint (q0 q) (q0 p) :=fun h => hinter h.symm
    simp only [qb,if_neg hnot]
  have hcover: (∑ r ∈ qj w,
      ((q0 r ∩ q0 q).card:ℝ)) = 4:=by
    have h :=ht.ts hw (q0 q)
    rw [qU,hqdim] at h
    exact_mod_cast h
  have hpoint (r:q1) (hr:r ∈ qj w) :
      ((q0 r ∩ q0 q).card:ℝ) + (if r =p then 2 else 0) ≤
        2* (qb q r*w r) :=by
    by_cases hrp:r=p
    · subst r
      rw [hintcard,if_pos rfl,hover,hwp]
      norm_num
    rw [if_neg hrp,add_zero]
    by_cases hd:Disjoint (q0 q) (q0 r)
    · have hz:q0 r ∩ q0 q = ∅ :=disjoint_iff_inter_eq_empty.mp hd.symm
      simp only [hz,card_empty,Nat.cast_zero,qb,if_pos hd,zero_mul,mul_zero,le_refl]
    · have hle: ((q0 r ∩ q0 q).card:ℝ) ≤ (q0 r).card:=by
        exact_mod_cast card_le_card (show q0 r ∩ q0 q ⊆
          q0 r from inter_subset_left)
      rw [ht.zh r (mem_filter.mp hr).2] at hle
      simpa only [qb,if_neg hd,one_mul] using hle
  have hsum:=sum_le_sum hpoint
  have hpP:p ∈ qj w :=mem_filter.mpr ⟨mem_univ p,hp⟩
  have hrow: (∑ r ∈ qj w,qb q r*w r) =
      ∑ r,qb q r*w r:=by
    apply sum_subset (subset_univ _)
    intro r _ hr
    have hz:w r=0:=hw.eq_zero_of_not_pos r (fun h => hr (mem_filter.mpr ⟨mem_univ r,h⟩))
    rw [hz,mul_zero]
  rw [sum_add_distrib,hcover] at hsum
  have hdelta: (∑ r ∈ qj w,if r =p then (2:ℝ) else 0) = 2:=by simp [hpP]
  rw [hdelta,← mul_sum,hrow] at hsum
  simp only [qm,hqdim,Nat.cast_ofNat]
  linarith only [hsum]
theorem qs.yU {w:q1 → ℝ}
    (ht:qs w) (hw:q6 w) (p q :q1) (hp:0 < w p)
    (hpdim:2 ≤ q3 p) (hqdim:2 ≤ q3 q) (hpq:p ≠ q)
    (hover:qb p q=1) : qm w p < qm w q:=by
  have hpface:q3 p =2 ∧ w p=2:=by
    rcases ht.normalized p hp with ⟨hd,_⟩ | h
    · omega
    · exact h
  have hgp:qm w p=2:=by
    rw [ht.tN hw p hp,hpface.1,hpface.2]
    norm_num
  rw [hgp]
  by_cases hq3:q3 q =3
  · have hq:q=qF:= (sz q).mp hq3
    rw [hq,xg,hw.sum_four]
    norm_num
  · have hqmax:=sM q
    have hq2:q3 q =2:=by omega
    have hnot: ¬ Disjoint (q0 p) (q0 q) :=by
      intro h
      simp only [qb,if_pos h] at hover
      norm_num at hover
    have hg:=ht.zK hw p q hp hpface.1 hq2 hpq hnot
    linarith
end Erdos556
end bT
section bA
namespace Erdos556
open Finset
theorem sK (w:q1 → ℝ) (hw:q6 w)
    (hdisj: (qe w :Set q1).Pairwise
      (fun p q=> Disjoint (q0 p) (q0 q)))
    (hzero:qd w =0) : qs w :=by
  classical
  by_cases hface: ∃ p:q1,q3 p =2 ∧ 0 < w p
  · obtain ⟨p,hpdim,hp⟩ :=hface
    obtain ⟨i,b,rfl⟩ := (u1 p).mp hpdim
    apply hw.wO i b hp ?_ hzero
    intro r hr hrp hrq
    by_contra hrzero
    have hrpos:0 < w r:=lt_of_le_of_ne (hw.nonneg r) (Ne.symm hrzero)
    have hpH:cubeFace i b ∈ qe w :=
      mem_filter.mpr ⟨mem_univ _,by rw [r4],hp⟩
    have hrH:r ∈ qe w :=mem_filter.mpr ⟨mem_univ _,hr,hrpos⟩
    exact hrq (u5 i b r hr (hdisj hpH hrH hrp.symm))
  · apply hw.wy ?_ hzero
    intro p hpdim hpne
    have hdim3:q3 p ≠ 3 :=fun h => hpne ((sz p).mp h)
    have hmax:=sM p
    have hdim2:q3 p =2:=by omega
    exact hw.eq_zero_of_not_pos p (fun h => hface ⟨p,hdim2,h⟩)
theorem xf {w:q1 → ℝ} (hw:q6 w)
    (p q :q1) (hpq:p ≠ q) (hp:0 < w p) (hq:0 < w q)
    (hpdim:2 ≤ q3 p) (hqdim:2 ≤ q3 q)
    (hover:qb p q=1) (ht:qs (qx w p q)) :
    qd (qx w p q) < qd w :=by
  have hw':=hw.transfer p q hpq hp hpdim hqdim
  have hp':0 < qx w p q p:=by
    rw [uH w p q hpq]
    exact add_pos hp hq
  have hgrad:=ht.yU hw' p q hp' hpdim hqdim hpq hover
  have hdiff:=zl w p q (w q) hover
  change qm (qx w p q) p -qm (qx w p q) q =
    qm w p-qm w q at hdiff
  have hneg:qm w p-qm w q < 0:=by linarith
  have hprod:=mul_neg_of_pos_of_neg hq hneg
  rw [qx,xT w p q (w q) hover]
  linarith
theorem y9 (w:q1 → ℝ) (hw:q6 w)
    (hzero:qd w =0) : qs w :=by
  classical
  have aux: ∀ M:ℕ,∀ w:q1 → ℝ,q6 w →
      (qe w).card=M → qd w =0 → qs w :=by
    intro M
    induction M using Nat.strong_induction_on with
    | h M ih=>
        intro w hw hM hzero
        by_cases hd: (qe w :Set q1).Pairwise
            (fun p q=> Disjoint (q0 p) (q0 q))
        · exact sK w hw hd hzero
        simp only [Set.Pairwise] at hd
        push Not at hd
        obtain ⟨p,hpH,q,hqH,hpq,hnot⟩ :=hd
        have hpdim:= (mem_filter.mp hpH).2.1
        have hqdim:= (mem_filter.mp hqH).2.1
        have hp:= (mem_filter.mp hpH).2.2
        have hq:= (mem_filter.mp hqH).2.2
        have hover:qb p q=1:=by simp only [qb,if_neg hnot]
        have impossible (p q :q1) (hpq:p ≠ q) (hp:0 < w p) (hq:0 < w q)
            (hpdim:2 ≤ q3 p) (hqdim:2 ≤ q3 q)
            (hover:qb p q=1)
            (hE:qd (qx w p q) ≤ qd w) : False:=by
          have hw':=hw.transfer p q hpq hp hpdim hqdim
          have hcard:=rh hw p q hpq hp hq hpdim hqdim
          have hz:qd (qx w p q) = 0:=
            le_antisymm (by rwa [hzero] at hE) (zS _ hw')
          have ht:=ih (qe (qx w p q)).card (by omega)
            (qx w p q) hw' rfl hz
          have hlt:=xf hw p q hpq hp hq hpdim hqdim hover ht
          rw [hz,hzero] at hlt
          exact hlt.false
        rcases si w p q (hw.nonneg p) (hw.nonneg q) hover with
          hE | hE
        · exact (impossible p q hpq hp hq hpdim hqdim hover hE).elim
        · have hqp:qb q p=1:= (sm q p).trans hover
          exact (impossible q p hpq.symm hq hp hqdim hpdim hqp hE).elim
  exact aux (qe w).card w hw rfl hzero
theorem qs.ct {w:q1 → ℝ} (ht:qs w)
    (hw:q6 w) : qd w =0:=by
  classical
  have hdiag (p q :q1) (hpq:p ≠ q) : qb p q*w p*w q=0:=by
    by_cases hp:0 < w p
    · by_cases hq:0 < w q
      · simp only [qb,if_pos (ht.disjoint p q hpq hp hq),zero_mul]
      · rw [hw.eq_zero_of_not_pos q hq,mul_zero]
    · rw [hw.eq_zero_of_not_pos p hp,mul_zero,zero_mul]
  rw [yO,ws w hdiag,u0,← sum_sub_distrib]
  apply sum_eq_zero
  intro p _
  by_cases hp:0 < w p
  · rcases ht.normalized p hp with ⟨hd,he⟩ | ⟨hd,he⟩ <;> rw [hd,he] <;> norm_num
  · rw [hw.eq_zero_of_not_pos p hp]
    ring
end Erdos556
end bA
section bF
namespace Erdos556
open Finset Filter
open scoped Topology
structure qN (w:q1 → ℝ) (δ:ℝ) : Prop where
  nonneg: ∀ p,0 ≤ w p
  sum_close: |∑ p,w p-4| ≤ δ
  vertex_small: ∀ p,q3 p =0 → w p ≤ δ
  edge_bound: ∀ p,q3 p =1 → w p ≤ 1+δ
  incompatible_small: ∀ p q,(q0 p ∩ q0 q).card=1 → w p*w q ≤ δ
  energy_small:qd w ≤ δ
theorem qN.mono {w:q1 → ℝ} {δ ε :ℝ}
    (h:qN w δ) (hδε:δ ≤ ε) : qN w ε:=by
  refine ⟨h.nonneg,h.sum_close.trans hδε,?_,?_,?_,h.energy_small.trans hδε⟩
  · intro p hp
    exact (h.vertex_small p hp).trans hδε
  · intro p hp
    exact (h.edge_bound p hp).trans (add_le_add le_rfl hδε)
  · intro p q hpq
    exact (h.incompatible_small p q hpq).trans hδε
theorem qN.le_five {w:q1 → ℝ} {δ:ℝ}
    (h:qN w δ) (hδ:δ ≤ 1) (p:q1) : w p ≤ 5 :=by
  have hsum:= (abs_le.mp h.sum_close).2
  have hp:w p ≤ ∑ q,w q:=single_le_sum (fun q _=> h.nonneg q) (mem_univ p)
  linarith
theorem qN.dP {w:q1 → ℝ} (h:qN w 0) :
    q6 w ∧ qs w :=by
  have hw:q6 w :=by
    refine ⟨h.nonneg,?_,?_,?_,?_⟩
    · have hs:=abs_le.mp h.sum_close
      linarith
    · intro p hp
      exact le_antisymm (h.vertex_small p hp) (h.nonneg p)
    · intro p hp
      simpa only [add_zero] using h.edge_bound p hp
    · intro p q hp hq heq
      have hmul:=h.incompatible_small p q heq
      exact (not_lt_of_ge hmul) (mul_pos hp hq)
  exact ⟨hw,y9 w hw (le_antisymm h.energy_small (zS w hw))⟩
theorem xH:Continuous qd:=by
  unfold qd
  fun_prop
theorem tj {w:ℕ → q1 → ℝ} {δ:ℕ → ℝ} {v:q1 → ℝ}
    (hw: ∀ n,qN (w n) (δ n))
    (hδ:Tendsto δ atTop (𝓝 0)) (hv:Tendsto w atTop (𝓝 v)) :
    q6 v ∧ qs v :=by
  have hp (p:q1) : Tendsto (fun n => w n p) atTop (𝓝 (v p)) :=
    (tendsto_pi_nhds.mp hv) p
  have hs:Tendsto (fun n => ∑ p,w n p) atTop (𝓝 (∑ p,v p)) :=
    tendsto_finsetSum univ (fun p _=> hp p)
  have he:Tendsto (fun n => qd (w n)) atTop (𝓝 (qd v)) :=
    (xH.tendsto v).comp hv
  apply qN.dP
  constructor
  · intro p
    exact ge_of_tendsto' (hp p) (fun n => (hw n).nonneg p)
  · exact le_of_tendsto_of_tendsto' ((hs.sub_const 4).abs) hδ (fun n => (hw n).sum_close)
  · intro p hd
    exact le_of_tendsto_of_tendsto' (hp p) hδ (fun n => (hw n).vertex_small p hd)
  · intro p hd
    have h :=le_of_tendsto_of_tendsto' (hp p) (tendsto_const_nhds.add hδ)
      (fun n => (hw n).edge_bound p hd)
    simpa only [add_zero] using h
  · intro p q hbad
    exact le_of_tendsto_of_tendsto' ((hp p).mul (hp q)) hδ
      (fun n => (hw n).incompatible_small p q hbad)
  · exact le_of_tendsto_of_tendsto' he hδ (fun n => (hw n).energy_small)
end Erdos556
end bF
section bX
namespace Erdos556
open SimpleGraph Finset
theorem tP (w:q1 → ℝ) (n:ℝ) :
    qO (fun p => w p/n) = qO w /n^2:=by
  unfold qO
  simp only [sum_div]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  split_ifs <;> simp [div_mul_div_comm,pow_two]
theorem yX (w:q1 → ℝ) (n:ℝ) (hn:n ≠ 0) :
    qd (fun p => w p/n) * n^2=
      (∑ p,w p) ^ 2-qO w -n* (∑ p,(q3 p :ℝ) * w p) :=by
  rw [zv,tP,← sum_div]
  have hsum: (∑ p,(q3 p :ℝ) * (w p /n)) =
      (∑ p,(q3 p :ℝ) * w p) / n:=by
    simp only [sum_div,mul_div_assoc]
  rw [hsum]
  field_simp
noncomputable def q2.rQ {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D)
    (n:ℝ) (p:q1) : ℝ:= (h.qa p).card/n
theorem q2.aH {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (n:ℝ) :
    (∑ p,h.rQ n p) = Fintype.card V /n:=by
  unfold rQ
  rw [← sum_div]
  congr 1
  exact_mod_cast h.xF
theorem q2.uC {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (n:ℝ) (hn:n ≠ 0) :
    qd (h.rQ n) * n^2= (Fintype.card V :ℝ) ^ 2-
      qO (fun p => ((h.qa p).card:ℝ)) -
      n* (∑ p,(q3 p :ℝ) * (h.qa p).card) :=by
  unfold rQ
  rw [yX _ n hn]
  have hs: (∑ p,((h.qa p).card:ℝ)) = Fintype.card V :=by
    exact_mod_cast h.xF
  rw [hs]
theorem q2.yw {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (n:ℕ) (hn:8 ≤ n)
    (hno: ∀ i,¬ cycleGraph n ⊑ c.graph i) (δ:ℝ) (hδ:0 ≤ δ)
    (hsize: |(Fintype.card V :ℝ) - 4*n| ≤ δ*n)
    (hvertex:6*E+Fintype.card V ≤ δ ^2* (n:ℝ) ^ 2)
    (hedge:48*E ≤ δ* (n:ℝ) ^ 2)
    (hpair:6*E+Fintype.card V ≤ δ * (n:ℝ) ^ 2)
    (henergy: (Fintype.card V :ℝ) + (2*D-n) *
        (∑ p,(q3 p :ℝ) * (h.qa p).card) + 6*E ≤ δ* (n:ℝ) ^ 2) :
    qN (h.rQ n) δ :=by
  have hnpos: (0:ℝ) < n:=by exact_mod_cast (show 0 < n by omega)
  have hnsq: (0:ℝ) < (n:ℝ) ^ 2:=sq_pos_of_pos hnpos
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro p
    exact div_nonneg (Nat.cast_nonneg _) hnpos.le
  · rw [h.aH]
    have hid: (Fintype.card V :ℝ) / n-4= (Fintype.card V -4*n) / n:=by
      field_simp
    rw [hid,abs_div,abs_of_pos hnpos]
    exact (div_le_iff₀ hnpos).mpr hsize
  · intro p hp
    apply (div_le_iff₀ hnpos).mpr
    have hb:= (h.zQ p hp).trans hvertex
    have hm: (0:ℝ) ≤ (h.qa p).card:=by positivity
    have hdn:=mul_nonneg hδ hnpos.le
    nlinarith
  · intro p hp
    apply (div_le_iff₀ hnpos).mpr
    have hb:=h.t5 n hn hno p hp
    nlinarith
  · intro p q hpq
    dsimp only [rQ]
    rw [div_mul_div_comm,← pow_two]
    apply (div_le_iff₀ hnsq).mpr
    exact (h.su p q hpq).trans hpair
  · have he:=h.uC n hnpos.ne'
    have hb:= (h.yS n).trans henergy
    nlinarith
end Erdos556
end bX
section br
namespace Erdos556
open SimpleGraph Finset
theorem vy (δ:ℝ) (hδ:0 < δ) :
    ∃ ε :ℝ,0 < ε ∧ ε ≤ δ ∧ ∃ n₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (c:q4 V) (n:ℕ),n₀ ≤ n → Fintype.card V =4*n-3 →
      (∀ i,¬ cycleGraph n ⊑ c.graph i) →
      ∀ h :q2 c (ε* (Fintype.card V :ℝ) ^ 2)
        ((n:ℝ) / 2+ε*Fintype.card V),qN (h.rQ n) δ :=by
  let t :ℝ:=min δ (min (δ^2) 1)
  have ht:0 < t:=lt_min hδ (lt_min (sq_pos_of_pos hδ) zero_lt_one)
  have htδ:t ≤ δ:=min_le_left _ _
  have htδsq:t ≤ δ^2:= (min_le_right _ _).trans (min_le_left _ _)
  let ε :ℝ:=t/100000
  have hε:0 < ε:=div_pos ht (by norm_num)
  have hεδ:ε ≤ δ:=by
    have hεt:ε ≤ t:=by dsimp only [ε];nlinarith
    exact hεt.trans htδ
  obtain ⟨m,hm⟩ :=exists_nat_ge (100000/t)
  refine ⟨ε,hε,hεδ,max 8 m,?_⟩
  intro V _ _ c n hn hN hno h
  have hn8:8 ≤ n:= (le_max_left _ _).trans hn
  have hmn:m ≤ n:= (le_max_right _ _).trans hn
  have hnpos: (0:ℝ) < n:=by exact_mod_cast (show 0 < n by omega)
  have htn:100000 ≤ t*n:=by
    have hmnR: (m:ℝ) ≤ n:=by exact_mod_cast hmn
    have hh:= (div_le_iff₀ ht).mp (hm.trans hmnR)
    nlinarith
  have hNR: (Fintype.card V :ℝ) = 4*n-3:=by
    have hh:Fintype.card V +3=4*n:=by omega
    have hhR: (Fintype.card V :ℝ) + 3=4*n:=by exact_mod_cast hh
    linarith
  have hNnonneg: (0:ℝ) ≤ Fintype.card V :=by positivity
  have hNle: (Fintype.card V :ℝ) ≤ 4*n:=by linarith
  have hNsq: (Fintype.card V :ℝ) ^ 2 ≤ 16* (n:ℝ) ^ 2:=by nlinarith
  have heq:100000*ε=t:=by dsimp only [ε];ring
  have hlarge:100000* (n:ℝ) ≤ t* (n:ℝ) ^ 2:=by
    nlinarith [mul_le_mul_of_nonneg_right htn hnpos.le]
  have hcommon: (Fintype.card V :ℝ) + 48* (ε* (Fintype.card V :ℝ) ^ 2) ≤
      t* (n:ℝ) ^ 2:=by
    have hscaled:=mul_le_mul_of_nonneg_left hNsq hε.le
    have heqscaled:100000*ε* (n:ℝ) ^ 2=t* (n:ℝ) ^ 2:=by rw [heq]
    nlinarith [mul_nonneg ht.le (sq_nonneg (n:ℝ))]
  have htδn:=mul_le_mul_of_nonneg_right htδ (sq_nonneg (n:ℝ))
  have htδsqn:=mul_le_mul_of_nonneg_right htδsq (sq_nonneg (n:ℝ))
  have hE:0 ≤ ε* (Fintype.card V :ℝ) ^ 2:=mul_nonneg hε.le (sq_nonneg _)
  apply h.yw n hn8 hno δ hδ.le
  · rw [hNR]
    have habs: |4* (n:ℝ) - 3-4*n| = 3:=by ring_nf;norm_num
    rw [habs]
    have hh:=mul_le_mul_of_nonneg_right htδ hnpos.le
    linarith
  · linarith
  · linarith
  · linarith
  · have hW:=h.wR
    have hmul:=mul_le_mul_of_nonneg_left hW (mul_nonneg (by positivity: (0:ℝ) ≤ 2*ε)
      hNnonneg)
    nlinarith
end Erdos556
end br
section bU
namespace Erdos556
open SimpleGraph Finset
theorem yq {V:Type*} [Finite V]
    (G H :SimpleGraph V) (hGH:G ≤ H) :
    Nat.card H.edgeSet=Nat.card G.edgeSet+Nat.card (H ⊓ Gᶜ).edgeSet:=by
  classical
  have heq:G ⊔ (H ⊓ Gᶜ) = H:=by
    ext u v
    constructor
    · rintro (hg | ⟨hh,_⟩)
      · exact hGH hg
      · exact hh
    · intro hh
      by_cases hg:G.Adj u v
      · exact Or.inl hg
      · exact Or.inr ⟨hh,hh.ne,hg⟩
  have hd:Disjoint G (H ⊓ Gᶜ) :=by
    apply SimpleGraph.disjoint_left.mpr
    intro u v hg hh
    exact hh.2.2 hg
  have hh:=yD _ _ hd
  rwa [heq] at hh
def q2.qI {V:Type*} [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) : SimpleGraph V :=
  qJ h.profile ⊓ h.bipartiteUnionᶜ
theorem q2.zE {V:Type*}
    [Finite V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) :
    (Nat.card (qJ h.profile).edgeSet:ℝ) =
      Nat.card h.bipartiteUnion.edgeSet+Nat.card h.qI.edgeSet:=by
  exact_mod_cast yq _ _ h.vm
theorem q2.tn {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (n:ℝ) (hn:n ≠ 0) :
    2* (Nat.card h.qI.edgeSet:ℝ) ≤
      Fintype.card V + (2*D-n) *
        (∑ p,(q3 p :ℝ) * (h.qa p).card) +
      6*E-qd (h.rQ n) * n^2:=by
  have he:=h.uC n hn
  have hpot:=sY h.profile
  have hsplit:=h.zE
  have hb:=h.yE
  change 2 * (Nat.card (qJ h.profile).edgeSet:ℝ) =
    qO (fun p => ((h.qa p).card:ℝ)) at hpot
  nlinarith
theorem q2.s2 {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (p q :q1) (i:Fin 3)
    (hsep:q5 p q i)
    (u v :V) (hu:u ∈ h.qa p) (hv:v ∈ h.qa q)
    (hwrong: ¬ (c.graph i).Adj u v) : h.qI.Adj u v:=by
  have hup:= (h.r3 p u).mp hu
  have hvp:= (h.r3 q v).mp hv
  have hpot: (qJ h.profile).Adj u v:=by
    change Disjoint (q0 (h.profile u)) (q0 (h.profile v))
    rw [hup,hvp]
    exact re _ _ i hsep.1
  refine ⟨hpot,hpot.ne,?_⟩
  intro hb
  obtain ⟨j,hj⟩ :=iSup_adj.mp hb
  have hopp:=h.ry j u v hj
  rw [hup,hvp] at hopp
  have hji:j=i:=by
    by_contra hji
    exact hsep.2 j hji hopp
  subst j
  exact hwrong (h.bipartite_le i hj)
end Erdos556
end bU
section cb
namespace Erdos556
open Finset Filter
open scoped Topology
theorem uQ (η:ℝ) (hη:0 < η) :
    ∃ δ :ℝ,0 < δ ∧ ∀ w:q1 → ℝ,qN w δ →
      ∃ v :q1 → ℝ,q6 v ∧ qs v ∧
        (∀ p,|w p -v p| < η) ∧ |qd w| < η:=by
  classical
  by_contra hn
  have hbad (δ:ℝ) (hδ:0 < δ) : ∃ w :q1 → ℝ,qN w δ ∧
      ¬ ∃ v:q1 → ℝ,q6 v ∧ qs v ∧
        (∀ p,|w p -v p| < η) ∧ |qd w| < η:=by
    by_contra h
    apply hn
    refine ⟨δ,hδ,?_⟩
    intro w hw
    by_contra hv
    exact h ⟨w,hw,hv⟩
  let ε :ℕ → ℝ:=fun n => 1 / ((n:ℝ) + 1)
  have hεpos (n:ℕ) : 0 < ε n :=by dsimp only [ε];positivity
  have hεle (n:ℕ) : ε n ≤ 1 :=by
    dsimp only [ε]
    apply (div_le_one (by positivity:0 < (n:ℝ) + 1)).mpr
    have hn:0 ≤ (n:ℝ) :=by positivity
    linarith
  choose w hw hfar using fun n => hbad (ε n) (hεpos n)
  let K :Set (q1 → ℝ) :=Set.Icc (fun _ => 0) (fun _ => 5)
  have hcompact:IsCompact K :=isCompact_Icc
  have hwK (n:ℕ) : w n ∈ K :=
    ⟨(hw n).nonneg,fun p => (hw n).le_five (hεle n) p⟩
  obtain ⟨v,hvK,φ,hφ,hv⟩ :=hcompact.tendsto_subseq hwK
  have hε:Tendsto ε atTop (𝓝 0) :=tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimε:Tendsto (ε ∘ φ) atTop (𝓝 0) :=hε.comp hφ.tendsto_atTop
  obtain ⟨hvweight,hvtiling⟩ :=tj (fun n => hw (φ n)) hlimε hv
  have heach (p:q1) : ∀ᶠ n in atTop,|w (φ n) p -v p| < η:=by
    have hp:= (tendsto_pi_nhds.mp hv) p
    simpa only [Real.dist_eq,Function.comp_apply] using (Metric.tendsto_nhds.mp hp) η hη
  have hall: ∀ᶠ n in atTop,∀ p,|w (φ n) p -v p| < η:=Filter.eventually_all.mpr heach
  have henergy:Tendsto (fun n => qd (w (φ n))) atTop (𝓝 0) :=by
    have hh:= (xH.tendsto v).comp hv
    rwa [hvtiling.ct hvweight] at hh
  have hevent: ∀ᶠ n in atTop,|qd (w (φ n))| < η:=by
    simpa only [Real.dist_eq,sub_zero] using (Metric.tendsto_nhds.mp henergy) η hη
  obtain ⟨n,hn,he⟩ := (hall.and hevent).exists
  exact hfar (φ n) ⟨v,hvweight,hvtiling,hn,he⟩
end Erdos556
end cb
section bC
namespace Erdos556
open SimpleGraph Finset
theorem v5 (η:ℝ) (hη:0 < η) :
    ∃ n₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (c:q4 V) (n:ℕ),n₀ ≤ n → Odd n →
      Fintype.card V =4*n-3 → (∀ i,¬ cycleGraph n ⊑ c.graph i) →
      ∃ E D:ℝ,∃ h:q2 c E D,∃ v:q1 → ℝ,
        q6 v ∧ qs v ∧
        (∀ p,|h.rQ n p-v p| < η) ∧
        (Nat.card h.qI.edgeSet:ℝ) ≤ η* (n:ℝ) ^ 2:=by
  let α :ℝ:=η/1000
  have hα:0 < α:=div_pos hη (by norm_num)
  have hαη:α < η:=by dsimp only [α];linarith
  obtain ⟨δ₀,hδ₀,hstable⟩ :=uQ α hα
  let δ :ℝ:=min δ₀ α
  have hδ:0 < δ:=lt_min hδ₀ hα
  obtain ⟨ε,hε,hεδ,n₁,happrox⟩ :=vy δ hδ
  have hεα:ε ≤ α:=hεδ.trans (min_le_right _ _)
  obtain ⟨n₂,hdecomp⟩ :=wZ ε hε
  obtain ⟨m,hm⟩ :=exists_nat_ge (4/α)
  refine ⟨max 8 (max m (max n₁ n₂)),?_⟩
  intro V _ _ c n hn hodd hN hno
  have hn8:8 ≤ n:= (le_max_left _ _).trans hn
  have hmnat:m ≤ n:= (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₁:n₁ ≤ n:= (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hn₂:n₂ ≤ n:= (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnpos: (0:ℝ) < n:=by exact_mod_cast (show 0 < n by omega)
  have hNleN:Fintype.card V ≤ 4 *n:=by omega
  have hnN:n ≤ Fintype.card V :=by omega
  obtain ⟨h⟩ :=hdecomp c n hn₂ hodd hnN hNleN hno
  have hw:= (happrox c n hn₁ hN hno h).mono (min_le_left δ₀ α)
  obtain ⟨v,hv,ht,hclose,henergy⟩ :=hstable _ hw
  refine ⟨_,_,h,v,hv,ht,fun p => (hclose p).trans hαη,?_⟩
  have hNnonneg: (0:ℝ) ≤ Fintype.card V :=by positivity
  have hNle: (Fintype.card V :ℝ) ≤ 4*n:=by exact_mod_cast hNleN
  have hNsq: (Fintype.card V :ℝ) ^ 2 ≤ 16* (n:ℝ) ^ 2:=by nlinarith
  have hαn:4 ≤ α*n:=by
    have hmn: (m:ℝ) ≤ n:=by exact_mod_cast hmnat
    have hh:= (div_le_iff₀ hα).mp (hm.trans hmn)
    nlinarith
  have hNsmall: (Fintype.card V :ℝ) ≤ α* (n:ℝ) ^ 2:=by
    nlinarith [mul_le_mul_of_nonneg_right hαn hnpos.le]
  have hEsmall:ε* (Fintype.card V :ℝ) ^ 2 ≤ 16*α* (n:ℝ) ^ 2:=by
    have hh:=mul_le_mul_of_nonneg_left hNsq hε.le
    have hh':=mul_le_mul_of_nonneg_right hεα (sq_nonneg (n:ℝ))
    nlinarith
  have hW:=h.wR
  have hWscaled:=mul_le_mul_of_nonneg_left hW
    (mul_nonneg (by positivity: (0:ℝ) ≤ 2*ε) hNnonneg)
  have he:= (abs_lt.mp henergy).1
  have hescaled:=mul_le_mul_of_nonneg_right (le_of_lt he) (sq_nonneg (n:ℝ))
  have hb:=h.tn n hnpos.ne'
  have hαeq:1000*α=η:=by dsimp only [α];ring
  have hαeqsq:1000*α* (n:ℝ) ^ 2=η* (n:ℝ) ^ 2:=by rw [hαeq]
  nlinarith [mul_nonneg hα.le (sq_nonneg (n:ℝ))]
end Erdos556
end bC
section b3
namespace Erdos556
open SimpleGraph Finset
structure qi {V:Type*} [DecidableEq V] (G:SimpleGraph V)
    [DecidableRel G.Adj] (X Y :Finset V) (d:ℕ) : Prop where
  left: ∀ x ∈ X,(Y.filter (fun y => ¬ G.Adj x y)).card ≤ d
  right: ∀ y ∈ Y,(X.filter (fun x => ¬ G.Adj y x)).card ≤ d
theorem qi.mono {V:Type*} [DecidableEq V] {G:SimpleGraph V}
    [DecidableRel G.Adj] {X Y X' Y':Finset V} {d:ℕ}
    (h:qi G X Y d) (hX:X' ⊆ X) (hY:Y' ⊆ Y) :
    qi G X' Y' d :=by
  constructor
  · intro x hx
    exact (card_le_card (filter_subset_filter _ hY)).trans (h.left x (hX hx))
  · intro y hy
    exact (card_le_card (filter_subset_filter _ hX)).trans (h.right y (hY hy))
theorem qi.symm {V:Type*} [DecidableEq V] {G:SimpleGraph V}
    [DecidableRel G.Adj] {X Y :Finset V} {d:ℕ}
    (h:qi G X Y d) : qi G Y X d:= ⟨h.right,h.left⟩
theorem r6 {V:Type*}
    (G:SimpleGraph V) [DecidableRel G.Adj] (x:V) (Y F :Finset V) (d:ℕ)
    (hmiss: (Y.filter (fun y => ¬ G.Adj x y)).card ≤ d) (hsize:F.card+d < Y.card) :
    ∃ y ∈ Y,y ∉ F ∧ G.Adj x y:=by
  classical
  let B :=Y.filter (fun y => ¬ G.Adj x y)
  have hc: (F ∪ B).card < Y.card:=
    (card_union_le F B).trans_lt ((Nat.add_le_add_left hmiss F.card).trans_lt hsize)
  obtain ⟨y,hy,hybad⟩ :=exists_mem_notMem_of_card_lt_card hc
  have hyF:y ∉ F:=fun h => hybad (mem_union_left _ h)
  have hyB:y ∉ B:=fun h => hybad (mem_union_right _ h)
  refine ⟨y,hy,hyF,?_⟩
  by_contra h
  exact hyB (mem_filter.mpr ⟨hy,h⟩)
theorem x9 {V:Type*}
    (G:SimpleGraph V) [DecidableRel G.Adj] (u v :V) (Y:Finset V) (d:ℕ)
    (hu: (Y.filter (fun y => ¬ G.Adj u y)).card ≤ d)
    (hv: (Y.filter (fun y => ¬ G.Adj v y)).card ≤ d) (hsize:2*d < Y.card) :
    ∃ y ∈ Y,G.Adj u y ∧ G.Adj v y:=by
  classical
  obtain ⟨y,hy,hybad,huy⟩ :=r6 G u Y
    (Y.filter (fun y => ¬ G.Adj v y)) d hu (by omega)
  refine ⟨y,hy,huy,?_⟩
  by_contra h
  exact hybad (mem_filter.mpr ⟨hy,h⟩)
end Erdos556
end b3
section ba
namespace Erdos556
open SimpleGraph Finset
theorem q2.tb {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (d:ℕ) :
    ∃ Z :Finset V,d*Z.card ≤ 2*Nat.card h.qI.edgeSet ∧
      ∀ p q:q1,∀ i:Fin 3,q5 p q i →
        qi (c.graph i) (h.qa p \ Z) (h.qa q \ Z) d :=by
  classical
  obtain ⟨K,_,hcount,hclean⟩ :=vk h.qI univ d
  let Z :Finset V :=univ \ K
  have hZ:Z.card=Fintype.card V -K.card:=by simp [Z,card_sdiff]
  have he:Nat.card (h.qI.induce ((univ:Finset V) : Set V)).edgeSet=
      Nat.card h.qI.edgeSet:=by
    have hsupp:h.qI.support ⊆ ((univ:Finset V) : Set V) :=
      fun _ _=> mem_univ _
    have hh:=h.qI.card_edgeFinset_induce_of_support_subset hsupp
    simpa only [q7] using hh
  have hc:d*Z.card ≤ 2*Nat.card h.qI.edgeSet:=by
    simp only [q7,card_univ] at hcount
    rw [he] at hcount
    rwa [hZ]
  refine ⟨Z,hc,?_⟩
  intro p q i hsep
  have hK {x:V} (hx:x ∉ Z) : x ∈ K:=by simpa [Z] using hx
  constructor
  · intro x hx
    have hxK:=hK (mem_sdiff.mp hx).2
    have hsub: ((h.qa q \ Z).filter (fun y => ¬ (c.graph i).Adj x y)) ⊆
        h.qI.neighborFinset x ∩ univ:=by
      intro y hy
      obtain ⟨hy,hxy⟩ :=mem_filter.mp hy
      exact mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr
        (h.s2 p q i hsep x y
          (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).1 hxy),mem_univ _⟩
    exact (card_le_card hsub).trans (hclean x hxK)
  · intro y hy
    have hyK:=hK (mem_sdiff.mp hy).2
    have hsub: ((h.qa p \ Z).filter (fun x => ¬ (c.graph i).Adj y x)) ⊆
        h.qI.neighborFinset y ∩ univ:=by
      intro x hx
      obtain ⟨hx,hyx⟩ :=mem_filter.mp hx
      have hxy: ¬ (c.graph i).Adj x y:=fun hxy=> hyx hxy.symm
      exact mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr
        (h.s2 p q i hsep x y
          (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).1 hxy).symm,mem_univ _⟩
    exact (card_le_card hsub).trans (hclean y hyK)
end Erdos556
end ba
section bV
namespace Erdos556
open SimpleGraph Finset
structure rv {V:Type*} [DecidableEq V]
    (c:q4 V) (n:ℕ) (η:ℝ) where
  weight:q1 → ℝ
  admissible:q6 weight
  tiling:qs weight
  sets:q1 → Finset V
  disjoint: ∀ p q,p ≠ q → Disjoint (sets p) (sets q)
  size_lower: ∀ p,(weight p -η) * n ≤ (sets p).card
  size_upper: ∀ p,((sets p).card:ℝ) ≤ (weight p +η) * n
  defect:ℕ
  defect_le: (defect:ℝ) ≤ η*n
  dense: ∀ p q i,q5 p q i →
    qi (c.graph i) (sets p) (sets q) defect
theorem zI (η:ℝ) (hη:0 < η) :
    ∃ n₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (c:q4 V) (n:ℕ),n₀ ≤ n → Odd n →
      Fintype.card V =4*n-3 → (∀ i,¬ cycleGraph n ⊑ c.graph i) →
      Nonempty (rv c n η) :=by
  let τ :ℝ:=min (η/4) (η^2/100)
  have hτ:0 < τ:=lt_min (by positivity) (by positivity)
  have hτη:τ ≤ η/4:=min_le_left _ _
  have hτsq:τ ≤ η^2/100:=min_le_right _ _
  obtain ⟨n₁,hstable⟩ :=v5 τ hτ
  obtain ⟨m,hm⟩ :=exists_nat_ge (8/η)
  refine ⟨max 1 (max m n₁),?_⟩
  intro V _ _ c n hn hodd hN hno
  classical
  have hn₁:n₁ ≤ n:= (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hmn:m ≤ n:= (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnpos: (0:ℝ) < n:=by exact_mod_cast (show 0 < n by omega)
  have hηn:8 ≤ η*n:=by
    have hmnR: (m:ℝ) ≤ n:=by exact_mod_cast hmn
    have hh:= (div_le_iff₀ hη).mp (hm.trans hmnR)
    nlinarith
  obtain ⟨E,D,h,v,hv,ht,hclose,hmissing⟩ :=hstable c n hn₁ hodd hN hno
  let d :ℕ:= ⌊η*n/4⌋₊
  have hdle: (d:ℝ) ≤ η*n/4:=Nat.floor_le (by positivity)
  have hdgt:η*n/4 < (d:ℝ) + 1:=Nat.lt_floor_add_one _
  have hdlo:η*n/8 ≤ (d:ℝ) :=by linarith
  obtain ⟨Z,hZcount,hclean⟩ :=h.tb d
  have hZcountR: (d:ℝ) * Z.card ≤ 2* (Nat.card h.qI.edgeSet:ℝ) :=by
    exact_mod_cast hZcount
  have hZnonneg: (0:ℝ) ≤ Z.card:=by positivity
  have hZ: (Z.card:ℝ) ≤ η*n/2:=by
    have hscaled:=mul_le_mul_of_nonneg_right hdlo hZnonneg
    have hτscaled:=mul_le_mul_of_nonneg_right hτsq (sq_nonneg (n:ℝ))
    have hpos:0 < η*n:=mul_pos hη hnpos
    nlinarith
  let A :q1 → Finset V :=fun p => h.qa p \ Z
  refine ⟨{
    weight:=v
    admissible:=hv
    tiling:=ht
    sets:=A
    disjoint:=fun p q hpq=> (h.tK p q hpq).mono sdiff_subset sdiff_subset
    size_lower:= ?_
    size_upper:= ?_
    defect:=d
    defect_le:=by linarith
    dense:=hclean}⟩
  · intro p
    have hp:= (abs_lt.mp (hclose p)).1
    have hratio:v p-τ < ((h.qa p).card:ℝ) / n:=by
      change-τ < ((h.qa p).card:ℝ) / n-v p at hp
      linarith
    have hraw:= (lt_div_iff₀ hnpos).mp hratio
    have hc:=card_sdiff_add_card_inter (h.qa p) Z
    have hi:=card_le_card (inter_subset_right:h.qa p ∩ Z ⊆ Z)
    have hcard: ((h.qa p).card:ℝ) ≤ (A p).card+ (Z.card:ℝ) :=by
      exact_mod_cast (show (h.qa p).card ≤ (A p).card+Z.card by dsimp only [A];omega)
    have hτηscaled:=mul_le_mul_of_nonneg_right hτη hnpos.le
    nlinarith
  · intro p
    have hp:= (abs_lt.mp (hclose p)).2
    have hratio: ((h.qa p).card:ℝ) / n < v p +τ:=by
      change ((h.qa p).card:ℝ) / n-v p < τ at hp
      linarith
    have hraw:= (div_lt_iff₀ hnpos).mp hratio
    have hcard: ((A p).card:ℝ) ≤ (h.qa p).card:=by
      exact_mod_cast card_le_card (sdiff_subset:A p ⊆ h.qa p)
    have hτηscaled:=mul_le_mul_of_nonneg_right hτη hnpos.le
    nlinarith
end Erdos556
end bV
section aR
namespace Erdos556
open Finset
theorem wJ: ∀ (i:Fin 3) (b:Bool) (q:q1),
    Disjoint (q0 (cubeFace i b)) (q0 q) →
      q5 (cubeFace i b) q i:=by decide
theorem qs.af {w:q1 → ℝ}
    (ht:qs w) (hw:q6 w) (i:Fin 3) (b:Bool)
    (hp:0 < w (cubeFace i b)) :
    ∃ q :q1,q ≠ cubeFace i b ∧ 0 < w q ∧ q5 (cubeFace i b) q i:=by
  classical
  have hpval:w (cubeFace i b) = 2:=by
    rcases ht.normalized _ hp with ⟨hd,_⟩ | ⟨_,he⟩
    · rw [r4] at hd
      omega
    · exact he
  have hex: ∃ q:q1,q ≠ cubeFace i b ∧ 0 < w q :=by
    by_contra hn
    have hz (q:q1) (hq:q ≠ cubeFace i b) : w q =0:=
      hw.eq_zero_of_not_pos q (fun hqpos=> hn ⟨q,hq,hqpos⟩)
    have hs: (∑ q,w q) = w (cubeFace i b) :=by
      apply sum_eq_single (cubeFace i b)
      · intro q _ hq
        exact hz q hq
      · simp
    rw [hw.sum_four,hpval] at hs
    norm_num at hs
  obtain ⟨q,hqp,hq⟩ :=hex
  exact ⟨q,hqp,hq,wJ i b q
    (ht.disjoint _ _ hqp.symm hp hq)⟩
end Erdos556
end aR
section bY
namespace Erdos556
open SimpleGraph Finset
theorem s8 {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (L d :ℕ) (hL:0 < L)
    (X Y :Finset V) (hdis:Disjoint X Y) (hdef:qi G X Y d)
    (hX:L+2*d+1 ≤ X.card) (hY:L+2*d ≤ Y.card)
    (u v :V) (hu:u ∈ X) (hv:v ∈ X) (huv:u ≠ v) :
    ∃ p :G.Walk u v,p.IsPath ∧ p.length=2*L ∧ ∀ z ∈ p.support,z ∈ X ∪ Y:=by
  induction L generalizing X Y u v with
  | zero=> omega
  | succ L ih=>
      classical
      by_cases hzero:L=0
      · subst L
        obtain ⟨y,hy,huy,hvy⟩ :=x9 G u v Y d
          (hdef.left u hu) (hdef.left v hv) (by omega)
        let p :G.Walk u v:=Walk.cons huy (Walk.cons hvy.symm Walk.nil)
        have huY:u ∉ Y:=Finset.disjoint_left.mp hdis hu
        refine ⟨p,?_,rfl,?_⟩
        · apply (Walk.cons_isPath_iff _ _).mpr
          refine ⟨Walk.IsPath.of_adj hvy.symm,?_⟩
          simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,
            or_false,not_or]
          exact ⟨fun h => huY (h ▸ hy),huv⟩
        · intro z hz
          simp only [p,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,
            or_false] at hz
          rcases hz with h | h | h
          · exact h ▸ mem_union_left Y hu
          · exact h ▸ mem_union_right X hy
          · exact h ▸ mem_union_left Y hv
      · obtain ⟨y,hy,_,huy⟩ :=r6 G u Y ∅ d
          (hdef.left u hu) (by simp only [card_empty];omega)
        have hpair: ({u,v} : Finset V).card ≤ 2:=by
          have h :=card_insert_le u ({v} : Finset V)
          simp only [card_singleton] at h
          omega
        obtain ⟨x,hx,hxf,hyx⟩ :=r6 G y X {u,v} d
          (hdef.right y hy) (by omega)
        have hxu:x ≠ u:=fun h => hxf (by simp [h])
        have hxv:x ≠ v:=fun h => hxf (by simp [h])
        have hx':x ∈ X.erase u :=mem_erase.mpr ⟨hxu,hx⟩
        have hv':v ∈ X.erase u :=mem_erase.mpr ⟨huv.symm,hv⟩
        have hX':L+2*d+1 ≤ (X.erase u).card:=by rw [card_erase_of_mem hu];omega
        have hY':L+2*d ≤ (Y.erase y).card:=by rw [card_erase_of_mem hy];omega
        obtain ⟨q,hq,hqL,hqS⟩ :=ih (by omega) (X.erase u) (Y.erase y)
          (hdis.mono (erase_subset _ _) (erase_subset _ _))
          (hdef.mono (erase_subset _ _) (erase_subset _ _)) hX' hY' x v hx' hv' hxv
        have huq:u ∉ q.support:=by
          intro h
          rcases mem_union.mp (hqS u h) with h | h
          · exact (mem_erase.mp h).1 rfl
          · exact (Finset.disjoint_left.mp hdis hu) (mem_of_mem_erase h)
        have hyq:y ∉ q.support:=by
          intro h
          rcases mem_union.mp (hqS y h) with h | h
          · exact (Finset.disjoint_left.mp hdis (mem_of_mem_erase h)) hy
          · exact (mem_erase.mp h).1 rfl
        have huyne:u ≠ y:=fun h => (Finset.disjoint_left.mp hdis hu) (h ▸ hy)
        let p :G.Walk u v:=Walk.cons huy (Walk.cons hyx q)
        refine ⟨p,?_,?_,?_⟩
        · apply (Walk.cons_isPath_iff _ _).mpr
          refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hq,hyq⟩,?_⟩
          simpa only [Walk.support_cons,List.mem_cons,not_or] using ⟨huyne,huq⟩
        · simp only [p,Walk.length_cons,hqL]
          omega
        · intro z hz
          simp only [p,Walk.support_cons,List.mem_cons] at hz
          rcases hz with h | h | h
          · exact h ▸ mem_union_left Y hu
          · exact h ▸ mem_union_right X hy
          · exact (union_subset_union (erase_subset _ _) (erase_subset _ _)) (hqS z h)
theorem rt {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (L d :ℕ) (hL:2 ≤ L)
    (X Y :Finset V) (hdis:Disjoint X Y) (hdef:qi G X Y d)
    (hX:L+2*d ≤ X.card) (hY:L+2*d ≤ Y.card)
    (u v :V) (hu:u ∈ X) (hv:v ∈ Y) :
    ∃ p :G.Walk u v,p.IsPath ∧ p.length=2*L-1 ∧ ∀ z ∈ p.support,z ∈ X ∪ Y:=by
  classical
  obtain ⟨x,hx,hxu,hvx⟩ :=r6 G v X {u} d
    (hdef.right v hv) (by simp only [card_singleton];omega)
  have hux:u ≠ x:=by
    intro h
    exact hxu (by simp [h])
  have hY':L-1+2*d ≤ (Y.erase v).card:=by rw [card_erase_of_mem hv];omega
  obtain ⟨q,hq,hqL,hqS⟩ :=s8 G (L-1) d (by omega)
    X (Y.erase v) (hdis.mono_right (erase_subset _ _))
    (hdef.mono Subset.rfl (erase_subset _ _)) (by omega) hY' u x hu hx hux
  have hvq:v ∉ q.support:=by
    intro h
    rcases mem_union.mp (hqS v h) with h | h
    · exact (Finset.disjoint_left.mp hdis h) hv
    · exact (mem_erase.mp h).1 rfl
  refine ⟨q.concat hvx.symm,hq.concat hvq hvx.symm,?_,?_⟩
  · rw [Walk.length_concat,hqL]
    omega
  · intro z hz
    rw [Walk.support_concat,List.mem_append,List.mem_singleton] at hz
    rcases hz with h | h
    · exact (union_subset_union Subset.rfl (erase_subset _ _)) (hqS z h)
    · exact h ▸ mem_union_right X hv
end Erdos556
end bY
section bW
namespace Erdos556
open SimpleGraph
theorem yV {m:ℕ} {i j :Fin m} (hij:i.val < j.val) :
    (cycleGraph m).Adj i j ↔ i.val+1=j.val ∨ (i.val=0 ∧ j.val+1=m) :=by
  rw [cycleGraph_adj',Fin.coe_sub_iff_lt.mpr hij,Fin.sub_val_of_le hij.le]
  have hi:=i.isLt
  have hj:=j.isLt
  omega
theorem qX {V:Type*} (G:SimpleGraph V)
    (m:ℕ) (hm:3 ≤ m) (f:ℕ → V)
    (hinj:Set.InjOn f (Set.Iio m))
    (hadj: ∀ i,i+1 < m → G.Adj (f i) (f (i+1)))
    (hclose:G.Adj (f (m-1)) (f 0)) :
    ∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=m:=by
  have hf:Function.Injective (fun i :Fin m => f i.val) :=by
    intro i j hij
    exact Fin.ext (hinj i.isLt j.isLt hij)
  have hmap: ∀ i j:Fin m,(cycleGraph m).Adj i j → G.Adj (f i.val) (f j.val) :=by
    intro i j hij
    have hne:i.val ≠ j.val:=fun h => hij.ne (Fin.ext h)
    wlog hlt:i.val < j.val generalizing i j
    · exact (this j i hij.symm hne.symm (by omega)).symm
    rcases (yV hlt).mp hij with hnext | ⟨hzero,hlast⟩
    · simpa only [hnext] using hadj i.val (by omega)
    · have hlast':j.val=m-1:=by omega
      simpa only [hzero,hlast'] using hclose.symm
  apply (cycleGraph_isContained_iff (by omega:2 < m)).mp
  exact ⟨{ toHom:= { toFun:=fun i => f i.val,map_rel':=fun h => hmap _ _ h }
           injective':=hf}⟩
end Erdos556
end bW
section bj
namespace Erdos556
open SimpleGraph
theorem r2 {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (hlen:2 ≤ p.length) (h:G.Adj u v) :
    ∃ c :G.Walk u u,c.IsCycle ∧ c.length=p.length+1:=by
  let q :G.Walk u v:=Walk.cons h Walk.nil
  have hq:q.IsPath:=by simp [q,h.ne]
  refine ⟨p.append q.reverse,?_,?_⟩
  · apply qy p q hp hq (by omega)
    intro x _ hx
    simpa only [q,Walk.support_cons,Walk.support_nil,List.mem_cons,
      List.mem_singleton,List.not_mem_nil,or_false] using hx
  · simp [q]
def qq (j k :ℕ) : ℕ:=if k =0 then 0 else if k < j then j +1-k else k +1
theorem zB (m j k:ℕ) (hj:2 ≤ j) (hjm:j+1 < m) (hk:k < m-1) :
    qq j k < m:=by
  unfold qq
  split_ifs <;> omega
theorem y0 (j:ℕ) (_hj:2 ≤ j) : Function.Injective (qq
    j) :=by
  intro a b h
  unfold qq at h
  split_ifs at h <;> omega
end Erdos556
end bj
section bb
namespace Erdos556
open SimpleGraph Finset
theorem ro {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (X Y :Finset V) (r d :ℕ) (hr:1 ≤ r)
    (hdis:Disjoint X Y) (hdef:qi G X Y d)
    (hX:r+2*d+1 ≤ X.card) (hY:r+2*d ≤ Y.card)
    (hno: ¬ cycleGraph (2*r+1) ⊑ G) :
    ∀ u ∈ X,∀ v ∈ X,¬ G.Adj u v:=by
  intro u hu v hv huv
  obtain ⟨p,hp,hlen,_⟩ :=s8 G r d hr X Y hdis hdef hX hY
    u v hu hv huv.ne
  obtain ⟨c,hc,hclen⟩ :=r2 p hp (by omega) huv
  exact hno ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr ⟨u,c,hc,by omega⟩)
theorem rG {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (X Y :Finset V) (r d :ℕ) (hr:2 ≤ r)
    (hdis:Disjoint X Y) (hdef:qi G X Y d)
    (hX:r+2*d ≤ X.card) (hY:r+2*d ≤ Y.card)
    (hno: ¬ cycleGraph (2*r+1) ⊑ G)
    (x:V) (hxX:x ∉ X) (hxY:x ∉ Y)
    (u v :V) (hu:u ∈ X) (hv:v ∈ Y) : ¬ (G.Adj x u ∧ G.Adj x v) :=by
  rintro ⟨hxu,hxv⟩
  obtain ⟨p,hp,hlen,hsupp⟩ :=rt G r d hr X Y hdis hdef hX hY
    u v hu hv
  have hxp:x ∉ p.support:=by
    intro h
    rcases mem_union.mp (hsupp x h) with h | h
    · exact hxX h
    · exact hxY h
  obtain ⟨c,hc,hclen⟩ :=r2 (p.concat hxv.symm)
    (hp.concat hxp hxv.symm) (by rw [Walk.length_concat,hlen];omega) hxu.symm
  have hclen':c.length=2*r+1:=by
    rw [Walk.length_concat,hlen] at hclen
    omega
  exact hno ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr ⟨u,c,hc,hclen'⟩)
end Erdos556
end bb
section b9
namespace Erdos556
open SimpleGraph Finset
theorem rv.zz {V:Type*} [DecidableEq V]
    {c:q4 V} {r:ℕ} {η:ℝ} (h:rv c (2*r+1) η)
    (hr:1 ≤ r) (hη:η ≤ 1/100) (p:q1) (hp:0 < h.weight p) :
    r+2*h.defect+1 ≤ (h.sets p).card:=by
  have hw:1 ≤ h.weight p :=by
    rcases h.tiling.normalized p hp with ⟨_,he⟩ | ⟨_,he⟩ <;> norm_num [he]
  have hsize:=h.size_lower p
  have hd:=h.defect_le
  have hrR: (1:ℝ) ≤ r:=by exact_mod_cast hr
  have hn: (0:ℝ) ≤ 2*r+1:=by positivity
  have hws:=mul_le_mul_of_nonneg_right hw hn
  have hηs:=mul_le_mul_of_nonneg_right hη hn
  have hbound: (r:ℝ) + 2*h.defect+1 ≤ (h.sets p).card:=by
    push_cast at hsize hd
    nlinarith
  exact_mod_cast hbound
theorem rv.t8 {V:Type*} [DecidableEq V]
    {c:q4 V} {r:ℕ} {η:ℝ} (h:rv c (2*r+1) η)
    (hr:1 ≤ r) (hη:η ≤ 1/100)
    (hno: ∀ i,¬ cycleGraph (2*r+1) ⊑ c.graph i)
    (i:Fin 3) (b:Bool) (hp:0 < h.weight (cubeFace i b)) :
    ∀ u ∈ h.sets (cubeFace i b),∀ v ∈ h.sets (cubeFace i b),¬ (c.graph i).Adj u v:=by
  obtain ⟨q,hqp,hq,hsep⟩ :=h.tiling.af h.admissible i b hp
  apply ro (c.graph i) (h.sets (cubeFace i b)) (h.sets q)
    r h.defect hr (h.disjoint _ _ hqp.symm) (h.dense _ _ i hsep)
    (h.zz hr hη _ hp) _ (hno i)
  have hh:=h.zz hr hη q hq
  omega
end Erdos556
end b9
section c6
namespace Erdos556
open Finset
theorem tm: ∀ p:q1,q3 p =1 →
    ∃ a :Fin 3,∀ l:Fin 4,qc l ∈ q0 p →
      qu l a=p:=by decide
theorem xu: ∀ (p:q1) (l m :Fin 4),
    q3 p =1 → qc l ∈ q0 p →
      qc m ∈ q0 p → l =m:=by decide
theorem zw: ∀ (i a :Fin 3) (b:Bool) (l:Fin 4),
    a ≠ i → qc l ∈ q0 (cubeFace i b) →
      q0 (qu l a) ⊆ q0 (cubeFace i b) :=by decide
theorem yv: ∀ (i k :Fin 3) (b:Bool) (l m :Fin 4),
    k ≠ i → l ≠ m → qc l ∈ q0 (cubeFace i b) →
      qc m ∈ q0 (cubeFace i b) →
      qc l k ≠ qc m k:=by decide
theorem xv: ∀ (i a :Fin 3) (b:Bool) (l m :Fin 4),
    a ≠ i → l ≠ m → qc l ∈ q0 (cubeFace i b) →
      qc m ∈ q0 (cubeFace i b) →
      Disjoint (q0 (qu l a)) (q0 (qu m a)) :=by
        decide
theorem xM: ∀ (i a k z :Fin 3) (b:Bool) (l m :Fin 4),
    a ≠ i → k ≠ i → a ≠ k →
      qc l ∈ q0 (cubeFace i b) →
      qc m ∈ q0 (cubeFace i b) →
      q5 (qu l a) (qu m a) z → z =k:=by decide
theorem z7: ∀ p q:q1,
    Disjoint (q0 p) (q0 q) → ∃ i,qV p q i :=by decide
theorem rz: ∀ p p':q1,∀ (i:Fin 3) (b:Bool),
    q0 p' ⊆ q0 p → p i=some b → p' i =some b :=by decide
theorem um (p q p' q':q1) (i:Fin 3)
    (hp:q0 p' ⊆ q0 p) (hq:q0 q' ⊆ q0 q)
    (hopp:qV p q i) : qV p' q' i :=by
  rcases hopp with ⟨hp0,hq1⟩ | ⟨hp1,hq0⟩
  · exact Or.inl ⟨rz p p' i false hp hp0,
      rz q q' i true hq hq1⟩
  · exact Or.inr ⟨rz p p' i true hp hp1,
      rz q q' i false hq hq0⟩
theorem wp (p q p' q':q1) (i:Fin 3)
    (hdis:Disjoint (q0 p) (q0 q))
    (hp:q0 p' ⊆ q0 p) (hq:q0 q' ⊆ q0 q)
    (hsep:q5 p' q' i) : q5 p q i :=by
  obtain ⟨j,hj⟩ :=z7 p q hdis
  have hji:j=i:=by
    by_contra hji
    exact hsep.2 j hji (um p q p' q' j hp hq hj)
  subst j
  refine ⟨hj,?_⟩
  intro j hji hj
  exact hsep.2 j hji (um p q p' q' j hp hq hj)
end Erdos556
end c6
section bE
namespace Erdos556
open SimpleGraph Finset
theorem rY {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (L:ℕ) (hL:0 < L) (X Y :Finset V)
    (hXY:Disjoint X Y) (hcomplete: ∀ x ∈ X,∀ y ∈ Y,G.Adj x y)
    (hX:L ≤ X.card) (hY:L ≤ Y.card)
    (u v :V) (hu:u ∈ X) (hv:v ∈ Y) :
    ∃ p :G.Walk u v,p.IsPath ∧ p.length=2*L-1 ∧
      ∀ z ∈ p.support,z ∈ X ∪ Y:=by
  classical
  by_cases hL1:L=1
  · subst L
    let p := (hcomplete u hu v hv).toWalk
    refine ⟨p,Walk.IsPath.of_adj _,rfl,?_⟩
    intro z hz
    have hz':z=u ∨ z=v:=by simpa [p,SimpleGraph.Adj.toWalk] using hz
    exact hz'.elim (fun h => h ▸ mem_union_left _ hu) (fun h => h ▸ mem_union_right _ hv)
  · have hex: (X.erase u).Nonempty:=by
      apply card_pos.mp
      rw [card_erase_of_mem hu]
      omega
    obtain ⟨x,hx⟩ :=hex
    have hxX:=mem_of_mem_erase hx
    have hux:u ≠ x:= (mem_erase.mp hx).1.symm
    have hY':L-1 ≤ (Y.erase v).card:=by rw [card_erase_of_mem hv];omega
    obtain ⟨q,hq,hqL,hqS⟩ :=rf G (L-1) (by omega)
      X (Y.erase v) (hXY.mono_right (erase_subset _ _))
      (fun a ha b hb=> hcomplete a ha b (mem_of_mem_erase hb)) (by omega) hY' u x hu hxX hux
    have hvq:v ∉ q.support:=by
      intro hvq
      rcases mem_union.mp (hqS v hvq) with hvX | hvY
      · exact Finset.disjoint_left.mp hXY hvX hv
      · exact (mem_erase.mp hvY).1 rfl
    refine ⟨q.concat (hcomplete x hxX v hv),hq.concat hvq _,?_,?_⟩
    · rw [Walk.length_concat,hqL]
      omega
    · intro z hz
      rw [Walk.support_concat,List.mem_append,List.mem_singleton] at hz
      rcases hz with hzq | hzv
      · exact (union_subset_union (Subset.refl X) (erase_subset _ _)) (hqS z hzq)
      · exact hzv ▸ mem_union_right X hv
theorem vw {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (L:ℕ) (hL:2 ≤ L) (X Y :Finset V)
    (hXY:Disjoint X Y) (hcomplete: ∀ x ∈ X,∀ y ∈ Y,G.Adj x y)
    (hX:L ≤ X.card) (hY:L ≤ Y.card) :
    ∃ (u:V) (c:G.Walk u u),c.IsCycle ∧ c.length=2*L ∧
      ∀ z ∈ c.support,z ∈ X ∪ Y:=by
  classical
  obtain ⟨u,hu⟩ :=card_pos.mp (show 0 < X.card by omega)
  obtain ⟨v,hv⟩ :=card_pos.mp (show 0 < Y.card by omega)
  obtain ⟨p,hp,hpL,hpS⟩ :=rY G L (by omega) X Y
    hXY hcomplete hX hY u v hu hv
  let q := (hcomplete u hu v hv).toWalk
  have hq:q.IsPath:=Walk.IsPath.of_adj _
  have hqS (z:V) (hz:z ∈ q.support) : z=u ∨ z=v:=by
    simpa [q,SimpleGraph.Adj.toWalk] using hz
  refine ⟨u,p.append q.reverse,
    qy p q hp hq (by omega) (fun z _ hz=> hqS z hz),?_,?_⟩
  · simp only [Walk.length_append,Walk.length_reverse,q,SimpleGraph.Adj.toWalk,
      Walk.length_cons,Walk.length_nil,hpL]
    omega
  · intro z hz
    rcases (Walk.mem_support_append_iff p q.reverse).mp hz with hzp | hzq
    · exact hpS z hzp
    · have hzq':z ∈ q.support:=by simpa only [Walk.support_reverse,List.mem_reverse] using hzq
      rcases hqS z hzq' with hzu | hzv
      · exact hzu ▸ mem_union_left _ hu
      · exact hzv ▸ mem_union_right _ hv
end Erdos556
end bE
section c3
namespace Erdos556
open SimpleGraph Finset
theorem sP {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (L b :ℕ) (hL:2 ≤ L)
    (hdegree: ∀ v,L+b ≤ G.degree v) (hno: ¬ cycleGraph (2*L) ⊑ Gᶜ) :
    q8 G b:=by
  classical
  intro S hS
  by_contra hdisc
  obtain ⟨A,B,hA,hB,hAB,_,_,hcover,hcross⟩ :=
    rk G S hdisc
  obtain ⟨a,ha⟩ :=hA
  obtain ⟨b₀,hb₀⟩ :=hB
  have hAcard:L ≤ A.card:=by
    have hd:=qR G A B S hcover hcross a ha
    have hmin:=hdegree a
    omega
  have hBcard:L ≤ B.card:=by
    have hcover':B ∪ A ∪ S=univ:=by rw [union_comm B A];exact hcover
    have hcross': ∀ u ∈ B,∀ v ∈ A,¬ G.Adj u v:=
      fun u hu v hv huv=> hcross v hv u hu huv.symm
    have hd:=qR G B A S hcover' hcross' b₀ hb₀
    have hmin:=hdegree b₀
    omega
  have hcomplete (u:V) (hu:u ∈ A) (v:V) (hv:v ∈ B) : Gᶜ.Adj u v:=by
    rw [compl_adj]
    refine ⟨?_,hcross u hu v hv⟩
    intro h
    exact Finset.disjoint_left.mp hAB hu (h ▸ hv)
  obtain ⟨u,c,hc,hlen,_⟩ :=vw Gᶜ L hL A B hAB
    hcomplete hAcard hBcard
  exact hno ((cycleGraph_isContained_iff (by omega)).mpr ⟨u,c,hc,hlen⟩)
end Erdos556
end c3
section aP
namespace Erdos556
open SimpleGraph Finset
theorem vc {V:Type*} {G:SimpleGraph V}
    {u v :V} (p:G.Walk u v) (hp:p.IsPath) (hlen:1 < p.length)
    (K:ℕ) (R:Finset V) (hoff: ∀ x ∈ p.support,x ∉ R)
    (hconn:qY G K u v R) :
    ∃ c :G.Walk u u,c.IsCycle ∧ p.length+1 ≤ c.length:=by
  obtain ⟨q,hq,_,hqR⟩ :=hconn
  have huv:u ≠ v:=by
    intro h
    have hz:= (hp.nil_iff_eq.mpr h).length_eq_zero
    omega
  have hqpos:0 < q.length:=Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne huv)
  have hc: (p.append q.reverse).IsCycle:=by
    apply qy p q hp hq hlen
    intro x hxp hxq
    by_cases hxu:x=u
    · exact Or.inl hxu
    by_cases hxv:x=v
    · exact Or.inr hxv
    exact (hoff x hxp (hqR x hxq hxu hxv)).elim
  refine ⟨p.append q.reverse,hc,?_⟩
  simp only [Walk.length_append,Walk.length_reverse]
  omega
theorem xQ {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (L b K:ℕ) (hL:2 ≤ L)
    (R:Finset V) (hR:R.card ≤ b) (hconn:q8 G b)
    (hdegree: ∀ v,L+R.card ≤ G.degree v)
    (hN:2*L+R.card ≤ Fintype.card V)
    (hres: ∀ u v,qY G K u v R) :
    ∃ (u:V) (c:G.Walk u u),c.IsCycle ∧ 2*L ≤ c.length:=by
  classical
  let U := (R:Set V)ᶜ
  have hRc:Fintype.card (R:Set V) = R.card:=by
    calc
      Fintype.card (R:Set V) = (R:Set V).ncard:=Nat.card_eq_fintype_card.symm
      _=R.card:=Set.ncard_coe_finset R
  have hUc:Fintype.card U =Fintype.card V -R.card:=by
    simp only [U,Fintype.card_compl_set,hRc]
  have hUlarge:2*L ≤ Fintype.card U :=by omega
  let:Nonempty U :=Fintype.card_pos_iff.mp (by omega)
  have hc: (G.induce U).Connected:= ⟨hconn R hR⟩
  have hdeg (v:U) : L ≤ (G.induce U).degree v :=by
    have h :=qW G R v
    have hg:=hdegree v.val
    change G.degree v.val ≤ (G.induce U).degree v +R.card at h
    omega
  obtain ⟨u,v,p,hp,hlen⟩ :=ur (G.induce U) hc L hL hdeg
  let f :G.induce U ↪g G :=SimpleGraph.Embedding.induce U
  have hp': (p.map f.toHom).IsPath:=hp.map f.injective
  have hplen:1 < (p.map f.toHom).length:=by rw [Walk.length_map];omega
  have hoff (x:V) (hx:x ∈ (p.map f.toHom).support) : x ∉ R:=by
    rw [Walk.support_map,List.mem_map] at hx
    obtain ⟨y,_,hyx⟩ :=hx
    exact hyx ▸ y.property
  obtain ⟨c,hcyc,hclen⟩ :=vc (p.map f.toHom) hp' hplen
    K R hoff (hres (f u) (f v))
  refine ⟨f u,c,hcyc,?_⟩
  rw [Walk.length_map] at hclen
  omega
end Erdos556
end aP
section bc
namespace Erdos556
open SimpleGraph Finset
theorem uI (D B :ℕ) (hD:0 < D) (hB:0 < B) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (L b :ℕ),
      N₀ ≤ Fintype.card V → 2 ≤ L → Fintype.card V ≤ D *L →
      Fintype.card V ≤ B *b → (∀ v,L+b ≤ G.degree v) →
      ¬ cycleGraph (2*L) ⊑ Gᶜ →
      (∀ (z:V) (c:G.Walk z z),c.IsCycle → c.length < 2*L) →
      Fintype.card V < 2 *L+b:=by
  have hBR: (0:ℝ) < B:=by exact_mod_cast hB
  let q :ℝ:=1/ (2*B)
  have hq:0 < q:=by dsimp [q];positivity
  have hq1:q ≤ 1:=by
    dsimp [q]
    apply (div_le_iff₀ (by positivity: (0:ℝ) < 2*B)).mpr
    have hBR1: (1:ℝ) ≤ B:=by exact_mod_cast hB
    linarith
  obtain ⟨N₀,hN₀⟩ :=sh D B 0 hD hB q hq hq1
  refine ⟨N₀,?_⟩
  intro V _ _ G _ L b hN hL hscale hbudget hdegree hcomp hcycles
  classical
  have hc:=sP G L b hL hdegree hcomp
  obtain ⟨R,hRsize,hres⟩ :=hN₀ G b L hN hc hdegree hscale hbudget
  have hR:R.card ≤ b:=by
    have hbR: (Fintype.card V :ℝ) ≤ (B:ℝ) * b:=by exact_mod_cast hbudget
    have hquot: (Fintype.card V :ℝ) / B ≤ b:= (div_le_iff₀ hBR).mpr (by nlinarith only [hbR])
    have heq:2*q*Fintype.card V = (Fintype.card V :ℝ) / B:=by
      dsimp [q]
      field_simp
    rw [heq] at hRsize
    exact_mod_cast hRsize.trans hquot
  have hres' (u v :V) : qY G (3*D) u v R :=by
    have h :=hres u v ∅ (by simp)
    simpa only [sdiff_empty] using h
  by_contra hlarge
  have hdegR (v:V) : L+R.card ≤ G.degree v :=by
    have h :=hdegree v
    omega
  obtain ⟨z,c,hcyc,hclen⟩ :=xQ G L b (3*D) hL R hR hc
    hdegR (by omega) hres'
  exact (hcycles z c hcyc).not_ge hclen
end Erdos556
end bc
section bx
namespace Erdos556
open SimpleGraph Finset
theorem wU {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (d:ℝ) (a:ℕ) (ha:a ≤ Fintype.card V) :
    ∃ S :Finset V,a ≤ S.card ∧
      (G.edgeFinset.card:ℝ) - d*Fintype.card V ≤
        ((G.induce (S:Set V)).edgeFinset.card:ℝ) - d*S.card ∧
      (S.card=a ∨ ∀ v:S,d < (G.induce (S:Set V)).degree v) :=by
  classical
  let excess (S:Finset V) : ℝ:=
    ((G.induce (S:Set V)).edgeFinset.card:ℝ) - d*S.card
  let baseline:ℝ:= (G.edgeFinset.card:ℝ) - d*Fintype.card V
  let good:Finset (Finset V) :=univ.filter fun S => a ≤ S.card ∧ baseline ≤ excess S
  have huniv: (univ:Finset V) ∈ good:=by
    have he: (G.induce (↑(univ:Finset V) : Set V)).edgeFinset.card=G.edgeFinset.card:=by
      rw [← G.card_filter_edgeFinset_toFinset_subset univ]
      simp
    simp [good,excess,baseline,he,ha]
  obtain ⟨S,hS,hminimal⟩ :=good.exists_min_image Finset.card ⟨_,huniv⟩
  obtain ⟨hSa,hgood⟩ := (mem_filter.mp hS).2
  refine ⟨S,hSa,hgood,?_⟩
  by_cases hcardeq:S.card=a
  · exact Or.inl hcardeq
  right
  intro v
  by_contra hdegree
  have hdegree': ((G.induce (S:Set V)).degree v :ℝ) ≤ d:=le_of_not_gt hdegree
  let T :=S.erase v.val
  have hcard:T.card+1=S.card:=card_erase_add_one v.property
  have hedge:=rN G S v
  have hedgeR: ((G.induce (T:Set V)).edgeFinset.card:ℝ) +
      (G.induce (S:Set V)).degree v = (G.induce (S:Set V)).edgeFinset.card:=by
        exact_mod_cast hedge
  have hcardR: (T.card:ℝ) + 1=S.card:=by exact_mod_cast hcard
  have hT:T ∈ good:=by
    apply mem_filter.mpr
    refine ⟨mem_univ _,by omega,?_⟩
    dsimp [excess] at hgood ⊢
    nlinarith
  have hle:=hminimal T hT
  omega
end Erdos556
end bx
section bv
namespace Erdos556
open SimpleGraph
def qK {V:Type*} (G:SimpleGraph V) (m:ℕ) : Prop:=
  ∀ (v:V) (c:G.Walk v v),c.IsCycle → c.length < m
theorem qK.of_embedding {V W :Type*} {G:SimpleGraph V} {H:SimpleGraph W}
    {m:ℕ} (hH:qK H m) (f:G ↪g H) : qK G m:=by
  intro v c hc
  have h :=hH (f v) (c.map f.toHom) (hc.map f.injective)
  simpa only [Walk.length_map] using h
theorem qK.induce {V:Type*} {G:SimpleGraph V} {m:ℕ}
    (hG:qK G m) (S:Set V) : qK (G.induce S) m :=
  hG.of_embedding (SimpleGraph.Embedding.induce S)
def yy {V:Type*} (G:SimpleGraph V) (S:Set V) :
    (G.induce S)ᶜ ↪g Gᶜ where
  toFun:=Subtype.val
  inj':=Subtype.val_injective
  map_rel_iff':=by
    intro x y
    change Gᶜ.Adj x.val y.val ↔ (G.induce S)ᶜ.Adj x y
    simp only [compl_adj,induce_adj,ne_eq,Subtype.coe_inj]
theorem qK.yB {V:Type*} {G:SimpleGraph V} {m:ℕ}
    (hG:qK Gᶜ m) (S:Set V) : qK (G.induce S)ᶜ m :=
  hG.of_embedding (yy G S)
theorem qK.eb {V:Type*} {G:SimpleGraph V} {m:ℕ}
    (hG:qK G m) (n:ℕ) (hn:3 ≤ n) (hmn:m ≤ n) : ¬ cycleGraph n ⊑ G :=by
  intro h
  obtain ⟨v,c,hc,hlen⟩ := (cycleGraph_isContained_iff (by omega)).mp h
  have hshort:=hG v c hc
  omega
end Erdos556
end bv
section bd
namespace Erdos556
open SimpleGraph Finset
theorem vS (D B :ℕ) (hD:0 < D) (hB:0 < B) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (L b :ℕ),
      N₀ ≤ L → 2 ≤ L → L+b+1 ≤ Fintype.card V →
      Fintype.card V ≤ D *L → Fintype.card V ≤ B *b →
      qK G (2*L) → qK Gᶜ (2*L) →
      ∃ S :Finset V,L+b+1 ≤ S.card ∧ S.card ≤ 2*L+b ∧
        (G.edgeFinset.card:ℝ) - (L+b:ℕ) * Fintype.card V ≤
          ((G.induce (S:Set V)).edgeFinset.card:ℝ) - (L+b:ℕ) * S.card:=by
  obtain ⟨N₀,hN₀⟩ :=uI D B hD hB
  refine ⟨N₀,?_⟩
  intro V _ _ G _ L b hLlarge hL hfloor hscale hbudget hG hGc
  classical
  obtain ⟨S,hSfloor,hSenergy,hSstop⟩ :=wU G
    ((L+b:ℕ) : ℝ) (L+b+1) hfloor
  refine ⟨S,hSfloor,?_,hSenergy⟩
  rcases hSstop with hstop | hmin
  · omega
  · have hSc:Fintype.card (S:Set V) = S.card:=by
      calc
        Fintype.card (S:Set V) = (S:Set V).ncard:=Nat.card_eq_fintype_card.symm
        _=S.card:=Set.ncard_coe_finset S
    have hScN:=card_le_univ S
    have hdegree (v: (S:Set V)) : L+b ≤ (G.induce (S:Set V)).degree v :=by
      have h :L+b < (G.induce (S:Set V)).degree v :=by exact_mod_cast hmin v
      exact h.le
    have hshort:=hG.induce (S:Set V)
    have hcomp:= (hGc.yB (S:Set V)).eb (2*L) (by omega) le_rfl
    have hbound:=hN₀ (G.induce (S:Set V)) L b (by omega) hL (by omega) (by omega)
      hdegree hcomp hshort
    omega
end Erdos556
end bd
section c2
namespace Erdos556
theorem xn (L b s:ℝ) (_hL:0 ≤ L)
    (hslo:L+b+1 ≤ s) (hshi:s ≤ 2*L+b) :
    L* (2*L+b-s) ≤
      ((2*L+b) ^ 2- (2* (L+b) + 1) * (2*L+b)) -
        (s^2- (2* (L+b) + 1) * s) :=by
  have h :=mul_nonneg (sub_nonneg.mpr hshi) (sub_nonneg.mpr hslo)
  nlinarith
theorem yN (L b N:ℝ) (hL:0 ≤ L) (hb:1 ≤ b)
    (hNlo:4*L-b ≤ N) (hNhi:N ≤ 4*L) :
    4* (L+b) * N+
      2* ((2*L+b) ^ 2- (2* (L+b) + 1) * (2*L+b)) - N^2+N ≤ 24*b*L:=by
  have hδ0:0 ≤ 4* (L+b) - N:=by linarith
  have hδ:4* (L+b) - N ≤ 5*b:=by linarith
  have hmul:=mul_le_mul hNhi hδ hδ0 (by positivity: (0:ℝ) ≤ 4*L)
  have hterm:0 ≤ (2*L+b) * (b+1) :=by positivity
  have hbL:=mul_le_mul_of_nonneg_right hb hL
  nlinarith
theorem vM (L b N s t e f eS eT:ℝ)
    (hL:0 < L) (hb:1 ≤ b)
    (hNlo:4*L-b ≤ N) (hNhi:N ≤ 4*L)
    (hslo:L+b+1 ≤ s) (hshi:s ≤ 2*L+b)
    (htlo:L+b+1 ≤ t) (hthi:t ≤ 2*L+b)
    (hcount:2* (e+f) = N* (N-1))
    (he:e- (L+b) * N ≤ eS- (L+b) * s)
    (hf:f- (L+b) * N ≤ eT- (L+b) * t)
    (heS:2*eS ≤ s* (s-1)) (heT:2*eT ≤ t* (t-1)) :
    2*L-24*b ≤ s ∧ 2*L-24*b ≤ t ∧
      s* (s-1) - 2*eS ≤ 24*b*L ∧ t* (t-1) - 2*eT ≤ 24*b*L:=by
  have hs:=xn L b s hL.le hslo hshi
  have ht:=xn L b t hL.le htlo hthi
  have hcap:=yN L b N hL.le hb hNlo hNhi
  have htotal:L* (2*L+b-s) + L* (2*L+b-t) +
      (s* (s-1) - 2*eS) + (t* (t-1) - 2*eT) ≤ 24*b*L:=by
    nlinarith only [hs,ht,hcap,hcount,he,hf]
  have hsnon:0 ≤ L* (2*L+b-s) :=mul_nonneg hL.le (sub_nonneg.mpr hshi)
  have htnon:0 ≤ L* (2*L+b-t) :=mul_nonneg hL.le (sub_nonneg.mpr hthi)
  have hsbound:L* (2*L+b-s) ≤ L* (24*b) :=by nlinarith only [htotal,htnon,heS,heT]
  have htbound:L* (2*L+b-t) ≤ L* (24*b) :=by nlinarith only [htotal,hsnon,heS,heT]
  have hs':= (mul_le_mul_iff_right₀ hL).mp hsbound
  have ht':= (mul_le_mul_iff_right₀ hL).mp htbound
  refine ⟨by linarith,by linarith,?_,?_⟩ <;> nlinarith only [htotal,hsnon,htnon,heS,heT]
end Erdos556
end c2
section b6
namespace Erdos556
open SimpleGraph Finset
theorem vQ (B:ℕ) (hB:0 < B) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (L b :ℕ),
      N₀ ≤ L → 2 ≤ L → 1 ≤ b → b ≤ L →
      4*L ≤ Fintype.card V +b → Fintype.card V ≤ 4 *L → Fintype.card V ≤ B *b →
      qK G (2*L) → qK Gᶜ (2*L) →
      ∃ S T:Finset V,
        2*L ≤ S.card+24*b ∧ S.card ≤ 2*L+b ∧
        2*L ≤ T.card+24*b ∧ T.card ≤ 2*L+b ∧
        ((Gᶜ.induce (S:Set V)).edgeFinset.card:ℝ) ≤ 12* (b:ℝ) * L ∧
        ((G.induce (T:Set V)).edgeFinset.card:ℝ) ≤ 12* (b:ℝ) * L:=by
  obtain ⟨N₀,hN₀⟩ :=vS 4 B (by decide) hB
  refine ⟨N₀,?_⟩
  intro V _ _ G _ L b hLlarge hL hb hbL hNlo hNhi hbudget hG hGc
  classical
  have hfloor:L+b+1 ≤ Fintype.card V :=by omega
  obtain ⟨S,hSlo,hShi,heS⟩ :=hN₀ G L b hLlarge hL hfloor hNhi hbudget hG hGc
  obtain ⟨T,hTlo,hThi,heT⟩ :=hN₀ Gᶜ L b hLlarge hL hfloor hNhi hbudget hGc
    (by simpa only [compl_compl] using hG)
  have hcard (U:Finset V) : Fintype.card (U:Set V) = U.card:=by
    calc
      Fintype.card (U:Set V) = (U:Set V).ncard:=Nat.card_eq_fintype_card.symm
      _=U.card:=Set.ncard_coe_finset U
  have hSe:=uh (G.induce (S:Set V))
  have hTe:=uh (Gᶜ.induce (T:Set V))
  rw [hcard S] at hSe
  rw [hcard T] at hTe
  have hNloR:4* (L:ℝ) - b ≤ Fintype.card V :=by
    have h :4* (L:ℝ) ≤ (Fintype.card V :ℝ) + b:=by exact_mod_cast hNlo
    linarith
  have heSR: (G.edgeFinset.card:ℝ) - ((L:ℝ) + b) * Fintype.card V ≤
      ((G.induce (S:Set V)).edgeFinset.card:ℝ) - ((L:ℝ) + b) * S.card:=by
    simpa only [Nat.cast_add] using heS
  have heTR: (Gᶜ.edgeFinset.card:ℝ) - ((L:ℝ) + b) * Fintype.card V ≤
      ((Gᶜ.induce (T:Set V)).edgeFinset.card:ℝ) - ((L:ℝ) + b) * T.card:=by
    simpa only [Nat.cast_add] using heT
  obtain ⟨hs,ht,hmissS,hmissT⟩ :=vM
    (L:ℝ) b (Fintype.card V) S.card T.card G.edgeFinset.card Gᶜ.edgeFinset.card
    (G.induce (S:Set V)).edgeFinset.card (Gᶜ.induce (T:Set V)).edgeFinset.card
    (by exact_mod_cast (show 0 < L by omega)) (by exact_mod_cast hb)
    hNloR (by exact_mod_cast hNhi) (by exact_mod_cast hSlo) (by exact_mod_cast hShi)
    (by exact_mod_cast hTlo) (by exact_mod_cast hThi)
    (rn G) heSR heTR hSe hTe
  have hsN:2*L ≤ S.card+24*b:=by
    exact_mod_cast (show 2 * (L:ℝ) ≤ (S.card:ℝ) + 24*b by linarith only [hs])
  have htN:2*L ≤ T.card+24*b:=by
    exact_mod_cast (show 2 * (L:ℝ) ≤ (T.card:ℝ) + 24*b by linarith only [ht])
  have hisoS: (G.induce (S:Set V))ᶜ ≃g Gᶜ.induce (S:Set V) :=by
    rw [z9]
  have hisoT: (Gᶜ.induce (T:Set V))ᶜ ≃g G.induce (T:Set V) :=by
    rw [z9,compl_compl]
  have hcountS:=rn (G.induce (S:Set V))
  have hcountT:=rn (Gᶜ.induce (T:Set V))
  rw [hisoS.card_edgeFinset_eq,hcard S] at hcountS
  rw [hisoT.card_edgeFinset_eq,hcard T] at hcountT
  exact ⟨S,T,hsN,hShi,htN,hThi,by nlinarith only [hcountS,hmissS],
    by nlinarith only [hcountT,hmissT]⟩
end Erdos556
end b6
section bJ
namespace Erdos556
open SimpleGraph Finset
theorem wQ {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A S :Finset V) (d:ℕ)
    (hAS:A ⊆ S)
    (hcore: ∀ v ∈ S,S.card ≤ (G.neighborFinset v ∩ S).card+d) :
    ∀ v ∈ A,A.card ≤ (G.neighborFinset v ∩ A).card+d:=by
  intro v hv
  have hS:=r1 G S v (hAS hv)
  have hA:=r1 G A v hv
  have hc:=hcore v (hAS hv)
  have hm: (Gᶜ.neighborFinset v ∩ A).card ≤ (Gᶜ.neighborFinset v ∩ S).card:=
    card_le_card (inter_subset_inter_left hAS)
  omega
theorem vv {V:Type*} [Fintype V]
    [DecidableEq V] (G:SimpleGraph V) [DecidableRel G.Adj]
    (A B S T :Finset V) (r:ℕ) (hAS:A ⊆ S) (hBT:B ⊆ T)
    (hA: ∀ v ∈ A,(Gᶜ.neighborFinset v ∩ S).card ≤ r)
    (hB: ∀ v ∈ B,(G.neighborFinset v ∩ T).card ≤ r) :
    (A ∩ B).card ≤ 2*r+1:=by
  classical
  by_cases hne: (A ∩ B).Nonempty
  · obtain ⟨v,hv⟩ :=hne
    have h :=r1 G (A ∩ B) v hv
    have hred: (G.neighborFinset v ∩ (A ∩ B)).card ≤ r:=by
      apply (card_le_card (inter_subset_inter_left
        ((inter_subset_right:A ∩ B ⊆ B).trans hBT))).trans
      exact hB v (mem_inter.mp hv).2
    have hblue: (Gᶜ.neighborFinset v ∩ (A ∩ B)).card ≤ r:=by
      apply (card_le_card (inter_subset_inter_left
        ((inter_subset_left:A ∩ B ⊆ A).trans hAS))).trans
      exact hA v (mem_inter.mp hv).1
    omega
  · rw [not_nonempty_iff_eq_empty.mp hne,card_empty]
    omega
theorem zL {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S T :Finset V) (r t :ℕ)
    (hr:0 < r)
    (hS:2* (Gᶜ.induce (S:Set V)).edgeFinset.card ≤ r*t)
    (hT:2* (G.induce (T:Set V)).edgeFinset.card ≤ r*t) :
    ∃ A B:Finset V,A ⊆ S ∧ B ⊆ T ∧ Disjoint A B ∧
      S.card ≤ A.card+t+2*r+1 ∧ T.card ≤ B.card+t ∧
      (∀ v ∈ A,A.card ≤ (G.neighborFinset v ∩ A).card+ (r+1)) ∧
      (∀ v ∈ B,B.card ≤ (Gᶜ.neighborFinset v ∩ B).card+ (r+1)) :=by
  classical
  obtain ⟨A,hAS,hAbad,hA⟩ :=vk Gᶜ S r
  obtain ⟨B,hBT,hBbad,hB⟩ :=vk G T r
  have hAloss:S.card-A.card ≤ t:=Nat.le_of_mul_le_mul_left (hAbad.trans hS) hr
  have hBloss:T.card-B.card ≤ t:=Nat.le_of_mul_le_mul_left (hBbad.trans hT) hr
  have hinter:=vv G A B S T r hAS hBT hA hB
  have hdis:Disjoint (A \ B) B :=Finset.disjoint_left.mpr fun _ hv=> (mem_sdiff.mp hv).2
  refine ⟨A \ B,B,sdiff_subset.trans hAS,hBT,hdis,?_,?_,?_,?_⟩
  · have hcard:=card_sdiff_add_card_inter A B
    omega
  · omega
  · apply sL G (A \ B) S r (sdiff_subset.trans hAS)
    intro v hv
    exact hA v (mem_sdiff.mp hv).1
  · apply sL Gᶜ B T r hBT
    intro v hv
    have heq:Gᶜᶜ.neighborFinset v =G.neighborFinset v :=by ext w;simp
    rw [heq]
    exact hB v hv
end Erdos556
end bJ
section bI
namespace Erdos556
open SimpleGraph Finset
theorem ss {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A:Finset V) (v:V) :
    (G.neighborFinset v ∩ A).card= ∑ u ∈ A,if G.Adj v u then 1 else 0 :=by
  rw [sum_boole]
  congr 1
  ext u
  simp only [mem_inter,mem_neighborFinset,mem_filter,and_comm]
theorem tI {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A B :Finset V) :
    ∑ v ∈ B,(G.neighborFinset v ∩ A).card=
      ∑ u ∈ A,(G.neighborFinset u ∩ B).card:=by
  simp_rw [ss]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  simp only [G.adj_comm]
theorem zN {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A B :Finset V) (hdis:Disjoint A B) :
    (∑ v ∈ B,(G.neighborFinset v ∩ A).card) +
      (∑ u ∈ A,(Gᶜ.neighborFinset u ∩ B).card) = A.card*B.card:=by
  classical
  rw [tI G A B,← sum_add_distrib]
  have hsum (u:V) (hu:u ∈ A) :
      (G.neighborFinset u ∩ B).card+ (Gᶜ.neighborFinset u ∩ B).card=B.card:=by
    rw [ss,ss,← sum_add_distrib]
    calc
      (∑ v ∈ B,((if G.Adj u v then 1 else 0) +
        if Gᶜ.Adj u v then 1 else 0)) = ∑ _v ∈ B,1:=by
        apply sum_congr rfl
        intro v hv
        have huv:u ≠ v:=fun h => (Finset.disjoint_left.mp hdis hu) (h ▸ hv)
        by_cases h :G.Adj u v <;> simp [compl_adj,huv,h]
      _=B.card:=by simp
  simp_rw [sum_congr rfl hsum]
  simp
theorem vG {V:Type*}
    (B:Finset V) (f:V → ℕ) (a k :ℕ) (hmax: ∀ v ∈ B,f v ≤ a)
    (hgood: (B.filter (fun v => k +1 ≤ f v)).card ≤ k) :
    ∑ v ∈ B,f v ≤ k* (a+B.card) :=by
  classical
  let C :=B.filter (fun v => k +1 ≤ f v)
  have hCB:C ⊆ B:=filter_subset _ _
  have hC: ∑ v ∈ C,f v ≤ C.card*a:=by
    calc
      _ ≤ ∑ _v ∈ C,a:=sum_le_sum fun v hv=> hmax v (hCB hv)
      _=_:=by simp
  have hD: ∑ v ∈ B \ C,f v ≤ (B \ C).card*k:=by
    calc
      _ ≤ ∑ _v ∈ B \ C,k:=by
        apply sum_le_sum
        intro v hv
        have hn: ¬ k+1 ≤ f v:=by
          intro h
          exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1,h⟩)
        omega
      _=_:=by simp
  have hc:C.card ≤ k:=hgood
  have hd: (B \ C).card ≤ B.card:=card_le_card sdiff_subset
  have hs:=sum_sdiff hCB (f:=f)
  have hm₁:=Nat.mul_le_mul_right a hc
  have hm₂:=Nat.mul_le_mul_right k hd
  nlinarith
theorem zR {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A B :Finset V) (a k :ℕ)
    (hdis:Disjoint A B) (hA:A.card=a) (hB:B.card=a) (hsize:4*k < a) :
    (∃ W ⊆ B,W.card=k ∧ ∀ v ∈ W,k+1 ≤ (G.neighborFinset v ∩ A).card) ∨
    (∃ W ⊆ A,W.card=k ∧ ∀ v ∈ W,k+1 ≤ (Gᶜ.neighborFinset v ∩ B).card) :=by
  classical
  let R :=B.filter (fun v => k +1 ≤ (G.neighborFinset v ∩ A).card)
  let C :=A.filter (fun v => k +1 ≤ (Gᶜ.neighborFinset v ∩ B).card)
  by_cases hR:k ≤ R.card
  · obtain ⟨W,hWR,hW⟩ :=exists_subset_card_eq hR
    exact Or.inl ⟨W,hWR.trans (filter_subset _ _),hW,
      fun v hv=> (mem_filter.mp (hWR hv)).2⟩
  by_cases hC:k ≤ C.card
  · obtain ⟨W,hWC,hW⟩ :=exists_subset_card_eq hC
    exact Or.inr ⟨W,hWC.trans (filter_subset _ _),hW,
      fun v hv=> (mem_filter.mp (hWC hv)).2⟩
  have hred:=vG B
    (fun v => (G.neighborFinset v ∩ A).card) a k
    (fun v _=> (card_le_card inter_subset_right).trans hA.le)
    (show R.card ≤ k by omega)
  have hblue:=vG A
    (fun v => (Gᶜ.neighborFinset v ∩ B).card) a k
    (fun v _=> (card_le_card inter_subset_right).trans hB.le)
    (show C.card ≤ k by omega)
  have hsum:=zN G A B hdis
  rw [hB] at hred
  rw [hA] at hblue
  rw [hA,hB] at hsum
  have ha:0 < a:=by omega
  exfalso
  nlinarith
end Erdos556
end bI
section b1
namespace Erdos556
open SimpleGraph Finset
theorem x1 {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A B :Finset V) (a k d:ℕ)
    (hdis:Disjoint A B) (hA:a ≤ A.card) (hB:a ≤ B.card)
    (hlarge:4*k < a) (hsize:k+2*d ≤ a) (hN:3 ≤ a+k)
    (hred: ∀ v ∈ A,A.card ≤ (G.neighborFinset v ∩ A).card+d)
    (hblue: ∀ v ∈ B,B.card ≤ (Gᶜ.neighborFinset v ∩ B).card+d) :
    (∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=a+k) ∨
    (∃ (v:V) (c:Gᶜ.Walk v v),c.IsCycle ∧ c.length=a+k) :=by
  classical
  obtain ⟨A',hA'A,hA'⟩ :=exists_subset_card_eq hA
  obtain ⟨B',hB'B,hB'⟩ :=exists_subset_card_eq hB
  have hdis':Disjoint A' B':=hdis.mono hA'A hB'B
  have hred':=wQ G A' A d hA'A hred
  have hblue':=wQ Gᶜ B' B d hB'B hblue
  rcases zR G A' B' a k hdis' hA' hB' hlarge with
    ⟨W,hWB,hW,hgood⟩ | ⟨W,hWA,hW,hgood⟩
  · left
    obtain ⟨v,c,hc,hlen⟩ :=sr G A' W d
      (hdis'.mono_right hWB) (by omega) (by omega) hred'
      (fun v hv=> by simpa only [hW] using hgood v hv)
    exact ⟨v,c,hc,by omega⟩
  · right
    obtain ⟨v,c,hc,hlen⟩ :=sr Gᶜ B' W d
      (hdis'.symm.mono_right hWA) (by omega) (by omega) hblue'
      (fun v hv=> by simpa only [hW] using hgood v hv)
    exact ⟨v,c,hc,by omega⟩
end Erdos556
end b1
section bO
namespace Erdos556
theorem ag (L b :ℕ) (hL:200 ≤ L) (hb:1 ≤ b)
    (hsmall:100000*b ≤ L) :
    0 < L/100 ∧
    24*b*L ≤ (L/100) * (L/10) ∧
    24*b+L/10+2* (L/100) + 1 ≤ L/4 ∧
    4* (L/4) < 2*L-L/4 ∧
    L/4+2* (L/100+1) ≤ 2*L-L/4 ∧
    (2*L-L/4) + L/4=2*L:=by
  have hrt:24*b*L ≤ (L/100) * (L/10) :=by
    have hr:480*b ≤ L/100:=by omega
    have ht:L ≤ 20* (L/10) :=by omega
    calc
      24*b*L ≤ 24*b* (20* (L/10)) :=Nat.mul_le_mul_left _ ht
      _= (480*b) * (L/10) :=by ring
      _ ≤ (L/100) * (L/10) :=Nat.mul_le_mul_right _ hr
  exact ⟨by omega,hrt,by omega,by omega,by omega,by omega⟩
end Erdos556
end bO
section bL
namespace Erdos556
open SimpleGraph Finset
theorem st (B:ℕ) (hB:0 < B) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (L b :ℕ),
      N₀ ≤ L → 1 ≤ b → 100000*b ≤ L →
      4*L ≤ Fintype.card V +b → Fintype.card V ≤ 4 *L → Fintype.card V ≤ B *b →
      qK G (2*L) → qK Gᶜ (2*L) → False:=by
  obtain ⟨N₁,hN₁⟩ :=vQ B hB
  refine ⟨max N₁ 200,?_⟩
  intro V _ _ G _ L b hlarge hb hsmall hNlo hNhi hbudget hG hGc
  classical
  obtain ⟨S,T,hSlo,hShi,hTlo,hThi,hSmiss,hTmiss⟩ :=
    hN₁ G L b (by omega) (by omega) hb (by omega) hNlo hNhi hbudget hG hGc
  obtain ⟨hr,hrt,hloss,hlargeA,hroom,hsum⟩ :=ag L b (by omega) hb hsmall
  have hSm:2* (Gᶜ.induce (S:Set V)).edgeFinset.card ≤ 24*b*L:=by
    exact_mod_cast (show 2 * ((Gᶜ.induce (S:Set V)).edgeFinset.card:ℝ) ≤
      24* (b:ℝ) * L by nlinarith only [hSmiss])
  have hTm:2* (G.induce (T:Set V)).edgeFinset.card ≤ 24*b*L:=by
    exact_mod_cast (show 2 * ((G.induce (T:Set V)).edgeFinset.card:ℝ) ≤
      24* (b:ℝ) * L by nlinarith only [hTmiss])
  obtain ⟨A,C,hAS,hCT,hdis,hAc,hCc,hA,hC⟩ :=
    zL G S T (L/100) (L/10) hr (hSm.trans hrt) (hTm.trans hrt)
  have hAsize:2*L-L/4 ≤ A.card:=by omega
  have hCsize:2*L-L/4 ≤ C.card:=by omega
  rcases x1 G A C (2*L-L/4) (L/4) (L/100+1)
      hdis hAsize hCsize hlargeA hroom (by omega) hA hC with
    ⟨v,c,hc,hlen⟩ | ⟨v,c,hc,hlen⟩
  · have h :=hG v c hc
    omega
  · have h :=hGc v c hc
    omega
theorem w7:
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (L:ℕ),
      N₀ ≤ L → 4*L-L/100000 ≤ Fintype.card V →
      (∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ 2*L ≤ c.length) ∨
      (∃ (v:V) (c:Gᶜ.Walk v v),c.IsCycle ∧ 2*L ≤ c.length) :=by
  obtain ⟨N₁,hN₁⟩ :=st 800000 (by decide)
  refine ⟨max N₁ 200000,?_⟩
  intro V _ _ G _ L hL hN
  classical
  by_contra hnone
  have hG:qK G (2*L) :=by
    intro v c hc
    by_contra! hlen
    exact hnone (Or.inl ⟨v,c,hc,hlen⟩)
  have hGc:qK Gᶜ (2*L) :=by
    intro v c hc
    by_contra! hlen
    exact hnone (Or.inr ⟨v,c,hc,hlen⟩)
  obtain ⟨S,_,hSc⟩ :=exists_subset_card_eq
    (show 4 *L-L/100000 ≤ (univ:Finset V).card by simpa using hN)
  have hcard:Fintype.card (S:Set V) = 4*L-L/100000:=by
    calc
      Fintype.card (S:Set V) = (S:Set V).ncard:=Nat.card_eq_fintype_card.symm
      _=S.card:=Set.ncard_coe_finset S
      _=4*L-L/100000:=hSc
  apply hN₁ (G.induce (S:Set V)) L (L/100000) (by omega) (by omega) (by omega)
  · rw [hcard]
    omega
  · rw [hcard]
    omega
  · rw [hcard]
    omega
  · exact hG.induce (S:Set V)
  · exact hGc.yB S
end Erdos556
end bL
section bi
namespace Erdos556
open SimpleGraph Fin.NatCast
theorem qL {m:ℕ} [NeZero m] (hm:2 ≤ m) (i:Fin m) :
    (cycleGraph m).Adj i (i+1) :=by
  rw [cycleGraph_adj']
  right
  rw [add_sub_cancel_left]
  change 1 %m=1
  exact Nat.mod_eq_of_lt (by omega)
def sO {V:Type*} {G:SimpleGraph V} {m:ℕ} [NeZero m]
    (f: (cycleGraph m).Copy G) (i:Fin m) : (cycleGraph m).Copy G where
  toHom:=
    { toFun:=fun j => f (i+j)
      map_rel':=by
        intro a b h
        apply f.toHom.map_rel
        simpa only [cycleGraph_adj',add_sub_add_left_eq_sub] using h }
  injective':=f.injective.comp (add_right_injective i)
@[simp] theorem va {V:Type*} {G:SimpleGraph V} {m:ℕ} [NeZero m]
    (f: (cycleGraph m).Copy G) (i j :Fin m) : sO f i j =f (i+j) :=rfl
def rD (k:ℕ) : ℕ:=if k =0 then 0 else k +1
theorem tx (m k :ℕ) (hm:2 ≤ m) (hk:k < m-1) : rD k < m :=by
  unfold rD
  split_ifs <;> omega
theorem tu:Function.Injective rD:=by
  intro a b h
  unfold rD at h
  split_ifs at h <;> omega
theorem xo {V:Type*} {G:SimpleGraph V} {m:ℕ}
    [NeZero m] (hm:4 ≤ m) (f: (cycleGraph m).Copy G) (h:G.Adj (f 0) (f 2)) :
    ∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=m-1:=by
  apply qX G (m-1) (by omega)
    (fun k => f (↑(rD k) : Fin m))
  · intro a ha b hb hab
    have hi:=congrArg Fin.val (f.injective hab)
    simp only [Fin.val_natCast,
      Nat.mod_eq_of_lt (tx m a (by omega) ha),
      Nat.mod_eq_of_lt (tx m b (by omega) hb)] at hi
    exact tu hi
  · intro k hk
    by_cases hk0:k=0
    · subst k
      simpa [rD] using h
    · have hs:=f.toHom.map_rel (qL (by omega:2 ≤ m) (↑(k+1) : Fin m))
      simpa [rD,hk0,Nat.cast_add] using hs
  · have hlast:rD (m-1-1) = m-1:=by unfold rD;split_ifs <;> omega
    have hwrap: (↑(m-1) : Fin m) + 1=0:=by
      change (↑(m-1) : Fin m) + (↑(1:ℕ) : Fin m) = 0
      rw [← Nat.cast_add,Nat.sub_add_cancel (by omega:1 ≤ m)]
      simp
    have hs:=f.toHom.map_rel (qL (by omega:2 ≤ m) (↑(m-1) : Fin m))
    have hzero:rD 0 =0:=by simp [rD]
    rw [hlast,hzero]
    change G.Adj (f.toHom (↑(m-1) : Fin m)) (f.toHom (0:Fin m))
    simpa only [hwrap] using hs
theorem qB {V:Type*} {G:SimpleGraph V} {m:ℕ}
    [NeZero m] (hm:4 ≤ m) (f: (cycleGraph m).Copy G)
    (hno: ¬ cycleGraph (m-1) ⊑ G) (i:Fin m) :
    Gᶜ.Adj (f i) (f (i+2)) :=by
  rw [compl_adj]
  refine ⟨?_,?_⟩
  · intro h
    have hi:=f.injective h
    have ht: (2:Fin m) = 0:=by
      apply add_left_cancel (a:=i)
      simpa only [add_zero] using hi.symm
    have ht':2%m=0:=congrArg Fin.val ht
    rw [Nat.mod_eq_of_lt (by omega:2 < m)] at ht'
    omega
  · intro h
    have hrot:G.Adj (sO f i 0) (sO f i 2) :=by
      simpa only [va,add_zero] using h
    exact hno ((cycleGraph_isContained_iff (by omega:2 < m-1)).mpr
      (xo hm (sO f i) hrot))
end Erdos556
end bi
section bg
namespace Erdos556
open SimpleGraph Fin.NatCast
theorem vj {m:ℕ} [NeZero m] (hm:Odd m) :
    Function.Injective (fun i :Fin m => i +i) :=by
  intro i j hij
  obtain ⟨r,hr⟩ :=hm
  have hi:=i.isLt
  have hj:=j.isLt
  have he:=congrArg Fin.val hij
  simp only [Fin.val_add] at he
  have hmod (x:ℕ) (hx:x < m) : (x+x) % m=
      if x +x < m then x +x else x +x-m:=by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
  rw [hmod i.val hi,hmod j.val hj] at he
  apply Fin.ext
  split_ifs at he <;> omega
theorem zT {m:ℕ} [NeZero m] (hm:2 ≤ m) (i j :Fin m) :
    (cycleGraph m).Adj i j ↔ i=j+1 ∨ j=i+1:=by
  obtain ⟨k,hkm⟩ : ∃ k,m=k+2:= ⟨m-2,by omega⟩
  subst m
  rw [cycleGraph_adj]
  simp only [sub_eq_iff_eq_add,add_comm]
def tv {V:Type*} {G H :SimpleGraph V} {m:ℕ} [NeZero m]
    (hm:2 ≤ m) (hodd:Odd m) (f: (cycleGraph m).Copy G)
    (hstep: ∀ i:Fin m,H.Adj (f i) (f (i+2))) : (cycleGraph m).Copy H where
  toHom:=
    { toFun:=fun i => f (i+i)
      map_rel':=by
        intro i j hij
        rcases (zT hm i j).mp hij with h | h
        · subst i
          have he: (j+1) + (j+1) = (j+j) + 2:=by
            calc
              _= (j+j) + ((1:Fin m) + 1) :=by abel
              _=_:=congrArg ((j+j) + ·) (Nat.cast_add 1 1).symm
          rw [he]
          exact (hstep (j+j)).symm
        · subst j
          have he: (i+1) + (i+1) = (i+i) + 2:=by
            calc
              _= (i+i) + ((1:Fin m) + 1) :=by abel
              _=_:=congrArg ((i+i) + ·) (Nat.cast_add 1 1).symm
          rw [he]
          exact hstep (i+i)}
  injective':=f.injective.comp (vj hodd)
@[simp] theorem e7 {V:Type*} {G H :SimpleGraph V} {m:ℕ} [NeZero m]
    (hm:2 ≤ m) (hodd:Odd m) (f: (cycleGraph m).Copy G)
    (hstep: ∀ i:Fin m,H.Adj (f i) (f (i+2))) (i:Fin m) :
    tv hm hodd f hstep i =f (i+i) :=rfl
theorem w6 {V:Type*} {G:SimpleGraph V} {m:ℕ}
    [NeZero m] (hm:5 ≤ m) (hodd:Odd m) (f: (cycleGraph m).Copy G)
    (hno: ¬ cycleGraph (m-1) ⊑ G) (hnoc: ¬ cycleGraph (m-1) ⊑ Gᶜ)
    (i:Fin m) : G.Adj (f i) (f (i+4)) :=by
  have hstep:=qB (by omega:4 ≤ m) f hno
  let g :=tv (by omega:2 ≤ m) hodd f hstep
  have hsurj:Function.Surjective (fun j :Fin m => j +j) :=
    (Finite.injective_iff_surjective).mp (vj hodd)
  obtain ⟨j,hj⟩ :=hsurj i
  change j +j=i at hj
  have h :=qB (by omega:4 ≤ m) g hnoc j
  change Gᶜᶜ.Adj (f (j+j)) (f ((j+2) + (j+2))) at h
  have he: (j+2) + (j+2) = (j+j) + 4:=by
    calc
      _= (j+j) + ((2:Fin m) + 2) :=by abel
      _=_:=congrArg ((j+j) + ·) (Nat.cast_add 2 2).symm
  rw [he,hj] at h
  simpa only [compl_compl] using h
end Erdos556
end bg
section bH
namespace Erdos556
open SimpleGraph Fin.NatCast
def qt (k:ℕ) : ℕ:=if k =0 then 0 else if k ≤ 3 then 4 -k else k +1
theorem xd:Function.Injective qt:=by
  intro a b h
  unfold qt at h
  split_ifs at h <;> omega
theorem vY (m k :ℕ) (hm:7 ≤ m) (hk:k < m-1) :
    qt k < m :=by
  unfold qt
  split_ifs <;> omega
theorem wa {V:Type*} {G:SimpleGraph V} {m:ℕ}
    [NeZero m] (hm:7 ≤ m) (f: (cycleGraph m).Copy G)
    (h03:G.Adj (f 0) (f 3)) (h15:G.Adj (f 1) (f 5)) :
    ∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=m-1:=by
  apply qX G (m-1) (by omega)
    (fun k => f (qt k :Fin m))
  · intro a ha b hb hab
    have hi:=congrArg Fin.val (f.injective hab)
    simp only [Fin.val_natCast,
      Nat.mod_eq_of_lt (vY m a hm ha),
      Nat.mod_eq_of_lt (vY m b hm hb)] at hi
    exact xd hi
  · intro k hk
    by_cases hk0:k=0
    · subst k
      simpa [qt] using h03
    by_cases hk1:k=1
    · subst k
      have h := (f.toHom.map_rel (qL (by omega:2 ≤ m) (2:Fin m))).symm
      have he: (2:Fin m) + 1=3:= (Nat.cast_add 2 1).symm
      simpa [qt,he] using h
    by_cases hk2:k=2
    · subst k
      have h := (f.toHom.map_rel (qL (by omega:2 ≤ m) (1:Fin m))).symm
      have he: (1:Fin m) + 1=2:= (Nat.cast_add 1 1).symm
      simpa [qt,he] using h
    by_cases hk3:k=3
    · subst k
      simpa [qt] using h15
    · have hkgt:3 < k:=by omega
      have h :=f.toHom.map_rel (qL (by omega:2 ≤ m) (↑(k+1) : Fin m))
      simpa [qt,hk0,show ¬ k ≤ 3 by omega,
        show ¬ k+1 ≤ 3 by omega,Nat.cast_add] using h
  · have hlast:qt (m-1-1) = m-1:=by
      unfold qt
      split_ifs <;> omega
    have hzero:qt 0 =0:=by simp [qt]
    rw [hlast,hzero]
    change G.Adj (f.toHom (↑(m-1) : Fin m)) (f.toHom (0:Fin m))
    have hwrap: (↑(m-1) : Fin m) + 1=0:=by
      change (↑(m-1) : Fin m) + (↑(1:ℕ) : Fin m) = 0
      rw [← Nat.cast_add,Nat.sub_add_cancel (by omega:1 ≤ m)]
      simp
    simpa only [hwrap] using
      f.toHom.map_rel (qL (by omega:2 ≤ m) (↑(m-1) : Fin m))
theorem vV {V:Type*} {G:SimpleGraph V} {m:ℕ}
    [NeZero m] (hm:7 ≤ m) (hodd:Odd m) (f: (cycleGraph m).Copy G)
    (hno: ¬ cycleGraph (m-1) ⊑ G) (hnoc: ¬ cycleGraph (m-1) ⊑ Gᶜ)
    (i:Fin m) : Gᶜ.Adj (f i) (f (i+3)) :=by
  rw [compl_adj]
  refine ⟨?_,?_⟩
  · intro h
    have hi:=f.injective h
    have ht: (3:Fin m) = 0:=by
      apply add_left_cancel (a:=i)
      simpa only [add_zero] using hi.symm
    have ht':3%m=0:=congrArg Fin.val ht
    rw [Nat.mod_eq_of_lt (by omega:3 < m)] at ht'
    omega
  · intro h
    let g :=sO f i
    have h03:G.Adj (g 0) (g 3) :=by
      simpa only [g,va,add_zero] using h
    have h15:=w6 (by omega:5 ≤ m) hodd g hno hnoc 1
    have he: (1:Fin m) + 4=5:= (Nat.cast_add 1 4).symm
    rw [he] at h15
    exact hno ((cycleGraph_isContained_iff (by omega:2 < m-1)).mpr
      (wa hm g h03 h15))
end Erdos556
end bH
section bR
namespace Erdos556
open SimpleGraph Fin.NatCast
def xR (m s a b :ℕ) : Prop:=
  a+s=b ∨ b+s=a ∨ a+s=b+m ∨ b+s=a+m
theorem s3 {V:Type*} {G:SimpleGraph V} {m:ℕ} [NeZero m]
    (f:Fin m → V) (s:ℕ) (hs: ∀ i,G.Adj (f i) (f (i+ (s:Fin m))))
    (a b :ℕ) (h:xR m s a b) : G.Adj (f (a:Fin m)) (f (b:Fin m)) :=by
  have hf (a b :ℕ) (hab:a+s=b ∨ a+s=b+m) :
      G.Adj (f (a:Fin m)) (f (b:Fin m)) :=by
    have he: (a:Fin m) + (s:Fin m) = (b:Fin m) :=by
      rw [← Nat.cast_add]
      rcases hab with h | h
      · rw [h]
      · rw [h,Nat.cast_add,Fin.natCast_self,add_zero]
    simpa only [he] using hs (a:Fin m)
  rcases h with h | h | h | h
  · exact hf a b (Or.inl h)
  · exact (hf b a (Or.inl h)).symm
  · exact hf a b (Or.inr h)
  · exact (hf b a (Or.inr h)).symm
def qD (r k :ℕ) : ℕ:=
  if k =0 then 0 else if k =1 then 3 else if k < r then 2 *k+2
  else if k =r then 1 else if k < 2 *r-1 then 4 *r+1-2*k else 2
theorem xG (r k :ℕ) (hr:3 ≤ r) (hk:k < 2*r) :
    qD r k < 2*r+1:=by
  unfold qD
  split_ifs <;> omega
theorem zt (r:ℕ) (hr:3 ≤ r) :
    Set.InjOn (qD r) (Set.Iio (2*r)) :=by
  intro a ha b hb hab
  change a < 2 *r at ha
  change b < 2 *r at hb
  unfold qD at hab
  split_ifs at hab <;> omega
theorem yY (r k :ℕ) (hr:3 ≤ r) (hk:k+1 < 2*r) :
    xR (2*r+1) 2 (qD r k) (qD r (k+1)) ∨
    xR (2*r+1) 3 (qD r k) (qD r (k+1)) :=by
  unfold qD xR
  split_ifs <;> first | contradiction | omega
theorem w2 {V:Type*} {G:SimpleGraph V}
    (r:ℕ) (hr:3 ≤ r) (f:Fin (2*r+1) → V) (hf:Function.Injective f)
    (h2: ∀ i,G.Adj (f i) (f (i+2))) (h3: ∀ i,G.Adj (f i) (f (i+3))) :
    ∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=2*r:=by
  apply qX G (2*r) (by omega)
    (fun k => f (qD r k:Fin (2*r+1)))
  · intro a ha b hb hab
    have hi:=congrArg Fin.val (hf hab)
    simp only [Fin.val_natCast,
      Nat.mod_eq_of_lt (xG r a hr ha),
      Nat.mod_eq_of_lt (xG r b hr hb)] at hi
    exact zt r hr ha hb hi
  · intro k hk
    rcases yY r k hr hk with h | h
    · exact s3 f 2 h2 _ _ h
    · exact s3 f 3 h3 _ _ h
  · have hlast:qD r (2*r-1) = 2:=by
      unfold qD
      split_ifs <;> omega
    have hzero:qD r 0=0:=by simp [qD]
    apply s3 f 2 h2
    rw [hlast,hzero]
    exact Or.inr (Or.inl rfl)
end Erdos556
end bR
section aW
namespace Erdos556
open SimpleGraph
theorem rS {V:Type*} (G:SimpleGraph V)
    (m:ℕ) (hm:7 ≤ m) (hodd:Odd m) (hc:cycleGraph m ⊑ G) :
    cycleGraph (m-1) ⊑ G ∨ cycleGraph (m-1) ⊑ Gᶜ:=by
  classical
  by_contra hn
  have hno: (¬ cycleGraph (m-1) ⊑ G) ∧ (¬ cycleGraph (m-1) ⊑ Gᶜ) :=not_or.mp hn
  obtain ⟨r,hr⟩ :=hodd
  have hmr:m=2*r+1:=by omega
  subst m
  obtain ⟨f⟩ :=hc
  have h2:=qB (by omega:4 ≤ 2*r+1) f hno.1
  have h3:=vV hm ⟨r,by omega⟩ f hno.1 hno.2
  obtain ⟨v,c,hcycle,hlen⟩ :=w2 r (by omega) f f.injective
    h2 h3
  apply hno.2
  apply (cycleGraph_isContained_iff (by omega:2 < 2*r+1-1)).mpr
  exact ⟨v,c,hcycle,by omega⟩
theorem vq {V:Type*} (G:SimpleGraph V)
    (n:ℕ) (hn:7 ≤ n) (hno: ¬ cycleGraph n ⊑ G) (hnoc: ¬ cycleGraph n ⊑ Gᶜ)
    (hex: ∃ m,n ≤ m ∧ (cycleGraph m ⊑ G ∨ cycleGraph m ⊑ Gᶜ)) :
    ∃ m,n < m ∧ Even m ∧ (cycleGraph m ⊑ G ∨ cycleGraph m ⊑ Gᶜ) ∧
      ¬ cycleGraph (m-1) ⊑ G ∧ ¬ cycleGraph (m-1) ⊑ Gᶜ:=by
  classical
  let m :=Nat.find hex
  have hm:=Nat.find_spec hex
  change n ≤ m ∧ (cycleGraph m ⊑ G ∨ cycleGraph m ⊑ Gᶜ) at hm
  have hlt:n < m:=by
    have hne:m ≠ n:=by
      intro h
      rcases hm.2 with hG | hGc
      · exact hno (h ▸ hG)
      · exact hnoc (h ▸ hGc)
    omega
  have hpred: ¬ (cycleGraph (m-1) ⊑ G ∨ cycleGraph (m-1) ⊑ Gᶜ) :=by
    intro h
    apply Nat.find_min hex (show m -1 < Nat.find hex by change m -1 < m;omega)
    exact ⟨by omega,h⟩
  have heven:Even m :=by
    rcases Nat.even_or_odd m with h | h
    · exact h
    · exfalso
      rcases hm.2 with hG | hGc
      · exact hpred (rS G m (by omega) h hG)
      · rcases rS Gᶜ m (by omega) h hGc with h₁ | h₂
        · exact hpred (Or.inr h₁)
        · exact hpred (Or.inl (by simpa only [compl_compl] using h₂))
  exact ⟨m,hlt,heven,hm.2,fun h => hpred (Or.inl h),fun h => hpred (Or.inr h)⟩
end Erdos556
end aW
section bs
namespace Erdos556
open SimpleGraph Fin.NatCast
def yZ {V:Type*} {G:SimpleGraph V} {m:ℕ} [NeZero m]
    (f: (cycleGraph m).Copy G) : (cycleGraph m).Copy G where
  toHom:=
    { toFun:=fun i => f (-i)
      map_rel':=by
        intro a b h
        apply f.toHom.map_rel
        simpa only [cycleGraph_adj',neg_sub_neg,or_comm] using h }
  injective':=f.injective.comp neg_injective
@[simp] theorem tg {V:Type*} {G:SimpleGraph V} {m:ℕ} [NeZero m]
    (f: (cycleGraph m).Copy G) (i:Fin m) : yZ f i=f (-i) :=rfl
theorem uK {m:ℕ} [NeZero m] (a b :ℕ) (h:a+b=m) :
    -(a:Fin m) = (b:Fin m) :=by
  apply neg_eq_iff_add_eq_zero.mpr
  rw [← Nat.cast_add,h,Fin.natCast_self]
theorem v6 {V:Type*} {G:SimpleGraph V} {m:ℕ}
    [NeZero m] (f: (cycleGraph m).Copy G) (j:ℕ) (hj:2 ≤ j) (hjm:j+1 < m)
    (hfirst:G.Adj (f 0) (f (j:Fin m)))
    (hsecond:G.Adj (f 2) (f (↑(j+1) : Fin m))) :
    ∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=m-1:=by
  apply qX G (m-1) (by omega)
    (fun k => f (qq j k:Fin m))
  · intro a ha b hb hab
    have hi:=congrArg Fin.val (f.injective hab)
    simp only [Fin.val_natCast,
      Nat.mod_eq_of_lt (zB m j a hj hjm ha),
      Nat.mod_eq_of_lt (zB m j b hj hjm hb)] at hi
    exact y0 j hj hi
  · intro k hk
    by_cases hk0:k=0
    · subst k
      simpa [qq,show 1 < j by omega] using hfirst
    by_cases hkj:k+1 < j
    · have hstep:= (f.toHom.map_rel
        (qL (by omega:2 ≤ m) (↑(j-k) : Fin m))).symm
      have h₁:qq j k=j-k+1:=by unfold qq;split_ifs <;> omega
      have h₂:qq j (k+1) = j-k:=by simp [qq,hkj]
      simpa only [h₁,h₂,Nat.cast_add,Nat.cast_one,Copy.toHom_apply] using hstep
    by_cases hke:k+1=j
    · have h₁:qq j k=2:=by unfold qq;split_ifs <;> omega
      have h₂:qq j (k+1) = j+1:=by
        unfold qq
        split_ifs <;> omega
      simpa only [h₁,h₂,Nat.cast_ofNat] using hsecond
    · have h₁:qq j k=k+1:=by unfold qq;split_ifs <;> omega
      have h₂:qq j (k+1) = (k+1) + 1:=by
        unfold qq
        split_ifs <;> omega
      have hstep:=f.toHom.map_rel
        (qL (by omega:2 ≤ m) (↑(k+1) : Fin m))
      simpa only [h₁,h₂,Nat.cast_add,Nat.cast_one,Copy.toHom_apply] using hstep
  · have hlast:qq j (m-1-1) = m-1:=by
      unfold qq
      split_ifs <;> omega
    have hzero:qq j 0=0:=by simp [qq]
    rw [hlast,hzero]
    change G.Adj (f.toHom (↑(m-1) : Fin m)) (f.toHom (0:Fin m))
    have hwrap: (↑(m-1) : Fin m) + 1=0:=by
      change (↑(m-1) : Fin m) + (↑(1:ℕ) : Fin m) = 0
      rw [← Nat.cast_add,Nat.sub_add_cancel (by omega:1 ≤ m)]
      simp
    simpa only [hwrap] using
      f.toHom.map_rel (qL (by omega:2 ≤ m) (↑(m-1) : Fin m))
theorem sc {V:Type*} {G:SimpleGraph V} {m:ℕ}
    [NeZero m] (f: (cycleGraph m).Copy G) (j:ℕ) (hj:2 ≤ j) (hjm:j+1 < m)
    (hno: ¬ cycleGraph (m-1) ⊑ G) (hfirst:G.Adj (f 0) (f (j:Fin m))) :
    Gᶜ.Adj (f 2) (f (↑(j+1) : Fin m)) :=by
  rw [compl_adj]
  refine ⟨?_,?_⟩
  · intro he
    have he':=congrArg Fin.val (f.injective he)
    change 2 %m= (j+1) % m at he'
    rw [Nat.mod_eq_of_lt (by omega:2 < m),Nat.mod_eq_of_lt hjm] at he'
    omega
  · intro hsecond
    exact hno ((cycleGraph_isContained_iff (by omega:2 < m-1)).mpr
      (v6 f j hj hjm hfirst hsecond))
end Erdos556
end bs
section aU
namespace Erdos556
open SimpleGraph Fin.NatCast
def qw (t a k:ℕ) : ℕ:=
  if k < t -1 then 2 *k+2 else
    if k - (t-1) < a then 2 * (a-1- (k- (t-1))) + 1
    else 2 * (a+t-1- (k- (t-1))) + 1
theorem xp (t a k:ℕ) (ha:2 ≤ a) (hat:a+2 ≤ t)
    (_hk:k < 2*t-1) : qw t a k < 2 *t:=by
  unfold qw
  split_ifs <;> omega
theorem zb (t a :ℕ) (ha:2 ≤ a) (hat:a+2 ≤ t) :
    Set.InjOn (qw t a) (Set.Iio (2*t-1)) :=by
  intro k hk l hl h
  change k < 2 *t-1 at hk
  change l < 2 *t-1 at hl
  unfold qw at h
  split_ifs at h <;> omega
theorem yR (t a k:ℕ) (ha:2 ≤ a) (hat:a+2 ≤ t)
    (hk:k+1 < 2*t-1) (hcross:k ≠ t-2) :
    xR (2*t) 2 (qw t a k) (qw t a (k+1)) :=by
  unfold qw xR
  split_ifs <;> first | contradiction | omega
theorem wm {V:Type*} {G:SimpleGraph V}
    (t a :ℕ) [NeZero (2*t)] (ha:2 ≤ a) (hat:a+2 ≤ t)
    (f:Fin (2*t) → V) (hf:Function.Injective f)
    (h2: ∀ i,G.Adj (f i) (f (i+2)))
    (hfirst:G.Adj (f 2) (f (↑(2*a+1) : Fin (2*t))))
    (hsecond:G.Adj (f (↑(2*t-2) : Fin (2*t))) (f (↑(2*a-1) : Fin (2*t)))) :
    ∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=2*t-1:=by
  apply qX G (2*t-1) (by omega)
    (fun k => f (qw t a k :Fin (2*t)))
  · intro k hk l hl h
    have hi:=congrArg Fin.val (hf h)
    simp only [Fin.val_natCast,
      Nat.mod_eq_of_lt (xp t a k ha hat hk),
      Nat.mod_eq_of_lt (xp t a l ha hat hl)] at hi
    exact zb t a ha hat hk hl hi
  · intro k hk
    by_cases hcross:k=t-2
    · have h₁:qw t a k =2*t-2:=by
        unfold qw
        split_ifs <;> omega
      have h₂:qw t a (k+1) = 2*a-1:=by
        unfold qw
        split_ifs <;> omega
      simpa only [h₁,h₂] using hsecond
    · exact s3 f 2 h2 _ _ (yR t a k ha hat hk hcross)
  · have hlast:qw t a (2*t-1-1) = 2*a+1:=by
      unfold qw
      split_ifs <;> omega
    have hzero:qw t a 0 =2:=by
      unfold qw
      split_ifs <;> omega
    simpa only [hlast,hzero,Nat.cast_ofNat] using hfirst.symm
end Erdos556
end aU
section bm
namespace Erdos556
open SimpleGraph Fin.NatCast
theorem tM {V:Type*} {G:SimpleGraph V} (t a :ℕ)
    [NeZero (2*t)] (ha:2 ≤ a) (hat:a+2 ≤ t) (f: (cycleGraph (2*t)).Copy G)
    (hno: ¬ cycleGraph (2*t-1) ⊑ G) (hnoc: ¬ cycleGraph (2*t-1) ⊑ Gᶜ) :
    ¬ G.Adj (f 0) (f (↑(2*a) : Fin (2*t))) :=by
  intro h
  have hfirst:=sc f (2*a) (by omega) (by omega) hno h
  let g :=yZ f
  have hneg: -(↑(2* (t-a)) : Fin (2*t)) = (↑(2*a) : Fin (2*t)) :=
    uK _ _ (by omega)
  have hrev:G.Adj (g 0) (g (↑(2* (t-a)) : Fin (2*t))) :=by
    simpa only [g,tg,neg_zero,hneg] using h
  have hsecond:=sc g (2* (t-a)) (by omega) (by omega) hno
    hrev
  change Gᶜ.Adj (f (-(2:Fin (2*t))))
    (f (-(↑(2* (t-a) + 1) : Fin (2*t)))) at hsecond
  have hneg2: -(2:Fin (2*t)) = (↑(2*t-2) : Fin (2*t)) :=
    uK 2 (2*t-2) (by omega)
  have hneg': -(↑(2* (t-a) + 1) : Fin (2*t)) = (↑(2*a-1) : Fin (2*t)) :=
    uK _ _ (by omega)
  rw [hneg2,hneg'] at hsecond
  have h2:=qB (by omega:4 ≤ 2*t) f hno
  exact hnoc ((cycleGraph_isContained_iff (by omega:2 < 2*t-1)).mpr
    (wm t a ha hat f f.injective h2 hfirst hsecond))
theorem zd {V:Type*} {G:SimpleGraph V} (t a :ℕ)
    [NeZero (2*t)] (ht:4 ≤ t) (ha:1 ≤ a) (hat:a < t)
    (f: (cycleGraph (2*t)).Copy G)
    (hno: ¬ cycleGraph (2*t-1) ⊑ G) (hnoc: ¬ cycleGraph (2*t-1) ⊑ Gᶜ) :
    Gᶜ.Adj (f 0) (f (↑(2*a) : Fin (2*t))) :=by
  by_cases ha1:a=1
  · subst a
    have h :=qB (by omega:4 ≤ 2*t) f hno 0
    simpa only [zero_add,Nat.mul_one,Nat.cast_ofNat] using h
  by_cases hlast:a+1=t
  · have h :=qB (by omega:4 ≤ 2*t) f hno
      (↑(2*a) : Fin (2*t))
    have he: (↑(2*a) : Fin (2*t)) + 2=0:=by
      change (↑(2*a) : Fin (2*t)) + (↑(2:ℕ) : Fin (2*t)) = 0
      rw [← Nat.cast_add,show 2 *a+2=2*t by omega,Fin.natCast_self]
    rw [he] at h
    exact h.symm
  rw [compl_adj]
  refine ⟨?_,tM t a (by omega) (by omega) f hno hnoc⟩
  intro he
  have hi:=congrArg Fin.val (f.injective he)
  change 0 = (2*a) % (2*t) at hi
  rw [Nat.mod_eq_of_lt (by omega:2*a < 2*t)] at hi
  omega
theorem w3 {V:Type*} {G:SimpleGraph V} (t a :ℕ)
    [NeZero (2*t)] (ht:4 ≤ t) (ha:1 ≤ a) (hat:a < t)
    (f: (cycleGraph (2*t)).Copy G)
    (hno: ¬ cycleGraph (2*t-1) ⊑ G) (hnoc: ¬ cycleGraph (2*t-1) ⊑ Gᶜ)
    (i:Fin (2*t)) : Gᶜ.Adj (f i) (f (i+ (↑(2*a) : Fin (2*t)))) :=by
  simpa only [va,add_zero] using
    zd t a ht ha hat (sO f i) hno hnoc
theorem z2 {V:Type*} {G:SimpleGraph V} (t:ℕ)
    [NeZero (2*t)] (ht:4 ≤ t) (f: (cycleGraph (2*t)).Copy G)
    (hno: ¬ cycleGraph (2*t-1) ⊑ G) (hnoc: ¬ cycleGraph (2*t-1) ⊑ Gᶜ)
    (i j :Fin (2*t)) (hne:i ≠ j) (hpar:i.val%2=j.val%2) : Gᶜ.Adj (f i) (f j) :=by
  have hneval:i.val ≠ j.val:=fun h => hne (Fin.ext h)
  wlog hij:i.val < j.val generalizing i j
  · exact (this j i hne.symm hpar.symm hneval.symm (by omega)).symm
  let a := (j.val-i.val) / 2
  have hdiff:i.val+2*a=j.val:=by dsimp only [a];omega
  have ha:1 ≤ a:=by omega
  have hat:a < t:=by have hj:=j.isLt;omega
  have he:i+ (↑(2*a) : Fin (2*t)) = j:=by
    apply Fin.ext
    simp only [Fin.val_add,Fin.val_natCast,
      Nat.mod_eq_of_lt (show 2 *a < 2*t by omega),hdiff,Nat.mod_eq_of_lt j.isLt]
  have h :=w3 t a ht ha hat f hno hnoc i
  simpa only [he] using h
end Erdos556
end bm
section aO
namespace Erdos556
open SimpleGraph Finset
def zq (t:ℕ) (b:Fin 2) (i:Fin t) : Fin (2*t) :=
  ⟨2*i.val+b.val,by have hi:=i.isLt;have hb:=b.isLt;omega⟩
theorem yo (t:ℕ) (b:Fin 2) :
    Function.Injective (zq t b) :=by
  intro i j h
  have hv:=congrArg Fin.val h
  change 2 *i.val+b.val=2*j.val+b.val at hv
  apply Fin.ext
  omega
noncomputable def wv {V:Type*} [DecidableEq V] {G:SimpleGraph V}
    {t:ℕ} (f: (cycleGraph (2*t)).Copy G) (b:Fin 2) : Finset V :=
  univ.image (fun i :Fin t => f (zq t b i))
theorem tz {V:Type*} [DecidableEq V] {G:SimpleGraph V}
    {t:ℕ} (f: (cycleGraph (2*t)).Copy G) (b:Fin 2) : (wv f b).card=t:=by
  classical
  have hinj:Function.Injective (fun i :Fin t => f (zq t b i)) :=
    f.injective.comp (yo t b)
  rw [wv,card_image_of_injective _ hinj,
    card_univ,Fintype.card_fin]
theorem aa {V:Type*} [DecidableEq V] {G:SimpleGraph V}
    {t:ℕ} (f: (cycleGraph (2*t)).Copy G) : Disjoint (wv f 0) (wv f 1) :=by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv0 hv1
  obtain ⟨i,_,hi⟩ :=mem_image.mp hv0
  obtain ⟨j,_,hj⟩ :=mem_image.mp hv1
  have h :=congrArg Fin.val (f.injective (hi.trans hj.symm))
  change 2 *i.val+0=2*j.val+1 at h
  omega
theorem zA {V:Type*} [DecidableEq V] {G:SimpleGraph V}
    {t:ℕ} [NeZero (2*t)] (ht:4 ≤ t) (f: (cycleGraph (2*t)).Copy G)
    (hno: ¬ cycleGraph (2*t-1) ⊑ G) (hnoc: ¬ cycleGraph (2*t-1) ⊑ Gᶜ)
    (b:Fin 2) : Gᶜ.IsClique ((wv f b:Finset V) : Set V) :=by
  classical
  intro u hu v hv huv
  obtain ⟨i,_,hi⟩ :=mem_image.mp hu
  obtain ⟨j,_,hj⟩ :=mem_image.mp hv
  rw [← hi,← hj]
  apply z2 t ht f hno hnoc
  · intro h
    exact huv (hi.symm.trans ((congrArg f h).trans hj))
  · change (2*i.val+b.val) % 2= (2*j.val+b.val) % 2
    omega
theorem yn {V:Type*} (G:SimpleGraph V)
    (t:ℕ) (ht:4 ≤ t) (hc:cycleGraph (2*t) ⊑ G)
    (hno: ¬ cycleGraph (2*t-1) ⊑ G) (hnoc: ¬ cycleGraph (2*t-1) ⊑ Gᶜ) :
    ∃ A B:Finset V,Disjoint A B ∧ A.card=t ∧ B.card=t ∧
      Gᶜ.IsClique (A:Set V) ∧ Gᶜ.IsClique (B:Set V) :=by
  classical
  let:NeZero (2*t) := ⟨by omega⟩
  obtain ⟨f⟩ :=hc
  exact ⟨wv f 0,wv f 1,aa f,
    tz f 0,tz f 1,
    zA ht f hno hnoc 0,zA ht f hno hnoc 1⟩
end Erdos556
end aO
section bh
namespace Erdos556
open SimpleGraph
theorem yi {V:Type*} [Fintype V] [DecidableEq V]
    (hcard:3 ≤ Fintype.card V) (a b :V) (hab:a ≠ b) :
    ∃ p : (⊤ : SimpleGraph V).Walk a b,p.IsHamiltonian:=by
  classical
  have htop: (⊤ : SimpleGraph V).IsHamiltonian:=by
    apply SimpleGraph.x3 hcard
    intro v
    rw [((⊤ : SimpleGraph V).degree_eq_card_sub_one v).mpr (by simp [IsUniversal])]
    omega
  let:Nontrivial V :=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨q,hq⟩ :=htop.exists_isHamiltonianCycle b
  let e :=Equiv.swap q.snd a
  let f := (Iso.completeGraph e).toHom
  have he₀:f q.snd=a:=Equiv.swap_apply_left _ _
  have he₁:f b=b:=Equiv.swap_apply_of_ne_of_ne
    (q.adj_snd hq.isCycle.not_nil).ne hab.symm
  let p := (q.tail.map f).copy he₀ he₁
  refine ⟨p,?_⟩
  have hmap:=hq.isHamiltonian_tail.map f e.bijective
  simpa only [p,Walk.IsHamiltonian,Walk.support_copy] using hmap
def wt {V:Type*} (G:SimpleGraph V) (a b :V) : SimpleGraph (Option V) where
  Adj
    | some u,some v => G.Adj u v
    | none,some v => v =a ∨ v=b
    | some u,none=> u =a ∨ u=b
    | none,none=> False
  symm:= ⟨by rintro (_ | u) (_ | v) h <;> first | exact h | exact h.symm⟩
  loopless:= ⟨by rintro (_ | u) <;> first | exact not_false | exact G.loopless.irrefl u⟩
@[simp] lemma e9 {V:Type*} (G:SimpleGraph V) (a b u v :V) :
    (wt G a b).Adj (some u) (some v) ↔ G.Adj u v:=Iff.rfl
@[simp] lemma e8 {V:Type*} (G:SimpleGraph V) (a b v:V) :
    (wt G a b).Adj none (some v) ↔ v=a ∨ v=b:=Iff.rfl
def ea {V:Type*} (G:SimpleGraph V) (a b :V) : G.Copy (wt G a
    b) where
  toHom:= { toFun:=some,map_rel':=fun h ↦ h }
  injective':=Option.some_injective V
def e5 {V:Type*} (G:SimpleGraph V) (a b :V) :
    (wt G a b).induce {x | x.isSome} ≃g G where
  toEquiv:=Equiv.optionIsSomeEquiv V
  map_rel_iff':=by
    rintro ⟨x,hx⟩ ⟨y,hy⟩
    cases x with
    | none=> simp at hx
    | some x =>
      cases y with
      | none=> simp at hy
      | some y => rfl
end Erdos556
end bh
section bM
namespace Erdos556
open SimpleGraph Finset
theorem rJ {V:Type*} (G:SimpleGraph V)
    (A:Finset V) (hA:G.IsClique (A:Set V)) (L:ℕ) (hL:2 ≤ L)
    (hsize:L+1 ≤ A.card) (u v :V) (hu:u ∈ A) (hv:v ∈ A) (huv:u ≠ v) :
    ∃ p :G.Walk u v,p.IsPath ∧ p.length=L ∧ ∀ x ∈ p.support,x ∈ A:=by
  classical
  have hpair: ({u,v} : Finset V) ⊆ A:=by
    simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨hu,hv⟩
  have hpaircard: ({u,v} : Finset V).card ≤ L+1:=by
    have h :=card_insert_le u ({v} : Finset V)
    simp only [card_singleton] at h
    omega
  obtain ⟨B,hpB,hBA,hBc⟩ :=exists_subsuperset_card_eq hpair hpaircard hsize
  have huB:u ∈ B:=hpB (by simp)
  have hvB:v ∈ B:=hpB (by simp)
  have hcard:Fintype.card (B:Set V) = L+1:=by
    calc
      Fintype.card (B:Set V) = (B:Set V).ncard:=Nat.card_eq_fintype_card.symm
      _=B.card:=Set.ncard_coe_finset B
      _=L+1:=hBc
  let f : (⊤ : SimpleGraph (B:Set V)) →g G :=
    { toFun:=Subtype.val
      map_rel':=by
        intro x y hxy
        apply hA (hBA x.property) (hBA y.property)
        intro heq
        have hne:x ≠ y:=by simpa only [top_adj] using hxy
        exact hne (Subtype.ext heq)}
  obtain ⟨q,hq⟩ :=yi (V:= (B:Set V)) (by omega)
    ⟨u,huB⟩ ⟨v,hvB⟩ (fun h => huv (congrArg Subtype.val h))
  refine ⟨q.map f,hq.isPath.map Subtype.val_injective,?_,?_⟩
  · rw [Walk.length_map,hq.length_eq,hcard]
    omega
  · intro x hx
    rw [Walk.support_map,List.mem_map] at hx
    obtain ⟨y,_,hyx⟩ :=hx
    exact hyx ▸ hBA y.property
end Erdos556
end bM
section ca
namespace Erdos556
open SimpleGraph Finset
theorem ri {V:Type*}
    {G:SimpleGraph V} {a a' b b':V}
    (A B :Finset V) (hdis:Disjoint A B) (hb':b' ∈ B)
    (p:G.Walk a a') (q:G.Walk b' b) (hp:p.IsPath) (hq:q.IsPath)
    (hL:2 ≤ p.length) (hpA: ∀ x ∈ p.support,x ∈ A) (hqB: ∀ x ∈ q.support,x ∈ B)
    (hab:G.Adj a b) (hab':G.Adj a' b') :
    ∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=p.length+q.length+2:=by
  classical
  have hbp:b' ∉ p.support:=fun h => (Finset.disjoint_left.mp hdis (hpA b' h)) hb'
  have hp': (p.concat hab').IsPath:=hp.concat hbp hab'
  have hinter: ∀ x ∈ (p.concat hab').support,x ∈ q.support → x=b':=by
    intro x hxp hxq
    simp only [Walk.support_concat,List.mem_append,List.mem_singleton] at hxp
    rcases hxp with hxp | hxb
    · exact ((Finset.disjoint_left.mp hdis (hpA x hxp)) (hqB x hxq)).elim
    · exact hxb
  have hr:=qr (p.concat hab') q hp' hq hinter
  obtain ⟨c,hc,hlen⟩ :=r2 ((p.concat hab').append q) hr
    (by simp only [Walk.length_append,Walk.length_concat];omega) hab
  refine ⟨a,c,hc,?_⟩
  simp only [Walk.length_append,Walk.length_concat] at hlen
  omega
theorem vO {V:Type*}
    (G:SimpleGraph V) (A B :Finset V) (hdis:Disjoint A B)
    (hA:G.IsClique (A:Set V)) (hB:G.IsClique (B:Set V))
    (L M :ℕ) (hL:2 ≤ L) (hM:2 ≤ M) (hAc:L+1 ≤ A.card) (hBc:M+1 ≤ B.card)
    (a a' b b':V) (ha:a ∈ A) (ha':a' ∈ A) (hb:b ∈ B) (hb':b' ∈ B)
    (haa:a ≠ a') (hbb:b ≠ b') (hab:G.Adj a b) (hab':G.Adj a' b') :
    ∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=L+M+2:=by
  classical
  obtain ⟨p,hp,hplen,hpA⟩ :=rJ G A hA L hL hAc a a' ha ha' haa
  obtain ⟨q,hq,hqlen,hqB⟩ :=rJ G B hB M hM hBc b' b hb' hb hbb.symm
  obtain ⟨v,c,hc,hlen⟩ :=ri A B hdis hb' p q hp hq
    (by omega) hpA hqB hab hab'
  exact ⟨v,c,hc,by omega⟩
theorem rj {V:Type*}
    (G:SimpleGraph V) (A B :Finset V) (hdis:Disjoint A B)
    (hA:G.IsClique (A:Set V)) (hB:G.IsClique (B:Set V))
    (r:ℕ) (hr:3 ≤ r) (hAc:r+1 ≤ A.card) (hBc:r+1 ≤ B.card)
    (hno: ¬ cycleGraph (2*r+1) ⊑ G)
    (a a' b b':V) (ha:a ∈ A) (ha':a' ∈ A) (hb:b ∈ B) (hb':b' ∈ B)
    (hab:G.Adj a b) (hab':G.Adj a' b') : a=a' ∨ b=b':=by
  classical
  by_contra! hne
  obtain ⟨v,c,hc,hlen⟩ :=vO G A B hdis hA hB r (r-1)
    (by omega) (by omega) hAc (by omega) a a' b b' ha ha' hb hb' hne.1 hne.2 hab hab'
  apply hno
  apply (cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr
  exact ⟨v,c,hc,by omega⟩
end Erdos556
end ca
section c9
namespace Erdos556
open SimpleGraph Finset
theorem ra {V:Type*}
    (A B :Finset V) (R:V → V → Prop)
    (hmatch: ∀ a ∈ A,∀ a' ∈ A,∀ b ∈ B,∀ b' ∈ B,
      R a b → R a' b' → a=a' ∨ b=b') :
    ∃ S :Finset V,S.card ≤ 1 ∧ ∀ a ∈ A,∀ b ∈ B,R a b → a ∈ S ∨ b ∈ S:=by
  classical
  by_cases hex: ∃ a ∈ A,∃ b ∈ B,R a b
  · obtain ⟨a,ha,b,hb,hab⟩ :=hex
    by_cases hall: ∀ u ∈ A,∀ v ∈ B,R u v → u=a
    · refine ⟨{a},by simp,?_⟩
      intro u hu v hv huv
      exact Or.inl (by simpa using hall u hu v hv huv)
    · push Not at hall
      obtain ⟨c,hc,d,hd,hcd,hca⟩ :=hall
      have hdb:d=b:= (hmatch c hc a ha d hd b hb hcd hab).resolve_left hca
      subst d
      refine ⟨{b},by simp,?_⟩
      intro u hu v hv huv
      have hvb:v=b:=by
        by_contra hne
        have hua:= (hmatch u hu a ha v hv b hb huv hab).resolve_right hne
        have huc:= (hmatch u hu c hc v hv b hb huv hcd).resolve_right hne
        exact hca (huc.symm.trans hua)
      exact Or.inr (by simpa using hvb)
  · refine ⟨∅,by simp,?_⟩
    intro a ha b hb hab
    exact (hex ⟨a,ha,b,hb,hab⟩).elim
theorem sp {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (A B S:Finset V) (hdis:Disjoint A B)
    (hcover: ∀ a ∈ A,∀ b ∈ B,G.Adj a b → a ∈ S ∨ b ∈ S) :
    ∀ a ∈ A \ S,∀ b ∈ B \ S,Gᶜ.Adj a b:=by
  intro a ha b hb
  rw [compl_adj]
  refine ⟨?_,?_⟩
  · intro he
    exact (Finset.disjoint_left.mp hdis (mem_sdiff.mp ha).1) (he ▸ (mem_sdiff.mp hb).1)
  · intro hab
    rcases hcover a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1 hab with h | h
    · exact (mem_sdiff.mp ha).2 h
    · exact (mem_sdiff.mp hb).2 h
end Erdos556
end c9
section bK
namespace Erdos556
open SimpleGraph Finset
def rW {V:Type*} (G:SimpleGraph V) (r:ℕ) : Prop:=
  ∃ A B:Finset V,Disjoint A B ∧ r ≤ A.card ∧ r ≤ B.card ∧
    G.IsClique (A:Set V) ∧ G.IsClique (B:Set V) ∧
    ∀ a ∈ A,∀ b ∈ B,Gᶜ.Adj a b
theorem sw {V:Type*}
    (G:SimpleGraph V) (r t :ℕ) (hr:3 ≤ r) (hrt:r+1 ≤ t)
    (hc:cycleGraph (2*t) ⊑ G)
    (hno: ¬ cycleGraph (2*t-1) ⊑ G) (hnoc: ¬ cycleGraph (2*t-1) ⊑ Gᶜ)
    (hforbid: ¬ cycleGraph (2*r+1) ⊑ Gᶜ) : rW Gᶜ r :=by
  classical
  obtain ⟨A,B,hdis,hAc,hBc,hA,hB⟩ :=yn G t (by omega) hc hno hnoc
  have hmatch:=rj Gᶜ A B hdis hA hB r hr
    (by omega) (by omega) hforbid
  obtain ⟨S,hS,hcover⟩ :=ra A B Gᶜ.Adj
    (fun a ha a' ha' b hb b' hb' hab hab'=> hmatch a a' b b' ha ha' hb hb' hab hab')
  have hsize (C:Finset V) (hC:r+1 ≤ C.card) : r ≤ (C \ S).card:=by
    have hcount:=card_sdiff_add_card_inter C S
    have hinter: (C ∩ S).card ≤ S.card:=card_le_card inter_subset_right
    omega
  refine ⟨A \ S,B \ S,hdis.mono sdiff_subset sdiff_subset,
    hsize A (by omega),hsize B (by omega),?_,?_,?_⟩
  · intro a ha b hb hab
    exact hA (mem_sdiff.mp ha).1 (mem_sdiff.mp hb).1 hab
  · intro a ha b hb hab
    exact hB (mem_sdiff.mp ha).1 (mem_sdiff.mp hb).1 hab
  · exact sp Gᶜ A B S hdis hcover
theorem wA {V:Type*}
    (G:SimpleGraph V) (r:ℕ) (hr:3 ≤ r)
    (hno: ¬ cycleGraph (2*r+1) ⊑ G) (hnoc: ¬ cycleGraph (2*r+1) ⊑ Gᶜ)
    (hex: ∃ m,2*r+1 ≤ m ∧ (cycleGraph m ⊑ G ∨ cycleGraph m ⊑ Gᶜ)) :
    rW G r ∨ rW Gᶜ r :=by
  classical
  obtain ⟨m,hmr,hmEven,hcycle,hpred,hpredc⟩ :=
    vq G (2*r+1) (by omega) hno hnoc hex
  obtain ⟨t,ht⟩ :=hmEven
  have hmt:m=2*t:=by omega
  rw [hmt] at hcycle hpred hpredc hmr
  rcases hcycle with hc | hc
  · exact Or.inr (sw G r t hr (by omega) hc hpred hpredc hnoc)
  · left
    have hpredcc: ¬ cycleGraph (2*t-1) ⊑ Gᶜᶜ:=by simpa only [compl_compl] using hpred
    have hnocc: ¬ cycleGraph (2*r+1) ⊑ Gᶜᶜ:=by simpa only [compl_compl] using hno
    simpa only [compl_compl] using
      sw Gᶜ r t hr (by omega) hc hpredc hpredcc hnocc
theorem vr:
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (r:ℕ),
      N₀ ≤ r → 4* (r+1) - (r+1) / 100000 ≤ Fintype.card V →
      (¬ cycleGraph (2*r+1) ⊑ G) → (¬ cycleGraph (2*r+1) ⊑ Gᶜ) →
      rW G r ∨ rW Gᶜ r :=by
  obtain ⟨N₁,hN₁⟩ :=w7
  refine ⟨max N₁ 3,?_⟩
  intro V _ _ G _ r hr hN hno hnoc
  apply wA G r (by omega) hno hnoc
  rcases hN₁ G (r+1) (by omega) hN with ⟨v,c,hc,hlen⟩ | ⟨v,c,hc,hlen⟩
  · refine ⟨c.length,by omega,Or.inl ?_⟩
    exact (cycleGraph_isContained_iff (by omega:2 < c.length)).mpr ⟨v,c,hc,rfl⟩
  · refine ⟨c.length,by omega,Or.inr ?_⟩
    exact (cycleGraph_isContained_iff (by omega:2 < c.length)).mpr ⟨v,c,hc,rfl⟩
end Erdos556
end bK
section bQ
namespace Erdos556
open SimpleGraph Finset
theorem rb {V:Type*}
    (G:SimpleGraph V) (A B :Finset V) (r:ℕ) (hr:1 ≤ r)
    (hdis:Disjoint A B) (hA:r+1 ≤ A.card) (hB:r ≤ B.card)
    (hcross: ∀ a ∈ A,∀ b ∈ B,G.Adj a b)
    (u v :V) (hu:u ∈ A) (hv:v ∈ A) (huv:G.Adj u v) :
    ∃ (w:V) (c:G.Walk w w),c.IsCycle ∧ c.length=2*r+1:=by
  classical
  obtain ⟨p,hp,hlen,_⟩ :=rf G r hr A B
    hdis hcross hA hB u v hu hv huv.ne
  obtain ⟨c,hc,hclen⟩ :=r2 p hp (by omega) huv
  exact ⟨u,c,hc,by omega⟩
theorem rx {V:Type*}
    (G:SimpleGraph V) (A B :Finset V) (r:ℕ) (hr:1 ≤ r)
    (hdis:Disjoint A B) (hA:r ≤ A.card) (hB:r ≤ B.card)
    (hcross: ∀ a ∈ A,∀ b ∈ B,G.Adj a b)
    (x u v:V) (hxA:x ∉ A) (hxB:x ∉ B) (hu:u ∈ A) (hv:v ∈ B)
    (hxu:G.Adj x u) (hxv:G.Adj x v) :
    ∃ (w:V) (c:G.Walk w w),c.IsCycle ∧ c.length=2*r+1:=by
  classical
  obtain ⟨p,hp,hlen,hsupp⟩ :=rY G r hr A B
    hdis hcross hA hB u v hu hv
  have hxp:x ∉ p.support:=by
    intro h
    rcases mem_union.mp (hsupp x h) with h | h
    · exact hxA h
    · exact hxB h
  have hp':=hp.concat hxp hxv.symm
  obtain ⟨c,hc,hclen⟩ :=r2 (p.concat hxv.symm) hp'
    (by rw [Walk.length_concat,hlen];omega) hxu.symm
  refine ⟨u,c,hc,?_⟩
  rw [Walk.length_concat,hlen] at hclen
  omega
end Erdos556
end bQ
section bt
namespace Erdos556
open SimpleGraph Finset
theorem uT {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (A S :Finset V) (hAS:A ⊆ S)
    (hjoin: ∀ a ∈ A,∀ s ∈ S,a ≠ s → G.Adj a s)
    (u:V) (hu:u ∈ S) : G.IsClique ((insert u A:Finset V) : Set V) :=by
  intro x hx y hy hxy
  rcases mem_insert.mp hx with hxu | hxA
  · subst x
    rcases mem_insert.mp hy with hyu | hyA
    · exact (hxy hyu.symm).elim
    · exact (hjoin y hyA u hu hxy.symm).symm
  · rcases mem_insert.mp hy with hyu | hyA
    · subst y
      exact hjoin x hxA u hu hxy
    · exact hjoin x hxA y (hAS hyA) hxy
theorem sC {V:Type*}
    (G:SimpleGraph V) (A S :Finset V) (hAS:A ⊆ S)
    (hjoin: ∀ a ∈ A,∀ s ∈ S,a ≠ s → G.Adj a s)
    (L:ℕ) (hL:3 ≤ L) (hA:L ≤ A.card)
    (u v :V) (hu:u ∈ S) (hv:v ∈ S) (hvA:v ∉ A) (huv:u ≠ v) :
    ∃ p :G.Walk u v,p.IsPath ∧ p.length=L ∧ ∀ x ∈ p.support,x ∈ S:=by
  classical
  have hAe: (A.erase u).Nonempty:=by
    apply card_pos.mp
    have hc:A.card-1 ≤ (A.erase u).card:=by
      by_cases h :u ∈ A
      · rw [card_erase_of_mem h]
      · rw [erase_eq_of_notMem h]
        omega
    omega
  obtain ⟨a,ha⟩ :=hAe
  have haA:=mem_of_mem_erase ha
  have hua:u ≠ a:= (mem_erase.mp ha).1.symm
  have hC:L ≤ (insert u A).card:=hA.trans (card_le_card (subset_insert _ _))
  obtain ⟨p,hp,hlen,hsupp⟩ :=rJ G (insert u A)
    (uT G A S hAS hjoin u hu) (L-1) (by omega) (by omega)
    u a (mem_insert_self _ _) (mem_insert_of_mem haA) hua
  have hvC:v ∉ insert u A:=by
    simp only [mem_insert,not_or]
    exact ⟨huv.symm,hvA⟩
  have hav:G.Adj a v:=hjoin a haA v hv (fun h => hvA (h ▸ haA))
  refine ⟨p.concat hav,hp.concat (fun h => hvC (hsupp v h)) hav,?_,?_⟩
  · rw [Walk.length_concat,hlen]
    omega
  · intro x hx
    rw [Walk.support_concat,List.mem_append,List.mem_singleton] at hx
    rcases hx with hx | hx
    · rcases mem_insert.mp (hsupp x hx) with hx | hx
      · exact hx ▸ hu
      · exact hAS hx
    · exact hx ▸ hv
theorem sF {V:Type*}
    (G:SimpleGraph V) (A S :Finset V) (hAS:A ⊆ S)
    (hjoin: ∀ a ∈ A,∀ s ∈ S,a ≠ s → G.Adj a s)
    (L:ℕ) (hL:3 ≤ L) (hA:L ≤ A.card) (hS:L+1 ≤ S.card)
    (u v :V) (hu:u ∈ S) (hv:v ∈ S) (huv:u ≠ v) :
    ∃ p :G.Walk u v,p.IsPath ∧ p.length=L ∧ ∀ x ∈ p.support,x ∈ S:=by
  classical
  by_cases hvA:v ∈ A
  · by_cases huA:u ∈ A
    · by_cases hsize:L+1 ≤ A.card
      · have hclique:G.IsClique (A:Set V) :=fun _ ha _ hb hab=> hjoin _ ha _ (hAS hb) hab
        obtain ⟨p,hp,hlen,hsupp⟩ :=rJ G A hclique L (by omega) hsize u v
          huA hvA huv
        exact ⟨p,hp,hlen,fun x hx=> hAS (hsupp x hx)⟩
      · obtain ⟨x,hxS,hxA⟩ :=exists_mem_notMem_of_card_lt_card (show A.card < S.card by omega)
        have hsize':L+1 ≤ (insert x A).card:=by rw [card_insert_of_notMem hxA];omega
        obtain ⟨p,hp,hlen,hsupp⟩ :=rJ G (insert x A)
          (uT G A S hAS hjoin x hxS) L (by omega) hsize'
          u v (mem_insert_of_mem huA) (mem_insert_of_mem hvA) huv
        refine ⟨p,hp,hlen,?_⟩
        intro y hy
        rcases mem_insert.mp (hsupp y hy) with hy | hy
        · exact hy ▸ hxS
        · exact hAS hy
    · obtain ⟨p,hp,hlen,hsupp⟩ :=sC G A S hAS hjoin
        L hL hA v u hv hu huA huv.symm
      refine ⟨p.reverse,hp.reverse,by simpa only [Walk.length_reverse] using hlen,?_⟩
      intro x hx
      exact hsupp x (by simpa only [Walk.support_reverse,List.mem_reverse] using hx)
  · exact sC G A S hAS hjoin L hL hA u v hu hv hvA huv
end Erdos556
end bt
section c4
namespace Erdos556
open SimpleGraph Finset
theorem wn {V:Type*}
    (G:SimpleGraph V) (A B :Finset V) (r:ℕ) (hr:1 ≤ r)
    (hdis:Disjoint A B) (hA:r ≤ A.card) (hB:r ≤ B.card)
    (hcross: ∀ a ∈ A,∀ b ∈ B,Gᶜ.Adj a b)
    (hno: ¬ cycleGraph (2*r+1) ⊑ Gᶜ)
    (x:V) (hxA:x ∉ A) (hxB:x ∉ B) :
    (∀ a ∈ A,G.Adj x a) ∨ (∀ b ∈ B,G.Adj x b) :=by
  classical
  by_contra h
  push Not at h
  obtain ⟨⟨a,ha,hxa⟩,⟨b,hb,hxb⟩⟩ :=h
  have hxa':Gᶜ.Adj x a:=by
    rw [compl_adj]
    exact ⟨fun he=> hxA (he ▸ ha),hxa⟩
  have hxb':Gᶜ.Adj x b:=by
    rw [compl_adj]
    exact ⟨fun he=> hxB (he ▸ hb),hxb⟩
  exact hno ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr
    (rx Gᶜ A B r hr hdis hA hB hcross
      x a b hxA hxB ha hb hxa' hxb'))
theorem yd {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (A B :Finset V) (r:ℕ) (hr:1 ≤ r)
    (hdis:Disjoint A B) (hAc:r ≤ A.card) (hBc:r ≤ B.card)
    (hA:G.IsClique (A:Set V)) (hB:G.IsClique (B:Set V))
    (hcross: ∀ a ∈ A,∀ b ∈ B,Gᶜ.Adj a b)
    (hno: ¬ cycleGraph (2*r+1) ⊑ Gᶜ) :
    ∃ S T:Finset V,Disjoint S T ∧ S ∪ T=univ ∧ A ⊆ S ∧ B ⊆ T ∧
      (∀ a ∈ A,∀ s ∈ S,a ≠ s → G.Adj a s) ∧
      (∀ b ∈ B,∀ t ∈ T,b ≠ t → G.Adj b t) :=by
  classical
  let X :=univ.filter (fun x => x ∉ B ∧ ∀ a ∈ A,G.Adj x a)
  let S :=A ∪ X
  let T :=Sᶜ
  have hAS:A ⊆ S:=subset_union_left
  have hBS: ∀ b ∈ B,b ∉ S:=by
    intro b hb hbs
    rcases mem_union.mp hbs with hbA | hbX
    · exact (Finset.disjoint_left.mp hdis hbA) hb
    · exact (mem_filter.mp hbX).2.1 hb
  have hBT:B ⊆ T:=fun b hb=> mem_compl.mpr (hBS b hb)
  refine ⟨S,T,disjoint_compl_right,union_compl S,hAS,hBT,?_,?_⟩
  · intro a ha s hs has
    rcases mem_union.mp hs with hsA | hsX
    · exact hA ha hsA has
    · exact ((mem_filter.mp hsX).2.2 a ha).symm
  · intro b hb t ht hbt
    have htS:t ∉ S:=mem_compl.mp ht
    by_cases htB:t ∈ B
    · exact hB hb htB hbt
    · have htA:t ∉ A:=fun h => htS (hAS h)
      rcases wn G A B r hr hdis hAc hBc hcross hno
        t htA htB with h | h
      · have htX:t ∈ X:=mem_filter.mpr ⟨mem_univ _,htB,h⟩
        exact (htS (mem_union_right A htX)).elim
      · exact (h b hb).symm
end Erdos556
end c4
section c5
namespace Erdos556
open SimpleGraph Finset
theorem r8 {V:Type*}
    (G:SimpleGraph V) (A B S T :Finset V) (r:ℕ) (hr:4 ≤ r)
    (hAS:A ⊆ S) (hBT:B ⊆ T) (hA:r ≤ A.card) (hB:r ≤ B.card)
    (hjoinA: ∀ a ∈ A,∀ s ∈ S,a ≠ s → G.Adj a s)
    (hjoinB: ∀ b ∈ B,∀ t ∈ T,b ≠ t → G.Adj b t)
    (hdis:Disjoint S T) (hS:r+1 ≤ S.card)
    (hno: ¬ cycleGraph (2*r+1) ⊑ G)
    (a a' b b':V) (ha:a ∈ S) (ha':a' ∈ S) (hb:b ∈ T) (hb':b' ∈ T)
    (hab:G.Adj a b) (hab':G.Adj a' b') : a=a' ∨ b=b':=by
  classical
  by_contra! hne
  obtain ⟨p,hp,hplen,hpS⟩ :=sF G A S hAS hjoinA
    r (by omega) hA hS a a' ha ha' hne.1
  have hT:r ≤ T.card:=hB.trans (card_le_card hBT)
  obtain ⟨q,hq,hqlen,hqT⟩ :=sF G B T hBT hjoinB
    (r-1) (by omega) (by omega) (by omega) b' b hb' hb hne.2.symm
  obtain ⟨v,c,hc,hlen⟩ :=ri S T hdis hb' p q hp hq
    (by omega) hpS hqT hab hab'
  exact hno ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr ⟨v,c,hc,by omega⟩)
theorem vt {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (A B S T :Finset V) (r:ℕ) (hr:4 ≤ r)
    (hAS:A ⊆ S) (hBT:B ⊆ T) (hA:r ≤ A.card) (hB:r ≤ B.card)
    (hjoinA: ∀ a ∈ A,∀ s ∈ S,a ≠ s → G.Adj a s)
    (hjoinB: ∀ b ∈ B,∀ t ∈ T,b ≠ t → G.Adj b t)
    (hdis:Disjoint S T) (hunion:S ∪ T=univ) (hN:2*r < Fintype.card V)
    (hno: ¬ cycleGraph (2*r+1) ⊑ G) :
    ∃ Z :Finset V,Z.card ≤ 1 ∧ ∀ s ∈ S,∀ t ∈ T,G.Adj s t → s ∈ Z ∨ t ∈ Z:=by
  have hcard:S.card+T.card=Fintype.card V :=by
    rw [← card_union_of_disjoint hdis,hunion,card_univ]
  apply ra S T G.Adj
  intro a ha a' ha' b hb b' hb' hab hab'
  by_cases hS:r+1 ≤ S.card
  · exact r8 G A B S T r hr
      hAS hBT hA hB hjoinA hjoinB hdis hS hno a a' b b' ha ha' hb hb' hab hab'
  · have hT:r+1 ≤ T.card:=by omega
    have h :=r8 G B A T S r hr
      hBT hAS hB hA hjoinB hjoinA hdis.symm hT hno b b' a a' hb hb' ha ha' hab.symm hab'.symm
    exact h.symm
end Erdos556
end c5
section c1
namespace Erdos556
open SimpleGraph Finset
theorem qS {V:Type*}
    (G:SimpleGraph V) (A S :Finset V) (r:ℕ) (hr:1 ≤ r)
    (hAS:A ⊆ S) (hA:r+1 ≤ A.card) (hS:2*r+1 ≤ S.card)
    (hjoin: ∀ a ∈ A,∀ s ∈ S,a ≠ s → G.Adj a s) :
    ∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=2*r+1:=by
  classical
  obtain ⟨C,hCA,hCc⟩ :=exists_subset_card_eq hA
  have hCS:C ⊆ S:=hCA.trans hAS
  have hdiff:r ≤ (S \ C).card:=by
    rw [card_sdiff,inter_eq_left.mpr hCS,hCc]
    omega
  obtain ⟨W,hWS,hWc⟩ :=exists_subset_card_eq hdiff
  have hCW:Disjoint C W:=by
    apply Finset.disjoint_left.mpr
    intro x hx hxW
    exact (mem_sdiff.mp (hWS hxW)).2 hx
  have hcross: ∀ a ∈ C,∀ w ∈ W,G.Adj a w:=by
    intro a ha w hw
    have hwS:= (mem_sdiff.mp (hWS hw)).1
    have haw:a ≠ w:=fun h => (Finset.disjoint_left.mp hCW ha) (h ▸ hw)
    exact hjoin a (hCA ha) w hwS haw
  obtain ⟨u,hu,v,hv,huv⟩ :=one_lt_card.mp (show 1 < C.card by omega)
  exact rb G C W r hr hCW (by omega) (by omega)
    hcross u v hu hv (hjoin u (hCA hu) v (hCS hv) huv)
theorem uu {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (A S :Finset V) (r:ℕ) (hr:1 ≤ r)
    (hA:r ≤ A.card) (hX:r+1 ≤ (S \ A).card)
    (hjoin: ∀ a ∈ A,∀ s ∈ S,a ≠ s → G.Adj a s)
    (hno: ¬ cycleGraph (2*r+1) ⊑ G) : Gᶜ.IsClique ((S \ A:Finset V) : Set V) :=by
  classical
  have hdis:Disjoint (S \ A) A :=Finset.disjoint_left.mpr fun _ hx=> (mem_sdiff.mp hx).2
  have hcross: ∀ x ∈ S \ A,∀ a ∈ A,G.Adj x a:=by
    intro x hx a ha
    exact (hjoin a ha x (mem_sdiff.mp hx).1 (fun h => (mem_sdiff.mp hx).2 (h ▸ ha))).symm
  intro u hu v hv huv
  rw [compl_adj]
  refine ⟨huv,?_⟩
  intro hadj
  exact hno ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr
    (rb G (S \ A) A r hr hdis hX hA hcross u v hu hv hadj))
theorem vP {V:Type*}
    (G:SimpleGraph V) (A S :Finset V) (hAS:A ⊆ S) (hsize:S.card ≤ A.card+1)
    (hjoin: ∀ a ∈ A,∀ s ∈ S,a ≠ s → G.Adj a s) : G.IsClique (S:Set V) :=by
  classical
  have hdiff: (S \ A).card ≤ 1:=by rw [card_sdiff,inter_eq_left.mpr hAS];omega
  intro u hu v hv huv
  by_cases huA:u ∈ A
  · exact hjoin u huA v hv huv
  by_cases hvA:v ∈ A
  · exact (hjoin v hvA u hu huv.symm).symm
  exact (huv (card_le_one.mp hdiff u (mem_sdiff.mpr ⟨hu,huA⟩) v (mem_sdiff.mpr ⟨hv,hvA⟩))).elim
theorem vR {V:Type*}
    (G:SimpleGraph V) (S T :Finset V) (r:ℕ) (hr:1 ≤ r)
    (hdis:Disjoint S T) (hS:r+1 ≤ S.card) (hT:r ≤ T.card)
    (hcross: ∀ s ∈ S,∀ t ∈ T,Gᶜ.Adj s t)
    (hno: ¬ cycleGraph (2*r+1) ⊑ Gᶜ) : G.IsClique (S:Set V) :=by
  classical
  intro u hu v hv huv
  by_contra hadj
  have hblue:Gᶜ.Adj u v:=by rw [compl_adj];exact ⟨huv,hadj⟩
  exact hno ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr
    (rb Gᶜ S T r hr hdis hS hT hcross u v hu hv hblue))
end Erdos556
end c1
section bG
namespace Erdos556
open SimpleGraph Finset
theorem uS {V:Type*}
    (G:SimpleGraph V) (A S T:Finset V) (r:ℕ) (hr:1 ≤ r)
    (hAS:A ⊆ S) (hA:r ≤ A.card) (hS:2*r+2 ≤ S.card) (hT:r-1 ≤ T.card)
    (hdis:Disjoint S T) (hcross: ∀ s ∈ S,∀ t ∈ T,Gᶜ.Adj s t)
    (hjoin: ∀ a ∈ A,∀ s ∈ S,a ≠ s → G.Adj a s)
    (hno: ¬ cycleGraph (2*r+1) ⊑ G) (hnoc: ¬ cycleGraph (2*r+1) ⊑ Gᶜ) : False:=by
  classical
  by_cases hlargeA:r+1 ≤ A.card
  · exact hno ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr
      (qS G A S r hr hAS hlargeA (by omega) hjoin))
  have hAc:A.card=r:=by omega
  let X :=S \ A
  have hX:r+2 ≤ X.card:=by
    dsimp only [X]
    rw [card_sdiff,inter_eq_left.mpr hAS,hAc]
    omega
  have hclique:Gᶜ.IsClique (X:Set V) :=
    uu G A S r hr hA
      (show r +1 ≤ X.card by omega) hjoin hno
  have hXT:Disjoint X T:=hdis.mono_left sdiff_subset
  have hU:2*r+1 ≤ (X ∪ T).card:=by
    rw [card_union_of_disjoint hXT]
    omega
  have hbluejoin: ∀ x ∈ X,∀ y ∈ X ∪ T,x ≠ y → Gᶜ.Adj x y:=by
    intro x hx y hy hxy
    rcases mem_union.mp hy with hy | hy
    · exact hclique hx hy hxy
    · exact hcross x (mem_sdiff.mp hx).1 y hy
  exact hnoc ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr
    (qS Gᶜ X (X ∪ T) r hr subset_union_left
      (by omega) hU hbluejoin))
theorem sE {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (A S T Z :Finset V) (r:ℕ) (hr:1 ≤ r)
    (hAS:A ⊆ S) (hA:r ≤ A.card) (hT:r ≤ T.card)
    (hjoin: ∀ a ∈ A,∀ s ∈ S,a ≠ s → G.Adj a s)
    (hdis:Disjoint S T) (hunion:S ∪ T=univ) (hN:3*r+2 ≤ Fintype.card V)
    (hZ:Z.card ≤ 1) (hcross: ∀ s ∈ S \ Z,∀ t ∈ T \ Z,Gᶜ.Adj s t)
    (hno: ¬ cycleGraph (2*r+1) ⊑ G) (hnoc: ¬ cycleGraph (2*r+1) ⊑ Gᶜ) :
    r ≤ (T \ Z).card:=by
  classical
  by_contra hsmall
  have hpart:=card_sdiff_add_card_inter T Z
  have hinter: (T ∩ Z).card ≤ 1:= (card_le_card inter_subset_right).trans hZ
  have hTc:T.card=r:=by omega
  have hlost: (T ∩ Z).Nonempty:=card_pos.mp (by omega)
  obtain ⟨z,hz⟩ :=hlost
  have hZT:Z ⊆ T:=by
    intro x hx
    have he:x=z:=card_le_one.mp hZ x hx z (mem_inter.mp hz).2
    exact he ▸ (mem_inter.mp hz).1
  have hSZ:Disjoint S Z:=hdis.mono_right hZT
  have hdiff:S \ Z=S:=by
    ext s
    constructor
    · exact fun h => (mem_sdiff.mp h).1
    · intro hs
      exact mem_sdiff.mpr ⟨hs,Finset.disjoint_left.mp hSZ hs⟩
  have hcard:S.card+T.card=Fintype.card V :=by
    rw [← card_union_of_disjoint hdis,hunion,card_univ]
  have hSc:2*r+2 ≤ S.card:=by omega
  have hcross': ∀ s ∈ S,∀ t ∈ T \ Z,Gᶜ.Adj s t:=by simpa only [hdiff] using hcross
  exact uS G A S (T \ Z) r hr hAS hA hSc (by omega)
    (hdis.mono_right sdiff_subset) hcross' hjoin hno hnoc
end Erdos556
end bG
section bP
namespace Erdos556
open SimpleGraph Finset
def uP {V:Type*} [Fintype V] [DecidableEq V] (G:SimpleGraph V) (r:ℕ) : Prop:=
  ∃ S T Z :Finset V,Z.card ≤ 1 ∧ Disjoint S T ∧ S ∪ T=univ \ Z ∧
    G.IsClique (S:Set V) ∧ G.IsClique (T:Set V) ∧
    (∀ s ∈ S,∀ t ∈ T,Gᶜ.Adj s t) ∧ S.card ≤ 2*r ∧ T.card ≤ 2*r
theorem rX {V:Type*}
    (G:SimpleGraph V) (S:Finset V) (r:ℕ) (hr:1 ≤ r)
    (hclique:G.IsClique (S:Set V)) (hno: ¬ cycleGraph (2*r+1) ⊑ G) :
    S.card ≤ 2*r:=by
  classical
  by_contra h
  exact hno ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr
    (qS G S S r hr Subset.rfl (by omega) (by omega)
      (fun _ ha _ hb hab=> hclique ha hb hab)))
theorem rC {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (A S T Z :Finset V) (r:ℕ) (hr:1 ≤ r)
    (hAS:A ⊆ S) (hA:r ≤ A.card)
    (hjoin: ∀ a ∈ A,∀ s ∈ S,a ≠ s → G.Adj a s)
    (hdis:Disjoint S T) (hZ:Z.card ≤ 1) (hT:r ≤ (T \ Z).card)
    (hcross: ∀ s ∈ S \ Z,∀ t ∈ T \ Z,Gᶜ.Adj s t)
    (hnoc: ¬ cycleGraph (2*r+1) ⊑ Gᶜ) : G.IsClique ((S \ Z:Finset V) : Set V) :=by
  by_cases hlarge:r+1 ≤ (S \ Z).card
  · exact vR G (S \ Z) (T \ Z) r hr
      (hdis.mono sdiff_subset sdiff_subset) hlarge hT hcross hnoc
  · have hcount:=card_sdiff_add_card_inter S Z
    have hinter: (S ∩ Z).card ≤ 1:= (card_le_card inter_subset_right).trans hZ
    have hsize:S.card ≤ A.card+1:=by omega
    have hclique:=vP G A S hAS hsize hjoin
    intro u hu v hv huv
    exact hclique (mem_sdiff.mp hu).1 (mem_sdiff.mp hv).1 huv
theorem sH {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) (hr:4 ≤ r) (hN:3*r+2 ≤ Fintype.card V)
    (hcore:rW G r)
    (hno: ¬ cycleGraph (2*r+1) ⊑ G) (hnoc: ¬ cycleGraph (2*r+1) ⊑ Gᶜ) :
    uP G r:=by
  classical
  obtain ⟨A,B,hAB,hAc,hBc,hA,hB,hcrossAB⟩ :=hcore
  obtain ⟨S,T,hdis,hunion,hAS,hBT,hjoinA,hjoinB⟩ :=
    yd G A B r (by omega) hAB hAc hBc hA hB hcrossAB hnoc
  obtain ⟨Z,hZ,hcover⟩ :=vt G A B S T r hr
    hAS hBT hAc hBc hjoinA hjoinB hdis hunion (by omega) hno
  have hcross:=sp G S T Z hdis hcover
  have hcross': ∀ t ∈ T \ Z,∀ s ∈ S \ Z,Gᶜ.Adj t s:=
    fun t ht s hs=> (hcross s hs t ht).symm
  have hTlarge:=sE G A S T Z r (by omega)
    hAS hAc (hBc.trans (card_le_card hBT)) hjoinA hdis hunion hN hZ hcross hno hnoc
  have hunion':T ∪ S=univ:=by simpa only [union_comm] using hunion
  have hSlarge:=sE G B T S Z r (by omega)
    hBT hBc (hAc.trans (card_le_card hAS)) hjoinB hdis.symm hunion' hN hZ hcross' hno hnoc
  have hSclique:=rC G A S T Z r (by omega)
    hAS hAc hjoinA hdis hZ hTlarge hcross hnoc
  have hTclique:=rC G B T S Z r (by omega)
    hBT hBc hjoinB hdis.symm hZ hSlarge hcross' hnoc
  refine ⟨S \ Z,T \ Z,Z,hZ,hdis.mono sdiff_subset sdiff_subset,?_,hSclique,hTclique,
    hcross,rX G (S \ Z) r (by omega) hSclique hno,
    rX G (T \ Z) r (by omega) hTclique hno⟩
  rw [← union_sdiff_distrib,hunion]
theorem wd:
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (r:ℕ),
      N₀ ≤ r → 4* (r+1) - (r+1) / 100000 ≤ Fintype.card V →
      (¬ cycleGraph (2*r+1) ⊑ G) → (¬ cycleGraph (2*r+1) ⊑ Gᶜ) →
      uP G r ∨ uP Gᶜ r :=by
  obtain ⟨N₁,hN₁⟩ :=vr
  refine ⟨max N₁ 4,?_⟩
  intro V _ _ G _ r hr hN hno hnoc
  have hN':3*r+2 ≤ Fintype.card V :=by
    have hdiv:=Nat.div_le_self (r+1) 100000
    omega
  rcases hN₁ G r (by omega) hN hno hnoc with h | h
  · exact Or.inl (sH G r (by omega) hN' h hno hnoc)
  · right
    apply sH Gᶜ r (by omega) hN' h hnoc
    simpa only [compl_compl] using hno
end Erdos556
end bP
section c0
namespace Erdos556
open SimpleGraph Finset
structure v8 {V:Type*} [DecidableEq V]
    (c:q4 V) (A:Finset V) (r:ℕ) (j k :Fin 3) where
  first:Finset V
  second:Finset V
  first_subset:first ⊆ A
  second_subset:second ⊆ A
  disjoint:Disjoint first second
  card_cover:A.card ≤ first.card+second.card+1
  first_clique: (c.graph j).IsClique (first:Set V)
  second_clique: (c.graph j).IsClique (second:Set V)
  cross: ∀ u ∈ first,∀ v ∈ second,(c.graph k).Adj u v
  first_card_le:first.card ≤ 2*r
  second_card_le:second.card ≤ 2*r
theorem q4.w8 {V:Type*}
    (c:q4 V) (A:Set V) (i j k:Fin 3)
    (hcol: ∀ a:Fin 3,a=i ∨ a=j ∨ a=k) (hjk:j ≠ k)
    (hno: ∀ u ∈ A,∀ v ∈ A,¬ (c.graph i).Adj u v) :
    ((c.graph j).induce A)ᶜ= (c.graph k).induce A :=by
  ext u v
  constructor
  · rintro ⟨hne,hj⟩
    have huv:u.val ≠ v.val:=fun hh=> hne (Subtype.ext hh)
    refine ⟨huv,?_⟩
    rcases hcol (c.colour u.val v.val) with hi | he | hk
    · exact (hno u.val u.property v.val v.property ⟨huv,hi⟩).elim
    · exact (hj ⟨huv,he⟩).elim
    · exact hk
  · intro hk
    refine ⟨fun hh=> hk.1 (congrArg Subtype.val hh),?_⟩
    intro hj
    exact hjk (hj.2.symm.trans hk.2)
theorem sj {V:Type*} [DecidableEq V]
    (c:q4 V) (A:Finset V) (r:ℕ) (j k :Fin 3)
    (hcomp: ((c.graph j).induce (A:Set V))ᶜ= (c.graph k).induce (A:Set V))
    (hpart:uP ((c.graph j).induce (A:Set V)) r) :
    Nonempty (v8 c A r j k) :=by
  classical
  obtain ⟨S,T,Z,hZ,hdis,hcov,hS,hT,hcross,hSc,hTc⟩ :=hpart
  let f : (A:Set V) ↪ V:= ⟨Subtype.val,Subtype.val_injective⟩
  have hsub (U:Finset (A:Set V)) : U.map f ⊆ A :=by
    intro u hu
    obtain ⟨v,_,rfl⟩ :=mem_map.mp hu
    exact v.property
  have hclique (U:Finset (A:Set V))
      (hU: ((c.graph j).induce (A:Set V)).IsClique (U:Set (A:Set V))) :
      (c.graph j).IsClique ((U.map f :Finset V) : Set V) :=by
    intro u hu v hv huv
    obtain ⟨u',hu',rfl⟩ :=mem_map.mp hu
    obtain ⟨v',hv',rfl⟩ :=mem_map.mp hv
    exact hU hu' hv' (fun hh=> huv (congrArg f hh))
  refine ⟨{
    first:=S.map f
    second:=T.map f
    first_subset:=hsub S
    second_subset:=hsub T
    disjoint:= ?_
    card_cover:= ?_
    first_clique:=hclique S hS
    second_clique:=hclique T hT
    cross:= ?_
    first_card_le:=by simpa only [card_map] using hSc
    second_card_le:=by simpa only [card_map] using hTc}⟩
  · apply Finset.disjoint_left.mpr
    intro u hu hv
    obtain ⟨s,hs,hes⟩ :=mem_map.mp hu
    obtain ⟨t,ht,het⟩ :=mem_map.mp hv
    exact Finset.disjoint_left.mp hdis hs ((f.injective (het.trans hes.symm)) ▸ ht)
  · rw [card_map,card_map]
    have hh:=congrArg Finset.card hcov
    rw [card_union_of_disjoint hdis,card_sdiff,inter_univ,card_univ] at hh
    have hcard:Fintype.card (A:Set V) = A.card:=by
      calc
        _= (A:Set V).ncard:=Nat.card_eq_fintype_card.symm
        _=A.card:=Set.ncard_coe_finset A
    rw [hcard] at hh
    omega
  · intro u hu v hv
    obtain ⟨s,hs,rfl⟩ :=mem_map.mp hu
    obtain ⟨t,ht,rfl⟩ :=mem_map.mp hv
    have hh:=hcross s hs t ht
    rw [hcomp] at hh
    exact hh
theorem vs:
    ∃ R₀:ℕ,∀ {V:Type*} [DecidableEq V]
      (c:q4 V) (A:Finset V) (r:ℕ) (i:Fin 3),
      R₀ ≤ r → 4* (r+1) - (r+1) / 100000 ≤ A.card →
      (∀ u ∈ A,∀ v ∈ A,¬ (c.graph i).Adj u v) →
      (∀ a,¬ cycleGraph (2*r+1) ⊑ c.graph a) →
      ∃ j k:Fin 3,j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
        Nonempty (v8 c A r j k) :=by
  obtain ⟨R₀,hR₀⟩ :=wd
  refine ⟨R₀,?_⟩
  intro V _ c A r i hr hA hnoI hno
  classical
  have hcols: ∀ i:Fin 3,∃ j k:Fin 3,j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      ∀ a :Fin 3,a=i ∨ a=j ∨ a=k:=by decide
  obtain ⟨j,k,hji,hki,hjk,hall⟩ :=hcols i
  have hc:=c.w8 (A:Set V) i j k hall hjk hnoI
  have hn (a:Fin 3) : ¬ cycleGraph (2*r+1) ⊑ (c.graph a).induce (A:Set V) :=
    fun hh=> hno a (hh.trans ⟨Copy.induce _ _⟩)
  have hcard:Fintype.card (A:Set V) = A.card:=by
    calc
      _= (A:Set V).ncard:=Nat.card_eq_fintype_card.symm
      _=A.card:=Set.ncard_coe_finset A
  have hAc:4* (r+1) - (r+1) / 100000 ≤ Fintype.card (A:Set V) :=by rwa [hcard]
  have hnc: ¬ cycleGraph (2*r+1) ⊑ ((c.graph j).induce (A:Set V))ᶜ:=by
    rw [hc]
    exact hn k
  rcases hR₀ ((c.graph j).induce (A:Set V)) r hr hAc (hn j) hnc with hp | hp
  · exact ⟨j,k,hji,hki,hjk,sj c A r j k hc hp⟩
  · have hkc: ((c.graph k).induce (A:Set V))ᶜ= (c.graph j).induce (A:Set V) :=by
      rw [← hc,compl_compl]
    rw [hc] at hp
    exact ⟨k,j,hki,hji,hjk.symm,sj c A r k j hkc hp⟩
end Erdos556
end c0
section bZ
namespace Erdos556
open SimpleGraph Finset
structure sW {V:Type*} [DecidableEq V]
    (c:q4 V) (p:q1) (A:Finset V) (L d :ℕ) where
  direction:Fin 3
  cores:Fin 4 → Finset V
  subprofile: ∀ l,qc l ∈ q0 p →
    q0 (qu l direction) ⊆ q0 p
  subset: ∀ l,qc l ∈ q0 p → cores l ⊆ A
  large: ∀ l,qc l ∈ q0 p → L ≤ (cores l).card
  profile_disjoint: ∀ l m,l ≠ m → qc l ∈ q0 p →
    qc m ∈ q0 p →
    Disjoint (q0 (qu l direction)) (q0 (qu m
      direction))
  core_disjoint: ∀ l m,l ≠ m → qc l ∈ q0 p →
    qc m ∈ q0 p → Disjoint (cores l) (cores m)
  dense: ∀ l m,qc l ∈ q0 p →
    qc m ∈ q0 p → ∀ i,
    q5 (qu l direction) (qu m direction) i →
    qi (c.graph i) (cores l) (cores m) d
theorem xL {V:Type*} [DecidableEq V]
    (c:q4 V) (p:q1) (A:Finset V) (L d :ℕ)
    (hp:q3 p =1) (hA:L ≤ A.card) :
    Nonempty (sW c p A L d) :=by
  obtain ⟨a,ha⟩ :=tm p hp
  have hsame (l m :Fin 4) (hl:qc l ∈ q0 p)
      (hm:qc m ∈ q0 p) : l=m:=
    xu p l m hp hl hm
  refine ⟨{
    direction:=a
    cores:=fun _ => A
    subprofile:=fun l hl=> by rw [ha l hl]
    subset:=fun _ _=> Subset.rfl
    large:=fun _ _=> hA
    profile_disjoint:=fun l m hlm hl hm=> (hlm (hsame l m hl hm)).elim
    core_disjoint:=fun l m hlm hl hm=> (hlm (hsame l m hl hm)).elim
    dense:= ?_}⟩
  intro l m hl hm i hsep
  have hsame':=hsame l m hl hm
  subst m
  have hd:=re _ _ i hsep.1
  have he:q0 (qu l a) = ∅ :=by
    simpa only [disjoint_self,Finset.bot_eq_empty] using hd
  have hmem:=r5 l a
  rw [he] at hmem
  exact (notMem_empty _ hmem).elim
def boolCore {V:Type*} (S T :Finset V) (b:Bool) : Finset V :=if b then T else S
theorem b5 {V:Type*} {S T A:Finset V}
    (hS:S ⊆ A) (hT:T ⊆ A) (b:Bool) : boolCore S T b ⊆ A :=by
  cases b <;> assumption
theorem aL {V:Type*} {S T :Finset V} {L:ℕ}
    (hS:L ≤ S.card) (hT:L ≤ T.card) (b:Bool) : L ≤ (boolCore S T b).card:=by
  cases b <;> assumption
theorem aG {V:Type*} {S T :Finset V} (hdis:Disjoint S T)
    (a b :Bool) (hab:a ≠ b) : Disjoint (boolCore S T a) (boolCore S T b) :=by
  cases a <;> cases b
  · exact (hab rfl).elim
  · exact hdis
  · exact hdis.symm
  · exact (hab rfl).elim
theorem d5 {V:Type*} {G:SimpleGraph V} {S T :Finset V}
    (hcross: ∀ u ∈ S,∀ v ∈ T,G.Adj u v)
    (a b :Bool) (hab:a ≠ b) :
    ∀ u ∈ boolCore S T a,∀ v ∈ boolCore S T b,G.Adj u v:=by
  cases a <;> cases b
  · exact (hab rfl).elim
  · exact hcross
  · exact fun u hu v hv=> (hcross v hv u hu).symm
  · exact (hab rfl).elim
theorem x0 {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S T :Finset V) (d:ℕ)
    (hcross: ∀ u ∈ S,∀ v ∈ T,G.Adj u v) : qi G S T d:=by
  constructor
  · intro u hu
    have he:T.filter (fun v => ¬ G.Adj u v) = ∅ :=by
      apply filter_eq_empty_iff.mpr
      intro v hv hn
      exact hn (hcross u hu v hv)
    rw [he,card_empty]
    exact Nat.zero_le _
  · intro v hv
    have he:S.filter (fun u => ¬ G.Adj v u) = ∅ :=by
      apply filter_eq_empty_iff.mpr
      intro u hu hn
      exact hn (hcross u hu v hv).symm
    rw [he,card_empty]
    exact Nat.zero_le _
theorem xS {V:Type*} [DecidableEq V]
    (c:q4 V) (A:Finset V) (r L d:ℕ) (i j k:Fin 3) (b:Bool)
    (hji:j ≠ i) (hki:k ≠ i) (hjk:j ≠ k)
    (hpart:v8 c A r j k)
    (hS:L ≤ hpart.first.card) (hT:L ≤ hpart.second.card) :
    Nonempty (sW c (cubeFace i b) A L d) :=by
  let B :Fin 4 → Finset V :=fun l => boolCore hpart.first hpart.second (qc l k)
  have hbits (l m :Fin 4) (hlm:l ≠ m)
      (hl:qc l ∈ q0 (cubeFace i b))
      (hm:qc m ∈ q0 (cubeFace i b)) :
      qc l k ≠ qc m k:=yv i k b l m hki hlm hl hm
  refine ⟨{
    direction:=j
    cores:=B
    subprofile:=fun l hl=> zw i j b l hji hl
    subset:=fun l _=> b5 hpart.first_subset hpart.second_subset _
    large:=fun l _=> aL hS hT _
    profile_disjoint:=fun l m hlm hl hm=> xv i j b l m hji hlm hl hm
    core_disjoint:=fun l m hlm hl hm=> aG hpart.disjoint _ _ (hbits l m hlm hl hm)
    dense:= ?_}⟩
  intro l m hl hm z hsep
  have hzk:=xM i j k z b l m hji hki hjk hl hm hsep
  subst z
  have hlm:l ≠ m:=by
    intro he
    subst m
    have hdis:=re _ _ k hsep.1
    have he:q0 (qu l j) = ∅ :=by
      simpa only [disjoint_self,Finset.bot_eq_empty] using hdis
    have hh:=r5 l j
    rw [he] at hh
    exact notMem_empty _ hh
  apply x0
  exact d5 hpart.cross _ _ (hbits l m hlm hl hm)
end Erdos556
end bZ
section b2
namespace Erdos556
open SimpleGraph Finset
noncomputable def qC:ℝ:=1/100000000
theorem y8:0 < qC:=by
  norm_num [qC]
theorem vL (r d M:ℕ) (η:ℝ) (hr:10 ≤ r) (hη:η ≤ 1/100)
    (hd: (d:ℝ) ≤ η* (2*r+1))
    (hM: (1-η) * (2*r+1) ≤ (M:ℝ)) : r+2*d+3 ≤ M:=by
  have hrR: (10:ℝ) ≤ r:=by exact_mod_cast hr
  have hηscaled:=mul_le_mul_of_nonneg_right hη (by positivity: (0:ℝ) ≤ 2*r+1)
  have hb: (r:ℝ) + 2*d+3 ≤ M:=by nlinarith
  exact_mod_cast hb
theorem wx (r M :ℕ) (hr:1000000 ≤ r)
    (hM: (2-qC) * (2*r+1) ≤ (M:ℝ)) :
    4* (r+1) - (r+1) / 100000 ≤ M:=by
  have hMR: (199999999:ℝ) * (2*r+1) ≤ 100000000*M:=by
    dsimp only [qC] at hM
    nlinarith
  have hMN:199999999* (2*r+1) ≤ 100000000*M:=by exact_mod_cast hMR
  omega
theorem wG:
    ∃ R₀:ℕ,∀ {V:Type*} [DecidableEq V] (c:q4 V) (r:ℕ),
      R₀ ≤ r → (∀ i,¬ cycleGraph (2*r+1) ⊑ c.graph i) →
      ∀ h :rv c (2*r+1) qC,
      ∀ p,0 < h.weight p →
        Nonempty (sW c p (h.sets p) (r+2*h.defect+3) h.defect) :=by
  obtain ⟨R₁,htwo⟩ :=vs
  refine ⟨max R₁ 1000000,?_⟩
  intro V _ c r hr hno h p hp
  have hrlarge:1000000 ≤ r:= (le_max_right _ _).trans hr
  have hr₁:R₁ ≤ r:= (le_max_left _ _).trans hr
  have hη:qC ≤ 1/100:=by norm_num [qC]
  have hd: (h.defect:ℝ) ≤ qC* (2*r+1) :=by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using h.defect_le
  have hs:=h.size_lower p
  push_cast at hs
  rcases h.tiling.normalized p hp with ⟨hpdim,hpval⟩ | ⟨hpdim,hpval⟩
  · rw [hpval] at hs
    exact xL c p (h.sets p) _ h.defect hpdim
      (vL r h.defect _ _ (by omega) hη hd hs)
  · obtain ⟨i,b,rfl⟩ := (u1 p).mp hpdim
    rw [hpval] at hs
    have hsize:=wx r _ hrlarge hs
    have hfree:=h.t8 (by omega) hη hno i b hp
    obtain ⟨j,k,hji,hki,hjk,⟨part⟩⟩ :=htwo c (h.sets (cubeFace i b)) r i hr₁ hsize hfree hno
    have hS: (1-qC) * (2*r+1) ≤ (part.first.card:ℝ) :=by
      have hcov: ((h.sets (cubeFace i b)).card:ℝ) ≤ part.first.card+part.second.card+1:=by
        exact_mod_cast part.card_cover
      have hTc: (part.second.card:ℝ) ≤ 2*r:=by exact_mod_cast part.second_card_le
      nlinarith
    have hT: (1-qC) * (2*r+1) ≤ (part.second.card:ℝ) :=by
      have hcov: ((h.sets (cubeFace i b)).card:ℝ) ≤ part.first.card+part.second.card+1:=by
        exact_mod_cast part.card_cover
      have hSc: (part.first.card:ℝ) ≤ 2*r:=by exact_mod_cast part.first_card_le
      nlinarith
    exact xS c _ r _ h.defect i j k b hji hki hjk part
      (vL r h.defect _ _ (by omega) hη hd hS)
      (vL r h.defect _ _ (by omega) hη hd hT)
end Erdos556
end b2
section b7
namespace Erdos556
open SimpleGraph Finset
structure yA {V:Type*} [DecidableEq V]
    (c:q4 V) (L d :ℕ) where
  profiles:Fin 4 → q1
  cores:Fin 4 → Finset V
  dimension: ∀ l,q3 (profiles l) = 1
  profile_disjoint: ∀ l m,l ≠ m →
    Disjoint (q0 (profiles l)) (q0 (profiles m))
  core_disjoint: ∀ l m,l ≠ m → Disjoint (cores l) (cores m)
  large: ∀ l,L ≤ (cores l).card
  dense: ∀ l m i,q5 (profiles l) (profiles m) i →
    qi (c.graph i) (cores l) (cores m) d
theorem ww {V:Type*} [DecidableEq V]
    {c:q4 V} {n L :ℕ} {η:ℝ} (h:rv c n η)
    (href: ∀ p,0 < h.weight p →
      Nonempty (sW c p (h.sets p) L h.defect)) :
    Nonempty (yA c L h.defect) :=by
  classical
  have hex (l:Fin 4) :
      ∃ p :q1,0 < h.weight p ∧ qc l ∈ q0 p :=by
    have hh:qc l ∈ (qj h.weight).biUnion q0:=by
      rw [h.tiling.cover h.admissible]
      exact mem_univ _
    obtain ⟨p,hp,hmem⟩ :=mem_biUnion.mp hh
    exact ⟨p,(mem_filter.mp hp).2,hmem⟩
  choose p hp hmem using hex
  let P :Fin 4 → {q:q1//0 < h.weight q} :=fun l => ⟨p l,hp l⟩
  let R (q: {q:q1//0 < h.weight q}) :
      sW c q.val (h.sets q.val) L h.defect:=
    Classical.choice (href q.val q.property)
  have hmemP (l:Fin 4) : qc l ∈ q0 (P l).val:=hmem l
  have hneq (l m :Fin 4) (hne:P l ≠ P m) : (P l).val ≠ (P m).val:=
    fun he=> hne (Subtype.ext he)
  refine ⟨{
    profiles:=fun l => qu l (R (P l)).direction
    cores:=fun l => (R (P l)).cores l
    dimension:=fun l => yh l _
    profile_disjoint:= ?_
    core_disjoint:= ?_
    large:=fun l => (R (P l)).large l (hmemP l)
    dense:= ?_}⟩
  · intro l m hlm
    by_cases he:P l=P m
    · have hm:qc m ∈ q0 (P l).val:=by rw [he];exact hmemP m
      rw [← he]
      exact (R (P l)).profile_disjoint l m hlm (hmemP l) hm
    · exact (h.tiling.disjoint _ _ (hneq l m he) (P l).property (P m).property).mono
        ((R (P l)).subprofile l (hmemP l)) ((R (P m)).subprofile m (hmemP m))
  · intro l m hlm
    by_cases he:P l=P m
    · have hm:qc m ∈ q0 (P l).val:=by rw [he];exact hmemP m
      rw [← he]
      exact (R (P l)).core_disjoint l m hlm (hmemP l) hm
    · exact (h.disjoint _ _ (hneq l m he)).mono
        ((R (P l)).subset l (hmemP l)) ((R (P m)).subset m (hmemP m))
  · intro l m i hsep
    by_cases he:P l=P m
    · have hm:qc m ∈ q0 (P l).val:=by rw [he];exact hmemP m
      rw [← he] at hsep ⊢
      exact (R (P l)).dense l m (hmemP l) hm i hsep
    · have hparent:=wp (P l).val (P m).val _ _ i
        (h.tiling.disjoint _ _ (hneq l m he) (P l).property (P m).property)
        ((R (P l)).subprofile l (hmemP l)) ((R (P m)).subprofile m (hmemP m)) hsep
      exact (h.dense _ _ i hparent).mono
        ((R (P l)).subset l (hmemP l)) ((R (P m)).subset m (hmemP m))
end Erdos556
end b7
section bl
namespace Erdos556
open Finset
theorem zk: ∀ d:Fin 4 → Fin 3,
    Function.Injective (fun i => vI i (d i)) →
    d= ![0,0,0,0] ∨
    d= ![0,1,1,0] ∨
    d= ![2,0,2,0] ∨
    d= ![1,0,0,1] ∨
    d= ![1,1,1,1] ∨
    d= ![2,2,1,1] ∨
    d= ![0,2,0,2] ∨
    d= ![1,1,2,2] ∨
    d= ![2,2,2,2] :=by decide
theorem xr (d:Fin 4 → Fin 3)
    (hd:Function.Injective (fun i => vI i (d i))) :
    ∃ (s:Fin 4 → Fin 4) (k:Fin 3 → Fin 3),Function.Injective s ∧ Function.Injective k ∧
      (uf (fun i => qu (s i) (d (s i))) k ∨
       uq (fun i => qu (s i) (d (s i))) k) :=by
  rcases zk d hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨![0,2,3,1],![1,2,0],by decide,by decide,?_⟩
    exact Or.inl (by decide)
  · refine ⟨![0,3,1,2],![2,1,0],by decide,by decide,?_⟩
    exact Or.inr (by decide)
  · refine ⟨![0,2,1,3],![1,0,2],by decide,by decide,?_⟩
    exact Or.inr (by decide)
  · refine ⟨![0,3,1,2],![2,0,1],by decide,by decide,?_⟩
    exact Or.inr (by decide)
  · refine ⟨![0,1,3,2],![0,2,1],by decide,by decide,?_⟩
    exact Or.inl (by decide)
  · refine ⟨![0,1,2,3],![0,1,2],by decide,by decide,?_⟩
    exact Or.inr (by decide)
  · refine ⟨![0,2,1,3],![1,2,0],by decide,by decide,?_⟩
    exact Or.inr (by decide)
  · refine ⟨![0,1,2,3],![0,2,1],by decide,by decide,?_⟩
    exact Or.inr (by decide)
  · refine ⟨![0,1,2,3],![0,1,2],by decide,by decide,?_⟩
    exact Or.inl (by decide)
theorem uO (p:Fin 4 → q1)
    (hdim: ∀ i,q3 (p i) = 1)
    (hdis: ∀ i j,i ≠ j → Disjoint (q0 (p i)) (q0 (p j))) :
    ∃ (s:Fin 4 → Fin 4) (k:Fin 3 → Fin 3),Function.Injective s ∧ Function.Injective k ∧
      (uf (fun i => p (s i)) k ∨ uq (fun i => p (s i))
        k) :=by
  classical
  choose a b hab using fun i => tq (p i) (hdim i)
  have ha:Function.Injective a :=by
    intro i j hij
    by_contra hne
    have hd:=hdis i j hne
    have hi:qc (a i) ∈ q0 (p i) :=by
      rw [hab i]
      exact r5 (a i) (b i)
    have hj:qc (a i) ∈ q0 (p j) :=by
      rw [hab j,hij]
      exact r5 (a j) (b j)
    exact (Finset.disjoint_left.mp hd hi) hj
  let e :Fin 4 ≃ Fin 4 :=Equiv.ofBijective a ⟨ha,(Finite.injective_iff_surjective).mp ha⟩
  let d :Fin 4 → Fin 3 :=fun i => b (e.symm i)
  have hcanon (i:Fin 4) : p (e.symm i) = qu i (d i) :=by
    rw [hab (e.symm i)]
    have hi:a (e.symm i) = i:=e.apply_symm_apply i
    rw [hi]
  have hodds:Function.Injective (fun i => vI i (d i)) :=by
    intro i j hij
    change vI i (d i) = vI j (d j) at hij
    by_contra hne
    have hd:=hdis (e.symm i) (e.symm j) (e.symm.injective.ne hne)
    have hi:vI i (d i) ∈ q0 (p (e.symm i)) :=by
      rw [hcanon i]
      exact un i (d i)
    have hj:vI i (d i) ∈ q0 (p (e.symm j)) :=by
      rw [hcanon j,hij]
      exact un j (d j)
    exact (Finset.disjoint_left.mp hd hi) hj
  obtain ⟨s,k,hs,hk,hp⟩ :=xr d hodds
  refine ⟨fun i => e.symm (s i),k,e.symm.injective.comp hs,hk,?_⟩
  have heq: (fun i => p (e.symm (s i))) = (fun i => qu (s i) (d (s i))) :=by
    funext i
    exact hcanon (s i)
  rwa [heq]
end Erdos556
end bl
section bD
namespace Erdos556
open SimpleGraph
def q4.relabel {V:Type*} (c:q4 V) (e:Fin 3 ≃ Fin 3) :
    q4 V where
  colour u v:=e.symm (c.colour u v)
  symm u v:=congrArg e.symm (c.symm u v)
theorem q4.dZ {V:Type*} (c:q4 V)
    (e:Fin 3 ≃ Fin 3) (i:Fin 3) : (c.relabel e).graph i =c.graph (e i) :=by
  ext u v
  simp only [e4,relabel,Equiv.symm_apply_eq]
end Erdos556
end bD
section aT
namespace Erdos556
open SimpleGraph Finset
theorem vD {V I :Type*} [Fintype V] [Fintype I]
    (G:I → SimpleGraph V) (A:I → Finset V) (r:ℕ) (hr:1 ≤ r)
    (hA: ∀ i,r+1 ≤ (A i).card) (hclique: ∀ i,(G i).IsClique (A i :Set V))
    (hno: ∀ i,¬ cycleGraph (2*r+1) ⊑ G i)
    (hcover: ∀ x:V,∃ i,x ∈ A i ∨ ∀ a ∈ A i,(G i).Adj x a) :
    Fintype.card V ≤ 2 *r*Fintype.card I :=by
  classical
  let S :I → Finset V :=fun i => univ.filter (fun x => x ∈ A i ∨ ∀ a ∈ A i,(G i).Adj x a)
  have hAS (i:I) : A i ⊆ S i:=by
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _,Or.inl hx⟩
  have hjoin (i:I) : ∀ a ∈ A i,∀ x ∈ S i,a ≠ x → (G i).Adj a x:=by
    intro a ha x hx hax
    rcases (mem_filter.mp hx).2 with hxA | hx
    · exact hclique i ha hxA hax
    · exact (hx a ha).symm
  have hsize (i:I) : (S i).card ≤ 2*r:=by
    by_contra h
    exact hno i ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr
      (qS (G i) (A i) (S i) r hr (hAS i) (hA i)
        (by omega) (hjoin i)))
  have hunion:univ.biUnion S = (univ:Finset V) :=by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨i,hi⟩ :=hcover x
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,hi⟩⟩
  calc
    Fintype.card V = (univ.biUnion S).card:=by rw [hunion,card_univ]
    _ ≤ ∑ i,(S i).card:=card_biUnion_le
    _ ≤ ∑ _i:I,2*r:=sum_le_sum fun i _=> hsize i
    _=2*r*Fintype.card I :=by simp [Nat.mul_comm]
end Erdos556
end aT
section bf
namespace Erdos556
open SimpleGraph Finset
structure rM {V:Type*} [DecidableEq V]
    (c:q4 V) (A:Fin 4 → Finset V) (d:ℕ) : Prop where
  disjoint: ∀ i j,i ≠ j → Disjoint (A i) (A j)
  red02:qi (c.graph 0) (A 0) (A 2) d
  red03:qi (c.graph 0) (A 0) (A 3) d
  red12:qi (c.graph 0) (A 1) (A 2) d
  red13:qi (c.graph 0) (A 1) (A 3) d
  blue01:qi (c.graph 1) (A 0) (A 1) d
  green23:qi (c.graph 2) (A 2) (A 3) d
def qM (i:Fin 4) : Fin 3 :=if i.val < 2 then 2 else 1
theorem y3: ∀ k:Fin 4 → Fin 3,
    k 0 ≠ 2 → k 1 ≠ 2 → k 2 ≠ 1 → k 3 ≠ 1 →
    (k 0 =0 ∧ k 2=0) ∨ (k 0 =0 ∧ k 3=0) ∨
    (k 1 =0 ∧ k 2=0) ∨ (k 1 =0 ∧ k 3=0) ∨
    (k 0 =1 ∧ k 1=1) ∨ (k 2 =2 ∧ k 3=2) :=by decide
theorem rM.zP {V:Type*} [DecidableEq V]
    {c:q4 V} {A:Fin 4 → Finset V} {d:ℕ}
    (h:rM c A d) (r:ℕ) (hr:2 ≤ r)
    (hsize: ∀ i,r+2*d+1 ≤ (A i).card)
    (hno: ∀ k,¬ cycleGraph (2*r+1) ⊑ c.graph k) :
    ∀ i,(c.graph (qM i)).IsClique (A i :Set V) :=by
  have hside (i j :Fin 4) (k:Fin 3) (hij:i ≠ j)
      (hd:qi (c.graph k) (A i) (A j) d) :
      ∀ u ∈ A i,∀ v ∈ A i,¬ (c.graph k).Adj u v:=
    ro (c.graph k) (A i) (A j) r d (by omega)
      (h.disjoint i j hij) hd (hsize i) (by have hj:=hsize j;omega) (hno k)
  intro i
  fin_cases i
  · apply c.r7 (A 0) 0 1 2 sN
    · exact hside 0 2 0 (by decide) h.red02
    · exact hside 0 1 1 (by decide) h.blue01
  · apply c.r7 (A 1) 0 1 2 sN
    · exact hside 1 2 0 (by decide) h.red12
    · exact hside 1 0 1 (by decide) h.blue01.symm
  · apply c.r7 (A 2) 0 2 1
      (fun k => by
        have hk:=sN k
        tauto)
    · exact hside 2 0 0 (by decide) h.red02.symm
    · exact hside 2 3 2 (by decide) h.green23
  · apply c.r7 (A 3) 0 2 1
      (fun k => by
        have hk:=sN k
        tauto)
    · exact hside 3 0 0 (by decide) h.red03.symm
    · exact hside 3 2 2 (by decide) h.green23.symm
theorem rM.u4 {V:Type*} [DecidableEq V]
    {c:q4 V} {A:Fin 4 → Finset V} {d:ℕ}
    (h:rM c A d) (r:ℕ) (hr:2 ≤ r)
    (hsize: ∀ i,r+2*d+1 ≤ (A i).card)
    (hno: ∀ k,¬ cycleGraph (2*r+1) ⊑ c.graph k)
    (x:V) (hx: ∀ i,x ∉ A i) :
    ∃ i,∀ a ∈ A i,(c.graph (qM i)).Adj x a:=by
  classical
  by_contra hn
  push Not at hn
  choose u hu hbad using hn
  have hne (i:Fin 4) : x ≠ u i :=by
    intro he
    exact hx i (he.symm ▸ hu i)
  have hcolour (i:Fin 4) : c.colour x (u i) ≠ qM i :=
    fun he=> hbad i ⟨hne i,he⟩
  have havoid (i j :Fin 4) (k:Fin 3) (hij:i ≠ j)
      (hd:qi (c.graph k) (A i) (A j) d) :
      ¬ (c.colour x (u i) = k ∧ c.colour x (u j) = k) :=by
    intro he
    apply rG (c.graph k) (A i) (A j) r d hr
      (h.disjoint i j hij) hd (by have hi:=hsize i;omega) (by have hj:=hsize j;omega)
      (hno k) x (hx i) (hx j) (u i) (u j) (hu i) (hu j)
    exact ⟨⟨hne i,he.1⟩,⟨hne j,he.2⟩⟩
  have h0:c.colour x (u 0) ≠ 2:=by simpa [qM] using hcolour 0
  have h1:c.colour x (u 1) ≠ 2:=by simpa [qM] using hcolour 1
  have h2:c.colour x (u 2) ≠ 1:=by simpa [qM] using hcolour 2
  have h3:c.colour x (u 3) ≠ 1:=by simpa [qM] using hcolour 3
  rcases y3 (fun i => c.colour x (u i)) h0 h1 h2 h3 with
    he | he | he | he | he | he
  · exact havoid 0 2 0 (by decide) h.red02 he
  · exact havoid 0 3 0 (by decide) h.red03 he
  · exact havoid 1 2 0 (by decide) h.red12 he
  · exact havoid 1 3 0 (by decide) h.red13 he
  · exact havoid 0 1 1 (by decide) h.blue01 he
  · exact havoid 2 3 2 (by decide) h.green23 he
theorem uo {V:Type*} [Fintype V] [DecidableEq V]
    (c:q4 V) (A:Fin 4 → Finset V) (r d :ℕ) (hr:2 ≤ r)
    (hN:8*r < Fintype.card V) (h:rM c A d)
    (hsize: ∀ i,r+2*d+1 ≤ (A i).card) :
    ∃ k,cycleGraph (2*r+1) ⊑ c.graph k :=by
  classical
  by_contra hn
  have hno: ∀ k,¬ cycleGraph (2*r+1) ⊑ c.graph k :=fun k hk=> hn ⟨k,hk⟩
  have hclique:=h.zP r hr hsize hno
  have hcover: ∀ x:V,∃ i,x ∈ A i ∨ ∀ a ∈ A i,(c.graph (qM i)).Adj x a:=by
    intro x
    by_cases hex: ∃ i,x ∈ A i
    · obtain ⟨i,hi⟩ :=hex
      exact ⟨i,Or.inl hi⟩
    · have hx: ∀ i,x ∉ A i:=fun i hi=> hex ⟨i,hi⟩
      obtain ⟨i,hi⟩ :=h.u4 r hr hsize hno x hx
      exact ⟨i,Or.inr hi⟩
  have hbound:=vD (fun i => c.graph (qM i)) A r
    (by omega) (fun i => by have hi:=hsize i;omega) hclique
    (fun i => hno (qM i)) hcover
  simp only [Fintype.card_fin] at hbound
  omega
end Erdos556
end bf
section bn
namespace Erdos556
open SimpleGraph Finset
theorem ue {V:Type*}
    {G:SimpleGraph V} {a a' b b' x :V}
    (X Y :Finset V) (hdis:Disjoint X Y) (hxX:x ∉ X) (hxY:x ∉ Y) (hb':b' ∈ Y)
    (p:G.Walk a a') (q:G.Walk b' b) (hp:p.IsPath) (hq:q.IsPath) (hL:1 ≤ p.length)
    (hpX: ∀ z ∈ p.support,z ∈ X) (hqY: ∀ z ∈ q.support,z ∈ Y)
    (hxa:G.Adj x a) (hxb:G.Adj x b) (hab:G.Adj a' b') :
    ∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=p.length+q.length+3:=by
  classical
  have hxP:x ∉ p.support:=fun h => hxX (hpX x h)
  have hp': (Walk.cons hxa p).IsPath:= (Walk.cons_isPath_iff _ _).mpr ⟨hp,hxP⟩
  have hdis':Disjoint (insert x X) Y :=by
    apply Finset.disjoint_left.mpr
    intro z hz hzY
    rcases mem_insert.mp hz with hzx | hzX
    · exact hxY (hzx ▸ hzY)
    · exact (Finset.disjoint_left.mp hdis hzX) hzY
  have hp'X: ∀ z ∈ (Walk.cons hxa p).support,z ∈ insert x X:=by
    intro z hz
    rw [Walk.support_cons,List.mem_cons] at hz
    rcases hz with hz | hz
    · exact mem_insert.mpr (Or.inl hz)
    · exact mem_insert_of_mem (hpX z hz)
  obtain ⟨v,c,hc,hlen⟩ :=ri (insert x X) Y hdis' hb'
    (Walk.cons hxa p) q hp' hq (by rw [Walk.length_cons];omega) hp'X hqY hxb hab
  exact ⟨v,c,hc,by rw [Walk.length_cons] at hlen;omega⟩
end Erdos556
end bn
section bw
namespace Erdos556
open SimpleGraph Finset
theorem rm {V:Type*} [DecidableEq V]
    (c:q4 V) (A:Fin 4 → Finset V) (r d :ℕ) (hr:4 ≤ r)
    (hdis: ∀ i j,i ≠ j → Disjoint (A i) (A j))
    (hsize: ∀ i,r+2*d+1 ≤ (A i).card)
    (hred02:qi (c.graph 0) (A 0) (A 2) d)
    (hred13:qi (c.graph 0) (A 1) (A 3) d)
    (hdiag: ∀ b ∈ A 1,∀ z ∈ A 2,¬ (c.graph 2).Adj b z)
    (x:V) (hx: ∀ i,x ∉ A i) (u:Fin 4 → V) (hu: ∀ i,u i ∈ A i)
    (h0: (c.graph 0).Adj x (u 0)) (h3: (c.graph 0).Adj x (u 3))
    (h1: (c.graph 1).Adj x (u 1)) (h2: (c.graph 1).Adj x (u 2)) :
    cycleGraph (2*r+1) ⊑ c.graph 0 ∨ cycleGraph (2*r+1) ⊑ c.graph 1 :=by
  classical
  by_cases hex: ∃ b ∈ A 1,∃ z ∈ A 2,(c.graph 0).Adj b z
  · obtain ⟨b,hb,z,hz,hbz⟩ :=hex
    obtain ⟨p,hp,hplen,hpS⟩ :=rt (c.graph 0) (r-2) d
      (by omega) (A 0) (A 2) (hdis 0 2 (by decide)) hred02
      (by have h :=hsize 0;omega) (by have h :=hsize 2;omega) (u 0) z (hu 0) hz
    obtain ⟨q,hq,hqlen,hqS⟩ :=rt (c.graph 0) 2 d
      (by decide) (A 1) (A 3) (hdis 1 3 (by decide)) hred13
      (by have h :=hsize 1;omega) (by have h :=hsize 3;omega) b (u 3) hb (hu 3)
    have hXY:Disjoint (A 0 ∪ A 2) (A 1 ∪ A 3) :=by
      rw [Finset.disjoint_union_left,Finset.disjoint_union_right,Finset.disjoint_union_right]
      exact ⟨⟨hdis 0 1 (by decide),hdis 0 3 (by decide)⟩,
        ⟨hdis 2 1 (by decide),hdis 2 3 (by decide)⟩⟩
    have hxX:x ∉ A 0 ∪ A 2:=by simp only [mem_union,not_or];exact ⟨hx 0,hx 2⟩
    have hxY:x ∉ A 1 ∪ A 3:=by simp only [mem_union,not_or];exact ⟨hx 1,hx 3⟩
    obtain ⟨v,w,hw,hwlen⟩ :=ue
      (A 0 ∪ A 2) (A 1 ∪ A 3) hXY hxX hxY (mem_union_left _ hb) p q hp hq
      (by omega) hpS hqS h0 h3 hbz.symm
    left
    exact (cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr ⟨v,w,hw,by omega⟩
  · have hblue: ∀ b ∈ A 1,∀ z ∈ A 2,(c.graph 1).Adj b z:=by
      intro b hb z hz
      have hbzne:b ≠ z:=fun h => (Finset.disjoint_left.mp (hdis 1 2 (by decide)) hb) (h ▸ hz)
      rcases sN (c.colour b z) with h | h | h
      · exact (hex ⟨b,hb,z,hz,⟨hbzne,h⟩⟩).elim
      · exact ⟨hbzne,h⟩
      · exact (hdiag b hb z hz ⟨hbzne,h⟩).elim
    right
    exact (cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr
      (rx (c.graph 1) (A 1) (A 2) r (by omega)
        (hdis 1 2 (by decide)) (by have h :=hsize 1;omega) (by have h :=hsize 2;omega)
        hblue x (u 1) (u 2) (hx 1) (hx 2) (hu 1) (hu 2) h1 h2)
end Erdos556
end bw
section bk
namespace Erdos556
open SimpleGraph Finset
structure FourCorePatternOne {V:Type*} [DecidableEq V]
    (c:q4 V) (A:Fin 4 → Finset V) (d:ℕ) : Prop where
  disjoint: ∀ i j,i ≠ j → Disjoint (A i) (A j)
  red02:qi (c.graph 0) (A 0) (A 2) d
  red13:qi (c.graph 0) (A 1) (A 3) d
  blue01:qi (c.graph 1) (A 0) (A 1) d
  blue23:qi (c.graph 1) (A 2) (A 3) d
structure rZ {V:Type*} [DecidableEq V]
    (c:q4 V) (A:Fin 4 → Finset V) (d:ℕ) : Prop
    extends FourCorePatternOne c A d where
  noGreen03: ∀ a ∈ A 0,∀ b ∈ A 3,¬ (c.graph 2).Adj a b
  noGreen12: ∀ a ∈ A 1,∀ b ∈ A 2,¬ (c.graph 2).Adj a b
theorem FourCorePatternOne.zP {V:Type*} [DecidableEq V]
    {c:q4 V} {A:Fin 4 → Finset V} {d:ℕ}
    (h:FourCorePatternOne c A d) (r:ℕ) (hr:2 ≤ r)
    (hsize: ∀ i,r+2*d+1 ≤ (A i).card)
    (hno: ∀ k,¬ cycleGraph (2*r+1) ⊑ c.graph k) :
    ∀ i,(c.graph 2).IsClique (A i :Set V) :=by
  have hside (i j :Fin 4) (k:Fin 3) (hij:i ≠ j)
      (hd:qi (c.graph k) (A i) (A j) d) :
      ∀ u ∈ A i,∀ v ∈ A i,¬ (c.graph k).Adj u v:=
    ro (c.graph k) (A i) (A j) r d (by omega)
      (h.disjoint i j hij) hd (hsize i) (by have hj:=hsize j;omega) (hno k)
  intro i
  apply c.r7 (A i) 0 1 2 sN
  · fin_cases i
    · exact hside 0 2 0 (by decide) h.red02
    · exact hside 1 3 0 (by decide) h.red13
    · exact hside 2 0 0 (by decide) h.red02.symm
    · exact hside 3 1 0 (by decide) h.red13.symm
  · fin_cases i
    · exact hside 0 1 1 (by decide) h.blue01
    · exact hside 1 0 1 (by decide) h.blue01.symm
    · exact hside 2 3 1 (by decide) h.blue23
    · exact hside 3 2 1 (by decide) h.blue23.symm
theorem t6: ∀ k:Fin 4 → Fin 3,(∀ i,k i ≠ 2) →
    (k 0 =0 ∧ k 2=0) ∨ (k 1 =0 ∧ k 3=0) ∨
    (k 0 =1 ∧ k 1=1) ∨ (k 2 =1 ∧ k 3=1) ∨
    (k 0 =0 ∧ k 1=1 ∧ k 2=1 ∧ k 3=0) ∨
    (k 0 =1 ∧ k 1=0 ∧ k 2=0 ∧ k 3=1) :=by decide
def sn (i:Fin 4) : Fin 4 := ![1,0,3,2] i
theorem zX:Function.Injective sn:=by decide
theorem rZ.u4 {V:Type*} [DecidableEq V]
    {c:q4 V} {A:Fin 4 → Finset V} {d:ℕ}
    (h:rZ c A d) (r:ℕ) (hr:4 ≤ r)
    (hsize: ∀ i,r+2*d+1 ≤ (A i).card)
    (hno: ∀ k,¬ cycleGraph (2*r+1) ⊑ c.graph k)
    (x:V) (hx: ∀ i,x ∉ A i) : ∃ i,∀ a ∈ A i,(c.graph 2).Adj x a:=by
  classical
  by_contra hn
  push Not at hn
  choose u hu hbad using hn
  have hne (i:Fin 4) : x ≠ u i :=by intro he;exact hx i (he.symm ▸ hu i)
  have hcolour (i:Fin 4) : c.colour x (u i) ≠ 2:=fun he=> hbad i ⟨hne i,he⟩
  have havoid (i j :Fin 4) (k:Fin 3) (hij:i ≠ j)
      (hd:qi (c.graph k) (A i) (A j) d) :
      ¬ (c.colour x (u i) = k ∧ c.colour x (u j) = k) :=by
    intro he
    apply rG (c.graph k) (A i) (A j) r d (by omega)
      (h.disjoint i j hij) hd (by have hi:=hsize i;omega) (by have hj:=hsize j;omega)
      (hno k) x (hx i) (hx j) (u i) (u j) (hu i) (hu j)
    exact ⟨⟨hne i,he.1⟩,⟨hne j,he.2⟩⟩
  rcases t6 (fun i => c.colour x (u i)) hcolour with
    he | he | he | he | he | he
  · exact havoid 0 2 0 (by decide) h.red02 he
  · exact havoid 1 3 0 (by decide) h.red13 he
  · exact havoid 0 1 1 (by decide) h.blue01 he
  · exact havoid 2 3 1 (by decide) h.blue23 he
  · have hout:=rm c A r d hr h.disjoint hsize
      h.red02 h.red13 h.noGreen12 x hx u hu
      ⟨hne 0,he.1⟩ ⟨hne 3,he.2.2.2⟩ ⟨hne 1,he.2.1⟩ ⟨hne 2,he.2.2.1⟩
    exact hout.elim (hno 0) (hno 1)
  · let A':=fun i => A (sn i)
    let u':=fun i => u (sn i)
    have hdis': ∀ i j,i ≠ j → Disjoint (A' i) (A' j) :=
      fun i j hij=> h.disjoint _ _ (zX.ne hij)
    have hout:=rm c A' r d hr hdis'
      (fun i => hsize (sn i)) h.red13 h.red02 h.noGreen03
      x (fun i => hx (sn i)) u' (fun i => hu (sn i))
      ⟨hne 1,he.2.1⟩ ⟨hne 2,he.2.2.1⟩ ⟨hne 0,he.1⟩ ⟨hne 3,he.2.2.2⟩
    exact hout.elim (hno 0) (hno 1)
theorem sA {V:Type*} [Fintype V] [DecidableEq V]
    (c:q4 V) (A:Fin 4 → Finset V) (r d :ℕ) (hr:4 ≤ r)
    (hN:8*r < Fintype.card V) (h:rZ c A d)
    (hsize: ∀ i,r+2*d+1 ≤ (A i).card) : ∃ k,cycleGraph (2*r+1) ⊑ c.graph k :=by
  classical
  by_contra hn
  have hno: ∀ k,¬ cycleGraph (2*r+1) ⊑ c.graph k :=fun k hk=> hn ⟨k,hk⟩
  have hclique:=h.toFourCorePatternOne.zP r (by omega) hsize hno
  have hcover: ∀ x:V,∃ i,x ∈ A i ∨ ∀ a ∈ A i,(c.graph 2).Adj x a:=by
    intro x
    by_cases hex: ∃ i,x ∈ A i
    · obtain ⟨i,hi⟩ :=hex
      exact ⟨i,Or.inl hi⟩
    · have hx: ∀ i,x ∉ A i:=fun i hi=> hex ⟨i,hi⟩
      obtain ⟨i,hi⟩ :=h.u4 r hr hsize hno x hx
      exact ⟨i,Or.inr hi⟩
  have hbound:=vD (fun _ :Fin 4 => c.graph 2) A r
    (by omega) (fun i => by have hi:=hsize i;omega) hclique (fun _ => hno 2) hcover
  simp only [Fintype.card_fin] at hbound
  omega
end Erdos556
end bk
section bN
namespace Erdos556
open SimpleGraph Finset
theorem FourCorePatternOne.al {V:Type*} [DecidableEq V]
    {c:q4 V} {A:Fin 4 → Finset V} {d:ℕ}
    (h:FourCorePatternOne c A d) (r:ℕ) (hr:4 ≤ r)
    (hsize: ∀ i,r+2*d+3 ≤ (A i).card)
    (hno: ∀ k,¬ cycleGraph (2*r+1) ⊑ c.graph k) :
    ∃ C :Fin 4 → Finset V,rZ c C d ∧
      ∀ i,r+2*d+1 ≤ (C i).card:=by
  classical
  have hclique:=h.zP r (by omega) (fun i => by have hi:=hsize i;omega) hno
  have hmatch03:=rj (c.graph 2) (A 0) (A 3)
    (h.disjoint 0 3 (by decide)) (hclique 0) (hclique 3) r (by omega)
    (by have hi:=hsize 0;omega) (by have hi:=hsize 3;omega) (hno 2)
  have hmatch12:=rj (c.graph 2) (A 1) (A 2)
    (h.disjoint 1 2 (by decide)) (hclique 1) (hclique 2) r (by omega)
    (by have hi:=hsize 1;omega) (by have hi:=hsize 2;omega) (hno 2)
  obtain ⟨Z₁,hZ₁,hcover₁⟩ :=ra (A 0) (A 3) (c.graph 2).Adj
    (fun a ha a' ha' b hb b' hb' hab hab'=> hmatch03 a a' b b' ha ha' hb hb' hab hab')
  obtain ⟨Z₂,hZ₂,hcover₂⟩ :=ra (A 1) (A 2) (c.graph 2).Adj
    (fun a ha a' ha' b hb b' hb' hab hab'=> hmatch12 a a' b b' ha ha' hb hb' hab hab')
  let Z :=Z₁ ∪ Z₂
  let C :=fun i => A i \ Z
  have hZ:Z.card ≤ 2:= (card_union_le Z₁ Z₂).trans (by omega)
  have hsub (i:Fin 4) : C i ⊆ A i:=sdiff_subset
  have hp:FourCorePatternOne c C d :=
    { disjoint:=fun i j hij=> (h.disjoint i j hij).mono (hsub i) (hsub j)
      red02:=h.red02.mono (hsub 0) (hsub 2)
      red13:=h.red13.mono (hsub 1) (hsub 3)
      blue01:=h.blue01.mono (hsub 0) (hsub 1)
      blue23:=h.blue23.mono (hsub 2) (hsub 3)}
  have hgreen03: ∀ a ∈ C 0,∀ b ∈ C 3,¬ (c.graph 2).Adj a b:=by
    intro a ha b hb hab
    rcases hcover₁ a (hsub 0 ha) b (hsub 3 hb) hab with h | h
    · exact (mem_sdiff.mp ha).2 (mem_union_left Z₂ h)
    · exact (mem_sdiff.mp hb).2 (mem_union_left Z₂ h)
  have hgreen12: ∀ a ∈ C 1,∀ b ∈ C 2,¬ (c.graph 2).Adj a b:=by
    intro a ha b hb hab
    rcases hcover₂ a (hsub 1 ha) b (hsub 2 hb) hab with h | h
    · exact (mem_sdiff.mp ha).2 (mem_union_right Z₁ h)
    · exact (mem_sdiff.mp hb).2 (mem_union_right Z₁ h)
  refine ⟨C,{ toFourCorePatternOne:=hp,noGreen03:=hgreen03,noGreen12:=hgreen12},?_⟩
  intro i
  have hc:=card_sdiff_add_card_inter (A i) Z
  have hi: ((A i) ∩ Z).card ≤ 2:= (card_le_card inter_subset_right).trans hZ
  have hs:=hsize i
  change r +2*d+1 ≤ (A i \ Z).card
  omega
theorem ul {V:Type*} [Fintype V] [DecidableEq V]
    (c:q4 V) (A:Fin 4 → Finset V) (r d :ℕ) (hr:4 ≤ r)
    (hN:8*r < Fintype.card V) (h:FourCorePatternOne c A d)
    (hsize: ∀ i,r+2*d+3 ≤ (A i).card) : ∃ k,cycleGraph (2*r+1) ⊑ c.graph k :=by
  classical
  by_contra hn
  have hno: ∀ k,¬ cycleGraph (2*r+1) ⊑ c.graph k :=fun k hk=> hn ⟨k,hk⟩
  obtain ⟨C,hC,hCs⟩ :=h.al r hr hsize hno
  exact hn (sA c C r d hr hN hC hCs)
end Erdos556
end bN
section aS
namespace Erdos556
open SimpleGraph Finset
theorem uJ {V:Type*}
    [Fintype V] [DecidableEq V] (c:q4 V) (r d :ℕ)
    (hr:4 ≤ r) (hN:8*r < Fintype.card V)
    (h:yA c (r+2*d+3) d) :
    ∃ i,cycleGraph (2*r+1) ⊑ c.graph i :=by
  classical
  obtain ⟨s,k,hs,hk,hpat⟩ :=uO
    h.profiles h.dimension h.profile_disjoint
  let e :Fin 3 ≃ Fin 3 :=Equiv.ofBijective k ⟨hk,(Finite.injective_iff_surjective).mp hk⟩
  let c':=c.relabel e
  let A :Fin 4 → Finset V :=fun i => h.cores (s i)
  have hgraph (i:Fin 3) : c'.graph i =c.graph (k i) :=c.dZ e i
  have hdis (i j :Fin 4) (hij:i ≠ j) : Disjoint (A i) (A j) :=
    h.core_disjoint _ _ (hs.ne hij)
  have hlarge (i:Fin 4) : r+2*d+3 ≤ (A i).card:=h.large (s i)
  have hdense (a b :Fin 4) (i:Fin 3)
      (hsep:q5 (h.profiles (s a)) (h.profiles (s b)) (k i)) :
      qi (c'.graph i) (A a) (A b) d :=by
    have hh:=h.dense (s a) (s b) (k i) hsep
    simpa only [hgraph] using hh
  have hcycle: ∃ i,cycleGraph (2*r+1) ⊑ c'.graph i :=by
    rcases hpat with hp | hp
    · obtain ⟨h02,h13,h01,h23⟩ :=hp
      have hpattern:FourCorePatternOne c' A d:=
        ⟨hdis,hdense 0 2 0 h02,hdense 1 3 0 h13,hdense 0 1 1 h01,hdense 2 3 1 h23⟩
      exact ul c' A r d hr hN hpattern hlarge
    · obtain ⟨h02,h03,h12,h13,h01,h23⟩ :=hp
      have hpattern:rM c' A d:=
        ⟨hdis,hdense 0 2 0 h02,hdense 0 3 0 h03,hdense 1 2 0 h12,
          hdense 1 3 0 h13,hdense 0 1 1 h01,hdense 2 3 2 h23⟩
      exact uo c' A r d (by omega) hN hpattern
        (fun i => by have hh:=hlarge i;omega)
  obtain ⟨i,hi⟩ :=hcycle
  rw [hgraph] at hi
  exact ⟨k i,hi⟩
end Erdos556
end aS
section bp
namespace Erdos556
open SimpleGraph
theorem wM:
    ∃ n₀:ℕ,∀ n:ℕ,n₀ ≤ n → Odd n → rr n (4*n-3) :=by
  obtain ⟨n₁,hclean⟩ :=
    zI qC y8
  obtain ⟨R₀,hrefine⟩ :=wG
  refine ⟨max n₁ (2*max R₀ 4 +1),?_⟩
  intro n hn hodd c
  classical
  obtain ⟨r,hr⟩ :=hodd
  have hnrepr:n=2*r+1:=by omega
  subst n
  have hlarge:n₁ ≤ 2*r+1:= (le_max_left _ _).trans hn
  have hr₀:R₀ ≤ r:=by omega
  have hr4:4 ≤ r:=by omega
  have hodd:Odd (2*r+1) := ⟨r,by omega⟩
  by_contra hnot
  have hno: ∀ i,¬ cycleGraph (2*r+1) ⊑ c.graph i :=fun i hi=> hnot ⟨i,hi⟩
  obtain ⟨h⟩ :=hclean c (2*r+1) hlarge hodd (by simp only [Fintype.card_fin]) hno
  obtain ⟨cores⟩ :=ww h (hrefine c r hr₀ hno h)
  have horder:8*r < Fintype.card (Fin (4* (2*r+1) - 3)) :=by
    simp only [Fintype.card_fin]
    omega
  exact hnot (uJ c r h.defect hr4 horder cores)
theorem erdos556:
    ∃ n₀:ℕ,∀ n:ℕ,n₀ ≤ n → Odd n → sS n =4*n-3:=by
  obtain ⟨n₁,hupper⟩ :=wM
  refine ⟨max n₁ 3,?_⟩
  intro n hn hodd
  apply le_antisymm
  · exact xk (hupper n (by omega) hodd)
  · exact wB n (by omega) hodd
end Erdos556
end bp
namespace OMA556
open SimpleGraph
theorem aq {V:Type*} (c:Erdos556.q4 V) :
    (⊤ : SimpleGraph V).IsEdgeColouring c.graph:=by
  constructor
  · ext u v
    rw [top_adj,iSup_adj]
    constructor
    · intro huv
      exact ⟨c.colour u v,huv,rfl⟩
    · rintro ⟨i,hi⟩
      exact hi.1
  · intro i j hij
    apply disjoint_iff_inf_le.mpr
    intro u v h
    exact (hij (h.1.2.symm.trans h.2.2)).elim
theorem ap {V:Type*} (c:Fin 3 → SimpleGraph V)
    (hc: (⊤ : SimpleGraph V).IsEdgeColouring c) :
    ∃ d :Erdos556.q4 V,∀ i,d.graph i =c i:=by
  classical
  have exists_colour (u v :V) (huv:u ≠ v) : ∃ i,(c i).Adj u v:=by
    apply iSup_adj.mp
    rw [← hc.1]
    exact (top_adj _ _).mpr huv
  have unique_colour {u v :V} {i j :Fin 3}
      (hi: (c i).Adj u v) (hj: (c j).Adj u v) : i=j:=by
    by_contra hij
    exact (disjoint_iff_inf_le.mp (hc.2 i j hij)) ⟨hi,hj⟩
  let col (u v :V) : Fin 3 :=
    if h :u=v then 0 else Classical.choose (exists_colour u v h)
  have chosen {u v :V} (h:u ≠ v) : (c (col u v)).Adj u v:=by
    dsimp only [col]
    rw [dif_neg h]
    exact Classical.choose_spec (exists_colour u v h)
  have symm (u v :V) : col u v=col v u:=by
    by_cases huv:u=v
    · subst v;rfl
    · exact unique_colour (chosen huv) (chosen (Ne.symm huv)).symm
  let d :Erdos556.q4 V := ⟨col,symm⟩
  refine ⟨d,?_⟩
  intro i
  ext u v
  change (u ≠ v ∧ col u v=i) ↔ (c i).Adj u v
  constructor
  · rintro ⟨huv,hi⟩
    simpa only [hi] using chosen huv
  · intro hi
    exact ⟨hi.ne,unique_colour (chosen hi.ne) hi⟩
theorem aM (n:ℕ) :
    multicolourRamsey (cycleGraph n) 3 =Erdos556.sS n :=by
  unfold multicolourRamsey Erdos556.sS
  congr 1
  ext m
  constructor
  · intro h c
    exact h c.graph (aq c)
  · intro h c hc
    obtain ⟨d,hd⟩ :=ap c hc
    obtain ⟨i,hi⟩ :=h d
    rw [hd] at hi
    exact ⟨i,hi⟩
theorem b0
    (h: ∃ n₀:ℕ,∀ n:ℕ,n₀ ≤ n → Odd n →
      Erdos556.sS n =4*n-3) :
    type_of% @Erdos556.erdos_556.variants.kss_large_odd:=by
  obtain ⟨n₀,hn₀⟩ :=h
  filter_upwards [Filter.eventually_ge_atTop n₀] with n hn ho
  rw [aM]
  exact hn₀ n hn ho
end OMA556
theorem OMA.solution : OMA.R_Erdos556_erdos_556_variants_luczak_asymptotic_R1.H2 := by
  obtain ⟨n₀, hupper⟩ := Erdos556.wM
  filter_upwards [Filter.eventually_ge_atTop n₀] with n hn ho
  intro c hc
  obtain ⟨d, hd⟩ := OMA556.ap c hc
  obtain ⟨i, hi⟩ := hupper n hn ho d
  rw [hd] at hi
  exact ⟨i, hi⟩
