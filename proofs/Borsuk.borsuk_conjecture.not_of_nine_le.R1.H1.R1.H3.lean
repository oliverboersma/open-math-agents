import OMAReductions.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1_H1_R1

/-!
The incidence lemmas and the finite obstruction certificate are adapted from OpenAI,
github.com/openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/Geometry/Borsuk/TenLabels and FiniteCases, used under Apache-2.0.

A triple or quadruple is indexed by its ten-bit set mask and one tag bit. Each
starting clause follows from an incidence rule. For each later clause, assume all
its literals false and propagate the listed earlier clauses to a contradiction.
The final clause is empty. Each propagation check is independently kernel reduced.
-/

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction

abbrev Labels := Fin 10
abbrev Family := Finset Labels → Prop

open scoped Classical

structure TenSystem (T Q : Family) : Prop where
  tetra_card : ∀ S, Q S → S.card = 4
  down : ∀ S U, Q S → U ⊆ S → U.card = 3 → T U
  pure : ∀ U, T U → ∃ S, Q S ∧ U ⊆ S
  no_boundary : ∀ S U, Q S → U ⊆ S → U.card = 3 →
    ∃ S', Q S' ∧ U ⊆ S' ∧ S' ≠ S
  complementary : ∀ S U, Q S → U ⊆ Sᶜ → U.card = 3 →
    (T U ↔ ¬ T (Sᶜ \ U))
  pair_count : ∀ S P, Q S → P ⊆ Sᶜ → P.card = 2 →
    ((Sᶜ \ P).filter (fun w => T (insert w P))).card = 2

variable {T Q : Family}

lemma filter_card_eq_two_three_pos {s r : Finset Labels} {p : Labels → Prop}
    [DecidablePred p] (hs : s.card = 4) (hr : r.card = 3) (hrs : r ⊆ s)
    (hp : (s.filter p).card = 2) : ∃ x ∈ r, p x := by
  by_contra hn
  have hsub : s.filter p ⊆ s \ r := by
    intro x hx
    obtain ⟨hxs, hpx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_sdiff.mpr ⟨hxs, ?_⟩
    intro hxr
    exact hn ⟨x, hxr, hpx⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hrs, hs, hr, hp] at hc
  norm_num at hc

lemma filter_card_eq_two_three_neg {s r : Finset Labels} {p : Labels → Prop}
    [DecidablePred p] (hr : r.card = 3) (hrs : r ⊆ s)
    (hp : (s.filter p).card = 2) : ∃ x ∈ r, ¬ p x := by
  by_contra hn
  have hsub : r ⊆ s.filter p := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨hrs hx, ?_⟩
    by_contra hnp
    exact hn ⟨x, hx, hnp⟩
  have hc := Finset.card_le_card hsub
  rw [hr, hp] at hc
  norm_num at hc

lemma three_pos (h : TenSystem T Q) (S P R : Finset Labels)
    (hS : Q S) (hP : P ⊆ Sᶜ) (hcP : P.card = 2)
    (hR : R ⊆ Sᶜ \ P) (hcR : R.card = 3) :
    ∃ w ∈ R, T (insert w P) := by
  classical
  apply filter_card_eq_two_three_pos (s := Sᶜ \ P) (r := R) ?_ hcR hR
    (h.pair_count S P hS hP hcP)
  rw [Finset.card_sdiff_of_subset hP, Finset.card_compl, h.tetra_card S hS, hcP]
  decide

lemma three_neg (h : TenSystem T Q) (S P R : Finset Labels)
    (hS : Q S) (hP : P ⊆ Sᶜ) (hcP : P.card = 2)
    (hR : R ⊆ Sᶜ \ P) (hcR : R.card = 3) :
    ∃ w ∈ R, ¬ T (insert w P) := by
  classical
  exact filter_card_eq_two_three_neg hcR hR (h.pair_count S P hS hP hcP)

lemma tetra_extension {S U : Finset Labels} (hU : U ⊆ S)
    (hcS : S.card = 4) (hcU : U.card = 3) :
    ∃ v, v ∉ U ∧ S = insert v U := by
  have hcard : (S \ U).card = 1 := by
    rw [Finset.card_sdiff_of_subset hU, hcS, hcU]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  have hm : v ∈ S \ U := by rw [hv]; simp
  refine ⟨v, (Finset.mem_sdiff.mp hm).2, ?_⟩
  have he := Finset.sdiff_union_of_subset hU
  rw [hv] at he
  simpa using he.symm

@[simp] lemma map_compl (e : Equiv.Perm Labels) (S : Finset Labels) :
    Sᶜ.map e.toEmbedding = (S.map e.toEmbedding)ᶜ := by
  ext x
  simp

@[simp] lemma map_symm_map (e : Equiv.Perm Labels) (S : Finset Labels) :
    (S.map e.symm.toEmbedding).map e.toEmbedding = S := by
  ext x
  simp

@[simp] lemma symm_map_map (e : Equiv.Perm Labels) (S : Finset Labels) :
    (S.map e.toEmbedding).map e.symm.toEmbedding = S := by
  ext x
  simp

lemma TenSystem.relabel (h : TenSystem T Q) (e : Equiv.Perm Labels) :
    TenSystem (fun U => T (U.map e.toEmbedding))
      (fun S => Q (S.map e.toEmbedding)) := by
  constructor
  · intro S hS
    simpa using h.tetra_card _ hS
  · intro S U hS hUS hcU
    exact h.down _ _ hS (Finset.map_subset_map.mpr hUS) (by simpa using hcU)
  · intro U hU
    obtain ⟨S, hS, hUS⟩ := h.pure _ hU
    refine ⟨S.map e.symm.toEmbedding, ?_, ?_⟩
    · simpa using hS
    · have hh := (Finset.map_subset_map (f := e.symm.toEmbedding)).mpr hUS
      simpa using hh
  · intro S U hS hUS hcU
    obtain ⟨S', hS', hUS', hne⟩ := h.no_boundary _ _ hS
      (Finset.map_subset_map.mpr hUS) (by simpa using hcU)
    refine ⟨S'.map e.symm.toEmbedding, ?_, ?_, ?_⟩
    · simpa using hS'
    · have hh := (Finset.map_subset_map (f := e.symm.toEmbedding)).mpr hUS'
      simpa using hh
    · intro he
      have hh := congrArg (Finset.map e.toEmbedding) he
      exact hne (by simpa using hh)
  · intro S U hS hUS hcU
    have hh := h.complementary _ _ hS
      (show U.map e.toEmbedding ⊆ (S.map e.toEmbedding)ᶜ by
        rw [← map_compl]
        exact Finset.map_subset_map.mpr hUS)
      (by simpa using hcU)
    simpa [Finset.map_sdiff] using hh
  · intro S P hS hPS hcP
    have hh := h.pair_count _ _ hS
      (show P.map e.toEmbedding ⊆ (S.map e.toEmbedding)ᶜ by
        rw [← map_compl]
        exact Finset.map_subset_map.mpr hPS)
      (by simpa using hcP)
    rw [← map_compl, ← Finset.map_sdiff, Finset.filter_map, Finset.card_map] at hh
    simpa only [Function.comp_apply, Finset.map_insert] using hh

end BorsukNine.FiniteObstruction

end OAI

namespace BorsukCert
abbrev Lit := ℕ × Bool
def rawAux : ℕ → ℕ → List Lit
  | 0, _ => []
  | k+1, n => if n=0 then [] else
      let u := n%4096-1
      (u/2,decide (u%2=1)) :: rawAux k (n/4096)
def raw := rawAux 25
def Hits (a : ℕ → Bool) (l : Lit) := a l.1 = l.2
def ValidList (a : ℕ → Bool) (ls : List Lit) := ∃ l ∈ ls, Hits a l
abbrev H (a : ℕ → Bool) (c : ℕ) := ValidList a (raw c)
abbrev Checked (a : ℕ → Bool) := {c : ℕ // H a c}
def pack {a : ℕ → Bool} {c : ℕ} (h : H a c) : Checked a := ⟨c,h⟩
def flip (l : Lit) : Lit := (l.1,!l.2)
def code (l : Lit) := 2*l.1 + l.2.toNat
theorem code_inj {l u : Lit} (h : code l = code u) : l = u := by
  obtain ⟨i,b⟩ := l
  obtain ⟨j,d⟩ := u
  cases b <;> cases d <;> simp_all [code,Bool.toNat] <;> omega
def mark (bad : ℕ) (l : Lit) := bad ||| 2^(code l)
theorem marked {bad : ℕ} {l u : Lit} :
    (mark bad u).testBit (code l) = true ↔ bad.testBit (code l) = true ∨ u=l := by
  simp [mark,Nat.testBit_two_pow,show (code u = code l) ↔ u=l from ⟨code_inj,congrArg code⟩]
def initial (ls : List Lit) := ls.foldr (fun l b => mark b l) 0
theorem initial_mem {ls : List Lit} {l : Lit} :
    (initial ls).testBit (code l) = true → l ∈ ls := by
  induction ls with
  | nil => simp [initial]
  | cons u ls ih =>
    intro h
    rcases marked.mp h with hb | rfl
    · exact List.mem_cons_of_mem _ (ih hb)
    · simp
def propagate (bad : ℕ) : List ℕ → Bool
  | [] => false
  | c :: cs =>
    match (raw c).filter (fun l => !bad.testBit (code l)) with
    | [] => true
    | [l] => propagate (mark bad (flip l)) cs
    | _ => false
theorem propagation {a : ℕ → Bool} (cs : List ℕ) (bad : ℕ)
    (hv : ∀ c ∈ cs, H a c) (hf : ∀ l, bad.testBit (code l) = true → ¬Hits a l)
    (ok : propagate bad cs = true) : False := by
  induction cs generalizing bad with
  | nil => simp [propagate] at ok
  | cons c cs ih =>
    obtain ⟨l,hl,ht⟩ := hv c (by simp)
    have hn : bad.testBit (code l) ≠ true := fun hb => hf l hb ht
    have hm : l ∈ (raw c).filter (fun l => !bad.testBit (code l)) := List.mem_filter.mpr ⟨hl,by simpa using hn⟩
    unfold propagate at ok
    split at ok
    next he => rw [he] at hm; exact List.not_mem_nil hm
    next u he =>
      rw [he] at hm
      have eq : l = u := by simpa using hm
      subst u
      apply ih (mark bad (flip l)) (fun k hk => hv k (by simp [hk])) _ ok
      intro x hx hxv
      rcases (marked.mp hx).symm with rfl | hx
      · simp [Hits,flip] at ht hxv
        simp [ht] at hxv
      · exact hf x hx hxv
    next => contradiction
theorem rup {a : ℕ → Bool} {c : ℕ} (xs : List (Checked a))
    (ok : propagate (initial (raw c)) (xs.map Subtype.val) = true) : H a c := by
  by_contra hn
  apply propagation (a := a) (xs.map Subtype.val) (initial (raw c)) _ _ ok
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact x.property
  · intro l hl h
    exact hn ⟨l,initial_mem hl,h⟩
end BorsukCert

open OAI.BorsukNine.FiniteObstruction
namespace BorsukCert
abbrev Face := Finset Labels
local instance : Std.Commutative Nat.lor := ⟨Nat.or_comm⟩
local instance : Std.Associative Nat.lor := ⟨Nat.or_assoc⟩
def bits (s : Face) := s.fold Nat.lor 0 (fun i => 2^i.val)
def face (n : ℕ) : Face := Finset.univ.filter (fun i => n.testBit i.val)
theorem face_bits (s : Face) : face (bits s) = s := by
  ext i
  simp only [face,Finset.mem_filter,Finset.mem_univ,true_and]
  induction s using Finset.induction_on with
  | empty => simp [bits]
  | insert j s hj ih =>
    rw [bits,Finset.fold_insert hj]
    change ((2^j.val ||| bits s).testBit i.val = true) ↔ _
    simp only [Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,ih,Finset.mem_insert,Fin.val_inj]
    tauto
def lit (tag : Bool) (s : Face) (sign : Bool) : Lit := (2*bits s+tag.toNat,sign)
def family (T Q : Family) (t : Bool) := if t then Q else T
noncomputable def faceValue (T Q : Family) (t : Bool) (s : Face) : Bool :=
  @decide (family T Q t s) (Classical.propDecidable _)
noncomputable def coloring (T Q : Family) (n : ℕ) : Bool :=
  faceValue T Q (decide (n%2=1)) (face (n/2))
theorem hit {T Q : Family} {tag sign : Bool} {s : Face} :
    Hits (coloring T Q) (lit tag s sign) ↔
      (if sign then family T Q tag s else ¬family T Q tag s) := by
  classical
  have d0 : 2 * bits s / 2 = bits s := by omega
  have d1 : (2 * bits s + 1) / 2 = bits s := by omega
  have m0 : 2 * bits s % 2 = 0 := by omega
  have m1 : (2 * bits s + 1) % 2 = 1 := by omega
  cases tag <;> cases sign <;> simp [Hits,coloring,lit,Bool.toNat,d0,d1,m0,m1,face_bits] <;> simp [faceValue,family]
def tailLits (tag sign : Bool) (u w : Face) : List Lit :=
  ((List.finRange 10).filter (fun i => i ∈ w)).map (fun i => lit tag (insert i u) sign)
theorem tail_ok {T Q : Family} {tag sign : Bool} {u w : Face} {i : Labels}
    (hw : i ∈ w) (hh : if sign then family T Q tag (insert i u) else ¬family T Q tag (insert i u)) :
    ValidList (coloring T Q) (tailLits tag sign u w) := by
  refine ⟨_,List.mem_map.mpr ⟨i,List.mem_filter.mpr ⟨List.mem_finRange i,by simpa using hw⟩,rfl⟩,hit.mpr hh⟩
def fixed : Face := {0,1,2,3}
def taut : List Lit := [(0,true),(0,false)]
theorem taut_ok (a : ℕ → Bool) : ValidList a taut := by
  cases hb : a 0 with
  | true => exact ⟨(0,true),by decide,hb⟩
  | false => exact ⟨(0,false),by decide,hb⟩
def rule (kind : ℕ) (s u r : Face) : List Lit :=
  match kind with
  | 0 => [lit true fixed true]
  | 1 => if u⊆s ∧ u.card=3 then [lit true s false,lit false u true] else taut
  | 2 => if u⊆s ∧ u.card=3 then lit true s false :: tailLits true true u
      (uᶜ.filter (fun i => insert i u ≠ s)) else taut
  | 3 => if u.card=3 then lit false u false :: tailLits true true u uᶜ else taut
  | 4 => if u⊆sᶜ ∧ u.card=3 then [lit true s false,lit false u true,lit false (sᶜ \ u) true] else taut
  | 5 => if u⊆sᶜ ∧ u.card=3 then [lit true s false,lit false u false,lit false (sᶜ \ u) false] else taut
  | 6 => if u⊆sᶜ ∧ u.card=2 ∧ r⊆sᶜ \ u ∧ r.card=3 then
      lit true s false :: tailLits false true u r else taut
  | _ => if u⊆sᶜ ∧ u.card=2 ∧ r⊆sᶜ \ u ∧ r.card=3 then
      lit true s false :: tailLits false false u r else taut
def seedLits (z : ℕ) := rule (z%8) (face (z/8%1024)) (face (z/8192%1024)) (face (z/8388608%1024))
class Legal (a : ℕ → Bool) : Prop where
  legal : ∀ z, ValidList a (seedLits z)
theorem seed {a : ℕ → Bool} [v : Legal a] {c : ℕ} (z : ℕ) (eq : raw c = seedLits z) : H a c := by
  unfold H
  rw [eq]
  exact v.legal z
end BorsukCert

open OAI.BorsukNine.FiniteObstruction
namespace BorsukCert
theorem valid_cons {a : ℕ → Bool} {l : Lit} {ls : List Lit} :
    ValidList a (l::ls) ↔ Hits a l ∨ ValidList a ls := by
  simp [ValidList]
theorem valid_nil {a : ℕ → Bool} : ¬ValidList a [] := by simp [ValidList]
theorem rule_sound {T Q : Family} (h : TenSystem T Q) (h0 : Q fixed) (k : ℕ) (s u r : Face) :
    ValidList (coloring T Q) (rule k s u r) := by
  classical
  unfold rule
  split
  · simpa [valid_cons,valid_nil,hit,family] using h0
  all_goals split
  all_goals try exact taut_ok _
  all_goals rename_i hc
  all_goals simp only [valid_cons,valid_nil,or_false,hit,Bool.false_eq_true,if_false,if_true,family]
  · by_cases hs : Q s
    · exact Or.inr (h.down _ _ hs hc.1 hc.2)
    · exact Or.inl hs
  · by_cases hs : Q s
    · obtain ⟨v,hv,hus,hne⟩ := h.no_boundary _ _ hs hc.1 hc.2
      obtain ⟨i,hi,rfl⟩ := tetra_extension hus (h.tetra_card v hv) hc.2
      exact Or.inr (tail_ok (i := i) (by simp [hi,hne]) hv)
    · exact Or.inl hs
  · by_cases hu : T u
    · obtain ⟨v,hv,hus⟩ := h.pure _ hu
      obtain ⟨i,hi,rfl⟩ := tetra_extension hus (h.tetra_card v hv) hc
      exact Or.inr (tail_ok (i := i) (by simpa using hi) hv)
    · exact Or.inl hu
  · by_cases hs : Q s
    · have he := h.complementary _ _ hs hc.1 hc.2
      tauto
    · exact Or.inl hs
  · by_cases hs : Q s
    · have he := h.complementary _ _ hs hc.1 hc.2
      tauto
    · exact Or.inl hs
  · by_cases hs : Q s
    · obtain ⟨i,hi,ht⟩ := three_pos h s u r hs hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      exact Or.inr (tail_ok hi ht)
    · exact Or.inl hs
  · by_cases hs : Q s
    · obtain ⟨i,hi,ht⟩ := three_neg h s u r hs hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      exact Or.inr (tail_ok hi ht)
    · exact Or.inl hs
theorem system_legal {T Q : Family} (h : TenSystem T Q) (h0 : Q fixed) : Legal (coloring T Q) :=
  ⟨fun _ => rule_sound h h0 _ _ _ _⟩
end BorsukCert

namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f1 : H a 64 := seed 120 rfl
lemma f2 : H a 122943 := seed 57465 rfl
lemma f3 : H a 0x8204202201200a006003f := seed 57466 rfl
lemma f4 : H a 188479 := seed 90233 rfl
lemma f5 : H a 0x8304302301300b007003f := seed 90234 rfl
lemma f6 : H a 319583 := seed 155833 rfl
lemma f7 : H a 319599 := seed 155865 rfl
lemma f8 : H a 319823 := seed 156313 rfl
lemma f9 : H a 0x8504502500d007006014f := seed 156314 rfl
lemma f10 : H a 320079 := seed 156825 rfl
lemma f11 : H a 581791 := seed 287033 rfl
lemma f12 : H a 581807 := seed 287065 rfl
lemma f13 : H a 581839 := seed 287129 rfl
lemma f14 : H a 582031 := seed 287513 rfl
lemma f15 : H a 582287 := seed 288025 rfl
lemma f16 : H a 582799 := seed 289049 rfl
lemma f17 : H a 583823 := seed 291097 rfl
lemma f18 : H a 0x91051031019015013012010d := seed 548867 rfl
lemma f19 : H a 1106207 := seed 549433 rfl
lemma f20 : H a 1106223 := seed 549465 rfl
lemma f21 : H a 0x91051031019015012012f := seed 549466 rfl
lemma f22 : H a 1106255 := seed 549529 rfl
lemma f23 : H a 0x91051031019013012014f := seed 549530 rfl
lemma f24 : H a 1106319 := seed 549657 rfl
lemma f25 : H a 1107215 := seed 551449 rfl
lemma f26 : H a 0x51031019015013012090f := seed 553498 rfl
lemma f27 : H a 2155039 := seed 1074233 rfl
lemma f28 : H a 2155055 := seed 1074265 rfl
lemma f29 : H a 0xa1061031029025022022f := seed 1074266 rfl
lemma f30 : H a 2155087 := seed 1074329 rfl
lemma f31 : H a 2155151 := seed 1074457 rfl
lemma f32 : H a 4252719 := seed 2123865 rfl
lemma f33 : H a 4252751 := seed 2123929 rfl
lemma f34 : H a 4252815 := seed 2124057 rfl
lemma f35 : H a 4254735 := seed 2127897 rfl
lemma f36 : H a 0xc10a1091089085083082080d := seed 4218883 rfl
lemma f37 : H a 8448031 := seed 4223033 rfl
lemma f38 : H a 8448047 := seed 4223065 rfl
lemma f39 : H a 0xc10a1091089083082084f := seed 4223130 rfl
lemma f40 : H a 0xc10910890850830820a0f := seed 4224026 rfl
lemma f41 : H a 221247 := seed 106617 rfl
lemma f42 : H a 0x8384382381380b807803f := seed 106618 rfl
lemma f43 : H a 0x8584582581580d8078060055 := seed 172035 rfl
lemma f44 : H a 352351 := seed 172217 rfl
lemma f45 : H a 352375 := seed 172265 rfl
lemma f46 : H a 0x8584582581580d8060077 := seed 172266 rfl
lemma f47 : H a 352471 := seed 172457 rfl
lemma f48 : H a 352599 := seed 172713 rfl
lemma f49 : H a 352855 := seed 173225 rfl
lemma f50 : H a 353367 := seed 174249 rfl
lemma f51 : H a 354391 := seed 176297 rfl
lemma f52 : H a 0x8984982981980d80b80a0095 := seed 303107 rfl
lemma f53 : H a 614583 := seed 303465 rfl
lemma f54 : H a 614615 := seed 303529 rfl
lemma f55 : H a 0x8984982980d80b80a0197 := seed 303914 rfl
lemma f56 : H a 615575 := seed 305449 rfl
lemma f57 : H a 616599 := seed 307497 rfl
lemma f58 : H a 0x4982981980d80b80a0897 := seed 307498 rfl
lemma f59 : H a 1138999 := seed 565865 rfl
lemma f60 : H a 0x918518318198158120137 := seed 565866 rfl
lemma f61 : H a 1139031 := seed 565929 rfl
lemma f62 : H a 1139095 := seed 566057 rfl
lemma f63 : H a 1139479 := seed 566825 rfl
lemma f64 : H a 1139991 := seed 567849 rfl
lemma f65 : H a 1141015 := seed 569897 rfl
lemma f66 : H a 0xa18618318298258238220215 := seed 1089539 rfl
lemma f67 : H a 0xa1861831829825823821f := seed 1090618 rfl
lemma f68 : H a 2187831 := seed 1090665 rfl
lemma f69 : H a 2187863 := seed 1090729 rfl
lemma f70 : H a 0xa18618318298238220257 := seed 1090730 rfl
lemma f71 : H a 2187927 := seed 1090857 rfl
lemma f72 : H a 0xa18618318258238220297 := seed 1090858 rfl
lemma f73 : H a 0xa18618298258238220317 := seed 1091114 rfl
lemma f74 : H a 2188823 := seed 1092649 rfl
lemma f75 : H a 0xc18618518498458438420415 := seed 2138115 rfl
lemma f76 : H a 0xc1861851849845843841f := seed 2140218 rfl
lemma f77 : H a 4285495 := seed 2140265 rfl
lemma f78 : H a 4285527 := seed 2140329 rfl
lemma f79 : H a 0xc18618518498438420457 := seed 2140330 rfl
lemma f80 : H a 4285591 := seed 2140457 rfl
lemma f81 : H a 0xc18618518458438420497 := seed 2140458 rfl
lemma f82 : H a 0xc18618498458438420517 := seed 2140714 rfl
lemma f83 : H a 4285975 := seed 2141225 rfl
lemma f84 : H a 0xc18518498458438420617 := seed 2141226 rfl
lemma f85 : H a 4287511 := seed 2144297 rfl
lemma f86 : H a 0x618518498458438420c17 := seed 2144298 rfl
lemma f87 : H a 0xc18a18918898858838820815 := seed 4235267 rfl
lemma f88 : H a 8480799 := seed 4239417 rfl
lemma f89 : H a 0xc18a1891889885883881f := seed 4239418 rfl
lemma f90 : H a 8480823 := seed 4239465 rfl
lemma f91 : H a 0xc18a18918898858820837 := seed 4239466 rfl
lemma f92 : H a 8480855 := seed 4239529 rfl
lemma f93 : H a 0xc18918898858838820a17 := seed 4240426 rfl
lemma f94 : H a 0xa18918898858838820c17 := seed 4241450 rfl
lemma f95 : H a 0x8684682681680e8078070065 := seed 204803 rfl
lemma f96 : H a 417903 := seed 205017 rfl
lemma f97 : H a 0x8684682681680e8070077 := seed 205034 rfl
lemma f98 : H a 418407 := seed 206025 rfl
lemma f99 : H a 0x4682681680e8078070867 := seed 209098 rfl
lemma f100 : H a 681127 := seed 338249 rfl
lemma f101 : H a 0x8a82a81a80e80b80b04a7 := seed 338250 rfl
lemma f102 : H a 0x9285283281a8168138130125 := seed 598019 rfl
lemma f103 : H a 1204527 := seed 598617 rfl
lemma f104 : H a 0x9285283281a8138130167 := seed 598730 rfl
lemma f105 : H a 1204647 := seed 598857 rfl
lemma f106 : H a 1205031 := seed 599625 rfl
lemma f107 : H a 1205543 := seed 600649 rfl
lemma f108 : H a 0x5283281a8168138130927 := seed 602698 rfl
lemma f109 : H a 0xa286283282a8268238230225 := seed 1122307 rfl
lemma f110 : H a 0xa286283282a8268230237 := seed 1123434 rfl
lemma f111 : H a 2253479 := seed 1123657 rfl
lemma f112 : H a 2253607 := seed 1123913 rfl
lemma f113 : H a 0xa286282a8268238230327 := seed 1123914 rfl
lemma f114 : H a 2254375 := seed 1125449 rfl
lemma f115 : H a 0xa283282a8268238230627 := seed 1125450 rfl
lemma f116 : H a 2255399 := seed 1127497 rfl
lemma f117 : H a 0x6283282a8268238230a27 := seed 1127498 rfl
lemma f118 : H a 0xc286285284a8468438430425 := seed 2170883 rfl
lemma f119 : H a 0xc286285284a8468430437 := seed 2173034 rfl
lemma f120 : H a 4351079 := seed 2173129 rfl
lemma f121 : H a 0xc286285284a8438430467 := seed 2173130 rfl
lemma f122 : H a 4351143 := seed 2173257 rfl
lemma f123 : H a 0xc286285284684384304a7 := seed 2173258 rfl
lemma f124 : H a 4351271 := seed 2173513 rfl
lemma f125 : H a 4351527 := seed 2174025 rfl
lemma f126 : H a 4353063 := seed 2177097 rfl
lemma f127 : H a 0xc28a289288a8868838830825 := seed 4268035 rfl
lemma f128 : H a 8546351 := seed 4272217 rfl
lemma f129 : H a 8546359 := seed 4272233 rfl
lemma f130 : H a 0xc28a289288a8868830837 := seed 4272234 rfl
lemma f131 : H a 8546407 := seed 4272329 rfl
lemma f132 : H a 0xc28a289288a8838830867 := seed 4272330 rfl
lemma f133 : H a 0xc28a288a8868838830927 := seed 4272714 rfl
lemma f134 : H a 8546855 := seed 4273225 rfl
lemma f135 : H a 0xc289288a8868838830a27 := seed 4273226 rfl
lemma f136 : H a 0x8c84c82c81c80e80d80d00c5 := seed 401411 rfl
lemma f137 : H a 811215 := seed 401817 rfl
lemma f138 : H a 811239 := seed 401865 rfl
lemma f139 : H a 811463 := seed 402313 rfl
lemma f140 : H a 811719 := seed 402825 rfl
lemma f141 : H a 0x8c84c81c80e80d80d02c7 := seed 402826 rfl
lemma f142 : H a 812231 := seed 403849 rfl
lemma f143 : H a 0x8c82c81c80e80d80d04c7 := seed 403850 rfl
lemma f144 : H a 0x9485483481c8168158150145 := seed 663555 rfl
lemma f145 : H a 0x9485483481c816815814f := seed 664218 rfl
lemma f146 : H a 0x9485483481c8168150157 := seed 664234 rfl
lemma f147 : H a 0x9485483481c8158150167 := seed 664266 rfl
lemma f148 : H a 1335751 := seed 664457 rfl
lemma f149 : H a 0x9485483481681581501c7 := seed 664458 rfl
lemma f150 : H a 1336135 := seed 665225 rfl
lemma f151 : H a 0x9483481c8168158150547 := seed 666250 rfl
lemma f152 : H a 0xa486483482c8268258250245 := seed 1187843 rfl
lemma f153 : H a 2384463 := seed 1189017 rfl
lemma f154 : H a 2384471 := seed 1189033 rfl
lemma f155 : H a 2384487 := seed 1189065 rfl
lemma f156 : H a 2384711 := seed 1189513 rfl
lemma f157 : H a 0xa486482c8268258250347 := seed 1189514 rfl
lemma f158 : H a 0xa483482c8268258250647 := seed 1191050 rfl
lemma f159 : H a 2386503 := seed 1193097 rfl
lemma f160 : H a 0x6483482c8268258250a47 := seed 1193098 rfl
lemma f161 : H a 0xc486485484c8468458450445 := seed 2236419 rfl
lemma f162 : H a 4482247 := seed 2238857 rfl
lemma f163 : H a 0xc486485484684584504c7 := seed 2238858 rfl
lemma f164 : H a 0xc486484c8468458450547 := seed 2239114 rfl
lemma f165 : H a 0xc485484c8468458450647 := seed 2239626 rfl
lemma f166 : H a 0x6485484c8468458450c47 := seed 2242698 rfl
lemma f167 : H a 8677463 := seed 4337833 rfl
lemma f168 : H a 8677479 := seed 4337865 rfl
lemma f169 : H a 8677959 := seed 4338825 rfl
lemma f170 : H a 0x9885883881c81a8198190185 := seed 794627 rfl
lemma f171 : H a 0x9885881c81a8198190387 := seed 796426 rfl
lemma f172 : H a 1598855 := seed 797449 rfl
lemma f173 : H a 0xa886883882c82a8298290285 := seed 1318915 rfl
lemma f174 : H a 0xa886883882a82982902c7 := seed 1320330 rfl
lemma f175 : H a 0xa886882c82a8298290387 := seed 1320714 rfl
lemma f176 : H a 0x6883882c82a8298290a87 := seed 1324298 rfl
lemma f177 : H a 0xc886885884c84a8498490485 := seed 2367491 rfl
lemma f178 : H a 0xc886885884c84a849848f := seed 2369818 rfl
lemma f179 : H a 0xc886885884c84a8490497 := seed 2369834 rfl
lemma f180 : H a 4744359 := seed 2369865 rfl
lemma f181 : H a 0xc886885884c84984904a7 := seed 2369866 rfl
lemma f182 : H a 4744391 := seed 2369929 rfl
lemma f183 : H a 0xc886885884a84984904c7 := seed 2369930 rfl
lemma f184 : H a 4744583 := seed 2370313 rfl
lemma f185 : H a 0xc886884c84a8498490587 := seed 2370314 rfl
lemma f186 : H a 0xc885884c84a8498490687 := seed 2370826 rfl
lemma f187 : H a 4746375 := seed 2373897 rfl
lemma f188 : H a 0x6885884c84a8498490c87 := seed 2373898 rfl
lemma f189 : H a 0xc88a889888a88988908c7 := seed 4469130 rfl
lemma f190 : H a 8940167 := seed 4470025 rfl
lemma f191 : H a 8940679 := seed 4471049 rfl
lemma f192 : H a 0xa889888c88a8898890c87 := seed 4471050 rfl
lemma f193 : H a 0xb08708388348328318310305 := seed 1581059 rfl
lemma f194 : H a 0xb0870838834832831830f := seed 1582618 rfl
lemma f195 : H a 0xb08708388348328310317 := seed 1582634 rfl
lemma f196 : H a 3171111 := seed 1582665 rfl
lemma f197 : H a 3171143 := seed 1582729 rfl
lemma f198 : H a 0xb08708388328318310347 := seed 1582730 rfl
lemma f199 : H a 0xd08708588548528518510505 := seed 2629635 rfl
lemma f200 : H a 0xd0870858854852851850f := seed 2632218 rfl
lemma f201 : H a 0xd08708588528518510547 := seed 2632330 rfl
lemma f202 : H a 5268871 := seed 2632457 rfl
lemma f203 : H a 0x708588548528518510d07 := seed 2636298 rfl
lemma f204 : H a 0xd08b08988948928918910905 := seed 4726787 rfl
lemma f205 : H a 9464087 := seed 4731433 rfl
lemma f206 : H a 9464199 := seed 4731657 rfl
lemma f207 : H a 0xd08988948928918910b07 := seed 4732426 rfl
lemma f208 : H a 9465095 := seed 4733449 rfl
lemma f209 : H a 0xe08708688648628618610605 := seed 3153923 rfl
lemma f210 : H a 0xe08708688648628610617 := seed 3157034 rfl
lemma f211 : H a 0xe08708688648618610627 := seed 3157066 rfl
lemma f212 : H a 6317703 := seed 3157257 rfl
lemma f213 : H a 0xe08688648628618610707 := seed 3157514 rfl
lemma f214 : H a 10512935 := seed 5256265 rfl
lemma f215 : H a 10512967 := seed 5256329 rfl
lemma f216 : H a 0xe08b08a88a28a18a10a47 := seed 5256330 rfl
lemma f217 : H a 0xe08b08a48a28a18a10a87 := seed 5256458 rfl
lemma f218 : H a 10513159 := seed 5256713 rfl
lemma f219 : H a 10513927 := seed 5258249 rfl
lemma f220 : H a 0xe08d08c88c48c28c18c10c05 := seed 6299651 rfl
lemma f221 : H a 12610599 := seed 6305865 rfl
lemma f222 : H a 12610631 := seed 6305929 rfl
lemma f223 : H a 12610695 := seed 6306057 rfl
lemma f224 : H a 12610823 := seed 6306313 rfl
lemma f225 : H a 0xe08c88c48c28c18c10d07 := seed 6306314 rfl
lemma f226 : H a 12611079 := seed 6306825 rfl
lemma f227 : H a 237631 := seed 114809 rfl
lemma f228 : H a 0x83c43c23c13c0bc07c03f := seed 114810 rfl
lemma f229 : H a 0x85c45c25c15c0dc07c060059 := seed 180227 rfl
lemma f230 : H a 368735 := seed 180409 rfl
lemma f231 : H a 368763 := seed 180465 rfl
lemma f232 : H a 368859 := seed 180657 rfl
lemma f233 : H a 368987 := seed 180913 rfl
lemma f234 : H a 0x85c45c25c0dc07c06015b := seed 180914 rfl
lemma f235 : H a 369243 := seed 181425 rfl
lemma f236 : H a 370779 := seed 184497 rfl
lemma f237 : H a 0x89c49c29c19c0dc0bc0a0099 := seed 311299 rfl
lemma f238 : H a 630943 := seed 311609 rfl
lemma f239 : H a 630971 := seed 311665 rfl
lemma f240 : H a 0x89c49c29c19c0dc0a00bb := seed 311666 rfl
lemma f241 : H a 631195 := seed 312113 rfl
lemma f242 : H a 631451 := seed 312625 rfl
lemma f243 : H a 631963 := seed 313649 rfl
lemma f244 : H a 632987 := seed 315697 rfl
lemma f245 : H a 0x91c51c31c19c15c13c120119 := seed 573443 rfl
lemma f246 : H a 1155359 := seed 574009 rfl
lemma f247 : H a 0x91c51c31c19c15c13c11f := seed 574010 rfl
lemma f248 : H a 1155387 := seed 574065 rfl
lemma f249 : H a 1155419 := seed 574129 rfl
lemma f250 : H a 0x91c51c31c19c13c12015b := seed 574130 rfl
lemma f251 : H a 1155483 := seed 574257 rfl
lemma f252 : H a 0x91c51c31c15c13c12019b := seed 574258 rfl
lemma f253 : H a 1155867 := seed 575025 rfl
lemma f254 : H a 0x91c31c19c15c13c12051b := seed 576050 rfl
lemma f255 : H a 1157403 := seed 578097 rfl
lemma f256 : H a 0x51c31c19c15c13c12091b := seed 578098 rfl
lemma f257 : H a 0xa1c61c31c29c25c23c220219 := seed 1097731 rfl
lemma f258 : H a 2204191 := seed 1098809 rfl
lemma f259 : H a 2204219 := seed 1098865 rfl
lemma f260 : H a 2204251 := seed 1098929 rfl
lemma f261 : H a 2204315 := seed 1099057 rfl
lemma f262 : H a 2204443 := seed 1099313 rfl
lemma f263 : H a 2206235 := seed 1102897 rfl
lemma f264 : H a 0x61c31c29c25c23c220a1b := seed 1102898 rfl
lemma f265 : H a 0xc1c61c51c49c45c43c420419 := seed 2146307 rfl
lemma f266 : H a 4301855 := seed 2148409 rfl
lemma f267 : H a 4301883 := seed 2148465 rfl
lemma f268 : H a 4302107 := seed 2148913 rfl
lemma f269 : H a 4303899 := seed 2152497 rfl
lemma f270 : H a 0xc1ca1c91c89c85c83c820819 := seed 4243459 rfl
lemma f271 : H a 8497183 := seed 4247609 rfl
lemma f272 : H a 0xc1ca1c91c89c85c83c81f := seed 4247610 rfl
lemma f273 : H a 8497211 := seed 4247665 rfl
lemma f274 : H a 0xc1ca1c91c89c85c82083b := seed 4247666 rfl
lemma f275 : H a 8497243 := seed 4247729 rfl
lemma f276 : H a 0xc1ca1c91c89c83c82085b := seed 4247730 rfl
lemma f277 : H a 0xc1ca1c91c85c83c82089b := seed 4247858 rfl
lemma f278 : H a 8497435 := seed 4248113 rfl
lemma f279 : H a 8497691 := seed 4248625 rfl
lemma f280 : H a 0xc1c91c89c85c83c820a1b := seed 4248626 rfl
lemma f281 : H a 0xa1c91c89c85c83c820c1b := seed 4249650 rfl
lemma f282 : H a 0x86c46c26c16c0ec07c070069 := seed 212995 rfl
lemma f283 : H a 434287 := seed 213209 rfl
lemma f284 : H a 434299 := seed 213233 rfl
lemma f285 : H a 0x86c46c26c16c0ec07007b := seed 213234 rfl
lemma f286 : H a 434539 := seed 213713 rfl
lemma f287 : H a 0x86c46c26c0ec07c07016b := seed 213714 rfl
lemma f288 : H a 434795 := seed 214225 rfl
lemma f289 : H a 436331 := seed 217297 rfl
lemma f290 : H a 0x46c26c16c0ec07c07086b := seed 217298 rfl
lemma f291 : H a 0x8ac4ac2ac1ac0ec0bc0b00a9 := seed 344067 rfl
lemma f292 : H a 0x8ac4ac2ac1ac0ec0bc0af := seed 344410 rfl
lemma f293 : H a 696507 := seed 344433 rfl
lemma f294 : H a 696747 := seed 344913 rfl
lemma f295 : H a 697003 := seed 345425 rfl
lemma f296 : H a 697515 := seed 346449 rfl
lemma f297 : H a 0x8ac2ac1ac0ec0bc0b04ab := seed 346450 rfl
lemma f298 : H a 698539 := seed 348497 rfl
lemma f299 : H a 0x92c52c32c1ac16c13c130129 := seed 606211 rfl
lemma f300 : H a 1220911 := seed 606809 rfl
lemma f301 : H a 0x92c52c32c1ac16c13c12f := seed 606810 rfl
lemma f302 : H a 1220923 := seed 606833 rfl
lemma f303 : H a 1220971 := seed 606929 rfl
lemma f304 : H a 1221035 := seed 607057 rfl
lemma f305 : H a 1221419 := seed 607825 rfl
lemma f306 : H a 0x92c52c1ac16c13c13032b := seed 607826 rfl
lemma f307 : H a 1221931 := seed 608849 rfl
lemma f308 : H a 1222955 := seed 610897 rfl
lemma f309 : H a 0xa2c62c32c2ac26c23c230229 := seed 1130499 rfl
lemma f310 : H a 0xa2c62c32c2ac26c23c22f := seed 1131610 rfl
lemma f311 : H a 2269755 := seed 1131633 rfl
lemma f312 : H a 0xa2c62c32c2ac26c23023b := seed 1131634 rfl
lemma f313 : H a 2269995 := seed 1132113 rfl
lemma f314 : H a 2271787 := seed 1135697 rfl
lemma f315 : H a 4367531 := seed 2181457 rfl
lemma f316 : H a 0xc2c62c52c46c43c4304ab := seed 2181458 rfl
lemma f317 : H a 4367659 := seed 2181713 rfl
lemma f318 : H a 4369451 := seed 2185297 rfl
lemma f319 : H a 0xc2ca2c92c8ac86c83c830829 := seed 4276227 rfl
lemma f320 : H a 8562735 := seed 4280409 rfl
lemma f321 : H a 0xc2ca2c92c8ac86c83c82f := seed 4280410 rfl
lemma f322 : H a 8562747 := seed 4280433 rfl
lemma f323 : H a 8562795 := seed 4280529 rfl
lemma f324 : H a 0xc2ca2c92c8ac83c83086b := seed 4280530 rfl
lemma f325 : H a 8562859 := seed 4280657 rfl
lemma f326 : H a 0xc2ca2c92c86c83c8308ab := seed 4280658 rfl
lemma f327 : H a 8562987 := seed 4280913 rfl
lemma f328 : H a 0xc2ca2c8ac86c83c83092b := seed 4280914 rfl
lemma f329 : H a 8563243 := seed 4281425 rfl
lemma f330 : H a 0xc2c92c8ac86c83c830a2b := seed 4281426 rfl
lemma f331 : H a 8563755 := seed 4282449 rfl
lemma f332 : H a 0xa2c92c8ac86c83c830c2b := seed 4282450 rfl
lemma f333 : H a 0x8cc4cc2cc1cc0ec0dc0d00c9 := seed 409603 rfl
lemma f334 : H a 827627 := seed 410065 rfl
lemma f335 : H a 827851 := seed 410513 rfl
lemma f336 : H a 828107 := seed 411025 rfl
lemma f337 : H a 0x8cc4cc1cc0ec0dc0d02cb := seed 411026 rfl
lemma f338 : H a 828619 := seed 412049 rfl
lemma f339 : H a 0x8cc2cc1cc0ec0dc0d04cb := seed 412050 rfl
lemma f340 : H a 0x94c54c34c1cc16c15c150149 := seed 671747 rfl
lemma f341 : H a 1352043 := seed 672465 rfl
lemma f342 : H a 1352139 := seed 672657 rfl
lemma f343 : H a 1352523 := seed 673425 rfl
lemma f344 : H a 1353035 := seed 674449 rfl
lemma f345 : H a 1354059 := seed 676497 rfl
lemma f346 : H a 0x54c34c1cc16c15c15094b := seed 676498 rfl
lemma f347 : H a 2400847 := seed 1197209 rfl
lemma f348 : H a 2400875 := seed 1197265 rfl
lemma f349 : H a 2400971 := seed 1197457 rfl
lemma f350 : H a 0xa4c64c34c26c25c2502cb := seed 1197458 rfl
lemma f351 : H a 2401099 := seed 1197713 rfl
lemma f352 : H a 2402891 := seed 1201297 rfl
lemma f353 : H a 4498635 := seed 2247057 rfl
lemma f354 : H a 0xc4ca4c94c8cc86c85c850849 := seed 4341763 rfl
lemma f355 : H a 8693867 := seed 4346065 rfl
lemma f356 : H a 8694091 := seed 4346513 rfl
lemma f357 : H a 8694347 := seed 4347025 rfl
lemma f358 : H a 8694859 := seed 4348049 rfl
lemma f359 : H a 0x98c58c38c1cc1ac19c190189 := seed 802819 rfl
lemma f360 : H a 0x98c58c38c1cc1ac19c18f := seed 803610 rfl
lemma f361 : H a 1614251 := seed 803665 rfl
lemma f362 : H a 1614283 := seed 803729 rfl
lemma f363 : H a 1615243 := seed 805649 rfl
lemma f364 : H a 0x98c38c1cc1ac19c19058b := seed 805650 rfl
lemma f365 : H a 0x58c38c1cc1ac19c19098b := seed 807698 rfl
lemma f366 : H a 0xa8c68c38c2cc2ac29c290289 := seed 1327107 rfl
lemma f367 : H a 0xa8c68c38c2cc2ac29c28f := seed 1328410 rfl
lemma f368 : H a 0xa8c68c38c2cc2ac29029b := seed 1328434 rfl
lemma f369 : H a 2663083 := seed 1328465 rfl
lemma f370 : H a 0xa8c68c38c2ac29c2902cb := seed 1328530 rfl
lemma f371 : H a 2663307 := seed 1328913 rfl
lemma f372 : H a 2664075 := seed 1330449 rfl
lemma f373 : H a 0xa8c38c2cc2ac29c29068b := seed 1330450 rfl
lemma f374 : H a 0x68c38c2cc2ac29c290a8b := seed 1332498 rfl
lemma f375 : H a 0xc8c68c58c4cc4ac49c490489 := seed 2375683 rfl
lemma f376 : H a 4760719 := seed 2378009 rfl
lemma f377 : H a 0xc8c68c58c4cc4ac49c48f := seed 2378010 rfl
lemma f378 : H a 0xc8c68c58c4cc4ac49049b := seed 2378034 rfl
lemma f379 : H a 4760747 := seed 2378065 rfl
lemma f380 : H a 0xc8c68c58c4ac49c4904cb := seed 2378130 rfl
lemma f381 : H a 4760971 := seed 2378513 rfl
lemma f382 : H a 4761227 := seed 2379025 rfl
lemma f383 : H a 0xc8c58c4cc4ac49c49068b := seed 2379026 rfl
lemma f384 : H a 4762763 := seed 2382097 rfl
lemma f385 : H a 0xc8ca8c98c8cc8ac89c890889 := seed 4472835 rfl
lemma f386 : H a 0xc8ca8c98c8cc8ac89c88f := seed 4477210 rfl
lemma f387 : H a 8956059 := seed 4477233 rfl
lemma f388 : H a 8956075 := seed 4477265 rfl
lemma f389 : H a 0xc8ca8c98c8ac89c8908cb := seed 4477330 rfl
lemma f390 : H a 8956299 := seed 4477713 rfl
lemma f391 : H a 8956555 := seed 4478225 rfl
lemma f392 : H a 8957067 := seed 4479249 rfl
lemma f393 : H a 3187531 := seed 1590929 rfl
lemma f394 : H a 0xb0c70c38c32c31c31034b := seed 1590930 rfl
lemma f395 : H a 3187595 := seed 1591057 rfl
lemma f396 : H a 0xb0c70c34c32c31c31038b := seed 1591058 rfl
lemma f397 : H a 3188491 := seed 1592849 rfl
lemma f398 : H a 3189515 := seed 1594897 rfl
lemma f399 : H a 0x70c38c34c32c31c310b0b := seed 1594898 rfl
lemma f400 : H a 0xd0c70c58c54c52c51c510509 := seed 2637827 rfl
end BorsukCert

namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f401 : H a 0xd0c70c58c54c52c51c50f := seed 2640410 rfl
lemma f402 : H a 5285195 := seed 2640529 rfl
lemma f403 : H a 5285259 := seed 2640657 rfl
lemma f404 : H a 0x70c58c54c52c51c510d0b := seed 2644498 rfl
lemma f405 : H a 0xd0cb0c98c94c92c91c910909 := seed 4734979 rfl
lemma f406 : H a 9480463 := seed 4739609 rfl
lemma f407 : H a 9480491 := seed 4739665 rfl
lemma f408 : H a 9480523 := seed 4739729 rfl
lemma f409 : H a 0xd0cb0c98c92c91c91094b := seed 4739730 rfl
lemma f410 : H a 0xd0cb0c94c92c91c91098b := seed 4739858 rfl
lemma f411 : H a 9480971 := seed 4740625 rfl
lemma f412 : H a 0xb0c98c94c92c91c910d0b := seed 4741650 rfl
lemma f413 : H a 0xe0c70c68c64c62c61c610609 := seed 3162115 rfl
lemma f414 : H a 6333995 := seed 3165265 rfl
lemma f415 : H a 6334091 := seed 3165457 rfl
lemma f416 : H a 6334219 := seed 3165713 rfl
lemma f417 : H a 0xe0c68c64c62c61c61070b := seed 3165714 rfl
lemma f418 : H a 0x70c68c64c62c61c610e0b := seed 3169298 rfl
lemma f419 : H a 0xe0cb0ca8ca4ca2ca1ca10a09 := seed 5259267 rfl
lemma f420 : H a 0xe0cb0ca8ca4ca2ca1ca0f := seed 5264410 rfl
lemma f421 : H a 10529323 := seed 5264465 rfl
lemma f422 : H a 10529355 := seed 5264529 rfl
lemma f423 : H a 0xe0cb0ca8ca2ca1ca10a4b := seed 5264530 rfl
lemma f424 : H a 10529419 := seed 5264657 rfl
lemma f425 : H a 10529547 := seed 5264913 rfl
lemma f426 : H a 0xe0ca8ca4ca2ca1ca10b0b := seed 5264914 rfl
lemma f427 : H a 0xb0ca8ca4ca2ca1ca10e0b := seed 5266450 rfl
lemma f428 : H a 0xe0cd0cc8cc4cc2cc1cc10c09 := seed 6307843 rfl
lemma f429 : H a 0xe0cd0cc8cc4cc2cc1cc0f := seed 6314010 rfl
lemma f430 : H a 12626971 := seed 6314033 rfl
lemma f431 : H a 12626987 := seed 6314065 rfl
lemma f432 : H a 12627019 := seed 6314129 rfl
lemma f433 : H a 0xe0cd0cc8cc2cc1cc10c4b := seed 6314130 rfl
lemma f434 : H a 12627083 := seed 6314257 rfl
lemma f435 : H a 12627211 := seed 6314513 rfl
lemma f436 : H a 0x8744742741740f407c078071 := seed 229379 rfl
lemma f437 : H a 467063 := seed 229609 rfl
lemma f438 : H a 0x87447427417407c0780f3 := seed 229858 rfl
lemma f439 : H a 467315 := seed 230113 rfl
lemma f440 : H a 0x8744742740f407c078173 := seed 230114 rfl
lemma f441 : H a 467571 := seed 230625 rfl
lemma f442 : H a 0x8744741740f407c078273 := seed 230626 rfl
lemma f443 : H a 469107 := seed 233697 rfl
lemma f444 : H a 0x8b44b42b41b40f40bc0b80b1 := seed 360451 rfl
lemma f445 : H a 0x8b44b42b41b40bc0b80f3 := seed 360930 rfl
lemma f446 : H a 0x8b44b42b40f40bc0b81b3 := seed 361314 rfl
lemma f447 : H a 730291 := seed 362849 rfl
lemma f448 : H a 731315 := seed 364897 rfl
lemma f449 : H a 0x9345343341b417413c138131 := seed 622595 rfl
lemma f450 : H a 1253687 := seed 623209 rfl
lemma f451 : H a 1253691 := seed 623217 rfl
lemma f452 : H a 0x9345343341b417413813b := seed 623218 rfl
lemma f453 : H a 1253747 := seed 623329 rfl
lemma f454 : H a 1253811 := seed 623457 rfl
lemma f455 : H a 1254195 := seed 624225 rfl
lemma f456 : H a 0x5343341b417413c138933 := seed 627298 rfl
lemma f457 : H a 2302519 := seed 1148009 rfl
lemma f458 : H a 2302523 := seed 1148017 rfl
lemma f459 : H a 2302579 := seed 1148129 rfl
lemma f460 : H a 2302771 := seed 1148513 rfl
lemma f461 : H a 2304563 := seed 1152097 rfl
lemma f462 : H a 0xc346345344b447443c438431 := seed 2195459 rfl
lemma f463 : H a 4400187 := seed 2197617 rfl
lemma f464 : H a 4400307 := seed 2197857 rfl
lemma f465 : H a 0xc3463453447443c4384b3 := seed 2197858 rfl
lemma f466 : H a 4402227 := seed 2201697 rfl
lemma f467 : H a 0xc34a349348b487483c838831 := seed 4292611 rfl
lemma f468 : H a 8595511 := seed 4296809 rfl
lemma f469 : H a 8595515 := seed 4296817 rfl
lemma f470 : H a 8595571 := seed 4296929 rfl
lemma f471 : H a 0xc34a349348b483c838873 := seed 4296930 rfl
lemma f472 : H a 8595635 := seed 4297057 rfl
lemma f473 : H a 0xc34a348b487483c838933 := seed 4297314 rfl
lemma f474 : H a 0xc349348b487483c838a33 := seed 4297826 rfl
lemma f475 : H a 8596531 := seed 4298849 rfl
lemma f476 : H a 860375 := seed 426409 rfl
lemma f477 : H a 860627 := seed 426913 rfl
lemma f478 : H a 861395 := seed 428449 rfl
lemma f479 : H a 0x9545543541d417415c158151 := seed 688131 rfl
lemma f480 : H a 0x9545543541d415c158173 := seed 688866 rfl
lemma f481 : H a 1385299 := seed 689825 rfl
lemma f482 : H a 0x9545541d417415c158353 := seed 689826 rfl
lemma f483 : H a 1385811 := seed 690849 rfl
lemma f484 : H a 0xa546543542d427425c258251 := seed 1212419 rfl
lemma f485 : H a 2433875 := seed 1214113 rfl
lemma f486 : H a 0xa546542d427425c258353 := seed 1214114 rfl
lemma f487 : H a 2435667 := seed 1217697 rfl
lemma f488 : H a 0x6543542d427425c258a53 := seed 1217698 rfl
lemma f489 : H a 0xc546545544d447445c458451 := seed 2260995 rfl
lemma f490 : H a 0x6545544d447445c458c53 := seed 2267298 rfl
lemma f491 : H a 0xc54a549548d487485c858851 := seed 4358147 rfl
lemma f492 : H a 8726615 := seed 4362409 rfl
lemma f493 : H a 8726643 := seed 4362465 rfl
lemma f494 : H a 8726867 := seed 4362913 rfl
lemma f495 : H a 8727123 := seed 4363425 rfl
lemma f496 : H a 0x9945943941d41b419c198191 := seed 819203 rfl
lemma f497 : H a 1646999 := seed 820009 rfl
lemma f498 : H a 1647059 := seed 820129 rfl
lemma f499 : H a 1647507 := seed 821025 rfl
lemma f500 : H a 0x9943941d41b419c198593 := seed 822050 rfl
lemma f501 : H a 0x5943941d41b419c198993 := seed 824098 rfl
lemma f502 : H a 0xc946945944d44b449c498491 := seed 2392067 rfl
lemma f503 : H a 4793495 := seed 2394409 rfl
lemma f504 : H a 4793523 := seed 2394465 rfl
lemma f505 : H a 0xc946945944b449c4984d3 := seed 2394530 rfl
lemma f506 : H a 4793747 := seed 2394913 rfl
lemma f507 : H a 0xc946944d44b449c498593 := seed 2394914 rfl
lemma f508 : H a 4795539 := seed 2398497 rfl
lemma f509 : H a 0x6945944d44b449c498c93 := seed 2398498 rfl
lemma f510 : H a 0xc94a949948d48b489c898891 := seed 4489219 rfl
lemma f511 : H a 0xc94a949948d48b489889b := seed 4493618 rfl
lemma f512 : H a 0xc949948d48b489c898a93 := seed 4494626 rfl
lemma f513 : H a 8989843 := seed 4495649 rfl
lemma f514 : H a 0xa949948d48b489c898c93 := seed 4495650 rfl
lemma f515 : H a 0xb1471439435433431c318311 := seed 1605635 rfl
lemma f516 : H a 3220371 := seed 1607457 rfl
lemma f517 : H a 0x71439435433431c318b13 := seed 1611298 rfl
lemma f518 : H a 0xd1471459455453451c518511 := seed 2654211 rfl
lemma f519 : H a 5317971 := seed 2656929 rfl
lemma f520 : H a 0xd1471459453451c518553 := seed 2656930 rfl
lemma f521 : H a 0x71459455453451c518d13 := seed 2660898 rfl
lemma f522 : H a 0xd14b1499495493491c918911 := seed 4751363 rfl
lemma f523 : H a 9513239 := seed 4756009 rfl
lemma f524 : H a 9513267 := seed 4756065 rfl
lemma f525 : H a 9514259 := seed 4758049 rfl
lemma f526 : H a 0xe14b14a94a54a34a1ca18a11 := seed 5275651 rfl
lemma f527 : H a 10562071 := seed 5280809 rfl
lemma f528 : H a 10562099 := seed 5280865 rfl
lemma f529 : H a 10562131 := seed 5280929 rfl
lemma f530 : H a 10562323 := seed 5281313 rfl
lemma f531 : H a 0xe14d14c94c54c34c1cc18c11 := seed 6324227 rfl
lemma f532 : H a 0xe14d14c94c34c1cc18c53 := seed 6330530 rfl
lemma f533 : H a 12659859 := seed 6330657 rfl
lemma f534 : H a 12659987 := seed 6330913 rfl
lemma f535 : H a 12660243 := seed 6331425 rfl
lemma f536 : H a 0x8e44e42e41e40f40e80eb := seed 459218 rfl
lemma f537 : H a 926179 := seed 459713 rfl
lemma f538 : H a 926435 := seed 460225 rfl
lemma f539 : H a 926947 := seed 461249 rfl
lemma f540 : H a 0x9645643641e417416c168161 := seed 720899 rfl
lemma f541 : H a 0x9645643641e417416816b := seed 721618 rfl
lemma f542 : H a 1450355 := seed 721633 rfl
lemma f543 : H a 0x9645643641e416c168173 := seed 721634 rfl
lemma f544 : H a 1450467 := seed 721857 rfl
lemma f545 : H a 0x96456436417416c1681e3 := seed 721858 rfl
lemma f546 : H a 1450851 := seed 722625 rfl
lemma f547 : H a 0x9645641e417416c168363 := seed 722626 rfl
lemma f548 : H a 0x9643641e417416c168563 := seed 723650 rfl
lemma f549 : H a 1452387 := seed 725697 rfl
lemma f550 : H a 0x5643641e417416c168963 := seed 725698 rfl
lemma f551 : H a 0xa646643642e427426c268261 := seed 1245187 rfl
lemma f552 : H a 0xa646643642e427426c267 := seed 1246410 rfl
lemma f553 : H a 2499299 := seed 1246657 rfl
lemma f554 : H a 2499427 := seed 1246913 rfl
lemma f555 : H a 0xa646642e427426c268363 := seed 1246914 rfl
lemma f556 : H a 0xa643642e427426c268663 := seed 1248450 rfl
lemma f557 : H a 2501219 := seed 1250497 rfl
lemma f558 : H a 0xc646645644e447446c468461 := seed 2293763 rfl
lemma f559 : H a 4596963 := seed 2296257 rfl
lemma f560 : H a 0xc646644e447446c468563 := seed 2296514 rfl
lemma f561 : H a 4598883 := seed 2300097 rfl
lemma f562 : H a 0xc64a649648e487486c868861 := seed 4390915 rfl
lemma f563 : H a 8792171 := seed 4395217 rfl
lemma f564 : H a 0xc64a649648e487486886b := seed 4395218 rfl
lemma f565 : H a 0xc64a649648e486c868873 := seed 4395234 rfl
lemma f566 : H a 8792419 := seed 4395713 rfl
lemma f567 : H a 0xc64a648e487486c868963 := seed 4395714 rfl
lemma f568 : H a 8792675 := seed 4396225 rfl
lemma f569 : H a 0xc649648e487486c868a63 := seed 4396226 rfl
lemma f570 : H a 8793187 := seed 4397249 rfl
lemma f571 : H a 0x9a45a43a41e41b41ac1a81a1 := seed 851971 rfl
lemma f572 : H a 1712555 := seed 852817 rfl
lemma f573 : H a 1712611 := seed 852929 rfl
lemma f574 : H a 1713059 := seed 853825 rfl
lemma f575 : H a 0x9a45a41e41b41ac1a83a3 := seed 853826 rfl
lemma f576 : H a 0x5a43a41e41b41ac1a89a3 := seed 856898 rfl
lemma f577 : H a 0xaa46a43a42e42b42ac2a82a1 := seed 1376259 rfl
lemma f578 : H a 2761635 := seed 1378113 rfl
lemma f579 : H a 0xca46a45a44e44b44ac4a84a1 := seed 2424835 rfl
lemma f580 : H a 4859047 := seed 2427209 rfl
lemma f581 : H a 0xca46a45a44e44b44ac4a7 := seed 2427210 rfl
lemma f582 : H a 0xca46a45a44e44b44a84ab := seed 2427218 rfl
lemma f583 : H a 0xca46a45a44e44ac4a84b3 := seed 2427234 rfl
lemma f584 : H a 4859107 := seed 2427329 rfl
lemma f585 : H a 0xca46a45a44b44ac4a84e3 := seed 2427330 rfl
lemma f586 : H a 4859299 := seed 2427713 rfl
lemma f587 : H a 0xca46a44e44b44ac4a85a3 := seed 2427714 rfl
lemma f588 : H a 4859555 := seed 2428225 rfl
lemma f589 : H a 0xca45a44e44b44ac4a86a3 := seed 2428226 rfl
lemma f590 : H a 4861091 := seed 2431297 rfl
lemma f591 : H a 0x6a45a44e44b44ac4a8ca3 := seed 2431298 rfl
lemma f592 : H a 0xca4aa49a48e48b48ac8a88a1 := seed 4521987 rfl
lemma f593 : H a 0xca4aa49a48e48b48ac8a7 := seed 4526410 rfl
lemma f594 : H a 9054379 := seed 4526417 rfl
lemma f595 : H a 0xca4aa49a48b48ac8a88e3 := seed 4526530 rfl
lemma f596 : H a 9055395 := seed 4528449 rfl
lemma f597 : H a 0xaa49a48e48b48ac8a8ca3 := seed 4528450 rfl
lemma f598 : H a 0xb247243a436433432c328321 := seed 1638403 rfl
lemma f599 : H a 3285799 := seed 1640009 rfl
lemma f600 : H a 3285859 := seed 1640129 rfl
lemma f601 : H a 0xb247243a433432c328363 := seed 1640130 rfl
lemma f602 : H a 0xb2472436433432c3283a3 := seed 1640258 rfl
lemma f603 : H a 0xb243a436433432c328723 := seed 1642050 rfl
lemma f604 : H a 3287843 := seed 1644097 rfl
lemma f605 : H a 0x7243a436433432c328b23 := seed 1644098 rfl
lemma f606 : H a 0xd247245a456453452c528521 := seed 2686979 rfl
lemma f607 : H a 5383463 := seed 2689609 rfl
lemma f608 : H a 5383523 := seed 2689729 rfl
lemma f609 : H a 0xd247245a453452c528563 := seed 2689730 rfl
lemma f610 : H a 0xd2472456453452c5285a3 := seed 2689858 rfl
lemma f611 : H a 5383971 := seed 2690625 rfl
lemma f612 : H a 0xd245a456453452c528723 := seed 2690626 rfl
lemma f613 : H a 5385507 := seed 2693697 rfl
lemma f614 : H a 0x7245a456453452c528d23 := seed 2693698 rfl
lemma f615 : H a 0xd24b249a496493492c928921 := seed 4784131 rfl
lemma f616 : H a 0xd24b249a496493492c927 := seed 4788810 rfl
lemma f617 : H a 9578795 := seed 4788817 rfl
lemma f618 : H a 9578851 := seed 4788929 rfl
lemma f619 : H a 0xd24b249a493492c928963 := seed 4788930 rfl
lemma f620 : H a 0xd24b2496493492c9289a3 := seed 4789058 rfl
lemma f621 : H a 9579299 := seed 4789825 rfl
lemma f622 : H a 0xd249a496493492c928b23 := seed 4789826 rfl
lemma f623 : H a 0xb249a496493492c928d23 := seed 4790850 rfl
lemma f624 : H a 0xe247246a466463462c628621 := seed 3211267 rfl
lemma f625 : H a 0xe2472466463462c6286a3 := seed 3214658 rfl
lemma f626 : H a 6432547 := seed 3214913 rfl
lemma f627 : H a 0xe246a466463462c628723 := seed 3214914 rfl
lemma f628 : H a 0xe24b24aa4a64a34a2ca28a21 := seed 5308419 rfl
lemma f629 : H a 10627627 := seed 5313617 rfl
lemma f630 : H a 0xe24b24aa4a64a2ca28a33 := seed 5313634 rfl
lemma f631 : H a 10627683 := seed 5313729 rfl
lemma f632 : H a 0xe24b24aa4a34a2ca28a63 := seed 5313730 rfl
lemma f633 : H a 10627747 := seed 5313857 rfl
lemma f634 : H a 0xe24b24a64a34a2ca28aa3 := seed 5313858 rfl
lemma f635 : H a 0xe24aa4a64a34a2ca28b23 := seed 5314114 rfl
lemma f636 : H a 10628643 := seed 5315649 rfl
lemma f637 : H a 0xb24aa4a64a34a2ca28e23 := seed 5315650 rfl
lemma f638 : H a 0xe24d24ca4c64c34c2cc28c21 := seed 6356995 rfl
lemma f639 : H a 12725291 := seed 6363217 rfl
lemma f640 : H a 0xe24d24ca4c64c34c28c2b := seed 6363218 rfl
lemma f641 : H a 12725347 := seed 6363329 rfl
lemma f642 : H a 0xe24d24ca4c34c2cc28c63 := seed 6363330 rfl
lemma f643 : H a 12725411 := seed 6363457 rfl
lemma f644 : H a 0xe24d24c64c34c2cc28ca3 := seed 6363458 rfl
lemma f645 : H a 0xe24ca4c64c34c2cc28d23 := seed 6363714 rfl
lemma f646 : H a 12725795 := seed 6364225 rfl
lemma f647 : H a 0xd24ca4c64c34c2cc28e23 := seed 6364226 rfl
lemma f648 : H a 0x9c45c43c41e41d41cc1c81c1 := seed 917507 rfl
lemma f649 : H a 0x9c45c43c41e41d41cc1c7 := seed 918410 rfl
lemma f650 : H a 0x9c45c43c41e41d41c81cb := seed 918418 rfl
lemma f651 : H a 0x9c45c43c41e41cc1c81d3 := seed 918434 rfl
lemma f652 : H a 0x9c45c43c41d41cc1c81e3 := seed 918466 rfl
lemma f653 : H a 0xac46c43c42e42d42cc2c82c1 := seed 1441795 rfl
lemma f654 : H a 2892487 := seed 1443209 rfl
lemma f655 : H a 0xac46c43c42e42d42c82cb := seed 1443218 rfl
lemma f656 : H a 2892499 := seed 1443233 rfl
lemma f657 : H a 2892515 := seed 1443265 rfl
lemma f658 : H a 0xac46c43c42d42cc2c82e3 := seed 1443266 rfl
lemma f659 : H a 0xcc46c45c44e44d44cc4c84c1 := seed 2490371 rfl
lemma f660 : H a 4990151 := seed 2492809 rfl
lemma f661 : H a 0xcc46c45c44e44d44cc4c7 := seed 2492810 rfl
lemma f662 : H a 4990155 := seed 2492817 rfl
lemma f663 : H a 0xcc46c45c44e44d44c84cb := seed 2492818 rfl
lemma f664 : H a 0xcc46c45c44e44cc4c84d3 := seed 2492834 rfl
lemma f665 : H a 4990179 := seed 2492865 rfl
lemma f666 : H a 0xcc46c45c44d44cc4c84e3 := seed 2492866 rfl
lemma f667 : H a 0xcc4ac49c48e48d48cc8c88c1 := seed 4587523 rfl
lemma f668 : H a 0xcc4ac49c48e48d48cc8c7 := seed 4592010 rfl
lemma f669 : H a 0xb447443c436435434c348341 := seed 1703939 rfl
lemma f670 : H a 3416903 := seed 1705609 rfl
lemma f671 : H a 0xb447443c436435434c347 := seed 1705610 rfl
lemma f672 : H a 3416907 := seed 1705617 rfl
lemma f673 : H a 0xb447443c436435434834b := seed 1705618 rfl
lemma f674 : H a 3416915 := seed 1705633 rfl
lemma f675 : H a 0xb447443c436434c348353 := seed 1705634 rfl
lemma f676 : H a 3416931 := seed 1705665 rfl
lemma f677 : H a 0xb447443c435434c348363 := seed 1705666 rfl
lemma f678 : H a 0xd447445c456455454c548541 := seed 2752515 rfl
lemma f679 : H a 5514567 := seed 2755209 rfl
lemma f680 : H a 0xd447445c456455454c547 := seed 2755210 rfl
lemma f681 : H a 5514571 := seed 2755217 rfl
lemma f682 : H a 0xd447445c456455454854b := seed 2755218 rfl
lemma f683 : H a 5514579 := seed 2755233 rfl
lemma f684 : H a 0xd447445c456454c548553 := seed 2755234 rfl
lemma f685 : H a 5514595 := seed 2755265 rfl
lemma f686 : H a 0xd44b449c496495494c948941 := seed 4849667 rfl
lemma f687 : H a 9709895 := seed 4854409 rfl
lemma f688 : H a 0xd44b449c496495494c947 := seed 4854410 rfl
lemma f689 : H a 0xd44b449c496495494894b := seed 4854418 rfl
lemma f690 : H a 9709907 := seed 4854433 rfl
lemma f691 : H a 0xd44b449c496494c948953 := seed 4854434 rfl
lemma f692 : H a 9709923 := seed 4854465 rfl
lemma f693 : H a 0xd44b449c495494c948963 := seed 4854466 rfl
lemma f694 : H a 6563399 := seed 3280009 rfl
lemma f695 : H a 6563411 := seed 3280033 rfl
lemma f696 : H a 6563427 := seed 3280065 rfl
lemma f697 : H a 0xe44b44ac4a64a54a4ca48a41 := seed 5373955 rfl
lemma f698 : H a 10758727 := seed 5379209 rfl
lemma f699 : H a 0xe44b44ac4a64a54a4ca47 := seed 5379210 rfl
lemma f700 : H a 10758731 := seed 5379217 rfl
lemma f701 : H a 0xe44b44ac4a64a54a48a4b := seed 5379218 rfl
lemma f702 : H a 10758739 := seed 5379233 rfl
lemma f703 : H a 0xe44b44ac4a64a4ca48a53 := seed 5379234 rfl
lemma f704 : H a 10758755 := seed 5379265 rfl
lemma f705 : H a 0xe44b44ac4a54a4ca48a63 := seed 5379266 rfl
lemma f706 : H a 0xe44d44cc4c64c54c4cc48c41 := seed 6422531 rfl
lemma f707 : H a 12856391 := seed 6428809 rfl
lemma f708 : H a 0xe44d44cc4c64c54c4cc47 := seed 6428810 rfl
lemma f709 : H a 0xe44d44cc4c64c4cc48c53 := seed 6428834 rfl
lemma f710 : H a 12856419 := seed 6428865 rfl
lemma f711 : H a 0xb847843c43a439438c388381 := seed 1835011 rfl
lemma f712 : H a 3679111 := seed 1836809 rfl
lemma f713 : H a 3679115 := seed 1836817 rfl
lemma f714 : H a 3679123 := seed 1836833 rfl
lemma f715 : H a 3679139 := seed 1836865 rfl
lemma f716 : H a 0xb847843c439438c3883a3 := seed 1836866 rfl
lemma f717 : H a 0xd847845c45a459458c588581 := seed 2883587 rfl
lemma f718 : H a 5776775 := seed 2886409 rfl
lemma f719 : H a 0xd847845c45a459458c587 := seed 2886410 rfl
lemma f720 : H a 5776779 := seed 2886417 rfl
lemma f721 : H a 0xd847845c45a459458858b := seed 2886418 rfl
lemma f722 : H a 5776787 := seed 2886433 rfl
lemma f723 : H a 0xd847845c45a458c588593 := seed 2886434 rfl
lemma f724 : H a 5776803 := seed 2886465 rfl
lemma f725 : H a 0xd847845c459458c5885a3 := seed 2886466 rfl
lemma f726 : H a 0xd84b849c49a499498c988981 := seed 4980739 rfl
lemma f727 : H a 0xd84b849c49a499498c987 := seed 4985610 rfl
lemma f728 : H a 9972131 := seed 4985665 rfl
lemma f729 : H a 0xd84b849c499498c9889a3 := seed 4985666 rfl
lemma f730 : H a 0xe847846c46a469468c688681 := seed 3407875 rfl
lemma f731 : H a 6825607 := seed 3411209 rfl
lemma f732 : H a 0xe847846c46a469468c687 := seed 3411210 rfl
lemma f733 : H a 6825611 := seed 3411217 rfl
lemma f734 : H a 0xe847846c46a469468868b := seed 3411218 rfl
lemma f735 : H a 0xe847846c46a468c688693 := seed 3411234 rfl
lemma f736 : H a 6825635 := seed 3411265 rfl
lemma f737 : H a 0xe847846c469468c6886a3 := seed 3411266 rfl
lemma f738 : H a 0xe84b84ac4aa4a94a8ca88a81 := seed 5505027 rfl
lemma f739 : H a 11020939 := seed 5510417 rfl
lemma f740 : H a 0xe84b84ac4aa4a94a88a8b := seed 5510418 rfl
lemma f741 : H a 11020947 := seed 5510433 rfl
lemma f742 : H a 11020963 := seed 5510465 rfl
lemma f743 : H a 0xe84d84cc4ca4c94c8cc88c81 := seed 6553603 rfl
lemma f744 : H a 13118599 := seed 6560009 rfl
lemma f745 : H a 0xe84d84cc4ca4c94c8cc87 := seed 6560010 rfl
lemma f746 : H a 13118603 := seed 6560017 rfl
lemma f747 : H a 0xe84d84cc4ca4c94c88c8b := seed 6560018 rfl
lemma f748 : H a 13118611 := seed 6560033 rfl
lemma f749 : H a 0xe84d84cc4ca4c8cc88c93 := seed 6560034 rfl
lemma f750 : H a 13118627 := seed 6560065 rfl
lemma f751 : H a 0xe84d84cc4c94c8cc88ca3 := seed 6560066 rfl
lemma f752 : H a 0xf0478474472471470c708701 := seed 3670019 rfl
lemma f753 : H a 7350023 := seed 3673609 rfl
lemma f754 : H a 7350035 := seed 3673633 rfl
lemma f755 : H a 7350051 := seed 3673665 rfl
lemma f756 : H a 0xf0478474471470c708723 := seed 3673666 rfl
lemma f757 : H a 0xf04b84b44b24b14b0cb08b01 := seed 5767171 rfl
lemma f758 : H a 11545351 := seed 5772809 rfl
lemma f759 : H a 0xf04b84b44b24b14b0cb07 := seed 5772810 rfl
lemma f760 : H a 11545355 := seed 5772817 rfl
lemma f761 : H a 0xf04b84b44b24b14b08b0b := seed 5772818 rfl
lemma f762 : H a 0xf04b84b44b24b0cb08b13 := seed 5772834 rfl
lemma f763 : H a 11545379 := seed 5772865 rfl
lemma f764 : H a 0xf04d84d44d24d14d0cd08d01 := seed 6815747 rfl
lemma f765 : H a 0xf04d84d44d24d14d0cd07 := seed 6822410 rfl
lemma f766 : H a 13643019 := seed 6822417 rfl
lemma f767 : H a 0xf04d84d44d24d14d08d0b := seed 6822418 rfl
lemma f768 : H a 0xf04d84d44d24d0cd08d13 := seed 6822434 rfl
lemma f769 : H a 13643043 := seed 6822465 rfl
lemma f770 : H a 0xf04d84d44d14d0cd08d23 := seed 6822466 rfl
lemma f771 : H a 0xf04e84e44e24e14e0ce08e01 := seed 7340035 rfl
lemma f772 : H a 14691847 := seed 7347209 rfl
lemma f773 : H a 14691851 := seed 7347217 rfl
lemma f774 : H a 0xf04e84e44e24e14e08e0b := seed 7347218 rfl
lemma f775 : H a 14691859 := seed 7347233 rfl
lemma f776 : H a 0xf04e84e44e24e0ce08e13 := seed 7347234 rfl
lemma f777 : H a 14691875 := seed 7347265 rfl
lemma f778 : H a 0xf04e84e44e14e0ce08e23 := seed 7347266 rfl
lemma f779 : H a 60164939839 := seed 917628 rfl
lemma f780 : H a 60148158527 := seed 917629 rfl
lemma f781 : H a 55871021119 := seed 1441916 rfl
lemma f782 : H a 55854239807 := seed 1441917 rfl
lemma f783 : H a 47283183679 := seed 2490492 rfl
lemma f784 : H a 47266402367 := seed 2490493 rfl
lemma f785 : H a 30107508799 := seed 4587644 rfl
lemma f786 : H a 30090727487 := seed 4587645 rfl
lemma f787 : H a 53724061759 := seed 1704060 rfl
lemma f788 : H a 53707280447 := seed 1704061 rfl
lemma f789 : H a 45136224319 := seed 2752636 rfl
lemma f790 : H a 45119443007 := seed 2752637 rfl
lemma f791 : H a 27960549439 := seed 4849788 rfl
lemma f792 : H a 27943768127 := seed 4849789 rfl
lemma f793 : H a 40842305599 := seed 3276924 rfl
lemma f794 : H a 40825524287 := seed 3276925 rfl
lemma f795 : H a 23666630719 := seed 5374076 rfl
lemma f796 : H a 23649849407 := seed 5374077 rfl
lemma f797 : H a 15078793279 := seed 6422652 rfl
lemma f798 : H a 15062011967 := seed 6422653 rfl
lemma f799 : H a 83712169222207 := seed 3758489726 rfl
lemma f800 : H a 83643432964159 := seed 3758489727 rfl
end BorsukCert

namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f801 : H a 0x8c22c21c203f := seed 5905973374 rfl
lemma f802 : H a 0x8c12c11c103f := seed 5905973375 rfl
lemma f803 : H a 0x8c24c21c203f := seed 6979715198 rfl
lemma f804 : H a 0x8c24c22c203f := seed 7516586110 rfl
lemma f805 : H a 92510409728063 := seed 3490316414 rfl
lemma f806 : H a 92441673470015 := seed 3490316415 rfl
lemma f807 : H a 0x9423421c203f := seed 5637800062 rfl
lemma f808 : H a 0x9413411c103f := seed 5637800063 rfl
lemma f809 : H a 0x9425421c203f := seed 6711541886 rfl
lemma f810 : H a 0x9415411c103f := seed 6711541887 rfl
lemma f811 : H a 0x94254234203f := seed 7516848254 rfl
lemma f812 : H a 0x94154134103f := seed 7516848255 rfl
lemma f813 : H a 0x6423422c203f := seed 2953969790 rfl
lemma f814 : H a 0xa423422c203f := seed 5101453438 rfl
lemma f815 : H a 0xa413412c103f := seed 5101453439 rfl
lemma f816 : H a 0xa426422c203f := seed 6712066174 rfl
lemma f817 : H a 0xa416412c103f := seed 6712066175 rfl
lemma f818 : H a 0xa4264234203f := seed 6980501630 rfl
lemma f819 : H a 0xa4164134103f := seed 6980501631 rfl
lemma f820 : H a 0x6425424c203f := seed 1881276542 rfl
lemma f821 : H a 0x6415414c103f := seed 1881276543 rfl
lemma f822 : H a 0xc425424c203f := seed 5102502014 rfl
lemma f823 : H a 0xc415414c103f := seed 5102502015 rfl
lemma f824 : H a 0xc426424c203f := seed 5639372926 rfl
lemma f825 : H a 0xc416414c103f := seed 5639372927 rfl
lemma f826 : H a 0xc4264254203f := seed 5907808382 rfl
lemma f827 : H a 0xc4164154103f := seed 5907808383 rfl
lemma f828 : H a 0xa429428c203f := seed 1883373694 rfl
lemma f829 : H a 0xa419418c103f := seed 1883373695 rfl
lemma f830 : H a 0xc429428c203f := seed 2957115518 rfl
lemma f831 : H a 0xc419418c103f := seed 2957115519 rfl
lemma f832 : H a 0xc42a428c203f := seed 3493986430 rfl
lemma f833 : H a 0xc42a4294203f := seed 3762421886 rfl
lemma f834 : H a 0xc41a4194103f := seed 3762421887 rfl
lemma f835 : H a 0x9813811c103f := seed 5503713407 rfl
lemma f836 : H a 0x9825821c203f := seed 6577455230 rfl
lemma f837 : H a 0x9815811c103f := seed 6577455231 rfl
lemma f838 : H a 0x98258238203f := seed 7516979326 rfl
lemma f839 : H a 0x98158138103f := seed 7516979327 rfl
lemma f840 : H a 0x6823822c203f := seed 2819883134 rfl
lemma f841 : H a 0xa823822c203f := seed 4967366782 rfl
lemma f842 : H a 0x6825824c203f := seed 1747189886 rfl
lemma f843 : H a 0x6815814c103f := seed 1747189887 rfl
lemma f844 : H a 0xc825824c203f := seed 4968415358 rfl
lemma f845 : H a 0xc815814c103f := seed 4968415359 rfl
lemma f846 : H a 0xc826824c203f := seed 5505286270 rfl
lemma f847 : H a 0xc816814c103f := seed 5505286271 rfl
lemma f848 : H a 0xc8268258203f := seed 5907939454 rfl
lemma f849 : H a 0xc8168158103f := seed 5907939455 rfl
lemma f850 : H a 0xa829828c203f := seed 1749287038 rfl
lemma f851 : H a 0xa819818c103f := seed 1749287039 rfl
lemma f852 : H a 0xc819818c103f := seed 2823028863 rfl
lemma f853 : H a 0xc82a828c203f := seed 3359899774 rfl
lemma f854 : H a 0xc81a8198103f := seed 3762552959 rfl
lemma f855 : H a 0x70238234203f := seed 2551709822 rfl
lemma f856 : H a 0x70138134103f := seed 2551709823 rfl
lemma f857 : H a 0xb0238234203f := seed 4699193470 rfl
lemma f858 : H a 0xb0138134103f := seed 4699193471 rfl
lemma f859 : H a 0xb0270234203f := seed 6578241662 rfl
lemma f860 : H a 0xb0170134103f := seed 6578241663 rfl
lemma f861 : H a 0xb0270238203f := seed 6712459390 rfl
lemma f862 : H a 0xb0170138103f := seed 6712459391 rfl
lemma f863 : H a 0x70258254203f := seed 1479016574 rfl
lemma f864 : H a 0x70158154103f := seed 1479016575 rfl
lemma f865 : H a 0xd0258254203f := seed 4700242046 rfl
lemma f866 : H a 0xd0270254203f := seed 5505548414 rfl
lemma f867 : H a 0xd0170154103f := seed 5505548415 rfl
lemma f868 : H a 0xd0270258203f := seed 5639766142 rfl
lemma f869 : H a 0xb0298294203f := seed 1481113726 rfl
lemma f870 : H a 0xb0198194103f := seed 1481113727 rfl
lemma f871 : H a 0xd0298294203f := seed 2554855550 rfl
lemma f872 : H a 0xd0198194103f := seed 2554855551 rfl
lemma f873 : H a 0xd02b0294203f := seed 3360161918 rfl
lemma f874 : H a 0xd01b0194103f := seed 3360161919 rfl
lemma f875 : H a 0xd02b0298203f := seed 3494379646 rfl
lemma f876 : H a 0xd01b0198103f := seed 3494379647 rfl
lemma f877 : H a 0x70168164103f := seed 942669951 rfl
lemma f878 : H a 0xe0268264203f := seed 4700766334 rfl
lemma f879 : H a 0xe0270264203f := seed 4969201790 rfl
lemma f880 : H a 0xe0170164103f := seed 4969201791 rfl
lemma f881 : H a 0xe0270268203f := seed 5103419518 rfl
lemma f882 : H a 0xe0170168103f := seed 5103419519 rfl
lemma f883 : H a 0xb02a82a4203f := seed 944767102 rfl
lemma f884 : H a 0xb01a81a4103f := seed 944767103 rfl
lemma f885 : H a 0xe02b02a4203f := seed 2823815294 rfl
lemma f886 : H a 0xe01b01a4103f := seed 2823815295 rfl
lemma f887 : H a 0xe02b02a8203f := seed 2958033022 rfl
lemma f888 : H a 0xd02c82c4203f := seed 945815678 rfl
lemma f889 : H a 0xd01c81c4103f := seed 945815679 rfl
lemma f890 : H a 0xe01c81c4103f := seed 1482686591 rfl
lemma f891 : H a 0xe02d02c4203f := seed 1751122046 rfl
lemma f892 : H a 0xe01d01c4103f := seed 1751122047 rfl
lemma f893 : H a 0xe02d02c8203f := seed 1885339774 rfl
lemma f894 : H a 0xe01d01c8103f := seed 1885339775 rfl
lemma f895 : H a 60148027487 := seed 852157 rfl
lemma f896 : H a 47283052639 := seed 2425020 rfl
lemma f897 : H a 47266271327 := seed 2425021 rfl
lemma f898 : H a 30090596447 := seed 4522173 rfl
lemma f899 : H a 53723930719 := seed 1638588 rfl
lemma f900 : H a 53707149407 := seed 1638589 rfl
lemma f901 : H a 45119311967 := seed 2687165 rfl
lemma f902 : H a 27943637087 := seed 4784317 rfl
lemma f903 : H a 0x8a14a11a105f := seed 6979649727 rfl
lemma f904 : H a 90242113212511 := seed 3490250943 rfl
lemma f905 : H a 0xa213212a105f := seed 5101387967 rfl
lemma f906 : H a 0xc21a2192105f := seed 3762356415 rfl
lemma f907 : H a 96909529849951 := seed 3289120958 rfl
lemma f908 : H a 0xc825824a205f := seed 4901306558 rfl
lemma f909 : H a 0x70238232205f := seed 2484601022 rfl
lemma f910 : H a 55870627999 := seed 1245500 rfl
lemma f911 : H a 55853846687 := seed 1245501 rfl
lemma f912 : H a 47266009247 := seed 2294077 rfl
lemma f913 : H a 30090334367 := seed 4391229 rfl
lemma f914 : H a 22592757919 := seed 5308732 rfl
lemma f915 : H a 0x86146116109f := seed 6979518783 rfl
lemma f916 : H a 0x92132116109f := seed 5503516991 rfl
lemma f917 : H a 0xa2262226209f := seed 6577783102 rfl
lemma f918 : H a 0xc2192186109f := seed 2822832447 rfl
lemma f919 : H a 0xa4134126109f := seed 4900127039 rfl
lemma f920 : H a 0xb0234232209f := seed 4497867070 rfl
lemma f921 : H a 0xb01a41a2109f := seed 743440703 rfl
lemma f922 : H a 0xe01d01c4109f := seed 1751122239 rfl
lemma f923 : H a 53723144479 := seed 1245756 rfl
lemma f924 : H a 44061827359 := seed 2425404 rfl
lemma f925 : H a 44045046047 := seed 2425405 rfl
lemma f926 : H a 26869371167 := seed 4522557 rfl
lemma f927 : H a 20428493087 := seed 5308989 rfl
lemma f928 : H a 11840655647 := seed 6357565 rfl
lemma f929 : H a 0x8614610e111f := seed 6711083583 rfl
lemma f930 : H a 0x8a14a10e111f := seed 6576996927 rfl
lemma f931 : H a 0xc2262246211f := seed 5505090110 rfl
lemma f932 : H a 0xc824c24a211f := seed 4498653758 rfl
lemma f933 : H a 55852274207 := seed 459837 rfl
lemma f934 : H a 53705314847 := seed 721981 rfl
lemma f935 : H a 40823558687 := seed 2294845 rfl
lemma f936 : H a 23664665119 := seed 4391996 rfl
lemma f937 : H a 23647883807 := seed 4391997 rfl
lemma f938 : H a 52631835167 := seed 853053 rfl
lemma f939 : H a 39766860319 := seed 2425916 rfl
lemma f940 : H a 39750079007 := seed 2425917 rfl
lemma f941 : H a 20444226079 := seed 4785212 rfl
lemma f942 : H a 0xc414c146121f := seed 4632740927 rfl
lemma f943 : H a 0xc418c186121f := seed 2487354431 rfl
lemma f944 : H a 96846165447199 := seed 740557887 rfl
lemma f945 : H a 45115380767 := seed 723005 rfl
lemma f946 : H a 40838243359 := seed 1247292 rfl
lemma f947 : H a 15057949727 := seed 4393021 rfl
lemma f948 : H a 13984470047 := seed 4524093 rfl
lemma f949 : H a 37601023007 := seed 1640509 rfl
lemma f950 : H a 0x8611610e141f := seed 5100472383 rfl
lemma f951 : H a 0x8a11a10e141f := seed 4966385727 rfl
lemma f952 : H a 0x92132116141f := seed 5503518783 rfl
lemma f953 : H a 0x9218a186141f := seed 943786047 rfl
lemma f954 : H a 48454764991519 := seed 1678116927 rfl
lemma f955 : H a 0xa4134126141f := seed 4900128831 rfl
lemma f956 : H a 0xb0234232241f := seed 4497868862 rfl
lemma f957 : H a 0xb0138132141f := seed 4632086591 rfl
lemma f958 : H a 30082471967 := seed 462909 rfl
lemma f959 : H a 27952293919 := seed 725052 rfl
lemma f960 : H a 27935512607 := seed 725053 rfl
lemma f961 : H a 23658375199 := seed 1249340 rfl
lemma f962 : H a 23641593887 := seed 1249341 rfl
lemma f963 : H a 22568114207 := seed 1380413 rfl
lemma f964 : H a 13997058079 := seed 2428988 rfl
lemma f965 : H a 13980276767 := seed 2428989 rfl
lemma f966 : H a 20437936159 := seed 1642556 rfl
lemma f967 : H a 20421154847 := seed 1642557 rfl
lemma f968 : H a 7539398687 := seed 3215421 rfl
lemma f969 : H a 77040456701983 := seed 2952990783 rfl
lemma f970 : H a 81439576954911 := seed 2818904127 rfl
lemma f971 : H a 55120034670623 := seed 1476988990 rfl
lemma f972 : H a 0x62132126181f := seed 2819690559 rfl
lemma f973 : H a 48454764992543 := seed 1678118975 rfl
lemma f974 : H a 0x6813812a181f := seed 2752778303 rfl
lemma f975 : H a 0x6814c14a181f := seed 1277431871 rfl
lemma f976 : H a 0x6825824a281f := seed 1680085054 rfl
lemma f977 : H a 0x70138132181f := seed 2484604991 rfl
lemma f978 : H a 30090530927 := seed 4489437 rfl
lemma f979 : H a 53723865199 := seed 1605852 rfl
lemma f980 : H a 53707083887 := seed 1605853 rfl
lemma f981 : H a 27943571567 := seed 4751581 rfl
lemma f982 : H a 89142333083759 := seed 3490218207 rfl
lemma f983 : H a 0xc8158149106f := seed 4867752159 rfl
lemma f984 : H a 47265943727 := seed 2261341 rfl
lemma f985 : H a 39768367279 := seed 3178844 rfl
lemma f986 : H a 0xa423422520af := seed 4866572638 rfl
lemma f987 : H a 0xc41a418510af := seed 3259105631 rfl
lemma f988 : H a 0xd01b019110af := seed 3259498847 rfl
lemma f989 : H a 60163957039 := seed 426588 rfl
lemma f990 : H a 60147175727 := seed 426589 rfl
lemma f991 : H a 53723078959 := seed 1213020 rfl
lemma f992 : H a 45135241519 := seed 2261596 rfl
lemma f993 : H a 27959566639 := seed 4358748 rfl
lemma f994 : H a 44061761839 := seed 2392668 rfl
lemma f995 : H a 44044980527 := seed 2392669 rfl
lemma f996 : H a 26869305647 := seed 4489821 rfl
lemma f997 : H a 11840590127 := seed 6324829 rfl
lemma f998 : H a 0xe0264261212f := seed 4465885790 rfl
lemma f999 : H a 55852208687 := seed 427101 rfl
lemma f1000 : H a 53705249327 := seed 689245 rfl
lemma f1001 : H a 39766794799 := seed 2393180 rfl
lemma f1002 : H a 20427379247 := seed 4752477 rfl
lemma f1003 : H a 7545623087 := seed 6325341 rfl
lemma f1004 : H a 80339796824623 := seed 2818868319 rfl
lemma f1005 : H a 96833277334063 := seed 2316043359 rfl
lemma f1006 : H a 0x9811c119122f := seed 4463527007 rfl
lemma f1007 : H a 0xc824c249222f := seed 4465099870 rfl
lemma f1008 : H a 0xc814c149122f := seed 4465099871 rfl
lemma f1009 : H a 0xc8158149122f := seed 4867753055 rfl
lemma f1010 : H a 47262274607 := seed 428125 rfl
lemma f1011 : H a 44041835567 := seed 821341 rfl
lemma f1012 : H a 40756304483375 := seed 1879214175 rfl
lemma f1013 : H a 45155424736303 := seed 1745127519 rfl
lemma f1014 : H a 57250858472495 := seed 1376389215 rfl
lemma f1015 : H a 0xa4234225242f := seed 4866574430 rfl
lemma f1016 : H a 30082406447 := seed 430173 rfl
lemma f1017 : H a 27952228399 := seed 692316 rfl
lemma f1018 : H a 27935447087 := seed 692317 rfl
lemma f1019 : H a 15070472239 := seed 2265180 rfl
lemma f1020 : H a 15053690927 := seed 2265181 rfl
lemma f1021 : H a 26878748719 := seed 823388 rfl
lemma f1022 : H a 26861967407 := seed 823389 rfl
lemma f1023 : H a 22584829999 := seed 1347676 rfl
lemma f1024 : H a 22568048687 := seed 1347677 rfl
lemma f1025 : H a 20437870639 := seed 1609820 rfl
lemma f1026 : H a 20421089327 := seed 1609821 rfl
lemma f1027 : H a 11833251887 := seed 2658397 rfl
lemma f1028 : H a 40756304484399 := seed 1879216223 rfl
lemma f1029 : H a 45155424737327 := seed 1745129567 rfl
lemma f1030 : H a 80339796826159 := seed 2818871391 rfl
lemma f1031 : H a 80344091793455 := seed 3355742303 rfl
lemma f1032 : H a 92448118609967 := seed 841093215 rfl
lemma f1033 : H a 0x6414c145182f := seed 1377964127 rfl
lemma f1034 : H a 60147568847 := seed 623005 rfl
lemma f1035 : H a 0xd01b019110cf := seed 3259498911 rfl
lemma f1036 : H a 53722947919 := seed 1147548 rfl
lemma f1037 : H a 19891556687 := seed 5276317 rfl
lemma f1038 : H a 0xc1189183114f := seed 2487255711 rfl
lemma f1039 : H a 0xa228a283214f := seed 1379992222 rfl
lemma f1040 : H a 0xc22a2283214f := seed 3259040414 rfl
lemma f1041 : H a 0xc814a149114f := seed 4397990559 rfl
lemma f1042 : H a 0xe01c81c2114f := seed 1415578271 rfl
lemma f1043 : H a 55868858959 := seed 361628 rfl
lemma f1044 : H a 53721899599 := seed 623772 rfl
lemma f1045 : H a 23647687247 := seed 4293789 rfl
lemma f1046 : H a 0xc1189183124f := seed 2487256223 rfl
lemma f1047 : H a 0xc225224a224f := seed 5102437534 rfl
lemma f1048 : H a 0xc218a183124f := seed 2453734559 rfl
lemma f1049 : H a 0x9811a119124f := seed 4396418207 rfl
lemma f1050 : H a 0xc824a249224f := seed 4397991070 rfl
lemma f1051 : H a 0xc814a149124f := seed 4397991071 rfl
lemma f1052 : H a 0xc825824a224f := seed 4901307550 rfl
lemma f1053 : H a 0xd0258252224f := seed 4633134238 rfl
lemma f1054 : H a 0xd0158152124f := seed 4633134239 rfl
lemma f1055 : H a 0xd01c81c2124f := seed 878707871 rfl
lemma f1056 : H a 45115184207 := seed 624797 rfl
lemma f1057 : H a 15074534479 := seed 4294812 rfl
lemma f1058 : H a 0x98138119144f := seed 5403052191 rfl
lemma f1059 : H a 0x9813811a144f := seed 5436606623 rfl
lemma f1060 : H a 0xa8138129144f := seed 4866705567 rfl
lemma f1061 : H a 0xb0138131144f := seed 4598532255 rfl
lemma f1062 : H a 0xb0238232244f := seed 4632086686 rfl
lemma f1063 : H a 26325096527 := seed 823453 rfl
lemma f1064 : H a 13443340367 := seed 2396317 rfl
lemma f1065 : H a 80339796695119 := seed 2751762591 rfl
lemma f1066 : H a 44061368719 := seed 2196252 rfl
lemma f1067 : H a 26885693839 := seed 4293404 rfl
lemma f1068 : H a 43507847567 := seed 2261789 rfl
lemma f1069 : H a 0x86146126118f := seed 7516390175 rfl
lemma f1070 : H a 0xc41c21c1118f := seed 241173279 rfl
lemma f1071 : H a 22590726799 := seed 4293916 rfl
lemma f1072 : H a 52094636687 := seed 689437 rfl
lemma f1073 : H a 18816766607 := seed 4752669 rfl
lemma f1074 : H a 5935010447 := seed 6325533 rfl
lemma f1075 : H a 0xc1191185128f := seed 2822800671 rfl
lemma f1076 : H a 0xd0254252228f := seed 4498916638 rfl
lemma f1077 : H a 44058223759 := seed 624924 rfl
lemma f1078 : H a 44041442447 := seed 624925 rfl
lemma f1079 : H a 39747523727 := seed 1149213 rfl
lemma f1080 : H a 13984011407 := seed 4294941 rfl
lemma f1081 : H a 43504702607 := seed 690461 rfl
lemma f1082 : H a 5932913807 := seed 5277981 rfl
lemma f1083 : H a 54019180668047 := seed 1275627806 rfl
lemma f1084 : H a 0xa1185183148f := seed 1279297823 rfl
lemma f1085 : H a 0xa2232223248f := seed 4866509086 rfl
lemma f1086 : H a 0xa2132126148f := seed 4967172383 rfl
lemma f1087 : H a 0xa2186183148f := seed 1245776159 rfl
lemma f1088 : H a 57317984117903 := seed 1175062814 rfl
lemma f1089 : H a 57249247859855 := seed 1175062815 rfl
lemma f1090 : H a 0x94134115148f := seed 5402921247 rfl
lemma f1091 : H a 0x94234216248f := seed 5436475678 rfl
lemma f1092 : H a 0xa4134125148f := seed 4866574623 rfl
lemma f1093 : H a 0xa4234226248f := seed 4900129054 rfl
lemma f1094 : H a 0xa4134126148f := seed 4900129055 rfl
lemma f1095 : H a 0xa4194186148f := seed 1682049311 rfl
lemma f1096 : H a 57256765887631 := seed 236456223 rfl
lemma f1097 : H a 0xb0134132148f := seed 4497869087 rfl
lemma f1098 : H a 0xb0294291248f := seed 1246234910 rfl
lemma f1099 : H a 0xb0194192148f := seed 1279789343 rfl
lemma f1100 : H a 0xb02a22a1248f := seed 642779422 rfl
lemma f1101 : H a 26324834447 := seed 692509 rfl
lemma f1102 : H a 0x70134132188f := seed 2350387487 rfl
lemma f1103 : H a 53721113359 := seed 230940 rfl
lemma f1104 : H a 52094112527 := seed 427549 rfl
lemma f1105 : H a 19889722127 := seed 4359709 rfl
lemma f1106 : H a 0xc1189183130f := seed 2487256607 rfl
lemma f1107 : H a 0x8c24c20d230f := seed 6476400158 rfl
lemma f1108 : H a 0xc814c149130f := seed 4465100319 rfl
lemma f1109 : H a 0xc824c24a230f := seed 4498654750 rfl
lemma f1110 : H a 0xc814c14a130f := seed 4498654751 rfl
lemma f1111 : H a 44057699599 := seed 363036 rfl
lemma f1112 : H a 11853309199 := seed 4295196 rfl
lemma f1113 : H a 43504178447 := seed 428573 rfl
lemma f1114 : H a 0x8612610e150f := seed 5637343775 rfl
lemma f1115 : H a 48451006829839 := seed 1174800927 rfl
lemma f1116 : H a 0xa418c186150f := seed 1413614111 rfl
lemma f1117 : H a 0xa822c229250f := seed 4464052766 rfl
lemma f1118 : H a 26324310287 := seed 430621 rfl
lemma f1119 : H a 19883432207 := seed 1217053 rfl
lemma f1120 : H a 10222115087 := seed 2396701 rfl
lemma f1121 : H a 77044751669519 := seed 3489862175 rfl
lemma f1122 : H a 48451006830863 := seed 1174802975 rfl
lemma f1123 : H a 0x6824c24a290f := seed 1277432350 rfl
lemma f1124 : H a 0x6814c14a190f := seed 1277432351 rfl
lemma f1125 : H a 37615773199 := seed 625692 rfl
lemma f1126 : H a 37062252047 := seed 691229 rfl
lemma f1127 : H a 0x8611610e160f := seed 5100473375 rfl
lemma f1128 : H a 23656344079 := seed 234524 rfl
lemma f1129 : H a 7537367567 := seed 2200605 rfl
lemma f1130 : H a 89148778420751 := seed 941659167 rfl
lemma f1131 : H a 77040456702479 := seed 2952991775 rfl
lemma f1132 : H a 30858820786703 := seed 637932575 rfl
lemma f1133 : H a 96846165383695 := seed 707007519 rfl
lemma f1134 : H a 96917049715215 := seed 472388638 rfl
lemma f1135 : H a 13439409167 := seed 432157 rfl
lemma f1136 : H a 6998531087 := seed 1218589 rfl
lemma f1137 : H a 23161970564111 := seed 872585247 rfl
lemma f1138 : H a 57249247861775 := seed 1175066655 rfl
lemma f1139 : H a 61721937587215 := seed 739514398 rfl
lemma f1140 : H a 60147929207 := seed 803053 rfl
lemma f1141 : H a 47266173047 := seed 2375917 rfl
lemma f1142 : H a 30107279479 := seed 4473068 rfl
lemma f1143 : H a 30090498167 := seed 4473069 rfl
lemma f1144 : H a 53707051127 := seed 1589485 rfl
lemma f1145 : H a 23666401399 := seed 5259500 rfl
lemma f1146 : H a 23649620087 := seed 5259501 rfl
lemma f1147 : H a 0x88a48a18a077 := seed 6979600622 rfl
lemma f1148 : H a 0xc81581489077 := seed 4850974959 rfl
lemma f1149 : H a 0xe02a82a0a077 := seed 2437939438 rfl
lemma f1150 : H a 0xd01c81c09077 := seed 828375279 rfl
lemma f1151 : H a 60147667127 := seed 672109 rfl
lemma f1152 : H a 47265910967 := seed 2244973 rfl
lemma f1153 : H a 44062253239 := seed 2638188 rfl
lemma f1154 : H a 44045471927 := seed 2638189 rfl
lemma f1155 : H a 22592659639 := seed 5259628 rfl
lemma f1156 : H a 13988040887 := seed 6308205 rfl
lemma f1157 : H a 0x94234214a0b7 := seed 5386142062 rfl
lemma f1158 : H a 0x9413411490b7 := seed 5386142063 rfl
lemma f1159 : H a 0xa4234224a0b7 := seed 4849795438 rfl
lemma f1160 : H a 0xa413412490b7 := seed 4849795439 rfl
lemma f1161 : H a 0xb01a41a090b7 := seed 693109103 rfl
lemma f1162 : H a 0xd01c41c090b7 := seed 694157679 rfl
lemma f1163 : H a 60163924279 := seed 410220 rfl
lemma f1164 : H a 60147142967 := seed 410221 rfl
lemma f1165 : H a 53723046199 := seed 1196652 rfl
lemma f1166 : H a 53706264887 := seed 1196653 rfl
lemma f1167 : H a 27942752567 := seed 4342381 rfl
lemma f1168 : H a 44061729079 := seed 2376300 rfl
lemma f1169 : H a 26869272887 := seed 4473453 rfl
lemma f1170 : H a 20428394807 := seed 5259885 rfl
lemma f1171 : H a 11840557367 := seed 6308461 rfl
lemma f1172 : H a 0xa09289249137 := seed 4698686063 rfl
lemma f1173 : H a 0xe02a82a0a137 := seed 2437939822 rfl
lemma f1174 : H a 55852175927 := seed 410733 rfl
lemma f1175 : H a 53721997879 := seed 672876 rfl
lemma f1176 : H a 53705216567 := seed 672877 rfl
lemma f1177 : H a 23647785527 := seed 4342893 rfl
lemma f1178 : H a 52631736887 := seed 803949 rfl
lemma f1179 : H a 39766762039 := seed 2376812 rfl
lemma f1180 : H a 37603021367 := seed 2638957 rfl
lemma f1181 : H a 20444127799 := seed 4736108 rfl
lemma f1182 : H a 20427346487 := seed 4736109 rfl
lemma f1183 : H a 7545590327 := seed 6308973 rfl
lemma f1184 : H a 88598888354359 := seed 941638767 rfl
lemma f1185 : H a 0xc09909889237 := seed 2957001839 rfl
lemma f1186 : H a 0xc418c1849237 := seed 2437022831 rfl
lemma f1187 : H a 0xc81581489237 := seed 4850975855 rfl
lemma f1188 : H a 0xd0254250a237 := seed 4448584814 rfl
lemma f1189 : H a 47262241847 := seed 411757 rfl
lemma f1190 : H a 45132063799 := seed 673900 rfl
lemma f1191 : H a 45115282487 := seed 673901 rfl
lemma f1192 : H a 15074632759 := seed 4343916 rfl
lemma f1193 : H a 39764665399 := seed 1329260 rfl
lemma f1194 : H a 39747884087 := seed 1329261 rfl
lemma f1195 : H a 14001153079 := seed 4474988 rfl
lemma f1196 : H a 13984371767 := seed 4474989 rfl
lemma f1197 : H a 37600924727 := seed 1591405 rfl
lemma f1198 : H a 40206414418999 := seed 1879197807 rfl
lemma f1199 : H a 0xa09289249437 := seed 4698687599 rfl
lemma f1200 : H a 57319594697783 := seed 1359612014 rfl
end BorsukCert

namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f1201 : H a 0x941341149437 := seed 5386143855 rfl
lemma f1202 : H a 0xa4234224a437 := seed 4849797230 rfl
lemma f1203 : H a 0xa41341249437 := seed 4849797231 rfl
lemma f1204 : H a 0xb01941909437 := seed 1229457519 rfl
lemma f1205 : H a 0xb01a41a09437 := seed 693110895 rfl
lemma f1206 : H a 30082373687 := seed 413805 rfl
lemma f1207 : H a 27952195639 := seed 675948 rfl
lemma f1208 : H a 23658276919 := seed 1200236 rfl
lemma f1209 : H a 23641495607 := seed 1200237 rfl
lemma f1210 : H a 15070439479 := seed 2248812 rfl
lemma f1211 : H a 26878715959 := seed 807020 rfl
lemma f1212 : H a 26861934647 := seed 807021 rfl
lemma f1213 : H a 13996959799 := seed 2379884 rfl
lemma f1214 : H a 13980178487 := seed 2379885 rfl
lemma f1215 : H a 20437837879 := seed 1593452 rfl
lemma f1216 : H a 11850000439 := seed 2642028 rfl
lemma f1217 : H a 11833219127 := seed 2642029 rfl
lemma f1218 : H a 7539300407 := seed 3166317 rfl
lemma f1219 : H a 40206414420023 := seed 1879199855 rfl
lemma f1220 : H a 0x609309289837 := seed 2953859183 rfl
lemma f1221 : H a 88598888355895 := seed 941641839 rfl
lemma f1222 : H a 57319594698807 := seed 1359614062 rfl
lemma f1223 : H a 57323890714679 := seed 823267438 rfl
lemma f1224 : H a 0x64234224a837 := seed 2702315630 rfl
lemma f1225 : H a 96846165350455 := seed 690229359 rfl
lemma f1226 : H a 0x681581489837 := seed 1629753455 rfl
lemma f1227 : H a 0x70268260a837 := seed 825233518 rfl
lemma f1228 : H a 60147536087 := seed 606637 rfl
lemma f1229 : H a 0x9213211290d7 := seed 5386076591 rfl
lemma f1230 : H a 0x70232230a0d7 := seed 2232943022 rfl
lemma f1231 : H a 0xd017015210d7 := seed 5438439855 rfl
lemma f1232 : H a 0xb019219090d7 := seed 1162346927 rfl
lemma f1233 : H a 0xe017016210d7 := seed 4902093231 rfl
lemma f1234 : H a 27959402839 := seed 4276908 rfl
lemma f1235 : H a 27942621527 := seed 4276909 rfl
lemma f1236 : H a 11303686487 := seed 6308525 rfl
lemma f1237 : H a 0x8294290a9157 := seed 6710969007 rfl
lemma f1238 : H a 0xc09889829157 := seed 2487239343 rfl
lemma f1239 : H a 0xa228a282a157 := seed 1363215022 rfl
lemma f1240 : H a 0xc22a2282a157 := seed 3242263214 rfl
lemma f1241 : H a 0x6824a248a157 := seed 1159987886 rfl
lemma f1242 : H a 0x68262260a157 := seed 355467950 rfl
lemma f1243 : H a 0xc81c21c09157 := seed 358613679 rfl
lemma f1244 : H a 55852044887 := seed 345261 rfl
lemma f1245 : H a 40823329367 := seed 2180269 rfl
lemma f1246 : H a 23664435799 := seed 4277420 rfl
lemma f1247 : H a 23647654487 := seed 4277421 rfl
lemma f1248 : H a 52111647319 := seed 804012 rfl
lemma f1249 : H a 39229891159 := seed 2376876 rfl
lemma f1250 : H a 0x8291290a9257 := seed 5100356783 rfl
lemma f1251 : H a 0xc09889829257 := seed 2487239855 rfl
lemma f1252 : H a 81508312982103 := seed 2701460654 rfl
lemma f1253 : H a 0x8a14a11a1257 := seed 6979650735 rfl
lemma f1254 : H a 0xc218a1829257 := seed 2436957359 rfl
lemma f1255 : H a 96832740430423 := seed 2232157359 rfl
lemma f1256 : H a 96914364736087 := seed 623117486 rfl
lemma f1257 : H a 0xc81581489257 := seed 4850975919 rfl
lemma f1258 : H a 0xc82c22c0a257 := seed 358614190 rfl
lemma f1259 : H a 0xc81c21c09257 := seed 358614191 rfl
lemma f1260 : H a 0xd02c22c0a257 := seed 627049646 rfl
lemma f1261 : H a 0xd02c82c22257 := seed 878707886 rfl
lemma f1262 : H a 45115151447 := seed 608429 rfl
lemma f1263 : H a 15074501719 := seed 4278444 rfl
lemma f1264 : H a 15057720407 := seed 4278445 rfl
lemma f1265 : H a 0x829229129457 := seed 5905664175 rfl
lemma f1266 : H a 61648368342103 := seed 1158416559 rfl
lemma f1267 : H a 0x9813811a1457 := seed 5436606639 rfl
lemma f1268 : H a 61721400616023 := seed 622069934 rfl
lemma f1269 : H a 0xa813812a1457 := seed 4900260015 rfl
lemma f1270 : H a 0x9818a1889457 := seed 625215663 rfl
lemma f1271 : H a 0xa818a1889457 := seed 1162086575 rfl
lemma f1272 : H a 61723548623959 := seed 353896622 rfl
lemma f1273 : H a 0xb01321309457 := seed 4380428463 rfl
lemma f1274 : H a 0xb01921909457 := seed 1162348719 rfl
lemma f1275 : H a 30099023959 := seed 348332 rfl
lemma f1276 : H a 30082242647 := seed 348333 rfl
lemma f1277 : H a 27935283287 := seed 610477 rfl
lemma f1278 : H a 23658145879 := seed 1134764 rfl
lemma f1279 : H a 26325063767 := seed 807085 rfl
lemma f1280 : H a 22047926359 := seed 1331372 rfl
lemma f1281 : H a 44605534541911 := seed 1678004399 rfl
lemma f1282 : H a 79794201598039 := seed 3288617135 rfl
lemma f1283 : H a 90242113214551 := seed 3490255023 rfl
lemma f1284 : H a 61648368343127 := seed 1158418607 rfl
lemma f1285 : H a 96845628479575 := seed 623120559 rfl
lemma f1286 : H a 0x68258248a857 := seed 1629753518 rfl
lemma f1287 : H a 0x6815814a1857 := seed 1680085167 rfl
lemma f1288 : H a 61723548624983 := seed 353898670 rfl
lemma f1289 : H a 0x701321309857 := seed 2232946863 rfl
lemma f1290 : H a 0x70238230a857 := seed 2434273454 rfl
lemma f1291 : H a 0x70252250a857 := seed 1160253614 rfl
lemma f1292 : H a 0x701581509857 := seed 1361580207 rfl
lemma f1293 : H a 44061335959 := seed 2179884 rfl
lemma f1294 : H a 26885661079 := seed 4277036 rfl
lemma f1295 : H a 26868879767 := seed 4277037 rfl
lemma f1296 : H a 0xa41861849197 := seed 1161954095 rfl
lemma f1297 : H a 0xc41c21c09197 := seed 224396079 rfl
lemma f1298 : H a 52094603927 := seed 673069 rfl
lemma f1299 : H a 0x829129069297 := seed 4966139183 rfl
lemma f1300 : H a 0x909149129297 := seed 4496835887 rfl
lemma f1301 : H a 0x861461161297 := seed 6979519791 rfl
lemma f1302 : H a 0xc41861849297 := seed 2235696431 rfl
lemma f1303 : H a 0xc42c22c0a297 := seed 224396590 rfl
lemma f1304 : H a 0xd02c22c0a297 := seed 627049774 rfl
lemma f1305 : H a 14000759959 := seed 4278572 rfl
lemma f1306 : H a 13983978647 := seed 4278573 rfl
lemma f1307 : H a 13447238807 := seed 4344109 rfl
lemma f1308 : H a 35990312087 := seed 1591597 rfl
lemma f1309 : H a 0x829129069497 := seed 4966140207 rfl
lemma f1310 : H a 0x849149069497 := seed 4899096879 rfl
lemma f1311 : H a 53469290603671 := seed 1275611438 rfl
lemma f1312 : H a 0xa0a30a24a497 := seed 4967123246 rfl
lemma f1313 : H a 0xa09849829497 := seed 1279281455 rfl
lemma f1314 : H a 0x921321129497 := seed 5386078511 rfl
lemma f1315 : H a 0xa21261229497 := seed 4447078703 rfl
lemma f1316 : H a 0xa21321261497 := seed 4967172399 rfl
lemma f1317 : H a 57317984085143 := seed 1158285614 rfl
lemma f1318 : H a 57249247827095 := seed 1158285615 rfl
lemma f1319 : H a 0x941341149497 := seed 5386144047 rfl
lemma f1320 : H a 0x942342162497 := seed 5436475694 rfl
lemma f1321 : H a 0xa41341249497 := seed 4849797423 rfl
lemma f1322 : H a 0xa41341261497 := seed 4900129071 rfl
lemma f1323 : H a 30081980567 := seed 217389 rfl
lemma f1324 : H a 26861541527 := seed 610605 rfl
lemma f1325 : H a 13996566679 := seed 2183468 rfl
lemma f1326 : H a 13979785367 := seed 2183469 rfl
lemma f1327 : H a 13443045527 := seed 2249005 rfl
lemma f1328 : H a 53469290604695 := seed 1275613486 rfl
lemma f1329 : H a 57317984086167 := seed 1158287662 rfl
lemma f1330 : H a 57249247828119 := seed 1158287663 rfl
lemma f1331 : H a 57253543843991 := seed 621941039 rfl
lemma f1332 : H a 0x701341321897 := seed 2350387503 rfl
lemma f1333 : H a 53704299287 := seed 214573 rfl
lemma f1334 : H a 20443210519 := seed 4277804 rfl
lemma f1335 : H a 20426429207 := seed 4277805 rfl
lemma f1336 : H a 35991884567 := seed 2377261 rfl
lemma f1337 : H a 3787494167 := seed 6309421 rfl
lemma f1338 : H a 0xc09889829317 := seed 2487240239 rfl
lemma f1339 : H a 0xc228a282a317 := seed 2436957742 rfl
lemma f1340 : H a 0xc41861849317 := seed 2235696687 rfl
lemma f1341 : H a 0xc814c14a1317 := seed 4498654767 rfl
lemma f1342 : H a 0xc42c22c0a317 := seed 224396846 rfl
lemma f1343 : H a 0xc41c21c09317 := seed 224396847 rfl
lemma f1344 : H a 0xc82c22c0a317 := seed 358614574 rfl
lemma f1345 : H a 44057666839 := seed 346668 rfl
lemma f1346 : H a 11853276439 := seed 4278828 rfl
lemma f1347 : H a 11836495127 := seed 4278829 rfl
lemma f1348 : H a 10226275607 := seed 4475437 rfl
lemma f1349 : H a 0x8c10e10c9517 := seed 4379249199 rfl
lemma f1350 : H a 0xa41261249517 := seed 4380035631 rfl
lemma f1351 : H a 0xa41861849517 := seed 1161955887 rfl
lemma f1352 : H a 0xa818a1889517 := seed 1162086959 rfl
lemma f1353 : H a 0xa41a21a09517 := seed 223349295 rfl
lemma f1354 : H a 27934497047 := seed 217645 rfl
lemma f1355 : H a 26324277527 := seed 414253 rfl
lemma f1356 : H a 19883399447 := seed 1200685 rfl
lemma f1357 : H a 10222082327 := seed 2380333 rfl
lemma f1358 : H a 81443871922455 := seed 3355775535 rfl
lemma f1359 : H a 0x641261249917 := seed 2232554031 rfl
lemma f1360 : H a 0x6412c1249917 := seed 2433880623 rfl
lemma f1361 : H a 0x6824a248a917 := seed 1159991854 rfl
lemma f1362 : H a 0x6824c248a917 := seed 1227100718 rfl
lemma f1363 : H a 0x6824c24a2917 := seed 1277432366 rfl
lemma f1364 : H a 0x6814c14a1917 := seed 1277432367 rfl
lemma f1365 : H a 0x68262260a917 := seed 355471918 rfl
lemma f1366 : H a 7558309399 := seed 4279340 rfl
lemma f1367 : H a 0x829129069617 := seed 4966140975 rfl
lemma f1368 : H a 0x849149069617 := seed 4899097647 rfl
lemma f1369 : H a 0x909149129617 := seed 4496837679 rfl
lemma f1370 : H a 30858820752919 := seed 621153327 rfl
lemma f1371 : H a 30929705018903 := seed 352980014 rfl
lemma f1372 : H a 0x941161149617 := seed 4379511855 rfl
lemma f1373 : H a 0x8c1861849617 := seed 356650031 rfl
lemma f1374 : H a 20435872279 := seed 611372 rfl
lemma f1375 : H a 19882351127 := seed 676909 rfl
lemma f1376 : H a 20412520372759 := seed 939611183 rfl
lemma f1377 : H a 30858820753943 := seed 621155375 rfl
lemma f1378 : H a 30929705019927 := seed 352982062 rfl
lemma f1379 : H a 92433619917335 := seed 2232030255 rfl
lemma f1380 : H a 92435230530071 := seed 2433356847 rfl
lemma f1381 : H a 96914364738071 := seed 623121454 rfl
lemma f1382 : H a 96845628480023 := seed 623121455 rfl
lemma f1383 : H a 96846165449239 := seed 740561967 rfl
lemma f1384 : H a 96917049715223 := seed 472388654 rfl
lemma f1385 : H a 11829156887 := seed 612397 rfl
lemma f1386 : H a 7552019479 := seed 1136684 rfl
lemma f1387 : H a 13439376407 := seed 415789 rfl
lemma f1388 : H a 53469290605591 := seed 1275615278 rfl
lemma f1389 : H a 30858820754455 := seed 621156399 rfl
lemma f1390 : H a 57249247829015 := seed 1158289455 rfl
lemma f1391 : H a 57319594699799 := seed 1359616046 rfl
lemma f1392 : H a 57250858441751 := seed 1359616047 rfl
lemma f1393 : H a 57253543844887 := seed 621942831 rfl
lemma f1394 : H a 61721400618007 := seed 622073902 rfl
lemma f1395 : H a 61721937587223 := seed 739514414 rfl
lemma f1396 : H a 60164251879 := seed 573900 rfl
lemma f1397 : H a 55870333159 := seed 1098188 rfl
lemma f1398 : H a 47282495719 := seed 2146764 rfl
lemma f1399 : H a 0xe01a11a090e7 := seed 2203058639 rfl
lemma f1400 : H a 0xe01d01c090e7 := seed 1633681871 rfl
lemma f1401 : H a 53722849639 := seed 1098444 rfl
lemma f1402 : H a 53706068327 := seed 1098445 rfl
lemma f1403 : H a 43239641447 := seed 2376397 rfl
lemma f1404 : H a 0xc09889819167 := seed 2453684943 rfl
lemma f1405 : H a 0xc11891819167 := seed 2436924111 rfl
lemma f1406 : H a 0x681491489167 := seed 1126433487 rfl
lemma f1407 : H a 0xc81491489167 := seed 4347658959 rfl
lemma f1408 : H a 0xc81a81889167 := seed 3242459855 rfl
lemma f1409 : H a 0xe01c81c09167 := seed 1365246671 rfl
lemma f1410 : H a 0xe02c82c12167 := seed 1382023886 rfl
lemma f1411 : H a 55868760679 := seed 312524 rfl
lemma f1412 : H a 53721801319 := seed 574668 rfl
lemma f1413 : H a 53705020007 := seed 574669 rfl
lemma f1414 : H a 23664370279 := seed 4244684 rfl
lemma f1415 : H a 38961455719 := seed 2376908 rfl
lemma f1416 : H a 38944674407 := seed 2376909 rfl
lemma f1417 : H a 0x981191189267 := seed 4346086607 rfl
lemma f1418 : H a 0xc81491489267 := seed 4347659471 rfl
lemma f1419 : H a 0xc81581489267 := seed 4850975951 rfl
lemma f1420 : H a 0xd01981909267 := seed 2437416143 rfl
lemma f1421 : H a 0xd01981911267 := seed 2454193359 rfl
lemma f1422 : H a 0xd01c81c09267 := seed 828376271 rfl
lemma f1423 : H a 47278826599 := seed 313548 rfl
lemma f1424 : H a 45131867239 := seed 575692 rfl
lemma f1425 : H a 40837948519 := seed 1099980 rfl
lemma f1426 : H a 40821167207 := seed 1099981 rfl
lemma f1427 : H a 0x889289099467 := seed 5402544335 rfl
lemma f1428 : H a 53951518053479 := seed 1359513807 rfl
lemma f1429 : H a 0x981381191467 := seed 5403052239 rfl
lemma f1430 : H a 0xa81381291467 := seed 4866705615 rfl
lemma f1431 : H a 0xb01381309467 := seed 4581755087 rfl
lemma f1432 : H a 0xb01381311467 := seed 4598532303 rfl
lemma f1433 : H a 0xa81a11a09467 := seed 324012239 rfl
lemma f1434 : H a 30098958439 := seed 315596 rfl
lemma f1435 : H a 30082177127 := seed 315597 rfl
lemma f1436 : H a 27951999079 := seed 577740 rfl
lemma f1437 : H a 23658080359 := seed 1102028 rfl
lemma f1438 : H a 15070242919 := seed 2150604 rfl
lemma f1439 : H a 13174872167 := seed 2379981 rfl
lemma f1440 : H a 19615750247 := seed 1593549 rfl
lemma f1441 : H a 0x609309289867 := seed 2953859279 rfl
lemma f1442 : H a 53951518054503 := seed 1359515855 rfl
lemma f1443 : H a 96909529753703 := seed 3238793422 rfl
lemma f1444 : H a 96909529786471 := seed 3255570638 rfl
lemma f1445 : H a 96914096302183 := seed 589566158 rfl
lemma f1446 : H a 0x681491489867 := seed 1126437071 rfl
lemma f1447 : H a 0x70238230a867 := seed 2434273486 rfl
lemma f1448 : H a 0x701681611867 := seed 842010831 rfl
lemma f1449 : H a 60163465639 := seed 181068 rfl
lemma f1450 : H a 60146684327 := seed 181069 rfl
lemma f1451 : H a 52649107879 := seed 1098572 rfl
lemma f1452 : H a 52632326567 := seed 1098573 rfl
lemma f1453 : H a 44061270439 := seed 2147148 rfl
lemma f1454 : H a 43239379367 := seed 2245453 rfl
lemma f1455 : H a 18549346727 := seed 5260109 rfl
lemma f1456 : H a 0xc41a418511a7 := seed 3259106127 rfl
lemma f1457 : H a 55851717287 := seed 181581 rfl
lemma f1458 : H a 39766303399 := seed 2147660 rfl
lemma f1459 : H a 22590628519 := seed 4244812 rfl
lemma f1460 : H a 35723973287 := seed 2639181 rfl
lemma f1461 : H a 5666542247 := seed 6309197 rfl
lemma f1462 : H a 0x81a11a05a2a7 := seed 4966106446 rfl
lemma f1463 : H a 0x9111511192a7 := seed 4446520655 rfl
lemma f1464 : H a 0xc419418492a7 := seed 2705458511 rfl
lemma f1465 : H a 47278564519 := seed 182604 rfl
lemma f1466 : H a 44058125479 := seed 575820 rfl
lemma f1467 : H a 44041344167 := seed 575821 rfl
lemma f1468 : H a 39764206759 := seed 1100108 rfl
lemma f1469 : H a 39747425447 := seed 1100109 rfl
lemma f1470 : H a 14000694439 := seed 4245836 rfl
lemma f1471 : H a 13983913127 := seed 4245837 rfl
lemma f1472 : H a 43236234407 := seed 674125 rfl
lemma f1473 : H a 0x8191190594a7 := seed 4966107471 rfl
lemma f1474 : H a 54019180569767 := seed 1225296206 rfl
lemma f1475 : H a 0xa1291281a4a7 := seed 1631619406 rfl
lemma f1476 : H a 57248979391655 := seed 1124731215 rfl
lemma f1477 : H a 0x9413411494a7 := seed 5386144079 rfl
lemma f1478 : H a 0x9413411514a7 := seed 5402921295 rfl
lemma f1479 : H a 57322011665575 := seed 588384590 rfl
lemma f1480 : H a 0xa412512494a7 := seed 4346480975 rfl
lemma f1481 : H a 0xa4234224a4a7 := seed 4849797454 rfl
lemma f1482 : H a 0xa419418494a7 := seed 1631717711 rfl
lemma f1483 : H a 0xb013413094a7 := seed 4447537487 rfl
lemma f1484 : H a 0xb019419114a7 := seed 1246234959 rfl
lemma f1485 : H a 0xb01a41a094a7 := seed 693111119 rfl
lemma f1486 : H a 30098696359 := seed 184652 rfl
lemma f1487 : H a 26878257319 := seed 577868 rfl
lemma f1488 : H a 13996501159 := seed 2150732 rfl
lemma f1489 : H a 21762447527 := seed 1200461 rfl
lemma f1490 : H a 5660252327 := seed 3166541 rfl
lemma f1491 : H a 57248979392679 := seed 1124733263 rfl
lemma f1492 : H a 53721015079 := seed 181836 rfl
lemma f1493 : H a 53704233767 := seed 181837 rfl
lemma f1494 : H a 52647535399 := seed 312908 rfl
lemma f1495 : H a 20443144999 := seed 4245068 rfl
lemma f1496 : H a 20426363687 := seed 4245069 rfl
lemma f1497 : H a 35723449127 := seed 2377293 rfl
lemma f1498 : H a 0xc09889819327 := seed 2453685839 rfl
lemma f1499 : H a 0xc11891819327 := seed 2436925007 rfl
lemma f1500 : H a 0x8c24c20d2327 := seed 6476400206 rfl
lemma f1501 : H a 0xc418c1849327 := seed 2437023311 rfl
lemma f1502 : H a 83651220509479 := seed 186910287 rfl
lemma f1503 : H a 0xc824c248a327 := seed 4448323150 rfl
lemma f1504 : H a 45131080999 := seed 182860 rfl
lemma f1505 : H a 44057601319 := seed 313932 rfl
lemma f1506 : H a 37599941927 := seed 1100365 rfl
lemma f1507 : H a 3516962087 := seed 5261901 rfl
lemma f1508 : H a 48450738361639 := seed 1124469327 rfl
lemma f1509 : H a 0xa41251249527 := seed 4346481231 rfl
lemma f1510 : H a 0xa822c2292527 := seed 4464052814 rfl
lemma f1511 : H a 27951212839 := seed 184908 rfl
lemma f1512 : H a 27934431527 := seed 184909 rfl
lemma f1513 : H a 26877733159 := seed 315980 rfl
lemma f1514 : H a 20436855079 := seed 1102412 rfl
lemma f1515 : H a 20420073767 := seed 1102413 rfl
lemma f1516 : H a 11849017639 := seed 2150988 rfl
lemma f1517 : H a 19614964007 := seed 1200717 rfl
lemma f1518 : H a 9953646887 := seed 2380365 rfl
lemma f1519 : H a 48450738362663 := seed 1124471375 rfl
lemma f1520 : H a 0x6824c248a927 := seed 1227100750 rfl
lemma f1521 : H a 40819332647 := seed 183373 rfl
lemma f1522 : H a 39762634279 := seed 314444 rfl
lemma f1523 : H a 37598893607 := seed 576589 rfl
lemma f1524 : H a 5662873127 := seed 4475981 rfl
lemma f1525 : H a 0x81a11a05a627 := seed 4966108238 rfl
lemma f1526 : H a 27010127205927 := seed 704924751 rfl
lemma f1527 : H a 27560017237543 := seed 688163919 rfl
lemma f1528 : H a 0x911151119627 := seed 4446522447 rfl
lemma f1529 : H a 30858552317479 := seed 587598927 rfl
lemma f1530 : H a 0x9418c1849627 := seed 826412111 rfl
lemma f1531 : H a 23656245799 := seed 185420 rfl
lemma f1532 : H a 22582766119 := seed 316492 rfl
lemma f1533 : H a 22565984807 := seed 316493 rfl
lemma f1534 : H a 20435806759 := seed 578636 rfl
lemma f1535 : H a 19613915687 := seed 676941 rfl
lemma f1536 : H a 5658679847 := seed 2380877 rfl
lemma f1537 : H a 27010127206951 := seed 704926799 rfl
lemma f1538 : H a 30860700326439 := seed 319427663 rfl
lemma f1539 : H a 92433351481895 := seed 2198475855 rfl
lemma f1540 : H a 92435230530087 := seed 2433356879 rfl
lemma f1541 : H a 96914096302631 := seed 589567054 rfl
lemma f1542 : H a 15049530407 := seed 186445 rfl
lemma f1543 : H a 11845872679 := seed 579660 rfl
lemma f1544 : H a 11829091367 := seed 579661 rfl
lemma f1545 : H a 6730062887 := seed 1202253 rfl
lemma f1546 : H a 9967283239 := seed 809036 rfl
lemma f1547 : H a 9950501927 := seed 809037 rfl
lemma f1548 : H a 5673364519 := seed 1333324 rfl
lemma f1549 : H a 27560017239079 := seed 688166991 rfl
lemma f1550 : H a 45152203283495 := seed 1225037903 rfl
lemma f1551 : H a 30858552319015 := seed 587601999 rfl
lemma f1552 : H a 48450738363431 := seed 1124472911 rfl
lemma f1553 : H a 48523501153319 := seed 1627789390 rfl
lemma f1554 : H a 48454764895271 := seed 1627789391 rfl
lemma f1555 : H a 57248979393575 := seed 1124735055 rfl
lemma f1556 : H a 57250858441767 := seed 1359616079 rfl
lemma f1557 : H a 61648905215015 := seed 1225529423 rfl
lemma f1558 : H a 61717641505831 := seed 1242306638 rfl
lemma f1559 : H a 61653201230887 := seed 689182799 rfl
lemma f1560 : H a 60146553287 := seed 115597 rfl
lemma f1561 : H a 18029257159 := seed 5260172 rfl
lemma f1562 : H a 9441419719 := seed 6308748 rfl
lemma f1563 : H a 0x8192190391c7 := seed 5435868047 rfl
lemma f1564 : H a 0x8292290391c7 := seed 5402346383 rfl
lemma f1565 : H a 0x8294290391c7 := seed 6476088207 rfl
lemma f1566 : H a 0xc098298191c7 := seed 2252358543 rfl
lemma f1567 : H a 0x8314310391c7 := seed 6459327375 rfl
lemma f1568 : H a 0xa112312191c7 := seed 4379935631 rfl
lemma f1569 : H a 0xc118318191c7 := seed 2235597711 rfl
lemma f1570 : H a 0xc11a118191c7 := seed 3242230671 rfl
lemma f1571 : H a 0xa2283282a1c7 := seed 1128334222 rfl
lemma f1572 : H a 55851586247 := seed 116109 rfl
lemma f1573 : H a 0x8191190392c7 := seed 4898997647 rfl
lemma f1574 : H a 0x8291290392c7 := seed 4865475983 rfl
lemma f1575 : H a 0x8294290392c7 := seed 6476088719 rfl
lemma f1576 : H a 0x8311310392c7 := seed 4848715151 rfl
lemma f1577 : H a 0xc2283282a2c7 := seed 2202076558 rfl
lemma f1578 : H a 0xc218318292c7 := seed 2202076559 rfl
lemma f1579 : H a 0xd029229122c7 := seed 2252866958 rfl
lemma f1580 : H a 47261652167 := seed 117133 rfl
lemma f1581 : H a 13463823559 := seed 4245900 rfl
lemma f1582 : H a 38958965959 := seed 1132940 rfl
lemma f1583 : H a 13195453639 := seed 4278668 rfl
lemma f1584 : H a 9438274759 := seed 4737420 rfl
lemma f1585 : H a 5127574727 := seed 5261709 rfl
lemma f1586 : H a 0x8191190394c7 := seed 4898998671 rfl
lemma f1587 : H a 0x8192190394c7 := seed 5435869583 rfl
lemma f1588 : H a 0x81a21a11a4c7 := seed 5905631630 rfl
lemma f1589 : H a 0x8291290394c7 := seed 4865477007 rfl
lemma f1590 : H a 0x8292290394c7 := seed 5402347919 rfl
lemma f1591 : H a 0x82a22a12a4c7 := seed 5905664398 rfl
lemma f1592 : H a 53404313425095 := seed 638601615 rfl
lemma f1593 : H a 0xa098298194c7 := seed 1178618255 rfl
lemma f1594 : H a 0x9113111194c7 := seed 5386045839 rfl
lemma f1595 : H a 53954203456711 := seed 621840783 rfl
lemma f1596 : H a 0xa119118314c7 := seed 1681951119 rfl
lemma f1597 : H a 55118155392199 := seed 1124665742 rfl
lemma f1598 : H a 0x92283282a4c7 := seed 591464846 rfl
lemma f1599 : H a 0xa2283282a4c7 := seed 1128335758 rfl
lemma f1600 : H a 0xa218318294c7 := seed 1128335759 rfl
end BorsukCert

namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f1601 : H a 0xb0291290a4c7 := seed 1128794510 rfl
lemma f1602 : H a 30081784007 := seed 119181 rfl
lemma f1603 : H a 38006853703879 := seed 1644253583 rfl
lemma f1604 : H a 0x6216116098c7 := seed 120590735 rfl
lemma f1605 : H a 53704102727 := seed 116365 rfl
lemma f1606 : H a 52093883207 := seed 312973 rfl
lemma f1607 : H a 37081948999 := seed 2147980 rfl
lemma f1608 : H a 19906274119 := seed 4245132 rfl
lemma f1609 : H a 19889492807 := seed 4245133 rfl
lemma f1610 : H a 51842294599 := seed 345740 rfl
lemma f1611 : H a 19637904199 := seed 4277900 rfl
lemma f1612 : H a 35203359559 := seed 2377356 rfl
lemma f1613 : H a 35186578247 := seed 2377357 rfl
lemma f1614 : H a 18010903367 := seed 4474509 rfl
lemma f1615 : H a 2982187847 := seed 6309517 rfl
lemma f1616 : H a 0x819099039347 := seed 4630562447 rfl
lemma f1617 : H a 0x819419039347 := seed 6509610639 rfl
lemma f1618 : H a 0x8290a9039347 := seed 4597040783 rfl
lemma f1619 : H a 0x829429039347 := seed 6476088975 rfl
lemma f1620 : H a 0x88a82a81a347 := seed 373311118 rfl
lemma f1621 : H a 0xc0a82a81a347 := seed 2252359310 rfl
lemma f1622 : H a 0xc09889819347 := seed 2453685903 rfl
lemma f1623 : H a 0x8310b1039347 := seed 4580279951 rfl
lemma f1624 : H a 0x831431039347 := seed 6459328143 rfl
lemma f1625 : H a 81504286450503 := seed 2198144654 rfl
lemma f1626 : H a 0x8a283282a347 := seed 323028622 rfl
lemma f1627 : H a 0xc2283282a347 := seed 2202076814 rfl
lemma f1628 : H a 81452197253959 := seed 119801487 rfl
lemma f1629 : H a 0xc824a248a347 := seed 4381214350 rfl
lemma f1630 : H a 45114168647 := seed 117389 rfl
lemma f1631 : H a 43503949127 := seed 313997 rfl
lemma f1632 : H a 9437750599 := seed 4475532 rfl
lemma f1633 : H a 36904926156103 := seed 1409337999 rfl
lemma f1634 : H a 0x819099039547 := seed 4630563471 rfl
lemma f1635 : H a 0x819219039547 := seed 5435869839 rfl
lemma f1636 : H a 0x8290a9039547 := seed 4597041807 rfl
lemma f1637 : H a 0x829229039547 := seed 5402348175 rfl
lemma f1638 : H a 0x8892890a9547 := seed 5436099215 rfl
lemma f1639 : H a 0xa09289229547 := seed 4631579279 rfl
lemma f1640 : H a 0x889829819547 := seed 373312143 rfl
lemma f1641 : H a 0x891831819547 := seed 356551311 rfl
lemma f1642 : H a 0xa11891819547 := seed 1363184271 rfl
lemma f1643 : H a 0xa2283282a547 := seed 1128336014 rfl
lemma f1644 : H a 19899984199 := seed 1102476 rfl
lemma f1645 : H a 19614832967 := seed 1135245 rfl
lemma f1646 : H a 9433557319 := seed 2380428 rfl
lemma f1647 : H a 9416776007 := seed 2380429 rfl
lemma f1648 : H a 81504286452039 := seed 2198147726 rfl
lemma f1649 : H a 0x6822a228a947 := seed 2232685198 rfl
lemma f1650 : H a 81452197255495 := seed 119804559 rfl
lemma f1651 : H a 40819201607 := seed 117901 rfl
lemma f1652 : H a 38940612167 := seed 347277 rfl
lemma f1653 : H a 6753003079 := seed 4279436 rfl
lemma f1654 : H a 6736221767 := seed 4279437 rfl
lemma f1655 : H a 0x819119039647 := seed 4898999439 rfl
lemma f1656 : H a 0x8290a9039647 := seed 4597042319 rfl
lemma f1657 : H a 0x829129039647 := seed 4865477775 rfl
lemma f1658 : H a 0x831131039647 := seed 4848716943 rfl
lemma f1659 : H a 0x8a1831829647 := seed 323030159 rfl
lemma f1660 : H a 0x92283282a647 := seed 591465614 rfl
lemma f1661 : H a 28662751073863 := seed 118230159 rfl
lemma f1662 : H a 0x921911909647 := seed 122162319 rfl
lemma f1663 : H a 0x982922912647 := seed 373820558 rfl
lemma f1664 : H a 23639333447 := seed 119949 rfl
lemma f1665 : H a 19898935879 := seed 578700 rfl
lemma f1666 : H a 21777525319 := seed 349324 rfl
lemma f1667 : H a 19630565959 := seed 611468 rfl
lemma f1668 : H a 19613784647 := seed 611469 rfl
lemma f1669 : H a 6748809799 := seed 2184332 rfl
lemma f1670 : H a 5138590279 := seed 2380940 rfl
lemma f1671 : H a 5121808967 := seed 2380941 rfl
lemma f1672 : H a 19312740112967 := seed 872469647 rfl
lemma f1673 : H a 20412520176199 := seed 838947983 rfl
lemma f1674 : H a 73191225793095 := seed 2717996175 rfl
lemma f1675 : H a 88654736370247 := seed 2450019470 rfl
lemma f1676 : H a 88654736435783 := seed 2483573902 rfl
lemma f1677 : H a 88586000177735 := seed 2483573903 rfl
lemma f1678 : H a 89135890143815 := seed 2433258639 rfl
lemma f1679 : H a 28729876326983 := seed 319362190 rfl
lemma f1680 : H a 90302527482439 := seed 2198410382 rfl
lemma f1681 : H a 81452197255751 := seed 119805071 rfl
lemma f1682 : H a 96914364738119 := seed 623121550 rfl
lemma f1683 : H a 96914364770887 := seed 639898766 rfl
lemma f1684 : H a 15049399367 := seed 120973 rfl
lemma f1685 : H a 11309001799 := seed 579724 rfl
lemma f1686 : H a 13170809927 := seed 350349 rfl
lemma f1687 : H a 11023850567 := seed 612493 rfl
lemma f1688 : H a 6729931847 := seed 1136781 rfl
lemma f1689 : H a 20412520176711 := seed 838949007 rfl
lemma f1690 : H a 38004706221127 := seed 1375819919 rfl
lemma f1691 : H a 38006853704775 := seed 1644255375 rfl
lemma f1692 : H a 45220402670663 := seed 1157929102 rfl
lemma f1693 : H a 53951518055495 := seed 1359517839 rfl
lemma f1694 : H a 54022939716679 := seed 621844622 rfl
lemma f1695 : H a 28662751075399 := seed 118233231 rfl
lemma f1696 : H a 52630360967 := seed 116493 rfl
lemma f1697 : H a 0x819059039387 := seed 4496344847 rfl
lemma f1698 : H a 0x829069039387 := seed 4462823183 rfl
lemma f1699 : H a 0x829429039387 := seed 6476089103 rfl
lemma f1700 : H a 0xc09829819387 := seed 2252359439 rfl
lemma f1701 : H a 0xc11831819387 := seed 2235598607 rfl
lemma f1702 : H a 0x86283282a387 := seed 188811022 rfl
lemma f1703 : H a 44040426887 := seed 117517 rfl
lemma f1704 : H a 43503687047 := seed 183053 rfl
lemma f1705 : H a 36006110599 := seed 1100556 rfl
lemma f1706 : H a 10225816967 := seed 4246285 rfl
lemma f1707 : H a 43252098439 := seed 215820 rfl
lemma f1708 : H a 43235317127 := seed 215821 rfl
lemma f1709 : H a 9974228359 := seed 4279052 rfl
lemma f1710 : H a 35201000839 := seed 1198860 rfl
lemma f1711 : H a 35184219527 := seed 1198861 rfl
lemma f1712 : H a 1906349447 := seed 5262093 rfl
lemma f1713 : H a 0x819219039587 := seed 5435869967 rfl
lemma f1714 : H a 0x81a21a05a587 := seed 5502978830 rfl
lemma f1715 : H a 38003632477575 := seed 1241598735 rfl
lemma f1716 : H a 0x829069039587 := seed 4462824207 rfl
lemma f1717 : H a 0x829229039587 := seed 5402348303 rfl
lemma f1718 : H a 0x82a22a06a587 := seed 5503011598 rfl
lemma f1719 : H a 40271392122247 := seed 1174555406 rfl
lemma f1720 : H a 0x849069059587 := seed 4395780879 rfl
lemma f1721 : H a 0x84a82a81a587 := seed 239094542 rfl
lemma f1722 : H a 0xa0a82a81a587 := seed 1178618638 rfl
lemma f1723 : H a 38553522509191 := seed 1224837903 rfl
lemma f1724 : H a 0x831071039587 := seed 4446063375 rfl
lemma f1725 : H a 0x831231039587 := seed 5385587471 rfl
lemma f1726 : H a 40821282153863 := seed 1157794574 rfl
lemma f1727 : H a 0x85207205a587 := seed 4379020046 rfl
lemma f1728 : H a 0x851251059587 := seed 5385653007 rfl
lemma f1729 : H a 0x851251071587 := seed 5435984655 rfl
lemma f1730 : H a 0xa1223221a587 := seed 4379937550 rfl
lemma f1731 : H a 0xa11231219587 := seed 4379937551 rfl
lemma f1732 : H a 0xa1285281a587 := seed 1228966670 rfl
lemma f1733 : H a 0xa11851831587 := seed 1279298319 rfl
lemma f1734 : H a 0x86207206a587 := seed 4345498382 rfl
lemma f1735 : H a 0x861071069587 := seed 4345498383 rfl
lemma f1736 : H a 0x861261069587 := seed 5385685775 rfl
lemma f1737 : H a 0x86283282a587 := seed 188812046 rfl
lemma f1738 : H a 0xa21831829587 := seed 1128336143 rfl
lemma f1739 : H a 41860112618887 := seed 118622991 rfl
lemma f1740 : H a 0xa4226224a587 := seed 4380035854 rfl
lemma f1741 : H a 0xa42a12a0a587 := seed 189795086 rfl
lemma f1742 : H a 26860558727 := seed 119565 rfl
lemma f1743 : H a 10238404999 := seed 2151180 rfl
lemma f1744 : H a 9416513927 := seed 2249485 rfl
lemma f1745 : H a 38003632478599 := seed 1241600783 rfl
lemma f1746 : H a 40821282154887 := seed 1157796622 rfl
lemma f1747 : H a 41860112619911 := seed 118625039 rfl
lemma f1748 : H a 0x621611609987 := seed 120591119 rfl
lemma f1749 : H a 39745459847 := seed 118029 rfl
lemma f1750 : H a 35988280967 := seed 576781 rfl
lemma f1751 : H a 38940350087 := seed 216333 rfl
lemma f1752 : H a 5679261319 := seed 4279564 rfl
lemma f1753 : H a 35199952519 := seed 675084 rfl
lemma f1754 : H a 35183171207 := seed 675085 rfl
lemma f1755 : H a 0x819059039687 := seed 4496346383 rfl
lemma f1756 : H a 0x819119039687 := seed 4898999567 rfl
lemma f1757 : H a 0x829069039687 := seed 4462824719 rfl
lemma f1758 : H a 0x829129039687 := seed 4865477903 rfl
lemma f1759 : H a 0x82a12a06a687 := seed 4966141198 rfl
lemma f1760 : H a 0x84a82a81a687 := seed 239095054 rfl
lemma f1761 : H a 0x849829819687 := seed 239095055 rfl
lemma f1762 : H a 0x90a82a81a687 := seed 641748238 rfl
lemma f1763 : H a 0x831071039687 := seed 4446063887 rfl
lemma f1764 : H a 0x831131039687 := seed 4848717071 rfl
lemma f1765 : H a 0x851151071687 := seed 4899114255 rfl
lemma f1766 : H a 0x911151119687 := seed 4446522639 rfl
lemma f1767 : H a 24331829814919 := seed 185142542 rfl
lemma f1768 : H a 0x92213212a687 := seed 4345892110 rfl
lemma f1769 : H a 0x86283282a687 := seed 188812558 rfl
lemma f1770 : H a 0x861831829687 := seed 188812559 rfl
lemma f1771 : H a 0x921861829687 := seed 692129039 rfl
lemma f1772 : H a 24263630558855 := seed 118099215 rfl
lemma f1773 : H a 0x861851849687 := seed 121769231 rfl
lemma f1774 : H a 0x94286284a687 := seed 625085710 rfl
lemma f1775 : H a 0x94291290a687 := seed 189271310 rfl
lemma f1776 : H a 22565591687 := seed 120077 rfl
lemma f1777 : H a 18825194119 := seed 578828 rfl
lemma f1778 : H a 5658286727 := seed 2184461 rfl
lemma f1779 : H a 18020084359 := seed 677132 rfl
lemma f1780 : H a 20411446434439 := seed 704730383 rfl
lemma f1781 : H a 13975657607 := seed 121101 rfl
lemma f1782 : H a 13455699079 := seed 186636 rfl
lemma f1783 : H a 10235260039 := seed 579852 rfl
lemma f1784 : H a 10218478727 := seed 579853 rfl
lemma f1785 : H a 5941341319 := seed 1104140 rfl
lemma f1786 : H a 5924560007 := seed 1104141 rfl
lemma f1787 : H a 13170547847 := seed 219405 rfl
lemma f1788 : H a 9966890119 := seed 612620 rfl
lemma f1789 : H a 5672971399 := seed 1136908 rfl
lemma f1790 : H a 5656190087 := seed 1136909 rfl
lemma f1791 : H a 9413368967 := seed 678157 rfl
lemma f1792 : H a 5136231559 := seed 1202444 rfl
lemma f1793 : H a 1899011207 := seed 1595661 rfl
lemma f1794 : H a 19311666371719 := seed 738253071 rfl
lemma f1795 : H a 36903852416135 := seed 1275123983 rfl
lemma f1796 : H a 36907073641607 := seed 1677777167 rfl
lemma f1797 : H a 36975810030727 := seed 1744886030 rfl
lemma f1798 : H a 20411446434951 := seed 704731407 rfl
lemma f1799 : H a 38006853704839 := seed 1644255503 rfl
lemma f1800 : H a 22682428091527 := seed 235428110 rfl
lemma f1801 : H a 53400554282119 := seed 1242061071 rfl
lemma f1802 : H a 40278910151815 := seed 235952398 rfl
lemma f1803 : H a 53404850363527 := seed 739268879 rfl
lemma f1804 : H a 38556743736455 := seed 1627494671 rfl
lemma f1805 : H a 40821282155655 := seed 1157798158 rfl
lemma f1806 : H a 23232318123143 := seed 218667278 rfl
lemma f1807 : H a 23163581865095 := seed 218667279 rfl
lemma f1808 : H a 54022939716743 := seed 621844750 rfl
lemma f1809 : H a 55118155394183 := seed 1124669710 rfl
lemma f1810 : H a 41859575618695 := seed 185669903 rfl
lemma f1811 : H a 55122451410055 := seed 588323086 rfl
lemma f1812 : H a 55054520458375 := seed 688986383 rfl
lemma f1813 : H a 55054520491143 := seed 705763599 rfl
lemma f1814 : H a 57317984087175 := seed 1158289678 rfl
lemma f1815 : H a 57317984119943 := seed 1175066894 rfl
lemma f1816 : H a 57322280103047 := seed 621943054 rfl
lemma f1817 : H a 57322280135815 := seed 638720270 rfl
lemma f1818 : H a 57325502114951 := seed 219683086 rfl
lemma f1819 : H a 57325502147719 := seed 236460302 rfl
lemma f1820 : H a 3514996487 := seed 4279821 rfl
lemma f1821 : H a 0x819059039707 := seed 4496346639 rfl
lemma f1822 : H a 0x819099039707 := seed 4630564367 rfl
lemma f1823 : H a 0x829069039707 := seed 4462824975 rfl
lemma f1824 : H a 0x889829819707 := seed 373313039 rfl
lemma f1825 : H a 0xd1071059707 := seed 352488975 rfl
lemma f1826 : H a 0x891831819707 := seed 356552207 rfl
lemma f1827 : H a 0x86207206a707 := seed 4345499150 rfl
lemma f1828 : H a 19898149639 := seed 185868 rfl
lemma f1829 : H a 19881368327 := seed 185869 rfl
lemma f1830 : H a 3510803207 := seed 2184717 rfl
lemma f1831 : H a 1917364999 := seed 2381324 rfl
lemma f1832 : H a 81452197255943 := seed 119805455 rfl
lemma f1833 : H a 83720225237767 := seed 237245966 rfl
lemma f1834 : H a 11828174087 := seed 121357 rfl
lemma f1835 : H a 11308215559 := seed 186892 rfl
lemma f1836 : H a 10234735879 := seed 317964 rfl
lemma f1837 : H a 2988748039 := seed 1202700 rfl
lemma f1838 : H a 36904926158087 := seed 1409341967 rfl
lemma f1839 : H a 38004706221319 := seed 1375820303 rfl
lemma f1840 : H a 38073442675975 := seed 1476483598 rfl
lemma f1841 : H a 0xd1071059d07 := seed 352492047 rfl
lemma f1842 : H a 41853936639239 := seed 1359157775 rfl
lemma f1843 : H a 0xe10d10c9d07 := seed 117840399 rfl
lemma f1844 : H a 41860112620807 := seed 118626831 rfl
lemma f1845 : H a 7533207047 := seed 121869 rfl
lemma f1846 : H a 6996467207 := seed 187405 rfl
lemma f1847 : H a 2970918407 := seed 678925 rfl
lemma f1848 : H a 20412520177159 := seed 838949903 rfl
lemma f1849 : H a 23161970564615 := seed 872586255 rfl
lemma f1850 : H a 60164694139 := seed 794868 rfl
lemma f1851 : H a 60147912827 := seed 794869 rfl
lemma f1852 : H a 47282937979 := seed 2367732 rfl
lemma f1853 : H a 47266156667 := seed 2367733 rfl
lemma f1854 : H a 53707034747 := seed 1581301 rfl
lemma f1855 : H a 45135978619 := seed 2629876 rfl
lemma f1856 : H a 27960303739 := seed 4727028 rfl
lemma f1857 : H a 27943522427 := seed 4727029 rfl
lemma f1858 : H a 40825278587 := seed 3154165 rfl
lemma f1859 : H a 0x90630618607b := seed 5637677302 rfl
lemma f1860 : H a 0x68138128507b := seed 2694054135 rfl
lemma f1861 : H a 0xc8258248607b := seed 4842586358 rfl
lemma f1862 : H a 0xc8158148507b := seed 4842586359 rfl
lemma f1863 : H a 0xc8198188507b := seed 2697199863 rfl
lemma f1864 : H a 0xe02d02c0607b := seed 1625293046 rfl
lemma f1865 : H a 60164432059 := seed 663924 rfl
lemma f1866 : H a 60147650747 := seed 663925 rfl
lemma f1867 : H a 30090219707 := seed 4333941 rfl
lemma f1868 : H a 22575861947 := seed 5251445 rfl
lemma f1869 : H a 14004805819 := seed 6300020 rfl
lemma f1870 : H a 0xc059058450bb := seed 2822775159 rfl
lemma f1871 : H a 0xa423422460bb := seed 4841406838 rfl
lemma f1872 : H a 0xa413412450bb := seed 4841406839 rfl
lemma f1873 : H a 0xa416412450bb := seed 6452019575 rfl
lemma f1874 : H a 0xa419418450bb := seed 1623327095 rfl
lemma f1875 : H a 0xc41a418450bb := seed 3233939831 rfl
lemma f1876 : H a 0xb01a41a050bb := seed 684720503 rfl
lemma f1877 : H a 60163907899 := seed 402036 rfl
lemma f1878 : H a 60147126587 := seed 402037 rfl
lemma f1879 : H a 53723029819 := seed 1188468 rfl
lemma f1880 : H a 53706248507 := seed 1188469 rfl
lemma f1881 : H a 27942736187 := seed 4334197 rfl
lemma f1882 : H a 52649550139 := seed 1319540 rfl
lemma f1883 : H a 44061712699 := seed 2368116 rfl
lemma f1884 : H a 44044931387 := seed 2368117 rfl
lemma f1885 : H a 26869256507 := seed 4465269 rfl
lemma f1886 : H a 20428378427 := seed 5251701 rfl
lemma f1887 : H a 55868940859 := seed 402548 rfl
lemma f1888 : H a 55852159547 := seed 402549 rfl
lemma f1889 : H a 53705200187 := seed 664693 rfl
lemma f1890 : H a 40823444027 := seed 2237557 rfl
lemma f1891 : H a 39749964347 := seed 2368629 rfl
lemma f1892 : H a 37619786299 := seed 2630772 rfl
lemma f1893 : H a 20444111419 := seed 4727924 rfl
lemma f1894 : H a 7545573947 := seed 6300789 rfl
lemma f1895 : H a 88323943322171 := seed 941630583 rfl
lemma f1896 : H a 0xc0590584523b := seed 2822775927 rfl
lemma f1897 : H a 0x9421c214623b := seed 4572447862 rfl
lemma f1898 : H a 0xc4254244623b := seed 4842456182 rfl
lemma f1899 : H a 0x98258218623b := seed 6451627126 rfl
lemma f1900 : H a 96914901590587 := seed 681837686 rfl
lemma f1901 : H a 96846165332539 := seed 681837687 rfl
lemma f1902 : H a 0xc8258248623b := seed 4842587254 rfl
lemma f1903 : H a 0xc8158148523b := seed 4842587255 rfl
lemma f1904 : H a 0xc8198188523b := seed 2697200759 rfl
lemma f1905 : H a 0x98194190523b := seed 415761527 rfl
lemma f1906 : H a 0xd0194190523b := seed 2294809719 rfl
lemma f1907 : H a 0xd01c81c0523b := seed 819987575 rfl
lemma f1908 : H a 47279006779 := seed 403572 rfl
lemma f1909 : H a 47262225467 := seed 403573 rfl
lemma f1910 : H a 45115266107 := seed 665717 rfl
lemma f1911 : H a 40821347387 := seed 1190005 rfl
lemma f1912 : H a 44058567739 := seed 796788 rfl
lemma f1913 : H a 44041786427 := seed 796789 rfl
lemma f1914 : H a 14001136699 := seed 4466804 rfl
lemma f1915 : H a 11837396027 := seed 4728949 rfl
lemma f1916 : H a 53126683186235 := seed 1476929655 rfl
lemma f1917 : H a 0x8c21c20c643b := seed 4840622198 rfl
lemma f1918 : H a 0x9421c214643b := seed 4572448886 rfl
lemma f1919 : H a 0x94234214643b := seed 5377755254 rfl
lemma f1920 : H a 0xa4234224643b := seed 4841408630 rfl
lemma f1921 : H a 0xa4134124543b := seed 4841408631 rfl
lemma f1922 : H a 0xa4194184543b := seed 1623328887 rfl
lemma f1923 : H a 0xb01a41a0543b := seed 684722295 rfl
lemma f1924 : H a 30099138619 := seed 405620 rfl
lemma f1925 : H a 27952179259 := seed 667764 rfl
lemma f1926 : H a 27935397947 := seed 667765 rfl
lemma f1927 : H a 23658260539 := seed 1192052 rfl
lemma f1928 : H a 23641479227 := seed 1192053 rfl
lemma f1929 : H a 26861918267 := seed 798837 rfl
lemma f1930 : H a 13996943419 := seed 2371700 rfl
lemma f1931 : H a 13980162107 := seed 2371701 rfl
lemma f1932 : H a 20437821499 := seed 1585268 rfl
lemma f1933 : H a 20421040187 := seed 1585269 rfl
lemma f1934 : H a 11833202747 := seed 2633845 rfl
lemma f1935 : H a 7556065339 := seed 3158132 rfl
lemma f1936 : H a 7539284027 := seed 3158133 rfl
lemma f1937 : H a 39931469387835 := seed 1879191671 rfl
lemma f1938 : H a 75120136968251 := seed 3758239863 rfl
lemma f1939 : H a 53126683187259 := seed 1476931703 rfl
lemma f1940 : H a 88323943323707 := seed 941633655 rfl
lemma f1941 : H a 57319594682427 := seed 1351225462 rfl
lemma f1942 : H a 57250858424379 := seed 1351225463 rfl
lemma f1943 : H a 92503966771259 := seed 2424967286 rfl
lemma f1944 : H a 57323890698299 := seed 814878838 rfl
lemma f1945 : H a 57255154440251 := seed 814878839 rfl
lemma f1946 : H a 0x64234224683b := seed 2693927030 rfl
lemma f1947 : H a 0x64134124583b := seed 2693927031 rfl
lemma f1948 : H a 96914901592123 := seed 681840758 rfl
lemma f1949 : H a 0x6814c148583b := seed 1218711671 rfl
lemma f1950 : H a 0x68258248683b := seed 1621364854 rfl
lemma f1951 : H a 55870382299 := seed 1122740 rfl
lemma f1952 : H a 0xb013213050db := seed 4372038071 rfl
lemma f1953 : H a 53722898779 := seed 1122996 rfl
lemma f1954 : H a 27942605147 := seed 4268725 rfl
lemma f1955 : H a 0xc0588582515b := seed 2487231159 rfl
lemma f1956 : H a 0xc814a148515b := seed 4372824759 rfl
lemma f1957 : H a 0xe01c81c2115b := seed 1415578295 rfl
lemma f1958 : H a 53705069147 := seed 599221 rfl
lemma f1959 : H a 23647638107 := seed 4269237 rfl
lemma f1960 : H a 0xc8258248625b := seed 4842587318 rfl
lemma f1961 : H a 0xd0258252225b := seed 4633134262 rfl
lemma f1962 : H a 40837997659 := seed 1124532 rfl
lemma f1963 : H a 15074485339 := seed 4270260 rfl
lemma f1964 : H a 0xa819818a145b := seed 1682180279 rfl
lemma f1965 : H a 0xb0132130545b := seed 4372039863 rfl
lemma f1966 : H a 0xb0138132145b := seed 4632086711 rfl
lemma f1967 : H a 23658129499 := seed 1126580 rfl
lemma f1968 : H a 23641348187 := seed 1126581 rfl
lemma f1969 : H a 13443291227 := seed 2371765 rfl
lemma f1970 : H a 19884169307 := seed 1585333 rfl
lemma f1971 : H a 96845628463195 := seed 614731959 rfl
lemma f1972 : H a 0x6824a248685b := seed 1151602870 rfl
lemma f1973 : H a 0x6815814a185b := seed 1680085175 rfl
lemma f1974 : H a 52649157019 := seed 1123124 rfl
lemma f1975 : H a 18817765787 := seed 5251893 rfl
lemma f1976 : H a 0xa0584582519b := seed 1279271735 rfl
lemma f1977 : H a 0x86146126119b := seed 7516390199 rfl
lemma f1978 : H a 0xa2186182519b := seed 1220608823 rfl
lemma f1979 : H a 0xc41a4184519b := seed 3233940279 rfl
lemma f1980 : H a 0xe01a41a0519b := seed 2295333687 rfl
lemma f1981 : H a 55868547739 := seed 206132 rfl
lemma f1982 : H a 39766352539 := seed 2172212 rfl
lemma f1983 : H a 52111368859 := seed 664884 rfl
lemma f1984 : H a 35992392347 := seed 2630965 rfl
lemma f1985 : H a 5934961307 := seed 6300981 rfl
lemma f1986 : H a 0x84514506529b := seed 4899087671 rfl
lemma f1987 : H a 0x94216214629b := seed 4371121462 rfl
lemma f1988 : H a 0x94116114529b := seed 4371121463 rfl
lemma f1989 : H a 0xd0252250629b := seed 4373087542 rfl
lemma f1990 : H a 0xd0254252229b := seed 4498916662 rfl
lemma f1991 : H a 43504653467 := seed 665909 rfl
lemma f1992 : H a 35990295707 := seed 1583413 rfl
lemma f1993 : H a 0xa0584582549b := seed 1279273271 rfl
lemma f1994 : H a 57253543826587 := seed 613550391 rfl
lemma f1995 : H a 0xa4134126149b := seed 4900129079 rfl
lemma f1996 : H a 0xa4194186149b := seed 1682049335 rfl
lemma f1997 : H a 0xb0134132149b := seed 4497869111 rfl
lemma f1998 : H a 0xb0294290649b := seed 1221069110 rfl
lemma f1999 : H a 0xb01a41a0549b := seed 684722487 rfl
lemma f2000 : H a 0xb01a41a2149b := seed 743442743 rfl
end BorsukCert

namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f2001 : H a 13996550299 := seed 2175284 rfl
lemma f2002 : H a 13979768987 := seed 2175285 rfl
lemma f2003 : H a 22047647899 := seed 1192244 rfl
lemma f2004 : H a 22030866587 := seed 1192245 rfl
lemma f2005 : H a 18810427547 := seed 1585461 rfl
lemma f2006 : H a 10239371419 := seed 2634036 rfl
lemma f2007 : H a 53129905330331 := seed 739258679 rfl
lemma f2008 : H a 57317984069787 := seed 1149899062 rfl
lemma f2009 : H a 57322280085659 := seed 613552438 rfl
lemma f2010 : H a 57253543827611 := seed 613552439 rfl
lemma f2011 : H a 57325502097563 := seed 211292470 rfl
lemma f2012 : H a 0x70154150589b := seed 1218974007 rfl
lemma f2013 : H a 53721064219 := seed 206388 rfl
lemma f2014 : H a 20426412827 := seed 4269621 rfl
lemma f2015 : H a 0xc0588582531b := seed 2487232055 rfl
lemma f2016 : H a 81520127795995 := seed 413206070 rfl
lemma f2017 : H a 0x8c24c20c631b := seed 6451234358 rfl
lemma f2018 : H a 0xc424c244631b := seed 4574021174 rfl
lemma f2019 : H a 0xc814a148531b := seed 4372825655 rfl
lemma f2020 : H a 0xc814c148531b := seed 4439934519 rfl
lemma f2021 : H a 43504129307 := seed 404021 rfl
lemma f2022 : H a 0xa0584582551b := seed 1279273527 rfl
lemma f2023 : H a 0x8612610e151b := seed 5637343799 rfl
lemma f2024 : H a 0xa2286282651b := seed 1220610614 rfl
lemma f2025 : H a 0xa418c184551b := seed 1354893879 rfl
lemma f2026 : H a 0xa81a41a0551b := seed 416287287 rfl
lemma f2027 : H a 26861000987 := seed 340533 rfl
lemma f2028 : H a 20436904219 := seed 1126964 rfl
lemma f2029 : H a 20420122907 := seed 1126965 rfl
lemma f2030 : H a 19883383067 := seed 1192501 rfl
lemma f2031 : H a 10222065947 := seed 2372149 rfl
lemma f2032 : H a 44402548566299 := seed 470823478 rfl
lemma f2033 : H a 0x60624622691b := seed 2349871670 rfl
lemma f2034 : H a 77044751669531 := seed 3489862199 rfl
lemma f2035 : H a 81520127797531 := seed 413209142 rfl
lemma f2036 : H a 0x6412c124591b := seed 2425492023 rfl
lemma f2037 : H a 0x6814c148591b := seed 1218712119 rfl
lemma f2038 : H a 39762683419 := seed 338996 rfl
lemma f2039 : H a 35988723227 := seed 797749 rfl
lemma f2040 : H a 0x8611610e161b := seed 5100473399 rfl
lemma f2041 : H a 0x94216214661b := seed 4371123254 rfl
lemma f2042 : H a 0x94116114561b := seed 4371123255 rfl
lemma f2043 : H a 0x98294290661b := seed 415763510 rfl
lemma f2044 : H a 23656294939 := seed 209972 rfl
lemma f2045 : H a 22566033947 := seed 341045 rfl
lemma f2046 : H a 20435855899 := seed 603188 rfl
lemma f2047 : H a 7537318427 := seed 2176053 rfl
lemma f2048 : H a 19882334747 := seed 668725 rfl
lemma f2049 : H a 5927098907 := seed 2372661 rfl
lemma f2050 : H a 88323943324187 := seed 941634615 rfl
lemma f2051 : H a 77040456702491 := seed 2952991799 rfl
lemma f2052 : H a 30929705003547 := seed 344593462 rfl
lemma f2053 : H a 92502356159003 := seed 2223641654 rfl
lemma f2054 : H a 92435230513691 := seed 2424968247 rfl
lemma f2055 : H a 96845628463643 := seed 614732855 rfl
lemma f2056 : H a 96846165334555 := seed 681841719 rfl
lemma f2057 : H a 13976099867 := seed 342069 rfl
lemma f2058 : H a 7552003099 := seed 1128500 rfl
lemma f2059 : H a 7535221787 := seed 1128501 rfl
lemma f2060 : H a 7015263259 := seed 1194036 rfl
lemma f2061 : H a 6998481947 := seed 1194037 rfl
lemma f2062 : H a 10235702299 := seed 800820 rfl
lemma f2063 : H a 37798497643547 := seed 1476474934 rfl
lemma f2064 : H a 37800645389339 := seed 1879128118 rfl
lemma f2065 : H a 53129905331227 := seed 739260471 rfl
lemma f2066 : H a 57317984070683 := seed 1149900854 rfl
lemma f2067 : H a 57249247812635 := seed 1149900855 rfl
lemma f2068 : H a 57250858425371 := seed 1351227447 rfl
lemma f2069 : H a 57322280086555 := seed 613554230 rfl
lemma f2070 : H a 57253543828507 := seed 613554231 rfl
lemma f2071 : H a 61648905198619 := seed 1217140791 rfl
lemma f2072 : H a 57325502098459 := seed 211294262 rfl
lemma f2073 : H a 61655349337115 := seed 471341111 rfl
lemma f2074 : H a 55870316779 := seed 1090004 rfl
lemma f2075 : H a 88386233786603 := seed 3255312854 rfl
lemma f2076 : H a 0xd015115050eb := seed 4339532247 rfl
lemma f2077 : H a 0xd017015050eb := seed 5379719639 rfl
lemma f2078 : H a 0xb019119050eb := seed 1120403927 rfl
lemma f2079 : H a 0xe01d01c050eb := seed 1625293271 rfl
lemma f2080 : H a 53706051947 := seed 1090261 rfl
lemma f2081 : H a 27942539627 := seed 4235989 rfl
lemma f2082 : H a 51827462507 := seed 1319637 rfl
lemma f2083 : H a 0xc8149148516b := seed 4339270359 rfl
lemma f2084 : H a 0xc8268248616b := seed 5379457750 rfl
lemma f2085 : H a 0xc8168149116b := seed 5404623575 rfl
lemma f2086 : H a 0xc81a8188516b := seed 3234071255 rfl
lemma f2087 : H a 0xe01c81c0516b := seed 1356858071 rfl
lemma f2088 : H a 55868744299 := seed 304340 rfl
lemma f2089 : H a 53721784939 := seed 566484 rfl
lemma f2090 : H a 23664353899 := seed 4236500 rfl
lemma f2091 : H a 23647572587 := seed 4236501 rfl
lemma f2092 : H a 36797698667 := seed 2630869 rfl
lemma f2093 : H a 0xc0588581526b := seed 2453677271 rfl
lemma f2094 : H a 96845360026219 := seed 581174487 rfl
lemma f2095 : H a 0xc8149148526b := seed 4339270871 rfl
lemma f2096 : H a 0xc8258248626b := seed 4842587350 rfl
lemma f2097 : H a 0xc8158148526b := seed 4842587351 rfl
lemma f2098 : H a 0xc8158149126b := seed 4867753175 rfl
lemma f2099 : H a 0xd0151150526b := seed 4339533015 rfl
lemma f2100 : H a 0xd01c81c1126b := seed 845153495 rfl
lemma f2101 : H a 47262028907 := seed 305365 rfl
lemma f2102 : H a 45131850859 := seed 567508 rfl
lemma f2103 : H a 40837932139 := seed 1091796 rfl
lemma f2104 : H a 0xb0191190546b := seed 1120405719 rfl
lemma f2105 : H a 30098942059 := seed 307412 rfl
lemma f2106 : H a 30082160747 := seed 307413 rfl
lemma f2107 : H a 27951982699 := seed 569556 rfl
lemma f2108 : H a 27935201387 := seed 569557 rfl
lemma f2109 : H a 23658063979 := seed 1093844 rfl
lemma f2110 : H a 23641282667 := seed 1093845 rfl
lemma f2111 : H a 15070226539 := seed 2142420 rfl
lemma f2112 : H a 13191637099 := seed 2371796 rfl
lemma f2113 : H a 13174855787 := seed 2371797 rfl
lemma f2114 : H a 36700865259627 := seed 1879093462 rfl
lemma f2115 : H a 36632129001579 := seed 1879093463 rfl
lemma f2116 : H a 71885237348459 := seed 2952835286 rfl
lemma f2117 : H a 71816501090411 := seed 2952835287 rfl
lemma f2118 : H a 71889532840043 := seed 3758141654 rfl
lemma f2119 : H a 71820796581995 := seed 3758141655 rfl
lemma f2120 : H a 54020254296171 := seed 1351127254 rfl
lemma f2121 : H a 89211068835947 := seed 3230175446 rfl
lemma f2122 : H a 0x68258248686b := seed 1621364950 rfl
lemma f2123 : H a 0x68258249286b := seed 1646530774 rfl
lemma f2124 : H a 60146667947 := seed 172885 rfl
lemma f2125 : H a 52632310187 := seed 1090389 rfl
lemma f2126 : H a 44044472747 := seed 2138965 rfl
lemma f2127 : H a 51827200427 := seed 1188693 rfl
lemma f2128 : H a 18549330347 := seed 5251925 rfl
lemma f2129 : H a 0xa062462161ab := seed 4463797078 rfl
lemma f2130 : H a 0xa058458151ab := seed 1245717335 rfl
lemma f2131 : H a 0xc058458151ab := seed 2319459159 rfl
lemma f2132 : H a 0xa412512451ab := seed 4338090839 rfl
lemma f2133 : H a 0xa426422461ab := seed 6452020054 rfl
lemma f2134 : H a 0xa416412451ab := seed 6452020055 rfl
lemma f2135 : H a 0xc41a418451ab := seed 3233940311 rfl
lemma f2136 : H a 0xe01a41a051ab := seed 2295333719 rfl
lemma f2137 : H a 55868482219 := seed 173396 rfl
lemma f2138 : H a 55851700907 := seed 173397 rfl
lemma f2139 : H a 52648043179 := seed 566612 rfl
lemma f2140 : H a 39766287019 := seed 2139476 rfl
lemma f2141 : H a 51826152107 := seed 664917 rfl
lemma f2142 : H a 35723956907 := seed 2630997 rfl
lemma f2143 : H a 5666525867 := seed 6301013 rfl
lemma f2144 : H a 0x8151150552ab := seed 4966098263 rfl
lemma f2145 : H a 0x8451450552ab := seed 4865533271 rfl
lemma f2146 : H a 88378717594283 := seed 2315789654 rfl
lemma f2147 : H a 88322869383851 := seed 706749783 rfl
lemma f2148 : H a 0x9128528162ab := seed 683705686 rfl
lemma f2149 : H a 0x9411511452ab := seed 4337567063 rfl
lemma f2150 : H a 47261766827 := seed 174421 rfl
lemma f2151 : H a 44058109099 := seed 567636 rfl
lemma f2152 : H a 44041327787 := seed 567637 rfl
lemma f2153 : H a 39747409067 := seed 1091925 rfl
lemma f2154 : H a 38942299307 := seed 1190229 rfl
lemma f2155 : H a 39931468928171 := seed 1644308823 rfl
lemma f2156 : H a 0x9058458154ab := seed 708847959 rfl
lemma f2157 : H a 0xa058458154ab := seed 1245718871 rfl
lemma f2158 : H a 0x9121521164ab := seed 4438133078 rfl
lemma f2159 : H a 57248979375275 := seed 1116342615 rfl
lemma f2160 : H a 0x9421521464ab := seed 4337568086 rfl
lemma f2161 : H a 0x9411511454ab := seed 4337568087 rfl
lemma f2162 : H a 0x9423421464ab := seed 5377755478 rfl
lemma f2163 : H a 0x9413411454ab := seed 5377755479 rfl
lemma f2164 : H a 0x9413411514ab := seed 5402921303 rfl
lemma f2165 : H a 57253275391147 := seed 579995991 rfl
lemma f2166 : H a 0xa412512454ab := seed 4338092375 rfl
lemma f2167 : H a 0xa423422464ab := seed 4841408854 rfl
lemma f2168 : H a 0xa413412454ab := seed 4841408855 rfl
lemma f2169 : H a 0xa429428464ab := seed 1623329110 rfl
lemma f2170 : H a 0xa429428524ab := seed 1648494934 rfl
lemma f2171 : H a 0xb023423064ab := seed 4439148886 rfl
lemma f2172 : H a 0xb013413054ab := seed 4439148887 rfl
lemma f2173 : H a 0xb019419054ab := seed 1221069143 rfl
lemma f2174 : H a 0xb029429124ab := seed 1246234966 rfl
lemma f2175 : H a 0xb01a41a054ab := seed 684722519 rfl
lemma f2176 : H a 0xb01a41a114ab := seed 709888343 rfl
lemma f2177 : H a 30098679979 := seed 176468 rfl
lemma f2178 : H a 26878240939 := seed 569684 rfl
lemma f2179 : H a 26861459627 := seed 569685 rfl
lemma f2180 : H a 22584322219 := seed 1093972 rfl
lemma f2181 : H a 22567540907 := seed 1093973 rfl
lemma f2182 : H a 13996484779 := seed 2142548 rfl
lemma f2183 : H a 13191375019 := seed 2240852 rfl
lemma f2184 : H a 18558773419 := seed 1585492 rfl
lemma f2185 : H a 71816500828331 := seed 2818617687 rfl
lemma f2186 : H a 39931468929195 := seed 1644310871 rfl
lemma f2187 : H a 88322869385387 := seed 706752855 rfl
lemma f2188 : H a 92514975770795 := seed 581046614 rfl
lemma f2189 : H a 0x6424524468ab := seed 1117917526 rfl
lemma f2190 : H a 0x6415414458ab := seed 1621234007 rfl
lemma f2191 : H a 53720998699 := seed 173652 rfl
lemma f2192 : H a 53704217387 := seed 173653 rfl
lemma f2193 : H a 20443128619 := seed 4236884 rfl
lemma f2194 : H a 20426347307 := seed 4236885 rfl
lemma f2195 : H a 19638018859 := seed 4335188 rfl
lemma f2196 : H a 35723432747 := seed 2369109 rfl
lemma f2197 : H a 18547757867 := seed 4466261 rfl
lemma f2198 : H a 3519042347 := seed 6301269 rfl
lemma f2199 : H a 75182429791019 := seed 2449614422 rfl
lemma f2200 : H a 0xc0584581532b := seed 2319459927 rfl
lemma f2201 : H a 0x8520d205632b := seed 4571956822 rfl
lemma f2202 : H a 0x85245205632b := seed 6451005014 rfl
lemma f2203 : H a 0x8c24c20d232b := seed 6476400214 rfl
lemma f2204 : H a 83651220493099 := seed 178521687 rfl
lemma f2205 : H a 0xc8149148532b := seed 4339271255 rfl
lemma f2206 : H a 0xc814c148532b := seed 4439934551 rfl
lemma f2207 : H a 0xc814c149132b := seed 4465100375 rfl
lemma f2208 : H a 0xc81c41c0532b := seed 417334871 rfl
lemma f2209 : H a 45131064619 := seed 174676 rfl
lemma f2210 : H a 11853194539 := seed 4237908 rfl
lemma f2211 : H a 0xa0584581552b := seed 1245719127 rfl
lemma f2212 : H a 0xa4125124552b := seed 4338092631 rfl
lemma f2213 : H a 0xa412c124552b := seed 4572973655 rfl
lemma f2214 : H a 0xa81a41a0552b := seed 416287319 rfl
lemma f2215 : H a 27951196459 := seed 176724 rfl
lemma f2216 : H a 27934415147 := seed 176725 rfl
lemma f2217 : H a 26877716779 := seed 307796 rfl
lemma f2218 : H a 26860935467 := seed 307797 rfl
lemma f2219 : H a 20436838699 := seed 1094228 rfl
lemma f2220 : H a 20420057387 := seed 1094229 rfl
lemma f2221 : H a 11043891499 := seed 2241108 rfl
lemma f2222 : H a 11027110187 := seed 2241109 rfl
lemma f2223 : H a 18558249259 := seed 1323604 rfl
lemma f2224 : H a 18541467947 := seed 1323605 rfl
lemma f2225 : H a 0x64145144592b := seed 1117917783 rfl
lemma f2226 : H a 48526992632107 := seed 177476182 rfl
lemma f2227 : H a 40836097579 := seed 175188 rfl
lemma f2228 : H a 39762617899 := seed 306260 rfl
lemma f2229 : H a 37615658539 := seed 568404 rfl
lemma f2230 : H a 0x90584581562b := seed 708848727 rfl
lemma f2231 : H a 0x91285281662b := seed 683707478 rfl
lemma f2232 : H a 30858552301099 := seed 579210327 rfl
lemma f2233 : H a 0x94115114562b := seed 4337568855 rfl
lemma f2234 : H a 23656229419 := seed 177236 rfl
lemma f2235 : H a 23639448107 := seed 177237 rfl
lemma f2236 : H a 22582749739 := seed 308308 rfl
lemma f2237 : H a 22565968427 := seed 308309 rfl
lemma f2238 : H a 20435790379 := seed 570452 rfl
lemma f2239 : H a 20419009067 := seed 570453 rfl
lemma f2240 : H a 7554034219 := seed 2143316 rfl
lemma f2241 : H a 7537252907 := seed 2143317 rfl
lemma f2242 : H a 18557200939 := seed 799828 rfl
lemma f2243 : H a 18540419627 := seed 799829 rfl
lemma f2244 : H a 5658663467 := seed 2372693 rfl
lemma f2245 : H a 80339796826667 := seed 2818872407 rfl
lemma f2246 : H a 89135890373163 := seed 2550699095 rfl
lemma f2247 : H a 92435230513707 := seed 2424968279 rfl
lemma f2248 : H a 83718882748971 := seed 312611926 rfl
lemma f2249 : H a 30930510572075 := seed 176952406 rfl
lemma f2250 : H a 96901208238635 := seed 2190218326 rfl
lemma f2251 : H a 96914901592619 := seed 681841750 rfl
lemma f2252 : H a 96914901641771 := seed 707007574 rfl
lemma f2253 : H a 15066295339 := seed 178260 rfl
lemma f2254 : H a 15049514027 := seed 178261 rfl
lemma f2255 : H a 13992815659 := seed 309332 rfl
lemma f2256 : H a 13976034347 := seed 309333 rfl
lemma f2257 : H a 11845856299 := seed 571476 rfl
lemma f2258 : H a 11829074987 := seed 571477 rfl
lemma f2259 : H a 7551937579 := seed 1095764 rfl
lemma f2260 : H a 7535156267 := seed 1095765 rfl
lemma f2261 : H a 13187705899 := seed 407636 rfl
lemma f2262 : H a 13170924587 := seed 407637 rfl
lemma f2263 : H a 11040746539 := seed 669780 rfl
lemma f2264 : H a 6746827819 := seed 1194068 rfl
lemma f2265 : H a 9967266859 := seed 800852 rfl
lemma f2266 : H a 9950485547 := seed 800853 rfl
lemma f2267 : H a 5673348139 := seed 1325140 rfl
lemma f2268 : H a 5656566827 := seed 1325141 rfl
lemma f2269 : H a 3509607467 := seed 1587285 rfl
lemma f2270 : H a 36629981256747 := seed 1476442199 rfl
lemma f2271 : H a 36632128740395 := seed 1744877655 rfl
lemma f2272 : H a 36700865260587 := seed 1879095382 rfl
lemma f2273 : H a 36632129002539 := seed 1879095383 rfl
lemma f2274 : H a 44396104477739 := seed 1241790550 rfl
lemma f2275 : H a 27628753480747 := seed 679778390 rfl
lemma f2276 : H a 27560017222699 := seed 679778391 rfl
lemma f2277 : H a 45152203267115 := seed 1216649303 rfl
lemma f2278 : H a 45155424738347 := seed 1745131607 rfl
lemma f2279 : H a 54019180555307 := seed 1216911446 rfl
lemma f2280 : H a 54023476571179 := seed 680564822 rfl
lemma f2281 : H a 53954740313131 := seed 680564823 rfl
lemma f2282 : H a 53955814054955 := seed 814782551 rfl
lemma f2283 : H a 30927288560683 := seed 579213398 rfl
lemma f2284 : H a 30858552302635 := seed 579213399 rfl
lemma f2285 : H a 48519474605099 := seed 1116084310 rfl
lemma f2286 : H a 48523501136939 := seed 1619400790 rfl
lemma f2287 : H a 48454764878891 := seed 1619400791 rfl
lemma f2288 : H a 48454764928043 := seed 1644566615 rfl
lemma f2289 : H a 57248979377195 := seed 1116346455 rfl
lemma f2290 : H a 57250858425387 := seed 1351227479 rfl
lemma f2291 : H a 57319594732587 := seed 1376393302 rfl
lemma f2292 : H a 61717641505835 := seed 1242306646 rfl
lemma f2293 : H a 60146536907 := seed 107413 rfl
lemma f2294 : H a 52112220619 := seed 1090452 rfl
lemma f2295 : H a 52095439307 := seed 1090453 rfl
lemma f2296 : H a 43256013259 := seed 2171796 rfl
lemma f2297 : H a 26080338379 := seed 4268948 rfl
lemma f2298 : H a 18029240779 := seed 5251988 rfl
lemma f2299 : H a 9424622027 := seed 6300565 rfl
lemma f2300 : H a 72920575726027 := seed 3254854551 rfl
lemma f2301 : H a 0xa058258151cb := seed 1178608535 rfl
lemma f2302 : H a 0x8314310351cb := seed 6450938775 rfl
lemma f2303 : H a 0xc21a218251cb := seed 3233874839 rfl
lemma f2304 : H a 0xa21a11a051cb := seed 114295703 rfl
lemma f2305 : H a 55851569867 := seed 107925 rfl
lemma f2306 : H a 35187086027 := seed 2631061 rfl
lemma f2307 : H a 0x8151150352cb := seed 4898989463 rfl
lemma f2308 : H a 0x8154150352cb := seed 6509602199 rfl
lemma f2309 : H a 0x9218318252cb := seed 583075223 rfl
lemma f2310 : H a 0xd025225062cb := seed 4373087638 rfl
lemma f2311 : H a 0xc21c11c052cb := seed 115344791 rfl
lemma f2312 : H a 13447025867 := seed 4237717 rfl
lemma f2313 : H a 13195437259 := seed 4270484 rfl
lemma f2314 : H a 35201770699 := seed 1583508 rfl
lemma f2315 : H a 36632128607435 := seed 1677765015 rfl
lemma f2316 : H a 0x8251250354cb := seed 4865468823 rfl
lemma f2317 : H a 0x8252250354cb := seed 5402339735 rfl
lemma f2318 : H a 0xa058258154cb := seed 1178610071 rfl
lemma f2319 : H a 38556743718091 := seed 1619102103 rfl
lemma f2320 : H a 0x9123121164cb := seed 5377657238 rfl
lemma f2321 : H a 54022939698379 := seed 613452182 rfl
lemma f2322 : H a 0xa123122164cb := seed 4841310614 rfl
lemma f2323 : H a 0x9128328164cb := seed 616597910 rfl
lemma f2324 : H a 0xa118318154cb := seed 1153468823 rfl
lemma f2325 : H a 0x9218318254cb := seed 583076247 rfl
lemma f2326 : H a 0xa219218254cb := seed 1623263639 rfl
lemma f2327 : H a 0xa219218314cb := seed 1648429463 rfl
lemma f2328 : H a 0xb023123064cb := seed 4338485654 rfl
lemma f2329 : H a 0xb023223064cb := seed 4372040086 rfl
lemma f2330 : H a 0xb023223124cb := seed 4397205910 rfl
lemma f2331 : H a 0xb02a22a064cb := seed 617613718 rfl
lemma f2332 : H a 30081767627 := seed 110997 rfl
lemma f2333 : H a 36632128608459 := seed 1677767063 rfl
lemma f2334 : H a 72920575727819 := seed 3254858135 rfl
lemma f2335 : H a 53949907425483 := seed 1149800855 rfl
lemma f2336 : H a 53954203441355 := seed 613454231 rfl
lemma f2337 : H a 55057474148555 := seed 110629271 rfl
lemma f2338 : H a 53704086347 := seed 108181 rfl
lemma f2339 : H a 52093866827 := seed 304789 rfl
lemma f2340 : H a 37065151307 := seed 2139797 rfl
lemma f2341 : H a 19889476427 := seed 4236949 rfl
lemma f2342 : H a 19621106507 := seed 4269717 rfl
lemma f2343 : H a 35203343179 := seed 2369172 rfl
lemma f2344 : H a 35186561867 := seed 2369173 rfl
lemma f2345 : H a 71814353212235 := seed 2483070615 rfl
lemma f2346 : H a 72914133275467 := seed 2449548951 rfl
lemma f2347 : H a 0x8310b103534b := seed 4571891351 rfl
lemma f2348 : H a 0x83143103534b := seed 6450939543 rfl
lemma f2349 : H a 0x89283281634b := seed 348161686 rfl
lemma f2350 : H a 0xc1283281634b := seed 2227209878 rfl
lemma f2351 : H a 0xc2283282634b := seed 2193688214 rfl
lemma f2352 : H a 81452197237579 := seed 111412887 rfl
lemma f2353 : H a 0xc8249248634b := seed 4339271318 rfl
lemma f2354 : H a 0xc824a248634b := seed 4372825750 rfl
lemma f2355 : H a 45114152267 := seed 109205 rfl
lemma f2356 : H a 11299542347 := seed 4237973 rfl
lemma f2357 : H a 35201246539 := seed 1321620 rfl
lemma f2358 : H a 35184465227 := seed 1321621 rfl
lemma f2359 : H a 2996856139 := seed 5253780 rfl
lemma f2360 : H a 36629981123915 := seed 1409329815 rfl
lemma f2361 : H a 0x81509503554b := seed 4630555287 rfl
lemma f2362 : H a 0xa0582581554b := seed 1178610327 rfl
lemma f2363 : H a 0x8310b103554b := seed 4571892375 rfl
lemma f2364 : H a 0xa2183182554b := seed 1119947415 rfl
lemma f2365 : H a 0xa822a228654b := seed 4371778198 rfl
lemma f2366 : H a 0xa21a11a0554b := seed 114297495 rfl
lemma f2367 : H a 11295349067 := seed 2142869 rfl
lemma f2368 : H a 9416759627 := seed 2372245 rfl
lemma f2369 : H a 36629981124939 := seed 1409331863 rfl
lemma f2370 : H a 72920575727947 := seed 3254858391 rfl
lemma f2371 : H a 81504286435659 := seed 2189759126 rfl
lemma f2372 : H a 40819185227 := seed 109717 rfl
lemma f2373 : H a 39225747019 := seed 306324 rfl
lemma f2374 : H a 35183416907 := seed 797845 rfl
lemma f2375 : H a 23639317067 := seed 111765 rfl
lemma f2376 : H a 22045878859 := seed 308372 rfl
lemma f2377 : H a 22029097547 := seed 308373 rfl
lemma f2378 : H a 19898919499 := seed 570516 rfl
lemma f2379 : H a 19882138187 := seed 570517 rfl
lemma f2380 : H a 7017163339 := seed 2143380 rfl
lemma f2381 : H a 7000382027 := seed 2143381 rfl
lemma f2382 : H a 21760727627 := seed 341141 rfl
lemma f2383 : H a 19630549579 := seed 603284 rfl
lemma f2384 : H a 6732012107 := seed 2176149 rfl
lemma f2385 : H a 5138573899 := seed 2372756 rfl
lemma f2386 : H a 5121792587 := seed 2372757 rfl
lemma f2387 : H a 72914133277259 := seed 2449552535 rfl
lemma f2388 : H a 88311055145547 := seed 2483565719 rfl
lemma f2389 : H a 20962410191435 := seed 813798551 rfl
lemma f2390 : H a 27630364617291 := seed 344495254 rfl
lemma f2391 : H a 89203015772747 := seed 2223543446 rfl
lemma f2392 : H a 96901476674123 := seed 2223772822 rfl
lemma f2393 : H a 81452197239371 := seed 111416471 rfl
lemma f2394 : H a 96914096286283 := seed 581178518 rfl
lemma f2395 : H a 96914364721739 := seed 614732950 rfl
lemma f2396 : H a 2989517899 := seed 1587348 rfl
lemma f2397 : H a 36632128609355 := seed 1677768855 rfl
lemma f2398 : H a 26734645304395 := seed 637810839 rfl
lemma f2399 : H a 53130979007563 := seed 839923863 rfl
lemma f2400 : H a 53949907426379 := seed 1149802647 rfl
end BorsukCert

namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f2401 : H a 53951518039115 := seed 1351129239 rfl
lemma f2402 : H a 53954203442251 := seed 613456023 rfl
lemma f2403 : H a 53955814054987 := seed 814782615 rfl
lemma f2404 : H a 61716836150347 := seed 1116477590 rfl
lemma f2405 : H a 61717104585803 := seed 1150032022 rfl
lemma f2406 : H a 55057474149451 := seed 110631063 rfl
lemma f2407 : H a 52630344587 := seed 108309 rfl
lemma f2408 : H a 52110386059 := seed 173844 rfl
lemma f2409 : H a 18832515979 := seed 4237076 rfl
lemma f2410 : H a 51842016139 := seed 206612 rfl
lemma f2411 : H a 35203081099 := seed 2238228 rfl
lemma f2412 : H a 0x81505503538b := seed 4496336663 rfl
lemma f2413 : H a 0x81641605638b := seed 6576711446 rfl
lemma f2414 : H a 0x84582581538b := seed 239085335 rfl
lemma f2415 : H a 0xc2186183138b := seed 2319517463 rfl
lemma f2416 : H a 0x86185184538b := seed 113379095 rfl
lemma f2417 : H a 0xc21c11c0538b := seed 115345175 rfl
lemma f2418 : H a 44040410507 := seed 109333 rfl
lemma f2419 : H a 10225800587 := seed 4238101 rfl
lemma f2420 : H a 43235300747 := seed 207637 rfl
lemma f2421 : H a 9974211979 := seed 4270868 rfl
lemma f2422 : H a 9957430667 := seed 4270869 rfl
lemma f2423 : H a 35200984459 := seed 1190676 rfl
lemma f2424 : H a 35184203147 := seed 1190677 rfl
lemma f2425 : H a 9437472139 := seed 4336404 rfl
lemma f2426 : H a 36628907382155 := seed 1275112215 rfl
lemma f2427 : H a 0x83107103558b := seed 4437674775 rfl
lemma f2428 : H a 0x83123103558b := seed 5377198871 rfl
lemma f2429 : H a 0xa1223221658b := seed 4371548950 rfl
lemma f2430 : H a 0x85283281658b := seed 213945110 rfl
lemma f2431 : H a 0xa1283281658b := seed 1153469206 rfl
lemma f2432 : H a 41920793830795 := seed 1115884310 rfl
lemma f2433 : H a 0x86207206658b := seed 4337109782 rfl
lemma f2434 : H a 0x86183182558b := seed 180423447 rfl
lemma f2435 : H a 0xa2186182558b := seed 1220610839 rfl
lemma f2436 : H a 41860112602507 := seed 110234391 rfl
lemma f2437 : H a 0xa4225224658b := seed 4338092822 rfl
lemma f2438 : H a 0xa4226224658b := seed 4371647254 rfl
lemma f2439 : H a 26860542347 := seed 111381 rfl
lemma f2440 : H a 10238388619 := seed 2142996 rfl
lemma f2441 : H a 9970018699 := seed 2175764 rfl
lemma f2442 : H a 36628907383179 := seed 1275114263 rfl
lemma f2443 : H a 72920575728011 := seed 3254858519 rfl
lemma f2444 : H a 40821282138507 := seed 1149408022 rfl
lemma f2445 : H a 41860112603531 := seed 110236439 rfl
lemma f2446 : H a 39208703627 := seed 175381 rfl
lemma f2447 : H a 35988264587 := seed 568597 rfl
lemma f2448 : H a 38940333707 := seed 208149 rfl
lemma f2449 : H a 5679244939 := seed 4271380 rfl
lemma f2450 : H a 35199936139 := seed 666900 rfl
lemma f2451 : H a 35183154827 := seed 666901 rfl
lemma f2452 : H a 0x81505503568b := seed 4496338199 rfl
lemma f2453 : H a 0x81611605668b := seed 4966100246 rfl
lemma f2454 : H a 20136501401227 := seed 704720151 rfl
lemma f2455 : H a 0x84582581568b := seed 239086871 rfl
lemma f2456 : H a 0x90584581568b := seed 708848919 rfl
lemma f2457 : H a 20961336448651 := seed 679578903 rfl
lemma f2458 : H a 0x91213211668b := seed 4371025174 rfl
lemma f2459 : H a 0x85183181568b := seed 213945623 rfl
lemma f2460 : H a 0x91285281668b := seed 683707670 rfl
lemma f2461 : H a 22565575307 := seed 111893 rfl
lemma f2462 : H a 18808396427 := seed 570645 rfl
lemma f2463 : H a 21760465547 := seed 210197 rfl
lemma f2464 : H a 5658270347 := seed 2176277 rfl
lemma f2465 : H a 1901091467 := seed 2635029 rfl
lemma f2466 : H a 20961336449675 := seed 679580951 rfl
lemma f2467 : H a 23229096094347 := seed 612537622 rfl
lemma f2468 : H a 24263630543499 := seed 109712663 rfl
lemma f2469 : H a 92518466218635 := seed 212342038 rfl
lemma f2470 : H a 92518466267787 := seed 237507862 rfl
lemma f2471 : H a 13975641227 := seed 112917 rfl
lemma f2472 : H a 13455682699 := seed 178452 rfl
lemma f2473 : H a 13438901387 := seed 178453 rfl
lemma f2474 : H a 10218462347 := seed 571669 rfl
lemma f2475 : H a 5924543627 := seed 1095957 rfl
lemma f2476 : H a 9950092427 := seed 604437 rfl
lemma f2477 : H a 9430133899 := seed 669972 rfl
lemma f2478 : H a 9413352587 := seed 669973 rfl
lemma f2479 : H a 5136215179 := seed 1194260 rfl
lemma f2480 : H a 5119433867 := seed 1194261 rfl
lemma f2481 : H a 1915776139 := seed 1587476 rfl
lemma f2482 : H a 1898994827 := seed 1587477 rfl
lemma f2483 : H a 36632128609419 := seed 1677768983 rfl
lemma f2484 : H a 20136501402763 := seed 704723223 rfl
lemma f2485 : H a 37731908672651 := seed 1644247319 rfl
lemma f2486 : H a 39931468930187 := seed 1644312855 rfl
lemma f2487 : H a 53194345573515 := seed 1275607318 rfl
lemma f2488 : H a 20961336450187 := seed 679581975 rfl
lemma f2489 : H a 38556743720075 := seed 1619106071 rfl
lemma f2490 : H a 38625480223883 := seed 1744935190 rfl
lemma f2491 : H a 40821282139275 := seed 1149409558 rfl
lemma f2492 : H a 55118155377803 := seed 1116281110 rfl
lemma f2493 : H a 55118960733323 := seed 1242110230 rfl
lemma f2494 : H a 57322011651211 := seed 580000022 rfl
lemma f2495 : H a 57322280086667 := seed 613554454 rfl
lemma f2496 : H a 57325502098571 := seed 211294486 rfl
lemma f2497 : H a 57325502147723 := seed 236460310 rfl
lemma f2498 : H a 36809631499 := seed 208404 rfl
lemma f2499 : H a 35199411979 := seed 405012 rfl
lemma f2500 : H a 2995021579 := seed 4337172 rfl
lemma f2501 : H a 0x81609605670b := seed 4697665046 rfl
lemma f2502 : H a 0xc606605670b := seed 369241622 rfl
lemma f2503 : H a 0x84582581570b := seed 239087127 rfl
lemma f2504 : H a 0x8a186183170b := seed 440471063 rfl
lemma f2505 : H a 0x86185184570b := seed 113380887 rfl
lemma f2506 : H a 20418091787 := seed 112149 rfl
lemma f2507 : H a 19629763339 := seed 210452 rfl
lemma f2508 : H a 3510786827 := seed 2176533 rfl
lemma f2509 : H a 1917348619 := seed 2373140 rfl
lemma f2510 : H a 1900567307 := seed 2373141 rfl
lemma f2511 : H a 0xc6066056b0b := seed 369243670 rfl
lemma f2512 : H a 75182429793035 := seed 2449618454 rfl
lemma f2513 : H a 79526776363787 := seed 438318615 rfl
lemma f2514 : H a 83703846693643 := seed 2189825558 rfl
lemma f2515 : H a 83704115178251 := seed 2248545814 rfl
lemma f2516 : H a 81452197239563 := seed 111416855 rfl
lemma f2517 : H a 83720225188619 := seed 212080150 rfl
lemma f2518 : H a 83720225237771 := seed 237245974 rfl
lemma f2519 : H a 11828157707 := seed 113173 rfl
lemma f2520 : H a 11308199179 := seed 178708 rfl
lemma f2521 : H a 10234719499 := seed 309780 rfl
lemma f2522 : H a 3793841419 := seed 1096212 rfl
lemma f2523 : H a 9966349579 := seed 342548 rfl
lemma f2524 : H a 9949568267 := seed 342549 rfl
lemma f2525 : H a 2971950347 := seed 1194517 rfl
lemma f2526 : H a 0x95055035d0b := seed 469809687 rfl
lemma f2527 : H a 36628907384075 := seed 1275116055 rfl
lemma f2528 : H a 0xc6066056d0b := seed 369244694 rfl
lemma f2529 : H a 40821282139403 := seed 1149409814 rfl
lemma f2530 : H a 40754156494091 := seed 1350736407 rfl
lemma f2531 : H a 0xe2072066d0b := seed 310581782 rfl
lemma f2532 : H a 41920793832715 := seed 1115888150 rfl
lemma f2533 : H a 0xe20b20a6d0b := seed 176495126 rfl
lemma f2534 : H a 46319914347787 := seed 1116019222 rfl
lemma f2535 : H a 41860112604427 := seed 110238231 rfl
lemma f2536 : H a 7533190667 := seed 113685 rfl
lemma f2537 : H a 3776011787 := seed 572437 rfl
lemma f2538 : H a 0xc60a6096e0b := seed 235158550 rfl
lemma f2539 : H a 26803381562891 := seed 637811734 rfl
lemma f2540 : H a 20962410192395 := seed 813800471 rfl
lemma f2541 : H a 23229096095243 := seed 612539414 rfl
lemma f2542 : H a 23161970564619 := seed 872586263 rfl
lemma f2543 : H a 24263630544395 := seed 109714455 rfl
lemma f2544 : H a 55870284019 := seed 1073636 rfl
lemma f2545 : H a 55853502707 := seed 1073637 rfl
lemma f2546 : H a 30106771699 := seed 4219364 rfl
lemma f2547 : H a 0xe017016050f3 := seed 4843373031 rfl
lemma f2548 : H a 60146897267 := seed 287461 rfl
lemma f2549 : H a 53722800499 := seed 1073892 rfl
lemma f2550 : H a 53706019187 := seed 1073893 rfl
lemma f2551 : H a 51693244787 := seed 1319653 rfl
lemma f2552 : H a 43105407347 := seed 2368229 rfl
lemma f2553 : H a 0xc8248a486173 := seed 4322493158 rfl
lemma f2554 : H a 0xc81489485173 := seed 4322493159 rfl
lemma f2555 : H a 0xc82682486173 := seed 5379457766 rfl
lemma f2556 : H a 0xc81a81889173 := seed 3242459879 rfl
lemma f2557 : H a 0xe01c81c09173 := seed 1365246695 rfl
lemma f2558 : H a 55868711539 := seed 287972 rfl
lemma f2559 : H a 53721752179 := seed 550116 rfl
lemma f2560 : H a 19487806067 := seed 4728037 rfl
lemma f2561 : H a 0xc0588580d273 := seed 2436900071 rfl
lemma f2562 : H a 0xc81489485273 := seed 4322493671 rfl
lemma f2563 : H a 0xc82582486273 := seed 4842587366 rfl
lemma f2564 : H a 0xc81581485273 := seed 4842587367 rfl
lemma f2565 : H a 0xd01c81c09273 := seed 828376295 rfl
lemma f2566 : H a 47278777459 := seed 288996 rfl
lemma f2567 : H a 45131818099 := seed 551140 rfl
lemma f2568 : H a 40821118067 := seed 1075429 rfl
lemma f2569 : H a 15074387059 := seed 4221156 rfl
lemma f2570 : H a 36150975194227 := seed 1879075046 rfl
lemma f2571 : H a 0xa81981889473 := seed 1631848679 rfl
lemma f2572 : H a 0xb01381309473 := seed 4581755111 rfl
lemma f2573 : H a 30098909299 := seed 291044 rfl
lemma f2574 : H a 27951949939 := seed 553188 rfl
lemma f2575 : H a 27935168627 := seed 553189 rfl
lemma f2576 : H a 23641249907 := seed 1077477 rfl
lemma f2577 : H a 13040638067 := seed 2371813 rfl
lemma f2578 : H a 6599759987 := seed 3158245 rfl
lemma f2579 : H a 36150975195251 := seed 1879077094 rfl
lemma f2580 : H a 88317497989235 := seed 3490197735 rfl
lemma f2581 : H a 88661178771571 := seed 3230159078 rfl
lemma f2582 : H a 0x609309289873 := seed 2953859303 rfl
lemma f2583 : H a 0x682582486873 := seed 1621364966 rfl
lemma f2584 : H a 0x681581485873 := seed 1621364967 rfl
lemma f2585 : H a 0x68258248a873 := seed 1629753574 rfl
lemma f2586 : H a 0x701381305873 := seed 2425884903 rfl
lemma f2587 : H a 0x702582506873 := seed 1353191654 rfl
lemma f2588 : H a 60146635187 := seed 156517 rfl
lemma f2589 : H a 52649058739 := seed 1074020 rfl
lemma f2590 : H a 52632277427 := seed 1074021 rfl
lemma f2591 : H a 51692982707 := seed 1188709 rfl
lemma f2592 : H a 0xc09a098491b3 := seed 3359654759 rfl
lemma f2593 : H a 0xa4224a2461b3 := seed 4321313638 rfl
lemma f2594 : H a 0xa412492451b3 := seed 4321313639 rfl
lemma f2595 : H a 0xa426422461b3 := seed 6452020070 rfl
lemma f2596 : H a 0xa416412451b3 := seed 6452020071 rfl
lemma f2597 : H a 0xc41a418451b3 := seed 3233940327 rfl
lemma f2598 : H a 0xe01a41a051b3 := seed 2295333735 rfl
lemma f2599 : H a 55868449459 := seed 157028 rfl
lemma f2600 : H a 52648010419 := seed 550244 rfl
lemma f2601 : H a 0xc419418492b3 := seed 2705458535 rfl
lemma f2602 : H a 47278515379 := seed 158052 rfl
lemma f2603 : H a 47261734067 := seed 158053 rfl
lemma f2604 : H a 44058076339 := seed 551268 rfl
lemma f2605 : H a 39764157619 := seed 1075556 rfl
lemma f2606 : H a 14000645299 := seed 4221284 rfl
lemma f2607 : H a 13983863987 := seed 4221285 rfl
lemma f2608 : H a 38808081587 := seed 1190245 rfl
lemma f2609 : H a 36150974932147 := seed 1744857446 rfl
lemma f2610 : H a 0x90530510d4b3 := seed 5386021223 rfl
lemma f2611 : H a 53400554230963 := seed 1216891239 rfl
lemma f2612 : H a 57248845157555 := seed 1099565415 rfl
lemma f2613 : H a 0x9411491454b3 := seed 4320790887 rfl
lemma f2614 : H a 0x9423421464b3 := seed 5377755494 rfl
lemma f2615 : H a 0x9413411454b3 := seed 5377755495 rfl
lemma f2616 : H a 0x9413411494b3 := seed 5386144103 rfl
lemma f2617 : H a 57253141173427 := seed 563218791 rfl
lemma f2618 : H a 0xa412492454b3 := seed 4321315175 rfl
lemma f2619 : H a 0xa423422464b3 := seed 4841408870 rfl
lemma f2620 : H a 0xa413412454b3 := seed 4841408871 rfl
lemma f2621 : H a 0xa429428464b3 := seed 1623329126 rfl
lemma f2622 : H a 0xa419418494b3 := seed 1631717735 rfl
lemma f2623 : H a 0xb023423064b3 := seed 4439148902 rfl
lemma f2624 : H a 0xb013413054b3 := seed 4439148903 rfl
lemma f2625 : H a 0xb013413094b3 := seed 4447537511 rfl
lemma f2626 : H a 0x94290a9064b3 := seed 164104550 rfl
lemma f2627 : H a 0xb029429064b3 := seed 1221069158 rfl
lemma f2628 : H a 0xb019419054b3 := seed 1221069159 rfl
lemma f2629 : H a 0xb0294290a4b3 := seed 1229457766 rfl
lemma f2630 : H a 0xb01a41a094b3 := seed 693111143 rfl
lemma f2631 : H a 30098647219 := seed 160100 rfl
lemma f2632 : H a 13996452019 := seed 2126180 rfl
lemma f2633 : H a 36150974933171 := seed 1744859494 rfl
lemma f2634 : H a 88317497727155 := seed 3355980135 rfl
lemma f2635 : H a 88592442759347 := seed 3355988327 rfl
lemma f2636 : H a 57248845158579 := seed 1099567463 rfl
lemma f2637 : H a 92510409222323 := seed 3230273894 rfl
lemma f2638 : H a 92441672980659 := seed 3238662503 rfl
lemma f2639 : H a 0x6413412458b3 := seed 2693927271 rfl
lemma f2640 : H a 0x70230a3068b3 := seed 2174226790 rfl
lemma f2641 : H a 0x7023423068b3 := seed 2291667302 rfl
lemma f2642 : H a 0x7015415058b3 := seed 1218974055 rfl
lemma f2643 : H a 53704184627 := seed 157285 rfl
lemma f2644 : H a 52647486259 := seed 288356 rfl
lemma f2645 : H a 52630704947 := seed 288357 rfl
lemma f2646 : H a 20443095859 := seed 4220516 rfl
lemma f2647 : H a 51708191539 := seed 403044 rfl
lemma f2648 : H a 19503801139 := seed 4335204 rfl
lemma f2649 : H a 35589215027 := seed 2369125 rfl
lemma f2650 : H a 18413540147 := seed 4466277 rfl
lemma f2651 : H a 3384824627 := seed 6301285 rfl
lemma f2652 : H a 75182429758259 := seed 2432837222 rfl
lemma f2653 : H a 75388638516019 := seed 2424456807 rfl
lemma f2654 : H a 0x84a0ca04e333 := seed 4571940454 rfl
lemma f2655 : H a 0x8490c904d333 := seed 4571940455 rfl
lemma f2656 : H a 0x84a44a04e333 := seed 6450988646 rfl
lemma f2657 : H a 0xc424c2446333 := seed 4574021222 rfl
lemma f2658 : H a 0xc418c1849333 := seed 2437023335 rfl
lemma f2659 : H a 0xc8248a486333 := seed 4322494054 rfl
lemma f2660 : H a 0xc81489485333 := seed 4322494055 rfl
lemma f2661 : H a 0xc814c1485333 := seed 4439934567 rfl
lemma f2662 : H a 0xc824c248a333 := seed 4448323174 rfl
lemma f2663 : H a 0xc81c41c05333 := seed 417334887 rfl
lemma f2664 : H a 0xc81c41c09333 := seed 425723495 rfl
lemma f2665 : H a 45131031859 := seed 158308 rfl
lemma f2666 : H a 44057552179 := seed 289380 rfl
lemma f2667 : H a 44040770867 := seed 289381 rfl
lemma f2668 : H a 43101476147 := seed 404069 rfl
lemma f2669 : H a 36660598067 := seed 1190501 rfl
lemma f2670 : H a 39929321411891 := seed 1359096423 rfl
lemma f2671 : H a 44396104443187 := seed 1225009766 rfl
lemma f2672 : H a 0x8860c608e533 := seed 4446235238 rfl
lemma f2673 : H a 44333812208947 := seed 420489831 rfl
lemma f2674 : H a 0xa05885845533 := seed 1480600167 rfl
lemma f2675 : H a 40204266427699 := seed 1350716007 rfl
lemma f2676 : H a 44602313200947 := seed 1216629351 rfl
lemma f2677 : H a 0xa4224a246533 := seed 4321315430 rfl
lemma f2678 : H a 0xa41249245533 := seed 4321315431 rfl
lemma f2679 : H a 0xa412c1245533 := seed 4572973671 rfl
lemma f2680 : H a 0xa81a41a05533 := seed 416287335 rfl
lemma f2681 : H a 19480729907 := seed 1192549 rfl
lemma f2682 : H a 9819412787 := seed 2372197 rfl
lemma f2683 : H a 75120136444211 := seed 3489804903 rfl
lemma f2684 : H a 44396104444211 := seed 1225011814 rfl
lemma f2685 : H a 44333812209971 := seed 420491879 rfl
lemma f2686 : H a 40204266428723 := seed 1350718055 rfl
lemma f2687 : H a 44602313201971 := seed 1216631399 rfl
lemma f2688 : H a 83643431934259 := seed 3230012007 rfl
lemma f2689 : H a 0x6412c1245933 := seed 2425492071 rfl
lemma f2690 : H a 0x6414c1445933 := seed 1352798823 rfl
lemma f2691 : H a 0x6814c1485933 := seed 1218712167 rfl
lemma f2692 : H a 27010127156787 := seed 679758951 rfl
lemma f2693 : H a 30858418083379 := seed 562433127 rfl
lemma f2694 : H a 0x9418c1849633 := seed 826412135 rfl
lemma f2695 : H a 0x9828c2886633 := seed 683936870 rfl
lemma f2696 : H a 23656196659 := seed 160868 rfl
lemma f2697 : H a 20435757619 := seed 554084 rfl
lemma f2698 : H a 19479681587 := seed 668773 rfl
lemma f2699 : H a 5524445747 := seed 2372709 rfl
lemma f2700 : H a 88311055276595 := seed 2550674535 rfl
lemma f2701 : H a 27010127157811 := seed 679760999 rfl
lemma f2702 : H a 96846165334579 := seed 681841767 rfl
lemma f2703 : H a 96914901609011 := seed 690230374 rfl
lemma f2704 : H a 11845823539 := seed 555108 rfl
lemma f2705 : H a 7551904819 := seed 1079396 rfl
lemma f2706 : H a 13053488179 := seed 407652 rfl
lemma f2707 : H a 6612610099 := seed 1194084 rfl
lemma f2708 : H a 9816267827 := seed 800869 rfl
lemma f2709 : H a 53126683188275 := seed 1476933735 rfl
lemma f2710 : H a 53401628220467 := seed 1476941927 rfl
lemma f2711 : H a 48454764895283 := seed 1627789415 rfl
lemma f2712 : H a 57248845159475 := seed 1099569255 rfl
lemma f2713 : H a 57319594683443 := seed 1351227494 rfl
lemma f2714 : H a 57250858441779 := seed 1359616103 rfl
lemma f2715 : H a 57255154441267 := seed 814880871 rfl
lemma f2716 : H a 61648905198643 := seed 1217140839 rfl
lemma f2717 : H a 61653201230899 := seed 689182823 rfl
lemma f2718 : H a 61723145956403 := seed 295180390 rfl
lemma f2719 : H a 60146504147 := seed 91045 rfl
lemma f2720 : H a 43121795539 := seed 2171812 rfl
lemma f2721 : H a 25929339347 := seed 4268965 rfl
lemma f2722 : H a 35070697939 := seed 3154852 rfl
lemma f2723 : H a 9290404307 := seed 6300581 rfl
lemma f2724 : H a 72920575693267 := seed 3238077351 rfl
lemma f2725 : H a 0xa0582580d1d3 := seed 1161831335 rfl
lemma f2726 : H a 0xc0682680e1d3 := seed 2235573158 rfl
lemma f2727 : H a 0x82922902d1d3 := seed 5377180583 rfl
lemma f2728 : H a 0x82942902d1d3 := seed 6450922407 rfl
lemma f2729 : H a 0xa2222a2261d3 := seed 4321248166 rfl
lemma f2730 : H a 0xe0260a6061d3 := seed 4323279782 rfl
lemma f2731 : H a 0xe026226061d3 := seed 4373611430 rfl
lemma f2732 : H a 51708584659 := seed 599460 rfl
lemma f2733 : H a 0x82512502d2d3 := seed 4848690599 rfl
lemma f2734 : H a 0x90682680e2d3 := seed 624960934 rfl
lemma f2735 : H a 0x82912902d2d3 := seed 4840310183 rfl
lemma f2736 : H a 0x82942902d2d3 := seed 6450922919 rfl
lemma f2737 : H a 35067552979 := seed 1583524 rfl
lemma f2738 : H a 0x82512502d4d3 := seed 4848691623 rfl
lemma f2739 : H a 0x82522502d4d3 := seed 5385562535 rfl
lemma f2740 : H a 0x90612610e4d3 := seed 4379388326 rfl
lemma f2741 : H a 0x82912902d4d3 := seed 4840311207 rfl
lemma f2742 : H a 0x82922902d4d3 := seed 5377182119 rfl
lemma f2743 : H a 30081734867 := seed 94629 rfl
lemma f2744 : H a 72920575695059 := seed 3238080935 rfl
lemma f2745 : H a 38006853654739 := seed 1619087783 rfl
lemma f2746 : H a 55057339930835 := seed 93852071 rfl
lemma f2747 : H a 53704053587 := seed 91813 rfl
lemma f2748 : H a 52110615379 := seed 288420 rfl
lemma f2749 : H a 19906224979 := seed 4220580 rfl
lemma f2750 : H a 19889443667 := seed 4220581 rfl
lemma f2751 : H a 51708060499 := seed 337572 rfl
lemma f2752 : H a 51691279187 := seed 337573 rfl
lemma f2753 : H a 36679344979 := seed 2172580 rfl
lemma f2754 : H a 36662563667 := seed 2172581 rfl
lemma f2755 : H a 19503670099 := seed 4269732 rfl
lemma f2756 : H a 19486888787 := seed 4269733 rfl
lemma f2757 : H a 35069125459 := seed 2369188 rfl
lemma f2758 : H a 0x80d08d02d353 := seed 4630537895 rfl
lemma f2759 : H a 0x80d40d02d353 := seed 6509586087 rfl
lemma f2760 : H a 72914133242707 := seed 2432771751 rfl
lemma f2761 : H a 0x8250a502d353 := seed 4580255399 rfl
lemma f2762 : H a 0x82542502d353 := seed 6459303591 rfl
lemma f2763 : H a 0x8264260a6353 := seed 6710961830 rfl
lemma f2764 : H a 0x8290a902d353 := seed 4571874983 rfl
lemma f2765 : H a 0x82942902d353 := seed 6450923175 rfl
lemma f2766 : H a 0x88948908d353 := seed 6451119783 rfl
lemma f2767 : H a 0x88a82a80e353 := seed 348145318 rfl
lemma f2768 : H a 0xc0a82a80e353 := seed 2227193510 rfl
lemma f2769 : H a 0xc0988980d353 := seed 2428520103 rfl
lemma f2770 : H a 0xc0a88a82a353 := seed 2487240358 rfl
lemma f2771 : H a 0xc09889829353 := seed 2487240359 rfl
lemma f2772 : H a 81504152216403 := seed 2172978854 rfl
lemma f2773 : H a 0x8a20aa0a6353 := seed 4320462502 rfl
lemma f2774 : H a 0x8a282a826353 := seed 297862822 rfl
lemma f2775 : H a 0xc2282a826353 := seed 2176911014 rfl
lemma f2776 : H a 81452063019859 := seed 94635687 rfl
lemma f2777 : H a 0xc8248a486353 := seed 4322494118 rfl
lemma f2778 : H a 0xc824a2486353 := seed 4372825766 rfl
lemma f2779 : H a 0xc824a248a353 := seed 4381214374 rfl
lemma f2780 : H a 43520681299 := seed 289444 rfl
lemma f2781 : H a 43118126419 := seed 338596 rfl
lemma f2782 : H a 35067028819 := seed 1321636 rfl
lemma f2783 : H a 35050247507 := seed 1321637 rfl
lemma f2784 : H a 9286735187 := seed 4467365 rfl
lemma f2785 : H a 36080091059539 := seed 1409313447 rfl
lemma f2786 : H a 0x8850a508d553 := seed 4379126439 rfl
lemma f2787 : H a 0x8290a902d553 := seed 4571876007 rfl
lemma f2788 : H a 0x82922902d553 := seed 5377182375 rfl
lemma f2789 : H a 0x8892890a9553 := seed 5436099239 rfl
lemma f2790 : H a 0xa09289229553 := seed 4631579303 rfl
lemma f2791 : H a 0xa2222a226553 := seed 4321249958 rfl
lemma f2792 : H a 46259098899795 := seed 93588135 rfl
lemma f2793 : H a 27934251347 := seed 94885 rfl
lemma f2794 : H a 19480598867 := seed 1127077 rfl
lemma f2795 : H a 9299323219 := seed 2372260 rfl
lemma f2796 : H a 9282541907 := seed 2372261 rfl
lemma f2797 : H a 71264463149395 := seed 2483057319 rfl
lemma f2798 : H a 72920575695187 := seed 3238081191 rfl
lemma f2799 : H a 73189078260051 := seed 2424394407 rfl
lemma f2800 : H a 81504152217939 := seed 2172981926 rfl
end BorsukCert

namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f2801 : H a 46259098900819 := seed 93590183 rfl
lemma f2802 : H a 0x6822a228a953 := seed 2232685222 rfl
lemma f2803 : H a 0x68248a486953 := seed 1101271718 rfl
lemma f2804 : H a 0x82512502d653 := seed 4848692391 rfl
lemma f2805 : H a 0x90682680e653 := seed 624962726 rfl
lemma f2806 : H a 0x8290a902d653 := seed 4571876519 rfl
lemma f2807 : H a 0x82912902d653 := seed 4840311975 rfl
lemma f2808 : H a 23639284307 := seed 95397 rfl
lemma f2809 : H a 19898886739 := seed 554148 rfl
lemma f2810 : H a 19496331859 := seed 603300 rfl
lemma f2811 : H a 19479550547 := seed 603301 rfl
lemma f2812 : H a 5004356179 := seed 2372772 rfl
lemma f2813 : H a 4987574867 := seed 2372773 rfl
lemma f2814 : H a 18487905016403 := seed 872445095 rfl
lemma f2815 : H a 71266610633299 := seed 2751493287 rfl
lemma f2816 : H a 72914133244499 := seed 2432775335 rfl
lemma f2817 : H a 88586000063059 := seed 2424853671 rfl
lemma f2818 : H a 90302393248339 := seed 2173244582 rfl
lemma f2819 : H a 96901476674131 := seed 2223772838 rfl
lemma f2820 : H a 81452063021651 := seed 94639271 rfl
lemma f2821 : H a 96913962068563 := seed 564401318 rfl
lemma f2822 : H a 96914364721747 := seed 614732966 rfl
lemma f2823 : H a 36080091061331 := seed 1409317031 rfl
lemma f2824 : H a 44330589412435 := seed 1627666599 rfl
lemma f2825 : H a 38006853655635 := seed 1619089575 rfl
lemma f2826 : H a 55057339931731 := seed 93853863 rfl
lemma f2827 : H a 52630311827 := seed 91941 rfl
lemma f2828 : H a 35068863379 := seed 2238244 rfl
lemma f2829 : H a 0x82906902d393 := seed 4437657383 rfl
lemma f2830 : H a 0x82942902d393 := seed 6450923303 rfl
lemma f2831 : H a 44040377747 := seed 92965 rfl
lemma f2832 : H a 43503637907 := seed 158501 rfl
lemma f2833 : H a 10242549139 := seed 4221732 rfl
lemma f2834 : H a 10225767827 := seed 4221733 rfl
lemma f2835 : H a 35066766739 := seed 1190692 rfl
lemma f2836 : H a 35049985427 := seed 1190693 rfl
lemma f2837 : H a 0x82506502d593 := seed 4446038823 rfl
lemma f2838 : H a 0x82522502d593 := seed 5385562919 rfl
lemma f2839 : H a 0xa0582580d593 := seed 1161833255 rfl
lemma f2840 : H a 0x82922902d593 := seed 5377182503 rfl
lemma f2841 : H a 0x84a82a80e593 := seed 213928742 rfl
lemma f2842 : H a 0xa0984980d593 := seed 1220561703 rfl
lemma f2843 : H a 0x86282a826593 := seed 163646246 rfl
lemma f2844 : H a 41859978384787 := seed 93457191 rfl
lemma f2845 : H a 0xa42262246593 := seed 4371647270 rfl
lemma f2846 : H a 26860509587 := seed 95013 rfl
lemma f2847 : H a 10238355859 := seed 2126628 rfl
lemma f2848 : H a 17886898579 := seed 1192740 rfl
lemma f2849 : H a 72920575695251 := seed 3238081319 rfl
lemma f2850 : H a 38003632429459 := seed 1216434983 rfl
lemma f2851 : H a 5930800787 := seed 4222245 rfl
lemma f2852 : H a 5545027219 := seed 4271396 rfl
lemma f2853 : H a 5528245907 := seed 4271397 rfl
lemma f2854 : H a 35065718419 := seed 666916 rfl
lemma f2855 : H a 20136501368467 := seed 687942951 rfl
lemma f2856 : H a 0x82512502d693 := seed 4848692519 rfl
lemma f2857 : H a 0x90612610e693 := seed 4379389222 rfl
lemma f2858 : H a 0x82906902d693 := seed 4437658919 rfl
lemma f2859 : H a 0x82a12a06a693 := seed 4966141222 rfl
lemma f2860 : H a 0x90a82a80e693 := seed 616582438 rfl
lemma f2861 : H a 0x86282a826693 := seed 163646758 rfl
lemma f2862 : H a 5540833939 := seed 2176292 rfl
lemma f2863 : H a 20411446385299 := seed 679564583 rfl
lemma f2864 : H a 24263496325779 := seed 92935463 rfl
lemma f2865 : H a 92515244206739 := seed 614602022 rfl
lemma f2866 : H a 13975608467 := seed 96549 rfl
lemma f2867 : H a 13455649939 := seed 162084 rfl
lemma f2868 : H a 10218429587 := seed 555301 rfl
lemma f2869 : H a 9815874707 := seed 604453 rfl
lemma f2870 : H a 9295916179 := seed 669988 rfl
lemma f2871 : H a 9279134867 := seed 669989 rfl
lemma f2872 : H a 5001997459 := seed 1194276 rfl
lemma f2873 : H a 4985216147 := seed 1194277 rfl
lemma f2874 : H a 1764777107 := seed 1587493 rfl
lemma f2875 : H a 36079017319571 := seed 1275099431 rfl
lemma f2876 : H a 37731908639891 := seed 1627470119 rfl
lemma f2877 : H a 39931468897427 := seed 1627535655 rfl
lemma f2878 : H a 53194345573523 := seed 1275607334 rfl
lemma f2879 : H a 20411446385811 := seed 679565607 rfl
lemma f2880 : H a 38006853655699 := seed 1619089703 rfl
lemma f2881 : H a 38075590159507 := seed 1744918822 rfl
lemma f2882 : H a 24331695582355 := seed 159979814 rfl
lemma f2883 : H a 55118021160083 := seed 1099503910 rfl
lemma f2884 : H a 55118960700563 := seed 1225333030 rfl
lemma f2885 : H a 57321877433491 := seed 563222822 rfl
lemma f2886 : H a 57322280086675 := seed 613554470 rfl
lemma f2887 : H a 55057339931795 := seed 93853991 rfl
lemma f2888 : H a 57325502098579 := seed 211294502 rfl
lemma f2889 : H a 57325502114963 := seed 219683110 rfl
lemma f2890 : H a 35065194259 := seed 405028 rfl
lemma f2891 : H a 0x82906902d713 := seed 4437659175 rfl
lemma f2892 : H a 0x8290a902d713 := seed 4571876903 rfl
lemma f2893 : H a 0xe10c90c5713 := seed 92671527 rfl
lemma f2894 : H a 20418059027 := seed 95781 rfl
lemma f2895 : H a 19881319187 := seed 161317 rfl
lemma f2896 : H a 1783130899 := seed 2373156 rfl
lemma f2897 : H a 83719822535443 := seed 161748518 rfl
lemma f2898 : H a 83720225188627 := seed 212080166 rfl
lemma f2899 : H a 11828124947 := seed 96805 rfl
lemma f2900 : H a 10888830227 := seed 211493 rfl
lemma f2901 : H a 2854513939 := seed 1194532 rfl
lemma f2902 : H a 2837732627 := seed 1194533 rfl
lemma f2903 : H a 36079017319699 := seed 1275099687 rfl
lemma f2904 : H a 36080091061523 := seed 1409317415 rfl
lemma f2905 : H a 38004706172179 := seed 1350654503 rfl
lemma f2906 : H a 44602313202963 := seed 1216633383 rfl
lemma f2907 : H a 41853936639251 := seed 1359157799 rfl
lemma f2908 : H a 0xe10c90c5d13 := seed 92674599 rfl
lemma f2909 : H a 41859978386707 := seed 93461031 rfl
lemma f2910 : H a 3792760339 := seed 556068 rfl
lemma f2911 : H a 5537164819 := seed 343076 rfl
lemma f2912 : H a 3373424147 := seed 605221 rfl
lemma f2913 : H a 20412520128019 := seed 813784103 rfl
lemma f2914 : H a 24261750578707 := seed 813898791 rfl
lemma f2915 : H a 24263496326675 := seed 92937255 rfl
lemma f2916 : H a 60146438627 := seed 58309 rfl
lemma f2917 : H a 51709567459 := seed 1090500 rfl
lemma f2918 : H a 51692786147 := seed 1090501 rfl
lemma f2919 : H a 43121730019 := seed 2139076 rfl
lemma f2920 : H a 34785481187 := seed 3154885 rfl
lemma f2921 : H a 17626587619 := seed 5252036 rfl
lemma f2922 : H a 9038750179 := seed 6300612 rfl
lemma f2923 : H a 71820795564515 := seed 3238044615 rfl
lemma f2924 : H a 72095740580323 := seed 3229664199 rfl
lemma f2925 : H a 0x81921901d1e3 := seed 5377147847 rfl
lemma f2926 : H a 0xa0a60a20e1e3 := seed 6451905478 rfl
lemma f2927 : H a 0xc09a0980d1e3 := seed 3233825735 rfl
lemma f2928 : H a 0xc11a118191e3 := seed 3242230727 rfl
lemma f2929 : H a 51708519139 := seed 566724 rfl
lemma f2930 : H a 71816500597475 := seed 2701174215 rfl
lemma f2931 : H a 0x81511501d2e3 := seed 4848657863 rfl
lemma f2932 : H a 0x90611610e2e3 := seed 4345832902 rfl
lemma f2933 : H a 0xc0581580d2e3 := seed 2202019271 rfl
lemma f2934 : H a 0x81911901d2e3 := seed 4840277447 rfl
lemma f2935 : H a 47261537507 := seed 59845 rfl
lemma f2936 : H a 43235988707 := seed 551365 rfl
lemma f2937 : H a 38942069987 := seed 1075653 rfl
lemma f2938 : H a 13178557667 := seed 4221381 rfl
lemma f2939 : H a 34782336227 := seed 1583557 rfl
lemma f2940 : H a 4741686499 := seed 5253572 rfl
lemma f2941 : H a 0x80d10d01d4e3 := seed 4865419719 rfl
lemma f2942 : H a 36632128509155 := seed 1627433415 rfl
lemma f2943 : H a 36907073524963 := seed 1619052999 rfl
lemma f2944 : H a 0x81911901d4e3 := seed 4840278471 rfl
lemma f2945 : H a 0x81921901d4e3 := seed 5377149383 rfl
lemma f2946 : H a 0x90a81a80e4e3 := seed 583027142 rfl
lemma f2947 : H a 0xa0990980d4e3 := seed 1623214535 rfl
lemma f2948 : H a 54022537045219 := seed 563120582 rfl
lemma f2949 : H a 0xb0231230a4e3 := seed 4346874310 rfl
lemma f2950 : H a 0xa11a09a054e3 := seed 63965639 rfl
lemma f2951 : H a 30081669347 := seed 61893 rfl
lemma f2952 : H a 25921935587 := seed 569797 rfl
lemma f2953 : H a 17619249379 := seed 1585604 rfl
lemma f2954 : H a 36082238478563 := seed 1644196295 rfl
lemma f2955 : H a 36632128510179 := seed 1627435463 rfl
lemma f2956 : H a 71820795566307 := seed 3238048199 rfl
lemma f2957 : H a 36907073525987 := seed 1619055047 rfl
lemma f2958 : H a 72091445614819 := seed 2692796871 rfl
lemma f2959 : H a 72095740582115 := seed 3229667783 rfl
lemma f2960 : H a 53957828303075 := seed 60297671 rfl
lemma f2961 : H a 53703988067 := seed 59077 rfl
lemma f2962 : H a 19621008227 := seed 4220613 rfl
lemma f2963 : H a 51707994979 := seed 304836 rfl
lemma f2964 : H a 51691213667 := seed 304837 rfl
lemma f2965 : H a 19486823267 := seed 4236997 rfl
lemma f2966 : H a 34800690019 := seed 2369220 rfl
lemma f2967 : H a 34783908707 := seed 2369221 rfl
lemma f2968 : H a 71814353113955 := seed 2432739015 rfl
lemma f2969 : H a 0x81509501d363 := seed 4580222663 rfl
lemma f2970 : H a 0x816416096363 := seed 6710929094 rfl
lemma f2971 : H a 79510934967139 := seed 2198087367 rfl
lemma f2972 : H a 0x885485095363 := seed 6476277447 rfl
lemma f2973 : H a 0xc05485415363 := seed 4599064263 rfl
lemma f2974 : H a 0x88681680e363 := seed 322971334 rfl
lemma f2975 : H a 0xc0681680e363 := seed 2202019526 rfl
lemma f2976 : H a 0x81909901d363 := seed 4571842247 rfl
lemma f2977 : H a 0x81941901d363 := seed 6450890439 rfl
lemma f2978 : H a 0xc0a81a80e363 := seed 2193639110 rfl
lemma f2979 : H a 0xc0a88a81a363 := seed 2453685958 rfl
lemma f2980 : H a 80352551392099 := seed 61081287 rfl
lemma f2981 : H a 0xc8248a486363 := seed 4322494150 rfl
lemma f2982 : H a 0xc82492486363 := seed 4339271366 rfl
lemma f2983 : H a 0xc8249248a363 := seed 4347659974 rfl
lemma f2984 : H a 0xc82c0ac06363 := seed 299894470 rfl
lemma f2985 : H a 0xc82c12c0a363 := seed 325060294 rfl
lemma f2986 : H a 36677182819 := seed 1092292 rfl
lemma f2987 : H a 36660401507 := seed 1092293 rfl
lemma f2988 : H a 34781812067 := seed 1321669 rfl
lemma f2989 : H a 2594202979 := seed 5253828 rfl
lemma f2990 : H a 0x80d08d01d563 := seed 4596984519 rfl
lemma f2991 : H a 36629981025635 := seed 1358998215 rfl
lemma f2992 : H a 36904926041443 := seed 1350617799 rfl
lemma f2993 : H a 0x81909901d563 := seed 4571843271 rfl
lemma f2994 : H a 0x81921901d563 := seed 5377149639 rfl
lemma f2995 : H a 45226444023139 := seed 294685382 rfl
lemma f2996 : H a 0xa11891819563 := seed 1363184327 rfl
lemma f2997 : H a 0xa82292286563 := seed 4338223814 rfl
lemma f2998 : H a 0xa11a09a05563 := seed 63965895 rfl
lemma f2999 : H a 27934185827 := seed 62149 rfl
lemma f3000 : H a 25921411427 := seed 307909 rfl
lemma f3001 : H a 19497314659 := seed 1094340 rfl
lemma f3002 : H a 10892695907 := seed 2142917 rfl
lemma f3003 : H a 9030887779 := seed 2372292 rfl
lemma f3004 : H a 9014106467 := seed 2372293 rfl
lemma f3005 : H a 2590009699 := seed 3158724 rfl
lemma f3006 : H a 36629981026659 := seed 1359000263 rfl
lemma f3007 : H a 71820795566435 := seed 3238048455 rfl
lemma f3008 : H a 71889532316003 := seed 3489706694 rfl
lemma f3009 : H a 72089298131299 := seed 2424361671 rfl
lemma f3010 : H a 80352551393635 := seed 61084359 rfl
lemma f3011 : H a 0x68248a486963 := seed 1101271750 rfl
lemma f3012 : H a 36676134499 := seed 568516 rfl
lemma f3013 : H a 2593154659 := seed 4730052 rfl
lemma f3014 : H a 19037794981475 := seed 822127815 rfl
lemma f3015 : H a 0x81511501d663 := seed 4848659655 rfl
lemma f3016 : H a 0x90611610e663 := seed 4345834694 rfl
lemma f3017 : H a 0x88581580d663 := seed 322972871 rfl
lemma f3018 : H a 0x81911901d663 := seed 4840279239 rfl
lemma f3019 : H a 27009321850467 := seed 579095751 rfl
lemma f3020 : H a 23639218787 := seed 62661 rfl
lemma f3021 : H a 21777410659 := seed 292036 rfl
lemma f3022 : H a 19630451299 := seed 554180 rfl
lemma f3023 : H a 19613669987 := seed 554181 rfl
lemma f3024 : H a 6748695139 := seed 2127044 rfl
lemma f3025 : H a 19479485027 := seed 570565 rfl
lemma f3026 : H a 6614510179 := seed 2143428 rfl
lemma f3027 : H a 6597728867 := seed 2143429 rfl
lemma f3028 : H a 17600895587 := seed 799941 rfl
lemma f3029 : H a 4735920739 := seed 2372804 rfl
lemma f3030 : H a 4719139427 := seed 2372805 rfl
lemma f3031 : H a 2588961379 := seed 2634948 rfl
lemma f3032 : H a 2572180067 := seed 2634949 rfl
lemma f3033 : H a 71266610567779 := seed 2717938887 rfl
lemma f3034 : H a 26805261101667 := seed 319304902 rfl
lemma f3035 : H a 88377912257123 := seed 2198353094 rfl
lemma f3036 : H a 88392679352931 := seed 824194246 rfl
lemma f3037 : H a 88323943094883 := seed 824194247 rfl
lemma f3038 : H a 88323943127651 := seed 840971463 rfl
lemma f3039 : H a 19312739998307 := seed 813749447 rfl
lemma f3040 : H a 72091445615203 := seed 2692797639 rfl
lemma f3041 : H a 72160182381155 := seed 2952844486 rfl
lemma f3042 : H a 27009321851491 := seed 579097799 rfl
lemma f3043 : H a 88665745320547 := seed 580932806 rfl
lemma f3044 : H a 96901074020963 := seed 2173441222 rfl
lemma f3045 : H a 96913962068579 := seed 564401350 rfl
lemma f3046 : H a 96914096286307 := seed 581178566 rfl
lemma f3047 : H a 15049284707 := seed 63685 rfl
lemma f3048 : H a 11040517219 := seed 555204 rfl
lemma f3049 : H a 6729817187 := seed 1079493 rfl
lemma f3050 : H a 13036510307 := seed 309445 rfl
lemma f3051 : H a 10906332259 := seed 571588 rfl
lemma f3052 : H a 10889550947 := seed 571589 rfl
lemma f3053 : H a 6595632227 := seed 1095877 rfl
lemma f3054 : H a 4733824099 := seed 1325252 rfl
lemma f3055 : H a 2586864739 := seed 1587396 rfl
lemma f3056 : H a 2570083427 := seed 1587397 rfl
lemma f3057 : H a 36082238479459 := seed 1644198087 rfl
lemma f3058 : H a 36150975196259 := seed 1879079110 rfl
lemma f3059 : H a 36632128511075 := seed 1627437255 rfl
lemma f3060 : H a 53130979007587 := seed 839923911 rfl
lemma f3061 : H a 19312739998819 := seed 813750471 rfl
lemma f3062 : H a 36975810292835 := seed 1879103686 rfl
lemma f3063 : H a 53468485184611 := seed 1116231878 rfl
lemma f3064 : H a 53951518039139 := seed 1351129287 rfl
lemma f3065 : H a 53955814055011 := seed 814782663 rfl
lemma f3066 : H a 61716701932643 := seed 1099700422 rfl
lemma f3067 : H a 61716836150371 := seed 1116477638 rfl
lemma f3068 : H a 53957828303971 := seed 60299463 rfl
lemma f3069 : H a 52630246307 := seed 59205 rfl
lemma f3070 : H a 51841917859 := seed 157508 rfl
lemma f3071 : H a 51707732899 := seed 173892 rfl
lemma f3072 : H a 17624753059 := seed 4335428 rfl
lemma f3073 : H a 1522557859 := seed 6301508 rfl
lemma f3074 : H a 1505776547 := seed 6301509 rfl
lemma f3075 : H a 0x81905901d3a3 := seed 4437624647 rfl
lemma f3076 : H a 0x8518498453a3 := seed 63047495 rfl
lemma f3077 : H a 0xc42c12c063a3 := seed 182454086 rfl
lemma f3078 : H a 44040312227 := seed 60229 rfl
lemma f3079 : H a 9957332387 := seed 4221765 rfl
lemma f3080 : H a 9839928739 := seed 4238148 rfl
lemma f3081 : H a 9823147427 := seed 4238149 rfl
lemma f3082 : H a 34798331299 := seed 1190724 rfl
lemma f3083 : H a 34781549987 := seed 1190725 rfl
lemma f3084 : H a 9034818979 := seed 4336452 rfl
lemma f3085 : H a 9018037667 := seed 4336453 rfl
lemma f3086 : H a 1520461219 := seed 5253956 rfl
lemma f3087 : H a 36079017252259 := seed 1241541447 rfl
lemma f3088 : H a 0x80d04d01d5a3 := seed 4462766919 rfl
lemma f3089 : H a 36628907283875 := seed 1224780615 rfl
lemma f3090 : H a 0x81505501d5a3 := seed 4446006087 rfl
lemma f3091 : H a 0x81521501d5a3 := seed 5385530183 rfl
lemma f3092 : H a 39996178621859 := seed 1124215622 rfl
lemma f3093 : H a 0xa058458155a3 := seed 1245719367 rfl
lemma f3094 : H a 0x81905901d5a3 := seed 4437625671 rfl
lemma f3095 : H a 0x81921901d5a3 := seed 5377149767 rfl
lemma f3096 : H a 0xa0a81a80e5a3 := seed 1119898438 rfl
lemma f3097 : H a 0xa0984980d5a3 := seed 1220561735 rfl
lemma f3098 : H a 0xa112512155a3 := seed 4438657863 rfl
lemma f3099 : H a 0x85281a8165a3 := seed 163613510 rfl
lemma f3100 : H a 0xa1281a8165a3 := seed 1103137606 rfl
lemma f3101 : H a 0xa118518155a3 := seed 1220578119 rfl
lemma f3102 : H a 40760466757027 := seed 59902791 rfl
lemma f3103 : H a 0xa4224a2465a3 := seed 4321315654 rfl
lemma f3104 : H a 0xa4225224a5a3 := seed 4346481478 rfl
lemma f3105 : H a 0x8518498455a3 := seed 63048519 rfl
lemma f3106 : H a 0xa428528465a3 := seed 1120013126 rfl
lemma f3107 : H a 26860444067 := seed 62277 rfl
lemma f3108 : H a 71820795566499 := seed 3238048583 rfl
lemma f3109 : H a 72095740582307 := seed 3229668167 rfl
lemma f3110 : H a 40759661255075 := seed 160469831 rfl
lemma f3111 : H a 40760466758051 := seed 59904839 rfl
lemma f3112 : H a 39745345187 := seed 60741 rfl
lemma f3113 : H a 38957016739 := seed 159044 rfl
lemma f3114 : H a 5679146659 := seed 4222276 rfl
lemma f3115 : H a 5662365347 := seed 4222277 rfl
lemma f3116 : H a 38822831779 := seed 175428 rfl
lemma f3117 : H a 38806050467 := seed 175429 rfl
lemma f3118 : H a 5544961699 := seed 4238660 rfl
lemma f3119 : H a 5528180387 := seed 4238661 rfl
lemma f3120 : H a 34797282979 := seed 666948 rfl
lemma f3121 : H a 34780501667 := seed 666949 rfl
lemma f3122 : H a 1519412899 := seed 4730180 rfl
lemma f3123 : H a 18486831208099 := seed 704671047 rfl
lemma f3124 : H a 0x81505501d6a3 := seed 4446006599 rfl
lemma f3125 : H a 0x8161160566a3 := seed 4966100294 rfl
lemma f3126 : H a 0x90584580d6a3 := seed 692071751 rfl
lemma f3127 : H a 0x9058458156a3 := seed 708848967 rfl
lemma f3128 : H a 19311666255523 := seed 679529799 rfl
lemma f3129 : H a 0x81905901d6a3 := seed 4437626183 rfl
lemma f3130 : H a 0x81911901d6a3 := seed 4840279367 rfl
lemma f3131 : H a 22610201335459 := seed 578964807 rfl
lemma f3132 : H a 0x84914904d6a3 := seed 4840377671 rfl
lemma f3133 : H a 0x8491490596a3 := seed 4865543495 rfl
lemma f3134 : H a 0x90a81a80e6a3 := seed 583028038 rfl
lemma f3135 : H a 0x9098498196a3 := seed 708857159 rfl
lemma f3136 : H a 23163984696995 := seed 59379015 rfl
lemma f3137 : H a 0x94214a1466a3 := seed 4320791878 rfl
lemma f3138 : H a 0x9421521466a3 := seed 4337569094 rfl
lemma f3139 : H a 0x94215214a6a3 := seed 4345957702 rfl
lemma f3140 : H a 22565477027 := seed 62789 rfl
lemma f3141 : H a 5540768419 := seed 2143556 rfl
lemma f3142 : H a 4735658659 := seed 2241860 rfl
lemma f3143 : H a 19036721240739 := seed 687912263 rfl
lemma f3144 : H a 71816500599459 := seed 2701178183 rfl
lemma f3145 : H a 72091445615267 := seed 2692797767 rfl
lemma f3146 : H a 23159957183139 := seed 562206023 rfl
lemma f3147 : H a 23163984698019 := seed 59381063 rfl
lemma f3148 : H a 13975542947 := seed 63813 rfl
lemma f3149 : H a 13187214499 := seed 162116 rfl
lemma f3150 : H a 13170433187 := seed 162117 rfl
lemma f3151 : H a 9949994147 := seed 555333 rfl
lemma f3152 : H a 5672856739 := seed 1079620 rfl
lemma f3153 : H a 13036248227 := seed 178501 rfl
lemma f3154 : H a 9832590499 := seed 571716 rfl
lemma f3155 : H a 9815809187 := seed 571717 rfl
lemma f3156 : H a 5538671779 := seed 1096004 rfl
lemma f3157 : H a 5521890467 := seed 1096005 rfl
lemma f3158 : H a 9027480739 := seed 670020 rfl
lemma f3159 : H a 9010699427 := seed 670021 rfl
lemma f3160 : H a 4733562019 := seed 1194308 rfl
lemma f3161 : H a 4716780707 := seed 1194309 rfl
lemma f3162 : H a 1513122979 := seed 1587524 rfl
lemma f3163 : H a 1496341667 := seed 1587525 rfl
lemma f3164 : H a 18486831209635 := seed 704674119 rfl
lemma f3165 : H a 36079017254051 := seed 1241545031 rfl
lemma f3166 : H a 36150974934179 := seed 1744861510 rfl
lemma f3167 : H a 19036721241251 := seed 687913287 rfl
lemma f3168 : H a 36632128511139 := seed 1627437383 rfl
lemma f3169 : H a 36700864998563 := seed 1744877894 rfl
lemma f3170 : H a 39931468897443 := seed 1627535687 rfl
lemma f3171 : H a 39931468930211 := seed 1644312903 rfl
lemma f3172 : H a 53129905233059 := seed 688929095 rfl
lemma f3173 : H a 53129905265827 := seed 705706311 rfl
lemma f3174 : H a 19311666257059 := seed 679532871 rfl
lemma f3175 : H a 36903852301475 := seed 1216403783 rfl
lemma f3176 : H a 36907073526947 := seed 1619056967 rfl
lemma f3177 : H a 36975810030755 := seed 1744886086 rfl
lemma f3178 : H a 40756303977635 := seed 1619171655 rfl
lemma f3179 : H a 23231915453603 := seed 159947078 rfl
lemma f3180 : H a 54018241031331 := seed 1099471174 rfl
lemma f3181 : H a 40760466758819 := seed 59906375 rfl
lemma f3182 : H a 57321877433507 := seed 563222854 rfl
lemma f3183 : H a 57322011651235 := seed 580000070 rfl
lemma f3184 : H a 53957828304035 := seed 60299591 rfl
lemma f3185 : H a 37597861667 := seed 60997 rfl
lemma f3186 : H a 36809533219 := seed 159300 rfl
lemma f3187 : H a 36675348259 := seed 175684 rfl
lemma f3188 : H a 3380696867 := seed 4238917 rfl
lemma f3189 : H a 2592368419 := seed 4337220 rfl
lemma f3190 : H a 1518888739 := seed 4468292 rfl
lemma f3191 : H a 1502107427 := seed 4468293 rfl
lemma f3192 : H a 0x9905901d723 := seed 411094599 rfl
lemma f3193 : H a 0x81905901d723 := seed 4437626439 rfl
lemma f3194 : H a 0x81909901d723 := seed 4571844167 rfl
lemma f3195 : H a 0xca09a08e723 := seed 176442950 rfl
lemma f3196 : H a 0xc909908d723 := seed 176442951 rfl
lemma f3197 : H a 0x891851815723 := seed 415272519 rfl
lemma f3198 : H a 0x8c20d20c6723 := seed 4337307206 rfl
lemma f3199 : H a 0x8c20d20ca723 := seed 4345695814 rfl
lemma f3200 : H a 0x851849845723 := seed 63049287 rfl
end BorsukCert

namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f3201 : H a 0x8c2892886723 := seed 180620870 rfl
lemma f3202 : H a 0x8c289288a723 := seed 189009478 rfl
lemma f3203 : H a 20417993507 := seed 63045 rfl
lemma f3204 : H a 19612883747 := seed 161349 rfl
lemma f3205 : H a 18556185379 := seed 292420 rfl
lemma f3206 : H a 3527469859 := seed 2127428 rfl
lemma f3207 : H a 3510688547 := seed 2127429 rfl
lemma f3208 : H a 19495480099 := seed 177732 rfl
lemma f3209 : H a 19478698787 := seed 177733 rfl
lemma f3210 : H a 3393284899 := seed 2143812 rfl
lemma f3211 : H a 3376503587 := seed 2143813 rfl
lemma f3212 : H a 17616890659 := seed 407108 rfl
lemma f3213 : H a 17600109347 := seed 407109 rfl
lemma f3214 : H a 2588175139 := seed 2242116 rfl
lemma f3215 : H a 1514695459 := seed 2373188 rfl
lemma f3216 : H a 1497914147 := seed 2373189 rfl
lemma f3217 : H a 71263389342499 := seed 2315286087 rfl
lemma f3218 : H a 71264463084323 := seed 2449503815 rfl
lemma f3219 : H a 71814353115939 := seed 2432742983 rfl
lemma f3220 : H a 79595512589091 := seed 421541446 rfl
lemma f3221 : H a 0x9905901db23 := seed 411096647 rfl
lemma f3222 : H a 72088224389923 := seed 2290144839 rfl
lemma f3223 : H a 72089298131747 := seed 2424362567 rfl
lemma f3224 : H a 72158034635555 := seed 2550191686 rfl
lemma f3225 : H a 75386759469859 := seed 2189579847 rfl
lemma f3226 : H a 0xc909908db23 := seed 176444999 rfl
lemma f3227 : H a 75471605787427 := seed 178280006 rfl
lemma f3228 : H a 79869652298531 := seed 312497734 rfl
lemma f3229 : H a 76005251574563 := seed 2172819014 rfl
lemma f3230 : H a 75938528598819 := seed 2432865863 rfl
lemma f3231 : H a 0xd10c90c5b23 := seed 59119175 rfl
lemma f3232 : H a 83703712475939 := seed 2173048390 rfl
lemma f3233 : H a 83703846693667 := seed 2189825606 rfl
lemma f3234 : H a 83703846710051 := seed 2198214214 rfl
lemma f3235 : H a 80352551394083 := seed 61085255 rfl
lemma f3236 : H a 83719822535459 := seed 161748550 rfl
lemma f3237 : H a 83719956753187 := seed 178525766 rfl
lemma f3238 : H a 11828059427 := seed 64069 rfl
lemma f3239 : H a 9966251299 := seed 293444 rfl
lemma f3240 : H a 3508591907 := seed 1079877 rfl
lemma f3241 : H a 10905546019 := seed 178756 rfl
lemma f3242 : H a 9026956579 := seed 408132 rfl
lemma f3243 : H a 9010175267 := seed 408133 rfl
lemma f3244 : H a 2586078499 := seed 1194564 rfl
lemma f3245 : H a 1512598819 := seed 1325636 rfl
lemma f3246 : H a 1495817507 := seed 1325637 rfl
lemma f3247 : H a 36079017254179 := seed 1241545287 rfl
lemma f3248 : H a 36628907285795 := seed 1224784455 rfl
lemma f3249 : H a 36629981027619 := seed 1359002183 rfl
lemma f3250 : H a 36904926043427 := seed 1350621767 rfl
lemma f3251 : H a 0xc905904dd23 := seed 310532679 rfl
lemma f3252 : H a 45220000001315 := seed 1099209286 rfl
lemma f3253 : H a 40759661255971 := seed 160471623 rfl
lemma f3254 : H a 40760466758947 := seed 59906631 rfl
lemma f3255 : H a 7533092387 := seed 64581 rfl
lemma f3256 : H a 6744763939 := seed 162884 rfl
lemma f3257 : H a 6727982627 := seed 162885 rfl
lemma f3258 : H a 5671284259 := seed 293956 rfl
lemma f3259 : H a 3524324899 := seed 556100 rfl
lemma f3260 : H a 3507543587 := seed 556101 rfl
lemma f3261 : H a 6593797667 := seed 179269 rfl
lemma f3262 : H a 5537099299 := seed 310340 rfl
lemma f3263 : H a 3373358627 := seed 572485 rfl
lemma f3264 : H a 4731989539 := seed 408644 rfl
lemma f3265 : H a 2585030179 := seed 670788 rfl
lemma f3266 : H a 1511550499 := seed 801860 rfl
lemma f3267 : H a 1494769187 := seed 801861 rfl
lemma f3268 : H a 9690738187811 := seed 436239431 rfl
lemma f3269 : H a 18486831210019 := seed 704674887 rfl
lemma f3270 : H a 18556641406499 := seed 939555910 rfl
lemma f3271 : H a 19037794983459 := seed 822131783 rfl
lemma f3272 : H a 0xc605604ee23 := seed 318913606 rfl
lemma f3273 : H a 22335256321571 := seed 587349063 rfl
lemma f3274 : H a 22405871627811 := seed 822230086 rfl
lemma f3275 : H a 22405871660579 := seed 839007302 rfl
lemma f3276 : H a 19311666257443 := seed 679533639 rfl
lemma f3277 : H a 19312739999267 := seed 813751367 rfl
lemma f3278 : H a 22678937595427 := seed 578968646 rfl
lemma f3279 : H a 22612080385571 := seed 813849671 rfl
lemma f3280 : H a 23159957184035 := seed 562207815 rfl
lemma f3281 : H a 27627813957155 := seed 562338886 rfl
lemma f3282 : H a 27560017223203 := seed 679779399 rfl
lemma f3283 : H a 23163179195939 := seed 159947847 rfl
lemma f3284 : H a 27630901489187 := seed 411606086 rfl
lemma f3285 : H a 27562165247523 := seed 419994695 rfl
lemma f3286 : H a 30927154343459 := seed 562437190 rfl
lemma f3287 : H a 30927288561187 := seed 579214406 rfl
lemma f3288 : H a 23163984698915 := seed 59382855 rfl
lemma f3289 : H a 27563105213987 := seed 59513927 rfl
lemma f3290 : H a 30930510573091 := seed 176954438 rfl
lemma f3291 : H a 30930510589475 := seed 185343046 rfl
lemma f3292 : H a 71262852469699 := seed 2248173447 rfl
lemma f3293 : H a 71812742501315 := seed 2231412615 rfl
lemma f3294 : H a 72912254194627 := seed 2197890951 rfl
lemma f3295 : H a 72997637514179 := seed 119547782 rfl
lemma f3296 : H a 36078480381379 := seed 1174432647 rfl
lemma f3297 : H a 36628370412995 := seed 1157671815 rfl
lemma f3298 : H a 37727882106307 := seed 1124150151 rfl
lemma f3299 : H a 37804673394115 := seed 118500230 rfl
lemma f3300 : H a 36078480382403 := seed 1174434695 rfl
lemma f3301 : H a 36628370414019 := seed 1157673863 rfl
lemma f3302 : H a 37727882107331 := seed 1124152199 rfl
lemma f3303 : H a 37804673395139 := seed 118502278 rfl
lemma f3304 : H a 18486294337219 := seed 637562247 rfl
lemma f3305 : H a 19036184368835 := seed 620801415 rfl
lemma f3306 : H a 20135696062147 := seed 587279751 rfl
lemma f3307 : H a 20208191334083 := seed 117976454 rfl
lemma f3308 : H a 18486294338243 := seed 637564295 rfl
lemma f3309 : H a 19036184369859 := seed 620803463 rfl
lemma f3310 : H a 20135696063171 := seed 587281799 rfl
lemma f3311 : H a 20208191335107 := seed 117978502 rfl
lemma f3312 : H a 18486294338755 := seed 637565319 rfl
lemma f3313 : H a 19036184370371 := seed 620804487 rfl
lemma f3314 : H a 20135696063683 := seed 587282823 rfl
lemma f3315 : H a 20208191335619 := seed 117979526 rfl
lemma f3316 : H a 9690201315139 := seed 369127047 rfl
lemma f3317 : H a 0x9503501d743 := seed 352366215 rfl
lemma f3318 : H a 0xa503502d743 := seed 318844551 rfl
lemma f3319 : H a 0xa609608e743 := seed 117714566 rfl
lemma f3320 : H a 9690201316163 := seed 369129095 rfl
lemma f3321 : H a 0x9503501db43 := seed 352368263 rfl
lemma f3322 : H a 0xa503502db43 := seed 318846599 rfl
lemma f3323 : H a 0xa609608eb43 := seed 117716614 rfl
lemma f3324 : H a 9690201316675 := seed 369130119 rfl
lemma f3325 : H a 0x9503501dd43 := seed 352369287 rfl
lemma f3326 : H a 0xa503502dd43 := seed 318847623 rfl
lemma f3327 : H a 0xa609608ed43 := seed 117717638 rfl
lemma f3328 : H a 9690201316931 := seed 369130631 rfl
lemma f3329 : H a 0x9503501de43 := seed 352369799 rfl
lemma f3330 : H a 0xa503502de43 := seed 318848135 rfl
lemma f3331 : H a 0xa609608ee43 := seed 117718150 rfl
lemma f3332 : H a 5292154804099 := seed 234909447 rfl
lemma f3333 : H a 5842044835715 := seed 218148615 rfl
lemma f3334 : H a 6941556529027 := seed 184626951 rfl
lemma f3335 : H a 7010829789059 := seed 117583622 rfl
lemma f3336 : H a 5292154805123 := seed 234911495 rfl
lemma f3337 : H a 5842044836739 := seed 218150663 rfl
lemma f3338 : H a 6941556530051 := seed 184628999 rfl
lemma f3339 : H a 7010829790083 := seed 117585670 rfl
lemma f3340 : H a 5292154805635 := seed 234912519 rfl
lemma f3341 : H a 5842044837251 := seed 218151687 rfl
lemma f3342 : H a 6941556530563 := seed 184630023 rfl
lemma f3343 : H a 7010829790595 := seed 117586694 rfl
lemma f3344 : H a 5292154805891 := seed 234913031 rfl
lemma f3345 : H a 5842044837507 := seed 218152199 rfl
lemma f3346 : H a 6941556530819 := seed 184630535 rfl
lemma f3347 : H a 7010829790851 := seed 117587206 rfl
lemma f3348 : H a 5292154806019 := seed 234913287 rfl
lemma f3349 : H a 5842044837635 := seed 218152455 rfl
lemma f3350 : H a 6941556530947 := seed 184630791 rfl
lemma f3351 : H a 7010829790979 := seed 117587462 rfl
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3352 : H a 30 := rup [pack f1,pack f2] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3353 : H a 46 := rup [pack f1,pack f4] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3354 : H a 54 := rup [pack f1,pack f41] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3355 : H a 58 := rup [pack f1,pack f227] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3356 : H a 3843 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3348,pack f3349,pack f3350,pack f3351] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3357 : H a 3715 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3344,pack f3345,pack f3346,pack f3347] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3358 : H a 3459 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3340,pack f3341,pack f3342,pack f3343] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3359 : H a 2947 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3336,pack f3337,pack f3338,pack f3339] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3360 : H a 1923 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3332,pack f3333,pack f3334,pack f3335] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3361 : H a 3651 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3328,pack f3329,pack f3330,pack f3331] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3362 : H a 3395 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3324,pack f3325,pack f3326,pack f3327] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3363 : H a 2883 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3320,pack f3321,pack f3322,pack f3323] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3364 : H a 1859 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3316,pack f3317,pack f3318,pack f3319] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3365 : H a 3267 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3312,pack f3313,pack f3314,pack f3315] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3366 : H a 2755 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3308,pack f3309,pack f3310,pack f3311] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3367 : H a 1731 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3304,pack f3305,pack f3306,pack f3307] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3368 : H a 2499 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3300,pack f3301,pack f3302,pack f3303] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3369 : H a 1475 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3296,pack f3297,pack f3298,pack f3299] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3370 : H a 963 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3292,pack f3293,pack f3294,pack f3295] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3371 : H a 0x17415c1d4151158954554 := rup [pack f1,pack f479,pack f482] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3372 : H a 0x1d415115c1582852891742a1 := rup [pack f1,pack f2792,pack f2801,pack f3371] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3373 : H a 1306672419 := rup [pack f1,pack f3353,pack f3352,pack f3356,pack f3358,pack f3362,pack f3255,pack f3257,pack f3291,pack f3261,pack f48,pack f3290,pack f3267,pack f233,pack f3269,pack f3259,pack f20,pack f3268,pack f3258,pack f12,pack f777,pack f2719,pack f769,pack f3247,pack f3239,pack f3245,pack f3241,pack f894,pack f999,pack f2549,pack f1012,pack f1028,pack f5,pack f96,pack f2900,pack f3372,pack f2520,pack f1835,pack f770] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3374 : H a 0xe23192d24c34c64ca4382 := rup [pack f1,pack f3352,pack f3255,pack f1558,pack f2292,pack f647] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3375 : H a 0xc92cc1cc0dc0d08cc0ec := rup [pack f1,pack f333,pack f339] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3376 : H a 0xe011c21890d08901510560dcc8c341072d018acc27 := rup [pack f1,pack f3354,pack f2305,pack f782,pack f2293,pack f126,pack f221,pack f1547,pack f1553,pack f2002,pack f2464,pack f2079,pack f2444,pack f389,pack f3375] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3377 : H a 0xc52c81c80d80d08c80e8 := rup [pack f1,pack f136,pack f143] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3378 : H a 0xe2319210e0d0890151d2420e474874c64c82 := rup [pack f1,pack f3352,pack f3355,pack f3255,pack f2705,pack f3291,pack f3261,pack f47,pack f3290,pack f3267,pack f232,pack f777,pack f1140,pack f1851,pack f1560,pack f744,pack f746,pack f750,pack f787,pack f2559,pack f2549,pack f3374,pack f438,pack f798,pack f856,pack f436,pack f888,pack f1486,pack f2177,pack f1572,pack f3376,pack f647,pack f318,pack f431,pack f2256,pack f2266,pack f2268,pack f2274,pack f1326,pack f1778,pack f1400,pack f1746,pack f189,pack f3377] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3379 : H a 0x4de2320e0c6ca4 := rup [pack f1,pack f3352,pack f3357,pack f3358,pack f3365,pack f777,pack f3257,pack f3269,pack f3268,pack f13,pack f17,pack f3258,pack f3373,pack f2570,pack f2579,pack f3058,pack f3378,pack f894,pack f781,pack f3264,pack f1544,pack f3255,pack f3291,pack f3261,pack f3275,pack f2558,pack f2544,pack f3290,pack f1851,pack f1140,pack f440,pack f436,pack f2705,pack f3267,pack f647,pack f2264,pack f2266,pack f2877,pack f2491,pack f1805,pack f743] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3380 : H a 5352118608070 := rup [pack f1,pack f3352,pack f3269,pack f3268,pack f2579,pack f2570,pack f777,pack f3257,pack f13,pack f17,pack f3258,pack f3373,pack f3058,pack f3378,pack f894,pack f2558,pack f3255,pack f3291,pack f1140,pack f3290,pack f1851,pack f2544,pack f440,pack f2643,pack f3261,pack f3267,pack f2588,pack f3264,pack f3286,pack f1887,pack f3275,pack f3283,pack f1164,pack f1866,pack f3379,pack f3154,pack f3162,pack f2675,pack f2686,pack f1916,pack f1939,pack f452,pack f228] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3381 : H a 0xc605a1c21190c90d114504d18509a10e116ca45a40952c113c43b := rup [pack f1,pack f3352,pack f1508,pack f1544,pack f19,pack f241,pack f233,pack f1908,pack f1910,pack f1913,pack f1915,pack f1916,pack f1917,pack f2935,pack f2603,pack f1010,pack f1189,pack f2101,pack f2567,pack f2151,pack f3013,pack f3122,pack f3055,pack f1523,pack f581,pack f121,pack f118,pack f560,pack f579,pack f558,pack f2016,pack f2035,pack f254,pack f245] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3382 : H a 0xd00780c605aa21e011c20c914520d18515159410e1165a42c127417483b := rup [pack f1,pack f3354,pack f3358,pack f3360,pack f3369,pack f1081,pack f1991,pack f2293,pack f232,pack f231,pack f322,pack f469,pack f1924,pack f1926,pack f1929,pack f1934,pack f1935,pack f1939,pack f1738,pack f2451,pack f2332,pack f791,pack f2574,pack f793,pack f2075,pack f2547,pack f721,pack f3375,pack f2161,pack f2568,pack f436,pack f337,pack f2481,pack f380] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3383 : H a 0x780c60c904d14a13808e333 := rup [pack f1,pack f2643,pack f2644,pack f2647,pack f2653,pack f2655,pack f787,pack f1175,pack f798,pack f1156,pack f1210,pack f1192,pack f42] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3384 : H a 0xc620d08e245533 := rup [pack f1,pack f2671,pack f2673] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3385 : H a 0xc611920d1b413808eca4c9415133417413b := rup [pack f1,pack f3357,pack f3358,pack f3365,pack f451,pack f1807,pack f747,pack f743,pack f1879,pack f3384,pack f452,pack f2684,pack f2685] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3386 : H a 0xd00c6e2304d1742c1 := rup [pack f1,pack f3353,pack f3352,pack f3264,pack f3380,pack f777,pack f2588,pack f3255,pack f3286,pack f1164,pack f3268,pack f3165,pack f2875,pack f3263,pack f3257,pack f3284,pack f3279,pack f3277,pack f3265,pack f3273,pack f45,pack f3383,pack f3385,pack f3087,pack f3281,pack f636,pack f2832,pack f239,pack f3276,pack f3266,pack f231,pack f3287,pack f3260,pack f782,pack f3381,pack f2558,pack f1887,pack f228,pack f3382] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3387 : H a 0xd00c6e2304d174 := rup [pack f1,pack f3352,pack f3264,pack f3277,pack f3265,pack f3273,pack f45,pack f3380,pack f3165,pack f3268,pack f17,pack f3255,pack f3286,pack f3263,pack f3257,pack f3284,pack f3291,pack f3373,pack f3276,pack f232,pack f231,pack f3287,pack f3260,pack f777,pack f3386,pack f781,pack f799,pack f801,pack f2704,pack f2286,pack f892,pack f894,pack f2545,pack f784,pack f786,pack f710,pack f746,pack f787,pack f2559,pack f2566,pack f2573,pack f2177,pack f647,pack f436,pack f3376] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3388 : H a 0xd02c80c6e2304d := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3357,pack f3361,pack f3356,pack f3358,pack f3362,pack f3366,pack f3367,pack f3370,pack f3264,pack f3277,pack f3265,pack f242,pack f3276,pack f3266,pack f3255,pack f3287,pack f3260,pack f646,pack f1104,pack f3286,pack f3263,pack f3257,pack f3268,pack f3373,pack f3380,pack f3279,pack f3273,pack f3281,pack f3284,pack f15,pack f2903,pack f343,pack f3387,pack f439,pack f453,pack f542,pack f2550,pack f1137,pack f1849,pack f2542,pack f2457,pack f2466,pack f2488,pack f787,pack f2191,pack f778,pack f2289,pack f2067,pack f535,pack f2910,pack f2914,pack f2912,pack f2911,pack f2141,pack f1843,pack f2013,pack f2502,pack f2511,pack f2528,pack f2398,pack f396,pack f764,pack f428,pack f370,pack f781,pack f2929,pack f2732,pack f653] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3389 : H a 0xe231190d111619114920dc54d02c282b4c82 := rup [pack f1,pack f3352,pack f3361,pack f3362,pack f3365,pack f3240,pack f3049,pack f777,pack f1151,pack f3285,pack f3277,pack f3265,pack f239,pack f750,pack f787,pack f888,pack f2612,pack f2636,pack f2712,pack f2590,pack f647,pack f445,pack f2269,pack f2279,pack f444,pack f2396,pack f1693,pack f706] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3390 : H a 0xc6e2305514918ac64d24c28c81c2cca4 := rup [pack f1,pack f3352,pack f3357,pack f3358,pack f3365,pack f3264,pack f3277,pack f3265,pack f647,pack f2706,pack f2707,pack f1801,pack f2486,pack f749,pack f743] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3391 : H a 0xe80c6e2304e20d2c1 := rup [pack f1,pack f3353,pack f3352,pack f3255,pack f3287,pack f3260,pack f3270,pack f2823,pack f3240,pack f3256,pack f3049,pack f777,pack f3264,pack f3276,pack f3278,pack f1151,pack f3285,pack f3266,pack f3289,pack f3272,pack f7,pack f3277,pack f3265,pack f990,pack f3286,pack f3263,pack f1164,pack f782,pack f1544,pack f1508,pack f1519,pack f2599,pack f1411,pack f3389,pack f788,pack f890,pack f1176,pack f2291,pack f1494,pack f3390,pack f3149,pack f3154,pack f3159,pack f1428,pack f1442,pack f1198,pack f1219,pack f1451,pack f42,pack f104,pack f97] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3392 : H a 0xe80c6e2304e20d := rup [pack f1,pack f3352,pack f3353,pack f3356,pack f3358,pack f3362,pack f777,pack f3264,pack f3276,pack f3278,pack f1151,pack f3266,pack f3256,pack f3289,pack f3255,pack f3287,pack f3260,pack f3270,pack f3272,pack f3277,pack f239,pack f3049,pack f3240,pack f2904,pack f3391,pack f781,pack f799,pack f801,pack f2704,pack f2286,pack f892,pack f894,pack f2545,pack f784,pack f786,pack f2600,pack f750,pack f2602,pack f2631,pack f647,pack f446,pack f1545,pack f1546,pack f444,pack f1837,pack f2530,pack f764] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3393 : H a 0xe230c90d119105508d18a152c34ca4d01c2c0b2d24 := rup [pack f1,pack f3356,pack f3358,pack f3362,pack f777,pack f892,pack f710,pack f647,pack f1545,pack f1546,pack f1548,pack f1837,pack f2530,pack f2906,pack f764] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3394 : H a 3336712898 := rup [pack f1,pack f3352,pack f3255,pack f3287,pack f3260,pack f137,pack f140,pack f3388,pack f138,pack f3392,pack f3166,pack f2633,pack f2609,pack f2705,pack f28,pack f777,pack f3264,pack f3276,pack f3278,pack f1151,pack f3272,pack f2124,pack f3256,pack f3282,pack f3285,pack f3266,pack f3289,pack f3277,pack f239,pack f3270,pack f3274,pack f7,pack f990,pack f2916,pack f3286,pack f657,pack f781,pack f2286,pack f892,pack f2138,pack f2600,pack f2589,pack f445,pack f444,pack f3393,pack f3242,pack f3244,pack f3252,pack f2957,pack f2943,pack f2155,pack f2186,pack f1029,pack f1013,pack f536,pack f292,pack f5] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3395 : H a 0xc909a13811614508d07c18517423c1b4c63 := rup [pack f1,pack f239,pack f710,pack f3051,pack f3055,pack f2645,pack f2676,pack f2687,pack f1916,pack f1939,pack f452,pack f228] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3396 : H a 814627 := rup [pack f1,pack f3352,pack f3361,pack f3362,pack f3365,pack f140,pack f138,pack f137,pack f777,pack f3255,pack f3264,pack f3286,pack f3287,pack f3388,pack f3276,pack f3277,pack f1164,pack f3263,pack f3260,pack f3256,pack f3272,pack f3274,pack f3278,pack f3270,pack f3392,pack f231,pack f3266,pack f239,pack f3285,pack f1151,pack f2548,pack f2705,pack f2609,pack f2633,pack f3166,pack f3394,pack f782,pack f3238,pack f1544,pack f2599,pack f2544,pack f1887,pack f446,pack f444,pack f3395,pack f647,pack f2254,pack f2267,pack f2269,pack f2278,pack f797,pack f2824,pack f2396,pack f1692,pack f706] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3397 : H a 48940098339532 := rup [pack f1,pack f3366,pack f3367,pack f3370,pack f658,pack f653] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3398 : H a 0x51031091013012019010d := rup [pack f1,pack f18,pack f23] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3399 : H a 0x120261292130310510910c63 := rup [pack f1,pack f561,pack f570,pack f3048,pack f1069,pack f3398] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3400 : H a 0xc6d02c2bca41c2 := rup [pack f1,pack f3353,pack f3370,pack f3367,pack f3366,pack f331,pack f318,pack f2736,pack f140,pack f781,pack f3397,pack f655,pack f553,pack f538,pack f349,pack f336,pack f639,pack f928,pack f2261,pack f769,pack f3396,pack f779,pack f2259,pack f2283,pack f2281,pack f2282,pack f990,pack f1104,pack f2265,pack f1552,pack f1115,pack f1122,pack f3399,pack f2708,pack f640] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3401 : H a 0xc6d02c2bca4 := rup [pack f1,pack f3353,pack f3370,pack f3367,pack f3366,pack f331,pack f318,pack f2736,pack f140,pack f781,pack f3397,pack f655,pack f553,pack f538,pack f336,pack f639,pack f928,pack f2258,pack f769,pack f3396,pack f3400,pack f1554,pack f2711,pack f780,pack f800,pack f802,pack f2260,pack f2288,pack f640,pack f1877,pack f2017,pack f2272,pack f989,pack f1107,pack f561,pack f570,pack f3050,pack f1121,pack f1069,pack f1977,pack f2034,pack f1114,pack f2023,pack f3398,pack f250,pack f245,pack f3063] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3402 : H a 48507395058731 := rup [pack f1,pack f3352,pack f779,pack f802,pack f800,pack f2203,pack f1500,pack f476,pack f783,pack f782,pack f893,pack f2961,pack f891,pack f3069,pack f798,pack f431,pack f639,pack f2287,pack f3401,pack f2253,pack f2664,pack f1259,pack f1243,pack f3198,pack f3233,pack f590,pack f3153,pack f598,pack f897,pack f1272,pack f1288,pack f46,pack f43] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3403 : H a 32168249967048 := rup [pack f1,pack f3370,pack f3369,pack f3368,pack f648,pack f652] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3404 : H a 7534890035 := rup [pack f1,pack f3355,pack f3354,pack f466,pack f475,pack f1567,pack f2302,pack f3403] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3405 : H a 0xe24c340e1d24c2cc28420820b01220ca3 := rup [pack f1,pack f590,pack f596,pack f644,pack f897,pack f930,pack f561,pack f3,pack f912] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3406 : H a 0xe020d21c82c1 := rup [pack f1,pack f3370,pack f3369,pack f3368,pack f3352,pack f779,pack f477,pack f3403,pack f335,pack f650,pack f537,pack f1377,pack f1370,pack f573,pack f362,pack f3404,pack f777,pack f782,pack f3238,pack f800,pack f3402,pack f1554,pack f954,pack f973,pack f891,pack f783,pack f1178,pack f938,pack f3405,pack f642,pack f638,pack f2294,pack f2918,pack f1260,pack f1304,pack f73,pack f66] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3407 : H a 0xe02c341cb1e3238220ca4c64c2cc82 := rup [pack f1,pack f779,pack f335,pack f537,pack f1377,pack f1370,pack f342,pack f777,pack f787,pack f1556,pack f645,pack f638,pack f2294,pack f2918,pack f1258,pack f1344,pack f72,pack f66] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3408 : H a 0xe02c341cb1e3d01ca4c64c2c := rup [pack f1,pack f537,pack f933,pack f335,pack f1174,pack f779,pack f1377,pack f1370,pack f362,pack f777,pack f3407,pack f889,pack f797,pack f1557,pack f645,pack f638,pack f2294,pack f2918,pack f1303,pack f1342,pack f70,pack f66] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3409 : H a 0xe020d21c8ca4c64 := rup [pack f1,pack f3370,pack f3369,pack f3368,pack f3406,pack f781,pack f779,pack f477,pack f3403,pack f335,pack f650,pack f537,pack f1389,pack f573,pack f362,pack f3404,pack f777,pack f772,pack f3408,pack f2285,pack f2262,pack f2260,pack f2280,pack f1547,pack f1136,pack f640,pack f3243,pack f2922,pack f2299,pack f1808,pack f1694,pack f225,pack f220] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3410 : H a 0xe020d21c8ca4 := rup [pack f1,pack f3370,pack f3369,pack f3368,pack f3352,pack f477,pack f779,pack f3403,pack f650,pack f537,pack f3406,pack f781,pack f933,pack f544,pack f362,pack f342,pack f335,pack f3404,pack f476,pack f777,pack f773,pack f3409,pack f561,pack f570,pack f641,pack f710,pack f3047,pack f3053,pack f1301,pack f1131,pack f969,pack f2051,pack f1127,pack f950,pack f2040,pack f929,pack f915,pack f889,pack f841,pack f840,pack f2917,pack f3,pack f787,pack f790,pack f792,pack f1297,pack f1162,pack f6,pack f230,pack f901,pack f902,pack f1556,pack f1318,pack f1330,pack f3251,pack f52,pack f642,pack f2272,pack f2275,pack f2236,pack f2228,pack f2376,pack f2373,pack f2462,pack f2447,pack f3049,pack f426,pack f417,pack f413,pack f419,pack f2926] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3411 : H a 60163957192 := rup [pack f1,pack f3368,pack f3369,pack f3370,pack f3352,pack f477,pack f476,pack f779,pack f777,pack f3403,pack f335,pack f342,pack f362,pack f650,pack f537,pack f573,pack f3406,pack f781,pack f933,pack f3410,pack f590,pack f596,pack f643,pack f750,pack f3148,pack f3157,pack f1253,pack f970,pack f951,pack f930,pack f903,pack f889,pack f813,pack f814,pack f2917,pack f3,pack f797,pack f794,pack f796,pack f1243,pack f1150,pack f11,pack f238,pack f911,pack f1266,pack f1284,pack f2692,pack f2701,pack f3196,pack f3226,pack f1526,pack f1537,pack f3019,pack f3042,pack f43,pack f2227,pack f2234,pack f625,pack f624,pack f634,pack f628,pack f917] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3412 : H a 0xd01d24d14d08 := rup [pack f1,pack f3356,pack f3358,pack f3362,pack f767,pack f764] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3413 : H a 57738339337044 := rup [pack f1,pack f3370,pack f3364,pack f3363,pack f669,pack f677] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3414 : H a 0xa2ca21b24a34e24a28aa4 := rup [pack f1,pack f628,pack f632] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3415 : H a 0xd8060158055858458258 := rup [pack f1,pack f43,pack f46] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3416 : H a 0xd0256485728954c077702 := rup [pack f1,pack f3362,pack f3364,pack f3369,pack f866,pack f1275,pack f1142,pack f1638,pack f2789,pack f678] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3417 : H a 0x56485728954c077701541 := rup [pack f1,pack f3362,pack f3364,pack f3369,pack f864,pack f1278,pack f1145,pack f1639,pack f2790,pack f678] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3418 : H a 0x29028938c2ac68ca8c29c := rup [pack f1,pack f366,pack f370] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3419 : H a 0xd0252285754c077 := rup [pack f1,pack f3354,pack f51,pack f92,pack f2452,pack f2412,pack f1280,pack f608,pack f3416,pack f1276,pack f1143,pack f295,pack f391,pack f3417,pack f1990,pack f1076,pack f3418] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3420 : H a 8745643 := rup [pack f1,pack f492,pack f167,pack f92,pack f51,pack f2142,pack f2144,pack f2145,pack f2146] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3421 : H a 90333214524048 := rup [pack f1,pack f3354,pack f3420,pack f51,pack f92,pack f2452,pack f2412,pack f1280,pack f3418,pack f374,pack f424,pack f739,pack f2461,pack f336,pack f349,pack f2305,pack f1199,pack f1172,pack f2355,pack f865,pack f866,pack f1206,pack f3419,pack f796,pack f1292,pack f1153,pack f1188,pack f42] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3422 : H a 90333214472843 := rup [pack f1,pack f3353,pack f3356,pack f3358,pack f3362,pack f3354,pack f15,pack f31,pack f2904,pack f3420,pack f167,pack f92,pack f51,pack f613,pack f2461,pack f2469,pack f2470,pack f1076,pack f2465,pack f2076,pack f2099,pack f2463,pack f3412,pack f208,pack f224,pack f765,pack f1870,pack f1896,pack f2156,pack f2230,pack f2131,pack f2200,pack f2526,pack f2527,pack f2531,pack f2532,pack f2236,pack f2180,pack f1842,pack f310,pack f292,pack f291,pack f1840,pack f309] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3423 : H a 0x5222cb541096701 := rup [pack f1,pack f3354,pack f2376,pack f2305,pack f2088,pack f790,pack f786,pack f864,pack f853,pack f850,pack f1961,pack f1053,pack f2338,pack f2372,pack f350] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3424 : H a 90333214523542 := rup [pack f1,pack f3353,pack f3354,pack f3362,pack f3364,pack f3369,pack f3421,pack f51,pack f92,pack f2452,pack f2412,pack f3420,pack f3422,pack f367,pack f2305,pack f2310,pack f2306,pack f468,pack f2308,pack f77,pack f2307,pack f59,pack f1076,pack f15,pack f31,pack f2785,pack f1280,pack f608,pack f53,pack f3423,pack f785,pack f1275,pack f1291,pack f1180,pack f1282,pack f1281,pack f42,pack f1147,pack f3416,pack f1638,pack f682] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3425 : H a 22054007452 := rup [pack f1,pack f3353,pack f3354,pack f3362,pack f3364,pack f3369,pack f3420,pack f51,pack f92,pack f2452,pack f2412,pack f608,pack f3421,pack f15,pack f31,pack f2785,pack f3422,pack f367,pack f2305,pack f1076,pack f3424,pack f2361,pack f680,pack f678] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3426 : H a 92931890615628 := rup [pack f1,pack f3369,pack f3364,pack f3362,pack f678,pack f684] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3427 : H a 22054010114 := rup [pack f1,pack f3355,pack f3362,pack f3364,pack f3369,pack f3425,pack f261,pack f242,pack f1633,pack f492,pack f167,pack f92,pack f608,pack f1981,pack f1989,pack f1990,pack f1986,pack f1984,pack f790,pack f1776,pack f1983,pack f3426,pack f344,pack f402,pack f682,pack f2356,pack f1298,pack f1460,pack f483,pack f2365,pack f1072,pack f2358,pack f2783,pack f1702,pack f1769,pack f174,pack f173] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3428 : H a 0x505528548708518d08588 := rup [pack f1,pack f199,pack f200] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3429 : H a 5384279 := rup [pack f1,pack f3355,pack f3356,pack f3358,pack f3362,pack f3354,pack f613,pack f607,pack f51,pack f92,pack f492,pack f2412,pack f2452,pack f3420,pack f3425,pack f242,pack f261,pack f1633,pack f1838,pack f3427,pack f2305,pack f3412,pack f525,pack f534,pack f768,pack f1075,pack f2526,pack f2527,pack f368,pack f2521,pack f2522,pack f391,pack f2461,pack f2469,pack f2465,pack f1348,pack f2907,pack f1984,pack f1734,pack f1827,pack f3428] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3430 : H a 0x23c32c2ac26ca2c22962c := rup [pack f1,pack f309,pack f310] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3431 : H a 0xec4ac0bc0a98ac2ac1ac := rup [pack f1,pack f291,pack f292] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3432 : H a 0xa64a4ca41a48 := rup [pack f1,pack f3361,pack f3363,pack f3366,pack f703,pack f697] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3433 : H a 0x52c5a4534521724528d24 := rup [pack f1,pack f606,pack f609] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3434 : H a 45141488947 := rup [pack f1,pack f698,pack f215,pack f169,pack f159,pack f2665,pack f2667,pack f2670,pack f2672,pack f2674] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3435 : H a 0xa88a94aa4a81 := rup [pack f1,pack f3366,pack f3359,pack f3357,pack f738,pack f740] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3436 : H a 0x8d4891a94898c948b4994 := rup [pack f1,pack f510,pack f511] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3437 : H a 0xc94ca4c88c81 := rup [pack f1,pack f3365,pack f3358,pack f3357,pack f743,pack f747] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3438 : H a 0x11915c51c12013c31c91c := rup [pack f1,pack f252,pack f245] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3439 : H a 0x708610e08605648688628 := rup [pack f1,pack f209,pack f210] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3440 : H a 0x610708605648688e08 := rup [pack f1,pack f3368,pack f3359,pack f3358,pack f3363,pack f3362,pack f3366,pack f3365,pack f3370,pack f3369,pack f3352,pack f3354,pack f3353,pack f3439,pack f114,pack f125,pack f211,pack f2334,pack f2724,pack f2744,pack f2798,pack f2849,pack f2370,pack f2443,pack f2300,pack f74,pack f83,pack f2956,pack f2923,pack f3007,pack f3108,pack f668,pack f649,pack f688,pack f727,pack f667,pack f3403,pack f686,pack f726,pack f785,pack f871,pack f809,pack f867] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3441 : H a 0x99498c981988 := rup [pack f1,pack f3358,pack f3359,pack f3368,pack f729,pack f726] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3442 : H a 0xe0119c99498c98183b190588198581 := rup [pack f1,pack f3353,pack f3354,pack f3358,pack f3360,pack f3369,pack f794,pack f2293,pack f2719,pack f796,pack f839,pack f1928,pack f2595,pack f2133,pack f713,pack f714,pack f364,pack f500,pack f725,pack f717] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3443 : H a 62137644356500 := rup [pack f1,pack f3370,pack f3360,pack f3359,pack f711,pack f716] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3444 : H a 0x89c83c85ca1cc1c81991c := rup [pack f1,pack f270,pack f272] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3445 : H a 0xa2cc2c8298ac86c83c92c := rup [pack f1,pack f319,pack f321] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3446 : H a 0x8aba2b981e01 := rup [pack f1,pack f794,pack f2178,pack f2239,pack f783,pack f870,pack f791,pack f780,pack f882,pack f2240,pack f2177,pack f2185] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3447 : H a 37239306625 := rup [pack f1,pack f794,pack f2178,pack f2239,pack f820,pack f3446,pack f779,pack f806,pack f2241,pack f2182] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3448 : H a 9091627 := rup [pack f1,pack f3355,pack f3353,pack f3352,pack f298,pack f314,pack f1839,pack f2905,pack f3447,pack f793,pack f2179,pack f2238,pack f784,pack f821,pack f875,pack f2236,pack f2180,pack f3412,pack f3249] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3449 : H a 0x8ab54864882f6415424c1 := rup [pack f1,pack f388,pack f594,pack f789,pack f1271,pack f1023,pack f825,pack f1033,pack f707,pack f797,pack f2188,pack f1060,pack f1430,pack f163,pack f161] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3450 : H a 0x8ab54864882f641542 := rup [pack f1,pack f3361,pack f3362,pack f3365,pack f298,pack f2180,pack f1023,pack f3449,pack f822,pack f1025,pack f1686,pack f2403,pack f3065,pack f709,pack f706] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3451 : H a 0x8ab54835471464882f641 := rup [pack f1,pack f2179,pack f1022,pack f63,pack f499,pack f3450,pack f821,pack f827,pack f2190,pack f1025,pack f2018,pack f2657,pack f517,pack f515] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3452 : H a 0xc48c64c41c4c := rup [pack f1,pack f3365,pack f3362,pack f3361,pack f706,pack f709] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3453 : H a 0xa982f6421154c2 := rup [pack f1,pack f1021,pack f824,pack f1025,pack f3064,pack f2401,pack f1686,pack f3452] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3454 : H a 0x8ab54864882f642541 := rup [pack f1,pack f298,pack f2178,pack f3453,pack f388,pack f594,pack f793,pack f1270,pack f1021,pack f823,pack f1032,pack f707,pack f797,pack f2189,pack f1058,pack f1429,pack f163,pack f161] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3455 : H a 0x83c829c2c86c92c8ab := rup [pack f1,pack f3353,pack f3355,pack f3352,pack f3354,pack f3361,pack f3362,pack f3365,pack f298,pack f388,pack f594,pack f1636,pack f2764,pack f2787,pack f2892,pack f2806,pack f1656,pack f3448,pack f326,pack f3451,pack f793,pack f2178,pack f1021,pack f1270,pack f3454,pack f789,pack f826,pack f2180,pack f1023,pack f2571,pack f1964,pack f3059,pack f2397,pack f1029,pack f3452,pack f478,pack f708,pack f490] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3456 : H a 0x83ca2b186c47 := rup [pack f1,pack f3355,pack f314,pack f222,pack f1690,pack f1691,pack f1688,pack f293,pack f302,pack f2249,pack f2250,pack f780,pack f1894,pack f796,pack f1850,pack f228,pack f1912] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3457 : H a 0xc41186c48192 := rup [pack f1,pack f798,pack f3067,pack f2404,pack f3452] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3458 : H a 0xa2182538238c1861901acc63 := rup [pack f1,pack f570,pack f641,pack f3066,pack f1978,pack f2435,pack f2303,pack f365,pack f359] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3459 : H a 0xa09a2180d825c411861a8190c481ac := rup [pack f1,pack f3352,pack f3354,pack f2407,pack f3069,pack f798,pack f3458,pack f3452,pack f358,pack f432,pack f2405,pack f2592,pack f3097,pack f2927,pack f576,pack f571] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3460 : H a 0x83c829a2b82fc41 := rup [pack f1,pack f3355,pack f128,pack f38,pack f629,pack f421,pack f798,pack f1019,pack f2243,pack f1455,pack f1068,pack f3456,pack f3457,pack f1654,pack f1022,pack f793,pack f3459,pack f294,pack f304,pack f361,pack f572,pack f2125,pack f2128,pack f2129,pack f1618,pack f1574,pack f1673,pack f1250,pack f1417,pack f1049,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3461 : H a 0x82f5881c81851901a8192 := rup [pack f1,pack f3355,pack f497,pack f1021,pack f1742,pack f171,pack f170] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3462 : H a 0x5484d44c855480dc4218f := rup [pack f1,pack f3352,pack f3362,pack f3364,pack f3365,pack f3367,pack f3369,pack f14,pack f24,pack f2990,pack f2941,pack f682,pack f663,pack f3426,pack f659,pack f822] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3463 : H a 0xa2b82f5484c8c483814584c2 := rup [pack f1,pack f1020,pack f783,pack f1025,pack f2248,pack f1432,pack f1061,pack f165,pack f161] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3464 : H a 84957813544140 := rup [pack f1,pack f3365,pack f3367,pack f3369,pack f666,pack f659] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3465 : H a 0xc2c82983c86c92c8ac := rup [pack f1,pack f3354,pack f3369,pack f3367,pack f3365,pack f3353,pack f3355,pack f3445,pack f314,pack f330,pack f1637,pack f1717,pack f2742,pack f1590,pack f2788,pack f2840,pack f1564,pack f2727,pack f38,pack f128,pack f3460,pack f707,pack f797,pack f1264,pack f1020,pack f2242,pack f3462,pack f3463,pack f2239,pack f1026,pack f62,pack f516,pack f3464,pack f2317,pack f2320,pack f663,pack f2316,pack f1974,pack f2937,pack f105,pack f2589,pack f3461,pack f501,pack f496] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3466 : H a 0x829c2c83c86c92c := rup [pack f1,pack f3455,pack f3465] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3467 : H a 39386789058 := rup [pack f1,pack f3353,pack f3355,pack f3352,pack f3354,pack f3365,pack f3366,pack f3368,pack f308,pack f314,pack f1691,pack f1603,pack f2745,pack f783,pack f2238,pack f2219,pack f3059,pack f2397,pack f2955,pack f2333,pack f3452,pack f667,pack f797,pack f785,pack f862] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3468 : H a 39386787990 := rup [pack f1,pack f3467,pack f2217,pack f2236,pack f821] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3469 : H a 35057220139 := rup [pack f1,pack f3353,pack f3365,pack f3367,pack f3369,pack f3355,pack f308,pack f1758,pack f2807,pack f2741,pack f1589,pack f1574,pack f617,pack f314,pack f629,pack f2788,pack f1265,pack f2825,pack f3467,pack f2220,pack f3464,pack f71,pack f2326,pack f2327,pack f2313,pack f663,pack f2314,pack f2938,pack f2939,pack f3468,pack f2218,pack f2237,pack f826,pack f1071,pack f1459,pack f798,pack f1696,pack f176,pack f173,pack f1963,pack f2569,pack f2223,pack f489] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3470 : H a 0x2c8688298394a229881a88984980d88b4a0a89c2a81b41901d459419c2905881c88d4c94542 := rup [pack f1,pack f633,pack f789,pack f914,pack f1155,pack f55,pack f501,pack f171,pack f512,pack f176,pack f3435] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3471 : H a 0x92b2c84c84d468882f4c1 := rup [pack f1,pack f3365,pack f3367,pack f3369,pack f3354,pack f3355,pack f128,pack f38,pack f617,pack f407,pack f308,pack f784,pack f2220,pack f1026,pack f3464,pack f71,pack f516,pack f2321,pack f2322,pack f2330,pack f353,pack f2326,pack f2325,pack f663,pack f2328,pack f2317,pack f2319,pack f1744,pack f1454,pack f2936,pack f1327,pack f1314,pack f1229,pack f2312,pack f2331,pack f472,pack f2323,pack f559,pack f2947,pack f2948,pack f2949,pack f2005,pack f111,pack f454,pack f24,pack f2725,pack f2839,pack f1975,pack f1073,pack f1731,pack f1568,pack f2746,pack f2887,pack f3470,pack f1776,pack f1032,pack f175,pack f173,pack f2223] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3472 : H a 0x92b82f541832286 := rup [pack f1,pack f3362,pack f3364,pack f3369,pack f1024,pack f790,pack f2357,pack f2997,pack f2226,pack f3426,pack f1027,pack f680,pack f519] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3473 : H a 0x458445648c484c8450468 := rup [pack f1,pack f161,pack f164] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3474 : H a 0x4c8648b01311458445381 := rup [pack f1,pack f3355,pack f1684,pack f1061,pack f1432,pack f3473] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3475 : H a 0x92b2d42c84c864882fb01311541 := rup [pack f1,pack f407,pack f617,pack f1274,pack f128,pack f790,pack f1024,pack f2221,pack f3474,pack f1019,pack f841,pack f2224,pack f3397,pack f3472,pack f2309] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3476 : H a 0x92b2d42c84c84d468864882f := rup [pack f1,pack f308,pack f3471,pack f783,pack f2219,pack f1025,pack f3475,pack f1023,pack f822,pack f1687,pack f3065,pack f2403,pack f3452] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3477 : H a 0x92b8ab2914c2 := rup [pack f1,pack f3355,pack f2222,pack f2183,pack f308,pack f298,pack f1689,pack f2219,pack f2181,pack f3065,pack f2403,pack f822,pack f3452] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3478 : H a 0x92b4c84d48ab4c1 := rup [pack f1,pack f3355,pack f3353,pack f3365,pack f3367,pack f3369,pack f3356,pack f3357,pack f3361,pack f308,pack f298,pack f2913,pack f1848,pack f784,pack f2220,pack f3464,pack f2180,pack f338,pack f663,pack f790,pack f821,pack f539,pack f887,pack f2178,pack f2537,pack f3263,pack f771] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3479 : H a 0x82983cc2c86c := rup [pack f1,pack f3355,pack f3353,pack f3466,pack f308,pack f2735,pack f1574,pack f1589,pack f2741,pack f1758,pack f1657,pack f3469,pack f3476,pack f328,pack f298,pack f1689,pack f3478,pack f2219,pack f3477,pack f2181,pack f2221,pack f820,pack f822,pack f2225,pack f2223,pack f2184,pack f3060,pack f2399,pack f3452] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3480 : H a 0x86b92b2984986184c2 := rup [pack f1,pack f3353,pack f3355,pack f289,pack f308,pack f1798,pack f2879,pack f617,pack f407,pack f563,pack f355,pack f783,pack f2219,pack f1274,pack f1232,pack f2110,pack f795,pack f842,pack f844,pack f884,pack f1351,pack f1296,pack f792,pack f2108,pack f788,pack f3437,pack f596,pack f643,pack f3157,pack f953,pack f918,pack f1190,pack f1157,pack f86,pack f58,pack f52,pack f75,pack f2116] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3481 : H a 35056433451 := rup [pack f1,pack f3353,pack f3355,pack f3352,pack f289,pack f308,pack f2863,pack f1780,pack f1299,pack f1309,pack f1367,pack f3480,pack f784,pack f2220,pack f2109,pack f796,pack f843,pack f883,pack f2215,pack f2107,pack f3435,pack f3143] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3482 : H a 0x83cc2c86b58868892c4c1498581 := rup [pack f1,pack f784,pack f796,pack f2110,pack f845,pack f843,pack f883,pack f744,pack f787,pack f791,pack f2107,pack f790,pack f2239,pack f2180,pack f324,pack f1026,pack f1017,pack f2112,pack f1478,pack f1090,pack f183,pack f177] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3483 : H a 0x86b3943884c1582682 := rup [pack f1,pack f3354,pack f3352,pack f2109,pack f795,pack f724,pack f720,pack f2506,pack f784,pack f563,pack f355,pack f733,pack f736,pack f791,pack f848,pack f2107,pack f2122,pack f2123,pack f834,pack f2153,pack f1482,pack f2622,pack f1095,pack f1996,pack f788,pack f2338,pack f2119,pack f2315,pack f2942,pack f2483,pack f3168,pack f2115,pack f2206,pack f2020,pack f1108,pack f797,pack f78,pack f85,pack f375,pack f579,pack f54,pack f57,pack f3443,pack f1213,pack f1241,pack f1286,pack f1361,pack f1381,pack f896,pack f964,pack f1256,pack f396,pack f87,pack f3415,pack f2501] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3484 : H a 0x588688498c884854904a8 := rup [pack f1,pack f183,pack f177] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3485 : H a 0x83cc2c86b92c6818ac312151 := rup [pack f1,pack f2108,pack f2121,pack f2120,pack f2246,pack f1018,pack f324] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3486 : H a 0xa413121524a7 := rup [pack f1,pack f1467,pack f1474] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3487 : H a 0x83cc2c86b58868892c498a41681c888ac485 := rup [pack f1,pack f2113,pack f3485,pack f3486,pack f3484,pack f1078,pack f1083] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3488 : H a 0x83cc2c86b58839438868892c4c1498 := rup [pack f1,pack f3353,pack f3355,pack f3354,pack f784,pack f289,pack f3482,pack f795,pack f2109,pack f3483,pack f792,pack f847,pack f2108,pack f869,pack f744,pack f794,pack f2178,pack f3487,pack f2112,pack f1026,pack f324,pack f314,pack f2234,pack f2850,pack f1745,pack f2442,pack f3441] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3489 : H a 35056432279 := rup [pack f1,pack f563,pack f355,pack f289,pack f1308,pack f1309,pack f1310,pack f1311] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3490 : H a 0x86b3946947143887086884c212a14a30a := rup [pack f1,pack f3359,pack f3370,pack f3356,pack f3364,pack f3352,pack f3357,pack f3360,pack f3367,pack f1374,pack f305,pack f563,pack f355,pack f395,pack f397,pack f1215,pack f1328,pack f1388,pack f716,pack f3443,pack f756,pack f797,pack f2111,pack f752,pack f1302,pack f1340,pack f785,pack f2105,pack f1290,pack f1501,pack f1373,pack f831,pack f2658,pack f1186,pack f943,pack f3219,pack f2117,pack f2968,pack f598,pack f70,pack f791,pack f61,pack f65,pack f1272,pack f966,pack f909,pack f1230,pack f87,pack f3415,pack f2453,pack f3125,pack f730] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3491 : H a 0x6946886816a4 := rup [pack f1,pack f3357,pack f3360,pack f3367,pack f734,pack f730] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3492 : H a 0xa18918815838858820898 := rup [pack f1,pack f94,pack f87] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3493 : H a 0x86ba189186a38158388ab056 := rup [pack f1,pack f355,pack f289,pack f51,pack f3116,pack f3135,pack f271,pack f3492,pack f2177,pack f1323] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3494 : H a 0xa189186a381586b8388ab := rup [pack f1,pack f3352,pack f3493,pack f3124] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3495 : H a 0x83cc2c86b69468892c4c2a1814a309681 := rup [pack f1,pack f3357,pack f3360,pack f3367,pack f289,pack f792,pack f2108,pack f1354,pack f2238,pack f3491,pack f737,pack f3118,pack f3139,pack f372,pack f415,pack f1018,pack f1220,pack f324,pack f3494] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3496 : H a 0x86b309115a64216609289 := rup [pack f1,pack f2952,pack f3052,pack f1441,pack f2582,pack f564,pack f3002,pack f3000,pack f3008] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3497 : H a 0xc2c86b394714388708309115342a64216d242c1ca4815289 := rup [pack f1,pack f3356,pack f3360,pack f3364,pack f3352,pack f3354,pack f3052,pack f3496,pack f416,pack f756,pack f752,pack f2105,pack f855,pack f3271,pack f3443,pack f1559,pack f2717,pack f2412,pack f2408,pack f638] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3498 : H a 83728286763287 := rup [pack f1,pack f791,pack f736,pack f783,pack f665,pack f205,pack f523,pack f1363,pack f2173,pack f2628,pack f1484,pack f587,pack f579] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3499 : H a 0x94194c948954 := rup [pack f1,pack f3368,pack f3363,pack f3362,pack f686,pack f693] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3500 : H a 0x86b39438894c68228a := rup [pack f1,pack f3359,pack f3360,pack f3370,pack f3352,pack f2107,pack f791,pack f736,pack f355,pack f369,pack f371,pack f716,pack f3443,pack f797,pack f2111,pack f2601,pack f1464,pack f3144,pack f2930,pack f577,pack f2802,pack f1649,pack f3499] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3501 : H a 0x83cc2c86b39469471438870868892c4c212a14a := rup [pack f1,pack f3356,pack f3360,pack f3364,pack f3352,pack f1374,pack f783,pack f665,pack f345,pack f3490,pack f3495,pack f791,pack f846,pack f842,pack f2107,pack f870,pack f874,pack f788,pack f3020,pack f2110,pack f2103,pack f769,pack f781,pack f3156,pack f3500,pack f3052,pack f3496,pack f3497,pack f416,pack f756,pack f752,pack f2105,pack f855,pack f3014,pack f3443,pack f2572,pack f1431,pack f560,pack f2409,pack f558] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3502 : H a 0xc2c86b7147084e4b01149682c81a64216198518289309 := rup [pack f1,pack f3356,pack f3360,pack f3364,pack f3352,pack f791,pack f1194,pack f2107,pack f3052,pack f874,pack f781,pack f769,pack f870,pack f2103,pack f1176,pack f289,pack f1333,pack f788,pack f736,pack f355,pack f1144,pack f3496,pack f414,pack f416,pack f756,pack f752,pack f785,pack f2105,pack f881,pack f855,pack f1227,pack f1530,pack f2694,pack f3271,pack f3014,pack f1151,pack f2572,pack f1431,pack f1559,pack f2717,pack f624,pack f644,pack f560,pack f42,pack f558,pack f638,pack f931,pack f1242,pack f1365,pack f60] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3503 : H a 0x39471438870834230a := rup [pack f1,pack f3356,pack f3360,pack f3364,pack f395,pack f397,pack f3443,pack f756,pack f855,pack f752] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3504 : H a 0x498518438618415c18458 := rup [pack f1,pack f75,pack f76] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3505 : H a 0x829c2c86b4c2149682 := rup [pack f1,pack f3353,pack f3355,pack f3352,pack f355,pack f289,pack f1368,pack f783,pack f665,pack f3489,pack f1823,pack f1698,pack f2891,pack f2829,pack f791,pack f846,pack f842,pack f870,pack f874,pack f788,pack f3020,pack f2110,pack f793,pack f781,pack f1295,pack f1347,pack f3503,pack f3502,pack f371,pack f3500,pack f3443,pack f408,pack f2111,pack f1204,pack f2367,pack f1394,pack f1268,pack f3504] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3506 : H a 0x83c829c2c12a := rup [pack f1,pack f3353,pack f3355,pack f3479,pack f289,pack f1716,pack f2829,pack f1698,pack f1757,pack f3481,pack f3489,pack f3488,pack f783,pack f1823,pack f2891,pack f2858,pack f355,pack f303,pack f3501,pack f3505,pack f2108,pack f3491,pack f3119,pack f3132,pack f3133,pack f7,pack f3113,pack f231,pack f3122,pack f2078,pack f2104,pack f290,pack f2089,pack f2090,pack f849] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3507 : H a 0x829c2c86b4c22d42c8654648298618149 := rup [pack f1,pack f3357,pack f3360,pack f3367,pack f3353,pack f3355,pack f3354,pack f289,pack f1757,pack f2858,pack f355,pack f3505,pack f2108,pack f3491,pack f63,pack f588,pack f737,pack f3119,pack f3132,pack f3133,pack f1375,pack f382,pack f2453,pack f10,pack f3113,pack f235,pack f3122,pack f3117,pack f2446,pack f1416,pack f2560,pack f1181,pack f941,pack f70,pack f66,pack f2109,pack f2114,pack f2118,pack f2808,pack f1664,pack f849,pack f2345,pack f486,pack f157,pack f787,pack f3413] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3508 : H a 0x83cc2c86b69468892c4c212914a681 := rup [pack f1,pack f3357,pack f3360,pack f3367,pack f289,pack f792,pack f2108,pack f1354,pack f3491,pack f2238,pack f737,pack f3118,pack f3137,pack f3139,pack f2451,pack f1018,pack f468,pack f324,pack f298,pack f3494,pack f1376] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3509 : H a 35374930988 := rup [pack f1,pack f3355,pack f3353,pack f3479,pack f289,pack f1716,pack f2829,pack f2858,pack f1698,pack f1757,pack f3481,pack f3489,pack f3488,pack f3506,pack f2735,pack f1574,pack f2807,pack f1657,pack f1299,pack f2879,pack f1798,pack f1367,pack f3507,pack f3508,pack f846,pack f842,pack f3437,pack f2110,pack f3156] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3510 : H a 0xc2b3943883543481d41c814a := rup [pack f1,pack f3368,pack f3369,pack f3363,pack f3364,pack f3370,pack f3352,pack f431,pack f341,pack f342,pack f343,pack f3403,pack f652,pack f3413,pack f677,pack f779,pack f1391,pack f1222,pack f1200,pack f2259,pack f787,pack f2255,pack f807,pack f890,pack f2557,pack f1409,pack f2991,pack f2273,pack f3006,pack f2270,pack f792,pack f797,pack f540,pack f64,pack f65,pack f50,pack f51,pack f3443,pack f959,pack f1371,pack f1329,pack f1378,pack f1317,pack f3504,pack f2413,pack f3492] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3511 : H a 0xc2b149c81215 := rup [pack f1,pack f3354,pack f788,pack f2255,pack f2338,pack f639,pack f2260,pack f2295,pack f2080,pack f2360,pack f2369,pack f779,pack f1957,pack f1042,pack f340] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3512 : H a 0x83c829682c81 := rup [pack f1,pack f3355,pack f3353,pack f791,pack f3509,pack f318,pack f2830,pack f1699,pack f2765,pack f1619,pack f2728,pack f1565,pack f3510,pack f788,pack f2255,pack f3511,pack f2259,pack f780,pack f810,pack f878,pack f881,pack f3411,pack f2180,pack f2218,pack f786,pack f2106,pack f2288,pack f1016,pack f2257,pack f804,pack f332,pack f2239] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3513 : H a 0x815c18838820898858918 := rup [pack f1,pack f87,pack f93] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3514 : H a 0xc2b394388438898a42215249838261420c18820498618115 := rup [pack f1,pack f2271,pack f2258,pack f50,pack f51,pack f2253,pack f816,pack f82,pack f3443,pack f1359,pack f3504,pack f2413,pack f3513] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3515 : H a 0xc2b394388542438096898a42215249309363838c18820498618 := rup [pack f1,pack f789,pack f546,pack f945,pack f600,pack f554,pack f3514,pack f64,pack f65,pack f2257,pack f79,pack f3504,pack f782,pack f2970,pack f866,pack f3513,pack f1289] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3516 : H a 35374929538 := rup [pack f1,pack f3355,pack f3353,pack f3363,pack f3364,pack f3370,pack f3509,pack f318,pack f2830,pack f1699,pack f2765,pack f1619,pack f2728,pack f1565,pack f3510,pack f791,pack f3512,pack f787,pack f848,pack f812,pack f808,pack f3413,pack f1201,pack f2256,pack f1326,pack f796,pack f2259,pack f351,pack f393,pack f673,pack f1209,pack f546,pack f554,pack f1390,pack f962,pack f1372,pack f1306,pack f3515] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3517 : H a 0xc2b149942ca4c8c498161c182584cc4e43184384204904b44a849c4580554ac215 := rup [pack f1,pack f3352,pack f3354,pack f639,pack f1298,pack f2260,pack f3089,pack f2426,pack f2271,pack f809,pack f589,pack f579,pack f383,pack f375,pack f64,pack f1379,pack f939,pack f1179,pack f84,pack f66] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3518 : H a 0x83c829341581 := rup [pack f1,pack f3352,pack f3354,pack f3370,pack f3364,pack f3363,pack f3355,pack f3353,pack f3509,pack f318,pack f2830,pack f1699,pack f2765,pack f1619,pack f2728,pack f1565,pack f3510,pack f3413,pack f673,pack f546,pack f1390,pack f600,pack f393,pack f2256,pack f1306,pack f2471,pack f3148,pack f788,pack f3516,pack f792,pack f639,pack f431,pack f796,pack f1247,pack f843,pack f833,pack f828,pack f662,pack f665,pack f783,pack f798,pack f1343,pack f786,pack f1197,pack f949,pack f1097,pack f2625,pack f1483,pack f1997,pack f1273,pack f2253,pack f2105,pack f2235,pack f2150,pack f2216,pack f3517,pack f74,pack f2259,pack f82,pack f3504,pack f780,pack f806,pack f2290,pack f2970,pack f3411,pack f2180,pack f2263,pack f2965,pack f332,pack f1031,pack f2983] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3519 : H a 0x83c829341216 := rup [pack f1,pack f3355,pack f3516,pack f3509,pack f3518,pack f795,pack f815,pack f2257,pack f2108,pack f788,pack f844,pack f2239,pack f2256,pack f819,pack f2217,pack f318,pack f1565,pack f2259,pack f780,pack f806,pack f879,pack f3411,pack f2180,pack f1016,pack f332] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3520 : H a 35374928705 := rup [pack f1,pack f3355,pack f3353,pack f3363,pack f3364,pack f3370,pack f3354,pack f3516,pack f792,pack f3509,pack f639,pack f318,pack f2830,pack f1699,pack f2765,pack f1619,pack f2728,pack f1565,pack f3510,pack f1298,pack f788,pack f2471,pack f1306,pack f3413,pack f351,pack f673,pack f546,pack f554,pack f1390,pack f3518,pack f720,pack f795,pack f844,pack f819,pack f815,pack f1203,pack f1995,pack f955,pack f1094,pack f1350,pack f1335,pack f793,pack f2257,pack f1245,pack f2152,pack f3519,pack f2260,pack f2271,pack f2315,pack f809,pack f50,pack f383,pack f375,pack f1379,pack f84,pack f1179,pack f67,pack f66] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3521 : H a 8636457 := rup [pack f1,pack f3355,pack f3370,pack f3369,pack f3368,pack f3353,pack f3509,pack f318,pack f431,pack f639,pack f2830,pack f1699,pack f2765,pack f1575,pack f1619,pack f2728,pack f1565,pack f3510,pack f3516,pack f792,pack f3520,pack f787,pack f811,pack f2255,pack f807,pack f1259,pack f847,pack f849,pack f790,pack f1776,pack f1540,pack f1380,pack f780,pack f1845,pack f3403,pack f660,pack f783,pack f718,pack f3411,pack f335,pack f362,pack f650,pack f2276,pack f2284,pack f2288,pack f2277,pack f1820,pack f1830,pack f537,pack f573,pack f2264,pack f2261,pack f781,pack f804,pack f841,pack f1117,pack f1510,pack f1132,pack f1349,pack f1843,pack f1266,pack f1061,pack f1432,pack f1422,pack f1055,pack f1684,pack f201,pack f216,pack f165,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3522 : H a 0x868838830c28a288258a8 := rup [pack f1,pack f127,pack f133] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3523 : H a 0x9481451581503481c8168 := rup [pack f1,pack f144,pack f151] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3524 : H a 0xb08b01b24b0c := rup [pack f1,pack f3363,pack f3359,pack f3356,pack f757,pack f762] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3525 : H a 0xa63b23b0b0d1486 := rup [pack f1,pack f3355,pack f631,pack f1113,pack f3207,pack f425,pack f1507,pack f704,pack f1353,pack f1703,pack f3215,pack f2509,pack f3036,pack f1841,pack f1825,pack f3428,pack f201] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3526 : H a 0x4c8a2ca8ca630a049ce0c942342b23b0b4580d1 := rup [pack f1,pack f3352,pack f3020,pack f2508,pack f3207,pack f120,pack f2001,pack f1982,pack f33,pack f3024,pack f3525,pack f3216,pack f3030,pack f2510,pack f232,pack f251,pack f1128,pack f240,pack f237,pack f3214,pack f3031,pack f2050,pack f2513,pack f426,pack f3026,pack f2380,pack f1661,pack f1695,pack f3473] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3527 : H a 0xb01a2ca8ca63b23b0b := rup [pack f1,pack f3355,pack f3353,pack f3352,pack f604,pack f784,pack f3020,pack f844,pack f788,pack f842,pack f792,pack f704,pack f886,pack f773,pack f2831,pack f631,pack f2000,pack f921,pack f1580,pack f398,pack f425,pack f1273,pack f1353,pack f3526,pack f3206,pack f3234,pack f2514,pack f2515,pack f3218,pack f2021,pack f2668,pack f2908,pack f2893,pack f3021,pack f520,pack f518] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3528 : H a 0xa63b23b0c0d2 := rup [pack f1,pack f3352,pack f704,pack f763,pack f884,pack f789,pack f739,pack f886,pack f779,pack f773,pack f3203,pack f477,pack f3206,pack f3234,pack f3233,pack f3411,pack f3404,pack f3033,pack f3218,pack f3217,pack f1189,pack f2693,pack f1909,pack f148,pack f2567,pack f3022,pack f3021,pack f3205,pack f2665,pack f2247,pack f2054,pack f465,pack f1130,pack f462,pack f423,pack f1561,pack f419] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3529 : H a 0xa63b230d1a090c5 := rup [pack f1,pack f763,pack f704,pack f1161,pack f1205,pack f3207,pack f886,pack f3213,pack f3231,pack f3227,pack f3228,pack f3043,pack f1163,pack f1141,pack f1184,pack f1221,pack f42] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3530 : H a 0xa63b23b0ca2ca09 := rup [pack f1,pack f3352,pack f3528,pack f704,pack f763,pack f884,pack f739,pack f886,pack f779,pack f773,pack f3529,pack f1877,pack f3212,pack f3028,pack f3222,pack f3223,pack f1850,pack f3215,pack f239,pack f3214,pack f3031,pack f1940,pack f2050,pack f1895,pack f228,pack f463,pack f1129,pack f423,pack f419] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3531 : H a 0xa63b230d1a0a0c6 := rup [pack f1,pack f3352,pack f3368,pack f3369,pack f3370,pack f763,pack f1010,pack f704,pack f886,pack f779,pack f884,pack f3203,pack f139,pack f3212,pack f3232,pack f3222,pack f3040,pack f1189,pack f1529,pack f1551,pack f3211,pack f1504,pack f1424,pack f2919,pack f123,pack f118,pack f2720,pack f3403,pack f650] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3532 : H a 0xa63b230d1a0a05a := rup [pack f1,pack f3352,pack f3020,pack f3203,pack f844,pack f788,pack f704,pack f763,pack f886,pack f884,pack f1173,pack f1149,pack f3207,pack f3531,pack f3213,pack f3228,pack f3227,pack f3043,pack f1184,pack f1152,pack f1221,pack f42,pack f1195,pack f842,pack f792,pack f1193,pack f3209,pack f1488,pack f1458,pack f3024,pack f1010,pack f1504,pack f1449,pack f3215,pack f3224,pack f3229,pack f3030,pack f1427,pack f1527,pack f1549,pack f984,pack f1396,pack f119,pack f101] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3533 : H a 0xa63b230d1a0a := rup [pack f1,pack f3352,pack f3207,pack f3024,pack f763,pack f1010,pack f704,pack f886,pack f779,pack f884,pack f3203,pack f3531,pack f1909,pack f2284,pack f2232,pack f3213,pack f3231,pack f3227,pack f3228,pack f334,pack f3210,pack f3209,pack f3025,pack f2126,pack f2209,pack f2102,pack f316,pack f3532,pack f3216,pack f3230,pack f3221,pack f3225,pack f3237,pack f3036,pack f3220,pack f992,pack f239,pack f7,pack f1030,pack f1004,pack f2147,pack f2187,pack f5,pack f292] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3534 : H a 44622297868 := rup [pack f1,pack f3352,pack f3203,pack f3020,pack f3528,pack f3207,pack f3024,pack f3533,pack f3530,pack f2252,pack f2245] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3535 : H a 10894115 := rup [pack f1,pack f3352,pack f3355,pack f704,pack f1703,pack f3020,pack f631,pack f568,pack f557,pack f604,pack f621,pack f763,pack f3203,pack f1316,pack f1086,pack f1580,pack f884,pack f739,pack f3534,pack f425,pack f3527,pack f1485,pack f314,pack f329,pack f2251,pack f1812,pack f1771,pack f177] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3536 : H a 0xa21b0be02a2b := rup [pack f1,pack f3353,pack f3355,pack f3354,pack f779,pack f314,pack f329,pack f2727,pack f3521,pack f1564,pack f469,pack f3411,pack f3403,pack f2508,pack f2302,pack f2296,pack f2298,pack f2304] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3537 : H a 44622199347 := rup [pack f1,pack f3354,pack f3352,pack f760,pack f2935,pack f704,pack f425,pack f2630,pack f1485,pack f2506,pack f3078,pack f3020,pack f528,pack f2696,pack f2697,pack f2176,pack f3164,pack f3023,pack f3123,pack f579,pack f2518] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3538 : H a 10894091 := rup [pack f1,pack f3354,pack f3352,pack f3535,pack f704,pack f3078,pack f3020,pack f631,pack f425,pack f760,pack f2506,pack f1485,pack f2630,pack f2935,pack f886,pack f884,pack f777,pack f742,pack f3536,pack f3537,pack f3414,pack f214,pack f1531,pack f1534,pack f2175,pack f3174,pack f3030,pack f3128,pack f579,pack f2517] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3539 : H a 44622158375 := rup [pack f1,pack f3352,pack f3363,pack f3359,pack f3356,pack f3535,pack f3538,pack f3524,pack f759,pack f784,pack f3020,pack f1531,pack f1534,pack f1829,pack f3030,pack f2898] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3540 : H a 44622158387 := rup [pack f1,pack f3352,pack f3363,pack f3359,pack f3356,pack f3535,pack f3538,pack f3524,pack f759,pack f784,pack f3020,pack f2696,pack f2697,pack f2895,pack f3023,pack f1833] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3541 : H a 10894081 := rup [pack f1,pack f3356,pack f3359,pack f3363,pack f3355,pack f3538,pack f3535,pack f704,pack f631,pack f886,pack f884,pack f3524,pack f777,pack f742,pack f789,pack f218,pack f759,pack f530,pack f2366,pack f3539,pack f3540,pack f3414,pack f314,pack f329,pack f421,pack f1637,pack f2998,pack f3426] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3542 : H a 10893867 := rup [pack f1,pack f3353,pack f3355,pack f3365,pack f3367,pack f3369,pack f3352,pack f3541,pack f783,pack f704,pack f1703,pack f631,pack f568,pack f557,pack f314,pack f329,pack f2742,pack f1590,pack f1315,pack f3521,pack f3464,pack f273,pack f469,pack f1933,pack f663,pack f2329,pack f2944,pack f1087,pack f1770,pack f1812,pack f3029,pack f181,pack f177] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3543 : H a 0xa63a2883b485 := rup [pack f1,pack f3352,pack f3357,pack f3358,pack f3365,pack f3020,pack f1927,pack f3542,pack f3541,pack f783,pack f3535,pack f3030,pack f1949,pack f1925,pack f848,pack f1938,pack f1937,pack f3142,pack f3396,pack f632,pack f461,pack f2696,pack f2478,pack f2877,pack f3170,pack f3437,pack f745] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3544 : H a 44621269051 := rup [pack f1,pack f3352,pack f3541,pack f783,pack f704,pack f3078,pack f3020,pack f273,pack f1927,pack f1933,pack f197,pack f3543,pack f180,pack f1930,pack f3029,pack f788,pack f3148,pack f2620,pack f2168,pack f2944,pack f3130,pack f579,pack f2778,pack f2354,pack f3413] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3545 : H a 0xa6382a486c82 := rup [pack f1,pack f3352,pack f3361,pack f3363,pack f3366,pack f3354,pack f3356,pack f3358,pack f3362,pack f3020,pack f3046,pack f3023,pack f25,pack f3029,pack f3039,pack f239,pack f3040,pack f268,pack f267,pack f3045,pack f3025,pack f3035,pack f3034,pack f557,pack f1357,pack f2757,pack f3541,pack f1852,pack f1246,pack f322,pack f783,pack f704,pack f2418,pack f3078,pack f787,pack f848,pack f1960,pack f2563,pack f1902,pack f819,pack f815,pack f1214,pack f228,pack f695,pack f656,pack f781,pack f302,pack f451,pack f1886,pack f1881,pack f1879,pack f488,pack f1277,pack f1668,pack f2989,pack f3189,pack f705,pack f352,pack f2388,pack f2389,pack f2395,pack f2678,pack f1331,pack f1393,pack f2909,pack f107,pack f2359,pack f2500,pack f975,pack f3513,pack f2210,pack f614,pack f404,pack f3412,pack f765] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3546 : H a 0xa6382a486ca4 := rup [pack f1,pack f3352,pack f3357,pack f3358,pack f3365,pack f3020,pack f3045,pack f3025,pack f3541,pack f3545,pack f788,pack f859,pack f786,pack f2229,pack f857,pack f798,pack f2139,pack f2951,pack f3047,pack f783,pack f847,pack f2583,pack f3046,pack f1407,pack f2207,pack f1008,pack f3029,pack f1413,pack f2961,pack f3039,pack f1423,pack f239,pack f3040,pack f1398,pack f267,pack f3023,pack f3035,pack f1852,pack f187,pack f323,pack f322,pack f3542,pack f3437,pack f513,pack f533,pack f749,pack f978,pack f2092,pack f392,pack f434,pack f312,pack f1143,pack f228,pack f99,pack f1886,pack f1882,pack f569,pack f2989,pack f2921,pack f2551,pack f2082,pack f550] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3547 : H a 44619179142 := rup [pack f1,pack f3352,pack f323,pack f3541,pack f783,pack f3020,pack f3029,pack f3545,pack f788,pack f847,pack f857,pack f859,pack f2583,pack f3047,pack f2951,pack f3546,pack f3176,pack f1437,pack f3003,pack f569] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3548 : H a 0xb0282a3224e4306 := rup [pack f1,pack f3365,pack f3367,pack f3369,pack f783,pack f2737,pack f2329,pack f661,pack f3464] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3549 : H a 0xa6382ac81ca3 := rup [pack f1,pack f3352,pack f568,pack f3541,pack f788,pack f859,pack f913,pack f2951,pack f857,pack f947,pack f3047,pack f3547,pack f3030,pack f783,pack f847,pack f1436,pack f791,pack f323,pack f631,pack f927,pack f590,pack f596,pack f940,pack f898,pack f3,pack f958,pack f977,pack f539,pack f3548,pack f2586,pack f3163,pack f569,pack f3177,pack f3004] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3550 : H a 0xa6348549868849032205a := rup [pack f1,pack f3355,pack f3541,pack f704,pack f1703,pack f1465,pack f1782,pack f3484] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3551 : H a 0xa6382ac8181f := rup [pack f1,pack f3352,pack f3355,pack f704,pack f568,pack f3541,pack f783,pack f847,pack f791,pack f1095,pack f731,pack f788,pack f1305,pack f859,pack f857,pack f1605,pack f3547,pack f758,pack f3020,pack f271,pack f958,pack f977,pack f976,pack f1496,pack f539,pack f1341,pack f1110,pack f3548,pack f3550,pack f1697,pack f1821,pack f193] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3552 : H a 0x4200a0820120220060 := rup [pack f1,pack f3] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3553 : H a 0x1302308300704300b0 := rup [pack f1,pack f5] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3554 : H a 0x1382388380780b8438 := rup [pack f1,pack f42] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3555 : H a 0x7c23c13c83c43c0bc := rup [pack f1,pack f228] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3556 : H a 31344203481547 := rup [pack f1,pack f3370,pack f3369,pack f3368,pack f650] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3557 : H a 31619081339347 := rup [pack f1,pack f3370,pack f3369,pack f3368,pack f651] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3558 : H a 86057325216979 := rup [pack f1,pack f3369,pack f3367,pack f3365,pack f664] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3559 : H a 58013536109383 := rup [pack f1,pack f3370,pack f3364,pack f3363,pack f671] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3560 : H a 57738658202443 := rup [pack f1,pack f3370,pack f3364,pack f3363,pack f673] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3561 : H a 59662602126163 := rup [pack f1,pack f3370,pack f3364,pack f3363,pack f675] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3562 : H a 58563090498403 := rup [pack f1,pack f3370,pack f3364,pack f3363,pack f677] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3563 : H a 94855767557451 := rup [pack f1,pack f3369,pack f3364,pack f3362,pack f682] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3564 : H a 0x96494c954947 := rup [pack f1,pack f3368,pack f3363,pack f3362,pack f688] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3565 : H a 0x94895494b964 := rup [pack f1,pack f3368,pack f3363,pack f3362,pack f689] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3566 : H a 0x94896494c953 := rup [pack f1,pack f3368,pack f3363,pack f3362,pack f691] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3567 : H a 0xa54a64a41a48a4c := rup [pack f1,pack f3366,pack f3363,pack f3361,pack f697] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3568 : H a 0xa64a4ca54a47 := rup [pack f1,pack f3366,pack f3363,pack f3361,pack f699] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3569 : H a 0xa64a48a54a4b := rup [pack f1,pack f3366,pack f3363,pack f3361,pack f701] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3570 : H a 0xa48a63a54a4c := rup [pack f1,pack f3366,pack f3363,pack f3361,pack f705] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3571 : H a 0x5815a458c594588 := rup [pack f1,pack f3369,pack f3360,pack f3358,pack f717] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3572 : H a 99254753904007 := rup [pack f1,pack f3369,pack f3360,pack f3358,pack f719] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3573 : H a 98155175232907 := rup [pack f1,pack f3369,pack f3360,pack f3358,pack f721] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3574 : H a 99254753854867 := rup [pack f1,pack f3369,pack f3360,pack f3358,pack f723] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3575 : H a 98155175134627 := rup [pack f1,pack f3369,pack f3360,pack f3358,pack f725] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3576 : H a 0x99498898c9a3 := rup [pack f1,pack f3368,pack f3359,pack f3358,pack f729] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3577 : H a 0x6816886a469468c := rup [pack f1,pack f3367,pack f3360,pack f3357,pack f730] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3578 : H a 0x6a468c694687 := rup [pack f1,pack f3367,pack f3360,pack f3357,pack f732] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3579 : H a 0x6886946a468b := rup [pack f1,pack f3367,pack f3360,pack f3357,pack f734] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3580 : H a 0x6a468868c693 := rup [pack f1,pack f3367,pack f3360,pack f3357,pack f735] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3581 : H a 0x68869468c6a3 := rup [pack f1,pack f3367,pack f3360,pack f3357,pack f737] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3582 : H a 0xa88a94aa4a8b := rup [pack f1,pack f3366,pack f3359,pack f3357,pack f740] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3583 : H a 0xca4c8cc94c87 := rup [pack f1,pack f3365,pack f3358,pack f3357,pack f745] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3584 : H a 0xca4c88c8cc93 := rup [pack f1,pack f3365,pack f3358,pack f3357,pack f749] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3585 : H a 0xca3c8cc88c94 := rup [pack f1,pack f3365,pack f3358,pack f3357,pack f751] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3586 : H a 0xb0bb24b08b14 := rup [pack f1,pack f3363,pack f3359,pack f3356,pack f761] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3587 : H a 0xd14d08d0cd23 := rup [pack f1,pack f3362,pack f3358,pack f3356,pack f770] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3588 : H a 0xe14e24e08e01e0c := rup [pack f1,pack f3361,pack f3357,pack f3356,pack f771] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3589 : H a 0xe24e08e14e0b := rup [pack f1,pack f3361,pack f3357,pack f3356,pack f774] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3590 : H a 0xe0ce08e24e13 := rup [pack f1,pack f3361,pack f3357,pack f3356,pack f776] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3591 : H a 14688706 := rup [pack f1,pack f779] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3592 : H a 14684609 := rup [pack f1,pack f780] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3593 : H a 13640386 := rup [pack f1,pack f781] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3594 : H a 13636289 := rup [pack f1,pack f782] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3595 : H a 11543746 := rup [pack f1,pack f783] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3596 : H a 11539649 := rup [pack f1,pack f784] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3597 : H a 7350466 := rup [pack f1,pack f785] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3598 : H a 7346369 := rup [pack f1,pack f786] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3599 : H a 13116226 := rup [pack f1,pack f787] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3600 : H a 13112129 := rup [pack f1,pack f788] (by dsimp only [pack,List.map]; decide +kernel)
end BorsukCert

namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3601 : H a 11019586 := rup [pack f1,pack f789] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3602 : H a 6826306 := rup [pack f1,pack f791] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3603 : H a 6822209 := rup [pack f1,pack f792] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3604 : H a 9971266 := rup [pack f1,pack f793] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3605 : H a 9967169 := rup [pack f1,pack f794] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3606 : H a 5777986 := rup [pack f1,pack f795] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3607 : H a 5773889 := rup [pack f1,pack f796] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3608 : H a 3681346 := rup [pack f1,pack f797] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3609 : H a 3677249 := rup [pack f1,pack f798] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3610 : H a 20436492994 := rup [pack f1,pack f799] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3611 : H a 37617410498 := rup [pack f1,pack f801] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3612 : H a 20436494530 := rup [pack f1,pack f803] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3613 : H a 20443833026 := rup [pack f1,pack f804] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3614 : H a 13997711810 := rup [pack f1,pack f805] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3615 : H a 14001906114 := rup [pack f1,pack f807] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3616 : H a 13985124801 := rup [pack f1,pack f808] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3617 : H a 39763846466 := rup [pack f1,pack f809] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3618 : H a 39750734273 := rup [pack f1,pack f810] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3619 : H a 13980932417 := rup [pack f1,pack f812] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3620 : H a 13998760642 := rup [pack f1,pack f813] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3621 : H a 14002954946 := rup [pack f1,pack f814] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3622 : H a 44043604673 := rup [pack f1,pack f815] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3623 : H a 44063531714 := rup [pack f1,pack f816] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3624 : H a 44046750401 := rup [pack f1,pack f817] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3625 : H a 14002955842 := rup [pack f1,pack f818] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3626 : H a 44043605569 := rup [pack f1,pack f819] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3627 : H a 20441212226 := rup [pack f1,pack f820] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3628 : H a 20423382593 := rup [pack f1,pack f821] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3629 : H a 20440165442 := rup [pack f1,pack f822] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3630 : H a 20447503938 := rup [pack f1,pack f824] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3631 : H a 52653466946 := rup [pack f1,pack f826] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3632 : H a 22578206273 := rup [pack f1,pack f827] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3633 : H a 44049897665 := rup [pack f1,pack f829] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3634 : H a 39774857410 := rup [pack f1,pack f830] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3635 : H a 44066155586 := rup [pack f1,pack f832] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3636 : H a 39772761154 := rup [pack f1,pack f833] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3637 : H a 15059128769 := rup [pack f1,pack f835] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3638 : H a 23657720194 := rup [pack f1,pack f836] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3639 : H a 7538743681 := rup [pack f1,pack f837] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3640 : H a 23665845122 := rup [pack f1,pack f838] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3641 : H a 23660865154 := rup [pack f1,pack f842] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3642 : H a 27939050881 := rup [pack f1,pack f843] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3643 : H a 23660866690 := rup [pack f1,pack f844] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3644 : H a 53708854657 := rup [pack f1,pack f845] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3645 : H a 20441476226 := rup [pack f1,pack f846] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3646 : H a 20430984833 := rup [pack f1,pack f847] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3647 : H a 23662701698 := rup [pack f1,pack f848] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3648 : H a 53710689665 := rup [pack f1,pack f849] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3649 : H a 37625538946 := rup [pack f1,pack f850] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3650 : H a 40828148353 := rup [pack f1,pack f851] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3651 : H a 53713049985 := rup [pack f1,pack f852] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3652 : H a 53731666114 := rup [pack f1,pack f853] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3653 : H a 53714884993 := rup [pack f1,pack f854] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3654 : H a 13979096833 := rup [pack f1,pack f856] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3655 : H a 47281611650 := rup [pack f1,pack f857] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3656 : H a 47264830337 := rup [pack f1,pack f858] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3657 : H a 47281612546 := rup [pack f1,pack f859] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3658 : H a 47264831233 := rup [pack f1,pack f860] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3659 : H a 47281874690 := rup [pack f1,pack f861] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3660 : H a 47268762497 := rup [pack f1,pack f862] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3661 : H a 23663224130 := rup [pack f1,pack f863] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3662 : H a 30103842050 := rup [pack f1,pack f866] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3663 : H a 30095185217 := rup [pack f1,pack f867] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3664 : H a 23669516034 := rup [pack f1,pack f868] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3665 : H a 47287904642 := rup [pack f1,pack f869] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3666 : H a 39771974914 := rup [pack f1,pack f871] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3667 : H a 39755193601 := rup [pack f1,pack f872] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3668 : H a 47287905538 := rup [pack f1,pack f873] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3669 : H a 47288167682 := rup [pack f1,pack f875] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3670 : H a 47271386369 := rup [pack f1,pack f876] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3671 : H a 27940624129 := rup [pack f1,pack f877] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3672 : H a 27965531714 := rup [pack f1,pack f878] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3673 : H a 26891790082 := rup [pack f1,pack f879] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3674 : H a 30096234049 := rup [pack f1,pack f880] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3675 : H a 27948750593 := rup [pack f1,pack f882] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3676 : H a 44067990274 := rup [pack f1,pack f883] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3677 : H a 44051733121 := rup [pack f1,pack f884] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3678 : H a 60173855490 := rup [pack f1,pack f885] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3679 : H a 44051734017 := rup [pack f1,pack f886] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3680 : H a 47292885634 := rup [pack f1,pack f887] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3681 : H a 55864204801 := rup [pack f1,pack f892] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3682 : H a 53735337218 := rup [pack f1,pack f893] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3683 : H a 14684615 := rup [pack f1,pack f3355,pack f1560] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3684 : H a 34781032985 := rup [pack f1,pack f3355,pack f1563] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3685 : H a 13636295 := rup [pack f1,pack f3355,pack f1572] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3686 : H a 4722889415 := rup [pack f1,pack f3355,pack f1573] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3687 : H a 35183071943 := rup [pack f1,pack f3355,pack f1576] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3688 : H a 11539655 := rup [pack f1,pack f3355,pack f1580] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3689 : H a 34780320967 := rup [pack f1,pack f3355,pack f1586] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3690 : H a 34781369543 := rup [pack f1,pack f3355,pack f1587] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3691 : H a 7346375 := rup [pack f1,pack f3355,pack f1602] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3692 : H a 13112135 := rup [pack f1,pack f3355,pack f1605] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3693 : H a 34779796295 := rup [pack f1,pack f3355,pack f1616] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3694 : H a 34783466311 := rup [pack f1,pack f3355,pack f1617] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3695 : H a 35182547783 := rup [pack f1,pack f3355,pack f1623] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3696 : H a 35186217799 := rup [pack f1,pack f3355,pack f1624] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3697 : H a 11015495 := rup [pack f1,pack f3355,pack f1630] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3698 : H a 34784702617 := rup [pack f1,pack f3355,pack f1634] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3699 : H a 34784703001 := rup [pack f1,pack f3355,pack f1635] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3700 : H a 9967175 := rup [pack f1,pack f3355,pack f1651] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3701 : H a 4722890311 := rup [pack f1,pack f3355,pack f1655] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3702 : H a 35183072839 := rup [pack f1,pack f3355,pack f1658] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3703 : H a 5773895 := rup [pack f1,pack f3355,pack f1664] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3704 : H a 4725174425 := rup [pack f1,pack f3355,pack f1672] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3705 : H a 4983528007 := rup [pack f1,pack f3355,pack f1673] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3706 : H a 4987198023 := rup [pack f1,pack f3355,pack f1674] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3707 : H a 3677255 := rup [pack f1,pack f3355,pack f1684] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3708 : H a 34779534215 := rup [pack f1,pack f3355,pack f1697] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3709 : H a 10753415 := rup [pack f1,pack f3355,pack f1703] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3710 : H a 23748252185 := rup [pack f1,pack f3355,pack f1713] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3711 : H a 23742025833 := rup [pack f1,pack f3355,pack f1715] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3712 : H a 9417814129 := rup [pack f1,pack f3355,pack f1723] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3713 : H a 23748350065 := rup [pack f1,pack f3355,pack f1724] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3714 : H a 23748350513 := rup [pack f1,pack f3355,pack f1725] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3715 : H a 6560135 := rup [pack f1,pack f3355,pack f1742] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3716 : H a 9705095 := rup [pack f1,pack f3355,pack f1749] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3717 : H a 34779534983 := rup [pack f1,pack f3355,pack f1755] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3718 : H a 34780321415 := rup [pack f1,pack f3355,pack f1756] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3719 : H a 35182286471 := rup [pack f1,pack f3355,pack f1763] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3720 : H a 35183072903 := rup [pack f1,pack f3355,pack f1764] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3721 : H a 3415175 := rup [pack f1,pack f3355,pack f1781] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3722 : H a 1494326407 := rup [pack f1,pack f3355,pack f1794] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3723 : H a 1495374983 := rup [pack f1,pack f3355,pack f1795] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3724 : H a 9010519175 := rup [pack f1,pack f3355,pack f1796] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3725 : H a 9279020167 := rup [pack f1,pack f3355,pack f1799] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3726 : H a 9413270663 := rup [pack f1,pack f3355,pack f1804] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3727 : H a 34779535111 := rup [pack f1,pack f3355,pack f1821] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3728 : H a 34779797255 := rup [pack f1,pack f3355,pack f1822] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3729 : H a 2891015 := rup [pack f1,pack f3355,pack f1834] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3730 : H a 1842695 := rup [pack f1,pack f3355,pack f1845] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3731 : H a 14684619 := rup [pack f1,pack f3354,pack f2293] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3732 : H a 35186217419 := rup [pack f1,pack f3354,pack f2302] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3733 : H a 20594184741 := rup [pack f1,pack f3354,pack f2317] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3734 : H a 14143869989 := rup [pack f1,pack f3354,pack f2346] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3735 : H a 35185275057 := rup [pack f1,pack f3354,pack f2347] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3736 : H a 35185275953 := rup [pack f1,pack f3354,pack f2348] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3737 : H a 35182548299 := rup [pack f1,pack f3354,pack f2363] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3738 : H a 39915246629 := rup [pack f1,pack f3354,pack f2370] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3739 : H a 5773899 := rup [pack f1,pack f3354,pack f2375] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3740 : H a 44212310181 := rup [pack f1,pack f3354,pack f2387] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3741 : H a 35182286219 := rup [pack f1,pack f3354,pack f2427] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3742 : H a 9420608907 := rup [pack f1,pack f3354,pack f2428] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3743 : H a 6560139 := rup [pack f1,pack f3354,pack f2439] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3744 : H a 4922585189 := rup [pack f1,pack f3354,pack f2454] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3745 : H a 3415179 := rup [pack f1,pack f3354,pack f2471] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3746 : H a 53872840805 := rup [pack f1,pack f3354,pack f2484] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3747 : H a 53872841253 := rup [pack f1,pack f3354,pack f2485] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3748 : H a 53873938737 := rup [pack f1,pack f3354,pack f2489] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3749 : H a 4987659 := rup [pack f1,pack f3354,pack f2506] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3750 : H a 2891019 := rup [pack f1,pack f3354,pack f2519] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3751 : H a 1426677003 := rup [pack f1,pack f3354,pack f2526] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3752 : H a 1842699 := rup [pack f1,pack f3354,pack f2536] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3753 : H a 5131776177 := rup [pack f1,pack f3354,pack f2540] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3754 : H a 14684627 := rup [pack f1,pack f3353,pack f2719] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3755 : H a 35051966931 := rup [pack f1,pack f3353,pack f2728] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3756 : H a 34981696211 := rup [pack f1,pack f3353,pack f2733] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3757 : H a 34981696723 := rup [pack f1,pack f3353,pack f2738] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3758 : H a 34982745299 := rup [pack f1,pack f3353,pack f2739] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3759 : H a 7346387 := rup [pack f1,pack f3353,pack f2743] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3760 : H a 13112147 := rup [pack f1,pack f3353,pack f2747] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3761 : H a 34578420563 := rup [pack f1,pack f3353,pack f2758] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3762 : H a 34582090579 := rup [pack f1,pack f3353,pack f2759] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3763 : H a 2772587347 := rup [pack f1,pack f3353,pack f2760] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3764 : H a 34981172051 := rup [pack f1,pack f3353,pack f2761] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3765 : H a 34984842067 := rup [pack f1,pack f3353,pack f2762] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3766 : H a 35051090089 := rup [pack f1,pack f3353,pack f2764] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3767 : H a 35051967315 := rup [pack f1,pack f3353,pack f2765] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3768 : H a 35048297811 := rup [pack f1,pack f3353,pack f2787] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3769 : H a 6822227 := rup [pack f1,pack f3353,pack f2793] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3770 : H a 2369837395 := rup [pack f1,pack f3353,pack f2797] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3771 : H a 17868429651 := rup [pack f1,pack f3353,pack f2799] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3772 : H a 34981697107 := rup [pack f1,pack f3353,pack f2804] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3773 : H a 5773907 := rup [pack f1,pack f3353,pack f2808] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3774 : H a 4523896973 := rup [pack f1,pack f3353,pack f2814] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3775 : H a 4523897869 := rup [pack f1,pack f3353,pack f2815] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3776 : H a 17801304659 := rup [pack f1,pack f3353,pack f2816] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3777 : H a 12850067 := rup [pack f1,pack f3353,pack f2827] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3778 : H a 10753427 := rup [pack f1,pack f3353,pack f2831] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3779 : H a 34980910483 := rup [pack f1,pack f3353,pack f2837] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3780 : H a 34982745491 := rup [pack f1,pack f3353,pack f2838] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3781 : H a 6560147 := rup [pack f1,pack f3353,pack f2846] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3782 : H a 28237254757 := rup [pack f1,pack f3353,pack f2855] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3783 : H a 28244594981 := rup [pack f1,pack f3353,pack f2856] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3784 : H a 3415187 := rup [pack f1,pack f3353,pack f2866] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3785 : H a 54007058981 := rup [pack f1,pack f3353,pack f2876] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3786 : H a 54006288681 := rup [pack f1,pack f3353,pack f2879] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3787 : H a 54008123689 := rup [pack f1,pack f3353,pack f2880] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3788 : H a 4987667 := rup [pack f1,pack f3353,pack f2894] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3789 : H a 2891027 := rup [pack f1,pack f3353,pack f2899] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3790 : H a 14684643 := rup [pack f1,pack f3352,pack f2916] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3791 : H a 17601278489 := rup [pack f1,pack f3352,pack f2924] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3792 : H a 34781147673 := rup [pack f1,pack f3352,pack f2925] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3793 : H a 34713195235 := rup [pack f1,pack f3352,pack f2931] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3794 : H a 4722889443 := rup [pack f1,pack f3352,pack f2934] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3795 : H a 11539683 := rup [pack f1,pack f3352,pack f2935] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3796 : H a 4722889955 := rup [pack f1,pack f3352,pack f2944] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3797 : H a 34784293401 := rup [pack f1,pack f3352,pack f2945] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3798 : H a 7346403 := rup [pack f1,pack f3352,pack f2951] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3799 : H a 4515223779 := rup [pack f1,pack f3352,pack f2954] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3800 : H a 17600452835 := rup [pack f1,pack f3352,pack f2958] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3801 : H a 17601501411 := rup [pack f1,pack f3352,pack f2959] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3802 : H a 13112163 := rup [pack f1,pack f3352,pack f2961] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3803 : H a 14546457621 := rup [pack f1,pack f3352,pack f2968] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3804 : H a 2508280675 := rup [pack f1,pack f3352,pack f2969] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3805 : H a 34782720153 := rup [pack f1,pack f3352,pack f2976] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3806 : H a 34782721049 := rup [pack f1,pack f3352,pack f2977] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3807 : H a 9009993059 := rup [pack f1,pack f3352,pack f2992] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3808 : H a 34779796835 := rup [pack f1,pack f3352,pack f2993] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3809 : H a 34781369699 := rup [pack f1,pack f3352,pack f2994] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3810 : H a 6822243 := rup [pack f1,pack f3352,pack f2999] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3811 : H a 40319946905 := rup [pack f1,pack f3352,pack f3009] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3812 : H a 34713196131 := rup [pack f1,pack f3352,pack f3015] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3813 : H a 4722890339 := rup [pack f1,pack f3352,pack f3018] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3814 : H a 5773923 := rup [pack f1,pack f3352,pack f3020] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3815 : H a 3677283 := rup [pack f1,pack f3352,pack f3047] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3816 : H a 4515224675 := rup [pack f1,pack f3352,pack f3057] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3817 : H a 4727386265 := rup [pack f1,pack f3352,pack f3061] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3818 : H a 12850083 := rup [pack f1,pack f3352,pack f3069] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3819 : H a 34779534243 := rup [pack f1,pack f3352,pack f3075] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3820 : H a 10753443 := rup [pack f1,pack f3352,pack f3078] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3821 : H a 34578159011 := rup [pack f1,pack f3352,pack f3088] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3822 : H a 1434539427 := rup [pack f1,pack f3352,pack f3090] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3823 : H a 8950732195 := rup [pack f1,pack f3352,pack f3091] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3824 : H a 34779534755 := rup [pack f1,pack f3352,pack f3094] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3825 : H a 9017857443 := rup [pack f1,pack f3352,pack f3095] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3826 : H a 6560163 := rup [pack f1,pack f3352,pack f3107] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3827 : H a 17601501603 := rup [pack f1,pack f3352,pack f3109] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3828 : H a 9705123 := rup [pack f1,pack f3352,pack f3112] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3829 : H a 34779535011 := rup [pack f1,pack f3352,pack f3129] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3830 : H a 4722890403 := rup [pack f1,pack f3352,pack f3130] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3831 : H a 5511843 := rup [pack f1,pack f3352,pack f3140] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3832 : H a 4718697123 := rup [pack f1,pack f3352,pack f3145] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3833 : H a 3415203 := rup [pack f1,pack f3352,pack f3148] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3834 : H a 54275395661 := rup [pack f1,pack f3352,pack f3164] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3835 : H a 54275428437 := rup [pack f1,pack f3352,pack f3167] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3836 : H a 54275428885 := rup [pack f1,pack f3352,pack f3168] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3837 : H a 4714765475 := rup [pack f1,pack f3352,pack f3174] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3838 : H a 54274658841 := rup [pack f1,pack f3352,pack f3175] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3839 : H a 4727648793 := rup [pack f1,pack f3352,pack f3176] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3840 : H a 9180963 := rup [pack f1,pack f3352,pack f3185] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3841 : H a 1493800739 := rup [pack f1,pack f3352,pack f3192] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3842 : H a 34779535139 := rup [pack f1,pack f3352,pack f3193] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3843 : H a 34779797283 := rup [pack f1,pack f3352,pack f3194] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3844 : H a 4987683 := rup [pack f1,pack f3352,pack f3203] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3845 : H a 47836139673 := rup [pack f1,pack f3352,pack f3223] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3846 : H a 2891043 := rup [pack f1,pack f3352,pack f3238] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3847 : H a 1293999395 := rup [pack f1,pack f3352,pack f3247] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3848 : H a 1428249891 := rup [pack f1,pack f3352,pack f3248] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3849 : H a 2569116963 := rup [pack f1,pack f3352,pack f3250] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3850 : H a 1842723 := rup [pack f1,pack f3352,pack f3255] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3851 : H a 4729221273 := rup [pack f1,pack f3352,pack f3277] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3852 : H a 0xb08348328059305318310819 := rup [pack f1,pack f3708,pack f3727,pack f193] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3853 : H a 0x58848534249868849032281a := rup [pack f1,pack f1470,pack f1581,pack f3484,pack f188] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3854 : H a 0xa6382ac81322305 := rup [pack f1,pack f704,pack f3709,pack f3547,pack f3600,pack f1305,pack f3541,pack f3595,pack f3646,pack f731,pack f568,pack f3602,pack f1095,pack f3853,pack f3550,pack f599,pack f3551,pack f3657,pack f913,pack f3798,pack f3655,pack f947,pack f3815,pack f3030,pack f1436,pack f3692,pack f323,pack f631,pack f927,pack f758,pack f2586,pack f569,pack f549,pack f618,pack f934,pack f3552,pack f906,pack f898,pack f896,pack f1339,pack f1110,pack f3852] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3855 : H a 0xa6382ac81322 := rup [pack f1,pack f3549,pack f3600,pack f3854,pack f2888,pack f2496,pack f3437,pack f3583] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3856 : H a 44619181185 := rup [pack f1,pack f3547,pack f3030,pack f3814,pack f1246,pack f323,pack f631,pack f3541,pack f3595,pack f927,pack f704,pack f3709,pack f568,pack f557,pack f3600,pack f3646,pack f3655,pack f3657,pack f1305,pack f731,pack f3602,pack f1436,pack f3815,pack f947,pack f3798,pack f913,pack f1095,pack f3551,pack f3855,pack f900,pack f3552,pack f258,pack f934,pack f1469,pack f3004,pack f3484,pack f569,pack f188,pack f1812,pack f1813,pack f1814,pack f470,pack f2585,pack f1582,pack f1584,pack f1596,pack f1591,pack f457,pack f1336,pack f1369,pack f1300,pack f527,pack f67] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3857 : H a 0xa41485c886814904988a8c410e8873 := rup [pack f1,pack f3709,pack f443,pack f470,pack f493,pack f2575,pack f2577,pack f2581,pack f3719,pack f987,pack f1456,pack f1460,pack f1154,pack f3484,pack f101] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3858 : H a 0xa6382a321701868 := rup [pack f1,pack f704,pack f3547,pack f3856,pack f744,pack f3814,pack f3647,pack f557,pack f3599,pack f1094,pack f1322,pack f3030,pack f3626,pack f1487,pack f3603,pack f3598,pack f3634,pack f3675,pack f1396,pack f3857,pack f777,pack f772,pack f3622,pack f3611,pack f1332,pack f1102,pack f3593,pack f3663,pack f3654,pack f3798,pack f3541,pack f3595,pack f967,pack f1543,pack f3604,pack f3810,pack f955,pack f919,pack f750,pack f331,pack f323,pack f320,pack f631,pack f927,pack f569,pack f561,pack f3054,pack f935,pack f3552,pack f230,pack f908,pack f907,pack f904,pack f905,pack f1512,pack f3246,pack f1364,pack f1124,pack f3429,pack f1134,pack f1384,pack f1685,pack f1395,pack f1139,pack f642,pack f91,pack f225,pack f39,pack f220,pack f36,pack f3404,pack f135,pack f3522,pack f2726] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3859 : H a 0xa6382a321701 := rup [pack f1,pack f704,pack f3856,pack f3599,pack f3622,pack f3593,pack f3626,pack f3604,pack f3814,pack f3647,pack f3603,pack f325,pack f320,pack f3820,pack f3598,pack f3654,pack f3675,pack f3634,pack f3611,pack f715,pack f3858,pack f168,pack f1435,pack f1437,pack f1438,pack f1443,pack f1444,pack f1448,pack f2597,pack f2135,pack f1875,pack f3031,pack f1452,pack f3028,pack f3791,pack f3827,pack f3027,pack f1011,pack f1006,pack f985,pack f998,pack f2077,pack f571,pack f2140,pack f297,pack f3553,pack f3431,pack f2392,pack f2819,pack f979,pack f982,pack f1666,pack f3570] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3860 : H a 0xa6382a702867 := rup [pack f1,pack f3814,pack f3661,pack f3547,pack f3030,pack f704,pack f3856,pack f3599,pack f3622,pack f1543,pack f3626,pack f1487,pack f320,pack f3541,pack f3595,pack f631,pack f131,pack f1434,pack f1437,pack f1631,pack f1533,pack f3807,pack f1515,pack f3426,pack f132,pack f2364,pack f468] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3861 : H a 0xa6382a702219099 := rup [pack f1,pack f3541,pack f3595,pack f1515,pack f3860,pack f3814,pack f3661,pack f3831,pack f3659,pack f3815,pack f3547,pack f3030,pack f704,pack f3856,pack f3599,pack f3626,pack f1487,pack f3647,pack f2691,pack f3810,pack f750,pack f327,pack f325,pack f323,pack f3535,pack f631,pack f1631,pack f3032,pack f3807,pack f3849,pack f3426,pack f2587,pack f620,pack f344,pack f569,pack f2638,pack f595] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3862 : H a 0xa6382a702219 := rup [pack f1,pack f3860,pack f3547,pack f3030,pack f704,pack f3856,pack f3599,pack f3626,pack f3604,pack f3597,pack f3650,pack f1424,pack f3541,pack f3659,pack f3815,pack f3622,pack f1543,pack f3814,pack f3647,pack f3810,pack f3603,pack f557,pack f1322,pack f1094,pack f744,pack f323,pack f3709,pack f1506,pack f3861,pack f3041,pack f3031,pack f1522,pack f3028,pack f3801,pack f3038,pack f3037,pack f3044,pack f569,pack f77,pack f32,pack f2578,pack f123,pack f212,pack f3484] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3863 : H a 44619178785 := rup [pack f1,pack f3814,pack f3856,pack f3647,pack f3603,pack f704,pack f557,pack f3599,pack f1322,pack f1094,pack f744,pack f3547,pack f3030,pack f2031,pack f322,pack f3541,pack f3595,pack f3709,pack f967,pack f1969,pack f3859,pack f3659,pack f2073,pack f3862,pack f263,pack f1468,pack f277,pack f3444,pack f3484,pack f1588,pack f186] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3864 : H a 44619179778 := rup [pack f1,pack f3856,pack f3863,pack f899,pack f704,pack f3599,pack f3622,pack f1346,pack f3626,pack f3604,pack f694,pack f3814,pack f3647,pack f3603,pack f557,pack f1322,pack f1094,pack f955,pack f919,pack f744,pack f3547,pack f3030,pack f631,pack f3541,pack f3595,pack f927,pack f3709,pack f568,pack f753,pack f3597,pack f3659,pack f3862,pack f3650,pack f1116,pack f3707,pack f258,pack f1468,pack f1424,pack f3552,pack f3484,pack f271,pack f974,pack f960,pack f971,pack f186,pack f3717,pack f1835,pack f1059,pack f1267,pack f163,pack f1504,pack f201] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3865 : H a 44619178522 := rup [pack f1,pack f704,pack f3547,pack f3856,pack f744,pack f3814,pack f3647,pack f557,pack f3599,pack f1094,pack f1322,pack f3030,pack f3626,pack f1487,pack f3603,pack f3864,pack f3598,pack f3634,pack f3675,pack f1396,pack f3857,pack f3798,pack f3863,pack f899,pack f3810,pack f955,pack f919,pack f323,pack f631,pack f3541,pack f3595,pack f927,pack f258,pack f1437,pack f3552,pack f569,pack f958,pack f3062,pack f539,pack f3056,pack f3548] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3866 : H a 0x588485c88341490498219819 := rup [pack f1,pack f3690,pack f1471,pack f186,pack f3484] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3867 : H a 10893354 := rup [pack f1,pack f631,pack f3541,pack f3595,pack f927,pack f704,pack f3709,pack f3814,pack f557,pack f3547,pack f3030,pack f3856,pack f744,pack f3599,pack f3647,pack f919,pack f955,pack f1094,pack f3626,pack f3622,pack f1322,pack f3603,pack f694,pack f3604,pack f3593,pack f3863,pack f899,pack f3864,pack f3598,pack f3654,pack f3663,pack f3634,pack f3652,pack f1263,pack f1062,pack f679,pack f3865,pack f1426,pack f3866,pack f271,pack f1581,pack f3552,pack f166,pack f942,pack f3473,pack f1777,pack f3142,pack f2865,pack f3435] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3868 : H a 2659 := rup [pack f1,pack f631,pack f3541,pack f3595,pack f3867,pack f3521,pack f469,pack f3544,pack f1600,pack f116,pack f134,pack f3758,pack f3733,pack f3464] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3869 : H a 0xc88342322306 := rup [pack f1,pack f3599,pack f2888,pack f2496,pack f3437,pack f3585] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3870 : H a 0x5884c8c88485490498688 := rup [pack f1,pack f181,pack f3484] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3871 : H a 8558215 := rup [pack f1,pack f3521,pack f469,pack f273,pack f3716,pack f1761,pack f1770,pack f1774] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3872 : H a 0x6882195884c81e4564c88485342364490 := rup [pack f1,pack f3599,pack f1402,pack f3004,pack f3870,pack f503,pack f179,pack f2083,pack f1469,pack f543,pack f540,pack f1320] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3873 : H a 0x829219c88485 := rup [pack f1,pack f3521,pack f273,pack f3809,pack f3792,pack f3690,pack f3710,pack f3871,pack f1931,pack f2967,pack f3004,pack f3599,pack f1402,pack f3872,pack f16,pack f34,pack f376,pack f3770,pack f2554,pack f541,pack f540,pack f1088,pack f1091,pack f1081,pack f1469,pack f1079,pack f1085,pack f178,pack f1307,pack f356,pack f3499,pack f3564] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3874 : H a 0x83b219486941 := rup [pack f1,pack f1930,pack f3833,pack f3600,pack f180,pack f273,pack f3825,pack f3797,pack f3603,pack f3828,pack f1925,pack f1950,pack f2615,pack f2163,pack f1928,pack f579,pack f156,pack f2778,pack f2354,pack f3413] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3875 : H a 79591132923042 := rup [pack f1,pack f3600,pack f2778,pack f2354,pack f3413] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3876 : H a 0x4e45a44a8ca44a14ac4b4 := rup [pack f1,pack f589,pack f579] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3877 : H a 0x83b2191464b3 := rup [pack f1,pack f273,pack f3809,pack f3792,pack f3684,pack f3699,pack f469,pack f447,pack f464,pack f3737,pack f3732,pack f3426,pack f3557,pack f1943,pack f3403] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3878 : H a 35049804934 := rup [pack f1,pack f3521,pack f273,pack f3825,pack f3797,pack f180,pack f1930,pack f3833,pack f3874,pack f690,pack f3602,pack f1235,pack f1926,pack f150,pack f3875,pack f3877,pack f3876,pack f296,pack f315,pack f582,pack f2160,pack f3766,pack f3768,pack f3755,pack f3829,pack f233,pack f480,pack f3371] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3879 : H a 35049804971 := rup [pack f1,pack f3878,pack f3873,pack f3723,pack f233,pack f1786,pack f542,pack f3521,pack f1931,pack f1815,pack f296,pack f315,pack f3768,pack f1237,pack f3771,pack f3755,pack f3371] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3880 : H a 0x8292194a8ca41c2 := rup [pack f1,pack f3868,pack f3879,pack f3878,pack f3521,pack f1931,pack f3873,pack f1786,pack f1815,pack f2244,pack f1814,pack f2699,pack f191,pack f273,pack f3825,pack f3809,pack f3797,pack f3699,pack f469,pack f3614,pack f3615,pack f1941,pack f3831,pack f3426,pack f1539,pack f2613,pack f3288,pack f635,pack f3563,pack f3737,pack f3876,pack f3414,pack f3768,pack f2780,pack f2786,pack f1648,pack f2371,pack f2800,pack f3499] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3881 : H a 31344203403732 := rup [pack f1,pack f3556,pack f3403] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3882 : H a 0x8292198204a8ca4 := rup [pack f1,pack f3879,pack f3878,pack f3873,pack f3723,pack f1782,pack f3521,pack f1931,pack f1786,pack f1815,pack f1814,pack f3724,pack f273,pack f3825,pack f3792,pack f3797,pack f3684,pack f469,pack f3880,pack f3592,pack f3730,pack f1936,pack f1538,pack f3411,pack f1135,pack f3881,pack f498,pack f3557,pack f2730,pack f3755,pack f2721,pack f2731,pack f1063,pack f335,pack f362,pack f3732,pack f2297,pack f1490,pack f1218,pack f1604,pack f1325,pack f128,pack f1101,pack f1118,pack f1387,pack f1355,pack f1279,pack f464,pack f1748,pack f93,pack f40,pack f3876,pack f192,pack f1665,pack f1828,pack f217] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3883 : H a 0x83b21934216205a11a23c820ca3 := rup [pack f1,pack f255,pack f253,pack f236,pack f235,pack f3160,pack f3162,pack f3159,pack f3172,pack f1925,pack f2066,pack f2008,pack f27,pack f3603,pack f274,pack f2041,pack f1987,pack f264] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3884 : H a 1156263 := rup [pack f1,pack f3868,pack f100,pack f122,pack f1466,pack f3776,pack f3740,pack f3568,pack f3567] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3885 : H a 35049807012 := rup [pack f1,pack f3878,pack f3873,pack f3724,pack f3884,pack f1783,pack f3723,pack f1782,pack f3521,pack f273,pack f3792,pack f3684,pack f3882,pack f3880,pack f972,pack f3592,pack f1936,pack f3881,pack f2731] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3886 : H a 8557081 := rup [pack f1,pack f3521,pack f273,pack f3797,pack f3825,pack f3878,pack f1931,pack f3873,pack f1786,pack f3723,pack f3724,pack f1814,pack f1815,pack f1791,pack f458,pack f3879,pack f3884,pack f3885,pack f3159,pack f3883,pack f3877,pack f37,pack f591,pack f3115] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3887 : H a 0x8194a8ca36482c82502586a481fc87 := rup [pack f1,pack f3868,pack f88,pack f37,pack f750,pack f3802,pack f590,pack f1609,pack f3833,pack f191,pack f223,pack f3017,pack f2561,pack f2093,pack f2933,pack f552,pack f551,pack f160,pack f961,pack f1783,pack f1816,pack f152,pack f3607,pack f3796,pack f3081,pack f2619,pack f2167,pack f591] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3888 : H a 0x83b4a8ca36a480d119 := rup [pack f1,pack f3833,pack f273,pack f3796,pack f3161,pack f1927,pack f3183,pack f3607,pack f3079,pack f2167,pack f2619,pack f591] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3889 : H a 0x8294a8ca381f := rup [pack f1,pack f3521,pack f273,pack f3886,pack f3158,pack f3121,pack f3833,pack f1930,pack f750,pack f3802,pack f596,pack f643,pack f1254,pack f469,pack f1048,pack f1578,pack f1659,pack f37,pack f3887,pack f3888,pack f3160,pack f3177,pack f1938,pack f1937,pack f3171,pack f3170,pack f3216,pack f1493,pack f3163,pack f3819,pack f3842,pack f2652,pack f2199,pack f598,pack f3869] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3890 : H a 0x829ca382011a := rup [pack f1,pack f3521,pack f3833,pack f1930,pack f750,pack f3802,pack f3886,pack f3158,pack f590,pack f258,pack f273,pack f246,pack f3160,pack f3177,pack f1938,pack f1937,pack f3171,pack f3170,pack f3216,pack f1493,pack f1829,pack f3819,pack f3842,pack f2652,pack f44,pack f2199,pack f2512,pack f598,pack f3524,pack f956,pack f920,pack f3552] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3891 : H a 35052489891 := rup [pack f1,pack f3868,pack f3886,pack f258,pack f3521,pack f273,pack f596,pack f750,pack f3833,pack f3802,pack f1930,pack f3889,pack f3890,pack f3813,pack f3794,pack f3161,pack f1413,pack f3837,pack f1927,pack f1946,pack f1944,pack f230,pack f2564,pack f2097,pack f3605,pack f926,pack f3594,pack f551,pack f946,pack f910,pack f3552] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3892 : H a 0x83bca4119342246 := rup [pack f1,pack f3868,pack f3599,pack f1413,pack f1930,pack f676,pack f273,pack f3794,pack f3813,pack f1927,pack f2564,pack f2097,pack f551,pack f2495,pack f2886,pack f3437,pack f3583] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3893 : H a 0x83b348249948b08c93 := rup [pack f1,pack f469,pack f273,pack f513,pack f533,pack f2869,pack f1826,pack f1641,pack f1038,pack f1405,pack f1569,pack f1701,pack f1499,pack f1106,pack f146,pack f195,pack f3523,pack f193,pack f2878] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3894 : H a 0x8294a8119342262c87 := rup [pack f1,pack f3521,pack f3891,pack f3892,pack f1928,pack f3606,pack f273,pack f3083,pack f670,pack f3796,pack f3886,pack f3722,pack f1816,pack f1817,pack f2618,pack f2166,pack f3876,pack f1644,pack f1828,pack f3893,pack f3583,pack f392,pack f434,pack f2476,pack f1338,pack f1238,pack f1498,pack f1824,pack f1640,pack f1700,pack f1404,pack f1566,pack f145,pack f3523,pack f194,pack f2487,pack f193] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3895 : H a 0x829ca4119342c88 := rup [pack f1,pack f3521,pack f3892,pack f3599,pack f1413,pack f670,pack f273,pack f3701,pack f3686,pack f469,pack f3437,pack f513,pack f533,pack f3584,pack f1046,pack f392,pack f434,pack f1251,pack f160,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3896 : H a 0x8294a8119342 := rup [pack f1,pack f3891,pack f3895,pack f1784,pack f3894] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3897 : H a 0x83b4a8ca44e46a43414a1245 := rup [pack f1,pack f273,pack f1928,pack f3083,pack f3606,pack f2620,pack f2168,pack f579] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3898 : H a 0x83b4a8ca44e46a4341245 := rup [pack f1,pack f3868,pack f1931,pack f1928,pack f3897,pack f3606,pack f2822,pack f2395,pack f3568,pack f3567] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3899 : H a 57257420538708 := rup [pack f1,pack f3413,pack f3560] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3900 : H a 0x8294a8119364 := rup [pack f1,pack f3521,pack f3896,pack f1931,pack f3891,pack f273,pack f3796,pack f3830,pack f3898,pack f156,pack f3875,pack f469,pack f3899,pack f3561,pack f3767,pack f3736,pack f315,pack f464,pack f587,pack f3876] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3901 : H a 0x829820119c8258113c51cc1c19c89c91c := rup [pack f1,pack f3886,pack f263,pack f262,pack f3521,pack f274,pack f1968,pack f1953,pack f3438,pack f247] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3902 : H a 0x819c8248616896424658136391b226 := rup [pack f1,pack f2028,pack f2033,pack f2032,pack f3642,pack f2920,pack f2988,pack f2084,pack f2555,pack f547] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3903 : H a 0x8294a8820119 := rup [pack f1,pack f3891,pack f3886,pack f3521,pack f273,pack f3796,pack f3830,pack f3896,pack f3600,pack f1931,pack f1401,pack f3003,pack f3898,pack f156,pack f1927,pack f1879,pack f3875,pack f3900,pack f3806,pack f3805,pack f268,pack f269,pack f241,pack f244,pack f3901,pack f3902,pack f2029,pack f3595,pack f1932,pack f2172,pack f2624,pack f587,pack f3876] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3904 : H a 0x82982012019c341246225c1b := rup [pack f1,pack f3521,pack f1927,pack f3607,pack f1931,pack f156,pack f3875,pack f184,pack f3600,pack f3886,pack f258,pack f469,pack f273,pack f269,pack f430,pack f2057,pack f2059,pack f2060,pack f3806,pack f3591,pack f895,pack f3899,pack f3561,pack f3767,pack f3766,pack f2777,pack f2756,pack f2771,pack f2773,pack f2763,pack f3736,pack f2353,pack f2848,pack f1293,pack f2794,pack f390,pack f948,pack f3738,pack f1066,pack f1650,pack f3499,pack f3442,pack f3552,pack f3636,pack f3666,pack f922] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3905 : H a 0x82934124689b := rup [pack f1,pack f3521,pack f1927,pack f3607,pack f156,pack f1931,pack f184,pack f3600,pack f469,pack f273,pack f244,pack f387,pack f2003,pack f2002,pack f3698,pack f3843,pack f3728,pack f3808,pack f3805,pack f124,pack f3899,pack f3561,pack f3767,pack f3766,pack f2777,pack f2771,pack f2766,pack f3735,pack f317,pack f1345,pack f2901,pack f435,pack f2666,pack f1111,pack f203,pack f3587,pack f3433,pack f610] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3906 : H a 0x83b4a8ca434124685b := rup [pack f1,pack f1931,pack f156,pack f3875,pack f1927,pack f273,pack f236,pack f1973,pack f3824,pack f3829,pack f3602,pack f1925,pack f2615,pack f2163,pack f3876,pack f585] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3907 : H a 0x8294a8820341246 := rup [pack f1,pack f3903,pack f255,pack f251,pack f246,pack f3891,pack f3886,pack f263,pack f3871,pack f3521,pack f3905,pack f3906,pack f274,pack f2057,pack f3904,pack f2058,pack f2063,pack f2064,pack f1942,pack f3782,pack f3744,pack f1925,pack f3581,pack f3577] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3908 : H a 0x8294a8820341 := rup [pack f1,pack f3868,pack f3903,pack f3891,pack f3521,pack f273,pack f3600,pack f1931,pack f1412,pack f3907,pack f1928,pack f3083,pack f1947,pack f1945,pack f3606,pack f1948,pack f2563,pack f2096,pack f696,pack f657,pack f2620,pack f2168,pack f1933,pack f555,pack f197,pack f3899,pack f3875,pack f3561,pack f2777,pack f3876,pack f2353,pack f1681,pack f2940,pack f3432,pack f422,pack f3569,pack f2950,pack f529] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3909 : H a 0x83b4a8ca43425a44e3 := rup [pack f1,pack f1930,pack f273,pack f665,pack f3795,pack f2939,pack f1949,pack f2171,pack f2623,pack f736,pack f585] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3910 : H a 0x8194a8ca43425a44e44a14ac := rup [pack f1,pack f3876,pack f583,pack f2606,pack f3828,pack f3121,pack f3138,pack f3115] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3911 : H a 0x82915cc814852454ab := rup [pack f1,pack f3521,pack f1928,pack f3606,pack f296,pack f315,pack f379,pack f2154,pack f2152,pack f3768,pack f1237,pack f3771,pack f3755,pack f2554,pack f2158,pack f3371] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3912 : H a 0x8294a8820245 := rup [pack f1,pack f3868,pack f3521,pack f3908,pack f1930,pack f3599,pack f3903,pack f249,pack f3891,pack f3871,pack f469,pack f273,pack f2836,pack f1928,pack f3083,pack f2424,pack f3572,pack f3606,pack f3909,pack f3911,pack f3910,pack f1665,pack f3432,pack f357,pack f422,pack f3569,pack f1313,pack f1593,pack f495,pack f529,pack f1084,pack f3870,pack f188] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3913 : H a 96849505174924 := rup [pack f1,pack f3574,pack f3571] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3914 : H a 0x829354258a5427490658b593251066 := rup [pack f1,pack f3521,pack f469,pack f3741,pack f3886,pack f260,pack f2432,pack f2433,pack f2434,pack f2834,pack f2805,pack f484,pack f2734] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3915 : H a 35052488736 := rup [pack f1,pack f3891,pack f3886,pack f3521,pack f3903,pack f3908,pack f674,pack f3599,pack f1930,pack f3912,pack f154,pack f155,pack f1927,pack f1946,pack f1944,pack f3607,pack f3773,pack f3644,pack f3648,pack f2564,pack f3605,pack f3715,pack f1929,pack f3594,pack f3729,pack f2167,pack f2619,pack f665,pack f3498,pack f1514,pack f736,pack f1436,pack f1425,pack f172,pack f1397,pack f587,pack f579,pack f1644,pack f1123,pack f207,pack f204,pack f3913,pack f381,pack f3573,pack f2437,pack f1148,pack f506,pack f3914,pack f983,pack f1407,pack f95] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3916 : H a 96849706403236 := rup [pack f1,pack f3913,pack f3572] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3917 : H a 35358110278 := rup [pack f1,pack f88,pack f37,pack f1927,pack f3607,pack f962,pack f2845,pack f2438,pack f3916,pack f3821,pack f3822,pack f3092] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3918 : H a 35052487490 := rup [pack f1,pack f3521,pack f273,pack f3915,pack f3917,pack f3083,pack f3891,pack f3599,pack f1930,pack f3896,pack f964,pack f3909,pack f249,pack f3910,pack f3911] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3919 : H a 8557736 := rup [pack f1,pack f3521,pack f3891,pack f3915,pack f3917,pack f3918,pack f965,pack f584,pack f588,pack f3898] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3920 : H a 2089 := rup [pack f1,pack f3868,pack f3521,pack f273,pack f3886,pack f263,pack f3919,pack f100,pack f180,pack f1471,pack f3884,pack f2967,pack f3599,pack f1467,pack f1473,pack f3813,pack f3794,pack f1413,pack f3606,pack f3625,pack f3621,pack f236,pack f1928,pack f2564,pack f2097,pack f1929,pack f2027,pack f1934,pack f3917,pack f551,pack f2062,pack f2006,pack f274] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3921 : H a 2095 := rup [pack f1,pack f3920,pack f320] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3922 : H a 2107 := rup [pack f1,pack f3920,pack f322] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3923 : H a 2155 := rup [pack f1,pack f3920,pack f323] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3924 : H a 2219 := rup [pack f1,pack f3920,pack f325] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3925 : H a 2347 := rup [pack f1,pack f3920,pack f327] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3926 : H a 2603 := rup [pack f1,pack f3920,pack f329] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3927 : H a 3115 := rup [pack f1,pack f3920,pack f331] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3928 : H a 2385063 := rup [pack f1,pack f3868,pack f3922,pack f156,pack f155,pack f100,pack f122,pack f180,pack f580,pack f3884,pack f3763,pack f3734,pack f1467,pack f3413,pack f3562,pack f3606,pack f3625,pack f3599,pack f1470,pack f2055,pack f2564,pack f2097,pack f1971,pack f2027,pack f3813,pack f3794,pack f551,pack f2069,pack f2009,pack f3444] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3929 : H a 0x2463424854c86886642e4581 := rup [pack f1,pack f3920,pack f3922,pack f3868,pack f1305,pack f3599,pack f676,pack f3928,pack f155,pack f3607,pack f1903,pack f1862,pack f2564,pack f2097,pack f3625,pack f1871,pack f1920,pack f3555,pack f551,pack f1885,pack f1093,pack f191,pack f185,pack f177] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3930 : H a 0x4984a84856885884c8490 := rup [pack f1,pack f177,pack f188] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3931 : H a 0x2463424a1485119819 := rup [pack f1,pack f3920,pack f3868,pack f1305,pack f3928,pack f159,pack f3689,pack f3718,pack f3813,pack f3794,pack f3929,pack f718,pack f3606,pack f3432,pack f3569,pack f2820,pack f376,pack f3930] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3932 : H a 0xa483424a148511991c582 := rup [pack f1,pack f3921,pack f3923,pack f3868,pack f3926,pack f3599,pack f2019,pack f1956,pack f3606,pack f1884,pack f925,pack f3432,pack f3438,pack f352,pack f3569,pack f2386,pack f2393,pack f2379,pack f2391,pack f268,pack f254,pack f2820,pack f2390,pack f1489,pack f3832,pack f3800,pack f241,pack f1213,pack f1445,pack f1541,pack f1545,pack f3817,pack f3851,pack f3811,pack f3845,pack f3522,pack f565,pack f562,pack f630,pack f2024,pack f3414] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3933 : H a 0x2463424a1485119 := rup [pack f1,pack f3599,pack f3928,pack f159,pack f3931,pack f278,pack f3082,pack f3932,pack f3607,pack f3644,pack f3648,pack f2167,pack f2619,pack f665,pack f736,pack f3876,pack f591] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3934 : H a 0x24634248513c581 := rup [pack f1,pack f3922,pack f3599,pack f3607,pack f1903,pack f1862,pack f1871,pack f1920,pack f3555] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3935 : H a 40008732513413 := rup [pack f1,pack f3868,pack f3599,pack f159,pack f3933,pack f248,pack f3160,pack f3934,pack f3606,pack f3432,pack f2386,pack f2393,pack f2479,pack f508,pack f3437,pack f3583] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3936 : H a 40008732515492 := rup [pack f1,pack f3868,pack f3935,pack f187,pack f3599,pack f676,pack f155,pack f3437,pack f508,pack f3584,pack f2886,pack f2868,pack f2872,pack f2885,pack f1517,pack f1120,pack f384,pack f2474,pack f2479,pack f2494,pack f1747,pack f1844,pack f3786,pack f1356,pack f1832,pack f1650,pack f3748,pack f204,pack f288,pack f459,pack f3016,pack f2932,pack f551] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3937 : H a 0x348c814a1486b24305145150158491c8b := rup [pack f1,pack f384,pack f2482,pack f1832,pack f1650,pack f1407,pack f2509,pack f3523,pack f3524,pack f3683,pack f149,pack f3680,pack f3697] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3938 : H a 0x5944984a191010e918b24964491928c93126988d08b14954489 := rup [pack f1,pack f1832,pack f1650,pack f204,pack f3586,pack f3565,pack f3499,pack f2740,pack f2857,pack f3524,pack f1998,pack f2627,pack f509] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3939 : H a 40008732513425 := rup [pack f1,pack f3920,pack f3868,pack f3936,pack f3182,pack f3155,pack f61,pack f3183,pack f3151,pack f22,pack f3160,pack f3839,pack f3158,pack f3935,pack f3003,pack f3837,pack f3162,pack f3215,pack f1356,pack f1119,pack f187,pack f184,pack f1305,pack f3599,pack f2835,pack f159,pack f156,pack f1517,pack f3937,pack f3585,pack f2886,pack f2869,pack f2874,pack f2871,pack f1747,pack f1844,pack f2896,pack f2795,pack f3938,pack f381,pack f2810,pack f3575,pack f3569,pack f3916,pack f3567,pack f3606] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3940 : H a 9767756961 := rup [pack f1,pack f3868,pack f3922,pack f159,pack f3935,pack f187,pack f3936,pack f3160,pack f3183,pack f3837,pack f3839,pack f231,pack f259,pack f3939,pack f508,pack f3585,pack f2476,pack f2383,pack f3432,pack f1871,pack f1920,pack f1883,pack f3555] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3941 : H a 9767758996 := rup [pack f1,pack f3868,pack f3940,pack f590,pack f3599,pack f159,pack f3437,pack f187,pack f3583,pack f2495,pack f2479,pack f1784,pack f2386,pack f248,pack f3432,pack f3934,pack f3606] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3942 : H a 2384706 := rup [pack f1,pack f3868,pack f3920,pack f2835,pack f159,pack f3940,pack f586,pack f3941,pack f2886,pack f2868,pack f2872,pack f2809,pack f3786,pack f3787,pack f3569,pack f3567,pack f1718,pack f3606,pack f3573,pack f3916] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3943 : H a 0x246a4258b587816a1cc218a16102904924300b006a := rup [pack f1,pack f3921,pack f3926,pack f994,pack f2423,pack f202,pack f2306,pack f172,pack f2374,pack f3942,pack f3600,pack f3741,pack f1103,pack f1711,pack f2437,pack f3606,pack f700,pack f153,pack f283,pack f1719,pack f1707,pack f1734,pack f3553,pack f1728,pack f2420,pack f937,pack f2504,pack f2415,pack f2039,pack f1984,pack f29,pack f1007,pack f1002,pack f2460,pack f2231,pack f2148,pack f2507,pack f418,pack f374,pack f420] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3944 : H a 40038794925218 := rup [pack f1,pack f3920,pack f3925,pack f3606,pack f3942,pack f3600,pack f1879,pack f2835,pack f156,pack f586,pack f3875,pack f3916,pack f381,pack f3573,pack f2423,pack f3741,pack f3742,pack f2437,pack f2422,pack f2419,pack f2425,pack f1518,pack f1706,pack f1721,pack f1711,pack f2344,pack f439,pack f460,pack f279,pack f1165,pack f2677,pack f2593,pack f3413,pack f456,pack f481,pack f3561,pack f2775,pack f2749,pack f3762,pack f3761,pack f2774,pack f1126,pack f1072,pack f2980,pack f32,pack f12,pack f3943,pack f1708,pack f3711,pack f1736,pack f1720,pack f1730,pack f1732,pack f2429,pack f313,pack f566,pack f1492,pack f3110,pack f3253,pack f3076,pack f3200,pack f622,pack f601] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3945 : H a 40018379412900 := rup [pack f1,pack f3920,pack f3942,pack f2835,pack f156,pack f3916,pack f381,pack f3573,pack f2423,pack f184,pack f2344,pack f2776,pack f3413] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3946 : H a 0x2464a1489831485 := rup [pack f1,pack f3942,pack f156,pack f2776,pack f2344,pack f3413] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3947 : H a 0xc34874a348388318b4 := rup [pack f1,pack f3922,pack f467,pack f473] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3948 : H a 9775096417 := rup [pack f1,pack f3920,pack f3606,pack f3942,pack f2835,pack f156,pack f3944,pack f3945,pack f3082,pack f3103,pack f1706,pack f1209,pack f3575,pack f363,pack f381,pack f403,pack f2423,pack f3741,pack f3742,pack f443,pack f461,pack f3946,pack f2757,pack f3413,pack f343,pack f393,pack f2710,pack f2635,pack f3947] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3949 : H a 0xc8234b48505a58731c861845838889c091384380b8072 := rup [pack f1,pack f437,pack f1103,pack f1727,pack f3554,pack f2196,pack f2416,pack f2505,pack f1185,pack f394,pack f411] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3950 : H a 2386498 := rup [pack f1,pack f3920,pack f3942,pack f3600,pack f2835,pack f156,pack f3606,pack f3948,pack f554,pack f2438,pack f3899,pack f3916,pack f485,pack f3561,pack f2757,pack f586,pack f3082,pack f3824,pack f3825,pack f3103,pack f3575,pack f3079,pack f2341,pack f2776,pack f2344,pack f233,pack f262,pack f1401,pack f1705,pack f3084,pack f1209,pack f2767,pack f2768,pack f1168,pack f2349,pack f2350,pack f2754,pack f1196,pack f1156,pack f2752,pack f3949,pack f1712,pack f3712,pack f1735,pack f1729,pack f1741,pack f2781,pack f2720,pack f1036,pack f1646,pack f286,pack f494,pack f3098,pack f2996,pack f1642,pack f2928,pack f1570,pack f146,pack f482,pack f3001,pack f543] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3951 : H a 9772958853 := rup [pack f1,pack f3868,pack f3920,pack f3950,pack f3942,pack f159,pack f3432,pack f3569,pack f487,pack f1092,pack f495,pack f352,pack f1203,pack f1160,pack f1321,pack f3600,pack f3607,pack f3643,pack f3596,pack f357,pack f3647,pack f1167,pack f3709,pack f3721,pack f3928,pack f2813,pack f3484,pack f186,pack f1752,pack f1759,pack f1751,pack f1765,pack f1601,pack f437,pack f1182,pack f3554] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3952 : H a 2385030 := rup [pack f1,pack f3868,pack f3920,pack f3942,pack f3950,pack f3622,pack f656,pack f3626,pack f695,pack f159,pack f3432,pack f3569,pack f3607,pack f3600,pack f154,pack f2757,pack f1960,pack f2563,pack f488] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3953 : H a 582 := rup [pack f1,pack f3868,pack f159,pack f3928,pack f3942,pack f3600,pack f3721,pack f3950,pack f3607,pack f3709,pack f3432,pack f3626,pack f3622,pack f3647,pack f352,pack f357,pack f3569,pack f1321,pack f487,pack f495,pack f1092,pack f3952,pack f2386,pack f2813,pack f3484,pack f3951,pack f186,pack f1773,pack f1768,pack f1767,pack f1216,pack f1211,pack f1597,pack f936,pack f902,pack f952,pack f916,pack f960,pack f2817,pack f3552,pack f19] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3954 : H a 0x831485a4158212a4905882494a89a4d24353 := rup [pack f1,pack f3925,pack f2682,pack f674,pack f3760,pack f3721,pack f1321,pack f3647,pack f3643,pack f3484,pack f3810,pack f3844,pack f3720,pack f1768,pack f616,pack f615] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3955 : H a 0x83734ca53354c82 := rup [pack f1,pack f3953,pack f3920,pack f702,pack f3773,pack f1208,pack f2618,pack f3778,pack f90,pack f468,pack f529,pack f2324,pack f495,pack f2459,pack f1084,pack f487,pack f2166,pack f2424,pack f129,pack f746,pack f748,pack f3599,pack f378,pack f1214,pack f3413,pack f1321,pack f2810,pack f1611,pack f3783,pack f3757,pack f502] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3956 : H a 35287226963 := rup [pack f1,pack f3953,pack f3924,pack f3921,pack f468,pack f2344,pack f90,pack f487,pack f495,pack f529,pack f702,pack f3773,pack f2813,pack f2212,pack f3101,pack f1084,pack f1733,pack f1208,pack f1480,pack f2678,pack f3181,pack f3111,pack f3254,pack f1509,pack f3954,pack f3955,pack f3600,pack f1213,pack f2820,pack f1518,pack f2811,pack f2809,pack f2818,pack f3774,pack f3775,pack f3433,pack f2632,pack f755,pack f3840,pack f612,pack f3188,pack f3195,pack f3197,pack f3798,pack f1435,pack f3202,pack f685,pack f2987,pack f3807,pack f2995,pack f3199,pack f1533,pack f3831,pack f1550,pack f593,pack f130] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3957 : H a 44369713736 := rup [pack f1,pack f3868,pack f3432,pack f3569] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3958 : H a 0x837485a47c8113212a := rup [pack f1,pack f3953,pack f3868,pack f3600,pack f1213,pack f2562,pack f3802,pack f169,pack f129,pack f215,pack f2022,pack f1976,pack f90,pack f2362,pack f2301,pack f2414,pack f2503,pack f3956,pack f3568,pack f468,pack f2424,pack f304,pack f307,pack f1667,pack f1679,pack f1681,pack f1680,pack f2378,pack f2377,pack f2381,pack f1418,pack f2095,pack f3793,pack f3812,pack f551,pack f2521,pack f2440,pack f401,pack f360,pack f400,pack f359,pack f1676] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3959 : H a 0x837485354582c81 := rup [pack f1,pack f3920,pack f3953,pack f3868,pack f3956,pack f3606,pack f3957,pack f215,pack f90,pack f169,pack f2211,pack f2130,pack f129,pack f2022,pack f1976,pack f2362,pack f2301,pack f2414,pack f2503,pack f3568,pack f1208,pack f2682,pack f2594,pack f2678,pack f1884,pack f1246,pack f468,pack f2424,pack f3600,pack f1166,pack f1213,pack f2554,pack f2562,pack f2660,pack f449,pack f3958,pack f3706,pack f3705,pack f1668,pack f1669,pack f1666,pack f2383,pack f2384,pack f1678,pack f2382,pack f1958,pack f3756,pack f3772,pack f484,pack f2441,pack f2523,pack f360,pack f401,pack f359,pack f400,pack f1675] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3960 : H a 0x49c4ac58c4cc48968cc8c := rup [pack f1,pack f375,pack f377] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3961 : H a 0x837485354582 := rup [pack f1,pack f3953,pack f3868,pack f3956,pack f468,pack f2424,pack f129,pack f90,pack f3606,pack f3957,pack f169,pack f215,pack f3568,pack f2455,pack f2318,pack f2157,pack f1993,pack f3959,pack f2386,pack f746,pack f1670,pack f3960] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3962 : H a 0x485a4224a4984a86884c8132 := rup [pack f1,pack f1077,pack f1792,pack f3930,pack f185] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3963 : H a 0x837485581489 := rup [pack f1,pack f3920,pack f3953,pack f1209,pack f468,pack f1045,pack f3703,pack f3607,pack f1214,pack f1613,pack f1226,pack f1225,pack f3599,pack f1305,pack f1481,pack f731,pack f660,pack f1257,pack f1419,pack f3962,pack f3687,pack f3702,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3964 : H a 0x8374853544c2 := rup [pack f1,pack f468,pack f2344,pack f3961,pack f3963,pack f1213,pack f3413,pack f3695,pack f447,pack f3559,pack f600,pack f3600,pack f1629,pack f197,pack f1970,pack f3833,pack f379,pack f129,pack f1959,pack f3607,pack f3956,pack f90,pack f665,pack f3595,pack f3645,pack f1215,pack f1853,pack f897,pack f1965,pack f1952,pack f3769,pack f2584,pack f1287,pack f1954,pack f1483,pack f2826,pack f2746,pack f229,pack f491,pack f3876,pack f3106,pack f3086,pack f3093] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3965 : H a 35287225172 := rup [pack f1,pack f3956,pack f468,pack f2344,pack f129,pack f90,pack f3961,pack f1959,pack f3963,pack f376,pack f1213,pack f3600,pack f3721,pack f3413,pack f150,pack f3559,pack f1629,pack f2048,pack f546,pack f3804,pack f56,pack f3964,pack f3788,pack f3642,pack f2702,pack f1383,pack f1901,pack f2014,pack f944,pack f731,pack f3602,pack f1207,pack f1477,pack f2042,pack f1988,pack f2864,pack f2915,pack f3484,pack f257,pack f526,pack f3714,pack f1730] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3966 : H a 0x8374855814c1 := rup [pack f1,pack f3953,pack f3925,pack f1209,pack f3607,pack f3965,pack f485,pack f3760,pack f129,pack f2756,pack f2779,pack f1119,pack f2030,pack f3764,pack f100,pack f468,pack f674,pack f1080,pack f3721,pack f3749,pack f3642,pack f731,pack f3602,pack f1207,pack f1319,pack f3484,pack f3714,pack f1740,pack f185,pack f2445,pack f2535,pack f1584,pack f409,pack f405] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3967 : H a 35287225729 := rup [pack f1,pack f3920,pack f3953,pack f3965,pack f129,pack f3765,pack f2753,pack f3764,pack f2751,pack f2769,pack f3760,pack f2756,pack f2779,pack f100,pack f674,pack f3833,pack f485,pack f2165,pack f468,pack f2344,pack f90,pack f3966,pack f665,pack f3595,pack f3645,pack f1334,pack f1503,pack f2662,pack f1215,pack f1853,pack f3656,pack f3658,pack f2584,pack f2625,pack f712,pack f715,pack f2569,pack f753,pack f755,pack f2546,pack f3876,pack f3083,pack f3822,pack f3096,pack f45,pack f3208,pack f2191,pack f2552,pack f442,pack f436,pack f601,pack f1103,pack f1831,pack f3561,pack f198] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3968 : H a 8615045 := rup [pack f1,pack f3953,pack f3925,pack f468,pack f129,pack f90,pack f3965,pack f485,pack f674,pack f3760,pack f3764,pack f1080,pack f100,pack f3967,pack f718,pack f3606,pack f1208,pack f3647,pack f3643,pack f1884,pack f2132,pack f2212,pack f3111,pack f3254,pack f2081,pack f2194,pack f301,pack f3954,pack f299] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3969 : H a 35288261441 := rup [pack f1,pack f3953,pack f3922,pack f3606,pack f3968,pack f3600,pack f1214,pack f3626,pack f3622,pack f1872,pack f1921,pack f1902,pack f1861,pack f2821,pack f1211,pack f1216,pack f3555,pack f3957,pack f1677,pack f302] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3970 : H a 79621199010388 := rup [pack f1,pack f3868,pack f3957,pack f3568,pack f1671,pack f2385] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3971 : H a 8615298 := rup [pack f1,pack f3953,pack f3968,pack f187,pack f3606,pack f1208,pack f3969,pack f3599,pack f1213,pack f3970,pack f487,pack f2812,pack f3181,pack f2873,pack f3437] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3972 : H a 2103 := rup [pack f1,pack f3920,pack f3953,pack f3923,pack f90,pack f129,pack f468,pack f2424,pack f3968,pack f184,pack f2757,pack f3971,pack f3607,pack f1209,pack f2091,pack f1959,pack f3913,pack f351,pack f586,pack f3083,pack f3104,pack f3822,pack f3823,pack f3079,pack f3575,pack f1119,pack f275,pack f2966,pack f44,pack f506,pack f2833,pack f3780,pack f3779,pack f3559,pack f96,pack f3413,pack f3599,pack f1213,pack f1224,pack f1223,pack f3648,pack f1041,pack f1518,pack f1832,pack f1650,pack f1357,pack f3605,pack f3715,pack f1212,pack f3594,pack f3729,pack f1217,pack f1207,pack f204,pack f2103,pack f1962,pack f362,pack f2074,pack f1951,pack f402,pack f1856,pack f287,pack f234,pack f346,pack f340] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3973 : H a 0xc88c81c8cca4 := rup [pack f1,pack f3437,pack f3584] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3974 : H a 0xc8858134212a48924a := rup [pack f1,pack f3972,pack f3953,pack f3923,pack f3926,pack f3599,pack f1187,pack f1148,pack f305,pack f303,pack f3607,pack f3621,pack f3594,pack f3625,pack f3605,pack f348,pack f1159,pack f1202,pack f3554,pack f59,pack f450,pack f2480,pack f3973,pack f3585,pack f3835,pack f3836,pack f508,pack f2227,pack f2137,pack f2103,pack f2074,pack f1009,pack f983,pack f285,pack f282,pack f312,pack f2881,pack f3430] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3975 : H a 0xa42342130249ca3 := rup [pack f1,pack f3953,pack f3921,pack f3599,pack f3161,pack f3181,pack f3155,pack f3179,pack f3180,pack f986,pack f1015,pack f1000,pack f980,pack f3553] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3976 : H a 0xc8858134212a249 := rup [pack f1,pack f3953,pack f3923,pack f3926,pack f305,pack f303,pack f300,pack f3607,pack f3621,pack f3594,pack f3625,pack f3605,pack f3599,pack f3975,pack f3437,pack f3973,pack f508,pack f2869,pack f2882,pack f2480,pack f2492,pack f2098,pack f1009,pack f983,pack f2475,pack f2473,pack f2103,pack f2074,pack f2227,pack f2137,pack f285,pack f282,pack f312,pack f2881,pack f3430] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3977 : H a 79600796573994 := rup [pack f1,pack f3925,pack f3953,pack f3607,pack f3621,pack f3789,pack f3846,pack f3594,pack f3625,pack f2689,pack f2036,pack f3781,pack f3826,pack f3605,pack f3599,pack f3648,pack f3644,pack f670,pack f3703,pack f187,pack f3976,pack f347,pack f3974,pack f2897,pack f3236,pack f3011,pack f2803,pack f1520,pack f1362,pack f522,pack f615,pack f1415,pack f1249,pack f1579,pack f1663,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3978 : H a 0xa4234207823813824a := rup [pack f1,pack f3972,pack f1159,pack f1202,pack f3554] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3979 : H a 19433788226 := rup [pack f1,pack f3953,pack f3972,pack f3607,pack f187,pack f672,pack f676,pack f3599,pack f3625,pack f3621,pack f3644,pack f3648,pack f3595,pack f3977,pack f2873,pack f1324,pack f1385,pack f3437,pack f590,pack f3161,pack f3585,pack f253,pack f384,pack f392,pack f2480,pack f1285,pack f1382,pack f1148,pack f1187,pack f1169,pack f455,pack f3978,pack f1360,pack f3975,pack f89,pack f3513,pack f20,pack f103,pack f993,pack f994,pack f996,pack f997,pack f2193,pack f3834,pack f3746,pack f1497,pack f1105,pack f1832,pack f2498,pack f3070,pack f2410,pack f3186,pack f399,pack f605,pack f3524] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3980 : H a 79591134237540 := rup [pack f1,pack f3920,pack f2757,pack f3899,pack f3559,pack f1613,pack f2343] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3981 : H a 0x81982089cc1c91ca1c := rup [pack f1,pack f3922,pack f276,pack f3444] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3982 : H a 19433788553 := rup [pack f1,pack f3920,pack f3953,pack f3922,pack f3979,pack f3600,pack f3607,pack f1883,pack f2757,pack f184,pack f3980,pack f554,pack f2982,pack f2966,pack f2965,pack f962,pack f2962,pack f3083,pack f3806,pack f3805,pack f2974,pack f2975,pack f3913,pack f3573,pack f2010,pack f2070,pack f268,pack f1453,pack f241,pack f1505,pack f2424,pack f2436,pack f2421,pack f2431,pack f2430,pack f2844,pack f2343,pack f991,pack f2015,pack f1955,pack f1403,pack f1497,pack f1165,pack f3413,pack f108,pack f102,pack f1628,pack f924,pack f256,pack f3981,pack f280,pack f2046,pack f1972,pack f3642] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3983 : H a 0x831c348b4934874 := rup [pack f1,pack f3922,pack f3972,pack f474,pack f3947] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3984 : H a 4744577 := rup [pack f1,pack f3920,pack f3953,pack f3922,pack f3972,pack f2757,pack f184,pack f3607,pack f1883,pack f3979,pack f3600,pack f3982,pack f381,pack f2981,pack f2659,pack f2553,pack f1168,pack f3913,pack f3899,pack f586,pack f3083,pack f3575,pack f150,pack f3559,pack f1612,pack f1621,pack f1620,pack f343,pack f351,pack f2341,pack f3736,pack f3735,pack f2591,pack f2669,pack f2712,pack f2636,pack f2844,pack f3102,pack f3100,pack f3099,pack f1066,pack f1111,pack f456,pack f923,pack f991,pack f1037,pack f1105,pack f26,pack f3398,pack f3983,pack f2574,pack f471,pack f3642,pack f2697] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3985 : H a 4744001 := rup [pack f1,pack f3920,pack f3953,pack f3922,pack f3984,pack f1246,pack f3606,pack f2757,pack f3600,pack f3626,pack f3622,pack f1872,pack f1921,pack f3643,pack f1960,pack f1902,pack f2563,pack f1861,pack f695,pack f656,pack f3555,pack f488,pack f1886,pack f3957,pack f215] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3986 : H a 79597578496583 := rup [pack f1,pack f3953,pack f3922,pack f3920,pack f3985,pack f3599,pack f3646,pack f3672,pack f3731,pack f3754,pack f3596,pack f3655,pack f3604,pack f3637,pack f3602,pack f3667,pack f1911,pack f3609,pack f3631,pack f1294,pack f3620,pack f3657,pack f3598,pack f3984,pack f2583,pack f1852,pack f1880,pack f3606,pack f722,pack f720,pack f169,pack f215,pack f1874,pack f1980,pack f2136,pack f2598,pack f3555,pack f1892,pack f1905,pack f1889,pack f1890,pack f1887,pack f2642,pack f206,pack f2713,pack f2828,pack f2688,pack f501,pack f3983,pack f3441,pack f1067,pack f2411,pack f365] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3987 : H a 19433002562 := rup [pack f1,pack f3920,pack f3868,pack f3953,pack f3985,pack f3596,pack f3657,pack f3691,pack f3599,pack f3646,pack f670,pack f3984,pack f1246,pack f3606,pack f182,pack f694,pack f3672,pack f3683,pack f3986,pack f3432,pack f3957,pack f422,pack f2395,pack f2394,pack f2385,pack f529,pack f2812,pack f2821,pack f1399,pack f1051,pack f1418,pack f1034,pack f1228,pack f141,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3988 : H a 19433003592 := rup [pack f1,pack f3920,pack f3868,pack f3953,pack f3987,pack f3628,pack f679,pack f3984,pack f3606,pack f3624,pack f654,pack f3985,pack f3596,pack f3657,pack f3598,pack f3605,pack f3649,pack f3655,pack f3707,pack f3599,pack f670,pack f1246,pack f182,pack f3432,pack f3957,pack f422,pack f2395,pack f2394,pack f2385,pack f529,pack f2812,pack f2821,pack f1433,pack f1051,pack f1418,pack f1056,pack f1262,pack f165,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3989 : H a 4744385 := rup [pack f1,pack f3953,pack f3922,pack f3920,pack f3985,pack f3599,pack f1880,pack f3984,pack f3606,pack f722,pack f720,pack f3596,pack f3646,pack f3655,pack f3657,pack f1852,pack f3602,pack f2583,pack f3609,pack f3598,pack f3987,pack f3605,pack f3624,pack f1873,pack f3628,pack f3638,pack f3669,pack f3649,pack f1346,pack f681,pack f683,pack f3988,pack f169,pack f215,pack f1922,pack f2026,pack f2214,pack f2680,pack f3555,pack f1906,pack f1889,pack f1898,pack f1888,pack f1899,pack f208,pack f2637,pack f2690,pack f2890,pack f2716,pack f521,pack f3983,pack f3412,pack f1112,pack f2499,pack f3587,pack f404] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3990 : H a 19438794305 := rup [pack f1,pack f3922,pack f3953,pack f3920,pack f3924,pack f3927,pack f3984,pack f3989,pack f3641,pack f3985,pack f3599,pack f1880,pack f1900,pack f3595,pack f3606,pack f215,pack f1923,pack f1876,pack f3555,pack f1857,pack f208,pack f187,pack f1854,pack f3869,pack f1859,pack f231,pack f1999,pack f3677,pack f3434,pack f169,pack f3679,pack f3591,pack f777,pack f3601,pack f742,pack f3603,pack f722,pack f3605,pack f3826,pack f3624,pack f3632,pack f3671,pack f3640,pack f3666,pack f3649,pack f2043,pack f1346,pack f710,pack f754,pack f2641,pack f1860,pack f1966,pack f1542,pack f2071,pack f2716,pack f957,pack f2025,pack f2782,pack f265,pack f521,pack f1488,pack f2953,pack f3412,pack f597,pack f645] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3991 : H a 0x3283643a432133472432c := rup [pack f1,pack f598,pack f605] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3992 : H a 4745799 := rup [pack f1,pack f3953,pack f3922,pack f3920,pack f3984,pack f3606,pack f3989,pack f3595,pack f3677,pack f3601,pack f741,pack f3679,pack f1900,pack f3985,pack f3599,pack f1880,pack f676,pack f722,pack f187,pack f169,pack f215,pack f1923,pack f1876,pack f3555,pack f231,pack f284,pack f1854,pack f1855,pack f1493,pack f3869,pack f3990,pack f3604,pack f1294,pack f3630,pack f3673,pack f3651,pack f3670,pack f1863,pack f1858,pack f3818,pack f3777,pack f2597,pack f1979,pack f3759,pack f1323,pack f2642,pack f2012,pack f1864,pack f2722,pack f501,pack f514,pack f3436,pack f2663,pack f2208,pack f3201,pack f3991] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3993 : H a 1158 := rup [pack f1,pack f3868,pack f3953,pack f3925,pack f3984,pack f3606,pack f3985,pack f3599,pack f1880,pack f3989,pack f3641,pack f3992,pack f3432,pack f3957,pack f2394,pack f487,pack f2812,pack f995,pack f2085,pack f2132,pack f2212,pack f306,pack f299] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3994 : H a 0x342b23702641c05aa4a41 := rup [pack f1,pack f3993,pack f3953,pack f3868,pack f3926,pack f3922,pack f3597,pack f763,pack f1853,pack f3216,pack f3844,pack f3599,pack f1880,pack f3607,pack f3679,pack f1873,pack f3633,pack f1531,pack f3664,pack f777,pack f1907,pack f635,pack f3555,pack f2703,pack f2698,pack f1919] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3995 : H a 0x34232133432832c724 := rup [pack f1,pack f3920,pack f3953,pack f3925,pack f3922,pack f3993,pack f1969,pack f1305,pack f3599,pack f676,pack f3991,pack f574,pack f578,pack f715,pack f3818,pack f602,pack f2061,pack f621,pack f763,pack f3844,pack f3216,pack f3688,pack f3660,pack f3629,pack f3630,pack f3073,pack f3831,pack f963,pack f3826,pack f3994,pack f3606,pack f3621,pack f3636,pack f3648,pack f3846,pack f2036,pack f2689,pack f3716,pack f1099,pack f1511,pack f622,pack f549,pack f3004,pack f2049,pack f277,pack f3981,pack f1470,pack f1714,pack f3930] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3996 : H a 0x3427233a39a4e021ac1b40bca8156417416805a := rup [pack f1,pack f3953,pack f3993,pack f3922,pack f3840,pack f3818,pack f3634,pack f1891,pack f3635,pack f3820,pack f3599,pack f1880,pack f676,pack f231,pack f3190,pack f1449,pack f3555,pack f2086,pack f575,pack f267,pack f1922,pack f545,pack f3811,pack f3189] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3997 : H a 0x3420603287233a3858641 := rup [pack f1,pack f3920,pack f3953,pack f3868,pack f3840,pack f3818,pack f3634,pack f3603,pack f1234,pack f3635,pack f3607,pack f1246,pack f3828,pack f755,pack f715,pack f3660,pack f3595,pack f578,pack f611,pack f3599,pack f676,pack f3605,pack f3826,pack f3628,pack f3674,pack f3624,pack f2134,pack f2596,pack f1873,pack f3669,pack f3649,pack f3638,pack f685,pack f777,pack f657,pack f1231,pack f1269,pack f3415,pack f2227,pack f3071,pack f3187,pack f1422,pack f2565,pack f1183,pack f2556,pack f1408,pack f3996,pack f3074,pack f3841,pack f3191,pack f1457,pack f3077,pack f1532,pack f2695,pack f2100,pack f1003,pack f115,pack f627,pack f556] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3998 : H a 0x7233a3642d241b4934610059 := rup [pack f1,pack f3920,pack f3953,pack f3925,pack f715,pack f3604,pack f3637,pack f1366,pack f3840,pack f3818,pack f3634,pack f3603,pack f3672,pack f3790,pack f694,pack f3716,pack f3635,pack f3820,pack f755,pack f3660,pack f763,pack f574,pack f1846,pack f1450,pack f3074,pack f3841,pack f1521,pack f3077,pack f1513,pack f213,pack f2127,pack f3440,pack f575,pack f3005,pack f620] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3999 : H a 0x3423213343287233a3 := rup [pack f1,pack f3993,pack f3920,pack f3953,pack f3922,pack f3840,pack f755,pack f626,pack f611,pack f3599,pack f900,pack f1880,pack f676,pack f574,pack f715,pack f3818,pack f1283,pack f3635,pack f3634,pack f3607,pack f3820,pack f3603,pack f1891,pack f1246,pack f1234,pack f3997,pack f3604,pack f3620,pack f3672,pack f3653,pack f1911,pack f1267,pack f3846,pack f2679,pack f2213,pack f3790,pack f1233,pack f3415,pack f3071,pack f2591,pack f1171,pack f2557,pack f1409,pack f456,pack f449,pack f1125,pack f3998,pack f231,pack f3073,pack f1504,pack f3555,pack f2087,pack f612,pack f239,pack f1867,pack f548,pack f3811,pack f3072] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4000 : H a 0xc81b231c1885642 := rup [pack f1,pack f3993,pack f3953,pack f3922,pack f3868,pack f3926,pack f3850,pack f3592,pack f763,pack f1853,pack f3216,pack f3844,pack f1880,pack f3604,pack f3627,pack f3639,pack f1911,pack f1904,pack f3831,pack f1531,pack f3555,pack f635,pack f1865,pack f2703,pack f2698] (by dsimp only [pack,List.map]; decide +kernel)
end BorsukCert

namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4001 : H a 0x34232133432832c := rup [pack f1,pack f3920,pack f3953,pack f3925,pack f3922,pack f3993,pack f1969,pack f1305,pack f3599,pack f676,pack f3995,pack f611,pack f626,pack f755,pack f3840,pack f2004,pack f3999,pack f603,pack f621,pack f763,pack f3844,pack f3216,pack f3688,pack f3612,pack f3613,pack f3190,pack f968,pack f3594,pack f3846,pack f4000,pack f3605,pack f3826,pack f3671,pack f2036,pack f2689,pack f3666,pack f731,pack f1511,pack f622,pack f1099,pack f549,pack f3004,pack f2049,pack f281,pack f3444,pack f1470,pack f1714,pack f3930] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4002 : H a 3416875 := rup [pack f1,pack f3953,pack f3922,pack f3993,pack f3599,pack f1880,pack f305,pack f313,pack f2192,pack f2196,pack f2205,pack f2206,pack f2873,pack f3725,pack f2201,pack f2202,pack f504,pack f2195,pack f665,pack f3595,pack f2193,pack f3437,pack f2198,pack f2197,pack f1853,pack f3161,pack f1869,pack f1914,pack f3884,pack f3555,pack f259,pack f1889,pack f1891,pack f1893,pack f3085,pack f2162,pack f3127,pack f591] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4003 : H a 53707177096 := rup [pack f1,pack f106,pack f112,pack f3747,pack f3785,pack f3437,pack f3585] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4004 : H a 0x25c31c22014616223ca1b := rup [pack f1,pack f2052,pack f2053,pack f2045,pack f2047,pack f3618,pack f2038,pack f1982,pack f264] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4005 : H a 53707150119 := rup [pack f1,pack f3953,pack f3993,pack f3922,pack f1969,pack f106,pack f112,pack f196,pack f1493,pack f1958,pack f3785,pack f3747,pack f2065,pack f2007,pack f4003,pack f3583,pack f590,pack f3161,pack f3172,pack f3173,pack f2030,pack f2019,pack f1797,pack f1783,pack f27,pack f28,pack f68,pack f3159,pack f1786,pack f1812,pack f311,pack f4004,pack f3444,pack f1495,pack f1462,pack f1525,pack f3644,pack f1531,pack f1414,pack f113] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4006 : H a 3416883 := rup [pack f1,pack f3953,pack f3922,pack f3993,pack f3599,pack f1880,pack f455,pack f460,pack f2643,pack f2649,pack f2660,pack f2661,pack f2480,pack f3726,pack f2654,pack f2656,pack f379,pack f2648,pack f665,pack f3595,pack f2646,pack f3973,pack f2651,pack f2650,pack f1853,pack f3161,pack f1869,pack f1914,pack f3884,pack f3555,pack f259,pack f1889,pack f1891,pack f1893,pack f3085,pack f2614,pack f3126,pack f591] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4007 : H a 57365878160523 := rup [pack f1,pack f3920,pack f3953,pack f3993,pack f3161,pack f4006,pack f4002,pack f3599,pack f4003,pack f4001,pack f3869,pack f3163,pack f3177,pack f3159,pack f3173,pack f3156,pack f3172,pack f3152,pack f3884,pack f1305,pack f2480,pack f2493,pack f2472,pack f2497,pack f2482,pack f2477,pack f1772,pack f3178,pack f1595,pack f1726,pack f3870,pack f178] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4008 : H a 14005341347 := rup [pack f1,pack f3920,pack f3953,pack f3993,pack f4006,pack f4002,pack f3599,pack f4003,pack f4001,pack f3869,pack f1305,pack f3161,pack f3163,pack f3172,pack f3173,pack f3884,pack f3177,pack f3152,pack f3156,pack f3159,pack f4007,pack f3585,pack f2873,pack f2884,pack f2889,pack f2883,pack f2874,pack f2870,pack f2869,pack f1772,pack f1592,pack f1719,pack f3870,pack f178] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4009 : H a 3419272 := rup [pack f1,pack f3953,pack f3920,pack f3993,pack f4006,pack f4002,pack f1305,pack f3599,pack f4003,pack f4001,pack f3869,pack f4008,pack f3437,pack f3973,pack f2873,pack f2883,pack f2874,pack f2869,pack f2480,pack f2476,pack f1759,pack f1597,pack f1709,pack f1479,pack f3870,pack f178] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4010 : H a 13995486347 := rup [pack f1,pack f3953,pack f3993,pack f3923,pack f3868,pack f3926,pack f4009,pack f1818,pack f1793,pack f439,pack f1782,pack f3722,pack f1783,pack f249,pack f2577,pack f1819,pack f604,pack f384,pack f2480,pack f2472,pack f2492,pack f2496,pack f2490,pack f2474,pack f1439,pack f1806,pack f3146,pack f3280,pack f3747,pack f3068,pack f2960,pack f2368,pack f1647,pack f1810,pack f61,pack f567,pack f1536,pack f630,pack f3414,pack f3566,pack f2791,pack f2729,pack f3371] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4011 : H a 14005453602 := rup [pack f1,pack f3953,pack f3920,pack f3993,pack f3923,pack f3868,pack f4009,pack f1782,pack f1818,pack f1819,pack f3722,pack f2577,pack f1787,pack f4010,pack f3583,pack f508,pack f2873,pack f2867,pack f2888,pack f2881,pack f1440,pack f1800,pack f2859,pack f1759,pack f3131,pack f3068,pack f2960,pack f2796,pack f1645,pack f567,pack f3491,pack f3565,pack f3499,pack f3602] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4012 : H a 3416865 := rup [pack f1,pack f4006,pack f4002,pack f3599,pack f4005,pack f4001] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4013 : H a 3416617 := rup [pack f1,pack f3953,pack f3927,pack f3924,pack f4012,pack f4009,pack f1818,pack f4011,pack f1819,pack f3184,pack f2011,pack f2072,pack f1787,pack f286,pack f3150,pack f8,pack f1782,pack f3722,pack f1783,pack f249,pack f1793,pack f3153,pack f4010,pack f223,pack f191,pack f672,pack f3725,pack f1803,pack f1810,pack f1790,pack f2784,pack f2723,pack f1800,pack f1788,pack f1809,pack f3154,pack f2467,pack f2541,pack f3157,pack f2445,pack f2535,pack f2335,pack f2400,pack f386,pack f429,pack f428,pack f385,pack f2917,pack f1562,pack f2986,pack f1632,pack f3556,pack f3563,pack f346,pack f340] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4014 : H a 834 := rup [pack f1,pack f3953,pack f3927,pack f3924,pack f3868,pack f676,pack f4009,pack f4012,pack f1782,pack f1818,pack f1819,pack f4010,pack f4011,pack f3722,pack f3838,pack f3153,pack f1793,pack f1787,pack f3184,pack f1783,pack f3158,pack f1785,pack f441,pack f288,pack f2072,pack f2011,pack f4013,pack f1802,pack f1789,pack f1811,pack f3155,pack f3181,pack f2543,pack f2468,pack f3169,pack f2444,pack f2529,pack f2402,pack f2336,pack f386,pack f429,pack f428,pack f385,pack f2929,pack f3012,pack f552,pack f551] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4015 : H a 3201 := rup [pack f1,pack f4014,pack f3600] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4016 : H a 3235 := rup [pack f1,pack f4014,pack f3833] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4017 : H a 3219 := rup [pack f1,pack f4014,pack f3784] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4018 : H a 3211 := rup [pack f1,pack f4014,pack f3745] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4019 : H a 3207 := rup [pack f1,pack f4014,pack f3721] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4020 : H a 0x4c84a8490588688 := rup [pack f1,pack f3993,pack f4019,pack f179,pack f3870] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4021 : H a 14566081364 := rup [pack f1,pack f4014,pack f3899,pack f3559] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4022 : H a 58562165642084 := rup [pack f1,pack f4014,pack f3993,pack f3923,pack f3868,pack f3920,pack f4017,pack f3899,pack f4021,pack f150,pack f197,pack f1611,pack f393,pack f2342,pack f2344,pack f2351,pack f2612,pack f3068,pack f2960,pack f1440,pack f2577,pack f1606,pack f2339,pack f567,pack f562,pack f243,pack f56,pack f2861,pack f2843,pack f505,pack f502] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4023 : H a 23250942890313 := rup [pack f1,pack f3920,pack f4014,pack f4019,pack f3993,pack f1752,pack f481,pack f4022,pack f546,pack f600,pack f2967,pack f1318,pack f1096,pack f3484,pack f3870,pack f3884,pack f1472,pack f1475,pack f1594] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4024 : H a 5676499729 := rup [pack f1,pack f4014,pack f3953,pack f3993,pack f3923,pack f3920,pack f4017,pack f1752,pack f481,pack f4023,pack f343,pack f345,pack f4021,pack f3413,pack f554,pack f600,pack f2967,pack f197,pack f1611,pack f1608,pack f1621,pack f1628,pack f1994,pack f1969,pack f2406,pack f2337,pack f2962,pack f1064,pack f2393,pack f1615,pack f2964,pack f382,pack f3114,pack f354,pack f447,pack f56,pack f3580,pack f2841,pack f505,pack f502] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4025 : H a 5676499788 := rup [pack f1,pack f4014,pack f3920,pack f4019,pack f3993,pack f4024,pack f1583,pack f1752,pack f481,pack f4021,pack f3413,pack f2967,pack f1611,pack f1608,pack f1621,pack f1628,pack f2964,pack f376,pack f56,pack f3870] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4026 : H a 0x6885884c8149363 := rup [pack f1,pack f4019,pack f3993,pack f4014,pack f546,pack f554,pack f600,pack f1318,pack f3870,pack f1097,pack f1086,pack f1100,pack f1082] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4027 : H a 1385864 := rup [pack f1,pack f4014,pack f3920,pack f3993,pack f4019,pack f1752,pack f481,pack f4024,pack f1583,pack f4025,pack f343,pack f2344,pack f4026,pack f3899,pack f1611,pack f1626,pack f2352,pack f2340,pack f580,pack f80,pack f3484,pack f178] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4028 : H a 5672047460 := rup [pack f1,pack f4014,pack f3993,pack f3920,pack f4017,pack f4027,pack f1752,pack f481,pack f3899,pack f4021,pack f4022,pack f150,pack f197,pack f1611,pack f393,pack f2344,pack f1583,pack f2612,pack f2352,pack f2342,pack f1737,pack f584,pack f588,pack f2449,pack f2313,pack f1308,pack f1992,pack f3558,pack f3580,pack f507,pack f502] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4029 : H a 1384777 := rup [pack f1,pack f3993,pack f3920,pack f4014,pack f3972,pack f4027,pack f1709,pack f481,pack f2699,pack f4028,pack f554,pack f2967,pack f1739,pack f1722,pack f351,pack f1710,pack f1712,pack f3413,pack f3696,pack f3695,pack f443,pack f466,pack f448,pack f3947] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4030 : H a 338 := rup [pack f1,pack f3920,pack f4014,pack f3972,pack f481,pack f4027,pack f172,pack f202,pack f1709,pack f4029,pack f343,pack f4021,pack f3413,pack f554,pack f150,pack f197,pack f1739,pack f2700,pack f2709,pack f2580,pack f2634,pack f1710,pack f3947] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4031 : H a 0xc10c1cd0cc09e0c := rup [pack f1,pack f3927,pack f4018,pack f428,pack f433] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4032 : H a 14559527751 := rup [pack f1,pack f3993,pack f3953,pack f4014,pack f3920,pack f4030,pack f554,pack f2070,pack f546,pack f1138,pack f2967,pack f150,pack f1621,pack f2543,pack f4031] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4033 : H a 22691978968073 := rup [pack f1,pack f4030,pack f4015,pack f3920,pack f3953,pack f4014,pack f3972,pack f3993,pack f343,pack f554,pack f1709,pack f2535,pack f4032,pack f3413,pack f718,pack f2967,pack f1722,pack f1146,pack f1739,pack f1165,pack f2070,pack f546,pack f1138,pack f1175,pack f1156,pack f2752,pack f2964,pack f4031,pack f3554,pack f2911,pack f3262,pack f77,pack f3589,pack f2973,pack f226] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4034 : H a 5540033927 := rup [pack f1,pack f3993,pack f3953,pack f4014,pack f3920,pack f2967,pack f554,pack f343,pack f1709,pack f1721,pack f1722,pack f2436,pack f2535,pack f4032,pack f3413,pack f4033,pack f2768,pack f2842,pack f3079,pack f3572] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4035 : H a 5540035594 := rup [pack f1,pack f3920,pack f4015,pack f4014,pack f4030,pack f3993,pack f4019,pack f4034,pack f546,pack f1089,pack f2967,pack f343,pack f2963,pack f1621,pack f2979,pack f2984,pack f2985,pack f2978,pack f2972,pack f3803,pack f2971,pack f3413,pack f2754,pack f1985,pack f2143,pack f1074,pack f3115,pack f2851,pack f190,pack f80,pack f3141,pack f2748,pack f122,pack f2862,pack f2311,pack f2417,pack f3484,pack f3582,pack f373,pack f3578] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4036 : H a 5540033363 := rup [pack f1,pack f4014,pack f3953,pack f3993,pack f4019,pack f4030,pack f3922,pack f4035,pack f2964,pack f3262,pack f56,pack f4034,pack f554,pack f2070,pack f546,pack f1138,pack f1089,pack f485,pack f2752,pack f2535,pack f100,pack f2911,pack f4031,pack f3484,pack f3589,pack f773,pack f3752,pack f2539,pack f2543,pack f2538,pack f3716,pack f219,pack f1878,pack f1851,pack f3617,pack f1897,pack f1918,pack f1868,pack f3555] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4037 : H a 1352547 := rup [pack f1,pack f4014,pack f3920,pack f3993,pack f3925,pack f3953,pack f3868,pack f345,pack f343,pack f554,pack f2967,pack f2031,pack f4036,pack f3413,pack f1611,pack f1608,pack f4032,pack f2393,pack f1120,pack f2516,pack f3750,pack f412,pack f2535,pack f3743,pack f487,pack f3623,pack f3568,pack f3957] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4038 : H a 5550159898 := rup [pack f1,pack f4015,pack f3953,pack f3993,pack f4014,pack f3925,pack f3972,pack f3920,pack f343,pack f4037,pack f4021,pack f485,pack f2535,pack f2521,pack f3751,pack f45,pack f435,pack f2525,pack f2524,pack f2533,pack f1337,pack f2534,pack f1236,pack f923,pack f3750,pack f1346,pack f1156,pack f3561,pack f1611,pack f1175,pack f345,pack f278,pack f1608,pack f1620,pack f2516,pack f1119,pack f1358,pack f1196,pack f412,pack f3554,pack f3743,pack f60,pack f1294] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4039 : H a 1355019 := rup [pack f1,pack f3920,pack f4015,pack f3993,pack f3953,pack f3925,pack f343,pack f4037,pack f4021,pack f3561,pack f1611,pack f485,pack f435,pack f766,pack f3750,pack f2535,pack f2524,pack f4038,pack f1609,pack f3693,pack f3694,pack f1622,pack f2749,pack f2779,pack f2772,pack f1836,pack f1516,pack f1743,pack f390,pack f3762,pack f2681,pack f3235,pack f3010,pack f2902,pack f2847,pack f3412,pack f3576,pack f623] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4040 : H a 5544974474 := rup [pack f1,pack f3993,pack f4015,pack f3920,pack f3926,pack f343,pack f4037,pack f4021,pack f3561,pack f150,pack f3121,pack f1609,pack f2779,pack f2756,pack f2852,pack f1613,pack f1753,pack f3579,pack f3577,pack f3647,pack f3739,pack f1611,pack f3645,pack f1133,pack f2056,pack f3749,pack f2749,pack f3762,pack f35,pack f3694,pack f269,pack f4039,pack f391,pack f2770,pack f427,pack f4031] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4041 : H a 1353753 := rup [pack f1,pack f4015,pack f4030,pack f3993,pack f3920,pack f3926,pack f4014,pack f343,pack f4037,pack f4021,pack f3561,pack f1611,pack f150,pack f1609,pack f3694,pack f3121,pack f2779,pack f266,pack f1607,pack f2756,pack f1613,pack f2852,pack f1753,pack f3579,pack f3577,pack f3602,pack f3645,pack f3647,pack f3619,pack f3616,pack f1891,pack f2233,pack f2149,pack f2204,pack f2094,pack f3601,pack f1366,pack f3430,pack f1386,pack f4040,pack f2754,pack f1196,pack f1614,pack f1271,pack f1352,pack f2862,pack f81,pack f3504,pack f1779,pack f3435,pack f3141] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4042 : H a 0x6a44a14ac4a84b44e4 := rup [pack f1,pack f4016,pack f579,pack f587] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4043 : H a 330 := rup [pack f1,pack f4014,pack f3953,pack f3920,pack f3993,pack f3925,pack f343,pack f345,pack f4037,pack f4021,pack f485,pack f3561,pack f2165,pack f1611,pack f4039,pack f4041,pack f278,pack f1608,pack f1621,pack f2750,pack f2516,pack f1119,pack f2752,pack f1615,pack f410,pack f100,pack f447,pack f405,pack f3134,pack f2946,pack f4042] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4044 : H a 2611 := rup [pack f1,pack f4043,pack f3993,pack f2699] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4045 : H a 1191 := rup [pack f1,pack f4043,pack f4030,pack f4014,pack f1476] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4046 : H a 3111 := rup [pack f1,pack f4043,pack f4030,pack f4014,pack f1555] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4047 : H a 2215 := rup [pack f1,pack f4043,pack f4014,pack f4030,pack f1491] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4048 : H a 28527178923 := rup [pack f1,pack f3953,pack f4014,pack f4030,pack f3920,pack f3083,pack f3820,pack f2159,pack f2164,pack f2169,pack f2170,pack f2854,pack f3602,pack f3105,pack f3491,pack f1760] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4049 : H a 5911779 := rup [pack f1,pack f3953,pack f4043,pack f4030,pack f4014,pack f3993,pack f4019,pack f4045,pack f3920,pack f3972,pack f3083,pack f3820,pack f724,pack f665,pack f3795,pack f3642,pack f3676,pack f3678,pack f731,pack f3602,pack f1191,pack f1151,pack f1319,pack f1090,pack f3484,pack f1721,pack f1722,pack f1177,pack f1170,pack f1146,pack f3554] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4050 : H a 19887965603 := rup [pack f1,pack f4045,pack f3953,pack f4014,pack f4043,pack f3920,pack f3820,pack f3083,pack f4048,pack f4049,pack f4042,pack f2607,pack f2617,pack f2608,pack f2616,pack f2626,pack f3080,pack f2860,pack f1762,pack f3602,pack f2621,pack f2456,pack f3577] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4051 : H a 6964403 := rup [pack f1,pack f3953,pack f4043,pack f4014,pack f3923,pack f3868,pack f4044,pack f3972,pack f3920,pack f2607,pack f2608,pack f2620,pack f2604,pack f2616,pack f2626,pack f2629,pack f2605,pack f2860,pack f3606,pack f2611,pack f692,pack f3602,pack f2610,pack f3656,pack f3658,pack f2576,pack f3799,pack f3816,pack f2718,pack f2640,pack f1447,pack f3491,pack f562,pack f3947,pack f1769] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4052 : H a 19887965356 := rup [pack f1,pack f4016,pack f4045,pack f4051,pack f4050,pack f585,pack f4042] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4053 : H a 4855460 := rup [pack f1,pack f4045,pack f4016,pack f3953,pack f4030,pack f4014,pack f4050,pack f4051,pack f4052,pack f2164,pack f2154,pack f582,pack f2174,pack f3795] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4054 : H a 1185 := rup [pack f1,pack f4043,pack f4015,pack f3920,pack f3993,pack f4030,pack f4014,pack f3953,pack f4045,pack f4016,pack f4046,pack f3921,pack f4047,pack f3972,pack f4053,pack f3828,pack f3136,pack f3115,pack f150,pack f3120,pack f2967,pack f3083,pack f3829,pack f3830,pack f3899,pack f1492,pack f1412,pack f485,pack f3561,pack f2776,pack f2767,pack f2768,pack f2165,pack f351,pack f2352,pack f381,pack f2755,pack f1179,pack f1524,pack f1461,pack f2617,pack f506,pack f1001,pack f589,pack f3572,pack f3571,pack f117,pack f3797,pack f1437,pack f3522] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4055 : H a 1699 := rup [pack f1,pack f4054,pack f588] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4056 : H a 0x2582c8648250a48268 := rup [pack f1,pack f3953,pack f157,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4057 : H a 0x942b02912687 := rup [pack f1,pack f4015,pack f4043,pack f3920,pack f4054,pack f3602,pack f3595,pack f3642,pack f1052,pack f1246,pack f3665,pack f3700,pack f3668,pack f3685,pack f1754,pack f1769,pack f1775,pack f1750,pack f1420,pack f1665,pack f4056] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4058 : H a 39773546770 := rup [pack f1,pack f3993,pack f4019,pack f4045,pack f4055,pack f4043,pack f3920,pack f4014,pack f3602,pack f3595,pack f3642,pack f3606,pack f718,pack f1098,pack f4057,pack f3491,pack f3484,pack f4020,pack f3580,pack f2853,pack f2861,pack f1321,pack f1308,pack f1312,pack f1585,pack f2458,pack f2447] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4059 : H a 9710338 := rup [pack f1,pack f3993,pack f3920,pack f4015,pack f4054,pack f4043,pack f4030,pack f3922,pack f3602,pack f3595,pack f3668,pack f3665,pack f3642,pack f2037,pack f3685,pack f3700,pack f1246,pack f1052,pack f4058,pack f1421,pack f1002,pack f981,pack f4056,pack f160,pack f1683,pack f1682,pack f1665,pack f3704,pack f1608,pack f3694,pack f1535,pack f1406,pack f1502,pack f1446,pack f1528,pack f1463,pack f244,pack f1423,pack f269,pack f1398,pack f110,pack f109,pack f97,pack f95,pack f1967,pack f2044,pack f3444] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4060 : H a 0x942911d01250268258 := rup [pack f1,pack f4030,pack f3953,pack f3972,pack f4044,pack f4015,pack f3993,pack f4043,pack f4014,pack f3920,pack f4054,pack f3921,pack f4059,pack f3656,pack f3596,pack f3594,pack f3610,pack f2714,pack f3602,pack f3643,pack f2584,pack f3607,pack f3623,pack f2639,pack f3947,pack f1057,pack f1112,pack f1014,pack f1035,pack f988,pack f3685,pack f981,pack f3703,pack f3608,pack f932,pack f1109,pack f4056,pack f158,pack f1652,pack f1653,pack f1660,pack f1662,pack f1611,pack f1627,pack f1625,pack f1610,pack f1005,pack f1065,pack f902,pack f406,pack f1070,pack f3553,pack f9,pack f21] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4061 : H a 0x581d01e24c34257 := rup [pack f1,pack f4054,pack f4046,pack f4016,pack f3927,pack f49,pack f69,pack f1244,pack f1252,pack f1255,pack f3848,pack f1248,pack f642,pack f638] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4062 : H a 27943572071 := rup [pack f1,pack f4015,pack f4030,pack f4055,pack f98,pack f1412,pack f2448,pack f1766,pack f3580,pack f3577] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4063 : H a 39771512065 := rup [pack f1,pack f4015,pack f4014,pack f4043,pack f4054,pack f4046,pack f4016,pack f3927,pack f3602,pack f4062,pack f4059,pack f3656,pack f3608,pack f3596,pack f3643,pack f3594,pack f3681,pack f3610,pack f777,pack f2714,pack f4061,pack f4060,pack f10,pack f30,pack f1054,pack f1047,pack f3847,pack f642,pack f638] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4064 : H a 0xe08e01e24e0c := rup [pack f1,pack f3588,pack f3590] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4065 : H a 0xd02aa4a2824f := rup [pack f1,pack f4015,pack f4054,pack f4043,pack f3868,pack f3926,pack f4044,pack f3682,pack f10,pack f1043,pack f1044,pack f1050,pack f3204,pack f1847,pack f3753,pack f637,pack f4064] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4066 : H a 0xa48268d02648832250c22 := rup [pack f1,pack f4015,pack f3920,pack f1261,pack f1577,pack f4056] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4067 : H a 0xd24c34c21e24 := rup [pack f1,pack f4046,pack f4016,pack f3927,pack f642,pack f638] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4068 : H a 9709841 := rup [pack f1,pack f4015,pack f3993,pack f3953,pack f4014,pack f4044,pack f3972,pack f4043,pack f4030,pack f3920,pack f4055,pack f3602,pack f4059,pack f3596,pack f3643,pack f2584,pack f3703,pack f3658,pack f4062,pack f4063,pack f769,pack f3593,pack f3662,pack f3666,pack f2715,pack f3831,pack f2638,pack f1539,pack f3700,pack f3947,pack f4065,pack f4066,pack f4067,pack f3288,pack f2854,pack f2450,pack f3491,pack f3578] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4069 : H a 27942658374 := rup [pack f1,pack f3920,pack f4055,pack f2854,pack f2450,pack f3491,pack f3578] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4070 : H a 9710850 := rup [pack f1,pack f3993,pack f4015,pack f3953,pack f4014,pack f4043,pack f4030,pack f3868,pack f4044,pack f3926,pack f3920,pack f4068,pack f524,pack f3602,pack f4059,pack f3596,pack f3643,pack f2584,pack f3658,pack f687,pack f769,pack f3593,pack f3682,pack f3662,pack f2715,pack f3683,pack f3831,pack f2638,pack f1539,pack f3983,pack f4069,pack f3288,pack f635,pack f3414,pack f4067,pack f1643,pack f1040,pack f1240,pack f1627,pack f147,pack f3523] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4071 : H a 2370 := rup [pack f1,pack f3993,pack f3953,pack f3972,pack f4030,pack f4043,pack f4014,pack f3868,pack f4016,pack f4047,pack f3924,pack f4044,pack f3926,pack f4017,pack f3920,pack f4015,pack f687,pack f3602,pack f4059,pack f3596,pack f3656,pack f3643,pack f3608,pack f3607,pack f2584,pack f4068,pack f525,pack f4070,pack f3594,pack f3670,pack f3681,pack f3623,pack f3610,pack f728,pack f775,pack f777,pack f2639,pack f1538,pack f2714,pack f1392,pack f3947,pack f4069,pack f3147,pack f2068,pack f595,pack f635,pack f532,pack f592,pack f3414,pack f531,pack f1239,pack f1626,pack f1039,pack f1571,pack f1410,pack f3523] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4072 : H a 1665 := rup [pack f1,pack f4071,pack f3603] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4073 : H a 1671 := rup [pack f1,pack f4071,pack f3716] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4074 : H a 1175 := rup [pack f1,pack f4071,pack f4043,pack f4014,pack f1319] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4075 : H a 1167 := rup [pack f1,pack f4071,pack f4014,pack f4030,pack f1090] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4076 : H a 1079 := rup [pack f1,pack f4071,pack f4043,pack f4014,pack f1201] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4077 : H a 183 := rup [pack f1,pack f4071,pack f4043,pack f4014,pack f1158] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4078 : H a 1218 := rup [pack f1,pack f4072,pack f4015,pack f3645] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4079 : H a 1416 := rup [pack f1,pack f4074,pack f4075,pack f4045,pack f4073,pack f4019,pack f3993,pack f3484] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4080 : H a 2851 := rup [pack f1,pack f4078,pack f3844] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4081 : H a 594 := rup [pack f1,pack f4079,pack f3920,pack f1709] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4082 : H a 1224 := rup [pack f1,pack f4079,pack f4073,pack f4075,pack f4019,pack f4045,pack f4074,pack f185] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4083 : H a 198 := rup [pack f1,pack f4082,pack f142] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4084 : H a 1094 := rup [pack f1,pack f4082,pack f162] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4085 : H a 2355 := rup [pack f1,pack f4084,pack f3953,pack f4083,pack f2683] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4086 : H a 2098 := rup [pack f1,pack f3920,pack f4082,pack f4079,pack f4081,pack f3953,pack f4072,pack f4085,pack f3925,pack f4080,pack f1599,pack f1710,pack f1598,pack f1704,pack f3111,pack f3254,pack f1511,pack f619,pack f615] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4087 : H a 561 := rup [pack f1,pack f4086,pack f4079,pack f3714] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4088 : H a 113 := rup [pack f1,pack f4086,pack f4079,pack f3713] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4089 : H a 585 := rup [pack f1,pack f4086,pack f4079,pack f1711] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4090 : H a 567 := rup [pack f1,pack f4087,pack f457] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4091 : H a 119 := rup [pack f1,pack f4088,pack f437] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4092 : H a 311 := rup [pack f1,pack f4089,pack f4015,pack f1165] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4093 : H a 0 := rup [pack f1,pack f4091,pack f4090,pack f4076,pack f4092,pack f3972,pack f4077,pack f3554] (by dsimp only [pack,List.map]; decide +kernel)
end BorsukCert


namespace OAI.BorsukNine.FiniteObstruction
open BorsukCert
theorem no_fixed_ten_system {T Q : Family} (h : TenSystem T Q) (h0 : Q fixed) : False := by
  letI := system_legal h h0
  have hh := f4093 (a := coloring T Q)
  exact valid_nil hh

theorem no_ten_system {T Q : Family} (h : TenSystem T Q) (hQ : ∃ S, Q S) : False := by
  obtain ⟨S,hS⟩ := hQ
  obtain ⟨e,he⟩ := Equiv.Perm.exists_map_finset_eq fixed S (by rw [h.tetra_card S hS]; decide)
  exact no_fixed_ten_system (h.relabel e) (by simpa only [he] using hS)
end OAI.BorsukNine.FiniteObstruction

theorem OMA.solution : OMA.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1_H1_R1.H3 := by
  rintro T Q ⟨hc,hd,hp,hb,hm,hn⟩
  exact OAI.BorsukNine.FiniteObstruction.no_ten_system ⟨hc,hd,hp,hb,hm,hn⟩
