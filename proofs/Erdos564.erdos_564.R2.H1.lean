import OMAReductions.R_Erdos564_erdos_564_R2

/-! Four-colour stepping up (Erdős–Hajnal; see Erdős, Hajnal, Máté and Rado, Set Theory: Partition Relations for Cardinals, 1984). The graph seed uses the finite counting argument of Erdős (1947). The parent reduction is by @tamoghnokandar. -/
namespace FourColour

lemma graph_seed (d t : ℕ) (size : 2 * d.choose t < 2 ^ t.choose 2) :
    ∃ c : ℕ → ℕ → Bool, ∀ S : Finset ℕ, S ⊆ Finset.range d → S.card = t →
      ∀ b : Bool, ¬ (∀ x ∈ S, ∀ y ∈ S, x < y → c x y = b) := by
  classical
  let V := Finset.range d
  let E := V.powersetCard 2
  let F := V.powersetCard t
  let inside := fun (S : Finset ℕ) => S.powersetCard 2
  let free := fun S => (E \ inside S).powerset
  let bad := fun S => free S ∪ (free S).image (fun G => G ∪ inside S)
  by_cases small : d < t
  · refine ⟨fun _ _ => false, ?_⟩
    intro S sub card
    have := Finset.card_le_card sub
    simp [card] at this
    omega
  have cap (S) (hS : S ∈ F) : (bad S).card ≤ 2 * 2^(E.card-t.choose 2) := by
    obtain ⟨sub,card⟩ := Finset.mem_powersetCard.mp hS
    have hsub : inside S ⊆ E := Finset.powersetCard_mono sub
    have freecard : (free S).card = 2^(E.card-t.choose 2) := by
      simp only [free, Finset.card_powerset, Finset.card_sdiff_of_subset hsub, inside,
        Finset.card_powersetCard,card]
    have h := Finset.card_union_le (free S) ((free S).image (fun G => G ∪ inside S))
    have hi : ((free S).image (fun G => G ∪ inside S)).card ≤ (free S).card := Finset.card_image_le
    dsimp only [bad]
    omega
  have allbad := Finset.card_biUnion_le_card_mul F bad _ cap
  have ht : t.choose 2 ≤ E.card := by
    simpa [E,V] using (Nat.choose_le_choose 2 (Nat.le_of_not_gt small))
  have count : (F.biUnion bad).card < E.powerset.card := by
    apply lt_of_le_of_lt allbad
    rw [Finset.card_powerset]
    have h := Nat.mul_lt_mul_of_pos_right size (show 0 < 2^(E.card-t.choose 2) by positivity)
    rw [← pow_add, Nat.add_sub_of_le ht] at h
    simpa [F,V,mul_left_comm,mul_comm,mul_assoc] using h
  obtain ⟨G,hG,hgood⟩ := Finset.exists_mem_notMem_of_card_lt_card count
  refine ⟨fun x y => decide ({x,y} ∈ G), ?_⟩
  intro S sub card b mono
  have hs : S ∈ F := Finset.mem_powersetCard.mpr ⟨sub,card⟩
  have vals (e : Finset ℕ) (he : e ∈ inside S) : decide (e ∈ G) = b := by
    obtain ⟨es,ec⟩ := Finset.mem_powersetCard.mp he
    obtain ⟨x,y,ne,eq⟩ := Finset.card_eq_two.mp ec
    subst e
    have hx := es (Finset.mem_insert_self x {y})
    have hy := es (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    rcases lt_or_gt_of_ne ne with h | h
    · exact mono _ hx _ hy h
    · simpa [Finset.pair_comm] using mono _ hy _ hx h
  apply hgood
  apply Finset.mem_biUnion.mpr
  refine ⟨S,hs,?_⟩
  cases b with
  | false =>
    apply Finset.mem_union_left
    apply Finset.mem_powerset.mpr
    intro e he
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hG) he,
      fun hi => (of_decide_eq_false (vals _ hi)) he⟩
  | true =>
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    have inc : inside S ⊆ G := fun e he => of_decide_eq_true (vals e he)
    exact ⟨G \ inside S, Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff_left (inside S)
      (Finset.mem_powerset.mp hG)), Finset.sdiff_union_of_subset inc⟩


def level : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | d+1, x, y => if x/2 = y/2 then 0 else level d (x/2) (y/2) + 1

lemma level_lt {d x y : ℕ} (h : x < y) (hy : y < 2^d) : level d x y < d := by
  induction d generalizing x y with
  | zero => simp at hy; omega
  | succ d ih =>
    rw [pow_succ] at hy
    simp only [level]
    split
    · omega
    · have := ih (x := x/2) (y := y/2) (by omega) (by omega)
      omega

lemma level_triple {d x y z : ℕ} (xy : x < y) (yz : y < z) (hz : z < 2^d) :
    level d x y ≠ level d y z ∧ level d x z = max (level d x y) (level d y z) := by
  induction d generalizing x y z with
  | zero => simp at hz; omega
  | succ d ih =>
    rw [pow_succ] at hz
    by_cases a : x/2 = y/2
    · have b : y/2 ≠ z/2 := by omega
      simp [level,a,b]
    · by_cases b : y/2 = z/2
      · have c : x/2 ≠ z/2 := by omega
        simp [level,b,c]
      · have c : x/2 ≠ z/2 := by omega
        obtain ⟨hne, hm⟩ := ih (x := x/2) (y := y/2) (z := z/2) (by omega) (by omega) (by omega)
        simp only [level, if_neg a, if_neg b, if_neg c]
        omega

def pattern (d : ℕ) (c : ℕ → ℕ → Bool) (x y z : ℕ) : Bool × Bool :=
  let u := level d x y
  let v := level d y z
  (decide (u < v), c (min u v) (max u v))

lemma left_anchor {d x y z : ℕ} {c : ℕ → ℕ → Bool} {b : Bool}
    (xy : x < y) (yz : y < z) (hz : z < 2^d) (mono : pattern d c x y z = (true,b)) :
    level d x y < level d x z ∧ c (level d x y) (level d x z) = b := by
  have h := congrArg Prod.fst mono
  have col := congrArg Prod.snd mono
  change decide (_ < _) = true at h
  have hlt := of_decide_eq_true h
  have hm := (level_triple xy yz hz).2
  rw [max_eq_right hlt.le] at hm
  simpa [pattern,hm,min_eq_left hlt.le,max_eq_right hlt.le,hlt] using And.intro hlt col

lemma right_anchor {d x y z : ℕ} {c : ℕ → ℕ → Bool} {b : Bool}
    (xy : x < y) (yz : y < z) (hz : z < 2^d) (mono : pattern d c x y z = (false,b)) :
    level d y z < level d x z ∧ c (level d y z) (level d x z) = b := by
  have h := congrArg Prod.fst mono
  have col := congrArg Prod.snd mono
  change decide (_ < _) = false at h
  have hn := of_decide_eq_false h
  obtain ⟨hne,hm⟩ := level_triple xy yz hz
  have hlt : level d y z < level d x y := by omega
  rw [max_eq_left hlt.le] at hm
  simpa [pattern,hm,min_eq_right hlt.le,max_eq_left hlt.le] using And.intro hlt col


lemma project (A : Finset ℕ) (f : ℕ → ℕ) (d : ℕ) (c : ℕ → ℕ → Bool) (b : Bool)
    (bound : ∀ x ∈ A, f x < d)
    (pair : ∀ x ∈ A, ∀ y ∈ A, x < y →
      f x ≠ f y ∧ c (min (f x) (f y)) (max (f x) (f y)) = b) :
    ∃ T : Finset ℕ, T ⊆ Finset.range d ∧ T.card = A.card ∧
      ∀ u ∈ T, ∀ v ∈ T, u < v → c u v = b := by
  have anypair (x) (hx : x ∈ A) (y) (hy : y ∈ A) (hne : x ≠ y) :
      f x ≠ f y ∧ c (min (f x) (f y)) (max (f x) (f y)) = b := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact pair x hx y hy h
    · obtain ⟨hn,hc⟩ := pair y hy x hx h
      exact ⟨hn.symm, by simpa [min_comm,max_comm] using hc⟩
  refine ⟨A.image f, ?_, Finset.card_image_of_injOn ?_, ?_⟩
  · intro u hu
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_range.mpr (bound x hx)
  · intro x hx y hy h
    exact Classical.byContradiction (fun hn => (anypair x hx y hy hn).1 h)
  · intro u hu v hv huv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    have hn : x ≠ y := fun h => huv.ne (congrArg f h)
    simpa [min_eq_left huv.le,max_eq_right huv.le] using (anypair x hx y hy hn).2

theorem stepping (d : ℕ) (c : ℕ → ℕ → Bool) (S : Finset ℕ)
    (nz : S.Nonempty) (bound : ∀ x ∈ S, x < 2^d) (b : Bool × Bool)
    (hom : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → pattern d c x y z = b) :
    ∃ T : Finset ℕ, T ⊆ Finset.range d ∧ T.card = S.card-1 ∧
      ∀ u ∈ T, ∀ v ∈ T, u < v → c u v = b.2 := by
  rcases b with ⟨flag,b⟩
  cases flag with
  | true =>
    let a := S.min' nz
    have ha : a ∈ S := S.min'_mem nz
    have hlt (x) (hx : x ∈ S.erase a) : a < x :=
      lt_of_le_of_ne (S.min'_le x (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1.symm
    obtain ⟨T,ht,card,col⟩ := project (S.erase a) (level d a) d c b
      (fun x hx => level_lt (hlt x hx) (bound _ (Finset.mem_erase.mp hx).2)) (by
        intro x hx y hy hxy
        have h := left_anchor (hlt x hx) hxy (bound _ (Finset.mem_erase.mp hy).2)
          (hom _ ha _ (Finset.mem_erase.mp hx).2 _ (Finset.mem_erase.mp hy).2 (hlt x hx) hxy)
        exact ⟨h.1.ne, by simpa [min_eq_left h.1.le,max_eq_right h.1.le] using h.2⟩)
    exact ⟨T,ht,card.trans (Finset.card_erase_of_mem ha),col⟩
  | false =>
    let a := S.max' nz
    have ha : a ∈ S := S.max'_mem nz
    have hlt (x) (hx : x ∈ S.erase a) : x < a :=
      lt_of_le_of_ne (S.le_max' x (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1
    obtain ⟨T,ht,card,col⟩ := project (S.erase a) (fun x => level d x a) d c b
      (fun x hx => level_lt (hlt x hx) (bound _ ha)) (by
        intro x hx y hy hxy
        have h := right_anchor hxy (hlt y hy) (bound _ ha)
          (hom _ (Finset.mem_erase.mp hx).2 _ (Finset.mem_erase.mp hy).2 _ ha hxy (hlt y hy))
        exact ⟨h.1.ne.symm, by simpa [min_eq_right h.1.le,max_eq_left h.1.le] using h.2⟩)
    exact ⟨T,ht,card.trans (Finset.card_erase_of_mem ha),col⟩
private def ordered (e : Finset ℕ) (p : ℕ × ℕ × ℕ) : Prop :=
  p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ e = {p.1,p.2.1,p.2.2}

private noncomputable def readTriple (e : Finset ℕ) : ℕ × ℕ × ℕ := by
  classical
  exact if h : ∃ p, ordered e p then h.choose else (0,0,0)

private lemma read_exact {x y z : ℕ} (xy : x < y) (yz : y < z) :
    readTriple {x,y,z} = (x,y,z) := by
  classical
  have h : ∃ p, ordered {x,y,z} p := ⟨(x,y,z),xy,yz,rfl⟩
  rw [readTriple,dif_pos h]
  have hs := h.choose_spec
  generalize h.choose = q at *
  obtain ⟨a,b,c⟩ := q
  obtain ⟨ab,bc,eq⟩ := hs
  change a < b at ab
  change b < c at bc
  change ({x,y,z} : Finset ℕ) = {a,b,c} at eq
  have mem (u : ℕ) := Finset.ext_iff.mp eq u
  simp only [Finset.mem_insert,Finset.mem_singleton] at mem
  have ha := (mem a).2 (by simp)
  have hb := (mem b).2 (by simp)
  have hc := (mem c).2 (by simp)
  congr <;> omega

private noncomputable def encode : Bool × Bool ≃ Fin 4 :=
  Fintype.equivFinOfCardEq (by decide)

private lemma finite_bound (k d m : ℕ) (hk : 0 < k)
    (size : 2 * d.choose (k-1) < 2^(k-1).choose 2)
    (ram : ∀ f : Finset (Fin m) → Fin 4, ∃ A : Finset (Fin m), A.card = k ∧
      ∃ b : Fin 4, ∀ e : Finset (Fin m), e ⊆ A → e.card = 3 → f e = b) : 2^d < m := by
  classical
  by_contra! hm
  obtain ⟨c,seed⟩ := graph_seed d (k-1) size
  let paint (e : Finset (Fin m)) := let p := readTriple (e.image Fin.val)
                                    encode (pattern d c p.1 p.2.1 p.2.2)
  obtain ⟨A,hA,b,hb⟩ := ram paint
  let S := A.image Fin.val
  have hS : S.card = k := (Finset.card_image_of_injective _ Fin.val_injective).trans hA
  have bound (x) (hx : x ∈ S) : x < 2^d := by
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    exact lt_of_lt_of_le a.isLt hm
  have hom (x) (hx : x ∈ S) (y) (hy : y ∈ S) (z) (hz : z ∈ S) (xy : x<y) (yz : y<z) :
      pattern d c x y z = encode.symm b := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    have uv : u ≠ v := fun e => xy.ne (congrArg Fin.val e)
    have vw : v ≠ w := fun e => yz.ne (congrArg Fin.val e)
    have uw : u ≠ w := fun e => (xy.trans yz).ne (congrArg Fin.val e)
    have sub : ({u,v,w} : Finset (Fin m)) ⊆ A := by
      intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl <;> assumption
    have col := hb {u,v,w} sub (by simp [uv,vw,uw])
    apply encode.injective
    simpa [paint,read_exact xy yz] using col
  obtain ⟨T,sub,card,mono⟩ := stepping d c S (Finset.card_pos.mp (hS ▸ hk)) bound _ hom
  exact seed T sub (by simpa [hS] using card) _ mono

private lemma seed_size {k : ℕ} (hk : 16 ≤ k) :
    2 * (2^(k/8)).choose (k-1) < 2^(k-1).choose 2 := by
  let t := k-1
  have ht : 4 ≤ t := by dsimp [t]; omega
  have hq : 2*(k/8)+2 ≤ t-1 := by dsimp [t]; omega
  have hp := Nat.mul_le_mul_left t hq
  have he : 1+(k/8)*t < t.choose 2 := by
    rw [Nat.choose_two_right]
    have : 2*(1+(k/8)*t+1) ≤ t*(t-1) := by nlinarith
    omega
  calc
    2 * (2^(k/8)).choose t ≤ 2 * (2^(k/8))^t := Nat.mul_le_mul_left _ (Nat.choose_le_pow _ _)
    _ = 2^(1+(k/8)*t) := by rw [pow_add,pow_mul,pow_one]
    _ < 2^t.choose 2 := Nat.pow_lt_pow_right (by decide) he

end FourColour

theorem OMA.solution : OMA.R_Erdos564_erdos_564_R2.H1 := by
  refine ⟨1/16,by norm_num,?_⟩
  filter_upwards [Filter.eventually_ge_atTop (16 : ℕ)] with k hk
  intro m ram
  have hd := FourColour.finite_bound k (2^(k/8)) m (by omega) (FourColour.seed_size hk) ram
  have hn : k ≤ 16*(k/8) := by omega
  have hr : (k : ℝ) ≤ 16*((k/8 : ℕ) : ℝ) := by exact_mod_cast hn
  have h := Real.rpow_le_rpow_of_exponent_le (x := (2:ℝ)) (by norm_num)
    (show (1/16 : ℝ)*k ≤ ((k/8 : ℕ):ℝ) by linarith)
  have hh := Real.rpow_le_rpow_of_exponent_le (x := (2:ℝ)) (by norm_num) h
  apply hh.trans
  have he : (2 : ℝ) ^ ((k/8 : ℕ) : ℝ) = ((2^(k/8) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    norm_cast
  rw [he,Real.rpow_natCast]
  exact_mod_cast hd.le
