import OMAReductions.R_Green100_green_100_parts_i_R1_H1_R1

/-! Adapted from OpenAI, openai/math, OddKaplansky at
adc7f1241b42e322a6451854ab7e4b4c146bf78a, used under Apache-2.0.
The finite Heisenberg group supplies matrix units in its group algebra.
Padding by an identity block lets one transfer a square matrix defect of
arbitrary size without extending the coefficient field. -/

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5

section
noncomputable section
open scoped Classical BigOperators
namespace OddKaplansky.CharacterIdempotents
variable {K : Type portUniverse1} {A : Type portUniverse2} {G : Type portUniverse3} [Field K] [Group A] [Fintype A] [Group G]

def projector (χ : A →* Kˣ) : MonoidAlgebra K A :=
  (Fintype.card A : K)⁻¹ • ∑ a : A, MonoidAlgebra.single a ((χ a : K)⁻¹)

lemma sum_character_eq_zero (χ : A →* Kˣ) (hχ : χ ≠ 1) :
    ∑ a : A, (χ a : K) = 0 := by
  have hn : ∃ b : A, (χ b : K) ≠ 1 := by
    by_contra! h
    apply hχ
    ext b
    exact h b
  obtain ⟨b, hb⟩ := hn
  have hh : (χ b : K) * ∑ a : A, (χ a : K) = ∑ a : A, (χ a : K) := by
    rw [Finset.mul_sum]
    simp only [← Units.val_mul, ← map_mul]
    exact Equiv.sum_comp (Equiv.mulLeft b) (fun a => (χ a : K))
  by_contra hs
  exact hb ((mul_eq_right₀ hs).mp hh)

lemma projector_mul_single (χ : A →* Kˣ) (b : A) :
    projector χ * MonoidAlgebra.single b 1 = (χ b : K) • projector χ := by
  unfold projector
  rw [smul_mul_assoc, Finset.sum_mul, smul_smul]
  rw [mul_comm (χ b : K), ← smul_smul]
  congr 1
  rw [Finset.smul_sum]
  calc
    (∑ a : A, MonoidAlgebra.single a ((χ a : K)⁻¹) * MonoidAlgebra.single b 1) =
        ∑ a : A, (χ b : K) • MonoidAlgebra.single (a * b) ((χ (a * b) : K)⁻¹) := by
      apply Finset.sum_congr rfl
      intro a _
      simp [MonoidAlgebra.single_mul_single, mul_comm]
    _ = _ := Equiv.sum_comp (Equiv.mulRight b)
      (fun a : A => (χ b : K) • MonoidAlgebra.single a ((χ a : K)⁻¹))

lemma projector_mul (χ ψ : A →* Kˣ) :
    projector χ * projector ψ =
      ((Fintype.card A : K)⁻¹ * ∑ b : A, ((χ b : K) * (ψ b : K)⁻¹)) •
        projector χ := by
  conv_lhs => rhs; unfold projector
  rw [mul_smul_comm, Finset.mul_sum]
  have hh (b : A) : projector χ * MonoidAlgebra.single b ((ψ b : K)⁻¹) =
      ((χ b : K) * (ψ b : K)⁻¹) • projector χ := by
    rw [show MonoidAlgebra.single b ((ψ b : K)⁻¹) =
      (ψ b : K)⁻¹ • MonoidAlgebra.single b 1 by simp]
    rw [mul_smul_comm, projector_mul_single, smul_smul, mul_comm]
  simp_rw [hh]
  rw [← Finset.sum_smul, smul_smul]

lemma projector_idempotent (χ : A →* Kˣ) (hcard : (Fintype.card A : K) ≠ 0) :
    IsIdempotentElem (projector χ) := by
  change projector χ * projector χ = projector χ
  rw [projector_mul]
  simp [hcard]

lemma projector_orthogonal (χ ψ : A →* Kˣ) (hne : χ ≠ ψ) :
    projector χ * projector ψ = 0 := by
  rw [projector_mul]
  have hn : χ * ψ⁻¹ ≠ 1 := by
    intro h
    apply hne
    apply MonoidHom.ext
    intro a
    have hh := congrArg (fun f : A →* Kˣ => f a) h
    exact mul_inv_eq_one.mp hh
  have h := sum_character_eq_zero (χ * ψ⁻¹) hn
  simpa using congrArg (fun c : K => ((Fintype.card A : K)⁻¹ * c) • projector χ) h

lemma projector_one_coeff (χ : A →* Kˣ) :
    (projector χ).coeff 1 = (Fintype.card A : K)⁻¹ := by
  simp [projector, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, Finsupp.single_apply]

lemma projector_ne_zero (χ : A →* Kˣ) (hcard : (Fintype.card A : K) ≠ 0) :
    projector χ ≠ 0 := by
  intro h
  have := congrArg (fun p : MonoidAlgebra K A => p.coeff 1) h
  rw [projector_one_coeff] at this
  exact (inv_ne_zero hcard) this

def pushed (f : A →* G) (χ : A →* Kˣ) : MonoidAlgebra K G :=
  MonoidAlgebra.mapDomainAlgHom K K f (projector χ)

lemma pushed_eq_sum (f : A →* G) (χ : A →* Kˣ) :
    pushed f χ = (Fintype.card A : K)⁻¹ •
      ∑ a : A, MonoidAlgebra.single (f a) ((χ a : K)⁻¹) := by
  simp [pushed, projector, map_sum]

lemma pushed_idempotent (f : A →* G) (χ : A →* Kˣ)
    (hc : (Fintype.card A : K) ≠ 0) :
    pushed f χ * pushed f χ = pushed f χ := by
  unfold pushed
  rw [← map_mul, projector_idempotent χ hc]

lemma pushed_orthogonal (f : A →* G) (χ ψ : A →* Kˣ) (hne : χ ≠ ψ) :
    pushed f χ * pushed f ψ = 0 := by
  unfold pushed
  rw [← map_mul, projector_orthogonal χ ψ hne, map_zero]

lemma pushed_ne_zero (f : A →* G) (hf : Function.Injective f) (χ : A →* Kˣ)
    (hc : (Fintype.card A : K) ≠ 0) : pushed f χ ≠ 0 := by
  intro h
  exact projector_ne_zero χ hc ((MonoidAlgebra.mapDomain_injective hf) (h.trans (MonoidAlgebra.mapDomain_zero f).symm))

lemma pushed_mul_single (f : A →* G) (χ : A →* Kˣ) (b : A) :
    pushed f χ * MonoidAlgebra.single (f b) 1 = (χ b : K) • pushed f χ := by
  have h := congrArg (MonoidAlgebra.mapDomainAlgHom K K f) (projector_mul_single χ b)
  rw [map_mul, map_smul] at h
  simpa only [pushed, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single] using h

lemma pushed_central (f : A →* G) (χ : A →* Kˣ)
    (hf : ∀ a g, Commute (f a) g) (x : MonoidAlgebra K G) :
    Commute (pushed f χ) x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    change pushed f χ * MonoidAlgebra.single g 1 = _
    rw [pushed_eq_sum, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one, one_mul,
      (hf a g).eq]
  | add x y hx hy => exact hx.add_right hy
  | smul r x hx => exact hx.smul_right r

lemma lift_pushed (f : A →* G) (χ : A →* Kˣ) (ρ : G →* K)
    (hρ : ∀ a, ρ (f a) = (χ a : K)) (hc : (Fintype.card A : K) ≠ 0) :
    MonoidAlgebra.lift K K G ρ (pushed f χ) = 1 := by
  rw [pushed_eq_sum]
  simp [map_sum, MonoidAlgebra.lift_single, hρ, hc]

end OddKaplansky.CharacterIdempotents

namespace OddKaplansky.Fourier
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse4} {E : Type portUniverse5} [Field K] [Fintype E] (M : ℕ) [NeZero M]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)

abbrev C := Multiplicative (ZMod M)
abbrev A := E → C M

def cyclicCharacter : C M →* Kˣ :=
  (AddChar.zmodChar M hζ.pow_eq_one).toMonoidHom.toHomUnits
lemma cyclicCharacter_injective : Function.Injective (cyclicCharacter M hζ) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply ZMod.val_injective M
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  exact congrArg (fun u : Kˣ => (u : K)) hab

def character (lmb : A (E := E) M) : A (E := E) M →* Kˣ :=
  (cyclicCharacter M hζ).comp (show A (E := E) M →* C M from
    { toFun := fun a => Multiplicative.ofAdd (∑ e, (lmb e).toAdd * (a e).toAdd)
      map_one' := by simp
      map_mul' := by intro a b; simp [mul_add, Finset.sum_add_distrib] })

lemma character_apply (lmb a : A (E := E) M) :
    character M hζ lmb a = cyclicCharacter M hζ (Multiplicative.ofAdd
      (∑ e, (lmb e).toAdd * (a e).toAdd)) := rfl

lemma character_symm (lmb a : A (E := E) M) : character M hζ lmb a = character M hζ a lmb := by
  simp only [character_apply, mul_comm]

lemma character_mul (lmb μ : A (E := E) M) :
    character M hζ (lmb * μ) = character M hζ lmb * character M hζ μ := by
  apply MonoidHom.ext
  intro a
  simp only [MonoidHom.mul_apply, character_apply, Pi.mul_apply, toAdd_mul,
    add_mul, Finset.sum_add_distrib, ofAdd_add, map_mul]

lemma character_mulSingle (lmb : A (E := E) M) (i : E) :
    character M hζ lmb (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod M))) =
      cyclicCharacter M hζ (lmb i) := by
  rw [character_apply]
  have hs : (∑ e, (lmb e).toAdd *
      ((Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod M)) : A (E := E) M) e).toAdd) = (lmb i).toAdd := by
    simp [Pi.mulSingle_apply, apply_ite]
  rw [hs, ofAdd_toAdd]

lemma character_injective : Function.Injective (character (E := E) M hζ) := by
  intro lmb μ he
  funext i
  apply cyclicCharacter_injective M hζ
  have h := congrArg (fun χ : A (E := E) M →* Kˣ =>
    χ (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod M)))) he
  simpa only [character_mulSingle] using h

@[simp] lemma character_one : character (E := E) M hζ 1 = 1 := by
  ext a
  simp [character_apply]

lemma character_ne_one (a : A (E := E) M) (ha : a ≠ 1) : character M hζ a ≠ 1 := by
  intro hh
  exact ha (character_injective M hζ (hh.trans (character_one M hζ).symm))

lemma sum_inverse_characters (a : A (E := E) M) (ha : a ≠ 1) :
    ∑ lmb : A (E := E) M, ((character M hζ lmb a : K)⁻¹) = 0 := by
  have hχ : (character M hζ a)⁻¹ ≠ 1 := by
    intro h
    apply character_ne_one M hζ a ha
    apply MonoidHom.ext
    intro b
    have hh := congrArg (fun χ : A (E := E) M →* Kˣ => (χ b)⁻¹) h
    simpa using hh
  simpa only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, character_symm] using
    CharacterIdempotents.sum_character_eq_zero ((character M hζ a)⁻¹) hχ

lemma sum_projector (hc : (Fintype.card (A (E := E) M) : K) ≠ 0) :
    ∑ lmb : A (E := E) M, CharacterIdempotents.projector (character M hζ lmb) = 1 := by
  have hp (lmb a : A (E := E) M) :
      (CharacterIdempotents.projector (character M hζ lmb)).coeff a =
        (Fintype.card (A (E := E) M) : K)⁻¹ * ((character M hζ lmb a : K)⁻¹) := by
    simp [CharacterIdempotents.projector, MonoidAlgebra.coeff_sum,
      MonoidAlgebra.coeff_smul, Finsupp.single_apply]
  ext a
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp_rw [hp]
  rw [← Finset.mul_sum]
  by_cases ha : a = 1
  · subst a
    simp only [map_one, Units.val_one, inv_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, MonoidAlgebra.coeff_one_one]
    exact inv_mul_cancel₀ hc
  · rw [sum_inverse_characters M hζ a ha]
    simp [MonoidAlgebra.one_def, ha]

end
end OddKaplansky.Fourier

end
end

end OAI


namespace OAI

section
namespace OddKaplansky.Heisenberg
noncomputable section
open scoped Classical BigOperators
variable (M q : ℕ)
abbrev Z := Fin q → Fourier.C M
def dot (y x : Z M q) : Fourier.C M := Multiplicative.ofAdd (∑ j, (y j).toAdd * (x j).toAdd)
lemma dot_one_left (x : Z M q) : dot M q 1 x=1 := by simp [dot]
lemma dot_one_right (y : Z M q) : dot M q y 1=1 := by simp [dot]
lemma dot_mul_left (y t x : Z M q) : dot M q (y*t) x = dot M q y x * dot M q t x := by
  apply Multiplicative.toAdd.injective
  simp [dot,add_mul,Finset.sum_add_distrib]
lemma dot_mul_right (y x s : Z M q) : dot M q y (x*s) = dot M q y x * dot M q y s := by
  apply Multiplicative.toAdd.injective
  simp [dot,mul_add,Finset.sum_add_distrib]
lemma dot_inv_left (y x : Z M q) : dot M q y⁻¹ x = (dot M q y x)⁻¹ := by
  apply Multiplicative.toAdd.injective
  simp [dot,Finset.sum_neg_distrib]
lemma dot_inv_right (y x : Z M q) : dot M q y x⁻¹ = (dot M q y x)⁻¹ := by
  apply Multiplicative.toAdd.injective
  simp [dot,Finset.sum_neg_distrib]
lemma dot_symm (y x : Z M q) : dot M q y x=dot M q x y := by simp [dot,mul_comm]
structure GroupData where
  x : Z M q
  y : Z M q
  k : Fourier.C M
lemma GroupData.ext {a b : GroupData M q} (hx : a.x=b.x) (hy : a.y=b.y) (hk : a.k=b.k) : a=b := by
  cases a; cases b; simp_all
instance : One (GroupData M q) := ⟨⟨1,1,1⟩⟩
instance : Mul (GroupData M q) := ⟨fun a b => ⟨a.x*b.x,a.y*b.y,a.k*b.k*dot M q a.y b.x⟩⟩
instance : Inv (GroupData M q) := ⟨fun a => ⟨a.x⁻¹,a.y⁻¹,a.k⁻¹*dot M q a.y a.x⟩⟩
@[simp] lemma one_x : (1 : GroupData M q).x=1 := rfl
@[simp] lemma one_y : (1 : GroupData M q).y=1 := rfl
@[simp] lemma one_k : (1 : GroupData M q).k=1 := rfl
@[simp] lemma mul_x (a b : GroupData M q) : (a*b).x=a.x*b.x := rfl
@[simp] lemma mul_y (a b : GroupData M q) : (a*b).y=a.y*b.y := rfl
@[simp] lemma mul_k (a b : GroupData M q) : (a*b).k=a.k*b.k*dot M q a.y b.x := rfl
@[simp] lemma inv_x (a : GroupData M q) : a⁻¹.x=a.x⁻¹ := rfl
@[simp] lemma inv_y (a : GroupData M q) : a⁻¹.y=a.y⁻¹ := rfl
@[simp] lemma inv_k (a : GroupData M q) : a⁻¹.k=a.k⁻¹*dot M q a.y a.x := rfl
instance : Group (GroupData M q) where
  mul_assoc a b c := by apply GroupData.ext <;> simp only [mul_x,mul_y,mul_k,dot_mul_left,dot_mul_right,mul_assoc]; ac_rfl
  one_mul a := by apply GroupData.ext <;> simp [dot_one_left]
  mul_one a := by apply GroupData.ext <;> simp [dot_one_right]
  inv_mul_cancel a := by apply GroupData.ext <;> simp [dot_inv_left,mul_comm]
def coordinates : GroupData M q ≃ Z M q × Z M q × Fourier.C M where
  toFun a := (a.x,a.y,a.k)
  invFun a := ⟨a.1,a.2.1,a.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance [NeZero M] : Fintype (GroupData M q) := Fintype.ofEquiv _ (coordinates M q).symm
lemma card [NeZero M] : Fintype.card (GroupData M q)=M*(M^q)^2 := by
  rw [Fintype.card_congr (coordinates M q)]
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_multiplicative,ZMod.card]
  ring
def central : Fourier.C M →* GroupData M q where
  toFun k := ⟨1,1,k⟩
  map_one' := rfl
  map_mul' a b := by apply GroupData.ext <;> simp [dot_one_left]
def X : Z M q →* GroupData M q where
  toFun x := ⟨x,1,1⟩
  map_one' := rfl
  map_mul' a b := by apply GroupData.ext <;> simp [dot_one_left]
def Y : Z M q →* GroupData M q where
  toFun y := ⟨1,y,1⟩
  map_one' := rfl
  map_mul' a b := by apply GroupData.ext <;> simp [dot_one_right]
lemma central_injective : Function.Injective (central M q) := fun _ _ he => congrArg GroupData.k he
lemma central_commute (c : Fourier.C M) (g : GroupData M q) : Commute (central M q c) g := by
  change central M q c*g=g*central M q c
  apply GroupData.ext <;> simp [central,dot_one_left,dot_one_right,mul_comm]
lemma YX (y x : Z M q) : Y M q y * X M q x = central M q (dot M q y x) * (X M q x * Y M q y) := by
  apply GroupData.ext <;> simp [central,X,Y,dot_one_left,dot_one_right]
lemma normal (g : GroupData M q) : g=central M q g.k * (X M q g.x * Y M q g.y) := by
  apply GroupData.ext <;> simp [central,X,Y,dot_one_left,dot_one_right]
end
end OddKaplansky.Heisenberg

end

end OAI


namespace OAI

universe portUniverse1

section
namespace OddKaplansky.Heisenberg
noncomputable section
open scoped Classical BigOperators Matrix
variable (M q : ℕ) [NeZero M] {K : Type portUniverse1} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
lemma character_dot (s y : Z M q) : Fourier.character M hζ s y = Fourier.cyclicCharacter M hζ (dot M q y s) := by
  rw [dot_symm]; rfl

def ρGroup : GroupData M q →* Matrix (Z M q) (Z M q) K where
  toFun g := Matrix.of fun u s => if u=s*g.x then (Fourier.cyclicCharacter M hζ g.k : K)*(Fourier.character M hζ s g.y : K) else 0
  map_one' := by ext u s; simp [Matrix.of_apply, Matrix.one_apply]
  map_mul' g h := by
    ext u s
    rw [Matrix.mul_apply,Finset.sum_eq_single (s*h.x)]
    · simp only [Matrix.of_apply,mul_x,mul_y,mul_k,map_mul,Units.val_mul]
      by_cases he : u=s*h.x*g.x
      · rw [show s*(g.x*h.x)=s*h.x*g.x by ac_rfl,if_pos he,if_pos he,ite_true]
        rw [Fourier.character_mul,MonoidHom.mul_apply,Units.val_mul]
        simp only [character_dot]
        ring
      · simp only [show s*(g.x*h.x)=s*h.x*g.x by ac_rfl,if_neg he,zero_mul]
    · intro b _ hb
      simp only [Matrix.of_apply,if_neg hb,mul_zero]
    · simp

def ρ : MonoidAlgebra K (GroupData M q) →ₐ[K] Matrix (Z M q) (Z M q) K := MonoidAlgebra.lift K _ _ (ρGroup M q hζ)
lemma ρ_single (g : GroupData M q) (c : K) (u s : Z M q) :
    ρ M q hζ (MonoidAlgebra.single g c) u s =
      if u=s*g.x then c*(Fourier.cyclicCharacter M hζ g.k : K)*(Fourier.character M hζ s g.y : K) else 0 := by
  rw [ρ,MonoidAlgebra.lift_single]
  change c*(if u=s*g.x then _ else 0)=_
  split_ifs <;> simp [mul_assoc]
def f : MonoidAlgebra K (GroupData M q) := CharacterIdempotents.pushed (central M q) (Fourier.cyclicCharacter M hζ)
lemma f_idempotent (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) : f M q hζ*f M q hζ=f M q hζ := CharacterIdempotents.pushed_idempotent _ _ hc
lemma f_ne_zero (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) : f M q hζ ≠ 0 := CharacterIdempotents.pushed_ne_zero _ (central_injective M q) _ hc
lemma f_central (a : MonoidAlgebra K (GroupData M q)) : Commute (f M q hζ) a := CharacterIdempotents.pushed_central _ _ (central_commute M q) a
lemma ρ_f (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) : ρ M q hζ (f M q hζ)=1 := by
  ext u s
  rw [f,CharacterIdempotents.pushed_eq_sum,map_smul,map_sum]
  simp only [Matrix.smul_apply,Matrix.sum_apply,ρ_single,central,MonoidHom.coe_mk,OneHom.coe_mk,mul_one,map_one,Units.val_one,mul_one,Matrix.one_apply]
  by_cases he : u=s
  · subst u
    simp only [ite_true,inv_mul_cancel₀ (Units.ne_zero _),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,smul_eq_mul]
    exact inv_mul_cancel₀ hc
  · simp [he]
def p (v : Z M q) : MonoidAlgebra K (GroupData M q) := CharacterIdempotents.pushed (Y M q) (Fourier.character M hζ v)
def D (v : Z M q) : MonoidAlgebra K (GroupData M q) := f M q hζ * p M q hζ v
lemma ρ_p (hc : (Fintype.card (Z M q) : K) ≠ 0) (v : Z M q) :
    ρ M q hζ (p M q hζ v) = Matrix.single v v 1 := by
  ext u s
  rw [p,CharacterIdempotents.pushed_eq_sum,map_smul,map_sum]
  simp only [Matrix.smul_apply,Matrix.sum_apply,ρ_single,Y,MonoidHom.coe_mk,OneHom.coe_mk,mul_one,map_one,Units.val_one]
  by_cases he : u=s
  · subst u
    simp only [ite_true,smul_eq_mul]
    have hs : ∑ a : Z M q, (Fourier.character M hζ v a : K)⁻¹ * (Fourier.character M hζ s a : K) = if s=v then (Fintype.card (Z M q) : K) else 0 := by
      by_cases hsv : s=v
      · subst s; simp
      · rw [if_neg hsv]
        have hh := CharacterIdempotents.sum_character_eq_zero ((Fourier.character M hζ s)*(Fourier.character M hζ v)⁻¹) (by
          intro h
          apply hsv
          apply Fourier.character_injective M hζ
          apply MonoidHom.ext
          intro a
          exact mul_inv_eq_one.mp (congrArg (fun f : Z M q →* Kˣ => f a) h))
        simpa [mul_comm] using hh
    rw [hs]
    by_cases hsv : s=v
    · subst s
      simpa only [Matrix.single_apply,ite_true,and_self] using inv_mul_cancel₀ hc
    · simp [hsv,Ne.symm hsv,Matrix.single]
  · simp [he,Matrix.single]; aesop
lemma ρ_D (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) (hz : (Fintype.card (Z M q) : K) ≠ 0) (v : Z M q) :
    ρ M q hζ (D M q hζ v)=Matrix.single v v 1 := by rw [D,map_mul,ρ_f M q hζ hc,one_mul,ρ_p M q hζ hz]
def xElt (u : Z M q) : MonoidAlgebra K (GroupData M q) := MonoidAlgebra.single (X M q u) 1
def Ω (u v : Z M q) : MonoidAlgebra K (GroupData M q) := xElt M q (u*v⁻¹) * D M q hζ v
lemma ρ_Ω (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) (hz : (Fintype.card (Z M q) : K) ≠ 0) (u v : Z M q) :
    ρ M q hζ (Ω M q hζ u v)=Matrix.single u v 1 := by
  rw [Ω,map_mul,ρ_D M q hζ hc hz]
  ext a b
  simp only [Matrix.mul_apply,xElt,ρ_single,X,MonoidHom.coe_mk,OneHom.coe_mk,map_one,Units.val_one,mul_one,Matrix.single]
  by_cases hb : b=v
  · subst b
    simp only [Matrix.of_apply,ite_and,mul_ite,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    simp [eq_comm]
  · simp [Ne.symm hb,Matrix.of_apply]
end
end OddKaplansky.Heisenberg

end

end OAI


namespace OAI

universe portUniverse1

section
namespace OddKaplansky.Heisenberg
noncomputable section
open scoped Classical BigOperators Matrix
variable (M q : ℕ) [NeZero M] {K : Type portUniverse1} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) (hz : (Fintype.card (Z M q) : K) ≠ 0)
abbrev Sector := LinearMap.range (Algebra.lmul K (MonoidAlgebra K (GroupData M q)) (f M q hζ))
lemma mem_sector_of_fixed {a : MonoidAlgebra K (GroupData M q)} (ha : f M q hζ*a=a) : a ∈ Sector M q hζ := ⟨a,ha⟩
include hc in
lemma fixed_of_mem_sector {a : MonoidAlgebra K (GroupData M q)} (ha : a ∈ Sector M q hζ) : f M q hζ*a=a := by
  obtain ⟨a,rfl⟩ := ha
  change f M q hζ*(f M q hζ*a)=f M q hζ*a
  rw [← mul_assoc,f_idempotent M q hζ hc]
include hc in
lemma Ω_fixed (u v : Z M q) : f M q hζ*Ω M q hζ u v=Ω M q hζ u v := by
  unfold Ω D
  rw [← mul_assoc,(f_central M q hζ _).eq,mul_assoc,← mul_assoc (f M q hζ),f_idempotent M q hζ hc]
def frame (xy : Z M q × Z M q) : MonoidAlgebra K (GroupData M q) := f M q hζ * MonoidAlgebra.single ⟨xy.1,xy.2,1⟩ 1
lemma f_single (g : GroupData M q) : f M q hζ*MonoidAlgebra.single g 1 = (Fourier.cyclicCharacter M hζ g.k : K) • frame M q hζ (g.x,g.y) := by
  have hg : central M q g.k * (⟨g.x,g.y,1⟩ : GroupData M q)=g := by apply GroupData.ext <;> simp [central,dot_one_left]
  have hs : MonoidAlgebra.single g (1 : K)=MonoidAlgebra.single (central M q g.k) 1*MonoidAlgebra.single (⟨g.x,g.y,1⟩ : GroupData M q) 1 := by rw [MonoidAlgebra.single_mul_single,one_mul,hg]
  rw [hs,← mul_assoc]
  have hh := CharacterIdempotents.pushed_mul_single (central M q) (Fourier.cyclicCharacter M hζ) g.k
  change f M q hζ*MonoidAlgebra.single (central M q g.k) 1=(Fourier.cyclicCharacter M hζ g.k : K) • f M q hζ at hh
  rw [hh,smul_mul_assoc]
  rfl
lemma span_frame : Submodule.span K (Set.range (frame M q hζ))=Sector M q hζ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨xy,rfl⟩
    exact ⟨_,rfl⟩
  · rintro _ ⟨a,rfl⟩
    change f M q hζ*a ∈ _
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [MonoidAlgebra.of_apply,f_single]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(g.x,g.y),rfl⟩)
    | add a b ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
lemma sector_dim_le : Module.finrank K (Sector M q hζ) ≤ Fintype.card (Z M q)*Fintype.card (Z M q) := by
  rw [← span_frame]
  simpa only [Set.finrank,Fintype.card_prod] using finrank_range_le_card (R := K) (frame M q hζ)

def encode : Matrix (Z M q) (Z M q) K →ₗ[K] MonoidAlgebra K (GroupData M q) where
  toFun T := ∑ u,∑ v,T u v • Ω M q hζ u v
  map_add' T S := by simp only [Matrix.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c T := by simp only [Matrix.smul_apply,smul_smul,smul_eq_mul,Finset.smul_sum,RingHom.id_apply]
lemma encode_apply (T : Matrix (Z M q) (Z M q) K) : encode M q hζ T=∑ u,∑ v,T u v • Ω M q hζ u v := rfl
include hc in
lemma encode_fixed (T : Matrix (Z M q) (Z M q) K) : f M q hζ*encode M q hζ T = encode M q hζ T := by
  simp only [encode_apply,Finset.mul_sum,mul_smul_comm,Ω_fixed M q hζ hc]
include hc hz in
lemma ρ_encode (T : Matrix (Z M q) (Z M q) K) : ρ M q hζ (encode M q hζ T)=T := by
  simp only [encode_apply,map_sum,map_smul,ρ_Ω M q hζ hc hz]
  ext u v
  simp [Matrix.sum_apply,Matrix.single_apply,ite_and]
include hc hz in
lemma encode_injective : Function.Injective (encode M q hζ) := by
  intro T S he
  have hh := congrArg (ρ M q hζ) he
  simpa only [ρ_encode M q hζ hc hz] using hh
include hc hz in
lemma encode_range : LinearMap.range (encode M q hζ)=Sector M q hζ := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro _ ⟨T,rfl⟩
    exact mem_sector_of_fixed _ _ _ (encode_fixed M q hζ hc T)
  · rw [LinearMap.finrank_range_of_inj (encode_injective M q hζ hc hz)]
    simpa only [Module.finrank_matrix,Module.finrank_self,mul_one] using sector_dim_le M q hζ
include hc hz in
lemma ρ_injective_on_sector {a b : MonoidAlgebra K (GroupData M q)}
    (ha : a ∈ Sector M q hζ) (hb : b ∈ Sector M q hζ) (he : ρ M q hζ a=ρ M q hζ b) : a=b := by
  rw [← encode_range M q hζ hc hz] at ha hb
  obtain ⟨T,rfl⟩ := ha
  obtain ⟨S,rfl⟩ := hb
  rw [ρ_encode M q hζ hc hz,ρ_encode M q hζ hc hz] at he
  rw [he]
include hc hz in
lemma Ω_mul (u v s t : Z M q) : Ω M q hζ u v*Ω M q hζ s t=if v=s then Ω M q hζ u t else 0 := by
  apply ρ_injective_on_sector M q hζ hc hz
  · apply mem_sector_of_fixed
    rw [← mul_assoc,Ω_fixed M q hζ hc]
  · split_ifs
    · exact mem_sector_of_fixed _ _ _ (Ω_fixed M q hζ hc _ _)
    · exact Submodule.zero_mem _
  · rw [map_mul,ρ_Ω M q hζ hc hz,ρ_Ω M q hζ hc hz]
    split_ifs with hv <;> simp only [ρ_Ω M q hζ hc hz,map_zero]
    all_goals
      ext a b
      simp [Matrix.mul_apply,Matrix.single_apply,ite_and,mul_ite,hv] <;> split_ifs <;> rfl
include hc hz in
lemma Ω_sum : ∑ u : Z M q, Ω M q hζ u u=f M q hζ := by
  apply ρ_injective_on_sector M q hζ hc hz
  · apply mem_sector_of_fixed
    simp only [Finset.mul_sum,Ω_fixed M q hζ hc]
  · exact ⟨1,by simp⟩
  · rw [map_sum,ρ_f M q hζ hc]
    simp only [ρ_Ω M q hζ hc hz]
    ext a b
    simp [Matrix.sum_apply,Matrix.single_apply,Matrix.one_apply,ite_and,eq_comm]
include hc hz in
lemma Ω_ne_zero (u v : Z M q) : Ω M q hζ u v≠0 := by
  intro he
  have hh := congrArg (fun a => ρ M q hζ a u v) he
  rw [ρ_Ω M q hζ hc hz,map_zero] at hh
  simp at hh
include hc hz in
lemma encode_mul (T S : Matrix (Z M q) (Z M q) K) : encode M q hζ (T*S)=encode M q hζ T*encode M q hζ S := by
  apply ρ_injective_on_sector M q hζ hc hz
  · exact mem_sector_of_fixed _ _ _ (encode_fixed M q hζ hc _)
  · apply mem_sector_of_fixed
    rw [← mul_assoc,encode_fixed M q hζ hc]
  · have hh : ρ M q hζ (encode M q hζ T*encode M q hζ S)=ρ M q hζ (encode M q hζ T)*ρ M q hζ (encode M q hζ S) := map_mul (ρ M q hζ) _ _
    rw [hh,ρ_encode M q hζ hc hz,ρ_encode M q hζ hc hz,ρ_encode M q hζ hc hz]
end
end OddKaplansky.Heisenberg

end

end OAI


namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7 portUniverse8 portUniverse9

section

noncomputable section
open scoped Classical BigOperators
namespace OddKaplansky.MatrixBlock
variable {S : Type portUniverse1} {R : Type portUniverse2} {m : Type portUniverse3} [Ring S] [Ring R] [Fintype m]
variable (f : S →+* R) (q : m → m → R)

def block (X : Matrix m m S) : R := ∑ i, ∑ j, f (X i j) * q i j

lemma block_zero : block f q 0 = 0 := by simp [block]
lemma block_add (X Y : Matrix m m S) : block f q (X + Y) = block f q X + block f q Y := by
  simp [block, add_mul, Finset.sum_add_distrib]
lemma block_sub (X Y : Matrix m m S) : block f q (X - Y) = block f q X - block f q Y := by
  simp [block, sub_mul, Finset.sum_sub_distrib]
lemma block_one : block f q 1 = ∑ i, q i i := by
  simp [block, Matrix.one_apply, apply_ite]

variable (hqq : ∀ i j k r, q i j * q k r = if j = k then q i r else 0)
variable (hcomm : ∀ x i j, Commute (f x) (q i j))
include hqq hcomm

lemma block_mul (X Y : Matrix m m S) : block f q (X * Y) = block f q X * block f q Y := by
  have hterm (i j k r : m) :
      (f (X i j) * q i j) * (f (Y k r) * q k r) =
        if j = k then f (X i j * Y k r) * q i r else 0 := by
    calc
      _ = f (X i j * Y k r) * (q i j * q k r) := by
        rw [map_mul, ← mul_assoc, mul_assoc (f (X i j)),
          (hcomm (Y k r) i j).eq.symm]
        simp only [mul_assoc]
      _ = _ := by rw [hqq]; split_ifs <;> simp
  have hmulij (i j : m) : (f (X i j) * q i j) * block f q Y =
      ∑ r, f (X i j * Y j r) * q i r := by
    simp only [block, Finset.mul_sum, hterm]
    rw [Finset.sum_comm]
    simp
  symm
  calc
    block f q X * block f q Y = ∑ i, ∑ j, (f (X i j) * q i j) * block f q Y := by
      change (∑ i, ∑ j, f (X i j) * q i j) * block f q Y = _
      simp only [Finset.sum_mul]
    _ = ∑ i, ∑ j, ∑ r, f (X i j * Y j r) * q i r := by simp_rw [hmulij]
    _ = block f q (X * Y) := by
      simp only [block, Matrix.mul_apply, map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

lemma block_sandwich (X : Matrix m m S) (i j : m) :
    q i i * block f q X * q j j = f (X i j) * q i j := by
  have hterm (k r : m) : q i i * (f (X k r) * q k r) * q j j =
      if i = k then if r = j then f (X k r) * q i j else 0 else 0 := by
    calc
      _ = f (X k r) * (q i i * q k r * q j j) := by
        rw [← mul_assoc, (hcomm (X k r) i i).eq.symm]
        simp only [mul_assoc]
      _ = _ := by
        by_cases hik : i = k <;> by_cases hrj : r = j <;>
          simp [hqq, hik, hrj]

  simp only [block, Finset.mul_sum, Finset.sum_mul, hterm]
  simp

lemma block_injective (hpure : ∀ x i j, f x * q i j = 0 → x = 0) :
    Function.Injective (block f q) := by
  intro X Y h
  have hz : block f q (X - Y) = 0 := by rw [block_sub, h, sub_self]
  have hXY : X - Y = 0 := by
    ext i j
    apply hpure _ i j
    rw [← block_sandwich f q hqq hcomm, hz, mul_zero, zero_mul]
  exact sub_eq_zero.mp hXY

theorem scalar_witnesses
    (hpure : ∀ x i j, f x * q i j = 0 → x = 0)
    (a b : Matrix m m S) (hab : a * b = 1) (hba : b * a ≠ 1) :
    ∃ a' b' : R, a' * b' = 1 ∧ b' * a' ≠ 1 := by
  let e := block f q 1
  let a' := 1 - e + block f q a
  let b' := 1 - e + block f q b
  have he : e * e = e := by rw [← block_mul f q hqq hcomm, mul_one]
  have hea : e * block f q a = block f q a := by rw [← block_mul f q hqq hcomm, one_mul]
  have hae : block f q a * e = block f q a := by rw [← block_mul f q hqq hcomm, mul_one]
  have heb : e * block f q b = block f q b := by rw [← block_mul f q hqq hcomm, one_mul]
  have hbe : block f q b * e = block f q b := by rw [← block_mul f q hqq hcomm, mul_one]
  have hab' : block f q a * block f q b = e := by rw [← block_mul f q hqq hcomm, hab]
  refine ⟨a',b',?_,?_⟩
  · dsimp [a',b']
    noncomm_ring [he, hea, hae, heb, hbe, hab']
  · intro h
    have h' : block f q b * block f q a = e := by
      apply add_left_cancel (a := 1 - e)
      calc
        1 - e + block f q b * block f q a =
            (1 - e + block f q b) * (1 - e + block f q a) := by
          noncomm_ring [he, hea, hae, heb, hbe]
        _ = 1 := h
        _ = 1 - e + e := by abel
    apply hba
    apply block_injective f q hqq hcomm hpure
    rw [block_mul f q hqq hcomm]
    exact h'

end OddKaplansky.MatrixBlock
namespace OddKaplansky.ProductAlgebras
variable {K : Type portUniverse4} {G : Type portUniverse5} {H : Type portUniverse6} [Field K] [Group G] [Group H]

def leftMap : MonoidAlgebra K G →ₐ[K] MonoidAlgebra K (G × H) :=
  MonoidAlgebra.mapDomainAlgHom K K (MonoidHom.inl G H)
def rightMap : MonoidAlgebra K H →ₐ[K] MonoidAlgebra K (G × H) :=
  MonoidAlgebra.mapDomainAlgHom K K (MonoidHom.inr G H)

lemma left_right_commute (x : MonoidAlgebra K G) (y : MonoidAlgebra K H) :
    Commute (leftMap x) (rightMap y) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    induction y using MonoidAlgebra.induction_on with
    | of h =>
      change _ * _ = _ * _
      simp [leftMap, rightMap, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single]
    | add y z hy hz => simpa only [map_add] using hy.add_right hz
    | smul c y hy => simpa only [map_smul] using hy.smul_right c
  | add x z hx hz => simpa only [map_add] using hx.add_left hz
  | smul c x hx => simpa only [map_smul] using hx.smul_left c

lemma product_coeff (x : MonoidAlgebra K G) (y : MonoidAlgebra K H) (g : G) (h : H) :
    (leftMap x * rightMap y).coeff (g,h) = x.coeff g * y.coeff h := by
  induction x using MonoidAlgebra.induction_on with
  | of a =>
    induction y using MonoidAlgebra.induction_on with
    | of b =>
      by_cases hag : a = g <;> by_cases hbh : b = h <;>
        simp [leftMap, rightMap, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
          hag, hbh, Prod.ext_iff]
    | add y z hy hz =>
      simp only [map_add, mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hy, hz]
    | smul c y hy =>
      simp only [map_smul, mul_smul_comm, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
        smul_eq_mul, hy]
      ring
  | add x z hx hz =>
    simp only [map_add, add_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hz]
  | smul c x hx =>
    simp only [map_smul, smul_mul_assoc, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      smul_eq_mul, hx]
    ring

lemma product_ne_zero {x : MonoidAlgebra K G} {y : MonoidAlgebra K H}
    (hx : x ≠ 0) (hy : y ≠ 0) : leftMap x * rightMap y ≠ 0 := by
  obtain ⟨g,hg⟩ : ∃ g, x.coeff g ≠ 0 := by
    by_contra! h
    apply hx
    ext g
    exact h g
  obtain ⟨h,hh⟩ : ∃ h, y.coeff h ≠ 0 := by
    by_contra! h
    apply hy
    ext a
    exact h a
  intro he
  have he' := congrArg (fun z : MonoidAlgebra K (G × H) => z.coeff (g,h)) he
  rw [product_coeff] at he'
  exact mul_ne_zero hg hh he'

end OddKaplansky.ProductAlgebras
namespace OddKaplansky.MatrixBlock
variable {S : Type portUniverse7} {R : Type portUniverse8} {m : Type portUniverse9} [Ring S] [Ring R] [Fintype m]
variable (f : S →+* R) (q : m → m → R)

def output (X : Matrix m m S) : R := 1 - block f q 1 + block f q X

lemma output_formula (X : Matrix m m S) :
    output f q X = 1 - ∑ i, q i i + ∑ i, ∑ j, f (X i j)*q i j := by
  rw [output,block_one,block]

variable (hqq : ∀ i j k r, q i j * q k r = if j = k then q i r else 0)
variable (hcomm : ∀ x i j, Commute (f x) (q i j))

include hqq hcomm in
theorem prescribed_scalar_products
    (hpure : ∀ x i j, f x * q i j = 0 → x = 0)
    (a b : Matrix m m S) (hab : a * b = 1) (hba : b * a ≠ 1) :
    output f q a * output f q b = 1 ∧ output f q b * output f q a ≠ 1 := by
  let e := block f q 1
  let a' := 1 - e + block f q a
  let b' := 1 - e + block f q b
  have he : e * e = e := by rw [← block_mul f q hqq hcomm, mul_one]
  have hea : e * block f q a = block f q a := by rw [← block_mul f q hqq hcomm, one_mul]
  have hae : block f q a * e = block f q a := by rw [← block_mul f q hqq hcomm, mul_one]
  have heb : e * block f q b = block f q b := by rw [← block_mul f q hqq hcomm, one_mul]
  have hbe : block f q b * e = block f q b := by rw [← block_mul f q hqq hcomm, mul_one]
  have hab' : block f q a * block f q b = e := by rw [← block_mul f q hqq hcomm, hab]
  change a' * b' = 1 ∧ b' * a' ≠ 1
  refine ⟨?_,?_⟩
  · dsimp [a',b']
    noncomm_ring [he, hea, hae, heb, hbe, hab']
  · intro h
    have h' : block f q b * block f q a = e := by
      apply add_left_cancel (a := 1 - e)
      calc
        1 - e + block f q b * block f q a =
            (1 - e + block f q b) * (1 - e + block f q a) := by
          noncomm_ring [he, hea, hae, heb, hbe]
        _ = 1 := h
        _ = 1 - e + e := by abel
    apply hba
    apply block_injective f q hqq hcomm hpure
    rw [block_mul f q hqq hcomm]
    exact h'

end OddKaplansky.MatrixBlock
end

end

end OAI


namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7 portUniverse8 portUniverse9 portUniverse10 portUniverse11 portUniverse12

section
namespace OddKaplansky.Heisenberg
noncomputable section
open scoped Classical BigOperators Matrix
variable (M q : ℕ) [NeZero M] {K : Type portUniverse1} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) (hz : (Fintype.card (Z M q) : K) ≠ 0)
def matrixEquiv : Matrix (Z M q) (Z M q) K ≃ₗ[K] Sector M q hζ :=
  (LinearEquiv.ofInjective (encode M q hζ) (encode_injective M q hζ hc hz)).trans
    (LinearEquiv.ofEq _ _ (encode_range M q hζ hc hz))
lemma matrixEquiv_mul (T S : Matrix (Z M q) (Z M q) K) :
    (matrixEquiv M q hζ hc hz (T*S)).val=(matrixEquiv M q hζ hc hz T).val*(matrixEquiv M q hζ hc hz S).val := encode_mul M q hζ hc hz T S

def scalar {L : Type portUniverse2} [Group L] (T : Matrix (Z M q) (Z M q) (MonoidAlgebra K L)) : MonoidAlgebra K (L×GroupData M q) :=
  MatrixBlock.output (ProductAlgebras.leftMap (K := K) (G := L) (H := GroupData M q)).toRingHom
    (fun u v => ProductAlgebras.rightMap (G := L) (Ω M q hζ u v)) T
include hc hz in
lemma scalar_products {L : Type portUniverse3} [Group L] (A B : Matrix (Z M q) (Z M q) (MonoidAlgebra K L))
    (hAB : A*B=1) (hBA : B*A≠1) : scalar M q hζ A*scalar M q hζ B=1 ∧ scalar M q hζ B*scalar M q hζ A≠1 := by
  apply MatrixBlock.prescribed_scalar_products
  · intro u v s t
    rw [← map_mul,Ω_mul M q hζ hc hz]
    split_ifs <;> simp
  · intro x u v
    exact ProductAlgebras.left_right_commute x (Ω M q hζ u v)
  · intro x u v he
    by_contra hx
    exact ProductAlgebras.product_ne_zero hx (Ω_ne_zero M q hζ hc hz u v) he
  · convert hAB using 1 ; congr ; exact Subsingleton.elim _ _
  · convert hBA using 1 ; congr ; exact Subsingleton.elim _ _
include hc hz in
lemma scalar_formula {L : Type portUniverse4} [Group L] (T : Matrix (Z M q) (Z M q) (MonoidAlgebra K L)) :
    scalar M q hζ T=ProductAlgebras.rightMap (G := L) (1-f M q hζ)+
      ∑ u,∑ v,ProductAlgebras.leftMap (T u v)*ProductAlgebras.rightMap (Ω M q hζ u v) := by
  rw [scalar,MatrixBlock.output_formula,← map_sum,Ω_sum M q hζ hc hz,map_sub,map_one]
  rfl
end
end OddKaplansky.Heisenberg

namespace OddKaplansky.Padding
noncomputable section
open scoped Classical BigOperators Matrix
variable {R : Type portUniverse5} {I : Type portUniverse6} {J : Type portUniverse7} [Ring R] [sectionInstance76 : Fintype I] [sectionInstance77 : Fintype J]
def pad (T : Matrix I I R) : Matrix (I⊕J) (I⊕J) R := Matrix.fromBlocks T 0 0 1
lemma pad_mul (A B : Matrix I I R) : pad (J := J) (A*B)=pad A*pad B := by simp [pad,Matrix.fromBlocks_multiply]
lemma pad_one
    {R : Type contextUniverse1}
    {I : Type contextUniverse2}
    {J : Type contextUniverse3}
    [Ring.{contextUniverse1} R]
    [Fintype.{contextUniverse2} I]
    [Fintype.{contextUniverse3} J] : pad (R := R) (I := I) (J := J) 1=1 := Matrix.fromBlocks_one
lemma pad_ne_one
    {R : Type contextUniverse1}
    {I : Type contextUniverse2}
    {J : Type contextUniverse3}
    [Ring.{contextUniverse1} R]
    [Fintype.{contextUniverse2} I]
    [Fintype.{contextUniverse3} J] {T : Matrix I I R} (h : T≠1) : pad (J := J) T≠1 := by
  intro he
  apply h
  funext i j
  have hh := congrFun (congrFun he (Sum.inl i)) (Sum.inl j)
  simpa [pad,Matrix.one_apply] using hh
lemma products (A B : Matrix I I R) (hAB : A*B=1) (hBA : B*A≠1) :
    pad (J := J) A*pad B=1 ∧ pad (J := J) B*pad A≠1 := by
  rw [← pad_mul,← pad_mul,hAB,pad_one]
  exact ⟨rfl,pad_ne_one hBA⟩
end
end OddKaplansky.Padding

namespace OddKaplansky.FixedField
noncomputable section
open scoped Classical BigOperators Matrix
variable (M : ℕ) (hM : 2≤M) (r : ℕ)
include hM in
lemma power_search : ∃ q, r≤M^q := by
  refine ⟨r,?_⟩
  exact (Nat.le_of_lt (Nat.lt_two_pow_self (n := r))).trans (Nat.pow_le_pow_left hM r)
def leastQ : ℕ := Nat.find (power_search M hM r)
lemma leastQ_spec : r≤M^(leastQ M hM r) := Nat.find_spec (power_search M hM r)
lemma leastQ_min {q : ℕ} (hq : r≤M^q) : leastQ M hM r≤q := Nat.find_min' (power_search M hM r) hq
variable [NeZero M] {K : Type portUniverse8} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (M : K)≠0)
def indices : (Fin r⊕Fin (M^(leastQ M hM r)-r)) ≃ Heisenberg.Z M (leastQ M hM r) :=
  finSumFinEquiv.trans ((finCongr (by
    have hh := leastQ_spec M hM r
    simp only [Heisenberg.Z,Fintype.card_fun,Fintype.card_fin,Fourier.C,Fintype.card_multiplicative,ZMod.card]
    omega)).trans (Fintype.equivFin _).symm)
def pad {L : Type portUniverse9} [Group L] (A : Matrix (Fin r) (Fin r) (MonoidAlgebra K L)) :
    Matrix (Heisenberg.Z M (leastQ M hM r)) (Heisenberg.Z M (leastQ M hM r)) (MonoidAlgebra K L) :=
  Matrix.reindexAlgEquiv K (MonoidAlgebra K L) (indices M hM r) (Padding.pad A)
def output {L : Type portUniverse10} [Group L] (A : Matrix (Fin r) (Fin r) (MonoidAlgebra K L)) :
    MonoidAlgebra K (L×Heisenberg.GroupData M (leastQ M hM r)) := Heisenberg.scalar M (leastQ M hM r) hζ (pad M hM r A)
include hc in
lemma output_products {L : Type portUniverse11} [Group L] (A B : Matrix (Fin r) (Fin r) (MonoidAlgebra K L))
    (hAB : A*B=1) (hBA : B*A≠1) : output M hM r hζ A*output M hM r hζ B=1 ∧ output M hM r hζ B*output M hM r hζ A≠1 := by
  have hcc : (Fintype.card (Fourier.C M) : K)≠0 := by simpa [Fourier.C] using hc
  have hzz : (Fintype.card (Heisenberg.Z M (leastQ M hM r)) : K)≠0 := by
    simpa [Heisenberg.Z,Fourier.C] using pow_ne_zero (leastQ M hM r) hc
  have hpad := Padding.products (J := Fin (M^(leastQ M hM r)-r)) A B
    (by convert hAB using 1 ; congr ; exact Subsingleton.elim _ _)
    (by convert hBA using 1 ; congr ; exact Subsingleton.elim _ _)
  let E := Matrix.reindexAlgEquiv K (MonoidAlgebra K L) (indices M hM r)
  have hone : E 1=1 := map_one E
  have hmul : ∀ X Y, E (X*Y)=E X*E Y := fun X Y => map_mul E X Y
  apply Heisenberg.scalar_products M (leastQ M hM r) hζ hcc hzz
  · change E (Padding.pad A)*E (Padding.pad B)=1
    rw [← hmul]
    have hh : E (Padding.pad A*Padding.pad B)=E 1 := by apply congrArg E; convert hpad.1 using 1 ; congr ; exact Subsingleton.elim _ _
    exact hh.trans hone
  · intro he
    apply hpad.2
    have hh : E (Padding.pad B*Padding.pad A)=E 1 := by
      rw [hmul,hone]
      exact he
    convert E.injective hh using 1 ; congr ; exact Subsingleton.elim _ _

lemma finite_field_data (K : Type portUniverse12) [Field K] [Fintype K] (hK : 3≤Fintype.card K) :
    ∃ ζ : K, IsPrimitiveRoot ζ (Fintype.card K-1) ∧ ((Fintype.card K-1 : ℕ) : K)≠0 := by
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  refine ⟨u,?_,?_⟩
  · rw [← Fintype.card_units K,← Nat.card_eq_fintype_card,← hu]
    simpa only [orderOf_units] using IsPrimitiveRoot.orderOf (u : K)
  · have hq : (Fintype.card K : K)=0 := by exact FiniteField.cast_card_eq_zero K
    have hsub : ((Fintype.card K-1 : ℕ) : K)=(Fintype.card K : K)-1 := by simpa only [Nat.cast_one] using (Nat.cast_sub (R := K) (show 1≤Fintype.card K by omega))
    rw [hsub,hq,zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
end
end OddKaplansky.FixedField

end

end OAI

namespace OAI.OddKaplansky
theorem fixed_field_transfer (K L : Type) [Field K] [Fintype K]
    [Group L] (hK : 3 ≤ Fintype.card K) (r : ℕ) (_hr : 0 < r)
    (A B : Matrix (Fin r) (Fin r) (MonoidAlgebra K L))
    (hAB : A * B = 1) (hBA : B * A ≠ 1) :
    ∃ (Λ : Type) (_ : Group Λ) (_ : Fintype Λ),
      ∃ a b : MonoidAlgebra K (L × Λ), a * b = 1 ∧ b * a ≠ 1 := by
  let M := Fintype.card K-1
  have hM : 2≤M := by dsimp [M]; omega
  let : NeZero M := ⟨by omega⟩
  obtain ⟨ζ,hζ,hc⟩ := FixedField.finite_field_data K hK
  refine ⟨Heisenberg.GroupData M (FixedField.leastQ M hM r),inferInstance,inferInstance,
    FixedField.output M hM r hζ A,FixedField.output M hM r hζ B,?_⟩
  exact FixedField.output_products M hM r hζ hc A B hAB hBA
end OAI.OddKaplansky
theorem OMA.solution : OMA.R_Green100_green_100_parts_i_R1_H1_R1.H2 := OAI.OddKaplansky.fixed_field_transfer
