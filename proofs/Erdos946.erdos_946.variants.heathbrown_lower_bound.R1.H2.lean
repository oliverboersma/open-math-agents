import OMAReductions.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1
import Mathlib

/-! A numerical instance of Heath-Brown's Key Lemma. The eight small-prime
valuations at each point are a permutation of 0,...,7 under bitwise xor.
We translate the offsets by a common CRT solution so the remaining part
of each pairwise difference is a common, coprime divisor. No factorization
of the 1583-digit points is needed. Construction after Heath-Brown,
Mathematika 31 (1984), 141–149, and E. Pechenick, Equality of Number-Theoretic
Functions over Consecutive Integers, sections 3.3–3.4. -/
-- Credit: @marcusbuffett
namespace OMA.HeathBrownSeven
open scoped ArithmeticFunction.sigma

private def num : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p,e)::l => p^e * num l

private def cnt : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (_,e)::l => (e+1)*cnt l

private def valid : List (ℕ × ℕ) → Bool
  | [] => true
  | (p,e)::l => decide p.Prime && decide ((p^e).Coprime (num l)) && valid l

private theorem count_factors (l : List (ℕ × ℕ)) (h : valid l=true) : σ 0 (num l)=cnt l := by
  induction l with
  | nil => simp [num,cnt]
  | cons entry l ih =>
    obtain ⟨p,e⟩ := entry
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at h
    rw [num,cnt,ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h.1.2,
      ArithmeticFunction.sigma_zero_apply_prime_pow h.1.1,ih h.2]

private def perm : Fin 7 → ℕ := ![4,1,0,5,2,3,6]
private def primes : Fin 8 → ℕ := ![2,3,5,7,11,13,17,19]
private def factors (i : Fin 7) (j : Option (Fin 7)) : List (ℕ × ℕ) :=
  List.ofFn fun h : Fin 8 =>
    let e := (perm i) ^^^ h.val
    (primes h, match j with | none => e | some k => e - ((perm k) ^^^ h.val))

private def part (i : Fin 7) := num (factors i none)
private def cofactor (i j : Fin 7) := num (factors i (some j))

private theorem divisor_balance (i j : Fin 7) :
    σ 0 (part i) * σ 0 (cofactor j i) = σ 0 (part j)*σ 0 (cofactor i j) := by
  have hv : ∀ (a : Fin 7) (b : Option (Fin 7)),valid (factors a b)=true := by decide +kernel
  simp only [part,cofactor,count_factors _ (hv _ _)]
  exact (show ∀ (a b : Fin 7),cnt (factors a none)*cnt (factors b (some a)) =
    cnt (factors b none)*cnt (factors a (some b)) from by decide +kernel) i j

private def shift : ℕ := 54293842776972455825610115246506857935407049442876485652587138012176197082363848973554568012581081827954864143527210512938933489767457530604277755014021315536257675889875856367945106079919662563014127674578992178723872970335872100925430927720457406693350569276823257365284362443006630129704144511962118462291104914955408003372875141121624418101503642821350647842907928268690580084906604888035965316138404279493095257134509918541137864534943561550794369402096222596150394455160059058953217298544590998125598185796832629109892005212820910117967862854146987213746066420750477479722837593144154610950156864012238889525018273310353119783150036757029237425659673275861230853898376237600628019292815889704196124192996825798597824822703431526904911463602730558907099515579759300099298464185970555616211086404359182601995655034323955503390770129057984204606463996493798516859652130992412530124133397604877068692508104247154554534836892118736190835613779723932902958353710909260476791982089838630920793942842306993389940269452424494848267739230228638998023588104815340649268742217725857500174050311423085334934277896809642035288295759874805353895560140979280224676483666067700033338650803153437485439508855751958403906358326017110943693026615909669169156690847093985881233901893229702887820215130978488844439471972456419940958404602072356450737039948662546043495035836446172006098625119764119954835234345226701601815995162586333907319972491572661369128910614668197591575144019038772864091185985577459818348260091912791873705117927670700227266886703500766346159498021235927261818219153500000000
private def offsets : Fin 7 → ℕ := ![1289242341647646750000,1087769754549337068139257076750,3017252254998615707186270832675,78354300210436852307898467208663359629652331708067500000,78354300210436852307898467226043170707260260150637903788,156708600420873704615796934423592430221811711620882837880,391771501052184261539492336043316795831721061998053080000]
private def pt (i : Fin 7) := shift+offsets i

private def cert (a b u v u' v' : ℕ) : Bool :=
  let d := b-a
  let f := d / (u.gcd v)
  let x := a / (u*f)
  let y := b / (v*f)
  decide (d = a.gcd b ∧ (u*f)*x=a ∧ (v*f)*y=b ∧ u'*x=a/d ∧ v'*y=b/d ∧
    u.Coprime f ∧ v.Coprime f ∧ (u*f).Coprime x ∧ (v*f).Coprime y ∧
    u'.Coprime x ∧ v'.Coprime y)

private theorem cert_sound {a b u v u' v' : ℕ} (h : cert a b u v u' v' = true)
    (balance : σ 0 u * σ 0 v' = σ 0 v * σ 0 u') :
    b-a = a.gcd b ∧ σ 0 a * σ 0 (b/(b-a)) = σ 0 b * σ 0 (a/(b-a)) := by
  let f := (b-a)/(u.gcd v)
  let x := a/(u*f)
  let y := b/(v*f)
  change decide ((b-a)=a.gcd b ∧ (u*f)*x=a ∧ (v*f)*y=b ∧
    u'*x=a/(b-a) ∧ v'*y=b/(b-a) ∧ u.Coprime f ∧ v.Coprime f ∧
    (u*f).Coprime x ∧ (v*f).Coprime y ∧ u'.Coprime x ∧ v'.Coprime y) = true at h
  obtain ⟨g,ax,by',qx,qy,uf,vf,ux,vy,ux',vy'⟩ := of_decide_eq_true h
  refine ⟨g,?_⟩
  rw [←qy,←qx,←ax,←by']
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ux,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime vy,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime uf,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime vf,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ux',
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime vy']
  calc
    _ = (σ 0 u * σ 0 v') * (σ 0 f * σ 0 x * σ 0 y) := by ring
    _ = _ := by rw [balance]; ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem seven : OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1.H2 := by
  have checked : ∀ i j : Fin 7,i<j → cert (pt i) (pt j) (part i) (part j) (cofactor i j) (cofactor j i)=true := by
    decide +kernel
  refine ⟨pt,?_,?_,fun i j h => cert_sound (checked i j h) (divisor_balance i j)⟩
  · exact fun i j h => Nat.add_lt_add_left
      ((show ∀ a b : Fin 7,a<b → offsets a < offsets b from by decide +kernel) i j h) _
  · intro i
    exact Nat.add_pos_left (show 0<shift from by decide +kernel) _

end OMA.HeathBrownSeven

theorem OMA.solution : OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1.H2 := OMA.HeathBrownSeven.seven
