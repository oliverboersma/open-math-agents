import OMAReductions.R_Green100_green_100_variants_operator_norm_R1_H3_R1

theorem OMA.solution : OMA.R_Green100_green_100_variants_operator_norm_R1_H3_R1.H3 := by
  intro A _ finite p q u pp pq qp uq
  let a := (u:A)*p
  let b := p*(↑u⁻¹:A)
  have ab : a*b = q := by
    dsimp [a,b]
    rw [uq,mul_assoc,← mul_assoc p p,pp]
    simp [mul_assoc]
  have ba : b*a = p := by simp [a,b,mul_assoc,pp]
  have ap : a*p=a := by simp [a,mul_assoc,pp]
  have pb : p*b=b := by simp [b,← mul_assoc,pp]
  have aq : a*q=a := by simp [a,mul_assoc,pq]
  have qb : q*b=b := by simp [b,← mul_assoc,qp]
  have qa : q*a=a := by rw [← ab,mul_assoc,ba,ap]
  have bq : b*q=b := by rw [← ab,← mul_assoc,ba,pb]
  have qq : q*q=q := by calc
    q*q = (a*b)*q := by rw [ab]
    _ = a*b := by rw [mul_assoc,bq]
    _ = q := ab
  have proj : (1-q)*(1-q) = 1-q := by simp [sub_mul,mul_sub,qq]
  have xy : (a+(1-q))*(b+(1-q))=1 := by
    rw [add_mul,mul_add,mul_add,ab,proj,mul_sub,sub_mul,aq,qb]
    simp
  have yx := finite _ _ xy
  rw [add_mul,mul_add,mul_add,ba,proj,mul_sub,sub_mul,bq,qa] at yx
  simp only [mul_one,one_mul,sub_self,add_zero,zero_add] at yx
  calc
    p = (p+(1-q))-(1-q) := by abel
    _ = 1-(1-q) := by rw [yx]
    _ = q := by abel
