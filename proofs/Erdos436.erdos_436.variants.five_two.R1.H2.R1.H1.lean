import OMAReductions.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1

-- Step Erdos436.erdos_436.variants.five_two.R1.H2.R1.H1: hypothesis H1 of reduction Erdos436.erdos_436.variants.five_two.R1.H2.R1
-- Credit: @ishaanzee
-- Proof: a finite check over 1 <= n < 7888, done by kernel reduction (no native code).

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1.H1 := by
  unfold OMA.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1.H1
  decide +kernel
