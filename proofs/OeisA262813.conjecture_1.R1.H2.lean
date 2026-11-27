import OMAReductions.R_OeisA262813_conjecture_1_R1
import Mathlib

/-! Step OeisA262813.conjecture_1.R1.H2. Credit: @ivillar (original proof). Explicit witnesses for n < 90. -/

namespace OMA262813H2

theorem main_H2 : OMA.R_OeisA262813_conjecture_1_R1.H2 := by
  intro n hn h90
  interval_cases n
  · exact ⟨0, 3, 0, by norm_num, by norm_num⟩
  · exact ⟨0, 3, 2, by norm_num, by norm_num⟩
  · exact ⟨0, 5, 0, by norm_num, by norm_num⟩
  · exact ⟨0, 5, 2, by norm_num, by norm_num⟩
  · exact ⟨0, 3, 4, by norm_num, by norm_num⟩
  · exact ⟨0, 7, 0, by norm_num, by norm_num⟩
  · exact ⟨0, 5, 4, by norm_num, by norm_num⟩
  · exact ⟨1, 5, 4, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 0, by norm_num, by norm_num⟩
  · exact ⟨0, 3, 6, by norm_num, by norm_num⟩
  · exact ⟨0, 9, 2, by norm_num, by norm_num⟩
  · exact ⟨0, 5, 6, by norm_num, by norm_num⟩
  · exact ⟨1, 5, 6, by norm_num, by norm_num⟩
  · exact ⟨0, 9, 4, by norm_num, by norm_num⟩
  · exact ⟨0, 7, 6, by norm_num, by norm_num⟩
  · exact ⟨0, 11, 2, by norm_num, by norm_num⟩
  · exact ⟨0, 3, 8, by norm_num, by norm_num⟩
  · exact ⟨1, 3, 8, by norm_num, by norm_num⟩
  · exact ⟨0, 5, 8, by norm_num, by norm_num⟩
  · exact ⟨1, 5, 8, by norm_num, by norm_num⟩
  · exact ⟨0, 13, 0, by norm_num, by norm_num⟩
  · exact ⟨0, 7, 8, by norm_num, by norm_num⟩
  · exact ⟨1, 7, 8, by norm_num, by norm_num⟩
  · exact ⟨0, 11, 6, by norm_num, by norm_num⟩
  · exact ⟨0, 13, 4, by norm_num, by norm_num⟩
  · exact ⟨0, 3, 10, by norm_num, by norm_num⟩
  · exact ⟨1, 3, 10, by norm_num, by norm_num⟩
  · exact ⟨0, 5, 10, by norm_num, by norm_num⟩
  · exact ⟨0, 15, 2, by norm_num, by norm_num⟩
  · exact ⟨0, 13, 6, by norm_num, by norm_num⟩
  · exact ⟨0, 7, 10, by norm_num, by norm_num⟩
  · exact ⟨0, 15, 4, by norm_num, by norm_num⟩
  · exact ⟨1, 15, 4, by norm_num, by norm_num⟩
  · exact ⟨2, 3, 10, by norm_num, by norm_num⟩
  · exact ⟨0, 9, 10, by norm_num, by norm_num⟩
  · exact ⟨0, 17, 0, by norm_num, by norm_num⟩
  · exact ⟨0, 3, 12, by norm_num, by norm_num⟩
  · exact ⟨1, 3, 12, by norm_num, by norm_num⟩
  · exact ⟨0, 5, 12, by norm_num, by norm_num⟩
  · exact ⟨0, 11, 10, by norm_num, by norm_num⟩
  · exact ⟨1, 11, 10, by norm_num, by norm_num⟩
  · exact ⟨0, 7, 12, by norm_num, by norm_num⟩
  · exact ⟨1, 7, 12, by norm_num, by norm_num⟩
  · exact ⟨0, 15, 8, by norm_num, by norm_num⟩
  · exact ⟨0, 17, 6, by norm_num, by norm_num⟩
  · exact ⟨0, 9, 12, by norm_num, by norm_num⟩
  · exact ⟨1, 9, 12, by norm_num, by norm_num⟩
  · exact ⟨2, 11, 10, by norm_num, by norm_num⟩
  · exact ⟨0, 19, 4, by norm_num, by norm_num⟩
  · exact ⟨0, 3, 14, by norm_num, by norm_num⟩
  · exact ⟨0, 11, 12, by norm_num, by norm_num⟩
  · exact ⟨0, 5, 14, by norm_num, by norm_num⟩
  · exact ⟨0, 15, 10, by norm_num, by norm_num⟩
  · exact ⟨0, 19, 6, by norm_num, by norm_num⟩
  · exact ⟨0, 7, 14, by norm_num, by norm_num⟩
  · exact ⟨0, 21, 2, by norm_num, by norm_num⟩
  · exact ⟨0, 13, 12, by norm_num, by norm_num⟩
  · exact ⟨1, 13, 12, by norm_num, by norm_num⟩
  · exact ⟨0, 9, 14, by norm_num, by norm_num⟩
  · exact ⟨1, 9, 14, by norm_num, by norm_num⟩
  · exact ⟨0, 17, 10, by norm_num, by norm_num⟩
  · exact ⟨1, 17, 10, by norm_num, by norm_num⟩
  · exact ⟨2, 7, 14, by norm_num, by norm_num⟩
  · exact ⟨0, 11, 14, by norm_num, by norm_num⟩
  · exact ⟨0, 3, 16, by norm_num, by norm_num⟩
  · exact ⟨0, 23, 0, by norm_num, by norm_num⟩
  · exact ⟨0, 5, 16, by norm_num, by norm_num⟩
  · exact ⟨1, 5, 16, by norm_num, by norm_num⟩
  · exact ⟨2, 17, 10, by norm_num, by norm_num⟩
  · exact ⟨0, 7, 16, by norm_num, by norm_num⟩
  · exact ⟨0, 21, 8, by norm_num, by norm_num⟩
  · exact ⟨0, 17, 12, by norm_num, by norm_num⟩
  · exact ⟨1, 17, 12, by norm_num, by norm_num⟩
  · exact ⟨0, 9, 16, by norm_num, by norm_num⟩
  · exact ⟨0, 23, 6, by norm_num, by norm_num⟩
  · exact ⟨1, 23, 6, by norm_num, by norm_num⟩
  · exact ⟨0, 15, 14, by norm_num, by norm_num⟩
  · exact ⟨0, 25, 0, by norm_num, by norm_num⟩
  · exact ⟨0, 11, 16, by norm_num, by norm_num⟩
  · exact ⟨0, 21, 10, by norm_num, by norm_num⟩
  · exact ⟨0, 19, 12, by norm_num, by norm_num⟩
  · exact ⟨0, 3, 18, by norm_num, by norm_num⟩
  · exact ⟨1, 3, 18, by norm_num, by norm_num⟩
  · exact ⟨0, 5, 18, by norm_num, by norm_num⟩
  · exact ⟨0, 13, 16, by norm_num, by norm_num⟩
  · exact ⟨1, 13, 16, by norm_num, by norm_num⟩
  · exact ⟨0, 7, 18, by norm_num, by norm_num⟩
  · exact ⟨1, 7, 18, by norm_num, by norm_num⟩
  · exact ⟨2, 19, 12, by norm_num, by norm_num⟩

end OMA262813H2

theorem OMA.solution : OMA.R_OeisA262813_conjecture_1_R1.H2 := OMA262813H2.main_H2
