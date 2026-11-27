import OMAReductions.R_Erdos20_erdos_20_R1_H2_R2

/-! Leave any unused positions constant and read each of the packed blocks at
its own coordinates. A sunflower in the packed words is a sunflower in every block. -/

private def blockPosition {n t N : ℕ} (h : t * n ≤ N) (b : Fin t) (j : Fin n) : Fin N :=
  Fin.castLE h (finProdFinEquiv (b, j))

private def packWords {n m t N : ℕ} (hN : 0 < N) (hm : m ≤ N)
    (words : Fin t → Fin n → Fin m) (x : Fin N) : Fin N :=
  if hx : x.val < t * n then
    let ij := finProdFinEquiv.symm (⟨x.val, hx⟩ : Fin (t * n))
    Fin.castLE hm (words ij.1 ij.2)
  else ⟨0, hN⟩

private theorem packWords_block {n m t N : ℕ} (hN : 0 < N) (hm : m ≤ N)
    (ht : t * n ≤ N) (words : Fin t → Fin n → Fin m) (b : Fin t) (j : Fin n) :
    packWords hN hm words (blockPosition ht b j) = Fin.castLE hm (words b j) := by
  unfold packWords blockPosition
  rw [Fin.val_castLE, dif_pos (finProdFinEquiv (b, j)).isLt]
  exact congrArg (fun ij => Fin.castLE hm (words ij.1 ij.2))
    (finProdFinEquiv.symm_apply_apply (b, j))

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1_H2_R2.H2 := by
  classical
  intro r n m t N hN hm ht W hW
  let encode : (Fin t → ↥W) ↪ (Fin N → Fin N) :=
    ⟨fun words => packWords hN hm (fun b => (words b).val), by
      intro u v huv
      funext b
      apply Subtype.ext
      funext j
      have heq := congrFun huv (blockPosition ht b j)
      change packWords hN hm (fun i => (u i).val) (blockPosition ht b j) =
        packWords hN hm (fun i => (v i).val) (blockPosition ht b j) at heq
      rw [packWords_block, packWords_block] at heq
      exact Fin.castLE_injective hm heq⟩
  refine ⟨Finset.univ.map encode, ?_, ?_⟩
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  · intro v hv hsun
    have pre (i : Fin r) : ∃ u : Fin t → ↥W, encode u = v i := by
      obtain ⟨u, _, hu⟩ := Finset.mem_map.mp (hv i)
      exact ⟨u, hu⟩
    choose u hu using pre
    have hread (i : Fin r) (b : Fin t) (j : Fin n) :
        v i (blockPosition ht b j) = Fin.castLE hm ((u i b).val j) := by
      rw [← hu i]
      exact packWords_block hN hm ht (fun k => (u i k).val) b j
    have hblock (b : Fin t) : ∀ a c : Fin r, (u a b).val = (u c b).val := by
      apply hW (fun i => (u i b).val) (fun i => (u i b).property)
      intro j
      rcases hsun (blockPosition ht b j) with equal | distinct
      · left
        intro a c
        apply Fin.castLE_injective hm
        rw [← hread, ← hread]
        exact equal a c
      · right
        intro a c heq
        exact distinct ((hread a b j).trans
          ((congrArg (Fin.castLE hm) heq).trans (hread c b j).symm))
    intro a c
    have heq : u a = u c := funext fun b => Subtype.ext (hblock b a c)
    rw [← hu a, ← hu c, heq]
