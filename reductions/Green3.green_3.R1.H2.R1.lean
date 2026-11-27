import OMAReductions.R_Green3_green_3_R1

/-!
# Packing at the two extreme cell indices

Suppose S has first index m and last index M−1, in a grid of N cells.
On the finer integer grid, the blocks of length N above S are disjoint from
the blocks of length M above S whenever the required product triple is absent.
Both families fit between mM and MN, giving (N+M)|S| ≤ M(N−m).
Only the range N²+3mM < 2MN can therefore support a counterexample of density
above one third. Lean proof by @Deldor14.
-/

namespace OMA.R_Green3_green_3_R1_H2_R1

open Finset

/-- Counting the integer blocks from the largest occupied cell. -/
def H1 : Prop := ∀ (N m M : ℕ) (S : Finset ℕ), 0 < M → M ≤ N →
    M-1 ∈ S → (∀ i ∈ S, m ≤ i ∧ i < M) →
    (∀ i ∈ S, ∀ j ∈ S, ∀ l ∈ S, ¬(i*j < (l+1)*N ∧ l*N < (i+1)*(j+1))) →
    (N+M)*S.card ≤ M*(N-m)

/-- The remaining integer configurations after accounting for both occupied extremes. -/
def H2 : Prop := ∀ (k m M : ℕ) (S : Finset ℕ), 0 < M → M ≤ 2^k →
    m ∈ S → M-1 ∈ S → (∀ i ∈ S, m ≤ i ∧ i < M) →
    (2^k)^2 + 3*m*M < 2*M*(2^k) → 2^k < 3*S.card →
    ∃ i ∈ S, ∃ j ∈ S, ∃ l ∈ S, i*j < (l+1)*2^k ∧ l*2^k < (i+1)*(j+1)

theorem main : H1 → H2 → OMA.R_Green3_green_3_R1.H2 := by
  classical
  intro pack tail k S hr hc
  let N := 2^k
  have hn : 0 < N := by dsimp [N]; positivity
  have hcard : N < 3*S.card := hc
  have hne : S.Nonempty := card_pos.mp (by omega)
  let m := S.min' hne
  let M := S.max' hne+1
  have hm := S.min'_mem hne
  have hM := S.max'_mem hne
  have hpM : 0 < M := Nat.zero_lt_succ _
  have hMN : M ≤ N := Nat.succ_le_of_lt (mem_range.mp (hr hM))
  have hMm : M-1 ∈ S := by simpa [M] using hM
  have hbounds (i : ℕ) (hi : i ∈ S) : m ≤ i ∧ i < M :=
    ⟨S.min'_le i hi,Nat.lt_succ_of_le (S.le_max' i hi)⟩
  by_contra! hno
  have absent : ∀ i ∈ S, ∀ j ∈ S, ∀ l ∈ S, ¬(i*j < (l+1)*N ∧ l*N < (i+1)*(j+1)) := by
    intro i hi j hj l hl h
    exact (not_lt_of_ge (hno i hi j hj l hl h.1)) h.2
  have hbound := pack N m M S hpM hMN hMm hbounds absent
  have hmN : m ≤ N := (hbounds m hm).2.le.trans hMN
  have hsplit : N-m+m = N := Nat.sub_add_cancel hmN
  have hres : N^2 + 3*m*M < 2*M*N := by
    nlinarith only [Nat.mul_lt_mul_of_pos_left hcard (by omega : 0<N+M),
      Nat.mul_le_mul_left 3 hbound, congrArg (fun t : ℕ => 3*M*t) hsplit]
  obtain ⟨i,hi,j,hj,l,hl,hi',hj'⟩ := tail k m M S hpM hMN hm hMm hbounds hres hc
  exact absent i hi j hj l hl ⟨hi',hj'⟩

end OMA.R_Green3_green_3_R1_H2_R1
