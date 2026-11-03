import Blotto.GeneralPaperLowerQuantileMean

/-! The weighted original-deviation law as an exact uniform occurrence
law, followed by an explicit sorting permutation. Occurrence expansion and
sorting are erased comparison proof analysis, never algorithmic work. -/
namespace Blotto.GeneralPaperWeightedDeviationLaw
open GeneralPaperCircleFiniteAverage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

noncomputable def occurrenceEquiv {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W) :
    Fin W ≃ (Σ j:Fin g,Fin (weights j)) :=
  (finCongr (show W=Fintype.card (Σ j:Fin g,Fin (weights j)) by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using hs.symm)).trans
      (Fintype.equivFin (Σ j:Fin g,Fin (weights j))).symm

noncomputable def expanded {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W)
    (z : Fin g → ℝ) : Fin W → ℝ := fun i => z ((occurrenceEquiv W weights hs i).1)

noncomputable def sorted {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W)
    (z : Fin g → ℝ) : Fin W → ℝ := GeneralPaperCircleSortedComparison.sorted (expanded W weights hs z)

theorem expanded_sum {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W)
    (z : Fin g → ℝ) (f : ℝ → ℝ) :
    (∑ i,f (expanded W weights hs z i))=∑ j,(weights j:ℝ)*f (z j) := by
  calc
    _ = ∑ o:(Σ j:Fin g,Fin (weights j)),f (z o.1) :=
      Equiv.sum_comp (occurrenceEquiv W weights hs) (fun o => f (z o.1))
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem sorted_sum {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W)
    (z : Fin g → ℝ) (f : ℝ → ℝ) :
    (∑ i,f (sorted W weights hs z i))=∑ j,(weights j:ℝ)*f (z j) := by
  have h := Equiv.sum_comp (Tuple.sort (expanded W weights hs z)) (fun i => f (expanded W weights hs z i))
  exact h.trans (expanded_sum W weights hs z f)

theorem sorted_average {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W)
    (z : Fin g → ℝ) (f : ℝ → ℝ) :
    average (fun i => f (sorted W weights hs z i))=∑ j,((weights j:ℝ)/W)*f (z j) := by
  unfold average
  rw [sorted_sum W weights hs z f,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sorted_monotone {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W)
    (z : Fin g → ℝ) : Monotone (sorted W weights hs z) :=
  GeneralPaperCircleSortedComparison.sorted_monotone _

theorem sorted_nonnegative {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W)
    (z : Fin g → ℝ) (hz : ∀ j,0≤z j) (i : Fin W) : 0≤sorted W weights hs z i := hz _

noncomputable def deviation {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (y : Fin g → ℝ) : Fin g → ℝ :=
  fun j => y j/((weights j:ℝ)/W)

theorem deviation_nonnegative {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (y : Fin g → ℝ)
    (hy : ∀ j,0≤y j) (j : Fin g) : 0≤deviation W weights y j :=
  div_nonneg (hy j) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem deviation_mean {g : ℕ} (W : ℕ) (hW : 0<W) (weights : Fin g → ℕ) (hp : ∀ j,0<weights j)
    (hs : ∑ j,weights j=W) (y : Fin g → ℝ) :
    average (sorted W weights hs (deviation W weights y))=∑ j,y j := by
  calc
    _ = ∑ j,((weights j:ℝ)/W)*deviation W weights y j :=
      sorted_average W weights hs (deviation W weights y) (fun z:ℝ => z)
    _ = ∑ j,y j := by
      apply Finset.sum_congr rfl
      intro j _
      have hP : (0:ℝ)<(weights j:ℝ)/W := div_pos (by exact_mod_cast hp j) (by exact_mod_cast hW)
      exact mul_div_cancel₀ _ hP.ne'

end Blotto.GeneralPaperWeightedDeviationLaw
