import Blotto.OverlapDescriptor

/-! Every active overlap curve and every descriptor output path respects the
hard budget. Inactive entries use the fixed feasible budget row. -/

namespace Blotto
open MeasureTheory Set

theorem overlap_endpoint_membership (a b c d : ℝ)
    (h : overlapLower a b c d < overlapUpper a b c d) :
    (overlapLower a b c d ∈ Icc (min a b) (max a b) ∧
      overlapLower a b c d ∈ Icc (min c d) (max c d)) ∧
    (overlapUpper a b c d ∈ Icc (min a b) (max a b) ∧
      overlapUpper a b c d ∈ Icc (min c d) (max c d)) := by
  have hlA := le_max_left (min a b) (min c d)
  have hlB := le_max_right (min a b) (min c d)
  have huA := min_le_left (max a b) (max c d)
  have huB := min_le_right (max a b) (max c d)
  have hle : overlapLower a b c d ≤ overlapUpper a b c d := le_of_lt h
  exact ⟨⟨⟨hlA, le_trans hle huA⟩, ⟨hlB, le_trans hle huB⟩⟩,
    ⟨⟨le_trans hlA hle, huA⟩, ⟨le_trans hlB hle, huB⟩⟩⟩

namespace OverlapGluing

theorem active_curve_budget {k h : ℕ} (G : OverlapGluing k h) {A B : ℝ}
    (hAP : ∀ i, FullBudget A (G.first.P i)) (hAQ : ∀ i, FullBudget A (G.first.Q i))
    (hBP : ∀ j, FullBudget B (G.second.P j)) (hBQ : ∀ j, FullBudget B (G.second.Q j))
    (hF : G.firstProbe = AffineProbe.coordinate (2 : Fin 3))
    (hS : G.secondProbe = AffineProbe.reflectedCoordinate G.d (0 : Fin 3))
    {i : Fin k} {j : Fin h} (hw : 0 < G.weight i j) {z : ℝ}
    (hzA : z ∈ G.first.auxiliaryInterval G.firstProbe i)
    (hzB : z ∈ G.second.auxiliaryInterval G.secondProbe j) :
    FullBudget (A + B - G.d) ((G.curve i j).value z) := by
  have hs := G.positive_sources hw
  have hnA : G.firstProbe.value (G.first.P i) ≠ G.firstProbe.value (G.first.Q i) := by
    intro hc
    have he := G.first.constant_probe_weight_zero G.firstProbe G.d G.first_uniform i hc
    rw [he] at hs
    exact (lt_irrefl 0 hs.1)
  have hnB : G.secondProbe.value (G.second.P j) ≠ G.secondProbe.value (G.second.Q j) := by
    intro hc
    have he := G.second.constant_probe_weight_zero G.secondProbe G.d G.second_uniform j hc
    rw [he] at hs
    exact (lt_irrefl 0 hs.2)
  have ha := G.first.pointAt_fullBudget G.firstProbe hAP hAQ i hnA hzA
  have hb := G.second.pointAt_fullBudget G.secondProbe hBP hBQ j hnB hzB
  have hα := G.first.pointAt_probe G.firstProbe i hnA z
  have hβ := G.second.pointAt_probe G.secondProbe j hnB z
  have hmatch : (G.first.pointAt G.firstProbe i z) 2 = G.d - (G.second.pointAt G.secondProbe j z) 0 := by
    change (G.firstProbe.value (G.first.pointAt G.firstProbe i z)) = z at hα
    have hα' : (G.first.pointAt G.firstProbe i z) 2 = z := by simpa only [hF, AffineProbe.coordinate] using hα
    have hβ' : G.d - (G.second.pointAt G.secondProbe j z) 0 = z := by simpa only [hS, AffineProbe.reflectedCoordinate] using hβ
    exact hα'.trans hβ'.symm
  exact glueAllocation_fullBudget ha hb hmatch

theorem descriptor_endpoints {k h : ℕ} (G : OverlapGluing k h) {A B : ℝ}
    (hAP : ∀ i, FullBudget A (G.first.P i)) (hAQ : ∀ i, FullBudget A (G.first.Q i))
    (hBP : ∀ j, FullBudget B (G.second.P j)) (hBQ : ∀ j, FullBudget B (G.second.Q j))
    (hF : G.firstProbe = AffineProbe.coordinate (2 : Fin 3))
    (hS : G.secondProbe = AffineProbe.reflectedCoordinate G.d (0 : Fin 3))
    (hbudget : 0 ≤ A + B - G.d) :
    (∀ r, FullBudget (A + B - G.d) ((G.descriptor (A + B - G.d)).P r)) ∧
      (∀ r, FullBudget (A + B - G.d) ((G.descriptor (A + B - G.d)).Q r)) := by
  have hEnd : ∀ i j, 0 < G.weight i j →
      FullBudget (A + B - G.d) ((G.curve i j).value (G.lower i j)) ∧
        FullBudget (A + B - G.d) ((G.curve i j).value (G.upper i j)) := by
    intro i j hw
    have he := overlap_endpoint_membership
      (G.firstProbe.value (G.first.P i)) (G.firstProbe.value (G.first.Q i))
      (G.secondProbe.value (G.second.P j)) (G.secondProbe.value (G.second.Q j)) (G.positive_overlap hw)
    exact ⟨G.active_curve_budget hAP hAQ hBP hBQ hF hS hw he.1.1 he.1.2,
      G.active_curve_budget hAP hAQ hBP hBQ hF hS hw he.2.1 he.2.2⟩
  constructor
  · intro r
    change FullBudget (A + B - G.d) (G.safeP _ (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2)
    unfold safeP
    split_ifs with hw
    · exact (hEnd _ _ hw).1
    · exact budgetRow_fullBudget hbudget
  · intro r
    change FullBudget (A + B - G.d) (G.safeQ _ (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2)
    unfold safeQ
    split_ifs with hw
    · exact (hEnd _ _ hw).2
    · exact budgetRow_fullBudget hbudget

end OverlapGluing
end Blotto
