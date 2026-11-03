import Blotto.GeneralPaperGlobalNodeQuery

/-! Cache validity from the levels of the actual updated tree. Only nodes
that receive the range increment need the enlarged offset cap; disjoint
codes need no reserve for an increment that they do not receive.
-/
namespace Blotto.GeneralPaperIntervalOutputValidity
open GeneralPaperIntervalCache GeneralPaperIntervalGeometry GeneralPaperIntervalUpdate
open GeneralPaperIntervalLevels GeneralPaperPreparedPowers
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem run_valid_of_output (lambda k : ℕ) (lo hi : ℚ) (amount height : ℕ) (node : Node height) (start span : ℚ)
    (hValid : Valid lambda k node)
    (hOutput : ∀ i<2^height,
      levelAt (run (prepare lambda k) lo hi amount height node start span).node i≤GeneralPaperPowerPrecision.levelBound lambda k) :
    Valid lambda k (run (prepare lambda k) lo hi amount height node start span).node := by
  induction height generalizing start span with
  | zero =>
    by_cases hD : Disjoint start span lo hi
    · rw [run.eq_def,if_pos hD]
      exact hValid
    · by_cases hC : Covered start span lo hi
      · have hn : (run (prepare lambda k) lo hi amount 0 node start span).node=raiseRoot amount node := by
          rw [run.eq_def,if_neg hD,if_pos hC]
        rw [hn] at hOutput ⊢
        have hc := hOutput 0 (Nat.two_pow_pos _)
        rw [raised_level] at hc
        exact raised_valid lambda k amount node hValid (by have := offset_le_level node 0; omega)
      · rw [run.eq_def,if_neg hD,if_neg hC]
        exact hValid
  | succ height ih =>
    by_cases hD : Disjoint start span lo hi
    · rw [run.eq_def,if_pos hD]
      exact hValid
    · by_cases hC : Covered start span lo hi
      · have hn : (run (prepare lambda k) lo hi amount (height+1) node start span).node=raiseRoot amount node := by
          rw [run.eq_def,if_neg hD,if_pos hC]
        rw [hn] at hOutput ⊢
        have hc := hOutput 0 (Nat.two_pow_pos _)
        rw [raised_level] at hc
        exact raised_valid lambda k amount node hValid (by have := offset_le_level node 0; omega)
      · have hn := partial_node (prepare lambda k) lo hi amount height node start span hD hC
        rw [hn] at hOutput ⊢
        have hChildren := GeneralPaperGlobalNodeQuery.child_validity lambda k node hValid
        apply rebuild_valid lambda k (offset node) _ _ (valid_offset lambda k node hValid)
        · apply ih (leftChild node) start (span/2) hChildren.1
          intro i hi
          have hI : i<2^(height+1) := by rw [pow_succ]; omega
          have hc := hOutput i hI
          change offset node+(if i<2^height then _ else _)≤_ at hc
          rw [if_pos hi] at hc
          omega
        · apply ih (rightChild node) (start+span/2) (span/2) hChildren.2
          intro i hi
          have hI : 2^height+i<2^(height+1) := by rw [pow_succ]; omega
          have hc := hOutput (2^height+i) hI
          change offset node+(if 2^height+i<2^height then _ else _)≤_ at hc
          rw [if_neg (by omega),Nat.add_sub_cancel_left] at hc
          omega

end Blotto.GeneralPaperIntervalOutputValidity
