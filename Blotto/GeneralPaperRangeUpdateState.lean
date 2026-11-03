import Blotto.GeneralPaperParentCachePrice

/-! Actual output paths supply the post-update cache invariants needed by
parent recomputation. Both child outputs are derived from the native partial
node equation; these proofs do not execute a validation or replay pass.
-/
namespace Blotto.GeneralPaperRangeUpdateState
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalGeometry
open GeneralPaperGlobalNodeQuery GeneralPaperPreparedPowers
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem output_valid (lambda k : ℕ) (lo hi : ℚ) (amount height : ℕ) (n : Node height) (start span : ℚ)
    (hValid : Valid lambda k n)
    (hOutput : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalUpdate.run (prepare lambda k) lo hi amount height n start span).node) :
    Valid lambda k (GeneralPaperIntervalUpdate.run (prepare lambda k) lo hi amount height n start span).node := by
  apply GeneralPaperIntervalOutputValidity.run_valid_of_output lambda k lo hi amount height n start span hValid
  intro i hi
  simpa only [Nat.zero_add] using hOutput i hi

theorem partial_children (lambda k : ℕ) (lo hi : ℚ) (amount height : ℕ) (n : Node (height+1)) (start span : ℚ)
    (hD : ¬Disjoint start span lo hi) (hC : ¬Covered start span lo hi) (hValid : Valid lambda k n)
    (hOutput : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalUpdate.run (prepare lambda k) lo hi amount (height+1) n start span).node) :
    let left := (GeneralPaperIntervalUpdate.run (prepare lambda k) lo hi amount height (leftChild n) start (span/2)).node
    let right := (GeneralPaperIntervalUpdate.run (prepare lambda k) lo hi amount height (rightChild n) (start+span/2) (span/2)).node
    Valid lambda k left ∧ Valid lambda k right ∧
      PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 left ∧
      PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 right := by
  let left := (GeneralPaperIntervalUpdate.run (prepare lambda k) lo hi amount height (leftChild n) start (span/2)).node
  let right := (GeneralPaperIntervalUpdate.run (prepare lambda k) lo hi amount height (rightChild n) (start+span/2) (span/2)).node
  have hv := output_valid lambda k lo hi amount (height+1) n start span hValid hOutput
  rw [partial_node (prepare lambda k) lo hi amount height n start span hD hC] at hv hOutput
  change offset n≤GeneralPaperPowerPrecision.levelBound lambda k ∧ Valid lambda k left ∧ Valid lambda k right ∧ _ at hv
  refine ⟨hv.2.1,hv.2.2.1,?_,?_⟩
  · intro i hIndex
    have hRange : i<2^(height+1) := by rw [pow_succ]; omega
    have h := hOutput i hRange
    change 0+(offset n+(if i<2^height then levelAt left i else levelAt right (i-2^height)))≤_ at h
    rw [ite_eq_left hIndex] at h
    change 0+levelAt left i≤GeneralPaperPowerPrecision.levelBound lambda k
    omega
  · intro i hIndex
    have hRange : 2^height+i<2^(height+1) := by rw [pow_succ]; omega
    have h := hOutput (2^height+i) hRange
    change 0+(offset n+(if 2^height+i<2^height then levelAt left (2^height+i) else levelAt right (2^height+i-2^height)))≤_ at h
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left] at h
    change 0+levelAt right i≤GeneralPaperPowerPrecision.levelBound lambda k
    omega

theorem output_path_from_effect (lambda k lo hi amount height start : ℕ) (n : Node height)
    (hFinal : ∀ i<2^height,levelAt n i+(if lo≤start+i ∧ start+i<hi then amount else 0)≤
      GeneralPaperPowerPrecision.levelBound lambda k) :
    PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalUpdate.run (prepare lambda k) (lo:ℚ) hi amount height n (start:ℚ) ((2:ℚ)^height)).node := by
  intro i hIndex
  rw [Nat.zero_add,update_level (prepare lambda k) lo hi amount height n start i hIndex]
  exact hFinal i hIndex

end Blotto.GeneralPaperRangeUpdateState
