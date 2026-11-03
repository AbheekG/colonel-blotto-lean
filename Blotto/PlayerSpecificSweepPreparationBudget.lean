import Blotto.PlayerSpecificSweepPreparationExecution

/-! One polynomial original-field envelope covers the actual initial,
suffix, cell-construction and enclosing preparation caller. -/
namespace Blotto.PlayerSpecificSweepPreparationBudget
open PlayerSpecificRationalSweepHeights PlayerSpecificRationalCellHeights
set_option autoImplicit false
set_option maxHeartbeats 2000000

def height (N H : ℕ) : ℕ := 10*(N+1)*(H+1)
def width (N H : ℕ) : ℕ := 4096*(N+1)*(H+1)

theorem profiles (N H : ℕ) :
    initialBound N H≤height N H ∧ bound (initialBound N H) H N≤height N H ∧
      PlayerSpecificSweepTraceFits.width (initialBound N H) N≤width N H ∧
      PlayerSpecificSweepTraceFits.width H N≤width N H ∧
      PlayerSpecificCellConstructionCopyCost.width (initialBound N H) H N≤width N H ∧
      128*(height N H+1)≤width N H ∧ N+3≤width N H ∧ H≤height N H := by
  unfold PlayerSpecificCellConstructionCopyCost.width PlayerSpecificSweepTraceFits.width
    PlayerSpecificCellConstructionCopyCost.height initialBound bound height width
  have hNH : 0≤N*H := Nat.zero_le _
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith only [hNH]

end Blotto.PlayerSpecificSweepPreparationBudget
