import Blotto.NativeArrayCoreControl
import Blotto.BinaryLifetimeArray

/-! Derived binary widths for the exact pinned array-builder scalar inventory.
The core bridge imports only the pinned standard-library implementation. -/
namespace Blotto.NativeArrayBuildControl
open NativeArrayCoreControl

theorem build_scalar_width {n : ℕ} {α : Type*} (produce : Fin n → α) :
    ∀ s ∈ (build produce).2,∀ value ∈ s.operands n,binaryWordWidth value ≤ binaryWordWidth (n+1) := by
  intro s hs value hv
  exact binaryWordWidth_mono ((Snapshot.operand_bound (build_valid produce s hs)) value hv)

end Blotto.NativeArrayBuildControl
