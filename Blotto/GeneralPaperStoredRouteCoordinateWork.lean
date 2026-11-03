import Blotto.GeneralPaperStoredRouteArrayWork
import Blotto.GeneralPaperStoredRouteCoordinate

/-! Each emitted coordinate includes its actual route, indexed group copy,
multiplication and output word. Optional absent routes retain their zero
branch, with no multiplication. -/
namespace Blotto.GeneralPaperStoredRouteCoordinateWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def bound (model : RationalCostModel) (A m s : ℕ) : ℕ :=
  GeneralPaperStoredRouteArrayWork.heightBound model A m s + (1 + 2 * s) +
    GeneralPaperEncodedScalarStorage.natBits m + binaryWordWidth m +
    5 * model.rat (1 + 4 * s) + 256 * (A + 1)

theorem value_height {m : ℕ} (groups : FixedArrayTable m ℚ) (route : GroupRoute m) (s : ℕ) (hs : 2 ≤ s)
    (hC : RationalHeight route.2 s) (hG : ∀ g,RationalHeight (groups.read g) s) :
    RationalHeight (GeneralPaperStoredRouteCoordinate.value groups route) (2 * s) := by
  rcases route with ⟨label,coefficient⟩
  cases label with
  | none => exact (show RationalHeight (0 : ℚ) 1 by norm_num [RationalHeight]).mono (by omega)
  | some label => simpa only [GeneralPaperStoredRouteCoordinate.value,two_mul] using hC.mul (hG label)

theorem work {m : ℕ} (model : RationalCostModel) (A s : ℕ) (installed : Installed A)
    (groups : FixedArrayTable m ℚ) (index : ℕ) (route : GroupRoute m)
    (hRoute : (GeneralPaperRouteArrayRead.read model A installed index).1 = some (route.1.map Fin.val,route.2))
    (hRouteWork : (GeneralPaperRouteArrayRead.read model A installed index).2 ≤ GeneralPaperStoredRouteArrayWork.heightBound model A m s)
    (hs : 2 ≤ s) (hC : RationalHeight route.2 s) (hG : ∀ g,RationalHeight (groups.read g) s) :
    (GeneralPaperStoredRouteCoordinate.read model A installed groups.data index).2 ≤ bound model A m s := by
  rw [(GeneralPaperStoredRouteCoordinate.source model A installed groups index route hRoute).2]
  rcases route with ⟨label,coefficient⟩
  cases label with
  | none =>
    simp only [GeneralPaperStoredRouteCoordinate.price]
    have hZero : rationalWordWidth (0 : ℚ) = 3 := by decide
    rw [hZero]
    unfold bound
    omega
  | some label =>
    have hCopy := rationalWordWidth_of_height (hG label)
    have hLabel := binaryWordWidth_mono (Nat.le_of_lt label.isLt)
    have hProduct : RationalHeight (coefficient * groups.read label) (2 * s) := by
      simpa only [two_mul] using hC.mul (hG label)
    have hArithmetic := GeneralPaperRationalScalarStep.work model A .mul coefficient (groups.read label) (2 * s)
      (hC.mono (by omega)) ((hG label).mono (by omega)) hProduct
    simp only [GeneralPaperStoredRouteCoordinate.price,groups.size]
    unfold bound GeneralPaperEncodedScalarStorage.natBits at *
    have hWidth : 1 + 2 * (2 * s) = 1 + 4 * s := by omega
    rw [hWidth] at hArithmetic
    omega

end Blotto.GeneralPaperStoredRouteCoordinateWork
