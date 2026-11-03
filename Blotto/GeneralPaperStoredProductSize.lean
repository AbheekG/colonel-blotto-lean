import Blotto.GeneralPaperBasisCacheSize

/-! Bounds for the actual materialized integer products. Dot-product
prefixes use the preceding native accumulator theorem; each stored
result is bounded without assuming cancellation or rational reduction.
-/
namespace Blotto.GeneralPaperStoredProductSize
open GeneralPaperBasisStoredProducts
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem mulVec {n : ℕ} (A : IntMatrix n) (u : Vector n) (H U : ℕ)
    (hA : ∀ a b,((A.read a).read b).natAbs≤H) (hu : ∀ a,(u.read a).natAbs≤U) (j : Fin n) :
    ((mulVecRun A u).1.read j).natAbs≤n*H*U := by
  rw [mulVec_data]
  have hh := GeneralPaperIntegerDotSize.run_bound (fun k => (A.read j).read k) u.read H U (hA j) hu
  simpa only [GeneralPaperBasisIntegerDot.run_value,Matrix.mulVec,dotProduct,observe] using hh

theorem row {n : ℕ} (v : Vector n) (A : IntMatrix n) (V H : ℕ)
    (hv : ∀ a,(v.read a).natAbs≤V) (hA : ∀ a b,((A.read a).read b).natAbs≤H) (j : Fin n) :
    ((rowRun v A).1.read j).natAbs≤n*V*H := by
  rw [row_data]
  have hh := GeneralPaperIntegerDotSize.run_bound v.read (fun k => (A.read k).read j) V H hv (fun k => hA k j)
  simpa only [GeneralPaperBasisIntegerDot.run_value,GeneralPaperBasisAdjugateBlock.rowProduct,dotProduct,observe] using hh

end Blotto.GeneralPaperStoredProductSize
