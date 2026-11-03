import Blotto.GeneralPaperEqualPreparationLifetime
import Blotto.GeneralPaperNativeScaleConstructionStorage

/-! Fast bit arithmetic preserves additive input rates. These are uniform
analysis-family bounds, not runtime certificates or a reference-word oracle.
Reference calibration and original input-family instantiation remain separate. -/
namespace Blotto.GeneralPaperEqualRateAlgebra
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

@[fun_prop]
theorem rational_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (f : Input → ℕ) (hf : Small f) : Small (fun x => model.rat (f x)) := by
  obtain ⟨C, d, hg⟩ := hFast
  exact GeneralPaperValueWeightSumConstructionStorage.primitive_small hg f hf

@[fun_prop]
theorem rational_poly (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (f : Input → ℕ) (hf : Polylog f) (hs : Small f) : Polylog (fun x => model.rat (f x)) := by
  obtain ⟨C, d, hg⟩ := hFast
  exact primitive_preserves hg hf hs

@[fun_prop]
theorem rational_linear (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (f r : Input → ℕ) (hf : Linear f r) (hs : Small f) : Linear (fun x => model.rat (f x)) r := by
  obtain ⟨C, d, hg⟩ := hFast
  exact primitive_preserves hg hf hs

@[fun_prop]
theorem encoded_natural_poly (f : Input → ℕ) (hf : Small f) :
    Polylog (fun x => GeneralPaperEncodedScalarStorage.natBits (f x)) := by
  unfold GeneralPaperEncodedScalarStorage.natBits
  fun_prop

@[fun_prop]
theorem encoded_natural_linear (f r : Input → ℕ) (hf : Small f) :
    Linear (fun x => GeneralPaperEncodedScalarStorage.natBits (f x)) r :=
  linear_poly _ r (encoded_natural_poly f hf)

@[fun_prop]
theorem encoded_natural_small (f : Input → ℕ) (hf : Small f) :
    Small (fun x => GeneralPaperEncodedScalarStorage.natBits (f x)) := by
  unfold GeneralPaperEncodedScalarStorage.natBits
  fun_prop

@[fun_prop]
theorem sub_linear (f g r : Input → ℕ) (hf : Linear f r) : Linear (fun x => f x - g x) r :=
  GeneralPaperSourceSoftBounds.dominated hf (fun _ => Nat.sub_le _ _)

@[fun_prop]
theorem maximum_linear (f g r : Input → ℕ) (hf : Linear f r) (hg : Linear g r) : Linear (fun x => max (f x) (g x)) r :=
  GeneralPaperSourceSoftBounds.dominated (add_same hf hg) (fun _ => by omega)

@[fun_prop]
theorem overhead_linear (n A r : Input → ℕ) (hn : Linear n r) (hs : Small n) (hA : Polylog A) :
    Linear (fun x => PaperIndexedArrayConstruction.overhead id (A x) (n x) (n x)) r := by
  have hOver : ∀ x, PaperIndexedArrayConstruction.overhead id (A x) (n x) (n x) ≤
      (n x + 1) * (6 * A x + 10 * binaryWordWidth (n x + 1) + 28) := by
    intro x
    simpa only [Nat.mul_one] using PaperIndexedArrayConstruction.overhead_bound id 1 (fun w => by change w ≤ 1 * w; omega) (A x) (n x) (n x) le_rfl
  have hMajor : Linear (fun x =>
      (n x + 1) * (6 * A x + 10 * binaryWordWidth (n x + 1) + 28)) r := by fun_prop
  exact GeneralPaperSourceSoftBounds.dominated hMajor hOver

@[fun_prop]
theorem sub_poly (f g : Input → ℕ) (hf : Polylog f) : Polylog (fun x => f x - g x) :=
  GeneralPaperSourceSoftBounds.dominated hf (fun _ => Nat.sub_le _ _)

@[fun_prop]
theorem maximum_poly (f g : Input → ℕ) (hf : Polylog f) (hg : Polylog g) :
    Polylog (fun x => max (f x) (g x)) :=
  GeneralPaperSourceSoftBounds.dominated (add_same hf hg) (fun _ => by omega)

theorem linear_small {f r : Input → ℕ} (hf : Linear f r) (hr : Small r) : Small f :=
  GeneralPaperSourceRowsStorageRates.soft_small hf (by fun_prop)

@[fun_prop]
theorem overhead_small (n A : Input → ℕ) (hn : Small n) (hA : Small A) :
    Small (fun x => PaperIndexedArrayConstruction.overhead id (A x) (n x) (n x)) := by
  have hMajor : Small (fun x =>
      (n x + 1) * (6 * A x + 10 * binaryWordWidth (n x + 1) + 28)) := by fun_prop
  apply GeneralPaperSourceWordGrowth.dominated hMajor
  intro x
  simpa only [Nat.mul_one] using PaperIndexedArrayConstruction.overhead_bound id 1
    (fun w => by change w ≤ 1 * w; omega) (A x) (n x) (n x) le_rfl

theorem poly_small {f : Input → ℕ} (hf : Polylog f) : Small f := GeneralPaperCacheConstructionGrowth.small_of_poly hf

end Blotto.GeneralPaperEqualRateAlgebra
