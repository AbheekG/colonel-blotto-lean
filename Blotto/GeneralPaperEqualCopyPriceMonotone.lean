import Blotto.GeneralPaperEqualReferenceCopyContract

/-! Explicit copy-price monotonicity in native dimensions and short field
widths. The original budget payload remains one additive term. -/
namespace Blotto.GeneralPaperEqualCopyPriceMonotone
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem sampler (S n b e : ℕ) {A B m M r R s t c C d D P Q w V a z : ℕ}
    (hA : A ≤ B) (hm : m ≤ M) (hr : r ≤ R) (hs : s ≤ t) (hc : c ≤ C)
    (hd : d ≤ D) (hP : P ≤ Q) (hw : w ≤ V) (ha : a ≤ z) :
    GeneralPaperEqualSamplerCopy.price S A n m r s c d P b w e a ≤
      GeneralPaperEqualSamplerCopy.price S B n M R t C D Q b V e z := by
  dsimp only [GeneralPaperEqualSamplerCopy.price,GeneralPaperEqualPreparedCopy.price,
    GeneralPaperEqualRationalCopy.routesPrice,GeneralPaperEqualRationalCopy.segmentsPrice,
    GeneralPaperScalarTableCopy.price,GeneralPaperScalarTableCopy.matrixPrice,
    GeneralPaperReferenceCopy.arrayPrice,GeneralPaperEqualBooleanCopy.price,
    GeneralPaperEqualBooleanCopy.wordPrice,GeneralPaperEncodedScalarStorage.natBits]
  gcongr

theorem scalar_target (S n P : ℕ) {A B : ℕ} (h : A ≤ B) :
    GeneralPaperScalarTableCopy.price S A n P ≤ GeneralPaperScalarTableCopy.price S B n P := by
  unfold GeneralPaperScalarTableCopy.price
  gcongr

end Blotto.GeneralPaperEqualCopyPriceMonotone
