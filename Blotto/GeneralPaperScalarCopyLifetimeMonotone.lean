import Blotto.GeneralPaperEqualCopyComponentContract

/-! Monotonicity of the literal scalar-array and active scalar copy reserves.
This changes only analysis majorants; executed destination references remain
the references stored by the actual selected closure. -/
namespace Blotto.GeneralPaperScalarCopyLifetimeMonotone
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem scalar (S : ℕ) {A D P Q : ℕ} (hA : A ≤ D) (hP : P ≤ Q) :
    GeneralPaperScalarTableCopyLifetime.scalarProfile S A P ≤ GeneralPaperScalarTableCopyLifetime.scalarProfile S D Q := by
  unfold GeneralPaperScalarTableCopyLifetime.scalarProfile GeneralPaperScalarTableCopyLifetime.scalarPrice
    GeneralPaperEncodedScalarStorage.natBits
  gcongr

theorem table (S n : ℕ) {A D B C P Q : ℕ} (hA : A ≤ D) (hB : B ≤ C) (hP : P ≤ Q) :
    GeneralPaperScalarTableCopyLifetime.profile S A n B P ≤ GeneralPaperScalarTableCopyLifetime.profile S D n C Q := by
  unfold GeneralPaperScalarTableCopyLifetime.profile GeneralPaperReferenceArrayCopyLifetime.profile
    GeneralPaperReferenceArrayCopyLifetime.parentCap GeneralPaperDualWidthFillStorage.profile
    GeneralPaperAdditivePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap
    GeneralPaperScalarTableCopyLifetime.scalarProfile GeneralPaperScalarTableCopyLifetime.scalarPrice
    GeneralPaperEncodedScalarStorage.natBits
  gcongr

end Blotto.GeneralPaperScalarCopyLifetimeMonotone
