import Blotto.GeneralPaperSourceRowsContract

/-! Decoder and explicit rational budget-check costs fit the advertised
source-stage rates. Field-squared summation is absorbed using the actual
constructed Lambda>=m before it is combined with decoding. -/
namespace Blotto.GeneralPaperSourceRowsRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSummaryArrayExecution
open GeneralPaperSourceRateAlgebra GeneralPaperSourceStorageRates GeneralPaperSourceRowsExecution
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

def rowBitCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    rowBitProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m (alphabet x)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  refine ⟨_,_,_,by
    unfold rowBitProfile GeneralPaperClosedBidExecution.bitProfile GeneralPaperClosedBidExecution.width
      GeneralPaperDecoderControls.operandWidth GeneralPaperDecoderControls.controlWord arrayWord
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem row_bit_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((rowBitCertificate C d W hW).fields,(rowBitCertificate C d W hW).symbols,
      (rowBitCertificate C d W hW).accuracy)=(1,2,0) := rfl

@[fun_prop]
theorem row_bit (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    rowBitProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m (alphabet x)) 1 2 0 :=
  (rowBitCertificate C d W hW).bound

def budgetCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperRowBudgetExecution.bitProfile (GeneralPaperFastRationalMajorant.model C d) (arrayWord (W x) x.m)
      x.m (binaryWordWidth (alphabet x).C) ((alphabet x).lambda+1)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  refine ⟨_,_,_,by
    unfold GeneralPaperRowBudgetExecution.bitProfile GeneralPaperRowBudgetExecution.width arrayWord
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem budget_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((budgetCertificate C d W hW).fields,(budgetCertificate C d W hW).symbols,
      (budgetCertificate C d W hW).accuracy)=(2,1,0) := rfl

theorem field_absorption (x : Input) : monomial 2 1 0 x≤monomial 1 2 0 x := by
  have h := GeneralPaperSourceAlphabetLower.fields_le_lambda x.m x.k
  have hfs : fields x≤symbols x := by
    change x.m≤(alphabet x).lambda at h
    unfold fields symbols
    omega
  dsimp only [monomial,pow_zero,pow_one,Nat.mul_one]
  nlinarith only [Nat.mul_le_mul_left (fields x*symbols x) hfs]

@[fun_prop]
theorem budget_bit (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperRowBudgetExecution.bitProfile (GeneralPaperFastRationalMajorant.model C d) (arrayWord (W x) x.m)
      x.m (binaryWordWidth (alphabet x).C) ((alphabet x).lambda+1)) 1 2 0 :=
  rate_mono (budgetCertificate C d W hW).bound field_absorption

def bitCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    bitProfile (GeneralPaperFastRationalMajorant.model C d) (W x)
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows x.m
      ((alphabet x).lambda+1) (alphabet x)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hb := row_bit C d W hW
  have hc := budget_bit C d W hW
  refine ⟨_,_,_,by
    unfold bitProfile arrayWord
    source_space⟩

theorem bit_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((bitCertificate C d W hW).fields,(bitCertificate C d W hW).symbols,
      (bitCertificate C d W hW).accuracy)=(1,3,2) := rfl

def arithmeticCertificate : Certificate (fun x =>
    arithmeticProfile (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows x.m (alphabet x)) := by
  refine ⟨_,_,_,by
    unfold arithmeticProfile rowArithmeticProfile GeneralPaperClosedBidExecution.arithmeticProfile
    source_space⟩

theorem arithmetic_degrees :
    (arithmeticCertificate.fields,arithmeticCertificate.symbols,arithmeticCertificate.accuracy)=(1,2,2) := rfl

theorem real_core_bound : ∃ A e : ℕ,∀ x,
    arithmeticProfile (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows x.m (alphabet x)≤
      A*monomial 1 2 2 x*(GeneralPaperSourceCoreLogBound.coreLog x)^e :=
  GeneralPaperSourceCoreLogBound.remove_unused_height arithmeticCertificate.bound (fun _ => rfl) (fun _ => rfl)

theorem bit_bound (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : ∃ A e : ℕ,∀ x,
    bitProfile (GeneralPaperFastRationalMajorant.model C d) (W x)
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows x.m
      ((alphabet x).lambda+1) (alphabet x)≤A*monomial 1 3 2 x*(logSize x)^e :=
  (bitCertificate C d W hW).bound

end Blotto.GeneralPaperSourceRowsRates
