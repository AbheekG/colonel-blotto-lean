import Blotto.GeneralPaperPhysicalResponseRound

/-! Shared-shift construction and every physical response check retain
the source's advertised powers. Absorb the field-squared sum/check term
using native Lambda>=m before combining it with decoder costs. -/
namespace Blotto.GeneralPaperPhysicalResponseRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperSourceStorageRates GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

@[fun_prop]
theorem cap_word_small : Small (fun x => binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).qbar) :=
  GeneralPaperSourceWordGrowth.dominated GeneralPaperSourceWordGrowth.denominator_word_small
    (fun x => binaryWordWidth_mono (GeneralPaperSourceAlphabetLower.cap_le_order x.m x.k))

def shiftCertificate : Certificate (fun x => GeneralPaperResponsePhysicalHeights.shiftHeight x.m
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x).C) := by
  refine ⟨_,_,_,by unfold GeneralPaperResponsePhysicalHeights.shiftHeight; source_space⟩

theorem shift_degrees : (shiftCertificate.fields,shiftCertificate.symbols,shiftCertificate.accuracy)=(1,1,0) := rfl

def additionCertificate : Certificate (fun x => GeneralPaperPhysicalBidExecution.additionWidth x.m
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar ((alphabet x).lambda+1) (alphabet x)) := by
  refine ⟨_,_,_,by
    unfold GeneralPaperPhysicalBidExecution.additionWidth GeneralPaperResponsePhysicalHeights.word
      GeneralPaperResponsePhysicalHeights.prefixHeight GeneralPaperResponsePhysicalHeights.bidHeight
      GeneralPaperResponsePhysicalHeights.shiftHeight
    source_space⟩

theorem addition_degrees : (additionCertificate.fields,additionCertificate.symbols,additionCertificate.accuracy)=(1,1,0) := rfl

theorem addition_small : Small (fun x => GeneralPaperPhysicalBidExecution.additionWidth x.m
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar ((alphabet x).lambda+1) (alphabet x)) := by
  unfold GeneralPaperPhysicalBidExecution.additionWidth GeneralPaperResponsePhysicalHeights.word
    GeneralPaperResponsePhysicalHeights.prefixHeight GeneralPaperResponsePhysicalHeights.bidHeight
    GeneralPaperResponsePhysicalHeights.shiftHeight
  fun_prop

theorem addition_price (C d : ℕ) : Rated (fun x => (GeneralPaperFastRationalMajorant.model C d).rat
    (GeneralPaperPhysicalBidExecution.additionWidth x.m (GeneralPaperProxyParameters.prepare x.m x.k).qbar
      ((alphabet x).lambda+1) (alphabet x))) 1 1 0 :=
  GeneralPaperSourceRateAlgebra.charge (C+1) d _ 1 1 0 additionCertificate.bound addition_small

def correctionCertificate (C d : ℕ) : Certificate (fun x => (5*x.m+2)*(GeneralPaperFastRationalMajorant.model C d).rat
    (GeneralPaperPhysicalBidExecution.additionWidth x.m (GeneralPaperProxyParameters.prepare x.m x.k).qbar
      ((alphabet x).lambda+1) (alphabet x))) := by
  have hp := addition_price C d
  refine ⟨_,_,_,by source_space⟩

theorem correction_degrees (C d : ℕ) :
    ((correctionCertificate C d).fields,(correctionCertificate C d).symbols,(correctionCertificate C d).accuracy)=(2,1,0) := rfl

theorem correction (C d : ℕ) : Rated (fun x => (5*x.m+2)*(GeneralPaperFastRationalMajorant.model C d).rat
    (GeneralPaperPhysicalBidExecution.additionWidth x.m (GeneralPaperProxyParameters.prepare x.m x.k).qbar
      ((alphabet x).lambda+1) (alphabet x))) 1 2 0 :=
  rate_mono (correctionCertificate C d).bound GeneralPaperSourceRowsRates.field_absorption

theorem bit_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperPhysicalResponseExecution.bitProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m
      (GeneralPaperProxyParameters.prepare x.m x.k).qbar ((alphabet x).lambda+1) (alphabet x)) 1 2 0 := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hd := GeneralPaperSourceRowsRates.row_bit C d W hW
  have hc := correction C d
  have ho : Rated (fun x => 128*(x.m+1)*arrayWord (W x) x.m+128*W x) 1 0 0 := by
    unfold arrayWord
    source_space
  have hall := add_same (add_same hd hc) (weaken ho (by decide : 1≤1) (by decide : 0≤2) (by decide : 0≤0))
  apply dominated hall
  intro x
  unfold GeneralPaperPhysicalResponseExecution.bitProfile GeneralPaperPhysicalResponseExecution.rowBitProfile
  exact le_of_eq (by ring)

def arithmeticCertificate : Certificate (fun x => GeneralPaperPhysicalResponseExecution.arithmeticProfile x.m (alphabet x)) := by
  refine ⟨_,_,_,by unfold GeneralPaperPhysicalResponseExecution.arithmeticProfile; source_space⟩

theorem arithmetic_degrees :
    (arithmeticCertificate.fields,arithmeticCertificate.symbols,arithmeticCertificate.accuracy)=(1,1,0) := rfl

def shiftPriceCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperPhysicalShiftExecution.bitProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m
      (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x).C) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  refine ⟨_,_,_,by
    unfold GeneralPaperPhysicalShiftExecution.bitProfile GeneralPaperPhysicalShiftExecution.width
      GeneralPaperPhysicalShiftExecution.natWidth arrayWord
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem shift_price_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((shiftPriceCertificate C d W hW).fields,(shiftPriceCertificate C d W hW).symbols,
      (shiftPriceCertificate C d W hW).accuracy)=(1,1,0) := rfl

theorem all_response_bit_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows*
      GeneralPaperPhysicalResponseExecution.bitProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m
        (GeneralPaperProxyParameters.prepare x.m x.k).qbar ((alphabet x).lambda+1) (alphabet x)) 1 3 2 :=
  GeneralPaperSourceRateAlgebra.mul _ _ 0 1 2 1 2 0 rows (bit_rate C d W hW)

theorem all_response_arithmetic_rate : Rated (fun x =>
    (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows*
      GeneralPaperPhysicalResponseExecution.arithmeticProfile x.m (alphabet x)) 1 2 2 :=
  GeneralPaperSourceRateAlgebra.mul _ _ 0 1 2 1 1 0 rows arithmeticCertificate.bound

end Blotto.GeneralPaperPhysicalResponseRates
