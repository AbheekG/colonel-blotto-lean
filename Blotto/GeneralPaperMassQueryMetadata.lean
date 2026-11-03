import Blotto.GeneralPaperMassReadPrice

/-! Native annotations returned by one power query and one product are
bounded as data and their actual additions are priced. No child is replayed
to obtain its annotation, and no price field is stored by the algorithm.
-/
namespace Blotto.GeneralPaperMassQueryMetadata
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

def cap (p columns : ℕ) : ℕ := (columns+2)*(12*(p+1)+82)+64
def width (p columns : ℕ) : ℕ := 64+16*(binaryWordWidth (p+1)+binaryWordWidth (columns+2)+1)

theorem word_bound (p columns : ℕ) : 1+binaryWordWidth (cap p columns)≤width p columns := by
  have hA := binaryWordWidth_mul 12 (p+1)
  have hB := GeneralPaperRayOperandWidthEnvelope.word_add (12*(p+1)) 82
  have hC := binaryWordWidth_mul (columns+2) (12*(p+1)+82)
  have hD := GeneralPaperRayOperandWidthEnvelope.word_add ((columns+2)*(12*(p+1)+82)) 64
  have h12 : binaryWordWidth 12=4 := by decide
  have h82 : binaryWordWidth 82=7 := by decide
  have h64 : binaryWordWidth 64=7 := by decide
  unfold cap width
  omega

theorem native_bound (lambda k exponent : ℕ) (mass : GeneralPaperDyadicFloat.Number) :
    let prepared := GeneralPaperPreparedPowers.prepare lambda k
    (GeneralPaperPreparedPowers.query prepared exponent).work+
      (GeneralPaperDyadicMultiply.multiply prepared.format.unit prepared.format.fractionalBits
        (GeneralPaperPreparedPowers.query prepared exponent).number mass).work+16≤
          cap prepared.format.fractionalBits prepared.format.columns := by
  have hQ := GeneralPaperPreparedPowers.query_work lambda k exponent
  have hP := GeneralPaperDyadicMultiply.multiply_work (GeneralPaperPreparedPowers.prepare lambda k).format.unit
    (GeneralPaperPreparedPowers.prepare lambda k).format.fractionalBits
    (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k) exponent).number mass
  unfold cap
  nlinarith only [hQ,hP]

theorem operand_width (m lambda k Qv : ℕ) :
    width (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits (GeneralPaperPowerPrecision.prepare lambda k).columns≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  have hc := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).columns
  have hPWord := GeneralPaperInitializerControlCounters.word_le_self ((GeneralPaperPowerPrecision.prepare lambda k).fractionalBits+1)
  have hCWord := GeneralPaperInitializerControlCounters.word_le_self ((GeneralPaperPowerPrecision.prepare lambda k).columns+2)
  have hPos := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change 128≤M at hPos
  change (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits≤128*M at hp
  change (GeneralPaperPowerPrecision.prepare lambda k).columns≤32*M at hc
  change width _ _≤1048576*M
  unfold width
  omega

end Blotto.GeneralPaperMassQueryMetadata
