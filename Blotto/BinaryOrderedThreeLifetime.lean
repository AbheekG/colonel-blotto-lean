import Blotto.BinaryThreeReferenceLifetime
import Blotto.BinaryThreeGeometryLifetime
import Blotto.BinaryQuadraticThreeFactoryLifetime

/-! The complete ordered three-variable factory traces the reached regime
test and either actual regular geometry/factory or exceptional endpoint arrays.
One five-word environment is retained and consumed throughout. -/
namespace Blotto.BinaryOrderedThreeLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryThreeInputCompiler BinaryThreeGeometryLifetime
set_option maxHeartbeats 2000000

def descriptorWithTrace (input : Input) : BinaryStoredOverlapEnvironment.Segment 3 9 × Trace :=
  let environment := environmentWithTrace input
  let regime := regimeWithTrace environment.1
  let compared := BinaryQuadraticExpressionLifetime.compareWithTrace regime.1 BinaryRationalOpcode.zero
  if !compared.1 then
    let geometry := geometryWithTrace environment.1
    let factory := BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace geometry.1
    (factory.1,wrap 32 2 [environment.2,regime.2,compared.2,geometry.2,factory.2])
  else
    let factory := BinaryThreeReferenceLifetime.exceptionalWithTrace input
    (factory.1,wrap 32 2 [environment.2,regime.2,compared.2,factory.2])

theorem descriptorWithTrace_erasure (input : Input) (hC : input.Canonical) :
    (descriptorWithTrace input).1 = BinaryThreeInputCompiler.descriptor input := by
  unfold descriptorWithTrace BinaryThreeInputCompiler.descriptor regular
  dsimp only [environmentWithTrace]
  simp only [regimeWithTrace_erasure input.environment (input_canonical input hC),
    BinaryQuadraticExpressionLifetime.compareWithTrace_erases]
  split
  · rename_i hRegular
    simp only [hRegular,ite_true]
    rw [geometryWithTrace_erasure input.environment (input_canonical input hC)]
    exact BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace_erases (geometryEnvironment input) (geometry_canonical input hC)
  · rename_i hExceptional
    simp only [hExceptional,ite_false]
    exact BinaryThreeReferenceLifetime.exceptionalWithTrace_erasure input

end Blotto.BinaryOrderedThreeLifetime
