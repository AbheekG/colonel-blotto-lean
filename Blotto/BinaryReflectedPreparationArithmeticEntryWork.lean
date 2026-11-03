import Blotto.BinaryFourPreparationArithmeticEntryWork
import Blotto.BinaryReflectedPreparationMeasured

/-! Entry visits follow actual reflected parameter, system and capacity words.
Only reached raw/comparison entry scans are counted; native prices remain separate. -/
namespace Blotto.BinaryReflectedPreparationArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryExpressionArithmeticEntryWork (tableCost build_bound quadratic_bound)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def system (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) : ℕ :=
  let long := BinaryReflectedSystemMeasured.lengths input
  let scale := BinaryQuadraticMeasured.apply .mul (parameters.read 6) (parameters.read 5)
  BinaryArithmeticEntryWork.raw .mul (parameters.read 6) (parameters.read 5)+
    tableCost 3 (fun j => BinaryArithmeticEntryWork.raw .mul (parameters.read 4) (long.1.1.read j))+
    tableCost 3 (fun j => BinaryArithmeticEntryWork.raw .mul scale.1.1 (long.1.1.read j))

theorem system_bound (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) :
    system input parameters ≤ 2*listCells (BinaryReflectedSystemMeasured.fromParameters input parameters).1.2 := by
  have hs := quadratic_bound .mul (parameters.read 6) (parameters.read 5)
  have hl := build_bound 3
    (fun j => BinaryQuadraticMeasured.apply .mul (parameters.read 4) ((BinaryReflectedSystemMeasured.lengths input).1.1.read j))
    (fun j => BinaryArithmeticEntryWork.raw .mul (parameters.read 4) ((BinaryReflectedSystemMeasured.lengths input).1.1.read j))
    (fun j => quadratic_bound .mul _ _)
  have hi := build_bound 3
    (fun j => BinaryQuadraticMeasured.apply .mul (BinaryQuadraticMeasured.apply .mul (parameters.read 6) (parameters.read 5)).1.1
      ((BinaryReflectedSystemMeasured.lengths input).1.1.read j))
    (fun j => BinaryArithmeticEntryWork.raw .mul (BinaryQuadraticMeasured.apply .mul (parameters.read 6) (parameters.read 5)).1.1
      ((BinaryReflectedSystemMeasured.lengths input).1.1.read j)) (fun j => quadratic_bound .mul _ _)
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,system,BinaryReflectedSystemMeasured.fromParameters_record,BinaryReflectedSystemMeasured.assemble,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def capacity (system : BinaryReflectedFourSetup.System) : ℕ :=
  tableCost 3 (fun j => BinaryArithmeticEntryWork.raw .sub (system.long.read j) (system.short.read j))

theorem capacity_bound (system : BinaryReflectedFourSetup.System) :
    capacity system ≤ 2*listCells (BinaryReflectedSystemMeasured.capacity system).1.2 := by
  simp only [BinaryReflectedSystemMeasured.capacity_record,BinaryPlannedQuadratic.apply_previous]
  exact build_bound 3 _ _ (fun _j => quadratic_bound .sub _ _)

def prepare (input : BinaryFourParameters.Input) : ℕ :=
  let parameters := BinaryFourParametersMeasured.prepare input
  let produced := BinaryReflectedSystemMeasured.fromParameters input parameters.1.1
  BinaryFourPreparationArithmeticEntryWork.parameters input+system input parameters.1.1+capacity produced.1.1

theorem prepare_bound (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    prepare input ≤ 2*listCells (BinaryReflectedPreparationMeasured.prepare input hC).1.2 := by
  have hp := BinaryFourPreparationArithmeticEntryWork.parameters_bound input
  have hs := system_bound input (BinaryFourParametersMeasured.prepare input).1.1
  have hc := capacity_bound (BinaryReflectedSystemMeasured.fromParameters input (BinaryFourParametersMeasured.prepare input).1.1).1.1
  simp only [prepare,BinaryReflectedPreparationMeasured.prepare_record,BinaryReflectedPreparationMeasured.fromParameters_record,
    BinaryReflectedPreparationMeasured.fromSystem_record,BinaryReflectedPreparationMeasured.assemble,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem prepare_input_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    prepare input ≤ 2*BinaryReflectedPreparationMeasured.envelope s := by
  have he := prepare_bound input hC
  have hu := (BinaryReflectedPreparationMeasured.prepare_bounds input source hC hR hCase s hs hH).2
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells at hu
  omega

end Blotto.BinaryReflectedPreparationArithmeticEntryWork
