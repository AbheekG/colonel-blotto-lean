import Blotto.BinaryFourPreparationArithmeticEntryWork
import Blotto.BinaryFourSmallUniformDrawMeasured

/-! Entry charges follow actual small-uniform scale operands, merged child,
five-opcode endpoint splitting, returned descriptor and categorical/point draw.
The zero-total division keeps the existing opcode behavior. -/
namespace Blotto.BinarySmallUniformArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryExpressionArithmeticEntryWork (quadratic_bound tableCost build_bound)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def splitArithmetic (first second coordinate : SignedWord) : ℕ :=
  let total := BinaryQuadraticMeasured.apply .add first second
  let low := BinaryQuadraticMeasured.apply .div first total.1.1
  let high := BinaryQuadraticMeasured.apply .div second total.1.1
  let left := BinaryQuadraticMeasured.apply .mul low.1.1 coordinate
  let right := BinaryQuadraticMeasured.apply .mul high.1.1 coordinate
  BinaryArithmeticEntryWork.raw .add first second+
    BinaryArithmeticEntryWork.raw .div first total.1.1+
    BinaryArithmeticEntryWork.raw .div second total.1.1+
    BinaryArithmeticEntryWork.raw .mul low.1.1 coordinate+
    BinaryArithmeticEntryWork.raw .mul high.1.1 coordinate

theorem splitArithmetic_bound (first second coordinate : SignedWord) :
    splitArithmetic first second coordinate ≤ 2*listCells (BinarySmallUniformSplitMeasured.arithmetic first second coordinate).1.2 := by
  let total := BinaryQuadraticMeasured.apply .add first second
  let low := BinaryQuadraticMeasured.apply .div first total.1.1
  let high := BinaryQuadraticMeasured.apply .div second total.1.1
  let left := BinaryQuadraticMeasured.apply .mul low.1.1 coordinate
  let right := BinaryQuadraticMeasured.apply .mul high.1.1 coordinate
  have h0 := quadratic_bound .add first second
  have h1 := quadratic_bound .div first total.1.1
  have h2 := quadratic_bound .div second total.1.1
  have h3 := quadratic_bound .mul low.1.1 coordinate
  have h4 := quadratic_bound .mul high.1.1 coordinate
  dsimp only [total,low,high,left,right] at h0 h1 h2 h3 h4
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,splitArithmetic,BinarySmallUniformSplitMeasured.arithmetic_record,BinarySmallUniformSplitMeasured.joinArithmetic,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem split_bound (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) :
    splitArithmetic first second (row.read 0) ≤ 2*listCells (BinarySmallUniformSplitMeasured.split first second row).1.2 := by
  have h := splitArithmetic_bound first second (row.read 0)
  simp only [BinarySmallUniformSplitMeasured.split_record,BinarySmallUniformSplitMeasured.collect,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def preparation (input : BinaryFourParameters.Input) : ℕ :=
  let parameters := BinaryFourParametersMeasured.prepare input
  BinaryFourPreparationArithmeticEntryWork.parameters input+
    BinaryArithmeticEntryWork.raw .mul (parameters.1.1.read 5) input.u+
    BinaryArithmeticEntryWork.raw .mul (parameters.1.1.read 5) input.v+
    BinaryArithmeticEntryWork.raw .mul (parameters.1.1.read 5) input.w

theorem preparation_bound (input : BinaryFourParameters.Input) :
    preparation input ≤ 2*listCells (BinarySmallUniformPreparationMeasured.prepare input).1.2 := by
  have hp := BinaryFourPreparationArithmeticEntryWork.parameters_bound input
  have hf := quadratic_bound .mul ((BinaryFourParametersMeasured.prepare input).1.1.read 5) input.u
  have hs := quadratic_bound .mul ((BinaryFourParametersMeasured.prepare input).1.1.read 5) input.v
  have ht := quadratic_bound .mul ((BinaryFourParametersMeasured.prepare input).1.1.read 5) input.w
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,preparation,BinarySmallUniformPreparationMeasured.prepare_record,BinarySmallUniformPreparationMeasured.collect,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def child (input : BinarySmallUniformCompiler.Input) : ℕ := BinaryArithmeticEntryWork.raw .add input.l0 input.l1

theorem child_bound (input : BinarySmallUniformCompiler.Input) :
    child input ≤ 2*listCells (BinarySmallUniformDescriptorMeasured.child input).1.2 := by
  have h := quadratic_bound .add input.l0 input.l1
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,child,BinarySmallUniformDescriptorMeasured.child_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def descriptor (input : BinarySmallUniformCompiler.Input) : ℕ :=
  let merged := BinarySmallUniformDescriptorMeasured.child input
  let table := BinaryThreeFactoryMeasured.descriptor merged.1.1
  child input+BinaryThreeFactoryArithmeticEntryWork.descriptor merged.1.1+
    tableCost 9 (fun slot => splitArithmetic input.l0 input.l1 ((table.1.1.P.read slot).read 0))+
    tableCost 9 (fun slot => splitArithmetic input.l0 input.l1 ((table.1.1.Q.read slot).read 0))

theorem descriptor_bound (input : BinarySmallUniformCompiler.Input) :
    descriptor input ≤ 2*listCells (BinarySmallUniformDescriptorMeasured.descriptor input).1.2 := by
  let merged := BinarySmallUniformDescriptorMeasured.child input
  let table := BinaryThreeFactoryMeasured.descriptor merged.1.1
  have hm := child_bound input
  have ht := BinaryThreeFactoryArithmeticEntryWork.descriptor_bound merged.1.1
  have hp := build_bound 9 (fun slot => BinarySmallUniformSplitMeasured.split input.l0 input.l1 (table.1.1.P.read slot))
    (fun slot => splitArithmetic input.l0 input.l1 ((table.1.1.P.read slot).read 0)) (fun slot => split_bound _ _ _)
  have hq := build_bound 9 (fun slot => BinarySmallUniformSplitMeasured.split input.l0 input.l1 (table.1.1.Q.read slot))
    (fun slot => splitArithmetic input.l0 input.l1 ((table.1.1.Q.read slot).read 0)) (fun slot => split_bound _ _ _)
  dsimp only [table,merged] at ht hp hq
  simp only [descriptor,BinarySmallUniformDescriptorMeasured.descriptor_record,BinarySmallUniformDescriptorMeasured.assemble,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def factory (input : BinaryFourParameters.Input) : ℕ :=
  preparation input+descriptor (BinarySmallUniformPreparationMeasured.prepare input).1.1

theorem factory_bound (input : BinaryFourParameters.Input) :
    factory input ≤ 2*listCells (BinarySmallUniformFactoryMeasured.descriptor input).1.2 := by
  have hp := preparation_bound input
  have hd := descriptor_bound (BinarySmallUniformPreparationMeasured.prepare input).1.1
  simp only [factory,BinarySmallUniformFactoryMeasured.descriptor_record,BinarySmallUniformFactoryMeasured.collect,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem prepared_bound (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) :
    factory input ≤ 2*listCells (BinaryFourSmallUniformDrawMeasured.prepared input hC hAd).1.2 := by
  rw [BinaryFourSmallUniformDrawMeasured.prepared_record]
  exact (
    factory_bound input
  )

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  let held := BinaryFourSmallUniformDrawMeasured.prepared input hC hAd
  factory input+BinaryCategoricalArithmeticEntryWork.segment store held.1.1 0 K scalar pc hp

theorem run_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    run store input hC hAd K scalar pc hp ≤
      2*listCells (BinaryFourSmallUniformDrawMeasured.run store input hC hAd K scalar pc hp).1.2 := by
  have hf := prepared_bound input hC hAd
  have hd := BinaryCategoricalArithmeticEntryWork.segment_bound store (BinaryFourSmallUniformDrawMeasured.prepared input hC hAd).1.1 0 K scalar pc hp
  simp only [run,BinaryFourSmallUniformDrawMeasured.run_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

end Blotto.BinarySmallUniformArithmeticEntryWork
