import Blotto.BinaryFourPreparationArithmeticEntryWork
import Blotto.BinaryFourGluingDrawMeasured

/-! Actual shared parameters feed both parent factories; actual returned
parents feed every overlap slot and the complete gluing draw. Entry helper
premises are discharged internally at each callback boundary. -/
namespace Blotto.BinaryGluingArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryStoredOverlapEnvironment (Segment)
open BinaryExpressionArithmeticEntryWork (tableCost build_bound)
open BinaryThreeFactoryArithmeticEntryWork (compiledCost compiled_bound)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def parents (input : BinaryFourParameters.Input) : ℕ :=
  let parameters := BinaryFourParametersMeasured.prepare input
  BinaryFourPreparationArithmeticEntryWork.parameters input+
    BinaryThreeFactoryArithmeticEntryWork.descriptor (BinaryFourParentCompiler.firstInput input parameters.1.1)+
    BinaryThreeFactoryArithmeticEntryWork.descriptor (BinaryFourParentCompiler.secondInput input parameters.1.1)

theorem parents_bound (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    parents input ≤ 2*listCells (BinaryFourGluingParentsMeasured.run input hC).1.2 := by
  have hp := BinaryFourPreparationArithmeticEntryWork.parameters_bound input
  have hf := BinaryThreeFactoryArithmeticEntryWork.descriptor_bound
    (BinaryFourParentCompiler.firstInput input (BinaryFourParametersMeasured.prepare input).1.1)
  have hs := BinaryThreeFactoryArithmeticEntryWork.descriptor_bound
    (BinaryFourParentCompiler.secondInput input (BinaryFourParametersMeasured.prepare input).1.1)
  simp only [parents,BinaryFourGluingParentsMeasured.run_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def fromEnvironment (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ) : ℕ :=
  compiledCost env.1.1 BinaryOverlapCompilerBridge.weight+
    tableCost 4 (fun r => compiledCost env.1.1 (BinaryOverlapCompilerBridge.safeP r))+
    tableCost 4 (fun r => compiledCost env.1.1 (BinaryOverlapCompilerBridge.safeQ r))

theorem fromEnvironment_bound (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ) :
    fromEnvironment env ≤ 2*listCells (BinaryOverlapGluingMeasured.fromEnvironment env).1.2 := by
  have hw := compiled_bound env.1.1 BinaryOverlapCompilerBridge.weight
  have hp := build_bound 4 (fun r => BinaryQuadraticSyntaxMeasured.run env.1.1 (BinaryOverlapCompilerBridge.safeP r))
    (fun r => compiledCost env.1.1 (BinaryOverlapCompilerBridge.safeP r)) (fun r => compiled_bound _ _)
  have hq := build_bound 4 (fun r => BinaryQuadraticSyntaxMeasured.run env.1.1 (BinaryOverlapCompilerBridge.safeQ r))
    (fun r => compiledCost env.1.1 (BinaryOverlapCompilerBridge.safeQ r)) (fun r => compiled_bound _ _)
  simp only [fromEnvironment,BinaryOverlapGluingMeasured.fromEnvironment_record,BinaryOverlapGluingMeasured.collect,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def slot {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) : ℕ :=
  fromEnvironment (BinaryOverlapGluingMeasured.environment first second interval budget i j)

theorem slot_bound {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) :
    slot first second interval budget i j ≤ 2*listCells (BinaryOverlapGluingMeasured.slot first second interval budget i j).1.2 := by
  rw [BinaryOverlapGluingMeasured.slot_record]
  exact (
    fromEnvironment_bound _
  )

def overlap {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h) (interval budget : SignedWord) : ℕ :=
  tableCost (k*h) (fun index =>
    let pair := finProdFinEquiv.symm index
    slot first second interval budget pair.1 pair.2)

theorem overlap_bound {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h) (interval budget : SignedWord) :
    overlap first second interval budget ≤ 2*listCells (BinaryOverlapGluingMeasured.descriptor first second interval budget).1.2 := by
  have hs := build_bound (k*h) (fun index =>
      let pair := finProdFinEquiv.symm index
      BinaryOverlapGluingMeasured.slot first second interval budget pair.1 pair.2)
    (fun index =>
      let pair := finProdFinEquiv.symm index
      slot first second interval budget pair.1 pair.2) (fun index => slot_bound _ _ _ _ _ _)
  dsimp only at hs
  simp only [overlap,BinaryOverlapGluingMeasured.descriptor_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def factory (input : BinaryFourParameters.Input) (hC : input.Canonical) : ℕ :=
  let produced := BinaryFourGluingParentsMeasured.run input hC
  parents input+overlap produced.1.1.2.1 produced.1.1.2.2 (produced.1.1.1.read 1) input.B

theorem factory_bound (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    factory input hC ≤ 2*listCells (BinaryFourGluingMeasured.descriptor input hC).1.2 := by
  have hp := parents_bound input hC
  have ho := overlap_bound (BinaryFourGluingParentsMeasured.run input hC).1.1.2.1
    (BinaryFourGluingParentsMeasured.run input hC).1.1.2.2
    ((BinaryFourGluingParentsMeasured.run input hC).1.1.1.read 1) input.B
  simp only [factory,BinaryFourGluingMeasured.descriptor_record,BinaryFourGluingMeasured.collect,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem prepared_bound (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryGluingSampler.Admissible input) :
    factory input hC ≤ 2*listCells (BinaryFourGluingDrawMeasured.prepared input hC hAd).1.2 := by
  rw [BinaryFourGluingDrawMeasured.prepared_record]
  exact (
    factory_bound input hC
  )

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  let held := BinaryFourGluingDrawMeasured.prepared input hC hAd
  factory input hC+BinaryCategoricalArithmeticEntryWork.segment store held.1.1 0 K scalar pc hp

theorem run_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    run store input hC hAd K scalar pc hp ≤
      2*listCells (BinaryFourGluingDrawMeasured.run store input hC hAd K scalar pc hp).1.2 := by
  have hf := prepared_bound input hC hAd
  have hd := BinaryCategoricalArithmeticEntryWork.segment_bound store (BinaryFourGluingDrawMeasured.prepared input hC hAd).1.1 0 K scalar pc hp
  simp only [run,BinaryFourGluingDrawMeasured.run_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

end Blotto.BinaryGluingArithmeticEntryWork
