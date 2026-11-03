import Blotto.BinaryThreeFactoryArithmeticEntryWork
import Blotto.BinaryWordGroupCompleteMeasured

/-! Complete uniform and mixed-two entry accounting follows actual descriptor
factories, categorical/point draws, optional rows and route emission. All helper
bounds are instantiated with concrete producers and returned data. -/
namespace Blotto.BinaryGroupArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers
set_option autoImplicit false
set_option maxHeartbeats 5000000

def uniformDraw {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  let prepared := BinaryGroupFactoryMeasured.uniformPrepared input hC hAd hm
  BinaryThreeFactoryArithmeticEntryWork.uniformFactory input hm+
    BinaryCategoricalArithmeticEntryWork.segment store prepared.1.1 0 K scalar pc hp

theorem uniformDraw_bound {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    uniformDraw store input hC hAd hm K scalar pc hp ≤ 2*listCells (BinaryWordGroupDrawMeasured.uniformRun store input hC hAd hm K scalar pc hp).1.2 := by
  let prepared := BinaryGroupFactoryMeasured.uniformPrepared input hC hAd hm
  have hf := BinaryThreeFactoryArithmeticEntryWork.uniformPrepared_bound input hC hAd hm
  have hd := BinaryCategoricalArithmeticEntryWork.segment_bound store prepared.1.1 0 K scalar pc hp
  dsimp only [prepared] at hd
  simp only [uniformDraw,BinaryWordGroupDrawMeasured.uniformRun_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def mixedTwoDraw (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  let prepared := BinaryGroupFactoryMeasured.mixedTwoPrepared input hC hAd
  BinaryThreeFactoryArithmeticEntryWork.descriptor (mixedThree input)+
    BinaryCategoricalArithmeticEntryWork.segment store prepared.1.1 0 K scalar pc hp

theorem mixedTwoDraw_bound (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    mixedTwoDraw store input hC hAd K scalar pc hp ≤ 2*listCells (BinaryWordGroupDrawMeasured.mixedTwoRun store input hC hAd K scalar pc hp).1.2 := by
  let prepared := BinaryGroupFactoryMeasured.mixedTwoPrepared input hC hAd
  have hf := BinaryThreeFactoryArithmeticEntryWork.mixedTwoPrepared_bound input hC hAd
  have hd := BinaryCategoricalArithmeticEntryWork.segment_bound store prepared.1.1 0 K scalar pc hp
  dsimp only [prepared] at hd
  simp only [mixedTwoDraw,BinaryWordGroupDrawMeasured.mixedTwoRun_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def emitOption {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) :
    Option (FixedArrayTable m SignedWord) → ℕ
  | none => 0
  | some row => BinaryExpressionArithmeticEntryWork.emit routes row

theorem emitOption_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (rows : Option (FixedArrayTable m SignedWord)) :
    emitOption routes rows ≤ 2*listCells (BinaryGroupEmissionMeasured.emitOption routes rows).1.2 := by
  cases rows with
  | none => simp only [emitOption,BinaryGroupEmissionMeasured.emitOption_record,wrap,combine,listCells]; omega
  | some row =>
      have h := BinaryExpressionArithmeticEntryWork.emit_bound routes row
      simp only [emitOption,BinaryGroupEmissionMeasured.emitOption_record,wrap,combine,listCells_append,listCells_under,listCells]
      omega

def emitMixedOption {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) :
    Option (FixedArrayTable (m+1) SignedWord) → ℕ
  | none => 0
  | some row => BinaryExpressionArithmeticEntryWork.mixed routes pivot row

theorem emitMixedOption_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (rows : Option (FixedArrayTable (m+1) SignedWord)) :
    emitMixedOption routes pivot rows ≤ 2*listCells (BinaryGroupEmissionMeasured.emitMixedOption routes pivot rows).1.2 := by
  cases rows with
  | none => simp only [emitMixedOption,BinaryGroupEmissionMeasured.emitMixedOption_record,wrap,combine,listCells]; omega
  | some row =>
      have h := BinaryExpressionArithmeticEntryWork.mixed_bound routes pivot row
      simp only [emitMixedOption,BinaryGroupEmissionMeasured.emitMixedOption_record,wrap,combine,listCells_append,listCells_under,listCells]
      omega

def uniformRun {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m=2 ∨ m=3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  let drawn := BinaryWordGroupDrawMeasured.uniformRun store input hC hAd hm K scalar pc hp
  uniformDraw store input hC hAd hm K scalar pc hp+emitOption routes drawn.1.1.1

theorem uniformRun_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m=2 ∨ m=3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    uniformRun store input hC hAd hm routes K scalar pc hp ≤
      2*listCells (BinaryWordGroupCompleteMeasured.uniformRun store input hC hAd hm routes K scalar pc hp).1.2 := by
  have hd := uniformDraw_bound store input hC hAd hm K scalar pc hp
  have he := emitOption_bound routes (BinaryWordGroupDrawMeasured.uniformRun store input hC hAd hm K scalar pc hp).1.1.1
  simp only [uniformRun,BinaryWordGroupCompleteMeasured.uniformRun_record,BinaryWordGroupCompleteMeasured.collect,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def mixedTwoRun {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  let drawn := BinaryWordGroupDrawMeasured.mixedTwoRun store input hC hAd K scalar pc hp
  mixedTwoDraw store input hC hAd K scalar pc hp+emitMixedOption routes pivot drawn.1.1.1

theorem mixedTwoRun_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    mixedTwoRun store input hC hAd routes pivot K scalar pc hp ≤
      2*listCells (BinaryWordGroupCompleteMeasured.mixedTwoRun store input hC hAd routes pivot K scalar pc hp).1.2 := by
  have hd := mixedTwoDraw_bound store input hC hAd K scalar pc hp
  have he := emitMixedOption_bound routes pivot (BinaryWordGroupDrawMeasured.mixedTwoRun store input hC hAd K scalar pc hp).1.1.1
  simp only [mixedTwoRun,BinaryWordGroupCompleteMeasured.mixedTwoRun_record,BinaryWordGroupCompleteMeasured.afterMixed_record,
    BinaryWordGroupCompleteMeasured.collect,wrap,combine,listCells_append,listCells_under,listCells]
  omega

end Blotto.BinaryGroupArithmeticEntryWork
