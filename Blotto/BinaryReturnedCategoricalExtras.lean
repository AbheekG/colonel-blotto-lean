import Blotto.BinaryReturnedInterpolationExtras
import Blotto.BinaryWordSegmentFixedMeasured
import Blotto.BinaryWordGroupDrawMeasured

/-! Actual normalization extras for categorical preparation, reached coin
selection, deterministic fallback and segment/group draws. These bounds price
normalization division/emission plus the preceding source-work component.
Group fields cover the draw only: factory normalization, metadata evaluation
and full native/physical costs remain separate. -/
namespace Blotto.BinaryReturnedCategoricalExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryCategoricalPreparation BinaryCategoricalRun BinaryCategoricalUnitLattice
open BinaryStoredSegmentProgram BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork
set_option autoImplicit false
set_option maxHeartbeats 3500000
attribute [local irreducible] BinaryNormalizedCoordinate.opcode

theorem sum_bound {α : Type*} (items : List (α × SignedWord)) :
    (BinaryQuadraticCategoricalMeasured.sumWithExtras items).2 ≤
      155*(BinaryQuadraticCategoricalMeasured.sumWithExtras items).1.2 := by
  induction items with
  | nil => simp only [BinaryQuadraticCategoricalMeasured.sumWithExtras]; omega
  | cons item rest ih =>
      have h := BinaryNormalizationExtraWork.opcode_bound .add item.2
        (BinaryQuadraticCategoricalMeasured.sumWithExtras rest).1.1.1
      simp only [BinaryQuadraticCategoricalMeasured.sumWithExtras]
      omega

theorem prepare_bound {α : Type*} (fallback : α) (weights : WeightList α) :
    (BinaryQuadraticCategoricalMeasured.prepareWithExtras fallback weights).2 ≤
      155*(BinaryQuadraticCategoricalMeasured.prepareWithExtras fallback weights).1.2 := by
  have hSum := sum_bound weights.items
  cases weights with
  | mk items hc hn => cases items with
    | nil => dsimp only [BinaryQuadraticCategoricalMeasured.prepareWithExtras]; omega
    | cons head rest => cases rest with
      | nil => dsimp only [BinaryQuadraticCategoricalMeasured.prepareWithExtras]; omega
      | cons next tail =>
          have hOp := BinaryNormalizationExtraWork.opcode_bound .div head.2
            (BinaryQuadraticCategoricalMeasured.sumWithExtras (head::next::tail)).1.1.1
          dsimp only at hSum
          dsimp only [BinaryQuadraticCategoricalMeasured.prepareWithExtras]
          split <;> dsimp only <;> omega

theorem categorical_bound {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordCategoricalMeasured.runWithExtras store fallback weights pc hp).2 ≤
      155*(BinaryWordCategoricalMeasured.runWithExtras store fallback weights pc hp).1.2 := by
  have hPrep := prepare_bound fallback weights
  rw [BinaryWordCategoricalMeasured.runWithExtras]
  dsimp only
  cases hs : (BinaryQuadraticCategoricalMeasured.prepareWithExtras fallback weights).1.1.1 with
  | done selected => dsimp only; omega
  | ask choice =>
      dsimp only
      cases hc : (BinaryWordCoinMeasured.sample store choice.probability pc hp).1.1.1 with
      | none => dsimp only; omega
      | some branch =>
          cases branch
          · dsimp only
            have hLater := categorical_bound store fallback choice.rest
              (BinaryWordCoinMeasured.sample store choice.probability pc hp).1.1.2
              (BinaryWordCoinMeasured.sample_position store choice.probability pc hp).2
            omega
          · dsimp only; omega
termination_by weights.items.length
decreasing_by
  have hw := BinaryQuadraticCategoricalMeasured.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

theorem choose_bound {α : Type*} (fallback : α) (weights : WeightList α) :
    (BinaryCategoricalLowerMeasured.chooseWithExtras fallback weights).2 ≤
      155*(BinaryCategoricalLowerMeasured.chooseWithExtras fallback weights).1.2 := by
  have hPrep := prepare_bound fallback weights
  rw [BinaryCategoricalLowerMeasured.chooseWithExtras]
  dsimp only
  cases hs : (BinaryQuadraticCategoricalMeasured.prepareWithExtras fallback weights).1.1.1 with
  | done selected => dsimp only; omega
  | ask choice =>
      dsimp only
      have hLater := choose_bound fallback choice.rest
      omega
termination_by weights.items.length
decreasing_by
  have hw := BinaryQuadraticCategoricalMeasured.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

theorem lower_segment_bound {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) :
    (BinaryCategoricalLowerMeasured.segmentWithExtras prepared fallback).2 ≤
      155*(BinaryCategoricalLowerMeasured.segmentWithExtras prepared fallback).1.2 := by
  have h := choose_bound fallback (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)
  dsimp only [BinaryCategoricalLowerMeasured.segmentWithExtras]
  omega

theorem select_bound {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordSegmentMeasured.selectWithExtras store prepared fallback pc hp).2 ≤
      155*(BinaryWordSegmentMeasured.selectWithExtras store prepared fallback pc hp).1.2 := by
  have h := categorical_bound store fallback (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp
  dsimp only [BinaryWordSegmentMeasured.selectWithExtras]
  omega

theorem segment_bound {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordSegmentMeasured.runWithExtras store prepared fallback K scalar pc hp).2 ≤
      155*(BinaryWordSegmentMeasured.runWithExtras store prepared fallback K scalar pc hp).1.2 := by
  have hSelected := select_bound store prepared fallback pc hp
  dsimp only [BinaryWordSegmentMeasured.runWithExtras]
  cases hs : (BinaryWordSegmentMeasured.selectWithExtras store prepared fallback pc hp).1.1.1.1 with
  | none => dsimp only; omega
  | some slot =>
      dsimp only
      have hPoint := BinaryReturnedInterpolationExtras.sample_bound prepared.table slot K scalar
      omega

theorem lower_bound {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) :
    (BinaryWordSegmentFixedMeasured.lowerWithExtras prepared fallback K scalar).2 ≤
      155*(BinaryWordSegmentFixedMeasured.lowerWithExtras prepared fallback K scalar).1.2 := by
  have hSelected := lower_segment_bound prepared fallback
  have hPoint := BinaryReturnedInterpolationExtras.sample_bound prepared.table
    (BinaryCategoricalLowerMeasured.segmentWithExtras prepared fallback).1.1.1 K scalar
  dsimp only [BinaryWordSegmentFixedMeasured.lowerWithExtras]
  omega

theorem fixed_bound {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordSegmentFixedMeasured.runWithExtras store prepared fallback K scalar pc hp).2 ≤
      155*(BinaryWordSegmentFixedMeasured.runWithExtras store prepared fallback K scalar pc hp).1.2 := by
  have hDraw := segment_bound store prepared fallback K scalar pc hp
  dsimp only [BinaryWordSegmentFixedMeasured.runWithExtras]
  cases hs : (BinaryWordSegmentMeasured.runWithExtras store prepared fallback K scalar pc hp).1.1.1.1 with
  | some row => dsimp only; omega
  | none =>
      dsimp only
      have hLower := lower_bound prepared fallback K scalar
      omega

theorem uniform_draw_bound {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupDrawMeasured.uniformRunWithDrawExtras store input hC hAd hm K scalar pc hp).2 ≤
      155*(BinaryWordGroupDrawMeasured.uniformRunWithDrawExtras store input hC hAd hm K scalar pc hp).1.2 := by
  have h := segment_bound store (BinaryGroupFactoryMeasured.uniformPrepared input hC hAd hm).1.1 0 K scalar pc hp
  simp only [BinaryWordGroupDrawMeasured.uniformRunWithDrawExtras_record]
  omega

theorem mixed_draw_bound (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupDrawMeasured.mixedTwoRunWithDrawExtras store input hC hAd K scalar pc hp).2 ≤
      155*(BinaryWordGroupDrawMeasured.mixedTwoRunWithDrawExtras store input hC hAd K scalar pc hp).1.2 := by
  have h := segment_bound store (BinaryGroupFactoryMeasured.mixedTwoPrepared input hC hAd).1.1 0 K scalar pc hp
  simp only [BinaryWordGroupDrawMeasured.mixedTwoRunWithDrawExtras_record]
  omega

theorem sum_price {α : Type*} (D : ℕ) (hD : 0 < D) (weights : WeightList α) (hUnit : UnitLattice D weights) :
    (BinaryQuadraticCategoricalMeasured.sumWithExtras weights.items).1.2+(BinaryQuadraticCategoricalMeasured.sumWithExtras weights.items).2 ≤
      156*(weights.items.length*BinaryQuadraticCategoricalMeasured.sumStepPrice D+4) := by
  have h := sum_bound weights.items
  have hw := BinaryQuadraticCategoricalMeasured.sum_work D hD weights hUnit
  simp only [BinaryQuadraticCategoricalMeasured.sumWithExtras_compat] at h ⊢
  omega

theorem prepare_price {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (fallback : α) (weights : WeightList α)
    (hUnit : UnitLattice D weights) (hLength : weights.items.length ≤ M) :
    (BinaryQuadraticCategoricalMeasured.prepareWithExtras fallback weights).1.2+(BinaryQuadraticCategoricalMeasured.prepareWithExtras fallback weights).2 ≤
      156*(BinaryQuadraticCategoricalMeasured.preparationPrice D M) := by
  have h := prepare_bound fallback weights
  have hw := BinaryQuadraticCategoricalMeasured.prepare_work D hD M fallback weights hUnit hLength
  simp only [BinaryQuadraticCategoricalMeasured.prepareWithExtras_compat] at h ⊢
  omega

theorem categorical_price {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (store : BinarySeedLookupTree.Store)
    (fallback : α) (weights : WeightList α) (hUnit : UnitLattice D weights) (hLength : weights.items.length ≤ M)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordCategoricalMeasured.runWithExtras store fallback weights pc hp).1.2+(BinaryWordCategoricalMeasured.runWithExtras store fallback weights pc hp).2 ≤
      156*((weights.items.length+1)*BinaryWordCategoricalMeasured.stepPrice D M store.width store.cap.value) := by
  have h := categorical_bound store fallback weights pc hp
  have hw := BinaryWordCategoricalMeasured.run_work D hD M store fallback weights hUnit hLength pc hp
  simp only [BinaryWordCategoricalMeasured.runWithExtras_compat] at h ⊢
  omega

theorem choose_price {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (fallback : α) (weights : WeightList α)
    (hUnit : UnitLattice D weights) (hLength : weights.items.length ≤ M) :
    (BinaryCategoricalLowerMeasured.chooseWithExtras fallback weights).1.2+(BinaryCategoricalLowerMeasured.chooseWithExtras fallback weights).2 ≤
      156*((weights.items.length+1)*BinaryCategoricalLowerMeasured.stepPrice D M) := by
  have h := choose_bound fallback weights
  have hw := BinaryCategoricalLowerMeasured.choose_work D hD M fallback weights hUnit hLength
  simp only [BinaryCategoricalLowerMeasured.chooseWithExtras_compat] at h ⊢
  omega

theorem lower_segment_price {n k : ℕ} (prepared : Prepared n k) (source : RationalSegmentLottery n k)
    (hR : prepared.table.Refines source) (s : ℕ) (hHeight : ∀ slot,RationalHeight (source.weight slot) s) (fallback : Fin k) :
    (BinaryCategoricalLowerMeasured.segmentWithExtras prepared fallback).1.2+(BinaryCategoricalLowerMeasured.segmentWithExtras prepared fallback).2 ≤
      156*(BinaryCategoricalLowerMeasured.workEnvelope k s) := by
  have h := lower_segment_bound prepared fallback
  have hw := BinaryCategoricalLowerMeasured.segment_work prepared source hR s hHeight fallback
  simp only [BinaryCategoricalLowerMeasured.segmentWithExtras_compat] at h ⊢
  omega

theorem select_price {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hHeight : ∀ slot,RationalHeight (source.weight slot) s)
    (fallback : Fin k) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordSegmentMeasured.selectWithExtras store prepared fallback pc hp).1.2+(BinaryWordSegmentMeasured.selectWithExtras store prepared fallback pc hp).2 ≤
      156*(BinaryWordSegmentMeasured.selectionPrice k s store.width store.cap.value) := by
  have h := select_bound store prepared fallback pc hp
  have hw := BinaryWordSegmentMeasured.select_work store prepared source hR s hHeight fallback pc hp
  simp only [BinaryWordSegmentMeasured.selectWithExtras_compat] at h ⊢
  omega

theorem segment_price {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hWeight : ∀ slot,RationalHeight (source.weight slot) s)
    (hEndpoint : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordSegmentMeasured.runWithExtras store prepared fallback K scalar pc hp).1.2+(BinaryWordSegmentMeasured.runWithExtras store prepared fallback K scalar pc hp).2 ≤
      156*(BinaryWordSegmentMeasured.workEnvelope n k s K store.width store.cap.value) := by
  have h := segment_bound store prepared fallback K scalar pc hp
  have hw := BinaryWordSegmentMeasured.run_work store prepared source hR s hWeight hEndpoint fallback K scalar pc hp
  simp only [BinaryWordSegmentMeasured.runWithExtras_compat] at h ⊢
  omega

theorem lower_price {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (source : RationalSegmentLottery n k)
    (hR : prepared.table.Refines source) (s : ℕ) (hHeight : source.HeightAt s) (K : ℕ) (scalar : BinaryScalarTape K) :
    (BinaryWordSegmentFixedMeasured.lowerWithExtras prepared fallback K scalar).1.2+(BinaryWordSegmentFixedMeasured.lowerWithExtras prepared fallback K scalar).2 ≤
      156*(BinaryWordSegmentFixedMeasured.lowerPrice n k s K) := by
  have h := lower_bound prepared fallback K scalar
  have hw := BinaryWordSegmentFixedMeasured.lower_work prepared fallback source hR s hHeight K scalar
  simp only [BinaryWordSegmentFixedMeasured.lowerWithExtras_compat] at h ⊢
  omega

theorem fixed_price {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source) (s : ℕ) (hHeight : source.HeightAt s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordSegmentFixedMeasured.runWithExtras store prepared fallback K scalar pc hp).1.2+(BinaryWordSegmentFixedMeasured.runWithExtras store prepared fallback K scalar pc hp).2 ≤
      156*(BinaryWordSegmentFixedMeasured.workEnvelope n k s K store.width store.cap.value) := by
  have h := fixed_bound store prepared fallback K scalar pc hp
  have hw := BinaryWordSegmentFixedMeasured.run_work store prepared fallback source hR s hHeight K scalar pc hp
  simp only [BinaryWordSegmentFixedMeasured.runWithExtras_compat] at h ⊢
  omega

theorem uniform_draw_price {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupDrawMeasured.uniformRunWithDrawExtras store input hC hAd hm K scalar pc hp).1.2+(BinaryWordGroupDrawMeasured.uniformRunWithDrawExtras store input hC hAd hm K scalar pc hp).2 ≤
      156*(BinaryWordGroupDrawMeasured.uniformPrice m s K store.width store.cap.value) := by
  have h := uniform_draw_bound store input hC hAd hm K scalar pc hp
  have hw := BinaryWordGroupDrawMeasured.uniformRun_work store input hC hAd hm s hs hHeight K scalar pc hp
  simp only [BinaryWordGroupDrawMeasured.uniformRunWithDrawExtras_compat] at h ⊢
  omega

theorem mixed_draw_price (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordGroupDrawMeasured.mixedTwoRunWithDrawExtras store input hC hAd K scalar pc hp).1.2+(BinaryWordGroupDrawMeasured.mixedTwoRunWithDrawExtras store input hC hAd K scalar pc hp).2 ≤
      156*(BinaryWordGroupDrawMeasured.mixedPrice s K store.width store.cap.value) := by
  have h := mixed_draw_bound store input hC hAd K scalar pc hp
  have hw := BinaryWordGroupDrawMeasured.mixedTwoRun_work store input hC hAd s hs hHeight K scalar pc hp
  simp only [BinaryWordGroupDrawMeasured.mixedTwoRunWithDrawExtras_compat] at h ⊢
  omega

end Blotto.BinaryReturnedCategoricalExtras
