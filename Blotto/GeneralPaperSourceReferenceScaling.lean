import Blotto.GeneralPaperReferenceScaling

/-! Compositional positive reference-width scaling of the closed source-space
profile. Every lemma unfolds one existing profile and uses kernel-checked
scaling rules for its immediate children. No phase-space or growth oracle
and no additional algorithm pass is introduced. -/
namespace Blotto
open GeneralPaperReferenceScaling
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace GeneralPaperSparseNodeBits
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperGlobalNodeQuery
@[fun_prop]
theorem reference_scale_perNode (m lambda k Qv : ℕ) :
    Scale (fun W => perNode W m lambda k Qv) := by
  fun_prop [perNode]
end GeneralPaperSparseNodeBits

namespace GeneralPaperEncodedForestStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalCache
open GeneralPaperGlobalNodeQuery
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile (m lambda k Qv : ℕ) :
    Scale (fun W => profile W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperEncodedForestStorage

namespace GeneralPaperGridArrayConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_frames (n : ℕ) :
    Scale (fun W => frames W n) := by
  fun_prop [frames]
end GeneralPaperGridArrayConstructionStorage

namespace GeneralPaperInitialForestConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperIntervalCache
open scoped BigOperators
@[fun_prop]
theorem reference_scale_nodeProfile (height : ℕ) :
    Scale (fun W => nodeProfile W height) := by
  fun_prop [nodeProfile]
end GeneralPaperInitialForestConstructionStorage

namespace GeneralPaperInitialForestConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperIntervalCache
open scoped BigOperators
@[fun_prop]
theorem reference_scale_familyProfile (m height : ℕ) :
    Scale (fun W => familyProfile W m height) := by
  fun_prop [familyProfile]
end GeneralPaperInitialForestConstructionStorage

namespace GeneralPaperInitialForestConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperIntervalCache
open scoped BigOperators
@[fun_prop]
theorem reference_scale_returnedProfile (m lambda : ℕ) :
    Scale (fun W => returnedProfile W m lambda) := by
  fun_prop [returnedProfile]
end GeneralPaperInitialForestConstructionStorage

namespace GeneralPaperInitialForestConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperIntervalCache
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile (m lambda : ℕ) :
    Scale (fun W => profile W m lambda) := by
  fun_prop [profile]
end GeneralPaperInitialForestConstructionStorage

namespace GeneralPaperSourceLifetimeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_baseProfile (m lambda k : ℕ) :
    Scale (fun W => baseProfile W m lambda k) := by
  fun_prop [baseProfile]
end GeneralPaperSourceLifetimeStorage

namespace GeneralPaperBatchTraversalStorage
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalBatch
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_frameProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => frameProfile model W m lambda k Qv) := by
  fun_prop [frameProfile]
end GeneralPaperBatchTraversalStorage

namespace GeneralPaperInstructionConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperBatchTraversalStorage
open GeneralPaperCatalogueCellHistory GeneralPaperCatalogueOccurrenceHistory
@[fun_prop]
theorem reference_scale_frames (n : ℕ) :
    Scale (fun W => frames W n) := by
  fun_prop [frames]
end GeneralPaperInstructionConstructionStorage

namespace GeneralPaperEpochNodeConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalCache GeneralPaperCatalogueCellHistory
open GeneralPaperCatalogueEpochRun
@[fun_prop]
theorem reference_scale_instructionProfile (m lambda k Qv : ℕ) :
    Scale (fun W => instructionProfile W m lambda k Qv) := by
  fun_prop [instructionProfile]
end GeneralPaperEpochNodeConstructionStorage

namespace GeneralPaperRangeUpdateBitPrice
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalGeometry
open GeneralPaperRangeUpdateExecution GeneralPaperRangeGeometryPrice GeneralPaperGlobalNodeQuery
@[fun_prop]
theorem reference_scale_nodeProfile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => nodeProfile price W m lambda k Qv) := by
  fun_prop [nodeProfile]
end GeneralPaperRangeUpdateBitPrice

namespace GeneralPaperBatchUpdateBitPrice
open GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperIntervalBatch (Instruction effect)
open GeneralPaperBatchUpdateExecution
@[fun_prop]
theorem reference_scale_rootProfile (price : ℕ → ℕ) (m lambda k Qv height : ℕ) :
    Scale (fun W => rootProfile price W m lambda k Qv height) := by
  fun_prop [rootProfile]
end GeneralPaperBatchUpdateBitPrice

namespace GeneralPaperBatchUpdateBitPrice
open GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperIntervalBatch (Instruction effect)
open GeneralPaperBatchUpdateExecution
@[fun_prop]
theorem reference_scale_entryProfile (price : ℕ → ℕ) (m lambda k Qv height : ℕ) :
    Scale (fun W => entryProfile price W m lambda k Qv height) := by
  fun_prop [entryProfile]
end GeneralPaperBatchUpdateBitPrice

namespace GeneralPaperCellInstructionPrice
open GeneralPaperEpochCellInstructions GeneralPaperIntervalBatch
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (n : ℕ) :
    Scale (fun W => profile W n) := by
  fun_prop [profile]
end GeneralPaperCellInstructionPrice

namespace GeneralPaperEpochNodeUpdate
open GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueOccurrenceHistory
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => profile price W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperEpochNodeUpdate

namespace GeneralPaperForestConstructorOperands
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalCache
@[fun_prop]
theorem reference_scale_nodeProfile (m lambda k Qv : ℕ) :
    Scale (fun W => nodeProfile W m lambda k Qv) := by
  fun_prop [nodeProfile]
end GeneralPaperForestConstructorOperands

namespace GeneralPaperRangeQueryStorage
open GeneralPaperIntervalCache GeneralPaperIntervalLevels
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m lambda k Qv height : ℕ) :
    Scale (fun W => profile model W m lambda k Qv height) := by
  fun_prop [profile]
end GeneralPaperRangeQueryStorage

namespace GeneralPaperEpochNodeConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalCache GeneralPaperCatalogueCellHistory
open GeneralPaperCatalogueEpochRun
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => profile model W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperEpochNodeConstructionStorage

namespace GeneralPaperForestFamilyConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalCache
@[fun_prop]
theorem reference_scale_familyProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => familyProfile model W m lambda k Qv) := by
  fun_prop [familyProfile]
end GeneralPaperForestFamilyConstructionStorage

namespace GeneralPaperForestFamilyConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalCache
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m k Qv : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m k Qv a) := by
  fun_prop [profile]
end GeneralPaperForestFamilyConstructionStorage

namespace GeneralPaperEncodedPartitionStorage
@[fun_prop]
theorem reference_scale_profile (L B : ℕ) :
    Scale (fun W => profile W L B) := by
  fun_prop [profile]
end GeneralPaperEncodedPartitionStorage

namespace GeneralPaperEncodedSignedPlans
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_profile (L n k : ℕ) :
    Scale (fun W => profile W L n k) := by
  fun_prop [profile]
end GeneralPaperEncodedSignedPlans

namespace GeneralPaperEncodedCellPlans
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_signedProfile (L B k : ℕ) :
    Scale (fun W => signedProfile W L B k) := by
  fun_prop [signedProfile]
end GeneralPaperEncodedCellPlans

namespace GeneralPaperEncodedRankPlans
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_cdfProfile (n k : ℕ) :
    Scale (fun W => cdfProfile W n k) := by
  fun_prop [cdfProfile]
end GeneralPaperEncodedRankPlans

namespace GeneralPaperEncodedRankPlans
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_tailProfile (n k : ℕ) :
    Scale (fun W => tailProfile W n k) := by
  fun_prop [tailProfile]
end GeneralPaperEncodedRankPlans

namespace GeneralPaperEncodedRankPlans
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_lossProfile (n k : ℕ) :
    Scale (fun W => lossProfile W n k) := by
  fun_prop [lossProfile]
end GeneralPaperEncodedRankPlans

namespace GeneralPaperEncodedCellPlans
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_unsignedProfile (L B k : ℕ) :
    Scale (fun W => unsignedProfile W L B k) := by
  fun_prop [unsignedProfile]
end GeneralPaperEncodedCellPlans

namespace GeneralPaperEncodedFieldPlanStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_profile (lambda k : ℕ) :
    Scale (fun W => profile W lambda k) := by
  fun_prop [profile]
end GeneralPaperEncodedFieldPlanStorage

namespace GeneralPaperEncodedCatalogueStorage
@[fun_prop]
theorem reference_scale_innerProfile (K L : ℕ) :
    Scale (fun W => innerProfile W K L) := by
  fun_prop [innerProfile]
end GeneralPaperEncodedCatalogueStorage

namespace GeneralPaperEncodedCatalogueStorage
@[fun_prop]
theorem reference_scale_profile (m K L : ℕ) :
    Scale (fun W => profile W m K L) := by
  fun_prop [profile]
end GeneralPaperEncodedCatalogueStorage

namespace GeneralPaperEncodedOptimizerCache
open GeneralPaperCodeAlphabet
@[fun_prop]
theorem reference_scale_summaryProfile (m lambda k : ℕ) :
    Scale (fun W => summaryProfile W m lambda k) := by
  fun_prop [summaryProfile]
end GeneralPaperEncodedOptimizerCache

namespace GeneralPaperEncodedOptionCache
open GeneralPaperResponseTag
@[fun_prop]
theorem reference_scale_profile (L K k : ℕ) :
    Scale (fun W => profile W L K k) := by
  fun_prop [profile]
end GeneralPaperEncodedOptionCache

namespace GeneralPaperEncodedOptimizerCache
open GeneralPaperCodeAlphabet
@[fun_prop]
theorem reference_scale_profile (m lambda k : ℕ) :
    Scale (fun W => profile W m lambda k) := by
  fun_prop [profile]
end GeneralPaperEncodedOptimizerCache

namespace GeneralPaperEncodedEpochCache
open GeneralPaperCatalogueEpochCache
@[fun_prop]
theorem reference_scale_profile (m lambda k : ℕ) :
    Scale (fun W => profile W m lambda k) := by
  fun_prop [profile]
end GeneralPaperEncodedEpochCache

namespace GeneralPaperCachedCatalogueFamily
open GeneralPaperCodeAlphabet
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_entriesProfile (m : ℕ) :
    Scale (fun W => entriesProfile W m) := by
  fun_prop [entriesProfile]
end GeneralPaperCachedCatalogueFamily

namespace GeneralPaperCatalogueSlotsPrice
open GeneralPaperCodeAlphabet GeneralPaperCatalogueSlotsExecution
open GeneralPaperCodeMinimumScan (Entry)
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperDecodeBucketExecution (primitive)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (cap : ℕ) :
    Scale (fun W => profile model W cap) := by
  fun_prop [profile]
end GeneralPaperCatalogueSlotsPrice

namespace GeneralPaperDecoderControls
open GeneralPaperCodeAlphabet
@[fun_prop]
theorem reference_scale_controlWord (lambda : ℕ) :
    Scale (fun W => controlWord W lambda) := by
  fun_prop [controlWord]
end GeneralPaperDecoderControls

namespace GeneralPaperCellCataloguePrice
open GeneralPaperCodeAlphabet GeneralPaperCellCatalogueExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperCellCatalogueOperands (width)
open GeneralPaperDecodeBucketExecution (primitive)
@[fun_prop]
theorem reference_scale_queryProfile (model : RationalCostModel) (n : ℕ) (a : Alphabet) :
    Scale (fun W => queryProfile model W n a) := by
  fun_prop [queryProfile]
end GeneralPaperCellCataloguePrice

namespace GeneralPaperCellCataloguePrice
open GeneralPaperCodeAlphabet GeneralPaperCellCatalogueExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperCellCatalogueOperands (width)
open GeneralPaperDecodeBucketExecution (primitive)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (n : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W n a) := by
  fun_prop [profile]
end GeneralPaperCellCataloguePrice

namespace GeneralPaperCachedCataloguePrice
open GeneralPaperCodeAlphabet GeneralPaperCachedCatalogueExecution
open GeneralPaperDecodeBucketExecution (primitive)
@[fun_prop]
theorem reference_scale_finishProfile (model : RationalCostModel) (n : ℕ) (a : Alphabet) :
    Scale (fun W => finishProfile model W n a) := by
  fun_prop [finishProfile]
end GeneralPaperCachedCataloguePrice

namespace GeneralPaperCataloguePointPrice
open GeneralPaperCataloguePointExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (primitive : ℕ → ℕ) (n U : ℕ) :
    Scale (fun W => profile primitive W n U) := by
  fun_prop [profile]
end GeneralPaperCataloguePointPrice

namespace GeneralPaperPricedSort
@[fun_prop]
theorem reference_scale_profile (n P : ℕ) :
    Scale (fun W => profile n W P) := by
  fun_prop [profile]
end GeneralPaperPricedSort

namespace GeneralPaperNaturalOrderPrice
@[fun_prop]
theorem reference_scale_profile (n P : ℕ) :
    Scale (fun W => profile n W P) := by
  fun_prop [profile]
end GeneralPaperNaturalOrderPrice

namespace GeneralPaperBoundaryCellPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (primitive : ℕ → ℕ) (n : ℕ) :
    Scale (fun W => profile primitive W n) := by
  fun_prop [profile]
end GeneralPaperBoundaryCellPrice

namespace GeneralPaperPartitionAssemblyPrice
open GeneralPaperPartitionExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (primitive : ℕ → ℕ) (N : ℕ) :
    Scale (fun W => profile primitive W N) := by
  fun_prop [profile]
end GeneralPaperPartitionAssemblyPrice

namespace GeneralPaperPartitionPrice
open GeneralPaperPartitionExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (primitive : ℕ → ℕ) (N U : ℕ) :
    Scale (fun W => profile primitive W N U) := by
  fun_prop [profile]
end GeneralPaperPartitionPrice

namespace GeneralPaperCataloguePartitionPrice
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
@[fun_prop]
theorem reference_scale_profile (primitive : ℕ → ℕ) (n U : ℕ) :
    Scale (fun W => profile primitive W n U) := by
  fun_prop [profile]
end GeneralPaperCataloguePartitionPrice

namespace GeneralPaperCachedCataloguePrice
open GeneralPaperCodeAlphabet GeneralPaperCachedCatalogueExecution
open GeneralPaperDecodeBucketExecution (primitive)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (n : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W n a) := by
  fun_prop [profile]
end GeneralPaperCachedCataloguePrice

namespace GeneralPaperCachedCatalogueFamily
open GeneralPaperCodeAlphabet
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m n : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m n a) := by
  fun_prop [profile]
end GeneralPaperCachedCatalogueFamily

namespace GeneralPaperCatalogueProjection
open GeneralPaperCodeMinimumScan (Entry)
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_rowProfile (K : ℕ) :
    Scale (fun W => rowProfile W K) := by
  fun_prop [rowProfile]
end GeneralPaperCatalogueProjection

namespace GeneralPaperCatalogueProjection
open GeneralPaperCodeMinimumScan (Entry)
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_familyProfile (m K : ℕ) :
    Scale (fun W => familyProfile W m K) := by
  fun_prop [familyProfile]
end GeneralPaperCatalogueProjection

namespace GeneralPaperCatalogueProjection
open GeneralPaperCodeMinimumScan (Entry)
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (m K : ℕ) :
    Scale (fun W => profile W m K) := by
  fun_prop [profile]
end GeneralPaperCatalogueProjection

namespace GeneralPaperCatalogueArraysExecution
open GeneralPaperCodeAlphabet
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m n : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m n a) := by
  fun_prop [profile]
end GeneralPaperCatalogueArraysExecution

namespace GeneralPaperCatalogueTagFamily
open GeneralPaperCodeAlphabet
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_rowProfile (model : RationalCostModel) (K lambda : ℕ) :
    Scale (fun W => rowProfile model W K lambda) := by
  fun_prop [rowProfile]
end GeneralPaperCatalogueTagFamily

namespace GeneralPaperCatalogueTagFamily
open GeneralPaperCodeAlphabet
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m K lambda : ℕ) :
    Scale (fun W => profile model W m K lambda) := by
  fun_prop [profile]
end GeneralPaperCatalogueTagFamily

namespace GeneralPaperRankArrayPrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperRankArrayExecution
open GeneralPaperRankArrayOperands (width)
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_queryProfile (primitive : ℕ → ℕ) (m depth V : ℕ) :
    Scale (fun W => queryProfile primitive W m depth V) := by
  fun_prop [queryProfile]
end GeneralPaperRankArrayPrice

namespace GeneralPaperRankArrayPrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperRankArrayExecution
open GeneralPaperRankArrayOperands (width)
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (primitive : ℕ → ℕ) (m k V : ℕ) :
    Scale (fun W => profile primitive W m k V) := by
  fun_prop [profile]
end GeneralPaperRankArrayPrice

namespace GeneralPaperSignedCutPrice
open GeneralPaperSignedCutExecution
open GeneralPaperSignedCutOperands (width)
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (primitive : ℕ → ℕ) (m U : ℕ) :
    Scale (fun W => profile primitive W m U) := by
  fun_prop [profile]
end GeneralPaperSignedCutPrice

namespace GeneralPaperSignedTailPrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperSignedTailExecution
@[fun_prop]
theorem reference_scale_profile (primitive : ℕ → ℕ) (m k U : ℕ) :
    Scale (fun W => profile primitive W m k U) := by
  fun_prop [profile]
end GeneralPaperSignedTailPrice

namespace GeneralPaperOptionPlanFamily
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (primitive : ℕ → ℕ) (m K k U : ℕ) :
    Scale (fun W => profile primitive W m K k U) := by
  fun_prop [profile]
end GeneralPaperOptionPlanFamily

namespace GeneralPaperCatalogueOptimizerPreparation
open GeneralPaperCodeAlphabet
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperDecodeBucketExecution (primitive)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m k : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m k a) := by
  fun_prop [profile]
end GeneralPaperCatalogueOptimizerPreparation

namespace GeneralPaperCellRepresentativePrice
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperSignedCutOperands (magnitude width)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (n : ℕ) :
    Scale (fun W => profile price W n) := by
  fun_prop [profile]
end GeneralPaperCellRepresentativePrice

namespace GeneralPaperEpochPointPrice
open GeneralPaperEpochPointExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (n m U : ℕ) :
    Scale (fun W => profile price W n m U) := by
  fun_prop [profile]
end GeneralPaperEpochPointPrice

namespace GeneralPaperEpochPartitionPrice
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (n m U : ℕ) :
    Scale (fun W => profile price W n m U) := by
  fun_prop [profile]
end GeneralPaperEpochPartitionPrice

namespace GeneralPaperSignedCellExtrasPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperSignedCutOperands (magnitude width)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m U : ℕ) :
    Scale (fun W => profile price W m U) := by
  fun_prop [profile]
end GeneralPaperSignedCellExtrasPrice

namespace GeneralPaperSignedCellPositionsPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperSignedCutOperands (magnitude width)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (n U : ℕ) :
    Scale (fun W => profile price W n U) := by
  fun_prop [profile]
end GeneralPaperSignedCellPositionsPrice

namespace GeneralPaperSignedCellPartitionPrice
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (n m U : ℕ) :
    Scale (fun W => profile price W n m U) := by
  fun_prop [profile]
end GeneralPaperSignedCellPartitionPrice

namespace GeneralPaperCDFShiftPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperSignedCutOperands (magnitude width)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m U : ℕ) :
    Scale (fun W => profile price W m U) := by
  fun_prop [profile]
end GeneralPaperCDFShiftPrice

namespace GeneralPaperSignedPositionsPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperSignedCutOperands (magnitude width)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m U : ℕ) :
    Scale (fun W => profile price W m U) := by
  fun_prop [profile]
end GeneralPaperSignedPositionsPrice

namespace GeneralPaperSignedUpdatePrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperSignedUpdateExecution
open GeneralPaperSignedTailOperands (magnitude width)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m k U : ℕ) :
    Scale (fun W => profile price W m k U) := by
  fun_prop [profile]
end GeneralPaperSignedUpdatePrice

namespace GeneralPaperCellPlanPrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperCellPlanExecution
@[fun_prop]
theorem reference_scale_signedProfile (price : ℕ → ℕ) (m k U : ℕ) :
    Scale (fun W => signedProfile price W m k U) := by
  fun_prop [signedProfile]
end GeneralPaperCellPlanPrice

namespace GeneralPaperCDFPairPrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperCDFPairExecution
open GeneralPaperSignedTailOperands (magnitude width)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m k U : ℕ) :
    Scale (fun W => profile price W m k U) := by
  fun_prop [profile]
end GeneralPaperCDFPairPrice

namespace GeneralPaperQueryLossPrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperQueryLossExecution
open GeneralPaperSignedTailOperands (magnitude width)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m k U : ℕ) :
    Scale (fun W => profile price W m k U) := by
  fun_prop [profile]
end GeneralPaperQueryLossPrice

namespace GeneralPaperUnsignedCellInputPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperSignedCutOperands (magnitude width)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (n m U : ℕ) :
    Scale (fun W => profile price W n m U) := by
  fun_prop [profile]
end GeneralPaperUnsignedCellInputPrice

namespace GeneralPaperUnsignedCellPartitionPrice
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (n m U : ℕ) :
    Scale (fun W => profile price W n m U) := by
  fun_prop [profile]
end GeneralPaperUnsignedCellPartitionPrice

namespace GeneralPaperCellPlanPrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperCellPlanExecution
@[fun_prop]
theorem reference_scale_unsignedProfile (price : ℕ → ℕ) (m k U : ℕ) :
    Scale (fun W => unsignedProfile price W m k U) := by
  fun_prop [unsignedProfile]
end GeneralPaperCellPlanPrice

namespace GeneralPaperFieldPlanPreparation
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (mx my k U : ℕ) :
    Scale (fun W => profile price W mx my k U) := by
  fun_prop [profile]
end GeneralPaperFieldPlanPreparation

namespace GeneralPaperFieldPlanFamily
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m mx my k U : ℕ) :
    Scale (fun W => profile price W m mx my k U) := by
  fun_prop [profile]
end GeneralPaperFieldPlanFamily

namespace GeneralPaperEpochCachePreparation
open GeneralPaperCodeAlphabet
open GeneralPaperDecodeBucketExecution (primitive)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m k : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m k a) := by
  fun_prop [profile]
end GeneralPaperEpochCachePreparation

namespace GeneralPaperFieldFamilyConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m k : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m k a) := by
  fun_prop [profile]
end GeneralPaperFieldFamilyConstructionStorage

namespace GeneralPaperOptionPlanConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_tagRowProfile (K L : ℕ) :
    Scale (fun W => tagRowProfile W K L) := by
  fun_prop [tagRowProfile]
end GeneralPaperOptionPlanConstructionStorage

namespace GeneralPaperSignedTailStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_returnedProfile (n k U : ℕ) :
    Scale (fun W => returnedProfile W n k U) := by
  fun_prop [returnedProfile]
end GeneralPaperSignedTailStorage

namespace GeneralPaperOptionPlanConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_rowProfile (K k U L : ℕ) :
    Scale (fun W => rowProfile W K k U L) := by
  fun_prop [rowProfile]
end GeneralPaperOptionPlanConstructionStorage

namespace GeneralPaperRankConstructionStorage
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperEncodedScalarStorage GeneralPaperRankArrayExecution
@[fun_prop]
theorem reference_scale_frames (n depth : ℕ) :
    Scale (fun W => frames W n depth) := by
  fun_prop [frames]
end GeneralPaperRankConstructionStorage

namespace GeneralPaperRankConstructionStorage
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperEncodedScalarStorage GeneralPaperRankArrayExecution
@[fun_prop]
theorem reference_scale_queryProfile (model : RationalCostModel) (k V : ℕ) :
    Scale (fun W => queryProfile model W k V) := by
  fun_prop [queryProfile]
end GeneralPaperRankConstructionStorage

namespace GeneralPaperRankConstructionStorage
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperEncodedScalarStorage GeneralPaperRankArrayExecution
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (n k V : ℕ) :
    Scale (fun W => profile model W n k V) := by
  fun_prop [profile]
end GeneralPaperRankConstructionStorage

namespace GeneralPaperSignedCutStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSignedCutExecution
@[fun_prop]
theorem reference_scale_framePeak (m U : ℕ) :
    Scale (fun W => framePeak W m U) := by
  fun_prop [framePeak]
end GeneralPaperSignedCutStorage

namespace GeneralPaperSignedCutStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSignedCutExecution
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m U : ℕ) :
    Scale (fun W => profile model W m U) := by
  fun_prop [profile]
end GeneralPaperSignedCutStorage

namespace GeneralPaperSignedTailStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_rankProfile (n k U : ℕ) :
    Scale (fun W => rankProfile W n k U) := by
  fun_prop [rankProfile]
end GeneralPaperSignedTailStorage

namespace GeneralPaperSignedTailStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (n k U : ℕ) :
    Scale (fun W => profile model W n k U) := by
  fun_prop [profile]
end GeneralPaperSignedTailStorage

namespace GeneralPaperOptionPlanConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_rowWindowProfile (model : RationalCostModel) (K k U mesh L : ℕ) :
    Scale (fun W => rowWindowProfile model W K k U mesh L) := by
  fun_prop [rowWindowProfile]
end GeneralPaperOptionPlanConstructionStorage

namespace GeneralPaperOptionPlanConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m K k U mesh L : ℕ) :
    Scale (fun W => profile model W m K k U mesh L) := by
  fun_prop [profile]
end GeneralPaperOptionPlanConstructionStorage

namespace GeneralPaperTagFamilyStorage
open GeneralPaperCodeAlphabet
@[fun_prop]
theorem reference_scale_rowCapacity (K lambda : ℕ) :
    Scale (fun W => rowCapacity W K lambda) := by
  fun_prop [rowCapacity]
end GeneralPaperTagFamilyStorage

namespace GeneralPaperTagValueStorage
open GeneralPaperCodeAlphabet GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (lambda : ℕ) :
    Scale (fun W => profile model W lambda) := by
  fun_prop [profile]
end GeneralPaperTagValueStorage

namespace GeneralPaperTagFamilyStorage
open GeneralPaperCodeAlphabet
@[fun_prop]
theorem reference_scale_rowProfile (model : RationalCostModel) (K lambda : ℕ) :
    Scale (fun W => rowProfile model W K lambda) := by
  fun_prop [rowProfile]
end GeneralPaperTagFamilyStorage

namespace GeneralPaperTagFamilyStorage
open GeneralPaperCodeAlphabet
@[fun_prop]
theorem reference_scale_familyProfile (model : RationalCostModel) (m K lambda : ℕ) :
    Scale (fun W => familyProfile model W m K lambda) := by
  fun_prop [familyProfile]
end GeneralPaperTagFamilyStorage

namespace GeneralPaperReadyConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperCatalogueProjection (Field)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m k mesh : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m k mesh a) := by
  fun_prop [profile]
end GeneralPaperReadyConstructionStorage

namespace GeneralPaperEpochCacheConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m k mesh : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m k mesh a) := by
  fun_prop [profile]
end GeneralPaperEpochCacheConstructionStorage

namespace GeneralPaperSummaryFamilyStorage
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_summaryProfile (k height : ℕ) :
    Scale (fun W => summaryProfile W k height) := by
  fun_prop [summaryProfile]
end GeneralPaperSummaryFamilyStorage

namespace GeneralPaperFourSummaryConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
@[fun_prop]
theorem reference_scale_returnedFamilyProfile (m k height : ℕ) :
    Scale (fun W => returnedFamilyProfile W m k height) := by
  fun_prop [returnedFamilyProfile]
end GeneralPaperFourSummaryConstructionStorage

namespace GeneralPaperFourSummaryConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
@[fun_prop]
theorem reference_scale_returnedProfile (m lambda k : ℕ) :
    Scale (fun W => returnedProfile W m lambda k) := by
  fun_prop [returnedProfile]
end GeneralPaperFourSummaryConstructionStorage

namespace GeneralPaperQuantileSearchPrice
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
open GeneralPaperQuantileSearchExecution GeneralPaperSourcePreparationSizes
@[fun_prop]
theorem reference_scale_profile (primitive : ℕ → ℕ) (m lambda k Qv height : ℕ) :
    Scale (fun W => profile primitive W m lambda k Qv height) := by
  fun_prop [profile]
end GeneralPaperQuantileSearchPrice

namespace GeneralPaperQuantileTraversalStorage
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
open GeneralPaperQuantileDescent GeneralPaperQuantileRecordStorage
@[fun_prop]
theorem reference_scale_coefficient (m lambda k Qv : ℕ) :
    Scale (fun W => coefficient W m lambda k Qv) := by
  fun_prop [coefficient]
end GeneralPaperQuantileTraversalStorage

namespace GeneralPaperQuantileQueryStorage
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
open GeneralPaperSourcePreparationSizes
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m lambda k Qv height : ℕ) :
    Scale (fun W => profile model W m lambda k Qv height) := by
  fun_prop [profile]
end GeneralPaperQuantileQueryStorage

namespace GeneralPaperSummaryConstructionStorage
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
open GeneralPaperEncodedScalarStorage GeneralPaperSummaryArrayExecution
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m lambda k Qv height : ℕ) :
    Scale (fun W => profile model W m lambda k Qv height) := by
  fun_prop [profile]
end GeneralPaperSummaryConstructionStorage

namespace GeneralPaperSummaryFamilyStorage
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_frames (m : ℕ) :
    Scale (fun W => frames W m) := by
  fun_prop [frames]
end GeneralPaperSummaryFamilyStorage

namespace GeneralPaperSummaryFamilyStorage
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_familyProfile (m k height : ℕ) :
    Scale (fun W => familyProfile W m k height) := by
  fun_prop [familyProfile]
end GeneralPaperSummaryFamilyStorage

namespace GeneralPaperFourSummaryConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => profile model W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperFourSummaryConstructionStorage

namespace GeneralPaperTreeEpochConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueOccurrenceHistory
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m k Qv : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m k Qv a) := by
  fun_prop [profile]
end GeneralPaperTreeEpochConstructionStorage

namespace GeneralPaperActualEpochParentStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueTreeCache GeneralPaperCatalogueOccurrenceHistory
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m k Qv : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m k Qv a) := by
  fun_prop [profile]
end GeneralPaperActualEpochParentStorage

namespace GeneralPaperEncodedPreparedPowers
open GeneralPaperSourcePreparationSizes GeneralPaperEncodedScalarStorage
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable
@[fun_prop]
theorem reference_scale_profile (m lambda k Qv : ℕ) :
    Scale (fun W => profile W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperEncodedPreparedPowers

namespace GeneralPaperEncodedProfitGrid
open GeneralPaperEncodedScalarStorage GeneralPaperProfitGridPrepare GeneralPaperProfitGridPoints
@[fun_prop]
theorem reference_scale_profile (P w B : ℕ) :
    Scale (fun W => profile W P w B) := by
  fun_prop [profile]
end GeneralPaperEncodedProfitGrid

namespace GeneralPaperEncodedSharedParameters
open GeneralPaperEncodedScalarStorage GeneralPaperSourcePreparationSizes
@[fun_prop]
theorem reference_scale_preparedProfitProfile (m lambda k Qv : ℕ) :
    Scale (fun W => preparedProfitProfile W m lambda k Qv) := by
  fun_prop [preparedProfitProfile]
end GeneralPaperEncodedSharedParameters

namespace GeneralPaperEncodedNatArray
open scoped BigOperators
@[fun_prop]
theorem reference_scale_footprint {n : ℕ} (values : FixedArrayTable n ℕ) :
    Scale (fun W => footprint (n := n) W values) := by
  fun_prop [footprint]
end GeneralPaperEncodedNatArray

namespace GeneralPaperEncodedSharedSource
open GeneralPaperCatalogueShared GeneralPaperCodeAlphabet GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_inputFootprint {m : ℕ} (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => inputFootprint (m := m) W weights Bc Br) := by
  fun_prop [inputFootprint]
end GeneralPaperEncodedSharedSource

namespace GeneralPaperEncodedSharedSource
open GeneralPaperCatalogueShared GeneralPaperCodeAlphabet GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile {m : ℕ} (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => profile (m := m) W k Qv a weights Bc Br) := by
  fun_prop [profile]
end GeneralPaperEncodedSharedSource

namespace GeneralPaperEncodedEpochLevels
open GeneralPaperEpochFieldState
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
open scoped BigOperators
@[fun_prop]
theorem reference_scale_fieldProfile (m lambda k Qv : ℕ) :
    Scale (fun W => fieldProfile W m lambda k Qv) := by
  fun_prop [fieldProfile]
end GeneralPaperEncodedEpochLevels

namespace GeneralPaperEncodedEpochLevels
open GeneralPaperEpochFieldState
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile (m lambda k Qv : ℕ) :
    Scale (fun W => profile W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperEncodedEpochLevels

namespace GeneralPaperEncodedSnapshotStorage
open GeneralPaperEpochSnapshot GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueOccurrenceHistory
open scoped BigOperators
@[fun_prop]
theorem reference_scale_blockProfile (m lambda k Qv : ℕ) :
    Scale (fun W => blockProfile W m lambda k Qv) := by
  fun_prop [blockProfile]
end GeneralPaperEncodedSnapshotStorage

namespace GeneralPaperEncodedSnapshotStorage
open GeneralPaperEpochSnapshot GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueOccurrenceHistory
open scoped BigOperators
@[fun_prop]
theorem reference_scale_fieldProfile (m lambda k Qv : ℕ) :
    Scale (fun W => fieldProfile W m lambda k Qv) := by
  fun_prop [fieldProfile]
end GeneralPaperEncodedSnapshotStorage

namespace GeneralPaperEncodedSnapshotStorage
open GeneralPaperEpochSnapshot GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueOccurrenceHistory
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile (m lambda k Qv : ℕ) :
    Scale (fun W => profile W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperEncodedSnapshotStorage

namespace GeneralPaperEncodedTrajectoryStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile (m lambda k : ℕ) :
    Scale (fun W => profile W m lambda k) := by
  fun_prop [profile]
end GeneralPaperEncodedTrajectoryStorage

namespace GeneralPaperLocalTrajectoryStorage
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
@[fun_prop]
theorem reference_scale_profile (m lambda k : ℕ) :
    Scale (fun W => profile W m lambda k) := by
  fun_prop [profile]
end GeneralPaperLocalTrajectoryStorage

namespace GeneralPaperEpochResidentStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueEpochRun
@[fun_prop]
theorem reference_scale_profile (m lambda k Qv : ℕ) :
    Scale (fun W => profile W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperEpochResidentStorage

namespace GeneralPaperFieldFamilyConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_rowProfile (model : RationalCostModel) (k : ℕ) (a : Alphabet) :
    Scale (fun W => rowProfile model W k a) := by
  fun_prop [rowProfile]
end GeneralPaperFieldFamilyConstructionStorage

namespace GeneralPaperNativeNatFillStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (n V : ℕ) :
    Scale (fun W => profile W n V) := by
  fun_prop [profile]
end GeneralPaperNativeNatFillStorage

namespace GeneralPaperCellInputConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_extrasProfile (model : RationalCostModel) (U m : ℕ) :
    Scale (fun W => extrasProfile model W U m) := by
  fun_prop [extrasProfile]
end GeneralPaperCellInputConstructionStorage

namespace GeneralPaperCellInputConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_positionsProfile (model : RationalCostModel) (U n : ℕ) :
    Scale (fun W => positionsProfile model W U n) := by
  fun_prop [positionsProfile]
end GeneralPaperCellInputConstructionStorage

namespace GeneralPaperEpochPointStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (U n m : ℕ) :
    Scale (fun W => profile model W U n m) := by
  fun_prop [profile]
end GeneralPaperEpochPointStorage

namespace GeneralPaperBoundaryConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedPartitionStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (A U N : ℕ) :
    Scale (fun W => profile model W A U N) := by
  fun_prop [profile]
end GeneralPaperBoundaryConstructionStorage

namespace GeneralPaperSortConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_controlCap (depth N : ℕ) :
    Scale (fun W => controlCap W depth N) := by
  fun_prop [controlCap]
end GeneralPaperSortConstructionStorage

namespace GeneralPaperSortConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_controlWord (depth N : ℕ) :
    Scale (fun W => controlWord W depth N) := by
  fun_prop [controlWord]
end GeneralPaperSortConstructionStorage

namespace GeneralPaperSortConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_coefficient (P C depth N : ℕ) :
    Scale (fun W => coefficient W P C depth N) := by
  fun_prop [coefficient]
end GeneralPaperSortConstructionStorage

namespace GeneralPaperNaturalOrderConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_sortProfile (model : RationalCostModel) (U n : ℕ) :
    Scale (fun W => sortProfile model W U n) := by
  fun_prop [sortProfile]
end GeneralPaperNaturalOrderConstructionStorage

namespace GeneralPaperNaturalOrderConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (U n : ℕ) :
    Scale (fun W => profile model W U n) := by
  fun_prop [profile]
end GeneralPaperNaturalOrderConstructionStorage

namespace GeneralPaperPartitionConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (U n : ℕ) :
    Scale (fun W => profile model W U n) := by
  dsimp only [profile,packingProfile,GeneralPaperBoundaryConstructionStorage.profile]
  fun_prop
end GeneralPaperPartitionConstructionStorage

namespace GeneralPaperEpochPartitionConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (U n m : ℕ) :
    Scale (fun W => profile model W U n m) := by
  fun_prop [profile]
end GeneralPaperEpochPartitionConstructionStorage

namespace GeneralPaperCellPartitionConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_signedProfile (model : RationalCostModel) (U n m : ℕ) :
    Scale (fun W => signedProfile model W U n m) := by
  fun_prop [signedProfile]
end GeneralPaperCellPartitionConstructionStorage

namespace GeneralPaperRankCutArrayStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_coreProfile (U n : ℕ) :
    Scale (fun W => coreProfile W U n) := by
  fun_prop [coreProfile]
end GeneralPaperRankCutArrayStorage

namespace GeneralPaperRankCutArrayStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_representativeProfile (model : RationalCostModel) (U n : ℕ) :
    Scale (fun W => representativeProfile model W U n) := by
  fun_prop [representativeProfile]
end GeneralPaperRankCutArrayStorage

namespace GeneralPaperRankCutArrayStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_projectedProfile (model : RationalCostModel) (U n : ℕ) :
    Scale (fun W => projectedProfile model W U n) := by
  fun_prop [projectedProfile]
end GeneralPaperRankCutArrayStorage

namespace GeneralPaperRankCutArrayStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_shiftProfile (model : RationalCostModel) (U n : ℕ) :
    Scale (fun W => shiftProfile model W U n) := by
  fun_prop [shiftProfile]
end GeneralPaperRankCutArrayStorage

namespace GeneralPaperRankRecordConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_recordProfile (n k V : ℕ) :
    Scale (fun W => recordProfile W n k V) := by
  fun_prop [recordProfile]
end GeneralPaperRankRecordConstructionStorage

namespace GeneralPaperRankRecordConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (n k V : ℕ) :
    Scale (fun W => profile model W n k V) := by
  fun_prop [profile]
end GeneralPaperRankRecordConstructionStorage

namespace GeneralPaperSignedUpdateConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_returnedProfile (n k U : ℕ) :
    Scale (fun W => returnedProfile W n k U) := by
  fun_prop [returnedProfile]
end GeneralPaperSignedUpdateConstructionStorage

namespace GeneralPaperSignedUpdateConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (n k U : ℕ) :
    Scale (fun W => profile model W n k U) := by
  fun_prop [profile]
end GeneralPaperSignedUpdateConstructionStorage

namespace GeneralPaperCellPlanConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperCellPartitionConstructionStorage (unsignedExtras signedPositions signedExtras)
@[fun_prop]
theorem reference_scale_signedProfile (model : RationalCostModel) (k U m : ℕ) :
    Scale (fun W => signedProfile model W k U m) := by
  fun_prop [signedProfile]
end GeneralPaperCellPlanConstructionStorage

namespace GeneralPaperCellInputConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_unsignedProfile (model : RationalCostModel) (U n m : ℕ) :
    Scale (fun W => unsignedProfile model W U n m) := by
  fun_prop [unsignedProfile]
end GeneralPaperCellInputConstructionStorage

namespace GeneralPaperCellPartitionConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_unsignedProfile (model : RationalCostModel) (U n m : ℕ) :
    Scale (fun W => unsignedProfile model W U n m) := by
  fun_prop [unsignedProfile]
end GeneralPaperCellPartitionConstructionStorage

namespace GeneralPaperCDFPairConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_returnedProfile (n k U : ℕ) :
    Scale (fun W => returnedProfile W n k U) := by
  fun_prop [returnedProfile]
end GeneralPaperCDFPairConstructionStorage

namespace GeneralPaperCDFPairConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (n k U : ℕ) :
    Scale (fun W => profile model W n k U) := by
  fun_prop [profile]
end GeneralPaperCDFPairConstructionStorage

namespace GeneralPaperQueryLossConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_returnedProfile (n k U : ℕ) :
    Scale (fun W => returnedProfile W n k U) := by
  fun_prop [returnedProfile]
end GeneralPaperQueryLossConstructionStorage

namespace GeneralPaperQueryLossConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (n k U : ℕ) :
    Scale (fun W => profile model W n k U) := by
  fun_prop [profile]
end GeneralPaperQueryLossConstructionStorage

namespace GeneralPaperCellPlanConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperCellPartitionConstructionStorage (unsignedExtras signedPositions signedExtras)
@[fun_prop]
theorem reference_scale_unsignedProfile (model : RationalCostModel) (k U m : ℕ) :
    Scale (fun W => unsignedProfile model W k U m) := by
  fun_prop [unsignedProfile]
end GeneralPaperCellPlanConstructionStorage

namespace GeneralPaperFieldPreparationPhaseStorage
open GeneralPaperCodeAlphabet GeneralPaperFiniteStorageWindows
open GeneralPaperFieldFamilyActiveStorage
open GeneralPaperCellPlanConstructionStorage (unsignedPart signedPart)
@[fun_prop]
theorem reference_scale_childrenProfile (model : RationalCostModel) (k : ℕ) (a : Alphabet) :
    Scale (fun W => childrenProfile model W k a) := by
  fun_prop [childrenProfile]
end GeneralPaperFieldPreparationPhaseStorage

namespace GeneralPaperFieldPreparationPhaseStorage
open GeneralPaperCodeAlphabet GeneralPaperFiniteStorageWindows
open GeneralPaperFieldFamilyActiveStorage
open GeneralPaperCellPlanConstructionStorage (unsignedPart signedPart)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m k : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m k a) := by
  fun_prop [profile]
end GeneralPaperFieldPreparationPhaseStorage

namespace GeneralPaperCataloguePaddingStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
open GeneralPaperCodeMinimumScan (Entry)
@[fun_prop]
theorem reference_scale_entryCapacity (lambda : ℕ) :
    Scale (fun W => entryCapacity W lambda) := by
  fun_prop [entryCapacity]
end GeneralPaperCataloguePaddingStorage

namespace GeneralPaperCachedCatalogueStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
@[fun_prop]
theorem reference_scale_recordProfile (n : ℕ) (a : Alphabet) :
    Scale (fun W => recordProfile W n a) := by
  fun_prop [recordProfile]
end GeneralPaperCachedCatalogueStorage

namespace GeneralPaperRawCatalogueStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
@[fun_prop]
theorem reference_scale_entryCapacity (lambda : ℕ) :
    Scale (fun W => entryCapacity W lambda) := by
  fun_prop [entryCapacity]
end GeneralPaperRawCatalogueStorage

namespace GeneralPaperCataloguePaddingStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
open GeneralPaperCodeMinimumScan (Entry)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (cap : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W cap a) := by
  fun_prop [profile]
end GeneralPaperCataloguePaddingStorage

namespace GeneralPaperCataloguePointStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (U n : ℕ) :
    Scale (fun W => profile model W U n) := by
  fun_prop [profile]
end GeneralPaperCataloguePointStorage

namespace GeneralPaperCataloguePartitionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (U n : ℕ) :
    Scale (fun W => profile model W U n) := by
  fun_prop [profile]
end GeneralPaperCataloguePartitionStorage

namespace GeneralPaperCodeEvaluatePrice
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls GeneralPaperCodeScanExecution
open GeneralPaperDecodeBucketExecution (primitive)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (a : Alphabet) :
    Scale (fun W => profile model W a) := by
  fun_prop [profile]
end GeneralPaperCodeEvaluatePrice

namespace GeneralPaperCodeScanPrice
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls GeneralPaperCodeScanExecution
open GeneralPaperDecodeBucketExecution (primitive)
@[fun_prop]
theorem reference_scale_stepProfile (model : RationalCostModel) (a : Alphabet) :
    Scale (fun W => stepProfile model W a) := by
  fun_prop [stepProfile]
end GeneralPaperCodeScanPrice

namespace GeneralPaperCodeScanPrice
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls GeneralPaperCodeScanExecution
open GeneralPaperDecodeBucketExecution (primitive)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (a : Alphabet) (count : ℕ) :
    Scale (fun W => profile model W a count) := by
  fun_prop [profile]
end GeneralPaperCodeScanPrice

namespace GeneralPaperCodeScanStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
@[fun_prop]
theorem reference_scale_coefficient (lambda : ℕ) :
    Scale (fun W => coefficient W lambda) := by
  fun_prop [coefficient]
end GeneralPaperCodeScanStorage

namespace GeneralPaperCodeScanStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
@[fun_prop]
theorem reference_scale_evaluateProfile (model : RationalCostModel) (a : Alphabet) :
    Scale (fun W => evaluateProfile model W a) := by
  fun_prop [evaluateProfile]
end GeneralPaperCodeScanStorage

namespace GeneralPaperCodeScanStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (a : Alphabet) (n : ℕ) :
    Scale (fun W => profile model W a n) := by
  fun_prop [profile]
end GeneralPaperCodeScanStorage

namespace GeneralPaperCodeSplitStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (a : Alphabet) :
    Scale (fun W => profile model W a) := by
  fun_prop [profile]
end GeneralPaperCodeSplitStorage

namespace GeneralPaperLeastValidStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
@[fun_prop]
theorem reference_scale_pointProfile (model : RationalCostModel) (a : Alphabet) :
    Scale (fun W => pointProfile model W a) := by
  fun_prop [pointProfile]
end GeneralPaperLeastValidStorage

namespace GeneralPaperLeastValidStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
@[fun_prop]
theorem reference_scale_childProfile (model : RationalCostModel) (a : Alphabet) :
    Scale (fun W => childProfile model W a) := by
  fun_prop [childProfile]
end GeneralPaperLeastValidStorage

namespace GeneralPaperLeastValidStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (a : Alphabet) :
    Scale (fun W => profile model W a) := by
  fun_prop [profile]
end GeneralPaperLeastValidStorage

namespace GeneralPaperLeastValidStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
@[fun_prop]
theorem reference_scale_cellProfile (model : RationalCostModel) (a : Alphabet) :
    Scale (fun W => cellProfile model W a) := by
  fun_prop [cellProfile]
end GeneralPaperLeastValidStorage

namespace GeneralPaperRawCatalogueConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
open GeneralPaperRawCatalogueStorage
@[fun_prop]
theorem reference_scale_coefficient (n lambda : ℕ) :
    Scale (fun W => coefficient W n lambda) := by
  fun_prop [coefficient]
end GeneralPaperRawCatalogueConstructionStorage

namespace GeneralPaperRawCatalogueConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
open GeneralPaperRawCatalogueStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (n : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W n a) := by
  dsimp only [profile]
  fun_prop
end GeneralPaperRawCatalogueConstructionStorage

namespace GeneralPaperCachedCatalogueStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (n : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W n a) := by
  fun_prop [profile]
end GeneralPaperCachedCatalogueStorage

namespace GeneralPaperCatalogueFamilyStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m n : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m n a) := by
  fun_prop [profile]
end GeneralPaperCatalogueFamilyStorage

namespace GeneralPaperCatalogueProjectionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet
open GeneralPaperCatalogueProjection (Field FieldType select)
@[fun_prop]
theorem reference_scale_rowCapacity (K : ℕ) (a : Alphabet) :
    Scale (fun W => rowCapacity W K a) := by
  fun_prop [rowCapacity]
end GeneralPaperCatalogueProjectionStorage

namespace GeneralPaperCatalogueProjectionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet
open GeneralPaperCatalogueProjection (Field FieldType select)
@[fun_prop]
theorem reference_scale_familyProfile (m K : ℕ) (a : Alphabet) :
    Scale (fun W => familyProfile W m K a) := by
  fun_prop [familyProfile]
end GeneralPaperCatalogueProjectionStorage

namespace GeneralPaperCatalogueProjectionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet
open GeneralPaperCatalogueProjection (Field FieldType select)
@[fun_prop]
theorem reference_scale_rowProfile (K : ℕ) (a : Alphabet) :
    Scale (fun W => rowProfile W K a) := by
  fun_prop [rowProfile]
end GeneralPaperCatalogueProjectionStorage

namespace GeneralPaperCatalogueArrayConstructionStorage
open GeneralPaperCodeAlphabet
open GeneralPaperCatalogueProjection (Field)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m n : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m n a) := by
  fun_prop [profile]
end GeneralPaperCatalogueArrayConstructionStorage

namespace GeneralPaperReadyPreparationPhaseStorage
open GeneralPaperCodeAlphabet GeneralPaperFiniteStorageWindows
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m k mesh : ℕ) (a : Alphabet) :
    Scale (fun W => profile model W m k mesh a) := by
  fun_prop [profile]
end GeneralPaperReadyPreparationPhaseStorage

namespace GeneralPaperEpochSourcePhaseStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperCatalogueEpochRun GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_childrenProfile (model : RationalCostModel) (m k : ℕ) (a : Alphabet) :
    Scale (fun W => childrenProfile model W m k a) := by
  fun_prop [childrenProfile]
end GeneralPaperEpochSourcePhaseStorage

namespace GeneralPaperEpochSourcePhaseStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperCatalogueEpochRun GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_returnedProfile (m lambda k Qv : ℕ) :
    Scale (fun W => returnedProfile W m lambda k Qv) := by
  fun_prop [returnedProfile]
end GeneralPaperEpochSourcePhaseStorage

namespace GeneralPaperZeroArrayStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (n : ℕ) :
    Scale (fun W => profile model W n) := by
  fun_prop [profile]
end GeneralPaperZeroArrayStorage

namespace GeneralPaperEpochInitialConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEpochFieldState
@[fun_prop]
theorem reference_scale_fieldProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => fieldProfile model W m lambda k Qv) := by
  fun_prop [fieldProfile]
end GeneralPaperEpochInitialConstructionStorage

namespace GeneralPaperEpochInitialConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEpochFieldState
@[fun_prop]
theorem reference_scale_familyProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => familyProfile model W m lambda k Qv) := by
  fun_prop [familyProfile]
end GeneralPaperEpochInitialConstructionStorage

namespace GeneralPaperLocalSourceLifetimeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperEncodedScalarStorage GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_baseProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => baseProfile model W m lambda k Qv) := by
  fun_prop [baseProfile]
end GeneralPaperLocalSourceLifetimeStorage

namespace GeneralPaperLocalSourceLifetimeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperEncodedScalarStorage GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_returnedProfile (m lambda k Qv : ℕ) :
    Scale (fun W => returnedProfile W m lambda k Qv) := by
  fun_prop [returnedProfile]
end GeneralPaperLocalSourceLifetimeStorage

namespace GeneralPaperDPControlStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperEncodedFixedVector
@[fun_prop]
theorem reference_scale_frame (K J : ℕ) :
    Scale (fun W => frame W K J) := by
  fun_prop [frame]
end GeneralPaperDPControlStorage

namespace GeneralPaperDPControlStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperEncodedFixedVector
@[fun_prop]
theorem reference_scale_labelsProfile (n : ℕ) :
    Scale (fun W => labelsProfile W n) := by
  fun_prop [labelsProfile]
end GeneralPaperDPControlStorage

namespace GeneralPaperDPPhaseStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
open GeneralPaperOrderedTableHeight GeneralPaperEncodedScatterStorage GeneralPaperEncodedFixedVector
@[fun_prop]
theorem reference_scale_applyFixed (J P : ℕ) :
    Scale (fun W => applyFixed W J P) := by
  fun_prop [applyFixed]
end GeneralPaperDPPhaseStorage

namespace GeneralPaperDPPhaseStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
open GeneralPaperOrderedTableHeight GeneralPaperEncodedScatterStorage GeneralPaperEncodedFixedVector
@[fun_prop]
theorem reference_scale_leafFixed (K J : ℕ) :
    Scale (fun W => leafFixed W K J) := by
  fun_prop [leafFixed]
end GeneralPaperDPPhaseStorage

namespace GeneralPaperDPPhaseStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
open GeneralPaperOrderedTableHeight GeneralPaperEncodedScatterStorage GeneralPaperEncodedFixedVector
@[fun_prop]
theorem reference_scale_mergeFixed (J : ℕ) :
    Scale (fun W => mergeFixed W J) := by
  fun_prop [mergeFixed]
end GeneralPaperDPPhaseStorage

namespace GeneralPaperDPPhaseStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
open GeneralPaperOrderedTableHeight GeneralPaperEncodedScatterStorage GeneralPaperEncodedFixedVector
@[fun_prop]
theorem reference_scale_phaseBound (K J s h : ℕ) :
    Scale (fun W => phaseBound W K J s h) := by
  fun_prop [phaseBound]
end GeneralPaperDPPhaseStorage

namespace GeneralPaperEncodedDPStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile (K J s h : ℕ) :
    Scale (fun W => profile W K J s h) := by
  fun_prop [profile]
end GeneralPaperEncodedDPStorage

namespace GeneralPaperDPConstructionStorage
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP GeneralPaperDPPhaseStorage
@[fun_prop]
theorem reference_scale_profile (K J s h : ℕ) :
    Scale (fun W => profile W K J s h) := by
  fun_prop [profile]
end GeneralPaperDPConstructionStorage

namespace GeneralPaperEncodedProfitField
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
@[fun_prop]
theorem reference_scale_profile (K H s : ℕ) :
    Scale (fun W => profile W K H s) := by
  fun_prop [profile]
end GeneralPaperEncodedProfitField

namespace GeneralPaperEncodedProfitInput
open scoped BigOperators
open GeneralPaperResponseTag GeneralPaperOrderedProfitTreeBuild GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
@[fun_prop]
theorem reference_scale_fieldProfile (m lambda k Qv : ℕ) :
    Scale (fun W => fieldProfile W m lambda k Qv) := by
  fun_prop [fieldProfile]
end GeneralPaperEncodedProfitInput

namespace GeneralPaperEncodedProfitInput
open scoped BigOperators
open GeneralPaperResponseTag GeneralPaperOrderedProfitTreeBuild GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
@[fun_prop]
theorem reference_scale_profile (m lambda k Qv : ℕ) :
    Scale (fun W => profile W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperEncodedProfitInput

namespace GeneralPaperActualProfitTreeStorage
open scoped BigOperators
open GeneralPaperResponseTag GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
open GeneralPaperUnsignedCellConstancy (Prefix)
@[fun_prop]
theorem reference_scale_profile (m lambda k Qv : ℕ) (prepared : GeneralPaperProfitParameters.Prepared) :
    Scale (fun W => profile W m lambda k Qv prepared) := by
  fun_prop [profile]
end GeneralPaperActualProfitTreeStorage

namespace GeneralPaperNativeSelectorOutputStorage
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP GeneralPaperEncodedLabelStorage GeneralPaperEncodedFixedVector
open GeneralPaperUnsignedCellConstancy (Prefix)
@[fun_prop]
theorem reference_scale_rootProfile (K J h : ℕ) :
    Scale (fun W => rootProfile W K J h) := by
  fun_prop [rootProfile]
end GeneralPaperNativeSelectorOutputStorage

namespace GeneralPaperRowTrimStorage
open GeneralPaperEncodedLabelStorage GeneralPaperEncodedFixedVector
@[fun_prop]
theorem reference_scale_loopFrames (m n : ℕ) :
    Scale (fun W => loopFrames W m n) := by
  fun_prop [loopFrames]
end GeneralPaperRowTrimStorage

namespace GeneralPaperRowTrimStorage
open GeneralPaperEncodedLabelStorage GeneralPaperEncodedFixedVector
@[fun_prop]
theorem reference_scale_profile (K m n : ℕ) :
    Scale (fun W => profile W K m n) := by
  fun_prop [profile]
end GeneralPaperRowTrimStorage

namespace GeneralPaperEncodedLabelStorage
open GeneralPaperEncodedFixedVector
@[fun_prop]
theorem reference_scale_bufferCoefficient (K : ℕ) :
    Scale (fun W => bufferCoefficient W K) := by
  fun_prop [bufferCoefficient]
end GeneralPaperEncodedLabelStorage

namespace GeneralPaperTypedDecodeStorage
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP GeneralPaperEncodedLabelStorage
@[fun_prop]
theorem reference_scale_frame (K J H : ℕ) :
    Scale (fun W => frame W K J H) := by
  fun_prop [frame]
end GeneralPaperTypedDecodeStorage

namespace GeneralPaperTypedDecodeStorage
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP GeneralPaperEncodedLabelStorage
@[fun_prop]
theorem reference_scale_profile (K J H h : ℕ) :
    Scale (fun W => profile W K J H h) := by
  fun_prop [profile]
end GeneralPaperTypedDecodeStorage

namespace GeneralPaperNativeSelectorOutputStorage
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP GeneralPaperEncodedLabelStorage GeneralPaperEncodedFixedVector
open GeneralPaperUnsignedCellConstancy (Prefix)
@[fun_prop]
theorem reference_scale_profile (m K J h : ℕ) :
    Scale (fun W => profile W m K J h) := by
  fun_prop [profile]
end GeneralPaperNativeSelectorOutputStorage

namespace GeneralPaperSelectorResidentStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile {m : ℕ} (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => profile (m := m) W k Qv a weights Bc Br) := by
  fun_prop [profile]
end GeneralPaperSelectorResidentStorage

namespace GeneralPaperActualDPConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile {m : ℕ} (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => profile (m := m) W k Qv a weights Bc Br) := by
  fun_prop [profile]
end GeneralPaperActualDPConstructionStorage

namespace GeneralPaperSelectedRowConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open scoped BigOperators
@[fun_prop]
theorem reference_scale_elementProfile (m lambda k : ℕ) :
    Scale (fun W => elementProfile W m lambda k) := by
  fun_prop [elementProfile]
end GeneralPaperSelectedRowConstructionStorage

namespace GeneralPaperSelectedRowConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile (m lambda k : ℕ) :
    Scale (fun W => profile W m lambda k) := by
  fun_prop [profile]
end GeneralPaperSelectedRowConstructionStorage

namespace GeneralPaperLevelArrayStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_elementProfile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => elementProfile model W m lambda k Qv n) := by
  fun_prop [elementProfile]
end GeneralPaperLevelArrayStorage

namespace GeneralPaperLevelArrayStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => profile model W m lambda k Qv n) := by
  fun_prop [profile]
end GeneralPaperLevelArrayStorage

namespace GeneralPaperFieldUpdateConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
open GeneralPaperCatalogueOccurrenceHistory (Learner block)
@[fun_prop]
theorem reference_scale_advanceProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => advanceProfile model W m lambda k Qv) := by
  fun_prop [advanceProfile]
end GeneralPaperFieldUpdateConstructionStorage

namespace GeneralPaperMeshQueryEnvelope
open GeneralPaperMeshQueryExecution
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => profile price W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperMeshQueryEnvelope

namespace GeneralPaperMeshQueryMetadata
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_referenceWord (k : ℕ) :
    Scale (fun W => referenceWord W k) := by
  fun_prop [referenceWord]
end GeneralPaperMeshQueryMetadata

namespace GeneralPaperCachedMeshPrefixQuery
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => profile price W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperCachedMeshPrefixQuery

namespace GeneralPaperCachedMeshPrefixQuery
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_cachedProfile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => cachedProfile price W m lambda k Qv) := by
  fun_prop [cachedProfile]
end GeneralPaperCachedMeshPrefixQuery

namespace GeneralPaperMeshQueryStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_recordProfile (m lambda k Qv : ℕ) :
    Scale (fun W => recordProfile W m lambda k Qv) := by
  fun_prop [recordProfile]
end GeneralPaperMeshQueryStorage

namespace GeneralPaperQuotientConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperBoundedQuotient
@[fun_prop]
theorem reference_scale_frameCap (t d : ℕ) :
    Scale (fun W => frameCap W t d) := by
  fun_prop [frameCap]
end GeneralPaperQuotientConstructionStorage

namespace GeneralPaperQuotientConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperBoundedQuotient
@[fun_prop]
theorem reference_scale_localCap (model : RationalCostModel) (A t d : ℕ) :
    Scale (fun W => localCap model W A t d) := by
  fun_prop [localCap]
end GeneralPaperQuotientConstructionStorage

namespace GeneralPaperMeshQueryStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => profile model W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperMeshQueryStorage

namespace GeneralPaperCachedMeshQueryStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_prefixProfile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => prefixProfile model W m lambda k Qv n) := by
  fun_prop [prefixProfile]
end GeneralPaperCachedMeshQueryStorage

namespace GeneralPaperIncrementStorage
open GeneralPaperEncodedScalarStorage GeneralPaperIncrementPrice
@[fun_prop]
theorem reference_scale_signedProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => signedProfile model W m lambda k Qv) := by
  fun_prop [signedProfile]
end GeneralPaperIncrementStorage

namespace GeneralPaperSignedDeltaStepPrice
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => profile price W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperSignedDeltaStepPrice

namespace GeneralPaperDeltaStepStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_signedProfile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => signedProfile model W m lambda k Qv n) := by
  fun_prop [signedProfile]
end GeneralPaperDeltaStepStorage

namespace GeneralPaperDeltaArrayStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_signedProfile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => signedProfile model W m lambda k Qv n) := by
  fun_prop [signedProfile]
end GeneralPaperDeltaArrayStorage

namespace GeneralPaperIncrementStorage
open GeneralPaperEncodedScalarStorage GeneralPaperIncrementPrice
@[fun_prop]
theorem reference_scale_unsignedProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => unsignedProfile model W m lambda k Qv) := by
  fun_prop [unsignedProfile]
end GeneralPaperIncrementStorage

namespace GeneralPaperMeshPairPrice
open GeneralPaperMeshPairExecution
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_cdfProfile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => cdfProfile price W m lambda k Qv) := by
  fun_prop [cdfProfile]
end GeneralPaperMeshPairPrice

namespace GeneralPaperCachedMeshIntervalQuery
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => profile price W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperCachedMeshIntervalQuery

namespace GeneralPaperCachedMeshIntervalQuery
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_cachedProfile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => cachedProfile price W m lambda k Qv) := by
  fun_prop [cachedProfile]
end GeneralPaperCachedMeshIntervalQuery

namespace GeneralPaperMeshPairPrice
open GeneralPaperMeshPairExecution
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_tailsProfile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => tailsProfile price W m lambda k Qv) := by
  fun_prop [tailsProfile]
end GeneralPaperMeshPairPrice

namespace GeneralPaperMeshPairPrice
open GeneralPaperMeshPairExecution
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_countsProfile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => countsProfile price W m lambda k Qv) := by
  fun_prop [countsProfile]
end GeneralPaperMeshPairPrice

namespace GeneralPaperMeshPairStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
open GeneralPaperMeshPairExecution
@[fun_prop]
theorem reference_scale_cdfProfile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => cdfProfile model W m lambda k Qv n) := by
  fun_prop [cdfProfile]
end GeneralPaperMeshPairStorage

namespace GeneralPaperCachedMeshQueryStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_intervalProfile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => intervalProfile model W m lambda k Qv n) := by
  fun_prop [intervalProfile]
end GeneralPaperCachedMeshQueryStorage

namespace GeneralPaperMeshPairStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
open GeneralPaperMeshPairExecution
@[fun_prop]
theorem reference_scale_tailsProfile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => tailsProfile model W m lambda k Qv n) := by
  fun_prop [tailsProfile]
end GeneralPaperMeshPairStorage

namespace GeneralPaperMeshPairStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
open GeneralPaperMeshPairExecution
@[fun_prop]
theorem reference_scale_countsProfile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => countsProfile model W m lambda k Qv n) := by
  fun_prop [countsProfile]
end GeneralPaperMeshPairStorage

namespace GeneralPaperUnsignedDeltaStepPrice
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_profile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => profile price W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperUnsignedDeltaStepPrice

namespace GeneralPaperDeltaStepStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_unsignedProfile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => unsignedProfile model W m lambda k Qv n) := by
  fun_prop [unsignedProfile]
end GeneralPaperDeltaStepStorage

namespace GeneralPaperDeltaArrayStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_unsignedProfile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => unsignedProfile model W m lambda k Qv n) := by
  fun_prop [unsignedProfile]
end GeneralPaperDeltaArrayStorage

namespace GeneralPaperFieldUpdateConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
open GeneralPaperCatalogueOccurrenceHistory (Learner block)
@[fun_prop]
theorem reference_scale_deltaProfile (model : RationalCostModel) (m lambda k Qv candidateCount responseCount : ℕ) :
    Scale (fun W => deltaProfile model W m lambda k Qv candidateCount responseCount) := by
  fun_prop [deltaProfile]
end GeneralPaperFieldUpdateConstructionStorage

namespace GeneralPaperActualUpdateConstructionStorage
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
open GeneralPaperEncodedScalarStorage GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueOccurrenceHistory (block)
@[fun_prop]
theorem reference_scale_nativeProfile (model : RationalCostModel) (m lambda k Qv C R : ℕ) :
    Scale (fun W => nativeProfile model W m lambda k Qv C R) := by
  fun_prop [nativeProfile]
end GeneralPaperActualUpdateConstructionStorage

namespace GeneralPaperActualUpdateConstructionStorage
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
open GeneralPaperEncodedScalarStorage GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueOccurrenceHistory (block)
@[fun_prop]
theorem reference_scale_fieldProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => fieldProfile model W m lambda k Qv) := by
  fun_prop [fieldProfile]
end GeneralPaperActualUpdateConstructionStorage

namespace GeneralPaperRoundUpdateStorage
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
@[fun_prop]
theorem reference_scale_profile (m lambda k Qv : ℕ) :
    Scale (fun W => profile W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperRoundUpdateStorage

namespace GeneralPaperActualUpdateConstructionStorage
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
open GeneralPaperEncodedScalarStorage GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueOccurrenceHistory (block)
@[fun_prop]
theorem reference_scale_roundProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => roundProfile model W m lambda k Qv) := by
  fun_prop [roundProfile]
end GeneralPaperActualUpdateConstructionStorage

namespace GeneralPaperProfitFieldConstructionStorage
open GeneralPaperResponseTag GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
@[fun_prop]
theorem reference_scale_optionCap (m lambda k Qv : ℕ) :
    Scale (fun W => optionCap W m lambda k Qv) := by
  fun_prop [optionCap]
end GeneralPaperProfitFieldConstructionStorage

namespace GeneralPaperProfitFieldConstructionStorage
open GeneralPaperResponseTag GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
@[fun_prop]
theorem reference_scale_prefixProfile (m lambda k Qv : ℕ) :
    Scale (fun W => prefixProfile W m lambda k Qv) := by
  fun_prop [prefixProfile]
end GeneralPaperProfitFieldConstructionStorage

namespace GeneralPaperRootScanStorage
open GeneralPaperEncodedFixedVector
@[fun_prop]
theorem reference_scale_profile (J C n : ℕ) :
    Scale (fun W => profile W J C n) := by
  fun_prop [profile]
end GeneralPaperRootScanStorage

namespace GeneralPaperRootSelectionStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperEncodedFixedVector
@[fun_prop]
theorem reference_scale_profile (J s budgetWord : ℕ) :
    Scale (fun W => profile W J s budgetWord) := by
  fun_prop [profile,GeneralPaperRootScanStorage.profile]
end GeneralPaperRootSelectionStorage

namespace GeneralPaperRootProfitPhaseStorage
open GeneralPaperResponseTag
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperEncodedScalarStorage
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile (m lambda k Qv : ℕ) (prepared : GeneralPaperProfitParameters.Prepared) (budgetWord : ℕ) :
    Scale (fun W => profile W m lambda k Qv prepared budgetWord) := by
  fun_prop [profile]
end GeneralPaperRootProfitPhaseStorage

namespace GeneralPaperActualRootProfitStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile {m : ℕ} (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => profile (m := m) W k Qv a weights Bc Br) := by
  fun_prop [profile]
end GeneralPaperActualRootProfitStorage

namespace GeneralPaperNativeProfitLeafPrice
open GeneralPaperNativeProfitLeafExecution
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
@[fun_prop]
theorem reference_scale_elementProfile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => elementProfile price W m lambda k Qv) := by
  fun_prop [elementProfile]
end GeneralPaperNativeProfitLeafPrice

namespace GeneralPaperNativeProfitScalarStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperNativeProfitScalarPrice
@[fun_prop]
theorem reference_scale_coefficientProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => coefficientProfile model W m lambda k Qv) := by
  fun_prop [coefficientProfile]
end GeneralPaperNativeProfitScalarStorage

namespace GeneralPaperNativeProfitScalarStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperNativeProfitScalarPrice
@[fun_prop]
theorem reference_scale_profitProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => profitProfile model W m lambda k Qv) := by
  fun_prop [profitProfile]
end GeneralPaperNativeProfitScalarStorage

namespace GeneralPaperNativeProfitLeafStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
@[fun_prop]
theorem reference_scale_elementProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => elementProfile model W m lambda k Qv) := by
  fun_prop [elementProfile]
end GeneralPaperNativeProfitLeafStorage

namespace GeneralPaperActualQueryCallbackStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueOccurrenceHistory
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => profile (m := m) model W k Qv a weights Bc Br) := by
  fun_prop [profile]
end GeneralPaperActualQueryCallbackStorage

namespace GeneralPaperProfitGridQueryStorage
open GeneralPaperEncodedScalarStorage GeneralPaperRankOperands
open GeneralPaperProfitGridPrepare
@[fun_prop]
theorem reference_scale_compact (model : RationalCostModel) (depth L : ℕ) :
    Scale (fun W => compact model W depth L) := by
  fun_prop [compact]
end GeneralPaperProfitGridQueryStorage

namespace GeneralPaperSourceGridCallbackStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open scoped BigOperators
@[fun_prop]
theorem reference_scale_gridProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => gridProfile model W m lambda k Qv) := by
  fun_prop [gridProfile]
end GeneralPaperSourceGridCallbackStorage

namespace GeneralPaperSourceGridCallbackStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => profile (m := m) model W k Qv a weights Bc Br) := by
  fun_prop [profile]
end GeneralPaperSourceGridCallbackStorage

namespace GeneralPaperSourceUpdateConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => profile (m := m) model W k Qv a weights Bc Br) := by
  fun_prop [profile]
end GeneralPaperSourceUpdateConstructionStorage

namespace GeneralPaperSelectedRowConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open scoped BigOperators
@[fun_prop]
theorem reference_scale_sourceProfile {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => sourceProfile (m := m) model W k Qv a weights Bc Br) := by
  fun_prop [sourceProfile]
end GeneralPaperSelectedRowConstructionStorage

namespace GeneralPaperCachedPowerQueryStorage
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedPreparedPowers
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => profile model W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperCachedPowerQueryStorage

namespace GeneralPaperEpochNumeratorArrayPrice
open GeneralPaperDyadicFloat
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_elementProfile (price : ℕ → ℕ) (m lambda k Qv : ℕ) :
    Scale (fun W => elementProfile price W m lambda k Qv) := by
  fun_prop [elementProfile]
end GeneralPaperEpochNumeratorArrayPrice

namespace GeneralPaperEpochNumeratorConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperDyadicFloat
@[fun_prop]
theorem reference_scale_elementProfile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => elementProfile model W m lambda k Qv n) := by
  fun_prop [elementProfile]
end GeneralPaperEpochNumeratorConstructionStorage

namespace GeneralPaperEpochNumeratorConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperDyadicFloat
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m lambda k Qv n : ℕ) :
    Scale (fun W => profile model W m lambda k Qv n) := by
  fun_prop [profile]
end GeneralPaperEpochNumeratorConstructionStorage

namespace GeneralPaperEpochPrefixConstructionStorage
open GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_shortProfile (model : RationalCostModel) (H n : ℕ) :
    Scale (fun W => shortProfile model W H n) := by
  fun_prop [shortProfile]
end GeneralPaperEpochPrefixConstructionStorage

namespace GeneralPaperSnapshotConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEpochFieldState GeneralPaperEpochSnapshot
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_blockProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => blockProfile model W m lambda k Qv) := by
  fun_prop [blockProfile]
end GeneralPaperSnapshotConstructionStorage

namespace GeneralPaperSnapshotConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEpochFieldState GeneralPaperEpochSnapshot
open GeneralPaperUnsignedCellConstancy (Summary)
@[fun_prop]
theorem reference_scale_fieldProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => fieldProfile model W m lambda k Qv) := by
  fun_prop [fieldProfile]
end GeneralPaperSnapshotConstructionStorage

namespace GeneralPaperSnapshotFamilyConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperAdaptiveEpoch GeneralPaperEpochFieldState
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => profile model W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperSnapshotFamilyConstructionStorage

namespace GeneralPaperRoundPhaseStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => profile (m := m) model W k Qv a weights Bc Br) := by
  fun_prop [profile]
end GeneralPaperRoundPhaseStorage

namespace GeneralPaperLocalSourceLifetimeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperEncodedScalarStorage GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_phaseProfile {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => phaseProfile (m := m) model W k Qv a weights Bc Br) := by
  fun_prop [phaseProfile]
end GeneralPaperLocalSourceLifetimeStorage

namespace GeneralPaperTrajectoryControllerStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperSummaryArrayExecution (arrayWord)
@[fun_prop]
theorem reference_scale_frameProfile (capacity : ℕ) :
    Scale (fun W => frameProfile W capacity) := by
  fun_prop [frameProfile]
end GeneralPaperTrajectoryControllerStorage

namespace GeneralPaperLocalSourceLifetimeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperEncodedScalarStorage GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => profile (m := m) model W k Qv a weights Bc Br) := by
  fun_prop [profile]
end GeneralPaperLocalSourceLifetimeStorage

namespace GeneralPaperEpochSourcePhaseStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperCatalogueEpochRun GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => profile (m := m) model W k Qv a weights Bc Br) := by
  fun_prop [profile]
end GeneralPaperEpochSourcePhaseStorage

namespace GeneralPaperTrajectoryAppendStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperRetainedTrajectoryBits (rowBits)
@[fun_prop]
theorem reference_scale_frames (capacity n : ℕ) :
    Scale (fun W => frames W capacity n) := by
  fun_prop [frames]
end GeneralPaperTrajectoryAppendStorage

namespace GeneralPaperTrajectoryAppendStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperRetainedTrajectoryBits (rowBits)
@[fun_prop]
theorem reference_scale_rowsProfile (m capacity L : ℕ) :
    Scale (fun W => rowsProfile W m capacity L) := by
  fun_prop [rowsProfile]
end GeneralPaperTrajectoryAppendStorage

namespace GeneralPaperTrajectoryAppendStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperRetainedTrajectoryBits (rowBits)
@[fun_prop]
theorem reference_scale_profile (m capacity chunkSize L : ℕ) :
    Scale (fun W => profile W m capacity chunkSize L) := by
  fun_prop [profile]
end GeneralPaperTrajectoryAppendStorage

namespace GeneralPaperSourceLifetimeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_appendProfile (m lambda k : ℕ) :
    Scale (fun W => appendProfile W m lambda k) := by
  fun_prop [appendProfile]
end GeneralPaperSourceLifetimeStorage

namespace GeneralPaperSourceLifetimeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_returnedProfile (m lambda k Qv : ℕ) :
    Scale (fun W => returnedProfile W m lambda k Qv) := by
  fun_prop [returnedProfile]
end GeneralPaperSourceLifetimeStorage

namespace GeneralPaperSourceLifetimeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_phaseProfile {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => phaseProfile (m := m) model W k Qv a weights Bc Br) := by
  fun_prop [phaseProfile]
end GeneralPaperSourceLifetimeStorage

namespace GeneralPaperSourceLifetimeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperFiniteStorageWindows
open scoped BigOperators
@[fun_prop]
theorem reference_scale_profile {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => profile (m := m) model W k Qv a weights Bc Br) := by
  fun_prop [profile]
end GeneralPaperSourceLifetimeStorage

end Blotto
