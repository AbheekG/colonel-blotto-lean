import Blotto.BinaryPRGHeapReflectedLifetime
import Blotto.BinaryThreeGeometryLifetime
import Blotto.BinaryReflectedReachedHeight

/-! The reached reflected terminal chooses its fractional focus with actual
signed-word comparisons against zero and the retained capacity. -/
namespace Blotto.BinaryReflectedFocusLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def fractionalWithTrace (capacity resource : FixedArrayTable 3 SignedWord) (j : Fin 3) : Bool × Trace :=
  let positive := BinaryQuadraticExpressionLifetime.compareWithTrace (resource.read j) BinaryRationalOpcode.zero
  let below := BinaryQuadraticExpressionLifetime.compareWithTrace (capacity.read j) (resource.read j)
  ((!positive.1) && (!below.1),wrap 12 2 [positive.2,below.2])

theorem fractionalWithTrace_erasure (capacity resource : FixedArrayTable 3 SignedWord) (j : Fin 3) :
    (fractionalWithTrace capacity resource j).1 = BinaryThreeResourceState.fractional capacity resource j := by
  simp only [fractionalWithTrace,BinaryThreeResourceState.fractional,
    BinaryQuadraticExpressionLifetime.compareWithTrace_erases]

def fractionalEnvelope (W : ℕ) : ℕ := 2 * BinaryThreeGeometryLifetime.comparisonEnvelope W + 32

theorem fractionalWithTrace_usage (capacity resource : FixedArrayTable 3 SignedWord)
    (j : Fin 3) (W : ℕ) (hW : 1 ≤ W)
    (hCap : width (capacity.read j) ≤ W) (hResource : width (resource.read j) ≤ W) :
    usage (fractionalWithTrace capacity resource j).2 ≤ fractionalEnvelope W := by
  have hPositive := BinaryThreeGeometryLifetime.comparison_usage (resource.read j) BinaryRationalOpcode.zero
    W hResource hW
  have hBelow := BinaryThreeGeometryLifetime.comparison_usage (capacity.read j) (resource.read j)
    W hCap hResource
  have hw := wrap_usage 12 2
    [(BinaryQuadraticExpressionLifetime.compareWithTrace (resource.read j) BinaryRationalOpcode.zero).2,
      (BinaryQuadraticExpressionLifetime.compareWithTrace (capacity.read j) (resource.read j)).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 12 2
    [(BinaryQuadraticExpressionLifetime.compareWithTrace (resource.read j) BinaryRationalOpcode.zero).2,
      (BinaryQuadraticExpressionLifetime.compareWithTrace (capacity.read j) (resource.read j)).2]) ≤ _
  unfold fractionalEnvelope
  omega

def focusWithTrace (capacity resource : FixedArrayTable 3 SignedWord) : Fin 3 × Trace :=
  let first := fractionalWithTrace capacity resource 0
  if first.1 then (0,wrap 12 2 [first.2]) else
    let second := fractionalWithTrace capacity resource 1
    (if second.1 then 1 else 2,wrap 12 2 [first.2,second.2])

theorem focusWithTrace_erasure (system : BinaryReflectedFourSetup.System)
    (state : BinaryThreeResourceState.State) :
    (focusWithTrace system.capacity state.resource).1 = BinaryNestedTerminalInput.focus system state := by
  unfold focusWithTrace BinaryNestedTerminalInput.focus
  simp only [fractionalWithTrace_erasure]
  split_ifs <;> rfl

def focusEnvelope (W : ℕ) : ℕ := 2 * fractionalEnvelope W + 40

theorem focusWithTrace_usage (capacity resource : FixedArrayTable 3 SignedWord)
    (W : ℕ) (hW : 1 ≤ W) (hCap : ∀ j, width (capacity.read j) ≤ W)
    (hResource : ∀ j, width (resource.read j) ≤ W) :
    usage (focusWithTrace capacity resource).2 ≤ focusEnvelope W := by
  have hFirst := fractionalWithTrace_usage capacity resource 0 W hW (hCap 0) (hResource 0)
  have hSecond := fractionalWithTrace_usage capacity resource 1 W hW (hCap 1) (hResource 1)
  unfold focusWithTrace
  dsimp only
  split
  · have hw := wrap_usage 12 2 [(fractionalWithTrace capacity resource 0).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 12 2 [(fractionalWithTrace capacity resource 0).2]) ≤ _
    unfold focusEnvelope
    omega
  · have hw := wrap_usage 12 2
      [(fractionalWithTrace capacity resource 0).2,(fractionalWithTrace capacity resource 1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 12 2
      [(fractionalWithTrace capacity resource 0).2,(fractionalWithTrace capacity resource 1).2]) ≤ _
    unfold focusEnvelope
    omega

theorem reached_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) :
    usage (focusWithTrace (BinaryReflectedFourSetup.prepare input).capacity result.state.resource).2 ≤
      focusEnvelope (2 * expressionHeightBudget s 21 + 1) := by
  let W := 2 * expressionHeightBudget s 21 + 1
  have hCap : ∀ j, width ((BinaryReflectedFourSetup.prepare input).capacity.read j) ≤ W := by
    intro j
    have hRef := BinaryReflectedFourSetup.prepare_refines input source hC hR hCase
    have hSourceHeight := hH.reflectedResourceSystem hs hCase
    have hHeight : RationalHeight (value ((BinaryReflectedFourSetup.prepare input).capacity.read j))
        (expressionHeightBudget s 15) := by
      rw [BinaryReflectedFourSetup.System.capacity,FixedArrayTable.read_ofFn,
        BinaryRationalOpcode.apply_value .sub _ _
          ((BinaryReflectedFourSetup.prepare_canonical input hC).2.1 j).1
          ((BinaryReflectedFourSetup.prepare_canonical input hC).2.2.1 j).1,
        hRef.2.1 j,hRef.2.2.1 j]
      have hl := hSourceHeight.2.1 j
      have ht := hSourceHeight.2.2.1 j
      have hv := hl.sub_level ht
      change RationalHeight
        ((source.reflectedResourceSystem hCase).long j -
          (source.reflectedResourceSystem hCase).short j) (expressionHeightBudget s 15)
      simpa only [show (14 : ℕ) + 1 = 15 by decide] using hv
    have hWidth := (BinaryReflectedFourSetup.capacity_canonical _
      (BinaryReflectedFourSetup.prepare_canonical input hC) j).2.trans
        (rationalWordWidth_of_height hHeight)
    have hm := expressionHeightBudget_mono s (by decide : 15 ≤ 21)
    dsimp only [W]
    omega
  have hResource : ∀ j, width (result.state.resource.read j) ≤ W := by
    intro j
    have hHeight := BinaryReflectedReachedHeight.reached_resource_height input source hC hR hCase
      s hs hH N bits result hSuccess j
    have hWidth := (result.canonical j).2.trans (rationalWordWidth_of_height hHeight)
    simpa only [W,Nat.add_comm] using hWidth
  exact focusWithTrace_usage _ _ W (by dsimp only [W]; omega) hCap hResource

theorem reached_all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (borrowed steps : ℕ) :
    retainedHeap borrowed
      (focusWithTrace (BinaryReflectedFourSetup.prepare input).capacity result.state.resource).2 steps ≤
      borrowed + focusEnvelope (2 * expressionHeightBudget s 21 + 1) ∧
    framePeak ((focusWithTrace (BinaryReflectedFourSetup.prepare input).capacity
      result.state.resource).2.take steps) ≤ focusEnvelope (2 * expressionHeightBudget s 21 + 1) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (reached_usage input source hC hR hCase s hs hH N bits result hSuccess) borrowed steps

def preparedFocusWithTrace {input : BinaryFourParameters.Input}
    (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) : Fin 3 × Trace :=
  focusWithTrace prepared.capacity state.resource

theorem preparedFocusWithTrace_erasure {input : BinaryFourParameters.Input}
    (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) :
    (preparedFocusWithTrace prepared state).1 =
      BinaryNestedTerminalInput.focus (BinaryReflectedFourSetup.prepare input) state := by
  unfold preparedFocusWithTrace
  rw [prepared.capacity_source]
  exact focusWithTrace_erasure _ state

theorem preparedFocusWithTrace_reached_usage (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) :
    usage (preparedFocusWithTrace prepared result.state).2 ≤
      focusEnvelope (2 * expressionHeightBudget s 21 + 1) := by
  unfold preparedFocusWithTrace
  rw [prepared.capacity_source]
  exact reached_usage input source hC hR hCase s hs hH N bits result hSuccess

theorem prepared_reached_widths (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) :
    (∀ j, width (prepared.capacity.read j) ≤ 2 * expressionHeightBudget s 21 + 1) ∧
      (∀ j, width (result.state.resource.read j) ≤ 2 * expressionHeightBudget s 21 + 1) := by
  constructor
  · intro j
    rw [prepared.capacity_source]
    have hRef := BinaryReflectedFourSetup.prepare_refines input source hC hR hCase
    have hSourceHeight := hH.reflectedResourceSystem hs hCase
    have hHeight : RationalHeight (value ((BinaryReflectedFourSetup.prepare input).capacity.read j))
        (expressionHeightBudget s 15) := by
      rw [BinaryReflectedFourSetup.System.capacity,FixedArrayTable.read_ofFn,
        BinaryRationalOpcode.apply_value .sub _ _
          ((BinaryReflectedFourSetup.prepare_canonical input hC).2.1 j).1
          ((BinaryReflectedFourSetup.prepare_canonical input hC).2.2.1 j).1,
        hRef.2.1 j,hRef.2.2.1 j]
      have hv := (hSourceHeight.2.1 j).sub_level (hSourceHeight.2.2.1 j)
      change RationalHeight
        ((source.reflectedResourceSystem hCase).long j -
          (source.reflectedResourceSystem hCase).short j) (expressionHeightBudget s 15)
      simpa only [show (14 : ℕ) + 1 = 15 by decide] using hv
    have hWidth := (BinaryReflectedFourSetup.capacity_canonical _
      (BinaryReflectedFourSetup.prepare_canonical input hC) j).2.trans
        (rationalWordWidth_of_height hHeight)
    have hm := expressionHeightBudget_mono s (by decide : 15 ≤ 21)
    omega
  · intro j
    have hHeight := BinaryReflectedReachedHeight.reached_resource_height input source hC hR hCase
      s hs hH N bits result hSuccess j
    have hWidth := (result.canonical j).2.trans (rationalWordWidth_of_height hHeight)
    omega

end Blotto.BinaryReflectedFocusLifetime
