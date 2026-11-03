import Blotto.BinarySmallUniformPreparationLifetime

/-! One proportional endpoint split executes the actual sum, two divisions
and two products. The zero-total case follows the existing opcode exactly. -/
namespace Blotto.BinarySmallUniformSplitLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage BinaryFactoryHeight
set_option maxHeartbeats 2000000

def splitWithTrace (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) :
    FixedArrayTable 4 SignedWord × Trace :=
  let total := BinaryQuadraticLifetime.applyWithTrace .add first second
  let low := BinaryQuadraticLifetime.applyWithTrace .div first total.1
  let high := BinaryQuadraticLifetime.applyWithTrace .div second total.1
  let left := BinaryQuadraticLifetime.applyWithTrace .mul low.1 (row.read 0)
  let right := BinaryQuadraticLifetime.applyWithTrace .mul high.1 (row.read 0)
  (FixedArrayTable.ofFn ![left.1,right.1,row.read 1,row.read 2],
    wrap 32 6 [total.2,low.2,high.2,left.2,right.2])

theorem splitWithTrace_erasure (first second : SignedWord) (row : FixedArrayTable 3 SignedWord)
    (hFirst : CanonicalWord first) (hSecond : CanonicalWord second)
    (hRow : ∀ j,CanonicalWord (row.read j)) :
    (splitWithTrace first second row).1 = BinarySmallUniformCompiler.split first second row := by
  have hTotal := BinaryQuadraticLifetime.applyWithTrace_state .add first second hFirst.1 hSecond.1
  have hTotalC : CanonicalWord (BinaryRationalOpcode.apply .add first second) :=
    BinaryReflectedFourSetup.opcode_canonical .add first second hFirst hSecond
  have hLow := BinaryQuadraticLifetime.applyWithTrace_state .div first
    (BinaryQuadraticLifetime.applyWithTrace .add first second).1 hFirst.1 (by rw [hTotal]; exact hTotalC.1)
  have hHigh := BinaryQuadraticLifetime.applyWithTrace_state .div second
    (BinaryQuadraticLifetime.applyWithTrace .add first second).1 hSecond.1 (by rw [hTotal]; exact hTotalC.1)
  have hLowC : CanonicalWord (BinaryRationalOpcode.apply .div first (BinaryRationalOpcode.apply .add first second)) :=
    BinaryReflectedFourSetup.opcode_canonical .div first _ hFirst hTotalC
  have hHighC : CanonicalWord (BinaryRationalOpcode.apply .div second (BinaryRationalOpcode.apply .add first second)) :=
    BinaryReflectedFourSetup.opcode_canonical .div second _ hSecond hTotalC
  have hLeft := BinaryQuadraticLifetime.applyWithTrace_state .mul
    (BinaryQuadraticLifetime.applyWithTrace .div first (BinaryQuadraticLifetime.applyWithTrace .add first second).1).1
    (row.read 0) (by rw [hLow,hTotal]; exact hLowC.1) (hRow 0).1
  have hRight := BinaryQuadraticLifetime.applyWithTrace_state .mul
    (BinaryQuadraticLifetime.applyWithTrace .div second (BinaryQuadraticLifetime.applyWithTrace .add first second).1).1
    (row.read 0) (by rw [hHigh,hTotal]; exact hHighC.1) (hRow 0).1
  unfold splitWithTrace BinarySmallUniformCompiler.split
  dsimp only
  rw [hLeft,hRight,hLow,hHigh,hTotal]

def envelope (s : ℕ) : ℕ :=
  5 * opcodeEnvelope (2 * expressionHeightBudget s 2 + 1) + 128

theorem splitWithTrace_usage (first second : SignedWord) (row : FixedArrayTable 3 SignedWord)
    (hFirstC : CanonicalWord first) (hSecondC : CanonicalWord second)
    (hRowC : ∀ j,CanonicalWord (row.read j)) (s : ℕ)
    (hFirst : RationalHeight (value first) s) (hSecond : RationalHeight (value second) s)
    (hRow : ∀ j,RationalHeight (value (row.read j)) s) :
    usage (splitWithTrace first second row).2 ≤ envelope s := by
  let total := BinaryQuadraticLifetime.applyWithTrace .add first second
  let low := BinaryQuadraticLifetime.applyWithTrace .div first total.1
  let high := BinaryQuadraticLifetime.applyWithTrace .div second total.1
  let left := BinaryQuadraticLifetime.applyWithTrace .mul low.1 (row.read 0)
  let right := BinaryQuadraticLifetime.applyWithTrace .mul high.1 (row.read 0)
  have hTotalState : total.1 = BinaryRationalOpcode.apply .add first second :=
    BinaryQuadraticLifetime.applyWithTrace_state .add first second hFirstC.1 hSecondC.1
  have hTotalC : CanonicalWord total.1 := by
    rw [hTotalState]
    exact BinaryReflectedFourSetup.opcode_canonical .add first second hFirstC hSecondC
  have hLowState : low.1 = BinaryRationalOpcode.apply .div first total.1 :=
    BinaryQuadraticLifetime.applyWithTrace_state .div first total.1 hFirstC.1 hTotalC.1
  have hHighState : high.1 = BinaryRationalOpcode.apply .div second total.1 :=
    BinaryQuadraticLifetime.applyWithTrace_state .div second total.1 hSecondC.1 hTotalC.1
  have hLowC : CanonicalWord low.1 := by
    rw [hLowState]
    exact BinaryReflectedFourSetup.opcode_canonical .div first total.1 hFirstC hTotalC
  have hHighC : CanonicalWord high.1 := by
    rw [hHighState]
    exact BinaryReflectedFourSetup.opcode_canonical .div second total.1 hSecondC hTotalC
  have hTotalH : RationalHeight (value total.1) (expressionHeightBudget s 1) := by
    rw [hTotalState,BinaryRationalOpcode.apply_value .add _ _ hFirstC.1 hSecondC.1]
    have hf : RationalHeight (value first) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hFirst
    have hs : RationalHeight (value second) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hSecond
    exact hf.add_level hs
  have hLowH : RationalHeight (value low.1) (expressionHeightBudget s 2) := by
    rw [hLowState,BinaryRationalOpcode.apply_value .div _ _ hFirstC.1 hTotalC.1]
    exact (hFirst.mono (expressionHeightBudget_ge_input s 1)).div_level hTotalH
  have hHighH : RationalHeight (value high.1) (expressionHeightBudget s 2) := by
    rw [hHighState,BinaryRationalOpcode.apply_value .div _ _ hSecondC.1 hTotalC.1]
    exact (hSecond.mono (expressionHeightBudget_ge_input s 1)).div_level hTotalH
  let W := 2 * expressionHeightBudget s 2 + 1
  have hFirstW : width first ≤ W := by
    have he := hFirstC.2.trans (rationalWordWidth_of_height hFirst)
    have hm := expressionHeightBudget_ge_input s 2
    dsimp only [W]
    omega
  have hSecondW : width second ≤ W := by
    have he := hSecondC.2.trans (rationalWordWidth_of_height hSecond)
    have hm := expressionHeightBudget_ge_input s 2
    dsimp only [W]
    omega
  have hTotalW : width total.1 ≤ W := by
    have he := hTotalC.2.trans (rationalWordWidth_of_height hTotalH)
    have hm := expressionHeightBudget_mono s (by decide : 1 ≤ 2)
    dsimp only [W]
    omega
  have hLowW : width low.1 ≤ W := by
    have he := hLowC.2.trans (rationalWordWidth_of_height hLowH)
    dsimp only [W]
    omega
  have hHighW : width high.1 ≤ W := by
    have he := hHighC.2.trans (rationalWordWidth_of_height hHighH)
    dsimp only [W]
    omega
  have hRowW : width (row.read 0) ≤ W := by
    have he := (hRowC 0).2.trans (rationalWordWidth_of_height (hRow 0))
    have hm := expressionHeightBudget_ge_input s 2
    dsimp only [W]
    omega
  have hTotalUsage := opcode_usage .add first second W hFirstW hSecondW
  have hLowUsage := opcode_usage .div first total.1 W hFirstW hTotalW
  have hHighUsage := opcode_usage .div second total.1 W hSecondW hTotalW
  have hLeftUsage := opcode_usage .mul low.1 (row.read 0) W hLowW hRowW
  have hRightUsage := opcode_usage .mul high.1 (row.read 0) W hHighW hRowW
  change usage total.2 ≤ _ at hTotalUsage
  change usage low.2 ≤ _ at hLowUsage
  change usage high.2 ≤ _ at hHighUsage
  change usage left.2 ≤ _ at hLeftUsage
  change usage right.2 ≤ _ at hRightUsage
  have hw := wrap_usage 32 6 [total.2,low.2,high.2,left.2,right.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 6 [total.2,low.2,high.2,left.2,right.2]) ≤ _
  unfold envelope
  dsimp only [W] at hTotalUsage hLowUsage hHighUsage hLeftUsage hRightUsage
  omega

theorem all_prefix (first second : SignedWord) (row : FixedArrayTable 3 SignedWord)
    (hFirstC : CanonicalWord first) (hSecondC : CanonicalWord second)
    (hRowC : ∀ j,CanonicalWord (row.read j)) (s : ℕ)
    (hFirst : RationalHeight (value first) s) (hSecond : RationalHeight (value second) s)
    (hRow : ∀ j,RationalHeight (value (row.read j)) s) (borrowed steps : ℕ) :
    retainedHeap borrowed (splitWithTrace first second row).2 steps ≤ borrowed + envelope s ∧
    framePeak ((splitWithTrace first second row).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (splitWithTrace_usage first second row hFirstC hSecondC hRowC s hFirst hSecond hRow) borrowed steps

end Blotto.BinarySmallUniformSplitLifetime
