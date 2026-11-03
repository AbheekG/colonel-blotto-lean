import Blotto.BinaryAssemblyArithmeticWork
import Blotto.BinaryThreeFactoryWork

/-! Actual first-case nested conditional profile construction has an explicit
primitive price through midpoint, parameter/geometry production, the positive
guard, regular descriptor/translation or zero-probability corner. Generated
heights follow the actual inputs and finite ASTs, without source/height oracles. -/

namespace Blotto.BinaryNestedFirstFactoryWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryNestedParameters BinaryNestedFirstConditional BinaryNestedParameterWork
open BinaryFactoryHeight BinarySyntaxUniformWork

def descriptorWithWork (input : Input) (x : SignedWord) : BinaryStoredOverlapEnvironment.Segment 3 9 × ℕ :=
  let parameters := BinaryNestedParameterWork.prepareWithWork input x
  let positive := !BinaryRationalArithmetic.lessEqual (parameters.1.read 4) zero
  let guardWork := BinaryRationalArithmetic.lessEqualWork (parameters.1.read 4) zero
  if positive then
    let env := geometry input x
    let table := BinaryThreeDescriptorCompiler.descriptor env
    (BinarySegmentAssembly.shiftThird table x, parameters.2 + guardWork + geometryWork input x +
      BinaryThreeDescriptorCompiler.descriptorWork env + BinaryAssemblyArithmeticWork.shiftWork table x)
  else (corner input x,parameters.2 + guardWork)

theorem descriptorWithWork_state (input : Input) (x : SignedWord) :
    (descriptorWithWork input x).1 = descriptor input x := by
  unfold descriptorWithWork descriptor
  dsimp only [BinaryNestedParameterWork.prepareWithWork]
  split_ifs <;> rfl

theorem descriptor_height (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) (hx : RationalHeight (value x) s) :
    SegmentHeight (descriptor input x) (expressionHeightBudget s 33) := by
  have hGeo := BinaryNestedParameterWork.geometry_height input x hC hX s hs hH hx
  have hGeoC := geometry_canonical input x hC hX
  have hTable := BinaryThreeFactoryWork.descriptor_height (geometry input x) hGeoC _ (height_three hs) hGeo
  rw [expressionHeightBudget_comp] at hTable
  have hX32 := hx.mono (expressionHeightBudget_ge_input s 32)
  have hShift := BinaryAssemblyArithmeticWork.shift_height _ x (BinaryThreeDescriptorCompiler.descriptor_canonical _ hGeoC)
    hX _ hTable hX32
  rw [expressionHeightBudget_comp] at hShift
  unfold descriptor
  split
  · exact hShift
  · have hm := expressionHeightBudget_ge_input s 33
    have h0 := (zero_height s hs).mono hm
    have h1 := (one_height s hs).mono hm
    refine ⟨?_,?_⟩
    · intro slot
      simp only [corner,FixedArrayTable.read_ofFn]
      split <;> assumption
    · intro slot j
      simp only [corner,FixedArrayTable.read_ofFn]
      fin_cases j
      · exact ⟨h0,hH.2.1.mono hm⟩
      · exact ⟨hH.2.2.1.mono hm,h0⟩
      · exact ⟨hx.mono hm,hx.mono hm⟩

def descriptorBound (s : ℕ) : ℕ := 3328 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) +
  compareBound (expressionHeightBudget s 16) + BinaryThreeFactoryWork.bound (expressionHeightBudget s 16) +
    18 * opcodeBound (expressionHeightBudget s 32)

theorem descriptorWithWork_bound (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) (hx : RationalHeight (value x) s) :
    (descriptorWithWork input x).2 ≤ descriptorBound s := by
  have hP := prepareWork_bound input x hC hX s hs hH hx
  have hParameter := prepare_height input x hC hX s hs hH hx 4
  have hGuard := comparator_bound ((prepare input x).read 4) zero (prepare_canonical input x hC hX 4) zero_canonical
    _ hParameter (zero_height _ (height_three hs))
  have hGeo := BinaryNestedParameterWork.geometry_height input x hC hX s hs hH hx
  have hGeoC := geometry_canonical input x hC hX
  have hGeoWork := geometryWork_bound input x hC hX s hs hH hx
  have hTableWork := BinaryThreeFactoryWork.descriptorWork_bound (geometry input x) hGeoC _ (height_three hs) hGeo
  have hTable := BinaryThreeFactoryWork.descriptor_height (geometry input x) hGeoC _ (height_three hs) hGeo
  rw [expressionHeightBudget_comp] at hTable
  have hShift := BinaryAssemblyArithmeticWork.shiftWork_bound _ x (BinaryThreeDescriptorCompiler.descriptor_canonical _ hGeoC)
    hX _ hTable (hx.mono (expressionHeightBudget_ge_input s 32))
  unfold descriptorWithWork
  dsimp only [BinaryNestedParameterWork.prepareWithWork]
  split_ifs <;> dsimp only <;> unfold descriptorBound <;> nlinarith

def firstProfileWithWork (input : Input) (K : ℕ) (bits : Fin K → Bool) : BinaryStoredOverlapEnvironment.Segment 3 9 × ℕ :=
  let scalar := BinaryDyadicMidpoint.sampleWithWork K bits
  let parameters := BinaryNestedParameterWork.prepareWithWork input scalar.1
  let table := descriptorWithWork input (parameters.1.read 3)
  (table.1,scalar.2 + parameters.2 + table.2)

theorem firstProfileWithWork_state (input : Input) (K : ℕ) (bits : Fin K → Bool) :
    (firstProfileWithWork input K bits).1 = firstProfile input K bits := by
  unfold firstProfileWithWork firstProfile midpointLocation
  rw [descriptorWithWork_state,BinaryNestedParameterWork.prepareWithWork_state]
  rfl

def firstBound (s K : ℕ) : ℕ := 180 * (K + 3) ^ 3 +
  2304 * BinaryRationalExpression.uniformPrice (expressionHeightBudget (max s (K + 2)) 16) +
    descriptorBound (expressionHeightBudget (max s (K + 2)) 16)

theorem firstProfile_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s)
    (K : ℕ) (bits : Fin K → Bool) :
    SegmentHeight (firstProfile input K bits) (expressionHeightBudget (max s (K + 2)) 49) := by
  let W := max s (K + 2)
  have hInput := BinaryFactoryHeight.InputHeight.mono hH (le_max_left s (K + 2))
  have hScalar : RationalHeight (value (BinaryDyadicMidpoint.sample K bits)) W := by
    rw [BinaryDyadicMidpoint.sample_value]
    exact (dyadicMidpointSample_height K bits).mono (le_max_right s (K + 2))
  have hX := prepare_height input _ hC (BinaryDyadicMidpoint.sample_canonical K bits) W (hs.trans (le_max_left _ _)) hInput hScalar 3
  have hInput16 := BinaryFactoryHeight.InputHeight.mono hInput (expressionHeightBudget_ge_input W 16)
  have hTable := descriptor_height input (midpointLocation input K bits) hC (midpointLocation_canonical input hC K bits)
    _ (height_three (hs.trans (le_max_left _ _))) hInput16 hX
  rw [expressionHeightBudget_comp] at hTable
  exact hTable

theorem firstProfileWithWork_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s)
    (K : ℕ) (bits : Fin K → Bool) : (firstProfileWithWork input K bits).2 ≤ firstBound s K := by
  let W := max s (K + 2)
  have hInput := BinaryFactoryHeight.InputHeight.mono hH (le_max_left s (K + 2))
  have hScalar : RationalHeight (value (BinaryDyadicMidpoint.sample K bits)) W := by
    rw [BinaryDyadicMidpoint.sample_value]
    exact (dyadicMidpointSample_height K bits).mono (le_max_right s (K + 2))
  have hS := BinaryDyadicMidpoint.sampleWithWork_bound K bits
  have hP := prepareWork_bound input _ hC (BinaryDyadicMidpoint.sample_canonical K bits) W (hs.trans (le_max_left _ _)) hInput hScalar
  have hX := prepare_height input _ hC (BinaryDyadicMidpoint.sample_canonical K bits) W (hs.trans (le_max_left _ _)) hInput hScalar 3
  have hD := descriptorWithWork_bound input (midpointLocation input K bits) hC (midpointLocation_canonical input hC K bits)
    _ (height_three (hs.trans (le_max_left _ _))) (BinaryFactoryHeight.InputHeight.mono hInput (expressionHeightBudget_ge_input W 16)) hX
  exact Nat.add_le_add (Nat.add_le_add hS hP) hD

end Blotto.BinaryNestedFirstFactoryWork
