import Blotto.BinaryAssemblyHeightWork
import Blotto.BinaryNestedRemainingFactoryWork

/-! The ordered eighteen-slot producer retains one parameter table for regime
selection and branch assembly. Its selected component producers and cached
mixture complement have exact old-table semantics and input-derived primitive
prices. This ledger does not certify copies, metadata or physical storage. -/

namespace Blotto.BinaryNestedOrderedFactoryWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryNestedParameters BinaryStoredOverlapEnvironment BinaryFactoryHeight BinaryNestedParameterWork

def width (s K : ℕ) : ℕ := max s (K + 2)
def height (s K d : ℕ) : ℕ := expressionHeightBudget (width s K) d

theorem input_height (input : Input) (s K : ℕ) (h : InputHeight input s) : InputHeight input (width s K) :=
  BinaryFactoryHeight.InputHeight.mono h (le_max_left _ _)

theorem parameter_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : InputHeight input s) (K : ℕ) (j : Fin 9) :
    RationalHeight (value ((BinaryNestedProfileCompiler.parameters input).read j)) (height s K 16) :=
  prepare_height input zero hC zero_canonical _ (hs.trans (le_max_left _ _))
    (input_height input s K hH) (zero_height _ (hs.trans (le_max_left _ _))) j

theorem family_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : InputHeight input s) (K : ℕ) (bits : Fin K → Bool) (j : Fin 9) :
    SegmentHeight (BinaryNestedComponents.familyLottery input ((BinaryNestedProfileCompiler.parameters input).read j) K bits)
      (height s K 81) := by
  have h16 := input_height input s K hH
  have hInput := BinaryFactoryHeight.InputHeight.mono h16 (expressionHeightBudget_ge_input (width s K) 16)
  have hFamily := BinaryNestedFamilyFactoryWork.family_input_height input _ hC
    (BinaryNestedProfileCompiler.parameters_canonical input hC j) _
    (height_three (hs.trans (le_max_left _ _))) hInput (parameter_height input hC s hs hH K j)
  rw [expressionHeightBudget_comp] at hFamily
  have ht := BinaryNestedFirstFactoryWork.firstProfile_height _
    (BinaryNestedComponents.familyInput_canonical input _ hC (BinaryNestedProfileCompiler.parameters_canonical input hC j))
    _ (height_three (hs.trans (le_max_left _ _))) hFamily K bits
  have hk : K + 2 ≤ height s K 32 := (le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input _ 32)
  change SegmentHeight _ (expressionHeightBudget (max (height s K 32) (K + 2)) 49) at ht
  rw [max_eq_left hk] at ht
  dsimp only [height] at ht
  rw [expressionHeightBudget_comp] at ht
  exact ht

def secondBranch (input : Input) (p : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : Fin K → Bool) : Segment 3 18 × ℕ :=
  let family := BinaryNestedFamilyFactoryWork.familyWithWork input (p.read 6) K bits
  let guardWork := BinaryRationalArithmetic.lessEqualWork input.t (p.read 6)
  if !BinaryRationalArithmetic.lessEqual input.t (p.read 6) then
    let uniform := BinaryNestedRemainingFactoryWork.secondWithWork input
    let assembled := BinaryAssemblyArithmeticWork.binaryWithWork (p.read 7) family.1 uniform.1
    (assembled.1,family.2 + guardWork + uniform.2 + assembled.2)
  else (BinarySegmentAssembly.padRight family.1 9 0,family.2 + guardWork)

def thirdBranch (input : Input) (p : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : Fin K → Bool) : Segment 3 18 × ℕ :=
  let residual := BinaryNestedRemainingFactoryWork.residualWithWork input
  let padded := BinarySegmentAssembly.padRight residual.1 6 0
  let guardWork := BinaryRationalArithmetic.lessEqualWork (p.read 2) zero
  if !BinaryRationalArithmetic.lessEqual (p.read 2) zero then
    let family := BinaryNestedFamilyFactoryWork.familyWithWork input (p.read 2) K bits
    let assembled := BinaryAssemblyArithmeticWork.binaryWithWork (p.read 8) family.1 padded
    (assembled.1,residual.2 + guardWork + family.2 + assembled.2)
  else (BinarySegmentAssembly.padRight padded 9 0,residual.2 + guardWork)

theorem secondBranch_state (input : Input) (K : ℕ) (bits : Fin K → Bool) :
    (secondBranch input (BinaryNestedProfileCompiler.parameters input) K bits).1 =
      BinaryNestedProfileCompiler.secondProfile input K bits := by
  unfold secondBranch BinaryNestedProfileCompiler.secondProfile
  dsimp only
  split_ifs <;> simp only [BinaryAssemblyArithmeticWork.binaryWithWork_state,
    BinaryNestedFamilyFactoryWork.familyWithWork_state,BinaryNestedRemainingFactoryWork.secondWithWork_state]

theorem thirdBranch_state (input : Input) (K : ℕ) (bits : Fin K → Bool) :
    (thirdBranch input (BinaryNestedProfileCompiler.parameters input) K bits).1 =
      BinaryNestedProfileCompiler.thirdProfile input K bits := by
  unfold thirdBranch BinaryNestedProfileCompiler.thirdProfile
  dsimp only
  split_ifs <;> simp only [BinaryAssemblyArithmeticWork.binaryWithWork_state,
    BinaryNestedFamilyFactoryWork.familyWithWork_state,BinaryNestedRemainingFactoryWork.residualWithWork_state]

theorem second_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : InputHeight input s) (K : ℕ) (bits : Fin K → Bool) :
    SegmentHeight (BinaryNestedProfileCompiler.secondProfile input K bits) (height s K 83) := by
  have hp := parameter_height input hC s hs hH K
  have hf := family_height input hC s hs hH K bits 6
  have hu := BinaryNestedRemainingFactoryWork.second_height input hC (width s K)
    (hs.trans (le_max_left _ _)) (input_height input s K hH)
  have hu81 := hu.mono (expressionHeightBudget_mono _ (by decide : 36 ≤ 81))
  have hm := BinaryAssemblyHeightWork.binary_height _ _ _ (BinaryNestedProfileCompiler.parameters_canonical input hC 7)
    (BinaryNestedComponents.familyLottery_canonical input _ hC (BinaryNestedProfileCompiler.parameters_canonical input hC 6) K bits)
    (BinaryNestedComponents.secondUniformLottery_canonical input hC) _ (height_three (hs.trans (le_max_left _ _)))
    ((hp 7).mono (expressionHeightBudget_mono _ (by decide : 16 ≤ 81))) hf hu81
  rw [expressionHeightBudget_comp] at hm
  unfold BinaryNestedProfileCompiler.secondProfile
  dsimp only
  split
  · exact hm
  · exact BinaryAssemblyArithmeticWork.pad_height _ 9 0 _ (height_three (hs.trans (le_max_left _ _)))
      (hf.mono (expressionHeightBudget_mono _ (by decide : 81 ≤ 83)))

theorem third_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : InputHeight input s) (K : ℕ) (bits : Fin K → Bool) :
    SegmentHeight (BinaryNestedProfileCompiler.thirdProfile input K bits) (height s K 83) := by
  have hp := parameter_height input hC s hs hH K
  have hf := family_height input hC s hs hH K bits 2
  have hr := BinaryNestedRemainingFactoryWork.residual_height input hC (width s K)
    (hs.trans (le_max_left _ _)) (input_height input s K hH)
  have hr81 := BinaryAssemblyArithmeticWork.pad_height _ 6 0 _ (height_three (hs.trans (le_max_left _ _)))
    (hr.mono (expressionHeightBudget_mono _ (by decide : 24 ≤ 81)))
  have hc := BinarySegmentAssembly.padRight_canonical _ 6 0 (BinaryNestedComponents.residualLottery_canonical input hC)
  have hm := BinaryAssemblyHeightWork.binary_height _ _ _ (BinaryNestedProfileCompiler.parameters_canonical input hC 8)
    (BinaryNestedComponents.familyLottery_canonical input _ hC (BinaryNestedProfileCompiler.parameters_canonical input hC 2) K bits)
    hc _ (height_three (hs.trans (le_max_left _ _)))
    ((hp 8).mono (expressionHeightBudget_mono _ (by decide : 16 ≤ 81))) hf hr81
  rw [expressionHeightBudget_comp] at hm
  unfold BinaryNestedProfileCompiler.thirdProfile
  dsimp only
  split
  · exact hm
  · exact BinaryAssemblyArithmeticWork.pad_height _ 9 0 _ (height_three (hs.trans (le_max_left _ _)))
      (hr81.mono (expressionHeightBudget_mono _ (by decide : 81 ≤ 83)))

def familyBound (s K : ℕ) : ℕ := BinaryNestedFamilyFactoryWork.bound (height s K 16) K
def mixtureBound (s K : ℕ) : ℕ := 19 * opcodeBound (height s K 82)
def secondBound (s K : ℕ) : ℕ := familyBound s K + compareBound (height s K 16) +
  BinaryNestedRemainingFactoryWork.secondBound (width s K) + mixtureBound s K
def thirdBound (s K : ℕ) : ℕ := BinaryNestedRemainingFactoryWork.residualBound (width s K) +
  compareBound (height s K 16) + familyBound s K + mixtureBound s K

theorem family_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : InputHeight input s) (K : ℕ) (bits : Fin K → Bool) (j : Fin 9) :
    (BinaryNestedFamilyFactoryWork.familyWithWork input ((BinaryNestedProfileCompiler.parameters input).read j) K bits).2 ≤ familyBound s K :=
  BinaryNestedFamilyFactoryWork.familyWithWork_bound input _ hC (BinaryNestedProfileCompiler.parameters_canonical input hC j)
    _ (height_three (hs.trans (le_max_left _ _)))
    (BinaryFactoryHeight.InputHeight.mono (input_height input s K hH) (expressionHeightBudget_ge_input _ 16))
    (parameter_height input hC s hs hH K j) K bits

theorem secondBranch_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : InputHeight input s) (K : ℕ) (bits : Fin K → Bool) :
    (secondBranch input (BinaryNestedProfileCompiler.parameters input) K bits).2 ≤ secondBound s K := by
  have hp := parameter_height input hC s hs hH K
  have hi := input_height input s K hH
  have hGuard := comparator_bound input.t _ hC.2.2.2.2.1 (BinaryNestedProfileCompiler.parameters_canonical input hC 6)
    _ (hi.2.2.2.2.1.mono (expressionHeightBudget_ge_input _ 16)) (hp 6)
  have hf := family_bound input hC s hs hH K bits 6
  have hu := BinaryNestedRemainingFactoryWork.secondWithWork_bound input hC (width s K) (hs.trans (le_max_left _ _)) hi
  have hFamily := family_height input hC s hs hH K bits 6
  have hUniform := (BinaryNestedRemainingFactoryWork.second_height input hC (width s K) (hs.trans (le_max_left _ _)) hi).mono
    (expressionHeightBudget_mono _ (by decide : 36 ≤ 81))
  have hm := BinaryAssemblyArithmeticWork.binaryWithWork_bound _ _ _ (BinaryNestedProfileCompiler.parameters_canonical input hC 7)
    (BinaryNestedComponents.familyLottery_canonical input _ hC (BinaryNestedProfileCompiler.parameters_canonical input hC 6) K bits)
    (BinaryNestedComponents.secondUniformLottery_canonical input hC) _ (height_three (hs.trans (le_max_left _ _)))
    ((hp 7).mono (expressionHeightBudget_mono _ (by decide : 16 ≤ 81))) hFamily hUniform
  rw [expressionHeightBudget_comp] at hm
  unfold secondBranch
  dsimp only
  split_ifs <;> simp only [BinaryNestedFamilyFactoryWork.familyWithWork_state,BinaryNestedRemainingFactoryWork.secondWithWork_state]
  · exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hf hGuard) hu) hm
  · exact (Nat.add_le_add hf hGuard).trans (by unfold secondBound height at *; omega)

theorem thirdBranch_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : InputHeight input s) (K : ℕ) (bits : Fin K → Bool) :
    (thirdBranch input (BinaryNestedProfileCompiler.parameters input) K bits).2 ≤ thirdBound s K := by
  have hp := parameter_height input hC s hs hH K
  have hi := input_height input s K hH
  have hGuard := comparator_bound _ zero (BinaryNestedProfileCompiler.parameters_canonical input hC 2) zero_canonical
    _ (hp 2) (zero_height _ (height_three (hs.trans (le_max_left _ _))))
  have hf := family_bound input hC s hs hH K bits 2
  have hr := BinaryNestedRemainingFactoryWork.residualWithWork_bound input hC (width s K) (hs.trans (le_max_left _ _)) hi
  have hFamily := family_height input hC s hs hH K bits 2
  have hResidual := BinaryAssemblyArithmeticWork.pad_height _ 6 0 _ (height_three (hs.trans (le_max_left _ _)))
    ((BinaryNestedRemainingFactoryWork.residual_height input hC (width s K) (hs.trans (le_max_left _ _)) hi).mono
      (expressionHeightBudget_mono _ (by decide : 24 ≤ 81)))
  have hm := BinaryAssemblyArithmeticWork.binaryWithWork_bound _ _ _ (BinaryNestedProfileCompiler.parameters_canonical input hC 8)
    (BinaryNestedComponents.familyLottery_canonical input _ hC (BinaryNestedProfileCompiler.parameters_canonical input hC 2) K bits)
    (BinarySegmentAssembly.padRight_canonical _ 6 0 (BinaryNestedComponents.residualLottery_canonical input hC))
    _ (height_three (hs.trans (le_max_left _ _)))
    ((hp 8).mono (expressionHeightBudget_mono _ (by decide : 16 ≤ 81))) hFamily hResidual
  rw [expressionHeightBudget_comp] at hm
  unfold thirdBranch
  dsimp only
  split_ifs <;> simp only [BinaryNestedFamilyFactoryWork.familyWithWork_state,BinaryNestedRemainingFactoryWork.residualWithWork_state]
  · exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hr hGuard) hf) hm
  · exact (Nat.add_le_add hr hGuard).trans (by unfold thirdBound; omega)

def profileWithWork (input : Input) (K : ℕ) (bits : Fin K → Bool) : Segment 3 18 × ℕ :=
  let parameters := BinaryNestedParameterWork.prepareWithWork input zero
  let firstGuard := BinaryRationalArithmetic.lessEqualWork input.t (parameters.1.read 2)
  if BinaryRationalArithmetic.lessEqual input.t (parameters.1.read 2) then
    let table := BinaryNestedFirstFactoryWork.firstProfileWithWork input K bits
    (BinarySegmentAssembly.padRight table.1 9 0,parameters.2 + firstGuard + table.2)
  else
    let secondGuard := BinaryRationalArithmetic.lessEqualWork (parameters.1.read 1) input.t
    let table := if BinaryRationalArithmetic.lessEqual (parameters.1.read 1) input.t then
      secondBranch input parameters.1 K bits else thirdBranch input parameters.1 K bits
    (table.1,parameters.2 + firstGuard + secondGuard + table.2)

theorem profileWithWork_state (input : Input) (K : ℕ) (bits : Fin K → Bool) :
    (profileWithWork input K bits).1 = BinaryNestedProfileCompiler.profile input K bits := by
  unfold profileWithWork BinaryNestedProfileCompiler.profile
  dsimp only [BinaryNestedParameterWork.prepareWithWork,BinaryNestedProfileCompiler.parameters]
  split
  · exact congrArg (fun table => BinarySegmentAssembly.padRight table 9 0)
      (BinaryNestedFirstFactoryWork.firstProfileWithWork_state input K bits)
  · split
    · exact secondBranch_state input K bits
    · exact thirdBranch_state input K bits

def bound (s K : ℕ) : ℕ := 2304 * BinaryRationalExpression.uniformPrice (height s K 16) +
  2 * compareBound (height s K 16) + BinaryNestedFirstFactoryWork.firstBound (width s K) K + secondBound s K + thirdBound s K

theorem profile_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : InputHeight input s) (K : ℕ) (bits : Fin K → Bool) :
    SegmentHeight (BinaryNestedProfileCompiler.profile input K bits) (height s K 83) := by
  have hf := BinaryNestedFirstFactoryWork.firstProfile_height input hC s hs hH K bits
  unfold BinaryNestedProfileCompiler.profile
  dsimp only
  split
  · exact BinaryAssemblyArithmeticWork.pad_height _ 9 0 _ (height_three (hs.trans (le_max_left _ _)))
      (hf.mono (expressionHeightBudget_mono _ (by decide : 49 ≤ 83)))
  · split
    · exact second_height input hC s hs hH K bits
    · exact third_height input hC s hs hH K bits

theorem profileWithWork_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : InputHeight input s) (K : ℕ) (bits : Fin K → Bool) :
    (profileWithWork input K bits).2 ≤ bound s K := by
  have hi := input_height input s K hH
  have hp := parameter_height input hC s hs hH K
  have hT := hi.2.2.2.2.1.mono (expressionHeightBudget_ge_input _ 16)
  have hP := prepareWork_bound input zero hC zero_canonical _ (hs.trans (le_max_left _ _)) hi
    (zero_height _ (hs.trans (le_max_left _ _)))
  have hg1 := comparator_bound input.t _ hC.2.2.2.2.1 (BinaryNestedProfileCompiler.parameters_canonical input hC 2) _ hT (hp 2)
  have hg2 := comparator_bound _ input.t (BinaryNestedProfileCompiler.parameters_canonical input hC 1) hC.2.2.2.2.1 _ (hp 1) hT
  have hf := BinaryNestedFirstFactoryWork.firstProfileWithWork_bound input hC (width s K) (hs.trans (le_max_left _ _)) hi K bits
  have hSecond := secondBranch_bound input hC s hs hH K bits
  have hThird := thirdBranch_bound input hC s hs hH K bits
  unfold profileWithWork
  dsimp only [BinaryNestedParameterWork.prepareWithWork]
  dsimp only [BinaryNestedProfileCompiler.parameters,height,width] at *
  split_ifs <;> dsimp only <;> unfold bound height width at * <;> omega

end Blotto.BinaryNestedOrderedFactoryWork
