import Blotto.BinaryNestedFirstFactoryWork

/-! Actual family substitution computes its stored probability before the
retained first-case producer. All produced operand/table heights and primitive
prices follow the actual original input and selected stored family length. -/

namespace Blotto.BinaryNestedFamilyFactoryWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryNestedParameters BinaryNestedComponents
open BinaryNestedParameterWork BinaryFactoryHeight

def familyWithWork (input : Input) (length : SignedWord) (K : ℕ) (bits : Fin K → Bool) :
    BinaryStoredOverlapEnvironment.Segment 3 9 × ℕ :=
  let parameters := BinaryNestedParameterWork.prepareWithWork input length
  let family : Input := ⟨input.M,input.a,input.d,input.c,length,parameters.1.read 5⟩
  let table := BinaryNestedFirstFactoryWork.firstProfileWithWork family K bits
  (table.1,parameters.2 + table.2)

theorem familyWithWork_state (input : Input) (length : SignedWord) (K : ℕ) (bits : Fin K → Bool) :
    (familyWithWork input length K bits).1 = familyLottery input length K bits := by
  unfold familyWithWork familyLottery familyInput
  rw [BinaryNestedFirstFactoryWork.firstProfileWithWork_state,BinaryNestedParameterWork.prepareWithWork_state]

theorem family_input_height (input : Input) (length : SignedWord) (hC : input.Canonical) (hL : CanonicalWord length)
    (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) (hLength : RationalHeight (value length) s) :
    InputHeight (familyInput input length) (expressionHeightBudget s 16) := by
  have hm := expressionHeightBudget_ge_input s 16
  exact ⟨hH.1.mono hm,hH.2.1.mono hm,hH.2.2.1.mono hm,hH.2.2.2.1.mono hm,hLength.mono hm,
    prepare_height input length hC hL s hs hH hLength 5⟩

def bound (s K : ℕ) : ℕ := 2304 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) +
  BinaryNestedFirstFactoryWork.firstBound (expressionHeightBudget s 16) K

theorem familyWithWork_bound (input : Input) (length : SignedWord) (hC : input.Canonical) (hL : CanonicalWord length)
    (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) (hLength : RationalHeight (value length) s)
    (K : ℕ) (bits : Fin K → Bool) : (familyWithWork input length K bits).2 ≤ bound s K := by
  have hParameters := prepareWork_bound input length hC hL s hs hH hLength
  have hFamily := family_input_height input length hC hL s hs hH hLength
  have hProfile := BinaryNestedFirstFactoryWork.firstProfileWithWork_bound (familyInput input length)
    (familyInput_canonical input length hC hL) _ (height_three hs) hFamily K bits
  exact Nat.add_le_add hParameters hProfile

end Blotto.BinaryNestedFamilyFactoryWork
