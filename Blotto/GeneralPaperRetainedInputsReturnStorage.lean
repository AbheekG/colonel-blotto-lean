import Blotto.GeneralPaperInitializerGridReturnStorage

/-! Literal retained-input parent and complete returned input record.
Original H/p/q, full parameter/auxiliary/grid/matrix owners, selected/initial
owners and six parent work/branch fields coexist. Shared prepared dictionary
and original source-label owners remain with the enclosing caller. -/
namespace Blotto.GeneralPaperRetainedInputsReturnStorage
open RationalOrderCell GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint)
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def controlFoot (W H p q : ℕ) (selected : GeneralPaperInitializerParameters.Parameters×ℤ) : ℕ :=
  natBits H+natBits p+natBits q+GeneralPaperInitializerControlStorage.parameterFoot W selected.1+integerBits selected.2
def recordFoot {T m K : ℕ} (W : ℕ) (inputs : GeneralPaperSharedBasisInputs.Inputs T m K) : ℕ :=
  GeneralPaperInitializerControlStorage.parameterFoot W inputs.controls+integerBits inputs.betaN+
    arrayFootprint W integerBits inputs.initialGrid+GeneralPaperEncodedScoreMatrixStorage.matrixFootprint W inputs.matrix+64*W
def metadataCap (W A B : ℕ) : ℕ := A+B+128*W+1
def controls {T m K S : ℕ} (model : RationalCostModel) (W H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) : List ℕ :=
  let selected := GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal
  let initial := GeneralPaperRetainedBasisInputs.grid true model W selected.1.1.N selected.1.1.depth prep.dictionary
  let result := GeneralPaperRetainedBasisInputs.run true model W H p q reciprocal prep matrix
  [selected.2,initial.2,result.2,64*W,selected.2+initial.2,GeneralPaperFinalStaticLoopStorage.bit reciprocal]
def window {T m K S : ℕ} (model : RationalCostModel) (W H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) : ℕ :=
  let selected := GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal
  let initial := GeneralPaperRetainedBasisInputs.grid true model W selected.1.1.N selected.1.1.depth prep.dictionary
  let result := GeneralPaperRetainedBasisInputs.run true model W H p q reciprocal prep matrix
  recordFoot W result.1+controlFoot W H p q selected.1+arrayFootprint W integerBits initial.1.2+
    GeneralPaperEncodedScoreMatrixStorage.matrixFootprint W matrix+fields W (controls model W H p q reciprocal prep matrix)+128*W
def profile (W Bcontrol Bgrid Bmatrix A B : ℕ) : ℕ :=
  2*Bcontrol+2*Bgrid+2*Bmatrix+6*(natBits (metadataCap W A B)+W)+224*W

theorem work {T m K S : ℕ} (model : RationalCostModel) (W H p q A B : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (hSelected : (GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal).2≤A)
    (hInitial : (GeneralPaperRetainedBasisInputs.grid true model W
      (GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal).1.1.N
      (GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal).1.1.depth prep.dictionary).2≤B) :
    (GeneralPaperRetainedBasisInputs.run true model W H p q reciprocal prep matrix).2≤A+B+64*W := by
  change (GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal).2+_+64*W≤_
  omega

theorem bounded {T m K S : ℕ} (model : RationalCostModel) (W H p q Bcontrol Bgrid Bmatrix A B : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (hControl : controlFoot W H p q (GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal).1≤Bcontrol)
    (hGrid : arrayFootprint W integerBits (GeneralPaperRetainedBasisInputs.grid true model W
      (GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal).1.1.N
      (GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal).1.1.depth prep.dictionary).1.2≤Bgrid)
    (hMatrix : GeneralPaperEncodedScoreMatrixStorage.matrixFootprint W matrix≤Bmatrix)
    (hSelected : (GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal).2≤A)
    (hInitial : (GeneralPaperRetainedBasisInputs.grid true model W
      (GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal).1.1.N
      (GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal).1.1.depth prep.dictionary).2≤B) :
    window model W H p q reciprocal prep matrix≤profile W Bcontrol Bgrid Bmatrix A B := by
  let selected := GeneralPaperRetainedBasisInputs.controls true model W m H p q reciprocal
  let initial := GeneralPaperRetainedBasisInputs.grid true model W selected.1.1.N selected.1.1.depth prep.dictionary
  let result := GeneralPaperRetainedBasisInputs.run true model W H p q reciprocal prep matrix
  change controlFoot W H p q selected.1≤Bcontrol at hControl
  change arrayFootprint W integerBits initial.1.2≤Bgrid at hGrid
  have hRecord : recordFoot W result.1≤Bcontrol+Bgrid+Bmatrix+64*W := by
    unfold recordFoot
    change GeneralPaperInitializerControlStorage.parameterFoot W selected.1.1+integerBits selected.1.2+
      arrayFootprint W integerBits initial.1.2+GeneralPaperEncodedScoreMatrixStorage.matrixFootprint W matrix+64*W≤_
    unfold controlFoot at hControl
    omega
  have hWork := work model W H p q A B reciprocal prep matrix hSelected hInitial
  change result.2≤A+B+64*W at hWork
  have hb := GeneralPaperFinalStaticLoopStorage.bit_bound reciprocal
  change selected.2≤A at hSelected
  change initial.2≤B at hInitial
  have hf := fields_bound W (natBits (metadataCap W A B)) (controls model W H p q reciprocal prep matrix) (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    change z∈[selected.2,initial.2,result.2,64*W,selected.2+initial.2,GeneralPaperFinalStaticLoopStorage.bit reciprocal] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold metadataCap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W (controls model W H p q reciprocal prep matrix)≤6*(natBits (metadataCap W A B)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [result,selected,initial] at hRecord hControl hGrid
  omega

end Blotto.GeneralPaperRetainedInputsReturnStorage
