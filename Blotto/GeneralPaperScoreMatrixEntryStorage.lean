import Blotto.GeneralPaperScoreEntryStorage

/-! Complete internal matrix-construction window: one outer reservation,
one current field reservation, both native constructor stacks, the actual
current entry arithmetic and the borrowed field-list container. Physical
column residency is not duplicated. Physical-wrapper metadata is separate. -/
namespace Blotto.GeneralPaperScoreMatrixEntryStorage
open GeneralPaperExactScoreDP GeneralPaperEncodedScalarStorage GeneralPaperEncodedReferenceVector
open GeneralPaperEncodedScoreMatrixStorage GeneralPaperScoreConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

def window {T m K : ℕ} (model : RationalCostModel) (W depth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ)
    (outer : ℕ) (ho : outer≤m) (j : Fin m) (inner : ℕ) (hi : inner≤K) (l : Fin K) : ℕ :=
  reservedFootprint W m (fieldFootprint W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (GeneralPaperScoreMatrixBits.fieldRun model W depth dict v S) outer ho).1+
    reservedFootprint W K (entryFootprint W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (GeneralPaperScoreMatrixBits.entryRun model W depth dict v S j) inner hi).1+
    constructorFrames (fun w => w) W W (GeneralPaperScoreMatrixBits.fieldRun model W depth dict v S) outer ho+
    constructorFrames (fun w => w) W W (GeneralPaperScoreMatrixBits.entryRun model W depth dict v S j) inner hi+
    GeneralPaperScoreEntryStorage.window model W depth dict v S j l+
    listFootprint W (fun _ : Field K => 0) (GeneralPaperScoreMatrixBits.matrixRun model W depth dict v S).1.data.toList+256*W

def profile (model : RationalCostModel) (W depth S V A m K : ℕ) : ℕ :=
  GeneralPaperScoreMatrixConstructionStorage.profile model W depth S V A m K+
    GeneralPaperScoreEntryStorage.profile model W m K S V A depth+256*W

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W depth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (S V A : ℕ)
    (hK : 0<K) (hCap : S<2^depth) (hv : ∀ j,RationalHeight (v.weight j) V)
    (ha : ∀ j l,RationalHeight (dict.anchor j l) A)
    (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W) (hField : binaryWordWidth (m+1)≤W)
    (outer : ℕ) (ho : outer≤m) (j : Fin m) (inner : ℕ) (hi : inner≤K) (l : Fin K) :
    window model W depth dict v S outer ho j inner hi l≤profile model W depth S V A m K := by
  have hM := GeneralPaperScoreMatrixConstructionStorage.matrix_prefix model W depth S A dict v hK hCap ha outer ho
  have hF := GeneralPaperScoreMatrixConstructionStorage.field_prefix model W depth S A dict v hK hCap j (ha j) inner hi
  have hMC := GeneralPaperScoreMatrixConstructionStorage.matrix_frames model W depth S V A dict v hK hCap hv ha hW hLabel hField outer ho
  have hFC := GeneralPaperScoreMatrixConstructionStorage.field_frames model W depth S V A dict v hK hCap j (hv j) (ha j) hW hLabel inner hi
  have hE := GeneralPaperScoreEntryStorage.bounded model W depth dict v S V A hK hCap j (hv j) l (ha j l)
  have hBorrow := borrowed_fields W (GeneralPaperScoreMatrixBits.matrixRun model W depth dict v S).1
  unfold window
  rw [hBorrow]
  have hAll := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add hM hF) hMC) hFC) hE) (m*(2*W)+32*W)) (256*W)
  exact hAll.trans_eq (by unfold profile GeneralPaperScoreMatrixConstructionStorage.profile; ring)

end Blotto.GeneralPaperScoreMatrixEntryStorage
