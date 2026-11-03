import Blotto.GeneralPaperEncodedScoreMatrixStorage

/-! Actual matrix-constructor reservations and native prefix-work metadata.
The outer matrix and current field are each reserved once. Entry arithmetic
scratch is separate; this file covers constructed payloads, descriptors,
references, prefix-work counters and the borrowed DP field-list container. -/
namespace Blotto.GeneralPaperScoreMatrixConstructionStorage
open GeneralPaperExactScoreDP GeneralPaperEncodedScalarStorage GeneralPaperEncodedReferenceVector
open GeneralPaperEncodedScoreMatrixStorage GeneralPaperScoreConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

theorem entry_return {T m K : ℕ} (model : RationalCostModel) (W depth S A : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (hK : 0<K) (hCap : S<2^depth)
    (j : Fin m) (l : Fin K) (ha : RationalHeight (dict.anchor j l) A) :
    entryFootprint W (GeneralPaperScoreMatrixBits.entryRun model W depth dict v S j l).1≤entryProfile W S A := by
  rw [GeneralPaperScoreMatrixBits.entry_data model W depth dict v S hK hCap j l]
  exact entry_bound W S A _ (score_bound v S hK j l) ha

theorem field_prefix {T m K : ℕ} (model : RationalCostModel) (W depth S A : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (hK : 0<K) (hCap : S<2^depth)
    (j : Fin m) (ha : ∀ l,RationalHeight (dict.anchor j l) A) (count : ℕ) (hc : count≤K) :
    reservedFootprint W K (entryFootprint W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (GeneralPaperScoreMatrixBits.entryRun model W depth dict v S j) count hc).1≤fieldProfile W K S A :=
  indexed_reserved_prefix (fun w => w) W W (entryProfile W S A) (entryFootprint W) _
    (fun l => entry_return model W depth S A dict v hK hCap j l (ha l)) count hc

theorem matrix_prefix {T m K : ℕ} (model : RationalCostModel) (W depth S A : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (hK : 0<K) (hCap : S<2^depth)
    (ha : ∀ j l,RationalHeight (dict.anchor j l) A) (count : ℕ) (hc : count≤m) :
    reservedFootprint W m (fieldFootprint W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (GeneralPaperScoreMatrixBits.fieldRun model W depth dict v S) count hc).1≤matrixProfile W m K S A :=
  indexed_reserved_prefix (fun w => w) W W (fieldProfile W K S A) (fieldFootprint W) _
    (fun j => native_field model W depth S A dict v hK hCap j (ha j)) count hc

theorem field_frames {T m K : ℕ} (model : RationalCostModel) (W depth S V A : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (hK : 0<K) (hCap : S<2^depth)
    (j : Fin m) (hv : RationalHeight (v.weight j) V) (ha : ∀ l,RationalHeight (dict.anchor j l) A)
    (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W) (count : ℕ) (hc : count≤K) :
    constructorFrames (fun w => w) W W (GeneralPaperScoreMatrixBits.entryRun model W depth dict v S j) count hc≤
      constructorProfile W K (GeneralPaperScoreMatrixBits.fieldProfile model W V A depth K) :=
  constructor_bound (fun w => w) W W _ _
    (GeneralPaperScoreMatrixBits.field_work model W depth dict v S V A hK hCap j hv ha hW hLabel) count hc

theorem matrix_frames {T m K : ℕ} (model : RationalCostModel) (W depth S V A : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (hK : 0<K) (hCap : S<2^depth)
    (hv : ∀ j,RationalHeight (v.weight j) V) (ha : ∀ j l,RationalHeight (dict.anchor j l) A)
    (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W) (hField : binaryWordWidth (m+1)≤W)
    (count : ℕ) (hc : count≤m) :
    constructorFrames (fun w => w) W W (GeneralPaperScoreMatrixBits.fieldRun model W depth dict v S) count hc≤
      constructorProfile W m (GeneralPaperScoreMatrixBits.matrixProfile model W V A depth m K) :=
  constructor_bound (fun w => w) W W _ _
    (GeneralPaperScoreMatrixBits.matrix_work model W depth dict v S V A hK hCap hv ha hW hLabel hField) count hc

def profile (model : RationalCostModel) (W depth S V A m K : ℕ) : ℕ :=
  matrixProfile W m K S A+fieldProfile W K S A+
    constructorProfile W K (GeneralPaperScoreMatrixBits.fieldProfile model W V A depth K)+
    constructorProfile W m (GeneralPaperScoreMatrixBits.matrixProfile model W V A depth m K)+
    m*(2*W)+32*W

end Blotto.GeneralPaperScoreMatrixConstructionStorage
