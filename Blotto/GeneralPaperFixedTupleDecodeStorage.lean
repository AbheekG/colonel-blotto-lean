import Blotto.GeneralPaperSourceStaticConstructionReachedRates

/-! Native predecessor shape-check and original-label reference-array
materialization. Full input witness, every reserved buffer/constructor
frame, optional returned row and encoded native guard/return work count.
The guarded failure branch allocates no materialization window. -/
namespace Blotto.GeneralPaperFixedTupleDecodeStorage
open GeneralPaperRayAffineMinimum GeneralPaperAffineWitnessStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedReferenceVector
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def rowFoot {m K : ℕ} (W : ℕ) : Option (FixedArrayTable m (Fin K)) → ℕ
  | none => 1
  | some row => 1+footprint W GeneralPaperScoreSelectionStorage.labelBits row.data+32*W

def rowProfile (W m K : ℕ) : ℕ := 1+m*(1+binaryWordWidth K+W)+96*W

theorem row_bound {m K : ℕ} (W : ℕ) (row : Option (FixedArrayTable m (Fin K))) : rowFoot W row≤rowProfile W m K := by
  cases row with
  | none => dsimp only [rowFoot,rowProfile]; omega
  | some row =>
    have h := GeneralPaperEncodedReferenceVector.bounded W (1+binaryWordWidth K) GeneralPaperScoreSelectionStorage.labelBits row.data
      (fun i => GeneralPaperScoreSelectionStorage.label_bound row.data[i.val])
    rw [row.size] at h
    dsimp only [rowFoot,rowProfile]
    omega

def price (W m : ℕ) : ℕ := 96*(m+1)*W
def metadataCap (W m : ℕ) : ℕ := m+1+3*price W m+(8*m+16)*W

def materialWork {K : ℕ} (W m : ℕ) (chosen : Choice K) : ℕ :=
  if chosen.labels.length=m then (PaperListReferenceArray.run (fun w => w) W chosen.labels).2 else 0

def materialWindow {K : ℕ} (W m copied : ℕ) (chosen : Choice K) : ℕ :=
  if chosen.labels.length=m then GeneralPaperListReferenceConstructionStorage.window W copied GeneralPaperScoreSelectionStorage.labelBits chosen.labels else 0

def window {K : ℕ} (W m copied : ℕ) (chosen : Choice K) : ℕ :=
  let result := GeneralPaperFixedTupleDecodePrice.run (fun w => w) W m chosen
  choiceFoot W chosen+materialWindow W m copied chosen+rowFoot W result.1+
    fields W [m,chosen.labels.length,materialWork W m chosen,result.2,(8*chosen.labels.length+16)*W,chosen.labels.length+1]+256*W

def profile (W m K R : ℕ) : ℕ := choiceProfile W K m R+
  GeneralPaperListReferenceConstructionStorage.profile W (1+binaryWordWidth K) m+rowProfile W m K+
    6*(natBits (metadataCap W m)+W)+288*W

theorem bounded {K : ℕ} (W m R copied : ℕ) (chosen : Choice K) (hLen : chosen.labels.length≤m)
    (hi : RationalHeight chosen.expression.intercept R) (hs : RationalHeight chosen.expression.slope R)
    (hW : 1≤W) (hIndex : binaryWordWidth (m+1)≤W) : window W m copied chosen≤profile W m K R := by
  let result := GeneralPaperFixedTupleDecodePrice.run (fun w => w) W m chosen
  have hChoice := choice_bound W m R chosen hLen hi hs
  have hRow := row_bound W result.1
  have hNativeIndex := (binaryWordWidth_mono (Nat.add_le_add_right hLen 1)).trans hIndex
  have hWork := (GeneralPaperFixedTupleDecodePrice.bit_work W m chosen hW hNativeIndex).trans
    (show 96*(chosen.labels.length+1)*W≤price W m by unfold price; gcongr)
  change result.2≤price W m at hWork
  have hMaterial : materialWindow W m copied chosen≤GeneralPaperListReferenceConstructionStorage.profile W (1+binaryWordWidth K) m := by
    unfold materialWindow
    split
    · exact GeneralPaperListReferenceConstructionStorage.bounded W _ m copied GeneralPaperScoreSelectionStorage.labelBits chosen.labels hLen
        (fun l _ => GeneralPaperScoreSelectionStorage.label_bound l) hW hIndex
    · omega
  have hMaterialWork : materialWork W m chosen≤price W m := by
    unfold materialWork
    split
    · have h := PaperListReferenceArray.bit_work W chosen.labels hW hNativeIndex
      exact h.trans (by unfold price; nlinarith only [hLen,Nat.mul_le_mul_right W (Nat.add_le_add_right hLen 1)])
    · omega
  have hTraffic := Nat.mul_le_mul_right W (show 8*chosen.labels.length+16≤8*m+16 by omega)
  have hf := fields_bound W (natBits (metadataCap W m))
    [m,chosen.labels.length,materialWork W m chosen,result.2,(8*chosen.labels.length+16)*W,chosen.labels.length+1] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (metadataCap W m)+W)+32*W at hf
  change choiceFoot W chosen+materialWindow W m copied chosen+rowFoot W result.1+
    GeneralPaperEncodedScalarStorage.fields W [m,chosen.labels.length,materialWork W m chosen,result.2,(8*chosen.labels.length+16)*W,chosen.labels.length+1]+256*W≤_
  unfold profile
  omega

end Blotto.GeneralPaperFixedTupleDecodeStorage
