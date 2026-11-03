import Blotto.GeneralPaperTypedDecodeStorage

/-! Decoded-list packing, reserved copy prefixes and returned/zero rows.
The abstract mutable-reference schedule retains one buffer per fill;
all unused reserved slots, input list cells and scalar/loop-frame reserves
are counted. Primitive arithmetic scratch remains a separate join. -/
namespace Blotto.GeneralPaperRowTrimStorage
open GeneralPaperEncodedLabelStorage GeneralPaperEncodedFixedVector
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def optionalFootprint {m K : ℕ} (W : ℕ) : Option (FixedArrayTable m (Fin K)) → ℕ
  | none => 32*W
  | some row => rowFootprint W row+32*W

theorem optional_bound {m K : ℕ} (W : ℕ) (row : Option (FixedArrayTable m (Fin K))) :
    optionalFootprint W row≤m*(rankWord K+W)+64*W := by
  cases row with
  | none => simp only [optionalFootprint]; omega
  | some row => have h := row_bound W row; dsimp only [optionalFootprint]; omega

theorem packing_prefix {K : ℕ} (W used : ℕ) (labels : List (Fin K)) :
    arrayFootprint W labels.length (ReferenceArrayBuilder.advance used (labels,#[])).2≤
      labels.length*(rankWord K+W)+64*W :=
  array_bound W labels.length _ (PaperListReferenceArray.every_prefix_capacity used labels)

theorem packed {K : ℕ} (index : ℕ → ℕ) (W A : ℕ) (labels : List (Fin K)) :
    arrayFootprint W labels.length (PaperListReferenceArray.run index A labels).1≤
      labels.length*(rankWord K+W)+64*W :=
  array_bound W labels.length _ (PaperListReferenceArray.size index A labels).le

theorem copy_prefix {K : ℕ} (index : ℕ → ℕ) (W A m count : ℕ) (data : Array (Fin K))
    (hm : m≤data.size) (hc : count≤m) :
    arrayFootprint W m (PaperIndexedArrayConstruction.fill index A
      (fun i : Fin m => (data[i.val]'(i.isLt.trans_le hm),64*A)) count hc).1≤m*(rankWord K+W)+64*W :=
  indexed_reserved_prefix index A W count _ hc

theorem copied {K : ℕ} (index : ℕ → ℕ) (W A m : ℕ) (data : Array (Fin K)) (hm : m≤data.size) :
    rowFootprint W (GeneralPaperRowTrimExecution.copyPrefix index A m data hm).1≤m*(rankWord K+W)+32*W :=
  row_bound W _

theorem zero (bits : Bool) (index : ℕ → ℕ) (W A m k : ℕ) :
    rowFootprint W (GeneralPaperZeroRowPrice.run bits index A m k).1≤
      m*(rankWord ((GeneralPaperSourceParameters.prepare k).summarySize+2)+W)+32*W := row_bound W _

theorem zero_prefix (index : ℕ → ℕ) (W A m k count : ℕ) (hc : count≤m) :
    arrayFootprint W m (PaperIndexedArrayConstruction.fill index A
      (fun _ : Fin m => ((0 : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)),64*A)) count hc).1≤
      m*(rankWord ((GeneralPaperSourceParameters.prepare k).summarySize+2)+W)+64*W :=
  indexed_reserved_prefix index A W count _ hc

def loopFrames (W m n : ℕ) : ℕ :=
  (n+m+1)*(64*W+GeneralPaperEncodedScalarStorage.natBits m+GeneralPaperEncodedScalarStorage.natBits n+16)

theorem controls (m n used count : ℕ) (hu : used≤n) (hc : count≤m) :
    GeneralPaperEncodedScalarStorage.natBits used+GeneralPaperEncodedScalarStorage.natBits count≤
      GeneralPaperEncodedScalarStorage.natBits n+GeneralPaperEncodedScalarStorage.natBits m :=
  (Nat.add_le_add (Nat.add_le_add_left (binaryWordWidth_mono hu) 1)
    (Nat.add_le_add_left (binaryWordWidth_mono hc) 1))

def window {K : ℕ} (index : ℕ → ℕ) (W A m : ℕ) (labels : List (Fin K)) : ℕ :=
  listFootprint W labels+arrayFootprint W labels.length (PaperListReferenceArray.run index A labels).1+
    optionalFootprint W (GeneralPaperRowTrimExecution.run index A m labels).1+loopFrames W m labels.length+64*W

def profile (W K m n : ℕ) : ℕ :=
  n*(2*rankWord K+3*W)+m*(rankWord K+W)+224*W+loopFrames W m n

theorem returned_window {K : ℕ} (index : ℕ → ℕ) (W A m : ℕ) (labels : List (Fin K)) :
    window index W A m labels≤profile W K m labels.length := by
  have hl := list_bound W labels.length labels (Nat.le_refl _)
  have ha := packed index W A labels
  have hr := optional_bound W (GeneralPaperRowTrimExecution.run index A m labels).1
  unfold window profile
  nlinarith only [hl,ha,hr]

theorem copying_window {K : ℕ} (index : ℕ → ℕ) (W A m count : ℕ) (labels : List (Fin K))
    (hm : m≤labels.toArray.size) (hc : count≤m) :
    listFootprint W labels+arrayFootprint W labels.length (PaperListReferenceArray.run index A labels).1+
      arrayFootprint W m (PaperIndexedArrayConstruction.fill index A
        (fun i : Fin m => (labels.toArray[i.val]'(i.isLt.trans_le hm),64*A)) count hc).1+
      loopFrames W m labels.length+64*W≤profile W K m labels.length := by
  have hl := list_bound W labels.length labels (Nat.le_refl _)
  have ha := packed index W A labels
  have hc' := copy_prefix index W A m count labels.toArray hm hc
  unfold profile
  nlinarith only [hl,ha,hc']

end Blotto.GeneralPaperRowTrimStorage
