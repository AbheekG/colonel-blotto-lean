import Blotto.GeneralPaperCircleMetadataExact

/-! Prepare native arc metadata once, then materialize each returned
sweep index in a sized array for rational bid evaluation. The draw consumes
the prepared list; it does not reconstruct or sort metadata again. -/
namespace Blotto.GeneralPaperNativeChoiceArray
set_option autoImplicit false
set_option maxHeartbeats 2200000

structure Prepared (g : ℕ) where
  arcs : List (ℕ×ℕ)
  count : arcs.length=g

def prepare {g : ℕ} (price : ℕ → ℕ) (A R : ℕ) (weights : FixedArrayTable g ℕ) : Prepared g × ℕ :=
  let made := GeneralPaperCircleArcMetadata.run price A R (List.ofFn weights.read) 0
  (⟨made.1.arcs,by rw [GeneralPaperCircleArcMetadata.length,List.length_ofFn]⟩,made.2+32*(g+1)*A)

theorem draw_length {g : ℕ} (model : RationalCostModel) (R W S l : ℕ) (prepared : Prepared g) :
    (GeneralPaperNativeCircleControlDraw.run model R W S l prepared.arcs).1.indices.length=g := by
  unfold GeneralPaperNativeCircleControlDraw.run
  dsimp only
  rw [GeneralPaperCircleCursorSweep.indices_length,prepared.count]

def draw {g : ℕ} (model : RationalCostModel) (R W S l : ℕ) (prepared : Prepared g) : FixedArrayTable g ℕ × ℕ :=
  let chosen := GeneralPaperNativeCircleControlDraw.run model R W S l prepared.arcs
  let stored := PaperListReferenceArray.run (fun _ => 1) 1 chosen.1.indices
  (⟨stored.1,by rw [PaperListReferenceArray.size,draw_length]⟩,chosen.2+stored.2+16)

theorem selected_data {g : ℕ} (model : RationalCostModel) (price : ℕ → ℕ) (A R W S : ℕ)
    (hR : 0<R) (hW : 0<W) (hS : 0<S) (l : Fin S) (weights : FixedArrayTable g ℕ)
    (hs : ∑ j,weights.read j=W) :
    (draw model R W S l.val (prepare price A R weights).1).1=FixedArrayTable.ofFn (fun j =>
      (GeneralPaperCircleCell.choice R W hR hW
        (GeneralPaperCircleCell.cell (R*W) (Nat.mul_pos hR hW)
          (GeneralPaperSelectedShift.selected (R*W) S (Nat.mul_pos hR hW) hS l).val
            (GeneralPaperCircleArcPartition.before (GeneralPaperCircleHardBudget.lengths R weights.read) j.val))
              (R*weights.read j)).val) := by
  unfold draw
  dsimp only
  congr 1
  rw [PaperListReferenceArray.data]
  change (GeneralPaperNativeCircleControlDraw.run model R W S l.val
    (GeneralPaperCircleArcMetadata.run price A R (List.ofFn weights.read) 0).1.arcs).1.indices.toArray=_
  rw [GeneralPaperCircleMetadataExact.selected_indices model price A R W S hR hW hS l weights hs]
  exact List.toArray_ofFn

theorem bounded {g : ℕ} (model : RationalCostModel) (price : ℕ → ℕ) (A R W S : ℕ)
    (hR : 0<R) (hW : 0<W) (hS : 0<S) (l : Fin S) (weights : FixedArrayTable g ℕ)
    (hs : ∑ j,weights.read j=W) (j : Fin g) :
    (draw model R W S l.val (prepare price A R weights).1).1.read j<R := by
  rw [selected_data model price A R W S hR hW hS l weights hs,FixedArrayTable.read_ofFn]
  exact (GeneralPaperCircleCell.choice R W hR hW _ _).isLt

theorem arithmetic_work {g : ℕ} (model : RationalCostModel) (price : ℕ → ℕ) (A R W S l : ℕ)
    (hR : 0<R) (hW : 0<W) (hS : 0<S) (hl : l<S) (weights : FixedArrayTable g ℕ)
    (hs : ∑ j,weights.read j=W) :
    (draw model R W S l (prepare price A R weights).1).2≤
      1024*(binaryWordWidth (R*W)+1)+24*R+100*g+100 := by
  have hSum : (List.ofFn weights.read).sum=W := by rw [List.sum_ofFn];exact hs
  have hControl := GeneralPaperNativeCircleControlDraw.arithmetic_work model price A R W S l hR hW hS hl
    (List.ofFn weights.read) hSum
  have hStore := PaperListReferenceArray.arithmetic_work
    (GeneralPaperNativeCircleControlDraw.run model R W S l (prepare price A R weights).1.arcs).1.indices
  rw [draw_length] at hStore
  rw [List.length_ofFn] at hControl
  change (GeneralPaperNativeCircleControlDraw.run model R W S l (prepare price A R weights).1.arcs).2≤
    1024*(binaryWordWidth (R*W)+1)+24*R+36*g+20 at hControl
  change (GeneralPaperNativeCircleControlDraw.run model R W S l (prepare price A R weights).1.arcs).2+
    (PaperListReferenceArray.run (fun _ => 1) 1
      (GeneralPaperNativeCircleControlDraw.run model R W S l (prepare price A R weights).1.arcs).1.indices).2+16≤_
  omega

end Blotto.GeneralPaperNativeChoiceArray
