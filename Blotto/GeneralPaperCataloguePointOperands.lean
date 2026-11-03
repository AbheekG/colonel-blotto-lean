import Blotto.GeneralPaperCataloguePointExecution

/-! Sign projection and successor arithmetic use full code words. Actual
signed codes give both raw and projected operands their derived caps.
-/
namespace Blotto.GeneralPaperCataloguePointOperands
open GeneralPaperCataloguePointExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def magnitude (U : ℕ) : ℕ := 8*(U+1)+256
def width (U : ℕ) : ℕ := 128+16*binaryWordWidth (U+1)

theorem word_bound (U : ℕ) : 1+binaryWordWidth (magnitude U)≤width U := by
  have hm := binaryWordWidth_mul 8 (U+1)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (8*(U+1)) 256
  have h8 : binaryWordWidth 8=4 := by decide
  have h256 : binaryWordWidth 256=9 := by decide
  unfold magnitude width
  omega

theorem project_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W U code : ℕ) (hCode : code<2*U) :
    (project primitive W U code).2≤3*primitive (width U)+32*W := by
  let N := magnitude U
  let L := width U
  have hWord := word_bound U
  have w (a : ℕ) (ha : a≤N) : 1+binaryWordWidth a≤L :=
    (Nat.add_le_add_left (binaryWordWidth_mono ha) 1).trans hWord
  have hCmp := GeneralPaperIntegerWordPrice.compare_le primitive hMono code U L
    (w _ (by dsimp [N,magnitude]; omega)) (w _ (by dsimp [N,magnitude]; omega))
  have hSub := (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a-b) code U N
    (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega)).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  change _≤2*primitive L at hSub
  unfold project
  dsimp only
  split <;> change _≤3*primitive L+32*W <;> omega

theorem successor_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W U code : ℕ) (hCode : code<2*U) :
    (successor primitive W U code).2≤5*primitive (width U)+64*W := by
  have hProject := project_work primitive hMono W U code hCode
  have hBound : (project primitive W U code).1<U := by
    rw [project_data]
    exact GeneralPaperUnsignedPartition.project_bound U code hCode
  have hWord := word_bound U
  have hAdd := (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b)
    (project primitive W U code).1 1 (magnitude U)
    (by unfold magnitude; omega) (by unfold magnitude; omega) (by unfold magnitude; omega)).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  unfold successor
  dsimp only
  omega

end Blotto.GeneralPaperCataloguePointOperands
