import Blotto.GeneralPaperSignedCutExecution

/-! Cut code operands, endpoint indices and native annotation construction
have derived words. V is the unsigned alphabet bound U at actual callers.
-/
namespace Blotto.GeneralPaperSignedCutOperands
open GeneralPaperSignedCutExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def magnitude (m U : ℕ) : ℕ := 128*(m+1)+4*(U+1)+256
def width (m U : ℕ) : ℕ := 256+16*(binaryWordWidth (m+2)+binaryWordWidth (U+1))

theorem word_bound (m U : ℕ) : 1+binaryWordWidth (magnitude m U)≤width m U := by
  have hm := binaryWordWidth_mul 128 (m+1)
  have hu := binaryWordWidth_mul 4 (U+1)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (128*(m+1)) (4*(U+1))
  have hb := GeneralPaperRayOperandWidthEnvelope.word_add (128*(m+1)+4*(U+1)) 256
  have hn := binaryWordWidth_mono (show m+1≤m+2 by omega)
  have h128 : binaryWordWidth 128=8 := by decide
  have h4 : binaryWordWidth 4=3 := by decide
  have h256 : binaryWordWidth 256=9 := by decide
  unfold magnitude width
  omega

theorem element_work {m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) (hQueries : ∀ q,queries.read q≤U) (i : Fin (m+1)) :
    (element primitive W U negative queries i).2≤3*primitive (width m U)+64*W := by
  let N := magnitude m U
  let L := width m U
  have hWord := word_bound m U
  have w (a : ℕ) (ha : a≤N) : 1+binaryWordWidth a≤L :=
    (Nat.add_le_add_left (binaryWordWidth_mono ha) 1).trans hWord
  have hIndex := i.isLt
  have hCmp := GeneralPaperIntegerWordPrice.compare_le primitive hMono i.val m L
    (w _ (by dsimp [N,magnitude]; omega)) (w _ (by dsimp [N,magnitude]; omega))
  have price (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤N) (hb : b≤N) (hc : op a b≤N) :
      GeneralPaperNaturalPrimitivePrice.binary primitive op a b≤2*primitive L :=
    (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono op a b N ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  unfold element
  dsimp only
  split
  · rename_i hi
    have hq := hQueries ⟨i.val,hi⟩
    have hAdd := price (fun a b => a+b) U (queries.read ⟨i.val,hi⟩)
      (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega)
    cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    all_goals change _≤3*primitive L+64*W; omega
  · have hMul := price (fun a b => a*b) 2 U
      (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega)
    cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    all_goals change _≤3*primitive L+64*W; omega

theorem annotation_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (m U : ℕ) :
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) m 1+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 54 (m+1)+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (54*(m+1)) 18≤6*primitive (width m U) := by
  let N := magnitude m U
  let L := width m U
  have hWord := word_bound m U
  have price (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤N) (hb : b≤N) (hc : op a b≤N) :
      GeneralPaperNaturalPrimitivePrice.binary primitive op a b≤2*primitive L :=
    (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono op a b N ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  have ha := price (fun a b => a+b) m 1
    (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega)
  have hb := price (fun a b => a*b) 54 (m+1)
    (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega)
  have hc := price (fun a b => a+b) (54*(m+1)) 18
    (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega)
  change _≤6*primitive L
  omega

end Blotto.GeneralPaperSignedCutOperands
