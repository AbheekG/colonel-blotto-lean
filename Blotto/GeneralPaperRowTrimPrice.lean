import Blotto.GeneralPaperRowTrimExecution

/-! Trim costs use actual decoded-list and retained size bounds. Array
guards and every copyPrefix write are included; no length census executes. -/
namespace Blotto.GeneralPaperRowTrimPrice
open GeneralPaperRowTrimExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem copy_work {α : Type*} (index : ℕ → ℕ) (A m : ℕ) (data : Array α) (hm : m≤data.size)
    (hA : 1≤A) (hIndex : ∀ i≤m,index (binaryWordWidth (i+1))≤A) :
    (copyPrefix index A m data hm).2≤64*m*A+44*(m+1)*A := by
  have h := GeneralPaperControlArrayPrice.indexed_work index A (64*A)
    (fun i : Fin m => (data[i.val]'(i.isLt.trans_le hm),64*A)) hA hIndex (fun _ => Nat.le_refl _)
  change (PaperIndexedArrayConstruction.run index A (fun i : Fin m => (data[i.val]'(i.isLt.trans_le hm),64*A))).2≤_
  nlinarith only [h]

def word (W m cap : ℕ) : ℕ := arrayWord W (max m cap+2)
def profile (W m cap : ℕ) : ℕ :=
  64*(cap+1)*word W m cap+64*m*word W m cap+44*(m+1)*word W m cap+65*word W m cap

theorem work {α : Type*} (W m cap : ℕ) (labels : List α) (hLen : labels.length≤cap) :
    (run (fun x => x) (word W m cap) m labels).2≤profile W m cap := by
  let A := word W m cap
  let packed := PaperListReferenceArray.run (fun x => x) A labels
  have hA : 1≤A := GeneralPaperSummaryArrayControls.array_word_positive W (max m cap+2)
  have hLength : packed.1.size=labels.length := PaperListReferenceArray.size _ _ _
  have bounded (x : ℕ) (hx : x≤max m cap+1) : 1+binaryWordWidth x≤A := by
    have h := binaryWordWidth_mono (show x≤(max m cap+2)+1 by omega)
    unfold A word arrayWord
    omega
  have hmWord := bounded m (by have := le_max_left m cap; omega)
  have hlWord := bounded packed.1.size (by have := le_max_right m cap; omega)
  have hPacked := PaperListReferenceArray.bit_work A labels hA (by
    have h := bounded (labels.length+1) (by have := le_max_right m cap; omega)
    omega)
  have hGuard := GeneralPaperIntegerWordPrice.compare_le (fun x => x) (fun _ _ h => h) m packed.1.size A hmWord hlWord
  unfold run
  dsimp only
  split
  · rename_i hm
    have hPrefix := copy_work (fun x => x) A m packed.1 hm hA (by
      intro i hi
      have h := bounded (i+1) (by have := le_max_left m cap; omega)
      omega)
    change packed.2+(copyPrefix (fun x => x) A m packed.1 hm).2+
      GeneralPaperIntegerWordPrice.compare (fun x => x) m packed.1.size+64*A≤_
    unfold profile
    change _≤64*(cap+1)*A+64*m*A+44*(m+1)*A+65*A
    nlinarith only [hPacked,hGuard,hPrefix,Nat.mul_le_mul_right (64*A) (Nat.add_le_add_right hLen 1)]
  · change packed.2+GeneralPaperIntegerWordPrice.compare (fun x => x) m packed.1.size+64*A≤_
    unfold profile
    change _≤64*(cap+1)*A+64*m*A+44*(m+1)*A+65*A
    nlinarith only [hPacked,hGuard,Nat.mul_le_mul_right (64*A) (Nat.add_le_add_right hLen 1),Nat.zero_le (m*A)]

theorem arithmetic_work {α : Type*} (m cap : ℕ) (labels : List α) (hLen : labels.length≤cap) :
    (run (fun _ => 1) 1 m labels).2≤64*cap+108*m+173 := by
  let packed := PaperListReferenceArray.run (fun _ => 1) 1 labels
  have hPacked := PaperListReferenceArray.arithmetic_work labels
  unfold run
  dsimp only
  split
  · rename_i hm
    have hPrefix := copy_work (fun _ => 1) 1 m packed.1 hm (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    change packed.2+(copyPrefix (fun _ => 1) 1 m packed.1 hm).2+1+64≤_
    nlinarith only [hPacked,hPrefix,hLen]
  · change packed.2+1+64≤_
    nlinarith only [hPacked,hLen]

end Blotto.GeneralPaperRowTrimPrice
