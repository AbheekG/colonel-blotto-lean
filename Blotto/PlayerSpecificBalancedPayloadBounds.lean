import Blotto.PlayerSpecificBalancedPayloadExecution
import Blotto.BinaryPayloadMergeBitWork

/-! Operand widths and caller prices for the actual balanced decoder.
All bounds use its computed block lengths, positions and return values. -/
namespace Blotto.PlayerSpecificBalancedPayloadBounds
open PlayerSpecificRationalTrace PlayerSpecificBalancedPayloadExecution
set_option autoImplicit false
set_option maxHeartbeats 2500000

def width (S : ℕ) : ℕ := 64*(S+1)

theorem result_width (model : RationalCostModel) (buffer : Array Bool) (pos length S : ℕ) (hl : length≤S) :
    binaryWordWidth (run model buffer pos length).1≤S+1 := by
  have hb:=(bounds model buffer pos length).trans_le
    (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show length≤S+1 by omega))
  exact binaryWordWidth_le_of_lt_pow (by omega) hb

theorem small_word (n S : ℕ) (hn : n≤S) : binaryWordWidth n≤S+1 :=
  (control_width n).trans (Nat.add_le_add_right hn 1)

theorem binary_cost (model : RationalCostModel) (op : ℕ → ℕ → ℕ) (a b S : ℕ)
    (ha : binaryWordWidth a≤S+1) (hb : binaryWordWidth b≤S+1) (hc : binaryWordWidth (op a b)≤S+1) :
    (PlayerSpecificNaturalExecution.binary model op a b).2≤64*model.rat (width S) := by
  apply PlayerSpecificNaturalExecution.binary_cost
  all_goals dsimp [width]; omega

theorem frame_cost (model : RationalCostModel) (buffer : Array Bool) (pos length result S : ℕ)
    (hb : buffer.size≤S) (hp : pos≤S) (hl : length≤S) (hr : binaryWordWidth result≤S+1) :
    frame model buffer pos length result≤13*model.rat (width S) := by
  have hw : ∀ n∈[buffer.size,pos,length,result],binaryWordWidth n≤width S := by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    have h : binaryWordWidth n≤S+1 := by
      rcases hn with hn|hn|hn|hn
      · rw [hn]; exact small_word _ S hb
      · rw [hn]; exact small_word _ S hp
      · rw [hn]; exact small_word _ S hl
      · rw [hn]; exact hr
    exact h.trans (by dsimp [width]; omega)
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model [] [buffer.size,pos,length,result] 0 (width S)
    (by simp) (by simp) hw (by dsimp [width]; omega) (by dsimp [width]; omega)
  simp only [List.length_nil,List.length_cons,Nat.mul_zero,Nat.zero_add] at hc
  have hR : S+1≤model.rat (width S) := (by dsimp [width]; omega : S+1≤width S).trans (model.word_le _)
  unfold frame
  omega

theorem shifted_bound (model : RationalCostModel) (buffer : Array Bool) (pos length : ℕ) :
    Nat.shiftLeft (run model buffer (pos+length/2) (length-length/2)).1 (length/2)<2^length := by
  change (run model buffer (pos+length/2) (length-length/2)).1 <<< (length/2)<2^length
  rw [Nat.shiftLeft_eq]
  have hb:=Nat.mul_lt_mul_of_pos_right (bounds model buffer (pos+length/2) (length-length/2)) (Nat.two_pow_pos (length/2))
  have he : length-length/2+length/2=length := by omega
  simpa only [←pow_add,he] using hb

theorem added_bound (model : RationalCostModel) (buffer : Array Bool) (pos length : ℕ) (hl : 1<length) :
    (run model buffer pos (length/2)).1+
      Nat.shiftLeft (run model buffer (pos+length/2) (length-length/2)).1 (length/2)<2^length := by
  change (run model buffer pos (length/2)).1+
    ((run model buffer (pos+length/2) (length-length/2)).1 <<< (length/2))<2^length
  have hb:=BinaryPayload.balancedValue_bounds buffer pos length
  rw [BinaryPayload.merge_value buffer pos length hl] at hb
  simpa only [value] using hb

end Blotto.PlayerSpecificBalancedPayloadBounds
