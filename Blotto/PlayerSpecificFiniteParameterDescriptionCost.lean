import Blotto.PlayerSpecificFiniteParameterDescription

/-! Concrete original-input polynomial bounds include the actual binary
description, all framing/header/accumulated-buffer work and the complete
recognizer. No encoded-length or serializer-work oracle is supplied. -/
namespace Blotto.PlayerSpecificFiniteParameterDescriptionCost
open PlayerSpecificRationalTrace PlayerSpecificFiniteParameterBudget
open PlayerSpecificFiniteParameterDescription
set_option autoImplicit false
set_option maxHeartbeats 2500000

def preparationBound (N L : ℕ) : ℕ :=
  (workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient))*work N L*size N L^2

theorem bit_length {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (run i).bits.length≤4*preparationBound N (inputSize i)+3 := by
  have hs:=PlayerSpecificFiniteParameterCost.polynomial_cost i
  have hf:=frame_price_le RationalCostModel.schoolbook i
  have hl:=PlayerSpecificCopyFrame.encoded_length
    (PlayerSpecificFiniteParameterExecution.frame i (run i).parameters) (frame_pure i _)
  have hm:=Nat.mul_le_mul_left 4 (hf.trans hs)
  exact hl.trans (Nat.add_le_add_right hm 3)

theorem encoding_work {N : ℕ} (i : RationalPlayerSpecificInput N) :
    PlayerSpecificCopyFrameCost.work (PlayerSpecificFiniteParameterExecution.frame i (run i).parameters)≤
      1000*(preparationBound N (inputSize i)+2)^3 := by
  have hs:=PlayerSpecificFiniteParameterCost.polynomial_cost i
  have hf:=frame_price_le RationalCostModel.schoolbook i
  have hc:=PlayerSpecificCopyFrameCost.source_work
    (PlayerSpecificFiniteParameterExecution.frame i (run i).parameters) (frame_pure i _)
  exact hc.trans (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (Nat.add_le_add_right (hf.trans hs) 2) 3))

theorem total_work {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (run i).work≤preparationBound N (inputSize i)+1000*(preparationBound N (inputSize i)+2)^3 := by
  have hs:=PlayerSpecificFiniteParameterCost.polynomial_cost i
  have he:=encoding_work i
  exact Nat.add_le_add hs he

theorem actual_resources {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (run i).bits.length≤4*preparationBound N (inputSize i)+3 ∧
      (run i).work≤preparationBound N (inputSize i)+1000*(preparationBound N (inputSize i)+2)^3 ∧
      PlayerSpecificCopyFrame.read (run i).bits=some
        (PlayerSpecificFiniteParameterExecution.frame i (run i).parameters,[]) := by
  refine ⟨bit_length i,total_work i,?_⟩
  simpa only [List.append_nil] using decoded i []

end Blotto.PlayerSpecificFiniteParameterDescriptionCost
