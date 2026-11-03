import Blotto.GeneralPaperNativeProfitOperands

/-! One shared coefficient per field, then three integer operations per
option. These routines evaluate native nonnegative profit numerators without
forming normalized rational profits or inspecting stored resource tags.
-/
namespace Blotto.GeneralPaperNativeProfitScalarPrice
open GeneralPaperNativeProfitOperands
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def coefficient (price : ℕ → ℕ) (W T weight : ℕ) : ℕ × ℕ :=
  let doubled := 2*T
  (doubled*weight,GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 T+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) doubled weight+64*W)

def profit (price : ℕ → ℕ) (W coefficient mesh positive negative : ℕ) : ℕ × ℕ :=
  let sum := mesh+positive
  let amount := sum-negative
  (coefficient*amount,GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) mesh positive+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) sum negative+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) coefficient amount+64*W)

theorem coefficient_data (price : ℕ → ℕ) (W T weight : ℕ) : (coefficient price W T weight).1=2*T*weight := rfl
theorem profit_data (price : ℕ → ℕ) (W coefficient mesh positive negative : ℕ) :
    (profit price W coefficient mesh positive negative).1=coefficient*(mesh+positive-negative) := rfl

theorem coefficient_work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv T mesh weight : ℕ)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hWeight : weight≤Qv) :
    (coefficient price W T weight).2≤4*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+64*W := by
  have hc := cap_large T Qv mesh
  have hw : 1+binaryWordWidth (cap T Qv mesh)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    rw [hT,hMesh]; exact operand_word m lambda k Qv
  have hp := coefficient_bound T Qv mesh weight hWeight
  have h1 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) 2 T (cap T Qv mesh)
    hc.2.2.2.2.2 (by omega) hc.2.2.1
  have h2 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) (2*T) weight (cap T Qv mesh)
    hc.2.2.1 (hWeight.trans hc.2.2.2.2.1) hp.2
  have h : (coefficient price W T weight).2≤4*price (1+binaryWordWidth (cap T Qv mesh))+64*W := by
    change GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 T+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) (2*T) weight+64*W≤_
    omega
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (hMono hw)) _)

theorem profit_work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv T mesh weight positive negative : ℕ)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hWeight : weight≤Qv) (hPositive : positive≤mesh) (hNegative : negative≤mesh) :
    (profit price W (2*T*weight) mesh positive negative).2≤6*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+64*W := by
  have hc := cap_large T Qv mesh
  have hw : 1+binaryWordWidth (cap T Qv mesh)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    rw [hT,hMesh]; exact operand_word m lambda k Qv
  have hSum : mesh+positive≤cap T Qv mesh := (by omega : mesh+positive≤2*mesh).trans hc.2.2.2.1
  have h1 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) mesh positive (cap T Qv mesh)
    (by omega) (by omega) hSum
  have h2 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a-b) (mesh+positive) negative (cap T Qv mesh)
    hSum (by omega) ((Nat.sub_le _ _).trans hSum)
  have h3 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) (2*T*weight) (mesh+positive-negative) (cap T Qv mesh)
    (coefficient_bound T Qv mesh weight hWeight).2 ((Nat.sub_le _ _).trans hSum)
    ((profit_bound T Qv mesh weight positive negative hWeight hPositive).trans hc.1)
  have h : (profit price W (2*T*weight) mesh positive negative).2≤6*price (1+binaryWordWidth (cap T Qv mesh))+64*W := by
    change GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) mesh positive+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) (mesh+positive) negative+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) (2*T*weight) (mesh+positive-negative)+64*W≤_
    omega
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 6 (hMono hw)) _)

theorem coefficient_arithmetic (T weight : ℕ) : (coefficient (fun _ => 1) 1 T weight).2=68 := rfl
theorem profit_arithmetic (coefficient mesh positive negative : ℕ) : (profit (fun _ => 1) 1 coefficient mesh positive negative).2=70 := rfl

end Blotto.GeneralPaperNativeProfitScalarPrice
