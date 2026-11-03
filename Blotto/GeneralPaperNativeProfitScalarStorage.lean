import Blotto.GeneralPaperMeshPairStorage

/-! Erased windows for native coefficient and option-profit arithmetic.
All input/output integers, unreduced products, saturating differences and
complete primitive scratch are included. No normalized rational profit or
resource-tag inspection is introduced. -/
namespace Blotto.GeneralPaperNativeProfitScalarStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperNativeProfitScalarPrice
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem source_fields (W m lambda k Qv T mesh : ℕ)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (xs : List ℕ) (hx : ∀ x∈xs,x≤GeneralPaperNativeProfitOperands.cap T Qv mesh) :
    fields W xs≤xs.length*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W := by
  apply fields_bound
  intro x hmem
  have hw : natBits (GeneralPaperNativeProfitOperands.cap T Qv mesh)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    rw [hT,hm]
    exact GeneralPaperNativeProfitOperands.operand_word m lambda k Qv
  exact (Nat.add_le_add_left (binaryWordWidth_mono (hx x hmem)) 1).trans hw

def coefficientWindow (model : RationalCostModel) (W T weight : ℕ) : ℕ :=
  fields W [2,T,2*T,weight,(coefficient model.rat W T weight).1]+(coefficient model.rat W T weight).2+256*W

def coefficientProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  5*(H+W)+32*W+4*model.rat H+64*W+256*W

theorem coefficient_bounded (model : RationalCostModel) (W m lambda k Qv T weight : ℕ)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows) (hw : weight≤Qv) :
    coefficientWindow model W T weight≤coefficientProfile model W m lambda k Qv := by
  let mesh := (GeneralPaperSourceParameters.prepare k).meshDenominator
  have hc := GeneralPaperNativeProfitOperands.cap_large T Qv mesh
  have hp := GeneralPaperNativeProfitOperands.coefficient_bound T Qv mesh weight hw
  have hf := source_fields W m lambda k Qv T mesh hT rfl [2,T,2*T,weight,2*T*weight] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl
    all_goals omega)
  have hprice := coefficient_work model.rat model.monotone W m lambda k Qv T mesh weight hT rfl hw
  change fields W [2,T,2*T,weight,(coefficient model.rat W T weight).1]≤5*(_+W)+32*W at hf
  dsimp only [coefficientWindow,coefficientProfile]
  omega

def profitWindow (model : RationalCostModel) (W coefficient mesh positive negative : ℕ) : ℕ :=
  fields W [coefficient,mesh,positive,negative,mesh+positive,mesh+positive-negative,
    (profit model.rat W coefficient mesh positive negative).1]+
    (profit model.rat W coefficient mesh positive negative).2+256*W

def profitProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  7*(H+W)+32*W+6*model.rat H+64*W+256*W

theorem profit_bounded (model : RationalCostModel) (W m lambda k Qv T mesh weight positive negative : ℕ)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hw : weight≤Qv) (hp : positive≤mesh) (hn : negative≤mesh) :
    profitWindow model W (2*T*weight) mesh positive negative≤profitProfile model W m lambda k Qv := by
  have hc := GeneralPaperNativeProfitOperands.cap_large T Qv mesh
  have hco := GeneralPaperNativeProfitOperands.coefficient_bound T Qv mesh weight hw
  have hpr := (GeneralPaperNativeProfitOperands.profit_bound T Qv mesh weight positive negative hw hp).trans hc.1
  have hf := source_fields W m lambda k Qv T mesh hT hm
    [2*T*weight,mesh,positive,negative,mesh+positive,mesh+positive-negative,2*T*weight*(mesh+positive-negative)] (by
      intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals omega)
  have hprice := profit_work model.rat model.monotone W m lambda k Qv T mesh weight positive negative hT hm hw hp hn
  change fields W [2*T*weight,mesh,positive,negative,mesh+positive,mesh+positive-negative,
    (profit model.rat W (2*T*weight) mesh positive negative).1]≤7*(_+W)+32*W at hf
  dsimp only [profitWindow,profitProfile]
  omega

end Blotto.GeneralPaperNativeProfitScalarStorage
