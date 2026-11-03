import Blotto.GeneralPaperExpressionSubstitution

/-! Fixed literal programs for the entire unsorted three-input segment
lottery. Their syntax depends only on slot/coordinate labels, not on values.
The five runtime inputs are the budget, three lengths and final mixture. -/
namespace Blotto.GeneralPaperThreeStaticPrograms
open GeneralPaperExpressionSubstitution (bind)
set_option autoImplicit false
set_option maxHeartbeats 1600000
abbrev Expr := RationalExpression 5

def orderedInputs : Fin 5 → Expr :=
  ![.input 0, .minimum (.input 1) (.input 2), .maximum (.input 1) (.input 2), .input 3, .input 4]

def parameters (j : Fin 4) : Expr := bind orderedInputs (RationalThreeInputCode.parameters j)
def regime : Expr := bind orderedInputs RationalThreeInputCode.regime

def orderedWeight (slot : Fin 9) : Expr :=
  .ifLe regime (.literal 0) (.literal (if slot = 0 then 1 else 0))
    (bind parameters (RationalThreeGeometryCode.chosen slot))

def exceptionalLeft (j : Fin 3) : Expr := ![.literal 0, .literal 0, .input 0] j
def exceptionalRight (j : Fin 3) : Expr := ![orderedInputs 1, orderedInputs 2, .literal 0] j

def orderedLeft (slot : Fin 9) (j : Fin 3) : Expr :=
  .ifLe regime (.literal 0) (exceptionalLeft j)
    (bind parameters (RationalThreeGeometryCode.vertex (RationalThreeGeometry.edges slot).1 j))

def orderedRight (slot : Fin 9) (j : Fin 3) : Expr :=
  .ifLe regime (.literal 0) (exceptionalRight j)
    (bind parameters (RationalThreeGeometryCode.vertex (RationalThreeGeometry.edges slot).2 j))

def swapped (j : Fin 3) : Fin 3 := ![1, 0, 2] j
def left (slot : Fin 9) (j : Fin 3) : Expr :=
  .ifLe (.input 1) (.input 2) (orderedLeft slot j) (orderedLeft slot (swapped j))
def right (slot : Fin 9) (j : Fin 3) : Expr :=
  .ifLe (.input 1) (.input 2) (orderedRight slot j) (orderedRight slot (swapped j))

theorem ordered_environment (i : RationalThreeSpec) :
    FixedArrayTable.ofFn (fun j => ((orderedInputs j).run (RationalThreeSpecCode.environment i)).1) =
      RationalThreeInputCode.environment i.orderedInput := by
  apply GeneralPaperNativeQuantizedLabels.table_ext
  intro j
  fin_cases j <;> rfl

theorem regime_value (i : RationalThreeSpec) :
    (regime.run (RationalThreeSpecCode.environment i)).1 = i.orderedInput.a + i.orderedInput.d - i.orderedInput.B := by
  rw [regime, GeneralPaperExpressionSubstitution.data, ordered_environment]
  exact RationalThreeInputCode.regime_value i.orderedInput

theorem parameter_value (i : RationalThreeSpec) (hE : 0 < i.orderedInput.a + i.orderedInput.d - i.orderedInput.B)
    (j : Fin 4) :
    ((parameters j).run (RationalThreeSpecCode.environment i)).1 =
      (RationalThreeGeometryCode.environment (i.orderedInput.geometry hE)).read j := by
  rw [parameters, GeneralPaperExpressionSubstitution.data, ordered_environment]
  exact RationalThreeInputCode.parameter_value i.orderedInput hE j

theorem geometry_environment (i : RationalThreeSpec) (hE : 0 < i.orderedInput.a + i.orderedInput.d - i.orderedInput.B) :
    FixedArrayTable.ofFn (fun j => ((parameters j).run (RationalThreeSpecCode.environment i)).1) =
      RationalThreeGeometryCode.environment (i.orderedInput.geometry hE) := by
  apply GeneralPaperNativeQuantizedLabels.table_ext
  intro j
  rw [FixedArrayTable.read_ofFn]
  exact parameter_value i hE j

end Blotto.GeneralPaperThreeStaticPrograms
