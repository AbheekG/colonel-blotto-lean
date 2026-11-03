import Blotto.RationalThreeGeometryCode
import Blotto.RationalThreeWeights

/-! Counted programs for all native three-variable segment-weight tables,
including zero slots and both ordered branch comparisons. -/

namespace Blotto.RationalThreeGeometryCode

def first : Fin 9 → Expr :=
  ![(.div (.mul (.mul W G) R) (.mul (.mul (.mul A C) E) F)),
    (.div (.mul (.mul (.sub U W) G) R) (.mul (.mul (.mul A C) E) F)),
    (.literal 0),
    (.literal 0),
    (.div (.mul (.sub V W) H) (.mul C E)),
    (.div (.mul W H) (.mul C E)),
    (.div (.mul (.mul W (.sub U V)) R) (.mul (.mul (.mul A C) E) F)),
    (.div H C),
    (.div (.mul (.mul V W) (.add (.add U V) (.mul (.literal 2) H))) (.mul (.mul A C) F))]

def second : Fin 9 → Expr :=
  ![(.div (.mul W G) (.mul A F)),
    (.div (.mul (.sub U W) S) (.mul (.mul (.mul A C) E) F)),
    (.div (.mul V H) (.mul C E)),
    (.literal 0),
    (.literal 0),
    (.literal 0),
    (.div (.mul W (.sub U V)) (.mul A F)),
    (.div H C),
    (.div (.mul V W) (.mul A F))]

def third : Fin 9 → Expr :=
  ![(.literal 0),
    (.div (.mul V (.sub W U)) (.mul C E)),
    (.div (.mul V F) (.mul C E)),
    (.div (.mul U G) (.mul C E)),
    (.div (.mul U (.sub W V)) (.mul C E)),
    (.literal 0),
    (.literal 0),
    (.div H C),
    (.literal 0)]

def chosen (slot : Fin 9) : Expr :=
  .ifLe W V (first slot) (.ifLe W U (second slot) (third slot))

theorem first_value (g : RationalThreeGeometry) (slot : Fin 9) :
    (first slot).value (environment g) = g.firstWeights slot := by
  fin_cases slot <;> simp [first, RationalThreeGeometry.firstWeights]

theorem second_value (g : RationalThreeGeometry) (slot : Fin 9) :
    (second slot).value (environment g) = g.secondWeights slot := by
  fin_cases slot <;> simp [second, RationalThreeGeometry.secondWeights]

theorem third_value (g : RationalThreeGeometry) (slot : Fin 9) :
    (third slot).value (environment g) = g.thirdWeights slot := by
  fin_cases slot <;> simp [third, RationalThreeGeometry.thirdWeights]

theorem chosen_value (g : RationalThreeGeometry) (slot : Fin 9) :
    (chosen slot).value (environment g) = g.chosenWeights slot := by
  by_cases h1 : g.w ≤ g.v
  · simp [chosen, RationalThreeGeometry.chosenWeights, h1, first_value]
  · by_cases h2 : g.w ≤ g.u
    · simp [chosen, RationalThreeGeometry.chosenWeights, h1, h2, second_value]
    · simp [chosen, RationalThreeGeometry.chosenWeights, h1, h2, third_value]

theorem chosen_operationBound (slot : Fin 9) : (chosen slot).operationBound ≤ 256 := by
  fin_cases slot <;> decide

theorem chosen_depth (slot : Fin 9) : (chosen slot).depth ≤ 16 := by
  fin_cases slot <;> decide

end Blotto.RationalThreeGeometryCode
