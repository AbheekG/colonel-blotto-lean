import Blotto.LottoArrayPaths
import Blotto.FourDyadicCoupling

/-! Every bit vector and every branch/descriptor choice of the global
array-resource path has the exact hard budget. The random-choice interpreter
and the cost/encoding refinement remain separate obligations. -/

namespace Blotto
open MeasureTheory

namespace NestedResourceSystem

noncomputable def dyadicPoint (i : NestedResourceSystem) (K : ℕ) (choice : ℕ → Bool) (useFamily : Bool)
    (outerBits innerBits : Fin K → Bool) (slot : Fin 9) (residualSlot : Fin 3) : Allocation 3 :=
  i.point choice useFamily (dyadicMidpointSample K outerBits) (dyadicMidpointSample K innerBits) slot residualSlot

theorem dyadicPoint_contract (i : NestedResourceSystem) (K : ℕ) (choice : ℕ → Bool) (useFamily : Bool)
    (outerBits innerBits : Fin K → Bool) (slot : Fin 9) (residualSlot : Fin 3) :
    FullBudget i.M (i.dyadicPoint K choice useFamily outerBits innerBits slot residualSlot) ∧
      InBox i.long (i.dyadicPoint K choice useFamily outerBits innerBits slot residualSlot) :=
  i.point_contract choice useFamily
    ⟨le_of_lt (dyadicMidpointSample_bounds K outerBits).1, le_of_lt (dyadicMidpointSample_bounds K outerBits).2⟩
    ⟨le_of_lt (dyadicMidpointSample_bounds K innerBits).1, le_of_lt (dyadicMidpointSample_bounds K innerBits).2⟩ slot residualSlot

end NestedResourceSystem

namespace LottoResourceSystem

noncomputable def arrayDyadicPoint {n : ℕ} (i : LottoResourceSystem n) (K : ℕ) (roundChoice : ℕ → Bool)
    (useUniform : Bool) (innerChoice : ℕ → Bool) (useFamily : Bool) (outerBits innerBits : Fin K → Bool)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) : Allocation n :=
  i.runArrayPoint roundChoice useUniform innerChoice useFamily
    (dyadicMidpointSample K outerBits) (dyadicMidpointSample K innerBits) index edge residualEdge

theorem arrayDyadicPoint_fullBudget {n : ℕ} (i : LottoResourceSystem n) (K : ℕ) (roundChoice : ℕ → Bool)
    (useUniform : Bool) (innerChoice : ℕ → Bool) (useFamily : Bool) (outerBits innerBits : Fin K → Bool)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.B (i.arrayDyadicPoint K roundChoice useUniform innerChoice useFamily outerBits innerBits index edge residualEdge) :=
  i.runArrayPoint_fullBudget roundChoice useUniform innerChoice useFamily
    ⟨le_of_lt (dyadicMidpointSample_bounds K outerBits).1, le_of_lt (dyadicMidpointSample_bounds K outerBits).2⟩
    ⟨le_of_lt (dyadicMidpointSample_bounds K innerBits).1, le_of_lt (dyadicMidpointSample_bounds K innerBits).2⟩ index edge residualEdge

end LottoResourceSystem
end Blotto
