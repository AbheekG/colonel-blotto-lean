import Blotto.PlayerSpecificModularContract

/-! Executing exact reduced-coefficient zero test, with row reads, controls
and complete original-input source price. -/
namespace Blotto.PlayerSpecificAlgebraicZeroExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1000000

def run (model : RationalCostModel) (a : Data) : Bool×ℕ :=
  (PlayerSpecificAlgebraicZero.run a,price model (copyRow a++[.control a.length,.control 1]))

theorem source_cost (model : RationalCostModel) (a : Data) (hlen : a.length≤3) :
    (run model a).2≤100*model.rat (2*PlayerSpecificRationalMagnitude.inputHeight a+32) := by
  let H:=PlayerSpecificRationalMagnitude.inputHeight a
  let W:=2*H+32
  have hc:=PlayerSpecificExtendedCopyCost.row_cost model a H W (input_height a) (by omega) (by omega) (by omega)
  have hctrl:=PlayerSpecificDenseTraceFits.controls_fits W [a.length,1] (by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl <;> dsimp only [W] <;> omega)
  have hp:=price_bound model W (by dsimp only [W]; omega) _ hctrl
  simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil] at hp
  rw [run,price_append]
  nlinarith only [hc,hp]

theorem actual_contract (model : RationalCostModel) (m a : Data) (hm : Normalized m)
    (hirr : Irreducible (semantics m)) (hml : m.length≤4) (ha : Reduced m a)
    (x : ℝ) (hx : realEvaluate m x=0) :
    ((run model a).1=true ↔ realEvaluate a x=0) ∧
      (run model a).2≤100*model.rat (2*PlayerSpecificRationalMagnitude.inputHeight a+32) := by
  have hl:=ha.2
  exact ⟨PlayerSpecificAlgebraicZero.actual_contract m a hm hirr ha x hx,source_cost model a (by omega)⟩

end Blotto.PlayerSpecificAlgebraicZeroExecution
