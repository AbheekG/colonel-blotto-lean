import Blotto.PlayerSpecificFourMergedDrawSourceCost
import Blotto.PlayerSpecificAlgebraicFourReflectedSizes

/-! The reflected component caches its parameter table and each of the
three short lengths, capacities and initial resource amounts once. -/
namespace Blotto.PlayerSpecificFourReflectedInputExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicFourReflectedInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def fields (p : Prepared) : FixedArrayTable 16 Data := FixedArrayTable.ofFn
  ![p.long.read 0,p.long.read 1,p.long.read 2,
    p.short.read 0,p.short.read 1,p.short.read 2,
    (p.resources.rows.read 0).length,(p.resources.rows.read 1).length,(p.resources.rows.read 2).length,
    (p.resources.rows.read 0).initialA,(p.resources.rows.read 1).initialA,(p.resources.rows.read 2).initialA,
    (p.resources.rows.read 0).initialB,(p.resources.rows.read 1).initialB,(p.resources.rows.read 2).initialB,
    p.budget]
def packing : Trace := .control 6::List.replicate 14 (.control 1)

def run (model : RationalCostModel) (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) : Prepared×ℕ :=
  let root:=r.root
  let p:=PlayerSpecificFourParameterExecution.run model root a
  let long:=original a
  let shortCalls:=FixedArrayTable.ofFn (fun j => PlayerSpecificMixtureScalarExecution.scale model root (p.1.read 4) (long.read j))
  let short:=FixedArrayTable.ofFn (fun j => (shortCalls.read j).1)
  let capacityCalls:=FixedArrayTable.ofFn (fun j => PlayerSpecificMixtureScalarExecution.scale model root (p.1.read 5) (long.read j))
  let capacity:=FixedArrayTable.ofFn (fun j => (capacityCalls.read j).1)
  let initialCalls:=FixedArrayTable.ofFn (fun j => PlayerSpecificMixtureScalarExecution.scale model root (p.1.read 6) (capacity.read j))
  let rows:=FixedArrayTable.ofFn (fun j =>
    (⟨capacity.read j,(initialCalls.read j).1,(initialCalls.read j).1⟩ : PlayerSpecificAlgebraicInitial.Result))
  let result:Prepared:=⟨⟨r,[],rows⟩,long,short,p.1.read 7⟩
  (result,p.2+(∑ j : Fin 3,(shortCalls.read j).2)+
    (∑ j : Fin 3,(capacityCalls.read j).2)+
    (∑ j : Fin 3,(initialCalls.read j).2)+
    price model (PlayerSpecificExpressionVectorExecution.frame root (environment a) (fields result))+
    price model packing)

theorem value (model : RationalCostModel) (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) :
    (run model r a).1=prepare model r a := by
  simp only [run,PlayerSpecificFourParameterExecution.value,
    PlayerSpecificMixtureScalarExecution.scale_value,FixedArrayTable.read_ofFn,
    prepare]

theorem packing_cost (model : RationalCostModel) : price model packing=32 := rfl

theorem price_equation (model : RationalCostModel) (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) :
    (run model r a).2=(PlayerSpecificFourParameterExecution.run model r.root a).2+
      (∑ j : Fin 3,(PlayerSpecificMixtureScalarExecution.scale model r.root
        ((parameters model r.root a).read 4) ((original a).read j)).2)+
      (∑ j : Fin 3,(PlayerSpecificMixtureScalarExecution.scale model r.root
        ((parameters model r.root a).read 5) ((original a).read j)).2)+
      (∑ j : Fin 3,(PlayerSpecificMixtureScalarExecution.scale model r.root
        ((parameters model r.root a).read 6)
          (PlayerSpecificAlgebraicField.times r.root.polynomial ((parameters model r.root a).read 5) ((original a).read j))).2)+
      price model (PlayerSpecificExpressionVectorExecution.frame r.root (environment a) (fields (run model r a).1))+32 := by
  simp only [run,PlayerSpecificFourParameterExecution.value,
    PlayerSpecificMixtureScalarExecution.scale_value,FixedArrayTable.read_ofFn,packing_cost]

end Blotto.PlayerSpecificFourReflectedInputExecution
