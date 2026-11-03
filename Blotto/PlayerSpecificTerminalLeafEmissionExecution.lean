import Blotto.PlayerSpecificTerminalCoreMeasuredSourceCost
import Blotto.PlayerSpecificAlgebraicTerminalLeafBounds
import Blotto.PlayerSpecificExpressionVectorFrameCost

/-! Measured original-coordinate leaf emission. Each uniform coordinate
executes its own division by the cached group total and product by the
sampled group allocation. The optional fractional coordinate is copied.
The source trace includes every returned original-coordinate row. -/
namespace Blotto.PlayerSpecificTerminalLeafEmissionExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicGrouping PlayerSpecificAlgebraicLeafAssignments
set_option autoImplicit false
set_option maxHeartbeats 2500000

def member {N : ℕ} (model : RationalCostModel)
    (root : PlayerSpecificAlgebraicCandidates.Candidate) (length : Fin N → Data)
    (groups : List (Group N)) (y : FixedArrayTable 4 Data)
    (g : Fin groups.length) (j : Fin N) : (Fin N × Data) × ℕ :=
  let quotient := PlayerSpecificAlgebraicExpressionExecution.binary model root .divide
    (length j) (groups.get g).total
  let product := PlayerSpecificAlgebraicExpressionExecution.binary model root .multiply
    quotient.1 (y.read (slot g))
  ((j,product.1),quotient.2+product.2+
    price model [.control g.val,.control j.val,.control 1])

theorem member_value {N : ℕ} (model : RationalCostModel)
    (root : PlayerSpecificAlgebraicCandidates.Candidate) (length : Fin N → Data)
    (groups : List (Group N)) (y : FixedArrayTable 4 Data)
    (g : Fin groups.length) (j : Fin N) :
    (member model root length groups y g j).1 =
      (j,PlayerSpecificAlgebraicField.times root.polynomial
        (PlayerSpecificAlgebraicField.divide root.polynomial (length j) (groups.get g).total)
        (y.read (slot g))) := by
  simp only [member,PlayerSpecificAlgebraicExpressionExecution.binary_value]

def measured {N : ℕ} (model : RationalCostModel)
    (root : PlayerSpecificAlgebraicCandidates.Candidate) (length : Fin N → Data)
    (groups : List (Group N)) (y : FixedArrayTable 4 Data) :
    List ((Fin N × Data) × ℕ) :=
  (List.finRange groups.length).flatMap (fun g =>
    (groups.get g).members.map (member model root length groups y g))

theorem measured_value {N : ℕ} (model : RationalCostModel)
    (root : PlayerSpecificAlgebraicCandidates.Candidate) (length : Fin N → Data)
    (groups : List (Group N)) (y : FixedArrayTable 4 Data) :
    (measured model root length groups y).map Prod.fst = assignments root length groups y := by
  simp only [measured,assignments,List.map_flatMap,List.map_map]
  congr 1
  funext g
  congr 1
  funext j
  exact member_value model root length groups y g j

def fromCore {N : ℕ} (model : RationalCostModel)
    (root : PlayerSpecificAlgebraicCandidates.Candidate) (length : Fin N → Data)
    (groups : List (Group N)) (fractional : Option (Fin N))
    (y : FixedArrayTable 4 Data) : FixedArrayTable N Data × ℕ :=
  let entries := measured model root length groups y
  let uniform := (FixedArrayTable.ofFn (fun _ => ([] : Data))).patch (entries.map Prod.fst)
  let result := match fractional with
    | none => uniform
    | some j => uniform.write j (y.read 3)
  (result,(entries.map Prod.snd).sum+
    price model (PlayerSpecificExpressionVectorExecution.frame root
      (FixedArrayTable.ofFn length) result)+
    price model [.control N,.control groups.length,
      .control (if fractional.isSome then 1 else 0)])

theorem fromCore_value {N : ℕ} (model : RationalCostModel)
    (root : PlayerSpecificAlgebraicCandidates.Candidate) (length : Fin N → Data)
    (groups : List (Group N)) (fractional : Option (Fin N))
    (y : FixedArrayTable 4 Data) :
    (fromCore model root length groups fractional y).1 =
      emitMixed root length groups fractional y := by
  simp only [fromCore,measured_value,emitMixed,emit]
  cases fractional <;> rfl

end Blotto.PlayerSpecificTerminalLeafEmissionExecution
