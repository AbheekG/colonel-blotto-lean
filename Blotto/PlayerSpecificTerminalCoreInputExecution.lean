import Blotto.PlayerSpecificTerminalCoreDrawSourceCost
import Blotto.PlayerSpecificTerminalPreparationPolynomial
import Blotto.PlayerSpecificAlgebraicTerminalCorePreparationSizes

/-! The measured terminal-core input retains the reached grouping,
materializes three group totals, and divides only a present fractional row. -/
namespace Blotto.PlayerSpecificTerminalCoreInputExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicResourceState
open PlayerSpecificAlgebraicTerminalPreparation PlayerSpecificAlgebraicTerminalCoreInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def resultRows (a : Input) : FixedArrayTable 6 Data :=
  FixedArrayTable.ofFn ![a.budget,a.lengths.read 0,a.lengths.read 1,a.lengths.read 2,
    (a.fractional.map Prod.fst).getD [],(a.fractional.map Prod.snd).getD []]

def frame {N : ℕ} (root : PlayerSpecificAlgebraicCandidates.Candidate)
    (g : Prepared N) (a : Input) : Trace :=
  PlayerSpecificExpressionVectorExecution.frame root (resultRows a) (resultRows a) ++
    [Event.control N,Event.control g.groups.length,
      Event.control (if g.fractional.isSome then 1 else 0),
      Event.control 0,Event.control 1,Event.control 2]

def fromPrepared {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (g : Prepared N) : Input × ℕ :=
  let model := RationalCostModel.schoolbook
  let budget := PlayerSpecificFieldCombinationContract.constant p.parameters.root.polynomial B
  let lengths : FixedArrayTable 3 Data := FixedArrayTable.ofFn (fun j =>
    ((g.groups[j.val]?).map (fun h => h.total)).getD [])
  let fraction : Option (Data × Data) × ℕ :=
    match g.fractional with
    | none => (none,0)
    | some j =>
      let ell := (p.rows.read j).length
      let divided := PlayerSpecificAlgebraicExpressionExecution.binary model p.parameters.root .divide
        (s.data.read j) ell
      (some (ell,divided.1),divided.2)
  let a : Input := ⟨budget.1,lengths,g.groups.length,fraction.1⟩
  (a,price model budget.2+fraction.2+price model (frame p.parameters.root g a)+price model [.control 1])

theorem fromPrepared_value {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (g : Prepared N) :
    (fromPrepared p s B g).1 = PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g := by
  unfold fromPrepared PlayerSpecificAlgebraicTerminalCoreInput.prepare
  cases hf : g.fractional with
  | none =>
    simp [PlayerSpecificFieldCombinationContract.constant_value]
  | some j =>
    simp [PlayerSpecificFieldCombinationContract.constant_value,
      PlayerSpecificAlgebraicExpressionExecution.binary_value]

def run {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) : Input × ℕ :=
  let g := PlayerSpecificTerminalPreparationExecution.run RationalCostModel.schoolbook p s B
  let a := fromPrepared p s B g.1
  (a.1,g.2+a.2+price RationalCostModel.schoolbook [.control 1])

theorem value {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) :
    (run p s B).1 = PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B
      (PlayerSpecificAlgebraicTerminalPreparation.prepare RationalCostModel.schoolbook p s B) := by
  simp only [run,fromPrepared_value,PlayerSpecificTerminalPreparationExecution.value]

end Blotto.PlayerSpecificTerminalCoreInputExecution
