import Blotto.PlayerSpecificNestedRestoreSourceCost

/-! Complete terminal nested draw caches one prepared input/focus,
runs the closed nested sampler once and restores its finite focus. -/
namespace Blotto.PlayerSpecificNestedTerminalDrawExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedTerminalInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin ((17*H+K)+K) → Bool) : FixedArrayTable 3 Data×ℕ :=
  let prepared:=PlayerSpecificNestedTerminalPreparationExecution.run model root a
  let sampled:=PlayerSpecificNestedSpecDrawExecution.run model root prepared.1.input H K bits
  let restored:=PlayerSpecificNestedRestoreExecution.run model root prepared.1.focus sampled.1
  (restored.1,prepared.2+sampled.2+restored.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (bits : Fin ((17*H+K)+K) → Bool) :
    (run model root a H K bits).1=PlayerSpecificAlgebraicNestedTerminalDraw.draw model root a H K bits := by
  simp only [run,PlayerSpecificNestedRestoreExecution.value,PlayerSpecificNestedTerminalPreparationExecution.input_value,
    PlayerSpecificNestedTerminalPreparationExecution.focus_value,PlayerSpecificNestedSpecDrawExecution.value,
    PlayerSpecificAlgebraicNestedTerminalDraw.draw,PlayerSpecificAlgebraicNestedTerminalInput.prepare]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl
theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (bits : Fin ((17*H+K)+K) → Bool) :
    (run model root a H K bits).2=(PlayerSpecificNestedTerminalPreparationExecution.run model root a).2+
      (PlayerSpecificNestedSpecDrawExecution.run model root (PlayerSpecificNestedTerminalPreparationExecution.run model root a).1.input H K bits).2+
      (PlayerSpecificNestedRestoreExecution.run model root (PlayerSpecificNestedTerminalPreparationExecution.run model root a).1.focus
        (PlayerSpecificNestedSpecDrawExecution.run model root (PlayerSpecificNestedTerminalPreparationExecution.run model root a).1.input H K bits).1).2+2 := by
  simp only [run,packing]

end Blotto.PlayerSpecificNestedTerminalDrawExecution
