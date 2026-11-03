import Blotto.PlayerSpecificModularHeights

/-! Actual modular Horner execution: scaled row, shifted reduced tail,
padded addition and actual remainder division, with complete copies. -/
namespace Blotto.PlayerSpecificModularExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def frame (m b a result : Data) : Trace :=
  copyRow m++copyRow b++copyRow a++copyRow result++[.control a.length]

def run (model : RationalCostModel) (m b : Data) : Data → Data×ℕ
  | [] => ([],price model (frame m b [] []))
  | c::cs =>
    let rest:=run model m b cs
    let scaled:=PlayerSpecificDenseExecution.scale c b
    let shifted:=PlayerSpecificDenseExecution.shift rest.1
    let added:=PlayerSpecificDenseExecution.add scaled.1 shifted.1
    let divided:=PlayerSpecificDivisionExecution.run added.1 m
    let result:=divided.1.2
    (result,rest.2+price model scaled.2+price model shifted.2+price model added.2+
      price model divided.2+price model (frame m b (c::cs) result))

theorem value (model : RationalCostModel) (m b a : Data) : (run model m b a).1=PlayerSpecificModularHorner.run m b a := by
  induction a with
  | nil => rfl
  | cons c cs ih =>
    simp only [run,PlayerSpecificDivisionExecution.value,PlayerSpecificDenseExecution.add_value,
      PlayerSpecificDenseExecution.shift_value,PlayerSpecificDenseExecution.scale_value,ih,
      PlayerSpecificModularHorner.run,PlayerSpecificModularHorner.input,PlayerSpecificAlgebraicReduction.reduce]

end Blotto.PlayerSpecificModularExecution
