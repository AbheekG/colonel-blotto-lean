import Blotto.PlayerSpecificNestedTerminalPreparationExecution

/-! All thirteen original terminal rows, six returned input fields and
the cached focus have derived sizes. No record-height oracle is supplied. -/
namespace Blotto.PlayerSpecificNestedTerminalPreparationFrameCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedTerminalInput PlayerSpecificAlgebraicNestedTerminalSizes PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem raw (root : Candidate) (a : Input) (H : ℕ) (ha : Fits root a H) :
    ∀ j,Reduced root.polynomial ((PlayerSpecificNestedTerminalPreparationExecution.fields a).read j) ∧
      HasHeight ((PlayerSpecificNestedTerminalPreparationExecution.fields a).read j) H := by
  intro j
  fin_cases j
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.budget
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.long 0
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.long 1
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.long 2
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.short 0
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.short 1
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.short 2
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.capacity 0
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.capacity 1
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.capacity 2
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.resource 0
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.resource 1
  · simpa [PlayerSpecificNestedTerminalPreparationExecution.fields,FixedArrayTable.read_ofFn] using ha.resource 2

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hH : 1≤H) (ha : Fits root a H) :
    price RationalCostModel.schoolbook (PlayerSpecificNestedTerminalPreparationExecution.frame root a
      (PlayerSpecificNestedTerminalPreparationExecution.run RationalCostModel.schoolbook root a).1)≤
        (4200*PlayerSpecificResourceCostProfile.rationalCoefficient)*(step H+21)^3 := by
  let model:=RationalCostModel.schoolbook
  let result:=(PlayerSpecificNestedTerminalPreparationExecution.run model root a).1
  let S:=step H+20
  have hbase : H≤step H := (Nat.le_succ _).trans (large H)
  have hHS : H≤S := by dsimp [S]; omega
  have hout : PlayerSpecificAlgebraicNestedParameterSizes.Fits root result.input (step H) := by
    change PlayerSpecificAlgebraicNestedParameterSizes.Fits root (PlayerSpecificNestedTerminalPreparationExecution.run model root a).1.input (step H)
    rw [PlayerSpecificNestedTerminalPreparationExecution.input_value]
    exact bounds model root a H ha hm hm0 hml hmH hH
  have hr:=raw root a H ha
  have ho:=PlayerSpecificAlgebraicNestedParameterSizes.environment_bounds root result.input [] (step H) hout ⟨nil_reduced _ hm0,nil_height _⟩
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model root (PlayerSpecificNestedTerminalPreparationExecution.fields a)
    (PlayerSpecificAlgebraicNestedInput.environment result.input []) S (mono hmH hHS) hml (mono he hHS)
    (fun j => ⟨mono (hr j).2 hHS,by have h:=(hr j).1.2; omega⟩)
    (fun j => ⟨mono (ho j).2 (by dsimp [S]; omega),by have h:=(ho j).1.2; omega⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hf':=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 4200 S)
  rw [show S+1=step H+21 by rfl] at hf'
  exact hf'

end Blotto.PlayerSpecificNestedTerminalPreparationFrameCost
