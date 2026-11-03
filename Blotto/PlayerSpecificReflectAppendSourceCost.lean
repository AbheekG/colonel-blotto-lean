import Blotto.PlayerSpecificReflectAppendExecution

/-! Complete three-coordinate reflection cost, including every source
length, returned row, subtraction and the literal-zero array frame. -/
namespace Blotto.PlayerSpecificReflectAppendSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (T : ℕ) : ℕ :=
  3*(8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(T+1)^3+
  (2200*PlayerSpecificResourceCostProfile.rationalCoefficient)*(step T+11)^3+16

theorem cost (root : Candidate) (long y : FixedArrayTable 3 Data) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hT : 1≤T)
    (hlong : ∀ j,Reduced root.polynomial (long.read j) ∧ HasHeight (long.read j) T)
    (hy : ∀ j,Reduced root.polynomial (y.read j) ∧ HasHeight (y.read j) T) :
    (PlayerSpecificReflectAppendExecution.run RationalCostModel.schoolbook root long y).2≤work T := by
  let model:=RationalCostModel.schoolbook
  let result:=(PlayerSpecificReflectAppendExecution.run model root long y).1
  let S:=step T+10
  let B:=(8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(T+1)^3
  have hTS : T≤S := by dsimp only [S]; have h:=large T; omega
  have hstepS : step T≤S := by dsimp only [S]; omega
  have hsub (j : Fin 3) : price model
      (PlayerSpecificFieldCombination.run true root.polynomial (long.read j) (y.read j)).2≤B := by
    have h:=(PlayerSpecificAlgebraicExpressionPrimitiveCost.binary_cost model root .subtract
      (long.read j) (y.read j) T hm hm0 hml (hlong j).1 (hy j).1 hmT
      (hlong j).2 (hy j).2 hT).trans
        (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 T)
    simp only [PlayerSpecificAlgebraicExpressionExecution.binary] at h
    exact h
  have hresult : ∀ j,Reduced root.polynomial (result.read j) ∧ HasHeight (result.read j) (step T) := by
    intro j
    dsimp only [result]
    rw [PlayerSpecificReflectAppendExecution.value]
    exact PlayerSpecificAlgebraicReflectAppend.bounds root long y T hm hm0 hlong hy j
  have henv : ∀ j,Reduced root.polynomial ((PlayerSpecificReflectAppendExecution.environment long y).read j) ∧
      HasHeight ((PlayerSpecificReflectAppendExecution.environment long y).read j) T := by
    intro j
    fin_cases j
    · simpa [PlayerSpecificReflectAppendExecution.environment,FixedArrayTable.read_ofFn] using hlong 0
    · simpa [PlayerSpecificReflectAppendExecution.environment,FixedArrayTable.read_ofFn] using hlong 1
    · simpa [PlayerSpecificReflectAppendExecution.environment,FixedArrayTable.read_ofFn] using hlong 2
    · simpa [PlayerSpecificReflectAppendExecution.environment,FixedArrayTable.read_ofFn] using hy 0
    · simpa [PlayerSpecificReflectAppendExecution.environment,FixedArrayTable.read_ofFn] using hy 1
    · simpa [PlayerSpecificReflectAppendExecution.environment,FixedArrayTable.read_ofFn] using hy 2
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model root
    (PlayerSpecificReflectAppendExecution.environment long y) result S
    (mono hmT hTS) hml (mono he hTS)
    (fun j => ⟨mono (henv j).2 hTS,by have h:=(henv j).1.2; omega⟩)
    (fun j => ⟨mono (hresult j).2 hstepS,by have h:=(hresult j).1.2; omega⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hframe:=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 2200 S)
  rw [show S+1=step T+11 by rfl] at hframe
  have hthree : price model (PlayerSpecificFieldCombination.run true root.polynomial (long.read 0) (y.read 0)).2+
      price model (PlayerSpecificFieldCombination.run true root.polynomial (long.read 1) (y.read 1)).2+
      price model (PlayerSpecificFieldCombination.run true root.polynomial (long.read 2) (y.read 2)).2≤3*B := by
    have h0:=hsub 0
    have h1:=hsub 1
    have h2:=hsub 2
    omega
  rw [PlayerSpecificReflectAppendExecution.price_equation]
  have hshape : work T=3*B+
      (2200*PlayerSpecificResourceCostProfile.rationalCoefficient)*(step T+11)^3+16 := by
    dsimp only [B]
    simp only [work,Nat.mul_assoc]
  rw [hshape]
  exact Nat.add_le_add_right (Nat.add_le_add hthree hframe) 16

end Blotto.PlayerSpecificReflectAppendSourceCost
