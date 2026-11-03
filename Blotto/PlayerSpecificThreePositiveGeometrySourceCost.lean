import Blotto.PlayerSpecificThreePositiveGeometryExecution

/-! Complete geometry-continuation source work is polynomial in raw
row height; environment/table heights are derived internally. -/
namespace Blotto.PlayerSpecificThreePositiveGeometrySourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
open PlayerSpecificAlgebraicThreeEnvironmentSizes PlayerSpecificAlgebraicDescriptorBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environmentCoefficient : ℕ := PlayerSpecificThreeEnvironmentSourceCost.coefficient*20^3
def tableCoefficient : ℕ := PlayerSpecificThreeGeometrySourceCost.coefficient*
  ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3+27)^3
def coefficient : ℕ := environmentCoefficient+tableCoefficient+PlayerSpecificThreePreparationInputs.frameCoefficient

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificThreePositiveGeometryExecution.run RationalCostModel.schoolbook root a).2≤coefficient*(H+1)^3 := by
  let model:=RationalCostModel.schoolbook
  let env:=PlayerSpecificThreeEnvironmentExecution.run model root a
  let result:=PlayerSpecificThreePositiveGeometryExecution.run model root a
  let T:=PlayerSpecificAlgebraicHeightEnvelope.iterate 3 H
  have hbase : H≤T := PlayerSpecificAlgebraicExpressionBudget.initial_le 3 H
  have henvH : ∀ j,HasHeight (env.1.read j) T := by
    rw [PlayerSpecificThreeEnvironmentExecution.value]
    exact environment_height root a H ha hm hm0 hml hmH (by omega)
  have henvRed : ∀ j,Reduced root.polynomial (env.1.read j) := by
    rw [PlayerSpecificThreeEnvironmentExecution.value]
    exact environment_reduced root a hm hm0
  have hec:=PlayerSpecificThreeEnvironmentSourceCost.cost root a H hm hm0 hml hmH he hv (by omega) ha
  have heQ : env.2≤environmentCoefficient*(H+1)^3 :=
    hec.trans (PlayerSpecificThreePreparationInputs.transfer _ 20 H (H+20) (by omega))
  have htc:=PlayerSpecificThreeGeometrySourceCost.cost root env.1 T hm hm0 hml (mono hmH hbase) (mono he hbase) hv
    (hH.trans hbase) (fun j => ⟨henvRed j,henvH j⟩)
  have htQ : (PlayerSpecificThreeGeometryExecution.run model root env.1).2≤tableCoefficient*(H+1)^3 :=
    htc.trans (PlayerSpecificThreePreparationInputs.transfer _ _ H (T+27) (PlayerSpecificThreePreparationInputs.shift 3 H 27))
  have hred:=PlayerSpecificAlgebraicThreeGeometry.reduced model root env.1 hm hm0 henvRed
  have hheight:=PlayerSpecificAlgebraicThreeGeometry.heights model root env.1 hm hm0 hml T (mono hmH hbase)
    (hH.trans hbase) (fun j => ⟨henvRed j,henvH j⟩)
  have hreturn : result.1=(PlayerSpecificThreeGeometryExecution.run model root env.1).1 := rfl
  have hd : Bounds root result.1 (PlayerSpecificAlgebraicHeightEnvelope.iterate 20 H) := by
    rw [hreturn,PlayerSpecificThreeGeometryExecution.value]
    change (∀ slot,HasHeight _ (PlayerSpecificAlgebraicHeightEnvelope.iterate 17 (PlayerSpecificAlgebraicHeightEnvelope.iterate 3 H))) ∧ _ at hheight
    rw [iterate_add] at hheight
    exact ⟨fun slot => ⟨hred.1 slot,hheight.1 slot⟩,fun slot j => ⟨hred.2.1 slot j,hheight.2.1 slot j⟩,
      fun slot j => ⟨hred.2.2 slot j,hheight.2.2 slot j⟩⟩
  have hf:=PlayerSpecificThreePreparationInputs.frame_polynomial root a result.1 H hmH hml he ha hd
  exact (Nat.add_le_add (Nat.add_le_add heQ htQ) hf).trans_eq (by
    change environmentCoefficient*(H+1)^3+tableCoefficient*(H+1)^3+PlayerSpecificThreePreparationInputs.frameCoefficient*(H+1)^3=
      (environmentCoefficient+tableCoefficient+PlayerSpecificThreePreparationInputs.frameCoefficient)*(H+1)^3
    ring)

end Blotto.PlayerSpecificThreePositiveGeometrySourceCost
