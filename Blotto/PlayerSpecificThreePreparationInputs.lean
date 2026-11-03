import Blotto.PlayerSpecificOverlapRowSourceCost

/-! Shared derived raw-input and returned-descriptor frames for actual
three-variable preparation. These certificates never enter execution. -/
namespace Blotto.PlayerSpecificThreePreparationInputs
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
open PlayerSpecificAlgebraicThreeEnvironmentSizes PlayerSpecificAlgebraicDescriptorBounds PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem raw {root : Candidate} {a : Input} {H : ℕ} (ha : Fits root a H) :
    ∀ j,Reduced root.polynomial ((PlayerSpecificThreeEnvironmentExecution.input a).read j) ∧
      HasHeight ((PlayerSpecificThreeEnvironmentExecution.input a).read j) H := by
  intro j
  fin_cases j
  · simpa [PlayerSpecificThreeEnvironmentExecution.input,FixedArrayTable.read_ofFn] using ha.budget
  · simpa [PlayerSpecificThreeEnvironmentExecution.input,FixedArrayTable.read_ofFn] using ha.first
  · simpa [PlayerSpecificThreeEnvironmentExecution.input,FixedArrayTable.read_ofFn] using ha.second
  · simpa [PlayerSpecificThreeEnvironmentExecution.input,FixedArrayTable.read_ofFn] using ha.third
  · simpa [PlayerSpecificThreeEnvironmentExecution.input,FixedArrayTable.read_ofFn] using ha.probability

theorem frame (model : RationalCostModel) (root : Candidate) (a : Input) (d : Descriptor 3 9) (S : ℕ)
    (hm : HasHeight root.polynomial S) (hml : root.polynomial.length≤4) (he : HasHeight [root.interval.lo,root.interval.hi] S)
    (ha : Fits root a S) (hd : Bounds root d S) (hS : 9≤S) :
    price model (PlayerSpecificDescriptorProgramExecution.frame root (PlayerSpecificThreeEnvironmentExecution.input a) d)≤
      69000*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  have hraw:=raw ha
  have hrow : ∀ row∈PlayerSpecificDescriptorProgramExecution.rows d,HasHeight row S ∧ row.length≤3 := by
    refine PlayerSpecificDescriptorProgramFrameCost.rows_property d (fun row => HasHeight row S ∧ row.length≤3) ?_ ?_ ?_
    · intro slot; exact ⟨(hd.weights slot).2,by have h:=(hd.weights slot).1.2; omega⟩
    · intro slot j; exact ⟨(hd.first slot j).2,by have h:=(hd.first slot j).1.2; omega⟩
    · intro slot j; exact ⟨(hd.second slot j).2,by have h:=(hd.second slot j).1.2; omega⟩
  exact PlayerSpecificDescriptorProgramFrameCost.cost model root (PlayerSpecificThreeEnvironmentExecution.input a) d S hm hml he
    (fun j => ⟨(hraw j).2,by have h:=(hraw j).1.2; omega⟩) hrow (by omega) (by omega) hS (by omega)

theorem mono (root : Candidate) (a : Input) (T S : ℕ) (ha : Fits root a T) (h : T≤S) : Fits root a S :=
  ⟨⟨ha.budget.1,PlayerSpecificPolynomialHeights.mono ha.budget.2 h⟩,
    ⟨ha.first.1,PlayerSpecificPolynomialHeights.mono ha.first.2 h⟩,
    ⟨ha.second.1,PlayerSpecificPolynomialHeights.mono ha.second.2 h⟩,
    ⟨ha.third.1,PlayerSpecificPolynomialHeights.mono ha.third.2 h⟩,
    ⟨ha.probability.1,PlayerSpecificPolynomialHeights.mono ha.probability.2 h⟩⟩

theorem shift (D H c : ℕ) : PlayerSpecificAlgebraicHeightEnvelope.iterate D H+c≤
    ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^D+c)*(H+1) := by
  have hi:=PlayerSpecificAlgebraicHeightEnvelope.iterate_bound D H
  nlinarith only [hi,Nat.zero_le (c*H)]

theorem transfer (C B H X : ℕ) (h : X≤B*(H+1)) : C*X^3≤(C*B^3)*(H+1)^3 := by
  exact (Nat.mul_le_mul_left C (Nat.pow_le_pow_left h 3)).trans_eq (by ring)

def frameCoefficient : ℕ := (69000*PlayerSpecificResourceCostProfile.rationalCoefficient)*
  ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^20)^3

theorem frame_polynomial (root : Candidate) (a : Input) (d : Descriptor 3 9) (H : ℕ)
    (hm : HasHeight root.polynomial H) (hml : root.polynomial.length≤4) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (ha : Fits root a H) (hd : Bounds root d (PlayerSpecificAlgebraicHeightEnvelope.iterate 20 H)) :
    price RationalCostModel.schoolbook (PlayerSpecificDescriptorProgramExecution.frame root (PlayerSpecificThreeEnvironmentExecution.input a) d)≤
      frameCoefficient*(H+1)^3 := by
  let S:=PlayerSpecificAlgebraicHeightEnvelope.iterate 20 H
  have hbase : H≤S := PlayerSpecificAlgebraicExpressionBudget.initial_le 20 H
  have hstep : PlayerSpecificAlgebraicHeightEnvelope.step H≤S := PlayerSpecificAlgebraicExpressionBudget.fuel_mono H (by decide : 1≤20)
  have h9 : 9≤S := by
    have hc:=PlayerSpecificAlgebraicHeightEnvelope.calibrate 9 H (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
    nlinarith only [hc,hstep,Nat.zero_le H]
  have hf:=frame RationalCostModel.schoolbook root a d S (PlayerSpecificPolynomialHeights.mono hm hbase) hml
    (PlayerSpecificPolynomialHeights.mono he hbase) (mono root a H S ha hbase) hd h9
  have hpad : 69000*RationalCostModel.schoolbook.rat (PlayerSpecificAlgebraicComparisonExecution.width S)≤
      69000*(S+1)*RationalCostModel.schoolbook.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
    apply Nat.mul_le_mul_right _
    omega
  exact ((hf.trans hpad).trans (PlayerSpecificResourceCostProfile.cubic 69000 S)).trans
    (transfer _ _ H (S+1) (PlayerSpecificAlgebraicHeightEnvelope.iterate_bound 20 H))

end Blotto.PlayerSpecificThreePreparationInputs
