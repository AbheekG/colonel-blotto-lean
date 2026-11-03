import Blotto.PlayerSpecificAlgebraicNestedFirstReference

/-! A single fixed-depth envelope covers both actually selected first
nested table branches, including every cached shifted endpoint. -/
namespace Blotto.PlayerSpecificAlgebraicNestedFirstSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem zero (root : Candidate) (a : Input) (extra : Data) (T : ℕ) (hfit : Fits root a T)
    (hExtra : Reduced root.polynomial extra ∧ HasHeight extra T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) :
    Bounds root (PlayerSpecificAlgebraicNestedFirstTable.zero root a extra) (iterate 22 T) := by
  have hbase : T≤ iterate 22 T := PlayerSpecificAlgebraicExpressionBudget.initial_le 22 T
  have hstep : step T≤ iterate 22 T := PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (show 1≤22 by omega)
  constructor
  · intro slot
    simp only [PlayerSpecificAlgebraicNestedFirstTable.zero,FixedArrayTable.read_ofFn]
    refine ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,?_⟩
    apply mono (constant_height root.polynomial _ T hmT _ (by omega) hml) hstep
    split
    · exact one_height.mono (by omega)
    · exact zero_height.mono (by omega)
  · intro slot j
    fin_cases j <;> simp only [PlayerSpecificAlgebraicNestedFirstTable.zero,FixedArrayTable.read_ofFn]
    · exact ⟨nil_reduced _ hm0,nil_height _⟩
    · exact ⟨hfit.second.1,mono hfit.second.2 hbase⟩
    · exact ⟨hExtra.1,mono hExtra.2 hbase⟩
  · intro slot j
    fin_cases j <;> simp only [PlayerSpecificAlgebraicNestedFirstTable.zero,FixedArrayTable.read_ofFn]
    · exact ⟨hfit.first.1,mono hfit.first.2 hbase⟩
    · exact ⟨nil_reduced _ hm0,nil_height _⟩
    · exact ⟨hExtra.1,mono hExtra.2 hbase⟩

theorem bounds (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) (T : ℕ)
    (hfit : Fits root a T) (hExtra : Reduced root.polynomial extra ∧ HasHeight extra T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) :
    Bounds root (PlayerSpecificAlgebraicNestedFirstTable.prepare model root a extra) (iterate 22 T) := by
  unfold PlayerSpecificAlgebraicNestedFirstTable.prepare
  split
  · have henv:=first_environment_bounds model root a extra T hfit hExtra hm hm0 hml hmT hT
    have hr:=PlayerSpecificAlgebraicThreeGeometry.reduced model root (firstEnvironment model root a extra) hm hm0 (fun j => (henv j).1)
    have hh:=PlayerSpecificAlgebraicThreeGeometry.heights model root (firstEnvironment model root a extra) hm hm0 hml
      (iterate 4 T) (mono hmT (PlayerSpecificAlgebraicExpressionBudget.initial_le 4 T))
      (hT.trans (PlayerSpecificAlgebraicExpressionBudget.initial_le 4 T)) henv
    rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hh
    have hd : Bounds root (PlayerSpecificAlgebraicThreeGeometry.prepare model root (firstEnvironment model root a extra)) (iterate 21 T) :=
      ⟨fun slot => ⟨hr.1 slot,hh.1 slot⟩,fun slot j => ⟨hr.2.1 slot j,hh.2.1 slot j⟩,
        fun slot j => ⟨hr.2.2 slot j,hh.2.2 slot j⟩⟩
    exact PlayerSpecificAlgebraicDescriptorShift.bounds root extra _ (iterate 21 T) hm hm0
      ⟨hExtra.1,mono hExtra.2 (PlayerSpecificAlgebraicExpressionBudget.initial_le 21 T)⟩ hd
  · exact zero root a extra T hfit hExtra hm hm0 hml hmT hT

end Blotto.PlayerSpecificAlgebraicNestedFirstSizes
