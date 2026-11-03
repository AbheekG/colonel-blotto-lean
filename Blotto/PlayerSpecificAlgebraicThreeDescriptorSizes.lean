import Blotto.PlayerSpecificAlgebraicDescriptorBounds

/-! One fixed height envelope covers ordered, swapped and exceptional
three-variable cached descriptors, from their actual algebraic inputs. -/
namespace Blotto.PlayerSpecificAlgebraicThreeDescriptorSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicThreeInput
open PlayerSpecificAlgebraicThreeEnvironmentSizes PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem exceptional (root : Candidate) (a : Input) (T : ℕ) (hfit : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) :
    Bounds root (PlayerSpecificAlgebraicOrderedThree.exceptional root a) (iterate 20 T) := by
  have hbase : T≤ iterate 20 T := PlayerSpecificAlgebraicExpressionBudget.initial_le 20 T
  have hstep : step T≤ iterate 20 T := PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (show 1≤20 by omega)
  constructor
  · intro slot
    simp only [PlayerSpecificAlgebraicOrderedThree.exceptional,FixedArrayTable.read_ofFn]
    refine ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,?_⟩
    apply mono (constant_height root.polynomial _ T hmT _ (by omega) hml) hstep
    split
    · exact one_height.mono (by omega)
    · exact zero_height.mono (by omega)
  · intro slot j
    fin_cases j <;> simp only [PlayerSpecificAlgebraicOrderedThree.exceptional,FixedArrayTable.read_ofFn]
    · exact ⟨nil_reduced _ hm0,nil_height _⟩
    · exact ⟨nil_reduced _ hm0,nil_height _⟩
    · exact ⟨hfit.budget.1,mono hfit.budget.2 hbase⟩
  · intro slot j
    fin_cases j <;> simp only [PlayerSpecificAlgebraicOrderedThree.exceptional,FixedArrayTable.read_ofFn]
    · exact ⟨hfit.first.1,mono hfit.first.2 hbase⟩
    · exact ⟨hfit.second.1,mono hfit.second.2 hbase⟩
    · exact ⟨nil_reduced _ hm0,nil_height _⟩

theorem ordered (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (hfit : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) :
    Bounds root (PlayerSpecificAlgebraicOrderedThree.prepare model root a) (iterate 20 T) := by
  unfold PlayerSpecificAlgebraicOrderedThree.prepare
  split
  · have hr:=PlayerSpecificAlgebraicThreeGeometry.reduced model root (environment root a) hm hm0 (environment_reduced root a hm hm0)
    have henv:=environment_height root a T hfit hm hm0 hml hmT (by omega)
    have hh:=PlayerSpecificAlgebraicThreeGeometry.heights model root (environment root a) hm hm0 hml
      (iterate 3 T) (mono hmT (PlayerSpecificAlgebraicExpressionBudget.initial_le 3 T))
      (hT.trans (PlayerSpecificAlgebraicExpressionBudget.initial_le 3 T))
      (fun j => ⟨environment_reduced root a hm hm0 j,henv j⟩)
    rw [iterate_add] at hh
    exact ⟨fun slot => ⟨hr.1 slot,hh.1 slot⟩,fun slot j => ⟨hr.2.1 slot j,hh.2.1 slot j⟩,
      fun slot j => ⟨hr.2.2 slot j,hh.2.2 slot j⟩⟩
  · exact exceptional root a T hfit hm hm0 hml hmT hT

theorem unordered (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (hfit : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) :
    Bounds root (PlayerSpecificAlgebraicUnorderedThree.prepare model root a) (iterate 20 T) := by
  unfold PlayerSpecificAlgebraicUnorderedThree.prepare
  split
  · exact ordered model root a T hfit hm hm0 hml hmT hT
  · have h:=ordered model root (PlayerSpecificAlgebraicUnorderedThree.swapped a) T (swapped root a T hfit) hm hm0 hml hmT hT
    constructor
    · exact h.weights
    · intro slot j
      fin_cases j <;> simp only [PlayerSpecificAlgebraicUnorderedThree.permuted,FixedArrayTable.read_ofFn]
      · exact h.first slot 1
      · exact h.first slot 0
      · exact h.first slot 2
    · intro slot j
      fin_cases j <;> simp only [PlayerSpecificAlgebraicUnorderedThree.permuted,FixedArrayTable.read_ofFn]
      · exact h.second slot 1
      · exact h.second slot 0
      · exact h.second slot 2

end Blotto.PlayerSpecificAlgebraicThreeDescriptorSizes
