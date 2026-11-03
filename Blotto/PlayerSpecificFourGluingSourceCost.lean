import Blotto.PlayerSpecificFourGluingExecution

/-! Complete original-input-height gluing source work, including all
parameters, both measured parents, all 81 cached overlaps and returns.
No intermediate size, descriptor or arithmetic oracle enters runtime. -/
namespace Blotto.PlayerSpecificFourGluingSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := PlayerSpecificFourParameterSourceCost.coefficient*(H+25)^3+
  PlayerSpecificFourParentInputSourceCost.coefficient*(iterate 13 H+30)^3+
  PlayerSpecificUnorderedThreeSourceCost.coefficient*(iterate 13 H+1)^3+
  PlayerSpecificFourParentInputSourceCost.coefficient*(iterate 13 H+30)^3+
  PlayerSpecificUnorderedThreeSourceCost.coefficient*(iterate 13 H+1)^3+
  PlayerSpecificOverlapTableSourceCost.work (iterate 33 H) 9 9+8

theorem fits_mono (root : Candidate) (a : Input) (H U : ℕ) (ha : Fits root a H) (hHU : H≤U) : Fits root a U :=
  ⟨⟨ha.budget.1,mono ha.budget.2 hHU⟩,⟨ha.first.1,mono ha.first.2 hHU⟩,⟨ha.second.1,mono ha.second.2 hHU⟩,
    ⟨ha.third.1,mono ha.third.2 hHU⟩,⟨ha.length.1,mono ha.length.2 hHU⟩,⟨ha.probability.1,mono ha.probability.2 hHU⟩⟩

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificFourGluingExecution.run RationalCostModel.schoolbook root a).2≤work H := by
  let model:=RationalCostModel.schoolbook
  let p:=parameters model root a
  let firstInput:=PlayerSpecificAlgebraicFourGluingInputs.first root a p
  let secondInput:=PlayerSpecificAlgebraicFourGluingInputs.second a p
  let first:=PlayerSpecificAlgebraicUnorderedThree.prepare model root firstInput
  let second:=PlayerSpecificAlgebraicUnorderedThree.prepare model root secondInput
  have h13:=PlayerSpecificAlgebraicExpressionBudget.initial_le 13 H
  have h33:=PlayerSpecificAlgebraicExpressionBudget.initial_le 33 H
  have h1333:=PlayerSpecificAlgebraicExpressionBudget.fuel_mono H (by decide : 13≤33)
  have hp:=parameter_bounds model root a H ha hm hm0 hml hmH hH
  have hpc:=PlayerSpecificFourParameterSourceCost.cost root a H hm hm0 hml hmH he hv hH ha
  have hic : ∀ b : Bool,(PlayerSpecificFourParentInputExecution.run model root a p b).2≤
      PlayerSpecificFourParentInputSourceCost.coefficient*(iterate 13 H+30)^3 := fun b =>
    PlayerSpecificFourParentInputSourceCost.cost root a p b (iterate 13 H) hm hm0 hml (mono hmH h13) (mono he h13) hv
      ((show 1≤H by omega).trans h13) (fits_mono root a H (iterate 13 H) ha h13) hp
  have hfirst:=PlayerSpecificUnorderedThreeSourceCost.cost root firstInput (iterate 13 H) hm hm0 hml (mono hmH h13) (mono he h13) hv
    (hH.trans h13) (PlayerSpecificAlgebraicFourGluingSizes.first_fits model root a H ha hm hm0 hml hmH hH)
  have hsecond:=PlayerSpecificUnorderedThreeSourceCost.cost root secondInput (iterate 13 H) hm hm0 hml (mono hmH h13) (mono he h13) hv
    (hH.trans h13) (PlayerSpecificAlgebraicFourGluingSizes.second_fits model root a H ha hm hm0 hml hmH hH)
  have hparents:=PlayerSpecificAlgebraicFourGluingSizes.parents model root a H ha hm hm0 hml hmH hH
  have ho:=PlayerSpecificOverlapTableSourceCost.cost root first second (p.read 1) a.budget (iterate 33 H) hm hm0 hml
    (mono hmH h33) (mono he h33) hv (hH.trans h33) hparents.1 hparents.2
    ⟨(hp 1).1,mono (hp 1).2 h1333⟩ ⟨ha.budget.1,mono ha.budget.2 h33⟩
  rw [PlayerSpecificFourGluingExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hpc (hic false)) hfirst)
    (hic true)) hsecond) ho) 8

theorem same_return_and_cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificFourGluingExecution.run RationalCostModel.schoolbook root a).1=
      PlayerSpecificAlgebraicFourGluingTable.prepare RationalCostModel.schoolbook root a ∧
    (PlayerSpecificFourGluingExecution.run RationalCostModel.schoolbook root a).2≤work H :=
  ⟨PlayerSpecificFourGluingExecution.value _ root a,cost root a H hm hm0 hml hmH he hv hH ha⟩

end Blotto.PlayerSpecificFourGluingSourceCost
