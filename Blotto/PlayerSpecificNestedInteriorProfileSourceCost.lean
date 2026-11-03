import Blotto.PlayerSpecificNestedInteriorProfileExecution

/-! Complete source bounds for all three interior cases and their
actual cached dispatcher. Every reached size derives from raw inputs. -/
namespace Blotto.PlayerSpecificNestedInteriorProfileSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def selectedWork (H K : ℕ) : ℕ := 2*(PlayerSpecificCompareSourceCost.coefficient*(H+1)^3)+
  PlayerSpecificNestedFirstProfileSourceCost.work H K+PlayerSpecificNestedSecondProfileSourceCost.work H K+
  PlayerSpecificNestedThirdProfileSourceCost.work H K+4
def work (H K : ℕ) : ℕ := PlayerSpecificNestedCaseParameterSourceCost.coefficient*(H+1)^3+selectedWork (iterate 9 H) K+2
theorem first_profile (C A B D : ℕ) : C+A+2≤2*C+A+B+D+4 := by omega
theorem second_profile (C A B D : ℕ) : C+C+B+4≤2*C+A+B+D+4 := by omega
theorem third_profile (C A B D : ℕ) : C+C+D+4≤2*C+A+B+D+4 := by omega

theorem selected_cost (root : Candidate) (a : Input) (p : Prepared) (H K : ℕ) (outer : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hp : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p H) :
    (PlayerSpecificNestedInteriorProfileExecution.selected RationalCostModel.schoolbook root a p K outer).2≤selectedWork H K := by
  have hc1:=PlayerSpecificCompareSourceCost.cost root a.short p.v H hm hm0 hml hmH he hv (by omega) ha.short hp.v
  have hc2:=PlayerSpecificCompareSourceCost.cost root p.u a.short H hm hm0 hml hmH he hv (by omega) hp.u ha.short
  have hf:=PlayerSpecificNestedFirstProfileSourceCost.cost root a H K outer hm hm0 hml hmH he hv hH ha
  have hs:=PlayerSpecificNestedSecondProfileSourceCost.cost root a p H K outer hm hm0 hml hmH he hv hH ha hp
  have ht:=PlayerSpecificNestedThirdProfileSourceCost.cost root a p H K outer hm hm0 hml hmH he hv hH ha hp
  simp only [PlayerSpecificNestedInteriorProfileExecution.selected,PlayerSpecificNestedInteriorProfileExecution.packing,
    PlayerSpecificNestedInteriorProfileExecution.two_tests_packing]
  split
  · exact (Nat.add_le_add_right (Nat.add_le_add hc1 hf) 2).trans (first_profile _ _ _ _)
  · split
    · exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc1 hc2) hs) 4).trans (second_profile _ _ _ _)
    · exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc1 hc2) ht) 4).trans (third_profile _ _ _ _)

theorem cost (root : Candidate) (a : Input) (H K : ℕ) (outer : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedInteriorProfileExecution.run RationalCostModel.schoolbook root a K outer).2≤work H K := by
  let model:=RationalCostModel.schoolbook
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 9 H
  have hp:=PlayerSpecificAlgebraicNestedCaseParameters.bounds model root a H ha hm hm0 hml hmH hH
  have hc:=PlayerSpecificNestedCaseParameterSourceCost.cost root a H hm hm0 hml hmH he hv hH ha
  have hs:=selected_cost root a (PlayerSpecificAlgebraicNestedCaseParameters.prepare model root a) (iterate 9 H) K outer
    hm hm0 hml (mono hmH hbase) (mono he hbase) hv (hH.trans hbase)
    (PlayerSpecificAlgebraicNestedInputTools.fits_mono root a H (iterate 9 H) ha hbase) hp
  rw [PlayerSpecificNestedInteriorProfileExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add hc hs) 2

theorem same_return_and_cost (root : Candidate) (a : Input) (H K : ℕ) (outer : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedInteriorProfileExecution.run RationalCostModel.schoolbook root a K outer).1=
      PlayerSpecificAlgebraicNestedInteriorProfile.prepare RationalCostModel.schoolbook root a K outer ∧
    (PlayerSpecificNestedInteriorProfileExecution.run RationalCostModel.schoolbook root a K outer).2≤work H K :=
  ⟨PlayerSpecificNestedInteriorProfileExecution.value _ root a K outer,cost root a H K outer hm hm0 hml hmH he hv hH ha⟩

end Blotto.PlayerSpecificNestedInteriorProfileSourceCost
