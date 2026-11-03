import Blotto.PlayerSpecificOverlapEnvironmentExecution

/-! Complete overlap environment/index/copy source work derives sizes
from original parent bounds and the common interval/fallback budget. -/
namespace Blotto.PlayerSpecificOverlapEnvironmentSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicReduction
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := 6621*PlayerSpecificResourceCostProfile.rationalCoefficient
def work (H k h : ℕ) : ℕ := coefficient*(H+k+h+21)^3
theorem profile (R : ℕ) : 6600*R+21*R=6621*R := by ring

theorem cost {k h : ℕ} (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) (i : Fin k) (j : Fin h) (H : ℕ)
    (hml : root.polynomial.length≤4) (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hf : Bounds root first H) (hs : Bounds root second H)
    (hi : Reduced root.polynomial interval ∧ HasHeight interval H) (hb : Reduced root.polynomial budget ∧ HasHeight budget H) :
    (PlayerSpecificOverlapEnvironmentExecution.run RationalCostModel.schoolbook root first second interval budget i j).2≤work H k h := by
  let model:=RationalCostModel.schoolbook
  let env:=(PlayerSpecificOverlapEnvironmentExecution.run model root first second interval budget i j).1
  let S:=H+k+h+20
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hHS : H≤S := by dsimp [S]; omega
  have hk : k≤S := by dsimp [S]; omega
  have hh : h≤S := by dsimp [S]; omega
  have h20 : 20≤S := by dsimp [S]; omega
  have henv : ∀ r,Reduced root.polynomial (env.read r) ∧ HasHeight (env.read r) H := by
    change ∀ r,Reduced root.polynomial ((PlayerSpecificOverlapEnvironmentExecution.run model root first second interval budget i j).1.read r) ∧
      HasHeight ((PlayerSpecificOverlapEnvironmentExecution.run model root first second interval budget i j).1.read r) H
    rw [PlayerSpecificOverlapEnvironmentExecution.value]
    exact PlayerSpecificAlgebraicOverlapEnvironment.bounds root first second interval budget H hf hs hi hb i j
  have hv:=PlayerSpecificExpressionVectorFrameCost.cost model root env env S (mono hmH hHS) hml (mono he hHS)
    (fun r => ⟨mono (henv r).2 hHS,by have h:=(henv r).1.2; omega⟩)
    (fun r => ⟨mono (henv r).2 hHS,by have h:=(henv r).1.2; omega⟩) (by omega) (by omega) (by omega)
  have hword : ∀ n∈[k,h,i.val,j.val,3,16,1],binaryWordWidth n≤W := by
    intro n hn
    have hil:=i.isLt
    have hjl:=j.isLt
    have hsmall : n≤S := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with hn|hn|hn|hn|hn|hn|hn <;> omega
    exact (control_width n).trans ((Nat.add_le_add_right hsmall 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model [] [k,h,i.val,j.val,3,16,1] 0 W
    (by simp) (by simp) hword (by have hw:=(PlayerSpecificAlgebraicActiveListCost.width_large S).1; change 32≤W at hw; omega)
    (PlayerSpecificAlgebraicActiveListCost.width_large S).1
  change price model (PlayerSpecificOverlapEnvironmentExecution.indices k h i j)≤21*model.rat W at hc
  change price model (PlayerSpecificExpressionVectorExecution.frame root env env)≤6600*model.rat W at hv
  have hsum:=(Nat.add_le_add hv hc).trans_eq (profile _)
  rw [PlayerSpecificOverlapEnvironmentExecution.price_equation]
  exact hsum.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 6621 S)

end Blotto.PlayerSpecificOverlapEnvironmentSourceCost
