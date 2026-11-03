import Blotto.PlayerSpecificAlgebraicGroupingSourceCost

/-! The complete cached grouping entry, including empty input and its
returned group/list frame, has polynomial source work. -/
namespace Blotto.PlayerSpecificAlgebraicGroupingEntryCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicGrouping
open PlayerSpecificAlgebraicGroupingSourceCost
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem join (t W : ℕ) : (t+1)*W+W=(t+2)*W := by ring

theorem cost {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths : FixedArrayTable N Data) (B : ℚ)
    (items : List (Fin N)) (T S : ℕ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmS : HasHeight root.polynomial S)
    (he : HasHeight [root.interval.lo,root.interval.hi,B] S) (hv : root.interval.lo<root.interval.hi)
    (hN : N+1≤S) (hl : ∀ k,Reduced root.polynomial (lengths.read k) ∧ HasHeight (lengths.read k) T)
    (hi : items.length≤N) (hpotential : (items.length+1)*(T+1)≤S) :
    (PlayerSpecificAlgebraicGroupingExecution.run model root lengths B items).2≤(items.length+1)*work model S := by
  cases items with
  | nil =>
    have hf:=PlayerSpecificAlgebraicGroupingFrameCost.cost model root B ([] : List (Fin N)) [] [] [] [] S
      hmS hml he (nil_height _) (by simp) (nil_height _) (by simp)
      (by intro g hg; exact False.elim (List.not_mem_nil hg)) (by simp) (by simp) (by simp) hN
    have hf':=hf.trans (Nat.mul_le_mul_right (model.rat (PlayerSpecificAlgebraicComparisonExecution.width S))
      (Nat.mul_le_mul_left 500 (show N+1≤S+1 by omega)))
    rw [List.length_nil,Nat.zero_add,Nat.one_mul]
    exact hf'.trans (frame_profile PlayerSpecificAlgebraicComparisonExecution.coefficient S _)
  | cons k rest =>
    have hpot : T+(rest.length+1)*(T+1)≤S := by simp only [List.length_cons] at hpotential; nlinarith only [hpotential]
    have ha:=aux model root lengths B T S hm hm0 hml hmS he hv hN hl rest [k] (lengths.read k) T (hl k).1 (hl k).2
      hpot (by simpa only [List.length_cons,List.length_nil,Nat.zero_add,Nat.add_comm] using hi)
    have hTS : T≤S := by nlinarith only [hpot,Nat.zero_le (rest.length*(T+1))]
    let result:=(PlayerSpecificAlgebraicGroupingExecution.packAux model root lengths B [k] (lengths.read k) rest).1
    have hr:=PlayerSpecificAlgebraicGroupingHeights.aux model root lengths B T S hm hm0 hl rest [k] (lengths.read k) T (hl k).1 (hl k).2 hpot
    have hshape:=PlayerSpecificAlgebraicGroupingShape.aux model root lengths B [k] (lengths.read k) rest
    have hf:=PlayerSpecificAlgebraicGroupingFrameCost.cost model root B [k] (lengths.read k) [] rest result S hmS hml he
      (mono (hl k).2 hTS) (by have h:=(hl k).1.2; omega) (nil_height _) (by simp)
      (by intro g hg; exact ⟨(hr g hg).2,by have h:=(hr g hg).1.2; omega⟩)
      (by simpa only [List.length_cons,List.length_nil,Nat.zero_add,Nat.add_comm] using hi)
      (by dsimp only [result]; have h:=hshape.2; simp only [List.length_cons] at hi; omega)
      (by dsimp only [result]; rw [hshape.1,List.length_append,List.length_reverse]; simpa only [List.length_cons,List.length_nil,Nat.zero_add,Nat.add_comm] using hi) hN
    have hf':=hf.trans (Nat.mul_le_mul_right (model.rat (PlayerSpecificAlgebraicComparisonExecution.width S))
      (Nat.mul_le_mul_left 500 (show N+1≤S+1 by omega)))
    have hfW:=hf'.trans (frame_profile PlayerSpecificAlgebraicComparisonExecution.coefficient S _)
    change price model (PlayerSpecificAlgebraicGroupingExecution.frame root B [k] (lengths.read k) [] rest result)≤work model S at hfW
    have hsum:=Nat.add_le_add ha hfW
    rw [join] at hsum
    exact hsum

def polynomialCoefficient : ℕ := PlayerSpecificAlgebraicGroupingSourceCost.coefficient*(PlayerSpecificAlgebraicComparisonCost.widthCoefficient^2+
  PlayerSpecificAlgebraicComparisonCost.widthCoefficient)

theorem polynomial_cost {N : ℕ} (root : Candidate) (lengths : FixedArrayTable N Data) (B : ℚ)
    (items : List (Fin N)) (T S : ℕ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmS : HasHeight root.polynomial S)
    (he : HasHeight [root.interval.lo,root.interval.hi,B] S) (hv : root.interval.lo<root.interval.hi)
    (hN : N+1≤S) (hl : ∀ k,Reduced root.polynomial (lengths.read k) ∧ HasHeight (lengths.read k) T)
    (hi : items.length≤N) (hpotential : (items.length+1)*(T+1)≤S) :
    (PlayerSpecificAlgebraicGroupingExecution.run RationalCostModel.schoolbook root lengths B items).2≤
      (items.length+1)*(polynomialCoefficient*(S+1)^3) := by
  have hc:=cost RationalCostModel.schoolbook root lengths B items T S hm hm0 hml hmS he hv hN hl hi hpotential
  have hw : work RationalCostModel.schoolbook S≤polynomialCoefficient*(S+1)^3 := by
    unfold work
    rw [PlayerSpecificAlgebraicComparisonCost.width_linear]
    exact PlayerSpecificAlgebraicPairCost.cubic_profile PlayerSpecificAlgebraicGroupingSourceCost.coefficient
      PlayerSpecificAlgebraicComparisonCost.widthCoefficient (S+1) (by omega)
  exact hc.trans (Nat.mul_le_mul_left (items.length+1) hw)

end Blotto.PlayerSpecificAlgebraicGroupingEntryCost
