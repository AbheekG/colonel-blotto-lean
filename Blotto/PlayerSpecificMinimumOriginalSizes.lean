import Blotto.PlayerSpecificMinimumSearchCost

/-! Original-input bounds for the actual minimum search. The common
height covers every stored initial coefficient, every dyadic test point
and all search counters. Initial-vector construction is priced separately. -/
namespace Blotto.PlayerSpecificMinimumOriginalSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificSturmVariations PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicInitialVector
open PlayerSpecificMinimumContract
set_option autoImplicit false
set_option maxHeartbeats 2500000

def inputSize {N : ℕ} (i : RationalPlayerSpecificInput N) : ℕ := PlayerSpecificInitialPositivePrecision.inputSize i
def height {N : ℕ} (i : RationalPlayerSpecificInput N) : ℕ :=
  PlayerSpecificAlgebraicInitialInputSizes.height N (inputSize i)+fuel i+N+4
def coefficient : ℕ := PlayerSpecificInitialPositivePrecision.initialCoefficient+
  PlayerSpecificInitialPositivePrecision.coefficient+6

theorem profile (A B N L T F H : ℕ) (hT : T≤A*(N+1)*(L+1))
    (hF : F=B*(N+1)*(L+1)) (hH : H=T+F+N+4) : H+1≤(A+B+6)*(N+1)*(L+1) := by
  have hN : N+1≤(N+1)*(L+1) := by nlinarith only [Nat.zero_le (N*L)]
  have hpos : 1≤(N+1)*(L+1) := by omega
  nlinarith only [hT,hF,hH,hN,hpos]

theorem height_polynomial {N : ℕ} (i : RationalPlayerSpecificInput N) :
    height i+1≤coefficient*(N+1)*(inputSize i+1) := by
  exact profile PlayerSpecificInitialPositivePrecision.initialCoefficient
    PlayerSpecificInitialPositivePrecision.coefficient N (inputSize i) _ _ _
    (PlayerSpecificAlgebraicInitialInputSizes.polynomial_height N (inputSize i)) (fuel_value i) rfl

theorem initial_le {N : ℕ} (i : RationalPlayerSpecificInput N) :
    PlayerSpecificAlgebraicInitialInputSizes.height N (inputSize i)≤height i := by unfold height; omega

theorem parameter_le {N : ℕ} (i : RationalPlayerSpecificInput N) :
    PlayerSpecificFiniteParameterSizes.height N (inputSize i)≤height i := by
  have hb:=PlayerSpecificInitialPositivePrecision.base_le_height (PlayerSpecificAlgebraicInitialInputSizes.base N (inputSize i))
  have hf : PlayerSpecificFiniteParameterSizes.height N (inputSize i)≤PlayerSpecificAlgebraicInitialInputSizes.base N (inputSize i) := by
    unfold PlayerSpecificAlgebraicInitialInputSizes.base
    omega
  exact (hf.trans hb).trans (initial_le i)

theorem search_source_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (run i r).work≤(fuel i+1)*PlayerSpecificMinimumSearchCost.coefficient*(N+1)*(height i+1)*
      RationalCostModel.schoolbook.rat (PlayerSpecificMinimumTestCost.width (height i)) := by
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hp:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sizes i r hr
  have hi:=PlayerSpecificAlgebraicInitialInputSizes.actual_sizes i r hr
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hs.2.1.ne_zero (by rw [hz]; rfl)
  obtain ⟨x,hx,_⟩:=PlayerSpecificInitialPositivePrecision.actual_lower_bounds i r hr
  have hv : r.root.interval.lo<r.root.interval.hi := by exact_mod_cast hx.2.1.1.trans_le hx.2.1.2
  have hred:=(reduced_rows RationalCostModel.schoolbook i r hs.1 hm0).2
  have hrows : ∀ a∈lengths (prepare RationalCostModel.schoolbook i r),HasHeight a (height i) ∧ a.length≤3 := by
    intro a ha
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp ha
    exact ⟨mono (hi.2 j).1 (initial_le i),by have hl:=(hred j).1.2; have hm:=hs.2.2.1; omega⟩
  have hmH:=mono hp.1 (parameter_le i)
  have he:=cons_height (hp.2.1.mono (parameter_le i)) (cons_height (hp.2.2.1.mono (parameter_le i)) (nil_height _))
  have hc:=PlayerSpecificMinimumSearchCost.source_cost RationalCostModel.schoolbook r.root.polynomial r.root.interval
    (lengths (prepare RationalCostModel.schoolbook i r)) (fuel i) 0 (height i) 1 hs.1 hm0 hs.2.2.1 hmH he hv
    (by rw [lengths_length]; unfold height; omega) hrows (by norm_num [PlayerSpecificPositiveFieldLowerBound.dyadic])
    (by unfold height; omega)
  simpa only [lengths_length,PlayerSpecificMinimumContract.run] using hc

theorem output_size {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    RationalHeight (run i r).quantum (height i) ∧ rationalWordWidth (run i r).quantum≤2*height i+1 := by
  obtain ⟨_,_,hq,_,he,_,_⟩:=actual_contract i r hr
  have h : RationalHeight (run i r).quantum (height i) := hq.symm ▸
    (PlayerSpecificMinimumSearchCost.dyadic_height _).mono (by unfold height; omega)
  exact ⟨h,by have hw:=rationalWordWidth_of_height h; omega⟩

end Blotto.PlayerSpecificMinimumOriginalSizes
