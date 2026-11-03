import Blotto.PlayerSpecificAlgebraicGroupingFrameCost

/-! Complete source work for the actually executed cached greedy loop.
Its additive height potential is derived from original endpoint rows. -/
namespace Blotto.PlayerSpecificAlgebraicGroupingSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicGrouping
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := PlayerSpecificAlgebraicComparisonExecution.coefficient+200002000
def work (model : RationalCostModel) (S : ℕ) : ℕ := coefficient*(S+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S)

theorem step_profile (A S R t : ℕ) :
    200000000*R+A*(S+1)*R+(t+1)*((A+200002000)*(S+1)*R)+500*(S+1)*R≤
      (t+2)*((A+200002000)*(S+1)*R) := by
  nlinarith only [Nat.zero_le (S*R),Nat.zero_le R]

theorem frame_profile (A S R : ℕ) : 500*(S+1)*R≤(A+200002000)*(S+1)*R := by
  nlinarith only [Nat.zero_le (A*(S+1)*R),Nat.zero_le (S*R),Nat.zero_le R]

theorem aux {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths : FixedArrayTable N Data) (B : ℚ)
    (T S : ℕ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmS : HasHeight root.polynomial S) (he : HasHeight [root.interval.lo,root.interval.hi,B] S)
    (hv : root.interval.lo<root.interval.hi) (hN : N+1≤S)
    (hl : ∀ k,Reduced root.polynomial (lengths.read k) ∧ HasHeight (lengths.read k) T)
    (rest : List (Fin N)) : ∀ (current : List (Fin N)) (s : Data) (C : ℕ),
    Reduced root.polynomial s → HasHeight s C → C+(rest.length+1)*(T+1)≤S → current.length+rest.length≤N →
    (PlayerSpecificAlgebraicGroupingExecution.packAux model root lengths B current s rest).2≤(rest.length+1)*work model S := by
  intro current s C hs hsC hpotential hi
  induction rest generalizing current s C with
  | nil =>
    have hsS:=mono hsC (show C≤S by omega)
    have hsl : s.length≤3 := by have h:=hs.2; omega
    have hf:=PlayerSpecificAlgebraicGroupingFrameCost.cost model root B current s [] [] [⟨current.reverse,s⟩] S
      hmS hml he hsS hsl (by intro q hq; exact False.elim (List.not_mem_nil hq)) (by simp)
      (by intro g hg; have hg' : g=⟨current.reverse,s⟩ := List.mem_singleton.mp hg; subst g; exact ⟨hsS,hsl⟩)
      hi (by simp) (by simpa only [List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,List.length_reverse,List.length_nil,Nat.add_zero] using hi) hN
    have hf':=hf.trans (Nat.mul_le_mul_right (model.rat (PlayerSpecificAlgebraicComparisonExecution.width S))
      (Nat.mul_le_mul_left 500 (show N+1≤S+1 by omega)))
    rw [List.length_nil,Nat.zero_add,Nat.one_mul]
    exact hf'.trans (frame_profile PlayerSpecificAlgebraicComparisonExecution.coefficient S
      (model.rat (PlayerSpecificAlgebraicComparisonExecution.width S)))
  | cons k rest ih =>
    let combined:=PlayerSpecificFieldCombination.run false root.polynomial s (lengths.read k)
    have hsumred : Reduced root.polynomial combined.1 := PlayerSpecificFieldCombination.reduced false _ _ _ hm hm0
    have hsumH : HasHeight combined.1 (C+T+1) := by
      change HasHeight (PlayerSpecificFieldCombination.run false root.polynomial s (lengths.read k)).1 _
      rw [PlayerSpecificFieldCombination.value]
      change HasHeight (PlayerSpecificAlgebraicField.plus root.polynomial s (lengths.read k)) _
      exact PlayerSpecificShortReduction.plus_height _ _ _ hm hm0 hs (hl k).1 C T hsC (hl k).2
    simp only [List.length_cons] at hpotential hi
    have hnext : C+T+1+(rest.length+1)*(T+1)≤S := by nlinarith only [hpotential]
    have hreset : T+(rest.length+1)*(T+1)≤S := by nlinarith only [hpotential,Nat.zero_le C]
    have hCS : C≤S := by omega
    have hTS : T≤S := by nlinarith only [hpotential,Nat.zero_le (rest.length*(T+1))]
    have hsumS:=mono hsumH (show C+T+1≤S by nlinarith only [hpotential,Nat.zero_le (rest.length*(T+1))])
    have hsl : s.length≤3 := by have h:=hs.2; omega
    have hll : (lengths.read k).length≤3 := by have h:=(hl k).1.2; omega
    have hsuml : combined.1.length≤3 := by have h:=hsumred.2; omega
    have hcomb:=(PlayerSpecificFieldCombinationCost.run_cost model false root.polynomial s (lengths.read k) hm hm0 hml S
      hmS (mono hsC hCS) (mono (hl k).2 hTS) (by omega) hsl hll).trans
      (Nat.mul_le_mul_left _ (model.monotone (PlayerSpecificAlgebraicExpressionPrimitiveCost.combination_width S)))
    have hcmp:=PlayerSpecificAlgebraicComparisonExecution.cost model root combined.1 [B] S hm hm0 hml hmS
      (by intro q hq; simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
          rcases hq with rfl|rfl <;> exact he _ (by simp)) hv hsumS
      (by intro q hq; have hq' : q=B := List.mem_singleton.mp hq; subst q; exact he B (by simp)) hsuml (by simp) (by omega)
    let result:=(PlayerSpecificAlgebraicGroupingExecution.packAux model root lengths B current s (k::rest)).1
    have hr:=PlayerSpecificAlgebraicGroupingHeights.aux model root lengths B T S hm hm0 hl (k::rest) current s C hs hsC
      (by simpa only [List.length_cons] using hpotential)
    have hshape:=PlayerSpecificAlgebraicGroupingShape.aux model root lengths B current s (k::rest)
    have hf:=PlayerSpecificAlgebraicGroupingFrameCost.cost model root B current s combined.1 (k::rest) result S
      hmS hml he (mono hsC hCS) hsl hsumS hsuml
      (by intro g hg; exact ⟨(hr g hg).2,by have h:=(hr g hg).1.2; omega⟩)
      (by simpa only [List.length_cons] using hi)
      (by dsimp only [result]; have h:=hshape.2; simp only [List.length_cons] at h; omega)
      (by dsimp only [result]; rw [hshape.1,List.length_append,List.length_reverse,List.length_cons]; exact hi) hN
    have hf':=hf.trans (Nat.mul_le_mul_right (model.rat (PlayerSpecificAlgebraicComparisonExecution.width S))
      (Nat.mul_le_mul_left 500 (show N+1≤S+1 by omega)))
    have hy:=ih (k::current) combined.1 (C+T+1) hsumred hsumH hnext (by simp only [List.length_cons]; omega)
    have hn:=ih [k] (lengths.read k) T (hl k).1 (hl k).2 hreset (by simp only [List.length_cons,List.length_nil]; omega)
    have hstep : 200000000*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S)+
        PlayerSpecificAlgebraicComparisonExecution.coefficient*(S+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S)+
        (rest.length+1)*work model S+500*(S+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S)≤
        (rest.length+2)*work model S := by
      exact step_profile PlayerSpecificAlgebraicComparisonExecution.coefficient S
        (model.rat (PlayerSpecificAlgebraicComparisonExecution.width S)) rest.length
    change price model combined.2≤_ at hcomb
    dsimp only [result,PlayerSpecificAlgebraicGroupingExecution.packAux] at hf' ⊢
    split <;> simp_all only
    · exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hcomb hcmp) hy) hf').trans
        hstep
    · exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hcomb hcmp) hn) hf').trans
        hstep

end Blotto.PlayerSpecificAlgebraicGroupingSourceCost
