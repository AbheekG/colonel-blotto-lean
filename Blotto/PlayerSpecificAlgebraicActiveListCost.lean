import Blotto.PlayerSpecificAlgebraicActiveListExecution

/-! Every active-list source caller is bounded using the actual row
heights and finite indices. Complete retained-list copies are charged. -/
namespace Blotto.PlayerSpecificAlgebraicActiveListCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem width_large (S : ℕ) : 32≤PlayerSpecificAlgebraicComparisonExecution.width S ∧
    1+2*S≤PlayerSpecificAlgebraicComparisonExecution.width S ∧
    S+1≤PlayerSpecificAlgebraicComparisonExecution.width S := by
  have h:=PlayerSpecificAlgebraicInitialPrimitiveCost.large (2*S+1)
  change _≤PlayerSpecificAlgebraicInitialPrimitiveCost.width (2*S+1) ∧
    _≤PlayerSpecificAlgebraicInitialPrimitiveCost.width (2*S+1) ∧ _≤PlayerSpecificAlgebraicInitialPrimitiveCost.width (2*S+1)
  omega

theorem frame_cost {N : ℕ} (model : RationalCostModel) (length resource : Data) (j : Fin N)
    (ids result : List (Fin N)) (S : ℕ) (hN : N≤S) (hi : ids.length≤S) (hr : result.length ≤ ids.length)
    (hlH : HasHeight length S) (hrH : HasHeight resource S) (hll : length.length≤3) (hrl : resource.length≤3) :
    price model (PlayerSpecificAlgebraicActiveListExecution.frame length resource j ids result)≤
      150*(S+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hw : ∀ w∈[N,j.val,ids.length,result.length]++ids.map Fin.val++result.map Fin.val,binaryWordWidth w≤W := by
    intro w hw
    have hsmall : w≤S := by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with ((rfl|rfl|rfl|rfl)|hw)|hw
      · exact hN
      · exact (Nat.le_of_lt j.isLt).trans hN
      · exact hi
      · exact hr.trans hi
      · obtain ⟨k,_,rfl⟩:=List.mem_map.mp hw
        exact (Nat.le_of_lt k.isLt).trans hN
      · obtain ⟨k,_,rfl⟩:=List.mem_map.mp hw
        exact (Nat.le_of_lt k.isLt).trans hN
    exact (control_width w).trans ((Nat.add_le_add_right hsmall 1).trans (width_large S).2.2)
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model [length,resource]
    ([N,j.val,ids.length,result.length]++ids.map Fin.val++result.map Fin.val) S W
    (by intro row hrow; simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow; rcases hrow with rfl|rfl <;> assumption)
    (by intro row hrow; simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow; rcases hrow with rfl|rfl <;> omega)
    hw (width_large S).2.1 (width_large S).1
  apply hc.trans
  apply Nat.mul_le_mul_right (model.rat W)
  simp only [List.length_append,List.length_map,List.length_cons,List.length_nil]
  omega

theorem step_profile (A R S t : ℕ) :
    A*(S+1)*R+(t+1)*(A+150)*(S+1)*R+150*(S+1)*R=(t+2)*(A+150)*(S+1)*R := by ring

theorem cost {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths resources : FixedArrayTable N Data)
    (S : ℕ) (hN : N≤S) (hS : 1≤S)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial S) (he : HasHeight [root.interval.lo,root.interval.hi] S)
    (hv : root.interval.lo<root.interval.hi)
    (hl : ∀ j,HasHeight (lengths.read j) S) (hr : ∀ j,HasHeight (resources.read j) S)
    (hll : ∀ j,(lengths.read j).length≤3) (hrl : ∀ j,(resources.read j).length≤3) :
    ∀ ids : List (Fin N),ids.length≤S →
      (PlayerSpecificAlgebraicActiveListExecution.run model root lengths resources ids).2≤
        (ids.length+1)*(2*PlayerSpecificAlgebraicComparisonExecution.coefficient+153)*(S+1)*
          model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  let A:=2*PlayerSpecificAlgebraicComparisonExecution.coefficient+3
  intro ids
  induction ids with
  | nil =>
    intro _
    have hc:=PlayerSpecificAlgebraicCallerFrame.cost model [] [N,0] 0 W
      (by simp) (by simp)
      (by intro word hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with hw|hw
          · subst word
            exact (control_width N).trans ((Nat.add_le_add_right hN 1).trans (width_large S).2.2)
          · subst word
            exact (control_width 0).trans (by have h:32≤W:=(width_large S).1; omega))
      (by have h:32≤W:=(width_large S).1; omega) (width_large S).1
    change price model (PlayerSpecificAlgebraicCallerFrame.run [] [N,0])≤_
    apply hc.trans
    simp only [List.length_nil,List.length_cons,Nat.mul_zero,Nat.zero_add,Nat.one_mul]
    apply Nat.mul_le_mul_right (model.rat W)
    have hbase : 6≤(A+150)*(S+1) := by
      have hA : 6≤A+150 := by dsimp [A]; omega
      have hm:=Nat.mul_le_mul_left (A+150) (show 1≤S+1 by omega)
      omega
    exact hbase
  | cons j ids ih =>
    intro hids
    have ht:=ih (by simp only [List.length_cons] at hids; omega)
    have ha:=PlayerSpecificAlgebraicActiveCost.cost model root (lengths.read j) (resources.read j) S hm hm0 hml hmH he hv
      (hl j) (hr j) (hll j) (hrl j) hS
    let result:=(PlayerSpecificAlgebraicActiveListExecution.run model root lengths resources (j::ids)).1
    have hresult : result.length≤(j::ids).length := PlayerSpecificAlgebraicActiveListExecution.length model root lengths resources (j::ids)
    have hf:=frame_cost model (lengths.read j) (resources.read j) j (j::ids) result S hN hids hresult
      (hl j) (hr j) (hll j) (hrl j)
    have hsum:=Nat.add_le_add (Nat.add_le_add ha ht) hf
    change _≤A*(S+1)*model.rat W+(ids.length+1)*(A+150)*(S+1)*model.rat W+150*(S+1)*model.rat W at hsum
    rw [step_profile] at hsum
    exact hsum

end Blotto.PlayerSpecificAlgebraicActiveListCost
