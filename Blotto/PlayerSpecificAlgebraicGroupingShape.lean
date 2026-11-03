import Blotto.PlayerSpecificAlgebraicGroupingExecution

/-! Structural bounds for the actual cached grouping, independent of
real-root semantics or budget promises. -/
namespace Blotto.PlayerSpecificAlgebraicGroupingShape
open PlayerSpecificDensePolynomial PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicGrouping
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem aux {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths : FixedArrayTable N Data) (B : ℚ)
    (current : List (Fin N)) (s : Data) (rest : List (Fin N)) :
    ((PlayerSpecificAlgebraicGroupingExecution.packAux model root lengths B current s rest).1.map Group.members).flatten=current.reverse++rest ∧
    (PlayerSpecificAlgebraicGroupingExecution.packAux model root lengths B current s rest).1.length≤rest.length+1 := by
  rw [PlayerSpecificAlgebraicGroupingExecution.aux_value]
  induction rest generalizing current s with
  | nil => simp only [PlayerSpecificAlgebraicGrouping.packAux,List.map_cons,List.map_nil,List.flatten_cons,
      List.flatten_nil,List.append_nil,List.length_cons,List.length_nil,Nat.le_refl,and_self]
  | cons k rest ih =>
    unfold PlayerSpecificAlgebraicGrouping.packAux
    dsimp only
    split
    · obtain ⟨ha,hb⟩:=ih (k::current) _
      refine ⟨?_,?_⟩
      · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using ha
      · simp only [List.length_cons]; omega
    · obtain ⟨ha,hb⟩:=ih [k] (lengths.read k)
      constructor
      · have ht : ((PlayerSpecificAlgebraicGrouping.packAux model root lengths.read B [k] (lengths.read k) rest).map Group.members).flatten=k::rest := by
          simpa only [List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using ha
        simp only [List.map_cons,List.flatten_cons,ht]
      · simp only [List.length_cons]; omega

theorem run {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths : FixedArrayTable N Data) (B : ℚ)
    (items : List (Fin N)) :
    ((PlayerSpecificAlgebraicGroupingExecution.run model root lengths B items).1.map Group.members).flatten=items ∧
    (PlayerSpecificAlgebraicGroupingExecution.run model root lengths B items).1.length ≤ items.length := by
  cases items with
  | nil => exact ⟨rfl,by rfl⟩
  | cons k rest =>
    have h:=aux model root lengths B [k] (lengths.read k) rest
    simpa only [PlayerSpecificAlgebraicGroupingExecution.run,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.singleton_append,List.length_cons] using h

end Blotto.PlayerSpecificAlgebraicGroupingShape
