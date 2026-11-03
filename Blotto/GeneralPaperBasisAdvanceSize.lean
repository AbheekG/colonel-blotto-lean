import Blotto.GeneralPaperSourceBasisStageSize

/-! Actual recovered blockers supply all operands of the native cached
basis update. The native ray endpoint supplies its own original-row
contract; no coefficient/operand-size oracle is added to the step.
-/
namespace Blotto.GeneralPaperBasisAdvanceSize
open RationalOrderCell GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperBasisOriginalDirection GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

def Contract {T m j : ℕ} (k : ℕ) (labels : Fin T → Fin m → Fin (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (answer : GeneralPaperRayEndpoint.Answer T m (prepare m k).K) : Prop :=
  let newRow := GeneralPaperBasisDenseRow.build (GeneralPaperRayBlockerRows.row labels answer.blocker)
  let u := (GeneralPaperBasisDirection.columnRun state.rows (next hj)).1
  let v := rowPrefix newRow (Nat.le_of_lt hj)
  let a := newRow.coefficients.read (next hj)
  let updated := GeneralPaperBasisStoredStep.run state.determinant state.adjugate u v a
  (∀ i,(u.read i).natAbs≤m+1) ∧ (∀ i,(v.read i).natAbs≤m+1) ∧ a.natAbs≤m+1 ∧
  updated.determinant.natAbs≤GeneralPaperBasisUpdateOperandSize.nextBound j (prepare m k).H (m+1) ∧
  ∀ i l,(updated.determinant*(state.adjugate.read i).read l+
    (mulVecRun state.adjugate u).1.read i*(rowRun v state.adjugate).1.read l).natAbs≤
      GeneralPaperBasisUpdateOperandSize.nextBound j (prepare m k).H (m+1)*(prepare m k).H+
        (j*(prepare m k).H*(m+1))*(j*(m+1)*(prepare m k).H)

theorem from_ray {T m j : ℕ} (k : ℕ) (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state)
    (answer : GeneralPaperRayEndpoint.Answer T m (prepare m k).K)
    (hContract : GeneralPaperRayEndpointSound.Contract (S:=S) dict v h ((betaN:ℚ)/(N:ℚ))
      (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
      (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity) answer) :
    Contract k dict.label state hj answer := by
  have hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h
      (((betaN:ℚ)/(N:ℚ):ℚ):ℝ)
      (fun a => (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point a:ℝ)) := by
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,reader,GeneralPaperBasisFreshPointSound.values] using inv.feasible
  obtain ⟨r,hOriginal,_⟩ := GeneralPaperRayEndpointReal.real_contract dict v h ((betaN:ℚ)/(N:ℚ)) _ _ answer hStart hContract
  have hNew (a : Fin (m*((prepare m k).K-1))) :
      ((GeneralPaperBasisDenseRow.build (GeneralPaperRayBlockerRows.row dict.label answer.blocker)).coefficients.read a).natAbs≤m+1 := by
    rw [hOriginal]
    exact GeneralPaperBasisRowSize.build_coefficient hm dict.label (GeneralPaperStrictScore.score v S) h r a
  have hU (i : Fin j) : ((GeneralPaperBasisDirection.columnRun state.rows (next hj)).1.read i).natAbs≤m+1 := by
    rw [GeneralPaperBasisDirection.column_read]
    exact GeneralPaperBasisRowSize.coefficient hm dict v S h N betaN initialGrid (Nat.le_of_lt hj) state inv i (next hj)
  have hV (i : Fin j) : ((rowPrefix (GeneralPaperBasisDenseRow.build (GeneralPaperRayBlockerRows.row dict.label answer.blocker))
      (Nat.le_of_lt hj)).read i).natAbs≤m+1 := by
    simp only [rowPrefix,FixedArrayTable.read_ofFn]
    exact hNew _
  have hc := GeneralPaperBasisCacheSize.cache_H k hm dict v S h N betaN initialGrid (Nat.le_of_lt hj) state inv
  exact ⟨hU,hV,hNew _,GeneralPaperBasisUpdateOperandSize.determinant _ _ _ _ _ _ _ hc.1 hc.2 hU hV (hNew _),
    GeneralPaperBasisUpdateOperandSize.update_numerator _ _ _ _ _ _ _ hc.1 hc.2 hU hV (hNew _)⟩

theorem actual_ray {T m j : ℕ} (k : ℕ) (hm : 0<m) (scoreDepth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (hK : 0<(prepare m k).K) (S h N : ℕ) (hCap : S<2^scoreDepth) (betaN : ℤ)
    (initialGrid : Vector (m*((prepare m k).K-1))) (state : State j (m*((prepare m k).K-1)))
    (hj : j<m*((prepare m k).K-1)) (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state) :
    ∃ answer,GeneralPaperRayEndpoint.prepared dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h
      ((betaN:ℚ)/(N:ℚ))
      (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
      (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity)=some answer ∧
      Contract k dict.label state hj answer := by
  obtain ⟨a,ha⟩ := next_velocity state.determinant state.adjugate state.rows (next hj) rfl
  have hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h
      (((betaN:ℚ)/(N:ℚ):ℚ):ℝ)
      (fun a => (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point a:ℝ)) := by
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,reader,GeneralPaperBasisFreshPointSound.values] using inv.feasible
  obtain ⟨answer,hr,hc⟩ := GeneralPaperRayEndpointSound.endpoint_sound scoreDepth dict v hK hCap h ((betaN:ℚ)/(N:ℚ)) _ _ hStart a ha
  exact ⟨answer,hr,from_ray k hm dict v S h N betaN initialGrid state hj inv answer hc⟩

end Blotto.GeneralPaperBasisAdvanceSize
