import Blotto.GeneralPaperBasisInvariant

/-! One executed ray search returns an original blocker and advances the
invariant. Fresh recomputation is identified with the feasible endpoint;
there is no supplied endpoint, basis, direction or rationalization oracle.
-/
namespace Blotto.GeneralPaperBasisStepSound
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStrictScore
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperBasisCoordinates GeneralPaperBasisOriginalDirection GeneralPaperBasisFreshPointSound
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem advance_valid {T m K j : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (state : State j (m*(K-1))) (hj : j<m*(K-1))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state)
    (answer : GeneralPaperRayEndpoint.Answer T m K)
    (hContract : GeneralPaperRayEndpointSound.Contract (S := S) dict v h ((betaN:ℚ)/(N:ℚ))
      (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
      (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity) answer) :
    Invariant dict v S h N betaN initialGrid (Nat.succ_le_of_lt hj) (advance dict.label state hj answer) := by
  have hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h (((betaN:ℚ)/(N:ℚ):ℚ):ℝ)
      (fun a => (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point a:ℝ)) := by
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,reader,values] using inv.feasible
  obtain ⟨r,hOriginal,hTight,hPositive,hForward,_⟩ := GeneralPaperRayEndpointReal.real_contract dict v h
    ((betaN:ℚ)/(N:ℚ)) _ _ answer hStart hContract
  have hUpdated := GeneralPaperBasisAppendCache.original_positive state.determinant inv.nonzero state.adjugate state.rows
    (next hj) rfl (Nat.le_of_lt hj) (Nat.succ_le_of_lt hj) inv.cache
    (GeneralPaperRayBlockerRows.row dict.label answer.blocker) hPositive
  have hPackedTight : rowValue (GeneralPaperBasisDenseRow.build (GeneralPaperRayBlockerRows.row dict.label answer.blocker))
      (fun k => values N betaN state.determinant state.adjugate state.rows initialGrid k+
        (answer.time:ℝ)*GeneralPaperBasisDirectionSound.values state.determinant state.adjugate state.rows (next hj) k)=
      bound (GeneralPaperBasisDenseRow.build (GeneralPaperRayBlockerRows.row dict.label answer.blocker)) N betaN := by
    unfold rowValue
    rw [GeneralPaperBasisDenseRow.build_evaluate]
    simpa only [bound,GeneralPaperBasisDenseRow.build_constant,GeneralPaperBasisDenseRow.build_slope,
      Row.bound,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,reader,values,GeneralPaperBasisDirectionSound.values] using hTight
  have hSame := GeneralPaperBasisEndpointRecompute.recompute N hN betaN state.determinant inv.nonzero state.adjugate
    state.rows initialGrid (next hj) rfl (Nat.le_of_lt hj) (Nat.succ_le_of_lt hj) inv.cache
    (GeneralPaperBasisDenseRow.build (GeneralPaperRayBlockerRows.row dict.label answer.blocker)) (answer.time:ℝ)
    hPackedTight _ hUpdated.1 _ hUpdated.2
  refine ⟨hUpdated.1,hUpdated.2,?_,?_⟩
  · intro i
    by_cases hi : i.val<j
    · let k : Fin j := ⟨i.val,hi⟩
      have he : i=k.castSucc := Fin.ext rfl
      change ∃ r : Index T m K (score v S) h, (GeneralPaperBasisAppendRows.append state.rows _).read i=GeneralPaperBasisDenseRow.build (constraints dict.label (score v S) h r)
      rw [he,GeneralPaperBasisAppendRows.old_read]
      exact inv.original k
    · have he : i=GeneralPaperBasisAppendIndex.encode j none := by
        apply Fin.ext
        change i.val=j
        have hb := i.isLt
        omega
      refine ⟨r,?_⟩
      change (GeneralPaperBasisAppendRows.append state.rows _).read i=_
      rw [he,GeneralPaperBasisAppendRows.last_read,hOriginal]
  · simp only [advance]
    rw [hSame]
    have hf := hForward (answer.time:ℝ) ⟨by exact_mod_cast hContract.1,le_rfl⟩
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,reader,values,GeneralPaperBasisDirectionSound.values] using hf

theorem step_valid {T m K j : ℕ} (scoreDepth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (hK : 0<K) (S h N : ℕ) (hN : 0<N) (hCap : S<2^scoreDepth) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) (state : State j (m*(K-1))) (hj : j<m*(K-1))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state) :
    ∃ newState,step dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h N betaN initialGrid state hj=some newState ∧
      Invariant dict v S h N betaN initialGrid (Nat.succ_le_of_lt hj) newState := by
  obtain ⟨a,ha⟩ := next_velocity state.determinant state.adjugate state.rows (next hj) rfl
  have hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h (((betaN:ℚ)/(N:ℚ):ℚ):ℝ)
      (fun a => (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point a:ℝ)) := by
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,reader,values] using inv.feasible
  obtain ⟨answer,hRun,hContract⟩ := GeneralPaperRayEndpointSound.endpoint_sound scoreDepth dict v hK hCap h
    ((betaN:ℚ)/(N:ℚ)) _ _ hStart a ha
  refine ⟨advance dict.label state hj answer,?_,advance_valid dict v S h N hN betaN initialGrid state hj inv answer hContract⟩
  change GeneralPaperRayEndpoint.prepared dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h
    ((betaN:ℚ)/(N:ℚ)) _ _=some answer at hRun
  simp only [step,hRun,Option.map_some]

end Blotto.GeneralPaperBasisStepSound
