import Blotto.GeneralPaperRayEndpoint

/-! The actual ray program returns the exact maximal forward endpoint
and an original tight positive-direction blocker, with no endpoint oracle.
This covers endpoint zero and a start on a lower-dimensional face.
-/
namespace Blotto.GeneralPaperRayEndpointSound
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStrictScore GeneralPaperRayFeasibility
open GeneralPaperRayEndpoint GeneralPaperRayBlockerRows
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def Contract {T m S K : ℕ} (d : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) (answer : Answer T m K) : Prop :=
  0≤answer.time ∧ answer.time≤1 ∧
    (∃ index,row d.label answer.blocker=constraints d.label (score v S) h index) ∧
      (GeneralPaperRayOriginalResidual.evaluate (row d.label answer.blocker) beta x w).value answer.time=0 ∧
        0<(GeneralPaperRayOriginalResidual.evaluate (row d.label answer.blocker) beta x w).slope ∧
          (∀ t : ℚ,0≤t ∧ t≤answer.time → GeneralPaperAffineConstraintRows.Feasible d.label (score v S) h (beta:ℝ)
            (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ))) ∧
              ∀ t : ℚ,answer.time<t → ¬GeneralPaperAffineConstraintRows.Feasible d.label (score v S) h (beta:ℝ)
                (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ))

theorem endpoint_sound {T m S K : ℕ} (scoreDepth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (hK : 0<K) (hCap : S<2^scoreDepth) (h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ)
    (hStart : GeneralPaperAffineConstraintRows.Feasible d.label (score v S) h (beta:ℝ) (fun j => (x j:ℝ)))
    (next : Variable m K) (hVelocity : w next=1) :
    ∃ answer,execute scoreDepth d v S h beta x w=some answer ∧ Contract (S := S) d v h beta x w answer := by
  obtain ⟨c,hScan,hNonnegative,hOne,hPositive,hTight⟩ := GeneralPaperStaticRaySound.finite_endpoint
    d.label (score v S) h (beta:ℝ) x w hStart next hVelocity
  have hZero : test v S h beta x w 0=true := by
    apply ((full_iff d.label v hK S h beta x w 0).mp ?_).2
    simpa only [Rat.cast_zero,zero_mul,add_zero] using hStart
  have hData (t : ℚ) := GeneralPaperRayPricedPredicate.actual_data scoreDepth d v S hK hCap x w h beta t
  have hStatic := GeneralPaperStaticRaySound.forward_static d.label (score v S) h (beta:ℝ) x w hStart c hScan
  cases hAccepted : test v S h beta x w c.time with
  | true =>
    refine ⟨⟨c.time,.inl c.blocker⟩,?_,hNonnegative,hOne,static_original d.label (score v S) h c.blocker,?_,?_,?_,?_⟩
    · simp only [execute,prepared,hScan,hData,hAccepted,ite_true]
    · change (GeneralPaperRayOriginalResidual.evaluate (GeneralPaperStaticRayRows.row d.label c.blocker) beta x w).value c.time=0
      rw [GeneralPaperRayOriginalResidual.static_eq]
      exact hTight
    · change 0<(GeneralPaperRayOriginalResidual.evaluate (GeneralPaperStaticRayRows.row d.label c.blocker) beta x w).slope
      rw [GeneralPaperRayOriginalResidual.static_eq]
      exact hPositive
    · intro t ht
      exact (full_iff d.label v hK S h beta x w t).mpr ⟨hStatic t ht,
        GeneralPaperRayBracket.test_downclosed v hK S h beta x w hZero c.time hAccepted t ht⟩
    · intro t ht hf
      exact GeneralPaperStaticRaySound.beyond_static d.label (beta:ℝ) x w c hScan t ht
        ((full_iff d.label v hK S h beta x w t).mp hf).1
  | false =>
    have hStrict : 0<c.time := by
      by_contra hn
      have hz : c.time=0 := by linarith only [hn,hNonnegative]
      rw [hz,hZero] at hAccepted
      contradiction
    obtain ⟨high,hRun,hN,hCap',hTrue,hHigh,hHighTight,hHighSlope,hBeyond⟩ := GeneralPaperRayHighSearch.search_sound
      scoreDepth d v hK hCap x w h beta 0 c.time le_rfl hStrict hZero hZero hAccepted
    have hValues (t : ℚ) := GeneralPaperRayBlockerRows.high_value d.label (score v S) h high.labels hHigh beta x w t
    have hSlopes := GeneralPaperRayBlockerAlgebra.slope_equal
      (GeneralPaperRayOriginalResidual.evaluate (row d.label (.inr high.labels)) beta x w)
      (GeneralPaperRayTupleResidual.residual x w beta high.labels.read) hValues
    refine ⟨⟨high.time,.inr high.labels⟩,?_,hN,hCap'.le.trans hOne,high_original d.label (score v S) h high.labels hHigh,?_,?_,?_,?_⟩
    · change GeneralPaperRayHighSearch.prepared (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1 S h beta x w 0 c.time=some high at hRun
      simp only [execute,prepared,hScan,hData,hAccepted,Bool.false_eq_true,ite_false,hRun,Option.map_some]
    · change (GeneralPaperRayOriginalResidual.evaluate (row d.label (.inr high.labels)) beta x w).value high.time=0
      rw [hValues]
      exact hHighTight
    · change 0<(GeneralPaperRayOriginalResidual.evaluate (row d.label (.inr high.labels)) beta x w).slope
      rw [hSlopes]
      exact hHighSlope
    · intro t ht
      exact (full_iff d.label v hK S h beta x w t).mpr
        ⟨hStatic t ⟨ht.1,ht.2.trans hCap'.le⟩,
          GeneralPaperRayBracket.test_downclosed v hK S h beta x w hZero high.time hTrue t ht⟩
    · intro t ht hf
      have hBad := hBeyond t ht
      have hGood := (GeneralPaperAffineConstraintSemantics.high_tuple_holds d.label (score v S) h
        ⟨high.labels.read,hHigh⟩ (beta:ℝ) _).mp (hf (.inr (.inr (.inr ⟨high.labels.read,hHigh⟩))))
      have hR : (0:ℝ)<((GeneralPaperRayTupleResidual.residual x w beta high.labels.read).value t:ℝ) := by exact_mod_cast hBad
      rw [GeneralPaperRayTupleResidual.residual_value,Rat.cast_sub,GeneralPaperRayAnchorCosts.tuple_cast] at hR
      linarith only [hR,hGood]

end Blotto.GeneralPaperRayEndpointSound
