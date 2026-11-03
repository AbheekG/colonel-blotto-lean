import Blotto.GeneralPaperRayEndpointSound

/-! The computed rational endpoint is maximal over ALL real forward ray
parameters. The returned original row is tight there and has positive
real directional coefficient, which is the Schur derivative needed by
the subsequent active-basis rank argument.
-/
namespace Blotto.GeneralPaperRayEndpointReal
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStrictScore
open GeneralPaperRayEndpoint GeneralPaperRayEndpointSound GeneralPaperRayBlockerRows
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem linear_real {v : Type*} (r : Row v) (x w : v → ℝ) (t : ℝ) :
    r.linear.evaluate (fun j => x j+t*w j)=r.linear.evaluate x+t*r.linear.evaluate w := by
  suffices hTerms : ∀ terms : List (v × ℤ),
      (LinearRow.mk terms 0).evaluate (fun j => x j+t*w j)=
        (LinearRow.mk terms 0).evaluate x+t*(LinearRow.mk terms 0).evaluate w from hTerms r.terms
  intro terms
  induction terms with
  | nil => simp only [LinearRow.evaluate,List.map_nil,List.sum_nil,mul_zero,add_zero]
  | cons term rest ih =>
    change (term.2:ℝ)*(x term.1+t*w term.1)+(LinearRow.mk rest 0).evaluate (fun j => x j+t*w j)=_
    rw [ih]
    simp only [LinearRow.evaluate,List.map_cons,List.sum_cons]
    ring

theorem row_segment {v : Type*} (r : Row v) (beta : ℝ) (x w : v → ℝ) (cap t : ℝ)
    (hStart : r.Holds beta x) (hEnd : r.Holds beta (fun j => x j+cap*w j)) (ht : 0≤t ∧ t≤cap) :
    r.Holds beta (fun j => x j+t*w j) := by
  change r.linear.evaluate (fun j => x j+cap*w j)≤r.bound beta at hEnd
  change r.linear.evaluate (fun j => x j+t*w j)≤r.bound beta
  rw [linear_real] at hEnd ⊢
  by_cases hw : 0≤r.linear.evaluate w
  · have hm := mul_le_mul_of_nonneg_right ht.2 hw
    linarith only [hEnd,hm]
  · have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hw) ht.1
    change r.linear.evaluate x≤r.bound beta at hStart
    linarith only [hStart,hm]

theorem real_contract {T m S K : ℕ} (d : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) (answer : Answer T m K)
    (hStart : GeneralPaperAffineConstraintRows.Feasible d.label (score v S) h (beta:ℝ) (fun j => (x j:ℝ)))
    (hContract : Contract (S := S) d v h beta x w answer) :
    ∃ index,row d.label answer.blocker=constraints d.label (score v S) h index ∧
      (row d.label answer.blocker).linear.evaluate (fun j => (x j:ℝ)+(answer.time:ℝ)*(w j:ℝ))=
        (row d.label answer.blocker).bound (beta:ℝ) ∧
          0<(row d.label answer.blocker).linear.evaluate (fun j => (w j:ℝ)) ∧
            (∀ t : ℝ,0≤t ∧ t≤(answer.time:ℝ) → GeneralPaperAffineConstraintRows.Feasible d.label (score v S) h (beta:ℝ)
              (fun j => (x j:ℝ)+t*(w j:ℝ))) ∧
                ∀ t : ℝ,(answer.time:ℝ)<t → ¬GeneralPaperAffineConstraintRows.Feasible d.label (score v S) h (beta:ℝ)
                  (fun j => (x j:ℝ)+t*(w j:ℝ)) := by
  rcases hContract with ⟨hNonnegative,_,⟨index,hOriginal⟩,hTight,hPositive,hForward,_⟩
  have hEnd := hForward answer.time ⟨hNonnegative,le_rfl⟩
  have hCast := GeneralPaperRayOriginalResidual.value_cast (row d.label answer.blocker) beta x w answer.time
  have hZero : ((GeneralPaperRayOriginalResidual.evaluate (row d.label answer.blocker) beta x w).value answer.time:ℝ)=0 := by exact_mod_cast hTight
  rw [hZero] at hCast
  have hRowTight := sub_eq_zero.mp hCast.symm
  have hDirection : (0:ℝ)<((GeneralPaperRayOriginalResidual.evaluate (row d.label answer.blocker) beta x w).slope:ℝ) := by exact_mod_cast hPositive
  rw [GeneralPaperRayOriginalResidual.slope_cast] at hDirection
  refine ⟨index,hOriginal,hRowTight,hDirection,?_,?_⟩
  · intro t ht i
    exact row_segment (constraints d.label (score v S) h i) (beta:ℝ) (fun j => (x j:ℝ)) (fun j => (w j:ℝ))
      (answer.time:ℝ) t (hStart i) (hEnd i) ht
  · intro t ht hf
    have hh := hf index
    rw [←hOriginal] at hh
    change (row d.label answer.blocker).linear.evaluate (fun j => (x j:ℝ)+t*(w j:ℝ))≤_ at hh
    rw [linear_real] at hh hRowTight
    have hp := mul_pos (sub_pos.mpr ht) hDirection
    nlinarith only [hh,hRowTight,hp]

theorem execute_real {T m S K : ℕ} (scoreDepth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (hK : 0<K) (hCap : S<2^scoreDepth) (h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ)
    (hStart : GeneralPaperAffineConstraintRows.Feasible d.label (score v S) h (beta:ℝ) (fun j => (x j:ℝ)))
    (next : Variable m K) (hVelocity : w next=1) :
    ∃ answer,execute scoreDepth d v S h beta x w=some answer ∧ Contract (S := S) d v h beta x w answer ∧
      ∀ t : ℝ,(0≤t ∧ t≤(answer.time:ℝ)) ↔ (0≤t ∧
        GeneralPaperAffineConstraintRows.Feasible d.label (score v S) h (beta:ℝ) (fun j => (x j:ℝ)+t*(w j:ℝ))) := by
  obtain ⟨answer,hRun,hContract⟩ := endpoint_sound scoreDepth d v hK hCap h beta x w hStart next hVelocity
  obtain ⟨_,_,_,_,hForward,hBeyond⟩ := real_contract d v h beta x w answer hStart hContract
  refine ⟨answer,hRun,hContract,?_⟩
  intro t
  constructor
  · intro ht
    exact ⟨ht.1,hForward t ht⟩
  · rintro ⟨ht,hf⟩
    refine ⟨ht,?_⟩
    by_contra hn
    exact hBeyond t (lt_of_not_ge hn) hf

end Blotto.GeneralPaperRayEndpointReal
