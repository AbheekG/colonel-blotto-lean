import Blotto.GeneralPaperStreamingQuotient

/-! Fixed-register small-step source programs for the two quotient loops.
Each step replaces the current configuration and jumps to the same loop.
The inductive runs are erased proofs, not stored execution histories.
-/
namespace Blotto.GeneralPaperQuotientRegisters
open GeneralPaperQuotientTraversal
set_option autoImplicit false
set_option maxHeartbeats 6000000

structure UpState where
  scale : ℕ
  fuel : ℕ
  count : ℕ

def upStep (n : ℕ) (s : UpState) : Option UpState := match s.fuel with
  | 0 => none
  | fuel+1 => if n<s.scale then none else some ⟨2*s.scale,fuel,s.count+1⟩

def upValue (n : ℕ) (s : UpState) : Top := up n s.scale s.fuel s.count

theorem up_step_value (n : ℕ) (s next : UpState) (h : upStep n s=some next) :
    upValue n s=upValue n next := by
  obtain ⟨scale,fuel,count⟩ := s
  cases fuel with
  | zero => cases h
  | succ fuel =>
    dsimp only [upStep] at h
    split at h
    · cases h
    · rename_i hn
      have he := Option.some.inj h
      subst next
      simp only [upValue,up,ite_eq_right hn]

theorem up_stop_value (n : ℕ) (s : UpState) (h : upStep n s=none) :
    upValue n s=⟨s.scale,s.count⟩ := by
  obtain ⟨scale,fuel,count⟩ := s
  cases fuel with
  | zero => rfl
  | succ fuel =>
    dsimp only [upStep] at h
    split at h
    · rename_i hn
      simp only [upValue,up,ite_eq_left hn]
    · cases h

inductive UpRuns (n : ℕ) : UpState → Top → Prop
  | stop (s : UpState) (h : upStep n s=none) : UpRuns n s ⟨s.scale,s.count⟩
  | step (s next : UpState) (result : Top) (h : upStep n s=some next)
      (later : UpRuns n next result) : UpRuns n s result

theorem up_runs (n : ℕ) (s : UpState) : UpRuns n s (upValue n s) := by
  obtain ⟨scale,fuel,count⟩ := s
  induction fuel generalizing scale count with
  | zero => exact .stop _ rfl
  | succ fuel ih =>
    by_cases hn : n<scale
    · have hs : upStep n ⟨scale,fuel+1,count⟩=none := by simp only [upStep,ite_eq_left hn]
      rw [up_stop_value _ _ hs]
      exact .stop _ hs
    · have hs : upStep n ⟨scale,fuel+1,count⟩=some ⟨2*scale,fuel,count+1⟩ := by simp only [upStep,ite_eq_right hn]
      rw [up_step_value _ _ _ hs]
      exact .step _ _ _ hs (ih _ _)

structure DownState where
  scale : ℕ
  remaining : ℕ
  quotient : ℕ
  remainder : ℕ

def downStep (s : DownState) : Option DownState := match s.remaining with
  | 0 => none
  | remaining+1 =>
    let smaller := s.scale/2
    let qr := restore smaller (s.quotient,s.remainder)
    some ⟨smaller,remaining,qr.1,qr.2⟩

def downValue (s : DownState) : ℕ × ℕ := down s.scale s.remaining (s.quotient,s.remainder)

theorem down_step_value (s next : DownState) (h : downStep s=some next) : downValue s=downValue next := by
  obtain ⟨scale,remaining,q,r⟩ := s
  cases remaining with
  | zero => cases h
  | succ remaining =>
    dsimp only [downStep] at h
    have he := Option.some.inj h
    subst next
    rfl

theorem down_stop_value (s : DownState) (h : downStep s=none) : downValue s=(s.quotient,s.remainder) := by
  obtain ⟨scale,remaining,q,r⟩ := s
  cases remaining with
  | zero => rfl
  | succ remaining => cases h

inductive DownRuns : DownState → (ℕ × ℕ) → Prop
  | stop (s : DownState) (h : downStep s=none) : DownRuns s (s.quotient,s.remainder)
  | step (s next : DownState) (result : ℕ × ℕ) (h : downStep s=some next)
      (later : DownRuns next result) : DownRuns s result

theorem down_runs (s : DownState) : DownRuns s (downValue s) := by
  obtain ⟨scale,remaining,q,r⟩ := s
  induction remaining generalizing scale q r with
  | zero => exact .stop _ rfl
  | succ remaining ih =>
    let next : DownState := ⟨scale/2,remaining,(restore (scale/2) (q,r)).1,(restore (scale/2) (q,r)).2⟩
    have hs : downStep ⟨scale,remaining+1,q,r⟩=some next := rfl
    rw [down_step_value _ _ hs]
    exact .step _ _ _ hs (ih _ _ _)

end Blotto.GeneralPaperQuotientRegisters
