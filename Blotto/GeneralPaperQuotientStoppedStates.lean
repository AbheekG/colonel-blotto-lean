import Blotto.GeneralPaperStreamingQuotientWork

/-! Connect actual halted register configurations to the composed quotient.
The proof runs and reachability histories are propositions and are erased;
only the current fixed-size register state and retained top survive.
-/
namespace Blotto.GeneralPaperQuotientStoppedStates
open GeneralPaperQuotientTraversal GeneralPaperQuotientRegisters GeneralPaperQuotientRegisterBounds
open GeneralPaperQuotientRegisterSpace GeneralPaperQuotientPhaseSpace
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem up_value_preserved (n a fuel : ℕ) (s : UpState) (h : UpReach n a fuel s) :
    up n a fuel 0=upValue n s := by
  induction h with
  | initial => rfl
  | next s next past step ih => exact ih.trans (up_step_value n s next step)

theorem up_stopped (n a fuel : ℕ) (ha : 0<a) (s : UpState) (h : UpReach n a fuel s) (hs : upStep n s=none) :
    s=finalUp n a fuel := by
  have hv := up_value_preserved n a fuel s h
  rw [up_stop_value n s hs] at hv
  have hScale := congrArg Top.scale hv
  have hCount := congrArg Top.depth hv
  have hb := up_reachable n a fuel ha s h
  obtain ⟨scale,remaining,count⟩ := s
  dsimp only at hScale hCount
  have hRemaining : remaining=fuel-count := by dsimp only [UpValid] at hb; omega
  unfold finalUp
  dsimp only
  rw [hScale,hCount,hRemaining]

theorem down_value_preserved (n a fuel : ℕ) (s : DownState) (h : DownReach n a fuel s) :
    downValue (initialDown n a fuel)=downValue s := by
  induction h with
  | initial => rfl
  | next s next past step ih => exact ih.trans (down_step_value s next step)

theorem down_stopped (n a fuel : ℕ) (s : DownState) (h : DownReach n a fuel s) (hs : downStep s=none) :
    (s.quotient,s.remainder)=((GeneralPaperStreamingQuotient.run n a fuel).quotient,
      (GeneralPaperStreamingQuotient.run n a fuel).remainder) := by
  have hv := down_value_preserved n a fuel s h
  rw [down_stop_value s hs] at hv
  exact hv.symm

theorem actual_handoff (model : RationalCostModel) (W n a fuel : ℕ) (ha : 0<a) (hW : counterWord fuel≤W)
    (s : UpState) (h : UpReach n a fuel s) (hs : upStep n s=none) :
    upFootprint W n a s+topFootprint W (up n a fuel 0)+
      downFootprint W n a (initialDown n a fuel)+16*W≤reservation model W n a := by
  rw [up_stopped n a fuel ha s h hs]
  exact handoff_bound model W n a fuel ha hW

theorem actual_finish (model : RationalCostModel) (W n a fuel : ℕ) (ha : 0<a) (hW : counterWord fuel≤W)
    (s : DownState) (h : DownReach n a fuel s) (_hs : downStep s=none) :
    finish W n a fuel s≤reservation model W n a :=
  finish_bound model W n a fuel ha hW s (down_reachable n a fuel ha s h)

end Blotto.GeneralPaperQuotientStoppedStates
