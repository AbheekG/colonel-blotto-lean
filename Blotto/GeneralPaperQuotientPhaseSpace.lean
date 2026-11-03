import Blotto.GeneralPaperQuotientRegisterSpace

/-! Include the retained top record, phase handoff, terminal state and
returned result in the quotient register-space bound. Every-step windows
are source reservations; proof histories and price annotations are erased.
-/
namespace Blotto.GeneralPaperQuotientPhaseSpace
open GeneralPaperQuotientTraversal GeneralPaperQuotientRegisters GeneralPaperQuotientRegisterBounds
open GeneralPaperQuotientRegisterSpace
set_option autoImplicit false
set_option maxHeartbeats 8000000

def topFootprint (W : ℕ) (top : Top) : ℕ := binaryWordWidth top.scale+binaryWordWidth top.depth+4*W

def resultFootprint (W : ℕ) (r : GeneralPaperNaturalGrowingQuotient.Result) : ℕ :=
  binaryWordWidth r.quotient+binaryWordWidth r.remainder+binaryWordWidth r.depth+binaryWordWidth r.work+8*W

def finalUp (n a fuel : ℕ) : UpState :=
  let top := up n a fuel 0
  ⟨top.scale,fuel-top.depth,top.depth⟩

theorem final_up_valid (n a fuel : ℕ) (ha : 0<a) : UpValid n a fuel (finalUp n a fuel) := by
  have hb := up_result n a fuel ⟨a,fuel,0⟩ (up_initial n a fuel ha)
  change 0<(up n a fuel 0).scale ∧ (up n a fuel 0).scale≤magnitude n a ∧ (up n a fuel 0).depth≤fuel at hb
  dsimp only [finalUp,UpValid]
  exact ⟨hb.1,hb.2.1,by omega⟩

theorem top_footprint (W n a fuel : ℕ) (ha : 0<a) (hW : counterWord fuel≤W) :
    topFootprint W (up n a fuel 0)≤operandWord n a+5*W := by
  have hb := up_result n a fuel ⟨a,fuel,0⟩ (up_initial n a fuel ha)
  change 0<(up n a fuel 0).scale ∧ (up n a fuel 0).scale≤magnitude n a ∧ (up n a fuel 0).depth≤fuel at hb
  have hs := value_word n a (up n a fuel 0).scale hb.2.1
  have hd := binaryWordWidth_mono (show (up n a fuel 0).depth≤fuel+1 by omega)
  unfold topFootprint counterWord at *
  omega

theorem work_word (fuel depth W : ℕ) (hd : depth≤fuel) (hW : counterWord fuel≤W) :
    binaryWordWidth (14*depth+4)≤W := by
  have hv : 14*depth+4≤32*(fuel+1)+128 := by omega
  have hm := binaryWordWidth_mono hv
  have hp := binaryWordWidth_mul 32 (fuel+1)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (32*(fuel+1)) 128
  have h32 : binaryWordWidth 32=6 := by decide
  have h128 : binaryWordWidth 128=8 := by decide
  unfold counterWord at hW
  omega

theorem result_footprint (W n a fuel : ℕ) (ha : 0<a) (hW : counterWord fuel≤W) :
    resultFootprint W (GeneralPaperStreamingQuotient.run n a fuel)≤2*operandWord n a+10*W := by
  have hb := GeneralPaperNaturalGrowingQuotient.operand_bounds n a fuel ha
  have hc := GeneralPaperNaturalGrowingQuotient.counters n a fuel
  have hq := value_word n a (GeneralPaperNaturalGrowingQuotient.run n a fuel).quotient (by unfold magnitude; omega)
  have hr := value_word n a (GeneralPaperNaturalGrowingQuotient.run n a fuel).remainder (by unfold magnitude; omega)
  have hd := binaryWordWidth_mono (show (GeneralPaperNaturalGrowingQuotient.run n a fuel).depth≤fuel+1 by omega)
  have hw := work_word fuel (GeneralPaperNaturalGrowingQuotient.run n a fuel).depth W hc.2 hW
  rw [←hc.1] at hw
  rw [GeneralPaperStreamingQuotient.data]
  unfold resultFootprint counterWord at *
  omega

def reservation (model : RationalCostModel) (W n a : ℕ) : ℕ := 128*(W+model.rat (operandWord n a))

def handoff (W n a fuel : ℕ) : ℕ :=
  upFootprint W n a (finalUp n a fuel)+topFootprint W (up n a fuel 0)+
    downFootprint W n a (initialDown n a fuel)+16*W

def finish (W n a fuel : ℕ) (s : DownState) : ℕ :=
  downFootprint W n a s+topFootprint W (up n a fuel 0)+
    resultFootprint W (GeneralPaperStreamingQuotient.run n a fuel)+16*W

theorem handoff_bound (model : RationalCostModel) (W n a fuel : ℕ) (ha : 0<a) (hW : counterWord fuel≤W) :
    handoff W n a fuel≤reservation model W n a := by
  have hu := up_footprint W n a fuel (finalUp n a fuel) (final_up_valid n a fuel ha) hW
  have ht := top_footprint W n a fuel ha hW
  have hd := down_footprint W n a fuel (initialDown n a fuel) (down_initial n a fuel ha) hW
  have hP := model.word_le (operandWord n a)
  unfold handoff reservation
  omega

theorem finish_bound (model : RationalCostModel) (W n a fuel : ℕ) (ha : 0<a) (hW : counterWord fuel≤W)
    (s : DownState) (h : DownValid n a fuel s) :
    finish W n a fuel s≤reservation model W n a := by
  have hd := down_footprint W n a fuel s h hW
  have ht := top_footprint W n a fuel ha hW
  have hr := result_footprint W n a fuel ha hW
  have hP := model.word_le (operandWord n a)
  unfold finish reservation
  omega

theorem reachable_up_window (model : RationalCostModel) (W n a fuel : ℕ) (ha : 0<a) (hW : counterWord fuel≤W)
    (s next : UpState) (h : UpReach n a fuel s) (hs : upStep n s=some next) :
    upWindow model W n a s next+16*W≤reservation model W n a := by
  have hw := up_window model W n a fuel s next (up_reachable n a fuel ha s h) hs hW
  unfold reservation
  omega

theorem reachable_down_window (model : RationalCostModel) (W n a fuel : ℕ) (ha : 0<a) (hW : counterWord fuel≤W)
    (s next : DownState) (h : DownReach n a fuel s) (hs : downStep s=some next) :
    downWindow model W n a s next+topFootprint W (up n a fuel 0)+16*W≤reservation model W n a := by
  have hw := down_window model W n a fuel ha s next (down_reachable n a fuel ha s h) hs hW
  have ht := top_footprint W n a fuel ha hW
  have hP := model.word_le (operandWord n a)
  unfold reservation
  omega

end Blotto.GeneralPaperQuotientPhaseSpace
