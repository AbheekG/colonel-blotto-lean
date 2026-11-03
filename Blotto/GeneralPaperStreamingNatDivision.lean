import Blotto.GeneralPaperStreamingDivisionSpace

/-! Native natural division reuses the streamed remainder directly.
This removes a redundant product/subtraction while preserving the entire
old result and work annotation. Cost and terminal live data remain bounded.
-/
namespace Blotto.GeneralPaperStreamingNatDivision
open GeneralPaperQuotientRegisterSpace GeneralPaperQuotientPhaseSpace
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run (n d fuel : ℕ) : GeneralPaperConstructedNatDivision.Result :=
  let found := GeneralPaperStreamingQuotient.run n d fuel
  ⟨found.quotient,found.remainder,found.depth,found.work+12⟩

theorem data (n d fuel : ℕ) : run n d fuel=GeneralPaperConstructedNatDivision.run n d fuel := by
  have hi := GeneralPaperNaturalGrowingQuotient.invariant n d fuel
  have hr : n-d*(GeneralPaperNaturalGrowingQuotient.run n d fuel).quotient=
      (GeneralPaperNaturalGrowingQuotient.run n d fuel).remainder := by omega
  simp only [run,GeneralPaperStreamingQuotient.data,GeneralPaperConstructedNatDivision.run,
    ←GeneralPaperNaturalGrowingQuotient.data,GeneralPaperNaturalGrowingQuotient.lift,hr]

def cost (model : RationalCostModel) (W n d fuel : ℕ) : ℕ :=
  GeneralPaperStreamingQuotientWork.cost model W n d fuel+64*W

theorem work (model : RationalCostModel) (W n d fuel : ℕ) (hd : 0<d) :
    cost model W n d fuel≤1024*((GeneralPaperConstructedNatDivision.run n d fuel).depth+1)*
      (W+model.rat (operandWord n d)) := by
  let F := W+model.rat (operandWord n d)
  have hw := GeneralPaperStreamingQuotientWork.work model W n d fuel hd
  have he := congrArg GeneralPaperGrowingQuotient.Result.depth (GeneralPaperStreamingQuotient.rational_data n d fuel)
  change (GeneralPaperStreamingQuotient.run n d fuel).depth=(GeneralPaperConstructedNatDivision.run n d fuel).depth at he
  rw [he] at hw
  change _≤512*((GeneralPaperConstructedNatDivision.run n d fuel).depth+1)*F at hw
  unfold cost
  change _≤1024*((GeneralPaperConstructedNatDivision.run n d fuel).depth+1)*F
  have hWF : W≤F := Nat.le_add_right _ _
  nlinarith only [hw,hWF,Nat.zero_le ((GeneralPaperConstructedNatDivision.run n d fuel).depth*F)]

theorem annotation_word (fuel depth W : ℕ) (hd : depth≤fuel) (hW : counterWord fuel≤W) :
    binaryWordWidth (14*depth+16)≤W := by
  have h := binaryWordWidth_mono (show 14*depth+16≤32*(fuel+1)+128 by omega)
  have hm := binaryWordWidth_mul 32 (fuel+1)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (32*(fuel+1)) 128
  have h32 : binaryWordWidth 32=6 := by decide
  have h128 : binaryWordWidth 128=8 := by decide
  unfold counterWord at hW
  omega

def footprint (W : ℕ) (r : GeneralPaperConstructedNatDivision.Result) : ℕ :=
  binaryWordWidth r.quotient+binaryWordWidth r.remainder+binaryWordWidth r.depth+binaryWordWidth r.work+8*W

theorem result_space (W n d fuel : ℕ) (hd : 0<d) (hW : counterWord fuel≤W) :
    footprint W (run n d fuel)≤2*operandWord n d+10*W := by
  have hb := GeneralPaperNaturalGrowingQuotient.operand_bounds n d fuel hd
  have hc := GeneralPaperNaturalGrowingQuotient.counters n d fuel
  have hq := value_word n d (GeneralPaperNaturalGrowingQuotient.run n d fuel).quotient (by unfold GeneralPaperQuotientRegisterBounds.magnitude; omega)
  have hr := value_word n d (GeneralPaperNaturalGrowingQuotient.run n d fuel).remainder (by unfold GeneralPaperQuotientRegisterBounds.magnitude; omega)
  have hdep := binaryWordWidth_mono (show (GeneralPaperNaturalGrowingQuotient.run n d fuel).depth≤fuel+1 by omega)
  have hw := annotation_word fuel (GeneralPaperNaturalGrowingQuotient.run n d fuel).depth W hc.2 hW
  have hw' : binaryWordWidth ((GeneralPaperNaturalGrowingQuotient.run n d fuel).work+12)≤W := by
    simpa only [hc.1,Nat.add_assoc,Nat.reduceAdd] using hw
  simp only [run,GeneralPaperStreamingQuotient.data,footprint]
  unfold counterWord at hW
  omega

theorem reservation (model : RationalCostModel) (W n d fuel : ℕ) (hd : 0<d) (hW : counterWord fuel≤W) :
    GeneralPaperQuotientPhaseSpace.reservation model W n d+footprint W (run n d fuel)+16*W≤
      256*(W+model.rat (operandWord n d)) := by
  have hr := result_space W n d fuel hd hW
  have hp := model.word_le (operandWord n d)
  unfold GeneralPaperQuotientPhaseSpace.reservation
  omega

def priced (model : RationalCostModel) (W n d fuel : ℕ) : GeneralPaperConstructedNatDivision.Result × ℕ :=
  (run n d fuel,cost model W n d fuel)

theorem priced_data (model : RationalCostModel) (W n d fuel : ℕ) :
    (priced model W n d fuel).1=GeneralPaperConstructedNatDivision.run n d fuel := data n d fuel

theorem priced_work (model : RationalCostModel) (W n d fuel : ℕ) (hd : 0<d) :
    (priced model W n d fuel).2≤1024*((GeneralPaperConstructedNatDivision.run n d fuel).depth+1)*
      (W+model.rat (operandWord n d)) := work model W n d fuel hd

end Blotto.GeneralPaperStreamingNatDivision
