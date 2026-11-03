import Blotto.PlayerSpecificFiniteSamplerMeasuredSourceJoin
import Blotto.PlayerSpecificFiniteAccuracySourceCost

/-! An accepted public preparation pays for recognition, initial arrays,
minimum computation, three actual precision calls and the retained
accuracy/budget metadata. Its return is the native prepared sampler. -/
namespace Blotto.PlayerSpecificFiniteSamplerMeasuredPreparationCost
open PlayerSpecificRationalTrace PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

def frameWidth {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ)
    (base : PlayerSpecificInitialMinimumExecution.Prepared N)
    (accuracy : PlayerSpecificFiniteAccuracy.Parameters) : ℕ :=
  rationalWordWidth i.budget+rationalWordWidth epsilon+
    binaryWordWidth N+binaryWordWidth base.minimum.exponent+
    binaryWordWidth accuracy.scalarBits+binaryWordWidth accuracy.coinBits+
    binaryWordWidth accuracy.outputBits+
    binaryWordWidth (PlayerSpecificAlgebraicFiniteDraw.bitCount N
      accuracy.coinBits accuracy.scalarBits)+16

def acceptedWork {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ)
    (p : Prepared N) : ℕ :=
  PlayerSpecificInitialMinimumCost.totalBound N (PlayerSpecificInitialPositivePrecision.inputSize i)+
  PlayerSpecificFiniteAccuracySourceCost.work N p.base.minimum.exponent epsilon+
  27*RationalCostModel.schoolbook.rat (frameWidth i epsilon p.base p.accuracy)+2

theorem frame_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ)
    (base : PlayerSpecificInitialMinimumExecution.Prepared N)
    (accuracy : PlayerSpecificFiniteAccuracy.Parameters) :
    price RationalCostModel.schoolbook
      (PlayerSpecificFiniteSamplerMeasuredExecution.frame i epsilon base accuracy)≤
      27*RationalCostModel.schoolbook.rat (frameWidth i epsilon base accuracy) := by
  let model:=RationalCostModel.schoolbook
  let W:=frameWidth i epsilon base accuracy
  let R:=model.rat W
  let words:List ℕ:=[N,base.minimum.exponent,accuracy.scalarBits,
    accuracy.coinBits,accuracy.outputBits,
    PlayerSpecificAlgebraicFiniteDraw.bitCount N accuracy.coinBits accuracy.scalarBits]
  have hW : 1≤W := by dsimp [W,frameWidth]; omega
  have hwords : ∀ word∈words,binaryWordWidth word≤W := by
    intro word hw
    simp only [words,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with hw|hw|hw|hw|hw|hw <;> rw [hw] <;> dsimp [W,frameWidth] <;> omega
  have hctrl:=PlayerSpecificAlgebraicCallerFrame.controls_cost model words W hwords hW
  have hctrl' : price model (words.map Event.control)≤18*R := by
    have hl : words.length=6 := rfl
    rw [hl] at hctrl
    norm_num at hctrl
    exact hctrl
  have hcopyFits : Fits W (copyRow [i.budget,epsilon]) := by
    intro e he
    simp only [copyRow,List.map_cons,List.map_nil,List.mem_cons,
      List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl
    · exact (control_width 2).trans (by dsimp [W,frameWidth]; omega)
    · dsimp only [Event.Fits,W,frameWidth]
      omega
    · dsimp only [Event.Fits,W,frameWidth]
      omega
  have hcopy:=price_bound model W hW (copyRow [i.budget,epsilon]) hcopyFits
  have hcopy' : price model (copyRow [i.budget,epsilon])≤9*R := by
    simpa only [copyRow,List.length_cons,List.length_map,List.length_nil,
      Nat.reduceAdd,Nat.reduceMul] using hcopy
  change price model (copyRow [i.budget,epsilon]++words.map Event.control)≤_
  rw [price_append]
  change _≤27*R
  omega

theorem accepted_cost {N : ℕ} (i : RationalPlayerSpecificInput N)
    (epsilon : ℚ) (he : 0<epsilon) (p : Prepared N)
    (hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p) :
    (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).2≤
      acceptedWork i epsilon p := by
  have hpublic : PlayerSpecificFiniteSampler.prepare i epsilon=some p := by
    rw [←PlayerSpecificFiniteSamplerMeasuredExecution.prepare_value i epsilon he]
    exact hp
  obtain ⟨base,hb,hpbase⟩:=PlayerSpecificFiniteSampler.selected i epsilon p hpublic
  let model:=RationalCostModel.schoolbook
  let initial:=PlayerSpecificInitialMinimumExecution.run i
  let accuracy:=PlayerSpecificFiniteAccuracyExecution.run N base.minimum.exponent epsilon
  have hi : initial.1=some base := hb
  have ha : accuracy.1=p.accuracy := by
    rw [PlayerSpecificFiniteAccuracyExecution.value N base.minimum.exponent epsilon he]
    rw [hpbase]
    rfl
  have hsource:=PlayerSpecificInitialMinimumCost.source_cost i
  have haccuracy:=PlayerSpecificFiniteAccuracySourceCost.cost N base.minimum.exponent epsilon he
  have hframe:=frame_cost i epsilon base accuracy.1
  have hframe' : price model
      (PlayerSpecificFiniteSamplerMeasuredExecution.frame i epsilon base accuracy.1)≤
      27*model.rat (frameWidth i epsilon p.base p.accuracy) := by
    rw [ha,hpbase] at hframe ⊢
    exact hframe
  have hcontrol : price model [.control 1]=2 := by rfl
  simp only [PlayerSpecificFiniteSamplerMeasuredExecution.prepare,hb]
  change initial.2+accuracy.2+
    price model (PlayerSpecificFiniteSamplerMeasuredExecution.frame i epsilon base accuracy.1)+
      price model [.control 1]≤_
  have hsum:=Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add hsource haccuracy) hframe') (le_of_eq hcontrol)
  simpa only [acceptedWork,hpbase,initial,accuracy,model,
    PlayerSpecificFiniteSampler.ofBase,
    PlayerSpecificAlgebraicInitialVectorBudget.inputSize,
    PlayerSpecificInitialPositivePrecision.inputSize] using hsum

end Blotto.PlayerSpecificFiniteSamplerMeasuredPreparationCost
