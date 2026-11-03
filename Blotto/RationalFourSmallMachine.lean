import Blotto.WordMachineChoice
import Blotto.RationalMachineLaw
import Blotto.RationalFourReflectedProgram

/-! Native root choice and both atom-conditioning continuations under one
shared cap. The root calls neither branch's standalone sampler. -/

namespace Blotto.RationalFourInput

abbrev SmallState (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) :=
  BinaryState (CategoricalState (Fin 9)) (i.reflectedResourceSystem hcase).SamplingState

def smallWords (i : RationalFourInput) : ProbabilityWords :=
  ProbabilityWords.ofRat i.p ⟨le_of_lt i.p_pos, le_of_lt i.p_lt⟩

def uniformMachine (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (scalarBits : Fin K → Bool) : WordStateMachine (CategoricalState (Fin 9)) (Fin 4 → ℚ) :=
  (i.smallUniformLottery hcase).machine 0 K scalarBits

def reflectedMachine (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) : WordStateMachine (i.reflectedResourceSystem hcase).SamplingState (Fin 4 → ℚ) :=
  ((i.reflectedResourceSystem hcase).machine K outerBits scalarBits).mapped
    (RationalAffineAllocation.reflectAppend i.originalLengths).value

def smallMachine (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) : WordStateMachine (i.SmallState hcase) (Fin 4 → ℚ) :=
  binaryMachine i.smallWords (i.uniformMachine hcase K scalarBits) (i.reflectedMachine hcase K outerBits scalarBits)
    (i.smallUniformLottery hcase).start (i.reflectedResourceSystem hcase).samplingStart

def SmallPathContract (i : RationalFourInput) (x : Fin 4 → ℚ) : Prop :=
  FullBudget (i.B : ℝ) (fun j => (x j : ℝ)) ∧
    InBox ![(i.u : ℝ), (i.v : ℝ), (i.w : ℝ), (i.ell : ℝ)] (fun j => (x j : ℝ))

theorem smallMachine_rank (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) : (i.smallMachine hcase K outerBits scalarBits).rank .start ≤ 20 := by
  have hu := (i.smallUniformLottery hcase).machine_rank 0 K scalarBits
  have hr := (i.reflectedResourceSystem hcase).machine_rank K outerBits scalarBits
  change 1 + max (((i.smallUniformLottery hcase).machine 0 K scalarBits).rank (i.smallUniformLottery hcase).start)
    (((i.reflectedResourceSystem hcase).machine K outerBits scalarBits).rank (i.reflectedResourceSystem hcase).samplingStart) ≤ 20
  omega

theorem smallMachine_forLeaves (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) :
    ((i.smallMachine hcase K outerBits scalarBits).specification .start).decode.ForLeaves i.SmallPathContract := by
  rw [smallMachine, binaryMachine_specification]
  constructor
  · apply RationalSegmentLottery.machine_forLeaves
    intro slot
    exact ⟨(i.smallUniformLottery hcase).point_fullBudget K (i.smallUniformLottery_endpoints hcase) slot scalarBits,
      (i.smallUniformLottery hcase).point_inBox K _ (i.smallUniformLottery_box hcase) slot scalarBits⟩
  · rw [reflectedMachine, WordStateMachine.mapped_specification]
    apply WordChoiceTree.map_forLeaves
    apply WordChoiceTree.forLeaves_mono _ _ _ _ ((i.reflectedResourceSystem hcase).machine_forLeaves K outerBits scalarBits)
    intro x hx
    unfold SmallPathContract
    rw [RationalAffineAllocation.value_real]
    exact ⟨RationalAffineAllocation.reflectAppend_fullBudget i.originalLengths (i.reflection_budget_sum hcase) hx.1 hx.2,
      RationalAffineAllocation.reflectAppend_box i.originalLengths (by exact_mod_cast le_of_lt i.ell_pos) hx.2⟩

def smallFallback (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) : Fin 4 → ℚ :=
  (i.smallMachine hcase K outerBits scalarBits).chooseLeaf .start

theorem smallFallback_contract (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) : i.SmallPathContract (i.smallFallback hcase K outerBits scalarBits) :=
  (i.smallMachine hcase K outerBits scalarBits).chooseLeaf_forLeaves .start _ (i.smallMachine_forLeaves hcase K outerBits scalarBits)

def smallFixedSample (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : Fin 4 → ℚ :=
  (i.smallMachine hcase K outerBits scalarBits).output R .start (i.smallFallback hcase K outerBits scalarBits) choiceBits

theorem smallFixedSample_contract (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.SmallPathContract (i.smallFixedSample hcase K R outerBits scalarBits choiceBits) := by
  rw [smallFixedSample, WordStateMachine.output_refines]
  exact WordChoiceTree.output_forLeaves _ _ _ _ _ (i.smallMachine_forLeaves hcase K outerBits scalarBits)
    (i.smallFallback_contract hcase K outerBits scalarBits)

theorem smallMachine_mean (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (f : (Fin 4 → ℚ) → ℝ) :
    ((i.smallMachine hcase K outerBits scalarBits).specification .start).decode.mean f =
      (i.p : ℝ) * (((i.smallUniformLottery hcase).machine 0 K scalarBits).specification (i.smallUniformLottery hcase).start).decode.mean f +
        (1 - (i.p : ℝ)) * (((i.reflectedResourceSystem hcase).machine K outerBits scalarBits).specification
          (i.reflectedResourceSystem hcase).samplingStart).decode.mean
          (fun x => f ((RationalAffineAllocation.reflectAppend i.originalLengths).value x)) := by
  rw [smallMachine, binaryMachine_mean, reflectedMachine, WordStateMachine.mapped_mean]
  rw [smallWords, ProbabilityWords.ofRat_rational]
  rfl

end Blotto.RationalFourInput
