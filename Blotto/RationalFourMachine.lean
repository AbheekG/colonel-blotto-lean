import Blotto.RationalFourSmallProgram
import Blotto.RationalFourGluingProgram
import Blotto.WordMachineEmbedding
import Blotto.WordMachineRuntimeFields

/-! One native controller interface for both ordered four-variable cases.
The deterministic rational comparison selects its initial state, then every
adaptive coin request uses the same caller-supplied cap. -/

namespace Blotto

inductive FourSamplingState (i : RationalFourInput) where
  | gluing (hcase : (1 - i.p) * i.ell ≤ i.w) (state : CategoricalState (Fin 81))
  | small (hcase : i.w < (1 - i.p) * i.ell) (state : i.SmallState hcase)

namespace RationalFourInput

def gluingMachine (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (K : ℕ)
    (scalarBits : Fin K → Bool) : WordStateMachine (CategoricalState (Fin 81)) (Fin 4 → ℚ) :=
  (i.gluingDescriptor hcase).machine 0 K scalarBits

def transition (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    FourSamplingState i → WordTransition (FourSamplingState i) (Fin 4 → ℚ)
  | .gluing hcase s => (i.gluingMachine hcase K scalarBits).step s |>.mapState (.gluing hcase)
  | .small hcase s => (i.smallMachine hcase K outerBits scalarBits).step s |>.mapState (.small hcase)

def rank (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) : FourSamplingState i → ℕ
  | .gluing hcase s => (i.gluingMachine hcase K scalarBits).rank s
  | .small hcase s => (i.smallMachine hcase K outerBits scalarBits).rank s

def machineReference (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    WordStateMachine (FourSamplingState i) (Fin 4 → ℚ) where
  step := i.transition K outerBits scalarBits
  rank := i.rank K outerBits scalarBits
  progress := by
    intro state
    cases state with
    | gluing hcase s =>
      apply WordTransition.mapState_progress
      exact (i.gluingMachine hcase K scalarBits).progress s
    | small hcase s =>
      apply WordTransition.mapState_progress
      exact (i.smallMachine hcase K outerBits scalarBits).progress s

def machine (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    WordStateMachine (FourSamplingState i) (Fin 4 → ℚ) :=
  if hcase : (1 - i.p) * i.ell ≤ i.w then
    let inner := i.gluingMachine hcase K scalarBits
    { step := fun
        | .gluing _ state => (inner.step state).mapState (.gluing hcase)
        | .small hBad _ => False.elim ((not_lt_of_ge hcase) hBad)
      rank := fun
        | .gluing _ state => inner.rank state
        | .small hBad _ => False.elim ((not_lt_of_ge hcase) hBad)
      progress := by
        intro cursor
        cases cursor with
        | gluing h state =>
          apply WordTransition.mapState_progress
          exact inner.progress state
        | small hBad state => exact False.elim ((not_lt_of_ge hcase) hBad) }
  else
    let hsmall := lt_of_not_ge hcase
    let inner := i.smallMachine hsmall K outerBits scalarBits
    { step := fun
        | .gluing hBad _ => False.elim (hcase hBad)
        | .small _ state => (inner.step state).mapState (.small hsmall)
      rank := fun
        | .gluing hBad _ => False.elim (hcase hBad)
        | .small _ state => inner.rank state
      progress := by
        intro cursor
        cases cursor with
        | gluing hBad state => exact False.elim (hcase hBad)
        | small h state =>
          apply WordTransition.mapState_progress
          exact inner.progress state }

theorem machine_refines (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    i.machine K outerBits scalarBits = i.machineReference K outerBits scalarBits := by
  unfold machine
  split_ifs with hcase
  · apply WordStateMachine.eq_of_runtime_fields
    · funext cursor
      cases cursor with
      | gluing h state => rfl
      | small hBad state => exact False.elim ((not_lt_of_ge hcase) hBad)
    · funext cursor
      cases cursor with
      | gluing h state => rfl
      | small hBad state => exact False.elim ((not_lt_of_ge hcase) hBad)
  · apply WordStateMachine.eq_of_runtime_fields
    · funext cursor
      cases cursor with
      | gluing hBad state => exact False.elim (hcase hBad)
      | small h state => rfl
    · funext cursor
      cases cursor with
      | gluing hBad state => exact False.elim (hcase hBad)
      | small h state => rfl

def start (i : RationalFourInput) (K : ℕ) (_outerBits _scalarBits : Fin K → Bool) : FourSamplingState i :=
  if hcase : (1 - i.p) * i.ell ≤ i.w then .gluing hcase (i.gluingDescriptor hcase).start
  else .small (lt_of_not_ge hcase) .start

theorem machine_rank (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    (i.machine K outerBits scalarBits).rank (i.start K outerBits scalarBits) ≤ 80 := by
  rw [machine_refines]
  unfold start
  split_ifs with hcase
  · exact le_of_eq ((i.gluingDescriptor hcase).machine_rank 0 K scalarBits)
  · exact (i.smallMachine_rank _ K outerBits scalarBits).trans (by decide : 20 ≤ 80)

theorem gluing_specification (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (hcase : (1 - i.p) * i.ell ≤ i.w) (s : CategoricalState (Fin 81)) :
    (i.machine K outerBits scalarBits).specification (.gluing hcase s) = (i.gluingMachine hcase K scalarBits).specification s := by
  rw [machine_refines]
  apply WordStateMachine.embedding_specification
  intro state
  rfl

theorem small_specification (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (hcase : i.w < (1 - i.p) * i.ell) (s : i.SmallState hcase) :
    (i.machine K outerBits scalarBits).specification (.small hcase s) = (i.smallMachine hcase K outerBits scalarBits).specification s := by
  rw [machine_refines]
  apply WordStateMachine.embedding_specification
  intro state
  rfl

theorem machine_forLeaves (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    ((i.machine K outerBits scalarBits).specification (i.start K outerBits scalarBits)).decode.ForLeaves
      (fun x => FullBudget (i.B : ℝ) (fun j => (x j : ℝ))) := by
  unfold start
  split_ifs with hcase
  · rw [i.gluing_specification]
    apply RationalSegmentLottery.machine_forLeaves
    intro slot
    exact (i.gluingDescriptor hcase).point_fullBudget K (i.gluingDescriptor_endpoints hcase) slot scalarBits
  · rw [i.small_specification]
    exact WordChoiceTree.forLeaves_mono _ _ _ (fun _ h => h.1) (i.smallMachine_forLeaves _ K outerBits scalarBits)

def fallback (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) : Fin 4 → ℚ :=
  (i.machine K outerBits scalarBits).chooseLeaf (i.start K outerBits scalarBits)

theorem fallback_fullBudget (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.fallback K outerBits scalarBits j : ℝ)) :=
  (i.machine K outerBits scalarBits).chooseLeaf_forLeaves (i.start K outerBits scalarBits) _ (i.machine_forLeaves K outerBits scalarBits)

def fixedSample (i : RationalFourInput) (K R : ℕ) (outerBits scalarBits : Fin K → Bool)
    (choiceBits : Fin R → Bool) : Fin 4 → ℚ :=
  (i.machine K outerBits scalarBits).output R (i.start K outerBits scalarBits) (i.fallback K outerBits scalarBits) choiceBits

theorem fixedSample_fullBudget (i : RationalFourInput) (K R : ℕ) (outerBits scalarBits : Fin K → Bool)
    (choiceBits : Fin R → Bool) : FullBudget (i.B : ℝ) (fun j => (i.fixedSample K R outerBits scalarBits choiceBits j : ℝ)) := by
  rw [fixedSample, WordStateMachine.output_refines]
  exact WordChoiceTree.output_forLeaves _ _ _ _ _ (i.machine_forLeaves K outerBits scalarBits) (i.fallback_fullBudget K outerBits scalarBits)

end RationalFourInput
end Blotto
