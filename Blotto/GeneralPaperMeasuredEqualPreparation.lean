import Blotto.GeneralPaperMeasuredUnequalPreparation
import Blotto.GeneralPaperAllBranchBitLaw

/-! Equal preparation retains the initializer's actual word and exponent.
Only equality transports use the canonical input views; later construction
and result attachment use the stored word, without another accuracy pass. -/
namespace Blotto.GeneralPaperMeasuredEqualPreparation
open GeneralPaperOriginalGameInput
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperAllBranchBitDispatch (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def prepare (model : RationalCostModel) (A K : ℕ) (p : Input) :
    (ℕ × Sampler (GeneralPaperEqualNativeSampler.rounded true model
      (GeneralPaperEqualInputDomain.word K (equalInput model p)) (equalInput model p).k
      p.values p.selector p.correct) (equalInput model p).k p.budget) × ℕ :=
  let initial := GeneralPaperOriginalMeasuredReference.prepare model A K p
  let actual := GeneralPaperEqualCopiedPipeline.dispatchCloseCopy model initial.1.2 initial.1.1.exponent
    p.values p.selector p.correct p.budget
  let source := GeneralPaperEqualSelectedPipeline.transport model initial.1.2 initial.1.1.exponent
    (GeneralPaperEqualInputDomain.word K (equalInput model p)) (equalInput model p).k
    p.values p.selector p.correct p.budget (GeneralPaperOriginalMeasuredReference.word model A K p)
    (GeneralPaperOriginalMeasuredReference.exponent model A K p) actual.1
  ((initial.1.2, source), initial.2 + actual.2)

theorem reference (model : RationalCostModel) (A K : ℕ) (p : Input) :
    (prepare model A K p).1.1 = GeneralPaperEqualInputDomain.word K (equalInput model p) :=
  GeneralPaperOriginalMeasuredReference.word model A K p

theorem source (model : RationalCostModel) (A K : ℕ) (p : Input) :
    (prepare model A K p).1.2 = (GeneralPaperEqualCopiedPipeline.run model A K (equalInput model p)).1 := rfl

theorem price (model : RationalCostModel) (A K : ℕ) (p : Input) :
    (prepare model A K p).2 = (GeneralPaperEqualCopiedPipeline.run model A K (equalInput model p)).2 := rfl

def width (model : RationalCostModel) (A K : ℕ) (p : Input) : ℕ := (prepare model A K p).1.2.address

def run (model : RationalCostModel) (A K : ℕ) (p : Input) : Option (Prepared p.n) × ℕ :=
  let prepared := prepare model A K p
  let W := prepared.1.1
  let source := prepared.1.2
  let actual := GeneralPaperStoredSelectedConstruction.run model W source
  match actual.1 with
  | none => (none, prepared.2 + actual.2 + 64 * (W + source.address + 1))
  | some output =>
    let finished := GeneralPaperSamplerRecordInstallation.attach W source.address prepared.2 output
    (some (.equal source.address finished), finished.work)

theorem pipeline (model : RationalCostModel) (A K : ℕ) (p : Input) :
    run model A K p =
      ((GeneralPaperStoredSelectedPipeline.run model A K (equalInput model p)).1.map
        (Prepared.equal (GeneralPaperStoredSelectedPipeline.width model A K (equalInput model p))),
       (GeneralPaperStoredSelectedPipeline.run model A K (equalInput model p)).2) := by
  simp only [run, reference, source, price, GeneralPaperStoredSelectedPipeline.run,
    GeneralPaperStoredSelectedPipeline.width]
  dsimp only [equalInput]
  split <;> simp_all only [Option.map_none, Option.map_some]

theorem work (model : RationalCostModel) (A K : ℕ) (p : Input) :
    (run model A K p).2 = (GeneralPaperStoredSelectedPipeline.run model A K (equalInput model p)).2 :=
  congrArg Prod.snd (pipeline model A K p)

theorem returns (model : RationalCostModel) (A K : ℕ) (p : Input) :
    ∃ output : GeneralPaperUnifiedDirectoryInstallation.Installed
        (GeneralPaperStoredSelectedPipeline.width model A K (equalInput model p)),
      (run model A K p).1 = some (.equal _ output) ∧
      (GeneralPaperStoredSelectedPipeline.run model A K (equalInput model p)).1 = some output := by
  obtain ⟨output, hReturn, _, _⟩ := GeneralPaperStoredSelectedPipeline.source model A K (equalInput model p)
  refine ⟨output, ?_, hReturn⟩
  rw [pipeline, hReturn]
  rfl

end Blotto.GeneralPaperMeasuredEqualPreparation
