import Blotto.GeneralPaperOneFieldOriginalStorage
import Blotto.GeneralPaperOriginalPreparationTime

/-! Common original-input space and description rates on the actual branch
output. Equal RAM masses include every resident key and returned root/work
fields. Unequal descriptions include both the sampler and prepared record.
Preparation phases retain the branch's existing address-capacity contract. -/
namespace Blotto.GeneralPaperOriginalStorageContract
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters
open GeneralPaperAllBranchBitDispatch (Prepared one)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (cellSize)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384

def NativeDescription (W : ℕ) (p : GeneralPaperNativeResourceDomain.Problem)
    (output : GeneralPaperClosedStrategyDriver.Prepared p.n) (bound : ℚ) : Prop :=
  let o := output.raw.strategies.original.reduced
  let k := output.raw.exponent
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  ∃ sampler : GeneralPaperStoredStrategySampler.Sampler p.n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
    output.sampler = some sampler ∧
    (GeneralPaperClosedDescriptionStorage.footprint W sampler : ℚ) ≤ bound ∧
    (GeneralPaperClosedDescriptionStorage.preparedFoot W output : ℚ) ≤ bound

inductive Contract (model : RationalCostModel) (K Cs ds Cd dd : ℕ) (p : Input) : Prepared p.n → Prop
  | oneField (hN : p.n = 1)
      (description : (GeneralPaperOneFieldOriginalStorage.description p : ℚ) ≤
        (Cd : ℚ) * descriptionScale p * (logarithm p : ℚ) ^ dd)
      (space : ∀ phase : GeneralPaperOneFieldOriginalStorage.Phase,
        (GeneralPaperOneFieldOriginalStorage.window model K p hN phase : ℚ) ≤
          (Cs : ℚ) * spaceScale p * (logarithm p : ℚ) ^ ds) :
      Contract model K Cs ds Cd dd p (one p hN).1
  | equal (hN : p.n ≠ 1) (hB : p.budget = 1)
      (output : Installed (GeneralPaperStoredSelectedPipeline.width model 1 K (equalInput model p)))
      (description : ∃ keys : Finset ℕ, (∀ key, output.memory key ≠ none → key ∈ keys) ∧
        (((∑ key ∈ keys, cellSize encode output.memory key) +
          GeneralPaperMeasuredEqualHeadlineRates.headBits model K (equalInput model p) output : ℕ) : ℚ) ≤
          (Cd : ℚ) * descriptionScale p * (logarithm p : ℚ) ^ dd)
      (space : ∀ phase : GeneralPaperMeasuredEqualStoragePhases.Phase model K (equalInput model p),
        ∃ keys : Finset ℕ,
          (∀ key, GeneralPaperMeasuredEqualStoragePhases.resident model 1 K (equalInput model p) phase key ≠ none → key ∈ keys) ∧
          (((∑ key ∈ keys, cellSize encode (GeneralPaperMeasuredEqualStoragePhases.resident model 1 K (equalInput model p) phase) key) +
            GeneralPaperMeasuredEqualDispatchStorage.window model K (equalInput model p) phase : ℕ) : ℚ) ≤
            (Cs : ℚ) * spaceScale p * (logarithm p : ℚ) ^ ds ∧
          (∑ key ∈ keys, cellSize encode (GeneralPaperMeasuredEqualStoragePhases.resident model 1 K (equalInput model p) phase) key) +
            GeneralPaperMeasuredEqualDispatchStorage.window model K (equalInput model p) phase <
              2 ^ GeneralPaperEqualInputDomain.word K (equalInput model p)) :
      Contract model K Cs ds Cd dd p (.equal _ output)
  | unequal (hN : p.n ≠ 1) (hStrict : p.budget < 1)
      (output : GeneralPaperClosedStrategyDriver.Prepared p.n)
      (description : NativeDescription (GeneralPaperMeasuredReferenceGrowth.word model K (unequalInput p hStrict))
        (unequalInput p hStrict) output ((Cd : ℚ) * descriptionScale p * (logarithm p : ℚ) ^ dd))
      (space : ∀ phase : GeneralPaperMeasuredUnequalStoragePhases.Phase model K (unequalInput p hStrict),
        (GeneralPaperMeasuredUnequalStoragePhases.window model K (unequalInput p hStrict) phase : ℚ) ≤
          (Cs : ℚ) * spaceScale p * (logarithm p : ℚ) ^ ds ∧
        GeneralPaperMeasuredUnequalStoragePhases.window model K (unequalInput p hStrict) phase <
          2 ^ GeneralPaperMeasuredReferenceGrowth.word model K (unequalInput p hStrict)) :
      Contract model K Cs ds Cd dd p (.unequal output)

end Blotto.GeneralPaperOriginalStorageContract
