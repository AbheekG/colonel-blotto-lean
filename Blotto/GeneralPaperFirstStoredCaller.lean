import Blotto.GeneralPaperFirstStoredResident

/-! Complete enclosing caller owners, saved actual prices and final result
attachment for direct corrected installation. Original input and the one
selected source coexist; constructor writes produce the compact final RAM. -/
namespace Blotto.GeneralPaperFirstStoredCaller
open GeneralPaperEqualInputDomain
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEncodedScalarStorage (fields natBits fields_bound)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def source (model : RationalCostModel) (K : ℕ) (p : Input model) :=
  GeneralPaperEqualFirstInputPipeline.run model 1 K p

def built (model : RationalCostModel) (K : ℕ) (p : Input model) :=
  GeneralPaperStoredSelectedConstruction.run model (word K p) (source model K p).1

def sourceWindow (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualInputInitializerLifetime.inputOwner model (word K p) p+
    GeneralPaperPreparationSourceOwners.owner (word K p) (source model K p).1

noncomputable def sourceProfile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  2*GeneralPaperEqualFirstInputResources.profile model (word K p) K p+
    natBits (2*GeneralPaperEqualBitDrawRates.log p.n p.k (rationalWordWidth p.budget)+1)+97*word K p

theorem source_bound (model : RationalCostModel) (K : ℕ) (p : Input model) :
    sourceWindow model K p ≤ sourceProfile model K p := by
  let S := word K p
  have hInput := GeneralPaperEqualInputInitializerLifetime.input_bound model S p
  have hBranch := GeneralPaperEqualFirstSelectedDescription.branch_bound model S S p.k p.values p.selector p.correct p.budget
    (source model K p).1.branch
  have hHeader := GeneralPaperEqualSelectedCopyLifetime.header_bound S (source model K p).1.address _
    (GeneralPaperEqualSelectedSampler.address_bound (source model K p).1)
  have hInputCap : GeneralPaperEqualInputInitializerLifetime.inputProfile model S p ≤
      GeneralPaperEqualFirstInputResources.profile model S K p := by
    dsimp only [GeneralPaperEqualFirstInputResources.profile,GeneralPaperMixedInitializerPhases.profile,
      GeneralPaperEqualInputInitializerLifetime.profile]
    omega
  have hBranchCap : GeneralPaperEqualSelectedBranchOwner.profile S p.n (p.k+1) (rationalWordWidth p.budget) ≤
      GeneralPaperEqualFirstInputResources.profile model S K p := by
    dsimp only [GeneralPaperEqualFirstInputResources.profile,GeneralPaperEqualFirstSelectedSpace.profile,
      GeneralPaperEqualFirstSelectedDescription.closureProfile]
    omega
  dsimp only [sourceWindow,sourceProfile,GeneralPaperPreparationSourceOwners.owner]
  change _ ≤ 2*GeneralPaperEqualFirstInputResources.profile model S K p+_+97*S
  dsimp only [S] at *
  omega

def controls (model : RationalCostModel) (K : ℕ) (p : Input model) : List ℕ :=
  let S := word K p
  let prepared := source model K p
  let actual := built model K p
  [S,K,p.n,p.k,prepared.1.address,(GeneralPaperEqualInputInitialization.prepareReference model 1 K p).2,
    prepared.2,actual.2,prepared.2+actual.2,(GeneralPaperFirstStoredPipeline.run model 1 K p).2]

def cap (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  word K p+K+p.n+p.k+(source model K p).1.address+GeneralPaperFirstStoredWork.price model K p+1

theorem fields_bounded (model : RationalCostModel) (K : ℕ) (p : Input model) (hS : 1 ≤ word K p) :
    ∀ z ∈ controls model K p,z ≤ cap model K p := by
  have hShape := GeneralPaperFirstStoredWork.work_identity model 1 K p
  have hWhole := GeneralPaperFirstStoredWork.actual_work model K p hS
  have hInit := GeneralPaperEqualFirstInputPipeline.work model 1 K p
  intro z hz
  simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
  unfold cap
  dsimp only [source,built] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

def controlWindow (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  fields (word K p) (controls model K p)+224*word K p

def controlProfile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  10*(natBits (cap model K p)+word K p)+256*word K p

theorem controls_bound (model : RationalCostModel) (K : ℕ) (p : Input model) (hS : 1 ≤ word K p) :
    controlWindow model K p ≤ controlProfile model K p := by
  have h := fields_bound (word K p) (natBits (cap model K p)) (controls model K p)
    (fun z hz => Nat.add_le_add_left (binaryWordWidth_mono (fields_bounded model K p hS z hz)) 1)
  change fields (word K p) _ ≤ 10*(natBits (cap model K p)+word K p)+32*word K p at h
  dsimp only [controlWindow,controlProfile]
  omega

def resultWindow (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  (built model K p).1.elim 0 (fun output => GeneralPaperResultAttachmentLifetime.window
    (word K p) (source model K p).1.address (source model K p).2 output)

def resultProfile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperMeasuredPlanLifetimeAlgebra.unit model (word K p) (source model K p).1.address
    (GeneralPaperFirstStoredWork.price model K p)

theorem result_bound (model : RationalCostModel) (K : ℕ) (p : Input model) (hS : 1 ≤ word K p) :
    resultWindow model K p ≤ resultProfile model K p := by
  obtain ⟨inner,hBuilt,hPrice,_⟩ := GeneralPaperFirstStoredConstruction.source model (word K p) (word K p)
    p.k p.values p.selector p.correct p.budget (source model K p).1
  have hShape := GeneralPaperFirstStoredWork.work_identity model 1 K p
  have hWhole := GeneralPaperFirstStoredWork.actual_work model K p hS
  have hAttach : (GeneralPaperSamplerRecordInstallation.attach (word K p) (source model K p).1.address
      (source model K p).2 inner).work ≤ GeneralPaperFirstStoredWork.price model K p := by
    change (source model K p).2+inner.work+64*(word K p+(source model K p).1.address+1) ≤ _
    rw [hPrice]
    exact hShape.symm ▸ hWhole
  have h := GeneralPaperResultAttachmentLifetime.window_bound model (word K p) (source model K p).1.address
    (source model K p).2 (GeneralPaperFirstStoredWork.price model K p) inner hAttach
  dsimp only [resultWindow,built]
  rw [hBuilt]
  exact h

def window (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  sourceWindow model K p+controlWindow model K p+resultWindow model K p+
    GeneralPaperSelectedOuterInputLifetime.combinedWindow model (word K p) (source model K p).1

noncomputable def profile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  sourceProfile model K p+controlProfile model K p+resultProfile model K p+
    GeneralPaperSelectedOuterInputLifetime.combinedBound model (word K p) (source model K p).1

theorem all_components (model : RationalCostModel) (K : ℕ) (p : Input model) (hS : 1 ≤ word K p) :
    window model K p ≤ profile model K p :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (source_bound model K p)
    (controls_bound model K p hS)) (result_bound model K p hS))
    (GeneralPaperFirstStoredWindows.combined model (word K p) (word K p) p.k p.values p.selector p.correct p.budget (source model K p).1)

end Blotto.GeneralPaperFirstStoredCaller
