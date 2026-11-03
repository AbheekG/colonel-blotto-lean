import Blotto.GeneralPaperEqualFirstInputPipeline

/-! Actual initialization at charge A followed by corrected preparation at
its constructed width S. Mixed-width observers retain original words and
all initializer return fields through the selected continuation. -/
namespace Blotto.GeneralPaperEqualFirstInputResources
open GeneralPaperEqualInputDomain
open GeneralPaperEncodedScalarStorage (fields natBits fields_bound)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def totalWork (model : RationalCostModel) (S A K : ℕ) (p : Input model) : ℕ :=
  (GeneralPaperEqualInputInitialization.prepareReference model A K p).2+
    GeneralPaperEqualFirstSelectedSpace.totalWork model S p

def parentCap (model : RationalCostModel) (S K : ℕ) (p : Input model) : ℕ :=
  p.n+p.k+S+K+GeneralPaperEqualFirstInputPipeline.price model S K p+1

def parentWindow (model : RationalCostModel) (S A K : ℕ) (p : Input model) : ℕ :=
  fields S [p.n,p.k,S,A,K,(GeneralPaperEqualInputInitialization.prepareReference model A K p).2,
    GeneralPaperEqualFirstSelectedSpace.totalWork model S p,totalWork model S A K p]+192*S

def parentProfile (model : RationalCostModel) (S K : ℕ) (p : Input model) : ℕ :=
  8*(natBits (parentCap model S K p)+S)+224*S

theorem parent_bound (model : RationalCostModel) (S A K : ℕ) (p : Input model) (hAS : A ≤ S) :
    parentWindow model S A K p ≤ parentProfile model S K p := by
  have hi := (GeneralPaperMeasuredInitializerMonotonicity.initialization model A S K hAS p).trans
    (GeneralPaperEqualInputInitialization.initialization_work model S K p)
  have hs := GeneralPaperEqualFirstSelectedPreparation.work model S S p.k p.values p.selector p.correct p.budget
  change GeneralPaperEqualFirstSelectedSpace.totalWork model S p ≤ _ at hs
  have hf := fields_bound S (natBits (parentCap model S K p))
    [p.n,p.k,S,A,K,(GeneralPaperEqualInputInitialization.prepareReference model A K p).2,
      GeneralPaperEqualFirstSelectedSpace.totalWork model S p,totalWork model S A K p] (by
        intro z hz
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals dsimp only [parentCap,GeneralPaperEqualFirstInputPipeline.price,totalWork]; omega)
  change fields S _ ≤ 8*(natBits (parentCap model S K p)+S)+32*S at hf
  dsimp only [parentWindow,parentProfile]
  omega

noncomputable def profile (model : RationalCostModel) (S K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperMixedInitializerPhases.profile model S K p+
    GeneralPaperEqualInputInitializerLifetime.returnedProfile model S K p+2*S+
    GeneralPaperEqualFirstSelectedSpace.profile model S p+parentProfile model S K p

def Phase (model : RationalCostModel) (S : ℕ) (p : Input model) :=
  Sum (GeneralPaperEqualInputInitializerLifetime.Phase p.n) (GeneralPaperEqualFirstSelectedSpace.Phase model S p)

noncomputable def window (model : RationalCostModel) (S A K : ℕ) (p : Input model) : Phase model S p → ℕ
  | .inl phase => GeneralPaperMixedInitializerPhases.window model S A K p phase+parentWindow model S A K p
  | .inr phase => GeneralPaperMixedInitializerControls.returnedOwner model S A K p+
      GeneralPaperEqualFirstSelectedSpace.window model S p phase+parentWindow model S A K p

theorem all_phases (model : RationalCostModel) (S A K : ℕ) (p : Input model)
    (hS : 1 ≤ S) (hIndex : binaryWordWidth (p.n+1) ≤ S) (hAS : A ≤ S) (phase : Phase model S p) :
    window model S A K p phase ≤ profile model S K p := by
  have hp := parent_bound model S A K p hAS
  cases phase with
  | inl phase =>
    have hi := GeneralPaperMixedInitializerPhases.all_phases model S A K hAS p phase
    dsimp only [window,profile]; omega
  | inr phase =>
    have hr := GeneralPaperMixedInitializerControls.returned_bound model S A K hAS p
    have hs := GeneralPaperEqualFirstSelectedSpace.all_phases model S p hS hIndex phase
    dsimp only [window,profile]; omega

theorem actual_work (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (GeneralPaperEqualFirstInputPipeline.run model A K p).2 = totalWork model (word K p) A K p :=
  GeneralPaperEqualFirstInputPipeline.work model A K p

theorem actual_return (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (GeneralPaperEqualFirstInputPipeline.run model A K p).1 =
      (GeneralPaperEqualFirstSelectedSpace.closure model (word K p) p).1 := by
  rw [GeneralPaperEqualFirstInputPipeline.data]
  exact GeneralPaperEqualFirstSelectedSpace.actual_return model _ p

end Blotto.GeneralPaperEqualFirstInputResources
