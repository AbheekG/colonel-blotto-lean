import Blotto.GeneralPaperMeasuredEqualRepricing

/-! The actual smaller-charge initializer's saved result and nested source
caller controls. Child construction still uses the retained physical word. -/
namespace Blotto.GeneralPaperMeasuredEqualSourceParents
open GeneralPaperEqualInputDomain
open GeneralPaperEncodedScalarStorage (fields)
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

theorem returned_owner (model : RationalCostModel) (S A K : ℕ) (h : A ≤ S) (p : Input model) :
    GeneralPaperMixedInitializerControls.returnedOwner model S A K p ≤
      GeneralPaperEqualInputInitializerLifetime.returnedOwner model S K p + 2 * S := by
  have hm := GeneralPaperMeasuredInitializerMonotonicity.initialization model A S K h p
  have hf := GeneralPaperMixedPrimitiveStorage.fields_mono S
    [p.k, word K p, (GeneralPaperEqualInputInitialization.prepareReference model A K p).2]
    [p.k, word K p, (GeneralPaperEqualInputInitialization.prepareReference model S K p).2]
    (by simp [List.forall₂_cons, hm])
  dsimp only [GeneralPaperMixedInitializerControls.returnedOwner, GeneralPaperEqualInputInitializerLifetime.returnedOwner]
  rw [GeneralPaperEqualInputInitialization.initialized_exponent, GeneralPaperEqualInputInitialization.initialized_word,
    GeneralPaperEqualInputInitialization.initialized_exponent, GeneralPaperEqualInputInitialization.initialized_word]
  omega

def dispatchParent (model : RationalCostModel) (S A K : ℕ) (p : Input model) : ℕ :=
  let initial := GeneralPaperEqualInputInitialization.prepareReference model A K p
  let source := GeneralPaperEqualDispatchLifetime.sourceWork model S p
  fields S [p.n, p.k, S, K, word K p, initial.2, source, initial.2 + source] + 192 * S

theorem dispatch_parent_bound (model : RationalCostModel) (S A K : ℕ) (h : A ≤ S) (p : Input model) :
    dispatchParent model S A K p ≤ GeneralPaperEqualDispatchLifetime.parentWindow model S K p := by
  have hm := GeneralPaperMeasuredInitializerMonotonicity.initialization model A S K h p
  have hf := GeneralPaperMixedPrimitiveStorage.fields_mono S
    [p.n, p.k, S, K, word K p, (GeneralPaperEqualInputInitialization.prepareReference model A K p).2,
      GeneralPaperEqualDispatchLifetime.sourceWork model S p,
      (GeneralPaperEqualInputInitialization.prepareReference model A K p).2 + GeneralPaperEqualDispatchLifetime.sourceWork model S p]
    [p.n, p.k, S, K, word K p, (GeneralPaperEqualInputInitialization.prepareReference model S K p).2,
      GeneralPaperEqualDispatchLifetime.sourceWork model S p,
      (GeneralPaperEqualInputInitialization.prepareReference model S K p).2 + GeneralPaperEqualDispatchLifetime.sourceWork model S p]
    (by simp [List.forall₂_cons, hm])
  exact Nat.add_le_add_right hf _

def selectedParent (model : RationalCostModel) (S A K : ℕ) (p : Input model) : ℕ :=
  let initial := GeneralPaperEqualInputInitialization.prepareReference model A K p
  let source := GeneralPaperEqualDispatchLifetime.sourceWork model S p
  let closed := (GeneralPaperEqualSelectedPreparationResources.closure model S p).2
  fields S [p.n, p.k, S, K, initial.2, source, closed, initial.2 + source + closed] + 192 * S

theorem selected_parent_bound (model : RationalCostModel) (S A K : ℕ) (h : A ≤ S) (p : Input model) :
    selectedParent model S A K p ≤ GeneralPaperEqualSelectedPreparationResources.parentWindow model S K p := by
  have hm := GeneralPaperMeasuredInitializerMonotonicity.initialization model A S K h p
  have hf := GeneralPaperMixedPrimitiveStorage.fields_mono S
    [p.n, p.k, S, K, (GeneralPaperEqualInputInitialization.prepareReference model A K p).2,
      GeneralPaperEqualDispatchLifetime.sourceWork model S p, (GeneralPaperEqualSelectedPreparationResources.closure model S p).2,
      (GeneralPaperEqualInputInitialization.prepareReference model A K p).2 + GeneralPaperEqualDispatchLifetime.sourceWork model S p +
        (GeneralPaperEqualSelectedPreparationResources.closure model S p).2]
    [p.n, p.k, S, K, (GeneralPaperEqualInputInitialization.prepareReference model S K p).2,
      GeneralPaperEqualDispatchLifetime.sourceWork model S p, (GeneralPaperEqualSelectedPreparationResources.closure model S p).2,
      (GeneralPaperEqualInputInitialization.prepareReference model S K p).2 + GeneralPaperEqualDispatchLifetime.sourceWork model S p +
        (GeneralPaperEqualSelectedPreparationResources.closure model S p).2]
    (by simp [List.forall₂_cons, hm])
  exact Nat.add_le_add_right hf _

def callerWindow (model : RationalCostModel) (A K : ℕ) (p : Input model) : ℕ :=
  fields (word K p) (GeneralPaperMeasuredEqualRepricing.controls model A K p) + 224 * word K p

theorem caller_bound (model : RationalCostModel) (A K : ℕ) (p : Input model) (h : A ≤ word K p) :
    callerWindow model A K p ≤ GeneralPaperPreparationCallerControls.window model K p := by
  exact Nat.add_le_add_right (GeneralPaperMixedPrimitiveStorage.fields_mono _ _ _
    (GeneralPaperMeasuredEqualRepricing.controls_mono model A (word K p) K h p)) _

end Blotto.GeneralPaperMeasuredEqualSourceParents
