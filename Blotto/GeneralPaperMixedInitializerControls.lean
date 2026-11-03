import Blotto.GeneralPaperMixedReferenceWordStorage

/-! Actual A-priced initializer controls stored at physical reference S.
The parsed return retains two borrowed references to its original words. -/
namespace Blotto.GeneralPaperMixedInitializerControls
open GeneralPaperEqualInputDomain
open GeneralPaperEncodedScalarStorage (fields natBits)
open GeneralPaperEqualInputInitializerLifetime (valueWords budgetWords numeratorWords denominatorWords accuracySum builtReference)
open GeneralPaperEqualInputInitializerLifetime (value_data budget_data numerator_data denominator_data accuracy_data built_data controlCap controlProfile)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def values (model : RationalCostModel) (A K : ℕ) (p : Input model) : List ℕ :=
  let v := valueWords model A p
  let b := budgetWords model A p
  let num := numeratorWords model A p
  let den := denominatorWords model A p
  let e := accuracySum model A p
  let built := builtReference model A K p
  let prec := GeneralPaperBinaryAccuracy.prepare id A p.words
  let actual := GeneralPaperEqualInputInitialization.prepareReference model A K p
  [p.n, p.k, A, K, v.1, b.1, num.1, den.1, e.1, built.1, prec.2, v.2, b.2, num.2, den.2, e.2, built.2, actual.2, v.2+b.2, v.2+b.2+num.2, v.2+b.2+num.2+den.2, v.2+b.2+num.2+den.2+e.2, v.2+b.2+num.2+den.2+e.2+built.2, v.2+b.2+num.2+den.2+e.2+built.2+128*A+128, prec.2+(v.2+b.2+num.2+den.2+e.2+built.2+128*A+128), 64*A, 64, 128*A, 128]

def controls (model : RationalCostModel) (S A K : ℕ) (p : Input model) : ℕ :=
  fields S (values model A K p) + 256 * S

theorem values_bound (model : RationalCostModel) (S A K : ℕ) (h : A ≤ S) (p : Input model) :
    ∀ z ∈ values model A K p, z ≤ controlCap model S K p := by
  have hF := (GeneralPaperMeasuredInitializerMonotonicity.initialization model A S K h p).trans
    (GeneralPaperEqualInputInitialization.initialization_work model S K p)
  have hShape := GeneralPaperEqualInputInitializerLifetime.price_shape model A K p
  have hNum : p.words.numerator.width ≤ accuracySize p := by unfold accuracySize GeneralPaperBinaryAccuracyConstructionStorage.inputSize; omega
  have hDen : p.words.denominator.width ≤ accuracySize p := by unfold accuracySize GeneralPaperBinaryAccuracyConstructionStorage.inputSize; omega
  intro z hz
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at hz
  simp only [value_data, budget_data, numerator_data, denominator_data, accuracy_data, built_data] at hz
  unfold controlCap
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem controls_bound (model : RationalCostModel) (S A K : ℕ) (h : A ≤ S) (p : Input model) :
    controls model S A K p ≤ controlProfile model S K p := by
  have hf := GeneralPaperExpressionArrayReturns.fields_mono_cap S (controlCap model S K p)
    (values model A K p) (values_bound model S A K h p)
  change fields S _ ≤ 29 * (natBits (controlCap model S K p) + S) + 32 * S at hf
  unfold controls controlProfile
  omega

def returnedOwner (model : RationalCostModel) (S A K : ℕ) (p : Input model) : ℕ :=
  let actual := GeneralPaperEqualInputInitialization.prepareReference model A K p
  fields S [actual.1.1, actual.1.2, actual.2] + 64 * S + 2 * S

theorem returned_bound (model : RationalCostModel) (S A K : ℕ) (h : A ≤ S) (p : Input model) :
    returnedOwner model S A K p ≤ GeneralPaperEqualInputInitializerLifetime.returnedProfile model S K p + 2 * S := by
  have hk := GeneralPaperEqualInputInitialization.initialized_exponent model A K p
  have hw := GeneralPaperEqualInputInitialization.initialized_word model A K p
  have hF := (GeneralPaperMeasuredInitializerMonotonicity.initialization model A S K h p).trans
    (GeneralPaperEqualInputInitialization.initialization_work model S K p)
  have hf := GeneralPaperExpressionArrayReturns.fields_mono_cap S (controlCap model S K p)
    [(GeneralPaperEqualInputInitialization.prepareReference model A K p).1.1,
      (GeneralPaperEqualInputInitialization.prepareReference model A K p).1.2,
      (GeneralPaperEqualInputInitialization.prepareReference model A K p).2] (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · rw [hk]; unfold controlCap; omega
      · rw [hw]; unfold controlCap; omega
      · unfold controlCap; omega)
  change fields S _ ≤ 3 * (natBits (controlCap model S K p) + S) + 32 * S at hf
  dsimp only [returnedOwner, GeneralPaperEqualInputInitializerLifetime.returnedProfile]
  omega

end Blotto.GeneralPaperMixedInitializerControls
