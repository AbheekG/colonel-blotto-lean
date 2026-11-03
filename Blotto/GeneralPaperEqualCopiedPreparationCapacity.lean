import Blotto.GeneralPaperEqualCopiedPreparationResources

/-! Uniform sharp space and numerical capacity for every literal phase of
initialized selected preparation, closure and retained copy, including the
new parent and all actual saved prices. -/
namespace Blotto.GeneralPaperEqualCopiedPreparationCapacity
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra GeneralPaperEqualCopiedPreparationResources
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem parent_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ), binaryWordWidth (parentCap model W K p) ≤
      C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  obtain ⟨Co,ho⟩ := GeneralPaperEqualSelectedPreparationCapacity.parent_word_growth model hFast
  let L := GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure (model := model)
  have hL : ∀ a : GeneralPaperEqualInputInitializerCapacity.Parameters model, 1 ≤ L a :=
    GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hOld : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualSelectedPreparationResources.parentCap model a.reference a.coefficient a.input) L :=
    ⟨Co,fun a => ho a.input a.reference a.coefficient⟩
  obtain ⟨Cw,hw⟩ := GeneralPaperEqualCopyRates.uniform_word_growth model
  have hCopy : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualSelectedCopyWork.profile a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L :=
    ⟨Cw,fun a => hw a.input a.reference a.coefficient⟩
  have hAll : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      parentCap model a.reference a.coefficient a.input) L := by
    dsimp only [parentCap]
    fun_prop
  obtain ⟨C,hC⟩ := hAll
  exact ⟨C,fun p W K => hC ⟨p,W,K⟩⟩

theorem parent_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => parentProfile model (word K p) K p) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  obtain ⟨C,hC⟩ := parent_word_growth model hFast
  have hm : Tight (fun p : Input model => logarithm p + binaryWordWidth (word K p) + binaryWordWidth K) logarithm := by
    have hBase : Tight (logarithm (model := model)) logarithm := ⟨1,fun _ => by omega⟩
    fun_prop
  obtain ⟨D,hD⟩ := hm
  have hCap : Small (fun p : Input model => parentCap model (word K p) K p) logarithm := by
    refine ⟨C * D,fun p => ?_⟩
    exact (hC p _ K).trans ((Nat.mul_le_mul_left C (hD p)).trans_eq (by ring))
  dsimp only [parentProfile]
  fun_prop

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => profile model (word K p) K p) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have ho := GeneralPaperEqualSelectedPreparationCapacity.profile_rate model hFast K
  have hc := GeneralPaperEqualSelectedCopyLifetimeRates.profile_rate model K
  have hp := parent_rate model hFast K
  dsimp only [profile]
  fun_prop

theorem uniform_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ), binaryWordWidth (profile model W K p) ≤
      C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  obtain ⟨Co,ho⟩ := GeneralPaperEqualSelectedPreparationCapacity.uniform_word_growth model hFast
  obtain ⟨Cc,hc⟩ := GeneralPaperEqualSelectedCopyLifetimeRates.uniform_word_growth model
  obtain ⟨Cp,hp⟩ := parent_word_growth model hFast
  let L := GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure (model := model)
  have hL : ∀ a : GeneralPaperEqualInputInitializerCapacity.Parameters model, 1 ≤ L a :=
    GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hOld : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualSelectedPreparationResources.profile model a.reference a.coefficient a.input) L :=
    ⟨Co,fun a => ho a.input a.reference a.coefficient⟩
  have hClosure : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualSelectedCopyLifetime.profile a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L :=
    ⟨Cc,fun a => hc a.input a.reference a.coefficient⟩
  have hCap : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      parentCap model a.reference a.coefficient a.input) L := ⟨Cp,fun a => hp a.input a.reference a.coefficient⟩
  have hW : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => a.reference) L := by
    refine ⟨1,fun a => ?_⟩
    dsimp only [L,GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure]; omega
  have hAll : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      profile model a.reference a.coefficient a.input) L := by
    dsimp only [profile,parentProfile]
    fun_prop
  obtain ⟨C,hC⟩ := hAll
  exact ⟨C,fun p W K => hC ⟨p,W,K⟩⟩

theorem uniform_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : Input model, profile model (word K p) K p < 2 ^ word K p :=
  GeneralPaperSelfReferenceCapacity.uniform_capacity (profile model) logarithm logarithm_positive (uniform_word_growth model hFast)

end Blotto.GeneralPaperEqualCopiedPreparationCapacity
