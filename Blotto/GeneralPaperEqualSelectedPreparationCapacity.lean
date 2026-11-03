import Blotto.GeneralPaperEqualSelectedPreparationResources

/-! One global coefficient covers all earlier and newly added local-closure
phases at the actual constructed word. Full price/control counters and all
retained owners occur in the uniform growth calculation. -/
namespace Blotto.GeneralPaperEqualSelectedPreparationCapacity
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra GeneralPaperEqualSelectedPreparationResources
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem close_price_le_profile (model : RationalCostModel) (W n k b : ℕ) :
    GeneralPaperEqualSelectedClosureWork.price model W n k b ≤ GeneralPaperEqualSelectedClosureLifetime.profile model W n k b := by
  unfold GeneralPaperEqualSelectedClosureLifetime.profile GeneralPaperEqualSelectedClosureLifetime.componentProfile
  omega

theorem parent_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ), binaryWordWidth (parentCap model W K p) ≤
      C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  obtain ⟨Co,ho⟩ := GeneralPaperEqualDispatchCapacity.parent_cap_word_growth model hFast
  obtain ⟨Cc,hc⟩ := GeneralPaperEqualSelectedClosureRates.uniform_word_growth model hFast
  let L := GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure (model := model)
  have hL : ∀ a : GeneralPaperEqualInputInitializerCapacity.Parameters model, 1 ≤ L a :=
    GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hOld : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualDispatchLifetime.parentCap model a.reference a.coefficient a.input) L :=
    ⟨Co,fun a => ho a.input a.reference a.coefficient⟩
  have hClosure : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualSelectedClosureLifetime.profile model a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L :=
    ⟨Cc,fun a => hc a.input a.reference a.coefficient⟩
  have hPrice : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualSelectedClosureWork.price model a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L :=
    small_mono hClosure (fun a => close_price_le_profile model a.reference a.input.n a.input.k (rationalWordWidth a.input.budget))
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
  have ho := GeneralPaperEqualDispatchCapacity.profile_rate model hFast K
  have hc := GeneralPaperEqualSelectedClosureRates.profile_rate model hFast K
  have hp := parent_rate model hFast K
  dsimp only [profile]
  fun_prop

theorem uniform_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ), binaryWordWidth (profile model W K p) ≤
      C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  obtain ⟨Co,ho⟩ := GeneralPaperEqualDispatchCapacity.uniform_word_growth model hFast
  obtain ⟨Cc,hc⟩ := GeneralPaperEqualSelectedClosureRates.uniform_word_growth model hFast
  obtain ⟨Cp,hp⟩ := parent_word_growth model hFast
  let L := GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure (model := model)
  have hL : ∀ a : GeneralPaperEqualInputInitializerCapacity.Parameters model, 1 ≤ L a :=
    GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hOld : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualDispatchLifetime.profile model a.reference a.coefficient a.input) L :=
    ⟨Co,fun a => ho a.input a.reference a.coefficient⟩
  have hClosure : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualSelectedClosureLifetime.profile model a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L :=
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

end Blotto.GeneralPaperEqualSelectedPreparationCapacity
