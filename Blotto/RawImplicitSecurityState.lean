import Blotto.GenericImplicitBlockHistory
import Blotto.ProductRawSecurityState

/-! Raw rational observations update actual compact blocks directly. Ordered
bid-code assumptions refer to the native trainer bid decoder; no raw-history
encoding or row enumeration is used. Exact current-field and target-law
refinements preserve all labelled duplicate bids. -/

namespace Blotto
open scoped BigOperators Classical
namespace ProductSecurityTrainer
open ImplicitLeafCounts

def bidDecoder {m : ℕ} {sizes : Fin m → ℕ} (bids : (field : Fin m) → Fin (sizes field) → ℚ)
    (field : Fin m) (code : ℕ) : ℚ := if h : code < sizes field then bids field ⟨code, h⟩ else 0

theorem bidDecoder_valid {m : ℕ} {sizes : Fin m → ℕ} (bids : (field : Fin m) → Fin (sizes field) → ℚ)
    (field : Fin m) (code : Fin (sizes field)) : bidDecoder bids field code.val = bids field code := by
  simp only [bidDecoder, code.isLt, dite_true]

structure ImplicitCodeConfig {m : ℕ} (c : ProductSecurityTrainer m) where
  capsA : Fin m → ℕ
  capsB : Fin m → ℕ
  sizesA : c.sizesA = fun field => capsA field + 1
  sizesB : c.sizesB = fun field => capsB field + 1
  orderedA : ∀ field, MonotoneResourceCuts.MonotoneDecode (capsA field) (bidDecoder c.bidsA field)
  orderedB : ∀ field, MonotoneResourceCuts.MonotoneDecode (capsB field) (bidDecoder c.bidsB field)
  zeroA : ∀ field, bidDecoder c.bidsA field 0 = 0
  zeroB : ∀ field, bidDecoder c.bidsB field 0 = 0

def compactBlocksA {m : ℕ} (c : ProductSecurityTrainer m) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation m)) : Fin m → List Block :=
  genericBlocks cfg.capsA (bidDecoder c.bidsA) rawSelected (fun _ x => x.2.1 x.2.2) c.eta c.theta history

def compactBlocksB {m : ℕ} (c : ProductSecurityTrainer m) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation m)) : Fin m → List Block :=
  genericBlocks cfg.capsB (bidDecoder c.bidsB) rawSelected (fun _ x => x.1 x.2.2) c.eta c.theta history

theorem genericFieldsA_refines {m : ℕ} (c : ProductSecurityTrainer m) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation m)) : ∀ field (code : Fin (cfg.capsA field + 1)),
    genericFields cfg.capsA (bidDecoder c.bidsA) rawSelected (fun _ x => x.2.1 x.2.2) c.eta c.theta history field code =
      c.rawFieldsA history field (code.cast (congrFun cfg.sizesA field).symm) := by
  induction history with
  | nil => intro field code; rfl
  | cons x history ih =>
    intro field code
    by_cases he : field = x.2.2
    · subst field
      simp only [genericFields, rawFieldsA, rawSelected, Function.update_self]
      rw [ih]
      have hDecode : bidDecoder c.bidsA x.2.2 code.val = c.bidsA x.2.2 (code.cast (congrFun cfg.sizesA x.2.2).symm) :=
        bidDecoder_valid c.bidsA _ (code.cast _)
      unfold genericLoss rawLossA
      simp only [rawSelected]
      rw [hDecode]
    · simp only [genericFields, rawFieldsA, rawSelected, Function.update_of_ne he]
      exact ih field code

theorem genericFieldsB_refines {m : ℕ} (c : ProductSecurityTrainer m) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation m)) : ∀ field (code : Fin (cfg.capsB field + 1)),
    genericFields cfg.capsB (bidDecoder c.bidsB) rawSelected (fun _ x => x.1 x.2.2) c.eta c.theta history field code =
      c.rawFieldsB history field (code.cast (congrFun cfg.sizesB field).symm) := by
  induction history with
  | nil => intro field code; rfl
  | cons x history ih =>
    intro field code
    by_cases he : field = x.2.2
    · subst field
      simp only [genericFields, rawFieldsB, rawSelected, Function.update_self]
      rw [ih]
      have hDecode : bidDecoder c.bidsB x.2.2 code.val = c.bidsB x.2.2 (code.cast (congrFun cfg.sizesB x.2.2).symm) :=
        bidDecoder_valid c.bidsB _ (code.cast _)
      unfold genericLoss rawLossB
      simp only [rawSelected]
      rw [hDecode]
    · simp only [genericFields, rawFieldsB, rawSelected, Function.update_of_ne he]
      exact ih field code

theorem compactBlocksA_refines {m : ℕ} (c : ProductSecurityTrainer m) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation m)) (field : Fin m) (code : Fin (cfg.capsA field + 1)) :
    labelMass (c.compactBlocksA cfg history field) code.val = c.rawFieldsA history field (code.cast (congrFun cfg.sizesA field).symm) :=
  (genericBlocks_refines cfg.capsA (bidDecoder c.bidsA) cfg.orderedA rawSelected _ c.eta c.theta history field code).trans
    (c.genericFieldsA_refines cfg history field code)

theorem compactBlocksB_refines {m : ℕ} (c : ProductSecurityTrainer m) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation m)) (field : Fin m) (code : Fin (cfg.capsB field + 1)) :
    labelMass (c.compactBlocksB cfg history field) code.val = c.rawFieldsB history field (code.cast (congrFun cfg.sizesB field).symm) :=
  (genericBlocks_refines cfg.capsB (bidDecoder c.bidsB) cfg.orderedB rawSelected _ c.eta c.theta history field code).trans
    (c.genericFieldsB_refines cfg history field code)

def compactLeafA {m : ℕ} (c : ProductSecurityTrainer m) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation m)) (field : Fin m) : ProposalLeaf :=
  genericLeaf cfg.capsA (bidDecoder c.bidsA) cfg.orderedA rawSelected (fun _ x => x.2.1 x.2.2)
    c.eta c.theta c.eta_unit c.theta_unit history field

def compactLeafB {m : ℕ} (c : ProductSecurityTrainer m) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation m)) (field : Fin m) : ProposalLeaf :=
  genericLeaf cfg.capsB (bidDecoder c.bidsB) cfg.orderedB rawSelected (fun _ x => x.1 x.2.2)
    c.eta c.theta c.eta_unit c.theta_unit history field

theorem budgetA_nonnegative {m : ℕ} (c : ProductSecurityTrainer m) : 0 ≤ c.budgetA :=
  (Finset.sum_nonneg (fun field _ => c.bidsA_nonnegative field (c.fallbackA field))).trans c.fallbackA_feasible

theorem budgetB_nonnegative {m : ℕ} (c : ProductSecurityTrainer m) : 0 ≤ c.budgetB :=
  (Finset.sum_nonneg (fun field _ => c.bidsB_nonnegative field (c.fallbackB field))).trans c.fallbackB_feasible

def compactPreparedA {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) : SizedImplicitSampler (n + 1) :=
  prepareLeafComb n (c.compactLeafA cfg history)
    (fun field code => by
      have he := bidDecoder_valid c.bidsA field (code.cast (congrFun cfg.sizesA field).symm)
      change bidDecoder c.bidsA field code.val = c.bidsA field (code.cast (congrFun cfg.sizesA field).symm) at he
      change 0 ≤ bidDecoder c.bidsA field code.val
      rw [he]
      exact c.bidsA_nonnegative field (code.cast (congrFun cfg.sizesA field).symm))
    cfg.zeroA c.budgetA c.budgetA_nonnegative

def compactPreparedB {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) : SizedImplicitSampler (n + 1) :=
  prepareLeafComb n (c.compactLeafB cfg history)
    (fun field code => by
      have he := bidDecoder_valid c.bidsB field (code.cast (congrFun cfg.sizesB field).symm)
      change bidDecoder c.bidsB field code.val = c.bidsB field (code.cast (congrFun cfg.sizesB field).symm) at he
      change 0 ≤ bidDecoder c.bidsB field code.val
      rw [he]
      exact c.bidsB_nonnegative field (code.cast (congrFun cfg.sizesB field).symm))
    cfg.zeroB c.budgetB c.budgetB_nonnegative

theorem compactPreparedA_budget {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) : (c.compactPreparedA cfg history).budget = c.budgetA := rfl

theorem compactPreparedB_budget {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) : (c.compactPreparedB cfg history).budget = c.budgetB := rfl

theorem prepareLeafComb_target_mean_cast (n : ℕ) (data : Fin (n + 1) → ProposalLeaf)
    (hn : ∀ field (code : Fin ((data field).cap + 1)), 0 ≤ (data field).decode code.val)
    (hz : ∀ field, (data field).decode 0 = 0) (budget : ℚ) (hb : 0 ≤ budget)
    (sizes : Fin (n + 1) → ℕ) (hSize : sizes = fun field => (data field).cap + 1)
    (bids weights : (field : Fin (n + 1)) → Fin (sizes field) → ℚ) (hw : ∀ field code, 0 < weights field code)
    (hBids : ∀ field (code : Fin ((data field).cap + 1)), (data field).decode code.val = bids field (code.cast (congrFun hSize field).symm))
    (hWeights : ∀ field (code : Fin ((data field).cap + 1)), labelMass (data field).blocks code.val = weights field (code.cast (congrFun hSize field).symm))
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (test : (Fin (n + 1) → ℚ) → ℝ) :
    (prepareLeafComb n data hn hz budget hb).targetKernel.mean test =
      ∑ index, (SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).realWeight index *
        test ((SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).row index) := by
  cases hSize
  have heBids : leafBids data = bids := by funext field code; exact hBids field code
  have heWeights : leafWeights data = weights := by funext field code; exact hWeights field code
  subst bids
  subst weights
  exact prepareLeafComb_target_mean n data hn hz budget hb fallback hf test

theorem compactPreparedA_target_mean {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) (test : (Fin (n + 1) → ℚ) → ℝ) :
    (c.compactPreparedA cfg history).targetKernel.mean test = (c.rawPreparedA history).rationalTargetKernel.mean test := by
  unfold rawPreparedA
  rw [ProductArrayTree.prepareSampler_rational_target_mean]
  apply prepareLeafComb_target_mean_cast n (c.compactLeafA cfg history) _ cfg.zeroA c.budgetA c.budgetA_nonnegative
    c.sizesA cfg.sizesA c.bidsA (c.rawFieldsA history) (c.rawFieldsA_positive history) _ _ c.fallbackA c.fallbackA_feasible test
  · intro field code
    exact bidDecoder_valid c.bidsA field (code.cast (congrFun cfg.sizesA field).symm)
  · intro field code
    exact c.compactBlocksA_refines cfg history field code

theorem compactPreparedB_target_mean {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) (test : (Fin (n + 1) → ℚ) → ℝ) :
    (c.compactPreparedB cfg history).targetKernel.mean test = (c.rawPreparedB history).rationalTargetKernel.mean test := by
  unfold rawPreparedB
  rw [ProductArrayTree.prepareSampler_rational_target_mean]
  apply prepareLeafComb_target_mean_cast n (c.compactLeafB cfg history) _ cfg.zeroB c.budgetB c.budgetB_nonnegative
    c.sizesB cfg.sizesB c.bidsB (c.rawFieldsB history) (c.rawFieldsB_positive history) _ _ c.fallbackB c.fallbackB_feasible test
  · intro field code
    exact bidDecoder_valid c.bidsB field (code.cast (congrFun cfg.sizesB field).symm)
  · intro field code
    exact c.compactBlocksB_refines cfg history field code

theorem compactPreparedA_native_mean_error {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) (epsilon : ℚ) (he : 0 < epsilon)
    (test : (Fin (n + 1) → ℚ) → ℝ) (hTest : ∀ row, 0 ≤ test row ∧ test row ≤ 1) :
    |(fairBitKernel ((c.compactPreparedA cfg history).bitBudget epsilon)).mean
        (fun bits => test ((c.compactPreparedA cfg history).sample epsilon bits)) -
      (c.rawPreparedA history).rationalTargetKernel.mean test| ≤ (epsilon : ℝ) := by
  have h := (c.compactPreparedA cfg history).nativeKernel_close epsilon he test hTest
  rw [c.compactPreparedA_target_mean cfg history test] at h
  exact h

theorem compactPreparedB_native_mean_error {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) (epsilon : ℚ) (he : 0 < epsilon)
    (test : (Fin (n + 1) → ℚ) → ℝ) (hTest : ∀ row, 0 ≤ test row ∧ test row ≤ 1) :
    |(fairBitKernel ((c.compactPreparedB cfg history).bitBudget epsilon)).mean
        (fun bits => test ((c.compactPreparedB cfg history).sample epsilon bits)) -
      (c.rawPreparedB history).rationalTargetKernel.mean test| ≤ (epsilon : ℝ) := by
  have h := (c.compactPreparedB cfg history).nativeKernel_close epsilon he test hTest
  rw [c.compactPreparedB_target_mean cfg history test] at h
  exact h

end ProductSecurityTrainer
end Blotto
