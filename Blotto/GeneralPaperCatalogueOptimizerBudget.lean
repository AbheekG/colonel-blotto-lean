import Blotto.GeneralPaperCatalogueOptimizerScore

/-! Hard physical budgets and rounded-score quality of the actual total
cached row picker, against every physically feasible decoded literal row.
The denominator and zero metadata come from catalogue execution. The selected
factor-four shift is used; no physical shifts enter the DP's tag comparisons.
-/
namespace Blotto.GeneralPaperCatalogueOptimizerBudget
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCatalogueArrays
open GeneralPaperCatalogueRowSemantics GeneralPaperCatalogueOptimizer
open GeneralPaperResponseTag
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

theorem decoded_budget_iff {m : ℕ} (a : Alphabet) (response : Bool) (q qbar : ℕ) (hm : 0<m) (hq : 0<q)
    (hCap : q≤qbar) (B : ℚ) (hBudgetDen : B.den∣q) (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hDecode : ∀ j, (decode a response (codes.read j)).choice=some (choices.read j)) :
    (∑ j, (choices.read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C))≤B ↔
      (∑ j, (choices.read j).tag)≤budget B := by
  have hDen : ∀ j, (choices.read j).threshold.den≤a.C :=
    fun j => (GeneralPaperCodeDecodeSound.decode_sound a response _ _ (hDecode j)).2
  have he := GeneralPaperTagBudgetTransfer.physical_budget_iff m q qbar a.C hm hq hCap a.scalePositive B hBudgetDen
    (fun j => (choices.read j).threshold) hDen (fun j => (choices.read j).opened)
  simpa only [GeneralPaperTagBudgetTransfer.physical,GeneralPaperTagBudgetTransfer.rowTag,List.sum_ofFn,Choice.physical,Choice.tag] using he

theorem output_decoded {m k : ℕ} (ready : Ready m k)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) (j : Fin m) :
    (decode ready.alphabet ready.response ((rowCodes ready.data row).read j)).choice=
      some ((rowChoices ready.data row).read j) := by
  rw [ready.data_spec]
  exact row_decoded ready.alphabet ready.response k ready.summaries row j

theorem physical_nonnegative (choice : Choice) (delta : ℚ) (hDelta : 0≤delta) : 0≤choice.physical delta := by
  unfold Choice.physical
  apply add_nonneg (Farey.value_nonnegative choice.threshold)
  cases choice.opened <;> simp [hDelta]

theorem output_budget_iff {m k : ℕ} (ready : Ready m k) (q qbar : ℕ) (hm : 0<m) (hq : 0<q)
    (hCap : q≤qbar) (B : ℚ) (hBudgetDen : B.den∣q)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) :
    (∑ j, ((rowChoices ready.data row).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar ready.alphabet.C))≤B ↔
      (∑ j, ((rowChoices ready.data row).read j).tag)≤budget B :=
  decoded_budget_iff ready.alphabet ready.response q qbar hm hq hCap B hBudgetDen
    (rowCodes ready.data row) (rowChoices ready.data row) (output_decoded ready row)

theorem candidate_closed {m k : ℕ} (ready : Ready m k) (hResponse : ready.response=false)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) (j : Fin m) :
    ((rowChoices ready.data row).read j).opened=false := by
  have he := output_decoded ready row j
  rw [hResponse] at he
  exact GeneralPaperCodeDecodeSound.candidate_closed ready.alphabet _ _ he

theorem pick_feasible {m k : ℕ} (ready : Ready m k) (Qv q qbar : ℕ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv)
    (values : FixedArrayTable m (Summary k)) (hTotal : ∀ j, 0<∑ r, (values.read j).read r)
    (B : ℚ) (hB : 0≤B) (hBudgetDen : B.den∣q) :
    let prefixes := FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))
    let output := pickRow ready (GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows weights prefixes B
    (∀ j, 0≤((rowChoices ready.data output).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar ready.alphabet.C)) ∧
      (∑ j, ((rowChoices ready.data output).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar ready.alphabet.C))≤B := by
  dsimp only
  let prefixes := FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))
  have hZero : ∀ j, ((tags ready.data).read j).read 0=0 := by
    rw [ready.data_spec]
    exact GeneralPaperCatalogueArrays.zero_tag ready.alphabet ready.response k ready.summaries
  have hZeroBudget : GeneralPaperNativeRowOptimizer.resource k
      (GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows weights prefixes
      (GeneralPaperOrderedNativeProfitOptimizer.plans k (8*ready.alphabet.C) ready.summaries ready.data.codes (tags ready.data))
      (zeroRow m k)≤budget B := by
    rw [GeneralPaperNativeRowValues.resource_tags]
    simp only [zeroRow,FixedArrayTable.read_ofFn,hZero,Finset.sum_const_zero]
    exact budget_nonnegative B hB
  obtain ⟨output,hSolve,hCost,_⟩ := GeneralPaperNativeRowScore.score_guarantee ready.alphabet.lambda k Qv
    (8*ready.alphabet.C) hQv (by omega) weights hWeights ready.summaries values hTotal ready.data.codes (tags ready.data)
    B (zeroRow m k) hZeroBudget
  have hCall : call ready (GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows weights prefixes B=some output := by
    unfold call
    rw [ready.cached_spec]
    exact hSolve
  rw [pickRow_eq ready _ _ weights prefixes B output hCall]
  have hTag : (∑ j, ((rowChoices ready.data output).read j).tag)≤budget B := by
    rw [←resource_exact k (8*ready.alphabet.C) (GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows
      weights prefixes ready.summaries ready.data output]
    exact hCost
  have hShift := GeneralPaperTagBudgetTransfer.shift_positive m qbar ready.alphabet.C hm (by omega) ready.alphabet.scalePositive
  exact ⟨fun j => physical_nonnegative _ _ hShift.le,(output_budget_iff ready q qbar hm hq hCap B hBudgetDen output).mpr hTag⟩

theorem pick_guarantee {m k : ℕ} (ready : Ready m k) (Qv q qbar : ℕ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv)
    (values : FixedArrayTable m (Summary k)) (hTotal : ∀ j, 0<∑ r, (values.read j).read r)
    (hMono : ∀ j, Monotone (ready.summaries.read j).read)
    (hCodes : ∀ j r, (ready.summaries.read j).read r<2*(8*ready.alphabet.C))
    (B : ℚ) (hBudgetDen : B.den∣q) (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hDecode : ∀ j, (decode ready.alphabet ready.response (codes.read j)).choice=some (choices.read j))
    (hBudget : (∑ j, (choices.read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar ready.alphabet.C))≤B) :
    let prefixes := FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))
    let output := pickRow ready (GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows weights prefixes B
    (∀ j, 0≤((rowChoices ready.data output).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar ready.alphabet.C)) ∧
    (∑ j, ((rowChoices ready.data output).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar ready.alphabet.C))≤B ∧
    referenceScore k (8*ready.alphabet.C) Qv weights ready.summaries prefixes codes-
      referenceScore k (8*ready.alphabet.C) Qv weights ready.summaries prefixes (rowCodes ready.data output)≤
        (GeneralPaperSourceParameters.prepare k).eta/2 := by
  dsimp only
  let prefixes := FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))
  have hTag := (decoded_budget_iff ready.alphabet ready.response q qbar hm hq hCap B hBudgetDen codes choices hDecode).mp hBudget
  obtain ⟨output,hSolve,hCost,hScore⟩ := GeneralPaperCatalogueOptimizerScore.call_guarantee ready Qv hQv weights hWeights
    values hTotal hMono hCodes B codes choices hDecode hTag
  have hPick := pickRow_eq ready (GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
    (GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows weights prefixes B output hSolve
  rw [hPick]
  have hShift := GeneralPaperTagBudgetTransfer.shift_positive m qbar ready.alphabet.C hm (by omega) ready.alphabet.scalePositive
  exact ⟨fun j => physical_nonnegative _ _ hShift.le,(output_budget_iff ready q qbar hm hq hCap B hBudgetDen output).mpr hCost,hScore⟩

end Blotto.GeneralPaperCatalogueOptimizerBudget
