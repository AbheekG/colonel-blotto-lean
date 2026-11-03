import Blotto.GeneralPaperCatalogueEpochBounds

/-! Both concrete adaptive row selectors obey their hard physical budgets
on the actual positive coherent snapshots. These properties are derived
from the generated zero entries and native optimizer, without comparison
rows, summary-order assumptions or supplied feasibility callbacks.
-/
namespace Blotto.GeneralPaperCatalogueEpochFeasible
open scoped BigOperators
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRows GeneralPaperCatalogueEpoch
open GeneralPaperCatalogueOptimizer GeneralPaperCatalogueRowSemantics
open GeneralPaperEpochSnapshot
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

theorem block_feasible {m k : ℕ} (ready : Ready m k) (Qv q qbar : ℕ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv)
    (blocks : FixedArrayTable m (Block k)) (hPositive : ∀ j, (blocks.read j).Positive)
    (hCoherent : ∀ j, (blocks.read j).Coherent) (B : ℚ) (hB : 0≤B) (hBudgetDen : B.den∣q) :
    let prefixes := FixedArrayTable.ofFn (fun j => (blocks.read j).cdf)
    let output := pickRow ready (GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows weights prefixes B
    (∀ j, 0≤((rowChoices ready.data output).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar ready.alphabet.C)) ∧
      (∑ j, ((rowChoices ready.data output).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar ready.alphabet.C))≤B := by
  let values := FixedArrayTable.ofFn (fun j => (blocks.read j).values)
  have hTotal : ∀ j, 0<∑ r, (values.read j).read r := by
    intro j
    simpa only [values,FixedArrayTable.read_ofFn,Block.Positive] using hPositive j
  have hPrefixes : FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))=
      FixedArrayTable.ofFn (fun j => (blocks.read j).cdf) := by
    apply PRGExactRealRAMContract.table_ext
    intro j
    simp only [values,FixedArrayTable.read_ofFn]
    exact (hCoherent j).symm
  have he := GeneralPaperCatalogueOptimizerBudget.pick_feasible ready Qv q qbar hm hQv hq hCap weights hWeights values hTotal B hB hBudgetDen
  dsimp only at he
  rw [hPrefixes] at he
  exact he

theorem candidate_feasible {m k : ℕ} (cache : Cache m k) (Qv q qbar : ℕ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv)
    (before : FixedArrayTable m (Snapshot k)) (hPositive : ∀ j, Positive (before.read j))
    (hCoherent : ∀ j, Coherent (before.read j)) (Bc Br : ℚ) (hB : 0≤Bc) (hBudgetDen : Bc.den∣q) :
    let rows := chooseRows cache (GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows weights before Bc Br
    (∀ j, 0≤((rowChoices cache.candidate.data rows.candidate).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C)) ∧
      (∑ j, ((rowChoices cache.candidate.data rows.candidate).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C))≤Bc := by
  have he := block_feasible cache.candidate Qv q qbar hm hQv hq hCap weights hWeights
    (FixedArrayTable.ofFn (fun j => (before.read j).lambda))
    (fun j => by rw [FixedArrayTable.read_ofFn]; exact (hPositive j).2.2.1)
    (fun j => by rw [FixedArrayTable.read_ofFn]; exact (hCoherent j).2.2.1) Bc hB hBudgetDen
  have ha : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  rw [ha] at he
  simpa only [chooseRows,FixedArrayTable.read_ofFn] using he

theorem response_feasible {m k : ℕ} (cache : Cache m k) (Qv q qbar : ℕ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv)
    (before : FixedArrayTable m (Snapshot k)) (hPositive : ∀ j, Positive (before.read j))
    (hCoherent : ∀ j, Coherent (before.read j)) (Bc Br : ℚ) (hB : 0≤Br) (hBudgetDen : Br.den∣q) :
    let rows := chooseRows cache (GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows weights before Bc Br
    (∀ j, 0≤((rowChoices cache.response.data rows.response).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C)) ∧
      (∑ j, ((rowChoices cache.response.data rows.response).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C))≤Br := by
  have he := block_feasible cache.response Qv q qbar hm hQv hq hCap weights hWeights
    (FixedArrayTable.ofFn (fun j => (before.read j).mu))
    (fun j => by rw [FixedArrayTable.read_ofFn]; exact (hPositive j).2.2.2)
    (fun j => by rw [FixedArrayTable.read_ofFn]; exact (hCoherent j).2.2.2) Br hB hBudgetDen
  have ha : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  rw [ha] at he
  simpa only [chooseRows,FixedArrayTable.read_ofFn] using he

end Blotto.GeneralPaperCatalogueEpochFeasible
