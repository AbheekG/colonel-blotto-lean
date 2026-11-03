import Blotto.GeneralPaperFieldUpdateExecution

/-! One indexed all-field update uses the single retained snapshot array
and the already selected complete rows. Each callback generates and adds its
eight arrays once. Plans persist by type, with no state validation pass.
-/
namespace Blotto.GeneralPaperRoundFieldsExecution
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRows
open GeneralPaperEpochSnapshot
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def element {m k : ℕ} {cache : Cache m k} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ)
    (state : State cache) (before : FixedArrayTable m (Snapshot k)) (rows : Rows m k) (j : Fin m) :
    GeneralPaperEpochFieldState.State k × ℕ :=
  let field := GeneralPaperFieldUpdateExecution.run bits index price W mesh (state.fields.read j) (before.read j) (rows.fieldChoice state j)
  (field.1,field.2+32*W)

def run {m k : ℕ} {cache : Cache m k} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ)
    (state : State cache) (before : FixedArrayTable m (Snapshot k)) (rows : Rows m k) : State cache × ℕ :=
  let filled := PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W) (element bits index price W mesh state before rows)
  (⟨filled.1,by
    intro j
    dsimp only [filled]
    rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact (GeneralPaperFieldUpdateExecution.retained_plan bits index price W mesh _ _ _).trans (state.plan_spec j)⟩,
    filled.2+64*W)

theorem element_data {m k : ℕ} {cache : Cache m k} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ)
    (state : State cache) (before : FixedArrayTable m (Snapshot k)) (rows : Rows m k) (j : Fin m)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (element bits index price W mesh state before rows j).1=GeneralPaperEpochFieldState.advance (state.fields.read j)
      (GeneralPaperEpochDeltas.generate (state.fields.read j) (before.read j) (rows.fieldChoice state j)).1 :=
  GeneralPaperFieldUpdateExecution.data bits index price W mesh _ _ _ hMesh

theorem round_data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ) (cache : Cache m k)
    (powers : GeneralPaperPreparedPowers.Prepared) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (state : State cache)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    let before := GeneralPaperAdaptiveEpoch.snapshots powers state.fields
    let rows := chooseRows cache profit T weights before Bc Br
    (run bits index price W mesh state before rows).1=(GeneralPaperCatalogueEpoch.round cache powers profit T weights Bc Br state).state := by
  dsimp only
  unfold run GeneralPaperCatalogueEpoch.round
  dsimp only
  congr 1
  rw [PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  exact element_data bits index price W mesh _ _ _ j hMesh

theorem every_prefix {m k : ℕ} {cache : Cache m k} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ)
    (state : State cache) (before : FixedArrayTable m (Snapshot k)) (rows : Rows m k) (count : ℕ) (hc : count≤m) :
    (PaperIndexedArrayConstruction.fill index (if bits then arrayWord W m else W)
      (element bits index price W mesh state before rows) count hc).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperRoundFieldsExecution
