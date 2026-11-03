import Blotto.GeneralPaperSignedDeltaStepPrice

/-! One indexed callback per occurrence or cell. The same two loop
implementations serve all eight arrays. Plans, prefixes, mesh and selected
bids are retained inputs; no ranks or query plans are prepared in the loop.
-/
namespace Blotto.GeneralPaperDeltaArrayExecution
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def unsignedElement {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n) : ℕ × ℕ :=
  let result := GeneralPaperUnsignedDeltaStepPrice.run bits price W mesh response cdfPrefix tailPrefix plan q
  (result.1,result.2+32*W)

def unsigned {n k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) : FixedArrayTable n ℕ × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W n else W)
    (unsignedElement bits price W mesh response cdfPrefix tailPrefix plan)

def signedElement {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh U bid : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperSignedUpdatePlan.Plan k n) (q : Fin n) : ℕ × ℕ :=
  let result := GeneralPaperSignedDeltaStepPrice.run bits price W mesh U bid prefixes plan q
  (result.1.increment,result.2+32*W)

def signed {n k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W mesh U bid : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperSignedUpdatePlan.Plan k n) : FixedArrayTable n ℕ × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W n else W) (signedElement bits price W mesh U bid prefixes plan)

theorem unsigned_data {n k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (unsigned bits index price W mesh response cdfPrefix tailPrefix plan).1=
      (GeneralPaperNativeDeltaArrays.unsigned k response cdfPrefix tailPrefix plan).1 := by
  rw [unsigned,GeneralPaperNativeDeltaArrays.unsigned,PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
  congr 1
  funext q
  exact GeneralPaperUnsignedDeltaStepPrice.data bits price W mesh response cdfPrefix tailPrefix plan q hMesh

theorem signed_data {n k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W mesh U bid : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperSignedUpdatePlan.Plan k n) (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (signed bits index price W mesh U bid prefixes plan).1=(GeneralPaperNativeDeltaArrays.signed k U bid prefixes plan).1 := by
  rw [signed,GeneralPaperNativeDeltaArrays.signed,PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
  congr 1
  funext q
  exact congrArg GeneralPaperSignedUpdatePlan.Result.increment (GeneralPaperSignedDeltaStepPrice.data bits price W mesh U bid prefixes plan q hMesh)

theorem unsigned_same_data {n k : ℕ} (price : ℕ → ℕ) (W mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (unsigned true (fun w => w) price W mesh response cdfPrefix tailPrefix plan).1=
      (unsigned false (fun _ => 1) (fun _ => 1) 1 mesh response cdfPrefix tailPrefix plan).1 := by
  rw [unsigned_data true (fun w => w) price W mesh response _ _ _ hMesh,
    unsigned_data false (fun _ => 1) (fun _ => 1) 1 mesh response _ _ _ hMesh]

theorem signed_same_data {n k : ℕ} (price : ℕ → ℕ) (W mesh U bid : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperSignedUpdatePlan.Plan k n) (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (signed true (fun w => w) price W mesh U bid prefixes plan).1=(signed false (fun _ => 1) (fun _ => 1) 1 mesh U bid prefixes plan).1 := by
  rw [signed_data true (fun w => w) price W mesh U bid _ _ hMesh,
    signed_data false (fun _ => 1) (fun _ => 1) 1 mesh U bid _ _ hMesh]

end Blotto.GeneralPaperDeltaArrayExecution
