import Blotto.GeneralPaperNativeProfitScalarPrice

/-! One retained coefficient and one indexed option fill produce a native
ordered-resource DP leaf. Each option queries its cached signed tails once,
forms one integer numerator and borrows the exact prepared resource tag.
-/
namespace Blotto.GeneralPaperNativeProfitLeafExecution
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
variable {R : Type}

def element {K k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W coefficient : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperOrderedNativeOptionProfits.Plan R k K) (i : Fin K) : (ℕ × R) × ℕ :=
  let queried := GeneralPaperMeshPairExecution.tails bits price W plan.mesh prefixes plan.tails i
  let numerator := GeneralPaperNativeProfitScalarPrice.profit price W coefficient plan.mesh queried.1.positive queried.1.negative
  ((numerator.1,plan.tags.read i),queried.2+numerator.2+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) queried.1.work 24+
    128*(if bits then GeneralPaperMeshQueryMetadata.referenceWord W k else W))

def run {K k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W T weight : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperOrderedNativeOptionProfits.Plan R k K) : GeneralPaperOrderedProfitDP.Field R K × ℕ :=
  let primitive := if bits then price else fun _ => 1
  let coefficient := GeneralPaperNativeProfitScalarPrice.coefficient primitive W T weight
  let filled := PaperIndexedArrayConstruction.run index (if bits then arrayWord W K else W)
    (element bits primitive W coefficient.1 prefixes plan)
  (filled.1,coefficient.2+filled.2+64*W)

theorem element_data {K k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W coefficient : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperOrderedNativeOptionProfits.Plan R k K) (i : Fin K)
    (hMesh : plan.mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (element bits price W coefficient prefixes plan i).1=
      (coefficient*(plan.mesh+(GeneralPaperSignedTailPlan.evaluate k prefixes plan.tails i).positive-
        (GeneralPaperSignedTailPlan.evaluate k prefixes plan.tails i).negative),plan.tags.read i) := by
  unfold element
  dsimp only
  rw [GeneralPaperNativeProfitScalarPrice.profit_data,GeneralPaperMeshPairExecution.tails_data bits price W plan.mesh _ _ _ hMesh]

theorem data {K k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W T weight : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperOrderedNativeOptionProfits.Plan R k K)
    (hMesh : plan.mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits index price W T weight prefixes plan).1=(GeneralPaperOrderedNativeOptionProfits.build k T weight prefixes plan).1 := by
  unfold run GeneralPaperOrderedNativeOptionProfits.build
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
  congr 1
  funext i
  exact element_data bits _ W (2*T*weight) prefixes plan i hMesh

theorem tags_preserved {K k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W T weight : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperOrderedNativeOptionProfits.Plan R k K) (i : Fin K) :
    ((run bits index price W T weight prefixes plan).1.read i).2=plan.tags.read i := by
  rw [run,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  rfl

end Blotto.GeneralPaperNativeProfitLeafExecution
