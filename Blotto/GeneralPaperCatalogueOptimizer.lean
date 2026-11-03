import Blotto.GeneralPaperCatalogueEmbedding

/-! Prepare the actual generated arrays and cached signed-tail plans once.
Calls reuse this object, a prepared profit grid and the shared trajectory
length. Both candidate and response modes use the same native optimizer.
The total row picker has a decoded zero fallback; later quality/success
proofs show that branch is unnecessary on positive actual snapshots.
-/
namespace Blotto.GeneralPaperCatalogueOptimizer
open GeneralPaperCodeAlphabet GeneralPaperCatalogueArrays
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false

structure Ready (m k : ℕ) where
  alphabet : Alphabet
  response : Bool
  summaries : FixedArrayTable m (Summary k)
  data : Arrays m ((GeneralPaperSourceParameters.prepare k).summarySize+2)
  cached : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan GeneralPaperResponseTag.Tag k
    ((GeneralPaperSourceParameters.prepare k).summarySize+2))
  data_spec : data=GeneralPaperCatalogueArrays.prepare alphabet response k summaries
  cached_spec : cached=GeneralPaperOrderedNativeProfitOptimizer.plans k (8*alphabet.C) summaries data.codes (tags data)

def prepare {m : ℕ} (a : Alphabet) (response : Bool) (k : ℕ) (summaries : FixedArrayTable m (Summary k)) : Ready m k :=
  let data := GeneralPaperCatalogueArrays.prepare a response k summaries
  let cached := GeneralPaperOrderedNativeProfitOptimizer.plans k (8*a.C) summaries data.codes (tags data)
  ⟨a,response,summaries,data,cached,rfl,rfl⟩

def call {m k : ℕ} (ready : Ready m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ) :
    Option (FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) :=
  GeneralPaperNativeRowOptimizer.optimize profit T weights prefixes ready.cached B

def zeroRow (m k : ℕ) : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :=
  FixedArrayTable.ofFn (fun _ => 0)

def pickRow {m k : ℕ} (ready : Ready m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ) :
    FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :=
  (call ready profit T weights prefixes B).getD (zeroRow m k)

theorem pickRow_eq {m k : ℕ} (ready : Ready m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)))
    (hSome : call ready profit T weights prefixes B=some row) : pickRow ready profit T weights prefixes B=row := by
  simp only [pickRow,hSome,Option.getD_some]

end Blotto.GeneralPaperCatalogueOptimizer
