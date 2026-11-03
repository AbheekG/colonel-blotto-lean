import Blotto.GeneralPaperCatalogueEpochCache

/-! Both adaptive native row selectors read the same four-family snapshot.
The common-width native indices are transported only into their constructed
field plans. Numerical row codes agree with the exact codes used by all
eight loss updates; proof transports perform no run-time data conversion.
-/
namespace Blotto.GeneralPaperCatalogueEpochRows
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueOptimizer
open GeneralPaperCatalogueRowSemantics
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

structure Rows (m k : ℕ) where
  candidate : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
  response : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))

def chooseRows {m k : ℕ} (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) (Bc Br : ℚ) : Rows m k :=
  let lambdaPrefix := FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)
  let muPrefix := FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)
  ⟨pickRow cache.candidate profit T weights lambdaPrefix Bc,pickRow cache.response profit T weights muPrefix Br⟩

def Rows.fieldChoice {m k : ℕ} {cache : Cache m k} (rows : Rows m k) (state : State cache) (j : Fin m) :
    GeneralPaperEpochDeltas.Choice (state.fields.read j).plan :=
  ⟨⟨(rows.candidate.read j).val,by rw [state.plan_spec,candidate_count]; exact (rows.candidate.read j).isLt⟩,
    ⟨(rows.response.read j).val,by rw [state.plan_spec,response_count]; exact (rows.response.read j).isLt⟩⟩

theorem read_data_eq {α : Type*} {n p : ℕ} (x : FixedArrayTable n α) (y : FixedArrayTable p α)
    (i : Fin n) (j : Fin p) (hData : x.data=y.data) (hIndex : i.val=j.val) : x.read i=y.read j := by
  have hx : i.val<x.data.size := by rw [x.size]; exact i.isLt
  have hy : j.val<y.data.size := by rw [y.size]; exact j.isLt
  have he : x.data[i.val]?=y.data[j.val]? := by rw [hData,hIndex]
  rw [Array.getElem?_eq_getElem hx,Array.getElem?_eq_getElem hy] at he
  exact Option.some.inj he

theorem field_candidate {m k : ℕ} {cache : Cache m k} (rows : Rows m k) (state : State cache) (j : Fin m) :
    (rows.fieldChoice state j).candidateBid=(rowCodes cache.candidate.data rows.candidate).read j := by
  have hData : (state.fields.read j).plan.candidateOptions.data=(cache.candidate.data.codes.read j).data := by
    rw [state.plan_spec,candidate_options_data]
  rw [rowCodes,FixedArrayTable.read_ofFn]
  exact read_data_eq _ _ _ _ hData rfl

theorem field_response {m k : ℕ} {cache : Cache m k} (rows : Rows m k) (state : State cache) (j : Fin m) :
    (rows.fieldChoice state j).responseBid=(rowCodes cache.response.data rows.response).read j := by
  have hData : (state.fields.read j).plan.responseOptions.data=(cache.response.data.codes.read j).data := by
    rw [state.plan_spec,response_options_data]
  rw [rowCodes,FixedArrayTable.read_ofFn]
  exact read_data_eq _ _ _ _ hData rfl

end Blotto.GeneralPaperCatalogueEpochRows
