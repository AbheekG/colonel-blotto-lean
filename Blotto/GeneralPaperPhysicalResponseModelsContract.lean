import Blotto.GeneralPaperPhysicalResponseStorageContract

/-! The native checked source-to-row path now shares one derived logarithmic
word for sharp real/bit time, simultaneous storage, finite capacity and
addresses. Both returned rows and combined physical/output flags agree.
Final native model refinement and compiler/input/output joins remain. -/
namespace Blotto.GeneralPaperPhysicalResponseModelsContract
open GeneralPaperSourceWordGrowth GeneralPaperInitializerPreparedPoint
open GeneralPaperFastRationalModel GeneralPaperPhysicalResponseReference
open GeneralPaperPhysicalResponseRowsContract GeneralPaperSourceCoreLogBound
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384

theorem native_paper_time {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ Ar er Ab eb : ℕ,∀ x,1≤x.m →
      (preparedRun false actual 1 x).2≤Ar*GeneralPaperSharpSourceRealRate.paperRate x*(coreLog x)^er ∧
      (preparedRun true actual (width C d x) x).2≤Ab*GeneralPaperSharpSourceBitRate.paperRate x*(logSize x)^eb :=
  GeneralPaperPhysicalResponseRowsContract.native_paper_time hg _ (width_tight C d)

theorem paper_contract {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ Ar er Ab eb As es Aw : ℕ,∀ (x : Input) (first : Bool),1≤x.m → 0<x.Qv →
      width C d x≤Aw*logSize x ∧
      (preparedRun false actual 1 x).2≤Ar*GeneralPaperSharpSourceRealRate.paperRate x*(coreLog x)^er ∧
      (preparedRun true actual (width C d x) x).2≤Ab*GeneralPaperSharpSourceBitRate.paperRate x*(logSize x)^eb ∧
      GeneralPaperPhysicalResponseStorageContract.live actual (width C d x) x first≤
        As*GeneralPaperSharpSourceSpaceRate.paperRate x*(logSize x)^es ∧
      GeneralPaperPhysicalResponseStorageContract.live actual (width C d x) x first<2^width C d x ∧
      (∀ address,address≤GeneralPaperPhysicalResponseStorageContract.live actual (width C d x) x first →
        binaryWordWidth address≤width C d x) ∧
      (preparedRun true actual (width C d x) x).1=(preparedRun false actual 1 x).1 ∧
      (preparedRun true actual (width C d x) x).1.2=true ∧
      ∀ i : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows,
        Feasible (ownBudget x.m x.k (x.b:ℝ) x.reciprocal:ℝ)
          (fun j => (((preparedRun true actual (width C d x) x).1.1.read i).read j:ℝ)) ∧
        ∀ j,RationalHeight (((preparedRun true actual (width C d x) x).1.1.read i).read j)
          (binaryWordWidth (alphabet x).C) := by
  rcases native_paper_time hg with ⟨Ar,er,Ab,eb,ht⟩
  rcases GeneralPaperPhysicalResponseStorageContract.native_paper_space hg with ⟨As,es,hs⟩
  rcases width_tight C d with ⟨Aw,hw⟩
  refine ⟨Ar,er,Ab,eb,As,es,Aw,?_⟩
  intro x first hm hQv
  have hm' : 0<x.m := by omega
  exact ⟨hw x,(ht x hm).1,(ht x hm).2,hs x first hm,
    GeneralPaperPhysicalResponseStorageContract.native_capacity hg x first,
    GeneralPaperPhysicalResponseStorageContract.native_address hg x first,
    native_model_data actual _ x hm' hQv,native_checks true actual _ x hm' hQv,
    fun i => ⟨native_hard_budget true actual _ x hm' hQv i,native_coordinate_height true actual _ x i⟩⟩

end Blotto.GeneralPaperPhysicalResponseModelsContract
