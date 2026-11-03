import Blotto.GeneralPaperSourceRowsStorageContract

/-! Complete native source-to-row time, simultaneous storage, reference
capacity and output/feasibility contracts at one derived logarithmic word.
Original-input/compiler/output-driver joins remain outside this component. -/
namespace Blotto.GeneralPaperSourceRowsModelsContract
open GeneralPaperSourceWordGrowth GeneralPaperInitializerPreparedPoint GeneralPaperCatalogueShared
open GeneralPaperFastRationalModel GeneralPaperSourceRowsReference
open GeneralPaperSourceRowsSharpContract GeneralPaperSourceCoreLogBound
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

theorem bit_native_profile {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (W : ℕ) (x : Input) : (preparedRun true actual W x).2≤
      GeneralPaperSourceRowsDriver.bitProfile C d W x.m x.k x.Qv ((alphabet x).lambda+1) (alphabet x) := by
  have hb : (0:ℝ)<x.b ∧ (x.b:ℝ)<1 := by exact_mod_cast x.hb
  have hbc := (GeneralPaperSourceBudgetWidths.own_word x.m x.k (x.b:ℝ) hb x.reciprocal).trans
    (GeneralPaperSourceBudgetWidths.leaf_word x.m x.k 0)
  have hbr := (GeneralPaperSourceBudgetWidths.opposing_word x.m x.k (x.b:ℝ) hb x.reciprocal).trans
    (GeneralPaperSourceBudgetWidths.leaf_word x.m x.k 0)
  exact GeneralPaperSourceRowsDriver.bit_work hg W x.k x.Qv ((alphabet x).lambda+1) (alphabet x) _ _
    x.weights (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal) _
    (by rw [GeneralPaperPreparedSharedSource.data]; rfl) x.weight_sum
    (GeneralPaperSourceBudgetWidths.own_height x.m x.k (x.b:ℝ) hb x.reciprocal) hbc hbr

theorem bit_profile_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,
    GeneralPaperSourceRowsDriver.bitProfile C d (width C d x) x.m x.k x.Qv ((alphabet x).lambda+1) (alphabet x)≤
      A*GeneralPaperSharpSourceBitRate.sourceRate x*(logSize x)^e :=
  bit_profile_soft C d _ (width_tight C d)

theorem paper_bit_profile_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,1≤x.m →
    GeneralPaperSourceRowsDriver.bitProfile C d (width C d x) x.m x.k x.Qv ((alphabet x).lambda+1) (alphabet x)≤
      A*GeneralPaperSharpSourceBitRate.paperRate x*(logSize x)^e := by
  rcases bit_profile_bound C d with ⟨A,e,hA⟩
  refine ⟨16*A,e,?_⟩
  intro x hm
  exact (hA x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A
    (GeneralPaperSharpSourceBitRate.nonempty_rate x hm))).trans_eq (by ring))

theorem native_paper_time {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ Ar er Ab eb : ℕ,∀ x,1≤x.m →
      (preparedRun false actual 1 x).2≤Ar*GeneralPaperSharpSourceRealRate.paperRate x*(coreLog x)^er ∧
      (preparedRun true actual (width C d x) x).2≤Ab*GeneralPaperSharpSourceBitRate.paperRate x*(logSize x)^eb := by
  rcases paper_real_bound with ⟨Ar,er,hr⟩
  rcases paper_bit_profile_bound C d with ⟨Ab,eb,hb⟩
  exact ⟨Ar,er,Ab,eb,fun x hm => ⟨(native_real_profile actual x).trans (hr x hm),
    (bit_native_profile hg _ x).trans (hb x hm)⟩⟩

theorem paper_contract {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ Ar er Ab eb As es Aw : ℕ,∀ (x : Input) (first : Bool),1≤x.m → 0<x.Qv →
      width C d x≤Aw*logSize x ∧
      (preparedRun false actual 1 x).2≤Ar*GeneralPaperSharpSourceRealRate.paperRate x*(coreLog x)^er ∧
      (preparedRun true actual (width C d x) x).2≤Ab*GeneralPaperSharpSourceBitRate.paperRate x*(logSize x)^eb ∧
      GeneralPaperSourceRowsStorageContract.live actual (width C d x) x first≤
        As*GeneralPaperSharpSourceSpaceRate.paperRate x*(logSize x)^es ∧
      GeneralPaperSourceRowsStorageContract.live actual (width C d x) x first<2^width C d x ∧
      (preparedRun true actual (width C d x) x).1=(preparedRun false actual 1 x).1 ∧
      (preparedRun true actual (width C d x) x).1.2=true ∧
      ∀ i : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows,
        Feasible (ownBudget x.m x.k (x.b:ℝ) x.reciprocal:ℝ)
          (fun j => (((preparedRun true actual (width C d x) x).1.1.read i).read j:ℝ)) ∧
        ∀ j,RationalHeight (((preparedRun true actual (width C d x) x).1.1.read i).read j)
          (binaryWordWidth (alphabet x).C) := by
  rcases native_paper_time hg with ⟨Ar,er,Ab,eb,ht⟩
  rcases GeneralPaperSourceRowsStorageContract.native_paper_space hg with ⟨As,es,hs⟩
  rcases reference_bound C d with ⟨Aw,hw⟩
  refine ⟨Ar,er,Ab,eb,As,es,Aw,?_⟩
  intro x first hm hQv
  have hm' : 0<x.m := by omega
  exact ⟨hw x,(ht x hm).1,(ht x hm).2,hs x first hm,
    GeneralPaperSourceRowsStorageContract.native_capacity hg x first,native_model_data actual _ x hm' hQv,
    native_checks true actual _ x hm' hQv,fun i => ⟨native_hard_budget true actual _ x hm' hQv i,
      native_coordinate_height true actual _ x i⟩⟩

end Blotto.GeneralPaperSourceRowsModelsContract
