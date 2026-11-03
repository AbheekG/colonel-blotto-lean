import Blotto.GeneralPaperSourceRowsReference

/-! Native source/postprocessing live ownership with the already completed
first output retained. These are erased observers of the actual runs, not
additional source/decoder passes. Literal input height remains additive. -/
namespace Blotto.GeneralPaperSourceRowsStorageContract
open GeneralPaperSourceWordGrowth GeneralPaperInitializerPreparedPoint GeneralPaperCatalogueShared
open GeneralPaperFastRationalModel GeneralPaperSourceRowsReference
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

noncomputable def postWindow (actual : RationalCostModel) (W : ℕ) (x : Input) : ℕ :=
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let c := ready.2.source
  let hc : c=GeneralPaperMaterializedPowerCache.specification x.m (alphabet x).lambda x.k x.Qv := by
    dsimp only [c,ready]; rw [GeneralPaperPreparedSharedSource.data]; rfl
  let hs : ready.1.2=prepare (alphabet x) x.k x.Qv x.weights Bc Br := by
    dsimp only [ready]; rw [GeneralPaperPreparedSharedSource.data]; rfl
  let produced := (GeneralPaperGeometricSourceExecution.run true (GeneralPaperSourceRowsExecution.index true)
    actual W x.k x.Qv (alphabet x) c hc ready.1.2
    (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs).1.2
  let codes : FixedArrayTable (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows
      (FixedArrayTable x.m ℕ) :=
    ⟨produced,GeneralPaperSourceRowsDriver.produced_size true actual W x.k x.Qv (alphabet x) c hc
      x.weights Bc Br ready.1.2 hs⟩
  GeneralPaperSourceRowsStorage.window actual W (alphabet x) codes Bc

theorem post_window_eq (actual : RationalCostModel) (W : ℕ) (x : Input) :
    postWindow actual W x=GeneralPaperSourceRowsStorage.window actual W (alphabet x)
      (GeneralPaperCatalogueFullTrajectory.table (alphabet x) x.k x.Qv x.weights
        (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal))
      (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) := by
  unfold postWindow
  dsimp only
  have h : (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights
      (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)).1.1.2=
      prepare (alphabet x) x.k x.Qv x.weights (ownBudget x.m x.k (x.b:ℝ) x.reciprocal)
        (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal) := by
    rw [GeneralPaperPreparedSharedSource.data]; rfl
  simp only [h]
  rw [GeneralPaperSourceRowsContract.native_table true actual W x.k x.Qv (alphabet x) _ _ x.weights
    (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal) _ rfl]

theorem post_bound {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) (W : ℕ) (x : Input) :
    postWindow actual W x≤GeneralPaperSourceRowsStorage.profile (GeneralPaperFastRationalMajorant.model C d) W
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows x.m ((alphabet x).lambda+1) (alphabet x) := by
  have hb : (0:ℝ)<x.b ∧ (x.b:ℝ)<1 := by exact_mod_cast x.hb
  rw [post_window_eq]
  exact (GeneralPaperSourceRowsStorage.bounded actual W ((alphabet x).lambda+1) (alphabet x) _ _
    (GeneralPaperSourceBudgetWidths.own_height x.m x.k (x.b:ℝ) hb x.reciprocal)
    (GeneralPaperSourceRowsContract.code_bound (alphabet x) x.k x.Qv x.weights _ _)).trans
      (GeneralPaperSourceRowsStorageRates.storage_mono actual _ (GeneralPaperFastRationalMajorant.dominates hg) W _ _ _ _)

def firstInput (x : Input) (reciprocal : Bool) : Input := {x with reciprocal:=reciprocal}

noncomputable def firstFootprint (actual : RationalCostModel) (W : ℕ) (x : Input) (first : Bool) : ℕ :=
  GeneralPaperEncodedRationalRows.tableFootprint W
    (GeneralPaperSourceRowsSharpContract.preparedRun true actual W (firstInput x first)).1.1

theorem first_bound (actual : RationalCostModel) (W : ℕ) (x : Input) (first : Bool) :
    firstFootprint actual W x first≤GeneralPaperEncodedRationalRows.tableProfile W
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows x.m (binaryWordWidth (alphabet x).C) :=
  GeneralPaperEncodedRationalRows.table_bound W _ _
    (GeneralPaperSourceRowsSharpContract.native_coordinate_height true actual W (firstInput x first))

noncomputable def live (actual : RationalCostModel) (W : ℕ) (x : Input) (first : Bool) : ℕ :=
  GeneralPaperSharpSourceSpaceContract.live actual W x first
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs+
    postWindow actual W x+firstFootprint actual W x first

theorem live_profile {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (W : ℕ) (x : Input) (first : Bool) : live actual W x first≤profile C d W x := by
  have hs := GeneralPaperSharpSourceSpaceContract.live_profile hg (fun _ => W) x first
    (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs le_rfl
  have hp := post_bound hg W x
  have hf := first_bound actual W x first
  exact Nat.add_le_add (Nat.add_le_add hs hp) hf

theorem native_capacity {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (x : Input) (first : Bool) : live actual (width C d x) x first<2^width C d x :=
  (live_profile hg _ x first).trans_lt (capacity C d x)

theorem native_address {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (x : Input) (first : Bool) (address : ℕ) (h : address≤live actual (width C d x) x first) :
    binaryWordWidth address≤width C d x := address_word C d x address (h.trans (live_profile hg _ x first))

theorem native_space_bound {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ A e : ℕ,∀ (x : Input) (first : Bool),
      live actual (width C d x) x first≤A*GeneralPaperClassifierSpaceRates.rate x*(logSize x)^e := by
  rcases quantitative_bound C d with ⟨A,e,hA⟩
  exact ⟨A,e,fun x first => (live_profile hg _ x first).trans (hA x)⟩

theorem native_paper_space {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ A e : ℕ,∀ (x : Input) (first : Bool),1≤x.m →
      live actual (width C d x) x first≤A*GeneralPaperSharpSourceSpaceRate.paperRate x*(logSize x)^e := by
  rcases paper_bound C d with ⟨A,e,hA⟩
  exact ⟨A,e,fun x first hm => (live_profile hg _ x first).trans (hA x hm)⟩

end Blotto.GeneralPaperSourceRowsStorageContract
