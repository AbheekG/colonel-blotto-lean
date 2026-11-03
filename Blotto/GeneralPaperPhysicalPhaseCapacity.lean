import Blotto.GeneralPaperPhysicalSourcePhaseCoverage

/-! Concrete native physical cursors, including empty/terminal prefixes,
inherit the complete prepared source-to-row live bound and its derived word.
No space premise or cursor validation is supplied to execution. -/
namespace Blotto.GeneralPaperPhysicalPhaseCapacity
open GeneralPaperCodeAlphabet GeneralPaperSourceWordGrowth GeneralPaperInitializerPreparedPoint
open GeneralPaperCatalogueShared GeneralPaperFastRationalModel GeneralPaperPhysicalResponseReference
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

inductive Cursor (m : ℕ) where
  | decoder : Fin m → Cursor m
  | rowPrefix : Fin (m+1) → Cursor m
  | scan : Fin m → Cursor m
  | scanPrefix : Fin (m+1) → Cursor m
  | finalCheck : Cursor m
  | response : Cursor m

def window {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (B : ℚ) : Cursor m → ℕ
  | .decoder j => GeneralPaperPhysicalBidStorage.window model W a delta (codes.read j)
  | .rowPrefix used => GeneralPaperPhysicalResponseStorage.rowPrefix model W a delta codes used.val (Nat.le_of_lt_succ used.isLt)
  | .scan used => GeneralPaperRowBudgetStorage.localWindow model (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 used.val (Nat.succ_le_of_lt used.isLt)
  | .scanPrefix used => GeneralPaperRowBudgetStorage.peak model (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 used.val (Nat.le_of_lt_succ used.isLt)
  | .finalCheck => GeneralPaperRowBudgetStorage.finalWindow model (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 B
  | .response => GeneralPaperPhysicalResponseStorage.window model W a delta codes B

theorem covered {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (B : ℚ) (cursor : Cursor m) :
    window model W a delta codes B cursor≤GeneralPaperPhysicalResponseStorage.window model W a delta codes B := by
  cases cursor with
  | decoder j => exact GeneralPaperPhysicalRowPhaseCoverage.decoder_covered model W a delta codes B j
  | rowPrefix used => exact GeneralPaperPhysicalRowPhaseCoverage.prefix_covered model W a delta codes B used.val (Nat.le_of_lt_succ used.isLt)
  | scan used => exact GeneralPaperPhysicalRowPhaseCoverage.physical_scan_covered model W a delta codes B used.val (Nat.succ_le_of_lt used.isLt)
  | scanPrefix used => exact GeneralPaperPhysicalRowPhaseCoverage.scan_prefix_covered model W a delta codes B used.val (Nat.le_of_lt_succ used.isLt)
  | finalCheck => exact GeneralPaperPhysicalRowPhaseCoverage.final_check_covered model W a delta codes B
  | response => exact le_rfl

noncomputable def preparedWindow (actual : RationalCostModel) (W : ℕ) (x : Input)
    (epoch : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period) (cursor : Cursor x.m) : ℕ :=
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let c := ready.2.source
  let hc : c=GeneralPaperMaterializedPowerCache.specification x.m (alphabet x).lambda x.k x.Qv := by
    dsimp only [c,ready]; rw [GeneralPaperPreparedSharedSource.data]; rfl
  let codes := GeneralPaperPhysicalSourcePhaseCoverage.sourceResponse actual W x.k x.Qv
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x) c hc
    (prepare (alphabet x) x.k x.Qv x.weights Bc Br)
    (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs epoch time
  window actual W (alphabet x)
    (GeneralPaperPhysicalShiftExecution.run true actual W x.m (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x).C).1
    codes Br cursor

theorem in_extra (actual : RationalCostModel) (W : ℕ) (x : Input)
    (epoch : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period) (cursor : Cursor x.m) :
    preparedWindow actual W x epoch time cursor≤GeneralPaperPhysicalResponseStorageContract.extraWindow actual W x := by
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let c := ready.2.source
  have hc : c=GeneralPaperMaterializedPowerCache.specification x.m (alphabet x).lambda x.k x.Qv := by
    dsimp only [c,ready]; rw [GeneralPaperPreparedSharedSource.data]; rfl
  have h := GeneralPaperPhysicalSourcePhaseCoverage.response_in_extra actual W x.k x.Qv
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x) c hc x.weights Bc Br
    (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs epoch time
  exact (covered actual W (alphabet x) _ _ Br cursor).trans h

theorem in_live (actual : RationalCostModel) (W : ℕ) (x : Input) (first : Bool)
    (epoch : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period) (cursor : Cursor x.m) :
    preparedWindow actual W x epoch time cursor≤GeneralPaperPhysicalResponseStorageContract.live actual W x first :=
  (in_extra actual W x epoch time cursor).trans (Nat.le_add_left _ _)

theorem capacity {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) (x : Input) (_first : Bool)
    (epoch : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period) (cursor : Cursor x.m) :
    preparedWindow actual (width C d x) x epoch time cursor<2^width C d x :=
  (in_live actual _ x _first epoch time cursor).trans_lt
    (GeneralPaperPhysicalResponseStorageContract.native_capacity hg x _first)

theorem address {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) (x : Input) (_first : Bool)
    (epoch : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period) (cursor : Cursor x.m)
    (a : ℕ) (ha : a≤preparedWindow actual (width C d x) x epoch time cursor) : binaryWordWidth a≤width C d x :=
  GeneralPaperPhysicalResponseStorageContract.native_address hg x _first a (ha.trans (in_live actual _ x _first epoch time cursor))

theorem paper_space {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ A e : ℕ,∀ (x : Input) (_first : Bool),1≤x.m →
      ∀ (epoch : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs)
      (time : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period) (cursor : Cursor x.m),
      preparedWindow actual (width C d x) x epoch time cursor≤
        A*GeneralPaperSharpSourceSpaceRate.paperRate x*(logSize x)^e := by
  rcases GeneralPaperPhysicalResponseStorageContract.native_paper_space hg with ⟨A,e,hA⟩
  exact ⟨A,e,fun x first hm epoch time cursor => (in_live actual _ x first epoch time cursor).trans (hA x first hm)⟩

end Blotto.GeneralPaperPhysicalPhaseCapacity
