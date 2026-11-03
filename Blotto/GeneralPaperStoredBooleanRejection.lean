import Blotto.GeneralPaperStoredBooleanTrialSource

/-! Finite observations of the stored first-success rejection computation.
The cap is only an observation parameter; no fallback is emitted on failure.
Observed work depends on reached trials, so successful extensions are stable. -/
namespace Blotto.GeneralPaperStoredBooleanRejection
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualBooleanRejection (Result)
open GeneralPaperStoredBooleanTrialSource (Correct)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def tail (tape : ℕ → List Bool) : ℕ → List Bool := fun t => tape (t + 1)

def run (model : RationalCostModel) (A : ℕ) (installed : Installed A) : ℕ → (ℕ → List Bool) → Result ℕ
  | 0,_ => ⟨none,0,0⟩
  | cap + 1,tape =>
    let current := GeneralPaperStoredBooleanTrial.run model A installed GeneralPaperBooleanFreshWord.nextList (tape 0)
    match current.output with
    | some label => ⟨some label,current.reads,current.work + 64 * (A + 1)⟩
    | none =>
      let later := run model A installed cap (tail tape)
      ⟨later.output,current.reads + later.reads,current.work + later.work + 128 * (A + 1)⟩

/- Source-width block conversion is solely a semantic observer used to
compare finite random inputs. The executed runner receives raw bit blocks. -/
def blocks {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (tape : ℕ → Fin (UniformNatRejection.width prepared.D) → Bool) : ℕ → List Bool :=
  fun t => List.ofFn (fun i : Fin prepared.rangeBits => tape t (i.cast prepared.rangeBits_correct))

def price {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {prepared : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared) : ℕ → (ℕ → Fin (UniformNatRejection.width prepared.D) → Bool) → ℕ
  | 0,_ => 0
  | cap + 1,tape =>
    let current := GeneralPaperStoredBooleanTrial.run model A installed GeneralPaperBooleanFreshWord.nextList (blocks prepared tape 0)
    match (GeneralPaperEqualBooleanRejection.trial cache (tape 0)).output with
    | some _ => current.work + 64 * (A + 1)
    | none => current.work + price model A installed cache cap (GeneralPaperEqualRejectionPrefix.tail tape) + 128 * (A + 1)

theorem source {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {prepared : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared) (hCorrect : Correct model A installed cache)
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width prepared.D) → Bool) :
    (run model A installed cap (blocks prepared tape)).output = (GeneralPaperEqualBooleanRejection.run cache cap tape).output.map Fin.val ∧
      (run model A installed cap (blocks prepared tape)).reads = (GeneralPaperEqualBooleanRejection.run cache cap tape).reads ∧
      (run model A installed cap (blocks prepared tape)).work = price model A installed cache cap tape := by
  induction cap generalizing tape with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ cap ih =>
    obtain ⟨hTrial,hReads⟩ := GeneralPaperStoredBooleanTrialSource.trial_source model A installed cache hCorrect (tape 0)
    have hTail : tail (blocks prepared tape) = blocks prepared (GeneralPaperEqualRejectionPrefix.tail tape) := rfl
    have hLater := ih (GeneralPaperEqualRejectionPrefix.tail tape)
    simp only [run,blocks] at hTrial hReads ⊢
    rw [hTrial]
    cases h : (GeneralPaperEqualBooleanRejection.trial cache (tape 0)).output <;>
      simp only [Option.map_none,Option.map_some,GeneralPaperEqualBooleanRejection.run,h,hReads,
        hTail,hLater.1,hLater.2.1,hLater.2.2,price,blocks,and_self]

theorem success_stable_one (model : RationalCostModel) (A : ℕ) (installed : Installed A) (cap : ℕ)
    (tape : ℕ → List Bool) (label : ℕ) (hSuccess : (run model A installed cap tape).output = some label) :
    run model A installed (cap + 1) tape = run model A installed cap tape := by
  induction cap generalizing tape with
  | zero => simp only [run,reduceCtorEq] at hSuccess
  | succ cap ih =>
    conv at hSuccess => lhs; rw [run]
    conv => lhs; rw [run]
    conv => rhs; rw [run]
    dsimp only at hSuccess ⊢
    cases hCurrent : (GeneralPaperStoredBooleanTrial.run model A installed GeneralPaperBooleanFreshWord.nextList (tape 0)).output with
    | some value => rfl
    | none =>
      simp only [hCurrent] at hSuccess ⊢
      rw [ih (tail tape) hSuccess]

theorem block_source {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {prepared : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared) (hCorrect : Correct model A installed cache)
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width prepared.D) → Bool) :
    (run model A installed cap (blocks prepared tape)).output =
      (GeneralPaperEqualRejectionPrefix.blockRun prepared.D cap tape).output.map
        (fun rank => (GeneralPaperEqualPreparedCache.select prepared rank).val) ∧
      (run model A installed cap (blocks prepared tape)).reads = (GeneralPaperEqualRejectionPrefix.blockRun prepared.D cap tape).reads := by
  obtain ⟨hv,hr,_⟩ := source model A installed cache hCorrect cap tape
  obtain ⟨hb,hbr⟩ := GeneralPaperEqualBooleanRejection.data cache cap tape
  rw [hb] at hv
  exact ⟨by simpa only [Option.map_map,Function.comp_def] using hv,hr.trans hbr⟩

theorem success_stable (model : RationalCostModel) (A : ℕ) (installed : Installed A) (cap extra : ℕ)
    (tape : ℕ → List Bool) (label : ℕ) (hSuccess : (run model A installed cap tape).output = some label) :
    run model A installed (cap + extra) tape = run model A installed cap tape := by
  induction extra with
  | zero => simp only [Nat.add_zero]
  | succ extra ih =>
    have hNow : (run model A installed (cap + extra) tape).output = some label := by rw [ih]; exact hSuccess
    rw [Nat.add_succ,success_stable_one model A installed (cap + extra) tape label hNow,ih]

end Blotto.GeneralPaperStoredBooleanRejection
