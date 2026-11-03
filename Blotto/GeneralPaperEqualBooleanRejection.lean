import Blotto.GeneralPaperEqualBooleanTrial

/-! Finite observations of one uncapped Boolean rejection computation.
Failure leaves the observation unfinished; a completed observation stops at
the first accepted block. The cap is an analysis parameter, not a fallback. -/
namespace Blotto.GeneralPaperEqualBooleanRejection
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperEqualBooleanCache (Cache)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 700000

structure Result (α : Type*) where
  output : Option α
  reads : ℕ
  work : ℕ

def trial {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (bits : Fin (UniformNatRejection.width p.D) → Bool) :=
  GeneralPaperEqualBooleanTrial.run c GeneralPaperBooleanFreshWord.nextList
    (List.ofFn (fun i => bits (i.cast p.rangeBits_correct)))

theorem trial_output {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (bits : Fin (UniformNatRejection.width p.D) → Bool) :
    (trial c bits).output = (UniformNatRejection.attempt p.D bits).map (GeneralPaperEqualPreparedCache.select p) := by
  rw [trial, GeneralPaperEqualBooleanTrial.output, GeneralPaperEqualPreparedCache.attempt_eq]

def run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) : ℕ → (ℕ → Fin (UniformNatRejection.width p.D) → Bool) → Result (Fin (count l))
  | 0, _ => ⟨none, 0, 0⟩
  | cap + 1, tape =>
    let current := trial c (tape 0)
    match current.output with
    | some i => ⟨some i, current.reads, current.work + 4⟩
    | none =>
      let later := run c cap (GeneralPaperEqualRejectionPrefix.tail tape)
      ⟨later.output, current.reads + later.reads, current.work + later.work + 8⟩

theorem data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width p.D) → Bool) :
    (run c cap tape).output = (GeneralPaperEqualRejectionPrefix.blockRun p.D cap tape).output.map
      (GeneralPaperEqualPreparedCache.select p) ∧
    (run c cap tape).reads = (GeneralPaperEqualRejectionPrefix.blockRun p.D cap tape).reads := by
  induction cap generalizing tape with
  | zero => exact ⟨rfl, rfl⟩
  | succ cap ih =>
    have hr : (trial c (tape 0)).reads = UniformNatRejection.width p.D := by
      rw [trial, GeneralPaperEqualBooleanTrial.reads, p.rangeBits_correct]
    have ht := ih (GeneralPaperEqualRejectionPrefix.tail tape)
    rw [run, GeneralPaperEqualRejectionPrefix.blockRun]
    dsimp only
    rw [trial_output]
    cases UniformNatRejection.attempt p.D (tape 0) <;>
      simp only [Option.map_none, Option.map_some, BinaryPayload.readCount_eq, hr, ht.1, ht.2, and_self]

theorem work {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width p.D) → Bool) :
    (run c cap tape).work ≤ cap * (GeneralPaperEqualBooleanTrial.bound p + 8) := by
  induction cap generalizing tape with
  | zero => simp only [run, Nat.zero_mul, le_refl]
  | succ cap ih =>
    have hh := GeneralPaperEqualBooleanTrial.work c GeneralPaperBooleanFreshWord.nextList
      (List.ofFn (fun i => tape 0 (i.cast p.rangeBits_correct)))
    have ht := ih (GeneralPaperEqualRejectionPrefix.tail tape)
    change (trial c (tape 0)).work ≤ _ at hh
    conv => lhs; rw [run]
    dsimp only
    split <;> dsimp only <;> simp only [Nat.add_mul, Nat.one_mul] <;> omega

theorem success_stable_one {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width p.D) → Bool)
    (i : Fin (count l)) (h : (run c cap tape).output = some i) : run c (cap + 1) tape = run c cap tape := by
  induction cap generalizing tape with
  | zero => simp only [run, reduceCtorEq] at h
  | succ cap ih =>
    conv at h => lhs; rw [run]
    conv => rhs; rw [run]
    conv => lhs; rw [run]
    dsimp only at h ⊢
    cases he : (trial c (tape 0)).output with
    | some label => rfl
    | none =>
      simp only [he] at h ⊢
      rw [ih _ h]

end Blotto.GeneralPaperEqualBooleanRejection
