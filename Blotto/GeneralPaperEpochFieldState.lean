import Blotto.GeneralPaperEpochFieldPlan

/-! Eight native level arrays for one battlefield: cells and occurrences
of each of the four learners. The stored plan is preserved by updates.
-/
namespace Blotto.GeneralPaperEpochFieldState
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
open GeneralPaperEpochFieldPlan
set_option autoImplicit false

structure State (k : ℕ) where
  plan : Plan k
  pOccurrences : Summary k
  qOccurrences : Summary k
  lambdaOccurrences : Summary k
  muOccurrences : Summary k
  pCells : FixedArrayTable plan.pCells.partition.count ℕ
  qCells : FixedArrayTable plan.qCells.partition.count ℕ
  lambdaCells : FixedArrayTable plan.lambdaCells.partition.count ℕ
  muCells : FixedArrayTable plan.muCells.partition.count ℕ

def initial {k : ℕ} (plan : Plan k) : State k :=
  ⟨plan,(GeneralPaperEpochLevelArray.initial _).1,(GeneralPaperEpochLevelArray.initial _).1,
    (GeneralPaperEpochLevelArray.initial _).1,(GeneralPaperEpochLevelArray.initial _).1,
    (GeneralPaperEpochLevelArray.initial _).1,(GeneralPaperEpochLevelArray.initial _).1,
    (GeneralPaperEpochLevelArray.initial _).1,(GeneralPaperEpochLevelArray.initial _).1⟩

def Bounded {k : ℕ} (state : State k) (bound : ℕ) : Prop :=
  (∀ r, state.pOccurrences.read r≤bound) ∧ (∀ r, state.qOccurrences.read r≤bound) ∧
  (∀ r, state.lambdaOccurrences.read r≤bound) ∧ (∀ r, state.muOccurrences.read r≤bound) ∧
  (∀ r, state.pCells.read r≤bound) ∧ (∀ r, state.qCells.read r≤bound) ∧
  (∀ r, state.lambdaCells.read r≤bound) ∧ (∀ r, state.muCells.read r≤bound)

theorem initial_bounded {k : ℕ} (plan : Plan k) : Bounded (initial plan) 0 := by
  simp only [Bounded,initial,GeneralPaperEpochLevelArray.initialize_read,le_refl,implies_true,and_self]

theorem bounded_mono {k : ℕ} (state : State k) (a b : ℕ) (h : Bounded state a) (hab : a≤b) : Bounded state b := by
  rcases h with ⟨hp,hq,hl,hm,hpc,hqc,hlc,hmc⟩
  exact ⟨fun r => (hp r).trans hab,fun r => (hq r).trans hab,fun r => (hl r).trans hab,fun r => (hm r).trans hab,
    fun r => (hpc r).trans hab,fun r => (hqc r).trans hab,fun r => (hlc r).trans hab,fun r => (hmc r).trans hab⟩

structure Deltas {k : ℕ} (state : State k) where
  pOccurrences : Summary k
  qOccurrences : Summary k
  lambdaOccurrences : Summary k
  muOccurrences : Summary k
  pCells : FixedArrayTable state.plan.pCells.partition.count ℕ
  qCells : FixedArrayTable state.plan.qCells.partition.count ℕ
  lambdaCells : FixedArrayTable state.plan.lambdaCells.partition.count ℕ
  muCells : FixedArrayTable state.plan.muCells.partition.count ℕ

def Deltas.Bounded {k : ℕ} {state : State k} (delta : Deltas state) (bound : ℕ) : Prop :=
  (∀ r, delta.pOccurrences.read r≤bound) ∧ (∀ r, delta.qOccurrences.read r≤bound) ∧
  (∀ r, delta.lambdaOccurrences.read r≤bound) ∧ (∀ r, delta.muOccurrences.read r≤bound) ∧
  (∀ r, delta.pCells.read r≤bound) ∧ (∀ r, delta.qCells.read r≤bound) ∧
  (∀ r, delta.lambdaCells.read r≤bound) ∧ (∀ r, delta.muCells.read r≤bound)

def advance {k : ℕ} (state : State k) (delta : Deltas state) : State k :=
  ⟨state.plan,(GeneralPaperEpochLevelArray.advance state.pOccurrences delta.pOccurrences).1,
    (GeneralPaperEpochLevelArray.advance state.qOccurrences delta.qOccurrences).1,
    (GeneralPaperEpochLevelArray.advance state.lambdaOccurrences delta.lambdaOccurrences).1,
    (GeneralPaperEpochLevelArray.advance state.muOccurrences delta.muOccurrences).1,
    (GeneralPaperEpochLevelArray.advance state.pCells delta.pCells).1,
    (GeneralPaperEpochLevelArray.advance state.qCells delta.qCells).1,
    (GeneralPaperEpochLevelArray.advance state.lambdaCells delta.lambdaCells).1,
    (GeneralPaperEpochLevelArray.advance state.muCells delta.muCells).1⟩

theorem advance_plan {k : ℕ} (state : State k) (delta : Deltas state) : (advance state delta).plan=state.plan := rfl

theorem advance_bounded {k : ℕ} (state : State k) (delta : Deltas state) (a b : ℕ)
    (hState : Bounded state a) (hDelta : delta.Bounded b) : Bounded (advance state delta) (a+b) := by
  rcases hState with ⟨hp,hq,hl,hm,hpc,hqc,hlc,hmc⟩
  rcases hDelta with ⟨dp,dq,dl,dm,dpc,dqc,dlc,dmc⟩
  simp only [Bounded,advance,GeneralPaperEpochLevelArray.advance_read]
  exact ⟨fun r => Nat.add_le_add (hp r) (dp r),fun r => Nat.add_le_add (hq r) (dq r),
    fun r => Nat.add_le_add (hl r) (dl r),fun r => Nat.add_le_add (hm r) (dm r),
    fun r => Nat.add_le_add (hpc r) (dpc r),fun r => Nat.add_le_add (hqc r) (dqc r),
    fun r => Nat.add_le_add (hlc r) (dlc r),fun r => Nat.add_le_add (hmc r) (dmc r)⟩

end Blotto.GeneralPaperEpochFieldState
