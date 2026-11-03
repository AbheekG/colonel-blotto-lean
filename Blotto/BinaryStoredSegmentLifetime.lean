import Blotto.BinaryCategoricalLifetime
import Blotto.BinarySegmentPointLifetime

/-! A complete selected stored-segment draw composes concrete categorical
preparation/coin lifetimes and reached interpolation/array lifetimes. The
selected label, none case and absolute reader position are exact, and one
shared bit cap is used. Actual canonical stored weights derive a common
denominator internally; source heights derive every reservation bound.
Input/seed/table payloads remain borrowed. This is the retained Euclidean
arithmetic allocation model with a direct midpoint, not the quadratic backend.
-/
set_option autoImplicit false
namespace Blotto.BinaryStoredSegmentLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryStoredSegmentProgram BinaryStoredSegmentChoiceWork

def selectWithTrace {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k)
    (N : ℕ) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) : (Option (Fin k)×ℕ)×Trace :=
  let result := BinaryCategoricalLifetime.runWithTrace fallback N bits
    (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)) pos hp
  (result.1,[.frames (k+4),.listAllocation k,.arrayAllocation (8*k+8)] ++ under 2 result.2)

@[simp] theorem selectWithTrace_erases {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k)
    (N : ℕ) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    (selectWithTrace prepared fallback N bits pos hp).1=prepared.selectIndexed fallback N bits pos hp := by
  exact BinaryCategoricalLifetime.runWithTrace_erases fallback N bits _ pos hp

def sourceStepBound (k s : ℕ) : ℕ :=
  (k+1)*(2000000*(3+2*(1+k*s))^4+8)+2500*(2+2*(1+k*s))^3+24+
    2*(5+8*(1+k*s))+8+50*(7+8*(1+k*s))^2+32

def selectionBound (k s remaining : ℕ) : ℕ := (remaining+2*k+2)*sourceStepBound k s+9*k+8

theorem stepBound_source (D k s : ℕ) (h : binaryWordWidth D ≤ 1+k*s) :
    BinaryCategoricalLifetime.stepBound D k ≤ sourceStepBound k s := by
  unfold BinaryCategoricalLifetime.stepBound BinaryCategoricalLifetime.preparationBound
    BinaryCategoricalLifetime.sumStepBound sourceStepBound
  gcongr

theorem selectWithTrace_bounds {n k : ℕ} (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hH : ∀ slot,RationalHeight (source.weight slot) s)
    (fallback : Fin k) (N : ℕ) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    listCells (selectWithTrace prepared fallback N bits pos hp).2+
      arraySlots (selectWithTrace prepared fallback N bits pos hp).2 ≤ selectionBound k s (N-pos) ∧
    framePeak (selectWithTrace prepared fallback N bits pos hp).2 ≤ N-pos+3*k+8*(1+k*s)+25 := by
  have hWidth := denominator_width prepared.table s (fun slot => by rw [hR.1 slot]; exact hH slot)
  have hUnit := source_unit prepared source hR
  have hLength : (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative).items.length=k := List.length_ofFn
  have hCat := BinaryCategoricalLifetime.runWithTrace_bounds (denominator prepared.table)
    (denominator_positive prepared.table) k fallback N bits
    (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)) pos hp ⟨hUnit,hLength.le⟩
  have hCatFrames := framePeak_under 2 (BinaryCategoricalLifetime.runWithTrace fallback N bits
    (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)) pos hp).2
  have hStep := stepBound_source (denominator prepared.table) k s hWidth
  have hTop := Nat.mul_le_mul_left (N-pos+2*k+2) hStep
  simp only [BinaryCategoricalLifetime.potential,BinaryCategoricalRun.Cursor.rank,hLength] at hCat
  unfold selectWithTrace selectionBound
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  unfold BinaryCategoricalLifetime.localFrames at hCat
  exact ⟨by nlinarith only [hCat.1,hTop],by omega⟩

def runWithTrace {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k)
    (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    (Option (FixedArrayTable n SignedWord)×ℕ)×Trace :=
  let selected := selectWithTrace prepared fallback N bits pos hp
  match selected.1.1 with
  | none => ((none,selected.1.2),[.frames 2,.arrayAllocation 8] ++ under 2 selected.2)
  | some slot =>
      let row := BinarySegmentPointLifetime.sampleWithTrace prepared.table slot K scalar
      ((some row.1,selected.1.2),[.frames 2,.arrayAllocation 8] ++ under 2 selected.2 ++ under 2 row.2)

@[simp] theorem runWithTrace_erases {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k)
    (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    (runWithTrace prepared fallback K N scalar bits pos hp).1=prepared.runIndexed fallback K N scalar bits pos hp := by
  unfold runWithTrace Prepared.runIndexed
  dsimp only
  rw [← selectWithTrace_erases prepared fallback N bits pos hp]
  cases hs : (selectWithTrace prepared fallback N bits pos hp).1.1 <;>
    simp only [Option.map_none,Option.map_some,BinarySegmentPointLifetime.sampleWithTrace_erases]

def bound (n k s K remaining : ℕ) : ℕ := selectionBound k s remaining+BinarySegmentPointLifetime.bound n s K+8
def frames (n k s K remaining : ℕ) : ℕ := remaining+n+3*k+8*(1+k*s)+2*K+60

theorem runWithTrace_bounds {n k : ℕ} (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3≤s) (hW : ∀ slot,RationalHeight (source.weight slot) s)
    (hE : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (fallback : Fin k) (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    listCells (runWithTrace prepared fallback K N scalar bits pos hp).2+
      arraySlots (runWithTrace prepared fallback K N scalar bits pos hp).2 ≤ bound n k s K (N-pos) ∧
    framePeak (runWithTrace prepared fallback K N scalar bits pos hp).2 ≤ frames n k s K (N-pos) := by
  have hSelect := selectWithTrace_bounds prepared source hR s hW fallback N bits pos hp
  have hSelectFrames := framePeak_under 2 (selectWithTrace prepared fallback N bits pos hp).2
  have hTable : ∀ slot j,RationalHeight (value ((prepared.table.P.read slot).read j)) s ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) s := by
    intro slot j; rw [hR.2.1 slot j,hR.2.2 slot j]; exact hE slot j
  unfold runWithTrace
  dsimp only
  cases hSelected : (selectWithTrace prepared fallback N bits pos hp).1.1 with
  | none =>
      simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
      unfold bound frames
      exact ⟨by omega,by omega⟩
  | some slot =>
      have hPoint := BinarySegmentPointLifetime.sampleWithTrace_bounds prepared.table prepared.canonical s hs hTable slot K scalar
      have hPointFrames := framePeak_under 2 (BinarySegmentPointLifetime.sampleWithTrace prepared.table slot K scalar).2
      simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
      unfold bound frames
      exact ⟨by omega,by omega⟩

theorem runWithTrace_position {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k)
    (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    pos≤(runWithTrace prepared fallback K N scalar bits pos hp).1.2 ∧
    (runWithTrace prepared fallback K N scalar bits pos hp).1.2≤N := by
  rw [runWithTrace_erases]
  exact BinaryCategoricalRun.runIndexed_position fallback N bits _ pos hp

theorem run_all_prefix {n k : ℕ} (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3≤s) (hW : ∀ slot,RationalHeight (source.weight slot) s)
    (hE : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (fallback : Fin k) (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N)
    (borrowedCells steps : ℕ) :
    retainedHeap borrowedCells (runWithTrace prepared fallback K N scalar bits pos hp).2 steps ≤
      borrowedCells+bound n k s K (N-pos) := by
  have hb := (runWithTrace_bounds prepared source hR s hs hW hE fallback K N scalar bits pos hp).1
  have hl := listCells_take_le (runWithTrace prepared fallback K N scalar bits pos hp).2 steps
  have ha := arraySlots_take_le (runWithTrace prepared fallback K N scalar bits pos hp).2 steps
  unfold retainedHeap
  omega

end Blotto.BinaryStoredSegmentLifetime
