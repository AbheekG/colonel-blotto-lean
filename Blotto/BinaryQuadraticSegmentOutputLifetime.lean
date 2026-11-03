import Blotto.BinaryScalarTape
import Blotto.BinaryQuadraticCategoricalLifetime
import Blotto.BinaryQuadraticPointOutputLifetime
import Blotto.BinaryStoredSegmentLifetime

/-! Actual quadratic categorical selection flows into one selected midpoint,
coordinate array, original-budget scaling and Boolean frame. Failed selection
returns none with its exact absolute reader position. Source weights derive
the common-lattice width; endpoints derive every point/output reservation.
All produced regions remain retained. Borrowed table/input/seed are explicit.
The enclosing factory is composed in the regular-three caller. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticSegmentOutputLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryStoredSegmentProgram BinaryStoredSegmentChoiceWork

def selectWithTrace {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k)
    (N : ℕ) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) : (Option (Fin k)×ℕ)×Trace :=
  let result := BinaryQuadraticCategoricalLifetime.runWithTrace fallback N bits
    (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)) pos hp
  (result.1,[.frames (k+4),.listAllocation k,.arrayAllocation (8*k+8)] ++ under 2 result.2)

@[simp] theorem selectWithTrace_erases {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k)
    (N : ℕ) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    (selectWithTrace prepared fallback N bits pos hp).1=prepared.selectIndexed fallback N bits pos hp := by
  exact BinaryQuadraticCategoricalLifetime.runWithTrace_erases fallback N bits _ pos hp

def sourceStepBound (k s : ℕ) : ℕ :=
  let W := 1+k*s
  (k+1)*(BinaryQuadraticLifetime.opcodeBound (1+2*W)+8)+2500*(2+2*W)^3+32+
    2*(5+8*W)+8+50*(7+8*W)^2+32

def sourceArithmeticFrames (k s : ℕ) : ℕ :=
  let W := 1+k*s
  BinaryQuadraticLifetime.opcodeFrames (1+2*W)+150*(2+2*W)^2+32

def selectionBound (k s remaining : ℕ) : ℕ := (remaining+2*k+2)*sourceStepBound k s+9*k+8
def selectionFrames (k s remaining : ℕ) : ℕ := remaining+3*k+sourceArithmeticFrames k s+8*(1+k*s)+35

theorem stepBound_source (D k s : ℕ) (h : binaryWordWidth D ≤ 1+k*s) :
    BinaryQuadraticCategoricalLifetime.stepBound D k ≤ sourceStepBound k s := by
  simp only [sourceStepBound] 
  unfold BinaryQuadraticCategoricalLifetime.stepBound BinaryQuadraticCategoricalLifetime.preparationBound
    BinaryQuadraticCategoricalLifetime.sumStepBound BinaryQuadraticCategoricalLifetime.operandWidth
    BinaryQuadraticLifetime.opcodeBound
  gcongr

theorem arithmeticFrames_source (D k s : ℕ) (h : binaryWordWidth D ≤ 1+k*s) :
    BinaryQuadraticCategoricalLifetime.arithmeticFrames D ≤ sourceArithmeticFrames k s := by
  simp only [sourceArithmeticFrames]
  unfold BinaryQuadraticCategoricalLifetime.arithmeticFrames BinaryQuadraticCategoricalLifetime.operandWidth
    BinaryQuadraticLifetime.opcodeFrames
  gcongr

theorem selectWithTrace_bounds {n k : ℕ} (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hH : ∀ slot,RationalHeight (source.weight slot) s)
    (fallback : Fin k) (N : ℕ) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    listCells (selectWithTrace prepared fallback N bits pos hp).2+
      arraySlots (selectWithTrace prepared fallback N bits pos hp).2 ≤ selectionBound k s (N-pos) ∧
    framePeak (selectWithTrace prepared fallback N bits pos hp).2 ≤ selectionFrames k s (N-pos) := by
  have hWidth := denominator_width prepared.table s (fun slot => by rw [hR.1 slot]; exact hH slot)
  have hUnit := source_unit prepared source hR
  have hLength : (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative).items.length=k := List.length_ofFn
  have hCat := BinaryQuadraticCategoricalLifetime.runWithTrace_bounds (denominator prepared.table)
    (denominator_positive prepared.table) k fallback N bits
    (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)) pos hp ⟨hUnit,hLength.le⟩
  have hCatFrames := framePeak_under 2 (BinaryQuadraticCategoricalLifetime.runWithTrace fallback N bits
    (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)) pos hp).2
  have hAF := arithmeticFrames_source (denominator prepared.table) k s hWidth
  have hStep := stepBound_source (denominator prepared.table) k s hWidth
  have hTop := Nat.mul_le_mul_left (N-pos+2*k+2) hStep
  simp only [BinaryQuadraticCategoricalLifetime.potential,BinaryCategoricalRun.Cursor.rank,hLength] at hCat
  unfold selectWithTrace selectionBound selectionFrames
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  unfold BinaryQuadraticCategoricalLifetime.localFrames at hCat
  exact ⟨by nlinarith only [hCat.1,hTop],by omega⟩

def runWithTrace {n k : ℕ} (budget : SignedWord) (header : List Bool) (prepared : Prepared n k) (fallback : Fin k)
    (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    (Option (List Bool)×ℕ)×Trace :=
  let selected := selectWithTrace prepared fallback N bits pos hp
  match selected.1.1 with
  | none => ((none,selected.1.2),[.frames 2,.arrayAllocation 8] ++ under 2 selected.2)
  | some slot =>
      let framed := BinaryQuadraticPointOutputLifetime.runWithTrace budget header prepared.table slot K scalar
      ((some framed.1,selected.1.2),[.frames 2,.arrayAllocation 8] ++ under 2 selected.2 ++ under 2 framed.2)

def reference {n k : ℕ} (budget : SignedWord) (header : List Bool) (prepared : Prepared n k) (fallback : Fin k)
    (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) : Option (List Bool)×ℕ :=
  let drawn := prepared.runIndexed fallback K N scalar bits pos hp
  (drawn.1.map (fun row => header++BinaryStoredRowFrame.words
    (List.ofFn (BinaryPRGOriginalSampler.rescale budget row).read)),drawn.2)

@[simp] theorem runWithTrace_erases {n k : ℕ} (budget : SignedWord) (header : List Bool)
    (hB : BinaryRationalOpcode.Valid budget) (prepared : Prepared n k) (fallback : Fin k)
    (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    (runWithTrace budget header prepared fallback K N scalar bits pos hp).1=
      reference budget header prepared fallback K N scalar bits pos hp := by
  unfold runWithTrace reference Prepared.runIndexed
  dsimp only
  rw [← selectWithTrace_erases prepared fallback N bits pos hp]
  cases hs : (selectWithTrace prepared fallback N bits pos hp).1.1 with
  | none => rfl
  | some slot =>
      simp only [Option.map_some,BinaryQuadraticPointOutputLifetime.runWithTrace_erases]
      have he : BinaryPRGWordControllerSegment.point prepared.table slot K scalar=
        BinarySegmentPoint.sample prepared.table slot K scalar :=
        (BinaryQuadraticPointLifetime.pointData_controller _ _ _ _).symm.trans
          (BinaryQuadraticPointLifetime.pointData_state _ prepared.canonical _ _ _)
      rw [he]
      unfold BinaryQuadraticOutputLifetime.outputData
      rw [BinaryQuadraticOutputLifetime.scaleData_state budget _ hB
        (fun j => (BinarySegmentPoint.sample_canonical prepared.table slot K scalar prepared.canonical j).1)]

def bound (n k s K remaining W headerLength : ℕ) : ℕ := selectionBound k s remaining+
  BinaryQuadraticPointOutputLifetime.bound n s K W headerLength+8

def frames (n k s K remaining W headerLength : ℕ) : ℕ := selectionFrames k s remaining+
  BinaryQuadraticPointOutputLifetime.frames n s K W headerLength+4

theorem runWithTrace_bounds {n k : ℕ} (budget : SignedWord) (header : List Bool)
    (hB : BinaryRationalOpcode.Valid budget) (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3≤s) (hW : ∀ slot,RationalHeight (source.weight slot) s)
    (hE : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (fallback : Fin k) (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    listCells (runWithTrace budget header prepared fallback K N scalar bits pos hp).2+
      arraySlots (runWithTrace budget header prepared fallback K N scalar bits pos hp).2≤
        bound n k s K (N-pos) (BinaryQuadraticPointOutputLifetime.widthBound budget s K) header.length ∧
    framePeak (runWithTrace budget header prepared fallback K N scalar bits pos hp).2≤
      frames n k s K (N-pos) (BinaryQuadraticPointOutputLifetime.widthBound budget s K) header.length := by
  have hSelect := selectWithTrace_bounds prepared source hR s hW fallback N bits pos hp
  have hSelectF := framePeak_under 2 (selectWithTrace prepared fallback N bits pos hp).2
  have hEndpoint : ∀ slot j,RationalHeight (value ((prepared.table.P.read slot).read j)) s ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) s := by
    intro slot j; rw [hR.2.1 slot j,hR.2.2 slot j]; exact hE slot j
  unfold runWithTrace
  dsimp only
  cases hChosen : (selectWithTrace prepared fallback N bits pos hp).1.1 with
  | none =>
      simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
      unfold bound frames
      exact ⟨by omega,by omega⟩
  | some slot =>
      have hOut := BinaryQuadraticPointOutputLifetime.runWithTrace_bounds budget header prepared.table hB prepared.canonical
        s hs hEndpoint slot K scalar
      have hOutF := framePeak_under 2 (BinaryQuadraticPointOutputLifetime.runWithTrace budget header prepared.table slot K scalar).2
      simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
      unfold bound frames
      exact ⟨by omega,by omega⟩

theorem runWithTrace_position {n k : ℕ} (budget : SignedWord) (header : List Bool) (prepared : Prepared n k) (fallback : Fin k)
    (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    pos≤(runWithTrace budget header prepared fallback K N scalar bits pos hp).1.2 ∧
    (runWithTrace budget header prepared fallback K N scalar bits pos hp).1.2≤N := by
  have h := BinaryCategoricalRun.runIndexed_position fallback N bits
    (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)) pos hp
  unfold runWithTrace
  dsimp only
  change pos≤(prepared.selectIndexed fallback N bits pos hp).2 ∧
    (prepared.selectIndexed fallback N bits pos hp).2≤N at h
  rw [← selectWithTrace_erases prepared fallback N bits pos hp] at h
  cases (selectWithTrace prepared fallback N bits pos hp).1.1 <;> exact h

theorem all_prefix_heap {n k : ℕ} (budget : SignedWord) (header : List Bool)
    (hB : BinaryRationalOpcode.Valid budget) (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3≤s) (hW : ∀ slot,RationalHeight (source.weight slot) s)
    (hE : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (fallback : Fin k) (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N)
    (borrowedInputCells originalSeedCells steps : ℕ) :
    retainedHeap (BinaryRationalOpcodeAllocation.payload budget+header.length+
      BinaryQuadraticPointLifetime.tableCells prepared.table+borrowedInputCells+originalSeedCells)
      (runWithTrace budget header prepared fallback K N scalar bits pos hp).2 steps≤
      BinaryRationalOpcodeAllocation.payload budget+header.length+BinaryQuadraticPointLifetime.tableCells prepared.table+
      borrowedInputCells+originalSeedCells+
      bound n k s K (N-pos) (BinaryQuadraticPointOutputLifetime.widthBound budget s K) header.length :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _
    (runWithTrace_bounds budget header hB prepared source hR s hs hW hE fallback K N scalar bits pos hp).1

theorem all_prefix_frames {n k : ℕ} (budget : SignedWord) (header : List Bool)
    (hB : BinaryRationalOpcode.Valid budget) (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3≤s) (hW : ∀ slot,RationalHeight (source.weight slot) s)
    (hE : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (fallback : Fin k) (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) (steps : ℕ) :
    framePeak ((runWithTrace budget header prepared fallback K N scalar bits pos hp).2.take steps)≤
      frames n k s K (N-pos) (BinaryQuadraticPointOutputLifetime.widthBound budget s K) header.length :=
  (framePeak_take_le _ _).trans
    (runWithTrace_bounds budget header hB prepared source hR s hs hW hE fallback K N scalar bits pos hp).2

end Blotto.BinaryQuadraticSegmentOutputLifetime
