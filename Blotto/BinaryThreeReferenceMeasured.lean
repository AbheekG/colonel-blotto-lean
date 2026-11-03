import Blotto.BinaryLifetimeArrayMeasured
import Blotto.BinaryThreeReferenceLifetime
import Blotto.BinaryUniformPairLifetime

/-! Measured borrowed-word row/table construction for exceptional three-variable
endpoints, coordinate restoration and the padded uniform pair. Each returned
callback feeds the pinned source pack once. Work is in conservative source
control/reference units; native addressing/ownership/allocator costs are separate. -/

namespace Blotto.BinaryThreeReferenceMeasured
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryExpressionCompiler
set_option autoImplicit false
set_option maxHeartbeats 3000000

def references {α : Type*} (n : ℕ) (f : Fin n → α) : (FixedArrayTable n α × Trace) × ℕ :=
  BinaryLifetimeArrayMeasured.build n (fun j => ((f j,wrap 8 1 []),4))

theorem references_data {α : Type*} (n : ℕ) (f : Fin n → α) :
    (references n f).1.1 = FixedArrayTable.ofFn f := by
  simp only [references,BinaryLifetimeArrayMeasured.build_data,BinaryLifetimeArray.build_erases]

def referenceWork (n : ℕ) : ℕ := 4*n+64*(n+1)^2
def referenceEnvelope (n : ℕ) : ℕ := 10*n+BinaryLifetimeArrayMeasured.storageReserve n+11

theorem references_work {α : Type*} (n : ℕ) (f : Fin n → α) : (references n f).2 ≤ referenceWork n := by
  simpa only [references,referenceWork,Nat.mul_comm] using
    BinaryLifetimeArrayMeasured.build_work_bound n (fun j => ((f j,wrap 8 1 []),4)) 4 (fun _ => Nat.le_refl _)

theorem references_usage {α : Type*} (n : ℕ) (f : Fin n → α) :
    usage (references n f).1.2 ≤ referenceEnvelope n := by
  have h := BinaryLifetimeArrayMeasured.build_bounds n (fun j => ((f j,wrap 8 1 []),4)) 8 1
    (by intro j; simp [BinaryPRGHeapPrimitiveLifetime.cells,wrap,combine,listCells,arraySlots])
    (by intro j; simp [wrap,combine,framePeak])
  unfold references referenceEnvelope
  omega

def rows {m : ℕ} (f : Fin 9 → Fin m → SignedWord) : (FixedArrayTable 9 (FixedArrayTable m SignedWord) × Trace) × ℕ :=
  BinaryLifetimeArrayMeasured.build 9 (fun slot => references m (f slot))

theorem rows_data {m : ℕ} (f : Fin 9 → Fin m → SignedWord) :
    (rows f).1.1 = FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (f slot)) := by
  simp only [rows,BinaryLifetimeArrayMeasured.build_data,BinaryLifetimeArray.build_erases,references_data]

def rowsWork (m : ℕ) : ℕ := 9*referenceWork m+6400
def rowsEnvelope (m : ℕ) : ℕ := 10*referenceEnvelope m+BinaryLifetimeArrayMeasured.storageReserve 9+28

theorem rows_work {m : ℕ} (f : Fin 9 → Fin m → SignedWord) : (rows f).2 ≤ rowsWork m :=
  BinaryLifetimeArrayMeasured.build_work_bound 9 _ _ (fun _ => references_work _ _)

theorem rows_usage {m : ℕ} (f : Fin 9 → Fin m → SignedWord) : usage (rows f).1.2 ≤ rowsEnvelope m := by
  have h := fun slot => references_usage m (f slot)
  have hb := BinaryLifetimeArrayMeasured.build_bounds 9 (fun slot => references m (f slot))
    (referenceEnvelope m) (referenceEnvelope m)
    (by intro slot; have hh := h slot; unfold usage at hh; omega)
    (by intro slot; have hh := h slot; unfold usage at hh; omega)
  unfold rows rowsEnvelope
  omega

def assemble {m : ℕ} (first second : Fin m → SignedWord) : (BinaryStoredOverlapEnvironment.Segment m 9 × Trace) × ℕ :=
  let weights := references 9 (fun slot => if slot = 0 then Constant.one.word else Constant.zero.word)
  let p := rows (fun _ => first)
  let q := rows (fun _ => second)
  ((⟨weights.1.1,p.1.1,q.1.1⟩,wrap 32 2 [weights.1.2,p.1.2,q.1.2]),weights.2+p.2+q.2+8)

theorem assemble_work {m : ℕ} (first second : Fin m → SignedWord) (hm : m ≤ 3) :
    (assemble first second).2 ≤ 50000 := by
  have hw := references_work 9 (fun slot => if slot = 0 then Constant.one.word else Constant.zero.word)
  have hp := rows_work (fun _ : Fin 9 => first)
  have hq := rows_work (fun _ : Fin 9 => second)
  have hmW : rowsWork m ≤ rowsWork 3 := by unfold rowsWork referenceWork; gcongr
  have hmBound : rowsWork m ≤ 15724 := hmW
  change _+_+_+8 ≤ _
  norm_num [rowsWork,referenceWork] at hw
  omega

theorem assemble_usage {m : ℕ} (first second : Fin m → SignedWord) (hm : m ≤ 3) :
    usage (assemble first second).1.2 ≤ 50000 := by
  have hw := references_usage 9 (fun slot => if slot = 0 then Constant.one.word else Constant.zero.word)
  have hp := rows_usage (fun _ : Fin 9 => first)
  have hq := rows_usage (fun _ : Fin 9 => second)
  have hmE : rowsEnvelope m ≤ rowsEnvelope 3 := by
    unfold rowsEnvelope referenceEnvelope BinaryLifetimeArrayMeasured.storageReserve
    gcongr
  have hmBound : rowsEnvelope m ≤ 9462 := hmE
  have hb := wrap_usage 32 2
    [(references 9 (fun slot => if slot = 0 then Constant.one.word else Constant.zero.word)).1.2,
      (rows (fun _ : Fin 9 => first)).1.2,(rows (fun _ : Fin 9 => second)).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hb
  change usage (wrap 32 2 [_,_,_]) ≤ _
  norm_num [rowsEnvelope,referenceEnvelope,BinaryLifetimeArrayMeasured.storageReserve] at hw
  omega

def exceptional (input : BinaryThreeInputCompiler.Input) : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ :=
  assemble ![Constant.zero.word,Constant.zero.word,input.B] ![input.a,input.d,Constant.zero.word]

theorem exceptional_data (input : BinaryThreeInputCompiler.Input) :
    (exceptional input).1.1 = (BinaryThreeReferenceLifetime.exceptionalWithTrace input).1 := by
  simp only [exceptional,assemble,references_data,rows_data,BinaryThreeReferenceLifetime.exceptionalWithTrace,
    BinaryThreeReferenceLifetime.weightsWithTrace,BinaryThreeReferenceLifetime.rowsWithTrace,
    BinaryThreeReferenceLifetime.rowWithTrace,BinaryLifetimeArray.build_erases]

theorem exceptional_work (input : BinaryThreeInputCompiler.Input) : (exceptional input).2 ≤ 50000 :=
  assemble_work _ _ (by decide)

theorem exceptional_usage (input : BinaryThreeInputCompiler.Input) : usage (exceptional input).1.2 ≤ 50000 :=
  assemble_usage _ _ (by decide)

def swap (segment : BinaryStoredOverlapEnvironment.Segment 3 9) : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ :=
  let first := rows (fun slot => ![(segment.P.read slot).read 1,(segment.P.read slot).read 0,(segment.P.read slot).read 2])
  let second := rows (fun slot => ![(segment.Q.read slot).read 1,(segment.Q.read slot).read 0,(segment.Q.read slot).read 2])
  ((⟨segment.weight,first.1.1,second.1.1⟩,wrap 32 2 [first.1.2,second.1.2]),first.2+second.2+8)

theorem swap_data (segment : BinaryStoredOverlapEnvironment.Segment 3 9) :
    (swap segment).1.1 = (BinaryThreeReferenceLifetime.swapWithTrace segment).1 := by
  simp only [swap,rows_data,BinaryThreeReferenceLifetime.swapWithTrace,BinaryThreeReferenceLifetime.swapRowsWithTrace,
    BinaryThreeReferenceLifetime.rowWithTrace,BinaryLifetimeArray.build_erases]

theorem swap_work (segment : BinaryStoredOverlapEnvironment.Segment 3 9) : (swap segment).2 ≤ 50000 := by
  have hp := rows_work (fun slot => ![(segment.P.read slot).read 1,(segment.P.read slot).read 0,(segment.P.read slot).read 2])
  have hq := rows_work (fun slot => ![(segment.Q.read slot).read 1,(segment.Q.read slot).read 0,(segment.Q.read slot).read 2])
  norm_num [rowsWork,referenceWork] at hp hq
  change _+_+8 ≤ _
  omega

theorem swap_usage (segment : BinaryStoredOverlapEnvironment.Segment 3 9) : usage (swap segment).1.2 ≤ 50000 := by
  have hp := rows_usage (fun slot => ![(segment.P.read slot).read 1,(segment.P.read slot).read 0,(segment.P.read slot).read 2])
  have hq := rows_usage (fun slot => ![(segment.Q.read slot).read 1,(segment.Q.read slot).read 0,(segment.Q.read slot).read 2])
  have hb := wrap_usage 32 2
    [(rows (fun slot => ![(segment.P.read slot).read 1,(segment.P.read slot).read 0,(segment.P.read slot).read 2])).1.2,
      (rows (fun slot => ![(segment.Q.read slot).read 1,(segment.Q.read slot).read 0,(segment.Q.read slot).read 2])).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hb
  norm_num [rowsEnvelope,referenceEnvelope,BinaryLifetimeArrayMeasured.storageReserve] at hp hq
  change usage (wrap 32 2 [_,_]) ≤ _
  omega

def uniformPair (input : BinaryGroupInputs.UniformInput 2) : (BinaryStoredOverlapEnvironment.Segment 2 9 × Trace) × ℕ :=
  assemble ![BinaryRationalOpcode.zero,input.budget] ![input.budget,BinaryRationalOpcode.zero]

theorem uniformPair_data (input : BinaryGroupInputs.UniformInput 2) :
    (uniformPair input).1.1 = (BinaryUniformPairLifetime.descriptorWithTrace input).1 := by
  simp only [uniformPair,assemble,references_data,rows_data,BinaryUniformPairLifetime.descriptorWithTrace,
    BinaryThreeReferenceLifetime.weightsWithTrace,BinaryUniformPairLifetime.rowsWithTrace,
    BinaryUniformPairLifetime.rowWithTrace,BinaryLifetimeArray.build_erases]

theorem uniformPair_work (input : BinaryGroupInputs.UniformInput 2) : (uniformPair input).2 ≤ 50000 :=
  assemble_work _ _ (by decide)

theorem uniformPair_usage (input : BinaryGroupInputs.UniformInput 2) : usage (uniformPair input).1.2 ≤ 50000 :=
  assemble_usage _ _ (by decide)

end Blotto.BinaryThreeReferenceMeasured
