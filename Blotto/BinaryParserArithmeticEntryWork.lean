import Blotto.BinaryPreparationArithmeticEntryWork
import Blotto.BinaryPromiseOpcodeRequest

/-! Concrete post-parse preparation entry charges survive parser failure,
accuracy rejection and the four single-player request routes. The original
frame supplies an unconditional polynomial ceiling. This is the preparation
entry class, not all sampled arithmetic or a complete native runtime model. -/
namespace Blotto.BinaryParserArithmeticEntryWork
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryTracePlanMeasured BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 6000000

def checkedGame (frame : List Bool) : ℕ :=
  match (BinaryCanonicalNormalizationParser.game frame).1.1.1.1.1.1.1 with
  | none => 0
  | some parsed => BinaryPreparationArithmeticEntryWork.checked parsed.1.2.game.input parsed.1.2.rows

theorem checked_bound (frame : List Bool) :
    checkedGame frame ≤ 2*listCells (BinaryPromiseOpcodeParser.checkedGame frame).1.1.1.1.1.1.1.1.2 := by
  simp only [checkedGame,BinaryPromiseOpcodeParser.checkedGame]
  split
  · simp only [wrap,combine,listCells_append,listCells_under,listCells]; omega
  · rename_i parsed hs
    have h := BinaryPreparationArithmeticEntryWork.checked_bound parsed.1.2.game.input parsed.1.2.game.canonical
      parsed.1.2.rows parsed.1.2.rows_readback
    simp only [hs,wrap,combine,listCells_append,listCells_under,listCells]
    omega

theorem read_bound (frame : List Bool) :
    checkedGame frame ≤ 2*listCells (BinaryPromiseOpcodeParser.read frame).1.1.1.2 := by
  have h := checked_bound frame
  simp only [BinaryPromiseOpcodeParser.read]
  split
  · simp only [wrap,combine,listCells_append,listCells_under,listCells]; omega
  · split <;> simp only [wrap,combine,listCells_append,listCells_under,listCells] <;> omega

theorem uniform : ∃ C d : ℕ,∀ frame : List Bool,checkedGame frame ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSource⟩ := BinaryPRGPhysicalRawRequestMeasured.uniform_joint
  refine ⟨2*C,d,?_⟩
  intro frame
  have h := read_bound frame
  rw [BinaryPromiseOpcodeParser.read_previous] at h
  have hs := hSource frame
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells] at hs
  simp only [Nat.mul_assoc]
  omega

theorem uniform_width : ∃ C d : ℕ,∀ frame : List Bool,
    binaryWordWidth (checkedGame frame) ≤ binaryWordWidth (C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := uniform
  exact ⟨C,d,fun frame => binaryWordWidth_mono (h frame)⟩

theorem pair_preparation_uniform : ∃ C d : ℕ,∀ frame : List Bool,
    checkedGame frame+checkedGame frame ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := uniform
  refine ⟨2*C,d,?_⟩
  intro frame
  have hs := h frame
  simp only [Nat.mul_assoc]
  omega

theorem raw_bound (rich : Bool) (frame bits : List Bool) :
    checkedGame frame ≤ 2*listCells (BinaryPromiseOpcodeRequest.raw rich frame bits).1.1.1.2 := by
  have h := read_bound frame
  simp only [BinaryPromiseOpcodeRequest.raw_record,BinaryRawParserContinuation.raw_record,BinaryPromiseOpcodeRequest.backend]
  split
  · simp only [BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]; omega
  · split <;> simp only [BinaryWrapperEmission.one_trace,BinaryWrapperEmission.two_trace,
      BinarySeedWrapperEmission.three_trace,wrap,combine,listCells_append,listCells_under,listCells] <;> omega

theorem parsedRaw_bound (rich : Bool) (frame bits : List Bool) :
    checkedGame frame ≤ 2*listCells (BinaryPromiseOpcodeRequest.parsedRaw rich frame bits).1.1.1.2 := by
  have h := read_bound frame
  simp only [BinaryPromiseOpcodeRequest.parsedRaw_record,BinaryRawParserContinuation.parsedRaw_record,BinaryPromiseOpcodeRequest.backend]
  split
  · simp only [BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]; omega
  · split <;> simp only [BinaryWrapperEmission.one_trace,BinaryWrapperEmission.two_trace,
      BinarySeedWrapperEmission.three_trace,wrap,combine,listCells_append,listCells_under,listCells] <;> omega

theorem generated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    checkedGame frame ≤ 2*listCells (BinaryPromiseOpcodeRequest.generated next rich frame state).1.1.1.2 := by
  have h := read_bound frame
  simp only [BinaryPromiseOpcodeRequest.generated_record,BinaryRawParserContinuation.generated_record,BinaryPromiseOpcodeRequest.backend]
  split
  · simp only [BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]; omega
  · split <;> simp only [BinaryWrapperEmission.one_trace,BinaryWrapperEmission.two_trace,
      BinarySeedWrapperEmission.three_trace,wrap,combine,listCells_append,listCells_under,listCells] <;> omega

theorem parsedGenerated_bound {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    checkedGame frame ≤ 2*listCells (BinaryPromiseOpcodeRequest.parsedGenerated next rich frame state).1.1.1.2 := by
  have h := read_bound frame
  simp only [BinaryPromiseOpcodeRequest.parsedGenerated_record,BinaryRawParserContinuation.parsedGenerated_record,BinaryPromiseOpcodeRequest.backend]
  split
  · simp only [BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]; omega
  · split <;> simp only [BinaryWrapperEmission.one_trace,BinaryWrapperEmission.two_trace,
      BinarySeedWrapperEmission.three_trace,wrap,combine,listCells_append,listCells_under,listCells] <;> omega

theorem pair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    checkedGame frame+checkedGame frame ≤
      2*listCells (BinaryPromiseOpcodeRequest.pair next frame state).1.1.1.2 := by
  let rich := (BinaryPromiseOpcodeRequest.generated next true frame state).1
  have hr := generated_bound next true frame state
  have hp := generated_bound next false frame rich.1.1.1.1.2
  simp only [rich,BinaryPromiseOpcodeRequest.generated_record] at hr hp
  simp only [BinaryPromiseOpcodeRequest.pair_record,BinaryRawParserContinuation.pair_record,
    BinaryWrapperEmission.two_trace,wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem parsedPair_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    checkedGame frame+checkedGame frame ≤
      2*listCells (BinaryPromiseOpcodeRequest.parsedPair next frame state).1.1.1.2 := by
  let rich := (BinaryPromiseOpcodeRequest.parsedGenerated next true frame state).1
  have hr := parsedGenerated_bound next true frame state
  have hp := parsedGenerated_bound next false frame rich.1.1.1.1.2
  simp only [rich,BinaryPromiseOpcodeRequest.parsedGenerated_record] at hr hp
  simp only [BinaryPromiseOpcodeRequest.parsedPair_record,BinaryRawParserContinuation.parsedPair_record,
    BinaryWrapperEmission.two_trace,wrap,combine,listCells_append,listCells_under,listCells]
  omega

end Blotto.BinaryParserArithmeticEntryWork
