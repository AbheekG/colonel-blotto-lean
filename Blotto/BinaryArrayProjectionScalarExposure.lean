import Blotto.BinaryArrayProjectionLifetime
import Blotto.PRGNativeArrayControl

/-! Scalar operand widths on the actual descending input-array read path.
This counts bits presented to size, zero-test, subtraction and index operations;
it is not a host implementation price for those operations or for transporting
the borrowed element reference. -/
namespace Blotto.BinaryArrayProjectionScalarExposure
open Blotto.NativeArrayConversionCore

def loopWithExposure {α : Type*} (data : Array α) (acc : List α) :
    (remaining : ℕ) → remaining ≤ data.size → List α × ℕ
  | 0,_ => (acc,1+binaryWordWidth data.size)
  | remaining+1,h =>
      let index := remaining
      let later := loopWithExposure data (data[index]'(by omega)::acc) remaining (by omega)
      (later.1,later.2+8+binaryWordWidth (remaining+1)+binaryWordWidth index+
        binaryWordWidth data.size)

theorem loop_state {α : Type*} (data : Array α) (acc : List α)
    (remaining : ℕ) (h : remaining ≤ data.size) :
    (loopWithExposure data acc remaining h).1 =
      (BinaryArrayProjectionLifetime.loopWithTrace data acc remaining h).1 := by
  induction remaining generalizing acc with
  | zero => rfl
  | succ remaining ih => exact ih (data[remaining]'(by omega)::acc) (by omega)

theorem loop_bound {α : Type*} (data : Array α) (acc : List α)
    (remaining : ℕ) (h : remaining ≤ data.size) :
    (loopWithExposure data acc remaining h).2 ≤
      (remaining+1)*(8+3*binaryWordWidth (data.size+1)) := by
  induction remaining generalizing acc with
  | zero =>
      have hw := binaryWordWidth_mono (show data.size ≤ data.size+1 by omega)
      simp only [loopWithExposure,Nat.zero_add,one_mul]
      omega
  | succ remaining ih =>
      let W := binaryWordWidth (data.size+1)
      have hLater := ih (data[remaining]'(by omega)::acc) (by omega)
      have hRemaining : binaryWordWidth (remaining+1) ≤ W :=
        binaryWordWidth_mono (by omega)
      have hIndex : binaryWordWidth remaining ≤ W :=
        binaryWordWidth_mono (by omega)
      have hSize : binaryWordWidth data.size ≤ W :=
        binaryWordWidth_mono (by omega)
      simp only [loopWithExposure]
      change (loopWithExposure data (data[remaining]'(by omega)::acc) remaining (by omega)).2 ≤
        (remaining+1)*(8+3*W) at hLater
      calc
        _ ≤ (remaining+1)*(8+3*W)+(8+3*W) := by omega
        _ = (remaining+1+1)*(8+3*W) := by ring

def readWithExposure {α : Type*} (data : Array α) : List α × ℕ :=
  loopWithExposure data [] data.size (Nat.le_refl _)

theorem read_state {α : Type*} (data : Array α) :
    (readWithExposure data).1 = (BinaryArrayProjectionLifetime.readWithTrace data).1 :=
  loop_state data [] _ _

theorem read_bound {α : Type*} (data : Array α) :
    (readWithExposure data).2 ≤
      (data.size+1)*(8+3*binaryWordWidth (data.size+1)) :=
  loop_bound data [] _ _

theorem raw_values_bound (frame : List Bool) (parsed : Blotto.PRGNativeArrayControl.Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    (readWithExposure parsed.1.2.request.prepared.original.values.data).2 ≤
      (frame.length+1)*(8+3*binaryWordWidth (frame.length+1)) := by
  have hn := PRGNativeArrayControl.dimension_bound frame parsed hRead
  have h := read_bound parsed.1.2.request.prepared.original.values.data
  rw [parsed.1.2.request.prepared.original.values.size] at h
  have hw := binaryWordWidth_mono (Nat.add_le_add_right hn 1)
  exact h.trans (Nat.mul_le_mul (by omega) (by omega))

end Blotto.BinaryArrayProjectionScalarExposure
