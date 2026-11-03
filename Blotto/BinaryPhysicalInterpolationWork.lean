import Blotto.BinaryScalarTape
import Blotto.BinaryPhysicalInterpolationRun
import Blotto.BooleanArrayIndexWork
import Blotto.BinaryPhysicalPointLifetime

/-! Measured paired-heap interpolation executes actual reads, four opcodes
and coordinate-list construction. Erasure agrees with the traced row producer;
projection, midpoint and final native packing are separate caller phases. -/
namespace Blotto.BinaryPhysicalInterpolationWork
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryWordObjectArray
set_option maxHeartbeats 4000000

def loopWithWork {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) :
    List (List Bool) → Option (List SignedWord) × ℕ
  | [] => (some [],4)
  | index::indices =>
      let p := getWithWork first index
      match p.1 with
      | none => (none,p.2+8)
      | some wordP =>
          let q := getWithWork second index
          match q.1 with
          | none => (none,p.2+q.2+8)
          | some wordQ =>
              let coordinate := BinaryPhysicalInterpolation.coordinateWithWork wordP wordQ scalar
              let later := loopWithWork first second scalar indices
              (later.1.map (fun rest => coordinate.1::rest),p.2+q.2+coordinate.2+later.2+16)

theorem loop_state {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) (indices : List (List Bool)) :
    (loopWithWork first second scalar indices).1 =
      (BinaryPhysicalInterpolationRow.loopWithTrace first second scalar indices).1 := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      rw [loopWithWork,BinaryPhysicalInterpolationRow.loopWithTrace]
      dsimp only
      rw [BinaryWordObjectArrayAccess.get_state]
      cases hp : (getWithWork first index).1 with
      | none => rfl
      | some wordP =>
          rw [BinaryWordObjectArrayAccess.get_state]
          cases hq : (getWithWork second index).1 with
          | none => rfl
          | some wordQ => simp only [BinaryPhysicalInterpolation.coordinate_work_state,ih]

theorem read_price {n : ℕ} (store : Store n) (I : ℕ) :
    BinaryWordObjectArray.readBound store I ≤ BinaryWordObjectArrayAccess.envelope store I := by
  unfold BinaryWordObjectArray.readBound BinaryWordObjectArrayAccess.envelope BinaryWordObjectArrayAccess.heapReadEnvelope
  omega

theorem coordinate_price (W : ℕ) : 44000*(9*W+5)^2+16 ≤ BinaryPhysicalInterpolation.bound W := by
  have hPow := (Nat.pow_le_pow_left (show 9*W+5 ≤ 9*W+6 by omega) 2).trans
    (Nat.pow_le_pow_right (show 0 < 9*W+6 by omega) (show 2 ≤ 3 by omega))
  unfold BinaryPhysicalInterpolation.bound BinaryQuadraticLifetime.opcodeBound BinaryQuadraticLifetime.opcodeFrames
  nlinarith

theorem loop_work {n m : ℕ} (first : Store n) (second : Store m) (p q : List SignedWord)
    (hP : first.Realizes p) (hQ : second.Realizes q) (scalar : SignedWord) (hT : BinaryRationalOpcode.Valid scalar)
    (I W : ℕ) (hW : 1 ≤ W) (ht : width scalar ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (indices : List (List Bool)) (hIndices : ∀ index ∈ indices,index.length ≤ I) :
    (loopWithWork first second scalar indices).2 ≤
      indices.length*BinaryPhysicalInterpolationRow.stepEnvelope first second I W+32 := by
  induction indices with
  | nil => simp [loopWithWork]
  | cons index indices ih =>
      have hi := hIndices index (by simp)
      have hRest := ih (fun i hm => hIndices i (by simp [hm]))
      have read_bound {r : ℕ} (store : Store r) : (getWithWork store index).2 ≤ BinaryWordObjectArrayAccess.envelope store I := by
        apply (getWithWork_bound store index).trans
        apply (show BinaryWordObjectArray.readBound store index.length ≤ BinaryWordObjectArray.readBound store I by
          unfold BinaryWordObjectArray.readBound BinaryReferenceVector.readBound; gcongr).trans (read_price store I)
      have hReadP := read_bound first
      have hReadQ := read_bound second
      rw [loopWithWork]
      dsimp only
      cases hGotP : (getWithWork first index).1 with
      | none =>
          simp only [List.length_cons]
          unfold BinaryPhysicalInterpolationRow.stepEnvelope
          nlinarith
      | some wordP =>
          cases hGotQ : (getWithWork second index).1 with
          | none =>
              simp only [List.length_cons]
              unfold BinaryPhysicalInterpolationRow.stepEnvelope
              nlinarith
          | some wordQ =>
              have hmP : wordP ∈ p := by
                rw [getWithWork_state,get_state first p hP] at hGotP
                exact getElemOption_mem _ _ _ hGotP
              have hmQ : wordQ ∈ q := by
                rw [getWithWork_state,get_state second q hQ] at hGotQ
                exact getElemOption_mem _ _ _ hGotQ
              have hc := (BinaryPhysicalInterpolation.coordinate_work wordP wordQ scalar (hp wordP hmP).1 (hq wordQ hmQ).1
                hT W hW (hp wordP hmP).2 (hq wordQ hmQ).2 ht).trans (coordinate_price W)
              simp only [List.length_cons]
              unfold BinaryPhysicalInterpolationRow.stepEnvelope at *
              nlinarith

def runWithWork (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) : List SignedWord × ℕ :=
  let first := BinaryWordObjectArrayLifetime.prepareWithWork p
  let second := BinaryWordObjectArrayLifetime.prepareWithWork q
  let indices := BooleanArrayIndexWork.enumerateWithWork p
  let row := loopWithWork first.1 second.1 scalar indices.1
  have hSome : row.1.isSome := by
    rw [loop_state,BinaryWordObjectArrayLifetime.prepareWithWork_state,BinaryWordObjectArrayLifetime.prepareWithWork_state,
      BooleanArrayIndexWork.enumerate_state,BinaryPhysicalInterpolationRow.loop_enumerate _ _ p q
        (prepare_realizes p) (prepare_realizes q) hLength scalar]
    rfl
  (row.1.get hSome,first.2+second.2+indices.2+row.2+16)

theorem run_state (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) :
    (runWithWork scalar p q hLength).1 = (BinaryPhysicalInterpolationRun.runWithTrace scalar p q hLength).1 := by
  unfold runWithWork BinaryPhysicalInterpolationRun.runWithTrace
  dsimp only
  rw [Option.get_eq_getD (fallback := []),Option.get_eq_getD (fallback := []),loop_state,
    BinaryWordObjectArrayLifetime.prepareWithWork_state,BinaryWordObjectArrayLifetime.prepareWithWork_state,
    BinaryWordObjectArrayLifetime.prepareWithTrace_state,BinaryWordObjectArrayLifetime.prepareWithTrace_state,
    BooleanArrayIndexWork.enumerate_state]

theorem preparation_price (words : List SignedWord) (W : ℕ) (hWords : ∀ word ∈ words,width word ≤ W) :
    (BinaryWordObjectArrayLifetime.prepareWithWork words).2 ≤ BinaryPhysicalOutputLifetime.preparationBound words.length W := by
  apply (BinaryWordObjectArrayLifetime.prepareWithWork_bound words).trans
  have hOld : BinaryWordObjectArrayLifetime.workEnvelope words ≤ BinaryWordObjectArrayLifetime.envelope words := by
    unfold BinaryWordObjectArrayLifetime.workEnvelope BinaryWordObjectArrayLifetime.envelope
    nlinarith
  apply hOld.trans
  have hPayload : payloadBits words ≤ BinaryPhysicalOutputLifetime.heapCap words.length W := payloadBits_bound words W hWords
  have hWidth := (BinaryPhysicalOutputLifetime.wordWidth_le (payloadBits words)).trans (Nat.add_le_add_right hPayload 1)
  unfold BinaryWordObjectArrayLifetime.envelope BinaryPRGWordStoreHeapMachine.allocationBound BinaryPhysicalOutputLifetime.preparationBound
  gcongr

theorem run_work (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length)
    (hT : BinaryRationalOpcode.Valid scalar) (W : ℕ) (hW : 1 ≤ W) (ht : width scalar ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    (runWithWork scalar p q hLength).2 ≤ BinaryPhysicalInterpolationRun.bound p.length W := by
  have hP := preparation_price p W (fun w hw => (hp w hw).2)
  have hQ' := preparation_price q W (fun w hw => (hq w hw).2)
  have hQ := hQ'.trans_eq (congrArg (fun N => BinaryPhysicalOutputLifetime.preparationBound N W) hLength.symm)
  have hIndices := BooleanArrayIndexWork.enumerate_work p
  have hWords : ∀ index ∈ (BooleanArrayIndexWork.enumerateWithWork p).1,index.length ≤ p.length+1 := by
    rw [BooleanArrayIndexWork.enumerate_state]
    intro index hi
    exact (BooleanArrayIndexEnumeration.enumerate_width p index hi).trans (BinaryPhysicalOutputLifetime.wordWidth_le p.length)
  have hLoop := loop_work (BinaryWordObjectArrayLifetime.prepareWithWork p).1
    (BinaryWordObjectArrayLifetime.prepareWithWork q).1 p q
    (by rw [BinaryWordObjectArrayLifetime.prepareWithWork_state]; exact prepare_realizes p)
    (by rw [BinaryWordObjectArrayLifetime.prepareWithWork_state]; exact prepare_realizes q)
    scalar hT (p.length+1) W hW ht hp hq (BooleanArrayIndexWork.enumerateWithWork p).1 hWords
  have hReadP := BinaryPhysicalInterpolationRun.read_bound_at p p.length W (p.length+1) (by omega) (fun w hw => (hp w hw).2) (by omega)
  have hReadQ := BinaryPhysicalInterpolationRun.read_bound_at q p.length W (p.length+1) hLength.symm.le (fun w hw => (hq w hw).2) (by omega)
  rw [BinaryWordObjectArrayLifetime.prepareWithTrace_state] at hReadP hReadQ
  have hStep : BinaryPhysicalInterpolationRow.stepEnvelope (BinaryWordObjectArrayLifetime.prepareWithWork p).1
      (BinaryWordObjectArrayLifetime.prepareWithWork q).1 (p.length+1) W ≤ BinaryPhysicalInterpolationRun.stepEnvelope p.length W := by
    rw [BinaryWordObjectArrayLifetime.prepareWithWork_state,BinaryWordObjectArrayLifetime.prepareWithWork_state]
    unfold BinaryPhysicalInterpolationRow.stepEnvelope BinaryPhysicalInterpolationRun.stepEnvelope
    omega
  have hLengthI : (BooleanArrayIndexWork.enumerateWithWork p).1.length = p.length := by
    rw [BooleanArrayIndexWork.enumerate_state]
    have h := congrArg List.length (BooleanArrayIndexEnumeration.enumerate_values p)
    simpa only [List.length_map,List.length_range] using h
  rw [hLengthI] at hLoop
  have hLoop' := hLoop.trans (Nat.add_le_add_right (Nat.mul_le_mul_left p.length hStep) 32)
  unfold runWithWork
  dsimp only
  unfold BinaryPhysicalInterpolationRun.bound
  omega

open BinaryRationalEncoding BinaryStoredOverlapEnvironment in
theorem selected_row_work {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (s : ℕ) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    (runWithWork (BinarySegmentPointLifetime.midpointWithTrace (List.ofFn bits)).1
      (table.P.read slot).data.toList (table.Q.read slot).data.toList (by
        rw [Array.length_toList,Array.length_toList,(table.P.read slot).size,(table.Q.read slot).size])).2 ≤
      BinaryPhysicalInterpolationRun.bound n (BinaryPhysicalPointLifetime.wordCap s K) := by
  let scalar := (BinarySegmentPointLifetime.midpointWithTrace (List.ofFn bits)).1
  have he : scalar = BinaryDyadicMidpoint.sample K bits := by
    simp only [scalar,BinarySegmentPointLifetime.midpointWithTrace_erases,BinaryDirectDyadicMidpoint.sample_ofFn]
  have hc : CanonicalWord scalar := by rw [he]; exact BinaryDyadicMidpoint.sample_canonical K bits
  have hh : RationalHeight (value scalar) (K+2) := by
    rw [he,BinaryDyadicMidpoint.sample_value]
    exact dyadicMidpointSample_height K bits
  have ht : width scalar ≤ BinaryPhysicalPointLifetime.wordCap s K := by
    have h := hc.2.trans (rationalWordWidth_of_height hh)
    have hm := le_max_right s (K+2)
    unfold BinaryPhysicalPointLifetime.wordCap
    omega
  have hp := BinaryPhysicalPointLifetime.table_words (table.P.read slot) s
    (BinaryPhysicalPointLifetime.wordCap s K) (hC.2.1 slot) (fun j => (hH slot j).1)
    (by unfold BinaryPhysicalPointLifetime.wordCap; have h := le_max_left s (K+2); omega)
  have hq := BinaryPhysicalPointLifetime.table_words (table.Q.read slot) s
    (BinaryPhysicalPointLifetime.wordCap s K) (hC.2.2 slot) (fun j => (hH slot j).2)
    (by unfold BinaryPhysicalPointLifetime.wordCap; have h := le_max_left s (K+2); omega)
  have h := run_work scalar (table.P.read slot).data.toList (table.Q.read slot).data.toList
    (by rw [Array.length_toList,Array.length_toList,(table.P.read slot).size,(table.Q.read slot).size]) hc.1
    (BinaryPhysicalPointLifetime.wordCap s K) (by unfold BinaryPhysicalPointLifetime.wordCap; omega) ht hp hq
  have hCount : (table.P.read slot).data.toList.length = n := by rw [Array.length_toList,(table.P.read slot).size]
  exact h.trans_eq (congrArg (fun N => BinaryPhysicalInterpolationRun.bound N (BinaryPhysicalPointLifetime.wordCap s K)) hCount)

end Blotto.BinaryPhysicalInterpolationWork
