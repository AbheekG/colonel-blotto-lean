import Blotto.BinaryPhysicalInterpolation
import Blotto.BinaryWordObjectArrayAccess
import Blotto.BinaryWordObjectArrayLifetime
import Blotto.BooleanArrayIndexEnumeration

/-! A selected endpoint pair is read from actual physical heaps at Boolean
indices. Every reached word is passed once to the direct affine opcodes.
Logical paired gathering is erased evidence, not a producer or callback. -/
namespace Blotto.BinaryPhysicalInterpolationRow
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryWordObjectArray
set_option maxHeartbeats 4000000

def pairRead {n m : ℕ} (first : Store n) (second : Store m) (index : List Bool) : Option (SignedWord × SignedWord) :=
  (get first index).bind (fun p => (get second index).map (fun q => (p,q)))

def coordinateData (scalar : SignedWord) (pair : SignedWord × SignedWord) : SignedWord :=
  BinaryQuadraticData.expression (BinarySegmentPoint.environment pair.1 pair.2 scalar) BinarySegmentPoint.program.compile

def loopWithTrace {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) :
    List (List Bool) → Option (List SignedWord) × Trace
  | [] => (some [],wrap 16 1 [])
  | index::indices =>
      let p := BinaryWordObjectArrayAccess.getWithTrace first index
      match p.1 with
      | none => (none,wrap 24 2 [p.2])
      | some wordP =>
          let q := BinaryWordObjectArrayAccess.getWithTrace second index
          match q.1 with
          | none => (none,wrap 32 2 [p.2,q.2])
          | some wordQ =>
              let coordinate := BinaryPhysicalInterpolation.coordinateWithTrace wordP wordQ scalar
              let later := loopWithTrace first second scalar indices
              (later.1.map (fun rest => coordinate.1::rest),wrapList 1 64 2 [p.2,q.2,coordinate.2,later.2])

theorem loop_state {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) (indices : List (List Bool)) :
    (loopWithTrace first second scalar indices).1 =
      (indices.mapM (pairRead first second)).map (List.map (coordinateData scalar)) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      rw [loopWithTrace]
      dsimp only
      rw [BinaryWordObjectArrayAccess.get_state,getWithWork_state]
      cases hp : get first index with
      | none => simp [List.mapM_cons,pairRead,hp]
      | some p =>
          rw [BinaryWordObjectArrayAccess.get_state,getWithWork_state]
          cases hq : get second index with
          | none => simp [List.mapM_cons,pairRead,hp,hq]
          | some q =>
              rw [ih]
              cases hl : indices.mapM (pairRead first second) with
              | none => simp [List.mapM_cons,pairRead,hp,hq,hl]
              | some pairs => simp [List.mapM_cons,pairRead,hp,hq,hl,coordinateData,BinaryPhysicalInterpolation.coordinate_state]

theorem gather_pairs_range (first second : List SignedWord) (hLength : first.length = second.length) :
    ((List.range first.length).mapM (fun i => first[i]?.bind (fun p => second[i]?.map (fun q => (p,q))))) =
      some (first.zip second) := by
  induction first generalizing second with
  | nil => have hs : second = [] := List.length_eq_zero_iff.mp hLength.symm; subst second; rfl
  | cons p first ih =>
      cases second with
      | nil => simp only [List.length_cons,List.length_nil] at hLength; omega
      | cons q second =>
          have hr : first.length = second.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hLength
          simp only [List.length_cons,List.range_succ_eq_map,List.mapM_cons,List.getElem?_cons_zero,
            List.mapM_map,Function.comp_def,List.getElem?_cons_succ,ih second hr,List.zip_cons_cons]
          rfl

theorem gather_enumerate {n m : ℕ} (first : Store n) (second : Store m) (p q : List SignedWord)
    (hP : first.Realizes p) (hQ : second.Realizes q) (hLength : p.length = q.length) :
    ((BooleanArrayIndexEnumeration.enumerateWithTrace p).1.mapM (pairRead first second)) = some (p.zip q) := by
  have hPair : pairRead first second = fun index => p[BinaryCarryCounter.value index]?.bind
      (fun x => q[BinaryCarryCounter.value index]?.map (fun y => (x,y))) := by
    funext index
    simp only [pairRead,get_state first p hP,get_state second q hQ]
    rfl
  rw [hPair]
  change List.mapM ((fun i => p[i]?.bind (fun x => q[i]?.map (fun y => (x,y)))) ∘ BinaryCarryCounter.value)
    (BooleanArrayIndexEnumeration.enumerateWithTrace p).1 = some (p.zip q)
  rw [← List.mapM_map,BooleanArrayIndexEnumeration.enumerate_values]
  exact gather_pairs_range p q hLength

theorem loop_enumerate {n m : ℕ} (first : Store n) (second : Store m) (p q : List SignedWord)
    (hP : first.Realizes p) (hQ : second.Realizes q) (hLength : p.length = q.length) (scalar : SignedWord) :
    (loopWithTrace first second scalar (BooleanArrayIndexEnumeration.enumerateWithTrace p).1).1 =
      some ((p.zip q).map (coordinateData scalar)) := by
  rw [loop_state,gather_enumerate first second p q hP hQ hLength]
  rfl

def stepEnvelope {n m : ℕ} (first : Store n) (second : Store m) (I W : ℕ) : ℕ :=
  BinaryWordObjectArrayAccess.envelope first I+BinaryWordObjectArrayAccess.envelope second I+
    BinaryPhysicalInterpolation.bound W+256

theorem loop_usage {n m : ℕ} (first : Store n) (second : Store m) (p q : List SignedWord)
    (hP : first.Realizes p) (hQ : second.Realizes q) (scalar : SignedWord) (hT : BinaryRationalOpcode.Valid scalar)
    (I W : ℕ) (hW : 1 ≤ W) (ht : width scalar ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (indices : List (List Bool)) (hIndices : ∀ index ∈ indices,index.length ≤ I) :
    usage (loopWithTrace first second scalar indices).2 ≤ indices.length*stepEnvelope first second I W+32 := by
  induction indices with
  | nil => exact (wrap_usage 16 1 []).trans (by simp)
  | cons index indices ih =>
      have hi := hIndices index (by simp)
      have hRest := ih (fun i hm => hIndices i (by simp [hm]))
      have hReadP : usage (BinaryWordObjectArrayAccess.getWithTrace first index).2 ≤ BinaryWordObjectArrayAccess.envelope first I := by
        apply (BinaryWordObjectArrayAccess.get_usage first index).trans
        unfold BinaryWordObjectArrayAccess.envelope BinaryReferenceVector.readBound
        gcongr
      have hReadQ : usage (BinaryWordObjectArrayAccess.getWithTrace second index).2 ≤ BinaryWordObjectArrayAccess.envelope second I := by
        apply (BinaryWordObjectArrayAccess.get_usage second index).trans
        unfold BinaryWordObjectArrayAccess.envelope BinaryReferenceVector.readBound
        gcongr
      rw [loopWithTrace]
      dsimp only
      cases hGotP : (BinaryWordObjectArrayAccess.getWithTrace first index).1 with
      | none =>
          have hw := wrap_usage 24 2 [(BinaryWordObjectArrayAccess.getWithTrace first index).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          simp only [List.length_cons]
          unfold stepEnvelope
          nlinarith
      | some wordP =>
          cases hGotQ : (BinaryWordObjectArrayAccess.getWithTrace second index).1 with
          | none =>
              have hw := wrap_usage 32 2 [(BinaryWordObjectArrayAccess.getWithTrace first index).2,
                (BinaryWordObjectArrayAccess.getWithTrace second index).2]
              simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
              simp only [List.length_cons]
              unfold stepEnvelope
              nlinarith
          | some wordQ =>
              have hmP : wordP ∈ p := by
                rw [BinaryWordObjectArrayAccess.get_realizes first p hP] at hGotP
                exact getElemOption_mem _ _ _ hGotP
              have hmQ : wordQ ∈ q := by
                rw [BinaryWordObjectArrayAccess.get_realizes second q hQ] at hGotQ
                exact getElemOption_mem _ _ _ hGotQ
              have hc := BinaryPhysicalInterpolation.coordinate_usage wordP wordQ scalar (hp wordP hmP).1 (hq wordQ hmQ).1
                hT W hW (hp wordP hmP).2 (hq wordQ hmQ).2 ht
              have hw := wrapList_usage 1 64 2 [(BinaryWordObjectArrayAccess.getWithTrace first index).2,
                (BinaryWordObjectArrayAccess.getWithTrace second index).2,
                (BinaryPhysicalInterpolation.coordinateWithTrace wordP wordQ scalar).2,
                (loopWithTrace first second scalar indices).2]
              simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
              simp only [List.length_cons]
              unfold stepEnvelope at *
              nlinarith

end Blotto.BinaryPhysicalInterpolationRow
