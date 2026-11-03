import Blotto.BinaryPRGWordControllerBooleanResourceUpdate
import Blotto.BinaryPRGWordControllerPairOutputWork
import Blotto.BinaryResourcePair

/-! Pair input construction reads actual Boolean-address capacity/resource
trees. It then executes the checked Tree4 pair program. No numeric/Fin address
conversion or native resource/register array is used by this producer. The
native Certified state below is only an input to the erasure theorem. -/
namespace Blotto.BinaryPRGWordControllerBooleanResourcePair
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerBooleanResourceUpdate

def Interior {width : ℕ} {cap : FixedBinaryWord width} (capacity : Tree width) (state : State width cap) : Prop :=
  ∀ address ∈ state.active,0 < value (lookup state.resource address.word) ∧
    value (lookup state.resource address.word) < value (lookup capacity address.word)

def source {width : ℕ} {cap : FixedBinaryWord width} (capacity : Tree width) (state : State width cap)
    (first second : Address width cap) (tail : List (Address width cap))
    (hCap : ∀ address : Address width cap,CanonicalWord (lookup capacity address.word))
    (hState : ∀ address : Address width cap,CanonicalWord (lookup state.resource address.word))
    (hInterior : Interior capacity state) (he : state.active = first :: second :: tail) :
    BinaryRationalPairProgram.Source where
  lengthI := lookup capacity first.word
  lengthJ := lookup capacity second.word
  resourceI := lookup state.resource first.word
  resourceJ := lookup state.resource second.word
  lengthI_canonical := hCap first
  lengthJ_canonical := hCap second
  resourceI_canonical := hState first
  resourceJ_canonical := hState second
  interiorI := hInterior first (by simp [he])
  interiorJ := hInterior second (by simp [he])

def pair {width : ℕ} {cap : FixedBinaryWord width} (capacity : Tree width) (state : State width cap)
    (first second : Address width cap) (tail : List (Address width cap))
    (hCap : ∀ address : Address width cap,CanonicalWord (lookup capacity address.word))
    (hState : ∀ address : Address width cap,CanonicalWord (lookup state.resource address.word))
    (hInterior : Interior capacity state) (he : state.active = first :: second :: tail) :
    BinaryPRGWordControllerPairOutputs.Outputs :=
  BinaryPRGWordControllerPairOutputs.prepare (source capacity state first second tail hCap hState hInterior he)

set_option maxHeartbeats 2000000 in
theorem source_reference {width : ℕ} {cap : FixedBinaryWord width} (capacity : Tree width) (state : State width cap)
    (first second : Address width cap) (tail : List (Address width cap))
    (hCap : ∀ address : Address width cap,CanonicalWord (lookup capacity address.word))
    (hState : ∀ address : Address width cap,CanonicalWord (lookup state.resource address.word))
    (hInterior : Interior capacity state) (he : state.active = first :: second :: tail)
    (n : ℕ) (hCount : n = cap.value)
    (hC : ∀ j,CanonicalWord ((table cap capacity n hCount).read j))
    (original : BinaryResourcePair.Certified (table cap capacity n hCount))
    (hOriginal : original.state = state.reference n hCount) :
    source capacity state first second tail hCap hState hInterior he =
      BinaryResourcePair.pairSource hC original (first.index n hCount) (second.index n hCount)
        (tail.map (fun address => address.index n hCount)) (by
          rw [hOriginal]
          simp only [State.reference,he,List.map_cons]) := by
  unfold source BinaryResourcePair.pairSource
  simp only [hOriginal,State.reference,table_read]

def pairWithWork {width : ℕ} {cap : FixedBinaryWord width} (capacity : Tree width) (state : State width cap)
    (first second : Address width cap) (tail : List (Address width cap))
    (hCap : ∀ address : Address width cap,CanonicalWord (lookup capacity address.word))
    (hState : ∀ address : Address width cap,CanonicalWord (lookup state.resource address.word))
    (hInterior : Interior capacity state) (he : state.active = first :: second :: tail) :
    BinaryPRGWordControllerPairOutputs.Outputs × ℕ :=
  let input := source capacity state first second tail hCap hState hInterior he
  let outputs := BinaryPRGWordControllerPairOutputs.prepareWithWork input
  (outputs.1,lookupCells capacity first.word + lookupCells capacity second.word +
    lookupCells state.resource first.word + lookupCells state.resource second.word +
      input.sourcePayloadWork + outputs.2 + 9)

theorem pairWithWork_erasure {width : ℕ} {cap : FixedBinaryWord width} (capacity : Tree width) (state : State width cap)
    (first second : Address width cap) (tail : List (Address width cap))
    (hCap : ∀ address : Address width cap,CanonicalWord (lookup capacity address.word))
    (hState : ∀ address : Address width cap,CanonicalWord (lookup state.resource address.word))
    (hInterior : Interior capacity state) (he : state.active = first :: second :: tail) :
    (pairWithWork capacity state first second tail hCap hState hInterior he).1 =
      pair capacity state first second tail hCap hState hInterior he := by
  unfold pairWithWork pair
  dsimp only
  rw [BinaryPRGWordControllerPairOutputs.prepareWithWork_erasure]

def bound (indexWidth W : ℕ) : ℕ :=
  BinaryPRGWordControllerPairOutputWork.traceBound W + 40 * indexWidth + 24 * W + 49

theorem pairWithWork_bound {indexWidth : ℕ} {cap : FixedBinaryWord indexWidth} (capacity : Tree indexWidth)
    (state : State indexWidth cap) (first second : Address indexWidth cap) (tail : List (Address indexWidth cap))
    (hCap : ∀ address : Address indexWidth cap,CanonicalWord (lookup capacity address.word))
    (hState : ∀ address : Address indexWidth cap,CanonicalWord (lookup state.resource address.word))
    (hInterior : Interior capacity state) (he : state.active = first :: second :: tail) (W : ℕ)
    (hTrace : BinaryRationalRegisterProgram.TraceWordBounds RealPairProgram.code
      (source capacity state first second tail hCap hState hInterior he).inputs W) :
    (pairWithWork capacity state first second tail hCap hState hInterior he).2 ≤ bound indexWidth W := by
  let input := source capacity state first second tail hCap hState hInterior he
  have hData := BinaryPRGWordControllerPairOutputWork.prepare_trace_bound input W hTrace
  have hBefore := BinaryPRGWordControllerPairRegisters.trace_start _ _ W hTrace
  have h0 : width (lookup capacity first.word) ≤ W := by
    simpa [source,BinaryRationalPairProgram.Source.inputs,BinaryRationalRegisterProgram.read,Array.getD] using hBefore 0
  have h1 : width (lookup capacity second.word) ≤ W := by
    simpa [source,BinaryRationalPairProgram.Source.inputs,BinaryRationalRegisterProgram.read,Array.getD] using hBefore 1
  have h2 : width (lookup state.resource first.word) ≤ W := by
    simpa [source,BinaryRationalPairProgram.Source.inputs,BinaryRationalRegisterProgram.read,Array.getD] using hBefore 2
  have h3 : width (lookup state.resource second.word) ≤ W := by
    simpa [source,BinaryRationalPairProgram.Source.inputs,BinaryRationalRegisterProgram.read,Array.getD] using hBefore 3
  have p0 := BinaryRationalExpression.payloadWords_bound _ W h0
  have p1 := BinaryRationalExpression.payloadWords_bound _ W h1
  have p2 := BinaryRationalExpression.payloadWords_bound _ W h2
  have p3 := BinaryRationalExpression.payloadWords_bound _ W h3
  unfold pairWithWork bound
  dsimp only
  rw [lookupCells_exact,lookupCells_exact,lookupCells_exact,lookupCells_exact]
  change _ + _ + _ + _ + input.sourcePayloadWork +
    (BinaryPRGWordControllerPairOutputs.prepareWithWork input).2 + 9 ≤ _
  have hPayload : input.sourcePayloadWork = 2 * (
      BinaryRationalExpression.payloadWords (lookup capacity first.word) +
      BinaryRationalExpression.payloadWords (lookup capacity second.word) +
      BinaryRationalExpression.payloadWords (lookup state.resource first.word) +
      BinaryRationalExpression.payloadWords (lookup state.resource second.word) + 2) := rfl
  rw [hPayload]
  omega

end Blotto.BinaryPRGWordControllerBooleanResourcePair
