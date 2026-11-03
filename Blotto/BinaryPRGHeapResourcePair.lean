import Blotto.BinaryPRGHeapStoredTree
import Blotto.BinaryPRGWordControllerBooleanResourceLoop
import Blotto.BinaryGeneralResourceLattice

/-! The reached resource pair program consumes four actual tape-heap reads.
The logical capacity/state appear only in type indices and erased proofs;
operands and quadratic Boolean register outputs come from the physical data.
Input payload copying and this register backend keep their own source prices.
Whole resource-loop/controller/space joins remain separate. -/

namespace Blotto.BinaryPRGHeapResourcePair
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Tree lookup)
open BinaryPRGWordControllerBooleanResourceUpdate
open BinaryPRGWordControllerBooleanResourcePair (Interior source pair)
open BinaryPRGHeapStoredTree (Stored)

variable {depth : ℕ} {cap : FixedBinaryWord depth} {capacity : Tree depth} {state : State depth cap}

def sourceWithWork (limits : Stored capacity) (bids : Stored state.resource)
    (first second : Address depth cap) (tail : List (Address depth cap))
    (hCap : ∀ address : Address depth cap,CanonicalWord (lookup capacity address.word))
    (hState : ∀ address : Address depth cap,CanonicalWord (lookup state.resource address.word))
    (hInterior : Interior capacity state) (he : state.active = first :: second :: tail) :
    BinaryRationalPairProgram.Source × ℕ :=
  let a := BinaryPRGHeapStoredTree.readWithWork limits first.word
  let b := BinaryPRGHeapStoredTree.readWithWork limits second.word
  let c := BinaryPRGHeapStoredTree.readWithWork bids first.word
  let d := BinaryPRGHeapStoredTree.readWithWork bids second.word
  (⟨a.1,b.1,c.1,d.1,
    (by simpa only [a,BinaryPRGHeapStoredTree.readWithWork_value] using hCap first),
    (by simpa only [b,BinaryPRGHeapStoredTree.readWithWork_value] using hCap second),
    (by simpa only [c,BinaryPRGHeapStoredTree.readWithWork_value] using hState first),
    (by simpa only [d,BinaryPRGHeapStoredTree.readWithWork_value] using hState second),
    (by simpa only [c,a,BinaryPRGHeapStoredTree.readWithWork_value] using hInterior first (by simp [he])),
    (by simpa only [d,b,BinaryPRGHeapStoredTree.readWithWork_value] using hInterior second (by simp [he]))⟩,
    a.2.work + b.2.work + c.2.work + d.2.work + 8)

theorem sourceWithWork_value (limits : Stored capacity) (bids : Stored state.resource)
    (first second : Address depth cap) (tail : List (Address depth cap))
    (hCap : ∀ address : Address depth cap,CanonicalWord (lookup capacity address.word))
    (hState : ∀ address : Address depth cap,CanonicalWord (lookup state.resource address.word))
    (hInterior : Interior capacity state) (he : state.active = first :: second :: tail) :
    (sourceWithWork limits bids first second tail hCap hState hInterior he).1 =
      source capacity state first second tail hCap hState hInterior he := by
  unfold sourceWithWork source
  dsimp only
  simp only [BinaryPRGHeapStoredTree.readWithWork_value]

theorem sourceWithWork_bound (limits : Stored capacity) (bids : Stored state.resource)
    (first second : Address depth cap) (tail : List (Address depth cap))
    (hCap : ∀ address : Address depth cap,CanonicalWord (lookup capacity address.word))
    (hState : ∀ address : Address depth cap,CanonicalWord (lookup state.resource address.word))
    (hInterior : Interior capacity state) (he : state.active = first :: second :: tail) :
    (sourceWithWork limits bids first second tail hCap hState hInterior he).2 ≤
      2 * BinaryPRGHeapStoredTree.readBound limits.heap.tape.length depth +
        2 * BinaryPRGHeapStoredTree.readBound bids.heap.tape.length depth + 8 := by
  have h0 := (BinaryPRGHeapStoredTree.readWithWork_bounds limits first.word).1
  have h1 := (BinaryPRGHeapStoredTree.readWithWork_bounds limits second.word).1
  have h2 := (BinaryPRGHeapStoredTree.readWithWork_bounds bids first.word).1
  have h3 := (BinaryPRGHeapStoredTree.readWithWork_bounds bids second.word).1
  unfold sourceWithWork
  dsimp only
  omega

def pairWithWork (limits : Stored capacity) (bids : Stored state.resource)
    (first second : Address depth cap) (tail : List (Address depth cap))
    (hCap : ∀ address : Address depth cap,CanonicalWord (lookup capacity address.word))
    (hState : ∀ address : Address depth cap,CanonicalWord (lookup state.resource address.word))
    (hInterior : Interior capacity state) (he : state.active = first :: second :: tail) :
    BinaryPRGWordControllerPairOutputs.Outputs × ℕ :=
  let input := sourceWithWork limits bids first second tail hCap hState hInterior he
  let outputs := BinaryPRGWordControllerPairOutputs.prepareWithWork input.1
  (outputs.1,input.2 + input.1.sourcePayloadWork + outputs.2 + 4)

theorem pairWithWork_value (limits : Stored capacity) (bids : Stored state.resource)
    (first second : Address depth cap) (tail : List (Address depth cap))
    (hCap : ∀ address : Address depth cap,CanonicalWord (lookup capacity address.word))
    (hState : ∀ address : Address depth cap,CanonicalWord (lookup state.resource address.word))
    (hInterior : Interior capacity state) (he : state.active = first :: second :: tail) :
    (pairWithWork limits bids first second tail hCap hState hInterior he).1 =
      pair capacity state first second tail hCap hState hInterior he := by
  unfold pairWithWork pair
  dsimp only
  rw [BinaryPRGWordControllerPairOutputs.prepareWithWork_erasure,sourceWithWork_value]

end Blotto.BinaryPRGHeapResourcePair
