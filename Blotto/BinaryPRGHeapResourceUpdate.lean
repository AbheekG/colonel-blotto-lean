import Blotto.BinaryPRGHeapWriteSequence
import Blotto.BinaryPRGWordControllerBooleanResourceUpdateWork

/-! Selected resource updates execute tape reads, quadratic arithmetic,
persistent heap writes and post-write tape fractional tests. Logical trees
are only type indices in the physical objects and refinement proofs. Actual
Boolean active identifiers are retained. Reached work is composed directly;
full source-loop prices, physical metadata and lifetime remain separate. -/

namespace Blotto.BinaryPRGHeapResourceUpdate
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore
open BinaryPRGWordControllerBooleanResourceUpdate
open BinaryPRGHeapStoredTree (Stored)

variable {depth : ℕ} {cap : FixedBinaryWord depth}

structure Physical (state : State depth cap) where
  resource : Stored state.resource
  active : List (Address depth cap)
  active_eq : active = state.active

def Physical.reindex {first second : State depth cap} (h : first = second) (data : Physical first) : Physical second :=
  ⟨Stored.reindex (congrArg State.resource h) data.resource,data.active,
    (by rw [← h]; exact data.active_eq)⟩

def fractionalWithWork {capacity resource : Tree depth} (limits : Stored capacity) (bids : Stored resource)
    (address : Address depth cap) : Bool × ℕ :=
  let bid := BinaryPRGHeapStoredTree.readWithWork bids address.word
  let limit := BinaryPRGHeapStoredTree.readWithWork limits address.word
  ((!BinaryRationalArithmetic.lessEqual bid.1 BinaryRationalOpcode.zero) &&
    (!BinaryRationalArithmetic.lessEqual limit.1 bid.1),
    bid.2.work + limit.2.work + BinaryRationalArithmetic.lessEqualWork bid.1 BinaryRationalOpcode.zero +
      BinaryRationalArithmetic.lessEqualWork limit.1 bid.1 + 6)

theorem fractionalWithWork_value {capacity resource : Tree depth} (limits : Stored capacity) (bids : Stored resource)
    (address : Address depth cap) : (fractionalWithWork limits bids address).1 = fractional capacity resource address := by
  simp only [fractionalWithWork,fractional,BinaryPRGHeapStoredTree.readWithWork_value]

def scanWithWork {capacity resource : Tree depth} (limits : Stored capacity) (bids : Stored resource) :
    List (Address depth cap) → List (Address depth cap) × ℕ
  | [] => ([],1)
  | address :: rest =>
      let tested := fractionalWithWork limits bids address
      let later := scanWithWork limits bids rest
      (if tested.1 then address :: later.1 else later.1,
        tested.2 + later.2 + 2 * (address.word.bits.length + 1) + 3)

theorem scanWithWork_value {capacity resource : Tree depth} (limits : Stored capacity) (bids : Stored resource)
    (addresses : List (Address depth cap)) :
    (scanWithWork limits bids addresses).1 = addresses.filter (fractional capacity resource) := by
  induction addresses with
  | nil => rfl
  | cons address rest ih => simp only [scanWithWork,fractionalWithWork_value,List.filter_cons,ih]

def updateWithWork {capacity : Tree depth} {state : State depth cap}
    (limits : Stored capacity) (data : Physical state)
    (first second : Address depth cap) (tail : List (Address depth cap)) (chosen : SignedWord) :
    Physical (update capacity state first second tail chosen) × ℕ :=
  let a := BinaryPRGHeapStoredTree.readWithWork data.resource first.word
  let b := BinaryPRGHeapStoredTree.readWithWork data.resource second.word
  let total := BinaryQuadraticOpcode.applyWithWork .add a.1 b.1
  let other := BinaryQuadraticOpcode.applyWithWork .sub total.1 chosen
  let intermediate := BinaryPRGHeapStoredTree.writeWithWork data.resource first.word chosen
  let next := BinaryPRGHeapStoredTree.writeWithWork intermediate.1 second.word other.1
  let retained := scanWithWork limits next.1 [first,second]
  let hTree : write (write state.resource first.word chosen) second.word other.1 =
      (update capacity state first second tail chosen).resource := by
    dsimp only [other,total,a,b]
    simp only [BinaryPRGWordControllerBooleanResourceUpdate.update,
      BinaryQuadraticData.apply_erasure,BinaryPRGHeapStoredTree.readWithWork_value]
  let hActive : retained.1 ++ tail = (update capacity state first second tail chosen).active := by
    rw [scanWithWork_value]
    rw [hTree]
    rfl
  (⟨Stored.reindex hTree next.1,retained.1 ++ tail,hActive⟩,
    a.2.work + b.2.work + total.2 + other.2 + intermediate.2.work + next.2.work + retained.2 +
      2 * (first.word.bits.length + 1) * (tail.length + 2) + 12)

theorem updateWithWork_active {capacity : Tree depth} {state : State depth cap}
    (limits : Stored capacity) (data : Physical state)
    (first second : Address depth cap) (tail : List (Address depth cap)) (chosen : SignedWord) :
    (updateWithWork limits data first second tail chosen).1.active =
      (update capacity state first second tail chosen).active :=
  (updateWithWork limits data first second tail chosen).1.active_eq

end Blotto.BinaryPRGHeapResourceUpdate
