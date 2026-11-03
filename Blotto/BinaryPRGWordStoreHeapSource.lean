import Blotto.BinaryPRGWordStoreHeapMachine
import Blotto.BinaryPRGWordControllerBooleanResourceSource

/-! Concrete physical heap operands at the actual resource source boundary.
Incoming native row cells build their own Boolean tape heaps; four reached
pair operands are fetched through encoded physical pointers. Query words stay
Boolean, while Fin indices occur only in native refinement proofs. The full
outer caller still has its previous source ledger: these slower physical tape
prices are additional explicit components, not prices transferred by erasure. -/
namespace Blotto.BinaryPRGWordStoreHeapSource
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordStoreHeap
open BinaryPRGWordStoreHeapMachine (Charge)
variable {n : ℕ}

abbrev stored (table : FixedArrayTable n SignedWord) : Store :=
  BinaryPRGWordStoreHeap.prepare BinaryRationalOpcode.zero table.data.toList

def prepare (table : FixedArrayTable n SignedWord) : Store × Charge :=
  BinaryPRGWordStoreHeapMachine.prepareWithWork BinaryRationalOpcode.zero table.data.toList

theorem prepare_erasure (table : FixedArrayTable n SignedWord) : (prepare table).1 = stored table :=
  BinaryPRGWordStoreHeapMachine.prepareWithWork_erasure _ _

theorem count_same_length {α β : Type*} (first : List α) (second : List β) (h : first.length = second.length)
    (counter : List Bool) : BinaryCarryCounter.count first counter = BinaryCarryCounter.count second counter := by
  induction first generalizing second counter with
  | nil => have he : second = [] := List.length_eq_zero_iff.mp h.symm; subst second; rfl
  | cons item rest ih =>
      cases second with
      | nil => simp at h
      | cons other later =>
          exact ih later (Nat.succ.inj h) (BinaryCarryCounter.increment counter)

theorem stored_cap (table : FixedArrayTable n SignedWord) : (stored table).cap.value = n := by
  rw [prepare_cap,Array.length_toList,table.size]

theorem stored_width_eq (first second : FixedArrayTable n SignedWord) : (stored first).width = (stored second).width := by
  change (BinaryCarryCounter.count first.data.toList []).length = (BinaryCarryCounter.count second.data.toList []).length
  rw [count_same_length first.data.toList second.data.toList (by simp [first.size,second.size])]

theorem lookup_rebase (first second : Store) (h : first = second) (address : FixedBinaryWord second.width) :
    BinaryPRGWordStoreHeapMachine.lookupStoreWithWork first
      (⟨address.bits,address.size.trans (congrArg Store.width h).symm⟩ : FixedBinaryWord first.width) =
        BinaryPRGWordStoreHeapMachine.lookupStoreWithWork second address := by
  subst second
  cases address
  rfl

theorem guard_rebase (first second : Store) (h : first = second) (address : FixedBinaryWord second.width) :
    BinaryIndexWord.ltWithWork
      (⟨address.bits,address.size.trans (congrArg Store.width h).symm⟩ : FixedBinaryWord first.width) first.cap =
        BinaryIndexWord.ltWithWork address second.cap := by
  subst second
  cases address
  rfl

def read (table : FixedArrayTable n SignedWord) (address : FixedBinaryWord (stored table).width) : Option SignedWord × Charge :=
  let prepared := prepare table
  let query : FixedBinaryWord prepared.1.width := ⟨address.bits,address.size.trans (congrArg Store.width (prepare_erasure table)).symm⟩
  let found := BinaryPRGWordStoreHeapMachine.lookupStoreWithWork prepared.1 query
  let guard := BinaryIndexWord.ltWithWork query prepared.1.cap
  (if guard.1 then found.1 else none,⟨prepared.2.work + guard.2 + found.2.work + 2,
    prepared.2.allocatedBits + found.2.allocatedBits + 4 * (address.bits.length + 1)^2 + 8⟩)

theorem read_value (table : FixedArrayTable n SignedWord) (address : FixedBinaryWord (stored table).width) (h : address.value < n) :
    (read table address).1 = some (table.read ⟨address.value,h⟩) := by
  unfold read
  dsimp only
  rw [lookup_rebase _ _ (prepare_erasure table),guard_rebase _ _ (prepare_erasure table)]
  rw [BinaryIndexWord.ltWithWork_state]
  have hCap : address.value < (stored table).cap.value := by rw [stored_cap]; exact h
  rw [(BinaryIndexWord.lt_value address (stored table).cap).mpr hCap]
  simp only [ite_true,BinaryPRGWordStoreHeapMachine.lookupStoreWithWork_erasure]
  rw [prepare_lookup]
  simp [List.getD_eq_getElem?_getD,FixedArrayTable.read,h,table.size]

def readBound (table : FixedArrayTable n SignedWord) : ℕ :=
  BinaryPRGWordStoreHeapMachine.preparationBound BinaryRationalOpcode.zero table.data.toList +
    BinaryPRGWordStoreHeapMachine.sourceLookupBound BinaryRationalOpcode.zero table.data.toList + 12 * (binaryWordWidth n + 1) + 2

theorem read_work (table : FixedArrayTable n SignedWord) (address : FixedBinaryWord (stored table).width) :
    (read table address).2.work ≤ readBound table := by
  have hp := BinaryPRGWordStoreHeapMachine.prepared_lookup_work BinaryRationalOpcode.zero table.data.toList address
  have hBuilt := (BinaryPRGWordStoreHeapMachine.prepareWithWork_bounds BinaryRationalOpcode.zero table.data.toList).1
  have hg := BinaryIndexWord.ltWithWork_bound address (stored table).cap
  have hw := BinaryPRGWordControllerWordStore.prepare_width_bound BinaryRationalOpcode.zero table.data.toList
  simp only [Array.length_toList,table.size] at hw
  change (stored table).width ≤ binaryWordWidth n at hw
  unfold read readBound
  dsimp only
  rw [lookup_rebase _ _ (prepare_erasure table),guard_rebase _ _ (prepare_erasure table)]
  change (BinaryPRGWordStoreHeapMachine.lookupStoreWithWork (stored table) address).2.work ≤ _ at hp
  change (prepare table).2.work ≤ _ at hBuilt
  omega

structure Inputs where
  capacityFirst : SignedWord
  capacitySecond : SignedWord
  resourceFirst : SignedWord
  resourceSecond : SignedWord

def pairInputs (capacity resource : FixedArrayTable n SignedWord)
    (first second : FixedBinaryWord (stored capacity).width) : Option Inputs × Charge :=
  let resourceFirst : FixedBinaryWord (stored resource).width := ⟨first.bits,first.size.trans (stored_width_eq capacity resource)⟩
  let resourceSecond : FixedBinaryWord (stored resource).width := ⟨second.bits,second.size.trans (stored_width_eq capacity resource)⟩
  let a := read capacity first
  let b := read capacity second
  let c := read resource resourceFirst
  let d := read resource resourceSecond
  ((do
      let af ← a.1
      let bf ← b.1
      let cf ← c.1
      let df ← d.1
      pure ⟨af,bf,cf,df⟩),
    ⟨a.2.work + b.2.work + c.2.work + d.2.work + 8,
      a.2.allocatedBits + b.2.allocatedBits + c.2.allocatedBits + d.2.allocatedBits + 8⟩)

theorem pairInputs_value (capacity resource : FixedArrayTable n SignedWord)
    (first second : FixedBinaryWord (stored capacity).width) (hFirst : first.value < n) (hSecond : second.value < n) :
    (pairInputs capacity resource first second).1 = some ⟨capacity.read ⟨first.value,hFirst⟩,capacity.read ⟨second.value,hSecond⟩,
      resource.read ⟨first.value,hFirst⟩,resource.read ⟨second.value,hSecond⟩⟩ := by
  unfold pairInputs
  dsimp only
  rw [read_value capacity first hFirst,read_value capacity second hSecond]
  rw [read_value resource _ hFirst,read_value resource _ hSecond]
  rfl

theorem pairInputs_work (capacity resource : FixedArrayTable n SignedWord)
    (first second : FixedBinaryWord (stored capacity).width) :
    (pairInputs capacity resource first second).2.work ≤ 2 * readBound capacity + 2 * readBound resource + 8 := by
  have h1 := read_work capacity first
  have h2 := read_work capacity second
  have h3 := read_work resource (⟨first.bits,first.size.trans (stored_width_eq capacity resource)⟩ : FixedBinaryWord (stored resource).width)
  have h4 := read_work resource (⟨second.bits,second.size.trans (stored_width_eq capacity resource)⟩ : FixedBinaryWord (stored resource).width)
  unfold pairInputs
  dsimp only
  omega

def requestInputs (request : BinaryPRGRequest.Request n) (rich : Bool)
    (first second : FixedBinaryWord (stored (BinaryPRGResourceWork.resourceInput request rich).length).width) : Option Inputs × Charge :=
  pairInputs (BinaryPRGResourceWork.resourceInput request rich).length (BinaryPRGResourceWork.resourceInput request rich).resource first second

theorem requestInputs_value (request : BinaryPRGRequest.Request n) (rich : Bool)
    (first second : FixedBinaryWord (stored (BinaryPRGResourceWork.resourceInput request rich).length).width)
    (hFirst : first.value < n) (hSecond : second.value < n) :
    (requestInputs request rich first second).1 = some
      ⟨(BinaryPRGResourceWork.resourceInput request rich).length.read ⟨first.value,hFirst⟩,
       (BinaryPRGResourceWork.resourceInput request rich).length.read ⟨second.value,hSecond⟩,
       (BinaryPRGResourceWork.resourceInput request rich).resource.read ⟨first.value,hFirst⟩,
       (BinaryPRGResourceWork.resourceInput request rich).resource.read ⟨second.value,hSecond⟩⟩ :=
  pairInputs_value _ _ _ _ hFirst hSecond

theorem requestInputs_work (request : BinaryPRGRequest.Request n) (rich : Bool)
    (first second : FixedBinaryWord (stored (BinaryPRGResourceWork.resourceInput request rich).length).width) :
    (requestInputs request rich first second).2.work ≤
      2 * readBound (BinaryPRGResourceWork.resourceInput request rich).length +
        2 * readBound (BinaryPRGResourceWork.resourceInput request rich).resource + 8 := pairInputs_work _ _ _ _

end Blotto.BinaryPRGWordStoreHeapSource
