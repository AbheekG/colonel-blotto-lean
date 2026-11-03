import Blotto.BinarySeedLookupTree
import Blotto.BinaryIndexWord
import Blotto.BinaryRationalExpressionWork

/-! A stored-rational table backend takes actual Boolean addresses.  Tree
production follows the original source list and its Boolean carry ruler;
lookup and selected writes follow only address bits.  Natural values occur in
proofs, never in the read/write data path.  Cell/payload work is explicit.
This is a concrete backend ingredient, not yet a claim that all current Fin /
native-array callers have been replaced or that heap pointer encoding is joined. -/

namespace Blotto.BinaryPRGWordControllerWordStore
open BinaryRationalNormalization BinaryRationalEncoding

inductive Tree : ℕ → Type
  | leaf : SignedWord → Tree 0
  | branch {depth : ℕ} : Tree depth → Tree depth → Tree (depth + 1)

def scan : {depth : ℕ} → Tree depth → List Bool → SignedWord
  | _, .leaf word, _ => word
  | _, .branch left _, [] => scan left []
  | _, .branch left right, bit :: rest => if bit then scan right rest else scan left rest

def build (fallback : SignedWord) : (ruler : List Bool) → List SignedWord → Tree ruler.length × List SignedWord
  | [], [] => (.leaf fallback, [])
  | [], word :: rest => (.leaf word, rest)
  | _ :: ruler, items =>
      let first := build fallback ruler items
      let second := build fallback ruler first.2
      (.branch first.1 second.1, second.2)

theorem build_suffix (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :
    (build fallback ruler items).2 = items.drop (2^ruler.length) := by
  induction ruler generalizing items with
  | nil => cases items <;> simp [build]
  | cons bit ruler ih =>
      simp only [build, ih, List.drop_drop, List.length_cons, pow_succ]
      congr 1
      omega

theorem build_scan (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (address : List Bool)
    (h : address.length = ruler.length) :
    scan (build fallback ruler items).1 address = items.getD (BinaryBigEndian.value address) fallback := by
  induction ruler generalizing items address with
  | nil =>
      have he : address = [] := List.length_eq_zero_iff.mp h
      subst address
      cases items <;> simp [build, scan, BinaryBigEndian.value]
  | cons cell ruler ih =>
      cases address with
      | nil => simp at h
      | cons bit rest =>
          have hr : rest.length = ruler.length := by simpa using h
          cases bit
          · simpa only [build, scan, Bool.false_eq_true, ite_false, BinaryBigEndian.value, zero_add] using ih items rest hr
          · simp only [build, scan, ite_true]
            rw [ih _ rest hr, build_suffix]
            simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, BinaryBigEndian.value, ite_true, hr]

def lookup {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) : SignedWord :=
  scan tree address.bits.reverse

theorem build_lookup (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord)
    (address : FixedBinaryWord ruler.length) :
    lookup (build fallback ruler items).1 address = items.getD address.value fallback := by
  unfold lookup
  rw [build_scan fallback ruler items address.bits.reverse (by simpa using address.size), BinaryBigEndian.value_reverse]
  rfl

def writeScan : {depth : ℕ} → Tree depth → List Bool → SignedWord → Tree depth
  | _, .leaf _, _, word => .leaf word
  | _, .branch left right, [], word => .branch (writeScan left [] word) right
  | _, .branch left right, bit :: rest, word =>
      if bit then .branch left (writeScan right rest word) else .branch (writeScan left rest word) right

theorem scan_writeScan {depth : ℕ} (tree : Tree depth) (address query : List Bool) (word : SignedWord)
    (hAddress : address.length = depth) (hQuery : query.length = depth) :
    scan (writeScan tree address word) query = if query = address then word else scan tree query := by
  induction tree generalizing address query with
  | leaf old =>
      have ha : address = [] := List.length_eq_zero_iff.mp hAddress
      have hq : query = [] := List.length_eq_zero_iff.mp hQuery
      subst address
      subst query
      rfl
  | @branch depth left right ihl ihr =>
      cases address with
      | nil => simp at hAddress
      | cons bit rest =>
          cases query with
          | nil => simp at hQuery
          | cons asked later =>
              have hr : rest.length = depth := by simpa using hAddress
              have hl : later.length = depth := by simpa using hQuery
              cases bit <;> cases asked <;> simp [writeScan, scan,
                ihl rest later hr hl, ihr rest later hr hl]

def write {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) (word : SignedWord) : Tree depth :=
  writeScan tree address.bits.reverse word

theorem lookup_write {depth : ℕ} (tree : Tree depth) (address query : FixedBinaryWord depth) (word : SignedWord) :
    lookup (write tree address word) query = if query.value = address.value then word else lookup tree query := by
  unfold lookup write
  rw [scan_writeScan tree address.bits.reverse query.bits.reverse word
    (by simpa using address.size) (by simpa using query.size)]
  have hEq : query.bits.reverse = address.bits.reverse ↔ query.value = address.value := by
    rw [List.reverse_inj]
    exact ⟨fun h => by simp only [FixedBinaryWord.value, h],
      fun h => BinaryBorrowWord.littleValue_injective query.bits address.bits (query.size.trans address.size.symm) h⟩
  simp only [hEq]

structure Store where
  width : ℕ
  cap : FixedBinaryWord width
  tree : Tree width

def prepare (fallback : SignedWord) (items : List SignedWord) : Store :=
  let ruler := BinaryCarryCounter.count items []
  ⟨ruler.length, ⟨ruler, rfl⟩, (build fallback ruler items).1⟩

theorem prepare_cap (fallback : SignedWord) (items : List SignedWord) :
    (prepare fallback items).cap.value = items.length := by
  change BinaryCarryCounter.value (BinaryCarryCounter.count items []) = items.length
  rw [BinaryCarryCounter.count_value]
  simp [BinaryCarryCounter.value, BinaryBigEndian.littleValue]

theorem prepare_lookup (fallback : SignedWord) (items : List SignedWord)
    (address : FixedBinaryWord (prepare fallback items).width) :
    lookup (prepare fallback items).tree address = items.getD address.value fallback :=
  build_lookup _ _ _ _

def read (store : Store) (address : FixedBinaryWord store.width) : Option SignedWord :=
  if BinaryIndexWord.lt address store.cap then some (lookup store.tree address) else none

theorem read_prepare (fallback : SignedWord) (items : List SignedWord)
    (address : FixedBinaryWord (prepare fallback items).width) :
    read (prepare fallback items) address = if address.value < items.length then
      some (items.getD address.value fallback) else none := by
  unfold read
  rw [prepare_lookup]
  have hGuard := BinaryIndexWord.lt_value address (prepare fallback items).cap
  rw [prepare_cap] at hGuard
  by_cases h : address.value < items.length
  · simp only [hGuard.mpr h, h, ite_true]
  · have hf : BinaryIndexWord.lt address (prepare fallback items).cap = false := Bool.eq_false_iff.mpr (fun he => h (hGuard.mp he))
    simp only [hf, h, Bool.false_eq_true, ite_false]

def update (store : Store) (address : FixedBinaryWord store.width) (word : SignedWord) : Store :=
  ⟨store.width, store.cap, write store.tree address word⟩

theorem update_cap (store : Store) (address : FixedBinaryWord store.width) (word : SignedWord) :
    (update store address word).cap = store.cap := rfl

def scanVisits : {depth : ℕ} → Tree depth → List Bool → ℕ
  | _, .leaf _, _ => 1
  | _, .branch left _, [] => 1 + scanVisits left []
  | _, .branch left right, bit :: rest => 1 + if bit then scanVisits right rest else scanVisits left rest

theorem scanVisits_exact {depth : ℕ} (tree : Tree depth) (address : List Bool) :
    scanVisits tree address = depth + 1 := by
  induction tree generalizing address with
  | leaf old => rfl
  | @branch depth left right ihl ihr =>
      cases address with
      | nil => simp [scanVisits, ihl]; omega
      | cons bit rest => cases bit <;> simp [scanVisits, ihl, ihr] <;> omega

def lookupCells {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) : ℕ :=
  4 * address.bits.length + 6 * scanVisits tree address.bits.reverse + BinaryRationalExpression.payloadWords (lookup tree address)

theorem lookupCells_exact {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) :
    lookupCells tree address = 10 * depth + 6 + BinaryRationalExpression.payloadWords (lookup tree address) := by
  rw [lookupCells, address.size, scanVisits_exact]
  omega

def writeVisits : {depth : ℕ} → Tree depth → List Bool → ℕ
  | _, .leaf _, _ => 1
  | _, .branch left _, [] => 1 + writeVisits left []
  | _, .branch left right, bit :: rest => 1 + if bit then writeVisits right rest else writeVisits left rest

theorem writeVisits_exact {depth : ℕ} (tree : Tree depth) (address : List Bool) :
    writeVisits tree address = depth + 1 := by
  induction tree generalizing address with
  | leaf old => rfl
  | @branch depth left right ihl ihr =>
      cases address with
      | nil => simp [writeVisits, ihl]; omega
      | cons bit rest => cases bit <;> simp [writeVisits, ihl, ihr] <;> omega

def updateCells (store : Store) (address : FixedBinaryWord store.width) (word : SignedWord) : ℕ :=
  4 * address.bits.length + 8 * writeVisits store.tree address.bits.reverse + BinaryRationalExpression.payloadWords word

theorem updateCells_exact (store : Store) (address : FixedBinaryWord store.width) (word : SignedWord) :
    updateCells store address word = 12 * store.width + 8 + BinaryRationalExpression.payloadWords word := by
  rw [updateCells, address.size, writeVisits_exact]
  omega

def readWithWork (store : Store) (address : FixedBinaryWord store.width) : Option SignedWord × ℕ :=
  let guard := BinaryIndexWord.ltWithWork address store.cap
  if guard.1 then (some (lookup store.tree address), guard.2 + lookupCells store.tree address + 2)
  else (none, guard.2 + 2)

theorem readWithWork_erasure (store : Store) (address : FixedBinaryWord store.width) :
    (readWithWork store address).1 = read store address := by
  unfold readWithWork read
  dsimp only
  rw [BinaryIndexWord.ltWithWork_state]
  split <;> rfl

theorem readWithWork_bound (store : Store) (address : FixedBinaryWord store.width) :
    (readWithWork store address).2 ≤ 22 * store.width + 20 +
      BinaryRationalExpression.payloadWords (lookup store.tree address) := by
  have hGuard := BinaryIndexWord.ltWithWork_bound address store.cap
  unfold readWithWork
  dsimp only
  split
  · rw [lookupCells_exact]
    omega
  · omega

theorem count_mapFalse (items : List SignedWord) (counter : List Bool) :
    BinaryCarryCounter.count items counter = BinaryCarryCounter.count (items.map (fun _ => false)) counter := by
  induction items generalizing counter with
  | nil => rfl
  | cons word rest ih => simpa only [BinaryCarryCounter.count, List.map_cons] using ih (BinaryCarryCounter.increment counter)

theorem prepare_width (fallback : SignedWord) (items : List SignedWord) :
    (prepare fallback items).width = (BinarySeedLookupTree.prepare (items.map (fun _ => false))).width := by
  unfold prepare BinarySeedLookupTree.prepare
  dsimp only
  rw [count_mapFalse]

theorem prepare_width_bound (fallback : SignedWord) (items : List SignedWord) :
    (prepare fallback items).width ≤ binaryWordWidth items.length := by
  rw [prepare_width]
  simpa only [List.length_map] using BinarySeedLookupTree.prepare_width_bound (items.map (fun _ => false))

theorem prepare_capacity_bound (fallback : SignedWord) (items : List SignedWord) :
    2^(prepare fallback items).width ≤ 2 * items.length + 1 := by
  rw [prepare_width]
  simpa only [List.length_map] using BinarySeedLookupTree.prepare_capacity_bound (items.map (fun _ => false))

def buildVisits (fallback : SignedWord) : List Bool → List SignedWord → ℕ
  | [], _ => 1
  | _ :: ruler, items => buildVisits fallback ruler items + buildVisits fallback ruler (build fallback ruler items).2 + 1

theorem buildVisits_exact (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :
    buildVisits fallback ruler items + 1 = 2^(ruler.length + 1) := by
  induction ruler generalizing items with
  | nil => rfl
  | cons bit ruler ih =>
      have hl := ih items
      have hr := ih (build fallback ruler items).2
      simp only [buildVisits, List.length_cons, pow_succ]
      omega

def maxPayload : {depth : ℕ} → Tree depth → ℕ
  | _, .leaf word => BinaryRationalExpression.payloadWords word
  | _, .branch left right => max (maxPayload left) (maxPayload right)

def copiedPayload : {depth : ℕ} → Tree depth → ℕ
  | _, .leaf word => BinaryRationalExpression.payloadWords word
  | _, .branch left right => copiedPayload left + copiedPayload right

theorem copiedPayload_bound {depth : ℕ} (tree : Tree depth) :
    copiedPayload tree ≤ 2^depth * maxPayload tree := by
  induction tree with
  | leaf word => simp [copiedPayload, maxPayload]
  | @branch depth left right ihl ihr =>
      have hl := ihl.trans (Nat.mul_le_mul_left (2^depth) (Nat.le_max_left (maxPayload left) (maxPayload right)))
      have hr := ihr.trans (Nat.mul_le_mul_left (2^depth) (Nat.le_max_right (maxPayload left) (maxPayload right)))
      simp only [copiedPayload, maxPayload, pow_succ]
      nlinarith

theorem getD_payload_bound (fallback : SignedWord) (items : List SignedWord) (W : ℕ)
    (hFallback : BinaryRationalExpression.payloadWords fallback ≤ W)
    (hItems : ∀ word ∈ items, BinaryRationalExpression.payloadWords word ≤ W) (index : ℕ) :
    BinaryRationalExpression.payloadWords (items.getD index fallback) ≤ W := by
  induction items generalizing index with
  | nil => simp only [List.getD_nil]; exact hFallback
  | cons word rest ih =>
      cases index with
      | zero => simp only [List.getD_cons_zero]; exact hItems word (by simp)
      | succ index =>
          simp only [List.getD_cons_succ]
          exact ih (fun next hn => hItems next (by simp [hn])) index

theorem build_maxPayload_bound (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (W : ℕ)
    (hAll : ∀ index, BinaryRationalExpression.payloadWords (items.getD index fallback) ≤ W) :
    maxPayload (build fallback ruler items).1 ≤ W := by
  induction ruler generalizing items with
  | nil =>
      cases items with
      | nil => exact hAll 0
      | cons word rest => exact hAll 0
  | cons bit ruler ih =>
      have hLeft := ih items hAll
      have hRight : ∀ index, BinaryRationalExpression.payloadWords ((build fallback ruler items).2.getD index fallback) ≤ W := by
        intro index
        rw [build_suffix, List.getD_eq_getElem?_getD, List.getElem?_drop]
        exact hAll (2^ruler.length + index)
      have hRightBound := ih (build fallback ruler items).2 hRight
      simp only [build, maxPayload]
      exact max_le hLeft hRightBound

def preparationCells (fallback : SignedWord) (items : List SignedWord) : ℕ :=
  4 * BinaryCarryCounter.countCarryCells items [] + items.length +
    6 * buildVisits fallback (BinaryCarryCounter.count items []) items + copiedPayload (prepare fallback items).tree

theorem preparationCells_bound (fallback : SignedWord) (items : List SignedWord) (W : ℕ)
    (hFallback : BinaryRationalExpression.payloadWords fallback ≤ W)
    (hItems : ∀ word ∈ items, BinaryRationalExpression.payloadWords word ≤ W) :
    preparationCells fallback items ≤ 33 * items.length + 6 + (2 * items.length + 1) * W := by
  have hCarry := BinaryCarryCounter.countCarryCells_bound items []
  change BinaryCarryCounter.countCarryCells items [] ≤ 2 * items.length at hCarry
  have hVisits := buildVisits_exact fallback (BinaryCarryCounter.count items []) items
  have hCapacity := prepare_capacity_bound fallback items
  change 2^(BinaryCarryCounter.count items []).length ≤ 2 * items.length + 1 at hCapacity
  rw [pow_succ] at hVisits
  have hMax := build_maxPayload_bound fallback (BinaryCarryCounter.count items []) items W
    (getD_payload_bound fallback items W hFallback hItems)
  have hCopied := copiedPayload_bound (prepare fallback items).tree
  have hCopyBound : copiedPayload (prepare fallback items).tree ≤ (2 * items.length + 1) * W := by
    exact hCopied.trans (Nat.mul_le_mul hCapacity hMax)
  unfold preparationCells
  omega

end Blotto.BinaryPRGWordControllerWordStore
