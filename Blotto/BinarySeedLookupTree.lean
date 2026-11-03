import Blotto.FixedBinaryWord
import Blotto.BinaryCarryCounterSize

/-! A complete Boolean seed tree is produced from the actual input seed.
Its height ruler is the Boolean carry-count word, never a decoded natural.
Reads reverse the little-endian address once, then follow Boolean branches.
The bounds count Boolean/list/tree cells; pointer widths, ownership and physical
allocation are separate execution obligations. -/

namespace Blotto.BinarySeedLookupTree

inductive Tree : ℕ → Type
  | leaf : Bool → Tree 0
  | branch {depth : ℕ} : Tree depth → Tree depth → Tree (depth + 1)

def scan : {depth : ℕ} → Tree depth → List Bool → Bool
  | _, .leaf bit, _ => bit
  | _, .branch left _, [] => scan left []
  | _, .branch left right, bit :: rest =>
      if bit then scan right rest else scan left rest

/-- The ruler's bits are used only as cells, never as an assembled index. -/
def build : (ruler : List Bool) → List Bool → Tree ruler.length × List Bool
  | [], [] => (.leaf false, [])
  | [], bit :: rest => (.leaf bit, rest)
  | _ :: ruler, seed =>
      let left := build ruler seed
      let right := build ruler left.2
      (.branch left.1 right.1, right.2)

theorem build_suffix (ruler seed : List Bool) :
    (build ruler seed).2 = seed.drop (2 ^ ruler.length) := by
  induction ruler generalizing seed with
  | nil => cases seed <;> simp [build]
  | cons cell ruler ih =>
      simp only [build, ih, List.drop_drop, List.length_cons, pow_succ]
      congr 1
      omega

theorem build_scan (ruler seed address : List Bool) (h : address.length = ruler.length) :
    scan (build ruler seed).1 address = seed.getD (BinaryBigEndian.value address) false := by
  induction ruler generalizing seed address with
  | nil =>
      have ha : address = [] := List.length_eq_zero_iff.mp h
      subst address
      cases seed <;> simp [build,scan,BinaryBigEndian.value]
  | cons cell ruler ih =>
      cases address with
      | nil => simp at h
      | cons bit rest =>
          have hr : rest.length = ruler.length := by simpa using h
          cases bit
          · simpa only [build,scan,Bool.false_eq_true,ite_false,BinaryBigEndian.value,
              zero_add] using ih seed rest hr
          · simp only [build,scan,ite_true]
            rw [ih _ rest hr,build_suffix]
            simp only [List.getD_eq_getElem?_getD,List.getElem?_drop,BinaryBigEndian.value,ite_true,hr]

def lookup {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) : Bool :=
  scan tree address.bits.reverse

theorem build_lookup (ruler seed : List Bool) (address : FixedBinaryWord ruler.length) :
    lookup (build ruler seed).1 address = seed.getD address.value false := by
  unfold lookup
  rw [build_scan ruler seed address.bits.reverse (by simpa using address.size),
    BinaryBigEndian.value_reverse]
  rfl

def cells : {depth : ℕ} → Tree depth → ℕ
  | _, .leaf _ => 1
  | _, .branch left right => cells left + cells right + 1

theorem cells_exact {depth : ℕ} (tree : Tree depth) : cells tree + 1 = 2 ^ (depth + 1) := by
  induction tree with
  | leaf bit => rfl
  | @branch depth left right ihl ihr =>
      simp only [cells,pow_succ]
      omega

/-- A reached tree-cell count, including the leaf. -/
def scanVisits : {depth : ℕ} → Tree depth → List Bool → ℕ
  | _, .leaf _, _ => 1
  | _, .branch left _, [] => scanVisits left [] + 1
  | _, .branch left right, bit :: rest =>
      (if bit then scanVisits right rest else scanVisits left rest) + 1

theorem scanVisits_exact {depth : ℕ} (tree : Tree depth) (address : List Bool) :
    scanVisits tree address = depth + 1 := by
  induction tree generalizing address with
  | leaf bit => rfl
  | @branch depth left right ihl ihr =>
      cases address with
      | nil => simp [scanVisits,ihl]
      | cons bit rest => cases bit <;> simp [scanVisits,ihl,ihr]

/-- Reverse-list cell visits plus the reached tree path. -/
def lookupCells {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) : ℕ :=
  address.bits.length + scanVisits tree address.bits.reverse

theorem lookupCells_exact {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) :
    lookupCells tree address = 2 * depth + 1 := by
  rw [lookupCells,address.size,scanVisits_exact]
  omega

/-- Build visits follow exactly the same recursive suffixes as the producer. -/
def buildVisits : List Bool → List Bool → ℕ
  | [], _ => 1
  | _ :: ruler, seed =>
      buildVisits ruler seed + buildVisits ruler (build ruler seed).2 + 1

theorem buildVisits_exact (ruler seed : List Bool) :
    buildVisits ruler seed + 1 = 2 ^ (ruler.length + 1) := by
  induction ruler generalizing seed with
  | nil => rfl
  | cons cell ruler ih =>
      have hl := ih seed
      have hr := ih (build ruler seed).2
      simp only [buildVisits,List.length_cons,pow_succ]
      omega

structure Store where
  width : ℕ
  cap : FixedBinaryWord width
  tree : Tree width

/-- This is the native producer: the carry loop, then the ruler-shaped tree. -/
def prepare (seed : List Bool) : Store :=
  let ruler := BinaryCarryCounter.count seed []
  ⟨ruler.length,⟨ruler,rfl⟩,(build ruler seed).1⟩

def Store.lookup (store : Store) (address : FixedBinaryWord store.width) : Bool :=
  BinarySeedLookupTree.lookup store.tree address

def Store.lookupCells (store : Store) (address : FixedBinaryWord store.width) : ℕ :=
  BinarySeedLookupTree.lookupCells store.tree address

/-- Tree paths and reverse-list visits, without an assumed unit-price machine. -/
def Store.lookupVisits (store : Store) (address : FixedBinaryWord store.width) : ℕ :=
  store.lookupCells address

def Store.lookupWithVisits (store : Store) (address : FixedBinaryWord store.width) : Bool × ℕ :=
  (store.lookup address,store.lookupVisits address)

theorem Store.lookupVisits_exact (store : Store) (address : FixedBinaryWord store.width) :
    store.lookupVisits address = 2 * store.width + 1 :=
  lookupCells_exact store.tree address

theorem Store.lookupVisits_bound (store : Store) (address : FixedBinaryWord store.width) :
    store.lookupVisits address ≤ 2 * store.width + 1 :=
  le_of_eq (store.lookupVisits_exact address)

theorem Store.lookupWithVisits_state (store : Store) (address : FixedBinaryWord store.width) :
    (store.lookupWithVisits address).1 = store.lookup address := rfl

theorem Store.cap_room (store : Store) : store.cap.value < 2 ^ store.width := by
  have h := BinaryBigEndian.value_bounds store.cap.bits.reverse
  rw [BinaryBigEndian.value_reverse,List.length_reverse,store.cap.size] at h
  exact h

theorem prepare_cap (seed : List Bool) : (prepare seed).cap.value = seed.length := by
  change BinaryCarryCounter.value (BinaryCarryCounter.count seed []) = seed.length
  rw [BinaryCarryCounter.count_value]
  simp [BinaryCarryCounter.value,BinaryBigEndian.littleValue]

theorem cap_value (seed : List Bool) : (prepare seed).cap.value = seed.length :=
  prepare_cap seed

theorem prepare_room (seed : List Bool) : seed.length < 2 ^ (prepare seed).width := by
  rw [← prepare_cap seed]
  exact (prepare seed).cap_room

theorem prepare_consumed (seed : List Bool) :
    (build (BinaryCarryCounter.count seed []) seed).2 = [] := by
  rw [build_suffix]
  apply List.drop_eq_nil_iff.mpr
  exact le_of_lt (prepare_room seed)

theorem prepare_lookup (seed : List Bool) (address : FixedBinaryWord (prepare seed).width) :
    (prepare seed).lookup address = seed.getD address.value false := by
  exact build_lookup (BinaryCarryCounter.count seed []) seed address

theorem prepare_lookup_in_range (seed : List Bool)
    (address : FixedBinaryWord (prepare seed).width) (h : address.value < seed.length) :
    (prepare seed).lookup address = seed[address.value] := by
  rw [prepare_lookup]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]

theorem prepare_lookupCells (seed : List Bool)
    (address : FixedBinaryWord (prepare seed).width) :
    (prepare seed).lookupCells address = 2 * (prepare seed).width + 1 :=
  lookupCells_exact (prepare seed).tree address

theorem prepare_width_bound (seed : List Bool) :
    (prepare seed).width ≤ binaryWordWidth seed.length := by
  change (BinaryCarryCounter.count seed []).length ≤ binaryWordWidth seed.length
  have h := BinaryCarryCounter.canonical_length_bound
    (BinaryCarryCounter.count seed []) (BinaryCarryCounter.count_canonical seed [] trivial)
  rw [BinaryCarryCounter.count_value] at h
  simpa only [BinaryCarryCounter.value,BinaryBigEndian.littleValue,Nat.zero_add] using h

theorem prepare_capacity_bound (seed : List Bool) :
    2 ^ (prepare seed).width ≤ 2 * seed.length + 1 := by
  let ruler := BinaryCarryCounter.count seed []
  have hv : BinaryCarryCounter.value ruler = seed.length := prepare_cap seed
  by_cases he : ruler = []
  · change 2 ^ ruler.length ≤ _
    rw [he]
    simp
  · have hc := BinaryCarryCounter.count_canonical seed [] (by trivial)
    have hl := BinaryCarryCounter.value_lower ruler hc he
    have hp : 0 < ruler.length := List.length_pos_iff.mpr he
    have hn : ruler.length = (ruler.length - 1) + 1 := by omega
    change 2 ^ ruler.length ≤ _
    rw [hn,pow_succ]
    rw [hv] at hl
    omega

theorem prepare_treeCells_bound (seed : List Bool) :
    cells (prepare seed).tree ≤ 4 * seed.length + 1 := by
  have he := cells_exact (prepare seed).tree
  have hc := prepare_capacity_bound seed
  rw [pow_succ] at he
  omega

/-- Ruler bits and tree nodes, excluding a pointer-width interpretation. -/
def Store.representationCells (store : Store) : ℕ := store.width + cells store.tree

theorem prepare_representationCells_bound (seed : List Bool) :
    (prepare seed).representationCells ≤ binaryWordWidth seed.length + 4 * seed.length + 1 := by
  have hw := prepare_width_bound seed
  have ht := prepare_treeCells_bound seed
  unfold Store.representationCells
  omega

/-- Counting carry cells, input-list counting cells, and one producer visit/node.
Each visited node has a conservative constant cell read/write allowance. -/
def preparationCells (seed : List Bool) : ℕ :=
  4 * BinaryCarryCounter.countCarryCells seed [] + seed.length +
    6 * buildVisits (BinaryCarryCounter.count seed []) seed

theorem preparationCells_bound (seed : List Bool) :
    preparationCells seed ≤ 33 * seed.length + 6 := by
  have hc := BinaryCarryCounter.countCarryCells_bound seed []
  change BinaryCarryCounter.countCarryCells seed [] ≤ 2 * seed.length at hc
  have hv := buildVisits_exact (BinaryCarryCounter.count seed []) seed
  have hp := prepare_capacity_bound seed
  change 2 ^ (BinaryCarryCounter.count seed []).length ≤ 2 * seed.length + 1 at hp
  rw [pow_succ] at hv
  unfold preparationCells
  omega

end Blotto.BinarySeedLookupTree
