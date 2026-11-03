import Blotto.BinaryPRGWordControllerWordStoreView
import Blotto.BinaryResourceState
import Blotto.BinaryQuadraticData

/-! A resource update backend follows retained Boolean addresses for both
selected writes and both retained-fractional tests. Its active identifiers are
Boolean words with erased in-cap proofs. Native tables/Fin identifiers occur
only in a noncomputable semantic view. This ingredient is not yet substituted
for the outer resource caller's native input/output arrays. -/
namespace Blotto.BinaryPRGWordControllerBooleanResourceUpdate
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerWordStoreView

structure Address (width : ℕ) (cap : FixedBinaryWord width) where
  word : FixedBinaryWord width
  in_cap : word.value < cap.value

noncomputable def Address.index {width : ℕ} {cap : FixedBinaryWord width}
    (address : Address width cap) (n : ℕ) (hCount : n = cap.value) : Fin n :=
  ⟨address.word.value,by simpa only [hCount] using address.in_cap⟩

structure State (width : ℕ) (cap : FixedBinaryWord width) where
  resource : Tree width
  active : List (Address width cap)

noncomputable def table {width : ℕ} (cap : FixedBinaryWord width) (tree : Tree width)
    (n : ℕ) (hCount : n = cap.value) : FixedArrayTable n SignedWord :=
  view ⟨width,cap,tree⟩ n hCount

noncomputable def State.reference {width : ℕ} {cap : FixedBinaryWord width}
    (state : State width cap) (n : ℕ) (hCount : n = cap.value) : BinaryResourceState.State n :=
  ⟨table cap state.resource n hCount,state.active.map (fun address => address.index n hCount)⟩

theorem table_read {width : ℕ} {cap : FixedBinaryWord width} (tree : Tree width)
    (address : Address width cap) (n : ℕ) (hCount : n = cap.value) :
    (table cap tree n hCount).read (address.index n hCount) = lookup tree address.word := by
  exact view_read_address ⟨width,cap,tree⟩ n hCount address.word (address.index n hCount).isLt

theorem table_write {width : ℕ} {cap : FixedBinaryWord width} (tree : Tree width)
    (address : Address width cap) (word : SignedWord) (n : ℕ) (hCount : n = cap.value) :
    table cap (write tree address.word word) n hCount =
      (table cap tree n hCount).write (address.index n hCount) word := by
  exact view_update ⟨width,cap,tree⟩ n hCount address.word (address.index n hCount).isLt word

def fractional {width : ℕ} {cap : FixedBinaryWord width} (capacity resource : Tree width)
    (address : Address width cap) : Bool :=
  let bid := lookup resource address.word
  let limit := lookup capacity address.word
  (!BinaryRationalArithmetic.lessEqual bid BinaryRationalOpcode.zero) &&
    (!BinaryRationalArithmetic.lessEqual limit bid)

theorem fractional_reference {width : ℕ} {cap : FixedBinaryWord width} (capacity resource : Tree width)
    (address : Address width cap) (n : ℕ) (hCount : n = cap.value) :
    fractional capacity resource address = BinaryResourceState.fractional
      (table cap capacity n hCount) (table cap resource n hCount) (address.index n hCount) := by
  simp only [fractional,BinaryResourceState.fractional,table_read]

theorem filter_reference {width : ℕ} {cap : FixedBinaryWord width} (capacity resource : Tree width)
    (addresses : List (Address width cap)) (n : ℕ) (hCount : n = cap.value) :
    (addresses.filter (fractional capacity resource)).map (fun address => address.index n hCount) =
      (addresses.map (fun address => address.index n hCount)).filter
        (BinaryResourceState.fractional (table cap capacity n hCount) (table cap resource n hCount)) := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
    simp only [List.filter_cons,List.map_cons]
    rw [fractional_reference capacity resource address n hCount]
    split <;> simp only [List.map_cons,ih]

theorem apply_native (op : RealArithmeticOp) (first second : SignedWord)
    (hFirst : BinaryRationalOpcode.Valid first) (hSecond : BinaryRationalOpcode.Valid second) :
    BinaryQuadraticData.apply op first second = BinaryRationalOpcode.apply op first second := by
  rw [← BinaryQuadraticData.apply_erasure,BinaryQuadraticOpcode.applyWithWork_state op first second hFirst hSecond]

def update {width : ℕ} {cap : FixedBinaryWord width} (capacity : Tree width) (state : State width cap)
    (first second : Address width cap) (tail : List (Address width cap)) (chosen : SignedWord) : State width cap :=
  let total := BinaryQuadraticData.apply .add (lookup state.resource first.word) (lookup state.resource second.word)
  let other := BinaryQuadraticData.apply .sub total chosen
  let next := write (write state.resource first.word chosen) second.word other
  ⟨next,[first,second].filter (fractional capacity next) ++ tail⟩

theorem update_reference {width : ℕ} {cap : FixedBinaryWord width} (capacity : Tree width)
    (state : State width cap) (first second : Address width cap) (tail : List (Address width cap))
    (chosen : SignedWord) (hFirst : BinaryRationalOpcode.Valid (lookup state.resource first.word))
    (hSecond : BinaryRationalOpcode.Valid (lookup state.resource second.word))
    (hChosen : BinaryRationalOpcode.Valid chosen) (n : ℕ) (hCount : n = cap.value) :
    (update capacity state first second tail chosen).reference n hCount =
      BinaryResourceState.update (table cap capacity n hCount) (state.reference n hCount)
        (first.index n hCount) (second.index n hCount) (tail.map (fun address => address.index n hCount)) chosen := by
  have hTotal := apply_native .add _ _ hFirst hSecond
  have hOther := apply_native .sub
    (BinaryQuadraticData.apply .add (lookup state.resource first.word) (lookup state.resource second.word)) chosen (by
    rw [hTotal]
    exact BinaryRationalOpcode.apply_valid .add _ _ hFirst hSecond) hChosen
  rw [hTotal] at hOther
  unfold update State.reference BinaryResourceState.update
  dsimp only
  simp only [table_read,hTotal,hOther,table_write,List.map_append,filter_reference,
    List.map_cons,List.map_nil]

end Blotto.BinaryPRGWordControllerBooleanResourceUpdate
