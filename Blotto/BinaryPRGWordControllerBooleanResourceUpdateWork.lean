import Blotto.BinaryPRGWordControllerBooleanResourceUpdate

/-! Own source prices for actual Boolean-address resource selection: tree
lookup/path-copy writes, quadratic arithmetic, both fractional comparisons,
and retained Boolean-address list construction. Pointer-word interpretation
and adoption by the outer resource caller remain separate joins. -/
namespace Blotto.BinaryPRGWordControllerBooleanResourceUpdateWork
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerBooleanResourceUpdate

def fractionalWithWork {width : ℕ} {cap : FixedBinaryWord width} (capacity resource : Tree width)
    (address : Address width cap) : Bool × ℕ :=
  let bid := lookup resource address.word
  let limit := lookup capacity address.word
  (fractional capacity resource address,
    lookupCells resource address.word + lookupCells capacity address.word +
      BinaryRationalArithmetic.lessEqualWork bid BinaryRationalOpcode.zero +
        BinaryRationalArithmetic.lessEqualWork limit bid + 6)

theorem fractionalWithWork_erasure {width : ℕ} {cap : FixedBinaryWord width} (capacity resource : Tree width)
    (address : Address width cap) : (fractionalWithWork capacity resource address).1 =
    fractional capacity resource address := rfl

def fractionalBound (indexWidth W : ℕ) : ℕ := 1000 * (W + 1)^2 + 20 * indexWidth + 4 * W + 20

theorem fractionalWithWork_bound {indexWidth : ℕ} {cap : FixedBinaryWord indexWidth}
    (capacity resource : Tree indexWidth) (address : Address indexWidth cap) (W : ℕ) (hW : 1 ≤ W)
    (hCap : width (lookup capacity address.word) ≤ W) (hResource : width (lookup resource address.word) ≤ W) :
    (fractionalWithWork capacity resource address).2 ≤ fractionalBound indexWidth W := by
  have hFirst := BinaryRationalArithmetic.lessEqualWork_bound (lookup resource address.word) BinaryRationalOpcode.zero
  have hSecond := BinaryRationalArithmetic.lessEqualWork_bound (lookup capacity address.word) (lookup resource address.word)
  have h0 : BinaryRationalArithmetic.pairWidth (lookup resource address.word) BinaryRationalOpcode.zero ≤ W :=
    max_le hResource hW
  have h1 : BinaryRationalArithmetic.pairWidth (lookup capacity address.word) (lookup resource address.word) ≤ W :=
    max_le hCap hResource
  have hb0 := hFirst.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right h0 1) 2))
  have hb1 := hSecond.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right h1 1) 2))
  have p0 := BinaryRationalExpression.payloadWords_bound _ W hResource
  have p1 := BinaryRationalExpression.payloadWords_bound _ W hCap
  unfold fractionalWithWork fractionalBound
  dsimp only
  rw [lookupCells_exact,lookupCells_exact]
  omega

def scanWithWork {width : ℕ} {cap : FixedBinaryWord width} (capacity resource : Tree width) :
    List (Address width cap) → List (Address width cap) × ℕ
  | [] => ([],1)
  | address :: rest =>
      let tested := fractionalWithWork capacity resource address
      let later := scanWithWork capacity resource rest
      (if tested.1 then address :: later.1 else later.1,tested.2 + later.2 + 2 * (width + 1) + 3)

theorem scanWithWork_erasure {width : ℕ} {cap : FixedBinaryWord width} (capacity resource : Tree width)
    (addresses : List (Address width cap)) : (scanWithWork capacity resource addresses).1 =
    addresses.filter (fractional capacity resource) := by
  induction addresses with
  | nil => rfl
  | cons address rest ih => simp only [scanWithWork,fractionalWithWork_erasure,List.filter_cons,ih]

theorem scanWithWork_bound {indexWidth : ℕ} {cap : FixedBinaryWord indexWidth} (capacity resource : Tree indexWidth)
    (addresses : List (Address indexWidth cap)) (W : ℕ) (hW : 1 ≤ W)
    (hCap : ∀ address ∈ addresses,width (lookup capacity address.word) ≤ W)
    (hResource : ∀ address ∈ addresses,width (lookup resource address.word) ≤ W) :
    (scanWithWork capacity resource addresses).2 ≤
      addresses.length * (fractionalBound indexWidth W + 2 * (indexWidth + 1) + 3) + 1 := by
  induction addresses with
  | nil => simp [scanWithWork]
  | cons address rest ih =>
    have hCurrent := fractionalWithWork_bound capacity resource address W hW
      (hCap address (by simp)) (hResource address (by simp))
    have hRest := ih (fun address h => hCap address (by simp [h])) (fun address h => hResource address (by simp [h]))
    simp only [scanWithWork,List.length_cons]
    nlinarith

def updateWithWork {width : ℕ} {cap : FixedBinaryWord width} (capacity : Tree width) (state : State width cap)
    (first second : Address width cap) (tail : List (Address width cap)) (chosen : SignedWord) : State width cap × ℕ :=
  let total := BinaryQuadraticOpcode.applyWithWork .add (lookup state.resource first.word) (lookup state.resource second.word)
  let other := BinaryQuadraticOpcode.applyWithWork .sub total.1 chosen
  let intermediate := write state.resource first.word chosen
  let next := write intermediate second.word other.1
  let retained := scanWithWork capacity next [first,second]
  (⟨next,retained.1 ++ tail⟩,
    lookupCells state.resource first.word + lookupCells state.resource second.word + total.2 + other.2 +
      updateCells ⟨width,cap,state.resource⟩ first.word chosen +
        updateCells ⟨width,cap,intermediate⟩ second.word other.1 + retained.2 +
          2 * (width + 1) * (tail.length + 2) + 12)

theorem updateWithWork_erasure {width : ℕ} {cap : FixedBinaryWord width} (capacity : Tree width) (state : State width cap)
    (first second : Address width cap) (tail : List (Address width cap)) (chosen : SignedWord) :
    (updateWithWork capacity state first second tail chosen).1 = BinaryPRGWordControllerBooleanResourceUpdate.update capacity state first second tail chosen := by
  unfold updateWithWork BinaryPRGWordControllerBooleanResourceUpdate.update
  dsimp only
  rw [BinaryQuadraticData.apply_erasure,BinaryQuadraticData.apply_erasure,scanWithWork_erasure]

def updateBound (indexWidth W tailLength : ℕ) : ℕ :=
  22000 * (W + 1)^2 + 2 * (fractionalBound indexWidth W + 2 * (indexWidth + 1) + 3) +
    44 * indexWidth + 8 * W + 45 + 2 * (indexWidth + 1) * (tailLength + 2)

theorem updateWithWork_bound {indexWidth : ℕ} {cap : FixedBinaryWord indexWidth} (capacity : Tree indexWidth)
    (state : State indexWidth cap) (first second : Address indexWidth cap) (tail : List (Address indexWidth cap))
    (chosen : SignedWord) (W : ℕ) (hW : 1 ≤ W)
    (hBefore : ∀ address : Address indexWidth cap,width (lookup state.resource address.word) ≤ W)
    (hCap : ∀ address : Address indexWidth cap,width (lookup capacity address.word) ≤ W)
    (hChosen : width chosen ≤ W)
    (hTotal : width (BinaryQuadraticData.apply .add (lookup state.resource first.word) (lookup state.resource second.word)) ≤ W)
    (hOther : width (BinaryQuadraticData.apply .sub
      (BinaryQuadraticData.apply .add (lookup state.resource first.word) (lookup state.resource second.word)) chosen) ≤ W) :
    (updateWithWork capacity state first second tail chosen).2 ≤ updateBound indexWidth W tail.length := by
  let added := BinaryQuadraticOpcode.applyWithWork .add (lookup state.resource first.word) (lookup state.resource second.word)
  let other := BinaryQuadraticOpcode.applyWithWork .sub added.1 chosen
  have hAdded : width added.1 ≤ W := by simpa only [added,BinaryQuadraticData.apply_erasure] using hTotal
  have hSub : width other.1 ≤ W := by simpa only [other,added,BinaryQuadraticData.apply_erasure] using hOther
  have hAddWork := (BinaryQuadraticOpcode.applyWithWork_bound .add _ _).trans
    (Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le (hBefore first) (hBefore second)) 1) 2))
  have hSubWork := (BinaryQuadraticOpcode.applyWithWork_bound .sub added.1 chosen).trans
    (Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hAdded hChosen) 1) 2))
  let next := write (write state.resource first.word chosen) second.word other.1
  have hAfter : ∀ address : Address indexWidth cap,width (lookup next address.word) ≤ W := by
    intro address
    dsimp only [next]
    rw [lookup_write,lookup_write]
    split
    · exact hSub
    · split
      · exact hChosen
      · exact hBefore address
  have hScan := scanWithWork_bound capacity next [first,second] W hW
    (fun address _ => hCap address) (fun address _ => hAfter address)
  have p0 := BinaryRationalExpression.payloadWords_bound _ W (hBefore first)
  have p1 := BinaryRationalExpression.payloadWords_bound _ W (hBefore second)
  have pChosen := BinaryRationalExpression.payloadWords_bound _ W hChosen
  have pOther := BinaryRationalExpression.payloadWords_bound _ W hSub
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd] at hScan
  unfold updateWithWork updateBound
  dsimp only
  rw [lookupCells_exact,lookupCells_exact,updateCells_exact,updateCells_exact]
  dsimp only
  change (10 * indexWidth + 6 + BinaryRationalExpression.payloadWords (lookup state.resource first.word)) +
    (10 * indexWidth + 6 + BinaryRationalExpression.payloadWords (lookup state.resource second.word)) +
    added.2 + other.2 + (12 * indexWidth + 8 + BinaryRationalExpression.payloadWords chosen) +
    (12 * indexWidth + 8 + BinaryRationalExpression.payloadWords other.1) +
    (scanWithWork capacity next [first,second]).2 + 2 * (indexWidth + 1) * (tail.length + 2) + 12 ≤ _
  change added.2 ≤ _ at hAddWork
  change other.2 ≤ _ at hSubWork
  omega

end Blotto.BinaryPRGWordControllerBooleanResourceUpdateWork
