import Blotto.BinaryPRGHeapScanLifetime

/-! Measure the Boolean comparison work of the reached heap scan using the
same two physical reads that decide each active coordinate. This is an exact
observer of the selected scan's result and trace; the lookup and control work
of the heap scan remain in their existing separate ledgers. -/
namespace Blotto.BinaryPRGHeapScanComparisonWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (Packed pack)
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 1000000

variable {capacity : Store}

def fractionalWithWork (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) : (Bool × Trace) × ℕ :=
  let bid := BinaryPRGHeapPackedLifetime.readWithTrace bids address.word
  let limit := BinaryPRGHeapPackedLifetime.readWithTrace (pack limits) address.word
  let positive := BinaryQuadraticResourceStateLifetime.compareWithTrace bid.1 BinaryRationalOpcode.zero
  let below := BinaryQuadraticResourceStateLifetime.compareWithTrace limit.1 bid.1
  (((!positive.1) && (!below.1),wrap 16 2 [bid.2,limit.2,positive.2,below.2]),
    BinaryRationalArithmetic.lessEqualWork bid.1 BinaryRationalOpcode.zero +
      BinaryRationalArithmetic.lessEqualWork limit.1 bid.1)

theorem fractionalWithWork_erases (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) :
    (fractionalWithWork limits bids address).1 =
      BinaryPRGHeapScanLifetime.fractionalWithTrace limits bids address := by
  rfl

theorem fractionalWithWork_native_comparisons (limits : Stored capacity.tree)
    (bids : Packed capacity.width) (address : Address capacity.width capacity.cap) :
    (fractionalWithWork limits bids address).2 =
      BinaryRationalArithmetic.lessEqualWork
        (bids.readWithWork address.word).1 BinaryRationalOpcode.zero +
      BinaryRationalArithmetic.lessEqualWork
        (BinaryPRGHeapStoredTree.readWithWork limits address.word).1
        (bids.readWithWork address.word).1 := by
  simp only [fractionalWithWork,
    BinaryPRGHeapPackedLifetime.readWithTrace_erasure,
    BinaryPRGHeapPackedStore.Packed.readWithWork]
  rfl

def scanWithWork (limits : Stored capacity.tree) (bids : Packed capacity.width) :
    List (Address capacity.width capacity.cap) →
      (List (Address capacity.width capacity.cap) × Trace) × ℕ
  | [] => (([],wrap 8 1 []),0)
  | address :: rest =>
      let tested := fractionalWithWork limits bids address
      let later := scanWithWork limits bids rest
      ((if tested.1.1 then address :: later.1.1 else later.1.1,
          wrapList (if tested.1.1 then 1 else 0) 8 2 [tested.1.2,later.1.2]),
        tested.2+later.2)

theorem scanWithWork_erases (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithWork limits bids addresses).1 =
      BinaryPRGHeapScanLifetime.scanWithTrace limits bids addresses := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      simp only [scanWithWork,BinaryPRGHeapScanLifetime.scanWithTrace,
        fractionalWithWork_erases,ih]

theorem scanWithWork_cost (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithWork limits bids addresses).2 =
      (addresses.map (fun address =>
        BinaryRationalArithmetic.lessEqualWork
          (bids.readWithWork address.word).1 BinaryRationalOpcode.zero +
        BinaryRationalArithmetic.lessEqualWork
          (BinaryPRGHeapStoredTree.readWithWork limits address.word).1
          (bids.readWithWork address.word).1)).sum := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      simp only [scanWithWork,List.map_cons,List.sum_cons,
        fractionalWithWork_native_comparisons,ih]

theorem fractionalWithWork_bound (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) (W : ℕ)
    (hBid : width (bids.readWithWork address.word).1 ≤ W)
    (hLimit : width (BinaryPRGHeapStoredTree.readWithWork limits address.word).1 ≤ W)
    (hZero : width BinaryRationalOpcode.zero ≤ W) :
    (fractionalWithWork limits bids address).2 ≤ 1000*(W+1)^2 := by
  rw [fractionalWithWork_native_comparisons]
  have hFirst := BinaryRationalArithmetic.lessEqualWork_bound
    (bids.readWithWork address.word).1 BinaryRationalOpcode.zero
  have hSecond := BinaryRationalArithmetic.lessEqualWork_bound
    (BinaryPRGHeapStoredTree.readWithWork limits address.word).1
    (bids.readWithWork address.word).1
  have hPairFirst : BinaryRationalArithmetic.pairWidth
      (bids.readWithWork address.word).1 BinaryRationalOpcode.zero ≤ W := max_le hBid hZero
  have hPairSecond : BinaryRationalArithmetic.pairWidth
      (BinaryPRGHeapStoredTree.readWithWork limits address.word).1
      (bids.readWithWork address.word).1 ≤ W := max_le hLimit hBid
  have hPowFirst := Nat.pow_le_pow_left (Nat.add_le_add_right hPairFirst 1) 2
  have hPowSecond := Nat.pow_le_pow_left (Nat.add_le_add_right hPairSecond 1) 2
  nlinarith

theorem fractionalWithWork_charge_decomposition (limits : Stored capacity.tree)
    (bids : Packed capacity.width) (address : Address capacity.width capacity.cap) :
    (BinaryPRGHeapResourceLoop.fractionalWithWork limits bids address).2 =
      (fractionalWithWork limits bids address).2 +
        (bids.readWithWork address.word).2.work +
        (BinaryPRGHeapStoredTree.readWithWork limits address.word).2.work + 6 := by
  rw [fractionalWithWork_native_comparisons]
  unfold BinaryPRGHeapResourceLoop.fractionalWithWork
  dsimp only
  omega

theorem scanWithWork_charge_decomposition (limits : Stored capacity.tree)
    (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (BinaryPRGHeapResourceLoop.scanWithWork limits bids addresses).2 =
      (scanWithWork limits bids addresses).2 +
        (addresses.map (fun address =>
          (bids.readWithWork address.word).2.work +
          (BinaryPRGHeapStoredTree.readWithWork limits address.word).2.work + 6 +
          2*(address.word.bits.length+1)+3)).sum + 1 := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      have hHead := fractionalWithWork_charge_decomposition limits bids address
      simp only [BinaryPRGHeapResourceLoop.scanWithWork,scanWithWork,
        List.map_cons,List.sum_cons] at *
      omega

theorem scanWithWork_bound (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) (W : ℕ)
    (hBid : ∀ address ∈ addresses,width (bids.readWithWork address.word).1 ≤ W)
    (hLimit : ∀ address ∈ addresses,
      width (BinaryPRGHeapStoredTree.readWithWork limits address.word).1 ≤ W)
    (hZero : width BinaryRationalOpcode.zero ≤ W) :
    (scanWithWork limits bids addresses).2 ≤ addresses.length*1000*(W+1)^2 := by
  induction addresses with
  | nil => simp [scanWithWork]
  | cons address rest ih =>
      have hHead := fractionalWithWork_bound limits bids address W
        (hBid address (by simp)) (hLimit address (by simp)) hZero
      have hTail := ih (by intro item hm; exact hBid item (by simp [hm]))
        (by intro item hm; exact hLimit item (by simp [hm]))
      simp only [scanWithWork,List.length_cons]
      nlinarith

/-- The reached comparison trace also carries the physical read and list
control work charged by the source-level heap scan. Both ledgers use the
same tested words and active-list decision. -/
def fractionalWithFullWork (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) : (Bool × Trace) × (ℕ × ℕ) :=
  let measured := fractionalWithWork limits bids address
  (measured.1,(measured.2,
    measured.2 + (bids.readWithWork address.word).2.work +
      (BinaryPRGHeapStoredTree.readWithWork limits address.word).2.work + 6))

theorem fractionalWithFullWork_erases (limits : Stored capacity.tree)
    (bids : Packed capacity.width) (address : Address capacity.width capacity.cap) :
    (fractionalWithFullWork limits bids address).1 =
      BinaryPRGHeapScanLifetime.fractionalWithTrace limits bids address := by
  exact fractionalWithWork_erases limits bids address

theorem fractionalWithFullWork_comparison (limits : Stored capacity.tree)
    (bids : Packed capacity.width) (address : Address capacity.width capacity.cap) :
    (fractionalWithFullWork limits bids address).2.1 =
      (fractionalWithWork limits bids address).2 := by rfl

theorem fractionalWithFullWork_charge (limits : Stored capacity.tree)
    (bids : Packed capacity.width) (address : Address capacity.width capacity.cap) :
    (fractionalWithFullWork limits bids address).2.2 =
      (BinaryPRGHeapResourceLoop.fractionalWithWork limits bids address).2 := by
  rw [fractionalWithWork_charge_decomposition]
  rfl

def scanWithFullWork (limits : Stored capacity.tree) (bids : Packed capacity.width) :
    List (Address capacity.width capacity.cap) →
      (List (Address capacity.width capacity.cap) × Trace) × (ℕ × ℕ)
  | [] => (([],wrap 8 1 []),(0,1))
  | address :: rest =>
      let tested := fractionalWithFullWork limits bids address
      let later := scanWithFullWork limits bids rest
      ((if tested.1.1 then address :: later.1.1 else later.1.1,
          wrapList (if tested.1.1 then 1 else 0) 8 2 [tested.1.2,later.1.2]),
        (tested.2.1+later.2.1,
          tested.2.2+later.2.2+2*(address.word.bits.length+1)+3))

theorem scanWithFullWork_erases (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithFullWork limits bids addresses).1 =
      BinaryPRGHeapScanLifetime.scanWithTrace limits bids addresses := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      simp only [scanWithFullWork,BinaryPRGHeapScanLifetime.scanWithTrace,
        fractionalWithFullWork_erases,ih]

theorem scanWithFullWork_comparison (limits : Stored capacity.tree)
    (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithFullWork limits bids addresses).2.1 =
      (scanWithWork limits bids addresses).2 := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      simp only [scanWithFullWork,scanWithWork,
        fractionalWithFullWork_comparison,ih]

theorem scanWithFullWork_charge (limits : Stored capacity.tree)
    (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithFullWork limits bids addresses).2.2 =
      (BinaryPRGHeapResourceLoop.scanWithWork limits bids addresses).2 := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      simp only [scanWithFullWork,BinaryPRGHeapResourceLoop.scanWithWork,
        fractionalWithFullWork_charge,ih]

theorem scanWithFullWork_bound (limits : Stored capacity.tree)
    (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithFullWork limits bids addresses).2.2 ≤
      BinaryPRGHeapResourceLoop.scanWorkBound limits bids addresses := by
  rw [scanWithFullWork_charge]
  exact BinaryPRGHeapResourceLoop.scanWithWork_bound limits bids addresses

end Blotto.BinaryPRGHeapScanComparisonWork
