import Blotto.BinaryPRGNumericalFlattenRaw
import Blotto.NativeArrayConversionControl

/-! The two selected numerical output tables use `packEntries`, whose
initializer is exactly `Array.mkEmpty n`. These source certificates follow
that initializer and its reached push sequence. Native ownership, physical
capacity and reference-bit transport remain separate backend contracts. -/
namespace Blotto.BinaryPRGNumericalPackControl
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGPreparation BinaryPRGRecognition
open NativeArrayConversionCore NativeArrayConversionControl
set_option autoImplicit false

theorem fromEntries_actual_pack {α : Type*} (n : ℕ)
    (entries : List (α × Trace)) (hEntries : entries.length = n) :
    let items := BinaryLifetimeArray.mapDirect Prod.fst entries
    let snapshots := (pushLoop items (Array.mkEmpty n)).2
    (BinaryLifetimeArray.fromEntries n entries hEntries).1.data =
      (pushLoop items (Array.mkEmpty n)).1 ∧
    snapshots.filterMap PushSnapshot.pushIndex = List.range n ∧
    prefixSlots snapshots ≤ (n+1)^2 ∧
    ((BooleanArrayIndexEnumeration.enumerateWithTrace items).1.map
      BinaryCarryCounter.value) = snapshots.filterMap PushSnapshot.pushIndex ∧
    (∀ s ∈ snapshots, ∀ value ∈ s.operands n,
      binaryWordWidth value ≤ binaryWordWidth (n+1)) := by
  dsimp only
  let items := BinaryLifetimeArray.mapDirect Prod.fst entries
  let snapshots := (pushLoop items (Array.mkEmpty n)).2
  have hLength : items.length = n := by
    dsimp only [items]
    rw [BinaryLifetimeArray.mapDirect_length,hEntries]
  have hValid : ∀ s ∈ snapshots, s.Valid n :=
    pushLoop_valid items (Array.mkEmpty n) n (by simp [hLength])
  have hData : (BinaryLifetimeArray.fromEntries n entries hEntries).1.data =
      (pushLoop items (Array.mkEmpty n)).1 := by
    change BinaryLifetimeArray.packEntries n items = _
    exact BinaryLifetimeArray.packEntries_pushLoop n items
  have hIndices : snapshots.filterMap PushSnapshot.pushIndex = List.range n := by
    have h := pushLoop_indices items (Array.mkEmpty n)
    simpa only [hLength,show (Array.mkEmpty n : Array α).size = 0 from rfl,
      List.range_eq_range'] using h
  have hSlots : prefixSlots snapshots ≤ (n+1)^2 := by
    have h := prefixSlots_bound n snapshots hValid
    rw [show snapshots.length = n+1 by
      rw [show snapshots = (pushLoop items (Array.mkEmpty n)).2 from rfl,
        pushLoop_length,hLength]] at h
    nlinarith
  have hBoolean :
      ((BooleanArrayIndexEnumeration.enumerateWithTrace items).1.map
        BinaryCarryCounter.value) = snapshots.filterMap PushSnapshot.pushIndex := by
    rw [BooleanArrayIndexEnumeration.enumerate_values,hLength,hIndices]
  have hWidths : ∀ s ∈ snapshots, ∀ value ∈ s.operands n,
      binaryWordWidth value ≤ binaryWordWidth (n+1) := by
    intro s hs value hv
    exact binaryWordWidth_mono ((PushSnapshot.operand_bound (hValid s hs)) value hv)
  exact ⟨hData,hIndices,hSlots,hBoolean,hWidths⟩

theorem prepareWithRows_pack_prefixSlots_covered {n : ℕ}
    (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    let lengthItems := BinaryLifetimeArray.mapDirect Prod.fst lengthEntries
    let poorItems := BinaryLifetimeArray.mapDirect Prod.fst poorEntries
    prefixSlots (pushLoop lengthItems (Array.mkEmpty n)).2 +
      prefixSlots (pushLoop poorItems (Array.mkEmpty n)).2 ≤
        arraySlots (BinaryPRGNumericalPreparationLifetime.prepareWithRows
          input rows hRows).2 := by
  dsimp only
  let lengthEntries := BinaryLifetimeArray.mapDirect
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul
      (BinaryQuadraticLifetime.applyWithTrace .div input.b input.a).1 item.1) lengthEntries
  have hLength : lengthEntries.length = n := by
    dsimp only [lengthEntries]
    rw [BinaryLifetimeArray.mapDirect_length,hRows,List.length_ofFn]
  have hPoor : poorEntries.length = n := by
    dsimp only [poorEntries]
    rw [BinaryLifetimeArray.mapDirect_length,hLength]
  have hFirst := (fromEntries_actual_pack n lengthEntries hLength).2.2.1
  have hSecond := (fromEntries_actual_pack n poorEntries hPoor).2.2.1
  dsimp only [lengthEntries,poorEntries] at hFirst hSecond
  have hTrace : 2*(n+1)^2 ≤
      arraySlots (BinaryPRGNumericalPreparationLifetime.prepareWithRows input rows hRows).2 := by
    unfold BinaryPRGNumericalPreparationLifetime.prepareWithRows
    dsimp only
    simp only [BinaryPRGHeapTraceUsage.wrapList,BinaryPRGHeapTraceUsage.wrap,
      BinaryPRGHeapTraceUsage.combine,BinaryLifetimeArray.fromEntries,
      BinarySeedPreparationSpace.arraySlots_append,
      BinarySeedPreparationSpace.arraySlots_under,
      BinarySeedPreparationSpace.arraySlots]
    omega
  omega

theorem parsed_two_packs_raw_control (bits : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed) :
    let input := parsed.1.2.game.input
    let rows := parsed.1.2.rows
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    let lengthItems := BinaryLifetimeArray.mapDirect Prod.fst lengthEntries
    let poorItems := BinaryLifetimeArray.mapDirect Prod.fst poorEntries
    prefixSlots (pushLoop lengthItems (Array.mkEmpty parsed.1.1)).2 +
      prefixSlots (pushLoop poorItems (Array.mkEmpty parsed.1.1)).2 ≤
        2*(bits.length+1)^2 ∧
    (∀ word ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace lengthItems).1,
      word.length ≤ binaryWordWidth (bits.length+1)) ∧
    (∀ word ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace poorItems).1,
      word.length ≤ binaryWordWidth (bits.length+1)) := by
  dsimp only
  let n := parsed.1.1
  let input := parsed.1.2.game.input
  let rows := parsed.1.2.rows
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengthEntries := BinaryLifetimeArray.mapDirect
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
  let lengthItems := BinaryLifetimeArray.mapDirect Prod.fst lengthEntries
  let poorItems := BinaryLifetimeArray.mapDirect Prod.fst poorEntries
  have hn : n ≤ bits.length := (BinaryPRGCheckedGameLifetime.parsed_sizes bits parsed h).1
  have hLength : lengthEntries.length = n := by
    dsimp only [lengthEntries,rows,n]
    rw [BinaryLifetimeArray.mapDirect_length,parsed.1.2.rows_length]
  have hPoor : poorEntries.length = n := by
    dsimp only [poorEntries]
    rw [BinaryLifetimeArray.mapDirect_length,hLength]
  have hItemsLength : lengthItems.length = n := by
    dsimp only [lengthItems]
    rw [BinaryLifetimeArray.mapDirect_length,hLength]
  have hItemsPoor : poorItems.length = n := by
    dsimp only [poorItems]
    rw [BinaryLifetimeArray.mapDirect_length,hPoor]
  have hSlots1 := (fromEntries_actual_pack n lengthEntries hLength).2.2.1
  have hSlots2 := (fromEntries_actual_pack n poorEntries hPoor).2.2.1
  dsimp only [lengthEntries,poorEntries,ratio,input,rows,n] at hSlots1 hSlots2
  have hPower : (n+1)^2 ≤ (bits.length+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  dsimp only [n] at hPower
  have hSlotBound : prefixSlots (pushLoop lengthItems (Array.mkEmpty n)).2 +
      prefixSlots (pushLoop poorItems (Array.mkEmpty n)).2 ≤ 2*(bits.length+1)^2 := by
    dsimp only [lengthItems,poorItems,lengthEntries,poorEntries,ratio,input,rows,n]
    omega
  have hWord1 : ∀ word ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace lengthItems).1,
      word.length ≤ binaryWordWidth (bits.length+1) := by
    intro word hw
    have hWidth := BooleanArrayIndexEnumeration.enumerate_width lengthItems word hw
    rw [hItemsLength] at hWidth
    exact hWidth.trans (binaryWordWidth_mono (by omega))
  have hWord2 : ∀ word ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace poorItems).1,
      word.length ≤ binaryWordWidth (bits.length+1) := by
    intro word hw
    have hWidth := BooleanArrayIndexEnumeration.enumerate_width poorItems word hw
    rw [hItemsPoor] at hWidth
    exact hWidth.trans (binaryWordWidth_mono (by omega))
  exact ⟨hSlotBound,hWord1,hWord2⟩

end Blotto.BinaryPRGNumericalPackControl
