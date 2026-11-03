import Blotto.BinaryPRGNumericalPreparationLifetime
import Blotto.BinaryLifetimeFlattenControl
import Blotto.BinaryQuadraticTraceLength

/-! Original-input event counts for the two reached numerical trace flattens. -/
namespace Blotto.BinaryPRGNumericalFlattenLength
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGPreparation BinaryPRGRecognition BinaryPRGNumericalPreparationLifetime
open BinaryLifetimeFlattenControl
open BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem entries_payload_bound {α : Type*} (entries : List (α × Trace)) (B : ℕ)
    (h : ∀ entry ∈ entries, entry.2.length ≤ B) :
    payloadCount (BinaryLifetimeArray.mapDirect Prod.snd entries) ≤ entries.length * B := by
  induction entries with
  | nil => simp [payloadCount,BinaryLifetimeArray.mapDirect]
  | cons entry rest ih =>
      have he := h entry (by simp)
      have hr := ih (fun item hi => h item (by simp [hi]))
      simp only [payloadCount,BinaryLifetimeArray.mapDirect,List.map_cons,List.sum_cons,
        List.length_cons] at hr ⊢
      simp only [Nat.add_mul,one_mul]
      omega

theorem mapped_payload_bound {α β : Type*} (rows : List α)
    (produce : α → β × Trace) (B : ℕ)
    (h : ∀ row ∈ rows, (produce row).2.length ≤ B) :
    payloadCount (BinaryLifetimeArray.mapDirect Prod.snd
      (BinaryLifetimeArray.mapDirect produce rows)) ≤ rows.length * B := by
  have hb := entries_payload_bound (BinaryLifetimeArray.mapDirect produce rows) B (by
    intro entry he
    rw [BinaryLifetimeArray.mapDirect_eq_map] at he
    obtain ⟨row,hr,rfl⟩ := List.mem_map.mp he
    exact h row hr)
  rw [BinaryLifetimeArray.mapDirect_length] at hb
  exact hb

def widthBound {n : ℕ} (input : Input n) : ℕ :=
  3 * BinaryPRGPreparationWork.storedInputWidth input + 1

theorem length_entries_payload_bound {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    let entries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    payloadCount (BinaryLifetimeArray.mapDirect Prod.snd entries) ≤
      n * (2 * BinaryQuadraticLifetime.opcodeBound (widthBound input)) := by
  dsimp only
  have hw := BinaryPRGPreparationWork.original_widths input
  have hTwo : width two ≤ widthBound input := by
    change 2 ≤ 3 * BinaryPRGPreparationWork.storedInputWidth input + 1
    omega
  have hValue : ∀ row ∈ rows, width row ≤ widthBound input := by
    intro row hr
    rw [hRows] at hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact (hw.2.2.1 j).trans (by simp [widthBound]; omega)
  have hb := mapped_payload_bound rows
    (BinaryQuadraticLifetime.applyWithTrace .mul two)
    (2 * BinaryQuadraticLifetime.opcodeBound (widthBound input))
    (fun row hr => BinaryQuadraticTraceLength.apply_event_bound .mul two row
      (widthBound input) hTwo (hValue row hr))
  have hLength : rows.length = n := by rw [hRows]; simp
  rw [hLength] at hb
  exact hb

theorem poor_entries_payload_bound {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    payloadCount (BinaryLifetimeArray.mapDirect Prod.snd poorEntries) ≤
      n * (2 * BinaryQuadraticLifetime.opcodeBound (widthBound input)) := by
  dsimp only
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengthEntries := BinaryLifetimeArray.mapDirect
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  have hRatio : width ratio.1 ≤ widthBound input := by
    have h := BinaryQuadraticLifetime.applyWithTrace_state .div input.b input.a
      hC.2.1.1 hC.1.1
    change width ratio.1 ≤ widthBound input
    rw [h]
    change width (prepare input).ratio ≤ widthBound input
    exact BinaryPRGPreparationWork.ratio_width input
  have hEntries : lengthEntries = List.ofFn (fun j : Fin n =>
      BinaryQuadraticLifetime.applyWithTrace .mul two (input.values.read j)) := by
    dsimp only [lengthEntries]
    rw [hRows,BinaryLifetimeArray.mapDirect_eq_map,List.map_ofFn]
    rfl
  have hLengthEntry : ∀ item ∈ lengthEntries, width item.1 ≤ widthBound input := by
    intro item hi
    rw [hEntries] at hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    rw [BinaryQuadraticLifetime.applyWithTrace_state .mul two (input.values.read j)
      two_canonical.1 (hC.2.2 j).1]
    simpa only [widthBound,prepare,FixedArrayTable.read_ofFn] using
      BinaryPRGPreparationWork.lengths_width input j
  have hb := mapped_payload_bound lengthEntries
    (fun item => BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1)
    (2 * BinaryQuadraticLifetime.opcodeBound (widthBound input))
    (fun item hi => BinaryQuadraticTraceLength.apply_event_bound .mul ratio.1 item.1
      (widthBound input) hRatio (hLengthEntry item hi))
  have hLength : lengthEntries.length = n := by
    rw [hEntries]
    simp
  rw [hLength] at hb
  exact hb

theorem prepareWithRows_flatten_reserve {n : ℕ} (input : Input n)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    flattenListReserve n (BinaryPRGPreparationWork.storedInputWidth input) ≤
      listCells (prepareWithRows input rows hRows).2 ∧
    flattenArrayReserve n (BinaryPRGPreparationWork.storedInputWidth input) ≤
      arraySlots (prepareWithRows input rows hRows).2 := by
  unfold prepareWithRows
  dsimp only
  constructor
  · simp [wrapList,wrap,listCells]
    omega
  · simp [wrapList,wrap,arraySlots]
    omega

theorem prepareWithRows_flatten_payload_covered {n : ℕ} (input : Input n)
    (hC : input.Canonical) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    payloadCount (BinaryLifetimeArray.mapDirect Prod.snd lengthEntries) +
      payloadCount (BinaryLifetimeArray.mapDirect Prod.snd poorEntries) ≤
        listCells (prepareWithRows input rows hRows).2 := by
  dsimp only
  have hOne := length_entries_payload_bound input rows hRows
  have hTwo := poor_entries_payload_bound input hC rows hRows
  have hReserve := (prepareWithRows_flatten_reserve input rows hRows).1
  change _ ≤ n*(2*BinaryQuadraticLifetime.opcodeBound (widthBound input)) at hOne hTwo
  have hBudget : flattenListReserve n (BinaryPRGPreparationWork.storedInputWidth input) =
      4*(n*(2*BinaryQuadraticLifetime.opcodeBound (widthBound input))) := by
    unfold flattenListReserve flattenSinglePayloadBound widthBound
    ring
  rw [hBudget] at hReserve
  omega

theorem prepareWithRows_direct_flatten_cons_covered {n : ℕ} (input : Input n)
    (hC : input.Canonical) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    let lengthLists := BinaryLifetimeArray.mapDirect Prod.snd lengthEntries
    let poorLists := BinaryLifetimeArray.mapDirect Prod.snd poorEntries
    (BinaryLifetimeFlattenList.gatherWithCount lengthLists []).2 +
      (BinaryLifetimeFlattenList.gatherWithCount poorLists []).2 ≤
        listCells (prepareWithRows input rows hRows).2 := by
  dsimp only
  have hOne := length_entries_payload_bound input rows hRows
  have hTwo := poor_entries_payload_bound input hC rows hRows
  have hReserve := (prepareWithRows_flatten_reserve input rows hRows).1
  change _ ≤ n*(2*BinaryQuadraticLifetime.opcodeBound (widthBound input)) at hOne hTwo
  have hBudget : flattenListReserve n (BinaryPRGPreparationWork.storedInputWidth input) =
      4*(n*(2*BinaryQuadraticLifetime.opcodeBound (widthBound input))) := by
    unfold flattenListReserve flattenSinglePayloadBound widthBound
    ring
  rw [hBudget] at hReserve
  rw [BinaryLifetimeFlattenList.gatherWithCount_count,
    BinaryLifetimeFlattenList.gatherWithCount_count]
  simp only [List.length_nil,Nat.add_zero,BinaryLifetimeFlattenList.payloadCount,
    payloadCount] at hOne hTwo ⊢
  omega

theorem prepareWithRows_flatten_slots_covered {n : ℕ} (input : Input n)
    (hC : input.Canonical) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    let lengthLists := BinaryLifetimeArray.mapDirect Prod.snd lengthEntries
    let poorLists := BinaryLifetimeArray.mapDirect Prod.snd poorEntries
    NativeArrayConversionControl.prefixSlots
      (NativeArrayConversionCore.pushLoop lengthLists.flatten #[]).2 +
    NativeArrayConversionControl.prefixSlots
      (NativeArrayConversionCore.pushLoop poorLists.flatten #[]).2 ≤
      arraySlots (prepareWithRows input rows hRows).2 := by
  dsimp only
  let S := BinaryPRGPreparationWork.storedInputWidth input
  let B := flattenSinglePayloadBound n S
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengthEntries := BinaryLifetimeArray.mapDirect
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
  let lengthLists := BinaryLifetimeArray.mapDirect Prod.snd lengthEntries
  let poorLists := BinaryLifetimeArray.mapDirect Prod.snd poorEntries
  have hT1 : payloadCount lengthLists ≤ B := by
    have hRaw := length_entries_payload_bound input rows hRows
    change payloadCount lengthLists ≤ n*(2*BinaryQuadraticLifetime.opcodeBound
      (widthBound input)) at hRaw
    calc
      _ ≤ n*(2*BinaryQuadraticLifetime.opcodeBound (widthBound input)) := hRaw
      _ = B := by unfold B S flattenSinglePayloadBound widthBound; ring
  have hT2 : payloadCount poorLists ≤ B := by
    have hRaw := poor_entries_payload_bound input hC rows hRows
    change payloadCount poorLists ≤ n*(2*BinaryQuadraticLifetime.opcodeBound
      (widthBound input)) at hRaw
    calc
      _ ≤ n*(2*BinaryQuadraticLifetime.opcodeBound (widthBound input)) := hRaw
      _ = B := by unfold B S flattenSinglePayloadBound widthBound; ring
  have hp1 := (selected_flatten_push_control lengthLists).2
  have hp2 := (selected_flatten_push_control poorLists).2
  have hSq1 : (payloadCount lengthLists+1)^2 ≤ (B+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hSq2 : (payloadCount poorLists+1)^2 ≤ (B+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hReserve := (prepareWithRows_flatten_reserve input rows hRows).2
  change 2*(B+1)^2 ≤ arraySlots (prepareWithRows input rows hRows).2 at hReserve
  have hSum : NativeArrayConversionControl.prefixSlots
      (NativeArrayConversionCore.pushLoop lengthLists.flatten #[]).2 +
      NativeArrayConversionControl.prefixSlots
      (NativeArrayConversionCore.pushLoop poorLists.flatten #[]).2 ≤ 2*(B+1)^2 := by
    calc
      _ ≤ (payloadCount lengthLists+1)^2+(payloadCount poorLists+1)^2 :=
        Nat.add_le_add hp1 hp2
      _ ≤ (B+1)^2+(B+1)^2 := Nat.add_le_add hSq1 hSq2
      _ = 2*(B+1)^2 := by ring
  exact hSum.trans hReserve

end Blotto.BinaryPRGNumericalFlattenLength
