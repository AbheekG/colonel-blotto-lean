import Blotto.BinaryPRGPromiseLifetime

/-! Actual quadratic ratio, doubled-length and poor-resource construction.
The selected checked path maps the retained parser row once into length
value/trace pairs, then maps those pairs once into poor-resource pairs.
Each array consumes the retained pairs without recomputing its producer.
The old native-array reader and the intermediate indexed-list variant remain
references. All produced word payloads and array versions stay reserved. -/
namespace Blotto.BinaryPRGNumericalPreparationLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition BinaryPRGPreparation
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryLifetimeUsage
open scoped BigOperators
set_option maxHeartbeats 3000000

def flattenSinglePayloadBound (n S : ℕ) : ℕ :=
  2*n*BinaryQuadraticLifetime.opcodeBound (3*S+1)

def flattenListReserve (n S : ℕ) : ℕ :=
  4*flattenSinglePayloadBound n S

def flattenArrayReserve (n S : ℕ) : ℕ :=
  2*(flattenSinglePayloadBound n S+1)^2

theorem flattenSinglePayloadBound_mono {n m S T : ℕ} (hn : n ≤ m) (hS : S ≤ T) :
    flattenSinglePayloadBound n S ≤ flattenSinglePayloadBound m T := by
  unfold flattenSinglePayloadBound BinaryQuadraticLifetime.opcodeBound
  gcongr

theorem flattenListReserve_mono {n m S T : ℕ} (hn : n ≤ m) (hS : S ≤ T) :
    flattenListReserve n S ≤ flattenListReserve m T := by
  unfold flattenListReserve
  exact Nat.mul_le_mul_left 4 (flattenSinglePayloadBound_mono hn hS)

theorem flattenArrayReserve_mono {n m S T : ℕ} (hn : n ≤ m) (hS : S ≤ T) :
    flattenArrayReserve n S ≤ flattenArrayReserve m T := by
  unfold flattenArrayReserve
  gcongr
  exact flattenSinglePayloadBound_mono hn hS

def prepareWithTrace {n : ℕ} (input : Input n) : Prepared n × Trace :=
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengths := BinaryLifetimeArray.build n (fun j => BinaryQuadraticLifetime.applyWithTrace .mul two (input.values.read j))
  let poor := BinaryLifetimeArray.build n (fun j => BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 (lengths.1.read j))
  (⟨input,ratio.1,lengths.1,poor.1⟩,
    wrapList (6*n+flattenListReserve n (BinaryPRGPreparationWork.storedInputWidth input))
      (64+flattenArrayReserve n (BinaryPRGPreparationWork.storedInputWidth input))
      (n+4) [ratio.2,lengths.2,poor.2])

def rowGet {α : Type*} : (items : List α) → Fin items.length → α
  | [], index => nomatch index
  | item::_, ⟨0,_⟩ => item
  | _::rest, ⟨index+1,h⟩ =>
      rowGet rest ⟨index,by simp at h; omega⟩

theorem rowGet_state {α : Type*} (items : List α) (index : Fin items.length) :
    rowGet items index = items[index.val]'index.isLt := by
  induction items with
  | nil => exact Fin.elim0 index
  | cons item rest ih =>
      rcases index with ⟨position,h⟩
      cases position with
      | zero => rfl
      | succ position =>
          simpa only [rowGet,List.getElem_cons_succ] using
            ih ⟨position,by simp at h; omega⟩

def prepareWithRows {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) : Prepared n × Trace :=
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengthEntries := BinaryLifetimeArray.mapDirect (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let lengths := BinaryLifetimeArray.fromEntries n lengthEntries (by simp [lengthEntries,BinaryLifetimeArray.mapDirect_length,hRows])
  let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1)
    lengthEntries
  let poor := BinaryLifetimeArray.fromEntries n poorEntries (by simp [poorEntries,lengthEntries,BinaryLifetimeArray.mapDirect_length,hRows])
  (⟨input,ratio.1,lengths.1,poor.1⟩,
    wrapList (6*n+flattenListReserve n (BinaryPRGPreparationWork.storedInputWidth input))
      (64+flattenArrayReserve n (BinaryPRGPreparationWork.storedInputWidth input))
      (n+4) [ratio.2,lengths.2,poor.2])

theorem prepareWithRows_eq {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    prepareWithRows input rows hRows = prepareWithTrace input := by
  subst rows
  simp only [prepareWithRows,BinaryLifetimeArray.mapDirect_eq_map,prepareWithTrace,List.map_ofFn,Function.comp_def,
    BinaryLifetimeArray.fromEntries_ofFn,BinaryLifetimeArray.build_erases,
    FixedArrayTable.read_ofFn]

theorem prepareWithRows_map_visits {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1)
      lengthEntries
    (BinaryLifetimeArray.mapWithVisits (BinaryQuadraticLifetime.applyWithTrace .mul two) rows).2 +
    (BinaryLifetimeArray.mapWithVisits (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries).2 +
    (BinaryLifetimeArray.mapWithVisits Prod.fst lengthEntries).2 +
    (BinaryLifetimeArray.mapWithVisits Prod.snd lengthEntries).2 +
    (BinaryLifetimeArray.mapWithVisits Prod.fst poorEntries).2 +
    (BinaryLifetimeArray.mapWithVisits Prod.snd poorEntries).2 = 6*n := by
  dsimp only
  simp only [BinaryLifetimeArray.mapWithVisits_visits,BinaryLifetimeArray.mapDirect_length,hRows,List.length_ofFn]
  omega

theorem prepareWithRows_map_cells {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    listCells (BinaryLifetimeArray.mapDirectWithTrace
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows).2 +
    listCells (BinaryLifetimeArray.mapDirectWithTrace (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries).2 +
    listCells (BinaryLifetimeArray.mapDirectWithTrace Prod.fst lengthEntries).2 +
    listCells (BinaryLifetimeArray.mapDirectWithTrace Prod.snd lengthEntries).2 +
    listCells (BinaryLifetimeArray.mapDirectWithTrace Prod.fst poorEntries).2 +
    listCells (BinaryLifetimeArray.mapDirectWithTrace Prod.snd poorEntries).2 = 6*n := by
  dsimp only
  simp only [BinaryLifetimeArray.mapDirectWithTrace_cells,BinaryLifetimeArray.mapDirect_length,
    hRows,List.length_ofFn]
  omega

theorem prepareWithRows_map_reservation {n : ℕ} (input : Input n)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    6*n ≤ listCells (prepareWithRows input rows hRows).2 ∧
    n+4 ≤ framePeak (prepareWithRows input rows hRows).2 := by
  unfold prepareWithRows
  dsimp only
  constructor
  · simp [wrapList,wrap,listCells]
    omega
  · simp [wrapList,wrap,framePeak]

theorem prepareWithRows_map_cells_covered {n : ℕ} (input : Input n)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    listCells (BinaryLifetimeArray.mapDirectWithTrace
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows).2 +
    listCells (BinaryLifetimeArray.mapDirectWithTrace (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries).2 +
    listCells (BinaryLifetimeArray.mapDirectWithTrace Prod.fst lengthEntries).2 +
    listCells (BinaryLifetimeArray.mapDirectWithTrace Prod.snd lengthEntries).2 +
    listCells (BinaryLifetimeArray.mapDirectWithTrace Prod.fst poorEntries).2 +
    listCells (BinaryLifetimeArray.mapDirectWithTrace Prod.snd poorEntries).2 ≤
      listCells (prepareWithRows input rows hRows).2 := by
  have hCells := prepareWithRows_map_cells input rows hRows
  have hReserved := (prepareWithRows_map_reservation input rows hRows).1
  dsimp only at hCells ⊢
  rw [hCells]
  exact hReserved

theorem prepareWithRows_map_frames_covered {n : ℕ} (input : Input n)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    framePeak (BinaryLifetimeArray.mapDirectWithTrace
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows).2 + 2 ≤
        framePeak (prepareWithRows input rows hRows).2 ∧
    framePeak (BinaryLifetimeArray.mapDirectWithTrace (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries).2 + 2 ≤
        framePeak (prepareWithRows input rows hRows).2 ∧
    framePeak (BinaryLifetimeArray.mapDirectWithTrace Prod.fst lengthEntries).2 + 2 ≤
        framePeak (prepareWithRows input rows hRows).2 ∧
    framePeak (BinaryLifetimeArray.mapDirectWithTrace Prod.snd lengthEntries).2 + 2 ≤
        framePeak (prepareWithRows input rows hRows).2 ∧
    framePeak (BinaryLifetimeArray.mapDirectWithTrace Prod.fst poorEntries).2 + 2 ≤
        framePeak (prepareWithRows input rows hRows).2 ∧
    framePeak (BinaryLifetimeArray.mapDirectWithTrace Prod.snd poorEntries).2 + 2 ≤
        framePeak (prepareWithRows input rows hRows).2 := by
  dsimp only
  have hRowLength : rows.length = n := by rw [hRows]; simp
  have hLengthEntries : (BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows).length = n := by
    rw [BinaryLifetimeArray.mapDirect_length,hRowLength]
  have hPoorEntries : (BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul
        (BinaryQuadraticLifetime.applyWithTrace .div input.b input.a).1 item.1)
      (BinaryLifetimeArray.mapDirect (BinaryQuadraticLifetime.applyWithTrace .mul two) rows)).length = n := by
    rw [BinaryLifetimeArray.mapDirect_length,hLengthEntries]
  have hReserve := (prepareWithRows_map_reservation input rows hRows).2
  have h1 := BinaryLifetimeArray.mapDirectWithTrace_frames
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  have h2 := BinaryLifetimeArray.mapDirectWithTrace_frames (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul
      (BinaryQuadraticLifetime.applyWithTrace .div input.b input.a).1 item.1)
    (BinaryLifetimeArray.mapDirect (BinaryQuadraticLifetime.applyWithTrace .mul two) rows)
  have h3 := BinaryLifetimeArray.mapDirectWithTrace_frames Prod.fst
    (BinaryLifetimeArray.mapDirect (BinaryQuadraticLifetime.applyWithTrace .mul two) rows)
  have h4 := BinaryLifetimeArray.mapDirectWithTrace_frames Prod.snd
    (BinaryLifetimeArray.mapDirect (BinaryQuadraticLifetime.applyWithTrace .mul two) rows)
  have h5 := BinaryLifetimeArray.mapDirectWithTrace_frames Prod.fst
    (BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul
        (BinaryQuadraticLifetime.applyWithTrace .div input.b input.a).1 item.1)
      (BinaryLifetimeArray.mapDirect (BinaryQuadraticLifetime.applyWithTrace .mul two) rows))
  have h6 := BinaryLifetimeArray.mapDirectWithTrace_frames Prod.snd
    (BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul
        (BinaryQuadraticLifetime.applyWithTrace .div input.b input.a).1 item.1)
      (BinaryLifetimeArray.mapDirect (BinaryQuadraticLifetime.applyWithTrace .mul two) rows))
  rw [hRowLength] at h1
  rw [hLengthEntries] at h2 h3 h4
  rw [hPoorEntries] at h5 h6
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

/-! The following indexed-list measures are retained for the former indexed
variant. The selected preparer above uses sequential maps instead. -/
def rowGetWithWork {α : Type*} : (items : List α) → Fin items.length → α × ℕ
  | [], index => nomatch index
  | item::_, ⟨0,_⟩ => (item,1)
  | _::rest, ⟨index+1,h⟩ =>
      let later := rowGetWithWork rest ⟨index,by simp at h; omega⟩
      (later.1,later.2+1)

theorem rowGetWithWork_state {α : Type*} (items : List α) (index : Fin items.length) :
    (rowGetWithWork items index).1 = items[index.val]'index.isLt := by
  induction items with
  | nil => exact Fin.elim0 index
  | cons item rest ih =>
      rcases index with ⟨position,h⟩
      cases position with
      | zero => rfl
      | succ position =>
          simpa only [rowGetWithWork,List.getElem_cons_succ] using
            ih ⟨position,by simp at h; omega⟩

theorem rowGetWithWork_matches {α : Type*} (items : List α) (index : Fin items.length) :
    (rowGetWithWork items index).1 = rowGet items index := by
  rw [rowGetWithWork_state,rowGet_state]

theorem rowGetWithWork_visits {α : Type*} (items : List α) (index : Fin items.length) :
    (rowGetWithWork items index).2 = index.val+1 := by
  induction items with
  | nil => exact Fin.elim0 index
  | cons item rest ih =>
      rcases index with ⟨position,h⟩
      cases position with
      | zero => rfl
      | succ position =>
          simp only [rowGetWithWork,ih]

def rowIndexWork {α : Type*} (items : List α) : ℕ :=
  ∑ index : Fin items.length, (rowGetWithWork items index).2

theorem rowIndexWork_bound {α : Type*} (items : List α) :
    rowIndexWork items ≤ items.length*(items.length+1) := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun index (_ : index ∈ Finset.univ) =>
    show (rowGetWithWork items index).2 ≤ items.length+1 by
      rw [rowGetWithWork_visits]
      omega)
  change rowIndexWork items ≤ ∑ _ : Fin items.length, (items.length+1) at h
  simpa [rowIndexWork] using h

theorem rowGetWithWork_scalar_width {α : Type*} (items : List α) (index : Fin items.length) :
    binaryWordWidth index.val ≤ binaryWordWidth (items.length+1) :=
  binaryWordWidth_mono (by omega)

/-- Conservative width exposure for the selected loop's zero test, index
update and their constant operands. This does not price native operations. -/
def rowGetWithScalar {α : Type*} : (items : List α) → Fin items.length → α × ℕ
  | [], index => nomatch index
  | item::_, ⟨0,_⟩ => (item,2*binaryWordWidth 0)
  | _::rest, ⟨index+1,h⟩ =>
      let later := rowGetWithScalar rest ⟨index,by simp at h; omega⟩
      (later.1,later.2+3*binaryWordWidth (index+1)+
        binaryWordWidth 0+binaryWordWidth 1)

theorem rowGetWithScalar_state {α : Type*} (items : List α) (index : Fin items.length) :
    (rowGetWithScalar items index).1 = rowGet items index := by
  induction items with
  | nil => exact Fin.elim0 index
  | cons item rest ih =>
      rcases index with ⟨position,h⟩
      cases position with
      | zero => rfl
      | succ position =>
          simpa only [rowGetWithScalar,rowGet] using
            ih ⟨position,by simp at h; omega⟩

theorem rowGetWithScalar_bound {α : Type*} (items : List α) (index : Fin items.length) :
    (rowGetWithScalar items index).2 ≤
      5*(index.val+1)*binaryWordWidth (items.length+1) := by
  induction items with
  | nil => exact Fin.elim0 index
  | cons item rest ih =>
      rcases index with ⟨position,h⟩
      cases position with
      | zero =>
          simp only [rowGetWithScalar,Nat.zero_add]
          have hw := binaryWordWidth_mono (show 0 ≤ (item::rest).length+1 by omega)
          omega
      | succ position =>
          let W := binaryWordWidth ((item::rest).length+1)
          have hLater := ih ⟨position,by simp at h; omega⟩
          have hRestWidth : binaryWordWidth (rest.length+1) ≤ W :=
            binaryWordWidth_mono (by simp)
          have hIndexWidth : binaryWordWidth (position+1) ≤ W :=
            binaryWordWidth_mono (by simp at h; omega)
          have hOneWidth : binaryWordWidth 1 ≤ W :=
            binaryWordWidth_mono (by simp)
          have hZeroWidth : binaryWordWidth 0 ≤ W :=
            binaryWordWidth_mono (by simp)
          have hScaled :
              5*(position+1)*binaryWordWidth (rest.length+1) ≤ 5*(position+1)*W :=
            Nat.mul_le_mul_left _ hRestWidth
          simp only [rowGetWithScalar]
          nlinarith only [hLater,hScaled,hIndexWidth,hZeroWidth,hOneWidth]

def rowScalarWork {α : Type*} (items : List α) : ℕ :=
  ∑ index : Fin items.length, (rowGetWithScalar items index).2

theorem rowScalarWork_bound {α : Type*} (items : List α) :
    rowScalarWork items ≤
      5*items.length*(items.length+1)*binaryWordWidth (items.length+1) := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun index (_ : index ∈ Finset.univ) =>
    show (rowGetWithScalar items index).2 ≤
      5*(items.length+1)*binaryWordWidth (items.length+1) by
      have hi := rowGetWithScalar_bound items index
      have hIndex : index.val+1 ≤ items.length+1 := by omega
      have hMul := Nat.mul_le_mul_right (binaryWordWidth (items.length+1))
        (Nat.mul_le_mul_left 5 hIndex)
      exact hi.trans hMul)
  change rowScalarWork items ≤
    ∑ _ : Fin items.length, 5*(items.length+1)*binaryWordWidth (items.length+1) at h
  simpa [rowScalarWork,mul_assoc,mul_left_comm,mul_comm] using h

theorem prepareWithRows_lookup {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) (j : Fin n) :
    (rowGetWithWork rows ⟨j.val,by rw [hRows]; simp⟩).1 =
      rowGet rows ⟨j.val,by rw [hRows]; simp⟩ ∧
    (rowGetWithWork rows ⟨j.val,by rw [hRows]; simp⟩).2 ≤ n ∧
    binaryWordWidth j.val ≤ binaryWordWidth (n+1) := by
  have hLength : rows.length = n := by rw [hRows]; simp
  refine ⟨rowGetWithWork_matches rows ⟨j.val,by rw [hLength]; exact j.isLt⟩,?_,?_⟩
  · rw [rowGetWithWork_visits]
    omega
  · exact binaryWordWidth_mono (by omega)

theorem prepareWithRows_index_work {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    rowIndexWork rows ≤ n*(n+1) := by
  have h := rowIndexWork_bound rows
  simpa only [hRows,List.length_ofFn] using h

theorem prepareWithRows_all_index_work {n : ℕ} (input : Input n)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    let lengthEntries := List.ofFn (fun j : Fin n =>
      BinaryQuadraticLifetime.applyWithTrace .mul two
        (rowGet rows ⟨j.val,by rw [hRows]; simp⟩))
    rowIndexWork rows + 2*rowIndexWork lengthEntries ≤ 3*n*(n+1) := by
  dsimp only
  have hOriginal := prepareWithRows_index_work input rows hRows
  have hLengths := rowIndexWork_bound (List.ofFn (fun j : Fin n =>
    BinaryQuadraticLifetime.applyWithTrace .mul two
      (rowGet rows ⟨j.val,by rw [hRows]; simp⟩)))
  simp only [List.length_ofFn] at hLengths
  nlinarith only [hOriginal,hLengths]

theorem prepareWithRows_scalar_exposure {n : ℕ} (input : Input n)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    let lengthEntries := List.ofFn (fun j : Fin n =>
      BinaryQuadraticLifetime.applyWithTrace .mul two
        (rowGet rows ⟨j.val,by rw [hRows]; simp⟩))
    rowScalarWork rows + 2*rowScalarWork lengthEntries ≤
      15*n*(n+1)*binaryWordWidth (n+1) := by
  dsimp only
  have hOriginal := rowScalarWork_bound rows
  have hRowsLength : rows.length = n := by rw [hRows]; simp
  rw [hRowsLength] at hOriginal
  have hLengths := rowScalarWork_bound (List.ofFn (fun j : Fin n =>
    BinaryQuadraticLifetime.applyWithTrace .mul two
      (rowGet rows ⟨j.val,by rw [hRows]; simp⟩)))
  simp only [List.length_ofFn] at hLengths
  nlinarith only [hOriginal,hLengths]

theorem prepareWithTrace_state {n : ℕ} (input : Input n) (hC : input.Canonical) :
    (prepareWithTrace input).1 = prepare input := by
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengths := BinaryLifetimeArray.build n (fun j => BinaryQuadraticLifetime.applyWithTrace .mul two (input.values.read j))
  let poor := BinaryLifetimeArray.build n (fun j => BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 (lengths.1.read j))
  have hR : ratio.1 = (prepare input).ratio :=
    BinaryQuadraticLifetime.applyWithTrace_state .div input.b input.a hC.2.1.1 hC.1.1
  have hL : lengths.1 = (prepare input).lengths := by
    apply BinaryOverlapInputPreparation.table_ext
    intro j
    simp only [lengths,BinaryLifetimeArray.build_erases,prepare,FixedArrayTable.read_ofFn]
    exact BinaryQuadraticLifetime.applyWithTrace_state .mul two (input.values.read j) two_canonical.1 (hC.2.2 j).1
  have hRC : Valid ratio.1 := by rw [hR]; exact (ratio_canonical input hC).1
  have hLC : ∀ j,Valid (lengths.1.read j) := by rw [hL]; exact fun j => (lengths_canonical input hC j).1
  have hP : poor.1 = FixedArrayTable.ofFn (fun j => apply .mul ratio.1 (lengths.1.read j)) := by
    apply BinaryOverlapInputPreparation.table_ext
    intro j
    simp only [poor,BinaryLifetimeArray.build_erases,FixedArrayTable.read_ofFn]
    exact BinaryQuadraticLifetime.applyWithTrace_state .mul ratio.1 (lengths.1.read j) hRC (hLC j)
  change (⟨input,ratio.1,lengths.1,poor.1⟩ : Prepared n) = prepare input
  rw [hP,hR,hL]
  rfl

theorem prepareWithRows_state {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (prepareWithRows input rows hRows).1 = prepare input := by
  rw [prepareWithRows_eq]
  exact prepareWithTrace_state input hC

def envelope (n S : ℕ) : ℕ :=
  let W := 3*S+1
  (2*n+1)*BinaryQuadraticLifetime.opcodeBound W+3*BinaryQuadraticLifetime.opcodeFrames W+
    4*(n+1)^2+9*n+130+flattenListReserve n S+flattenArrayReserve n S

theorem envelope_mono {n m S T : ℕ} (hn : n ≤ m) (hS : S ≤ T) :
    envelope n S ≤ envelope m T := by
  unfold envelope
  dsimp only
  gcongr
  · unfold BinaryQuadraticLifetime.opcodeBound
    gcongr
  · unfold BinaryQuadraticLifetime.opcodeFrames
    gcongr
  · exact flattenListReserve_mono hn hS
  · exact flattenArrayReserve_mono hn hS

theorem prepareWithTrace_usage {n : ℕ} (input : Input n) (hC : input.Canonical) :
    usage (prepareWithTrace input).2 ≤ envelope n (BinaryPRGPreparationWork.storedInputWidth input) := by
  let W := 3*BinaryPRGPreparationWork.storedInputWidth input+1
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengths := BinaryLifetimeArray.build n (fun j => BinaryQuadraticLifetime.applyWithTrace .mul two (input.values.read j))
  let poor := BinaryLifetimeArray.build n (fun j => BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 (lengths.1.read j))
  have hw := BinaryPRGPreparationWork.original_widths input
  have ha : width input.a ≤ W := hw.1.trans (by dsimp [W]; omega)
  have hb : width input.b ≤ W := hw.2.1.trans (by dsimp [W]; omega)
  have hTwo : width two ≤ W := by change 2 ≤ W; dsimp [W]; omega
  have hv : ∀ j,width (input.values.read j) ≤ W := fun j => (hw.2.2.1 j).trans (by dsimp [W]; omega)
  have hState := prepareWithTrace_state input hC
  have hRData : ratio.1 = (prepare input).ratio := congrArg Prepared.ratio hState
  have hLData : lengths.1 = (prepare input).lengths := congrArg Prepared.lengths hState
  have hRW : width ratio.1 ≤ W := by rw [hRData]; exact BinaryPRGPreparationWork.ratio_width input
  have hLW : ∀ j,width (lengths.1.read j) ≤ W := by rw [hLData]; exact BinaryPRGPreparationWork.lengths_width input
  have hRatio := opcode_usage .div input.b input.a W hb ha
  have hLengths := array_usage n (fun j => BinaryQuadraticLifetime.applyWithTrace .mul two (input.values.read j))
    (BinaryQuadraticLifetime.opcodeBound W) (BinaryQuadraticLifetime.opcodeFrames W)
    (fun j => (BinaryQuadraticLifetime.applyWithTrace_bounds .mul two (input.values.read j) W hTwo (hv j)).1)
    (fun j => (BinaryQuadraticLifetime.applyWithTrace_bounds .mul two (input.values.read j) W hTwo (hv j)).2)
  have hPoor := array_usage n (fun j => BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 (lengths.1.read j))
    (BinaryQuadraticLifetime.opcodeBound W) (BinaryQuadraticLifetime.opcodeFrames W)
    (fun j => (BinaryQuadraticLifetime.applyWithTrace_bounds .mul ratio.1 (lengths.1.read j) W hRW (hLW j)).1)
    (fun j => (BinaryQuadraticLifetime.applyWithTrace_bounds .mul ratio.1 (lengths.1.read j) W hRW (hLW j)).2)
  have hWrap := wrapList_usage
    (6*n+flattenListReserve n (BinaryPRGPreparationWork.storedInputWidth input))
    (64+flattenArrayReserve n (BinaryPRGPreparationWork.storedInputWidth input))
    (n+4) [ratio.2,lengths.2,poor.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  change usage ratio.2 ≤ opcodeEnvelope W at hRatio
  change usage lengths.2 ≤ _ at hLengths
  change usage poor.2 ≤ _ at hPoor
  change usage (prepareWithTrace input).2 ≤ _ at hWrap
  unfold envelope
  change _ ≤ (2*n+1)*BinaryQuadraticLifetime.opcodeBound W+
    3*BinaryQuadraticLifetime.opcodeFrames W+4*(n+1)^2+9*n+130+
    flattenListReserve n (BinaryPRGPreparationWork.storedInputWidth input)+
    flattenArrayReserve n (BinaryPRGPreparationWork.storedInputWidth input)
  unfold opcodeEnvelope at hRatio
  nlinarith only [hWrap,hRatio,hLengths,hPoor]

theorem prepareWithRows_usage {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    usage (prepareWithRows input rows hRows).2 ≤
      envelope n (BinaryPRGPreparationWork.storedInputWidth input) := by
  rw [prepareWithRows_eq]
  exact prepareWithTrace_usage input hC

theorem all_prefix {n : ℕ} (input : Input n) (hC : input.Canonical) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareWithTrace input).2 steps ≤ borrowed+envelope n (BinaryPRGPreparationWork.storedInputWidth input) ∧
    framePeak ((prepareWithTrace input).2.take steps) ≤ envelope n (BinaryPRGPreparationWork.storedInputWidth input) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepareWithTrace_usage input hC) borrowed steps

end Blotto.BinaryPRGNumericalPreparationLifetime
