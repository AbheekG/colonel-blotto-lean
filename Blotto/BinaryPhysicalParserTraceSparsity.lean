import Blotto.BinaryInputParserTraceSparsity
import Blotto.BinaryPhysicalOutputTraceSparsity
import Blotto.BinaryPRGPhysicalRawRequestMeasured
import Blotto.BinaryTerminalPhysicalRawPolynomial

/-! The complete physical parser's actual returned trace has an unconditional
structural event envelope, including rejected canonical games and accuracies. -/
namespace Blotto.BinaryPhysicalParserTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization BinaryRationalEncoding
open BinaryMeasuredTraceSparsity BinaryInputParserTraceSparsity
open BinaryPRGHeapPrimitiveLifetime (cells)
open BinaryResourceTraceLength (under_length)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem legacy_comparison_bound (first second : SignedWord) :
    Bounded (BinaryQuadraticExpressionLifetime.compareWithTrace first second).2 := by
  have h := BinaryArithmeticTraceSparsity.comparison_bound first second
  rw [BinaryQuadraticExpressionMeasured.compare_erases] at h
  exact h

theorem and_then_bound (first : Bool × Trace) (later : Unit → Bool × Trace)
    (hFirst : Bounded first.2) (hLater : ∀ u,Bounded (later u).2) :
    Bounded (BinaryPRGPromiseControlLifetime.andThenWithTrace first later).2 := by
  unfold BinaryPRGPromiseControlLifetime.andThenWithTrace
  split
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨hFirst,hLater ()⟩
  · apply wrap_bound 8 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using hFirst

theorem positive_bound (word : SignedWord) : Bounded (BinaryPRGPromiseControlLifetime.positiveWithTrace word).2 := by
  apply wrap_bound 8 1 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using legacy_comparison_bound _ _

theorem equal_bound (first second : SignedWord) : Bounded (BinaryPRGPromiseControlLifetime.equalWithTrace first second).2 :=
  and_then_bound _ _ (legacy_comparison_bound _ _) (fun _ => legacy_comparison_bound _ _)

theorem all_bound (f : SignedWord → Bool × Trace) (words : List SignedWord) (h : ∀ word,Bounded (f word).2) :
    Bounded (BinaryPRGPromiseControlLifetime.allWithTrace f words).2 := by
  induction words with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons word rest ih => exact and_then_bound _ _ (h word) (fun _ => ih)

theorem scaled_bound (twice b word : SignedWord) : Bounded (BinaryPRGPromiseControlLifetime.scaledWithTrace twice b word).2 := by
  apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryArithmeticTraceSparsity.opcode_bound _ _ _,legacy_comparison_bound _ _⟩

theorem sum_bound (words : List SignedWord) : Bounded (BinaryStoredWordSumLifetime.sumWithTrace words).2 := by
  induction words with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons word rest ih =>
      apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨ih,BinaryArithmeticTraceSparsity.opcode_bound _ _ _⟩

theorem fields_bound {n : ℕ} (input : BinaryPRGRecognition.Input n) (rows : List SignedWord) :
    Bounded (BinaryPRGPromiseLifetime.fieldsWithTrace input rows).2 := by
  apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryArithmeticTraceSparsity.opcode_bound _ _ _,all_bound _ _ (fun _ => scaled_bound _ _ _)⟩

theorem remaining_bound {n : ℕ} (input : BinaryPRGRecognition.Input n) (rows : List SignedWord) :
    Bounded (BinaryPRGPromiseLifetime.remainingWithTrace input rows).2 := by
  apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  refine ⟨sum_bound _,?_⟩
  apply and_then_bound
  · exact equal_bound _ _
  · intro u
    apply and_then_bound
    · exact positive_bound _
    · intro u
      apply and_then_bound
      · exact positive_bound _
      · intro u
        exact and_then_bound _ _ (legacy_comparison_bound _ _) (fun _ => fields_bound _ _)

theorem promise_bound {n : ℕ} (input : BinaryPRGRecognition.Input n) (rows : List SignedWord) :
    Bounded (BinaryPRGPromiseLifetime.checkRowsWithTrace input rows).2 := by
  apply wrapList_bound n 32 (n+4) _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact and_then_bound _ _ (all_bound _ _ positive_bound) (fun _ => remaining_bound _ _)

theorem map_trace_bound {α β : Type*} (f : α → β) (items : List α) :
    Bounded (BinaryLifetimeArray.mapDirectWithTrace f items).2 := by
  induction items with
  | nil => simp [BinaryLifetimeArray.mapDirectWithTrace,Bounded,cells,listCells,arraySlots]
  | cons item rest ih => exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) ih

theorem from_entries_bound {α : Type*} (n : ℕ) (entries : List (α × Trace)) (hLength : entries.length = n)
    (h : ∀ entry ∈ entries,Bounded entry.2) : Bounded (BinaryLifetimeArray.fromEntries n entries hLength).2 := by
  have hc := flatten_bound (BinaryLifetimeArray.mapDirect Prod.snd entries) (by
    intro trace ht
    rw [BinaryLifetimeArray.mapDirect_eq_map] at ht
    obtain ⟨entry,hEntry,rfl⟩ := List.mem_map.mp ht
    exact h entry hEntry)
  have hl : (BinaryLifetimeArray.mapDirect Prod.snd entries).length = n :=
    (BinaryLifetimeArray.mapDirect_length _ _).trans hLength
  rw [hl] at hc
  unfold Bounded BinaryLifetimeArray.fromEntries
  simp only [BinaryLifetimeFlattenList.flattenDirect_result,List.length_append,under_length,
    cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,List.length_cons,List.length_nil]
  unfold cells at hc
  nlinarith only [hc]

theorem mapped_entries_bound {α : Type*} (produce : α → SignedWord × Trace) (items : List α)
    (h : ∀ item,Bounded (produce item).2) :
    ∀ entry ∈ BinaryLifetimeArray.mapDirect produce items,Bounded entry.2 := by
  intro entry hEntry
  rw [BinaryLifetimeArray.mapDirect_eq_map] at hEntry
  obtain ⟨item,hi,rfl⟩ := List.mem_map.mp hEntry
  exact h item

theorem store_bound (words : List SignedWord) : Bounded (BinaryWordObjectArrayLifetime.prepareWithTrace words).2 := by
  have h := BinaryPhysicalOutputTraceSparsity.prepare_bound words
  rw [BinaryWordObjectArrayMeasured.prepare_erases] at h
  exact h

theorem physical_map_bound (entries : List (SignedWord × Trace)) :
    Bounded (BinaryPRGNumericalPhysicalMapLifetime.prepareWithTrace entries).2 := by
  apply wrapList_bound 1 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨map_trace_bound _ _,store_bound _⟩

theorem numerical_physical_bound {n : ℕ} (input : BinaryPRGRecognition.Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    Bounded (BinaryPRGCheckedPhysicalPreparationLifetime.prepareWithRowsPhysical input rows hRows).2 := by
  apply wrap_bound 128 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  refine ⟨?_,physical_map_bound _,physical_map_bound _⟩
  apply wrapList_bound _ _ (n+4) _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryArithmeticTraceSparsity.opcode_bound _ _ _,
    from_entries_bound n _ _ (mapped_entries_bound _ _ (fun _ => BinaryArithmeticTraceSparsity.opcode_bound _ _ _)),
    from_entries_bound n _ _ (mapped_entries_bound _ _ (fun _ => BinaryArithmeticTraceSparsity.opcode_bound _ _ _))⟩

theorem checked_physical_bound {n : ℕ} (input : BinaryPRGRecognition.Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    Bounded (BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysicalWithRows input hC rows hRows).2 := by
  unfold BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysicalWithRows
  dsimp only
  split
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨promise_bound _ _,numerical_physical_bound _ _ _⟩
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using promise_bound input rows

theorem checked_game_bound (bits : List Bool) : Bounded (BinaryPRGPhysicalCheckedGameLifetime.readWithTrace bits).2 := by
  unfold BinaryPRGPhysicalCheckedGameLifetime.readWithTrace
  dsimp only
  split
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using game_bound bits
  · apply wrap_bound 48 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨game_bound _,checked_physical_bound _ _ _ _⟩

theorem parser_bound (bits : List Bool) : Bounded (BinaryPRGPhysicalRawRequestLifetime.readWithTrace bits).2 := by
  unfold BinaryPRGPhysicalRawRequestLifetime.readWithTrace
  dsimp only
  split
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using checked_game_bound bits
  · split
    · apply wrap_bound 48 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨checked_game_bound _,accuracy_bound _⟩
    · apply wrap_bound 64 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨checked_game_bound _,accuracy_bound _,assemble_bound _ _ _ _ _⟩

theorem measured_parser_bound (bits : List Bool) : Bounded (BinaryPRGPhysicalRawRequestMeasured.read bits).1.2 := by
  rw [BinaryPRGPhysicalRawRequestMeasured.read_erases]
  exact parser_bound bits

theorem parser_length_usage (bits : List Bool) : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace bits).2.length ≤
    3*usage (BinaryPRGPhysicalRawRequestLifetime.readWithTrace bits).2+3 :=
  length_usage _ (parser_bound bits)

theorem uniform_parser_length : ∃ C d : ℕ,∀ bits : List Bool,
    (BinaryPRGPhysicalRawRequestLifetime.readWithTrace bits).2.length ≤ C*(bits.length+1)^d := by
  obtain ⟨C,d,hEnvelope⟩ := BinaryTerminalPhysicalRawPolynomial.uniform_envelope
  refine ⟨3*C+3,d,?_⟩
  intro bits
  have hu := (BinaryPRGPhysicalRawRequestLifetime.readWithTrace_usage bits).trans (hEnvelope bits.length)
  have ht := parser_length_usage bits
  have hOne := Nat.one_le_pow d (bits.length+1) (by omega)
  nlinarith only [hu,ht,hOne]

end Blotto.BinaryPhysicalParserTraceSparsity
