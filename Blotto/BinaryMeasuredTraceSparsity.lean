import Blotto.BinaryInitialTraceSparsity
import Blotto.BinaryLifetimeArrayMeasured
import Blotto.BinaryLifetimeListArrayMeasured

/-! A source event certificate with slack three covers allocation-free empty
list-to-array conversion, whose actual trace has three events. Positive local
headers pay for child slack. All certificates are erased proof observers. -/
namespace Blotto.BinaryMeasuredTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapPrimitiveLifetime (cells)
open BinaryResourceTraceLength (under_length)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def Bounded (trace : Trace) : Prop := trace.length ≤ 3*cells trace+3

theorem children_nil : (∀ child ∈ ([] : List Trace),Bounded child) ↔ True := by simp

theorem of_sparse (trace : Trace) (h : BinaryInitialTraceSparsity.Sparse trace) : Bounded trace := by
  unfold Bounded BinaryInitialTraceSparsity.Sparse at *
  omega

theorem under_bound (depth : ℕ) (trace : Trace) (h : Bounded trace) : Bounded (under depth trace) := by
  simpa only [Bounded,under_length,BinaryPRGHeapPrimitiveLifetime.cells_under] using h

theorem flatten_bound (children : List Trace) (h : ∀ child ∈ children,Bounded child) :
    children.flatten.length ≤ 3*cells children.flatten+3*children.length := by
  induction children with
  | nil => simp [cells,listCells,arraySlots]
  | cons child rest ih =>
      have hc := h child (by simp)
      have hr := ih (by intro trace ht; exact h trace (by simp [ht]))
      unfold Bounded at hc
      simp only [List.flatten_cons,List.length_append,BinaryPRGHeapPrimitiveLifetime.cells_append,List.length_cons]
      omega

theorem prefix_bound (header : Trace) (children : List Trace)
    (h : ∀ child ∈ children,Bounded child)
    (hHeader : header.length+3*children.length ≤ 3*cells header+3) :
    Bounded (header++children.flatten) := by
  have hc := flatten_bound children h
  unfold Bounded
  simp only [List.length_append,BinaryPRGHeapPrimitiveLifetime.cells_append]
  omega

theorem combine_bound (children : List Trace) (h : ∀ child ∈ children,Bounded child) :
    (combine children).length ≤ 3*cells (combine children)+3*children.length := by
  induction children with
  | nil => simp [combine,cells,listCells,arraySlots]
  | cons child rest ih =>
      have hc := h child (by simp)
      have hr := ih (by intro trace ht; exact h trace (by simp [ht]))
      unfold Bounded at hc
      simp only [combine,List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
        BinaryPRGHeapPrimitiveLifetime.cells_under,List.length_cons]
      omega

theorem wrap_bound (slots frames : ℕ) (children : List Trace)
    (h : ∀ child ∈ children,Bounded child) (hSlots : 3*children.length ≤ 3*slots+1) :
    Bounded (wrap slots frames children) := by
  have hc := combine_bound children h
  have hCells : cells (wrap slots frames children) = slots+cells (combine children) := by
    rw [wrap,BinaryPRGHeapPrimitiveLifetime.cells_append]
    simp only [cells,listCells,arraySlots]
    omega
  unfold Bounded
  rw [hCells]
  simp only [wrap,List.length_append,List.length_cons,List.length_nil]
  omega

theorem wrapList_bound (allocated slots frames : ℕ) (children : List Trace)
    (h : ∀ child ∈ children,Bounded child) (hSlots : 3*children.length ≤ 3*(allocated+slots)) :
    Bounded (wrapList allocated slots frames children) := by
  have hc := combine_bound children h
  have hCells : cells (wrapList allocated slots frames children) = allocated+slots+cells (combine children) := by
    rw [wrapList,BinaryPRGHeapPrimitiveLifetime.cells_append,wrap,BinaryPRGHeapPrimitiveLifetime.cells_append]
    simp only [cells,listCells,arraySlots]
    omega
  unfold Bounded
  rw [hCells]
  simp only [wrapList,wrap,List.length_append,List.length_cons,List.length_nil]
  omega

theorem children_bound (n : ℕ) (traces : Fin n → Trace) (h : ∀ j,Bounded (traces j)) :
    (BinaryLifetimeArray.children n traces).length ≤ 3*cells (BinaryLifetimeArray.children n traces)+3*n := by
  have hc := flatten_bound (List.ofFn traces) (by
    intro trace ht
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
    exact h j)
  simpa only [BinaryLifetimeArray.children,List.length_ofFn] using hc

theorem measured_build {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ)
    (h : ∀ j,Bounded (produce j).1.2) : Bounded (BinaryLifetimeArrayMeasured.build n produce).1.2 := by
  have hc := children_bound n (fun j => (produce j).1.2) h
  rw [BinaryLifetimeArrayMeasured.build_trace]
  unfold Bounded
  simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
    BinaryPRGHeapPrimitiveLifetime.cells_under,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,List.length_cons,List.length_nil]
  unfold cells at hc
  unfold BinaryLifetimeArrayMeasured.storageReserve
  nlinarith only [hc]

theorem build {α : Type*} (n : ℕ) (produce : Fin n → α × Trace)
    (h : ∀ j,Bounded (produce j).2) : Bounded (BinaryLifetimeArray.build n produce).2 := by
  have hc := children_bound n (fun j => (produce j).2) h
  unfold cells at hc
  rw [BinaryLifetimeArray.build_reference]
  unfold BinaryLifetimeArray.buildReference Bounded
  simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
    BinaryPRGHeapPrimitiveLifetime.cells_under,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,List.length_cons,List.length_nil]
  nlinarith only [hc]

theorem push_length {α : Type*} (capacity : ℕ) (items : List α) (acc : Array α) :
    (BinaryLifetimeListArray.pushWithTrace capacity items acc).2.length = 2*items.length+1 := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih =>
      simp only [BinaryLifetimeListArray.pushWithTrace,List.length_append,under_length,
        List.length_cons,List.length_nil,ih]
      omega

theorem toArray_bound {α : Type*} (items : List α) :
    Bounded (BinaryLifetimeListArray.toArrayWithTrace items).2 := by
  have hc := BinaryLifetimeListArray.pushWithTrace_bounds items.length items (Array.mkEmpty items.length)
  have hl := push_length items.length items (Array.mkEmpty items.length)
  unfold Bounded BinaryLifetimeListArray.toArrayWithTrace
  simp only [List.length_append,cells,listCells_append,arraySlots_append,listCells,arraySlots,
    List.length_cons,List.length_nil]
  omega

theorem table_bound {α : Type*} (items : List α) :
    Bounded (BinaryLifetimeListArrayMeasured.table items).1.2 := by
  rw [BinaryLifetimeListArrayMeasured.table_erases]
  exact toArray_bound items

theorem length_usage (trace : Trace) (h : Bounded trace) : trace.length ≤ 3*usage trace+3 := by
  unfold Bounded usage at *
  omega

theorem prefix_one (header trace : Trace) (depth : ℕ)
    (hHeader : header.length ≤ 3*cells header) (h : Bounded trace) :
    Bounded (header++under depth trace) := by
  unfold Bounded at h ⊢
  simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
    BinaryPRGHeapPrimitiveLifetime.cells_under]
  omega

theorem prefix_two (header first second : Trace) (a b : ℕ)
    (hHeader : header.length+3 ≤ 3*cells header) (hFirst : Bounded first) (hSecond : Bounded second) :
    Bounded (header++under a first++under b second) := by
  unfold Bounded at hFirst hSecond ⊢
  simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
    BinaryPRGHeapPrimitiveLifetime.cells_under]
  omega

theorem prefix_three (header first second third : Trace) (a b c : ℕ)
    (hHeader : header.length+6 ≤ 3*cells header)
    (hFirst : Bounded first) (hSecond : Bounded second) (hThird : Bounded third) :
    Bounded (header++under a first++under b second++under c third) := by
  unfold Bounded at hFirst hSecond hThird ⊢
  simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
    BinaryPRGHeapPrimitiveLifetime.cells_under]
  omega

theorem prefix_four (header first second third fourth : Trace) (a b c d : ℕ)
    (hHeader : header.length+9 ≤ 3*cells header)
    (hFirst : Bounded first) (hSecond : Bounded second) (hThird : Bounded third) (hFourth : Bounded fourth) :
    Bounded (header++under a first++under b second++under c third++under d fourth) := by
  unfold Bounded at hFirst hSecond hThird hFourth ⊢
  simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
    BinaryPRGHeapPrimitiveLifetime.cells_under]
  omega

end Blotto.BinaryMeasuredTraceSparsity
