import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryLifetimeArrayMeasured
import Blotto.BinaryQuadraticMeasured
import Blotto.BinaryGroupEmissionLifetimeBound

/-! Actual quadratic route arithmetic feeds one-pass array construction.
Mixed emission extracts the retained group row and implements the final pivot
write by an explicit copy. Arithmetic is priced in Boolean work; array control
and copied reference slots use conservative source reservations. Native bit/
address/ownership/observer/allocator realization remains separate. -/

namespace Blotto.BinaryGroupEmissionMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryRationalExpression
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 3500000

def cellWithExtras {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) : ((SignedWord × Trace) × ℕ) × ℕ :=
  match (routes.read j).1 with
  | none => (((BinaryRationalOpcode.zero,wrap 8 1 []),8),0)
  | some g =>
      let result := BinaryNormalizedCoordinate.opcode .mul (routes.read j).2 (row.read g)
      ((result.1.1,result.1.2+8),result.2)

def cell {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) : (SignedWord × Trace) × ℕ :=
  (cellWithExtras routes row j).1

theorem cellWithExtras_compat {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) :
    (cellWithExtras routes row j).1 = cell routes row j := rfl

theorem cell_record {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) :
    cell routes row j =
  match (routes.read j).1 with
  | none => ((BinaryRationalOpcode.zero,wrap 8 1 []),8)
  | some g =>
      let result := BinaryPlannedQuadratic.apply .mul (routes.read j).2 (row.read g)
      (result.1,result.2+8) := by
  dsimp only [cell,cellWithExtras]
  split <;> simp only [BinaryNormalizedCoordinate.opcode_record]

theorem cell_erases {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) :
    (cell routes row j).1 = BinaryGroupEmissionLifetime.cellWithTrace routes row j := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,cell_record,BinaryGroupEmissionLifetime.cellWithTrace,BinaryQuadraticMeasured.apply_erases]
  split <;> rename_i hRoute <;> simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,hRoute]

theorem cell_work {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) (W : ℕ)
    (hRoutes : ∀ j,width (routes.read j).2 ≤ W) (hRows : ∀ g,width (row.read g) ≤ W) :
    (cell routes row j).2 ≤ 11000*(W+1)^2+8 := by
  simp only [cell_record]
  simp only [BinaryPlannedQuadratic.apply_previous]
  split
  · exact Nat.le_add_left _ _
  · rename_i g hRoute
    have h := BinaryQuadraticMeasured.apply_bound .mul (routes.read j).2 (row.read g)
    have hw : BinaryRationalArithmetic.pairWidth (routes.read j).2 (row.read g) ≤ W := max_le (hRoutes j) (hRows g)
    have hp := Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 2)
    dsimp only
    omega

def emitWithExtras {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) : ((FixedArrayTable n SignedWord × Trace) × ℕ) × ℕ :=
  BinaryLifetimeArrayExtras.build n (cellWithExtras routes row)

def emit {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) : (FixedArrayTable n SignedWord × Trace) × ℕ :=
  (emitWithExtras routes row).1

theorem emitWithExtras_compat {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) :
    (emitWithExtras routes row).1 = emit routes row := rfl

theorem emit_record {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) :
    emit routes row =
  BinaryLifetimeArrayMeasured.build n (cell routes row) := by
  simp only [emit,emitWithExtras,BinaryLifetimeArrayExtras.build_record]
  rfl

theorem emit_data {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) :
    (emit routes row).1.1 = (BinaryGroupEmissionLifetime.emitWithTrace routes row).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,emit_record,BinaryGroupEmissionLifetime.emitWithTrace,BinaryLifetimeArrayMeasured.build_data,cell_erases]

theorem emit_state {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (hRows : ∀ g,CanonicalWord (row.read g)) : (emit routes row).1.1 = BinaryGroupRoutes.emit routes row := by
  rw [emit_data,BinaryGroupEmissionLifetime.emitWithTrace_erasure routes row hRoutes hRows]

def workEnvelope (n W : ℕ) : ℕ := n*(11000*(W+1)^2+8)+64*(n+1)^2

theorem emit_work {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (W : ℕ)
    (hRoutes : ∀ j,width (routes.read j).2 ≤ W) (hRows : ∀ g,width (row.read g) ≤ W) :
    (emit routes row).2 ≤ workEnvelope n W := by
  rw [emit_record]
  exact BinaryLifetimeArrayMeasured.build_work_bound n _ _ (fun j => cell_work routes row j W hRoutes hRows)

def envelope (n W : ℕ) : ℕ := n*(BinaryQuadraticLifetime.opcodeBound W+8)+
  BinaryLifetimeArrayMeasured.storageReserve n+2*n+BinaryQuadraticLifetime.opcodeFrames W+11

theorem emit_usage {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (W : ℕ)
    (hRoutes : ∀ j,width (routes.read j).2 ≤ W) (hRows : ∀ g,width (row.read g) ≤ W) :
    usage (emit routes row).1.2 ≤ envelope n W := by
  rw [emit_record]
  have hCell := fun j => BinaryGroupEmissionLifetimeBound.cell_bounds routes row j W hRoutes hRows
  have h := BinaryLifetimeArrayMeasured.build_bounds n (cell routes row)
    (BinaryQuadraticLifetime.opcodeBound W+8) (BinaryQuadraticLifetime.opcodeFrames W+1)
    (fun j => by rw [cell_erases]; exact (hCell j).1)
    (fun j => by rw [cell_erases]; exact (hCell j).2)
  exact h.trans_eq (by unfold envelope; omega)

def subrow {m : ℕ} (row : FixedArrayTable (m+1) SignedWord) : (FixedArrayTable m SignedWord × Trace) × ℕ :=
  BinaryLifetimeArrayMeasured.build m (fun j => ((row.read j.castSucc,wrap 8 1 []),4))

theorem subrow_data {m : ℕ} (row : FixedArrayTable (m+1) SignedWord) :
    (subrow row).1.1 = FixedArrayTable.ofFn (fun j : Fin m => row.read j.castSucc) := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,subrow,BinaryLifetimeArrayMeasured.build_data,BinaryLifetimeArray.build_erases]

theorem subrow_work {m : ℕ} (row : FixedArrayTable (m+1) SignedWord) :
    (subrow row).2 ≤ m*4+64*(m+1)^2 :=
  BinaryLifetimeArrayMeasured.build_work_bound m _ 4 (fun _ => le_rfl)

def replace {n : ℕ} (table : FixedArrayTable n SignedWord) (pivot : Fin n) (word : SignedWord) :
    (FixedArrayTable n SignedWord × Trace) × ℕ :=
  BinaryLifetimeArrayMeasured.build n (fun j => ((if j = pivot then word else table.read j,wrap 8 1 []),4))

theorem replace_data {n : ℕ} (table : FixedArrayTable n SignedWord) (pivot : Fin n) (word : SignedWord) :
    (replace table pivot word).1.1 = table.write pivot word := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,replace,BinaryLifetimeArrayMeasured.build_data,BinaryLifetimeArray.build_erases,
    FixedArrayTable.read_ofFn,FixedArrayTable.read_write]

theorem replace_work {n : ℕ} (table : FixedArrayTable n SignedWord) (pivot : Fin n) (word : SignedWord) :
    (replace table pivot word).2 ≤ n*4+64*(n+1)^2 :=
  BinaryLifetimeArrayMeasured.build_work_bound n _ 4 (fun _ => le_rfl)

def referenceEnvelope (n : ℕ) : ℕ := n*8+BinaryLifetimeArrayMeasured.storageReserve n+2*n+11

theorem subrow_usage {m : ℕ} (row : FixedArrayTable (m+1) SignedWord) :
    usage (subrow row).1.2 ≤ referenceEnvelope m := by
  exact BinaryLifetimeArrayMeasured.build_bounds m _ 8 1
    (fun _ => by simp [BinaryPRGHeapPrimitiveLifetime.cells,wrap,combine,listCells,arraySlots])
    (fun _ => by simp [wrap,combine,framePeak])

theorem replace_usage {n : ℕ} (table : FixedArrayTable n SignedWord) (pivot : Fin n) (word : SignedWord) :
    usage (replace table pivot word).1.2 ≤ referenceEnvelope n := by
  exact BinaryLifetimeArrayMeasured.build_bounds n _ 8 1
    (fun _ => by simp [BinaryPRGHeapPrimitiveLifetime.cells,wrap,combine,listCells,arraySlots])
    (fun _ => by simp [wrap,combine,framePeak])

def emitMixedWithExtras {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) : ((FixedArrayTable n SignedWord × Trace) × ℕ) × ℕ :=
  let uniform := subrow row
  let produced := emitWithExtras routes uniform.1.1
  let emitted := produced.1
  let actual := BinaryNormalizedCoordinate.opcode .add (emitted.1.1.read pivot) (row.read (Fin.last m))
  let extra := actual.1
  let copied := replace emitted.1.1 pivot extra.1.1
  (((copied.1.1,wrap 64 2 [uniform.1.2,emitted.1.2,extra.1.2,copied.1.2]),
    uniform.2+emitted.2+extra.2+copied.2+8),produced.2+actual.2)

def emitMixed {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) : (FixedArrayTable n SignedWord × Trace) × ℕ :=
  (emitMixedWithExtras routes pivot row).1

theorem emitMixedWithExtras_compat {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) :
    (emitMixedWithExtras routes pivot row).1 = emitMixed routes pivot row := rfl

theorem emitMixed_record {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) :
    emitMixed routes pivot row =
  let uniform := subrow row
  let emitted := emit routes uniform.1.1
  let extra := BinaryPlannedQuadratic.apply .add (emitted.1.1.read pivot) (row.read (Fin.last m))
  let copied := replace emitted.1.1 pivot extra.1.1
  ((copied.1.1,wrap 64 2 [uniform.1.2,emitted.1.2,extra.1.2,copied.1.2]),
    uniform.2+emitted.2+extra.2+copied.2+8) := by
  simp only [emitMixed,emitMixedWithExtras,emitWithExtras_compat,BinaryNormalizedCoordinate.opcode_record]

theorem emitMixed_data {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) :
    (emitMixed routes pivot row).1.1 = (BinaryGroupEmissionLifetime.emitMixedWithTrace routes pivot row).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,emitMixed_record,BinaryGroupEmissionLifetime.emitMixedWithTrace,replace_data,subrow_data,emit_data,
    BinaryQuadraticMeasured.apply_erases]

theorem emitMixed_state {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (hRows : ∀ g,CanonicalWord (row.read g)) :
    (emitMixed routes pivot row).1.1 = BinaryGroupRoutes.emitMixed routes pivot row := by
  rw [emitMixed_data,BinaryGroupEmissionLifetime.emitMixedWithTrace_erasure routes pivot row hRoutes hRows]

def mixedWorkEnvelope (n m s : ℕ) : ℕ := m*4+64*(m+1)^2+workEnvelope n (2*s+1)+
  11000*(2*expressionHeightBudget s 1+2)^2+n*4+64*(n+1)^2+8

theorem mixed_widths {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (hRows : ∀ g,CanonicalWord (row.read g)) (s : ℕ) (hs : 3 ≤ s)
    (hR : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hH : ∀ g,RationalHeight (value (row.read g)) s) :
    (∀ j,width (routes.read j).2 ≤ 2*s+1) ∧
      (∀ g,width ((subrow row).1.1.read g) ≤ 2*s+1) ∧
      width ((emit routes (subrow row).1.1).1.1.read pivot) ≤ 2*expressionHeightBudget s 1+1 ∧
      width (row.read (Fin.last m)) ≤ 2*expressionHeightBudget s 1+1 := by
  let uniform := subrow row
  have hUniform : ∀ g,CanonicalWord (uniform.1.1.read g) := by
    intro g; rw [subrow_data,FixedArrayTable.read_ofFn]; exact hRows _
  have hUH : ∀ g,RationalHeight (value (uniform.1.1.read g)) s := by
    intro g; rw [subrow_data,FixedArrayTable.read_ofFn]; exact hH _
  have hRW : ∀ j,width (routes.read j).2 ≤ 2*s+1 := by
    intro j
    have h := (hRoutes j).2.trans (rationalWordWidth_of_height (hR j))
    omega
  have hUW : ∀ g,width (uniform.1.1.read g) ≤ 2*s+1 := by
    intro g
    have h := (hUniform g).2.trans (rationalWordWidth_of_height (hUH g))
    omega
  have hEmitState := emit_state routes uniform.1.1 hRoutes hUniform
  have hCan := BinaryGroupRoutes.emit_canonical routes uniform.1.1 hRoutes hUniform pivot
  have hHeight := BinaryGroupRouteEmissionWork.emit_height routes uniform.1.1 hRoutes hUniform s hs hR hUH pivot
  have hFirst : width ((emit routes uniform.1.1).1.1.read pivot) ≤ 2*expressionHeightBudget s 1+1 := by
    rw [hEmitState]
    have h := hCan.2.trans (rationalWordWidth_of_height hHeight)
    omega
  have hLast : width (row.read (Fin.last m)) ≤ 2*expressionHeightBudget s 1+1 := by
    have h := (hRows (Fin.last m)).2.trans
      (rationalWordWidth_of_height ((hH (Fin.last m)).mono (expressionHeightBudget_ge_input s 1)))
    omega
  exact ⟨hRW,hUW,hFirst,hLast⟩

theorem emitMixed_work {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (hRows : ∀ g,CanonicalWord (row.read g)) (s : ℕ) (hs : 3 ≤ s)
    (hR : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hH : ∀ g,RationalHeight (value (row.read g)) s) :
    (emitMixed routes pivot row).2 ≤ mixedWorkEnvelope n m s := by
  simp only [emitMixed_record]
  simp only [BinaryPlannedQuadratic.apply_previous]
  let uniform := subrow row
  obtain ⟨hRW,hUW,hFirst,hLast⟩ := mixed_widths routes pivot row hRoutes hRows s hs hR hH
  have hEmit := emit_work routes uniform.1.1 (2*s+1) hRW hUW
  have hExtra := BinaryQuadraticMeasured.apply_bound .add ((emit routes uniform.1.1).1.1.read pivot) (row.read (Fin.last m))
  have hPair : BinaryRationalArithmetic.pairWidth ((emit routes uniform.1.1).1.1.read pivot) (row.read (Fin.last m)) ≤
      2*expressionHeightBudget s 1+1 := max_le hFirst hLast
  have hp : (BinaryQuadraticMeasured.apply .add ((emit routes uniform.1.1).1.1.read pivot)
      (row.read (Fin.last m))).2 ≤ 11000*(2*expressionHeightBudget s 1+2)^2 :=
    hExtra.trans (Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left (by omega) 2))
  have hSub := subrow_work row
  have hCopy := replace_work (emit routes uniform.1.1).1.1 pivot
    (BinaryQuadraticMeasured.apply .add ((emit routes uniform.1.1).1.1.read pivot) (row.read (Fin.last m))).1.1
  change uniform.2+_+_+_+8 ≤ _
  unfold mixedWorkEnvelope
  dsimp only [uniform] at *
  omega

def mixedEnvelope (n m s : ℕ) : ℕ := referenceEnvelope m+envelope n (2*s+1)+
  BinaryLifetimeUsage.opcodeEnvelope (2*expressionHeightBudget s 1+1)+referenceEnvelope n+128

theorem emitMixed_usage {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (hRows : ∀ g,CanonicalWord (row.read g)) (s : ℕ) (hs : 3 ≤ s)
    (hR : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hH : ∀ g,RationalHeight (value (row.read g)) s) :
    usage (emitMixed routes pivot row).1.2 ≤ mixedEnvelope n m s := by
  simp only [emitMixed_record]
  simp only [BinaryPlannedQuadratic.apply_previous]
  let uniform := subrow row
  let emitted := emit routes uniform.1.1
  let extra := BinaryQuadraticMeasured.apply .add (emitted.1.1.read pivot) (row.read (Fin.last m))
  let copied := replace emitted.1.1 pivot extra.1.1
  obtain ⟨hRW,hUW,hFirst,hLast⟩ := mixed_widths routes pivot row hRoutes hRows s hs hR hH
  have hSub := subrow_usage row
  have hEmit := emit_usage routes uniform.1.1 (2*s+1) hRW hUW
  have hExtra : usage extra.1.2 ≤ BinaryLifetimeUsage.opcodeEnvelope (2*expressionHeightBudget s 1+1) := by
    rw [BinaryQuadraticMeasured.apply_erases]
    exact BinaryLifetimeUsage.opcode_usage .add (emitted.1.1.read pivot) (row.read (Fin.last m)) _ hFirst hLast
  have hCopy := replace_usage emitted.1.1 pivot extra.1.1
  have hw := wrap_usage 64 2 [uniform.1.2,emitted.1.2,extra.1.2,copied.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 64 2 [uniform.1.2,emitted.1.2,extra.1.2,copied.1.2]) ≤ _
  unfold mixedEnvelope
  change usage uniform.1.2 ≤ _ at hSub
  change usage emitted.1.2 ≤ _ at hEmit
  change usage copied.1.2 ≤ _ at hCopy
  omega

def emitOptionWithExtras {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (rows : Option (FixedArrayTable m SignedWord)) : ((Option (FixedArrayTable n SignedWord) × Trace) × ℕ) × ℕ :=
  match rows with
  | none => (((none,wrap 8 1 []),4),0)
  | some row =>
      let produced := emitWithExtras routes row
      let emitted := produced.1
      (((some emitted.1.1,wrap 16 2 [emitted.1.2]),emitted.2+4),produced.2)

def emitOption {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) :
    Option (FixedArrayTable m SignedWord) → (Option (FixedArrayTable n SignedWord) × Trace) × ℕ :=
  fun rows => (emitOptionWithExtras routes rows).1

theorem emitOptionWithExtras_compat {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (rows : Option (FixedArrayTable m SignedWord)) :
    (emitOptionWithExtras routes rows).1 = emitOption routes rows := rfl

theorem emitOption_record {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (rows : Option (FixedArrayTable m SignedWord)) :
    emitOption routes rows =
  match rows with
  | none => ((none,wrap 8 1 []),4)
  | some row =>
      let emitted := emit routes row
      ((some emitted.1.1,wrap 16 2 [emitted.1.2]),emitted.2+4) := by
  cases rows <;> rfl

theorem emitOption_data {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (rows : Option (FixedArrayTable m SignedWord)) :
    (emitOption routes rows).1.1 = (BinaryGroupEmissionLifetime.emitOptionWithTrace routes rows).1 := by
  cases rows <;> simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,emitOption_record,BinaryGroupEmissionLifetime.emitOptionWithTrace,emit_data]

theorem emitOption_work {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (rows : Option (FixedArrayTable m SignedWord)) (W : ℕ)
    (hR : ∀ j,width (routes.read j).2 ≤ W)
    (hH : ∀ row,rows = some row → ∀ g,width (row.read g) ≤ W) :
    (emitOption routes rows).2 ≤ workEnvelope n W+4 := by
  cases rows with
  | none => exact Nat.le_add_left _ _
  | some row => exact Nat.add_le_add_right (emit_work routes row W hR (hH row rfl)) 4

theorem emitOption_usage {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (rows : Option (FixedArrayTable m SignedWord)) (W : ℕ)
    (hR : ∀ j,width (routes.read j).2 ≤ W)
    (hH : ∀ row,rows = some row → ∀ g,width (row.read g) ≤ W) :
    usage (emitOption routes rows).1.2 ≤ envelope n W+32 := by
  cases rows with
  | none => exact (wrap_usage 8 1 []).trans (by simp)
  | some row =>
      have h := emit_usage routes row W hR (hH row rfl)
      have hw := wrap_usage 16 2 [(emit routes row).1.2]
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      exact hw.trans (by omega)

def emitMixedOptionWithExtras {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (rows : Option (FixedArrayTable (m+1) SignedWord)) : ((Option (FixedArrayTable n SignedWord) × Trace) × ℕ) × ℕ :=
  match rows with
  | none => (((none,wrap 8 1 []),4),0)
  | some row =>
      let produced := emitMixedWithExtras routes pivot row
      let emitted := produced.1
      (((some emitted.1.1,wrap 16 2 [emitted.1.2]),emitted.2+4),produced.2)

def emitMixedOption {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) :
    Option (FixedArrayTable (m+1) SignedWord) → (Option (FixedArrayTable n SignedWord) × Trace) × ℕ :=
  fun rows => (emitMixedOptionWithExtras routes pivot rows).1

theorem emitMixedOptionWithExtras_compat {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (rows : Option (FixedArrayTable (m+1) SignedWord)) :
    (emitMixedOptionWithExtras routes pivot rows).1 = emitMixedOption routes pivot rows := rfl

theorem emitMixedOption_record {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (rows : Option (FixedArrayTable (m+1) SignedWord)) :
    emitMixedOption routes pivot rows =
  match rows with
  | none => ((none,wrap 8 1 []),4)
  | some row =>
      let emitted := emitMixed routes pivot row
      ((some emitted.1.1,wrap 16 2 [emitted.1.2]),emitted.2+4) := by
  cases rows <;> rfl

theorem emitMixedOption_data {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (rows : Option (FixedArrayTable (m+1) SignedWord)) :
    (emitMixedOption routes pivot rows).1.1 = (BinaryGroupEmissionLifetime.emitMixedOptionWithTrace routes pivot rows).1 := by
  cases rows <;> simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,emitMixedOption_record,BinaryGroupEmissionLifetime.emitMixedOptionWithTrace,emitMixed_data]

theorem emitMixedOption_work {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (rows : Option (FixedArrayTable (m+1) SignedWord)) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (hRows : ∀ row,rows = some row → ∀ g,CanonicalWord (row.read g)) (s : ℕ) (hs : 3 ≤ s)
    (hR : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hH : ∀ row,rows = some row → ∀ g,RationalHeight (value (row.read g)) s) :
    (emitMixedOption routes pivot rows).2 ≤ mixedWorkEnvelope n m s+4 := by
  cases rows with
  | none => exact Nat.le_add_left _ _
  | some row =>
      exact Nat.add_le_add_right (emitMixed_work routes pivot row hRoutes (hRows row rfl) s hs hR (hH row rfl)) 4

theorem emitMixedOption_usage {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (rows : Option (FixedArrayTable (m+1) SignedWord)) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (hRows : ∀ row,rows = some row → ∀ g,CanonicalWord (row.read g)) (s : ℕ) (hs : 3 ≤ s)
    (hR : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hH : ∀ row,rows = some row → ∀ g,RationalHeight (value (row.read g)) s) :
    usage (emitMixedOption routes pivot rows).1.2 ≤ mixedEnvelope n m s+32 := by
  cases rows with
  | none => exact (wrap_usage 8 1 []).trans (by simp)
  | some row =>
      have h := emitMixed_usage routes pivot row hRoutes (hRows row rfl) s hs hR (hH row rfl)
      have hw := wrap_usage 16 2 [(emitMixed routes pivot row).1.2]
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      exact hw.trans (by omega)

theorem option_all_prefix {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (rows : Option (FixedArrayTable m SignedWord)) (W : ℕ)
    (hR : ∀ j,width (routes.read j).2 ≤ W)
    (hH : ∀ row,rows = some row → ∀ g,width (row.read g) ≤ W) (borrowed steps : ℕ) :
    retainedHeap borrowed (emitOption routes rows).1.2 steps ≤ borrowed+(envelope n W+32) ∧
      framePeak ((emitOption routes rows).1.2.take steps) ≤ envelope n W+32 :=
  all_prefix _ _ (emitOption_usage routes rows W hR hH) borrowed steps

theorem mixed_option_all_prefix {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (rows : Option (FixedArrayTable (m+1) SignedWord)) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (hRows : ∀ row,rows = some row → ∀ g,CanonicalWord (row.read g)) (s : ℕ) (hs : 3 ≤ s)
    (hR : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hH : ∀ row,rows = some row → ∀ g,RationalHeight (value (row.read g)) s) (borrowed steps : ℕ) :
    retainedHeap borrowed (emitMixedOption routes pivot rows).1.2 steps ≤ borrowed+(mixedEnvelope n m s+32) ∧
      framePeak ((emitMixedOption routes pivot rows).1.2.take steps) ≤ mixedEnvelope n m s+32 :=
  all_prefix _ _ (emitMixedOption_usage routes pivot rows hRoutes hRows s hs hR hH) borrowed steps

theorem workEnvelope_polynomial (n W : ℕ) : workEnvelope n W ≤ 20000*(n+W+1)^3 := by
  let X := n+W+1
  have hX : 0 < X := by dsimp only [X]; omega
  have hN : n ≤ X := by dsimp only [X]; omega
  have hN1 : n+1 ≤ X := by dsimp only [X]; omega
  have hW : W+1 ≤ X := by dsimp only [X]; omega
  have hProduct : n*(W+1)^2 ≤ X^3 :=
    (Nat.mul_le_mul hN (Nat.pow_le_pow_left hW 2)).trans_eq (by ring)
  have hSquare : (n+1)^2 ≤ X^3 := (Nat.pow_le_pow_left hN1 2).trans (Nat.pow_le_pow_right hX (by decide))
  have hLinear : n ≤ X^3 := hN.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hX (by decide : 1 ≤ 3))
  unfold workEnvelope
  change _ ≤ 20000*X^3
  nlinarith only [hProduct,hSquare,hLinear]

theorem envelope_polynomial (n W : ℕ) : envelope n W ≤ 1000000*(n+W+2)^4 := by
  let X := n+W+2
  have hX : 0 < X := by dsimp only [X]; omega
  have hN : n ≤ X := by dsimp only [X]; omega
  have hN1 : n+1 ≤ X := by dsimp only [X]; omega
  have hW : W+2 ≤ X := by dsimp only [X]; omega
  have hProduct : n*(W+2)^3 ≤ X^4 :=
    (Nat.mul_le_mul hN (Nat.pow_le_pow_left hW 3)).trans_eq (by ring)
  have hN2 : (n+1)^2 ≤ X^4 := (Nat.pow_le_pow_left hN1 2).trans (Nat.pow_le_pow_right hX (by decide))
  have hW2 : (W+2)^2 ≤ X^4 := (Nat.pow_le_pow_left hW 2).trans (Nat.pow_le_pow_right hX (by decide))
  have hN4 : n ≤ X^4 := hN.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hX (by decide : 1 ≤ 4))
  have hOne := Nat.one_le_pow 4 X (by omega)
  unfold envelope BinaryLifetimeArrayMeasured.storageReserve BinaryQuadraticLifetime.opcodeBound
    BinaryQuadraticLifetime.opcodeFrames
  change _ ≤ 1000000*X^4
  nlinarith only [hProduct,hN2,hW2,hN4,hOne]

end Blotto.BinaryGroupEmissionMeasured
