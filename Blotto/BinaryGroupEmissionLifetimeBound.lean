import Blotto.BinaryGroupEmissionLifetime

/-! Cached coefficients and actual row widths/heights derive all emission
reservations, including absent routes, mixed pivot addition and none outputs. -/
namespace Blotto.BinaryGroupEmissionLifetimeBound
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage BinaryGroupEmissionLifetime
set_option maxHeartbeats 2000000

theorem cell_bounds {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) (W : ℕ)
    (hRoutes : ∀ j,width (routes.read j).2 ≤ W) (hRows : ∀ g,width (row.read g) ≤ W) :
    listCells (cellWithTrace routes row j).2 + arraySlots (cellWithTrace routes row j).2 ≤ BinaryQuadraticLifetime.opcodeBound W + 8 ∧
      framePeak (cellWithTrace routes row j).2 ≤ BinaryQuadraticLifetime.opcodeFrames W + 1 := by
  unfold cellWithTrace
  split
  · simp [wrap,combine,listCells,arraySlots,framePeak]
  · rename_i g hg
    have h := BinaryQuadraticLifetime.applyWithTrace_bounds .mul (routes.read j).2 (row.read g) W (hRoutes j) (hRows g)
    exact ⟨h.1.trans (by omega),h.2.trans (by omega)⟩

def envelope (n W : ℕ) : ℕ :=
  n * (BinaryQuadraticLifetime.opcodeBound W + 8) + BinaryQuadraticLifetime.opcodeFrames W + 1 + 2 * (n + 1)^2 + n + 14

theorem emitWithTrace_usage {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (W : ℕ)
    (hRoutes : ∀ j,width (routes.read j).2 ≤ W) (hRows : ∀ g,width (row.read g) ≤ W) :
    usage (emitWithTrace routes row).2 ≤ envelope n W := by
  have h := array_usage n (cellWithTrace routes row) (BinaryQuadraticLifetime.opcodeBound W + 8) (BinaryQuadraticLifetime.opcodeFrames W + 1)
    (fun j => (cell_bounds routes row j W hRoutes hRows).1) (fun j => (cell_bounds routes row j W hRoutes hRows).2)
  change usage (BinaryLifetimeArray.build n (cellWithTrace routes row)).2 ≤ _
  unfold envelope
  omega

def mixedEnvelope (n m s : ℕ) : ℕ :=
  envelope n (2 * s + 1) + opcodeEnvelope (2 * expressionHeightBudget s 1 + 1) +
    2 * (m + 1)^2 + 4 * (n + 1)^2 + n + m + 128

theorem emitMixedWithTrace_usage {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m + 1) SignedWord) (hC : ∀ j,CanonicalWord (routes.read j).2)
    (hRow : ∀ g,CanonicalWord (row.read g)) (s : ℕ) (hs : 3 ≤ s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) s) (hRows : ∀ g,RationalHeight (value (row.read g)) s) :
    usage (emitMixedWithTrace routes pivot row).2 ≤ mixedEnvelope n m s := by
  let uniform := FixedArrayTable.ofFn (fun g : Fin m => row.read g.castSucc)
  have hUniform : ∀ g,CanonicalWord (uniform.read g) := by intro g; rw [FixedArrayTable.read_ofFn]; exact hRow _
  have hUH : ∀ g,RationalHeight (value (uniform.read g)) s := by intro g; rw [FixedArrayTable.read_ofFn]; exact hRows _
  have hRW : ∀ j,width (routes.read j).2 ≤ 2 * s + 1 := by
    intro j
    have h := (hC j).2.trans (rationalWordWidth_of_height (hRoutes j))
    omega
  have hUW : ∀ g,width (uniform.read g) ≤ 2 * s + 1 := by
    intro g
    have h := (hUniform g).2.trans (rationalWordWidth_of_height (hUH g))
    omega
  let emitted := emitWithTrace routes uniform
  have hE : emitted.1 = BinaryGroupRoutes.emit routes uniform := emitWithTrace_erasure routes uniform hC hUniform
  have hBaseC := BinaryGroupRoutes.emit_canonical routes uniform hC hUniform pivot
  have hBaseH := BinaryGroupRouteEmissionWork.emit_height routes uniform hC hUniform s hs hRoutes hUH pivot
  have hBaseW : width (emitted.1.read pivot) ≤ 2 * expressionHeightBudget s 1 + 1 := by
    rw [hE]
    have h := hBaseC.2.trans (rationalWordWidth_of_height hBaseH)
    omega
  have hLastW : width (row.read (Fin.last m)) ≤ 2 * expressionHeightBudget s 1 + 1 := by
    have h := (hRow (Fin.last m)).2.trans (rationalWordWidth_of_height (hRows _))
    have hLevel := expressionHeightBudget_ge_input s 1
    omega
  let extra := BinaryQuadraticLifetime.applyWithTrace .add (emitted.1.read pivot) (row.read (Fin.last m))
  have hExtra := opcode_usage .add (emitted.1.read pivot) (row.read (Fin.last m)) _ hBaseW hLastW
  have hEmit := emitWithTrace_usage routes uniform (2 * s + 1) hRW hUW
  have hw := wrap_usage (2 * (m + 1)^2 + 4 * (n + 1)^2 + 64) (n + m + 8) [emitted.2,extra.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap (2 * (m + 1)^2 + 4 * (n + 1)^2 + 64) (n + m + 8) [emitted.2,extra.2]) ≤ _
  change usage emitted.2 ≤ _ at hEmit
  change usage extra.2 ≤ _ at hExtra
  unfold mixedEnvelope
  omega

theorem emitOptionWithTrace_usage {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (rows : Option (FixedArrayTable m SignedWord)) (W : ℕ) (hRoutes : ∀ j,width (routes.read j).2 ≤ W)
    (hRows : ∀ row,rows = some row → ∀ g,width (row.read g) ≤ W) :
    usage (emitOptionWithTrace routes rows).2 ≤ envelope n W + 20 := by
  cases rows with
  | none =>
      have h := wrap_usage 8 1 []
      simp only [List.map_nil,List.sum_nil,Nat.add_zero] at h
      exact h.trans (by omega)
  | some row =>
      have h := emitWithTrace_usage routes row W hRoutes (hRows row rfl)
      have hw := wrap_usage 16 2 [(emitWithTrace routes row).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      exact hw.trans (by omega)

theorem emitMixedOptionWithTrace_usage {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (rows : Option (FixedArrayTable (m + 1) SignedWord)) (hC : ∀ j,CanonicalWord (routes.read j).2)
    (hRowsC : ∀ row,rows = some row → ∀ g,CanonicalWord (row.read g)) (s : ℕ) (hs : 3 ≤ s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hRows : ∀ row,rows = some row → ∀ g,RationalHeight (value (row.read g)) s) :
    usage (emitMixedOptionWithTrace routes pivot rows).2 ≤ mixedEnvelope n m s + 20 := by
  cases rows with
  | none =>
      have h := wrap_usage 8 1 []
      simp only [List.map_nil,List.sum_nil,Nat.add_zero] at h
      exact h.trans (by omega)
  | some row =>
      have h := emitMixedWithTrace_usage routes pivot row hC (hRowsC row rfl) s hs hRoutes (hRows row rfl)
      have hw := wrap_usage 16 2 [(emitMixedWithTrace routes pivot row).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      exact hw.trans (by omega)

end Blotto.BinaryGroupEmissionLifetimeBound
