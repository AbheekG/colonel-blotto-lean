import Blotto.BinaryLifetimeUsage
import Blotto.BinaryGroupRouteEmissionWork

/-! Actual cached-route emission uses traced quadratic multiplication and
the mixed pivot addition. Row extraction and the final persistent write have
explicit reference reservations, retaining every old/new array region. -/
namespace Blotto.BinaryGroupEmissionLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 1500000

def cellWithTrace {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) : SignedWord × Trace :=
  match (routes.read j).1 with
  | none => (BinaryRationalOpcode.zero,wrap 8 1 [])
  | some g => BinaryQuadraticLifetime.applyWithTrace .mul (routes.read j).2 (row.read g)

def emitWithTrace {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) : FixedArrayTable n SignedWord × Trace :=
  BinaryLifetimeArray.build n (cellWithTrace routes row)

theorem emitWithTrace_erasure {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (hC : ∀ j,CanonicalWord (routes.read j).2)
    (hRow : ∀ g,CanonicalWord (row.read g)) :
    (emitWithTrace routes row).1 = BinaryGroupRoutes.emit routes row := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [emitWithTrace,BinaryLifetimeArray.build_erases,FixedArrayTable.read_ofFn,BinaryGroupRoutes.emit]
  unfold cellWithTrace
  cases hRoute : (routes.read j).1 with
  | none => rfl
  | some g =>
      exact BinaryQuadraticLifetime.applyWithTrace_state .mul _ _ (hC j).1 (hRow g).1

def emitMixedWithTrace {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m + 1) SignedWord) : FixedArrayTable n SignedWord × Trace :=
  let uniform := FixedArrayTable.ofFn (fun g : Fin m => row.read g.castSucc)
  let emitted := emitWithTrace routes uniform
  let extra := BinaryQuadraticLifetime.applyWithTrace .add (emitted.1.read pivot) (row.read (Fin.last m))
  (emitted.1.write pivot extra.1,
    wrap (2 * (m + 1)^2 + 4 * (n + 1)^2 + 64) (n + m + 8) [emitted.2,extra.2])

theorem emitMixedWithTrace_erasure {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m + 1) SignedWord) (hC : ∀ j,CanonicalWord (routes.read j).2)
    (hRow : ∀ g,CanonicalWord (row.read g)) :
    (emitMixedWithTrace routes pivot row).1 = BinaryGroupRoutes.emitMixed routes pivot row := by
  let uniform := FixedArrayTable.ofFn (fun g : Fin m => row.read g.castSucc)
  have hUniform : ∀ g,CanonicalWord (uniform.read g) := by intro g; rw [FixedArrayTable.read_ofFn]; exact hRow _
  have hEmit := emitWithTrace_erasure routes uniform hC hUniform
  have hBase := BinaryGroupRoutes.emit_canonical routes uniform hC hUniform pivot
  unfold emitMixedWithTrace BinaryGroupRoutes.emitMixed
  dsimp only
  change (emitWithTrace routes uniform).1.write pivot
    (BinaryQuadraticLifetime.applyWithTrace .add ((emitWithTrace routes uniform).1.read pivot) (row.read (Fin.last m))).1 = _
  rw [hEmit,BinaryQuadraticLifetime.applyWithTrace_state .add _ _ hBase.1 (hRow _).1]

def emitOptionWithTrace {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) :
    Option (FixedArrayTable m SignedWord) → Option (FixedArrayTable n SignedWord) × Trace
  | none => (none,wrap 8 1 [])
  | some row => let emitted := emitWithTrace routes row; (some emitted.1,wrap 16 2 [emitted.2])

theorem emitOptionWithTrace_erasure {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (rows : Option (FixedArrayTable m SignedWord)) (hC : ∀ j,CanonicalWord (routes.read j).2)
    (hRows : ∀ row,rows = some row → ∀ g,CanonicalWord (row.read g)) :
    (emitOptionWithTrace routes rows).1 = rows.map (BinaryGroupRoutes.emit routes) := by
  cases rows with
  | none => rfl
  | some row => simp only [emitOptionWithTrace,emitWithTrace_erasure routes row hC (hRows row rfl),Option.map_some]

def emitMixedOptionWithTrace {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) :
    Option (FixedArrayTable (m + 1) SignedWord) → Option (FixedArrayTable n SignedWord) × Trace
  | none => (none,wrap 8 1 [])
  | some row => let emitted := emitMixedWithTrace routes pivot row; (some emitted.1,wrap 16 2 [emitted.2])

theorem emitMixedOptionWithTrace_erasure {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (rows : Option (FixedArrayTable (m + 1) SignedWord)) (hC : ∀ j,CanonicalWord (routes.read j).2)
    (hRows : ∀ row,rows = some row → ∀ g,CanonicalWord (row.read g)) :
    (emitMixedOptionWithTrace routes pivot rows).1 = rows.map (BinaryGroupRoutes.emitMixed routes pivot) := by
  cases rows with
  | none => rfl
  | some row => simp only [emitMixedOptionWithTrace,emitMixedWithTrace_erasure routes pivot row hC (hRows row rfl),Option.map_some]

end Blotto.BinaryGroupEmissionLifetime
