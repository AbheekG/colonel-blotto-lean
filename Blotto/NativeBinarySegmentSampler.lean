import Blotto.BinarySegmentSampler

/-! Source-free native segment sampling takes only stored words and erased
canonical/nonnegative-weight proofs. Semantic descriptors occur in correctness
statements, never as data arguments of the executable entry point. -/

namespace Blotto.NativeBinarySegmentSampler
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredOverlapEnvironment
open BinaryCategoricalPreparation

def weights {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hWeights : ∀ slot, 0 ≤ value (table.weight.read slot)) : WeightList (Fin k) where
  items := List.ofFn (fun slot => (slot,table.weight.read slot))
  canonical := by intro item hi; obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp hi; exact hC.1 slot
  nonnegative := by intro item hi; obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp hi; exact hWeights slot

def select {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hWeights : ∀ slot, 0 ≤ value (table.weight.read slot)) (fallback : Fin k) (R : ℕ) (bits : Fin R → Bool) : Option (Fin k) × ℕ :=
  BinaryCategoricalRun.runIndexed fallback R bits (.remaining (weights table hC hWeights)) 0 (Nat.zero_le R)

def output {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hWeights : ∀ slot, 0 ≤ value (table.weight.read slot)) (fallback : Fin k) (R : ℕ) (bits : Fin R → Bool) : Fin k :=
  (select table hC hWeights fallback R bits).1.getD fallback

def sample {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hWeights : ∀ slot, 0 ≤ value (table.weight.read slot)) (fallback : Fin k) (R K : ℕ)
    (choice : Fin R → Bool) (scalar : Fin K → Bool) : FixedArrayTable n SignedWord :=
  BinarySegmentPoint.sample table (output table hC hWeights fallback R choice) K scalar

def flatSample {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hWeights : ∀ slot, 0 ≤ value (table.weight.read slot)) (fallback : Fin k) (R K : ℕ)
    (bits : Fin (R+K) → Bool) : FixedArrayTable n SignedWord :=
  sample table hC hWeights fallback R K (firstBitBlock R K bits) (secondBitBlock R K bits)

theorem sample_eq {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hWeights : ∀ slot, 0 ≤ value (table.weight.read slot)) (source : RationalSegmentLottery n k)
    (hr : table.Refines source) (fallback : Fin k) (R K : ℕ) (choice : Fin R → Bool) (scalar : Fin K → Bool) :
    sample table hC hWeights fallback R K choice scalar = BinarySegmentSampler.sample table source hC hr fallback R K choice scalar := rfl

theorem flatSample_eq {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hWeights : ∀ slot, 0 ≤ value (table.weight.read slot)) (source : RationalSegmentLottery n k)
    (hr : table.Refines source) (fallback : Fin k) (R K : ℕ) (bits : Fin (R+K) → Bool) :
    flatSample table hC hWeights fallback R K bits = BinarySegmentSampler.flatSample table source hC hr fallback R K bits := rfl

theorem flatSample_canonical {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hWeights : ∀ slot, 0 ≤ value (table.weight.read slot)) (fallback : Fin k) (R K : ℕ) (bits : Fin (R+K) → Bool) :
    ∀ j, CanonicalWord ((flatSample table hC hWeights fallback R K bits).read j) :=
  BinarySegmentPoint.sample_canonical table _ K _ hC

end Blotto.NativeBinarySegmentSampler
