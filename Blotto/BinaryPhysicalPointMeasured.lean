import Blotto.BinaryMidpointTapeMeasured
import Blotto.BinaryPhysicalInterpolationMeasured
import Blotto.BinaryLifetimeListArrayMeasured
import Blotto.BinaryTapePointWork

/-! A selected point consumes one measured midpoint, paired physical endpoint
heaps/reads/interpolation and final source array packing. The full preceding
word table/trace is preserved. Endpoint projection reserves source references;
native projection/address/ownership/observer/allocator prices remain separate. -/

namespace Blotto.BinaryPhysicalPointMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryStoredOverlapEnvironment
set_option autoImplicit false
set_option maxHeartbeats 4000000

set_option cleanup.letToHave false in
def stageWithExtras (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length) :
    ((List SignedWord × Trace) × ℕ) × ℕ :=
  let midpoint := BinaryMidpointTapeMeasured.sample seed
  let produced := BinaryPhysicalInterpolationMeasured.runWithExtras midpoint.1.1 p q hLength
  let row := produced.1
  (((row.1.1,wrap 32 2 [midpoint.1.2,row.1.2]),midpoint.2+row.2+8),produced.2)

def stage (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length) : (List SignedWord × Trace) × ℕ :=
  (stageWithExtras p q seed hLength).1

theorem stageWithExtras_compat (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length) :
    (stageWithExtras p q seed hLength).1 = stage p q seed hLength := rfl

set_option cleanup.letToHave false in
theorem stage_record (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length) :
    stage p q seed hLength =
  let midpoint := BinaryMidpointTapeMeasured.sample seed
  let row := BinaryPhysicalInterpolationMeasured.run midpoint.1.1 p q hLength
  ((row.1.1,wrap 32 2 [midpoint.1.2,row.1.2]),midpoint.2+row.2+8) := by rfl

theorem stage_erases (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length) :
    (stage p q seed hLength).1 = BinaryTapePointLifetime.sampleWithTrace p q seed hLength := by
  simp only [stage_record,BinaryTapePointLifetime.sampleWithTrace,BinaryMidpointTapeMeasured.sample_erases,
    BinaryPhysicalInterpolationMeasured.run_erases]

theorem stage_data (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length) :
    (stage p q seed hLength).1.1 = (BinaryTapePointLifetime.sampleWithTrace p q seed hLength).1 :=
  congrArg Prod.fst (stage_erases p q seed hLength)

theorem stage_work (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length) :
    (stage p q seed hLength).2 = (BinaryTapePointWork.sampleWithWork p q seed hLength).2 := by
  simp only [stage_record,BinaryTapePointWork.sampleWithWork,BinaryMidpointTapeMeasured.sample_work,
    BinaryPhysicalInterpolationMeasured.run_work,BinaryMidpointTapeMeasured.sample_erases,
    BinaryMidpointTapeLifetime.sample_work_state]

theorem stage_bound (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length)
    (W : ℕ) (hCap : seed.length+2 ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    (stage p q seed hLength).2 ≤ BinaryTapePointLifetime.bound p.length W seed.length := by
  rw [stage_work]
  exact BinaryTapePointWork.sample_work p q seed hLength W hCap hp hq

set_option cleanup.letToHave false in
def sampleWithExtras {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    ((FixedArrayTable n SignedWord × Trace) × ℕ) × ℕ :=
  let p := table.P.read slot
  let q := table.Q.read slot
  have hLength : p.data.toList.length = q.data.toList.length := by
    rw [Array.length_toList,Array.length_toList,p.size,q.size]
  let produced := stageWithExtras p.data.toList q.data.toList bits.bits hLength
  let row := produced.1
  have hRowLength : row.1.1.length = n := by
    change (stage p.data.toList q.data.toList bits.bits hLength).1.1.length = n
    rw [stage_erases,BinaryTapePointLifetime.sample_length,Array.length_toList,p.size]
  let packed := BinaryLifetimeListArrayMeasured.table row.1.1
  (((⟨packed.1.1.data,packed.1.1.size.trans hRowLength⟩,
    wrapList (2*n+K) 64 (2*n+K+4) [row.1.2,packed.1.2]),row.2+packed.2+4*n+16),produced.2)

def sample {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    (FixedArrayTable n SignedWord × Trace) × ℕ :=
  (sampleWithExtras table slot K bits).1

theorem sampleWithExtras_compat {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ)
    (bits : BinaryScalarTape K) : (sampleWithExtras table slot K bits).1 = sample table slot K bits := rfl

theorem sample_record {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    sample table slot K bits =
  let p := table.P.read slot
  let q := table.Q.read slot
  let hLength : p.data.toList.length = q.data.toList.length := by rw [Array.length_toList,Array.length_toList,p.size,q.size]
  let row := stage p.data.toList q.data.toList bits.bits hLength
  let hRowLength : row.1.1.length = n := by
    rw [stage_erases,BinaryTapePointLifetime.sample_length,Array.length_toList,p.size]
  let packed := BinaryLifetimeListArrayMeasured.table row.1.1
  ((⟨packed.1.1.data,packed.1.1.size.trans hRowLength⟩,
    wrapList (2*n+K) 64 (2*n+K+4) [row.1.2,packed.1.2]),row.2+packed.2+4*n+16) := by rfl

theorem sample_erases {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    (sample table slot K bits).1 = BinaryPhysicalPointLifetime.sampleWithTrace table slot K bits := by
  have hData : (sample table slot K bits).1.1.data =
      (BinaryPhysicalPointLifetime.sampleWithTrace table slot K bits).1.data := by
    simp only [sample_record,BinaryPhysicalPointLifetime.sampleWithTrace,BinaryLifetimeListArrayMeasured.table_array,
      BinaryLifetimeListArray.tableWithTrace,BinaryLifetimeListArray.toArrayWithTrace_state,stage_data]
  have hExt : ∀ a b : FixedArrayTable n SignedWord,a.data = b.data → a = b := by
    intro a b h
    cases a
    cases b
    cases h
    rfl
  apply Prod.ext (hExt _ _ hData)
  simp only [sample_record,BinaryPhysicalPointLifetime.sampleWithTrace,stage_erases,
    BinaryLifetimeListArrayMeasured.table_erases,BinaryLifetimeListArray.tableWithTrace,stage_data]

def price (n s K : ℕ) : ℕ := BinaryTapePointLifetime.bound n (BinaryPhysicalPointLifetime.wordCap s K) K+
  n*(n+11)+4*n+24

theorem sample_work {n k : ℕ} (table : Segment n k) (hC : table.Canonical) (s : ℕ)
    (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    (sample table slot K bits).2 ≤ price n s K := by
  let p := table.P.read slot
  let q := table.Q.read slot
  have hLength : p.data.toList.length = q.data.toList.length := by rw [Array.length_toList,Array.length_toList,p.size,q.size]
  let row := stage p.data.toList q.data.toList bits.bits hLength
  have hp := BinaryPhysicalPointLifetime.table_words p s (BinaryPhysicalPointLifetime.wordCap s K)
    (hC.2.1 slot) (fun j => (hH slot j).1)
    (by unfold BinaryPhysicalPointLifetime.wordCap; have h := le_max_left s (K+2); omega)
  have hq := BinaryPhysicalPointLifetime.table_words q s (BinaryPhysicalPointLifetime.wordCap s K)
    (hC.2.2 slot) (fun j => (hH slot j).2)
    (by unfold BinaryPhysicalPointLifetime.wordCap; have h := le_max_left s (K+2); omega)
  have hRow := stage_bound p.data.toList q.data.toList bits.bits hLength (BinaryPhysicalPointLifetime.wordCap s K)
    (by simp only [BinaryScalarTape.length]; unfold BinaryPhysicalPointLifetime.wordCap; have h := le_max_right s (K+2); omega) hp hq
  have hRowLength : row.1.1.length = n := by
    rw [stage_erases,BinaryTapePointLifetime.sample_length,Array.length_toList,p.size]
  have hPack := BinaryLifetimeListArrayMeasured.table_bound row.1.1
  have hPack' := hPack.trans_eq (congrArg (fun N => N*(N+11)+8) hRowLength)
  have hPCount : p.data.toList.length = n := by rw [Array.length_toList,p.size]
  rw [hPCount,BinaryScalarTape.length] at hRow
  change row.2 ≤ _ at hRow
  change row.2+(BinaryLifetimeListArrayMeasured.table row.1.1).2+4*n+16 ≤ _
  unfold price
  omega

theorem all_prefix {n k : ℕ} (table : Segment n k) (hC : table.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (sample table slot K bits).1.2 steps ≤ borrowed+BinaryPhysicalPointLifetime.bound n s K ∧
      framePeak ((sample table slot K bits).1.2.take steps) ≤ BinaryPhysicalPointLifetime.bound n s K := by
  rw [sample_erases]
  exact BinaryPhysicalPointLifetime.all_prefix table hC s hs hH slot K bits borrowed steps

end Blotto.BinaryPhysicalPointMeasured
