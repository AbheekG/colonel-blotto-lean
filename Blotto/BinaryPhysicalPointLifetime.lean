import Blotto.BinaryScalarTape
import Blotto.BinaryPhysicalInterpolationRun
import Blotto.BinaryTapePointLifetime
import Blotto.BinarySegmentPointLifetime

/-! A selected segment point projects each endpoint row once, owns two
physical word heaps and a Boolean index stream, and packs its actual returned
coordinate list. Native projection/packing source regions are reserved. Retained
scalar views supply their actual tapes; native reference-bit transport and
legacy reader adapters retain their model scopes. -/
namespace Blotto.BinaryPhysicalPointLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryStoredOverlapEnvironment
set_option maxHeartbeats 4000000

theorem coordinates_table {n : ℕ} (p q : FixedArrayTable n SignedWord) (scalar : SignedWord) :
    BinaryPhysicalInterpolationRun.coordinates scalar p.data.toList q.data.toList =
      List.ofFn (fun j => BinaryQuadraticData.expression
        (BinarySegmentPoint.environment (p.read j) (q.read j) scalar) BinarySegmentPoint.program.compile) := by
  apply List.ext_getElem
  · simp only [BinaryPhysicalInterpolationRun.coordinates,List.length_map,List.length_zip,
      Array.length_toList,p.size,q.size,Nat.min_self,List.length_ofFn]
  · intro i hi hi'
    simp only [BinaryPhysicalInterpolationRun.coordinates,List.getElem_map,List.getElem_zip,
      Array.getElem_toList,List.getElem_ofFn,BinaryPhysicalInterpolationRow.coordinateData,FixedArrayTable.read]

def sampleWithTrace {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    FixedArrayTable n SignedWord × Trace :=
  let p := table.P.read slot
  let q := table.Q.read slot
  have hLength : p.data.toList.length = q.data.toList.length := by rw [Array.length_toList,Array.length_toList,p.size,q.size]
  let row := BinaryTapePointLifetime.sampleWithTrace p.data.toList q.data.toList bits.bits hLength
  have hRowLength : row.1.length = n := by
    rw [BinaryTapePointLifetime.sample_length,
      Array.length_toList,p.size]
  let packed := BinaryLifetimeListArray.tableWithTrace row.1
  (⟨packed.1.data,packed.1.size.trans hRowLength⟩,wrapList (2*n+K) 64 (2*n+K+4) [row.2,packed.2])

theorem sample_state {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    (sampleWithTrace table slot K bits).1 = FixedArrayTable.ofFn (fun j => BinaryQuadraticData.expression
      (BinarySegmentPoint.environment ((table.P.read slot).read j) ((table.Q.read slot).read j)
        (BinaryDirectDyadicMidpoint.sample (List.ofFn bits))) BinarySegmentPoint.program.compile) := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  unfold sampleWithTrace
  dsimp only
  simp only [FixedArrayTable.read,BinaryLifetimeListArray.tableWithTrace,BinaryLifetimeListArray.toArrayWithTrace_state,
    BinaryTapePointLifetime.sample_state,
    coordinates_table,BinaryScalarTape.listOfFn_read,FixedArrayTable.ofFn,Array.getElem_ofFn,List.getElem_toArray,List.getElem_ofFn]

def wordCap (s K : ℕ) : ℕ := 1+2*max s (K+2)
def bound (n s K : ℕ) : ℕ :=
  BinaryPhysicalInterpolationRun.bound n (wordCap s K)+n*(n+1)+16*n+50*K+1024

theorem table_words {n : ℕ} (row : FixedArrayTable n SignedWord) (s W : ℕ)
    (hC : ∀ j,CanonicalWord (row.read j)) (hH : ∀ j,RationalHeight (value (row.read j)) s)
    (hW : 1+2*s ≤ W) :
    ∀ word ∈ row.data.toList,BinaryRationalOpcode.Valid word ∧ width word ≤ W := by
  intro word hm
  obtain ⟨i,hi,hValue⟩ := List.mem_iff_getElem.mp hm
  let j : Fin n := ⟨i,by simpa only [Array.length_toList,row.size] using hi⟩
  have hj : row.read j = word := by simpa only [FixedArrayTable.read,Array.getElem_toList] using hValue
  rw [← hj]
  have h := (hC j).2.trans (rationalWordWidth_of_height (hH j))
  exact ⟨(hC j).1,by omega⟩

theorem sample_usage {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (s : ℕ) (_hs : 3 ≤ s) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    usage (sampleWithTrace table slot K bits).2 ≤ bound n s K := by
  let p := table.P.read slot
  let q := table.Q.read slot
  have hLength : p.data.toList.length = q.data.toList.length := by rw [Array.length_toList,Array.length_toList,p.size,q.size]
  let row := BinaryTapePointLifetime.sampleWithTrace p.data.toList q.data.toList bits.bits hLength
  have hRowLength : row.1.length = n := by
    rw [BinaryTapePointLifetime.sample_length,
      Array.length_toList,p.size]
  have hP := table_words p s (wordCap s K) (hC.2.1 slot) (fun j => (hH slot j).1)
    (by unfold wordCap; have h := le_max_left s (K+2); omega)
  have hQ := table_words q s (wordCap s K) (hC.2.2 slot) (fun j => (hH slot j).2)
    (by unfold wordCap; have h := le_max_left s (K+2); omega)
  have hRun := BinaryTapePointLifetime.sample_usage p.data.toList q.data.toList bits.bits hLength
    (wordCap s K) (by simp only [BinaryScalarTape.length]; unfold wordCap; have h := le_max_right s (K+2); omega) hP hQ
  simp only [BinaryScalarTape.length] at hRun
  have hPCount : p.data.toList.length = n := by rw [Array.length_toList,p.size]
  have hRun' := hRun.trans_eq (congrArg (fun N => BinaryTapePointLifetime.bound N (wordCap s K) K) hPCount)
  have hPack := BinaryLifetimeListArray.tableWithTrace_usage row.1
  have hPack' := hPack.trans_eq (congrArg (fun N => N*(N+1)+N+1) hRowLength)
  have hw := wrapList_usage (2*n+K) 64 (2*n+K+4) [row.2,(BinaryLifetimeListArray.tableWithTrace row.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (sampleWithTrace table slot K bits).2 ≤ _ at hw
  change usage row.2 ≤ _ at hRun'
  unfold bound BinaryTapePointLifetime.bound at *
  omega

theorem all_prefix {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (sampleWithTrace table slot K bits).2 steps ≤ borrowed+bound n s K ∧
      framePeak ((sampleWithTrace table slot K bits).2.take steps) ≤ bound n s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (sample_usage table hC s hs hH slot K bits) borrowed steps

end Blotto.BinaryPhysicalPointLifetime
