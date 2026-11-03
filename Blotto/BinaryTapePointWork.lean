import Blotto.BinaryScalarTape
import Blotto.BinaryTapePointLifetime
import Blotto.BinaryPhysicalInterpolationWork

/-! Measured midpoint and paired-row execution join on the actual returned
scalar word. Decoded endpoint/seed tapes are inputs; their native projection/
materialization and final native packing are explicit caller boundaries. -/
namespace Blotto.BinaryTapePointWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryStoredOverlapEnvironment
set_option maxHeartbeats 3000000

def sampleWithWork (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length) : List SignedWord × ℕ :=
  let midpoint := BinaryMidpointTapeLifetime.sampleWithWork seed
  let row := BinaryPhysicalInterpolationWork.runWithWork midpoint.1 p q hLength
  (row.1,midpoint.2+row.2+8)

theorem sample_state (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length) :
    (sampleWithWork p q seed hLength).1 = (BinaryTapePointLifetime.sampleWithTrace p q seed hLength).1 := by
  simp only [sampleWithWork,BinaryTapePointLifetime.sampleWithTrace,BinaryPhysicalInterpolationWork.run_state,
    BinaryMidpointTapeLifetime.sample_work_state]

theorem sample_work (p q : List SignedWord) (seed : List Bool) (hLength : p.length = q.length)
    (W : ℕ) (hCap : seed.length+2 ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    (sampleWithWork p q seed hLength).2 ≤ BinaryTapePointLifetime.bound p.length W seed.length := by
  let midpoint := BinaryMidpointTapeLifetime.sampleWithWork seed
  let row := BinaryPhysicalInterpolationWork.runWithWork midpoint.1 p q hLength
  have hs := BinaryMidpointTapeLifetime.sample_contract seed
  have hValid : BinaryRationalOpcode.Valid midpoint.1 := by
    change BinaryRationalOpcode.Valid (BinaryMidpointTapeLifetime.sampleWithWork seed).1
    rw [BinaryMidpointTapeLifetime.sample_work_state]
    exact hs.1.1
  have hWidth : width midpoint.1 ≤ W := by
    change width (BinaryMidpointTapeLifetime.sampleWithWork seed).1 ≤ W
    rw [BinaryMidpointTapeLifetime.sample_work_state]
    exact hs.2.1.trans hCap
  have hRow := BinaryPhysicalInterpolationWork.run_work midpoint.1 p q hLength hValid W (by omega) hWidth hp hq
  have hMid := BinaryMidpointTapeLifetime.sample_work seed
  change row.2 ≤ _ at hRow
  change midpoint.2 ≤ _ at hMid
  change midpoint.2+row.2+8 ≤ _
  unfold BinaryTapePointLifetime.bound
  omega

theorem selected_stage_work {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (s : ℕ) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    (sampleWithWork (table.P.read slot).data.toList (table.Q.read slot).data.toList (List.ofFn bits) (by
      rw [Array.length_toList,Array.length_toList,(table.P.read slot).size,(table.Q.read slot).size])).2 ≤
        BinaryTapePointLifetime.bound n (BinaryPhysicalPointLifetime.wordCap s K) K := by
  have hp := BinaryPhysicalPointLifetime.table_words (table.P.read slot) s
    (BinaryPhysicalPointLifetime.wordCap s K) (hC.2.1 slot) (fun j => (hH slot j).1)
    (by unfold BinaryPhysicalPointLifetime.wordCap; have h := le_max_left s (K+2); omega)
  have hq := BinaryPhysicalPointLifetime.table_words (table.Q.read slot) s
    (BinaryPhysicalPointLifetime.wordCap s K) (hC.2.2 slot) (fun j => (hH slot j).2)
    (by unfold BinaryPhysicalPointLifetime.wordCap; have h := le_max_left s (K+2); omega)
  have h := sample_work (table.P.read slot).data.toList (table.Q.read slot).data.toList (List.ofFn bits)
    (by rw [Array.length_toList,Array.length_toList,(table.P.read slot).size,(table.Q.read slot).size])
    (BinaryPhysicalPointLifetime.wordCap s K)
    (by simp only [List.length_ofFn]; unfold BinaryPhysicalPointLifetime.wordCap; have h := le_max_right s (K+2); omega) hp hq
  have hCount : (table.P.read slot).data.toList.length = n := by rw [Array.length_toList,(table.P.read slot).size]
  simp only [List.length_ofFn] at h
  exact h.trans_eq (congrArg (fun N => BinaryTapePointLifetime.bound N (BinaryPhysicalPointLifetime.wordCap s K) K) hCount)

end Blotto.BinaryTapePointWork
