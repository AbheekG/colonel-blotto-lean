import Blotto.SequentialFairPRGSource
import Blotto.BinaryCompleteRepresentationSpace

/-! Complete declared-source cost and representation contracts for the four
fixed sequential-source runners. All original cost fields remain in the sum;
source-bit calls are added. Borrowed tape storage is counted explicitly.
Representation prices remain explicit; this is not native allocator calibration. -/
namespace Blotto.SequentialFairPRGSourceContracts
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage SequentialFairPRGSource
open BinaryCompleteRepresentationSpace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def singleLedger (arithmetic : ℕ) (factoryReturned : Single (List Bool)) : ℕ :=
  let returned := factoryReturned.1
  let produced := returned.1.1.1.1
  (arithmetic+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2)

def pairedLedger (arithmetic : ℕ) (factoryReturned : Pair (List Bool)) : ℕ :=
  let returned := factoryReturned.1
  let produced := returned.1.1.1.1
  (arithmetic+produced.1.1.2+BinaryBigEndian.littleValue produced.1.1.1.1.2.1+BinaryBigEndian.littleValue produced.1.1.1.1.2.2+usage produced.1.1.1.2+
      BinaryGenerationExecutionCharges.total produced.1.2+produced.2.1.1+produced.2.1.2+produced.2.2.1.1.1.1.1.1.1.1.1.1+produced.2.2.1.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.1.2+produced.2.2.1.1.1.1.1.2+produced.2.2.1.1.1.1.2+produced.2.2.1.1.1.2+produced.2.2.1.1.2+produced.2.2.1.2+produced.2.2.2.1.1.1.1.1.1+produced.2.2.2.1.1.1.1.1.2+produced.2.2.2.1.1.1.1.2+produced.2.2.2.1.1.1.2+produced.2.2.2.1.1.2+produced.2.2.2.1.2+produced.2.2.2.2)+(returned.1.1.1.2+returned.1.1.2+returned.1.2+returned.2+factoryReturned.2)

def generatedCost (rich : Bool) (frame tape : List Bool) : ℕ :=
  singleLedger (BinaryCompleteRequestArithmeticEntryWork.generatedCost SequentialFairBitSource.next rich frame tape)
    (generated rich frame tape)+drawCount frame

theorem generated_cost : ∃ C d : ℕ,∀ (rich : Bool) (frame tape : List Bool),
    generatedCost rich frame tape ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := BinaryReturnedFactoryExtras.generated_complete_joint
  refine ⟨C+6066,d+1,?_⟩
  intro rich frame tape
  have ho := (h SequentialFairBitSource.next rich frame tape).1
  have hn := drawCount_bound frame
  change singleLedger _ (generated rich frame tape) ≤ _ at ho
  have hp := Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show d ≤ d+1 by omega)
  have hl : frame.length+1 ≤ (frame.length+1)^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show 1 ≤ d+1 by omega)
  unfold generatedCost BinaryPRGSeedRequestBound.seedCountBound at *
  nlinarith only [ho,hn,Nat.mul_le_mul_left C hp,hl]

theorem generated_prefix (prices : Representation) (rich : Bool) (frame tape : List Bool) (steps : ℕ) :
    representedWorkspace prices (generated rich frame tape).1.1.1.1.1.1.1.1.2 steps ≤
      units prices*(generatedCost rich frame tape) := by
  have hLen := BinaryCompleteTraceHeaders.generated_length SequentialFairBitSource.next rich frame tape
  change (generated rich frame tape).1.1.1.1.1.1.1.1.2.length ≤
    BinaryGenerationExecutionCharges.total (generated rich frame tape).1.1.1.1.1.1.2 at hLen
  have hHeader := BinaryCompleteTraceHeaders.arrayRecords_le_length (generated rich frame tape).1.1.1.1.1.1.1.1.2
  apply represented_le
  unfold generatedCost singleLedger
  dsimp only
  omega

theorem generated_complete : ∃ C d : ℕ,∀ (prices : Representation) (rich : Bool) 
    (frame tape : List Bool) (steps : ℕ),
    generatedCost rich frame tape ≤ C*(frame.length+1)^d ∧
      prices.listCellUnits*(frame.length+tape.length)+representedWorkspace prices (generated rich frame tape).1.1.1.1.1.1.1.1.2 steps ≤
        prices.listCellUnits*(frame.length+tape.length)+units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := generated_cost
  refine ⟨C,d,?_⟩
  intro prices rich frame tape steps
  have hc := h rich frame tape
  exact ⟨hc,Nat.add_le_add_left ((generated_prefix prices rich frame tape steps).trans (Nat.mul_le_mul_left (units prices) hc)) _⟩

def parsedGeneratedCost (rich : Bool) (frame tape : List Bool) : ℕ :=
  singleLedger (BinaryCompleteRequestArithmeticEntryWork.generatedCost SequentialFairBitSource.next rich frame tape)
    (parsedGenerated rich frame tape)+drawCount frame

theorem parsedGenerated_cost : ∃ C d : ℕ,∀ (rich : Bool) (frame tape : List Bool),
    parsedGeneratedCost rich frame tape ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := BinaryReturnedFactoryExtras.parsedGenerated_complete_joint
  refine ⟨C+6066,d+1,?_⟩
  intro rich frame tape
  have ho := (h SequentialFairBitSource.next rich frame tape).1
  have hn := drawCount_bound frame
  change singleLedger _ (parsedGenerated rich frame tape) ≤ _ at ho
  have hp := Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show d ≤ d+1 by omega)
  have hl : frame.length+1 ≤ (frame.length+1)^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show 1 ≤ d+1 by omega)
  unfold parsedGeneratedCost BinaryPRGSeedRequestBound.seedCountBound at *
  nlinarith only [ho,hn,Nat.mul_le_mul_left C hp,hl]

theorem parsedGenerated_prefix (prices : Representation) (rich : Bool) (frame tape : List Bool) (steps : ℕ) :
    representedWorkspace prices (parsedGenerated rich frame tape).1.1.1.1.1.1.1.1.2 steps ≤
      units prices*(parsedGeneratedCost rich frame tape) := by
  have hLen := BinaryCompleteTraceHeaders.parsedGenerated_length SequentialFairBitSource.next rich frame tape
  change (parsedGenerated rich frame tape).1.1.1.1.1.1.1.1.2.length ≤
    BinaryGenerationExecutionCharges.total (parsedGenerated rich frame tape).1.1.1.1.1.1.2 at hLen
  have hHeader := BinaryCompleteTraceHeaders.arrayRecords_le_length (parsedGenerated rich frame tape).1.1.1.1.1.1.1.1.2
  apply represented_le
  unfold parsedGeneratedCost singleLedger
  dsimp only
  omega

theorem parsedGenerated_complete : ∃ C d : ℕ,∀ (prices : Representation) (rich : Bool) 
    (frame tape : List Bool) (steps : ℕ),
    parsedGeneratedCost rich frame tape ≤ C*(frame.length+1)^d ∧
      prices.listCellUnits*(frame.length+tape.length)+representedWorkspace prices (parsedGenerated rich frame tape).1.1.1.1.1.1.1.1.2 steps ≤
        prices.listCellUnits*(frame.length+tape.length)+units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedGenerated_cost
  refine ⟨C,d,?_⟩
  intro prices rich frame tape steps
  have hc := h rich frame tape
  exact ⟨hc,Nat.add_le_add_left ((parsedGenerated_prefix prices rich frame tape steps).trans (Nat.mul_le_mul_left (units prices) hc)) _⟩

def pairCost (frame tape : List Bool) : ℕ :=
  pairedLedger (BinaryCompleteRequestArithmeticEntryWork.pairCost SequentialFairBitSource.next frame tape)
    (pair frame tape)+(drawCount frame+drawCount frame)

theorem pair_cost : ∃ C d : ℕ,∀ (frame tape : List Bool),
    pairCost frame tape ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := BinaryReturnedFactoryExtras.pair_complete_joint
  refine ⟨C+6066,d+1,?_⟩
  intro frame tape
  have ho := (h SequentialFairBitSource.next frame tape).1
  have hn := drawCount_bound frame
  change pairedLedger _ (pair frame tape) ≤ _ at ho
  have hp := Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show d ≤ d+1 by omega)
  have hl : frame.length+1 ≤ (frame.length+1)^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show 1 ≤ d+1 by omega)
  unfold pairCost BinaryPRGSeedRequestBound.seedCountBound at *
  nlinarith only [ho,hn,Nat.mul_le_mul_left C hp,hl]

theorem pair_prefix (prices : Representation) (frame tape : List Bool) (steps : ℕ) :
    representedWorkspace prices (pair frame tape).1.1.1.1.1.1.1.1.2 steps ≤
      units prices*(pairCost frame tape) := by
  have hLen := BinaryCompleteTraceHeaders.pair_length SequentialFairBitSource.next frame tape
  change (pair frame tape).1.1.1.1.1.1.1.1.2.length ≤
    BinaryGenerationExecutionCharges.total (pair frame tape).1.1.1.1.1.1.2 at hLen
  have hHeader := BinaryCompleteTraceHeaders.arrayRecords_le_length (pair frame tape).1.1.1.1.1.1.1.1.2
  apply represented_le
  unfold pairCost pairedLedger
  dsimp only
  omega

theorem pair_complete : ∃ C d : ℕ,∀ (prices : Representation) 
    (frame tape : List Bool) (steps : ℕ),
    pairCost frame tape ≤ C*(frame.length+1)^d ∧
      prices.listCellUnits*(frame.length+tape.length)+representedWorkspace prices (pair frame tape).1.1.1.1.1.1.1.1.2 steps ≤
        prices.listCellUnits*(frame.length+tape.length)+units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := pair_cost
  refine ⟨C,d,?_⟩
  intro prices frame tape steps
  have hc := h frame tape
  exact ⟨hc,Nat.add_le_add_left ((pair_prefix prices frame tape steps).trans (Nat.mul_le_mul_left (units prices) hc)) _⟩

def parsedPairCost (frame tape : List Bool) : ℕ :=
  pairedLedger (BinaryCompleteRequestArithmeticEntryWork.parsedPairCost SequentialFairBitSource.next frame tape)
    (parsedPair frame tape)+(drawCount frame+drawCount frame)

theorem parsedPair_cost : ∃ C d : ℕ,∀ (frame tape : List Bool),
    parsedPairCost frame tape ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := BinaryReturnedFactoryExtras.parsedPair_complete_joint
  refine ⟨C+6066,d+1,?_⟩
  intro frame tape
  have ho := (h SequentialFairBitSource.next frame tape).1
  have hn := drawCount_bound frame
  change pairedLedger _ (parsedPair frame tape) ≤ _ at ho
  have hp := Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show d ≤ d+1 by omega)
  have hl : frame.length+1 ≤ (frame.length+1)^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show 1 ≤ d+1 by omega)
  unfold parsedPairCost BinaryPRGSeedRequestBound.seedCountBound at *
  nlinarith only [ho,hn,Nat.mul_le_mul_left C hp,hl]

theorem parsedPair_prefix (prices : Representation) (frame tape : List Bool) (steps : ℕ) :
    representedWorkspace prices (parsedPair frame tape).1.1.1.1.1.1.1.1.2 steps ≤
      units prices*(parsedPairCost frame tape) := by
  have hLen := BinaryCompleteTraceHeaders.parsedPair_length SequentialFairBitSource.next frame tape
  change (parsedPair frame tape).1.1.1.1.1.1.1.1.2.length ≤
    BinaryGenerationExecutionCharges.total (parsedPair frame tape).1.1.1.1.1.1.2 at hLen
  have hHeader := BinaryCompleteTraceHeaders.arrayRecords_le_length (parsedPair frame tape).1.1.1.1.1.1.1.1.2
  apply represented_le
  unfold parsedPairCost pairedLedger
  dsimp only
  omega

theorem parsedPair_complete : ∃ C d : ℕ,∀ (prices : Representation) 
    (frame tape : List Bool) (steps : ℕ),
    parsedPairCost frame tape ≤ C*(frame.length+1)^d ∧
      prices.listCellUnits*(frame.length+tape.length)+representedWorkspace prices (parsedPair frame tape).1.1.1.1.1.1.1.1.2 steps ≤
        prices.listCellUnits*(frame.length+tape.length)+units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedPair_cost
  refine ⟨C,d,?_⟩
  intro prices frame tape steps
  have hc := h frame tape
  exact ⟨hc,Nat.add_le_add_left ((parsedPair_prefix prices frame tape steps).trans (Nat.mul_le_mul_left (units prices) hc)) _⟩

theorem generated_fair_complete : ∃ C d : ℕ,∀ (prices : Representation) (rich : Bool) 
    (frame : List Bool) (bits : Fin (drawCount frame) → Bool) (steps : ℕ),
    generatedCost rich frame (List.ofFn bits)+frame.length+(List.ofFn bits).length ≤ C*(frame.length+1)^d ∧
      prices.listCellUnits*(frame.length+(List.ofFn bits).length)+
        representedWorkspace prices (generated rich frame (List.ofFn bits)).1.1.1.1.1.1.1.1.2 steps ≤
        units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := generated_cost
  refine ⟨C+6068,d+1,?_⟩
  intro prices rich frame bits steps
  have hc := h rich frame (List.ofFn bits)
  have hn := single_tape_bound frame bits
  have hp := Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show d ≤ d+1 by omega)
  have hl : frame.length+1 ≤ (frame.length+1)^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show 1 ≤ d+1 by omega)
  have hTotal : generatedCost rich frame (List.ofFn bits)+frame.length+(List.ofFn bits).length ≤
      (C+6068)*(frame.length+1)^(d+1) := by
    unfold BinaryPRGSeedRequestBound.seedCountBound at hn
    nlinarith only [hc,hn,Nat.mul_le_mul_left C hp,hl]
  refine ⟨hTotal,?_⟩
  have hCell : prices.listCellUnits ≤ units prices := by unfold units; omega
  have hBorrow := Nat.mul_le_mul_right (frame.length+(List.ofFn bits).length) hCell
  calc
    _ ≤ units prices*(frame.length+(List.ofFn bits).length)+
        units prices*(generatedCost rich frame (List.ofFn bits)) :=
      Nat.add_le_add hBorrow (generated_prefix prices rich frame (List.ofFn bits) steps)
    _ = units prices*(generatedCost rich frame (List.ofFn bits)+frame.length+(List.ofFn bits).length) := by ring
    _ ≤ _ := Nat.mul_le_mul_left (units prices) hTotal

theorem parsedGenerated_fair_complete : ∃ C d : ℕ,∀ (prices : Representation) (rich : Bool) 
    (frame : List Bool) (bits : Fin (drawCount frame) → Bool) (steps : ℕ),
    parsedGeneratedCost rich frame (List.ofFn bits)+frame.length+(List.ofFn bits).length ≤ C*(frame.length+1)^d ∧
      prices.listCellUnits*(frame.length+(List.ofFn bits).length)+
        representedWorkspace prices (parsedGenerated rich frame (List.ofFn bits)).1.1.1.1.1.1.1.1.2 steps ≤
        units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedGenerated_cost
  refine ⟨C+6068,d+1,?_⟩
  intro prices rich frame bits steps
  have hc := h rich frame (List.ofFn bits)
  have hn := single_tape_bound frame bits
  have hp := Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show d ≤ d+1 by omega)
  have hl : frame.length+1 ≤ (frame.length+1)^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show 1 ≤ d+1 by omega)
  have hTotal : parsedGeneratedCost rich frame (List.ofFn bits)+frame.length+(List.ofFn bits).length ≤
      (C+6068)*(frame.length+1)^(d+1) := by
    unfold BinaryPRGSeedRequestBound.seedCountBound at hn
    nlinarith only [hc,hn,Nat.mul_le_mul_left C hp,hl]
  refine ⟨hTotal,?_⟩
  have hCell : prices.listCellUnits ≤ units prices := by unfold units; omega
  have hBorrow := Nat.mul_le_mul_right (frame.length+(List.ofFn bits).length) hCell
  calc
    _ ≤ units prices*(frame.length+(List.ofFn bits).length)+
        units prices*(parsedGeneratedCost rich frame (List.ofFn bits)) :=
      Nat.add_le_add hBorrow (parsedGenerated_prefix prices rich frame (List.ofFn bits) steps)
    _ = units prices*(parsedGeneratedCost rich frame (List.ofFn bits)+frame.length+(List.ofFn bits).length) := by ring
    _ ≤ _ := Nat.mul_le_mul_left (units prices) hTotal

theorem pair_fair_complete : ∃ C d : ℕ,∀ (prices : Representation) 
    (frame : List Bool) (bits : Fin (drawCount frame+drawCount frame) → Bool) (steps : ℕ),
    pairCost frame (List.ofFn bits)+frame.length+(List.ofFn bits).length ≤ C*(frame.length+1)^d ∧
      prices.listCellUnits*(frame.length+(List.ofFn bits).length)+
        representedWorkspace prices (pair frame (List.ofFn bits)).1.1.1.1.1.1.1.1.2 steps ≤
        units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := pair_cost
  refine ⟨C+6068,d+1,?_⟩
  intro prices frame bits steps
  have hc := h frame (List.ofFn bits)
  have hn := pair_tape_bound frame bits
  have hp := Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show d ≤ d+1 by omega)
  have hl : frame.length+1 ≤ (frame.length+1)^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show 1 ≤ d+1 by omega)
  have hTotal : pairCost frame (List.ofFn bits)+frame.length+(List.ofFn bits).length ≤
      (C+6068)*(frame.length+1)^(d+1) := by
    unfold BinaryPRGSeedRequestBound.seedCountBound at hn
    nlinarith only [hc,hn,Nat.mul_le_mul_left C hp,hl]
  refine ⟨hTotal,?_⟩
  have hCell : prices.listCellUnits ≤ units prices := by unfold units; omega
  have hBorrow := Nat.mul_le_mul_right (frame.length+(List.ofFn bits).length) hCell
  calc
    _ ≤ units prices*(frame.length+(List.ofFn bits).length)+
        units prices*(pairCost frame (List.ofFn bits)) :=
      Nat.add_le_add hBorrow (pair_prefix prices frame (List.ofFn bits) steps)
    _ = units prices*(pairCost frame (List.ofFn bits)+frame.length+(List.ofFn bits).length) := by ring
    _ ≤ _ := Nat.mul_le_mul_left (units prices) hTotal

theorem parsedPair_fair_complete : ∃ C d : ℕ,∀ (prices : Representation) 
    (frame : List Bool) (bits : Fin (drawCount frame+drawCount frame) → Bool) (steps : ℕ),
    parsedPairCost frame (List.ofFn bits)+frame.length+(List.ofFn bits).length ≤ C*(frame.length+1)^d ∧
      prices.listCellUnits*(frame.length+(List.ofFn bits).length)+
        representedWorkspace prices (parsedPair frame (List.ofFn bits)).1.1.1.1.1.1.1.1.2 steps ≤
        units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedPair_cost
  refine ⟨C+6068,d+1,?_⟩
  intro prices frame bits steps
  have hc := h frame (List.ofFn bits)
  have hn := pair_tape_bound frame bits
  have hp := Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show d ≤ d+1 by omega)
  have hl : frame.length+1 ≤ (frame.length+1)^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < frame.length+1 by omega) (show 1 ≤ d+1 by omega)
  have hTotal : parsedPairCost frame (List.ofFn bits)+frame.length+(List.ofFn bits).length ≤
      (C+6068)*(frame.length+1)^(d+1) := by
    unfold BinaryPRGSeedRequestBound.seedCountBound at hn
    nlinarith only [hc,hn,Nat.mul_le_mul_left C hp,hl]
  refine ⟨hTotal,?_⟩
  have hCell : prices.listCellUnits ≤ units prices := by unfold units; omega
  have hBorrow := Nat.mul_le_mul_right (frame.length+(List.ofFn bits).length) hCell
  calc
    _ ≤ units prices*(frame.length+(List.ofFn bits).length)+
        units prices*(parsedPairCost frame (List.ofFn bits)) :=
      Nat.add_le_add hBorrow (parsedPair_prefix prices frame (List.ofFn bits) steps)
    _ = units prices*(parsedPairCost frame (List.ofFn bits)+frame.length+(List.ofFn bits).length) := by ring
    _ ≤ _ := Nat.mul_le_mul_left (units prices) hTotal

end Blotto.SequentialFairPRGSourceContracts
