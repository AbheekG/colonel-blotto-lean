import Blotto.BinaryPhysicalHeapInputLifetime
import Blotto.BinaryMultiplication
import Blotto.BinaryCarryCounterSize
import Blotto.BinaryPRGHeapResourcePolynomial

/-! Boolean calculation of the two-tree builder allowance. The data path uses
carry counting, full addition, and schoolbook multiplication. Natural values
and work fields are specifications in the existing Boolean/list-cell model;
native observer arithmetic and reference ownership remain separate. -/

namespace Blotto.BinaryPhysicalBuildAllowance
open BinaryRationalNormalization BinarySeedPreparationSpace
open BinaryPRGPhysicalRawRequestLifetime (Request)
set_option autoImplicit false
set_option maxHeartbeats 1500000

def hundred : List Bool := [false,false,true,false,false,true,true]
def eight : List Bool := [false,false,false,true]

theorem hundred_value : BinaryBigEndian.littleValue hundred = 100 := by decide
theorem eight_value : BinaryBigEndian.littleValue eight = 8 := by decide

def nodesWord : List Bool → List Bool
  | [] => [true]
  | _ :: rest => true :: nodesWord rest

theorem nodesWord_length (ruler : List Bool) :
    (nodesWord ruler).length = ruler.length+1 := by
  induction ruler with
  | nil => rfl
  | cons bit rest ih => simp only [nodesWord,List.length_cons,ih]

theorem nodesWord_value (ruler : List Bool) :
    BinaryBigEndian.littleValue (nodesWord ruler) =
      BinaryPRGWordStoreHeapMachine.nodes ruler.length := by
  induction ruler with
  | nil => rfl
  | cons bit rest ih =>
      have hp := Nat.two_pow_pos (rest.length+1)
      simp only [nodesWord,BinaryBigEndian.littleValue,ite_true,ih,
        BinaryPRGWordStoreHeapMachine.nodes,List.length_cons,pow_succ]
      omega

def nodesWordWithWork : List Bool → List Bool × ℕ
  | [] => ([true],2)
  | _ :: rest =>
      let later := nodesWordWithWork rest
      (true :: later.1,later.2+2)

theorem nodesWordWithWork_erases (ruler : List Bool) :
    (nodesWordWithWork ruler).1 = nodesWord ruler := by
  induction ruler with
  | nil => rfl
  | cons bit rest ih => simp only [nodesWordWithWork,nodesWord,ih]

theorem nodesWordWithWork_work (ruler : List Bool) :
    (nodesWordWithWork ruler).2 = 2*(ruler.length+1) := by
  induction ruler with
  | nil => rfl
  | cons bit rest ih => simp only [nodesWordWithWork,List.length_cons,ih]; omega

def treeWord (nodes tape : List Bool) : List Bool :=
  let counted := BinaryCarryCounter.count tape [true]
  let square := BinaryMultiplication.multiply counted counted
  let scaled := BinaryMultiplication.multiply hundred square
  BinaryMultiplication.multiply nodes (BinaryAddition.add scaled eight)

def treeWithWork (nodes tape : List Bool) : List Bool × ℕ :=
  let counted := BinaryPRGWordStoreHeapMachine.countWithWork tape [true]
  let square := BinaryMultiplication.multiply counted.1 counted.1
  let scaled := BinaryMultiplication.multiply hundred square
  let allocation := BinaryAddition.add scaled eight
  (BinaryMultiplication.multiply nodes allocation,
    counted.2.work + BinaryMultiplication.work counted.1 counted.1 +
      BinaryMultiplication.work hundred square + BinaryAddition.bitWork scaled eight +
      BinaryMultiplication.work nodes allocation + 16)

theorem treeWithWork_erases (nodes tape : List Bool) :
    (treeWithWork nodes tape).1 = treeWord nodes tape := by
  simp only [treeWithWork,treeWord,BinaryPRGWordStoreHeapMachine.countWithWork_erasure]

theorem treeWithWork_value (nodes tape : List Bool) :
    BinaryBigEndian.littleValue (treeWithWork nodes tape).1 =
      BinaryBigEndian.littleValue nodes *
        (BinaryPRGWordStoreHeapMachine.allocationBound tape.length+8) := by
  unfold treeWithWork
  dsimp only
  rw [BinaryMultiplication.multiply_value,BinaryAddition.add_value,
    BinaryMultiplication.multiply_value,BinaryMultiplication.multiply_value,
    BinaryPRGWordStoreHeapMachine.countWithWork_erasure,hundred_value,eight_value]
  have hCount := BinaryCarryCounter.count_value tape [true]
  change BinaryBigEndian.littleValue (BinaryCarryCounter.count tape [true]) =
    1+tape.length at hCount
  rw [hCount]
  unfold BinaryPRGWordStoreHeapMachine.allocationBound
  ring

theorem count_word_length (tape : List Bool) :
    (BinaryPRGWordStoreHeapMachine.countWithWork tape [true]).1.length ≤ tape.length+2 := by
  rw [BinaryPRGWordStoreHeapMachine.countWithWork_erasure]
  have h := BinaryCarryCounter.countFromOne_length tape
  have hl := Nat.log2_le_self (tape.length+1)
  unfold binaryWordWidth at h
  omega

theorem treeWithWork_length (nodes tape : List Bool) (S : ℕ)
    (_hS : 8 ≤ S) (hNodes : nodes.length ≤ S) (hTape : tape.length+2 ≤ S) :
    (treeWithWork nodes tape).1.length ≤ 5*S+15 := by
  let counted := BinaryPRGWordStoreHeapMachine.countWithWork tape [true]
  let square := BinaryMultiplication.multiply counted.1 counted.1
  let scaled := BinaryMultiplication.multiply hundred square
  let allocation := BinaryAddition.add scaled eight
  have hc : counted.1.length ≤ S := (count_word_length tape).trans hTape
  have hs := BinaryMultiplication.multiply_length counted.1 counted.1
  have ht := BinaryMultiplication.multiply_length hundred square
  have ha := BinaryAddition.add_length scaled eight
  have hm := BinaryMultiplication.multiply_length nodes allocation
  change square.length ≤ _ at hs
  change scaled.length ≤ _ at ht
  change allocation.length ≤ _ at ha
  change (BinaryMultiplication.multiply nodes allocation).length ≤ _ at hm
  change (BinaryMultiplication.multiply nodes allocation).length ≤ 5*S+15
  norm_num only [hundred,eight,List.length_cons,List.length_nil] at ht ha
  omega

theorem treeWithWork_work_bound (nodes tape : List Bool) (S : ℕ)
    (hS : 8 ≤ S) (hNodes : nodes.length ≤ S) (hTape : tape.length+2 ≤ S) :
    (treeWithWork nodes tape).2 ≤ 10000*(S+1)^2 := by
  let counted := BinaryPRGWordStoreHeapMachine.countWithWork tape [true]
  let square := BinaryMultiplication.multiply counted.1 counted.1
  let scaled := BinaryMultiplication.multiply hundred square
  let allocation := BinaryAddition.add scaled eight
  have hc : counted.1.length ≤ S := (count_word_length tape).trans hTape
  have hs := BinaryMultiplication.multiply_length counted.1 counted.1
  change square.length ≤ _ at hs
  have ht := BinaryMultiplication.multiply_length hundred square
  change scaled.length ≤ _ at ht
  have ha := BinaryAddition.add_length scaled eight
  change allocation.length ≤ _ at ha
  norm_num only [hundred,eight,List.length_cons,List.length_nil] at ht ha
  have hSquare : square.length ≤ 3*S := by omega
  have hScaled : scaled.length ≤ 3*S+14 := by omega
  have hAllocation : allocation.length ≤ 3*S+15 := by omega
  have hCount := (BinaryPRGWordStoreHeapMachine.countWithWork_bounds tape [true]).1
  change counted.2.work ≤ _ at hCount
  have hCountTop : counted.2.work ≤ 12*S^2 := by
    unfold BinaryPRGWordStoreHeapMachine.countBound at hCount
    simp only [List.length_singleton] at hCount
    have hm := Nat.mul_le_mul (show tape.length+1 ≤ S by omega) hTape
    nlinarith
  have hSquareWork := BinaryMultiplication.work_bound counted.1 counted.1
  have hSquareTop : BinaryMultiplication.work counted.1 counted.1 ≤
      1+S*(22*(3*S+2)+3) := by
    exact hSquareWork.trans (Nat.add_le_add_left
      (Nat.mul_le_mul hc (show 22*(2*counted.1.length+counted.1.length+2)+3 ≤
        22*(3*S+2)+3 by omega)) 1)
  have hScaleWork := BinaryMultiplication.work_bound hundred square
  have hScaleTop : BinaryMultiplication.work hundred square ≤
      1+7*(22*(3*S+16)+3) := by
    norm_num only [hundred,List.length_cons,List.length_nil] at hScaleWork
    exact hScaleWork.trans (by omega)
  have hAdd := BinaryAddition.bitWork_bound scaled eight
  have hAddTop : BinaryAddition.bitWork scaled eight ≤ 22*(3*S+15) := by
    norm_num only [eight,List.length_cons,List.length_nil] at hAdd
    exact hAdd.trans (Nat.mul_le_mul_left 22 (by omega))
  have hMul := BinaryMultiplication.work_bound nodes allocation
  have hMulTop : BinaryMultiplication.work nodes allocation ≤
      1+S*(22*(5*S+17)+3) := by
    exact hMul.trans (Nat.add_le_add_left
      (Nat.mul_le_mul hNodes (show 22*(2*nodes.length+allocation.length+2)+3 ≤
        22*(5*S+17)+3 by omega)) 1)
  change counted.2.work + BinaryMultiplication.work counted.1 counted.1 +
    BinaryMultiplication.work hundred square + BinaryAddition.bitWork scaled eight +
    BinaryMultiplication.work nodes allocation + 16 ≤ _
  nlinarith only [hS,hCountTop,hSquareTop,hScaleTop,hAddTop,hMulTop]

def calculate (ruler first second : List Bool) : List Bool :=
  let nodes := nodesWord ruler
  BinaryAddition.add (treeWord nodes first) (treeWord nodes second)

def calculateWithWork (ruler first second : List Bool) : List Bool × ℕ :=
  let nodes := nodesWordWithWork ruler
  let a := treeWithWork nodes.1 first
  let b := treeWithWork nodes.1 second
  (BinaryAddition.add a.1 b.1,
    nodes.2+a.2+b.2+BinaryAddition.bitWork a.1 b.1+8)

theorem calculateWithWork_erases (ruler first second : List Bool) :
    (calculateWithWork ruler first second).1 = calculate ruler first second := by
  simp only [calculateWithWork,calculate,treeWithWork_erases,nodesWordWithWork_erases]

theorem calculateWithWork_value (ruler first second : List Bool) :
    BinaryBigEndian.littleValue (calculateWithWork ruler first second).1 =
      BinaryPRGWordStoreHeapMachine.nodes ruler.length *
        (BinaryPRGWordStoreHeapMachine.allocationBound first.length+8)+
      BinaryPRGWordStoreHeapMachine.nodes ruler.length *
        (BinaryPRGWordStoreHeapMachine.allocationBound second.length+8) := by
  simp only [calculateWithWork,BinaryAddition.add_value,treeWithWork_value,
    nodesWordWithWork_erases,nodesWord_value]

theorem calculateWithWork_bound (ruler first second : List Bool) :
    (calculateWithWork ruler first second).2 ≤
      30000*(ruler.length+first.length+second.length+9)^2 := by
  let S := ruler.length+first.length+second.length+8
  have hS : 8 ≤ S := by dsimp only [S]; omega
  have hNodes : (nodesWord ruler).length ≤ S := by
    rw [nodesWord_length]
    dsimp only [S]
    omega
  have hFirst : first.length+2 ≤ S := by dsimp only [S]; omega
  have hSecond : second.length+2 ≤ S := by dsimp only [S]; omega
  have ha := treeWithWork_work_bound (nodesWord ruler) first S hS hNodes hFirst
  have hb := treeWithWork_work_bound (nodesWord ruler) second S hS hNodes hSecond
  have hal := treeWithWork_length (nodesWord ruler) first S hS hNodes hFirst
  have hbl := treeWithWork_length (nodesWord ruler) second S hS hNodes hSecond
  have hAdd := BinaryAddition.bitWork_bound
    (treeWithWork (nodesWord ruler) first).1 (treeWithWork (nodesWord ruler) second).1
  have hAddTop : BinaryAddition.bitWork
      (treeWithWork (nodesWord ruler) first).1 (treeWithWork (nodesWord ruler) second).1 ≤
      22*(5*S+16) := hAdd.trans (Nat.mul_le_mul_left 22 (by omega))
  simp only [calculateWithWork,nodesWordWithWork_erases,nodesWordWithWork_work]
  change 2*(ruler.length+1)+(treeWithWork (nodesWord ruler) first).2+
    (treeWithWork (nodesWord ruler) second).2+
    BinaryAddition.bitWork (treeWithWork (nodesWord ruler) first).1
      (treeWithWork (nodesWord ruler) second).1+8 ≤ _
  change _ ≤ 30000*(S+1)^2
  have hRuler : ruler.length+1 ≤ S := by dsimp only [S]; omega
  nlinarith only [ha,hb,hAddTop,hRuler,hS]

theorem calculateWithWork_length (ruler first second : List Bool) :
    (calculateWithWork ruler first second).1.length ≤
      5*(ruler.length+first.length+second.length+8)+16 := by
  let S := ruler.length+first.length+second.length+8
  have hS : 8 ≤ S := by dsimp only [S]; omega
  have hNodes : (nodesWord ruler).length ≤ S := by
    rw [nodesWord_length]
    dsimp only [S]
    omega
  have ha := treeWithWork_length (nodesWord ruler) first S hS hNodes
    (by dsimp only [S]; omega)
  have hb := treeWithWork_length (nodesWord ruler) second S hS hNodes
    (by dsimp only [S]; omega)
  have hAdd := BinaryAddition.add_length
    (treeWithWork (nodesWord ruler) first).1 (treeWithWork (nodesWord ruler) second).1
  simp only [calculateWithWork,nodesWordWithWork_erases]
  change (BinaryAddition.add (treeWithWork (nodesWord ruler) first).1
    (treeWithWork (nodesWord ruler) second).1).length ≤ 5*S+16
  omega

/-- This companion builds the physical trees once and returns the Boolean
allowance calculated from precisely those two heap tapes. -/
def rawArraysWithTraceAndAllowance (capacity resource : List SignedWord) :
    (((Σ ruler : List Bool,
      BinaryPhysicalHeapInputLifetime.RawArraysAt capacity resource ruler) × Trace) ×
      List Bool) × ℕ :=
  let built := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource
  let calculated := calculateWithWork built.1.1
    built.1.2.1.heap.tape built.1.2.2.heap.tape
  ((built,calculated.1),calculated.2)

theorem rawArraysWithTraceAndAllowance_erases (capacity resource : List SignedWord) :
    (rawArraysWithTraceAndAllowance capacity resource).1.1 =
      BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource := rfl

theorem rawArraysWithTraceAndAllowance_data (capacity resource : List SignedWord) :
    let built := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource
    (rawArraysWithTraceAndAllowance capacity resource).1 =
      (built,calculate built.1.1 built.1.2.1.heap.tape built.1.2.2.heap.tape) := by
  simp only [rawArraysWithTraceAndAllowance,calculateWithWork_erases]

theorem rawArraysWithTraceAndAllowance_value (capacity resource : List SignedWord) :
    BinaryBigEndian.littleValue (rawArraysWithTraceAndAllowance capacity resource).1.2 =
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        capacity resource).2 := by
  unfold rawArraysWithTraceAndAllowance
  dsimp only
  rw [calculateWithWork_value]
  rfl

theorem rawArraysWithTraceAndAllowance_input_work_bound {n : ℕ}
    (capacity resource : FixedArrayTable n SignedWord) (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    (rawArraysWithTraceAndAllowance capacity.data.toList resource.data.toList).2 ≤
      30000*(binaryWordWidth n+
        2*BinaryPRGHeapResourceInputBounds.initialHeapBound n W+9)^2 := by
  let ruler := (BinaryPRGHeapAllocationLifetime.countWithTrace capacity.data.toList []).1
  let K := BinaryPRGHeapResourceInputBounds.initialHeapBound n W
  have hRuler : ruler = BinaryCarryCounter.count capacity.data.toList [] :=
    (BinaryPRGHeapAllocationLifetime.countWithTrace_erasure
      capacity.data.toList []).trans
      (BinaryPRGWordStoreHeapMachine.countWithWork_erasure capacity.data.toList [])
  have hDepth : ruler.length ≤ binaryWordWidth n := by
    rw [hRuler]
    exact BinaryPRGHeapResourceInputBounds.source_depth capacity
  have hCap :
      (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
        BinaryRationalOpcode.zero ruler capacity.data.toList).1.heap.tape.length ≤ K := by
    rw [BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_erasure,hRuler]
    exact BinaryPRGHeapResourceInputBounds.prepared_heap_bound
      capacity capacity W hW hCapacity
  have hRes :
      (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
        BinaryRationalOpcode.zero ruler resource.data.toList).1.heap.tape.length ≤ K := by
    rw [BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_erasure,hRuler]
    exact BinaryPRGHeapResourceInputBounds.prepared_heap_bound
      capacity resource W hW hResource
  have hCalc := calculateWithWork_bound ruler
    (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
      BinaryRationalOpcode.zero ruler capacity.data.toList).1.heap.tape
    (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
      BinaryRationalOpcode.zero ruler resource.data.toList).1.heap.tape
  have hSize : ruler.length+
      (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
        BinaryRationalOpcode.zero ruler capacity.data.toList).1.heap.tape.length+
      (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
        BinaryRationalOpcode.zero ruler resource.data.toList).1.heap.tape.length+9 ≤
        binaryWordWidth n+2*K+9 := by omega
  have hTop := Nat.mul_le_mul_left 30000 (Nat.pow_le_pow_left hSize 2)
  exact hCalc.trans hTop

open BinaryPRGHeapResourcePolynomial in
theorem calculationEnvelope_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => 30000*(binaryWordWidth p.count+
      2*BinaryPRGHeapResourceInputBounds.initialHeapBound p.count p.wordWidth+9)^2) := by
  simp only [BinaryPRGHeapResourceInputBounds.initialHeapBound,
    BinaryPRGWordStoreHeap.heapBound]
  resource_polynomial

theorem uniform_rawArrays_calculation_work : ∃ C d : ℕ,
    ∀ {n : ℕ} (capacity resource : FixedArrayTable n SignedWord) (W : ℕ),
      1 ≤ W → (∀ j,width (capacity.read j) ≤ W) →
      (∀ j,width (resource.read j) ≤ W) →
      (rawArraysWithTraceAndAllowance capacity.data.toList resource.data.toList).2 ≤
        C*(n+W+2)^d := by
  obtain ⟨C,d,hPoly⟩ := calculationEnvelope_polynomial
  refine ⟨C,d,?_⟩
  intro n capacity resource W hW hCapacity hResource
  have h := hPoly (⟨n,W,0,0,0⟩ : BinaryPRGHeapResourcePolynomial.Parameters)
  have hSize : BinaryPRGHeapResourcePolynomial.inputSize
      (⟨n,W,0,0,0⟩ : BinaryPRGHeapResourcePolynomial.Parameters)+1 = n+W+2 := by
    simp [BinaryPRGHeapResourcePolynomial.inputSize,binaryWordWidth]
  rw [hSize] at h
  exact (rawArraysWithTraceAndAllowance_input_work_bound
    capacity resource W hW hCapacity hResource).trans h

theorem uniform_request_readback_calculation_work : ∃ C d : ℕ,
    ∀ {n : ℕ} (request : Request n) (rich : Bool),
      let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        request).1.1.getD ([],[])
      (rawArraysWithTraceAndAllowance
        words.1 (if rich then words.1 else words.2)).2 ≤
        C*(n+BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request+2)^d := by
  obtain ⟨C,d,hBound⟩ := uniform_rawArrays_calculation_work
  refine ⟨C,d,?_⟩
  intro n request rich
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let W := BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request
  have hW := BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth_pos request
  obtain ⟨hl,hr⟩ :=
    BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth_inputs request
  have hCapacity : ∀ j,width (selected.length.read j) ≤ W := by
    cases rich <;> exact hl
  have hResource : ∀ j,width (selected.resource.read j) ≤ W := by
    cases rich
    · exact hr
    · exact hl
  have h := hBound selected.length selected.resource W hW hCapacity hResource
  have hWords :
      (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        request).1.1.getD ([],[]) =
      (request.logical.request.prepared.lengths.data.toList,
        request.logical.request.prepared.poorResources.data.toList) := by
    change (BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).1.getD
      ([],[]) = _
    rw [BinaryPhysicalNumericalReadbackLifetime.request_pair_words]
    rfl
  dsimp only
  rw [hWords]
  cases rich <;> simpa [selected,W,BinaryPRGResourceWork.resourceInput,
    BinaryPRGPreparation.Prepared.rich,BinaryPRGPreparation.Prepared.poor] using h

theorem accepted_readback_calculation_work_polynomial : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ rich : Bool,
      let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        parsed.1.2).1.1.getD ([],[])
      (rawArraysWithTraceAndAllowance
        words.1 (if rich then words.1 else words.2)).2 ≤ C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ := uniform_request_readback_calculation_work
  refine ⟨C*130^d,2*d,?_⟩
  intro frame parsed hParsed rich
  let X := frame.length+3
  have hX : 3 ≤ X := by dsimp only [X]; omega
  have hn := BinaryPhysicalNumericalReadbackLifetime.accepted_dimension
    frame parsed hParsed
  have hW := BinaryPhysicalNumericalReadbackLifetime.accepted_physicalWordWidth_bound
    frame parsed hParsed
  have hHeap : PRGPhysicalArrayInterface.heapCap frame.length ≤ 128*X^2 := by
    unfold PRGPhysicalArrayInterface.heapCap
    dsimp only [X]
    nlinarith
  have hSize : parsed.1.1+
      BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth parsed.1.2+2 ≤
        130*X^2 := by
    have hSquare : X ≤ X^2 := by nlinarith
    have hThree : 3 ≤ X^2 := by nlinarith
    dsimp only [X] at *
    omega
  have h := hBound parsed.1.2 rich
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  have hTop : C*(130*X^2)^d = (C*130^d)*X^(2*d) := by
    rw [mul_pow,pow_mul]
    ring
  exact h.trans (hp.trans_eq hTop)

end Blotto.BinaryPhysicalBuildAllowance
