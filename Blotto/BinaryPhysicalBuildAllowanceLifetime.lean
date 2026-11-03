import Blotto.BinaryPhysicalBuildAllowance

/-! Actual structural allocation traces for the Boolean builder-allowance
calculator. Every copied bit, intermediate arithmetic result and source
activation remains retained. Native reference bits and observer costs are
separate from this source-cell contract. -/

namespace Blotto.BinaryPhysicalBuildAllowanceLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryPhysicalBuildAllowance
open BinaryRationalNormalization
open BinaryPRGPhysicalRawRequestLifetime (Request)
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem reverse_usage (bits : List Bool) :
    usage (reverseWithTrace bits []).2 ≤ 2*bits.length+1 := by
  have hc := reverseWithTrace_cells bits []
  have ha := reverseWithTrace_arrays bits []
  have hf := reverseWithTrace_frames bits []
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

def addLoopWithTrace : List Bool → List Bool → Bool → List Bool → List Bool × Trace
  | [],[],carry,acc =>
      let reversed := reverseWithTrace (if carry then true :: acc else acc) []
      (reversed.1,wrapList (if carry then 1 else 0) 8 1 [reversed.2])
  | a :: rest,[],carry,acc =>
      let later := addLoopWithTrace rest [] (BinaryAddition.nextCarry a false carry)
        (BinaryAddition.sumBit a false carry :: acc)
      (later.1,wrapList 1 8 2 [later.2])
  | [],b :: rest,carry,acc =>
      let later := addLoopWithTrace [] rest (BinaryAddition.nextCarry false b carry)
        (BinaryAddition.sumBit false b carry :: acc)
      (later.1,wrapList 1 8 2 [later.2])
  | a :: as,b :: bs,carry,acc =>
      let later := addLoopWithTrace as bs (BinaryAddition.nextCarry a b carry)
        (BinaryAddition.sumBit a b carry :: acc)
      (later.1,wrapList 1 8 2 [later.2])

theorem addLoopWithTrace_erases (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (addLoopWithTrace a b carry acc).1 = BinaryAddition.loop a b carry acc := by
  induction a generalizing b carry acc with
  | nil =>
      induction b generalizing carry acc with
      | nil => cases carry <;>
          simp only [addLoopWithTrace,BinaryAddition.loop,ite_true,Bool.false_eq_true,
            ite_false,reverseWithTrace_result,List.reverseAux_eq,List.append_nil]
      | cons bit rest ih => simp only [addLoopWithTrace,BinaryAddition.loop,ih]
  | cons bit rest ih =>
      cases b with
      | nil => simp only [addLoopWithTrace,BinaryAddition.loop,ih]
      | cons other tail => simp only [addLoopWithTrace,BinaryAddition.loop,ih]

theorem addLoopWithTrace_usage (a b : List Bool) (carry : Bool) (acc : List Bool) :
    usage (addLoopWithTrace a b carry acc).2 ≤
      15*max a.length b.length+2*acc.length+15 := by
  induction a generalizing b carry acc with
  | nil =>
      induction b generalizing carry acc with
      | nil =>
          have hr := reverse_usage (if carry then true :: acc else acc)
          have hw := wrapList_usage (if carry then 1 else 0) 8 1
            [(reverseWithTrace (if carry then true :: acc else acc) []).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          cases carry <;>
            simp only [addLoopWithTrace,Bool.false_eq_true,ite_false,ite_true,
              List.length_cons,List.length_nil,Nat.max_self] at hr hw ⊢ <;> omega
      | cons bit rest ih =>
          have hi := ih (BinaryAddition.nextCarry false bit carry)
            (BinaryAddition.sumBit false bit carry :: acc)
          have hw := wrapList_usage 1 8 2
            [(addLoopWithTrace [] rest (BinaryAddition.nextCarry false bit carry)
              (BinaryAddition.sumBit false bit carry :: acc)).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          simp only [List.length_cons,List.length_nil,Nat.zero_max] at hi ⊢
          simp only [addLoopWithTrace]
          omega
  | cons bit rest ih =>
      cases b with
      | nil =>
          have hi := ih [] (BinaryAddition.nextCarry bit false carry)
            (BinaryAddition.sumBit bit false carry :: acc)
          have hw := wrapList_usage 1 8 2
            [(addLoopWithTrace rest [] (BinaryAddition.nextCarry bit false carry)
              (BinaryAddition.sumBit bit false carry :: acc)).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          simp only [List.length_cons,List.length_nil,Nat.max_zero] at hi ⊢
          simp only [addLoopWithTrace]
          omega
      | cons other tail =>
          have hi := ih tail (BinaryAddition.nextCarry bit other carry)
            (BinaryAddition.sumBit bit other carry :: acc)
          have hw := wrapList_usage 1 8 2
            [(addLoopWithTrace rest tail (BinaryAddition.nextCarry bit other carry)
              (BinaryAddition.sumBit bit other carry :: acc)).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          simp only [List.length_cons] at hi ⊢
          simp only [addLoopWithTrace]
          omega

def addWithTrace (a b : List Bool) : List Bool × Trace := addLoopWithTrace a b false []

theorem addWithTrace_erases (a b : List Bool) :
    (addWithTrace a b).1 = BinaryAddition.add a b :=
  addLoopWithTrace_erases a b false []

theorem addWithTrace_usage (a b : List Bool) :
    usage (addWithTrace a b).2 ≤ 15*max a.length b.length+15 := by
  simpa only [addWithTrace,List.length_nil,Nat.mul_zero,Nat.add_zero] using
    addLoopWithTrace_usage a b false []

def multiplyWithTrace : List Bool → List Bool → List Bool × Trace
  | [],_ => ([],wrap 8 1 [])
  | bit :: rest,other =>
      let earlier := multiplyWithTrace rest other
      let shifted := false :: earlier.1
      if bit then
        let added := addWithTrace other shifted
        (added.1,wrapList 1 16 2 [earlier.2,added.2])
      else (shifted,wrapList 1 8 2 [earlier.2])

theorem multiplyWithTrace_erases (a b : List Bool) :
    (multiplyWithTrace a b).1 = BinaryMultiplication.multiply a b := by
  induction a with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> simp only [multiplyWithTrace,BinaryMultiplication.multiply,
        Bool.false_eq_true,ite_false,ite_true,addWithTrace_erases,ih]

theorem multiplyWithTrace_usage (a b : List Bool) :
    usage (multiplyWithTrace a b).2 ≤
      a.length*(30*a.length+15*b.length+53)+9 := by
  induction a with
  | nil => simp [multiplyWithTrace,usage,BinaryPRGHeapPrimitiveLifetime.cells,
      wrap,combine,listCells,arraySlots,framePeak]
  | cons bit rest ih =>
      have hLen := BinaryMultiplication.multiply_length rest b
      have hAdd := addWithTrace_usage b (false :: (multiplyWithTrace rest b).1)
      rw [multiplyWithTrace_erases] at hAdd
      have hAddTop : usage (addWithTrace b
          (false :: (multiplyWithTrace rest b).1)).2 ≤
          30*rest.length+15*b.length+30 := by
        rw [multiplyWithTrace_erases]
        simp only [List.length_cons] at hAdd
        omega
      cases bit
      · have hw := wrapList_usage 1 8 2 [(multiplyWithTrace rest b).2]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
        simp only [multiplyWithTrace,Bool.false_eq_true,ite_false,List.length_cons]
        nlinarith
      · have hw := wrapList_usage 1 16 2
          [(multiplyWithTrace rest b).2,
            (addWithTrace b (false :: (multiplyWithTrace rest b).1)).2]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
        simp only [multiplyWithTrace,ite_true,List.length_cons]
        nlinarith

theorem multiplyWithTrace_uniform_usage (a b : List Bool) (S : ℕ)
    (ha : a.length ≤ S) (hb : b.length ≤ S) :
    usage (multiplyWithTrace a b).2 ≤ 100*(S+1)^2 := by
  have h := multiplyWithTrace_usage a b
  have hm := Nat.mul_le_mul ha
    (show 30*a.length+15*b.length+53 ≤ 45*S+53 by omega)
  nlinarith

def nodesWordWithTrace : List Bool → List Bool × Trace
  | [] => ([true],wrapList 1 8 1 [])
  | _ :: rest =>
      let later := nodesWordWithTrace rest
      (true :: later.1,wrapList 1 8 1 [later.2])

theorem nodesWordWithTrace_erases (ruler : List Bool) :
    (nodesWordWithTrace ruler).1 = nodesWord ruler := by
  induction ruler with
  | nil => rfl
  | cons bit rest ih => simp only [nodesWordWithTrace,nodesWord,ih]

theorem nodesWordWithTrace_usage (ruler : List Bool) :
    usage (nodesWordWithTrace ruler).2 ≤ 12*(ruler.length+1) := by
  induction ruler with
  | nil =>
      have h := wrapList_usage 1 8 1 []
      simp only [List.map_nil,List.sum_nil] at h
      change usage (wrapList 1 8 1 []) ≤ 12*(0+1)
      omega
  | cons bit rest ih =>
      have h := wrapList_usage 1 8 1 [(nodesWordWithTrace rest).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at h
      simp only [nodesWordWithTrace,List.length_cons]
      omega

def treeWithTrace (nodes tape : List Bool) : List Bool × Trace :=
  let counted := BinaryPRGHeapAllocationLifetime.countWithTrace tape [true]
  let square := multiplyWithTrace counted.1 counted.1
  let scaled := multiplyWithTrace hundred square.1
  let allocation := addWithTrace scaled.1 eight
  let product := multiplyWithTrace nodes allocation.1
  (product.1,wrapList 11 64 4
    [counted.2,square.2,scaled.2,allocation.2,product.2])

theorem treeWithTrace_erases (nodes tape : List Bool) :
    (treeWithTrace nodes tape).1 = treeWord nodes tape := by
  simp only [treeWithTrace,treeWord,multiplyWithTrace_erases,addWithTrace_erases,
    BinaryPRGHeapAllocationLifetime.countWithTrace_erasure,
    BinaryPRGWordStoreHeapMachine.countWithWork_erasure]

theorem treeWithTrace_length (nodes tape : List Bool) (S : ℕ)
    (hS : 8 ≤ S) (hNodes : nodes.length ≤ S) (hTape : tape.length+2 ≤ S) :
    (treeWithTrace nodes tape).1.length ≤ 5*S+15 := by
  rw [treeWithTrace_erases,← treeWithWork_erases]
  exact treeWithWork_length nodes tape S hS hNodes hTape

theorem treeWithTrace_usage (nodes tape : List Bool) (S : ℕ)
    (hS : 8 ≤ S) (hNodes : nodes.length ≤ S) (hTape : tape.length+2 ≤ S) :
    usage (treeWithTrace nodes tape).2 ≤ 100000*(S+1)^2 := by
  let counted := BinaryPRGHeapAllocationLifetime.countWithTrace tape [true]
  let square := multiplyWithTrace counted.1 counted.1
  let scaled := multiplyWithTrace hundred square.1
  let allocation := addWithTrace scaled.1 eight
  let product := multiplyWithTrace nodes allocation.1
  have hHundred : hundred.length = 7 := rfl
  have hEight : eight.length = 4 := rfl
  have hc : counted.1.length ≤ S := by
    change (BinaryPRGHeapAllocationLifetime.countWithTrace tape [true]).1.length ≤ S
    rw [BinaryPRGHeapAllocationLifetime.countWithTrace_erasure]
    exact (count_word_length tape).trans hTape
  have hSquare : square.1.length ≤ 3*S := by
    change (multiplyWithTrace counted.1 counted.1).1.length ≤ _
    rw [multiplyWithTrace_erases]
    have h := BinaryMultiplication.multiply_length counted.1 counted.1
    omega
  have hScaled : scaled.1.length ≤ 3*S+14 := by
    change (multiplyWithTrace hundred square.1).1.length ≤ _
    rw [multiplyWithTrace_erases]
    have h := BinaryMultiplication.multiply_length hundred square.1
    rw [hHundred] at h
    omega
  have hAllocation : allocation.1.length ≤ 3*S+15 := by
    change (addWithTrace scaled.1 eight).1.length ≤ _
    rw [addWithTrace_erases]
    have h := BinaryAddition.add_length scaled.1 eight
    rw [hEight] at h
    omega
  have hCount := BinaryPRGHeapRulerLifetime.count_usage tape [true]
  change usage counted.2 ≤ _ at hCount
  have hCountTop : usage counted.2 ≤ 396*S^2 := by
    unfold BinaryPRGWordStoreHeapMachine.countBound at hCount
    simp only [List.length_singleton] at hCount
    have hm := Nat.mul_le_mul (show tape.length+1 ≤ S by omega) hTape
    nlinarith
  have hSquareUse := multiplyWithTrace_uniform_usage counted.1 counted.1 (3*S+15)
    (by omega) (by omega)
  have hScaledUse := multiplyWithTrace_uniform_usage hundred square.1 (3*S+15)
    (by norm_num only [hundred,List.length_cons,List.length_nil]; omega) (by omega)
  have hProductUse := multiplyWithTrace_uniform_usage nodes allocation.1 (3*S+15)
    (by omega) hAllocation
  have hAllocationUse := addWithTrace_usage scaled.1 eight
  have hAllocationTop : usage allocation.2 ≤ 45*S+225 := by
    change usage (addWithTrace scaled.1 eight).2 ≤ _
    rw [hEight] at hAllocationUse
    omega
  change usage square.2 ≤ _ at hSquareUse
  change usage scaled.2 ≤ _ at hScaledUse
  change usage product.2 ≤ _ at hProductUse
  have hw := wrapList_usage 11 64 4
    [counted.2,square.2,scaled.2,allocation.2,product.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrapList 11 64 4
    [counted.2,square.2,scaled.2,allocation.2,product.2]) ≤ _
  nlinarith only [hw,hCountTop,hSquareUse,hScaledUse,hProductUse,hAllocationTop,hS]

def calculateWithTrace (ruler first second : List Bool) : List Bool × Trace :=
  let nodes := nodesWordWithTrace ruler
  let a := treeWithTrace nodes.1 first
  let b := treeWithTrace nodes.1 second
  let combined := addWithTrace a.1 b.1
  (combined.1,wrap 64 4 [nodes.2,a.2,b.2,combined.2])

theorem calculateWithTrace_erases (ruler first second : List Bool) :
    (calculateWithTrace ruler first second).1 = calculate ruler first second := by
  simp only [calculateWithTrace,calculate,addWithTrace_erases,treeWithTrace_erases,
    nodesWordWithTrace_erases]

theorem calculateWithTrace_usage (ruler first second : List Bool) :
    usage (calculateWithTrace ruler first second).2 ≤
      300000*(ruler.length+first.length+second.length+9)^2 := by
  let S := ruler.length+first.length+second.length+8
  let nodes := nodesWordWithTrace ruler
  let a := treeWithTrace nodes.1 first
  let b := treeWithTrace nodes.1 second
  let combined := addWithTrace a.1 b.1
  have hS : 8 ≤ S := by dsimp only [S]; omega
  have hNodes : nodes.1.length ≤ S := by
    change (nodesWordWithTrace ruler).1.length ≤ S
    rw [nodesWordWithTrace_erases,nodesWord_length]
    dsimp only [S]
    omega
  have ha := treeWithTrace_usage nodes.1 first S hS hNodes
    (by dsimp only [S]; omega)
  have hb := treeWithTrace_usage nodes.1 second S hS hNodes
    (by dsimp only [S]; omega)
  have hal := treeWithTrace_length nodes.1 first S hS hNodes
    (by dsimp only [S]; omega)
  have hbl := treeWithTrace_length nodes.1 second S hS hNodes
    (by dsimp only [S]; omega)
  have hAdd := addWithTrace_usage a.1 b.1
  have hAddTop : usage combined.2 ≤ 75*S+240 := by
    change usage (addWithTrace a.1 b.1).2 ≤ _
    change a.1.length ≤ _ at hal
    change b.1.length ≤ _ at hbl
    omega
  have hNodeUse := nodesWordWithTrace_usage ruler
  change usage nodes.2 ≤ _ at hNodeUse
  change usage a.2 ≤ _ at ha
  change usage b.2 ≤ _ at hb
  have hw := wrap_usage 64 4 [nodes.2,a.2,b.2,combined.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 64 4 [nodes.2,a.2,b.2,combined.2]) ≤ 300000*(S+1)^2
  have hRuler : ruler.length+1 ≤ S := by dsimp only [S]; omega
  nlinarith only [hw,ha,hb,hAddTop,hNodeUse,hRuler,hS]

def rawArraysWithTraceAndAllowance (capacity resource : List SignedWord) :
    ((Σ ruler : List Bool,
      BinaryPhysicalHeapInputLifetime.RawArraysAt capacity resource ruler) × List Bool) × Trace :=
  let built := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource
  let calculated := calculateWithTrace built.1.1
    built.1.2.1.heap.tape built.1.2.2.heap.tape
  ((built.1,calculated.1),wrap 32 2 [built.2,calculated.2])

theorem rawArraysWithTraceAndAllowance_data (capacity resource : List SignedWord) :
    let built := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource
    (rawArraysWithTraceAndAllowance capacity resource).1 =
      (built.1,calculate built.1.1 built.1.2.1.heap.tape built.1.2.2.heap.tape) := by
  simp only [rawArraysWithTraceAndAllowance,calculateWithTrace_erases]

theorem rawArraysWithTraceAndAllowance_value (capacity resource : List SignedWord) :
    BinaryBigEndian.littleValue (rawArraysWithTraceAndAllowance capacity resource).1.2 =
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork capacity resource).2 := by
  have h := BinaryPhysicalBuildAllowance.rawArraysWithTraceAndAllowance_value capacity resource
  rw [BinaryPhysicalBuildAllowance.rawArraysWithTraceAndAllowance_data] at h
  simpa only [rawArraysWithTraceAndAllowance_data] using h

theorem rawArraysWithTraceAndAllowance_usage (capacity resource : List SignedWord) :
    let built := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource
    usage (rawArraysWithTraceAndAllowance capacity resource).2 ≤
      usage built.2+300000*(built.1.1.length+
        built.1.2.1.heap.tape.length+built.1.2.2.heap.tape.length+9)^2+38 := by
  let built := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource
  have hc := calculateWithTrace_usage built.1.1
    built.1.2.1.heap.tape built.1.2.2.heap.tape
  have hw := wrap_usage 32 2 [built.2,(calculateWithTrace built.1.1
    built.1.2.1.heap.tape built.1.2.2.heap.tape).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [built.2,(calculateWithTrace built.1.1
    built.1.2.1.heap.tape built.1.2.2.heap.tape).2]) ≤
      usage built.2+300000*(built.1.1.length+
        built.1.2.1.heap.tape.length+built.1.2.2.heap.tape.length+9)^2+38
  exact hw.trans (by omega)

theorem returned_size_bound {n : ℕ} (capacity resource : FixedArrayTable n SignedWord)
    (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    let built := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
      capacity.data.toList resource.data.toList
    built.1.1.length+built.1.2.1.heap.tape.length+built.1.2.2.heap.tape.length+9 ≤
      binaryWordWidth n+2*BinaryPRGHeapResourceInputBounds.initialHeapBound n W+9 := by
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
  change ruler.length+
    (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
      BinaryRationalOpcode.zero ruler capacity.data.toList).1.heap.tape.length+
    (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace
      BinaryRationalOpcode.zero ruler resource.data.toList).1.heap.tape.length+9 ≤
    binaryWordWidth n+2*K+9
  omega

def envelope (n W : ℕ) : ℕ :=
  let K := BinaryPRGHeapResourceInputBounds.initialHeapBound n W
  33*(BinaryPRGWordStoreHeapMachine.countBound n 0+
    2*(4*n+1)*(BinaryPRGWordStoreHeapMachine.allocationBound K+8))+
    6*n+168+300000*(binaryWordWidth n+2*K+9)^2

theorem rawArraysWithTraceAndAllowance_input_usage {n : ℕ}
    (capacity resource : FixedArrayTable n SignedWord) (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W)
    (hResource : ∀ j,width (resource.read j) ≤ W) :
    usage (rawArraysWithTraceAndAllowance capacity.data.toList resource.data.toList).2 ≤
      envelope n W := by
  let built := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
    capacity.data.toList resource.data.toList
  have hSize := returned_size_bound capacity resource W hW hCapacity hResource
  have hPow := Nat.mul_le_mul_left 300000 (Nat.pow_le_pow_left hSize 2)
  have hBuild := BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork_input_bound
    capacity resource W hW hCapacity hResource
  have hRaw := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace_usage
    capacity.data.toList resource.data.toList
  simp only [Array.length_toList,capacity.size] at hRaw
  have hTotal := rawArraysWithTraceAndAllowance_usage
    capacity.data.toList resource.data.toList
  dsimp only at hTotal hSize
  unfold envelope
  dsimp only
  omega

open BinaryPRGHeapResourcePolynomial in
theorem envelope_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => envelope p.count p.wordWidth) := by
  simp only [envelope,BinaryPRGHeapResourceInputBounds.initialHeapBound,
    BinaryPRGWordStoreHeap.heapBound,BinaryPRGWordStoreHeapMachine.countBound,
    BinaryPRGWordStoreHeapMachine.allocationBound]
  resource_polynomial

theorem uniform_input_usage : ∃ C d : ℕ,
    ∀ {n : ℕ} (capacity resource : FixedArrayTable n SignedWord) (W : ℕ),
      1 ≤ W → (∀ j,width (capacity.read j) ≤ W) →
      (∀ j,width (resource.read j) ≤ W) →
      usage (rawArraysWithTraceAndAllowance capacity.data.toList resource.data.toList).2 ≤
        C*(n+W+2)^d := by
  obtain ⟨C,d,hPoly⟩ := envelope_polynomial
  refine ⟨C,d,?_⟩
  intro n capacity resource W hW hCapacity hResource
  have h := hPoly (⟨n,W,0,0,0⟩ : BinaryPRGHeapResourcePolynomial.Parameters)
  have hSize : BinaryPRGHeapResourcePolynomial.inputSize
      (⟨n,W,0,0,0⟩ : BinaryPRGHeapResourcePolynomial.Parameters)+1 = n+W+2 := by
    simp [BinaryPRGHeapResourcePolynomial.inputSize,binaryWordWidth]
  rw [hSize] at h
  exact (rawArraysWithTraceAndAllowance_input_usage
    capacity resource W hW hCapacity hResource).trans h

theorem uniform_readback_usage : ∃ C d : ℕ,
    ∀ {n : ℕ} (request : Request n) (rich : Bool),
      let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        request).1.1.getD ([],[])
      usage (rawArraysWithTraceAndAllowance
        words.1 (if rich then words.1 else words.2)).2 ≤
        C*(n+BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request+2)^d := by
  obtain ⟨C,d,hBound⟩ := uniform_input_usage
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

theorem accepted_readback_usage_polynomial : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ rich : Bool,
      let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        parsed.1.2).1.1.getD ([],[])
      usage (rawArraysWithTraceAndAllowance
        words.1 (if rich then words.1 else words.2)).2 ≤ C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ := uniform_readback_usage
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

theorem accepted_readback_all_prefix_polynomial : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (rich : Bool) (borrowed steps : ℕ),
      let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        parsed.1.2).1.1.getD ([],[])
      let trace := (rawArraysWithTraceAndAllowance
        words.1 (if rich then words.1 else words.2)).2
      retainedHeap borrowed trace steps ≤ borrowed+C*(frame.length+3)^d ∧
        framePeak (trace.take steps) ≤ C*(frame.length+3)^d := by
  obtain ⟨C,d,hUsage⟩ := accepted_readback_usage_polynomial
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed rich borrowed steps
  exact all_prefix _ _ (hUsage frame parsed hParsed rich) borrowed steps

theorem rawArraysWithTraceAndAllowance_all_prefix (capacity resource : List SignedWord)
    (borrowed steps : ℕ) :
    let built := BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource
    let B := usage built.2+300000*(built.1.1.length+
      built.1.2.1.heap.tape.length+built.1.2.2.heap.tape.length+9)^2+38
    retainedHeap borrowed (rawArraysWithTraceAndAllowance capacity resource).2 steps ≤
        borrowed+B ∧
      framePeak ((rawArraysWithTraceAndAllowance capacity resource).2.take steps) ≤ B :=
  all_prefix _ _ (rawArraysWithTraceAndAllowance_usage capacity resource) borrowed steps

end Blotto.BinaryPhysicalBuildAllowanceLifetime
