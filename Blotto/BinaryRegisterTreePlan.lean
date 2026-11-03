import Blotto.BinaryPairRegisterPlan

/-! Register storage produces its actual tree/word/remainder and final-depth
plan together. Each reached reversal/tree/wrapper case increments visits once;
that count is returned for concrete caller pricing. Old data and trace records
remain exact. Native scalar/record/reference/allocator interpretation is separate. -/
namespace Blotto.BinaryRegisterTreePlan
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryTracePlanMeasured BinaryTraceDepth
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerPairRegisters
set_option autoImplicit false
set_option maxHeartbeats 5000000

abbrev Result (α : Type*) := (α × Plan) × ℕ

def Refines {α : Type*} (produced : Result α) (old : α × Trace) (depth : ℕ) : Prop :=
  produced.1.1 = old.1 ∧ denote produced.1.2 = under depth old.2

def Safe {α : Type*} (produced : Result α) : Prop :=
  nodes produced.1.2 ≤ 2*payload produced.1.2 ∧ produced.2 ≤ payload produced.1.2

def reverseAt : List Bool → List Bool → ℕ → Result (List Bool)
  | [],acc,depth => ((acc,.block [.frames (depth+1)]),1)
  | bit::rest,acc,depth =>
      let later := reverseAt rest (bit::acc) (depth+1)
      ((later.1.1,.join (.block [.frames (depth+1),.listAllocation 1]) later.1.2),later.2+1)

theorem reverse_refines (bits acc : List Bool) (depth : ℕ) :
    Refines (reverseAt bits acc depth) (reverseWithTrace bits acc) depth := by
  induction bits generalizing acc depth with
  | nil => constructor <;> trivial
  | cons bit rest ih =>
      have h := ih (bit::acc) (depth+1)
      simp only [Refines,reverseAt,reverseWithTrace,denote,h.1,h.2,under_append,under_compose]
      constructor <;> trivial

theorem reverse_safe (bits acc : List Bool) (depth : ℕ) : Safe (reverseAt bits acc depth) := by
  induction bits generalizing acc depth with
  | nil => simp [reverseAt,Safe,nodes,payload]
  | cons bit rest ih =>
      have h := ih (bit::acc) (depth+1)
      simp only [reverseAt,Safe,nodes,payload,List.length_cons,List.length_nil] at h ⊢
      constructor <;> omega

def buildAt (fallback : SignedWord) : (ruler : List Bool) → List SignedWord → ℕ → Result (Tree ruler.length × List SignedWord)
  | [],[],depth => (((.leaf fallback,[]),.block [.frames (depth+1),.arrayAllocation 8]),1)
  | [],word::rest,depth => (((.leaf word,rest),.block [.frames (depth+1),.arrayAllocation 8]),1)
  | _::ruler,seed,depth =>
      let left := buildAt fallback ruler seed (depth+1)
      let right := buildAt fallback ruler left.1.1.2 (depth+1)
      (((.branch left.1.1.1 right.1.1.1,right.1.1.2),
        .join (.block [.frames (depth+1),.arrayAllocation 8]) (.join left.1.2 right.1.2)),left.2+right.2+1)

theorem build_refines (fallback : SignedWord) (ruler : List Bool) (seed : List SignedWord) (depth : ℕ) :
    Refines (buildAt fallback ruler seed depth) (BinaryQuadraticResourcePairLifetime.buildWithTrace fallback ruler seed) depth := by
  induction ruler generalizing seed depth with
  | nil => cases seed <;> constructor <;> trivial
  | cons cell ruler ih =>
      have hl := ih seed (depth+1)
      have hr := ih (BinaryQuadraticResourcePairLifetime.buildWithTrace fallback ruler seed).1.2 (depth+1)
      simp only [Refines,buildAt,BinaryQuadraticResourcePairLifetime.buildWithTrace,denote,
        hl.1,hl.2,hr.1,hr.2,under_append,under_compose,List.append_assoc]
      constructor <;> trivial

theorem build_safe (fallback : SignedWord) (ruler : List Bool) (seed : List SignedWord) (depth : ℕ) :
    Safe (buildAt fallback ruler seed depth) := by
  induction ruler generalizing seed depth with
  | nil => cases seed <;> simp [buildAt,Safe,nodes,payload]
  | cons cell ruler ih =>
      have hl := ih seed (depth+1)
      have hr := ih (buildAt fallback ruler seed (depth+1)).1.1.2 (depth+1)
      simp only [buildAt,Safe,nodes,payload,List.length_cons,List.length_nil] at hl hr ⊢
      constructor <;> omega

def scanAt : {height : ℕ} → Tree height → List Bool → ℕ → Result SignedWord
  | _,.leaf word,_,depth => ((word,.block [.frames (depth+1),.arrayAllocation 4]),1)
  | _,.branch left _right,[],depth =>
      let later := scanAt left [] (depth+1)
      ((later.1.1,.join (.block [.frames (depth+1),.arrayAllocation 4]) later.1.2),later.2+1)
  | _,.branch left right,bit::rest,depth =>
      let later := if bit then scanAt right rest (depth+1) else scanAt left rest (depth+1)
      ((later.1.1,.join (.block [.frames (depth+1),.arrayAllocation 4]) later.1.2),later.2+1)

theorem scan_refines {height : ℕ} (tree : Tree height) (address : List Bool) (depth : ℕ) :
    Refines (scanAt tree address depth) (BinaryQuadraticResourcePairLifetime.scanTreeWithTrace tree address) depth := by
  induction tree generalizing address depth with
  | leaf word => constructor <;> trivial
  | branch left right hl hr =>
      cases address with
      | nil =>
          have h := hl [] (depth+1)
          simp only [Refines,scanAt,BinaryQuadraticResourcePairLifetime.scanTreeWithTrace,denote,
            h.1,h.2,under_append,under_compose]
          constructor <;> trivial
      | cons bit rest =>
          cases bit <;> simp only [scanAt,BinaryQuadraticResourcePairLifetime.scanTreeWithTrace,Bool.false_eq_true,ite_false,ite_true]
          · have h := hl rest (depth+1)
            simp only [Refines,denote,h.1,h.2,under_append,under_compose]
            constructor <;> trivial
          · have h := hr rest (depth+1)
            simp only [Refines,denote,h.1,h.2,under_append,under_compose]
            constructor <;> trivial

theorem scan_safe {height : ℕ} (tree : Tree height) (address : List Bool) (depth : ℕ) : Safe (scanAt tree address depth) := by
  induction tree generalizing address depth with
  | leaf word => simp [scanAt,Safe,nodes,payload]
  | branch left right hl hr => cases address with
    | nil =>
        have h := hl [] (depth+1)
        simp only [scanAt,Safe,nodes,payload,List.length_cons,List.length_nil] at h ⊢
        constructor <;> omega
    | cons bit rest =>
        cases bit
        · have h := hl rest (depth+1)
          simp only [scanAt,Safe,nodes,payload,List.length_cons,List.length_nil,Bool.false_eq_true,ite_false] at h ⊢
          constructor <;> omega
        · have h := hr rest (depth+1)
          simp only [scanAt,Safe,nodes,payload,List.length_cons,List.length_nil,ite_true] at h ⊢
          constructor <;> omega

def lookupAt {height : ℕ} (tree : Tree height) (address : FixedBinaryWord height) (depth : ℕ) : Result SignedWord :=
  let reversed := reverseAt address.bits [] (depth+2)
  let reached := scanAt tree reversed.1.1 (depth+2)
  ((reached.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8]) (.join reversed.1.2 reached.1.2)),
    reversed.2+reached.2+1)

theorem lookup_refines {height : ℕ} (tree : Tree height) (address : FixedBinaryWord height) (depth : ℕ) :
    Refines (lookupAt tree address depth) (BinaryQuadraticResourcePairLifetime.lookupWithTrace tree address) depth := by
  have hr := reverse_refines address.bits [] (depth+2)
  have hs := scan_refines tree (reverseWithTrace address.bits []).1 (depth+2)
  simp only [Refines,lookupAt,BinaryQuadraticResourcePairLifetime.lookupWithTrace,denote,
    hr.1,hr.2,hs.1,hs.2,under_append,under_compose,List.append_assoc]
  constructor <;> trivial

theorem lookup_safe {height : ℕ} (tree : Tree height) (address : FixedBinaryWord height) (depth : ℕ) : Safe (lookupAt tree address depth) := by
  have hr := reverse_safe address.bits [] (depth+2)
  have hs := scan_safe tree (reverseAt address.bits [] (depth+2)).1.1 (depth+2)
  simp only [lookupAt,Safe,nodes,payload,List.length_cons,List.length_nil] at hr hs ⊢
  constructor <;> omega

def writeScanAt : {height : ℕ} → Tree height → List Bool → SignedWord → ℕ → Result (Tree height)
  | _,.leaf _,_,word,depth => ((.leaf word,.block [.frames (depth+1),.arrayAllocation 8]),1)
  | _,.branch left right,[],word,depth =>
      let later := writeScanAt left [] word (depth+1)
      ((.branch later.1.1 right,.join (.block [.frames (depth+1),.arrayAllocation 8]) later.1.2),later.2+1)
  | _,.branch left right,bit::rest,word,depth =>
      if bit then
        let later := writeScanAt right rest word (depth+1)
        ((.branch left later.1.1,.join (.block [.frames (depth+1),.arrayAllocation 8]) later.1.2),later.2+1)
      else
        let later := writeScanAt left rest word (depth+1)
        ((.branch later.1.1 right,.join (.block [.frames (depth+1),.arrayAllocation 8]) later.1.2),later.2+1)

theorem writeScan_refines {height : ℕ} (tree : Tree height) (address : List Bool) (word : SignedWord) (depth : ℕ) :
    Refines (writeScanAt tree address word depth) (BinaryQuadraticResourcePairLifetime.writeScanWithTrace tree address word) depth := by
  induction tree generalizing address depth with
  | leaf old => constructor <;> trivial
  | branch left right hl hr => cases address with
    | nil =>
        have h := hl [] (depth+1)
        simp only [Refines,writeScanAt,BinaryQuadraticResourcePairLifetime.writeScanWithTrace,denote,
          h.1,h.2,under_append,under_compose]
        constructor <;> trivial
    | cons bit rest =>
        cases bit
        · have h := hl rest (depth+1)
          simp only [Refines,writeScanAt,BinaryQuadraticResourcePairLifetime.writeScanWithTrace,denote,
            h.1,h.2,under_append,under_compose,Bool.false_eq_true,ite_false]
          constructor <;> trivial
        · have h := hr rest (depth+1)
          simp only [Refines,writeScanAt,BinaryQuadraticResourcePairLifetime.writeScanWithTrace,denote,
            h.1,h.2,under_append,under_compose,ite_true]
          constructor <;> trivial

theorem writeScan_safe {height : ℕ} (tree : Tree height) (address : List Bool) (word : SignedWord) (depth : ℕ) :
    Safe (writeScanAt tree address word depth) := by
  induction tree generalizing address depth with
  | leaf old => simp [writeScanAt,Safe,nodes,payload]
  | branch left right hl hr => cases address with
    | nil =>
        have h := hl [] (depth+1)
        simp only [writeScanAt,Safe,nodes,payload,List.length_cons,List.length_nil] at h ⊢
        constructor <;> omega
    | cons bit rest =>
        cases bit
        · have h := hl rest (depth+1)
          simp only [writeScanAt,Safe,nodes,payload,List.length_cons,List.length_nil,Bool.false_eq_true,ite_false] at h ⊢
          constructor <;> omega
        · have h := hr rest (depth+1)
          simp only [writeScanAt,Safe,nodes,payload,List.length_cons,List.length_nil,ite_true] at h ⊢
          constructor <;> omega

def writeAt {height : ℕ} (tree : Tree height) (address : FixedBinaryWord height) (word : SignedWord) (depth : ℕ) : Result (Tree height) :=
  let reversed := reverseAt address.bits [] (depth+2)
  let written := writeScanAt tree reversed.1.1 word (depth+2)
  ((written.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8]) (.join reversed.1.2 written.1.2)),
    reversed.2+written.2+1)

theorem write_refines {height : ℕ} (tree : Tree height) (address : FixedBinaryWord height) (word : SignedWord) (depth : ℕ) :
    Refines (writeAt tree address word depth) (BinaryQuadraticResourcePairLifetime.writeWithTrace tree address word) depth := by
  have hr := reverse_refines address.bits [] (depth+2)
  have hw := writeScan_refines tree (reverseWithTrace address.bits []).1 word (depth+2)
  simp only [Refines,writeAt,BinaryQuadraticResourcePairLifetime.writeWithTrace,denote,
    hr.1,hr.2,hw.1,hw.2,under_append,under_compose,List.append_assoc]
  constructor <;> trivial

theorem write_safe {height : ℕ} (tree : Tree height) (address : FixedBinaryWord height) (word : SignedWord) (depth : ℕ) : Safe (writeAt tree address word depth) := by
  have hr := reverse_safe address.bits [] (depth+2)
  have hw := writeScan_safe tree (reverseAt address.bits [] (depth+2)).1.1 word (depth+2)
  simp only [writeAt,Safe,nodes,payload,List.length_cons,List.length_nil] at hr hw ⊢
  constructor <;> omega

def initialAt (source : BinaryRationalPairProgram.Source) (depth : ℕ) : Result Registers :=
  let built := buildAt BinaryRationalOpcode.zero [false,false,false,false] (initialWords source) (depth+2)
  ((⟨built.1.1.1,a5⟩,.join (.block [.frames (depth+2),.listAllocation 13,.arrayAllocation 16]) built.1.2),built.2+1)

theorem initial_refines (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    Refines (initialAt source depth) (BinaryHeapPairRegistersMeasured.initial source).1 depth := by
  have h := build_refines BinaryRationalOpcode.zero [false,false,false,false] (initialWords source) (depth+2)
  simp only [Refines,initialAt,BinaryHeapPairRegistersMeasured.initial,BinaryQuadraticResourcePairLifetime.initialWithTrace,
    denote,h.1,h.2,under_append,under_compose]
  constructor <;> trivial

theorem initial_safe (source : BinaryRationalPairProgram.Source) (depth : ℕ) : Safe (initialAt source depth) := by
  have h := build_safe BinaryRationalOpcode.zero [false,false,false,false] (initialWords source) (depth+2)
  simp only [initialAt,Safe,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  constructor <;> omega

end Blotto.BinaryRegisterTreePlan
