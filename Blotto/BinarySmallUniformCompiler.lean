import Blotto.BinaryFourParameters
import Blotto.BinaryThreeSpecCompiler
import Blotto.BinaryReflectedFourSetup
import Blotto.RationalMergeFour

/-! The actual small-case uniform parent is computed from the six stored words:
three scale products, the merged three-variable descriptor, and Boolean
proportional splitting of its first coordinate. No supplied parent factory or
runtime rational source/encoder is used. Full execution prices remain separate. -/

namespace Blotto.BinarySmallUniformCompiler
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler BinaryStoredOverlapEnvironment
open BinaryReflectedFourSetup

structure Input where
  B : SignedWord
  l0 : SignedWord
  l1 : SignedWord
  l2 : SignedWord
  l3 : SignedWord

def Input.Canonical (input : Input) : Prop:=CanonicalWord input.B ∧ CanonicalWord input.l0 ∧
  CanonicalWord input.l1 ∧ CanonicalWord input.l2 ∧ CanonicalWord input.l3

def Input.Refines (input : Input) (source : RationalMergeFourInput) : Prop:=value input.B=source.B ∧
  value input.l0=source.l0 ∧ value input.l1=source.l1 ∧ value input.l2=source.l2 ∧ value input.l3=source.l3

def prepare (input : BinaryFourParameters.Input) : Input:=
  let parameters:=BinaryFourParameters.prepare input
  ⟨input.B,BinaryRationalOpcode.apply .mul (parameters.read 5) input.u,
    BinaryRationalOpcode.apply .mul (parameters.read 5) input.v,
    BinaryRationalOpcode.apply .mul (parameters.read 5) input.w,input.ell⟩

theorem prepare_canonical (input : BinaryFourParameters.Input) (h : input.Canonical) : (prepare input).Canonical:=
  ⟨h.1,opcode_canonical .mul _ _ (BinaryFourParameters.prepare_canonical input h 5) h.2.1,
    opcode_canonical .mul _ _ (BinaryFourParameters.prepare_canonical input h 5) h.2.2.1,
    opcode_canonical .mul _ _ (BinaryFourParameters.prepare_canonical input h 5) h.2.2.2.1,h.2.2.2.2.1⟩

theorem prepare_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (h : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) :
    (prepare input).Refines (source.smallUniformInput hCase):=by
  rw [source.smallUniformInput_refines]
  have hs:=BinaryFourParameters.prepare_value input source h hr 5
  change value ((BinaryFourParameters.prepare input).read 5)=source.scaleFraction at hs
  refine ⟨hr.1,?_,?_,?_,hr.2.2.2.2.1⟩
  · rw [prepare,BinaryRationalOpcode.apply_value .mul _ _ (BinaryFourParameters.prepare_canonical input h 5).1 h.2.1.1,hs,hr.2.1]
    rfl
  · rw [prepare,BinaryRationalOpcode.apply_value .mul _ _ (BinaryFourParameters.prepare_canonical input h 5).1 h.2.2.1.1,hs,hr.2.2.1]
    rfl
  · rw [prepare,BinaryRationalOpcode.apply_value .mul _ _ (BinaryFourParameters.prepare_canonical input h 5).1 h.2.2.2.1.1,hs,hr.2.2.2.1]
    rfl

def child (input : Input) : BinaryThreeInputCompiler.Input:=
  ⟨input.B,BinaryRationalOpcode.apply .add input.l0 input.l1,input.l2,input.l3,Constant.one.word⟩

theorem child_canonical (input : Input) (h : input.Canonical) : (child input).Canonical:=
  ⟨h.1,opcode_canonical .add _ _ h.2.1 h.2.2.1,h.2.2.2.1,h.2.2.2.2,Constant.word_canonical .one⟩

theorem child_refines (input : Input) (source : RationalMergeFourInput) (h : input.Canonical) (hr : input.Refines source) :
    BinaryThreeSpecCompiler.Refines (child input) source.childSpec:=by
  refine ⟨hr.1,?_,hr.2.2.2.1,hr.2.2.2.2,Constant.word_value .one⟩
  rw [child,BinaryRationalOpcode.apply_value .add _ _ h.2.1.1 h.2.2.1.1,hr.2.1,hr.2.2.1]
  rfl

def split (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) : FixedArrayTable 4 SignedWord:=
  let total:=BinaryRationalOpcode.apply .add first second
  FixedArrayTable.ofFn ![BinaryRationalOpcode.apply .mul (BinaryRationalOpcode.apply .div first total) (row.read 0),
    BinaryRationalOpcode.apply .mul (BinaryRationalOpcode.apply .div second total) (row.read 0),row.read 1,row.read 2]

theorem split_canonical (first second : SignedWord) (row : FixedArrayTable 3 SignedWord)
    (hFirst : CanonicalWord first) (hSecond : CanonicalWord second) (hRow : ∀ j,CanonicalWord (row.read j)) :
    ∀ j,CanonicalWord ((split first second row).read j):=by
  have ht:=opcode_canonical .add _ _ hFirst hSecond
  intro j
  rw [split,FixedArrayTable.read_ofFn]
  fin_cases j
  · exact opcode_canonical .mul _ _ (opcode_canonical .div _ _ hFirst ht) (hRow 0)
  · exact opcode_canonical .mul _ _ (opcode_canonical .div _ _ hSecond ht) (hRow 0)
  · exact hRow 1
  · exact hRow 2

theorem split_value (first second : SignedWord) (row : FixedArrayTable 3 SignedWord)
    (hFirst : CanonicalWord first) (hSecond : CanonicalWord second) (hRow : ∀ j,CanonicalWord (row.read j)) (j : Fin 4) :
    value ((split first second row).read j)=
      (RationalAffineAllocation.splitFirstTwo (value first) (value second)).value (fun r=>value (row.read r)) j:=by
  have ht:=opcode_canonical .add _ _ hFirst hSecond
  have hf:=opcode_canonical .div first _ hFirst ht
  have hs:=opcode_canonical .div second _ hSecond ht
  rw [split,FixedArrayTable.read_ofFn]
  fin_cases j
  · change value (BinaryRationalOpcode.apply .mul (BinaryRationalOpcode.apply .div first (BinaryRationalOpcode.apply .add first second)) (row.read 0))=
        (RationalAffineAllocation.splitFirstTwo (value first) (value second)).value (fun r=>value (row.read r)) 0
    rw [BinaryRationalOpcode.apply_value .mul _ _ hf.1 (hRow 0).1,
      BinaryRationalOpcode.apply_value .div _ _ hFirst.1 ht.1,
      BinaryRationalOpcode.apply_value .add _ _ hFirst.1 hSecond.1]
    simp [RealArithmeticOp.applyRat,RationalAffineAllocation.value,RationalAffineAllocation.splitFirstTwo,Fin.sum_univ_succ]
  · change value (BinaryRationalOpcode.apply .mul (BinaryRationalOpcode.apply .div second (BinaryRationalOpcode.apply .add first second)) (row.read 0))=
        (RationalAffineAllocation.splitFirstTwo (value first) (value second)).value (fun r=>value (row.read r)) 1
    rw [BinaryRationalOpcode.apply_value .mul _ _ hs.1 (hRow 0).1,
      BinaryRationalOpcode.apply_value .div _ _ hSecond.1 ht.1,
      BinaryRationalOpcode.apply_value .add _ _ hFirst.1 hSecond.1]
    simp [RealArithmeticOp.applyRat,RationalAffineAllocation.value,RationalAffineAllocation.splitFirstTwo,Fin.sum_univ_succ]
  · simp [RationalAffineAllocation.value,RationalAffineAllocation.splitFirstTwo,Fin.sum_univ_succ]
  · simp [RationalAffineAllocation.value,RationalAffineAllocation.splitFirstTwo,Fin.sum_univ_succ]

def descriptor (input : Input) : Segment 4 9:=
  let childTable:=BinaryThreeSpecCompiler.descriptor (child input)
  ⟨childTable.weight,FixedArrayTable.ofFn (fun i=>split input.l0 input.l1 (childTable.P.read i)),
    FixedArrayTable.ofFn (fun i=>split input.l0 input.l1 (childTable.Q.read i))⟩

theorem descriptor_canonical (input : Input) (h : input.Canonical) : (descriptor input).Canonical:=by
  have hc:=BinaryThreeSpecCompiler.descriptor_canonical (child input) (child_canonical input h)
  refine ⟨hc.1,?_,?_⟩
  · intro i j
    rw [descriptor,FixedArrayTable.read_ofFn]
    exact split_canonical _ _ _ h.2.1 h.2.2.1 (hc.2.1 i) j
  · intro i j
    rw [descriptor,FixedArrayTable.read_ofFn]
    exact split_canonical _ _ _ h.2.1 h.2.2.1 (hc.2.2 i) j

theorem descriptor_refines (input : Input) (source : RationalMergeFourInput) (h : input.Canonical) (hr : input.Refines source) :
    (descriptor input).Refines source.segmentLottery:=by
  have hc:=BinaryThreeSpecCompiler.descriptor_canonical (child input) (child_canonical input h)
  have he:=BinaryThreeSpecCompiler.descriptor_refines (child input) source.childSpec (child_canonical input h) (child_refines input source h hr)
  refine ⟨he.1,?_,?_⟩
  · intro i j
    rw [descriptor,FixedArrayTable.read_ofFn,split_value _ _ _ h.2.1 h.2.2.1 (hc.2.1 i),hr.2.1,hr.2.2.1]
    rw [show (fun r=>value (((BinaryThreeSpecCompiler.descriptor (child input)).P.read i).read r))=source.childSpec.segmentLottery.P i from funext (he.2.1 i)]
    rfl
  · intro i j
    rw [descriptor,FixedArrayTable.read_ofFn,split_value _ _ _ h.2.1 h.2.2.1 (hc.2.2 i),hr.2.1,hr.2.2.1]
    rw [show (fun r=>value (((BinaryThreeSpecCompiler.descriptor (child input)).Q.read i).read r))=source.childSpec.segmentLottery.Q i from funext (he.2.2 i)]
    rfl

def fromOriginal (input : BinaryFourParameters.Input) : Segment 4 9:=descriptor (prepare input)

theorem fromOriginal_canonical (input : BinaryFourParameters.Input) (h : input.Canonical) : (fromOriginal input).Canonical:=
  descriptor_canonical _ (prepare_canonical input h)

theorem fromOriginal_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (h : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) :
    (fromOriginal input).Refines (source.smallUniformLottery hCase):=
  descriptor_refines _ _ (prepare_canonical input h) (prepare_refines input source h hr hCase)

end Blotto.BinarySmallUniformCompiler
