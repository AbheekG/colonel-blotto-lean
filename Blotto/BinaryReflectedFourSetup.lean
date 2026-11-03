import Blotto.BinaryFourParentCompiler
import Blotto.RationalFourResources

/-! The small four-variable branch initializes actual Boolean nested resource
data from its six stored original words and computed eight-parameter table.
Capacities and initial resources use the verified Boolean opcodes. Refinement
to the retained reflected system is derived, not a supplied parent factory.
The resource/terminal sampling controller is implemented separately. -/

namespace Blotto.BinaryReflectedFourSetup
open BinaryRationalNormalization BinaryRationalEncoding

structure System where
  M : SignedWord
  long : FixedArrayTable 3 SignedWord
  short : FixedArrayTable 3 SignedWord
  initial : FixedArrayTable 3 SignedWord

def originalLengths (input : BinaryFourParameters.Input) : FixedArrayTable 3 SignedWord :=
  FixedArrayTable.ofFn ![input.u,input.v,input.w]

def fromParameters (input : BinaryFourParameters.Input) (p : FixedArrayTable 8 SignedWord) : System :=
  let lengths := originalLengths input
  { M := p.read 7
    long := lengths
    short := FixedArrayTable.ofFn (fun j => BinaryRationalOpcode.apply .mul (p.read 4) (lengths.read j))
    initial := FixedArrayTable.ofFn (fun j => BinaryRationalOpcode.apply .mul
      (BinaryRationalOpcode.apply .mul (p.read 6) (p.read 5)) (lengths.read j)) }

def prepare (input : BinaryFourParameters.Input) : System := fromParameters input (BinaryFourParameters.prepare input)

def System.capacity (system : System) : FixedArrayTable 3 SignedWord :=
  FixedArrayTable.ofFn (fun j => BinaryRationalOpcode.apply .sub (system.long.read j) (system.short.read j))

def System.Canonical (system : System) : Prop := CanonicalWord system.M ∧
  (∀ j, CanonicalWord (system.long.read j)) ∧ (∀ j, CanonicalWord (system.short.read j)) ∧
  (∀ j, CanonicalWord (system.initial.read j))

def System.Refines (system : System) (source : RationalNestedResourceSystem) : Prop :=
  value system.M = source.M ∧ (∀ j, value (system.long.read j) = source.long j) ∧
    (∀ j, value (system.short.read j) = source.short j) ∧ (∀ j, value (system.initial.read j) = source.initial j)

theorem opcode_canonical (op : RealArithmeticOp) (a b : SignedWord) (ha : CanonicalWord a) (hb : CanonicalWord b) :
    CanonicalWord (BinaryRationalOpcode.apply op a b) := by
  refine ⟨BinaryRationalOpcode.apply_valid op a b ha.1 hb.1,?_⟩
  have h := BinaryRationalOpcode.apply_width op a b ha.1 hb.1
  rw [← BinaryRationalOpcode.apply_value op a b ha.1 hb.1] at h
  exact h

theorem originalLengths_canonical (input : BinaryFourParameters.Input) (h : input.Canonical) :
    ∀ j, CanonicalWord ((originalLengths input).read j) := by
  intro j
  rw [originalLengths,FixedArrayTable.read_ofFn]
  fin_cases j
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1

theorem originalLengths_value (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (h : input.Refines source) : ∀ j, value ((originalLengths input).read j) = source.originalLengths j := by
  intro j
  unfold originalLengths RationalFourInput.originalLengths
  rw [FixedArrayTable.read_ofFn]
  fin_cases j
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1

theorem fromParameters_canonical (input : BinaryFourParameters.Input) (p : FixedArrayTable 8 SignedWord)
    (h : input.Canonical) (hp : ∀ j, CanonicalWord (p.read j)) : (fromParameters input p).Canonical := by
  have hl := originalLengths_canonical input h
  refine ⟨hp 7,hl,?_,?_⟩
  · intro j
    change CanonicalWord ((FixedArrayTable.ofFn _).read j)
    rw [FixedArrayTable.read_ofFn]
    exact opcode_canonical .mul _ _ (hp 4) (hl j)
  · intro j
    change CanonicalWord ((FixedArrayTable.ofFn _).read j)
    rw [FixedArrayTable.read_ofFn]
    exact opcode_canonical .mul _ _ (opcode_canonical .mul _ _ (hp 6) (hp 5)) (hl j)

theorem prepare_canonical (input : BinaryFourParameters.Input) (h : input.Canonical) : (prepare input).Canonical :=
  fromParameters_canonical input _ h (BinaryFourParameters.prepare_canonical input h)

theorem prepare_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hcase : source.w < (1-source.p)*source.ell) :
    (prepare input).Refines (source.reflectedResourceSystem hcase) := by
  rw [source.reflectedResourceSystem_refines]
  have hp := BinaryFourParameters.prepare_canonical input hC
  have hv := BinaryFourParameters.prepare_value input source hC hR
  have hl := originalLengths_canonical input hC
  have hlv := originalLengths_value input source hR
  refine ⟨hv 7,hlv,?_,?_⟩
  · intro j
    change value ((FixedArrayTable.ofFn _).read j) = _
    rw [FixedArrayTable.read_ofFn]
    rw [BinaryRationalOpcode.apply_value .mul _ _ (hp 4).1 (hl j).1,hv 4,hlv j]
    rfl
  · intro j
    have hInner := BinaryRationalOpcode.apply_valid .mul _ _ (hp 6).1 (hp 5).1
    change value ((FixedArrayTable.ofFn _).read j) = _
    rw [FixedArrayTable.read_ofFn]
    rw [BinaryRationalOpcode.apply_value .mul _ _ hInner (hl j).1,
      BinaryRationalOpcode.apply_value .mul _ _ (hp 6).1 (hp 5).1,hv 6,hv 5,hlv j]
    rfl

theorem capacity_canonical (system : System) (h : system.Canonical) :
    ∀ j, CanonicalWord (system.capacity.read j) := by
  intro j
  rw [System.capacity,FixedArrayTable.read_ofFn]
  exact opcode_canonical .sub _ _ (h.2.1 j) (h.2.2.1 j)

theorem capacity_value (system : System) (source : RationalNestedResourceSystem)
    (hC : system.Canonical) (hR : system.Refines source) :
    ∀ j, value (system.capacity.read j) = source.capacity j := by
  intro j
  rw [System.capacity,FixedArrayTable.read_ofFn,BinaryRationalOpcode.apply_value .sub _ _ (hC.2.1 j).1 (hC.2.2.1 j).1,
    hR.2.1 j,hR.2.2.1 j]
  rfl

def reflect (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) : FixedArrayTable 4 SignedWord :=
  FixedArrayTable.ofFn ![BinaryRationalOpcode.apply .sub input.u (row.read 0),
    BinaryRationalOpcode.apply .sub input.v (row.read 1),BinaryRationalOpcode.apply .sub input.w (row.read 2),
    BinaryRationalOpcode.zero]

theorem reflect_value (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (row : FixedArrayTable 3 SignedWord)
    (hRow : ∀ j, CanonicalWord (row.read j)) (j : Fin 4) :
    value ((reflect input row).read j) = (RationalAffineAllocation.reflectAppend source.originalLengths).value
      (fun r => value (row.read r)) j := by
  unfold reflect
  rw [FixedArrayTable.read_ofFn]
  fin_cases j
  · change value (BinaryRationalOpcode.apply .sub input.u (row.read 0)) = _
    rw [BinaryRationalOpcode.apply_value .sub _ _ hC.2.1.1 (hRow 0).1,hR.2.1]
    simp [RationalAffineAllocation.reflectAppend,RationalAffineAllocation.value,RationalFourInput.originalLengths,Fin.sum_univ_succ,RealArithmeticOp.applyRat]
    ring
  · change value (BinaryRationalOpcode.apply .sub input.v (row.read 1)) = _
    rw [BinaryRationalOpcode.apply_value .sub _ _ hC.2.2.1.1 (hRow 1).1,hR.2.2.1]
    simp [RationalAffineAllocation.reflectAppend,RationalAffineAllocation.value,RationalFourInput.originalLengths,Fin.sum_univ_succ,RealArithmeticOp.applyRat]
    ring
  · change value (BinaryRationalOpcode.apply .sub input.w (row.read 2)) = _
    rw [BinaryRationalOpcode.apply_value .sub _ _ hC.2.2.2.1.1 (hRow 2).1,hR.2.2.2.1]
    simp [RationalAffineAllocation.reflectAppend,RationalAffineAllocation.value,RationalFourInput.originalLengths,Fin.sum_univ_succ,RealArithmeticOp.applyRat]
    ring
  · change value BinaryRationalOpcode.zero = _
    rw [BinaryRationalOpcode.zero_value]
    simp [RationalAffineAllocation.reflectAppend,RationalAffineAllocation.value,Fin.sum_univ_succ]

end Blotto.BinaryReflectedFourSetup
