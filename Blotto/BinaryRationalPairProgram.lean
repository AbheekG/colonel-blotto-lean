import Blotto.BinaryRegisterHeightBridge
import Blotto.RationalPairProgramBitCost

/-! The actual seven-instruction PRG pair preparation runs on canonical Boolean
source words. Its lower/upper/probability outputs refine the retained rational
pair exactly. Lattice/height certificates of that pair derive all register word
and cubic work bounds; no separate final-word oracle is supplied. Parsing and
canonical source preparation remain explicit setup components. -/

namespace Blotto.BinaryRationalPairProgram
open BinaryRationalNormalization BinaryRationalOpcode BinaryRationalEncoding

structure Source where
  lengthI : SignedWord
  lengthJ : SignedWord
  resourceI : SignedWord
  resourceJ : SignedWord
  lengthI_canonical : CanonicalWord lengthI
  lengthJ_canonical : CanonicalWord lengthJ
  resourceI_canonical : CanonicalWord resourceI
  resourceJ_canonical : CanonicalWord resourceJ
  interiorI : 0 < value resourceI ∧ value resourceI < value lengthI
  interiorJ : 0 < value resourceJ ∧ value resourceJ < value lengthJ

namespace Source

noncomputable def pair (source : Source) : RationalRoundingPair where
  lengthI := value source.lengthI
  lengthJ := value source.lengthJ
  resourceI := value source.resourceI
  resourceJ := value source.resourceJ
  interiorI := source.interiorI
  interiorJ := source.interiorJ

def inputs (source : Source) : Array SignedWord :=
  #[source.lengthI, source.lengthJ, source.resourceI, source.resourceJ, zero]

theorem inputs_canonical (source : Source) : BinaryRegisterHeightBridge.CanonicalRegisters source.inputs := by
  intro index
  by_cases hi : index < 5
  · interval_cases index <;> simp only [inputs, BinaryRationalRegisterProgram.read, Array.getD]
    · exact source.lengthI_canonical
    · exact source.lengthJ_canonical
    · exact source.resourceI_canonical
    · exact source.resourceJ_canonical
    · exact zero_canonical
  · have hRead : BinaryRationalRegisterProgram.read source.inputs index = zero := by
      simp [inputs, BinaryRationalRegisterProgram.read, Array.getD, show ¬index < 5 from hi]
    rw [hRead]
    exact zero_canonical

theorem inputs_valid (source : Source) : BinaryRationalRegisterProgram.ValidRegisters source.inputs :=
  BinaryRegisterHeightBridge.canonicalRegisters_valid _ source.inputs_canonical

theorem inputs_interpreted (source : Source) :
    BinaryRationalRegisterProgram.interpreted source.inputs = RationalPairProgram.inputs source.pair := by
  simp [BinaryRationalRegisterProgram.interpreted, inputs, RationalPairProgram.inputs, pair, zero_value]

def run (source : Source) : Array SignedWord := BinaryRationalRegisterProgram.run RealPairProgram.code source.inputs

def runWithWork (source : Source) : Array SignedWord × ℕ := BinaryRationalRegisterProgram.runWithWork RealPairProgram.code source.inputs

theorem run_interpreted (source : Source) : BinaryRationalRegisterProgram.interpreted source.run = RationalPairProgram.run source.pair := by
  rw [run, BinaryRationalRegisterProgram.run_interpreted _ _ source.inputs_valid, source.inputs_interpreted]
  rfl

theorem run_lower (source : Source) : value (BinaryRationalRegisterProgram.read source.run 7) = source.pair.lower := by
  rw [← BinaryRationalRegisterProgram.interpreted_read, source.run_interpreted]
  exact RationalPairProgram.run_lower source.pair

theorem run_upper (source : Source) : value (BinaryRationalRegisterProgram.read source.run 8) = source.pair.upper := by
  rw [← BinaryRationalRegisterProgram.interpreted_read, source.run_interpreted]
  exact RationalPairProgram.run_upper source.pair

theorem run_probability (source : Source) : value (BinaryRationalRegisterProgram.read source.run 11) = source.pair.probability := by
  rw [← BinaryRationalRegisterProgram.interpreted_read, source.run_interpreted]
  exact RationalPairProgram.run_probability source.pair

theorem run_probability_denominator_positive (source : Source) :
    0 < value (BinaryRationalRegisterProgram.read source.run 10) := by
  rw [← BinaryRationalRegisterProgram.interpreted_read, source.run_interpreted]
  exact RationalPairProgram.denominator_positive source.pair

theorem run_canonical (source : Source) : BinaryRegisterHeightBridge.CanonicalRegisters source.run :=
  BinaryRegisterHeightBridge.run_canonical _ _ source.inputs_canonical

theorem run_size (source : Source) : source.run.size = 12 := by
  rw [run, BinaryRationalRegisterProgram.run_size]
  rfl

theorem trace_wordBounds (source : Source) {s : ℕ} (h : source.pair.FieldsHeight s) (hs : 2 ≤ s) :
    BinaryRationalRegisterProgram.TraceWordBounds RealPairProgram.code source.inputs (32 * s + 31) := by
  apply BinaryRegisterHeightBridge.final_semantic_trace _ _ source.inputs_canonical
  rw [source.inputs_interpreted]
  exact RationalPairProgram.final_wordBounds h hs

theorem run_wordBounds (source : Source) {s : ℕ} (h : source.pair.FieldsHeight s) (hs : 2 ≤ s) :
    BinaryRationalRegisterProgram.WordBounds source.run (32 * s + 31) :=
  BinaryRationalRegisterProgram.trace_bounds_final _ _ _ (source.trace_wordBounds h hs)

theorem run_lower_zero_boundary (source : Source) (h : source.pair.total ≤ source.pair.lengthJ) :
    value (BinaryRationalRegisterProgram.read source.run 7) = 0 := by
  rw [source.run_lower]
  unfold RationalRoundingPair.lower
  exact max_eq_left (sub_nonpos.mpr h)

theorem pair_never_zero_divisor (source : Source) :
    BinaryEuclideanGCD.nonzero (BinaryRationalRegisterProgram.read source.run 10).numerator = true := by
  have hWord : ∀ word : SignedWord, 0 < value word → BinaryEuclideanGCD.nonzero word.numerator = true := by
    intro word hPositive
    apply (BinaryEuclideanGCD.nonzero_true_iff _).mpr
    by_contra hn
    have hz : BinaryBigEndian.littleValue word.numerator = 0 := by omega
    unfold value at hPositive
    rw [hz] at hPositive
    cases word.negative <;> simp at hPositive
  exact hWord _ source.run_probability_denominator_positive

theorem work_bound (source : Source) {s : ℕ} (h : source.pair.FieldsHeight s) (hs : 2 ≤ s) :
    source.runWithWork.2 ≤ 7 * (12000 * (32 * s + 32) ^ 3 + 28 * (64 * s + 63) + 4) := by
  have hWork := BinaryRationalRegisterProgram.work_bound_of_trace RealPairProgram.code source.inputs (32 * s + 31)
    (source.trace_wordBounds h hs)
  rw [runWithWork, BinaryRationalRegisterProgram.runWithWork_refines]
  change BinaryRationalRegisterProgram.work RealPairProgram.code source.inputs ≤ _
  have hWidth : 32 * s + 31 + 1 = 32 * s + 32 := by omega
  have hPayload : 1 + 2 * (32 * s + 31) = 64 * s + 63 := by omega
  rw [hWidth, hPayload] at hWork
  exact hWork

theorem lattice_work_bound (source : Source) {D : ℕ} (hD : 0 < D) (h : source.pair.Lattice D)
    (hi : source.pair.lengthI ≤ 1) (hj : source.pair.lengthJ ≤ 1) :
    source.runWithWork.2 ≤ 7 * (12000 * (32 * binaryWordWidth D + 96) ^ 3 +
      28 * (64 * binaryWordWidth D + 191) + 4) := by
  have hWork := source.work_bound (RationalPairProgram.fieldsHeight_lattice source.pair hD h hi hj) (by omega)
  have hWidth : 32 * (2 + binaryWordWidth D) + 32 = 32 * binaryWordWidth D + 96 := by omega
  have hPayload : 64 * (2 + binaryWordWidth D) + 63 = 64 * binaryWordWidth D + 191 := by omega
  rw [hWidth, hPayload] at hWork
  exact hWork

def sourcePayloadWork (source : Source) : ℕ :=
  2 * (BinaryRationalRegisterProgram.payloadWords source.lengthI + BinaryRationalRegisterProgram.payloadWords source.lengthJ +
    BinaryRationalRegisterProgram.payloadWords source.resourceI + BinaryRationalRegisterProgram.payloadWords source.resourceJ + 2)

def preparationWork (source : Source) : ℕ := source.sourcePayloadWork + source.runWithWork.2

theorem sourcePayloadWork_bound (source : Source) {s : ℕ} (h : source.pair.FieldsHeight s) :
    source.sourcePayloadWork ≤ 8 * (3 + 4 * s) + 4 := by
  have hLI := source.lengthI_canonical.2.trans (rationalWordWidth_of_height h.1)
  have hLJ := source.lengthJ_canonical.2.trans (rationalWordWidth_of_height h.2.1)
  have hRI := source.resourceI_canonical.2.trans (rationalWordWidth_of_height h.2.2.1)
  have hRJ := source.resourceJ_canonical.2.trans (rationalWordWidth_of_height h.2.2.2)
  unfold sourcePayloadWork
  have pLI := BinaryRationalRegisterProgram.payloadWords_bound source.lengthI (1 + 2 * s) hLI
  have pLJ := BinaryRationalRegisterProgram.payloadWords_bound source.lengthJ (1 + 2 * s) hLJ
  have pRI := BinaryRationalRegisterProgram.payloadWords_bound source.resourceI (1 + 2 * s) hRI
  have pRJ := BinaryRationalRegisterProgram.payloadWords_bound source.resourceJ (1 + 2 * s) hRJ
  nlinarith

theorem preparationWork_bound (source : Source) {s : ℕ} (h : source.pair.FieldsHeight s) (hs : 2 ≤ s) :
    source.preparationWork ≤ 8 * (3 + 4 * s) + 4 +
      7 * (12000 * (32 * s + 32) ^ 3 + 28 * (64 * s + 63) + 4) :=
  Nat.add_le_add (source.sourcePayloadWork_bound h) (source.work_bound h hs)

end Source

def fromWords (lengthI lengthJ resourceI resourceJ : SignedWord)
    (hLI : Valid lengthI) (hLJ : Valid lengthJ) (hRI : Valid resourceI) (hRJ : Valid resourceJ)
    (hI : 0 < value resourceI ∧ value resourceI < value lengthI)
    (hJ : 0 < value resourceJ ∧ value resourceJ < value lengthJ) : Source where
  lengthI := canonicalize lengthI
  lengthJ := canonicalize lengthJ
  resourceI := canonicalize resourceI
  resourceJ := canonicalize resourceJ
  lengthI_canonical := ⟨canonicalize_valid _ hLI, by rw [canonicalize_value _ hLI]; exact canonicalize_width _ hLI⟩
  lengthJ_canonical := ⟨canonicalize_valid _ hLJ, by rw [canonicalize_value _ hLJ]; exact canonicalize_width _ hLJ⟩
  resourceI_canonical := ⟨canonicalize_valid _ hRI, by rw [canonicalize_value _ hRI]; exact canonicalize_width _ hRI⟩
  resourceJ_canonical := ⟨canonicalize_valid _ hRJ, by rw [canonicalize_value _ hRJ]; exact canonicalize_width _ hRJ⟩
  interiorI := by simpa only [canonicalize_value _ hRI, canonicalize_value _ hLI] using hI
  interiorJ := by simpa only [canonicalize_value _ hRJ, canonicalize_value _ hLJ] using hJ

def fromPositiveRatios (numerators denominators : Fin 4 → PositiveBinaryWord)
    (hI : 0 < (numerators 2).value / ((denominators 2).value : ℚ) ∧
      (numerators 2).value / ((denominators 2).value : ℚ) < (numerators 0).value / ((denominators 0).value : ℚ))
    (hJ : 0 < (numerators 3).value / ((denominators 3).value : ℚ) ∧
      (numerators 3).value / ((denominators 3).value : ℚ) < (numerators 1).value / ((denominators 1).value : ℚ)) : Source where
  lengthI := fromPositiveWords false (numerators 0) (denominators 0)
  lengthJ := fromPositiveWords false (numerators 1) (denominators 1)
  resourceI := fromPositiveWords false (numerators 2) (denominators 2)
  resourceJ := fromPositiveWords false (numerators 3) (denominators 3)
  lengthI_canonical := fromPositiveWords_canonical _ _ _
  lengthJ_canonical := fromPositiveWords_canonical _ _ _
  resourceI_canonical := fromPositiveWords_canonical _ _ _
  resourceJ_canonical := fromPositiveWords_canonical _ _ _
  interiorI := by simpa only [fromPositiveWords_value, BinaryRatFrame.signedValue, Bool.false_eq_true, ite_false] using hI
  interiorJ := by simpa only [fromPositiveWords_value, BinaryRatFrame.signedValue, Bool.false_eq_true, ite_false] using hJ

def readFields (frame : List Bool) : Option (SignedWord × SignedWord × SignedWord × SignedWord × List Bool) :=
  (readFrame frame).bind (fun lengthI => (readFrame lengthI.2).bind (fun lengthJ =>
    (readFrame lengthJ.2).bind (fun resourceI => (readFrame resourceI.2).map (fun resourceJ =>
      (lengthI.1, lengthJ.1, resourceI.1, resourceJ.1, resourceJ.2)))))

def less (first second : SignedWord) : Bool := !BinaryRationalArithmetic.lessEqual second first

theorem less_iff (first second : SignedWord) (hA : Valid first) (hB : Valid second) :
    less first second = true ↔ value first < value second := by
  have h := BinaryRationalArithmetic.lessEqual_iff second first hB hA
  unfold less
  cases he : BinaryRationalArithmetic.lessEqual second first
  · have hn : ¬value second ≤ value first := fun hn => by have hf := h.mpr hn; rw [he] at hf; cases hf
    simp only [Bool.not_false, true_iff]
    exact lt_of_not_ge hn
  · have hn := h.mp he
    simp only [Bool.not_true, Bool.false_eq_true, false_iff]
    exact not_lt_of_ge hn

def checkInterior (length resource : SignedWord) : Bool := less zero resource && less resource length

theorem checkInterior_iff (length resource : SignedWord) (hL : Valid length) (hR : Valid resource) :
    checkInterior length resource = true ↔ 0 < value resource ∧ value resource < value length := by
  rw [checkInterior, Bool.and_eq_true, less_iff zero resource zero_valid hR, zero_value,
    less_iff resource length hR hL]

def fromCanonicalChecked (lengthI lengthJ resourceI resourceJ : SignedWord)
    (hLI : CanonicalWord lengthI) (hLJ : CanonicalWord lengthJ)
    (hRI : CanonicalWord resourceI) (hRJ : CanonicalWord resourceJ) : Option Source :=
  if hI : checkInterior lengthI resourceI = true then
    if hJ : checkInterior lengthJ resourceJ = true then
      some ⟨lengthI, lengthJ, resourceI, resourceJ, hLI, hLJ, hRI, hRJ,
        (checkInterior_iff lengthI resourceI hLI.1 hRI.1).mp hI,
        (checkInterior_iff lengthJ resourceJ hLJ.1 hRJ.1).mp hJ⟩ else none else none

theorem fromCanonicalChecked_complete (lengthI lengthJ resourceI resourceJ : SignedWord)
    (hLI : CanonicalWord lengthI) (hLJ : CanonicalWord lengthJ)
    (hRI : CanonicalWord resourceI) (hRJ : CanonicalWord resourceJ)
    (hI : 0 < value resourceI ∧ value resourceI < value lengthI)
    (hJ : 0 < value resourceJ ∧ value resourceJ < value lengthJ) :
    ∃ source, fromCanonicalChecked lengthI lengthJ resourceI resourceJ hLI hLJ hRI hRJ = some source ∧
      source.lengthI = lengthI ∧ source.lengthJ = lengthJ ∧ source.resourceI = resourceI ∧ source.resourceJ = resourceJ := by
  unfold fromCanonicalChecked
  rw [dite_eq_left ((checkInterior_iff lengthI resourceI hLI.1 hRI.1).mpr hI),
    dite_eq_left ((checkInterior_iff lengthJ resourceJ hLJ.1 hRJ.1).mpr hJ)]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

def encodedFields (pair : RationalRoundingPair) : List Bool :=
  BinaryRatFrame.encode pair.lengthI ++ BinaryRatFrame.encode pair.lengthJ ++
    BinaryRatFrame.encode pair.resourceI ++ BinaryRatFrame.encode pair.resourceJ

theorem readFields_encode_append (pair : RationalRoundingPair) (suffix : List Bool) :
    ∃ lengthI lengthJ resourceI resourceJ,
      readFields (encodedFields pair ++ suffix) = some (lengthI, lengthJ, resourceI, resourceJ, suffix) ∧
      value lengthI = pair.lengthI ∧ value lengthJ = pair.lengthJ ∧
      value resourceI = pair.resourceI ∧ value resourceJ = pair.resourceJ ∧
      CanonicalWord lengthI ∧ CanonicalWord lengthJ ∧ CanonicalWord resourceI ∧ CanonicalWord resourceJ := by
  obtain ⟨resourceJ, hRJ, vRJ, cRJ⟩ := readFrame_encode_append pair.resourceJ suffix
  obtain ⟨resourceI, hRI, vRI, cRI⟩ := readFrame_encode_append pair.resourceI (BinaryRatFrame.encode pair.resourceJ ++ suffix)
  obtain ⟨lengthJ, hLJ, vLJ, cLJ⟩ := readFrame_encode_append pair.lengthJ
    (BinaryRatFrame.encode pair.resourceI ++ BinaryRatFrame.encode pair.resourceJ ++ suffix)
  obtain ⟨lengthI, hLI, vLI, cLI⟩ := readFrame_encode_append pair.lengthI
    (BinaryRatFrame.encode pair.lengthJ ++ BinaryRatFrame.encode pair.resourceI ++ BinaryRatFrame.encode pair.resourceJ ++ suffix)
  simp only [List.append_assoc] at hLI hLJ hRI
  refine ⟨lengthI, lengthJ, resourceI, resourceJ, ?_, vLI, vLJ, vRI, vRJ, cLI, cLJ, cRI, cRJ⟩
  simp only [readFields, encodedFields, List.append_assoc, hLI, Option.bind_some,
    hLJ, hRI, hRJ, Option.map_some]

theorem checked_encoded_pair (pair : RationalRoundingPair) (suffix : List Bool) :
    ∃ lengthI lengthJ resourceI resourceJ, ∃ hLI : CanonicalWord lengthI, ∃ hLJ : CanonicalWord lengthJ,
      ∃ hRI : CanonicalWord resourceI, ∃ hRJ : CanonicalWord resourceJ, ∃ source,
      readFields (encodedFields pair ++ suffix) = some (lengthI, lengthJ, resourceI, resourceJ, suffix) ∧
      fromCanonicalChecked lengthI lengthJ resourceI resourceJ hLI hLJ hRI hRJ = some source ∧
      source.pair = pair := by
  obtain ⟨lengthI, lengthJ, resourceI, resourceJ, hRead, vLI, vLJ, vRI, vRJ, cLI, cLJ, cRI, cRJ⟩ := readFields_encode_append pair suffix
  have hI : 0 < value resourceI ∧ value resourceI < value lengthI := by rw [vRI, vLI]; exact pair.interiorI
  have hJ : 0 < value resourceJ ∧ value resourceJ < value lengthJ := by rw [vRJ, vLJ]; exact pair.interiorJ
  obtain ⟨source, hCheck, hLI, hLJ, hRI, hRJ⟩ := fromCanonicalChecked_complete lengthI lengthJ resourceI resourceJ cLI cLJ cRI cRJ hI hJ
  refine ⟨lengthI, lengthJ, resourceI, resourceJ, cLI, cLJ, cRI, cRJ, source, hRead, hCheck, ?_⟩
  have hData : source.pair.lengthI = pair.lengthI ∧ source.pair.lengthJ = pair.lengthJ ∧
      source.pair.resourceI = pair.resourceI ∧ source.pair.resourceJ = pair.resourceJ := by
    simp [Source.pair, hLI, hLJ, hRI, hRJ, vLI, vLJ, vRI, vRJ]
  have hEq : ∀ a b : RationalRoundingPair,
      a.lengthI = b.lengthI → a.lengthJ = b.lengthJ → a.resourceI = b.resourceI → a.resourceJ = b.resourceJ → a = b := by
    intro a b h1 h2 h3 h4
    cases a
    cases b
    simp only at h1 h2 h3 h4
    cases h1
    cases h2
    cases h3
    cases h4
    rfl
  exact hEq source.pair pair hData.1 hData.2.1 hData.2.2.1 hData.2.2.2

end Blotto.BinaryRationalPairProgram
