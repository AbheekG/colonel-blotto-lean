import Blotto.GeneralPaperSourceInitializerReturnStorageReachedRates

/-! Literal outer endpoint caller. Guard rejection, failed basis and
successful continuation retain actual parent work/prefix/branch fields.
Reached input ownership, full returned basis and optional point coexist.
The previous scalar window supplies all primitive guard/fraction scratch;
whole endpoint work only sizes encoded metadata. -/
namespace Blotto.GeneralPaperOuterEndpointFrameStorage
open RationalOrderCell GeneralPaperBasisState GeneralPaperEncodedScalarStorage
open GeneralPaperRetainedBasisEndpoint (numerator denominator)
open GeneralPaperRetainedBasisEndpointBits (guardPrice endpointPrice continueRun)
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

def metadataCap (W F : ℕ) : ℕ := F+80*W+1
def controls {T m K S : ℕ} (model : RationalCostModel) (W H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (endpoint : Farey.Fraction) (value : ℚ) : List ℕ :=
  let g := guardPrice model W value
  let result := GeneralPaperRetainedBasisEndpointBits.run model W H p q reciprocal prep matrix endpoint value
  [g,result.2,GeneralPaperFinalStaticLoopStorage.bit (decide (reciprocal=true ∧ value=0))]++
    if reciprocal=true ∧ value=0 then [] else
      let inputs := GeneralPaperRetainedBasisInputs.run true model W H p q reciprocal prep matrix
      let basis := GeneralPaperSharedBasisBits.run model W prep inputs.1
      [inputs.2,basis.2,64*W,g+inputs.2,g+inputs.2+basis.2,GeneralPaperFinalStaticLoopStorage.bit basis.1.isSome]++
        match basis.1 with
        | none => []
        | some state =>
          let checked := continueRun model W prep.dictionary.label inputs.1.matrix S prep.threshold inputs.1.controls.auxiliary
            (if reciprocal then 1/value else value) inputs.1.betaN (numerator endpoint reciprocal) inputs.1.controls.N (denominator endpoint reciprocal) state
          let e := endpointPrice model W endpoint value reciprocal
          [checked.2,e,80*W,g+inputs.2+basis.2+checked.2,g+inputs.2+basis.2+checked.2+e,GeneralPaperFinalStaticLoopStorage.bit checked.1.isSome]
def basisFoot {T m K S : ℕ} (model : RationalCostModel) (W H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (value : ℚ) : ℕ :=
  if reciprocal=true ∧ value=0 then 0 else
    let inputs := GeneralPaperRetainedBasisInputs.run true model W H p q reciprocal prep matrix
    match (GeneralPaperSharedBasisBits.run model W prep inputs.1).1 with
    | none => 0
    | some state => GeneralPaperEncodedBasisStorage.footprint W state
def window {T m K S : ℕ} (model : RationalCostModel) (W H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (endpoint : Farey.Fraction) (value : ℚ) : ℕ :=
  GeneralPaperEndpointScalarStorage.window model W endpoint value reciprocal+
    (if reciprocal=true ∧ value=0 then 0 else GeneralPaperRetainedInputsReturnStorage.window model W H p q reciprocal prep matrix)+
    basisFoot model W H p q reciprocal prep matrix value+
    GeneralPaperRawEndpointReturnStorage.optionFoot W (GeneralPaperRetainedBasisEndpointBits.run model W H p q reciprocal prep matrix endpoint value).1+
    fields W (controls model W H p q reciprocal prep matrix endpoint value)+256*W
def profile (W Scalar Input Basis Point F : ℕ) : ℕ := Scalar+Input+Basis+Point+15*(natBits (metadataCap W F)+W)+288*W

theorem controls_length {T m K S : ℕ} (model : RationalCostModel) (W H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (endpoint : Farey.Fraction) (value : ℚ) : (controls model W H p q reciprocal prep matrix endpoint value).length≤15 := by
  unfold controls
  dsimp only
  split
  · norm_num only [List.length_append,List.length_cons,List.length_nil]
  · split <;> norm_num only [List.length_append,List.length_cons,List.length_nil]

theorem controls_bound {T m K S : ℕ} (model : RationalCostModel) (W H p q F : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (endpoint : Farey.Fraction) (value : ℚ)
    (hTotal : (GeneralPaperRetainedBasisEndpointBits.run model W H p q reciprocal prep matrix endpoint value).2≤F) :
    fields W (controls model W H p q reciprocal prep matrix endpoint value)≤15*(natBits (metadataCap W F)+W)+32*W := by
  let inputs := GeneralPaperRetainedBasisInputs.run true model W H p q reciprocal prep matrix
  let basis := GeneralPaperSharedBasisBits.run model W prep inputs.1
  let g := guardPrice model W value
  have hb := GeneralPaperFinalStaticLoopStorage.bit_bound (decide (reciprocal=true ∧ value=0))
  have ht := GeneralPaperFinalStaticLoopStorage.bit_bound true
  have hf := GeneralPaperFinalStaticLoopStorage.bit_bound false
  have hFields := fields_bound W (natBits (metadataCap W F)) (controls model W H p q reciprocal prep matrix endpoint value) (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    have hPath := hTotal
    unfold controls at hz
    dsimp only at hz
    by_cases hGuard : reciprocal=true ∧ value=0
    · rw [ite_eq_left hGuard] at hz
      simp only [List.append_nil,List.mem_cons,List.not_mem_nil,or_false] at hz
      have hG : g≤F := by simpa only [GeneralPaperRetainedBasisEndpointBits.run,ite_eq_left hGuard] using hTotal
      unfold metadataCap
      rcases hz with rfl|rfl|rfl <;> omega
    · rw [ite_eq_right hGuard] at hz
      simp only [GeneralPaperRetainedBasisEndpointBits.run,ite_eq_right hGuard] at hPath
      cases hBasis : basis.1 with
      | none =>
        change z∈[g,(GeneralPaperRetainedBasisEndpointBits.run model W H p q reciprocal prep matrix endpoint value).2,
          GeneralPaperFinalStaticLoopStorage.bit (decide (reciprocal=true ∧ value=0))]++
          ([inputs.2,basis.2,64*W,g+inputs.2,g+inputs.2+basis.2,GeneralPaperFinalStaticLoopStorage.bit basis.1.isSome]++
            (match basis.1 with | none => [] | some state => _)) at hz
        rw [hBasis] at hz
        change (match basis.1 with | none => (none,g+inputs.2+basis.2+64*W) | some state => _).2≤F at hPath
        rw [hBasis] at hPath
        dsimp only at hz hPath
        simp only [Option.isSome] at hz
        simp only [List.append_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
        unfold metadataCap
        rcases hz with (rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl) <;> omega
      | some state =>
        let checked := continueRun model W prep.dictionary.label inputs.1.matrix S prep.threshold inputs.1.controls.auxiliary
          (if reciprocal then 1/value else value) inputs.1.betaN (numerator endpoint reciprocal) inputs.1.controls.N (denominator endpoint reciprocal) state
        let e := endpointPrice model W endpoint value reciprocal
        have hc := GeneralPaperFinalStaticLoopStorage.bit_bound checked.1.isSome
        change z∈[g,(GeneralPaperRetainedBasisEndpointBits.run model W H p q reciprocal prep matrix endpoint value).2,
          GeneralPaperFinalStaticLoopStorage.bit (decide (reciprocal=true ∧ value=0))]++
          ([inputs.2,basis.2,64*W,g+inputs.2,g+inputs.2+basis.2,GeneralPaperFinalStaticLoopStorage.bit basis.1.isSome]++
            (match basis.1 with | none => [] | some s => _)) at hz
        rw [hBasis] at hz
        change z∈[g,(GeneralPaperRetainedBasisEndpointBits.run model W H p q reciprocal prep matrix endpoint value).2,
          GeneralPaperFinalStaticLoopStorage.bit (decide (reciprocal=true ∧ value=0))]++
          ([inputs.2,basis.2,64*W,g+inputs.2,g+inputs.2+basis.2,GeneralPaperFinalStaticLoopStorage.bit true]++
            [checked.2,e,80*W,g+inputs.2+basis.2+checked.2,g+inputs.2+basis.2+checked.2+e,GeneralPaperFinalStaticLoopStorage.bit checked.1.isSome]) at hz
        change (match basis.1 with | none => (none,g+inputs.2+basis.2+64*W) | some s => _).2≤F at hPath
        rw [hBasis] at hPath
        change g+inputs.2+basis.2+checked.2+e+80*W≤F at hPath
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
        unfold metadataCap
        rcases hz with (rfl|rfl|rfl)|((rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl)) <;> omega)
  exact hFields.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (controls_length model W H p q reciprocal prep matrix endpoint value)) _)

theorem bounded {T m K S : ℕ} (model : RationalCostModel) (W H p q Scalar Input Basis Point F : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (endpoint : Farey.Fraction) (value : ℚ)
    (hScalar : GeneralPaperEndpointScalarStorage.window model W endpoint value reciprocal≤Scalar)
    (hInput : ¬(reciprocal=true ∧ value=0) → GeneralPaperRetainedInputsReturnStorage.window model W H p q reciprocal prep matrix≤Input)
    (hBasis : ¬(reciprocal=true ∧ value=0) → ∀ state,
      (GeneralPaperSharedBasisBits.run model W prep (GeneralPaperRetainedBasisInputs.run true model W H p q reciprocal prep matrix).1).1=some state →
      GeneralPaperEncodedBasisStorage.footprint W state≤Basis)
    (hPoint : GeneralPaperRawEndpointReturnStorage.optionFoot W (GeneralPaperRetainedBasisEndpointBits.run model W H p q reciprocal prep matrix endpoint value).1≤Point)
    (hTotal : (GeneralPaperRetainedBasisEndpointBits.run model W H p q reciprocal prep matrix endpoint value).2≤F) :
    window model W H p q reciprocal prep matrix endpoint value≤profile W Scalar Input Basis Point F := by
  have hInputs : (if reciprocal=true ∧ value=0 then 0 else GeneralPaperRetainedInputsReturnStorage.window model W H p q reciprocal prep matrix)≤Input := by
    split
    · omega
    · exact hInput (by assumption)
  have hBasisFoot : basisFoot model W H p q reciprocal prep matrix value≤Basis := by
    unfold basisFoot
    dsimp only
    split
    · omega
    · split
      · omega
      · exact hBasis (by assumption) _ (by assumption)
  have hFields := controls_bound model W H p q F reciprocal prep matrix endpoint value hTotal
  unfold window profile
  omega

theorem guard_bound {T m K S : ℕ} (model : RationalCostModel) (W H p q Scalar Input Basis Point F : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (endpoint : Farey.Fraction) (value : ℚ) (hGuard : reciprocal=true ∧ value=0)
    (hScalar : GeneralPaperEndpointScalarStorage.window model W endpoint value reciprocal≤Scalar) (hPoint : 1≤Point)
    (hPrice : guardPrice model W value≤F) : window model W H p q reciprocal prep matrix endpoint value≤profile W Scalar Input Basis Point F := by
  apply bounded model W H p q Scalar Input Basis Point F reciprocal prep matrix endpoint value hScalar
  · intro h; exact False.elim (h hGuard)
  · intro h; exact False.elim (h hGuard)
  · simpa only [GeneralPaperRetainedBasisEndpointBits.run,ite_eq_left hGuard,GeneralPaperRawEndpointReturnStorage.optionFoot] using hPoint
  · simpa only [GeneralPaperRetainedBasisEndpointBits.run,ite_eq_left hGuard] using hPrice

end Blotto.GeneralPaperOuterEndpointFrameStorage
