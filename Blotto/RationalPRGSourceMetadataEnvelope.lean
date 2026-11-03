import Blotto.RationalPRGSharedConstructionMetadataWork
import Blotto.RationalPRGRequestEntryConstructionMetadata
import Blotto.RationalPRGRequestPacketRoutingMetadata
import Blotto.RationalPRGSharpArithmeticLedger

/-! Fast source envelopes for the reached midpoint, reader, entry and
factory metadata. These observers retain their original branch/multiplicity
semantics. Reference-store implementation and full representation space are
separate from the scalar/descriptor metadata covered here. -/

namespace Blotto.RationalPRGSourceMetadataEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

theorem height_eq (s d : ℕ) :
    expressionHeightBudget s d = 2^d*s+(2^d-1) := by
  have h : 1 ≤ 2^d := by have hp := Nat.two_pow_pos d; omega
  unfold expressionHeightBudget
  rw [Nat.mul_comm (s+1), Nat.mul_add, Nat.mul_one, Nat.add_sub_assoc h]

theorem midpoint_bound (c K : ℕ) :
    dyadicMidpointMetadataBound c K ≤ 1024*(c+1)*(K+1)^2 := by
  have h1 : binaryWordWidth (K+1) ≤ K+2 := by unfold binaryWordWidth; have h := Nat.log2_le_self (K+1); omega
  have h2 : binaryWordWidth (2*K+4) ≤ 2*K+5 := by unfold binaryWordWidth; have h := Nat.log2_le_self (2*K+4); omega
  have h3 : binaryWordWidth (K+2) ≤ K+3 := by unfold binaryWordWidth; have h := Nat.log2_le_self (K+2); omega
  have ha := Nat.mul_le_mul_left (K+1) (Nat.mul_le_mul_left (6+3*c) h1)
  have hb := Nat.mul_le_mul_left (2*K+1) (Nat.mul_le_mul_left (12+6*c) h2)
  have hc := Nat.mul_le_mul_left (6+3*c) h3
  unfold dyadicMidpointMetadataBound indexedLoopMetadataBound
  calc
    _ ≤ (K+1)*((6+3*c)*(K+2)+6)+K*(K+1)+
      (2*K+1)*((12+6*c)*(2*K+5)+8)+(6+3*c)*(K+3)+6 := by
        nlinarith only [ha,hb,hc]
    _ ≤ _ := by ring_nf; omega

theorem reader_bound (c n K : ℕ) :
    (10*n+6*K+6166)*positionReaderUnitBound c (RationalLottoResourceSystem.sampleBitBudget n K)+
      9072*(K*RationalPRGInput.scalarReaderUnitBound c (RationalLottoResourceSystem.sampleBitBudget n K)) ≤
        1000000000*(c+1)*(n+K+1)^2 := by
  have h1 : binaryWordWidth (RationalLottoResourceSystem.sampleBitBudget n K+2) ≤ 3003*(n+K+1) := by
    have h := Nat.log2_le_self (RationalLottoResourceSystem.sampleBitBudget n K+2)
    unfold binaryWordWidth
    rw [RationalLottoResourceSystem.sampleBitBudget_eq] at *
    omega
  have h2 : binaryWordWidth (RationalLottoResourceSystem.sampleBitBudget n K+1) ≤ 3003*(n+K+1) :=
    (binaryWordWidth_mono (by omega)).trans h1
  have ha := Nat.mul_le_mul_left (10*n+6*K+6166) (Nat.mul_le_mul_left (16+4*c) h1)
  have hb := Nat.mul_le_mul_left (9072*K) (Nat.mul_le_mul_left (5+c) h2)
  unfold positionReaderUnitBound RationalPRGInput.scalarReaderUnitBound
  calc
    _ ≤ (10*n+6*K+6166)*((16+4*c)*(3003*(n+K+1))+8)+
      9072*(K*((5+c)*(3003*(n+K+1))+1)) := by nlinarith only [ha,hb]
    _ ≤ _ := by ring_nf; omega

theorem entry_bound (c s : ℕ) :
    RationalTerminalLotto.entryConstructionMetadataBound c s ≤ 2^128*(c+1)*(s+1) := by
  norm_num [Blotto.indexedLoopMetadataBound,
    Blotto.rationalEnvironmentMetadataBound,
    Blotto.RationalExpression.metadataInstructionBound,
    Blotto.RationalNestedSpec.sortingFieldsMetadataBound,
    Blotto.RationalTerminalResources.inputConstructionMetadataBound,
    Blotto.PreparedSegmentDescriptor.preparationMetadataBound,
    Blotto.RationalThreeInputCode.constructionMetadataBound,
    Blotto.RationalThreeSpecCode.constructionMetadataBound,
    Blotto.RationalThreeSpecCode.endpointConstructionMetadataBound,
    Blotto.RationalNestedInput.firstConditionalMetadataBound,
    Blotto.RationalNestedInput.firstMidpointConstructionMetadataBound,
    Blotto.RationalNestedInput.familyInputMetadataBound,
    Blotto.RationalNestedInput.secondUniformMetadataBound,
    Blotto.RationalNestedInput.secondProfileMetadataBound,
    Blotto.RationalNestedResidualCode.compilerMetadataBound,
    Blotto.RationalNestedInput.paddedResidualMetadataBound,
    Blotto.RationalNestedInput.thirdProfileMetadataBound,
    Blotto.RationalNestedInput.profileConstructionMetadataBound,
    Blotto.RationalNestedSpec.profileConstructionMetadataBound,
    Blotto.RationalPermutationCode.descriptorMetadataBound,
    Blotto.RationalTerminalResources.profileConstructionMetadataBound,
    Blotto.RationalUniformGroupSpec.entryConstructionMetadataBound,
    Blotto.RationalFourSpec.wrapperConstructionMetadataBound,
    Blotto.RationalFourParameterTable.preparationMetadataBound,
    Blotto.RationalFourInput.entryParameterMetadataBound,
    Blotto.RationalOverlapFormula.slotIndexMetadataUnitBound,
    Blotto.RationalFourInput.gluingConstructionMetadataBound,
    Blotto.RationalSplitCode.descriptorMetadataBound,
    Blotto.RationalMergeFourInput.constructionMetadataBound,
    Blotto.RationalFourInput.smallParentConstructionMetadataBound,
    Blotto.RationalFourInput.entryConstructionMetadataBound,
    Blotto.RationalMixedGroupSpec.entryConstructionMetadataBound,
    Blotto.RationalTerminalLotto.entryConstructionMetadataBound, height_eq, binaryWordWidth, Nat.log2_def]
  ring_nf
  omega

theorem factory_bound (c s K : ℕ) :
    RationalTerminalResources.profileConstructionMetadataBound c s K ≤ 2^128*(c+1)*(s+K+3) := by
  norm_num [Blotto.indexedLoopMetadataBound,
    Blotto.rationalEnvironmentMetadataBound,
    Blotto.RationalExpression.metadataInstructionBound,
    Blotto.RationalNestedSpec.sortingFieldsMetadataBound,
    Blotto.RationalTerminalResources.inputConstructionMetadataBound,
    Blotto.PreparedSegmentDescriptor.preparationMetadataBound,
    Blotto.RationalThreeInputCode.constructionMetadataBound,
    Blotto.RationalThreeSpecCode.constructionMetadataBound,
    Blotto.RationalThreeSpecCode.endpointConstructionMetadataBound,
    Blotto.RationalNestedInput.firstConditionalMetadataBound,
    Blotto.RationalNestedInput.firstMidpointConstructionMetadataBound,
    Blotto.RationalNestedInput.familyInputMetadataBound,
    Blotto.RationalNestedInput.secondUniformMetadataBound,
    Blotto.RationalNestedInput.secondProfileMetadataBound,
    Blotto.RationalNestedResidualCode.compilerMetadataBound,
    Blotto.RationalNestedInput.paddedResidualMetadataBound,
    Blotto.RationalNestedInput.thirdProfileMetadataBound,
    Blotto.RationalNestedInput.profileConstructionMetadataBound,
    Blotto.RationalNestedSpec.profileConstructionMetadataBound,
    Blotto.RationalPermutationCode.descriptorMetadataBound,
    Blotto.RationalTerminalResources.profileConstructionMetadataBound,
    Blotto.RationalUniformGroupSpec.entryConstructionMetadataBound,
    Blotto.RationalFourSpec.wrapperConstructionMetadataBound,
    Blotto.RationalFourParameterTable.preparationMetadataBound,
    Blotto.RationalFourInput.entryParameterMetadataBound,
    Blotto.RationalOverlapFormula.slotIndexMetadataUnitBound,
    Blotto.RationalFourInput.gluingConstructionMetadataBound,
    Blotto.RationalSplitCode.descriptorMetadataBound,
    Blotto.RationalMergeFourInput.constructionMetadataBound,
    Blotto.RationalFourInput.smallParentConstructionMetadataBound,
    Blotto.RationalFourInput.entryConstructionMetadataBound,
    Blotto.RationalMixedGroupSpec.entryConstructionMetadataBound,
    Blotto.RationalTerminalLotto.entryConstructionMetadataBound, height_eq, binaryWordWidth, Nat.log2_def]
  simp only [max_def]
  split_ifs <;> ring_nf <;> omega

theorem packet_routing_bound (c n s : ℕ) :
    RationalTerminalLotto.packetRoutingMetadataBound c n s ≤
      16384*(c+1)*(n+1)*(n+s+6) := by
  simp only [RationalTerminalLotto.packetRoutingMetadataBound,
    RationalTerminalLotto.groupPacketMetadataBound,
    RationalTerminalPacking.routingMetadataBound, RationalTerminalPacking.entryMetadataBound,
    rationalEnvironmentMetadataBound, RationalExpression.metadataInstructionBound,
    indexedLoopMetadataBound, height_eq]
  generalize hb : binaryWordWidth (n+4) = b
  generalize ha : binaryWordWidth (n+1) = a
  norm_num [binaryWordWidth, Nat.log2_def]
  have hB : b ≤ n+5 := by rw [← hb]; unfold binaryWordWidth; have h := Nat.log2_le_self (n+4); omega
  have hA : a ≤ n+2 := by rw [← ha]; unfold binaryWordWidth; have h := Nat.log2_le_self (n+1); omega
  calc
    _ ≤ 304*s+742+177*c+
      (n*(16*s+364+114*c+(8+8*c)*(n+5))+
        5*((n+1)*((6+3*c)*(n+2)+6))+384+144*c) := by
          have h1 := Nat.mul_le_mul_left n (Nat.mul_le_mul_left (8+8*c) hB)
          have h2 := Nat.mul_le_mul_left (5*(n+1)) (Nat.mul_le_mul_left (6+3*c) hA)
          nlinarith only [h1,h2]
    _ ≤ _ := by ring_nf; omega

noncomputable def work {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.selectedMidpointMetadataBitWork primitive rich K bits+
    i.selectedPositionReaderAllowance c rich K bits+
    i.selectedScalarReaderWork primitive rich K bits+
    i.selectedConstructionMetadataWork primitive c rich K bits+
    i.selectedEntryConstructionMetadataWork primitive c rich K bits+
    i.selectedPacketRoutingMetadataWork primitive c rich K bits

def componentBound (c n s K : ℕ) : ℕ :=
  9072*dyadicMidpointMetadataBound c K+
    ((10*n+6*K+6166)*positionReaderUnitBound c (RationalLottoResourceSystem.sampleBitBudget n K)+
      9072*(K*RationalPRGInput.scalarReaderUnitBound c (RationalLottoResourceSystem.sampleBitBudget n K)))+
    2592*RationalTerminalResources.profileConstructionMetadataBound c
      (expressionHeightBudget (max s (K+2)) 22) K+
    RationalTerminalLotto.entryConstructionMetadataBound c s+
    RationalTerminalLotto.packetRoutingMetadataBound c n s

theorem work_bound {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    work i primitive c rich K bits ≤ componentBound c n (3+i.originalInputWordWidth) K := by
  have hm := i.selectedMidpointMetadataBitWork_bound primitive c hPrimitive rich K bits
  have hp := i.selectedPositionReaderAllowance_bound c rich K bits
  have hs := i.selectedScalarReaderWork_bound primitive c hPrimitive rich K bits
  have hf := i.selectedConstructionMetadataWork_bound primitive c hPrimitive rich K bits
  have he := i.selectedEntryConstructionMetadataWork_bound primitive c hPrimitive rich K bits
  have hr := i.selectedPacketRoutingMetadataWork_bound_of_inputWidth primitive c hPrimitive
    (3+i.originalInputWordWidth) le_rfl rich K bits
  unfold work componentBound
  omega

theorem component_bound_fast {n : ℕ} (i : RationalPRGOriginalInput n) (c K : ℕ) :
    componentBound c n (3+i.originalInputWordWidth) K ≤
      2^256*(c+1)*(n+K+1)*(i.originalInputWordWidth+K+6) := by
  let S := i.originalInputWordWidth+K+6
  let N := n+K+1
  have hn := RationalPRGLinearFramingWork.count_le_inputWidth i
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hNS : N ≤ S := by dsimp [N,S]; omega
  have hK : K+1 ≤ N := by dsimp [N]; omega
  have hm := midpoint_bound c K
  have hr := reader_bound c n K
  have he := entry_bound c (3+i.originalInputWordWidth)
  have hf := factory_bound c (expressionHeightBudget (max (3+i.originalInputWordWidth) (K+2)) 22) K
  have hp := packet_routing_bound c n (3+i.originalInputWordWidth)
  have hH : expressionHeightBudget (max (3+i.originalInputWordWidth) (K+2)) 22+K+3 ≤ (2^22+1)*S := by
    have hMax : max (3+i.originalInputWordWidth) (K+2)+1 ≤ S := by
      have hh : max (3+i.originalInputWordWidth) (K+2) ≤ i.originalInputWordWidth+K+5 :=
        max_le (by omega) (by omega)
      dsimp [S]
      omega
    rw [height_eq]
    dsimp [S] at *
    omega
  have hHS := Nat.mul_le_mul_left (2^128*(c+1)) hH
  have hSq := Nat.mul_le_mul hK (hK.trans hNS)
  have hNSq := Nat.mul_le_mul_left N hNS
  have hSmall : 3+i.originalInputWordWidth+1 ≤ S := by dsimp [S]; omega
  have hE := Nat.mul_le_mul_left (2^128*(c+1)) hSmall
  have hPacket : n+1 ≤ N ∧ n+(3+i.originalInputWordWidth)+6 ≤ 2*S := by dsimp [N,S]; omega
  have hP := Nat.mul_le_mul hPacket.1 hPacket.2
  have hPE := Nat.mul_le_mul_left (16384*(c+1)) hP
  have hME := Nat.mul_le_mul_left (9072*(1024*(c+1))) hSq
  have hRE := Nat.mul_le_mul_left (1000000000*(c+1)) hNSq
  have hSE : S ≤ N*S := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right S hN
  have hFE := Nat.mul_le_mul_left (2592*(2^128*(c+1)*(2^22+1))) hSE
  have hEE := Nat.mul_le_mul_left (2^128*(c+1)) hSE
  unfold componentBound
  change _ ≤ 2^256*(c+1)*N*S
  change _ ≤ 1000000000*(c+1)*N^2 at hr
  calc
    _ ≤ (9072*1024+1000000000+2592*2^128*(2^22+1)+2^128+32768)*(c+1)*N*S := by
      nlinarith only [hm,hr,he,hf,hp,hHS,hE,hPE,hME,hRE,hFE,hEE]
    _ ≤ _ := by gcongr; norm_num

theorem work_fast {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    work i primitive c rich K bits ≤
      2^256*(c+1)*(n+K+1)*(i.originalInputWordWidth+K+6) :=
  (work_bound i primitive c hPrimitive rich K bits).trans (component_bound_fast i c K)

theorem work_raw_accuracy {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n a.precision) → Bool) :
    work i primitive c rich a.precision bits ≤
      2^256*(c+1)*(n+⌈Real.logb 2 (1/a.real)⌉₊+6)*
        (i.originalInputWordWidth+⌈Real.logb 2 (1/a.real)⌉₊+11) := by
  have hK : a.precision ≤ ⌈Real.logb 2 (1/a.real)⌉₊+5 := by
    simpa only [a.logExponent_eq_ceil] using a.precision_log_bounds.2
  have hN := Nat.mul_le_mul_left (2^256*(c+1)) (show n+a.precision+1 ≤ n+⌈Real.logb 2 (1/a.real)⌉₊+6 by omega)
  exact (work_fast i primitive c hPrimitive rich a.precision bits).trans
    (Nat.mul_le_mul hN (by omega))

theorem work_rational_accuracy {n : ℕ} (i : RationalPRGOriginalInput n) (ε : ℚ) (hε : 0 < ε)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n (rationalAccuracyPrecision ε)) → Bool) :
    work i primitive c rich (rationalAccuracyPrecision ε) bits ≤
      2^256*(c+1)*(n+⌈Real.logb 2 (1/(ε:ℝ))⌉₊+6)*
        (i.originalInputWordWidth+⌈Real.logb 2 (1/(ε:ℝ))⌉₊+11) := by
  have hK := (rationalAccuracyPrecision_log_bounds ε hε).2
  have hN := Nat.mul_le_mul_left (2^256*(c+1))
    (show n+rationalAccuracyPrecision ε+1 ≤ n+⌈Real.logb 2 (1/(ε:ℝ))⌉₊+6 by omega)
  exact (work_fast i primitive c hPrimitive rich (rationalAccuracyPrecision ε) bits).trans
    (Nat.mul_le_mul hN (by omega))

end Blotto.RationalPRGSourceMetadataEnvelope
