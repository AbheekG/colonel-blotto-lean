import Blotto.PRGPaperPreparationCost
import Blotto.RationalPRGSourceMetadataEnvelope
import Blotto.RationalPRGReferenceRouteCost
import Blotto.RationalPRGGroupTableConstructionWork
import Blotto.RationalPRGSeedPreparationWork

/-! Composition of the primary paper-model draw prices. Rational arithmetic,
bit control, reached metadata, route references, group-table construction,
source packing, seed handling and actual stored-row framing retain their
individual meanings. No native library or allocator rate is asserted. -/

namespace Blotto.RationalLottoResourceSystem

noncomputable def paperPackingControlWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedTerminalWindowWork (coinBitBudget n K) (firstBitBlock (coinBitBudget n K) K inner)
    (fun value _ _ => RationalPackingMetadata.packedWork primitive
      (i.terminalData value).length (i.terminalData value).B (i.terminalData value).uniformItems)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le _)

theorem OnLattice.paperPackingControlWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    i.paperPackingControlWork primitive K bits ≤ RationalPackingMetadata.packedBound c n := by
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  let inner := firstBitBlock (innerBitBudget n K) K bits
  have hw := i.sharedTerminalWindowWork_bound D h.1 (coinBitBudget n K)
    (firstBitBlock (coinBitBudget n K) K inner)
    (fun value _ _ => RationalPackingMetadata.packedWork primitive
      (i.terminalData value).length (i.terminalData value).B (i.terminalData value).uniformItems)
    (RationalPackingMetadata.packedBound c n) 0
    (fun value _ _ _ => by
      simpa only [Nat.zero_mul,Nat.add_zero] using
        (i.terminalData value).packingMetadataWork_bound primitive c hPrimitive)
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le _)
  simpa only [paperPackingControlWork,Nat.zero_mul,Nat.add_zero] using hw

end Blotto.RationalLottoResourceSystem

namespace Blotto.PRGPaperDrawCost
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 512

def width {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : ℕ :=
  RationalPRGLinearFramingWork.uniformWidth i K

def outputWidth {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : ℕ :=
  2^77*(i.originalInputWordWidth+K+6)

def logFactor {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : ℕ :=
  binaryWordWidth (width i K+2)+1

def bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K h : ℕ) : ℕ :=
  3*h+2^300*(c+1)*((n+1)*model.rat (width i K)+(n+K+1)*width i K*logFactor i K)

noncomputable def arithmeticWork {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.normalizationBitWork model+
    if rich then i.richProcessingAndScalingWork model primitive false K bits
    else i.poorProcessingAndScalingWork model primitive false K bits

theorem arithmetic_work_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (rich : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    arithmeticWork i model primitive rich K bits ≤ RationalPRGSharpArithmeticLedger.sharpBound i model c K 0 := by
  have hn := i.normalizationBitWork_bound model
  have hr := i.richProcessingAndScalingWork_bound model primitive c hPrimitive false K bits
  have hp := i.poorProcessingAndScalingWork_logical_bound model primitive c hPrimitive K bits
  have hCoeff := Nat.mul_le_mul_right (model.rat i.processingSourceWidth)
    (show 32*n+15 ≤ 192*n+15 by omega)
  apply le_trans (b := RationalPRGLinearFramingWork.bound i model c K 0)
  · unfold arithmeticWork RationalPRGLinearFramingWork.bound
    cases rich <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mul_zero,Nat.add_zero] <;> omega
  · exact RationalPRGSharpArithmeticLedger.bound_sharp i model c K 0

noncomputable def packingWork {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ)
    (rich : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then i.normalizedInput.richNativeSystem.paperPackingControlWork primitive K bits
  else i.normalizedInput.poorNativeSystem.paperPackingControlWork primitive K bits

theorem packing_work_bound {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    packingWork i primitive rich K bits ≤ RationalPackingMetadata.packedBound c n := by
  cases rich with
  | false =>
    exact i.normalizedInput.poorNativeSystem_on_lattice.paperPackingControlWork_bound primitive c hPrimitive K bits
  | true =>
    exact i.normalizedInput.richNativeSystem_on_lattice.paperPackingControlWork_bound primitive c hPrimitive K bits

def seedWork (primitive : ℕ → ℕ) (R : ℕ) (bits : Fin R → Bool) : ℕ :=
  RationalPRGBinaryRequest.seedPreparationBitWork primitive R (List.ofFn bits)+
    indexedLoopMetadataBitWork primitive 0 R+R

def seedBound (c R : ℕ) : ℕ :=
  (R+1)*((c+2)*binaryWordWidth (R+1)+1)+c*binaryWordWidth R+3*R+indexedLoopMetadataBound c R

theorem seed_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (R : ℕ) (bits : Fin R → Bool) : seedWork primitive R bits ≤ seedBound c R := by
  have hs := RationalPRGBinaryRequest.seedPreparationBitWork_bound primitive c hPrimitive R (List.ofFn bits)
  simp only [List.length_ofFn,max_self] at hs
  have hi := indexedLoopMetadataBitWork_bound primitive c hPrimitive R
  unfold seedWork seedBound
  omega

theorem seed_bound_fast (c R : ℕ) :
    seedBound c R ≤ (10*c+20)*(R+1)*(binaryWordWidth (R+1)+1) := by
  have hw : binaryWordWidth R ≤ binaryWordWidth (R+1) := binaryWordWidth_mono (by omega)
  have hp := Nat.mul_le_mul_left c hw
  unfold seedBound indexedLoopMetadataBound
  calc
    _ ≤ (R+1)*((c+2)*binaryWordWidth (R+1)+1)+c*binaryWordWidth (R+1)+3*R+
      (R+1)*((6+3*c)*binaryWordWidth (R+1)+6) := by omega
    _ ≤ _ := by ring_nf; omega

noncomputable def work {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) : ℕ :=
  let i := p.source
  let K := p.precision
  arithmeticWork i model primitive rich K bits+
    RationalPRGSourceMetadataEnvelope.work i primitive c rich K bits+
    i.selectedRouteReferenceWork primitive rich K bits+packingWork i primitive rich K bits+
    i.selectedGroupTableConstructionWork primitive rich K bits+
    ReferenceStoredRowFrame.work primitive p.bytes (NativePRGPreparedSampler.sample p rich bits) (outputWidth i K)+
    seedWork primitive (RationalLottoResourceSystem.sampleBitBudget n K) bits

theorem width_facts {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    1 ≤ width i K ∧ n+K+1 ≤ width i K ∧ outputWidth i K+1 ≤ width i K ∧
      3+i.originalInputWordWidth ≤ width i K ∧
      RationalLottoResourceSystem.sampleBitBudget n K ≤ width i K ∧
      RationalTerminalPacking.routePayloadWidth n (3+i.originalInputWordWidth)+1 ≤ width i K ∧
      n+4 ≤ width i K+2 := by
  have hn := RationalPRGLinearFramingWork.count_le_inputWidth i
  have hl := Nat.log2_le_self (n+4)
  unfold width outputWidth RationalPRGLinearFramingWork.uniformWidth
    RationalTerminalPacking.routePayloadWidth binaryWordWidth
  rw [RationalLottoResourceSystem.sampleBitBudget_eq]
  norm_num only [Nat.reducePow,Nat.reduceMul]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

theorem rectangle (N W Q : ℕ) (hN : 1 ≤ N) (hW : 1 ≤ W) (hQ : 1 ≤ Q) :
    1 ≤ N*W*Q ∧ W ≤ N*W*Q ∧ N*Q ≤ N*W*Q ∧ N*W ≤ N*W*Q := by
  have hNW : 1 ≤ N*W := Nat.mul_le_mul hN hW
  have hB : 1 ≤ N*W*Q := Nat.mul_le_mul hNW hQ
  have hLast : N*W ≤ N*W*Q := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N*W) hQ
  have hWFirst : W ≤ N*W := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right W hN
  have hNFirst : N ≤ N*W := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hW
  exact ⟨hB,hWFirst.trans hLast,Nat.mul_le_mul_right Q hNFirst,hLast⟩

theorem packing_bound_fast (c n Q : ℕ) (hQ : 1 ≤ Q) (hWidth : binaryWordWidth (n+4) ≤ Q) :
    RationalPackingMetadata.packedBound c n ≤ 128*(c+1)*(n+1)*Q := by
  have hIndex : binaryWordWidth (n+1) ≤ Q :=
    (binaryWordWidth_mono (by omega : n+1 ≤ n+4)).trans hWidth
  have hBody : RationalPackingMetadata.bodyBound c n ≤ (26+6*c)*Q := by
    have hp := Nat.mul_le_mul_left (12+6*c) hWidth
    unfold RationalPackingMetadata.bodyBound
    nlinarith only [hp,hQ]
  have hLabel : RationalPackingMetadata.labelBound c n ≤ (10+3*c)*Q := by
    have hp := Nat.mul_le_mul_left (4+3*c) hWidth
    unfold RationalPackingMetadata.labelBound
    nlinarith only [hp,hQ]
  have hGroup : RationalPackingMetadata.groupCellBound c n ≤ (8+2*c)*Q := by
    have hp := Nat.mul_le_mul_left (4+2*c) hWidth
    unfold RationalPackingMetadata.groupCellBound
    nlinarith only [hp,hQ]
  have hLoop : indexedLoopMetadataBound c n ≤ (n+1)*((12+3*c)*Q) := by
    have hp := Nat.mul_le_mul_left (6+3*c) hIndex
    have hh : (6+3*c)*binaryWordWidth (n+1)+6 ≤ (12+3*c)*Q := by nlinarith only [hp,hQ]
    exact Nat.mul_le_mul_left (n+1) hh
  have hOne : 1 ≤ n+1 := by omega
  have hb := Nat.mul_le_mul (show n ≤ n+1 by omega) hBody
  have hl := Nat.mul_le_mul_left (n+1) hLabel
  have hg := Nat.mul_le_mul hOne hGroup
  have hc := Nat.mul_le_mul_right ((n+1)*Q) (show 96+24*c ≤ 128*(c+1) by omega)
  unfold RationalPackingMetadata.packedBound
  nlinarith only [hb,hl,hLoop,hg,hc]

theorem route_bound_fast {n : ℕ} (i : RationalPRGOriginalInput n) (c K : ℕ) :
    RationalPRGReferenceRouteCost.bound c n (3+i.originalInputWordWidth) ≤
      1024*(c+1)*(n+K+1)*width i K*logFactor i K := by
  let W := width i K
  let Q := logFactor i K
  let N := n+K+1
  let B := N*W*Q
  have hf := width_facts i K
  have hQ : 1 ≤ Q := by dsimp [Q,logFactor]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hRect := rectangle N W Q hN hf.1 hQ
  have hn : n+1 ≤ N := by dsimp [N]; omega
  have hNW : n+1 ≤ W := hn.trans hf.2.1
  have ha := RationalPRGReferenceRouteCost.address_log_bound n (3+i.originalInputWordWidth)
  have hlog1 := binaryWordWidth_mono (show n+2 ≤ W+2 by omega)
  have hlog2 := binaryWordWidth_mono (show
      RationalTerminalPacking.routePayloadWidth n (3+i.originalInputWordWidth)+1 ≤ W+2 by
        have h := hf.2.2.2.2.2.1; omega)
  have hA : RationalPRGReferenceRouteCost.addressWidth n (3+i.originalInputWordWidth)+1 ≤ 2*Q := by
    change RationalPRGReferenceRouteCost.addressWidth n (3+i.originalInputWordWidth)+1 ≤
      2*(binaryWordWidth (W+2)+1)
    omega
  have hProduct := Nat.mul_le_mul (Nat.mul_le_mul hn hNW) hA
  have hCost := Nat.mul_le_mul_left (32*c+112) hProduct
  have hCoeff := Nat.mul_le_mul_right B (show 64*c+227 ≤ 1024*(c+1) by omega)
  have hB : 1 ≤ B := hRect.1
  calc
    _ ≤ (64*c+224)*B+3 := by
      unfold RationalPRGReferenceRouteCost.bound
      dsimp only [B]
      nlinarith only [hCost]
    _ ≤ 1024*(c+1)*B := by nlinarith only [hB,hCoeff]
    _ = _ := by dsimp only [B,N,W,Q]; ring

theorem group_bound_fast {n : ℕ} (i : RationalPRGOriginalInput n) (c K : ℕ) :
    RationalTerminalLotto.groupTableConstructionBound c n (3+i.originalInputWordWidth) ≤
      256*(c+1)*(n+K+1)*width i K*logFactor i K := by
  let W := width i K
  let Q := logFactor i K
  let N := n+K+1
  let B := N*W*Q
  have hf := width_facts i K
  have hQ : 1 ≤ Q := by dsimp [Q,logFactor]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hRect := rectangle N W Q hN hf.1 hQ
  have hWidth : binaryWordWidth (n+4) ≤ Q :=
    (binaryWordWidth_mono hf.2.2.2.2.2.2).trans (Nat.le_succ _)
  have hIndex := Nat.mul_le_mul_left n hWidth
  have hn : n ≤ N := by dsimp [N]; omega
  have hnQ : n*Q ≤ B := (Nat.mul_le_mul_right Q hn).trans hRect.2.2.1
  have hs : 3+i.originalInputWordWidth ≤ B := hf.2.2.2.1.trans hRect.2.1
  have hConst := Nat.mul_le_mul_left (132+36*c) hRect.1
  have hCoeff := Nat.mul_le_mul_right B (show 186+36*c ≤ 256*(c+1) by omega)
  have hFour : binaryWordWidth 4 = 3 := by decide
  calc
    _ ≤ 256*(c+1)*B := by
      unfold RationalTerminalLotto.groupTableConstructionBound RationalTerminalLotto.groupEntryPayloadWidth
        indexedLoopMetadataBound
      rw [hFour]
      nlinarith only [hIndex,hnQ,hs,hConst,hCoeff]
    _ = _ := by dsimp only [B,N,W,Q]; ring

theorem formatting_bound_fast {n : ℕ} (i : RationalPRGOriginalInput n) (header : List Bool) (c K : ℕ) :
    ReferenceStoredRowFrame.bound header c n (outputWidth i K) ≤
      3*header.length+4096*(c+1)*(n+K+1)*width i K*logFactor i K := by
  let W := width i K
  let Q := logFactor i K
  let N := n+K+1
  let B := N*W*Q
  have hf := width_facts i K
  have hQ : 1 ≤ Q := by dsimp [Q,logFactor]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hRect := rectangle N W Q hN hf.1 hQ
  have hn : n+1 ≤ N := by dsimp [N]; omega
  have hNW : n+1 ≤ W := hn.trans hf.2.1
  have h1 := binaryWordWidth_mono (show n+1 ≤ W+2 by omega)
  have h2 := binaryWordWidth_mono (show outputWidth i K+1 ≤ W+2 by have h := hf.2.2.1; omega)
  have ha := StoredArrayReferenceList.poolAddressWidth_log_bound n (outputWidth i K)
  have hA : StoredArrayReferenceList.poolAddressWidth n (outputWidth i K)+1 ≤ 2*Q := by
    change StoredArrayReferenceList.poolAddressWidth n (outputWidth i K)+1 ≤
      2*(binaryWordWidth (W+2)+1)
    omega
  have hQOut : binaryWordWidth (outputWidth i K+2)+1 ≤ Q := by
    apply Nat.add_le_add_right
    apply binaryWordWidth_mono
    have h := hf.2.2.1
    omega
  have hRef := Nat.mul_le_mul_left (5*c+6) (Nat.mul_le_mul hn hA)
  have hNQ := hRect.2.2.1
  have hNQPrice := Nat.mul_le_mul_left (10*c+12) hNQ
  have hRefBound : (5*c+6)*(n+1)*(StoredArrayReferenceList.poolAddressWidth n (outputWidth i K)+1) ≤
      (10*c+12)*B := by dsimp only [B]; nlinarith only [hRef,hNQPrice]
  have hOut := Nat.mul_le_mul (Nat.mul_le_mul (show n ≤ N by omega) hf.2.2.1) hQOut
  have hOutBound := Nat.mul_le_mul_left (1024*(c+1)) hOut
  have hOutPrice : 1024*(c+1)*(n*(outputWidth i K+1)*(binaryWordWidth (outputWidth i K+2)+1)) ≤
      1024*(c+1)*B := hOutBound
  have hnB : n ≤ B := (show n ≤ W by omega).trans hRect.2.1
  have hB : 1 ≤ B := hRect.1
  have hCoeff := Nat.mul_le_mul_right B (show 1034*c+1043 ≤ 4096*(c+1) by omega)
  calc
    _ ≤ 3*header.length+4096*(c+1)*B := by
      unfold ReferenceStoredRowFrame.bound
      nlinarith only [hRefBound,hOutPrice,hnB,hB,hCoeff]
    _ = _ := by dsimp only [B,N,W,Q]; ring

theorem seed_bound_width {n : ℕ} (i : RationalPRGOriginalInput n) (c K : ℕ) :
    seedBound c (RationalLottoResourceSystem.sampleBitBudget n K) ≤
      100000*(c+1)*(n+K+1)*width i K*logFactor i K := by
  let R := RationalLottoResourceSystem.sampleBitBudget n K
  let N := n+K+1
  let W := width i K
  let Q := logFactor i K
  have hf := width_facts i K
  have hQ : 1 ≤ Q := by dsimp [Q,logFactor]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hRect := rectangle N W Q hN hf.1 hQ
  have hR : R+1 ≤ 3008*N := by dsimp [R,N]; rw [RationalLottoResourceSystem.sampleBitBudget_eq]; omega
  have hLog : binaryWordWidth (R+1)+1 ≤ Q := by
    apply Nat.add_le_add_right
    apply binaryWordWidth_mono
    have h := hf.2.2.2.2.1
    omega
  have hs := seed_bound_fast c R
  have hm := Nat.mul_le_mul_left (10*c+20) (Nat.mul_le_mul hR hLog)
  have hb := Nat.mul_le_mul_left (3008*(10*c+20)) hRect.2.2.1
  have hc := Nat.mul_le_mul_right (N*W*Q) (show 3008*(10*c+20) ≤ 100000*(c+1) by omega)
  calc
    _ ≤ 100000*(c+1)*(N*W*Q) := by nlinarith only [hs,hm,hb,hc]
    _ = _ := by dsimp only [N,W,Q]; ring

theorem sample_width {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) (j : Fin n) :
    rationalWordWidth ((NativePRGPreparedSampler.sample p rich bits).allocation j) ≤
      outputWidth p.source p.precision := by
  cases rich with
  | false => exact (p.source.storedSample_widths p.precision bits j).2
  | true => exact (p.source.storedSample_widths p.precision bits j).1

theorem work_bound {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    work p model primitive c rich bits ≤ bound p.source model c p.precision p.bytes.length := by
  let i := p.source
  let K := p.precision
  let W := width i K
  let Q := logFactor i K
  let N := n+K+1
  let B := N*W*Q
  let Z := (n+1)*model.rat W+B
  have hf := width_facts i K
  have hQ : 1 ≤ Q := by dsimp [Q,logFactor]; omega
  have hRect := rectangle N W Q (by dsimp [N]; omega) hf.1 hQ
  have hBZ : B ≤ Z := Nat.le_add_left _ _
  have hS : i.originalInputWordWidth+K+6 ≤ W := by
    dsimp [W,width,RationalPRGLinearFramingWork.uniformWidth]
    omega
  have hSB : N*(i.originalInputWordWidth+K+6) ≤ B :=
    (Nat.mul_le_mul_left N hS).trans hRect.2.2.2
  have hMeta := RationalPRGSourceMetadataEnvelope.work_fast i primitive c hPrimitive rich K bits
  have hMetaB := Nat.mul_le_mul_left (2^256*(c+1)) hSB
  have hRoute := (i.selectedRouteReferenceWork_bound primitive c hPrimitive rich K bits).trans
    (route_bound_fast i c K)
  have hPackWidth : binaryWordWidth (n+4) ≤ Q :=
    (binaryWordWidth_mono hf.2.2.2.2.2.2).trans (Nat.le_succ _)
  have hPack := (packing_work_bound i primitive c hPrimitive rich K bits).trans
    (packing_bound_fast c n Q hQ hPackWidth)
  have hnQ : (n+1)*Q ≤ B :=
    (Nat.mul_le_mul_right Q (show n+1 ≤ N by dsimp [N]; omega)).trans hRect.2.2.1
  have hPackB := Nat.mul_le_mul_left (128*(c+1)) hnQ
  have hGroup := (i.selectedGroupTableConstructionWork_bound_of_inputWidth primitive c hPrimitive
    (3+i.originalInputWordWidth) le_rfl rich K bits).trans (group_bound_fast i c K)
  have hFrame := (ReferenceStoredRowFrame.work_bound primitive c hPrimitive p.bytes
    (NativePRGPreparedSampler.sample p rich bits) (outputWidth i K) (sample_width p rich bits)).trans
      (formatting_bound_fast i p.bytes c K)
  have hSeed := (seed_work_bound primitive c hPrimitive
    (RationalLottoResourceSystem.sampleBitBudget n K) bits).trans (seed_bound_width i c K)
  have hArith := arithmetic_work_bound i model primitive c hPrimitive rich K bits
  have hAZ : (n+1)*model.rat W+N*W ≤ Z := Nat.add_le_add_left hRect.2.2.2 _
  have hArithZ := Nat.mul_le_mul_left (1000000000*(c+1)) hAZ
  have hOther := Nat.mul_le_mul_left ((2^256+1024+128+256+4096+100000)*(c+1)) hBZ
  have hCoeff := Nat.mul_le_mul_right ((c+1)*Z)
    (show 1000000000+2^256+1024+128+256+4096+100000 ≤ 2^300 by decide)
  unfold work bound RationalPRGSharpArithmeticLedger.sharpBound at *
  change _ ≤ 3*p.bytes.length+2^300*(c+1)*Z
  dsimp only [i,K,W,Q,N,B,Z,width] at hMeta hMetaB hRoute hPack hPackB hGroup hFrame hSeed hArith hArithZ hOther hCoeff ⊢
  norm_num only [Nat.reducePow] at hMeta hMetaB hOther hCoeff ⊢
  nlinarith only [hMeta,hMetaB,hRoute,hPack,hPackB,hGroup,hFrame,hSeed,hArith,hArithZ,hOther,hCoeff]

def accuracyWidth {n : ℕ} (i : RationalPRGOriginalInput n) (k : ℕ) : ℕ :=
  2^90*(i.originalInputWordWidth+k+11)

def accuracyBound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (c k h : ℕ) : ℕ :=
  let V := accuracyWidth i k
  3*h+2^300*(c+1)*((n+1)*model.rat V+(n+k+6)*V*(binaryWordWidth (V+2)+1))

theorem bound_accuracy {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (c K k h : ℕ) (hK : K ≤ k+5) : bound i model c K h ≤ accuracyBound i model c k h := by
  have hW : width i K ≤ accuracyWidth i k := by
    unfold width RationalPRGLinearFramingWork.uniformWidth accuracyWidth
    exact Nat.mul_le_mul_left (2^90) (by omega)
  have hRat := Nat.mul_le_mul_left (n+1) (model.monotone hW)
  have hLog := Nat.add_le_add_right (binaryWordWidth_mono (Nat.add_le_add_right hW 2)) 1
  have hBits := Nat.mul_le_mul (Nat.mul_le_mul (show n+K+1 ≤ n+k+6 by omega) hW) hLog
  exact Nat.add_le_add_left (Nat.mul_le_mul_left (2^300*(c+1))
    (Nat.add_le_add hRat hBits)) (3*h)

theorem envelope_at_profile (model : RationalCostModel) (C d : ℕ)
    (hFast : ∀ w, model.rat w ≤ C*(w+1)*(binaryWordWidth (w+2)+1)^d)
    (n N W : ℕ) (hN : n+1 ≤ N) :
    (n+1)*model.rat W+N*W*(binaryWordWidth (W+2)+1) ≤
      (C+1)*N*(W+1)*(binaryWordWidth (W+2)+1)^(d+1) := by
  let Q := binaryWordWidth (W+2)+1
  have hQ : 0 < Q := by dsimp only [Q]; omega
  have hStep : Q^d ≤ Q^(d+1) := Nat.pow_le_pow_right hQ (Nat.le_succ _)
  have hLinear : Q ≤ Q^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hQ (by omega : 1 ≤ d+1)
  have hRat := Nat.mul_le_mul hN (hFast W)
  have hRate := Nat.mul_le_mul_left (N*(C*(W+1))) hStep
  have hWords := Nat.mul_le_mul (Nat.mul_le_mul_left N (show W ≤ W+1 by omega)) hLinear
  change (n+1)*model.rat W+N*W*Q ≤ (C+1)*N*(W+1)*Q^(d+1)
  change (n+1)*model.rat W ≤ N*(C*(W+1)*Q^d) at hRat
  nlinarith only [hRat,hRate,hWords]

theorem bound_at_profile {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (C d : ℕ) (hFast : ∀ w, model.rat w ≤ C*(w+1)*(binaryWordWidth (w+2)+1)^d)
    (c K h : ℕ) :
    bound i model c K h ≤
      3*h+2^300*(c+1)*(C+1)*(n+K+1)*(width i K+1)*(logFactor i K)^(d+1) := by
  have hh := Nat.mul_le_mul_left (2^300*(c+1))
    (envelope_at_profile model C d hFast n (n+K+1) (width i K) (by omega))
  unfold bound logFactor
  nlinarith only [hh]

theorem accuracy_bound_at_profile {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (C d : ℕ) (hFast : ∀ w, model.rat w ≤ C*(w+1)*(binaryWordWidth (w+2)+1)^d)
    (c k h : ℕ) :
    accuracyBound i model c k h ≤
      3*h+2^300*(c+1)*(C+1)*(n+k+6)*(accuracyWidth i k+1)*
        (binaryWordWidth (accuracyWidth i k+2)+1)^(d+1) := by
  have hh := Nat.mul_le_mul_left (2^300*(c+1))
    (envelope_at_profile model C d hFast n (n+k+6) (accuracyWidth i k) (by omega))
  unfold accuracyBound
  nlinarith only [hh]

theorem work_raw_accuracy {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n a.precision) → Bool) :
    work (NativePRGPreparedSampler.ofInput i a.precision) model primitive c rich bits ≤
      accuracyBound i model c ⌈Real.logb 2 (1/a.real)⌉₊ (NativePRGPreparedSampler.header n).length := by
  have hK : a.precision ≤ ⌈Real.logb 2 (1/a.real)⌉₊+5 := by
    simpa only [a.logExponent_eq_ceil] using a.precision_log_bounds.2
  exact (work_bound (NativePRGPreparedSampler.ofInput i a.precision) model primitive c hPrimitive rich bits).trans
    (bound_accuracy i model c a.precision _ _ hK)

theorem output_length {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    (NativePRGPreparedSampler.output p rich bits).length ≤
      p.bytes.length+2*n*outputWidth p.source p.precision+n := by
  let row := NativePRGPreparedSampler.sample p rich bits
  have hWidth : ∀ q ∈ row.data.toList, rationalWordWidth q ≤ outputWidth p.source p.precision := by
    rw [BinaryNativeRowEncoder.array_list]
    intro q hq
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact sample_width p rich bits j
  have hSum : (row.data.toList.map rationalWordWidth).sum ≤ n*outputWidth p.source p.precision := by
    calc
      _ ≤ (row.data.toList.map (fun _ => outputWidth p.source p.precision)).sum :=
        List.sum_le_sum hWidth
      _ = _ := by simp [row.size]
  have hLength := BinaryNativeRowEncoder.frame_length p.bytes row.data.toList
  change (ReferenceStoredRowFrame.frame p.bytes row).length ≤ _
  rw [ReferenceStoredRowFrame.frame_data]
  change (BinaryNativeRowEncoder.frame p.bytes row.data.toList).length ≤ _
  simp only [Array.length_toList,row.size] at hLength
  nlinarith only [hLength,hSum]

/- The data, hard-budget and cost-observer contracts share the same prepared
descriptor and bit path. The observer prices the listed components above;
this theorem alone does not assert that no further source component exists. -/
theorem observed_draw_contract {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    RationalPRGBinaryRequest.ReturnedBudget n (if rich then p.source.a else p.source.b)
      (NativePRGPreparedSampler.output p rich bits) ∧
    (NativePRGPreparedSampler.output p rich bits).length ≤
      p.bytes.length+2*n*outputWidth p.source p.precision+n ∧
    work p model primitive c rich bits ≤ bound p.source model c p.precision p.bytes.length :=
  ⟨NativePRGPreparedSampler.output_read_budget p rich bits,output_length p rich bits,
    work_bound p model primitive c hPrimitive rich bits⟩

end Blotto.PRGPaperDrawCost
