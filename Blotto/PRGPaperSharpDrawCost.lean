import Blotto.PRGPaperSplitPreparationCost

/-! The appendix separates n rational operations from n+K digit operations.
For the permitted rational majorant that includes binary word traffic, the
same reached-component observer has this sharper form. This is a source
cost-model theorem, with no claim about native allocation or library costs. -/

namespace Blotto.PRGPaperSharpDrawCost
open PRGPaperDrawCost
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 512

theorem logFactor_le_width {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    logFactor i K ≤ width i K := by
  let S := i.originalInputWordWidth+K+6
  have hWide : width i K+2 ≤ 2^91*S := by
    dsimp [width,RationalPRGLinearFramingWork.uniformWidth,S]
    omega
  have hLog := (binaryWordWidth_mono hWide).trans (binaryWordWidth_mul (2^91) S)
  have hConst : binaryWordWidth (2^91) = 92 := by decide
  rw [hConst] at hLog
  have hSmall := Nat.log2_le_self S
  unfold logFactor
  dsimp [width,RationalPRGLinearFramingWork.uniformWidth,S] at *
  unfold binaryWordWidth at hLog ⊢
  omega

theorem route_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K : ℕ) :
    RationalPRGReferenceRouteCost.bound c n (3+i.originalInputWordWidth) ≤
      1024*(c+1)*(n+1)*model.withWordTraffic.rat (width i K) := by
  have hOld := route_bound_fast i c 0
  have hW : width i 0 ≤ width i K := by
    unfold width RationalPRGLinearFramingWork.uniformWidth
    omega
  have hQ : logFactor i 0 ≤ logFactor i K :=
    Nat.add_le_add_right (binaryWordWidth_mono (Nat.add_le_add_right hW 2)) 1
  have hMove := Nat.mul_le_mul_left (1024*(c+1)*(n+1)) (Nat.mul_le_mul hW hQ)
  have hTraffic : width i K*logFactor i K ≤ model.withWordTraffic.rat (width i K) :=
    Nat.le_add_left _ _
  have hPay := Nat.mul_le_mul_left (1024*(c+1)*(n+1)) hTraffic
  simp only [Nat.add_zero] at hOld
  nlinarith only [hOld,hMove,hPay]

theorem formatting_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (header : List Bool) (c K : ℕ) :
    ReferenceStoredRowFrame.bound header c n (outputWidth i K) ≤
      3*header.length+4096*(c+1)*(n+1)*model.withWordTraffic.rat (width i K) := by
  let W := width i K
  let Q := logFactor i K
  let N := n+1
  let B := N*W*Q
  have hf := width_facts i K
  have hQ : 1 ≤ Q := by dsimp [Q,logFactor]; omega
  have hRect := rectangle N W Q (by dsimp [N]; omega) hf.1 hQ
  have hNW : n+1 ≤ W := (show n+1 ≤ n+K+1 by omega).trans hf.2.1
  have h1 := binaryWordWidth_mono (show n+1 ≤ W+2 by omega)
  have h2 := binaryWordWidth_mono (show outputWidth i K+1 ≤ W+2 by have h := hf.2.2.1; omega)
  have ha := StoredArrayReferenceList.poolAddressWidth_log_bound n (outputWidth i K)
  have hA : StoredArrayReferenceList.poolAddressWidth n (outputWidth i K)+1 ≤ 2*Q := by
    change _ ≤ 2*(binaryWordWidth (W+2)+1)
    omega
  have hQOut : binaryWordWidth (outputWidth i K+2)+1 ≤ Q := by
    apply Nat.add_le_add_right
    apply binaryWordWidth_mono
    have h := hf.2.2.1
    omega
  have hRef := Nat.mul_le_mul_left (5*c+6) (Nat.mul_le_mul (Nat.le_refl N) hA)
  have hNQPrice := Nat.mul_le_mul_left (10*c+12) hRect.2.2.1
  have hRefBound : (5*c+6)*(n+1)*(StoredArrayReferenceList.poolAddressWidth n (outputWidth i K)+1) ≤
      (10*c+12)*B := by dsimp only [B,N] at *; nlinarith only [hRef,hNQPrice]
  have hOut := Nat.mul_le_mul (Nat.mul_le_mul (show n ≤ N by dsimp [N]; omega) hf.2.2.1) hQOut
  have hOutPrice : 1024*(c+1)*(n*(outputWidth i K+1)*(binaryWordWidth (outputWidth i K+2)+1)) ≤
      1024*(c+1)*B := Nat.mul_le_mul_left (1024*(c+1)) hOut
  have hnB : n ≤ B := (show n ≤ W by omega).trans hRect.2.1
  have hB : 1 ≤ B := hRect.1
  have hCoeff := Nat.mul_le_mul_right B (show 1034*c+1043 ≤ 4096*(c+1) by omega)
  have hTraffic : W*Q ≤ model.withWordTraffic.rat W := Nat.le_add_left _ _
  have hPay := Nat.mul_le_mul_left (4096*(c+1)*N) hTraffic
  unfold ReferenceStoredRowFrame.bound
  dsimp only [B,N] at hRefBound hOutPrice hnB hB hCoeff hPay ⊢
  nlinarith only [hRefBound,hOutPrice,hnB,hB,hCoeff,hPay]

theorem group_bound {n : ℕ} (i : RationalPRGOriginalInput n) (c K : ℕ) :
    RationalTerminalLotto.groupTableConstructionBound c n (3+i.originalInputWordWidth) ≤
      256*(c+1)*(n+K+1)*width i K := by
  let W := width i K
  let N := n+K+1
  let B := N*W
  have hf := width_facts i K
  have hQ := logFactor_le_width i K
  have hRect := rectangle N W 1 (by dsimp [N]; omega) hf.1 (by omega)
  simp only [Nat.mul_one] at hRect
  have hWidth : binaryWordWidth (n+4) ≤ W :=
    ((binaryWordWidth_mono hf.2.2.2.2.2.2).trans (Nat.le_succ _)).trans hQ
  have hIndex := Nat.mul_le_mul_left n hWidth
  have hnW : n*W ≤ B := Nat.mul_le_mul_right W (by dsimp [N]; omega)
  have hs : 3+i.originalInputWordWidth ≤ B := hf.2.2.2.1.trans hRect.2.1
  have hConst := Nat.mul_le_mul_left (132+36*c) hRect.1
  have hCoeff := Nat.mul_le_mul_right B (show 186+36*c ≤ 256*(c+1) by omega)
  have hFour : binaryWordWidth 4 = 3 := by decide
  calc
    _ ≤ 256*(c+1)*B := by
      unfold RationalTerminalLotto.groupTableConstructionBound RationalTerminalLotto.groupEntryPayloadWidth
        indexedLoopMetadataBound
      rw [hFour]
      nlinarith only [hIndex,hnW,hs,hConst,hCoeff]
    _ = _ := by dsimp only [B,N,W]; ring

theorem seed_bound {n : ℕ} (i : RationalPRGOriginalInput n) (c K : ℕ) :
    seedBound c (RationalLottoResourceSystem.sampleBitBudget n K) ≤
      100000*(c+1)*(n+K+1)*width i K := by
  let R := RationalLottoResourceSystem.sampleBitBudget n K
  let N := n+K+1
  let W := width i K
  have hf := width_facts i K
  have hR : R+1 ≤ 3008*N := by dsimp [R,N]; rw [RationalLottoResourceSystem.sampleBitBudget_eq]; omega
  have hLog : binaryWordWidth (R+1)+1 ≤ W := by
    apply le_trans (b := logFactor i K)
    · apply Nat.add_le_add_right
      apply binaryWordWidth_mono
      have h := hf.2.2.2.2.1
      omega
    · exact logFactor_le_width i K
  have hs := seed_bound_fast c R
  have hm := Nat.mul_le_mul_left (10*c+20) (Nat.mul_le_mul hR hLog)
  have hc := Nat.mul_le_mul_right (N*W) (show 3008*(10*c+20) ≤ 100000*(c+1) by omega)
  calc
    _ ≤ 100000*(c+1)*(N*W) := by nlinarith only [hs,hm,hc]
    _ = _ := by dsimp only [N,W]; ring

def bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K h : ℕ) : ℕ :=
  3*h+2^300*(c+1)*((n+1)*model.withWordTraffic.rat (width i K)+(n+K+1)*width i K)

theorem work_bound {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    work p model primitive c rich bits ≤ bound p.source model c p.precision p.bytes.length := by
  let i := p.source
  let K := p.precision
  let W := width i K
  let N := n+K+1
  let P := model.withWordTraffic.rat W
  let B := N*W
  let Z := (n+1)*P+B
  have hf := width_facts i K
  have hQ := logFactor_le_width i K
  have hS : i.originalInputWordWidth+K+6 ≤ W := by
    dsimp [W,width,RationalPRGLinearFramingWork.uniformWidth]
    omega
  have hMeta := RationalPRGSourceMetadataEnvelope.work_fast i primitive c hPrimitive rich K bits
  have hMetaB := Nat.mul_le_mul_left (2^256*(c+1)) (Nat.mul_le_mul_left N hS)
  have hRoute := (i.selectedRouteReferenceWork_bound primitive c hPrimitive rich K bits).trans
    (route_bound i model c K)
  have hPackWidth : binaryWordWidth (n+4) ≤ logFactor i K :=
    (binaryWordWidth_mono hf.2.2.2.2.2.2).trans (Nat.le_succ _)
  have hPack := (packing_work_bound i primitive c hPrimitive rich K bits).trans
    (packing_bound_fast c n (logFactor i K) (by unfold logFactor; omega) hPackWidth)
  have hPackB := Nat.mul_le_mul_left (128*(c+1))
    (Nat.mul_le_mul (show n+1 ≤ N by dsimp [N]; omega) hQ)
  have hGroup := (i.selectedGroupTableConstructionWork_bound_of_inputWidth primitive c hPrimitive
    (3+i.originalInputWordWidth) le_rfl rich K bits).trans (group_bound i c K)
  have hFrame := (ReferenceStoredRowFrame.work_bound primitive c hPrimitive p.bytes
    (NativePRGPreparedSampler.sample p rich bits) (outputWidth i K) (sample_width p rich bits)).trans
      (formatting_bound i model p.bytes c K)
  have hSeed := (seed_work_bound primitive c hPrimitive
    (RationalLottoResourceSystem.sampleBitBudget n K) bits).trans (seed_bound i c K)
  have hArith := arithmetic_work_bound i model primitive c hPrimitive rich K bits
  have hRat : model.rat W ≤ P := Nat.le_add_right _ _
  have hPay := Nat.mul_le_mul_left (1000000000*(c+1))
    (Nat.add_le_add_right (Nat.mul_le_mul_left (n+1) hRat) B)
  have hBZ : B ≤ Z := Nat.le_add_left _ _
  have hPZ : (n+1)*P ≤ Z := Nat.le_add_right _ _
  have hOther := Nat.mul_le_mul_left ((2^256+128+256+100000)*(c+1)) hBZ
  have hRefs := Nat.mul_le_mul_left ((1024+4096)*(c+1)) hPZ
  have hCoeff := Nat.mul_le_mul_right ((c+1)*Z)
    (show 1000000000+2^256+128+256+100000+1024+4096 ≤ 2^300 by decide)
  unfold work bound RationalPRGSharpArithmeticLedger.sharpBound at *
  dsimp only [i,K,W,N,P,B,Z,width] at hMeta hMetaB hRoute hPack hPackB hGroup hFrame hSeed hArith hPay hOther hRefs hCoeff ⊢
  norm_num only [Nat.reducePow] at hMeta hMetaB hOther hCoeff ⊢
  nlinarith only [hMeta,hMetaB,hRoute,hPack,hPackB,hGroup,hFrame,hSeed,hArith,hPay,hOther,hRefs,hCoeff]

def accuracyBound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c k h : ℕ) : ℕ :=
  let V := PRGPaperDrawCost.accuracyWidth i k
  3*h+2^300*(c+1)*((n+1)*model.withWordTraffic.rat V+(n+k+6)*V)

theorem bound_accuracy {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (c K k h : ℕ) (hK : K ≤ k+5) : bound i model c K h ≤ accuracyBound i model c k h := by
  have hW : width i K ≤ PRGPaperDrawCost.accuracyWidth i k := by
    unfold width RationalPRGLinearFramingWork.uniformWidth PRGPaperDrawCost.accuracyWidth
    exact Nat.mul_le_mul_left (2^90) (by omega)
  have hRat := Nat.mul_le_mul_left (n+1) (model.withWordTraffic.monotone hW)
  have hWords := Nat.mul_le_mul (show n+K+1 ≤ n+k+6 by omega) hW
  exact Nat.add_le_add_left (Nat.mul_le_mul_left (2^300*(c+1))
    (Nat.add_le_add hRat hWords)) (3*h)

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

theorem sharp_envelope_profile (model : RationalCostModel) (C d : ℕ)
    (hFast : ∀ w, model.rat w ≤ C*(w+1)*(binaryWordWidth (w+2)+1)^d)
    (n N W : ℕ) (hN : n+1 ≤ N) :
    (n+1)*model.withWordTraffic.rat W+N*W ≤
      (C+2)*N*(W+1)*(binaryWordWidth (W+2)+1)^(d+1) := by
  let Q := binaryWordWidth (W+2)+1
  have hQ : 0 < Q := by dsimp only [Q]; omega
  have hPow : 1 ≤ Q^(d+1) := Nat.one_le_pow _ _ hQ
  have hRat := Nat.mul_le_mul hN (model.withWordTraffic_fast C d hFast W)
  have hWords := Nat.mul_le_mul (Nat.mul_le_mul_left N (show W ≤ W+1 by omega)) hPow
  change (n+1)*model.withWordTraffic.rat W ≤ N*((C+1)*(W+1)*Q^(d+1)) at hRat
  change _ ≤ (C+2)*N*(W+1)*Q^(d+1)
  simp only [Nat.mul_one] at hWords
  nlinarith only [hRat,hWords]

theorem accuracy_profile_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (C d : ℕ) (hFast : ∀ w, model.rat w ≤ C*(w+1)*(binaryWordWidth (w+2)+1)^d)
    (c k h : ℕ) :
    accuracyBound i model c k h ≤
      3*h+2^300*(c+1)*(C+2)*(n+k+6)*(PRGPaperDrawCost.accuracyWidth i k+1)*
        (binaryWordWidth (PRGPaperDrawCost.accuracyWidth i k+2)+1)^(d+1) := by
  have hh := Nat.mul_le_mul_left (2^300*(c+1))
    (sharp_envelope_profile model C d hFast n (n+k+6) (PRGPaperDrawCost.accuracyWidth i k) (by omega))
  unfold accuracyBound
  nlinarith only [hh]

/- These clauses concern the same original game, precision and bit paths.
Source execution coverage beyond the listed cost observer is separate. -/
theorem original_contract {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) :
    regret i.realValues (i.a:ℝ) (i.storedRichLaw a.precision) (i.storedPoorLaw a.precision) < a.real ∧
    regret i.realValues (i.b:ℝ) (i.storedPoorLaw a.precision) (i.storedRichLaw a.precision) < a.real ∧
    RationalLottoResourceSystem.sampleBitBudget n a.precision ≤
      3*n+5*⌈Real.logb 2 (1/a.real)⌉₊+3025 ∧
    ∀ rich (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n a.precision) → Bool),
      RationalPRGBinaryRequest.ReturnedBudget n (if rich then i.a else i.b)
        (NativePRGPreparedSampler.output (NativePRGPreparedSampler.ofInput i a.precision) rich bits) ∧
      work (NativePRGPreparedSampler.ofInput i a.precision) model primitive c rich bits ≤
        accuracyBound i model c ⌈Real.logb 2 (1/a.real)⌉₊ (NativePRGPreparedSampler.header n).length := by
  have hRegret := NativePRGPreparedSampler.prepared_accuracy_regrets i a
  refine ⟨hRegret.1,hRegret.2,a.sampleBitBudget_ceil_bound n,?_⟩
  intro rich bits
  exact ⟨NativePRGPreparedSampler.output_read_budget (NativePRGPreparedSampler.ofInput i a.precision) rich bits,
    work_raw_accuracy i a model primitive c hPrimitive rich bits⟩

end Blotto.PRGPaperSharpDrawCost
