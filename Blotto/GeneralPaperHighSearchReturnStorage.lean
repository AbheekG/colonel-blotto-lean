import Blotto.GeneralPaperSourceFinalRecoveryRates

/-! Actual high-search branch/return ownership. The input list and active
phase buffers are retained by their preceding contracts. This additional
window owns the complete parametric result, guarded final bracket/label
row, answer time/labels, scalar arguments and native partial-work fields.
Only the actually reached final/recovery calls contribute their counters. -/
namespace Blotto.GeneralPaperHighSearchReturnStorage
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def finishing {m S K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (h : ℕ) (beta : ℚ) (stages : Option (GeneralPaperRayParametricDP.Output S K)) :
    Option GeneralPaperRayCrossingRefinement.Bracket × ℕ :=
  match stages with
  | none => (none,0)
  | some out => GeneralPaperFinalRefinementPrice.bits model W matrix out.table x w h beta out.bracket.lower out.bracket.upper

def recovering {m S K : ℕ} (model : RationalCostModel) (W : ℕ) (h : ℕ) (beta : ℚ)
    (stages : Option (GeneralPaperRayParametricDP.Output S K))
    (final : Option GeneralPaperRayCrossingRefinement.Bracket) : Option (FixedArrayTable m (Fin K)) × ℕ :=
  match stages,final with
  | some out,some b => GeneralPaperHighBlockerPrice.run model.rat (fun w => w) W m out.table h beta b.lower b.upper
  | _,_ => (none,0)

def answerFoot {m K : ℕ} (W : ℕ) : Option (GeneralPaperRayHighSearch.Answer m K) → ℕ
  | none => 32*W
  | some a => rationalWordWidth a.time+GeneralPaperFixedTupleDecodeStorage.rowFoot W (some a.labels)+64*W
def answerProfile (W m K R : ℕ) : ℕ := 1+2*R+GeneralPaperFixedTupleDecodeStorage.rowProfile W m K+64*W

theorem answer_bound {m K : ℕ} (W R : ℕ) (a : Option (GeneralPaperRayHighSearch.Answer m K))
    (ha : ∀ b,a=some b → RationalHeight b.time R) : answerFoot W a≤answerProfile W m K R := by
  cases a with
  | none => dsimp only [answerFoot,answerProfile]; omega
  | some a =>
    have ht := rationalWordWidth_of_height (ha a rfl)
    have hr := GeneralPaperFixedTupleDecodeStorage.row_bound W (some a.labels)
    dsimp only [answerFoot,answerProfile]
    omega

def price (model : RationalCostModel) (W m K S R : ℕ) : ℕ := GeneralPaperHighSearchPriceFacts.profile m S K W (model.rat (6*R+9))
def metadataCap (model : RationalCostModel) (W m K S R : ℕ) : ℕ := m+K+S+1+3*price model W m K S R+24*W

def window {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta lo hi : ℚ) : ℕ :=
  let inputs := GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w
  let stages := GeneralPaperParametricRunBits.run model W matrix x w S h beta inputs.1 lo hi
  let final := finishing model W matrix x w h beta stages.1
  let row := recovering (m:=m) model W h beta stages.1 final.1
  let result := GeneralPaperHighSearchBits.run model W matrix x w S h beta lo hi
  GeneralPaperParametricOutputStorage.outputFoot W stages.1+
    GeneralPaperCrossingRefinementStorage.bracketFoot W final.1+GeneralPaperFixedTupleDecodeStorage.rowFoot W row.1+
    answerFoot W result.1+rationalWordWidth beta+rationalWordWidth lo+rationalWordWidth hi+
    fields W [m,K,S,h,inputs.2,stages.2,final.2,row.2,result.2,inputs.2+stages.2,
      inputs.2+stages.2+final.2,inputs.2+stages.2+final.2+row.2,8*W,16*W,24*W]+384*W

def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperParametricOutputStorage.outputProfile W m K S R+(2*(1+2*R)+64*W)+
    GeneralPaperFixedTupleDecodeStorage.rowProfile W m K+answerProfile W m K R+3*(1+2*R)+
    15*(natBits (metadataCap model W m K S R)+W)+416*W

theorem bounded {m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ)
    (hD : 0<D) (hE : 0<E) (hED : E∣D)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a))
    (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a)) (S h : ℕ) (hhS : h≤S) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (lo hi : ℚ)
    (hLo : 0≤lo) (ho : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth ((S+1)*(K*K)+3)≤W)
    (hFinalIndex : binaryWordWidth (S+4)≤W) :
    window model W matrix x w S h beta lo hi≤profile model W m K S (width D E m X V P) := by
  let R := width D E m X V P
  let inputs := GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w
  let stages := GeneralPaperParametricRunBits.run model W matrix x w S h beta inputs.1 lo hi
  let final := finishing model W matrix x w h beta stages.1
  let row := recovering (m:=m) model W h beta stages.1 final.1
  let result := GeneralPaperHighSearchBits.run model W matrix x w S h beta lo hi
  have hNativeResult : result=(match stages.1 with
      | none => (none,inputs.2+stages.2+8*W)
      | some out =>
        let f := GeneralPaperFinalRefinementPrice.bits model W matrix out.table x w h beta out.bracket.lower out.bracket.upper
        match f.1 with
        | none => (none,inputs.2+stages.2+f.2+16*W)
        | some b =>
          let r := GeneralPaperHighBlockerPrice.run model.rat (fun w => w) W m out.table h beta b.lower b.upper
          (r.1.map (fun labels => ⟨b.lower,labels⟩),inputs.2+stages.2+f.2+r.2+24*W)) := by
    unfold result GeneralPaperHighSearchBits.run GeneralPaperHighSearchPriceControl.run
    dsimp only
    cases hs : stages.1 with
    | none => rfl
    | some out =>
      cases hf : (GeneralPaperFinalRefinementPrice.bits model W matrix out.table x w h beta out.bracket.lower out.bracket.upper).1 <;> rfl
  have hInputs : inputs.1=GeneralPaperRayAffineScoreInput.fields matrix x w := GeneralPaperAffineInputPrice.data _ _ _ _ _
  have hLen : inputs.1.length≤m := by rw [hInputs,GeneralPaperRayAffineScoreInput.fields_length]
  have hFields : ∀ f∈inputs.1,GeneralPaperRayAffineDPSize.FieldBounded D E X V f := by
    rw [hInputs]; exact GeneralPaperRayAnchorBound.fields D E X V matrix x w hx hw
  have hOutput := GeneralPaperParametricOutputStorage.bounded model W D E X V P hD hE matrix x w S h beta inputs.1 hLen hFields lo hi hl hh
  have hFinalHeights : ∀ b,final.1=some b → RationalHeight b.lower R ∧ RationalHeight b.upper R := by
    intro b hf
    cases hs : stages.1 with
    | none => simp only [final,finishing,hs] at hf; contradiction
    | some out =>
      have hn : GeneralPaperRayParametricDP.run (GeneralPaperRayPricedPredicate.query matrix x w S h beta) S
          (GeneralPaperRayAffineScoreInput.fields matrix x w) lo hi=some out := by
        simpa only [stages,GeneralPaperParametricRunBits.data,hInputs] using hs
      have hv := GeneralPaperHighSearchPriceFacts.state D E X V P hD hE matrix x w hx hw h beta lo hi hl hh out hn
      have hf' : GeneralPaperRayFinalBudget.finish matrix out.table x w h beta out.bracket.lower out.bracket.upper=some b := by
        simpa only [final,finishing,hs,GeneralPaperFinalRefinementPrice.bits_data] using hf
      have ht := GeneralPaperRayParametricRunSize.finish hD hE (Nat.le_refl m)
        (GeneralPaperRayPricedPredicate.query matrix x w S h beta) out.table hv.1 h beta out.bracket.lower out.bracket.upper hb hv.2.1 hv.2.2 b hf'
      exact ⟨ht.1,ht.2.1⟩
  have hBracket : GeneralPaperCrossingRefinementStorage.bracketFoot W final.1≤2*(1+2*R)+64*W := by
    cases hf : final.1 with
    | none => simp only [GeneralPaperCrossingRefinementStorage.bracketFoot]; omega
    | some b =>
      have a := rationalWordWidth_of_height (hFinalHeights b hf).1
      have b' := rationalWordWidth_of_height (hFinalHeights b hf).2
      simp only [GeneralPaperCrossingRefinementStorage.bracketFoot]
      omega
  have hAnswer := answer_bound W R result.1 (by
    intro a ha
    rw [hNativeResult] at ha
    cases hs : stages.1 with
    | none => simp only [hs] at ha; contradiction
    | some out =>
      cases hf : final.1 with
      | none =>
        have hf' := hf
        have he : (GeneralPaperFinalRefinementPrice.bits model W matrix out.table x w h beta out.bracket.lower out.bracket.upper).1=none := by simpa only [final,finishing,hs] using hf'
        simp only [hs,he] at ha
        contradiction
      | some b =>
        have ht := (hFinalHeights b hf).1
        have hf' := hf
        have he : (GeneralPaperFinalRefinementPrice.bits model W matrix out.table x w h beta out.bracket.lower out.bracket.upper).1=some b := by simpa only [final,finishing,hs] using hf'
        simp only [hs,he] at ha
        cases hr : (GeneralPaperHighBlockerPrice.run model.rat (fun w => w) W m out.table h beta b.lower b.upper).1 with
        | none => simp only [hr,Option.map_none] at ha; contradiction
        | some labels =>
          simp only [hr,Option.map_some,Option.some.injEq] at ha
          cases ha
          exact ht)
  have hRow := GeneralPaperFixedTupleDecodeStorage.row_bound W row.1
  have hWork := GeneralPaperHighSearchBits.work model W D E X V P hD hE hED matrix x w hx hw S h beta hb lo hi hLo ho hHi hl hh hW hK hM hIndex hBatch hFinalIndex
  change result.2≤price model W m K S R at hWork
  have hSum : inputs.2+stages.2+final.2+row.2≤result.2 := by
    rw [hNativeResult]
    cases hs : stages.1 with
    | none => simp only [final,finishing,row,recovering,hs]; omega
    | some out =>
      dsimp only
      cases hf : (GeneralPaperFinalRefinementPrice.bits model W matrix out.table x w h beta out.bracket.lower out.bracket.upper).1 with
      | none => simp only [final,finishing,row,recovering,hs,hf]; omega
      | some b => simp only [final,finishing,row,recovering,hs,hf]; omega
  have hBeta := rationalWordWidth_of_height (GeneralPaperRayOperandStorageHeight.budget (E:=E) (m:=m) (X:=X) (V:=V) hD hb)
  have hLower := rationalWordWidth_of_height hl
  have hUpper := rationalWordWidth_of_height hh
  have hf := fields_bound W (natBits (metadataCap model W m K S R))
    [m,K,S,h,inputs.2,stages.2,final.2,row.2,result.2,inputs.2+stages.2,
      inputs.2+stages.2+final.2,inputs.2+stages.2+final.2+row.2,8*W,16*W,24*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤15*(natBits (metadataCap model W m K S R)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [R,inputs,stages,final,row,result] at hOutput hBracket hAnswer hRow hf
  omega

end Blotto.GeneralPaperHighSearchReturnStorage
