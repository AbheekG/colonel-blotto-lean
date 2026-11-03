import Blotto.GeneralPaperSourceHighSearchReturnReachedRates

/-! Native static-or-high endpoint branch/return storage. Full blocker
descriptors, reduced times, guarded high answers and native partial-price
fields are owned. Previous contracts own scan/probe/high active buffers.
Skipped calls have zero counters; no runtime observer is introduced. -/
namespace Blotto.GeneralPaperEndpointReturnStorage
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperRayUniformSize
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def probe {T m K : ℕ} (query : ℚ → Bool×ℕ)
    (a : Option (GeneralPaperRayMinimum.Choice (StaticIndex T m K))) : Bool×ℕ :=
  match a with
  | none => (false,0)
  | some c => query c.time

def highResult {T m K : ℕ} (query : ℚ → Bool×ℕ) (high : GeneralPaperEndpointPriceControl.High m K)
    (a : Option (GeneralPaperRayMinimum.Choice (StaticIndex T m K))) :
    Option (GeneralPaperRayHighSearch.Answer m K)×ℕ :=
  match a with
  | none => (none,0)
  | some c => if (query c.time).1=true then (none,0) else high 0 c.time

def descriptorFoot {T m K : ℕ} (W : ℕ) : GeneralPaperRayBlockerRows.Descriptor T m K → ℕ
  | .inl i => GeneralPaperNativeStaticScanStorage.indexFoot W i+8*W
  | .inr row => GeneralPaperFixedTupleDecodeStorage.rowFoot W (some row)+8*W
def answerFoot {T m K : ℕ} (W : ℕ) : Option (GeneralPaperRayEndpoint.Answer T m K) → ℕ
  | none => 32*W
  | some a => rationalWordWidth a.time+descriptorFoot W a.blocker+64*W

theorem static_answer_bound {T m K : ℕ} (W : ℕ) (c : GeneralPaperRayMinimum.Choice (StaticIndex T m K)) :
    answerFoot W (some ⟨c.time,.inl c.blocker⟩)≤
      GeneralPaperStaticChoiceStorage.choiceFoot W (GeneralPaperNativeStaticScanStorage.indexFoot W) (some c)+40*W := by
  dsimp only [answerFoot,descriptorFoot,GeneralPaperStaticChoiceStorage.choiceFoot]
  omega

theorem high_answer_bound {T m K : ℕ} (W : ℕ) (a : Option (GeneralPaperRayHighSearch.Answer m K)) :
    answerFoot (T:=T) W (a.map (fun b => ⟨b.time,.inr b.labels⟩))≤GeneralPaperHighSearchReturnStorage.answerFoot W a+8*W := by
  cases a <;> dsimp only [Option.map_none,Option.map_some,answerFoot,descriptorFoot,GeneralPaperHighSearchReturnStorage.answerFoot] <;> omega

def price (model : RationalCostModel) (W T m K S R : ℕ) : ℕ :=
  GeneralPaperEndpointPriceControl.profile T m K S W (model.rat (6*R+9))
def metadataCap (model : RationalCostModel) (W T m K S R : ℕ) : ℕ := T+m+K+S+1+3*price model W T m K S R+32*W

def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ) : ℕ :=
  let static := GeneralPaperStaticScanPrice.run model.rat W labels x w
  let query := GeneralPaperRayPredicateBits.run model W matrix x w S h beta
  let accepted := probe query static.choice
  let high := highResult query (GeneralPaperHighSearchBits.run model W matrix x w S h beta) static.choice
  let result := GeneralPaperEndpointBits.run model W labels matrix S h beta x w
  GeneralPaperStaticChoiceStorage.choiceFoot W (GeneralPaperNativeStaticScanStorage.indexFoot W) static.choice+
    GeneralPaperHighSearchReturnStorage.answerFoot W high.1+answerFoot W result.1+rationalWordWidth beta+
    fields W [T,m,K,S,h,static.work,accepted.2,high.2,result.2,static.work+accepted.2,
      static.work+accepted.2+high.2,if accepted.1 then 1 else 0,8*W,16*W,32*W]+384*W

def profile (model : RationalCostModel) (W T m K S R : ℕ) : ℕ :=
  2*GeneralPaperStaticChoiceStorage.choiceProfile W (GeneralPaperNativeStaticScanStorage.indexProfile W T m K) R+
    2*GeneralPaperHighSearchReturnStorage.profile model W m K S R+(1+2*R)+
      15*(natBits (metadataCap model W T m K S R)+W)+496*W

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ)
    (hD : 0<D) (hE : 0<E) (hED : E∣D) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (hhS : h≤S) (beta : ℚ)
    (x w : Variable m K → ℚ) (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a))
    (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a)) (hb : GeneralPaperRayRationalBound.Bounded D P beta)
    (hStart : GeneralPaperAffineConstraintRows.Feasible labels (GeneralPaperRayQueryWork.scores matrix) h
      (beta:ℝ) (fun a => (x a:ℝ))) (next : Variable m K) (hVelocity : w next=1)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth ((S+1)*(K*K)+3)≤W)
    (hFinalIndex : binaryWordWidth (S+4)≤W) :
    window model W labels matrix S h beta x w≤profile model W T m K S (width D E m X V P) := by
  let R := width D E m X V P
  let static := GeneralPaperStaticScanPrice.run model.rat W labels x w
  let query := GeneralPaperRayPredicateBits.run model W matrix x w S h beta
  let accepted := probe query static.choice
  let high := highResult query (GeneralPaperHighSearchBits.run model W matrix x w S h beta) static.choice
  let result := GeneralPaperEndpointBits.run model W labels matrix S h beta x w
  have hm : 0<m := Nat.zero_lt_of_lt next.1.isLt
  have hStatic := GeneralPaperStaticChoiceStorage.choice_bound W
    (GeneralPaperNativeStaticScanStorage.indexProfile W T m K) R (GeneralPaperNativeStaticScanStorage.indexFoot W) static.choice (by
      intro c hc
      exact ⟨GeneralPaperNativeStaticScanStorage.index_bound W c.blocker,
        GeneralPaperEndpointPriceFacts.static_height model.rat W D E X V P hm hD hE labels matrix x w hx hw h beta hb c hc⟩)
  have hHighNative : ∀ c,static.choice=some c →
      GeneralPaperHighSearchReturnStorage.answerFoot W (GeneralPaperHighSearchBits.run model W matrix x w S h beta 0 c.time).1≤
        GeneralPaperHighSearchReturnStorage.profile model W m K S R := by
    intro c hc
    have ht := GeneralPaperEndpointPriceFacts.static_height model.rat W D E X V P hm hD hE labels matrix x w hx hw h beta hb c hc
    have hi := GeneralPaperEndpointPriceFacts.static_interval model.rat W labels matrix h beta x w hStart next hVelocity c hc
    have hNative := GeneralPaperHighSearchReturnStorage.bounded model W D E X V P hD hE hED matrix x w hx hw S h hhS beta hb
      0 c.time le_rfl hi.1 hi.2 (GeneralPaperEndpointPriceFacts.zero_height D E m X V P) ht hW hK hM hIndex hBatch hFinalIndex
    apply le_trans (b:=GeneralPaperHighSearchReturnStorage.window model W matrix x w S h beta 0 c.time) _ hNative
    unfold GeneralPaperHighSearchReturnStorage.window
    dsimp only
    omega
  have hHigh : GeneralPaperHighSearchReturnStorage.answerFoot W high.1≤GeneralPaperHighSearchReturnStorage.profile model W m K S R := by
    cases hs : static.choice with
    | none =>
      simp only [high,highResult,hs,GeneralPaperHighSearchReturnStorage.answerFoot]
      unfold GeneralPaperHighSearchReturnStorage.profile
      omega
    | some c =>
      by_cases ha : (query c.time).1=true
      · simp only [high,highResult,hs,ha,ite_true,GeneralPaperHighSearchReturnStorage.answerFoot]
        unfold GeneralPaperHighSearchReturnStorage.profile
        omega
      · simpa only [high,highResult,hs,ha,Bool.false_eq_true,ite_false] using hHighNative c hs
  have hNativeResult : result=(match static.choice with
      | none => (none,static.work+8*W)
      | some c =>
        if (query c.time).1=true then
          (some ⟨c.time,.inl c.blocker⟩,static.work+(query c.time).2+16*W)
        else
          let a := GeneralPaperHighSearchBits.run model W matrix x w S h beta 0 c.time
          (a.1.map (fun b => ⟨b.time,.inr b.labels⟩),static.work+(query c.time).2+a.2+32*W)) := by
    unfold result GeneralPaperEndpointBits.run GeneralPaperEndpointPriceControl.run
    cases static.choice <;> rfl
  have hAnswer : answerFoot W result.1≤
      GeneralPaperStaticChoiceStorage.choiceProfile W (GeneralPaperNativeStaticScanStorage.indexProfile W T m K) R+
        GeneralPaperHighSearchReturnStorage.profile model W m K S R+80*W := by
    rw [hNativeResult]
    cases hs : static.choice with
    | none => dsimp only [answerFoot]; omega
    | some c =>
      dsimp only
      by_cases ha : (query c.time).1=true
      · simp only [ha,ite_true]
        have hp := static_answer_bound W c
        rw [hs] at hStatic
        omega
      · simp only [ha,Bool.false_eq_true,ite_false]
        have hp := high_answer_bound (T:=T) W (GeneralPaperHighSearchBits.run model W matrix x w S h beta 0 c.time).1
        have hn := hHighNative c hs
        omega
  have hWork := GeneralPaperEndpointBits.work model W D E X V P hD hE hED labels matrix S h beta x w hx hw hb hStart next hVelocity
    hW hK hM hIndex hBatch hFinalIndex
  change result.2≤price model W T m K S R at hWork
  have hSum : static.work+accepted.2+high.2≤result.2 := by
    rw [hNativeResult]
    cases hs : static.choice with
    | none => simp only [accepted,probe,high,highResult,hs]; omega
    | some c =>
      dsimp only
      by_cases ha : (query c.time).1=true
      · simp only [accepted,probe,high,highResult,hs,ha,ite_true]; omega
      · simp only [accepted,probe,high,highResult,hs,ha,Bool.false_eq_true,ite_false]; omega
  have hBool : (if accepted.1 then 1 else 0)≤1 := by split <;> omega
  have hf := fields_bound W (natBits (metadataCap model W T m K S R))
    [T,m,K,S,h,static.work,accepted.2,high.2,result.2,static.work+accepted.2,
      static.work+accepted.2+high.2,if accepted.1 then 1 else 0,8*W,16*W,32*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤15*(natBits (metadataCap model W T m K S R)+W)+32*W at hf
  have hBeta := rationalWordWidth_of_height (GeneralPaperRayOperandStorageHeight.budget (E:=E) (m:=m) (X:=X) (V:=V) hD hb)
  unfold window profile
  dsimp only
  dsimp only [R,static,query,accepted,high,result] at hStatic hHigh hAnswer hf
  omega

end Blotto.GeneralPaperEndpointReturnStorage
