import Blotto.GeneralPaperStreamingCFSpace

/-! Complete midpoint-query source space: construct the initial pair,
stream the CF registers, retain/test one fraction and return the whole
native result. The caller frame and simultaneous input/output records are
included. Phase maxima are analytical quantities; no trace is stored.
-/
namespace Blotto.GeneralPaperStreamingQuerySpace
open GeneralPaperRegularCFLoop GeneralPaperCFOperandBounds GeneralPaperStreamingCFSpace
set_option autoImplicit false
set_option maxHeartbeats 8000000

def resultFootprint (W : ℕ) (r : GeneralPaperMidpointQuery.Result) : ℕ :=
  selectedFootprint W r.fraction+binaryWordWidth r.work+binaryWordWidth r.steps+
    binaryWordWidth r.quotientDepth+8*W

theorem filtered_selected (W C t : ℕ) (closed : Bool) (s : State) :
    selectedFootprint W (GeneralPaperMidpointFilterBits.filter closed C t s).fraction≤selectedFootprint W s.selected := by
  unfold GeneralPaperMidpointFilterBits.filter
  dsimp only
  cases hs : s.selected with
  | none => simp only [Option.bind_none,le_refl]
  | some f =>
    simp only [Option.bind_some]
    split
    · exact Nat.le_refl _
    · simp only [selectedFootprint]
      omega

theorem selected_space (W lambda N M : ℕ) (s : State) (h : Valid lambda N M s)
    (hN : N<2^lambda) (hM : M<2^lambda) : selectedFootprint W s.selected≤2*(lambda+1)+W := by
  cases he : s.selected with
  | none => simp only [selectedFootprint]; omega
  | some f =>
    have hf := h.selected f he
    have hn := GeneralPaperCFOperandPrice.small_word lambda f.num (hf.1.trans_lt hN)
    have hd := GeneralPaperCFOperandPrice.small_word lambda f.den (hf.2.trans_lt hM)
    simp only [selectedFootprint]
    omega

theorem result_space (W C t lambda N M : ℕ) (closed : Bool) (s : State)
    (h : Valid lambda N M s) (hN : N<2^lambda) (hM : M<2^lambda)
    (hc : Small W s) (hw : binaryWordWidth (s.work+32)≤W) :
    resultFootprint W (GeneralPaperMidpointFilterBits.filter closed C t s)≤2*(lambda+1)+12*W := by
  have hs := (filtered_selected W C t closed s).trans (selected_space W lambda N M s h hN hM)
  have hcs := hc.steps
  have hcd := hc.depth
  unfold resultFootprint
  change _+binaryWordWidth (s.work+32)+binaryWordWidth s.steps+binaryWordWidth s.quotientDepth+8*W≤_
  omega

def filterScratch (model : RationalCostModel) (C t : ℕ) (s : State) : ℕ :=
  match s.selected with
  | none => 0
  | some f => GeneralPaperMidpointFilterBits.operandWork model C t f

theorem filter_scratch (model : RationalCostModel) (D C t lambda : ℕ) (s : State)
    (h : Valid lambda (2*t+1) (2*C) s) (ht : t<C) (hM : 2*C<2^lambda) :
    filterScratch model C t s≤15*model.rat (GeneralPaperCFOperandPrice.width lambda D) := by
  unfold filterScratch
  cases hs : s.selected with
  | none => exact Nat.zero_le _
  | some f =>
    have hf := h.selected f hs
    exact GeneralPaperMidpointFilterBits.operand_work model D C t lambda f ht hM hf.1 hf.2

def filterWindow (model : RationalCostModel) (W C t : ℕ) (closed : Bool) (s : State) : ℕ :=
  footprint W s+resultFootprint W (GeneralPaperMidpointFilterBits.filter closed C t s)+filterScratch model C t s+32*W

theorem filter_space (model : RationalCostModel) (W D C t lambda : ℕ) (closed : Bool)
    (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda)
    (hW : GeneralPaperCFControlWords.width lambda≤W) :
    filterWindow model W C t closed (GeneralPaperMidpointQuery.raw D C t lambda)≤
      512*(W+model.rat (GeneralPaperCFOperandPrice.width lambda D)) := by
  let s := GeneralPaperMidpointQuery.raw D C t lambda
  have hv := midpoint_all_prefixes D C t lambda (2*lambda+4) hC ht hPower
  have hp := GeneralPaperRegularCFFuel.midpoint_pair_bound C t lambda hC ht hPower
  have hc := prefix_small W D C t lambda (2*lambda+4) hD hC ht hPower (by omega) hW
  have hWords := GeneralPaperCFControlWords.prefix_words D C t lambda (2*lambda+4) hD hC ht hPower (by omega)
  have hm := binaryWordWidth_mono (show s.work+32≤s.work+512 by omega)
  have hw : binaryWordWidth (s.work+32)≤W := hm.trans (hWords.2.2.2.trans hW)
  have hs := state_space W lambda (2*t+1) (2*C) s hv hp.1 hp.2 hc
  have hr := result_space W C t lambda (2*t+1) (2*C) closed s hv hp.1 hp.2 hc hw
  have hf := filter_scratch model D C t lambda s hv ht hp.2
  have hP : lambda+1≤model.rat (GeneralPaperCFOperandPrice.width lambda D) :=
    (show lambda+1≤GeneralPaperCFOperandPrice.width lambda D by unfold GeneralPaperCFOperandPrice.width; omega).trans
      (model.word_le _)
  change filterWindow model W C t closed s≤_
  unfold filterWindow
  omega

def frame (W D C t lambda : ℕ) : ℕ :=
  binaryWordWidth D+binaryWordWidth C+binaryWordWidth t+binaryWordWidth lambda+
    binaryWordWidth (2*lambda+4)+32*W

theorem frame_space (model : RationalCostModel) (W D C t lambda : ℕ)
    (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) (hW : GeneralPaperCFControlWords.width lambda≤W) :
    frame W D C t lambda≤64*(W+model.rat (GeneralPaperCFOperandPrice.width lambda D)) := by
  let L := GeneralPaperCFOperandPrice.width lambda D
  let P := model.rat L
  have hp := GeneralPaperRegularCFFuel.midpoint_pair_bound C t lambda hC ht hPower
  have hc := GeneralPaperCFOperandPrice.small_word lambda C (by omega : C<2^lambda)
  have htW := GeneralPaperCFOperandPrice.small_word lambda t (by omega : t<2^lambda)
  have hL : lambda+1≤L := by dsimp [L,GeneralPaperCFOperandPrice.width]; omega
  have hD : binaryWordWidth D≤L := by dsimp [L,GeneralPaperCFOperandPrice.width]; omega
  have hP := model.word_le L
  have hl := GeneralPaperCFControlWords.bounded lambda lambda (by unfold GeneralPaperCFControlWords.cap; omega)
  have hFuel := (GeneralPaperCFControlWords.fuel_words lambda (2*lambda+4) (lambda+2) (by omega) (by omega)).2.2.2
  change _≤64*(W+P)
  unfold frame
  change L≤P at hP
  omega

def initialWindow (model : RationalCostModel) (W C t : ℕ) : ℕ :=
  footprint W (initial C t)+GeneralPaperStreamingMidpointRaw.initialWork model C t+32*W

theorem initial_space (model : RationalCostModel) (W D C t lambda : ℕ)
    (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda)
    (hW : GeneralPaperCFControlWords.width lambda≤W) :
    initialWindow model W C t≤512*(W+model.rat (GeneralPaperCFOperandPrice.width lambda D)) := by
  have hp := GeneralPaperRegularCFFuel.midpoint_pair_bound C t lambda hC ht hPower
  have hc := prefix_small W D C t lambda 0 hD hC ht hPower (by omega) hW
  have hs := state_space W lambda (2*t+1) (2*C) (initial C t) (initial_valid C t lambda hC ht hPower) hp.1 hp.2 hc
  have hi := GeneralPaperStreamingMidpointRaw.initial_work model D C t lambda hC ht hPower
  have hP : lambda+1≤model.rat (GeneralPaperCFOperandPrice.width lambda D) :=
    (show lambda+1≤GeneralPaperCFOperandPrice.width lambda D by unfold GeneralPaperCFOperandPrice.width; omega).trans
      (model.word_le _)
  unfold initialWindow
  omega

def peak (model : RationalCostModel) (W : ℕ) (closed : Bool) (D C t lambda : ℕ) : ℕ :=
  frame W D C t lambda+max (initialWindow model W C t)
    (max (GeneralPaperStreamingCFSpace.peak model W D lambda (2*lambda+4) (initial C t))
      (filterWindow model W C t closed (GeneralPaperMidpointQuery.raw D C t lambda)))

theorem peak_bound (model : RationalCostModel) (W D C t lambda : ℕ) (closed : Bool)
    (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda)
    (hW : GeneralPaperCFControlWords.width lambda≤W) :
    peak model W closed D C t lambda≤1024*(W+model.rat (GeneralPaperCFOperandPrice.width lambda D)) := by
  have hF := frame_space model W D C t lambda hC ht hPower hW
  have hI := initial_space model W D C t lambda hD hC ht hPower hW
  have hRun := GeneralPaperStreamingCFSpace.peak_bound model W D C t lambda hD hC ht hPower hW
    ⟨2*lambda+4,initial C t⟩ .start
  have hQ := filter_space model W D C t lambda closed hD hC ht hPower hW
  unfold peak
  change GeneralPaperStreamingCFSpace.peak model W D lambda (2*lambda+4) (initial C t)≤_ at hRun
  have hm := max_le hI (max_le hRun hQ)
  omega

theorem source (model : RationalCostModel) (m k t : ℕ) (closed : Bool)
    (ht : t<(GeneralPaperProxyParameters.alphabet m k).C) :
    let a := GeneralPaperProxyParameters.alphabet m k
    peak model (GeneralPaperPrecallControlWord.word m k) closed a.D a.C t a.lambda≤
      1024*(GeneralPaperPrecallControlWord.word m k+model.rat (GeneralPaperCFOperandPrice.width a.lambda a.D)) := by
  let a := GeneralPaperProxyParameters.alphabet m k
  exact peak_bound model _ a.D a.C t a.lambda closed a.orderPositive a.scalePositive ht a.dyadic
    (GeneralPaperClassifierCFWords.calibrated m k a.lambda (Or.inr rfl))

theorem root (model : RationalCostModel) (m k t : ℕ) (closed : Bool)
    (ht : t<(GeneralPaperProxyParameters.prepare m k).Qg) :
    let r := GeneralPaperProxyParameters.prepare m k
    peak model (GeneralPaperPrecallControlWord.word m k) closed r.H r.Qg t (r.gridBits+3)≤
      1024*(GeneralPaperPrecallControlWord.word m k+model.rat (GeneralPaperCFOperandPrice.width (r.gridBits+3) r.H)) := by
  let r := GeneralPaperProxyParameters.prepare m k
  exact peak_bound model _ r.H r.Qg t (r.gridBits+3) closed
    (GeneralPaperProxyParameters.H_positive m k) (GeneralPaperProxyParameters.grid_positive m k) ht
    (GeneralPaperProxyClassifier.grid_dyadic m k)
    (GeneralPaperClassifierCFWords.calibrated m k (r.gridBits+3) (Or.inl rfl))

end Blotto.GeneralPaperStreamingQuerySpace
