import Blotto.GeneralPaperRankArrayPrice
import Blotto.GeneralPaperEncodedScalarStorage

/-! Native rank-search frames retain actual bounded indices, full code
comparands, midpoint/work records and return annotations. The summary array
is borrowed. Fuel controls this single selected path; no source/summary
scan or trace is introduced. -/
namespace Blotto.GeneralPaperRankTraversalStorage
open GeneralPaperEncodedScalarStorage GeneralPaperRankOperands
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def resultBits (W : ℕ) (r : GeneralPaperRankSearch.Result) : ℕ :=
  natBits r.rank+natBits r.work+natBits r.probes+64*W

def frame {n : ℕ} (W : ℕ) (values : FixedArrayTable n ℕ) (cut depth fuel lo hi : ℕ) : ℕ :=
  let mid := GeneralPaperRankMidpoint.midpoint depth lo hi
  let read := if h : mid.quotient<n then values.read ⟨mid.quotient,h⟩ else 0
  fields W [n,cut,depth,fuel,lo,hi,mid.quotient,mid.work,read]+
    resultBits W (GeneralPaperRankSearch.run values cut depth fuel lo hi)+256*W

def peak {n : ℕ} (W : ℕ) (values : FixedArrayTable n ℕ) (cut depth : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,lo,hi => frame W values cut depth 0 lo hi
  | fuel+1,lo,hi =>
    frame W values cut depth (fuel+1) lo hi+
      if lo<hi then
        let mid := GeneralPaperRankMidpoint.midpoint depth lo hi
        if h : mid.quotient<n then
          if values.read ⟨mid.quotient,h⟩<cut then peak W values cut depth fuel (mid.quotient+1) hi
          else peak W values cut depth fuel lo mid.quotient
        else 0
      else 0

theorem result_bound {n : ℕ} (W depth V fuel lo hi cut : ℕ) (values : FixedArrayTable n ℕ)
    (hf : fuel≤depth) (ho : lo≤hi) (hh : hi≤n) (hn : n<2^depth) :
    resultBits W (GeneralPaperRankSearch.run values cut depth fuel lo hi)≤3*width depth V+64*W := by
  have hRank := GeneralPaperRankReturnPrice.rank_le_hi values cut depth fuel lo hi ho hh hn
  have hWork := GeneralPaperRankSearch.run_work values cut depth fuel lo hi
  have hProbes := GeneralPaperRankSearch.run_probes values cut depth fuel lo hi
  have hp := Nat.mul_le_mul_right (12*depth+34) hf
  have hN := basic n depth V
  have hw := word_bound n depth V hn
  have a := binaryWordWidth_mono (show (GeneralPaperRankSearch.run values cut depth fuel lo hi).rank≤magnitude n depth V by omega)
  have b := binaryWordWidth_mono (show (GeneralPaperRankSearch.run values cut depth fuel lo hi).work≤magnitude n depth V by
    have h0 : depth*(12*depth+34)+8≤64*(depth+1)^2 := by nlinarith only [Nat.zero_le depth]
    omega)
  have c := binaryWordWidth_mono (show (GeneralPaperRankSearch.run values cut depth fuel lo hi).probes≤magnitude n depth V by omega)
  unfold resultBits natBits
  omega

theorem frame_bound {n : ℕ} (W depth V fuel lo hi cut : ℕ) (values : FixedArrayTable n ℕ)
    (hf : fuel≤depth) (ho : lo≤hi) (hh : hi≤n) (hn : n<2^depth)
    (hc : cut≤V) (hv : ∀ i,values.read i≤V) :
    frame W values cut depth fuel lo hi≤32*width depth V+512*W := by
  let N := magnitude n depth V
  have hN := basic n depth V
  have hMid := GeneralPaperRankMidpoint.midpoint_bounds n depth lo hi ho hh hn
  have hMidWork := GeneralPaperRankMidpoint.midpoint_work depth lo hi
  have hMidCap : 12*depth+2≤64*(depth+1)^2 := by nlinarith only [Nat.zero_le depth]
  have hWork := GeneralPaperRankSearch.run_work values cut depth fuel lo hi
  have hProbes := GeneralPaperRankSearch.run_probes values cut depth fuel lo hi
  have hRank := GeneralPaperRankReturnPrice.rank_le_hi values cut depth fuel lo hi ho hh hn
  have hprod := Nat.mul_le_mul_right (12*depth+34) hf
  have h0 : depth*(12*depth+34)+8≤64*(depth+1)^2 := by nlinarith only [Nat.zero_le depth]
  have hw := word_bound n depth V hn
  have w (a : ℕ) (ha : a≤N) : natBits a≤width depth V :=
    (Nat.add_le_add_left (binaryWordWidth_mono ha) 1).trans hw
  have hRead : (if h : (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient<n then
      values.read ⟨(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient,h⟩ else 0)≤N := by
    split
    · exact (hv _).trans hN.2.1
    · omega
  have hFields := fields_bound W (width depth V)
    [n,cut,depth,fuel,lo,hi,(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient,
      (GeneralPaperRankMidpoint.midpoint depth lo hi).work,
      if h : (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient<n then
        values.read ⟨(GeneralPaperRankMidpoint.midpoint depth lo hi).quotient,h⟩ else 0] (by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with ha|ha|ha|ha|ha|ha|ha|ha|ha <;> subst a <;> apply w <;> dsimp only [N] <;> omega)
  have a := w _ (by dsimp only [N]; omega : (GeneralPaperRankSearch.run values cut depth fuel lo hi).rank≤N)
  have b := w _ (by dsimp only [N]; omega : (GeneralPaperRankSearch.run values cut depth fuel lo hi).work≤N)
  have c := w _ (by dsimp only [N]; omega : (GeneralPaperRankSearch.run values cut depth fuel lo hi).probes≤N)
  unfold frame resultBits
  dsimp only
  dsimp only [List.length_cons,List.length_nil] at hFields
  omega

theorem bounded {n : ℕ} (W depth V fuel lo hi cut : ℕ) (values : FixedArrayTable n ℕ)
    (hf : fuel≤depth) (ho : lo≤hi) (hh : hi≤n) (hn : n<2^depth)
    (hc : cut≤V) (hv : ∀ i,values.read i≤V) :
    peak W values cut depth fuel lo hi≤(fuel+1)*(32*width depth V+512*W) := by
  induction fuel generalizing lo hi with
  | zero => simpa only [peak,Nat.zero_add,one_mul] using frame_bound W depth V 0 lo hi cut values hf ho hh hn hc hv
  | succ fuel ih =>
    have hFrame := frame_bound W depth V (fuel+1) lo hi cut values hf ho hh hn hc hv
    rw [peak]
    split
    · rename_i hOpen
      have hm := GeneralPaperRankMidpoint.midpoint_inside n depth lo hi hOpen hh hn
      have hIndex : (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient<n := hm.2.trans_le hh
      simp only [hIndex,dite_true]
      split
      · have hChild := ih ((GeneralPaperRankMidpoint.midpoint depth lo hi).quotient+1) hi (by omega) (by omega) hh
        exact (Nat.add_le_add hFrame hChild).trans_eq (by ring)
      · have hChild := ih lo (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient (by omega) hm.1 (by omega)
        exact (Nat.add_le_add hFrame hChild).trans_eq (by ring)
    · nlinarith only [hFrame,Nat.zero_le fuel]

def lookupBits {n : ℕ} (W : ℕ) (r : GeneralPaperRankLookupPrice.Lookup n) : ℕ :=
  natBits r.position.val+natBits r.work+natBits r.probes+64*W

theorem lookup_bound {n : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W depth V : ℕ)
    (values : FixedArrayTable n ℕ) (cut : ℕ) (hn : n<2^depth) :
    lookupBits W (GeneralPaperRankLookupPrice.run bits primitive W depth values cut).1≤3*width depth V+64*W := by
  rw [GeneralPaperRankLookupPrice.data bits primitive W depth values cut hn]
  have hw := word_bound n depth V hn
  have hN := basic n depth V
  have hWork := GeneralPaperRankSearch.run_work values cut depth depth 0 n
  have hProbes := GeneralPaperRankSearch.run_probes values cut depth depth 0 n
  have hWorkN : (GeneralPaperRankSearch.run values cut depth depth 0 n).work+8≤magnitude n depth V := by
    have h : depth*(12*depth+34)+16≤64*(depth+1)^2 := by nlinarith only [Nat.zero_le depth]
    omega
  have a := binaryWordWidth_mono (show min (GeneralPaperRankSearch.run values cut depth depth 0 n).rank n≤magnitude n depth V from
    (Nat.min_le_right ..).trans hN.1)
  have b := binaryWordWidth_mono hWorkN
  have c := binaryWordWidth_mono (show (GeneralPaperRankSearch.run values cut depth depth 0 n).probes≤magnitude n depth V by omega)
  unfold lookupBits GeneralPaperRankLookupPrice.specification natBits
  dsimp only
  omega

def window {n : ℕ} (model : RationalCostModel) (W depth : ℕ) (values : FixedArrayTable n ℕ) (cut : ℕ) : ℕ :=
  peak W values cut depth depth 0 n+
    lookupBits W (GeneralPaperRankLookupPrice.run true model.rat W depth values cut).1+
    (GeneralPaperRankLookupPrice.run true model.rat W depth values cut).2+256*W

theorem query {n : ℕ} (model : RationalCostModel) (W depth V : ℕ) (values : FixedArrayTable n ℕ) (cut : ℕ)
    (hn : n<2^depth) (hc : cut≤V) (hv : ∀ i,values.read i≤V) :
    window model W depth values cut≤(depth+1)*(32*width depth V+512*W)+
      3*width depth V+64*W+1024*(depth+1)*(W+model.rat (width depth V))+256*W := by
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add
    (bounded W depth V depth 0 n cut values (Nat.le_refl _) (Nat.zero_le _) (Nat.le_refl _) hn hc hv)
    (lookup_bound true model.rat W depth V values cut hn))
    (GeneralPaperRankLookupPrice.bit_work model.rat model.monotone W depth V values cut hn hc hv)) (256*W)
  exact h.trans_eq (by ring)

end Blotto.GeneralPaperRankTraversalStorage
