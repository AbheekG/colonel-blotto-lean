import Blotto.GeneralPaperFieldFamilyConstructionStorage

/-! Every native field constructor has four cell and four occurrence
children. A candidate/response selector covers each pair while completed
field records, original input families and full outer buffers remain live. -/
namespace Blotto.GeneralPaperFieldFamilyActiveStorage
open GeneralPaperCodeAlphabet
open GeneralPaperFieldFamilyConstructionStorage (ValidInputs)
open GeneralPaperCellPlanConstructionStorage (unsignedPart signedPart)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def own {m k : ℕ} (arrays : GeneralPaperFourSummaryArrays.Arrays m k) (mode : Bool) (j : Fin m) :=
  (if mode then arrays.q else arrays.p).read j
def opposite {m k : ℕ} (arrays : GeneralPaperFourSummaryArrays.Arrays m k) (mode : Bool) (j : Fin m) :=
  (if mode then arrays.p else arrays.q).read j
def signed {m k : ℕ} (arrays : GeneralPaperFourSummaryArrays.Arrays m k) (mode : Bool) (j : Fin m) :=
  (if mode then arrays.mu else arrays.lambda).read j
def options {m k : ℕ}
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ)) (mode : Bool) (j : Fin m) :=
  (if mode then response else candidate).read j

theorem selected_bounds {m k : ℕ} (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (hv : ValidInputs a arrays candidate response) (mode : Bool) (j : Fin m) :
    (∀ i,(own arrays mode j).read i<8*a.C) ∧ (∀ i,(opposite arrays mode j).read i<8*a.C) ∧
    (∀ i,(signed arrays mode j).read i<2*(8*a.C)) ∧ (∀ i,(options candidate response mode j).read i<8*a.C) := by
  rcases hv with ⟨hp,hq,hl,hm,hx,hy⟩
  cases mode
  · exact ⟨hp j,hq j,hl j,hx j⟩
  · exact ⟨hq j,hp j,hm j,hy j⟩

theorem with_occurrence_children {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (hv : ValidInputs a arrays candidate response) (count : ℕ) (hc : count≤m) (mode : Bool) (j : Fin m)
    (cdfCount tailCount signedCount : ℕ) (hCDF : cdfCount≤(GeneralPaperSourceParameters.prepare k).summarySize)
    (ht : tailCount≤(GeneralPaperSourceParameters.prepare k).summarySize+1)
    (hs : signedCount≤(GeneralPaperSourceParameters.prepare k).summarySize) (q : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)) :
    GeneralPaperFieldFamilyConstructionStorage.window model W a arrays candidate response count hc+
      GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a arrays candidate response j+
      GeneralPaperQueryLossConstructionStorage.window model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j)
        (own arrays mode j) cdfCount tailCount hCDF ht q+
      GeneralPaperSignedUpdateConstructionStorage.window model W k (8*a.C) (own arrays mode j) (signed arrays mode j) signedCount hs≤
    GeneralPaperFieldFamilyConstructionStorage.profile model W m k a+GeneralPaperFieldFamilyConstructionStorage.rowProfile model W k a+
      GeneralPaperQueryLossConstructionStorage.profile model W (GeneralPaperSourceParameters.prepare k).summarySize k (8*a.C)+
      GeneralPaperSignedUpdateConstructionStorage.profile model W (GeneralPaperSourceParameters.prepare k).summarySize k (8*a.C) := by
  have hf := GeneralPaperFieldFamilyConstructionStorage.bounded model W a arrays candidate response hv count hc
  have hr := GeneralPaperFieldFamilyConstructionStorage.row_bounded model W a arrays candidate response hv j
  have hb := selected_bounds a arrays candidate response hv mode j
  have hl := GeneralPaperQueryLossConstructionStorage.bounded model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j)
    (own arrays mode j) (fun i => (hb.2.1 i).le) (fun i => (hb.2.2.1 i).le) hb.1 cdfCount tailCount hCDF ht q
  have hs' := GeneralPaperSignedUpdateConstructionStorage.bounded model W k (8*a.C) (own arrays mode j) (signed arrays mode j)
    (fun i => (hb.1 i).le) hb.2.2.1 signedCount hs
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hf hr) hl) hs'

theorem with_cell_children {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (hv : ValidInputs a arrays candidate response) (count : ℕ) (hc : count≤m) (mode : Bool) (j : Fin m) :
    let ownSummary := own arrays mode j
    let otherSummary := opposite arrays mode j
    let signedSummary := signed arrays mode j
    let bids := options candidate response mode j
    let U := 8*a.C
    let s := (GeneralPaperSourceParameters.prepare k).summarySize
    let K := s+2
    let u := unsignedPart model W k U otherSummary signedSummary bids
    let t := signedPart model W k U ownSummary bids
    ∀ inputCount positionCount extraCount usedP usedE copied cellCountU cellCountS repCountU repCountS cdfCount tailCount rankCount
      (hi : inputCount≤s+K) (hp : positionCount≤2*s) (he : extraCount≤2*K+1)
      (hcu : cellCountU≤u.count) (hcs : cellCountS≤t.count) (hru : repCountU≤u.count) (hrs : repCountS≤t.count)
      (hCDF : cdfCount≤u.count) (ht : tailCount≤u.count+1) (hq : rankCount≤t.count) (q : Fin (u.count+1)),
    GeneralPaperFieldFamilyConstructionStorage.window model W a arrays candidate response count hc+
      GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a arrays candidate response j+
      GeneralPaperCellPlanConstructionStorage.unsignedWindow model W k U otherSummary signedSummary bids
        inputCount usedP usedE copied cellCountU repCountU cdfCount tailCount hi hcu hru hCDF ht q+
      GeneralPaperCellPlanConstructionStorage.signedWindow model W k U ownSummary bids
        positionCount extraCount usedP usedE copied cellCountS repCountS rankCount hp he hcs hrs hq≤
    GeneralPaperFieldFamilyConstructionStorage.profile model W m k a+GeneralPaperFieldFamilyConstructionStorage.rowProfile model W k a+
      GeneralPaperCellPlanConstructionStorage.unsignedProfile model W k U K+GeneralPaperCellPlanConstructionStorage.signedProfile model W k U K := by
  have hf := GeneralPaperFieldFamilyConstructionStorage.bounded model W a arrays candidate response hv count hc
  have hr := GeneralPaperFieldFamilyConstructionStorage.row_bounded model W a arrays candidate response hv j
  have hb := selected_bounds a arrays candidate response hv mode j
  dsimp only
  intro inputCount positionCount extraCount usedP usedE copied cellCountU cellCountS repCountU repCountS cdfCount tailCount rankCount
    hi hp he hcu hcs hru hrs hCDF ht hq q
  have hu := GeneralPaperCellPlanConstructionStorage.unsigned_bounded model W k (8*a.C) (opposite arrays mode j) (signed arrays mode j)
    (options candidate response mode j) hb.2.1 hb.2.2.1 hb.2.2.2 inputCount usedP usedE copied cellCountU repCountU cdfCount tailCount
    hi hcu hru hCDF ht q
  have hs := GeneralPaperCellPlanConstructionStorage.signed_bounded model W k (8*a.C) (own arrays mode j) (options candidate response mode j)
    hb.1 hb.2.2.2 positionCount extraCount usedP usedE copied cellCountS repCountS rankCount hp he hcs hrs hq
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hf hr) hu) hs

end Blotto.GeneralPaperFieldFamilyActiveStorage
