import Blotto.GeneralPaperCrossingPreparationStorage

/-! Native crossing refinement joins every preparation phase, selected
search/read/query scratch and its enclosing return. The optional adjacent
bracket retains both rational endpoints. Batch generation and outer affine
tables/basis/source owners remain separate compiler joins. -/
namespace Blotto.GeneralPaperCrossingRefinementStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def bracketFoot (W : ℕ) : Option GeneralPaperRayCrossingRefinement.Bracket → ℕ
  | none => 32*W
  | some b => rationalWordWidth b.lower+rationalWordWidth b.upper+64*W

theorem bracket_bound (model : RationalCostModel) (W R : ℕ) (query : ℚ → Bool×ℕ) (lo hi : ℚ) (points : List ℚ)
    (hl : RationalHeight lo R) (hh : RationalHeight hi R) (hp : ∀ t∈points,RationalHeight t R) :
    bracketFoot W (GeneralPaperPricedCrossingRefinement.run model.rat (fun w => w) W query lo hi points).bracket≤2*(1+2*R)+64*W := by
  rw [GeneralPaperPricedCrossingRefinement.data]
  unfold GeneralPaperRayCrossingRefinement.narrow
  dsimp only
  split
  · rename_i hr
    have a := rationalWordWidth_of_height (GeneralPaperRayBracketSize.read_height lo hi points R hl hh hp
      ⟨(GeneralPaperRaySearchControls.selected (fun i => query ((GeneralPaperRaySortedCrossings.array lo hi points).read i))).rank-1,by omega⟩)
    have b := rationalWordWidth_of_height (GeneralPaperRayBracketSize.read_height lo hi points R hl hh hp
      ⟨(GeneralPaperRaySearchControls.selected (fun i => query ((GeneralPaperRaySortedCrossings.array lo hi points).read i))).rank,hr.2⟩)
    change rationalWordWidth _+rationalWordWidth _+64*W≤_
    dsimp only
    omega
  · change 32*W≤_; omega

theorem price_mono (W P E n N : ℕ) (hn : n≤N) :
    GeneralPaperPricedCrossingRefinement.profile n W P E≤GeneralPaperPricedCrossingRefinement.profile N W P E := by
  have hArray := GeneralPaperRayRefinementResidents.price_mono hn W P
  unfold GeneralPaperPricedCrossingRefinement.profile GeneralPaperPricedCrossingRefinement.searchProfile
  gcongr

def metadataCap (model : RationalCostModel) (W n R E : ℕ) : ℕ :=
  n+3+(binaryWordWidth (n+3)+1)+GeneralPaperPricedCrossingRefinement.profile n W (model.rat (1+2*R)) E
def callerProfile (model : RationalCostModel) (W n R E : ℕ) : ℕ :=
  10*(natBits (metadataCap model W n R E)+W)+288*W

def caller (model : RationalCostModel) (W : ℕ) (query : ℚ → Bool×ℕ) (lo hi : ℚ) (points : List ℚ) : ℕ :=
  let values := GeneralPaperPricedCrossingArray.run model.rat (fun w => w) W lo hi points
  let search := GeneralPaperPricedRaySearch.selected (GeneralPaperPricedCrossingRefinement.readQuery query W values.1) W
  let result := GeneralPaperPricedCrossingRefinement.run model.rat (fun w => w) W query lo hi points
  fields W [points.length,(GeneralPaperRaySortedCrossings.ordered lo hi points).length,search.rank,search.probes,
    search.work,values.2,result.work,values.2+search.work,24*W,search.rank-1]+256*W

theorem caller_bound (model : RationalCostModel) (W n R E : ℕ) (query : ℚ → Bool×ℕ) (lo hi : ℚ) (points : List ℚ)
    (hn : points.length≤n) (hl : RationalHeight lo R) (hh : RationalHeight hi R) (hp : ∀ t∈points,RationalHeight t R)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+3)≤W)
    (hE : ∀ t∈GeneralPaperRaySortedCrossings.ordered lo hi points,(query t).2≤E) :
    caller model W query lo hi points≤callerProfile model W n R E := by
  let values := GeneralPaperPricedCrossingArray.run model.rat (fun w => w) W lo hi points
  let search := GeneralPaperPricedRaySearch.selected (GeneralPaperPricedCrossingRefinement.readQuery query W values.1) W
  let result := GeneralPaperPricedCrossingRefinement.run model.rat (fun w => w) W query lo hi points
  let count := (GeneralPaperRaySortedCrossings.ordered lo hi points).length
  let d := GeneralPaperRaySearchControls.depth count
  have hLen : count≤n+2 := (GeneralPaperRaySortedCrossings.ordered_length lo hi points).trans (Nat.add_le_add_right hn 2)
  have hRank := (GeneralPaperRaySearchStorage.rank_range (GeneralPaperPricedCrossingRefinement.readQuery query W values.1) W d d 0 count
    (Nat.zero_le _) le_rfl (GeneralPaperRaySearchControls.size_cap count)).2
  change search.rank≤count at hRank
  have hProbes := GeneralPaperPricedCrossingRefinement.probes model.rat (fun w => w) W query lo hi points
  change search.probes≤binaryWordWidth (points.length+3)+1 at hProbes
  have hProbe' := hProbes.trans (Nat.add_le_add_right (binaryWordWidth_mono (Nat.add_le_add_right hn 3)) 1)
  have hWork := (GeneralPaperPricedCrossingRefinement.bit_work model W R E query lo hi points hW
    ((binaryWordWidth_mono (Nat.add_le_add_right hn 3)).trans hIndex) hl hh hp hE).trans
      (price_mono W (model.rat (1+2*R)) E points.length n hn)
  change result.work≤GeneralPaperPricedCrossingRefinement.profile n W (model.rat (1+2*R)) E at hWork
  have hShape : result.work=values.2+search.work+24*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W n R E))
    [points.length,count,search.rank,search.probes,search.work,values.2,result.work,values.2+search.work,24*W,search.rank-1] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤10*(natBits (metadataCap model W n R E)+W)+32*W at hf
  change GeneralPaperEncodedScalarStorage.fields W [points.length,count,search.rank,search.probes,search.work,values.2,result.work,values.2+search.work,24*W,search.rank-1]+256*W≤_
  unfold callerProfile
  omega

inductive Phase where
  | prepare (phase : GeneralPaperCrossingPreparationStorage.Phase)
  | search
  | returned

def window (model : RationalCostModel) (W : ℕ) (query : ℚ → Bool×ℕ) (space : ℚ → ℕ)
    (lo hi : ℚ) (points : List ℚ) (phase : Phase) : ℕ :=
  GeneralPaperCrossingPreparationStorage.owners model W lo hi points+
    bracketFoot W (GeneralPaperPricedCrossingRefinement.run model.rat (fun w => w) W query lo hi points).bracket+
    caller model W query lo hi points+
    match phase with
    | .prepare p => GeneralPaperCrossingPreparationStorage.window model W lo hi points p
    | .search => GeneralPaperCrossingSearchStorage.window model W query space lo hi points
    | .returned => 0

def profile (model : RationalCostModel) (W n R E Q : ℕ) : ℕ :=
  GeneralPaperCrossingPreparationStorage.ownersProfile W n R+(2*(1+2*R)+64*W)+callerProfile model W n R E+
    GeneralPaperCrossingPreparationStorage.profile model W n R+GeneralPaperCrossingSearchStorage.profile model W n R E Q

theorem all_phases (model : RationalCostModel) (W n R E Q : ℕ) (query : ℚ → Bool×ℕ) (space : ℚ → ℕ)
    (lo hi : ℚ) (points : List ℚ) (hn : points.length≤n) (hl : RationalHeight lo R) (hh : RationalHeight hi R)
    (hp : ∀ t∈points,RationalHeight t R) (hW : 1≤W) (hIndex : binaryWordWidth (n+3)≤W)
    (hE : ∀ t∈GeneralPaperRaySortedCrossings.ordered lo hi points,(query t).2≤E)
    (hQ : ∀ t∈GeneralPaperRaySortedCrossings.ordered lo hi points,space t≤Q) (phase : Phase) :
    window model W query space lo hi points phase≤profile model W n R E Q := by
  have hO := GeneralPaperCrossingPreparationStorage.owners_bound model W n R lo hi points hn hl hh hp
  have hB := bracket_bound model W R query lo hi points hl hh hp
  have hC := caller_bound model W n R E query lo hi points hn hl hh hp hW hIndex hE
  have hP := GeneralPaperCrossingPreparationStorage.all_phases model W n R lo hi points hn hl hh hp hW hIndex
  have hS := GeneralPaperCrossingSearchStorage.bounded model W n R E Q query space lo hi points hn hl hh hp hE hQ
  cases phase with
  | prepare p =>
    have h := hP p
    unfold window profile
    dsimp only
    omega
  | search => unfold window profile; dsimp only; omega
  | returned => unfold window profile; dsimp only; omega

end Blotto.GeneralPaperCrossingRefinementStorage
