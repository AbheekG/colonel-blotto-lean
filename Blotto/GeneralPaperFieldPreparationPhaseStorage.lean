import Blotto.GeneralPaperLocalSourceLifetimeStorage

/-! Close the previously separate active field-preparation children under
one finite phase observer. Actual unsigned/signed partitions determine every
clipped cell/rank capacity. All four cell and four occurrence constructors
are covered by the two native candidate/response modes. Extrema erase. -/
namespace Blotto.GeneralPaperFieldPreparationPhaseStorage
open GeneralPaperCodeAlphabet GeneralPaperFiniteStorageWindows
open GeneralPaperFieldFamilyActiveStorage
open GeneralPaperCellPlanConstructionStorage (unsignedPart signedPart)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def progressCap (k : ℕ) : ℕ := 64+64*(GeneralPaperSourceParameters.prepare k).summarySize

abbrev Progress (k : ℕ) := Fin 13 → Fin (progressCap k+1)

theorem native_caps (k : ℕ) :
    ∀ x∈[(GeneralPaperSourceParameters.prepare k).summarySize,
      (GeneralPaperSourceParameters.prepare k).summarySize+1,2*(GeneralPaperSourceParameters.prepare k).summarySize,
      2*((GeneralPaperSourceParameters.prepare k).summarySize+2)+1,
      (GeneralPaperSourceParameters.prepare k).summarySize+((GeneralPaperSourceParameters.prepare k).summarySize+2),
      GeneralPaperBatchCounterPrice.limit k+1],x≤progressCap k := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx|hx|hx|hx|hx <;> rw [hx] <;>
    dsimp only [progressCap,GeneralPaperBatchCounterPrice.limit] <;> omega

def children {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (mode : Bool) (j : Fin m) (progress : Progress k) : ℕ :=
  let S := (GeneralPaperSourceParameters.prepare k).summarySize
  let K := S+2
  let U := 8*a.C
  let ownSummary := own arrays mode j
  let otherSummary := opposite arrays mode j
  let signedSummary := signed arrays mode j
  let bids := options candidate response mode j
  let u := unsignedPart model W k U otherSummary signedSummary bids
  let t := signedPart model W k U ownSummary bids
  let p := fun i : Fin 13 => (progress i).val
  GeneralPaperCellPlanConstructionStorage.unsignedWindow model W k U otherSummary signedSummary bids
    (min (p 0) (S+K)) (p 1) (p 2) (p 3) (min (p 4) u.count) (min (p 5) u.count)
    (min (p 6) u.count) (min (p 7) (u.count+1))
    (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..)
    ⟨min (p 12) u.count,Nat.lt_succ_of_le (Nat.min_le_right ..)⟩+
  GeneralPaperCellPlanConstructionStorage.signedWindow model W k U ownSummary bids
    (min (p 8) (2*S)) (min (p 9) (2*K+1)) (p 1) (p 2) (p 3)
    (min (p 10) t.count) (min (p 11) t.count) (min (p 12) t.count)
    (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..)+
  GeneralPaperQueryLossConstructionStorage.window model W k U otherSummary signedSummary ownSummary
    (min (p 0) S) (min (p 1) (S+1)) (Nat.min_le_right ..) (Nat.min_le_right ..)
    ⟨min (p 2) S,Nat.lt_succ_of_le (Nat.min_le_right ..)⟩+
  GeneralPaperSignedUpdateConstructionStorage.window model W k U ownSummary signedSummary
    (min (p 3) S) (Nat.min_le_right ..)

def childrenProfile (model : RationalCostModel) (W k : ℕ) (a : Alphabet) : ℕ :=
  let S := (GeneralPaperSourceParameters.prepare k).summarySize
  let U := 8*a.C
  GeneralPaperCellPlanConstructionStorage.unsignedProfile model W k U (S+2)+
    GeneralPaperCellPlanConstructionStorage.signedProfile model W k U (S+2)+
    GeneralPaperQueryLossConstructionStorage.profile model W S k U+
    GeneralPaperSignedUpdateConstructionStorage.profile model W S k U

theorem children_bound {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (hv : GeneralPaperFieldFamilyConstructionStorage.ValidInputs a arrays candidate response)
    (mode : Bool) (j : Fin m) (progress : Progress k) :
    children model W a arrays candidate response mode j progress≤childrenProfile model W k a := by
  have hb := selected_bounds a arrays candidate response hv mode j
  dsimp only [children,childrenProfile]
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · apply Nat.add_le_add
      · exact GeneralPaperCellPlanConstructionStorage.unsigned_bounded model W k (8*a.C)
          (opposite arrays mode j) (signed arrays mode j) (options candidate response mode j)
          hb.2.1 hb.2.2.1 hb.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _
      · exact GeneralPaperCellPlanConstructionStorage.signed_bounded model W k (8*a.C)
          (own arrays mode j) (options candidate response mode j) hb.1 hb.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _
    · exact GeneralPaperQueryLossConstructionStorage.bounded model W k (8*a.C)
        (opposite arrays mode j) (signed arrays mode j) (own arrays mode j)
        (fun i => (hb.2.1 i).le) (fun i => (hb.2.2.1 i).le) hb.1 _ _ _ _ _
  · exact GeneralPaperSignedUpdateConstructionStorage.bounded model W k (8*a.C)
      (own arrays mode j) (signed arrays mode j) (fun i => (hb.1 i).le) hb.2.2.1 _ _

abbrev Cursor (m k : ℕ) := Fin (m+1) × Bool × Fin m × Progress k

def visit {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (cursor : Cursor m k) : ℕ :=
  let ⟨count,mode,j,progress⟩ := cursor
  GeneralPaperFieldFamilyConstructionStorage.window model W a arrays candidate response count.val (Nat.le_of_lt_succ count.isLt)+
    GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a arrays candidate response j+
    children model W a arrays candidate response mode j progress

def peak {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ)) : ℕ :=
  maximum (visit model W a arrays candidate response)

def profile (model : RationalCostModel) (W m k : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperFieldFamilyConstructionStorage.profile model W m k a+
    GeneralPaperFieldFamilyConstructionStorage.rowProfile model W k a+childrenProfile model W k a

theorem bounded {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (hv : GeneralPaperFieldFamilyConstructionStorage.ValidInputs a arrays candidate response) :
    peak model W a arrays candidate response≤profile model W m k a := by
  apply maximum_bound
  intro cursor
  rcases cursor with ⟨count,mode,j,progress⟩
  exact Nat.add_le_add (Nat.add_le_add
    (GeneralPaperFieldFamilyConstructionStorage.bounded model W a arrays candidate response hv count.val (Nat.le_of_lt_succ count.isLt))
    (GeneralPaperFieldFamilyConstructionStorage.row_bounded model W a arrays candidate response hv j))
    (children_bound model W a arrays candidate response hv mode j progress)

theorem native_tree_arrays (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda)
    (hv : GeneralPaperCatalogueTreeCache.Valid a k trees) (hp : GeneralPaperCatalogueTreeCache.Paths a k trees) :
    let x := GeneralPaperTreeEpochConstructionStorage.arrays model W m k Qv a c hc digits trees
    let hm := GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc
    peak model W a x
      (GeneralPaperEpochCacheConstructionStorage.candidate model W c.controls.source.meshDenominator a x hm).data.codes
      (GeneralPaperEpochCacheConstructionStorage.response model W c.controls.source.meshDenominator a x hm).data.codes≤
        profile model W m k a :=
  bounded model W a _ _ _ (GeneralPaperEpochCacheConstructionStorage.inputs_valid model W _ a _ _
    (GeneralPaperTreeEpochConstructionStorage.valid_four model W m k Qv a c hc digits trees hv hp))

end Blotto.GeneralPaperFieldPreparationPhaseStorage
