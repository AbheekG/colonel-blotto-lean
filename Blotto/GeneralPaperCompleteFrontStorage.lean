import Blotto.GeneralPaperPrecallConstructionStorage

/-! Selected complete classifier preparation, including the previously
separate parameter-construction phase. Join the actual returned record and
original-input caller frame at the actual combined source-precall word.
Input/compiler height interpretation and global source W remain open. -/
namespace Blotto.GeneralPaperCompleteFrontStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPrecallCacheStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def window (model : RationalCostModel) (W m k : ℕ) (b : ℚ) : ℕ :=
  let c := (GeneralPaperPrecallCachePrice.prepare model.rat W m k).1.1
  GeneralPaperPrecallConstructionStorage.window model W m k+
    GeneralPaperClassifierConstructionStorage.window model W m k c
      (GeneralPaperStreamingPreparedClassifier.cache_positive model W m k) b+
    GeneralPaperClassifierResultStorage.frontFootprint W (GeneralPaperStreamingPreparedClassifier.prepare model W m k b).1+
    rationalWordWidth b+fields W [m,k]+256*W

def profile (model : RationalCostModel) (W m k B : ℕ) : ℕ :=
  GeneralPaperPrecallConstructionStorage.profile model W m k+
    GeneralPaperClassifierConstructionStorage.profile model W m k B+
    GeneralPaperClassifierResultStorage.frontProfile W m k+(1+2*B)+2*payload m k+290*W

theorem bounded (model : RationalCostModel) (W m k : ℕ)
    (hW : GeneralPaperPrecallControlWord.word m k≤W) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) : window model W m k b≤profile model W m k B := by
  have hp := GeneralPaperPrecallConstructionStorage.bounded model W m k
  have hc := GeneralPaperClassifierConstructionStorage.bounded model W m k
    (GeneralPaperPrecallCachePrice.prepare model.rat W m k).1.1
    (GeneralPaperPrecallCachePrice.data model.rat W m k)
    (GeneralPaperStreamingPreparedClassifier.cache_positive model W m k) hW b hb B hB
  have hr := GeneralPaperClassifierResultStorage.front_returned model W m k b hb
  have hbW := rationalWordWidth_of_height hB
  have hi := GeneralPaperPrecallConstructorBounds.input_words m k
  have hf := fields_bound W (payload m k) [m,k] (by
    intro x hx
    apply hi x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    rcases hx with hx|hx <;> tauto)
  change _≤2*(payload m k+W)+32*W at hf
  unfold window profile
  dsimp only
  omega

theorem source_word (model : RationalCostModel) (m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) :
    window model (GeneralPaperSourcePrecallPreparation.word m k Qv) m k b≤
      profile model (GeneralPaperSourcePrecallPreparation.word m k Qv) m k B :=
  bounded model _ m k (GeneralPaperSourcePrecallPreparation.front_word m k Qv) b hb B hB

theorem retained_source_cache (model : RationalCostModel) (W m k Qv : ℕ)
    (hW : GeneralPaperPrecallControlWord.word m k≤W) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) :
    window model W m k b+
      GeneralPaperPreparationCacheStorage.footprint W (GeneralPaperSourcePrecallPreparation.prepare model W m k Qv b).1.2≤
        profile model W m k B+
          GeneralPaperPreparationCacheStorage.profile W m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv := by
  have hf := bounded model W m k hW b hb B hB
  rw [GeneralPaperSourcePrecallPreparation.data]
  exact Nat.add_le_add hf (GeneralPaperPreparationCacheStorage.native W m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv)

theorem with_residents {m : ℕ} (model : RationalCostModel) (W k Qv B : ℕ)
    (hW : GeneralPaperPrecallControlWord.word m k≤W) (b : ℚ) (hb : 0<b ∧ b<1)
    (hB : RationalHeight b B) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    window model W m k b+
      (GeneralPaperClassifierResultStorage.frontFootprint W r.1.1+
        (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
          GeneralPaperEpochResidentStorage.footprint W k Qv r.1.1.1.2 weights Bc Br epoch time)+64*W)≤
      profile model W m k B+GeneralPaperPrecallResidentStorage.residentProfile W k Qv r.1.1.1.2 weights Bc Br :=
  Nat.add_le_add (bounded model W m k hW b hb B hB)
    (GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br epoch time he ht)

end Blotto.GeneralPaperCompleteFrontStorage
