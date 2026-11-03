import Blotto.GeneralPaperRaySearchStorage

/-! Selected native crossing search, including actual depth construction
and outer return metadata. Query storage remains one active reservation.
The analytical size cap and query-space function are erased observers. -/
namespace Blotto.GeneralPaperSelectedSearchStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def depth (N : ℕ) : ℕ := binaryWordWidth N+1
def workCap (W E N : ℕ) : ℕ := depth N*((12*depth N+34)*W+E)+(12*binaryWordWidth N+26)*W
def metadataCap (W E N : ℕ) : ℕ := N+depth N+1+workCap W E N

def window {n : ℕ} (model : RationalCostModel) (query : Fin n → Bool×ℕ) (space : Fin n → ℕ) (W : ℕ) : ℕ :=
  let scale := GeneralPaperPowerCeiling.ceiling n
  let d := scale.doublings+1
  let inner := GeneralPaperPricedRaySearch.run query W d d 0 n
  let result := GeneralPaperPricedRaySearch.selected query W
  GeneralPaperRaySearchStorage.peak model query space W d d 0 n+
    GeneralPaperCeilingConstructionStorage.peak W n 1 (by decide)+
    fields W [n,d,result.rank,result.work,result.probes,inner.work,scale.work*W,inner.work+scale.work*W]+256*W

def profile (model : RationalCostModel) (W E Q N : ℕ) : ℕ :=
  (depth N+1)*GeneralPaperRaySearchStorage.coefficient model W E (depth N) N+Q+
    depth N*(5*GeneralPaperCeilingConstructionStorage.word N+192*W)+
    8*(natBits (metadataCap W E N)+W)+32*W+256*W

theorem profile_mono (model : RationalCostModel) (W E Q n N : ℕ) (hn : n≤N) :
    profile model W E Q n≤profile model W E Q N := by
  have hd : depth n≤depth N := Nat.add_le_add_right (binaryWordWidth_mono hn) 1
  have hi := GeneralPaperRaySearchStorage.coefficient_mono model W E (depth n) (depth N) n N hd hn
  unfold profile metadataCap workCap GeneralPaperCeilingConstructionStorage.word natBits
  gcongr

theorem actual {n : ℕ} (model : RationalCostModel) (query : Fin n → Bool×ℕ) (space : Fin n → ℕ) (W E Q : ℕ)
    (hE : ∀ i,(query i).2≤E) (hQ : ∀ i,space i≤Q) :
    window model query space W≤profile model W E Q n := by
  let scale := GeneralPaperPowerCeiling.ceiling n
  let d := scale.doublings+1
  let inner := GeneralPaperPricedRaySearch.run query W d d 0 n
  let result := GeneralPaperPricedRaySearch.selected query W
  have hd : d≤depth n := GeneralPaperRaySearchControls.depth_bound n
  have hs : n<2^d := GeneralPaperRaySearchControls.size_cap n
  have hSearch := GeneralPaperRaySearchStorage.bounded model query space W E Q d d 0 n le_rfl (Nat.zero_le _) le_rfl hs hE hQ
  have hSearch' := hSearch.trans (Nat.add_le_add_right
    (Nat.mul_le_mul (Nat.add_le_add_right hd 1) (GeneralPaperRaySearchStorage.coefficient_mono model W E d (depth n) n n hd le_rfl)) Q)
  have hCeiling := GeneralPaperCeilingConstructionStorage.bounded W n 1 (by decide) (by omega)
  change GeneralPaperCeilingConstructionStorage.peak W n 1 (by decide)≤d*(5*GeneralPaperCeilingConstructionStorage.word n+192*W) at hCeiling
  have hCeiling' := hCeiling.trans (Nat.mul_le_mul_right _ hd)
  have hWork := GeneralPaperPricedRaySearch.selected_work query W E hE
  have hWork' : result.work≤workCap W E n := hWork.trans (by unfold workCap; gcongr <;> exact hd)
  have hRank : result.rank≤n := (GeneralPaperRaySearchStorage.rank_range query W d d 0 n (Nat.zero_le _) le_rfl hs).2
  have hProbes : result.probes≤depth n := GeneralPaperPricedRaySearch.selected_probes query W
  have hShape : result.work=inner.work+scale.work*W+16*W := rfl
  have hFields := fields_bound W (natBits (metadataCap W E n))
    [n,d,result.rank,result.work,result.probes,inner.work,scale.work*W,inner.work+scale.work*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤8*(natBits (metadataCap W E n)+W)+32*W at hFields
  change GeneralPaperRaySearchStorage.peak model query space W d d 0 n+
    GeneralPaperCeilingConstructionStorage.peak W n 1 (by decide)+
    GeneralPaperEncodedScalarStorage.fields W [n,d,result.rank,result.work,result.probes,inner.work,scale.work*W,inner.work+scale.work*W]+256*W≤_
  unfold profile
  omega

theorem bounded {n : ℕ} (model : RationalCostModel) (query : Fin n → Bool×ℕ) (space : Fin n → ℕ) (W E Q N : ℕ)
    (hn : n≤N) (hE : ∀ i,(query i).2≤E) (hQ : ∀ i,space i≤Q) :
    window model query space W≤profile model W E Q N :=
  (actual model query space W E Q hE hQ).trans (profile_mono model W E Q n N hn)

end Blotto.GeneralPaperSelectedSearchStorage
