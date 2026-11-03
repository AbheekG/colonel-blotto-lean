import Blotto.GeneralPaperSignedTailStorage

/-! Each native option plan reuses its actual tag row and retained mesh.
The outer indexed constructor owns full reserved plan buffers and original
summary/code/tag inputs while one signed-tail constructor is active. -/
namespace Blotto.GeneralPaperOptionPlanConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def tagRowProfile (W K L : ℕ) : ℕ := K*(L+17*W+1)+32*W

theorem tags_bound {K : ℕ} (W L : ℕ) (tags : FixedArrayTable K GeneralPaperResponseTag.Tag)
    (ht : ∀ i,rationalWordWidth (tags.read i).threshold≤L) :
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.tagBits W) tags≤tagRowProfile W K L := by
  have h := GeneralPaperEncodedFixedVector.bounded W (L+1+16*W) (GeneralPaperEncodedOptionCache.tagBits W) tags (by
    intro i
    have hi := ht i
    unfold GeneralPaperEncodedOptionCache.tagBits
    omega)
  exact h.trans_eq (by unfold tagRowProfile; ring)

def row {K : ℕ} (model : RationalCostModel) (W k U mesh : ℕ) (summary : Summary k)
    (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K GeneralPaperResponseTag.Tag) :=
  (GeneralPaperOptionPlanPrice.run true (fun w => w) model.rat W k U mesh summary codes tags).1

def rowProfile (W K k U L : ℕ) : ℕ :=
  tagRowProfile W K L+GeneralPaperSignedTailStorage.returnedProfile W K k U+(128+8*k)+64*W

theorem row_returned {K : ℕ} (model : RationalCostModel) (W k U mesh L : ℕ) (summary : Summary k)
    (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K GeneralPaperResponseTag.Tag)
    (ht : ∀ i,rationalWordWidth (tags.read i).threshold≤L)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    GeneralPaperEncodedOptionCache.footprint W (row model W k U mesh summary codes tags)≤rowProfile W K k U L := by
  have htag := tags_bound W L tags ht
  have htail := GeneralPaperSignedTailStorage.returned_bound model W k U summary codes
  have hmesh := GeneralPaperEncodedOptionCache.mesh_word k
  rw [←hm] at hmesh
  change natBits mesh≤128+8*k at hmesh
  change GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.tagBits W) tags+
    GeneralPaperSignedTailStorage.returned model W k U summary codes+natBits mesh+64*W≤_
  unfold rowProfile
  omega

def rowWindow {K : ℕ} (model : RationalCostModel) (W k U mesh : ℕ) (summary : Summary k)
    (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K GeneralPaperResponseTag.Tag)
    (count : ℕ) (hc : count≤K+1) (q : Fin (K+1)) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.tagBits W) tags+natBits mesh+
    fields W [k,U,mesh,K]+GeneralPaperSignedTailStorage.window model W k U summary codes count hc q+
    GeneralPaperEncodedOptionCache.footprint W (row model W k U mesh summary codes tags)+
    (GeneralPaperOptionPlanPrice.run true (fun w => w) model.rat W k U mesh summary codes tags).2+128*W

def rowWindowProfile (model : RationalCostModel) (W K k U mesh L : ℕ) : ℕ :=
  tagRowProfile W K L+(128+8*k)+fields W [k,U,mesh,K]+GeneralPaperSignedTailStorage.profile model W K k U+
    rowProfile W K k U L+(GeneralPaperSignedTailPrice.profile model.rat W K k U+64*W)+128*W

theorem row_bound {K : ℕ} (model : RationalCostModel) (W k U mesh L : ℕ) (summary : Summary k)
    (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K GeneralPaperResponseTag.Tag)
    (hs : ∀ r,summary.read r≤2*U) (hcCode : ∀ i,codes.read i≤U)
    (ht : ∀ i,rationalWordWidth (tags.read i).threshold≤L)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (count : ℕ) (hc : count≤K+1) (q : Fin (K+1)) :
    rowWindow model W k U mesh summary codes tags count hc q≤rowWindowProfile model W K k U mesh L := by
  have htag := tags_bound W L tags ht
  have hmesh := GeneralPaperEncodedOptionCache.mesh_word k
  rw [←hm] at hmesh
  change natBits mesh≤128+8*k at hmesh
  have htail := GeneralPaperSignedTailStorage.bounded model W k U summary codes hs hcCode count hc q
  have hr := row_returned model W k U mesh L summary codes tags ht hm
  have hp := GeneralPaperOptionPlanPrice.bit_work model.rat model.monotone W k U mesh summary codes tags hcCode hs
  unfold rowWindow rowWindowProfile
  omega

def familyPrefix {m K : ℕ} (model : RationalCostModel) (W k U mesh : ℕ) (summaries : FixedArrayTable m (Summary k))
    (codes : FixedArrayTable m (FixedArrayTable K ℕ)) (tags : FixedArrayTable m (FixedArrayTable K GeneralPaperResponseTag.Tag))
    (count : ℕ) (hc : count≤m) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W m (GeneralPaperEncodedOptionCache.footprint W)
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperOptionPlanFamily.element true (fun w => w) model.rat W k U mesh summaries codes tags) count hc).1

theorem family_prefix_bound {m K : ℕ} (model : RationalCostModel) (W k U mesh L : ℕ) (summaries : FixedArrayTable m (Summary k))
    (codes : FixedArrayTable m (FixedArrayTable K ℕ)) (tags : FixedArrayTable m (FixedArrayTable K GeneralPaperResponseTag.Tag))
    (ht : ∀ j i,rationalWordWidth ((tags.read j).read i).threshold≤L)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (count : ℕ) (hc : count≤m) :
    familyPrefix model W k U mesh summaries codes tags count hc≤m*(rowProfile W K k U L+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m) W
    (rowProfile W K k U L) (GeneralPaperEncodedOptionCache.footprint W)
    (GeneralPaperOptionPlanFamily.element true (fun w => w) model.rat W k U mesh summaries codes tags)
    (fun j => row_returned model W k U mesh L (summaries.read j) (codes.read j) (tags.read j) (ht j) hm) count hc

theorem family_returned {m K : ℕ} (model : RationalCostModel) (W k U mesh L : ℕ) (summaries : FixedArrayTable m (Summary k))
    (codes : FixedArrayTable m (FixedArrayTable K ℕ)) (tags : FixedArrayTable m (FixedArrayTable K GeneralPaperResponseTag.Tag))
    (ht : ∀ j i,rationalWordWidth ((tags.read j).read i).threshold≤L)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.footprint W)
      (GeneralPaperOptionPlanFamily.run true (fun w => w) model.rat W k U mesh summaries codes tags).1≤
      m*(rowProfile W K k U L+W)+32*W := by
  apply GeneralPaperEncodedFixedVector.bounded W (rowProfile W K k U L)
  intro j
  rw [GeneralPaperOptionPlanFamily.run,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact row_returned model W k U mesh L (summaries.read j) (codes.read j) (tags.read j) (ht j) hm

def window {m K : ℕ} (model : RationalCostModel) (W k U mesh : ℕ) (summaries : FixedArrayTable m (Summary k))
    (codes : FixedArrayTable m (FixedArrayTable K ℕ)) (tags : FixedArrayTable m (FixedArrayTable K GeneralPaperResponseTag.Tag))
    (count rowCount : ℕ) (hc : count≤m) (hr : rowCount≤K+1) (j : Fin m) (q : Fin (K+1)) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) summaries+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) codes+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.tagBits W)) tags+
    2*familyPrefix model W k U mesh summaries codes tags count hc+GeneralPaperGridArrayConstructionStorage.frames W m+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.footprint W)
      (GeneralPaperOptionPlanFamily.run true (fun w => w) model.rat W k U mesh summaries codes tags).1+
    rowWindow model W k U mesh (summaries.read j) (codes.read j) (tags.read j) rowCount hr q+
    fields W [m,K,k,U,mesh]+(GeneralPaperOptionPlanFamily.run true (fun w => w) model.rat W k U mesh summaries codes tags).2+128*W

def profile (model : RationalCostModel) (W m K k U mesh L : ℕ) : ℕ :=
  (m*((GeneralPaperSourceParameters.prepare k).summarySize*(natBits (2*U)+W)+33*W)+32*W)+
    (m*(K*(natBits U+W)+33*W)+32*W)+(m*(tagRowProfile W K L+W)+32*W)+
    2*(m*(rowProfile W K k U L+W)+64*W)+GeneralPaperGridArrayConstructionStorage.frames W m+
    (m*(rowProfile W K k U L+W)+32*W)+rowWindowProfile model W K k U mesh L+
    fields W [m,K,k,U,mesh]+GeneralPaperOptionPlanFamily.profile model.rat W m K k U+128*W

theorem bounded {m K : ℕ} (model : RationalCostModel) (W k U mesh L : ℕ) (summaries : FixedArrayTable m (Summary k))
    (codes : FixedArrayTable m (FixedArrayTable K ℕ)) (tags : FixedArrayTable m (FixedArrayTable K GeneralPaperResponseTag.Tag))
    (hs : ∀ j r,(summaries.read j).read r≤2*U) (hq : ∀ j i,(codes.read j).read i≤U)
    (ht : ∀ j i,rationalWordWidth ((tags.read j).read i).threshold≤L)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (count rowCount : ℕ) (hc : count≤m) (hr : rowCount≤K+1) (j : Fin m) (q : Fin (K+1)) :
    window model W k U mesh summaries codes tags count rowCount hc hr j q≤profile model W m K k U mesh L := by
  have hsummary := GeneralPaperEncodedFixedVector.bounded W _ (GeneralPaperEncodedNatArray.footprint W) summaries
    (fun j => GeneralPaperEncodedNatArray.bounded W (natBits (2*U)) (summaries.read j)
      (fun r => Nat.add_le_add_left (binaryWordWidth_mono (hs j r)) 1))
  have hcodes := GeneralPaperEncodedFixedVector.bounded W _ (GeneralPaperEncodedNatArray.footprint W) codes
    (fun j => GeneralPaperEncodedNatArray.bounded W (natBits U) (codes.read j)
      (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hq j i)) 1))
  have htags := GeneralPaperEncodedFixedVector.bounded W _ _ tags (fun j => tags_bound W L (tags.read j) (ht j))
  have hp := family_prefix_bound model W k U mesh L summaries codes tags ht hm count hc
  have hf := family_returned model W k U mesh L summaries codes tags ht hm
  have hrow := row_bound model W k U mesh L (summaries.read j) (codes.read j) (tags.read j) (hs j) (hq j) (ht j) hm rowCount hr q
  have hwork := GeneralPaperOptionPlanFamily.bit_work model.rat model.monotone W k U mesh summaries codes tags hq hs
  have hsummary' : GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) summaries≤
      m*((GeneralPaperSourceParameters.prepare k).summarySize*(natBits (2*U)+W)+33*W)+32*W := hsummary.trans_eq (by ring)
  have hcodes' : GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) codes≤
      m*(K*(natBits U+W)+33*W)+32*W := hcodes.trans_eq (by ring)
  unfold window profile
  omega

end Blotto.GeneralPaperOptionPlanConstructionStorage
