import Blotto.GeneralPaperSignedTailPrice

/-! Option plans read their common mesh from retained source parameters.
Resource tags and the mesh are reused by reference/value; neither catalogue
tags nor source parameters are regenerated during signed-tail preparation.
-/
namespace Blotto.GeneralPaperOptionPlanPrice
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096
variable {R : Type}

def run {K : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k U mesh : ℕ) (summary : Summary k)
    (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K R) : GeneralPaperOrderedNativeOptionProfits.Plan R k K × ℕ :=
  let tails := GeneralPaperSignedTailExecution.run bits index primitive W k U summary codes
  (⟨tags,mesh,tails.1⟩,tails.2+64*W)

theorem data {K : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k U mesh : ℕ) (summary : Summary k)
    (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K R)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits index primitive W k U mesh summary codes tags).1=
      GeneralPaperOrderedNativeOptionProfits.prepare k U summary codes tags := by
  unfold run GeneralPaperOrderedNativeOptionProfits.prepare
  dsimp only
  rw [GeneralPaperSignedTailExecution.data,hMesh]

theorem tags_preserved {K : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k U mesh : ℕ) (summary : Summary k)
    (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K R) :
    (run bits index primitive W k U mesh summary codes tags).1.tags=tags := rfl

theorem mesh_preserved {K : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k U mesh : ℕ) (summary : Summary k)
    (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K R) :
    (run bits index primitive W k U mesh summary codes tags).1.mesh=mesh := rfl

theorem bit_work {K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k U mesh : ℕ) (summary : Summary k)
    (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K R)
    (hCodes : ∀ i,codes.read i≤U) (hSummary : ∀ r,summary.read r≤2*U) :
    (run true (fun w => w) primitive W k U mesh summary codes tags).2≤
      GeneralPaperSignedTailPrice.profile primitive W K k U+64*W := by
  exact Nat.add_le_add_right (GeneralPaperSignedTailPrice.bit_work primitive hMono W k U summary codes hCodes hSummary) _

theorem arithmetic_work {K : ℕ} (k U mesh : ℕ) (summary : Summary k) (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K R) :
    (run false (fun _ => 1) (fun _ => 1) 1 k U mesh summary codes tags).2≤
      GeneralPaperSignedTailPrice.arithmeticProfile K k+64 := by
  exact Nat.add_le_add_right (GeneralPaperSignedTailPrice.arithmetic_work k U summary codes) _

theorem retained_mesh (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) :
    c.controls.source.meshDenominator=(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  rw [hc]
  rfl

end Blotto.GeneralPaperOptionPlanPrice
