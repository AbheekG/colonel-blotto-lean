import Blotto.GeneralPaperSourceEndpointProbeStorage

/-! The existing uniform root envelope also bounds the retained point,
direction and short budget rational owners. Packed array readers preserve
these actual coordinate heights; no runtime height traversal is added. -/
namespace Blotto.GeneralPaperRayOperandStorageHeight
open RationalOrderCell GeneralPaperRayRationalBound GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem point {D E m X V P : ℕ} {q : ℚ} (hD : 0<D) (hq : Bounded D X q) :
    RationalHeight q (width D E m X V P) := by
  have hCap : X+1≤ interceptCap m X P+interceptCap m X P+1 := by unfold interceptCap; nlinarith
  have hh := binaryWordWidth_mono hCap
  have ht := hq.height hD
  apply ht.mono
  unfold width GeneralPaperRayAffineBound.rootWidth
  omega

theorem direction {D E m X V P : ℕ} {q : ℚ} (hE : 0<E) (hq : Bounded E V q) :
    RationalHeight q (width D E m X V P) := by
  have hCap : V+1≤ slopeCap m V+slopeCap m V+1 := by unfold slopeCap; nlinarith
  have hh := binaryWordWidth_mono hCap
  have ht := hq.height hE
  apply ht.mono
  unfold width GeneralPaperRayAffineBound.rootWidth
  omega

theorem budget {D E m X V P : ℕ} {q : ℚ} (hD : 0<D) (hq : Bounded D P q) :
    RationalHeight q (width D E m X V P) := by
  have hCap : P+1≤ interceptCap m X P+interceptCap m X P+1 := by unfold interceptCap; nlinarith
  have hh := binaryWordWidth_mono hCap
  have ht := hq.height hD
  apply ht.mono
  unfold width GeneralPaperRayAffineBound.rootWidth
  omega

theorem packed_bound {m K : ℕ} (W R : ℕ) (values : GeneralPaperBasisRationalSolve.RatVector (m*(K-1)))
    (h : ∀ a,RationalHeight (GeneralPaperBasisOriginalDirection.reader values a) R) :
    GeneralPaperEncodedRationalRows.rowFootprint W values≤GeneralPaperEncodedRationalRows.rowProfile W (m*(K-1)) R := by
  apply GeneralPaperEncodedRationalRows.row_bound
  intro i
  obtain ⟨a,ha⟩ := GeneralPaperBasisCoordinates.index_surjective m K i
  have hh := h a
  simpa only [GeneralPaperBasisOriginalDirection.reader,ha] using hh

end Blotto.GeneralPaperRayOperandStorageHeight
