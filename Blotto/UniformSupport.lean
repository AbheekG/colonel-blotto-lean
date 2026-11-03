import Blotto.AffineMixture
import Blotto.Boxes

namespace Blotto
open MeasureTheory Set

theorem uniformLaw_supported (L : ℝ) : ∀ᵐ t ∂uniformLaw L, t ∈ Icc 0 L := by
  have h : ∀ᵐ t ∂(volume.restrict (Icc 0 L) : Measure ℝ), t ∈ Icc 0 L :=
    ae_restrict_mem measurableSet_Icc
  exact Measure.ae_smul_measure h ((ENNReal.ofReal L)⁻¹)

theorem affineMeasure_supported {T L : ℝ} (hTL : T ≤ L) (q : ℝ) :
    ∀ᵐ t ∂affineMeasure q (uniformLaw T) (uniformLaw L), t ∈ Icc 0 L := by
  have hT : ∀ᵐ t ∂uniformLaw T, t ∈ Icc 0 L := (uniformLaw_supported T).mono fun t ht => ⟨ht.1, le_trans ht.2 hTL⟩
  have hL := uniformLaw_supported L
  rw [affineMeasure, ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure hT _, Measure.ae_smul_measure hL _⟩

end Blotto
