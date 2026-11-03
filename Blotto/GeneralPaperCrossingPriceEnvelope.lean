import Blotto.GeneralPaperPricedCrossingRefinement

/-! Explicit soft-linear sorting and logarithmic-query envelopes. In
particular the DP query price E is multiplied only by a logarithm of the
batch length, rather than by the number of crossings.
-/
namespace Blotto.GeneralPaperCrossingPriceEnvelope
set_option autoImplicit false

theorem sort_profile (n W P : ℕ) :
    GeneralPaperPricedSort.profile n W P≤
      256*(n+1)*(binaryWordWidth (n+1)+2)^2*(P+W) := by
  let w := binaryWordWidth (n+1)
  let slack :=
    (256*(n+1)*w^2+(1023*n+1024)*w+(1022*n+1024))*P+
    ((232*n+256)*w^2+(824*n+1012)*w+(712*n+1004))*W
  have he : GeneralPaperPricedSort.profile n W P+slack=
      256*(n+1)*(binaryWordWidth (n+1)+2)^2*(P+W) := by
    unfold GeneralPaperPricedSort.profile
    dsimp only [slack,w]
    ring
  omega

theorem refinement_profile (n W P E : ℕ) :
    GeneralPaperPricedCrossingRefinement.profile n W P E≤
      512*(n+3)*(binaryWordWidth (n+3)+2)^2*(P+W)+
        (binaryWordWidth (n+3)+1)*E := by
  let w := binaryWordWidth (n+3)
  let slack :=
    (512*(n+3)*w^2+(2047*n+6142)*w+(2043*n+6134))*P+
    ((488*n+1476)*w^2+(1848*n+5654)*w+(1640*n+5112))*W
  have he : GeneralPaperPricedCrossingRefinement.profile n W P E+slack=
      512*(n+3)*(binaryWordWidth (n+3)+2)^2*(P+W)+
        (binaryWordWidth (n+3)+1)*E := by
    unfold GeneralPaperPricedCrossingRefinement.profile
      GeneralPaperPricedCrossingArray.profile GeneralPaperPricedCrossingSort.profile
      GeneralPaperPricedSort.profile GeneralPaperPricedCrossingRefinement.searchProfile
    dsimp only [slack,w]
    have hn : n+2+1=n+3 := by omega
    rw [hn]
    ring
  omega

end Blotto.GeneralPaperCrossingPriceEnvelope
