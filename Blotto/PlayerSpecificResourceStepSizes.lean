import Blotto.PlayerSpecificResourceCostProfile

/-! Every reached cached request derives its actual probability and
both chosen-resource coefficient envelopes from the live rows. These
are proof bounds; no such certificate is an executing input. -/
namespace Blotto.PlayerSpecificResourceStepSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicReduction
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (U : ℕ) : ℕ := PlayerSpecificAlgebraicPairHeights.probabilityHeight U+6*(U+1)+100

theorem large (U H : ℕ) (hH : H≤U) :
    U≤height U ∧ PlayerSpecificAlgebraicPairHeights.resourceHeight U≤height U ∧
      PlayerSpecificAlgebraicPairHeights.probabilityHeight U+H+3≤height U+1 ∧ 1≤height U := by
  unfold height PlayerSpecificAlgebraicPairHeights.resourceHeight
  omega

theorem linear (U : ℕ) : height U+1≤(8*PlayerSpecificAlgebraicHeightEnvelope.coefficient+107)*(U+1) := by
  have h:=PlayerSpecificAlgebraicPairHeights.probability_linear U
  unfold height
  nlinarith only [h,Nat.zero_le U]

theorem requested {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (f : Frame N)
    (hf : request RationalCostModel.schoolbook p s=some f) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (hs : Valid p x s) (U : ℕ)
    (hml : p.parameters.root.polynomial.length≤4) (hmH : HasHeight p.parameters.root.polynomial U)
    (hl : ∀ j,HasHeight (p.rows.read j).length U) (hr : ∀ j,HasHeight (s.data.read j) U) :
    Reduced p.parameters.root.polynomial f.pair.probability ∧
      HasHeight f.pair.probability (PlayerSpecificAlgebraicPairHeights.probabilityHeight U) ∧
      ∀ upper : Bool,
        (Reduced p.parameters.root.polynomial (if upper then f.pair.upperA else f.pair.lowerA) ∧
          HasHeight (if upper then f.pair.upperA else f.pair.lowerA) (PlayerSpecificAlgebraicPairHeights.resourceHeight U)) ∧
        (Reduced p.parameters.root.polynomial (if upper then f.pair.upperB else f.pair.lowerB) ∧
          HasHeight (if upper then f.pair.upperB else f.pair.lowerB) (PlayerSpecificAlgebraicPairHeights.resourceHeight U)) := by
  have hm0 : p.parameters.root.polynomial≠[] := by
    intro h
    exact hc.irreducible.ne_zero (by rw [h]; rfl)
  have he:=(fields RationalCostModel.schoolbook p s f hf).2
  have hred:=PlayerSpecificAlgebraicPairStep.reduced RationalCostModel.schoolbook p.parameters.root
    (p.rows.read f.first).length (p.rows.read f.second).length (s.data.read f.first) (s.data.read f.second)
      hc.normalized hm0 (hc.lengths f.first) (hc.lengths f.second)
  have hres:=PlayerSpecificAlgebraicPairHeights.resources RationalCostModel.schoolbook p.parameters.root
    (p.rows.read f.first).length (p.rows.read f.second).length (s.data.read f.first) (s.data.read f.second)
      hc.normalized hm0 (hc.lengths f.first) (hc.lengths f.second) (hs.reduced f.first) (hs.reduced f.second)
        U (hl f.first) (hl f.second) (hr f.first) (hr f.second)
  have hprob:=PlayerSpecificAlgebraicPairHeights.probability RationalCostModel.schoolbook p.parameters.root
    (p.rows.read f.first).length (p.rows.read f.second).length (s.data.read f.first) (s.data.read f.second)
      hc.normalized hm0 hml (hc.lengths f.first) (hc.lengths f.second) (hs.reduced f.first) (hs.reduced f.second)
        U hmH (hl f.first) (hl f.second) (hr f.first) (hr f.second)
  rw [he]
  refine ⟨hred.2.2.2.2.2,hprob,?_⟩
  intro upper
  cases upper
  · simpa only [Bool.false_eq_true,ite_false] using ⟨⟨hred.2.2.2.1,hres.2.2.2.1⟩,⟨hred.2.2.2.2.1,hres.2.2.2.2⟩⟩
  · simpa only [ite_true] using ⟨⟨hred.2.1,hres.2.1⟩,⟨hred.2.2.1,hres.2.2.1⟩⟩

end Blotto.PlayerSpecificResourceStepSizes
