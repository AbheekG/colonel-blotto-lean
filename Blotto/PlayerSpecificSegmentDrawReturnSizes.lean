import Blotto.PlayerSpecificSegmentDrawPacketCost

/-! Original descriptor certificates derive every actual segment-draw
return size. No output-height witness is supplied to execution. -/
namespace Blotto.PlayerSpecificSegmentDrawReturnSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem bounds_mono {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (T U : ℕ) (h : T≤U) (hd : Bounds root d T) : Bounds root d U :=
  ⟨fun slot => ⟨(hd.weights slot).1,mono (hd.weights slot).2 h⟩,
    fun slot j => ⟨(hd.first slot j).1,mono (hd.first slot j).2 h⟩,
    fun slot j => ⟨(hd.second slot j).1,mono (hd.second slot j).2 h⟩⟩

theorem output {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots) (fallback : Fin slots) (T H K : ℕ)
    (bits : Fin ((slots-1)*H+K) → Bool) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmT : HasHeight root.polynomial T) (hd : Bounds root d T) :
    ∀ j,Reduced root.polynomial ((PlayerSpecificSegmentDrawExecution.run model root d fallback H K bits).1.read j) ∧
      HasHeight ((PlayerSpecificSegmentDrawExecution.run model root d fallback H K bits).1.read j)
        (PlayerSpecificSegmentDrawSizes.height N slots T H K) := by
  have hh:=PlayerSpecificAlgebraicSegmentHeights.sample model root d fallback H K bits hm hm0 hml T hmT hd.first hd.second
  intro j
  rw [PlayerSpecificSegmentDrawExecution.value]
  constructor
  · unfold PlayerSpecificAlgebraicSegmentSample.sample PlayerSpecificAlgebraicSegment.interpolate
    rw [FixedArrayTable.read_ofFn]
    exact PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0
  · exact mono (hh j) (by dsimp [PlayerSpecificSegmentDrawSizes.height]; omega)

end Blotto.PlayerSpecificSegmentDrawReturnSizes
