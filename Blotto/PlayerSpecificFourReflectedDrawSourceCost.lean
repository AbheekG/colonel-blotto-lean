import Blotto.PlayerSpecificFourReflectedDrawExecution

/-! Complete source work for the reached reflected component, including
both bit blocks, the adaptive path, terminal conversion, nested draw and
coordinate reflection from the original four-input height. -/
namespace Blotto.PlayerSpecificFourReflectedDrawSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def packetSize (H K : ℕ) : ℕ := (2*H)+((17*H+K)+K)
def outputHeight (T K : ℕ) : ℕ := PlayerSpecificNestedTerminalDrawSourceCost.outputHeight (iterate 16 T) K
def work (T H K : ℕ) : ℕ :=
  PlayerSpecificBitSlicePolynomial.coefficient*(packetSize H K+1)^3+
  PlayerSpecificBitSlicePolynomial.coefficient*(packetSize H K+1)^3+
  PlayerSpecificFourReflectedPathSourceCost.work T H+
  PlayerSpecificFourReflectedTerminalSourceCost.work T+
  PlayerSpecificNestedTerminalDrawSourceCost.work (iterate 16 T) H K+
  PlayerSpecificReflectAppendSourceCost.work (outputHeight T K)+2

theorem cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (x : ℝ) (T H K : ℕ) (bits : Fin ((2*H)+((17*H+K)+K)) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo<r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length≤4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2≤T)
    (hcase : i.w < (1-i.p)*i.ell) :
    (PlayerSpecificFourReflectedDrawExecution.run r a H K bits).2≤work T H K := by
  let model:=RationalCostModel.schoolbook
  let M:=packetSize H K
  let head:=PlayerSpecificBitSliceExecution.run model M 0 (2*H) (by dsimp only [M,packetSize]; omega) bits
  let inner:=PlayerSpecificBitSliceExecution.run model M (2*H) ((17*H+K)+K) (by dsimp only [M,packetSize]; omega) bits
  let path:=PlayerSpecificFourReflectedPathExecution.runCached r a H head.1
  let terminal:=PlayerSpecificFourReflectedTerminalExecution.run model r.root path.1.1 path.1.2.1
  let sampled:=PlayerSpecificNestedTerminalDrawExecution.run model r.root terminal.1 H K inner.1
  let W:=outputHeight T K
  let reflected:=PlayerSpecificReflectAppendExecution.run model r.root path.1.1.long sampled.1
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have h16:=PlayerSpecificAlgebraicExpressionBudget.initial_le 16 T
  have h1516:=PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 15≤16)
  have hTW : T≤W := h16.trans (PlayerSpecificNestedTerminalDrawSourceCost.height_lower (iterate 16 T) K)
  have h16W : iterate 16 T≤W := PlayerSpecificNestedTerminalDrawSourceCost.height_lower (iterate 16 T) K
  have h15W : iterate 15 T≤W := h1516.trans h16W
  have hhead:=PlayerSpecificBitSlicePolynomial.cost M 0 (2*H) (by dsimp only [M,packetSize]; omega) bits
  have hinner:=PlayerSpecificBitSlicePolynomial.cost M (2*H) ((17*H+K)+K)
    (by dsimp only [M,packetSize]; omega) bits
  have hpath : path.2≤PlayerSpecificFourReflectedPathSourceCost.work T H := by
    rw [PlayerSpecificFourReflectedPathExecution.cached_cost]
    exact PlayerSpecificFourReflectedPathSourceCost.cost r a x T H head.1 hm hirr hv hx hfit hml hmT he hT
  have hpval : path.1.1=PlayerSpecificAlgebraicFourReflectedInput.prepare model r a :=
    PlayerSpecificFourReflectedPathExecution.cached_input_value r a H head.1
  have hsval : path.1.2.1=(PlayerSpecificAlgebraicFourReflectedPath.draw r a H head.1).1 := by
    have h:=PlayerSpecificFourReflectedPathExecution.cached_state_value r a H head.1
    exact congrArg Prod.fst h
  have hterminal : terminal.2≤PlayerSpecificFourReflectedTerminalSourceCost.work T := by
    dsimp only [terminal]
    rw [hpval,hsval]
    exact PlayerSpecificFourReflectedTerminalSourceCost.cost r a i x T H head.1 hm hirr hv hx ha hfit hml hmT he hT hcase
  have htval : terminal.1=PlayerSpecificAlgebraicFourReflectedTerminal.input
      (PlayerSpecificAlgebraicFourReflectedInput.prepare model r a)
      (PlayerSpecificAlgebraicFourReflectedPath.draw r a H head.1).1 := by
    dsimp only [terminal]
    rw [PlayerSpecificFourReflectedTerminalExecution.value,hpval,hsval]
  have hfits : PlayerSpecificAlgebraicNestedTerminalSizes.Fits r.root terminal.1 (iterate 16 T) := by
    rw [htval]
    exact PlayerSpecificAlgebraicFourReflectedTerminal.fits r a i hm hirr hv x hx ha T hfit hml hmT hT hcase H head.1
  have hnested:=PlayerSpecificNestedTerminalDrawSourceCost.cost r.root terminal.1 (iterate 16 T) H K inner.1
    hm hm0 hml (mono hmT h16) (mono he h16) hv (hT.trans h16) hfits
  have hy : ∀ j,Reduced r.root.polynomial (sampled.1.read j) ∧ HasHeight (sampled.1.read j) W := by
    intro j
    dsimp only [sampled]
    rw [PlayerSpecificNestedTerminalDrawExecution.value]
    exact PlayerSpecificAlgebraicNestedTerminalDraw.bounds model r.root terminal.1 (iterate 16 T) hfits
      hm hm0 hml (mono hmT h16) (hT.trans h16) H K inner.1 j
  have hb:=PlayerSpecificAlgebraicFourReflectedSizes.bounds model r a T hfit hm hm0 hml hmT hT
  have hlong : ∀ j,Reduced r.root.polynomial (path.1.1.long.read j) ∧
      HasHeight (path.1.1.long.read j) W := by
    intro j
    rw [hpval]
    exact ⟨(hb.1 j).1,mono (hb.1 j).2 h15W⟩
  have hreflect:=PlayerSpecificReflectAppendSourceCost.cost r.root path.1.1.long sampled.1 W
    hm hm0 hml (mono hmT hTW) (mono he hTW) (by omega) hlong hy
  change head.2+inner.2+path.2+terminal.2+sampled.2+reflected.2+
    price model [.control 1]≤_
  rw [show price model [.control 1]=2 by rfl]
  unfold work
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add hhead hinner) hpath) hterminal) hnested) hreflect) 2

theorem same_return_and_cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (x : ℝ) (T H K : ℕ) (bits : Fin ((2*H)+((17*H+K)+K)) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo<r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length≤4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2≤T)
    (hcase : i.w < (1-i.p)*i.ell) :
    (PlayerSpecificFourReflectedDrawExecution.run r a H K bits).1=
      PlayerSpecificAlgebraicFourReflectedDraw.draw r a H K bits ∧
    (PlayerSpecificFourReflectedDrawExecution.run r a H K bits).2≤work T H K :=
  ⟨PlayerSpecificFourReflectedDrawExecution.value r a H K bits,
    cost r a i x T H K bits hm hirr hv hx ha hfit hml hmT he hT hcase⟩

end Blotto.PlayerSpecificFourReflectedDrawSourceCost
