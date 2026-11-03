import Blotto.PlayerSpecificAlgebraicReflectAppend

/-! The actual reached reflected state supplies every terminal row;
the real terminal witness and all row bounds are derived from that path. -/
namespace Blotto.PlayerSpecificAlgebraicFourReflectedTerminal
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def input (p : PlayerSpecificAlgebraicFourReflectedInput.Prepared) (s : State 3) : PlayerSpecificAlgebraicNestedTerminalInput.Input :=
  ⟨p.budget,p.long,p.short,FixedArrayTable.ofFn (fun j => (p.resources.rows.read j).length),s.data⟩

theorem values (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hcase : i.w < (1-i.p)*i.ell) (s : State 3)
    (hs : (i.reflectedResourceSystem hcase).Valid (eval s x)) :
    PlayerSpecificAlgebraicNestedTerminalInput.Values
      (input (PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a) s)
      ((i.reflectedResourceSystem hcase).terminal (eval s x) hs) x := by
  have hp := PlayerSpecificAlgebraicFourReflectedInput.values RationalCostModel.schoolbook r a i hm hirr hv x hx ha T hfit hcase
  refine ⟨hp.2.2.2.2,hp.1,hp.2.1,?_,fun _ => rfl⟩
  intro j
  simp only [input,FixedArrayTable.read_ofFn]
  exact hp.2.2.1 j

theorem fits (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (hcase : i.w < (1-i.p)*i.ell) (H : ℕ) (bits : Fin (2*H) → Bool) :
    PlayerSpecificAlgebraicNestedTerminalSizes.Fits r.root
      (input (PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a)
        (PlayerSpecificAlgebraicFourReflectedPath.draw r a H bits).1) (iterate 16 T) := by
  have hm0 : r.root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hp := PlayerSpecificAlgebraicFourReflectedSizes.bounds RationalCostModel.schoolbook r a T hfit hm hm0 hml hmT hT
  have hr := (PlayerSpecificAlgebraicFourReflectedPath.contract r a i hm hirr hv x hx ha T hfit hml hmT hT hcase H bits).1.reduced
  have hh := PlayerSpecificAlgebraicFourReflectedPath.heights r a hm hirr hv x hx T hfit hml hmT hT H bits
  have hi := PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 15 ≤ 16)
  refine ⟨⟨hp.2.2.2.1,mono hp.2.2.2.2 hi⟩,fun j => ⟨(hp.1 j).1,mono (hp.1 j).2 hi⟩,
    fun j => ⟨(hp.2.1 j).1,mono (hp.2.1 j).2 hi⟩,?_,fun j => ⟨hr j,hh j⟩⟩
  intro j
  simp only [input,FixedArrayTable.read_ofFn]
  exact ⟨(hp.2.2.1 j).1.1,mono (hp.2.2.1 j).1.2 hi⟩

end Blotto.PlayerSpecificAlgebraicFourReflectedTerminal
