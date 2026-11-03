import Blotto.PlayerSpecificFourReflectedTerminalExecution

/-! The reached reflected terminal conversion copies all original resource
fields and all thirteen terminal fields within the original-height envelope. -/
namespace Blotto.PlayerSpecificFourReflectedTerminalSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (T : ℕ) : ℕ :=
  (6000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(iterate 16 T+21)^3+28

theorem cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (x : ℝ) (T H : ℕ) (bits : Fin (2*H) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo<r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length≤4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2≤T)
    (hcase : i.w < (1-i.p)*i.ell) :
    (PlayerSpecificFourReflectedTerminalExecution.run RationalCostModel.schoolbook r.root
      (PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a)
      (PlayerSpecificAlgebraicFourReflectedPath.draw r a H bits).1).2≤work T := by
  let model:=RationalCostModel.schoolbook
  let p:=PlayerSpecificAlgebraicFourReflectedInput.prepare model r a
  let s:=(PlayerSpecificAlgebraicFourReflectedPath.draw r a H bits).1
  let terminal:=PlayerSpecificAlgebraicFourReflectedTerminal.input p s
  let S:=iterate 16 T+20
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hb:=PlayerSpecificAlgebraicFourReflectedSizes.bounds model r a T hfit hm hm0 hml hmT hT
  have h15:=PlayerSpecificAlgebraicExpressionBudget.initial_le 15 T
  have h16:=PlayerSpecificAlgebraicExpressionBudget.initial_le 16 T
  have h1516:=PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 15≤16)
  have hTS : T≤S := by dsimp only [S]; omega
  have h15S : iterate 15 T≤S := h1516.trans (by dsimp only [S]; omega)
  have h16S : iterate 16 T≤S := by dsimp only [S]; omega
  have hcopy : ∀ j,(p.resources.rows.read j).initialB=(p.resources.rows.read j).initialA := by
    intro j
    dsimp only [p]
    simp only [PlayerSpecificAlgebraicFourReflectedInput.prepare,FixedArrayTable.read_ofFn]
  have hpfields : ∀ j,Reduced r.root.polynomial ((PlayerSpecificFourReflectedInputExecution.fields p).read j) ∧
      HasHeight ((PlayerSpecificFourReflectedInputExecution.fields p).read j) (iterate 15 T) := by
    intro j
    fin_cases j
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.1 0
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.1 1
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.1 2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.2.1 0
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.2.1 1
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.2.1 2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using (hb.2.2.1 0).1
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using (hb.2.2.1 1).1
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using (hb.2.2.1 2).1
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using (hb.2.2.1 0).2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using (hb.2.2.1 1).2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using (hb.2.2.1 2).2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn,hcopy] using (hb.2.2.1 0).2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn,hcopy] using (hb.2.2.1 1).2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn,hcopy] using (hb.2.2.1 2).2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.2.2.2
  have ht:=PlayerSpecificAlgebraicFourReflectedTerminal.fits r a i hm hirr hv x hx ha T hfit hml hmT hT hcase H bits
  have htfields : ∀ j,Reduced r.root.polynomial ((PlayerSpecificFourReflectedTerminalExecution.fields terminal).read j) ∧
      HasHeight ((PlayerSpecificFourReflectedTerminalExecution.fields terminal).read j) (iterate 16 T) := by
    intro j
    fin_cases j
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.budget
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.long 0
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.long 1
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.long 2
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.short 0
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.short 1
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.short 2
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.capacity 0
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.capacity 1
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.capacity 2
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.resource 0
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.resource 1
    · simpa [PlayerSpecificFourReflectedTerminalExecution.fields,FixedArrayTable.read_ofFn] using ht.resource 2
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model r.root
    (PlayerSpecificFourReflectedInputExecution.fields p)
    (PlayerSpecificFourReflectedTerminalExecution.fields terminal) S
    (mono hmT hTS) hml (mono he hTS)
    (fun j => ⟨mono (hpfields j).2 h15S,by have h:=(hpfields j).1.2; omega⟩)
    (fun j => ⟨mono (htfields j).2 h16S,by have h:=(htfields j).1.2; omega⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hf':=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 6000 S)
  rw [show S+1=iterate 16 T+21 by rfl] at hf'
  change price model (PlayerSpecificExpressionVectorExecution.frame r.root
    (PlayerSpecificFourReflectedInputExecution.fields p)
    (PlayerSpecificFourReflectedTerminalExecution.fields terminal))+price model PlayerSpecificFourReflectedTerminalExecution.packing≤_
  rw [PlayerSpecificFourReflectedTerminalExecution.packing_cost]
  unfold work
  exact Nat.add_le_add_right hf' 28

end Blotto.PlayerSpecificFourReflectedTerminalSourceCost
