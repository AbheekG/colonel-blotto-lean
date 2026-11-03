import Blotto.GeneralPaperCategoricalCountCallbackLifetime

/-! Internal integer-data lifetime across denominator-product recursion,
count-array callbacks and the returned table. The cached denominator and
product-work record stay live during count construction. The caller owns
the source compact descriptor and earlier preparation data in borrowed. -/
namespace Blotto.GeneralPaperCategoricalIntegerLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def productTime (model : RationalCostModel) (A r s : ℕ) : ℕ :=
  r * GeneralPaperStoredCategoricalProduct.stepBound model A r s + 64 * A + 64

def arrayTime (model : RationalCostModel) (A r s : ℕ) : ℕ :=
  r * GeneralPaperStoredCategoricalCounts.stepBound model A r s + PaperIndexedArrayConstruction.overhead id A r r

def totalTime (model : RationalCostModel) (A r s : ℕ) : ℕ := productTime model A r s + arrayTime model A r s + 64 * A + 64

def productOwner {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) : ℕ :=
  let product := GeneralPaperStoredCategoricalProduct.run p.weights model A
  natBits product.1 + fields A [product.2] + 64 * A

def productOwnerProfile (model : RationalCostModel) (A r s : ℕ) : ℕ :=
  s * r + 2 + (natBits (productTime model A r s) + A) + 96 * A

theorem denominator_word {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) (h : ∀ i, RationalHeight (p.weights.read i) s) :
    natBits (GeneralPaperStoredCategoricalProduct.run p.weights model A).1 ≤ s * r + 2 := by
  have hw := GeneralPaperEqualCategoricalIntegerData.denominator_word p.lottery.weight h
  rw [← GeneralPaperStoredCategoricalProduct.prepared_data p model A] at hw
  unfold natBits
  omega

theorem product_owner_bound {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) (h : ∀ i, RationalHeight (p.weights.read i) s) :
    productOwner p model A ≤ productOwnerProfile model A r s := by
  have hD := denominator_word p model A h
  have hWork := GeneralPaperStoredCategoricalProduct.work p.weights model A h
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (productTime model A r s)
    [(GeneralPaperStoredCategoricalProduct.run p.weights model A).2] (by
      intro x hx
      rw [List.mem_singleton.mp hx]
      exact hWork)
  simp only [List.length_singleton, one_mul] at hFields
  unfold productOwner productOwnerProfile
  dsimp only
  omega

theorem count_word {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) (h : ∀ i, RationalHeight (p.weights.read i) s) (i : Fin r) :
    natBits (GeneralPaperStoredCategoricalCounts.coordinate p.weights model A
      (GeneralPaperStoredCategoricalProduct.run p.weights model A).1 i).1 ≤ s * r + 2 := by
  have hD := denominator_word p model A h
  have hNumeric := GeneralPaperStoredCategoricalCounts.numeric_bounds p _
    (GeneralPaperStoredCategoricalProduct.prepared_data p model A) i
  have hCount : (GeneralPaperStoredCategoricalCounts.coordinate p.weights model A
      (GeneralPaperStoredCategoricalProduct.run p.weights model A).1 i).1 ≤
      (GeneralPaperStoredCategoricalProduct.run p.weights model A).1 := hNumeric.2.2.2
  exact (Nat.add_le_add_left (binaryWordWidth_mono hCount) 1).trans hD

inductive Phase (r : ℕ) where
  | product (k : ℕ) (hk : k ≤ r)
  | count (i : Fin r)
  | returned

def window {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A borrowed : ℕ) : Phase r → ℕ
  | .product k hk => borrowed + GeneralPaperCategoricalProductLifetime.live p.weights model A k hk + 128 * A
  | .count i => GeneralPaperIndexedArrayLifetime.window id A
      (GeneralPaperStoredCategoricalCounts.coordinate p.weights model A (GeneralPaperStoredCategoricalProduct.run p.weights model A).1)
      natBits i.val i.isLt.le (borrowed + productOwner p model A)
      (GeneralPaperCategoricalCountCallbackLifetime.footprint p.weights model A
        (GeneralPaperStoredCategoricalProduct.run p.weights model A).1 i) + 128 * A
  | .returned =>
      let actual := GeneralPaperStoredCategoricalCounts.run p model A
      borrowed + natBits actual.1.D + arrayFootprint A natBits actual.1.counts +
        fields A [actual.2.1, actual.2.2] + 128 * A

def profile (model : RationalCostModel) (A r s borrowed : ℕ) : ℕ :=
  borrowed + 256 * (r + 1) * productTime model A r s + productOwnerProfile model A r s +
    arrayProfile A r (s * r + 2) + (r + 1) * GeneralPaperIndexedArrayLifetime.frame A r (arrayTime model A r s) +
    256 * GeneralPaperStoredCategoricalCounts.stepBound model A r s +
    2 * (natBits (totalTime model A r s) + A) + 160 * A

theorem borrowed_mono (model : RationalCostModel) (A r s B C : ℕ) (h : B ≤ C) :
    profile model A r s B ≤ profile model A r s C := by
  unfold profile
  omega

theorem all_phases {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) (h : ∀ i, RationalHeight (p.weights.read i) s)
    (borrowed : ℕ) (phase : Phase r) : window p model A borrowed phase ≤ profile model A r s borrowed := by
  have hOwner := product_owner_bound p model A h
  have hDenominator := denominator_word p model A h
  have hCoordinates := GeneralPaperStoredCategoricalCounts.coordinate_work p model A _
    (GeneralPaperStoredCategoricalProduct.prepared_data p model A) h
  cases phase with
  | product k hk =>
    have hProduct := GeneralPaperCategoricalProductLifetime.native_height_bound p.weights model A k hk h
    simp only [window, profile]
    unfold productTime
    omega
  | count i =>
    have hWindow := GeneralPaperIndexedArrayLifetime.window_bound id A
      (GeneralPaperStoredCategoricalCounts.coordinate p.weights model A (GeneralPaperStoredCategoricalProduct.run p.weights model A).1)
      natBits (s * r + 2) (256 * GeneralPaperStoredCategoricalCounts.stepBound model A r s)
      (count_word p model A h) i.val i.isLt.le (borrowed + productOwner p model A) _
      (GeneralPaperCategoricalCountCallbackLifetime.native_height_bound p model A _
        (GeneralPaperStoredCategoricalProduct.prepared_data p model A) h i)
    have hArrayWork := GeneralPaperPreparedSegmentCompaction.array_work r rfl A
      (GeneralPaperStoredCategoricalCounts.stepBound model A r s)
      (GeneralPaperStoredCategoricalCounts.coordinate p.weights model A (GeneralPaperStoredCategoricalProduct.run p.weights model A).1)
      hCoordinates
    rw [GeneralPaperSizedBitArray.eq_run] at hArrayWork
    change (PaperIndexedArrayConstruction.run id A
      (GeneralPaperStoredCategoricalCounts.coordinate p.weights model A
        (GeneralPaperStoredCategoricalProduct.run p.weights model A).1)).2 ≤ arrayTime model A r s at hArrayWork
    have hFrame := Nat.mul_le_mul_left (r + 1) (GeneralPaperIndexedArrayLifetime.frame_mono A r _ _ hArrayWork)
    simp only [window, profile]
    omega
  | returned =>
    have hWork := GeneralPaperStoredCategoricalCounts.work p model A h
    have hWord : ∀ i, natBits ((GeneralPaperStoredCategoricalCounts.run p model A).1.counts.read i) ≤ s * r + 2 := by
      intro i
      change natBits ((GeneralPaperSizedBitArray.run p.weights.data.size p.weights.size A
        (GeneralPaperStoredCategoricalCounts.coordinate p.weights model A (GeneralPaperStoredCategoricalProduct.run p.weights model A).1)).1.read i) ≤ _
      rw [GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
      exact count_word p model A h i
    have hPayload := array_bound A (s * r + 2) natBits (GeneralPaperStoredCategoricalCounts.run p model A).1.counts hWord
    have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (totalTime model A r s)
      [(GeneralPaperStoredCategoricalCounts.run p model A).2.1, (GeneralPaperStoredCategoricalCounts.run p model A).2.2] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> unfold totalTime productTime arrayTime <;> omega)
    change fields A _ ≤ 2 * (natBits (totalTime model A r s) + A) + 32 * A at hFields
    simp only [window, profile]
    change natBits (GeneralPaperStoredCategoricalCounts.run p model A).1.D ≤ _ at hDenominator
    unfold productOwnerProfile
    omega

end Blotto.GeneralPaperCategoricalIntegerLifetime
