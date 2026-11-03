import Blotto.GeneralPaperEqualSelectedCopyControls

/-! Complete selected-copy lifetime: original branch and outer record,
copied mixed-width closure, actual branch children, address-copy scratch and
all saved outer copy prices/partial sums. -/
namespace Blotto.GeneralPaperEqualSelectedCopyLifetime
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEncodedScalarStorage
open GeneralPaperEqualBitDrawRates (log)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def sourceHeader (S A : ℕ) : ℕ := fields S [A] + 64 * S

theorem header_bound (S A D : ℕ) (hA : A ≤ D) : sourceHeader S A ≤ natBits D + 97 * S := by
  have h := Nat.add_le_add_left (binaryWordWidth_mono hA) 1
  unfold sourceHeader fields
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  change natBits A ≤ natBits D at h
  omega

def window {n : ℕ} (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (a : Sampler v k budget)
    (cursor : GeneralPaperEqualSelectedCopyComponents.Cursor a) : ℕ :=
  GeneralPaperEqualSelectedBranchOwner.footprint S a.branch + sourceHeader S a.address +
    GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualSelectedCopy.run S a).1 +
    GeneralPaperEqualSelectedCopyComponents.window S a.address a.branch cursor +
    GeneralPaperScalarTableCopyLifetime.scalarWindow S a.address natBits a.address +
    GeneralPaperEqualSelectedCopyControls.window S a

def profile (S n k b : ℕ) : ℕ :=
  GeneralPaperEqualSelectedBranchOwner.profile S n k b + natBits (2 * log n k b + 1) + 97 * S +
    2 * GeneralPaperEqualDescriptionRates.paperBound n k b +
    GeneralPaperEqualSelectedCopyComponents.profile S n k b +
    GeneralPaperScalarTableCopyLifetime.scalarProfile S (2 * log n k b + 1) (natBits (2 * log n k b + 1)) +
    GeneralPaperEqualSelectedCopyControls.profile S n k b

theorem all_cursors {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (cursor : GeneralPaperEqualSelectedCopyComponents.Cursor a) :
    window S a cursor ≤ profile S n k (rationalWordWidth budget) := by
  have hSource := GeneralPaperEqualSelectedBranchOwner.bounded model W S k values v hv budget a.branch
  have hA := GeneralPaperEqualSelectedSampler.address_bound a
  have hHeader := header_bound S a.address _ hA
  have hTarget := GeneralPaperEqualSelectedDescription.paper_bound model W k values v hv budget
    (GeneralPaperEqualSelectedCopy.run S a).1
  have hChildren := GeneralPaperEqualSelectedCopyComponents.bounded model W S k values v hv budget a cursor
  have hAddress := GeneralPaperScalarTableCopyLifetime.scalar_bound S a.address
    (natBits (2 * log n k (rationalWordWidth budget) + 1)) natBits a.address
    (Nat.add_le_add_left (binaryWordWidth_mono hA) 1)
  have hAddressMono := GeneralPaperScalarCopyLifetimeMonotone.scalar S hA
    (le_rfl : natBits (2 * log n k (rationalWordWidth budget) + 1) ≤ natBits (2 * log n k (rationalWordWidth budget) + 1))
  have hControls := GeneralPaperEqualSelectedCopyControls.bounded model W S k values v hv budget a
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperEqualSelectedCopyLifetime
