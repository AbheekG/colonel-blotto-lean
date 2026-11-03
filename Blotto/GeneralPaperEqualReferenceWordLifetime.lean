import Blotto.GeneralPaperValueInputLengthLifetime

/-! All seven actual reference-construction scalars, the stored-word scan,
local scratch, partial prices and exact final work/return metadata. The
reserve is analysis only and adds no source width or memory census. -/
namespace Blotto.GeneralPaperEqualReferenceWordLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperEqualAddressConstruction (price)
open GeneralPaperAddressConstructionLifetime (scalarFoot scalar_bound)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def footprint (model : RationalCostModel) (A K n k S b E : ℕ) : ℕ :=
  let s0 := S + b
  let s1 := s0 + n
  let s2 := s1 + E
  let total := s2 + 1
  let counted := GeneralPaperStoredWordLength.run A total
  let base := 128 + k
  let L := base + counted.1
  let W := K * L
  let p0 := price model A S b s0
  let p1 := price model A s0 n s1
  let p2 := price model A s1 E s2
  let p3 := price model A s2 1 total
  let p4 := price model A 128 k base
  let p5 := price model A base counted.1 L
  let p6 := price model A K L W
  let F := (GeneralPaperEqualReferenceConstruction.run model A K n k S b E).2
  scalarFoot model A S b s0 +
    scalarFoot model A s0 n s1 +
    scalarFoot model A s1 E s2 +
    scalarFoot model A s2 1 total +
    GeneralPaperWordLengthLifetime.footprint A total +
    scalarFoot model A 128 k base +
    scalarFoot model A base counted.1 L +
    scalarFoot model A K L W +
    fields A [p0, p0 + p1, p0 + p1 + p2, p0 + p1 + p2 + p3, p0 + p1 + p2 + p3 + counted.2, p0 + p1 + p2 + p3 + counted.2 + p4, p0 + p1 + p2 + p3 + counted.2 + p4 + p5, p0 + p1 + p2 + p3 + counted.2 + p4 + p5 + p6, F] +
    256 * A

theorem bounded (model : RationalCostModel) (A K n k S b E : ℕ) :
    footprint model A K n k S b E ≤ 1024 * (GeneralPaperEqualReferenceConstruction.run model A K n k S b E).2 := by
  let s0 := S + b
  let s1 := s0 + n
  let s2 := s1 + E
  let total := s2 + 1
  let counted := GeneralPaperStoredWordLength.run A total
  let base := 128 + k
  let L := base + counted.1
  let W := K * L
  let p0 := price model A S b s0
  let p1 := price model A s0 n s1
  let p2 := price model A s1 E s2
  let p3 := price model A s2 1 total
  let p4 := price model A 128 k base
  let p5 := price model A base counted.1 L
  let p6 := price model A K L W
  let F := (GeneralPaperEqualReferenceConstruction.run model A K n k S b E).2
  have hF : F = p0 + p1 + p2 + p3 + counted.2 + p4 + p5 + p6 + 128 * A + 128 := rfl
  have hCount := GeneralPaperWordLengthLifetime.bounded A total
  change GeneralPaperWordLengthLifetime.footprint A total ≤ 32 * counted.2 at hCount
  have h0 := scalar_bound model A S b s0
  change scalarFoot model A S b s0 ≤ 32 * p0 at h0
  have h1 := scalar_bound model A s0 n s1
  change scalarFoot model A s0 n s1 ≤ 32 * p1 at h1
  have h2 := scalar_bound model A s1 E s2
  change scalarFoot model A s1 E s2 ≤ 32 * p2 at h2
  have h3 := scalar_bound model A s2 1 total
  change scalarFoot model A s2 1 total ≤ 32 * p3 at h3
  have h4 := scalar_bound model A 128 k base
  change scalarFoot model A 128 k base ≤ 32 * p4 at h4
  have h5 := scalar_bound model A base counted.1 L
  change scalarFoot model A base counted.1 L ≤ 32 * p5 at h5
  have h6 := scalar_bound model A K L W
  change scalarFoot model A K L W ≤ 32 * p6 at h6
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A F
    [p0, p0 + p1, p0 + p1 + p2, p0 + p1 + p2 + p3, p0 + p1 + p2 + p3 + counted.2, p0 + p1 + p2 + p3 + counted.2 + p4, p0 + p1 + p2 + p3 + counted.2 + p4 + p5, p0 + p1 + p2 + p3 + counted.2 + p4 + p5 + p6, F] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A [p0, p0 + p1, p0 + p1 + p2, p0 + p1 + p2 + p3, p0 + p1 + p2 + p3 + counted.2, p0 + p1 + p2 + p3 + counted.2 + p4, p0 + p1 + p2 + p3 + counted.2 + p4 + p5, p0 + p1 + p2 + p3 + counted.2 + p4 + p5 + p6, F] ≤ 9 * (natBits F + A) + 32 * A at hFields
  have hCounter := GeneralPaperNaturalScalarLifetime.counter_word F
  unfold footprint
  change scalarFoot model A S b s0 +
    scalarFoot model A s0 n s1 +
    scalarFoot model A s1 E s2 +
    scalarFoot model A s2 1 total +
    GeneralPaperWordLengthLifetime.footprint A total +
    scalarFoot model A 128 k base +
    scalarFoot model A base counted.1 L +
    scalarFoot model A K L W +
    fields A [p0, p0 + p1, p0 + p1 + p2, p0 + p1 + p2 + p3, p0 + p1 + p2 + p3 + counted.2, p0 + p1 + p2 + p3 + counted.2 + p4, p0 + p1 + p2 + p3 + counted.2 + p4 + p5, p0 + p1 + p2 + p3 + counted.2 + p4 + p5 + p6, F] +
    256 * A ≤ 1024 * F
  omega

def profile (model : RationalCostModel) (A K n k S b E : ℕ) : ℕ :=
  1024 * GeneralPaperEqualReferenceConstruction.profile model A K n k S b E

theorem source_bound (model : RationalCostModel) (A K n k S b E : ℕ) :
    footprint model A K n k S b E ≤ profile model A K n k S b E :=
  (bounded model A K n k S b E).trans
    (Nat.mul_le_mul_left 1024 (GeneralPaperEqualReferenceConstruction.work model A K n k S b E))

end Blotto.GeneralPaperEqualReferenceWordLifetime
