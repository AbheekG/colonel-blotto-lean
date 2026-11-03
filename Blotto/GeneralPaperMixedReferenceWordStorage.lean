import Blotto.GeneralPaperMixedValueLengthStorage

/-! Complete reference construction: actual A-priced scalar/scan work and
all partial/parent counters stored at physical width R. -/
namespace Blotto.GeneralPaperMixedReferenceWordStorage
open GeneralPaperEncodedScalarStorage (fields)
open GeneralPaperEqualAddressConstruction (price)
open GeneralPaperMixedPrimitiveStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def controls (model : RationalCostModel) (A K n k S b E : ℕ) : List ℕ :=
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
[p0, p0 + p1, p0 + p1 + p2, p0 + p1 + p2 + p3, p0 + p1 + p2 + p3 + counted.2, p0 + p1 + p2 + p3 + counted.2 + p4, p0 + p1 + p2 + p3 + counted.2 + p4 + p5, p0 + p1 + p2 + p3 + counted.2 + p4 + p5 + p6, F]

def footprint (model : RationalCostModel) (R A K n k S b E : ℕ) : ℕ :=
  let s0 := S + b
  let s1 := s0 + n
  let s2 := s1 + E
  let total := s2 + 1
  let counted := GeneralPaperStoredWordLength.run A total
  let base := 128 + k
  let L := base + counted.1
  let W := K * L
  scalarFoot model R A S b s0 +
    scalarFoot model R A s0 n s1 +
    scalarFoot model R A s1 E s2 +
    scalarFoot model R A s2 1 total +
    wordFoot R A total +
    scalarFoot model R A 128 k base +
    scalarFoot model R A base counted.1 L +
    scalarFoot model R A K L W +
    fields R (controls model A K n k S b E) +
    256 * R

theorem diagonal (model : RationalCostModel) (R K n k S b E : ℕ) :
    footprint model R R K n k S b E = GeneralPaperEqualReferenceWordLifetime.footprint model R K n k S b E := rfl

theorem le_diagonal (model : RationalCostModel) (R A K n k S b E : ℕ) (h : A ≤ R) :
    footprint model R A K n k S b E ≤ footprint model R R K n k S b E := by
  let s0 := S + b
  let s1 := s0 + n
  let s2 := s1 + E
  let total := s2 + 1
  let base := 128 + k
  let L := base + binaryWordWidth total
  let out := K * L
  have hp0 := price_mono model R A S b s0 h
  have hp1 := price_mono model R A s0 n s1 h
  have hp2 := price_mono model R A s1 E s2 h
  have hp3 := price_mono model R A s2 1 total h
  have hp4 := price_mono model R A 128 k base h
  have hp5 := price_mono model R A base (binaryWordWidth total) L h
  have hp6 := price_mono model R A K L out h
  have hpCount := word_price_mono R A total h
  have hpFull := GeneralPaperMeasuredInitializerMonotonicity.reference model A R h K n k S b E
  have hc := fields_mono R (controls model A K n k S b E) (controls model R K n k S b E) (by
    dsimp only [controls]
    simp only [GeneralPaperStoredWordLength.data]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil)))))))))
    all_goals dsimp only [s0, s1, s2, total, base, L, out] at *
    all_goals omega)
  have hs0 := scalar_le_diagonal model R A S b s0 h
  have hs1 := scalar_le_diagonal model R A s0 n s1 h
  have hs2 := scalar_le_diagonal model R A s1 E s2 h
  have hs3 := scalar_le_diagonal model R A s2 1 total h
  have hs4 := scalar_le_diagonal model R A 128 k base h
  have hs5 := scalar_le_diagonal model R A base (binaryWordWidth total) L h
  have hs6 := scalar_le_diagonal model R A K L out h
  have hw := word_le_diagonal R A total h
  simp only [footprint, GeneralPaperStoredWordLength.data]
  dsimp only [s0, s1, s2, total, base, L, out] at *
  omega

theorem bounded (model : RationalCostModel) (R A K n k S b E : ℕ) (h : A ≤ R) :
    footprint model R A K n k S b E ≤ GeneralPaperEqualReferenceWordLifetime.profile model R K n k S b E :=
  (le_diagonal model R A K n k S b E h).trans (by
    rw [diagonal]
    exact GeneralPaperEqualReferenceWordLifetime.source_bound model R K n k S b E)

end Blotto.GeneralPaperMixedReferenceWordStorage
