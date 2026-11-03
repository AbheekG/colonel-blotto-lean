import Blotto.GeneralPaperRetainedModifiedColumns

/-! Erased decoding of the returned physical pair. This is not a data-path
dictionary constructor: the evaluator keeps both stored column arrays. -/
namespace Blotto.GeneralPaperPhysicalColumnPair
open GeneralPaperOriginalDrawEquilibrium
set_option autoImplicit false

def decode {T m K : ℕ} (physical : Columns T m K) : GeneralPaperSourcePairRun.Pair T m K :=
  ⟨GeneralPaperRowQuantizer.dictionary physical.rich,GeneralPaperRowQuantizer.dictionary physical.poor⟩

theorem matches_iff {T m K : ℕ} (physical : Columns T m K) (pair : GeneralPaperSourcePairRun.Pair T m K) :
    Matches physical pair ↔ decode physical=pair := by
  cases pair
  simp only [Matches,decode,GeneralPaperSourcePairRun.Pair.mk.injEq]

theorem rich_map {T m K : ℕ} (rich : Option (FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)))
    (poor : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    (rich.map (fun r => (⟨r,poor⟩ : Columns T m K))).map decode=
      (rich.map GeneralPaperRowQuantizer.dictionary).map (fun r => (⟨r,GeneralPaperRowQuantizer.dictionary poor⟩ : GeneralPaperSourcePairRun.Pair T m K)) := by
  cases rich <;> rfl

theorem poor_map {T m K : ℕ} (rich : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (poor : Option (FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))) :
    (poor.map (fun p => (⟨rich,p⟩ : Columns T m K))).map decode=
      (poor.map GeneralPaperRowQuantizer.dictionary).map (fun p => (⟨GeneralPaperRowQuantizer.dictionary rich,p⟩ : GeneralPaperSourcePairRun.Pair T m K)) := by
  cases poor <;> rfl

end Blotto.GeneralPaperPhysicalColumnPair
