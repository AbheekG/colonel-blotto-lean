import Blotto.GeneralPaperStoredFreshCollect

/-! The executed fresh-word reader loads its ruler count before scanning.
Its source correspondence preserves bits, random-source state, read count
and the exact local countdown/read/copy work. -/
namespace Blotto.GeneralPaperStoredFreshRead
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

structure Result (S : Type*) where
  bits : Option (List Bool)
  state : S
  reads : ℕ
  work : ℕ

def read {S : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (next : S → Bool × S) (state : S) : Result S :=
  let count := GeneralPaperStoredRulerRead.read model A installed
  match count.1 with
  | none => ⟨none,state,0,count.2 + 64 * (A + 1)⟩
  | some size =>
    let actual := GeneralPaperStoredFreshCollect.collect model A next size [] state
    ⟨some actual.bits,actual.state,actual.reads,count.2 + actual.work + 128 * (A + 1)⟩

theorem on_count {S : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (next : S → Bool × S) (state : S) (size : ℕ)
    (hCount : (GeneralPaperStoredRulerRead.read model A installed).1 = some size) :
    (read model A installed next state).bits = some (GeneralPaperStoredFreshCollect.collect model A next size [] state).bits ∧
      (read model A installed next state).state = (GeneralPaperStoredFreshCollect.collect model A next size [] state).state ∧
      (read model A installed next state).reads = size ∧
      (read model A installed next state).work = (GeneralPaperStoredRulerRead.read model A installed).2 +
        GeneralPaperStoredFreshCollect.price model A size 0 + 128 * (A + 1) := by
  simp only [read,hCount,GeneralPaperStoredFreshCollect.reads,GeneralPaperStoredFreshCollect.work,List.length_nil,and_self]

theorem source {S : Type*} {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {prepared : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared) (next : S → Bool × S) (state : S)
    (hCount : (GeneralPaperStoredRulerRead.read model A installed).1 = some prepared.rangeBits) :
    (read model A installed next state).bits = some (GeneralPaperEqualBooleanTrial.readWord cache next state).1.1.bits ∧
      (read model A installed next state).state = (GeneralPaperEqualBooleanTrial.readWord cache next state).1.2 ∧
      (read model A installed next state).reads = prepared.rangeBits ∧
      (read model A installed next state).work = (GeneralPaperStoredRulerRead.read model A installed).2 +
        GeneralPaperStoredFreshCollect.price model A prepared.rangeBits 0 + 128 * (A + 1) := by
  obtain ⟨hv,hs,hr,hw⟩ := on_count model A installed next state prepared.rangeBits hCount
  have hd := GeneralPaperStoredFreshCollect.data model A next cache.ruler [] state
  rw [cache.ruler_length] at hd
  exact ⟨hv.trans (congrArg some hd.1),hs.trans hd.2,hr,hw⟩

theorem source_length {S : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (next : S → Bool × S) (state : S) (size : ℕ)
    (hCount : (GeneralPaperStoredRulerRead.read model A installed).1 = some size) :
    ((read model A installed next state).bits.map List.length) = some (size + 1) := by
  rw [(on_count model A installed next state size hCount).1,Option.map_some,GeneralPaperStoredFreshCollect.length]
  rfl

end Blotto.GeneralPaperStoredFreshRead
