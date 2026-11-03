import Blotto.GeneralPaperPreparedSourceCompilerPair

/-! Change erased row/label size proofs without changing stored columns.
Cached runtime sizes remain the controls used by native construction. -/
namespace Blotto.GeneralPaperColumnPairReindex
open GeneralPaperOriginalDrawEquilibrium
set_option autoImplicit false

def run {T U m K L : ℕ} (hT : T=U) (hK : K=L) (physical : Columns T m K) : Columns U m L := by
  subst U
  subst L
  exact physical

theorem reflexive {T m K : ℕ} (physical : Columns T m K) : run rfl rfl physical=physical := rfl

theorem map_reflexive {T m K : ℕ} (physical : Option (Columns T m K)) : physical.map (run rfl rfl)=physical := by
  cases physical <;> rfl

end Blotto.GeneralPaperColumnPairReindex
