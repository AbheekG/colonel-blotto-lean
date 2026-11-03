import Blotto.GeneralPaperOrderedNativeOptionProfits

/-! Derive the optimizer's input-profit domain from per-field weights and
actual native option numerators. Capacities add along the same balanced tree.
The source still must construct the option catalogue, padded tree and total
rounded-value weight; no optimizer-quality oracle is introduced.
-/
namespace Blotto.GeneralPaperOrderedProfitCapacity
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperOrderedProfitDP GeneralPaperOrderedProfitSound GeneralPaperOrderedProfitTreeBounds
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
set_option maxHeartbeats 3500000

def Capacity {K : ℕ} (D : ℕ) : {h : ℕ} → Tree R K h → ℕ → Prop
  | _,.leaf field,weight => ∀ a, (field.read a).1≤2*D*weight
  | _,.node left right,weight => ∃ wl wr, Capacity D left wl ∧ Capacity D right wr ∧ weight=wl+wr

theorem realized_bound {K h : ℕ} (D : ℕ) (tree : Tree R K h) (weight : ℕ) (hCapacity : Capacity D tree weight)
    (labels : List (Fin K)) (cost : R) (P : ℕ) (hRealizes : Realizes tree labels cost P) : P≤2*D*weight := by
  induction tree generalizing weight labels cost P with
  | leaf field =>
    obtain ⟨a,rfl,rfl,rfl⟩ := hRealizes
    exact hCapacity a
  | node left right ihl ihr =>
    obtain ⟨wl,wr,hcl,hcr,rfl⟩ := hCapacity
    obtain ⟨ll,lc,lp,rr,rc,rp,hl,hr,rfl,rfl,rfl⟩ := hRealizes
    have ha := ihl wl hcl ll lc lp hl
    have hb := ihr wr hcr rr rc rp hr
    have he := Nat.add_le_add ha hb
    simpa only [Nat.mul_add] using he

theorem native_leaf {K : ℕ} (k U T weight : ℕ) (summary values : Summary k) (hTotal : 0<∑ r, values.read r)
    (codes : FixedArrayTable K ℕ) (tags : FixedArrayTable K R) :
    Capacity (2*T*(GeneralPaperSourceParameters.prepare k).meshDenominator)
      (.leaf (GeneralPaperOrderedNativeOptionProfits.build k T weight (GeneralPaperEpochPrefixArray.build values)
        (GeneralPaperOrderedNativeOptionProfits.prepare k U summary codes tags)).1) weight :=
  GeneralPaperOrderedNativeOptionProfits.numerator_bound k U T weight summary values hTotal codes tags

theorem source_bounded {K h : ℕ} (m lambda k Qv : ℕ) (tree : Tree R K h)
    (hCapacity : Capacity (2*(GeneralPaperTrajectoryParameters.prepare lambda k).rows*(GeneralPaperSourceParameters.prepare k).meshDenominator) tree Qv) :
    BoundedProfit (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf tree := by
  intro labels cost P hRealizes
  have he := realized_bound _ tree Qv hCapacity labels cost P hRealizes
  rw [GeneralPaperProfitParameters.qProf_spec]
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using he

end Blotto.GeneralPaperOrderedProfitCapacity
