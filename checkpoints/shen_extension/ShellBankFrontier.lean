import checkpoints.shen_extension.ShellBankOrders
import checkpoints.shen_extension.BalancedShellOrder
import checkpoints.shen_extension.SinkLayerWindow
import checkpoints.shen_extension.WideShellOrder
import checkpoints.shen_extension.OddShellOrder
import checkpoints.shen_extension.DiagonalShellTransfer
import checkpoints.shen_extension.SymmetricUniformProfile

namespace LeanCH.BR.ShellBankFrontier
open Finset BRq2 BRq3 BR45 BRsGen CHRuleCatalog RetainedLayerCapacity ShellBankOrders

/-- Choose the greatest lower bound furnished by the three proved capacity
tests at the specified cutoff and retained degree. Arithmetic only. -/
private def earlyFloor (q d : ℕ) : ℕ :=
  max (if MixedRoom q d then 5*d else 0)
    (max (if SymmetricRoom d q then (if d≤2*q-2 then 6*d-1 else 6*d-2) else 0)
         (if 7≤q ∧ 6≤d ∧ d≤q+1 ∧ FourthRoom d then
            (if ShellProfileCapacity.Capacity d then 7*d else 7*d-1) else 0))

private def ranks (q d : ℕ) := (Icc 2 5).filter (UniformProfileCapacity.Fits q d)

private def profileFloor (q d : ℕ) : ℕ :=
  if (ranks q d).Nonempty then
    max (if MixedShellUniform.Room q d then 5*d+1 else 0)
        (if SymmetricUniformProfile.Capacity q d then 6*d else 0)
  else 0

def localFloor (q d : ℕ) : ℕ :=
  max (DiagonalShellTransfer.orderFloor q d) <|
  max (if OddShellOrder.Capacity q d (q/2) (q-q/2) then 9*d+1 else 0) <|
  max (profileFloor q d) <|
  max (earlyFloor q d)
    (if 10≤q ∧ WideShellOrder.Capacity q d (min d (q/2)) then 10*d+1 else 0)

/-- The contribution from any smaller retained degree costs one vertex per
lost unit of quota. The iteration ranges over degree only, never digraphs. -/
def orderFloor (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | d+1 => max (orderFloor q d + 1) (localFloor q (d+1))

private theorem early_bound {D V q d} (free : QFree D V q) (live : V.Nonempty)
    (rank : ∀v∈V,d≤(outN D V v).card) : earlyFloor q d ≤ V.card := by
  unfold earlyFloor
  apply max_le
  · split
    next hm => exact ShellBankOrders.mixed_order free hm live rank
    next => omega
  apply max_le
  · split
    next hs =>
      split
      next more => exact symmetric_improved free hs more live rank
      next => exact symmetric_order free hs live rank
    next => omega
  · split
    next h =>
      split
      next extra =>
        exact BalancedShellOrder.order_floor free h.1 h.2.1 h.2.2.1 h.2.2.2 extra live rank
      next => exact EqualShellEscape.order_floor free h.1 h.2.1 h.2.2.1 h.2.2.2 live rank
    next => omega

theorem local_bound {D V q d} (free : QFree D V q) (live : V.Nonempty)
    (rank : ∀v∈V,d≤(outN D V v).card) : localFloor q d ≤ V.card := by
  apply max_le (DiagonalShellTransfer.bound free live rank)
  apply max_le
  · split
    next h => exact OddShellOrder.order free live rank h
    next => omega
  apply max_le
  · unfold profileFloor
    split
    next h =>
      obtain ⟨s,sm⟩ := h
      have fit : UniformProfileCapacity.Fits q d s := (mem_filter.mp sm).2
      apply max_le
      · split
        next room => exact UniformProfileCapacity.order free live rank room fit
        next => omega
      · split
        next room => exact SymmetricUniformProfile.order free live rank room fit
        next => omega
    next => omega
  apply max_le (early_bound free live rank)
  split
  next h => exact WideShellOrder.order free live rank h.1 h.2
  next => omega

theorem at_cutoff {p : Input} (bad : Bad p) {q : ℕ} (within : q≤cutoff p) : orderFloor q p.s ≤ p.n := by
  have below : p.s < p.n := by
    have pos := bad.order
    have deg := Compose.FloorSix.out_card bad.degree (show 0<p.n from bad.order)
    change p.s≤(outN p.D (range p.n) 0).card at deg
    have sub : outN p.D (range p.n) 0 ⊆ (range p.n).erase 0 := by
      intro y ym
      refine mem_erase.mpr ⟨?_,outN_subset ym⟩
      rintro rfl
      exact Bool.noConfusion ((bad.loopless 0 bad.order).symm.trans (mem_outN.mp ym).2)
    have lim := card_le_card sub
    rw [card_erase_of_mem (mem_range.mpr bad.order),card_range] at lim
    omega
  have fit (d : ℕ) (ds : d≤p.s) : localFloor q d+p.s≤p.n+d := by
    by_cases hi : 1<localFloor q d
    · have bound : GuardedFamilyRules.OrderBound q d (localFloor q d-1) :=
        ⟨by omega,fun _ _ f live rank=>by have := local_bound f live rank; omega⟩
      have no := GuardedFamilyRules.forbidden bad bound
      by_contra! fail
      exact no ⟨within,ds,by omega⟩
    · omega
  have all (d) : d≤p.s → orderFloor q d+p.s≤p.n+d := by
    induction d with
    | zero => intro; simp [orderFloor]; omega
    | succ d ih =>
      intro h
      have := ih (by omega)
      have := fit (d+1) h
      simp only [orderFloor]
      omega
  have := all p.s le_rfl
  omega

theorem native_order (p : Input) (bad : Bad p) : orderFloor (cutoff p) p.s≤p.n := at_cutoff bad le_rfl

/- Every bad family receives its order bound, including when all three
parameters are symbolic. A concrete smaller order discharges the family. -/
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] native_order

theorem excluded {p : Input} (bad : Bad p) (small : p.n<orderFloor (cutoff p) p.s) : False :=
  (Nat.not_lt_of_ge (native_order p bad)) small

attribute [aesop safe forward (immediate := [bad,small]) (rule_sets := [CHGraphFamilies])] excluded

#print axioms local_bound
attribute [aesop safe forward (immediate := [bad,within]) (rule_sets := [CHGraphFamilies])] at_cutoff

#print axioms at_cutoff
#print axioms native_order
#print axioms excluded
end LeanCH.BR.ShellBankFrontier

