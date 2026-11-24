import checkpoints.shen_extension.BankExitRanks
import checkpoints.shen_extension.ParentBankPeel
import checkpoints.shen_extension.SignatureRestoration
import checkpoints.shen_extension.StrictCount
import checkpoints.shen_extension.MinimalPowerDescent

namespace LeanCH.BR.ReachDescentCatalog
open Finset BRq2 BRq3 CHRuleCatalog BypassDegreeDescent BypassRepair ParentBankPeel

/-- Every positive lower quota is a smaller child. At quota zero the
cardinality bound would require a nonempty carrier of size zero. -/
theorem lower_quotas {p : Input} (least : MinimalChild p) (pos : 0<cutoff p) :
    ∀t,t<p.s → NoHost (cutoff p) t := by
  intro t smaller
  by_cases zero : t=0
  · subst t
    intro G W live size
    have nz := card_pos.mpr live
    simp only [Nat.mul_zero] at size
    omega
  exact MinimalPowerDescent.lower_host least pos (by omega) smaller

/-- One price-free consequence of the lower quotas, simultaneously for
every split of the cutoff and every eligible parent bank size. -/
structure Bounds (q r n : ℕ) : Prop where
  radii : ∀i j,i+j≤q → floorTable q r i+floorTable q r j<n
  pair : 2≤r → n≤q*(r-1)+2 → n-1≤r*(r-1)
  bank : ∀s,2≤q → 2≤r → n=q*(r-1)+2 → s≤r →
    s*(n-s)≤(n-(floorTable q r (q-2)+1)-s)*(r*r/4)+peelCap q r s

theorem bounds {D V q r} (free : QFree D V q) (degree : ∀v∈V,r≤(outN D V v).card)
    (live : V.Nonempty) (lower : ∀t,t<r → NoHost q t) (hq : 0<q) (hr : 0<r) :
    Bounds q r V.card := by
  constructor
  · intro i j time
    by_contra! fits
    exact growth_regime free degree rfl lower hq hr time ⟨card_pos.mpr live,fits⟩
  · intro enough top
    by_contra! crowd
    exact SignatureRestoration.pair_regime free degree rfl (lower (r-1) (by omega)) ⟨enough,hq,top,crowd⟩
  · intro s time enough band fit
    by_contra! crowd
    exact bank_regime free degree rfl lower time enough band fit crowd

theorem least_bounds {p : Input} (bad : Bad p) (least : MinimalChild p) :
    Bounds (cutoff p) p.s p.n := by
  have cut := (remaining_from_run p bad).1
  have free := qfree_of_noShort bad.loopless bad.missing
  have rank (v) (vm : v∈range p.n) := Compose.FloorSix.out_card bad.degree (mem_range.mp vm)
  simpa only [card_range] using bounds free rank (card_pos.mp (by simpa only [card_range] using bad.order))
    (lower_quotas least (by omega)) (by omega) bad.degree_pos

/-- The strongest floor over all ways of splitting the available radius.
The maximum is over integers from zero to q, independent of graph size. -/
def radiusOrder (q r : ℕ) : ℕ :=
  1+(range (q+1)).sup (fun i=>floorTable q r i+floorTable q r (q-i))

theorem radius_order {q r n} (constraints : Bounds q r n) (live : 0<n) : radiusOrder q r≤n := by
  unfold radiusOrder
  have bound : (range (q+1)).sup (fun i=>floorTable q r i+floorTable q r (q-i))≤n-1 := by
    apply Finset.sup_le
    intro i im
    have dt := mem_range.mp im
    have := constraints.radii i (q-i) (by omega)
    omega
  omega

theorem rank_exit {q r n} (constraints : Bounds q r n) (live : 0<n) (small : n<radiusOrder q r) : False :=
  (Nat.not_lt_of_ge (radius_order constraints live)) small

theorem lower_from_bad {p : Input} (bad : Bad p) (least : MinimalChild p) :
    ∀t,t<p.s → NoHost (cutoff p) t :=
  lower_quotas least ((by decide : 1≤3).trans (remaining_from_run p bad).1)

/-- Carry the same quotas to the actual native graph being studied in
the child. The carrier may have fewer vertices than the original input. -/
theorem source_floors {q r} {X : ShenMinimumOrder.Source q r}
    (lower : ∀t,t<r → NoHost q t) (hq : 0<q) (hr : 0<r) (live : X.V.Nonempty) :
    Floors X.D X.V q r ∧ Bounds q r X.V.card :=
  ⟨floors_packet X.free X.degree lower hq hr,bounds X.free X.degree live lower hq hr⟩

/-- Reuse the least descendant's universal lower quotas on its native
source, retaining that source's labels in every ball and its actual order
in the radius bound. Only the numerical bound is passed up to p.n. -/
theorem marked_source {p : Input} (bad : Bad p) (least : MinimalChild p)
    {X : ShenMinimumOrder.Source (cutoff p) p.s} (order : X.V.card≤p.n) :
    Floors X.D X.V (cutoff p) p.s ∧ Bounds (cutoff p) p.s X.V.card ∧
    radiusOrder (cutoff p) p.s≤p.n := by
  have pos : 0<cutoff p := (by decide : 1≤3).trans (remaining_from_run p bad).1
  obtain ⟨table,tests⟩ := source_floors (X:=X) (lower_from_bad bad least) pos bad.degree_pos X.nonempty
  exact ⟨table,tests,(radius_order tests (card_pos.mpr X.nonempty)).trans order⟩

theorem native_floor {p : Input} (bad : Bad p) (least : MinimalChild p)
    {X : ShenMinimumOrder.Source (cutoff p) p.s} (order : X.V.card≤p.n) : Floors X.D X.V (cutoff p) p.s :=
  (marked_source bad least order).1

theorem native_bounds {p : Input} (bad : Bad p) (least : MinimalChild p)
    {X : ShenMinimumOrder.Source (cutoff p) p.s} (order : X.V.card≤p.n) : Bounds (cutoff p) p.s X.V.card :=
  (marked_source bad least order).2.1

theorem least_order {p : Input} (bad : Bad p) (least : MinimalChild p) : radiusOrder (cutoff p) p.s≤p.n :=
  radius_order (least_bounds bad least) bad.order

attribute [aesop safe forward (immediate := [bad,least,order]) (rule_sets := [CHGraphFamilies])] native_floor native_bounds
attribute [aesop safe forward (immediate := [bad,least]) (rule_sets := [CHGraphFamilies])] least_order
#print axioms marked_source
attribute [aesop safe forward (immediate := [constraints,live,small]) (rule_sets := [CHGraphFamilies])] rank_exit
attribute [aesop safe forward (immediate := [constraints,live]) (rule_sets := [CHGraphFamilies])] radius_order
attribute [aesop safe forward (immediate := [bad,least]) (rule_sets := [CHGraphFamilies])] lower_from_bad
attribute [aesop safe forward (immediate := [least,pos]) (rule_sets := [CHGraphFamilies])] lower_quotas
attribute [aesop safe forward (immediate := [bad,least]) (rule_sets := [CHGraphFamilies])] least_bounds
attribute [aesop safe forward (immediate := [free,degree,live,lower,hq,hr]) (rule_sets := [CHGraphFamilies])] bounds
attribute [aesop safe forward (immediate := [free,hq,hr,size,exact,floor2,floor3,regular]) (rule_sets := [CHGraphFamilies])] StrictCount.below_diagonal StrictCount.two_strict_diagonal
attribute [aesop safe forward (immediate := [free,degree,size,lower,arith]) (rule_sets := [CHGraphFamilies])] SignatureRestoration.pair_regime
#print axioms least_bounds
#print axioms source_floors
end LeanCH.BR.ReachDescentCatalog

