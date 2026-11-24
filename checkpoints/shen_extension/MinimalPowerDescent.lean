import checkpoints.shen_extension.BypassDegreeDescent
import LeanCH.BR.BRDiagonalThird

namespace LeanCH.BR.MinimalPowerDescent
open Finset BRq2 BRq3 CHRuleCatalog BypassRepair BypassDegreeDescent ShenReachTransition

/-- The same comparison supplies every smaller positive quota on every
finite host, even when the host uses different labels. -/
theorem lower_host {p : Input} (least : MinimalChild p) (pos : 1≤cutoff p)
    {d} (hd : 0<d) (smaller : d<p.s) : NoHost (cutoff p) d := by
  intro D W live size free deg
  obtain ⟨c,_,edge,dr,_,le,_⟩ := host_child p hd pos live size free deg
  obtain ⟨low,rank⟩ := least.compare c edge
  have := rank (Nat.le_antisymm low le)
  omega

/-- A power child with arbitrary requested degree. Its arcs are the actual
off-diagonal bounded-reach pairs on the original vertex labels. -/
theorem power_edge {p : Input} (bad : Bad p) {t d} (degree : 0<d)
    (pos : 0<CH.ceilDiv p.n d) (fits : CH.ceilDiv p.n d*t≤cutoff p)
    (growth : ∀x∈range p.n,d+1≤(ball p.D (range p.n) x t).card) :
    let k := CH.ceilDiv p.n d
    let E := nextGraph p.D (range p.n) (cutoff p) k (fun _=>t) (fun _=>0)
    Child p ⟨p.n,d,E⟩ ∧ ∀x∈range p.n, outN E (range p.n) x=(ball p.D (range p.n) x t).erase x := by
  let k := CH.ceilDiv p.n d
  let E := nextGraph p.D (range p.n) (cutoff p) k (fun _=>t) (fun _=>0)
  have row (x) (xm : x∈range p.n) : outN E (range p.n) x=(ball p.D (range p.n) x t).erase x :=
    SATBoundaryPilot.power_out xm fits
  have time : t≤cutoff p := (show t≤k*t by simpa using Nat.mul_le_mul_right t pos).trans fits
  refine ⟨reach_child bad d k _ _ degree pos rfl (fun _ _=>time) ?_,row⟩
  intro x inside
  have xv := mem_range.mpr inside
  have enough := growth x xv
  have size := card_erase_add_one (self_mem_ball (D:=p.D) (k:=t) xv)
  obtain ⟨H,sub,count⟩ := exists_subset_card_eq
    (show d≤(outN E (range p.n) x).card by rw [row x xv]; omega)
  exact ⟨H.toList,by simpa using count,H.nodup_toList,fun y hy => by
    obtain ⟨yv,xy⟩ := mem_outN.mp (sub (mem_toList.mp hy))
    exact ⟨mem_range.mp yv,xy⟩⟩

/-- In a minimal input every affordable strictly smaller cutoff must have
an actual root short of the power degree. All distances use the parent. -/
theorem short_root {p : Input} (bad : Bad p) (least : MinimalChild p) {t d}
    (degree : 0<d) (pos : 0<CH.ceilDiv p.n d) (fits : CH.ceilDiv p.n d*t≤cutoff p)
    (desc : CH.ceilDiv p.n d<cutoff p) :
    ∃ x∈range p.n, (ball p.D (range p.n) x t).card≤d := by
  by_contra! rich
  have edge := (power_edge bad degree pos fits rich).1
  exact (Nat.not_lt_of_ge (least.compare _ edge).1) desc

/-- The lower-rank inputs to the diagonal third-ball theorem come from
this very minimum. Thus a factor three in the cutoff supplies a literal
child at three times the degree and one third the cutoff. -/
theorem triple_child {p : Input} (bad : Bad p) (ranks : ∀d, 0<d → d<p.s → NoHost (cutoff p) d)
    (four : 4≤p.s) (diag : p.s≤cutoff p) {k} (factor : cutoff p=3*k) :
    ∃ c : Input, Child p c ∧ Bad c ∧ c.n=p.n ∧ c.s=3*p.s ∧ cutoff c=k ∧ cutoff c<cutoff p := by
  have free := qfree_of_noShort bad.loopless bad.missing
  have degree (x) (hx : x∈range p.n) := Compose.FloorSix.out_card bad.degree (mem_range.mp hx)
  have bound x (hx : x∈range p.n) := BRsGen.third_ball_ge_on_diagonal four diag (fun d low high D V ff deg live => by
    by_contra! small
    exact ranks d (by omega) high D V live (by omega) ff deg) free degree hx
  obtain ⟨c,edge,order,d,cut⟩ := SATBoundaryPilot.powered_child bad (by omega : 0<k) (by decide) factor
    bound
  exact ⟨c,edge,bad_child bad edge,order,d,cut,by omega⟩

/-- Numerical guard on the selected input, without any bound on degree
or cutoff above the displayed diagonal condition. -/
@[aesop safe forward (immediate := [bad,least]) (rule_sets := [CHGraphFamilies])]
theorem no_triple {p : Input} (bad : Bad p) (least : MinimalChild p) :
    4≤p.s → p.s≤cutoff p → cutoff p%3≠0 := by
  intro four diag div
  have factor : cutoff p=3*(cutoff p/3) := by omega
  obtain ⟨c,edge,_,_,_,_,less⟩ := triple_child bad
    (fun _ hd small => lower_host least (by omega) hd small) four diag factor
  exact (Nat.not_lt_of_ge (least.compare c edge).1) less

attribute [aesop safe forward (immediate := [bad,least,degree,pos,fits,desc]) (rule_sets := [CHGraphFamilies])] short_root
attribute [aesop safe forward (immediate := [least,pos,hd,smaller]) (rule_sets := [CHGraphFamilies])] lower_host

#print axioms lower_host
#print axioms power_edge
#print axioms short_root
#print axioms triple_child
#print axioms no_triple
end LeanCH.BR.MinimalPowerDescent
