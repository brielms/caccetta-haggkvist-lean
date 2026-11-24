import checkpoints.shen_extension.UniformPowerReplay

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 CHRuleCatalog ShenReachTransition

/-- Apply the second-neighbour theorem on the reach graph at any
affordable radius. Its second neighbours give actual new labels at the
doubled radius, at the very vertex whose in-ball is charged. -/
theorem power_receiver {D V q k} (free : QFree D V q) (live : V.Nonempty)
    (time : 2*k≤q) :
    ∃x∈V, 2*(ball D V x k).card≤(ball D V x (2*k)).card+1 ∧
      2*(ball D V x k).card+(reverseBall D V x (q-2*k)).card≤V.card+2 := by
  classical
  let E := nextGraph D V q 2 (fun _=>k) (fun _=>0)
  have ef : QFree E V 2 := next_free free (fun _ _=>by omega) (by decide)
  obtain ⟨x,xm,good⟩ := ShenSeymour.witness ef le_rfl live
  have row (v) (vm : v∈V) : outN E V v=(ball D V v k).erase v :=
    SATBoundaryPilot.power_out vm time
  have sub : ShenSeymour.second E V x⊆ball D V x (2*k)\ball D V x k := by
    intro z zm
    obtain ⟨zv,ne,off,y,yv,xy,yz⟩ := mem_filter.mp zm
    have yh : y∈outN E V x := mem_outN.mpr ⟨yv,xy⟩
    have zh : z∈outN E V y := mem_outN.mpr ⟨zv,yz⟩
    rw [row x xm] at yh
    rw [row y yv] at zh
    refine mem_sdiff.mpr ⟨?_,?_⟩
    · simpa only [two_mul] using ball_trans (mem_of_mem_erase yh) (mem_of_mem_erase zh)
    · intro zball
      have head : z∈outN E V x := (row x xm).symm ▸ mem_erase.mpr ⟨ne,zball⟩
      exact off (mem_outN.mp head).2
  have bill := good.trans (card_le_card sub)
  rw [row x xm,card_sdiff_of_subset (ball_mono_radius (by omega : k≤2*k))] at bill
  have self := card_erase_add_one (self_mem_ball (D:=D) (k:=k) xm)
  have mono := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=x) (by omega : k≤2*k))
  have other := reverseBall_add_ball_le (v:=x) free (by omega : 2*k+(q-2*k)≤q)
  exact ⟨x,xm,by omega,by omega⟩

theorem uniform_receiver {p : Input} (bad : Bad p) (src : UniformSource p)
    (fit : 2*2≤cutoff p) :
    ∃E : CH.Digraph, (∀u v,E u v=true → p.D u v=true) ∧
      QFree E (range p.n) (cutoff p) ∧ OutEq p.s E (range p.n) ∧
      (∀v∈range p.n,(ball E (range p.n) v 3).card=3*p.s ∧ 2*p.s<(ball E (range p.n) v 2).card) ∧
      ∃x∈range p.n,4*p.s+1≤(ball E (range p.n) x 4).card ∧
        4*p.s+(reverseBall E (range p.n) x (cutoff p-4)).card≤p.n := by
  obtain ⟨E,sub,free,reg,score⟩ := src.witness
  obtain ⟨x,xm,outgoing,incoming⟩ := power_receiver free (nonempty_range_iff.mpr bad.order.ne') fit
  change 2*(ball E (range p.n) x 2).card≤(ball E (range p.n) x 4).card+1 at outgoing
  change 2*(ball E (range p.n) x 2).card+(reverseBall E (range p.n) x (cutoff p-4)).card≤(range p.n).card+2 at incoming
  rw [card_range] at incoming
  have := (score x xm).2
  exact ⟨E,sub,free,reg,score,x,xm,by omega,by omega⟩

attribute [aesop safe forward (immediate := [free,live,time]) (rule_sets := [CHGraphFamilies])] power_receiver
attribute [aesop safe forward (immediate := [bad,src,fit]) (rule_sets := [CHGraphFamilies])] uniform_receiver
#print axioms power_receiver
#print axioms uniform_receiver
end LeanCH.BR.FragmentScoreEquality