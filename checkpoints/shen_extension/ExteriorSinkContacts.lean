import checkpoints.shen_extension.SecondHeadReturnGate
import checkpoints.shen_extension.DirectAccountEntry

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- At a complete account each primary origin uses all cycle labels. For an
exterior sink, all contacts among those actual origins share the same two
endpoints. The sink and the cycle belong to the same selected graph. -/
theorem sink_account_contacts {D V q r C A target e} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (account : CompleteAccount t C A) (length : C.card+1=r) (ee : e∈exterior D V C)
    (sink : ∀a∈exterior D V C,D e a≠true) :
    let K := (claims t C).filter (fun Y=>C⊆outN D V (t.rep Y))
    (contacts D V (K.image t.rep) 3).card≤1 ∧
      ∀p∈contacts D V (K.image t.rep) 3,N2 D V p.1=exterior D V C := by
  classical
  let K := (claims t C).filter (fun Y=>C⊆outN D V (t.rep Y))
  let U := K.image t.rep
  change (contacts D V U 3).card≤1 ∧ ∀p∈contacts D V U 3,N2 D V p.1=exterior D V C
  have shape u (um : u∈U) : u∈V ∧ C⊆outN D V u ∧ (outN D V u\C).card=1 ∧
      (N2 D V u).card≤r ∧ (ball D V u 3).card≤3*r := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp um
    obtain ⟨claim,inside⟩ := mem_filter.mp ym
    have key := (mem_filter.mp claim).1
    have uv := rep_native t key
    have low := (mem_filter.mp (mem_filter.mp (t.represents Y key)).1).2
    obtain ⟨hq,a,b,c,d,_⟩ := ready.cycle
    have bound := low_third_second free hq reg uv a b c d low
    change (ball D V (t.rep Y) 2).card≤2*r+1 at bound
    have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
    rw [reg _ uv] at one
    have two := @card_B2 D V (t.rep Y)
    have diff := card_sdiff_of_subset inside
    rw [reg _ uv] at diff
    exact ⟨uv,inside,by omega,by omega,low⟩
  have unique : Set.InjOn (N2 D V) (U:Set ℕ) := by
    intro u um v vm eq
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp um
    obtain ⟨Z,zm,rfl⟩ := mem_image.mp vm
    have key S (sm : S∈K) := (mem_filter.mp (mem_filter.mp sm).1).1
    exact congrArg t.rep ((rep_key t (key Y ym)).symm.trans (eq.trans (rep_key t (key Z zm))))
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have width := account.width
  have ev : e∈V := by
    obtain ⟨a,_,ae⟩ := mem_biUnion.mp (mem_sdiff.mp ee).1
    exact outN_subset ae
  have identify (p : ℕ×ℕ) (pm : p∈contacts D V U 3) :
      privateHeads D V C p.1={p.2} ∧ N2 D V p.1=exterior D V C := by
    obtain ⟨pair,hit⟩ := mem_filter.mp pm
    obtain ⟨um,vm,dist⟩ := mem_offDiag.mp pair
    obtain ⟨uv,first,uslot,ys,low⟩ := shape _ um
    obtain ⟨vv,common,vslot,cap,_⟩ := shape _ vm
    by_cases small : (N2 D V p.1).card≤(exterior D V C).card
    · exact single_slot_collision free (by omega) uv dist first common uslot.le small (by omega) hit
    have diff : N2 D V p.1≠exterior D V C := fun eq=>small (le_of_eq (congrArg card eq))
    obtain ⟨w,slot⟩ := card_eq_one.mp uslot
    have firstEq : outN D V p.1=insert w C := by
      calc outN D V p.1=(outN D V p.1\C)∪C := (sdiff_union_of_subset first).symm
           _=insert w C := by rw [slot,singleton_union]
    have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
    rw [reg _ uv] at one
    have two := @card_B2 D V p.1
    have three := @card_B3 D V p.1
    exact (sink_excludes_larger_contact free (by omega) uv vv dist firstEq common vslot.le ee
      (fun c cm=>(mem_outN.mp (account.allHeads c cm ee)).2) sink diff (by omega)
      (by rw [reg _ ev]; omega)
      (fun b bm=>by rw [reg _ (N2_subV (mem_sdiff.mp bm).1)]; exact cap) (by omega) hit).elim
  refine ⟨?_, fun p pm=>(identify p pm).2⟩
  apply card_le_one.mpr
  intro p pm a am
  obtain ⟨pv,py⟩ := identify p pm
  obtain ⟨av,ay⟩ := identify a am
  have eq : p.1=a.1 := unique (mem_offDiag.mp (mem_filter.mp pm).1).1
    (mem_offDiag.mp (mem_filter.mp am).1).1 (py.trans ay.symm)
  rw [eq] at pv
  exact Prod.ext eq (singleton_injective (pv.symm.trans av))

attribute [aesop safe forward (immediate := [free,reg,ready,account,length,ee,sink]) (rule_sets := [CHGraphFamilies])] sink_account_contacts
#print axioms sink_account_contacts
end LeanCH.BR.LowShellCycleSelection
