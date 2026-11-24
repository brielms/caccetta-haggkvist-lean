import checkpoints.shen_extension.FlatTightTraffic

namespace LeanCH.BR.Closure.FlatTransientReturn
open Finset Function BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor
open PairedFamilyLoop RawRepairAlternative FirstPacketBarrier FlatExchangeTriangle

def Tight {F} (q : ℕ) (E : CH.Digraph) (V : Finset ℕ)
    (raw : PairedFamilyLoop.State F → ℕ→ℝ) (a : PairedFamilyLoop.State F) :=
  ∀z∈V\gone a,realCol q E (V\gone a) (raw a) z=1

def Slack {F} (q : ℕ) (E : CH.Digraph) (V : Finset ℕ)
    (raw : PairedFamilyLoop.State F → ℕ→ℝ) (a : PairedFamilyLoop.State F) :=
  ∃z∈V\gone a,realCol q E (V\gone a) (raw a) z<1

private theorem first_arrival {α : Type*} [Finite α] (go : α→α) (P : α→Prop)
    (all : ∀a : periodicPts go,P a.val) {seed} (start : ¬P seed) :
    ∃j, (∀i≤j,¬P (go^[i] seed)) ∧ P (go (go^[j] seed)) := by
  classical
  obtain ⟨t,per⟩ := CycleSlotOrbit.recurrent go seed
  have hit : ∃i,P (go^[i] seed) := ⟨t,all ⟨_,per⟩⟩
  have yes := Nat.find_spec hit
  have pos : 0<Nat.find hit := by
    by_contra! zero
    rw [show Nat.find hit=0 by omega] at yes
    exact start yes
  refine ⟨Nat.find hit-1,fun i hi => Nat.find_min hit (by omega),?_⟩
  have step := iterate_succ_apply' go (Nat.find hit-1) seed
  rw [←step,show (Nat.find hit-1).succ=Nat.find hit by omega]
  exact yes

/-- The residue of the flat child fixes the omission size at every other
tight state, whether or not the state lies on an orbit. -/
theorem tight_size {F q E V m} (hq : 2≤q) (balance : 2*m=q+1)
    (cycles : ∀a : PairedFamilyLoop.State F,Cycle E V q (previous a))
    {a : PairedFamilyLoop.State F} (count : (gone a).card=m) (modOne : ((V\gone a).card : ZMod q)=1)
    {b : PairedFamilyLoop.State F} {p : ℕ→ℝ} (law : RealDual q E (V\gone b) 1 p)
    (tight : ∀z∈V\gone b,realCol q E (V\gone b) p z=1) : (gone b).card=m := by
  have total (s : PairedFamilyLoop.State F) : ((V\gone s).card : ZMod q)+((gone s).card : ZMod q)=V.card := by
    have eq : (V\gone s).card+(gone s).card=V.card := card_sdiff_add_card_eq_card (sdiff_subset.trans (cycles s).sub : gone s⊆V)
    rw [←Nat.cast_add,eq]
  have x := total a
  have y := total b
  rw [modOne,count] at x
  rw [(CanonicalCycleLaw.unit_columns hq tight).1 law.normalized] at y
  have eq : ((gone b).card : ZMod q)=(m:ZMod q) := add_left_cancel (y.trans x.symm)
  have rem := (ZMod.natCast_eq_natCast_iff _ _ _).mp eq
  change (gone b).card%q=m%q at rem
  rw [Nat.mod_eq_of_lt (by omega : m<q)] at rem
  have cap := card_le_card (sdiff_subset : gone b⊆previous b)
  change (gone b).card≤(previous b).card at cap
  rw [(cycles b).size] at cap
  by_cases small : (gone b).card<q
  · rwa [Nat.mod_eq_of_lt small] at rem
  · have reduced := Nat.mod_eq_sub_mod (show q≤(gone b).card by omega)
    rw [reduced,Nat.mod_eq_of_lt (by omega)] at rem
    omega

/-- A nonempty initial segment of the selected schedule has a slack
column at every state. The actual next child has every column tight and
exactly the balanced omission size. -/
def Returns {F} (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (m : ℕ) (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (raw : PairedFamilyLoop.State F → ℕ→ℝ) (seed : PairedFamilyLoop.State F) :=
  seed∉periodicPts go ∧ ∃j, (∀i≤j,Slack q E V raw (go^[i] seed)) ∧
    Tight q E V raw (go (go^[j] seed)) ∧ (gone (go (go^[j] seed))).card=m

theorem returns {F q E V m} (hq : 2≤q) (balance : 2*m=q+1)
    (cycles : ∀s : PairedFamilyLoop.State F,Cycle E V q (previous s))
    {a : PairedFamilyLoop.State F} (count : (gone a).card=m) (modOne : ((V\gone a).card : ZMod q)=1)
    {go : PairedFamilyLoop.State F → PairedFamilyLoop.State F} {raw : PairedFamilyLoop.State F → ℕ→ℝ}
    (laws : ∀s,RealDual q E (V\gone s) 1 (raw s))
    (flat : ∀s : periodicPts go,Tight q E V raw s.val)
    {seed : PairedFamilyLoop.State F} (different : (gone seed).card≠m) : Returns q E V m go raw seed := by
  have size (v : PairedFamilyLoop.State F) := tight_size hq balance cycles count modOne (laws v)
  have start : ¬Tight q E V raw seed := fun same => different (size seed same)
  obtain ⟨j,early,hit⟩ := first_arrival go (Tight q E V raw) flat start
  refine ⟨fun per => start (flat ⟨_,per⟩),j,?_,hit,size _ hit⟩
  intro i le
  have no := early i le
  by_contra! empty
  apply no
  intro z hz
  exact le_antisymm ((laws _).columns z hz) (le_of_not_gt (fun lt => empty ⟨z,hz,lt⟩))

theorem on_schedule {q D V F} (hq : 2≤q) (free : QFree (graph D F) V q)
    (small : SmallerSmallRow q V.card) (cycles : ∀I∈F,Cycle (graph D F) V q I)
    (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (join : ∀s,previous (go s)=current s)
    (mark : ∀s,Marked (graph D F) (previous s) (current s) (current (go s)))
    (flat : ∀a : Function.periodicPts go,BRsub.Sat q (graph D F) (V\RawRepairAlternative.gone a.val))
    {x p : ℕ→ℚ} (xp : ∀u∈V,0<x u) (pp : ∀u∈V,0≤p u)
    (strict : ∀u∈V,mass V x<WeightedSD.row q (graph D F) V x u)
    (costrict : ∀u∈V,mass V p<WeightedSD.col q (graph D F) V p u)
    (raw : PairedFamilyLoop.State F → ℕ→ℝ)
    (laws : ∀a,RealDual q (graph D F) (V\gone a) 1 (raw a))
    (flatRaw : ∀s : periodicPts go,Tight q (graph D F) V raw s.val)
    (s : Function.periodicPts go) :
    let E := graph D F
    let A := previous s.val
    let B := current s.val
    let C := current (go s.val)
    let T := A∪B∪C
    ((V\RawRepairAlternative.gone s.val).card : ZMod q)=1 →
    Packet E V A B C →
    Packet E V (previous (go s.val)) C (current (go (go s.val))) →
    Packet E V (previous (go (go s.val))) (current (go (go s.val))) (current (go (go (go s.val)))) →
    ∃N∈F,(B\C).card<(N\T).card ∧ ∀J∈({A,B,C} : Finset (Finset ℕ)),
      ∃seed : PairedFamilyLoop.State F,previous seed=N ∧ current seed=J ∧ Returns q E V (B\C).card go raw seed := by
  classical
  intro E A B C T modOne a b c
  obtain ⟨⟨N,nf,far⟩,_⟩ := FlatTightTraffic.on_schedule hq free small cycles go join mark flat xp pp strict costrict s modOne a b c
  have left (v : PairedFamilyLoop.State F) := cycles _ (mem_product.mp (mem_filter.mp v.property).1).1
  have right (v : PairedFamilyLoop.State F) := (mem_product.mp (mem_filter.mp v.property).1).2
  have ca : Cycle E V q A := left s.val
  obtain ⟨e⟩ := a.copy
  have eq : (B\C).card=(A\B).card := by simpa only [Fintype.card_coe] using Fintype.card_congr e.equiv
  have bal := card_sdiff_add_card_inter A B
  rw [ca.size,show A∩B=B\C from a.overlap,←eq] at bal
  refine ⟨N,nf,far,?_⟩
  intro J jh
  have role : J=A ∨ J=B ∨ J=C := by simpa using jh
  have jf : J∈F := by
    rcases role with rfl|rfl|rfl
    · exact (mem_product.mp (mem_filter.mp s.val.property).1).1
    · exact right s.val
    · exact right (go s.val)
  have sub : J⊆T := by
    rcases role with rfl|rfl|rfl
    · exact subset_union_left.trans subset_union_left
    · exact subset_union_right.trans subset_union_left
    · exact subset_union_right
  have cmp := card_le_card (show N\T⊆N\J from fun v vh =>
    mem_sdiff.mpr ⟨(mem_sdiff.mp vh).1,fun j => (mem_sdiff.mp vh).2 (sub j)⟩)
  change (B\C).card<(N\T).card at far
  have diff : N≠J := by
    intro same
    rw [←same,sdiff_self] at cmp
    change (N\T).card≤0 at cmp
    omega
  let seed : PairedFamilyLoop.State F := ⟨(N,J),mem_filter.mpr ⟨mem_product.mpr ⟨nf,jf⟩,diff⟩⟩
  refine ⟨seed,rfl,rfl,returns hq (by omega) left (a:=s.val) eq.symm modOne laws flatRaw ?_⟩
  change (N\J).card≠(B\C).card
  omega

#print axioms returns
#print axioms on_schedule

end LeanCH.BR.Closure.FlatTransientReturn
