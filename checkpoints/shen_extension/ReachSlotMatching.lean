import checkpoints.shen_extension.ReverseReachPayment
import Mathlib.Combinatorics.Hall.Finite

namespace LeanCH.BR.ReachSlotMatching
open Finset BRq2 BRq3 BR45 BRsub WeightedSD ReverseReachPayment Closure.ShortestCycleWeights
open Classical

abbrev Slot := Σ _v : ℕ, ℕ
def slots (S : Finset ℕ) (capacity : ℕ→ℕ) : Finset Slot :=
  S.sigma (fun v=>range (capacity v))

theorem mem_slots {S cap} {s : Slot} : s∈slots S cap ↔ s.1∈S ∧ s.2<cap s.1 := by
  simp [slots]

theorem card_slots (S : Finset ℕ) (cap : ℕ→ℕ) : (slots S cap).card=∑v∈S,cap v := by
  simp [slots]

/-- Different demanded units get different labelled supply slots. A supply
slot remembers both the original vertex and its copy index. -/
def Assignment (E : CH.Digraph) (V T : Finset ℕ) (k : ℕ) (demand capacity : ℕ→ℕ)
    (reserved : Finset Slot) : Prop :=
  ∃f : ↥(slots T demand)→Slot, Function.Injective f ∧ ∀d,
    f d∈slots V capacity ∧ f d∉reserved ∧ d.val.1∈ball E V (f d).1 k

/-- Test the Hall inequalities after removing exactly the reserved supply
slots, using any time horizon, supply and demand on any labelled relation of reach. -/
theorem assign {E V T k demand capacity reserved}
    (hall : ∀S⊆T,S.Nonempty →
      (slots S demand).card ≤ (slots (starts E V S k) capacity \ reserved).card) :
    Assignment E V T k demand capacity reserved := by
  classical
  let options (d : ↥(slots T demand)) := slots (starts E V {d.val.1} k) capacity \ reserved
  have cover (Z : Finset ↥(slots T demand)) : Z.card≤(Z.biUnion options).card := by
    by_cases live : Z.Nonempty
    · let S := Z.image (fun d=>d.val.1)
      have st : S⊆T := by
        intro t tm
        obtain ⟨d,_,rfl⟩ := mem_image.mp tm
        exact (mem_slots.mp d.property).1
      have dem : Z.image Subtype.val⊆slots S demand := by
        intro x xm
        obtain ⟨d,dm,rfl⟩ := mem_image.mp xm
        exact mem_slots.mpr ⟨mem_image.mpr ⟨d,dm,rfl⟩,(mem_slots.mp d.property).2⟩
      have left := card_le_card dem
      rw [card_image_of_injective _ Subtype.val_injective] at left
      have right : slots (starts E V S k) capacity \ reserved ⊆ Z.biUnion options := by
        intro y ym
        obtain ⟨ys,off⟩ := mem_sdiff.mp ym
        obtain ⟨start,idx⟩ := mem_slots.mp ys
        obtain ⟨yv,t,ts,hit⟩ := mem_filter.mp start
        obtain ⟨d,dm,ed⟩ := mem_image.mp ts
        exact mem_biUnion.mpr ⟨d,dm,mem_sdiff.mpr ⟨mem_slots.mpr
          ⟨mem_filter.mpr ⟨yv,d.val.1,mem_singleton_self _,ed ▸ hit⟩,idx⟩,off⟩⟩
      exact left.trans ((hall S st (live.image _)).trans (card_le_card right))
    · simp [not_nonempty_iff_eq_empty.mp live]
  obtain ⟨f,inj,fit⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' options).mp cover
  refine ⟨f,inj,?_⟩
  intro d
  obtain ⟨ym,off⟩ := mem_sdiff.mp (fit d)
  obtain ⟨start,ix⟩ := mem_slots.mp ym
  obtain ⟨yv,t,ts,hit⟩ := mem_filter.mp start
  have eq := mem_singleton.mp ts
  exact ⟨mem_slots.mpr ⟨yv,ix⟩,off,eq ▸ hit⟩

/-- Any uniform lower bound on excess supply pays arbitrary reservations
up to that bound; the deleted slots may have any physical labels. -/
theorem assign_margin {E V T k demand capacity reserved} {margin : ℕ}
    (slack : ∀S⊆T,S.Nonempty →
      (∑v∈S,demand v)+margin≤∑u∈starts E V S k,capacity u) (spent : reserved.card≤margin) :
    Assignment E V T k demand capacity reserved := by
  apply assign
  intro S st ne
  rw [card_slots]
  let A := slots (starts E V S k) capacity
  have missing := card_sdiff_add_card_inter A reserved
  have charge := card_le_card (inter_subset_right (s₁:=A) (s₂:=reserved))
  have total : A.card=∑u∈starts E V S k,capacity u := card_slots _ _
  have bound := slack S st ne
  change _≤(A\reserved).card
  omega

theorem monotone_starts {E V S T k} (st : S⊆T) : starts E V S k⊆starts E V T k := by
  intro u um
  obtain ⟨uv,v,vs,hit⟩ := mem_filter.mp um
  exact mem_filter.mpr ⟨uv,v,st vs,hit⟩

/-- A failed reverse merge at integral prices supplies a simultaneous
assignment, even after any one supply slot is reserved. The guaranteed
margin of one is strict inequality at integral weights. -/
theorem from_expansion {q E V T} {capacity : ℕ→ℕ}
    (law : Expansion q E V (fun v=>(capacity v:ℚ))) (tv : T⊆V)
    (room : (starts E V T (q-1)).card+1<V.card)
    {reserved : Finset Slot} (spent : reserved.card≤1) :
    Assignment E V T (q-1) (fun t=>q*capacity t) capacity reserved := by
  apply assign_margin (margin:=1) _ spent
  intro S st live
  have inc := card_le_card (monotone_starts (E:=E) (V:=V) (k:=q-1) st)
  have strict := law S (st.trans tv) live (by omega)
  change (q:ℚ)*(∑v∈S,(capacity v:ℚ)) < ∑v∈starts E V S (q-1),(capacity v:ℚ) at strict
  have nat : q*(∑v∈S,capacity v)<∑v∈starts E V S (q-1),capacity v := by exact_mod_cast strict
  rw [←Finset.mul_sum]
  omega

def ReservedAssignments (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (capacity : ℕ→ℕ) : Prop :=
  ∀T⊆V,(starts E V T (q-1)).card+1<V.card → ∀reserved : Finset Slot,reserved.card≤1 →
    Assignment E V T (q-1) (fun t=>q*capacity t) capacity reserved

theorem from_native {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card) :
    ReservedAssignments q (fun i j=>X.D j i) X.V X.weights :=
  fun _ tv room _ spent=>from_expansion (native_rows X hq small) tv room spent

attribute [aesop safe forward (immediate := [X,hq,small]) (rule_sets := [CHGraphFamilies])] from_native
attribute [aesop safe forward (immediate := [law,tv,room,spent]) (rule_sets := [CHGraphFamilies])] from_expansion
attribute [aesop safe forward (immediate := [slack,spent]) (rule_sets := [CHGraphFamilies])] assign_margin
/-- Heads shared by an arbitrary marked family of parents. -/
noncomputable def commonHeads (D : CH.Digraph) (V P : Finset ℕ) : Finset ℕ :=
  V.filter (fun t=>∀p∈P,D p t=true)

/-- All marked parents are absent from the forward horizon of their common
heads. This supplies the actual room required by the payment test. -/
theorem common_room {q D V P} (free : QFree D V q) (time : 1≤q) (pv : P⊆V) :
    (starts (fun x y=>D y x) V (commonHeads D V P) (q-1)).card + P.card ≤ V.card := by
  have sub : starts (fun x y=>D y x) V (commonHeads D V P) (q-1) ⊆ V\P := by
    intro p pm
    obtain ⟨inV,t,tm,pt⟩ := mem_filter.mp pm
    refine mem_sdiff.mpr ⟨inV,?_⟩
    intro marked
    obtain ⟨_,k,short,path⟩ := mem_ball.mp pt
    have feed := (mem_filter.mp tm).2
    exact free.reverse t (k+1) (by omega) (by omega) (.step inV (feed p marked) path)
  have le := card_le_card sub
  have count := card_sdiff_add_card_eq_card pv
  omega

/-- The packet keeps the targets, graph, time and prices, so a consumer
can choose a particular slot to preserve after learning the assignment law. -/
def CommonAssignment (q : ℕ) (D : CH.Digraph) (V P : Finset ℕ) (capacity : ℕ→ℕ) : Prop :=
  ∀reserved : Finset Slot,reserved.card≤1 →
    Assignment (fun i j=>D j i) V (commonHeads D V P) (q-1)
      (fun t=>q*capacity t) capacity reserved

theorem common_assignment {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {P} (pv : P⊆X.V) (many : 2≤P.card) : CommonAssignment q X.D X.V P X.weights := by
  have bound := common_room X.free (by omega : 1≤q) pv
  exact from_native X hq small _ (filter_subset _ _) (by omega)

/-- A pair of family arcs supplies two actual reserved labels and marks
their common receiver inside the set to which the entire assignment applies. -/
structure Marked {q n} (X : Model q n) (P : Finset ℕ) (z : ℕ) : Prop where
  receiver : z∈commonHeads X.D X.V P
  assignments : CommonAssignment q X.D X.V P X.weights

open Closure.FirstPacketBarrier Closure.MarkedCyclePeeling in
theorem family_arcs {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F : Family} (native : F⊆family X) {p t z : ℕ} (diff : p≠t)
    (left : graph X.D F p z=true) (right : graph X.D F t z=true) : Marked X {p,t} z := by
  obtain ⟨A,am⟩ := active.mp left
  obtain ⟨B,bm⟩ := active.mp right
  obtain ⟨af,pa,za,arc⟩ := mem_col.mp am
  obtain ⟨bf,tb,_,arc'⟩ := mem_col.mp bm
  have ca := (mem_filter.mp (native af)).2
  have cb := (mem_filter.mp (native bf)).2
  constructor
  · apply mem_filter.mpr
    refine ⟨ca.sub za,?_⟩
    intro i im
    rcases mem_insert.mp im with rfl|single
    · exact arc
    · simpa [mem_singleton.mp single] using arc'
  · exact common_assignment X hq small (insert_subset (ca.sub pa) (singleton_subset_iff.mpr (cb.sub tb))) (by simp [diff])

attribute [aesop safe forward (immediate := [X,hq,small,pv,many]) (rule_sets := [CHGraphFamilies])] common_assignment
attribute [aesop safe forward (immediate := [X,hq,small,native,diff,left,right]) (rule_sets := [CHGraphFamilies])] family_arcs
#print axioms family_arcs
#print axioms from_native
#print axioms assign
end LeanCH.BR.ReachSlotMatching
