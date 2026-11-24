import checkpoints.shen_extension.ReachLedgerCatalog
import checkpoints.shen_extension.FlatPeelReach
import checkpoints.shen_extension.SharedArcBarrier

namespace LeanCH.BR.ReverseReachPayment
open Finset BRq2 BRq3 BR45 BRsub WeightedSD Closure.ForwardMerge Closure.ShortestCycleWeights
open Classical

/-- The actual possible starts of a walk into a target set at a given horizon. -/
noncomputable def starts (E : CH.Digraph) (V T : Finset ℕ) (k : ℕ) : Finset ℕ :=
  V.filter (fun x => ∃t∈T, t∈ball E V x k)

theorem targets_inside {E V T k} (sub : T⊆V) : T⊆starts E V T k :=
  fun t tm => mem_filter.mpr ⟨sub tm,t,tm,self_mem_ball (sub tm)⟩

/-- A bank of starting labels misses every target exactly when it is disjoint
from their backward reach. All paths and both sides use the same graph. -/
theorem misses_iff {E V H T k} (hv : H⊆V) (tv : T⊆V) :
    T⊆V\ballSet E V H k ↔ H⊆V\starts E V T k := by
  constructor
  · intro miss x xh
    refine mem_sdiff.mpr ⟨hv xh,?_⟩
    rintro xm
    obtain ⟨t,tt,xt⟩ := (mem_filter.mp xm).2
    exact (mem_sdiff.mp (miss tt)).2 (mem_ballSet.mpr ⟨x,xh,xt⟩)
  · intro miss t tt
    refine mem_sdiff.mpr ⟨tv tt,?_⟩
    intro reached
    obtain ⟨x,xh,xt⟩ := mem_ballSet.mp reached
    exact (mem_sdiff.mp (miss xh)).2 (mem_filter.mpr ⟨hv xh,t,tt,xt⟩)

/-- An unreached column keeps every original parent through the preceding
round. Strict columns suffice, at arbitrary nonnormalized positive prices. -/
theorem remote_pays {q V D E} {w : ℕ→ℚ}
    (sub : ∀i j,E i j=true → D i j=true) (positive : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w < WeightedSD.col q E V w i)
    {H : Finset ℕ} (room : (V\H).card+1<V.card) (live : (V\H).Nonempty)
    (bill : mass (V\H) w ≤ (q:ℚ)*mass (V\ballSet E V H (q-1)) w) : NativeMergePays q D V := by
  let U := V\H
  let J : CH.Digraph := fun i j => E j i
  have rows (x) (xm : x∈V) : mass V w < WeightedSD.row q J V w x := strict x xm
  have interior : V\ballSet E V H (q-1) ⊆ Closure.FlatPeelReach.interior J V U (q-1) := by
    intro x xm
    have xv := (mem_sdiff.mp xm).1
    refine mem_filter.mpr ⟨xv,?_⟩
    intro y back
    obtain ⟨yv,k,short,path⟩ := mem_ball.mp back
    exact mem_sdiff.mpr ⟨yv,fun yh => (mem_sdiff.mp xm).2
      (mem_ballSet.mpr ⟨y,yh,mem_ball.mpr ⟨xv,k,short,path.reverse_of_mem xv⟩⟩)⟩
  have kept := interior.trans (Closure.FlatPeelReach.survives (D:=J) (U:=U) sdiff_subset
    (fun x xm=>(rows x xm).le) (q-1))
  have inner (k) : rounds q J V w U k ⊆ V := by
    induction k with
    | zero => exact sdiff_subset
    | succ k ih => exact (filter_subset _ _).trans ih
  exact ⟨E,sub,Or.inr ⟨U,sdiff_subset,room,live,w,positive,rows,bill.trans
    (mul_le_mul_of_nonneg_left (mass_mono kept (fun x xm=>(positive x (inner _ xm)).le))
      (Nat.cast_nonneg q))⟩⟩

/-- Work backwards from the survivors. Keeping precisely their possible
ancestors is the cheapest carrier that protects every chosen target. -/
theorem targets_pay {q V D E} {w : ℕ→ℚ}
    (sub : ∀i j,E i j=true → D i j=true) (positive : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w < WeightedSD.col q E V w i)
    {T : Finset ℕ} (tv : T⊆V) (live : T.Nonempty)
    (room : (starts E V T (q-1)).card+1<V.card)
    (bill : mass (starts E V T (q-1)) w ≤ (q:ℚ)*mass T w) : NativeMergePays q D V := by
  let A := starts E V T (q-1)
  have av : A⊆V := filter_subset _ _
  have erase : V\(V\A)=A := Finset.sdiff_sdiff_eq_self av
  have remote : T⊆V\ballSet E V (V\A) (q-1) :=
    (misses_iff sdiff_subset tv).mpr Subset.rfl
  apply remote_pays sub positive strict (H:=V\A)
  · rwa [erase]
  · rw [erase]
    exact live.mono (targets_inside tv)
  · rw [erase]
    exact bill.trans (mul_le_mul_of_nonneg_left (mass_mono remote
      (fun x xm=>(positive x (mem_sdiff.mp xm).1).le)) (Nat.cast_nonneg q))

/-- The original one-bank price test admits a witness exactly when a
nonempty target set can protect itself at the price of its backward reach. -/
theorem bill_iff_targets {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} {w : ℕ→ℚ}
    (positive : ∀x∈V,0<w x) :
    (∃H⊆V,(V\H).card+1<V.card ∧ (V\H).Nonempty ∧
      mass (V\H) w≤(q:ℚ)*mass (V\ballSet E V H (q-1)) w) ↔
    (∃T⊆V,T.Nonempty ∧ (starts E V T (q-1)).card+1<V.card ∧
      mass (starts E V T (q-1)) w≤(q:ℚ)*mass T w) := by
  constructor
  · rintro ⟨H,hv,room,alive,paid⟩
    let T := V\ballSet E V H (q-1)
    have tv : T⊆V := sdiff_subset
    have miss := (misses_iff (E:=E) (k:=q-1) hv tv).mp (Subset.rfl : T⊆T)
    have inside : starts E V T (q-1)⊆V\H := by
      intro x xm
      exact mem_sdiff.mpr ⟨(mem_filter.mp xm).1,fun xh=>(mem_sdiff.mp (miss xh)).2 xm⟩
    have retained : 0<mass (V\H) w :=
      sum_pos (fun x xm=>positive x (mem_sdiff.mp xm).1) alive
    have live : T.Nonempty := by
      by_contra! empty
      change mass (V\H) w≤(q:ℚ)*mass T w at paid
      simp [empty,mass] at paid
      exact retained.not_ge paid
    exact ⟨T,tv,live,by have := card_le_card inside; omega,
      (mass_mono inside (fun x xm=>(positive x (mem_sdiff.mp xm).1).le)).trans paid⟩
  · rintro ⟨T,tv,live,room,paid⟩
    let A := starts E V T (q-1)
    have av : A⊆V := filter_subset _ _
    have minimize := Finset.sdiff_sdiff_eq_self av
    have miss : T⊆V\ballSet E V (V\A) (q-1) := (misses_iff sdiff_subset tv).mpr Subset.rfl
    refine ⟨V\A,sdiff_subset,?_,?_,?_⟩
    · rwa [minimize]
    · rw [minimize]; exact live.mono (targets_inside tv)
    · rw [minimize]
      exact paid.trans (mul_le_mul_of_nonneg_left
        (mass_mono miss (fun x xm=>(positive x (mem_sdiff.mp xm).1).le)) (Nat.cast_nonneg q))

/-- Strict weighted expansion is necessary at these very prices for every
target set whose backward reach leaves room for a merge. -/
def Expansion (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) : Prop :=
  ∀T⊆V,T.Nonempty → (starts E V T (q-1)).card+1<V.card →
    (q:ℚ)*mass T w<mass (starts E V T (q-1)) w

theorem expansion {q V D E} {w : ℕ→ℚ} (sub : ∀i j,E i j=true → D i j=true)
    (positive : ∀v∈V,0<w v) (strict : ∀v∈V,mass V w<WeightedSD.col q E V w v)
    (stuck : ¬NativeMergePays q D V) : Expansion q E V w := by
  intro T tv ne room
  by_contra! enough
  exact stuck (targets_pay sub positive strict tv ne room enough)

theorem at_terminal {q n c} (X : Model q n) {F : Closure.MarkedCyclePeeling.Family} {w : ℕ→ℚ}
    (hq : 2≤q) (small : SmallerSmallRow q X.V.card) (pos : ∀v∈X.V,0<w v)
    (total : mass X.V w=1) (high : 1<c)
    (flat : ∀v∈X.V,WeightedSD.col q (Closure.FirstPacketBarrier.graph X.D F) X.V w v=c) :
    Expansion q (Closure.FirstPacketBarrier.graph X.D F) X.V w := by
  apply expansion (D:=X.D) _ pos _ (no_native_merge hq X.free small)
  · intro x y xy
    obtain ⟨A,ha⟩ := Closure.FirstPacketBarrier.active.mp xy
    exact (Closure.MarkedCyclePeeling.mem_col.mp ha).2.2.2
  · intro v vm; rw [total,flat v vm]; exact high

/-- At strict row prices the same rule runs with walks reversed, so its
sets of starts are ordinary forward balls from the named targets. -/
theorem from_rows {q V E} {w : ℕ→ℚ} (hq : 2≤q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (pos : ∀x∈V,0<w x)
    (strict : ∀x∈V,mass V w<WeightedSD.row q E V w x) :
    Expansion q (fun i j=>E j i) V w :=
  expansion (fun _ _ h=>h) pos strict (no_native_merge hq free.reverse small)

theorem native_rows {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card) :
    Expansion q (fun i j=>X.D j i) X.V (fun i=>(X.weights i : ℚ)) :=
  from_rows hq X.free small (fun x xm=>by exact_mod_cast X.positive x xm) X.strict

/-- Quantify reach into the specified targets, allowing each start to reach
the same or different targets. Only unreached targets enter the bill. -/
theorem reached_mass {q V E H T} {w : ℕ→ℚ} (law : Expansion q E V w)
    (positive : ∀i∈V,0<w i) (hv : H⊆V) (tv : T⊆V)
    (room : (V\H).card+1<V.card) (alive : (V\H).Nonempty) :
    (q:ℚ)*mass T w < mass (V\H) w + q*mass (T∩ballSet E V H (q-1)) w := by
  classical
  let S := T\ballSet E V H (q-1)
  have sv : S⊆V := sdiff_subset.trans tv
  have miss := (misses_iff (E:=E) (k:=q-1) hv sv).mp
    (show S⊆V\ballSet E V H (q-1) from fun _ m=>mem_sdiff.mpr ⟨sv m,(mem_sdiff.mp m).2⟩)
  have inside : starts E V S (q-1)⊆V\H := fun x xm=>mem_sdiff.mpr
    ⟨(mem_filter.mp xm).1,fun xh=>(mem_sdiff.mp (miss xh)).2 xm⟩
  have loss : (q:ℚ)*mass S w<mass (V\H) w := by
    by_cases live : S.Nonempty
    · have r := card_le_card inside
      exact (law S sv live (by omega)).trans_le (mass_mono inside (fun x xm=>(positive x (mem_sdiff.mp xm).1).le))
    · rw [not_nonempty_iff_eq_empty] at live
      simp only [live,mass,sum_empty,mul_zero]
      exact sum_pos (fun x xm=>positive x (mem_sdiff.mp xm).1) alive
  have parts : mass S w + mass (T∩ballSet E V H (q-1)) w = mass T w := by
    unfold mass
    rw [←sum_union (Finset.disjoint_left.mpr (fun x a b=>(mem_sdiff.mp a).2 (mem_inter.mp b).2))]
    congr 1
    ext x
    simp
    tauto
  nlinarith only [loss,congrArg (fun z:ℚ=>(q:ℚ)*z) parts]

/-- At a given cap on individual target weights, the gap in the bill forces
a labelled set of any requested size allowed by that gap. -/
theorem reached_labels {q V E H T} {w : ℕ→ℚ} {price : ℚ} {k : ℕ}
    (law : Expansion q E V w) (positive : ∀i∈V,0<w i) (hv : H⊆V) (tv : T⊆V)
    (room : (V\H).card+1<V.card) (alive : (V\H).Nonempty) (unit : 0≤price)
    (cap : ∀x∈T∩ballSet E V H (q-1),w x≤price)
    (need : mass (V\H) w+(q:ℚ)*(k*price)≤q*mass T w) :
    ∃S⊆T∩ballSet E V H (q-1),S.card=k+1 := by
  have forced := reached_mass law positive hv tv room alive
  let A := T∩ballSet E V H (q-1)
  have bound : mass A w ≤ (A.card:ℚ)*price := by
    calc
      mass A w ≤ ∑ _x∈A,price := sum_le_sum cap
      _ = _ := by simp
  apply exists_subset_card_eq
  by_contra! low
  change A.card<k+1 at low
  have c : (A.card:ℚ)≤k := by exact_mod_cast (show A.card≤k by omega)
  have upper := mul_le_mul_of_nonneg_left (bound.trans (mul_le_mul_of_nonneg_right c unit)) (Nat.cast_nonneg q : (0:ℚ)≤q)
  change mass (V\H) w+(q:ℚ)*(k*price)≤q*mass T w at need
  change (q:ℚ)*mass T w < mass (V\H) w + q*mass A w at forced
  linarith

attribute [aesop safe forward (immediate := [X,hq,small,pos,total,high,flat]) (rule_sets := [CHGraphFamilies])] at_terminal
attribute [aesop safe forward (immediate := [sub,positive,strict,stuck]) (rule_sets := [CHGraphFamilies])] expansion
attribute [aesop safe forward (immediate := [sub,positive,strict,tv,live,room,bill]) (rule_sets := [CHGraphFamilies])] targets_pay
attribute [aesop safe forward (immediate := [law,positive,hv,tv,room,alive]) (rule_sets := [CHGraphFamilies])] reached_mass
attribute [aesop safe forward (immediate := [law,positive,hv,tv,room,alive,unit,cap,need]) (rule_sets := [CHGraphFamilies])] reached_labels
attribute [aesop safe forward (immediate := [hq,free,small,pos,strict]) (rule_sets := [CHGraphFamilies])] from_rows
attribute [aesop safe forward (immediate := [X,hq,small]) (rule_sets := [CHGraphFamilies])] native_rows
#print axioms native_rows
#print axioms at_terminal
#print axioms bill_iff_targets
#print axioms reached_labels
#print axioms targets_pay
end LeanCH.BR.ReverseReachPayment
