import checkpoints.shen_extension.SharedArcPivotMerge
import checkpoints.shen_extension.SingleArcModuleBoundary

namespace LeanCH.BR.Closure.StrictFlatSubsetMerge
open Finset BRq2 BRq3 BR45 BRsub WeightedSD SharedArcPivotMerge
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling

def common (D : CH.Digraph) (V S : Finset ℕ) : Finset ℕ :=
  V.filter (fun y => ∀s∈S,D s y=true)

/-- If the representative can pay its row, every exterior vertex sees
all or none of the merged set. All vertex weights are positive. -/
theorem uniform_of_merge_feasible {q : ℕ} (hq : 2≤q) {D : CH.Digraph} {V S : Finset ℕ}
    (free : QFree D V q) (small : SmallerSmallRow q V.card) (sub : S⊆V) (size : 2≤S.card)
    {w : ℕ→ℚ} (pos : ∀x∈V,0<w x) (rows : ∀x∈V,mass V w≤WeightedSD.row q D V w x)
    (paid : mass V w≤mass S w+q*mass (common D V S) w) : InUniform D V S := by
  classical
  obtain ⟨z,zs⟩ := card_pos.mp (show 0<S.card by omega)
  let U := V \ S
  let Z := mergeV V S z
  let G := mergeOut D V S z
  let w' (x : ℕ) := if x=z then mass S w else w x
  have outside {x} (xu : x∈U) : x≠z := fun e => (mem_sdiff.mp xu).2 (e ▸ zs)
  have split (g : ℕ→ℚ) : (∑y∈Z,g y)=g z+∑y∈U,g y := by
    change (∑y∈insert z U,g y)=_
    exact sum_insert (fun zu => outside zu rfl)
  have same (x) (xu : x∈U) : w' x=w x := by simp [w',outside xu]
  have addParts (g : ℕ→ℚ) : (∑y∈S,g y)+(∑y∈U,g y)=∑y∈V,g y := by
    rw [add_comm]; exact sum_sdiff sub
  have sw : 0<mass S w := sum_pos (fun x xs => pos x (sub xs)) ⟨z,zs⟩
  have wz : w' z=mass S w := by simp [w']
  have mw : mass Z w'=mass V w := by
    rw [mass,split,wz,sum_congr rfl same]; exact addParts w
  have wpos (x) (xz : x∈Z) : 0<w' x := by
    rcases mem_insert.mp xz with rfl|xu
    · rwa [wz]
    · rw [same x xu]; exact pos x (mem_sdiff.mp xu).1
  have cz : outW G Z w' z=mass (common D V S) w := by
    have filterEq : U.filter (fun y => G z y=true)=common D V S := by
      ext y
      simp only [common,mem_filter]
      constructor
      · rintro ⟨yu,e⟩
        have pair : y∈V \ S ∧ ∀s∈S,D s y=true := by simpa only [G,mergeOut,ite_true,decide_eq_true_eq] using e
        exact ⟨(mem_sdiff.mp yu).1,pair.2⟩
      · rintro ⟨yv,all⟩
        have yu : y∈U := mem_sdiff.mpr ⟨yv,fun ys => loopfree free (by omega) yv (all y ys)⟩
        exact ⟨yu,by simpa only [G,mergeOut,ite_true,decide_eq_true_eq] using And.intro yu all⟩
    have noLoop : G z z=false := by simp [G,mergeOut,zs]
    rw [outW,split,noLoop]; simp only [Bool.false_eq_true,ite_false,zero_add]
    rw [←sum_filter,←filterEq,mass]
    exact sum_congr rfl (fun i hi => same i (mem_filter.mp hi).1)
  have loss (x) (xu : x∈U) :
      outW G Z w' x-outW D V w x =
        (if ∃s∈S,D x s=true then mass S w else 0)-outW D S w x := by
    have eq (y) (yu : y∈U) : G x y=D x y := by simp [G,mergeOut,outside xu,outside yu,
      show x∈V \ S from xu,show y∈V \ S from yu]
    have head : G x z=true ↔ ∃s∈S,D x s=true := by simp [G,mergeOut,outside xu,show x∈V \ S from xu]
    have zsum := split (fun y => if G x y=true then w' y else 0)
    have us := addParts (fun y => if D x y=true then w y else 0)
    have restEq : (∑y∈U,if G x y=true then w' y else 0)=(∑y∈U,if D x y=true then w y else 0) :=
      sum_congr rfl (fun y yu => by rw [eq y yu,same y yu])
    simp only [head,wz,restEq] at zsum
    unfold outW; linarith only [zsum,us]
  have monotone (x) (xu : x∈U) : outW D V w x ≤ outW G Z w' x := by
    apply sub_nonneg.mp
    rw [loss x xu]
    by_cases hit : ∃s∈S,D x s=true
    · rw [ite_eq_left hit,sub_nonneg,outW_eq_mass]
      exact mass_mono outN_subset (fun i hi => (pos i (sub hi)).le)
    · have zero : outW D S w x=0 := sum_eq_zero fun s hs => ite_eq_right (fun e => hit ⟨s,hs,e⟩)
      rw [ite_eq_right hit,zero]; norm_num
  have feasible (x) (xz : x∈Z) : mass Z w'≤WeightedSD.row q G Z w' x := by
    rw [mw]
    rcases mem_insert.mp xz with rfl|xu
    · simpa only [WeightedSD.row,wz,cz] using paid
    · rw [WeightedSD.row,same x xu]
      exact (rows x (mem_sdiff.mp xu).1).trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (monotone x xu) (Nat.cast_nonneg q)))
  have tight := positive_feasible_rows_tight_of_smallRow hq
    (small G Z (mergeV_card_lt sub size zs) (mergeOut_qfree free sub zs)) w' wpos feasible
  have all (x) (xu : x∈U) (hit : ∃s∈S,D x s=true) (y) (ys : y∈S) : D x y=true := by
    by_contra miss
    have lost : outW D S w x<mass S w := by
      apply sum_lt_sum
      · intro j js; split <;> first | exact le_rfl | exact (pos j (sub js)).le
      · exact ⟨y,ys,by simp [miss,pos y (sub ys)]⟩
    have diff := loss x xu
    rw [ite_eq_left hit] at diff
    have gt := mul_lt_mul_of_pos_left (show outW D V w x<outW G Z w' x by linarith only [diff,lost])
      (show (0:ℚ)<q by exact_mod_cast (by omega : 0<q))
    have tt := tight x (mem_insert_of_mem xu)
    rw [mw,WeightedSD.row,same x xu] at tt
    have rr := rows x (mem_sdiff.mp xu).1
    unfold WeightedSD.row at rr
    linarith only [gt,tt,rr]
  intro i is j js x xv xs
  have xu : x∈U := mem_sdiff.mpr ⟨xv,xs⟩
  by_cases hit : ∃s∈S,D x s=true
  · rw [all x xu hit i is,all x xu hit j js]
  · exact (Bool.eq_false_iff.mpr (fun e => hit ⟨i,is,e⟩)).trans
      (Bool.eq_false_iff.mpr (fun e => hit ⟨j,js,e⟩)).symm

/-- Strict in both orientations on every proper nontrivial subset of an
unsaturated flat graph. No regularity or ambient order restriction. -/
theorem strict {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V : Finset ℕ}
    (free : QFree E V q) (small : SmallerSmallRow q V.card) (unsat : ¬Sat q E V)
    {w p : ℕ→ℚ} (pos : ∀x∈V,0<w x ∧ 0<p x)
    (rows : ∀x∈V,mass V w≤WeightedSD.row q E V w x)
    (cols : ∀x∈V,mass V p≤WeightedSD.col q E V p x)
    {S : Finset ℕ} (sub : S⊆V) (size : 2≤S.card) (proper : S≠V) :
    mass S w+q*mass (common E V S) w<mass V w ∧
    mass S p+q*mass (common (fun i j => E j i) V S) p<mass V p := by
  have rev : ¬Sat q (fun i j => E j i) V := fun sat => unsat (SerialChain.sat_reverse sat)
  constructor
  · apply lt_of_not_ge
    intro paid
    exact positive_feasible_nonsaturated_out_prime (D:=fun i j => E j i) hq small free.reverse rev p
      (fun i hi => (pos i hi).2) cols S sub size proper
      (uniform_of_merge_feasible hq free small sub size (fun i hi => (pos i hi).1) rows paid)
  · apply lt_of_not_ge
    intro paid
    exact positive_feasible_nonsaturated_out_prime hq small free unsat w
      (fun i hi => (pos i hi).1) rows S sub size proper
      (uniform_of_merge_feasible (D:=fun i j => E j i) hq free.reverse small sub size
        (fun i hi => (pos i hi).2) cols paid)

theorem native {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) (f : SharedArcFlatCut.Missing X F)
    {w p : ℕ→ℚ} (pos : ∀x∈X.V,0<w x ∧ 0<p x)
    (rows : ∀x∈X.V,mass X.V w≤WeightedSD.row q (graph X.D F) X.V w x)
    (cols : ∀x∈X.V,mass X.V p≤WeightedSD.col q (graph X.D F) X.V p x)
    {S : Finset ℕ} (sub : S⊆X.V) (size : 2≤S.card) (proper : S≠X.V) :
    mass S w+q*mass (common (graph X.D F) X.V S) w<mass X.V w ∧
    mass S p+q*mass (common (fun i j => graph X.D F j i) X.V S) p<mass X.V p := by
  have notmod := SingleArcModuleBoundary.on_flat X hq small F f pos rows cols S sub size proper
  have free := PrivateArcEndpoints.graph_free X F
  constructor
  · exact lt_of_not_ge fun paid => notmod.2 (uniform_of_merge_feasible hq free small sub size
      (fun i hi => (pos i hi).1) rows paid)
  · exact lt_of_not_ge fun paid => notmod.1 (uniform_of_merge_feasible (D:=fun i j => graph X.D F j i) hq
      free.reverse small sub size (fun i hi => (pos i hi).2) cols paid)

/-- The old feasible weights also satisfy both strict merge bounds on the
saturated prime host, where common neighbourhoods can be larger. -/
theorem host {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (pos : ∀x∈X.V,0<w x ∧ 0<p x)
    (rows : ∀x∈X.V,mass X.V w≤WeightedSD.row q (graph X.D F) X.V w x)
    (cols : ∀x∈X.V,mass X.V p≤WeightedSD.col q (graph X.D F) X.V p x)
    {S : Finset ℕ} (sub : S⊆X.V) (size : 2≤S.card) (proper : S≠X.V) :
    mass S w+q*mass (common X.D X.V S) w<mass X.V w ∧
    mass S p+q*mass (common (fun i j => X.D j i) X.V S) p<mass X.V p := by
  have edge (i) (_ : i∈X.V) (j) (_ : j∈X.V) (ed : graph X.D F i j=true) : X.D i j=true :=
    (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have rq (i) (hi : i∈X.V) : mass X.V w≤WeightedSD.row q X.D X.V w i :=
    (rows i hi).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (outW_mono_graph edge (fun j hj => (pos j hj).1.le) hi) (Nat.cast_nonneg q)))
  have cq (i) (hi : i∈X.V) : mass X.V p≤WeightedSD.col q X.D X.V p i :=
    (cols i hi).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (inW_mono_graph edge (fun j hj => (pos j hj).2.le) hi) (Nat.cast_nonneg q)))
  have prime := X.prime S sub size proper
  constructor
  · apply lt_of_not_ge
    intro paid
    have inc := uniform_of_merge_feasible hq X.free small sub size (fun i hi => (pos i hi).1) rq paid
    exact prime ⟨outUniform_inUniform (D:=fun i j => X.D j i) X.free.reverse
      (SerialChain.sat_reverse X.sat) sub inc,inc⟩
  · apply lt_of_not_ge
    intro paid
    have out := uniform_of_merge_feasible (D:=fun i j => X.D j i) hq X.free.reverse small sub size
      (fun i hi => (pos i hi).2) cq paid
    exact prime ⟨out,outUniform_inUniform X.free X.sat sub out⟩

private theorem reserve {q : ℕ} {E D : CH.Digraph} {V S : Finset ℕ} {w : ℕ→ℚ} {a b : ℕ}
    (edge : ∀i j,E i j=true → D i j=true) (off : E a b=false) (on : D a b=true)
    (bv : b∈V) (as : a∈S) (others : ∀s∈S,s≠a → E s b=true)
    (pos : ∀i∈V,0<w i) (bound : mass S w+q*mass (common D V S) w<mass V w) :
    mass S w+q*(w b+mass (common E V S) w)<mass V w := by
  have old : b∉common E V S := fun h => Bool.noConfusion (off.symm.trans ((mem_filter.mp h).2 a as))
  have sub : insert b (common E V S)⊆common D V S := by
    apply insert_subset_iff.mpr
    constructor
    · refine mem_filter.mpr ⟨bv,fun i hi => ?_⟩
      by_cases ia : i=a
      · exact ia ▸ on
      · exact edge i b (others i hi ia)
    · intro y hy
      exact mem_filter.mpr ⟨(mem_filter.mp hy).1,fun i hi => edge i y ((mem_filter.mp hy).2 i hi)⟩
  have le := mass_mono sub (fun i hi => (pos i (mem_filter.mp hi).1).le)
  have ins : mass (insert b (common E V S)) w=w b+mass (common E V S) w := sum_insert old
  rw [ins] at le
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left le (Nat.cast_nonneg q))).trans_lt bound

/-- On the old predecessor side the gap exceeds q times the weight of
the new head. The transpose gives the same statement for successors. -/
theorem endpoint_reserve {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) (f : SharedArcFlatCut.Missing X F) {w p : ℕ→ℚ}
    (pos : ∀x∈X.V,0<w x ∧ 0<p x)
    (rows : ∀x∈X.V,mass X.V w≤WeightedSD.row q (graph X.D F) X.V w x)
    (cols : ∀x∈X.V,mass X.V p≤WeightedSD.col q (graph X.D F) X.V p x)
    {S : Finset ℕ} (sub : S⊆X.V) (size : 2≤S.card) (proper : S≠X.V) :
    (f.val.1.val∈S → (∀s∈S,s≠f.val.1.val → graph X.D F s f.val.2=true) →
      mass S w+q*(w f.val.2+mass (common (graph X.D F) X.V S) w)<mass X.V w) ∧
    (f.val.2.val∈S → (∀s∈S,s≠f.val.2.val → graph X.D F f.val.1 s=true) →
      mass S p+q*(p f.val.1+mass (common (fun i j => graph X.D F j i) X.V S) p)<mass X.V p) := by
  have both := host X hq small F pos rows cols sub size proper
  have edge (i j) (ed : graph X.D F i j=true) : X.D i j=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  exact ⟨fun hit rest => reserve edge f.property.2 f.property.1 f.val.2.property hit rest
      (fun i hi => (pos i hi).1) both.1,
    fun hit rest => reserve (E:=fun i j => graph X.D F j i) (D:=fun i j => X.D j i)
      (fun i j => edge j i) f.property.2 f.property.1 f.val.1.property hit rest
      (fun i hi => (pos i hi).2) both.2⟩

end LeanCH.BR.Closure.StrictFlatSubsetMerge
#print axioms LeanCH.BR.Closure.StrictFlatSubsetMerge.strict
#print axioms LeanCH.BR.Closure.StrictFlatSubsetMerge.native
#print axioms LeanCH.BR.Closure.StrictFlatSubsetMerge.endpoint_reserve
