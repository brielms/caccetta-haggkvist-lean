import checkpoints.shen_extension.ShortestCycleWeights
import LeanCH.BR.BRTightCycleReversal
import LeanCH.BR.BRWeightedCycleStructure

namespace LeanCH.BR.Closure.PuncturedDistance
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights

/-- Length of a shortest directed walk from h in the full graph.
The value zero at an unreachable vertex is unused in the cycle argument. -/
noncomputable def depth (D : CH.Digraph) (V : Finset ℕ) (h x : ℕ) : ℕ := by
  classical
  exact if p : ∃ k, Walk D V h x k then Nat.find p else 0

theorem depth_le_walk {D V h x k} (walk : Walk D V h x k) : depth D V h x ≤ k := by
  classical
  have reach : ∃ n, Walk D V h x n := ⟨k,walk⟩
  rw [depth,dite_eq_left reach]
  exact Nat.find_min' reach walk

theorem depth_step_le {D V h u v} (reach : ∃ n, Walk D V h u n)
    (vv : v ∈ V) (uv : D u v = true) : depth D V h v ≤ depth D V h u+1 := by
  classical
  have walk := (Nat.find_spec reach).snoc vv uv
  have bound := depth_le_walk walk
  change depth D V h v ≤ (if e : ∃ n, Walk D V h u n then Nat.find e else 0)+1
  simpa only [dite_eq_left reach] using bound

private theorem geodesic {D V q h x d j} (free : QFree D V q)
    (forward : Walk D V h x d) (back : Walk D V x h j)
    (positive : 0 < j) (total : d+j=q+1) : depth D V h x = d := by
  classical
  have path : ∃ k, Walk D V h x k := ⟨d,forward⟩
  rw [depth,dite_eq_left path]
  apply le_antisymm (Nat.find_min' path forward)
  by_contra! shorter
  exact free h (Nat.find path+j) (by omega) (by omega) ((Nat.find_spec path).append back)

/-- If the shortest cycle through an arc visits h, each arc except the
closing arc into h increases full-graph directed distance by exactly one. -/
theorem rise_on_cycle {D V q M h u v} (free : QFree D V q) (c : Cycle D V q M)
    (hm : h ∈ M) (um : u ∈ M) (vm : v ∈ M) (vh : v ≠ h) (uv : D u v = true) :
    depth D V h v = depth D V h u + 1 := by
  have heads (x) (xm : x ∈ M) : ∃ y ∈ M, D x y = true := by
    obtain ⟨y,hy⟩ := card_pos.mp (show 0 < (outN D M x).card by rw [c.heads x xm]; decide)
    exact ⟨y,mem_outN.mp hy⟩
  obtain ⟨i,ip,iq,walk,back⟩ := WeightedSD.tight_cycle_complementary_walks
    (free.mono_set c.sub) c.size heads hm vm (Ne.symm vh)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  obtain ⟨p,initialWalk,_,pv⟩ := walk.unsnoc
  have pm : p ∈ M := initialWalk.end_mem_or.elim (fun e => e ▸ hm) id
  have unique : (inN D M v).card = 1 := c.incoming v vm
  have eq : p = u := card_le_one.mp unique.le _ (mem_inN.mpr ⟨pm,pv⟩) _ (mem_inN.mpr ⟨um,uv⟩)
  subst p
  let k := q+1-(j+1)
  have kpos : 0 < k := by dsimp [k]; omega
  have back' : Walk D V v h k := back.mono c.sub
  have dv := geodesic free (walk.mono c.sub) back' kpos (by dsimp [k]; omega)
  have fromU : Walk D V u h (k+1) := .step (c.sub vm) uv back'
  have du := geodesic free (initialWalk.mono c.sub) fromU (by omega) (by dsimp [k]; omega)
  omega

/-- For every arc carried by a shortest cycle, deleting one vertex either
preserves such a witness through the same arc or forces an exact layer step. -/
theorem retained_or_rise {D V q h u v} (free : QFree D V q) (vh : v ≠ h)
    (uv : D u v = true) (witness : ∃ M, Cycle D V q M ∧ u ∈ M ∧ v ∈ M) :
    (∃ M, Cycle D (V \ {h}) q M ∧ u ∈ M ∧ v ∈ M) ∨
    depth D V h v = depth D V h u+1 := by
  obtain ⟨M,c,um,vm⟩ := witness
  by_cases inside : h ∈ M
  · exact Or.inr (rise_on_cycle free c inside um vm vh uv)
  · have sub : M ⊆ V \ {h} := fun x hx => mem_sdiff.mpr
      ⟨c.sub hx, fun eq => inside ((mem_singleton.mp eq) ▸ hx)⟩
    exact Or.inl ⟨M,⟨sub,c.size,c.heads,c.incoming⟩,um,vm⟩

/-- Two parents at different full-graph depths supply an actual shortest
cycle through their named receiver after puncture. It carries one parent. -/
theorem two_parents {D V q h u v t} (free : QFree D V q) (th : t ≠ h)
    (ut : D u t = true) (vt : D v t = true)
    (cu : ∃ M, Cycle D V q M ∧ u ∈ M ∧ t ∈ M)
    (cv : ∃ M, Cycle D V q M ∧ v ∈ M ∧ t ∈ M)
    (unequal : depth D V h u ≠ depth D V h v) :
    ∃ M, Cycle D (V \ {h}) q M ∧ t ∈ M ∧ (u ∈ M ∨ v ∈ M) := by
  rcases retained_or_rise free th ut cu with ⟨M,c,um,tm⟩ | ru
  · exact ⟨M,c,tm,Or.inl um⟩
  rcases retained_or_rise free th vt cv with ⟨M,c,vm,tm⟩ | rv
  · exact ⟨M,c,tm,Or.inr vm⟩
  omega

/-- The normalized CH source supplies the two full-graph edge witnesses
for every cutoff. The marked label t is also the one on the destination. -/
theorem marked_step {q budget} (X : Model q budget) (hq : 2 ≤ q) {h t A u v}
    (ca : Cycle X.D (X.V \ {h}) q A) (tw : t ∈ X.V \ {h}) (away : t ∉ A)
    (ua : u ∈ A) (va : v ∈ A) (ut : X.D u t = true) (vt : X.D v t = true)
    (unequal : depth X.D X.V h u ≠ depth X.D X.V h v) :
    ∃ M, Cycle X.D (X.V \ {h}) q M ∧ t ∈ M \ A ∧ 2 ≤ (inN X.D A t).card ∧
      (u ∈ M ∨ v ∈ M) := by
  obtain ⟨tv,nh⟩ := mem_sdiff.mp tw
  have th : t ≠ h := by simpa using nh
  have cu := edge_cycle X hq (mem_sdiff.mp (ca.sub ua)).1 tv ut
  have cv := edge_cycle X hq (mem_sdiff.mp (ca.sub va)).1 tv vt
  obtain ⟨M,c,tm,parent⟩ := two_parents X.free th ut vt cu cv unequal
  have ne : u ≠ v := fun eq => unequal (eq ▸ rfl)
  exact ⟨M,c,mem_sdiff.mpr ⟨tm,away⟩,one_lt_card.mpr
    ⟨u,mem_inN.mpr ⟨ua,ut⟩,v,mem_inN.mpr ⟨va,vt⟩,ne⟩,parent⟩

/-- Every subgraph of retained vertices whose edges lose all their shortest-cycle
witnesses is acyclic. The cutoff on the conclusion is arbitrary. -/
theorem acyclic_after_removing_witnessed_edges {D E V T q h}
    (free : QFree D V q) (sub : T ⊆ V \ {h})
    (edges : ∀ u ∈ T, ∀ v ∈ T, E u v = true →
      D u v = true ∧ (∃ M, Cycle D V q M ∧ u ∈ M ∧ v ∈ M) ∧
      ¬ (∃ M, Cycle D (V \ {h}) q M ∧ u ∈ M ∧ v ∈ M))
    (k : ℕ) : QFree E T k := by
  have increase (u) (ut : u ∈ T) (v) (vt : v ∈ T) (uv : E u v = true) :
      depth D V h v = depth D V h u+1 := by
    obtain ⟨orig,full,miss⟩ := edges u ut v vt uv
    have vh : v ≠ h := by simpa using (mem_sdiff.mp (sub vt)).2
    exact (retained_or_rise free vh orig full).resolve_left miss
  have distance_along {u v l} (walk : Walk E T u v l) (start : u ∈ T) :
      depth D V h v = depth D V h u + l := by
    induction walk with
    | refl a => omega
    | @step a b c n bm ab tail ih =>
      have inc := increase a start b bm ab
      have remaining := ih bm
      omega
  intro x l positive _ walk
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  obtain ⟨_,_,xt,_⟩ := walk.unsnoc
  have eq := distance_along walk xt
  omega

#print axioms acyclic_after_removing_witnessed_edges

/-- Deleting h preserves the shortest cycle length or makes the graph acyclic
whenever each retained arc lies on a shortest cycle before deletion. -/
theorem puncture_girth {D V q h} (free : QFree D V q)
    (full : ∀ u ∈ V \ {h}, ∀ v ∈ V \ {h}, D u v = true →
      ∃ M, Cycle D V q M ∧ u ∈ M ∧ v ∈ M) :
    (∃ M, Cycle D (V \ {h}) q M) ∨ ∀ k, QFree D (V \ {h}) k := by
  classical
  by_cases yes : ∃ M, Cycle D (V \ {h}) q M
  · exact Or.inl yes
  · right
    intro k
    exact acyclic_after_removing_witnessed_edges free ((fun _ hx => hx))
      (fun u hu v hv uv => ⟨uv,full u hu v hv uv,fun ⟨M,c,_,_⟩ => yes ⟨M,c⟩⟩) k

theorem source_puncture_girth {q budget} (X : Model q budget) (hq : 2 ≤ q) (h : ℕ) :
    (∃ M, Cycle X.D (X.V \ {h}) q M) ∨ ∀ k, QFree X.D (X.V \ {h}) k :=
  puncture_girth X.free (fun _ hu _ hv uv =>
    edge_cycle X hq (mem_sdiff.mp hu).1 (mem_sdiff.mp hv).1 uv)

#print axioms puncture_girth
#print axioms source_puncture_girth

/-- At a minimum-weight root, every surviving row retains a head, so the
acyclic alternative is impossible. No anchored configuration or size
threshold is needed to obtain this first retained shortest cycle. -/
theorem minimum_seed {q budget} (X : Model q budget) (hq : 2 ≤ q) {h}
    (hv : h ∈ X.V) (minimum : ∀ z ∈ X.V, X.weights h ≤ X.weights z) :
    ∃ M, Cycle X.D (X.V \ {h}) q M := by
  classical
  let W := X.V \ {h}
  have large : q+2 < X.V.card := by
    by_contra! small
    exact (WeightedSD.smallRow_of_card_le_add_two hq X.free small).no_strict
      X.live _ (fun _ _ => Nat.cast_nonneg _) X.strict
  have wp : W.card+1 = X.V.card := by
    simpa [W] using card_sdiff_add_card_eq_card (singleton_subset_iff.mpr hv)
  have hasHead (u) (uw : u ∈ W) : 1 ≤ (outN X.D W u).card := by
    by_contra! zero
    have uv := (mem_sdiff.mp uw).1
    have only (z) (zv : z ∈ X.V) (uz : X.D u z = true) : z = h := by
      by_contra ne
      have zw : z ∈ W := mem_sdiff.mpr ⟨zv,by simpa using ne⟩
      have pos := card_pos.mpr (show (outN X.D W u).Nonempty from ⟨z,mem_outN.mpr ⟨zw,uz⟩⟩)
      omega
    have headMass : (∑ z ∈ X.V, if X.D u z = true then X.weights z else 0) ≤ X.weights h := by
      calc
        _ ≤ ∑ z ∈ X.V, if z = h then X.weights h else 0 := by
          apply sum_le_sum
          intro z hz
          by_cases edge : X.D u z = true
          · rw [ite_eq_left edge,ite_eq_left (only z hz edge),only z hz edge]
          · simp [edge]
        _ = _ := by simp [hv]
    have lower : (X.V.erase u).card * X.weights h ≤ ∑ z ∈ X.V.erase u, X.weights z := by
      simpa using sum_le_sum (s := X.V.erase u) (fun z hz => minimum z (mem_of_mem_erase hz))
    have c := card_erase_add_one uv
    have count : q ≤ (X.V.erase u).card := by omega
    have mass := (Nat.mul_le_mul_right (X.weights h) count).trans lower
    have total := sum_erase_add X.V X.weights uv
    have strict := ShenPrimeTransition.nat_strict.mp X.strict u uv
    unfold ShenPrimeTransition.score at strict
    have cap := Nat.mul_le_mul_left q headMass
    omega
  rcases source_puncture_girth X hq h with yes | acyclic
  · exact yes
  · have kpos : 1 ≤ W.card := by omega
    have bound := dt_size kpos (ball_q_one W.card kpos) (acyclic W.card)
      hasHead (card_pos.mp kpos)
    simp only [Nat.mul_one] at bound
    change W.card+1 ≤ W.card at bound
    omega

/-- Counterexample input in the order and minimum-outdegree variables of CH.
Every minimum-weight root of the same normalized model admits a seed. -/
theorem seed_from_input {n r : ℕ} {D : CH.Digraph}
    (hn : 0 < n) (hr : 0 < r) (loop : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n r)
    (no : ¬ CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r)) :
    let q := CH.ceilDiv n r
    ∃ X : Model q n, ∀ h ∈ X.V, (∀ z ∈ X.V, X.weights h ≤ X.weights z) →
      ∃ M, Cycle X.D (X.V \ {h}) q M := by
  let q := CH.ceilDiv n r
  have cover : n ≤ q*r := by
    have rem := Nat.mod_lt (n+r-1) hr
    have div := Nat.mod_add_div (n+r-1) r
    rw [Nat.mul_comm r] at div
    dsimp [q,CH.ceilDiv]
    omega
  have rn : r < n := by
    obtain ⟨heads,size,distinct,valid⟩ := degree 0 hn
    have sub : heads.toFinset ⊆ (range n).erase 0 := by
      intro x hx
      obtain ⟨xn,edge⟩ := valid x (List.mem_toFinset.mp hx)
      refine mem_erase.mpr ⟨?_,mem_range.mpr xn⟩
      rintro rfl
      rw [loop 0 hn] at edge
      exact Bool.false_ne_true edge
    have count := card_le_card sub
    rw [List.toFinset_card_of_nodup distinct,size,card_erase_of_mem (by simp [hn]),card_range] at count
    omega
  have hq : 2 ≤ q := by
    by_contra! small
    have bound := Nat.mul_le_mul_right r (show q ≤ 1 by omega)
    rw [Nat.one_mul] at bound
    omega
  obtain ⟨X⟩ := normalize hq hn cover loop degree no
  exact ⟨X,fun _ hv minimum => minimum_seed X hq hv minimum⟩

#print axioms seed_from_input

#print axioms minimum_seed

#print axioms retained_or_rise
#print axioms two_parents
#print axioms marked_step
end LeanCH.BR.Closure.PuncturedDistance
