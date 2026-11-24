import checkpoints.shen_extension.BalancedSecondNeighborhood
import checkpoints.shen_extension.SingleArcCycleParents

namespace LeanCH.BR.Closure.SingletonSecondNeighbors
open Finset BRq2 BRq3 BR45 WeightedSD
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling

abbrev adj (E : CH.Digraph) (V : Finset ℕ) (i j : V) := E i j=true

theorem three_free {q E V} (hq : 3≤q) (free : QFree E V q) : BalancedSecondNeighborhood.IsThreeFree (adj E V) := by
  refine ⟨⟨fun i=>loopfree free (by omega) i.property,fun i j ij ji=>?_⟩,fun i j k ij jk ki=>?_⟩
  · exact free i 2 (by omega) (by omega) (.step j.property ij (.step i.property ji (.refl _)))
  · exact free i 3 (by omega) hq (.step j.property ij (.step k.property jk (.step i.property ki (.refl _))))

/-- The regular order exits apply to an induced support inside the
original input, without a regularity hypothesis on the remaining rows. -/
theorem regular_order {q E V} (hq : 3≤q) (free : QFree E V q)
    {U : Finset ℕ} (sub : U⊆V) (live : U.Nonempty) {d : ℕ} (small : d=3 ∨ d=4 ∨ d=5)
    (outD : ∀i∈U,(outN E U i).card=d) (inD : ∀i∈U,(inN E U i).card=d) : 3*d+1≤U.card := by
  have counts (P : ℕ→Prop) [DecidablePred P] :
      (univ.filter (fun i : U=>P i)).card=(U.filter P).card := by
    change (U.attach.filter (fun i=>P i.val)).card=_
    rw [filter_attach,card_map,card_attach]
  have reg : BalancedSecondNeighborhood.IsRegular (adj E U) d := ⟨fun i=>(counts (fun j=>E i j=true)).trans (outD i i.property),
    fun i=>(counts (fun j=>E j i=true)).trans (inD i i.property)⟩
  have f := three_free hq (free.mono_set sub)
  obtain ⟨i,hi⟩ := live
  let ne : Nonempty U := ⟨⟨i,hi⟩⟩
  rcases small with rfl|rfl|rfl
  · simpa using BalancedSecondNeighborhood.regular_threeFree_order_ge_of_e2 _ f reg ne (BalancedSecondNeighborhood.regular_oriented_three_e2 _ f.1 reg)
  · simpa using BalancedSecondNeighborhood.regular_threeFree_four_order_ge_13 _ f reg ne
  · simpa using BalancedSecondNeighborhood.regular_threeFree_five_order_ge_16 _ f reg ne

private theorem ent {q E V} (hq : 3≤q) (free : QFree E V q) (a v : V) (av : E a v=true) :
    BalancedSecondNeighborhood.isEnt (adj E V) a v := ⟨av,fun ⟨j,vj,ja⟩=>(three_free hq free).2 a v j av vj ja⟩

/-- At the marked old arc the side theorem applies to any single
balanced weight. Flat row and column weights may differ. -/
theorem balanced_ports {q E V} (hq : 3≤q) (free : QFree E V q) (a v : V) (av : E a v=true)
    (k : V→ℝ) (pos : ∀i,0≤k i) (bal : BalancedSecondNeighborhood.IsBalanced (adj E V) k) :
    let A := adj E V
    k v+k a≤(∑i∈BalancedSecondNeighborhood.outN A v ∩ BalancedSecondNeighborhood.nonAdj A a,k i)+(∑i∈BalancedSecondNeighborhood.inN A a ∩ BalancedSecondNeighborhood.nonAdj A v,k i) :=
  (BalancedSecondNeighborhood.nonTriangle_arc_P2_bound _ (three_free hq free).1 pos bal (ent hq free a v av)).1

/-- On an arbitrary heavy midpoint with the heir and first-child laws,
the two old flat weights give separate exact budgets on distance-two
pairs. Balance of either weight is unnecessary. -/
theorem flat_ports {q E V} (hq : 3≤q) (free : QFree E V q) (a v : V) (av : E a v=true)
    (first : ∀i∈V,i≠v.val → E a i=true → E v i=true)
    (heir : ∀i∈V,i≠a.val → E i v=true → E i a=true)
    {w p : ℕ→ℚ} (wr : ∀i∈V,WeightedSD.row q E V w i=1) (pc : ∀i∈V,WeightedSD.col q E V p i=1) :
    let B := outN E V v \ outN E V a
    let P := inN E V a \ inN E V v
    (q:ℚ)*mass B w=((q:ℚ)-1)*w v+w a ∧ (q:ℚ)*mass P p=((q:ℚ)-1)*p a+p v ∧
      (∀i : V,i.val∈B → BalancedSecondNeighborhood.isP2 (adj E V) a i) ∧
      (∀i : V,i.val∈P → BalancedSecondNeighborhood.isP2 (adj E V) i v) := by
  intro B P
  have law {S K : Finset ℕ} {j : ℕ} (u : ℕ→ℚ) (com : S \ K={j}) :
      mass (K \ S) u=mass K u-mass S u+u j := by
    have split (A B : Finset ℕ) : mass (A \ B) u + mass (A ∩ B) u=mass A u := by
      unfold mass
      rw [←sum_union (disjoint_left.mpr (fun _ h h' => (mem_sdiff.mp h).2 (mem_inter.mp h').2))]
      congr 1; ext i; by_cases h : i∈B <;> simp [h]
    have ss := split S K
    rw [com,inter_comm] at ss
    simp only [mass,sum_singleton] at ss
    have kk := split K S
    unfold mass at *
    linarith
  have fs : outN E V a \ outN E V v={v.val} := by
    ext i
    constructor
    · intro h
      obtain ⟨ai,vi⟩ := mem_sdiff.mp h
      obtain ⟨iv,ed⟩ := mem_outN.mp ai
      exact mem_singleton.mpr (by by_contra ne; exact vi (mem_outN.mpr ⟨iv,first i iv ne ed⟩))
    · intro h
      obtain rfl := mem_singleton.mp h
      exact mem_sdiff.mpr ⟨mem_outN.mpr ⟨v.property,av⟩,fun h=>loopfree free (by omega) v.property (mem_outN.mp h).2⟩
  have hs : inN E V v \ inN E V a={a.val} := by
    ext i
    constructor
    · intro h
      obtain ⟨iv,ia⟩ := mem_sdiff.mp h
      obtain ⟨mem,ed⟩ := mem_inN.mp iv
      exact mem_singleton.mpr (by by_contra ne; exact ia (mem_inN.mpr ⟨mem,heir i mem ne ed⟩))
    · intro h
      obtain rfl := mem_singleton.mp h
      exact mem_sdiff.mpr ⟨mem_inN.mpr ⟨a.property,av⟩,fun h=>loopfree free (by omega) a.property (mem_inN.mp h).2⟩
  have row (i : V) : w i+(q:ℚ)*mass (outN E V i) w=1 := by simpa [WeightedSD.row,outW_eq_mass] using wr i i.property
  have col (i : V) : p i+(q:ℚ)*mass (inN E V i) p=1 := by
    simpa [WeightedSD.col,inW,mass,inN,sum_filter] using pc i i.property
  have f := three_free hq free
  refine ⟨?_,?_,?_,?_⟩
  · change (q:ℚ)*mass (outN E V v \ outN E V a) w=_
    rw [law w fs]; linarith only [row a,row v]
  · change (q:ℚ)*mass (inN E V a \ inN E V v) p=_
    rw [law p hs]; linarith only [col a,col v]
  · intro i hi
    obtain ⟨vi,ai⟩ := mem_sdiff.mp hi
    have vi' : adj E V v i := (mem_outN.mp vi).2
    exact ⟨fun eq=>f.1.2 a v av (eq ▸ vi'),fun h=>ai (mem_outN.mpr ⟨i.property,h⟩),
      f.2 a v i av vi',v,av,vi'⟩
  · intro i hi
    obtain ⟨ia,iv⟩ := mem_sdiff.mp hi
    have ia' : adj E V i a := (mem_inN.mp ia).2
    exact ⟨fun eq=>f.1.2 i a ia' (eq ▸ av),fun h=>iv (mem_inN.mpr ⟨i.property,h⟩),
      f.2 i a v ia' av,a,ia',av⟩

end LeanCH.BR.Closure.SingletonSecondNeighbors
#print axioms LeanCH.BR.Closure.SingletonSecondNeighbors.regular_order
#print axioms LeanCH.BR.Closure.SingletonSecondNeighbors.balanced_ports
#print axioms LeanCH.BR.Closure.SingletonSecondNeighbors.flat_ports
