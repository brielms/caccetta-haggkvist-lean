import checkpoints.shen_extension.MinimumPunctureIncidence
import checkpoints.shen_extension.PunctureDualExtension

namespace LeanCH.BR.Closure.PunctureCycleLoop
open Finset BRq2 BRq3 BR45 ShortestCycleClasses ShortestCycleWeights

/-- Each move uses two different members of the present cycle as parents
of one marked exterior vertex in the next cycle. -/
def Step (D : CH.Digraph) (M N : Finset ℕ) : Prop :=
  ∃z∈N\M,2≤(inN D M z).card

private theorem touches {D W q z a} (rel : Relation.EqvGen (Together D W q) z a)
    (ne : z≠a) : ∃M⊆W,M.card=q+1 ∧ OutEq 1 D M ∧ z∈M := by
  classical
  by_contra miss
  have invariant {i j} (p : Relation.EqvGen (Together D W q) i j) : (i=z ↔ j=z) := by
    induction p with
    | rel i j h =>
      obtain ⟨M,mv,sz,one,im,jm⟩ := h
      exact ⟨fun eq => False.elim (miss ⟨M,mv,sz,one,eq ▸ im⟩),
        fun eq => False.elim (miss ⟨M,mv,sz,one,eq ▸ jm⟩)⟩
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ij jk => exact ij.trans jk
  exact ne (((invariant rel).mp rfl).symm)

/-- Every retained label occurs on an original shortest cycle in a large
minimum puncture, including labels supplied by a different family of moves. -/
theorem cover {n} (X : Model 3 n) (large : 13≤X.V.card) {h} (hv : h∈X.V)
    (minimum : ∀x∈X.V,X.weights h≤X.weights x) {z} (zw : z∈X.V\{h}) :
    ∃N,ShenCycleSuccessor.Cycle X.D (X.V\{h}) 3 N ∧ z∈N := by
  classical
  let W := X.V\{h}
  have tot := card_sdiff_add_card_eq_card (singleton_subset_iff.mpr hv)
  have wc : 2≤W.card := by dsimp [W]; simp only [card_singleton] at tot; omega
  have other {V : Finset ℕ} (size : 2≤V.card) (z : ℕ) : ∃a∈V,a≠z := by
    by_contra! eq
    have b := card_le_card (show V⊆{z} from fun x xv => mem_singleton.mpr (eq x xv))
    simp only [card_singleton] at b
    omega
  obtain ⟨u,uv,uh⟩ := other (V:=X.V) (by omega) h
  obtain ⟨r,rv,rh,_⟩ := X.separated h hv u uv uh
  have source := TriangleMinimumPuncture.minimum_puncture X hv minimum r rv rh
  have safe := X.free.mono_set (show W⊆X.V from sdiff_subset)
  have cover (z) (zw : z∈W) : ∃N,ShenCycleSuccessor.Cycle X.D W 3 N ∧ z∈N := by
    have zr : z∈carrier X.D W 3 r := source.symm ▸ zw
    have eq : carrier X.D W 3 z=W := (ClassParentBanks.class_eq zr).symm.trans source
    obtain ⟨a,aw,az⟩ := other wc z
    obtain ⟨N,nw,sz,one,zn⟩ := touches (mem_filter.mp (show a∈carrier X.D W 3 z from eq.symm ▸ aw)).2 (Ne.symm az)
    have reg := dt_reg (by decide : 1≤3) (ball_q_one 3 (by decide)) (safe.mono_set nw)
      (fun i hi => (one i hi).ge) (by simpa using sz)
    exact ⟨N,⟨nw,sz,one,reg.2⟩,zn⟩
  exact cover z zw

/-- A closed positive sequence of original four-cycle supports in the
minimum puncture. Consecutive supports differ, including the wraparound. -/
theorem loop {n} (X : Model 3 n) (large : 13≤X.V.card) {h} (hv : h∈X.V)
    (minimum : ∀x∈X.V,X.weights h≤X.weights x) :
    ∃(f : ℕ→Finset ℕ) (l : ℕ), 2≤l ∧ f l=f 0 ∧
      ∀i,ShenCycleSuccessor.Cycle X.D (X.V\{h}) 3 (f i) ∧ Step X.D (f i) (f (i+1)) := by
  classical
  let W := X.V\{h}
  have tot := card_sdiff_add_card_eq_card (singleton_subset_iff.mpr hv)
  have wc : 2≤W.card := by dsimp [W]; simp only [card_singleton] at tot; omega
  have cover := fun z (zw : z∈W) => PunctureCycleLoop.cover X large hv minimum zw
  let family := W.powerset.filter (ShenCycleSuccessor.Cycle X.D W 3)
  have yes {M} (c : ShenCycleSuccessor.Cycle X.D W 3 M) : M∈family :=
    mem_filter.mpr ⟨mem_powerset.mpr c.sub,c⟩
  have next (M) (mem : M∈family) : ∃N∈family,Step X.D M N := by
    have c := (mem_filter.mp mem).2
    rcases MinimumPunctureIncidence.receiver X (by decide) hv minimum c with sm | ⟨z,zz,rich⟩
    · have lim := card_le_card (show inN X.D M h⊆M from filter_subset _ _)
      have := c.size
      omega
    · obtain ⟨N,cn,zn⟩ := cover z (mem_sdiff.mp zz).1
      exact ⟨N,yes cn,z,mem_sdiff.mpr ⟨zn,(mem_sdiff.mp zz).2⟩,rich⟩
  obtain ⟨v,vw⟩ := card_pos.mp (by omega : 0<W.card)
  obtain ⟨seed,cseed,_⟩ := cover v vw
  choose! g gm gs using next
  let f := fun i : ℕ => g^[i] seed
  have fm (i) : f i∈family := by
    induction i with
    | zero => exact yes cseed
    | succ i ih => simpa only [f,Function.iterate_succ_apply'] using gm _ ih
  have fs (i) : Step X.D (f i) (f (i+1)) := by
    simpa only [f,Function.iterate_succ_apply'] using gs _ (fm i)
  obtain ⟨i,_,j,_,ij,eq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (s:=range (family.card+1)) (t:=family) (f:=f) (by simp) (fun k _ => fm k)
  have make (i j) (lt : i<j) (eq : f i=f j) :
      ∃(F : ℕ→Finset ℕ) (l : ℕ), 2≤l ∧ F l=F 0 ∧
      ∀t,ShenCycleSuccessor.Cycle X.D W 3 (F t) ∧ Step X.D (F t) (F (t+1)) := by
    have diff : f i≠f (i+1) := by
      obtain ⟨z,hz,_⟩ := fs i
      exact fun e => (mem_sdiff.mp hz).2 (e.symm ▸ (mem_sdiff.mp hz).1)
    refine ⟨fun k => f (i+k),j-i,by by_contra! bad; exact diff (by simpa [show j=i+1 by omega] using eq),?_,?_⟩
    · simpa [show i+(j-i)=j by omega] using eq.symm
    · intro t
      exact ⟨(mem_filter.mp (fm (i+t))).2,by simpa [Nat.add_assoc] using fs (i+t)⟩
  rcases Nat.lt_or_gt_of_ne ij with lt | lt
  · exact make i j lt eq
  · exact make j i lt eq.symm

#print axioms loop
end LeanCH.BR.Closure.PunctureCycleLoop
