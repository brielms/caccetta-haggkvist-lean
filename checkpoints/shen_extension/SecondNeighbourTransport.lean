import checkpoints.shen_extension.InducedPrimeTransition
import checkpoints.shen_extension.HalfRowsSink
import checkpoints.shen_extension.TightCycleSuccessor
import Mathlib.Combinatorics.Hall.Finite

namespace LeanCH.BR.ShenSecondNeighbour
open BRq2 BRq3 ShenPrimeTransition Finset

def exits (D : CH.Digraph) (V O S : Finset ℕ) : Finset ℕ :=
  S.biUnion (outN D (V \ O))

private theorem score_out (q D V w a) :
    score q D V w a = w a + q * ∑ z ∈ outN D V a, w z := by simp [score,outN,sum_filter]

/-- Restricting one light row of S either loses actual heads outside O, or
the ambient row could not have reached the score of the original root. -/
theorem exit_cut {D V q w u} (hq : 1 ≤ q) {S : Finset ℕ}
    (sub : S ⊆ outN D V u) {a} (ha : a ∈ S)
    (light : score q D S w a ≤ ∑ z ∈ S, w z)
    (floor : score q D V w u ≤ score q D V w a) :
    (q-1)*(∑ z ∈ S, w z) + w u ≤ q * ∑ z ∈ exits D V (outN D V u) S, w z := by
  let O := outN D V u
  let E := exits D V O S
  have cover : outN D V a ⊆ (outN D S a ∪ (O \ S)) ∪ E := by
    intro z hz
    obtain ⟨hv,arc⟩ := mem_outN.mp hz
    by_cases ho : z ∈ O
    · apply mem_union_left
      by_cases hin : z ∈ S
      · exact mem_union_left _ (mem_outN.mpr ⟨hin,arc⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨ho,hin⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨a,ha,mem_outN.mpr ⟨mem_sdiff.mpr ⟨hv,ho⟩,arc⟩⟩)
  have upper : (∑ z ∈ outN D V a, w z) ≤
      (∑ z ∈ outN D S a, w z) + (∑ z ∈ O \ S, w z) + ∑ z ∈ E, w z := by
    have h := sum_le_sum_of_subset_of_nonneg (f:=w) cover (by intros; omega)
    have h₁ := sum_union_inter (f:=w) (s₁:=outN D S a ∪ (O \ S)) (s₂:=E)
    have h₂ := sum_union_inter (f:=w) (s₁:=outN D S a) (s₂:=O \ S)
    omega
  have partition := sum_sdiff (f:=w) sub
  rw [score_out] at light
  simp only [score_out] at floor
  change (∑ z ∈ O \ S, w z) + _ = ∑ z ∈ O, w z at partition
  change w u + q * (∑ z ∈ O, w z) ≤ _ at floor
  have up := Nat.mul_le_mul_left q upper
  have eq := congrArg (q * ·) partition
  have pred := congrArg (· * ∑ z ∈ S, w z) (show q-1+1=q by omega)
  simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul] at up eq pred
  change _ ≤ q * ∑ z ∈ E, w z
  omega

/-- Capacity units keep the vertex label and its local slot index. -/
def units {ι : Type*} (S : Finset ι) (load : ι → ℕ) : Finset (Σ _ : ι, ℕ) :=
  S.sigma fun a => range (load a)

private theorem units_card {ι : Type*} (S : Finset ι) (d : ι → ℕ) :
    (units S d).card = ∑ a ∈ S, d a := by simp [units,card_sigma]

def demand (q : ℕ) (w : ℕ → ℕ) (u pin a : ℕ) :=
  (q-1)*w a + if a=pin then w u else 0

def Assigned (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℕ) (u pin : ℕ) : Prop :=
  ∃ f : (units (outN D V u) (demand q w u pin)) → (Σ _ : ℕ, ℕ),
    Function.Injective f ∧ ∀ i, (f i).1 ∈ outN D (V \ outN D V u) i.val.1 ∧ (f i).2 < q*w (f i).1

/-- Hall with labelled capacity units on both sides; different colours on
the left may name the very same destination label on the right. -/
private theorem realize_cuts {ι : Type*} [DecidableEq ι] (K : Finset ι) (load : ι → ℕ)
    (reach : ι → Finset ℕ) (cap : ℕ → ℕ)
    (hall : ∀ S ⊆ K, (∑ a ∈ S, load a) ≤ ∑ z ∈ S.biUnion reach, cap z) :
    ∃ f : (units K load) → (Σ _ : ℕ, ℕ), Function.Injective f ∧
      ∀ i, (f i).1 ∈ reach i.val.1 ∧ (f i).2 < cap (f i).1 := by
  classical
  let choices (i : units K load) := units (reach i.val.1) cap
  have test (A : Finset (units K load)) : A.card ≤ (A.biUnion choices).card := by
    let S := A.image (fun i => i.val.1)
    have sub : S ⊆ K := by
      intro a ha
      obtain ⟨i,_,rfl⟩ := mem_image.mp ha
      exact (mem_sigma.mp i.property).1
    have left : A.image Subtype.val ⊆ units S load := by
      intro t ht
      obtain ⟨i,hi,rfl⟩ := mem_image.mp ht
      exact mem_sigma.mpr ⟨mem_image_of_mem _ hi,(mem_sigma.mp i.property).2⟩
    have right : units (S.biUnion reach) cap ⊆ A.biUnion choices := by
      intro t ht
      obtain ⟨b,hb,edge⟩ := mem_biUnion.mp (mem_sigma.mp ht).1
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hb
      exact mem_biUnion.mpr ⟨i,hi,mem_sigma.mpr ⟨edge,(mem_sigma.mp ht).2⟩⟩
    have lo := card_le_card left
    have hi := card_le_card right
    rw [card_image_of_injective _ Subtype.val_injective,units_card] at lo
    rw [units_card] at hi
    exact lo.trans ((hall S sub).trans hi)
  obtain ⟨f,inj,ok⟩ := (all_card_le_biUnion_card_iff_existsInjective' choices).mp test
  exact ⟨f,inj,fun i => ⟨(mem_sigma.mp (ok i)).1,mem_range.mp (mem_sigma.mp (ok i)).2⟩⟩

/-- A single assignment pays all rows at this root simultaneously. Failure
gives a strict induced subgraph with the very same weighting. -/
theorem descent_or_assign {D V q w u} (hq : 1 ≤ q)
    (floor : ∀ a ∈ outN D V u, score q D V w u ≤ score q D V w a) :
    (∃ S ⊆ outN D V u, S.Nonempty ∧ Strict q D S w) ∨
      ∀ pin ∈ outN D V u, Assigned q D V w u pin := by
  classical
  by_cases smaller : ∃ S ⊆ outN D V u, S.Nonempty ∧ Strict q D S w
  · exact Or.inl smaller
  right
  intro pin _
  let O := outN D V u
  let supply := fun z => q*w z
  let d := demand q w u pin
  apply realize_cuts O d (outN D (V \ O)) supply
  intro S sub
  by_cases empty : S = ∅
  · simp [empty]
  have low : ¬Strict q D S w := fun yes => smaller ⟨S,sub,nonempty_iff_ne_empty.mpr empty,yes⟩
  rw [nat_strict] at low
  push Not at low
  obtain ⟨a,ha,light⟩ := low
  have cut := exit_cut hq sub ha light (floor a (sub ha))
  have cap : (∑ z ∈ S, d z) ≤ (q-1)*(∑ z ∈ S, w z) + w u := by
    simp only [d,demand,sum_add_distrib,←mul_sum,sum_ite_eq']
    split_ifs <;> omega
  simpa only [supply,←mul_sum,exits,O] using cap.trans cut

/-- Even after deletions, a used endpoint is either a deleted original
head of u or originally nonadjacent to u. Both parts use the same labels. -/
theorem destination_ancestry {G H V u a z} (free : QFree G V 3) (hu : u∈V)
    (keep : ∀ x∈V, ∀ y∈V, H x y=true → G x y=true)
    (ha : a ∈ outN H V u) (hz : z ∈ outN H (V \ outN H V u) a) :
    z ≠ u ∧ G z u ≠ true ∧ (z ∈ outN G V u \ outN H V u ∨ G u z ≠ true) := by
  obtain ⟨av,ua⟩ := mem_outN.mp ha
  obtain ⟨live,az⟩ := mem_outN.mp hz
  obtain ⟨zv,old⟩ := mem_sdiff.mp live
  have e := keep u hu a av ua
  have f := keep a av z zv az
  refine ⟨?_,fun back => free u 3 (by decide) le_rfl (.step av e (.step zv f (.step hu back (.refl u)))),?_⟩
  · rintro rfl
    exact digonfree free (by decide) zv av e f
  · by_cases uz : G u z=true
    · exact Or.inl (mem_sdiff.mpr ⟨mem_outN.mpr ⟨zv,uz⟩,old⟩)
    · exact Or.inr uz

#print axioms descent_or_assign
#print axioms destination_ancestry

/-- At minimum strict weight mass the first branch is excluded on this
very carrier. At least one root attains the required minimum score. -/
theorem minimal_transport {q D V b} {X : Witness q D V b} (least : X.Minimal)
    (hq : 1 ≤ q) (free : QFree D X.carrier q) :
    ∃ u ∈ X.carrier, (outN D X.carrier u).Nonempty ∧
      ∀ pin ∈ outN D X.carrier u, Assigned q D X.carrier X.weights u pin := by
  classical
  obtain ⟨u,hu,low⟩ := X.carrier.exists_min_image (score q D X.carrier X.weights) X.nonempty
  have live : (outN D X.carrier u).Nonempty := by
    by_contra! empty
    have zero := nat_strict.mp X.strict u hu
    rw [score_out,empty,sum_empty,Nat.mul_zero,Nat.add_zero] at zero
    exact zero.not_ge (single_le_sum (f := X.weights) (by intros; omega) hu)
  refine ⟨u,hu,live,?_⟩
  rcases descent_or_assign hq (fun a ha => low a (outN_subset ha)) with ⟨S,sub,ne,strict⟩ | pay
  · have sc := sub.trans (outN_subset : outN D X.carrier u ⊆ X.carrier)
    have outside : u ∈ X.carrier \ S := mem_sdiff.mpr ⟨hu,fun h =>
      loopfree free hq hu (mem_outN.mp (sub h)).2⟩
    have diff := single_le_sum (f := X.weights) (by intros; omega) outside
    have pos := X.positive u hu
    have total := sum_sdiff (f := X.weights) sc
    obtain ⟨a,ha,small⟩ := light_after_edit least (sc.trans X.subset) ne X.weights
      (fun z hz => X.positive z (sc hz)) (by omega)
    exact ((nat_strict.mp strict a ha).not_ge small).elim
  · exact pay

/-- The no-sink root from the first audit is also a transport root in a
regular ordinary source. The alternative gives literal smaller bad data. -/
theorem cyclic_source_fork {D V s} (free : QFree D V 3) (ne : V.Nonempty)
    (order : V.card ≤ 3*s) (reg : OutEq s D V) :
    ∃ u ∈ V, (∀ a ∈ outN D V u, ∃ z ∈ outN D V a, z ∈ outN D V u) ∧
      ((∃ S ⊆ outN D V u, S.Nonempty ∧ S.card < V.card ∧
        ∃ d, 0 < d ∧ S.card ≤ 3*d ∧ QFree D S 3 ∧ ∀ a ∈ S, d ≤ (outN D S a).card) ∨
        ((∀ T ⊆ outN D V u, T.Nonempty → ¬Strict 3 D T (fun _ => 1)) ∧
        ∀ pin ∈ outN D V u, Assigned 3 D V (fun _ => 1) u pin)) := by
  obtain ⟨u,hu,inner⟩ := HalfRows.source_cyclic_neighbourhood free ne order (fun a ha => (reg a ha).ge)
  refine ⟨u,hu,inner,?_⟩
  have same (a) (ha : a ∈ outN D V u) :
      score 3 D V (fun _ => 1) u ≤ score 3 D V (fun _ => 1) a := by
    simp [score_out,reg u hu,reg a (outN_subset ha)]
  by_cases small : ∃ S ⊆ outN D V u, S.Nonempty ∧ Strict 3 D S (fun _ => 1)
  · obtain ⟨S,sub,nonempty,strict⟩ := small
    have sc := sub.trans (outN_subset : outN D V u ⊆ V)
    have smaller := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sc,fun eq =>
      loopfree free (by decide) hu (mem_outN.mp (sub (eq.symm ▸ hu))).2⟩)
    obtain ⟨a,ha,least⟩ := S.exists_min_image (fun z => (outN D S z).card) nonempty
    have lo := nat_strict.mp strict a ha
    simp [score_out] at lo
    have := nonempty.card_pos
    exact Or.inl ⟨S,sub,nonempty,smaller,_,by omega,by omega,free.mono_set sc,least⟩
  · exact Or.inr ⟨fun T sub ne strict => small ⟨T,sub,ne,strict⟩,
      (descent_or_assign (by decide : 1 ≤ 3) same).resolve_left small⟩

#print axioms minimal_transport
#print axioms cyclic_source_fork

def exterior (D : CH.Digraph) (V O S : Finset ℕ) := (O \ S) ∪ exits D V O S

/-- A single physical rectangle for all rows of S. Each extra internal
head corresponds in the count to one omitted exterior label in this row. -/
theorem row_defect {D V u s S k} (hu : u ∈ V) (reg : OutEq s D V)
    (sub : S ⊆ outN D V u) (deficit : (exits D V (outN D V u) S).card+k=S.card)
    {a} (ha : a ∈ S) :
    (outN D S a).card = k + (exterior D V (outN D V u) S \ outN D V a).card := by
  let O := outN D V u
  let E := exterior D V O S
  have apart {z} (hz : z ∈ exits D V O S) : z ∉ O := by
    obtain ⟨b,_,edge⟩ := mem_biUnion.mp hz
    exact (mem_sdiff.mp (mem_outN.mp edge).1).2
  have dis : Disjoint (O \ S) (exits D V O S) :=
    disjoint_left.mpr (fun _ h e => apart e (mem_sdiff.mp h).1)
  have ec : E.card = (O \ S).card + (exits D V O S).card := card_union_of_disjoint dis
  have os := card_sdiff_add_card_eq_card sub
  have inner : Disjoint (outN D S a) E := by
    apply disjoint_left.mpr
    intro z zS zE
    rcases mem_union.mp zE with diff | out
    · exact (mem_sdiff.mp diff).2 (outN_subset zS)
    · exact apart out (sub (outN_subset zS))
  have eq : outN D V a ∪ (E \ outN D V a) = outN D S a ∪ E := by
    ext z
    by_cases e : z ∈ E
    · simp [e]
    · simp only [mem_union,mem_sdiff,e,false_and,or_false]
      constructor
      · intro h
        by_cases zs : z ∈ S
        · exact mem_outN.mpr ⟨zs,(mem_outN.mp h).2⟩
        exfalso
        apply e
        by_cases zo : z ∈ O
        · exact mem_union_left _ (mem_sdiff.mpr ⟨zo,zs⟩)
        · exact mem_union_right _ (mem_biUnion.mpr ⟨a,ha,mem_outN.mpr
            ⟨mem_sdiff.mpr ⟨outN_subset h,zo⟩,(mem_outN.mp h).2⟩⟩)
      · intro h
        exact mem_outN.mpr ⟨outN_subset (sub (outN_subset h)),(mem_outN.mp h).2⟩
  have h := congrArg card eq
  rw [card_union_of_disjoint (disjoint_left.mpr (fun _ hin hex => (mem_sdiff.mp hex).2 hin)),
    card_union_of_disjoint inner,reg a (outN_subset (sub ha))] at h
  have oc : O.card=s := reg u hu
  change (O \ S).card + S.card = O.card at os
  change (exits D V O S).card+k=S.card at deficit
  change _ = k + (E \ outN D V a).card
  omega

/-- On the second slack level the audit's half-row theorem supplies a
complete rectangle into a common set of exterior labels. -/
theorem half_rectangle_of_sinks {D V u s S k} (free : QFree D V 3) (hu : u ∈ V)
    (reg : OutEq s D V) (sub : S ⊆ outN D V u)
    (deficit : (exits D V (outN D V u) S).card+k=S.card)
    (second : S.card=3*k+2) (sinks : HalfRows.HasSinks D S) :
    S.card ≤ 2*(S.filter (fun a => exterior D V (outN D V u) S ⊆ outN D V a)).card := by
  have row (a) (ha : a ∈ S) := row_defect hu reg sub deficit ha
  have h := HalfRows.half_of_sinks (free.mono_set (sub.trans outN_subset)) second
    (fun a ha => by have := row a ha; omega) sinks
  convert h using 2
  congr 1
  apply filter_congr
  intro a ha
  have := row a ha
  rw [←sdiff_eq_empty_iff_subset,←card_eq_zero]
  omega

#print axioms row_defect
#print axioms half_rectangle_of_sinks

/-- Repeatedly take the smaller ordinary host when necessary. The result
is an actual subgraph on original labels with a cyclic transport root.
The degree parameter is allowed to change on descent. -/
theorem triangle_source_supplies {D V s} (free : QFree D V 3) (ne : V.Nonempty)
    (order : V.card ≤ 3*s) (degree : ∀ a ∈ V, s ≤ (outN D V a).card) :
    ∃ (F : CH.Digraph) (W : Finset ℕ) (d : ℕ), W ⊆ V ∧
      (∀ a b, F a b = true → D a b = true) ∧ W.Nonempty ∧ W.card ≤ 3*d ∧
      QFree F W 3 ∧ OutEq d F W ∧
      ∃ u ∈ W, (outN F W u).Nonempty ∧
        (∀ a ∈ outN F W u, ∃ z ∈ outN F W a, z ∈ outN F W u) ∧
        (∀ T ⊆ outN F W u, T.Nonempty → ¬Strict 3 F T (fun _ => 1)) ∧
        ∀ pin ∈ outN F W u, Assigned 3 F W (fun _ => 1) u pin := by
  obtain ⟨H,sub,reg⟩ := exists_outEq degree
  have hf := qfree_sub sub free
  obtain ⟨u,hu,inner,branch⟩ := cyclic_source_fork hf ne order reg
  rcases branch with ⟨S,sc,live,smaller,d,_,bound,sf,low⟩ | assigned
  · obtain ⟨F,W,e,ws,keep,rest⟩ := triangle_source_supplies sf live bound low
    exact ⟨F,W,e,ws.trans (sc.trans outN_subset),fun a b arc => sub a b (keep a b arc),rest⟩
  · have pos := ne.card_pos
    have eq := reg u hu
    exact ⟨H,V,s,Finset.Subset.rfl,sub,ne,order,hf,reg,u,hu,card_pos.mp (by omega),inner,assigned⟩
termination_by V.card

#print axioms triangle_source_supplies

private theorem counted_cover {D V U Y} {q s l : ℕ} (hq : 1 ≤ q)
    (reg : OutEq s D V) (uv : U ⊆ V) (_ne : U.Nonempty)
    (low : ¬Strict q D U (fun _ => 1))
    (masks : ∀ a ∈ U, ∃ P : Finset ℕ, U ⊆ P ∧ P.card=l ∧ outN D V a ⊆ P ∪ Y) :
    q*s + (q-1)*U.card+1 ≤ q*l + q*Y.card := by
  rw [nat_strict] at low
  push Not at low
  obtain ⟨a,ha,light⟩ := low
  simp [score_out] at light
  obtain ⟨P,up,size,cover⟩ := masks a ha
  have split : outN D V a ⊆ (outN D U a ∪ (P \ U)) ∪ Y := by
    intro z hz
    rcases mem_union.mp (cover hz) with zp | zy
    · apply mem_union_left
      by_cases zu : z ∈ U
      · exact mem_union_left _ (mem_outN.mpr ⟨zu,(mem_outN.mp hz).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨zp,zu⟩)
    · exact mem_union_right _ zy
  have upper := (card_le_card split).trans (card_union_le _ _)
  have upper' := card_union_le (outN D U a) (P \ U)
  rw [reg a (uv ha)] at upper
  have bound := Nat.mul_le_mul_left q (show s ≤ (outN D U a).card+(P \ U).card+Y.card by omega)
  have partition := congrArg (q * ·) (card_sdiff_add_card_eq_card up)
  have pred := congrArg (· * U.card) (show q-1+1=q by omega)
  simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,size] at bound partition pred
  omega

/-- Joint Hall inequalities for two colours on the common heads. Y is a
union of actual permitted destinations; a destination label is counted once.
Failure of the light-row premise on a nonempty subbank is a smaller strict host. -/
theorem two_root_cut {D V q s u v} (hq : 1 ≤ q) (reg : OutEq s D V) (hu : u∈V) (hv : v∈V)
    (light : ∀ T ⊆ outN D V u ∩ outN D V v, T.Nonempty → ¬Strict q D T (fun _ => 1))
    (room : (q-1)*(outN D V u ∩ outN D V v).card + q*(outN D V u ∩ outN D V v).card ≤ q*s)
    {A B : Finset ℕ} (aa : A ⊆ outN D V u ∩ outN D V v) (bb : B ⊆ outN D V u ∩ outN D V v)
    (ne : (A ∪ B).Nonempty) :
    (q-1)*(A.card+B.card)+1 ≤ q*(exits D V (outN D V u) A ∪ exits D V (outN D V v) B).card := by
  let K := outN D V u ∩ outN D V v
  let Y := exits D V (outN D V u) A ∪ exits D V (outN D V v) B
  have uk : A ∪ B ⊆ K := union_subset aa bb
  have kv : K ⊆ V := inter_subset_left.trans outN_subset
  have coverA (a) (ha : a∈A) : outN D V a ⊆ outN D V u ∪ Y := by
    intro z hz
    by_cases h : z ∈ outN D V u
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_union_left _ (mem_biUnion.mpr
        ⟨a,ha,mem_outN.mpr ⟨mem_sdiff.mpr ⟨outN_subset hz,h⟩,(mem_outN.mp hz).2⟩⟩))
  have coverB (a) (ha : a∈B) : outN D V a ⊆ outN D V v ∪ Y := by
    intro z hz
    by_cases h : z ∈ outN D V v
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_union_right _ (mem_biUnion.mpr
        ⟨a,ha,mem_outN.mpr ⟨mem_sdiff.mpr ⟨outN_subset hz,h⟩,(mem_outN.mp hz).2⟩⟩))
  have size := congrArg ((q-1) * ·) (card_union_add_card_inter A B)
  simp only [Nat.mul_add] at size
  change _ ≤ q*Y.card
  rw [Nat.mul_add]
  by_cases overlap : (A ∩ B).Nonempty
  · have ik : A ∩ B ⊆ K := inter_subset_left.trans aa
    have cap := counted_cover (Y:=Y) (l:=K.card) hq reg (ik.trans kv) overlap
      (light _ ik overlap) (fun a ha => by
        refine ⟨K,ik,rfl,?_⟩
        intro z hz
        rcases mem_union.mp (coverA a (mem_inter.mp ha).1 hz) with zu | zy
        · rcases mem_union.mp (coverB a (mem_inter.mp ha).2 hz) with zv | zy
          · exact mem_union_left _ (mem_inter.mpr ⟨zu,zv⟩)
          · exact mem_union_right _ zy
        · exact mem_union_right _ zy)
    have small := Nat.mul_le_mul_left (q-1) (card_le_card uk)
    change (q-1)*K.card + q*K.card ≤ q*s at room
    omega
  · have cap := counted_cover (Y:=Y) (l:=s) hq reg (uk.trans kv) ne (light _ uk ne)
      (fun a ha => by
        rcases mem_union.mp ha with ha | ha
        · exact ⟨_,uk.trans inter_subset_left,reg u hu,coverA a ha⟩
        · exact ⟨_,uk.trans inter_subset_right,reg v hv,coverB a ha⟩)
    rw [not_nonempty_iff_eq_empty.mp overlap,card_empty,Nat.mul_zero,Nat.add_zero] at size
    omega

#print axioms two_root_cut

/-- At the cyclic root of the terminal ordinary host a suitable adjacent
second root actually exists, and the common bank is nonempty. -/
theorem supplied_pair {D V s u} (reg : OutEq s D V) (hu : u ∈ V)
    (ne : (outN D V u).Nonempty)
    (inner : ∀ a ∈ outN D V u, ∃ z ∈ outN D V a, z ∈ outN D V u)
    (light : ∀ S ⊆ outN D V u, S.Nonempty → ¬Strict 3 D S (fun _ => 1)) :
    ∃ v ∈ outN D V u, let K := outN D V u ∩ outN D V v
      K.Nonempty ∧ 3*K.card+1 ≤ s ∧ ∀ A ⊆ K, ∀ B ⊆ K, (A ∪ B).Nonempty →
      2*(A.card+B.card)+1 ≤ 3*(exits D V (outN D V u) A ∪ exits D V (outN D V v) B).card := by
  have low := light _ Finset.Subset.rfl ne
  rw [nat_strict] at low
  push Not at low
  obtain ⟨v,hv,atv⟩ := low
  have eq : outN D (outN D V u) v = outN D V u ∩ outN D V v := by
    ext z
    simp only [mem_outN,mem_inter]
    grind
  simp [score_out,eq,reg u hu] at atv
  obtain ⟨z,zv,zu⟩ := inner v hv
  refine ⟨v,hv,⟨z,mem_inter.mpr ⟨zu,zv⟩⟩,by omega,?_⟩
  intro A aa B bb nonempty
  exact two_root_cut (by decide : 1 ≤ 3) reg hu (outN_subset hv)
    (fun S sub h => light S (sub.trans inter_subset_left) h) (by omega) aa bb nonempty

#print axioms supplied_pair

def colouredHeads (D : CH.Digraph) (V : Finset ℕ) (u v : ℕ) (i : ℕ ⊕ ℕ) : Finset ℕ :=
  i.elim (outN D (V \ outN D V u)) (outN D (V \ outN D V v))

def JointAssignment (D : CH.Digraph) (V : Finset ℕ) (u v : ℕ) : Prop :=
  let K := outN D V u ∩ outN D V v
  ∀ pin : ℕ ⊕ ℕ, ∃ f : (units (K.disjSum K) (fun a => 2 + if a=pin then 1 else 0)) → (Σ _ : ℕ, ℕ),
    Function.Injective f ∧ ∀ i, (f i).1 ∈ colouredHeads D V u v i.val.1 ∧ (f i).2 < 3

theorem joint_of_cuts {D V u v}
    (cut : ∀ A ⊆ outN D V u ∩ outN D V v, ∀ B ⊆ outN D V u ∩ outN D V v, (A ∪ B).Nonempty →
      2*(A.card+B.card)+1 ≤ 3*(exits D V (outN D V u) A ∪ exits D V (outN D V v) B).card) : JointAssignment D V u v := by
  intro pin
  apply realize_cuts (cap := fun _ => 3)
  intro T sub
  by_cases empty : T = ∅
  · simp [empty]
  have left := Finset.toLeft_subset_toLeft sub
  have right := Finset.toRight_subset_toRight sub
  simp only [toLeft_disjSum,toRight_disjSum] at left right
  have ne : (T.toLeft ∪ T.toRight).Nonempty := by
    obtain ⟨a,ha⟩ := nonempty_iff_ne_empty.mpr empty
    cases a with
    | inl a => exact ⟨a,mem_union_left _ (mem_toLeft.mpr ha)⟩
    | inr a => exact ⟨a,mem_union_right _ (mem_toRight.mpr ha)⟩
  have targets : T.biUnion (colouredHeads D V u v) =
      exits D V (outN D V u) T.toLeft ∪ exits D V (outN D V v) T.toRight := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha,e⟩ := mem_biUnion.mp hz
      cases a with
      | inl a => exact mem_union_left _ (mem_biUnion.mpr ⟨a,mem_toLeft.mpr ha,e⟩)
      | inr a => exact mem_union_right _ (mem_biUnion.mpr ⟨a,mem_toRight.mpr ha,e⟩)
    · intro hz
      rcases mem_union.mp hz with l | r
      · obtain ⟨a,ha,e⟩ := mem_biUnion.mp l
        exact mem_biUnion.mpr ⟨Sum.inl a,mem_toLeft.mp ha,e⟩
      · obtain ⟨a,ha,e⟩ := mem_biUnion.mp r
        exact mem_biUnion.mpr ⟨Sum.inr a,mem_toRight.mp ha,e⟩
  have bound := cut _ left _ right ne
  rw [card_toLeft_add_card_toRight] at bound
  simp [sum_add_distrib,targets] 
  split_ifs <;> omega

#print axioms joint_of_cuts

/-- Both colours draw from the same three copies of each label. The graph,
the adjacent roots and the nonempty common bank are all source-supplied. -/
theorem triangle_joint_transport {D V s} (free : QFree D V 3) (ne : V.Nonempty)
    (order : V.card ≤ 3*s) (degree : ∀ a ∈ V, s ≤ (outN D V a).card) :
    ∃ (F : CH.Digraph) (W : Finset ℕ) (d : ℕ), W ⊆ V ∧
      (∀ a b, F a b = true → D a b = true) ∧ W.Nonempty ∧ W.card ≤ 3*d ∧
      QFree F W 3 ∧ OutEq d F W ∧ ∃ u ∈ W, ∃ v ∈ outN F W u,
      (∀ a ∈ outN F W u, ∃ z ∈ outN F W a, z ∈ outN F W u) ∧
      (outN F W u ∩ outN F W v).Nonempty ∧ 3*(outN F W u ∩ outN F W v).card+1 ≤ d ∧
      JointAssignment F W u v := by
  obtain ⟨F,W,d,sub,keep,live,size,hf,reg,u,hu,heads,inner,light,_⟩ :=
    triangle_source_supplies free ne order degree
  obtain ⟨v,hv,nonempty,bound,cuts⟩ := supplied_pair reg hu heads inner light
  exact ⟨F,W,d,sub,keep,live,size,hf,reg,u,hu,v,hv,inner,nonempty,bound,joint_of_cuts cuts⟩

#print axioms triangle_joint_transport

/-- Choose the order across all positive degrees first. On this one graph
both fixed-degree leastness (for the cycle rules) and local strict-subbank
exclusion (for the joint matching) are available. -/
theorem common_source_terminal {D V s} (free : QFree D V 3) (ne : V.Nonempty)
    (order : V.card ≤ 3*s) (degree : ∀ a ∈ V, s ≤ (outN D V a).card) :
    ∃ d, ∃ X : ShenMinimumOrder.Source 3 d, X.V.card ≤ V.card ∧ X.V.card ≤ 3*d ∧
      OutEq d X.D X.V ∧ ShenRootedKernel.Terminal 3 X.D X.V d ∧ ∃ u ∈ X.V, ∃ v ∈ outN X.D X.V u,
      (∀ a ∈ outN X.D X.V u, ∃ z ∈ outN X.D X.V a, z ∈ outN X.D X.V u) ∧
      (outN X.D X.V u ∩ outN X.D X.V v).Nonempty ∧
      3*(outN X.D X.V u ∩ outN X.D X.V v).card+1 ≤ d ∧ JointAssignment X.D X.V u v ∧
      ∃ N, ShenCycleSuccessor.Via X u N ∧ (v ∈ N ∨
        (v ∉ N ∧ 2 ≤ (ShenKernelHead.parents X.D N v).card ∧
          ∃ K, ShenCycleSuccessor.Via X v K ∧ v ∈ K)) := by
  classical
  let Bad (m : ℕ) := ∃ (F : CH.Digraph) (W : Finset ℕ) (t : ℕ), W.card=m ∧ W.Nonempty ∧
    QFree F W 3 ∧ W.card ≤ 3*t ∧ ∀ a ∈ W, t ≤ (outN F W a).card
  have input : Bad V.card := ⟨D,V,s,rfl,ne,free,order,degree⟩
  have ex : ∃ m, Bad m := ⟨_,input⟩
  obtain ⟨G,W,d,size,live,gfree,bound,deg⟩ := Nat.find_spec ex
  have small (m) (h : Bad m) : W.card ≤ m := size.trans_le (Nat.find_min' ex h)
  obtain ⟨F,sub,reg⟩ := exists_outEq deg
  have hf := qfree_sub sub gfree
  have least : DeleteRepair.Least 3 d W := by
    intro E U sf mind nonempty
    by_contra! tooSmall
    have hit := small U.card ⟨E,U,d,rfl,nonempty,sf,by omega,mind⟩
    omega
  let X : ShenMinimumOrder.Source 3 d := ⟨F,W,live,hf,fun a ha => (reg a ha).ge,least⟩
  obtain ⟨u,hu,inner⟩ := HalfRows.source_cyclic_neighbourhood hf live bound (fun a ha => (reg a ha).ge)
  have hd := live.card_pos
  have ds : 0<d := by omega
  have heads : (outN F W u).Nonempty := card_pos.mp ((reg u hu).symm ▸ ds)
  have lower (S) (sc : S ⊆ outN F W u) (neS : S.Nonempty) : ¬Strict 3 F S (fun _ => 1) := by
    intro strict
    have sw := sc.trans (outN_subset : outN F W u ⊆ W)
    have smaller := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sw,fun eq =>
      loopfree hf (by decide) hu (mem_outN.mp (sc (eq.symm ▸ hu))).2⟩)
    obtain ⟨a,ha,minimum⟩ := S.exists_min_image (fun t => (outN F S t).card) neS
    have lo := nat_strict.mp strict a ha
    simp [score_out] at lo
    have hit := small S.card ⟨F,S,_,rfl,neS,hf.mono_set sw,by omega,minimum⟩
    omega
  obtain ⟨v,hv,bank,cap,cuts⟩ := supplied_pair reg hu heads inner lower
  have term : ShenRootedKernel.Terminal 3 F W d :=
    ⟨⟨live,bound,fun a ha => (reg a ha).ge⟩,fun S sub e cand =>
      small _ ⟨F,S,e,rfl,cand.nonempty,hf.mono_set sub,cand.order,cand.degree⟩⟩
  exact ⟨d,X,small _ input,bound,reg,term,u,hu,v,hv,inner,bank,cap,joint_of_cuts cuts,
    ShenCycleSuccessor.cover_head_in_two X (by decide) ds hu hv⟩

theorem common_source {D V s} (free : QFree D V 3) (ne : V.Nonempty)
    (order : V.card ≤ 3*s) (degree : ∀ a ∈ V, s ≤ (outN D V a).card) :
    ∃ d, ∃ X : ShenMinimumOrder.Source 3 d, X.V.card ≤ V.card ∧ X.V.card ≤ 3*d ∧
      OutEq d X.D X.V ∧ ∃ u ∈ X.V, ∃ v ∈ outN X.D X.V u,
      (∀ a ∈ outN X.D X.V u, ∃ z ∈ outN X.D X.V a, z ∈ outN X.D X.V u) ∧
      (outN X.D X.V u ∩ outN X.D X.V v).Nonempty ∧
      3*(outN X.D X.V u ∩ outN X.D X.V v).card+1 ≤ d ∧ JointAssignment X.D X.V u v ∧
      ∃ N, ShenCycleSuccessor.Via X u N ∧ (v ∈ N ∨
        (v ∉ N ∧ 2 ≤ (ShenKernelHead.parents X.D N v).card ∧
          ∃ K, ShenCycleSuccessor.Via X v K ∧ v ∈ K)) := by
  obtain ⟨d,X,small,bound,reg,_,more⟩ := common_source_terminal free ne order degree
  exact ⟨d,X,small,bound,reg,more⟩

#print axioms common_source_terminal
#print axioms common_source
end LeanCH.BR.ShenSecondNeighbour
