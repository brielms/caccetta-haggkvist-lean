import checkpoints.shen_extension.LayeredPathCertificate
import checkpoints.shen_extension.MandatoryTwoStep

namespace LeanCH.BR.Closure.ShortestReturnCertificate
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights RootedSplice MandatoryTwoStep
open LayeredPathCertificate

private abbrev ReturnPath (D : CH.Digraph) (V : Finset ℕ) (q t : ℕ) (p : ℕ → ℕ) :=
  LayeredPathCertificate.Valid (fun _ u v => v ∈ V ∧ D u v = true) (q+1) t t p

private def carrier (q : ℕ) (p : ℕ → ℕ) := (range (q+1)).image p

private theorem cycle_path {D V q t C} (hq : 1 ≤ q) (free : QFree D V q)
    (c : Cycle D V q C) (tc : t ∈ C) :
    ∃ p, ReturnPath D V q t p ∧ ∀ i < q+1, p i ∈ C := by
  have heads (x) (xc : x ∈ C) : ∃ y ∈ C, D x y = true := by
    obtain ⟨y,hy⟩ := card_pos.mp (show 0 < (outN D C x).card by rw [c.heads x xc]; decide)
    exact ⟨y,mem_outN.mp hy⟩
  obtain ⟨y,yc,ty⟩ := heads t tc
  have ne : t ≠ y := by rintro rfl; exact loopfree free hq (c.sub tc) ty
  obtain ⟨k,_,bound,forward,back⟩ := WeightedSD.tight_cycle_complementary_walks
    (free.mono_set c.sub) c.size heads tc yc ne
  have w : Walk D C t t (q+1) := by
    simpa only [show k+(q+1-k)=q+1 by omega] using forward.append back
  obtain ⟨p,start,finish,edge⟩ := w.toFun
  refine ⟨p,⟨start,finish,fun i hi => ⟨c.sub (edge i hi).1,(edge i hi).2⟩⟩,?_⟩
  intro i hi
  cases i with
  | zero => simpa only [start] using tc
  | succ i => exact (edge i (by omega)).1

private theorem carrier_cycle {D V q t p} (hq : 1 ≤ q) (free : QFree D V q)
    (tv : t ∈ V) (hp : ReturnPath D V q t p) : Cycle D V q (carrier q p) ∧ t ∈ carrier q p := by
  let M := carrier q p
  have inside (i) (hi : i < q+1) : p i ∈ M := mem_image.mpr ⟨i,mem_range.mpr hi,rfl⟩
  have tM : t ∈ M := hp.1 ▸ inside 0 (by omega)
  have sub : M ⊆ V := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    have bound := mem_range.mp hi
    cases i with
    | zero => simpa only [hp.1] using tv
    | succ i => exact (hp.2.2 i (by omega)).1
  have step (i) (hi : i < q+1) : p (i+1) ∈ M ∧ D (p i) (p (i+1)) = true := by
    refine ⟨?_,(hp.2.2 i hi).2⟩
    by_cases last : i=q
    · simpa only [last,hp.2.1] using tM
    · exact inside _ (by omega)
  have closed : Walk D M t t (q+1) := by simpa only [hp.1,hp.2.1] using walk_of_edges step
  obtain ⟨K,KM,size,deg⟩ := boundary_closed_walk_support (free.mono_set sub) closed
  have room : M.card ≤ q+1 := (card_image_le.trans (card_range _).le)
  obtain rfl : K=M := eq_of_subset_of_card_le KM (size ▸ room)
  have reg := dt_reg hq (ball_q_one q hq) (free.mono_set sub) deg (by simpa using size)
  exact ⟨⟨sub,size,reg.1,reg.2⟩,tM⟩

private theorem no_earlier {D V q t p r i j} (free : QFree D V q)
    (hp : ReturnPath D V q t p) (hr : ReturnPath D V q t r)
    (ij : i<j) (jl : j<q+1) (same : p i = r j) : False := by
  have pre := walk_between hp.2.2 (Nat.zero_le i) (show i ≤ q+1 by omega)
  have post := walk_between hr.2.2 (show j ≤ q+1 by omega) le_rfl
  rw [hp.1,same] at pre
  rw [hr.2.1] at post
  exact free t ((i-0)+(q+1-j)) (by omega) (by omega) (pre.append post)

/-- Two fixed shortest cycles identify every vertex forced by a named receiver. -/
theorem two_cycles {D V q t} (hq : 1 ≤ q) (free : QFree D V q)
    (seed : ∃ C, Cycle D V q C ∧ t ∈ C) :
    ∃ A B, Cycle D V q A ∧ t ∈ A ∧ Cycle D V q B ∧ t ∈ B ∧
      ∀ h ∈ A ∩ B, Forces D V q t h := by
  obtain ⟨C,c,tc⟩ := seed
  obtain ⟨p,hp,_⟩ := cycle_path hq free c tc
  obtain ⟨a,b,ha,hb,agree⟩ := two_paths ⟨p,hp⟩
  obtain ⟨ca,ta⟩ := carrier_cycle hq free (c.sub tc) ha
  obtain ⟨cb,tb⟩ := carrier_cycle hq free (c.sub tc) hb
  refine ⟨_,_,ca,ta,cb,tb,?_⟩
  intro x hx K ck tk
  obtain ⟨i,hi,ai⟩ := mem_image.mp (mem_inter.mp hx).1
  obtain ⟨j,hj,bj⟩ := mem_image.mp (mem_inter.mp hx).2
  have il := mem_range.mp hi
  have jl := mem_range.mp hj
  have same := ai.trans bj.symm
  obtain rfl : i=j := by
    rcases lt_trichotomy i j with h|e|h
    · exact (no_earlier free ha hb h jl same).elim
    · exact e
    · exact (no_earlier free hb ha h il same.symm).elim
  obtain ⟨r,hr,allK⟩ := cycle_path hq free ck tk
  exact ((agree i il.le same r hr).trans ai) ▸ allK i il

theorem detects_every_deletion {D V q t A B}
    (a : Cycle D V q A) (ta : t ∈ A)
    (b : Cycle D V q B) (tb : t ∈ B)
    (common : ∀ h ∈ A ∩ B, Forces D V q t h) (h : ℕ) :
    Covered D V q h t ↔ h ∉ A ∨ h ∉ B := by
  classical
  constructor
  · intro good
    by_contra! stuck
    exact (forces_iff.mp (common h (mem_inter.mpr stuck))) good
  · rintro (ha | hb)
    · by_contra absent
      exact ha (forces_iff.mpr absent A a ta)
    · by_contra absent
      exact hb (forces_iff.mpr absent B b tb)

theorem cheaper_cycle {A B M U : Finset ℕ} (c : ℕ → ℕ)
    (common : A ∩ B = M) (aU : A ⊆ U) (bU : B ⊆ U) :
    2 * min (∑ x ∈ A \ M, c x) (∑ x ∈ B \ M, c x) ≤ ∑ x ∈ U \ M, c x := by
  classical
  have disj : Disjoint (A \ M) (B \ M) := by
    apply disjoint_left.mpr
    intro x xa xb
    exact (mem_sdiff.mp xa).2 (common ▸ mem_inter.mpr ⟨(mem_sdiff.mp xa).1, (mem_sdiff.mp xb).1⟩)
  have sub : (A \ M) ∪ (B \ M) ⊆ U \ M :=
    union_subset (fun _ hx => mem_sdiff.mpr ⟨aU (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩)
      (fun _ hx => mem_sdiff.mpr ⟨bU (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩)
  have total := sum_le_sum_of_subset_of_nonneg (f := c) sub (by intros; omega)
  rw [sum_union disj] at total
  omega


/-- One pair answers all single-label punctures at once. -/
theorem all_punctures {D V q t} (hq : 1 ≤ q) (free : QFree D V q) (seed : ∃ C, Cycle D V q C ∧ t ∈ C) :
    ∃ A B, Cycle D V q A ∧ t ∈ A ∧ Cycle D V q B ∧ t ∈ B ∧
      ∀ h, Covered D V q h t ↔ h ∉ A ∨ h ∉ B := by
  obtain ⟨A,B,a,ta,b,tb,common⟩ := two_cycles hq free seed
  exact ⟨A,B,a,ta,b,tb,detects_every_deletion a ta b tb common⟩

/-- Keep the model and receiver supplied by the caller. -/
theorem on_model {q budget} (X : Model q budget) (hq : 2 ≤ q) {t} (tv : t ∈ X.V) :
    ∃ A B, Cycle X.D X.V q A ∧ t ∈ A ∧ Cycle X.D X.V q B ∧ t ∈ B ∧
      ∀ h, Covered X.D X.V q h t ↔ h ∉ A ∨ h ∉ B := by
  have head : ∃ y ∈ X.V, X.D t y = true := by
    by_contra none
    have small := ShenPrimeTransition.nat_strict.mp X.strict t tv
    have total := sum_erase_add X.V X.weights tv
    have zero : (∑ y ∈ X.V, if X.D t y = true then X.weights y else 0) = 0 :=
      sum_eq_zero fun y yv => ite_eq_right (fun edge => none ⟨y,yv,edge⟩)
    simp only [ShenPrimeTransition.score,zero,Nat.mul_zero,Nat.add_zero] at small
    omega
  obtain ⟨y,yv,ty⟩ := head
  obtain ⟨C,c,tc,_⟩ := edge_cycle X hq tv yv ty
  exact all_punctures (by omega) X.free ⟨C,c,tc⟩

/-- From arbitrary CH input, pick one normalized model and, for each receiver,
pick its two cycles before the label to delete is supplied. -/
theorem from_input {n r q D} (hn : 0 < n) (hq : 2 ≤ q) (order : n ≤ q*r)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (no : ¬CH.HasDirectedCycleAtMost D n q) :
    ∃ X : Model q n, ∀ t ∈ X.V, ∃ A B,
      Cycle X.D X.V q A ∧ t ∈ A ∧ Cycle X.D X.V q B ∧ t ∈ B ∧
      ∀ h, Covered X.D X.V q h t ↔ h ∉ A ∨ h ∉ B := by
  obtain ⟨X⟩ := normalize hq hn order loop degree no
  exact ⟨X,fun _ tv => on_model X hq tv⟩

#print axioms LayeredPathCertificate.two_paths
#print axioms on_model
#print axioms from_input
#print axioms two_cycles
#print axioms all_punctures
#print axioms cheaper_cycle
end LeanCH.BR.Closure.ShortestReturnCertificate
