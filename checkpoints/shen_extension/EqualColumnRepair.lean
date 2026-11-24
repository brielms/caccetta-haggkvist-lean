import checkpoints.shen_extension.LightColumnPacking

namespace LeanCH.BR.Closure.EqualColumnRepair
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights
open MandatoryTwoStep RootedSplice DeleteRepair

/-- An outside parent whose original margin is no larger than the loss from
deleting K. The definition retains the actual parent and its unique class head. -/
def Blocks {q n} (X : Model q n) (K : Finset ℕ) (p x : ℕ) : Prop :=
  p∈X.V\K ∧ x∈K ∧ outN X.D K p={x} ∧
    score q X.D X.V X.weights p + (∑z∈K,X.weights z) ≤ (∑z∈X.V,X.weights z)+q*X.weights x

/-- Read the original weighted obstruction from any jointly safe collection
of bypass rectangles. The same comparison applies to single and multiple pivots. -/
theorem gift_loss {q n} (X : Model q n) (hq : 2≤q) {K : Finset ℕ} {E : CH.Digraph}
    (sub : K⊆X.V) (live : K.Nonempty) (proper : K≠X.V)
    (chain : ∀u∈K,∀v∈K,Forces X.D X.V q u v ∨ Forces X.D X.V q v u)
    (safeE : QFree E (X.V\K) q)
    (preserve : ∀p∈X.V\K,∀z∈X.V\K,X.D p z=true → E p z=true)
    (gifts : ℕ→Finset ℕ)
    (fresh : ∀p x,Blocks X K p x → ∀z∈gifts x,z∈X.V\K ∧ E p z=true ∧ X.D p z=false) :
    ∃p x, Blocks X K p x ∧
      score q X.D X.V X.weights p + (∑z∈K,X.weights z) + q*(∑z∈gifts x,X.weights z)
        ≤ (∑z∈X.V,X.weights z)+q*X.weights x := by
  classical
  let U := X.V\K
  have uv : U⊆X.V := sdiff_subset
  have ulive : U.Nonempty := sdiff_nonempty.mpr (fun back => proper (Subset.antisymm sub back))
  have less : U.card<X.V.card := by
    have count := card_sdiff_add_card_eq_card sub
    have pos := card_pos.mpr live
    dsimp [U]; omega
  have fail : ¬Strict q E U X.weights := fun strict => less.not_ge
    (X.minimal E U X.weights ulive safeE (fun z zu => X.positive z (uv zu))
      ((sum_le_sum_of_subset_of_nonneg uv (by intros; omega)).trans X.bounded) strict)
  rw [nat_strict] at fail
  push Not at fail
  obtain ⟨p,pu,low⟩ := fail
  let O := outN X.D U p
  let G := outN E U p
  let B := outN X.D K p
  have inc : O⊆G := fun z zo => mem_outN.mpr ⟨(mem_outN.mp zo).1,preserve p pu z (mem_outN.mp zo).1 (mem_outN.mp zo).2⟩
  have mass := sum_sdiff sub (f:=X.weights)
  change (∑z∈U,X.weights z)+(∑z∈K,X.weights z)=_ at mass
  have split : score q X.D X.V X.weights p =
      X.weights p+q*(∑z∈O,X.weights z)+q*(∑z∈B,X.weights z) := by
    simp only [O,B,U,score,outN,sum_filter]
    rw [←sum_sdiff sub (f:=fun z => if X.D p z=true then X.weights z else 0),Nat.mul_add]
    omega
  have form : score q E U X.weights p = X.weights p+q*(∑z∈G,X.weights z) := by
    simp only [G,score,outN,sum_filter]
  rw [form] at low
  have high := nat_strict.mp X.strict p (uv pu)
  have old := Nat.mul_le_mul_left q (sum_le_sum_of_subset_of_nonneg inc (f:=X.weights) (by intros; omega))
  have cap : score q X.D X.V X.weights p + (∑z∈K,X.weights z) ≤
      (∑z∈X.V,X.weights z)+q*(∑z∈B,X.weights z) := by omega
  have bx : B.Nonempty := by
    by_contra empty
    rw [not_nonempty_iff_eq_empty.mp empty,sum_empty,Nat.mul_zero] at cap
    omega
  obtain ⟨x,xb⟩ := bx
  obtain ⟨xk,px⟩ := mem_outN.mp xb
  have one : B={x} := by
    ext z
    constructor
    · intro zb
      obtain ⟨zk,pz⟩ := mem_outN.mp zb
      apply mem_singleton.mpr
      rcases chain z zk x xk with f|f
      · exact ComparableColumnCut.distinct_heads X hq (uv pu) (sub zk) pz px f
      · exact (ComparableColumnCut.distinct_heads X hq (uv pu) (sub xk) px pz f).symm
    · intro eq
      exact mem_singleton.mp eq ▸ xb
  have block : Blocks X K p x := ⟨pu,xk,one,by simpa [one] using cap⟩
  refine ⟨p,x,block,?_⟩
  let H := gifts x
  have more : H⊆G := fun z zh => mem_outN.mpr ⟨(fresh p x block z zh).1,(fresh p x block z zh).2.1⟩
  have sep : Disjoint O H := by
    apply disjoint_left.mpr
    intro z zo zh
    have yes := (mem_outN.mp zo).2
    rw [(fresh p x block z zh).2.2] at yes
    contradiction
  have joint := sum_le_sum_of_subset_of_nonneg (union_subset inc more) (f:=X.weights) (by intros; omega)
  rw [sum_union sep] at joint
  have gain := Nat.mul_le_mul_left q joint
  rw [Nat.mul_add] at gain
  rw [one,sum_singleton] at split
  dsimp only [H] at gain
  omega

theorem blocker_of_rectangles {q n} (X : Model q n) (hq : 2≤q) {K J : Finset ℕ} {E : CH.Digraph}
    (sub : K⊆X.V) (live : K.Nonempty) (proper : K≠X.V)
    (chain : ∀u∈K,∀v∈K,Forces X.D X.V q u v ∨ Forces X.D X.V q v u)
    (safeE : QFree E (X.V\K) q)
    (preserve : ∀p∈X.V\K,∀z∈X.V\K,X.D p z=true → E p z=true)
    (restores : ∀t∈J,∀p∈X.V\K,X.D p t=true → ∀y∈outN X.D (X.V\K) t,E p y=true)
    (missing : ∀t∈J,∀p∈X.V\K,X.D p t=true → ∀y∈outN X.D (X.V\K) t,X.D p y=false)
    (paid : ∀t∈J,X.weights t≤∑y∈outN X.D (X.V\K) t,X.weights y) :
    ∃p x,x∉J ∧ Blocks X K p x := by
  classical
  let gifts (x : ℕ) := if x∈J then outN X.D (X.V\K) x else ∅
  obtain ⟨p,x,b,loss⟩ := gift_loss X hq sub live proper chain safeE preserve gifts (by
    intro p x b z zh
    by_cases xj : x∈J
    · have head : z∈outN X.D (X.V\K) x := by simpa [gifts,xj] using zh
      have hit : x∈outN X.D K p := b.2.2.1 ▸ mem_singleton_self _
      have px := (mem_outN.mp hit).2
      exact ⟨(mem_outN.mp head).1,restores x xj p b.1 px z head,missing x xj p b.1 px z head⟩
    · simp [gifts,xj] at zh)
  refine ⟨p,x,?_,b⟩
  intro xj
  simp only [gifts,ite_eq_left xj] at loss
  have high := nat_strict.mp X.strict p (mem_sdiff.mp b.1).1
  have gain := Nat.mul_le_mul_left q (paid x xj)
  omega

/-- After all parents of t are compensated by the bypass rectangle, some
outside parent still fails at a different class head. Exact retained head
mass suffices; no minimum-weight hypothesis occurs in the repair itself. -/
theorem after_pivot {q n} (X : Model q n) (hq : 2≤q) {K : Finset ℕ} {t r}
    (sub : K⊆X.V) (proper : K≠X.V) (tk : t∈K) (rk : r∈K) (ne : t≠r)
    (chain : ∀u∈K,∀v∈K,Forces X.D X.V q u v ∨ Forces X.D X.V q v u)
    (mandatory : Forces X.D X.V q t r)
    (paid : X.weights t≤∑z∈outN X.D (X.V\K) t,X.weights z) :
    ∃p x, x≠t ∧ Blocks X K p x := by
  classical
  let U := X.V\K
  let W := insert t U
  let H := outN X.D U t
  let E := repair X.D (inN X.D U t) (fun _ => H)
  have uv : U⊆X.V := sdiff_subset
  have tu : t∉U := fun hit => (mem_sdiff.mp hit).2 tk
  have tw : t∈W := mem_insert_self _ _
  have wv : W⊆X.V := insert_subset (sub tk) uv
  have ru : r∉W := fun hit => (mem_insert.mp hit).elim ne.symm (fun e => (mem_sdiff.mp e).2 rk)
  have absent : ¬∃C,Cycle X.D W q C ∧ t∈C := by
    rintro ⟨C,c,tc⟩
    exact ru (c.sub (mandatory C ⟨c.sub.trans wv,c.size,c.heads,c.incoming⟩ tc))
  have safe : QFree E U q := by
    have good := PunctureBypass.safe hq (X.free.mono_set wv) tw absent
    simpa only [W,erase_insert tu] using good
  obtain ⟨p,x,out,block⟩ := blocker_of_rectangles X hq (J:={t}) sub ⟨t,tk⟩ proper chain safe
    (fun _ _ _ _ arc => repair_old arc)
    (fun s st p pu ps y yh => by
      obtain rfl := mem_singleton.mp st
      exact repair_new (mem_inN.mpr ⟨pu,ps⟩) yh)
    (fun s st p pu ps y yh => by
      obtain rfl := mem_singleton.mp st
      exact missing_arc X hq (mem_erase.mpr ⟨ne,sub tk⟩) (uv pu) (uv (mem_outN.mp yh).1)
        ps (mem_outN.mp yh).2 (forces_iff.mp mandatory))
    (fun s st => mem_singleton.mp st ▸ paid)
  exact ⟨p,x,fun eq => out (mem_singleton.mpr eq),block⟩

theorem class_profile {q n} (X : Model q n) (hq : 2≤q) {K : Finset ℕ} {h}
    (sub : K⊆X.V) (hk : h∈K)
    (equal : ∀x∈K,∀y∈K,Forces X.D X.V q x y)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card) :
    (∀x∈K,X.weights x≤(q-1)*X.weights h) ∧
    (∀x∈K,outN X.D (X.V\K) x=outN X.D X.V x) := by
  classical
  have light (x) (xk : x∈K) : X.weights x≤(q-1)*X.weights h := by
    by_cases same : x=h
    · rw [same]; exact Nat.le_mul_of_pos_left _ (by omega)
    · have absent := forces_iff.mp (equal x xk h hk)
      have tw := mem_erase.mpr ⟨same,sub xk⟩
      exact (((PunctureReceiverFrontier.classify X hq (sub hk) tw minimum size).resolve_left absent).1).le
  have outside (x) (xk : x∈K) (y) (yh : y∈outN X.D X.V x) : y∉K := by
    intro yk
    have xy := (mem_outN.mp yh).2
    have ne : x≠y := by rintro rfl; exact loopfree X.free (by omega) (sub xk) xy
    have dis := LightColumnPacking.disjoint_neighbourhoods X hq (sub xk) (sub yk) ne minimum size
      (light x xk) (light y yk) (Or.inl (equal x xk y yk))
    exact disjoint_left.mp dis (mem_insert_of_mem (mem_union_left _ yh)) (mem_insert_self _ _)
  have heads (x) (xk : x∈K) : outN X.D (X.V\K) x=outN X.D X.V x := by
    ext y
    constructor
    · intro yh
      exact mem_outN.mpr ⟨(mem_sdiff.mp (mem_outN.mp yh).1).1,(mem_outN.mp yh).2⟩
    · intro yh
      exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨(mem_outN.mp yh).1,outside x xk y yh⟩,(mem_outN.mp yh).2⟩
  exact ⟨light,heads⟩

/-- The native light-class hypotheses supply all the head mass and all missing
entries used by the general deletion test, on the original finite budget. -/
theorem class_data {q n} (X : Model q n) (hq : 2≤q) {K : Finset ℕ} {h}
    (sub : K⊆X.V) (hk : h∈K) (many : 2≤K.card)
    (equal : ∀x∈K,∀y∈K,Forces X.D X.V q x y)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card) :
    K≠X.V ∧ (∀t∈K, X.weights t≤∑z∈outN X.D (X.V\K) t,X.weights z) ∧
    (∀t∈K,∀p∈X.V\K,X.D p t=true → ∀y∈outN X.D (X.V\K) t,X.D p y=false) := by
  classical
  obtain ⟨light,heads⟩ := class_profile X hq sub hk equal minimum size
  have floor (x) (xk : x∈K) := PunctureWeightCoverage.flow_floor X (sub xk) minimum size
  have proper : K≠X.V := by
    have nonempty : (outN X.D X.V h).Nonempty := by
      by_contra none
      have e := floor h hk
      rw [not_nonempty_iff_eq_empty.mp none,sum_empty] at e
      omega
    obtain ⟨y,yh⟩ := nonempty
    intro eq
    rw [←heads h hk] at yh
    obtain ⟨inside,away⟩ := mem_sdiff.mp (mem_outN.mp yh).1
    exact away (eq ▸ inside)
  refine ⟨proper,fun t tk => ?_,?_⟩
  · rw [heads t tk]
    exact (light t tk).trans (floor t tk).le
  · intro t tk p pu pt y yh
    obtain ⟨r,rk,ne⟩ := exists_mem_ne (s:=K) (a:=t) (by omega)
    exact missing_arc X hq (mem_erase.mpr ⟨ne.symm,sub tk⟩) (mem_sdiff.mp pu).1
      (mem_sdiff.mp (mem_outN.mp yh).1).1 pt (mem_outN.mp yh).2 (forces_iff.mp (equal t tk r rk))

/-- In a recurrent class containing a minimum label, all pivots can actually
be bypassed. Consequently at least two different class heads have a blocking
outside parent in the same original weighted model. -/
theorem two_blockers {q n} (X : Model q n) (hq : 2≤q) {K : Finset ℕ} {h}
    (sub : K⊆X.V) (hk : h∈K) (many : 2≤K.card)
    (equal : ∀x∈K,∀y∈K,Forces X.D X.V q x y)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card) :
    ∃p x r y, x≠y ∧ p≠r ∧ Blocks X K p x ∧ Blocks X K r y := by
  obtain ⟨proper,paid,_⟩ := class_data X hq sub hk many equal minimum size
  have chain (x) (xk : x∈K) (y) (yk : y∈K) :
      Forces X.D X.V q x y ∨ Forces X.D X.V q y x := Or.inl (equal x xk y yk)
  have next (t) (tk : t∈K) : ∃p x,x≠t ∧ Blocks X K p x := by
    obtain ⟨r,rk,ne⟩ := exists_mem_ne (s:=K) (a:=t) (by omega)
    apply after_pivot X hq sub proper tk rk ne.symm chain (equal t tk r rk)
    exact paid t tk
  obtain ⟨p,x,_,first⟩ := next h hk
  obtain ⟨r,y,yx,second⟩ := next x first.2.1
  refine ⟨p,x,r,y,yx.symm,?_,first,second⟩
  rintro rfl
  exact yx (singleton_inj.mp (second.2.2.1.symm.trans first.2.2.1))

#print axioms two_blockers
#print axioms after_pivot
end LeanCH.BR.Closure.EqualColumnRepair
