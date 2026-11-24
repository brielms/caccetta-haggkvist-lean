import checkpoints.shen_extension.JointBlockerCycle

namespace LeanCH.BR.Closure.MultiPivotRepair
open Finset BRq2 BRq3 BR45 DeleteRepair ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights
open MandatoryTwoStep EqualColumnRepair

noncomputable def targets (U J : Finset ℕ) (P H : ℕ→ℕ→Prop) (p : ℕ) : Finset ℕ := by
  classical exact U.filter (fun y => ∃t∈J,P t p ∧ H t y)

noncomputable def edited (D : CH.Digraph) (U J : Finset ℕ) (P H : ℕ→ℕ→Prop) :=
  repair D U (targets U J P H)

theorem target_mem {U J p y P H} : y∈targets U J P H p ↔ y∈U ∧ ∃t∈J,P t p ∧ H t y := by
  classical simp only [targets,mem_filter]

/-- A positive original walk from pivot to pivot can replace each
unmodified gap between consecutive shortcuts at the price of one shortcut. -/
def SafeGaps (D : CH.Digraph) (V U J : Finset ℕ) (P H : ℕ→ℕ→Prop) : Prop :=
  ∀i∈J,∀j∈J,∀y∈U,∀p∈U, H i y → P j p →
    ∀k,Walk D U y p k → ∃d, 1 ≤ d ∧ d ≤ k+1 ∧ Walk D V i j d

/-- Transfer an integer allowance along each transition between pivots.
The two occurrences of each pivot's allowance cancel around a closed walk. -/
def PotentialGaps (D : CH.Digraph) (V U J : Finset ℕ) (P H : ℕ→ℕ→Prop) (f : ℕ→ℕ) : Prop :=
  ∀i∈J,∀j∈J,∀y∈U,∀p∈U, H i y → P j p →
    ∀k,Walk D U y p k → ∃d, 1 ≤ d ∧ d+f j ≤ k+1+f i ∧ Walk D V i j d

private theorem lift_gap {D V U J P H f} (short : PotentialGaps D V U J P H f)
    {k i j y p} (ij : i∈J) (jj : j∈J) (yu : y∈U) (pu : p∈U)
    (iy : H i y) (pj : P j p) (path : Walk (edited D U J P H) U y p k) :
    ∃d, 1 ≤ d ∧ d+f j ≤ k+1+f i ∧ Walk D V i j d := by
  induction k using Nat.strong_induction_on generalizing i y with
  | h k ih =>
    rcases first_new_arc path with old|⟨s,su,z,zt,a,b,len,front,tail⟩
    · exact short i ij j jj y yu p pu iy pj k old
    obtain ⟨zu,t,tj,st,tz⟩ := target_mem.mp zt
    obtain ⟨d,dp,dc,walk⟩ := short i ij t tj y yu s su iy st a front
    obtain ⟨e,ep,ec,finish⟩ := ih b (by omega) tj zu tz tail
    exact ⟨d+e,by omega,by omega,walk.append finish⟩

theorem safe_with_potential {D V U J q P H f} (free : QFree D V q) (uv : U⊆V) (short : PotentialGaps D V U J P H f) :
    QFree (edited D U J P H) U q := by
  intro a k pos small path
  rcases first_new_arc path with old|⟨p,pu,y,yt,i,j,len,front,tail⟩
  · exact free a k pos small (old.mono uv)
  obtain ⟨yu,t,tj,pt,ty⟩ := target_mem.mp yt
  have around : Walk (edited D U J P H) U y p (j+i) := tail.append (walk_sub (fun _ _ h => repair_old h) front)
  obtain ⟨d,dp,dc,walk⟩ := lift_gap short tj tj yu pu ty pt around
  exact free t d dp (by omega) walk

theorem safe {D V U J q P H} (free : QFree D V q) (uv : U⊆V) (short : SafeGaps D V U J P H) :
    QFree (edited D U J P H) U q :=
  safe_with_potential (f:=fun _ => 0) free uv short

abbrev Shortens (D : CH.Digraph) (V U J : Finset ℕ) :=
  SafeGaps D V U J (fun t p => D p t=true) (fun t y => D t y=true)

/-- If these pivots jointly cover every low-margin parent after deleting K,
the edited graph is a strictly smaller countermodel. Thus a blocker must
have its unique class head outside J. -/
theorem blocker_outside {q n} (X : Model q n) (hq : 2≤q) {K J : Finset ℕ}
    (sub : K⊆X.V) (live : K.Nonempty) (proper : K≠X.V) 
    (chain : ∀u∈K,∀v∈K,Forces X.D X.V q u v ∨ Forces X.D X.V q v u)
    (short : Shortens X.D X.V (X.V\K) J)
    (missing : ∀t∈J,∀p∈X.V\K,X.D p t=true → ∀y∈outN X.D (X.V\K) t,X.D p y=false)
    (paid : ∀t∈J,X.weights t≤∑y∈outN X.D (X.V\K) t,X.weights y) :
    ∃p x,x∉J ∧ Blocks X K p x := by
  classical
  exact blocker_of_rectangles X hq sub live proper chain (safe X.free sdiff_subset short)
    (fun _ _ _ _ arc => repair_old arc)
    (fun t tj p pu pt y yh => repair_new pu (target_mem.mpr ⟨(mem_outN.mp yh).1,t,tj,pt,(mem_outN.mp yh).2⟩))
    missing paid

theorem recurrent_blocker {q n} (X : Model q n) (hq : 2≤q) {K J : Finset ℕ} {h}
    (sub : K⊆X.V) (hk : h∈K) (many : 2≤K.card) (jk : J⊆K)
    (equal : ∀x∈K,∀y∈K,Forces X.D X.V q x y)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card)
    (short : Shortens X.D X.V (X.V\K) J) : ∃p x,x∉J ∧ Blocks X K p x := by
  obtain ⟨proper,paid,missing⟩ := class_data X hq sub hk many equal minimum size
  exact blocker_outside X hq sub ⟨h,hk⟩ proper (fun u uk v vk => Or.inl (equal u uk v vk))
    short (fun t tj => missing t (jk tj)) (fun t tj => paid t (jk tj))

#print axioms safe_with_potential
#print axioms safe
#print axioms blocker_outside
#print axioms recurrent_blocker
end LeanCH.BR.Closure.MultiPivotRepair
