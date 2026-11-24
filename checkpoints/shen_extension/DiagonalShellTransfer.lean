import checkpoints.shen_extension.OneSpareShellEscape
import checkpoints.shen_extension.dot_tensor_research.DiagonalEight
namespace LeanCH.BR.DiagonalShellTransfer
open Finset BRq2 BRq3 BR45 BRsGen

/-- A short fourth ball cannot leave both its third and fourth layers
below the degree when its second layer has at most one more vertex than
the cutoff. The upper bound on the fourth ball is an input. -/
theorem floor_of_profile {D V q r u b} (free : QFree D V q) (reg : OutEq r D V)
    (uv : u∈V) (hr : 7≤r) (time : r≤q)
    (profile : (ball D V u 4).card≤b →
      (N2 D V u).card≤q+1 ∧ (N3 D V u).card<r ∧ b<(ball D V u 3).card+r) :
    b+1≤(ball D V u 4).card := by
  by_contra! short
  obtain ⟨width,narrow,remaining⟩ := profile (by omega)
  have growth := SparseCycleReturns.two_deficient free uv (fun v vm=>(reg v vm).ge)
    (reg u uv) hr time width narrow
  have count := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
  omega

/-- Record the cutoff, degree and fourth-ball threshold from the
signature of an existing verified profile. The payload converts its
actual root and layers to the hypotheses of the layer rule. -/
structure Profile where
  cutoff : ℕ
  degree : ℕ
  threshold : ℕ
  layers : ∀ {D V}, QFree D V cutoff → OutEq degree D V → ∀ u∈V,
    (ball D V u 4).card≤threshold →
      (N2 D V u).card≤cutoff+1 ∧ (N3 D V u).card<degree ∧ threshold<(ball D V u 3).card+degree

/-- Convert inclusive ball sizes into the needed layer inequalities.
The order and degree of the host and all three profile sizes are
inferred from the supplied theorem, with only the arithmetic tested. -/
def of_exact {q r second third fourth : ℕ}
    (known : ∀ {D V}, QFree D V q → OutEq r D V → ∀ {u}, u∈V →
      (ball D V u 4).card≤fourth → (ball D V u 2).card=second ∧
      (ball D V u 3).card=third ∧ (ball D V u 4).card=fourth)
    (time : 4≤q) (width : second≤r+q+2) (narrow : third<second+r) (small : fourth<third+r) :
    Profile where
  cutoff := q
  degree := r
  threshold := fourth
  layers := by
    intro D V free reg u uv cap
    obtain ⟨h2,h3,_⟩ := known free reg uv cap
    have h1 := card_B1 (free.mono_bound time) uv
    rw [reg u uv] at h1
    have b2 := @card_B2 D V u
    have b3 := @card_B3 D V u
    omega

theorem order {D V q r} (record : Profile) (free : QFree D V q) (live : V.Nonempty)
    (rank : ∀v∈V,r≤(outN D V v).card) (cut : record.cutoff≤q)
    (fit : record.degree≤r) (size : 7≤record.degree) (time : record.degree≤record.cutoff)
    (pair : 4+4≤q) : 2*record.threshold+1≤V.card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq (fun v hv=>fit.trans (rank v hv))
  have ff := qfree_sub sub free
  have each (u) (uv : u∈V) := floor_of_profile (ff.mono_bound cut) reg uv size time
    (record.layers (ff.mono_bound cut) reg u uv)
  have total := card_ge_of_two_balls ff pair each each live
  omega

def profiles : List Profile :=
  [of_exact DiagonalEight.short_profile (by decide) (by decide) (by decide) (by decide)]

private def entryFloor (q r : ℕ) (record : Profile) :=
  if record.cutoff≤q ∧ record.degree≤r ∧ 7≤record.degree ∧ record.degree≤record.cutoff ∧ 4+4≤q
  then 2*record.threshold+1 else 0

def orderFloor (q r : ℕ) := (profiles.map (entryFloor q r)).foldr max 0

theorem bound {D V q r} (free : QFree D V q) (live : V.Nonempty)
    (rank : ∀v∈V,r≤(outN D V v).card) : orderFloor q r≤V.card := by
  have single (record : Profile) : entryFloor q r record≤V.card := by
    unfold entryFloor
    split
    next guard => exact order record free live rank guard.1 guard.2.1 guard.2.2.1 guard.2.2.2.1 guard.2.2.2.2
    next => omega
  have all (rs : List Profile) : (rs.map (entryFloor q r)).foldr max 0≤V.card := by
    induction rs with
    | nil => exact Nat.zero_le _
    | cons x xs ih => exact max_le (single x) ih
  exact all profiles

attribute [aesop safe forward (immediate := [free,reg,uv,hr,time,profile]) (rule_sets := [CHGraphFamilies])] floor_of_profile
attribute [aesop safe forward (immediate := [free,live,rank]) (rule_sets := [CHGraphFamilies])] bound
#print axioms floor_of_profile
#print axioms order
#print axioms bound
end LeanCH.BR.DiagonalShellTransfer
