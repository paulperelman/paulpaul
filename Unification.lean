import ChallengeSpec

/-!
# The four-force unification node in the challenge's public language

This module evaluates the methodology that would lead from the repository's
public language to the unification of the four fundamental forces (strong,
weak, electromagnetic, gravitational) inside Yang-Mills theory, without extra
spatial dimensions and without string theory. It is the companion of
`UNIFICATION_SCENARIOS.md` and the third member of the family whose earlier
members are `MassGap.lean` (mass gap: everything proved but one explicit
axiom node) and `Confinement.lean` (confinement: no datum needed, but the
unconditional claim not derivable).

The public language quantifies over a **single** closed matrix subgroup with
a nonabelian simple real Lie algebra (`GaugeGroup.IsSimple`), one Wilson
family per group, and one running slope per family. Unification claims a
common parent for several sectors, a meeting of coupling flows, a matter
embedding, and a coupling of the stress trace to a metric datum. No structure
field of `PublicTheory` carries any of this: the gauge group is an orphan
structure, diffeomorphisms do not exist in the language (the mass-gap module
records that `PoincareAction` intertwines pure translations only), field
labels are unstructured, and the running datum is one slope for one family.

The machine-checked content:

* `GaugeInterface`: the sector interface (the `GaugeIntertwinesTypeDef`
  pattern of `Confinement.lean` — unitary action fixing the vacuum,
  covariance, separation).
* `FactorsThrough`: the factoring datum expressing that several sector
  interfaces are restrictions of one parent interface — the spectral form of
  "the forces share one gauge origin".
* `freeLabel_parentFixed` / `free_means_parentNeutral`: a free label is fixed
  by the parent action — the Gauss-law argument at the unified group.
* `sectorConfined_of_parentNeutral`: a label charged under **any** sector
  whose interface factors through the parent is confined — unification
  strengthens the confinement conclusion from one sector to all of them,
  conditionally on the parent datum and the parent shell-neutrality.
* `charged_of_sectorCharged`: sector charge is detected by the parent.
* `CouplingFlow` / `UnifiedCouplings` / `unified_of_flow`: coupling
  unification is arithmetic **given** the flow datum; the datum itself is a
  postulate the public language cannot supply (`running` is one slope for
  one family).
* `DiffIntertwines` / `diagonal_pullback`: the gravitational analogue of the
  mass-gap module's missing Lorentz datum. The public language has no
  diffeomorphism object at all; with the datum declared, spectral measures
  transfer across it — the pullback law on which any stress-trace coupling
  would have to rest.

Consequently the unification methodology is ruled out as a public-language
derivation: the decoupled-sector witness (the direct-sum construction of
`ConfinementScenarios.md` Part IV, applied one level up) satisfies every
hypothesis class clause for a disjoint union of gauge sectors, which is
manifestly not a unification. What survives is a conditional skeleton with
five named missing data (`UNIFICATION_SCENARIOS.md` Part V). This file
contains no `sorry` and no `axiom`; the missing data are carried visibly by
the structures and hypotheses of the bridge theorems, in the discipline of
`Confinement.lean`.
-/
set_option autoImplicit false
noncomputable section
namespace YangMills
open MeasureTheory Set Function Filter
open scoped Topology NNReal ENNReal

variable {H : HilbertSpace} {Labels : FieldLabels}

/-! ## Geometry copied from the public coordinates -/

/-- The time coordinate as a continuous linear functional. -/
def timeL : Spacetime →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap { toFun := time, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[fun_prop] lemma time_cont : Continuous time := timeL.continuous

/-- The spatial part as a continuous linear map. -/
def spatialL : Spacetime →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap { toFun := spatial, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[fun_prop] lemma spatial_cont : Continuous spatial := spatialL.continuous

@[fun_prop] lemma spatial_norm_cont : Continuous fun p : Spacetime => ‖spatial p‖ :=
  continuous_norm.comp spatial_cont

lemma closed_forwardCone : IsClosed forwardCone :=
  isClosed_le (by fun_prop) time_cont

theorem measurableSet_forwardCone : MeasurableSet forwardCone :=
  closed_forwardCone.measurableSet

@[fun_prop] lemma continuous_minkowskiSquare : Continuous minkowskiSquare := by
  unfold minkowskiSquare; fun_prop

/-! ## The positive-mass shell in the public language -/

/-- The positive-mass shell: forward-cone points of Minkowski square `m^2`. -/
def massShell (m : ℝ) : Set Spacetime :=
  {p | p ∈ forwardCone ∧ minkowskiSquare p = m ^ 2 ∧ p ≠ 0}

theorem measurableSet_massShell (m : ℝ) : MeasurableSet (massShell m) := by
  have hEq : massShell m =
      forwardCone ∩ {p : Spacetime | minkowskiSquare p = m ^ 2} ∩
        Set.compl {(0 : Spacetime)} := by
    ext p
    simp only [massShell, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [hEq]
  exact ((measurableSet_forwardCone.inter
    (isClosed_eq continuous_minkowskiSquare continuous_const).measurableSet).inter
    (measurableSet_singleton (0 : Spacetime)).compl)

/-! ## Label excitations and spectral freeness -/

/-- One smeared field application to the vacuum: the state `φ_ℓ(f)Ω`. -/
def excitation (T : WightmanTheory H Labels) (ℓ : Labels.carrier)
    (f : TestFunction) : H.carrier := (T.fields.field ℓ f T.fields.vacuum).1

/-- The zero state has zero spectral measure. -/
theorem diagonal_zero_measure (T : WightmanTheory H Labels) (m : ℝ) :
    (T.energyMomentum.diagonal 0) (massShell m) = 0 := by
  have hreal : (T.energyMomentum.diagonal 0).real (massShell m) = 0 := by
    have h := T.energyMomentum.diagonalIdentity (measurableSet_massShell m) (0 : H.carrier)
    simp only [map_zero, inner_zero_left] at h
    exact Complex.ofReal_eq_zero.mp h
  have hne : (T.energyMomentum.diagonal 0) (massShell m) ≠ ∞ := measure_ne_top _ _
  exact measureReal_eq_zero_iff hne |>.mp hreal

/-- A spectrally charged excitation is a nonzero state. -/
theorem excitation_nonzero_of_free {T : WightmanTheory H Labels}
    {ℓ : Labels.carrier} {f : TestFunction} {m : ℝ}
    (hne : (T.energyMomentum.diagonal (excitation T ℓ f)) (massShell m) ≠ 0) :
    excitation T ℓ f ≠ 0 := by
  intro h0
  rw [h0] at hne
  exact hne (diagonal_zero_measure T m)

/-- A label is **spectrally free** if some of its vacuum excitations charge a
positive-mass shell of the joint energy-momentum PVM. -/
def FreeLabel (T : WightmanTheory H Labels) (ℓ : Labels.carrier) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∃ f : TestFunction,
    (T.energyMomentum.diagonal (excitation T ℓ f)) (massShell m) ≠ 0

/-- Spectral confinement of a label: no free on-shell carrier at all. -/
def ConfinedLabel (T : WightmanTheory H Labels) (ℓ : Labels.carrier) : Prop :=
  ¬ FreeLabel T ℓ

/-! ## The gauge interface — the datum the public language lacks -/

/-- The sector/parent interface (the `GaugeIntertwinesTypeDef` pattern of
`Confinement.lean`, renamed because that file is not a library root): a
unitary gauge action on states fixing the vacuum and preserving the field
domain, an induced label action, gauge covariance of the fields, and
separation of distinct labels by shared nonzero vacuum excitations. -/
structure GaugeInterface (T : WightmanTheory H Labels)
    (gauge : GaugeGroup) where
  ρ : ↥gauge.image → Labels.carrier ≃ₗ[ℂ] Labels.carrier
  U : ↥gauge.image → H.Operator
  vacuumFixed (g : ↥gauge.image) : U g T.fields.vacuum.1 = T.fields.vacuum.1
  domainMapsTo (g : ↥gauge.image) (v : H.carrier) :
    v ∈ T.fields.domain → U g v ∈ T.fields.domain
  covariance (g : ↥gauge.image) (ℓ : Labels.carrier) (f : TestFunction)
      (v : ↥T.fields.domain) :
    U g (T.fields.field ℓ f v).1 =
      (T.fields.field (ρ g ℓ) f
        ⟨U g v.1, domainMapsTo g v.1 v.2⟩).1
  separates (ℓ ℓ' : Labels.carrier) (f : TestFunction) :
    excitation T ℓ f = excitation T ℓ' f → excitation T ℓ f ≠ 0 → ℓ = ℓ'

/-- The Gauss-law-shaped datum: on-shell excitations are gauge-neutral. -/
def ShellNeutral (T : WightmanTheory H Labels) (gauge : GaugeGroup)
    (U : ↥gauge.image → H.Operator) : Prop :=
  ∀ (g : ↥gauge.image) (ℓ : Labels.carrier) (f : TestFunction) (m : ℝ),
    0 < m →
    (T.energyMomentum.diagonal (excitation T ℓ f)) (massShell m) ≠ 0 →
    U g (excitation T ℓ f) = excitation T ℓ f

/-- A label is charged under a gauge group when some transformation moves it. -/
def ColorCharged (gauge : GaugeGroup) (ρ : ↥gauge.image → Labels.carrier ≃ₗ[ℂ] Labels.carrier)
    (ℓ : Labels.carrier) : Prop := ∃ g : ↥gauge.image, ρ g ℓ ≠ ℓ

/-! ## The unification datum: sectors factoring through one parent -/

/-- The factoring datum: several sector interfaces are restrictions of one
parent interface on a larger gauge group — the spectral form of "the forces
share one gauge origin". No structure field of `PublicTheory` carries any of
this; the existence theory of `ChallengeSpec` is stated one group at a time. -/
structure FactorsThrough (T : WightmanTheory H Labels)
    (sector parent : GaugeGroup)
    (I : GaugeInterface T sector) (P : GaugeInterface T parent) where
  embed : ↥sector.image → ↥parent.image
  embedOnStates (g : ↥sector.image) : I.U g = P.U (embed g)
  embedOnLabels (g : ↥sector.image) (ℓ : Labels.carrier) : I.ρ g ℓ = P.ρ (embed g) ℓ

/-- Gauge covariance of the vacuum excitation under the parent action. -/
lemma gauge_excitation (T : WightmanTheory H Labels) (gauge : GaugeGroup)
    (I : GaugeInterface T gauge) (g : ↥gauge.image) (ℓ : Labels.carrier)
    (f : TestFunction) :
    I.U g (excitation T ℓ f) = excitation T (I.ρ g ℓ) f := by
  have hc := I.covariance g ℓ f T.fields.vacuum
  show I.U g (T.fields.field ℓ f T.fields.vacuum).1 =
    (T.fields.field (I.ρ g ℓ) f T.fields.vacuum).1
  rw [hc]
  exact congrArg (fun v : ↥T.fields.domain => (T.fields.field (I.ρ g ℓ) f v).1)
    (Subtype.ext (I.vacuumFixed g))

/-- A free label is fixed by the parent action: the Gauss-law argument at the
unified group. -/
theorem freeLabel_parentFixed (T : WightmanTheory H Labels) (gauge : GaugeGroup)
    (P : GaugeInterface T gauge) (hphys : ShellNeutral T gauge P.U)
    {ℓ : Labels.carrier} (hfree : FreeLabel T ℓ) (g : ↥gauge.image) :
    P.ρ g ℓ = ℓ := by
  obtain ⟨m, hm, f, hne⟩ := hfree
  have h0 : excitation T ℓ f ≠ 0 := excitation_nonzero_of_free hne
  have hh : excitation T (P.ρ g ℓ) f = excitation T ℓ f :=
    (gauge_excitation T gauge P g ℓ f).symm.trans (hphys g ℓ f m hm hne)
  exact (P.separates ℓ (P.ρ g ℓ) f hh.symm h0).symm

/-- Sector charge is detected by the parent: a label moved by a sector
transformation is moved by the parent transformation it factors through. -/
theorem charged_of_sectorCharged (T : WightmanTheory H Labels)
    (sector parent : GaugeGroup) (I : GaugeInterface T sector) (P : GaugeInterface T parent)
    (F : FactorsThrough T sector parent I P)
    {ℓ : Labels.carrier} (hcharge : ColorCharged sector I.ρ ℓ) :
    ColorCharged parent P.ρ ℓ := by
  obtain ⟨g, hne⟩ := hcharge
  refine ⟨F.embed g, ?_⟩
  rw [← F.embedOnLabels g ℓ]
  exact hne

/-- **Unification strengthens the confinement conclusion.** A label charged
under any sector whose interface factors through the parent is confined —
conditional on the parent interface and the parent shell-neutrality. The
conditional chain of `Confinement.lean` thus covers all sectors at once —
but every hypothesis is a missing datum of the public language. -/
theorem sectorConfined_of_parentNeutral (T : WightmanTheory H Labels)
    (sector parent : GaugeGroup) (I : GaugeInterface T sector) (P : GaugeInterface T parent)
    (F : FactorsThrough T sector parent I P)
    (hphys : ShellNeutral T parent P.U)
    {ℓ : Labels.carrier} (hcharge : ColorCharged sector I.ρ ℓ) :
    ConfinedLabel T ℓ := by
  intro hfree
  obtain ⟨g, hne⟩ := hcharge
  have hfixed : P.ρ (F.embed g) ℓ = ℓ :=
    freeLabel_parentFixed T parent P hphys hfree (F.embed g)
  rw [← F.embedOnLabels g ℓ] at hfixed
  exact hne hfixed

/-- Contrapositive summary: freeness forces parent-neutrality. -/
theorem free_means_parentNeutral (T : WightmanTheory H Labels)
    (gauge : GaugeGroup) (P : GaugeInterface T gauge) (hphys : ShellNeutral T gauge P.U)
    {ℓ : Labels.carrier} (hfree : FreeLabel T ℓ) :
    ¬ ColorCharged gauge P.ρ ℓ := by
  intro hc
  obtain ⟨g, hne⟩ := hc
  exact hne (freeLabel_parentFixed T gauge P hphys hfree g)

/-! ## The coupling-flow datum (ledger node A1) -/

/-- The candidate coupling-flow datum: a finite family of sector running
slopes **with a meeting point**. The public language supplies one slope for
one Wilson family (`ChallengeSpec.WilsonRegularity.running`); the meeting
condition across families is a postulate. -/
structure CouplingFlow (k : ℕ) where
  beta : Fin k → ℝ
  meet : ∃ μ : ℝ, 0 < μ ∧ ∀ i : Fin k, beta i = μ

/-- Coupling unification in the spectral language: the sector slopes agree at
a strictly positive scale. -/
def UnifiedCouplings (k : ℕ) (beta : Fin k → ℝ) : Prop :=
  ∃ μ : ℝ, 0 < μ ∧ ∀ i : Fin k, beta i = μ

/-- Coupling unification is arithmetic **given** the flow datum. The theorem
is one line; the physics is entirely in `CouplingFlow.meet`, which the public
language cannot supply — this is the exact shape of the mass-gap module's
isolated node. -/
theorem unified_of_flow {k : ℕ} (F : CouplingFlow k) :
    UnifiedCouplings k F.beta := F.meet

/-! ## The gravity datum (ledger nodes A2/A3) -/

/-- The candidate diffeomorphism-intertwining datum — the gravitational
analogue of the mass-gap module's missing `LorentzIntertwines`. The public
language has no diffeomorphism object at all (`PoincareAction` intertwines
pure translations only), so the datum is declared here, visibly, in the
discipline of the family: assumed as a structure, never silently. -/
structure DiffIntertwines (T : WightmanTheory H Labels) where
  diffeo : Type
  coords : diffeo → (Spacetime →L[ℝ] Spacetime)
  U : diffeo → H.Operator
  vacuumFixed (φ : diffeo) : U φ T.fields.vacuum.1 = T.fields.vacuum.1
  domainMapsTo (φ : diffeo) (v : H.carrier) :
    v ∈ T.fields.domain → U φ v ∈ T.fields.domain
  spectralCovariance (φ : diffeo) {A : Set Spacetime} (_ : MeasurableSet A) :
    T.energyMomentum.projection (Set.preimage (coords φ : Spacetime → Spacetime) A) =
      ((U φ).adjoint).comp ((T.energyMomentum.projection A).comp (U φ))

/-- The pullback law: spectral pairings transfer across the diffeomorphism
action — the identity on which any stress-trace (gravitational) coupling
would have to rest. Proved from PVM algebra alone, given the datum. -/
theorem diagonal_pullback (T : WightmanTheory H Labels) (D : DiffIntertwines T)
    (φ : D.diffeo) {A : Set Spacetime} (hA : MeasurableSet A) (ψ : H.carrier) :
    inner ℂ (D.U φ ψ) ((T.energyMomentum.projection A) ((D.U φ) ψ)) =
      inner ℂ ψ ((T.energyMomentum.projection
        (Set.preimage (D.coords φ : Spacetime → Spacetime) A)) ψ) := by
  have h1 : inner ℂ (D.U φ ψ) ((T.energyMomentum.projection A) ((D.U φ) ψ))
      = inner ℂ ψ ((D.U φ).adjoint ((T.energyMomentum.projection A) ((D.U φ) ψ))) :=
    (ContinuousLinearMap.adjoint_inner_right (D.U φ) ψ _).symm
  have h2 : ((D.U φ).adjoint) ((T.energyMomentum.projection A) ((D.U φ) ψ))
      = (((D.U φ).adjoint).comp ((T.energyMomentum.projection A).comp (D.U φ))) ψ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [h1, h2, ← D.spectralCovariance φ hA]

end YangMills
end
