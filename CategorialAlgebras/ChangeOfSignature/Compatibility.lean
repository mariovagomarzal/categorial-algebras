import CategorialAlgebras.ChangeOfSignature.CompatibilityDerivors
import CategorialAlgebras.ChangeOfSignature.Models
import CategorialAlgebras.Dimensions.GraduationCompatibility
import CategorialAlgebras.Presentations.UnificationModels

/-!
# Change of signature commutes with the presentation and dimension functors

The functors of a change of signature commute with graduation, unification,
discretization and truncation:
$$\mathrm{Gd}^{(n)}_{\Sigma}\circ\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}=
\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}\circ\mathrm{Gd}^{(n)}_{\Lambda},\qquad
\mathrm{Uf}^{(n)}_{\Sigma}\circ\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}=
\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}\circ\mathrm{Uf}^{(n)}_{\Lambda},$$
and similarly for discretization and truncation in both presentations. These are the
naturality conditions that make graduation, unification, discretization and truncation
transformations between the indexed categories of categorial algebras.

The equalities of functors are natural isomorphisms whose components are identities on the
underlying elements. They are the comparisons of induced functors obtained from the
equalities of the composite generalized hep-derivors, restricted to models and transported
to categorial algebras.
-/

universe u v w

namespace CategorialAlgebras.ChangeOfSignature

open CategoryTheory Presentations Dimensions

set_option backward.isDefEq.respectTransparency false

variable {S T : Type u} {sig : Signature.{u, v} S} {tau : Signature.{u, v} T}

/-! ## Cells of the transformed models -/

/-- In a transformed model, the recovered boundaries of a cell of sort $s$ are those of
the original model at the sort $\varphi(s)$. -/
theorem homogeneous_boundary_val {n : ℕ} (c : Derivor sig tau)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) tau))
    (hB : (Homogeneous.specification (Fin n) tau).IsModel B)
    (k : Fin n) (b : Bool) (s : S) (x : (homogeneous (Fin n) c).Cell B s) :
    ((((recoveredAlgebra ((homogeneous (Fin n) c).transformed B)
        (homogeneous_isModel c B hB)).sort s).str.dim k).boundary b x).val =
      (((recoveredAlgebra B hB).sort (c.sortMap s)).str.dim k).boundary b x.val := by
  let hA := homogeneous_isModel c B hB
  let q := (((recoveredAlgebra ((homogeneous (Fin n) c).transformed B) hA).sort s).str.dim k).boundary b x
  have hq : q ∈ ((homogeneous (Fin n) c).transformed B).op
      (.boundary k s b) (Homogeneous.single x) := by
    cases b <;> erw [Homogeneous.boundary_op (fun e => hA.2 _ ⟨e, rfl⟩)] <;>
      exact Part.mem_some _
  have hv := ((homogeneous (Fin n) c).mem_transformed_op B _ _ _).mp hq |>.2
  cases b
  · change q.val ∈ Term.partialEval _ (Homogeneous.unary (.source k (c.sortMap s)) _) at hv
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some,
      Homogeneous.boundary_op (fun e => hB.2 _ ⟨e, rfl⟩) _ false] at hv
    exact Part.mem_some_iff.mp hv
  · change q.val ∈ Term.partialEval _ (Homogeneous.unary (.target k (c.sortMap s)) _) at hv
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some,
      Homogeneous.boundary_op (fun e => hB.2 _ ⟨e, rfl⟩) _ true] at hv
    exact Part.mem_some_iff.mp hv

/-- The homogeneous derivor of a change of signature translates the fixed-source equation
of sort $s$ to that of sort $\varphi(s)$. -/
theorem homogeneous_translate_equation {n : ℕ} (c : Derivor sig tau) (k : Fin n) (s : S) :
    (homogeneousDerivor (Fin n) c).translateSingletonSet s
        (Homogeneous.singletonEquation (truncationEquation sig k s)) =
      Homogeneous.singletonEquation (truncationEquation tau k (c.sortMap s)) := by
  refine (translateSingletonSet_singleton (homogeneousDerivor (Fin n) c) _).trans ?_
  congr 1
  apply Prod.ext
  · rfl
  · apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) tau) (.source k _))
    funext j
    fin_cases j
    rfl

/-- A cell of a transformed model satisfies a fixed-source equation exactly when its
underlying element satisfies the translated equation in the original model. -/
theorem homogeneous_satisfies_iff {n : ℕ} (c : Derivor sig tau)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) tau))
    (hB : (Homogeneous.specification (Fin n) tau).IsModel B)
    (k : Fin n) (s : S) (x : (homogeneous (Fin n) c).Cell B s) :
    EEquationSet.Satisfies ((homogeneous (Fin n) c).transformed B) (Word.singletonValuation x)
        (Homogeneous.singletonEquation (truncationEquation sig k s)) ↔
      EEquationSet.Satisfies B (Word.singletonValuation x.val)
        ((homogeneousDerivor (Fin n) c).translateSingletonSet s
          (Homogeneous.singletonEquation (truncationEquation sig k s))) := by
  rw [homogeneous_translate_equation]
  refine (satisfies_truncationEquation_iff _ (homogeneous_isModel c B hB) k s x).trans
    (Iff.trans ?_ (satisfies_truncationEquation_iff B hB k (c.sortMap s) x.val).symm)
  change _ = _ ↔ _ = _
  constructor
  · intro hx
    exact (homogeneous_boundary_val c B hB k false s x).symm.trans (congrArg Subtype.val hx)
  · intro hx
    exact Subtype.ext ((homogeneous_boundary_val c B hB k false s x).trans hx)

/-- Graduation followed by the homogeneous derivor of a change of signature has a
surjective canonical composition comparison on models. -/
theorem graduation_homogeneous_comparison_surjective {n : ℕ} (c : Derivor sig tau)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) tau))
    (hB : (Homogeneous.specification (Fin n) tau).IsModel B) :
    ∀ p, Function.Surjective
      (((graduation n sig).comparison (homogeneous (Fin n) c) B).toMap p) := by
  apply ((graduation n sig).comparison_surjective_iff (homogeneous (Fin n) c) B).mpr
  rintro ⟨k, s⟩ x hx
  change EEquationSet.Satisfies _ _ (if hh : k.val < n then _ else _)
  change EEquationSet.Satisfies B _ ((homogeneousDerivor (Fin n) c).translateSingletonSet _
    (if hh : k.val < n then _ else _)) at hx
  by_cases hk : k.val < n
  · erw [dite_eq_left hk] at hx ⊢
    exact (homogeneous_satisfies_iff c B hB ⟨k.val, hk⟩ s x).mpr hx
  · erw [dite_eq_right hk]
    exact fun _ _ he => he.elim

/-- Truncation followed by the homogeneous derivor of a change of signature has a
surjective canonical composition comparison on models. -/
theorem truncation_homogeneous_comparison_surjective {m n : ℕ} (h : m ≤ n)
    (c : Derivor sig tau)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) tau))
    (hB : (Homogeneous.specification (Fin n) tau).IsModel B) :
    ∀ p, Function.Surjective
      (((homogeneousTruncation sig h).comparison (homogeneous (Fin n) c) B).toMap p) := by
  apply ((homogeneousTruncation sig h).comparison_surjective_iff (homogeneous (Fin n) c) B).mpr
  intro s x hx
  change EEquationSet.Satisfies _ _ (if hh : m < n then _ else _)
  change EEquationSet.Satisfies B _ ((homogeneousDerivor (Fin n) c).translateSingletonSet _
    (if hh : m < n then _ else _)) at hx
  by_cases hm : m < n
  · erw [dite_eq_left hm] at hx ⊢
    exact (homogeneous_satisfies_iff c B hB ⟨m, hm⟩ s x).mpr hx
  · erw [dite_eq_right hm]
    exact fun _ _ he => he.elim

/-! ## The compatibility squares on models -/

/-- Graduation commutes with change of signature on models:
$\mathrm{Gd}^{(n)}_{\Sigma}\circ\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}\circ\mathrm{Gd}^{(n)}_{\Lambda}$. -/
noncomputable def graduationModelsChange (n : ℕ) (c : Derivor sig tau) :
    homogeneousModels.{0, u, v, w} (Fin n) c ⋙ graduationModels n sig ≅
      graduationModels n tau ⋙ heterogeneousModels (Fin (n + 1)) c :=
  inducedSquareModelsNatIso _ _ _ _ (congrArg GeneralizedHepDerivor.toDerivor (graduation_comp n c))
    _ _ _ _ (graduation_isModel n sig) (homogeneous_isModel c) (heterogeneous_isModel c)
    (graduation_isModel n tau) (fun B hB => graduation_homogeneous_comparison_surjective c B hB)
    (fun B _ => (heterogeneous (Fin (n + 1)) c).comparison_surjective_of_empty
      (graduation n tau) B (fun _ => rfl))
    (fun B _ p x => cells_of_eq (graduation_comp n c) B p x)

/-- Unification commutes with change of signature on models:
$\mathrm{Uf}^{(n)}_{\Sigma}\circ\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}\circ\mathrm{Uf}^{(n)}_{\Lambda}$. -/
noncomputable def unificationModelsChange (n : ℕ) (c : Derivor sig tau) :
    heterogeneousModels.{0, u, v, w} (Fin (n + 1)) c ⋙ unificationModels n sig ≅
      unificationModels n tau ⋙ homogeneousModels (Fin n) c :=
  inducedSquareModelsNatIso _ _ _ _
    (congrArg GeneralizedHepDerivor.toDerivor (unification_comp n c))
    _ _ _ _ (unification_isModel n sig) (heterogeneous_isModel c) (homogeneous_isModel c)
    (unification_isModel n tau)
    (fun B _ => (unification n sig).comparison_surjective_of_empty _ B (fun _ => rfl))
    (fun B _ => (homogeneous (Fin n) c).comparison_surjective_of_empty _ B (fun _ => rfl))
    (fun B _ p x => cells_of_eq (unification_comp n c) B p x)

/-- Homogeneous discretization commutes with change of signature on models. -/
noncomputable def homogeneousDiscretizationModelsChange {m n : ℕ} (h : m ≤ n)
    (c : Derivor sig tau) :
    homogeneousModels.{0, u, v, w} (Fin m) c ⋙ homogeneousDiscretizationModels sig h ≅
      homogeneousDiscretizationModels tau h ⋙ homogeneousModels (Fin n) c :=
  inducedSquareModelsNatIso _ _ _ _
    (congrArg GeneralizedHepDerivor.toDerivor (homogeneousDiscretization_comp h c))
    _ _ _ _ (homogeneousDiscretization_isModel sig h) (homogeneous_isModel c)
    (homogeneous_isModel c) (homogeneousDiscretization_isModel tau h)
    (fun B _ => (homogeneousDiscretization sig h).comparison_surjective_of_empty _ B
      (fun _ => rfl))
    (fun B _ => (homogeneous (Fin n) c).comparison_surjective_of_empty _ B (fun _ => rfl))
    (fun B _ p x => cells_of_eq (homogeneousDiscretization_comp h c) B p x)

/-- Homogeneous truncation commutes with change of signature on models. -/
noncomputable def homogeneousTruncationModelsChange {m n : ℕ} (h : m ≤ n)
    (c : Derivor sig tau) :
    homogeneousModels.{0, u, v, w} (Fin n) c ⋙ homogeneousTruncationModels sig h ≅
      homogeneousTruncationModels tau h ⋙ homogeneousModels (Fin m) c :=
  inducedSquareModelsNatIso _ _ _ _
    (congrArg GeneralizedHepDerivor.toDerivor (homogeneousTruncation_comp h c))
    _ _ _ _ (homogeneousTruncation_isModel sig h) (homogeneous_isModel c)
    (homogeneous_isModel c) (homogeneousTruncation_isModel tau h)
    (fun B hB => truncation_homogeneous_comparison_surjective h c B hB)
    (fun B _ => (homogeneous (Fin m) c).comparison_surjective_of_empty _ B (fun _ => rfl))
    (fun B _ p x => cells_of_eq (homogeneousTruncation_comp h c) B p x)

/-- Heterogeneous discretization commutes with change of signature on models. -/
noncomputable def heterogeneousDiscretizationModelsChange {m n : ℕ} (h : m ≤ n)
    (c : Derivor sig tau) :
    heterogeneousModels.{0, u, v, w} (Fin (m + 1)) c ⋙ heterogeneousDiscretizationModels sig h ≅
      heterogeneousDiscretizationModels tau h ⋙ heterogeneousModels (Fin (n + 1)) c :=
  inducedSquareModelsNatIso _ _ _ _
    (congrArg GeneralizedHepDerivor.toDerivor (heterogeneousDimension_comp (clampDimension m) c))
    _ _ _ _ (heterogeneousDiscretization_isModel sig h) (heterogeneous_isModel c)
    (heterogeneous_isModel c) (heterogeneousDiscretization_isModel tau h)
    (fun B _ => (heterogeneousDiscretization sig h).comparison_surjective_of_empty _ B
      (fun _ => rfl))
    (fun B _ => (heterogeneous (Fin (n + 1)) c).comparison_surjective_of_empty _ B
      (fun _ => rfl))
    (fun B _ p x => cells_of_eq (heterogeneousDimension_comp (clampDimension m) c) B p x)

/-- Heterogeneous truncation commutes with change of signature on models. -/
noncomputable def heterogeneousTruncationModelsChange {m n : ℕ} (h : m ≤ n)
    (c : Derivor sig tau) :
    heterogeneousModels.{0, u, v, w} (Fin (n + 1)) c ⋙ heterogeneousTruncationModels sig h ≅
      heterogeneousTruncationModels tau h ⋙ heterogeneousModels (Fin (m + 1)) c :=
  inducedSquareModelsNatIso _ _ _ _
    (congrArg GeneralizedHepDerivor.toDerivor
      (heterogeneousDimension_comp (cellInclusion h).toOrderHom c))
    _ _ _ _ (heterogeneousTruncation_isModel sig h) (heterogeneous_isModel c)
    (heterogeneous_isModel c) (heterogeneousTruncation_isModel tau h)
    (fun B _ => (heterogeneousTruncation sig h).comparison_surjective_of_empty _ B
      (fun _ => rfl))
    (fun B _ => (heterogeneous (Fin (m + 1)) c).comparison_surjective_of_empty _ B
      (fun _ => rfl))
    (fun B _ p x => cells_of_eq (heterogeneousDimension_comp (cellInclusion h).toOrderHom c)
      B p x)

/-! ## Elements -/

/-- The graduation square on models is the identity on underlying elements. -/
theorem graduationModelsComp_hom_val (n : ℕ) (c : Derivor sig tau)
    (B : (Homogeneous.specification (Fin n) tau).Models) (p)
    (x : ((homogeneousModels.{0, u, v, w} (Fin n) c ⋙ graduationModels n sig).obj B).obj.obj.carrier p) :
    ((((graduationModelsChange n c).hom.app B).hom.hom.toMap p x).val).val = x.val.val :=
  eq_of_heq (inducedSquareModelsNatIso_hom_heq (graduation n sig) (homogeneous (Fin n) c)
    (heterogeneous (Fin (n + 1)) c) (graduation n tau) _ _ _ _ _ _ _ _ _ _ _ _ B p x)

/-- The unification square on models is the identity on underlying elements. -/
theorem unificationModelsComp_hom_val (n : ℕ) (c : Derivor sig tau)
    (B : (Heterogeneous.specification (Fin (n + 1)) tau).Models) (s)
    (x : ((heterogeneousModels.{0, u, v, w} (Fin (n + 1)) c ⋙
      unificationModels n sig).obj B).obj.obj.carrier s) :
    ((((unificationModelsChange n c).hom.app B).hom.hom.toMap s x).val).val = x.val.val :=
  eq_of_heq (inducedSquareModelsNatIso_hom_heq (unification n sig)
    (heterogeneous (Fin (n + 1)) c) (homogeneous (Fin n) c) (unification n tau)
    _ _ _ _ _ _ _ _ _ _ _ _ B s x)

/-- The homogeneous discretization square on models is the identity on underlying
elements. -/
theorem homogeneousDiscretizationModelsComp_hom_val {m n : ℕ} (h : m ≤ n) (c : Derivor sig tau)
    (B : (Homogeneous.specification (Fin m) tau).Models) (s)
    (x : ((homogeneousModels.{0, u, v, w} (Fin m) c ⋙
      homogeneousDiscretizationModels sig h).obj B).obj.obj.carrier s) :
    ((((homogeneousDiscretizationModelsChange h c).hom.app B).hom.hom.toMap s x).val).val =
      x.val.val :=
  eq_of_heq (inducedSquareModelsNatIso_hom_heq (homogeneousDiscretization sig h)
    (homogeneous (Fin m) c) (homogeneous (Fin n) c) (homogeneousDiscretization tau h)
    _ _ _ _ _ _ _ _ _ _ _ _ B s x)

/-- The homogeneous truncation square on models is the identity on underlying elements. -/
theorem homogeneousTruncationModelsComp_hom_val {m n : ℕ} (h : m ≤ n) (c : Derivor sig tau)
    (B : (Homogeneous.specification (Fin n) tau).Models) (s)
    (x : ((homogeneousModels.{0, u, v, w} (Fin n) c ⋙
      homogeneousTruncationModels sig h).obj B).obj.obj.carrier s) :
    ((((homogeneousTruncationModelsChange h c).hom.app B).hom.hom.toMap s x).val).val =
      x.val.val :=
  eq_of_heq (inducedSquareModelsNatIso_hom_heq (homogeneousTruncation sig h)
    (homogeneous (Fin n) c) (homogeneous (Fin m) c) (homogeneousTruncation tau h)
    _ _ _ _ _ _ _ _ _ _ _ _ B s x)

/-- The heterogeneous discretization square on models is the identity on underlying
elements. -/
theorem heterogeneousDiscretizationModelsComp_hom_val {m n : ℕ} (h : m ≤ n)
    (c : Derivor sig tau) (B : (Heterogeneous.specification (Fin (m + 1)) tau).Models) (p)
    (x : ((heterogeneousModels.{0, u, v, w} (Fin (m + 1)) c ⋙
      heterogeneousDiscretizationModels sig h).obj B).obj.obj.carrier p) :
    ((((heterogeneousDiscretizationModelsChange h c).hom.app B).hom.hom.toMap p x).val).val =
      x.val.val :=
  eq_of_heq (inducedSquareModelsNatIso_hom_heq (heterogeneousDiscretization sig h)
    (heterogeneous (Fin (m + 1)) c) (heterogeneous (Fin (n + 1)) c)
    (heterogeneousDiscretization tau h) _ _ _ _ _ _ _ _ _ _ _ _ B p x)

/-- The heterogeneous truncation square on models is the identity on underlying
elements. -/
theorem heterogeneousTruncationModelsComp_hom_val {m n : ℕ} (h : m ≤ n)
    (c : Derivor sig tau) (B : (Heterogeneous.specification (Fin (n + 1)) tau).Models) (p)
    (x : ((heterogeneousModels.{0, u, v, w} (Fin (n + 1)) c ⋙
      heterogeneousTruncationModels sig h).obj B).obj.obj.carrier p) :
    ((((heterogeneousTruncationModelsChange h c).hom.app B).hom.hom.toMap p x).val).val =
      x.val.val :=
  eq_of_heq (inducedSquareModelsNatIso_hom_heq (heterogeneousTruncation sig h)
    (heterogeneous (Fin (n + 1)) c) (heterogeneous (Fin (m + 1)) c)
    (heterogeneousTruncation tau h) _ _ _ _ _ _ _ _ _ _ _ _ B p x)

/-! ## The compatibility squares on categorial algebras -/

/-- Graduation commutes with change of signature:
$\mathrm{Gd}^{(n)}_{\Sigma}\circ\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}\circ\mathrm{Gd}^{(n)}_{\Lambda}$. -/
noncomputable def graduationFunctorChange (n : ℕ) (c : Derivor sig tau) :
    homogeneousFunctor.{0, u, v, w} (Fin n) c ⋙ graduationFunctor n sig ≅
      graduationFunctor n tau ⋙ heterogeneousFunctor (Fin (n + 1)) c :=
  conjugateSquareIso Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism (graduationModelsChange n c)

/-- Unification commutes with change of signature:
$\mathrm{Uf}^{(n)}_{\Sigma}\circ\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}\circ\mathrm{Uf}^{(n)}_{\Lambda}$. -/
noncomputable def unificationFunctorChange (n : ℕ) (c : Derivor sig tau) :
    heterogeneousFunctor.{0, u, v, w} (Fin (n + 1)) c ⋙ unificationFunctor n sig ≅
      unificationFunctor n tau ⋙ homogeneousFunctor (Fin n) c :=
  conjugateSquareIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism (unificationModelsChange n c)

/-- Homogeneous discretization commutes with change of signature:
$\mathrm{Ds}^{(n,m)}_{\Sigma}\circ\mathbf{c}^{(m)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}\circ\mathrm{Ds}^{(n,m)}_{\Lambda}$. -/
noncomputable def homogeneousDiscretizationFunctorChange {m n : ℕ} (h : m ≤ n)
    (c : Derivor sig tau) :
    homogeneousFunctor.{0, u, v, w} (Fin m) c ⋙ homogeneousDiscretizationFunctor sig h ≅
      homogeneousDiscretizationFunctor tau h ⋙ homogeneousFunctor (Fin n) c :=
  conjugateSquareIso Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    (homogeneousDiscretizationModelsChange h c)

/-- Homogeneous truncation commutes with change of signature:
$\mathrm{Tr}^{(m,n)}_{\Sigma}\circ\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{(m)\ast}_{\mathfrak{gd}}\circ\mathrm{Tr}^{(m,n)}_{\Lambda}$. -/
noncomputable def homogeneousTruncationFunctorChange {m n : ℕ} (h : m ≤ n)
    (c : Derivor sig tau) :
    homogeneousFunctor.{0, u, v, w} (Fin n) c ⋙ homogeneousTruncationFunctor sig h ≅
      homogeneousTruncationFunctor tau h ⋙ homogeneousFunctor (Fin m) c :=
  conjugateSquareIso Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    (homogeneousTruncationModelsChange h c)

/-- Heterogeneous discretization commutes with change of signature:
$\mathrm{Ds}^{\mathrm{htg}(n,m)}_{\Sigma}\circ\mathbf{c}^{\mathrm{htg}(m)\ast}_{\mathfrak{gd}}
\cong\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}\circ
\mathrm{Ds}^{\mathrm{htg}(n,m)}_{\Lambda}$. -/
noncomputable def heterogeneousDiscretizationFunctorChange {m n : ℕ} (h : m ≤ n)
    (c : Derivor sig tau) :
    heterogeneousFunctor.{0, u, v, w} (Fin (m + 1)) c ⋙ heterogeneousDiscretizationFunctor sig h ≅
      heterogeneousDiscretizationFunctor tau h ⋙ heterogeneousFunctor (Fin (n + 1)) c :=
  conjugateSquareIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    (heterogeneousDiscretizationModelsChange h c)

/-- Heterogeneous truncation commutes with change of signature:
$\mathrm{Tr}^{\mathrm{htg}(m,n)}_{\Sigma}\circ\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}
\cong\mathbf{c}^{\mathrm{htg}(m)\ast}_{\mathfrak{gd}}\circ
\mathrm{Tr}^{\mathrm{htg}(m,n)}_{\Lambda}$. -/
noncomputable def heterogeneousTruncationFunctorChange {m n : ℕ} (h : m ≤ n)
    (c : Derivor sig tau) :
    heterogeneousFunctor.{0, u, v, w} (Fin (n + 1)) c ⋙ heterogeneousTruncationFunctor sig h ≅
      heterogeneousTruncationFunctor tau h ⋙ heterogeneousFunctor (Fin (m + 1)) c :=
  conjugateSquareIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    (heterogeneousTruncationModelsChange h c)

/-! ## Naturality with respect to reducts -/

/-- Graduation is natural with respect to the reducts of the split indexed categories of categorial algebras, up to the natural isomorphisms above. -/
noncomputable def graduationNaturality (n : ℕ) (c : Derivor sig tau) :
    homogeneousReductFunctor.{0, u, u, v, v, w} (Fin n) c ⋙ graduationFunctor n sig ≅ graduationFunctor n tau ⋙ heterogeneousReductFunctor (Fin (n + 1)) c :=
  Functor.isoWhiskerRight (homogeneousFunctorReductIso (Fin n) c).symm _ ≪≫ graduationFunctorChange n c ≪≫
    Functor.isoWhiskerLeft _ (heterogeneousFunctorReductIso (Fin (n + 1)) c)

/-- Unification is natural with respect to the reducts of the split indexed categories of categorial algebras, up to the natural isomorphisms above. -/
noncomputable def unificationNaturality (n : ℕ) (c : Derivor sig tau) :
    heterogeneousReductFunctor.{0, u, u, v, v, w} (Fin (n + 1)) c ⋙ unificationFunctor n sig ≅ unificationFunctor n tau ⋙ homogeneousReductFunctor (Fin n) c :=
  Functor.isoWhiskerRight (heterogeneousFunctorReductIso (Fin (n + 1)) c).symm _ ≪≫ unificationFunctorChange n c ≪≫
    Functor.isoWhiskerLeft _ (homogeneousFunctorReductIso (Fin n) c)

/-- Homogeneous discretization is natural with respect to reducts. -/
noncomputable def homogeneousDiscretizationNaturality {m n : ℕ} (h : m ≤ n) (c : Derivor sig tau) :
    homogeneousReductFunctor.{0, u, u, v, v, w} (Fin m) c ⋙ homogeneousDiscretizationFunctor sig h ≅ homogeneousDiscretizationFunctor tau h ⋙ homogeneousReductFunctor (Fin n) c :=
  Functor.isoWhiskerRight (homogeneousFunctorReductIso (Fin m) c).symm _ ≪≫ homogeneousDiscretizationFunctorChange h c ≪≫
    Functor.isoWhiskerLeft _ (homogeneousFunctorReductIso (Fin n) c)

/-- Homogeneous truncation is natural with respect to reducts. -/
noncomputable def homogeneousTruncationNaturality {m n : ℕ} (h : m ≤ n) (c : Derivor sig tau) :
    homogeneousReductFunctor.{0, u, u, v, v, w} (Fin n) c ⋙ homogeneousTruncationFunctor sig h ≅ homogeneousTruncationFunctor tau h ⋙ homogeneousReductFunctor (Fin m) c :=
  Functor.isoWhiskerRight (homogeneousFunctorReductIso (Fin n) c).symm _ ≪≫ homogeneousTruncationFunctorChange h c ≪≫
    Functor.isoWhiskerLeft _ (homogeneousFunctorReductIso (Fin m) c)

/-- Heterogeneous discretization is natural with respect to reducts. -/
noncomputable def heterogeneousDiscretizationNaturality {m n : ℕ} (h : m ≤ n) (c : Derivor sig tau) :
    heterogeneousReductFunctor.{0, u, u, v, v, w} (Fin (m + 1)) c ⋙ heterogeneousDiscretizationFunctor sig h ≅ heterogeneousDiscretizationFunctor tau h ⋙ heterogeneousReductFunctor (Fin (n + 1)) c :=
  Functor.isoWhiskerRight (heterogeneousFunctorReductIso (Fin (m + 1)) c).symm _ ≪≫ heterogeneousDiscretizationFunctorChange h c ≪≫
    Functor.isoWhiskerLeft _ (heterogeneousFunctorReductIso (Fin (n + 1)) c)

/-- Heterogeneous truncation is natural with respect to reducts. -/
noncomputable def heterogeneousTruncationNaturality {m n : ℕ} (h : m ≤ n) (c : Derivor sig tau) :
    heterogeneousReductFunctor.{0, u, u, v, v, w} (Fin (n + 1)) c ⋙ heterogeneousTruncationFunctor sig h ≅ heterogeneousTruncationFunctor tau h ⋙ heterogeneousReductFunctor (Fin (m + 1)) c :=
  Functor.isoWhiskerRight (heterogeneousFunctorReductIso (Fin (n + 1)) c).symm _ ≪≫ heterogeneousTruncationFunctorChange h c ≪≫
    Functor.isoWhiskerLeft _ (heterogeneousFunctorReductIso (Fin (m + 1)) c)

end CategorialAlgebras.ChangeOfSignature
