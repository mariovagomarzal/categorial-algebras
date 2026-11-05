import CategorialAlgebras.Heterogeneous.Recovery

/-!
# Validity of heterogeneous equations

Expansion satisfies every contextual equation. The verification uses only categorical
laws and preservation by the original higher functors, with no inhabitedness assumptions.
-/

universe i u v w x

namespace CategorialAlgebras.Heterogeneous

variable {I : Type i} [Preorder I] {S : Type u} {sig : Signature.{u, v} S}

/-! ## Evaluation in expanded algebras -/

/-- Select either boundary between two dimensions. -/
def CategorialAlgebra.boundary (A : CategorialAlgebra.{i, u, v, w} I sig)
    {j k : I} (h : j < k) (b : Bool) {s} (x : A.carrier (k, s)) : A.carrier (j, s) :=
  ((A.sort s).str.dim j k h).boundary b x

/-- Boundaries retract identities. -/
theorem CategorialAlgebra.boundary_retract (A : CategorialAlgebra.{i, u, v, w} I sig)
    {j k : I} (h : j < k) (b : Bool) {s} (x : A.carrier (j, s)) :
    A.boundary h b (((A.sort s).str.dim j k h).identity x) = x := by
  cases b
  · exact ((A.sort s).str.dim j k h).source_identity x
  · exact ((A.sort s).str.dim j k h).target_identity x

/-- Boundaries of composites are their outer boundaries. -/
theorem CategorialAlgebra.boundary_comp (A : CategorialAlgebra.{i, u, v, w} I sig)
    {j k : I} (h : j < k) (b : Bool) {s} {x y z : A.carrier (k, s)}
    (hz : z ∈ ((A.sort s).str.dim j k h).comp x y) :
    A.boundary h b z = A.boundary h b (if b then x else y) := by
  cases b
  · exact ((A.sort s).str.dim j k h).source_comp _ _ _ hz
  · exact ((A.sort s).str.dim j k h).target_comp _ _ _ hz

/-- Original operations preserve both boundaries. -/
theorem CategorialAlgebra.operation_boundary (A : CategorialAlgebra.{i, u, v, w} I sig)
    {a s} (σ : sig a s) {j k : I} (h : j < k) (b : Bool)
    (x : Word.Family (fun s => A.carrier (k, s)) a) :
    A.boundary h b ((A.op σ).toFun k x) =
      (A.op σ).toFun j (fun p => A.boundary h b (x p)) := by
  cases b
  · exact ((A.op σ).map_source j k h x).symm
  · exact ((A.op σ).map_target j k h x).symm

/-- Evaluate a boundary in an expansion. -/
theorem eval_expansion_boundary {X : I × S → Type x}
    (A : CategorialAlgebra.{i, u, v, w} I sig) (v : SortedSet.Map X A.carrier)
    {j k : I} (h : j < k) (b : Bool) {s} (t : Term (Symbol I sig) X (k, s)) :
    Term.partialEval (A := A.toPartialAlgebra) v (boundary h b t) =
      (Term.partialEval (A := A.toPartialAlgebra) v t).bind
        (fun x => Part.some (A.boundary h b x)) := by
  erw [boundary, partialEval_unary]
  congr 1
  funext x
  cases b <;> rfl

/-- Evaluate an identity in an expansion. -/
theorem eval_expansion_identity {X : I × S → Type x}
    (A : CategorialAlgebra.{i, u, v, w} I sig) (v : SortedSet.Map X A.carrier)
    {j k : I} (h : j < k) {s} (t : Term (Symbol I sig) X (j, s)) :
    Term.partialEval (A := A.toPartialAlgebra) v (identityTerm h t) =
      (Term.partialEval (A := A.toPartialAlgebra) v t).bind
        (fun x => Part.some (((A.sort s).str.dim j k h).identity x)) := by
  erw [identityTerm, partialEval_unary]
  rfl

/-- Evaluate an original operation in an expansion using original input positions. -/
theorem eval_expansion_base {X : I × S → Type x}
    (A : CategorialAlgebra.{i, u, v, w} I sig) (v : SortedSet.Map X A.carrier)
    (k : I) {a s} (σ : sig a s)
    (t : Word.Family (fun s => Term (Symbol I sig) X (k, s)) a) :
    Term.partialEval (A := A.toPartialAlgebra) v (base k σ t) =
      (partFamily (fun p => Term.partialEval (A := A.toPartialAlgebra) v (t p))).bind
        (fun z => Part.some ((A.op σ).toFun k z)) := by
  rw [partialEval_base]
  congr 1
  funext z
  exact congrArg (fun z => Part.some ((A.op σ).toFun k z))
    ((dimensionFamily k a).apply_symm_apply z)

/-- Compositions of uniform variables evaluate to the basic partial composition. -/
theorem eval_expansion_binary (A : CategorialAlgebra.{i, u, v, w} I sig)
    {j k : I} {s m} (x : Fin m → A.carrier (k, s)) (h : j < k) (p q : Fin m) :
    Term.partialEval (A := A.toPartialAlgebra) (uniformValuation x)
      (binary h (variableTerm (k, s) p) (variableTerm (k, s) q)) =
      ((A.sort s).str.dim j k h).comp (x p) (x q) := by
  erw [partialEval_binary]
  simp only [eval_uniform_variable, Part.bind_some]
  rfl

/-! ## Functoriality equations -/

/-- Original operation boundary equations hold because operations are higher functors. -/
theorem operation_boundary_valid (A : CategorialAlgebra.{i, u, v, w} I sig)
    {a s} (σ : sig a s) {j k : I} (hk : j < k) (b : Bool) :
    QEEquation.Valid A.toPartialAlgebra (Axiom.operationBoundary σ hk b).equation.equation := by
  dsimp only [Axiom.equation, contextualEquation]
  intro v _
  let a' := dimensionWord k a
  let t := dimensionFamily k a (fun p => Term.var (sig := Symbol I sig) (Word.position a' p))
  let r := dimensionFamily k a (fun p => v _ (Word.position a' p))
  have ht p : Term.partialEval (A := A.toPartialAlgebra) v (t p) = Part.some (r p) :=
    eval_dimension_family v k a _ _ (fun _ => rfl) p
  change EEquation.Satisfies A.toPartialAlgebra v
    (boundary hk b (base k σ t), base j σ (fun p => boundary hk b (t p)))
  simp only [EEquation.Satisfies, eval_expansion_boundary A, eval_expansion_base A, ht,
    partFamily_some, Part.bind_some, Part.mem_some_iff, exists_eq_left]
  exact A.operation_boundary σ hk b r

/-- Original operation identity equations hold because operations preserve identities. -/
theorem operation_identity_valid (A : CategorialAlgebra.{i, u, v, w} I sig)
    {a s} (σ : sig a s) {j k : I} (hk : j < k) :
    QEEquation.Valid A.toPartialAlgebra (Axiom.operationIdentity σ hk).equation.equation := by
  dsimp only [Axiom.equation, contextualEquation]
  intro v _
  let a' := dimensionWord j a
  let t := dimensionFamily j a (fun p => Term.var (sig := Symbol I sig) (Word.position a' p))
  let r := dimensionFamily j a (fun p => v _ (Word.position a' p))
  have ht p : Term.partialEval (A := A.toPartialAlgebra) v (t p) = Part.some (r p) :=
    eval_dimension_family v j a _ _ (fun _ => rfl) p
  change EEquation.Satisfies A.toPartialAlgebra v
    (identityTerm hk (base j σ t), base k σ (fun p => identityTerm hk (t p)))
  simp only [EEquation.Satisfies, eval_expansion_identity A, eval_expansion_base A, ht,
    partFamily_some, Part.bind_some, Part.mem_some_iff, exists_eq_left]
  exact ((A.op σ).map_identity j k hk r).symm

/-- Original operation composition equations hold for every componentwise defined tuple. -/
theorem operation_composition_valid (A : CategorialAlgebra.{i, u, v, w} I sig)
    {a s} (σ : sig a s) {j k : I} (hk : j < k) :
    QEEquation.Valid A.toPartialAlgebra (Axiom.operationComposition σ hk).equation.equation := by
  dsimp only [Axiom.equation, contextualEquation]
  intro v hv
  let a' := dimensionWord k a
  let tx := dimensionFamily k a
    (fun p => Term.var (sig := Symbol I sig) (X := PairVariables a') (Word.position a' p, false))
  let ty := dimensionFamily k a
    (fun p => Term.var (sig := Symbol I sig) (X := PairVariables a') (Word.position a' p, true))
  let x := dimensionFamily k a (fun p => v _ (Word.position a' p, false))
  let y := dimensionFamily k a (fun p => v _ (Word.position a' p, true))
  have hx p : Term.partialEval (A := A.toPartialAlgebra) v (tx p) = Part.some (x p) :=
    eval_dimension_family v k a _ _ (fun _ => rfl) p
  have hy p : Term.partialEval (A := A.toPartialAlgebra) v (ty p) = Part.some (y p) :=
    eval_dimension_family v k a _ _ (fun _ => rfl) p
  change ∀ p, EEquation.Satisfies A.toPartialAlgebra v
    (((dimensionFamily k a).symm (fun p => defined (binary hk (tx p) (ty p)))) p) at hv
  have hp : ∀ p, EEquation.Satisfies A.toPartialAlgebra v
      (defined (binary hk (tx p) (ty p))) := by
    have hh := (dimensionFamily_all
      (A := EEquation (Symbol I sig) (PairVariables a'))
      (fun _ e => EEquation.Satisfies A.toPartialAlgebra v e) k a
      ((dimensionFamily k a).symm (fun p => defined (binary hk (tx p) (ty p))))).mp hv
    simpa only [Equiv.apply_symm_apply] using hh
  have hd p : (((A.sort (a.get p)).str.dim j k hk).comp (x p) (y p)).Dom := by
    have hc := (satisfies_defined _ _ _).mp (hp p)
    rw [partialEval_binary, hx, hy, Part.bind_some, Part.bind_some] at hc
    exact hc
  let z p := (((A.sort (a.get p)).str.dim j k hk).comp (x p) (y p)).get (hd p)
  have hz p : z p ∈ ((A.sort (a.get p)).str.dim j k hk).comp (x p) (y p) := Part.get_mem (hd p)
  have hm := (A.op σ).map_comp j k hk x y z ((mem_partFamily _ _).mpr hz)
  have hf : partFamily (fun p => Term.partialEval (A := A.toPartialAlgebra) v
      (binary hk (tx p) (ty p))) = Part.some z := by
    apply Part.eq_some_iff.mpr
    apply (mem_partFamily _ _).mpr
    intro p
    rw [partialEval_binary, hx, hy, Part.bind_some, Part.bind_some]
    exact hz p
  change EEquation.Satisfies A.toPartialAlgebra v
    (base k σ (fun p => binary hk (tx p) (ty p)), binary hk (base k σ tx) (base k σ ty))
  unfold EEquation.Satisfies
  rw [eval_expansion_base A, hf, Part.bind_some, partialEval_binary,
    eval_expansion_base A, eval_expansion_base]
  simp only [hx, hy, partFamily_some, Part.bind_some, Part.mem_some_iff, exists_eq_left]
  exact hm

/-! ## Verification of all schemas -/

/-- Every contextual equation is valid in the expansion of a categorial algebra. -/
theorem CategorialAlgebra.satisfiesEquations (A : CategorialAlgebra.{i, u, v, w} I sig) :
    SatisfiesEquations A.toPartialAlgebra := by
  intro e
  cases e with
  | total k σ =>
    intro v _
    apply (satisfies_defined _ _ _).mpr
    erw [partialEval_variables]
    exact Part.some_dom _
  | boundaryTotal hk s b =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x _
    apply (satisfies_defined _ _ _).mpr
    erw [eval_expansion_boundary]
    simp only [eval_uniform_variable, Part.bind_some, Part.some_dom]
  | retract hk s b =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x _
    unfold EEquation.Satisfies
    simp only [eval_expansion_boundary, eval_expansion_identity, eval_uniform_variable,
      Part.bind_some,
      Part.mem_some_iff, exists_eq_left, A.boundary_retract]
  | domainForward hk s =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hd := (satisfies_defined _ _ _).mp (hx 0)
    erw [eval_expansion_binary] at hd
    unfold EEquation.Satisfies
    simp only [eval_expansion_boundary, eval_uniform_variable, Part.bind_some,
      Part.mem_some_iff, exists_eq_left]
    exact (((A.sort s).str.dim _ _ hk).comp_dom _ _).mp hd
  | domainBackward hk s =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hd := hx 0
    change EEquation.Satisfies A.toPartialAlgebra (uniformValuation x)
      (Heterogeneous.boundary hk false (variableTerm _ 0),
        Heterogeneous.boundary hk true (variableTerm _ 1)) at hd
    unfold EEquation.Satisfies at hd
    simp only [eval_expansion_boundary, eval_uniform_variable, Part.bind_some,
      Part.mem_some_iff, exists_eq_left] at hd
    apply (satisfies_defined _ _ _).mpr
    erw [eval_expansion_binary]
    exact (((A.sort s).str.dim _ _ hk).comp_dom _ _).mpr hd
  | compositeBoundary hk s b =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hd := (satisfies_defined _ _ _).mp (hx 0)
    erw [eval_expansion_binary] at hd
    let z := (((A.sort s).str.dim _ _ hk).comp (x 0) (x 1)).get hd
    have hz : z ∈ ((A.sort s).str.dim _ _ hk).comp (x 0) (x 1) := Part.get_mem hd
    unfold EEquation.Satisfies
    cases b <;>
      simp only [Bool.false_eq_true, ↓reduceIte, eval_expansion_boundary,
        eval_expansion_binary, eval_uniform_variable, Part.bind_some,
        Part.mem_bind_iff, Part.mem_some_iff]
    · exact ⟨_, ⟨z, hz, rfl⟩, A.boundary_comp hk false hz⟩
    · exact ⟨_, ⟨z, hz, rfl⟩, A.boundary_comp hk true hz⟩
  | unit hk s b =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x _
    unfold EEquation.Satisfies
    cases b <;>
      simp only [Bool.false_eq_true, ↓reduceIte, partialEval_binary,
        eval_expansion_boundary, eval_expansion_identity, eval_uniform_variable, Part.bind_some,
        Part.mem_some_iff, exists_eq_right]
    · exact ((A.sort s).str.dim _ _ hk).comp_source _
    · exact ((A.sort s).str.dim _ _ hk).target_comp_self _
  | assoc hk s =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hxy := (satisfies_defined _ _ _).mp (hx 0)
    have hyz := (satisfies_defined _ _ _).mp (hx 1)
    erw [eval_expansion_binary] at hxy hyz
    obtain ⟨q, hq, hq'⟩ := ((A.sort s).str.dim _ _ hk).assoc _ _ _ _ _
      (Part.get_mem hxy) (Part.get_mem hyz)
    unfold EEquation.Satisfies
    simp only [partialEval_binary, eval_uniform_variable, Part.bind_some, Part.mem_bind_iff]
    exact ⟨q, ⟨_, Part.get_mem hxy, hq⟩, _, Part.get_mem hyz, hq'⟩
  | identityTotal hk s =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x _
    apply (satisfies_defined _ _ _).mpr
    erw [eval_expansion_identity]
    simp only [eval_uniform_variable, Part.bind_some, Part.some_dom]
  | globular hj jk s b c =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x _
    unfold EEquation.Satisfies
    simp only [eval_expansion_boundary, eval_uniform_variable, Part.bind_some,
      Part.mem_some_iff, exists_eq_left]
    exact ((A.sort s).str.compatible _ _ _ hj jk).globular b c _
  | identityIdentity hj jk s =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x _
    unfold EEquation.Satisfies
    simp only [eval_expansion_identity, eval_uniform_variable, Part.bind_some,
      Part.mem_some_iff, exists_eq_left]
    exact ((A.sort s).str.compatible _ _ _ hj jk).identity_identity _
  | boundaryComposition hj jk s b =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hd := (satisfies_defined _ _ _).mp (hx 0)
    erw [eval_expansion_binary] at hd
    unfold EEquation.Satisfies
    simp only [eval_expansion_boundary, partialEval_binary, eval_uniform_variable,
      Part.bind_some, Part.mem_bind_iff, Part.mem_some_iff]
    exact ⟨_, ⟨_, Part.get_mem hd, rfl⟩,
      ((A.sort s).str.compatible _ _ _ hj jk).boundary_comp b _ _ _ (Part.get_mem hd)⟩
  | identityComposition hj jk s =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hd := (satisfies_defined _ _ _).mp (hx 0)
    erw [eval_expansion_binary] at hd
    unfold EEquation.Satisfies
    simp only [eval_expansion_identity, partialEval_binary, eval_uniform_variable,
      Part.bind_some, Part.mem_bind_iff, Part.mem_some_iff]
    exact ⟨_, ⟨_, Part.get_mem hd, rfl⟩,
      ((A.sort s).str.compatible _ _ _ hj jk).identity_comp _ _ _ (Part.get_mem hd)⟩
  | interchange hj jk s =>
    apply (uniform_valid_iff _ _ _).mpr
    intro x hx
    have hxy := (satisfies_defined _ _ _).mp (hx 0)
    have hzt := (satisfies_defined _ _ _).mp (hx 1)
    have hxz := (satisfies_defined _ _ _).mp (hx 2)
    have hyt := (satisfies_defined _ _ _).mp (hx 3)
    erw [eval_expansion_binary] at hxy hzt hxz hyt
    obtain ⟨q, hq, hq'⟩ := ((A.sort s).str.compatible _ _ _ hj jk).interchange _ _ _ _ _ _ _ _
      (Part.get_mem hxy) (Part.get_mem hzt) (Part.get_mem hxz) (Part.get_mem hyt)
    unfold EEquation.Satisfies
    simp only [partialEval_binary, eval_uniform_variable, Part.bind_some, Part.mem_bind_iff]
    exact ⟨q, ⟨_, Part.get_mem hxy, _, Part.get_mem hzt, hq⟩,
      _, Part.get_mem hxz, _, Part.get_mem hyt, hq'⟩

  | operationBoundary σ hk b => exact operation_boundary_valid A σ hk b
  | operationIdentity σ hk => exact operation_identity_valid A σ hk
  | operationComposition σ hk => exact operation_composition_valid A σ hk

end CategorialAlgebras.Heterogeneous
