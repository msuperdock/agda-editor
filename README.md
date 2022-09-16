# agda-editor

`agda-editor` is a library for building interactive editors for dependently typed data.
Editors are composable; for example, given editors for types `A : Set` and `B : Set`, we can construct an editor for the product type `A × B : Set`, or for the list type `List A`.

We also handle dependent sum types; given an editor for type `A : Set` and a *dependent editor* for a type `B : A → Set` dependent on a value of type `A`, we can construct an editor for the dependent sum type `Σ A B`.
By a *dependent editor*, we mean an editor whose state type `S : A → Set` depends on a value of type `A`, such that for any values `x₁ x₂ : A`, a state of type `S x₁` can be updated to a state of type `S x₂`.
This update may depend on how `x₁` was transformed to obtain `x₂`; to accommodate this, we allow the type `A` to be given a categorical structure, where objects are terms of type `A`, and arrows are specified by a type `F : A → A → Set`.
In this way, changes to a value `x : A` may propogate to an editor of a type dependent on `x`.

