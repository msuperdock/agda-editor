# agda-editor

`agda-editor` is a library for building interactive editors for dependently typed data.
Editors are composable; for example, given editors for types `A : Set` and `B : Set`, `agda-editor` provides functions that automatically construct an editor for the product type `A × B : Set`, or for the list type `List A`.
Similarly, given an editor for type `A : Set` and a "dependent editor" for a type `B : A → Set` dependent on a value of type `A`, `agda-editor` provides functions that automatically construct an editor for the dependent sum type `Σ A B`.
Our concept of a "dependent editor" allows changes to a value `x : A` to be propogated to the state of an editor of a type dependent on `x`.

