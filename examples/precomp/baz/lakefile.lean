import Lake
open System Lake DSL

package baz where
  defaultFacet := PackageFacet.oleans
  dependencies := #[
    { name := `bar, src := Source.path (FilePath.mk ".." /  "bar") }
  ]
