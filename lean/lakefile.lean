import Lake
open Lake DSL

package SpectralAlgebras where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- finite certificates for "Modular and integral spectral algebras of abelian Cayley graphs" -/
@[default_target]
lean_lib SpectralAlgebras
